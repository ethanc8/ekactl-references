// ─────────────────────────────────────────────────────────
//  The Determinant from Multilinear Algebra
//  A unified introduction for first-year students
// ─────────────────────────────────────────────────────────

#set document(title: "The Determinant from Multilinear Algebra")
#set page(
  paper: "us-letter",
  margin: (x: 1.2in, y: 1.0in),
  numbering: "1",
)
#set text(size: 11pt)
#set par(justify: true, leading: 0.75em, spacing: 1.05em)
#set heading(numbering: "1.")
#show heading.where(level: 1): set text(size: 13pt)
#show heading.where(level: 2): set text(size: 11pt, style: "italic")
#show heading: set block(above: 1.6em, below: 0.65em)
#show math.equation.where(block: true): set block(above: 1.1em, below: 1.1em)

// ── Math operators ────────────────────────────────────────
#let Det  = math.op("det")
#let Sgn  = math.op("sgn")

// ── Coloured environment boxes ────────────────────────────
#let envbox(accent, title, body) = {
  v(0.45em)
  block(
    width: 100%,
    inset: (left: 10pt, right: 10pt, top: 8pt, bottom: 9pt),
    stroke: (left: 3pt + accent),
    fill: accent.lighten(90%),
    radius: (right: 3pt),
  )[#text(weight: "bold", fill: accent.darken(12%))[#title.]#h(0.4em)#body]
  v(0.45em)
}

#let defn(title, body)  = envbox(rgb("#1e40af"), [Definition (#title)], body)
#let thm(title, body)   = envbox(rgb("#14532d"), [Theorem (#title)], body)
#let psketch(body)      = envbox(rgb("#374151"), [Proof sketch], body)
#let rem(body)          = envbox(rgb("#78350f"), [Remark], body)
#let exm(body)          = envbox(rgb("#4c1d95"), [Example], body)

// ─────────────────────────────────────────────────────────
//  Title block
// ─────────────────────────────────────────────────────────
#align(center)[
  #v(0.5em)
  #text(size: 20pt, weight: "bold")[The Determinant from Multilinear Algebra]
  #v(0.5em)
  #text(size: 11.5pt, style: "italic")[A unified introduction for first-year students]
  #v(1.2em)
]

// ─────────────────────────────────────────────────────────
= What Are We Trying to Measure?

Take $n$ vectors $bold(v)_1, dots.c, bold(v)_n in RR^n$. Together they span a _parallelotope_: in $RR^2$ this is a parallelogram; in $RR^3$, a parallelepiped. We want a function
$omega(bold(v)_1, dots.c, bold(v)_n)$
that measures the *signed volume* of this shape. "Signed" means we track orientation as well as size: scaling one edge by $lambda$ should multiply the volume by $lambda$, and swapping two edges should flip the sign.

If you have seen determinants before, you already know the destination. The determinant of a $2 times 2$ matrix gives the signed area of the parallelogram spanned by its columns, and the determinant of a $3 times 3$ matrix gives the signed volume of the parallelepiped. What is less clear is _why_ the formula takes the form it does. The goal here is to show that the determinant formula is the _only_ answer consistent with a few natural requirements on signed volume — it is not conjured from thin air, but forced on us.

For those thinking more abstractly: a linear map $T: V -> V$ stretches, compresses, or flips space. The determinant should capture the signed volume-scaling factor of $T$ as a property intrinsic to $T$ itself, independent of any choice of basis. Both perspectives lead to the same three axioms.

// ─────────────────────────────────────────────────────────
= Multilinear Maps

Our first requirement is that the signed-volume function be linear in each argument separately. Scaling one edge of the parallelotope by $lambda$ should scale the volume by $lambda$. Splitting one edge into a sum $bold(u) + bold(v)$ should split the parallelotope into two, with volumes adding.

#defn("multilinear (or $k$-linear)")[
  Let $V$ be a vector space over a field $F$. A map $M: V^k -> F$ is *$k$-linear* if it is linear in each of its $k$ arguments separately, with all others held fixed. That is, for each slot $i$ and for all scalars $lambda in F$ and vectors $bold(u), bold(v) in V$:
  $ M(bold(v)_1, dots.c, lambda bold(u) + bold(v), dots.c, bold(v)_k) = lambda, M(bold(v)_1, dots.c, bold(u), dots.c, bold(v)_k) + M(bold(v)_1, dots.c, bold(v), dots.c, bold(v)_k), $
  where $lambda bold(u) + bold(v)$ occupies the $i$-th position.
]

#exm[
  The dot product $(bold(u), bold(v)) mapsto bold(u) dot bold(v)$ on $RR^n$ is bilinear (2-linear): linear in each factor independently. The familiar $2 times 2$ determinant $Det mat(a, b; c, d) = a d - b c$, viewed as a function of its two column vectors, is also bilinear: scale either column by $lambda$ and the output scales by $lambda$.
]

Multilinear maps form a vector space: you can add two of them pointwise and scale them by constants, and the result remains multilinear. This will matter when we count how many signed-volume functions there can be.

// ─────────────────────────────────────────────────────────
= The Alternating Condition

Multilinearity alone does not determine a unique signed-volume function. We also need to enforce orientation. Swapping two edges of a parallelotope should reverse its orientation, changing the sign of the signed volume. And if two edges coincide — a degenerate configuration — the volume should be zero.

#defn("alternating")[
  A $k$-linear map $M: V^k -> F$ is *alternating* if it vanishes whenever any two arguments are equal:
  $ M(bold(v)_1, dots.c, bold(v)_k) = 0 quad "whenever" bold(v)_i = bold(v)_j "for some" i eq.not j. $
]

This single condition implies antisymmetry. To see why: consider expanding
$M(dots.c, bold(v)_i + bold(v)_j, dots.c, bold(v)_i + bold(v)_j, dots.c)$
using multilinearity, once distributing in the $i$-th slot and once in the $j$-th. Both expansions must equal zero (equal arguments), and comparing them forces
$ M(dots.c, bold(v)_i, dots.c, bold(v)_j, dots.c) = -M(dots.c, bold(v)_j, dots.c, bold(v)_i, dots.c). $

Swapping any two arguments negates the output. More generally, permuting all $n$ arguments by a permutation $sigma in S_n$ multiplies $M$ by the _sign_ of $sigma$:
$ M(bold(v)_(sigma(1)), dots.c, bold(v)_(sigma(n))) = Sgn(sigma) dot M(bold(v)_1, dots.c, bold(v)_n), $
where $Sgn(sigma) = +1$ if $sigma$ can be written as a product of an even number of transpositions, and $-1$ if odd.

A further consequence: if $bold(v)_1, dots.c, bold(v)_n$ are *linearly dependent*, then $M(bold(v)_1, dots.c, bold(v)_n) = 0$. Any dependence relation lets one vector be written as a linear combination of the others; multilinearity expands $M$ into a sum of terms, each containing a repeated argument, and the alternating condition kills every one of them. Geometrically, a degenerate parallelotope — whose edges fail to span all of $RR^n$ — has zero volume.

#rem[
  In matrix language: linearly dependent columns mean the matrix is singular. The alternating condition is precisely what forces singular matrices to have determinant zero. Note that this is a _consequence_ of the axioms, not a separate assumption.
]

// ─────────────────────────────────────────────────────────
= The Key Theorem

We are now ready for the heart of the argument.

#thm("one-dimensionality of alternating $n$-linear forms")[
  Let $V$ be an $n$-dimensional vector space over a field $F$. The space of all alternating $n$-linear maps $omega: V^n -> F$ is *one-dimensional*: any two such maps are scalar multiples of each other.
]

#psketch[
  Fix a basis $bold(e)_1, dots.c, bold(e)_n$ of $V$, and let $M: V^n -> F$ be alternating and $n$-linear. Write each argument in basis coordinates:
  $bold(v)_j = sum_(i=1)^n a_(i j) bold(e)_i.$
  Expanding $M(bold(v)_1, dots.c, bold(v)_n)$ by multilinearity gives a sum over all $n^n$ index tuples $(i_1, dots.c, i_n)$ of terms
  $ a_(i_1 1) a_(i_2 2) dots.c a_(i_n n) dot M(bold(e)_(i_1), dots.c, bold(e)_(i_n)). $
  *The alternating condition eliminates most terms.* Whenever two indices $i_k$ coincide, two arguments are the same basis vector, so $M$ vanishes. Only tuples where $(i_1, dots.c, i_n)$ is a permutation $sigma in S_n$ of $(1, dots.c, n)$ survive; there are exactly $n!$ of these. *Antisymmetry handles the rest.* For a surviving term,
  $ M(bold(e)_(sigma(1)), dots.c, bold(e)_(sigma(n))) = Sgn(sigma) dot M(bold(e)_1, dots.c, bold(e)_n). $
  Substituting back:
  $ M(bold(v)_1, dots.c, bold(v)_n) = (sum_(sigma in S_n) Sgn(sigma) a_(sigma(1), 1) a_(sigma(2), 2) dots.c a_(sigma(n), n)) dot M(bold(e)_1, dots.c, bold(e)_n). $
  The sum in parentheses depends only on the coordinate entries $a_(i j)$, not on $M$ at all. So $M$ is completely determined by the single scalar $M(bold(e)_1, dots.c, bold(e)_n)$: change that scalar, and $M$ changes proportionally everywhere, but its shape is fixed. Any two alternating $n$-linear maps that agree on $(bold(e)_1, dots.c, bold(e)_n)$ must agree everywhere.
]

This is what makes the determinant _inevitable_. There is, up to a scalar multiple, only one function consistent with multilinearity and the alternating property. Fixing that scalar — by specifying the volume of the unit hypercube — pins down the determinant uniquely.

// ─────────────────────────────────────────────────────────
= The Determinant: Two Perspectives

The one-dimensionality theorem suggests two equivalent definitions, each illuminating a different facet.

== Via normalization

Require that the unit hypercube — the parallelotope spanned by the standard basis vectors $bold(e)_1, dots.c, bold(e)_n$ — have signed volume 1. The formula from the proof sketch immediately becomes a complete and explicit definition.

#defn("determinant — Leibniz formula")[
  The *determinant* of an $n times n$ matrix $A = (a_(i j))$ is the unique alternating $n$-linear form in the columns of $A$ satisfying $Det(I_n) = 1$. Its value is given by the *Leibniz formula*:
  $ Det(A) = sum_(sigma in S_n) Sgn(sigma) product_(i=1)^n a_(i, sigma(i)), $
  where the sum runs over all $n!$ permutations $sigma$ of $\{1, dots.c, n\}$.
]

#exm[
  For $n = 2$, there are two permutations: the identity ($Sgn = +1$) and the single transposition ($Sgn = -1$). The formula gives $Det mat(a, b; c, d) = a d - b c$. For $n = 3$, all six permutations produce the standard cofactor expansion familiar from a first linear algebra course.
]

This perspective is closest to computation, and it makes checking the formula against known cases immediate.

== Via linear maps

For those thinking in terms of abstract linear maps $T: V -> V$: given any alternating $n$-linear form $M$, define the *pullback* of $M$ along $T$ by
$ (M compose T)(bold(v)_1, dots.c, bold(v)_n) := M(T bold(v)_1, dots.c, T bold(v)_n). $
Because $T$ is linear and $M$ is $n$-linear, $M compose T$ is again $n$-linear. Because $T$ is linear and $M$ is alternating ($M = 0$ when two inputs coincide), $M compose T$ is again alternating. So $M compose T$ belongs to the same one-dimensional space as $M$. It must therefore be a scalar multiple of $M$: there exists $lambda in F$ with
$ M(T bold(v)_1, dots.c, T bold(v)_n) = lambda dot M(bold(v)_1, dots.c, bold(v)_n) quad "for all" bold(v)_1, dots.c, bold(v)_n in V. $
If we replace $M$ by any nonzero scalar multiple $c M$, both sides scale by $c$ and $lambda$ is unchanged. So $lambda$ depends only on $T$, not on the choice of $M$.

#defn("determinant — intrinsic form")[
  The *determinant* of a linear map $T: V -> V$ is the unique scalar $Det T in F$ such that
  $ M compose T = (Det T) dot M $
  for every alternating $n$-linear map $M: V^n -> F$.
]

The two definitions agree: evaluating the intrinsic form at $(bold(e)_1, dots.c, bold(e)_n)$ with any nonzero $M$ and applying the basis expansion recovers the Leibniz formula. The intrinsic form has the advantage of making certain properties transparent, as the next section shows.

// ─────────────────────────────────────────────────────────
= Properties as Theorems

A key philosophical point of this approach: the familiar properties of the determinant are not additional axioms imposed by fiat. They are _theorems_, forced by the three axioms of multilinearity, the alternating property, and normalization. The table below records why each holds.

#align(center)[
  #table(
    columns: (auto, 1fr),
    align: (center + horizon, left + horizon),
    inset: (x: 10pt, y: 9pt),
    stroke: 0.5pt + luma(200),
    fill: (_, row) => if row == 0 { luma(233) } else { white },
    table.header(
      [*Property*],
      [*Why it follows from the axioms*],
    ),
    [$Det(A B) = Det A dot Det B$],
    [Both sides are alternating $n$-linear forms in the columns of $A$, normalized to agree on $I_n$; one-dimensionality forces equality. From the abstract side: $(M compose S) compose T = M compose (S T)$, and tracking scalars gives $Det(S) dot Det(T)$.],
    [$Det(A) = 0 arrow.l.r A$ is singular],
    [Singular $=>$ linearly dependent columns $=>$ the alternating form vanishes. Conversely, if $A$ is invertible then $Det(A) dot Det(A^(-1)) = Det(I) = 1$, so $Det(A) eq.not 0$.],
    [$Det(A^top) = Det(A)$],
    [Transposing swaps row and column indices. In the Leibniz sum, relabeling $sigma$ by $sigma^(-1)$ (same sign) shows the two sums are identical.],
    [Scaling a row by $lambda$ multiplies $Det$ by $lambda$],
    [Scaling one row is a scaling of one argument — exactly what multilinearity governs.],
    [Swapping two rows negates $Det$],
    [Direct consequence of antisymmetry. Adding a multiple of one row to another leaves $Det$ unchanged: the extra term has a repeated row, so it vanishes by the alternating property.],
  )
]

// ─────────────────────────────────────────────────────────
= The Bigger Picture

The multilinear algebra framework does more than derive a formula — it locates the determinant within a much larger structure. The space of alternating $n$-linear forms on an $n$-dimensional space $V$ is the *top exterior power* $Lambda^n V^*$, and the Leibniz formula is the coordinate expression of the evaluation of this exterior form. The same ideas appear throughout mathematics:

- *Differential forms and integration.* The change-of-variables formula
  $integral_U f = integral_(phi(U)) (f compose phi) |Det D phi|$
  is the determinant acting as a volume-scaling factor on differential forms — the same signed-volume intuition, now on curved spaces.

- *Orientation on manifolds.* Choosing an orientation on a smooth manifold is precisely choosing a consistent nonzero element of $Lambda^n T^*_p M$ at each point — the top exterior power of the cotangent space.

- *Algebra.* The same exterior-power construction applies to free modules over any commutative ring, making the determinant a concept in commutative algebra and algebraic geometry, not just in linear algebra over fields.

The entire structure flows from three axioms: *multilinearity, the alternating property, and normalization.* Everything else — the formula, multiplicativity, the relationship to invertibility and orientation — is forced. The determinant is not a definition; it is the unique answer those axioms demand.
