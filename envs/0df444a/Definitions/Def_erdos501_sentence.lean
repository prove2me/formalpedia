-- Prove2me | Definitions.Def_erdos501_sentence
-- name    : erdos501_sentence
-- status  : Definition
-- author  : @LG
-- created : 2026-11-23T23:15:40.189299+00:00
-- url     : https://prove2.me/theorems/737b3a56-7e19-4031-8fa4-be24099cbea5
-- title:
--   Erdős 501 as a first-order sentence: every complete ordered field has the Erdős property
-- statement:
--   This bundle renders the first question of Erdős Problem 501 as a single first-order sentence $\varphi_{501}$ (`Erdos501`) of the language $L$ of set theory with symbols $\emptyset, \omega, \mathcal{P}, \bigcup, (\cdot,\cdot), \in$, following the shape of DeepMind's `formal-conjectures` statement.
--
--   Rather than constructing $\mathbb{R}$ inside set theory, the sentence quantifies over **all complete ordered fields** $(R, +, \cdot, <, 0, 1)$ given as sets — $+$ and $\cdot$ as sets of triples $((x,y),z)$, $<$ as a set of pairs — and asserts the Erdős property for each: for every function $A : R \to \mathcal{P}(R)$ such that every $A_x$ is bounded and has outer measure $< 1$, there is an infinite independent $X \subseteq R$. ZFC proves that any two complete ordered fields are isomorphic and that the property is invariant under isomorphism, so this is ZFC-equivalent to the property for $\mathbb{R}$.
--
--   The constituent predicates:
--
--   1. `completeOrderedFieldF` — the field axioms, a total order compatible with $+$ and $\cdot$, and Dedekind completeness (every nonempty bounded-above subset has a least upper bound);
--   2. `boundedF` — $\exists m_1, m_2 \in R,\ \forall y \in S,\ m_1 < y < m_2$ (bounded above and below);
--   3. `outerMeasureLtOneF` — there are sequences $a, b : \omega \to R$ with $a_n < b_n$ whose open intervals $(a_n, b_n)$ cover $S$, and whose partial sums $s_0 = 0$, $s_{n+1} + a_n = s_n + b_n$ are all $\le r$ for some $r < 1$: the definition of Lebesgue outer measure $< 1$;
--   4. `infiniteF` — $\omega$ injects into $X$ (ZFC-equivalent to "not finite" by choice);
--   5. `independentF` — $\forall x, y \in X,\ x \ne y \to x \notin A_y$.
--
--   **Formalization Note.** Formulas are built with the depth-polymorphic de Bruijn-level combinators of `definable_saturated_fol` (`allF fun x => …` binds a variable and passes its level to the body); `appF`, `app2F`, `isFunF`, `succF` are reused verbatim from that definition. The sentence is obtained by evaluation at depth $0$ (`toSentence`). Ported verbatim from Part A of `Challenge.lean`.
-- source:
--   https://github.com/elliotglazer/erdos501/blob/218d1c1e46f77d4db80e566d1721782e85b94a17/Challenge.lean#L339-L528 (Part A, the sentence); statement shape: google-deepmind/formal-conjectures, FormalConjectures/ErdosProblems/501.lean; E. Glazer, Sol (2026), Erdős Problem 501 after adding ω₂ random reals, docs/paper/erdos501_random_profiles_rev10.pdf

/- Ported verbatim from elliotglazer/erdos501, Challenge.lean (Apache 2.0, (c) 2026 Elliot Glazer),
   commit 218d1c1e46f77d4db80e566d1721782e85b94a17. -/
import Mathlib.ModelTheory.Satisfiability
import Definitions.Def_definable_saturated_fol

open FirstOrder FirstOrder.Language
open scoped FirstOrder

namespace Erdos501.FOL

/-! ### The sentence `Erdos501`

We follow DeepMind's formalization of the first question and render it as
follows.

* **The real numbers.**  Rather than constructing `ℝ` inside set theory, the
  sentence quantifies over *all* complete ordered fields `(R, +, ·, <, 0, 1)`
  given as sets (`+`, `·` as sets of triples `((x, y), z)`, `<` as a set of pairs)
  and asserts the Erdős property for each of them.  ZFC proves that any two
  complete ordered fields are isomorphic and the Erdős property is invariant
  under isomorphism, so this is ZFC-equivalent to the property for `ℝ`.
* **Bounded.**  `∃ m₁ m₂ ∈ R, ∀ y ∈ A_x, m₁ < y < m₂` (`boundedF`).
* **Outer measure `< 1`.**  Lebesgue outer measure is the infimum of `∑ (bₙ - aₙ)`
  over covers by countably many open intervals; it is `< 1` iff there is a cover
  `(aₙ, bₙ)ₙ∈ω` with all partial sums `sₙ = ∑_{k<n} (b_k - a_k)` (defined by
  `s₀ = 0`, `s_{n+1} + aₙ = sₙ + bₙ`) bounded by some `r < 1`
  (`outerMeasureLtOneF`).
* **Infinite.**  `ω` injects into `X` (`infiniteF`; ZFC-equivalent to "not
  finite" by choice).
* **Independent.**  `∀ x y ∈ X, x ≠ y → x ∉ A(y)` (`independentF`). -/

/-- `x < y`, for an order relation `lt` given as a set of ordered pairs. -/
def ltF (lt x y : Tm) : Fm := memF (pairT x y) lt

/-- `x ≤ y`, i.e. `x < y ∨ x = y`. -/
def leF (lt x y : Tm) : Fm := orF (ltF lt x y) (eqF x y)

-- `appF`, `app2F`, `isFunF`, `succF` are provided verbatim by `Definitions.Def_definable_saturated_fol`.

/-- `op` is a binary operation on `R`: every pair `(x, y) ∈ R × R` has exactly one
`op`-value, and it lies in `R`. -/
def isOp2F (R op : Tm) : Fm :=
  allIn R fun x => allIn R fun y => exIn R fun z =>
    andF (app2F op (varT x) (varT y) (varT z))
      (allF fun z' => impF (app2F op (varT x) (varT y) (varT z')) (eqF (varT z') (varT z)))

/-- `(R, plus, times, lt, zero, one)` is a complete ordered field: `plus`, `times`
are binary operations on `R`, `zero, one ∈ R`, the field axioms, the axioms of a
total order compatible with `+` and `·`, and Dedekind completeness (every
nonempty subset of `R` with an upper bound has a least upper bound). -/
def completeOrderedFieldF (R plus times lt zero one : Tm) : Fm :=
  andsF [
    isOp2F R plus,
    isOp2F R times,
    memF zero R,
    memF one R,
    -- `+` is associative: x + y = u → u + z = v → y + z = w → x + w = w' → v = w'
    allIn R fun x => allIn R fun y => allIn R fun z =>
      allF fun u => allF fun v => allF fun w => allF fun w' =>
        impF (app2F plus (varT x) (varT y) (varT u)) <| impF (app2F plus (varT u) (varT z) (varT v)) <|
        impF (app2F plus (varT y) (varT z) (varT w)) <| impF (app2F plus (varT x) (varT w) (varT w')) <|
        eqF (varT v) (varT w'),
    -- `+` is commutative
    allIn R fun x => allIn R fun y => allF fun u =>
      impF (app2F plus (varT x) (varT y) (varT u)) (app2F plus (varT y) (varT x) (varT u)),
    -- x + 0 = x
    allIn R fun x => app2F plus (varT x) zero (varT x),
    -- additive inverses
    allIn R fun x => exIn R fun y => app2F plus (varT x) (varT y) zero,
    -- `·` is associative
    allIn R fun x => allIn R fun y => allIn R fun z =>
      allF fun u => allF fun v => allF fun w => allF fun w' =>
        impF (app2F times (varT x) (varT y) (varT u)) <| impF (app2F times (varT u) (varT z) (varT v)) <|
        impF (app2F times (varT y) (varT z) (varT w)) <| impF (app2F times (varT x) (varT w) (varT w')) <|
        eqF (varT v) (varT w'),
    -- `·` is commutative
    allIn R fun x => allIn R fun y => allF fun u =>
      impF (app2F times (varT x) (varT y) (varT u)) (app2F times (varT y) (varT x) (varT u)),
    -- x · 1 = x
    allIn R fun x => app2F times (varT x) one (varT x),
    -- multiplicative inverses of nonzero elements
    allIn R fun x => impF (notF (eqF (varT x) zero)) (exIn R fun y => app2F times (varT x) (varT y) one),
    -- 0 ≠ 1
    notF (eqF zero one),
    -- distributivity: y + z = u → x · u = v → x · y = w → x · z = t → w + t = t' → v = t'
    allIn R fun x => allIn R fun y => allIn R fun z =>
      allF fun u => allF fun v => allF fun w => allF fun t => allF fun t' =>
        impF (app2F plus (varT y) (varT z) (varT u)) <| impF (app2F times (varT x) (varT u) (varT v)) <|
        impF (app2F times (varT x) (varT y) (varT w)) <| impF (app2F times (varT x) (varT z) (varT t)) <|
        impF (app2F plus (varT w) (varT t) (varT t')) <| eqF (varT v) (varT t'),
    -- `<` is irreflexive
    allIn R fun x => notF (ltF lt (varT x) (varT x)),
    -- `<` is transitive
    allIn R fun x => allIn R fun y => allIn R fun z =>
      impF (ltF lt (varT x) (varT y)) <| impF (ltF lt (varT y) (varT z)) <| ltF lt (varT x) (varT z),
    -- `<` is total
    allIn R fun x => allIn R fun y =>
      orF (ltF lt (varT x) (varT y)) (orF (eqF (varT x) (varT y)) (ltF lt (varT y) (varT x))),
    -- `<` is compatible with `+`: x < y → x + z = u → y + z = v → u < v
    allIn R fun x => allIn R fun y => allIn R fun z => allF fun u => allF fun v =>
      impF (ltF lt (varT x) (varT y)) <| impF (app2F plus (varT x) (varT z) (varT u)) <|
      impF (app2F plus (varT y) (varT z) (varT v)) <| ltF lt (varT u) (varT v),
    -- products of positive elements are positive: 0 < x → 0 < y → x · y = u → 0 < u
    allIn R fun x => allIn R fun y => allF fun u =>
      impF (ltF lt zero (varT x)) <| impF (ltF lt zero (varT y)) <|
      impF (app2F times (varT x) (varT y) (varT u)) <| ltF lt zero (varT u),
    -- Dedekind completeness: every nonempty bounded-above `S ⊆ R` has a least upper bound
    allIn (powT R) fun S =>
      impF (notF (eqF (varT S) empT)) <|
      impF (exIn R fun b => allIn (varT S) fun s => leF lt (varT s) (varT b)) <|
      exIn R fun u =>
        andF (allIn (varT S) fun s => leF lt (varT s) (varT u))
          (allIn R fun v => impF (allIn (varT S) fun s => leF lt (varT s) (varT v))
            (leF lt (varT u) (varT v)))
  ]

/-- `S` is bounded (above and below) in `(R, <)`: `∃ m₁ m₂ ∈ R, ∀ y ∈ S, m₁ < y < m₂`.
This renders `Bornology.IsBounded (A x)`. -/
def boundedF (R lt S : Tm) : Fm :=
  exIn R fun m₁ => exIn R fun m₂ => allIn S fun y =>
    andF (ltF lt (varT m₁) (varT y)) (ltF lt (varT y) (varT m₂))

/-- The Lebesgue outer measure of `S ⊆ R` is `< 1`: there are sequences
`a, b : ω → R` with `aₙ < bₙ`, such that the open intervals `(aₙ, bₙ)` cover `S`,
and whose total length `∑ₙ (bₙ - aₙ)` is `< 1`; the total length is expressed
through the partial sums `s : ω → R`, `s 0 = 0`, `s (n+1) + aₙ = s n + bₙ`, all of
which are `≤ r` for some `r < 1`.  This renders `volume.toOuterMeasure (A x) < 1`. -/
def outerMeasureLtOneF (R plus lt zero one S : Tm) : Fm :=
  exF fun a => exF fun b => exF fun s => andsF [
    isFunF omT R (varT a),
    isFunF omT R (varT b),
    isFunF omT R (varT s),
    -- the intervals are nondegenerate: ∀ n ∈ ω, aₙ < bₙ
    allIn omT fun n => allF fun u => allF fun v =>
      impF (appF (varT a) (varT n) (varT u)) <| impF (appF (varT b) (varT n) (varT v)) <|
      ltF lt (varT u) (varT v),
    -- they cover `S`: ∀ y ∈ S, ∃ n ∈ ω, aₙ < y < bₙ
    allIn S fun y => exIn omT fun n => exF fun u => exF fun v =>
      andF (appF (varT a) (varT n) (varT u)) <| andF (appF (varT b) (varT n) (varT v)) <|
      andF (ltF lt (varT u) (varT y)) (ltF lt (varT y) (varT v)),
    -- s 0 = 0
    appF (varT s) empT zero,
    -- s (n+1) + aₙ = s n + bₙ
    allIn omT fun n => allF fun m => impF (succF (varT n) (varT m)) <|
      allF fun u => allF fun v => allF fun w => allF fun w' => allF fun t => allF fun t' =>
        impF (appF (varT a) (varT n) (varT u)) <| impF (appF (varT b) (varT n) (varT v)) <|
        impF (appF (varT s) (varT n) (varT w)) <| impF (appF (varT s) (varT m) (varT w')) <|
        impF (app2F plus (varT w') (varT u) (varT t)) <| impF (app2F plus (varT w) (varT v) (varT t')) <|
        eqF (varT t) (varT t'),
    -- the partial sums are bounded by some r < 1
    exIn R fun r => andF (ltF lt (varT r) one)
      (allIn omT fun n => allF fun w => impF (appF (varT s) (varT n) (varT w)) (leF lt (varT w) (varT r)))
  ]

/-- `X` is infinite: `ω` injects into `X`.  This renders `X.Infinite`. -/
def infiniteF (X : Tm) : Fm :=
  exF fun f => andF (isFunF omT X (varT f))
    (allIn omT fun n => allIn omT fun m => allF fun u =>
      impF (appF (varT f) (varT n) (varT u)) <| impF (appF (varT f) (varT m) (varT u)) <|
      eqF (varT n) (varT m))

/-- `X` is independent for the family `A`: `∀ x y ∈ X, x ≠ y → x ∉ A(y)`.
This renders `X.Pairwise (fun x y => x ∉ A y)`. -/
def independentF (A X : Tm) : Fm :=
  allIn X fun x => allIn X fun y => impF (notF (eqF (varT x) (varT y)))
    (allF fun Ay => impF (appF A (varT y) (varT Ay)) (notF (memF (varT x) (varT Ay))))

/-- The Erdős property for the complete ordered field `(R, plus, times, lt, zero, one)`:
for every function `A : R → 𝒫(R)` such that every `A(x)` is bounded and has outer
measure `< 1`, there is an infinite independent `X ⊆ R`. -/
def erdosPropertyF (R plus lt zero one : Tm) : Fm :=
  allF fun A => impF (isFunF R (powT R) (varT A)) <|
    impF (allIn R fun x => allF fun Ax => impF (appF (varT A) (varT x) (varT Ax))
      (andF (boundedF R lt (varT Ax)) (outerMeasureLtOneF R plus lt zero one (varT Ax)))) <|
    exIn (powT R) fun X => andF (infiniteF (varT X)) (independentF (varT A) (varT X))

set_option linter.dupNamespace false in
/-- **Erdős problem #501, first question, as a sentence of `L`**: for every complete
ordered field `(R, +, ·, <, 0, 1)`, every family `⟨A_x : x ∈ R⟩` of bounded subsets
of `R` of outer measure `< 1` has an infinite independent set. -/
def Erdos501 : L.Sentence :=
  toSentence <|
    allF fun R => allF fun plus => allF fun times => allF fun lt => allF fun zeroR => allF fun oneR =>
      impF (completeOrderedFieldF (varT R) (varT plus) (varT times) (varT lt) (varT zeroR) (varT oneR))
        (erdosPropertyF (varT R) (varT plus) (varT lt) (varT zeroR) (varT oneR))

end Erdos501.FOL


