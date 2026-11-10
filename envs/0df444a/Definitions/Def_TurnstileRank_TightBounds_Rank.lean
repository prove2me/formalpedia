-- Prove2me | Definitions.Def_TurnstileRank_TightBounds_Rank
-- name    : TurnstileRank_TightBounds_Rank
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T20:06:42.475661+00:00
-- url     : https://prove2.me/theorems/fda77c88-87c0-4485-87a6-f625b5dccd4a
-- title:
--   Rank queries, select queries, the bound RQ(ε, n, U), and correct turnstile rank algorithms
-- statement:
--   A turnstile stream over the ordered universe $[U]=\{0,\dots,U-1\}$ (Lean: `Fin U`) changes a frequency vector, initially zero; streams are the published unit-update streams of `BoolCSPDel_TurnstileAlg` (a list of pairs $(u,\pm)$, inserting or deleting one copy of $u$), whose final vector is `finalVec s` $=$ `BoolCSPDel.freq s`. An integer update $(u,\Delta)$ is $|\Delta|$ unit updates.
--
--   * Definition 4.1: for $f\in\mathbb Z^U$ and $x\in\{0,\dots,U\}$, the rank is $R_f(x)=\sum_{u<x}f_u$ (`rank f x`), and $\|f\|_1=\sum_u f_u$ for nonnegative $f$ (`mass f`).
--   * Theorem 1.1: with $L=\log_2(2+U\varepsilon)$,
--   $$RQ(\varepsilon,n,U)=\min\Big\{\varepsilon^{-1}L^{3/2}\log_2\Big(2+\frac{n\varepsilon}{\sqrt L}\Big),\ \varepsilon^{-2}\log_2U\,\log_2n,\ \log_2\binom{U+n}{n}\Big\}.$$
--   * An answer $a$ to the rank query $x$ is correct (`RankOK f ε x a`) when $|a-R_f(x)|\le\varepsilon\|f\|_1$. An answer $a$ to the select query with target $r$ is correct (`SelectOK f ε r a`) when $a$ is a natural number $\hat x<U$ with $R_f(\hat x+1)\ge r-\varepsilon\|f\|_1$ and $R_f(\hat x)\le r+\varepsilon\|f\|_1$ (printed p. 2).
--   * A stream is admissible for $n$ when its final vector is nonnegative with total at most $n$; intermediate vectors are unrestricted.
--   * An algorithm is the published `BoolCSPDel.TurnstileAlg (Fin U) Ω S (ℕ → ℝ)`: from a seed $\omega$ (law $\mu$, a probability measure) an initial state, a transition per update, and an output map giving an answer for every query. Its space is `CosDensity.memoryBits S` $=\log_2|S|$. It is correct for $(U,n,\varepsilon)$ (`RankCorrect μ A n ε`) when, for every admissible stream and every query $x\le U$, the event $|\text{answer}-R_f(x)|\le\varepsilon\|f\|_1$ has probability at least $2/3$ (`CosDensity.SucceedsWP`: a measurable event of measure at least $2/3$ inside it).
--   * Stored seed (`IsStoredSeed A`): the transition and output maps do not depend on the seed, which then only selects the initial state, so it is part of the counted state.
-- source:
--   Hu, Jiang, Liu, Yu (2026), Tight Bounds for Rank Estimation in Turnstile Streams, held STOC 2027 submission, SHA-256 4be4260012249f6a39249d22651326b8b78a13b1a792ae41b80f8363cd5567b6, printed pp. 1–2 (PDF 2–3), Theorem 1.1 and select queries, and Definition 4.1, printed p. 12 (PDF 13)

import Mathlib
import Definitions.Def_BoolCSPDel_TurnstileAlg
import Definitions.Def_CosDensity_StreamAlg

/-!
# Rank queries, the bound `RQ(ε, n, U)`, and correct turnstile rank algorithms

Hu, Jiang, Liu, Yu (2026), *Tight Bounds for Rank Estimation in Turnstile Streams*, held STOC 2027
submission (SHA-256 4be42600…): §1, printed pp. 1–2 (PDF 2–3), the problem and Theorem 1.1;
Definition 4.1, printed p. 12 (PDF 13); select queries, printed p. 2 (PDF 3).

"A stream over the ordered universe `[U] = {0, …, U − 1}` maintains a frequency vector, initially
zero, through updates `(u, Δ)` … The final frequency vector `f ∈ ℤ^U_{≥0}` is promised to be
nonnegative, and `n` is an upper bound on its final total frequency `‖f‖₁`. A rank query at `x`
asks for `R_f(x) = Σ_{u<x} f_u` … within additive error `ε‖f‖₁` with constant success probability
for each fixed query."

**Formalization Note.**
* The universe `[U]` is `Fin U`; a query is a natural number `x` with `x ≤ U`.
* Streams are the published `BoolCSPDel` unit-update turnstile streams (`List (Fin U × Bool)`,
  `true` inserts and `false` deletes one copy; `BoolCSPDel.freq`). An integer update `(u, Δ)` is
  `|Δ|` unit updates, so the class of final vectors and the space needed are unchanged.
* Algorithms are the published `BoolCSPDel.TurnstileAlg (Fin U) Ω S (ℕ → ℝ)`: a seed `ω` from a
  probability measure, an initial state, a transition and an output map; the output after a stream
  is a function answering every query `x`. Space is `CosDensity.memoryBits S = log₂ |S|`.
  In the lower-bound model the seed is persistent, public and free; `IsStoredSeed` restricts to
  algorithms whose transition and output ignore the seed, so the seed only selects the initial
  state and is counted in `log₂ |S|`.
* Correctness (`RankCorrect`) is per fixed stream and per fixed query: on every stream (of any
  length, intermediate vectors unrestricted) whose final vector is nonnegative with total at most
  `n`, and for every query `x ≤ U`, the event `|answer − R_f(x)| ≤ ε‖f‖₁` holds with probability at
  least `2/3` (`CosDensity.SucceedsWP`: a measurable event of measure `≥ 2/3` inside it).
* All logarithms are base two (`Real.logb 2`, §3.2).
-/

noncomputable section

open scoped BigOperators

namespace TurnstileRank.TightBounds

/-- Definition 4.1: the rank `R_f(x) = Σ_{u < x} f_u` of a frequency vector on `[U]`. -/
def rank {U : ℕ} (f : Fin U → ℤ) (x : ℕ) : ℤ :=
  ∑ u ∈ Finset.univ.filter (fun u : Fin U => u.val < x), f u

/-- The total mass `‖f‖₁ = Σ_u f_u` of a (nonnegative) frequency vector. -/
def mass {U : ℕ} (f : Fin U → ℤ) : ℤ := ∑ u, f u

/-- `L = log₂(2 + Uε)` of Theorem 1.1. -/
def Lterm (ε : ℝ) (U : ℕ) : ℝ := Real.logb 2 (2 + U * ε)

/-- Theorem 1.1: `RQ(ε, n, U) = min{ε⁻¹ L^{3/2} log₂(2 + nε/√L), ε⁻² log₂ U log₂ n, log₂ C(U+n, n)}`
with `L = log₂(2 + Uε)`. -/
def RQ (ε : ℝ) (n U : ℕ) : ℝ :=
  min (min (ε⁻¹ * Lterm ε U ^ ((3 : ℝ) / 2) * Real.logb 2 (2 + n * ε / Real.sqrt (Lterm ε U)))
      (ε⁻¹ ^ 2 * Real.logb 2 U * Real.logb 2 n))
    (Real.logb 2 (Nat.choose (U + n) n))

/-- The answer `a` to the rank query `x` on `f` is within `ε‖f‖₁` of `R_f(x)`. -/
def RankOK {U : ℕ} (f : Fin U → ℤ) (ε : ℝ) (x : ℕ) (a : ℝ) : Prop :=
  |a - (rank f x : ℝ)| ≤ ε * (mass f : ℝ)

/-- Select query (printed p. 2): the answer `a` to the select query with target rank `r` is a
coordinate `x̂ ∈ [U]` with `R_f(x̂ + 1) ≥ r − ε‖f‖₁` and `R_f(x̂) ≤ r + ε‖f‖₁`. -/
def SelectOK {U : ℕ} (f : Fin U → ℤ) (ε r : ℝ) (a : ℝ) : Prop :=
  ∃ xh : ℕ, a = (xh : ℝ) ∧ xh < U ∧ r - ε * (mass f : ℝ) ≤ (rank f (xh + 1) : ℝ) ∧
    (rank f xh : ℝ) ≤ r + ε * (mass f : ℝ)

/-- The final frequency vector of a unit-update stream over `[U]`. -/
def finalVec {U : ℕ} (s : List (Fin U × Bool)) : Fin U → ℤ := fun u => BoolCSPDel.freq s u

/-- A stream is admissible for the bound `n`: its final vector is nonnegative with total at most
`n` (intermediate vectors are unrestricted). -/
def Admissible {U : ℕ} (n : ℕ) (s : List (Fin U × Bool)) : Prop :=
  (∀ u, 0 ≤ finalVec s u) ∧ mass (finalVec s) ≤ n

/-- A randomized turnstile rank algorithm with seed law `μ` is correct for `(U, n, ε)`: for every
admissible stream and every query `x ≤ U`, the answer is within `ε‖f‖₁` of `R_f(x)` with
probability at least `2/3`. -/
def RankCorrect {U : ℕ} {Ω S : Type} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (A : BoolCSPDel.TurnstileAlg (Fin U) Ω S (ℕ → ℝ)) (n : ℕ) (ε : ℝ) : Prop :=
  ∀ s : List (Fin U × Bool), Admissible n s → ∀ x : ℕ, x ≤ U →
    CosDensity.SucceedsWP μ (fun ω => RankOK (finalVec s) ε x (A.out ω (A.run ω s) x)) (2 / 3)

/-- The stored-seed restriction: transition and output do not depend on the seed, so the seed
only chooses the (random) initial state and is part of the counted state. -/
def IsStoredSeed {U Ω S O : Type} (A : BoolCSPDel.TurnstileAlg U Ω S O) : Prop :=
  ∀ ω ω' : Ω, A.step ω = A.step ω' ∧ A.out ω = A.out ω'

end TurnstileRank.TightBounds


