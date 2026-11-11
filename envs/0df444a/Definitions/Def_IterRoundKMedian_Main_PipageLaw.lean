-- Prove2me | Definitions.Def_IterRoundKMedian_Main_PipageLaw
-- name    : IterRoundKMedian_Main_PipageLaw
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:25:20.946026+00:00
-- url     : https://prove2.me/theorems/68640995-56d5-4925-b5a2-9a94bd9d20a3
-- title:
--   Pipage rounding with granularity δ: rounded fractional parts, their marginals and the negative-correlation properties (7)
-- statement:
--   Let $U$ be a finite index set, $y\in\mathbb R_{\ge0}^U$ and $\delta>0$. Write $y_i/\delta=n_i+f_i$ with $n_i=\lfloor y_i/\delta\rfloor$ and $0\le f_i<1$. Pipage rounding with granularity $\delta$ (with respect to any laminar family) keeps the integer parts, rounds the fractional parts to bits $X_i\in\{0,1\}$ and returns
--   $$\hat y_i=\delta\,(n_i+X_i).$$
--   A probability law $\mu$ on $\{0,1\}^U$ (finitely many outcomes, nonnegative weights summing to one) is a **pipage law for $(y,\delta)$** if $\mathbb E[X_i]=f_i$ for every $i$ and, for every $S\subseteq U$,
--   $$\mathbb E\Big[\prod_{i\in S}X_i\Big]\le\prod_{i\in S}f_i,\qquad \mathbb E\Big[\prod_{i\in S}(1-X_i)\Big]\le\prod_{i\in S}(1-f_i),\qquad \mathrm{Var}\Big(\sum_{i\in S}X_i\Big)\le\sum_{i\in S}\mathrm{Var}(X_i).$$
--   These are the marginal identity $\mathbb E[\hat y_i]=y_i$ and the properties (7) that the paper states for the output of its pipage rounding procedure.
--
--   **Formalization Note.** `FinLaw Ω` is a finite probability law (`prob`, `expect`, `pr`, `var`); `bitVal` maps a bit to $0/1$; `IsPipageLaw y δ μ`; `pipageOutput y δ X i` $=\delta(\lfloor y_i/\delta\rfloor+X_i)$; $f_i$ is `Int.fract (y i / δ)`.
-- source:
--   Byrka, Guo, Hu, Li, Shin, Vajanopath, Wan, Wang, Iterative Randomized Rounding for k-Median in General and Euclidean Metrics, STOC 2027 submission (manuscript sha256 02f6267b…), pp. 11–12, §2 (pipage rounding with a laminar family, (7))

import Mathlib

namespace IterRoundKMedian.Main

/-- A probability law on a finite outcome space: nonnegative weights summing to one. -/
structure FinLaw (Ω : Type*) [Fintype Ω] where
  prob : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ prob ω
  sum_one : ∑ ω, prob ω = 1

namespace FinLaw

variable {Ω : Type*} [Fintype Ω]

/-- Expectation `E[f]`. -/
def expect (μ : FinLaw Ω) (f : Ω → ℝ) : ℝ := ∑ ω, μ.prob ω * f ω

/-- Probability `Pr[E]` of an event. -/
noncomputable def pr (μ : FinLaw Ω) (E : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω ∈ Finset.univ.filter E, μ.prob ω

/-- Variance `Var(f) = E[(f − E f)²]`. -/
def var (μ : FinLaw Ω) (f : Ω → ℝ) : ℝ := μ.expect (fun ω => (f ω - μ.expect f) ^ 2)

end FinLaw

/-- `0/1` value of a bit. -/
def bitVal (b : Bool) : ℝ := if b then 1 else 0

/-- Pipage rounding with granularity `δ` of a nonnegative vector `y` indexed by a finite
set `U` (§2): write `y_i/δ = n_i + f_i` with `n_i = ⌊y_i/δ⌋`, `0 ≤ f_i < 1`; the procedure
returns bits `X_i ∈ {0,1}` and `ŷ_i = δ (n_i + X_i)`. A law `μ` on the bit vectors `X`
is a *pipage law* for `(y, δ)` if it has the marginals `E[X_i] = f_i` and the
negative-correlation properties (7): for every `S ⊆ U`,
`E[∏_{i∈S} X_i] ≤ ∏_{i∈S} f_i`, `E[∏_{i∈S} (1 − X_i)] ≤ ∏_{i∈S} (1 − f_i)` and
`Var(Σ_{i∈S} X_i) ≤ Σ_{i∈S} Var(X_i)`. The output law of the pipage rounding procedure of
§2 (for any laminar family) is such a law. -/
structure IsPipageLaw {U : Type*} [Fintype U] [DecidableEq U] (y : U → ℝ) (δ : ℝ)
    (μ : FinLaw (U → Bool)) : Prop where
  marginal : ∀ i, μ.expect (fun X => bitVal (X i)) = Int.fract (y i / δ)
  prod_one : ∀ S : Finset U,
    μ.expect (fun X => ∏ i ∈ S, bitVal (X i)) ≤ ∏ i ∈ S, Int.fract (y i / δ)
  prod_zero : ∀ S : Finset U,
    μ.expect (fun X => ∏ i ∈ S, (1 - bitVal (X i))) ≤ ∏ i ∈ S, (1 - Int.fract (y i / δ))
  var_sum : ∀ S : Finset U,
    μ.var (fun X => ∑ i ∈ S, bitVal (X i)) ≤ ∑ i ∈ S, μ.var (fun X => bitVal (X i))

/-- The rounded vector `ŷ_i = δ (⌊y_i/δ⌋ + X_i)`. -/
noncomputable def pipageOutput {U : Type*} (y : U → ℝ) (δ : ℝ) (X : U → Bool) (i : U) : ℝ :=
  δ * ((⌊y i / δ⌋ : ℝ) + bitVal (X i))

end IterRoundKMedian.Main


