-- Prove2me | Definitions.Def_HindsightGain_Uniform_Supplement_weights
-- name    : HindsightGain_Uniform_Supplement_weights
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:49:57.511205+00:00
-- url     : https://prove2.me/theorems/72d8c20e-a48a-48db-8827-92ba7f97b915
-- title:
--   Hindsight gain and moment parameters for independent weights
-- statement:
--   In the model $(K,A)$ of Section 1.1, let $\zeta=(\zeta_1,\dots,\zeta_n)$ be random weights on a probability space, with means $p_i=\mathbb E\zeta_i$. With $\mathrm{Val}_A(a)=\max_{x\in K}\sum_e\big(\prod_{i\in e}a_i\big)A_e(x_e)$ the weighted optimum, the **hindsight gain** is
--   $$\mathrm{Gap}_A(\zeta)=\mathbb E\,\mathrm{Val}_A(\zeta)-\mathrm{Val}_A(p).$$
--   The moment parameters are $M=\sum_i\mathbb E\zeta_i^2$, $\bar M=\sum_i(\mathbb E\zeta_i)^2$ and $\sigma_{\max}=\max_i\sqrt{\mathrm{Var}(\zeta_i)}$. For a variable $i$, the incident coefficient energy is $b_i^2=\sum_{e\ni i}\|A_e\|_F^2$, the sum of the squared coefficients of the interactions involving $i$.
--
--   These are the quantities of Theorems 1 and 8.
--
--   **Formalization Note** The expectation is the Bochner integral, which is $0$ for a non-integrable function; every theorem using `gap` therefore also asserts integrability of $\mathrm{Val}_A(\zeta)$. The maximum $\sigma_{\max}$ is a supremum over the finite nonempty index set. The published `Model`, `val`, `frobenius` and `weightMeans` are reused unchanged.
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, eq. (3) p.4, eq. (8) p.13, p.14, Theorem 8 p.17

import Mathlib
import Definitions.Def_HindsightGain_Uniform_fluctuations

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace HindsightGain.Uniform.Supplement

open HindsightGain.Uniform

/-- Equation (3)/(8): `Gap_A(ζ) = E Val_A(ζ) - Val_A(p)`, `p_i = E ζ_i`. -/
def gap {Ω : Type} [MeasurableSpace Ω] {n D r : ℕ} (M : Model n D r)
    (μ : Measure Ω) (ζ : Fin n → Ω → ℝ) : ℝ :=
  (∫ ω, val M (fun i => ζ i ω) ∂μ) - val M (weightMeans μ ζ)

/-- `M = Σ_i E ζ_i²` (pp.4, 14). -/
def secondMomentSum {Ω : Type} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ζ : Fin n → Ω → ℝ) : ℝ :=
  ∑ i, ∫ ω, ζ i ω ^ 2 ∂μ

/-- `M̄ = Σ_i (E ζ_i)²` (p.14). -/
def meanSqSum {Ω : Type} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ζ : Fin n → Ω → ℝ) : ℝ :=
  ∑ i, (∫ ω, ζ i ω ∂μ) ^ 2

/-- `σ_max = max_i √Var(ζ_i)`, a maximum over the finite index set (pp.4, 14). -/
def sigmaMax {Ω : Type} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ζ : Fin n → Ω → ℝ) : ℝ :=
  ⨆ i, Real.sqrt (variance (ζ i) μ)

/-- `b_i² = Σ_{e ∋ i} ‖A_e‖_F²` (p.17). -/
def incidentSq {n D r : ℕ} (M : Model n D r) (i : Fin n) : ℝ :=
  ∑ e : Edge n r, if i ∈ e.val then ∑ a : Fin r → Fin D, (M.A e a) ^ 2 else 0

end HindsightGain.Uniform.Supplement


