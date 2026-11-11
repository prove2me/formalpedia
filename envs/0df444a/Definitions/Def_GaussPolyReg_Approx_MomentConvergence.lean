-- Prove2me | Definitions.Def_GaussPolyReg_Approx_MomentConvergence
-- name    : GaussPolyReg_Approx_MomentConvergence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:39:40.365919+00:00
-- url     : https://prove2.me/theorems/ed9c609e-a968-4d3a-9a0c-017b95aeb6b4
-- title:
--   Mixed-moment and Wasserstein convergence interface
-- statement:
--   For random vectors $P_n$ and $P$ on probability spaces, the moment-upgrade predicate requires, for every tuple of nonnegative integer exponents $a$, integrability of the corresponding mixed monomials and
--
--   $$\mathbb E\prod_i P_{n,i}^{a_i}\longrightarrow\mathbb E\prod_i P_i^{a_i}.$$
--
--   For every real $r\ge1$ it also requires finite $r$th absolute moments of the Euclidean norms and $W_r(\operatorname{Law}(P_n),\operatorname{Law}(P))\to0$. The limit probability space is arbitrary.
--
--   This is a shared name for all conclusions of Lemma A.4. It supplies no convergence theorem or assumed moment bound.
-- source:
--   Chris Jones, Regularity lemma for Gaussian polynomials, STOC 2027 submission #1637 (October 2026), Lemma A.4 and its proof, p.17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1637.pdf

import Mathlib
import Definitions.Def_GaussPolyReg_Approx_Chaos

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace GaussPolyReg.Approx

/-- The full conclusion of A.4: finite mixed moments, their convergence, every finite
real-order absolute moment, and convergence in every W_r, r ≥ 1. -/
def MomentUpgrade {Ω₀ Ω : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω]
    (μ₀ : Measure Ω₀) (μ : Measure Ω) {k : ℕ}
    (p : ℕ → Fin k → Ω₀ → ℝ) (P : Fin k → Ω → ℝ) : Prop :=
  (∀ a : Fin k → ℕ,
    (∀ n, Integrable (fun x => ∏ i, (p n i x) ^ a i) μ₀) ∧
    Integrable (fun x => ∏ i, (P i x) ^ a i) μ ∧
    Tendsto (fun n => ∫ x, ∏ i, (p n i x) ^ a i ∂μ₀) atTop
      (𝓝 (∫ x, ∏ i, (P i x) ^ a i ∂μ))) ∧
  (∀ r : ℝ, 1 ≤ r →
    (∀ n, Integrable (fun x => ‖vectorOf (p n) x‖ ^ r) μ₀) ∧
    Integrable (fun x => ‖vectorOf P x‖ ^ r) μ ∧
    Tendsto (fun n => wasserstein r (μ₀.map (vectorOf (p n))) (μ.map (vectorOf P)))
      atTop (𝓝 0))

end GaussPolyReg.Approx


