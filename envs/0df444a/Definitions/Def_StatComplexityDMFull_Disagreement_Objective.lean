-- Prove2me | Definitions.Def_StatComplexityDMFull_Disagreement_Objective
-- name    : StatComplexityDMFull_Disagreement_Objective
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:53:58.452235+00:00
-- url     : https://prove2.me/theorems/ccc45319-82a7-47f6-9b17-a29ac5290d00
-- title:
--   The square-loss dual DEC objective and the exact posterior bound
-- statement:
--   Let $\mu$ be a prior over model mean data $f^M$ with selected optimizers $\pi_M$. Let $\bar f:\Pi\to[0,1]$ be an external reference mean and let $p$ be a decision law independent of $M$. The square-loss divergence uses only the difference of means. For $\gamma>0$ define
--
--   $$J_\gamma(\mu,\bar f;p)=\mathbb E_{M\sim\mu}\mathbb E_{\pi\sim p}
--   [f^M(\pi_M)-f^M(\pi)-\gamma(f^M(\pi)-\bar f(\pi))^2],$$
--   $$\underline{\mathrm{dec}}^{\rm Sq}_\gamma(\mu,\bar f)
--   =\inf_{p\in\Delta(\Pi)}J_\gamma(\mu,\bar f;p).$$
--
--   Here $\Delta(\Pi)$ comprises every Radon Borel decision probability law. With $\rho_\mu=(M\mapsto\pi_M)_\#\mu$, also define
--
--   $$B_\gamma(\mu)=\inf_{\Delta>0}\left\{2\Delta+
--   \frac{24\log^2\gamma}{\gamma}\sup_{M\in\mathcal M}
--   \theta(\mathcal F_{\mathcal M}-f^M,\Delta,\gamma^{-1};\rho_\mu)\right\}.$$
--
--   These are computed from the mean data and the prior. Neither the objective nor the DEC is a free variable fixed by an assumed bound. The model supremum is inside the positive-scale infimum. For the bounded source data, $-\gamma\le J_\gamma\le1$; posterior sampling supplies an admissible decision law.
--
--   **Formalization Note** The objective is a real iterated integral. The DEC and $B_\gamma$ use extended-real extrema. All source values are finite for $\gamma\ge e$; no extremum is required to be attained.
-- source:
--   Foster, Kakade, Qian and Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3, p. 28, square-mean divergence; p. 45, (70), Theorem 6.2 and (72)

import Mathlib
import Definitions.Def_StatComplexityDMFull_Disagreement_RadonLaw
import Definitions.Def_StatComplexityDMFull_Disagreement_MeanModel
import Definitions.Def_StatComplexityDMFull_Disagreement_Coefficient

set_option autoImplicit false

namespace StatComplexityDMFull.Disagreement

/-- The true independent-model/decision objective of (70), using the square-mean divergence. -/
noncomputable def sqDecObjective {M A : Type*} [MeasurableSpace M] [MeasurableSpace A]
    (μ : MeasureTheory.Measure M) (D : MeanModel M A) (g : A → ℝ) (γ : ℝ)
    (p : MeasureTheory.Measure A) : ℝ :=
  ∫ m, (∫ a, D.mean m (D.optimal m) - D.mean m a - γ * (D.mean m a - g a) ^ 2 ∂p) ∂μ

/-- The prior-dependent dual DEC, with every source Radon decision law admissible. -/
noncomputable def sqDEC {M A : Type*} [MeasurableSpace M] [TopologicalSpace A]
    [MeasurableSpace A] (μ : MeasureTheory.Measure M) (D : MeanModel M A)
    (g : A → ℝ) (γ : ℝ) : EReal :=
  sInf {x : EReal | ∃ p : RadonLaw A, x = (sqDecObjective μ D g γ p.val : EReal)}

/-- The exact right-hand side of (72): the model supremum is inside the positive-scale infimum. -/
noncomputable def posteriorBound {M A : Type*} [MeasurableSpace M] [MeasurableSpace A]
    (μ : MeasureTheory.Measure M) (D : MeanModel M A) (γ : ℝ) : EReal :=
  ⨅ Δ : {x : ℝ // 0 < x}, ((2 * Δ.val : ℝ) : EReal) +
    ((24 * Real.log γ ^ 2 / γ : ℝ) : EReal) *
      (⨆ m : M, disagreementCoeff μ D.optimal (shiftClass (meanClass D) (D.mean m)) Δ.val γ⁻¹)

end StatComplexityDMFull.Disagreement


