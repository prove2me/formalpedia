-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:28:52.490736+00:00
-- url     : https://prove2.me/theorems/ce48e7e8-f67c-45cf-996a-7da544d48121
-- title:
--   Wirtinger Integration By Parts
-- statement:
--   Definitions and structural lemmas for Wirtinger Integration By Parts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
instance sigmaFinite_mu (β : ℂ) : SigmaFinite (mu β) := by unfold mu; infer_instance
theorem muPi_eq (β : ℂ) (ι : Type) [Fintype ι] :
    muPi β ι = (Real.toNNReal (‖β‖ / (2 * Real.pi))) ^ Fintype.card ι • (volume : Measure (ι → ℂ)) := by
  unfold muPi
  refine Measure.pi_eq fun s hs => ?_
  simp only [mu, Measure.smul_apply, volume_pi_pi, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]
instance (β : ℂ) (ι : Type) [Fintype ι] : IsFiniteMeasureOnCompacts (muPi β ι) := by
  rw [muPi_eq]; infer_instance
section
variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
end
def Bd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (f : E → W) (s : Set E) (x : E) (n : ℕ)
    (A P : ℝ) : Prop :=
  ∀ j ≤ n, ‖iteratedFDerivWithin ℝ j f s x‖ ≤ A * P ^ j
section Gen
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
end Gen
noncomputable def bk {d : ℕ} (g : (Fin d → ℂ) → ℂ) (k : Fin d) (x : Fin d → ℂ) : ℂ :=
  (∑ l, Complex.normSq (fderiv ℂ g x (Pi.single l 1)))⁻¹ • (starRingEnd ℂ) (fderiv ℂ g x (Pi.single k 1))
section Main
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {d : ℕ}
noncomputable def wirtL (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] {d : ℕ} (k : Fin d) :
    ((Fin d → ℂ) →L[ℝ] V) →L[ℝ] V :=
  (1 / 2 : ℂ) • (ContinuousLinearMap.apply ℝ V (Pi.single k (1 : ℂ) : Fin d → ℂ) -
    Complex.I • ContinuousLinearMap.apply ℝ V (Pi.single k Complex.I : Fin d → ℂ))
end Main
section Main2
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] {d : ℕ}
end Main2
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


