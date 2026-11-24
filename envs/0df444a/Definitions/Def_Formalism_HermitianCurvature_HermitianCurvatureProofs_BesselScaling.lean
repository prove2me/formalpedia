-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselScaling
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselScaling
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T17:56:03.029668+00:00
-- url     : https://prove2.me/theorems/e48f9c61-54a9-4888-8e26-95a88e5936d2
-- title:
--   Bessel Scaling
-- statement:
--   Definitions and structural lemmas for Bessel Scaling, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BesselScaling.lean

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaBOfComponents
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.BesselScaling
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
theorem haar_smul {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) (c : ℝ≥0) (hc : 0 < c) :
    IsHaarOn U (c • μ) where
  conc := by
    rw [Measure.smul_apply, h.conc, smul_zero]
  left := fun a ha => by rw [Measure.map_smul, h.left a ha]
  right := fun a ha => by rw [Measure.map_smul, h.right a ha]
  finite_compact := fun K hK => by
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (h.finite_compact K hK)
  ne_zero := by
    intro h0
    apply h.ne_zero
    have h1 : (c • μ) Set.univ = 0 := by rw [h0]; rfl
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd (by exact_mod_cast h2 : c = 0) hc.ne'
    · exact Measure.measure_univ_eq_zero.mp h2
section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
def scaleG (D : RealPlaceData k r Wp Wq) (c : ℝ≥0) (hc : 0 < c) : RealPlaceData k r Wp Wq :=
  { D with μG := c • D.μG, haarG := haar_smul D.haarG c hc }
variable [FiniteDimensional ℂ Wq]
end
end Formalism.FourierDecayAlt.P.BesselScaling
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.BesselScaling
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
end Formalism.FourierDecayAlt.P.BesselScaling


