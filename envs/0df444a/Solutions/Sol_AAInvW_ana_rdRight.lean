-- Prove2me | solution 1 for AAInvW.ana_rdRight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:53:29.520283+00:00
-- url     : https://prove2.me/submissions/334b221b-39b1-4b8f-abee-143362ed060d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SmoothLinear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_ConjugatedGeneratorGlRelation
import Theorems.Thm_AAInvW_ana_mul_inv
import Theorems.Thm_AAInvW_isUnit_of_inUH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace AAInvW
theorem _root_.solution (hH : HInvol H) {f : Matrix (Fin n) (Fin n) ℂ → E} {X s g : Matrix (Fin n) (Fin n) ℂ}
    (hs : inUH H s) : RdV X (fun x => f (x * s)) g = RdV (s⁻¹ * X * s) f (g * s) := by
  unfold RdV
  congr 1
  funext t
  dsimp only
  congr 1
  rw [show ((t : ℂ) • (s⁻¹ * X * s)) = s⁻¹ * ((t : ℂ) • X) * s by rw [Matrix.mul_smul, Matrix.smul_mul],
    Matrix.exp_conj' s _ (isUnit_of_inUH hH hs)]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc s s⁻¹, ana_mul_inv hH hs, Matrix.one_mul]
end AAInvW
