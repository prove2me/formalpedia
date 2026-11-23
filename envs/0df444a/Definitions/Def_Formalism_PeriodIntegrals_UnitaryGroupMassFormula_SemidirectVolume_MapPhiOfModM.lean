-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_MapPhiOfModM
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_MapPhiOfModM
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:19:53.840801+00:00
-- url     : https://prove2.me/theorems/9e12750d-8387-43f9-882f-7199edb4de34
-- title:
--   Map Phi Of Mod M
-- statement:
--   Definitions and structural lemmas for Map Phi Of Mod M, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/MapPhiOfModM.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoAFTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolSemiDirect.W.Cj
open MeasureTheory Measure
open scoped NNReal
section Gen
variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A]
  [BorelSpace A] {k : ℕ}
def phi (X : GL (Fin k) A) : (Fin k → A) ≃ₜ+ (Fin k → A) where
  toFun v := (X : Matrix (Fin k) (Fin k) A).mulVec v
  invFun v := ((X⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A).mulVec v
  left_inv v := by
    simp only [Matrix.mulVec_mulVec]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  right_inv v := by
    simp only [Matrix.mulVec_mulVec]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  map_add' v w := Matrix.mulVec_add _ v w
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id
def modM (X : GL (Fin k) A) : ℝ≥0 := addEquivAddHaarChar (phi X)
end Gen
end PI.VolSemiDirect.W.Cj


