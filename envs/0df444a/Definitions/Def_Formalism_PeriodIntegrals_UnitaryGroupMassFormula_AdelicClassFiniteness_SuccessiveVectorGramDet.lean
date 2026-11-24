-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SuccessiveVectorGramDet
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SuccessiveVectorGramDet
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T14:09:16.734071+00:00
-- url     : https://prove2.me/theorems/a74abbd7-5754-4114-a5fc-f18e856793cf
-- title:
--   Successive Vector Gram Det
-- statement:
--   Definitions and structural lemmas for Successive Vector Gram Det, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SuccessiveVectorGramDet.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartShortOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSmulRight
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_P2M_PIW_AdelClassFin_hform_add_left__8d9208e82c86
import Theorems.Thm_P2M_PIW_AdelClassFin_hform_add_right__73a64fb2bbe8
import Theorems.Thm_P2M_PIW_AdelClassFin_hform_smul_left__345360160129
import Theorems.Thm_P2M_PIW_AdelClassFin_hform_smul_right__f0caf7c17a43
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace PIW.AdelClassFin
open Formalism.UG NumberField
open scoped Matrix
section GD
variable {E : Type} [Field E] [NumberField E] [StarRing E] {m : ℕ} (J : Matrix (Fin m) (Fin m) E)
theorem gd_qsmul (q : ℚ) (x : Fin m → E) : q • x = ((q : E)) • x := by
  ext i
  simp [Rat.smul_def]
theorem gd_star_rat (q : ℚ) : star ((q : E)) = (q : E) := by
  first
    | exact star_ratCast q
    | simpa [starRingEnd_apply] using map_ratCast (starRingEnd E) q
def gdLeft (y : Fin m → E) : (Fin m → E) →ₗ[ℚ] ℚ where
  toFun x := Algebra.trace ℚ E (hform (starRingEnd E) J x y)
  map_add' x x' := by rw [hform_add_left', map_add]
  map_smul' q x := by
    rw [gd_qsmul, hform_smul_left', gd_star_rat, RingHom.id_apply, smul_eq_mul, ← Rat.smul_def, map_smul,
      smul_eq_mul]
def gdRight (x : Fin m → E) : (Fin m → E) →ₗ[ℚ] ℚ where
  toFun y := Algebra.trace ℚ E (hform (starRingEnd E) J x y)
  map_add' y y' := by rw [hform_add_right', map_add]
  map_smul' q y := by
    rw [gd_qsmul, hform_smul_right', RingHom.id_apply, smul_eq_mul, ← Rat.smul_def, map_smul, smul_eq_mul]
end GD
end PIW.AdelClassFin
end


