-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondCoordinateVectorNsmul
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondCoordinateVectorNsmul
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T14:16:13.389633+00:00
-- url     : https://prove2.me/theorems/64ea3a5d-cb0b-4e97-bdb3-2a05fae8ca7d
-- title:
--   Second Coordinate Vector Nsmul
-- statement:
--   Definitions and structural lemmas for Second Coordinate Vector Nsmul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/SecondCoordinateVectorNsmul.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondProjectionSplitEquiv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_FinKW_LocTo_ov_smul_eq
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
namespace PI.UnitaryGroupMassFormula.ScXuExists.BrB
open NumberField IsDedekindDomain Matrix PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.ScXuExists
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists
abbrev LL (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) : Submodule (OV I v) (Fin I.n → RV I v) :=
  Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))
def vecqL (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (q : RV I v →+* KV I v)
    (hq : ∀ c, q (algebraMap (KV I v) (RV I v) c) = c) :
    (Fin I.n → RV I v) →ₗ[OV I v] (Fin I.n → KV I v) where
  toFun x i := q (x i)
  map_add' x y := by funext i; simp
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [PI.FinKW.LocTo.ov_smul_eq, map_mul]
    have e : ((c : KV I v) ⊗ₜ[I.F] (1 : I.E)) = algebraMap (KV I v) (RV I v) (c : KV I v) := by
      simp [Algebra.TensorProduct.algebraMap_apply]
    rw [e, hq]
    rfl
end PI.UnitaryGroupMassFormula.ScXuExists.BrB


