-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantAlgebraComparison_BridgeHomFormula
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantAlgebraComparison_BridgeHomFormula
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T13:57:42.432085+00:00
-- url     : https://prove2.me/theorems/35ba71f4-351d-4a05-b32c-0fc0f38dd197
-- title:
--   Bridge Hom Formula
-- statement:
--   Definitions and structural lemmas for Bridge Hom Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantAlgebraComparison/BridgeHomFormula.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantAlgebraComparison_InvAlgOfSteps
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_L2_SG_AdBridge_ofHAFin_mem
import Theorems.Thm_Formalism_L2_SG_AdBridge_ofHAInf_mem
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
namespace PI.UnitaryGroupMassFormula.BridgeInvAlg
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge
theorem hmat_mul (I : AutInst) (g h : HAd I) : hmat I (g * h) = hmat I g * hmat I h := rfl
theorem hmat_one (I : AutInst) : hmat I 1 = 1 := rfl
theorem P_mul_inv (I : AutInst) (v : InfinitePlace I.F) : I.P v * (I.P v)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))
theorem P_inv_mul (I : AutInst) (v : InfinitePlace I.F) : (I.P v)⁻¹ * I.P v = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))
theorem ofHAInf_mul (I : AutInst) (g h : HAd I) (v : InfinitePlace I.F) :
    ofHAInf I (g * h) v = ofHAInf I g v * ofHAInf I h v := by
  unfold ofHAInf
  rw [hmat_mul, Matrix.map_mul]
  set A := (hmat I g).map (thetaV I v)
  set B := (hmat I h).map (thetaV I v)
  set P := I.P v
  calc P⁻¹ * (A * B) * P = P⁻¹ * A * (P * P⁻¹) * B * P := by
        rw [P_mul_inv]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = P⁻¹ * A * P * (P⁻¹ * B * P) := by simp only [Matrix.mul_assoc]
theorem ofHAInf_one (I : AutInst) (v : InfinitePlace I.F) : ofHAInf I 1 v = 1 := by
  unfold ofHAInf
  rw [hmat_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, P_inv_mul]
theorem ofHAFin_mul (I : AutInst) (g h : HAd I) :
    ofHAFin I (g * h) = ofHAFin I g * ofHAFin I h := by
  unfold ofHAFin
  rw [hmat_mul, Matrix.map_mul]
theorem ofHAFin_one (I : AutInst) : ofHAFin I 1 = 1 := by
  unfold ofHAFin
  rw [hmat_one, Matrix.map_one _ (map_zero _) (map_one _)]
def infU (I : AutInst) (h : HAd I) (v : InfinitePlace I.F) : Formalism.REAL.UJ (I.ε v) :=
  ⟨⟨ofHAInf I h v, ofHAInf I h⁻¹ v,
    by rw [← ofHAInf_mul, mul_inv_cancel, ofHAInf_one],
    by rw [← ofHAInf_mul, inv_mul_cancel, ofHAInf_one]⟩, ofHAInf_mem I h v⟩
def finU (I : AutInst) (h : HAd I) : I.Gf :=
  ⟨⟨ofHAFin I h, ofHAFin I h⁻¹,
    by rw [← ofHAFin_mul, mul_inv_cancel, ofHAFin_one],
    by rw [← ofHAFin_mul, inv_mul_cancel, ofHAFin_one]⟩, ofHAFin_mem I h⟩
def bridgeHom (I : AutInst) : HAd I →* I.GA where
  toFun h := (fun v => infU I h v, finU I h)
  map_one' := by
    refine Prod.ext (funext fun v => ?_) ?_
    · exact Subtype.ext (Units.ext (ofHAInf_one I v))
    · exact Subtype.ext (Units.ext (ofHAFin_one I))
  map_mul' g h := by
    refine Prod.ext (funext fun v => ?_) ?_
    · exact Subtype.ext (Units.ext (ofHAInf_mul I g h v))
    · exact Subtype.ext (Units.ext (ofHAFin_mul I g h))
end PI.UnitaryGroupMassFormula.BridgeInvAlg


