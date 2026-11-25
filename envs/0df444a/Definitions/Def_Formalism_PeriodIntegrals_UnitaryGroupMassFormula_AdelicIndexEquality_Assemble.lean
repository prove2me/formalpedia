-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Assemble
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Assemble
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T11:42:54.024039+00:00
-- url     : https://prove2.me/theorems/e748096b-4b6d-5ed9-a4b8-07a78dd0c959
-- title:
--   Assemble
-- statement:
--   Definitions and structural lemmas for Assemble, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/Assemble.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQOneOfClosure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQEqOneOfMemNormalizer
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_modQ_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_modQ_one
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
namespace PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S
section Lift
variable (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
def liftFn (hL : LiftU) (g : Uv I v) : I.Gf := Classical.choose (hL I v g g.2)
theorem liftFn_spec (hL : LiftU) (g : Uv I v) :
    matV I v ((liftFn I v hL g : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) = g ∧ SuppAt I v (liftFn I v hL g) :=
  Classical.choose_spec (hL I v g g.2)
theorem eq_liftFn (hL : LiftU) (hJ : MatVInj) (g : Uv I v) (y : I.Gf)
    (hy : matV I v (y : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) = g) (hs : SuppAt I v y) :
    y = liftFn I v hL g := by
  apply hJ I
  intro w
  by_cases hw : w = v
  · rw [hw, hy, (liftFn_spec I v hL g).1]
  · rw [hs w hw, (liftFn_spec I v hL g).2 w hw]
def liftHom (hL : LiftU) (hJ : MatVInj) : Uv I v →* I.Gf where
  toFun := liftFn I v hL
  map_one' := by
    symm
    apply eq_liftFn I v hL hJ 1 1
    · simp
    · intro w _
      simp
  map_mul' := by
    intro g h
    symm
    apply eq_liftFn I v hL hJ (g * h)
    · simp only [Subgroup.coe_mul, map_mul, Subgroup.coe_mul]
      rw [(liftFn_spec I v hL g).1, (liftFn_spec I v hL h).1]
    · intro w hw
      simp only [Subgroup.coe_mul, map_mul]
      rw [(liftFn_spec I v hL g).2 w hw, (liftFn_spec I v hL h).2 w hw, one_mul]
def chiV (hC : KComm) (hL : LiftU) (hJ : MatVInj) : Uv I v →* ℚ where
  toFun g := modQ (PI.AdIndexEq.Ksub I) (liftHom I v hL hJ g)
  map_one' := by simp [modQ_one]
  map_mul' g h := by simp only [map_mul]; exact modQ_mul _ (hC I) _ _
end Lift
end PI.UnitaryGroupMassFormula.AdIndexEq
end


