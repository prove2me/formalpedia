-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_QdetMemAdjSub
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_QdetMemAdjSub
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:59.806263+00:00
-- url     : https://prove2.me/theorems/9816ad3f-6f42-407b-ab54-c099bbe793d5
-- title:
--   Qdet Mem Adj Sub
-- statement:
--   Definitions and structural lemmas for Qdet Mem Adj Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CentralCharacters/QdetMemAdjSub.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_CentralScalar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.DSIC
open PI.DSInfCharCap
open scoped InnerProductSpace Matrix
def opOn {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (S : Submodule ℂ H) (f : H → H)
    (hst : ∀ v ∈ S, f v ∈ S) (hadd : ∀ v ∈ S, ∀ w ∈ S, f (v + w) = f v + f w)
    (hsm : ∀ (c : ℂ), ∀ v ∈ S, f (c • v) = c • f v) : Module.End ℂ S where
  toFun v := ⟨f v, hst v v.2⟩
  map_add' v w := Subtype.ext (hadd v v.2 w w.2)
  map_smul' c v := Subtype.ext (hsm c v v.2)
def conjHom {A : Type*} [Ring A] [Algebra ℂ A] (P P' : A) (h1 : P' * P = 1) (h2 : P * P' = 1) : A →ₐ[ℂ] A where
  toFun X := P * X * P'
  map_one' := by rw [mul_one, h2]
  map_mul' X Y := by
    calc P * (X * Y) * P' = P * X * (P' * P) * Y * P' := by rw [h1]; noncomm_ring
      _ = P * X * P' * (P * Y * P') := by noncomm_ring
  map_zero' := by rw [mul_zero, zero_mul]
  map_add' X Y := by rw [mul_add, add_mul]
  commutes' r := by
    show P * algebraMap ℂ A r * P' = algebraMap ℂ A r
    rw [← Algebra.commutes r P, mul_assoc, h2, mul_one]
def adjSub {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (S : Submodule ℂ H) :
    Subalgebra ℂ (Module.End ℂ S) where
  carrier := {X | ∃ X' : Module.End ℂ S, ∀ v w : S, ⟪((X v : S) : H), (w : H)⟫_ℂ = ⟪(v : H), ((X' w : S) : H)⟫_ℂ}
  mul_mem' := by
    rintro X Y ⟨X', hX⟩ ⟨Y', hY⟩
    refine ⟨Y' * X', fun v w => ?_⟩
    rw [Module.End.mul_apply, hX, hY, Module.End.mul_apply]
  add_mem' := by
    rintro X Y ⟨X', hX⟩ ⟨Y', hY⟩
    refine ⟨X' + Y', fun v w => ?_⟩
    rw [LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, Submodule.coe_add, inner_add_left,
      inner_add_right, hX, hY]
  algebraMap_mem' r := by
    refine ⟨algebraMap ℂ (Module.End ℂ S) ((starRingEnd ℂ) r), fun v w => ?_⟩
    rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, Submodule.coe_smul, Submodule.coe_smul,
      inner_smul_left, inner_smul_right]
end PI.UnitaryGroupMassFormula.DSIC


