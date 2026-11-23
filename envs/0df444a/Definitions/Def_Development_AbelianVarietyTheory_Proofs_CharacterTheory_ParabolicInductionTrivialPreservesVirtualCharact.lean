-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ParabolicInductionTrivialPreservesVirtualCharact
-- name    : Development_AbelianVarietyTheory_Proofs_CharacterTheory_ParabolicInductionTrivialPreservesVirtualCharact
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:12:52.452059+00:00
-- url     : https://prove2.me/theorems/e4df983a-dc8c-4e0b-b19d-0c905bc967ff
-- title:
--   Parabolic Induction Trivial Preserves Virtual Charact
-- statement:
--   Definitions and structural lemmas for Parabolic Induction Trivial Preserves Virtual Charact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ParabolicInductionTrivialPreservesVirtualCharact.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinearStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
noncomputable section
namespace GlobalTheory.ParabVirt
variable {F : Type} [Field F] {n : ℕ}
def lin (x : GL (Fin n) F) : (Fin n → F) ≃ₗ[F] (Fin n → F) :=
  LinearEquiv.ofLinear (Matrix.toLin' (x : Matrix (Fin n) (Fin n) F))
    (Matrix.toLin' ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])
theorem lin_apply (x : GL (Fin n) F) (v : Fin n → F) :
    lin x v = Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v := rfl
open Polynomial in
variable {F : Type} [Field F] {n : ℕ} in
theorem _root_.GlobalTheory.ParabVirt.lin_mul (x y : GL (Fin n) F) (v : Fin n → F) :
    _root_.GlobalTheory.ParabVirt.lin (x * y) v =
      _root_.GlobalTheory.ParabVirt.lin x (_root_.GlobalTheory.ParabVirt.lin y v) := by
  simp only [_root_.GlobalTheory.ParabVirt.lin_apply, Units.val_mul,
    Matrix.toLin'_mul_apply]
open Polynomial in
variable {F : Type} [Field F] {n : ℕ} in
theorem _root_.GlobalTheory.ParabVirt.lin_one (v : Fin n → F) :
    _root_.GlobalTheory.ParabVirt.lin (1 : GL (Fin n) F) v = v := by
  simp [_root_.GlobalTheory.ParabVirt.lin_apply]
theorem lin_inv (x : GL (Fin n) F) (v : Fin n → F) : lin x⁻¹ v = (lin x).symm v := rfl
open Polynomial in
variable {F : Type} [Field F] {n : ℕ} in
theorem _root_.GlobalTheory.ParabVirt.map_eq_of_stable (x : GL (Fin n) F)
    (W : Submodule F (Fin n → F)) (h : ∀ v ∈ W, _root_.GlobalTheory.ParabVirt.lin x v ∈ W) :
    W.map (_root_.GlobalTheory.ParabVirt.lin x).toLinearMap = W := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq _ _)
  rintro _ ⟨v, hv, rfl⟩
  exact h v hv
def stab (W : Submodule F (Fin n → F)) : Subgroup (GL (Fin n) F) where
  carrier := {x | ∀ v ∈ W, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W}
  one_mem' := fun v hv => by rw [← lin_apply, lin_one]; exact hv
  mul_mem' := fun {x y} hx hy v hv => by
    rw [← lin_apply, lin_mul]; exact hx _ (hy v hv)
  inv_mem' := fun {x} hx v hv => by
    rw [← lin_apply, lin_inv]
    rw [← map_eq_of_stable x W hx] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    simpa using hw
def resMat {a : ℕ} (W : Submodule F (Fin n → F)) (e : W ≃ₗ[F] (Fin a → F)) :
    stab W →* Matrix (Fin a) (Fin a) F where
  toFun h := LinearMap.toMatrix'
    (e.conj ((Matrix.toLin' ((h : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)).restrict h.2))
  map_one' := by
    rw [← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun v => ?_
    rw [LinearEquiv.conj_apply_apply, ← LinearEquiv.eq_symm_apply]
    ext1
    simp
  map_mul' x y := by
    rw [← LinearMap.toMatrix'_comp]
    congr 1
    refine LinearMap.ext fun v => ?_
    simp only [LinearEquiv.conj_apply_apply, LinearMap.comp_apply, LinearEquiv.symm_apply_apply]
    congr 1
    ext1
    exact lin_mul x.1 y.1 _
end GlobalTheory.ParabVirt


