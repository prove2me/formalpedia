-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T12:57:31.83486+00:00
-- url     : https://prove2.me/theorems/b49f5c51-22e6-4a2e-8986-3865a883d3a6
-- title:
--   Continuous UMat Apply
-- statement:
--   Definitions and structural lemmas for Continuous UMat Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/ContinuousUMatApply.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
open Matrix
namespace PI.ScMuExists.UnitaryGroupMassFormula
section Lin
variable {n r : ℕ}
theorem spanLt_mono (e : Fin r → Fin n → ℂ) {a b : ℕ} (h : a ≤ b) : spanLt e a ≤ spanLt e b := by
  unfold spanLt
  exact Submodule.span_mono (Set.image_mono fun b (hb : b.1 < a) => lt_of_lt_of_le hb h)
theorem mulVec_eq_sub_add (g : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    g *ᵥ x = (g - 1) *ᵥ x + x := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]
theorem sub_mem_spanLt {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : InS e z g) (a : ℕ) {x : Fin n → ℂ} (hx : x ∈ spanLt e a) : (g - 1) *ᵥ x ∈ spanLt e a := by
  have key : spanLt e a ≤ (spanLt e a).comap (Matrix.mulVecLin (g - 1)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, hb, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
    exact spanLt_mono e (le_of_lt hb) (hg.1 b)
  exact key hx
theorem mem_spanLt_of_inS {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : InS e z g) (a : ℕ) {x : Fin n → ℂ} (hx : x ∈ spanLt e a) : g *ᵥ x ∈ spanLt e a := by
  rw [mulVec_eq_sub_add g x]
  exact Submodule.add_mem _ (sub_mem_spanLt hg a hx) hx
theorem inv_preserves {W : Submodule ℂ (Fin n → ℂ)} {g g' : Matrix (Fin n) (Fin n) ℂ} (h1 : g' * g = 1)
    (hW : ∀ x ∈ W, g *ᵥ x ∈ W) : ∀ x ∈ W, g' *ᵥ x ∈ W := by
  let f : W →ₗ[ℂ] W := (Matrix.mulVecLin g).restrict (fun x hx => hW x hx)
  have hf : Function.Injective f := by
    intro a b hab
    have h2 : g *ᵥ (a : Fin n → ℂ) = g *ᵥ (b : Fin n → ℂ) := congrArg Subtype.val hab
    have h3 := congrArg (fun y => g' *ᵥ y) h2
    simp only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at h3
    exact Subtype.ext h3
  have hs : Function.Surjective f := LinearMap.injective_iff_surjective.mp hf
  intro x hx
  obtain ⟨y, hy⟩ := hs ⟨x, hx⟩
  have hy' : g *ᵥ (y : Fin n → ℂ) = x := congrArg Subtype.val hy
  rw [← hy', Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  exact y.2
theorem mul_sub_one_mulVec (g g' : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    (g * g' - 1) *ᵥ x = g *ᵥ ((g' - 1) *ᵥ x) + (g - 1) *ᵥ x := by
  simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, mul_sub, mul_one,
    Matrix.one_mulVec] <;> abel
theorem inv_sub_one_mulVec {g g' : Matrix (Fin n) (Fin n) ℂ} (h1 : g' * g = 1) (x : Fin n → ℂ) :
    (g' - 1) *ᵥ x = -(g' *ᵥ ((g - 1) *ᵥ x)) := by
  simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec,
    neg_sub]
theorem inS_one (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : InS e z 1 := by
  unfold InS
  refine ⟨fun a => ?_, ?_⟩ <;> simp
theorem inS_mul {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {g g' : Matrix (Fin n) (Fin n) ℂ}
    (hg : InS e z g) (hg' : InS e z g') : InS e z (g * g') := by
  refine ⟨fun a => ?_, ?_⟩
  · rw [mul_sub_one_mulVec]
    exact Submodule.add_mem _ (mem_spanLt_of_inS hg _ (hg'.1 a)) (hg.1 a)
  · rw [mul_sub_one_mulVec]
    exact Submodule.add_mem _ (mem_spanLt_of_inS hg _ hg'.2) hg.2
theorem inS_inv {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {g g' : Matrix (Fin n) (Fin n) ℂ}
    (hg : InS e z g) (h1 : g' * g = 1) : InS e z g' := by
  have hp : ∀ (a : ℕ), ∀ x ∈ spanLt e a, g' *ᵥ x ∈ spanLt e a := fun a =>
    inv_preserves h1 (fun x hx => mem_spanLt_of_inS hg a hx)
  refine ⟨fun a => ?_, ?_⟩
  · rw [inv_sub_one_mulVec h1]
    exact Submodule.neg_mem _ (hp _ _ (hg.1 a))
  · rw [inv_sub_one_mulVec h1]
    exact Submodule.neg_mem _ (hp _ _ hg.2)
theorem inN_one (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : InN ε e z 1 := by
  unfold InN
  exact ⟨inS_one e z, fun y _ => by simp⟩
theorem inN_mul {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {g g' : Matrix (Fin n) (Fin n) ℂ}
    (hg : InN ε e z g) (hg' : InN ε e z g') : InN ε e z (g * g') := by
  refine ⟨inS_mul hg.1 hg'.1, fun y hy => ?_⟩
  rw [mul_sub_one_mulVec]
  exact Submodule.add_mem _ (mem_spanLt_of_inS hg.1 _ (hg'.2 y hy)) (hg.2 y hy)
theorem inN_inv {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {g g' : Matrix (Fin n) (Fin n) ℂ}
    (hg : InN ε e z g) (h1 : g' * g = 1) : InN ε e z g' := by
  refine ⟨inS_inv hg.1 h1, fun y hy => ?_⟩
  rw [inv_sub_one_mulVec h1]
  exact Submodule.neg_mem _
    (inv_preserves h1 (fun x hx => mem_spanLt_of_inS hg.1 r hx) _ (hg.2 y hy))
end Lin
section Inst
variable (I : Formalism.MainNotions.S.AutInst)
theorem uMat_mul {n : ℕ} {ε : Fin n → Bool} (g h : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.uMat (g * h) = Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat h := rfl
theorem uMat_one {n : ℕ} {ε : Fin n → Bool} : Formalism.MainNotions.S.uMat (1 : Formalism.REAL.UJ ε) = 1 := rfl
theorem uMat_inv_mul {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.uMat g⁻¹ * Formalism.MainNotions.S.uMat g = 1 := by
  rw [← uMat_mul, inv_mul_cancel, uMat_one]
variable {r : ℕ}
def NSub (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Subgroup I.Ginf where
  carrier := Ninf I e z
  one_mem' := fun v => by
    show InN _ _ _ (Formalism.MainNotions.S.uMat (1 : Formalism.REAL.UJ (I.ε v)))
    rw [uMat_one]; exact inN_one _ _ _
  mul_mem' := fun {a b} ha hb v => by
    show InN _ _ _ (Formalism.MainNotions.S.uMat (a v * b v))
    rw [uMat_mul]; exact inN_mul (ha v) (hb v)
  inv_mem' := fun {a} ha v => by
    show InN _ _ _ (Formalism.MainNotions.S.uMat ((a v)⁻¹))
    exact inN_inv (ha v) (uMat_inv_mul (a v))
def HSub (S : Set (Fin I.n → I.E)) : Subgroup I.Ginf where
  carrier := Hset I S
  one_mem' := fun v x _ => by
    show Formalism.MainNotions.S.uMat (1 : Formalism.REAL.UJ (I.ε v)) *ᵥ _ = _
    rw [uMat_one, Matrix.one_mulVec]
  mul_mem' := fun {a b} ha hb v x hx => by
    show Formalism.MainNotions.S.uMat (a v * b v) *ᵥ _ = _
    rw [uMat_mul, ← Matrix.mulVec_mulVec, hb v x hx, ha v x hx]
  inv_mem' := fun {a} ha v x hx => by
    show Formalism.MainNotions.S.uMat ((a v)⁻¹) *ᵥ _ = _
    conv_lhs => rw [← ha v x hx]
    rw [Matrix.mulVec_mulVec, uMat_inv_mul, Matrix.one_mulVec]
end Inst
end PI.ScMuExists.UnitaryGroupMassFormula


