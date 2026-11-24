-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SmulPeriodMapMkZeroFstEqNegForm
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SmulPeriodMapMkZeroFstEqNegForm
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T13:13:29.593934+00:00
-- url     : https://prove2.me/theorems/b4cc547f-a308-4a35-86d3-956a75ba05ed
-- title:
--   Smul Period Map Mk Zero Fst Eq Neg Form
-- statement:
--   Definitions and structural lemmas for Smul Period Map Mk Zero Fst Eq Neg Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/SmulPeriodMapMkZeroFstEqNegForm.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Theorems.Thm_GlobalTheory_AnArc_EF_bijective
import Theorems.Thm_GlobalTheory_AnArc_EF_smul
import Theorems.Thm_GlobalTheory_AnArc_yLin_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
namespace GlobalTheory
namespace KerPerp
variable {O L Y : Type*} [Ring O] [AddCommGroup L] [Module O L] [AddCommGroup Y] [Module O Y]
  {bar : O → O} {EF : LinearMap.BilinForm ℤ L}
def kerPerp (hadj : ∀ (a : O) x x', EF (a • x) x' = EF x (bar a • x')) (y : L →ₗ[O] Y) : Submodule O L where
  carrier := {t | ∀ v, y v = 0 → EF t v = 0}
  zero_mem' v _ := by simp
  add_mem' {t t'} ht ht' v hv := by simp [ht v hv, ht' v hv]
  smul_mem' a t ht v hv := by rw [hadj]; exact ht _ (by simp [hv])
variable {hadj : ∀ (a : O) x x', EF (a • x) x' = EF x (bar a • x')} {y : L →ₗ[O] Y}
theorem apply_eq_of_eq {t : L} (ht : t ∈ kerPerp hadj y) {v v' : L} (h : y v = y v') : EF t v = EF t v' := by
  rw [← sub_eq_zero, ← map_sub]
  exact ht _ (by rw [map_sub, h, sub_self])
theorem exists_of_dual (hs : Function.Surjective EF) (φ : Module.Dual ℤ Y) :
    ∃ t ∈ kerPerp hadj y, ∀ v, -EF t v = φ (y v) := by
  obtain ⟨t, ht⟩ := hs (-(φ ∘ₗ y.toAddMonoidHom.toIntLinearMap))
  exact ⟨t, fun v hv => by simp [ht, hv], fun v => by simp [ht]⟩
variable (hadj)
def toDual (hy : Function.Surjective y) : kerPerp hadj y →ₗ[ℤ] Module.Dual ℤ Y :=
  LinearMap.mk₂ ℤ (fun t x => -EF t (Function.surjInv hy x))
    (fun _ _ _ => by simp [add_comm]) (fun _ _ _ => by simp)
    (fun t x x' => by
      rw [← neg_add, ← map_add]
      exact congrArg _ (apply_eq_of_eq t.2 (by simp [Function.surjInv_eq])))
    (fun k t x => by
      rw [smul_neg, ← map_zsmul]
      exact congrArg _ (apply_eq_of_eq t.2 (by simp [Function.surjInv_eq])))
@[simp] theorem toDual_apply (hy : Function.Surjective y) (t : kerPerp hadj y) (v : L) :
    toDual hadj hy t (y v) = -EF t v :=
  congrArg Neg.neg (apply_eq_of_eq t.2 (Function.surjInv_eq hy _))
theorem toDual_bijective (hb : Function.Bijective EF) (hy : Function.Surjective y) :
    Function.Bijective (toDual hadj hy) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro t ht
    refine Subtype.ext (hb.1 (LinearMap.ext fun v => ?_))
    have := toDual_apply hadj hy t v
    rw [ht] at this
    simpa using this
  · intro φ
    obtain ⟨t, ht, hφ⟩ := exists_of_dual (hadj := hadj) (y := y) hb.2 φ
    refine ⟨⟨t, ht⟩, LinearMap.ext fun x => ?_⟩
    obtain ⟨v, rfl⟩ := hy x
    rw [toDual_apply, hφ]
def equivDual (hb : Function.Bijective EF) (hy : Function.Surjective y) : kerPerp hadj y ≃ₗ[ℤ] Module.Dual ℤ Y :=
  LinearEquiv.ofBijective _ (toDual_bijective hadj hb hy)
@[simp] theorem equivDual_apply (hb : Function.Bijective EF) (hy : Function.Surjective y) (t : kerPerp hadj y)
    (v : L) : equivDual hadj hb hy t (y v) = -EF t v := toDual_apply hadj hy t v
theorem neg_apply_equivDual_symm (hb : Function.Bijective EF) (hy : Function.Surjective y) (φ : Module.Dual ℤ Y)
    (v : L) : -EF ((equivDual hadj hb hy).symm φ) v = φ (y v) := by
  rw [← equivDual_apply hadj hb hy, LinearEquiv.apply_symm_apply]
theorem equivDual_smul (hb : Function.Bijective EF) (hy : Function.Surjective y) (a : O) (t : kerPerp hadj y)
    (x : Y) : equivDual hadj hb hy (a • t) x = equivDual hadj hb hy t (bar a • x) := by
  obtain ⟨v, rfl⟩ := hy x
  rw [← map_smul y, equivDual_apply, equivDual_apply, Submodule.coe_smul, hadj]
variable {be : LinearMap.BilinForm ℤ Y}
def nilTo (hb : Function.Bijective EF) (hy : Function.Surjective y)
    (hbe : ∀ (a : O) x x', be (a • x) x' = be x (bar a • x')) : L →ₗ[O] kerPerp hadj y where
  toFun a := (equivDual hadj hb hy).symm (be (y a))
  map_add' a b := by simp
  map_smul' c a := (equivDual hadj hb hy).injective (LinearMap.ext fun x => by
    rw [RingHom.id_apply, equivDual_smul, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, map_smul, hbe])
theorem neg_apply_nilTo (hb : Function.Bijective EF) (hy : Function.Surjective y)
    (hbe : ∀ (a : O) x x', be (a • x) x' = be x (bar a • x')) (a b : L) :
    -EF (nilTo hadj hb hy hbe a) b = be (y a) (y b) := neg_apply_equivDual_symm hadj hb hy _ b
variable {hadj}
section Nil
variable {nn : L → L}
end Nil
end KerPerp
namespace AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
theorem nilTo_ne_zero {a : A.La} (ha : a.y ≠ 0) :
    KerPerp.nilTo A.EF_smul A.EF_bijective A.yLin_surjective A.be_adj a ≠ 0 := fun h => by
  have h1 := KerPerp.neg_apply_nilTo A.EF_smul A.EF_bijective A.yLin_surjective A.be_adj a a
  rw [h] at h1
  have h2 : (0 : ℤ) = A.be a.y a.y := by simpa using h1
  exact (A.be_pos _ ha).ne h2
example (c τ₀ : ℂ) : KerPerp.nilTo (gaussCM c τ₀).EF_smul (gaussCM c τ₀).EF_bijective
    (gaussCM c τ₀).yLin_surjective (gaussCM c τ₀).be_adj
    (La.mk (A := gaussCM c τ₀) (1 : GaussianInt) 0 0) ≠ 0 :=
  (gaussCM c τ₀).nilTo_ne_zero (one_ne_zero (α := GaussianInt))
end AnArc
end GlobalTheory


