-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CompRel
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CompRel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:47:33.01408+00:00
-- url     : https://prove2.me/theorems/bb427370-3bc7-4f5b-8f8f-97cf6f001060
-- title:
--   Comp Rel
-- statement:
--   Definitions and structural lemmas for Comp Rel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/CompRel.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.HomCalc
variable {O O' O'' : Type} [CommRing O] [CommRing O'] [CommRing O''] {f : O →+* O'} {g : O' →+* O''}
  {N : NumD O} {N' : NumD O'} {N'' : NumD O''}
def comp (I : NumD.Hom f N N') (I' : NumD.Hom g N' N'') : NumD.Hom (g.comp f) N N'' where
  φ := I'.φ.comp I.φ
  h x := I'.h (I.φ x) * Units.map g.toMonoidHom (I.h x)
  h_one := by rw [map_one, I'.h_one, I.h_one, map_one, mul_one]
  θ_eq x y u := by
    have a := congrArg (fun v => Additive.ofMul (Units.map g.toMonoidHom v)) (I.θ_eq x y u)
    have b := congrArg Additive.ofMul (I'.θ_eq (I.φ x) (I.φ y) (I.φ u))
    have c : Units.map (g.comp f).toMonoidHom (N.θ x y u) =
      Units.map g.toMonoidHom (Units.map f.toMonoidHom (N.θ x y u)) := rfl
    apply Additive.ofMul.injective
    simp only [c, map_mul, ofMul_mul, MonoidHom.comp_apply] at a b ⊢
    linear_combination (norm := abel) a + b
  σ_eq x := by
    have a := congrArg (fun v => Additive.ofMul (Units.map g.toMonoidHom v)) (I.σ_eq x)
    have b := congrArg Additive.ofMul (I'.σ_eq (I.φ x))
    have c : Units.map (g.comp f).toMonoidHom (N.σ x) =
      Units.map g.toMonoidHom (Units.map f.toMonoidHom (N.σ x)) := rfl
    apply Additive.ofMul.injective
    simp only [c, map_mul, ofMul_mul, MonoidHom.comp_apply, map_inv I.φ] at a b ⊢
    linear_combination (norm := abel) a + b
  lam := I'.lam * Units.map g.toMonoidHom I.lam
  th_eq x := by
    rw [MonoidHom.comp_apply, I'.th_eq, I.th_eq]
    simp only [map_mul, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.comp_apply]
    ring
  e := I.e.trans I'.e
  c_eq χ := by rw [AddEquiv.trans_apply, I'.c_eq, I.c_eq]; rfl
  ψ_eq χ := by
    have c : Units.map (g.comp f).toMonoidHom (N.ψ χ) =
      Units.map g.toMonoidHom (Units.map f.toMonoidHom (N.ψ χ)) := rfl
    rw [c, ← I.ψ_eq, map_mul, ← I'.ψ_eq, I.c_eq, AddEquiv.trans_apply, mul_assoc]
def inv {M M' : NumD O} (I : NumD.Iso M' M) : NumD.Hom (RingHom.id O) M M' where
  φ := I.φ.symm.toMonoidHom
  h x := (I.h (I.φ.symm x))⁻¹
  h_one := by rw [map_one, I.h_one, inv_one]
  θ_eq x y u := by
    have a := congrArg Additive.ofMul (I.θ_eq (I.φ.symm x) (I.φ.symm y) (I.φ.symm u))
    show M'.θ (I.φ.symm x) (I.φ.symm y) (I.φ.symm u) * _ * _ * _ = M.θ x y u * _ * _ * _ * _
    apply Additive.ofMul.injective
    simp only [map_mul, ofMul_mul, ofMul_inv, MulEquiv.apply_symm_apply] at a ⊢
    linear_combination (norm := abel) -a
  σ_eq x := by
    have a := congrArg Additive.ofMul (I.σ_eq (I.φ.symm x))
    show M'.σ (I.φ.symm x) * _ = M.σ x * _
    apply Additive.ofMul.injective
    simp only [map_inv I.φ.symm, ofMul_mul, ofMul_inv, MulEquiv.apply_symm_apply] at a ⊢
    linear_combination (norm := abel) -a
  lam := I.lam⁻¹
  th_eq x := by
    have a := I.th_eq (I.φ.symm x)
    rw [MulEquiv.apply_symm_apply] at a
    show M'.th (I.φ.symm x) = _ * M.th x
    rw [a, ← mul_inv, Units.inv_mul_cancel_left]
  e := I.e.symm
  c_eq χ := by
    show _ = I.φ.symm _
    rw [MulEquiv.eq_symm_apply, ← I.c_eq, AddEquiv.apply_symm_apply]
  ψ_eq χ := by
    obtain ⟨χ, rfl⟩ := I.e.surjective χ
    show _ = M.ψ _
    rw [AddEquiv.symm_apply_apply, I.c_eq, MulEquiv.symm_apply_apply, ← I.ψ_eq, mul_inv_cancel_right]
end GlobalTheory.HomCalc
end


