-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_biCech_preimageFamily_equiv_tensor_cochain_pinned
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/410f25cb-1a1c-52cc-9973-73c9dc4b78f7

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BiCech
import Definitions.Def_AlgebraicGeometry_BoundedCochainTensor
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

import Theorems.Thm_AlgebraicGeometry_Scheme_Pullback_isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_biCech_preimageFamily_equiv_tensor_cochain_pinned
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 32000000

open CategoryTheory CategoryTheory.Limits TensorProduct AlgebraicGeometry

universe u

namespace KbAux

def piUncurry (R : Type u) [Semiring R] {ι κ : Type u} (M : ι → κ → Type u) [∀ i j, AddCommMonoid (M i j)] [∀ i j, Module R (M i j)] :
    (∀ i, ∀ j, M i j) ≃ₗ[R] (∀ p : ι × κ, M p.1 p.2) where
  toFun f p := f p.1 p.2
  invFun g i j := g (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[scoped simp] theorem piUncurry_apply (R : Type u) [Semiring R] {ι κ : Type u} (M : ι → κ → Type u) [∀ i j, AddCommMonoid (M i j)]
    [∀ i j, Module R (M i j)] (f : ∀ i, ∀ j, M i j) (p : ι × κ) : piUncurry R M f p = f p.1 p.2 := rfl

def eqTransport {R : Type u} [CommRing R] {Z : Scheme.{u}} {π : Z ⟶ Spec (.of R)} (F : OModulePresheaf π)
    {W W' : Z.Opens} (h : W' = W) : F.obj W ≃ₗ[R] F.obj W' :=
  LinearEquiv.ofLinear (F.res h.le) (F.res h.ge)
    (by rw [← OModulePresheaf.res_comp]; exact F.res_refl _)
    (by rw [← OModulePresheaf.res_comp]; exact F.res_refl _)

@[scoped simp] theorem eqTransport_apply {R : Type u} [CommRing R] {Z : Scheme.{u}} {π : Z ⟶ Spec (.of R)} (F : OModulePresheaf π)
    {W W' : Z.Opens} (h : W' = W) (x : F.obj W) : eqTransport F h x = F.res h.le x := rfl

end KbAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_biCech_preimageFamily_equiv_tensor_cochain_pinned.KbAux"

open KbAux

theorem solution
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of k)) (πY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated πX] [IsSeparated πY]
    (𝔘 : X.OrderedAffineCover) (𝔙 : Y.OrderedAffineCover) :
    ∃ e : ∀ p q : ℕ,
        OModulePresheaf.BiCech.C (OModulePresheaf.unit (pullback.fst πX πY ≫ πX))
            (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY)) p q ≃ₗ[k]
          ((OModulePresheaf.unit πX).cochain 𝔘 p ⊗[k] (OModulePresheaf.unit πY).cochain 𝔙 q),

      (∀ (p q : ℕ) (c : OModulePresheaf.BiCech.C (OModulePresheaf.unit (pullback.fst πX πY ≫ πX))
            (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY)) p q),
        e (p + 1) q (OModulePresheaf.BiCech.dH (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)) _ _ p q c) =
          ((OModulePresheaf.unit πX).d 𝔘 p).rTensor _ (e p q c)) ∧
      (∀ (p q : ℕ) (c : OModulePresheaf.BiCech.C (OModulePresheaf.unit (pullback.fst πX πY ≫ πX))
            (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY)) p q),
        e p (q + 1) (OModulePresheaf.BiCech.dV (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)) _ _ p q c) =
          ((OModulePresheaf.unit πY).d 𝔙 q).lTensor _ (e p q c)) ∧

      (∀ (p q : ℕ) (α : (OModulePresheaf.unit πX).cochain 𝔘 p) (β : (OModulePresheaf.unit πY).cochain 𝔙 q)
          (s : 𝔘.Idx p) (t : 𝔙.Idx q),
        (e p q).symm (α ⊗ₜ[k] β) (s, t) =
          ((pullback πX πY).presheaf.map (homOfLE (inf_le_left.trans
              (le_of_eq (Scheme.OrderedAffineCover.preimage_iInf_fin (pullback.fst πX πY) (fun j => 𝔘.U (s.1 j))).symm))).op).hom
            (((pullback.fst πX πY).app (𝔘.inter s)).hom (α s)) *
          ((pullback πX πY).presheaf.map (homOfLE (inf_le_right.trans
              (le_of_eq (Scheme.OrderedAffineCover.preimage_iInf_fin (pullback.snd πX πY) (fun j => 𝔙.U (t.1 j))).symm))).op).hom
            (((pullback.snd πX πY).app (𝔙.inter t)).hom (β t))) := by
  classical

  have hbox : ∀ {p q : ℕ} (s : 𝔘.Idx p) (t : 𝔙.Idx q),
      (𝔘.preimageFamily (pullback.fst πX πY)).inter s ⊓ (𝔙.preimageFamily (pullback.snd πX πY)).inter t =
        pullback.fst πX πY ⁻¹ᵁ 𝔘.inter s ⊓ pullback.snd πX πY ⁻¹ᵁ 𝔙.inter t := by
    intro p q s t
    change (⨅ j, pullback.fst πX πY ⁻¹ᵁ 𝔘.U (s.1 j)) ⊓ (⨅ j, pullback.snd πX πY ⁻¹ᵁ 𝔙.U (t.1 j)) = _
    rw [← Scheme.OrderedAffineCover.preimage_iInf_fin, ← Scheme.OrderedAffineCover.preimage_iInf_fin]
    rfl

  have box : ∀ (p q : ℕ) (s : 𝔘.Idx p) (t : 𝔙.Idx q),
      ∃ E : ((OModulePresheaf.unit πX).obj (𝔘.inter s) ⊗[k] (OModulePresheaf.unit πY).obj (𝔙.inter t)) ≃ₗ[k]
          (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).obj
            ((𝔘.preimageFamily (pullback.fst πX πY)).inter s ⊓ (𝔙.preimageFamily (pullback.snd πX πY)).inter t),
        ∀ (a : (OModulePresheaf.unit πX).obj (𝔘.inter s)) (b : (OModulePresheaf.unit πY).obj (𝔙.inter t)),
          E (a ⊗ₜ[k] b) =
          ((pullback πX πY).presheaf.map (homOfLE (inf_le_left.trans
              (le_of_eq (Scheme.OrderedAffineCover.preimage_iInf_fin (pullback.fst πX πY) (fun j => 𝔘.U (s.1 j))).symm))).op).hom
            (((pullback.fst πX πY).app (𝔘.inter s)).hom a) *
          ((pullback πX πY).presheaf.map (homOfLE (inf_le_right.trans
              (le_of_eq (Scheme.OrderedAffineCover.preimage_iInf_fin (pullback.snd πX πY) (fun j => 𝔙.U (t.1 j))).symm))).op).hom
            (((pullback.snd πX πY).app (𝔙.inter t)).hom b) := by
    intro p q s t
    letI iU := Scheme.TwoAffineOpenCover.algebraOfHom πX (𝔘.inter s)
    letI iV := Scheme.TwoAffineOpenCover.algebraOfHom πY (𝔙.inter t)
    letI iE := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.fst πX πY ≫ πX) (pullback.fst πX πY ⁻¹ᵁ 𝔘.inter s ⊓ pullback.snd πX πY ⁻¹ᵁ 𝔙.inter t)
    obtain ⟨-, e, he⟩ := AlgebraicGeometry.Scheme.Pullback.isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage
      πX πY (𝔘.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter πX 𝔘 s) (𝔙.inter t) (Scheme.OrderedAffineCover.isAffineOpen_inter πY 𝔙 t)
    refine ⟨e.toLinearEquiv.trans (eqTransport (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)) (hbox s t)), fun a b => ?_⟩
    change (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).res (hbox s t).le (e (a ⊗ₜ[k] b)) = _
    rw [he]
    change ((pullback πX πY).presheaf.map (homOfLE _).op).hom (_ * _) = _
    rw [map_mul]
    congr 1
    · change (((pullback.fst πX πY).app (𝔘.inter s) ≫ (pullback πX πY).presheaf.map (homOfLE _).op) ≫ (pullback πX πY).presheaf.map (homOfLE _).op).hom a =
        ((pullback.fst πX πY).app (𝔘.inter s) ≫ (pullback πX πY).presheaf.map (homOfLE _).op).hom a
      rw [Category.assoc, ← Functor.map_comp]
      rfl
    · change (((pullback.snd πX πY).app (𝔙.inter t) ≫ (pullback πX πY).presheaf.map (homOfLE _).op) ≫ (pullback πX πY).presheaf.map (homOfLE _).op).hom b =
        ((pullback.snd πX πY).app (𝔙.inter t) ≫ (pullback πX πY).presheaf.map (homOfLE _).op).hom b
      rw [Category.assoc, ← Functor.map_comp]
      rfl
  choose Ebox hEbox using box

  let Etot : ∀ p q : ℕ, ((OModulePresheaf.unit πX).cochain 𝔘 p ⊗[k] (OModulePresheaf.unit πY).cochain 𝔙 q) ≃ₗ[k]
      OModulePresheaf.BiCech.C (OModulePresheaf.unit (pullback.fst πX πY ≫ πX))
        (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY)) p q := fun p q =>
    ((TensorProduct.piLeft k ((OModulePresheaf.unit πY).cochain 𝔙 q) (fun s : 𝔘.Idx p => (OModulePresheaf.unit πX).obj (𝔘.inter s))).trans
      ((LinearEquiv.piCongrRight fun s : 𝔘.Idx p =>
          TensorProduct.piRight k k ((OModulePresheaf.unit πX).obj (𝔘.inter s)) (fun t : 𝔙.Idx q => (OModulePresheaf.unit πY).obj (𝔙.inter t))).trans
        (piUncurry k (fun (s : 𝔘.Idx p) (t : 𝔙.Idx q) => (OModulePresheaf.unit πX).obj (𝔘.inter s) ⊗[k] (OModulePresheaf.unit πY).obj (𝔙.inter t))))).trans
      (LinearEquiv.piCongrRight fun st : 𝔘.Idx p × 𝔙.Idx q => Ebox p q st.1 st.2)
  have hEtot : ∀ (p q : ℕ) (α : (OModulePresheaf.unit πX).cochain 𝔘 p) (β : (OModulePresheaf.unit πY).cochain 𝔙 q)
      (st : 𝔘.Idx p × 𝔙.Idx q), Etot p q (α ⊗ₜ[k] β) st = Ebox p q st.1 st.2 (α st.1 ⊗ₜ[k] β st.2) := by
    intro p q α β st
    change Ebox p q st.1 st.2 ((TensorProduct.piRight k k ((OModulePresheaf.unit πX).obj (𝔘.inter st.1))
      (fun t : 𝔙.Idx q => (OModulePresheaf.unit πY).obj (𝔙.inter t)))
      ((TensorProduct.piLeft k ((OModulePresheaf.unit πY).cochain 𝔙 q) (fun s : 𝔘.Idx p => (OModulePresheaf.unit πX).obj (𝔘.inter s))
        (α ⊗ₜ[k] β)) st.1) st.2) = _
    congr 1
  refine ⟨fun p q => (Etot p q).symm, ?_, ?_, ?_⟩
  · intro p q c
    obtain ⟨x, rfl⟩ : ∃ x, c = Etot p q x := ⟨(Etot p q).symm c, by simp⟩
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_eq]
    suffices H : (OModulePresheaf.BiCech.dH (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)) (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY)) p q) ∘ₗ (Etot p q).toLinearMap =
        (Etot (p + 1) q).toLinearMap ∘ₗ ((OModulePresheaf.unit πX).d 𝔘 p).rTensor _ from LinearMap.congr_fun H x
    apply TensorProduct.ext'
    intro α β
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul]
    funext st
    obtain ⟨s', t⟩ := st
    rw [OModulePresheaf.BiCech.dH_apply, hEtot, OModulePresheaf.d_apply, TensorProduct.sum_tmul, map_sum]
    simp only [← Int.cast_smul_eq_zsmul k, ← TensorProduct.smul_tmul', map_smul, hEtot, hEbox]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    change ((pullback πX πY).presheaf.map (homOfLE _).op).hom (_ * _) = _
    rw [map_mul]
    congr 1
    · change ((pullback.fst πX πY).app _ ≫ (pullback πX πY).presheaf.map (homOfLE _).op ≫ (pullback πX πY).presheaf.map (homOfLE _).op).hom _ =
        ((X.presheaf.map (homOfLE _).op ≫ (pullback.fst πX πY).app _) ≫ (pullback πX πY).presheaf.map (homOfLE _).op).hom _
      rw [Scheme.Hom.naturality, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
      rfl
    · change ((pullback.snd πX πY).app _ ≫ (pullback πX πY).presheaf.map (homOfLE _).op ≫ (pullback πX πY).presheaf.map (homOfLE _).op).hom _ =
        ((pullback.snd πX πY).app _ ≫ (pullback πX πY).presheaf.map (homOfLE _).op).hom _
      rw [← Functor.map_comp]
      rfl
  · intro p q c
    obtain ⟨x, rfl⟩ : ∃ x, c = Etot p q x := ⟨(Etot p q).symm c, by simp⟩
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_eq]
    suffices H : (OModulePresheaf.BiCech.dV (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)) (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY)) p q) ∘ₗ (Etot p q).toLinearMap =
        (Etot p (q + 1)).toLinearMap ∘ₗ ((OModulePresheaf.unit πY).d 𝔙 q).lTensor _ from LinearMap.congr_fun H x
    apply TensorProduct.ext'
    intro α β
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.lTensor_tmul]
    funext st
    obtain ⟨s', t⟩ := st
    rw [OModulePresheaf.BiCech.dV_apply, hEtot, OModulePresheaf.d_apply, TensorProduct.tmul_sum, map_sum]
    simp only [← Int.cast_smul_eq_zsmul k, TensorProduct.tmul_smul, map_smul, hEtot, hEbox]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    change ((pullback πX πY).presheaf.map (homOfLE _).op).hom (_ * _) = _
    rw [map_mul]
    congr 1
    · change ((pullback.fst πX πY).app _ ≫ (pullback πX πY).presheaf.map (homOfLE _).op ≫ (pullback πX πY).presheaf.map (homOfLE _).op).hom _ =
        ((pullback.fst πX πY).app _ ≫ (pullback πX πY).presheaf.map (homOfLE _).op).hom _
      rw [← Functor.map_comp]
      rfl
    · change ((pullback.snd πX πY).app _ ≫ (pullback πX πY).presheaf.map (homOfLE _).op ≫ (pullback πX πY).presheaf.map (homOfLE _).op).hom _ =
        ((Y.presheaf.map (homOfLE _).op ≫ (pullback.snd πX πY).app _) ≫ (pullback πX πY).presheaf.map (homOfLE _).op).hom _
      rw [Scheme.Hom.naturality, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
      rfl
  · intro p q α β s t
    rw [LinearEquiv.symm_symm, hEtot, hEbox]

end S_AlgebraicGeometry_OModulePresheaf_exists_biCech_preimageFamily_equiv_tensor_cochain_pinned
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_biCech_preimageFamily_equiv_tensor_cochain_pinned (solution)
