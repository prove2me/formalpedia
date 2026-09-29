-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.comap_of_isOpenImmersion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/43cf3048-61f8-5cb4-a3e1-3bc3273d0873

import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_comap_of_isOpenImmersion

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {X Y : Scheme.{u}} {I : X.IdealSheafData} (hI : I.IsInvertible) (j : Y ⟶ X) [IsOpenImmersion j] :
    (I.comap j).IsInvertible := by
  intro y
  obtain ⟨U, f, hxf, g, hg, hIg⟩ := hI (j y)

  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hyV₀, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  let V₀' : Y.affineOpens := ⟨V₀, hV₀⟩
  let W₀ : X.affineOpens := ⟨j ''ᵁ V₀, hV₀.image_of_isOpenImmersion j⟩
  have hxW₀ : j y ∈ (W₀ : X.Opens) := ⟨y, hyV₀, rfl⟩

  obtain ⟨h, h', hhh', hxh⟩ :=
    exists_basicOpen_le_affine_inter (X.affineBasicOpen f).2 W₀.2 (j y) ⟨hxf, hxW₀⟩
  have hW : (X.affineBasicOpen h : X.Opens) ≤ X.affineBasicOpen f := X.basicOpen_le h

  let gh : Γ(X, X.affineBasicOpen h) := (X.presheaf.map (homOfLE hW).op).hom g
  have hgh : gh ∈ nonZeroDivisors Γ(X, X.affineBasicOpen h) := by
    letI := (X.affineBasicOpen f).2.isLocalization_basicOpen h
    exact IsLocalization.nonZeroDivisors_le_comap (M := .powers h) (S := Γ(X, X.basicOpen h)) hg
  have hIh : I.ideal (X.affineBasicOpen h) = Ideal.span {gh} := by
    rw [← I.map_ideal (U := X.affineBasicOpen h) (V := X.affineBasicOpen f) hW, hIg, Ideal.map_span,
      Set.image_singleton]
    rfl

  let f' : Γ(Y, V₀) := (j.appIso V₀).hom h'
  have hf' : (j.appIso V₀).inv f' = h' := by
    change ((j.appIso V₀).hom ≫ (j.appIso V₀).inv) h' = h'
    rw [Iso.hom_inv_id]; rfl
  have himg : j ''ᵁ Y.basicOpen f' = X.basicOpen h := by
    rw [Scheme.image_basicOpen, hf', ← hhh']
  have hyf' : y ∈ Y.basicOpen f' := by
    have : j y ∈ j ''ᵁ Y.basicOpen f' := by rw [himg]; exact hxh
    obtain ⟨y', hy', hyy'⟩ := this
    rwa [← j.isOpenEmbedding.injective hyy']

  have heqA : (⟨j ''ᵁ (Y.affineBasicOpen (U := V₀') f' : Y.Opens),
      (Y.affineBasicOpen (U := V₀') f').2.image_of_isOpenImmersion j⟩ : X.affineOpens) = X.affineBasicOpen h :=
    Subtype.ext himg
  refine ⟨V₀', f', hyf', ?_⟩

  let e₁ : Γ(X, X.affineBasicOpen h) ⟶ Γ(X, j ''ᵁ (Y.affineBasicOpen (U := V₀') f' : Y.Opens)) :=
    X.presheaf.map (eqToHom (congrArg Subtype.val heqA)).op
  haveI : IsIso e₁ := by dsimp only [e₁]; infer_instance
  let e₂ := j.appIso (Y.affineBasicOpen (U := V₀') f' : Y.Opens)
  let g' : Γ(Y, Y.affineBasicOpen (U := V₀') f') := e₂.hom (e₁.hom gh)
  refine ⟨g', ?_, ?_⟩
  ·
    have hinj₁ : Function.Injective (e₂.inv.hom) := (ConcreteCategory.bijective_of_isIso e₂.inv).1
    have hinj₂ : Function.Injective ((inv e₁).hom) := (ConcreteCategory.bijective_of_isIso (inv e₁)).1
    refine mem_nonZeroDivisors_of_injective hinj₁ ?_
    refine mem_nonZeroDivisors_of_injective hinj₂ ?_
    have h1 : e₂.inv.hom g' = e₁.hom gh := by
      change (e₂.hom ≫ e₂.inv) (e₁.hom gh) = e₁.hom gh
      rw [Iso.hom_inv_id]; rfl
    have h2 : (inv e₁).hom (e₁.hom gh) = gh := by
      change (e₁ ≫ inv e₁) gh = gh
      rw [IsIso.hom_inv_id]; rfl
    rw [h1, h2]
    exact hgh
  ·
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]

    have hle : (⟨j ''ᵁ (Y.affineBasicOpen (U := V₀') f' : Y.Opens),
        (Y.affineBasicOpen (U := V₀') f').2.image_of_isOpenImmersion j⟩ : X.affineOpens) ≤ X.affineBasicOpen h :=
      le_of_eq heqA
    have hIj : I.ideal ⟨j ''ᵁ (Y.affineBasicOpen (U := V₀') f' : Y.Opens),
        (Y.affineBasicOpen (U := V₀') f').2.image_of_isOpenImmersion j⟩ = Ideal.span {e₁.hom gh} := by
      rw [← I.map_ideal' (U := ⟨j ''ᵁ (Y.affineBasicOpen (U := V₀') f' : Y.Opens), _⟩)
        (V := X.affineBasicOpen h) (eqToHom (congrArg Subtype.val heqA)).op, hIh, Ideal.map_span, Set.image_singleton]
    rw [hIj]

    have h1 : e₂.inv.hom g' = e₁.hom gh := by
      change (e₂.hom ≫ e₂.inv) (e₁.hom gh) = e₁.hom gh
      rw [Iso.hom_inv_id]; rfl
    apply le_antisymm
    · intro x hx
      rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hx
      obtain ⟨a, ha⟩ := hx
      rw [Ideal.mem_span_singleton']
      refine ⟨e₂.hom.hom a, ?_⟩
      have hx' : x = e₂.hom.hom (e₂.inv.hom x) := by
        change x = (e₂.inv ≫ e₂.hom) x
        rw [Iso.inv_hom_id]; rfl
      rw [hx', ← ha, map_mul]
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, h1]
      exact Ideal.subset_span rfl

end S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_comap_of_isOpenImmersion
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_comap_of_isOpenImmersion (solution)
