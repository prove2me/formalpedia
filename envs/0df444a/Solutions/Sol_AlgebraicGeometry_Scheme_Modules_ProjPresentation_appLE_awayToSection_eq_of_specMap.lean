-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.appLE_awayToSection_eq_of_specMap
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:07.110567+00:00
-- url     : https://prove2.me/submissions/8cd8460e-00f6-4aad-a258-a695fd1ee175

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints
import Definitions.Def_AlgebraicGeometry_ProjSpaceEquivalence

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation

private theorem appLE_awayToSection_of_fac
    {A τ : Type} [CommRing A] [SetLike τ A] [AddSubgroupClass τ A]
    (𝒜 : ℕ → τ) [GradedRing 𝒜]
    {g : A} {m : ℕ} (hg : g ∈ 𝒜 m) (hm : 0 < m)
    {Y : Scheme.{0}} (φ : Y ⟶ Proj 𝒜) {V : Y.Opens} (hV : IsAffineOpen V)
    (ψ : CommRingCat.of (HomogeneousLocalization.Away 𝒜 g) ⟶ Γ(Y, V))
    (hfac : V.ι ≫ φ = V.toSpecΓ ≫ Spec.map ψ ≫ Proj.awayι 𝒜 g hg hm)
    (hle : V ≤ φ ⁻¹ᵁ Proj.basicOpen 𝒜 g) (z : HomogeneousLocalization.Away 𝒜 g) :
    φ.appLE (Proj.basicOpen 𝒜 g) V hle (Proj.awayToSection 𝒜 g z) = ψ z := by
  have h₁ : φ.resLE _ V hle =
      V.toSpecΓ ≫ Spec.map ψ ≫ (Proj.basicOpenIsoSpec 𝒜 g hg hm).inv := by
    rw [← cancel_mono (Proj.basicOpen 𝒜 g).ι, Scheme.Hom.resLE_comp_ι, hfac]
    simp only [Category.assoc, Proj.basicOpenIsoSpec_inv_ι]
  have h₂ := Scheme.Opens.toSpecΓ_SpecMap_appLE φ (Proj.basicOpen 𝒜 g) V hle
  rw [h₁] at h₂
  have h₃ : V.toSpecΓ ≫ Spec.map (Proj.awayToSection 𝒜 g ≫ φ.appLE (Proj.basicOpen 𝒜 g) V hle) =
      V.toSpecΓ ≫ Spec.map ψ := by
    have he : (Proj.basicOpen 𝒜 g).toSpecΓ ≫ Spec.map (Proj.awayToSection 𝒜 g) =
        (Proj.basicOpenIsoSpec 𝒜 g hg hm).hom := by rw [Proj.basicOpenIsoSpec_hom]; rfl
    rw [Spec.map_comp, reassoc_of% h₂]
    rw [he, Iso.inv_hom_id, Category.comp_id]
  haveI : IsIso V.toSpecΓ := by rw [← hV.isoSpec_hom]; infer_instance
  rw [cancel_epi] at h₃
  have h₄ := Spec.map_inj.mp h₃
  simpa using congrArg (fun t => t.hom z) h₄

/-- Pulling a chart section back along a field-valued point evaluates it by its chart homomorphism. -/
theorem _root_.solution
    {K : Type} [Field K] {N : ℕ}
    (y : Spec (CommRingCat.of K) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K))
    (i : Fin (N + 1))
    (φ : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
      (MvPolynomial.X i) →+* K)
    (hy : y = Spec.map (CommRingCat.ofHom φ) ≫ Proj.awayι
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (MvPolynomial.X i)
      (ProjSpace.X_mem_one K N i) one_pos)
    (hle : (⊤ : (Spec (CommRingCat.of K)).Opens) ≤
      y ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i))
    (z : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
      (MvPolynomial.X i)) :
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom
      (y.appLE (Proj.basicOpen _ (MvPolynomial.X i)) ⊤ hle (Proj.awayToSection _ (MvPolynomial.X i) z)) =
      φ z := by
  let ψ : CommRingCat.of (HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (MvPolynomial.X i)) ⟶
      Γ(Spec (CommRingCat.of K), ⊤) :=
    CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).inv
  have hfac : (⊤ : (Spec (CommRingCat.of K)).Opens).ι ≫ y =
      (⊤ : (Spec (CommRingCat.of K)).Opens).toSpecΓ ≫ Spec.map ψ ≫
        Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (MvPolynomial.X i)
          (ProjSpace.X_mem_one K N i) one_pos := by
    dsimp only [ψ]
    rw [Scheme.Opens.toSpecΓ_top, Spec.map_comp]
    simp only [Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv_assoc, hy]
  rw [appLE_awayToSection_of_fac _ (ProjSpace.X_mem_one K N i) one_pos y
    (isAffineOpen_top _) ψ hfac hle z]
  change (Scheme.ΓSpecIso (CommRingCat.of K)).hom
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv (φ z)) = φ z
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id]
  rfl

end AlgebraicGeometry.Scheme.Modules.ProjPresentation
