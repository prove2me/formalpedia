-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.mem_chart_of_isUnit_ratio
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:01:46.241204+00:00
-- url     : https://prove2.me/submissions/76f56aab-63ab-4bda-9177-3a262b0d6a9d

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation

/-- An invertible coordinate ratio forces the target coordinate chart. -/
theorem _root_.solution
    {K : Type} [Field K] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {M : X.Modules} {N : ℕ} (P : M.ProjPresentation f N)
    {i j : Fin (N+1)} {O : X.Opens}
    (hO : O ≤ P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i))
    {x : X} (hx : x ∈ O)
    (hu : IsUnit (X.presheaf.map (homOfLE hO).op
      (P.toProj.app (Proj.basicOpen _ (MvPolynomial.X i))
        (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio K N i j))))) :
    x ∈ P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j) := by
  let r := P.toProj.app (Proj.basicOpen _ (MvPolynomial.X i))
    (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio K N i j))
  have h1 : X.basicOpen (X.presheaf.map (homOfLE hO).op r) = O := X.basicOpen_of_isUnit hu
  have h2 : X.basicOpen (X.presheaf.map (homOfLE hO).op r) = O ⊓ X.basicOpen r :=
    X.basicOpen_res _ _
  have hx' : x ∈ X.basicOpen r := by
    have : x ∈ O ⊓ X.basicOpen r := by rw [← h2,h1]; exact hx
    exact this.2
  dsimp only [r] at hx'
  rw [← Scheme.preimage_basicOpen] at hx'
  obtain ⟨hp,hunit⟩ := (Scheme.mem_basicOpen'' _ _ _).mp hx'
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (N+1)) K
  let p := P.toProj.base x
  haveI : p.asHomogeneousIdeal.toIdeal.IsPrime := p.isPrime
  have hle : Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin (N+1)) K) ≤
      p.asHomogeneousIdeal.toIdeal.primeCompl := Submonoid.powers_le.mpr hp
  have hgerm := ProjectiveSpectrum.Proj.awayToSection_germ 𝒜 (MvPolynomial.X i) p hp
  have hcomp : (Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 (MvPolynomial.X i)) p hp
      (Proj.awayToSection 𝒜 (MvPolynomial.X i) (ProjSpace.ratio K N i j)) =
      (Proj.stalkIso' 𝒜 p).toCommRingCatIso.inv
        (HomogeneousLocalization.mapId 𝒜 hle (ProjSpace.ratio K N i j)) := by
    have ht := congrArg (fun φ => (φ : _ → _) (ProjSpace.ratio K N i j))
      (congrArg (fun φ => φ.hom) hgerm)
    first | simpa using ht | (simp at ht ⊢; exact ht)
  rw [hcomp] at hunit
  have hu' : IsUnit (HomogeneousLocalization.mapId 𝒜 hle (ProjSpace.ratio K N i j)) :=
    (isUnit_map_iff (Proj.stalkIso' 𝒜 p).symm _).mp hunit
  rw [← HomogeneousLocalization.isUnit_iff_isUnit_val] at hu'
  have hval : (HomogeneousLocalization.mapId 𝒜 hle (ProjSpace.ratio K N i j)).val =
      Localization.mk (MvPolynomial.X j : MvPolynomial (Fin (N+1)) K)
        ⟨MvPolynomial.X i ^ 1, hle ⟨1,rfl⟩⟩ := by
    rw [ProjSpace.ratio, HomogeneousLocalization.Away.mk, HomogeneousLocalization.mapId,
      HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk]
    rfl
  rw [hval,Localization.mk_eq_mk',IsLocalization.AtPrime.isUnit_mk'_iff] at hu'
  change p ∈ Proj.basicOpen 𝒜 (MvPolynomial.X j)
  rw [Proj.mem_basicOpen]
  exact fun hmem => hu' hmem

end AlgebraicGeometry.Scheme.Modules.ProjPresentation
