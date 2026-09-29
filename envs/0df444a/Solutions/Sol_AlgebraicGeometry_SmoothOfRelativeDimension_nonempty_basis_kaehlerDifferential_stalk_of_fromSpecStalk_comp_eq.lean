-- Prove2me | solution 1 for AlgebraicGeometry.SmoothOfRelativeDimension.nonempty_basis_kaehlerDifferential_stalk_of_fromSpecStalk_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/d24a88cb-a1b8-5323-b04b-55ea5f2a3425

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_nonempty_basis_kaehlerDifferential_stalk_of_fromSpecStalk_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))
    (n : ℕ) [SmoothOfRelativeDimension n f] (y : Y)
    [Algebra R (Y.presheaf.stalk y)]
    (halg : Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))) :
    Nonempty (Module.Basis (Fin n) (Y.presheaf.stalk y) (Ω[Y.presheaf.stalk y⁄R])) := by
  classical

  obtain ⟨U, hU, V, hV, hyV, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) y

  obtain ⟨r, s, hys, e₁, hf₁⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine
    (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).right
    (RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves n).away
    y ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ ⟨V, hV⟩ ⟨V, hV⟩ hyV hyV e hf (by trivial)
  set W : Y.Opens := Y.basicOpen s with hW
  have hWaff : IsAffineOpen W := hV.basicOpen s
  have hyW : y ∈ W := hys
  have eW : W ≤ f ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens) := fun x _ => by simp

  letI algA : Algebra R Γ(Y, W) := ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ W eW).hom.toAlgebra

  letI algAs : Algebra Γ(Y, W) (Y.presheaf.stalk y) := Y.presheaf.algebra_section_stalk ⟨y, hyW⟩
  have hpin : CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)) =
      (Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop ≫ Y.presheaf.germ ⊤ y trivial := by
    have h := congrArg Scheme.Hom.appTop halg
    rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop] at h

    have h' := congrArg (fun k => (Scheme.ΓSpecIso (.of R)).inv ≫ k ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk y)).hom) h
    simp only [Category.assoc] at h'
    rw [← Scheme.ΓSpecIso_inv_naturality_assoc] at h'
    simpa using h'.symm
  haveI : IsScalarTower R Γ(Y, W) (Y.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq fun a => by
    show (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y))).hom a =
      (Y.presheaf.germ W y hyW).hom (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ W eW).hom a)
    rw [hpin, ← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE, Category.assoc,
      TopCat.Presheaf.germ_res]
    rfl

  have hstd : Algebra.IsStandardSmoothOfRelativeDimension n R Γ(Y, W) := by
    have h₁ := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).left
      _ r _ hf₁
    rw [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE] at h₁
    have h₂ : (f.appLE ⊤ W eW).hom.IsStandardSmoothOfRelativeDimension n := h₁
    have h₃ := ((RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)).cancel_left_isIso
      (Scheme.ΓSpecIso (.of R)).inv (f.appLE ⊤ W eW)).mpr h₂
    rw [← CommRingCat.hom_comp] at h₃
    exact h₃
  haveI := hstd
  haveI : Algebra.IsStandardSmooth R Γ(Y, W) := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  haveI : Nontrivial Γ(Y, W) := (algebraMap Γ(Y, W) (Y.presheaf.stalk y)).domain_nontrivial
  have hrank : Module.rank Γ(Y, W) Ω[Γ(Y, W)⁄R] = n :=
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
  haveI : Module.Finite Γ(Y, W) Ω[Γ(Y, W)⁄R] := Module.finite_of_rank_eq_nat hrank
  let bA : Module.Basis (Fin n) Γ(Y, W) Ω[Γ(Y, W)⁄R] :=
    Module.finBasisOfFinrankEq _ _ (Module.finrank_eq_of_rank_eq hrank)

  haveI := hWaff.isLocalization_stalk ⟨y, hyW⟩
  exact ⟨bA.ofIsLocalizedModule (Y.presheaf.stalk y) (hWaff.primeIdealOf ⟨y, hyW⟩).asIdeal.primeCompl
    (KaehlerDifferential.map R R Γ(Y, W) (Y.presheaf.stalk y))⟩

end S_AlgebraicGeometry_SmoothOfRelativeDimension_nonempty_basis_kaehlerDifferential_stalk_of_fromSpecStalk_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_nonempty_basis_kaehlerDifferential_stalk_of_fromSpecStalk_comp_eq (solution)
