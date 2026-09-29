-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_finiteBySections_pullback_of_quasiFiniteAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/af101091-d0e5-5558-9484-85e61dd40b58

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_iso
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_finiteBySections_pullback_of_quasiFiniteAt

universe u

set_option autoImplicit false
section gamma_solution
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} [IsProper f] {M : X.Modules} {N : ℕ}
    (𝔔 : M.ProjPresentation f N) (𝔭 : PrimeSpectrum R)
    (hqf : ∀ x : X, f x = 𝔭 → 𝔔.toProj.QuasiFiniteAt x) :
    ∃ g : R, g ∉ 𝔭.asIdeal ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A], IsUnit (algebraMap R A g) →
        ∀ {X' : Scheme.{u}} (p : X' ⟶ X) (f' : X' ⟶ Spec (.of A)),
          IsPullback p f' f (Spec.map (CommRingCat.ofHom (algebraMap R A))) →
          Scheme.Modules.FiniteBySections ((Scheme.Modules.pullback p).obj M) f' := by
  classical
  haveI : LocallyOfFiniteType 𝔔.toProj := by
    have : LocallyOfFiniteType (𝔔.toProj ≫ ProjSpace.π R N) := by rw [𝔔.toProj_π]; infer_instance
    exact locallyOfFiniteType_of_comp _ (ProjSpace.π R N)

  let W : X.Opens := 𝔔.toProj.quasiFiniteLocus
  let Z : Set (PrimeSpectrum R) := f.base '' ((W : Set X)ᶜ)
  have hZ : IsClosed Z := f.isClosedMap _ W.isOpen.isClosed_compl
  have h𝔭Z : 𝔭 ∈ Zᶜ := by
    rintro ⟨x, hx, hfx⟩
    exact hx (Scheme.Hom.mem_quasiFiniteLocus.2 (hqf x hfx))
  obtain ⟨_, ⟨g, rfl⟩, hg𝔭, hgZ⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open h𝔭Z hZ.isOpen_compl
  refine ⟨g, hg𝔭, ?_⟩
  have hW : ∀ x : X, f x ∈ PrimeSpectrum.basicOpen g → 𝔔.toProj.QuasiFiniteAt x := by
    intro x hx
    by_contra hx'
    exact hgZ hx ⟨x, fun h => hx' (Scheme.Hom.mem_quasiFiniteLocus.1 h), rfl⟩
  intro A _ _ hgA X' p f' sq

  let Rg : Type u := Localization.Away g
  let ιg : Spec (.of Rg) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R Rg))
  let pg := pullback.fst f ιg
  let fg := pullback.snd f ιg
  obtain ⟨𝔔g, -, hcompg, -⟩ :=
    Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback (IsPullback.of_hasPullback f ιg) 𝔔
  haveI : LocallyOfFiniteType 𝔔g.toProj := by
    have : LocallyOfFiniteType (𝔔g.toProj ≫ ProjSpace.π Rg N) := by rw [𝔔g.toProj_π]; infer_instance
    exact locallyOfFiniteType_of_comp _ (ProjSpace.π Rg N)
  haveI : LocallyQuasiFinite (ProjSpace.map R Rg N) :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) (ProjSpace.isPullback_map R Rg N).flip inferInstance
  haveI : LocallyQuasiFinite 𝔔g.toProj := by
    rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff, eq_top_iff]
    rintro x -
    rw [Scheme.Hom.mem_quasiFiniteLocus, ← Scheme.Hom.quasiFiniteAt_comp_iff (g := ProjSpace.map R Rg N), hcompg,
      Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion]
    apply hW
    have h1 : f (pg x) = ιg (fg x) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    have h2 : ιg (fg x) ∈ Set.range (PrimeSpectrum.comap (algebraMap R Rg)) :=
      ⟨fg x, (Spec.map_apply (CommRingCat.ofHom (algebraMap R Rg)) (fg x)).symm⟩
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g] at h2
    rw [h1]
    exact h2
  haveI : IsProper 𝔔g.toProj := by
    have : IsProper (𝔔g.toProj ≫ ProjSpace.π Rg N) := by rw [𝔔g.toProj_π]; infer_instance
    exact IsProper.of_comp _ (ProjSpace.π Rg N)
  haveI : IsFinite 𝔔g.toProj := IsFinite.of_isProper_of_locallyQuasiFinite _

  letI : Algebra Rg A := (IsLocalization.Away.lift g hgA).toAlgebra
  haveI : IsScalarTower R Rg A :=
    IsScalarTower.of_algebraMap_eq fun r => (IsLocalization.Away.lift_eq g hgA r).symm
  have hι : Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap Rg A)) ≫ ιg := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  let p' : X' ⟶ pullback f ιg :=
    pullback.lift p (f' ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg A)))
      (by rw [Category.assoc, ← hι]; exact sq.w)
  have hp' : p' ≫ pg = p := pullback.lift_fst _ _ _
  have sq' : IsPullback p' f' fg (Spec.map (CommRingCat.ofHom (algebraMap Rg A))) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f ιg)
    rw [hp', ← hι]; exact sq
  obtain ⟨𝔔A, -, -, hsqA⟩ := Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback sq' 𝔔g
  haveI : IsFinite 𝔔A.toProj := MorphismProperty.of_isPullback (P := @IsFinite) hsqA inferInstance
  have hF : Scheme.Modules.FiniteBySections
      ((Scheme.Modules.pullback p').obj ((Scheme.Modules.pullback pg).obj M)) f' := ⟨N, 𝔔A, inferInstance⟩
  exact Scheme.Modules.FiniteBySections.of_iso
    (((Scheme.Modules.pullbackComp p' pg).app M) ≪≫ (Scheme.Modules.pullbackCongr hp').app M) hF

end gamma_solution

end S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_finiteBySections_pullback_of_quasiFiniteAt
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_finiteBySections_pullback_of_quasiFiniteAt (solution)
