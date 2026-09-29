-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_iff_isLocalizedModule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/bdd0a80b-ca62-5fdd-b236-4cdb676705e6

import Mathlib
import Theorems.Thm_TopCat_Sheaf_isIso_of_isIso_app_of_isBasis
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_iff_isLocalizedModule

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
theorem solution {R : CommRingCat.{u}}
    (M : (Spec (.of R)).Modules) :
    IsIso M.fromTildeΓ ↔ ∀ f : R, IsLocalizedModule (Submonoid.powers (M := R) f)
      ((modulesSpecToSheaf.obj M).1.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom := by
  constructor
  · intro hiso f
    generalize hr : (modulesSpecToSheaf.obj M).1.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op = r
    have happ := (Scheme.Modules.toOpen_fromTildeΓ_app M (PrimeSpectrum.basicOpen f)).trans hr
    haveI : IsIso (modulesSpecToSheaf.map M.fromTildeΓ).1 := by
      haveI : IsIso (modulesSpecToSheaf.map M.fromTildeΓ) := inferInstance
      infer_instance
    let e := (asIso ((modulesSpecToSheaf.map M.fromTildeΓ).1.app (op (PrimeSpectrum.basicOpen f)))).toLinearEquiv
    have hre : r.hom = e.toLinearMap ∘ₗ
        (tilde.toOpen ((modulesSpecToSheaf.obj M).presheaf.obj (op ⊤)) (PrimeSpectrum.basicOpen f)).hom := by
      rw [← happ]; rfl
    rw [hre]
    exact IsLocalizedModule.of_linearEquiv (Submonoid.powers (M := R) f) _ e
  · intro hloc

    suffices IsIso (modulesSpecToSheaf.map M.fromTildeΓ) from
      (SpecModulesToSheafFullyFaithful (R := R)).isIso_of_isIso_map _
    apply TopCat.Sheaf.isIso_of_isIso_app_of_isBasis (B := fun f : R => PrimeSpectrum.basicOpen f)
      PrimeSpectrum.isBasis_basic_opens
    intro f
    specialize hloc f
    revert hloc
    generalize hr : (modulesSpecToSheaf.obj M).1.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op = r
    intro hloc
    have happ := (Scheme.Modules.toOpen_fromTildeΓ_app M (PrimeSpectrum.basicOpen f)).trans hr

    set l₁ := (tilde.toOpen ((modulesSpecToSheaf.obj M).presheaf.obj (op ⊤)) (PrimeSpectrum.basicOpen f)).hom
      with hl₁
    set g := ((modulesSpecToSheaf.map M.fromTildeΓ).1.app (op (PrimeSpectrum.basicOpen f))).hom with hgdef
    have hg : g ∘ₗ l₁ = r.hom := by rw [← happ]; rfl
    haveI : IsLocalizedModule (Submonoid.powers (M := R) f) l₁ := by rw [hl₁]; infer_instance
    let e := IsLocalizedModule.linearEquiv (Submonoid.powers (M := R) f) l₁ r.hom
    have he' : e.toLinearMap ∘ₗ l₁ = r.hom := by
      ext x; simp [e]
    have he : g = e.toLinearMap :=
      IsLocalizedModule.linearMap_ext (S := Submonoid.powers (M := R) f) (f := l₁) (f' := r.hom) (hg.trans he'.symm)
    have hb : Function.Bijective ((modulesSpecToSheaf.map M.fromTildeΓ).1.app (op (PrimeSpectrum.basicOpen f))) := by
      change Function.Bijective g
      rw [he]; exact e.bijective
    exact (ConcreteCategory.isIso_iff_bijective _).mpr hb

end S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_iff_isLocalizedModule
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_iff_isLocalizedModule (solution)
