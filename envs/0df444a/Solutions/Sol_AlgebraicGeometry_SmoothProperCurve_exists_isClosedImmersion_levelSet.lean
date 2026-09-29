-- Prove2me | solution 1 for AlgebraicGeometry.SmoothProperCurve.exists_isClosedImmersion_levelSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/358fd734-9ae7-578d-b278-6d8cc4cbd939

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_isClosedImmersion_levelSet

set_option autoImplicit false

universe u

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_isClosedImmersion_levelSet.AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_isClosedImmersion_levelSet.AlgebraicGeometry.SmoothProperCurve NeronModelInfra Algebra.TensorProduct"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp pullbackSpecIso_inv_fst' IsProper IsAffineOpen.fromSpec_top IsFinite IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme pullbackSpecIso Scheme.isoSpec_Spec_inv IsClosedImmersion.iff_isProper_and_mono IsClosedImmersion.spec_of_surjective IsClosedImmersion IsSeparated isAffineOpen_top IsProper.of_comp IsFinite.SpecMap_iff IsAffineOpen Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom"
namespace SmoothProperCurve
p2m_export "AlgebraicGeometry.SmoothProperCurve" "specMap baseChange"
namespace LevelSetImpl
p2m_open "AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry"

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (U₀ : C.Opens) (hU₀ : IsAffineOpen U₀)

theorem fromSpec_comp :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
    hU₀.fromSpec ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R Γ(C, U₀))) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
  have h := IsAffineOpen.SpecMap_appLE_fromSpec c (isAffineOpen_top (Spec (CommRingCat.of R))) hU₀
    (le_top : U₀ ≤ c ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  rw [← h]
  rfl

variable (S : Type u) [CommRing S] [Algebra R S]

noncomputable def chartMap :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
    pullback (specMap R S) (specMap R Γ(C, U₀)) ⟶ pullback c (specMap R S) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
  pullback.lift (pullback.snd _ _ ≫ hU₀.fromSpec) (pullback.fst _ _)
    (by rw [Category.assoc, fromSpec_comp c U₀ hU₀, ← pullback.condition])

theorem chartMap_snd :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
    chartMap c U₀ hU₀ S ≫ pullback.snd c (specMap R S) = pullback.fst _ _ :=
  pullback.lift_snd _ _ _

theorem chartMap_fst :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
    chartMap c U₀ hU₀ S ≫ pullback.fst c (specMap R S) = pullback.snd _ _ ≫ hU₀.fromSpec :=
  pullback.lift_fst _ _ _

scoped instance mono_chartMap :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
    Mono (chartMap c U₀ hU₀ S) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
  refine ⟨fun {T} x y h => ?_⟩
  apply pullback.hom_ext
  · have h1 := congrArg (· ≫ pullback.snd c (specMap R S)) h
    simpa only [Category.assoc, chartMap_snd] using h1
  · have h2 := congrArg (· ≫ pullback.fst c (specMap R S)) h
    simp only [Category.assoc, chartMap_fst] at h2
    rw [← Category.assoc, ← Category.assoc] at h2
    exact (cancel_mono hU₀.fromSpec).mp h2

end AlgebraicGeometry.SmoothProperCurve.LevelSetImpl
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_isClosedImmersion_levelSet.AlgebraicGeometry P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_isClosedImmersion_levelSet.AlgebraicGeometry.SmoothProperCurve P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_isClosedImmersion_levelSet.AlgebraicGeometry.SmoothProperCurve.LevelSetImpl"
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_isClosedImmersion_levelSet.AlgebraicGeometry P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_isClosedImmersion_levelSet.AlgebraicGeometry.SmoothProperCurve"
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_isClosedImmersion_levelSet.AlgebraicGeometry"

open AlgebraicGeometry.SmoothProperCurve.LevelSetImpl in
theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U₀ : C.Opens) (hU₀ : IsAffineOpen U₀) (f : Γ(C, U₀))
    (S : Type u) [CommRing S] [Algebra R S] (s : S)
    (hfin : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
      Module.Finite S (S ⊗[R] Γ(C, U₀) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U₀))})) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
    ∃ ι : Spec (CommRingCat.of (S ⊗[R] Γ(C, U₀) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U₀))})) ⟶ pullback c (specMap R S),
      IsClosedImmersion ι ∧ ι ≫ baseChange R c S = specMap S (S ⊗[R] Γ(C, U₀) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U₀))}) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
  set I : Ideal (S ⊗[R] Γ(C, U₀)) := Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U₀))} with hI
  haveI : Module.Finite S (S ⊗[R] Γ(C, U₀) ⧸ I) := hfin

  let q : Spec (CommRingCat.of (S ⊗[R] Γ(C, U₀) ⧸ I)) ⟶ Spec (CommRingCat.of (S ⊗[R] Γ(C, U₀))) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let e := (pullbackSpecIso R S Γ(C, U₀)).inv
  let ι := q ≫ e ≫ chartMap c U₀ hU₀ S
  have hιsnd : ι ≫ baseChange R c S = specMap S (S ⊗[R] Γ(C, U₀) ⧸ I) := by
    show (q ≫ e ≫ chartMap c U₀ hU₀ S) ≫ pullback.snd c (specMap R S) = _
    simp only [Category.assoc, chartMap_snd, q, e]
    rw [pullbackSpecIso_inv_fst', ← Spec.map_comp]
    rfl
  refine ⟨ι, ?_, hιsnd⟩

  haveI : IsClosedImmersion q := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  haveI : Mono ι := by
    show Mono (q ≫ e ≫ chartMap c U₀ hU₀ S)
    infer_instance
  haveI : IsProper (ι ≫ baseChange R c S) := by
    rw [hιsnd]
    haveI : IsFinite (specMap S (S ⊗[R] Γ(C, U₀) ⧸ I)) := by
      rw [IsFinite.SpecMap_iff]
      show (algebraMap S (S ⊗[R] Γ(C, U₀) ⧸ I)).Finite
      exact RingHom.finite_algebraMap.mpr inferInstance
    infer_instance
  haveI : IsProper ι := IsProper.of_comp ι (baseChange R c S)
  exact IsClosedImmersion.iff_isProper_and_mono ι |>.mpr ⟨inferInstance, inferInstance⟩

end S_AlgebraicGeometry_SmoothProperCurve_exists_isClosedImmersion_levelSet
end P2MW
export P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_isClosedImmersion_levelSet (solution)
