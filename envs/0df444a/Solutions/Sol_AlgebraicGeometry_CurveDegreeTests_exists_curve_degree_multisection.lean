-- Prove2me | solution 1 for AlgebraicGeometry.CurveDegreeTests.exists_curve_degree_multisection
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-13T16:40:33.942896+00:00
-- url     : https://prove2.me/submissions/e176f6b3-cd28-4048-96b2-6a0f299ac72a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_CurveDegreeTests
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_twoAffineOpenCover_mem_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_finite_multisection_of_proper_surjective
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_positive_euler_degree_multiplier_of_finite_surjective
import Mathlib.AlgebraicGeometry.PullbackCarrier

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

namespace AlgebraicGeometry.CurveDegreeTests.Multisection
open CategoryTheory CategoryTheory.Limits MonoidalCategory
universe u

/-- The Euler characteristic computed by the given affine charts. -/
def euler {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) (𝒰 : C.TwoAffineOpenCover) (N : C.Modules) : ℤ :=
  (Module.finrank K (𝒰.sectionsOf c N).H0 : ℤ) -
    Module.finrank K (𝒰.sectionsOf c N).H1

/-- Compare the actual section modules on the same cover. -/
theorem euler_iso {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) (𝒰 : C.TwoAffineOpenCover)
    {M N : C.Modules} (e : M ≅ N) : euler c 𝒰 M = euler c 𝒰 N := by
  obtain ⟨𝒲, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso c c
      (Iso.refl C) (by simp) 𝒰 N M
      (e ≪≫ ((Scheme.Modules.pullbackId C).app N).symm)
  have h0' : 𝒲.U0 = 𝒰.U0 := by simpa using h0
  have h1' : 𝒲.U1 = 𝒰.U1 := by simpa using h1
  have hW : 𝒲 = 𝒰 := by
    cases 𝒲
    cases 𝒰
    simp_all
  subst 𝒲
  unfold euler
  rw [e0.finrank_eq, e1.finrank_eq]

/-- The sheaf comparison associated to a commutative square of schemes. -/
def squarePullbackIso {X Y C D : Scheme.{u}}
    (f : Y ⟶ X) (a : C ⟶ X) (b : D ⟶ Y) (g : D ⟶ C)
    (h : b ≫ f = g ≫ a) (M : X.Modules) :
    (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback f).obj M) ≅
      (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback a).obj M) :=
  (Scheme.Modules.pullbackComp b f).app M ≪≫
    (Scheme.Modules.pullbackCongr h).app M ≪≫
      ((Scheme.Modules.pullbackComp g a).app M).symm

/-- A smooth proper integral curve has the required computational charts,
using two independently proved public geometric results. -/
theorem exists_cover {K : Type u} [Field K] [IsAlgClosed K] {D : Scheme.{u}}
    (δ : D ⟶ Spec (.of K)) [IsIntegral D] [IsProper δ]
    [SmoothOfRelativeDimension 1 δ] : Nonempty D.TwoAffineOpenCover := by
  letI : GeometricallyIntegral δ := geometricallyIntegral_of_isAlgClosed δ
  obtain ⟨𝒱, _⟩ := SmoothProperCurve.exists_twoAffineOpenCover_mem_of_isAlgClosed K δ
    (Classical.choice (inferInstance : Nonempty D))
  exact ⟨𝒱⟩

/-- A curve in the fibre product determines a test on Y whose map to X
agrees with the original test after the finite curve cover. -/
def liftedProbe {K : Type u} [Field K] {X Y D : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) (f : Y ⟶ X) (t : Probe π)
    (b : D ⟶ Limits.pullback t.toScheme f)
    [IsIntegral D]
    [IsProper ((b ≫ pullback.fst t.toScheme f) ≫ t.toBase)]
    [SmoothOfRelativeDimension 1 ((b ≫ pullback.fst t.toScheme f) ≫ t.toBase)]
    (𝒱 : D.TwoAffineOpenCover) : Probe (f ≫ π) where
  curve := D
  toBase := (b ≫ pullback.fst t.toScheme f) ≫ t.toBase
  integral := inferInstance
  proper := inferInstance
  smooth := inferInstance
  toScheme := b ≫ pullback.snd t.toScheme f
  over_base := by
    simp only [Category.assoc]
    rw [← pullback.condition_assoc, t.over_base]
  cover := 𝒱

theorem liftedProbe_square {K : Type u} [Field K] {X Y D : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) (f : Y ⟶ X) (t : Probe π)
    (b : D ⟶ Limits.pullback t.toScheme f)
    [IsIntegral D]
    [IsProper ((b ≫ pullback.fst t.toScheme f) ≫ t.toBase)]
    [SmoothOfRelativeDimension 1 ((b ≫ pullback.fst t.toScheme f) ≫ t.toBase)]
    (𝒱 : D.TwoAffineOpenCover) :
    (liftedProbe π f t b 𝒱).toScheme ≫ f =
      (b ≫ pullback.fst t.toScheme f) ≫ t.toScheme := by
  change (b ≫ pullback.snd t.toScheme f) ≫ f = _
  simp only [Category.assoc]
  rw [pullback.condition]

end AlgebraicGeometry.CurveDegreeTests.Multisection

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.CurveDegreeTests.Multisection
universe u

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π]
    (f : Y ⟶ X) [IsProper f] [Surjective f] (t : CurveDegreeTests.Probe π) :
    ∃ (s : CurveDegreeTests.Probe (f ≫ π)) (g : s.curve ⟶ t.curve),
      IsFinite g ∧ Surjective g ∧ s.toScheme ≫ f = g ≫ t.toScheme ∧
        ∃ d : ℕ, 0 < d ∧ ∀ M : X.Modules, Scheme.Modules.IsInvertible M →
          s.degree ((Scheme.Modules.pullback f).obj M) = (d : ℤ) * t.degree M := by
  obtain ⟨D, b, hD, hproper, hsmooth, hfinite, hsurj⟩ :=
    SmoothProperCurve.exists_finite_multisection_of_proper_surjective K t.toBase
      (pullback.fst t.toScheme f)
  letI := hD
  letI := hproper
  letI := hsmooth
  letI := hfinite
  letI := hsurj
  let g := b ≫ pullback.fst t.toScheme f
  let δ := g ≫ t.toBase
  obtain ⟨𝒱⟩ := exists_cover δ
  let s := liftedProbe π f t b 𝒱
  have hcomm : s.toScheme ≫ f = g ≫ t.toScheme := liftedProbe_square π f t b 𝒱
  obtain ⟨d, hd, hdegree⟩ :=
    SmoothProperCurve.exists_positive_euler_degree_multiplier_of_finite_surjective
      K t.toBase δ g rfl t.cover 𝒱
  refine ⟨s, g, hfinite, hsurj, hcomm, d, hd, ?_⟩
  intro M hM
  have he := euler_iso δ 𝒱 (squarePullbackIso f t.toScheme s.toScheme g hcomm M)
  have hm := hdegree ((Scheme.Modules.pullback t.toScheme).obj M) (hM.pullback t.toScheme)
  change euler δ 𝒱 ((Scheme.Modules.pullback s.toScheme).obj
      ((Scheme.Modules.pullback f).obj M)) - euler δ 𝒱 (𝟙_ D.Modules) =
    (d : ℤ) * (euler t.toBase t.cover ((Scheme.Modules.pullback t.toScheme).obj M) -
      euler t.toBase t.cover (𝟙_ t.curve.Modules))
  rw [he]
  exact hm
