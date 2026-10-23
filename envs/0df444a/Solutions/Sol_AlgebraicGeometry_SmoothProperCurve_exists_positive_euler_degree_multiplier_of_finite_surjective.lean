-- Prove2me | solution 1 for AlgebraicGeometry.SmoothProperCurve.exists_positive_euler_degree_multiplier_of_finite_surjective
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-13T17:09:06.254339+00:00
-- url     : https://prove2.me/submissions/3179dae2-9f15-4aef-9d4d-44f9c7b28051

import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse_monoidalV2
import Mathlib.CategoryTheory.Adjunction.Mates
import Definitions.Def_AlgebraicGeometry_CurveDegreeTests
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_positive_locally_free_rank_pushforward_structure
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_linearEquiv_cech_pushforward_of_finite
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_eulerChar_tensor_lineBundle_locallyFree

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace Philippon.InvertibleProjection
open CategoryTheory MonoidalCategory
universe u₁ u₂ v₁ v₂
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]

/-- A tensor inverse makes tensoring an equivalence; the equivalence constructor
supplies the adjunction coherences. -/
def tensorInverseEquivalence (N N' : C) (e : N ⊗ N' ≅ 𝟙_ C) : C ≌ C :=
  CategoryTheory.Equivalence.mk (tensorLeft N') (tensorLeft N)
    ((tensorLeftTensor N N').symm ≪≫
      (tensoringLeft C).mapIso e ≪≫ leftUnitorNatIso C).symm
    ((tensorLeftTensor N' N).symm ≪≫
      (tensoringLeft C).mapIso ((β_ N' N) ≪≫ e) ≪≫ leftUnitorNatIso C)

/-- The tensorator, viewed as a natural isomorphism of composite functors. -/
def monoidalTensorLeftIso (F : C ⥤ D) [F.Monoidal] (N : C) :
    F ⋙ tensorLeft (F.obj N) ≅ tensorLeft N ⋙ F :=
  NatIso.ofComponents (fun X => Functor.Monoidal.μIso F N X) (by
    intro X Y f
    exact Functor.LaxMonoidal.μ_natural_right F N f)

/-- A strong monoidal left adjoint satisfies the projection formula for
tensor-invertible objects, with no geometric assumptions. -/
def projectionIso (F : C ⥤ D) [F.Monoidal] (G : D ⥤ C) (adj : F ⊣ G)
    (N N' : C) (e : N ⊗ N' ≅ 𝟙_ C) (M : D) :
    N ⊗ G.obj M ≅ G.obj (F.obj N ⊗ M) := by
  let eD : F.obj N ⊗ F.obj N' ≅ 𝟙_ D :=
    Functor.Monoidal.μIso F N N' ≪≫ F.mapIso e ≪≫
      (Functor.Monoidal.εIso F).symm
  let adj₁ := (tensorInverseEquivalence N N' e).toAdjunction.comp adj
  let adj₂ := adj.comp (tensorInverseEquivalence (F.obj N) (F.obj N') eD).toAdjunction
  exact (conjugateIsoEquiv adj₁ adj₂ (monoidalTensorLeftIso F N')).app M

end Philippon.InvertibleProjection

namespace AlgebraicGeometry.Scheme.Modules
open CategoryTheory MonoidalCategory Philippon.InvertibleProjection
universe u

/-- The projection formula for an invertible sheaf and the structure sheaf. -/
def invertiblePushforwardPullbackIso {X Y : Scheme.{u}} (g : X ⟶ Y)
    (N : Y.Modules) (hN : IsInvertible N) :
    (pushforward g).obj ((pullback g).obj N) ≅
      N ⊗ (pushforward g).obj (𝟙_ X.Modules) := by
  let N' := hN.exists_tensor_inverse_monoidalV2.choose
  let e : N ⊗ N' ≅ 𝟙_ Y.Modules :=
    hN.exists_tensor_inverse_monoidalV2.choose_spec.2.some
  exact (projectionIso (pullback g) (pushforward g) (pullbackPushforwardAdjunction g)
    N N' e (𝟙_ X.Modules) ≪≫
      (pushforward g).mapIso (ρ_ ((pullback g).obj N))).symm

end AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AlgebraicGeometry.CurveDegreeTests.FinitePushforward
open CategoryTheory MonoidalCategory
universe u

/-- The Euler characteristic of the actual two-chart section complex. -/
def euler {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) (𝒰 : C.TwoAffineOpenCover) (M : C.Modules) : ℤ :=
  (Module.finrank K (𝒰.sectionsOf c M).H0 : ℤ) -
    Module.finrank K (𝒰.sectionsOf c M).H1

/-- The already proved comparison of section modules gives invariance under
an isomorphism of sheaves, with the affine charts unchanged. -/
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

/-- Finite pushforward preserves the Euler characteristic, conditional on
the open cohomology-comparison child. -/
theorem euler_pushforward (K : Type u) [Field K] {C D : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) (δ : D ⟶ Spec (.of K))
    [IsIntegral C] [IsIntegral D] [IsProper c] [IsProper δ]
    [SmoothOfRelativeDimension 1 c] [SmoothOfRelativeDimension 1 δ]
    (g : D ⟶ C) [IsFinite g] (hg : g ≫ c = δ)
    (𝒰 : C.TwoAffineOpenCover) (𝒱 : D.TwoAffineOpenCover)
    (M : D.Modules) (hM : Scheme.Modules.IsInvertible M) :
    euler δ 𝒱 M = euler c 𝒰 ((Scheme.Modules.pushforward g).obj M) := by
  obtain ⟨⟨e0⟩, ⟨e1⟩⟩ :=
    SmoothProperCurve.exists_linearEquiv_cech_pushforward_of_finite
      K c δ g hg 𝒰 𝒱 M hM
  unfold euler
  rw [e0.finrank_eq, e1.finrank_eq]

end AlgebraicGeometry.CurveDegreeTests.FinitePushforward

open AlgebraicGeometry CategoryTheory MonoidalCategory
open AlgebraicGeometry.CurveDegreeTests.FinitePushforward
universe u

theorem solution
    (K : Type u) [Field K] {C D : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) (δ : D ⟶ Spec (.of K))
    [IsIntegral C] [IsIntegral D] [IsProper c] [IsProper δ]
    [SmoothOfRelativeDimension 1 c] [SmoothOfRelativeDimension 1 δ]
    (g : D ⟶ C) [IsFinite g] [Surjective g] (hg : g ≫ c = δ)
    (𝒰 : C.TwoAffineOpenCover) (𝒱 : D.TwoAffineOpenCover) :
    let χC : C.Modules → ℤ := fun N =>
      (Module.finrank K (𝒰.sectionsOf c N).H0 : ℤ) -
        Module.finrank K (𝒰.sectionsOf c N).H1
    let χD : D.Modules → ℤ := fun N =>
      (Module.finrank K (𝒱.sectionsOf δ N).H0 : ℤ) -
        Module.finrank K (𝒱.sectionsOf δ N).H1
    ∃ d : ℕ, 0 < d ∧ ∀ N : C.Modules, Scheme.Modules.IsInvertible N →
      χD ((Scheme.Modules.pullback g).obj N) - χD (𝟙_ D.Modules) =
        (d : ℤ) * (χC N - χC (𝟙_ C.Modules)) := by
  change ∃ d : ℕ, 0 < d ∧ ∀ N : C.Modules, Scheme.Modules.IsInvertible N →
    euler δ 𝒱 ((Scheme.Modules.pullback g).obj N) - euler δ 𝒱 (𝟙_ D.Modules) =
      (d : ℤ) * (euler c 𝒰 N - euler c 𝒰 (𝟙_ C.Modules))
  obtain ⟨d, hd, hE⟩ :=
    SmoothProperCurve.exists_positive_locally_free_rank_pushforward_structure K c δ g hg
  refine ⟨d, hd, ?_⟩
  intro N hN
  let E := (Scheme.Modules.pushforward g).obj (𝟙_ D.Modules)
  have hχN : euler δ 𝒱 ((Scheme.Modules.pullback g).obj N) =
      euler c 𝒰 (N ⊗ E) :=
    (euler_pushforward K c δ g hg 𝒰 𝒱 _ (hN.pullback g)).trans
      (euler_iso c 𝒰 (Scheme.Modules.invertiblePushforwardPullbackIso g N hN))
  have hχO : euler δ 𝒱 (𝟙_ D.Modules) = euler c 𝒰 E :=
    euler_pushforward K c δ g hg 𝒰 𝒱 _ (Scheme.Modules.isInvertible_unit D)
  have hχ := SmoothProperCurve.eulerChar_tensor_lineBundle_locallyFree K c 𝒰 d E hE N hN
  change euler c 𝒰 (N ⊗ E) =
    (d : ℤ) * (euler c 𝒰 N - euler c 𝒰 (𝟙_ C.Modules)) + euler c 𝒰 E at hχ
  rw [hχN, hχO, hχ, add_sub_cancel_right]
