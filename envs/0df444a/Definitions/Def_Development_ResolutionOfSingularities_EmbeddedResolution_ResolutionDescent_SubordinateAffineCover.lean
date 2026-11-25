-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SubordinateAffineCover
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SubordinateAffineCover
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T02:03:47.678492+00:00
-- url     : https://prove2.me/theorems/9a1168ca-eb4d-40bc-b2ba-c11f6ccf18d5
-- title:
--   Subordinate Affine Cover
-- statement:
--   Definitions and structural lemmas for Subordinate Affine Cover, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SubordinateAffineCover.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpens
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_smooth_sigmaDesc
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_sigma___sigmaOpensDesc_a310daec50eb
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_sigma___sigmaOpensDesc_assoc_1a480721dd20

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
universe u
def affineOpensLePreimageCover {X' X : Scheme.{u}} (φ : X' ⟶ X) {ι : Type u}
    (U : ι → X.Opens) : Set X'.Opens :=
  {W : X'.Opens | IsAffineOpen W ∧ ∃ i, W ≤ φ ⁻¹ᵁ (U i)}
noncomputable def opensCoprodMapOfRefinement {X' X : Scheme.{u}} (φ : X' ⟶ X) {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → X'.Opens) (β : κ → ι)
    (hβ : ∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) :
    sigmaOpens X' V ⟶ sigmaOpens X U :=
  Sigma.desc fun a =>
    φ.resLE (U (β a)) (V a) (hβ a) ≫ Sigma.ι (fun i => (U i).toScheme) (β a)
@[simp]
theorem sigmaι_opensCoprodMapOfRefinement {X' X : Scheme.{u}} (φ : X' ⟶ X) {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → X'.Opens) (β : κ → ι)
    (hβ : ∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) (a : κ) :
    Sigma.ι (fun a => (V a).toScheme) a ≫ opensCoprodMapOfRefinement φ U V β hβ =
      φ.resLE (U (β a)) (V a) (hβ a) ≫ Sigma.ι (fun i => (U i).toScheme) (β a) := by
  simp [opensCoprodMapOfRefinement]
theorem opensCoprodMapOfRefinement_comp_sigmaOpensDesc {X' X : Scheme.{u}} (φ : X' ⟶ X) {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → X'.Opens) (β : κ → ι)
    (hβ : ∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) :
    opensCoprodMapOfRefinement φ U V β hβ ≫ sigmaOpensDesc X U = sigmaOpensDesc X' V ≫ φ := by
  refine Limits.Sigma.hom_ext _ _ fun a => ?_
  rw [← Category.assoc, sigmaι_opensCoprodMapOfRefinement, Category.assoc, sigma_ι_sigmaOpensDesc,
    sigma_ι_sigmaOpensDesc_assoc]
  simp
theorem resLE_eq_homOfLE_comp_restrict {X' X : Scheme.{u}} (φ : X' ⟶ X)
    (U : X.Opens) (V : X'.Opens) (e : V ≤ φ ⁻¹ᵁ U) :
    φ.resLE U V e = X'.homOfLE e ≫ φ ∣_ U := by
  rw [← cancel_mono U.ι]
  simp
theorem smooth_resLE {X' X : Scheme.{u}} (φ : X' ⟶ X) [Smooth φ]
    (U : X.Opens) (V : X'.Opens) (e : V ≤ φ ⁻¹ᵁ U) :
    Smooth (φ.resLE U V e) := by
  rw [resLE_eq_homOfLE_comp_restrict]
  infer_instance
theorem smooth_opensCoprodMapOfRefinement {X' X : Scheme.{u}} (φ : X' ⟶ X) [Smooth φ] {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → X'.Opens) (β : κ → ι)
    (hβ : ∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) :
    Smooth (opensCoprodMapOfRefinement φ U V β hβ) := by
  show Smooth (Sigma.desc fun a => φ.resLE (U (β a)) (V a) (hβ a) ≫
      Sigma.ι (fun i => (U i).toScheme) (β a))
  refine smooth_sigmaDesc _ fun a => ?_
  have := smooth_resLE φ (U (β a)) (V a) (hβ a)
  infer_instance
instance instSmoothOpensCoprodRefine {X' X : Scheme.{u}} (φ : X' ⟶ X) [Smooth φ] {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → X'.Opens) (β : κ → ι)
    (hβ : ∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) :
    Smooth (opensCoprodMapOfRefinement φ U V β hβ) :=
  smooth_opensCoprodMapOfRefinement φ U V β hβ
theorem locallyOfFiniteType_opensCoprodMapOfRefinement {X' X : Scheme.{u}} (φ : X' ⟶ X)
    [LocallyOfFiniteType φ] {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → X'.Opens) (β : κ → ι)
    (hβ : ∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) :
    LocallyOfFiniteType (opensCoprodMapOfRefinement φ U V β hβ) := by
  have h1 : LocallyOfFiniteType (sigmaOpensDesc X' V ≫ φ) := inferInstance
  have h2 : LocallyOfFiniteType (opensCoprodMapOfRefinement φ U V β hβ ≫ sigmaOpensDesc X U) := by
    rw [opensCoprodMapOfRefinement_comp_sigmaOpensDesc]
    exact h1
  exact locallyOfFiniteType_of_comp _ (sigmaOpensDesc X U)
instance instLocallyOfFiniteTypeOpensCoprodRefine {X' X : Scheme.{u}} (φ : X' ⟶ X)
    [LocallyOfFiniteType φ] {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → X'.Opens) (β : κ → ι)
    (hβ : ∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) :
    LocallyOfFiniteType (opensCoprodMapOfRefinement φ U V β hβ) :=
  locallyOfFiniteType_opensCoprodMapOfRefinement φ U V β hβ
end FunctorialResolution.EmbeddedResolution


