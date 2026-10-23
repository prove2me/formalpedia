-- Prove2me | solution 1 for AlgebraicGeometry.SmoothProperCurve.exists_positive_locally_free_rank_pushforward_structure
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-22T16:58:20.774782+00:00
-- url     : https://prove2.me/submissions/09d94b8d-d57e-4ec5-b0e0-8f263bc05236

import Definitions.Def_AlgebraicGeometry_CurveDegreeTests
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver
import Theorems.Thm_AlgebraicGeometry_flat_and_finrank_eq_of_isFinite_of_surjective_of_ringKrullDim_le_one
import Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_ringKrullDim_stalk_eq_of_isClosed

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

namespace PhilipponFiniteCurveRank

lemma stalk_dimension_le (K : Type u) [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 c] (x : C) :
    ringKrullDim (C.presheaf.stalk x) ≤ 1 := by
  haveI : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  haveI : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace c
  obtain ⟨y, hyx, hy⟩ := nonempty_inter_closedPoints
    (Set.singleton_nonempty x |>.mono subset_closure) isClosed_closure.isLocallyClosed
  have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hyx
  have hd := SmoothOfRelativeDimension.ringKrullDim_stalk_eq_of_isClosed K c 1 y hy
  rw [ringKrullDim_stalk_eq_coheight] at hd ⊢
  exact (WithBot.coe_le_coe.mpr (Order.coheight_anti (show y ≤ x from hxy))).trans hd.le

end PhilipponFiniteCurveRank

theorem solution
    (K : Type u) [Field K] {C D : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) (δ : D ⟶ Spec (.of K))
    [IsIntegral C] [IsIntegral D] [IsProper c] [IsProper δ]
    [SmoothOfRelativeDimension 1 c] [SmoothOfRelativeDimension 1 δ]
    (g : D ⟶ C) [IsFinite g] [Surjective g] (hg : g ≫ c = δ) :
    ∃ d : ℕ, 0 < d ∧ ∀ x : C, ∃ U : C.Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj
        ((Scheme.Modules.pushforward g).obj (𝟙_ D.Modules)) ≅
          SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin d))) := by
  haveI : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  haveI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian c
  haveI : IsIntegrallyClosed Γ(Spec (.of K), ⊤) :=
    IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have hnormal : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x) := by
    intro x
    exact (Smooth.isDomain_and_isIntegrallyClosed_stalk c x).2
  let x₀ : C := Classical.choice inferInstance
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (show x₀ ∈ (⊤ : C.Opens) from trivial)
  haveI : Nonempty U := ⟨⟨x₀, hxU⟩⟩
  haveI : Algebra Γ(C, U) Γ(D, g ⁻¹ᵁ U) := (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  obtain ⟨hlfp, hflat, _⟩ := flat_and_finrank_eq_of_isFinite_of_surjective_of_ringKrullDim_le_one
    g hnormal (PhilipponFiniteCurveRank.stalk_dimension_le K c) U hU _ rfl
  haveI := hlfp
  haveI := hflat
  let d := g.finrank x₀
  have hd : ∀ x : C, g.finrank x = d := fun x =>
    g.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace x x₀
  have hpos : 0 < d := (Nat.succ_le_iff.mp
    ((g.one_le_finrank_iff_surjective).mpr inferInstance x₀))
  refine ⟨d, hpos, ?_⟩
  exact (Scheme.Modules.isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver
    g d hd (𝟙_ D.Modules) (fun x => ⟨⊤, trivial,
      ⟨Scheme.Modules.pullbackTensorUnitObjIso (g ⁻¹ᵁ ⊤).ι⟩⟩)).exists_trivialization
