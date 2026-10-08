-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralCurveProperties_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13IntegralCurveProperties_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:51:59.414439+00:00
-- url     : https://prove2.me/theorems/6d5ee98f-1789-49b9-8b5b-e809440956fe
-- title:
--   FLT.Assumptions.MazurProof.N13IntegralCurveProperties source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13IntegralCurveProperties

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13IntegralCurveProperties
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralCurveScheme_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralFractionalHull_p0
import Mathlib.AlgebraicGeometry.Properties

set_option autoImplicit false




/-!
# Integrality of the ordinary N13 model

The affine chart embeds in its rational generic fibre.  On the infinity
chart, the parameter `t` is regular because the coordinate ring is free over
`ℤ₂[t]`; localizing at `t` identifies it with the affine overlap.  Thus both
charts and their common principal open are domains.

The two irreducible chart images cover the glued scheme and have nonempty
intersection.  This proves that the ordinary two-chart N13 model is reduced,
irreducible, and integral without any point enumeration.
-/

open CategoryTheory
open Polynomial
open Set Topology

namespace MazurProof.N13IntegralCurveProperties

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

open AlgebraicGeometry

private abbrev AffineCurve :=
  N13OrdinaryCurveOverlap.AffineCurve

private abbrev InfinityCurve :=
  N13OrdinaryCurveOverlap.InfinityCurve

private abbrev AffineOverlap :=
  N13OrdinaryCurveOverlap.AffineOverlap

private abbrev InfinityOverlap :=
  N13OrdinaryCurveOverlap.InfinityOverlap

instance affineCurve_isDomain : IsDomain AffineCurve :=
  N13IntegralFractionalHull.integralToRational_injective.isDomain
    N13IntegralFractionalHull.integralToRational

theorem affine_xClass_ne_zero :
    N13OrdinaryCurveOverlap.xClass ≠ 0 := by
  intro h
  have h0 := congrArg
    (N13GeneralizedMumfordIntegral.coeff0
      (R := N13OrdinaryCurveOverlap.R₂)) h
  simp [N13OrdinaryCurveOverlap.xClass] at h0

instance affineOverlap_isDomain : IsDomain AffineOverlap :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      affine_xClass_ne_zero)

instance infinityOverlap_isDomain : IsDomain InfinityOverlap :=
  N13OrdinaryCurveOverlap.overlapEquiv.symm.toMulEquiv.isDomain
    AffineOverlap

/-- The infinity parameter is a non-zero-divisor.  This is the free-module
argument: multiplication by `t` is scalar multiplication by the nonzero
polynomial `X` on a free `ℤ₂[t]`-module. -/
theorem infinity_tClass_mem_nonZeroDivisors :
    N13IntegralInfinityChart.tClass ∈
      nonZeroDivisors InfinityCurve := by
  apply IsRegular.mem_nonZeroDivisors
  rw [← isLeftRegular_iff_isRegular]
  intro z w h
  apply
    (IsRegular.of_ne_zero
      (Polynomial.X_ne_zero :
        (Polynomial.X :
          N13IntegralInfinityChart.Base) ≠ 0)).smul_right_injective
      InfinityCurve
  simpa [N13IntegralInfinityChart.tClass,
    Algebra.smul_def] using h

theorem infinity_powers_le_nonZeroDivisors :
    Submonoid.powers N13IntegralInfinityChart.tClass ≤
      nonZeroDivisors InfinityCurve :=
  Submonoid.powers_le.mpr
    infinity_tClass_mem_nonZeroDivisors

theorem infinity_to_overlap_injective :
    Function.Injective
      (algebraMap InfinityCurve InfinityOverlap) :=
  IsLocalization.injective InfinityOverlap
    infinity_powers_le_nonZeroDivisors

instance infinityCurve_isDomain : IsDomain InfinityCurve :=
  infinity_to_overlap_injective.isDomain
    (algebraMap InfinityCurve InfinityOverlap)

private instance chart_isIntegral (i : Bool) :
    IsIntegral (N13IntegralCurveScheme.chart i) := by
  cases i <;>
    dsimp [N13IntegralCurveScheme.chart] <;>
    infer_instance

/-- Two irreducible open subsets with nonempty intersection and union the
whole space make the ambient space irreducible. -/
private theorem irreducibleSpace_of_two_open_cover
    {X : Type*} [TopologicalSpace X]
    (A B : Set X)
    (hAopen : IsOpen A)
    (_hBopen : IsOpen B)
    (hcover : A ∪ B = Set.univ)
    (hAirr : IsIrreducible A)
    (hBirr : IsIrreducible B)
    (hAB : (A ∩ B).Nonempty) :
    IrreducibleSpace X := by
  rw [irreducibleSpace_def]
  have hAdense : Dense A := by
    rw [dense_iff_inter_open]
    intro W hW hWne
    by_cases hWA : (W ∩ A).Nonempty
    · exact hWA
    · have hBW : (B ∩ W).Nonempty := by
        obtain ⟨x, hxW⟩ := hWne
        have hxCover : x ∈ A ∪ B := by
          rw [hcover]
          trivial
        rcases hxCover with hxA | hxB
        · exact (hWA ⟨x, hxW, hxA⟩).elim
        · exact ⟨x, hxB, hxW⟩
      have hBA : (B ∩ A).Nonempty := by
        simpa [inter_comm] using hAB
      rcases
          hBirr.isPreirreducible
            W A hW hAopen hBW hBA with
        ⟨x, hxB, hxW, hxA⟩
      exact ⟨x, hxW, hxA⟩
  have hclosure : IsIrreducible (closure A) :=
    hAirr.closure
  rw [hAdense.closure_eq] at hclosure
  simpa using hclosure

private def affineRange :
    Set N13IntegralCurveScheme.IntegralCurve :=
  Set.range
    (N13IntegralCurveScheme.glueData.ι false).base

private def infinityRange :
    Set N13IntegralCurveScheme.IntegralCurve :=
  Set.range
    (N13IntegralCurveScheme.glueData.ι true).base

private theorem affineRange_open :
    IsOpen affineRange :=
  (N13IntegralCurveScheme.glueData.ι false).isOpenEmbedding.isOpen_range

private theorem infinityRange_open :
    IsOpen infinityRange :=
  (N13IntegralCurveScheme.glueData.ι true).isOpenEmbedding.isOpen_range

private theorem affineRange_irreducible :
    IsIrreducible affineRange := by
  rw [affineRange, ← Set.image_univ]
  exact
    (IrreducibleSpace.isIrreducible_univ
      (N13IntegralCurveScheme.chart false).carrier).image
      (N13IntegralCurveScheme.glueData.ι false).base
      (N13IntegralCurveScheme.glueData.ι false).base.hom.continuous.continuousOn

private theorem infinityRange_irreducible :
    IsIrreducible infinityRange := by
  rw [infinityRange, ← Set.image_univ]
  exact
    (IrreducibleSpace.isIrreducible_univ
      (N13IntegralCurveScheme.chart true).carrier).image
      (N13IntegralCurveScheme.glueData.ι true).base
      (N13IntegralCurveScheme.glueData.ι true).base.hom.continuous.continuousOn

private theorem ranges_cover :
    affineRange ∪ infinityRange = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  obtain ⟨i, y, hy⟩ :=
    N13IntegralCurveScheme.glueData.ι_jointly_surjective x
  subst x
  cases i
  · exact Or.inl ⟨y, rfl⟩
  · exact Or.inr ⟨y, rfl⟩

private noncomputable def overlapPoint :
    (N13IntegralCurveScheme.glueData.V (false, true)).carrier := by
  let p : (Spec (.of AffineOverlap)).carrier :=
    Classical.choice
      (inferInstance :
        Nonempty (Spec (.of AffineOverlap)).carrier)
  simpa [N13IntegralCurveScheme.glueData,
    CategoryTheory.GlueData.ofGlueData',
    N13IntegralCurveScheme.glueData',
    N13IntegralCurveScheme.overlap] using p

private theorem ranges_inter_nonempty :
    (affineRange ∩ infinityRange).Nonempty := by
  let z := overlapPoint
  refine
    ⟨N13IntegralCurveScheme.glueData.ι false
        (N13IntegralCurveScheme.glueData.f false true z),
      ?_, ?_⟩
  · exact ⟨_, rfl⟩
  · refine
      ⟨N13IntegralCurveScheme.glueData.f true false
          (N13IntegralCurveScheme.glueData.t false true z),
        ?_⟩
    have h :=
      congrArg (fun q => q z)
        (N13IntegralCurveScheme.glueData.glue_condition false true)
    change
      N13IntegralCurveScheme.glueData.ι true
          (N13IntegralCurveScheme.glueData.f true false
            (N13IntegralCurveScheme.glueData.t false true z)) =
        N13IntegralCurveScheme.glueData.ι false
          (N13IntegralCurveScheme.glueData.f false true z) at h
    exact h

instance integralCurve_isReduced :
    IsReduced N13IntegralCurveScheme.IntegralCurve := by
  letI :
      ∀ i : Bool,
        IsReduced
          ((N13IntegralCurveScheme.glueData.openCover).X i) :=
    fun i => by
      change IsReduced (N13IntegralCurveScheme.chart i)
      infer_instance
  exact IsReduced.of_openCover
    N13IntegralCurveScheme.IntegralCurve
    N13IntegralCurveScheme.glueData.openCover

instance integralCurve_irreducibleSpace :
    IrreducibleSpace N13IntegralCurveScheme.IntegralCurve :=
  irreducibleSpace_of_two_open_cover
    affineRange
    infinityRange
    affineRange_open
    infinityRange_open
    ranges_cover
    affineRange_irreducible
    infinityRange_irreducible
    ranges_inter_nonempty

instance integralCurve_isIntegral :
    IsIntegral N13IntegralCurveScheme.IntegralCurve :=
  isIntegral_of_irreducibleSpace_of_isReduced
    N13IntegralCurveScheme.IntegralCurve

end

end MazurProof.N13IntegralCurveProperties


