-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/f55824a3-dda1-5bbb-860c-44c3f9ef33d4

import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.AlgebraicGeometry.Properties
import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isIntegral

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel"
namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "chartAlg XMid fFin fInf ιFin ιInf glue_condition mem_range_ιFin_or_mem_range_ιInf"
p2m_open "AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

scoped instance isDomain_chartAlg' (S : Set F) : IsDomain (CommRingCat.of (chartAlg R F S)) :=
  inferInstanceAs (IsDomain (chartAlg R F S))

theorem range_ιFin_inter_range_ιInf_nonempty :
    (Set.range (ιFin R F j).base ∩ Set.range (ιInf R F j).base).Nonempty := by
  obtain ⟨z⟩ : Nonempty (XMid R F j) := inferInstance
  refine ⟨(fFin R F j ≫ ιFin R F j).base z, ⟨(fFin R F j).base z, ?_⟩, ⟨(fInf R F j).base z, ?_⟩⟩
  · rw [Scheme.Hom.comp_base, TopCat.comp_app]
  · rw [glue_condition, Scheme.Hom.comp_base, TopCat.comp_app]

theorem isPreirreducible_range_of_irreducibleSpace {Y : Scheme.{u}} [IrreducibleSpace Y]
    (f : Y ⟶ AlgebraicCurve.TwoChartIntegralModel R F j) : IsPreirreducible (Set.range f.base) := by
  rw [← Set.image_univ]
  exact ((IrreducibleSpace.isIrreducible_univ Y).image f.base
    f.continuous.continuousOn).isPreirreducible

theorem irreducibleSpace : IrreducibleSpace (AlgebraicCurve.TwoChartIntegralModel R F j) := by
  have hU₁o : IsOpen (Set.range (ιFin R F j).base) := (ιFin R F j).isOpenEmbedding.isOpen_range
  have hU₂o : IsOpen (Set.range (ιInf R F j).base) := (ιInf R F j).isOpenEmbedding.isOpen_range
  have hU₁i : IsPreirreducible (Set.range (ιFin R F j).base) :=
    isPreirreducible_range_of_irreducibleSpace R F j _
  have hU₂i : IsPreirreducible (Set.range (ιInf R F j).base) :=
    isPreirreducible_range_of_irreducibleSpace R F j _
  have hmeet := range_ιFin_inter_range_ιInf_nonempty R F j
  have h₁ : Set.range (ιFin R F j).base ⊆
      closure (Set.range (ιFin R F j).base ∩ Set.range (ιInf R F j).base) :=
    subset_closure_inter_of_isPreirreducible_of_isOpen hU₁i hU₂o hmeet
  have h₂ : Set.range (ιInf R F j).base ⊆
      closure (Set.range (ιFin R F j).base ∩ Set.range (ιInf R F j).base) := by
    rw [Set.inter_comm]
    exact subset_closure_inter_of_isPreirreducible_of_isOpen hU₂i hU₁o
      (by rwa [Set.inter_comm] at hmeet)
  have hcov : Set.range (ιFin R F j).base ∪ Set.range (ιInf R F j).base = Set.univ :=
    Set.eq_univ_of_forall (mem_range_ιFin_or_mem_range_ιInf R F j)
  have hdense : closure (Set.range (ιFin R F j).base ∩ Set.range (ιInf R F j).base) = Set.univ :=
    Set.eq_univ_of_univ_subset (hcov ▸ Set.union_subset h₁ h₂)
  have hpre : IsPreirreducible (Set.univ : Set (AlgebraicCurve.TwoChartIntegralModel R F j)) := by
    rw [← hdense]
    exact (hU₁i.open_subset (hU₁o.inter hU₂o) Set.inter_subset_left).closure
  obtain ⟨x, -⟩ := hmeet
  exact { isPreirreducible_univ := hpre, toNonempty := ⟨x⟩ }

theorem isReduced : IsReduced (AlgebraicCurve.TwoChartIntegralModel R F j) := by
  have (x : AlgebraicCurve.TwoChartIntegralModel R F j) :
      _root_.IsReduced ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk x) := by
    rcases mem_range_ιFin_or_mem_range_ιInf R F j x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact isReduced_of_injective _
        (asIso <| (ιFin R F j).stalkMap y).commRingCatIsoToRingEquiv.injective
    · exact isReduced_of_injective _
        (asIso <| (ιInf R F j).stalkMap y).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk _

theorem isIntegral_impl : IsIntegral (AlgebraicCurve.TwoChartIntegralModel R F j) :=
  haveI := isReduced R F j
  haveI := irreducibleSpace R F j
  isIntegral_of_irreducibleSpace_of_isReduced _

end AlgebraicCurve.TwoChartIntegralModel
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isIntegral.AlgebraicCurve P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isIntegral.AlgebraicCurve.TwoChartIntegralModel"
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isIntegral.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isIntegral.AlgebraicCurve P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isIntegral.AlgebraicCurve.TwoChartIntegralModel"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry _root_.AlgebraicCurve.TwoChartIntegralModel _root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isIntegral.AlgebraicCurve.TwoChartIntegralModel in
theorem solution.{u} (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)] :
    IsIntegral (AlgebraicCurve.TwoChartIntegralModel R F j) :=
  AlgebraicCurve.TwoChartIntegralModel.isIntegral_impl R F j

end S_AlgebraicCurve_TwoChartIntegralModel_isIntegral
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isIntegral (solution)
