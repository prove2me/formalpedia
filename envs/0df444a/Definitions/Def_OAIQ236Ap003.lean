-- Prove2me | Definitions.Def_OAIQ236Ap003
-- name    : OAIQ236Ap003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T19:48:17.955446+00:00
-- url     : https://prove2.me/theorems/2dea7d77-8ac7-4a6b-8a4a-690d3fab5216
-- title:
--   Definitions bundle OAIQ236Ap003 of the split of OpenAI, Parabolic intersections in Artin groups
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure` and `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections`, carved from OpenAI's openai/math development (OpenAI, *Parabolic intersections in Artin groups*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 347 declarations of OpenAI's Lean: 117 definitions, 1 inductive type or structure, 1 instance and 228 theorems. The definitions and types are `OAI.HarmonicArtin.Geometric.invariantForm`, `OAI.HarmonicArtin.Geometric.invariantScale`, `OAI.HarmonicArtin.HasPositiveHead`, `OAI.HarmonicArtin.ParabolicIntersections.GraphRealization.Space`, `OAI.HarmonicArtin.ParabolicIntersections.GraphRealization.act`, `OAI.HarmonicArtin.ParabolicIntersections.GraphRealization.actPoint`, `OAI.HarmonicArtin.ParabolicIntersections.GraphRealization.action`, `OAI.HarmonicArtin.ParabolicIntersections.GraphRealization.arc`, `OAI.HarmonicArtin.ParabolicIntersections.GraphRealization.embed`, `OAI.HarmonicArtin.ParabolicIntersections.GraphRealization.premetric`, `OAI.HarmonicArtin.ParabolicIntersections.GraphRealization.product`, `OAI.HarmonicArtin.ParabolicIntersections.GraphRealization.vertex`, `OAI.HarmonicArtin.ParabolicIntersections.MeshNilpotent`, `OAI.HarmonicArtin.ParabolicIntersections.QuiverSimpleOn`, `OAI.HarmonicArtin.ParabolicIntersections.VisualAmalgam`, `OAI.HarmonicArtin.ParabolicIntersections.VisualVertex`, `OAI.HarmonicArtin.ParabolicIntersections.artinExponent`, `OAI.HarmonicArtin.ParabolicIntersections.artinMap`, `OAI.HarmonicArtin.ParabolicIntersections.instMulActionArtinVisualVertex`, `OAI.HarmonicArtin.ParabolicIntersections.instMulActionArtinVisualVertex_1`, `OAI.HarmonicArtin.ParabolicIntersections.meshArrowValues`, `OAI.HarmonicArtin.ParabolicIntersections.meshChosenArrow`, `OAI.HarmonicArtin.ParabolicIntersections.meshQuiverGraph`, `OAI.HarmonicArtin.ParabolicIntersections.meshQuiverNeighborEquiv`, `OAI.HarmonicArtin.ParabolicIntersections.meshRelation`, `OAI.HarmonicArtin.ParabolicIntersections.meshRelations`, `OAI.HarmonicArtin.ParabolicIntersections.parabolicComponent`, `OAI.HarmonicArtin.ParabolicIntersections.parabolicRead`, `OAI.HarmonicArtin.ParabolicIntersections.parabolicRep`, `OAI.HarmonicArtin.ParabolicIntersections.parabolicRetractionAction`, `OAI.HarmonicArtin.ParabolicIntersections.parabolicStepArtin`, `OAI.HarmonicArtin.ParabolicIntersections.parabolicStepLetter`, `OAI.HarmonicArtin.ParabolicIntersections.parabolicStepPerm`, `OAI.HarmonicArtin.ParabolicIntersections.parabolicStepRatio`, `OAI.HarmonicArtin.ParabolicIntersections.parabolicSubtree`, `OAI.HarmonicArtin.ParabolicIntersections.parabolicWordPerm`, `OAI.HarmonicArtin.ParabolicIntersections.positiveSupport`, `OAI.HarmonicArtin.ParabolicIntersections.positiveSupportHom`, `OAI.HarmonicArtin.ParabolicIntersections.visualAction`, `OAI.HarmonicArtin.ParabolicIntersections.visualEdgeInclusion` and 78 more.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `ArtinGroups_Cancellation_BlockPivot`, `ArtinGroups_Complexes_BlockClosed`, `ArtinGroups_Complexes_CoefficientSocle`, `ArtinGroups_Complexes_ColorBoundary`, `ArtinGroups_Complexes_DiagonalVertex`, `ArtinGroups_Complexes_FiniteSum`, `ArtinGroups_Complexes_FiniteSum2`, `ArtinGroups_Complexes_GeneratorArray`, `ArtinGroups_Complexes_GeneratorVector`, `ArtinGroups_Complexes_PlacementSignedWeight`, `ArtinGroups_Complexes_Refl`, `ArtinGroups_Complexes_ScalarSupported`, `ArtinGroups_Complexes_UnfoldedCartanSymm`, `ArtinGroups_Coxeter_AlternatingLiftProd`, `ArtinGroups_Coxeter_ArtinCoxeter`, `ArtinGroups_Coxeter_ParabolicProductMap`, `ArtinGroups_Functors_Index`, `ArtinGroups_Functors_LevelGeneratorEquiv`, `ArtinGroups_Functors_Path`, `ArtinGroups_Functors_Path2`, `ArtinGroups_Functors_PathMarked`, `ArtinGroups_Functors_ZigzagLinear`, `ArtinGroups_Geometry_CartanOffNonpos`, `ArtinGroups_Geometry_CartanRestricted`, `ArtinGroups_Geometry_InvariantForm`, `ArtinGroups_Geometry_LongestMulSelf`, `ArtinGroups_Geometry_RestrictionLength`, `ArtinGroups_Geometry_RootNonnegAscent`, `ArtinGroups_Geometry_RootNonposDescent`, `ArtinGroups_Geometry_RootRowOrthogonalWord`, `ArtinGroups_Harmonic_Candidate`, `ArtinGroups_Harmonic_Coset`, `ArtinGroups_Harmonic_CosetVertex`, `ArtinGroups_Harmonic_Crossing`, `ArtinGroups_Harmonic_DimensionNonneg`, `ArtinGroups_Harmonic_DimensionPosMultiplicityPos`, `ArtinGroups_Harmonic_FiniteFusionEdge`, `ArtinGroups_Harmonic_FinsuppMapDomainFiber`, `ArtinGroups_Harmonic_FusionColorRegion`, `ArtinGroups_Harmonic_FusionFactorStep`, `ArtinGroups_Harmonic_FusionFold`, `ArtinGroups_Harmonic_FusionLabel`, `ArtinGroups_Harmonic_FusionPacketPerm`, `ArtinGroups_Harmonic_FusionRest`, `ArtinGroups_Harmonic_FusionZeroLabel`, `ArtinGroups_Harmonic_GeneratorPlacement`, `ArtinGroups_Harmonic_Harmonic`, `ArtinGroups_Harmonic_LeftSector`, `ArtinGroups_Harmonic_Level`, `ArtinGroups_Harmonic_PacketWord`, `ArtinGroups_Harmonic_PositiveDegreeHom`, `ArtinGroups_Harmonic_PositiveHead`, `ArtinGroups_Harmonic_PositiveLiftSimple`, `ArtinGroups_Harmonic_PositiveSimpleLiftMul`, `ArtinGroups_Harmonic_PredAboveSuccSucc`, `ArtinGroups_Harmonic_PrismFlag`, `ArtinGroups_Harmonic_PrismPrefix`, `ArtinGroups_Harmonic_PrismSimplexZero`, `ArtinGroups_Harmonic_ProbeFixedOutside`, `ArtinGroups_Harmonic_QuantumNumber`, `ArtinGroups_Harmonic_ReducedExpression`, `ArtinGroups_Harmonic_RestrictedArtinHom`, `ArtinGroups_Harmonic_RowReflect`, `ArtinGroups_Harmonic_SphericalFoldedMatrix`, `ArtinGroups_Harmonic_SphericalPair`, `ArtinGroups_Harmonic_StringAdjacent`, `ArtinGroups_Harmonic_UnfoldedHom`, `ArtinGroups_Harmonic_UnfoldedMatrix`, `ArtinGroups_ParabolicIntersections_ArtinRelabel`, `ArtinGroups_ParabolicIntersections_CosetContainment`, `ArtinGroups_ParabolicIntersections_GeneratorPowers`, `ArtinGroups_ParabolicIntersections_GraphRealizationAction`, `ArtinGroups_ParabolicIntersections_GraphRealizationDistance`, `ArtinGroups_ParabolicIntersections_GraphRealizationHyperbolic`, `ArtinGroups_ParabolicIntersections_GraphRealizationSpace`, `ArtinGroups_ParabolicIntersections_MeshNilpotence`, `ArtinGroups_ParabolicIntersections_MeshQuiver`, `ArtinGroups_ParabolicIntersections_MeshQuiverWords`, `ArtinGroups_ParabolicIntersections_ParabolicCosetProjection`, `ArtinGroups_ParabolicIntersections_ParabolicMinimumStep`, `ArtinGroups_ParabolicIntersections_ParabolicRead`, `ArtinGroups_ParabolicIntersections_ParabolicReadBraid`, `ArtinGroups_ParabolicIntersections_ParabolicReadReduced`, `ArtinGroups_ParabolicIntersections_ParabolicRetractionAction`, `ArtinGroups_ParabolicIntersections_PositiveSupport`, `ArtinGroups_ParabolicIntersections_PositiveTransport`, `ArtinGroups_ParabolicIntersections_VisualAmalgam`, `ArtinGroups_ParabolicIntersections_VisualParabolicSubtree`, `ArtinGroups_ParabolicIntersections_VisualTree`, `ArtinGroups_ParabolicIntersections_VisualTreeProperties`, `ArtinGroups_Quivers_Level`, `ArtinGroups_Quivers_LinearMatrix`, `ArtinGroups_Quivers_ProbeVertex`, `ArtinGroups_Quivers_Reduction`, `ArtinGroups_Quivers_StringArrow`, `ArtinGroups_Quivers_VertexHom`, `ArtinGroups_Quivers_VertexLinear`, `ArtinGroups_Quivers_VertexMinimal`, `ArtinGroups_Realizations_CellDeligne`, `ArtinGroups_Realizations_FusionWeightSplit`, `ArtinGroups_Realizations_NerveOrderMap`, `ArtinGroups_Realizations_NerveOrderRetractionEquiv`, `ArtinGroups_Realizations_NervePrismPatch`, `ArtinGroups_Realizations_NervePrismValue`, `ArtinGroups_Realizations_RealizeSimplex`.
--
--   **Imports.** It imports the published bundle `Def_ArtinParabolicIntersections`; the bundles `OAIQ236Ap000` and `OAIQ236Ap001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ236Ap005`, `OAIQ236Ap006` and `OAIQ236Ap007`.
-- source:
--   OpenAI, Parabolic intersections in Artin groups, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.List.ChainOfFn
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.PushoutI
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.Isometry
import Definitions.Def_ArtinParabolicIntersections
import Definitions.Def_OAIQ236Ap000
import Definitions.Def_OAIQ236Ap001

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_VertexHom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver
namespace Zigzag

variable {V A K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

def vertexHom (v : V) : Q.Zigzag K →+* K where
  toFun x := x.vertex v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

end Zigzag
end HarmonicArtin.ReversibleQuiver

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_GeneratorPlacement
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.dual_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.source_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.target_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_false _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

namespace ReversibleQuiver.Zigzag

variable {V A K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

variable {I J L : Type*}

lemma reduction_support {p : I → GeneratorPlacement V} {q : J → GeneratorPlacement V}
    {M : Matrix I J (Q.Zigzag K)} (hc : ProjectiveEntries Q p q M)
    (hd : MapDegree Q p q 0 0 M) (i : I) (j : J) (v : V)
    (hne : (M i j).vertex v ≠ 0) : p i = q j ∧ (p i).color = v := by
  have hleft := congrArg (fun x : Q.Zigzag K => x.vertex v) (hc.1 i j)
  have hright := congrArg (fun x : Q.Zigzag K => x.vertex v) (hc.2 i j)
  have hpv : (p i).color = v := by
    by_contra h
    have hh : v ≠ (p i).color := Ne.symm h
    change (vertexId Q (p i).color).vertex v * (M i j).vertex v = (M i j).vertex v at hleft
    rw [vertexId_eval, ite_eq_right hh] at hleft
    exact hne (hleft.symm.trans (MulZeroClass.zero_mul _))
  have hqv : (q j).color = v := by
    by_contra h
    have hh : v ≠ (q j).color := Ne.symm h
    change (M i j).vertex v * (vertexId Q (q j).color).vertex v = (M i j).vertex v at hright
    rw [vertexId_eval, ite_eq_right hh] at hright
    exact hne (hright.symm.trans (MulZeroClass.mul_zero _))
  have hcq : (q j).cochain = (p i).cochain := by
    by_contra h
    have hz := (hd i j).1 (by simpa only [add_zero] using h)
    exact hne (by simp [hz])
  have hiq : (p i).internal = (q j).internal := by
    by_contra h
    have hz := (hd i j).2.1 (by simpa only [zero_add, sub_ne_zero] using h)
    exact hne (by rw [hz]; rfl)
  exact ⟨by cases hp : p i; cases hq : q j; simp_all, hpv⟩

namespace BasedComplex

variable [Fintype I] [Fintype J] [Fintype L]

noncomputable def multiplicity (E : BasedComplex Q (K := K) I) (a : GeneratorPlacement V) : ℕ :=
  Nat.card {i : I // E.placement i = a}

end BasedComplex
end ReversibleQuiver.Zigzag
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_Level
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

namespace ReversibleQuiver.Zigzag

variable {V A K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

namespace BasedComplex

variable {I : Type*} [Fintype I]

noncomputable def restrict (E : BasedComplex Q (K := K) I) (T : Set I) [Fintype T]
    (hT : ∀ i ∈ T, ∀ j ∈ T, ∀ k ∉ T,
      E.differential i k * E.differential k j = 0) :
    BasedComplex Q (K := K) T := by
  classical
  exact {
    placement := fun i => E.placement i
    differential := fun i j => E.differential i j
    entries := ⟨fun i j => E.entries.1 i j, fun i j => E.entries.2 i j⟩
    degree := fun i j => E.degree i j
    square_zero := by
      apply Matrix.ext
      intro i j
      change (∑ k : T, E.differential i k * E.differential k j) = 0
      have he := congrArg (fun M : Matrix I I (Q.Zigzag K) => M i j) E.square_zero
      change (∑ k, E.differential i k * E.differential k j) = 0 at he
      rw [← he]
      apply Fintype.sum_of_injective (Subtype.val : T → I) Subtype.val_injective
      · intro k hk
        apply hT i i.property j j.property k
        intro hkT
        exact hk ⟨⟨k, hkT⟩, rfl⟩
      · intro k
        rfl }

end BasedComplex
end ReversibleQuiver.Zigzag
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Cancellation_BlockPivot
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

namespace BlockPivot

variable {E : BasedComplex Q (K := K) (J ⊕ J ⊕ I)}

omit [DecidableEq I] [DecidableEq J] in
lemma retained_sum {X Y : Type*} (U : Matrix X (J ⊕ J ⊕ I) (Q.Zigzag K))
    (M : Matrix (J ⊕ J ⊕ I) Y (Q.Zigzag K))
    (hU : ∀ i j, U i (.inr (.inl j)) = 0) (hM : ∀ i j, M (.inl i) j = 0)
    (i : X) (j : Y) :
    (∑ k : I, U i (.inr (.inr k)) * M (.inr (.inr k)) j) = (U * M) i j := by
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, hU, hM, MulZeroClass.mul_zero,
    MulZeroClass.zero_mul, Finset.sum_const_zero, zero_add]

end BlockPivot
end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_BlockClosed
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K:Type*} (Q:ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I:Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

def BlockClosed (E:BasedComplex Q (K:=K) I) (T:Set I) : Prop :=
  ∀ i j, E.differential i j ≠ 0 → (i∈T ↔ j∈T)

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma BlockClosed.restrict_condition {E:BasedComplex Q (K:=K) I} {T:Set I}
    (h:BlockClosed Q E T) : ∀ i∈T,∀ j∈T,∀ k∉T,E.differential i k*E.differential k j=0 := by
  intro i hi j _ k hk
  have hz:E.differential i k=0 := by
    by_contra hh
    exact hk ((h i k hh).mp hi)
  rw [hz,zero_mul]

noncomputable def blockRestriction (E:BasedComplex Q (K:=K) I) (T:Set I)
    (h:BlockClosed Q E T) : BasedComplex Q (K:=K) T :=
  E.restrict Q T h.restrict_condition

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_Reduction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.dual_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.source_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.target_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_false _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J L : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

def reductionAt (p : I → GeneratorPlacement V) (q : J → GeneratorPlacement V)
    (M : Matrix I J (Q.Zigzag K)) (a : GeneratorPlacement V) :
    Matrix {i // p i = a} {j // q j = a} K :=
  fun i j => (M i.1 j.1).vertex a.color

lemma reductionAt_add (p : I → GeneratorPlacement V) (q : J → GeneratorPlacement V)
    (M N : Matrix I J (Q.Zigzag K)) (a : GeneratorPlacement V) :
    reductionAt Q p q (M + N) a = reductionAt Q p q M a + reductionAt Q p q N a := rfl

lemma reductionAt_identity [DecidableEq I] (p : I → GeneratorPlacement V)
    (a : GeneratorPlacement V) :
    reductionAt Q p p (projectiveIdentity Q (K := K) p) a = 1 := by
  classical
  apply Matrix.ext
  intro i j
  by_cases h : i = j
  · subst j
    simp [reductionAt, projectiveIdentity, i.property]
  · have h' : (i : I) ≠ (j : I) := fun he => h (Subtype.ext he)
    simp [reductionAt, projectiveIdentity, h, h']

lemma reductionAt_mul [Fintype J]
    (p : I → GeneratorPlacement V) (q : J → GeneratorPlacement V)
    (r : L → GeneratorPlacement V) (M : Matrix I J (Q.Zigzag K))
    (N : Matrix J L (Q.Zigzag K)) (a : GeneratorPlacement V)
    (hc : ProjectiveEntries Q p q M) (hd : MapDegree Q p q 0 0 M) :
    reductionAt Q p r (M * N) a =
      reductionAt Q p q M a * reductionAt Q q r N a := by
  classical
  apply Matrix.ext
  intro i l
  change (vertexHom Q (K := K) a.color) ((M * N) i.1 l.1) = _
  simp only [Matrix.mul_apply, map_sum, map_mul]
  apply Finset.sum_congr_set {j | q j = a}
  · intro j hj
    rfl
  · intro j hj
    have hz : (M i.1 j).vertex a.color = 0 := by
      by_contra hn
      have hs := (reduction_support Q hc hd i.1 j a.color hn).1
      exact hj (hs.symm.trans i.property)
    change (M i.1 j).vertex a.color * (N j l.1).vertex a.color = 0
    rw [hz]
    exact MulZeroClass.zero_mul _

end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_Level
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J L : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

namespace BasedComplex

variable [Fintype I] [Fintype J] [Fintype L]

structure ChainIsomorphism [DecidableEq I] [DecidableEq J]
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J) where
  forward : Map Q E F
  backward : Map Q F E
  sourceEquation : forward.matrix * backward.matrix = projectiveIdentity Q E.placement
  targetEquation : backward.matrix * forward.matrix = projectiveIdentity Q F.placement

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_DiagonalVertex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.dual_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.source_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.target_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_false _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V]

omit [Fintype V] in
lemma tokenBasis_mul_positive (α : V) (x : Q.Zigzag K) (hx : x.vertex = 0) :
    tokenBasis Q α * x = 0 := by
  apply ext
  · change (tokenBasis Q α * x).vertex = 0
    rw [vertex_mul]
    change (0 : V → K) * x.vertex = 0
    exact MulZeroClass.zero_mul _
  · change (tokenBasis Q α * x).arrow = 0
    rw [arrow_mul]
    change Q.leftScale 0 x.arrow + Q.rightScale 0 x.vertex = 0
    ext a
    simp [leftScale, rightScale]
  · change (tokenBasis Q α * x).token = 0
    rw [token_mul]
    change (0 : V → K) * x.token + (Pi.single α (1 : K)) * x.vertex + Q.backtrack 0 x.arrow = 0
    rw [hx]
    ext a
    simp

omit [Fintype V] in
lemma positive_mul_tokenBasis (α : V) (x : Q.Zigzag K) (hx : x.vertex = 0) :
    x * tokenBasis Q α = 0 := by
  apply ext
  · change (x * tokenBasis Q α).vertex = 0
    rw [vertex_mul]
    change x.vertex * (0 : V → K) = 0
    exact MulZeroClass.mul_zero _
  · change (x * tokenBasis Q α).arrow = 0
    rw [arrow_mul]
    change Q.leftScale x.vertex 0 + Q.rightScale x.arrow 0 = 0
    ext a
    simp [leftScale, rightScale]
  · change (x * tokenBasis Q α).token = 0
    rw [token_mul]
    change x.vertex * (Pi.single α (1 : K)) + x.token * (0 : V → K) + Q.backtrack x.arrow 0 = 0
    rw [hx]
    ext a
    simp

namespace BasedComplex
variable {I J : Type*} [Fintype I] [Fintype J]

def diagonalVertex (E : BasedComplex Q (K := K) I) (i : I) :
    Matrix I I (Q.Zigzag K) →ₗ[K] K where
  toFun f := (f i i).vertex (E.placement i).color
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [DecidableEq I]

omit [Fintype V] in
lemma diagonalVertex_identity (E : BasedComplex Q (K := K) I) (i : I) :
    diagonalVertex Q E i (projectiveIdentity Q E.placement) = 1 := by
  change (projectiveIdentity Q (K := K) E.placement i i).vertex (E.placement i).color = 1
  rw [projectiveIdentity, Matrix.diagonal_apply_eq, vertexId_eval, ite_eq_left rfl]

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_LinearMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V]
variable {I J : Type*} [Fintype I] [Fintype J]

def LinearMatrix (f : Matrix I J (Q.Zigzag K)) : Prop :=
  ∀ i j, (f i j).vertex = 0 ∧ (f i j).token = 0

end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_VertexLinear
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J L : Type*}

def vertexLinear : Q.Zigzag K →ₗ[K] (V → K) where
  toFun := vertex
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma vertex_sum {T : Type*} (s : Finset T) (f : T → Q.Zigzag K) :
    (∑ t ∈ s, f t).vertex = ∑ t ∈ s, (f t).vertex :=
  map_sum (vertexLinear Q) f s

end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_CoefficientSocle
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

def coefficientSocle (E : BasedComplex Q (K := K) I) (α : V) (c : ℤ) :
    Submodule K (I → K) where
  carrier := {x | (∀ i, (E.placement i).color ≠ α ∨ (E.placement i).cochain ≠ c → x i = 0) ∧
    ∀ j a, Q.source a = α → ∑ i, x i * (E.differential i j).arrow a = 0}
  zero_mem' := by constructor <;> simp
  add_mem' := by
    rintro x y ⟨hx,hxd⟩ ⟨hy,hyd⟩
    constructor
    · intro i hi; simp only [Pi.add_apply, hx i hi, hy i hi, add_zero]
    · intro j a ha
      simp only [Pi.add_apply, _root_.add_mul, Finset.sum_add_distrib, hxd j a ha, hyd j a ha, add_zero]
  smul_mem' := by
    rintro r x ⟨hx,hxd⟩
    constructor
    · intro i hi; simp only [Pi.smul_apply, hx i hi, smul_zero]
    · intro j a ha
      simp only [Pi.smul_apply, smul_eq_mul, _root_.mul_assoc, ← Finset.mul_sum, hxd j a ha,
        MulZeroClass.mul_zero]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_GeneratorVector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def generatorVector (E : BasedComplex Q (K := K) I) : V → ℝ :=
  fun α => Nat.card {i : I // (E.placement i).color = α}

omit [Fintype V] [DecidableEq A] in
lemma generatorVector_sum (E : BasedComplex Q (K := K) I) (α : V) :
    generatorVector Q E α = ∑ i, if (E.placement i).color = α then (1 : ℝ) else 0 := by
  classical
  simp only [generatorVector, Nat.card_eq_fintype_card, Fintype.card_subtype,
    ← Finset.sum_boole]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ColorBoundary
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K:Type*} (Q:ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I:Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

def colorBoundary (U:Set V) : Set V :=
  {v | v∉U ∧ ∃ a:A,Q.source a∈U ∧ Q.target a=v}

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_FiniteSum
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V] [Fintype I] [DecidableEq I]
  {T R : I → Type*} [∀ i, Fintype (T i)] [∀ i, Fintype (R i)]

noncomputable def finiteSum (E : (i:I) → BasedComplex Q (K := K) (T i)) :
    BasedComplex Q (K := K) (Sigma T) where
  placement := fun x => (E x.1).placement x.2
  differential := Matrix.blockDiagonal' (fun i => (E i).differential)
  entries := by
    constructor
    · rintro ⟨i,x⟩ ⟨j,y⟩
      by_cases h : i=j
      · subst j
        rw [Matrix.blockDiagonal'_apply_eq]
        exact (E i).entries.1 x y
      · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h,mul_zero]
    · rintro ⟨i,x⟩ ⟨j,y⟩
      by_cases h : i=j
      · subst j
        rw [Matrix.blockDiagonal'_apply_eq]
        exact (E i).entries.2 x y
      · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h,zero_mul]
  degree := by
    rintro ⟨i,x⟩ ⟨j,y⟩
    by_cases h : i=j
    · subst j
      rw [Matrix.blockDiagonal'_apply_eq]
      exact (E i).degree x y
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
      exact ⟨fun _ => rfl,homogeneous_zero Q _⟩
  square_zero := by
    rw [← Matrix.blockDiagonal'_mul]
    simp only [(E _).square_zero]
    exact Matrix.blockDiagonal'_zero

noncomputable def Map.finiteSum
    {E : (i:I) → BasedComplex Q (K := K) (T i)}
    {F : (i:I) → BasedComplex Q (K := K) (R i)} (f : (i:I) → Map Q (E i) (F i)) :
    Map Q (finiteSum Q E) (finiteSum Q F) where
  matrix := Matrix.blockDiagonal' (fun i => (f i).matrix)
  entries := by
    constructor
    · rintro ⟨i,x⟩ ⟨j,y⟩
      by_cases h : i=j
      · subst j
        rw [Matrix.blockDiagonal'_apply_eq]
        exact (f i).entries.1 x y
      · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h,mul_zero]
    · rintro ⟨i,x⟩ ⟨j,y⟩
      by_cases h : i=j
      · subst j
        rw [Matrix.blockDiagonal'_apply_eq]
        exact (f i).entries.2 x y
      · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h,zero_mul]
  degree := by
    rintro ⟨i,x⟩ ⟨j,y⟩
    by_cases h : i=j
    · subst j
      rw [Matrix.blockDiagonal'_apply_eq]
      exact (f i).degree x y
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
      exact ⟨fun _ => rfl,homogeneous_zero Q _⟩
  commute := by
    change Matrix.blockDiagonal' (fun i => (E i).differential) * Matrix.blockDiagonal' (fun i => (f i).matrix) =
      Matrix.blockDiagonal' (fun i => (f i).matrix) * Matrix.blockDiagonal' (fun i => (F i).differential)
    rw [← Matrix.blockDiagonal'_mul,← Matrix.blockDiagonal'_mul]
    congr 1
    funext i
    exact (f i).commute

lemma finiteSum_identity [∀ i, DecidableEq (T i)]
    (E : (i:I) → BasedComplex Q (K := K) (T i)) :
    Matrix.blockDiagonal' (fun i => projectiveIdentity Q (K := K) (E i).placement) =
      projectiveIdentity Q (finiteSum Q E).placement := by
  classical
  apply Matrix.ext
  rintro ⟨i,x⟩ ⟨j,y⟩
  by_cases h : i=j
  · subst j
    rw [Matrix.blockDiagonal'_apply_eq]
    simp only [projectiveIdentity,Matrix.diagonal_apply,Sigma.mk.inj_iff,heq_eq_eq,
      true_and,finiteSum]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
    have he : (⟨i,x⟩ : Sigma T) ≠ ⟨j,y⟩ := fun he => h (congrArg Sigma.fst he)
    simp only [projectiveIdentity,Matrix.diagonal_apply,ite_eq_right he]

noncomputable def ChainIsomorphism.finiteSum [∀ i, DecidableEq (T i)] [∀ i, DecidableEq (R i)]
    {E : (i:I) → BasedComplex Q (K := K) (T i)}
    {F : (i:I) → BasedComplex Q (K := K) (R i)}
    (f : (i:I) → ChainIsomorphism Q (E i) (F i)) :
    ChainIsomorphism Q (finiteSum Q E) (finiteSum Q F) where
  forward := Map.finiteSum Q (fun i => (f i).forward)
  backward := Map.finiteSum Q (fun i => (f i).backward)
  sourceEquation := by
    change Matrix.blockDiagonal' (fun i => (f i).forward.matrix) * Matrix.blockDiagonal' (fun i => (f i).backward.matrix) = _
    rw [← Matrix.blockDiagonal'_mul]
    simp only [(f _).sourceEquation]
    exact finiteSum_identity Q E
  targetEquation := by
    change Matrix.blockDiagonal' (fun i => (f i).backward.matrix) * Matrix.blockDiagonal' (fun i => (f i).forward.matrix) = _
    rw [← Matrix.blockDiagonal'_mul]
    simp only [(f _).targetEquation]
    exact finiteSum_identity Q F

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_FiniteSum2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]
  {T R : I → Type*} [∀ i, Fintype (T i)] [∀ i, Fintype (R i)]
  [∀ i, DecidableEq (T i)] [∀ i, DecidableEq (R i)]

omit [Fintype V] [DecidableEq A] [∀ i, DecidableEq (T i)] in
lemma finiteSum_entries (E : (i:I) → BasedComplex Q (K := K) (T i))
    (M : (i:I) → Matrix (T i) (T i) (Zigzag Q K))
    (hM : ∀ i, ProjectiveEntries Q (E i).placement (E i).placement (M i)) :
    ProjectiveEntries Q (finiteSum Q E).placement (finiteSum Q E).placement
      (Matrix.blockDiagonal' M) := by
  constructor
  all_goals
    rintro ⟨i,x⟩ ⟨j,y⟩
    by_cases h : i=j
    · subst j
      rw [Matrix.blockDiagonal'_apply_eq]
      first | exact (hM i).1 x y | exact (hM i).2 x y
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
      first | exact MulZeroClass.mul_zero _ | exact MulZeroClass.zero_mul _

omit [Fintype V] [DecidableEq A] [∀ i, DecidableEq (T i)] in
lemma finiteSum_degree (E : (i:I) → BasedComplex Q (K := K) (T i))
    (M : (i:I) → Matrix (T i) (T i) (Zigzag Q K)) {n v : ℤ}
    (hM : ∀ i, MapDegree Q (E i).placement (E i).placement n v (M i)) :
    MapDegree Q (finiteSum Q E).placement (finiteSum Q E).placement n v
      (Matrix.blockDiagonal' M) := by
  rintro ⟨i,x⟩ ⟨j,y⟩
  by_cases h : i=j
  · subst j
    rw [Matrix.blockDiagonal'_apply_eq]
    exact hM i x y
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
    exact ⟨fun _ => rfl,homogeneous_zero Q _⟩

noncomputable def HomotopyEquivalence.finiteSum
    {E : (i:I) → BasedComplex Q (K := K) (T i)}
    {F : (i:I) → BasedComplex Q (K := K) (R i)}
    (f : (i:I) → HomotopyEquivalence Q (E i) (F i)) :
    HomotopyEquivalence Q (finiteSum Q E) (finiteSum Q F) where
  forward := Map.finiteSum Q (fun i => (f i).forward)
  backward := Map.finiteSum Q (fun i => (f i).backward)
  sourceHomotopy := Matrix.blockDiagonal' (fun i => (f i).sourceHomotopy)
  targetHomotopy := Matrix.blockDiagonal' (fun i => (f i).targetHomotopy)
  sourceEntries := finiteSum_entries Q E _ (fun i => (f i).sourceEntries)
  targetEntries := finiteSum_entries Q F _ (fun i => (f i).targetEntries)
  sourceDegree := finiteSum_degree Q E _ (fun i => (f i).sourceDegree)
  targetDegree := finiteSum_degree Q F _ (fun i => (f i).targetDegree)
  sourceEquation := by
    change Matrix.blockDiagonal' (fun i => (f i).forward.matrix) * Matrix.blockDiagonal' (fun i => (f i).backward.matrix) = _
    rw [← finiteSum_identity Q E]
    change _ = Matrix.blockDiagonal' (fun i => projectiveIdentity Q (E i).placement) +
      (Matrix.blockDiagonal' (fun i => (E i).differential) * Matrix.blockDiagonal' (fun i => (f i).sourceHomotopy) +
       Matrix.blockDiagonal' (fun i => (f i).sourceHomotopy) * Matrix.blockDiagonal' (fun i => (E i).differential))
    rw [← Matrix.blockDiagonal'_mul,← Matrix.blockDiagonal'_mul,← Matrix.blockDiagonal'_mul,
      ← Matrix.blockDiagonal'_add,← Matrix.blockDiagonal'_add]
    congr 1
    funext i
    exact (f i).sourceEquation
  targetEquation := by
    change Matrix.blockDiagonal' (fun i => (f i).backward.matrix) * Matrix.blockDiagonal' (fun i => (f i).forward.matrix) = _
    rw [← finiteSum_identity Q F]
    change _ = Matrix.blockDiagonal' (fun i => projectiveIdentity Q (F i).placement) +
      (Matrix.blockDiagonal' (fun i => (F i).differential) * Matrix.blockDiagonal' (fun i => (f i).targetHomotopy) +
       Matrix.blockDiagonal' (fun i => (f i).targetHomotopy) * Matrix.blockDiagonal' (fun i => (F i).differential))
    rw [← Matrix.blockDiagonal'_mul,← Matrix.blockDiagonal'_mul,← Matrix.blockDiagonal'_mul,
      ← Matrix.blockDiagonal'_add,← Matrix.blockDiagonal'_add]
    congr 1
    funext i
    exact (f i).targetEquation

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_GeneratorArray
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V] [Fintype I] [Fintype J]

noncomputable def generatorArray (E : BasedComplex Q (K := K) I) :
    GeneratorPlacement V →₀ ℕ := ∑ i, Finsupp.single (E.placement i) 1

lemma generatorArray_apply (E : BasedComplex Q (K := K) I) (a : GeneratorPlacement V) :
    E.generatorArray Q a = E.multiplicity Q a := by
  classical
  simp only [generatorArray, Finsupp.finsetSum_apply, Finsupp.single_apply,
    multiplicity, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [Finset.sum_boole, Nat.cast_id]

noncomputable def levelArray (E : BasedComplex Q (K := K) I) : V × ℤ →₀ ℕ :=
  (E.generatorArray Q).mapDomain (fun a => (a.color, a.level))

lemma levelArray_eq_sum (E : BasedComplex Q (K := K) I) :
    E.levelArray Q = ∑ i, Finsupp.single ((E.placement i).color, (E.placement i).level) 1 := by
  simp only [levelArray, generatorArray, Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single]

lemma levelArray_apply (E : BasedComplex Q (K := K) I) (v : V) (d : ℤ) :
    E.levelArray Q (v, d) = Nat.card {i : I //
      (E.placement i).color = v ∧ (E.placement i).level = d} := by
  classical
  simp only [levelArray_eq_sum, Finsupp.finsetSum_apply, Finsupp.single_apply,
    Prod.mk.injEq, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [Finset.sum_boole, Nat.cast_id]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PlacementSignedWeight
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def placementSignedWeight (a : GeneratorPlacement V) (v : V) : ℝ :=
  if a.color=v then cochainSign a.level else 0

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_Refl
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I J L N : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  [Fintype I] [Fintype J] [Fintype L] [Fintype N]
  [DecidableEq I] [DecidableEq J] [DecidableEq L] [DecidableEq N]

noncomputable def ChainIsomorphism.symm {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (a : ChainIsomorphism Q E F) :
    ChainIsomorphism Q F E where
  forward := a.backward
  backward := a.forward
  sourceEquation := a.targetEquation
  targetEquation := a.sourceEquation

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ScalarSupported
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I J : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def ScalarSupported (E:BasedComplex Q (K:=K) I) (l c:ℤ) (x:I→K) : Prop :=
  ∀ i,¬ ((E.placement i).level=l ∧ (E.placement i).cochain=c)→x i=0

def ScalarExactAt (E:BasedComplex Q (K:=K) I) (α:V) (l c:ℤ) : Prop :=
  ∀ x:I→K,ScalarSupported Q E l c x→
    Matrix.vecMul x (E.differential.map (vertexHom Q α))=0→
    ∃ y:I→K,ScalarSupported Q E (l-1) (c-1) y ∧
      Matrix.vecMul y (E.differential.map (vertexHom Q α))=x

omit [DecidableEq I] in
lemma scalarSupported_sub (E:BasedComplex Q (K:=K) I) {l c:ℤ} {x y:I→K}
    (hx:ScalarSupported Q E l c x) (hy:ScalarSupported Q E l c y) :
    ScalarSupported Q E l c (x-y) := by
  intro i hi
  change x i-y i=0
  rw [hx i hi,hy i hi,sub_self]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_UnfoldedCartanSymm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
open scoped _root_.Matrix

variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

variable {I : Type*} [Fintype I]

omit [Fintype V] [DecidableEq A] in
lemma generatorVector_nonneg (E : BasedComplex Q (K := K) I) (α : V) :
    0 ≤ generatorVector Q E α := Nat.cast_nonneg _

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_Path
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Iso
open Zigzag

variable {V A W B K : Type*} {Q : ReversibleQuiver V A} {R : ReversibleQuiver W B}
  (e : Iso Q R)

variable [Field K] [Fintype A] [Fintype B] [DecidableEq V] [DecidableEq W]
lemma path_coordinates (x:Q.Zigzag K) (p:Path V A) :
    pathCoordinates R (e.zigzagLinear x) (e.path p) = pathCoordinates Q x p := by
  rcases p with v|a|v
  · change x.vertex (e.vertex.symm (e.vertex v)) = x.vertex v
    rw [Equiv.symm_apply_apply]
  · change x.arrow (e.arrow.symm (e.arrow a)) = x.arrow a
    rw [Equiv.symm_apply_apply]
  · change x.token (e.vertex.symm (e.vertex v)) = x.token v
    rw [Equiv.symm_apply_apply]

variable [Fintype V] [Fintype W] [DecidableEq A] [DecidableEq B]

def cornerPath (s t:V) : CornerPath Q s t ≃ CornerPath R (e.vertex s) (e.vertex t) where
  toFun p := ⟨e.path p, (e.path_source p).trans (congrArg e.vertex p.property.1),
    (e.path_target p).trans (congrArg e.vertex p.property.2)⟩
  invFun p := ⟨e.path.symm p,by
    have hs := e.path_source (e.path.symm p)
    have ht := e.path_target (e.path.symm p)
    simp only [Equiv.apply_symm_apply,p.property.1,p.property.2] at hs ht
    exact ⟨e.vertex.injective hs.symm,e.vertex.injective ht.symm⟩⟩
  left_inv p := Subtype.ext (e.path.symm_apply_apply p)
  right_inv p := Subtype.ext (e.path.apply_symm_apply p)

end HarmonicArtin.ReversibleQuiver.Iso

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_Crossing
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.GraphConnection

variable {J K : Type*} [Fintype J] [DecidableEq J] [Field K]

variable (N : J → J → Prop) [DecidableRel N]

theorem crossing_square (μ : J → K) (hμ : ∀ a, μ a ≠ 0) (δ A : K)
    (hA : A ≠ 0) (hroot : A^2 + A⁻¹^2 + δ = 0)
    (hPF : ∀ a, ∑ b ∈ neighbors N a, μ b = δ * μ a)
    (a a' b c : J) (hba : N b a) (hba' : N b a') (hca : N c a)
    (hca' : N c a') :
    (∑ d ∈ neighbors N b ∩ neighbors N c,
      crossing μ A a b c d * crossing μ A b a' d c) =
      if a = a' then μ c / μ a else 0 := by
  classical
  by_cases hbc : b = c
  · subst c
    rw [Finset.inter_self]
    have ha : a ∈ neighbors N b := (mem_neighbors _ _ _).2 hba
    have ha' : a' ∈ neighbors N b := (mem_neighbors _ _ _).2 hba'
    have hexp (d : J) : crossing μ A a b b d * crossing μ A b a' d b =
        (if a = d then A^2 else 0) +
        (if a = d ∧ a' = d then μ b / μ a else 0) +
        μ d / μ b + (if a' = d then A⁻¹^2 else 0) := by
      unfold crossing
      simp only [ite_true, if_true]
      by_cases ha : a = d <;> by_cases ha' : a' = d <;>
        simp only [ha, ha', ite_true, if_true, ite_false, if_false, and_self, true_and, false_and]
      all_goals subst_vars
      all_goals field_simp [hA, hμ]
      all_goals ring
    simp_rw [hexp, Finset.sum_add_distrib]
    have hs1 : (∑ d ∈ neighbors N b, if a = d then A^2 else 0) = A^2 := by
      simpa only [eq_comm] using Finset.sum_ite_eq' (neighbors N b) a (fun _ => A^2)
        |>.trans (ite_eq_left ha)
    have hs4 : (∑ d ∈ neighbors N b, if a' = d then A⁻¹^2 else 0) = A⁻¹^2 := by
      simpa only [eq_comm] using Finset.sum_ite_eq' (neighbors N b) a' (fun _ => A⁻¹^2)
        |>.trans (ite_eq_left ha')
    have hs2 : (∑ d ∈ neighbors N b, if a = d ∧ a' = d then μ b / μ a else 0) =
        if a = a' then μ b / μ a else 0 := by
      by_cases haa : a = a'
      · subst a'
        simp only [and_self, ite_true, if_true]
        simpa only [eq_comm] using Finset.sum_ite_eq' (neighbors N b) a (fun _ => μ b / μ a)
          |>.trans (ite_eq_left ha)
      · rw [ite_eq_right haa]
        apply Finset.sum_eq_zero
        intro d hd
        exact ite_eq_right (fun equalities => haa (equalities.1.trans equalities.2.symm))
    have hs3 : (∑ d ∈ neighbors N b, μ d / μ b) = δ := by
      rw [← Finset.sum_div, hPF, mul_div_cancel_right₀ _ (hμ b)]
    rw [hs1,hs2,hs3,hs4]
    linear_combination hroot
  · have ha : a ∈ neighbors N b ∩ neighbors N c := by simp [hba,hca]
    have hexp (d : J) : crossing μ A a b c d * crossing μ A b a' d c =
        if a = d ∧ a' = d then μ c / μ a else 0 := by
      unfold crossing
      simp only [hbc, ite_false, if_false, add_zero, zero_add]
      by_cases ha : a = d <;> by_cases ha' : a' = d <;>
        simp only [ha,ha',ite_true, if_true,ite_false, if_false,and_self,true_and,false_and]
      all_goals field_simp [hA, hμ]
      all_goals ring
    simp_rw [hexp]
    by_cases haa : a = a'
    · subst a'
      simp only [and_self,ite_true, if_true]
      simpa only [eq_comm] using Finset.sum_ite_eq' (neighbors N b ∩ neighbors N c) a
        (fun _ => μ c / μ a) |>.trans (ite_eq_left ha)
    · rw [ite_eq_right haa]
      apply Finset.sum_eq_zero
      intro d hd
      exact ite_eq_right (fun equalities => haa (equalities.1.trans equalities.2.symm))

end HarmonicArtin.GraphConnection

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_StringArrow
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver

variable {V B J K : Type*} (Q : ReversibleQuiver V B)

variable (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
    (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)

namespace StringFunctor

variable [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]

local notation "I" => StringIndex (V := V) N

lemma sum_over {R : Type*} [AddCommMonoid R] (a : V × J) (f : I → R) :
    (∑ i : I, if i.old=a then f i else 0) = ∑ c : {c : J // N a.2 c}, f (liftIndex N a c) := by
  symm
  apply Fintype.sum_of_injective (liftIndex N a)
  · intro c d h
    apply Subtype.ext
    exact congrArg StringIndex.label h
  · intro i hi
    have hv : i.old ≠ a := by
      intro h
      apply hi
      refine ⟨⟨i.label,?_⟩,?_⟩
      · rw [← h]
        exact i.property
      · apply StringIndex.ext
        · exact h.symm
        · rfl
    exact ite_eq_right hv
  · intro c
    simp [liftIndex,StringIndex.old]

end StringFunctor
end HarmonicArtin.ReversibleQuiver

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_Index
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor

variable {V B J K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)

abbrev Index {T : Type*} (p : T → GeneratorPlacement (V × J)) :=
  (i : T) × {c : J // N (p i).color.2 c}

def placement {T : Type*} (p : T → GeneratorPlacement (V × J)) :
    Index N p → GeneratorPlacement (V × J) :=
  fun i => ⟨((p i.1).color.1,i.2),(p i.1).cochain,(p i.1).internal⟩

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_LeftSector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.GraphConnection
variable {J K : Type*} [Fintype J] [DecidableEq J] [Field K]
  (N : J → J → Prop) [DecidableRel N] (hN : ∀ ⦃left right⦄, N left right → N right left)

include hN in
lemma marked_sector_inverse (μ : J → K) (hμ : ∀ a, μ a ≠ 0) (δ A : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ neighbors N a, μ b = δ * μ a) (b c : J) :
    Matrix.of (fun (a : LeftSector N true b c) (d : RightSector N true b c) => crossing μ A a b c d) *
      Matrix.of (fun (d : RightSector N true b c) (a : LeftSector N true b c) =>
        crossing μ A b a d c * (μ a / μ c)) =
      (1 : Matrix (LeftSector N true b c) (LeftSector N true b c) K) := by
  classical
  ext a a'
  simp only [Matrix.mul_apply, Matrix.of_apply,← mul_assoc,← Finset.sum_mul]
  have hs : (∑ d : RightSector N true b c, crossing μ A a b c d * crossing μ A b a' d c) =
      if a.val=a'.val then μ c / μ a else 0 := by
    rw [← crossing_square N μ hμ δ A hA hroot hPF a a' b c
      (hN a.property.1) (hN a'.property.1) (hN a.property.2) (hN a'.property.2)]
    exact (Finset.sum_subtype (neighbors N b ∩ neighbors N c)
      (fun d => show d ∈ neighbors N b ∩ neighbors N c ↔ N b d ∧ N c d by simp)
      (fun d => crossing μ A a b c d * crossing μ A b a' d c)).symm
  rw [hs]
  by_cases he : a=a'
  · subst a'
    simp only [↓reduceIte,Matrix.one_apply_eq]
    field_simp [hμ]
  · rw [ite_eq_right (fun equality => he (Subtype.ext equality)),zero_mul,Matrix.one_apply_ne he]

include hN in
lemma sector_inverse (μ : J → K) (hμ : ∀ a, μ a ≠ 0) (δ A : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ neighbors N a, μ b = δ * μ a)
    (b c : J) (r : K) (hr : r ≠ 0) (marked : Bool) :
    sectorSwitch N μ A b c r marked * sectorUnswitch N μ A b c r marked=1 := by
  cases marked
  · exact scalar_sector_inverse N b c r hr
  · exact marked_sector_inverse N hN μ hμ δ A hA hroot hPF b c

end HarmonicArtin.GraphConnection

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_PathMarked
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor

variable {V B J K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃left right⦄, N left right → N right left)
  [Fintype J] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)

def pathMarked : Path V B → Bool
  | .inl _ => false
  | .inr (.inl e) => step e
  | .inr (.inr _) => false

abbrev PathLeft (p : Path V B) (b c : J) :=
  GraphConnection.LeftSector N (pathMarked step p) b c
abbrev PathRight (p : Path V B) (b c : J) :=
  GraphConnection.RightSector N (pathMarked step p) b c

def pathScalar (p : Path V B) (b c : J) : K :=
  match p with
  | .inl _ => 1
  | .inr (.inl e) => if orient e then μ c / μ b else 1
  | .inr (.inr _) => μ c / μ b

omit [Fintype J] [DecidableEq J] in
lemma pathScalar_ne_zero (hμ : ∀ a, μ a ≠ 0) (p : Path V B) (b c : J) :
    pathScalar orient μ p b c ≠ 0 := by
  rcases p with v|e|v
  · exact one_ne_zero
  · simp only [pathScalar]; split
    · exact div_ne_zero (hμ c) (hμ b)
    · exact one_ne_zero
  · exact div_ne_zero (hμ c) (hμ b)

def pathSwitch (p : Path V B) (b c : J) : Matrix (PathLeft step N p b c) (PathRight step N p b c) K :=
  GraphConnection.sectorSwitch N μ A b c (pathScalar orient μ p b c) (pathMarked step p)

def pathUnswitch (p : Path V B) (b c : J) : Matrix (PathRight step N p b c) (PathLeft step N p b c) K :=
  GraphConnection.sectorUnswitch N μ A b c (pathScalar orient μ p b c) (pathMarked step p)

include hN in
lemma pathSwitch_inverse (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (p : Path V B) (b c : J) :
    pathSwitch step N orient μ A p b c * pathUnswitch step N orient μ A p b c = 1 :=
  GraphConnection.sector_inverse N hN μ hμ δ A hA hroot hPF b c
    (pathScalar orient μ p b c) (pathScalar_ne_zero orient μ hμ p b c) (pathMarked step p)

include hN in
lemma pathUnswitch_inverse (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (p : Path V B) (b c : J) :
    pathUnswitch step N orient μ A p b c * pathSwitch step N orient μ A p b c = 1 := by
  classical
  exact (Matrix.mul_eq_one_comm_of_equiv (GraphConnection.sectorEquiv N hN (pathMarked step p) b c)).mp
    (pathSwitch_inverse step N hN orient μ A hμ δ hA hroot hPF p b c)

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_QuantumNumber
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

lemma stringMultiplicity_le_one (m : ℕ) (i j : StringLabel m) :
    stringMultiplicity m i j ≤ 1 := by
  unfold stringMultiplicity
  split_ifs <;> omega

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionLabel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

variable {E : Type*} [Fintype E] [DecidableEq E] (m : E → ℕ)

lemma factorMultiplicity_le_one (e : E) (L L' : FusionLabel m) :
    factorMultiplicity m e L L' ≤ 1 := by
  unfold factorMultiplicity
  split_ifs
  · exact stringMultiplicity_le_one _ _ _
  · omega

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_VertexMinimal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J L : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

def VertexMinimal [Fintype I] (E : BasedComplex Q (K := K) I) (v : V) : Prop :=
  ∀ i j, (E.differential i j).vertex v = 0

lemma vertexEntries_zero_left {p : I → GeneratorPlacement V} {q : J → GeneratorPlacement V}
    {M : Matrix I J (Q.Zigzag K)} (hM : ProjectiveEntries Q p q M)
    (i : I) (j : J) {v : V} (hv : (p i).color ≠ v) : (M i j).vertex v = 0 := by
  have h := congrArg (fun x : Q.Zigzag K => x.vertex v) (hM.1 i j)
  change (vertexId Q (p i).color).vertex v * (M i j).vertex v = (M i j).vertex v at h
  rw [vertexId_eval, ite_eq_right (Ne.symm hv), MulZeroClass.zero_mul] at h
  exact h.symm

lemma vertexEntries_zero_right {p : I → GeneratorPlacement V} {q : J → GeneratorPlacement V}
    {M : Matrix I J (Q.Zigzag K)} (hM : ProjectiveEntries Q p q M)
    (i : I) (j : J) {v : V} (hv : (q j).color ≠ v) : (M i j).vertex v = 0 := by
  have h := congrArg (fun x : Q.Zigzag K => x.vertex v) (hM.2 i j)
  change (M i j).vertex v * (vertexId Q (q j).color).vertex v = (M i j).vertex v at h
  rw [vertexId_eval, ite_eq_right (Ne.symm hv), MulZeroClass.mul_zero] at h
  exact h.symm

lemma reductionAt_vertex_boundary [Fintype I]
    (E : BasedComplex Q (K := K) I) (H : Matrix I I (Q.Zigzag K))
    (a : GeneratorPlacement V) (hE : VertexMinimal Q E a.color) :
    reductionAt Q E.placement E.placement (E.differential * H + H * E.differential) a = 0 := by
  apply Matrix.ext
  intro i j
  change (vertexHom Q (K := K) a.color)
    ((E.differential * H + H * E.differential) i.val j.val) = 0
  simp only [Matrix.add_apply, Matrix.mul_apply, map_add, map_sum, map_mul]
  change (∑ k, (E.differential i.val k).vertex a.color * (H k j.val).vertex a.color) +
    (∑ k, (H i.val k).vertex a.color * (E.differential k j.val).vertex a.color) = 0
  have hz (i j : I) : (E.differential i j).vertex a.color = 0 := hE i j
  simp only [hz, MulZeroClass.zero_mul, MulZeroClass.mul_zero, Finset.sum_const_zero, add_zero]

namespace BasedComplex

variable [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem multiplicity_eq_of_vertex_homotopyEquivalence
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (h : HomotopyEquivalence Q E F) (a : GeneratorPlacement V)
    (hE : VertexMinimal Q E a.color) (hF : VertexMinimal Q F a.color) :
    E.multiplicity Q a = F.multiplicity Q a := by
  classical
  let f := reductionAt Q E.placement F.placement h.forward.matrix a
  let g := reductionAt Q F.placement E.placement h.backward.matrix a
  have hfg : f * g = 1 := by
    dsimp only [f, g]
    rw [← reductionAt_mul Q _ _ _ _ _ a h.forward.entries h.forward.degree,
      h.sourceEquation, reductionAt_add, reductionAt_identity,
      reductionAt_vertex_boundary Q E _ a hE, add_zero]
  have hgf : g * f = 1 := by
    dsimp only [f, g]
    rw [← reductionAt_mul Q _ _ _ _ _ a h.backward.entries h.backward.degree,
      h.targetEquation, reductionAt_add, reductionAt_identity,
      reductionAt_vertex_boundary Q F _ a hF, add_zero]
  have hd := (Matrix.toLinearEquivRight'OfInv hfg hgf).finrank_eq
  simpa only [multiplicity, Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one, Nat.card_eq_fintype_card] using hd.symm

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_LevelGeneratorEquiv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
universe u
attribute [local instance] Classical.propDecidable
variable {V B J : Type u} {K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second : J⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
open Zigzag.BasedComplex

variable (orient : B → Bool) (μ : J → K) (A : K)
  (ho : ∀ b, orient (Q.reverse b) = !(orient b))
  (hμ : ∀ a, μ a ≠ 0) (δ : K)
  (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
  (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)

variable {T : Type u} [Fintype T] [DecidableEq T]
def levelGeneratorEquiv (p : T → GeneratorPlacement (V × J)) (v:V) (j:J) (d:ℤ) :
    {i : Index N p // (placement N p i).color=(v,j) ∧ (placement N p i).level=d} ≃
      (Σ a : {a:J // N a j}, {i:T // (p i).color=(v,(a:J)) ∧ (p i).level=d}) where
  toFun x := ⟨⟨(p x.val.1).color.2,by
      have hj := congrArg Prod.snd x.property.1
      change x.val.2.val=j at hj
      simpa only [← hj] using x.val.2.property⟩,
    x.val.1,⟨Prod.ext (by have h := congrArg Prod.fst x.property.1; exact h) rfl,x.property.2⟩⟩
  invFun x := ⟨⟨x.2.val,⟨j,by simpa only [x.2.property.1] using x.1.property⟩⟩,
    ⟨Prod.ext (by have h := congrArg Prod.fst x.2.property.1; exact h) rfl,x.2.property.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact (congrArg Prod.snd x.property.1).symm
  right_inv x := by
    apply Sigma.ext
    · apply Subtype.ext
      exact congrArg Prod.snd x.2.property.1
    · have ha := congrArg Prod.snd x.2.property.1
      dsimp only at ha
      apply (Subtype.heq_iff_coe_eq (fun i => by simp only [ha])).mpr
      rfl

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_StringAdjacent
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.labelSplit_apply _root_.OAI.HarmonicArtin.labelSplit_symm_at _root_.OAI.HarmonicArtin.labelSplit_symm_rest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

lemma stringAdjacent_symm (m : ℕ) :
    ∀ ⦃first second : StringLabel m⦄, stringAdjacent m first second → stringAdjacent m second first :=
  fun _ _ h => h.symm

lemma stringAdjacent_connected (m : ℕ) (a b : StringLabel m) :
    Relation.ReflTransGen (stringAdjacent m) a b := by
  have ascending (a b : StringLabel m) (h : a.val ≤ b.val) :
      Relation.ReflTransGen (stringAdjacent m) a b := by
    induction n : b.val-a.val generalizing b with
    | zero =>
      have : a=b := Fin.ext (by omega)
      subst b
      exact .refl
    | succ n ih =>
      let c : StringLabel m := ⟨b.val-1,by have := b.isLt; omega⟩
      have hb : c.val+1=b.val := by dsimp [c]; omega
      exact (ih c (by dsimp [c]; omega) (by dsimp [c]; omega)).tail (Or.inl hb)
  by_cases h : a.val ≤ b.val
  · exact ascending a b h
  · have hp := ascending b a (by omega)
    clear h
    induction hp with
    | refl => exact .refl
    | tail hp hbc ih => exact .head hbc.symm ih

lemma stringAdjacent_weight (m : ℕ) (hm : 2 ≤ m) (a : StringLabel m) :
    ∑ b ∈ GraphConnection.neighbors (stringAdjacent m) a, stringWeight m b =
      (2 * Real.cos (Real.pi/m)) * stringWeight m a := by
  rw [← string_dimension_identity hm]
  simp only [GraphConnection.neighbors,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  dsimp only [stringAdjacent,stringMultiplicity]
  by_cases h₁ : a.val+1=b.val
  · have h₂ : ¬ b.val+1=a.val := by omega
    simp [h₁,h₂]
  · by_cases h₂ : b.val+1=a.val <;> simp [h₁,h₂]

namespace ReversibleQuiver
variable {V B : Type} (Q : ReversibleQuiver V B)
  [Fintype V] [Fintype B] [DecidableEq V] [DecidableEq B]

namespace StringFunctor
open Zigzag.BasedComplex

variable (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (hn : ∀ b, Q.source b ≠ Q.target b) (m : ℕ) (hm : 2 ≤ m)
local notation "N" => stringAdjacent m

include hm

lemma string_connection_exists : ∃ A : ℂ, A ≠ 0 ∧
    A^2+A⁻¹^2+(2 * Real.cos (Real.pi/m) : ℝ)=0 ∧
    (∀ a : StringLabel m, (stringWeight m a : ℂ) ≠ 0) ∧
    ∀ a, (∑ b ∈ GraphConnection.neighbors N a, (stringWeight m b : ℂ)) =
      (2 * Real.cos (Real.pi/m) : ℝ) * (stringWeight m a : ℂ) := by
  obtain ⟨A,hA,hr⟩ := GraphConnection.exists_crossing_parameter
    (2 * Real.cos (Real.pi/m) : ℝ)
  refine ⟨A,hA,hr,?_,?_⟩
  · intro a
    exact_mod_cast ne_of_gt (stringWeight_pos hm a)
  · intro a
    exact_mod_cast stringAdjacent_weight m hm a

end StringFunctor
end ReversibleQuiver
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionRest
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver

attribute [local instance] Classical.propDecidable
variable {E V : Type} [Fintype E] [DecidableEq E] (m:E → ℕ) (e:E)

def fusionVertexSplit : FusionVertex (V:=V) m ≃
    FusionVertex (V:=V) (fun f:FusionRest e => m f) × StringLabel (m e) where
  toFun α := ((α.1,restLabel m e α.2),α.2 e)
  invFun α := (α.1.1,(labelSplit m e).symm (α.1.2,α.2))
  left_inv α := Prod.ext rfl ((labelSplit m e).symm_apply_apply α.2)
  right_inv α := by
    obtain ⟨⟨v,L⟩,a⟩ := α
    have h := (labelSplit m e).apply_symm_apply (L,a)
    change ((v,restLabel m e ((labelSplit m e).symm (L,a))),
      ((labelSplit m e).symm (L,a)) e) = ((v,L),a)
    change (restLabel m e ((labelSplit m e).symm (L,a)),
      ((labelSplit m e).symm (L,a)) e) = (L,a) at h
    exact congrArg (fun z : FusionLabel (fun f:FusionRest e => m f) × StringLabel (m e) =>
      ((v,z.1),z.2)) h

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionFactorStep
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
variable {E V : Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (e:E) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)

include hd in
omit [Fintype E] [Fintype V] [DecidableEq V] in
lemma restEdge_symm : ∀ s t,(d s t).removeFactor e=(d t s).removeFactor e :=
  fun s t => congrArg (FusionEdge.removeFactor e) (hd s t)

local notation "mr" => (fun f:FusionRest e => m f)
local notation "dr" => (fun s t => FusionEdge.removeFactor e (d s t))

noncomputable def fusionFactorStep (a:FusionQuiverArrow mr dr) : Bool :=
  (d a.1.1.1 a.1.2.1).usesFactor e

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionPacketPerm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V : Type} {K:Type*} [Field K]
  [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)

variable (e:E)
local notation "dr" => (fun s t=>FusionEdge.removeFactor e (d s t))

include hd in
omit [Fintype E] [Fintype V] [DecidableEq V] in
lemma restFusion_symmetric : ∀ s t, dr s t=dr t s :=
  fun s t=>congrArg (FusionEdge.removeFactor e) (hd s t)

include hdiag in
omit [Fintype E] [Fintype V] [DecidableEq V] in
lemma restFusion_diagonal : ∀ s, dr s s=.units 0 := by
  intro s
  change FusionEdge.removeFactor e (d s s) = _
  rw [hdiag]
  rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Coxeter_AlternatingLiftProd
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable

lemma alternating_lift_prod {S G : Type*} [Group G] (f : S → G) (i j : S) (n : ℕ) :
    FreeGroup.lift f (alternating i j n)=((altList i j n).map f).prod := by
  induction n generalizing i j with
  | zero => simp [alternating,altList]
  | succ n ih => simp only [alternating,map_mul,FreeGroup.lift_apply_of,altList_succ,
      List.map_cons,List.prod_cons,ih]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_RootNonnegAscent
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open HarmonicArtin.CoxeterExchange

attribute [local instance] Classical.propDecidable Classical.decEq
variable {S W : Type*} [Fintype S] [DecidableEq S] [Group W]
  {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

theorem representation_map_eq_one (w : W) (hw : representation cs w=1) : w=1 := by
  by_contra h
  obtain ⟨s,hs⟩ := exists_right_descent cs h
  have hn := root_nonpos_of_descent cs w s hs s
  rw [hw] at hn
  norm_num at hn

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_RootNonposDescent
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open HarmonicArtin.CoxeterExchange
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W : Type*} [Fintype S] [DecidableEq S] [Group W]
  {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

lemma root_nonpos_iff_descent (w : W) (s : S) :
    (∀ k,representation cs w (Pi.single s 1) k≤0) ↔
      cs.length (w*cs.simple s)+1=cs.length w := by
  constructor
  · intro hn
    rcases cs.length_mul_simple w s with ha | hd
    · have hp := root_nonneg_of_ascent cs w s ha
      exact (geometric_root_ne_zero cs w s (funext (fun k => le_antisymm (hn k) (hp k)))).elim
    · exact hd
  · exact root_nonpos_of_descent cs w s

lemma representation_nonpos_of_columns (z : W)
    (hz : ∀ i k,representation cs z (Pi.single i 1) k≤0)
    (x : S → ℝ) (hx : ∀ i,0 ≤ x i) : ∀ k,representation cs z x k≤0 := by
  intro k
  rw [vector_eq_sum_simple x,map_sum,Finset.sum_apply]
  apply Finset.sum_nonpos
  intro i _
  rw [map_smul]
  exact mul_nonpos_of_nonneg_of_nonpos (hx i) (hz i k)

theorem length_mul_of_all_descents (z : W)
    (hz : ∀ i,cs.length (z*cs.simple i)+1=cs.length z) (w : W) :
    cs.length (z*w)+cs.length w=cs.length z := by
  have hcols : ∀ i k,representation cs z (Pi.single i 1) k≤0 :=
    fun i => root_nonpos_of_descent cs z i (hz i)
  have H : ∀ u : List S,cs.IsReduced u → cs.length (z*cs.wordProd u)+u.length=cs.length z := by
    intro u
    induction u using List.reverseRecOn with
    | nil => simp
    | append_singleton u i ih =>
      intro hr
      have hru : cs.IsReduced u := by simpa only [List.take_left] using hr.take u.length
      have hp := ih hru
      have has : cs.length (cs.wordProd u*cs.simple i)=cs.length (cs.wordProd u)+1 := by
        simpa only [cs.wordProd_append,cs.wordProd_singleton,List.length_append,
          List.length_singleton,hru.eq] using hr.eq
      have hroot := root_nonneg_of_ascent cs (cs.wordProd u) i has
      have hneg : ∀ k,representation cs (z*cs.wordProd u) (Pi.single i 1) k≤0 := by
        rw [map_mul]
        exact representation_nonpos_of_columns cs z hcols _ hroot
      have hstep := (root_nonpos_iff_descent cs (z*cs.wordProd u) i).mp hneg
      simp only [cs.wordProd_append,cs.wordProd_singleton,List.length_append,List.length_singleton]
      rw [← mul_assoc]
      omega
  obtain ⟨u,hu,he⟩ := cs.exists_isReduced w
  simpa only [← hu.eq,← he] using H u hu

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_LongestMulSelf
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open CoxeterExchange

variable {S W:Type*} [Fintype S] [DecidableEq S] [Group W]
  {M:CoxeterMatrix S} (cs:CoxeterSystem M W)

lemma longest_mul_self (z:W) (hz:∀w,cs.length w ≤ cs.length z) : z*z=1 := by
  have h:=length_mul_of_all_descents cs z (all_descents_of_longest cs z hz) z
  exact cs.length_eq_zero_iff.mp (by omega)

lemma longest_conjugates_simple (z:W) (hz:∀w,cs.length w ≤ cs.length z) (s:S) :
    ∃ t:S,z*cs.simple s*z=cs.simple t := by
  apply cs.length_eq_one_iff.mp
  have h:=length_mul_of_all_descents cs z (all_descents_of_longest cs z hz) (cs.simple s*z)
  have h':=all_left_descents_of_longest cs z hz s
  rw [← mul_assoc] at h
  omega

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_ReducedExpression
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe v
variable {S : Type v}
open CoxeterExchange

lemma wordArtin_append (M : CoxeterMatrix S) (u v : List S) :
    wordArtin M (u++v)=wordArtin M u*wordArtin M v := by
  simp only [wordArtin,List.map_append,List.prod_append]

lemma wordArtin_mem_parabolic (M : CoxeterMatrix S) (J : Set S) (u : List S)
    (hu : ∀ i ∈ u, i ∈ J) : wordArtin M u ∈ artinParabolic M J := by
  induction u with
  | nil => exact (artinParabolic M J).one_mem
  | cons i u ih =>
    change generator M i*wordArtin M u ∈ artinParabolic M J
    exact (artinParabolic M J).mul_mem (Subgroup.subset_closure ⟨i,hu i (by simp),rfl⟩)
      (ih (fun k hk => hu k (List.mem_cons_of_mem i hk)))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PositiveLiftSimple
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.positiveToCoxeter_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

lemma positiveLift_simple (s:S) : positiveLift M (M.toCoxeterSystem.simple s)=generator M s := by
  have h:M.toCoxeterSystem.IsReduced [s]:=by
    change M.toCoxeterSystem.length (M.toCoxeterSystem.simple s)=1
    exact M.toCoxeterSystem.length_simple s
  simpa [wordCoxeter,wordArtin] using positiveLift_word M [s] h

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_CosetVertex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe u
variable {S : Type u}

 theorem spherical_empty (M : CoxeterMatrix S) : IsSpherical M ∅ := by
  simp only [IsSpherical, coxeterParabolic, Set.image_empty, Subgroup.closure_empty]
  infer_instance

open _root_.Matrix

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionFold
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix
open scoped _root_.Matrix BigOperators

variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m : E → ℕ)

noncomputable def fusionFold (p : V → ℝ) : V × FusionLabel m → ℝ :=
  fun α => fusionWeight m α.2 * p α.1

noncomputable def fusionUnfoldedCartan (d : V → V → FusionEdge E) :
    Matrix (V × FusionLabel m) (V × FusionLabel m) ℝ :=
  Matrix.diagonal (fun _ => (2 : ℝ)) -
    Matrix.of (fun (α β : V × FusionLabel m) => ((d α.1 β.1).multiplicity m α.2 β.2 : ℝ))

noncomputable def fusionFoldedCartan (d : V → V → FusionEdge E) : Matrix V V ℝ :=
  Matrix.diagonal (fun _ => (2 : ℝ)) - Matrix.of (fun s t => (d s t).dimension m)

lemma fusion_intertwining (hm : ∀ e, 2 ≤ m e) (d : V → V → FusionEdge E) (p : V → ℝ) :
    fusionUnfoldedCartan m d *ᵥ fusionFold m p =
      fusionFold m (fusionFoldedCartan m d *ᵥ p) := by
  funext α
  simp only [fusionUnfoldedCartan, Matrix.sub_mulVec, Matrix.mulVec_diagonal,
    Pi.sub_apply, fusionFold, fusionFoldedCartan]
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.of_apply, fusionFold]
  have hs (s : V) : (∑ L : FusionLabel m,
      ((d α.1 s).multiplicity m α.2 L : ℝ) * (fusionWeight m L * p s)) =
      (d α.1 s).dimension m * fusionWeight m α.2 * p s := by
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, FusionEdge.dimension_identity m hm]
  simp_rw [hs]
  simp only [mul_sub, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro s _
    ring

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_RowReflect
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.labelSplit_apply _root_.OAI.HarmonicArtin.labelSplit_symm_at _root_.OAI.HarmonicArtin.labelSplit_symm_rest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix
open scoped _root_.Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {V:Type*} [Fintype V] [DecidableEq V]

lemma rowReflect_geometric (M:CoxeterMatrix V) (i:V) (x:V → ℝ) :
    rowReflect (Geometric.cartan M) i x=Geometric.simpleReflection M i x :=
  (Geometric.simpleReflection_apply M i x).symm

variable {E:Type*} [Fintype E] [DecidableEq E] (m:E → ℕ)

theorem fusion_reflection_intertwining (hm:∀ e,2 ≤ m e)
    (d:V → V → FusionEdge E) (hdiag:∀ i,d i i=.units 0) (i:V) (p:V → ℝ) :
    rowReflectWord (fusionUnfoldedCartan m d)
      ((Finset.univ:Finset (FusionLabel m)).toList.map (fun L=>(i,L)))
      (fusionFold m p)=fusionFold m (rowReflect (fusionFoldedCartan m d) i p) := by
  let l:=((Finset.univ:Finset (FusionLabel m)).toList.map (fun L=>(i,L)))
  have hn:l.Nodup := List.Nodup.map (fun _ _ h=>Prod.mk.inj h |>.2) (Finset.nodup_toList _)
  have ho : ∀ α∈l,∀ β∈l,α≠β → fusionUnfoldedCartan m d α β=0 := by
    rintro α hα β hβ hne
    obtain ⟨L,_,rfl⟩:=List.mem_map.mp hα
    obtain ⟨L',_,rfl⟩:=List.mem_map.mp hβ
    simp [fusionUnfoldedCartan,hne,hdiag,FusionEdge.multiplicity]
  rw [rowReflectWord_orthogonal _ l hn ho]
  rw [fusion_intertwining m hm]
  have hs : (∑ α∈l.toFinset, fusionFold m (fusionFoldedCartan m d *ᵥ p) α • Pi.single α 1)=
      fusionFold m ((fusionFoldedCartan m d *ᵥ p) i • Pi.single i 1) := by
    have hl : l.toFinset = Finset.univ.image (fun L:FusionLabel m=>(i,L)) := by
      ext α
      simp [l]
    rw [hl,Finset.sum_image (by intro a _ b _ h; exact Prod.mk.inj h |>.2)]
    ext β
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,fusionFold,Pi.single_apply]
    by_cases hb:β.1=i
    · rcases β with ⟨v,L⟩
      dsimp at hb
      subst v
      simp
    · have hx : ∀ L:FusionLabel m,β≠(i,L) := fun L h=>hb (congrArg Prod.fst h)
      simp [hx,hb]
  rw [hs]
  ext α
  simp only [rowReflect,fusionFold,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring

noncomputable def fusionExpandedWord (w:List V) : List (V × FusionLabel m) :=
  w.flatMap (fun i=>(Finset.univ:Finset (FusionLabel m)).toList.map (fun L=>(i,L)))

theorem fusion_word_intertwining (hm:∀ e,2 ≤ m e)
    (d:V → V → FusionEdge E) (hdiag:∀ i,d i i=.units 0) (w:List V) (p:V → ℝ) :
    rowReflectWord (fusionUnfoldedCartan m d) (fusionExpandedWord m w) (fusionFold m p)=
      fusionFold m (rowReflectWord (fusionFoldedCartan m d) w p) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change rowReflectWord (fusionUnfoldedCartan m d)
      (((Finset.univ:Finset (FusionLabel m)).toList.map (fun L=>(i,L))) ++
        fusionExpandedWord m w) (fusionFold m p)=_
    rw [rowReflectWord_append,ih,fusion_reflection_intertwining m hm d hdiag]
    rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_FusionWeightSplit
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.labelSplit_symm_at _root_.OAI.HarmonicArtin.labelSplit_symm_rest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.propDecidable
variable {E:Type} [Fintype E] [DecidableEq E] (m:E → ℕ)

lemma fusionWeight_split (e:E) (L:FusionLabel m) :
    fusionWeight m L = stringWeight (m e) (L e) *
      fusionWeight (fun f:FusionRest e=>m f) (restLabel m e L) :=
  Fintype.prod_eq_mul_prod_subtype_ne (fun f=>stringWeight (m f) (L f)) e

lemma fusionWeight_join (e:E) (r:FusionLabel (fun f:FusionRest e=>m f)) (j:StringLabel (m e)) :
    fusionWeight m ((labelSplit m e).symm (r,j)) =
      stringWeight (m e) j * fusionWeight (fun f:FusionRest e=>m f) r := by
  rw [fusionWeight_split m e]
  have h := (labelSplit m e).apply_symm_apply (r,j)
  change (restLabel m e ((labelSplit m e).symm (r,j)),((labelSplit m e).symm (r,j)) e)=(r,j) at h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp only at h₁ h₂
  rw [h₁,h₂]

lemma fusion_slice_proportional (hm:∀ e,2 ≤ m e) (f:FusionLabel m → ℝ)
    (hf:∀ L,0≤f L)
    (hs:∀ e (r:FusionLabel (fun g:FusionRest e=>m g)), ∃ c:ℝ, ∀ j,
      f ((labelSplit m e).symm (r,j))=c*stringWeight (m e) j) :
    ∃ c:ℝ, 0 ≤ c ∧ ∀ L,f L=c*fusionWeight m L := by
  let L₀ : FusionLabel m := fun e=>⟨0,by have := hm e; omega⟩
  let g (L:FusionLabel m) := f L / fusionWeight m L
  have hg (L:FusionLabel m) (i:E) (j:StringLabel (m i)) : g (Function.update L i j)=g L := by
    let r := restLabel m i L
    obtain ⟨c,hc⟩ := hs i r
    have he (a:StringLabel (m i)) :
        g ((labelSplit m i).symm (r,a)) = c / fusionWeight (fun t:FusionRest i=>m t) r := by
      dsimp [g]
      rw [hc,fusionWeight_join]
      have hw := ne_of_gt (stringWeight_pos (hm i) a)
      have hr := ne_of_gt (fusionWeight_pos (fun t:FusionRest i=>m t) (fun t=>hm t) r)
      field_simp
    have hx : (labelSplit m i).symm (r,L i)=L := (labelSplit m i).symm_apply_apply L
    have hy : (labelSplit m i).symm (r,j)=Function.update L i j := by
      apply (labelSplit m i).injective
      rw [Equiv.apply_symm_apply]
      apply Prod.ext
      · funext t
        exact (Function.update_of_ne t.property _ _).symm
      · change j = Function.update L i j i
        exact (Function.update_self i j L).symm
    exact (congrArg g hy.symm).trans ((he j).trans ((he (L i)).symm.trans (congrArg g hx)))
  refine ⟨g L₀,div_nonneg (hf L₀) (le_of_lt (fusionWeight_pos m hm L₀)),fun L=>?_⟩
  have h := finitePi_update_constant (E:=E) g hg L L₀
  dsimp [g] at h ⊢
  exact (div_eq_iff (ne_of_gt (fusionWeight_pos m hm L))).mp h

lemma fusion_weighted_matrix_proportional (hm:∀ e,2 ≤ m e)
    (B:FusionLabel m → FusionLabel m → ℕ)
    (hB:∀ e (r t:FusionLabel (fun g:FusionRest e=>m g)), ∃ c:ℝ, ∀ j,
      (∑ i, stringWeight (m e) i *
        (B ((labelSplit m e).symm (t,i)) ((labelSplit m e).symm (r,j)):ℝ))=
          c*stringWeight (m e) j) :
    ∃ c:ℝ,0 ≤ c ∧ ∀ L,
      (∑ H,fusionWeight m H*(B H L:ℝ))=c*fusionWeight m L := by
  apply fusion_slice_proportional m hm (fun L=>∑ H,fusionWeight m H*(B H L:ℝ))
  · intro L
    exact Finset.sum_nonneg fun H _=>mul_nonneg (le_of_lt (fusionWeight_pos m hm H)) (Nat.cast_nonneg _)
  · intro e r
    choose c hc using hB e r
    refine ⟨∑ t,fusionWeight (fun g:FusionRest e=>m g) t*c t,fun j=>?_⟩
    rw [← (labelSplit m e).symm.sum_comp]
    rw [Fintype.sum_prod_type]
    simp_rw [fusionWeight_join]
    calc
      _ = ∑ t,fusionWeight (fun g:FusionRest e=>m g) t *
          (∑ i,stringWeight (m e) i * (B ((labelSplit m e).symm (t,i)) ((labelSplit m e).symm (r,j)):ℝ)) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by simp_rw [hc]; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro t _; ring

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionZeroLabel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V:Type} {K:Type*} [Field K]
  [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E→ℕ) (d:V→V→FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hm:∀ e,2 ≤ m e)

def fusionZeroLabel : FusionLabel m := fun e=>⟨0,by have:=hm e;omega⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_ProbeVertex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver
variable {V A:Type*} (Q:ReversibleQuiver V A)
attribute [local instance] Classical.decEq Classical.propDecidable

def probeQuiver : ReversibleQuiver (ProbeVertex V) (ProbeArrow V A) where
  source
    | .inl a => .inl (Q.source a)
    | .inr (v,b,dir) => if dir then .inr (v,b) else .inl v
  target
    | .inl a => .inl (Q.target a)
    | .inr (v,b,dir) => if dir then .inl v else .inr (v,b)
  reverse :=
    { toFun := fun a => match a with
        | .inl a => .inl (Q.reverse a)
        | .inr (v,b,dir) => .inr (v,b,!dir)
      invFun := fun a => match a with
        | .inl a => .inl (Q.reverse a)
        | .inr (v,b,dir) => .inr (v,b,!dir)
      left_inv := by
        rintro (a|⟨v,b,dir⟩)
        · simp only [Q.reverse_reverse]
        · simp
      right_inv := by
        rintro (a|⟨v,b,dir⟩)
        · simp only [Q.reverse_reverse]
        · simp }
  reverse_reverse := by
    rintro (a|⟨v,b,dir⟩)
    · simp only [Equiv.coe_fn_mk,Q.reverse_reverse]
    · simp
  source_reverse := by
    rintro (a|⟨v,b,dir⟩)
    · simp only [Equiv.coe_fn_mk,Q.source_reverse]
    · cases dir <;> rfl
  target_reverse := by
    rintro (a|⟨v,b,dir⟩)
    · simp only [Equiv.coe_fn_mk,Q.target_reverse]
    · cases dir <;> rfl

lemma probeQuiver_no_loops (hn:∀a,Q.source a≠Q.target a) :
    ∀a,(probeQuiver Q).source a≠(probeQuiver Q).target a := by
  rintro (a|⟨v,b,dir⟩)
  · exact fun h=>hn a (Sum.inl.inj h)
  · cases dir <;> simp [probeQuiver]

end HarmonicArtin.ReversibleQuiver

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_CartanRestricted
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open HarmonicArtin.CoxeterExchange
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [DecidableEq S]

lemma coordinateExtension_injective (J : Set S) : Function.Injective (coordinateExtension J) := by
  intro x y h
  funext j
  simpa only [coordinateExtension_apply] using congrFun h (j:S)

theorem restrictionHom_injective (M : CoxeterMatrix S) (J : Set S) :
    Function.Injective (restrictionHom M J) := by
  have hker : ∀ w, restrictionHom M J w=1 → w=1 := by
    intro w hw
    apply representation_map_eq_one (restrictedMatrix M J).toCoxeterSystem w
    apply LinearEquiv.ext
    intro x
    apply coordinateExtension_injective J
    have he := representation_extension M J w x
    rw [hw,map_one] at he
    exact he.symm
  intro a b h
  have hmap : restrictionHom M J (a*b⁻¹)=1 := by simp only [map_mul,map_inv,h,mul_inv_cancel]
  exact mul_inv_eq_one.mp (hker _ hmap)

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_RestrictionLength
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open HarmonicArtin.CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [DecidableEq S]

omit [Fintype S] [DecidableEq S] in
lemma restrictionHom_mem_parabolic (M : CoxeterMatrix S) (J : Set S)
    (w : (restrictedMatrix M J).Group) : restrictionHom M J w ∈ coxeterParabolic M J := by
  induction w using (restrictedMatrix M J).toCoxeterSystem.simple_induction_left with
  | one => simpa only [map_one] using (coxeterParabolic M J).one_mem
  | mul_simple_left w i ih =>
    rw [map_mul,restrictionHom_simple]
    exact (coxeterParabolic M J).mul_mem
      (Subgroup.subset_closure (Set.mem_image_of_mem _ i.property)) ih

theorem restricted_finite (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J) :
    Finite (restrictedMatrix M J).Group := by
  let : Finite (coxeterParabolic M J) := hJ
  exact Finite.of_injective
    (fun w => (⟨restrictionHom M J w,restrictionHom_mem_parabolic M J w⟩ : coxeterParabolic M J))
    (fun a b h => restrictionHom_injective M J (congrArg Subtype.val h))

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_RootRowOrthogonalWord
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open HarmonicArtin.CoxeterExchange
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W : Type*} [Fintype S] [DecidableEq S] [Group W]
  {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

lemma rootRow_orthogonal_word (a : S) (u : List S) (x : S → ℝ)
    (hu : ∀ i∈u,cartan M a i=0) :
    rootRow M a (representation cs (cs.wordProd u) x)=rootRow M a x := by
  induction u with
  | nil => simp
  | cons i u ih =>
    have hao : cartan M a i=0 := hu i (by simp)
    have hu' : ∀ j∈u,cartan M a j=0 := fun j hj => hu j (by simp [hj])
    rw [CoxeterSystem.wordProd_cons,map_mul,LinearEquiv.mul_apply,representation_simple,
      simpleReflection_apply,map_sub,map_smul,rootRow_single,hao,smul_zero,sub_zero,ih hu']

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_InvariantForm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open _root_.Matrix
open scoped _root_.Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W:Type*} [Fintype S] [DecidableEq S] [Group W] [Fintype W]
  {M:CoxeterMatrix S} (cs:CoxeterSystem M W)

noncomputable def invariantForm (x y:S → ℝ) : ℝ :=
  ∑ w:W,representation cs w x ⬝ᵥ representation cs w y

lemma invariantForm_symm (x y:S → ℝ) : invariantForm cs x y=invariantForm cs y x := by
  unfold invariantForm
  apply Finset.sum_congr rfl
  intro w _
  exact dotProduct_comm _ _

lemma invariantForm_sub_right (x y z:S → ℝ) :
    invariantForm cs x (y-z)=invariantForm cs x y-invariantForm cs x z := by
  simp only [invariantForm,map_sub,dotProduct_sub,Finset.sum_sub_distrib]

lemma invariantForm_smul_right (x y:S → ℝ) (r:ℝ) :
    invariantForm cs x (r • y)=r*invariantForm cs x y := by
  simp only [invariantForm,map_smul,dotProduct_smul,smul_eq_mul,Finset.mul_sum]

lemma invariantForm_neg_left (x y:S → ℝ) :
    invariantForm cs (-x) y= -invariantForm cs x y := by
  rw [invariantForm_symm,invariantForm,invariantForm]
  simp only [map_neg,dotProduct_neg,Finset.sum_neg_distrib]
  rw [show (∑ w,representation cs w y ⬝ᵥ representation cs w x)=
    ∑ w,representation cs w x ⬝ᵥ representation cs w y from by
      apply Finset.sum_congr rfl; intro w _; exact dotProduct_comm _ _]

lemma invariantForm_invariant (g:W) (x y:S → ℝ) :
    invariantForm cs (representation cs g x) (representation cs g y)=invariantForm cs x y := by
  unfold invariantForm
  have he (w:W) : representation cs w (representation cs g x) ⬝ᵥ
      representation cs w (representation cs g y)=
      representation cs (w*g) x ⬝ᵥ representation cs (w*g) y := by
    simp only [map_mul,LinearEquiv.mul_apply]
  simp_rw [he]
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun w=>rfl)

lemma invariantForm_pos (x:S → ℝ) (hx:x≠0) : 0 < invariantForm cs x x := by
  apply Finset.sum_pos'
  · intro w _
    exact Finset.sum_nonneg (fun i _=>mul_self_nonneg _)
  · refine ⟨1,Finset.mem_univ _,?_⟩
    simp only [map_one]
    change 0 < x ⬝ᵥ x
    exact lt_of_le_of_ne (Finset.sum_nonneg (fun i _=>mul_self_nonneg _))
      (Ne.symm (fun h=>hx (dotProduct_self_eq_zero.mp h)))

lemma invariantForm_basis_row (i:S) (x:S → ℝ) :
    invariantForm cs (Pi.single i 1) x=
      (invariantForm cs (Pi.single i 1) (Pi.single i 1)/2)*(cartan M *ᵥ x) i := by
  have h:=invariantForm_invariant cs (cs.simple i) (Pi.single i 1) x
  have he : simpleReflection M i (Pi.single i 1)= -(Pi.single i 1) := by
    simp only [simpleReflection_apply]
    have hh : (cartan M *ᵥ Pi.single i 1) i=2 := by simp [Matrix.mulVec_single]
    rw [hh]
    module
  simp only [representation_simple] at h
  rw [he,simpleReflection_apply,
    invariantForm_neg_left,invariantForm_sub_right,invariantForm_smul_right] at h
  linarith

noncomputable def invariantScale (i:S) : ℝ := invariantForm cs (Pi.single i 1) (Pi.single i 1)/2

lemma invariantScale_pos (i:S) : 0 < invariantScale cs i := by
  apply div_pos _ (by norm_num)
  apply invariantForm_pos
  intro h
  have hi:=congrFun h i
  simp at hi

lemma invariantForm_matrix (x y:S → ℝ) :
    invariantForm cs x y=∑ i,∑ j,invariantScale cs i*cartan M i j*x i*y j := by
  have hx : x=∑ i,x i • Pi.single i (1:ℝ) := by
    ext j
    simp [Pi.single_apply]
  rw [invariantForm_symm cs x y]
  conv_lhs => rw [hx]
  simp only [invariantForm,map_sum,map_smul,dotProduct_sum,dotProduct_smul,
    smul_eq_mul]
  rw [Finset.sum_comm]
  have he (i:S) : (∑ w,x i*(representation cs w y ⬝ᵥ representation cs w (Pi.single i 1)))=
      x i*invariantForm cs (Pi.single i 1) y := by
    rw [← Finset.mul_sum,invariantForm_symm]
    rfl
  simp_rw [he]
  apply Finset.sum_congr rfl
  intro i _
  rw [invariantForm_basis_row cs i y]
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,invariantScale]
  apply Finset.sum_congr rfl
  intro j _
  ring

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_CartanOffNonpos
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open _root_.Matrix
open scoped _root_.Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W:Type*} [Fintype S] [DecidableEq S] [Group W] [Fintype W]
  {M:CoxeterMatrix S} (cs:CoxeterSystem M W)

omit [Fintype S] in
lemma cartan_off_nonpos (M:CoxeterMatrix S) (i j:S) (h:i≠j) : cartan M i j ≤ 0 := by
  simpa [cartan,HarmonicArtin.framedCartan] using
    HarmonicArtin.framedCartan_off M (.inl i) (.inl j) (by simpa using h)

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FiniteFusionEdge
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

variable {S : Type*} [LinearOrder S]

def fusionLabelSize (M : CoxeterMatrix S) (e : FiniteFusionEdge M) : ℕ := M e.val.1 e.val.2

lemma fusionLabelSize_ge_four (M : CoxeterMatrix S) (e : FiniteFusionEdge M) :
    4 ≤ fusionLabelSize M e := e.property.2

noncomputable def sortedFusionEdge (M : CoxeterMatrix S) (s t : S)
    (hst : s ≠ t) (hm : 4 ≤ M s t) : FiniteFusionEdge M :=
  if h : s<t then ⟨(s,t), h, hm⟩ else
    ⟨(t,s), lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hst), by simpa only [M.symmetric t s] using hm⟩

lemma sortedFusionEdge_size (M : CoxeterMatrix S) (s t : S)
    (hst : s ≠ t) (hm : 4 ≤ M s t) :
    fusionLabelSize M (sortedFusionEdge M s t hst hm) = M s t := by
  unfold sortedFusionEdge
  split_ifs <;> simp only [fusionLabelSize, M.symmetric t s]

lemma sortedFusionEdge_symm (M : CoxeterMatrix S) (s t : S)
    (hst : s ≠ t) (hm : 4 ≤ M s t) (hmt : 4 ≤ M t s) :
    sortedFusionEdge M s t hst hm = sortedFusionEdge M t s hst.symm hmt := by
  apply Subtype.ext
  unfold sortedFusionEdge
  by_cases h : s < t
  · have ht : ¬t < s := not_lt.mpr (le_of_lt h)
    simp only [dite_eq_left h, dite_eq_right ht]
  · have ht : t < s := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hst)
    simp only [dite_eq_right h, dite_eq_left ht]

noncomputable def coxeterFusionEdge (M : CoxeterMatrix S) :
    (S ⊕ Unit) → (S ⊕ Unit) → FusionEdge (FiniteFusionEdge M)
  | .inl s, .inl t =>
    if hst : s=t then .units 0 else
    if h0 : M s t=0 then .units 2 else
    if h2 : M s t=2 then .units 0 else
    if h3 : M s t=3 then .units 1 else
      .string (sortedFusionEdge M s t hst (by have := M.off_diagonal s t hst; omega))
  | .inl _, .inr _ => .units 1
  | .inr _, .inl _ => .units 1
  | .inr _, .inr _ => .units 0

lemma coxeterFusionEdge_symm (M : CoxeterMatrix S) (s t : S ⊕ Unit) :
    coxeterFusionEdge M s t = coxeterFusionEdge M t s := by
  cases s with
  | inl s =>
    cases t with
    | inl t =>
      by_cases hst : s=t
      · subst t; rfl
      by_cases h0 : M s t=0
      · simp only [coxeterFusionEdge, hst, Ne.symm hst, h0, ← M.symmetric s t, ↓reduceDIte]
      by_cases h2 : M s t=2
      · simp only [coxeterFusionEdge, hst, Ne.symm hst, h2, ← M.symmetric s t, ↓reduceDIte]
      by_cases h3 : M s t=3
      · simp only [coxeterFusionEdge, hst, Ne.symm hst, h3, ← M.symmetric s t, ↓reduceDIte]
      simp only [coxeterFusionEdge, hst, Ne.symm hst, h0, h2, h3, ← M.symmetric s t, ↓reduceDIte]
      congr 1
      exact sortedFusionEdge_symm M s t hst _ _
    | inr t => rfl
  | inr s => cases t <;> rfl

lemma coxeterFusionEdge_diag (M : CoxeterMatrix S) (s : S ⊕ Unit) :
    coxeterFusionEdge M s s = .units 0 := by
  cases s <;> simp [coxeterFusionEdge]

lemma fusionFoldedCartan_eq_framedCartan (M : CoxeterMatrix S) :
    fusionFoldedCartan (fusionLabelSize M) (coxeterFusionEdge M) = framedCartan M := by
  ext s t
  simp only [fusionFoldedCartan, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.of_apply]
  cases s with
  | inl s =>
    cases t with
    | inl t =>
      by_cases hst : s=t
      · subst t; simp [coxeterFusionEdge, framedCartan, FusionEdge.dimension]
      have hSum : (Sum.inl s : S ⊕ Unit) ≠ Sum.inl t := by simpa only [ne_eq, Sum.inl.injEq] using hst
      simp only [ite_eq_right hSum, zero_sub, framedCartan, ite_eq_right hst]
      by_cases h0 : M s t=0
      · simp_all [coxeterFusionEdge, FusionEdge.dimension]
      by_cases h2 : M s t=2
      · simp_all [coxeterFusionEdge, FusionEdge.dimension]
      by_cases h3 : M s t=3
      · simp_all [coxeterFusionEdge, FusionEdge.dimension]
      simp only [coxeterFusionEdge, hst, h0, h2, h3, ↓reduceDIte, ↓reduceIte, FusionEdge.dimension,
        sortedFusionEdge_size]
      ring
    | inr t => simp [coxeterFusionEdge, framedCartan, FusionEdge.dimension]
  | inr s =>
    cases t with
    | inl t => simp [coxeterFusionEdge, framedCartan, FusionEdge.dimension]
    | inr t => cases s; cases t; simp [coxeterFusionEdge, framedCartan, FusionEdge.dimension]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_SphericalFoldedMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix
open scoped _root_.Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] [LinearOrder S]

omit [Fintype S] in
lemma spherical_folded_matrix (M:CoxeterMatrix S) (J:Set S) :
    fusionFoldedCartan (fusionLabelSize M)
      (fun i j:J=>coxeterFusionEdge M (.inl i) (.inl j))=
      (Geometric.cartan M).submatrix ((↑):J → S) ((↑):J → S) := by
  ext i j
  have h:=congrFun (congrFun (fusionFoldedCartan_eq_framedCartan M) (.inl i)) (.inl j)
  simpa [fusionFoldedCartan,Matrix.diagonal_apply,framedCartan,Geometric.cartan,
    Subtype.ext_iff] using h

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_UnfoldedMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.labelSplit_apply _root_.OAI.HarmonicArtin.labelSplit_symm_at _root_.OAI.HarmonicArtin.labelSplit_symm_rest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix Geometric CoxeterExchange
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [LinearOrder S]

noncomputable def unfoldedMatrix (M : CoxeterMatrix S) (J : Set S) :
    CoxeterMatrix (J × FusionLabel (fusionLabelSize M)) where
  M α β := if α=β then 1 else if (coxeterFusionEdge M (.inl α.1) (.inl β.1)).multiplicity
    (fusionLabelSize M) α.2 β.2=0 then 2 else 3
  isSymm := by
    ext α β
    dsimp [Matrix.transpose]
    rw [coxeterFusionEdge_symm M (.inl β.1) (.inl α.1),FusionEdge.multiplicity_symm]
    simp only [eq_comm]
  diagonal α := by simp
  off_diagonal α β h := by simp only [ite_eq_right h]; split_ifs <;> omega

@[simp] lemma unfoldedMatrix_apply (M : CoxeterMatrix S) (J : Set S)
    (α β : J × FusionLabel (fusionLabelSize M)) :
    unfoldedMatrix M J α β=if α=β then 1 else
      if (coxeterFusionEdge M (.inl α.1) (.inl β.1)).multiplicity
        (fusionLabelSize M) α.2 β.2=0 then 2 else 3 := rfl

omit [Fintype S] in
lemma foldedMatrix_cartan (M : CoxeterMatrix S) (J : Set S) :
    fusionFoldedCartan (fusionLabelSize M)
      (fun i j : J => coxeterFusionEdge M (.inl i) (.inl j))=cartan (restrictedMatrix M J) := by
  rw [spherical_folded_matrix,cartan_restricted]

lemma rowReflectWord_representation {V W : Type*} [Fintype V] [DecidableEq V] [Group W]
    {N : CoxeterMatrix V} (cs : CoxeterSystem N W) (u : List V) (p : V → ℝ) :
    rowReflectWord (cartan N) u p=representation cs (cs.wordProd u) p := by
  induction u with
  | nil => simp [rowReflectWord]
  | cons i u ih =>
    change rowReflect (cartan N) i (rowReflectWord (cartan N) u p)=_
    rw [ih,rowReflect_geometric,CoxeterSystem.wordProd_cons,map_mul,
      LinearEquiv.mul_apply,representation_simple]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_UnfoldedHom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open Geometric CoxeterExchange
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable

lemma fusionExpandedWord_append {E V : Type*} [Fintype E] [DecidableEq E] (m : E → ℕ)
    (u v : List V) : fusionExpandedWord m (u++v)=fusionExpandedWord m u++fusionExpandedWord m v := by
  simp only [fusionExpandedWord,List.flatMap_append]

lemma fusionExpandedWord_flatten_replicate {E V : Type*} [Fintype E] [DecidableEq E] (m : E → ℕ)
    (u : List V) (n : ℕ) : fusionExpandedWord m ((List.replicate n u).flatten)=
      (List.replicate n (fusionExpandedWord m u)).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,List.flatten_cons,fusionExpandedWord_append,ih]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_SphericalPair
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
variable {S : Type*} [Fintype S]
lemma spherical_pair (M : CoxeterMatrix S) (i j : S) (hm : 2≤M i j) :
    IsSpherical M ({i,j} : Set S) :=
  CoxeterExchange.finite_parabolic_pair M.toCoxeterSystem i j hm
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_RestrictedArtinHom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} (M:CoxeterMatrix S) (J:Set S)

lemma restrictedArtin_relators : ∀ r∈braidRelators (restrictedMatrix M J),
    FreeGroup.lift (fun s:J=>generator M s) r=1 := by
  have ha:∀ i j:J,∀n,
      FreeGroup.lift (fun s:J=>generator M s) (alternating i j n)=
        wordArtin M (altList (i:S) (j:S) n) := by
    intro i j n
    induction n generalizing i j with
    | zero => simp [alternating,wordArtin,altList]
    | succ n ih => simp only [alternating,map_mul,FreeGroup.lift_apply_of,
        wordArtin,altList_succ,List.map_cons,List.prod_cons,ih]
  rintro r ⟨⟨i,j⟩,rfl⟩
  rw [map_mul,map_inv,ha,ha]
  exact mul_inv_eq_one.mpr (wordArtin_braid M i j)

noncomputable def restrictedArtinHom : Artin (restrictedMatrix M J) →* Artin M :=
  PresentedGroup.toGroup (restrictedArtin_relators M J)

@[simp] lemma restrictedArtinHom_generator (s:J) :
    restrictedArtinHom M J (generator (restrictedMatrix M J) s)=generator M s :=
  PresentedGroup.toGroup.of _

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_CellDeligne
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe v
variable {S : Type v}

lemma wordCoxeter_append (M : CoxeterMatrix S) (u v : List S) :
    wordCoxeter M (u++v)=wordCoxeter M u*wordCoxeter M v := by
  simp only [wordCoxeter,List.map_append,List.prod_append]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PositiveDegreeHom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

universe u
variable {S:Type u} (M:CoxeterMatrix S)

lemma positive_word_surjective (a:PositiveArtin M) : ∃w:List S,wordPositive M w=a := by
  obtain ⟨w,rfl⟩:=PresentedMonoid.surjective_mk a
  exact ⟨FreeMonoid.toList w,by rw [wordPositive_mk,FreeMonoid.ofList_toList]⟩

lemma positiveToCoxeter_length_le (a:PositiveArtin M) :
    M.toCoxeterSystem.length (positiveToCoxeter M a)≤positiveDegree M a := by
  obtain ⟨w,rfl⟩:=positive_word_surjective M a
  rw [positiveToCoxeter_word,positiveDegree_word]
  exact M.toCoxeterSystem.length_wordProd_le w

lemma positive_eq_simpleLift_of_degree [Finite S] (a:PositiveArtin M)
    (h:M.toCoxeterSystem.length (positiveToCoxeter M a)=positiveDegree M a) :
    a=positiveSimpleLift M (positiveToCoxeter M a) := by
  obtain ⟨w,rfl⟩:=positive_word_surjective M a
  rw [positiveToCoxeter_word,positiveDegree_word] at h
  rw [positiveToCoxeter_word]
  exact (positiveSimpleLift_word M w h).symm

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PositiveSimpleLiftMul
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)
local notation "cs" => M.toCoxeterSystem

lemma positive_simple_factors (a b:PositiveArtin M) (w:M.Group)
    (h:a*b=positiveSimpleLift M w) :
    a=positiveSimpleLift M (positiveToCoxeter M a) ∧
      b=positiveSimpleLift M (positiveToCoxeter M b) := by
  have hd:=congrArg (positiveDegree M) h
  simp only [positiveDegree_mul,positiveDegree_simpleLift] at hd
  have hc:=congrArg (positiveToCoxeter M) h
  simp only [map_mul,positiveToCoxeter_simpleLift] at hc
  have ha:=positiveToCoxeter_length_le M a
  have hb:=positiveToCoxeter_length_le M b
  have hab:=M.toCoxeterSystem.length_mul_le (positiveToCoxeter M a) (positiveToCoxeter M b)
  rw [hc] at hab
  exact ⟨positive_eq_simpleLift_of_degree M a (by omega),
    positive_eq_simpleLift_of_degree M b (by omega)⟩

lemma longest_inverse_eq (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z) : z⁻¹=z := by
  have hzz:=longest_mul_self cs z hz
  calc z⁻¹=z⁻¹*(z*z):=by rw [hzz,mul_one]
       _=z:=by group

lemma length_mul_longest (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z) (w:M.Group) :
    M.toCoxeterSystem.length (w*z)+M.toCoxeterSystem.length w=M.toCoxeterSystem.length z := by
  have h:=length_mul_of_all_descents cs z (all_descents_of_longest cs z hz) w⁻¹
  have he:(w*z)⁻¹=z*w⁻¹:=by rw [mul_inv_rev,longest_inverse_eq M z hz]
  rw [←he,M.toCoxeterSystem.length_inv,M.toCoxeterSystem.length_inv] at h
  exact h

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PositiveHead
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

def HasPositiveHead (a:PositiveArtin M) : Prop :=
  ∃h:M.Group,PositivePrefix M (positiveSimpleLift M h) a ∧
    ∀w:M.Group,PositivePrefix M (positiveSimpleLift M w) a→
      PositivePrefix M (positiveSimpleLift M w) (positiveSimpleLift M h)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.StdSimplexCompat
attribute [-instance] _root_.OAI.closedSubmoduleNormedAddCommGroup _root_.OAI.isProbabilityMeasure_map_fst _root_.OAI.isProbabilityMeasure_map_measurableEquiv _root_.OAI.isProbabilityMeasure_map_snd _root_.OAI.isProbabilityMeasure_map_subtype_val _root_.OAI.vonNeumannToStarSubalgebraIsClosed
attribute [-simp] _root_.OAI.fin3_lit_0_1 _root_.OAI.fin3_lit_0_2 _root_.OAI.fin3_lit_1_0 _root_.OAI.fin3_lit_1_2 _root_.OAI.fin3_lit_2_0 _root_.OAI.fin3_lit_2_1 _root_.OAI.fin3_mk_0 _root_.OAI.fin3_mk_1 _root_.OAI.fin3_mk_2 _root_.OAI.fin4_lit_0_1 _root_.OAI.fin4_lit_0_2 _root_.OAI.fin4_lit_0_3 _root_.OAI.fin4_lit_1_0 _root_.OAI.fin4_lit_1_2 _root_.OAI.fin4_lit_1_3 _root_.OAI.fin4_lit_2_0 _root_.OAI.fin4_lit_2_1 _root_.OAI.fin4_lit_2_3 _root_.OAI.fin4_lit_3_0 _root_.OAI.fin4_lit_3_1 _root_.OAI.fin4_lit_3_2 _root_.OAI.fin4_mk_0 _root_.OAI.fin4_mk_1 _root_.OAI.fin4_mk_2 _root_.OAI.fin4_mk_3 _root_.OAI.fin5_lit_0_1 _root_.OAI.fin5_lit_0_2 _root_.OAI.fin5_lit_0_3 _root_.OAI.fin5_lit_0_4 _root_.OAI.fin5_lit_1_0 _root_.OAI.fin5_lit_1_2 _root_.OAI.fin5_lit_1_3 _root_.OAI.fin5_lit_1_4 _root_.OAI.fin5_lit_2_0 _root_.OAI.fin5_lit_2_1 _root_.OAI.fin5_lit_2_3 _root_.OAI.fin5_lit_2_4 _root_.OAI.fin5_lit_3_0 _root_.OAI.fin5_lit_3_1 _root_.OAI.fin5_lit_3_2 _root_.OAI.fin5_lit_3_4 _root_.OAI.fin5_lit_4_0 _root_.OAI.fin5_lit_4_1 _root_.OAI.fin5_lit_4_2 _root_.OAI.fin5_lit_4_3 _root_.OAI.fin5_mk_0 _root_.OAI.fin5_mk_1 _root_.OAI.fin5_mk_2 _root_.OAI.fin5_mk_3 _root_.OAI.fin5_mk_4 _root_.OAI.ofNat_le_infty _root_.OAI.vecCons3_one _root_.OAI.vecCons3_two _root_.OAI.vecCons4_one _root_.OAI.vecCons4_three _root_.OAI.vecCons4_two _root_.OAI.vecConsTail1_1 _root_.OAI.vecConsTail2_1 _root_.OAI.vecConsTail2_2 _root_.OAI.vecConsTail3_1 _root_.OAI.vecConsTail3_2 _root_.OAI.vecConsTail3_3 _root_.OAI.vecConsTail4_1 _root_.OAI.vecConsTail4_2 _root_.OAI.vecConsTail4_3 _root_.OAI.vecConsTail4_4 _root_.YoungDiagram.card_transpose
/-!
# Standard simplex compatibility layer for ports of openai/math

This file is not OpenAI's code. OpenAI's openai/math is built on Mathlib `d13f23b`; prove2.me's
environment is Mathlib `0df444a`. Both have the structure `Convexity.StdSimplex`, but `0df444a`
lacks part of its API (the files `Mathlib.Geometry.Convex.ConvexSpace.{Topology,
CompactSpaceStdSimplex, Barycenter, PathConnectedSpaceStdSimplex}` and some lemmas of `Defs`),
and its `SimplexCategory.toTop` takes the topological simplex to be the subtype
`stdSimplex ℝ (Fin (n+1))`, where `d13f23b` takes the structure.

Part 1 adds the missing `d13f23b` API to `Convexity.StdSimplex` under its `d13f23b` names. It is
copied from Mathlib `d13f23b` (Copyright (c) 2025 Lean FRO, LLC, authors Kim Morrison, Andrew
Yang, Yaël Dillies; Copyright (c) 2026 Joël Riou; released under the Apache 2.0 license), adapted
to `0df444a` (module keywords removed).

Part 2 (`OAI.SStd`) is ours: the subtype `stdSimplex R X` on a finite type with the `d13f23b`
names, for ported code that identifies the simplex with `SimplexCategory.toTop.obj`; there the
port rewrites `Convexity.StdSimplex` to `OAI.SStd`.
-/

noncomputable section StdSimplexCompat

universe u v w

open Topology

/-! ## Part 1: the `d13f23b` API missing from `0df444a`, on `Convexity.StdSimplex` -/

/-! ## Part 2: `OAI.SStd`, the subtype `stdSimplex R X` with the `d13f23b` names -/

namespace OAI

namespace SStd

section Semiring

variable {R : Type*} [Semiring R] [PartialOrder R]
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

@[simp] lemma weights_inj {s t : SStd R X} : s.weights = t.weights ↔ s = t :=
  ⟨ext, fun h => h ▸ rfl⟩

/-- The structure `Convexity.StdSimplex` with the same weights. -/
noncomputable def toStdSimplex (s : SStd R X) : Convexity.StdSimplex R X where
  weights := s.weights
  nonneg := fun x => s.weights_nonneg x
  total := by rw [Finsupp.sum_fintype _ _ (by simp)]; exact s.total_of_fintype

/-- The point of the subtype with the weights of a `Convexity.StdSimplex`. -/
def ofStdSimplex (s : Convexity.StdSimplex R X) : SStd R X :=
  ⟨⇑s.weights, fun x => s.weights_nonneg x, by
    have := s.total
    rwa [Finsupp.sum_fintype _ _ (by simp)] at this⟩

@[simp] lemma weights_toStdSimplex (s : SStd R X) : s.toStdSimplex.weights = s.weights := rfl

@[simp] lemma weights_ofStdSimplex (s : Convexity.StdSimplex R X) :
    (ofStdSimplex s).weights = s.weights := by
  ext x
  rfl

/-- `SStd R X` and `Convexity.StdSimplex R X` are in bijection, weights preserved. -/
noncomputable def equivStdSimplex : SStd R X ≃ Convexity.StdSimplex R X where
  toFun := toStdSimplex
  invFun := ofStdSimplex
  left_inv s := ext (by simp)
  right_inv s := by
    ext : 1
    simp

end Semiring

section OrderedRing

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- Push a simplex point forward along a map of index types (this Mathlib's `stdSimplex.map`). -/
noncomputable def map (g : X → Y) (s : SStd R X) : SStd R Y := stdSimplex.map g s

lemma map_val_apply [DecidableEq Y] (g : X → Y) (s : SStd R X) (y : Y) :
    (map g s).1 y = ∑ x ∈ Finset.univ.filter (fun x => g x = y), s.1 x := by
  change (FunOnFinite.linearMap R R g s.1) y = _
  rw [FunOnFinite.linearMap_apply_apply]

@[simp] lemma weights_map (g : X → Y) (s : SStd R X) :
    (map g s).weights = s.weights.mapDomain g := by
  classical
  ext y
  rw [weights_apply, map_val_apply, Finsupp.mapDomain, Finsupp.sum_fintype _ _ (by simp),
    Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply, Finset.sum_filter, weights_apply]

@[simp] lemma map_id (s : SStd R X) : map id s = s := stdSimplex.map_id_apply s

end OrderedRing

end SStd

end OAI

end StdSimplexCompat
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_RealizeSimplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section TopologyDependencies
open CategoryTheory Opposite Simplicial
open scoped unitInterval

namespace HarmonicArtin
universe u

noncomputable def stdBridge (n : ℕ) : OAI.SStd ℝ (Fin (n+1)) ≃ₜ Convexity.StdSimplex ℝ (Fin (n+1)) :=
  { toEquiv := OAI.SStd.equivStdSimplex
    continuous_toFun := by
      apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).continuous_iff.mpr
      exact continuous_pi fun k => (continuous_apply k).comp continuous_subtype_val
    continuous_invFun := by
      refine Continuous.subtype_mk ?_ _
      refine continuous_pi fun k => ?_
      exact Convexity.StdSimplex.continuous_weights_apply ℝ k }

lemma stdBridge_map {n m : ℕ} (g : Fin (n+1) → Fin (m+1)) (x : OAI.SStd ℝ (Fin (n+1))) :
    stdBridge m (OAI.SStd.map g x) = Convexity.StdSimplex.map g (stdBridge n x) := by
  apply Convexity.StdSimplex.ext
  ext k
  simp [stdBridge, OAI.SStd.equivStdSimplex, OAI.SStd.toStdSimplex,
    OAI.SStd.weights_map, Convexity.StdSimplex.weights_map]

/-- `TopCat.toSSetObjEquiv` with the structure `Convexity.StdSimplex` as the simplex. -/
noncomputable def toSimp (Y : TopCat.{u}) (n : SimplexCategoryᵒᵖ) :
    (TopCat.toSSet.obj Y).obj n ≃ C(Convexity.StdSimplex ℝ (Fin (n.unop.len + 1)), Y) where
  toFun s := (TopCat.toSSetObjEquiv Y n s).comp
    ⟨(stdBridge _).symm, (stdBridge _).symm.continuous⟩
  invFun f := (TopCat.toSSetObjEquiv Y n).symm
    (f.comp ⟨stdBridge _, (stdBridge _).continuous⟩)
  left_inv s := by
    simp only [Equiv.symm_apply_eq]
    ext z
    simp
  right_inv f := by
    ext z
    simp

lemma toSimp_naturality_apply {Y : TopCat.{u}} {n m : SimplexCategory} (f : n ⟶ m)
    (x : (TopCat.toSSet.obj Y).obj (op m)) (z : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    toSimp Y _ ((TopCat.toSSet.obj Y).map f.op x) z =
      toSimp Y _ x (Convexity.StdSimplex.map f.toOrderHom z) := by
  have h := TopCat.toSSetObjEquiv_naturality_apply f x ((stdBridge _).symm z)
  simp only [toSimp, Equiv.coe_fn_mk, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  refine h.trans ?_
  congr 1
  have := stdBridge_map f.toOrderHom ((stdBridge _).symm z)
  rw [Homeomorph.apply_symm_apply] at this
  rw [Homeomorph.eq_symm_apply]
  exact this

lemma toSimp_map {Y Y' : TopCat.{u}} (φ : Y ⟶ Y') (n : SimplexCategoryᵒᵖ)
    (s : (TopCat.toSSet.obj Y).obj n) (z : Convexity.StdSimplex ℝ (Fin (n.unop.len + 1))) :
    toSimp Y' n ((TopCat.toSSet.map φ).app n s) z = φ (toSimp Y n s z) := rfl

noncomputable def realizeSimplex (X : SSet.{u}) {n : SimplexCategory}
    (x : X.obj (op n)) : C(Convexity.StdSimplex ℝ (Fin (n.len + 1)), |X|) :=
  toSimp _ _ ((sSetTopAdj.unit.app X).app (op n) x)

lemma realizeSimplex_natural (X : SSet.{u}) {n m : SimplexCategory}
    (f : n ⟶ m) (x : X.obj (op m)) (z : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    realizeSimplex X (X.map f.op x) z =
      realizeSimplex X x (Convexity.StdSimplex.map f.toOrderHom z) := by
  have h := ConcreteCategory.congr_hom ((sSetTopAdj.unit.app X).naturality f.op) x
  change (sSetTopAdj.unit.app X).app (op n) (X.map f.op x) =
    (TopCat.toSSet.obj |X|).map f.op ((sSetTopAdj.unit.app X).app (op m) x) at h
  unfold realizeSimplex
  rw [h]
  exact toSimp_naturality_apply f _ z

end HarmonicArtin

end TopologyDependencies

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Coxeter_ArtinCoxeter
attribute [-simp] _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} (M : CoxeterMatrix S)

lemma artinCoxeter_relators : ∀ r ∈ braidRelators M,
    FreeGroup.lift M.toCoxeterSystem.simple r = 1 := by
  rintro r ⟨⟨s,t⟩,rfl⟩
  rw [map_mul,map_inv,alternating_lift_prod,alternating_lift_prod]
  exact mul_inv_eq_one.mpr (altList_braid M.toCoxeterSystem s t)

noncomputable def artinCoxeter : Artin M →* M.Group := PresentedGroup.toGroup (artinCoxeter_relators M)

@[simp] lemma artinCoxeter_generator (s : S) :
    artinCoxeter M (generator M s) = M.toCoxeterSystem.simple s := PresentedGroup.toGroup.of _

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_ZigzagLinear
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

variable {V A K : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V]
  [DecidableEq (ProbeVertex V)]
local notation "R" => probeQuiver Q

noncomputable def zigzagLinear : Q.Zigzag K →ₗ[K] (probeQuiver Q).Zigzag K where
  toFun x := (Sum.elim x.vertex (fun _=>0), Sum.elim x.arrow (fun _=>0),
    Sum.elim x.token (fun _=>0))
  map_add' x y := by
    apply Zigzag.ext (Q:=probeQuiver Q) <;> funext z <;> cases z
    all_goals first | rfl | exact (zero_add (0:K)).symm
  map_smul' c x := by
    apply Zigzag.ext (Q:=probeQuiver Q) <;> funext z <;> cases z
    all_goals first | rfl | exact (smul_zero c).symm

@[simp] lemma zigzag_vertex_core (x:Q.Zigzag K) (v:V) :
    (zigzagLinear Q x).vertex (.inl v)=x.vertex v := rfl
@[simp] lemma zigzag_vertex_leaf (x:Q.Zigzag K) (p:V×Bool) :
    (zigzagLinear Q x).vertex (.inr p)=0 := rfl
@[simp] lemma zigzag_arrow_core (x:Q.Zigzag K) (a:A) :
    (zigzagLinear Q x).arrow (.inl a)=x.arrow a := rfl
@[simp] lemma zigzag_arrow_leaf (x:Q.Zigzag K) (p:V×Bool×Bool) :
    (zigzagLinear Q x).arrow (.inr p)=0 := rfl
@[simp] lemma zigzag_token_core (x:Q.Zigzag K) (v:V) :
    (zigzagLinear Q x).token (.inl v)=x.token v := rfl
@[simp] lemma zigzag_token_leaf (x:Q.Zigzag K) (p:V×Bool) :
    (zigzagLinear Q x).token (.inr p)=0 := rfl

lemma zigzagLinear_mul (x y:Q.Zigzag K) :
    zigzagLinear Q (x*y)=zigzagLinear Q x*zigzagLinear Q y := by
  apply Zigzag.ext (Q:=probeQuiver Q)
  · ext z; cases z <;> simp
  · ext z
    rcases z with a|⟨v,b,d⟩
    · rfl
    · cases d
      · change (0:K)= (zigzagLinear Q x).vertex (.inl v)*0+0*(zigzagLinear Q y).vertex (.inr (v,b))
        simp
      · change (0:K)= (zigzagLinear Q x).vertex (.inr (v,b))*0+0*(zigzagLinear Q y).vertex (.inl v)
        simp
  · ext z
    cases z with
    | inl v =>
      rw [zigzag_token_core Q, token_mul (Q:=Q),token_mul (Q:=probeQuiver Q)]
      simp only [Pi.add_apply,Pi.mul_apply,zigzag_vertex_core,zigzag_token_core]
      congr 1
      change Q.backtrack x.arrow y.arrow v =
        (probeQuiver Q).backtrack (Sum.elim x.arrow (fun _=>0)) (Sum.elim y.arrow (fun _=>0)) (.inl v)
      simp [backtrack,probeQuiver,Fintype.sum_sum_type]
    | inr p =>
      rw [zigzag_token_leaf Q,token_mul (Q:=probeQuiver Q)]
      simp only [Pi.add_apply,Pi.mul_apply,zigzag_vertex_leaf,zigzag_token_leaf,MulZeroClass.zero_mul,zero_add]
      change (0:K)=(probeQuiver Q).backtrack (Sum.elim x.arrow (fun _=>0)) (Sum.elim y.arrow (fun _=>0)) (.inr p)
      simp [backtrack,probeQuiver,Fintype.sum_sum_type]

lemma zigzag_vertexId (v:V) : zigzagLinear Q (vertexId Q (K:=K) v)=vertexId R (.inl v) := by
  apply Zigzag.ext (Q:=probeQuiver Q)
  · funext z
    cases z with
    | inl w =>
      rw [zigzag_vertex_core Q, vertexId_eval,vertexId_eval]
      simp
    | inr w => rw [zigzag_vertex_leaf Q,vertexId_eval]; simp
  · funext z; cases z <;> rfl
  · funext z; cases z <;> rfl

lemma zigzag_homogeneous {d:ℤ} {x:Q.Zigzag K} (h:Homogeneous Q d x) :
    Homogeneous R d (zigzagLinear Q x) := by
  refine ⟨?_,?_,?_⟩
  · intro hd; funext z
    cases z with
    | inl z => exact congrFun (h.1 hd) z
    | inr z => rfl
  · intro hd; funext z
    cases z with
    | inl z => exact congrFun (h.2.1 hd) z
    | inr z => rfl
  · intro hd; funext z
    cases z with
    | inl z => exact congrFun (h.2.2 hd) z
    | inr z => rfl

variable {I J L:Type*}
def placement (p:GeneratorPlacement V) : GeneratorPlacement (ProbeVertex V) :=
  ⟨.inl p.color,p.cochain,p.internal⟩

noncomputable def matrix (M:Matrix I J (Q.Zigzag K)) : Matrix I J ((probeQuiver Q).Zigzag K) :=
  M.map (zigzagLinear Q)

@[simp] lemma matrix_apply (M:Matrix I J (Q.Zigzag K)) (i:I) (j:J) :
    matrix Q M i j=zigzagLinear Q (M i j) := rfl
@[simp] lemma matrix_zero : matrix Q (0:Matrix I J (Q.Zigzag K))=0 := by
  apply Matrix.ext; intro i j; exact map_zero (zigzagLinear Q)
@[simp] lemma matrix_add (M N:Matrix I J (Q.Zigzag K)) :
    matrix Q (M+N)=matrix Q M+matrix Q N := by
  apply Matrix.ext; intro i j; exact map_add (zigzagLinear Q) _ _
@[simp] lemma matrix_mul [Fintype J] (M:Matrix I J (Q.Zigzag K)) (N:Matrix J L (Q.Zigzag K)) :
    matrix Q (M*N)=matrix Q M*matrix Q N := by
  apply Matrix.ext
  intro i j
  simp only [matrix_apply,Matrix.mul_apply,map_sum,zigzagLinear_mul]

lemma matrix_entries {p:I → GeneratorPlacement V} {q:J → GeneratorPlacement V}
    {M : Matrix I J (Q.Zigzag K)} (h : ProjectiveEntries Q p q M) :
    ProjectiveEntries (probeQuiver Q) (placement ∘ p) (placement ∘ q) (matrix Q M) := by
  constructor
  · intro i j
    change vertexId (probeQuiver Q) (Sum.inl (p i).color) * zigzagLinear Q (M i j) = _
    rw [← zigzag_vertexId Q,← zigzagLinear_mul Q,h.1]
    rfl
  · intro i j
    change zigzagLinear Q (M i j) * vertexId (probeQuiver Q) (Sum.inl (q j).color) = _
    rw [← zigzag_vertexId Q,← zigzagLinear_mul Q,h.2]
    rfl

lemma matrix_degree {p:I → GeneratorPlacement V} {q:J → GeneratorPlacement V}
    {M : Matrix I J (Q.Zigzag K)} {n v:ℤ} (h : MapDegree Q p q n v M) :
    MapDegree (probeQuiver Q) (placement ∘ p) (placement ∘ q) n v (matrix Q M) := by
  intro i j
  refine ⟨?_,zigzag_homogeneous Q (h i j).2⟩
  intro hn
  change zigzagLinear Q (M i j) = 0
  rw [(h i j).1 hn,map_zero]

@[simp] lemma matrix_identity [DecidableEq I] (p : I → GeneratorPlacement V) :
    matrix Q (projectiveIdentity Q (K := K) p) = projectiveIdentity (probeQuiver Q) (placement ∘ p) := by
  apply Matrix.ext
  intro i j
  by_cases h:i=j
  · subst j
    simp only [matrix,Matrix.map_apply,projectiveIdentity,Matrix.diagonal_apply_eq]
    change zigzagLinear Q (vertexId Q (p i).color) = vertexId (probeQuiver Q) (Sum.inl (p i).color)
    exact zigzag_vertexId Q (K := K) (p i).color
  · simp [matrix,projectiveIdentity,h]

noncomputable def complex [Fintype I] (E : BasedComplex Q (K := K) I) : BasedComplex (probeQuiver Q) (K := K) I where
  placement := placement ∘ E.placement
  differential := matrix Q E.differential
  entries := matrix_entries Q E.entries
  degree := matrix_degree Q E.degree
  square_zero := by rw [← matrix_mul,E.square_zero,matrix_zero]

noncomputable def chainMap [Fintype I] [Fintype J]
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J} (f : Map Q E F) :
    Map (probeQuiver Q) (complex Q E) (complex Q F) where
  matrix := matrix Q f.matrix
  entries := matrix_entries Q f.entries
  degree := matrix_degree Q f.degree
  commute := by
    change matrix Q E.differential * matrix Q f.matrix = matrix Q f.matrix * matrix Q F.differential
    rw [← matrix_mul,← matrix_mul,f.commute]

noncomputable def homotopyEquivalence [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J} (f : HomotopyEquivalence Q E F) :
    HomotopyEquivalence (probeQuiver Q) (complex Q E) (complex Q F) where
  forward := chainMap Q f.forward
  backward := chainMap Q f.backward
  sourceHomotopy := matrix Q f.sourceHomotopy
  targetHomotopy := matrix Q f.targetHomotopy
  sourceEntries := matrix_entries Q f.sourceEntries
  targetEntries := matrix_entries Q f.targetEntries
  sourceDegree := matrix_degree Q f.sourceDegree
  targetDegree := matrix_degree Q f.targetDegree
  sourceEquation := by
    change matrix Q f.forward.matrix * matrix Q f.backward.matrix = _
    rw [← matrix_mul,f.sourceEquation,matrix_add,matrix_add,matrix_mul,matrix_mul,matrix_identity]
    rfl
  targetEquation := by
    change matrix Q f.backward.matrix * matrix Q f.forward.matrix = _
    rw [← matrix_mul,f.targetEquation,matrix_add,matrix_add,matrix_mul,matrix_mul,matrix_identity]
    rfl

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionColorRegion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix
open scoped _root_.Matrix _root_.OAI.Matrix BigOperators

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)

def fusionColorRegion (U:Set V) : Set (FusionVertex (V:=V) m) := {a | a.1∈U}

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_Path2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

variable {V A K:Type*} (Q:ReversibleQuiver V A)
local notation "R" => probeQuiver Q

def path : Path V A → Path (ProbeVertex V) (ProbeArrow V A) :=
  Sum.map Sum.inl (Sum.map Sum.inl Sum.inl)

@[simp] lemma path_source (p:Path V A) : Path.source R (path p)=.inl (Path.source Q p) := by
  rcases p with v|a|v <;> rfl
@[simp] lemma path_target (p:Path V A) : Path.target R (path p)=.inl (Path.target Q p) := by
  rcases p with v|a|v <;> rfl
@[simp] lemma path_length (p:Path V A) : Path.length (path p)=Path.length p := by
  rcases p with v|a|v <;> rfl

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FinsuppMapDomainFiber
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
lemma finsupp_mapDomain_fiber {A B M:Type*} [AddCommMonoid M]
    (f g:A →₀ M) (h:A → B) (b:B) (he:∀ a,h a=b → f a=g a) :
    f.mapDomain h b=g.mapDomain h b := by
  classical
  rw [Finsupp.mapDomain,Finsupp.mapDomain,Finsupp.sum_apply,Finsupp.sum_apply]
  rw [Finsupp.sum_of_support_subset f (Finset.subset_union_left) _ (by simp),
    Finsupp.sum_of_support_subset g (Finset.subset_union_right) _ (by simp)]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha:h a=b
  · rw [Finsupp.single_apply,Finsupp.single_apply,ite_eq_left ha,ite_eq_left ha,he a ha]
  · simp only [Finsupp.single_apply,ha,ite_false, if_false]
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_DimensionNonneg
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix
open scoped _root_.Matrix _root_.OAI.Matrix BigOperators

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)
local notation "C" => fusionFoldedCartan m d

include hd in
omit [Fintype E] [DecidableEq E] [Fintype V] in
lemma fusionFoldedCartan_symm (s t:V) : C s t=C t s := by
  simp only [fusionFoldedCartan,Matrix.sub_apply,Matrix.diagonal_apply,Matrix.of_apply]
  rw [hd s t]
  simp only [eq_comm]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_DimensionPosMultiplicityPos
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix
open scoped _root_.Matrix _root_.OAI.Matrix BigOperators

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)
local notation "C" => fusionFoldedCartan m d

include hm in
omit [Fintype V] in
lemma fusion_arrow_color_cartan_neg (r:FusionQuiverArrow m d)
    (hr:r.1.1.1≠r.1.2.1) : C r.1.1.1 r.1.2.1<0 := by
  simp only [fusionFoldedCartan,Matrix.sub_apply,Matrix.diagonal_apply,Matrix.of_apply,
    ite_eq_right hr,zero_sub,neg_lt_zero]
  exact FusionEdge.dimension_pos_of_multiplicity_pos m hm (d r.1.1.1 r.1.2.1) r.1.1.2 r.1.2.2 (by have:=r.2.isLt; omega)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PacketWord
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix
open scoped _root_.Matrix _root_.OAI.Matrix BigOperators

attribute [local instance] Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

omit [Fintype S] in
lemma fusionLabelSize_ge_two (e:FiniteFusionEdge M) : 2 ≤ fusionLabelSize M e :=
  le_trans (by decide) (fusionLabelSize_ge_four M e)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_ProbeFixedOutside
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

omit [Fintype S] [LinearOrder S] in
lemma sourceParabolic_empty : artinParabolic M ∅=⊥ := by simp [artinParabolic]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Coxeter_ParabolicProductMap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

omit [Fintype S] [LinearOrder S] in
lemma sourceGenerators_commute {s t:S} (h:M s t=2) : Commute (generator M s) (generator M t) := by
  have he:=wordArtin_braid M s t
  change generator M s * generator M t = generator M t * generator M s
  simpa [h,CoxeterExchange.altList,wordArtin] using he

omit [Fintype S] [LinearOrder S] in
lemma sourceParabolics_commute (B C:Set S) (h:∀s∈B,∀t∈C,M s t=2)
    (b c:Artin M) (hb:b∈artinParabolic M B) (hc:c∈artinParabolic M C) : Commute b c := by
  have hh:artinParabolic M B≤Subgroup.centralizer (artinParabolic M C:Set (Artin M)):=by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨s,hs,rfl⟩
    change generator M s∈Subgroup.centralizer (Subgroup.closure ((generator M) '' C):Set (Artin M))
    rw [Subgroup.centralizer_closure]
    rintro _ ⟨t,ht,rfl⟩
    exact (sourceGenerators_commute M (h s hs t ht)).symm.eq
  exact (hh hb c hc).symm

noncomputable def sourceParabolicProductMap (B C:Set S) (hc:∀s∈B,∀t∈C,M s t=2) :
    artinParabolic M B × artinParabolic M C →* Artin M :=
  (artinParabolic M B).subtype.noncommCoprod (artinParabolic M C).subtype
    (fun b c=>sourceParabolics_commute M B C hc b c b.property c.property)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_Harmonic
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

omit [Fintype S] [LinearOrder S] in
lemma rightCoset_self (T:Set S) (x:Artin M) : x∈rightCoset M T x := by
  change x*x⁻¹∈artinParabolic M T
  simp only [mul_inv_cancel]
  exact Subgroup.one_mem _

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_Candidate
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

omit [Fintype S] [LinearOrder S] in
lemma rightCoset_mul_eq (J:Set S) (g z:Artin M) (hg:g∈artinParabolic M J) :
    rightCoset M J (g*z)=rightCoset M J z := by
  ext y
  change y*(g*z)⁻¹∈artinParabolic M J ↔ y*z⁻¹∈artinParabolic M J
  rw [_root_.mul_inv_rev,←mul_assoc]
  exact (artinParabolic M J).mul_mem_cancel_right ((artinParabolic M J).inv_mem hg)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_Coset
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

omit [Fintype S] [LinearOrder S] in
lemma rightCoset_mono {T U:Set S} (h:T⊆U) (x:Artin M) : rightCoset M T x⊆rightCoset M U x :=
  fun _ hy=>artinParabolic_mono M h hy

omit [Fintype S] [LinearOrder S] in
lemma rightCoset_eq_of_mem (T:Set S) (x y:Artin M) (hy:y∈rightCoset M T x) :
    rightCoset M T y=rightCoset M T x := by
  have h:=rightCoset_mul_eq M T (y*x⁻¹) x hy
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using h

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PrismPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped BigOperators unitInterval
open Simplicial

attribute [local instance] Classical.decEq Classical.propDecidable

lemma continuous_prismPrefix {n:ℕ} (k:Fin (n+1)) : Continuous (fun z:Convexity.StdSimplex ℝ (Fin (n+1))=>prismPrefix z k) := by
  unfold prismPrefix
  fun_prop

lemma prismCell_closed {n:ℕ} (k:Fin (n+1)) : IsClosed (PrismCell k) := by
  apply IsClosed.inter
  · exact isClosed_le ((continuous_prismPrefix k).comp continuous_fst) (continuous_subtype_val.comp continuous_snd)
  · exact isClosed_le (continuous_subtype_val.comp continuous_snd)
      (((continuous_prismPrefix k).comp continuous_fst).add ((Convexity.StdSimplex.continuous_weights_apply ℝ k).comp continuous_fst))

lemma prismPrefix_last {n:ℕ} (z:Convexity.StdSimplex ℝ (Fin (n+1))) :
    prismPrefix z (Fin.last n)+z.weights (Fin.last n)=1 := by
  rw [prismPrefix_add]
  have he:(Finset.Iic (Fin.last n):Finset (Fin (n+1)))=Finset.univ:=by
    ext i; simp only [Finset.mem_Iic,Finset.mem_univ,iff_true]; exact Fin.le_last i
  rw [he]; exact z.total_of_fintype

lemma prismCell_cover {n:ℕ} (p:Convexity.StdSimplex ℝ (Fin (n+1)) × I) : ∃k,p∈PrismCell k := by
  let A:Finset (Fin (n+1)):=Finset.univ.filter (fun k=>p.2.val≤ prismPrefix p.1 k+p.1.weights k)
  have hA:A.Nonempty:=by
    refine ⟨Fin.last n,?_⟩
    simp only [A,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [prismPrefix_last]
    exact p.2.property.2
  let k:=A.min' hA
  have hk:k∈A:=Finset.min'_mem A hA
  refine ⟨k,?_,(Finset.mem_filter.mp hk).2⟩
  by_cases hz:k=0
  · rw [hz,prismPrefix_zero]; exact p.2.property.1
  · let j:Fin (n+1):=⟨k.val-1,lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩
    have hj:j<k:=by dsimp [j]; exact Nat.sub_lt (Fin.pos_iff_ne_zero.mpr hz) (by omega)
    have hjn:j∉A:=fun hm=>(not_le_of_gt hj) (Finset.min'_le A j hm)
    have hh:prismPrefix p.1 j+p.1.weights j<p.2.val:=by
      simpa only [A,Finset.mem_filter,Finset.mem_univ,true_and,not_le] using hjn
    have he:prismPrefix p.1 k=prismPrefix p.1 j+p.1.weights j:=by
      rw [prismPrefix_add]
      apply Finset.sum_congr
      · ext i
        simp only [Finset.mem_Iio,Finset.mem_Iic,Fin.lt_def,Fin.le_iff_val_le_val]
        dsimp [j]
        have hp:=Fin.pos_iff_ne_zero.mpr hz
        omega
      · intro _ _; rfl
    rw [he]
    exact hh.le

noncomputable def prismSimplex {n:ℕ} (k:Fin (n+1)) :
    C(Convexity.StdSimplex ℝ (Fin (n+1)) × I,Convexity.StdSimplex ℝ (Fin (n+2))) where
  toFun p := {
    weights := Finsupp.equivFunOnFinite.symm (prismWeights k p)
    nonneg := by
      change ∀ index, 0 ≤ prismWeights k p index
      intro i
      obtain rfl|⟨j,rfl⟩:=Fin.eq_self_or_eq_succAbove k.castSucc i
      · simpa only [prismWeights,Fin.insertNth_apply_same] using prismLeft_nonneg k p
      · simp only [prismWeights,Fin.insertNth_apply_succAbove]
        by_cases hj:j=k
        · subst j
          simp only [Function.update_self]
          exact sub_nonneg.mpr (prismLeft_le k p)
        · rw [Function.update_of_ne hj]
          exact p.1.weights_nonneg j
    total := by
      rw [Finsupp.sum_fintype _ _ (by simp)]
      change (∑ index, prismWeights k p index) = 1
      simp only [prismWeights, Fin.sum_insertNth]
      rw [Finset.sum_update_of_mem (Finset.mem_univ k)]
      have hs:=Finset.sum_sdiff (by simp : ({k}:Finset (Fin (n+1)))⊆Finset.univ) (f:=p.1.weights)
      simp only [Finset.sum_singleton,p.1.total_of_fintype] at hs
      linarith }
  continuous_toFun:=by
    rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).continuous_iff]
    apply continuous_pi
    intro i
    obtain rfl|⟨j,rfl⟩:=Fin.eq_self_or_eq_succAbove k.castSucc i
    · change Continuous (fun p=>prismWeights k p k.castSucc)
      simp only [prismWeights,Fin.insertNth_apply_same]
      unfold prismLeft
      exact ((Convexity.StdSimplex.continuous_weights_apply ℝ k).comp continuous_fst).min (continuous_const.max
        ((continuous_subtype_val.comp continuous_snd).sub ((continuous_prismPrefix k).comp continuous_fst)))
    · change Continuous (fun p=>prismWeights k p (k.castSucc.succAbove j))
      simp only [prismWeights,Fin.insertNth_apply_succAbove]
      by_cases hj:j=k
      · subst j
        simp only [Function.update_self]
        unfold prismLeft
        exact ((Convexity.StdSimplex.continuous_weights_apply ℝ k).comp continuous_fst).sub
          (((Convexity.StdSimplex.continuous_weights_apply ℝ k).comp continuous_fst).min
            (continuous_const.max ((continuous_subtype_val.comp continuous_snd).sub
              ((continuous_prismPrefix k).comp continuous_fst))))
      · simp only [Function.update_of_ne hj]
        exact (Convexity.StdSimplex.continuous_weights_apply ℝ j).comp continuous_fst

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PrismFlag
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped BigOperators unitInterval
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable

lemma prismSimplex_collapse {n:ℕ} (k:Fin (n+1))
    (p:Convexity.StdSimplex ℝ (Fin (n+1))×I) :
    Convexity.StdSimplex.map k.predAbove (prismSimplex k p)=p.1 := by
  apply Convexity.StdSimplex.ext
  apply DFunLike.coe_injective
  rw [simplex_map_weights]
  change FunOnFinite.linearMap ℝ ℝ k.predAbove (k.castSucc.insertNth _ _)=_
  rw [collapse_insertNth]
  ext i
  by_cases hi:i=k
  · subst i; simp only [Pi.add_apply,Pi.single_eq_same,Function.update_self] <;> ring
  · simp only [Pi.add_apply,Pi.single_eq_of_ne hi,Function.update_of_ne hi,zero_add]

lemma prismSimplex_time {n:ℕ} (k:Fin (n+1))
    (p:Convexity.StdSimplex ℝ (Fin (n+1))×I)
    (hp:p∈PrismCell k) :
    (Convexity.StdSimplex.map (prismFlag k) (prismSimplex k p)).weights 0=p.2.val := by
  rw [simplex_map_weights]
  change FunOnFinite.linearMap ℝ ℝ (prismFlag k) (k.castSucc.insertNth _ _) 0=_
  rw [flag_insertNth]
  have he:(∑i∈Finset.Iio k,Function.update p.1.weights k
      (p.1.weights k-prismLeft k p) i)=prismPrefix p.1 k:=by
    apply Finset.sum_congr rfl
    intro i hi
    exact Function.update_of_ne (ne_of_lt (Finset.mem_Iio.mp hi)) _ _
  rw [he,prismLeft_cell k p hp]
  ring

lemma simplex_flag_nonneg_le_one {n:ℕ} (k:Fin (n+1))
    (w:Convexity.StdSimplex ℝ (Fin (n+2))) :
    (Convexity.StdSimplex.map (prismFlag k) w).weights 0∈Set.Icc (0:ℝ) 1 := by
  constructor
  · exact (Convexity.StdSimplex.map (prismFlag k) w).weights_nonneg 0
  · have hs:=(Convexity.StdSimplex.map (prismFlag k) w).total_of_fintype
    rw [Fin.sum_univ_two] at hs
    linarith [(Convexity.StdSimplex.map (prismFlag k) w).weights_nonneg 1]

noncomputable def prismMarginals {n:ℕ} (k:Fin (n+1))
    (w:Convexity.StdSimplex ℝ (Fin (n+2))) :
    Convexity.StdSimplex ℝ (Fin (n+1))×I :=
  (Convexity.StdSimplex.map k.predAbove w,
    ⟨(Convexity.StdSimplex.map (prismFlag k) w).weights 0,simplex_flag_nonneg_le_one k w⟩)

lemma prismMarginals_coordinates {n:ℕ} (k:Fin (n+1))
    (w:Convexity.StdSimplex ℝ (Fin (n+2))) :
    ⇑(prismMarginals k w).1.weights=Pi.single k (w.weights k.castSucc)+
      (fun i=>w.weights (k.castSucc.succAbove i)) ∧
    (prismMarginals k w).2.val=w.weights k.castSucc+
      ∑i∈Finset.Iio k,w.weights (k.castSucc.succAbove i) := by
  have he:=simplex_insertNth_decomp k w
  constructor
  · change ⇑(Convexity.StdSimplex.map k.predAbove w).weights = _
    rw [simplex_map_weights]
    nth_rw 1 [←he]; exact collapse_insertNth _ _ _
  · change (Convexity.StdSimplex.map (prismFlag k) w).weights 0 = _
    rw [simplex_map_weights]
    nth_rw 1 [←he]; exact flag_insertNth _ _ _

lemma prismMarginals_prefix {n:ℕ} (k:Fin (n+1))
    (w:Convexity.StdSimplex ℝ (Fin (n+2))) :
    prismPrefix (prismMarginals k w).1 k=∑i∈Finset.Iio k,w.weights (k.castSucc.succAbove i) := by
  unfold prismPrefix
  rw [(prismMarginals_coordinates k w).1]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Pi.add_apply,Pi.single_eq_of_ne (ne_of_lt (Finset.mem_Iio.mp hi)),zero_add]

lemma prismMarginals_cell {n:ℕ} (k:Fin (n+1))
    (w:Convexity.StdSimplex ℝ (Fin (n+2))) :
    prismMarginals k w∈PrismCell k := by
  have hc:=prismMarginals_coordinates k w
  change prismPrefix (prismMarginals k w).1 k≤(prismMarginals k w).2.val ∧
    (prismMarginals k w).2.val≤prismPrefix (prismMarginals k w).1 k+(prismMarginals k w).1.weights k
  rw [prismMarginals_prefix,hc.1,hc.2]
  simp only [Pi.add_apply,Pi.single_eq_same]
  constructor <;> linarith [w.weights_nonneg k.castSucc,w.weights_nonneg (k.castSucc.succAbove k)]

lemma prismSimplex_marginals {n:ℕ} (k:Fin (n+1))
    (w:Convexity.StdSimplex ℝ (Fin (n+2))) :
    prismSimplex k (prismMarginals k w)=w := by
  have hl:prismLeft k (prismMarginals k w)=w.weights k.castSucc:=by
    rw [prismLeft_cell _ _ (prismMarginals_cell k w),prismMarginals_prefix,
      (prismMarginals_coordinates k w).2]
    ring
  apply Convexity.StdSimplex.ext
  apply DFunLike.coe_injective
  change k.castSucc.insertNth _ _=w.weights
  rw [hl]
  convert simplex_insertNth_decomp k w using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext i
  rw [(prismMarginals_coordinates k w).1]
  by_cases hi:i=k
  · subst i
    simp only [Function.update_self,Pi.add_apply,Pi.single_eq_same] <;> ring
  · simp only [Function.update_of_ne hi,Pi.add_apply,Pi.single_eq_of_ne hi,zero_add]

lemma prismMarginals_simplex {n:ℕ} (k:Fin (n+1))
    (p:Convexity.StdSimplex ℝ (Fin (n+1))×I)
    (hp:p∈PrismCell k) : prismMarginals k (prismSimplex k p)=p := by
  apply Prod.ext
  · exact prismSimplex_collapse k p
  · apply Subtype.ext; exact prismSimplex_time k p hp

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PredAboveSuccSucc
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped BigOperators unitInterval
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable

lemma prismMarginals_face_right {n:ℕ} (k:Fin (n+1)) (z:Convexity.StdSimplex ℝ (Fin (n+1))) :
    (prismMarginals k (Convexity.StdSimplex.map k.succ.succAbove z)).1=z ∧
    (prismMarginals k (Convexity.StdSimplex.map k.succ.succAbove z)).2.val=prismPrefix z k+z.weights k := by
  constructor
  · change Convexity.StdSimplex.map k.predAbove (Convexity.StdSimplex.map k.succ.succAbove z)=z
    rw [← Convexity.StdSimplex.map_comp]
    have he:k.predAbove∘k.succ.succAbove=id:=funext (predAbove_succ_succAbove k)
    rw [he,Convexity.StdSimplex.map_id]
  · change (Convexity.StdSimplex.map (prismFlag k) (Convexity.StdSimplex.map k.succ.succAbove z)).weights 0=_
    rw [← Convexity.StdSimplex.map_comp,prismPrefix_add,simplex_map_weights]
    rw [FunOnFinite.linearMap_apply_apply]
    apply Finset.sum_congr
    · ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iic]
      have he:=congrArg Prod.snd (prismGrid_face_right k i)
      change prismFlag k (k.succ.succAbove i)=(if i≤k then (0:Fin 2) else 1) at he
      simp only [Function.comp_apply,he]
      by_cases hi:i≤k <;> simp [hi]
    · intro _ _; rfl

lemma prismMarginals_face_adjacent {n:ℕ} (k l:Fin (n+1)) (hkl:l.val=k.val+1)
    (z:Convexity.StdSimplex ℝ (Fin (n+1))) :
    prismMarginals l (Convexity.StdSimplex.map k.succ.succAbove z)=
      prismMarginals k (Convexity.StdSimplex.map k.succ.succAbove z) := by
  apply Prod.ext
  · change Convexity.StdSimplex.map l.predAbove (Convexity.StdSimplex.map k.succ.succAbove z)=
      Convexity.StdSimplex.map k.predAbove (Convexity.StdSimplex.map k.succ.succAbove z)
    rw [← Convexity.StdSimplex.map_comp,← Convexity.StdSimplex.map_comp]
    congr 1
    funext i
    exact congrArg Prod.fst (prismGrid_face_adjacent k l hkl i)
  · apply Subtype.ext
    change (Convexity.StdSimplex.map (prismFlag l) (Convexity.StdSimplex.map k.succ.succAbove z)).weights 0=
      (Convexity.StdSimplex.map (prismFlag k) (Convexity.StdSimplex.map k.succ.succAbove z)).weights 0
    rw [← Convexity.StdSimplex.map_comp,← Convexity.StdSimplex.map_comp]
    have he:prismFlag l∘k.succ.succAbove=prismFlag k∘k.succ.succAbove:=by
      funext i
      exact congrArg Prod.snd (prismGrid_face_adjacent k l hkl i)
    rw [he]

lemma prismSimplex_face_right {n:ℕ} (k:Fin (n+1)) (p:Convexity.StdSimplex ℝ (Fin (n+1))×I)
    (hp:p.2.val=prismPrefix p.1 k+p.1.weights k) :
    prismSimplex k p=Convexity.StdSimplex.map k.succ.succAbove p.1 := by
  have hm:prismMarginals k (Convexity.StdSimplex.map k.succ.succAbove p.1)=p:=by
    apply Prod.ext
    · exact (prismMarginals_face_right k p.1).1
    · apply Subtype.ext; exact (prismMarginals_face_right k p.1).2.trans hp.symm
  simpa only [hm] using (prismSimplex_marginals k (Convexity.StdSimplex.map k.succ.succAbove p.1))

lemma prismSimplex_face_adjacent {n:ℕ} (k l:Fin (n+1)) (hkl:l.val=k.val+1)
    (p:Convexity.StdSimplex ℝ (Fin (n+1))×I) (hp:p.2.val=prismPrefix p.1 k+p.1.weights k) :
    prismSimplex l p=Convexity.StdSimplex.map k.succ.succAbove p.1 := by
  have hm:prismMarginals l (Convexity.StdSimplex.map k.succ.succAbove p.1)=p:=by
    rw [prismMarginals_face_adjacent k l hkl]
    apply Prod.ext
    · exact (prismMarginals_face_right k p.1).1
    · apply Subtype.ext; exact (prismMarginals_face_right k p.1).2.trans hp.symm
  simpa only [hm] using (prismSimplex_marginals l (Convexity.StdSimplex.map k.succ.succAbove p.1))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_NervePrismPatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable

lemma prismMarginals_natural {n m:SimplexCategory} (u:n⟶m) (k:Fin (n.len+1))
    (w:Convexity.StdSimplex ℝ (Fin (n.len+2))) :
    prismMarginals (u.toOrderHom k) (Convexity.StdSimplex.map (prismOrdinal u k).toOrderHom w)=
      (Convexity.StdSimplex.map u.toOrderHom (prismMarginals k w).1,(prismMarginals k w).2) := by
  apply Prod.ext
  · change Convexity.StdSimplex.map (u.toOrderHom k).predAbove
      (Convexity.StdSimplex.map (prismOrdinal u k).toOrderHom w)=
      Convexity.StdSimplex.map u.toOrderHom (Convexity.StdSimplex.map k.predAbove w)
    rw [←Convexity.StdSimplex.map_comp,←Convexity.StdSimplex.map_comp]
    congr 1
    funext i
    exact congrArg Prod.fst (prismGrid_natural u k i)
  · apply Subtype.ext
    change (Convexity.StdSimplex.map (prismFlag (u.toOrderHom k))
      (Convexity.StdSimplex.map (prismOrdinal u k).toOrderHom w)).weights 0=
      (Convexity.StdSimplex.map (prismFlag k) w).weights 0
    rw [←Convexity.StdSimplex.map_comp]
    have he:prismFlag (u.toOrderHom k)∘(prismOrdinal u k).toOrderHom=prismFlag k:=by
      funext i
      exact congrArg Prod.snd (prismGrid_natural u k i)
    rw [he]

lemma prismCell_natural {n m:SimplexCategory} (u:n⟶m) (k:Fin (n.len+1))
    (p:Convexity.StdSimplex ℝ (Fin (n.len+1))×I) (hp:p∈PrismCell k) :
    (Convexity.StdSimplex.map u.toOrderHom p.1,p.2)∈PrismCell (u.toOrderHom k) := by
  have hm:=prismMarginals_natural u k (prismSimplex k p)
  rw [prismMarginals_simplex k p hp] at hm
  rw [←hm]
  exact prismMarginals_cell _ _

lemma map_prismSimplex {n m:SimplexCategory} (u:n⟶m) (k:Fin (n.len+1))
    (p:Convexity.StdSimplex ℝ (Fin (n.len+1))×I) (hp:p∈PrismCell k) :
    Convexity.StdSimplex.map (prismOrdinal u k).toOrderHom (prismSimplex k p)=
      prismSimplex (u.toOrderHom k) (Convexity.StdSimplex.map u.toOrderHom p.1,p.2) := by
  have hm:=prismMarginals_natural u k (prismSimplex k p)
  rw [prismMarginals_simplex k p hp] at hm
  rw [←hm]
  exact (prismSimplex_marginals _ _).symm

noncomputable def nervePrismPatch {P Q:Type*} [Preorder P] [Preorder Q]
    (f g:P→o Q) (h:∀p,f p≤g p) {n:SimplexCategory}
    (x:(nerve P).obj (op n)) (k:Fin (n.len+1)) :
    C(Convexity.StdSimplex ℝ (Fin (n.len+1))×I,|nerve Q|) :=
  (realizeSimplex (nerve Q) (nervePrism f g h x k)).comp (prismSimplex k)

lemma nervePrismPatch_natural {P Q:Type*} [Preorder P] [Preorder Q]
    (f g:P→o Q) (h:∀p,f p≤g p) {n m:SimplexCategory} (u:n⟶m)
    (x:(nerve P).obj (op m)) (k:Fin (n.len+1))
    (p:Convexity.StdSimplex ℝ (Fin (n.len+1))×I) (hp:p∈PrismCell k) :
    nervePrismPatch f g h ((nerve P).map u.op x) k p=
      nervePrismPatch f g h x (u.toOrderHom k) (Convexity.StdSimplex.map u.toOrderHom p.1,p.2) := by
  change realizeSimplex _ (nervePrism f g h ((nerve P).map u.op x) k) (prismSimplex k p)=_
  rw [nervePrism_natural,realizeSimplex_natural,map_prismSimplex _ _ _ hp]
  rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_NervePrismValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped BigOperators unitInterval
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable

lemma nervePrismPatch_adjacent {P Q:Type*} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) {n:SimplexCategory} (x:(nerve P).obj (op n))
    (k l:Fin (n.len+1)) (hkl:l.val=k.val+1)
    (p:Convexity.StdSimplex ℝ (Fin (n.len+1))×I) (hk:p∈PrismCell k) (hl:p∈PrismCell l) :
    nervePrismPatch f g h x k p=nervePrismPatch f g h x l p := by
  have hp:p.2.val=prismPrefix p.1 k+p.1.weights k:=by
    have hh:=hl.1
    rw [prismPrefix_step p.1 k l hkl] at hh
    exact le_antisymm hk.2 hh
  change realizeSimplex _ (nervePrism f g h x k) (prismSimplex k p)=
    realizeSimplex _ (nervePrism f g h x l) (prismSimplex l p)
  rw [prismSimplex_face_right k p hp,prismSimplex_face_adjacent k l hkl p hp]
  have h₁:=realizeSimplex_natural (nerve Q) (SimplexCategory.δ k.succ) (nervePrism f g h x k) p.1
  have h₂:=realizeSimplex_natural (nerve Q) (SimplexCategory.δ k.succ) (nervePrism f g h x l) p.1
  rw [nervePrism_face_adjacent f g h x k l hkl] at h₂
  exact h₁.symm.trans h₂

lemma nervePrismPatch_agree {P Q:Type*} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) {n:SimplexCategory} (x:(nerve P).obj (op n))
    (k l:Fin (n.len+1)) (p:Convexity.StdSimplex ℝ (Fin (n.len+1))×I)
    (hk:p∈PrismCell k) (hl:p∈PrismCell l) :
    nervePrismPatch f g h x k p=nervePrismPatch f g h x l p := by
  have aux:∀l:Fin (n.len+1),∀k≤l,p∈PrismCell k→p∈PrismCell l→
      nervePrismPatch f g h x k p=nervePrismPatch f g h x l p:=by
    intro l
    induction l using Fin.induction with
    | zero =>
      intro k hkl _ _
      have he:k=0:=le_antisymm hkl (Fin.zero_le _)
      rw [he]
    | succ j ih =>
      intro k hkl hk hl
      by_cases hh:k≤j.castSucc
      · have hc:p∈PrismCell j.castSucc:=prismCell_between p hk hl hh (by
        simp only [Fin.le_iff_val_le_val,Fin.val_castSucc,Fin.val_succ]; omega)
        exact (ih k hh hk hc).trans (nervePrismPatch_adjacent f g h x j.castSucc j.succ
          (by simp only [Fin.val_succ,Fin.val_castSucc]) p hc hl)
      · have he:k=j.succ:=by
          apply Fin.ext
          simp only [Fin.le_iff_val_le_val,Fin.val_succ,Fin.val_castSucc] at hh hkl ⊢
          omega
        rw [he]
  rcases le_total k l with hkl|hlk
  · exact aux l k hkl hk hl
  · exact (aux k l hlk hl hk).symm

noncomputable def nervePrismValue {P Q:Type*} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) {n:SimplexCategory} (x:(nerve P).obj (op n))
    (p:Convexity.StdSimplex ℝ (Fin (n.len+1))×I) : |nerve Q| :=
  nervePrismPatch f g h x (prismCell_cover p).choose p

lemma nervePrismValue_eq {P Q:Type*} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) {n:SimplexCategory} (x:(nerve P).obj (op n))
    (k:Fin (n.len+1)) (p:Convexity.StdSimplex ℝ (Fin (n.len+1))×I) (hp:p∈PrismCell k) :
    nervePrismValue f g h x p=nervePrismPatch f g h x k p :=
  nervePrismPatch_agree f g h x _ _ p (prismCell_cover p).choose_spec hp

noncomputable def nervePrismSimplex {P Q:Type*} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) {n:SimplexCategory} (x:(nerve P).obj (op n)) :
    C(Convexity.StdSimplex ℝ (Fin (n.len+1)),C(I,|nerve Q|)) :=
  (⟨nervePrismValue f g h x,by
    apply (locallyFinite_of_finite (fun k:Fin (n.len+1)=>PrismCell k)).continuous
    · exact Set.iUnion_eq_univ_iff.mpr prismCell_cover
    · exact prismCell_closed
    · intro k
      apply (nervePrismPatch f g h x k).continuous.continuousOn.congr
      intro p hp
      exact nervePrismValue_eq f g h x k p hp⟩ : C(Convexity.StdSimplex ℝ (Fin (n.len+1))×I,|nerve Q|)).curry

lemma nervePrismSimplex_natural {P Q:Type*} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) {n m:SimplexCategory} (u:n⟶m)
    (x:(nerve P).obj (op m)) (z:Convexity.StdSimplex ℝ (Fin (n.len+1))) (t:I) :
    nervePrismSimplex f g h ((nerve P).map u.op x) z t=
      nervePrismSimplex f g h x (Convexity.StdSimplex.map u.toOrderHom z) t := by
  obtain ⟨k,hk⟩:=prismCell_cover (z,t)
  change nervePrismValue f g h ((nerve P).map u.op x) (z,t)=
    nervePrismValue f g h x (Convexity.StdSimplex.map u.toOrderHom z,t)
  rw [nervePrismValue_eq f g h _ k _ hk,
    nervePrismValue_eq f g h x _ _ (prismCell_natural u k _ hk)]
  exact nervePrismPatch_natural f g h u x k (z,t) hk

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PrismSimplexZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe u
open scoped BigOperators unitInterval
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable

lemma prismSimplex_zero {n:ℕ} (z:Convexity.StdSimplex ℝ (Fin (n+1))) :
    prismSimplex 0 (z,(0:I))=Convexity.StdSimplex.map Fin.succ z := by
  have hm:prismMarginals 0 (Convexity.StdSimplex.map Fin.succ z)=(z,(0:I)):=by
    apply Prod.ext
    · change Convexity.StdSimplex.map (0:Fin (n+1)).predAbove (Convexity.StdSimplex.map Fin.succ z)=z
      rw [← Convexity.StdSimplex.map_comp]
      have he:(0:Fin (n+1)).predAbove∘Fin.succ=id:=by
        funext i; exact Fin.predAbove_succ_of_le _ _ (Fin.zero_le _)
      rw [he,Convexity.StdSimplex.map_id]
    · apply Subtype.ext
      change (Convexity.StdSimplex.map (prismFlag 0) (Convexity.StdSimplex.map Fin.succ z)).weights 0=0
      rw [← Convexity.StdSimplex.map_comp, simplex_map_weights]
      rw [FunOnFinite.linearMap_apply_apply]
      apply Finset.sum_eq_zero
      intro i hi
      have hn:prismFlag (0:Fin (n+1)) i.succ≠0:=by simp [prismFlag]
      exact (hn (Finset.mem_filter.mp hi).2).elim
  simpa only [hm] using prismSimplex_marginals 0 (Convexity.StdSimplex.map Fin.succ z)

lemma prismSimplex_one {n:ℕ} (z:Convexity.StdSimplex ℝ (Fin (n+1))) :
    prismSimplex (Fin.last n) (z,(1:I))=Convexity.StdSimplex.map Fin.castSucc z := by
  have hm:prismMarginals (Fin.last n) (Convexity.StdSimplex.map Fin.castSucc z)=(z,(1:I)):=by
    apply Prod.ext
    · change Convexity.StdSimplex.map (Fin.last n).predAbove (Convexity.StdSimplex.map Fin.castSucc z)=z
      rw [← Convexity.StdSimplex.map_comp]
      have he:(Fin.last n).predAbove∘Fin.castSucc=id:=by
        funext i; exact Fin.predAbove_castSucc_of_le _ _ (Fin.le_last _)
      rw [he,Convexity.StdSimplex.map_id]
    · apply Subtype.ext
      change (Convexity.StdSimplex.map (prismFlag (Fin.last n)) (Convexity.StdSimplex.map Fin.castSucc z)).weights 0=1
      rw [← Convexity.StdSimplex.map_comp, simplex_map_weights]
      rw [FunOnFinite.linearMap_apply_apply]
      have he:Finset.univ.filter (fun i:Fin (n+1)=>(prismFlag (Fin.last n)∘Fin.castSucc) i=0)=Finset.univ:=by
        ext i
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,iff_true,Function.comp_apply]
        simp only [prismFlag,Fin.castSucc_le_castSucc_iff,Fin.le_last,ite_true, if_true]
      rw [he]; exact z.total_of_fintype
  simpa only [hm] using prismSimplex_marginals (Fin.last n) (Convexity.StdSimplex.map Fin.castSucc z)

lemma nervePrismSimplex_zero {P Q:Type u} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) {n:SimplexCategory} (x:(nerve P).obj (op n))
    (z:Convexity.StdSimplex ℝ (Fin (n.len+1))) :
    nervePrismSimplex f g h x z 0=realizeSimplex (nerve Q) ((nerveMap g.toFunctor).app (op n) x) z := by
  have hz:(z,(0:I))∈PrismCell (0:Fin (n.len+1)):=by
    constructor
    · rw [prismPrefix_zero]; rfl
    · rw [prismPrefix_zero,zero_add]; exact z.weights_nonneg 0
  change nervePrismValue f g h x (z,0)=_
  rw [nervePrismValue_eq f g h x 0 _ hz]
  change realizeSimplex _ (nervePrism f g h x 0) (prismSimplex 0 (z,0))=_
  rw [prismSimplex_zero]
  have hh:=realizeSimplex_natural (nerve Q) (SimplexCategory.δ (0:Fin (n.len+2))) (nervePrism f g h x 0) z
  rw [nervePrism_zero_face] at hh
  exact hh.symm

lemma nervePrismSimplex_one {P Q:Type u} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) {n:SimplexCategory} (x:(nerve P).obj (op n))
    (z:Convexity.StdSimplex ℝ (Fin (n.len+1))) :
    nervePrismSimplex f g h x z 1=realizeSimplex (nerve Q) ((nerveMap f.toFunctor).app (op n) x) z := by
  have hz:(z,(1:I))∈PrismCell (Fin.last n.len):=by
    constructor
    · change prismPrefix z (Fin.last n.len)≤1
      have hh:=prismPrefix_last z
      linarith [z.weights_nonneg (Fin.last n.len)]
    · rw [prismPrefix_last]; rfl
  change nervePrismValue f g h x (z,1)=_
  rw [nervePrismValue_eq f g h x (Fin.last n.len) _ hz]
  change realizeSimplex _ (nervePrism f g h x (Fin.last n.len)) (prismSimplex (Fin.last n.len) (z,1))=_
  rw [prismSimplex_one]
  have hh:=realizeSimplex_natural (nerve Q) (SimplexCategory.δ (Fin.last (n.len+1)))
    (nervePrism f g h x (Fin.last n.len)) z
  rw [nervePrism_one_face] at hh
  change _=realizeSimplex _ _ (Convexity.StdSimplex.map (Fin.last (n.len+1)).succAbove z) at hh
  rw [Fin.succAbove_last] at hh
  exact hh.symm

lemma realizeSimplex_map {X Y:SSet} (u:X⟶Y) {n:SimplexCategory} (x:X.obj (op n))
    (z:Convexity.StdSimplex ℝ (Fin (n.len+1))) :
    SSet.toTop.map u (realizeSimplex X x z)=realizeSimplex Y (u.app (op n) x) z := by
  have hh:=ConcreteCategory.congr_hom (NatTrans.congr_app (sSetTopAdj.unit.naturality u) (op n)) x
  have ht:=congrArg (fun q=>toSimp _ _ q z) hh
  exact ht.symm

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ArtinRelabel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Maps of Artin presentations induced by label-preserving maps. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange
variable {S T : Type} (M : CoxeterMatrix S) (N : CoxeterMatrix T)
    (f : S → T) (hf : ∀ i j, N (f i) (f j)=M i j)

include hf in
lemma artinMap_relators : ∀ r ∈ braidRelators M,
    FreeGroup.lift (fun s => generator N (f s)) r=1 := by
  rintro r ⟨⟨i,j⟩,rfl⟩
  rw [map_mul,map_inv,alternating_lift_prod,alternating_lift_prod]
  apply mul_inv_eq_one.mpr
  have h := wordArtin_braid N (f i) (f j)
  rw [hf] at h
  simpa only [wordArtin,←_root_.OAI.HarmonicArtin.CoxeterExchange.altList_map,List.map_map,Function.comp_def] using h

noncomputable def artinMap : Artin M →* Artin N :=
  PresentedGroup.toGroup (artinMap_relators M N f hf)

@[simp] lemma artinMap_generator (s : S) :
    artinMap M N f hf (generator M s)=generator N (f s) := PresentedGroup.toGroup.of _

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_CosetContainment
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Confining paths of parabolic cosets

This is the coset argument in Proposition 6.9 of paper 082-03. A path
whose types stay in one set cannot escape its standard coset. The proof
uses actual subgroup cosets, including upward as well as downward edges.
-/

namespace HarmonicArtin.ParabolicIntersections

variable {S : Type*} (M : CoxeterMatrix S)

/-- A smaller-type coset through a point of a larger-type coset is
contained in that larger coset. -/
theorem rightCoset_subset_of_point {T D : Set S} (hTD : T ⊆ D)
    {w z : Artin M} (hw : w ∈ rightCoset M D z) :
    rightCoset M T w ⊆ rightCoset M D z := by
  intro a ha
  change a * w⁻¹ ∈ artinParabolic M T at ha
  change w * z⁻¹ ∈ artinParabolic M D at hw
  change a * z⁻¹ ∈ artinParabolic M D
  have hh := (artinParabolic M D).mul_mem (standard_mono M hTD ha) hw
  simpa only [mul_assoc, inv_mul_cancel_left] using hh

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ParabolicMinimumStep
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Coxeter coset step used in the standard-parabolic retraction. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W : Type} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

/-- A nonminimal element has a left descent in the parabolic colors. -/
theorem exists_parabolic_left_descent (J : Set S) (w : W)
    (hw : ¬ IsParabolicMinimum cs J w) :
    ∃ t ∈ J, cs.length (cs.simple t*w) < cs.length w := by
  obtain ⟨a,v,ha,hv,he,hlen⟩ := exists_parabolic_decomposition cs J w
  have ha1 : a ≠ 1 := by
    intro ha1
    have hwv : w=v := by simpa only [ha1,one_mul] using he
    exact hw (hwv ▸ hv)
  obtain ⟨l,hl,hr,haeq⟩ := (mem_parabolic_iff_reduced_word cs J a).mp ha
  cases l with
  | nil => exact (ha1 (by simpa only [cs.wordProd_nil] using haeq.symm)).elim
  | cons t l =>
    refine ⟨t,hl t (by simp),?_⟩
    have htail : ∀ i ∈ l, i ∈ J := fun i hi => hl i (List.mem_cons_of_mem t hi)
    have htailp := wordProd_mem_parabolic cs J l htail
    have he' : cs.simple t*w=cs.wordProd l*v := by
      rw [he,←haeq,cs.wordProd_cons,←mul_assoc,cs.simple_mul_simple_cancel_left]
    rw [he',length_mul_of_minimum cs J v hv _ htailp]
    rw [←haeq,hr.eq] at hlen
    have hredtail : cs.IsReduced l := by simpa only [List.drop_succ_cons,List.drop_zero] using hr.drop 1
    rw [hredtail.eq]
    simp only [List.length_cons] at hlen
    omega

/-- Multiplying a minimal left-coset representative by one simple
reflection either remains minimal or crosses a wall of the parabolic. -/
theorem parabolic_minimum_step (J : Set S) (v : W)
    (hv : IsParabolicMinimum cs J v) (s : S) :
    IsParabolicMinimum cs J (v*cs.simple s) ∨
      ∃ t ∈ J, v*cs.simple s=cs.simple t*v := by
  by_cases hmin : IsParabolicMinimum cs J (v*cs.simple s)
  · exact Or.inl hmin
  right
  obtain ⟨t,ht,hdes⟩ := exists_parabolic_left_descent cs J _ hmin
  have htmin := hv (cs.simple t) (simple_mem_parabolic cs J ht)
  have hright := cs.length_mul_simple v s
  have hleft := cs.length_simple_mul (v*cs.simple s) t
  have hascent : cs.length (v*cs.simple s)=cs.length v+1 := by
    rcases hright with hr | hr
    · exact hr
    · have hbound := cs.length_mul_le (cs.simple t*(v*cs.simple s)) (cs.simple s)
      have hs : cs.simple s*cs.simple s=1 := by
        simpa only [mul_one] using cs.simple_mul_simple_cancel_left (w:=1) s
      rw [mul_assoc,mul_assoc,hs,mul_one,cs.length_simple] at hbound
      omega
  obtain ⟨u,hu,he⟩ := cs.exists_isReduced v
  have hured : cs.IsReduced (u++[s]) := by
    change cs.length (cs.wordProd (u++[s]))=(u++[s]).length
    rw [cs.wordProd_append,cs.wordProd_singleton,←he,List.length_append,List.length_singleton,hascent,he,hu.eq]
  obtain ⟨j,hj,hdel⟩ := simple_exchange cs hured t (by
    simpa only [cs.wordProd_append,cs.wordProd_singleton,←he] using hdes)
  by_cases hju : j<u.length
  · rw [List.eraseIdx_append_of_lt_length hju,cs.wordProd_append,
      cs.wordProd_append,cs.wordProd_singleton,←he,←mul_assoc] at hdel
    have hd := mul_right_cancel hdel
    have hb := cs.length_wordProd_le (u.eraseIdx j)
    rw [←hd,List.length_eraseIdx,ite_eq_left hju,←hu.eq,←he] at hb
    have hpos : 0 < cs.length v := by
      rw [he,hu.eq]
      omega
    omega
  · have hjend : j=u.length := by
      simp only [List.length_append,List.length_singleton] at hj
      omega
    rw [hjend,List.eraseIdx_append_of_length_le (by omega),Nat.sub_self,
      List.eraseIdx_zero,List.tail_cons,List.append_nil,←he] at hdel
    have htv : cs.simple t*(v*cs.simple s)=v := by
      simpa only [cs.wordProd_append,cs.wordProd_singleton,←he] using hdel
    refine ⟨t,ht,?_⟩
    calc v*cs.simple s = cs.simple t*(cs.simple t*(v*cs.simple s)) := by
           rw [cs.simple_mul_simple_cancel_left]
         _ = cs.simple t*v := by rw [htv]

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ParabolicCosetProjection
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical minimal coset representatives and their parabolic components. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W : Type} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)
    (J : Set S)

theorem exists_minimum_rep (w : W) :
    ∃ v, IsParabolicMinimum cs J v ∧ ∃ a ∈ parabolic cs J, w=a*v := by
  obtain ⟨a,v,ha,hv,hw,_⟩ := exists_parabolic_decomposition cs J w
  exact ⟨v,hv,a,ha,hw⟩

noncomputable def parabolicRep (w : W) : W :=
  Classical.choose (exists_minimum_rep cs J w)

lemma parabolicRep_min (w : W) : IsParabolicMinimum cs J (parabolicRep cs J w) :=
  (Classical.choose_spec (exists_minimum_rep cs J w)).1

noncomputable def parabolicComponent (w : W) : W := w*(parabolicRep cs J w)⁻¹

lemma parabolicComponent_mul_rep (w : W) :
    parabolicComponent cs J w*parabolicRep cs J w=w := by
  simp only [parabolicComponent,inv_mul_cancel_right]

lemma parabolicComponent_mem (w : W) : parabolicComponent cs J w ∈ parabolic cs J := by
  obtain ⟨a,ha,hw⟩ := (Classical.choose_spec (exists_minimum_rep cs J w)).2
  have he : w*(parabolicRep cs J w)⁻¹=a :=
    (congrArg (fun x => x*(parabolicRep cs J w)⁻¹) hw).trans (mul_inv_cancel_right _ _)
  change w*(parabolicRep cs J w)⁻¹ ∈ parabolic cs J
  exact he.symm ▸ ha

lemma parabolicRep_eq_of_decomposition (w a v : W) (ha : a ∈ parabolic cs J)
    (hv : IsParabolicMinimum cs J v) (hw : w=a*v) : parabolicRep cs J w=v := by
  apply parabolic_minimum_unique cs J hv (parabolicRep_min cs J w)
  refine ⟨(parabolicComponent cs J w)⁻¹*a,
    (parabolic cs J).mul_mem ((parabolic cs J).inv_mem (parabolicComponent_mem cs J w)) ha,?_⟩
  have he := parabolicComponent_mul_rep cs J w
  calc parabolicRep cs J w = (parabolicComponent cs J w)⁻¹*w :=
         (eq_inv_mul_iff_mul_eq).mpr he
       _ = (parabolicComponent cs J w)⁻¹*(a*v) := congrArg _ hw
       _ = _ := by group

noncomputable def parabolicStepRatio (w : W) (s : S) : W :=
  (parabolicComponent cs J w)⁻¹*parabolicComponent cs J (w*cs.simple s)

/-- The component changes by either no letter or a simple letter of `J`. -/
theorem parabolicStepRatio_cases (w : W) (s : S) :
    parabolicStepRatio cs J w s=1 ∨
      ∃ t : J, parabolicStepRatio cs J w s=cs.simple t := by
  rcases parabolic_minimum_step cs J (parabolicRep cs J w) (parabolicRep_min cs J w) s
    with hmin | ⟨t,ht,he⟩
  · left
    have hr : parabolicRep cs J (w*cs.simple s)=parabolicRep cs J w*cs.simple s := by
      apply parabolicRep_eq_of_decomposition cs J _ (parabolicComponent cs J w) _
        (parabolicComponent_mem cs J w) hmin
      rw [←mul_assoc,parabolicComponent_mul_rep]
    unfold parabolicStepRatio parabolicComponent
    rw [hr,mul_inv_rev]
    group
  · right
    have hr : parabolicRep cs J (w*cs.simple s)=parabolicRep cs J w := by
      apply parabolicRep_eq_of_decomposition cs J _
        (parabolicComponent cs J w*cs.simple t) _
        ((parabolic cs J).mul_mem (parabolicComponent_mem cs J w) (simple_mem_parabolic cs J ht))
        (parabolicRep_min cs J w)
      rw [mul_assoc,←he,←mul_assoc,parabolicComponent_mul_rep]
    refine ⟨⟨t,ht⟩,?_⟩
    unfold parabolicStepRatio parabolicComponent
    rw [hr]
    conv_rhs => rw [show cs.simple t=(parabolicRep cs J w*cs.simple s)*
        (parabolicRep cs J w)⁻¹ by rw [he,mul_inv_cancel_right]]
    group

lemma parabolicStepRatio_one_of_minimum (w : W) (s : S)
    (hmin : IsParabolicMinimum cs J (parabolicRep cs J w*cs.simple s)) :
    parabolicStepRatio cs J w s=1 := by
  have hr : parabolicRep cs J (w*cs.simple s)=parabolicRep cs J w*cs.simple s := by
    apply parabolicRep_eq_of_decomposition cs J _ (parabolicComponent cs J w) _
      (parabolicComponent_mem cs J w) hmin
    rw [←mul_assoc,parabolicComponent_mul_rep]
  unfold parabolicStepRatio parabolicComponent
  rw [hr,mul_inv_rev]
  group

lemma parabolicStepRatio_reflection (w : W) (s : S)
    (hne : parabolicStepRatio cs J w s ≠ 1) :
    parabolicStepRatio cs J w s =
      parabolicRep cs J w*cs.simple s*(parabolicRep cs J w)⁻¹ := by
  rcases parabolic_minimum_step cs J (parabolicRep cs J w) (parabolicRep_min cs J w) s
    with hmin | ⟨t,ht,he⟩
  · exact (hne (parabolicStepRatio_one_of_minimum cs J w s hmin)).elim
  have hr : parabolicRep cs J (w*cs.simple s)=parabolicRep cs J w := by
    apply parabolicRep_eq_of_decomposition cs J _ (parabolicComponent cs J w*cs.simple t) _
      ((parabolic cs J).mul_mem (parabolicComponent_mem cs J w) (simple_mem_parabolic cs J ht))
      (parabolicRep_min cs J w)
    rw [mul_assoc,←he,←mul_assoc,parabolicComponent_mul_rep]
  unfold parabolicStepRatio parabolicComponent
  rw [hr]
  group

lemma parabolicStepRatio_reverse (w : W) (s : S) :
    parabolicStepRatio cs J (w*cs.simple s) s=parabolicStepRatio cs J w s := by
  have he : parabolicStepRatio cs J (w*cs.simple s) s=(parabolicStepRatio cs J w s)⁻¹ := by
    simp only [parabolicStepRatio,cs.simple_mul_simple_cancel_right,mul_inv_rev,inv_inv]
  rw [he]
  rcases parabolicStepRatio_cases cs J w s with h | ⟨t,h⟩
  · rw [h,inv_one]
  · rw [h,cs.inv_simple]

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ParabolicRead
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reading the parabolic letters crossed by a Coxeter gallery. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W : Type} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)
    (J : Set S)

noncomputable def parabolicStepLetter (w : W) (s : S) : Option J :=
  parabolicLetter cs J (parabolicStepRatio cs J w s)

lemma parabolicStepLetter_value (w : W) (s : S) :
    parabolicLetterValue cs J (parabolicStepLetter cs J w s)=parabolicStepRatio cs J w s := by
  unfold parabolicStepLetter parabolicLetter
  refine Classical.epsilon_spec (p := fun l : Option J =>
    parabolicLetterValue cs J l=parabolicStepRatio cs J w s) ?_
  rcases parabolicStepRatio_cases cs J w s with h | ⟨t,h⟩
  · exact ⟨none,h.symm⟩
  · exact ⟨some t,h.symm⟩

lemma parabolicStepLetter_reverse (w : W) (s : S) :
    parabolicStepLetter cs J (w*cs.simple s) s=parabolicStepLetter cs J w s := by
  unfold parabolicStepLetter
  rw [parabolicStepRatio_reverse]

lemma parabolicStepLetter_conjugate (w : W) (s : S) (t : J)
    (ht : parabolicStepLetter cs J w s=some t) :
    MulAut.conj (parabolicComponent cs J w) (cs.simple t)=MulAut.conj w (cs.simple s) := by
  have hr := parabolicStepLetter_value cs J w s
  rw [ht] at hr
  change cs.simple t=parabolicStepRatio cs J w s at hr
  have hne : parabolicStepRatio cs J w s ≠ 1 := by
    intro he
    have hl := congrArg cs.length (hr.trans he)
    rw [cs.length_simple,cs.length_one] at hl
    omega
  rw [parabolicStepRatio_reflection cs J w s hne] at hr
  simp only [MulAut.conj_apply]
  rw [hr]
  have hw := parabolicComponent_mul_rep cs J w
  calc _ = (parabolicComponent cs J w*parabolicRep cs J w)*cs.simple s*
      (parabolicComponent cs J w*parabolicRep cs J w)⁻¹ := by group
       _ = _ := by rw [hw]

noncomputable def parabolicRead : W → List S → List J
  | _, [] => []
  | w, s::u => (parabolicStepLetter cs J w s).toList ++ parabolicRead (w*cs.simple s) u

/-- The read word records exactly the change in the parabolic component. -/
theorem parabolicRead_product (w : W) (u : List S) :
    cs.wordProd ((parabolicRead cs J w u).map Subtype.val) =
      (parabolicComponent cs J w)⁻¹*parabolicComponent cs J (w*cs.wordProd u) := by
  induction u generalizing w with
  | nil => simp [parabolicRead]
  | cons s u ih =>
    simp only [parabolicRead,List.map_append,cs.wordProd_append,
      parabolicLetter_word,parabolicStepLetter_value,ih,cs.wordProd_cons]
    unfold parabolicStepRatio
    rw [mul_assoc w]
    group

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ParabolicReadReduced
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A parabolic read of a reduced gallery is reduced. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W : Type} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

/-- The converse to the usual no-repeated-inversion property. -/
theorem reduced_of_nodup_inversions (u : List S) (hu : (cs.leftInvSeq u).Nodup) :
    cs.IsReduced u := by
  induction u with
  | nil => simp [CoxeterSystem.IsReduced]
  | cons s u ih =>
    change (cs.simple s :: (cs.leftInvSeq u).map (MulAut.conj (cs.simple s))).Nodup at hu
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hu
    have hr := ih htail.of_map
    rcases cs.length_simple_mul (cs.wordProd u) s with ha | hd
    · change cs.length (cs.simple s*cs.wordProd u)=(s::u).length
      rw [ha,hr.eq,List.length_cons]
    · have hm := simple_mem_leftInvSeq_of_shorter cs hr s (by omega)
      apply (hnot ?_).elim
      exact List.mem_map.mpr ⟨cs.simple s,hm,by simp only [MulAut.conj_apply,mul_inv_cancel_right]⟩

/-- The read gallery crosses a subsequence of the original reflecting
walls; conjugating by the initial component identifies their labels. -/
theorem parabolicRead_inversions (J : Set S) (w : W) (u : List S) :
    ((cs.leftInvSeq ((parabolicRead cs J w u).map Subtype.val)).map
      (MulAut.conj (parabolicComponent cs J w))).Sublist
      ((cs.leftInvSeq u).map (MulAut.conj w)) := by
  induction u generalizing w with
  | nil => simp [parabolicRead]
  | cons s u ih =>
    have hi := ih (w*cs.simple s)
    cases hl : parabolicStepLetter cs J w s with
    | none =>
      have hv := parabolicStepLetter_value cs J w s
      rw [hl] at hv
      change 1=(parabolicComponent cs J w)⁻¹*parabolicComponent cs J (w*cs.simple s) at hv
      have hc : parabolicComponent cs J (w*cs.simple s)=parabolicComponent cs J w :=
        (inv_mul_eq_one.mp hv.symm).symm
      rw [hc] at hi
      simpa only [parabolicRead,hl,Option.toList_none,List.nil_append,
        CoxeterSystem.leftInvSeq,List.map_cons,conjugate_sequence] using
        List.Sublist.cons (MulAut.conj w (cs.simple s)) hi
    | some t =>
      have hv := parabolicStepLetter_value cs J w s
      rw [hl] at hv
      change cs.simple t=(parabolicComponent cs J w)⁻¹*parabolicComponent cs J (w*cs.simple s) at hv
      have hc : parabolicComponent cs J (w*cs.simple s)=parabolicComponent cs J w*cs.simple t :=
        ((eq_inv_mul_iff_mul_eq).mp hv).symm
      rw [hc] at hi
      have href := parabolicStepLetter_conjugate cs J w s t hl
      simpa only [parabolicRead,hl,Option.toList_some,List.singleton_append,List.map_cons,
        CoxeterSystem.leftInvSeq,conjugate_sequence,href] using
        List.Sublist.cons_cons (MulAut.conj w (cs.simple s)) hi

/-- Retraction to a standard parabolic preserves reducedness of galleries,
allowing letters which do not cross a parabolic wall to disappear. -/
theorem parabolicRead_reduced (J : Set S) (w : W) (u : List S) (hu : cs.IsReduced u) :
    cs.IsReduced ((parabolicRead cs J w u).map Subtype.val) := by
  apply reduced_of_nodup_inversions cs
  have h := (parabolicRead_inversions cs J w u).nodup
    (hu.nodup_leftInvSeq.map (MulAut.conj w).injective)
  exact h.of_map

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ParabolicReadBraid
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The parabolic read respects braid relations by the reduced-word theorem. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S) (J : Set S)
local notation "cs" => M.toCoxeterSystem
local notation "R" => restrictedMatrix M J

/-- Equal reduced galleries have equal positive reads in the parabolic. -/
theorem parabolicRead_word_eq (w : M.Group) (u v : List S)
    (hu : (cs).IsReduced u) (hv : (cs).IsReduced v) (he : (cs).wordProd u=(cs).wordProd v) :
    wordArtin R (parabolicRead cs J w u)=wordArtin R (parabolicRead cs J w v) := by
  suffices h : wordPositive R (parabolicRead cs J w u)=wordPositive R (parabolicRead cs J w v) by
    simpa only [positiveToArtin_word] using congrArg (positiveToArtin R) h
  apply wordPositive_eq_of_reduced R _ _
      ((restriction_reduced_iff M J _).mp (parabolicRead_reduced cs J w u hu))
      ((restriction_reduced_iff M J _).mp (parabolicRead_reduced cs J w v hv))
  apply restrictionHom_injective M J
  change restrictionHom M J ((restrictedMatrix M J).toCoxeterSystem.wordProd (parabolicRead cs J w u)) =
    restrictionHom M J ((restrictedMatrix M J).toCoxeterSystem.wordProd (parabolicRead cs J w v))
  rw [restriction_wordProd,restriction_wordProd,parabolicRead_product,parabolicRead_product,he]

/-- The precise braid compatibility needed for the parabolic retraction. -/
theorem parabolicRead_braid (w : M.Group) (i j : S) :
    wordArtin R (parabolicRead cs J w (altList i j (M i j))) =
      wordArtin R (parabolicRead cs J w (altList j i (M i j))) := by
  by_cases hij : i=j
  · subst j; rfl
  apply parabolicRead_word_eq M J w
  · exact altList_reduced cs i j hij _ (Or.inr le_rfl)
  · exact altList_reduced cs j i (Ne.symm hij) _ (Or.inr (le_of_eq (M.symmetric i j)))
  · exact altList_braid cs i j

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ParabolicRetractionAction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.artinCoxeter_generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The parabolic gallery retraction as an action of the Artin presentation. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S) (J : Set S)
local notation "cs" => M.toCoxeterSystem
local notation "R" => restrictedMatrix M J
local notation "State" => M.Group × Artin R

noncomputable def parabolicStepArtin (w : M.Group) (s : S) : Artin R :=
  wordArtin R (parabolicStepLetter cs J w s).toList

omit [Fintype S] in
lemma parabolicStepArtin_reverse (w : M.Group) (s : S) :
    parabolicStepArtin M J (w*(cs).simple s) s=parabolicStepArtin M J w s := by
  unfold parabolicStepArtin
  rw [parabolicStepLetter_reverse]

noncomputable def parabolicStepPerm (s : S) : Equiv.Perm State where
  toFun x := (x.1*(cs).simple s,x.2*parabolicStepArtin M J x.1 s)
  invFun x := (x.1*(cs).simple s,x.2*(parabolicStepArtin M J x.1 s)⁻¹)
  left_inv := by
    rintro ⟨w,a⟩
    apply Prod.ext
    · exact (cs).simple_mul_simple_cancel_right s
    · change (a*parabolicStepArtin M J w s)*(parabolicStepArtin M J (w*(cs).simple s) s)⁻¹=a
      rw [parabolicStepArtin_reverse,mul_inv_cancel_right]
  right_inv := by
    rintro ⟨w,a⟩
    apply Prod.ext
    · exact (cs).simple_mul_simple_cancel_right s
    · change (a*(parabolicStepArtin M J w s)⁻¹)*parabolicStepArtin M J (w*(cs).simple s) s=a
      rw [parabolicStepArtin_reverse,inv_mul_cancel_right]

noncomputable def parabolicWordPerm (u : List S) : (Equiv.Perm State)ᵐᵒᵖ :=
  (u.map fun s => MulOpposite.op (parabolicStepPerm M J s)).prod

omit [Fintype S] in
/-- Using the opposite permutation group makes the word act in its written order. -/
lemma parabolicWordPerm_apply (u : List S) (w : M.Group) (a : Artin R) :
    MulOpposite.unop (parabolicWordPerm M J u) (w,a) =
      (w*(cs).wordProd u,a*wordArtin R (parabolicRead cs J w u)) := by
  induction u generalizing w a with
  | nil => simp [parabolicWordPerm,parabolicRead,wordArtin]
  | cons s u ih =>
    change MulOpposite.unop (parabolicWordPerm M J u)
      (w*(cs).simple s,a*parabolicStepArtin M J w s)=_
    rw [ih]
    simp only [(cs).wordProd_cons,parabolicRead,wordArtin_append,parabolicStepArtin,mul_assoc]

lemma parabolicWordPerm_braid (i j : S) :
    parabolicWordPerm M J (altList i j (M i j))=
      parabolicWordPerm M J (altList j i (M i j)) := by
  apply MulOpposite.unop_injective
  apply Equiv.ext
  rintro ⟨w,a⟩
  rw [parabolicWordPerm_apply,parabolicWordPerm_apply,altList_braid cs i j,
    parabolicRead_braid M J w i j]

lemma parabolicPerm_relators : ∀ r ∈ braidRelators M,
    FreeGroup.lift (fun s => MulOpposite.op (parabolicStepPerm M J s)) r=1 := by
  rintro r ⟨⟨i,j⟩,rfl⟩
  rw [map_mul,map_inv]
  apply mul_inv_eq_one.mpr
  rw [alternating_lift_prod,alternating_lift_prod]
  exact parabolicWordPerm_braid M J i j

noncomputable def parabolicRetractionAction : Artin M →* (Equiv.Perm State)ᵐᵒᵖ :=
  PresentedGroup.toGroup (parabolicPerm_relators M J)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_GeneratorPowers
attribute [-simp] _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Infinite cyclic generator subgroups and their intersections with standard
parabolics. The retraction argument supplies infinite branching in visual trees. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} (M : CoxeterMatrix S)

lemma exponent_relators : ∀ r∈braidRelators M,
    FreeGroup.lift (fun _ : S => Multiplicative.ofAdd (1 : ℤ)) r=1 := by
  rintro r ⟨⟨s,t⟩,rfl⟩
  rw [map_mul,map_inv,exponent_alternating,exponent_alternating,mul_inv_cancel]

/-- The total exponent homomorphism for the Artin presentation. -/
def artinExponent : Artin M →* Multiplicative ℤ :=
  PresentedGroup.toGroup (exponent_relators M)

@[simp] lemma artinExponent_generator (s : S) :
    artinExponent M (generator M s)=Multiplicative.ofAdd (1 : ℤ) :=
  PresentedGroup.toGroup.of _

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_GraphRealizationDistance
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The path distance on unit intervals attached to graph edges. -/
namespace HarmonicArtin.ParabolicIntersections.GraphRealization
open TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} (H : SimpleGraph V)

lemma distance_cases (p q : Point H) :
    (∃ e t s,p=.edge e t ∧ q=.edge e s ∧ distance H p q=|(t : ℝ)-s|) ∨
      ∃ i j,distance H p q=route H p q i j := by
  cases p with
  | vertex x => exact Or.inr (via_eq_route H _ _)
  | edge e t =>
    cases q with
    | vertex y => exact Or.inr (via_eq_route H _ _)
    | edge f s =>
      by_cases he : e=f
      · subst f
        rcases min_choice |(t : ℝ)-s| (via H (.edge e t) (.edge e s)) with h|h
        · exact Or.inl ⟨e,t,s,rfl,rfl,by simpa [distance] using h⟩
        · obtain ⟨i,j,hv⟩ := via_eq_route H (.edge e t) (.edge e s)
          exact Or.inr ⟨i,j,by simpa [distance] using h.trans hv⟩
      · simpa only [distance,ite_eq_right he] using Or.inr (via_eq_route H (.edge e t) (.edge f s))

lemma distance_nonneg (p q : Point H) : 0 ≤ distance H p q := by
  rcases distance_cases H p q with ⟨e,t,s,rfl,rfl,hd⟩|⟨i,j,hd⟩
  · rw [hd]; exact abs_nonneg _
  · rw [hd]; exact route_nonneg H p q i j

lemma distance_comm (p q : Point H) : distance H p q=distance H q p := by
  have h (p q : Point H) : distance H p q ≤ distance H q p := by
    rcases distance_cases H q p with ⟨e,t,s,rfl,rfl,hd⟩|⟨i,j,hd⟩
    · rw [hd,abs_sub_comm]
      exact distance_le_direct H e s t
    · rw [hd,route_comm]
      exact distance_le_route H p q j i
  exact le_antisymm (h p q) (h q p)

lemma distance_self (p : Point H) : distance H p p=0 := by
  apply le_antisymm _ (distance_nonneg H p p)
  cases p with
  | vertex v => simpa [route,anchor,weight] using distance_le_route H (.vertex v) (.vertex v) false false
  | edge e t => simpa using distance_le_direct H e t t

theorem distance_triangle (hH : H.Connected) (p q r : Point H) :
    distance H p r ≤ distance H p q+distance H q r := by
  rcases distance_cases H p q with ⟨e,t,s,hp,hq,hd⟩|⟨i,j,hd⟩
  · subst p; subst q
    rcases distance_cases H (.edge e s) r with ⟨f,a,b,he,hr,hd'⟩|⟨i,j,hd'⟩
    · cases he
      subst r
      have ht := abs_sub_le (t : ℝ) s b
      exact (distance_le_direct H e t b).trans (by rw [hd,hd']; exact ht)
    · have hle := distance_le_route H (.edge e t) r i j
      have hw := edge_weight_le H e t s i
      rw [hd,hd']
      refine hle.trans ?_
      unfold route
      have ha : anchor H (.edge e t) i=anchor H (.edge e s) i := by cases i <;> rfl
      rw [ha]
      linarith
  · rcases distance_cases H q r with ⟨e,t,s,hq,hr,hd'⟩|⟨k,l,hd'⟩
    · subst q; subst r
      have hle := distance_le_route H p (.edge e s) i j
      have hw := edge_weight_le H e s t j
      rw [hd,hd']
      refine hle.trans ?_
      unfold route
      have ha : anchor H (.edge e s) j=anchor H (.edge e t) j := by cases j <;> rfl
      rw [ha]
      rw [abs_sub_comm (s : ℝ) t] at hw
      linarith
    · rw [hd,hd']
      exact (distance_le_route H p r i l).trans (route_triangle H hH p q r i j k l)

@[instance_reducible]
noncomputable def premetric (hH : H.Connected) : PseudoMetricSpace (Point H) where
  dist := distance H
  dist_self := distance_self H
  dist_comm := distance_comm H
  dist_triangle := distance_triangle H hH

end HarmonicArtin.ParabolicIntersections.GraphRealization

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_GraphRealizationSpace
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The metric realization of a connected graph by unit intervals. -/
namespace HarmonicArtin.ParabolicIntersections.GraphRealization
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} (H : SimpleGraph V)

def Space (hH : H.Connected) :=
  @SeparationQuotient (Point H) (premetric H hH).toUniformSpace.toTopologicalSpace

noncomputable instance spaceMetric (hH : H.Connected) : MetricSpace (Space H hH) :=
  @SeparationQuotient.instMetricSpace (Point H) (premetric H hH)

noncomputable def embed (hH : H.Connected) : Point H → Space H hH :=
  @SeparationQuotient.mk (Point H) (premetric H hH).toUniformSpace.toTopologicalSpace

lemma embed_surjective (hH : H.Connected) : Function.Surjective (embed H hH) :=
  @SeparationQuotient.surjective_mk (Point H) (premetric H hH).toUniformSpace.toTopologicalSpace

noncomputable def vertex (hH : H.Connected) (v : V) : Space H hH := embed H hH (.vertex v)

noncomputable def arc (hH : H.Connected) (e : H.Dart) (t : Set.Icc (0 : ℝ) 1) : Space H hH :=
  embed H hH (.edge e t)

end HarmonicArtin.ParabolicIntersections.GraphRealization

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_GraphRealizationAction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An action on a graph extends isometrically to its unit-interval realization. -/
namespace HarmonicArtin.ParabolicIntersections.GraphRealization
open TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (H : SimpleGraph V) (hA : PreservesAdj (G := G) H)

def actPoint (g : G) : Point H → Point H
  | .vertex v => .vertex (g • v)
  | .edge e t => .edge (actDart H hA g e) t

lemma actPoint_one (p : Point H) : actPoint H hA 1 p=p := by
  cases p with
  | vertex v => simp [actPoint]
  | edge e t =>
    change Point.edge (actDart H hA 1 e) t=Point.edge e t
    apply congrArg (fun d : H.Dart => Point.edge d t)
    apply SimpleGraph.Dart.ext
    simp [actDart,one_smul]

lemma actPoint_mul (g h : G) (p : Point H) :
    actPoint H hA (g*h) p=actPoint H hA g (actPoint H hA h p) := by
  cases p with
  | vertex v => simp [actPoint,mul_smul]
  | edge e t =>
    change Point.edge (actDart H hA (g*h) e) t=
      Point.edge (actDart H hA g (actDart H hA h e)) t
    apply congrArg (fun d : H.Dart => Point.edge d t)
    apply SimpleGraph.Dart.ext
    simp [actDart,mul_smul]

lemma anchor_act (g : G) (p : Point H) (i : Bool) :
    anchor H (actPoint H hA g p) i=g • anchor H p i := by
  cases p <;> cases i <;> rfl

lemma weight_act (g : G) (p : Point H) (i : Bool) :
    weight H (actPoint H hA g p) i=weight H p i := by
  cases p <;> cases i <;> rfl

lemma route_act (hH : H.Connected) (g : G) (p q : Point H) (i j : Bool) :
    route H (actPoint H hA g p) (actPoint H hA g q) i j=route H p q i j := by
  simp only [route,anchor_act,weight_act,graph_action_dist H hH hA]

lemma distance_act (hH : H.Connected) (g : G) (p q : Point H) :
    distance H (actPoint H hA g p) (actPoint H hA g q)=distance H p q := by
  have hv (p q : Point H) : via H (actPoint H hA g p) (actPoint H hA g q)=via H p q := by
    simp only [via,route_act H hA hH]
  cases p with
  | vertex x => cases q <;> exact hv _ _
  | edge e t =>
    cases q with
    | vertex y =>
      change via H (actPoint H hA g (.edge e t)) (actPoint H hA g (.vertex y))=via H (.edge e t) (.vertex y)
      exact hv _ _
    | edge f s =>
      have he : actDart H hA g e=actDart H hA g f ↔ e=f := (actDart_injective H hA g).eq_iff
      simp only [actPoint,distance,he]
      rw [←actPoint,←actPoint,hv]

noncomputable def act (hH : H.Connected) (g : G) : Space H hH → Space H hH := by
  let _ := premetric H hH
  exact SeparationQuotient.map (actPoint H hA g)

lemma act_embed (hH : H.Connected) (g : G) (p : Point H) :
    act H hA hH g (embed H hH p)=embed H hH (actPoint H hA g p) := by
  let _ := premetric H hH
  have hi : Isometry (actPoint H hA g) := by
    apply isometry_iff_dist_eq.mpr
    exact distance_act H hA hH g
  exact SeparationQuotient.map_mk hi.uniformContinuous p

@[instance_reducible]
noncomputable def action (hH : H.Connected) : MulAction G (Space H hH) where
  smul := act H hA hH
  one_smul x := by
    obtain ⟨p,rfl⟩ := embed_surjective H hH x
    change act H hA hH 1 (embed H hH p)=embed H hH p
    rw [act_embed,actPoint_one]
  mul_smul g h x := by
    obtain ⟨p,rfl⟩ := embed_surjective H hH x
    change act H hA hH (g*h) (embed H hH p)=act H hA hH g (act H hA hH h (embed H hH p))
    rw [act_embed,act_embed,act_embed,actPoint_mul]

end HarmonicArtin.ParabolicIntersections.GraphRealization

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_GraphRealizationHyperbolic
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hyperbolicity passes from graph vertices to the unit-interval realization. -/
namespace HarmonicArtin.ParabolicIntersections.GraphRealization
open TreeAction
variable {V : Type} (H : SimpleGraph V) (hH : H.Connected)

noncomputable def product (o x y : Space H hH) : ℝ := (dist o x+dist o y-dist x y)/2

end HarmonicArtin.ParabolicIntersections.GraphRealization

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshNilpotence
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published finite-Dynkin path input

`MeshNilpotent` is the positive-degree nilpotence assertion for the
preprojective (mesh) algebra of an induced finite Dynkin graph. Its
relations are displayed explicitly, rather than asserted for a complex.
The standard finite-dimensionality input is Amiot, *On the structure of
triangulated categories with finitely many indecomposables*, Bull. Soc.
Math. France 135 (2007), Proposition 9.1; the essential-path formulation
is Coquereaux (2002), §§3.1–3.2, and Cooper (2007), Theorem 5.4.3 and
Proposition 5.6.10. On a bipartite Dynkin graph the usual signed mesh
relations have the same zero sets as the displayed all-plus relations.

This module proves evaluation of the abstract relations. It does not
assume their vanishing for coefficient maps of the target paper's
complexes, nor assume any stabilizer or bounded-height conclusion.
-/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type} (Q : ReversibleQuiver V A) [Fintype A]

noncomputable def meshRelation (v : V) : FreeAlgebra ℂ A :=
  ∑ a, if Q.source a = v then FreeAlgebra.ι ℂ a * FreeAlgebra.ι ℂ (Q.reverse a) else 0

def meshRelations (U : Set V) : Set (FreeAlgebra ℂ A) :=
  {z | ∃ a, (Q.source a ∉ U ∨ Q.target a ∉ U) ∧ z = FreeAlgebra.ι ℂ a} ∪
  {z | ∃ a b, Q.target a ≠ Q.source b ∧ z = FreeAlgebra.ι ℂ a * FreeAlgebra.ι ℂ b} ∪
  {z | ∃ v ∈ U, z = meshRelation Q v}

/-- Exact abstract algebra input: sufficiently long positive words lie
in the two-sided ideal generated by the mesh relations. -/
def MeshNilpotent (U : Set V) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∀ w : List A, w.length = N →
    (w.map (FreeAlgebra.ι ℂ)).prod ∈ TwoSidedIdeal.span (meshRelations Q U)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshQuiver
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The simple graph of a finite induced reversible quiver. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type} (Q : ReversibleQuiver V A) (U : Set V)

def QuiverSimpleOn : Prop := ∀ a b : A, Q.source a∈U → Q.target a∈U →
  Q.source a=Q.source b → Q.target a=Q.target b → a=b

def meshQuiverGraph (hloop : ∀ a, Q.source a≠Q.target a) : SimpleGraph U where
  Adj u v := ∃ a, Q.source a=u.val ∧ Q.target a=v.val
  symm := ⟨by
    rintro u v ⟨a,hs,ht⟩
    exact ⟨Q.reverse a,(Q.source_reverse a).trans ht,(Q.target_reverse a).trans hs⟩⟩
  loopless := ⟨by
    rintro u ⟨a,hs,ht⟩
    exact hloop a (hs.trans ht.symm)⟩

variable (hloop : ∀ a, Q.source a≠Q.target a)

noncomputable def meshChosenArrow {u v : U} (h : (meshQuiverGraph Q U hloop).Adj u v) : A :=
  h.choose

lemma meshChosenArrow_source {u v : U} (h : (meshQuiverGraph Q U hloop).Adj u v) :
    Q.source (meshChosenArrow Q U hloop h)=u.val := h.choose_spec.1

lemma meshChosenArrow_target {u v : U} (h : (meshQuiverGraph Q U hloop).Adj u v) :
    Q.target (meshChosenArrow Q U hloop h)=v.val := h.choose_spec.2

lemma meshChosenArrow_eq (hsimple : QuiverSimpleOn Q U) {u v : U}
    (h : (meshQuiverGraph Q U hloop).Adj u v) (a : A)
    (hs : Q.source a=u.val) (ht : Q.target a=v.val) : meshChosenArrow Q U hloop h=a :=
  hsimple _ a ((meshChosenArrow_source Q U hloop h).symm ▸ u.property)
    ((meshChosenArrow_target Q U hloop h).symm ▸ v.property)
    ((meshChosenArrow_source Q U hloop h).trans hs.symm)
    ((meshChosenArrow_target Q U hloop h).trans ht.symm)

noncomputable def meshQuiverNeighborEquiv (hsimple : QuiverSimpleOn Q U) (v : U) :
    {u : U // (meshQuiverGraph Q U hloop).Adj u v} ≃
      {a : A // Q.source a=v.val ∧ Q.target a∈U} where
  toFun u := ⟨meshChosenArrow Q U hloop u.property.symm,
    meshChosenArrow_source Q U hloop u.property.symm,
    (meshChosenArrow_target Q U hloop u.property.symm).symm ▸ u.val.property⟩
  invFun a := ⟨⟨Q.target a.val,a.property.2⟩,
    ⟨Q.reverse a.val,Q.source_reverse a.val,(Q.target_reverse a.val).trans a.property.1⟩⟩
  left_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    exact meshChosenArrow_target Q U hloop u.property.symm
  right_inv a := by
    apply Subtype.ext
    apply meshChosenArrow_eq Q U hloop hsimple
    · exact a.property.1
    · rfl

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshQuiverWords
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonzero arrow words are actual paths in the induced simple graph. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A R : Type} (Q : ReversibleQuiver V A) (U : Set V)
  (hloop : ∀ a, Q.source a≠Q.target a) (hsimple : QuiverSimpleOn Q U)
  [Ring R]

noncomputable def meshArrowValues (B : A → R) (u v : U)
    (h : (meshQuiverGraph Q U hloop).Adj u v) : R :=
  B (meshChosenArrow Q U hloop h)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PositiveSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveSimpleLift_one _root_.OAI.HarmonicArtin.positiveSimpleLift_simple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Support of an element of the actual positive Artin monoid. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable

lemma altList_support {S : Type} (i j s : S) (n : ℕ) (hn : 2 ≤ n) :
    s ∈ altList i j n ↔ s=i ∨ s=j := by
  constructor
  · exact mem_altList i j n s
  · intro h
    obtain ⟨k, rfl⟩ : ∃ k, n=k+2 := ⟨n-2, by omega⟩
    simp only [altList_succ, List.mem_cons]
    exact h.elim Or.inl (fun hs => Or.inr (Or.inl hs))

variable {S : Type} (M : CoxeterMatrix S)

lemma support_relations : ∀ a b : FreeMonoid S, positiveBraidRelations M a b →
    FreeMonoid.lift (fun s => (⟨{s}⟩ : SupportValue S)) a =
      FreeMonoid.lift (fun s => (⟨{s}⟩ : SupportValue S)) b := by
  rintro a b ⟨i,j,rfl,rfl⟩
  simp only [FreeMonoid.lift_ofList]
  ext s
  rw [supportValue_word, supportValue_word]
  by_cases hij : i=j
  · rw [hij]
  by_cases hn : M i j=0
  · simp only [hn, altList_zero]
  · have hge : 2 ≤ M i j := by have := M.off_diagonal i j hij; omega
    rw [altList_support i j s _ hge, altList_support j i s _ hge, or_comm]

noncomputable def positiveSupportHom : PositiveArtin M →* SupportValue S :=
  PresentedMonoid.lift (fun s => ⟨{s}⟩) (support_relations M)

noncomputable def positiveSupport (a : PositiveArtin M) : Set S :=
  (positiveSupportHom M a).carrier

@[simp] lemma positiveSupport_one : positiveSupport M 1 = ∅ := by
  unfold positiveSupport
  rw [map_one]
  rfl

@[simp] lemma positiveSupport_generator (s : S) :
    positiveSupport M (positiveGenerator M s) = {s} := rfl

@[simp] lemma positiveSupport_mul (a b : PositiveArtin M) :
    positiveSupport M (a*b) = positiveSupport M a ∪ positiveSupport M b := by
  unfold positiveSupport
  rw [map_mul]
  rfl

@[simp] lemma positiveSupport_word (w : List S) :
    positiveSupport M (wordPositive M w) = {s | s ∈ w} := by
  ext s
  induction w with
  | nil => simp only [wordPositive, List.map_nil, List.prod_nil, positiveSupport_one,
      Set.mem_empty_iff_false, Set.mem_ofPred_eq, List.not_mem_nil]
  | cons t w ih =>
    change s ∈ positiveSupport M (positiveGenerator M t*wordPositive M w) ↔ _
    rw [positiveSupport_mul, Set.mem_union, positiveSupport_generator, Set.mem_singleton_iff, ih]
    exact List.mem_cons.symm

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PositiveTransport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relabeling positive Artin monoids and finite-type cancellation. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable

lemma altList_map {S T : Type} (f : S → T) (i j : S) (n : ℕ) :
    (altList i j n).map f = altList (f i) (f j) n := by
  induction n generalizing i j with
  | zero => rfl
  | succ n ih => simp only [altList_succ, List.map_cons, ih]

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_VisualAmalgam
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual amalgamated-product presentation of a visual splitting.
The factors and edge group are the standard subgroups of the given Artin
group, and the inverse homomorphism is constructed from its braid relators. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} (M : CoxeterMatrix S) (Y Z : Set S)

noncomputable def visualEdgeInclusion (b : Bool) :
    artinParabolic M (Y∩Z) →* artinParabolic M (visualSide Y Z b) :=
  Subgroup.inclusion (standard_mono M (by cases b <;> simp [visualSide]))

abbrev VisualAmalgam := Monoid.PushoutI (visualEdgeInclusion M Y Z)

noncomputable def visualToArtin : VisualAmalgam M Y Z →* Artin M :=
  Monoid.PushoutI.lift (fun b => (artinParabolic M (visualSide Y Z b)).subtype)
    (artinParabolic M (Y∩Z)).subtype (by intro b; rfl)

noncomputable def visualGenerator (hsplit : IsVisualSplit M Y Z) (s : S) : VisualAmalgam M Y Z :=
  if hs : s∈Y then Monoid.PushoutI.of false
    ⟨generator M s,Subgroup.subset_closure ⟨s,hs,rfl⟩⟩
  else Monoid.PushoutI.of true
    ⟨generator M s,Subgroup.subset_closure
      ⟨s,(visualSplit_cover M Y Z hsplit s).resolve_left hs,rfl⟩⟩

lemma visualGenerator_eq (hsplit : IsVisualSplit M Y Z) (b : Bool) (s : S)
    (hs : s∈visualSide Y Z b) :
    visualGenerator M Y Z hsplit s=Monoid.PushoutI.of b
      ⟨generator M s,Subgroup.subset_closure ⟨s,hs,rfl⟩⟩ := by
  cases b with
  | false => simp [visualGenerator,show s∈Y from hs]
  | true =>
    by_cases hy : s∈Y
    · let x : artinParabolic M (Y∩Z) :=
        ⟨generator M s,Subgroup.subset_closure ⟨s,⟨hy,hs⟩,rfl⟩⟩
      rw [visualGenerator,dite_eq_left hy]
      exact (Monoid.PushoutI.of_apply_eq_base (visualEdgeInclusion M Y Z) false x).trans
        (Monoid.PushoutI.of_apply_eq_base (visualEdgeInclusion M Y Z) true x).symm
    · simp [visualGenerator,hy]

lemma visualWord (hsplit : IsVisualSplit M Y Z) (b : Bool) (w : List S)
    (hw : ∀ s∈w, s∈visualSide Y Z b) :
    (w.map (visualGenerator M Y Z hsplit)).prod=Monoid.PushoutI.of b
      ⟨wordArtin M w,wordArtin_mem_parabolic M _ w hw⟩ := by
  induction w with
  | nil => exact (MonoidHom.map_one _).symm
  | cons s w ih =>
    simp only [List.map_cons,List.prod_cons]
    rw [visualGenerator_eq M Y Z hsplit b s (hw s (by simp)),
      ih (fun t ht => hw t (List.mem_cons_of_mem s ht)),←map_mul]
    congr 1

lemma visual_relators (hsplit : IsVisualSplit M Y Z) : ∀ r∈braidRelators M,
    FreeGroup.lift (visualGenerator M Y Z hsplit) r=1 := by
  rintro r ⟨⟨s,t⟩,rfl⟩
  by_cases hm : M s t=0
  · simp [hm,alternating]
  · obtain ⟨b,hs,ht⟩ := visualSplit_finite_edge M Y Z hsplit s t hm
    have hw : ∀ i∈altList s t (M s t), i∈visualSide Y Z b := by
      intro i hi
      rcases (show i=s ∨ i=t by simpa using mem_altList s t _ i hi) with rfl|rfl
      · exact hs
      · exact ht
    have hw' : ∀ i∈altList t s (M s t), i∈visualSide Y Z b := by
      intro i hi
      rcases (show i=t ∨ i=s by simpa using mem_altList t s _ i hi) with rfl|rfl
      · exact ht
      · exact hs
    rw [map_mul,map_inv,alternating_lift_prod,alternating_lift_prod,
      visualWord M Y Z hsplit b _ hw,visualWord M Y Z hsplit b _ hw']
    apply mul_inv_eq_one.mpr
    congr 1
    apply Subtype.ext
    exact wordArtin_braid M s t

noncomputable def visualFromArtin (hsplit : IsVisualSplit M Y Z) : Artin M →* VisualAmalgam M Y Z :=
  PresentedGroup.toGroup (visual_relators M Y Z hsplit)

@[simp] lemma visualFromArtin_generator (hsplit : IsVisualSplit M Y Z) (s : S) :
    visualFromArtin M Y Z hsplit (generator M s)=visualGenerator M Y Z hsplit s :=
  PresentedGroup.toGroup.of _

@[simp] lemma visualToArtin_generator (hsplit : IsVisualSplit M Y Z) (s : S) :
    visualToArtin M Y Z (visualGenerator M Y Z hsplit s)=generator M s := by
  unfold visualGenerator
  split <;> exact Monoid.PushoutI.lift_of _ _ _ _

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_VisualTree
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.artinExponent_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.artinMap_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.artinCoxeter_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Bass--Serre tree and stabilizers of an actual visual Artin splitting. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} (M : CoxeterMatrix S) (Y Z : Set S)
local notation "φ" => visualEdgeInclusion M Y Z

abbrev VisualVertex := AmalgamTree.Vertex φ

noncomputable abbrev visualAction (hsplit : IsVisualSplit M Y Z) :
    MulAction (Artin M) (VisualVertex M Y Z) :=
  MulAction.compHom _ (visualFromArtin M Y Z hsplit)

noncomputable def visualVertex (hsplit : IsVisualSplit M Y Z) (b : Bool) (g : Artin M) : VisualVertex M Y Z :=
  AmalgamTree.vertex φ b (visualFromArtin M Y Z hsplit g)

variable [hSplit : Fact (IsVisualSplit M Y Z)]
noncomputable local instance instMulActionArtinVisualVertex : MulAction (Artin M) (VisualVertex M Y Z) :=
  visualAction M Y Z hSplit.out

@[simp] lemma visual_smul_vertex (g h : Artin M) (b : Bool) :
    g • visualVertex M Y Z hSplit.out b h=visualVertex M Y Z hSplit.out b (g*h) := by
  change AmalgamTree.vertex φ b (visualFromArtin M Y Z hSplit.out g*visualFromArtin M Y Z hSplit.out h)=_
  rw [←map_mul]
  rfl

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_VisualTreeProperties
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Proper stabilizers and branching in the visual Bass--Serre tree. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S) (Y Z : Set S)
variable [hSplit : Fact (IsVisualSplit M Y Z)]
noncomputable local instance instMulActionArtinVisualVertex_1 : MulAction (Artin M) (VisualVertex M Y Z) :=
  visualAction M Y Z hSplit.out

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_VisualParabolicSubtree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every proper standard parabolic preserves a proper convex subtree. -/
namespace HarmonicArtin.ParabolicIntersections
open TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S) (Y Z : Set S)
variable [hSplit : Fact (IsVisualSplit M Y Z)]
noncomputable local instance visualParabolicSubtreeAction : MulAction (Artin M) (VisualVertex M Y Z) :=
  visualAction M Y Z hSplit.out

noncomputable def parabolicSubtree (X : Set S) : Set (VisualVertex M Y Z) :=
  orbitVertices (artinParabolic M X) (visualVertex M Y Z hSplit.out false 1)
    (visualVertex M Y Z hSplit.out true 1)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_NerveOrderMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe u
open scoped unitInterval
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable

noncomputable def nervePrismMap {P Q:Type u} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) : nerve P⟶TopCat.toSSet.obj (TopCat.of C(I,|nerve Q|)) where
  app n:=↾fun x=>(toSimp _ n).symm (nervePrismSimplex f g h x)
  naturality {n m} a:=by
    apply ConcreteCategory.hom_ext
    intro x
    apply (toSimp _ m).injective
    ext z t
    change toSimp (TopCat.of C(I,|nerve Q|)) m ((toSimp (TopCat.of C(I,|nerve Q|)) m).symm (nervePrismSimplex f g h ((nerve P).map a.unop.op x))) z t =
      toSimp (TopCat.of C(I,|nerve Q|)) m ((TopCat.toSSet.obj (TopCat.of C(I,|nerve Q|))).map a ((toSimp (TopCat.of C(I,|nerve Q|)) n).symm (nervePrismSimplex f g h x))) z t
    rw [Equiv.apply_symm_apply]
    have key := toSimp_naturality_apply (Y := (TopCat.of C(I,|nerve Q|))) a.unop
      ((toSimp (TopCat.of C(I,|nerve Q|)) n).symm (nervePrismSimplex f g h x)) z
    rw [Equiv.apply_symm_apply] at key
    exact (nervePrismSimplex_natural f g h a.unop x z t).trans (congrArg (fun c => c t) key.symm)

noncomputable def nervePrismReal {P Q:Type u} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) : C(|nerve P|,C(I,|nerve Q|)) :=
  ((sSetTopAdj.homEquiv _ _).symm (nervePrismMap f g h)).hom

lemma nervePrismReal_zero {P Q:Type u} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) :
    TopCat.ofHom (nervePrismReal f g h)≫nervePathEvaluate Q 0=
      SSet.toTop.map (nerveMap g.toFunctor) := by
  apply (sSetTopAdj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  simp only [nervePrismReal,TopCat.ofHom_hom,Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_unit]
  ext n x
  apply (toSimp _ n).injective
  ext z
  change toSimp _ n ((TopCat.toSSet.map (nervePathEvaluate Q 0)).app n
      ((toSimp (TopCat.of C(I,|nerve Q|)) n).symm (nervePrismSimplex f g h x))) z = _
  rw [toSimp_map, Equiv.apply_symm_apply]
  change nervePrismSimplex f g h x z 0=
    SSet.toTop.map (nerveMap g.toFunctor) (realizeSimplex (nerve P) x z)
  rw [nervePrismSimplex_zero,realizeSimplex_map]

lemma nervePrismReal_one {P Q:Type u} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) :
    TopCat.ofHom (nervePrismReal f g h)≫nervePathEvaluate Q 1=
      SSet.toTop.map (nerveMap f.toFunctor) := by
  apply (sSetTopAdj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  simp only [nervePrismReal,TopCat.ofHom_hom,Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_unit]
  ext n x
  apply (toSimp _ n).injective
  ext z
  change toSimp _ n ((TopCat.toSSet.map (nervePathEvaluate Q 1)).app n
      ((toSimp (TopCat.of C(I,|nerve Q|)) n).symm (nervePrismSimplex f g h x))) z = _
  rw [toSimp_map, Equiv.apply_symm_apply]
  change nervePrismSimplex f g h x z 1=
    SSet.toTop.map (nerveMap f.toFunctor) (realizeSimplex (nerve P) x z)
  rw [nervePrismSimplex_one,realizeSimplex_map]

noncomputable def nerveOrderComparisonHomotopy {P Q:Type u} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) :
    ContinuousMap.Homotopy (nerveOrderMap f) (nerveOrderMap g) :=
  (show ContinuousMap.Homotopy (nerveOrderMap g) (nerveOrderMap f) from {
    toFun:=fun p=>nervePrismReal f g h p.2 p.1
    continuous_toFun:=(nervePrismReal f g h).uncurry.continuous.comp continuous_swap
    map_zero_left:=fun p=>ConcreteCategory.congr_hom (nervePrismReal_zero f g h) p
    map_one_left:=fun p=>ConcreteCategory.congr_hom (nervePrismReal_one f g h) p }).symm

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_NerveOrderRetractionEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe u
open Simplicial CategoryTheory Opposite

noncomputable def nerveOrderRetractionEquiv {P Q:Type u} [Preorder P] [Preorder Q]
    (r:P→oQ) (i:Q→oP) (hr:r.comp i=OrderHom.id) (hi:∀p,p≤ i (r p)) :
    ContinuousMap.HomotopyEquiv |nerve P| |nerve Q| where
  toFun:=nerveOrderMap r
  invFun:=nerveOrderMap i
  left_inv:=by
    rw [←nerveOrderMap_comp,←nerveOrderMap_id P]
    exact ⟨(nerveOrderComparisonHomotopy (OrderHom.id (α:=P)) (i.comp r) hi).symm⟩
  right_inv:=by
    rw [←nerveOrderMap_comp,hr,nerveOrderMap_id]

end HarmonicArtin

end OAI
end


