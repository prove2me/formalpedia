-- Prove2me | Definitions.Def_OAIQ225Ag003
-- name    : OAIQ225Ag003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:19:58.766851+00:00
-- url     : https://prove2.me/theorems/948d1e32-f4fa-4b21-b736-6fc44441e297
-- title:
--   Definitions bundle OAIQ225Ag003 of the split of OpenAI, Harmonic heights and the Artin K(pi,1) conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HarmonicArtin.salvetti_cover_contractible`, carved from OpenAI's openai/math development (OpenAI, *Harmonic heights and the Artin K(pi,1) conjecture*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 374 declarations of OpenAI's Lean: 114 definitions, 2 inductive types or structures, 4 instances and 254 theorems. The definitions and types are `OAI.HarmonicArtin.Geometric.cartanForm`, `OAI.HarmonicArtin.Geometric.invariantForm`, `OAI.HarmonicArtin.Geometric.invariantScale`, `OAI.HarmonicArtin.Geometric.rootPair`, `OAI.HarmonicArtin.HasPositiveHead`, `OAI.HarmonicArtin.NaturalCylinder.linkIso`, `OAI.HarmonicArtin.NoncriticalPositiveCell`, `OAI.HarmonicArtin.OrderMappingCylinder.nerveEquiv`, `OAI.HarmonicArtin.PositiveCellPoset`, `OAI.HarmonicArtin.PositiveDescentSet`, `OAI.HarmonicArtin.PositiveEarlier`, `OAI.HarmonicArtin.PositiveLiftedCell`, `OAI.HarmonicArtin.PositiveRegion`, `OAI.HarmonicArtin.PositiveSuffix`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.PathLeft`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.PathRight`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.pathMarked`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.pathScalar`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.pathSwitch`, `OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.pathUnswitch`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.BlockClosed`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ChainIsomorphism`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ScalarExactAt`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ScalarSupported`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.blockInclusion`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.blockProjection`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.blockRestriction`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.generatorArray`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.levelArray`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.multiplicity`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.restrict`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.atLevel`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.reductionAt`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.signDiagonal`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.vertexHom`, `OAI.HarmonicArtin.SourceCosetBelow`, `OAI.HarmonicArtin.SphericalLiftedFiber`, `OAI.HarmonicArtin.WeightContractionPiece`, `OAI.HarmonicArtin.WeightContractionPiece.Extends`, `OAI.HarmonicArtin.WeightContractionPiece.inclusion` and 76 more.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `ArtinGroups_Cancellation_BlockPivot`, `ArtinGroups_Complexes_BlockClosed`, `ArtinGroups_Complexes_GeneratorArray`, `ArtinGroups_Complexes_ScalarSupported`, `ArtinGroups_Coxeter_AlternatingLiftProd`, `ArtinGroups_Coxeter_ParabolicLongest`, `ArtinGroups_Coxeter_PositiveBraidRelations`, `ArtinGroups_Functors_PathMarked`, `ArtinGroups_Geometry_Cartan`, `ArtinGroups_Geometry_CartanForm`, `ArtinGroups_Geometry_CartanOffNonpos`, `ArtinGroups_Geometry_CartanRestricted`, `ArtinGroups_Geometry_Form`, `ArtinGroups_Geometry_InvariantForm`, `ArtinGroups_Geometry_LongestMulSelf`, `ArtinGroups_Geometry_RestrictionLength`, `ArtinGroups_Geometry_RootNonnegAscent`, `ArtinGroups_Geometry_RootNonposDescent`, `ArtinGroups_Geometry_RootPair`, `ArtinGroups_Geometry_RootRowOrthogonalWord`, `ArtinGroups_Geometry_SphericalCartanPos`, `ArtinGroups_Geometry_SphericalCartanPos2`, `ArtinGroups_Geometry_StrictChamber`, `ArtinGroups_Harmonic_ConeAttachmentRel`, `ArtinGroups_Harmonic_Coset`, `ArtinGroups_Harmonic_CosetBelow`, `ArtinGroups_Harmonic_Crossing`, `ArtinGroups_Harmonic_DimensionNonneg`, `ArtinGroups_Harmonic_DimensionPosMultiplicityPos`, `ArtinGroups_Harmonic_Earlier`, `ArtinGroups_Harmonic_EarlyDelay`, `ArtinGroups_Harmonic_FiniteChainEnum`, `ArtinGroups_Harmonic_FiniteFusionEdge`, `ArtinGroups_Harmonic_FusionColorRegion`, `ArtinGroups_Harmonic_FusionFactorStep`, `ArtinGroups_Harmonic_FusionFold`, `ArtinGroups_Harmonic_FusionLabel`, `ArtinGroups_Harmonic_FusionPacketPerm`, `ArtinGroups_Harmonic_FusionRest`, `ArtinGroups_Harmonic_FusionZeroLabel`, `ArtinGroups_Harmonic_GeneratorPlacement`, `ArtinGroups_Harmonic_Harmonic`, `ArtinGroups_Harmonic_Initial`, `ArtinGroups_Harmonic_LateDelay`, `ArtinGroups_Harmonic_LeftSector`, `ArtinGroups_Harmonic_Level`, `ArtinGroups_Harmonic_LiftedDeck`, `ArtinGroups_Harmonic_OrderMappingCylinder`, `ArtinGroups_Harmonic_PacketWord`, `ArtinGroups_Harmonic_PositiveDegreeHom`, `ArtinGroups_Harmonic_PositiveDescentSet`, `ArtinGroups_Harmonic_PositiveHead`, `ArtinGroups_Harmonic_PositiveMatchingTypeKey`, `ArtinGroups_Harmonic_PositivePrefix`, `ArtinGroups_Harmonic_PositivePrefixMulLeft`, `ArtinGroups_Harmonic_PositiveRegion`, `ArtinGroups_Harmonic_PositiveReverseHom`, `ArtinGroups_Harmonic_PositiveSimpleLiftMul`, `ArtinGroups_Harmonic_PredAboveSuccSucc`, `ArtinGroups_Harmonic_PrismFlag`, `ArtinGroups_Harmonic_PrismPrefix`, `ArtinGroups_Harmonic_PrismSimplexZero`, `ArtinGroups_Harmonic_QuantumNumber`, `ArtinGroups_Harmonic_RestrictedArtinHom`, `ArtinGroups_Harmonic_RestrictionHomRange`, `ArtinGroups_Harmonic_RowReflect`, `ArtinGroups_Harmonic_SimpleFrontLink`, `ArtinGroups_Harmonic_SphericalFoldedMatrix`, `ArtinGroups_Harmonic_SphericalLongest`, `ArtinGroups_Harmonic_SphericalPair`, `ArtinGroups_Harmonic_StringAdjacent`, `ArtinGroups_Harmonic_TieCode`, `ArtinGroups_Harmonic_TopBlockMatchingKey`, `ArtinGroups_Harmonic_UnfoldedColorOrthogonal`, `ArtinGroups_Harmonic_UnfoldedHom`, `ArtinGroups_Harmonic_UnfoldedInclusion`, `ArtinGroups_Harmonic_UnfoldedMatrix`, `ArtinGroups_Harmonic_UnionCarrier`, `ArtinGroups_Quivers_Level`, `ArtinGroups_Quivers_Reduction`, `ArtinGroups_Quivers_SignDiagonal`, `ArtinGroups_Quivers_StringArrow`, `ArtinGroups_Quivers_VertexHom`, `ArtinGroups_Realizations_CellDeligne`, `ArtinGroups_Realizations_ConeWeights`, `ArtinGroups_Realizations_FusionWeightSplit`, `ArtinGroups_Realizations_NerveOrderMap`, `ArtinGroups_Realizations_NerveOrderRetractionEquiv`, `ArtinGroups_Realizations_NervePrismPatch`, `ArtinGroups_Realizations_NervePrismValue`, `ArtinGroups_Realizations_NoncriticalPositiveCell`, `ArtinGroups_Realizations_OrderWeights`, `ArtinGroups_Realizations_PositiveCellPoset`, `ArtinGroups_Realizations_PositiveLiftedCell`, `ArtinGroups_Realizations_RealizeSimplex`, `ArtinGroups_Realizations_WeightAttach`, `ArtinGroups_Realizations_WeightCarrier`, `ArtinGroups_Realizations_WeightDim`, `ArtinGroups_Realizations_WeightHomeomorph`, `ArtinGroups_Realizations_WeightLinearLinkInverse`, `ArtinGroups_Realizations_WeightMap`, `ArtinGroups_Realizations_WeightOld`, `ArtinGroups_Realizations_WeightVertexRetract`.
--
--   **Imports.** It imports the published bundle `Def_HarmonicArtin`; the bundles `OAIQ225Ag000` and `OAIQ225Ag001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ225Ag005`, `OAIQ225Ag006`, `OAIQ225Ag007` and `OAIQ225Ag008`.
-- source:
--   OpenAI, Harmonic heights and the Artin K(pi,1) conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Harmonic-heights-and-the-Artin-K-pi-1-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Definitions.Def_HarmonicArtin
import Definitions.Def_OAIQ225Ag000
import Definitions.Def_OAIQ225Ag001

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_VertexHom
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_GeneratorPlacement
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_vertex
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Level
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Cancellation_BlockPivot
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_BlockClosed
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

noncomputable def blockInclusion (E:BasedComplex Q (K:=K) I) (T:Set I) : Matrix T I (Q.Zigzag K) :=
  (projectiveIdentity Q E.placement).submatrix Subtype.val id
noncomputable def blockProjection (E:BasedComplex Q (K:=K) I) (T:Set I) : Matrix I T (Q.Zigzag K) :=
  (projectiveIdentity Q E.placement).submatrix id Subtype.val

omit [Fintype V] [DecidableEq A] in
lemma blockInclusion_mul (E:BasedComplex Q (K:=K) I) (T:Set I)
    {J:Type*} (p:J → GeneratorPlacement V) (M:Matrix I J (Q.Zigzag K))
    (hM:ProjectiveEntries Q E.placement p M) :
    blockInclusion Q E T*M=M.submatrix Subtype.val id := by
  apply Matrix.ext
  intro i j
  change (∑ k,(if (i:I)=k then vertexId Q (K:=K) (E.placement i).color else 0)*M k j)=M i j
  simp only [ite_mul,zero_mul,Fintype.sum_ite_eq]
  exact hM.1 i j

omit [Fintype V] [DecidableEq A] in
lemma mul_blockProjection (E:BasedComplex Q (K:=K) I) (T:Set I)
    {J:Type*} (p:J → GeneratorPlacement V) (M:Matrix J I (Q.Zigzag K))
    (hM:ProjectiveEntries Q p E.placement M) :
    M*blockProjection Q E T=M.submatrix id Subtype.val := by
  apply Matrix.ext
  intro i j
  change (∑ k,M i k*(if k=(j:I) then vertexId Q (K:=K) (E.placement k).color else 0))=M i j
  simp only [mul_ite,MulZeroClass.mul_zero,Fintype.sum_ite_eq']
  exact hM.2 i j

omit [Fintype V] [DecidableEq A] in
lemma blockInclusion_commute (E:BasedComplex Q (K:=K) I) (T:Set I) (h:BlockClosed Q E T) :
    (blockRestriction Q E T h).differential*blockInclusion Q E T=
      blockInclusion Q E T*E.differential := by
  rw [blockInclusion_mul Q E T _ _ E.entries]
  apply Matrix.ext
  intro i j
  change (∑ k:T,E.differential i k*(if (k:I)=j then vertexId Q (K:=K) (E.placement k).color else 0))=E.differential i j
  by_cases hj:j∈T
  · let j':T:=⟨j,hj⟩
    have he (k:T) : ((k:I)=j) ↔ k=j' := by simp only [j',Subtype.ext_iff]
    simp only [he,mul_ite,MulZeroClass.mul_zero,Fintype.sum_ite_eq']
    exact E.entries.2 i j
  · have hz:E.differential i j=0 := by
      by_contra hh
      exact hj ((h i j hh).mp i.property)
    rw [hz]
    apply Finset.sum_eq_zero
    intro k _
    have hne:(k:I)≠j := by intro he; exact hj (he ▸ k.property)
    rw [ite_eq_right hne,MulZeroClass.mul_zero]

omit [Fintype V] [DecidableEq A] in
lemma blockProjection_commute (E:BasedComplex Q (K:=K) I) (T:Set I) (h:BlockClosed Q E T) :
    E.differential*blockProjection Q E T=
      blockProjection Q E T*(blockRestriction Q E T h).differential := by
  rw [mul_blockProjection Q E T _ _ E.entries]
  apply Matrix.ext
  intro i j
  change E.differential i j=(∑ k:T,(if i=(k:I) then vertexId Q (K:=K) (E.placement i).color else 0)*E.differential k j)
  by_cases hi:i∈T
  · let i':T:=⟨i,hi⟩
    have he (k:T) : (i=(k:I)) ↔ i'=k := by simp only [i',Subtype.ext_iff]
    simp only [he,ite_mul,zero_mul,Fintype.sum_ite_eq]
    exact (E.entries.1 i j).symm
  · have hz:E.differential i j=0 := by
      by_contra hh
      exact hi ((h i j hh).mpr j.property)
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro k _
    have hne:i≠(k:I) := by intro he; exact hi (he.symm ▸ k.property)
    rw [ite_eq_right hne,zero_mul]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_Reduction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_vertex
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_GeneratorArray
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ScalarSupported
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

omit [DecidableEq I] in
lemma scalarDifferential_square (E:BasedComplex Q (K:=K) I) (α:V) :
    E.differential.map (vertexHom Q α) * E.differential.map (vertexHom Q α)=0 := by
  rw [← Matrix.map_mul,E.square_zero]
  apply Matrix.ext
  intro i j
  change (vertexHom Q α) (0:Q.Zigzag K)=0
  exact map_zero _

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_Level
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J L : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

def atLevel (p : I → GeneratorPlacement V) (q : J → GeneratorPlacement V)
    (M : Matrix I J (Q.Zigzag K)) (d : ℤ) :
    Matrix {i // (p i).level = d} {j // (q j).level = d} (Q.Zigzag K) :=
  fun i j => M i.val j.val

lemma atLevel_mul [Fintype J]
    (p : I → GeneratorPlacement V) (q : J → GeneratorPlacement V)
    (r : L → GeneratorPlacement V) (M : Matrix I J (Q.Zigzag K))
    (N : Matrix J L (Q.Zigzag K)) (d : ℤ)
    [Fintype {j // (q j).level = d}]
    (hM : ∀ i j, M i j ≠ 0 → (q j).level ≤ (p i).level)
    (hN : ∀ j k, N j k ≠ 0 → (r k).level ≤ (q j).level) :
    atLevel Q p r (M * N) d = atLevel Q p q M d * atLevel Q q r N d := by
  classical
  apply Matrix.ext
  intro i k
  change (∑ j, M i.val j * N j k.val) =
    ∑ j : {j // (q j).level = d}, M i.val j.val * N j.val k.val
  symm
  apply Fintype.sum_of_injective (Subtype.val : {j // (q j).level = d} → J)
    Subtype.val_injective
  · intro j hj
    by_cases h₁ : M i.val j = 0
    · rw [h₁]
      exact MulZeroClass.zero_mul _
    by_cases h₂ : N j k.val = 0
    · rw [h₂]
      exact MulZeroClass.mul_zero _
    have hle := hM i.val j h₁
    have hge := hN j k.val h₂
    have hq : (q j).level = d := by
      rw [i.property] at hle
      rw [k.property] at hge
      exact le_antisymm hle hge
    exact (hj ⟨⟨j, hq⟩, rfl⟩).elim
  · intro j
    rfl

lemma atLevel_add (p : I → GeneratorPlacement V) (q : J → GeneratorPlacement V)
    (M N : Matrix I J (Q.Zigzag K)) (d : ℤ) :
    atLevel Q p q (M + N) d = atLevel Q p q M d + atLevel Q p q N d := rfl

lemma atLevel_identity [DecidableEq I] (p : I → GeneratorPlacement V) (d : ℤ) :
    atLevel Q p p (projectiveIdentity Q (K := K) p) d =
      projectiveIdentity Q (fun i : {i // (p i).level = d} => p i.val) := by
  apply Matrix.ext
  intro i j
  change (if i.val = j.val then vertexId Q (p i.val).color else 0) =
    (if i = j then vertexId Q (p i.val).color else 0)
  simp only [Subtype.val_inj]

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Crossing
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_StringArrow
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_LeftSector
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_PathMarked
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_QuantumNumber
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionLabel
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_StringAdjacent
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionRest
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionFactorStep
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionPacketPerm
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_AlternatingLiftProd
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_Cartan
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric

open scoped Classical

variable {S W : Type*} [DecidableEq S] [Group W]

lemma cartan_symm (M : CoxeterMatrix S) (i j : S) : cartan M i j=cartan M j i := by
  simp only [cartan, M.symmetric i j, eq_comm]

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_Form
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPreorderLiftedCell
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric.FiniteOrbit
open _root_.Matrix
open scoped _root_.Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S G:Type*} [Fintype S] [Group G] [Fintype G]
  (ρ:G →* (S → ℝ) ≃ₗ[ℝ] (S → ℝ))

variable [DecidableEq S]

lemma form_basis_row {M:CoxeterMatrix S} (i:S) (g:G)
    (hg:ρ g=simpleReflection M i) (x:S → ℝ) :
    form ρ (Pi.single i 1) x=
      (form ρ (Pi.single i 1) (Pi.single i 1)/2)*(cartan M *ᵥ x) i := by
  have h:=form_invariant ρ g (Pi.single i 1) x
  have he : simpleReflection M i (Pi.single i 1)= -(Pi.single i 1) := by
    simp only [simpleReflection_apply]
    have hh : (cartan M *ᵥ Pi.single i 1) i=2 := by simp [Matrix.mulVec_single]
    rw [hh]
    module
  rw [hg,he,simpleReflection_apply,
    form_neg_left,form_sub_right,form_smul_right] at h
  linarith

variable {T:Type*}
  {M:CoxeterMatrix S} (ι:T → S) (g:T → G) (hg:∀ i,ρ (g i)=simpleReflection M (ι i))

include hg

lemma scale_balance (i j:T) :
    scale ρ (ι i)*cartan M (ι i) (ι j)=scale ρ (ι j)*cartan M (ι i) (ι j) := by
  have h:=form_symm ρ (Pi.single (ι i) 1) (Pi.single (ι j) 1)
  rw [form_basis_row ρ (ι i) (g i) (hg i) (Pi.single (ι j) 1),
    form_basis_row ρ (ι j) (g j) (hg j) (Pi.single (ι i) 1)] at h
  simpa [Matrix.mulVec_single,← cartan_symm M (ι i) (ι j),scale] using h

variable [Fintype T]

lemma form_matrix (x y:T → ℝ) :
    form ρ (∑ i,x i • Pi.single (ι i) 1) (∑ j,y j • Pi.single (ι j) 1)=
      ∑ i,∑ j,scale ρ (ι i)*cartan M (ι i) (ι j)*x i*y j := by
  rw [form_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [form_smul_left,form_basis_row ρ (ι i) (g i) (hg i)]
  simp only [Matrix.mulVec_sum,Matrix.mulVec_smul,Finset.sum_apply,Pi.smul_apply,
    Matrix.mulVec_single,smul_eq_mul,Finset.mul_sum,scale,
    MulOpposite.op_one,one_smul,Matrix.col,Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem principal_posDef (hι:Function.Injective ι) :
    ((cartan M).submatrix ι ι).PosDef := by
  have hs : ((cartan M).submatrix ι ι).IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j
    exact cartan_symm M (ι j) (ι i)
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hs
  intro x hx
  let z:T → ℝ := fun i=>x i/Real.sqrt (scale ρ (ι i))
  have heval (v:T → ℝ) (i:T) : (∑ j,v j • Pi.single (ι j) (1:ℝ)) (ι i)=v i := by
    simp only [Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul]
    simp [hι.eq_iff]
  have hz:(∑ i,z i • Pi.single (ι i) (1:ℝ))≠0 := by
    intro h
    apply hx
    ext i
    have hi:=congrFun h (ι i)
    rw [heval] at hi
    exact (div_eq_zero_iff.mp hi).resolve_right (ne_of_gt (Real.sqrt_pos.2 (scale_pos ρ (ι i))))
  have hpos:=form_pos ρ _ hz
  rw [form_matrix ρ ι g hg] at hpos
  have he : (∑ i,∑ j,scale ρ (ι i)*cartan M (ι i) (ι j)*z i*z j)=
      x ⬝ᵥ (((cartan M).submatrix ι ι) *ᵥ x) := by
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,Matrix.submatrix_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij:cartan M (ι i) (ι j)=0
    · simp [hij]
    · have hd:=mul_right_cancel₀ hij (scale_balance ρ ι g hg i j)
      have hn:=ne_of_gt (Real.sqrt_pos.2 (scale_pos ρ (ι i)))
      have hsq:=Real.sq_sqrt (scale_pos ρ (ι i)).le
      dsimp [z]
      rw [← hd]
      field_simp
      rw [hsq]
      ring
  rw [he] at hpos
  simpa only [star_trivial] using hpos

end HarmonicArtin.Geometric.FiniteOrbit

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_SphericalCartanPos
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] [DecidableEq S]

theorem spherical_cartan_posDef (M:CoxeterMatrix S) (J:Set S) (hJ:IsSpherical M J) :
    ((cartan M).submatrix ((↑):J → S) ((↑):J → S)).PosDef := by
  let : Finite (coxeterParabolic M J) := hJ
  let : Fintype (coxeterParabolic M J) := Fintype.ofFinite _
  let ρ := (representation M.toCoxeterSystem).comp (coxeterParabolic M J).subtype
  let g:J → coxeterParabolic M J := fun i=>⟨M.simple i,
    Subgroup.subset_closure (Set.mem_image_of_mem _ i.property)⟩
  apply FiniteOrbit.principal_posDef ρ ((↑):J → S) g
  · intro i
    exact representation_simple M.toCoxeterSystem i
  · exact Subtype.val_injective

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_RootNonnegAscent
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_CartanRestricted
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_RestrictionLength
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_RootNonposDescent
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPreorderLiftedCell
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

lemma length_le_of_all_descents (z : W)
    (hz : ∀ i,cs.length (z*cs.simple i)+1=cs.length z) (w : W) :
    cs.length w ≤ cs.length z := by
  have := length_mul_of_all_descents cs z hz w
  omega

theorem finite_of_all_descents (z : W)
    (hz : ∀ i,cs.length (z*cs.simple i)+1=cs.length z) : Finite W := by
  apply Set.finite_univ_iff.mp
  apply ((List.finite_length_le S (cs.length z)).image cs.wordProd).subset
  intro w _
  obtain ⟨u,hu,he⟩ := cs.exists_isReduced w
  refine ⟨u,?_,he.symm⟩
  change u.length ≤ cs.length z
  rw [← hu.eq,← he]
  exact length_le_of_all_descents cs z hz w

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_LongestMulSelf
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_PositiveBraidRelations
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

lemma wordPositive_append (u v:List S) : wordPositive M (u++v)=wordPositive M u*wordPositive M v := by
  simp only [wordPositive,List.map_append,List.prod_append]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositiveDegreeHom
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_CellDeligne
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe v
variable {S : Type v}

def cellToDeligne (M : CoxeterMatrix S) (a : LiftedCell M) : Deligne M :=
  ⟨(a.2.1,rightCoset M a.2.1 a.1⁻¹),a.2.property,⟨a.1⁻¹,rfl⟩⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositiveSimpleLiftMul
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

lemma positiveSimpleLift_mul (a b:M.Group)
    (h:M.toCoxeterSystem.length (a*b)=M.toCoxeterSystem.length a+M.toCoxeterSystem.length b) :
    positiveSimpleLift M (a*b)=positiveSimpleLift M a*positiveSimpleLift M b := by
  let u:=reducedExpression M a
  let v:=reducedExpression M b
  have hu:M.toCoxeterSystem.IsReduced u:=reducedExpression_reduced M a
  have hv:M.toCoxeterSystem.IsReduced v:=reducedExpression_reduced M b
  have he:wordCoxeter M (u++v)=a*b:=by
    rw [wordCoxeter_append,wordCoxeter_reducedExpression,wordCoxeter_reducedExpression]
  have hr:M.toCoxeterSystem.IsReduced (u++v):=by
    change M.toCoxeterSystem.length (wordCoxeter M (u++v))=(u++v).length
    rw [he,h,List.length_append,←hu.eq,←hv.eq]
    change M.toCoxeterSystem.length a+M.toCoxeterSystem.length b=M.toCoxeterSystem.length (wordCoxeter M u)+M.toCoxeterSystem.length (wordCoxeter M v)
    rw [wordCoxeter_reducedExpression,wordCoxeter_reducedExpression]
  rw [←he,positiveSimpleLift_word M _ hr,wordPositive_append]
  rfl

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

lemma positiveSimpleLift_left_complement (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z) (w:M.Group) :
    positiveSimpleLift M w*positiveSimpleLift M (w⁻¹*z)=positiveSimpleLift M z := by
  have hl:=length_mul_longest M z hz w⁻¹
  rw [M.toCoxeterSystem.length_inv] at hl
  have h:=positiveSimpleLift_mul M w (w⁻¹*z) (by rw [mul_inv_cancel_left];omega)
  simpa only [mul_inv_cancel_left] using h.symm

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositivePrefix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} (M:CoxeterMatrix S)

variable [Fintype S]

lemma positivePrefix_simple_iff (u v:M.Group) :
    PositivePrefix M (positiveSimpleLift M u) (positiveSimpleLift M v) ↔ WeakPrefix M.toCoxeterSystem u v := by
  constructor
  · rintro ⟨c,hc⟩
    have hsimple:=(positive_simple_factors M (positiveSimpleLift M u) c v hc.symm).2
    have hm:=congrArg (positiveToCoxeter M) hc
    simp only [positiveToCoxeter_simpleLift,map_mul] at hm
    have he:positiveToCoxeter M c=u⁻¹*v:=by rw [hm,inv_mul_cancel_left]
    have hd:=congrArg (positiveDegree M) hc
    simp only [positiveDegree_simpleLift,positiveDegree_mul] at hd
    rw [hsimple,positiveDegree_simpleLift,he] at hd
    exact hd
  · intro h
    refine ⟨positiveSimpleLift M (u⁻¹*v),?_⟩
    have he:=positiveSimpleLift_mul M u (u⁻¹*v) (by simpa only [mul_inv_cancel_left] using (show M.toCoxeterSystem.length v=M.toCoxeterSystem.length u+M.toCoxeterSystem.length (u⁻¹*v) from h))
    simpa only [mul_inv_cancel_left] using he

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_RestrictionHomRange
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

omit [Fintype S] in
lemma restrictionHom_range_eq (J:Set S) :
    (restrictionHom M J).range=coxeterParabolic M J := by
  apply le_antisymm
  · rintro _ ⟨w,rfl⟩
    exact Geometric.restrictionHom_mem_parabolic M J w
  · apply (Subgroup.closure_le _).mpr
    rintro y ⟨i,hi,rfl⟩
    exact ⟨(restrictedMatrix M J).toCoxeterSystem.simple ⟨i,hi⟩,
      restrictionHom_simple M J ⟨i,hi⟩⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_ParabolicLongest
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

lemma exists_parabolic_longest (T:Set S) (hT:IsSpherical M T) :
    ∃z:M.Group,IsParabolicLongest M T z := by
  let : Finite (restrictedMatrix M T).Group := restricted_finite M T hT
  obtain ⟨z,hz⟩:=exists_longest (restrictedMatrix M T).toCoxeterSystem
  refine ⟨restrictionHom M T z,Geometric.restrictionHom_mem_parabolic M T z,?_⟩
  intro w hw
  have hr:w∈(restrictionHom M T).range:=by rw [restrictionHom_range_eq];exact hw
  obtain ⟨v,rfl⟩:=hr
  simpa only [restriction_length] using hz v

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_InvariantForm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPreorderLiftedCell
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

lemma invariantScale_balance (i j:S) :
    invariantScale cs i * cartan M i j=invariantScale cs j * cartan M i j := by
  have h:=invariantForm_symm cs (Pi.single i 1) (Pi.single j 1)
  rw [invariantForm_basis_row cs i (Pi.single j 1),invariantForm_basis_row cs j (Pi.single i 1)] at h
  simpa [Matrix.mulVec_single,← cartan_symm M i j,invariantScale] using h

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

include cs in

theorem cartan_posDef : (cartan M).PosDef := by
  have hs : (cartan M).IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j
    exact cartan_symm M j i
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hs
  intro x hx
  let z:S → ℝ := fun i=>x i/Real.sqrt (invariantScale cs i)
  have hz:z≠0 := by
    intro h
    apply hx
    ext i
    have hi:=congrFun h i
    exact (div_eq_zero_iff.mp hi).resolve_right (ne_of_gt (Real.sqrt_pos.2 (invariantScale_pos cs i)))
  have hpos:=invariantForm_pos cs z hz
  rw [invariantForm_matrix] at hpos
  have he : (∑ i,∑ j,invariantScale cs i*cartan M i j*z i*z j)=x ⬝ᵥ (cartan M *ᵥ x) := by
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij:cartan M i j=0
    · simp [hij]
    · have hd:=mul_right_cancel₀ hij (invariantScale_balance cs i j)
      have hn:=ne_of_gt (Real.sqrt_pos.2 (invariantScale_pos cs i))
      have hsq:=Real.sq_sqrt (invariantScale_pos cs i).le
      dsimp [z]
      rw [← hd]
      field_simp
      rw [hsq]
      ring
  rw [he] at hpos
  simpa only [star_trivial] using hpos

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_StrictChamber
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

include cs in

lemma exists_strict_chamber : ∃ p:S → ℝ,∀ i,(cartan M *ᵥ p) i=1 := by
  have hu := (cartan_posDef cs).isUnit
  have hs := (Matrix.mulVec_surjective_iff_isUnit (A:=cartan M)).mpr hu
  obtain ⟨p,hp⟩:=hs (fun _=>1)
  exact ⟨p,fun i=>congrFun hp i⟩

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_CartanOffNonpos
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_CartanForm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open _root_.Matrix CoxeterExchange
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W:Type*} [Fintype S] [DecidableEq S] [Group W]
  {M:CoxeterMatrix S} (cs:CoxeterSystem M W)

noncomputable def cartanForm (M:CoxeterMatrix S) (x y:S→ℝ) : ℝ := x ⬝ᵥ (cartan M *ᵥ y)

lemma cartanForm_symm (M:CoxeterMatrix S) (x y:S→ℝ) : cartanForm M x y=cartanForm M y x := by
  simp only [cartanForm,Matrix.mulVec,dotProduct,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [cartan_symm M j i]
  ring

lemma cartanForm_single_left (M:CoxeterMatrix S) (i:S) (x:S→ℝ) :
    cartanForm M (Pi.single i 1) x=(cartan M *ᵥ x) i := by
  simp [cartanForm]

lemma cartanForm_single_right (M:CoxeterMatrix S) (x:S→ℝ) (i:S) :
    cartanForm M x (Pi.single i 1)=(cartan M *ᵥ x) i := by
  rw [cartanForm_symm,cartanForm_single_left]

lemma cartanForm_reflection (M:CoxeterMatrix S) (i:S) (x y:S→ℝ) :
    cartanForm M (simpleReflection M i x) (simpleReflection M i y)=cartanForm M x y := by
  simp only [simpleReflection_apply,cartanForm,Matrix.mulVec_sub,Matrix.mulVec_smul,
    dotProduct_sub,sub_dotProduct,dotProduct_smul,smul_dotProduct,smul_eq_mul]
  change cartanForm M x y - (cartan M *ᵥ x) i * cartanForm M (Pi.single i 1) y -
    (cartan M *ᵥ y) i * (cartanForm M x (Pi.single i 1) -
      (cartan M *ᵥ x) i * cartanForm M (Pi.single i 1) (Pi.single i 1)) = _
  rw [cartanForm_single_right,cartanForm_single_left,cartanForm_single_left]
  have hd : (cartan M *ᵥ Pi.single i (1:ℝ)) i = 2 := by simp [Matrix.mulVec_single]
  rw [hd]
  change cartanForm M x y - _ - _ = cartanForm M x y
  ring

lemma cartanForm_invariant (w:W) (x y:S→ℝ) :
    cartanForm M (representation cs w x) (representation cs w y)=cartanForm M x y := by
  obtain ⟨u,hu,he⟩:=cs.exists_isReduced w
  rw [he]
  clear hu he w
  induction u with
  | nil => simp
  | cons i u ih =>
    simpa only [cs.wordProd_cons,map_mul,LinearEquiv.mul_apply,representation_simple,
      cartanForm_reflection] using ih

lemma positive_root_sum_ge_one (w:W) (i:S)
    (h:∀j,0 ≤ representation cs w (Pi.single i 1) j) :
    1≤∑j,representation cs w (Pi.single i 1) j := by
  let v:=representation cs w (Pi.single i 1)
  have hq:cartanForm M v v=2 := by
    rw [cartanForm_invariant,cartanForm_single_left]
    simp [Matrix.mulVec_single]
  have hb:∀j k,cartan M j k≤(2:ℝ) := by
    intro j k
    by_cases he:j=k
    · subst k; simp
    · exact (cartan_off_nonpos M j k he).trans (by norm_num)
  have hh:cartanForm M v v≤2*(∑j,v j)^2 := by
    calc
      cartanForm M v v = ∑j,∑k,v j*cartan M j k*v k := by
        simp only [cartanForm,Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc]
      _ ≤ ∑j,∑k,v j*2*v k := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hb j k) (h j)) (h k)
      _ = 2*(∑j,v j)^2 := by
        simp only [Finset.sum_mul,Finset.mul_sum,pow_two]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hn:0≤∑j,v j:=Finset.sum_nonneg (fun j _=>h j)
  change 1≤∑j,v j
  nlinarith

lemma length_sum_bound (x:S→ℝ) (hx:cartan M *ᵥ x=1) (w:W) :
    (cs.length w:ℝ)+(∑i,representation cs w x i)≤∑i,x i := by
  have H:∀u:List S,cs.IsReduced u→
      (u.length:ℝ)+(∑i,representation cs (cs.wordProd u) x i)≤∑i,x i := by
    intro u
    induction u using List.reverseRecOn with
    | nil => simp
    | append_singleton u i ih =>
      intro hr
      have hru:cs.IsReduced u:=by simpa only [List.take_left] using hr.take u.length
      have hp:=ih hru
      have has:cs.length (cs.wordProd u*cs.simple i)=cs.length (cs.wordProd u)+1 := by
        simpa only [cs.wordProd_append,cs.wordProd_singleton,List.length_append,
          List.length_singleton,hru.eq] using hr.eq
      have hroot:=positive_root_sum_ge_one cs (cs.wordProd u) i (root_nonneg_of_ascent cs _ _ has)
      have he:simpleReflection M i x=x-Pi.single i 1 := by
        rw [simpleReflection_apply,hx]
        simp only [Pi.one_apply,one_smul]
      simp only [cs.wordProd_append,cs.wordProd_singleton,map_mul,LinearEquiv.mul_apply,
        representation_simple,he,map_sub,Pi.sub_apply,Finset.sum_sub_distrib,
        List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one]
      linarith
  obtain ⟨u,hu,he⟩:=cs.exists_isReduced w
  simpa only [←hu.eq,←he] using H u hu

include cs in

theorem finite_of_cartan_posDef (hC:(cartan M).PosDef) : Finite W := by
  let x: S→ℝ := (cartan M)⁻¹ *ᵥ 1
  have hx:cartan M *ᵥ x=1 := by
    dsimp [x]
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hC.isUnit),
      Matrix.one_mulVec]
  have hs:∀v:S→ℝ,cartanForm M v x=∑i,v i := by
    intro v
    simp only [cartanForm,hx,dotProduct,Pi.one_apply,mul_one]
  have hl:∀w:W,-(∑i,x i)≤∑i,representation cs w x i := by
    intro w
    let v:=representation cs w x
    have hn:=hC.posSemidef.dotProduct_mulVec_nonneg (v+x)
    simp only [star_trivial] at hn
    have hq:cartanForm M v v=cartanForm M x x:=cartanForm_invariant cs w x x
    have he:cartanForm M (v+x) (v+x)=cartanForm M v v+cartanForm M v x+
        cartanForm M x v+cartanForm M x x := by
      simp only [cartanForm,Matrix.mulVec_add,dotProduct_add,add_dotProduct]
      ring
    change 0 ≤ cartanForm M (v+x) (v+x) at hn
    rw [he,hq,cartanForm_symm M x v,hs,hs] at hn
    dsimp [v] at hn
    linarith
  obtain ⟨N,hN⟩:=exists_nat_ge (2*∑i,x i)
  have hb:∀w:W,cs.length w≤N := by
    intro w
    have h1:=length_sum_bound cs x hx w
    have h2:=hl w
    have h3:(cs.length w:ℝ)≤N:=by linarith
    exact_mod_cast h3
  apply Set.finite_univ_iff.mp
  apply ((List.finite_length_le S N).image cs.wordProd).subset
  intro w _
  obtain ⟨u,hu,he⟩:=cs.exists_isReduced w
  refine ⟨u,?_,he.symm⟩
  change u.length≤N
  rw [←hu.eq,←he]
  exact hb w

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_RootPair
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPreorderLiftedCell
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open _root_.Matrix HarmonicArtin.CoxeterExchange
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W : Type*} [Fintype S] [DecidableEq S] [Group W]
  {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

noncomputable def rootPair (M : CoxeterMatrix S) (x y : S → ℝ) : ℝ :=
  x ⬝ᵥ (cartan M *ᵥ y)

lemma rootPair_symm (M : CoxeterMatrix S) (x y : S → ℝ) : rootPair M x y=rootPair M y x := by
  simp only [rootPair,Matrix.mulVec,dotProduct,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [cartan_symm M j i]
  ring

lemma rootPair_sub_left (M : CoxeterMatrix S) (x y z : S → ℝ) :
    rootPair M (x-y) z=rootPair M x z-rootPair M y z := by
  simp only [rootPair,sub_dotProduct]

lemma rootPair_sub_right (M : CoxeterMatrix S) (x y z : S → ℝ) :
    rootPair M x (y-z)=rootPair M x y-rootPair M x z := by
  simp only [rootPair,Matrix.mulVec_sub,dotProduct_sub]

lemma rootPair_smul_left (M : CoxeterMatrix S) (r : ℝ) (x y : S → ℝ) :
    rootPair M (r • x) y=r*rootPair M x y := by
  simp only [rootPair,smul_dotProduct,smul_eq_mul]

lemma rootPair_smul_right (M : CoxeterMatrix S) (r : ℝ) (x y : S → ℝ) :
    rootPair M x (r • y)=r*rootPair M x y := by
  rw [rootPair_symm,rootPair_smul_left,rootPair_symm M y x]

lemma rootPair_basis_left (M : CoxeterMatrix S) (i : S) (x : S → ℝ) :
    rootPair M (Pi.single i 1) x=rootRow M i x := by
  simp [rootPair,dotProduct,Pi.single_apply,rootRow_apply]

lemma rootPair_basis_right (M : CoxeterMatrix S) (i : S) (x : S → ℝ) :
    rootPair M x (Pi.single i 1)=rootRow M i x := by
  rw [rootPair_symm,rootPair_basis_left]

lemma reflection_rootPair (M : CoxeterMatrix S) (i : S) (x y : S → ℝ) :
    rootPair M (simpleReflection M i x) (simpleReflection M i y)=rootPair M x y := by
  simp only [simpleReflection_apply,← rootRow_apply,rootPair_sub_left,rootPair_sub_right,
    rootPair_smul_left,rootPair_smul_right,rootPair_basis_left,rootPair_basis_right,
    map_sub,map_smul,rootRow_single,cartan_diag,smul_eq_mul]
  ring

lemma representation_rootPair (w : W) (x y : S → ℝ) :
    rootPair M (representation cs w x) (representation cs w y)=rootPair M x y := by
  induction w using cs.simple_induction_left generalizing x y with
  | one => simp
  | mul_simple_left w i ih =>
    rw [map_mul,LinearEquiv.mul_apply,LinearEquiv.mul_apply,representation_simple,
      reflection_rootPair,ih]

lemma rootRow_representation (w : W) (s : S) (p : S → ℝ) :
    rootRow M s (representation cs w p)=rootPair M (representation cs w⁻¹ (Pi.single s 1)) p := by
  have h := representation_rootPair cs w (representation cs w⁻¹ (Pi.single s 1)) p
  rw [← LinearEquiv.mul_apply,← map_mul,mul_inv_cancel,map_one] at h
  change rootPair M (Pi.single s 1) (representation cs w p)=_ at h
  simpa only [rootPair_basis_left] using h

lemma rootPair_pos (M : CoxeterMatrix S) (p x : S → ℝ)
    (hp : ∀ i,0 < rootRow M i p) (hx : ∀ i,0 ≤ x i) (hne : x≠0) :
    0 < rootPair M x p := by
  obtain ⟨i,hi⟩ : ∃ i,x i≠0 := by
    by_contra! h
    exact hne (funext h)
  have hi' : 0 < x i := lt_of_le_of_ne (hx i) (Ne.symm hi)
  change 0 < ∑ j,x j*rootRow M j p
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hx j) (hp j).le)
    ⟨i,Finset.mem_univ _,mul_pos hi' (hp i)⟩

lemma rootPair_nonpos (M : CoxeterMatrix S) (p x : S → ℝ)
    (hp : ∀ i,0 < rootRow M i p) (hx : ∀ i,x i≤0) : rootPair M x p≤0 := by
  change (∑ j,x j*rootRow M j p)≤0
  exact Finset.sum_nonpos (fun j _ => mul_nonpos_of_nonpos_of_nonneg (hx j) (hp j).le)

theorem rootRow_pos_iff_left_ascent (p : S → ℝ) (hp : ∀ i,0 < rootRow M i p)
    (w : W) (s : S) :
    0 < rootRow M s (representation cs w p) ↔
      cs.length (cs.simple s*w)=cs.length w+1 := by
  rw [rootRow_representation]
  constructor
  · intro h
    rcases cs.length_mul_simple w⁻¹ s with ha | hd
    · simpa only [inverse_right_length,cs.length_inv] using ha
    · have hn := root_nonpos_of_descent cs w⁻¹ s hd
      exact (not_lt_of_ge (rootPair_nonpos M p _ hp hn) h).elim
  · intro h
    have ha : cs.length (w⁻¹*cs.simple s)=cs.length w⁻¹+1 := by
      simpa only [inverse_right_length,cs.length_inv] using h
    exact rootPair_pos M p _ hp (root_nonneg_of_ascent cs w⁻¹ s ha)
      (geometric_root_ne_zero cs w⁻¹ s)

theorem chamber_stabilizer (p : S → ℝ) (hp : ∀ i,0 < rootRow M i p)
    (w : W) (hw : representation cs w p=p) : w=1 := by
  by_contra h
  obtain ⟨s,hs⟩ := exists_right_descent cs (inv_ne_one.mpr h)
  have has : cs.length (cs.simple s*w)=cs.length w+1 :=
    (rootRow_pos_iff_left_ascent cs p hp w s).mp (by rw [hw]; exact hp s)
  rw [inverse_right_length,cs.length_inv] at hs
  omega

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_RootRowOrthogonalWord
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

theorem orthogonal_ascent_block (p : S → ℝ) (hp : ∀ i,0 < rootRow M i p)
    (u : List S) (hu : u.Nodup)
    (ho : ∀ i∈u,∀ j∈u,i≠j → cartan M i j=0)
    (w : W) (hw : ∀ i∈u,cs.length (cs.simple i*w)=cs.length w+1) :
    cs.length (cs.wordProd u*w)=u.length+cs.length w := by
  induction u with
  | nil => simp
  | cons i u ih =>
    obtain ⟨hin,hn⟩ := List.nodup_cons.mp hu
    have ho' : ∀ a∈u,∀ b∈u,a≠b → cartan M a b=0 :=
      fun a ha b hb => ho a (by simp [ha]) b (by simp [hb])
    have hw' : ∀ a∈u,cs.length (cs.simple a*w)=cs.length w+1 :=
      fun a ha => hw a (by simp [ha])
    have hi : 0 < rootRow M i (representation cs w p) :=
      (rootRow_pos_iff_left_ascent cs p hp w i).mpr (hw i (by simp))
    have hi' : 0 < rootRow M i (representation cs (cs.wordProd u*w) p) := by
      rw [map_mul,LinearEquiv.mul_apply,rootRow_orthogonal_word]
      · exact hi
      · intro j hj
        exact ho i (by simp) j (by simp [hj]) (fun he => hin (he ▸ hj))
    have ha := (rootRow_pos_iff_left_ascent cs p hp (cs.wordProd u*w) i).mp hi'
    rw [CoxeterSystem.wordProd_cons,mul_assoc,ha,ih hn ho' hw',List.length_cons]
    omega

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_SphericalCartanPos2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open HarmonicArtin.CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] [DecidableEq S]

theorem spherical_of_cartan_posDef (M:CoxeterMatrix S) (J:Set S)
    (hJ:((cartan M).submatrix ((↑):J→S) Subtype.val).PosDef) : IsSpherical M J := by
  have hC:(cartan (restrictedMatrix M J)).PosDef := by rwa [cartan_restricted]
  let : Finite (restrictedMatrix M J).Group := finite_of_cartan_posDef
    (restrictedMatrix M J).toCoxeterSystem hC
  have hr:coxeterParabolic M J≤(restrictionHom M J).range := by
    apply (Subgroup.closure_le _).mpr
    rintro y ⟨i,hi,rfl⟩
    exact ⟨(restrictedMatrix M J).toCoxeterSystem.simple ⟨i,hi⟩,restrictionHom_simple M J ⟨i,hi⟩⟩
  apply Finite.of_surjective
    (fun w=>(⟨restrictionHom M J w,restrictionHom_mem_parabolic M J w⟩:coxeterParabolic M J))
  intro y
  obtain ⟨w,hw⟩:=hr y.property
  exact ⟨w,Subtype.ext hw⟩

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ConeAttachmentRel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.orderWeightSupportLinearOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

universe u v
variable {A:Type u} {L:Type v} [TopologicalSpace A] [TopologicalSpace L]

noncomputable def coneAttachmentOld (f:C(L,A)) : C(A,ConeAttachment f) :=
  ⟨fun a=>Quot.mk _ (.inl a),continuous_quot_mk.comp continuous_inl⟩

noncomputable def coneAttachmentCone (f:C(L,A)) : C(I×L,ConeAttachment f) :=
  ⟨fun p=>Quot.mk _ (.inr p),continuous_quot_mk.comp continuous_inr⟩

lemma coneAttachment_base (f:C(L,A)) (x:L) :
    coneAttachmentCone f (0,x)=coneAttachmentOld f (f x) := Quot.sound (.base x)

lemma coneAttachment_apex (f:C(L,A)) (x y:L) :
    coneAttachmentCone f (1,x)=coneAttachmentCone f (1,y) := Quot.sound (.apex x y)

section Contracting
variable (f:C(L,A)) (c:L) (H:ContinuousMap.Homotopy (ContinuousMap.id L) (ContinuousMap.const L c))

noncomputable def coneAttachmentRetract : C(ConeAttachment f,A) where
  toFun:=Quot.lift (Sum.elim id (fun p:I×L=>f (H p))) (by
    intro a b h
    cases h with
    | base x => simp only [Sum.elim_inr,Sum.elim_inl,H.apply_zero,ContinuousMap.id_apply,id_eq]
    | apex x y => simp only [Sum.elim_inr,H.apply_one,ContinuousMap.const_apply])
  continuous_toFun:=continuous_quot_lift _ (continuous_sum_dom.mpr ⟨continuous_id,f.continuous.comp H.continuous⟩)

noncomputable def coneAttachmentMiddle : C(ConeAttachment f,ConeAttachment f) where
  toFun:=Quot.lift (Sum.elim (coneAttachmentOld f) (fun p:I×L=>coneAttachmentCone f (p.1,H p))) (by
    intro a b h
    cases h with
    | base x => simpa only [Sum.elim_inr,Sum.elim_inl,H.apply_zero,ContinuousMap.id_apply] using coneAttachment_base f x
    | apex x y => exact coneAttachment_apex f _ _)
  continuous_toFun:=continuous_quot_lift _ (continuous_sum_dom.mpr
    ⟨(coneAttachmentOld f).continuous,(coneAttachmentCone f).continuous.comp (continuous_fst.prodMk H.continuous)⟩)

noncomputable def coneAttachmentFirstFun (t:I) : ConeAttachment f→ ConeAttachment f :=
  Quot.lift (Sum.elim (coneAttachmentOld f)
    (fun p:I×L=>coneAttachmentCone f (p.1,H (min t p.1,p.2)))) (by
    intro a b h
    cases h with
    | base x =>
      simpa [min_eq_right (show (0:I)≤t from t.property.1)] using coneAttachment_base f x
    | apex x y => exact coneAttachment_apex f _ _)

noncomputable def coneAttachmentFirst :
    ContinuousMap.HomotopyRel (ContinuousMap.id (ConeAttachment f)) (coneAttachmentMiddle f c H)
      (Set.range (coneAttachmentOld f)) where
  toFun p:=coneAttachmentFirstFun f c H p.1 p.2
  continuous_toFun:=by
    apply isQuotientMap_quot_mk.continuous_lift_prod_right
    apply continuous_prod_sum_elim
    · exact (coneAttachmentOld f).continuous.comp continuous_snd
    · exact (coneAttachmentCone f).continuous.comp
        (continuous_snd.fst.prodMk (H.continuous.comp
          ((continuous_fst.min continuous_snd.fst).prodMk continuous_snd.snd)))
  map_zero_left:=by
    intro p
    induction p using Quot.inductionOn with
    | h p =>
      cases p with
      | inl a => rfl
      | inr p => simp [coneAttachmentFirstFun,coneAttachmentCone]
  map_one_left:=by
    intro p
    induction p using Quot.inductionOn with
    | h p =>
      cases p with
      | inl a => rfl
      | inr p => simp [coneAttachmentFirstFun,min_eq_right (show p.1≤(1:I) from p.1.property.2),coneAttachmentMiddle]
  prop' t p hp:=by
    obtain ⟨a,rfl⟩:=hp
    rfl

noncomputable def coneAttachmentSecondFun (t:I) : ConeAttachment f→ ConeAttachment f :=
  Quot.lift (Sum.elim (coneAttachmentOld f)
    (fun p:I×L=>coneAttachmentCone f ((σ t)*p.1,H p))) (by
    intro a b h
    cases h with
    | base x =>
      simpa only [Sum.elim_inr,Sum.elim_inl,mul_zero,H.apply_zero,ContinuousMap.id_apply] using coneAttachment_base f x
    | apex x y => simp only [Sum.elim_inr,H.apply_one,ContinuousMap.const_apply])

noncomputable def coneAttachmentSecond :
    ContinuousMap.HomotopyRel (coneAttachmentMiddle f c H)
      ((coneAttachmentOld f).comp (coneAttachmentRetract f c H))
      (Set.range (coneAttachmentOld f)) where
  toFun p:=coneAttachmentSecondFun f c H p.1 p.2
  continuous_toFun:=by
    apply isQuotientMap_quot_mk.continuous_lift_prod_right
    apply continuous_prod_sum_elim
    · exact (coneAttachmentOld f).continuous.comp continuous_snd
    · exact (coneAttachmentCone f).continuous.comp
        (((unitInterval.continuous_symm.comp continuous_fst).mul continuous_snd.fst).prodMk
          (H.continuous.comp continuous_snd))
  map_zero_left:=by
    intro p
    induction p using Quot.inductionOn with
    | h p =>
      cases p with
      | inl a => rfl
      | inr p => simp only [coneAttachmentSecondFun,Sum.elim_inr,unitInterval.symm_zero,one_mul];rfl
  map_one_left:=by
    intro p
    induction p using Quot.inductionOn with
    | h p =>
      cases p with
      | inl a => rfl
      | inr p =>
        simp only [coneAttachmentSecondFun,Sum.elim_inr,unitInterval.symm_one,zero_mul]
        exact coneAttachment_base f (H p)
  prop' t p hp:=by
    obtain ⟨a,rfl⟩:=hp
    rfl

noncomputable def coneAttachmentDeformation :
    ContinuousMap.HomotopyRel (ContinuousMap.id (ConeAttachment f))
      ((coneAttachmentOld f).comp (coneAttachmentRetract f c H))
      (Set.range (coneAttachmentOld f)) :=
  (coneAttachmentFirst f c H).trans (coneAttachmentSecond f c H)

end Contracting
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_SignDiagonal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
universe u
open _root_.Matrix

variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

noncomputable def signDiagonal (p:I→GeneratorPlacement V) (ε:I→Bool) : Matrix I I (Q.Zigzag K) :=
  Matrix.diagonal (fun i=>if ε i then -vertexId Q (p i).color else vertexId Q (p i).color)

omit [Fintype I] in
lemma signDiagonal_entries (p:I→GeneratorPlacement V) (ε:I→Bool) :
    ProjectiveEntries Q p p (signDiagonal Q (K:=K) p ε) := by
  constructor <;> intro i j <;> by_cases h:i=j
  · subst j
    simp only [signDiagonal,Matrix.diagonal_apply_eq]
    split_ifs <;> simp only [mul_neg,vertexId_mul_self]
  · simp only [signDiagonal,Matrix.diagonal_apply_ne _ h,mul_zero]
  · subst j
    simp only [signDiagonal,Matrix.diagonal_apply_eq]
    split_ifs <;> simp only [neg_mul,vertexId_mul_self]
  · simp only [signDiagonal,Matrix.diagonal_apply_ne _ h,zero_mul]

lemma signDiagonal_square (p:I→GeneratorPlacement V) (ε:I→Bool) :
    signDiagonal Q (K:=K) p ε*signDiagonal Q p ε=projectiveIdentity Q p := by
  rw [signDiagonal,Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp only [neg_mul_neg,vertexId_mul_self]

omit [Fintype J] [DecidableEq J] in
lemma signDiagonal_mul {p:I→GeneratorPlacement V} {q:J→GeneratorPlacement V}
    (ε:I→Bool) (M:Matrix I J (Q.Zigzag K)) (hM:ProjectiveEntries Q p q M) (i:I) (j:J) :
    (signDiagonal Q (K:=K) p ε * M) i j=if ε i then -M i j else M i j := by
  rw [signDiagonal,Matrix.diagonal_mul]
  split_ifs <;> simp only [neg_mul,hM.1]

omit [Fintype I] [DecidableEq I] in
lemma mul_signDiagonal {p:I→GeneratorPlacement V} {q:J→GeneratorPlacement V}
    (ε:J→Bool) (M:Matrix I J (Q.Zigzag K)) (hM:ProjectiveEntries Q p q M) (i:I) (j:J) :
    (M * signDiagonal Q (K:=K) q ε) i j=if ε j then -M i j else M i j := by
  rw [signDiagonal,Matrix.mul_diagonal]
  split_ifs <;> simp only [mul_neg,hM.2]

end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionFold
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_RowReflect
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_FusionWeightSplit
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionZeroLabel
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FiniteFusionEdge
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_SphericalFoldedMatrix
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

omit [LinearOrder S] in
theorem spherical_no_infinite_label (M:CoxeterMatrix S) (J:Set S) (hJ:IsSpherical M J)
    (i j:J) (hij:i≠j) : M i j≠0 := by
  intro hzero
  let C:=((Geometric.cartan M).submatrix ((↑):J → S) ((↑):J → S))
  let x:J → ℝ:=Pi.single i 1+Pi.single j 1
  have hne:x≠0 := by
    intro h
    have hi:=congrFun h i
    simp [x,hij] at hi
  have hpos:0 < x ⬝ᵥ (C *ᵥ x) := by
    simpa only [star_trivial] using (Geometric.spherical_cartan_posDef M J hJ).dotProduct_mulVec_pos hne
  have hval : (i:S)≠j := fun h=>hij (Subtype.ext h)
  have hval' : (j:S)≠i := Ne.symm hval
  have hct : x ⬝ᵥ (C *ᵥ x)=0 := by
    simp [x,C,Matrix.mulVec_add,add_dotProduct,dotProduct_add,Matrix.mulVec_single,
      Geometric.cartan,hval,hval',hzero,← M.symmetric i j]
  rw [hct] at hpos
  exact lt_irrefl _ hpos

theorem spherical_fusion_multiplicity_le_one (M:CoxeterMatrix S) (J:Set S)
    (hJ:IsSpherical M J) (i j:J) (L L':FusionLabel (fusionLabelSize M)) :
    (coxeterFusionEdge M (.inl i) (.inl j)).multiplicity (fusionLabelSize M) L L' ≤ 1 := by
  by_cases hij:i=j
  · subst j
    simp [coxeterFusionEdge_diag,FusionEdge.multiplicity]
  have hval : (i:S)≠j := fun h=>hij (Subtype.ext h)
  have hzero := spherical_no_infinite_label M J hJ i j hij
  simp only [coxeterFusionEdge,dite_eq_right hval,dite_eq_right hzero]
  split_ifs with h2 h3
  · simp [FusionEdge.multiplicity]
  · simp only [FusionEdge.multiplicity]
    split_ifs <;> omega
  · exact factorMultiplicity_le_one (fusionLabelSize M) _ L L'

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_UnfoldedMatrix
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

lemma unfoldedMatrix_cartan (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J) :
    cartan (unfoldedMatrix M J)=fusionUnfoldedCartan (fusionLabelSize M)
      (fun i j : J => coxeterFusionEdge M (.inl i) (.inl j)) := by
  funext α β
  by_cases he : α=β
  · subst β
    simp [cartan,fusionUnfoldedCartan,coxeterFusionEdge_diag,FusionEdge.multiplicity]
  · have hn := spherical_fusion_multiplicity_le_one M J hJ α.1 β.1 α.2 β.2
    have hp : (coxeterFusionEdge M (.inl α.1) (.inl β.1)).multiplicity
        (fusionLabelSize M) α.2 β.2=0 ∨
      (coxeterFusionEdge M (.inl α.1) (.inl β.1)).multiplicity
        (fusionLabelSize M) α.2 β.2=1 := by omega
    rcases hp with hzero | hone
    · have hm : unfoldedMatrix M J α β=2 := by rw [unfoldedMatrix_apply,ite_eq_right he,ite_eq_left hzero]
      have hc : cartan (unfoldedMatrix M J) α β=0 := by
        simp only [cartan,ite_eq_right he,hm]
        norm_num
      rw [hc]
      simp only [fusionUnfoldedCartan,Matrix.sub_apply,Matrix.diagonal_apply,ite_eq_right he,
        Matrix.of_apply,hzero,Nat.cast_zero,sub_zero]
    · have hm : unfoldedMatrix M J α β=3 := by simp only [unfoldedMatrix_apply,ite_eq_right he,hone] <;> norm_num
      have hc : cartan (unfoldedMatrix M J) α β= -1 := by
        simp only [cartan,ite_eq_right he,hm]
        norm_num [Real.cos_pi_div_three]
      rw [hc]
      simp only [fusionUnfoldedCartan,Matrix.sub_apply,Matrix.diagonal_apply,ite_eq_right he,
        Matrix.of_apply,hone,Nat.cast_one,zero_sub]

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

theorem unfolded_word_representation (M : CoxeterMatrix S) (J : Set S)
    (hJ : IsSpherical M J) (u : List J) (p : J → ℝ) :
    representation (unfoldedMatrix M J).toCoxeterSystem
      ((unfoldedMatrix M J).toCoxeterSystem.wordProd (fusionExpandedWord (fusionLabelSize M) u))
      (fusionFold (fusionLabelSize M) p)=
      fusionFold (fusionLabelSize M)
        (representation (restrictedMatrix M J).toCoxeterSystem
          ((restrictedMatrix M J).toCoxeterSystem.wordProd u) p) := by
  rw [← rowReflectWord_representation,← rowReflectWord_representation,unfoldedMatrix_cartan M J hJ]
  simpa only [foldedMatrix_cartan] using fusion_word_intertwining (fusionLabelSize M)
    (fun e => le_trans (by norm_num) (fusionLabelSize_ge_four M e))
    (fun i j : J => coxeterFusionEdge M (.inl i) (.inl j))
    (fun i => coxeterFusionEdge_diag M (.inl i)) u p

lemma unfolded_rootRow_fold (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J)
    (p : J → ℝ) (α : J × FusionLabel (fusionLabelSize M)) :
    rootRow (unfoldedMatrix M J) α (fusionFold (fusionLabelSize M) p)=
      fusionWeight (fusionLabelSize M) α.2*rootRow (restrictedMatrix M J) α.1 p := by
  rw [rootRow_apply,unfoldedMatrix_cartan M J hJ,fusion_intertwining (fusionLabelSize M)
    (fun e => le_trans (by norm_num) (fusionLabelSize_ge_four M e)),foldedMatrix_cartan]
  rfl

lemma unfolded_strict_chamber (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J) :
    ∃ p : J → ℝ,(∀ i,0 < rootRow (restrictedMatrix M J) i p) ∧
      ∀ α,0 < rootRow (unfoldedMatrix M J) α (fusionFold (fusionLabelSize M) p) := by
  let : Finite (restrictedMatrix M J).Group := restricted_finite M J hJ
  let : Fintype (restrictedMatrix M J).Group := Fintype.ofFinite _
  obtain ⟨p,hp⟩ := exists_strict_chamber (restrictedMatrix M J).toCoxeterSystem
  refine ⟨p,?_,?_⟩
  · intro i
    rw [rootRow_apply,hp]
    norm_num
  · intro α
    rw [unfolded_rootRow_fold M J hJ,rootRow_apply,hp,mul_one]
    exact fusionWeight_pos (fusionLabelSize M)
      (fun e => le_trans (by norm_num) (fusionLabelSize_ge_four M e)) α.2

theorem unfolded_left_ascent_iff (M : CoxeterMatrix S) (J : Set S)
    (hJ : IsSpherical M J) (u : List J) (α : J × FusionLabel (fusionLabelSize M)) :
    let c := (restrictedMatrix M J).toCoxeterSystem
    let d := (unfoldedMatrix M J).toCoxeterSystem
    d.length (d.simple α*d.wordProd (fusionExpandedWord (fusionLabelSize M) u))=
        d.length (d.wordProd (fusionExpandedWord (fusionLabelSize M) u))+1 ↔
      c.length (c.simple α.1*c.wordProd u)=c.length (c.wordProd u)+1 := by
  dsimp only
  obtain ⟨p,hp,hq⟩ := unfolded_strict_chamber M J hJ
  rw [← rootRow_pos_iff_left_ascent _ (fusionFold (fusionLabelSize M) p) hq,
    ← rootRow_pos_iff_left_ascent _ p hp,unfolded_word_representation M J hJ,
    unfolded_rootRow_fold M J hJ]
  exact mul_pos_iff_of_pos_left (fusionWeight_pos (fusionLabelSize M)
    (fun e => le_trans (by norm_num) (fusionLabelSize_ge_four M e)) α.2)

theorem unfolded_word_one (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J)
    (u : List J) (hu : (restrictedMatrix M J).toCoxeterSystem.wordProd u=1) :
    (unfoldedMatrix M J).toCoxeterSystem.wordProd (fusionExpandedWord (fusionLabelSize M) u)=1 := by
  obtain ⟨p,hp,hq⟩ := unfolded_strict_chamber M J hJ
  apply chamber_stabilizer (unfoldedMatrix M J).toCoxeterSystem
    (fusionFold (fusionLabelSize M) p) hq
  rw [unfolded_word_representation M J hJ,hu,map_one]
  rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_UnfoldedHom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.labelSplit_apply _root_.OAI.HarmonicArtin.labelSplit_symm_at _root_.OAI.HarmonicArtin.labelSplit_symm_rest
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

variable {S : Type*} [Fintype S] [LinearOrder S]

noncomputable def unfoldedHom (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J) :
    (restrictedMatrix M J).Group →* (unfoldedMatrix M J).Group :=
  (restrictedMatrix M J).toCoxeterSystem.lift
    ⟨fun i => (unfoldedMatrix M J).toCoxeterSystem.wordProd
      (fusionExpandedWord (fusionLabelSize M) [i]),by
      intro i j
      let c := (restrictedMatrix M J).toCoxeterSystem
      let d := (unfoldedMatrix M J).toCoxeterSystem
      have hword : c.wordProd ((List.replicate ((restrictedMatrix M J) i j) [i,j]).flatten)=1 := by
        rw [wordProd_flatten_replicate]
        simpa only [CoxeterSystem.wordProd_cons,CoxeterSystem.wordProd_nil,mul_one]
          using c.simple_mul_simple_pow i j
      have hu := unfolded_word_one M J hJ _ hword
      rw [fusionExpandedWord_flatten_replicate,wordProd_flatten_replicate] at hu
      have he : fusionExpandedWord (fusionLabelSize M) [i,j]=
          fusionExpandedWord (fusionLabelSize M) [i]++fusionExpandedWord (fusionLabelSize M) [j] :=
        fusionExpandedWord_append _ [i] [j]
      rw [he,d.wordProd_append] at hu
      exact hu⟩

@[simp] lemma unfoldedHom_simple (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J) (i : J) :
    unfoldedHom M J hJ ((restrictedMatrix M J).toCoxeterSystem.simple i)=
      (unfoldedMatrix M J).toCoxeterSystem.wordProd (fusionExpandedWord (fusionLabelSize M) [i]) :=
  (restrictedMatrix M J).toCoxeterSystem.lift_apply_simple _ i

lemma unfoldedHom_wordProd (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J) (u : List J) :
    unfoldedHom M J hJ ((restrictedMatrix M J).toCoxeterSystem.wordProd u)=
      (unfoldedMatrix M J).toCoxeterSystem.wordProd (fusionExpandedWord (fusionLabelSize M) u) := by
  induction u with
  | nil => simp [fusionExpandedWord]
  | cons i u ih =>
    rw [CoxeterSystem.wordProd_cons,map_mul,unfoldedHom_simple,ih]
    change _=(unfoldedMatrix M J).toCoxeterSystem.wordProd
      (fusionExpandedWord (fusionLabelSize M) ([i]++u))
    rw [fusionExpandedWord_append,CoxeterSystem.wordProd_append]

theorem unfolded_word_eq (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J)
    (u v : List J) (h : (restrictedMatrix M J).toCoxeterSystem.wordProd u=
      (restrictedMatrix M J).toCoxeterSystem.wordProd v) :
    (unfoldedMatrix M J).toCoxeterSystem.wordProd (fusionExpandedWord (fusionLabelSize M) u)=
      (unfoldedMatrix M J).toCoxeterSystem.wordProd (fusionExpandedWord (fusionLabelSize M) v) := by
  rw [← unfoldedHom_wordProd M J hJ,← unfoldedHom_wordProd M J hJ,h]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_UnfoldedColorOrthogonal
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

lemma unfolded_color_orthogonal (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J)
    (α β : J × FusionLabel (fusionLabelSize M)) (hcolor : α.1=β.1) (hne : α≠β) :
    cartan (unfoldedMatrix M J) α β=0 := by
  rw [unfoldedMatrix_cartan M J hJ]
  simp [fusionUnfoldedCartan,hne,hcolor,coxeterFusionEdge_diag,
    FusionEdge.multiplicity]

theorem unfolded_reducedWord (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J)
    (u : List J) (hu : (restrictedMatrix M J).toCoxeterSystem.IsReduced u) :
    (unfoldedMatrix M J).toCoxeterSystem.IsReduced (fusionExpandedWord (fusionLabelSize M) u) := by
  let c := (restrictedMatrix M J).toCoxeterSystem
  let d := (unfoldedMatrix M J).toCoxeterSystem
  obtain ⟨p,hp,hq⟩ := unfolded_strict_chamber M J hJ
  induction u with
  | nil => simp [fusionExpandedWord,CoxeterSystem.IsReduced]
  | cons i u ih =>
    have hru : c.IsReduced u := by simpa only [List.drop_succ_cons,List.drop_zero] using hu.drop 1
    have heu := ih hru
    let block := (Finset.univ : Finset (FusionLabel (fusionLabelSize M))).toList.map (fun L => (i,L))
    have hn : block.Nodup := List.Nodup.map (fun a b h => Prod.mk.inj h |>.2) (Finset.nodup_toList _)
    have hcolor : ∀ α∈block,α.1=i := by
      intro α hα
      obtain ⟨L,_,rfl⟩ := List.mem_map.mp hα
      rfl
    have horth : ∀ α∈block,∀ β∈block,α≠β → cartan (unfoldedMatrix M J) α β=0 := by
      intro α hα β hβ hne
      exact unfolded_color_orthogonal M J hJ α β ((hcolor α hα).trans (hcolor β hβ).symm) hne
    have ha : c.length (c.simple i*c.wordProd u)=c.length (c.wordProd u)+1 := by
      simpa only [CoxeterSystem.wordProd_cons,List.length_cons,← hru.eq] using hu.eq
    have has : ∀ α∈block,d.length (d.simple α*d.wordProd (fusionExpandedWord (fusionLabelSize M) u))=
        d.length (d.wordProd (fusionExpandedWord (fusionLabelSize M) u))+1 := by
      intro α hα
      apply (unfolded_left_ascent_iff M J hJ u α).mpr
      rw [hcolor α hα]
      exact ha
    have hb := orthogonal_ascent_block d (fusionFold (fusionLabelSize M) p) hq block hn horth
      (d.wordProd (fusionExpandedWord (fusionLabelSize M) u)) has
    change d.length (d.wordProd (block++fusionExpandedWord (fusionLabelSize M) u))=
      (block++fusionExpandedWord (fusionLabelSize M) u).length
    rw [d.wordProd_append,hb,List.length_append,heu.eq]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_UnfoldedInclusion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S]

abbrev unfoldedInclusion (M : CoxeterMatrix S) (J : Set S)
    (α : J × FusionLabel (fusionLabelSize M)) : FusionVertex (V:=S⊕Unit) (fusionLabelSize M) :=
  (Sum.inl α.1.val,α.2)

omit [Fintype S] in
lemma unfoldedInclusion_injective (M : CoxeterMatrix S) (J : Set S) :
    Function.Injective (unfoldedInclusion M J) := by
  intro α β h
  exact Prod.ext (Subtype.ext (Sum.inl.inj (Prod.mk.inj h).1)) (Prod.mk.inj h).2

variable (M : CoxeterMatrix S)

lemma fusionExpandedWord_map {E V T : Type*} [Fintype E] [DecidableEq E]
    (m : E → ℕ) (f : V → T) (u : List V) :
    fusionExpandedWord m (u.map f)=(fusionExpandedWord m u).map (fun α => (f α.1,α.2)) := by
  induction u with
  | nil => rfl
  | cons i u ih =>
    simp only [List.map_cons,fusionExpandedWord,List.flatMap_cons,List.map_append,List.map_map]
    congr 1

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_SphericalPair
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionColorRegion
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_DimensionNonneg
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_DimensionPosMultiplicityPos
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PacketWord
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Harmonic
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

omit [LinearOrder S] in
lemma framed_spherical_posDef (T:Set S) (hT:IsSpherical M T) :
    ((framedCartan M).submatrix ((↑):((Sum.inl : S→S⊕Unit) '' T)→S⊕Unit) Subtype.val).PosDef := by
  let e:((Sum.inl : S→S⊕Unit) '' T)→T:=fun i=>⟨(Classical.choose i.property),
    (Classical.choose_spec i.property).1⟩
  have he:∀ i:((Sum.inl : S→S⊕Unit) '' T),Sum.inl (e i:S)=(i:S⊕Unit):=
    fun i=>(Classical.choose_spec i.property).2
  have hi:Function.Injective e:=by
    intro i j hij
    apply Subtype.ext
    rw [←he i,←he j,hij]
  have h:((Geometric.cartan M).submatrix ((↑):T→S) Subtype.val).PosDef:=
    Geometric.spherical_cartan_posDef M T hT
  convert h.submatrix hi using 1
  all_goals try with_reducible_and_instances rfl
  ext i j
  change framedCartan M (i:S⊕Unit) (j:S⊕Unit)=Geometric.cartan M (e i) (e j)
  rw [←he i,←he j]
  rfl

noncomputable def sourceCosetRepresentative (P:Deligne M) : Artin M :=
  P.property.2.choose

omit [Fintype S] [LinearOrder S] in
lemma sourceCosetRepresentative_spec (P:Deligne M) :
    P.val.2=rightCoset M P.val.1 (sourceCosetRepresentative M P) :=
  P.property.2.choose_spec

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_RestrictedArtinHom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.unfoldedHom_simple
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Coset
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

noncomputable def sourceCoset (T:Set S) (hT:IsSpherical M T) (x:Artin M) : Deligne M :=
  ⟨(T,rightCoset M T x),hT,⟨x,rfl⟩⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_CosetBelow
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

abbrev SourceCosetBelow (B:Set S) (hB:IsSpherical M B) (x:Artin M) :=
  Set.Iic (sourceCoset M B hB x)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.StdSimplexCompat
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.closedSubmoduleNormedAddCommGroup _root_.OAI.isProbabilityMeasure_map_fst _root_.OAI.isProbabilityMeasure_map_measurableEquiv _root_.OAI.isProbabilityMeasure_map_snd _root_.OAI.isProbabilityMeasure_map_subtype_val _root_.OAI.vonNeumannToStarSubalgebraIsClosed
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_OrderWeights
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.orderWeightSupportLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open Simplicial CategoryTheory Opposite Convexity
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

lemma chainWeights_total {n:ℕ} (x:Fin (n+1)→o P) (z:StdSimplex ℝ (Fin (n+1))) :
    (chainWeights x z).sum (fun _ a=>a)=1 := by
  rw [chainWeights,← Finsupp.sum_finsetSum_index (by intros;rfl) (by intros;rfl)]
  simpa only [Finsupp.sum_single_index (h:=fun (_:P) (a:ℝ)=>a) (by rfl)] using z.total_of_fintype

noncomputable def orderWeightsOfChain {n:ℕ} (x:Fin (n+1)→o P) (z:StdSimplex ℝ (Fin (n+1))) : OrderWeights P where
  weights:=chainWeights x z
  nonneg:=chainWeights_nonneg x z
  total:=chainWeights_total x z
  chain:=by
    intro p hp q hq
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp (chainWeights_support x z hp)
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp (chainWeights_support x z hq)
    exact (le_total i j).imp (fun h=>x.monotone h) (fun h=>x.monotone h)

noncomputable def orderWeightsChart : (Σn:SimplexCategory,((nerve P).obj (op n)) × StdSimplex ℝ (Fin (n.len+1)))→OrderWeights P :=
  fun p=>orderWeightsOfChain (nerveChain p.2.1) p.2.2

noncomputable instance instTopologicalSpaceOrderWeights : TopologicalSpace (OrderWeights P) := by
  letI (n:SimplexCategory):TopologicalSpace ((nerve P).obj (op n)):=⊥
  exact TopologicalSpace.coinduced orderWeightsChart inferInstance

lemma orderWeightsChart_continuous {n:SimplexCategory} (x:(nerve P).obj (op n)) :
    Continuous (fun z:StdSimplex ℝ (Fin (n.len+1))=>orderWeightsOfChain (nerveChain x) z) := by
  let (n:SimplexCategory):TopologicalSpace ((nerve P).obj (op n)):=⊥
  have hc : Continuous (orderWeightsChart (P:=P)) := continuous_coinduced_rng
  exact hc.comp ((continuous_sigmaMk (i:=n)).comp (continuous_const.prodMk continuous_id))

lemma orderWeights_continuous_iff {Y:Type*} [TopologicalSpace Y] (f:OrderWeights P→Y) :
    Continuous f ↔ ∀(n:SimplexCategory) (x:(nerve P).obj (op n)),
      Continuous (fun z:StdSimplex ℝ (Fin (n.len+1))=>f (orderWeightsOfChain (nerveChain x) z)) := by
  let (n:SimplexCategory):TopologicalSpace ((nerve P).obj (op n)):=⊥
  let (n:SimplexCategory):DiscreteTopology ((nerve P).obj (op n)):=⟨rfl⟩
  rw [continuous_coinduced_dom,continuous_sigma_iff]
  constructor
  · intro h n x
    exact (h n).comp (continuous_const.prodMk continuous_id)
  · intro h n
    exact continuous_prod_of_discrete_left.mpr (h n)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_RealizeSimplex
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
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

noncomputable def coneSimplex (n : ℕ) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)) × I, Convexity.StdSimplex ℝ (Fin (n + 2))) where
  toFun point := Convexity.convexCombPair point.2.val (1 - point.2.val)
    point.2.property.1 (sub_nonneg.mpr point.2.property.2) (add_sub_cancel _ _)
    (Convexity.StdSimplex.single 0) (Convexity.StdSimplex.map Fin.succ point.1)
  continuous_toFun := by
    rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).continuous_iff]
    refine continuous_pi (fun index => ?_)
    simp only [Function.comp_apply, Convexity.StdSimplex.weights_convexCombPair,
      Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact ((continuous_subtype_val.comp continuous_snd).mul continuous_const).add
      ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul
        ((Convexity.StdSimplex.continuous_weights_apply ℝ index).comp
          ((Convexity.StdSimplex.continuous_map ℝ Fin.succ).comp continuous_fst)))

@[simp] lemma coneSimplex_zero (n : ℕ) (z : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    coneSimplex n (z, 0) = Convexity.StdSimplex.map Fin.succ z := by
  ext i
  simp [coneSimplex]

@[simp] lemma coneSimplex_one (n : ℕ) (z : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    coneSimplex n (z, 1) = Convexity.StdSimplex.single 0 := by
  ext i
  simp [coneSimplex]

variable (P : Type u) [Preorder P] [OrderBot P]

noncomputable def nerveConeSimplex {n : SimplexCategory} (x : (nerve P).obj (op n)) :
    C(Convexity.StdSimplex ℝ (Fin (n.len + 1)), C(I, |nerve P|)) :=
  ((realizeSimplex (nerve P) (prependNerve P x)).comp (coneSimplex n.len)).curry

noncomputable def nerveBotPoint : |nerve P| :=
  realizeSimplex (nerve P) (ComposableArrows.mk₀ (⊥ : P)) (Convexity.StdSimplex.single 0)

@[simp] lemma nerveConeSimplex_one {n : SimplexCategory}
    (x : (nerve P).obj (op n)) (z : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    nerveConeSimplex P x z 1 = nerveBotPoint P := by
  change realizeSimplex (nerve P) (prependNerve P x) (coneSimplex n.len (z, 1)) = _
  rw [coneSimplex_one]
  let f : ⦋0⦌ ⟶ ⦋n.len + 1⦌ := SimplexCategory.mkHom (OrderHom.const _ 0)
  have hf : (nerve P).map f.op (prependNerve P x) = ComposableArrows.mk₀ (⊥ : P) := by
    apply nerve.ext_of_isThin
    rfl
  have h := realizeSimplex_natural (nerve P) f (prependNerve P x) (Convexity.StdSimplex.single 0)
  rw [hf, Convexity.StdSimplex.map_single] at h
  exact h.symm

section TopCone
variable (Q : Type u) [Preorder Q] [OrderTop Q]

noncomputable def topConeSimplex (n : ℕ) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)) × I, Convexity.StdSimplex ℝ (Fin (n + 2))) where
  toFun point := Convexity.convexCombPair point.2.val (1 - point.2.val)
    point.2.property.1 (sub_nonneg.mpr point.2.property.2) (add_sub_cancel _ _)
    (Convexity.StdSimplex.single (Fin.last (n + 1)))
    (Convexity.StdSimplex.map Fin.castSucc point.1)
  continuous_toFun := by
    rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).continuous_iff]
    refine continuous_pi (fun index => ?_)
    simp only [Function.comp_apply, Convexity.StdSimplex.weights_convexCombPair,
      Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact ((continuous_subtype_val.comp continuous_snd).mul continuous_const).add
      ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul
        ((Convexity.StdSimplex.continuous_weights_apply ℝ index).comp
          ((Convexity.StdSimplex.continuous_map ℝ Fin.castSucc).comp continuous_fst)))

@[simp] lemma topConeSimplex_zero (n : ℕ) (z : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    topConeSimplex n (z, 0) = Convexity.StdSimplex.map Fin.castSucc z := by
  ext i
  simp [topConeSimplex]

@[simp] lemma topConeSimplex_one (n : ℕ) (z : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    topConeSimplex n (z, 1) = Convexity.StdSimplex.single (Fin.last (n + 1)) := by
  ext i
  simp [topConeSimplex]

noncomputable def nerveTopConeSimplex {n : SimplexCategory} (x : (nerve Q).obj (op n)) :
    C(Convexity.StdSimplex ℝ (Fin (n.len + 1)), C(I, |nerve Q|)) :=
  ((realizeSimplex (nerve Q) (appendNerve Q x)).comp (topConeSimplex n.len)).curry

noncomputable def nerveTopPoint : |nerve Q| :=
  realizeSimplex (nerve Q) (ComposableArrows.mk₀ (⊤ : Q)) (Convexity.StdSimplex.single 0)

@[simp] lemma nerveTopConeSimplex_one {n : SimplexCategory}
    (x : (nerve Q).obj (op n)) (z : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    nerveTopConeSimplex Q x z 1 = nerveTopPoint Q := by
  change realizeSimplex (nerve Q) (appendNerve Q x) (topConeSimplex n.len (z, 1)) = _
  rw [topConeSimplex_one]
  let f : ⦋0⦌ ⟶ ⦋n.len + 1⦌ := SimplexCategory.mkHom (OrderHom.const _ (Fin.last (n.len + 1)))
  have hf : (nerve Q).map f.op (appendNerve Q x) = ComposableArrows.mk₀ (⊤ : Q) := by
    apply nerve.ext_of_isThin
    funext i
    change (Fin.snoc (α := fun _ : Fin (n.len + 2) => Q) x.obj ⊤)
      (Fin.last (n.len + 1)) = ⊤
    exact Fin.snoc_last _ _
  have h := realizeSimplex_natural (nerve Q) f (appendNerve Q x) (Convexity.StdSimplex.single 0)
  rw [hf, Convexity.StdSimplex.map_single] at h
  exact h.symm

end TopCone
end HarmonicArtin

end TopologyDependencies

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightDim
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped BigOperators
open Simplicial CategoryTheory Opposite Convexity

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

lemma orderWeightsOfChain_canonical (w:OrderWeights P) :
    orderWeightsOfChain (weightChain w) (weightSimplex w)=w := by
  apply OrderWeights.ext
  ext p
  by_cases hp:p∈w.weights.support
  · obtain ⟨i,hi⟩:∃i,weightChain w i=p:=by
      exact ⟨(weightEnum w).symm ⟨p,hp⟩,congrArg Subtype.val ((weightEnum w).apply_symm_apply _)⟩
    rw [← hi]
    exact chainWeights_injective_apply _ (weightChain_injective w) _ i
  · change chainWeights _ _ p=w.weights p
    rw [Finsupp.notMem_support_iff.mp hp,chainWeights_apply]
    apply Finset.sum_eq_zero
    intro i _
    have hn:weightChain w i≠p:=by
      intro he
      exact hp (he ▸ (weightEnum w i).property)
    simp [hn]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PrismPrefix
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
attribute [-simp] _root_.OAI.HarmonicArtin.coneSimplex_one _root_.OAI.HarmonicArtin.coneSimplex_zero _root_.OAI.HarmonicArtin.nerveConeSimplex_one _root_.OAI.HarmonicArtin.nerveTopConeSimplex_one _root_.OAI.HarmonicArtin.topConeSimplex_one _root_.OAI.HarmonicArtin.topConeSimplex_zero
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PrismFlag
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PredAboveSuccSucc
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_NervePrismPatch
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_NervePrismValue
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PrismSimplexZero
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_NerveOrderMap
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_NerveOrderRetractionEquiv
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

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_OrderMappingCylinder
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open Simplicial

universe u
variable {P Q:Type u} [PartialOrder P] [PartialOrder Q]

namespace OrderMappingCylinder
variable (f:P→oQ)

noncomputable def nerveEquiv : ContinuousMap.HomotopyEquiv
    |CategoryTheory.nerve (OrderMappingCylinder f)| |CategoryTheory.nerve Q| :=
  nerveOrderRetractionEquiv (project f) (right f) (project_right f) (le_right_project f)

end OrderMappingCylinder
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightMap
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped BigOperators
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable
universe u v
variable {P:Type u} {Q:Type v} [PartialOrder P] [PartialOrder Q]

lemma weightMap_chain {n:ℕ} (f:P→oQ) (x:Fin (n+1)→o P)
    (z:Convexity.StdSimplex ℝ (Fin (n+1))) :
    weightMap f (orderWeightsOfChain x z)=orderWeightsOfChain (f.comp x) z := by
  apply OrderWeights.ext
  change Finsupp.mapDomain f (chainWeights x z)=chainWeights (f.comp x) z
  simp only [chainWeights,Finsupp.mapDomain_finsetSum,Finsupp.mapDomain_single]
  rfl

lemma chainWeightsChart_continuous {n:ℕ} (x:Fin (n+1)→oP) :
    Continuous (orderWeightsOfChain x) :=
  orderWeightsChart_continuous (nerveOfChain x)

lemma weightMap_continuous (f:P→o Q) : Continuous (weightMap f) := by
  rw [orderWeights_continuous_iff]
  intro n x
  simp_rw [weightMap_chain]
  exact chainWeightsChart_continuous _

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FiniteChainEnum
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped BigOperators
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

lemma carrierSimplex_reconstruct (C:Finset P) (hC:IsChain (·≤·) (↑C:Set P)) (hne:C.Nonempty)
    (w:OrderWeights P) (hw:w.weights.support⊆C) :
    orderWeightsOfChain (finiteChainOrder C hC hne) (carrierSimplex C hC hne w hw)=w := by
  apply OrderWeights.ext
  ext p
  by_cases hp:p∈C
  · let i:=(finiteChainEnum C hC hne).symm ⟨p,hp⟩
    have hi:finiteChainOrder C hC hne i=p:=
      congrArg Subtype.val ((finiteChainEnum C hC hne).apply_symm_apply ⟨p,hp⟩)
    change chainWeights _ _ p=w.weights p
    rw [← hi,chainWeights_injective_apply _ (finiteChainOrder_injective _ _ _)]
    rfl
  · have hpw:p∉w.weights.support:=fun h=>hp (hw h)
    have hpz:p∉(chainWeights (finiteChainOrder C hC hne) (carrierSimplex C hC hne w hw)).support:=by
      intro ht
      obtain ⟨i,_,hi⟩:=Finset.mem_image.mp (chainWeights_support _ _ ht)
      exact hp (hi ▸ (finiteChainEnum C hC hne i).property)
    exact (Finsupp.notMem_support_iff.mp hpz).trans (Finsupp.notMem_support_iff.mp hpw).symm

lemma continuous_of_finite_chain_carrier {Z:Type*} [TopologicalSpace Z]
    (f:Z→OrderWeights P) (C:Finset P) (hC:IsChain (·≤·) (↑C:Set P)) (hne:C.Nonempty)
    (hf:∀z,(f z).weights.support⊆C) (hc:∀p,Continuous (fun z=>(f z).weights p)) :
    Continuous f := by
  have hs:Continuous (fun z=>carrierSimplex C hC hne (f z) (hf z)):=by
    rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (C.card-1+1))).continuous_iff]
    change Continuous (fun z index=>(f z).weights (finiteChainOrder C hC hne index))
    exact continuous_pi (fun i=>hc _)
  have he:(fun z=>orderWeightsOfChain (finiteChainOrder C hC hne) (carrierSimplex C hC hne (f z) (hf z)))=f:=by
    funext z
    exact carrierSimplex_reconstruct C hC hne (f z) (hf z)
  rw [←he]
  exact (chainWeightsChart_continuous _).comp hs

noncomputable instance finiteLinearWeightsCompact (R:Type*) [LinearOrder R] [Fintype R] :
    CompactSpace (OrderWeights R) := by
  classical
  by_cases h:Nonempty R
  · let := h
    let C:Finset R:=Finset.univ
    have hc:IsChain (·≤·) (↑C:Set R):=fun a _ b _ _=>le_total a b
    have hn:C.Nonempty:=Finset.univ_nonempty
    have hs:Function.Surjective (orderWeightsOfChain (finiteChainOrder C hc hn)):=by
      intro w
      exact ⟨carrierSimplex C hc hn w (Finset.subset_univ _),carrierSimplex_reconstruct C hc hn w _⟩
    exact isCompact_univ_iff.mp (by
      rw [←Set.range_eq_univ.mpr hs]
      exact isCompact_range (chainWeightsChart_continuous _))
  · have : IsEmpty R := not_nonempty_iff.mp h
    have : IsEmpty (OrderWeights R) := ⟨fun weights=>by
      obtain ⟨point,_⟩:=weights.support_nonempty
      exact isEmptyElim point⟩
    infer_instance

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightCarrier
attribute [-instance] _root_.OAI.HarmonicArtin.finiteLinearWeightsCompact _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.orderWeightSupportLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped BigOperators
open Simplicial CategoryTheory Opposite Convexity

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

lemma weightEval_continuous (p:P) : Continuous (fun w:OrderWeights P=>w.weights p) := by
  rw [orderWeights_continuous_iff]
  intro n x
  change Continuous (fun z:StdSimplex ℝ (Fin (n.len+1))=>chainWeights (nerveChain x) z p)
  simp_rw [chainWeights_apply]
  apply continuous_finsetSum
  intro i _
  by_cases h:nerveChain x i=p
  · simp only [h,ite_eq_left]
    exact StdSimplex.continuous_weights_apply ℝ i
  · simp only [h]
    exact continuous_const

noncomputable instance instT2SpaceOrderWeights : T2Space (OrderWeights P) :=
  T2Space.of_injective_continuous
    (f:=fun w:OrderWeights P=>fun p=>w.weights p)
    (by intro x y h;apply OrderWeights.ext;exact DFunLike.ext' h)
    (continuous_pi weightEval_continuous)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_ConeWeights
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped BigOperators unitInterval
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable
universe u v
variable {P:Type u} {Q:Type v} [PartialOrder P] [PartialOrder Q]

lemma orderWeights_prod_continuous {Z Y:Type*} [TopologicalSpace Z] [LocallyCompactSpace Z]
    [TopologicalSpace Y] (f:Z×OrderWeights P→Y)
    (hc:∀(n:SimplexCategory) (x:(nerve P).obj (op n)),
      Continuous (fun p:Z×Convexity.StdSimplex ℝ (Fin (n.len+1))=>f (p.1,orderWeightsOfChain (nerveChain x) p.2))) :
    Continuous f := by
  have ht (w:OrderWeights P):Continuous (fun t=>f (t,w)):=by
    have h:Continuous (fun t=>f (t,orderWeightsOfChain (weightChain w) (weightSimplex w))):=
      (hc ⦋weightDim w⦌ (nerveOfChain (weightChain w))).comp (continuous_id.prodMk continuous_const)
    simpa only [orderWeightsOfChain_canonical] using h
  let F:OrderWeights P→C(Z,Y):=fun w=>⟨fun t=>f (t,w),ht w⟩
  have hF:Continuous F:=by
    rw [orderWeights_continuous_iff]
    intro n x
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (hc n x).comp continuous_swap
  exact (ContinuousMap.continuous_uncurry_of_continuous ⟨F,hF⟩).comp continuous_swap

lemma coneWeights_continuous (f:Q→oP) (v:P) (hv:∀q,f q≤v ∨ v≤f q) :
    Continuous (fun p:I×OrderWeights Q=>coneWeights f v hv p.1 p.2) := by
  apply orderWeights_prod_continuous
  intro n x
  let C:Finset P:=insert v (Finset.univ.image (f.comp (nerveChain x)))
  have hC:IsChain (·≤·) (↑C:Set P):=by
    intro a ha b hb _
    change a∈insert v (Finset.univ.image (f.comp (nerveChain x))) at ha
    change b∈insert v (Finset.univ.image (f.comp (nerveChain x))) at hb
    rcases Finset.mem_insert.mp ha with hpa|hpa
    · subst a
      rcases Finset.mem_insert.mp hb with hpb|hpb
      · subst b;exact Or.inl le_rfl
      · obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hpb
        exact (hv (nerveChain x j)).symm
    · rcases Finset.mem_insert.mp hb with hpb|hpb
      · subst b
        obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hpa
        exact hv (nerveChain x i)
      · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hpa
        obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hpb
        exact (le_total i j).imp (fun h=>(f.comp (nerveChain x)).monotone h) (fun h=>(f.comp (nerveChain x)).monotone h)

  apply continuous_of_finite_chain_carrier _ C hC (Finset.insert_nonempty _ _)
  · intro p a ha
    have hs:=coneWeights_support f v hv p.1 (orderWeightsOfChain (nerveChain x) p.2) ha
    rcases Finset.mem_insert.mp hs with rfl|hs
    · exact Finset.mem_insert_self _ _
    · obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp hs
      obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp (chainWeights_support _ _ hq)
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  · intro q
    simp_rw [coneWeights_apply,weightMap_chain]
    apply Continuous.add
    · exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        ((weightEval_continuous q).comp ((chainWeightsChart_continuous _).comp continuous_snd))
    · split_ifs
      · exact continuous_subtype_val.comp continuous_fst
      · exact continuous_const

noncomputable def coneWeightsContinuous (f:Q→oP) (v:P) (hv:∀q,f q≤v ∨ v≤f q) :
    C(I×OrderWeights Q,OrderWeights P) :=⟨_,coneWeights_continuous f v hv⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightHomeomorph
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

universe u v
variable {P:Type u} {Q:Type v} [PartialOrder P] [PartialOrder Q]

noncomputable def weightHomeomorph (e:P≃oQ) : OrderWeights P≃ₜOrderWeights Q where
  toFun:=weightMap (e : P→oQ)
  invFun:=weightMap (e.symm : Q→oP)
  left_inv w:=by
    rw [weightMap_comp]
    have he:(e.symm : Q→oP).comp (e : P→oQ)=OrderHom.id:=by ext p;exact e.symm_apply_apply p
    rw [he,weightMap_id]
  right_inv w:=by
    rw [weightMap_comp]
    have he:(e : P→oQ).comp (e.symm : Q→oP)=OrderHom.id:=by ext p;exact e.apply_symm_apply p
    rw [he,weightMap_id]
  continuous_toFun:=weightMap_continuous _
  continuous_invFun:=weightMap_continuous _

variable (r:P→P→Prop) (c:P)

structure WeightContractionPiece where
  carrier:Set P
  root_mem:c∈carrier
  down:∀{x y},x∈carrier → r y x → y∈carrier
  hom:ContinuousMap.Homotopy (ContinuousMap.id (OrderWeights carrier))
    (ContinuousMap.const _ (weightVertex ⟨c,root_mem⟩))

namespace WeightContractionPiece
variable {r c}
noncomputable def inclusion (a:WeightContractionPiece r c) :=weightInclusion a.carrier

def Extends (a b:WeightContractionPiece r c) : Prop :=
  ∃h:a.carrier⊆b.carrier,∀t:I,∀w:OrderWeights a.carrier,
    weightMap a.inclusion (a.hom (t,w))=
      weightMap b.inclusion (b.hom (t,weightMap (weightSubset _ _ h) w))

lemma extends_refl (a:WeightContractionPiece r c) : a.Extends a := by
  refine ⟨Set.Subset.rfl,?_⟩
  intro t w
  rw [weightSubset_self,weightMap_id]

lemma extends_compare {a b:WeightContractionPiece r c} (h:a.Extends b)
    (w:OrderWeights a.carrier) (z:OrderWeights b.carrier)
    (he:weightMap a.inclusion w=weightMap b.inclusion z) (t:I) :
    weightMap a.inclusion (a.hom (t,w))=weightMap b.inclusion (b.hom (t,z)) := by
  obtain ⟨h,hh⟩:=h
  rw [hh]
  have hz:weightMap (weightSubset _ _ h) w=z:=by
    apply weightMap_injective b.inclusion Subtype.val_injective
    rw [weightMap_comp]
    exact he
  rw [hz]

end WeightContractionPiece
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_EarlyDelay
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPreorderLiftedCell
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval
open Topology

attribute [local instance] Classical.propDecidable
universe u v
variable {X:Type u} {Y:Type v} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]

noncomputable def earlyDelayMap (δ:C(X,I)) : C(I×X,EarlyDelay δ) where
  toFun := fun p => ⟨(p.1*δ p.2,p.2),mul_le_of_le_one_left (by exact bot_le) (by exact le_top)⟩
  continuous_toFun:=Continuous.subtype_mk
    ((continuous_fst.mul (δ.continuous.comp continuous_snd)).prodMk continuous_snd) _

omit [T2Space X] in
lemma earlyDelayMap_surjective (δ:C(X,I)) : Function.Surjective (earlyDelayMap δ) := by
  rintro ⟨⟨t,x⟩,ht⟩
  by_cases hd:δ x=0
  · have h:t=0:=le_antisymm (hd ▸ ht) t.property.1
    subst t
    refine ⟨(0,x),?_⟩
    apply Subtype.ext
    simp [earlyDelayMap]
  · have hdv:(δ x).val≠0:=by intro he;apply hd;exact Subtype.ext he
    have hp:0<(δ x).val:=lt_of_le_of_ne (δ x).property.1 (Ne.symm hdv)
    let s:I:=⟨t.val/(δ x).val,div_nonneg t.property.1 hp.le,(div_le_one hp).mpr ht⟩
    refine ⟨(s,x),?_⟩
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact div_mul_cancel₀ _ hdv
    · rfl

lemma earlyDelayMap_quotient (δ:C(X,I)) : IsQuotientMap (earlyDelayMap δ) := by
  have hp:IsProperMap (earlyDelayMap δ):=
    isProperMap_of_comp_of_t2 (earlyDelayMap δ).continuous
      (continuous_snd.comp continuous_subtype_val) isProperMap_snd_of_compactSpace
  exact hp.isClosedMap.isQuotientMap (earlyDelayMap δ).continuous (earlyDelayMap_surjective δ)

noncomputable def earlyDelayValue (δ:C(X,I)) (D:C(I×X,Y)) (p:EarlyDelay δ) : Y :=
  D ((earlyDelayMap_surjective δ p).choose)

omit [T2Space X] in
lemma earlyDelayValue_map (δ:C(X,I)) (D:C(I×X,Y))
    (hD:∀x,δ x=0→∀t:I,D (t,x)=D (0,x)) (p:I×X) :
    earlyDelayValue δ D (earlyDelayMap δ p)=D p := by
  let q:=(earlyDelayMap_surjective δ (earlyDelayMap δ p)).choose
  have he:earlyDelayMap δ q=earlyDelayMap δ p:=
    (earlyDelayMap_surjective δ (earlyDelayMap δ p)).choose_spec
  have hx:q.2=p.2:=congrArg (fun z:EarlyDelay δ=>z.val.2) he
  have ht:q.1*δ q.2=p.1*δ p.2:=congrArg (fun z:EarlyDelay δ=>z.val.1) he
  change D q=D p
  change D (q.1,q.2)=D (p.1,p.2)
  rw [hx]
  by_cases hd:δ p.2=0
  · exact (hD _ hd q.1).trans (hD _ hd p.1).symm
  · have hdv:(δ p.2).val≠0:=by intro he;apply hd;exact Subtype.ext he
    have heq:q.1=p.1:=by
      apply Subtype.ext
      have h:=congrArg Subtype.val ht
      change q.1.val*(δ q.2).val=p.1.val*(δ p.2).val at h
      rw [hx] at h
      exact mul_right_cancel₀ hdv h
    rw [heq]

noncomputable def earlyDelayContinuous (δ:C(X,I)) (D:C(I×X,Y))
    (hD:∀x,δ x=0→∀t:I,D (t,x)=D (0,x)) : C(EarlyDelay δ,Y) where
  toFun:=earlyDelayValue δ D
  continuous_toFun:=by
    apply (earlyDelayMap_quotient δ).continuous_iff.mpr
    have he:(earlyDelayValue δ D) ∘ earlyDelayMap δ=D:=by
      funext p
      exact earlyDelayValue_map δ D hD p
    rw [he]
    exact D.continuous

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_LateDelay
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.orderWeightSupportLinearOrder
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval
open Topology

attribute [local instance] Classical.propDecidable
universe u v
variable {A:Type u} {X:Type v} [TopologicalSpace A] [TopologicalSpace X] [T2Space X]

variable (i:C(A,X)) (r:C(X,A)) (hr:∀a,r (i a)=a)
  (D:ContinuousMap.HomotopyRel (ContinuousMap.id X) (i.comp r) (Set.range i))
  (δ:C(X,I)) (hd:∀x,δ x<1) (hz:∀x,δ x=0↔x∈Set.range i)
  (c:A) (H:ContinuousMap.Homotopy (ContinuousMap.id A) (ContinuousMap.const A c))

noncomputable def extensionEarly : C(EarlyDelay δ,X) :=
  earlyDelayContinuous δ D.toHomotopy.toContinuousMap (extension_stationary i r D δ hz)

lemma extension_agree (x:X) :
    extensionEarly i r D δ hz ⟨(δ x,x),le_rfl⟩=
      extensionLate i r δ hd c H ⟨(δ x,x),le_rfl⟩ := by
  have he:earlyDelayMap δ (1,x)=⟨(δ x,x),le_rfl⟩:=by apply Subtype.ext;simp [earlyDelayMap]
  change earlyDelayValue δ D.toHomotopy.toContinuousMap _=_
  rw [←he,earlyDelayValue_map δ D.toHomotopy.toContinuousMap (extension_stationary i r D δ hz)]
  change D (1,x)=i (H (lateDelayTime δ hd ⟨(δ x,x),le_rfl⟩,r x))
  have ht:lateDelayTime δ hd ⟨(δ x,x),le_rfl⟩=0:=by apply Subtype.ext;simp [lateDelayTime]
  rw [ht,D.apply_one,H.apply_zero]
  rfl

noncomputable def extensionValue (p:I×X) : X :=
  if h:p.1≤δ p.2 then extensionEarly i r D δ hz ⟨p,h⟩
  else extensionLate i r δ hd c H ⟨p,le_of_not_ge h⟩

lemma extensionValue_early (p:EarlyDelay δ) :
    extensionValue i r D δ hd hz c H p.val=extensionEarly i r D δ hz p := by
  simp only [extensionValue,dite_eq_left p.property]

lemma extensionValue_late (p:LateDelay δ) :
    extensionValue i r D δ hd hz c H p.val=extensionLate i r δ hd c H p := by
  dsimp only [extensionValue]
  split_ifs with h
  · have he:p.val.1=δ p.val.2:=le_antisymm h p.property
    obtain ⟨⟨t,x⟩,hp⟩:=p
    change t=δ x at he
    subst t
    exact extension_agree i r D δ hd hz c H x
  · rfl

lemma extensionValue_continuous : Continuous (extensionValue i r D δ hd hz c H) := by
  let B:Bool→Set (I×X):=fun b=>if b then {p | p.1≤δ p.2} else {p | δ p.2≤p.1}
  apply (locallyFinite_of_finite B).continuous
  · apply Set.iUnion_eq_univ_iff.mpr
    intro p
    rcases le_total p.1 (δ p.2) with h|h
    · exact ⟨true,h⟩
    · exact ⟨false,h⟩
  · intro b
    cases b
    · exact isClosed_le (δ.continuous.comp continuous_snd) continuous_fst
    · exact isClosed_le continuous_fst (δ.continuous.comp continuous_snd)
  · intro b
    rw [continuousOn_iff_continuous_domRestrict]
    cases b
    · exact (extensionLate i r δ hd c H).continuous.congr (fun p=>(extensionValue_late i r D δ hd hz c H p).symm)
    · exact (extensionEarly i r D δ hz).continuous.congr (fun p=>(extensionValue_early i r D δ hd hz c H p).symm)

noncomputable def extendContraction :
    ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.const X (i c)) where
  toFun:=extensionValue i r D δ hd hz c H
  continuous_toFun:=extensionValue_continuous i r D δ hd hz c H
  map_zero_left:=by
    intro x
    rw [show (0,x)=(earlyDelayMap δ (0,x)).val by simp [earlyDelayMap],extensionValue_early]
    exact (earlyDelayValue_map δ D.toHomotopy.toContinuousMap (extension_stationary i r D δ hz) (0,x)).trans (D.apply_zero x)
  map_one_left:=by
    intro x
    rw [show (1,x)=(⟨(1,x),le_of_lt (hd x)⟩:LateDelay δ).val from rfl,extensionValue_late]
    change i (H (lateDelayTime δ hd ⟨(1,x),le_of_lt (hd x)⟩,r x))=i c
    have ht:lateDelayTime δ hd ⟨(1,x),le_of_lt (hd x)⟩=1:=by
      apply Subtype.ext
      exact div_self (ne_of_gt (sub_pos.mpr (hd x)))
    rw [ht,H.apply_one]
    rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightOld
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped BigOperators unitInterval

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

noncomputable def weightOldMap (v:P) : C(OrderWeights (WeightOld v),OrderWeights P) :=
  ⟨weightMap (weightOldIncl v),weightMap_continuous _⟩
noncomputable def weightLinkMap (v:P) : C(OrderWeights (WeightLink v),OrderWeights (WeightOld v)) :=
  ⟨weightMap (weightLinkOld v),weightMap_continuous _⟩
noncomputable def weightConeMap (v:P) : C(I×OrderWeights (WeightLink v),OrderWeights P) :=
  coneWeightsContinuous (weightLinkIncl v) v (fun p=>p.property.2)

lemma weightOldMap_at (v:P) (w:OrderWeights (WeightOld v)) : (weightOldMap v w).weights v=0 := by
  apply weightMap_zero_of_not_range
  rintro ⟨p,hp⟩
  exact p.property hp

lemma weightConeMap_at (v:P) (p:I×OrderWeights (WeightLink v)) :
    (weightConeMap v p).weights v=p.1.val := by
  rw [show weightConeMap v p=coneWeights (weightLinkIncl v) v (fun p=>p.property.2) p.1 p.2 from rfl,
    coneWeights_apply]
  have hz:(weightMap (weightLinkIncl v) p.2).weights v=0:=by
    apply weightMap_zero_of_not_range
    rintro ⟨q,hq⟩
    exact q.property.1 hq
  rw [hz,ite_eq_left rfl,mul_zero,zero_add]

lemma weightConeMap_zero (v:P) (w:OrderWeights (WeightLink v)) :
    weightConeMap v (0,w)=weightOldMap v (weightLinkMap v w) := by
  rw [show weightConeMap v (0,w)=coneWeights (weightLinkIncl v) v (fun p=>p.property.2) 0 w from rfl,
    coneWeights_zero]
  exact (weightMap_comp (weightLinkOld v) (weightOldIncl v) w).symm

lemma weightConeMap_one (v:P) (w:OrderWeights (WeightLink v)) :
    weightConeMap v (1,w)=weightVertex v := coneWeights_one_vertex (weightLinkIncl v) v (fun q=>q.property.2) w

lemma weightConeMap_eq_cone {v:P} {t s:I} {w z:OrderWeights (WeightLink v)}
    (h:weightConeMap v (t,w)=weightConeMap v (s,z)) : t=s ∧ (t=1 ∨ w=z) := by
  have ht:t=s:=Subtype.ext (by simpa only [weightConeMap_at] using congrArg (fun a:OrderWeights P=>a.weights v) h)
  subst s
  refine ⟨rfl,?_⟩
  by_cases he:t=1
  · exact Or.inl he
  right
  apply OrderWeights.ext
  ext p
  have hs:=congrArg (fun a:OrderWeights P=>a.weights p.val) h
  change (coneWeights (weightLinkIncl v) v (fun q=>q.property.2) t w).weights p.val=
    (coneWeights (weightLinkIncl v) v (fun q=>q.property.2) t z).weights p.val at hs
  simp only [coneWeights_apply,ite_eq_right (Ne.symm p.property.1),add_zero] at hs
  have hw:(weightMap (weightLinkIncl v) w).weights p.val=w.weights p:=
    weightMap_apply_embedding (weightLinkIncl v) Subtype.val_injective w p
  have hz:(weightMap (weightLinkIncl v) z).weights p.val=z.weights p:=
    weightMap_apply_embedding (weightLinkIncl v) Subtype.val_injective z p
  rw [hw,hz] at hs
  exact mul_left_cancel₀ (sub_ne_zero.mpr (fun h=>he (Subtype.ext h.symm))) hs

lemma weightOld_surjective_zero {v:P} (w:OrderWeights P) (hv:w.weights v=0) :
    ∃z:OrderWeights (WeightOld v),weightOldMap v z=w := by
  have hs:∀p∈w.weights.support,p≠v:=by
    intro p hp he;subst p
    exact Finsupp.mem_support_iff.mp hp hv
  exact ⟨weightRestrict {p | p≠v} w hs,weightRestrict_map _ w hs⟩

lemma weightDelete_reconstruct {v:P} (w:OrderWeights P) (ht:w.weights v<1) (hp:0<w.weights v) :
    weightConeMap v (weightTime v w,weightRestrict {p | p≠v ∧ (p≤v ∨ v≤p)}
      (weightDelete v w ht) (weightDelete_link w ht hp))=w := by
  apply OrderWeights.ext
  ext p
  change (coneWeights (weightLinkIncl v) v (fun q=>q.property.2) (weightTime v w) _).weights p=w.weights p
  rw [coneWeights_apply]
  have he:weightMap (weightLinkIncl v)
      (weightRestrict {p | p≠v ∧ (p≤v ∨ v≤p)} (weightDelete v w ht) (weightDelete_link w ht hp))=
      weightDelete v w ht:=weightRestrict_map _ _ _
  rw [he,weightDelete_apply]
  change (1-w.weights v)*((1-w.weights v)⁻¹*(if p=v then 0 else w.weights p))+
    (if v=p then w.weights v else 0)=w.weights p
  by_cases he:p=v
  · subst p;simp
  · rw [ite_eq_right he,ite_eq_right (Ne.symm he),←mul_assoc,mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr ht)),one_mul,add_zero]

lemma weightParts_surjective (v:P) (c:OrderWeights (WeightLink v)) :
    Function.Surjective (Sum.elim (weightOldMap v) (weightConeMap v)) := by
  intro w
  by_cases hz:w.weights v=0
  · obtain ⟨z,rfl⟩:=weightOld_surjective_zero w hz
    exact ⟨.inl z,rfl⟩
  by_cases ho:w.weights v=1
  · exact ⟨.inr (1,c),(weightConeMap_one v c).trans (weight_eq_vertex_of_one w v ho).symm⟩
  have ht:w.weights v<1:=lt_of_le_of_ne (weight_le_one w v) ho
  have hp:0<w.weights v:=lt_of_le_of_ne (w.nonneg v) (Ne.symm hz)
  exact ⟨.inr (weightTime v w,weightRestrict _ (weightDelete v w ht) (weightDelete_link w ht hp)),
    weightDelete_reconstruct w ht hp⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightLinearLinkInverse
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped BigOperators unitInterval
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable
universe u v

lemma weightLinearLinkMap_surjective {P:Type*} [LinearOrder P] (v:P) :
    Function.Surjective (weightLinkMap v) := by
  intro w
  refine ⟨weightMap (weightLinearLinkInverse v) w,?_⟩
  change weightMap (weightLinkOld v) (weightMap (weightLinearLinkInverse v) w)=w
  rw [weightMap_comp]
  exact weightMap_id w

lemma weightLinearCone_surjective {P:Type*} [LinearOrder P] (v:P) (c:OrderWeights (WeightLink v)) :
    Function.Surjective (weightConeMap v) := by
  intro w
  obtain ⟨z,hz⟩:=weightParts_surjective v c w
  rcases z with z|z
  · obtain ⟨l,hl⟩:=weightLinearLinkMap_surjective v z
    refine ⟨(0,l),?_⟩
    rw [weightConeMap_zero,hl]
    exact hz
  · exact ⟨z,hz⟩

lemma weightLinearCone_quotient {P:Type*} [LinearOrder P] [Fintype P]
    (v:P) (c:OrderWeights (WeightLink v)) : Topology.IsQuotientMap (weightConeMap v) :=
  Topology.IsQuotientMap.of_surjective_continuous (weightLinearCone_surjective v c) (weightConeMap v).continuous

lemma weightCone_embedding {P Q:Type*} [PartialOrder P] [PartialOrder Q]
    (j:Q↪oP) (v:Q) (p:I×OrderWeights (WeightLink v)) :
    weightMap ⟨j,j.monotone⟩ (weightConeMap v p)=
      weightConeMap (j v) (p.1,weightMap (weightLinkEmbedding j v) p.2) := by
  let jo:Q→oP:=⟨j,j.monotone⟩
  change weightMap jo (coneWeights (weightLinkIncl v) v (fun q=>q.property.2) p.1 p.2)=
    coneWeights (weightLinkIncl (j v)) (j v) (fun q=>q.property.2) p.1 (weightMap (weightLinkEmbedding j v) p.2)
  rw [weightMap_cone]
  apply OrderWeights.ext
  change (σ p.1).val • (weightMap (jo.comp (weightLinkIncl v)) p.2).weights+_= _
  have he:weightMap (jo.comp (weightLinkIncl v)) p.2=
      weightMap (weightLinkIncl (j v)) (weightMap (weightLinkEmbedding j v) p.2):=
    (weightMap_comp (weightLinkEmbedding j v) (weightLinkIncl (j v)) p.2).symm
  rw [he]
  rfl

lemma continuous_comp_weightEmbedding {P Q Y:Type*} [PartialOrder P] [LinearOrder Q]
    [Fintype Q] [TopologicalSpace Y] (j:Q↪oP) (v:Q) (c:OrderWeights (WeightLink v))
    (f:OrderWeights P→Y) (hCone:Continuous (f ∘ weightConeMap (j v))) :
    Continuous (f ∘ weightMap ⟨j,j.monotone⟩) := by
  apply (weightLinearCone_quotient v c).continuous_iff.mpr
  have hp:Continuous (fun p:I×OrderWeights (WeightLink v)=>
      (p.1,weightMap (weightLinkEmbedding j v) p.2)):=
    continuous_fst.prodMk ((weightMap_continuous (weightLinkEmbedding j v)).comp continuous_snd)
  exact (hCone.comp hp).congr (fun p=>congrArg f (weightCone_embedding j v p).symm)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightAttach
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P] (v:P)

noncomputable def weightAttach : C(ConeAttachment (weightLinkMap v),OrderWeights P) where
  toFun:=Quot.lift (Sum.elim (weightOldMap v) (weightConeMap v)) (by
    intro a b h
    cases h with
    | base x => exact weightConeMap_zero v x
    | apex x y => exact (weightConeMap_one v x).trans (weightConeMap_one v y).symm)
  continuous_toFun:=continuous_quot_lift _ (continuous_sum_dom.mpr ⟨(weightOldMap v).continuous,(weightConeMap v).continuous⟩)

lemma weightAttach_surjective (c:OrderWeights (WeightLink v)) : Function.Surjective (weightAttach v) := by
  intro w
  obtain ⟨p,hp⟩:=weightParts_surjective v c w
  exact ⟨Quot.mk _ p,hp⟩

lemma weightAttach_injective : Function.Injective (weightAttach v) := by
  intro a b
  induction a using Quot.inductionOn with
  | h a =>
    induction b using Quot.inductionOn with
    | h b =>
      cases a with
      | inl a =>
        cases b with
        | inl b =>
          intro h
          have hab:a=b:=weightMap_injective (weightOldIncl v) Subtype.val_injective h
          subst b;rfl
        | inr b =>
          intro h
          have ht:b.1=0:=Subtype.ext (by
            have he:=congrArg (fun w:OrderWeights P=>w.weights v) h
            change (weightOldMap v a).weights v=(weightConeMap v b).weights v at he
            rw [weightOldMap_at,weightConeMap_at] at he
            exact he.symm)
          obtain ⟨t,b⟩:=b
          dsimp only at ht
          subst t
          change weightOldMap v a=weightConeMap v (0,b) at h
          rw [weightConeMap_zero] at h
          have ha:a=weightLinkMap v b:=weightMap_injective (weightOldIncl v) Subtype.val_injective h
          subst a
          exact (coneAttachment_base (weightLinkMap v) b).symm
      | inr a =>
        cases b with
        | inl b =>
          intro h
          have ht:a.1=0:=Subtype.ext (by
            have he:=congrArg (fun w:OrderWeights P=>w.weights v) h
            change (weightConeMap v a).weights v=(weightOldMap v b).weights v at he
            rw [weightOldMap_at,weightConeMap_at] at he
            exact he)
          obtain ⟨t,a⟩:=a
          dsimp only at ht
          subst t
          change weightConeMap v (0,a)=weightOldMap v b at h
          rw [weightConeMap_zero] at h
          have hb:weightLinkMap v a=b:=weightMap_injective (weightOldIncl v) Subtype.val_injective h
          subst b
          exact coneAttachment_base (weightLinkMap v) a
        | inr b =>
          intro h
          obtain ⟨t,a⟩:=a
          obtain ⟨s,b⟩:=b
          obtain ⟨he,hh⟩:=weightConeMap_eq_cone h
          subst s
          rcases hh with ht|hab
          · subst t
            exact coneAttachment_apex (weightLinkMap v) a b
          · subst b;rfl

noncomputable def weightAttachEquiv (c:OrderWeights (WeightLink v)) :
    ConeAttachment (weightLinkMap v) ≃ OrderWeights P :=
  Equiv.ofBijective (weightAttach v) ⟨weightAttach_injective v,weightAttach_surjective v c⟩

lemma weightAttachEquiv_symm_old (c:OrderWeights (WeightLink v)) (w:OrderWeights (WeightOld v)) :
    (weightAttachEquiv v c).symm (weightOldMap v w)=coneAttachmentOld (weightLinkMap v) w := by
  apply (weightAttachEquiv v c).symm_apply_eq.mpr
  rfl

lemma weightAttachEquiv_symm_cone (c:OrderWeights (WeightLink v)) (p:I×OrderWeights (WeightLink v)) :
    (weightAttachEquiv v c).symm (weightConeMap v p)=coneAttachmentCone (weightLinkMap v) p := by
  apply (weightAttachEquiv v c).symm_apply_eq.mpr
  rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightVertexRetract
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

universe u
variable {P:Type u} [PartialOrder P] (v:P)
  (c:OrderWeights (WeightLink v))
  (H:ContinuousMap.Homotopy (ContinuousMap.id _) (ContinuousMap.const _ c))

noncomputable def weightVertexDelay (v:P) : C(OrderWeights P,I) where
  toFun w:=⟨w.weights v/2,by
    constructor
    · exact div_nonneg (w.nonneg v) (by norm_num)
    · have hh:=weight_le_one w v;linarith⟩
  continuous_toFun:=by
    apply Continuous.subtype_mk
    exact (weightEval_continuous v).div_const 2

lemma weightVertexDelay_lt (w:OrderWeights P) : weightVertexDelay v w<1 := by
  change w.weights v/2<1
  have hh:=weight_le_one w v
  linarith

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_UnionCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P] {r:P→P→Prop} {c:P}
namespace WeightContractionPiece

instance instReflExtends : Std.Refl (@Extends P _ r c) :=⟨extends_refl⟩

variable (C:Set (WeightContractionPiece r c)) (hc:IsChain Extends C) (hne:C.Nonempty)

def unionCarrier : Set P :={x | ∃a∈C,x∈a.carrier}
lemma subset_union {a:WeightContractionPiece r c} (ha:a∈C) : a.carrier⊆unionCarrier C :=
  fun _ hx=>⟨a,ha,hx⟩

end WeightContractionPiece
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Initial
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

variable {r:P→P→Prop} {c:P}
namespace WeightContractionPiece

noncomputable def initial (hc:∀x,¬r x c) : WeightContractionPiece r c where
  carrier:={c}
  root_mem:=Set.mem_singleton c
  down:=by
    intro x y hx hy
    have he:x=c:=Set.mem_singleton_iff.mp hx
    exact (hc y (he ▸ hy)).elim
  hom:={
    toFun p:=p.2
    continuous_toFun:=continuous_snd
    map_zero_left:=fun _=>rfl
    map_one_left:=fun w=>weight_eq_vertex_subsingleton w _ }

variable (wf:WellFounded r) (htotal:∀x y,x≠y → r x y ∨ r y x)

variable (a:WeightContractionPiece r c) (v:P) (hv:v∉a.carrier)
  (heA:∀x,x∈a.carrier↔r x v)
  (hlink:ContractibleSpace (OrderWeights (WeightEarlierLink r v)))

noncomputable def insertLinkContractionPoint : OrderWeights (WeightLink (⟨v,Set.mem_insert v a.carrier⟩:↥(insert v a.carrier))) :=
  let e:=weightHomeomorph (insertLinkIso r (fun x=>wf.irrefl.irrefl x) a.carrier v heA).symm
  e (Classical.choose (@id_nullhomotopic _ _ hlink))

noncomputable def insertLinkContraction :
    ContinuousMap.Homotopy (ContinuousMap.id _)
      (ContinuousMap.const _ (insertLinkContractionPoint wf a v heA hlink)) :=
  transportContraction (weightHomeomorph (insertLinkIso r (fun x=>wf.irrefl.irrefl x) a.carrier v heA).symm)
    (Classical.choose (@id_nullhomotopic _ _ hlink))
    (Classical.choice (Classical.choose_spec (@id_nullhomotopic _ _ hlink)))

end WeightContractionPiece

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Earlier
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P : Type} [PartialOrder P] (f : P →o ℕ)

namespace NaturalCylinder

lemma earlier_inr_iff (m n : ℕ) : earlier f (OrderMappingCylinder.right f m) (OrderMappingCylinder.right f n) ↔ m < n := by
  rw [earlier,weightJoinEarlier_iff]
  simp only [weightJoinKey,ite_eq_right (inr_not_old f m),ite_eq_right (inr_not_old f n)]
  change (m+1<n+1 ∨ m+1=n+1 ∧ WellOrderingRel (OrderMappingCylinder.right f m) (OrderMappingCylinder.right f n)) ↔ m<n
  constructor
  · rintro (h|⟨he,hr⟩)
    · omega
    · have he' : m=n := by omega
      subst m
      exact (WellOrderingRel.isWellOrder.wf.irrefl.irrefl _ hr).elim
  · intro h; exact Or.inl (by omega)

lemma link_iff (x : OrderMappingCylinder f) (n : ℕ) :
    (earlier f x (OrderMappingCylinder.right f n) ∧ (x ≤ OrderMappingCylinder.right f n ∨ OrderMappingCylinder.right f n ≤ x)) ↔ x < OrderMappingCylinder.right f n := by
  cases x with
  | inl p =>
    have hr : earlier f (OrderMappingCylinder.left f p) (OrderMappingCylinder.right f n) :=
      weightJoinEarlier_old _ _ (inl_old f p) (inr_not_old f n)
    change (earlier f (OrderMappingCylinder.left f p) (OrderMappingCylinder.right f n) ∧ (f p ≤ n ∨ False)) ↔ OrderMappingCylinder.left f p < OrderMappingCylinder.right f n
    rw [lt_iff_le_not_ge]
    change (_ ∧ (f p≤n ∨ False)) ↔ (f p≤n ∧ ¬ False)
    simp only [hr,true_and,or_false,not_false_eq_true,and_true]
  | inr m =>
    change (earlier f (OrderMappingCylinder.right f m) (OrderMappingCylinder.right f n) ∧ (OrderMappingCylinder.right f m ≤ OrderMappingCylinder.right f n ∨ OrderMappingCylinder.right f n ≤ OrderMappingCylinder.right f m)) ↔ OrderMappingCylinder.right f m < OrderMappingCylinder.right f n
    rw [earlier_inr_iff]
    change (m < n ∧ (m ≤ n ∨ n ≤ m)) ↔ (m ≤ n ∧ ¬ n ≤ m)
    omega

noncomputable def linkIso (n : ℕ) :
    WeightEarlierLink (earlier f) (OrderMappingCylinder.right f n) ≃o {x : OrderMappingCylinder f // x < OrderMappingCylinder.right f n} where
  toFun x := ⟨x.val,(link_iff f x.val n).mp x.property⟩
  invFun x := ⟨x.val,(link_iff f x.val n).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by intros; rfl

end NaturalCylinder

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_LiftedDeck
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe u
variable {S:Type u} (M:CoxeterMatrix S)

def SphericalLiftedFiber (T:Set S) :=
  {a:LiftedCell M // a.2.val⊆T ∧ a.1∈artinParabolic M T}

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_SimpleFrontLink
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

lemma alternating_isReduced_of_longest (z:M.Group)
    (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z) (s t:S) :
    M.toCoxeterSystem.IsReduced (altList s t (M s t)) := by
  by_cases he:s=t
  · subst t
    simpa only [M.diagonal s,altList_succ,altList_zero] using
      (show M.toCoxeterSystem.IsReduced [s] from by
        change M.toCoxeterSystem.length (M.toCoxeterSystem.simple s)=1
        exact M.toCoxeterSystem.length_simple s)
  · have hs:WeakPrefix M.toCoxeterSystem (M.toCoxeterSystem.simple s) z:=
      (positivePrefix_simple_iff M _ _).mp (by
        exact ⟨positiveSimpleLift M ((M.toCoxeterSystem.simple s)⁻¹*z),
          (positiveSimpleLift_left_complement M z hz _).symm⟩)
    have ht:WeakPrefix M.toCoxeterSystem (M.toCoxeterSystem.simple t) z:=
      (positivePrefix_simple_iff M _ _).mp (by
        exact ⟨positiveSimpleLift M ((M.toCoxeterSystem.simple t)⁻¹*z),
          (positiveSimpleLift_left_complement M z hz _).symm⟩)
    obtain ⟨v,hm,hl,hv,hv'⟩:=double_descent_prefix M.toCoxeterSystem s t he z
      (by have h:=(weakPrefix_simple_iff M.toCoxeterSystem s z).mp hs;omega)
      (by have h:=(weakPrefix_simple_iff M.toCoxeterSystem t z).mp ht;omega)
    have h₁:=M.toCoxeterSystem.length_wordProd_le (altList s t (M s t))
    have h₂:=M.toCoxeterSystem.length_mul_le (M.toCoxeterSystem.wordProd (altList s t (M s t))) v
    rw [←hv] at h₂
    change M.toCoxeterSystem.length (M.toCoxeterSystem.wordProd (altList s t (M s t)))=(altList s t (M s t)).length
    rw [length_altList] at h₁ ⊢
    omega

omit [Fintype S] in
lemma positivePrefix_first (s:S) (w:List S) : PositivePrefix M (positiveGenerator M s) (wordPositive M (s::w)) :=⟨wordPositive M w,rfl⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositiveHead
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositivePrefixMulLeft
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

omit [Fintype S] in
lemma exists_positive_first {a:PositiveArtin M} (ha:a≠1) :
    ∃s:S,PositivePrefix M (positiveGenerator M s) a := by
  obtain ⟨w,hw⟩:=positive_word_surjective M a
  cases w with
  | nil=>exact (ha hw.symm).elim
  | cons s w=>exact ⟨s,hw ▸ positivePrefix_first M s w⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositiveReverseHom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)
variable (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
include z hz

lemma reverse_wordPositive_braid (s t:S) :
    wordPositive M (altList s t (M s t)).reverse=wordPositive M (altList t s (M s t)).reverse := by
  apply wordPositive_eq_of_reduced M
  · exact (alternating_isReduced_of_longest M z hz s t).reverse
  · have h:=alternating_isReduced_of_longest M z hz t s
    rw [M.symmetric t s] at h
    exact h.reverse
  · change M.toCoxeterSystem.wordProd (altList s t (M s t)).reverse=M.toCoxeterSystem.wordProd (altList t s (M s t)).reverse
    rw [M.toCoxeterSystem.wordProd_reverse,M.toCoxeterSystem.wordProd_reverse,altList_braid]

lemma reverse_presented_relations : ∀u v:FreeMonoid S,positiveBraidRelations M u v →
    FreeMonoid.lift (fun s=>MulOpposite.op (positiveGenerator M s)) u=
      FreeMonoid.lift (fun s=>MulOpposite.op (positiveGenerator M s)) v := by
  rintro u v ⟨s,t,rfl,rfl⟩
  apply MulOpposite.unop_injective
  simp only [FreeMonoid.lift_ofList,MulOpposite.unop_list_prod,List.map_map]
  change (List.map (positiveGenerator M) (altList s t (M s t))).reverse.prod =
    (List.map (positiveGenerator M) (altList t s (M s t))).reverse.prod
  simpa only [wordPositive, List.map_reverse] using reverse_wordPositive_braid M z hz s t

noncomputable def positiveReverseHom : PositiveArtin M →* (PositiveArtin M)ᵐᵒᵖ :=
  PresentedMonoid.lift (fun s=>MulOpposite.op (positiveGenerator M s)) (reverse_presented_relations M z hz)

noncomputable def positiveReverse (a:PositiveArtin M) : PositiveArtin M := (positiveReverseHom M z hz a).unop

@[simp] lemma positiveReverse_generator (s:S) : positiveReverse M z hz (positiveGenerator M s)=positiveGenerator M s :=rfl
@[simp] lemma positiveReverse_one : positiveReverse M z hz 1=1 :=by unfold positiveReverse;rw [map_one];rfl
lemma positiveReverse_mul (a b:PositiveArtin M) : positiveReverse M z hz (a*b)=positiveReverse M z hz b*positiveReverse M z hz a :=by unfold positiveReverse;rw [map_mul];rfl

lemma positiveReverse_word (w:List S) : positiveReverse M z hz (wordPositive M w)=wordPositive M w.reverse := by
  induction w with
  | nil=>exact positiveReverse_one M z hz
  | cons s w ih=>
    change positiveReverse M z hz (positiveGenerator M s*wordPositive M w)=_
    rw [positiveReverse_mul,positiveReverse_generator,ih,List.reverse_cons,wordPositive_append]
    rfl

@[simp] lemma positiveReverse_involutive (a:PositiveArtin M) : positiveReverse M z hz (positiveReverse M z hz a)=a :=by
  obtain ⟨w,rfl⟩:=positive_word_surjective M a
  rw [positiveReverse_word,positiveReverse_word,List.reverse_reverse]

def PositiveSuffix (a b:PositiveArtin M) : Prop := ∃c:PositiveArtin M,b=c*a

lemma positiveReverse_prefix_iff (a b:PositiveArtin M) :
    PositivePrefix M (positiveReverse M z hz a) (positiveReverse M z hz b) ↔ PositiveSuffix M a b := by
  constructor
  · rintro ⟨c,hc⟩
    refine ⟨positiveReverse M z hz c,?_⟩
    have h:=congrArg (positiveReverse M z hz) hc
    simpa only [positiveReverse_mul,positiveReverse_involutive] using h
  · rintro ⟨c,hc⟩
    exact ⟨positiveReverse M z hz c,by rw [hc,positiveReverse_mul]⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositiveDescentSet
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
variable (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)

def PositiveDescentSet (a:PositiveArtin M) : Set S :=
  {s | PositiveSuffix M (positiveGenerator M s) a}

include z hz in
lemma positiveDescentSet_nonempty {a:PositiveArtin M} (ha:a≠1) :
    (PositiveDescentSet M a).Nonempty := by
  have hra:positiveReverse M z hz a≠1:=by
    intro he
    have h:=congrArg (positiveReverse M z hz) he
    simp only [positiveReverse_involutive,positiveReverse_one] at h
    exact ha h
  obtain ⟨s,hs⟩:=exists_positive_first M hra
  refine ⟨s,?_⟩
  apply (positiveReverse_prefix_iff M z hz _ _).mp
  simpa only [positiveReverse_generator] using hs

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_SphericalLongest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric
open scoped unitInterval

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

noncomputable def sphericalLongest (T:SphericalType M) : M.Group :=
  (exists_parabolic_longest M T.val T.property).choose

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_TopBlockMatchingKey
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} (M:CoxeterMatrix S)

section FirstDescent
variable [Fintype S] [LinearOrder S] (z:M.Group)
  (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
  (b:PositiveArtin M) (hb:b≠1)

noncomputable def firstPositiveDescent : S :=
  (PositiveDescentSet M b).toFinset.min'
    (Set.toFinset_nonempty.mpr (positiveDescentSet_nonempty M z hz hb))

end FirstDescent
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_PositiveLiftedCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

abbrev PositiveLiftedCell := PositiveArtin M × SphericalType M

noncomputable def positiveCellTop (a:PositiveLiftedCell M) : PositiveArtin M :=
  a.1*positiveSimpleLift M (sphericalLongest M a.2)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositiveMatchingTypeKey
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
variable (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)

noncomputable def positiveMatchingTypeKey (a:PositiveLiftedCell M) : ℕ :=
  if h:positiveCellTop M a=1 then 0 else
    topBlockMatchingKey (firstPositiveDescent M z hz (positiveCellTop M a) h) a.2.val.toFinset

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositiveRegion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} (M:CoxeterMatrix S)

def PositiveRegion (g:Artin M) : Set (LiftedCell M) :=
  {a | ∃p:PositiveArtin M,a.1=g*positiveToArtin M p}

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_TieCode
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceDeligne_countable : Countable (Deligne M) := by
  let :Countable (Artin M):=Function.Surjective.countable (PresentedGroup.mk_surjective (braidRelators M))
  apply Function.Injective.countable (f:=fun P:Deligne M=>(P.val.1,sourceCosetRepresentative M P))
  intro P R h
  have ht:P.val.1=R.val.1:=congrArg (fun z:Set S × Artin M=>z.1) h
  have hx:sourceCosetRepresentative M P=sourceCosetRepresentative M R:=congrArg (fun z:Set S × Artin M=>z.2) h
  apply Subtype.ext
  apply Prod.ext
  · exact ht
  · rw [sourceCosetRepresentative_spec,sourceCosetRepresentative_spec,ht,hx]

noncomputable def sourceTieCode (P:Deligne M) : ℕ :=
  letI:=sourceDeligne_countable M
  letI:=Encodable.ofCountable (Deligne M)
  Encodable.encode P

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_NoncriticalPositiveCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
variable (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
variable (inj:Function.Injective (positiveToArtin M))

abbrev NoncriticalPositiveCell := {a:PositiveLiftedCell M // positiveCellTop M a≠1}

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_PositiveCellPoset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] (M : CoxeterMatrix S)

@[reducible] def PositiveCellPoset (_inj : Function.Injective (positiveToArtin M)) := PositiveLiftedCell M

variable [LinearOrder S]
variable (z : M.Group) (hz : ∀ w, M.toCoxeterSystem.length w ≤ M.toCoxeterSystem.length z)
variable (inj : Function.Injective (positiveToArtin M))

def PositiveEarlier (a b : PositiveCellPoset M inj) : Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) WellOrderingRel)
    (positiveDegree M (positiveCellTop M a),(positiveMatchingTypeKey M z hz a,a))
    (positiveDegree M (positiveCellTop M b),(positiveMatchingTypeKey M z hz b,b))

end HarmonicArtin

end OAI
end


