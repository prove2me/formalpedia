-- Prove2me | Definitions.Def_OAIQ236Ap004
-- name    : OAIQ236Ap004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T19:47:59.356426+00:00
-- url     : https://prove2.me/theorems/3cacc2a3-c0a5-4c1c-86b9-ef10a0942f04
-- title:
--   Definitions bundle OAIQ236Ap004 of the split of OpenAI, Parabolic intersections in Artin groups
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure` and `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections`, carved from OpenAI's openai/math development (OpenAI, *Parabolic intersections in Artin groups*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 215 declarations of OpenAI's Lean: 93 definitions, 2 inductive types or structures, 4 instances and 116 theorems. The definitions and types are `OAI.HarmonicArtin.IsFrontHead`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ActedIndex`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ArrowPair`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.CappedOn`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.CornerPath`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.DownClosed`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.EqualColorPair`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.HomPath`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.TermwiseSplitInjection`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.arrowCornerEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.blockInclusion`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.blockProjection`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.coefficientTopDual`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.diagonalToken`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homInternalSupport`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.layerVector`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.lowMatrix`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.lowerLevelSet`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.purePathEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.purePathForget`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.restrictLayer`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.tokenCornerEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.unfoldedCartan`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.zeroCornerEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.CoefficientMatrix`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.TokenMatrix`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.arrowLinear`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.atLevel`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.matrixOne`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.matrixTwo`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.matrixZero`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathOne`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathTwo`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathZero`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.signDiagonal`, `OAI.HarmonicArtin.WeightContractionPiece`, `OAI.HarmonicArtin.WeightContractionPiece.Extends`, `OAI.HarmonicArtin.WeightContractionPiece.inclusion`, `OAI.HarmonicArtin.WeightContractionPiece.initial`, `OAI.HarmonicArtin.WeightContractionPiece.insertLinkContraction` and 55 more.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `ArtinGroups_Complexes_ActedIndex`, `ArtinGroups_Complexes_BlockClosed`, `ArtinGroups_Complexes_Capped`, `ArtinGroups_Complexes_CoefficientSocle`, `ArtinGroups_Complexes_CoefficientTopDual`, `ArtinGroups_Complexes_CornerPath`, `ArtinGroups_Complexes_DiagonalVertex`, `ArtinGroups_Complexes_DownClosed`, `ArtinGroups_Complexes_EqualColorPair`, `ArtinGroups_Complexes_ExtendLayer`, `ArtinGroups_Complexes_GeneratorVector`, `ArtinGroups_Complexes_HomInternalSupport`, `ArtinGroups_Complexes_HomPath`, `ArtinGroups_Complexes_LayerVector`, `ArtinGroups_Complexes_LowMatrix`, `ArtinGroups_Complexes_RestrictLayer`, `ArtinGroups_Complexes_TermwiseSplitInjection`, `ArtinGroups_Complexes_TwistNewTestIndex`, `ArtinGroups_Harmonic_BinaryProductBoundary`, `ArtinGroups_Harmonic_ConeAttachmentRel`, `ArtinGroups_Harmonic_EarlyDelay`, `ArtinGroups_Harmonic_FiniteChainEnum`, `ArtinGroups_Harmonic_FusionColorWord`, `ArtinGroups_Harmonic_FusionFold`, `ArtinGroups_Harmonic_FusionQuiverSimpleEdge`, `ArtinGroups_Harmonic_Initial`, `ArtinGroups_Harmonic_InsertOldIso`, `ArtinGroups_Harmonic_LateDelay`, `ArtinGroups_Harmonic_MaximalReducedMonoidPrefix`, `ArtinGroups_Harmonic_MaximalReducedPositivePrefix`, `ArtinGroups_Harmonic_PositiveHead`, `ArtinGroups_Harmonic_SimplexSupport`, `ArtinGroups_Harmonic_UnionCarrier`, `ArtinGroups_Harmonic_WordFrontData`, `ArtinGroups_Quivers_CoefficientMatrix`, `ArtinGroups_Quivers_LengthCases`, `ArtinGroups_Quivers_Level`, `ArtinGroups_Quivers_PathTwo`, `ArtinGroups_Quivers_PathTwoSelf`, `ArtinGroups_Quivers_PathZero`, `ArtinGroups_Quivers_SignDiagonal`, `ArtinGroups_Quivers_TokenTestVector`, `ArtinGroups_Quivers_UnitTestVector`, `ArtinGroups_Quivers_VertexLinear`, `ArtinGroups_Realizations_ConeWeights`, `ArtinGroups_Realizations_NerveChain`, `ArtinGroups_Realizations_OrderWeights`, `ArtinGroups_Realizations_WeightAttach`, `ArtinGroups_Realizations_WeightCarrier`, `ArtinGroups_Realizations_WeightDim`, `ArtinGroups_Realizations_WeightDual`, `ArtinGroups_Realizations_WeightHomeomorph`, `ArtinGroups_Realizations_WeightLinearLinkInverse`, `ArtinGroups_Realizations_WeightMap`, `ArtinGroups_Realizations_WeightMapCover`, `ArtinGroups_Realizations_WeightOld`, `ArtinGroups_Realizations_WeightVertexRetract`.
--
--   **Imports.** It imports the published bundle `Def_ArtinParabolicIntersections`; the bundles `OAIQ236Ap000` and `OAIQ236Ap001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ236Ap005` and `OAIQ236Ap007`.
-- source:
--   OpenAI, Parabolic intersections in Artin groups, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Definitions.Def_ArtinParabolicIntersections
import Definitions.Def_OAIQ236Ap000
import Definitions.Def_OAIQ236Ap001

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ActedIndex
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

abbrev ActedIndex (E : BasedComplex Q (K := K) I) (α : V) :=
  {i : I // (E.placement i).color = α}

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

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

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

end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_DiagonalVertex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V]

namespace BasedComplex
variable {I J : Type*} [Fintype I] [Fintype J]

variable [DecidableEq I]

def diagonalToken (E : BasedComplex Q (K := K) I) (i : I) : Matrix I I (Q.Zigzag K) :=
  Matrix.diagonal (fun j => if j = i then tokenBasis Q (E.placement i).color else 0)

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ExtendLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]

lemma tokenOnly_mul_positive {x y : Q.Zigzag K}
    (hx : x.vertex = 0) (ha : x.arrow = 0) (hy : y.vertex = 0) : x * y = 0 := by
  apply ext
  · change (x * y).vertex = 0
    rw [vertex_mul, hx, MulZeroClass.zero_mul]
  · change (x * y).arrow = 0
    rw [arrow_mul, hx, ha]
    ext a
    simp [leftScale, rightScale]
  · change (x * y).token = 0
    rw [token_mul, hx, ha, hy, MulZeroClass.zero_mul, MulZeroClass.mul_zero,
      backtrack_zero_left, add_zero, add_zero]

lemma positive_mul_tokenOnly {x y : Q.Zigzag K}
    (hx : x.vertex = 0) (hy : y.vertex = 0) (ha : y.arrow = 0) : x * y = 0 := by
  apply ext
  · change (x * y).vertex = 0
    rw [vertex_mul, hx, MulZeroClass.zero_mul]
  · change (x * y).arrow = 0
    rw [arrow_mul, hx, hy]
    ext a
    simp [leftScale, rightScale]
  · change (x * y).token = 0
    rw [token_mul, hx, hy, ha, MulZeroClass.zero_mul, MulZeroClass.mul_zero,
      backtrack_zero_right, add_zero, add_zero]

namespace BasedComplex
variable {I J : Type*} [Fintype I] [Fintype J]

lemma differential_arrow_level (E : BasedComplex Q (K := K) I) {i j : I}
    (h : (E.placement j).level ≠ (E.placement i).level) :
    (E.differential i j).arrow = 0 := by
  by_cases hc : (E.placement j).cochain = (E.placement i).cochain + 1
  · apply (E.degree i j).2.2.1
    dsimp only [GeneratorPlacement.level] at h
    omega
  · rw [(E.degree i j).1 hc]
    rfl

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_PathZero
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]

def pathZero : Q.Zigzag K →ₗ[K] Q.Zigzag K where
  toFun x := (x.vertex, 0, 0)
  map_add' x y := by
    apply ext
    · rfl
    · change (0 : A → K) = 0 + 0
      rw [add_zero]
    · change (0 : V → K) = 0 + 0
      rw [add_zero]
  map_smul' r x := by
    apply ext
    · rfl
    · change (0 : A → K) = r • 0
      rw [smul_zero]
    · change (0 : V → K) = r • 0
      rw [smul_zero]

def pathOne : Q.Zigzag K →ₗ[K] Q.Zigzag K where
  toFun x := (0, x.arrow, 0)
  map_add' x y := by
    apply ext
    · change (0 : V → K) = 0 + 0
      rw [add_zero]
    · rfl
    · change (0 : V → K) = 0 + 0
      rw [add_zero]
  map_smul' r x := by
    apply ext
    · change (0 : V → K) = r • 0
      rw [smul_zero]
    · rfl
    · change (0 : V → K) = r • 0
      rw [smul_zero]

lemma pathZero_mul (x y : Q.Zigzag K) :
    pathZero Q (x * y) = pathZero Q x * pathZero Q y := by
  apply ext
  · change (x * y).vertex = (pathZero Q x * pathZero Q y).vertex
    rw [vertex_mul, vertex_mul]
    rfl
  · change (0 : A → K) = (pathZero Q x * pathZero Q y).arrow
    rw [arrow_mul]
    change (0 : A → K) = Q.leftScale x.vertex 0 + Q.rightScale 0 y.vertex
    ext a
    simp [leftScale, rightScale]
  · change (0 : V → K) = (pathZero Q x * pathZero Q y).token
    rw [token_mul]
    change (0 : V → K) = x.vertex * 0 + 0 * y.vertex + Q.backtrack 0 0
    simp

lemma pathOne_mul (x y : Q.Zigzag K) :
    pathOne Q (x * y) = pathZero Q x * pathOne Q y + pathOne Q x * pathZero Q y := by
  apply ext
  · change (0 : V → K) = (pathZero Q x * pathOne Q y).vertex +
      (pathOne Q x * pathZero Q y).vertex
    rw [vertex_mul, vertex_mul]
    change (0 : V → K) = x.vertex * 0 + 0 * y.vertex
    simp
  · change (x * y).arrow = (pathZero Q x * pathOne Q y).arrow +
      (pathOne Q x * pathZero Q y).arrow
    rw [arrow_mul, arrow_mul, arrow_mul]
    change Q.leftScale x.vertex y.arrow + Q.rightScale x.arrow y.vertex =
      (Q.leftScale x.vertex y.arrow + Q.rightScale 0 0) +
        (Q.leftScale 0 0 + Q.rightScale x.arrow y.vertex)
    ext a
    simp [leftScale, rightScale]
  · change (0 : V → K) = (pathZero Q x * pathOne Q y).token +
      (pathOne Q x * pathZero Q y).token
    rw [token_mul, token_mul]
    change (0 : V → K) = (x.vertex * 0 + 0 * 0 + Q.backtrack 0 y.arrow) +
      (0 * 0 + 0 * y.vertex + Q.backtrack x.arrow 0)
    simp

lemma pathZero_vertexId (α : V) : pathZero Q (vertexId Q (K := K) α) = vertexId Q α := rfl
lemma pathOne_vertexId (α : V) : pathOne Q (vertexId Q (K := K) α) = 0 := rfl

lemma pathZero_eq_zero {x : Q.Zigzag K} (h : x.vertex = 0) : pathZero Q x = 0 := by
  apply ext
  · exact h
  · rfl
  · rfl

lemma pathOne_eq_self {x : Q.Zigzag K} (h₀ : x.vertex = 0) (h₂ : x.token = 0) :
    pathOne Q x = x := by
  apply ext
  · exact h₀.symm
  · rfl
  · exact h₂.symm

variable {I J L : Type*}

def matrixZero : Matrix I J (Q.Zigzag K) →ₗ[K] Matrix I J (Q.Zigzag K) where
  toFun f i j := pathZero Q (f i j)
  map_add' f g := by apply Matrix.ext; intro i j; exact map_add _ _ _
  map_smul' r f := by apply Matrix.ext; intro i j; exact (pathZero Q).map_smul' r (f i j)

def matrixOne : Matrix I J (Q.Zigzag K) →ₗ[K] Matrix I J (Q.Zigzag K) where
  toFun f i j := pathOne Q (f i j)
  map_add' f g := by apply Matrix.ext; intro i j; exact map_add _ _ _
  map_smul' r f := by apply Matrix.ext; intro i j; exact (pathOne Q).map_smul' r (f i j)

lemma matrixZero_mul [Fintype J] (f : Matrix I J (Q.Zigzag K))
    (g : Matrix J L (Q.Zigzag K)) :
    matrixZero Q (f * g) = matrixZero Q f * matrixZero Q g := by
  apply Matrix.ext
  intro i k
  change pathZero Q (∑ j, f i j * g j k) = ∑ j, pathZero Q (f i j) * pathZero Q (g j k)
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => pathZero_mul Q _ _

end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_RestrictLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]

lemma pathOne_eq_zero {x : Q.Zigzag K} (h : x.arrow = 0) : pathOne Q x = 0 := by
  apply ext
  · rfl
  · exact h
  · rfl

namespace BasedComplex
variable {I J : Type*} [Fintype I] [Fintype J]

def restrictLayer (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (l k : ℤ) : Matrix I J (Q.Zigzag K) →ₗ[K]
      Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K) where
  toFun f i j := f i.val j.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_CoefficientMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J : Type*} [Fintype I] [Fintype J]

def CoefficientMatrix (f : Matrix I J (Q.Zigzag K)) : Prop :=
  ∀ i j, (f i j).arrow = 0 ∧ (f i j).token = 0

omit [Fintype I] [Fintype J] in
lemma matrixZero_eq_self {f : Matrix I J (Q.Zigzag K)} (hf : CoefficientMatrix Q f) :
    matrixZero Q f = f := by
  apply Matrix.ext
  intro i j
  apply ext
  · rfl
  · exact (hf i j).1.symm
  · exact (hf i j).2.symm

end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_PathTwo
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]

def pathTwo : Q.Zigzag K →ₗ[K] Q.Zigzag K where
  toFun x := (0, 0, x.token)
  map_add' _ _ := by
    apply ext
    · change (0 : V → K) = 0 + 0
      rw [add_zero]
    · change (0 : A → K) = 0 + 0
      rw [add_zero]
    · rfl
  map_smul' r x := by
    apply ext
    · change (0 : V → K) = r • 0
      rw [smul_zero]
    · change (0 : A → K) = r • 0
      rw [smul_zero]
    · rfl

lemma path_decomposition (x : Q.Zigzag K) :
    pathZero Q x + pathOne Q x + pathTwo Q x = x := by
  apply ext
  · change x.vertex + 0 + 0 = x.vertex
    simp only [add_zero]
  · change (0 : A → K) + x.arrow + 0 = x.arrow
    simp only [zero_add, add_zero]
  · change (0 : V → K) + 0 + x.token = x.token
    simp only [zero_add]

lemma pathTwo_mul_positive (x : Q.Zigzag K) {y : Q.Zigzag K} (hy : y.vertex = 0) :
    pathTwo Q x * y = 0 := tokenOnly_mul_positive Q rfl rfl hy

lemma positive_mul_pathTwo {x : Q.Zigzag K} (hx : x.vertex = 0) (y : Q.Zigzag K) :
    x * pathTwo Q y = 0 := positive_mul_tokenOnly Q hx rfl rfl

variable {I J L : Type*}

def matrixTwo : Matrix I J (Q.Zigzag K) →ₗ[K] Matrix I J (Q.Zigzag K) where
  toFun f i j := pathTwo Q (f i j)
  map_add' f g := by apply Matrix.ext; intro i j; exact map_add _ _ _
  map_smul' r f := by apply Matrix.ext; intro i j; exact (pathTwo Q).map_smul' r (f i j)

lemma matrix_decomposition (f : Matrix I J (Q.Zigzag K)) :
    matrixZero Q f + matrixOne Q f + matrixTwo Q f = f := by
  apply Matrix.ext
  intro i j
  exact path_decomposition Q (f i j)

end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_PathTwoSelf
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]

lemma pathTwo_eq_self {x : Q.Zigzag K} (h₀ : x.vertex = 0) (h₁ : x.arrow = 0) :
    pathTwo Q x = x := by
  apply ext
  · exact h₀.symm
  · exact h₁.symm
  · rfl

lemma pathTwo_eq_zero {x : Q.Zigzag K} (h : x.token = 0) : pathTwo Q x = 0 := by
  apply ext
  · rfl
  · rfl
  · exact h

lemma pathTwo_mul_linear_left {x : Q.Zigzag K} (h₀ : x.vertex = 0) (h₂ : x.token = 0)
    (y : Q.Zigzag K) : pathTwo Q (x * y) = x * pathOne Q y := by
  apply ext
  · change (0 : V → K) = (x * pathOne Q y).vertex
    rw [vertex_mul, h₀, MulZeroClass.zero_mul]
  · change (0 : A → K) = (x * pathOne Q y).arrow
    rw [arrow_mul, h₀]
    ext a
    change (0 : K) = 0 * y.arrow a + x.arrow a * 0
    simp only [MulZeroClass.mul_zero, MulZeroClass.zero_mul, zero_add]
  · change (x * y).token = (x * pathOne Q y).token
    rw [token_mul, token_mul, h₀, h₂]
    simp only [MulZeroClass.zero_mul, zero_add]
    rfl

lemma pathTwo_mul_linear_right (x : Q.Zigzag K) {y : Q.Zigzag K}
    (h₀ : y.vertex = 0) (h₂ : y.token = 0) : pathTwo Q (x * y) = pathOne Q x * y := by
  apply ext
  · change (0 : V → K) = (pathOne Q x * y).vertex
    rw [vertex_mul, h₀, MulZeroClass.mul_zero]
  · change (0 : A → K) = (pathOne Q x * y).arrow
    rw [arrow_mul, h₀]
    ext a
    change (0 : K) = 0 * y.arrow a + x.arrow a * 0
    simp only [MulZeroClass.mul_zero, MulZeroClass.zero_mul, zero_add]
  · change (x * y).token = (pathOne Q x * y).token
    rw [token_mul, token_mul, h₀, h₂]
    simp only [MulZeroClass.mul_zero, zero_add]
    rfl

variable {I J L : Type*}

lemma matrixOne_entries {p : I → GeneratorPlacement V} {q : J → GeneratorPlacement V}
    {f : Matrix I J (Q.Zigzag K)} (hf : ProjectiveEntries Q p q f) :
    ProjectiveEntries Q p q (matrixOne Q f) := by
  constructor
  · intro i j
    have h := congrArg (pathOne Q) (hf.1 i j)
    rw [pathOne_mul, pathZero_vertexId, pathOne_vertexId,
      MulZeroClass.zero_mul, add_zero] at h
    exact h
  · intro i j
    have h := congrArg (pathOne Q) (hf.2 i j)
    rw [pathOne_mul, pathZero_vertexId, pathOne_vertexId,
      MulZeroClass.mul_zero, zero_add] at h
    exact h

lemma matrixOne_degree {p : I → GeneratorPlacement V} {q : J → GeneratorPlacement V}
    {n v : ℤ} {f : Matrix I J (Q.Zigzag K)} (hf : MapDegree Q p q n v f) :
    MapDegree Q p q n v (matrixOne Q f) := by
  intro i j
  constructor
  · intro h
    change pathOne Q (f i j) = 0
    rw [(hf i j).1 h, map_zero]
  · exact ⟨fun _ => rfl, (hf i j).2.2.1, fun _ => rfl⟩

end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_Capped
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J : Type*}

lemma degree_token_support {p : I → GeneratorPlacement V}
    {q : J → GeneratorPlacement V} {M : Matrix I J (Q.Zigzag K)}
    {n v : ℤ} (hc : ProjectiveEntries Q p q M) (hd : MapDegree Q p q n v M)
    (i : I) (j : J) (w : V) (hne : (M i j).token w ≠ 0) :
    (p i).color = w ∧ (q j).color = w ∧
    (q j).cochain = (p i).cochain + n ∧
    (q j).internal = (p i).internal + v - 2 := by
  have hleft := congrArg (fun x : Q.Zigzag K => x.token w) (hc.1 i j)
  have hright := congrArg (fun x : Q.Zigzag K => x.token w) (hc.2 i j)
  have hpv : (p i).color = w := by
    by_contra h
    have hh : w ≠ (p i).color := Ne.symm h
    change (vertexId Q (p i).color * M i j).token w = (M i j).token w at hleft
    rw [token_mul] at hleft
    simp only [token_vertexId, arrow_vertexId, MulZeroClass.zero_mul,
      backtrack_zero_left, Pi.add_apply, Pi.zero_apply, add_zero] at hleft
    change (vertexId Q (p i).color).vertex w * (M i j).token w = _ at hleft
    rw [vertexId_eval, ite_eq_right hh, MulZeroClass.zero_mul] at hleft
    exact hne hleft.symm
  have hqv : (q j).color = w := by
    by_contra h
    have hh : w ≠ (q j).color := Ne.symm h
    change (M i j * vertexId Q (q j).color).token w = (M i j).token w at hright
    rw [token_mul] at hright
    simp only [token_vertexId, arrow_vertexId, MulZeroClass.mul_zero,
      backtrack_zero_right, Pi.add_apply, Pi.zero_apply, zero_add, add_zero] at hright
    change (M i j).token w * (vertexId Q (q j).color).vertex w = _ at hright
    rw [vertexId_eval, ite_eq_right hh, MulZeroClass.mul_zero] at hright
    exact hne hright.symm
  have hcq : (q j).cochain = (p i).cochain + n := by
    by_contra h
    have hz := (hd i j).1 h
    exact hne (by rw [hz]; rfl)
  have hiq : (q j).internal = (p i).internal + v - 2 := by
    by_contra h
    have hh : v + (p i).internal - (q j).internal ≠ 2 := by omega
    have hz := (hd i j).2.2.2 hh
    exact hne (by rw [hz]; rfl)
  exact ⟨hpv, hqv, hcq, hiq⟩

namespace BasedComplex
variable [Fintype I] [Fintype J]

def CappedOn (E : BasedComplex Q (K := K) I) (U : Set V) (q : ℤ) : Prop :=
  ∀ i, (E.placement i).color ∈ U → (E.placement i).level ≤ q

lemma differential_token_level (E : BasedComplex Q (K := K) I) {i j : I}
    (h : (E.placement j).level ≠ (E.placement i).level - 1) :
    (E.differential i j).token = 0 := by
  by_cases hc : (E.placement j).cochain = (E.placement i).cochain + 1
  · apply (E.degree i j).2.2.2
    dsimp only [GeneratorPlacement.level] at h
    omega
  · rw [(E.degree i j).1 hc]
    rfl

lemma capped_incoming_token (E : BasedComplex Q (K := K) I) (U : Set V) (q : ℤ)
    (hcap : E.CappedOn Q U q) (j : I) (hj : (E.placement j).level = q)
    (hU : (E.placement j).color ∈ U) (i : I) :
    pathTwo Q (E.differential i j) = 0 := by
  apply pathTwo_eq_zero Q
  ext w
  by_contra hw
  obtain ⟨hi, hjc, hc, hu⟩ := degree_token_support Q E.entries E.degree i j w hw
  have h : (E.placement i).color ∈ U := by simpa only [hi, hjc] using hU
  have hb := hcap i h
  dsimp only [GeneratorPlacement.level] at hb hj
  omega

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomInternalSupport
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

noncomputable def homInternalSupport (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) : Finset ℤ :=
  Finset.univ.image fun t : I × J × Fin 3 =>
    (F.placement t.2.1).internal - (E.placement t.1).internal + (t.2.2.val : ℤ)

omit [Fintype V] [DecidableEq A] in
lemma mem_homInternalSupport (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (v : ℤ) :
    v ∈ homInternalSupport Q E F ↔ ∃ (i : I) (j : J) (r : Fin 3),
      v = (F.placement j).internal - (E.placement i).internal + (r.val : ℤ) := by
  classical
  simp only [homInternalSupport, Finset.mem_image, Finset.mem_univ, true_and,
    Prod.exists, eq_comm]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

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

def arrowLinear : Q.Zigzag K →ₗ[K] (A → K) where
  toFun := arrow
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma arrow_sum {T : Type*} (s : Finset T) (f : T → Q.Zigzag K) :
    (∑ t ∈ s, f t).arrow = ∑ t ∈ s, (f t).arrow :=
  map_sum (arrowLinear Q) f s

def TokenMatrix (f : Matrix I J (Q.Zigzag K)) : Prop :=
  ∀ i j, (f i j).vertex = 0 ∧ (f i j).arrow = 0

lemma matrixTwo_eq_self {f : Matrix I J (Q.Zigzag K)} (hf : TokenMatrix Q f) :
    matrixTwo Q f = f := by
  apply Matrix.ext
  intro i j
  exact pathTwo_eq_self Q (hf i j).1 (hf i j).2

lemma tokenMatrix_sub {f g : Matrix I J (Q.Zigzag K)}
    (hf : TokenMatrix Q f) (hg : TokenMatrix Q g) : TokenMatrix Q (f-g) := by
  intro i j
  constructor
  · change (f i j).vertex - (g i j).vertex = 0
    rw [(hf i j).1, (hg i j).1, sub_zero]
  · change (f i j).arrow - (g i j).arrow = 0
    rw [(hf i j).2, (hg i j).2, sub_zero]

end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_CoefficientSocle
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

omit [Fintype V] [DecidableEq A] [Fintype I] [Fintype J] in
lemma entry_vertex_left_support {p : I → GeneratorPlacement V} {q : J → GeneratorPlacement V}
    {f : Matrix I J (Q.Zigzag K)} (hf : ProjectiveEntries Q p q f)
    (i : I) (j : J) (α : V) (hα : α ≠ (p i).color) : (f i j).vertex α = 0 := by
  have hh := congrArg (fun z : Q.Zigzag K => z.vertex α) (hf.1 i j)
  change (vertexId Q (p i).color).vertex α * (f i j).vertex α = _ at hh
  rw [vertexId_eval, ite_eq_right hα, MulZeroClass.zero_mul] at hh
  exact hh.symm

omit [Fintype V] [DecidableEq A] [Fintype I] [Fintype J] in
lemma entry_vertex_right_support {p : I → GeneratorPlacement V} {q : J → GeneratorPlacement V}
    {f : Matrix I J (Q.Zigzag K)} (hf : ProjectiveEntries Q p q f)
    (i : I) (j : J) (α : V) (hα : α ≠ (q j).color) : (f i j).vertex α = 0 := by
  have hh := congrArg (fun z : Q.Zigzag K => z.vertex α) (hf.2 i j)
  change (f i j).vertex α * (vertexId Q (q j).color).vertex α = _ at hh
  rw [vertexId_eval, ite_eq_right hα, MulZeroClass.mul_zero] at hh
  exact hh.symm

omit [Fintype V] [DecidableEq A] in
lemma coefficient_row_zero {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    {f : Matrix I J (Q.Zigzag K)} (hf : ProjectiveEntries Q E.placement F.placement f)
    (hc : CoefficientMatrix Q f) (i : I)
    (hz : ∀ j, (f i j).vertex (E.placement i).color = 0) : ∀ j, f i j = 0 := by
  intro j
  apply ext
  · funext α
    by_cases ha : α = (E.placement i).color
    · subst α; exact hz j
    · exact entry_vertex_left_support Q hf i j α ha
  · exact (hc i j).1
  · exact (hc i j).2

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_CoefficientTopDual
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

def coefficientTopDual (E : BasedComplex Q (K := K) I) (α : V) (c : ℤ) :
    Submodule K (I → K) where
  carrier := {x | (∀ i, (E.placement i).color ≠ α ∨ (E.placement i).cochain ≠ c → x i = 0) ∧
    ∀ i a, ∑ j, (E.differential i j).arrow a * x j = 0}
  zero_mem' := by constructor <;> simp
  add_mem' := by
    rintro x y ⟨hx,hxd⟩ ⟨hy,hyd⟩
    constructor
    · intro i hi; simp only [Pi.add_apply, hx i hi, hy i hi, add_zero]
    · intro i a
      simp only [Pi.add_apply, _root_.mul_add, Finset.sum_add_distrib, hxd i a, hyd i a, add_zero]
  smul_mem' := by
    rintro r x ⟨hx,hxd⟩
    constructor
    · intro i hi; simp only [Pi.smul_apply, hx i hi, smul_zero]
    · intro i a
      simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ r, ← Finset.mul_sum, hxd i a,
        MulZeroClass.mul_zero]

omit [Fintype V] [DecidableEq A] in
lemma token_sum {T : Type*} (s : Finset T) (f : T → Q.Zigzag K) :
    (∑ t ∈ s, f t).token = ∑ t ∈ s, (f t).token :=
  map_sum ({ toFun := token
             map_add' := fun _ _ => rfl
             map_smul' := fun _ _ => rfl } : Q.Zigzag K →ₗ[K] (V → K)) f s

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomPath
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

abbrev HomPath (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (n v : ℤ) :=
  {t : I × J × Path V A //
    Path.source Q t.2.2 = (E.placement t.1).color ∧
    Path.target Q t.2.2 = (F.placement t.2.1).color ∧
    (F.placement t.2.1).cochain = (E.placement t.1).cochain + n ∧
    Path.length t.2.2 = v + (E.placement t.1).internal - (F.placement t.2.1).internal}

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_CornerPath
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

abbrev CornerPath (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J) (r : ℤ) :=
  {t : I × J × Path V A //
    Path.source Q t.2.2 = (E.placement t.1).color ∧
    Path.target Q t.2.2 = (F.placement t.2.1).color ∧ Path.length t.2.2 = r}

noncomputable def purePathForget (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k) (r : ℤ) :
    (Σ v : {v // v ∈ homInternalSupport Q E F}, HomPath Q E F (k-l+r-v.val) v.val) →
      CornerPath Q E F r := fun x => ⟨x.2.val, x.2.property.1, x.2.property.2.1, by
        have hh := x.2.property.2.2
        have he := hE x.2.val.1
        have hf := hF x.2.val.2.1
        dsimp only [GeneratorPlacement.level] at he hf
        omega⟩

omit [Fintype V] [DecidableEq A] in
lemma purePathForget_injective (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k) (r : ℤ) :
    Function.Injective (purePathForget Q E F hE hF r) := by
  rintro ⟨⟨a,ha⟩,⟨ta,hta⟩⟩ ⟨⟨b,hb⟩,⟨tb,htb⟩⟩ hh
  have ht : ta=tb := congrArg Subtype.val hh
  subst tb
  have hab : a=b := by
    have h₁ := hta.2.2.2
    have h₂ := htb.2.2.2
    dsimp only at h₁ h₂
    omega
  subst b
  rfl

omit [Fintype V] [DecidableEq A] in
lemma purePathForget_surjective (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k) (r : ℤ) :
    Function.Surjective (purePathForget Q E F hE hF r) := by
  rintro ⟨⟨i,j,p⟩,hpt⟩
  let v := (F.placement j).internal - (E.placement i).internal + Path.length p
  have hv : v ∈ homInternalSupport Q E F := by
    rw [mem_homInternalSupport]
    rcases p with p | p | p
    · exact ⟨i,j,0,rfl⟩
    · exact ⟨i,j,1,rfl⟩
    · exact ⟨i,j,2,rfl⟩
  refine ⟨⟨⟨v,hv⟩, ⟨(i,j,p),hpt.1,hpt.2.1,?_,?check⟩⟩, rfl⟩
  · have he := hE i
    have hf := hF j
    have hp := hpt.2.2
    dsimp only [GeneratorPlacement.level] at he hf
    dsimp only at hp ⊢
    dsimp only [v]
    omega
  case check =>
    dsimp only [v]
    omega

noncomputable def purePathEquiv (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k) (r : ℤ) :
    (Σ v : {v // v ∈ homInternalSupport Q E F}, HomPath Q E F (k-l+r-v.val) v.val) ≃
      CornerPath Q E F r := Equiv.ofBijective (purePathForget Q E F hE hF r)
        ⟨purePathForget_injective Q E F hE hF r, purePathForget_surjective Q E F hE hF r⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_DownClosed
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

def DownClosed (E:BasedComplex Q (K:=K) I) (T:Set I) : Prop :=
  ∀ i∈T,∀ j,E.differential i j≠0→j∈T

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma DownClosed.low_condition {E:BasedComplex Q (K:=K) I} {T:Set I}
    (h:DownClosed Q E T) : ∀ i∈T,∀ j∈T,∀ k∉T,E.differential i k*E.differential k j=0 := by
  intro i hi j _ k hk
  have hz:E.differential i k=0 := Classical.not_not.mp (fun hn=>hk (h i hi k hn))
  rw [hz,zero_mul]

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma DownClosed.high_condition {E:BasedComplex Q (K:=K) I} {T:Set I}
    (h:DownClosed Q E T) : ∀ i∈Tᶜ,∀ j∈Tᶜ,∀ k∉Tᶜ,E.differential i k*E.differential k j=0 := by
  intro i _ j hj k hk
  have hk':k∈T:=Classical.not_not.mp hk
  have hz:E.differential k j=0 := Classical.not_not.mp (fun hn=>hj (h k hk' j hn))
  rw [hz,MulZeroClass.mul_zero]

def lowerLevelSet (E:BasedComplex Q (K:=K) I) (d:ℤ) : Set I := {i|(E.placement i).level≤d}

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_EqualColorPair
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

abbrev EqualColorPair (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J) :=
  {ij : I × J // (E.placement ij.1).color = (F.placement ij.2).color}

abbrev ArrowPair (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J) :=
  {t : I × J × A // Q.source t.2.2 = (E.placement t.1).color ∧
    Q.target t.2.2 = (F.placement t.2.1).color}

noncomputable def zeroCornerEquiv (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) : CornerPath Q E F 0 ≃ EqualColorPair Q E F where
  toFun x := ⟨(x.val.1,x.val.2.1), by
    rcases x with ⟨⟨i,j,p⟩,hs,ht,hl⟩
    rcases p with p | p | p
    · exact hs.symm.trans ht
    · simp only [Path.length] at hl; omega
    · simp only [Path.length] at hl; omega⟩
  invFun x := ⟨(x.val.1,x.val.2,Sum.inl (E.placement x.val.1).color),rfl,x.property,rfl⟩
  left_inv x := by
    apply Subtype.ext
    rcases x with ⟨⟨i,j,p⟩,hs,ht,hl⟩
    dsimp only
    rcases p with p | p | p
    · dsimp only [Path.source] at hs
      subst p
      rfl
    · simp only [Path.length] at hl; omega
    · simp only [Path.length] at hl; omega
  right_inv x := by rfl

noncomputable def tokenCornerEquiv (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) : CornerPath Q E F 2 ≃ EqualColorPair Q E F where
  toFun x := ⟨(x.val.1,x.val.2.1), by
    rcases x with ⟨⟨i,j,p⟩,hs,ht,hl⟩
    rcases p with p | p | p
    · simp only [Path.length] at hl; omega
    · simp only [Path.length] at hl; omega
    · exact hs.symm.trans ht⟩
  invFun x := ⟨(x.val.1,x.val.2,Sum.inr (Sum.inr (E.placement x.val.1).color)),rfl,x.property,rfl⟩
  left_inv x := by
    apply Subtype.ext
    rcases x with ⟨⟨i,j,p⟩,hs,ht,hl⟩
    dsimp only
    rcases p with p | p | p
    · simp only [Path.length] at hl; omega
    · simp only [Path.length] at hl; omega
    · dsimp only [Path.source] at hs
      subst p
      rfl
  right_inv x := by rfl

noncomputable def arrowCornerEquiv (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) : CornerPath Q E F 1 ≃ ArrowPair Q E F where
  toFun x := by
    rcases x with ⟨⟨i,j,p⟩,hs,ht,hl⟩
    rcases p with p | p | p
    · simp only [Path.length] at hl; omega
    · exact ⟨(i,j,p),hs,ht⟩
    · simp only [Path.length] at hl; omega
  invFun x := ⟨(x.val.1,x.val.2.1,Sum.inr (Sum.inl x.val.2.2)),x.property.1,x.property.2,rfl⟩
  left_inv x := by
    apply Subtype.ext
    rcases x with ⟨⟨i,j,p⟩,hs,ht,hl⟩
    rcases p with p | p | p
    · simp only [Path.length] at hl; omega
    · rfl
    · simp only [Path.length] at hl; omega
  right_inv x := by rfl

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

noncomputable def unfoldedCartan : Matrix V V ℝ := fun α β =>
  (if α = β then 2 else 0) - Nat.card {a : A // Q.source a = α ∧ Q.target a = β}

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_UnitTestVector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K I : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] [Fintype I]

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] in
lemma corner_length_zero {α β : V} (p : CornerPath Q α β) (h : Path.length p.val=0) :
    p.val = Sum.inl α := by
  rcases p with ⟨p,hs,ht⟩
  rcases p with v|a|v
  · exact congrArg Sum.inl hs
  · norm_num [Path.length] at h
  · norm_num [Path.length] at h

end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_LayerVector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

noncomputable def layerVector (E:BasedComplex Q (K:=K) I) (d:ℤ)
    (x:{i // (E.placement i).level=d}→K) : I→K := by
  classical
  exact fun i=>if h:(E.placement i).level=d then x ⟨i,h⟩ else 0

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_LowMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J L:Type u} [Fintype I] [Fintype J] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq L]
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

noncomputable def lowMatrix (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (M:Matrix I J (Q.Zigzag K)) (d:ℤ) :
    Matrix (lowerLevelSet Q E d) (lowerLevelSet Q F d) (Q.Zigzag K) :=
  fun i j=>M i j

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] [DecidableEq L] in
lemma lowMatrix_mul (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (G:BasedComplex Q (K:=K) L) (M:Matrix I J (Q.Zigzag K))
    (N:Matrix J L (Q.Zigzag K)) (d:ℤ)
    (hM:∀ i j,M i j≠0→(F.placement j).level≤(E.placement i).level) :
    lowMatrix Q E G (M*N) d=lowMatrix Q E F M d*lowMatrix Q F G N d := by
  apply Matrix.ext
  intro i k
  change (∑ j,M i j*N j k)=∑ j:lowerLevelSet Q F d,M i j*N j k
  symm
  apply Fintype.sum_of_injective (Subtype.val:lowerLevelSet Q F d→J) Subtype.val_injective
  · intro j hj
    have hz:M i j=0 := by
      by_contra hn
      have hi:(E.placement i).level≤d:=i.property
      exact hj ⟨⟨j,le_trans (hM i j hn) hi⟩,rfl⟩
    rw [hz,zero_mul]
  · intro j; rfl

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma lowMatrix_add (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (M N:Matrix I J (Q.Zigzag K)) (d:ℤ) :
    lowMatrix Q E F (M+N) d=lowMatrix Q E F M d+lowMatrix Q E F N d := rfl

omit [Fintype V] [DecidableEq A] in
lemma lowMatrix_identity (E:BasedComplex Q (K:=K) I) (d:ℤ) :
    lowMatrix Q E E (projectiveIdentity Q E.placement) d=
      projectiveIdentity Q (fun i:lowerLevelSet Q E d=>E.placement i) := by
  apply Matrix.ext; intro i j
  change (if (i:I)=(j:I) then vertexId Q (K:=K) (E.placement i).color else 0)=
    (if i=j then vertexId Q (K:=K) (E.placement i).color else 0)
  simp only [Subtype.val_inj]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_TermwiseSplitInjection
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J T : Type*} [Fintype I] [Fintype J] [Fintype T] [DecidableEq I]

structure TermwiseSplitInjection (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) where
  inclusion : Map Q E F
  retraction : Matrix J I (Q.Zigzag K)
  split : inclusion.matrix * retraction = projectiveIdentity Q E.placement

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_TwistNewTestIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I]

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] in
lemma corner_other_length {α β:V} (hne:β≠α) (p:Zigzag.CornerPath Q β α) :
    Path.length p.val=1 := by
  obtain ⟨p,hp,hq⟩:=p
  rcases p with v|a|v
  · exact (hne (hp.symm.trans hq)).elim
  · rfl
  · exact (hne (hp.symm.trans hq)).elim

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_OrderWeights
attribute [-instance] _root_.OAI.HarmonicArtin.orderWeightSupportLinearOrder
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_SimplexSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open Convexity
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

lemma simplexSupport_nonempty {n:ℕ} (z:StdSimplex ℝ (Fin (n+1))) :
    (simplexSupport z).Nonempty := by
  by_contra hn
  have hz:∀index,z.weights index=0:=by
    intro i
    by_contra h
    exact hn ⟨i,(mem_simplexSupport z i).mpr h⟩
  have ht:=z.total_of_fintype
  simp only [hz,Finset.sum_const_zero] at ht
  norm_num at ht

lemma simplexSupportDim_succ {n:ℕ} (z:StdSimplex ℝ (Fin (n+1))) :
    simplexSupportDim z+1=(simplexSupport z).card := by
  have :=(simplexSupport_nonempty z).card_pos
  unfold simplexSupportDim
  omega

noncomputable def simplexSupportEnum {n:ℕ} (z:StdSimplex ℝ (Fin (n+1))) :
    Fin (simplexSupportDim z+1) ≃o {i // i∈simplexSupport z} :=
  (simplexSupport z).orderIsoOfFin (simplexSupportDim_succ z).symm

noncomputable def simplexSupportInclusion {n:ℕ} (z:StdSimplex ℝ (Fin (n+1))) :
    Fin (simplexSupportDim z+1) →o Fin (n+1) :=
  ⟨fun i=>(simplexSupportEnum z i).val,fun _ _ h=>(simplexSupportEnum z).monotone h⟩

noncomputable def simplexSupported {n:ℕ} (z:StdSimplex ℝ (Fin (n+1))) :
    StdSimplex ℝ (Fin (simplexSupportDim z+1)) :=
  ⟨Finsupp.equivFunOnFinite.symm (fun index=>z.weights (simplexSupportInclusion z index)),
    fun index=>z.nonneg _,by
    rw [Finsupp.sum_fintype _ _ (by intros; rfl)]
    have he:=Equiv.sum_comp (simplexSupportEnum z).toEquiv (fun index=>z.weights index.val)
    change (∑index,z.weights (simplexSupportInclusion z index))=1
    rw [show (∑index,z.weights (simplexSupportInclusion z index))=
      ∑index:simplexSupport z,z.weights index.val from he]
    rw [Finset.sum_coe_sort]
    calc
      _ = ∑index,z.weights index := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        exact not_not.mp (fun h=>hi ((mem_simplexSupport z i).mpr h))
      _=1:=z.total_of_fintype⟩

lemma simplexSupported_map {n:ℕ} (z:StdSimplex ℝ (Fin (n+1))) :
    StdSimplex.map (simplexSupportInclusion z) (simplexSupported z)=z := by
  apply StdSimplex.ext
  apply Finsupp.ext
  intro index
  change Finsupp.mapDomain (simplexSupportInclusion z) (simplexSupported z).weights index =
    z.weights index
  by_cases supported:index∈simplexSupport z
  · let supportedIndex:Fin (simplexSupportDim z+1):=
      (simplexSupportEnum z).symm ⟨index,supported⟩
    have imageEq:simplexSupportInclusion z supportedIndex=index:=
      congrArg Subtype.val ((simplexSupportEnum z).apply_symm_apply ⟨index,supported⟩)
    have inclusionInjective:Function.Injective (simplexSupportInclusion z):=
      Subtype.val_injective.comp (simplexSupportEnum z).injective
    rw [← imageEq, Finsupp.mapDomain_apply inclusionInjective]
    rfl
  · have weightZero:z.weights index=0:=
      not_not.mp (fun nonzero=>supported ((mem_simplexSupport z index).mpr nonzero))
    rw [Finsupp.mapDomain_of_notMem_range, weightZero]
    rintro ⟨supportedIndex, imageEq⟩
    exact supported (imageEq ▸ (simplexSupportEnum z supportedIndex).property)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_WeightDim
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_NerveChain
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

noncomputable def nerveWeightsSimplex {n:SimplexCategory} (x:(nerve P).obj (op n)) :
    C(StdSimplex ℝ (Fin (n.len+1)),OrderWeights P) :=
  ⟨fun z=>orderWeightsOfChain (nerveChain x) z,orderWeightsChart_continuous x⟩

noncomputable def supportedWeightMap {n:ℕ} (x:Fin (n+1)→o P)
    (z:StdSimplex ℝ (Fin (n+1))) :
    Fin (simplexSupportDim z+1) →o Fin (weightDim (orderWeightsOfChain x z)+1) :=
  { toFun:=fun i=>(weightEnum (orderWeightsOfChain x z)).symm
      ⟨x (simplexSupportInclusion z i),chainWeights_support_positive x z (simplexSupportEnum z i).property⟩
    monotone':=fun _ _ h=>(weightEnum (orderWeightsOfChain x z)).symm.monotone
      (x.monotone ((simplexSupportInclusion z).monotone h)) }

lemma supportedWeightMap_chain {n:ℕ} (x:Fin (n+1)→o P)
    (z:StdSimplex ℝ (Fin (n+1))) :
    (weightChain (orderWeightsOfChain x z)).comp (supportedWeightMap x z)=
      x.comp (simplexSupportInclusion z) := by
  apply DFunLike.ext
  intro i
  change ((weightEnum (orderWeightsOfChain x z)) ((weightEnum (orderWeightsOfChain x z)).symm _)).val=_
  exact congrArg Subtype.val ((weightEnum (orderWeightsOfChain x z)).apply_symm_apply _)

lemma supportedWeightMap_simplex {n:ℕ} (x:Fin (n+1)→o P)
    (z:StdSimplex ℝ (Fin (n+1))) :
    StdSimplex.map (supportedWeightMap x z) (simplexSupported z)=
      weightSimplex (orderWeightsOfChain x z) := by
  apply chainWeights_coordinates_injective _ (weightChain_injective _)
  rw [← chainWeights_natural,supportedWeightMap_chain,chainWeights_natural,simplexSupported_map]
  exact congrArg OrderWeights.weights (orderWeightsOfChain_canonical (orderWeightsOfChain x z)).symm

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_WeightMap
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

noncomputable def weightMapContinuous (f:P→oQ) : C(OrderWeights P,OrderWeights Q) :=
  ⟨weightMap f,weightMap_continuous f⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FiniteChainEnum
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_WeightCarrier
attribute [-instance] _root_.OAI.HarmonicArtin.finiteLinearWeightsCompact _root_.OAI.HarmonicArtin.orderWeightSupportLinearOrder
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_WeightDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

lemma weightDual_continuous : Continuous (weightDual (P:=P)) := by
  rw [orderWeights_continuous_iff]
  intro n x
  let c:=nerveChain x
  let C:Finset Pᵒᵈ:=Finset.univ.image c
  have hc:IsChain (·≤·) (↑C:Set Pᵒᵈ):=by
    rintro a ha b hb hn
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp ha
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hb
    exact (le_total i j).symm.imp (fun h=>c.monotone h) (fun h=>c.monotone h)
  have hne:C.Nonempty:=Finset.Nonempty.image Finset.univ_nonempty _
  apply continuous_of_finite_chain_carrier _ C hc hne
  · intro z
    exact chainWeights_support c z
  · intro p
    exact (weightEval_continuous (P:=P) p).comp (chainWeightsChart_continuous c)

noncomputable def weightDualHomeomorph : OrderWeights P≃ₜOrderWeights Pᵒᵈ where
  toFun:=weightDual
  invFun:=weightDual
  left_inv _:=rfl
  right_inv _:=rfl
  continuous_toFun:=weightDual_continuous
  continuous_invFun:=weightDual_continuous

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_ConeWeights
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_WeightHomeomorph
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_EarlyDelay
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_LateDelay
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.orderWeightSupportLinearOrder
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_ConeAttachmentRel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.orderWeightSupportLinearOrder
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_WeightOld
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_WeightLinearLinkInverse
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

theorem continuous_of_weightParts {P:Type u} [PartialOrder P] {Y:Type v} [TopologicalSpace Y]
    (v:P) (f:OrderWeights P→Y)
    (hOld:Continuous (f ∘ weightOldMap v))
    (hCone:Continuous (f ∘ weightConeMap v)) : Continuous f := by
  rw [orderWeights_continuous_iff]
  intro n x
  let a:Fin (n.len+1)→o P:=nerveChain x
  let C:Finset P:=Finset.univ.image a
  have hC:IsChain (·<·) (↑C:Set P):=by
    intro p hp q hq hne
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hp
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hq
    exact (le_total i j).imp (fun hle=>lt_of_le_of_ne (a.monotone hle) hne)
      (fun hle=>lt_of_le_of_ne (a.monotone hle) hne.symm)
  have ha (i:Fin (n.len+1)):a i∈C:=Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  by_cases hv:v∈C
  · by_cases hn:(C.erase v).Nonempty
    · let _ := IsChain.linearOrder (show IsChain (·≤·) (↑C:Set P) from
        fun x hx y hy hne => (hC hx hy hne).imp le_of_lt le_of_lt)
      let rv:C:=⟨v,hv⟩
      let j:C→oP:=⟨Subtype.val,fun _ _ h=>h⟩
      let aC:Fin (n.len+1)→o C:=⟨fun i=>⟨a i,ha i⟩,fun _ _ h=>a.monotone h⟩
      obtain ⟨b,hb⟩:=hn
      let c:WeightLink rv:=⟨⟨b,(Finset.mem_erase.mp hb).2⟩,
        (by intro h;exact (Finset.mem_erase.mp hb).1 (congrArg Subtype.val h)),le_total _ _⟩
      let je:C↪oP:=OrderEmbedding.subtype (·∈C)
      have hf:Continuous (f ∘ weightMap j):=
        continuous_comp_weightEmbedding je rv (weightVertex c) f hCone
      have hh:=hf.comp (chainWeightsChart_continuous aC)
      change Continuous (fun z=>f (weightMap j (orderWeightsOfChain aC z))) at hh
      simp_rw [weightMap_chain] at hh
      have hj:j.comp aC=nerveChain x:=by ext i;rfl
      rw [hj] at hh
      exact hh
    · have hs:C⊆{v}:=by
        intro p hp
        by_contra hh
        have hpv:p≠v:=by simpa only [Finset.mem_singleton] using hh
        exact hn ⟨p,Finset.mem_erase.mpr ⟨hpv,hp⟩⟩
      have he (z:Convexity.StdSimplex ℝ (Fin (n.len+1))) : orderWeightsOfChain a z=weightVertex v:=
        weight_support_singleton _ _ ((chainWeights_support a z).trans hs)
      simp_rw [show nerveChain x=a from rfl,he]
      exact continuous_const
  · let aO:Fin (n.len+1)→o WeightOld v:=
      ⟨fun i=>⟨a i,(by intro h;exact hv (h ▸ ha i))⟩,fun _ _ h=>a.monotone h⟩
    have hh:=hOld.comp (chainWeightsChart_continuous aO)
    change Continuous (fun z=>f (weightMap (weightOldIncl v) (orderWeightsOfChain aO z))) at hh
    simp_rw [weightMap_chain] at hh
    have hj:(weightOldIncl v).comp aO=nerveChain x:=by ext i;rfl
    rw [hj] at hh
    exact hh

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_WeightAttach
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

noncomputable def weightAttachHomeomorph (c:OrderWeights (WeightLink v)) :
    ConeAttachment (weightLinkMap v) ≃ₜ OrderWeights P where
  toEquiv:=weightAttachEquiv v c
  continuous_toFun:=(weightAttach v).continuous
  continuous_invFun:=by
    change Continuous (weightAttachEquiv v c).symm
    apply continuous_of_weightParts v
    · have he:(weightAttachEquiv v c).symm ∘ weightOldMap v=coneAttachmentOld (weightLinkMap v):=by
        funext w;exact weightAttachEquiv_symm_old v c w
      rw [he]
      exact (coneAttachmentOld (weightLinkMap v)).continuous
    · have he:(weightAttachEquiv v c).symm ∘ weightConeMap v=coneAttachmentCone (weightLinkMap v):=by
        funext w;exact weightAttachEquiv_symm_cone v c w
      rw [he]
      exact (coneAttachmentCone (weightLinkMap v)).continuous

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_WeightVertexRetract
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

noncomputable def weightVertexRetract : C(OrderWeights P,OrderWeights (WeightOld v)) :=
  (coneAttachmentRetract (weightLinkMap v) c H).comp ⟨(weightAttachHomeomorph v c).symm,(weightAttachHomeomorph v c).symm.continuous⟩

noncomputable def weightVertexDeformation :
    ContinuousMap.HomotopyRel (ContinuousMap.id (OrderWeights P))
      ((weightOldMap v).comp (weightVertexRetract v c H)) (Set.range (weightOldMap v)) where
  toFun p:=weightAttach v (coneAttachmentDeformation (weightLinkMap v) c H
    (p.1,(weightAttachHomeomorph v c).symm p.2))
  continuous_toFun:=(weightAttach v).continuous.comp
    ((coneAttachmentDeformation (weightLinkMap v) c H).continuous.comp
      (continuous_fst.prodMk ((weightAttachHomeomorph v c).symm.continuous.comp continuous_snd)))
  map_zero_left:=by
    intro w
    rw [(coneAttachmentDeformation (weightLinkMap v) c H).apply_zero]
    exact (weightAttachHomeomorph v c).apply_symm_apply w
  map_one_left:=by
    intro w
    rw [(coneAttachmentDeformation (weightLinkMap v) c H).apply_one]
    rfl
  prop' t w hw:=by
    obtain ⟨a,rfl⟩:=hw
    change weightAttach v (coneAttachmentDeformation (weightLinkMap v) c H
      (t,(weightAttachEquiv v c).symm (weightOldMap v a)))=_
    rw [weightAttachEquiv_symm_old]
    rw [(coneAttachmentDeformation (weightLinkMap v) c H).eq_fst t ⟨a,rfl⟩]
    rfl

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

lemma weightVertexDelay_zero (w:OrderWeights P) :
    weightVertexDelay v w=0↔w∈Set.range (weightOldMap v) := by
  constructor
  · intro h
    have hz:w.weights v=0:=by
      have he:=congrArg Subtype.val h
      change w.weights v/2=0 at he
      linarith
    exact weightOld_surjective_zero w hz
  · rintro ⟨w,rfl⟩
    apply Subtype.ext
    change (weightOldMap v w).weights v/2=0
    rw [weightOldMap_at,zero_div]

variable (a:OrderWeights (WeightOld v))
  (K:ContinuousMap.Homotopy (ContinuousMap.id _) (ContinuousMap.const _ a))

noncomputable def weightExtendContraction :
    ContinuousMap.Homotopy (ContinuousMap.id (OrderWeights P))
      (ContinuousMap.const _ (weightOldMap v a)) :=
  extendContraction (weightOldMap v) (weightVertexRetract v c H)
    (weightVertexDeformation v c H) (weightVertexDelay v)
    (weightVertexDelay_lt v) (weightVertexDelay_zero v) a K

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_InsertOldIso
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

variable (A:Set P) (v:P) (hv:v∉A)
  (l:OrderWeights (WeightLink (⟨v,Set.mem_insert v A⟩:↥(insert v A))))
  (L:ContinuousMap.Homotopy (ContinuousMap.id _) (ContinuousMap.const _ l))
  (a:OrderWeights A) (H:ContinuousMap.Homotopy (ContinuousMap.id _) (ContinuousMap.const _ a))

noncomputable def weightInsertContraction :
    ContinuousMap.Homotopy (ContinuousMap.id (OrderWeights ↥(insert v A)))
      (ContinuousMap.const _ (weightMap (weightSubset A (insert v A) (Set.subset_insert v A)) a)) := by
  let e:=weightHomeomorph (insertOldIso A v hv)
  let K:=transportContraction e a H
  let E:=weightExtendContraction (⟨v,Set.mem_insert v A⟩:↥(insert v A)) l L (e a) K
  refine E.cast rfl ?_
  apply ContinuousMap.ext
  intro w
  change weightMap (weightOldIncl _) (weightMap (OrderHomClass.toOrderHom (insertOldIso A v hv)) a)=_
  rw [weightMap_comp,insertOldIso_incl]
  rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_WeightMapCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval
open Simplicial

universe u v w z
variable {P:Type u} [PartialOrder P] {J:Type v} {Q:J→Type u} [∀j,PartialOrder (Q j)]
  (f:∀j,Q j→oP) {Z:Type w} [TopologicalSpace Z] [LocallyCompactSpace Z]
  {Y:Type z} [TopologicalSpace Y]

lemma weightMapCover_rep (hf:WeightMapCover f) (w:OrderWeights P) :
    ∃i:J,∃z:OrderWeights (Q i),weightMap (f i) z=w := by
  obtain ⟨i,b,hb⟩:=hf (weightDim w) (weightChain w)
  refine ⟨i,orderWeightsOfChain b (weightSimplex w),?_⟩
  rw [weightMap_chain,hb]
  exact orderWeightsOfChain_canonical w

noncomputable def weightMapGlueIndex (hf:WeightMapCover f) (w:OrderWeights P) : J :=
  (weightMapCover_rep f hf w).choose
noncomputable def weightMapGlueRep (hf:WeightMapCover f) (w:OrderWeights P) : OrderWeights (Q (weightMapGlueIndex f hf w)) :=
  (weightMapCover_rep f hf w).choose_spec.choose
lemma weightMapGlueRep_map (hf:WeightMapCover f) (w:OrderWeights P) :
    weightMap (f _) (weightMapGlueRep f hf w)=w :=
  (weightMapCover_rep f hf w).choose_spec.choose_spec

variable (F:∀i:J,C(Z×OrderWeights (Q i),Y))

def WeightMapCompatible : Prop :=
  ∀(i j:J) (wi:OrderWeights (Q i)) (wj:OrderWeights (Q j)),
    weightMap (f i) wi=weightMap (f j) wj → ∀t:Z,F i (t,wi)=F j (t,wj)

noncomputable def weightMapGlueValue (hf:WeightMapCover f) (p:Z×OrderWeights P) : Y :=
  F (weightMapGlueIndex f hf p.2) (p.1,weightMapGlueRep f hf p.2)

omit [LocallyCompactSpace Z] in
lemma weightMapGlueValue_on (hf:WeightMapCover f) (hF:WeightMapCompatible f F)
    (i:J) (p:Z×OrderWeights (Q i)) :
    weightMapGlueValue f F hf (p.1,weightMap (f i) p.2)=F i p := by
  exact hF _ _ _ _ (weightMapGlueRep_map f hf _) _

lemma weightMapGlueValue_continuous (hf:WeightMapCover f) (hF:WeightMapCompatible f F) :
    Continuous (weightMapGlueValue f F hf) := by
  apply orderWeights_prod_continuous
  intro n x
  obtain ⟨i,b,hb⟩:=hf n.len (nerveChain x)
  have he (z:Convexity.StdSimplex ℝ (Fin (n.len+1))) :
      weightMap (f i) (orderWeightsOfChain b z)=orderWeightsOfChain (nerveChain x) z := by
    rw [weightMap_chain,hb]
  have hc:Continuous (fun p:Z×Convexity.StdSimplex ℝ (Fin (n.len+1))=>F i (p.1,orderWeightsOfChain b p.2)):=
    (F i).continuous.comp (continuous_fst.prodMk ((chainWeightsChart_continuous b).comp continuous_snd))
  apply hc.congr
  intro p
  rw [←he]
  exact (weightMapGlueValue_on f F hf hF i (p.1,orderWeightsOfChain b p.2)).symm

noncomputable def weightMapGlue (hf:WeightMapCover f) (hF:WeightMapCompatible f F) : C(Z×OrderWeights P,Y) :=
  ⟨weightMapGlueValue f F hf,weightMapGlueValue_continuous f F hf hF⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_UnionCarrier
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

include hc hne in
lemma union_finset_cover (s:Finset P) (hs:∀x∈s,x∈unionCarrier C) :
    ∃a∈C,∀x∈s,x∈a.carrier := by
  induction s using Finset.induction_on with
  | empty => obtain ⟨a,ha⟩:=hne;exact ⟨a,ha,by simp⟩
  | @insert x s hx ih =>
    obtain ⟨a,ha,haC⟩:=ih (fun y hy=>hs y (Finset.mem_insert_of_mem hy))
    obtain ⟨b,hb,hxb⟩:=hs x (Finset.mem_insert_self x s)
    rcases hc.total ha hb with hab|hba
    · refine ⟨b,hb,?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl|hy
      · exact hxb
      · exact hab.choose (haC y hy)
    · refine ⟨a,ha,?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl|hy
      · exact hba.choose hxb
      · exact haC y hy

noncomputable def unionIncl (a:C) : a.val.carrier→o unionCarrier C :=
  weightSubset _ _ (subset_union C a.property)

lemma unionIncl_ambient (a:C) : (weightInclusion (unionCarrier C)).comp (unionIncl C a)=a.val.inclusion :=rfl

include hc hne in
lemma union_map_cover : WeightMapCover (unionIncl C) := by
  intro n a
  obtain ⟨b,hb,hcover⟩:=union_finset_cover C hc hne
    (Finset.univ.image (fun i=> (a i).val)) (by
      intro x hx
      obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
      exact (a i).property)
  let d:Fin (n+1)→o b.carrier:=⟨fun i=>⟨(a i).val,hcover _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)⟩,
    fun _ _ h=>a.monotone h⟩
  exact ⟨⟨b,hb⟩,d,by ext i;rfl⟩

noncomputable def unionLocal (a:C) : C(I×OrderWeights a.val.carrier,OrderWeights (unionCarrier C)) :=
  (weightMapContinuous (unionIncl C a)).comp a.val.hom.toContinuousMap

include hc in
lemma union_compatible : WeightMapCompatible (unionIncl C) (unionLocal C) := by
  intro a b w z he t
  apply weightMap_injective (weightInclusion (unionCarrier C)) Subtype.val_injective
  change weightMap (weightInclusion _) (weightMap (unionIncl C a) (a.val.hom (t,w)))=
    weightMap (weightInclusion _) (weightMap (unionIncl C b) (b.val.hom (t,z)))
  simp only [weightMap_comp,unionIncl_ambient]
  have hW:weightMap a.val.inclusion w=weightMap b.val.inclusion z:=by
    have hh:=congrArg (weightMap (weightInclusion (unionCarrier C))) he
    simpa only [weightMap_comp,unionIncl_ambient] using hh
  rcases hc.total a.property b.property with hab|hba
  · exact extends_compare hab w z hW t
  · exact (extends_compare hba z w hW.symm t).symm

noncomputable def unionMap : C(I×OrderWeights (unionCarrier C),OrderWeights (unionCarrier C)) :=
  weightMapGlue (unionIncl C) (unionLocal C) (union_map_cover C hc hne) (union_compatible C hc)

lemma unionMap_on (a:C) (t:I) (w:OrderWeights a.val.carrier) :
    unionMap C hc hne (t,weightMap (unionIncl C a) w)=weightMap (unionIncl C a) (a.val.hom (t,w)) :=
  weightMapGlueValue_on (unionIncl C) (unionLocal C) (union_map_cover C hc hne) (union_compatible C hc) a (t,w)

noncomputable def union : WeightContractionPiece r c where
  carrier:=unionCarrier C
  root_mem:=by obtain ⟨a,ha⟩:=hne;exact ⟨a,ha,a.root_mem⟩
  down:=by
    intro x y hx h
    obtain ⟨a,ha,hx⟩:=hx
    exact ⟨a,ha,a.down hx h⟩
  hom:={
    toContinuousMap:=unionMap C hc hne
    map_zero_left:=by
      intro w
      obtain ⟨a,z,rfl⟩:=weightMapCover_rep (unionIncl C) (union_map_cover C hc hne) w
      change unionMap C hc hne (0,weightMap (unionIncl C a) z)=_
      rw [unionMap_on,a.val.hom.apply_zero]
      rfl
    map_one_left:=by
      intro w
      obtain ⟨a,z,rfl⟩:=weightMapCover_rep (unionIncl C) (union_map_cover C hc hne) w
      change unionMap C hc hne (1,weightMap (unionIncl C a) z)=_
      rw [unionMap_on,a.val.hom.apply_one]
      exact weightMap_vertex _ _ }

end WeightContractionPiece
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_Initial
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

noncomputable def successor : WeightContractionPiece r c where
  carrier:=insert v a.carrier
  root_mem:=Set.mem_insert_of_mem v a.root_mem
  down:=by
    intro x y hx hy
    rcases Set.mem_insert_iff.mp hx with hx|hx
    · subst x
      exact Set.mem_insert_of_mem v ((heA y).mpr hy)
    · exact Set.mem_insert_of_mem v (a.down hx hy)
  hom:=by
    let E:=weightInsertContraction a.carrier v hv
      (insertLinkContractionPoint wf a v heA hlink) (insertLinkContraction wf a v heA hlink)
      (weightVertex ⟨c,a.root_mem⟩) a.hom
    refine E.cast rfl ?_
    apply ContinuousMap.ext
    intro w
    exact weightMap_vertex _ _

end WeightContractionPiece

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_BinaryProductBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {A B:Type u} [PartialOrder A] [PartialOrder B] [OrderTop A] [OrderTop B]

noncomputable def binaryBoundarySliceIso :
    {x:BinaryProductBoundary A B //x.val.1≠⊤} ≃o BinaryProductBox (⊤:A×B) where
  toFun x:=⟨x.val.val,le_top,x.property⟩
  invFun x:=⟨⟨x.val,by intro he;exact x.property.2 (congrArg Prod.fst he)⟩,x.property.2⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=by intros;rfl

noncomputable def binaryBoundaryFiberIso (v:BinaryProductBoundary A B) (hv:v.val.1=⊤) :
    {x:BinaryProductBoundary A B //x.val.1≠⊤ ∧ x<v} ≃o BinaryProductBox v.val where
  toFun x:=⟨x.val.val,x.property.2.le,x.property.1⟩
  invFun x:=⟨⟨x.val,by intro he;exact x.property.2 (congrArg Prod.fst he)⟩,x.property.2,by
    apply lt_of_le_of_ne x.property.1
    intro he
    exact x.property.2 ((congrArg Prod.fst he).trans hv)⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=by intros;rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_LengthCases
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Path

variable {V A : Type*}

lemma length_cases (p : Path V A) : p.length = 0 ∨ p.length = 1 ∨ p.length = 2 := by
  rcases p with v | a | v
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

end HarmonicArtin.ReversibleQuiver.Path

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_TokenTestVector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K I : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] [Fintype I]

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] in
lemma corner_length_two {α β : V} (p : CornerPath Q α β) (h : Path.length p.val=2) :
    p.val = Sum.inr (Sum.inr α) := by
  rcases p with ⟨p,hs,ht⟩
  rcases p with v|a|v
  · norm_num [Path.length] at h
  · norm_num [Path.length] at h
  · exact congrArg (fun v => Sum.inr (Sum.inr v)) hs

end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_SignDiagonal
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

noncomputable def fusionD0 : ℝ := ∑ L : FusionLabel m, (fusionWeight m L)^2

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionColorWord
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

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V:Type} {K:Type*} [Field K]
  [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E→ℕ) (d:V→V→FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)

noncomputable def fusionColorWord (j:V) : List (FusionVertex (V:=V) m) :=
  (Finset.univ:Finset (FusionLabel m)).toList.map fun L=>(j,L)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionQuiverSimpleEdge
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.labelSplit_apply _root_.OAI.HarmonicArtin.labelSplit_symm_at _root_.OAI.HarmonicArtin.labelSplit_symm_rest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m : E → ℕ) (d : V → V → FusionEdge E) (hd : ∀ s t, d s t = d t s)

noncomputable def fusionOrdinaryMatrix : CoxeterMatrix (FusionVertex (V := V) m) where
  M α β := if α=β then 1 else
    if (d α.1 β.1).multiplicity m α.2 β.2 = 0 then 2 else
    if (d α.1 β.1).multiplicity m α.2 β.2 = 1 then 3 else 0
  isSymm := by
    apply Matrix.ext
    intro α β
    change (if β = α then 1 else if (d β.1 α.1).multiplicity m β.2 α.2 = 0 then 2 else if (d β.1 α.1).multiplicity m β.2 α.2 = 1 then 3 else 0) = (if α = β then 1 else if (d α.1 β.1).multiplicity m α.2 β.2 = 0 then 2 else if (d α.1 β.1).multiplicity m α.2 β.2 = 1 then 3 else 0)
    rw [hd β.1 α.1, FusionEdge.multiplicity_symm m _ β.2 α.2]
    by_cases h : α = β <;> simp only [h, eq_comm, ite_true, if_true, ite_false, if_false]
  diagonal α := by simp
  off_diagonal α β h := by
    simp only [ite_eq_right h]
    split_ifs <;> norm_num

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_MaximalReducedMonoidPrefix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveDegree_generator _root_.OAI.HarmonicArtin.positiveDegree_mul _root_.OAI.HarmonicArtin.positiveDegree_one _root_.OAI.HarmonicArtin.positiveDegree_word _root_.OAI.HarmonicArtin.positiveSimpleLift_one _root_.OAI.HarmonicArtin.positiveSimpleLift_simple _root_.OAI.HarmonicArtin.positiveToCoxeter_generator _root_.OAI.HarmonicArtin.positiveToCoxeter_simpleLift _root_.OAI.HarmonicArtin.positiveToCoxeter_word
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
lemma maximal_reduced_monoid_prefix (s:S) (w:List S) :
    ∃ u v:List S, M.toCoxeterSystem.IsReduced u ∧
      wordPositive M (s::w)=wordPositive M u*wordPositive M v ∧
      u.length+v.length=(s::w).length ∧ 0<u.length ∧
      ∀ u' v':List S,M.toCoxeterSystem.IsReduced u'→
        wordPositive M (s::w)=wordPositive M u'*wordPositive M v'→
        u'.length+v'.length=(s::w).length→u'.length≤u.length := by
  let P:ℕ→Prop:=fun n=>∃u v:List S,M.toCoxeterSystem.IsReduced u ∧
    wordPositive M (s::w)=wordPositive M u*wordPositive M v ∧
    u.length+v.length=(s::w).length ∧ u.length=n
  have hP:P 1 := by
    refine ⟨[s],w,?_,?_,by simp [Nat.add_comm],rfl⟩
    · change M.toCoxeterSystem.length (M.toCoxeterSystem.simple s)=1
      exact M.toCoxeterSystem.length_simple s
    · simp [wordPositive]
  have hb:1≤(s::w).length:=by simp
  obtain ⟨u,v,hu,he,hl,hmax⟩:=Nat.findGreatest_spec hb hP
  refine ⟨u,v,hu,he,hl,?_,?_⟩
  · have hh:=Nat.le_findGreatest hb hP
    omega
  · intro u' v' hu' he' hl'
    rw [hmax]
    exact Nat.le_findGreatest (by omega) ⟨u',v',hu',he',hl',rfl⟩

lemma reduced_monoid_left_factor (w:List S) (s:S) (hw:M.toCoxeterSystem.IsReduced w)
    (h:¬M.toCoxeterSystem.IsReduced (s::w)) :
    ∃v:List S,M.toCoxeterSystem.IsReduced v ∧
      wordPositive M w=positiveGenerator M s*wordPositive M v ∧ v.length+1=w.length := by
  let cs:=M.toCoxeterSystem
  have hd:cs.IsLeftDescent (cs.wordProd w) s := by
    by_contra hn
    apply h
    change cs.length (cs.simple s*cs.wordProd w)=w.length+1
    rw [cs.not_isLeftDescent_iff.mp hn,hw.eq]
  obtain ⟨v,hv,he⟩:=cs.exists_isReduced (cs.simple s*cs.wordProd w)
  have hp:cs.wordProd (s::v)=cs.wordProd w := by
    rw [cs.wordProd_cons,←he,cs.simple_mul_simple_cancel_left]
  have hl:v.length+1=w.length := by
    rw [←hv.eq,←he,←hw.eq]
    exact cs.isLeftDescent_iff.mp hd
  have hr:cs.IsReduced (s::v) := by
    change cs.length (cs.wordProd (s::v))=v.length+1
    rw [hp,hw.eq,hl]
  refine ⟨v,hv,?_,hl⟩
  exact wordPositive_eq_of_reduced M w (s::v) hw hr hp.symm

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_MaximalReducedPositivePrefix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeArtinHom_generator _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word
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
lemma maximal_reduced_positive_prefix (s:S) (w:List S) :
    ∃ u v:List S, M.toCoxeterSystem.IsReduced u ∧
      wordArtin M (s::w)=wordArtin M u*wordArtin M v ∧
      u.length+v.length=(s::w).length ∧ 0<u.length ∧
      ∀ u' v':List S,M.toCoxeterSystem.IsReduced u'→
        wordArtin M (s::w)=wordArtin M u'*wordArtin M v'→
        u'.length+v'.length=(s::w).length→u'.length≤u.length := by
  let P:ℕ→Prop:=fun n=>∃u v:List S,M.toCoxeterSystem.IsReduced u ∧
    wordArtin M (s::w)=wordArtin M u*wordArtin M v ∧
    u.length+v.length=(s::w).length ∧ u.length=n
  have hP:P 1 := by
    refine ⟨[s],w,?_,?_,by simp [Nat.add_comm],rfl⟩
    · change M.toCoxeterSystem.length (M.toCoxeterSystem.simple s)=1
      exact M.toCoxeterSystem.length_simple s
    · simp [wordArtin]
  have hb:1≤(s::w).length:=by simp
  obtain ⟨u,v,hu,he,hl,hmax⟩:=Nat.findGreatest_spec hb hP
  refine ⟨u,v,hu,he,hl,?_,?_⟩
  · have hh:=Nat.le_findGreatest hb hP
    omega
  · intro u' v' hu' he' hl'
    rw [hmax]
    exact Nat.le_findGreatest (by omega) ⟨u',v',hu',he',hl',rfl⟩

lemma reduced_left_factor (w:List S) (s:S) (hw:M.toCoxeterSystem.IsReduced w)
    (h:¬M.toCoxeterSystem.IsReduced (s::w)) :
    ∃v:List S,M.toCoxeterSystem.IsReduced v ∧
      wordArtin M w=generator M s*wordArtin M v ∧ v.length+1=w.length := by
  let cs:=M.toCoxeterSystem
  have hd:cs.IsLeftDescent (cs.wordProd w) s := by
    by_contra hn
    apply h
    change cs.length (cs.simple s*cs.wordProd w)=w.length+1
    rw [cs.not_isLeftDescent_iff.mp hn,hw.eq]
  obtain ⟨v,hv,he⟩:=cs.exists_isReduced (cs.simple s*cs.wordProd w)
  have hp:cs.wordProd (s::v)=cs.wordProd w := by
    rw [cs.wordProd_cons,←he,cs.simple_mul_simple_cancel_left]
  have hl:v.length+1=w.length := by
    rw [←hv.eq,←he,←hw.eq]
    exact cs.isLeftDescent_iff.mp hd
  have hr:cs.IsReduced (s::v) := by
    change cs.length (cs.wordProd (s::v))=v.length+1
    rw [hp,hw.eq,hl]
  refine ⟨v,hv,?_,hl⟩
  exact wordArtin_eq_of_reduced M w (s::v) hw hr hp.symm

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_WordFrontData
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

def WordFrontData (u v:List S) : Prop :=
  wordPositive M u=wordPositive M v ∧ u.length=v.length ∧
    ∀s us t vs,u=s::us→v=t::vs→FrontLinked M (wordPositive M u) s t

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

def IsFrontHead (a:PositiveArtin M) (s:S) (h:M.Group) : Prop :=
  PositivePrefix M (positiveSimpleLift M h) a ∧
    PositivePrefix M (positiveGenerator M s) (positiveSimpleLift M h) ∧
    ∀w:M.Group,PositivePrefix M (positiveSimpleLift M w) a→
      PositivePrefix M (positiveGenerator M s) (positiveSimpleLift M w)→
      PositivePrefix M (positiveSimpleLift M w) (positiveSimpleLift M h)

end HarmonicArtin

end OAI
end


