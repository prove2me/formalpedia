-- Prove2me | Definitions.Def_OAIQ225Ag007
-- name    : OAIQ225Ag007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:24:26.62576+00:00
-- url     : https://prove2.me/theorems/d0ced62d-c303-497a-91a5-f3d265958eb8
-- title:
--   Definitions bundle OAIQ225Ag007 of the split of OpenAI, Harmonic heights and the Artin K(pi,1) conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HarmonicArtin.salvetti_cover_contractible`, carved from OpenAI's openai/math development (OpenAI, *Harmonic heights and the Artin K(pi,1) conjecture*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 255 declarations of OpenAI's Lean: 94 definitions, 3 inductive types or structures, 4 instances and 154 theorems. The definitions and types are `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ClassCone`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ClassOutsideCap`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ClassOutsideFloor`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ClassTestExact`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ClassTestUpper`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.EqualColorPair`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.FiniteModel.positiveWord`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.FiniteModel.positiveWordMap`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.HomPath`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.HomotopyEquivalence.coneSource`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.HomotopyEquivalence.coneTarget`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.HomotopyEquivalence.negativeTwistModern`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.HomotopyEquivalence.positiveTwistModern`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.HomotopyEquivalence.test`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map.homotopyConeMap`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map.inverseMatrix`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map.scalarMatrix`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.NegativeAmplitudeCoreIndex`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.PlacementSupported`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.PositiveBraidRel`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ScalarKernel`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.TestUpperBound`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.UnfoldedPresentation`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.allPureIndex`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.blockInclusionMap`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.blockProjectionMap`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.canonicalLowTarget`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.coefficientOutgoing`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.diagonalToken`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.diagonalVertex`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.emptyTestIndex`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.extendLayer`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.generatorTokenTest`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homInternalSupport`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseWordAction`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.layerVector`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.leftMatrix`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.linearHomDifferential`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeConeIndex`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeConeSign` and 57 more.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `ArtinGroups_Complexes_BlockClosed`, `ArtinGroups_Complexes_Capped`, `ArtinGroups_Complexes_CoefficientSocle`, `ArtinGroups_Complexes_CoefficientTopDual`, `ArtinGroups_Complexes_ColorSupport`, `ArtinGroups_Complexes_Cone`, `ArtinGroups_Complexes_Cone2`, `ArtinGroups_Complexes_DiagonalVertex`, `ArtinGroups_Complexes_EmptyTestIndex`, `ArtinGroups_Complexes_EqualColorPair`, `ArtinGroups_Complexes_ExtendLayer`, `ArtinGroups_Complexes_GeneratorTokenTest`, `ArtinGroups_Complexes_GeneratorVector`, `ArtinGroups_Complexes_HomInternalSupport`, `ArtinGroups_Complexes_HomPath`, `ArtinGroups_Complexes_HomSpaceDuality`, `ArtinGroups_Complexes_HomSpacePairing`, `ArtinGroups_Complexes_HomotopyConeMap`, `ArtinGroups_Complexes_InverseMatrix`, `ArtinGroups_Complexes_InverseWordAction`, `ArtinGroups_Complexes_LayerVector`, `ArtinGroups_Complexes_LeftMatrix`, `ArtinGroups_Complexes_NegativeAmplitudeCoreIndex`, `ArtinGroups_Complexes_NegativeConeIndex`, `ArtinGroups_Complexes_NegativeTwistModern`, `ArtinGroups_Complexes_OutsideCap`, `ArtinGroups_Complexes_PlacedProjective`, `ArtinGroups_Complexes_PlacementSignedWeight`, `ArtinGroups_Complexes_PositiveConeIndex`, `ArtinGroups_Complexes_PositiveTwistModern`, `ArtinGroups_Complexes_PositiveTwistOtherTest2`, `ArtinGroups_Complexes_PositiveTwistOtherTest3`, `ArtinGroups_Complexes_PositiveWord`, `ArtinGroups_Complexes_PositiveWordActionTest`, `ArtinGroups_Complexes_RestrictExtendLayerMul`, `ArtinGroups_Complexes_RestrictLayer`, `ArtinGroups_Complexes_ScalarExactNotZero`, `ArtinGroups_Complexes_ScalarKernel`, `ArtinGroups_Complexes_ScalarSupported`, `ArtinGroups_Complexes_ScalarSupportedCochainShift`, `ArtinGroups_Complexes_ScalarSupportedTokenShift`, `ArtinGroups_Complexes_Test`, `ArtinGroups_Complexes_TestComplexVertexDifferential`, `ArtinGroups_Complexes_TestExact`, `ArtinGroups_Complexes_TestUpperBound`, `ArtinGroups_Complexes_TokenShift`, `ArtinGroups_Complexes_TwistNewTestIndex`, `ArtinGroups_Complexes_UnfoldedPresentation`, `ArtinGroups_Complexes_WordInverseModel`, `ArtinGroups_Coxeter_PositiveBraidRel`, `ArtinGroups_Harmonic_ArtinReindex`, `ArtinGroups_Harmonic_Candidate`, `ArtinGroups_Harmonic_Coset`, `ArtinGroups_Harmonic_FiniteArtinPositiveLeft`, `ArtinGroups_Harmonic_Initial`, `ArtinGroups_Harmonic_InsertOldIso`, `ArtinGroups_Harmonic_PositiveLiftSimple`, `ArtinGroups_Harmonic_PositivePrefix`, `ArtinGroups_Harmonic_RestrictionHomRange`, `ArtinGroups_Harmonic_SphericalLongest`, `ArtinGroups_Harmonic_TopBlockMatchingKey`, `ArtinGroups_Harmonic_UnionCarrier`, `ArtinGroups_Quivers_CoefficientMatrix`, `ArtinGroups_Quivers_PathTwo`, `ArtinGroups_Quivers_PathTwoSelf`, `ArtinGroups_Quivers_PathZero`, `ArtinGroups_Quivers_SignDiagonal`, `ArtinGroups_Quivers_TraceLinear`, `ArtinGroups_Quivers_VertexLinear`, `ArtinGroups_Realizations_CellDeligne`, `ArtinGroups_Realizations_FiniteWeightsCompact`, `ArtinGroups_Realizations_FullSphericalCell`, `ArtinGroups_Realizations_WeightAttach`, `ArtinGroups_Realizations_WeightInsertRetract`, `ArtinGroups_Realizations_WeightLinearLinkInverse`, `ArtinGroups_Realizations_WeightMap`, `ArtinGroups_Realizations_WeightMapCover`, `ArtinGroups_Realizations_WeightRetractionPiece`, `ArtinGroups_Realizations_WeightVertexRetract`.
--
--   **Imports.** It imports the published bundle `Def_HarmonicArtin`; the bundles `OAIQ225Ag002`, `OAIQ225Ag003` and `OAIQ225Ag004` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ225Ag010`.
-- source:
--   OpenAI, Harmonic heights and the Artin K(pi,1) conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Harmonic-heights-and-the-Artin-K-pi-1-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Definitions.Def_HarmonicArtin
import Definitions.Def_OAIQ225Ag002
import Definitions.Def_OAIQ225Ag003
import Definitions.Def_OAIQ225Ag004

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_BlockClosed
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
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

omit [Fintype V] [DecidableEq A] in
lemma blockInclusion_entries (E:BasedComplex Q (K:=K) I) (T:Set I) :
    ProjectiveEntries Q (fun i:T=>E.placement i) E.placement (blockInclusion Q E T) :=
  ⟨fun i j=>(projectiveEntries_identity Q).1 (i:I) j,
   fun i j=>(projectiveEntries_identity Q).2 (i:I) j⟩
omit [Fintype V] [DecidableEq A] in
lemma blockProjection_entries (E:BasedComplex Q (K:=K) I) (T:Set I) :
    ProjectiveEntries Q E.placement (fun i:T=>E.placement i) (blockProjection Q E T) :=
  ⟨fun i j=>(projectiveEntries_identity Q).1 i (j:I),
   fun i j=>(projectiveEntries_identity Q).2 i (j:I)⟩

noncomputable def blockInclusionMap (E:BasedComplex Q (K:=K) I) (T:Set I) (h:BlockClosed Q E T) :
    Map Q (blockRestriction Q E T h) E where
  matrix:=blockInclusion Q E T
  entries:=blockInclusion_entries Q E T
  degree:=fun i j=>mapDegree_identity Q (i:I) j
  commute:=blockInclusion_commute Q E T h

noncomputable def blockProjectionMap (E:BasedComplex Q (K:=K) I) (T:Set I) (h:BlockClosed Q E T) :
    Map Q E (blockRestriction Q E T h) where
  matrix:=blockProjection Q E T
  entries:=blockProjection_entries Q E T
  degree:=fun i j=>mapDegree_identity Q i (j:I)
  commute:=blockProjection_commute Q E T h

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_TraceLinear
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V]

lemma trace_smul (r : K) (x : Q.Zigzag K) : trace Q (r • x) = r * trace Q x := by
  simp only [trace, token_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

def traceLinear : Q.Zigzag K →ₗ[K] K where
  toFun := trace Q
  map_add' := trace_add Q
  map_smul' := by intro r x; exact trace_smul Q r x

namespace BasedComplex
variable [Fintype I] [Fintype J]

noncomputable def supertrace (E : BasedComplex Q (K := K) I) :
    Matrix I I (Q.Zigzag K) →ₗ[K] K where
  toFun f := ∑ i, cochainSign (K := K) (E.placement i).cochain * trace Q (f i i)
  map_add' f g := by
    simp only [Matrix.add_apply, trace_add, _root_.mul_add, Finset.sum_add_distrib]
  map_smul' r f := by
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, trace_smul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

lemma supertrace_mul (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {n v : ℤ}
    {f : Matrix I J (Q.Zigzag K)} (hf : MapDegree Q E.placement F.placement n v f)
    (g : Matrix J I (Q.Zigzag K)) :
    supertrace Q F (g * f) = cochainSign (K := K) n * supertrace Q E (f * g) := by
  change (∑ j, cochainSign (K := K) _ * traceLinear Q (∑ i, g j i * f i j)) =
    cochainSign (K := K) n * ∑ i, cochainSign (K := K) _ * traceLinear Q (∑ j, f i j * g j i)
  simp only [map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hc : (F.placement j).cochain = (E.placement i).cochain + n
  · change cochainSign (K := K) _ * trace Q (g j i * f i j) =
      cochainSign (K := K) n * (cochainSign (K := K) _ * trace Q (f i j * g j i))
    rw [hc, cochainSign_add, trace_mul_comm Q (g j i)]
    ring
  · rw [(hf i j).1 hc, MulZeroClass.mul_zero, MulZeroClass.zero_mul,
      map_zero, MulZeroClass.mul_zero, MulZeroClass.mul_zero]
    exact (MulZeroClass.mul_zero _).symm

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_DiagonalVertex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
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

def diagonalToken (E : BasedComplex Q (K := K) I) (i : I) : Matrix I I (Q.Zigzag K) :=
  Matrix.diagonal (fun j => if j = i then tokenBasis Q (E.placement i).color else 0)

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ExtendLayer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
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

def extendLayer (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (l k : ℤ) :
    Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K) →ₗ[K]
      Matrix I J (Q.Zigzag K) where
  toFun f i j := if hi : (E.placement i).level = l then
      if hj : (F.placement j).level = k then f ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0
  map_add' f g := by
    apply Matrix.ext
    intro i j
    change (if hi : (E.placement i).level = l then
      if hj : (F.placement j).level = k then f ⟨i, hi⟩ ⟨j, hj⟩ + g ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0) =
      (if hi : (E.placement i).level = l then
      if hj : (F.placement j).level = k then f ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0) +
      (if hi : (E.placement i).level = l then
      if hj : (F.placement j).level = k then g ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0)
    split_ifs <;> simp only [add_zero]
  map_smul' r f := by
    apply Matrix.ext
    intro i j
    change (if hi : (E.placement i).level = l then
      if hj : (F.placement j).level = k then r • f ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0) =
      r • (if hi : (E.placement i).level = l then
      if hj : (F.placement j).level = k then f ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0)
    split_ifs <;> simp only [smul_zero]

lemma extendLayer_entry (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (l k : ℤ)
    (f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K))
    (i : I) (j : J) :
    extendLayer Q E F l k f i j = if hi : (E.placement i).level = l then
      if hj : (F.placement j).level = k then f ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0 := rfl

lemma extendLayer_apply (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (l k : ℤ)
    (f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K))
    (i : {i // (E.placement i).level = l}) (j : {j // (F.placement j).level = k}) :
    extendLayer Q E F l k f i j = f i j := by
  change (if hi : (E.placement i.val).level = l then
      if hj : (F.placement j.val).level = k then f ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0 else 0) = f i j
  rw [dite_eq_left i.property, dite_eq_left j.property]

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_PathZero
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
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

lemma matrixZero_eq_zero {f : Matrix I J (Q.Zigzag K)} (hf : PositiveMatrix Q f) :
    matrixZero Q f = 0 := by
  apply Matrix.ext
  intro i j
  exact pathZero_eq_zero Q (hf i j)

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_RestrictLayer
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

lemma restrictLayer_extend (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (l k : ℤ)
    (f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K)) :
    restrictLayer Q E F l k (extendLayer Q E F l k f) = f := by
  apply Matrix.ext
  intro i j
  exact extendLayer_apply Q E F l k f i j

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_CoefficientMatrix
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_PathTwo
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

lemma positive_matrix_decomposition {f : Matrix I J (Q.Zigzag K)} (hf : PositiveMatrix Q f) :
    matrixOne Q f + matrixTwo Q f = f := by
  have h := matrix_decomposition Q f
  rw [matrixZero_eq_zero Q hf, zero_add] at h
  exact h

lemma matrixTwo_mul_positive [Fintype J]
    (f : Matrix I J (Q.Zigzag K)) {g : Matrix J L (Q.Zigzag K)}
    (hg : PositiveMatrix Q g) : matrixTwo Q f * g = 0 := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun t _ => pathTwo_mul_positive Q _ (hg t j)

lemma positive_mul_matrixTwo [Fintype J]
    {f : Matrix I J (Q.Zigzag K)} (hf : PositiveMatrix Q f)
    (g : Matrix J L (Q.Zigzag K)) : f * matrixTwo Q g = 0 := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun t _ => positive_mul_pathTwo Q (hf i t) _

namespace BasedComplex
variable [Fintype I] [Fintype J]

noncomputable def linearHomDifferential (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n : ℤ) :
    Matrix I J (Q.Zigzag K) →ₗ[K] Matrix I J (Q.Zigzag K) where
  toFun f := matrixOne Q E.differential * f -
    cochainSign (K := K) n • (f * matrixOne Q F.differential)
  map_add' f g := by
    simp only [Matrix.mul_add, Matrix.add_mul, smul_add]
    abel
  map_smul' r f := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub, RingHom.id_apply]
    rw [smul_comm]

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_PathTwoSelf
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_Capped
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

lemma differential_token_level (E : BasedComplex Q (K := K) I) {i j : I}
    (h : (E.placement j).level ≠ (E.placement i).level - 1) :
    (E.differential i j).token = 0 := by
  by_cases hc : (E.placement j).cochain = (E.placement i).cochain + 1
  · apply (E.degree i j).2.2.2
    dsimp only [GeneratorPlacement.level] at h
    omega
  · rw [(E.degree i j).1 hc]
    rfl

lemma extendLayer_coefficient (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (l k : ℤ)
    {f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K)}
    (hf : CoefficientMatrix Q f) : CoefficientMatrix Q (extendLayer Q E F l k f) := by
  intro i j
  simp only [extendLayer_entry]
  split_ifs with hi hj
  · exact hf ⟨i, hi⟩ ⟨j, hj⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

lemma extend_restrictLayer (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (l k : ℤ) {f : Matrix I J (Q.Zigzag K)}
    (hs : ∀ i j, (E.placement i).level ≠ l ∨ (F.placement j).level ≠ k → f i j = 0) :
    extendLayer Q E F l k (restrictLayer Q E F l k f) = f := by
  apply Matrix.ext
  intro i j
  rw [extendLayer_entry]
  split_ifs with hi hj
  · rfl
  · exact (hs i j (Or.inr hj)).symm
  · exact (hs i j (Or.inl hi)).symm

lemma extend_mul_matrixTwo_support (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (q d : ℤ)
    (f : Matrix {i // (E.placement i).level = q} {j // (F.placement j).level = d} (Q.Zigzag K))
    (i : I) (j : J) (h : (E.placement i).level ≠ q ∨ (F.placement j).level ≠ d-1) :
    (extendLayer Q E F q d f * matrixTwo Q F.differential) i j = 0 := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro t _
  rw [extendLayer_entry]
  split_ifs with hi ht
  · have hj : (F.placement j).level ≠ (F.placement t).level - 1 := by
      rcases h with hh | hh
      · exact (hh hi).elim
      · simpa only [ht] using hh
    change f ⟨i, hi⟩ ⟨t, ht⟩ * pathTwo Q (F.differential t j) = 0
    rw [pathTwo_eq_zero Q (differential_token_level Q F hj), MulZeroClass.mul_zero]
  · exact MulZeroClass.zero_mul _
  · exact MulZeroClass.zero_mul _

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomSpacePairing
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

omit [DecidableEq A] in
lemma supertrace_mul_single [DecidableEq I] [DecidableEq J]
    (E : BasedComplex Q (K := K) I) (f : Matrix I J (Q.Zigzag K)) (i : I) (j : J)
    (z : Q.Zigzag K) :
    supertrace Q E (f * Matrix.single j i z) =
      cochainSign (K := K) (E.placement i).cochain * trace Q (f i j * z) := by
  unfold supertrace
  change (∑ k, cochainSign (K := K) (E.placement k).cochain *
    trace Q ((f * Matrix.single j i z) k k)) = _
  rw [Finset.sum_eq_single i]
  · rw [Matrix.mul_single_apply_same]
  · intro k _ hk
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hk, trace_zero, MulZeroClass.mul_zero]
  · intro h
    exact (h (Finset.mem_univ i)).elim

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomSpaceDuality
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

local instance zigzagFiniteDimensional : FiniteDimensional K (Q.Zigzag K) :=
  (pathBasis Q (K := K)).finiteDimensional_of_finite

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomInternalSupport
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_VertexLinear
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

lemma tokenMatrix_smul (r : K) {f : Matrix I J (Q.Zigzag K)}
    (hf : TokenMatrix Q f) : TokenMatrix Q (r • f) := by
  intro i j
  constructor
  · change r • (f i j).vertex = 0
    rw [(hf i j).1, smul_zero]
  · change r • (f i j).arrow = 0
    rw [(hf i j).2, smul_zero]

end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_CoefficientSocle
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_LeftMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J L : Type*} [Fintype I] [Fintype J] [Fintype L]

lemma coefficientMap_row_support {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (f : Map Q E F)
    (hf : CoefficientMatrix Q f.matrix) (U : Set V)
    (hF : ∀ j, (F.placement j).color ∈ U) (i : I) (j : J)
    (hi : (E.placement i).color ∉ U) : f.matrix i j = 0 := by
  apply Zigzag.ext
  · funext w
    change (f.matrix i j).vertex w = 0
    by_contra hw
    have he := (reduction_support Q f.entries f.degree i j w hw).1
    exact hi (he ▸ hF j)
  · exact (hf i j).1
  · exact (hf i j).2

noncomputable def leftMatrix (a : Matrix I J (Q.Zigzag K)) :
    Matrix J L (Q.Zigzag K) →ₗ[K] Matrix I L (Q.Zigzag K) where
  toFun f := a * f
  map_add' _ _ := Matrix.mul_add _ _ _
  map_smul' _ _ := Matrix.mul_smul _ _ _

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_RestrictExtendLayerMul
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J : Type*} [Fintype I] [Fintype J]

lemma restrict_extendLayer_mul (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (q d k : ℤ)
    (f : Matrix {i // (E.placement i).level = q} {j // (F.placement j).level = d} (Q.Zigzag K))
    (g : Matrix J J (Q.Zigzag K)) :
    restrictLayer Q E F q k (extendLayer Q E F q d f * g) =
      f * restrictLayer Q F F d k g := by
  classical
  apply Matrix.ext
  intro i j
  change (∑ t, extendLayer Q E F q d f i.val t * g t j.val) =
    ∑ t : {j // (F.placement j).level = d}, f i t * g t.val j.val
  symm
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
  · intro t ht
    have hh : (F.placement t).level ≠ d := fun h => ht ⟨⟨t, h⟩, rfl⟩
    rw [extendLayer_entry, dite_eq_left i.property, dite_eq_right hh, MulZeroClass.zero_mul]
  · intro t
    rw [extendLayer_apply Q E F q d f i t]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_CoefficientTopDual
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def topSocleMatrix (α : V) (x : I → K) (y : J → K) :
    Matrix I J (Q.Zigzag K) := fun i j => (x i * y j) • vertexId Q α

omit [Fintype V] [DecidableEq A] in
lemma token_sum {T : Type*} (s : Finset T) (f : T → Q.Zigzag K) :
    (∑ t ∈ s, f t).token = ∑ t ∈ s, (f t).token :=
  map_sum ({ toFun := token
             map_add' := fun _ _ => rfl
             map_smul' := fun _ _ => rfl } : Q.Zigzag K →ₗ[K] (V → K)) f s

omit [Fintype V] [DecidableEq A] [Fintype I] [Fintype J] in
lemma topSocleMatrix_ne_zero (α : V) {x : I → K} {y : J → K}
    (hx : x ≠ 0) (hy : y ≠ 0) : topSocleMatrix Q α x y ≠ 0 := by
  obtain ⟨i,hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hx (funext hn)
  obtain ⟨j,hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hy (funext hn)
  intro hz
  have he := congrArg (fun f : Matrix I J (Q.Zigzag K) => (f i j).vertex α) hz
  have h : x i * y j = 0 := by
    simpa [topSocleMatrix, vertexId_eval] using he
  exact (mul_ne_zero hi hj) h

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_UnfoldedPresentation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

universe u

variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

structure UnfoldedPresentation (M : CoxeterMatrix V) : Prop where
  relation (α β : V) : α = β ∨ M α β = 0 ∨
    (M α β = 2 ∧ OrthogonalVertices Q α β) ∨
    (M α β = 3 ∧ Nonempty (SimpleEdge Q α β))

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomPath
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_EqualColorPair
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

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_GeneratorVector
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_NegativeAmplitudeCoreIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

abbrev NegativeAmplitudeCoreIndex (E : BasedComplex Q (K := K) I) (α : V) :=
  {u : TestIndex Q E.placement α // Path.length u.2.val ≠ 2} ⊕
    {i : I // (E.placement i).color ≠ α}

noncomputable instance negativeAmplitudeCoreFintype (E : BasedComplex Q (K := K) I) (α : V) :
    Fintype (NegativeAmplitudeCoreIndex Q E α) := by
  classical
  unfold NegativeAmplitudeCoreIndex
  infer_instance

noncomputable instance negativeAmplitudeCoreDecidable (E : BasedComplex Q (K := K) I) (α : V) :
    DecidableEq (NegativeAmplitudeCoreIndex Q E α) := fun a b => instDecidableEqSum a b

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PlacedProjective
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

noncomputable def placedProjective (p:GeneratorPlacement V) : BasedComplex Q (K:=K) PUnit.{u+1} where
  placement _:=p
  differential:=0
  entries:=projectiveEntries_zero Q
  degree:=mapDegree_zero Q 1 0
  square_zero:=Matrix.zero_mul _

noncomputable def placedGeneratorMap (E:BasedComplex Q (K:=K) I) (i:I)
    (hi:∀ j,E.differential i j=0) : Map Q (placedProjective Q (E.placement i)) E where
  matrix _ j:=projectiveIdentity Q (K:=K) E.placement i j
  entries:=⟨fun _ j=>(projectiveEntries_identity Q).1 i j,
    fun _ j=>(projectiveEntries_identity Q).2 i j⟩
  degree:=fun _ j=>mapDegree_identity Q i j
  commute:=by
    apply Matrix.ext
    intro z j
    change (∑ _k:PUnit.{u+1}, (0:Q.Zigzag K) * projectiveIdentity Q (K:=K) E.placement i j)=
      (projectiveIdentity Q (K:=K) E.placement*E.differential) i j
    simp only [zero_mul,Finset.sum_const_zero]
    exact ((congrArg (fun M:Matrix I I (Q.Zigzag K)=>M i j)
      (projectiveIdentity_mul Q E.entries)).trans (hi j)).symm

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_TokenShift
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

noncomputable def tokenShift (E : BasedComplex Q (K := K) I) :
    BasedComplex Q (K := K) I where
  placement i := ⟨(E.placement i).color, (E.placement i).cochain - 1,
    (E.placement i).internal + 2⟩
  differential := -E.differential
  entries := projectiveEntries_neg Q E.entries
  degree i j := by
    constructor
    · intro h
      change -E.differential i j = 0
      rw [(E.degree i j).1 (by dsimp only at h; omega), neg_zero]
    · change Homogeneous Q (0 + ((E.placement i).internal + 2) -
        ((E.placement j).internal + 2)) (-E.differential i j)
      convert homogeneous_neg Q (E.degree i j).2 using 1 <;> first | (with_reducible_and_instances rfl) | (omega)
  square_zero := by rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg, E.square_zero]

def testShiftIndexEquiv (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    (TestIndex Q E.placement α ⊕ TestIndex Q E.placement α ⊕ TestIndex Q E.placement α) ≃
      TestIndex Q (E.positiveTwist Q α).placement α where
  toFun
    | .inl u => ⟨.inl u, selfCornerEquiv Q hn α false⟩
    | .inr (.inl u) => ⟨.inr u.1, u.2⟩
    | .inr (.inr u) => ⟨.inl u, selfCornerEquiv Q hn α true⟩
  invFun
    | ⟨.inl u, p⟩ => if (selfCornerEquiv Q hn α).symm p then .inr (.inr u) else .inl u
    | ⟨.inr i, p⟩ => .inr (.inl ⟨i, p⟩)
  left_inv u := by rcases u with u | u | u <;> rfl
  right_inv u := by
    rcases u with ⟨u | i, p⟩
    · have he := (selfCornerEquiv Q hn α).apply_symm_apply p
      cases h : (selfCornerEquiv Q hn α).symm p
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        congr 1
        change (selfCornerEquiv Q hn α false : CornerPath Q α α) = p
        simpa only [h] using he
      · simp only [h, ↓reduceIte]
        congr 1
        change (selfCornerEquiv Q hn α true : CornerPath Q α α) = p
        simpa only [h] using he
    · rfl

noncomputable def normalizedTestTwist (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :=
  ((E.positiveTwist Q α).testComplex Q α).reindex Q (testShiftIndexEquiv Q hn E α)

lemma normalizedTestTwist_pivot_entry (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) (u v : TestIndex Q E.placement α) :
    (normalizedTestTwist Q hn E α).differential (.inl u) (.inr (.inl v)) =
      projectiveIdentity Q (testPlacement Q E.placement α) u v := by
  classical
  change (pathCoordinates Q (K := K) (pathBasis Q (K := K) (.inl α) *
    evaluationMatrix Q E.placement α u v.1) v.2.val) • vertexId Q (K := K) α = _
  rw [pathBasis_vertex]
  simp only [evaluationMatrix]
  by_cases h : u.1 = v.1
  · rcases u with ⟨i, p⟩
    rcases v with ⟨j, q⟩
    dsimp only at h
    subst j
    simp only [ite_true, if_true, cornerPath_left, pathBasis_coordinates, projectiveIdentity,
      Matrix.diagonal_apply, testPlacement, Sigma.mk.inj_iff, heq_eq_eq, true_and]
    simp only [Subtype.val_inj, ite_smul, one_smul, zero_smul]
  · have huv : u ≠ v := fun he => h (congrArg Sigma.fst he)
    simp only [ite_eq_right h, MulZeroClass.mul_zero, coordinates_zero, zero_smul,
      projectiveIdentity, Matrix.diagonal_apply, ite_eq_right huv]

omit [DecidableEq I] in
lemma normalizedTestTwist_unit_token (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) (u v : TestIndex Q E.placement α) :
    (normalizedTestTwist Q hn E α).differential (.inl u) (.inr (.inr v)) = 0 := by
  change (pathCoordinates Q (K := K) (pathBasis Q (K := K) (.inl α) *
    (-((testMatrix Q E.placement E.placement α E.differential) u v • vertexId Q (K := K) α)))
      (.inr (.inr α))) • vertexId Q (K := K) α = 0
  rw [pathBasis_vertex, _root_.mul_neg, mul_smul, vertexId_mul_self]
  rw [map_neg, Pi.neg_apply, coordinates_smul, pathCoordinates_token, token_vertexId]
  simp only [Pi.zero_apply, MulZeroClass.mul_zero, neg_zero, zero_smul]

omit [DecidableEq I] in
lemma normalizedTestTwist_token_token (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) (u v : TestIndex Q E.placement α) :
    (normalizedTestTwist Q hn E α).differential (.inr (.inr u)) (.inr (.inr v)) =
      -(E.testComplex Q α).differential u v := by
  have ht : tokenBasis Q (K := K) α * vertexId Q α = tokenBasis Q α := by
    simpa only [Path.target, pathBasis_token] using
      (pathBasis_right Q (K := K) (.inr (.inr α)))
  change (pathCoordinates Q (K := K) (pathBasis Q (K := K) (.inr (.inr α)) *
    (-((testMatrix Q E.placement E.placement α E.differential) u v • vertexId Q (K := K) α)))
      (.inr (.inr α))) • vertexId Q (K := K) α =
    -((testMatrix Q E.placement E.placement α E.differential) u v • vertexId Q (K := K) α)
  rw [pathBasis_token, _root_.mul_neg, mul_smul, ht]
  simp only [map_neg, Pi.neg_apply, coordinates_smul, ← pathBasis_token,
    pathBasis_coordinates, ite_true, if_true, _root_.mul_one, neg_smul]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ScalarSupported
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.instAlgebra
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.dual_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.source_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.target_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_false _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I J : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [DecidableEq I] [DecidableEq J] in
lemma scalarSupported_map (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (α:V) {l c n v:ℤ} (M:Matrix I J (Q.Zigzag K))
    (he:ProjectiveEntries Q E.placement F.placement M)
    (hd:MapDegree Q E.placement F.placement n v M)
    {x:I→K} (hx:ScalarSupported Q E l c x) :
    ScalarSupported Q F (l+n+v) (c+n) (Matrix.vecMul x (M.map (vertexHom Q α))) := by
  intro j hj
  apply Finset.sum_eq_zero
  intro i hi
  change x i * (M i j).vertex α=0
  by_cases hxi:x i=0
  · rw [hxi,MulZeroClass.zero_mul]
  by_cases hm:(M i j).vertex α=0
  · rw [hm,MulZeroClass.mul_zero]
  have hp:(E.placement i).level=l ∧ (E.placement i).cochain=c :=
    Classical.not_not.mp (fun h=>hxi (hx i h))
  obtain ⟨_,_,hc,hu⟩:=degree_vertex_support Q he hd i j α hm
  exact (hj (by dsimp only [GeneratorPlacement.level] at *; constructor <;> omega)).elim

theorem scalarExact_transport (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (e:HomotopyEquivalence Q E F) (α:V) (hcolor:∀ i,(E.placement i).color=α)
    {l c:ℤ} (hF:ScalarExactAt Q F α l c) : ScalarExactAt Q E α l c := by
  intro x hx hdx
  let f:=e.forward.matrix.map (vertexHom Q α)
  let b:=e.backward.matrix.map (vertexHom Q α)
  let h:=e.sourceHomotopy.map (vertexHom Q α)
  let dE:=E.differential.map (vertexHom Q α)
  let dF:=F.differential.map (vertexHom Q α)
  have hf: dE*f=f*dF := by
    simpa only [Matrix.map_mul] using congrArg
      (fun M:Matrix I J (Q.Zigzag K)=>M.map (vertexHom Q α)) e.forward.commute
  have hb:dF*b=b*dE := by
    simpa only [Matrix.map_mul] using congrArg
      (fun M:Matrix J I (Q.Zigzag K)=>M.map (vertexHom Q α)) e.backward.commute
  have hs:ScalarSupported Q F l c (Matrix.vecMul x f) := by
    simpa only [add_zero] using scalarSupported_map Q E F α e.forward.matrix
      e.forward.entries e.forward.degree hx
  have hd:Matrix.vecMul (Matrix.vecMul x f) dF=0 := by
    rw [Matrix.vecMul_vecMul,← hf,← Matrix.vecMul_vecMul]
    change Matrix.vecMul (Matrix.vecMul x dE) f=0
    rw [hdx,Matrix.zero_vecMul]
  obtain ⟨y,hy,hdy⟩:=hF (Matrix.vecMul x f) hs hd
  refine ⟨Matrix.vecMul y b-Matrix.vecMul x h,?_,?_⟩
  · apply scalarSupported_sub Q E
    · simpa only [add_zero] using scalarSupported_map Q F E α e.backward.matrix
        e.backward.entries e.backward.degree hy
    · convert scalarSupported_map Q E E α e.sourceHomotopy e.sourceEntries e.sourceDegree hx using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1 <;> omega)
  · have hid:(projectiveIdentity Q (K:=K) E.placement).map (vertexHom Q α)=1 := by
      apply Matrix.ext
      intro i j
      by_cases he:i=j
      · subst j
        simp only [Matrix.one_apply,Matrix.map_apply,projectiveIdentity,Matrix.diagonal_apply]
        change (vertexId Q (K:=K) (E.placement i).color).vertex α=1
        simp [hcolor i,vertexId_eval]
      · simp [projectiveIdentity,Matrix.map_apply,he,vertexHom]
    have he:f*b=1+dE*h+h*dE := by
      simpa only [Matrix.map_mul,Matrix.map_add _ (map_add _),hid,← add_assoc] using congrArg
        (fun M:Matrix I I (Q.Zigzag K)=>M.map (vertexHom Q α)) e.sourceEquation
    have hh:Matrix.vecMul (Matrix.vecMul x f) b=x+Matrix.vecMul (Matrix.vecMul x h) dE := by
      rw [Matrix.vecMul_vecMul,he,Matrix.vecMul_add,Matrix.vecMul_add,
        Matrix.vecMul_one,← Matrix.vecMul_vecMul]
      change x+Matrix.vecMul (Matrix.vecMul x dE) h+_= _
      rw [hdx,Matrix.zero_vecMul,add_zero,← Matrix.vecMul_vecMul]
    change Matrix.vecMul (Matrix.vecMul y b-Matrix.vecMul x h) dE=x
    rw [Matrix.sub_vecMul,Matrix.vecMul_vecMul,← hb,← Matrix.vecMul_vecMul,hdy,hh]
    exact add_sub_cancel_right _ _

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_TestComplexVertexDifferential
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I]

lemma testComplex_vertex_differential (E:BasedComplex Q (K:=K) I) (α:V) :
    (E.testComplex Q α).differential.map (vertexHom Q α)=
      testMatrix Q E.placement E.placement α E.differential := by
  apply Matrix.ext
  intro i j
  change ((testMatrix Q E.placement E.placement α E.differential i j) • vertexId Q α).vertex α = _
  simp

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ScalarSupportedCochainShift
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma scalarSupported_cochainShift (E F:BasedComplex Q (K:=K) I)
    (hl:∀ i,(F.placement i).level=(E.placement i).level)
    (hc:∀ i,(F.placement i).cochain=(E.placement i).cochain-1)
    (l c:ℤ) (x:I→K) : ScalarSupported Q F l c x ↔ ScalarSupported Q E l (c+1) x := by
  constructor <;> intro h i hi <;> apply h i <;> intro hh <;> apply hi
  · rw [hl,hc] at hh
    exact ⟨hh.1,by omega⟩
  · rw [hl,hc]
    exact ⟨hh.1,by omega⟩

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma scalarExact_cochainShift_iff (E F:BasedComplex Q (K:=K) I) (α β:V)
    (hl:∀ i,(F.placement i).level=(E.placement i).level)
    (hc:∀ i,(F.placement i).cochain=(E.placement i).cochain-1)
    (hd:F.differential.map (vertexHom Q β) = -E.differential.map (vertexHom Q α))
    (l c:ℤ) : ScalarExactAt Q F β l c ↔ ScalarExactAt Q E α l (c+1) := by
  constructor
  · intro h x hx hd0
    have hxs:ScalarSupported Q F l c x :=
      (scalarSupported_cochainShift Q E F hl hc l c x).mpr hx
    have hdx:Matrix.vecMul x (F.differential.map (vertexHom Q β))=0 := by
      rw [hd,Matrix.vecMul_neg,hd0,neg_zero]
    obtain ⟨y,hy,hyb⟩:=h x hxs hdx
    refine ⟨-y,?_,?_⟩
    · have hh:ScalarSupported Q E (l-1) (c-1+1) y :=
        (scalarSupported_cochainShift Q E F hl hc (l-1) (c-1) y).mp hy
      intro i hi
      change -y i=0
      rw [hh i,neg_zero]
      simpa only [sub_add_cancel,add_sub_cancel_right] using hi
    · rw [hd,Matrix.vecMul_neg] at hyb
      simpa only [Matrix.neg_vecMul] using hyb
  · intro h x hx hd0
    have hxs:ScalarSupported Q E l (c+1) x :=
      (scalarSupported_cochainShift Q E F hl hc l c x).mp hx
    have hdx:Matrix.vecMul x (E.differential.map (vertexHom Q α))=0 := by
      rw [hd,Matrix.vecMul_neg] at hd0
      exact neg_eq_zero.mp hd0
    obtain ⟨y,hy,hyb⟩:=h x hxs hdx
    refine ⟨-y,?_,?_⟩
    · apply (scalarSupported_cochainShift Q E F hl hc (l-1) (c-1) (-y)).mpr
      intro i hi
      change -y i=0
      rw [hy i,neg_zero]
      simpa only [sub_add_cancel,add_sub_cancel_right] using hi
    · rw [hd,Matrix.vecMul_neg,Matrix.neg_vecMul,neg_neg,hyb]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_GeneratorTokenTest
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

def generatorTokenTest (E:BasedComplex Q (K:=K) I) (i:I) :
    TestIndex Q E.placement (E.placement i).color :=
  ⟨i,Sum.inr (Sum.inr (E.placement i).color),rfl,rfl⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_TwistNewTestIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_false _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I]

def twistNewTestIndex (E:BasedComplex Q (K:=K) I) (α β:V)
    (p:Zigzag.CornerPath Q β α) (u:TestIndex Q E.placement α) :
    TestIndex Q (E.positiveTwist Q α).placement β := ⟨Sum.inl u,p⟩

def twistOldTestIndex (E:BasedComplex Q (K:=K) I) (α β:V)
    (u:TestIndex Q E.placement β) :
    TestIndex Q (E.positiveTwist Q α).placement β := ⟨Sum.inr u.1,u.2⟩

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] in
lemma corner_other_length {α β:V} (hne:β≠α) (p:Zigzag.CornerPath Q β α) :
    Path.length p.val=1 := by
  obtain ⟨p,hp,hq⟩:=p
  rcases p with v|a|v
  · exact (hne (hp.symm.trans hq)).elim
  · rfl
  · exact (hne (hp.symm.trans hq)).elim

lemma twistTest_new_differential
    (E:BasedComplex Q (K:=K) I) (α β:V)
    (y:TestIndex Q (E.positiveTwist Q α).placement β→K)
    (p:Zigzag.CornerPath Q β α) (v:TestIndex Q E.placement α) :
    Matrix.vecMul y (testMatrix Q (E.positiveTwist Q α).placement
      (E.positiveTwist Q α).placement β (E.positiveTwist Q α).differential)
      (twistNewTestIndex Q E α β p v) =
    -Matrix.vecMul (fun u=>y (twistNewTestIndex Q E α β p u))
      (testMatrix Q E.placement E.placement α E.differential) v := by
  classical
  change (∑ z:TestIndex Q (E.positiveTwist Q α).placement β,
    y z * pathCoordinates Q (pathBasis Q z.2.val *
      (E.positiveTwist Q α).differential z.1 (Sum.inl v)) p.val)=_
  rw [Fintype.sum_sigma,Fintype.sum_sum_type]
  dsimp only
  have ho:(∑ i:I,∑ z:Zigzag.CornerPath Q β (E.placement i).color,
      y ⟨Sum.inr i,z⟩ * pathCoordinates Q
      (pathBasis Q z.val * (E.positiveTwist Q α).differential (Sum.inr i) (Sum.inl v)) p.val)=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro z hz
    change _ * pathCoordinates Q (_ * 0) _=0
    rw [MulZeroClass.mul_zero,coordinates_zero,MulZeroClass.mul_zero]
  have he := congrArg (fun a:K =>
    (∑ u:TestIndex Q E.placement α,∑ z:Zigzag.CornerPath Q β α,
      y ⟨Sum.inl u,z⟩ * pathCoordinates Q (pathBasis Q z.val *
      (E.positiveTwist Q α).differential (Sum.inl u) (Sum.inl v)) p.val) + a) ho
  apply he.trans
  rw [add_zero]
  rw [show -Matrix.vecMul (fun u=>y (twistNewTestIndex Q E α β p u))
      (testMatrix Q E.placement E.placement α E.differential) v =
      ∑ u, -(y (twistNewTestIndex Q E α β p u) *
      testMatrix Q E.placement E.placement α E.differential u v) by
        exact (Finset.sum_neg_distrib _).symm]
  apply Finset.sum_congr rfl
  intro u hu
  change (∑ z:Zigzag.CornerPath Q β α,y ⟨Sum.inl u,z⟩ *
    pathCoordinates Q (pathBasis Q z.val *
      (-(testMatrix Q E.placement E.placement α E.differential u v • vertexId Q (K:=K) α))) p.val)=_
  simp only [_root_.mul_neg,mul_smul,cornerPath_right,map_neg,map_smul,
    pathBasis_coordinates,Pi.neg_apply,Pi.smul_apply,smul_eq_mul]
  rw [Finset.sum_eq_single p]
  · simp [twistNewTestIndex]
  · intro z hz hzp
    rw [ite_eq_right (fun equality=>hzp (Subtype.ext equality))]
    simp
  · simp

lemma twistTest_old_differential
    (E:BasedComplex Q (K:=K) I) (α β:V)
    (y:TestIndex Q (E.positiveTwist Q α).placement β→K)
    (hy:∀ p:Zigzag.CornerPath Q β α,∀ u:TestIndex Q E.placement α,
      y (twistNewTestIndex Q E α β p u)=0)
    (v:TestIndex Q E.placement β) :
    Matrix.vecMul y (testMatrix Q (E.positiveTwist Q α).placement
      (E.positiveTwist Q α).placement β (E.positiveTwist Q α).differential)
      (twistOldTestIndex Q E α β v) =
    Matrix.vecMul (fun u=>y (twistOldTestIndex Q E α β u))
      (testMatrix Q E.placement E.placement β E.differential) v := by
  classical
  change (∑ z:TestIndex Q (E.positiveTwist Q α).placement β,
    y z * pathCoordinates Q (pathBasis Q z.2.val *
      (E.positiveTwist Q α).differential z.1 (Sum.inr v.1)) v.2.val)=_
  rw [Fintype.sum_sigma,Fintype.sum_sum_type]
  dsimp only
  have hn:(∑ u:TestIndex Q E.placement α,∑ z:Zigzag.CornerPath Q β α,
      y ⟨Sum.inl u,z⟩ * pathCoordinates Q
      (pathBasis Q z.val * (E.positiveTwist Q α).differential (Sum.inl u) (Sum.inr v.1)) v.2.val)=0 := by
    apply Finset.sum_eq_zero
    intro u hu
    apply Finset.sum_eq_zero
    intro z hz
    have hh:=hy z u
    change y ⟨Sum.inl u,z⟩=0 at hh
    rw [hh,MulZeroClass.zero_mul]
  have he := congrArg (fun a:K => a+
    (∑ i:I,∑ z:Zigzag.CornerPath Q β (E.placement i).color,
      y ⟨Sum.inr i,z⟩ * pathCoordinates Q (pathBasis Q z.val *
      (E.positiveTwist Q α).differential (Sum.inr i) (Sum.inr v.1)) v.2.val)) hn
  apply he.trans
  rw [zero_add]
  change _ = ∑ z:TestIndex Q E.placement β,
    y (twistOldTestIndex Q E α β z) *
    pathCoordinates Q (pathBasis Q z.2.val * E.differential z.1 v.1) v.2.val
  rw [Fintype.sum_sigma]
  rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PositiveTwistOtherTest2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem positiveTwist_other_test_exact
    (E:BasedComplex Q (K:=K) I) (α β:V) (hne:β≠α) (l c:ℤ)
    (hα:ScalarExactAt Q (E.testComplex Q α) α l (c+1))
    (hβ:ScalarExactAt Q (E.testComplex Q β) β l c) :
    ScalarExactAt Q ((E.positiveTwist Q α).testComplex Q β) β l c := by
  classical
  intro y hs hd
  let T:=(E.positiveTwist Q α).testComplex Q β
  let D:=T.differential.map (vertexHom Q β)
  have hx:∀ p:Zigzag.CornerPath Q β α,∃ z:TestIndex Q E.placement α→K,
      ScalarSupported Q (E.testComplex Q α) (l-1) c z ∧
      Matrix.vecMul z ((E.testComplex Q α).differential.map (vertexHom Q α))=
        fun u=>y (twistNewTestIndex Q E α β p u) := by
    intro p
    have hl:=corner_other_length Q hne p
    suffices hh:∃ z:TestIndex Q E.placement α→K,
        ScalarSupported Q (E.testComplex Q α) (l-1) (c+1-1) z ∧
        Matrix.vecMul z ((E.testComplex Q α).differential.map (vertexHom Q α))=
          fun u=>y (twistNewTestIndex Q E α β p u) from by
      simpa only [add_sub_cancel_right] using hh
    apply hα
    · intro i hi
      apply hs
      intro hh
      apply hi
      change (E.placement i.1).cochain+((E.placement i.1).internal+Path.length i.2.val)=l ∧
        (E.placement i.1).cochain=c+1
      change (E.placement i.1).cochain-1+
        ((E.placement i.1).internal+Path.length i.2.val+Path.length p.val)=l ∧
        (E.placement i.1).cochain-1=c at hh
      omega
    · rw [testComplex_vertex_differential Q E α]
      funext v
      have hh:=congrFun hd (twistNewTestIndex Q E α β p v)
      rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
        twistTest_new_differential Q E α β y p v] at hh
      exact neg_eq_zero.mp hh
  choose z hzs hzd using hx
  let Z:TestIndex Q (E.positiveTwist Q α).placement β→K :=
    fun ⟨i,p⟩=>match i with
    | .inl u=> -z p u
    | .inr _=>0
  have hZs:ScalarSupported Q T (l-1) (c-1) Z := by
    rintro ⟨i,p⟩ hi
    rcases i with u|i
    · change -z p u=0
      rw [hzs p u,neg_zero]
      intro hh
      apply hi
      have hl:=corner_other_length Q hne p
      change (E.placement u.1).cochain-1+
        ((E.placement u.1).internal+Path.length u.2.val+Path.length p.val)=l-1 ∧
        (E.placement u.1).cochain-1=c-1
      change (E.placement u.1).cochain+
        ((E.placement u.1).internal+Path.length u.2.val)=l-1 ∧
        (E.placement u.1).cochain=c at hh
      omega
    · rfl
  have hZn:∀ p u,Matrix.vecMul Z D (twistNewTestIndex Q E α β p u)=
      y (twistNewTestIndex Q E α β p u) := by
    intro p u
    dsimp only [D,T]
    rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
      twistTest_new_differential Q E α β Z p u]
    change -Matrix.vecMul (-(z p)) (testMatrix Q E.placement E.placement α E.differential) u=_
    rw [Matrix.neg_vecMul,Pi.neg_apply,neg_neg]
    have hh:=congrFun (hzd p) u
    rwa [testComplex_vertex_differential Q E α] at hh
  let r:=y-Matrix.vecMul Z D
  have hrn:∀ p u,r (twistNewTestIndex Q E α β p u)=0 := by
    intro p u
    change y _-Matrix.vecMul Z D _=0
    rw [hZn,sub_self]
  have hrs:ScalarSupported Q T l c r := by
    apply scalarSupported_sub Q T hs
    convert scalarSupported_map Q T T β T.differential T.entries T.degree hZs using 1 <;>
      omega
  have hrd:Matrix.vecMul r D=0 := by
    change Matrix.vecMul (y-Matrix.vecMul Z D) D=0
    rw [Matrix.sub_vecMul,hd,Matrix.vecMul_vecMul,scalarDifferential_square Q T β,
      Matrix.vecMul_zero,sub_self]
  have hro:Matrix.vecMul (fun u=>r (twistOldTestIndex Q E α β u))
      ((E.testComplex Q β).differential.map (vertexHom Q β))=0 := by
    rw [testComplex_vertex_differential Q E β]
    funext v
    have hh:=congrFun hrd (twistOldTestIndex Q E α β v)
    change Matrix.vecMul r (T.differential.map (vertexHom Q β)) _=0 at hh
    rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
      twistTest_old_differential Q E α β r hrn v] at hh
    exact hh
  obtain ⟨w,hws,hwd⟩:=hβ (fun u=>r (twistOldTestIndex Q E α β u))
    (fun u hu=>hrs _ hu) hro
  let W:TestIndex Q (E.positiveTwist Q α).placement β→K :=
    fun ⟨i,p⟩=>match i with
    | .inl _=>0
    | .inr i=>w ⟨i,p⟩
  have hWn:∀ p u,W (twistNewTestIndex Q E α β p u)=0:=fun _ _=>rfl
  have hWs:ScalarSupported Q T (l-1) (c-1) W := by
    rintro ⟨i,p⟩ hi
    rcases i with u|i
    · rfl
    · exact hws ⟨i,p⟩ hi
  have hWd:Matrix.vecMul W D=r := by
    funext i
    obtain ⟨i,p⟩:=i
    rcases i with u|i
    · change Zigzag.CornerPath Q β α at p
      change Matrix.vecMul W (T.differential.map (vertexHom Q β))
        (twistNewTestIndex Q E α β p u)=r (twistNewTestIndex Q E α β p u)
      rw [hrn,testComplex_vertex_differential Q (E.positiveTwist Q α) β,
        twistTest_new_differential Q E α β W p u]
      change -Matrix.vecMul (0:TestIndex Q E.placement α→K) _ u=0
      rw [Matrix.zero_vecMul,Pi.zero_apply,neg_zero]
    · change Zigzag.CornerPath Q β (E.placement i).color at p
      change Matrix.vecMul W (T.differential.map (vertexHom Q β))
        (twistOldTestIndex Q E α β ⟨i,p⟩)=r (twistOldTestIndex Q E α β ⟨i,p⟩)
      rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
        twistTest_old_differential Q E α β W hWn ⟨i,p⟩]
      have hh:=congrFun hwd ⟨i,p⟩
      rwa [testComplex_vertex_differential Q E β] at hh
  refine ⟨Z+W,?_,?_⟩
  · intro i hi
    change Z i+W i=0
    rw [hZs i hi,hWs i hi,add_zero]
  · change Matrix.vecMul (Z+W) D=y
    rw [Matrix.add_vecMul,hWd]
    change Matrix.vecMul Z D+(y-Matrix.vecMul Z D)=y
    abel

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PositiveTwistOtherTest3
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem positiveTwist_other_test_exact_reflect
    (E:BasedComplex Q (K:=K) I) (α β:V) (hne:β≠α) (l c:ℤ)
    (hα:ScalarExactAt Q (E.testComplex Q α) α (l-1) c)
    (hT:ScalarExactAt Q ((E.positiveTwist Q α).testComplex Q β) β l c) :
    ScalarExactAt Q (E.testComplex Q β) β l c := by
  classical
  intro x hs hd
  let T:=(E.positiveTwist Q α).testComplex Q β
  let D:=T.differential.map (vertexHom Q β)
  let X:TestIndex Q (E.positiveTwist Q α).placement β→K :=
    fun ⟨i,p⟩=>match i with
    | .inl _=>0
    | .inr i=>x ⟨i,p⟩
  have hXn:∀ p u,X (twistNewTestIndex Q E α β p u)=0:=fun _ _=>rfl
  have hXs:ScalarSupported Q T l c X := by
    rintro ⟨i,p⟩ hi
    rcases i with u|i
    · rfl
    · exact hs ⟨i,p⟩ hi
  have hXd:Matrix.vecMul X D=0 := by
    funext v
    obtain ⟨i,p⟩:=v
    rcases i with u|i
    · change Zigzag.CornerPath Q β α at p
      change Matrix.vecMul X (T.differential.map (vertexHom Q β))
        (twistNewTestIndex Q E α β p u)=0
      rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
        twistTest_new_differential Q E α β X p u]
      change -Matrix.vecMul (0:TestIndex Q E.placement α→K) _ u=0
      rw [Matrix.zero_vecMul,Pi.zero_apply,neg_zero]
    · change Zigzag.CornerPath Q β (E.placement i).color at p
      change Matrix.vecMul X (T.differential.map (vertexHom Q β))
        (twistOldTestIndex Q E α β ⟨i,p⟩)=0
      rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
        twistTest_old_differential Q E α β X hXn ⟨i,p⟩]
      have hh:=congrFun hd ⟨i,p⟩
      rwa [testComplex_vertex_differential Q E β] at hh
  obtain ⟨z,hzs,hzd⟩:=hT X hXs hXd
  have hx:∀ p:Zigzag.CornerPath Q β α,∃ a:TestIndex Q E.placement α→K,
      ScalarSupported Q (E.testComplex Q α) (l-1-1) (c-1) a ∧
      Matrix.vecMul a ((E.testComplex Q α).differential.map (vertexHom Q α))=
        fun u=>z (twistNewTestIndex Q E α β p u) := by
    intro p
    have hl:=corner_other_length Q hne p
    apply hα
    · intro i hi
      apply hzs
      intro hh
      apply hi
      change (E.placement i.1).cochain+((E.placement i.1).internal+Path.length i.2.val)=l-1 ∧
        (E.placement i.1).cochain=c
      change (E.placement i.1).cochain-1+
        ((E.placement i.1).internal+Path.length i.2.val+Path.length p.val)=l-1 ∧
        (E.placement i.1).cochain-1=c-1 at hh
      omega
    · rw [testComplex_vertex_differential Q E α]
      funext v
      have hh:=congrFun hzd (twistNewTestIndex Q E α β p v)
      rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
        twistTest_new_differential Q E α β z p v,hXn p v] at hh
      exact neg_eq_zero.mp hh
  choose a has had using hx
  let B:TestIndex Q (E.positiveTwist Q α).placement β→K :=
    fun ⟨i,p⟩=>match i with
    | .inl u=> -a p u
    | .inr _=>0
  have hBs:ScalarSupported Q T (l-1-1) (c-1-1) B := by
    rintro ⟨i,p⟩ hi
    rcases i with u|i
    · change -a p u=0
      rw [has p u,neg_zero]
      intro hh
      apply hi
      have hl:=corner_other_length Q hne p
      change (E.placement u.1).cochain-1+
        ((E.placement u.1).internal+Path.length u.2.val+Path.length p.val)=l-1-1 ∧
        (E.placement u.1).cochain-1=c-1-1
      change (E.placement u.1).cochain+
        ((E.placement u.1).internal+Path.length u.2.val)=l-1-1 ∧
        (E.placement u.1).cochain=c-1 at hh
      omega
    · rfl
  have hBn:∀ p u,Matrix.vecMul B D (twistNewTestIndex Q E α β p u)=
      z (twistNewTestIndex Q E α β p u) := by
    intro p u
    dsimp only [D,T]
    rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
      twistTest_new_differential Q E α β B p u]
    change -Matrix.vecMul (-(a p)) (testMatrix Q E.placement E.placement α E.differential) u=_
    rw [Matrix.neg_vecMul,Pi.neg_apply,neg_neg]
    have hh:=congrFun (had p) u
    rwa [testComplex_vertex_differential Q E α] at hh
  let r:=z-Matrix.vecMul B D
  have hrn:∀ p u,r (twistNewTestIndex Q E α β p u)=0 := by
    intro p u
    change z _-Matrix.vecMul B D _=0
    rw [hBn,sub_self]
  have hrs:ScalarSupported Q T (l-1) (c-1) r := by
    apply scalarSupported_sub Q T hzs
    convert scalarSupported_map Q T T β T.differential T.entries T.degree hBs using 1 <;>
      omega
  have hrd:Matrix.vecMul r D=X := by
    change Matrix.vecMul (z-Matrix.vecMul B D) D=X
    rw [Matrix.sub_vecMul,hzd,Matrix.vecMul_vecMul,scalarDifferential_square Q T β,
      Matrix.vecMul_zero,sub_zero]
  refine ⟨fun u=>r (twistOldTestIndex Q E α β u),fun u hu=>hrs _ hu,?_⟩
  rw [testComplex_vertex_differential Q E β]
  funext v
  have hh:=congrFun hrd (twistOldTestIndex Q E α β v)
  change Matrix.vecMul r (T.differential.map (vertexHom Q β)) _=x v at hh
  rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
    twistTest_old_differential Q E α β r hrn v] at hh
  exact hh

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ScalarSupportedTokenShift
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma scalarSupported_tokenShift (E:BasedComplex Q (K:=K) I) (l c:ℤ) (x:I→K) :
    ScalarSupported Q (E.tokenShift Q) l c x ↔ ScalarSupported Q E (l-1) (c+1) x := by
  constructor <;> intro h i hi <;> apply h i <;> intro hh <;> apply hi
  · change (E.placement i).cochain-1+((E.placement i).internal+2)=l ∧
      (E.placement i).cochain-1=c at hh
    dsimp only [GeneratorPlacement.level]
    omega
  · change (E.placement i).cochain-1+((E.placement i).internal+2)=l ∧
      (E.placement i).cochain-1=c
    dsimp only [GeneratorPlacement.level] at hh
    omega

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma scalarDifferential_tokenShift (E:BasedComplex Q (K:=K) I) (α:V) :
    (E.tokenShift Q).differential.map (vertexHom Q α)=
      -E.differential.map (vertexHom Q α) := by
  apply Matrix.ext
  intro i j
  exact map_neg (vertexHom Q α) _

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
theorem scalarExact_tokenShift_iff (E:BasedComplex Q (K:=K) I) (α:V) (l c:ℤ) :
    ScalarExactAt Q (E.tokenShift Q) α l c ↔ ScalarExactAt Q E α (l-1) (c+1) := by
  constructor
  · intro h x hx hd
    have hxs:ScalarSupported Q (E.tokenShift Q) l c x :=
      (scalarSupported_tokenShift Q E l c x).mpr hx
    have hdx:Matrix.vecMul x ((E.tokenShift Q).differential.map (vertexHom Q α))=0 := by
      rw [scalarDifferential_tokenShift,Matrix.vecMul_neg,hd,neg_zero]
    obtain ⟨y,hy,hyb⟩:=h x hxs hdx
    refine ⟨-y,?_,?_⟩
    · have hh:ScalarSupported Q E (l-1-1) (c-1+1) y :=
        (scalarSupported_tokenShift Q E (l-1) (c-1) y).mp hy
      intro i hi
      change -y i=0
      rw [hh i,neg_zero]
      simpa only [sub_add_cancel,add_sub_cancel_right] using hi
    · rw [scalarDifferential_tokenShift,Matrix.vecMul_neg] at hyb
      simpa only [Matrix.neg_vecMul] using hyb
  · intro h x hx hd
    have hxs:ScalarSupported Q E (l-1) (c+1) x :=
      (scalarSupported_tokenShift Q E l c x).mp hx
    have hdx:Matrix.vecMul x (E.differential.map (vertexHom Q α))=0 := by
      rw [scalarDifferential_tokenShift,Matrix.vecMul_neg] at hd
      exact neg_eq_zero.mp hd
    obtain ⟨y,hy,hyb⟩:=h x hxs hdx
    refine ⟨-y,?_,?_⟩
    · apply (scalarSupported_tokenShift Q E (l-1) (c-1) (-y)).mpr
      intro i hi
      change -y i=0
      rw [hy i,neg_zero]
      simpa only [sub_add_cancel,add_sub_cancel_right] using hi
    · rw [scalarDifferential_tokenShift,Matrix.vecMul_neg,Matrix.neg_vecMul,neg_neg,hyb]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_Test
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [DecidableEq J] in
lemma test_homotopy_equation {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J}
    (f : Map Q E F) (g : Map Q F E) (α : V)
    {h : Matrix I I (Q.Zigzag K)} (hh : ProjectiveEntries Q E.placement E.placement h)
    (he : f.matrix * g.matrix = projectiveIdentity Q E.placement +
      (E.differential * h + h * E.differential)) :
    (f.test Q α).matrix * (g.test Q α).matrix =
      projectiveIdentity Q (E.testComplex Q α).placement +
      ((E.testComplex Q α).differential * testTransform Q E.placement E.placement α h +
        testTransform Q E.placement E.placement α h * (E.testComplex Q α).differential) := by
  change testTransform Q _ _ α f.matrix * testTransform Q _ _ α g.matrix =
    projectiveIdentity Q (testPlacement Q E.placement α) +
      (testTransform Q _ _ α E.differential * testTransform Q _ _ α h +
        testTransform Q _ _ α h * testTransform Q _ _ α E.differential)
  rw [testTransform_mul Q α _ f.entries, testTransform_mul Q α _ E.entries,
    testTransform_mul Q α _ hh, he, testTransform_add, testTransform_add,
    testTransform_identity]
  congr 2
  exact Subsingleton.elim _ _

noncomputable def HomotopyEquivalence.test {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (e : HomotopyEquivalence Q E F) (α : V) :
    HomotopyEquivalence Q (E.testComplex Q α) (F.testComplex Q α) where
  forward := e.forward.test Q α
  backward := e.backward.test Q α
  sourceHomotopy := testTransform Q E.placement E.placement α e.sourceHomotopy
  targetHomotopy := testTransform Q F.placement F.placement α e.targetHomotopy
  sourceEntries := scalarCornerMatrix_entries Q α _ _ (fun _ => rfl) (fun _ => rfl) _
  targetEntries := scalarCornerMatrix_entries Q α _ _ (fun _ => rfl) (fun _ => rfl) _
  sourceDegree := testMatrix_degree Q α e.sourceDegree
  targetDegree := testMatrix_degree Q α e.targetDegree
  sourceEquation := test_homotopy_equation Q e.forward e.backward α
    e.sourceEntries e.sourceEquation
  targetEquation := test_homotopy_equation Q e.backward e.forward α
    e.targetEntries e.targetEquation

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_TestUpperBound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I J : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def TestUpperBound (E:BasedComplex Q (K:=K) I) (U:Set V) (t:ℤ) : Prop :=
  ∀ α∈U,∀ l:ℤ,t<l→∀ c:ℤ,ScalarExactAt Q (E.testComplex Q α) α l c

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_TestExact
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

def ClassTestExact (α:V) (l c:ℤ) : FiniteHomotopyClass Q (K:=K)→Prop :=
  Quotient.lift (fun E=>ScalarExactAt Q (E.complex.testComplex Q α) α l c) (by
    intro E F h
    obtain ⟨e⟩:=h
    apply propext
    constructor
    · exact fun h=>scalarExact_transport Q _ _ ((e.symm Q).test Q α) α (fun _=>rfl) h
    · exact fun h=>scalarExact_transport Q _ _ (e.test Q α) α (fun _=>rfl) h)

def ClassTestUpper (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) (t:ℤ) : Prop :=
  ∀ α∈U,∀ l:ℤ,t<l→∀ c:ℤ,ClassTestExact Q α l c x

lemma classTestExact_positive_other (x:FiniteHomotopyClass Q (K:=K)) (α β:V)
    (hne:β≠α) (l c:ℤ)
    (ha:ClassTestExact Q α l (c+1) x) (hb:ClassTestExact Q β l c x) :
    ClassTestExact Q β l c (classPositiveTwist Q α x) := by
  induction x using Quotient.inductionOn with | _ E =>
    exact positiveTwist_other_test_exact Q E.complex α β hne l c ha hb

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_OutsideCap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I:Type u} [Fintype I] [DecidableEq I]

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma scalarExact_of_absent_degree (E:BasedComplex Q (K:=K) I) (α:V) (l c:ℤ)
    (h:∀ i,(E.placement i).level≠l) : ScalarExactAt Q E α l c := by
  intro x hx _
  have hz:x=0 := by funext i; exact hx i (fun hh=>h i hh.1)
  refine ⟨0,?_,?_⟩
  · intro index _; rfl
  · rw [Matrix.zero_vecMul,hz]

omit [DecidableEq I] in
lemma testUpperBound_of_generator_cap (E:BasedComplex Q (K:=K) I) (d:ℤ)
    (h:∀ i,(E.placement i).level≤d) (U:Set V) : TestUpperBound Q E U (d+2) := by
  intro α _ l hl c
  apply scalarExact_of_absent_degree Q _ α l c
  intro j he
  have hp:Path.length j.2.val≤2 := by rcases j.2.val with v|a|v <;> norm_num [Path.length]
  have hi:=h j.1
  dsimp only [testComplex,testPlacement,GeneratorPlacement.level] at he hi
  omega

def ClassOutsideCap (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) (d:ℤ) : Prop :=
  ∀ i,((minimalClassModel Q x).complex.placement i).color∉U→
    ((minimalClassModel Q x).complex.placement i).level≤d

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_LayerVector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_PositiveBraidRel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} (Q:ReversibleQuiver V A)

inductive PositiveBraidRel : List V→List V→Prop
  | refl (w) : PositiveBraidRel w w
  | symm {v w} : PositiveBraidRel v w→PositiveBraidRel w v
  | trans {v w z} : PositiveBraidRel v w→PositiveBraidRel w z→PositiveBraidRel v z
  | cons (α) {v w} : PositiveBraidRel v w→PositiveBraidRel (α::v) (α::w)
  | orthogonal {α β} (h:OrthogonalVertices Q α β) (w) :
      PositiveBraidRel (α::β::w) (β::α::w)
  | adjacent {α β} (e:SimpleEdge Q α β) (w) :
      PositiveBraidRel (α::β::α::w) (β::α::β::w)

namespace PositiveBraidRel
lemma length_eq {v w:List V} (h:PositiveBraidRel Q v w) : v.length=w.length := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h k ih ik => exact ih.trans ik
  | cons α h ih => exact congrArg Nat.succ ih
  | orthogonal => rfl
  | adjacent => rfl

lemma mem_iff {v w:List V} (h:PositiveBraidRel Q v w) (s:V) : s∈v↔s∈w := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h k ih ik => exact ih.trans ik
  | cons α h ih => simpa only [List.mem_cons] using or_congr Iff.rfl ih
  | orthogonal => simp only [List.mem_cons]; tauto
  | adjacent => simp only [List.mem_cons]; tauto

lemma mem_set {v w:List V} (h:PositiveBraidRel Q v w) (U:Set V)
    (hv:∀ s∈v,s∈U) : ∀ s∈w,s∈U := fun s hs=>hv s ((h.mem_iff Q s).mpr hs)
end PositiveBraidRel

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_InverseWordAction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

noncomputable def inverseWordAction : List V→FiniteHomotopyClass Q (K:=K)→FiniteHomotopyClass Q (K:=K)
  | [],x=>x
  | α::w,x=>inverseWordAction w (classNegativeTwist Q α x)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PositiveWord
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

namespace FiniteModel
noncomputable def positiveWord : List V → FiniteModel.{u} Q (K:=K) → FiniteModel.{u} Q (K:=K)
  | [],E=>E
  | α::w,E=>ofComplex Q ((positiveWord w E).complex.positiveTwist Q α)

noncomputable def positiveWordMap : (w:List V) → {E F:FiniteModel.{u} Q (K:=K)} →
    Map Q E.complex F.complex → Map Q (positiveWord Q w E).complex (positiveWord Q w F).complex
  | [],_,_,f=>f
  | α::w,_,_,f=>(positiveWordMap w f).positiveTwist Q α

end FiniteModel

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_WordInverseModel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def wordInverseModel (w:List V) (x:FiniteHomotopyClass Q (K:=K)) :=
  minimalClassModel Q (inverseWordAction Q w x)

noncomputable def canonicalLowTarget (w:List V) (x:FiniteHomotopyClass Q (K:=K)) :=
  FiniteModel.positiveWord Q w (wordInverseModel Q w x)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ColorSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

def ClassOutsideFloor (U:Set V) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K)) : Prop :=
  ∀ i,((minimalClassModel Q x).complex.placement i).color∉U→
    q≤((minimalClassModel Q x).complex.placement i).level

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_InverseMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
open _root_.Matrix

attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J L:Type u} [Fintype I] [Fintype J] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq L]
  {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma cone_homotopy_degree11 (f:Map Q E F)
    (H:Matrix (I⊕J) (I⊕J) (Q.Zigzag K))
    (hH:MapDegree Q (f.cone Q).placement (f.cone Q).placement (-1) 0 H) :
    MapDegree Q E.placement E.placement (-1) 0 H.toBlocks₁₁ := by
  intro i j
  refine ⟨?_,(hH (.inl i) (.inl j)).2⟩
  intro h
  apply (hH (.inl i) (.inl j)).1
  change (E.placement j).cochain-1≠(E.placement i).cochain-1+(-1)
  omega

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma cone_homotopy_degree22 (f:Map Q E F)
    (H:Matrix (I⊕J) (I⊕J) (Q.Zigzag K))
    (hH:MapDegree Q (f.cone Q).placement (f.cone Q).placement (-1) 0 H) :
    MapDegree Q F.placement F.placement (-1) 0 H.toBlocks₂₂ :=
  fun i j=>hH (.inr i) (.inr j)

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma cone_homotopy_degree21 (f:Map Q E F)
    (H:Matrix (I⊕J) (I⊕J) (Q.Zigzag K))
    (hH:MapDegree Q (f.cone Q).placement (f.cone Q).placement (-1) 0 H) :
    MapDegree Q F.placement E.placement 0 0 H.toBlocks₂₁ := by
  intro i j
  refine ⟨?_,(hH (.inr i) (.inl j)).2⟩
  intro h
  apply (hH (.inr i) (.inl j)).1
  change (E.placement j).cochain-1≠(F.placement i).cochain+(-1)
  omega

omit [Fintype V] [DecidableEq A] in
lemma cone_identity_blocks (f:Map Q E F) :
    projectiveIdentity Q (K:=K) (f.cone Q).placement=
      Matrix.fromBlocks (projectiveIdentity Q E.placement) 0 0
        (projectiveIdentity Q F.placement) := by
  apply Matrix.ext
  intro i j
  rcases i with i|i <;> rcases j with j|j <;> simp [projectiveIdentity,Matrix.diagonal,Map.cone,Map.conePlacement]

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma cone_homotopy_source_block (f:Map Q E F)
    (H:Matrix (I⊕J) (I⊕J) (Q.Zigzag K)) :
    ((f.cone Q).differential*H+H*(f.cone Q).differential).toBlocks₁₁=
      -(E.differential*H.toBlocks₁₁+H.toBlocks₁₁*E.differential)+f.matrix*H.toBlocks₂₁ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks H]
  change ((Matrix.fromBlocks (-E.differential) f.matrix 0 F.differential)*
      Matrix.fromBlocks H.toBlocks₁₁ H.toBlocks₁₂ H.toBlocks₂₁ H.toBlocks₂₂+
    Matrix.fromBlocks H.toBlocks₁₁ H.toBlocks₁₂ H.toBlocks₂₁ H.toBlocks₂₂*
      Matrix.fromBlocks (-E.differential) f.matrix 0 F.differential).toBlocks₁₁=_
  rw [Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply]
  change (-E.differential*H.toBlocks₁₁+f.matrix*H.toBlocks₂₁)+
    (H.toBlocks₁₁*(-E.differential)+H.toBlocks₁₂*(0 : Matrix J I (Q.Zigzag K)))=_
  simp only [Matrix.mul_zero,add_zero,Matrix.neg_mul,Matrix.mul_neg]
  abel

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma cone_homotopy_target_block (f:Map Q E F)
    (H:Matrix (I⊕J) (I⊕J) (Q.Zigzag K)) :
    ((f.cone Q).differential*H+H*(f.cone Q).differential).toBlocks₂₂=
      (F.differential*H.toBlocks₂₂+H.toBlocks₂₂*F.differential)+H.toBlocks₂₁*f.matrix := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks H]
  change ((Matrix.fromBlocks (-E.differential) f.matrix 0 F.differential)*
      Matrix.fromBlocks H.toBlocks₁₁ H.toBlocks₁₂ H.toBlocks₂₁ H.toBlocks₂₂+
    Matrix.fromBlocks H.toBlocks₁₁ H.toBlocks₁₂ H.toBlocks₂₁ H.toBlocks₂₂*
      Matrix.fromBlocks (-E.differential) f.matrix 0 F.differential).toBlocks₂₂=_
  rw [Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply]
  change ((0 : Matrix J I (Q.Zigzag K))*H.toBlocks₁₂+F.differential*H.toBlocks₂₂)+
    (H.toBlocks₂₁*f.matrix+H.toBlocks₂₂*F.differential)=_
  simp only [Matrix.zero_mul,zero_add]
  abel

noncomputable def Map.inverseMatrix (f:Map Q E F) (g:Matrix J I (Q.Zigzag K))
    (hg:ProjectiveEntries Q F.placement E.placement g)
    (hd:MapDegree Q F.placement E.placement 0 0 g)
    (hfg:f.matrix*g=projectiveIdentity Q E.placement)
    (hgf:g*f.matrix=projectiveIdentity Q F.placement) : Map Q F E where
  matrix:=g
  entries:=hg
  degree:=hd
  commute:=by
    calc
      F.differential*g=(projectiveIdentity Q F.placement*F.differential)*g := by
        exact congrArg (fun m=>m*g) (projectiveIdentity_mul Q F.entries).symm
      _=((g*f.matrix)*F.differential)*g := by rw [hgf]
      _=(g*(f.matrix*F.differential))*g := by simp only [Matrix.mul_assoc]
      _=(g*(E.differential*f.matrix))*g := by rw [f.commute]
      _=(g*E.differential)*(f.matrix*g) := by simp only [Matrix.mul_assoc]
      _=(g*E.differential)*projectiveIdentity Q E.placement :=
        congrArg (fun m=>(g*E.differential)*m) hfg
      _=g*E.differential := mul_projectiveIdentity Q (projectiveEntries_mul Q hg E.entries)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomotopyConeMap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
open _root_.Matrix

attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J L N:Type u} [Fintype I] [Fintype J] [Fintype L] [Fintype N]
  [DecidableEq I] [DecidableEq J] [DecidableEq L] [DecidableEq N]
  {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
  {G:BasedComplex Q (K:=K) L} {D:BasedComplex Q (K:=K) N}

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J]
  [DecidableEq L] [DecidableEq N] in
lemma cone_block_entries (f:Map Q E F) (g:Map Q G D)
    (a:Matrix I L (Q.Zigzag K)) (b:Matrix I N (Q.Zigzag K))
    (c:Matrix J L (Q.Zigzag K)) (d:Matrix J N (Q.Zigzag K))
    (ha:ProjectiveEntries Q E.placement G.placement a)
    (hb:ProjectiveEntries Q E.placement D.placement b)
    (hc:ProjectiveEntries Q F.placement G.placement c)
    (hd:ProjectiveEntries Q F.placement D.placement d) :
    ProjectiveEntries Q (f.cone Q).placement (g.cone Q).placement
      (Matrix.fromBlocks a b c d) := by
  constructor <;> intro i j <;> rcases i with i|i <;> rcases j with j|j
  · exact ha.1 i j
  · exact hb.1 i j
  · exact hc.1 i j
  · exact hd.1 i j
  · exact ha.2 i j
  · exact hb.2 i j
  · exact hc.2 i j
  · exact hd.2 i j

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J]
  [DecidableEq L] [DecidableEq N] in
lemma cone_block_degree (f:Map Q E F) (g:Map Q G D)
    (a:Matrix I L (Q.Zigzag K)) (b:Matrix I N (Q.Zigzag K))
    (c:Matrix J L (Q.Zigzag K)) (d:Matrix J N (Q.Zigzag K)) (n v:ℤ)
    (ha:MapDegree Q E.placement G.placement n v a)
    (hb:MapDegree Q E.placement D.placement (n-1) v b)
    (hc:MapDegree Q F.placement G.placement (n+1) v c)
    (hd:MapDegree Q F.placement D.placement n v d) :
    MapDegree Q (f.cone Q).placement (g.cone Q).placement n v
      (Matrix.fromBlocks a b c d) := by
  intro i j
  rcases i with i|i <;> rcases j with j|j
  · refine ⟨?_,(ha i j).2⟩
    intro h
    apply (ha i j).1
    change (G.placement j).cochain-1≠(E.placement i).cochain-1+n at h
    omega
  · refine ⟨?_,(hb i j).2⟩
    intro h
    apply (hb i j).1
    change (D.placement j).cochain≠(E.placement i).cochain-1+n at h
    omega
  · refine ⟨?_,(hc i j).2⟩
    intro h
    apply (hc i j).1
    change (G.placement j).cochain-1≠(F.placement i).cochain+n at h
    omega
  · exact hd i j

noncomputable def Map.homotopyConeMap (f:Map Q E F) (g:Map Q G D)
    (a:Map Q E G) (b:Map Q F D) (h:Matrix I N (Q.Zigzag K))
    (he:ProjectiveEntries Q E.placement D.placement h)
    (hd:MapDegree Q E.placement D.placement (-1) 0 h)
    (hc:f.matrix*b.matrix=a.matrix*g.matrix+(E.differential*h+h*D.differential)) :
    Map Q (f.cone Q) (g.cone Q) where
  matrix:=Matrix.fromBlocks a.matrix h 0 b.matrix
  entries:=cone_block_entries Q f g _ _ _ _ a.entries he (projectiveEntries_zero Q) b.entries
  degree:=cone_block_degree Q f g _ _ _ _ 0 0 a.degree hd (mapDegree_zero Q _ _) b.degree
  commute:=by
    change Matrix.fromBlocks (-E.differential) f.matrix 0 F.differential *
      Matrix.fromBlocks a.matrix h 0 b.matrix =
      Matrix.fromBlocks a.matrix h 0 b.matrix *
      Matrix.fromBlocks (-G.differential) g.matrix 0 D.differential
    rw [Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply]
    simp only [Matrix.neg_mul,Matrix.mul_neg,Matrix.mul_zero,Matrix.zero_mul,
      add_zero,zero_add,neg_zero,a.commute,b.commute]
    congr 1
    rw [hc]
    abel

omit [Fintype V] [DecidableEq A] in
lemma homotopy_coherence_closed (e:HomotopyEquivalence Q F G) :
    F.differential*(e.sourceHomotopy*e.forward.matrix-e.forward.matrix*e.targetHomotopy)+
      (e.sourceHomotopy*e.forward.matrix-e.forward.matrix*e.targetHomotopy)*G.differential=0 := by
  have hs:=congrArg (fun m=>m*e.forward.matrix) e.sourceEquation
  have ht:=congrArg (fun m=>e.forward.matrix*m) e.targetEquation
  have hid₁ : projectiveIdentity Q F.placement*e.forward.matrix=e.forward.matrix :=
    projectiveIdentity_mul Q e.forward.entries
  have hid₂ : e.forward.matrix*projectiveIdentity Q G.placement=e.forward.matrix :=
    mul_projectiveIdentity Q e.forward.entries
  erw [Matrix.add_mul,hid₁] at hs
  erw [Matrix.mul_add,hid₂] at ht
  have hh:(F.differential*e.sourceHomotopy+e.sourceHomotopy*F.differential)*e.forward.matrix=
      e.forward.matrix*(G.differential*e.targetHomotopy+e.targetHomotopy*G.differential) := by
    apply add_left_cancel (a:=e.forward.matrix)
    rw [← hs,← ht,Matrix.mul_assoc]
  have hc₁ : (e.sourceHomotopy*e.forward.matrix)*G.differential=
      (e.sourceHomotopy*F.differential)*e.forward.matrix := by
    rw [Matrix.mul_assoc,← e.forward.commute,← Matrix.mul_assoc]
  have hc₂ : F.differential*(e.forward.matrix*e.targetHomotopy)=
      (e.forward.matrix*G.differential)*e.targetHomotopy := by
    rw [← Matrix.mul_assoc,e.forward.commute]
  have hr : F.differential*(e.sourceHomotopy*e.forward.matrix-e.forward.matrix*e.targetHomotopy)+
      (e.sourceHomotopy*e.forward.matrix-e.forward.matrix*e.targetHomotopy)*G.differential =
      (F.differential*e.sourceHomotopy+e.sourceHomotopy*F.differential)*e.forward.matrix-
      e.forward.matrix*(G.differential*e.targetHomotopy+e.targetHomotopy*G.differential) := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.add_mul,Matrix.mul_add]
    rw [hc₁,hc₂]
    simp only [← Matrix.mul_assoc]
    abel
  rw [hr,hh,sub_self]

omit [Fintype V] [DecidableEq A] in
lemma cone_target_replace_backward_square (f:Map Q E F) (e:HomotopyEquivalence Q F G) :
    (f.matrix*e.forward.matrix)*e.backward.matrix =
      projectiveIdentity Q E.placement*f.matrix+
        (E.differential*(f.matrix*e.sourceHomotopy)+(f.matrix*e.sourceHomotopy)*F.differential) := by
  have hid : projectiveIdentity Q E.placement*f.matrix=f.matrix :=
    projectiveIdentity_mul Q f.entries
  have hid' : f.matrix*projectiveIdentity Q F.placement=f.matrix :=
    mul_projectiveIdentity Q f.entries
  erw [hid,Matrix.mul_assoc,e.sourceEquation,Matrix.mul_add,hid',Matrix.mul_add]
  simp only [← Matrix.mul_assoc]
  rw [f.commute]

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma cone_target_replace_correction (f:Map Q E F) (e:HomotopyEquivalence Q F G)
    (k:Matrix J L (Q.Zigzag K))
    (hk:k=e.sourceHomotopy*e.forward.matrix-e.forward.matrix*e.targetHomotopy)
    (hkc:F.differential*k+k*G.differential=0) :
    -(E.differential*(f.matrix*e.sourceHomotopy*k))+
      (f.matrix*e.forward.matrix)*(e.targetHomotopy+e.backward.matrix*k)+
      (f.matrix*e.sourceHomotopy*k)*G.differential =
      (f.matrix*e.sourceHomotopy)*e.forward.matrix := by
  have hb : -(E.differential*(f.matrix*e.sourceHomotopy*k))+
      (f.matrix*e.sourceHomotopy*k)*G.differential =
      f.matrix*k-(f.matrix*e.forward.matrix)*(e.backward.matrix*k) := by
    have hkc' : k*G.differential=-(F.differential*k) :=
      eq_neg_of_add_eq_zero_right hkc
    have hs : F.differential*e.sourceHomotopy+e.sourceHomotopy*F.differential =
        e.forward.matrix*e.backward.matrix-projectiveIdentity Q F.placement := by
      rw [e.sourceEquation]
      abel
    calc
      _ = -(f.matrix*((F.differential*e.sourceHomotopy+e.sourceHomotopy*F.differential)*k)) := by
        simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_assoc]
        rw [hkc']
        simp only [Matrix.mul_neg,← Matrix.mul_assoc,neg_add_rev]
        rw [f.commute]
        abel
      _ = f.matrix*k-(f.matrix*e.forward.matrix)*(e.backward.matrix*k) := by
        rw [hs,Matrix.sub_mul,Matrix.mul_sub]
        have hid : projectiveIdentity Q F.placement*k=k := by
          rw [hk]
          apply projectiveIdentity_mul Q
          simpa only [sub_eq_add_neg] using projectiveEntries_add Q
            (projectiveEntries_mul Q e.sourceEntries e.forward.entries)
            (projectiveEntries_neg Q (projectiveEntries_mul Q e.forward.entries e.targetEntries))
        erw [hid]
        simp only [Matrix.mul_assoc]
        abel
  have hsum : (f.matrix*e.forward.matrix)*(e.targetHomotopy+e.backward.matrix*k) =
      (f.matrix*e.forward.matrix)*e.targetHomotopy+
        (f.matrix*e.forward.matrix)*(e.backward.matrix*k) := Matrix.mul_add _ _ _
  rw [hsum]
  calc
    _ = (-(E.differential*(f.matrix*e.sourceHomotopy*k))+
          (f.matrix*e.sourceHomotopy*k)*G.differential)+
        ((f.matrix*e.forward.matrix)*e.targetHomotopy+
          (f.matrix*e.forward.matrix)*(e.backward.matrix*k)) := by abel
    _ = (f.matrix*e.sourceHomotopy)*e.forward.matrix := by
      rw [hb,hk,Matrix.mul_sub]
      simp only [Matrix.mul_assoc]
      abel

noncomputable def HomotopyEquivalence.coneTarget (e:HomotopyEquivalence Q F G) (f:Map Q E F) :
    HomotopyEquivalence Q (f.cone Q) ((f.comp Q e.forward).cone Q) := by
  let g:=f.comp Q e.forward
  let k:=e.sourceHomotopy*e.forward.matrix-e.forward.matrix*e.targetHomotopy
  have ke:ProjectiveEntries Q F.placement G.placement k := by
    simpa only [k,sub_eq_add_neg] using projectiveEntries_add Q
      (projectiveEntries_mul Q e.sourceEntries e.forward.entries)
      (projectiveEntries_neg Q (projectiveEntries_mul Q e.forward.entries e.targetEntries))
  have kd:MapDegree Q F.placement G.placement (-1) 0 k := by
    have h₁:=mapDegree_mul Q e.sourceDegree e.forward.degree
    have h₂:=mapDegree_mul Q e.forward.degree e.targetDegree
    simp only [add_zero,zero_add] at h₁ h₂
    simpa only [k,sub_eq_add_neg] using mapDegree_add Q h₁ (mapDegree_neg Q h₂)
  have kc:F.differential*k+k*G.differential=0 := homotopy_coherence_closed Q e
  let j:=e.targetHomotopy+e.backward.matrix*k
  have je:ProjectiveEntries Q G.placement G.placement j :=
    projectiveEntries_add Q e.targetEntries (projectiveEntries_mul Q e.backward.entries ke)
  have jd:MapDegree Q G.placement G.placement (-1) 0 j :=
    mapDegree_add Q e.targetDegree (mapDegree_mul Q e.backward.degree kd)
  have jc:G.differential*j+j*G.differential=
      G.differential*e.targetHomotopy+e.targetHomotopy*G.differential := by
    have hz:G.differential*(e.backward.matrix*k)+(e.backward.matrix*k)*G.differential=0 := by
      rw [← Matrix.mul_assoc,e.backward.commute]
      simpa only [Matrix.mul_add,Matrix.mul_assoc,Matrix.mul_zero] using
        congrArg (fun m=>e.backward.matrix*m) kc
    dsimp only [j]
    simp only [Matrix.mul_add,Matrix.add_mul]
    calc
      _ = (G.differential*e.targetHomotopy+e.targetHomotopy*G.differential)+
          (G.differential*(e.backward.matrix*k)+(e.backward.matrix*k)*G.differential) := by abel
      _ = _ := by rw [hz,add_zero]
  have pe:ProjectiveEntries Q E.placement F.placement (f.matrix*e.sourceHomotopy) :=
    projectiveEntries_mul Q f.entries e.sourceEntries
  have pd:MapDegree Q E.placement F.placement (-1) 0 (f.matrix*e.sourceHomotopy) :=
    mapDegree_mul Q f.degree e.sourceDegree
  let a:Map Q (f.cone Q) (g.cone Q):=f.coneMap Q g (Map.identity Q E) e.forward (by
    change projectiveIdentity Q E.placement*(f.matrix*e.forward.matrix)=_
    exact projectiveIdentity_mul Q (projectiveEntries_mul Q f.entries e.forward.entries))
  let b:Map Q (g.cone Q) (f.cone Q):=g.homotopyConeMap Q f (Map.identity Q E) e.backward
    (f.matrix*e.sourceHomotopy) pe pd (cone_target_replace_backward_square Q f e)
  let h:=Matrix.fromBlocks (0:Matrix I I (Q.Zigzag K)) (0:Matrix I J (Q.Zigzag K))
      (0:Matrix J I (Q.Zigzag K)) e.sourceHomotopy
  let t:=Matrix.fromBlocks (0:Matrix I I (Q.Zigzag K)) (f.matrix*e.sourceHomotopy*k)
      (0:Matrix L I (Q.Zigzag K)) j
  refine ⟨a,b,h,t,?_,?_,?_,?_,?_,?_⟩
  · exact cone_block_entries Q f f _ _ _ _ (projectiveEntries_zero Q)
      (projectiveEntries_zero Q) (projectiveEntries_zero Q) e.sourceEntries
  · exact cone_block_entries Q g g _ _ _ _ (projectiveEntries_zero Q)
      (projectiveEntries_mul Q pe ke) (projectiveEntries_zero Q) je
  · exact cone_block_degree Q f f _ _ _ _ (-1) 0 (mapDegree_zero Q _ _)
      (mapDegree_zero Q _ _) (mapDegree_zero Q _ _) e.sourceDegree
  · exact cone_block_degree Q g g _ _ _ _ (-1) 0 (mapDegree_zero Q _ _)
      (mapDegree_mul Q pd kd) (mapDegree_zero Q _ _) jd
  · change Matrix.fromBlocks (projectiveIdentity Q E.placement) 0 0 e.forward.matrix *
      Matrix.fromBlocks (projectiveIdentity Q E.placement) (f.matrix*e.sourceHomotopy) 0 e.backward.matrix =
      projectiveIdentity Q (f.cone Q).placement+
        (Matrix.fromBlocks (-E.differential) f.matrix 0 F.differential*h+
          h*Matrix.fromBlocks (-E.differential) f.matrix 0 F.differential)
    dsimp only [h]
    rw [cone_identity_blocks,Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply,Matrix.fromBlocks_add,Matrix.fromBlocks_add]
    simp only [Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add]
    have hi:projectiveIdentity Q E.placement*projectiveIdentity Q E.placement=
        projectiveIdentity Q E.placement :=projectiveIdentity_mul Q (projectiveEntries_identity Q (K:=K) (p:=E.placement))
    have hp:projectiveIdentity Q E.placement*(f.matrix*e.sourceHomotopy)=
        f.matrix*e.sourceHomotopy := projectiveIdentity_mul Q pe
    erw [hi,hp,e.sourceEquation]
  · change Matrix.fromBlocks (projectiveIdentity Q E.placement) (f.matrix*e.sourceHomotopy) 0 e.backward.matrix *
      Matrix.fromBlocks (projectiveIdentity Q E.placement) 0 0 e.forward.matrix =
      projectiveIdentity Q (g.cone Q).placement+
        (Matrix.fromBlocks (-E.differential) g.matrix 0 G.differential*t+
          t*Matrix.fromBlocks (-E.differential) g.matrix 0 G.differential)
    dsimp only [t]
    rw [cone_identity_blocks,Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply,Matrix.fromBlocks_add,Matrix.fromBlocks_add]
    simp only [Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add,Matrix.neg_mul]
    have hi:projectiveIdentity Q E.placement*projectiveIdentity Q E.placement=
        projectiveIdentity Q E.placement :=projectiveIdentity_mul Q (projectiveEntries_identity Q (K:=K) (p:=E.placement))
    erw [hi,jc,← e.targetEquation]
    congr 1
    exact (cone_target_replace_correction Q f e k rfl kc).symm

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_Cone
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
open _root_.Matrix

attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J L:Type u} [Fintype I] [Fintype J] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq L]
  {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
  {G:BasedComplex Q (K:=K) L}

omit [Fintype V] [DecidableEq A] in
lemma cone_source_replace_backward_square (e:HomotopyEquivalence Q E G) (f:Map Q G F) :
    f.matrix*projectiveIdentity Q F.placement =
      e.backward.matrix*(e.forward.matrix*f.matrix)+
        (G.differential*(-(e.targetHomotopy*f.matrix))+
          (-(e.targetHomotopy*f.matrix))*F.differential) := by
  have hid : f.matrix*projectiveIdentity Q F.placement=f.matrix :=
    mul_projectiveIdentity Q f.entries
  have hid' : projectiveIdentity Q G.placement*f.matrix=f.matrix :=
    projectiveIdentity_mul Q f.entries
  rw [hid]
  simp only [Matrix.mul_neg,Matrix.neg_mul,← Matrix.mul_assoc]
  rw [e.targetEquation,Matrix.add_mul]
  erw [hid']
  simp only [Matrix.add_mul,Matrix.mul_assoc]
  rw [← f.commute]
  abel

omit [Fintype V] [DecidableEq A] [DecidableEq J] in
lemma cone_source_replace_correction (e:HomotopyEquivalence Q E G) (f:Map Q G F)
    (k:Matrix I L (Q.Zigzag K))
    (hk:k=e.sourceHomotopy*e.forward.matrix-e.forward.matrix*e.targetHomotopy)
    (hkc:E.differential*k+k*G.differential=0) :
    -(E.differential*(-(k*e.targetHomotopy*f.matrix)))+
      (-(e.sourceHomotopy-k*e.backward.matrix))*(e.forward.matrix*f.matrix)+
      (-(k*e.targetHomotopy*f.matrix))*F.differential =
      e.forward.matrix*(-(e.targetHomotopy*f.matrix)) := by
  have kc:E.differential*k=-(k*G.differential) := eq_neg_of_add_eq_zero_left hkc
  have hs:G.differential*e.targetHomotopy+e.targetHomotopy*G.differential =
      e.backward.matrix*e.forward.matrix-projectiveIdentity Q G.placement := by
    rw [e.targetEquation]
    abel
  have ke:ProjectiveEntries Q E.placement G.placement k := by
    rw [hk]
    simpa only [sub_eq_add_neg] using projectiveEntries_add Q
      (projectiveEntries_mul Q e.sourceEntries e.forward.entries)
      (projectiveEntries_neg Q (projectiveEntries_mul Q e.forward.entries e.targetEntries))
  have hid:k*projectiveIdentity Q G.placement=k := mul_projectiveIdentity Q ke
  have hb : -(E.differential*(-(k*e.targetHomotopy*f.matrix)))+
      (-(k*e.targetHomotopy*f.matrix))*F.differential =
      k*f.matrix-(k*e.backward.matrix)*(e.forward.matrix*f.matrix) := by
    calc
      _ = -(k*(G.differential*e.targetHomotopy+e.targetHomotopy*G.differential)*f.matrix) := by
        simp only [Matrix.mul_neg,Matrix.neg_mul,neg_neg,← Matrix.mul_assoc]
        rw [kc]
        simp only [Matrix.neg_mul,Matrix.mul_add,Matrix.add_mul,Matrix.mul_assoc]
        rw [← f.commute]
        abel
      _ = _ := by
        rw [hs,Matrix.mul_sub,Matrix.sub_mul]
        erw [hid]
        simp only [Matrix.mul_assoc]
        abel
  calc
    _ = (-(E.differential*(-(k*e.targetHomotopy*f.matrix)))+
          (-(k*e.targetHomotopy*f.matrix))*F.differential)+
          (-(e.sourceHomotopy-k*e.backward.matrix))*(e.forward.matrix*f.matrix) := by abel
    _ = _ := by
      rw [hb]
      simp only [Matrix.neg_mul,Matrix.sub_mul,Matrix.mul_assoc]
      calc
        _ = (k-e.sourceHomotopy*e.forward.matrix)*f.matrix := by
          simp only [Matrix.sub_mul,Matrix.mul_assoc]
          abel
        _ = _ := by
          rw [hk]
          simp only [Matrix.sub_mul,Matrix.mul_neg,Matrix.mul_assoc]
          abel

noncomputable def HomotopyEquivalence.coneSource (e:HomotopyEquivalence Q E G) (f:Map Q G F) :
    HomotopyEquivalence Q ((e.forward.comp Q f).cone Q) (f.cone Q) := by
  let g:=e.forward.comp Q f
  let k:=e.sourceHomotopy*e.forward.matrix-e.forward.matrix*e.targetHomotopy
  have ke:ProjectiveEntries Q E.placement G.placement k := by
    simpa only [k,sub_eq_add_neg] using projectiveEntries_add Q
      (projectiveEntries_mul Q e.sourceEntries e.forward.entries)
      (projectiveEntries_neg Q (projectiveEntries_mul Q e.forward.entries e.targetEntries))
  have kd:MapDegree Q E.placement G.placement (-1) 0 k := by
    have h₁:=mapDegree_mul Q e.sourceDegree e.forward.degree
    have h₂:=mapDegree_mul Q e.forward.degree e.targetDegree
    simp only [add_zero,zero_add] at h₁ h₂
    simpa only [k,sub_eq_add_neg] using mapDegree_add Q h₁ (mapDegree_neg Q h₂)
  have kc:E.differential*k+k*G.differential=0 := homotopy_coherence_closed Q e
  let h:=e.sourceHomotopy-k*e.backward.matrix
  have he:ProjectiveEntries Q E.placement E.placement h := by
    simpa only [h,sub_eq_add_neg] using projectiveEntries_add Q e.sourceEntries
      (projectiveEntries_neg Q (projectiveEntries_mul Q ke e.backward.entries))
  have hd:MapDegree Q E.placement E.placement (-1) 0 h := by
    simpa only [h,sub_eq_add_neg] using mapDegree_add Q e.sourceDegree
      (mapDegree_neg Q (mapDegree_mul Q kd e.backward.degree))
  have hc:E.differential*h+h*E.differential=
      E.differential*e.sourceHomotopy+e.sourceHomotopy*E.differential := by
    have hz:E.differential*(k*e.backward.matrix)+(k*e.backward.matrix)*E.differential=0 := by
      simp only [Matrix.mul_assoc]
      rw [← e.backward.commute]
      simpa only [Matrix.add_mul,Matrix.mul_assoc,Matrix.zero_mul] using
        congrArg (fun m=>m*e.backward.matrix) kc
    dsimp only [h]
    simp only [Matrix.mul_sub,Matrix.sub_mul]
    calc
      _ = (E.differential*e.sourceHomotopy+e.sourceHomotopy*E.differential)-
          (E.differential*(k*e.backward.matrix)+(k*e.backward.matrix)*E.differential) := by abel
      _ = _ := by rw [hz,sub_zero]
  have pe:ProjectiveEntries Q G.placement F.placement (-(e.targetHomotopy*f.matrix)) :=
    projectiveEntries_neg Q (projectiveEntries_mul Q e.targetEntries f.entries)
  have pd:MapDegree Q G.placement F.placement (-1) 0 (-(e.targetHomotopy*f.matrix)) :=
    mapDegree_neg Q (mapDegree_mul Q e.targetDegree f.degree)
  let a:Map Q (g.cone Q) (f.cone Q):=g.coneMap Q f e.forward (Map.identity Q F) (by
    change _=(e.forward.matrix*f.matrix)*projectiveIdentity Q F.placement
    exact (mul_projectiveIdentity Q (projectiveEntries_mul Q e.forward.entries f.entries)).symm)
  let b:Map Q (f.cone Q) (g.cone Q):=f.homotopyConeMap Q g e.backward (Map.identity Q F)
    (-(e.targetHomotopy*f.matrix)) pe pd (cone_source_replace_backward_square Q e f)
  let s:=Matrix.fromBlocks (-h) (-(k*e.targetHomotopy*f.matrix))
      (0:Matrix J I (Q.Zigzag K)) (0:Matrix J J (Q.Zigzag K))
  let t:=Matrix.fromBlocks (-e.targetHomotopy) (0:Matrix L J (Q.Zigzag K))
      (0:Matrix J L (Q.Zigzag K)) (0:Matrix J J (Q.Zigzag K))
  refine ⟨a,b,s,t,?_,?_,?_,?_,?_,?_⟩
  · exact cone_block_entries Q g g _ _ _ _ (projectiveEntries_neg Q he)
      (projectiveEntries_neg Q (projectiveEntries_mul Q (projectiveEntries_mul Q ke e.targetEntries) f.entries))
      (projectiveEntries_zero Q) (projectiveEntries_zero Q)
  · exact cone_block_entries Q f f _ _ _ _ (projectiveEntries_neg Q e.targetEntries)
      (projectiveEntries_zero Q) (projectiveEntries_zero Q) (projectiveEntries_zero Q)
  · exact cone_block_degree Q g g _ _ _ _ (-1) 0 (mapDegree_neg Q hd)
      (mapDegree_neg Q (mapDegree_mul Q (mapDegree_mul Q kd e.targetDegree) f.degree))
      (mapDegree_zero Q _ _) (mapDegree_zero Q _ _)
  · exact cone_block_degree Q f f _ _ _ _ (-1) 0 (mapDegree_neg Q e.targetDegree)
      (mapDegree_zero Q _ _) (mapDegree_zero Q _ _) (mapDegree_zero Q _ _)
  · change Matrix.fromBlocks e.forward.matrix 0 0 (projectiveIdentity Q F.placement) *
      Matrix.fromBlocks e.backward.matrix (-(e.targetHomotopy*f.matrix)) 0 (projectiveIdentity Q F.placement) =
      projectiveIdentity Q (g.cone Q).placement+
        (Matrix.fromBlocks (-E.differential) g.matrix 0 F.differential*s+
          s*Matrix.fromBlocks (-E.differential) g.matrix 0 F.differential)
    dsimp only [s]
    rw [cone_identity_blocks,Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply,Matrix.fromBlocks_add,Matrix.fromBlocks_add]
    simp only [Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add,Matrix.neg_mul,Matrix.mul_neg,neg_neg]
    have hi:projectiveIdentity Q F.placement*projectiveIdentity Q F.placement=
        projectiveIdentity Q F.placement :=
      projectiveIdentity_mul Q (projectiveEntries_identity Q (K:=K) (p:=F.placement))
    erw [hi,hc,← e.sourceEquation]
    simp only [neg_zero,zero_add,add_zero]
    congr 1
    simpa only [h,g,Map.comp,Matrix.neg_mul,Matrix.mul_neg,neg_neg,add_assoc] using
      (cone_source_replace_correction Q e f k rfl kc).symm
  · change Matrix.fromBlocks e.backward.matrix (-(e.targetHomotopy*f.matrix)) 0 (projectiveIdentity Q F.placement) *
      Matrix.fromBlocks e.forward.matrix 0 0 (projectiveIdentity Q F.placement) =
      projectiveIdentity Q (f.cone Q).placement+
        (Matrix.fromBlocks (-G.differential) f.matrix 0 F.differential*t+
          t*Matrix.fromBlocks (-G.differential) f.matrix 0 F.differential)
    dsimp only [t]
    rw [cone_identity_blocks,Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply,Matrix.fromBlocks_add,Matrix.fromBlocks_add]
    simp only [Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add,Matrix.neg_mul,Matrix.mul_neg,neg_neg]
    have hi:projectiveIdentity Q F.placement*projectiveIdentity Q F.placement=
        projectiveIdentity Q F.placement :=
      projectiveIdentity_mul Q (projectiveEntries_identity Q (K:=K) (p:=F.placement))
    have hp:(e.targetHomotopy*f.matrix)*projectiveIdentity Q F.placement=
        e.targetHomotopy*f.matrix :=
      mul_projectiveIdentity Q (projectiveEntries_mul Q e.targetEntries f.entries)
    erw [hi,hp,e.targetEquation]
    simp only [neg_zero,zero_add]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_SignDiagonal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
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

omit [Fintype I] in
lemma signDiagonal_degree (p:I→GeneratorPlacement V) (ε:I→Bool) :
    MapDegree Q p p 0 0 (signDiagonal Q (K:=K) p ε) := by
  intro i j
  by_cases h:i=j
  · subst j
    simp only [signDiagonal,Matrix.diagonal_apply_eq]
    split_ifs
    · simpa only [Matrix.neg_apply,projectiveIdentity,Matrix.diagonal_apply_eq] using
        (mapDegree_neg Q (mapDegree_identity Q (K:=K) (p:=p)) i i)
    · simpa only [projectiveIdentity,Matrix.diagonal_apply_eq] using
        (mapDegree_identity Q (K:=K) (p:=p) i i)
  · simp only [signDiagonal,Matrix.diagonal_apply_ne _ h]
    constructor
    · intro; trivial
    · exact homogeneous_zero Q _

namespace BasedComplex
noncomputable def signChainIsomorphism (E F:BasedComplex Q (K:=K) I) (ε:I→Bool)
    (hp:F.placement=E.placement)
    (hd:∀ i j,(if ε j then -E.differential i j else E.differential i j)=
      (if ε i then -F.differential i j else F.differential i j)) :
    ChainIsomorphism Q E F := by
  let s:=signDiagonal Q (K:=K) E.placement ε
  have he:ProjectiveEntries Q E.placement F.placement s := by
    rw [hp]; exact signDiagonal_entries Q _ _
  have hdeg:MapDegree Q E.placement F.placement 0 0 s := by
    rw [hp]; exact signDiagonal_degree Q _ _
  let f:Map Q E F:=⟨s,he,hdeg,by
    apply Matrix.ext
    intro i j
    have hF:ProjectiveEntries Q E.placement F.placement F.differential := by
      rw [← hp]; exact F.entries
    exact (mul_signDiagonal Q ε E.differential E.entries i j).trans
      ((hd i j).trans (signDiagonal_mul Q ε F.differential hF i j).symm)⟩
  have hg:ProjectiveEntries Q F.placement E.placement s := by
    rw [hp]; exact signDiagonal_entries Q _ _
  have hgd:MapDegree Q F.placement E.placement 0 0 s := by
    rw [hp]; exact signDiagonal_degree Q _ _
  have hs:f.matrix*s=projectiveIdentity Q E.placement := signDiagonal_square Q _ _
  have ht:s*f.matrix=projectiveIdentity Q F.placement := by
    rw [hp]; exact signDiagonal_square Q _ _
  refine ⟨f,⟨s,hg,hgd,?_⟩,hs,ht⟩
  calc
    F.differential*s=(projectiveIdentity Q F.placement*F.differential)*s := by
      exact congrArg (fun matrix=>matrix*s) (projectiveIdentity_mul Q F.entries).symm
    _=((s*f.matrix)*F.differential)*s := by rw [ht]
    _=(s*(f.matrix*F.differential))*s := by simp only [Matrix.mul_assoc]
    _=(s*(E.differential*f.matrix))*s := by rw [f.commute]
    _=(s*E.differential)*(f.matrix*s) := by simp only [Matrix.mul_assoc]
    _=(s*E.differential)*projectiveIdentity Q E.placement := by rw [hs]
    _=s*E.differential := mul_projectiveIdentity Q (projectiveEntries_mul Q hg E.entries)

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PositiveConeIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
open _root_.Matrix

attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}

def positiveConeIndex (f:Map Q E F) (α:V) :
    ((TestIndex Q E.placement α ⊕ I) ⊕ (TestIndex Q F.placement α ⊕ J)) ≃
      (TestIndex Q (f.cone Q).placement α ⊕ (I ⊕ J)) where
  toFun
    | .inl (.inl p) => .inl ⟨.inl p.1,p.2⟩
    | .inl (.inr i) => .inr (.inl i)
    | .inr (.inl p) => .inl ⟨.inr p.1,p.2⟩
    | .inr (.inr j) => .inr (.inr j)
  invFun
    | .inl ⟨.inl i,p⟩ => .inl (.inl ⟨i,p⟩)
    | .inl ⟨.inr j,p⟩ => .inr (.inl ⟨j,p⟩)
    | .inr (.inl i) => .inl (.inr i)
    | .inr (.inr j) => .inr (.inr j)
  left_inv := by intro k;rcases k with (p|i)|(p|j) <;> rfl
  right_inv := by intro k;rcases k with ⟨i|j,p⟩|(i|j) <;> rfl

def positiveConeSign (α:V) :
    ((TestIndex Q E.placement α ⊕ I) ⊕ (TestIndex Q F.placement α ⊕ J)) → Bool
  | .inl (.inl _) => true
  | _ => false

omit [DecidableEq I] [DecidableEq J] in
lemma positiveCone_placement (f:Map Q E F) (α:V) :
    ((f.positiveTwist Q α).cone Q).placement =
      (((f.cone Q).positiveTwist Q α).reindex Q (positiveConeIndex Q f α)).placement := by
  funext k
  rcases k with (p|i)|(p|j) <;> rfl

lemma positiveCone_differential (f:Map Q E F) (α:V)
    (i j:(TestIndex Q E.placement α ⊕ I) ⊕ (TestIndex Q F.placement α ⊕ J)) :
    (if positiveConeSign Q (E:=E) (F:=F) α j then
      -((((f.cone Q).positiveTwist Q α).reindex Q (positiveConeIndex Q f α)).differential i j)
     else (((f.cone Q).positiveTwist Q α).reindex Q (positiveConeIndex Q f α)).differential i j) =
    (if positiveConeSign Q (E:=E) (F:=F) α i then
      -(((f.positiveTwist Q α).cone Q).differential i j)
     else ((f.positiveTwist Q α).cone Q).differential i j) := by
  rcases i with (p|i)|(p|i) <;> rcases j with (r|j)|(r|j)
  · change -(-((pathCoordinates Q (pathBasis Q (K:=K) p.2.val * (-E.differential p.1 r.1)) r.2.val) • vertexId Q α)) =
      -(-(-((pathCoordinates Q (pathBasis Q (K:=K) p.2.val * E.differential p.1 r.1) r.2.val) • vertexId Q α)))
    simp only [neg_neg,mul_neg,map_neg,Pi.neg_apply,neg_smul]
  · change evaluationMatrix Q (f.cone Q).placement α ⟨.inl p.1,p.2⟩ (.inl j) =
      -(-evaluationMatrix Q E.placement α p j)
    simp only [evaluationMatrix,Sum.inl.injEq,neg_neg]
    split_ifs <;> rfl
  · rfl
  · change evaluationMatrix Q (f.cone Q).placement α ⟨.inl p.1,p.2⟩ (.inr j) = -(0:Q.Zigzag K)
    simp only [evaluationMatrix,Sum.inl_ne_inr,ite_false, if_false,neg_zero]
  · change -(0:Q.Zigzag K)= -0
    simp only [neg_zero]
  · rfl
  · rfl
  · rfl
  · change -(-((pathCoordinates Q (pathBasis Q (K:=K) p.2.val * 0) r.2.val) • vertexId Q α))=0
    simp only [mul_zero,map_zero,Pi.zero_apply,zero_smul,neg_zero]
  · change evaluationMatrix Q (f.cone Q).placement α ⟨.inr p.1,p.2⟩ (.inl j)=0
    simp only [evaluationMatrix,Sum.inr_ne_inl,ite_false, if_false]
  · rfl
  · change evaluationMatrix Q (f.cone Q).placement α ⟨.inr p.1,p.2⟩ (.inr j)=
      evaluationMatrix Q F.placement α p j
    simp only [evaluationMatrix,Sum.inr.injEq]
    split_ifs <;> rfl
  · change -(0:Q.Zigzag K)=0
    simp only [neg_zero]
  · rfl
  · rfl
  · rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_Cone2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

def ClassCone (x y z:FiniteHomotopyClass Q (K:=K)) : Prop :=
  ∃ E F:FiniteModel Q (K:=K), ∃ f:Map Q E.complex F.complex,
    classOfComplex Q E.complex=x ∧ classOfComplex Q F.complex=y ∧
    classOfComplex Q (f.cone Q)=z

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_EmptyTestIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I:Type u} [Fintype I] [DecidableEq I]

def emptyTestIndex (E:BasedComplex Q (K:=K) I) (α:V)
    (h:IsEmpty (TestIndex Q E.placement α)) : I ≃ I ⊕ TestIndex Q E.placement α where
  toFun:=Sum.inl
  invFun
    | .inl i=>i
    | .inr p=>h.false p |>.elim
  left_inv _:=rfl
  right_inv k:=by cases k with
    | inl i=>rfl
    | inr p=>exact (h.false p).elim

omit [DecidableEq I] in
lemma negativeTwist_empty_reindex (E:BasedComplex Q (K:=K) I) (α:V)
    (h:IsEmpty (TestIndex Q E.placement α)) :
    (E.negativeTwist Q α).reindex Q (emptyTestIndex Q E α h)=E := by
  apply ext_placement_differential Q <;> rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_NegativeConeIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
open _root_.Matrix

attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}

def negativeConeIndex (f:Map Q E F) (α:V) :
    ((I ⊕ TestIndex Q E.placement α) ⊕ (J ⊕ TestIndex Q F.placement α)) ≃
      ((I ⊕ J) ⊕ TestIndex Q (f.cone Q).placement α) where
  toFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr p) => .inr ⟨.inl p.1,p.2⟩
    | .inr (.inl j) => .inl (.inr j)
    | .inr (.inr p) => .inr ⟨.inr p.1,p.2⟩
  invFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr j) => .inr (.inl j)
    | .inr ⟨.inl i,p⟩ => .inl (.inr ⟨i,p⟩)
    | .inr ⟨.inr j,p⟩ => .inr (.inr ⟨j,p⟩)
  left_inv := by
    intro k; rcases k with (i|p)|(j|p) <;> rfl
  right_inv := by
    intro k; rcases k with (i|j)|⟨i|j,p⟩ <;> rfl

def negativeConeSign (α:V) :
    ((I ⊕ TestIndex Q E.placement α) ⊕ (J ⊕ TestIndex Q F.placement α)) → Bool
  | .inl (.inr _) => true
  | _ => false

omit [DecidableEq I] [DecidableEq J] in
lemma negativeCone_placement (f:Map Q E F) (α:V) :
    ((f.negativeTwist Q α).cone Q).placement =
      (((f.cone Q).negativeTwist Q α).reindex Q (negativeConeIndex Q f α)).placement := by
  funext k
  rcases k with (i|p)|(j|p)
  · rfl
  · change GeneratorPlacement.mk α ((E.placement p.1).cochain+1-1)
        ((E.placement p.1).internal+Path.length p.2.val-2) =
      GeneratorPlacement.mk α ((E.placement p.1).cochain-1+1)
        ((E.placement p.1).internal+Path.length p.2.val-2)
    congr 1
    omega
  · rfl
  · rfl

lemma negativeCone_differential (f:Map Q E F) (α:V)
    (i j:(I ⊕ TestIndex Q E.placement α) ⊕ (J ⊕ TestIndex Q F.placement α)) :
    (if negativeConeSign Q (E:=E) (F:=F) α j then
      -((((f.cone Q).negativeTwist Q α).reindex Q (negativeConeIndex Q f α)).differential i j)
     else (((f.cone Q).negativeTwist Q α).reindex Q (negativeConeIndex Q f α)).differential i j) =
    (if negativeConeSign Q (E:=E) (F:=F) α i then
      -(((f.negativeTwist Q α).cone Q).differential i j)
     else ((f.negativeTwist Q α).cone Q).differential i j) := by
  rcases i with (i|p)|(i|p) <;> rcases j with (j|r)|(j|r)
  · rfl
  · change -coevaluationMatrix Q (f.cone Q).placement α (.inl i) ⟨.inl r.1,r.2⟩ =
      -coevaluationMatrix Q E.placement α i r
    simp only [coevaluationMatrix, Sum.inl.injEq]
    split_ifs <;> rfl
  · rfl
  · change coevaluationMatrix Q (f.cone Q).placement α (.inl i) ⟨.inr r.1,r.2⟩ = 0
    simp only [coevaluationMatrix, Sum.inl_ne_inr,ite_false, if_false]
  · change (0:Q.Zigzag K)= -(-0)
    simp only [neg_zero]
  · change -(-((pathCoordinates Q (pathBasis Q (K:=K) p.2.val * (-E.differential p.1 r.1)) r.2.val) • vertexId Q α)) =
      -(-(-((pathCoordinates Q (pathBasis Q (K:=K) p.2.val * E.differential p.1 r.1) r.2.val) • vertexId Q α)))
    simp only [neg_neg,mul_neg,map_neg,Pi.neg_apply,neg_smul]
  · change (0:Q.Zigzag K)= -0
    simp only [neg_zero]
  · rfl
  · rfl
  · change -coevaluationMatrix Q (f.cone Q).placement α (.inr i) ⟨.inl r.1,r.2⟩ = 0
    simp only [coevaluationMatrix, Sum.inr_ne_inl,ite_false, if_false,neg_zero]
  · rfl
  · change coevaluationMatrix Q (f.cone Q).placement α (.inr i) ⟨.inr r.1,r.2⟩ =
      coevaluationMatrix Q F.placement α i r
    simp only [coevaluationMatrix, Sum.inr.injEq]
    split_ifs <;> rfl
  · rfl
  · change -(-((pathCoordinates Q (pathBasis Q (K:=K) p.2.val * 0) r.2.val) • vertexId Q α))=0
    simp only [mul_zero,map_zero,Pi.zero_apply,zero_smul,neg_zero]
  · rfl
  · rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_NegativeTwistModern
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I:Type u} [Fintype I] [DecidableEq I]

noncomputable def HomotopyEquivalence.negativeTwistModern
    {J:Type u} [Fintype J] [DecidableEq J]
    {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (e:HomotopyEquivalence Q E F) (α:V) :
    HomotopyEquivalence Q (E.negativeTwist Q α) (F.negativeTwist Q α) := by
  convert e.negativeTwist Q α using 1
  all_goals try with_reducible_and_instances rfl

noncomputable def allPureIndex (E:BasedComplex Q (K:=K) I) (q:ℤ)
    (h:∀ i,(E.placement i).level=q) : I ≃ {i:I // (E.placement i).level=q} where
  toFun i:=⟨i,h i⟩
  invFun i:=i.val
  left_inv _:=rfl
  right_inv _:=rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PlacementSignedWeight
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex
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

noncomputable def signedGeneratorVector {I : Type u} [Fintype I]
    (E : BasedComplex Q (K:=K) I) (v : V) : ℝ :=
  ∑ i, placementSignedWeight (E.placement i) v

omit [Fintype V] [DecidableEq A] in
lemma signedGeneratorVector_array {I : Type u} [Fintype I]
    (E : BasedComplex Q (K:=K) I) (v : V) :
    signedGeneratorVector Q E v=
      Finsupp.liftAddHom (fun a => multiplesHom ℝ (placementSignedWeight a v)) (E.generatorArray Q) := by
  simp only [signedGeneratorVector,generatorArray,map_sum,Finsupp.liftAddHom_apply_single]
  simp

omit [Fintype V] [DecidableEq A] in
lemma ScalarPivot.signedWeight_cancel {I : Type u} [Fintype I]
    {E : BasedComplex Q (K:=K) I} (p : ScalarPivot Q E) (v : V) :
    placementSignedWeight (E.placement p.source) v+
      placementSignedWeight (E.placement p.target) v=0 := by
  have hl : (E.placement p.target).level=(E.placement p.source).level+1 := by
    simp only [GeneratorPlacement.level,p.cochain,p.internal]
    omega
  simp only [placementSignedWeight,p.color,hl,cochainSign_add_one]
  split_ifs <;> ring

omit [Fintype V] [DecidableEq A] in
lemma ScalarPivot.signedGeneratorVector_reduced {I : Type u} [Fintype I] [DecidableEq I]
    {E : BasedComplex Q (K:=K) I} (p : ScalarPivot Q E) :
    signedGeneratorVector Q (p.reduced Q)=signedGeneratorVector Q E := by
  funext v
  let f : I → ℝ := fun i => placementSignedWeight (E.placement i) v
  have hs : ∑ i : p.Retained Q, f i =
      ∑ i ∈ ((Finset.univ : Finset I).erase p.source).erase p.target, f i := by
    symm
    apply Finset.sum_subtype
    intro i
    simp [and_comm]
  change (∑ i : p.Retained Q, f i)=∑ i, f i
  rw [hs]
  have h1 := Finset.sum_erase_add (Finset.univ : Finset I) f (Finset.mem_univ p.source)
  have h2 := Finset.sum_erase_add ((Finset.univ : Finset I).erase p.source) f
    (by simp [p.distinct.symm] : p.target∈(Finset.univ : Finset I).erase p.source)
  have hc := p.signedWeight_cancel Q v
  change f p.source + f p.target=0 at hc
  linarith

namespace FiniteModel

omit [Fintype V] [DecidableEq A] in
theorem exists_minimal_signed (E : FiniteModel.{u} Q (K:=K)) :
    ∃ F : FiniteModel.{u} Q (K:=K), F.complex.IsMinimal Q ∧
      Nonempty (HomotopyEquivalence Q E.complex F.complex) ∧
      signedGeneratorVector Q E.complex=signedGeneratorVector Q F.complex := by
  have h : ∀ n (B : FiniteModel.{u} Q (K:=K)), Fintype.card B.Index=n →
      ∃ F : FiniteModel.{u} Q (K:=K), F.complex.IsMinimal Q ∧
        Nonempty (HomotopyEquivalence Q B.complex F.complex) ∧
        signedGeneratorVector Q B.complex=signedGeneratorVector Q F.complex := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro B hn
      by_cases hm : B.complex.IsMinimal Q
      · exact ⟨B,hm,⟨HomotopyEquivalence.refl Q B.complex⟩,rfl⟩
      obtain ⟨p⟩ := scalarPivot_of_not_minimal Q B.complex hm
      let C := ofComplex Q (p.reduced Q)
      have hc : Fintype.card C.Index<n := by
        dsimp only [C,ofComplex]
        rw [← hn]
        exact p.retained_card_lt Q
      obtain ⟨F,hF,⟨e⟩,hs⟩ := ih (Fintype.card C.Index) hc C rfl
      exact ⟨F,hF,⟨(p.reductionEquivalence Q).trans Q e⟩,
        (p.signedGeneratorVector_reduced Q).symm.trans hs⟩
  exact h (Fintype.card E.Index) E rfl

end FiniteModel

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PositiveTwistModern
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I:Type u} [Fintype I] [DecidableEq I]

noncomputable def HomotopyEquivalence.positiveTwistModern
    {J:Type u} [Fintype J] [DecidableEq J]
    {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (e:HomotopyEquivalence Q E F) (α:V) :
    HomotopyEquivalence Q (E.positiveTwist Q α) (F.positiveTwist Q α) := by
  convert e.positiveTwist Q α using 1
  all_goals try with_reducible_and_instances rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PositiveWordActionTest
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma exists_top_test (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) (t:ℤ)
    (hex:∃n:ℕ,ClassTestUpper Q x U (t+n)) (hnot:¬ClassTestUpper Q x U t) :
    ∃l:ℤ,t<l ∧ ClassTestUpper Q x U l ∧ ∃α∈U,∃c,¬ClassTestExact Q α l c x := by
  let n:=Nat.find hex
  have hn:ClassTestUpper Q x U (t+n):=Nat.find_spec hex
  have hpos:0<n:=by
    by_contra hh
    have :n=0:=by omega
    apply hnot
    simpa only [this,Int.natCast_zero,add_zero] using hn
  have hprev:¬ClassTestUpper Q x U (t+n-1):=by
    intro hh
    have he:t+((n-1:ℕ):ℤ)=t+n-1:=by omega
    have :=Nat.find_min hex (show n-1<n by omega)
    exact this (by rw [he]; exact hh)
  refine ⟨t+n,by omega,hn,?_⟩
  by_contra hh
  apply hprev
  intro α hα l hl c
  by_cases he:l=t+n
  · subst l
    by_contra hc
    exact hh ⟨α,hα,c,hc⟩
  · exact hn α hα l (by omega) c

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ScalarExactNotZero
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma scalarExact_not_of_zero_differential {I:Type u} [Fintype I]
    (E:BasedComplex Q (K:=K) I) (α:V) (hd:E.differential=0) (i:I) :
    ¬ScalarExactAt Q E α (E.placement i).level (E.placement i).cochain := by
  intro h
  have hdm:E.differential.map (vertexHom Q α)=0 := by rw [hd]; ext a b; exact map_zero (vertexHom Q (K:=K) α)
  let x:I→K:=Pi.single i 1
  have hx:ScalarSupported Q E (E.placement i).level (E.placement i).cochain x := by
    intro j hj
    have hji:j≠i:=by rintro rfl; exact hj ⟨rfl,rfl⟩
    exact Pi.single_eq_of_ne hji _
  obtain ⟨y,_,hy⟩:=h x hx (by rw [hdm,Matrix.vecMul_zero])
  rw [hdm,Matrix.vecMul_zero] at hy
  have hh:=congrFun hy i
  simp [x] at hh

lemma initialClass_test_not_exact (α β:V) (p:Zigzag.CornerPath Q α β) :
    ¬ClassTestExact Q α (Path.length p.val) 0 (initialClass Q (K:=K) β) := by
  let E:=initialProjective Q (K:=K) β
  change ¬ScalarExactAt Q (E.testComplex Q α) α _ _
  have hd:(E.testComplex Q α).differential=0 := by
    change scalarCornerMatrix Q α (testMatrix Q E.placement E.placement α 0)=0
    rw [testMatrix_zero,scalarCornerMatrix_zero]
  simpa only [E,testComplex,testPlacement,initialProjective,GeneratorPlacement.level,
    zero_add] using scalarExact_not_of_zero_differential Q (E.testComplex Q α) α hd ⟨PUnit.unit,p⟩

lemma classPositiveTwist_initial_orthogonal {α β:V} (h:OrthogonalVertices Q α β) :
    classPositiveTwist Q α (initialClass Q (K:=K) β)=initialClass Q β := by
  let E:=initialProjective Q (K:=K) β
  let :IsEmpty (TestIndex Q E.placement α):=⟨fun i=>by
    rcases i with ⟨i,⟨p,hs,ht⟩⟩
    change Path.source Q p=α at hs
    change Path.target Q p=β at ht
    rcases p with a|a|a
    · exact h.1 (hs.symm.trans ht)
    · exact h.2 a hs ht
    · exact h.1 (hs.symm.trans ht)⟩
  change classOfComplex Q (E.positiveTwist Q α)=classOfComplex Q E
  rw [classOfComplex_reindex Q _ (Equiv.emptySum (TestIndex Q E.placement α) PUnit).symm]
  congr 1

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ScalarKernel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def ScalarKernel {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (f:Map Q E F) (x:I→K) : Prop := ∀ j β,∑ i,x i*(f.matrix i j).vertex β=0

def PlacementSupported (E:BasedComplex Q (K:=K) I) (α:V) (c:ℤ) (x:I→K) : Prop :=
  ∀ i,(E.placement i).color≠α ∨ (E.placement i).cochain≠c→x i=0

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma differential_arrow_right_support (E:BasedComplex Q (K:=K) I) (i j:I) (a:A)
    (h:(E.placement j).color≠Q.target a) : (E.differential i j).arrow a=0 := by
  have hh:=congrArg (fun z:Q.Zigzag K=>z.arrow a) (E.entries.2 i j)
  simpa only [arrow_mul,Pi.add_apply,leftScale,rightScale,arrow_vertexId,Pi.zero_apply,
    MulZeroClass.mul_zero,zero_add,vertexId_eval,ite_eq_right h.symm,MulZeroClass.mul_zero] using hh.symm

noncomputable def coefficientOutgoing (E:BasedComplex Q (K:=K) I) (x:I→K) (a:A) : I→K :=
  fun j=>∑ i,x i*(E.differential i j).arrow a

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma coefficientOutgoing_support (E:BasedComplex Q (K:=K) I) (α:V) (c:ℤ)
    {x:I→K} (hx:PlacementSupported Q E α c x) (a:A) :
    PlacementSupported Q E (Q.target a) (c+1) (coefficientOutgoing Q E x a) := by
  intro j hj
  apply Finset.sum_eq_zero
  intro i _
  rcases hj with hj|hj
  · rw [differential_arrow_right_support Q E i j a hj,MulZeroClass.mul_zero]
  · by_cases hi:(E.placement i).cochain=c
    · rw [(E.degree i j).1 (by omega)]
      exact MulZeroClass.mul_zero _
    · rw [hx i (Or.inr hi),MulZeroClass.zero_mul]

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma ScalarKernel.outgoing {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    {f:Map Q E F} (hf:CoefficientMatrix Q f.matrix) {x:I→K} (hx:ScalarKernel Q f x)
    (a:A) : ScalarKernel Q f (coefficientOutgoing Q E x a) := by
  intro j β
  by_cases hb:β=(F.placement j).color
  · subst β
    by_cases hja:(F.placement j).color=Q.target a
    · rw [hja]
      have hh (i:I) := congrArg (fun M:Matrix I J (Q.Zigzag K)=>(M i j).arrow a) f.commute
      simp only [Matrix.mul_apply,arrow_sum,Finset.sum_apply,arrow_mul,Pi.add_apply,
        leftScale,rightScale,(hf _ _).1,Pi.zero_apply,MulZeroClass.mul_zero,
        MulZeroClass.zero_mul,zero_add,add_zero] at hh
      change ∑ k,(∑ i,x i*(E.differential i k).arrow a)*(f.matrix k j).vertex (Q.target a)=0
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp_rw [_root_.mul_assoc,← Finset.mul_sum,hh,Finset.mul_sum,← _root_.mul_assoc]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul]
      apply Finset.sum_eq_zero
      intro k _
      rw [hx k (Q.source a),MulZeroClass.zero_mul]
    · apply Finset.sum_eq_zero
      intro i _
      by_cases hc:(E.placement i).color=Q.target a
      · have he:(f.matrix i j).vertex (F.placement j).color=0 := by
          by_contra he
          have hs:=reduction_support Q f.entries f.degree i j _ he
          exact hja (hs.1 ▸ hc)
        rw [he,MulZeroClass.mul_zero]
      · have hz:coefficientOutgoing Q E x a i=0 := by
          apply Finset.sum_eq_zero
          intro k _
          rw [differential_arrow_right_support Q E k i a hc,MulZeroClass.mul_zero]
        rw [hz,MulZeroClass.zero_mul]
  · apply Finset.sum_eq_zero
    intro i _
    rw [entry_vertex_right_support Q f.entries i j β hb,MulZeroClass.mul_zero]

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma ScalarKernel.project {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    {f:Map Q E F} {x:I→K} (hx:ScalarKernel Q f x) (p:GeneratorPlacement V) :
    ScalarKernel Q f (fun i=>if E.placement i=p then x i else 0) := by
  intro j β
  by_cases hj:F.placement j=p
  · convert hx j β using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro i _
    dsimp only
    by_cases hi:E.placement i=p
    · rw [ite_eq_left hi]
    · rw [ite_eq_right hi,MulZeroClass.zero_mul]
      have hz:(f.matrix i j).vertex β=0 := by
        by_contra hz
        exact hi ((reduction_support Q f.entries f.degree i j β hz).1.trans hj)
      rw [hz,MulZeroClass.mul_zero]
  · apply Finset.sum_eq_zero
    intro i _
    dsimp only
    by_cases hi:E.placement i=p
    · rw [ite_eq_left hi]
      have hz:(f.matrix i j).vertex β=0 := by
        by_contra hz
        exact hj ((reduction_support Q f.entries f.degree i j β hz).1.symm.trans hi)
      rw [hz,MulZeroClass.mul_zero]
    · rw [ite_eq_right hi,MulZeroClass.zero_mul]

noncomputable def Map.scalarMatrix {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (f:Map Q E F) : Matrix I J K := fun i j=>(f.matrix i j).vertex (F.placement j).color

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma map_vertex_source_eq_target {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (f:Map Q E F) (i:I) (j:J) :
    (f.matrix i j).vertex (E.placement i).color=f.scalarMatrix Q i j := by
  by_cases h:(E.placement i).color=(F.placement j).color
  · exact congrArg _ h
  · rw [entry_vertex_right_support Q f.entries i j _ h]
    exact (entry_vertex_left_support Q f.entries i j _ (Ne.symm h)).symm

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma map_coefficient_entry {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (f:Map Q E F) (hf:CoefficientMatrix Q f.matrix) (i:I) (j:J) :
    f.matrix i j=f.scalarMatrix Q i j •vertexId Q (E.placement i).color := by
  apply ext
  · funext β
    simp only [vertex_smul,Pi.smul_apply,smul_eq_mul,vertexId_eval]
    by_cases hb:β=(E.placement i).color
    · subst β
      rw [ite_eq_left rfl,_root_.mul_one]
      exact map_vertex_source_eq_target Q f i j
    · rw [ite_eq_right hb,MulZeroClass.mul_zero]
      exact entry_vertex_left_support Q f.entries i j _ hb
  · simpa only [arrow_smul,arrow_vertexId,smul_zero] using (hf i j).1
  · simpa only [token_smul,token_vertexId,smul_zero] using (hf i j).2

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma scalarKernel_of_vecMul_zero {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (f:Map Q E F) {x:I→K} (hx:Matrix.vecMul x (f.scalarMatrix Q)=0) : ScalarKernel Q f x := by
  intro j β
  by_cases hb:β=(F.placement j).color
  · subst β
    exact congrFun hx j
  · apply Finset.sum_eq_zero
    intro i _
    rw [entry_vertex_right_support Q f.entries i j _ hb,MulZeroClass.mul_zero]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositiveLiftSimple
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.positiveToArtin_generator _root_.OAI.HarmonicArtin.positiveToArtin_word _root_.OAI.HarmonicArtin.restrictedArtinHom_generator
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

lemma positiveLift_longest_conjugate (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
    (s t:S) (hst:z*M.toCoxeterSystem.simple s*z=M.toCoxeterSystem.simple t) :
    positiveLift M z*generator M s=generator M t*positiveLift M z := by
  have hzz:=longest_mul_self cs z hz
  have hst':M.toCoxeterSystem.simple t*z=z*M.toCoxeterSystem.simple s := by rw [← hst,mul_assoc,mul_assoc,hzz,mul_one]
  have hr:=all_descents_of_longest cs z hz s
  have hl:=all_left_descents_of_longest cs z hz t
  have hp:positiveLift M z=positiveLift M (z*M.toCoxeterSystem.simple s)*generator M s := by
    have h:=positiveLift_mul M (z*M.toCoxeterSystem.simple s) (M.toCoxeterSystem.simple s) (by
      rw [mul_assoc,M.toCoxeterSystem.simple_mul_simple_self,mul_one,M.toCoxeterSystem.length_simple]; omega)
    simpa only [mul_assoc,M.toCoxeterSystem.simple_mul_simple_self,mul_one,positiveLift_simple] using h
  have hq:positiveLift M z=generator M t*positiveLift M (M.toCoxeterSystem.simple t*z) := by
    have h:=positiveLift_mul M (M.toCoxeterSystem.simple t) (M.toCoxeterSystem.simple t*z) (by
      rw [← mul_assoc,M.toCoxeterSystem.simple_mul_simple_self,one_mul,M.toCoxeterSystem.length_simple]; omega)
    simpa only [← mul_assoc,M.toCoxeterSystem.simple_mul_simple_self,one_mul,positiveLift_simple] using h
  calc
    positiveLift M z*generator M s=(generator M t*positiveLift M (z*M.toCoxeterSystem.simple s))*generator M s := by rw [hq,hst']
    _ = generator M t*positiveLift M z := by rw [mul_assoc,← hp]

lemma positiveLift_longest_square_commute_generator (z:M.Group)
    (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z) (s:S) :
    Commute (positiveLift M z^2) (generator M s) := by
  obtain ⟨t,hst⟩:=longest_conjugates_simple cs z hz s
  have hts:z*M.toCoxeterSystem.simple t*z=M.toCoxeterSystem.simple s := by
    rw [← hst]
    have hzz:=longest_mul_self cs z hz
    calc z*(z*M.toCoxeterSystem.simple s*z)*z = (z*z)*M.toCoxeterSystem.simple s*(z*z) := by group
         _ = M.toCoxeterSystem.simple s := by rw [hzz,one_mul,mul_one]
  have h₁:=positiveLift_longest_conjugate M z hz s t hst
  have h₂:=positiveLift_longest_conjugate M z hz t s hts
  show positiveLift M z^2 * generator M s=generator M s*positiveLift M z^2
  rw [pow_two,mul_assoc,h₁,← mul_assoc,h₂,mul_assoc]

lemma positiveLift_longest_square_central (z:M.Group)
    (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z) (g:Artin M) :
    Commute (positiveLift M z^2) g := by
  have hg:g∈Subgroup.closure (Set.range (generator M)) := by
    have hh : Subgroup.closure (Set.range (generator M))=⊤ := PresentedGroup.closure_range_of (braidRelators M)
    rw [hh]; trivial
  induction hg using Subgroup.closure_induction with
  | mem x hx => obtain ⟨s,rfl⟩:=hx; exact positiveLift_longest_square_commute_generator M z hz s
  | one => exact Commute.one_right _
  | mul a b ha hb ia ib => exact ia.mul_right ib
  | inv a ha ia => exact ia.inv_right

lemma positive_fraction_longest (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
    (g:Artin M) : ∃ n:ℕ,∃ u:List S,g=wordArtin M u*(positiveLift M z^2)^(- (n:ℤ)) := by
  let Ω:Artin M:=positiveLift M z^2
  have hg:g∈Subgroup.closure (Set.range (generator M)) := by
    have hh:Subgroup.closure (Set.range (generator M))=⊤:=PresentedGroup.closure_range_of (braidRelators M)
    rw [hh]; trivial
  change ∃ n:ℕ,∃ u:List S,g=wordArtin M u*Ω^(- (n:ℤ))
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨0,[],by simp [wordArtin]⟩
  | mul_left a ha y hy ih =>
    obtain ⟨s,rfl⟩:=ha
    obtain ⟨n,u,rfl⟩:=ih
    exact ⟨n,s::u,by simp only [wordArtin,List.map_cons,List.prod_cons,mul_assoc]⟩
  | inv_mul_cancel a ha y hy ih =>
    obtain ⟨s,rfl⟩:=ha
    obtain ⟨n,u,rfl⟩:=ih
    obtain ⟨v,hv⟩:=positiveLift_longest_square_complement M z hz s
    have hinv:(generator M s)⁻¹=wordArtin M v*Ω⁻¹ := by
      apply (mul_left_cancel_iff (a:=generator M s)).mp
      rw [← mul_assoc,hv,mul_inv_cancel, mul_inv_cancel]
    refine ⟨n+1,v++u,?_⟩
    rw [hinv,wordArtin_append]
    have hp:Commute Ω⁻¹ (wordArtin M u):=(positiveLift_longest_square_central M z hz _).inv_left
    calc
      wordArtin M v*Ω⁻¹*(wordArtin M u*Ω^(-(n:ℤ))) =
          wordArtin M v*(Ω⁻¹*wordArtin M u)*Ω^(-(n:ℤ)) := by group
      _ = (wordArtin M v*wordArtin M u)*(Ω⁻¹*Ω^(-(n:ℤ))) := by rw [hp.eq]; group
      _ = (wordArtin M v*wordArtin M u)*Ω^(-((n+1:ℕ):ℤ)) := by
        congr 1
        rw [← zpow_neg_one,← zpow_add]
        congr 1
        omega

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FiniteArtinPositiveLeft
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

theorem finiteArtin_positive_left_fraction [Finite M.Group] (g:Artin M) :
    ∃ u v:List S,g=(wordArtin M u)⁻¹*wordArtin M v := by
  obtain ⟨z,hz⟩:=exists_longest M.toCoxeterSystem
  obtain ⟨n,u,hu⟩:=positive_fraction_longest M z hz g
  obtain ⟨v,hv⟩:=positiveLift_longest_square_positive M z
  obtain ⟨v',hv'⟩:=wordArtin_positive_power M v n
  refine ⟨v',u,?_⟩
  rw [hu,hv',hv,zpow_neg,zpow_natCast]
  exact ((positiveLift_longest_square_central M z hz (wordArtin M u)).pow_left n).inv_left.eq.symm

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Candidate
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Coset
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.liftedPartialOrder
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
lemma rightCoset_eq_of_mem (T:Set S) (x y:Artin M) (hy:y∈rightCoset M T x) :
    rightCoset M T y=rightCoset M T x := by
  have h:=rightCoset_mul_eq M T (y*x⁻¹) x hy
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using h

omit [Fintype S] [LinearOrder S] in
lemma sourceCosetRepresentative_mem (P:Deligne M) : sourceCosetRepresentative M P∈P.val.2 := by
  rw [sourceCosetRepresentative_spec]
  exact rightCoset_self M _ _

omit [Fintype S] [LinearOrder S] in
lemma sourceCoset_eq (P:Deligne M) (x:Artin M) (hx:x∈P.val.2) :
    sourceCoset M P.val.1 P.property.1 x=P := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change rightCoset M P.val.1 x=P.val.2
    rw [sourceCosetRepresentative_spec] at hx ⊢
    exact rightCoset_eq_of_mem M _ _ _ hx

omit [Fintype S] [LinearOrder S] in
lemma deligne_eq_of_le_type_eq {P R:Deligne M} (h:P≤R) (ht:P.val.1=R.val.1) : P=R := by
  let x:=sourceCosetRepresentative M P
  have hx:=sourceCosetRepresentative_mem M P
  have hr:=sourceCoset_eq M R x (h.2 hx)
  have hp:=sourceCoset_eq M P x hx
  rw [←hr,←hp]
  apply Subtype.ext
  simp only [sourceCoset,ht]

omit [Fintype S] [LinearOrder S] in
lemma deligne_lt_type {P R:Deligne M} (h:P<R) : P.val.1⊂R.val.1 := by
  exact lt_of_le_of_ne h.le.1 (fun he=>h.ne (deligne_eq_of_le_type_eq M h.le he))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightMap
attribute [-instance] _root_.OAI.HarmonicArtin.finiteLinearWeightsCompact _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.instT2SpaceOrderWeights
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

noncomputable def weightMapContinuous (f:P→oQ) : C(OrderWeights P,OrderWeights Q) :=
  ⟨weightMap f,weightMap_continuous f⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightLinearLinkInverse
attribute [-instance] _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightAttach
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightVertexRetract
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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

lemma weightVertexRetract_old (w:OrderWeights (WeightOld v)) :
    weightVertexRetract v c H (weightOldMap v w)=w := by
  change coneAttachmentRetract _ c H ((weightAttachEquiv v c).symm (weightOldMap v w))=w
  rw [weightAttachEquiv_symm_old]
  rfl

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_InsertOldIso
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightMapCover
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_UnionCarrier
attribute [-instance] _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
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

variable (C:Set (WeightContractionPiece r c)) (hc:IsChain Extends C) (hne:C.Nonempty)

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Initial
attribute [-instance] _root_.OAI.HarmonicArtin.liftedPartialOrder
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

variable (wf:WellFounded r) (htotal:∀x y,x≠y → r x y ∨ r y x)

variable (a:WeightContractionPiece r c) (v:P) (hv:v∉a.carrier)
  (heA:∀x,x∈a.carrier↔r x v)
  (hlink:ContractibleSpace (OrderWeights (WeightEarlierLink r v)))

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ArtinReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
universe u v
variable {S:Type u} {T:Type v} (M:CoxeterMatrix S) (e:S≃T)

lemma braidRelators_reindex :
    FreeGroup.freeGroupCongr e '' braidRelators M=braidRelators (M.reindex e) := by
  ext z
  constructor
  · rintro ⟨r,⟨⟨s,t⟩,rfl⟩,rfl⟩
    refine ⟨(e s,e t),?_⟩
    simp only [CoxeterMatrix.reindex_apply,e.symm_apply_apply,map_mul,map_inv,alternating_reindex]
  · rintro ⟨⟨s,t⟩,rfl⟩
    refine ⟨alternating (e.symm s) (e.symm t) (M (e.symm s) (e.symm t))*
      (alternating (e.symm t) (e.symm s) (M (e.symm s) (e.symm t)))⁻¹,
      ⟨(e.symm s,e.symm t),rfl⟩,?_⟩
    simp only [CoxeterMatrix.reindex_apply,map_mul,map_inv,alternating_reindex,e.apply_symm_apply]

noncomputable def artinReindex : Artin M≃*Artin (M.reindex e) :=
  QuotientGroup.congr (Subgroup.normalClosure (braidRelators M))
    (Subgroup.normalClosure (braidRelators (M.reindex e))) (FreeGroup.freeGroupCongr e)
    (by
      rw [← braidRelators_reindex M e]
      exact Subgroup.map_normalClosure _ _ (FreeGroup.freeGroupCongr e).surjective)

lemma artinReindex_generator (s:S) : artinReindex M e (generator M s)=generator (M.reindex e) (e s) :=rfl

lemma artinParabolic_reindex (A:Set S) :
    (artinParabolic M A).map (artinReindex M e).toMonoidHom=artinParabolic (M.reindex e) (e '' A) := by
  rw [artinParabolic,artinParabolic,MonoidHom.map_closure,Set.image_image,Set.image_image]
  congr 1

lemma spherical_reindex (A:Set S) : IsSpherical (M.reindex e) (e '' A) ↔ IsSpherical M A := by
  let f:coxeterParabolic M A≃*coxeterParabolic (M.reindex e) (e '' A):=
    ((M.reindexGroupEquiv e).symm.subgroupMap (coxeterParabolic M A)).trans
      (MulEquiv.subgroupCongr (coxeterParabolic_reindex M e A))
  constructor
  · intro h
    let :Finite (coxeterParabolic (M.reindex e) (e '' A)):=h
    exact Finite.of_equiv _ f.toEquiv.symm
  · intro h
    let :Finite (coxeterParabolic M A):=h
    exact Finite.of_equiv _ f.toEquiv

lemma artinParabolic_reindex_mem (A:Set S) (x:Artin M) :
    artinReindex M e x∈artinParabolic (M.reindex e) (e '' A) ↔ x∈artinParabolic M A := by
  rw [← artinParabolic_reindex]
  exact Subgroup.mem_map_iff_mem (artinReindex M e).injective

lemma rightCoset_reindex (A:Set S) (x:Artin M) :
    artinReindex M e '' rightCoset M A x=rightCoset (M.reindex e) (e '' A) (artinReindex M e x) := by
  ext y
  obtain ⟨z,rfl⟩:=(artinReindex M e).surjective y
  have he:(artinReindex M e z∈artinReindex M e '' rightCoset M A x) ↔ z∈rightCoset M A x:=by
    constructor
    · rintro ⟨a,ha,he⟩
      exact (artinReindex M e).injective he ▸ ha
    · intro h
      exact ⟨z,h,rfl⟩
  rw [he]
  change (z*x⁻¹∈artinParabolic M A) ↔ _
  rw [rightCoset,Set.mem_ofPred_eq,← map_inv,← map_mul,artinParabolic_reindex_mem]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_CellDeligne
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderLiftedPuncturedBoundary _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe v
variable {S : Type v}

lemma cellToDeligne_monotone (M : CoxeterMatrix S) : Monotone (cellToDeligne M) := by
  intro a b hab
  obtain ⟨hAB,u,hu,hur,humin,ha⟩ := (lifted_le_iff_face M a b).mp hab
  change a.2.1 ⊆ b.2.1 ∧ rightCoset M a.2.1 a.1⁻¹ ⊆ rightCoset M b.2.1 b.1⁻¹
  refine ⟨hAB,?_⟩
  intro g hg
  change g*(a.1⁻¹)⁻¹ ∈ artinParabolic M a.2.1 at hg
  change g*(b.1⁻¹)⁻¹ ∈ artinParabolic M b.2.1
  simp only [inv_inv] at hg ⊢
  have hmem := artinParabolic_mono M hAB hg
  have huA := wordArtin_mem_parabolic M b.2.1 u hu
  have hprod := (artinParabolic M b.2.1).mul_mem hmem ((artinParabolic M b.2.1).inv_mem huA)
  simpa only [ha,mul_assoc,mul_inv_cancel,mul_one] using hprod

def cellToDeligneOrderHom (M : CoxeterMatrix S) : LiftedCell M →o Deligne M :=
  ⟨cellToDeligne M,cellToDeligne_monotone M⟩

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

lemma positivePrefix_of_simple_eq {a b:PositiveArtin M} {w:M.Group}
    (h:PositivePrefix M a b) (hb:b=positiveSimpleLift M w) :
    a=positiveSimpleLift M (positiveToCoxeter M a) := by
  obtain ⟨c,hc⟩:=h
  exact (positive_simple_factors M a c w (hc.symm.trans hb)).1

theorem exists_greatest_common_simplePrefix (u v:M.Group) :
    ∃g:M.Group,PositivePrefix M (positiveSimpleLift M g) (positiveSimpleLift M u) ∧
      PositivePrefix M (positiveSimpleLift M g) (positiveSimpleLift M v) ∧
      ∀a:PositiveArtin M,PositivePrefix M a (positiveSimpleLift M u)→
        PositivePrefix M a (positiveSimpleLift M v)→PositivePrefix M a (positiveSimpleLift M g) := by
  obtain ⟨g,hgu,hgv,hgreat⟩:=exists_greatest_common_weakPrefix M.toCoxeterSystem u v
  refine ⟨g,(positivePrefix_simple_iff M g u).mpr hgu,(positivePrefix_simple_iff M g v).mpr hgv,?_⟩
  intro a hau hav
  have he:=positivePrefix_of_simple_eq M hau rfl
  rw [he] at hau hav ⊢
  exact (positivePrefix_simple_iff M _ _).mpr (hgreat _
    ((positivePrefix_simple_iff M _ _).mp hau) ((positivePrefix_simple_iff M _ _).mp hav))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_RestrictionHomRange
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

theorem exists_longest_descent_factor (J:Set S) (w:M.Group)
    (hJ:∀s∈J,M.toCoxeterSystem.length (M.toCoxeterSystem.simple s*w)<M.toCoxeterSystem.length w) :
    ∃q:(restrictedMatrix M J).Group,∃v:M.Group,
      (∀r:(restrictedMatrix M J).Group,(restrictedMatrix M J).toCoxeterSystem.length r≤
        (restrictedMatrix M J).toCoxeterSystem.length q) ∧
      IsParabolicMinimum M.toCoxeterSystem J v ∧
      w=restrictionHom M J q*v ∧
      M.toCoxeterSystem.length w=(restrictedMatrix M J).toCoxeterSystem.length q+
        M.toCoxeterSystem.length v := by
  obtain ⟨a,v,ha,hv,he,hl⟩:=exists_parabolic_decomposition M.toCoxeterSystem J w
  have hmem:a∈(restrictionHom M J).range:=by
    rw [restrictionHom_range_eq]
    exact ha
  obtain ⟨q,hq⟩:=hmem
  have hd:∀s:J,(restrictedMatrix M J).toCoxeterSystem.length
      ((restrictedMatrix M J).toCoxeterSystem.simple s*q)<
      (restrictedMatrix M J).toCoxeterSystem.length q:=by
    intro s
    have hh: M.toCoxeterSystem.length (M.toCoxeterSystem.simple s*a)<M.toCoxeterSystem.length a:=
      (descent_parabolic_factor M.toCoxeterSystem J ha hv s.property).mp (by rw [←he];exact hJ s s.property)
    rw [←hq,←restrictionHom_simple M J s,←map_mul,restriction_length,restriction_length] at hh
    exact hh
  have hdi:∀s:J,(restrictedMatrix M J).toCoxeterSystem.length
      (q⁻¹*(restrictedMatrix M J).toCoxeterSystem.simple s)+1=
      (restrictedMatrix M J).toCoxeterSystem.length q⁻¹:=by
    intro s
    have hi:((restrictedMatrix M J).toCoxeterSystem.simple s*q)⁻¹=q⁻¹*(restrictedMatrix M J).toCoxeterSystem.simple s:=by
      rw [mul_inv_rev,(restrictedMatrix M J).toCoxeterSystem.inv_simple]
    have hh:=hd s
    have hp:=(restrictedMatrix M J).toCoxeterSystem.length_simple_mul q s
    rcases hp with hp|hp
    · omega
    · simpa only [←hi,CoxeterSystem.length_inv] using hp
  refine ⟨q,v,?_,hv,by rw [hq];exact he,?_⟩
  · intro r
    simpa only [CoxeterSystem.length_inv] using
      length_le_of_all_descents (restrictedMatrix M J).toCoxeterSystem q⁻¹ hdi r
  · simpa only [←hq,restriction_length] using hl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_SphericalLongest
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderLiftedPuncturedBoundary
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

noncomputable def cellWithTop (b:Artin M) (T:SphericalType M) : LiftedCell M :=
  (b*(positiveLift M (sphericalLongest M T))⁻¹,T)

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

lemma firstPositiveDescent_mem : firstPositiveDescent M z hz b hb∈PositiveDescentSet M b := by
  exact Set.mem_toFinset.mp (Finset.min'_mem _ _)

lemma firstPositiveDescent_le {s:S} (hs:s∈PositiveDescentSet M b) :
    firstPositiveDescent M z hz b hb ≤ s :=
  Finset.min'_le _ _ (Set.mem_toFinset.mpr hs)

end FirstDescent
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_FiniteWeightsCompact
attribute [-instance] _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open Topology
open scoped unitInterval

attribute [local instance] Classical.decEq Classical.propDecidable
universe u v
variable {P : Type u} [PartialOrder P]

noncomputable instance finiteWeightsCompact [Finite P] : CompactSpace (OrderWeights P) := by
  let _ := Fintype.ofFinite P
  let C := {c : Finset P // IsChain (· ≤ ·) (↑c : Set P) ∧ c.Nonempty}
  let f := fun c : C => orderWeightsOfChain (finiteChainOrder c.val c.property.1 c.property.2)
  have cover : (Set.univ : Set (OrderWeights P)) = ⋃ c : C, Set.range (f c) := by
    apply Set.Subset.antisymm
    · intro w _
      let c : C := ⟨w.weights.support, (fun p hp q hq _ => w.chain p hp q hq),w.support_nonempty⟩
      apply Set.mem_iUnion.mpr
      refine ⟨c,carrierSimplex c.val c.property.1 c.property.2 w (Finset.Subset.refl _),?_⟩
      exact carrierSimplex_reconstruct c.val c.property.1 c.property.2 w _
    · exact Set.subset_univ _
  apply isCompact_univ_iff.mp
  rw [cover]
  exact isCompact_iUnion fun c => isCompact_range (chainWeightsChart_continuous _)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_FullSphericalCell
attribute [-instance] _root_.OAI.HarmonicArtin.instPartialOrderLiftedPuncturedBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] (M : CoxeterMatrix S)

noncomputable def fullSphericalCell [Finite M.Group] : LiftedCell M :=
  (1,⟨Set.univ,show Finite (coxeterParabolic M Set.univ) from inferInstance⟩)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightRetractionPiece
attribute [-instance] _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P] (r:P→P→Prop) (A:Set P)

structure WeightRetractionPiece where
  carrier:Set P
  base:A⊆carrier
  down:∀{x y},x∈carrier → r y x → y∈carrier
  map:C(OrderWeights carrier,OrderWeights A)
  retract:∀w:OrderWeights A,map (weightMap (weightSubset A carrier base) w)=w

namespace WeightRetractionPiece
variable {r A}

def Extends (a b:WeightRetractionPiece r A) : Prop :=
  ∃h:a.carrier⊆b.carrier,∀w:OrderWeights a.carrier,
    b.map (weightMap (weightSubset _ _ h) w)=a.map w

lemma extends_refl (a:WeightRetractionPiece r A) : a.Extends a := by
  refine ⟨Set.Subset.rfl,?_⟩
  intro w
  rw [weightSubset_self,weightMap_id]

instance instReflExtends : Std.Refl (@Extends P _ r A):=⟨extends_refl⟩

lemma extends_compare {a b:WeightRetractionPiece r A} (h:a.Extends b)
    (w:OrderWeights a.carrier) (z:OrderWeights b.carrier)
    (he:weightMap (weightInclusion a.carrier) w=weightMap (weightInclusion b.carrier) z) :
    a.map w=b.map z := by
  obtain ⟨h,hh⟩:=h
  have hz:weightMap (weightSubset _ _ h) w=z:=by
    apply weightMap_injective (weightInclusion b.carrier) Subtype.val_injective
    rw [weightMap_comp]
    exact he
  rw [←hh,hz]

variable (C:Set (WeightRetractionPiece r A)) (hc:IsChain Extends C) (hne:C.Nonempty)

def unionCarrier : Set P :={x | ∃a∈C,x∈a.carrier}
lemma subset_union {a:WeightRetractionPiece r A} (ha:a∈C) : a.carrier⊆unionCarrier C :=
  fun _ hx=>⟨a,ha,hx⟩

include hc hne in
lemma union_finset_cover (s:Finset P) (hs:∀x∈s,x∈unionCarrier C) :
    ∃a∈C,∀x∈s,x∈a.carrier := by
  induction s using Finset.induction_on with
  | empty=>obtain ⟨a,ha⟩:=hne;exact ⟨a,ha,by simp⟩
  | @insert x s hx ih=>
    obtain ⟨a,ha,hac⟩:=ih (fun y hy=>hs y (Finset.mem_insert_of_mem hy))
    obtain ⟨b,hb,hxb⟩:=hs x (Finset.mem_insert_self x s)
    rcases hc.total ha hb with hab|hba
    · refine ⟨b,hb,?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl|hy
      · exact hxb
      · exact hab.choose (hac y hy)
    · refine ⟨a,ha,?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl|hy
      · exact hba.choose hxb
      · exact hac y hy

noncomputable def unionIncl (a:C) : a.val.carrier→o unionCarrier C :=
  weightSubset _ _ (subset_union C a.property)

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

noncomputable def unionLocal (a:C) : C(Unit×OrderWeights a.val.carrier,OrderWeights A) :=
  a.val.map.comp ContinuousMap.snd

include hc in
lemma union_compatible : WeightMapCompatible (unionIncl C) (unionLocal C) := by
  intro a b w z he t
  have hW:weightMap (weightInclusion a.val.carrier) w=weightMap (weightInclusion b.val.carrier) z:=by
    have hh:=congrArg (weightMap (weightInclusion (unionCarrier C))) he
    rw [weightMap_comp,weightMap_comp] at hh
    exact hh
  rcases hc.total a.property b.property with hab|hba
  · exact extends_compare hab w z hW
  · exact (extends_compare hba z w hW.symm).symm

noncomputable def unionMap : C(OrderWeights (unionCarrier C),OrderWeights A) :=
  (weightMapGlue (unionIncl C) (unionLocal C) (union_map_cover C hc hne) (union_compatible C hc)).comp
    ⟨fun w=>((),w),continuous_const.prodMk continuous_id⟩

lemma unionMap_on (a:C) (w:OrderWeights a.val.carrier) :
    unionMap C hc hne (weightMap (unionIncl C a) w)=a.val.map w :=
  weightMapGlueValue_on (unionIncl C) (unionLocal C) (union_map_cover C hc hne) (union_compatible C hc) a ((),w)

noncomputable def union : WeightRetractionPiece r A where
  carrier:=unionCarrier C
  base:=by
    obtain ⟨a,ha⟩:=hne
    exact fun x hx=>⟨a,ha,a.base hx⟩
  down:=by
    intro x y hx h
    obtain ⟨a,ha,hx⟩:=hx
    exact ⟨a,ha,a.down hx h⟩
  map:=unionMap C hc hne
  retract:=by
    intro w
    obtain ⟨a,ha⟩:=hne
    have he:weightSubset A (unionCarrier C) (fun x hx=>⟨a,ha,a.base hx⟩)=
        (unionIncl C ⟨a,ha⟩).comp (weightSubset A a.carrier a.base):=rfl
    rw [he,← weightMap_comp]
    exact (unionMap_on C hc (show C.Nonempty from ⟨a,ha⟩) ⟨a,ha⟩ _).trans (a.retract w)

end WeightRetractionPiece
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Realizations_WeightInsertRetract
attribute [-instance] _root_.OAI.HarmonicArtin.finiteWeightsCompact _root_.OAI.HarmonicArtin.instPreorderLiftedCell _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

noncomputable def weightInsertRetract (A:Set P) (v:P) (hv:v∉A)
    (hc:ContractibleSpace (OrderWeights (WeightLink (⟨v,Set.mem_insert v A⟩:↥(insert v A))))) :
    C(OrderWeights ↥(insert v A),OrderWeights A) :=
  let c:=Classical.choose (@id_nullhomotopic _ _ hc)
  let H:=Classical.choice (Classical.choose_spec (@id_nullhomotopic _ _ hc))
  (show C(_,_) from ⟨(weightHomeomorph (insertOldIso A v hv)).symm,
    (weightHomeomorph (insertOldIso A v hv)).symm.continuous⟩).comp (weightVertexRetract _ c H)

lemma weightInsertRetract_old (A:Set P) (v:P) (hv:v∉A)
    (hc:ContractibleSpace (OrderWeights (WeightLink (⟨v,Set.mem_insert v A⟩:↥(insert v A)))))
    (w:OrderWeights A) :
    weightInsertRetract A v hv hc (weightMap (weightSubset A (insert v A) (Set.subset_insert v A)) w)=w := by
  let e:=weightHomeomorph (insertOldIso A v hv)
  have he:weightMap (weightSubset A (insert v A) (Set.subset_insert v A)) w=
      weightOldMap (⟨v,Set.mem_insert v A⟩:↥(insert v A)) (e w):=by
    change _=weightMap (weightOldIncl _) (weightMap (OrderHomClass.toOrderHom (insertOldIso A v hv)) w)
    rw [weightMap_comp,insertOldIso_incl]
  rw [he]
  change e.symm (weightVertexRetract _ _ _ (weightOldMap _ (e w)))=w
  rw [weightVertexRetract_old,e.symm_apply_apply]

namespace WeightRetractionPiece
variable {r:P→P→Prop} {A:Set P}

noncomputable def initial (hA:∀{x y},x∈A → r y x → y∈A) : WeightRetractionPiece r A where
  carrier:=A
  base:=Set.Subset.rfl
  down:=hA
  map:=ContinuousMap.id _
  retract:=by intro w; rw [weightSubset_self,weightMap_id];rfl

variable (wf:WellFounded r) (htotal:∀x y,x≠y → r x y ∨ r y x)

variable (a:WeightRetractionPiece r A) (v:P) (hv:v∉a.carrier)
  (heA:∀x,x∈a.carrier↔r x v)
  (hlink:ContractibleSpace (OrderWeights (WeightEarlierLink r v)))

include wf heA hlink in
theorem insertLinkContractible :
    ContractibleSpace (OrderWeights (WeightLink (⟨v,Set.mem_insert v a.carrier⟩:↥(insert v a.carrier)))) :=
  (weightHomeomorph (insertLinkIso r (fun x=>wf.irrefl.irrefl x) a.carrier v heA)).contractibleSpace_iff.mpr hlink

noncomputable def successor : WeightRetractionPiece r A where
  carrier:=insert v a.carrier
  base:=a.base.trans (Set.subset_insert v a.carrier)
  down:=by
    intro x y hx hy
    rcases Set.mem_insert_iff.mp hx with hx|hx
    · subst x
      exact Set.mem_insert_of_mem v ((heA y).mpr hy)
    · exact Set.mem_insert_of_mem v (a.down hx hy)
  map:=a.map.comp (weightInsertRetract a.carrier v hv (insertLinkContractible wf a v heA hlink))
  retract:=by
    intro w
    have he:weightSubset A (insert v a.carrier) (a.base.trans (Set.subset_insert v a.carrier))=
        (weightSubset a.carrier (insert v a.carrier) (Set.subset_insert v a.carrier)).comp
          (weightSubset A a.carrier a.base):=rfl
    rw [he,← weightMap_comp]
    change a.map (weightInsertRetract _ _ _ _ (weightMap _ (weightMap _ w)))=w
    rw [weightInsertRetract_old,a.retract]

end WeightRetractionPiece

end HarmonicArtin

end OAI
end


