-- Prove2me | Definitions.Def_OAIQ236Ap006
-- name    : OAIQ236Ap006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T19:52:16.850722+00:00
-- url     : https://prove2.me/theorems/df5e2d09-5a39-4774-86db-887d0d68e6b5
-- title:
--   Definitions bundle OAIQ236Ap006 of the split of OpenAI, Parabolic intersections in Artin groups
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure` and `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections`, carved from OpenAI's openai/math development (OpenAI, *Parabolic intersections in Artin groups*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 207 declarations of OpenAI's Lean: 63 definitions, 3 inductive types or structures, 5 instances and 136 theorems. The definitions and types are `OAI.HarmonicArtin.ParabolicIntersections.arrowMatrix`, `OAI.HarmonicArtin.ParabolicIntersections.cochainInterval`, `OAI.HarmonicArtin.ParabolicIntersections.positiveMap`, `OAI.HarmonicArtin.ReversibleQuiver.Iso.testIndex`, `OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.BlockPivot`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.BlockPivot.homotopy`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.BlockPivot.inclusionMap`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.BlockPivot.reduced`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.BlockPivot.reducedDifferential`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.BlockPivot.reductionEquivalence`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.BlockPivot.reductionMap`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.BlockPivot.remainder`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.BraidCoreIndex`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.BraidTwistIndex`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ChainIsomorphism.toHomotopyEquivalence`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ChainIsomorphism.trans`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ClassLowerBound`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ClassTestExact`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ClassUpperBound`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.CommuteTwistIndex`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.HomOperator`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.HomOperator.onCohomology`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.HomOperator.onCycles`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.HomotopyEquivalence.test`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.PositiveBraidRel`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDifferential`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCorePlacement`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreSwap`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstPivot`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidRawCoreDifferential`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistIndexEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.classHomDimension`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.colorRestriction`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.commuteTwistDifferential`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.commuteTwistIndexEquiv`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.commuteTwistPlacement`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.commuteTwistSwap`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homBoundaries`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homCohomology` and 26 more.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `ArtinGroups_Cancellation_BlockPivot`, `ArtinGroups_Cancellation_ReducedDifferential`, `ArtinGroups_Cancellation_ReducedDifferential2`, `ArtinGroups_Complexes_CoefficientTopDual`, `ArtinGroups_Complexes_ColorBoundary`, `ArtinGroups_Complexes_CommuteTwistSwap`, `ArtinGroups_Complexes_CorrectionBoundary`, `ArtinGroups_Complexes_DiagonalVertex`, `ArtinGroups_Complexes_FiniteSum2`, `ArtinGroups_Complexes_HomDetector`, `ArtinGroups_Complexes_HomDimension`, `ArtinGroups_Complexes_HomDimension2`, `ArtinGroups_Complexes_HomOperator`, `ArtinGroups_Complexes_HomSpace`, `ArtinGroups_Complexes_HomSpaceMul`, `ArtinGroups_Complexes_InitialProjective`, `ArtinGroups_Complexes_InverseHomMatrix`, `ArtinGroups_Complexes_IsolatedIndexCycle`, `ArtinGroups_Complexes_LevelArrayComplexMinimal`, `ArtinGroups_Complexes_MinimalGeneratorDualCycle`, `ArtinGroups_Complexes_OptionSumEquiv`, `ArtinGroups_Complexes_PlacementSignedWeight`, `ArtinGroups_Complexes_PositiveHomTransform`, `ArtinGroups_Complexes_PositiveTwistFiberEquiv`, `ArtinGroups_Complexes_PositiveWordActionAppend`, `ArtinGroups_Complexes_PureHomSpaceHomogeneous`, `ArtinGroups_Complexes_Refl`, `ArtinGroups_Complexes_ReindexHomOperator`, `ArtinGroups_Complexes_ScalarSupported`, `ArtinGroups_Complexes_SumTestEquiv`, `ArtinGroups_Complexes_Test`, `ArtinGroups_Complexes_TestExact`, `ArtinGroups_Complexes_TotalVector`, `ArtinGroups_Complexes_UpperBound`, `ArtinGroups_Coxeter_BraidCoreFirstTarget`, `ArtinGroups_Coxeter_BraidCoreIndex`, `ArtinGroups_Coxeter_BraidCorePlacement`, `ArtinGroups_Coxeter_BraidFirstPivot`, `ArtinGroups_Coxeter_BraidSecondPivot`, `ArtinGroups_Coxeter_OrdinaryCoxeterMatrix`, `ArtinGroups_Coxeter_PositiveBraidRel`, `ArtinGroups_Functors_ComplexInitial`, `ArtinGroups_Functors_Path`, `ArtinGroups_Functors_ProbeEmbeddingMap`, `ArtinGroups_Functors_ReversibleQuiverMap`, `ArtinGroups_Functors_TestIndex`, `ArtinGroups_Harmonic_FusionQuiverSimpleEdge`, `ArtinGroups_Harmonic_PositiveLiftSimple`, `ArtinGroups_Harmonic_PositivePrefix`, `ArtinGroups_Harmonic_PositiveReverseHom`, `ArtinGroups_Harmonic_PositiveSimpleLiftMul`, `ArtinGroups_Harmonic_ReducedExpression`, `ArtinGroups_Harmonic_SimpleFrontLink`, `ArtinGroups_ParabolicIntersections_CoefficientPaths`, `ArtinGroups_ParabolicIntersections_PositiveTransport`, `ArtinGroups_Quivers_EdgeContraction`, `ArtinGroups_Quivers_OrthogonalVertices`, `ArtinGroups_Quivers_ProbeLeaf`, `ArtinGroups_Quivers_ProbeSimpleEdge`, `ArtinGroups_Quivers_SimpleEdge`, `ArtinGroups_Quivers_TestTransform`, `ArtinGroups_Quivers_TraceLinear`, `ArtinGroups_Quivers_VertexMinimal`.
--
--   **Imports.** It imports the published bundle `Def_ArtinParabolicIntersections`; the bundles `OAIQ236Ap002` and `OAIQ236Ap003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ236Ap008` and `OAIQ236Ap009`.
-- source:
--   OpenAI, Parabolic intersections in Artin groups, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Mathlib.Algebra.FreeAlgebra
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Definitions.Def_ArtinParabolicIntersections
import Definitions.Def_OAIQ236Ap002
import Definitions.Def_OAIQ236Ap003

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Cancellation_BlockPivot
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.dual_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.source_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.target_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_false _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

structure BlockPivot (E : BasedComplex Q (K := K) (J ⊕ J ⊕ I)) where
  coefficient : K
  nonzero : coefficient ≠ 0
  color : ∀ j, (E.placement (.inr (.inl j))).color = (E.placement (.inl j)).color
  cochain : ∀ j, (E.placement (.inr (.inl j))).cochain =
    (E.placement (.inl j)).cochain + 1
  internal : ∀ j, (E.placement (.inr (.inl j))).internal =
    (E.placement (.inl j)).internal
  entry : ∀ i j, E.differential (.inl i) (.inr (.inl j)) =
    coefficient • projectiveIdentity Q (fun j => E.placement (.inl j)) i j

namespace BlockPivot

variable {E : BasedComplex Q (K := K) (J ⊕ J ⊕ I)} (p : BlockPivot Q E)

noncomputable def homotopy : Matrix (J ⊕ J ⊕ I) (J ⊕ J ⊕ I) (Q.Zigzag K)
  | .inr (.inl i), .inl j =>
      p.coefficient⁻¹ • projectiveIdentity Q (fun j => E.placement (.inl j)) i j
  | _, _ => 0

omit [DecidableEq I] in
lemma homotopy_entries : ProjectiveEntries Q E.placement E.placement (p.homotopy Q) := by
  constructor
  · intro i j
    rcases i with i | i | i <;> rcases j with j | j | j
    all_goals try exact MulZeroClass.mul_zero _
    change vertexId Q (E.placement (.inr (.inl i))).color *
      (p.coefficient⁻¹ • projectiveIdentity Q (fun j => E.placement (.inl j)) i j) = _
    rw [p.color, mul_smul]
    exact congrArg (p.coefficient⁻¹ • ·)
      ((projectiveEntries_identity Q (p := fun j => E.placement (.inl j))).1 i j)
  · intro i j
    rcases i with i | i | i <;> rcases j with j | j | j
    all_goals try exact MulZeroClass.zero_mul _
    change (p.coefficient⁻¹ • projectiveIdentity Q (fun j => E.placement (.inl j)) i j) *
      vertexId Q (E.placement (.inl j)).color = _
    rw [smul_mul]
    exact congrArg (p.coefficient⁻¹ • ·)
      ((projectiveEntries_identity Q (p := fun j => E.placement (.inl j))).2 i j)

omit [DecidableEq I] in
lemma homotopy_degree : MapDegree Q E.placement E.placement (-1) 0 (p.homotopy Q) := by
  intro i j
  rcases i with i | i | i <;> rcases j with j | j | j
  all_goals try exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  by_cases hij : i = j
  · subst j
    change ( (E.placement (.inl i)).cochain ≠ (E.placement (.inr (.inl i))).cochain + -1 →
        p.coefficient⁻¹ • projectiveIdentity Q (fun j => E.placement (.inl j)) i i = 0) ∧ _
    refine ⟨fun h => (h (by rw [p.cochain]; omega)).elim, ?_⟩
    change Homogeneous Q (0 + (E.placement (.inr (.inl i))).internal -
      (E.placement (.inl i)).internal) (p.coefficient⁻¹ • projectiveIdentity Q
        (fun j => E.placement (.inl j)) i i)
    rw [p.internal]
    simp only [projectiveIdentity, Matrix.diagonal_apply, ite_true, if_true]
    simpa only [zero_add, sub_self] using homogeneous_smul Q (r := p.coefficient⁻¹)
      (hx := homogeneous_vertexId Q (K := K) (E.placement (.inl i)).color)
  · change (_ → p.coefficient⁻¹ • projectiveIdentity Q (fun j => E.placement (.inl j)) i j = 0) ∧ _
    change (_ → p.coefficient⁻¹ • projectiveIdentity Q (fun j => E.placement (.inl j)) i j = 0) ∧
      Homogeneous Q _ (p.coefficient⁻¹ • projectiveIdentity Q (fun j => E.placement (.inl j)) i j)
    rw [show projectiveIdentity Q (fun j => E.placement (.inl j)) i j = 0 by
      simp only [projectiveIdentity, Matrix.diagonal_apply, ite_eq_right hij], smul_zero]
    exact ⟨fun _ => rfl, homogeneous_zero Q _⟩

omit [DecidableEq I] in
lemma homotopy_mul {L : Type*} (M : Matrix (J ⊕ J ⊕ I) L (Q.Zigzag K))
    {q : L → GeneratorPlacement V} (hM : ProjectiveEntries Q E.placement q M)
    (i : J ⊕ J ⊕ I) (j : L) :
    (p.homotopy Q * M) i j = match i with
      | .inr (.inl k) => p.coefficient⁻¹ • M (.inl k) j
      | _ => 0 := by
  rcases i with i | i | i
  all_goals simp only [Matrix.mul_apply, Fintype.sum_sum_type, homotopy,
    MulZeroClass.zero_mul, Finset.sum_const_zero, add_zero]
  simp only [projectiveIdentity, Matrix.diagonal_apply, smul_ite, smul_zero,
    ite_mul, MulZeroClass.zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true,
    smul_mul, hM.1]

omit [DecidableEq I] in
lemma mul_homotopy {L : Type*} [Fintype L]
    (M : Matrix L (J ⊕ J ⊕ I) (Q.Zigzag K))
    {q : L → GeneratorPlacement V} (hM : ProjectiveEntries Q q E.placement M)
    (i : L) (j : J ⊕ J ⊕ I) :
    (M * p.homotopy Q) i j = match j with
      | .inl k => p.coefficient⁻¹ • M i (.inr (.inl k))
      | _ => 0 := by
  rcases j with j | j | j
  all_goals simp only [Matrix.mul_apply, Fintype.sum_sum_type, homotopy,
    MulZeroClass.mul_zero, Finset.sum_const_zero, add_zero, zero_add]
  simp only [projectiveIdentity, Matrix.diagonal_apply, smul_ite, smul_zero,
    mul_ite, MulZeroClass.mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true,
    mul_smul]
  rw [← p.color]
  exact congrArg (p.coefficient⁻¹ • ·) (hM.2 i (.inr (.inl j)))

omit [DecidableEq I] in
lemma homotopy_square : p.homotopy Q * p.homotopy Q = 0 := by
  apply Matrix.ext
  intro i j
  rw [p.homotopy_mul Q _ (p.homotopy_entries Q)]
  rcases i with i | i | i
  · rfl
  · exact smul_zero _
  · rfl

omit [DecidableEq I] in
lemma homotopy_retract : p.homotopy Q * E.differential * p.homotopy Q = p.homotopy Q := by
  apply Matrix.ext
  intro i j
  rw [p.mul_homotopy Q _ (projectiveEntries_mul Q (p.homotopy_entries Q) E.entries)]
  rcases j with j | j | j
  · change p.coefficient⁻¹ • (p.homotopy Q * E.differential) i (.inr (.inl j)) = _
    rw [p.homotopy_mul Q _ E.entries]
    rcases i with i | i | i
    · exact smul_zero _
    · dsimp only
      rw [p.entry]
      change p.coefficient⁻¹ • (p.coefficient⁻¹ • (p.coefficient • _)) = p.coefficient⁻¹ • _
      congr 1
      rw [smul_smul, inv_mul_cancel₀ p.nonzero, one_smul]
    · exact smul_zero _
  · rcases i with i | i | i <;> rfl
  · rcases i with i | i | i <;> rfl

noncomputable def remainder : Matrix (J ⊕ J ⊕ I) (J ⊕ J ⊕ I) (Q.Zigzag K) :=
  GaussianCancellation.cornerRemainder (projectiveIdentity Q E.placement)
    E.differential (p.homotopy Q)

lemma remainder_entries : ProjectiveEntries Q E.placement E.placement (p.remainder Q) := by
  unfold remainder GaussianCancellation.cornerRemainder
  simp only [sub_eq_add_neg]
  exact projectiveEntries_add Q
    (projectiveEntries_add Q (projectiveEntries_identity Q)
      (projectiveEntries_neg Q (projectiveEntries_mul Q E.entries (p.homotopy_entries Q))))
    (projectiveEntries_neg Q (projectiveEntries_mul Q (p.homotopy_entries Q) E.entries))

lemma remainder_degree : MapDegree Q E.placement E.placement 0 0 (p.remainder Q) := by
  have h₁ := mapDegree_mul Q E.degree (p.homotopy_degree Q)
  have h₂ := mapDegree_mul Q (p.homotopy_degree Q) E.degree
  norm_num at h₁ h₂
  unfold remainder GaussianCancellation.cornerRemainder
  simp only [sub_eq_add_neg]
  exact mapDegree_add Q (mapDegree_add Q (mapDegree_identity Q) (mapDegree_neg Q h₁))
    (mapDegree_neg Q h₂)

lemma remainder_commutes : p.remainder Q * E.differential = E.differential * p.remainder Q :=
  GaussianCancellation.cornerRemainder_commutes _ _ _
    (projectiveIdentity_mul Q E.entries) (mul_projectiveIdentity Q E.entries) E.square_zero

lemma remainder_square : p.remainder Q * p.remainder Q = p.remainder Q :=
  GaussianCancellation.cornerRemainder_idempotent _ _ _
    (projectiveIdentity_mul Q (projectiveEntries_identity Q))
    (projectiveIdentity_mul Q E.entries) (mul_projectiveIdentity Q E.entries)
    (projectiveIdentity_mul Q (p.homotopy_entries Q))
    (mul_projectiveIdentity Q (p.homotopy_entries Q))
    E.square_zero (p.homotopy_square Q) (p.homotopy_retract Q)

lemma remainder_source_row (i : J) (k : J ⊕ J ⊕ I) : p.remainder Q (.inl i) k = 0 := by
  change (projectiveIdentity Q E.placement) (.inl i) k -
      (E.differential * p.homotopy Q) (.inl i) k -
      (p.homotopy Q * E.differential) (.inl i) k = 0
  rw [p.homotopy_mul Q _ E.entries, sub_zero, p.mul_homotopy Q _ E.entries]
  rcases k with k | k | k
  · dsimp only
    rw [p.entry, smul_smul, inv_mul_cancel₀ p.nonzero, one_smul]
    simp only [projectiveIdentity, Matrix.diagonal_apply, Sum.inl.injEq, sub_self]
  · simp [projectiveIdentity]
  · simp [projectiveIdentity]

lemma remainder_target_column (k : J ⊕ J ⊕ I) (j : J) :
    p.remainder Q k (.inr (.inl j)) = 0 := by
  change (projectiveIdentity Q E.placement) k (.inr (.inl j)) -
      (E.differential * p.homotopy Q) k (.inr (.inl j)) -
      (p.homotopy Q * E.differential) k (.inr (.inl j)) = 0
  rw [p.mul_homotopy Q _ E.entries, sub_zero, p.homotopy_mul Q _ E.entries]
  rcases k with k | k | k
  · simp [projectiveIdentity]
  · dsimp only
    rw [p.entry, smul_smul, inv_mul_cancel₀ p.nonzero, one_smul]
    simp only [projectiveIdentity, Matrix.diagonal_apply, Sum.inr.injEq, Sum.inl.injEq]
    by_cases h : k = j
    · subst j
      simp only [ite_true, if_true, p.color, sub_self]
    · simp only [ite_eq_right h, sub_self]
  · simp [projectiveIdentity]

lemma remainder_retained (i j : I) : p.remainder Q (.inr (.inr i)) (.inr (.inr j)) =
    projectiveIdentity Q (fun k => E.placement (.inr (.inr k))) i j := by
  change (projectiveIdentity Q E.placement) (.inr (.inr i)) (.inr (.inr j)) -
      (E.differential * p.homotopy Q) (.inr (.inr i)) (.inr (.inr j)) -
      (p.homotopy Q * E.differential) (.inr (.inr i)) (.inr (.inr j)) = _
  rw [p.mul_homotopy Q _ E.entries, p.homotopy_mul Q _ E.entries]
  by_cases hij : i = j
  · subst j
    simp [projectiveIdentity]
  · simp [projectiveIdentity, hij]

end BlockPivot
end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Cancellation_ReducedDifferential
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.BlockPivot

variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]
  {E : BasedComplex Q (K := K) (J ⊕ J ⊕ I)} (p : BlockPivot Q E)

noncomputable def reducedDifferential : Matrix (J ⊕ J ⊕ I) (J ⊕ J ⊕ I) (Q.Zigzag K) :=
  p.remainder Q * E.differential

lemma reducedDifferential_entries :
    ProjectiveEntries Q E.placement E.placement (p.reducedDifferential Q) :=
  projectiveEntries_mul Q (p.remainder_entries Q) E.entries

lemma reducedDifferential_degree :
    MapDegree Q E.placement E.placement 1 0 (p.reducedDifferential Q) := by
  exact mapDegree_mul Q (p.remainder_degree Q) E.degree

lemma reducedDifferential_square : p.reducedDifferential Q * p.reducedDifferential Q = 0 :=
  GaussianCancellation.cornerReduced_square _ _ _
    (projectiveIdentity_mul Q E.entries) (mul_projectiveIdentity Q E.entries) E.square_zero

lemma reducedDifferential_source_row (i : J) (k : J ⊕ J ⊕ I) :
    p.reducedDifferential Q (.inl i) k = 0 := by
  change (∑ j, p.remainder Q (.inl i) j * E.differential j k) = 0
  simp only [p.remainder_source_row Q, MulZeroClass.zero_mul, Finset.sum_const_zero]

lemma reducedDifferential_target_column (k : J ⊕ J ⊕ I) (j : J) :
    p.reducedDifferential Q k (.inr (.inl j)) = 0 := by
  unfold reducedDifferential
  rw [p.remainder_commutes Q]
  change (∑ l, E.differential k l * p.remainder Q l (.inr (.inl j))) = 0
  simp only [p.remainder_target_column Q, MulZeroClass.mul_zero, Finset.sum_const_zero]

lemma remainder_mul_reduced : p.remainder Q * p.reducedDifferential Q = p.reducedDifferential Q := by
  unfold reducedDifferential
  rw [← _root_.mul_assoc, p.remainder_square Q]

lemma reduced_mul_remainder : p.reducedDifferential Q * p.remainder Q = p.reducedDifferential Q := by
  unfold reducedDifferential
  rw [_root_.mul_assoc, ← p.remainder_commutes Q, ← _root_.mul_assoc, p.remainder_square Q]

noncomputable def reduced : BasedComplex Q (K := K) I where
  placement := fun i => E.placement (.inr (.inr i))
  differential := fun i j => p.reducedDifferential Q (.inr (.inr i)) (.inr (.inr j))
  entries := ⟨fun i j => (p.reducedDifferential_entries Q).1 _ _,
    fun i j => (p.reducedDifferential_entries Q).2 _ _⟩
  degree := fun i j => p.reducedDifferential_degree Q _ _
  square_zero := by
    apply Matrix.ext
    intro i j
    change (∑ k : I,
      p.reducedDifferential Q (.inr (.inr i)) (.inr (.inr k)) *
        p.reducedDifferential Q (.inr (.inr k)) (.inr (.inr j))) = 0
    rw [retained_sum Q _ _ (p.reducedDifferential_target_column Q)
      (p.reducedDifferential_source_row Q), p.reducedDifferential_square Q]
    rfl

noncomputable def reductionMap : Map Q E (p.reduced Q) where
  matrix := fun i j => p.remainder Q i (.inr (.inr j))
  entries := ⟨fun i j => (p.remainder_entries Q).1 _ _,
    fun i j => (p.remainder_entries Q).2 _ _⟩
  degree := fun i j => p.remainder_degree Q _ _
  commute := by
    apply Matrix.ext
    intro i j
    change (E.differential * p.remainder Q) i (.inr (.inr j)) =
      ∑ k : I, p.remainder Q i (.inr (.inr k)) *
        p.reducedDifferential Q (.inr (.inr k)) (.inr (.inr j))
    rw [retained_sum Q _ _ (p.remainder_target_column Q)
      (p.reducedDifferential_source_row Q), p.remainder_mul_reduced Q,
      ← p.remainder_commutes Q]
    rfl

noncomputable def inclusionMap : Map Q (p.reduced Q) E where
  matrix := fun i j => p.remainder Q (.inr (.inr i)) j
  entries := ⟨fun i j => (p.remainder_entries Q).1 _ _,
    fun i j => (p.remainder_entries Q).2 _ _⟩
  degree := fun i j => p.remainder_degree Q _ _
  commute := by
    apply Matrix.ext
    intro i j
    change (∑ k : I, p.reducedDifferential Q (.inr (.inr i)) (.inr (.inr k)) *
      p.remainder Q (.inr (.inr k)) j) =
      (p.remainder Q * E.differential) (.inr (.inr i)) j
    rw [retained_sum Q _ _ (p.reducedDifferential_target_column Q)
      (p.remainder_source_row Q), p.reduced_mul_remainder Q]
    rfl

lemma reduction_inclusion :
    (p.reductionMap Q).matrix * (p.inclusionMap Q).matrix = p.remainder Q := by
  apply Matrix.ext
  intro i j
  change (∑ k : I, p.remainder Q i (.inr (.inr k)) *
    p.remainder Q (.inr (.inr k)) j) = p.remainder Q i j
  rw [retained_sum Q _ _ (p.remainder_target_column Q)
    (p.remainder_source_row Q), p.remainder_square Q]

lemma inclusion_reduction :
    (p.inclusionMap Q).matrix * (p.reductionMap Q).matrix =
      projectiveIdentity Q (p.reduced Q).placement := by
  apply Matrix.ext
  intro i j
  change (p.remainder Q * p.remainder Q) (.inr (.inr i)) (.inr (.inr j)) = _
  rw [p.remainder_square Q, p.remainder_retained Q]
  rfl

noncomputable def reductionEquivalence : HomotopyEquivalence Q E (p.reduced Q) where
  forward := p.reductionMap Q
  backward := p.inclusionMap Q
  sourceHomotopy := -p.homotopy Q
  targetHomotopy := 0
  sourceEntries := projectiveEntries_neg Q (p.homotopy_entries Q)
  targetEntries := projectiveEntries_zero Q
  sourceDegree := mapDegree_neg Q (p.homotopy_degree Q)
  targetDegree := mapDegree_zero Q (-1) 0
  sourceEquation := by
    rw [p.reduction_inclusion Q]
    exact GaussianCancellation.cornerRemainder_homotopy _ _ _
  targetEquation := by
    rw [p.inclusion_reduction Q, Matrix.mul_zero, Matrix.zero_mul, add_zero, add_zero]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.BlockPivot

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Cancellation_ReducedDifferential2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.BlockPivot

variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]
  {E : BasedComplex Q (K := K) (J ⊕ J ⊕ I)} (p : BlockPivot Q E)

lemma reduced_differential (i j : I) :
    (p.reduced Q).differential i j =
      E.differential (.inr (.inr i)) (.inr (.inr j)) -
        ∑ k : J, (p.coefficient⁻¹ • E.differential (.inr (.inr i)) (.inr (.inl k))) *
          E.differential (.inl k) (.inr (.inr j)) := by
  change (p.remainder Q * E.differential) (.inr (.inr i)) (.inr (.inr j)) = _
  rw [show p.remainder Q * E.differential = E.differential -
      E.differential * p.homotopy Q * E.differential from
    GaussianCancellation.cornerRemainder_mul_d _ _ _
      (projectiveIdentity_mul Q E.entries) E.square_zero]
  change E.differential (.inr (.inr i)) (.inr (.inr j)) -
    (∑ k, (E.differential * p.homotopy Q) (.inr (.inr i)) k *
      E.differential k (.inr (.inr j))) = _
  congr 1
  simp only [Fintype.sum_sum_type, p.mul_homotopy Q _ E.entries,
    MulZeroClass.zero_mul, Finset.sum_const_zero, add_zero]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.BlockPivot

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomSpace
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]

lemma projectiveEntries_smul {p : I → GeneratorPlacement V}
    {q : J → GeneratorPlacement V} {M : Matrix I J (Q.Zigzag K)}
    (r : K) (h : ProjectiveEntries Q p q M) :
    ProjectiveEntries Q p q (r • M) := by
  constructor
  · intro i j
    change vertexId Q _ * (r • M i j) = r • M i j
    rw [mul_smul, h.1]
  · intro i j
    change (r • M i j) * vertexId Q _ = r • M i j
    rw [smul_mul, h.2]

lemma mapDegree_smul {p : I → GeneratorPlacement V}
    {q : J → GeneratorPlacement V} {M : Matrix I J (Q.Zigzag K)}
    {n v : ℤ} (r : K) (h : MapDegree Q p q n v M) :
    MapDegree Q p q n v (r • M) := by
  intro i j
  exact ⟨fun hc => by change r • M i j = 0; rw [(h i j).1 hc, smul_zero],
    homogeneous_smul Q (h i j).2 r⟩

namespace BasedComplex

variable [Fintype I] [Fintype J]

def homSpace (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (n v : ℤ) : Submodule K (Matrix I J (Q.Zigzag K)) where
  carrier := {f | ProjectiveEntries Q E.placement F.placement f ∧
    MapDegree Q E.placement F.placement n v f}
  zero_mem' := ⟨projectiveEntries_zero Q, mapDegree_zero Q n v⟩
  add_mem' hf hg := ⟨projectiveEntries_add Q hf.1 hg.1, mapDegree_add Q hf.2 hg.2⟩
  smul_mem' r _ hf := ⟨projectiveEntries_smul Q r hf.1, mapDegree_smul Q r hf.2⟩

noncomputable def homDifferential (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n : ℤ) :
    Matrix I J (Q.Zigzag K) →ₗ[K] Matrix I J (Q.Zigzag K) where
  toFun f := E.differential * f - cochainSign (K := K) n • (f * F.differential)
  map_add' f g := by
    simp only [Matrix.mul_add, Matrix.add_mul, smul_add]
    abel
  map_smul' r f := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    simp only [RingHom.id_apply]
    rw [smul_comm]

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_TraceLinear
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V]

namespace BasedComplex
variable [Fintype I] [Fintype J]

noncomputable def homCycles (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (n v : ℤ) : Submodule K (Matrix I J (Q.Zigzag K)) :=
  homSpace Q E F n v ⊓ LinearMap.ker (homDifferential Q E F n)

noncomputable def homBoundaries (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (n v : ℤ) : Submodule K (Matrix I J (Q.Zigzag K)) :=
  (homSpace Q E F (n - 1) v).map (homDifferential Q E F (n - 1))

abbrev homCohomology (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (n v : ℤ) :=
  homCycles Q E F n v ⧸
    (homBoundaries Q E F n v).comap (homCycles Q E F n v).subtype

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomSpaceMul
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J L : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V] [Fintype I] [Fintype J] [Fintype L]

lemma homSpace_mul {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    {G : BasedComplex Q (K := K) L} {n m v w : ℤ}
    {f : Matrix I J (Q.Zigzag K)} {g : Matrix J L (Q.Zigzag K)}
    (hf : f ∈ homSpace Q E F n v) (hg : g ∈ homSpace Q F G m w) :
    f * g ∈ homSpace Q E G (n + m) (v + w) :=
  ⟨projectiveEntries_mul Q hf.1 hg.1, mapDegree_mul Q hf.2 hg.2⟩

lemma homDifferential_mul (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (G : BasedComplex Q (K := K) L)
    (n m : ℤ) (f : Matrix I J (Q.Zigzag K)) (g : Matrix J L (Q.Zigzag K)) :
    homDifferential Q E G (n + m) (f * g) =
      homDifferential Q E F n f * g +
        cochainSign (K := K) n • (f * homDifferential Q F G m g) := by
  change E.differential * (f * g) - cochainSign (K := K) (n + m) • (f * g * G.differential) =
    (E.differential * f - cochainSign (K := K) n • (f * F.differential)) * g +
      cochainSign (K := K) n • (f * (F.differential * g - cochainSign (K := K) m • (g * G.differential)))
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    smul_sub, smul_smul, cochainSign_add, Matrix.mul_assoc]
  abel

lemma homCycles_mul {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    {G : BasedComplex Q (K := K) L} {n m v w : ℤ}
    {f : Matrix I J (Q.Zigzag K)} {g : Matrix J L (Q.Zigzag K)}
    (hf : f ∈ homCycles Q E F n v) (hg : g ∈ homCycles Q F G m w) :
    f * g ∈ homCycles Q E G (n + m) (v + w) := by
  refine ⟨homSpace_mul Q hf.1 hg.1, ?_⟩
  change homDifferential Q E G (n + m) (f * g) = 0
  rw [homDifferential_mul Q E F G n m,
    show homDifferential Q E F n f = 0 from hf.2,
    show homDifferential Q F G m g = 0 from hg.2,
    Matrix.zero_mul, Matrix.mul_zero, smul_zero, add_zero]

lemma homBoundary_mul_cycle {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} {G : BasedComplex Q (K := K) L}
    {n m v w : ℤ} {f : Matrix I J (Q.Zigzag K)} {g : Matrix J L (Q.Zigzag K)}
    (hf : f ∈ homBoundaries Q E F n v) (hg : g ∈ homCycles Q F G m w) :
    f * g ∈ homBoundaries Q E G (n + m) (v + w) := by
  obtain ⟨h, hh, rfl⟩ := hf
  refine ⟨h * g, ?_, ?_⟩
  · have hm := homSpace_mul Q hh hg.1
    have he : n + m - 1 = n - 1 + m := by omega
    change h * g ∈ homSpace Q E G (n + m - 1) (v + w)
    rw [he]
    exact hm
  · convert homDifferential_mul Q E F G (n - 1) m h g using 1
    · congr 2; omega
    · rw [show homDifferential Q F G m g = 0 from hg.2,
        Matrix.mul_zero, smul_zero, add_zero]

lemma homCycle_mul_boundary {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} {G : BasedComplex Q (K := K) L}
    {n m v w : ℤ} {f : Matrix I J (Q.Zigzag K)} {g : Matrix J L (Q.Zigzag K)}
    (hf : f ∈ homCycles Q E F n v) (hg : g ∈ homBoundaries Q F G m w) :
    f * g ∈ homBoundaries Q E G (n + m) (v + w) := by
  obtain ⟨h, hh, rfl⟩ := hg
  refine ⟨cochainSign (K := K) n • (f * h), ?_, ?_⟩
  · have hm := (homSpace Q E G (n + (m - 1)) (v + w)).smul_mem
      (cochainSign (K := K) n) (homSpace_mul Q hf.1 hh)
    have he : n + m - 1 = n + (m - 1) := by omega
    change cochainSign (K := K) n • (f * h) ∈ homSpace Q E G (n + m - 1) (v + w)
    rw [he]
    exact hm
  · rw [map_smul]
    have hm := homDifferential_mul Q E F G n (m - 1) f h
    have he : n + m - 1 = n + (m - 1) := by omega
    rw [he, hm, show homDifferential Q E F n f = 0 from hf.2,
      Matrix.zero_mul, zero_add, smul_smul, cochainSign_mul_self, one_smul]

lemma map_mem_homCycles {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (f : Map Q E F) :
    f.matrix ∈ homCycles Q E F 0 0 := by
  refine ⟨⟨f.entries, f.degree⟩, ?_⟩
  change E.differential * f.matrix - cochainSign (K := K) 0 •
    (f.matrix * F.differential) = 0
  rw [cochainSign_zero, one_smul, f.commute, sub_self]

lemma homotopyEquation_boundary {E : BasedComplex Q (K := K) I}
    {f : Matrix I I (Q.Zigzag K)} {h : Matrix I I (Q.Zigzag K)}
    (hh : h ∈ homSpace Q E E (-1) 0)
    (he : f = E.differential * h + h * E.differential) :
    f ∈ homBoundaries Q E E 0 0 := by
  refine ⟨h, hh, ?_⟩
  change E.differential * h - cochainSign (K := K) (-1) • (h * E.differential) = f
  have hs : cochainSign (K := K) (-1) = -1 := by
    rw [cochainSign_neg, show (1 : ℤ) = 0 + 1 by rfl, cochainSign_add_one, cochainSign_zero]
  rw [hs, neg_one_smul, sub_neg_eq_add, he]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_DiagonalVertex
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

variable [DecidableEq I]

omit [Fintype V] in
lemma identity_mem_homCycles (E : BasedComplex Q (K := K) I) :
    projectiveIdentity Q E.placement ∈ homCycles Q E E 0 0 := by
  exact map_mem_homCycles Q (HomotopyEquivalence.refl Q E).forward

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomOperator
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J I' J' : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V] [Fintype I] [Fintype J] [Fintype I'] [Fintype J']

structure HomOperator (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (E' : BasedComplex Q (K := K) I')
    (F' : BasedComplex Q (K := K) J') where
  component : ℤ → Matrix I J (Q.Zigzag K) →ₗ[K] Matrix I' J' (Q.Zigzag K)
  preserves : ∀ n v f, f ∈ homSpace Q E F n v → component n f ∈ homSpace Q E' F' n v
  commute : ∀ n v f, f ∈ homSpace Q E F n v →
    homDifferential Q E' F' n (component n f) =
      component (n + 1) (homDifferential Q E F n f)

namespace HomOperator
variable {Q} {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
  {E' : BasedComplex Q (K := K) I'} {F' : BasedComplex Q (K := K) J'}

lemma map_cycles (T : HomOperator Q E F E' F') (n v : ℤ)
    {f : Matrix I J (Q.Zigzag K)} (hf : f ∈ homCycles Q E F n v) :
    T.component n f ∈ homCycles Q E' F' n v := by
  constructor
  · exact T.preserves n v f hf.1
  · change homDifferential Q E' F' n (T.component n f) = 0
    rw [T.commute n v f hf.1, show homDifferential Q E F n f = 0 from hf.2, map_zero]

lemma map_boundaries (T : HomOperator Q E F E' F') (n v : ℤ)
    {f : Matrix I J (Q.Zigzag K)} (hf : f ∈ homBoundaries Q E F n v) :
    T.component n f ∈ homBoundaries Q E' F' n v := by
  obtain ⟨g, hg, rfl⟩ := hf
  refine ⟨T.component (n - 1) g, T.preserves (n - 1) v g hg, ?_⟩
  simpa only [sub_add_cancel] using T.commute (n - 1) v g hg

noncomputable def onCycles (T : HomOperator Q E F E' F') (n v : ℤ) :
    homCycles Q E F n v →ₗ[K] homCycles Q E' F' n v :=
  (T.component n).restrict (fun _ hf => T.map_cycles n v hf)

noncomputable def onCohomology (T : HomOperator Q E F E' F') (n v : ℤ) :
    homCohomology Q E F n v →ₗ[K] homCohomology Q E' F' n v :=
  Submodule.mapQ _ _ (T.onCycles n v) (by
    intro f hf
    exact T.map_boundaries n v hf)

lemma onCohomology_injective (T : HomOperator Q E F E' F') (n v : ℤ)
    (hr : ∀ f, f ∈ homCycles Q E F n v →
      T.component n f ∈ homBoundaries Q E' F' n v → f ∈ homBoundaries Q E F n v) :
    Function.Injective (T.onCohomology n v) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm
  · intro x hx
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change Submodule.Quotient.mk (T.onCycles n v f) = 0 at hx
    have hb := (Submodule.Quotient.mk_eq_zero _).mp hx
    have hf := hr f f.property hb
    change Submodule.Quotient.mk f = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr hf
  · exact bot_le

end HomOperator

lemma homDifferential_sandwich {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} {E' : BasedComplex Q (K := K) I'}
    {F' : BasedComplex Q (K := K) J'} (a : Map Q E' E) (b : Map Q F F')
    (n : ℤ) (f : Matrix I J (Q.Zigzag K)) :
    homDifferential Q E' F' n (a.matrix * f * b.matrix) =
      a.matrix * homDifferential Q E F n f * b.matrix := by
  change E'.differential * (a.matrix * f * b.matrix) -
    cochainSign (K := K) n • (a.matrix * f * b.matrix * F'.differential) =
    a.matrix * (E.differential * f -
      cochainSign (K := K) n • (f * F.differential)) * b.matrix
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, a.commute]
    simp only [Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, ← b.commute]
    simp only [Matrix.mul_assoc]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_TestTransform
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J L : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [DecidableEq A] in
lemma testTransform_neg (p : I → GeneratorPlacement V)
    (q : J → GeneratorPlacement V) (α : V) (M : Matrix I J (Q.Zigzag K)) :
    testTransform Q p q α (-M) = -testTransform Q p q α M := by
  apply Matrix.ext
  intro i j
  simp only [testTransform, scalarCornerMatrix, testMatrix, Matrix.neg_apply,
    _root_.mul_neg, map_neg, Pi.neg_apply, neg_smul]

end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PositiveHomTransform
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K I J : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [DecidableEq A] in
lemma testTransform_smul (p : I → GeneratorPlacement V) (q : J → GeneratorPlacement V)
    (α : V) (r : K) (f : Matrix I J (Q.Zigzag K)) :
    testTransform Q p q α (r • f) = r • testTransform Q p q α f := by
  apply Matrix.ext
  intro i j
  simp only [testTransform, scalarCornerMatrix, testMatrix, Matrix.smul_apply,
    mul_smul, coordinates_smul, smul_smul]

omit [DecidableEq A] in
lemma testTransform_sub (p : I → GeneratorPlacement V) (q : J → GeneratorPlacement V)
    (α : V) (f g : Matrix I J (Q.Zigzag K)) :
    testTransform Q p q α (f - g) =
      testTransform Q p q α f - testTransform Q p q α g := by
  simp only [sub_eq_add_neg, testTransform_add, testTransform_neg]

namespace BasedComplex
variable [Fintype I] [Fintype J]

noncomputable def positiveHomTransform (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) (n : ℤ)
    (f : Matrix I J (Q.Zigzag K)) :
    Matrix (TestIndex Q E.placement α ⊕ I) (TestIndex Q F.placement α ⊕ J) (Q.Zigzag K) :=
  Matrix.fromBlocks (cochainSign (K := K) n • testTransform Q E.placement F.placement α f)
    0 0 f

noncomputable def negativeHomTransform (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) (n : ℤ)
    (f : Matrix I J (Q.Zigzag K)) :
    Matrix (I ⊕ TestIndex Q E.placement α) (J ⊕ TestIndex Q F.placement α) (Q.Zigzag K) :=
  Matrix.fromBlocks f 0 0
    (cochainSign (K := K) n • testTransform Q E.placement F.placement α f)

lemma positiveHomTransform_entries (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) (n : ℤ)
    {f : Matrix I J (Q.Zigzag K)} (hf : ProjectiveEntries Q E.placement F.placement f) :
    ProjectiveEntries Q (E.positiveTwist Q α).placement (F.positiveTwist Q α).placement
      (positiveHomTransform Q E F α n f) := by
  have ht := projectiveEntries_smul Q (cochainSign (K := K) n)
    (scalarCornerMatrix_entries Q α (testPlacement Q E.placement α)
      (testPlacement Q F.placement α) (fun _ => rfl) (fun _ => rfl)
        (testMatrix Q E.placement F.placement α f))
  constructor <;> intro i j <;> rcases i with i | i <;> rcases j with j | j
  · exact ht.1 i j
  · exact MulZeroClass.mul_zero _
  · exact MulZeroClass.mul_zero _
  · exact hf.1 i j
  · exact ht.2 i j
  · exact MulZeroClass.zero_mul _
  · exact MulZeroClass.zero_mul _
  · exact hf.2 i j

lemma negativeHomTransform_entries (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) (n : ℤ)
    {f : Matrix I J (Q.Zigzag K)} (hf : ProjectiveEntries Q E.placement F.placement f) :
    ProjectiveEntries Q (E.negativeTwist Q α).placement (F.negativeTwist Q α).placement
      (negativeHomTransform Q E F α n f) := by
  have ht := projectiveEntries_smul Q (cochainSign (K := K) n)
    (scalarCornerMatrix_entries Q α (cotestPlacement Q E.placement α)
      (cotestPlacement Q F.placement α) (fun _ => rfl) (fun _ => rfl)
        (testMatrix Q E.placement F.placement α f))
  constructor <;> intro i j <;> rcases i with i | i <;> rcases j with j | j
  · exact hf.1 i j
  · exact MulZeroClass.mul_zero _
  · exact MulZeroClass.mul_zero _
  · exact ht.1 i j
  · exact hf.2 i j
  · exact MulZeroClass.zero_mul _
  · exact MulZeroClass.zero_mul _
  · exact ht.2 i j

lemma positiveHomTransform_degree (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) (n v : ℤ)
    {f : Matrix I J (Q.Zigzag K)} (hf : MapDegree Q E.placement F.placement n v f) :
    MapDegree Q (E.positiveTwist Q α).placement (F.positiveTwist Q α).placement n v
      (positiveHomTransform Q E F α n f) := by
  have ht := mapDegree_smul Q (cochainSign (K := K) n) (testMatrix_degree Q α hf)
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · constructor
    · intro hc
      apply (ht i j).1
      intro he
      apply hc
      change (testPlacement Q F.placement α j).cochain - 1 =
        (testPlacement Q E.placement α i).cochain - 1 + n
      omega
    · exact (ht i j).2
  · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · exact hf i j

lemma negativeHomTransform_degree (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) (n v : ℤ)
    {f : Matrix I J (Q.Zigzag K)} (hf : MapDegree Q E.placement F.placement n v f) :
    MapDegree Q (E.negativeTwist Q α).placement (F.negativeTwist Q α).placement n v
      (negativeHomTransform Q E F α n f) := by
  have ht := mapDegree_smul Q (cochainSign (K := K) n) (cotestMatrix_degree Q α hf)
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · exact hf i j
  · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · constructor
    · intro hc
      apply (ht i j).1
      intro he
      apply hc
      change (cotestPlacement Q F.placement α j).cochain + 1 =
        (cotestPlacement Q E.placement α i).cochain + 1 + n
      omega
    · exact (ht i j).2

lemma positiveHomTransform_differential (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) (n : ℤ)
    {f : Matrix I J (Q.Zigzag K)} (hf : ProjectiveEntries Q E.placement F.placement f) :
    homDifferential Q (E.positiveTwist Q α) (F.positiveTwist Q α) n
      (positiveHomTransform Q E F α n f) =
    positiveHomTransform Q E F α (n + 1) (homDifferential Q E F n f) := by
  change (E.positiveTwist Q α).differential * positiveHomTransform Q E F α n f -
    cochainSign (K := K) n • (positiveHomTransform Q E F α n f * (F.positiveTwist Q α).differential) = _
  rw [positiveTwist_differential, positiveTwist_differential]
  unfold positiveHomTransform
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul,
    sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
  simp only [← sub_eq_add_neg]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, smul_zero,
    testTransform_mul Q α _ E.entries, testTransform_mul Q α _ hf,
    evaluation_natural Q α hf, smul_smul, cochainSign_mul_self, one_smul,
    sub_self, cochainSign_add_one, neg_zero]
  congr 1
  simp [homDifferential, testTransform_sub, testTransform_smul,
    smul_sub, smul_smul, cochainSign_mul_self, neg_smul, smul_neg]

lemma negativeHomTransform_differential (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) (n : ℤ)
    {f : Matrix I J (Q.Zigzag K)} (hf : ProjectiveEntries Q E.placement F.placement f) :
    homDifferential Q (E.negativeTwist Q α) (F.negativeTwist Q α) n
      (negativeHomTransform Q E F α n f) =
    negativeHomTransform Q E F α (n + 1) (homDifferential Q E F n f) := by
  change (E.negativeTwist Q α).differential * negativeHomTransform Q E F α n f -
    cochainSign (K := K) n • (negativeHomTransform Q E F α n f * (F.negativeTwist Q α).differential) = _
  rw [negativeTwist_differential, negativeTwist_differential]
  unfold negativeHomTransform
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul,
    sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
  simp only [← sub_eq_add_neg]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, smul_zero,
    testTransform_mul Q α _ E.entries, testTransform_mul Q α _ hf,
    coevaluation_natural Q α hf, sub_self, cochainSign_add_one, neg_zero]
  congr 1
  simp [homDifferential, testTransform_sub, testTransform_smul,
    smul_sub, smul_smul, cochainSign_mul_self, neg_smul, smul_neg]

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ReindexHomOperator
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J I' J' : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V] [Fintype I] [Fintype J] [Fintype I'] [Fintype J']

noncomputable def reindexHomOperator (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (e : I' ≃ I) (f : J' ≃ J) :
    HomOperator Q E F (E.reindex Q e) (F.reindex Q f) where
  component _ := {
    toFun g := g.submatrix e f
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  preserves n v g hg := by
    constructor
    · exact ⟨fun i j => hg.1.1 (e i) (f j), fun i j => hg.1.2 (e i) (f j)⟩
    · exact fun i j => hg.2 (e i) (f j)
  commute n v g _ := by
    change E.differential.submatrix e e * g.submatrix e f -
      cochainSign (K := K) n • (g.submatrix e f * F.differential.submatrix f f) =
      (E.differential * g - cochainSign (K := K) n • (g * F.differential)).submatrix e f
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    rfl

noncomputable def sandwichHomOperator {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} {E' : BasedComplex Q (K := K) I'}
    {F' : BasedComplex Q (K := K) J'} (a : Map Q E' E) (b : Map Q F F') :
    HomOperator Q E F E' F' where
  component _ := {
    toFun g := a.matrix * g * b.matrix
    map_add' _ _ := by simp only [Matrix.mul_add, Matrix.add_mul]
    map_smul' _ _ := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  preserves n v g hg := by
    constructor
    · exact projectiveEntries_mul Q (projectiveEntries_mul Q a.entries hg.1) b.entries
    · change MapDegree Q E'.placement F'.placement n v (a.matrix * g * b.matrix)
      simpa only [zero_add, add_zero] using
        mapDegree_mul Q (mapDegree_mul Q a.degree hg.2) b.degree
  commute n _ g _ := homDifferential_sandwich Q a b n g

variable [Fintype V] [DecidableEq A]

noncomputable def positiveHomOperator (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) :
    HomOperator Q E F (E.positiveTwist Q α) (F.positiveTwist Q α) where
  component n := {
    toFun := positiveHomTransform Q E F α n
    map_add' f g := by
      simp only [positiveHomTransform, testTransform_add, smul_add]
      rw [Matrix.fromBlocks_add]
      simp only [add_zero]
    map_smul' r f := by
      simp only [positiveHomTransform, testTransform_smul, RingHom.id_apply]
      rw [Matrix.fromBlocks_smul, smul_comm r]
      simp only [smul_zero] }
  preserves n v g hg := ⟨positiveHomTransform_entries Q E F α n hg.1,
    positiveHomTransform_degree Q E F α n v hg.2⟩
  commute n _ g hg := positiveHomTransform_differential Q E F α n hg.1

noncomputable def negativeHomOperator (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) :
    HomOperator Q E F (E.negativeTwist Q α) (F.negativeTwist Q α) where
  component n := {
    toFun := negativeHomTransform Q E F α n
    map_add' f g := by
      simp only [negativeHomTransform, testTransform_add, smul_add]
      rw [Matrix.fromBlocks_add]
      simp only [add_zero]
    map_smul' r f := by
      simp only [negativeHomTransform, testTransform_smul, RingHom.id_apply]
      rw [Matrix.fromBlocks_smul, smul_comm r]
      simp only [smul_zero] }
  preserves n v g hg := ⟨negativeHomTransform_entries Q E F α n hg.1,
    negativeHomTransform_degree Q E F α n v hg.2⟩
  commute n _ g hg := negativeHomTransform_differential Q E F α n hg.1

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_CorrectionBoundary
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J I' J' : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V] [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
  [DecidableEq I] [DecidableEq J] [DecidableEq I'] [DecidableEq J']

lemma HomotopyEquivalence.sourceCorrection_boundary {E : BasedComplex Q (K := K) I}
    {E' : BasedComplex Q (K := K) I'} (e : HomotopyEquivalence Q E E') :
    e.forward.matrix * e.backward.matrix - projectiveIdentity Q E.placement ∈
      homBoundaries Q E E 0 0 := by
  apply homotopyEquation_boundary Q ⟨e.sourceEntries, e.sourceDegree⟩
  rw [e.sourceEquation]
  abel

lemma HomotopyEquivalence.sandwichCorrection_boundary {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} {E' : BasedComplex Q (K := K) I'}
    {F' : BasedComplex Q (K := K) J'}
    (e : HomotopyEquivalence Q E E') (f : HomotopyEquivalence Q F F')
    (n v : ℤ) {g : Matrix I J (Q.Zigzag K)} (hg : g ∈ homCycles Q E F n v) :
    e.forward.matrix * (e.backward.matrix * g * f.forward.matrix) * f.backward.matrix - g ∈
      homBoundaries Q E F n v := by
  have hl := homBoundary_mul_cycle Q (e.sourceCorrection_boundary Q) hg
  have hr := homCycle_mul_boundary Q hg (f.sourceCorrection_boundary Q)
  have hc := homCycles_mul Q (map_mem_homCycles Q f.forward) (map_mem_homCycles Q f.backward)
  have hll := homBoundary_mul_cycle Q hl hc
  simp only [zero_add, add_zero] at hll hr
  have hb := (homBoundaries Q E F n v).add_mem hll hr
  have heq : (e.forward.matrix * e.backward.matrix - projectiveIdentity Q E.placement) *
      g * (f.forward.matrix * f.backward.matrix) +
      g * (f.forward.matrix * f.backward.matrix - projectiveIdentity Q F.placement) =
      e.forward.matrix * (e.backward.matrix * g * f.forward.matrix) * f.backward.matrix - g := by
    have hi : projectiveIdentity Q E.placement * g = g := projectiveIdentity_mul Q hg.1.1
    have hj : g * projectiveIdentity Q F.placement = g := mul_projectiveIdentity Q hg.1.1
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub]
    erw [hi, hj]
    simp only [Matrix.mul_assoc]
    abel
  rw [heq] at hb
  exact hb

lemma HomotopyEquivalence.sandwich_injective {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} {E' : BasedComplex Q (K := K) I'}
    {F' : BasedComplex Q (K := K) J'}
    (e : HomotopyEquivalence Q E E') (f : HomotopyEquivalence Q F F') (n v : ℤ) :
    Function.Injective ((sandwichHomOperator Q e.backward f.forward).onCohomology n v) := by
  apply HomOperator.onCohomology_injective
  intro g hg hb
  have hb' := (sandwichHomOperator Q e.forward f.backward).map_boundaries n v hb
  have hc := e.sandwichCorrection_boundary Q f n v hg
  have hd := (homBoundaries Q E F n v).sub_mem hb' hc
  change e.forward.matrix * (e.backward.matrix * g * f.forward.matrix) * f.backward.matrix -
    (e.forward.matrix * (e.backward.matrix * g * f.forward.matrix) * f.backward.matrix - g) ∈
      homBoundaries Q E F n v at hd
  simpa only [sub_sub_cancel] using hd

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_InverseHomMatrix
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

noncomputable def inverseHomMatrix (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) (n : ℤ)
    (f : Matrix I J (Q.Zigzag K)) :
    Matrix (InverseTwistIndex Q E α) (InverseTwistIndex Q F α) (Q.Zigzag K) :=
  Matrix.fromBlocks (cochainSign (K := K) n • testTransform Q E.placement F.placement α f) 0 0
    (Matrix.fromBlocks (testTransform Q E.placement F.placement α f) 0 0
      (Matrix.fromBlocks (testTransform Q E.placement F.placement α f) 0 0
        (Matrix.fromBlocks f 0 0
          (cochainSign (K := K) n • testTransform Q E.placement F.placement α f))))

omit [DecidableEq I] [DecidableEq J] in
lemma inverseHomMatrix_normalized (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (α : V) (n : ℤ) (f : Matrix I J (Q.Zigzag K)) :
    (positiveHomTransform Q (E.negativeTwist Q α) (F.negativeTwist Q α) α n
      (negativeHomTransform Q E F α n f)).submatrix
      (inverseTwistIndexEquiv Q hn E α) (inverseTwistIndexEquiv Q hn F α) =
      inverseHomMatrix Q E F α n f := by
  apply Matrix.ext
  intro i j
  rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v
  all_goals simp only [Matrix.submatrix_apply, inverseTwistIndexEquiv, Equiv.coe_fn_mk,
    inverseHomMatrix, positiveHomTransform, negativeHomTransform, Matrix.fromBlocks,
    Matrix.smul_apply,
    testTransform, scalarCornerMatrix, testMatrix, Matrix.of_apply,
    Matrix.zero_apply, Sum.elim_inl, Sum.elim_inr, MulZeroClass.mul_zero,
    coordinates_zero, zero_smul, smul_zero, selfCornerEquiv_false, selfCornerEquiv_true]
  all_goals simp only [mul_smul, coordinates_smul, pathBasis_vertex, pathBasis_token, smul_smul]
  all_goals (
    have ht : tokenBasis Q (K := K) α * vertexId Q α = tokenBasis Q α := by
      simpa only [Path.target, pathBasis_token] using
        (pathBasis_right Q (K := K) (.inr (.inr α)))
    simp only [vertexId_mul_self, ht, pathCoordinates_vertex, pathCoordinates_token]
    have hv : (vertexId Q (K := K) α).vertex α = 1 := by
      simp only [vertex_vertexId, Pi.single_eq_same]
    have htv : (tokenBasis Q (K := K) α).vertex α = 0 := rfl
    have htt : (tokenBasis Q (K := K) α).token α = 1 := by
      change (Pi.single α (1 : K) : V → K) α = 1
      exact Pi.single_eq_same α 1
    simp only [hv, htv, htt, token_vertexId, Pi.zero_apply,
      _root_.mul_one, MulZeroClass.mul_zero])
  all_goals first
    | exact zero_smul K (vertexId Q α)
    | exact congrArg (fun c : K => c • vertexId Q α)
        (by rw [← _root_.mul_assoc, cochainSign_mul_self]; exact _root_.one_mul _)

lemma inverseHomMatrix_projection (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) (n : ℤ)
    {f : Matrix I J (Q.Zigzag K)} (hf : ProjectiveEntries Q E.placement F.placement f) :
    inverseHomMatrix Q E F α n f * inverseTwistProjection Q F α =
      inverseTwistProjection Q E α * f := by
  apply Matrix.ext
  intro i j
  rcases i with u | u | u | i | u
  all_goals simp only [Matrix.mul_apply, Fintype.sum_sum_type,
    inverseHomMatrix, inverseTwistProjection, Matrix.fromBlocks, Matrix.of_apply,
    Matrix.zero_apply, Sum.elim_inl, Sum.elim_inr, MulZeroClass.mul_zero,
    MulZeroClass.zero_mul, Finset.sum_const_zero, zero_add, add_zero]
  · exact congrArg (fun a => a u j) (evaluation_natural Q α hf)
  · exact congrArg (fun a => a i j)
      ((projectiveIdentity_mul Q hf).trans (mul_projectiveIdentity Q hf).symm).symm

lemma inverseHomMatrix_extract (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) (n : ℤ)
    {f : Matrix I J (Q.Zigzag K)} (hf : ProjectiveEntries Q E.placement F.placement f) :
    inverseTwistInjection Q E α * inverseHomMatrix Q E F α n f *
      inverseTwistProjection Q F α = f := by
  rw [Matrix.mul_assoc, inverseHomMatrix_projection Q E F α n hf,
    ← Matrix.mul_assoc, inverseTwist_targetEquation]
  exact projectiveIdentity_mul Q hf

lemma reverseHomMatrix_projection (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) (n : ℤ)
    {f : Matrix I J (Q.Zigzag K)} (hf : ProjectiveEntries Q E.placement F.placement f) :
    inverseHomMatrix Q E F α n f * reverseTwistProjection Q F α =
      reverseTwistProjection Q E α * f := by
  apply Matrix.ext
  intro i j
  rcases i with u | u | u | i | u
  all_goals simp only [Matrix.mul_apply, Fintype.sum_sum_type,
    inverseHomMatrix, reverseTwistProjection, Matrix.fromBlocks, Matrix.of_apply,
    Matrix.zero_apply, Sum.elim_inl, Sum.elim_inr, MulZeroClass.mul_zero,
    MulZeroClass.zero_mul, Finset.sum_const_zero, zero_add, add_zero, mul_neg, neg_mul, Finset.sum_neg_distrib, neg_zero]
  · exact congrArg (fun a => -a u j) (evaluation_natural Q α hf)
  · exact congrArg (fun a => a i j)
      ((projectiveIdentity_mul Q hf).trans (mul_projectiveIdentity Q hf).symm).symm

lemma reverseHomMatrix_extract (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) (n : ℤ)
    {f : Matrix I J (Q.Zigzag K)} (hf : ProjectiveEntries Q E.placement F.placement f) :
    reverseTwistInjection Q E α * inverseHomMatrix Q E F α n f *
      reverseTwistProjection Q F α = f := by
  rw [Matrix.mul_assoc, reverseHomMatrix_projection Q E F α n hf,
    ← Matrix.mul_assoc, reverseTwist_targetEquation]
  exact projectiveIdentity_mul Q hf

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_OrthogonalVertices
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A : Type*} (Q : ReversibleQuiver V A)

lemma OrthogonalVertices.symm {α β : V} (h : OrthogonalVertices Q α β) :
    OrthogonalVertices Q β α := by
  refine ⟨h.1.symm, ?_⟩
  intro a hs ht
  exact h.2 (Q.reverse a) ((Q.source_reverse a).trans ht)
    ((Q.target_reverse a).trans hs)

namespace BasedComplex

variable {K I J : Type*} [Field K] [Fintype V] [Fintype A]
  [DecidableEq V] [DecidableEq A] [Fintype I] [Fintype J]

variable [DecidableEq I] [DecidableEq J]

abbrev CommuteTwistIndex (E : BasedComplex Q (K := K) I) (α β : V) :=
  TestIndex Q E.placement α ⊕ TestIndex Q E.placement β ⊕ I

noncomputable def commuteTwistIndexEquiv (E : BasedComplex Q (K := K) I)
    {α β : V} (h : OrthogonalVertices Q α β) :
    CommuteTwistIndex Q E α β ≃
      (TestIndex Q (E.positiveTwist Q β).placement α ⊕ (TestIndex Q E.placement β ⊕ I)) where
  toFun
    | .inl u => .inl ⟨.inr u.1, u.2⟩
    | .inr u => .inr u
  invFun
    | .inl ⟨.inl _, p⟩ => (no_corner_of_orthogonal Q h p).elim
    | .inl ⟨.inr i, p⟩ => .inl ⟨i, p⟩
    | .inr u => .inr u
  left_inv u := by
    rcases u with u | u <;> rfl
  right_inv u := by
    rcases u with ⟨u | i, p⟩ | u
    · exact (no_corner_of_orthogonal Q h p).elim
    · rfl
    · rfl

noncomputable def normalizedCommuteTwist (E : BasedComplex Q (K := K) I)
    {α β : V} (h : OrthogonalVertices Q α β) :
    BasedComplex Q (K := K) (CommuteTwistIndex Q E α β) :=
  ((E.positiveTwist Q β).positiveTwist Q α).reindex Q (commuteTwistIndexEquiv Q E h)

def commuteTwistPlacement (E : BasedComplex Q (K := K) I) (α β : V) :
    CommuteTwistIndex Q E α β → GeneratorPlacement V
  | .inl u => ⟨α, (E.placement u.1).cochain - 1,
      (E.placement u.1).internal + Path.length u.2.val⟩
  | .inr (.inl u) => ⟨β, (E.placement u.1).cochain - 1,
      (E.placement u.1).internal + Path.length u.2.val⟩
  | .inr (.inr i) => E.placement i

omit [DecidableEq I] in
lemma normalizedCommuteTwist_placement (E : BasedComplex Q (K := K) I)
    {α β : V} (h : OrthogonalVertices Q α β) :
    (normalizedCommuteTwist Q E h).placement = commuteTwistPlacement Q E α β := by
  funext u
  rcases u with u | u | i <;> rfl

noncomputable def commuteTwistDifferential (E : BasedComplex Q (K := K) I) (α β : V) :
    Matrix (CommuteTwistIndex Q E α β) (CommuteTwistIndex Q E α β) (Q.Zigzag K)
  | .inl u, .inl v => -testTransform Q E.placement E.placement α E.differential u v
  | .inr (.inl u), .inr (.inl v) => -testTransform Q E.placement E.placement β E.differential u v
  | .inl u, .inr (.inr j) => evaluationMatrix Q E.placement α u j
  | .inr (.inl u), .inr (.inr j) => evaluationMatrix Q E.placement β u j
  | .inr (.inr i), .inr (.inr j) => E.differential i j
  | _, _ => 0

omit [DecidableEq I] in
lemma normalizedCommuteTwist_differential (E : BasedComplex Q (K := K) I)
    {α β : V} (h : OrthogonalVertices Q α β) :
    (normalizedCommuteTwist Q E h).differential = commuteTwistDifferential Q E α β := by
  apply Matrix.ext
  intro i j
  rcases i with u | u | i <;> rcases j with v | v | j
  all_goals simp only [normalizedCommuteTwist, reindex, Matrix.submatrix_apply,
    commuteTwistIndexEquiv, Equiv.coe_fn_mk, positiveTwist_differential,
    Matrix.fromBlocks, commuteTwistDifferential, Matrix.neg_apply, Matrix.of_apply,
    Matrix.zero_apply, Sum.elim_inl, Sum.elim_inr, testTransform, scalarCornerMatrix, testMatrix,
    evaluationMatrix, Sum.inr_ne_inl, Sum.inr.injEq, ↓reduceIte]
  refine @ite_cond_congr _ _ _ ?_ ?_ _ _ (Sum.inr.injEq _ _)

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomDimension
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
universe u
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

instance finiteDimensional : FiniteDimensional K (Q.Zigzag K) :=
  (pathBasis Q (K := K)).finiteDimensional_of_finite

namespace BasedComplex
variable {I J I' J' : Type*} [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
  [DecidableEq I] [DecidableEq J] [DecidableEq I'] [DecidableEq J']

noncomputable def homDimension (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) : ℕ :=
  Module.finrank K (homCohomology Q E F n v)

omit [DecidableEq A] in
lemma HomotopyEquivalence.homDimension_eq {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} {E' : BasedComplex Q (K := K) I'}
    {F' : BasedComplex Q (K := K) J'}
    (e : HomotopyEquivalence Q E E') (f : HomotopyEquivalence Q F F') (n v : ℤ) :
    homDimension Q E F n v = homDimension Q E' F' n v := by
  apply le_antisymm
  · exact LinearMap.finrank_le_finrank_of_injective (e.sandwich_injective Q f n v)
  · exact LinearMap.finrank_le_finrank_of_injective ((e.symm Q).sandwich_injective Q (f.symm Q) n v)

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomDetector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V]
variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def homDetector (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ)
    (L : Matrix I J (Q.Zigzag K) →ₗ[K] K)
    (hL : ∀ f ∈ homBoundaries Q E F n v, L f = 0) :
    homCohomology Q E F n v →ₗ[K] K :=
  Submodule.liftQ _ (L.comp (homCycles Q E F n v).subtype) (by
    intro f hf
    exact hL f hf)

lemma boundary_of_homDimension_le_one (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ)
    (hd : homDimension Q E F n v ≤ 1)
    (L : Matrix I J (Q.Zigzag K) →ₗ[K] K)
    (hL : ∀ f ∈ homBoundaries Q E F n v, L f = 0)
    {u : Matrix I J (Q.Zigzag K)} (hu : u ∈ homCycles Q E F n v) (huL : L u ≠ 0)
    {f : Matrix I J (Q.Zigzag K)} (hf : f ∈ homCycles Q E F n v) (hfL : L f = 0) :
    f ∈ homBoundaries Q E F n v := by
  let T := homDetector Q E F n v L hL
  have hin := injective_of_finrank_le_one hd T
    (Submodule.Quotient.mk (⟨u, hu⟩ : homCycles Q E F n v)) huL
  have hz : (Submodule.Quotient.mk (⟨f, hf⟩ : homCycles Q E F n v) :
      homCohomology Q E F n v) = 0 := by
    apply hin
    change L f = T 0
    rw [map_zero]
    exact hfL
  exact (Submodule.Quotient.mk_eq_zero
    ((homBoundaries Q E F n v).comap (homCycles Q E F n v).subtype)).mp hz

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PureHomSpaceHomogeneous
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J : Type*} [Fintype I] [Fintype J]

lemma pure_homSpace_homogeneous (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k n v r : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (h : n + v = k-l+r) {f : Matrix I J (Q.Zigzag K)}
    (hf : f ∈ homSpace Q E F n v) (i : I) (j : J) : Homogeneous Q r (f i j) := by
  by_cases hc : (F.placement j).cochain = (E.placement i).cochain + n
  · have he := hE i
    have ht := hF j
    dsimp only [GeneratorPlacement.level] at he ht
    have hh : v + (E.placement i).internal - (F.placement j).internal = r := by omega
    rw [← hh]
    exact (hf.2 i j).2
  · rw [(hf.2 i j).1 hc]
    exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

lemma pure_homSpace_linear (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k n v : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (h : n + v = k-l+1) {f : Matrix I J (Q.Zigzag K)}
    (hf : f ∈ homSpace Q E F n v) : LinearMatrix Q f := by
  intro i j
  have hh := pure_homSpace_homogeneous Q E F hE hF h hf i j
  exact ⟨hh.1 (by norm_num), hh.2.2 (by norm_num)⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_CoefficientTopDual
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

omit [Fintype V] [DecidableEq A] in
lemma pure_differential_linear (E : BasedComplex Q (K := K) I) {l : ℤ}
    (hE : ∀ i, (E.placement i).level = l) : LinearMatrix Q E.differential :=
  pure_homSpace_linear Q E E hE hE (by omega) ⟨E.entries,E.degree⟩

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

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma pure_differential_arrow (E:BasedComplex Q (K:=K) I) {q:ℤ}
    (hp:∀ i,(E.placement i).level=q) {i j:I} (hne:E.differential i j≠0) :
    ∃ a:A,Q.source a=(E.placement i).color ∧ Q.target a=(E.placement j).color := by
  have hl:=pure_differential_linear Q E hp i j
  have ha:∃ a,(E.differential i j).arrow a≠0 := by
    by_contra hn
    push Not at hn
    apply hne
    apply ext
    · exact hl.1
    · exact funext hn
    · exact hl.2
  obtain ⟨a,ha⟩:=ha
  exact ⟨a,coordinates_corner Q (E.entries.1 i j) (E.entries.2 i j)
    (p:=.inr (.inl a)) ha⟩

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma pure_color_block (E:BasedComplex Q (K:=K) I) {q:ℤ} (U:Set V)
    (hp:∀ i,(E.placement i).level=q)
    (hb:∀ i,(E.placement i).color∉colorBoundary Q U) :
    BlockClosed Q E {i | (E.placement i).color∈U} := by
  intro i j hn
  obtain ⟨a,hs,ht⟩:=pure_differential_arrow Q E hp hn
  change ((E.placement i).color∈U ↔ (E.placement j).color∈U)
  constructor
  · intro hi
    by_contra hj
    exact hb j ⟨hj,a,hs ▸ hi,ht⟩
  · intro hj
    by_contra hi
    apply hb i
    exact ⟨hi,Q.reverse a,by simpa only [Q.source_reverse,ht] using hj,
      by simpa only [Q.target_reverse] using hs⟩

noncomputable def colorRestriction (E:BasedComplex Q (K:=K) I) {q:ℤ} (U:Set V)
    (hp:∀ i,(E.placement i).level=q)
    (hb:∀ i,(E.placement i).color∉colorBoundary Q U) :
    BasedComplex Q (K:=K) {i // (E.placement i).color∈U} :=
  blockRestriction Q E _ (pure_color_block Q E U hp hb)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_CommuteTwistSwap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

def commuteTwistSwap (E : BasedComplex Q (K := K) I) (α β : V) :
    CommuteTwistIndex Q E α β ≃ CommuteTwistIndex Q E β α where
  toFun
    | .inl u => .inr (.inl u)
    | .inr (.inl u) => .inl u
    | .inr (.inr i) => .inr (.inr i)
  invFun
    | .inl u => .inr (.inl u)
    | .inr (.inl u) => .inl u
    | .inr (.inr i) => .inr (.inr i)
  left_inv u := by rcases u with u | u | i <;> rfl
  right_inv u := by rcases u with u | u | i <;> rfl

omit [DecidableEq I] in
lemma normalizedCommuteTwist_swap (E : BasedComplex Q (K := K) I)
    {α β : V} (h : OrthogonalVertices Q α β) :
    (normalizedCommuteTwist Q E (h.symm Q)).reindex Q (commuteTwistSwap Q E α β) =
      normalizedCommuteTwist Q E h := by
  apply ext_placement_differential Q
  · change (normalizedCommuteTwist Q E (h.symm Q)).placement ∘ _ = _
    rw [normalizedCommuteTwist_placement, normalizedCommuteTwist_placement]
    funext i
    rcases i with u | u | i <;> rfl
  · change (normalizedCommuteTwist Q E (h.symm Q)).differential.submatrix _ _ = _
    rw [normalizedCommuteTwist_differential, normalizedCommuteTwist_differential]
    apply Matrix.ext
    intro i j
    rcases i with u | u | i <;> rcases j with v | v | j <;> rfl

noncomputable def orthogonal_positiveTwists (E : BasedComplex Q (K := K) I)
    {α β : V} (h : OrthogonalVertices Q α β) :
    HomotopyEquivalence Q ((E.positiveTwist Q β).positiveTwist Q α)
      ((E.positiveTwist Q α).positiveTwist Q β) := by
  classical
  let f := ((E.positiveTwist Q β).positiveTwist Q α).reindexHomotopyEquivalence Q
    (commuteTwistIndexEquiv Q E h)
  let g := ((E.positiveTwist Q α).positiveTwist Q β).reindexHomotopyEquivalence Q
    (commuteTwistIndexEquiv Q E (h.symm Q))
  let k := (normalizedCommuteTwist Q E (h.symm Q)).reindexHomotopyEquivalence Q
    (commuteTwistSwap Q E α β)
  have k' : HomotopyEquivalence Q (normalizedCommuteTwist Q E (h.symm Q))
      (normalizedCommuteTwist Q E h) := by
    rw [← normalizedCommuteTwist_swap Q E h]
    exact k
  exact (f.trans Q (k'.symm Q)).trans Q (g.symm Q)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_FiniteSum2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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

def sumTwistEquiv (E : (i:I) → BasedComplex Q (K := K) (T i)) (α:V) :
    (Σ i, TestIndex Q (E i).placement α ⊕ T i) ≃
      (TestIndex Q (finiteSum Q E).placement α ⊕ Sigma T) where
  toFun
    | ⟨i,.inl ⟨x,p⟩⟩ => .inl ⟨⟨i,x⟩,p⟩
    | ⟨i,.inr x⟩ => .inr ⟨i,x⟩
  invFun
    | .inl ⟨⟨i,x⟩,p⟩ => ⟨i,.inl ⟨x,p⟩⟩
    | .inr ⟨i,x⟩ => ⟨i,.inr x⟩
  left_inv z := by rcases z with ⟨i,⟨x,p⟩|x⟩ <;> rfl
  right_inv z := by rcases z with ⟨⟨i,x⟩,p⟩|⟨i,x⟩ <;> rfl

lemma sumTwist_eq (E : (i:I) → BasedComplex Q (K := K) (T i)) (α:V) :
    ((finiteSum Q E).positiveTwist Q α).reindex Q (sumTwistEquiv Q E α) =
      finiteSum Q (fun i => (E i).positiveTwist Q α) := by
  classical
  apply ext_placement_differential Q
  · funext z
    rcases z with ⟨i,⟨x,p⟩|x⟩ <;> rfl
  · apply Matrix.ext
    rintro ⟨i,x⟩ ⟨j,y⟩
    by_cases hij : i=j
    · subst j
      rcases x with ⟨x,p⟩|x <;> rcases y with ⟨y,q⟩|y
      all_goals dsimp only [reindex,Matrix.submatrix_apply,sumTwistEquiv,Equiv.coe_fn_mk]
      all_goals simp only [finiteSum,positiveTwist_differential,Matrix.blockDiagonal'_apply_eq,
        Matrix.fromBlocks,Matrix.of_apply,Sum.elim_inl,Sum.elim_inr,testTransform,scalarCornerMatrix,testMatrix,
        evaluationMatrix,Matrix.neg_apply,Matrix.zero_apply,Sigma.mk.inj_iff,heq_eq_eq,true_and]
    · have hs (x:T i) (y:T j) : (⟨i,x⟩ : Sigma T) ≠ ⟨j,y⟩ := fun h => hij (congrArg Sigma.fst h)
      rcases x with ⟨x,p⟩|x <;> rcases y with ⟨y,q⟩|y
      all_goals dsimp only [reindex,Matrix.submatrix_apply,sumTwistEquiv,Equiv.coe_fn_mk]
      all_goals simp only [finiteSum,positiveTwist_differential,Matrix.blockDiagonal'_apply_ne _ _ _ hij,
        Matrix.fromBlocks,Matrix.of_apply,Sum.elim_inl,Sum.elim_inr,testTransform,scalarCornerMatrix,testMatrix,
        evaluationMatrix,Matrix.neg_apply,Matrix.zero_apply,ite_eq_right (hs _ _),MulZeroClass.mul_zero,
        coordinates_zero,zero_smul,neg_zero]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_SimpleEdge
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A : Type*} (Q : ReversibleQuiver V A)

namespace SimpleEdge

variable {α β : V} (e : SimpleEdge Q α β)

lemma corner_unique (p : CornerPath Q α β) : p = e.corner Q := by
  rcases p with ⟨v | a | v, hs, ht⟩
  · exact (e.distinct (hs.symm.trans ht)).elim
  · apply Subtype.ext
    change Sum.inr (Sum.inl a) = Sum.inr (Sum.inl e.arrow)
    exact congrArg (fun a => Sum.inr (Sum.inl a)) (e.unique a hs ht)
  · exact (e.distinct (hs.symm.trans ht)).elim

end SimpleEdge
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Coxeter_BraidCoreIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

abbrev BraidCoreIndex (E : BasedComplex Q (K := K) I) (α β : V) :=
  TestIndex Q E.placement β ⊕ TestIndex Q E.placement α ⊕
    TestIndex Q E.placement α ⊕ TestIndex Q E.placement β ⊕ I

abbrev BraidTwistIndex (E : BasedComplex Q (K := K) I) (α β : V) :=
  TestIndex Q E.placement α ⊕ TestIndex Q E.placement α ⊕
    (TestIndex Q E.placement α ⊕ TestIndex Q E.placement α ⊕ BraidCoreIndex Q E α β)

noncomputable instance braidCoreFintype (E : BasedComplex Q (K := K) I) (α β : V) :
    Fintype (BraidCoreIndex Q E α β) := by
  classical
  unfold BraidCoreIndex
  infer_instance

noncomputable instance braidTwistFintype (E : BasedComplex Q (K := K) I) (α β : V) :
    Fintype (BraidTwistIndex Q E α β) := by
  classical
  unfold BraidTwistIndex
  infer_instance

noncomputable def braidTwistIndexEquiv (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β) :
    BraidTwistIndex Q E α β ≃
      (TestIndex Q ((E.positiveTwist Q α).positiveTwist Q β).placement α ⊕
        (TestIndex Q (E.positiveTwist Q α).placement β ⊕ (TestIndex Q E.placement α ⊕ I))) where
  toFun
    | .inl u => .inl ⟨.inr (.inl u), selfCornerEquiv Q hn α false⟩
    | .inr (.inl u) => .inr (.inr (.inl u))
    | .inr (.inr (.inl u)) => .inl ⟨.inl ⟨.inl u, (e.reverse Q).corner Q⟩, e.corner Q⟩
    | .inr (.inr (.inr (.inl u))) => .inl ⟨.inr (.inl u), selfCornerEquiv Q hn α true⟩
    | .inr (.inr (.inr (.inr (.inl u)))) => .inl ⟨.inl ⟨.inr u.1, u.2⟩, e.corner Q⟩
    | .inr (.inr (.inr (.inr (.inr (.inl u))))) => .inr (.inl ⟨.inl u, (e.reverse Q).corner Q⟩)
    | .inr (.inr (.inr (.inr (.inr (.inr (.inl u)))))) => .inl ⟨.inr (.inr u.1), u.2⟩
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl u))))))) => .inr (.inl ⟨.inr u.1, u.2⟩)
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr i))))))) => .inr (.inr (.inr i))
  invFun
    | .inl ⟨.inl ⟨.inl u, _⟩, _⟩ => .inr (.inr (.inl u))
    | .inl ⟨.inl ⟨.inr i, p⟩, _⟩ => .inr (.inr (.inr (.inr (.inl ⟨i, p⟩))))
    | .inl ⟨.inr (.inl u), p⟩ => if (selfCornerEquiv Q hn α).symm p then
        .inr (.inr (.inr (.inl u))) else .inl u
    | .inl ⟨.inr (.inr i), p⟩ => .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨i, p⟩))))))
    | .inr (.inl ⟨.inl u, _⟩) => .inr (.inr (.inr (.inr (.inr (.inl u)))))
    | .inr (.inl ⟨.inr i, p⟩) => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨i, p⟩)))))))
    | .inr (.inr (.inl u)) => .inr (.inl u)
    | .inr (.inr (.inr i)) => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr i)))))))
  left_inv u := by
    rcases u with u | u | u | u | u | u | u | u | i <;> rfl
  right_inv u := by
    rcases u with ⟨⟨u | i, p⟩ | (u | i), q⟩ | (⟨u | i, p⟩ | (u | i))
    · have hp : p = (e.reverse Q).corner Q := (e.reverse Q).corner_unique Q p
      have hq : q = e.corner Q := e.corner_unique Q q
      cases hp
      cases hq
      rfl
    · have hq : q = e.corner Q := e.corner_unique Q q
      cases hq
      rfl
    · have he := (selfCornerEquiv Q hn α).apply_symm_apply q
      cases h : (selfCornerEquiv Q hn α).symm q
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        congr 2
        change (selfCornerEquiv Q hn α false : CornerPath Q α α) = q
        simpa only [h] using he
      · simp only [h, ↓reduceIte]
        congr 2
        change (selfCornerEquiv Q hn α true : CornerPath Q α α) = q
        simpa only [h] using he
    · rfl
    · have hp : p = (e.reverse Q).corner Q := (e.reverse Q).corner_unique Q p
      cases hp
      rfl
    · rfl
    · rfl
    · rfl

noncomputable def normalizedBraidTwist (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β) :
    BasedComplex Q (K := K) (BraidTwistIndex Q E α β) :=
  (((E.positiveTwist Q α).positiveTwist Q β).positiveTwist Q α).reindex Q
    (braidTwistIndexEquiv Q hn E e)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Coxeter_BraidCoreFirstTarget
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma braidCore_to_firstTarget (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β)
    (i : BraidCoreIndex Q E α β) (v : TestIndex Q E.placement α) :
    (normalizedBraidTwist Q hn E e).differential
      (.inr (.inr (.inr (.inr i)))) (.inr (.inl v)) =
      match i with
      | .inr (.inl u) => if u = v then arrowBasis Q (e.reverse Q).arrow else 0
      | _ => 0 := by
  rcases i with u | u | u | u | i
  all_goals simp only [normalizedBraidTwist, reindex, Matrix.submatrix_apply,
    braidTwistIndexEquiv, Equiv.coe_fn_mk, positiveTwist_differential,
    Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
    Matrix.zero_apply, evaluationMatrix, SimpleEdge.corner_val, pathBasis_arrow,
    Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, ↓reduceIte]

lemma braidFirstSource_to_core (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β)
    (u : TestIndex Q E.placement α) (j : BraidCoreIndex Q E α β) :
    (normalizedBraidTwist Q hn E e).differential
      (.inl u) (.inr (.inr (.inr (.inr j)))) =
      match j with
      | .inr (.inr (.inl v)) => -projectiveIdentity Q (testPlacement Q E.placement α) u v
      | _ => 0 := by
  rcases j with v | v | v | v | j
  all_goals simp only [normalizedBraidTwist, reindex, Matrix.submatrix_apply,
    braidTwistIndexEquiv, Equiv.coe_fn_mk, positiveTwist_differential,
    Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
    Matrix.zero_apply, Matrix.neg_apply, testTransform, scalarCornerMatrix, testMatrix,
    evaluationMatrix, selfCornerEquiv_false, pathBasis_vertex,
    Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, ↓reduceIte,
    MulZeroClass.mul_zero, coordinates_zero, zero_smul, neg_zero]
  simp only [projectiveIdentity, Matrix.diagonal_apply, testPlacement]
  apply congrArg Neg.neg
  by_cases hi : u.1 = v.1
  · rcases u with ⟨i, p⟩
    rcases v with ⟨j, q⟩
    dsimp only at hi
    subst j
    simp only [ite_true, if_true, cornerPath_left, pathBasis_coordinates]
    by_cases hp : p = q
    · subst q
      simp
    · have hpq : p.val ≠ q.val := fun h => hp (Subtype.ext h)
      simp [hp, hpq]
  · have huv : u ≠ v := fun h => hi (congrArg Sigma.fst h)
    simp only [ite_eq_right hi, ite_eq_right huv, MulZeroClass.mul_zero, coordinates_zero, zero_smul]

omit [DecidableEq I] in
lemma braidCore_to_secondTarget (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β)
    (i : BraidCoreIndex Q E α β) (v : TestIndex Q E.placement α) :
    (normalizedBraidTwist Q hn E e).differential
      (.inr (.inr (.inr (.inr i)))) (.inr (.inr (.inr (.inl v)))) = 0 := by
  rcases i with u | u | u | u | i
  all_goals simp only [normalizedBraidTwist, reindex, Matrix.submatrix_apply,
    braidTwistIndexEquiv, Equiv.coe_fn_mk, positiveTwist_differential,
    Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
    Matrix.zero_apply, Matrix.neg_apply, testTransform, scalarCornerMatrix, testMatrix,
    evaluationMatrix, Sum.inr_ne_inl, ↓reduceIte,
    MulZeroClass.mul_zero, coordinates_zero, zero_smul, neg_zero]

omit [DecidableEq I] in
lemma braidFirstSource_to_secondTarget (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β)
    (u v : TestIndex Q E.placement α) :
    (normalizedBraidTwist Q hn E e).differential
      (.inl u) (.inr (.inr (.inr (.inl v)))) = 0 := by
  simp only [normalizedBraidTwist, reindex, Matrix.submatrix_apply,
    braidTwistIndexEquiv, Equiv.coe_fn_mk, positiveTwist_differential,
    Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
    Matrix.neg_apply, testTransform, scalarCornerMatrix, testMatrix,
    selfCornerEquiv_false, selfCornerEquiv_true, pathBasis_vertex]
  simp only [_root_.mul_neg, mul_smul, vertexId_mul_self]
  simp only [map_neg, Pi.neg_apply, coordinates_smul]
  have hz : pathCoordinates Q (vertexId Q (K := K) α) (.inr (.inr α)) = 0 := by
    rw [← pathBasis_vertex, pathBasis_coordinates]
    rfl
  simp only [hz, MulZeroClass.mul_zero, neg_zero, zero_smul]

omit [DecidableEq I] in
lemma braidSecondSource_to_firstTarget (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β)
    (u v : TestIndex Q E.placement α) :
    (normalizedBraidTwist Q hn E e).differential
      (.inr (.inr (.inl u))) (.inr (.inl v)) = 0 := by
  simp only [normalizedBraidTwist, reindex, Matrix.submatrix_apply,
    braidTwistIndexEquiv, Equiv.coe_fn_mk, positiveTwist_differential,
    Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
    evaluationMatrix, Sum.inl_ne_inr, ↓reduceIte]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Coxeter_BraidFirstPivot
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

noncomputable def braidFirstPivot (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β) :
    BlockPivot Q (normalizedBraidTwist Q hn E e) where
  coefficient := 1
  nonzero := one_ne_zero
  color _ := rfl
  cochain u := by
    change (E.placement u.1).cochain - 1 = (E.placement u.1).cochain - 1 - 1 + 1
    omega
  internal u := by
    change (E.placement u.1).internal + Path.length u.2.val =
      (E.placement u.1).internal + Path.length u.2.val + 0
    omega
  entry u v := by
    simp only [normalizedBraidTwist, reindex, Matrix.submatrix_apply,
      braidTwistIndexEquiv, Equiv.coe_fn_mk, positiveTwist_differential,
      Matrix.fromBlocks, Matrix.of_apply, evaluationMatrix, selfCornerEquiv_false,
      pathBasis_vertex, Sum.inr.injEq, Sum.inl.injEq, Sum.elim_inl, Sum.elim_inr,
      one_smul, projectiveIdentity, Matrix.diagonal_apply]
    refine @ite_cond_congr _ _ _ ?_ ?_ _ _ rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_EdgeContraction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

noncomputable def edgeContraction (p : I → GeneratorPlacement V)
    {α β : V} (e : SimpleEdge Q α β) :
    Matrix (TestIndex Q p β) (TestIndex Q p α) K :=
  fun u v => if u.1 = v.1 then
    pathCoordinates Q (arrowBasis Q e.arrow * pathBasis Q u.2.val) v.2.val else 0

namespace BasedComplex

noncomputable def braidCoreDifferential (E : BasedComplex Q (K := K) I)
    {α β : V} (e : SimpleEdge Q α β) :
    Matrix (BraidCoreIndex Q E α β) (BraidCoreIndex Q E α β) (Q.Zigzag K)
  | .inl u, .inl v => scalarCornerMatrix Q α (testMatrix Q E.placement E.placement β E.differential) u v
  | .inr (.inl u), .inr (.inl v) => scalarCornerMatrix Q β (testMatrix Q E.placement E.placement α E.differential) u v
  | .inr (.inr (.inl u)), .inr (.inr (.inl v)) => -testTransform Q E.placement E.placement α E.differential u v
  | .inr (.inr (.inr (.inl u))), .inr (.inr (.inr (.inl v))) => -testTransform Q E.placement E.placement β E.differential u v
  | .inl u, .inr (.inr (.inl v)) => -scalarCornerMatrix Q α (edgeContraction Q E.placement e) u v
  | .inl u, .inr (.inr (.inr (.inl v))) => if u = v then arrowBasis Q e.arrow else 0
  | .inr (.inl u), .inr (.inr (.inl v)) => if u = v then arrowBasis Q (e.reverse Q).arrow else 0
  | .inr (.inl u), .inr (.inr (.inr (.inl v))) => -scalarCornerMatrix Q β (edgeContraction Q E.placement (e.reverse Q)) u v
  | .inr (.inr (.inl u)), .inr (.inr (.inr (.inr j))) => evaluationMatrix Q E.placement α u j
  | .inr (.inr (.inr (.inl u))), .inr (.inr (.inr (.inr j))) => evaluationMatrix Q E.placement β u j
  | .inr (.inr (.inr (.inr i))), .inr (.inr (.inr (.inr j))) => E.differential i j
  | _, _ => 0

noncomputable def braidRawCoreDifferential (E : BasedComplex Q (K := K) I)
    {α β : V} (e : SimpleEdge Q α β) :
    Matrix (BraidCoreIndex Q E α β) (BraidCoreIndex Q E α β) (Q.Zigzag K)
  | .inr (.inl _), .inr (.inr (.inl _)) => 0
  | i, j => braidCoreDifferential Q E e i j

lemma arrowBasis_right_vertex (a : A) :
    arrowBasis Q (K := K) a * vertexId Q (Q.target a) = arrowBasis Q a := by
  simpa only [Path.target, pathBasis_arrow] using
    pathBasis_right Q (K := K) (.inr (.inl a))

lemma arrowBasis_coordinates_self (a : A) :
    pathCoordinates Q (arrowBasis Q (K := K) a) (.inr (.inl a)) = 1 := by
  rw [← pathBasis_arrow, pathBasis_coordinates, ite_eq_left rfl]

lemma simpleEdge_arrow_right {α β : V} (e : SimpleEdge Q α β) :
    arrowBasis Q (K := K) e.arrow * vertexId Q β = arrowBasis Q e.arrow := by
  simpa only [e.target] using arrowBasis_right_vertex Q (K := K) e.arrow

lemma normalizedBraidTwist_core (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β)
    (i j : BraidCoreIndex Q E α β) :
    (normalizedBraidTwist Q hn E e).differential
      (.inr (.inr (.inr (.inr i)))) (.inr (.inr (.inr (.inr j)))) =
      braidRawCoreDifferential Q E e i j := by
  rcases i with u | u | u | u | i <;> rcases j with v | v | v | v | j
  all_goals simp only [normalizedBraidTwist, reindex, Matrix.submatrix_apply,
    braidTwistIndexEquiv, Equiv.coe_fn_mk, positiveTwist_differential,
    Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
    Matrix.zero_apply, Matrix.neg_apply, testTransform, scalarCornerMatrix, testMatrix,
    braidRawCoreDifferential, braidCoreDifferential,
    MulZeroClass.mul_zero, coordinates_zero, zero_smul, neg_zero,
    SimpleEdge.corner_val, pathBasis_arrow]
  all_goals try simp only [_root_.mul_neg, mul_smul, map_neg, Pi.neg_apply,
    coordinates_smul, neg_smul, neg_neg, simpleEdge_arrow_right Q e,
    simpleEdge_arrow_right Q (e.reverse Q),
    arrowBasis_coordinates_self, _root_.mul_one]
  all_goals try simp only [evaluationMatrix, edgeContraction,
    Sum.inr.injEq, Sum.inl.injEq, Sum.inr_ne_inl, Sum.inl_ne_inr, ↓reduceIte,
    SimpleEdge.corner_val, pathBasis_arrow]
  all_goals try (refine @ite_cond_congr _ _ _ ?_ ?_ _ _ rfl)
  · split_ifs with h
    · have hx := congrArg (fun x : TestIndex Q (E.positiveTwist Q α).placement β => x.1) h
      cases hx
    · rfl
  · split_ifs <;> simp only [MulZeroClass.mul_zero, coordinates_zero]
  · rcases u with ⟨i, p⟩
    rcases v with ⟨j, q⟩
    refine @ite_cond_congr _ _ _ ?_ ?_ _ _ ?_
    apply propext
    constructor
    · intro h
      have hi := congrArg (fun x : TestIndex Q (E.positiveTwist Q α).placement β => x.1) h
      have hij : i = j := Sum.inr.inj hi
      subst j
      have hpq : p = q := by cases h; rfl
      cases hpq
      rfl
    · intro h
      cases h
      rfl
  · split_ifs <;> simp only [MulZeroClass.mul_zero, coordinates_zero]

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Coxeter_BraidSecondPivot
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

noncomputable instance braidCoreDecidable (E : BasedComplex Q (K := K) I) (α β : V) :
    DecidableEq (BraidCoreIndex Q E α β) := Classical.decEq _

noncomputable instance braidFirstReducedDecidable (E : BasedComplex Q (K := K) I) (α β : V) :
    DecidableEq (TestIndex Q E.placement α ⊕ TestIndex Q E.placement α ⊕
      BraidCoreIndex Q E α β) := fun a b => instDecidableEqSum a b

lemma braidFirstReduction_core (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β)
    (i j : BraidCoreIndex Q E α β) :
    ((braidFirstPivot Q hn E e).reduced Q).differential
      (.inr (.inr i)) (.inr (.inr j)) = braidCoreDifferential Q E e i j := by
  rw [BlockPivot.reduced_differential, normalizedBraidTwist_core]
  simp only [braidFirstPivot, inv_one, one_smul, braidCore_to_firstTarget,
    braidFirstSource_to_core]
  rcases i with u | u | u | u | i <;> rcases j with v | v | v | v | j
  all_goals simp only [braidRawCoreDifferential, braidCoreDifferential,
    MulZeroClass.zero_mul, MulZeroClass.mul_zero, Finset.sum_const_zero, sub_zero]
  simp only [ite_mul, MulZeroClass.zero_mul,
    projectiveIdentity, Matrix.diagonal_apply, testPlacement, _root_.mul_neg,
    mul_ite, MulZeroClass.mul_zero, zero_sub]
  rw [simpleEdge_arrow_right Q (e.reverse Q)]
  simp

omit [DecidableEq I] in
lemma braidFirstReduction_core_to_secondTarget (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β)
    (i : BraidCoreIndex Q E α β) (v : TestIndex Q E.placement α) :
    ((braidFirstPivot Q hn E e).reduced Q).differential
      (.inr (.inr i)) (.inr (.inl v)) = 0 := by
  rw [BlockPivot.reduced_differential, braidCore_to_secondTarget]
  simp only [braidFirstSource_to_secondTarget, MulZeroClass.mul_zero,
    Finset.sum_const_zero, sub_zero]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Coxeter_BraidCorePlacement
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

def braidCorePlacement (E : BasedComplex Q (K := K) I) (α β : V) :
    BraidCoreIndex Q E α β → GeneratorPlacement V
  | .inl u => ⟨α, (E.placement u.1).cochain - 2,
      (E.placement u.1).internal + Path.length u.2.val + 1⟩
  | .inr (.inl u) => ⟨β, (E.placement u.1).cochain - 2,
      (E.placement u.1).internal + Path.length u.2.val + 1⟩
  | .inr (.inr (.inl u)) => ⟨α, (E.placement u.1).cochain - 1,
      (E.placement u.1).internal + Path.length u.2.val⟩
  | .inr (.inr (.inr (.inl u))) => ⟨β, (E.placement u.1).cochain - 1,
      (E.placement u.1).internal + Path.length u.2.val⟩
  | .inr (.inr (.inr (.inr i))) => E.placement i

def braidCoreSwap (E : BasedComplex Q (K := K) I) (α β : V) :
    BraidCoreIndex Q E α β ≃ BraidCoreIndex Q E β α where
  toFun
    | .inl u => .inr (.inl u)
    | .inr (.inl u) => .inl u
    | .inr (.inr (.inl u)) => .inr (.inr (.inr (.inl u)))
    | .inr (.inr (.inr (.inl u))) => .inr (.inr (.inl u))
    | .inr (.inr (.inr (.inr i))) => .inr (.inr (.inr (.inr i)))
  invFun
    | .inl u => .inr (.inl u)
    | .inr (.inl u) => .inl u
    | .inr (.inr (.inl u)) => .inr (.inr (.inr (.inl u)))
    | .inr (.inr (.inr (.inl u))) => .inr (.inr (.inl u))
    | .inr (.inr (.inr (.inr i))) => .inr (.inr (.inr (.inr i)))
  left_inv u := by rcases u with u | u | u | u | i <;> rfl
  right_inv u := by rcases u with u | u | u | u | i <;> rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomDimension2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def classHomDimension (n v : ℤ) :
    FiniteHomotopyClass Q (K := K) → FiniteHomotopyClass Q (K := K) → ℕ :=
  Quotient.lift₂ (fun E F => homDimension Q E.complex F.complex n v)
    (by
      intro E E' F F' ⟨e⟩ ⟨f⟩
      exact e.homDimension_eq Q f n v)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_InitialProjective
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [DecidableEq A] in
lemma homDimension_le_homSpace {I J : Type*} [Fintype I] [Fintype J]
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    homDimension Q E F n v ≤ Module.finrank K (homSpace Q E F n v) := by
  apply le_trans (Submodule.finrank_quotient_le _)
  exact Submodule.finrank_mono inf_le_left

lemma initial_self_entry_decomposition (hn : ∀ a, Q.source a ≠ Q.target a)
    (α : V) (n v : ℤ)
    {f : Matrix PUnit PUnit (Q.Zigzag K)}
    (hf : f ∈ homSpace Q (initialProjective Q α) (initialProjective Q α) n v)
    (i j : PUnit) :
    f i j = (f i j).vertex α • vertexId Q α + (f i j).token α • tokenBasis Q α :=
  diagonal_corner_decomposition Q hn α (f i j) (hf.1.1 i j) (hf.1.2 i j)

omit [Fintype V] [DecidableEq A] in
lemma initial_self_entry_homogeneous (α : V) (n v : ℤ)
    {f : Matrix PUnit PUnit (Q.Zigzag K)}
    (hf : f ∈ homSpace Q (initialProjective Q α) (initialProjective Q α) n v)
    (i j : PUnit) : Homogeneous Q v (f i j) := by
  simpa only [initialProjective, add_zero, sub_zero] using (hf.2 i j).2

noncomputable def initialCoordinate (α : V) (n v : ℤ) :
    homSpace Q (initialProjective Q (K := K) α) (initialProjective Q α) n v →ₗ[K] K where
  toFun f := if v = 0 then (f.val PUnit.unit PUnit.unit).vertex α
    else (f.val PUnit.unit PUnit.unit).token α
  map_add' f g := by split_ifs <;> rfl
  map_smul' r f := by split_ifs <;> rfl

lemma initialCoordinate_injective (hn : ∀ a, Q.source a ≠ Q.target a)
    (α : V) (n v : ℤ) : Function.Injective (initialCoordinate Q (K := K) α n v) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro f hf
  change (initialCoordinate Q α n v) f = 0 at hf
  change f = 0
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  have hi : i = PUnit.unit := Subsingleton.elim _ _
  have hj : j = PUnit.unit := Subsingleton.elim _ _
  subst i
  subst j
  rw [initial_self_entry_decomposition Q hn α n v f.property PUnit.unit PUnit.unit]
  have hh := initial_self_entry_homogeneous Q α n v f.property PUnit.unit PUnit.unit
  by_cases hv : v = 0
  · have hzero : (f.val PUnit.unit PUnit.unit).vertex α = 0 := by
      simpa only [initialCoordinate, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_left hv] using hf
    rw [hzero, hh.2.2 (by omega)]
    simp only [Pi.zero_apply, zero_smul, add_zero]
    rfl
  · have hzero : (f.val PUnit.unit PUnit.unit).token α = 0 := by
      simpa only [initialCoordinate, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_right hv] using hf
    rw [hzero, hh.1 hv]
    simp only [Pi.zero_apply, zero_smul, add_zero]
    rfl

lemma initial_homDimension_le_one (hn : ∀ a, Q.source a ≠ Q.target a)
    (α : V) (n v : ℤ) :
    homDimension Q (initialProjective Q (K := K) α) (initialProjective Q α) n v ≤ 1 := by
  apply le_trans (homDimension_le_homSpace Q _ _ n v)
  simpa only [Module.finrank_self] using LinearMap.finrank_le_finrank_of_injective
    (initialCoordinate_injective Q (K := K) hn α n v)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_IsolatedIndexCycle
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I:Type*} (Q:ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] [Fintype I] [DecidableEq I]

lemma isolated_index_cycle (E:BasedComplex Q (K:=K) I) (i:I)
    (hr:∀j,E.differential i j=0) (hc:∀j,E.differential j i=0) :
    Matrix.single i i (vertexId Q (K:=K) (E.placement i).color)∈homCycles Q E E 0 0 := by
  let f:=Matrix.single i i (vertexId Q (K:=K) (E.placement i).color)
  have h₁:E.differential*f=0 := by
    apply Matrix.ext; intro j k
    change (∑l,E.differential j l*f l k)=0
    apply Finset.sum_eq_zero
    intro l hl
    by_cases hli:i=l
    · subst l
      rw [hc,zero_mul]
    · simp [f,hli]
  have h₂:f*E.differential=0 := by
    apply Matrix.ext; intro j k
    change (∑l,f j l*E.differential l k)=0
    apply Finset.sum_eq_zero
    intro l hl
    by_cases hli:i=l
    · subst l
      rw [hr,mul_zero]
    · simp [f,hli]
  refine ⟨⟨?_,?_⟩,?_⟩
  · apply projectiveEntries_single Q
    · exact vertexId_mul_self Q _
    · exact vertexId_mul_self Q _
  · apply mapDegree_single Q _ _ _ _ _ 0 0 (by omega)
    simpa only [zero_add,sub_self,Path.length,pathBasis_vertex] using pathBasis_homogeneous Q (K:=K) (Sum.inl (E.placement i).color)
  · change E.differential*f-cochainSign (K:=K) 0 • (f*E.differential)=0
    rw [h₁,h₂,smul_zero,sub_zero]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_VertexMinimal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J L : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

namespace BasedComplex

variable [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

variable [Fintype V] [DecidableEq A]

omit [Fintype J] [DecidableEq J] [DecidableEq I] in
lemma positiveTwist_vertexMinimal (E : BasedComplex Q (K := K) I)
    (hE : E.IsMinimal Q) (α β : V) (hαβ : α ≠ β) :
    VertexMinimal Q (E.positiveTwist Q α) β := by
  intro i j
  rcases i with i | i
  · exact vertexEntries_zero_left Q (E.positiveTwist Q α).entries (.inl i) j hαβ
  · rcases j with j | j
    · exact vertexEntries_zero_right Q (E.positiveTwist Q α).entries (.inr i) (.inl j) hαβ
    · change (E.differential i j).vertex β = 0
      rw [hE i j]
      rfl

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PositiveTwistFiberEquiv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

noncomputable def positiveTwistFiberEquiv (E : BasedComplex Q (K := K) I)
    (α : V) (a : GeneratorPlacement V) (hα : α ≠ a.color) :
    {i // E.placement i = a} ≃ {i // (E.positiveTwist Q α).placement i = a} :=
  Equiv.ofBijective (fun i => ⟨Sum.inr i.val, i.property⟩) (by
    constructor
    · intro i j h
      exact Subtype.ext (Sum.inr.inj (congrArg Subtype.val h))
    · intro i
      rcases i with ⟨i | i, hi⟩
      · exact (hα (congrArg GeneratorPlacement.color hi)).elim
      · exact ⟨⟨i, hi⟩, rfl⟩)

theorem positiveTwist_exterior_multiplicity (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (α : V) (e : HomotopyEquivalence Q (E.positiveTwist Q α) F)
    (a : GeneratorPlacement V) (hα : α ≠ a.color) :
    F.multiplicity Q a = E.multiplicity Q a := by
  calc
    F.multiplicity Q a = (E.positiveTwist Q α).multiplicity Q a :=
      (multiplicity_eq_of_vertex_homotopyEquivalence Q _ _ e a
        (positiveTwist_vertexMinimal Q E hE α a.color hα)
        (fun i j => congrFun (hF i j) a.color)).symm
    _ = E.multiplicity Q a := Nat.card_congr (positiveTwistFiberEquiv Q E α a hα).symm

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_Refl
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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

noncomputable def ChainIsomorphism.trans {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} {G : BasedComplex Q (K := K) L}
    (a : ChainIsomorphism Q E F) (b : ChainIsomorphism Q F G) :
    ChainIsomorphism Q E G where
  forward := Map.comp Q a.forward b.forward
  backward := Map.comp Q b.backward a.backward
  sourceEquation := by
    change (a.forward.matrix*b.forward.matrix)*(b.backward.matrix*a.backward.matrix)=_
    calc
      _ = a.forward.matrix*(b.forward.matrix*b.backward.matrix)*a.backward.matrix := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [b.sourceEquation]
        exact (congrArg (fun z => z*a.backward.matrix)
          (mul_projectiveIdentity Q a.forward.entries)).trans a.sourceEquation
  targetEquation := by
    change (b.backward.matrix*a.backward.matrix)*(a.forward.matrix*b.forward.matrix)=_
    calc
      _ = b.backward.matrix*(a.backward.matrix*a.forward.matrix)*b.forward.matrix := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [a.targetEquation]
        exact (congrArg (fun z => z*b.forward.matrix)
          (mul_projectiveIdentity Q b.backward.entries)).trans b.targetEquation

noncomputable def ChainIsomorphism.toHomotopyEquivalence {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (a : ChainIsomorphism Q E F) :
    HomotopyEquivalence Q E F where
  forward := a.forward
  backward := a.backward
  sourceHomotopy := 0
  targetHomotopy := 0
  sourceEntries := projectiveEntries_zero Q
  targetEntries := projectiveEntries_zero Q
  sourceDegree := mapDegree_zero Q (-1) 0
  targetDegree := mapDegree_zero Q (-1) 0
  sourceEquation := by simpa only [Matrix.mul_zero,Matrix.zero_mul,add_zero] using a.sourceEquation
  targetEquation := by simpa only [Matrix.mul_zero,Matrix.zero_mul,add_zero] using a.targetEquation

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_SumTestEquiv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]
  {T : I → Type*} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]

omit [Fintype V] [DecidableEq A] [∀ i, DecidableEq (T i)] in
lemma finiteSum_minimal (E : (i:I) → BasedComplex Q (K := K) (T i))
    (hE : ∀ i, (E i).IsMinimal Q) : (finiteSum Q E).IsMinimal Q := by
  rintro ⟨i,x⟩ ⟨j,y⟩
  change (Matrix.blockDiagonal' (fun i => (E i).differential) ⟨i,x⟩ ⟨j,y⟩).vertex=0
  by_cases h : i=j
  · subst j; rw [Matrix.blockDiagonal'_apply_eq]; exact hE i x y
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]; rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_LevelArrayComplexMinimal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  {I : Type u} [Fintype I] [DecidableEq I]

lemma finiteSum_levelArray {T : I → Type u} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
    (E : (i:I) → BasedComplex Q (K := K) (T i)) :
    (finiteSum Q E).levelArray Q = ∑ i, (E i).levelArray Q := by
  classical
  simp only [levelArray_eq_sum,Fintype.sum_sigma]
  rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_MinimalGeneratorDualCycle
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem minimal_generator_dual_cycle
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (hF : F.IsMinimal Q) (e : HomotopyEquivalence Q E F) (j : J) :
    ∃ x : I → K, x ≠ 0 ∧
      (∀ i, E.placement i ≠ F.placement j → x i = 0) ∧
      ∀ k, ∑ i, (E.differential k i).vertex (F.placement j).color * x i = 0 := by
  have hf0 i k w : (F.differential i k).vertex w = 0 := congrFun (hF i k) w
  let x : I → K := fun i => (e.forward.matrix i j).vertex (F.placement j).color
  refine ⟨x, ?_, ?_, ?_⟩
  · intro hx
    have he := congrArg (fun M : Matrix J J (Q.Zigzag K) =>
      (M j j).vertex (F.placement j).color) e.targetEquation
    have hz i : (e.forward.matrix i j).vertex (F.placement j).color = 0 :=
      congrFun hx i
    simp only [Matrix.mul_apply, Matrix.add_apply, vertex_add, Pi.add_apply, vertex_sum,
      Finset.sum_apply, vertex_mul, Pi.mul_apply, hf0, hz,
      MulZeroClass.zero_mul, MulZeroClass.mul_zero, Finset.sum_const_zero,
      add_zero] at he
    simp [projectiveIdentity] at he
  · intro i hi
    by_contra hn
    exact hi ((reduction_support Q e.forward.entries e.forward.degree i j
      (F.placement j).color hn).1)
  · intro k
    have he := congrArg (fun M : Matrix I J (Q.Zigzag K) =>
      (M k j).vertex (F.placement j).color) e.forward.commute
    simpa only [Matrix.mul_apply, vertex_sum, Finset.sum_apply, vertex_mul,
      Pi.mul_apply, hf0, Pi.zero_apply, MulZeroClass.mul_zero,
      Finset.sum_const_zero] using he

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_OptionSumEquiv
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
open Zigzag

universe u
attribute [local instance] Classical.decEq
variable {V A : Type u} {K : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  (hn:∀ a,Q.source a≠Q.target a)

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] in
lemma packet_orthogonal_inl {J L:Type u} (v:J ⊕ L → V)
    (hv:Pairwise fun a b => OrthogonalVertices Q (v a) (v b)) :
    Pairwise fun a b => OrthogonalVertices Q ((v ∘ Sum.inl) a) ((v ∘ Sum.inl) b) :=
  fun _ _ h=>hv (fun hh=>h (Sum.inl.inj hh))

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] in
lemma packet_orthogonal_inr {J L:Type u} (v:J ⊕ L → V)
    (hv:Pairwise fun a b => OrthogonalVertices Q (v a) (v b)) :
    Pairwise fun a b => OrthogonalVertices Q ((v ∘ Sum.inr) a) ((v ∘ Sum.inr) b) :=
  fun _ _ h=>hv (fun hh=>h (Sum.inr.inj hh))

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] in
lemma packet_orthogonal_fiber {J L:Type u} (v:J × L → V)
    (hv:Pairwise fun a b => OrthogonalVertices Q (v a) (v b)) (j:J) :
    Pairwise fun a b => OrthogonalVertices Q (v (j,a)) (v (j,b)) :=
  fun _ _ h=>hv (fun hh=>h (congrArg Prod.snd hh))

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PlacementSignedWeight
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_ScalarSupported
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.instAlgebra
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.dual_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.source_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.target_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_false _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_true
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_Test
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_TestExact
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

def ClassTestExact (α:V) (l c:ℤ) : FiniteHomotopyClass Q (K:=K)→Prop :=
  Quotient.lift (fun E=>ScalarExactAt Q (E.complex.testComplex Q α) α l c) (by
    intro E F h
    obtain ⟨e⟩:=h
    apply propext
    constructor
    · exact fun h=>scalarExact_transport Q _ _ ((e.symm Q).test Q α) α (fun _=>rfl) h
    · exact fun h=>scalarExact_transport Q _ _ (e.test Q α) α (fun _=>rfl) h)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Coxeter_PositiveBraidRel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

variable {K:Type*} [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def positiveWordAction : List V→FiniteHomotopyClass Q (K:=K)→FiniteHomotopyClass Q (K:=K)
  | [],x=>x
  | α::w,x=>classPositiveTwist Q α (positiveWordAction w x)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_PositiveWordActionAppend
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
  (hn:∀ a,Q.source a≠Q.target a)

lemma positiveWordAction_append (w z:List V) (x:FiniteHomotopyClass Q (K:=K)) :
    positiveWordAction Q (w++z) x=positiveWordAction Q w (positiveWordAction Q z x) := by
  induction w with
  | nil => rfl
  | cons a w ih => exact congrArg (classPositiveTwist Q a) ih

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_UpperBound
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
  {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def ClassUpperBound (l:ℤ) (x:FiniteHomotopyClass Q (K:=K)) : Prop :=
  ∀ i, ((minimalClassModel Q x).complex.placement i).level≤l

def ClassLowerBound (l:ℤ) (x:FiniteHomotopyClass Q (K:=K)) : Prop :=
  ∀ i, l≤((minimalClassModel Q x).complex.placement i).level

omit [Fintype V] [DecidableEq A] in
lemma minimal_bound_transport (E:BasedComplex Q (K:=K) I)
    (F:BasedComplex Q (K:=K) J) (hF:F.IsMinimal Q)
    (e:HomotopyEquivalence Q E F) (P:GeneratorPlacement V→Prop)
    (h:∀ i,P (E.placement i)) : ∀ j,P (F.placement j) := by
  intro j
  obtain ⟨x,hx,hs,_⟩ := minimal_generator_dual_cycle Q E F hF e j
  have hex : ∃ i,x i≠0 := not_forall.mp (fun hh=>hx (funext hh))
  obtain ⟨i,hi⟩:=hex
  have hp:E.placement i=F.placement j := Classical.not_not.mp (fun hn=>hi (hs i hn))
  rw [← hp]
  exact h i

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Coxeter_OrdinaryCoxeterMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} (Q:ReversibleQuiver V A)

noncomputable def ordinaryCoxeterMatrix : CoxeterMatrix V := by
  classical
  refine { M := fun α β => if α=β then 1 else if OrthogonalVertices Q α β then 2
      else if Nonempty (SimpleEdge Q α β) then 3 else 0
           isSymm := ?_, diagonal := ?_, off_diagonal := ?_ }
  · apply Matrix.ext
    intro α β
    have ho:OrthogonalVertices Q α β↔OrthogonalVertices Q β α :=
      ⟨OrthogonalVertices.symm Q,OrthogonalVertices.symm Q⟩
    have he:Nonempty (SimpleEdge Q α β)↔Nonempty (SimpleEdge Q β α) :=
      ⟨fun ⟨e⟩=>⟨e.reverse Q⟩,fun ⟨e⟩=>⟨e.reverse Q⟩⟩
    change (if β=α then 1 else if OrthogonalVertices Q β α then 2
      else if Nonempty (SimpleEdge Q β α) then 3 else 0) =
      (if α=β then 1 else if OrthogonalVertices Q α β then 2
      else if Nonempty (SimpleEdge Q α β) then 3 else 0)
    simp only [eq_comm (a:=α) (b:=β),ho,he]
  · intro α; simp
  · intro α β h
    simp only [h,ite_false, if_false]
    split
    · norm_num
    · split <;> norm_num

lemma ordinaryCoxeterMatrix_orthogonal {α β:V} (h:OrthogonalVertices Q α β) :
    ordinaryCoxeterMatrix Q α β=2 := by
  classical
  simp [ordinaryCoxeterMatrix,h.1,h]

lemma ordinaryCoxeterMatrix_adjacent {α β:V} (e:SimpleEdge Q α β) :
    ordinaryCoxeterMatrix Q α β=3 := by
  classical
  have ho:¬OrthogonalVertices Q α β:=fun h=>h.2 e.arrow e.source e.target
  simp [ordinaryCoxeterMatrix,e.distinct,ho,show Nonempty (SimpleEdge Q α β) from ⟨e⟩]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_TotalVector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
open _root_.Matrix
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma signedGeneratorVector_pure {I : Type u} [Fintype I]
    (E : BasedComplex Q (K:=K) I) (q : ℤ) (hE : ∀ i,(E.placement i).level=q) :
    signedGeneratorVector Q E=cochainSign (K:=ℝ) q • generatorVector Q E := by
  funext v
  simp only [signedGeneratorVector,placementSignedWeight,hE,generatorVector_sum,
    Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_Path
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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

variable [Fintype V] [Fintype W] [DecidableEq A] [DecidableEq B]
lemma path_basis (p:Path V A) :
    e.zigzagLinear (pathBasis Q (K := K) p) = pathBasis R (e.path p) := by
  apply (pathCoordinates R).injective
  funext q
  obtain ⟨q,rfl⟩ := e.path.surjective q
  rw [e.path_coordinates,pathBasis_coordinates,pathBasis_coordinates]
  simp only [e.path.injective.eq_iff]

end HarmonicArtin.ReversibleQuiver.Iso

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_TestIndex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Iso
open Zigzag Zigzag.BasedComplex

variable {V A W B K : Type*} {Q : ReversibleQuiver V A} {R : ReversibleQuiver W B}
  (e : Iso Q R) [Field K] [Fintype V] [Fintype W] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq W] [DecidableEq A] [DecidableEq B]
  {I J : Type*}

def testIndex (p : I → GeneratorPlacement V) (α:V) :
    TestIndex Q p α ≃ TestIndex R (e.placement ∘ p) (e.vertex α) :=
  Equiv.sigmaCongrRight fun i => e.cornerPath α (p i).color

lemma test_matrix (p:I → GeneratorPlacement V) (q:J → GeneratorPlacement V) (α:V)
    (M:Matrix I J (Q.Zigzag K)) (i:TestIndex Q p α) (j:TestIndex Q q α) :
    testMatrix R (e.placement ∘ p) (e.placement ∘ q) (e.vertex α) (e.matrix M)
      (e.testIndex p α i) (e.testIndex q α j) = testMatrix Q p q α M i j := by
  change pathCoordinates R (pathBasis R (e.path i.2.val) * e.zigzagLinear (M i.1 j.1))
    (e.path j.2.val) = _
  rw [← e.path_basis,← e.zigzagLinear_mul,e.path_coordinates]
  rfl

lemma test_transform (p:I → GeneratorPlacement V) (q:J → GeneratorPlacement V) (α:V)
    (M:Matrix I J (Q.Zigzag K)) (i:TestIndex Q p α) (j:TestIndex Q q α) :
    testTransform R (e.placement ∘ p) (e.placement ∘ q) (e.vertex α) (e.matrix M)
      (e.testIndex p α i) (e.testIndex q α j) =
      e.zigzagLinear (testTransform Q p q α M i j) := by
  unfold testTransform scalarCornerMatrix
  rw [e.test_matrix,← e.zigzag_vertexId,map_smul]

lemma evaluation_matrix (p:I → GeneratorPlacement V) (α:V)
    (i:TestIndex Q p α) (j:I) :
    evaluationMatrix R (e.placement ∘ p) (e.vertex α) (K := K) (e.testIndex p α i) j =
      e.zigzagLinear (evaluationMatrix Q p α i j) := by
  classical
  change (if i.1=j then pathBasis R (e.path i.2.val) else 0) = _
  unfold evaluationMatrix
  split_ifs
  · exact (e.path_basis i.2.val).symm
  · exact (map_zero e.zigzagLinear).symm

variable [Fintype I]

lemma positiveTwist_transport (E:BasedComplex Q (K := K) I) (α:V) :
    ((e.complex E).positiveTwist R (e.vertex α)).reindex R
      ((e.testIndex E.placement α).sumCongr (Equiv.refl I)) =
      e.complex (E.positiveTwist Q α) := by
  apply ext_placement_differential R
  · funext i
    rcases i with i|i
    · change GeneratorPlacement.mk _ _ (_ + Path.length (e.path i.2.val)) = _
      rw [e.path_length]
      rfl
    · rfl
  · apply Matrix.ext
    intro i j
    rcases i with i|i <;> rcases j with j|j
    · change -(testTransform R (e.placement ∘ E.placement) (e.placement ∘ E.placement)
          (e.vertex α) (e.matrix E.differential) (e.testIndex E.placement α i)
          (e.testIndex E.placement α j)) = e.zigzagLinear (-testTransform Q _ _ _ _ i j)
      rw [e.test_transform,map_neg]
    · exact e.evaluation_matrix E.placement α i j
    · exact (map_zero e.zigzagLinear).symm
    · rfl

end HarmonicArtin.ReversibleQuiver.Iso

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_ReversibleQuiverMap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Iso
open Zigzag Zigzag.BasedComplex

universe u
variable {V A W B : Type u} {K : Type*} {Q : ReversibleQuiver V A} {R : ReversibleQuiver W B}
  (e : Iso Q R) [Field K] [Fintype V] [Fintype W] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq W] [DecidableEq A] [DecidableEq B]
  {I : Type u} [Fintype I] [DecidableEq I]

lemma classMap_positiveTwist (α:V) (x:FiniteHomotopyClass Q (K := K)) :
    e.classMap (classPositiveTwist Q α x) = classPositiveTwist R (e.vertex α) (e.classMap x) := by
  induction x using Quotient.inductionOn with | _ E =>
    change classOfComplex R (e.complex (E.complex.positiveTwist Q α)) =
      classOfComplex R ((e.complex E.complex).positiveTwist R (e.vertex α))
    rw [← e.positiveTwist_transport]
    exact (classOfComplex_reindex R _ _).symm

omit [Fintype V] [Fintype W] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq W] [DecidableEq A] [DecidableEq B] in
lemma loopless (e : Iso Q R) (hn:∀ a,Q.source a ≠ Q.target a) : ∀ b,R.source b ≠ R.target b := by
  intro b h
  apply hn (e.arrow.symm b)
  rw [e.source_symm,e.target_symm,h]

omit [Fintype V] [Fintype W] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq W] [DecidableEq A] [DecidableEq B] in
lemma orthogonal {s t:V} (h:OrthogonalVertices Q s t) :
    OrthogonalVertices R (e.vertex s) (e.vertex t) := by
  constructor
  · exact fun he => h.1 (e.vertex.injective he)
  · intro b hs ht
    apply h.2 (e.arrow.symm b)
    · rw [e.source_symm,hs,Equiv.symm_apply_apply]
    · rw [e.target_symm,ht,Equiv.symm_apply_apply]

omit [Fintype V] [Fintype W] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq W] [DecidableEq A] [DecidableEq B] in
lemma orthogonal_pairwise {J:Type*} (v:J → V)
    (hv:Pairwise fun a b => OrthogonalVertices Q (v a) (v b)) :
    Pairwise fun a b => OrthogonalVertices R ((e.vertex ∘ v) a) ((e.vertex ∘ v) b) :=
  fun _ _ h => e.orthogonal (hv h)

end HarmonicArtin.ReversibleQuiver.Iso

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_ComplexInitial
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Iso
open Zigzag Zigzag.BasedComplex

universe u
variable {V A W B : Type u} {K : Type*} {Q : ReversibleQuiver V A} {R : ReversibleQuiver W B}
  (e : Iso Q R) [Field K] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq W]

lemma complex_initial (α:V) :
    e.complex (initialProjective Q (K:=K) α : BasedComplex Q PUnit.{u+1}) =
      initialProjective R (e.vertex α) := by
  apply ext_placement_differential R
  · rfl
  · exact e.matrix_zero

lemma classMap_initial (α:V) :
    e.classMap (initialClass Q (K:=K) α) = initialClass R (e.vertex α) := by
  change classOfComplex R (e.complex (initialProjective Q α : BasedComplex Q PUnit.{u+1})) = _
  rw [e.complex_initial]
  rfl

end HarmonicArtin.ReversibleQuiver.Iso

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Functors_ProbeEmbeddingMap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]
local notation "R" => probeQuiver Q

noncomputable def classMap : FiniteHomotopyClass Q (K:=K) → FiniteHomotopyClass R (K:=K) :=
  Quotient.map (fun E=>FiniteModel.ofComplex R (complex Q E.complex)) (by
    intro E F ⟨h⟩
    exact ⟨homotopyEquivalence Q h⟩)

omit [DecidableEq A] [DecidableEq (ProbeArrow V A)] in
@[simp] lemma classMap_complex {I:Type u} [Fintype I] [DecidableEq I]
    (E:BasedComplex Q (K:=K) I) :
    classMap Q (classOfComplex Q E)=classOfComplex R (complex Q E) := rfl

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionQuiverSimpleEdge
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m : E → ℕ) (d : V → V → FusionEdge E) (hd : ∀ s t, d s t = d t s)

omit [Fintype V] [DecidableEq V] in
lemma fusionQuiver_orthogonal (α β : FusionVertex (V := V) m) (hne : α ≠ β)
    (h0 : (d α.1 β.1).multiplicity m α.2 β.2 = 0) :
    ReversibleQuiver.Zigzag.OrthogonalVertices (fusionQuiver m d hd) α β := by
  refine ⟨hne, ?_⟩
  intro a hs ht
  change a.1.1 = α at hs
  change a.1.2 = β at ht
  obtain ⟨⟨α',β'⟩, k⟩ := a
  dsimp only at hs ht
  subst α'; subst β'
  have hh := k.isLt
  dsimp only at hh
  exact Nat.not_lt_zero k.val (h0 ▸ hh)

noncomputable def fusionQuiver_simpleEdge (α β : FusionVertex (V := V) m) (hne : α ≠ β)
    (h1 : (d α.1 β.1).multiplicity m α.2 β.2 = 1) :
    ReversibleQuiver.Zigzag.SimpleEdge (fusionQuiver m d hd) α β where
  arrow := ⟨(α,β), ⟨0, by simpa only [h1] using Nat.zero_lt_one⟩⟩
  source := rfl
  target := rfl
  distinct := hne
  unique := by
    rintro ⟨⟨α',β'⟩,k⟩ hs ht
    change α'=α at hs
    change β'=β at ht
    subst α'; subst β'
    congr 1
    apply Fin.ext
    have hh := k.isLt
    dsimp only at hh ⊢
    have hh' : k.val < 1 := h1 ▸ hh
    omega

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_ReducedExpression
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe v
variable {S : Type v}
open CoxeterExchange

lemma positiveLift_mul [Finite S] (M : CoxeterMatrix S) (a b : M.Group)
    (hab : M.toCoxeterSystem.length (a*b) =
      M.toCoxeterSystem.length a+M.toCoxeterSystem.length b) :
    positiveLift M (a*b)=positiveLift M a*positiveLift M b := by
  let u := reducedExpression M a
  let v := reducedExpression M b
  have hru := reducedExpression_reduced M a
  have hrv := reducedExpression_reduced M b
  have hu : M.toCoxeterSystem.wordProd u=a := wordCoxeter_reducedExpression M a
  have hv : M.toCoxeterSystem.wordProd v=b := wordCoxeter_reducedExpression M b
  have hr : M.toCoxeterSystem.IsReduced (u++v) := by
    change M.toCoxeterSystem.length (M.toCoxeterSystem.wordProd (u++v))=(u++v).length
    rw [M.toCoxeterSystem.wordProd_append,hu,hv,hab,List.length_append]
    rw [← hu,← hv,hru.eq,hrv.eq]
  have hp : wordCoxeter M (u++v)=a*b := by
    change M.toCoxeterSystem.wordProd (u++v)=a*b
    rw [M.toCoxeterSystem.wordProd_append,hu,hv]
  rw [← hp,positiveLift_word M (u++v) hr,wordArtin_append]
  rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PositiveLiftSimple
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
lemma positiveLift_longest_square_positive (z:M.Group) :
    ∃ u:List S,wordArtin M u=positiveLift M z^2 := by
  refine ⟨reducedExpression M z++reducedExpression M z,?_⟩
  rw [wordArtin_append,pow_two]
  rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PositiveSimpleLiftMul
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PositivePrefix
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
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_SimpleFrontLink
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
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

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PositiveReverseHom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveSupport_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveSupport_mul _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveSupport_one
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

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_CoefficientPaths
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The path-algebra relations satisfied by actual minimal differentials. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type} (Q : ReversibleQuiver V A)
  [Fintype V] [Fintype A]
  {I : Type} [Fintype I]

noncomputable def arrowMatrix (E : BasedComplex Q (K := ℂ) I) (a : A) : Matrix I I ℂ :=
  fun i j => (E.differential i j).arrow a

omit [Fintype V] in
/-- Truncating to a cochain interval gives a complex. No differential can
leave and re-enter the interval because it increases cochain degree by one. -/
lemma cochain_interval_restrict (E : BasedComplex Q (K := ℂ) I) (l r : ℤ) :
    ∀ i ∈ {i | l ≤ (E.placement i).cochain ∧ (E.placement i).cochain ≤ r},
    ∀ j ∈ {j | l ≤ (E.placement j).cochain ∧ (E.placement j).cochain ≤ r},
    ∀ k ∉ {k | l ≤ (E.placement k).cochain ∧ (E.placement k).cochain ≤ r},
      E.differential i k * E.differential k j = 0 := by
  intro i hi j hj k hk
  change l ≤ (E.placement i).cochain ∧ (E.placement i).cochain ≤ r at hi
  change l ≤ (E.placement j).cochain ∧ (E.placement j).cochain ≤ r at hj
  by_cases hik : E.differential i k = 0
  · rw [hik, Zigzag.zero_mul]
  by_cases hkj : E.differential k j = 0
  · rw [hkj, Zigzag.mul_zero]
  have hci : (E.placement k).cochain = (E.placement i).cochain + 1 := by
    by_contra hn
    exact hik ((E.degree i k).1 hn)
  have hcj : (E.placement j).cochain = (E.placement k).cochain + 1 := by
    by_contra hn
    exact hkj ((E.degree k j).1 hn)
  exact (hk ⟨by omega, by omega⟩).elim

noncomputable def cochainInterval (E : BasedComplex Q (K := ℂ) I) (l r : ℤ) :
    BasedComplex Q (K := ℂ) {i | l ≤ (E.placement i).cochain ∧ (E.placement i).cochain ≤ r} :=
  E.restrict Q _ (cochain_interval_restrict Q E l r)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_ProbeSimpleEdge
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver
open Zigzag Zigzag.BasedComplex CoxeterExchange

variable {V A:Type} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
attribute [local instance] Classical.decEq Classical.propDecidable
local notation "R" => probeQuiver Q
variable [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)] in
lemma probe_orthogonal {α β:V} (h:OrthogonalVertices Q α β) :
    OrthogonalVertices R (.inl α) (.inl β) := by
  refine ⟨fun hh=>h.1 (Sum.inl.inj hh),?_⟩
  rintro (a|⟨v,b,dir⟩) hs ht
  · exact h.2 a (Sum.inl.inj hs) (Sum.inl.inj ht)
  · cases dir <;> simp [probeQuiver] at hs ht

def probe_simpleEdge {α β:V} (e:SimpleEdge Q α β) :
    SimpleEdge R (.inl α) (.inl β) where
  arrow:=.inl e.arrow
  source:=congrArg Sum.inl e.source
  target:=congrArg Sum.inl e.target
  distinct:=fun h=>e.distinct (Sum.inl.inj h)
  unique:=by
    rintro (a|⟨v,b,dir⟩) hs ht
    · exact congrArg Sum.inl (e.unique a (Sum.inl.inj hs) (Sum.inl.inj ht))
    · cases dir <;> simp [probeQuiver] at hs ht

end HarmonicArtin.ReversibleQuiver

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PositiveTransport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveSupport_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveSupport_mul _root_.OAI.HarmonicArtin.ParabolicIntersections.positiveSupport_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relabeling positive Artin monoids and finite-type cancellation. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable

variable {S T : Type} (M : CoxeterMatrix S) (N : CoxeterMatrix T)
    (f : S → T) (hf : ∀ i j, N (f i) (f j)=M i j)

include hf in
lemma positiveMap_relations :
    ∀ a b : FreeMonoid S, positiveBraidRelations M a b →
      FreeMonoid.lift (fun s => positiveGenerator N (f s)) a =
      FreeMonoid.lift (fun s => positiveGenerator N (f s)) b := by
  rintro a b ⟨i,j,rfl,rfl⟩
  simp only [FreeMonoid.lift_ofList]
  have h := wordPositive_braid N (f i) (f j)
  rw [hf] at h
  have hm : wordPositive N ((altList i j (M i j)).map f) =
      wordPositive N ((altList j i (M i j)).map f) := by
    simpa only [altList_map] using h
  simpa only [wordPositive,List.map_map,Function.comp_def] using hm

noncomputable def positiveMap : PositiveArtin M →* PositiveArtin N :=
  PresentedMonoid.lift (fun s => positiveGenerator N (f s)) (positiveMap_relations M N f hf)

@[simp] lemma positiveMap_generator (i : S) :
    positiveMap M N f hf (positiveGenerator M i)=positiveGenerator N (f i) := rfl

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_ProbeLeaf
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver
variable {V A:Type} (Q:ReversibleQuiver V A)

lemma probe_source_leaf {a:ProbeArrow V A} {α:V} {b:Bool}
    (h:(probeQuiver Q).source a=.inr (α,b)) : (probeQuiver Q).target a=.inl α := by
  rcases a with a|⟨v,c,d⟩
  · exact (Sum.inl_ne_inr h).elim
  · cases d
    · exact (Sum.inl_ne_inr h).elim
    · have he:(v,c)=(α,b):=Sum.inr.inj h
      cases he
      rfl

lemma probe_target_leaf {a:ProbeArrow V A} {α:V} {b:Bool}
    (h:(probeQuiver Q).target a=.inr (α,b)) : (probeQuiver Q).source a=.inl α := by
  have hh:=probe_source_leaf Q (a:=(probeQuiver Q).reverse a) (by rw [source_reverse]; exact h)
  rwa [target_reverse] at hh

namespace Zigzag.BasedComplex
variable {K I:Type*} [Field K] [Fintype V] [Fintype A] [Fintype I]
attribute [local instance] Classical.decEq Classical.propDecidable
local notation "R" => probeQuiver Q

lemma probe_differential_row_zero (E:BasedComplex R (K:=K) I) (α:V) (b:Bool)
    (hc:∀j,(E.placement j).color≠.inl α)
    (hf:∀j,(E.placement j).color=.inr (α,b)→(E.placement j).cochain=0)
    (i:I) (hi:(E.placement i).color=.inr (α,b)) (j:I) : E.differential i j=0 := by
  apply (pathCoordinates R).injective
  funext p
  rw [coordinates_zero]
  by_contra hp
  have hs:=coordinates_corner R (E.entries.1 i j) (E.entries.2 i j) hp
  have hdeg:(E.placement j).cochain=(E.placement i).cochain+1 := by
    by_contra h
    exact hp (by rw [(E.degree i j).1 h,coordinates_zero])
  rcases p with v|a|v
  · have hj:(E.placement j).color=.inr (α,b):=hs.2.symm.trans (hs.1.trans hi)
    have hh:=hf j hj
    have hh':=hf i hi
    omega
  · have hh:=probe_source_leaf Q (hs.1.trans hi)
    exact hc j (hs.2.symm.trans hh)
  · have hj:(E.placement j).color=.inr (α,b):=hs.2.symm.trans (hs.1.trans hi)
    have hh:=hf j hj
    have hh':=hf i hi
    omega

lemma probe_differential_col_zero (E:BasedComplex R (K:=K) I) (α:V) (b:Bool)
    (hc:∀j,(E.placement j).color≠.inl α)
    (hf:∀j,(E.placement j).color=.inr (α,b)→(E.placement j).cochain=0)
    (i:I) (hi:(E.placement i).color=.inr (α,b)) (j:I) : E.differential j i=0 := by
  apply (pathCoordinates R).injective
  funext p
  rw [coordinates_zero]
  by_contra hp
  have hs:=coordinates_corner R (E.entries.1 j i) (E.entries.2 j i) hp
  have hdeg:(E.placement i).cochain=(E.placement j).cochain+1 := by
    by_contra h
    exact hp (by rw [(E.degree j i).1 h,coordinates_zero])
  rcases p with v|a|v
  · have hj:(E.placement j).color=.inr (α,b):=hs.1.symm.trans (hs.2.trans hi)
    have hh:=hf j hj
    have hh':=hf i hi
    omega
  · have hh:=probe_target_leaf Q (hs.2.trans hi)
    exact hc j (hs.1.symm.trans hh)
  · have hj:(E.placement j).color=.inr (α,b):=hs.1.symm.trans (hs.2.trans hi)
    have hh:=hf j hj
    have hh':=hf i hi
    omega

lemma generatorArray_placement_pos (E:BasedComplex R (K:=K) I) (i:I) :
    0<E.generatorArray R (E.placement i) := by
  rw [generatorArray_apply]
  change 0<Nat.card {j:I // E.placement j=E.placement i}
  have : Nonempty {j:I // E.placement j=E.placement i}:=⟨⟨i,rfl⟩⟩
  exact Nat.card_pos

end Zigzag.BasedComplex
end HarmonicArtin.ReversibleQuiver

end OAI
end


