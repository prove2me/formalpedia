-- Prove2me | Definitions.Def_OAIQ225Ag006
-- name    : OAIQ225Ag006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:24:40.63796+00:00
-- url     : https://prove2.me/theorems/6ea90b72-664a-4e28-8d0e-17cab0d6388e
-- title:
--   Definitions bundle OAIQ225Ag006 of the split of OpenAI, Harmonic heights and the Artin K(pi,1) conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HarmonicArtin.salvetti_cover_contractible`, carved from OpenAI's openai/math development (OpenAI, *Harmonic heights and the Artin K(pi,1) conjecture*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 259 declarations of OpenAI's Lean: 93 definitions, 3 inductive types or structures, 5 instances and 158 theorems. The definitions and types are `OAI.HarmonicArtin.ReversibleQuiver.Iso.coefficientTopDual`, `OAI.HarmonicArtin.ReversibleQuiver.Iso.cornerPath`, `OAI.HarmonicArtin.ReversibleQuiver.Iso.dualSupportedCycles`, `OAI.HarmonicArtin.ReversibleQuiver.Iso.testIndex`, `OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.chainMap`, `OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap`, `OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.complex`, `OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.cornerPath`, `OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.homotopyEquivalence`, `OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix`, `OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path`, `OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.placement`, `OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.termwiseSplitInjection`, `OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.testIndex`, `OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzagLinear`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ActedIndex`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.AdjacentTestIndex`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.AmplitudeCoreIndex`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ArrowPair`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.BlockPivot`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.BlockPivot.homotopy`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.BlockPivot.inclusionMap`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.BlockPivot.reduced`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.BlockPivot.reducedDifferential`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.BlockPivot.reductionEquivalence`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.BlockPivot.reductionMap`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.BlockPivot.remainder`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.BraidCoreIndex`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.BraidTwistIndex`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.CappedOn`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ChainIsomorphism.coefficientSocle`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ChainIsomorphism.coefficientTopDual`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ChainIsomorphism.pureDualSupportedCycles`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ChainIsomorphism.pureSupportedCycles`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ChainIsomorphism.symm`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ChainIsomorphism.toHomotopyEquivalence`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ChainIsomorphism.trans`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ClassColorSupport`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ClassLowerBound`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ClassUpperBound` and 56 more.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `ArtinGroups_Cancellation_BlockPivot`, `ArtinGroups_Cancellation_ReducedDifferential`, `ArtinGroups_Cancellation_ReducedDifferential2`, `ArtinGroups_Complexes_ActedIndex`, `ArtinGroups_Complexes_ArrowShift`, `ArtinGroups_Complexes_Capped`, `ArtinGroups_Complexes_CoefficientSocle`, `ArtinGroups_Complexes_CoefficientTopDual`, `ArtinGroups_Complexes_ColorBoundary`, `ArtinGroups_Complexes_ColorSupport`, `ArtinGroups_Complexes_CommuteTwistSwap`, `ArtinGroups_Complexes_CornerPath`, `ArtinGroups_Complexes_CorrectionBoundary`, `ArtinGroups_Complexes_DownClosed`, `ArtinGroups_Complexes_EqualColorPair`, `ArtinGroups_Complexes_HomDimension`, `ArtinGroups_Complexes_HomDimension2`, `ArtinGroups_Complexes_HomOperator`, `ArtinGroups_Complexes_HomSpace`, `ArtinGroups_Complexes_HomSpaceMul`, `ArtinGroups_Complexes_InverseHomMatrix`, `ArtinGroups_Complexes_LowMatrix`, `ArtinGroups_Complexes_NegativeHomTransformReflect`, `ArtinGroups_Complexes_OptionSumEquiv`, `ArtinGroups_Complexes_PositiveHomTransform`, `ArtinGroups_Complexes_PositiveTwistFiberEquiv`, `ArtinGroups_Complexes_PositiveWordActionAppend`, `ArtinGroups_Complexes_PureHomSpaceHomogeneous`, `ArtinGroups_Complexes_PureSupportedCycles`, `ArtinGroups_Complexes_Refl`, `ArtinGroups_Complexes_ReindexConeIsomorphism`, `ArtinGroups_Complexes_ReindexHomOperator`, `ArtinGroups_Complexes_TermwiseSplitInjection`, `ArtinGroups_Complexes_UpperBound`, `ArtinGroups_Coxeter_BraidCoreFirstTarget`, `ArtinGroups_Coxeter_BraidCoreIndex`, `ArtinGroups_Coxeter_BraidCorePlacement`, `ArtinGroups_Coxeter_BraidFirstPivot`, `ArtinGroups_Coxeter_BraidSecondPivot`, `ArtinGroups_Coxeter_OrdinaryCoxeterMatrix`, `ArtinGroups_Coxeter_PositiveBraidRel`, `ArtinGroups_Functors_ComplexInitial`, `ArtinGroups_Functors_Path`, `ArtinGroups_Functors_Path2`, `ArtinGroups_Functors_ProbeEmbeddingMap`, `ArtinGroups_Functors_ReversibleQuiverMap`, `ArtinGroups_Functors_SupportedCycles`, `ArtinGroups_Functors_TermwiseSplitInjection`, `ArtinGroups_Functors_TestIndex`, `ArtinGroups_Functors_TestIndex2`, `ArtinGroups_Functors_ZigzagLinear`, `ArtinGroups_Harmonic_FusionQuiverSimpleEdge`, `ArtinGroups_Harmonic_UnfoldedInclusion`, `ArtinGroups_Quivers_EdgeContraction`, `ArtinGroups_Quivers_LengthCases`, `ArtinGroups_Quivers_Level`, `ArtinGroups_Quivers_LinearMatrix`, `ArtinGroups_Quivers_OrthogonalVertices`, `ArtinGroups_Quivers_ProbeVertex`, `ArtinGroups_Quivers_SimpleEdge`, `ArtinGroups_Quivers_TestTransform`, `ArtinGroups_Quivers_TokenTestVector`, `ArtinGroups_Quivers_TraceLinear`, `ArtinGroups_Quivers_UnitTestVector`, `ArtinGroups_Quivers_VertexMinimal`.
--
--   **Imports.** It imports the published bundle `Def_HarmonicArtin`; the bundles `OAIQ225Ag002` and `OAIQ225Ag003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ225Ag009` and `OAIQ225Ag010`.
-- source:
--   OpenAI, Harmonic heights and the Artin K(pi,1) conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Harmonic-heights-and-the-Artin-K-pi-1-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Definitions.Def_HarmonicArtin
import Definitions.Def_OAIQ225Ag002
import Definitions.Def_OAIQ225Ag003

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Cancellation_BlockPivot
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.dual_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.source_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.target_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_false _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_true
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Cancellation_ReducedDifferential
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Cancellation_ReducedDifferential2
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ActedIndex
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

abbrev ActedIndex (E : BasedComplex Q (K := K) I) (α : V) :=
  {i : I // (E.placement i).color = α}

abbrev AmplitudeCoreIndex (E : BasedComplex Q (K := K) I) (α : V) :=
  {u : TestIndex Q E.placement α // Path.length u.2.val ≠ 0} ⊕
    {i : I // (E.placement i).color ≠ α}

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_TestTransform
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_OrthogonalVertices
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_SimpleEdge
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_BraidCoreIndex
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
        change (selfCornerEquiv Q hn α false : _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.CornerPath Q α α) = q
        simpa only [h] using he
      · simp only [h, ↓reduceIte]
        congr 2
        change (selfCornerEquiv Q hn α true : _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.CornerPath Q α α) = q
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_BraidCoreFirstTarget
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ArrowShift
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

abbrev AdjacentTestIndex (E:BasedComplex Q (K:=K) I) (α β:V) :=
  TestIndex Q E.placement β ⊕ TestIndex Q E.placement β ⊕
    TestIndex Q E.placement β ⊕ TestIndex Q E.placement β ⊕ TestIndex Q E.placement α

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_Level
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J L : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

lemma mapDegree_level_bound {p : I → GeneratorPlacement V} {q : J → GeneratorPlacement V}
    {M : Matrix I J (Q.Zigzag K)} {n v : ℤ} (h : MapDegree Q p q n v M)
    {i : I} {j : J} (hne : M i j ≠ 0) :
    (q j).level ≤ (p i).level + n + v := by
  have hc : (q j).cochain = (p i).cochain + n := by
    by_contra hc
    exact hne ((h i j).1 hc)
  have ha := homogeneous_nonzero_degree Q (h i j).2 hne
  dsimp only [GeneratorPlacement.level]
  omega

lemma atLevel_degree_neg (p : I → GeneratorPlacement V) (q : J → GeneratorPlacement V)
    (M : Matrix I J (Q.Zigzag K)) (d : ℤ) (hM : MapDegree Q p q (-1) 0 M) :
    atLevel Q p q M d = 0 := by
  apply Matrix.ext
  intro i j
  change M i.val j.val = 0
  by_contra hne
  have h := mapDegree_level_bound Q hM hne
  rw [i.property, j.property] at h
  omega

namespace BasedComplex

variable [Fintype I] [Fintype J] [Fintype L]

lemma map_level_bound {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    (f : Map Q E F) (i : I) (j : J) (h : f.matrix i j ≠ 0) :
    (F.placement j).level ≤ (E.placement i).level := by
  simpa only [add_zero] using mapDegree_level_bound Q f.degree h

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomSpace
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_TraceLinear
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomSpaceMul
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomOperator
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.instPreorderLiftedCell
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PositiveHomTransform
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ReindexHomOperator
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_CorrectionBoundary
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_InverseHomMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_NegativeHomTransformReflect
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

lemma negativeHomTransform_reflect_boundary (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (α : V) (n v : ℤ) {f : Matrix I J (Q.Zigzag K)}
    (hf : ProjectiveEntries Q E.placement F.placement f)
    (hb : negativeHomTransform Q E F α n f ∈
      homBoundaries Q (E.negativeTwist Q α) (F.negativeTwist Q α) n v) :
    f ∈ homBoundaries Q E F n v := by
  have h₁ := (positiveHomOperator Q (E.negativeTwist Q α)
    (F.negativeTwist Q α) α).map_boundaries n v hb
  have h₂ := (reindexHomOperator Q
    ((E.negativeTwist Q α).positiveTwist Q α)
    ((F.negativeTwist Q α).positiveTwist Q α)
    (inverseTwistIndexEquiv Q hn E α) (inverseTwistIndexEquiv Q hn F α)).map_boundaries n v h₁
  have h₃ := (sandwichHomOperator Q
    (normalizedInverseTwistHomotopyEquivalence Q hn E α).backward
    (normalizedInverseTwistHomotopyEquivalence Q hn F α).forward).map_boundaries n v h₂
  change inverseTwistInjection Q E α *
    (positiveHomTransform Q (E.negativeTwist Q α) (F.negativeTwist Q α) α n
      (negativeHomTransform Q E F α n f)).submatrix
      (inverseTwistIndexEquiv Q hn E α) (inverseTwistIndexEquiv Q hn F α) *
      inverseTwistProjection Q F α ∈ homBoundaries Q E F n v at h₃
  rw [inverseHomMatrix_normalized, inverseHomMatrix_extract Q E F α n hf] at h₃
  exact h₃

lemma negativeHomCohomology_injective (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (α : V) (n v : ℤ) :
    Function.Injective ((negativeHomOperator Q E F α).onCohomology n v) := by
  apply HomOperator.onCohomology_injective
  intro f hf hb
  exact negativeHomTransform_reflect_boundary Q hn E F α n v hf.1.1 hb

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomDimension
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_LinearMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_Capped
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J : Type*}

namespace BasedComplex
variable [Fintype I] [Fintype J]

def CappedOn (E : BasedComplex Q (K := K) I) (U : Set V) (q : ℤ) : Prop :=
  ∀ i, (E.placement i).color ∈ U → (E.placement i).level ≤ q

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PureHomSpaceHomogeneous
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_CoefficientSocle
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_CoefficientTopDual
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
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
lemma pure_differential_linear (E : BasedComplex Q (K := K) I) {l : ℤ}
    (hE : ∀ i, (E.placement i).level = l) : LinearMatrix Q E.differential :=
  pure_homSpace_linear Q E E hE hE (by omega) ⟨E.entries,E.degree⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_CornerPath
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
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

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_EqualColorPair
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

abbrev ArrowPair (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J) :=
  {t : I × J × A // Q.source t.2.2 = (E.placement t.1).color ∧
    Q.target t.2.2 = (F.placement t.2.1).color}

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ColorBoundary
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
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

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_CommuteTwistSwap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_BraidFirstPivot
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_EdgeContraction
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_BraidSecondPivot
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_BraidCorePlacement
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_HomDimension2
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_DownClosed
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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

noncomputable def lowRestriction (E:BasedComplex Q (K:=K) I) (T:Set I) (h:DownClosed Q E T) :
    BasedComplex Q (K:=K) T := E.restrict Q T h.low_condition

def lowerLevelSet (E:BasedComplex Q (K:=K) I) (d:ℤ) : Set I := {i|(E.placement i).level≤d}

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_LowMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional _root_.OAI.HarmonicArtin.instPreorderLiftedCell
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

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma homotopy_level_bound (E:BasedComplex Q (K:=K) I)
    (H:Matrix I I (Q.Zigzag K)) (hH:MapDegree Q E.placement E.placement (-1) 0 H)
    (i j:I) (h:H i j≠0) : (E.placement j).level≤(E.placement i).level := by
  have hh:=mapDegree_level_bound Q hH h
  omega

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_TokenTestVector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
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

lemma token_coordinates (α : V) (p : Path V A) :
    pathCoordinates Q (tokenBasis Q (K := K) α) p = if Sum.inr (Sum.inr α)=p then 1 else 0 := by
  rw [← pathBasis_token,pathBasis_coordinates]

noncomputable def tokenTestVector (p : I → GeneratorPlacement V) (α : V) :
    (I → K) →ₗ[K] (TestIndex Q p α → K) where
  toFun x i := x i.1 * pathCoordinates Q (tokenBasis Q α) i.2.val
  map_add' x y := by funext i; exact _root_.add_mul _ _ _
  map_smul' r x := by funext i; exact _root_.mul_assoc _ _ _

noncomputable def sumTokenTest (p : I → GeneratorPlacement V) (α : V) :
    (TestIndex Q p α → K) →ₗ[K] (I → K) where
  toFun x i := ∑ z : CornerPath Q α (p i).color, x ⟨i,z⟩
  map_add' x y := by funext i; exact Finset.sum_add_distrib
  map_smul' r x := by funext i; exact (Finset.mul_sum _ _ _).symm

omit [Fintype I] [DecidableEq A] in
lemma sumTokenTest_support (p : I → GeneratorPlacement V) (α : V) (c : ℤ)
    (x : TestIndex Q p α → K)
    (hx : ∀ i, ¬ ((p i.1).cochain=c ∧ Path.length i.2.val=2) → x i=0) :
    ∀ i, (p i).color ≠ α ∨ (p i).cochain ≠ c → sumTokenTest Q p α x i=0 := by
  intro i hi
  apply Finset.sum_eq_zero
  intro z hz
  apply hx
  rintro ⟨hc,hl⟩
  rcases hi with hi|hi
  · apply hi
    have he := corner_length_two Q z hl
    have ht := z.property.2
    rw [he] at ht
    exact ht.symm
  · exact hi hc

omit [Fintype I] in
lemma tokenTestVector_sum (p : I → GeneratorPlacement V) (α : V) (c : ℤ)
    (x : TestIndex Q p α → K)
    (hx : ∀ i, ¬ ((p i.1).cochain=c ∧ Path.length i.2.val=2) → x i=0) :
    tokenTestVector Q p α (sumTokenTest Q p α x) = x := by
  funext i
  change (∑ z : CornerPath Q α (p i.1).color, x ⟨i.1,z⟩) *
    pathCoordinates Q (tokenBasis Q α) i.2.val = x i
  by_cases hl : Path.length i.2.val=2
  · have he := corner_length_two Q i.2 hl
    rw [token_coordinates,ite_eq_left he.symm,_root_.mul_one]
    apply Finset.sum_eq_single i.2
    · intro z hz hzi
      apply hx
      rintro ⟨hc,hzlen⟩
      apply hzi
      apply Subtype.ext
      exact (corner_length_two Q z hzlen).trans he.symm
    · simp
  · rw [hx i (fun h => hl h.2)]
    rw [token_coordinates,ite_eq_right (fun he => hl (by rw [← he]; rfl)),MulZeroClass.mul_zero]

omit [Fintype I] in
lemma sumTokenTest_unit (p : I → GeneratorPlacement V) (α : V)
    (x : I → K) (hx : ∀ i, (p i).color≠α → x i=0) :
    sumTokenTest Q p α (tokenTestVector Q p α x)=x := by
  funext i
  by_cases hi : (p i).color=α
  · let z : CornerPath Q α (p i).color := ⟨Sum.inr (Sum.inr α),rfl,hi.symm⟩
    change (∑ w : CornerPath Q α (p i).color, x i * pathCoordinates Q (tokenBasis Q α) w.val)=x i
    rw [Finset.sum_eq_single z]
    · rw [token_coordinates,ite_eq_left rfl,_root_.mul_one]
    · intro w hw hwz
      rw [token_coordinates,ite_eq_right (fun he => hwz (Subtype.ext he.symm)),MulZeroClass.mul_zero]
    · simp
  · change (∑ w : CornerPath Q α (p i).color, x i * pathCoordinates Q (tokenBasis Q α) w.val)=x i
    rw [hx i hi]
    simp

omit [DecidableEq A] in
lemma trace_left_corner {α : V} (x : Zigzag Q K) (hx : vertexId Q α * x=x) :
    trace Q x=x.token α := by
  unfold trace
  apply Finset.sum_eq_single α
  · intro β hβ hβα
    have hh := coordinates_vertexId_left Q α x (Sum.inr (Sum.inr β))
    rw [hx] at hh
    simpa [Path.source,pathCoordinates_token,hβα,Ne.symm hβα] using hh
  · simp

lemma token_path_mul {α β : V} (p : CornerPath Q α β) (x : Zigzag Q K) :
    (pathBasis Q p.val*x).token α=pathCoordinates Q x (Path.dual Q p.val) := by
  rw [coordinates_trace,Path.dual_dual,trace_mul_comm]
  symm
  apply trace_left_corner
  rw [← _root_.mul_assoc,cornerPath_left]

lemma tokenTestVector_differential (E : BasedComplex Q (K := K) I) (α:V)
    (x : I → K) (hx : ∀ i, (E.placement i).color≠α → x i=0)
    (i : TestIndex Q E.placement α) :
    Matrix.vecMul (tokenTestVector Q E.placement α x)
      (testMatrix Q E.placement E.placement α E.differential).transpose i =
      ∑ j, x j * pathCoordinates Q (E.differential i.1 j) (Path.dual Q i.2.val) := by
  change (∑ z : TestIndex Q E.placement α, x z.1 * pathCoordinates Q (tokenBasis Q α) z.2.val *
    pathCoordinates Q (pathBasis Q i.2.val * E.differential i.1 z.1) z.2.val)=_
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hc : (E.placement j).color=α
  · let z : CornerPath Q α (E.placement j).color := ⟨Sum.inr (Sum.inr α),rfl,hc.symm⟩
    rw [Finset.sum_eq_single z]
    · rw [token_coordinates,ite_eq_left rfl,_root_.mul_one]
      change x j * (pathBasis Q i.2.val * E.differential i.1 j).token α = _
      rw [token_path_mul]
    · intro w hw hwz
      rw [token_coordinates,ite_eq_right (fun he => hwz (Subtype.ext he.symm)),
        MulZeroClass.mul_zero,MulZeroClass.zero_mul]
    · simp
  · simp only [hx j hc,MulZeroClass.zero_mul,Finset.sum_const_zero]

namespace BasedComplex

noncomputable def topTestCycles (E : BasedComplex Q (K := K) I) (α:V) (c:ℤ) :=
  ScalarCycles.supportedKernel (testMatrix Q E.placement E.placement α E.differential).transpose
    (fun i => (E.placement i.1).cochain=c ∧ Path.length i.2.val=2)

lemma tokenTestVector_top (E : BasedComplex Q (K := K) I) {l : ℤ}
    (hE : ∀ i, (E.placement i).level=l) (α:V) (c:ℤ)
    {x : I → K} (hx : x ∈ coefficientTopDual Q E α c) :
    tokenTestVector Q E.placement α x ∈ topTestCycles Q E α c := by
  constructor
  · intro i hi
    change x i.1 * pathCoordinates Q (tokenBasis Q α) i.2.val=0
    by_cases hc : (E.placement i.1).cochain=c
    · have hl : Path.length i.2.val≠2 := fun h => hi ⟨hc,h⟩
      rw [token_coordinates,ite_eq_right (fun he => hl (by rw [← he]; rfl)),MulZeroClass.mul_zero]
    · rw [hx.1 i.1 (Or.inr hc),MulZeroClass.zero_mul]
  · funext i
    rw [tokenTestVector_differential Q E α x (fun i h => hx.1 i (Or.inl h))]
    rcases i with ⟨i,⟨p,hs,ht⟩⟩
    rcases p with v|a|v
    · apply Finset.sum_eq_zero
      intro j hj
      change x j * (E.differential i j).token v=0
      rw [(pure_differential_linear Q E hE i j).2]
      simp
    · simpa only [Path.dual,pathCoordinates_arrow,mul_comm,Pi.zero_apply] using hx.2 i (Q.reverse a)
    · apply Finset.sum_eq_zero
      intro j hj
      change x j * (E.differential i j).vertex v=0
      rw [(pure_differential_linear Q E hE i j).1]
      simp

lemma sumTokenTest_top (E : BasedComplex Q (K := K) I) (α:V) (c:ℤ)
    {x : TestIndex Q E.placement α → K} (hx : x ∈ topTestCycles Q E α c) :
    sumTokenTest Q E.placement α x ∈ coefficientTopDual Q E α c := by
  have hs := sumTokenTest_support Q E.placement α c x hx.1
  constructor
  · exact hs
  · intro i a
    by_cases ha : Q.target a=α
    · by_cases ht : Q.source a=(E.placement i).color
      · let z : TestIndex Q E.placement α := ⟨i,Sum.inr (Sum.inl (Q.reverse a)),
          (Q.source_reverse a).trans ha,(Q.target_reverse a).trans ht⟩
        have hh := tokenTestVector_differential Q E α (sumTokenTest Q E.placement α x)
          (fun j h => hs j (Or.inl h)) z
        rw [tokenTestVector_sum Q E.placement α c x hx.1,hx.2] at hh
        simpa only [z,Path.dual,Q.reverse_reverse,pathCoordinates_arrow,mul_comm,Pi.zero_apply] using hh.symm
      · apply Finset.sum_eq_zero
        intro j hj
        have hz : (E.differential i j).arrow a=0 := by
          by_contra hn
          exact ht (coordinates_corner Q (p := Sum.inr (Sum.inl a))
            (E.entries.1 i j) (E.entries.2 i j) hn).1
        rw [hz,MulZeroClass.zero_mul]
    · apply Finset.sum_eq_zero
      intro j hj
      by_cases hjc : (E.placement j).color=α
      · have hz : (E.differential i j).arrow a=0 := by
          by_contra hn
          exact ha ((coordinates_corner Q (p := Sum.inr (Sum.inl a))
            (E.entries.1 i j) (E.entries.2 i j) hn).2.trans hjc)
        rw [hz,MulZeroClass.zero_mul]
      · rw [hs j (Or.inl hjc),MulZeroClass.mul_zero]

noncomputable def coefficientTopTestEquiv (E : BasedComplex Q (K := K) I) {l : ℤ}
    (hE : ∀ i, (E.placement i).level=l) (α:V) (c:ℤ) :
    coefficientTopDual Q E α c ≃ₗ[K] topTestCycles Q E α c where
  toFun x := ⟨tokenTestVector Q E.placement α x.val,tokenTestVector_top Q E hE α c x.property⟩
  invFun y := ⟨sumTokenTest Q E.placement α y.val,sumTokenTest_top Q E α c y.property⟩
  left_inv x := by
    apply Subtype.ext
    exact sumTokenTest_unit Q E.placement α x.val (fun i h => x.property.1 i (Or.inl h))
  right_inv y := by
    apply Subtype.ext
    exact tokenTestVector_sum Q E.placement α c y.val y.property.1
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  map_smul' r x := by apply Subtype.ext; exact map_smul _ _ _

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_UnitTestVector
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
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

lemma vertex_coordinates (α : V) (p : Path V A) :
    pathCoordinates Q (vertexId Q (K := K) α) p = if Sum.inl α=p then 1 else 0 := by
  rw [← pathBasis_vertex,pathBasis_coordinates]

noncomputable def unitTestVector (p : I → GeneratorPlacement V) (α : V) :
    (I → K) →ₗ[K] (TestIndex Q p α → K) where
  toFun x i := x i.1 * pathCoordinates Q (vertexId Q α) i.2.val
  map_add' x y := by funext i; exact _root_.add_mul _ _ _
  map_smul' r x := by funext i; exact _root_.mul_assoc _ _ _

noncomputable def sumUnitTest (p : I → GeneratorPlacement V) (α : V) :
    (TestIndex Q p α → K) →ₗ[K] (I → K) where
  toFun x i := ∑ z : CornerPath Q α (p i).color, x ⟨i,z⟩
  map_add' x y := by funext i; exact Finset.sum_add_distrib
  map_smul' r x := by funext i; exact (Finset.mul_sum _ _ _).symm

omit [Fintype I] [DecidableEq A] in
lemma sumUnitTest_support (p : I → GeneratorPlacement V) (α : V) (c : ℤ)
    (x : TestIndex Q p α → K)
    (hx : ∀ i, ¬ ((p i.1).cochain=c ∧ Path.length i.2.val=0) → x i=0) :
    ∀ i, (p i).color ≠ α ∨ (p i).cochain ≠ c → sumUnitTest Q p α x i=0 := by
  intro i hi
  apply Finset.sum_eq_zero
  intro z hz
  apply hx
  rintro ⟨hc,hl⟩
  rcases hi with hi|hi
  · apply hi
    have he := corner_length_zero Q z hl
    have ht := z.property.2
    rw [he] at ht
    exact ht.symm
  · exact hi hc

omit [Fintype I] in
lemma unitTestVector_sum (p : I → GeneratorPlacement V) (α : V) (c : ℤ)
    (x : TestIndex Q p α → K)
    (hx : ∀ i, ¬ ((p i.1).cochain=c ∧ Path.length i.2.val=0) → x i=0) :
    unitTestVector Q p α (sumUnitTest Q p α x) = x := by
  funext i
  change (∑ z : CornerPath Q α (p i.1).color, x ⟨i.1,z⟩) *
    pathCoordinates Q (vertexId Q α) i.2.val = x i
  by_cases hl : Path.length i.2.val=0
  · have he := corner_length_zero Q i.2 hl
    rw [vertex_coordinates,ite_eq_left he.symm,_root_.mul_one]
    apply Finset.sum_eq_single i.2
    · intro z hz hzi
      apply hx
      rintro ⟨hc,hzlen⟩
      apply hzi
      apply Subtype.ext
      exact (corner_length_zero Q z hzlen).trans he.symm
    · simp
  · rw [hx i (fun h => hl h.2)]
    rw [vertex_coordinates,ite_eq_right (fun he => hl (by rw [← he]; rfl)),MulZeroClass.mul_zero]

omit [Fintype I] in
lemma sumUnitTest_unit (p : I → GeneratorPlacement V) (α : V)
    (x : I → K) (hx : ∀ i, (p i).color≠α → x i=0) :
    sumUnitTest Q p α (unitTestVector Q p α x)=x := by
  funext i
  by_cases hi : (p i).color=α
  · let z : CornerPath Q α (p i).color := ⟨Sum.inl α,rfl,hi.symm⟩
    change (∑ w : CornerPath Q α (p i).color, x i * pathCoordinates Q (vertexId Q α) w.val)=x i
    rw [Finset.sum_eq_single z]
    · rw [vertex_coordinates,ite_eq_left rfl,_root_.mul_one]
    · intro w hw hwz
      rw [vertex_coordinates,ite_eq_right (fun he => hwz (Subtype.ext he.symm)),MulZeroClass.mul_zero]
    · simp
  · change (∑ w : CornerPath Q α (p i).color, x i * pathCoordinates Q (vertexId Q α) w.val)=x i
    rw [hx i hi]
    simp

omit [DecidableEq A] in
lemma unitTestVector_differential (E : BasedComplex Q (K := K) I) (α:V)
    (x : I → K) (hx : ∀ i, (E.placement i).color≠α → x i=0)
    (j : TestIndex Q E.placement α) :
    Matrix.vecMul (unitTestVector Q E.placement α x)
      (testMatrix Q E.placement E.placement α E.differential) j =
      ∑ i, x i * pathCoordinates Q (E.differential i j.1) j.2.val := by
  change (∑ z : TestIndex Q E.placement α, x z.1 * pathCoordinates Q (vertexId Q α) z.2.val *
    pathCoordinates Q (pathBasis Q z.2.val * E.differential z.1 j.1) j.2.val)=_
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hc : (E.placement i).color=α
  · simp only [_root_.mul_assoc,← Finset.mul_sum]
    rw [coordinates_mul_expansion Q (vertexId Q α) (E.differential i j.1)
      (vertexId_mul_self Q α) (by rw [hc]; exact vertexId_mul_self Q α)]
    have heq := E.entries.1 i j.1
    rw [hc] at heq
    rw [heq]
  · simp only [hx i hc,MulZeroClass.zero_mul,Finset.sum_const_zero]

namespace BasedComplex

noncomputable def socleTestCycles (E : BasedComplex Q (K := K) I) (α:V) (c:ℤ) :=
  ScalarCycles.supportedKernel (testMatrix Q E.placement E.placement α E.differential)
    (fun i => (E.placement i.1).cochain=c ∧ Path.length i.2.val=0)

lemma unitTestVector_socle (E : BasedComplex Q (K := K) I) {l : ℤ}
    (hE : ∀ i, (E.placement i).level=l) (α:V) (c:ℤ)
    {x : I → K} (hx : x ∈ coefficientSocle Q E α c) :
    unitTestVector Q E.placement α x ∈ socleTestCycles Q E α c := by
  constructor
  · intro i hi
    change x i.1 * pathCoordinates Q (vertexId Q α) i.2.val=0
    by_cases hc : (E.placement i.1).cochain=c
    · have hl : Path.length i.2.val≠0 := fun h => hi ⟨hc,h⟩
      rw [vertex_coordinates,ite_eq_right (fun he => hl (by rw [← he]; rfl)),MulZeroClass.mul_zero]
    · rw [hx.1 i.1 (Or.inr hc),MulZeroClass.zero_mul]
  · funext j
    rw [unitTestVector_differential Q E α x (fun i h => hx.1 i (Or.inl h))]
    rcases j with ⟨j,⟨p,hs,ht⟩⟩
    rcases p with v|a|v
    · apply Finset.sum_eq_zero
      intro i hi
      change x i * (E.differential i j).vertex v=0
      rw [(pure_differential_linear Q E hE i j).1]
      simp
    · exact hx.2 j a hs
    · apply Finset.sum_eq_zero
      intro i hi
      change x i * (E.differential i j).token v=0
      rw [(pure_differential_linear Q E hE i j).2]
      simp

lemma sumUnitTest_socle (E : BasedComplex Q (K := K) I) (α:V) (c:ℤ)
    {x : TestIndex Q E.placement α → K} (hx : x ∈ socleTestCycles Q E α c) :
    sumUnitTest Q E.placement α x ∈ coefficientSocle Q E α c := by
  have hs := sumUnitTest_support Q E.placement α c x hx.1
  constructor
  · exact hs
  · intro j a ha
    by_cases ht : Q.target a=(E.placement j).color
    · let z : TestIndex Q E.placement α := ⟨j,Sum.inr (Sum.inl a),ha,ht⟩
      have hh := unitTestVector_differential Q E α (sumUnitTest Q E.placement α x)
        (fun i h => hs i (Or.inl h)) z
      rw [unitTestVector_sum Q E.placement α c x hx.1,hx.2] at hh
      exact hh.symm
    · apply Finset.sum_eq_zero
      intro i hi
      have hz : (E.differential i j).arrow a=0 := by
        by_contra hn
        exact ht (coordinates_corner Q (p := Sum.inr (Sum.inl a)) (E.entries.1 i j) (E.entries.2 i j) hn).2
      rw [hz,MulZeroClass.mul_zero]

noncomputable def coefficientSocleTestEquiv (E : BasedComplex Q (K := K) I) {l : ℤ}
    (hE : ∀ i, (E.placement i).level=l) (α:V) (c:ℤ) :
    coefficientSocle Q E α c ≃ₗ[K] socleTestCycles Q E α c where
  toFun x := ⟨unitTestVector Q E.placement α x.val,unitTestVector_socle Q E hE α c x.property⟩
  invFun y := ⟨sumUnitTest Q E.placement α y.val,sumUnitTest_socle Q E α c y.property⟩
  left_inv x := by
    apply Subtype.ext
    exact sumUnitTest_unit Q E.placement α x.val (fun i h => x.property.1 i (Or.inl h))
  right_inv y := by
    apply Subtype.ext
    exact unitTestVector_sum Q E.placement α c y.val y.property.1
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  map_smul' r x := by apply Subtype.ext; exact map_smul _ _ _

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PureSupportedCycles
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K I J : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype I] in
lemma testMatrix_identity (p : I → GeneratorPlacement V) (α : V) :
    testMatrix Q p p α (projectiveIdentity Q p (K := K)) = 1 := by
  apply Matrix.ext
  intro u v
  change pathCoordinates Q (pathBasis Q u.2.val *
    (if u.1 = v.1 then vertexId Q (p u.1).color else 0)) v.2.val = _
  by_cases hi : u.1 = v.1
  · rcases u with ⟨i,u⟩
    rcases v with ⟨j,v⟩
    dsimp only at hi
    subst j
    simp only [ite_true, if_true,cornerPath_right,pathBasis_coordinates]
    by_cases hp : u=v
    · subst v; simp
    · have hv : u.val ≠ v.val := fun h => hp (Subtype.ext h)
      simp [hp,hv]
  · rw [ite_eq_right hi,MulZeroClass.mul_zero,coordinates_zero]
    exact (Matrix.one_apply_ne (fun h => hi (congrArg Sigma.fst h))).symm

namespace BasedComplex

omit [DecidableEq I] [DecidableEq J] in
lemma pureMap_test_support {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (f : Map Q E F) {l : ℤ}
    (hE : ∀ i, (E.placement i).level=l) (hF : ∀ j, (F.placement j).level=l)
    (α : V) (c n : ℤ) (i : TestIndex Q E.placement α) (j : TestIndex Q F.placement α)
    (h : testMatrix Q E.placement F.placement α f.matrix i j ≠ 0) :
    ((E.placement i.1).cochain=c ∧ Path.length i.2.val=n) ↔
      ((F.placement j.1).cochain=c ∧ Path.length j.2.val=n) := by
  have he : (F.placement j.1).cochain = (E.placement i.1).cochain := by
    by_contra hh
    apply h
    unfold testMatrix
    rw [(f.degree i.1 j.1).1 (by simpa only [add_zero] using hh),
      MulZeroClass.mul_zero,coordinates_zero]
  have hh := pure_homSpace_homogeneous Q E F hE hF (n := 0) (v := 0) (r := 0)
    (by omega) ⟨f.entries,f.degree⟩ i.1 j.1
  have hp := coordinates_mul_degree Q (pathBasis_homogeneous Q i.2.val) hh h
  have hlen : Path.length j.2.val = Path.length i.2.val := by simpa only [add_zero] using hp
  rw [he,hlen]

noncomputable def ChainIsomorphism.pureSupportedCycles
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    (f : ChainIsomorphism Q E F) {l : ℤ}
    (hE : ∀ i, (E.placement i).level=l) (hF : ∀ j, (F.placement j).level=l)
    (α : V) (c n : ℤ) :
    ScalarCycles.supportedKernel (testMatrix Q E.placement E.placement α E.differential)
      (fun i => (E.placement i.1).cochain=c ∧ Path.length i.2.val=n) ≃ₗ[K]
    ScalarCycles.supportedKernel (testMatrix Q F.placement F.placement α F.differential)
      (fun i => (F.placement i.1).cochain=c ∧ Path.length i.2.val=n) := by
  apply ScalarCycles.conjugateEquiv _ _ _ _
    (testMatrix Q E.placement F.placement α f.forward.matrix)
    (testMatrix Q F.placement E.placement α f.backward.matrix)
  · exact pureMap_test_support Q f.forward hE hF α c n
  · exact pureMap_test_support Q f.backward hF hE α c n
  · rw [testMatrix_mul Q α _ f.forward.entries,f.sourceEquation,testMatrix_identity]
  · rw [testMatrix_mul Q α _ f.backward.entries,f.targetEquation,testMatrix_identity]
  · rw [testMatrix_mul Q α _ E.entries,testMatrix_mul Q α _ f.forward.entries,f.forward.commute]

noncomputable def ChainIsomorphism.pureDualSupportedCycles
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    (f : ChainIsomorphism Q E F) {l : ℤ}
    (hE : ∀ i, (E.placement i).level=l) (hF : ∀ j, (F.placement j).level=l)
    (α : V) (c n : ℤ) :
    ScalarCycles.supportedKernel (testMatrix Q E.placement E.placement α E.differential).transpose
      (fun i => (E.placement i.1).cochain=c ∧ Path.length i.2.val=n) ≃ₗ[K]
    ScalarCycles.supportedKernel (testMatrix Q F.placement F.placement α F.differential).transpose
      (fun i => (F.placement i.1).cochain=c ∧ Path.length i.2.val=n) := by
  apply ScalarCycles.transposeConjugateEquiv _ _ _ _
    (testMatrix Q E.placement F.placement α f.forward.matrix)
    (testMatrix Q F.placement E.placement α f.backward.matrix)
  · exact pureMap_test_support Q f.forward hE hF α c n
  · exact pureMap_test_support Q f.backward hF hE α c n
  · rw [testMatrix_mul Q α _ f.forward.entries,f.sourceEquation,testMatrix_identity]
  · rw [testMatrix_mul Q α _ f.backward.entries,f.targetEquation,testMatrix_identity]
  · rw [testMatrix_mul Q α _ F.entries,testMatrix_mul Q α _ f.backward.entries,f.backward.commute]

noncomputable def ChainIsomorphism.coefficientSocle
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    (f : ChainIsomorphism Q E F) {l : ℤ}
    (hE : ∀ i, (E.placement i).level=l) (hF : ∀ j, (F.placement j).level=l)
    (α : V) (c : ℤ) :
    coefficientSocle Q E α c ≃ₗ[K] coefficientSocle Q F α c :=
  ((coefficientSocleTestEquiv Q E hE α c).trans
    (f.pureSupportedCycles Q hE hF α c 0)).trans
    (coefficientSocleTestEquiv Q F hF α c).symm

noncomputable def ChainIsomorphism.coefficientTopDual
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    (f : ChainIsomorphism Q E F) {l : ℤ}
    (hE : ∀ i, (E.placement i).level=l) (hF : ∀ j, (F.placement j).level=l)
    (α : V) (c : ℤ) :
    coefficientTopDual Q E α c ≃ₗ[K] coefficientTopDual Q F α c :=
  ((coefficientTopTestEquiv Q E hE α c).trans
    (f.pureDualSupportedCycles Q hE hF α c 2)).trans
    (coefficientTopTestEquiv Q F hF α c).symm

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_Refl
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

noncomputable def ChainIsomorphism.symm {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (a : ChainIsomorphism Q E F) :
    ChainIsomorphism Q F E where
  forward := a.backward
  backward := a.forward
  sourceEquation := a.targetEquation
  targetEquation := a.sourceEquation

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

noncomputable def Map.reindex {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (f : Map Q E F) (e : L ≃ I) (d : N ≃ J) :
    Map Q (E.reindex Q e) (F.reindex Q d) where
  matrix := f.matrix.submatrix e d
  entries := ⟨fun i j => f.entries.1 (e i) (d j), fun i j => f.entries.2 (e i) (d j)⟩
  degree := fun i j => f.degree (e i) (d j)
  commute := by
    change E.differential.submatrix e e * f.matrix.submatrix e d =
      f.matrix.submatrix e d * F.differential.submatrix d d
    rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv,f.commute]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_LengthCases
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_UpperBound
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

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_TermwiseSplitInjection
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_PositiveBraidRel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} (Q:ReversibleQuiver V A)

variable {K:Type*} [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def positiveWordAction : List V→FiniteHomotopyClass Q (K:=K)→FiniteHomotopyClass Q (K:=K)
  | [],x=>x
  | α::w,x=>classPositiveTwist Q α (positiveWordAction w x)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_OrdinaryCoxeterMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex
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

def ClassColorSupport (U:Set V) (x:FiniteHomotopyClass Q (K:=K)) : Prop :=
  ∀ i,((minimalClassModel Q x).complex.placement i).color∈U

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_OptionSumEquiv
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_VertexMinimal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PositiveTwistFiberEquiv
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_PositiveWordActionAppend
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Complexes_ReindexConeIsomorphism
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional
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
  {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}

omit [DecidableEq I] [DecidableEq J] [DecidableEq L] [DecidableEq N] in
lemma Map.reindexCone_eq (f : Map Q E F) (e : L ≃ I) (d : N ≃ J) :
    (f.cone Q).reindex Q (Equiv.sumCongr e d) = (f.reindex Q e d).cone Q := by
  apply ext_placement_differential
  · funext i
    rcases i with i|i <;> rfl
  · apply Matrix.ext
    intro i j
    rcases i with i|i <;> rcases j with j|j <;> rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_Path
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
lemma path_basis (p:Path V A) :
    e.zigzagLinear (pathBasis Q (K := K) p) = pathBasis R (e.path p) := by
  apply (pathCoordinates R).injective
  funext q
  obtain ⟨q,rfl⟩ := e.path.surjective q
  rw [e.path_coordinates,pathBasis_coordinates,pathBasis_coordinates]
  simp only [e.path.injective.eq_iff]

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_TestIndex
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_ReversibleQuiverMap
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_ComplexInitial
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_ProbeVertex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_ZigzagLinear
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
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

lemma complex_minimal [Fintype I] {E : BasedComplex Q (K := K) I} (h:E.IsMinimal Q) :
    (complex Q E).IsMinimal (probeQuiver Q) := by
  intro i j
  ext v
  change (zigzagLinear Q (E.differential i j)).vertex v=0
  cases v <;> simp [h i j]

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
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_Path2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse
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

lemma path_injective : Function.Injective (path (V:=V) (A:=A)) := by
  exact Sum.map_injective.mpr ⟨Sum.inl_injective,Sum.map_injective.mpr ⟨Sum.inl_injective,Sum.inl_injective⟩⟩
@[simp] lemma path_source (p:Path V A) : Path.source R (path p)=.inl (Path.source Q p) := by
  rcases p with v|a|v <;> rfl
@[simp] lemma path_target (p:Path V A) : Path.target R (path p)=.inl (Path.target Q p) := by
  rcases p with v|a|v <;> rfl
@[simp] lemma path_length (p:Path V A) : Path.length (path p)=Path.length p := by
  rcases p with v|a|v <;> rfl

lemma cornerPath_surjective (s t:V)
    (p:CornerPath R (.inl s) (.inl t)) :
    ∃q:CornerPath Q s t,path q.val=p.val := by
  rcases p with ⟨p,hs,ht⟩
  rcases p with (v|v)|(a|⟨v,b,d⟩)|(v|v)
  · exact ⟨⟨.inl v,Sum.inl.inj hs,Sum.inl.inj ht⟩,rfl⟩
  · cases hs
  · exact ⟨⟨.inr (.inl a),Sum.inl.inj hs,Sum.inl.inj ht⟩,rfl⟩
  · cases d
    · cases ht
    · cases hs
  · exact ⟨⟨.inr (.inr v),Sum.inl.inj hs,Sum.inl.inj ht⟩,rfl⟩
  · cases hs

noncomputable def cornerPath (s t:V) : CornerPath Q s t ≃ CornerPath R (.inl s) (.inl t) :=
  Equiv.ofBijective (fun p=>⟨path p.val,by
    rw [path_source,path_target,p.property.1,p.property.2]; exact ⟨rfl,rfl⟩⟩)
    ⟨fun _ _ h=>Subtype.ext (path_injective (congrArg Subtype.val h)),by
      intro p; obtain ⟨q,hq⟩:=cornerPath_surjective Q s t p
      exact ⟨q,Subtype.ext hq⟩⟩

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_TestIndex2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

variable {V A K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]
  {I J:Type*}
local notation "R" => probeQuiver Q

noncomputable def testIndex (p : I → GeneratorPlacement V) (α:V) :
    TestIndex Q p α ≃ TestIndex R (placement ∘ p) (Sum.inl α) :=
  Equiv.sigmaCongrRight fun i => cornerPath Q α (p i).color

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_ProbeEmbeddingMap
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_SupportedCycles
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype
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
  {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma test_matrix_reindex (E:BasedComplex Q (K := K) I) (α:V) :
    (testMatrix R (e.complex E).placement (e.complex E).placement (e.vertex α) (e.complex E).differential).submatrix
      (e.testIndex E.placement α) (e.testIndex E.placement α) =
      testMatrix Q E.placement E.placement α E.differential := by
  apply Matrix.ext
  intro i j
  exact e.test_matrix _ _ _ _ i j

omit [Fintype V] [Fintype W] [DecidableEq A] [DecidableEq B] [DecidableEq I] in
lemma test_support_reindex (E:BasedComplex Q (K := K) I) (α:V) (c n:ℤ) :
    (fun i : TestIndex R (e.complex E).placement (e.vertex α) =>
      ((e.complex E).placement i.1).cochain=c ∧ Path.length i.2.val=n) ∘ e.testIndex E.placement α =
      (fun i : TestIndex Q E.placement α => (E.placement i.1).cochain=c ∧ Path.length i.2.val=n) := by
  funext i
  change (_ ∧ Path.length (e.path i.2.val)=n) = _
  rw [e.path_length]
  rfl

noncomputable def dualSupportedCycles (E:BasedComplex Q (K := K) I) (α:V) (c n:ℤ) :
    ScalarCycles.supportedKernel (testMatrix Q E.placement E.placement α E.differential).transpose
      (fun i => (E.placement i.1).cochain=c ∧ Path.length i.2.val=n) ≃ₗ[K]
    ScalarCycles.supportedKernel
      (testMatrix R (e.complex E).placement (e.complex E).placement (e.vertex α) (e.complex E).differential).transpose
      (fun i => ((e.complex E).placement i.1).cochain=c ∧ Path.length i.2.val=n) := by
  apply LinearEquiv.symm
  refine (ScalarCycles.reindexEquiv
    (testMatrix R (e.complex E).placement (e.complex E).placement (e.vertex α) (e.complex E).differential).transpose
    (fun i => ((e.complex E).placement i.1).cochain=c ∧ Path.length i.2.val=n) (e.testIndex E.placement α)).trans
    (ScalarCycles.congrEquiv _ _ _ _ ?_ (e.test_support_reindex E α c n))
  exact (Matrix.transpose_submatrix _ _ _).symm.trans (congrArg Matrix.transpose (e.test_matrix_reindex E α))

noncomputable def coefficientTopDual (E:BasedComplex Q (K := K) I) {l:ℤ}
    (hE:∀ i,(E.placement i).level=l) (α:V) (c:ℤ) :
    BasedComplex.coefficientTopDual Q E α c ≃ₗ[K]
      BasedComplex.coefficientTopDual R (e.complex E) (e.vertex α) c :=
  (coefficientTopTestEquiv Q E hE α c).trans ((e.dualSupportedCycles E α c 2).trans
    (coefficientTopTestEquiv R (e.complex E) hE (e.vertex α) c).symm)

end HarmonicArtin.ReversibleQuiver.Iso

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_TermwiseSplitInjection
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
local notation "R" => probeQuiver Q

noncomputable def termwiseSplitInjection {E:BasedComplex Q (K:=K) I}
    {F:BasedComplex Q (K:=K) J} (ι:TermwiseSplitInjection Q E F) :
    TermwiseSplitInjection R (complex Q E) (complex Q F) where
  inclusion:=chainMap Q ι.inclusion
  retraction:=matrix Q ι.retraction
  split:=by
    change matrix Q ι.inclusion.matrix*matrix Q ι.retraction=_
    rw [← matrix_mul,ι.split,matrix_identity]
    rfl

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionQuiverSimpleEdge
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
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_UnfoldedInclusion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.labelSplit_apply _root_.OAI.HarmonicArtin.labelSplit_symm_at _root_.OAI.HarmonicArtin.labelSplit_symm_rest
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

variable (M : CoxeterMatrix S)
local notation "Q" => fusionQuiver (fusionLabelSize M) (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

lemma unfolded_ordinaryMatrix (J : Set S) (hJ : IsSpherical M J)
    (α β : J × FusionLabel (fusionLabelSize M)) :
    ordinaryCoxeterMatrix Q (unfoldedInclusion M J α) (unfoldedInclusion M J β)=
      unfoldedMatrix M J α β := by
  by_cases he : α=β
  · subst β
    simp
  · have hi := fun hh => he (unfoldedInclusion_injective M J hh)
    have hn := spherical_fusion_multiplicity_le_one M J hJ α.1 β.1 α.2 β.2
    have hp : (coxeterFusionEdge M (.inl α.1) (.inl β.1)).multiplicity
        (fusionLabelSize M) α.2 β.2=0 ∨
      (coxeterFusionEdge M (.inl α.1) (.inl β.1)).multiplicity
        (fusionLabelSize M) α.2 β.2=1 := by omega
    rcases hp with hz|ho
    · have horth := fusionQuiver_orthogonal (fusionLabelSize M) (coxeterFusionEdge M)
        (coxeterFusionEdge_symm M) (unfoldedInclusion M J α) (unfoldedInclusion M J β) hi hz
      rw [ordinaryCoxeterMatrix_orthogonal Q horth,unfoldedMatrix_apply,ite_eq_right he,ite_eq_left hz]
    · let edge := fusionQuiver_simpleEdge (fusionLabelSize M) (coxeterFusionEdge M)
        (coxeterFusionEdge_symm M) (unfoldedInclusion M J α) (unfoldedInclusion M J β) hi ho
      rw [ordinaryCoxeterMatrix_adjacent Q edge,unfoldedMatrix_apply,ite_eq_right he,ho]
      norm_num

end HarmonicArtin

end OAI
end


