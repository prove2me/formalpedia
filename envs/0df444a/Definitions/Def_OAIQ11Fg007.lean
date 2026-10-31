-- Prove2me | Definitions.Def_OAIQ11Fg007
-- name    : OAIQ11Fg007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T09:39:59.535921+00:00
-- url     : https://prove2.me/theorems/b7fce6c3-47b8-4cea-852d-fd0b09b1e711
-- title:
--   Definitions bundle OAIQ11Fg007 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 39 declarations of OpenAI's Lean: 15 definitions, 2 instances and 22 theorems. The definitions and types are `OAI.Generator.FiniteMatrixStage.energy`, `OAI.Generator.FiniteMatrixStage.generatedVonNeumann`, `OAI.Generator.FiniteMatrixStage.restrictStage`, `OAI.Generator.FiniteMatrixStage.stageExpectation`, `OAI.Generator.FiniteMatrixStage.stageUnion`, `OAI.Generator.FiniteMatrixStage.stageVonNeumann`, `OAI.Generator.MatrixUnitSystem.wotLinearMap`, `OAI.Generator.Tracial.EquivalentPartition.subset`, `OAI.Generator.Tracial.Q`, `OAI.Generator.Tracial.boundedPartialSupport`, `OAI.Generator.Tracial.boundedPartialUnitary`, `OAI.Generator.Tracial.conditionalExpectation`, `OAI.Generator.tupleOrbitClosure`, `OAI.Generator.tupleOrbitMap`, `OAI.Generator.vonNeumannOfWOTClosed`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_Bicommutant`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/Bicommutant.lean), [`FactorGeneration_DyadicComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/DyadicComparison.lean), [`FactorGeneration_Expectations`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/Expectations.lean), [`FactorGeneration_HaarPatches`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/HaarPatches.lean), [`FactorGeneration_MatrixAlgebras`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/MatrixAlgebras.lean), [`FactorGeneration_MatrixExpectation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/MatrixExpectation.lean), [`FactorGeneration_MatrixSequence`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/MatrixSequence.lean), [`FactorGeneration_QuotientHilbert`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/QuotientHilbert.lean), [`FactorGeneration_SpectralTruncation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/SpectralTruncation.lean).
--
--   **Imports.** It imports the published bundle `Def_FactorGeneration`; the bundles `OAIQ11Fg003`, `OAIQ11Fg004` and `OAIQ11Fg005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ11Fg011`, `OAIQ11Fg012` and `OAIQ11Fg029`; the statements `OAI.Generator.FiniteMatrixStage.exists_matrix_generated_centered_partition`, `OAI_Generator_Tracial_exists_admissible_family_patch`, `OAI.Generator.Tracial.exists_eventually_centered_corner_representatives`, `OAI.Generator.Tracial.exists_irreducible_matrix_energy_descent`, `OAI_Generator_Tracial_exists_unitResidual_controlled_patch`, `OAI_Generator_Tracial_maskPartialSequence_orthogonal` and `OAI_Generator_Tracial_powerBlockWord_expand`; the proofs of `OAI.Generator.FiniteMatrixStage.generated_isII1`, `OAI_Generator_Tracial_exists_admissible_family_patch`, `OAI_Generator_Tracial_exists_component_controlled_refinement`, `OAI_Generator_Tracial_integerValueWord_blocks`, `OAI_Generator_Tracial_maskPartialSequence_orthogonal`, `OAI_Generator_Tracial_powerBlockWord_expand`, `OAI_Generator_Tracial_predualFunctional_unitBall_continuous` and `OAI_Generator_Tracial_reducedOrderedMoments_integerWord`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_FactorGeneration
import Definitions.Def_OAIQ11Fg003
import Definitions.Def_OAIQ11Fg004
import Definitions.Def_OAIQ11Fg005

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Bicommutant
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.vectorOrbitClosure_complete _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Finite diagonal amplification and the projection onto a simultaneous
operator orbit. These are the analytic ingredients of the bicommutant theorem. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

theorem diagonalOperator_star (T : H →L[ℂ] H) :
    diagonalOperator (ι := ι) (star T)=star (diagonalOperator (ι := ι) T) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  simp only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  simp only [PiLp.inner_apply,diagonalOperator_apply,
    ContinuousLinearMap.adjoint_inner_right]

def tupleOrbitMap (S : StarSubalgebra ℂ (H →L[ℂ] H)) (x : FiniteHilbert ι H) :
    S →ₗ[ℂ] FiniteHilbert ι H where
  toFun a := diagonalOperator a.val x
  map_add' a b := by ext i; rfl
  map_smul' c a := by ext i; rfl

def tupleOrbitClosure (S : StarSubalgebra ℂ (H →L[ℂ] H)) (x : FiniteHilbert ι H) :
    Submodule ℂ (FiniteHilbert ι H) := (tupleOrbitMap S x).range.topologicalClosure

instance tupleOrbitClosure_complete (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : FiniteHilbert ι H) : CompleteSpace (tupleOrbitClosure S x) :=
  inferInstanceAs (CompleteSpace (tupleOrbitMap S x).range.topologicalClosure)

theorem mem_tupleOrbitClosure (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : FiniteHilbert ι H) : x ∈ tupleOrbitClosure S x := by
  apply Submodule.le_topologicalClosure
  refine ⟨1,?_⟩
  ext i
  rfl

theorem tupleOrbitClosure_invariant (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : FiniteHilbert ι H) (a : S) {y : FiniteHilbert ι H}
    (hy : y ∈ tupleOrbitClosure S x) : diagonalOperator a.val y ∈ tupleOrbitClosure S x := by
  have h : (tupleOrbitMap S x).range.topologicalClosure ≤
      (tupleOrbitClosure S x).comap (diagonalOperator a.val).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro z ⟨b,rfl⟩
      apply Submodule.le_topologicalClosure
      refine ⟨a*b,?_⟩
      ext i
      rfl
    · exact (Submodule.isClosed_topologicalClosure _).preimage (diagonalOperator a.val).continuous
  exact h hy

theorem tupleOrbitProjection_commutes (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : FiniteHilbert ι H) (a : S) :
    (tupleOrbitClosure S x).starProjection*diagonalOperator a.val=
      diagonalOperator a.val*(tupleOrbitClosure S x).starProjection := by
  apply starProjection_commutes_of_invariant
  · exact fun y hy => tupleOrbitClosure_invariant S x a hy
  · rw [← diagonalOperator_star]
    exact fun y hy => tupleOrbitClosure_invariant S x (star a) hy

variable [DecidableEq ι]

omit [Fintype ι] in
theorem operatorEntry_mem_centralizer (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (Q : FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H)
    (hQ : ∀ a : S,Q*diagonalOperator a.val=diagonalOperator a.val*Q) (i j : ι) :
    operatorEntry Q i j ∈ Set.centralizer (S : Set (H →L[ℂ] H)) := by
  intro a ha
  ext z
  change a (Q (tupleSingle j z) i)=Q (tupleSingle j (a z)) i
  have h := congrArg (fun T : FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H =>
    T (tupleSingle j z) i) (hQ ⟨a,ha⟩)
  simpa only [mul_apply_eq_comp,diagonalOperator_apply,
    diagonalOperator_single] using h.symm

omit [CompleteSpace H] in
theorem diagonalOperator_commutes_of_entries (T : H →L[ℂ] H)
    (Q : FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H)
    (h : ∀ i j,operatorEntry Q i j*T=T*operatorEntry Q i j) :
    Q*diagonalOperator T=diagonalOperator T*Q := by
  ext x i
  rw [tuple_eq_sum_single x]
  simp only [map_sum,mul_apply_eq_comp,diagonalOperator_single]
  simp only [WithLp.ofLp_sum,Finset.sum_apply,diagonalOperator_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun a : H →L[ℂ] H => a (x j)) (h i j)

theorem bicommutant_tuple_mem_closure (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (x : FiniteHilbert ι H) : diagonalOperator T x ∈ tupleOrbitClosure S x := by
  let Q := (tupleOrbitClosure S x).starProjection
  have hcomm : Q*diagonalOperator T=diagonalOperator T*Q :=
    diagonalOperator_commutes_of_entries T Q (fun i j => hT _
      (operatorEntry_mem_centralizer S Q (tupleOrbitProjection_commutes S x) i j))
  apply Submodule.starProjection_eq_self_iff.mp
  have h := congrArg (fun a : FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H => a x) hcomm
  change Q (diagonalOperator T x)=diagonalOperator T (Q x) at h
  rw [show Q x=x from Submodule.starProjection_eq_self_iff.mpr (mem_tupleOrbitClosure S x)] at h
  exact h

end

/-! The double commutant theorem for actual unital star subalgebras of B(H).
Finite simultaneous strong approximation constructs a WOT-convergent net.
No bounded approximation or separable-predual theorem is claimed here. -/
section
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem bicommutant_finite_strong_approximation (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (s : Finset H) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : S,∀ x ∈ s,‖T x-a.val x‖ < ε := by
  classical
  let x : FiniteHilbert s H := WithLp.toLp 2 (fun i : s => i.val)
  have h := bicommutant_tuple_mem_closure S T hT x
  obtain ⟨z,⟨a,rfl⟩,ha⟩ := Metric.mem_closure_iff.mp h ε hε
  refine ⟨a,?_⟩
  intro y hy
  have hb := PiLp.norm_apply_le (diagonalOperator T x-tupleOrbitMap S x a) (⟨y,hy⟩ : s)
  exact hb.trans_lt (by simpa only [dist_eq_norm] using ha)

theorem bicommutant_exists_strong_net (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    ∃ a : Finset H × ℕ → S,∀ x : H,
      Tendsto (fun d => (a d).val x) atTop (𝓝 (T x)) := by
  classical
  have hex (d : Finset H × ℕ) := bicommutant_finite_strong_approximation S T hT d.1
    (1/((d.2 : ℝ)+1)) (by positivity)
  choose a ha using hex
  refine ⟨a,?_⟩
  intro x
  apply (tendsto_iff_dist_tendsto_zero).mpr
  have hsnd : Tendsto (fun d : Finset H × ℕ => d.2) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  apply squeeze_zero' (Eventually.of_forall (fun d => dist_nonneg)) ?_
    (tendsto_one_div_add_atTop_nhds_zero_nat.comp hsnd)
  filter_upwards [eventually_ge_atTop (({x} : Finset H),0)] with d hd
  rw [dist_comm,dist_eq_norm]
  exact (ha d x (hd.1 (Finset.mem_singleton_self x))).le

theorem wotClosed_bicommutant (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : WOTClosed S) :
    Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))=S := by
  classical
  apply Set.Subset.antisymm
  · intro T hT
    obtain ⟨a,ha⟩ := bicommutant_exists_strong_net S T hT
    have hw : Tendsto (fun d => ContinuousLinearMapWOT.ofCLM (a d).val) atTop
        (𝓝 (ContinuousLinearMapWOT.ofCLM T)) := by
      apply ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr
      intro x y
      exact (continuous_const.inner continuous_id).continuousAt.tendsto.comp (ha x)
    exact hS.mem_of_tendsto hw (Eventually.of_forall (fun d => (a d).property))
  · intro T hT a ha
    exact (ha T hT).symm

def vonNeumannOfWOTClosed (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : WOTClosed S) :
    VonNeumannAlgebra H where
  toStarSubalgebra := S
  centralizer_centralizer' := wotClosed_bicommutant S hS

end

/-! Countable algebraic generators give a separable star algebra using only
continuous addition and scalar multiplication. No multiplication continuity is
required, so the result applies to the two-norm on a tracial quotient. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_DyadicComparison
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Halving every projection in a diffuse factor without a trace.
Maximality leaves no residual corner: a diffuse residual splits into two
nonzero orthogonal projections, and a polar link gives a strict extension. -/

/-! Finite partitions with explicit equivalence witnesses and compatible binary
refinement. The common initial projection is halved once and its two pieces
are transported to every old piece, so all new pieces remain equivalent. -/

/-! Actual sums of countable orthogonal partial isometries, including least
initial/final support identities. No trace or countable-cofinality premise. -/

/-! Actual finite sums of orthogonal partial isometries and finite subsets of
equivalent partitions. The finite subset is arbitrary, without an index order. -/
open scoped BigOperators
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι : Type*} [Fintype ι]

def subset (E : EquivalentPartition p ι) (s : Finset ι) : AlgebraProjection M :=
  AlgebraProjection.finsetSum (fun i => (E.leg i).target) s
    (fun i _ j _ => E.orthogonal i j)

/-! Exact finite cardinal comparison of sums of equivalent nonzero projections.
Finiteness prevents a larger collection from embedding in a smaller one. -/

end EquivalentPartition
end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_SpectralTruncation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Positivity of the tracial pairing does not require the two positive
operators to commute. These estimates will control spectral truncation. -/

/-! Upper spectral truncation of a self-adjoint operator. The truncation
remains in the original operator ball and has a positive discarded part. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

attribute [local instance] OAI.Generator.Tracial.truncationCStar
attribute [local instance] OAI.Generator.Tracial.truncationOrder
attribute [local instance] OAI.Generator.Tracial.truncationLE
attribute [local instance] OAI.Generator.Tracial.truncationStarOrder
theorem upperTruncate_distance (τ : TracialRepresentation M)
    (a x : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (hx : IsSelfAdjoint x) :
    τ.norm₂ (upperTruncate a ‖x‖-x)^2 +
      τ.norm₂ ((a-algebraMap ℝ M.toStarSubalgebra ‖x‖)⁺)^2 ≤ τ.norm₂ (a-x)^2 := by
  let d := (a-algebraMap ℝ M.toStarSubalgebra ‖x‖)⁺
  let z := upperTruncate a ‖x‖
  have hd : 0 ≤ d := CFC.posPart_nonneg _
  have had : a=z+d := by dsimp [z,d,upperTruncate]; abel
  have hdz : d*z=‖x‖ • d := upperTruncate_discard_mul a ha ‖x‖
  have ht := trace_mul_le_norm τ d x hd hx
  have hsq := norm₂_sub_sq τ (a-x) d
  have hid : a-x-d=z-x := by rw [had]; abel
  rw [hid,(ha.sub hx).star_eq,τ.trace_mul_comm (a-x) d] at hsq
  have htrace : (τ.trace (d*(a-x))).re =
      τ.norm₂ d^2+‖x‖*(τ.trace d).re-(τ.trace (d*x)).re := by
    rw [had,mul_sub,mul_add,trace_sub,cornerTrace_add,hdz,← Complex.coe_smul,
      cornerTrace_smul,Complex.sub_re,Complex.add_re,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [norm₂_sq_trace τ,hd.isSelfAdjoint.star_eq]
    ring
  rw [htrace] at hsq
  change τ.norm₂ (z-x)^2 + τ.norm₂ d^2 ≤ τ.norm₂ (a-x)^2
  linarith

end

/-! Spectral truncation forces a self-adjoint least-distance point in a
subalgebra ball to have norm at most the norm of the ambient test operator. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

attribute [local instance] OAI.Generator.Tracial.interiorCStar
attribute [local instance] OAI.Generator.Tracial.interiorOrder
attribute [local instance] OAI.Generator.Tracial.interiorPreorder
attribute [local instance] OAI.Generator.Tracial.interiorLE
attribute [local instance] OAI.Generator.Tracial.interiorStarOrder
theorem selfAdjoint_ball_minimum_upper (τ : TracialRepresentation M) (hNM : N ≤ M)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (R : ℝ)
    (c : N.toStarSubalgebra) (hc : IsSelfAdjoint c) (hcR : ‖c‖ ≤ R)
    (hmin : ∀ a : N.toStarSubalgebra, IsSelfAdjoint a → ‖a‖ ≤ R →
      τ.norm₂ (x-coordinateInclusion hNM c) ≤ τ.norm₂ (x-coordinateInclusion hNM a)) :
    coordinateInclusion hNM c ≤ algebraMap ℝ M.toStarSubalgebra ‖x‖ := by
  have hz := hmin (upperTruncate c ‖x‖) (upperTruncate_selfAdjoint c hc ‖x‖)
    (upperTruncate_norm_le c hc ‖x‖ R (norm_nonneg _) hcR)
  rw [included_upperTruncate hNM c hc] at hz
  have hd := upperTruncate_distance τ (coordinateInclusion hNM c) x
    (included_selfAdjoint hNM c hc) hx
  have hrev (a b : M.toStarSubalgebra) : τ.norm₂ (a-b)=τ.norm₂ (b-a) := norm_sub_rev _ _
  rw [hrev x,hrev x] at hz
  have he : τ.norm₂ ((coordinateInclusion hNM c-algebraMap ℝ M.toStarSubalgebra ‖x‖)⁺)=0 := by
    nlinarith [show 0 ≤ τ.norm₂ (coordinateInclusion hNM c-x) from norm_nonneg _,
      show 0 ≤ τ.norm₂ (upperTruncate (coordinateInclusion hNM c) ‖x‖-x) from norm_nonneg _,
      show 0 ≤ τ.norm₂ ((coordinateInclusion hNM c-algebraMap ℝ M.toStarSubalgebra ‖x‖)⁺) from norm_nonneg _]
  exact sub_nonpos.mp ((CFC.posPart_eq_zero_iff _
    ((included_selfAdjoint hNM c hc).sub (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all ‖x‖)))).mp
      ((τ.norm₂_eq_zero_iff _).mp he))

theorem selfAdjoint_ball_minimum_norm (τ : TracialRepresentation M) (hNM : N ≤ M)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (R : ℝ)
    (c : N.toStarSubalgebra) (hc : IsSelfAdjoint c) (hcR : ‖c‖ ≤ R)
    (hmin : ∀ a : N.toStarSubalgebra, IsSelfAdjoint a → ‖a‖ ≤ R →
      τ.norm₂ (x-coordinateInclusion hNM c) ≤ τ.norm₂ (x-coordinateInclusion hNM a)) :
    ‖c‖ ≤ ‖x‖ := by
  have hu := selfAdjoint_ball_minimum_upper τ hNM x hx R c hc hcR hmin
  have hn := selfAdjoint_ball_minimum_upper τ hNM (-x) hx.neg R (-c) hc.neg
    (by simpa using hcR) (by
      intro a ha hRa
      have h := hmin (-a) ha.neg (by simpa using hRa)
      have hneg (b : M.toStarSubalgebra) : τ.norm₂ (-b)=τ.norm₂ b := norm_neg _
      rw [map_neg,show -x- -(coordinateInclusion hNM c)=-(x-coordinateInclusion hNM c) by abel,
        show -x-coordinateInclusion hNM a=-(x-coordinateInclusion hNM (-a)) by rw [map_neg]; abel,
        hneg,hneg]
      exact h)
  rw [map_neg,norm_neg] at hn
  exact selfAdjoint_norm_le_of_bounds _ (included_selfAdjoint hNM c hc) ‖x‖ (norm_nonneg _) hu hn

end

/-! Two-sided spectral clipping and trace-norm control. The auxiliary trace
is explicit; the trace-free construction supplies it on its actual closure. -/
open scoped CStarAlgebra
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Expectations
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The orthogonal subalgebra representative of a self-adjoint ambient
operator is constructed, with its operator norm bound. -/
section
open scoped ComplexStarModule
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem exists_selfAdjoint_expectation (τ : TracialRepresentation M) (hNM : N ≤ M)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    ∃ c : N.toStarSubalgebra, IsSelfAdjoint c ∧ ‖c‖ ≤ ‖x‖ ∧
      TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) (x-coordinateInclusion hNM c) := by
  obtain ⟨c,hc,hcR,hmin,hvar⟩ := exists_selfAdjoint_ball_variational τ hNM x (‖x‖+1)
    (by positivity)
  have hcn := selfAdjoint_ball_minimum_norm τ hNM x hx (‖x‖+1) c hc hcR hmin
  let r := x-coordinateInclusion hNM c
  have hr : IsSelfAdjoint r := hx.sub (included_selfAdjoint hNM c hc)
  have hreal (a : N.toStarSubalgebra) (ha : IsSelfAdjoint a) :
      (τ.trace (coordinateInclusion hNM a*r)).re=0 := by
    let t : ℝ := 1/(‖a‖+1)
    have ht : 0<t := by dsimp [t]; positivity
    have hta : ‖t • a‖ ≤ 1 := by
      rw [norm_smul,Real.norm_of_nonneg ht.le]
      dsimp [t]
      rw [one_div_mul_eq_div,div_le_one (by positivity)]
      linarith [norm_nonneg a]
    have hp := hvar (c+t • a) (hc.add ((IsSelfAdjoint.all t).smul ha))
      ((norm_add_le _ _).trans (by linarith))
    have hm := hvar (c-t • a) (hc.sub ((IsSelfAdjoint.all t).smul ha))
      ((norm_sub_le _ _).trans (by linarith))
    have hep : c+t • a-c=t • a := by abel
    have hem : c-t • a-c=-(t • a) := by abel
    rw [hep,← Complex.coe_smul,map_smul,map_smul,inner_smul_right] at hp
    rw [hem,map_neg,map_neg,inner_neg_right,← Complex.coe_smul,map_smul,map_smul,inner_smul_right] at hm
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.neg_re] at hp hm
    change t*(inner ℂ (baseVector τ r) (baseVector τ (coordinateInclusion hNM a))).re ≤ 0 at hp
    change -(t*(inner ℂ (baseVector τ r) (baseVector τ (coordinateInclusion hNM a))).re) ≤ 0 at hm
    have hzero : (inner ℂ (baseVector τ r) (baseVector τ (coordinateInclusion hNM a))).re=0 := by
      nlinarith
    rw [baseVector_inner_trace,hr.star_eq,τ.trace_mul_comm] at hzero
    exact hzero
  have hSA (a : N.toStarSubalgebra) (ha : IsSelfAdjoint a) :
      τ.trace (coordinateInclusion hNM a*r)=0 :=
    Complex.ext (hreal a ha) (selfAdjoint_pairing_im τ _ r (included_selfAdjoint hNM a ha) hr)
  refine ⟨c,hc,hcn,?_⟩
  intro a
  let aN : N.toStarSubalgebra := ⟨(a : M.toStarSubalgebra).val,a.property⟩
  have hd := realPart_add_I_smul_imaginaryPart aN
  have he : (a : M.toStarSubalgebra)=coordinateInclusion hNM
      ((ℜ aN : N.toStarSubalgebra)+Complex.I • (ℑ aN : N.toStarSubalgebra)) := by
    rw [hd]; rfl
  change τ.trace ((a : M.toStarSubalgebra)*r)=0
  rw [he,map_add,map_smul,add_mul,smul_mul_assoc,cornerTrace_add,cornerTrace_smul,
    hSA _ (ℜ aN).property,hSA _ (ℑ aN).property,mul_zero,add_zero]

end

/-! A bounded trace-preserving subalgebra projection from self-adjoint least-distance points. Tracial orthogonality gives uniqueness and the bimodule identities. -/
section
open scoped ComplexStarModule
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_bounded_subalgebra_representative (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    ∃ y : M.toStarSubalgebra, y.val ∈ N ∧ ‖y‖ ≤ 2*‖x‖ ∧
      TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) (x-y) := by
  obtain ⟨a,ha,hna,hoa⟩ := exists_selfAdjoint_expectation τ hNM (ℜ x) (ℜ x).property
  obtain ⟨b,hb,hnb,hob⟩ := exists_selfAdjoint_expectation τ hNM (ℑ x) (ℑ x).property
  let y := coordinateInclusion hNM a+Complex.I • coordinateInclusion hNM b
  refine ⟨y,N.add_mem a.property (N.smul_mem b.property _),?_,?_⟩
  · calc ‖y‖ ≤ ‖a‖+‖b‖ := by
           change ‖y‖ ≤ ‖coordinateInclusion hNM a‖+‖coordinateInclusion hNM b‖
           simpa only [y,norm_smul,Complex.norm_I,one_mul] using
             norm_add_le (coordinateInclusion hNM a) (Complex.I • coordinateInclusion hNM b)
         _ ≤ 2*‖x‖ := by
           have hr := hna.trans (realPart.norm_le x)
           have hi := hnb.trans (imaginaryPart.norm_le x)
           linarith
  · have h := hoa.add τ (hob.smul τ Complex.I)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [y]
    rw [smul_sub]
    nth_rw 1 [← realPart_add_I_smul_imaginaryPart x]
    abel

def conditionalExpectation (hNM : N ≤ M) (x : M.toStarSubalgebra) : M.toStarSubalgebra :=
  (exists_bounded_subalgebra_representative τ hNM x).choose

end

/-! The constructed expectation preserves adjoints, is a bimodule map,
and is the orthogonal projection for the trace norm. -/

/-! Positivity of the constructed expectation. The negative spectral part
is an actual subalgebra test operator; tracial orthogonality eliminates it. -/

/-! The constructed expectation satisfies the Schwarz inequality and is
contractive in operator norm. -/

/-! Actual nested subalgebras satisfy the expectation tower identity.
The resulting energy identity is the decreasing-subfactor step of A.1.2. -/

/-! Conditional expectations onto a decreasing sequence of actual
subalgebras converge in L2. This supplies the limiting argument in A.1.2;
it does not construct that source's decreasing subfactors. -/
open Filter
open scoped Topology BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_MatrixAlgebras
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Equal-trace finite partitions extend to actual matrix units in the same
factor. The theorem also retains a prescribed corner as the sum of diagonals. -/
open scoped BigOperators

/-! The matrix-unit image in the original represented algebra, with its
finite dimensionality and weak-operator closedness proved. -/
open scoped BigOperators
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace MatrixUnitSystem
variable (E : Generator.MatrixUnitSystem ι M.toStarSubalgebra)

theorem concreteAlgebra_le : E.concreteAlgebra ≤ M.toStarSubalgebra := by
  rintro x ⟨a,rfl⟩
  exact (E.hom a).property

theorem mem_concreteAlgebra (x : M.toStarSubalgebra) :
    x.val ∈ E.concreteAlgebra ↔ x ∈ E.algebra := by
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a,Subtype.ext ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨a,congrArg Subtype.val ha⟩

instance concrete_finiteDimensional : FiniteDimensional ℂ E.concreteAlgebra := by
  change FiniteDimensional ℂ E.concreteHom.toAlgHom.range
  exact FiniteDimensional.of_surjective E.concreteHom.toAlgHom.rangeRestrict.toLinearMap
    E.concreteHom.toAlgHom.rangeRestrict_surjective

def wotLinearMap : Matrix ι ι ℂ →ₗ[ℂ] (H →WOT[ℂ] H) :=
  (ContinuousLinearMap.WOTofCLM.toLinearMap).comp E.concreteHom.toAlgHom.toLinearMap

theorem concreteAlgebra_wotClosed : WOTClosed E.concreteAlgebra := by
  have heq : {T : H →WOT[ℂ] H | T.toCLM ∈ E.concreteAlgebra} =
      (E.wotLinearMap.range : Set (H →WOT[ℂ] H)) := by
    ext T
    constructor
    · rintro ⟨a,ha⟩
      exact ⟨a, congrArg ContinuousLinearMapWOT.ofCLM ha⟩
    · rintro ⟨a,ha⟩
      exact ⟨a,congrArg ContinuousLinearMapWOT.toCLM ha⟩
  unfold WOTClosed
  rw [heq]
  exact E.wotLinearMap.range.closed_of_finiteDimensional

end MatrixUnitSystem

end

/-! The actual relative commutant in M is a diffuse scalar-center von
Neumann algebra, with the restricted faithful trace available from M. -/
namespace MatrixUnitSystem

/-! Passing an irreducible inclusion through a common finite matrix algebra
preserves irreducibility of the actual relative commutants. -/
variable {ι A B : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]

open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}
variable (E : MatrixUnitSystem ι N.toStarSubalgebra) (hNM : N ≤ M)

theorem relative_inclusion :
    E.relativeVonNeumann ≤ (E.map (coordinateInclusion hNM)).relativeVonNeumann := by
  intro x hx
  have h := (E.relativeStar_mem x).mp hx
  apply ((E.map (coordinateInclusion hNM)).relativeStar_mem x).mpr
  exact ⟨hNM h.1,h.2⟩

end MatrixUnitSystem

/-! Explicit Bell projections in two equal finite matrix factors. -/
open scoped BigOperators

/-! Exact normalized traces of constructed matrix algebras and all their
commuting product refinements. -/
open scoped BigOperators

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_MatrixSequence
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Finite matrix stages and a quantified refinement operation, including
zero expectation. Reindexing changes no represented algebra. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace FiniteMatrixStage
open Tracial
variable {N M : VonNeumannAlgebra H}

def energy (E : FiniteMatrixStage N) (τ : TracialRepresentation M) (hNM : N ≤ M)
    (x : M.toStarSubalgebra) : ℝ :=
  τ.norm₂ (conditionalExpectation τ (E.commutant_le hNM) x)^2

end FiniteMatrixStage

end

/-! Iterated compatible full matrix refinements attain every positive
finite-family commutant expectation budget. The reduction factor is proved. -/

/-! L2 separability supplies a countable centered dense family. The constructed
matrix sequence has scalar common relative commutant in the ambient algebra. -/

/-! The actual weakly closed star algebra generated by the increasing finite
matrix stages. Its ambient relative commutant is scalar. This does not yet
package a diffuse II1 subfactor or derive the representation hypotheses. -/

/-! The constructed matrix-generated weak closure is an actual II1 factor.
Its bundled von Neumann algebra and faithful trace use the same operators. -/
section
namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def generatedVonNeumann (A : ℕ → FiniteMatrixStage N) : VonNeumannAlgebra H :=
  vonNeumannOfWOTClosed (generated A) (generated_closed A)

end FiniteMatrixStage

end

/-! Finite matrix stages strongly approximate the actual weakly generated
algebra. The approximants here have no operator norm bound. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {N M : VonNeumannAlgebra H}

def stageUnion (A : ℕ → FiniteMatrixStage N) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  ⨆ n,(A n).units.concreteAlgebra

end FiniteMatrixStage

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_MatrixExpectation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Construct contractive expectations onto the actual finite matrix stages.
For every element of their weak closure, these expectations converge in L2
and remain in its operator norm ball. -/
open Filter
open scoped Topology
namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def stageVonNeumann (E : FiniteMatrixStage N) : VonNeumannAlgebra H :=
  vonNeumannOfWOTClosed E.units.concreteAlgebra E.units.concreteAlgebra_wotClosed

theorem stageVonNeumann_le (E : FiniteMatrixStage N) : E.stageVonNeumann ≤ N :=
  E.units.concreteAlgebra_le

def stageExpectation (E : FiniteMatrixStage N) (τ : TracialRepresentation M) (hNM : N ≤ M)
    (x : M.toStarSubalgebra) : M.toStarSubalgebra :=
  conditionalExpectation τ (E.stageVonNeumann_le.trans hNM) x

end FiniteMatrixStage

/-! Construct scalarizing partitions for an actual finite matrix algebra
inside a diffuse finite factor. No chain or pinching hypothesis is assumed. -/

/-! Finite matrix approximation and Bell partitions give actual small
pinching energy. The commuting matrix factor is constructed, not assumed. -/
open Filter
open scoped BigOperators Topology
namespace FiniteMatrixStage

section
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N : VonNeumannAlgebra H}

/-- View the same finite matrix stage inside any algebra containing it. -/
def restrictStage (E : FiniteMatrixStage N) (R : VonNeumannAlgebra H)
    (hER : E.units.concreteAlgebra ≤ R.toStarSubalgebra) : FiniteMatrixStage R where
  size := E.size
  positive := E.positive
  units := {
    entry := fun i j => ⟨(E.units.entry i j).val,
      hER ((E.units.mem_concreteAlgebra _).mpr (E.units.entry_mem i j))⟩
    star_entry := fun i j => Subtype.ext (congrArg (fun x : N.toStarSubalgebra => x.val) (E.units.star_entry i j))
    mul_entry := fun i j k l => by
      apply Subtype.ext
      simpa only [MulMemClass.coe_mul,ZeroMemClass.coe_zero,Subtype.coe_mk,
        apply_ite Subtype.val] using congrArg (fun x : N.toStarSubalgebra => x.val) (E.units.mul_entry i j k l)
    total := by
      apply Subtype.ext
      have h := congrArg (fun x : N.toStarSubalgebra => x.val) E.units.total
      change R.toStarSubalgebra.subtype (∑ i,_) = 1
      rw [map_sum]
      change N.toStarSubalgebra.subtype (∑ i,E.units.entry i i)=1 at h
      rw [map_sum] at h
      exact h }

end

/-! Countably many finite matrix algebras give L2 separability of their weak closure. -/
open UltrapowerBridge Tracial

end FiniteMatrixStage

/-! The actual finite-stage conditional expectations converge strongly and
adjoint-strongly on every vector in the given representation. The generated
algebra also has a constructed separable faithful cyclic Hilbert representation. -/
open Filter
open scoped Topology

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_HaarPatches
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The same ordered signed words in any star algebra, with exact transport
through bounded sequence evaluation and the actual quotient homomorphism. -/

/-! The finite-error f=1 conclusion of Popa Lemma 3.2, for the irreducible
scalar-commutant inclusion with the explicit represented-factor hypotheses. -/

/-! A countable diagonal construction with actual vanishing ordered moments.
The countable coefficients may vary with the sequence coordinate. -/
open Filter
open scoped Topology

/-! Actual positive-support partial independence in the bounded-sequence
tracial quotient. Freeness is expressed by domination of atTop. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def boundedPartialUnitary (v : ℕ → PartialUnitary M) : Bounded M :=
  ⟨fun j => (v j).val,1,zero_le_one,fun j => (v j).unitary.norm_le_one⟩

def boundedPartialSupport (v : ℕ → PartialUnitary M) : Bounded M :=
  ⟨fun j => (v j).support.val,1,zero_le_one,fun j => (v j).support.property.norm_le⟩

end

/-! Exact multilinearity factors for ordered words; no factors are inverted
and signs affect only the partial-unitary letters. -/

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_QuotientHilbert
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The actual trace Hilbert completion of the bounded-sequence tracial quotient.
The vector-trace representation is explicit data; its existence for an arbitrary
factor is not asserted here. No free-independence premise occurs. -/
open Filter
open scoped Topology ComplexConjugate
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

abbrev Q := TracialQuotient τ (ω : Filter ℕ)

@[simp] theorem trace_add (a b : Q τ ω) :
    quotientTrace τ ω (a+b) = quotientTrace τ ω a + quotientTrace τ ω b := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      apply tendsto_nhds_unique (traceRep_tendsto τ ω (a+b))
      change Tendsto (fun n => τ.trace (a.val n + b.val n)) _
        (𝓝 (traceRep τ ω a + traceRep τ ω b))
      simpa only [TracialRepresentation.trace_add] using
        (traceRep_tendsto τ ω a).add (traceRep_tendsto τ ω b)

@[simp] theorem trace_smul (c : ℂ) (a : Q τ ω) :
    quotientTrace τ ω (c • a) = c * quotientTrace τ ω a := by
  induction a using Quotient.inductionOn with
  | h a =>
    apply tendsto_nhds_unique (traceRep_tendsto τ ω (c • a))
    change Tendsto (fun n => τ.trace (c • a.val n)) _ (𝓝 (c * traceRep τ ω a))
    simpa only [TracialRepresentation.trace_smul] using
      (traceRep_tendsto τ ω a).const_mul c

end

/-! Centering actual bounded representatives changes no centered quotient
class. Every such class is a nonzero scalar multiple of a coordinatewise
centered contraction representative. -/
open Filter
open scoped Topology

/-! Trace Cauchy–Schwarz and unitary invariance on the tracial quotient. -/
open Filter
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end


