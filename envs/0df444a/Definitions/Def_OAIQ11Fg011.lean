-- Prove2me | Definitions.Def_OAIQ11Fg011
-- name    : OAIQ11Fg011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T09:47:01.788227+00:00
-- url     : https://prove2.me/theorems/35f87701-fdfb-431c-ac35-25aa7ef63e81
-- title:
--   Definitions bundle OAIQ11Fg011 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 34 declarations of OpenAI's Lean: 12 definitions, 2 instances and 20 theorems. The definitions and types are `OAI.Generator.Tracial.L2`, `OAI.Generator.Tracial.boundedMap`, `OAI.Generator.Tracial.constantQuotient`, `OAI.Generator.Tracial.constantSequence`, `OAI.Generator.Tracial.inclusion`, `OAI.Generator.Tracial.quotientInnerCore`, `OAI.Generator.Tracial.sequenceInclusion`, `OAI.Generator.Tracial.sequenceQuotient`, `OAI.Generator.Tracial.traceFreeDimension`, `OAI.Generator.Tracial.traceFreeDyadicCut`, `OAI.Generator.Tracial.traceFreeDyadicSup`, `OAI.Generator.Tracial.traceLinear`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_Dimension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/Dimension.lean), [`FactorGeneration_DyadicComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/DyadicComparison.lean), [`FactorGeneration_QuotientHilbert`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/QuotientHilbert.lean), [`FactorGeneration_QuotientRepresentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/QuotientRepresentation.lean).
--
--   **Imports.** It imports the bundles `OAIQ11Fg007` and `OAIQ11Fg008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ11Fg013` and `OAIQ11Fg014`; the statements `OAI_Generator_Tracial_absorbedGapList_reduced`, `OAI_Generator_Tracial_conjugateGaps_reduced`, `OAI_Generator_Tracial_exactOrderedMoments_core`, `OAI_Generator_Tracial_exact_moment_of_cyclic_family`, `OAI_Generator_Tracial_exists_full_support_ordered_independence`, `OAI_Generator_Tracial_integerWord_closed_endpoints`, `OAI_Generator_Tracial_maximal_word_gaps`, `OAI_Generator_Tracial_productGapList_members`, `OAI_Generator_Tracial_product_reduced_moment`, `OAI_Generator_Tracial_reducedOrderedMoments_haar`, `OAI_Generator_Tracial_reducedOrderedMoments_integerWord`, `OAI_Generator_Tracial_reduced_integer_gap_functional`, `OAI.Generator.Tracial.select_coordinate_with_bounds`, `OAI_Generator_Tracial_signedReducedGaps_blocks`, `OAI_Generator_Tracial_signedReducedGaps_integer` and `OAI_Generator_Tracial_signedReducedGaps_repeat`; the proofs of `OAI_Generator_Tracial_HaarEndpoints_negative_conjugate_correlation`, `OAI_Generator_Tracial_HaarEndpoints_positive_conjugate_correlation`, `OAI_Generator_Tracial_absorbedGapList_reduced`, `OAI_Generator_Tracial_conjugateGaps_reduced`, `OAI_Generator_Tracial_exactOrderedMoments_core`, `OAI_Generator_Tracial_exact_moment_of_cyclic_family`, `OAI_Generator_Tracial_exists_coordinate_haar_endpoints`, `OAI_Generator_Tracial_integerWord_closed_endpoints`, `OAI_Generator_Tracial_maximal_word_gaps`, `OAI_Generator_Tracial_productGapList_members`, `OAI_Generator_Tracial_product_reduced_moment`, `OAI_Generator_Tracial_reducedOrderedMoments_haar`, `OAI_Generator_Tracial_reducedOrderedMoments_integerWord`, `OAI_Generator_Tracial_reduced_integer_gap_functional`, `OAI_Generator_Tracial_signedReducedGaps_blocks`, `OAI_Generator_Tracial_signedReducedGaps_integer`, `OAI_Generator_Tracial_signedReducedGaps_repeat` and `OAI_Generator_Tracial_successive_reduced_word_zero`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ11Fg007
import Definitions.Def_OAIQ11Fg008

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

theorem subset_val (E : EquivalentPartition p ι) (s : Finset ι) :
    (E.subset s).val=∑ i ∈ s, (E.leg i).target.val := rfl

theorem subset_le_iff (E : EquivalentPartition p ι) (s : Finset ι) (q : AlgebraProjection M) :
    E.subset s ≤ q ↔ ∀ i ∈ s, (E.leg i).target ≤ q :=
  AlgebraProjection.finsetSum_le_iff _ _ _ _

theorem subset_le (E : EquivalentPartition p ι) (s : Finset ι) : E.subset s ≤ p :=
  (E.subset_le_iff s p).mpr (fun i _ => E.bound i)

theorem subset_mono (E : EquivalentPartition p ι) {s t : Finset ι} (h : s ⊆ t) :
    E.subset s ≤ E.subset t :=
  (E.subset_le_iff s _).mpr (fun i hi => (E.subset_le_iff t _).mp le_rfl i (h hi))

theorem subset_empty (E : EquivalentPartition p ι) : (E.subset ∅).val=0 := by
  simp only [subset_val,Finset.sum_empty]

/-! Exact finite cardinal comparison of sums of equivalent nonzero projections.
Finiteness prevents a larger collection from embedding in a smaller one. -/

theorem subset_mul_piece_of_not_mem (E : EquivalentPartition p ι) (s : Finset ι)
    (i : ι) (hi : i ∉ s) : (E.subset s).val*(E.leg i).target.val=0 := by
  rw [subset_val,Finset.sum_mul]
  exact Finset.sum_eq_zero (fun j hj => E.orthogonal j i (fun h => hi (h ▸ hj)))

end EquivalentPartition
end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Dimension
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Archimedean comparison for the constructed dyadic reference projections.
Orthogonal sibling corners supply copies for the finite-algebra shift argument. -/

/-! Finite rounding by actual subset projections. A maximal fitting subset
leaves a remainder smaller in comparison than any unused equivalent piece. -/
namespace Tracial

section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-! The dyadic lower cut on projections below p and its normalized faithful monotone supremum, capped at one. -/

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

/-- Membership contains an actual partial-isometry witness through Subequivalent. -/
def traceFreeDyadicCut (p q : AlgebraProjection M) : Set ℝ :=
  {x | ∃ n, ∃ s : Finset (DyadicIndex n),
    ((traceFreeDyadicPartition hfactor hdiff p n).subset s).Subequivalent q ∧
      x=dyadicWeight n s}

def traceFreeDyadicSup (p q : AlgebraProjection M) : ℝ :=
  sSup (traceFreeDyadicCut hfactor hdiff p q)

theorem traceFreeDyadicCut_bddAbove (p q : AlgebraProjection M) :
    BddAbove (traceFreeDyadicCut hfactor hdiff p q) := by
  refine ⟨1,?_⟩
  rintro x ⟨n,s,_,rfl⟩
  exact dyadicWeight_le_one n s

end

/-! Common refinements compare arbitrary dyadic levels. The supremum takes
the exact dyadic value on every reference subset projection, and finite
rounding bounds every projection with an explicit error at each level. -/

/-! Orthogonal lower approximants fit disjoint collections of the reference
pieces. Equivalent complements and finite cancellation enforce the capacity. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι : Type*} [Fintype ι]

theorem subset_complement [DecidableEq ι] (E : EquivalentPartition p ι) (s : Finset ι) :
    E.subset (Finset.univ \ s)=AlgebraProjection.remainder (E.subset s) p (E.subset_le s) := by
  classical
  apply Subtype.ext
  change (∑ i ∈ Finset.univ \ s, (E.leg i).target.val)=p.val-(E.subset s).val
  rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ s),E.total]
  rfl

end EquivalentPartition
end

/-! Orthogonal additivity of the constructed dyadic dimension. Numerical
rounding errors tend to zero; every lower and upper bound uses actual
partial-isometry witnesses in the original finite diffuse factor. -/

end Tracial

/-! Classification of projection comparison by the constructed finite
dimension, and a wrapper for exactly the original IsII1Factor predicate.
No normality or trace-extension claim is made here. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Tracial
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

/-- The same constructed lower cut, now normalized at the algebra identity. -/
def traceFreeDimension (q : AlgebraProjection M) : ℝ :=
  traceFreeDyadicSup hfactor hdiff ⟨1,IsStarProjection.one _⟩ q

end Tracial

end

/-! Bounds and concrete dyadic upper approximants for the constructed
projection dimension. These finite estimates do not assume continuity. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_QuotientHilbert
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
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

def traceLinear : Q τ ω →ₗ[ℂ] ℂ where
  toFun := quotientTrace τ ω
  map_add' := trace_add τ ω
  map_smul' := trace_smul τ ω

theorem trace_pair (a b : M.toStarSubalgebra) :
    τ.trace (star a*b) = inner ℂ ((a : H →L[ℂ] H) τ.vector)
      ((b : H →L[ℂ] H) τ.vector) := by
  unfold TracialRepresentation.trace
  change inner ℂ τ.vector ((star (a : H →L[ℂ] H)) ((b : H →L[ℂ] H) τ.vector)) = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

theorem trace_pair_conj (a b : Q τ ω) :
    star (quotientTrace τ ω (star b*a)) = quotientTrace τ ω (star a*b) := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      change star (traceRep τ ω (star b*a)) = traceRep τ ω (star a*b)
      apply tendsto_nhds_unique ((traceRep_tendsto τ ω (star b*a)).star)
      have ht := traceRep_tendsto τ ω (star a*b)
      change Tendsto (fun n => τ.trace (star (a.val n)*b.val n)) _ _ at ht
      change Tendsto (fun n => star (τ.trace (star (b.val n)*a.val n))) _ _
      convert ht using 1
      all_goals try with_reducible_and_instances rfl
      funext n
      simp only [trace_pair]
      exact inner_conj_symm _ _

theorem trace_square_nonneg (a : Q τ ω) :
    0 ≤ (quotientTrace τ ω (star a*a)).re := by
  induction a using Quotient.inductionOn with
  | h a =>
    have ht := Complex.continuous_re.continuousAt.tendsto.comp (traceRep_tendsto τ ω (star a*a))
    change 0 ≤ (traceRep τ ω (star a*a)).re
    apply ge_of_tendsto ht
    exact Eventually.of_forall (fun n => by
      change 0 ≤ (τ.trace (star (a.val n)*a.val n)).re
      rw [τ.trace_star_mul]
      simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using sq_nonneg (τ.norm₂ (a.val n)))

/-- The quotient two-norm is the ultralimit of the coordinate two-norms. -/
theorem norm₂_tendsto (a : Bounded M) :
    Tendsto (fun n => τ.norm₂ (a.val n)) (ω : Filter ℕ)
      (𝓝 (Real.sqrt (quotientTrace τ ω (star (quotientMap τ (ω : Filter ℕ) a) *
        quotientMap τ (ω : Filter ℕ) a)).re)) := by
  change Tendsto (fun n => τ.norm₂ (a.val n)) (ω : Filter ℕ)
    (𝓝 (Real.sqrt (traceRep τ ω (star a*a)).re))
  have ht := (Complex.continuous_re.continuousAt.tendsto.comp (traceRep_tendsto τ ω (star a*a))).sqrt
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  change τ.norm₂ (a.val n) = Real.sqrt (τ.trace (star (a.val n)*a.val n)).re
  rw [τ.trace_star_mul, ← Complex.ofReal_pow, Complex.ofReal_re]
  exact (Real.sqrt_sq (show 0 ≤ τ.norm₂ (a.val n) from norm_nonneg _)).symm

theorem trace_square_faithful (a : Q τ ω)
    (ha : quotientTrace τ ω (star a*a) = 0) : a = 0 := by
  induction a using Quotient.inductionOn with
  | h a =>
    change quotientMap τ (ω : Filter ℕ) a = quotientMap τ (ω : Filter ℕ) 0
    apply (quotientMap_eq_iff τ (ω : Filter ℕ) a 0).mpr
    have ht := norm₂_tendsto τ ω a
    change quotientTrace τ ω (star (quotientMap τ (ω : Filter ℕ) a) *
      quotientMap τ (ω : Filter ℕ) a) = 0 at ha
    simpa [TraceRel, ha] using ht

/-- The norm here is the trace norm, not the operator norm. -/
@[instance_reducible] def quotientInnerCore : InnerProductSpace.Core ℂ (Q τ ω) where
  inner a b := quotientTrace τ ω (star a*b)
  conj_inner_symm := trace_pair_conj τ ω
  re_inner_nonneg := trace_square_nonneg τ ω
  add_left a b c := by simp only [star_add, add_mul, trace_add]
  smul_left a b c := by simp only [star_smul, smul_mul_assoc, trace_smul]; rfl
  definite := trace_square_faithful τ ω

instance quotientNormedAddCommGroup : NormedAddCommGroup (Q τ ω) :=
  (quotientInnerCore τ ω).toNormedAddCommGroup
instance quotientInnerProductSpace : InnerProductSpace ℂ (Q τ ω) :=
  .ofCore { quotientInnerCore τ ω with }

@[simp] theorem inner_eq_trace (a b : Q τ ω) :
    inner ℂ a b = quotientTrace τ ω (star a*b) := rfl

/-- Genuine complete complex Hilbert space for the quotient trace. -/
abbrev L2 := UniformSpace.Completion (Q τ ω)

def inclusion : Q τ ω →ₗᵢ[ℂ] L2 τ ω :=
  UniformSpace.Completion.toComplₗᵢ

@[simp] theorem inclusion_inner (a b : Q τ ω) :
    inner ℂ (inclusion τ ω a) (inclusion τ ω b) = quotientTrace τ ω (star a*b) := by
  exact UniformSpace.Completion.inner_coe (𝕜 := ℂ) a b

end

/-! Centering actual bounded representatives changes no centered quotient
class. Every such class is a nonzero scalar multiple of a coordinatewise
centered contraction representative. -/
open Filter
open scoped Topology

/-! Trace Cauchy–Schwarz and unitary invariance on the tracial quotient. -/
open Filter
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

@[simp] theorem quotient_norm_one : ‖(1 : Q τ ω)‖ = 1 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_eq_trace, star_one, one_mul, quotientTrace_one]
  norm_num

@[simp] theorem quotient_trace_sub (a b : Q τ ω) :
    quotientTrace τ ω (a-b) = quotientTrace τ ω a-quotientTrace τ ω b :=
  (traceLinear τ ω).map_sub a b

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_QuotientRepresentation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Complete operator-norm bounded sequences and their contractive map to the
actual quotient trace Hilbert space. This map is not asserted injective. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

/-- Forget continuity (automatic on the discrete index set) and retain boundedness. -/
def boundedMap : Sequences M →⋆ₐ[ℂ] Bounded M where
  toFun a := ⟨a, ⟨‖a‖, norm_nonneg a, a.norm_coe_le_norm⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

/-- The actual star-algebra quotient map on complete bounded sequences. -/
def sequenceQuotient : Sequences M →⋆ₐ[ℂ] Q τ ω :=
  (quotientStarAlgHom τ (ω : Filter ℕ)).comp boundedMap

theorem sequence_norm_tendsto (a : Sequences M) :
    Tendsto (fun n => τ.norm₂ (a n)) (ω : Filter ℕ) (𝓝 ‖sequenceQuotient τ ω a‖) := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_eq_trace]
  exact norm₂_tendsto τ ω (boundedMap a)

theorem sequenceQuotient_norm_le (a : Sequences M) :
    ‖sequenceQuotient τ ω a‖ ≤ ‖a‖ := by
  apply le_of_tendsto (sequence_norm_tendsto τ ω a)
  exact Eventually.of_forall (fun n => (τ.norm₂_le_norm (a n)).trans (a.norm_coe_le_norm n))

/-- The continuous Hilbert realization used by the analytic remainder theorem. -/
def sequenceInclusion : Sequences M →L[ℂ] L2 τ ω :=
  LinearMap.mkContinuous
    { toFun := fun a => inclusion τ ω (sequenceQuotient τ ω a)
      map_add' := by intros; simp only [map_add]
      map_smul' := by intros; simp only [map_smul]; rfl } 1
    (by
      intro a
      change ‖inclusion τ ω (sequenceQuotient τ ω a)‖ ≤ 1*‖a‖
      rw [LinearIsometry.norm_map, one_mul]
      exact sequenceQuotient_norm_le τ ω a)

@[simp] theorem sequenceInclusion_apply (a : Sequences M) :
    sequenceInclusion τ ω a = inclusion τ ω (sequenceQuotient τ ω a) := rfl

end

/-! The faithful constant embedding into the tracial quotient, with its trace and trace norm, for every ultrafilter. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def constantSequence : M.toStarSubalgebra →⋆ₐ[ℂ] Sequences M where
  toFun := BoundedContinuousFunction.const ℕ
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

def constantQuotient : M.toStarSubalgebra →⋆ₐ[ℂ] Q τ ω :=
  (sequenceQuotient τ ω).comp constantSequence

end

/-! Left multiplication by bounded representatives on the completed trace
Hilbert space. The quotient ideal, not an assumed operator action, determines
which representatives induce the same operator. -/
open Filter
open scoped Topology

/-! Faithful concrete Hilbert-space representation of the tracial quotient
star algebra. Weak operator closedness of its image is not claimed here. -/
open Filter
open scoped Topology

/-! The standard completion/continuous-linear-map structures are not new hypotheses. -/

/-! Fixed-index selection for bounded coordinate representatives. -/
open Filter
open scoped Topology
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end


