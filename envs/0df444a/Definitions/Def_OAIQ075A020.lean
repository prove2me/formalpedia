-- Prove2me | Definitions.Def_OAIQ075A020
-- name    : OAIQ075A020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T08:14:59.594999+00:00
-- url     : https://prove2.me/theorems/45d53921-8015-4c33-9b53-4c3afa1f4743
-- title:
--   Definitions bundle OAIQ075A020 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 26 declarations of OpenAI's Lean: 3 definitions and 23 theorems. The definitions and types are `OAI.Generator.MatrixUnitSystem.relativeEquiv`, `OAI.Generator.Tracial.traceOrbitHull`, `OAI.HochschildPatching.evaluatedTail`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`BoundedHochschild_MixedWords`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoundedHochschild/MixedWords.lean), [`BoundedHochschild_PartialUnitaries`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoundedHochschild/PartialUnitaries.lean), [`FactorGeneration_MatrixAlgebras`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/MatrixAlgebras.lean), [`FactorGeneration_MatrixRefinement`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/MatrixRefinement.lean), [`FactorGeneration_PartialIsometries`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/PartialIsometries.lean), [`FactorGeneration_Supports`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/Supports.lean), [`FactorGeneration_TraceTopology`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/TraceTopology.lean), [`FactorGeneration_UniformPartitions`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/UniformPartitions.lean).
--
--   **Imports.** It imports the bundles `OAIQ075A013`, `OAIQ075A014` and `OAIQ075A015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ075A026` and `OAIQ075A027`; the statement `OAI_KadisonSimilarity_projection_tendsto_zero_of_normal_geometry`; the proofs of `OAI_KadisonSimilarity_exists_corner_intertwiner_of_column_tests` and `OAI_KadisonSimilarity_projection_tendsto_zero_of_normal_geometry`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ075A013
import Definitions.Def_OAIQ075A014
import Definitions.Def_OAIQ075A015

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PartialUnitaries
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partial unitaries, ordered limits and trace estimates. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open Filter Topology
open scoped ComplexOrder
namespace HochschildComparison
open BoundedHochschild
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

namespace PartialUnitary



section
omit [PartialOrder M] [StarOrderedRing M]

lemma norm_power_le_one (v : PartialUnitary M) (k : Bool × ℕ) : ‖v.power k‖≤1 := by
  apply (norm_pow_le' _ (Nat.succ_pos _)).trans
  apply pow_le_one₀ (norm_nonneg _)
  split <;> simpa only [norm_star] using v.norm_le_one
end

end PartialUnitary
end HochschildComparison

 

 

open Filter Topology
open scoped ComplexOrder







open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_MixedWords
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mixed-word Taylor expansions, moment corners and patch coefficients. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open Filter Topology
open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison
variable {M : Type*} [CStarAlgebra M]


variable {I : Type*} (F : I → M)

def evaluatedTail {K : ℕ} (l : List (WordAtom I K)) : List ((Bool × ℕ) × M) :=
  l.map (fun ka => ((ka.1.1,ka.1.2.val),wordCoeff F ka.2))
end HochschildPatching

 

 

open scoped ComplexOrder





open Filter Topology
open scoped ComplexOrder





open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_TraceTopology
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Operator-norm bounded trace-norm limits remain in the same ball of the algebra, without requiring a cyclic trace vector. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-! The actual closed convex unitary orbit in the coordinate trace Hilbert
space, with bounded representatives and conjugation invariance. -/

def traceOrbitHull (G : Subgroup (unitary M.toStarSubalgebra)) (b : M.toStarSubalgebra) : Set H :=
  closure (convexHull ℝ (baseVector τ '' algebraOrbit G b))

end

/-! The least-norm point of the actual orbit hull is represented in M and
fixed by every conjugating unitary; its trace and distance bounds are retained. -/
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem baseVector_injective : Function.Injective (baseVector τ) := by
  intro a b h
  apply sub_eq_zero.mp
  apply τ.separating
  change baseVector τ (a-b) = 0
  rw [map_sub, h, sub_self]

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_PartialIsometries
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual partial isometries, allowing distinct initial and final projections,
with the extension order and its exact trace distance. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace PartialIsometry

theorem distance_sq (τ : TracialRepresentation M) {v w : PartialIsometry M} (h : v ≤ w) :
    τ.norm₂ (w.val-v.val)^2=(τ.trace w.support.val).re-(τ.trace v.support.val).re := by
  have he := congrArg Complex.re (τ.trace_star_mul (w.val-v.val))
  rw [difference_square h,trace_sub,Complex.sub_re] at he
  simpa only [← Complex.ofReal_pow,Complex.ofReal_re] using he.symm

theorem support_trace_mono (τ : TracialRepresentation M) {v w : PartialIsometry M} (h : v ≤ w) :
    (τ.trace v.support.val).re ≤ (τ.trace w.support.val).re := by
  have he := distance_sq τ h
  nlinarith [sq_nonneg (τ.norm₂ (w.val-v.val))]

end PartialIsometry

end

/-! Actual L2 limits of partial isometries and upper bounds of increasing
sequences, using their exact support-trace distance. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
namespace PartialIsometry

theorem support_trace_le_one (v : PartialIsometry M) : (τ.trace v.support.val).re ≤ 1 := by
  rw [projection_trace_sq τ _ v.support.property]
  have h := (τ.norm₂_le_norm v.support.val).trans v.support.property.norm_le
  nlinarith [show 0 ≤ τ.norm₂ v.support.val from norm_nonneg _]

theorem monotone_cauchy (a : ℕ → PartialIsometry M) (ha : Monotone a) :
    CauchySeq (fun n => ((a n).val : H →L[ℂ] H) τ.vector) := by
  let t : ℕ → ℝ := fun n => (τ.trace (a n).support.val).re
  have ht : Monotone t := fun i j hij => support_trace_mono τ (ha hij)
  have hb : BddAbove (Set.range t) := ⟨1,by rintro _ ⟨n,rfl⟩; exact support_trace_le_one τ (a n)⟩
  have hc := tendsto_atTop_ciSup ht hb
  apply Metric.cauchySeq_iff'.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hc (Ioi_mem_nhds (show (⨆ n, t n)-ε^2 < ⨆ n,t n by nlinarith)))
  refine ⟨N,fun n hn => ?_⟩
  have hupper : t n ≤ ⨆ n,t n := le_ciSup hb n
  have hsmall : (⨆ n,t n)-ε^2 < t N := hN N le_rfl
  have he := distance_sq τ (ha hn)
  change τ.norm₂ ((a n).val-(a N).val)^2=t n-t N at he
  rw [dist_eq_norm]
  change τ.norm₂ ((a n).val-(a N).val)<ε
  nlinarith [show 0 ≤ τ.norm₂ ((a n).val-(a N).val) from norm_nonneg _]

/-- Closedness of actual partial isometries in the operator norm unit ball
for L2 convergence. -/
theorem of_L2_limit (a : ℕ → PartialIsometry M) (b : M.toStarSubalgebra)
    (hb : Tendsto (fun n => τ.norm₂ ((a n).val-b)) atTop (𝓝 0)) :
    ∃ v : PartialIsometry M, v.val=b := by
  let p : M.toStarSubalgebra := star b*b
  have hp : Tendsto (fun n => τ.norm₂ ((a n).support.val-p)) atTop (𝓝 0) := by
    have ht := norm₂_limit_mul τ (fun n => star (a n).val) (fun n => (a n).val)
      (star b) b 1 (fun n => (a n).adjoint.norm_le_one)
      (norm₂_limit_star τ _ _ hb) hb
    simpa only [(a _).initial] using ht
  have hproj : IsStarProjection p := by
    constructor
    · have ht := norm₂_limit_mul τ (fun n => (a n).support.val) (fun n => (a n).support.val)
        p p 1 (fun n => (a n).support.property.norm_le) hp hp
      have ht' : Tendsto (fun n => τ.norm₂ ((a n).support.val-p*p)) atTop (𝓝 0) := by
        simpa only [(a _).support.property.isIdempotentElem.eq] using ht
      exact norm₂_limit_unique τ _ ht' hp
    · change star (star b*b)=star b*b
      simp only [star_mul,star_star]
  exact ⟨⟨⟨p,hproj⟩,b,rfl⟩,rfl⟩

/-- A bounded L2 limit retains every eventually fixed extension. -/
theorem le_of_eventually_le_limit (a : ℕ → PartialIsometry M) (v w : PartialIsometry M)
    (hv : Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0))
    (hw : ∀ᶠ n in atTop, w ≤ a n) : w ≤ v := by
  have ht := norm₂_limit_mul τ (fun n => (a n).val) (fun _ => w.support.val)
    v.val w.support.val 1 (fun n => (a n).norm_le_one) hv
    (by simp only [sub_self,TracialRepresentation.norm₂_zero]; exact tendsto_const_nhds)
  have hc : Tendsto (fun n => τ.norm₂ ((a n).val*w.support.val-w.val)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hw] with n hn
    rw [show (a n).val*w.support.val=w.val from hn,sub_self,τ.norm₂_zero]
  exact norm₂_limit_unique τ _ ht hc

theorem monotone_limit (a : ℕ → PartialIsometry M) (ha : Monotone a) :
    ∃ v : PartialIsometry M, (∀ n, a n ≤ v) ∧
      Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0) := by
  obtain ⟨ξ,hξ⟩ := cauchySeq_tendsto_of_complete (monotone_cauchy τ a ha)
  obtain ⟨b,hb,hbξ⟩ := bounded_trace_limit τ (fun n => (a n).val) 1 (by norm_num)
    (fun n => (a n).norm_le_one) ξ hξ
  have ht : Tendsto (fun n => τ.norm₂ ((a n).val-b)) atTop (𝓝 0) := by
    apply (tendsto_vector_iff_norm₂ τ atTop _ b).mp
    simpa only [hbξ] using hξ
  obtain ⟨v,hv⟩ := of_L2_limit τ a b ht
  rw [← hv] at ht
  refine ⟨v,fun n => ?_,ht⟩
  apply le_of_eventually_le_limit τ a v (a n) ht
  exact (eventually_ge_atTop n).mono (fun m hm => ha hm)

/-! Every nonempty chain of actual partial isometries has an upper bound which
is an L2 limit of a sequence from the chain. This is the analytic chain
construction underlying the projection-comparison Zorn argument. -/

theorem eq_of_le_of_trace_eq {v w : PartialIsometry M} (h : v ≤ w)
    (ht : (τ.trace v.support.val).re=(τ.trace w.support.val).re) : v=w := by
  have he := distance_sq τ h
  rw [ht,sub_self] at he
  have hz := (τ.norm₂_eq_zero_iff _).mp (sq_eq_zero_iff.mp he)
  exact ext (sub_eq_zero.mp hz).symm

theorem support_limit (a : ℕ → PartialIsometry M) (v : PartialIsometry M)
    (hv : Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0)) :
    Tendsto (fun n => τ.norm₂ ((a n).support.val-v.support.val)) atTop (𝓝 0) := by
  have ht := norm₂_limit_mul τ (fun n => star (a n).val) (fun n => (a n).val)
    (star v.val) v.val 1 (fun n => (a n).adjoint.norm_le_one)
    (norm₂_limit_star τ _ _ hv) hv
  simpa only [(a _).initial,v.initial] using ht

theorem limit_le_of_le (a : ℕ → PartialIsometry M) (v w : PartialIsometry M)
    (hv : Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0))
    (hw : ∀ n, a n ≤ w) : v ≤ w := by
  have ht := norm₂_limit_mul τ (fun _ => w.val) (fun n => (a n).support.val)
    w.val v.support.val 1 (fun _ => w.norm_le_one)
    (by simp only [sub_self,TracialRepresentation.norm₂_zero]; exact tendsto_const_nhds)
    (support_limit τ a v hv)
  have he : (fun n => w.val*(a n).support.val)=(fun n => (a n).val) := funext hw
  simp only [show ∀ n, w.val*(a n).support.val=(a n).val from hw] at ht
  exact norm₂_limit_unique τ _ ht hv

end PartialIsometry

end

/-! Orthogonal patching with distinct source and target supports. -/

/-! A maximal actual partial isometry between subprojections of prescribed
projections. Chain upper bounds are constructed L2 limits, not assumed. -/
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
namespace PartialIsometry

theorem supports_of_L2_limit (a : ℕ → PartialIsometry M) (v : PartialIsometry M)
    (hv : Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0))
    (p q : AlgebraProjection M)
    (hp : ∀ n, (a n).support ≤ p) (hq : ∀ n, (a n).target ≤ q) :
    v.support ≤ p ∧ v.target ≤ q := by
  constructor
  · apply (v.support_le_iff_mul p).mpr
    have ht := norm₂_limit_mul τ (fun n => (a n).val) (fun _ => p.val)
      v.val p.val 1 (fun n => (a n).norm_le_one) hv
      (by simp only [sub_self,TracialRepresentation.norm₂_zero]; exact tendsto_const_nhds)
    have he : ∀ n, (a n).val*p.val=(a n).val := fun n =>
      ((a n).support_le_iff_mul p).mp (hp n)
    simp only [he] at ht
    exact norm₂_limit_unique τ _ ht hv
  · apply (v.target_le_iff_mul q).mpr
    have ht := norm₂_limit_mul τ (fun _ => q.val) (fun n => (a n).val)
      q.val v.val 1 (fun _ => q.property.norm_le)
      (by simp only [sub_self,TracialRepresentation.norm₂_zero]; exact tendsto_const_nhds) hv
    have he : ∀ n, q.val*(a n).val=(a n).val := fun n =>
      ((a n).target_le_iff_mul q).mp (hq n)
    simp only [he] at ht
    exact norm₂_limit_unique τ _ ht hv

end PartialIsometry

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Supports
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Kernel and range projections constructed in the actual von Neumann algebra.
Membership follows from commutant invariance, with no spectral theorem assumed. -/

/-! Spectral sign cuts from continuous positive parts and actual range projections.
These are constructed operators, not assumed Borel functional calculus data. -/
open scoped CStarAlgebra

/-! A polar operator is constructed by extending the isometry on a range.
No polar-decomposition or projection-comparison hypothesis is used. -/

/-! Polar decomposition inside the given concrete von Neumann algebra. -/
open scoped CStarAlgebra
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

attribute [local instance] OAI.Generator.Tracial.polarCStar
attribute [local instance] OAI.Generator.Tracial.polarOrder
attribute [local instance] OAI.Generator.Tracial.polarStarOrder
theorem exists_polar_decomposition (x : M.toStarSubalgebra) :
    ∃ v : M.toStarSubalgebra,
      v * CFC.sqrt (star x*x) = x ∧
      star v*v = (rangeProjection (CFC.sqrt (star x*x))).val ∧
      v*(rangeProjection (CFC.sqrt (star x*x))).val=v := by
  let a := CFC.sqrt (star x*x)
  have ha : IsSelfAdjoint a := (CFC.sqrt_nonneg _).isSelfAdjoint
  have haa : a*a=star x*x := CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg _)
  have hn (ξ : H) : ‖x.val ξ‖=‖a.val ξ‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have he := congrArg (fun t : M.toStarSubalgebra =>
      inner ℂ ξ ((t : H →L[ℂ] H) ξ)) haa
    have has : star a.val=a.val := congrArg Subtype.val ha.star_eq
    have hs (z : H →L[ℂ] H) : inner ℂ ξ ((star z*z) ξ) = (‖z ξ‖ : ℂ)^2 := by
      rw [mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_right,inner_self_eq_norm_sq_to_K]
      rfl
    have he' : (‖a.val ξ‖ : ℂ)^2 = (‖x.val ξ‖ : ℂ)^2 := by
      calc _ = inner ℂ ξ ((star a.val*a.val) ξ) := (hs _).symm
           _ = inner ℂ ξ ((star x.val*x.val) ξ) := by rw [has]; exact he
           _ = _ := hs _
    exact_mod_cast he'.symm
  obtain ⟨v,hva,hvi,hvs⟩ := exists_isometric_range_factor a.val x.val hn
  let s := rangeProjection a
  have hs : (s.val : H →L[ℂ] H)=a.val.range.topologicalClosure.starProjection :=
    rangeProjection_eq_closure_projection a
  rw [← hs] at hvi hvs
  have hmem : v ∈ M := by
    rw [← M.commutant_commutant]
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro y hy
    have hya := (VonNeumannAlgebra.mem_commutant_iff.mp hy) a.val a.property
    have hyx := (VonNeumannAlgebra.mem_commutant_iff.mp hy) x.val x.property
    have hys := (VonNeumannAlgebra.mem_commutant_iff.mp hy) s.val.val s.val.property
    have hz : (y*v-v*y)*a.val=0 := by
      rw [sub_mul,mul_assoc,hva,mul_assoc,← hya,← mul_assoc,hva,hyx,sub_self]
    have hd := mul_closure_range_projection_eq_zero a.val (y*v-v*y) hz
    rw [← hs,sub_mul,mul_assoc,hvs,mul_assoc,← hys,← mul_assoc,hvs] at hd
    exact sub_eq_zero.mp hd
  exact ⟨⟨v,hmem⟩,Subtype.ext hva,Subtype.ext hvi,Subtype.ext hvs⟩

end

/-! Exact initial and final support projections of the constructed polar part. -/
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

attribute [local instance] OAI.Generator.Tracial.polarSupportsCStar
attribute [local instance] OAI.Generator.Tracial.polarSupportsOrder
attribute [local instance] OAI.Generator.Tracial.polarSupportsStarOrder
theorem exists_polar_with_supports (x : M.toStarSubalgebra) :
    ∃ v : M.toStarSubalgebra,
      v*CFC.sqrt (star x*x)=x ∧
      star v*v=(rangeProjection (star x)).val ∧
      v*star v=(rangeProjection x).val := by
  obtain ⟨v,hvx,hvi,hvs⟩ := exists_polar_decomposition x
  let a := CFC.sqrt (star x*x)
  let s := rangeProjection a
  have ht : IsStarProjection (v*star v) := by
    constructor
    · change (v*star v)*(v*star v)=v*star v
      calc _ = (v*(star v*v))*star v := by simp only [mul_assoc]
           _ = v*star v := by rw [hvi,hvs]
    · exact IsSelfAdjoint.mul_star_self v
  let t : AlgebraProjection M := ⟨v*star v,ht⟩
  have hxt : rangeProjection x ≤ t := by
    apply (rangeProjection_le_iff x t).mpr
    change (v*star v)*x=x
    calc _ = (v*star v)*(v*a) := by rw [hvx]
         _ = (v*(star v*v))*a := by simp only [mul_assoc]
         _ = x := by rw [hvi,hvs,hvx]
  have htx : t ≤ rangeProjection x := by
    let r := rangeProjection x
    have hz : (r.val*v-v)*a=0 := by
      rw [sub_mul,mul_assoc,hvx,rangeProjection_mul,sub_self]
    have he := mul_closure_range_projection_eq_zero a.val
      ((r.val*v-v : M.toStarSubalgebra) : H →L[ℂ] H)
      (congrArg Subtype.val hz)
    rw [← rangeProjection_eq_closure_projection a] at he
    have he' : (r.val*v-v)*s.val=0 := Subtype.ext he
    rw [sub_mul,mul_assoc,hvs] at he'
    change r.val*(v*star v)=v*star v
    rw [← mul_assoc,sub_eq_zero.mp he']
  refine ⟨v,hvx,?_,?_⟩
  · simpa only [sqrt_rangeProjection] using hvi
  · exact congrArg (fun z : AlgebraProjection M => z.val) (le_antisymm htx hxt)

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_MatrixAlgebras
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Equal-trace finite partitions extend to actual matrix units in the same
factor. The theorem also retains a prescribed corner as the sum of diagonals. -/
open scoped BigOperators

/-! The matrix-unit image in the original represented algebra, with its
finite dimensionality and weak-operator closedness proved. -/
open scoped BigOperators

/-! The actual relative commutant in M is a diffuse scalar-center von
Neumann algebra, with the restricted faithful trace available from M. -/
namespace MatrixUnitSystem

section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (E : MatrixUnitSystem ι M.toStarSubalgebra)

def relativeEquiv : E.commutant ≃⋆ₐ[ℂ] E.relativeVonNeumann.toStarSubalgebra where
  toFun a := ⟨a.val.val,⟨a,rfl⟩⟩
  invFun a := ⟨⟨a.val,((E.relativeStar_mem a.val).mp a.property).1⟩,
    fun i j => Subtype.ext (((E.relativeStar_mem a.val).mp a.property).2 i j)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

theorem relative_scalar_center (o : ι)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (c : E.relativeVonNeumann.toStarSubalgebra)
    (hc : ∀ a : E.relativeVonNeumann.toStarSubalgebra,a*c=c*a) :
    ∃ z : ℂ,c=z • (1 : E.relativeVonNeumann.toStarSubalgebra) := by
  obtain ⟨z,hz⟩ := E.commutant_scalar_center o hfactor (E.relativeEquiv.symm c) (by
    intro a
    apply E.relativeEquiv.injective
    change E.relativeEquiv (a*E.relativeEquiv.symm c)=
      E.relativeEquiv (E.relativeEquiv.symm c*a)
    rw [map_mul,map_mul,E.relativeEquiv.apply_symm_apply]
    exact hc (E.relativeEquiv a))
  refine ⟨z,?_⟩
  have h := congrArg E.relativeEquiv hz
  simpa only [StarAlgEquiv.apply_symm_apply,map_smul,map_one] using h

theorem relative_diffuse (o : ι)
    (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (p : E.relativeVonNeumann.toStarSubalgebra) (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : E.relativeVonNeumann.toStarSubalgebra,
      IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q := by
  obtain ⟨q,hq,hq0,hqp,hpq,hqp'⟩ := E.commutant_diffuse o hdiff
    (E.relativeEquiv.symm p) (hp.map E.relativeEquiv.symm) (by
      intro h
      apply hp0
      simpa using congrArg E.relativeEquiv h)
  refine ⟨E.relativeEquiv q,?_,?_,?_,?_,?_⟩
  · exact hq.map E.relativeEquiv.toStarAlgHom
  · intro h
    apply hq0
    exact E.relativeEquiv.injective (h.trans (map_zero E.relativeEquiv).symm)
  · intro h
    apply hqp
    exact E.relativeEquiv.injective (h.trans (E.relativeEquiv.apply_symm_apply p).symm)
  · simpa only [map_mul,StarAlgEquiv.apply_symm_apply] using congrArg E.relativeEquiv hpq
  · simpa only [map_mul,StarAlgEquiv.apply_symm_apply] using congrArg E.relativeEquiv hqp'

end

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

theorem relative_irreducible (o : ι)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
        ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (c : (E.map (coordinateInclusion hNM)).relativeVonNeumann.toStarSubalgebra)
    (hc : ∀ a : E.relativeVonNeumann.toStarSubalgebra,
      coordinateInclusion (E.relative_inclusion hNM) a*c=
        c*coordinateInclusion (E.relative_inclusion hNM) a) :
    ∃ z : ℂ,c=z • (1 : (E.map (coordinateInclusion hNM)).relativeVonNeumann.toStarSubalgebra) := by
  let F := E.map (coordinateInclusion hNM)
  let cM := coordinateInclusion F.relativeVonNeumann_le c
  have hentries : ∀ i j,Commute (coordinateInclusion hNM (E.entry i j)) cM := by
    intro i j
    apply Subtype.ext
    exact ((F.relativeStar_mem c.val).mp c.property).2 i j
  have hamp (a : N.toStarSubalgebra) : Commute
      (coordinateInclusion hNM (E.amplify o a)) cM := by
    let b : E.relativeVonNeumann.toStarSubalgebra :=
      E.relativeEquiv ⟨E.amplify o a,E.amplify_mem o a⟩
    apply Subtype.ext
    exact congrArg (fun t : F.relativeVonNeumann.toStarSubalgebra => t.val) (hc b)
  obtain ⟨z,hz⟩ := hirr cM (fun x =>
    E.commute_mapped_of_amplify o (coordinateInclusion hNM) cM hentries hamp x)
  exact ⟨z,Subtype.ext (congrArg (fun t : M.toStarSubalgebra => t.val) hz)⟩

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
-- module Solutions.OAIQ075_KS.FactorGeneration_UniformPartitions
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Finite equal-trace partitions in an actual diffuse algebra, constructed
by repeated exact trace cuts. No matrix units or comparison theorem are
assumed. These partitions do not yet approximate an arbitrary given
spectral partition. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

/-! Complete finitely many orthogonal grid-trace projections to an actual
equal-trace unit partition, retaining explicit disjoint groups of pieces. -/

/-! Quantitative equal-trace approximation by rounding down spectral pieces.
All projections and partitions are constructed in the given diffuse algebra. -/

include hdiff in
theorem exists_uniform_trace_approximation
    (Q : CornerPartition (identityProjection M)) (n : ℕ) (hn : 0 < n) :
    ∃ R : CornerPartition (identityProjection M), R.size=n ∧
      (∀ j,τ.trace (R.piece j).val=(((n : ℝ)⁻¹ : ℝ) : ℂ)) ∧
      ∃ J : Fin Q.size → Finset (Fin R.size),
        (∀ i j,i ≠ j → Disjoint (J i) (J j)) ∧
        (∀ i,(Q.piece i).val*(∑ j ∈ J i,(R.piece j).val)=
          ∑ j ∈ J i,(R.piece j).val) ∧
        ∀ i,τ.norm₂ ((Q.piece i).val-∑ j ∈ J i,(R.piece j).val)^2 < (n : ℝ)⁻¹ := by
  classical
  choose m q hle ht herr using fun i => exists_rounded_trace_subprojection τ hdiff (Q.piece i) n hn
  have horth (i j : Fin Q.size) (hij : i ≠ j) : (q i).val*(q j).val=0 :=
    orthogonal_subprojections (Q.orthogonal i j hij) (hle i) (hle j)
  have htracele (i : Fin Q.size) : (m i : ℝ)*(n : ℝ)⁻¹ ≤ (τ.trace (Q.piece i).val).re := by
    have hpos : 0 ≤ (τ.trace ((Q.piece i).val-(q i).val)).re := by
      rw [projection_trace_sq τ _ ((q i).property.sub_of_mul_eq_right (Q.piece i).property (hle i))]
      positivity
    rw [trace_sub,ht,Complex.sub_re,Complex.ofReal_re] at hpos
    linarith
  have hsum : (∑ i,m i : ℕ) ≤ n := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => htracele i)
    rw [Q.trace_total τ] at h
    have hreal : ((∑ i,m i : ℕ) : ℝ)*(n : ℝ)⁻¹ ≤ 1 := by
      simpa only [Nat.cast_sum,Finset.sum_mul,identityProjection,τ.trace_one,Complex.one_re] using h
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hmul := mul_inv_cancel₀ (ne_of_gt hnR)
    have hbound : ((∑ i,m i : ℕ) : ℝ) ≤ (n : ℝ) :=
      (mul_le_mul_iff_left₀ (inv_pos.mpr hnR)).mp (hreal.trans_eq hmul.symm)
    exact_mod_cast hbound
  obtain ⟨R,hsize,hRt,J,hJdis,hJsum⟩ := exists_uniform_trace_extension τ hdiff q horth n hn m hsum ht
  refine ⟨R,hsize,hRt,J,hJdis,?_,?_⟩
  · intro i
    rw [hJsum]
    exact hle i
  · intro i
    rw [hJsum]
    exact herr i

include hdiff in
theorem exists_dyadic_trace_approximation
    (Q : CornerPartition (identityProjection M)) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, ∃ R : CornerPartition (identityProjection M), R.size=2^k ∧
      (∀ j,τ.trace (R.piece j).val=((((2^k : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) ∧
      ∃ J : Fin Q.size → Finset (Fin R.size),
        (∀ i j,i ≠ j → Disjoint (J i) (J j)) ∧
        (∀ i,(Q.piece i).val*(∑ j ∈ J i,(R.piece j).val)=
          ∑ j ∈ J i,(R.piece j).val) ∧
        ∀ i,τ.norm₂ ((Q.piece i).val-∑ j ∈ J i,(R.piece j).val)^2 < ε := by
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hk' : (((2^k : ℕ) : ℝ)⁻¹ : ℝ) < ε := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat,inv_pow] using hk
  obtain ⟨R,hsize,ht,J,hd,hle,herr⟩ := exists_uniform_trace_approximation τ hdiff Q (2^k) (by positivity)
  exact ⟨k,R,hsize,ht,J,hd,hle,fun i => (herr i).trans hk'⟩

end

/-! A finite commuting self-adjoint family admits simultaneous L2 spectral
approximation on one constructed dyadic equal-trace partition. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

variable (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

include hdiff in
theorem exists_dyadic_spectral_sum_approximation {ι : Type*} [Fintype ι]
    (Q : CornerPartition (identityProjection M)) (c : ι → Fin Q.size → ℂ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, ∃ R : CornerPartition (identityProjection M), R.size=2^k ∧
      (∀ j,τ.trace (R.piece j).val=((((2^k : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) ∧
      ∃ d : ι → Fin R.size → ℂ, ∀ i,
        τ.norm₂ ((∑ l,c i l • (Q.piece l).val)-∑ j,d i j • (R.piece j).val) < ε := by
  classical
  let A : ℝ := ∑ i,∑ l,‖c i l‖
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let δ := ε/(A+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hsmall : A*δ < ε := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < A+1)).mpr
    nlinarith
  obtain ⟨k,R,hsize,ht,J,_,_,herr⟩ := exists_dyadic_trace_approximation τ hdiff Q (δ^2) (sq_pos_of_pos hδ)
  let d : ι → Fin R.size → ℂ := fun i j => ∑ l,if j ∈ J l then c i l else 0
  have hd (i : ι) : (∑ j,d i j • (R.piece j).val)=
      ∑ l,c i l • (∑ j ∈ J l,(R.piece j).val) := by
    simp only [d,Finset.sum_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.smul_sum]
    simp only [ite_smul,zero_smul]
    simp
  have herr' (l : Fin Q.size) :
      τ.norm₂ ((Q.piece l).val-∑ j ∈ J l,(R.piece j).val) ≤ δ := by
    have h := herr l
    have hnonneg : 0 ≤ τ.norm₂ ((Q.piece l).val-∑ j ∈ J l,(R.piece j).val) := norm_nonneg _
    nlinarith
  refine ⟨k,R,hsize,ht,d,?_⟩
  intro i
  rw [hd,← Finset.sum_sub_distrib]
  simp only [← smul_sub]
  calc
    τ.norm₂ (∑ l,c i l • ((Q.piece l).val-∑ j ∈ J l,(R.piece j).val)) ≤
        ∑ l,τ.norm₂ (c i l • ((Q.piece l).val-∑ j ∈ J l,(R.piece j).val)) :=
      norm₂_finset_sum_le τ Finset.univ _
    _ ≤ ∑ l,‖c i l‖*δ := by
      apply Finset.sum_le_sum
      intro l _
      rw [τ.norm₂_smul]
      exact mul_le_mul_of_nonneg_left (herr' l) (norm_nonneg _)
    _ = (∑ l,‖c i l‖)*δ := (Finset.sum_mul _ _ _).symm
    _ ≤ A*δ := by
      apply mul_le_mul_of_nonneg_right _ hδ.le
      exact Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun l _ => norm_nonneg _)) (Finset.mem_univ i)
    _ < ε := hsmall

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_MatrixRefinement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! A normal element of a diffuse finite factor has L2 approximations in
constructed full dyadic matrix algebras. No prescribed MASA is needed. -/

/-! Concrete commutants reverse matrix-algebra inclusion. Expectations are
compatible with restriction to an intermediate represented subalgebra. -/
section
namespace MatrixUnitSystem
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The product commutant is exactly the commutant of the new system inside
of the old commutant, with both algebras represented on the same H. -/
theorem relative_product_inside (E : MatrixUnitSystem ι M.toStarSubalgebra)
    (F : MatrixUnitSystem κ E.relativeVonNeumann.toStarSubalgebra)
    (hc : ∀ i j k l,Commute (E.entry i j)
      ((F.map (coordinateInclusion E.relativeVonNeumann_le)).entry k l)) :
    (E.product (F.map (coordinateInclusion E.relativeVonNeumann_le)) hc).relativeVonNeumann =
      F.relativeVonNeumann := by
  let G := F.map (coordinateInclusion E.relativeVonNeumann_le)
  apply le_antisymm
  · intro x hx
    have hE := E.relative_antitone (E.product G hc) (E.algebra_le_product_left G hc) hx
    have hG := G.relative_antitone (E.product G hc) (E.algebra_le_product_right G hc) hx
    exact (F.relativeStar_mem x).mpr ⟨hE,((G.relativeStar_mem x).mp hG).2⟩
  · intro x hx
    have hF := (F.relativeStar_mem x).mp hx
    have hE := (E.relativeStar_mem x).mp hF.1
    apply ((E.product G hc).relativeStar_mem x).mpr
    refine ⟨hE.1,?_⟩
    intro a b
    change ((E.entry a.1 b.1).val*(F.entry a.2 b.2).val)*x=
      x*((E.entry a.1 b.1).val*(F.entry a.2 b.2).val)
    rw [mul_assoc,hF.2,← mul_assoc,hE.2,mul_assoc]

end MatrixUnitSystem

end

/-! Quantitative energy descent retaining a prescribed finite matrix algebra
in an irreducible inclusion. All expectations and refinements are constructed. -/

/-! Reindex full matrix units without changing their actual algebra or
relative commutant. This keeps iterated constructions indexed by Fin n. -/

/-! An actual full matrix algebra of any positive finite size can be
constructed in the relative commutant. No commuting matrix units are assumed. -/

end Generator

end

end OAI
end


