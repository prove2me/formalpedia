-- Prove2me | Definitions.Def_OAIQ11Fg023
-- name    : OAIQ11Fg023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T10:31:29.052425+00:00
-- url     : https://prove2.me/theorems/ec496e3d-ab6e-40e0-8001-d06365f59af5
-- title:
--   Definitions bundle OAIQ11Fg023 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 26 declarations of OpenAI's Lean: 4 definitions and 22 theorems. The definitions and types are `OAI.Generator.Tracial.quotientResidualTrace`, `OAI.Generator.Tracial.traceClosedSpan`, `OAI.Generator.Tracial.traceVectorCLM`, `OAI.Generator.Tracial.unitaryWord`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_Dimension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/Dimension.lean), [`FactorGeneration_FreeGroupMoments`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/FreeGroupMoments.lean), [`FactorGeneration_LaurentMoments`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/LaurentMoments.lean), [`FactorGeneration_LocalizedStates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/LocalizedStates.lean), [`FactorGeneration_NormalDimension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/NormalDimension.lean), [`FactorGeneration_NormalTrace`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/NormalTrace.lean), [`FactorGeneration_PerturbationBounds`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/PerturbationBounds.lean), [`FactorGeneration_ResidualCompletion`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/ResidualCompletion.lean), [`FactorGeneration_SpectralDimension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/SpectralDimension.lean), [`FactorGeneration_SpectralStates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/SpectralStates.lean).
--
--   **Imports.** It imports the bundle `OAIQ11Fg016` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ11Fg017` and `OAIQ11Fg026`; the statement `OAI.Generator.Tracial.reduced_integer_moment_closedSpan`; the proofs of `OAI.Generator.Tracial.conjugate_freeGroup_trace`, `OAI.Generator.Tracial.exists_coordinate_ordered_unitary`, `OAI.Generator.Tracial.nonempty_coordinateHaarData`, `OAI.Generator.Tracial.reduced_integer_moment_closedSpan` and `OAI.Generator.Tracial.successive_freeGroup_trace`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ11Fg016

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

theorem traceFreeDyadicSup_self (p : AlgebraProjection M) :
    traceFreeDyadicSup hfactor hdiff p p=1 := by
  apply le_antisymm (traceFreeDyadicSup_le_one hfactor hdiff p p)
  rw [← dyadicWeight_univ 0]
  apply traceFreeDyadicSup_lower_bound hfactor hdiff p p 0 Finset.univ
  rw [EquivalentPartition.subset_univ]
  exact AlgebraProjection.subequivalent_refl p

theorem traceFreeDyadicSup_eq_zero_iff
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p q : AlgebraProjection M) (hp : p.val≠0) :
    traceFreeDyadicSup hfactor hdiff p q=0 ↔ q.val=0 := by
  constructor
  · intro h
    by_contra hq
    have hh := traceFreeDyadicSup_pos hfactor hdiff hfinite p q hq
    rw [h] at hh
    exact lt_irrefl _ hh
  · exact traceFreeDyadicSup_zero hfactor hdiff p q hp

end

/-! Common refinements compare arbitrary dyadic levels. The supremum takes
the exact dyadic value on every reference subset projection, and finite
rounding bounds every projection with an explicit error at each level. -/

/-! Orthogonal lower approximants fit disjoint collections of the reference
pieces. Equivalent complements and finite cancellation enforce the capacity. -/

/-! Orthogonal additivity of the constructed dyadic dimension. Numerical
rounding errors tend to zero; every lower and upper bound uses actual
partial-isometry witnesses in the original finite diffuse factor. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
/-- Faithfulness and additivity give strict increase along proper inclusion. -/
theorem traceFreeDyadicSup_strictMono
    (p q r : AlgebraProjection M) (hp : p.val≠0) (hrp : r ≤ p) (hqr : q < r) :
    traceFreeDyadicSup hfactor hdiff p q < traceFreeDyadicSup hfactor hdiff p r := by
  have hle : q ≤ r := le_of_lt hqr
  let s := AlgebraProjection.remainder q r hle
  have hs : s.val≠0 := by
    change r.val-q.val≠0
    intro h
    exact (ne_of_lt hqr) (Subtype.ext (sub_eq_zero.mp h).symm)
  have hpos := traceFreeDyadicSup_pos hfactor hdiff hfinite p s hs
  have he := traceFreeDyadicSup_orthogonal_add hfactor hdiff hfinite p q s hp
    (hle.trans hrp) ((AlgebraProjection.remainder_le q r hle).trans hrp)
    (AlgebraProjection.remainder_orthogonal q r hle)
  rw [AlgebraProjection.orthogonalSum_remainder] at he
  linarith

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

include hfinite in
theorem traceFree_target_eq_of_dimension_le
    (p q : AlgebraProjection M) (hp : p.val≠0) (hqp : q ≤ p)
    (v : PartialIsometry M) (ht : v.target ≤ q)
    (hd : traceFreeDyadicSup hfactor hdiff p q ≤ traceFreeDyadicSup hfactor hdiff p v.support) :
    v.target=q := by
  by_contra he
  have hlt := traceFreeDyadicSup_strictMono hfactor hdiff hfinite p v.target q hp hqp
    (lt_of_le_of_ne ht he)
  have heq := traceFreeDyadicSup_equivalent hfactor hdiff p
    (show v.support.Equivalent v.target from ⟨v,rfl,rfl⟩)
  linarith

include hfinite in
/-- Real-valued comparison is exactly witnessed projection subequivalence. -/
theorem traceFreeDyadicSup_le_iff_subequivalent
    (p q r : AlgebraProjection M) (hp : p.val≠0) (hqp : q ≤ p) :
    traceFreeDyadicSup hfactor hdiff p q ≤ traceFreeDyadicSup hfactor hdiff p r ↔
      q.Subequivalent r := by
  refine ⟨fun hd => ?_,traceFreeDyadicSup_mono hfactor hdiff p⟩
  rcases AlgebraProjection.subequivalent_total hfactor q r with h | h
  · exact h
  · obtain ⟨v,hv,ht⟩ := h
    have he : v.target=q := traceFree_target_eq_of_dimension_le hfactor hdiff hfinite
      p q hp hqp v ht (by rw [hv]; exact hd)
    exact ⟨v.adjoint,he,le_of_eq (v.adjoint_target.trans hv)⟩

include hfinite in
theorem traceFreeDyadicSup_eq_iff_equivalent
    (p q r : AlgebraProjection M) (hp : p.val≠0) (hqp : q ≤ p) (hrp : r ≤ p) :
    traceFreeDyadicSup hfactor hdiff p q=traceFreeDyadicSup hfactor hdiff p r ↔
      q.Equivalent r := by
  constructor
  · intro h
    exact AlgebraProjection.equivalent_of_mutual_subequivalent hfinite
      ((traceFreeDyadicSup_le_iff_subequivalent hfactor hdiff hfinite p q r hp hqp).mp (le_of_eq h))
      ((traceFreeDyadicSup_le_iff_subequivalent hfactor hdiff hfinite p r q hp hrp).mp (le_of_eq h.symm))
  · exact traceFreeDyadicSup_equivalent hfactor hdiff p

end Tracial

end

/-! Bounds and concrete dyadic upper approximants for the constructed
projection dimension. These finite estimates do not assume continuity. -/
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
theorem traceFreeDimension_le_iff_subequivalent
    (hunit : (1 : M.toStarSubalgebra) ≠ 0) (q r : AlgebraProjection M) :
    traceFreeDimension hfactor hdiff q ≤ traceFreeDimension hfactor hdiff r ↔
      q.Subequivalent r :=
  traceFreeDyadicSup_le_iff_subequivalent hfactor hdiff hfinite _ q r hunit (one_mul _)

include hfinite in
theorem traceFreeDimension_strictMono (hunit : (1 : M.toStarSubalgebra) ≠ 0) :
    StrictMono (traceFreeDimension hfactor hdiff) :=
  fun _ _ h => traceFreeDyadicSup_strictMono hfactor hdiff hfinite _ _ _ hunit (one_mul _) h

include hfinite in
/-- Actual projection upper approximants for every real c in [0,1]. -/
theorem traceFreeDimension_exists_upper
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (n : ℕ) :
    ∃ r : AlgebraProjection M, c ≤ traceFreeDimension hfactor hdiff r ∧
      traceFreeDimension hfactor hdiff r ≤ c+1/2^n := by
  obtain ⟨s,hs,ht⟩ := exists_dyadicWeight_upper c hc hc1 n
  refine ⟨(traceFreeDyadicPartition hfactor hdiff ⟨1,IsStarProjection.one _⟩ n).subset s,?_,?_⟩
  · simpa only [traceFreeDimension,traceFreeDyadicSup_subset hfactor hdiff hfinite
      ⟨1,IsStarProjection.one _⟩ hunit] using hs
  · simpa only [traceFreeDimension,traceFreeDyadicSup_subset hfactor hdiff hfinite
      ⟨1,IsStarProjection.one _⟩ hunit] using ht

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_ResidualCompletion
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual residual projections, null-set masking, and coordinatewise
orthogonal partial-unitary patching. -/

/-! An actual positive residual support increment with exact ordered moments
for arbitrary countably many centered compressed quotient coefficients. -/
open Filter

/-! Faithful-trace completion criterion and the exact quarter-increment
residual estimate for actual orthogonal coordinate patches. -/

/-! Actual moment-preserving residual extensions, retaining coordinate partial
unitaries in N and the quantitative decrease of residual support. -/

/-! Iteration of actual moment-preserving partial-unitary extensions. Every
stage retains its coordinate representatives and a geometric residual bound. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def quotientResidualTrace (ω : Ultrafilter ℕ) (v : ℕ → PartialUnitary M) : ℝ :=
  (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))).re

end

/-! Coordinatewise monotone upper bounds and quantitative convergence in the
actual quotient two-norm. No completeness of the quotient is assumed. -/
open UltrapowerBridge Filter
open scoped Topology

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_LaurentMoments
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Extend exact moments by separate trace continuity in the two-norm. No
joint continuity of quotient multiplication, or operator-norm structure on Q,
is assumed. -/
section
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def traceClosedSpan (S : Set (Q τ ω)) : Submodule ℂ (Q τ ω) :=
  (Submodule.span ℂ S).topologicalClosure

/-! Extend exact moments by separate trace continuity in the two-norm. No
joint continuity of quotient multiplication, or operator-norm structure on Q,
is assumed. -/

end

/-! Construct an included Haar unitary and the full nonzero-integer endpoint
formula over any two-norm-separable unital subalgebra of the actual quotient. -/

/-! Extend a trace identity in each factor to the closed linear span of its
allowed values. This uses separate continuity only. -/

/-! Construct an included Haar unitary and the full nonzero-integer endpoint
formula over any two-norm-separable unital subalgebra of the actual quotient. -/

/-! From the endpoint formula to every alternating word shape. -/
open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_FreeGroupMoments
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Every nonempty reduced word in successive Haar variables has zero trace.
The induction eliminates the largest label, retaining centered lower-label gaps. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def unitaryWord {A : Type*} (v : A → unitary (Q τ ω)) (w : List (A × Bool)) : Q τ ω :=
  (w.map (fun x => algebraSignedLetter (v x.1 : Q τ ω) (!x.2))).prod

end

/-! The actual free-group representation furnished by successive Haar variables. -/

/-! Reduced-word moments for p*y*(star p). Distinct labels have centered ratios;
reducedness requires distinct labels precisely at opposite-sign gaps. -/

/-! Positive and negative conjugate terms in first-order correlation. Same-sign gaps require no centering hypothesis. -/
open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_NormalDimension
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Increasing projection suprema and compatible sequential comparison.
The witnesses live in the original algebra; no trace or dimension is used. -/

/-! Original-factor wrapper for normalized faithful order-continuous projection
dimension. This does not assert the existence of a linear trace functional. -/

/-! Exact prescribed dimensions are attained by actual subprojections.
Chain bounds use the proved arbitrary-net continuity of dimension. -/
namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
theorem traceFreeDimension_exists_small_subprojection
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (p : AlgebraProjection M) (hp : p.val≠0) (ε : ℝ) (hε : 0<ε) :
    ∃ q : AlgebraProjection M, q ≤ p ∧ 0 < traceFreeDimension hfactor hdiff q ∧
      traceFreeDimension hfactor hdiff q < ε := by
  classical
  have hpD : 0 < traceFreeDimension hfactor hdiff p :=
    traceFreeDyadicSup_pos hfactor hdiff hfinite _ p hp
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one (lt_min hε hpD) (by norm_num : (1/2 : ℝ)<1)
  rw [one_div_pow] at hn
  have hn0 : (0 : ℝ)<1/2^n := by positivity
  have hi : Nonempty (DyadicIndex n) := Fintype.card_pos_iff.mp (by
    rw [card_dyadicIndex]; positivity)
  let i : DyadicIndex n := Classical.choice hi
  let e := (traceFreeDyadicPartition hfactor hdiff ⟨1,IsStarProjection.one _⟩ n).subset {i}
  have heD : traceFreeDimension hfactor hdiff e=1/2^n := by
    change traceFreeDyadicSup hfactor hdiff ⟨1,IsStarProjection.one _⟩
      ((traceFreeDyadicPartition hfactor hdiff ⟨1,IsStarProjection.one _⟩ n).subset {i})=1/2^n
    rw [traceFreeDyadicSup_subset hfactor hdiff hfinite ⟨1,IsStarProjection.one _⟩ hunit]
    simp only [dyadicWeight,Finset.card_singleton,Nat.cast_one]
  obtain ⟨v,hv,ht⟩ := (traceFreeDimension_le_iff_subequivalent hfactor hdiff hfinite hunit e p).mp
    (by rw [heD]; exact (lt_min_iff.mp hn).2.le)
  have he : traceFreeDimension hfactor hdiff v.target=1/2^n := by
    have h := traceFreeDyadicSup_equivalent hfactor hdiff ⟨1,IsStarProjection.one _⟩
      (show e.Equivalent v.target from ⟨v,hv,rfl⟩)
    exact h.symm.trans heD
  exact ⟨v.target,ht,by rw [he]; exact hn0,by rw [he]; exact (lt_min_iff.mp hn).1⟩

end

/-! Finite partitions with prescribed dimensions, and actual equivalent
partitions of arbitrary positive finite size in every corner. -/
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
theorem traceFreeDimension_remainder
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (q p : AlgebraProjection M) (hq : q ≤ p) :
    traceFreeDimension hfactor hdiff (AlgebraProjection.remainder q p hq)=
      traceFreeDimension hfactor hdiff p-traceFreeDimension hfactor hdiff q := by
  have h := traceFreeDyadicSup_orthogonal_add hfactor hdiff hfinite
    ⟨1,IsStarProjection.one _⟩ q (AlgebraProjection.remainder q p hq)
    hunit (one_mul _) (one_mul _) (AlgebraProjection.remainder_orthogonal q p hq)
  rw [AlgebraProjection.orthogonalSum_remainder] at h
  change traceFreeDimension hfactor hdiff p=
    traceFreeDimension hfactor hdiff q+
      traceFreeDimension hfactor hdiff (AlgebraProjection.remainder q p hq) at h
  linarith

end Tracial

/-! Actual vector functionals and their continuity on directed projection
suprema. No factor, trace, separability, or dimension hypothesis is used. -/
open Filter
open scoped Topology BigOperators

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_SpectralDimension
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Finite spectral weights of the constructed projection dimension obey an
operator-norm bound. No linear trace on noncommuting elements is assumed. -/

/-! Construct the unique real spectral dimension value of each self-adjoint
operator by norm approximation. Global noncommuting additivity is not asserted. -/

/-! The constructed spectral value is bounded and extends the actual
projection dimension. These laws do not assert noncommuting additivity. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem dimensionSpectralValue_norm_le (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    ‖dimensionSpectralValue hfactor hdiff hfinite hunit x hx‖ ≤ ‖x‖ :=
  (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx).2.norm_le hfactor hdiff

end

/-! Finite-family tests and real homogeneity for the constructed spectral value.
These statements do not assert additivity for noncommuting operators. -/
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem dimensionSpectralValue_zero (hunit : (1 : M.toStarSubalgebra) ≠ 0) :
    dimensionSpectralValue hfactor hdiff hfinite hunit 0 (IsSelfAdjoint.zero _)=0 := by
  have h := dimensionSpectralValue_norm_le hfactor hdiff hfinite hunit 0 (IsSelfAdjoint.zero _)
  rw [norm_zero] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_SpectralStates
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.predualFunctionals_normed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Additivity on commuting self-adjoint operators, proved using actual common
spectral refinements. The commutation hypothesis is essential to this proof. -/
open scoped BigOperators

/-! Positive spectral approximants, positivity of the constructed scalar, and
order preservation on commuting self-adjoint operators. -/
open scoped BigOperators CStarAlgebra

/-! A nonzero positive operator dominates a positive multiple of an actual
nonzero spectral projection. This proves faithfulness without linearity. -/
open scoped CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.spectralFaithfulCStar
attribute [local instance] OAI.Generator.Tracial.spectralFaithfulOrder
attribute [local instance] OAI.Generator.Tracial.spectralFaithfulPreorder
attribute [local instance] OAI.Generator.Tracial.spectralFaithfulLE
attribute [local instance] OAI.Generator.Tracial.spectralFaithfulStarOrder
theorem dimensionSpectralValue_pos
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x : M.toStarSubalgebra) (hx : 0 ≤ x) (hx0 : x≠0) :
    0 < (dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint).re := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let q := cornerSpectralCut (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M) x (‖x‖/2)
  have hq : q.val≠0 := positive_spectral_cut_ne_zero x hx (‖x‖/2) (by positivity) (by linarith)
  have hd : 0 < traceFreeDimension hfactor hdiff q := traceFreeDyadicSup_pos
    hfactor hdiff hfinite ⟨1,IsStarProjection.one _⟩ q hq
  exact (mul_pos (half_pos hn) hd).trans_le
    (dimensionSpectralValue_spectral_cut_lower hfactor hdiff hfinite hunit x hx (‖x‖/2))

theorem dimensionSpectralValue_eq_zero_iff_of_nonneg
    (hunit : (1 : M.toStarSubalgebra) ≠ 0) (x : M.toStarSubalgebra) (hx : 0 ≤ x) :
    dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint=0 ↔ x=0 := by
  constructor
  · intro h
    by_contra hx0
    have hp := dimensionSpectralValue_pos hfactor hdiff hfinite hunit x hx hx0
    rw [h,Complex.zero_re] at hp
    exact (lt_irrefl 0) hp
  · intro h
    subst x
    exact dimensionSpectralValue_zero hfactor hdiff hfinite hunit

end

/-! Unitary conjugacy preserves projection dimension and its constructed
spectral extension. No trace identity is assumed. -/
open scoped BigOperators
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem traceFreeDimension_unitaryConjugate (p : AlgebraProjection M)
    (u : unitary M.toStarSubalgebra) :
    traceFreeDimension hfactor hdiff (p.unitaryConjugate u)=traceFreeDimension hfactor hdiff p :=
  (traceFreeDyadicSup_equivalent hfactor hdiff ⟨1,IsStarProjection.one _⟩
    (p.equivalent_unitaryConjugate u)).symm

theorem dimensionSpectralValue_unitary_conjugate
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (u : unitary M.toStarSubalgebra) (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    dimensionSpectralValue hfactor hdiff hfinite hunit
      (Unitary.conjStarAlgAut ℂ M.toStarSubalgebra u x)
      (hx.map (Unitary.conjStarAlgAut ℂ M.toStarSubalgebra u))=
      dimensionSpectralValue hfactor hdiff hfinite hunit x hx := by
  classical
  let φ := Unitary.conjStarAlgAut ℂ M.toStarSubalgebra u
  have hnorm (a : M.toStarSubalgebra) : ‖φ a‖=‖a‖ := by
    change ‖((u : M.toStarSubalgebra)*a)*(star u : unitary M.toStarSubalgebra)‖=‖a‖
    rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul]
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨Q,c,_,hQ,herr⟩ := exists_finite_spectral_approximation_preserving_commutant
    ⟨1,IsStarProjection.one _⟩ x hx (ε/2) (half_pos hε)
  simp only [one_mul,mul_one] at herr
  have hc := hQ x (Commute.refl x) (Commute.one_left x)
  let q (i : Fin Q.size) := (Q.piece i).unitaryConjugate u
  have ho (i j : Fin Q.size) (hij : i≠j) : (q i).val*(q j).val=0 := by
    change φ (Q.piece i).val*φ (Q.piece j).val=0
    exact (map_mul φ (Q.piece i).val (Q.piece j).val).symm.trans
      ((congrArg φ (Q.orthogonal i j hij)).trans (map_zero φ))
  have hs : (∑ i, (q i).val)=(1 : M.toStarSubalgebra) := by
    change (∑ i, φ (Q.piece i).val)=1
    exact (map_sum φ (fun i => (Q.piece i).val) Finset.univ).symm.trans
      ((congrArg φ Q.total).trans (map_one φ))
  have hcomm (i : Fin Q.size) : Commute (q i).val (φ x) :=
    (hc i).map φ
  have hmap : (∑ i, (c i : ℂ) • (q i).val)=φ (∑ i, (c i : ℂ) • (Q.piece i).val) := by
    change (∑ i, (c i : ℂ) • φ (Q.piece i).val)=_
    simp only [map_sum,map_smul]
  have hval := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit (φ x) (hx.map φ)).2.family_bound
    hfactor hdiff q ho hs (fun i => (c i : ℂ)) hcomm
  have hweight : (∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (q i) : ℂ))=
      ∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ) := by
    simp only [q,traceFreeDimension_unitaryConjugate hfactor hdiff]
  have hval' :
      ‖dimensionSpectralValue hfactor hdiff hfinite hunit (φ x) (hx.map φ) -
        ∑ i, (c i : ℂ) * (traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)‖ ≤
      ‖x - ∑ i, (c i : ℂ) • (Q.piece i).val‖ := by
    calc
      _ = ‖dimensionSpectralValue hfactor hdiff hfinite hunit (φ x) (hx.map φ) -
          ∑ i, (c i : ℂ) * (traceFreeDimension hfactor hdiff (q i) : ℂ)‖ :=
        congrArg (fun z : ℂ => ‖dimensionSpectralValue hfactor hdiff hfinite hunit
          (φ x) (hx.map φ) - z‖) hweight.symm
      _ ≤ ‖φ x - ∑ i, (c i : ℂ) • (q i).val‖ := hval
      _ = ‖φ (x - ∑ i, (c i : ℂ) • (Q.piece i).val)‖ :=
        congrArg (fun z : M.toStarSubalgebra => ‖z‖)
          ((congrArg (fun z => φ x - z) hmap).trans (map_sub φ x _).symm)
      _ = _ := hnorm _
  have hxval := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx).2
    Q (fun i => (c i : ℂ)) hc
  have htri := dist_triangle
    (dimensionSpectralValue hfactor hdiff hfinite hunit (φ x) (hx.map φ))
    (∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ))
    (dimensionSpectralValue hfactor hdiff hfinite hunit x hx)
  simp only [dist_eq_norm] at htri
  rw [norm_sub_rev (∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ))
    (dimensionSpectralValue hfactor hdiff hfinite hunit x hx)] at htri
  change ‖dimensionSpectralValue hfactor hdiff hfinite hunit (φ x) (hx.map φ)-
    dimensionSpectralValue hfactor hdiff hfinite hunit x hx‖ ≤ 0+ε
  linarith only [htri,hval',hxval,herr]

end

/-! The constructed scalar agrees on x*x and xx*, by an actual unitary polar
decomposition. This is a quadratic identity, not unrestricted additivity. -/
open scoped CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.spectralSquareCStar
attribute [local instance] OAI.Generator.Tracial.spectralSquareOrder
attribute [local instance] OAI.Generator.Tracial.spectralSquareStarOrder
theorem dimensionSpectralValue_star_mul_self
    (hunit : (1 : M.toStarSubalgebra) ≠ 0) (x : M.toStarSubalgebra) :
    dimensionSpectralValue hfactor hdiff hfinite hunit (star x*x) (IsSelfAdjoint.star_mul_self x)=
      dimensionSpectralValue hfactor hdiff hfinite hunit (x*star x) (IsSelfAdjoint.mul_star_self x) := by
  obtain ⟨u,hu⟩ := exists_unitary_polar_decomposition hfactor hfinite x
  let a := CFC.sqrt (star x*x)
  have ha : star a=a := (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
  have haa : a*a=star x*x := CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg _)
  have he : Unitary.conjStarAlgAut ℂ M.toStarSubalgebra u (star x*x)=x*star x := by
    change (u : M.toStarSubalgebra)*(star x*x)*star (u : M.toStarSubalgebra)=x*star x
    calc _ = ((u : M.toStarSubalgebra)*a)*star ((u : M.toStarSubalgebra)*a) := by
           rw [star_mul,ha,← haa]
           simp only [mul_assoc]
      _ = x*star x := by rw [hu]
  have h := dimensionSpectralValue_unitary_conjugate hfactor hdiff hfinite hunit
    u (star x*x) (IsSelfAdjoint.star_mul_self x)
  simpa only [he] using h.symm

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_LocalizedStates
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Localization of actual signed vector/dimension values. Fixed strict
sublevel sets, rather than a limiting strict inequality, supply Zorn bounds. -/
open Filter
open scoped Topology

/-! Tight multiplicative localization of an actual Hilbert vector functional
against the constructed projection dimension. The corner is constructed. -/

/-! Positive spectral approximants inside an actual projection corner, and
extension of localized projection inequalities to positive operators. -/
open scoped BigOperators CStarAlgebra

/-! Projection localization yields actual positive-operator inequalities for
bounded linear functionals, and a nearly cyclic functional on the corner. -/
open scoped BigOperators CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.localizedCStar
attribute [local instance] OAI.Generator.Tracial.localizedOrder
local instance localizedPreorder_rc417ad_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.localizedLE
attribute [local instance] OAI.Generator.Tracial.localizedStarOrder
theorem positive_functional_bounds_of_projection_bounds
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (φ : M.toStarSubalgebra →L[ℂ] ℂ) (E : AlgebraProjection M)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hproj : ∀ p : AlgebraProjection M, p ≤ E →
      a*traceFreeDimension hfactor hdiff p ≤ (φ p.val).re ∧
      (φ p.val).re ≤ b*traceFreeDimension hfactor hdiff p)
    (x : M.toStarSubalgebra) (hx : 0 ≤ x) (hEx : E.val*x=x) :
    a*(dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint).re ≤ (φ x).re ∧
      (φ x).re ≤ b*(dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint).re := by
  let t := dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint
  have hxE : x*E.val=x := by
    simpa only [star_mul,E.property.isSelfAdjoint.star_eq,hx.isSelfAdjoint.star_eq]
      using congrArg star hEx
  have happrox (ε : ℝ) (hε : 0<ε) :
      a*t.re ≤ (φ x).re+ε ∧ (φ x).re ≤ b*t.re+ε := by
    let C := a+b+‖φ‖+1
    have hC : 0<C := by dsimp [C]; positivity
    let δ := ε/C
    have hδ : 0<δ := div_pos hε hC
    have hCδ : C*δ=ε := mul_div_cancel₀ _ hC.ne'
    obtain ⟨Q,c,hc,hQ,herr⟩ := exists_positive_corner_spectral_approximation E x hx hEx δ hδ
    let y : M.toStarSubalgebra := ∑ i, (c i : ℂ) • (Q.piece i).val
    let w : ℝ := ∑ i, c i*traceFreeDimension hfactor hdiff (Q.piece i)
    let v : ℝ := (φ y).re
    have hw : (w : ℂ)=∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ) := by
      simp only [w,Complex.ofReal_sum,Complex.ofReal_mul]
    have hv : v=∑ i, c i*(φ (Q.piece i).val).re := by
      simp only [v,y,map_sum,map_smul,smul_eq_mul,Complex.re_sum,Complex.mul_re,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    have hav : a*w ≤ v := by
      rw [hv,show a*w=∑ i, c i*(a*traceFreeDimension hfactor hdiff (Q.piece i)) by
        simp only [w,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring]
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (hproj (Q.piece i) (Q.piece_le i)).1 (hc i))
    have hvb : v ≤ b*w := by
      rw [hv,show b*w=∑ i, c i*(b*traceFreeDimension hfactor hdiff (Q.piece i)) by
        simp only [w,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring]
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (hproj (Q.piece i) (Q.piece_le i)).2 (hc i))
    have hspec := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx.isSelfAdjoint).2.corner_bound
      hfactor hdiff E (hEx.trans hxE.symm) Q (fun i => (c i : ℂ)) hQ
    have htw : |t.re-w| ≤ δ := by
      have h := Complex.abs_re_le_norm (t-(w : ℂ))
      rw [Complex.sub_re,Complex.ofReal_re] at h
      apply h.trans
      rw [hw]
      exact hspec.trans herr.le
    have hφ : |(φ x).re-v| ≤ ‖φ‖*δ := by
      have he : (φ x).re-v=(φ (x-y)).re := by rw [map_sub,Complex.sub_re]
      rw [he]
      exact (Complex.abs_re_le_norm _).trans ((φ.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left herr.le (norm_nonneg φ)))
    have htw' := abs_le.mp htw
    have hφ' := abs_le.mp hφ
    have had := mul_nonneg ha hδ.le
    have hbd := mul_nonneg hb hδ.le
    dsimp only [C] at hCδ
    constructor <;> nlinarith
  constructor
  · apply le_of_forall_pos_le_add
    intro ε hε
    exact (happrox ε hε).1
  · apply le_of_forall_pos_le_add
    intro ε hε
    exact (happrox ε hε).2

end

/-! An actual positive normalized vector functional with arbitrarily small
multiplicative failure of cyclicity on a nonzero corner. No trace is assumed. -/
open scoped CStarAlgebra

/-! A full finite matrix partition can be rebased into every nonzero corner.
The legs are constructed partial isometries, not assumed matrix units. -/
open scoped BigOperators

/-! Extension of a vector functional through actual matrix-partition legs.
Finite coefficient identities transfer the corner quadratic inequality. -/
open scoped BigOperators CStarAlgebra

/-! Globally defined positive unital linear functionals with arbitrarily small multiplicative quadratic trace error. -/
open scoped BigOperators CStarAlgebra

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_NormalTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A genuine linear state with exact equality of real quadratic values,
constructed from the original finite factor predicates by scalar compactness. -/

/-! Construction of a tracial state on the original concrete finite diffuse factor without a supplied trace. -/

/-! Every positive normalized tracial functional agrees with the dimension on
all projections. Lower and upper dyadic bounds use actual partial isometries. -/
section
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.stateDimensionCStar
attribute [local instance] OAI.Generator.Tracial.stateDimensionOrder
local instance stateDimensionPreorder_rc417ad_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.stateDimensionLE
attribute [local instance] OAI.Generator.Tracial.stateDimensionStarOrder
include hfinite in
theorem tracialFunctional_projection_dimension_re (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (φ : M.toStarSubalgebra →L[ℂ] ℂ) (h1 : φ 1=1)
    (hpos : ∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (φ x).re)
    (htrace : ∀ x y : M.toStarSubalgebra, φ (x*y)=φ (y*x))
    (p : AlgebraProjection M) : (φ p.val).re=traceFreeDimension hfactor hdiff p := by
  apply eq_of_all_dyadic_errors
  intro n
  obtain ⟨s,t,_,_,hs,ht,hl,hu,hgap⟩ := traceFreeDyadicSup_rounding hfactor hdiff hfinite
    ⟨1,IsStarProjection.one _⟩ p hunit (one_mul _) n
  have hφl := tracialFunctional_subequivalent φ hpos htrace hs
  have hφu := tracialFunctional_subequivalent φ hpos htrace ht
  rw [tracialFunctional_dyadic_subset_re hfactor hdiff φ h1 htrace] at hφl hφu
  change dyadicWeight n s ≤ traceFreeDimension hfactor hdiff p at hl
  change traceFreeDimension hfactor hdiff p ≤ dyadicWeight n t at hu
  have hn : 0 ≤ 1/(2 : ℝ)^n := by positivity
  rw [show (2 : ℝ)/2^n=2*(1/2^n) by ring]
  apply abs_le.mpr
  constructor <;> linarith

include hfinite in
theorem tracialFunctional_projection_dimension (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (φ : M.toStarSubalgebra →L[ℂ] ℂ) (h1 : φ 1=1)
    (hpos : ∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (φ x).re)
    (hstar : ∀ x : M.toStarSubalgebra, φ (star x)=star (φ x))
    (htrace : ∀ x y : M.toStarSubalgebra, φ (x*y)=φ (y*x))
    (p : AlgebraProjection M) : φ p.val=(traceFreeDimension hfactor hdiff p : ℂ) := by
  apply Complex.ext
  · exact tracialFunctional_projection_dimension_re hfactor hdiff hfinite hunit φ h1 hpos htrace p
  · have h := congrArg Complex.im (hstar p.val)
    rw [p.property.isSelfAdjoint.star_eq] at h
    change (φ p.val).im= -(φ p.val).im at h
    change (φ p.val).im=0
    linarith

end

/-! Identification of the actual tracial state with the spectral dimension
value, and unrestricted additivity for noncommuting self-adjoint operators. -/
section
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.spectralAdditivityCStar
local instance spectralAdditivityOrder_rc417ad_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance spectralAdditivityPreorder_rc417ad_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance spectralAdditivityLE_rc417ad_1 : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance spectralAdditivityStarOrder_rc417ad_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
theorem functional_eq_dimensionSpectralValue (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (φ : M.toStarSubalgebra →L[ℂ] ℂ) (hnorm : ‖φ‖ ≤ 1)
    (hproj : ∀ p : AlgebraProjection M, φ p.val=(traceFreeDimension hfactor hdiff p : ℂ))
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    φ x=dimensionSpectralValue hfactor hdiff hfinite hunit x hx :=
  (functional_isDimensionSpectralValue hfactor hdiff φ hnorm hproj x).unique hfactor hdiff hx
    (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx).2

end

/-! The constructed faithful normalized trace on the original algebra.
Projection-net continuity is proved explicitly; no general normality or
representation theorem is hidden in the definition. -/

/-! The constructed trace is dominated by a finite sum of concrete vector
functionals. The matrix partition is constructed inside the localized corner. -/

/-! Finite vector-functional representation and actual ultraweak continuity of
the constructed trace. No normality criterion is taken as an axiom. -/
open scoped BigOperators CStarAlgebra

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_PerturbationBounds
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Exact 2 ell signed coefficients in each formal row. In particular the
identity prefix label is still a nonidentity basis letter in the formal group. -/

/-! Exact trace-two-norm of the single common logarithmic perturbation. -/
namespace Tracial

/-! Sharp trace-two-norm displacement of a skew-adjoint exponential, via the
real path t ↦ exp(t K). This proves the scalar-calculus estimate used in the
manuscript without an extra exponential factor. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def traceVectorCLM : M.toStarSubalgebra →L[ℂ] H :=
  ({ toFun := fun a => (a : H →L[ℂ] H) τ.vector
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : M.toStarSubalgebra →ₗ[ℂ] H).mkContinuous 1
    (fun a => by
      change τ.norm₂ a ≤ 1*‖a‖
      simpa only [one_mul] using τ.norm₂_le_norm a)

end

/-! A single coordinate satisfies the size and correlation bounds for the
literal word. Its P-valued unitary letters are the retained construction. -/

/-! The manuscript's two perturbation inequalities, constructed under explicit
faithful vector-trace, irreducibility, diffuseness and trace-vector separability
data. No perturbation endpoint or free-moment premise is assumed. -/
open UltrapowerBridge Filter

end Tracial

end Generator

end

end OAI
end


