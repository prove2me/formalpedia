-- Prove2me | Definitions.Def_OAIQ11Fg008
-- name    : OAIQ11Fg008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T09:39:27.07565+00:00
-- url     : https://prove2.me/theorems/e44edfc1-eb55-41ae-8a1b-15a671298124
-- title:
--   Definitions bundle OAIQ11Fg008 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 84 declarations of OpenAI's Lean: 27 definitions and 57 theorems. The definitions and types are `OAI.Generator.Tracial.CornerPartition.blockIndices`, `OAI.Generator.Tracial.CornerPartition.includeUnit`, `OAI.Generator.Tracial.CornerPartition.joint`, `OAI.Generator.Tracial.CornerPartition.mapInclusion`, `OAI.Generator.Tracial.CornerPartition.refineBlocks`, `OAI.Generator.Tracial.CornerPartition.scalarEnergy`, `OAI.Generator.Tracial.CornerUnitary.adjoint`, `OAI.Generator.Tracial.CornerUnitary.patch`, `OAI.Generator.Tracial.EquivalentPartition.ofHalving`, `OAI.Generator.Tracial.EquivalentPartition.rebase`, `OAI.Generator.Tracial.EquivalentPartition.refine`, `OAI.Generator.Tracial.PartialUnitary.Extends`, `OAI.Generator.Tracial.SpectralInterval.approximant`, `OAI.Generator.Tracial.SpectralInterval.child`, `OAI.Generator.Tracial.SpectralInterval.high`, `OAI.Generator.Tracial.SpectralInterval.highProjection`, `OAI.Generator.Tracial.SpectralInterval.level`, `OAI.Generator.Tracial.SpectralInterval.low`, `OAI.Generator.Tracial.SpectralInterval.lowProjection`, `OAI.Generator.Tracial.SpectralInterval.partition`, `OAI.Generator.Tracial.cornerScalar`, `OAI.Generator.Tracial.cornerSpectralCut`, `OAI.Generator.Tracial.cornerSpectralPartition`, `OAI.Generator.Tracial.positiveSupport`, `OAI.Generator.Tracial.traceFreeBinaryPartition`, `OAI.Generator.Tracial.traceFreeDyadicPartition`, `OAI.Generator.Tracial.unitaryPolarOrder`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_CornerTrace`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/CornerTrace.lean), [`FactorGeneration_DyadicComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/DyadicComparison.lean), [`FactorGeneration_FiniteComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/FiniteComparison.lean), [`FactorGeneration_LocalQuantization`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/LocalQuantization.lean), [`FactorGeneration_LocalizedStates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/LocalizedStates.lean), [`FactorGeneration_PartialUnitaries`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/PartialUnitaries.lean), [`FactorGeneration_Pinching`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/Pinching.lean), [`FactorGeneration_ProjectionLimits`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/ProjectionLimits.lean), [`FactorGeneration_SpectralApproximation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/SpectralApproximation.lean), [`FactorGeneration_SpectralPinching`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/SpectralPinching.lean), [`FactorGeneration_Supports`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/Supports.lean).
--
--   **Imports.** It imports the bundles `OAIQ11Fg003`, `OAIQ11Fg004` and `OAIQ11Fg005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ11Fg011` and `OAIQ11Fg012`; the statement `OAI_Generator_FiniteMatrixStage_exists_irreducible_matrix_generated_algebra`; the proofs of `OAI.Generator.FiniteMatrixStage.generated_isII1`, `OAI_Generator_FiniteMatrixStage_two_generators_of_tensor_extensions`, `OAI.Generator.Tracial.CornerPartition.block_commutant_mem_subalgebra`, `OAI.Generator.Tracial.CornerPartition.exists_indexed_orthogonal_refinement_budget`, `OAI_Generator_Tracial_exists_irreducible_centered_partition` and `OAI.Generator.Tracial.exists_normal_matrix_approximation`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ11Fg003
import Definitions.Def_OAIQ11Fg004
import Definitions.Def_OAIQ11Fg005

section
-- module Solutions.OAIQ11_FG.FactorGeneration_ProjectionLimits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A nonzero projection in a diffuse tracial algebra contains nonzero projections of arbitrarily small trace. -/

/-! Monotone projection limits with trace bounds, giving chain bounds for prescribed trace cuts. -/

/-! Exact trace cuts in a diffuse coordinate algebra. -/

/-! Algebraic part of Popa 1308.3982v3, Lemma 3.2: adding a supported
partial unitary in the residual corner. The small mixed-word estimates and
the existence of an appropriate patch are separate analytic requirements. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace CornerUnitary
variable {p q : AlgebraProjection M}

theorem mul_support (v : CornerUnitary p) : v.val*p.val=v.val := by
  have htr : star v.val*(v.val*p.val)=p.val := by
    rw [← mul_assoc,v.initial,p.property.isIdempotentElem.eq]
  have he : star (v.val-v.val*p.val)*(v.val-v.val*p.val)=0 := by
    simp only [star_sub,star_mul,p.property.isSelfAdjoint.star_eq,sub_mul,mul_sub,
      mul_assoc,v.initial,htr,p.property.isIdempotentElem.eq,sub_self]
  exact (sub_eq_zero.mp ((CStarRing.star_mul_self_eq_zero_iff _).mp he)).symm

theorem support_mul (v : CornerUnitary p) : p.val*v.val=v.val := by
  calc p.val*v.val = (v.val*star v.val)*v.val := by rw [v.final]
       _ = v.val*(star v.val*v.val) := mul_assoc _ _ _
       _ = v.val := by rw [v.initial,v.mul_support]

def adjoint (v : CornerUnitary p) : CornerUnitary p :=
  ⟨star v.val,by simpa only [star_star] using v.final,
    by simpa only [star_star] using v.initial⟩

theorem mul_eq_zero (v : CornerUnitary p) (w : CornerUnitary q) (hpq : p.val*q.val=0) :
    v.val*w.val=0 := by
  calc v.val*w.val = (v.val*p.val)*(q.val*w.val) := by rw [v.mul_support,w.support_mul]
       _ = v.val*(p.val*q.val)*w.val := by simp only [mul_assoc]
       _ = 0 := by rw [hpq,mul_zero,zero_mul]

def patch (v : CornerUnitary p) (w : CornerUnitary q) (hpq : p.val*q.val=0) :
    CornerUnitary ⟨p.val+q.val,p.property.add q.property hpq⟩ where
  val := v.val+w.val
  initial := by
    have hqp : q.val*p.val=0 := by
      simpa only [star_mul,p.property.isSelfAdjoint.star_eq,q.property.isSelfAdjoint.star_eq,star_zero]
        using congrArg star hpq
    have h₁ : star v.val*w.val=0 := v.adjoint.mul_eq_zero w hpq
    have h₂ : star w.val*v.val=0 := w.adjoint.mul_eq_zero v hqp
    change star (v.val+w.val)*(v.val+w.val)=p.val+q.val
    rw [star_add,add_mul,mul_add,mul_add,v.initial,w.initial,h₁,h₂,add_zero,zero_add]
  final := by
    have hqp : q.val*p.val=0 := by
      simpa only [star_mul,p.property.isSelfAdjoint.star_eq,q.property.isSelfAdjoint.star_eq,star_zero]
        using congrArg star hpq
    have h₁ : v.val*star w.val=0 := v.mul_eq_zero w.adjoint hpq
    have h₂ : w.val*star v.val=0 := w.mul_eq_zero v.adjoint hqp
    change (v.val+w.val)*star (v.val+w.val)=p.val+q.val
    rw [star_add,add_mul,mul_add,mul_add,v.final,w.final,h₁,h₂,add_zero,zero_add]

end CornerUnitary

end

/-! Dyadic projections inside a diffuse algebra with faithful trace. -/

/-! Finite spectral sums in the constructed dyadic projection algebras. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_CornerTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Trace estimates in the actual ambient algebra. The corner scalar uses
its normalized trace. These estimates do not assume or assert the existence
of a local-quantizing projection. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-- The scalar conditional expectation in pMp, expressed in ambient coordinates. -/
def cornerScalar (p : AlgebraProjection M) (x : M.toStarSubalgebra) : ℂ :=
  τ.trace (p.val*x*p.val) / τ.trace p.val

end

/-! Actual noncommutative L1 on the coordinate algebra: trace(sqrt(x* x)).
The supported L2-to-L1 estimate retains the square root of the support trace.
No quantizing projection or conditional expectation theorem is assumed. -/

/-! A finite compression-energy estimate yields a nonzero corner projection with simultaneous L1 control. -/

/-! The scalar trace estimate for a term with two supported patch letters.
It reduces to the actual compressed middle coefficient and keeps trace(q),
not trace(p), as the scale of the error. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Supports
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Kernel and range projections constructed in the actual von Neumann algebra.
Membership follows from commutant invariance, with no spectral theorem assumed. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- Kernel projections fix the range of every operator they annihilate. -/
theorem kernelProjection_mul_of_mul_eq_zero (x y : M.toStarSubalgebra) (h : x*y=0) :
    (kernelProjection x).val*y=y := by
  apply Subtype.ext
  ext ξ
  apply kernelProjection_fixes
  exact congrArg (fun t : M.toStarSubalgebra => (t : H →L[ℂ] H) ξ) h

/-- For self-adjoint x, its range projection kills every y killed by x. -/
theorem rangeProjection_mul_eq_zero (x y : M.toStarSubalgebra) (hx : IsSelfAdjoint x)
    (h : x*y=0) : (rangeProjection x).val*y=0 := by
  change (1-(kernelProjection (star x)).val)*y=0
  rw [hx.star_eq,sub_mul,one_mul,kernelProjection_mul_of_mul_eq_zero x y h,sub_self]

end

/-! Spectral sign cuts from continuous positive parts and actual range projections.
These are constructed operators, not assumed Borel functional calculus data. -/
open scoped CStarAlgebra
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

attribute [local instance] OAI.Generator.Tracial.positiveSupportCStar
attribute [local instance] OAI.Generator.Tracial.positiveSupportOrder
local instance positiveSupportPreorder_r2465d1_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance positiveSupportLE_r2465d1_1 : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
attribute [local instance] OAI.Generator.Tracial.positiveSupportStarOrder
def positiveSupport (x : M.toStarSubalgebra) : AlgebraProjection M := rangeProjection x⁺

theorem positiveSupport_mul_pos (x : M.toStarSubalgebra) :
    (positiveSupport x).val*x⁺=x⁺ := rangeProjection_mul _

theorem positiveSupport_mul_neg (x : M.toStarSubalgebra) :
    (positiveSupport x).val*x⁻=0 :=
  rangeProjection_mul_eq_zero x⁺ x⁻ (CFC.posPart_nonneg x).isSelfAdjoint
    (CFC.posPart_mul_negPart x)

theorem positiveSupport_mul (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    (positiveSupport x).val*x=x⁺ := by
  calc (positiveSupport x).val*x = (positiveSupport x).val*(x⁺-x⁻) :=
         congrArg (fun z => (positiveSupport x).val*z) (CFC.posPart_sub_negPart x hx).symm
    _ = x⁺ := by rw [mul_sub,positiveSupport_mul_pos,positiveSupport_mul_neg,sub_zero]

theorem mul_positiveSupport (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    x*(positiveSupport x).val=x⁺ := by
  have h := congrArg star (positiveSupport_mul x hx)
  simpa only [star_mul,hx.star_eq,(positiveSupport x).property.isSelfAdjoint.star_eq,
    (CFC.posPart_nonneg x).isSelfAdjoint.star_eq] using h

theorem positiveSupport_commutes (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    Commute (positiveSupport x).val x := by
  show (positiveSupport x).val*x=x*(positiveSupport x).val
  rw [positiveSupport_mul x hx,mul_positiveSupport x hx]

theorem positiveSupport_compression (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    (positiveSupport x).val*x*(positiveSupport x).val=x⁺ := by
  rw [mul_assoc,mul_positiveSupport x hx,positiveSupport_mul_pos]

theorem positiveSupport_complement_mul (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    (1-(positiveSupport x).val)*x = -x⁻ := by
  rw [sub_mul,one_mul,positiveSupport_mul x hx]
  calc x-x⁺ = (x⁺-x⁻)-x⁺ := congrArg (fun z => z-x⁺) (CFC.posPart_sub_negPart x hx).symm
    _ = -x⁻ := by abel

theorem positiveSupport_complement_compression (x : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) :
    (1-(positiveSupport x).val)*x*(1-(positiveSupport x).val) = -x⁻ := by
  have hright : x⁻*(positiveSupport x).val=0 := by
    have h := congrArg star (positiveSupport_mul_neg x)
    simpa only [star_mul,(positiveSupport x).property.isSelfAdjoint.star_eq,
      (CFC.negPart_nonneg x).isSelfAdjoint.star_eq,star_zero] using h
  rw [positiveSupport_complement_mul x hx,mul_sub,mul_one,neg_mul,hright,neg_zero,sub_zero]

end

/-! A polar operator is constructed by extending the isometry on a range.
No polar-decomposition or projection-comparison hypothesis is used. -/

/-! Polar decomposition inside the given concrete von Neumann algebra. -/
open scoped CStarAlgebra

/-! Exact initial and final support projections of the constructed polar part. -/
open scoped CStarAlgebra
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_FiniteComparison
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! The closed span of algebra translates of a projection range gives its
central support. All operators act on the original Hilbert space; no trace,
cyclic vector, separability, finiteness, or comparison theorem is assumed. -/

/-! The original finiteness predicate excludes proper self-equivalence of a
projection. Projection comparison is connected to the unchanged IsII1Factor
predicate, with no representation, trace, or separability premise. -/

/-! Arbitrary-chain bounds with moving orthogonal initial and final supports, obtained from successive fixed-multiplier weak operator limits without a trace. -/
namespace Tracial
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace PartialIsometry

/-- A directed increasing family of square-zero partial isometries has an
upper bound with orthogonal initial/final projections inside p. -/
theorem traceFree_orthogonal_monotone_upper_bound
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (a : ι → PartialIsometry M) (ha : Monotone a)
    (p : AlgebraProjection M) (hp : ∀ i, (a i).support ≤ p)
    (hq : ∀ i, (a i).target ≤ p)
    (ho : ∀ i, (a i).support.val*(a i).target.val=0) :
    ∃ v : PartialIsometry M, (∀ i, a i ≤ v) ∧ v.support ≤ p ∧ v.target ≤ p ∧
      v.support.val*v.target.val=0 := by
  let ω : Ultrafilter ι := Ultrafilter.of atTop
  obtain ⟨T, _, ht⟩ := exists_weak_operator_ultralimit ω
    (fun i => (a i).val.val) 1 (by norm_num) (fun i => (a i).norm_le_one)
  let b : M.toStarSubalgebra := ⟨T, weak_operator_limit_mem M (fun i => (a i).val) T ht⟩
  have hb : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val.val x)) (ω : Filter ι)
      (𝓝 (inner ℂ y (b.val x))) := ht
  have hbp (i : ι) : b*(a i).support.val=(a i).val := by
    apply wot_limit_unique (fun j => (a j).val*(a i).support.val) _ _
      (wot_limit_mul_right _ _ _ hb)
    intro x y
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_ge_atTop i).filter_mono (Ultrafilter.of_le atTop)] with j hj
    exact (congrArg (fun z : M.toStarSubalgebra => inner ℂ y (z.val x)) (ha hj)).symm
  have hab (i : ι) : star (a i).val*b=(a i).support.val := by
    apply wot_limit_unique (fun j => star (a i).val*(a j).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    intro x y
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_ge_atTop i).filter_mono (Ultrafilter.of_le atTop)] with j hj
    exact (congrArg (fun z : M.toStarSubalgebra => inner ℂ y (z.val x))
      (cross_initial_rev (ha hj))).symm
  have hba (i : ι) : star b*(a i).val=(a i).support.val := by
    simpa only [star_mul, star_star, (a i).support.property.isSelfAdjoint.star_eq]
      using congrArg star (hab i)
  have hfix (i : ι) : (b*star b)*(a i).val=(a i).val := by
    rw [mul_assoc, hba i, hbp i]
  have hpartial : (b*star b)*b=b := by
    apply wot_limit_unique (fun i => (b*star b)*(a i).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    simpa only [hfix] using hb
  have hid : (star b*b)*(star b*b)=star b*b := by
    calc _ = star b*((b*star b)*b) := by simp only [mul_assoc]
         _ = star b*b := by rw [hpartial]
  let v : PartialIsometry M := ⟨⟨star b*b, ⟨hid, IsSelfAdjoint.star_mul_self b⟩⟩, b, rfl⟩
  have hcross (i j : ι) : (a i).val*(a j).val=0 := by
    obtain ⟨k,hik,hjk⟩ := exists_ge_ge i j
    exact (a i).mul_eq_zero (a j)
      (projection_orthogonal_of_le (ho k) (support_mono (ha hik)) (target_mono (ha hjk)))
  have hbi (i : ι) : b*(a i).val=0 := by
    apply wot_limit_unique (fun j => (a j).val*(a i).val) _ _
      (wot_limit_mul_right _ _ _ hb)
    simpa only [hcross] using (fun x y : H =>
      (tendsto_const_nhds : Tendsto (fun _ : ι => inner ℂ y ((0 : M.toStarSubalgebra).val x))
        (ω : Filter ι) (𝓝 (inner ℂ y ((0 : M.toStarSubalgebra).val x)))))
  have hbb : b*b=0 := by
    apply wot_limit_unique (fun i => b*(a i).val) _ _ (wot_limit_mul_left _ _ _ hb)
    simpa only [hbi] using (fun x y : H =>
      (tendsto_const_nhds : Tendsto (fun _ : ι => inner ℂ y ((0 : M.toStarSubalgebra).val x))
        (ω : Filter ι) (𝓝 (inner ℂ y ((0 : M.toStarSubalgebra).val x)))))
  refine ⟨v, hbp, ?_, ?_, ?_⟩
  · apply (v.support_le_iff_mul p).mpr
    apply wot_limit_unique (fun i => (a i).val*p.val) _ _
      (wot_limit_mul_right _ _ _ hb)
    simpa only [fun i => ((a i).support_le_iff_mul p).mp (hp i)] using hb
  · apply (v.target_le_iff_mul p).mpr
    apply wot_limit_unique (fun i => p.val*(a i).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    simpa only [fun i => ((a i).target_le_iff_mul p).mp (hq i)] using hb
  · change (star b*b)*(b*star b)=0
    calc _ = star b*(b*b)*star b := by simp only [mul_assoc]
         _ = 0 := by rw [hbb,mul_zero,zero_mul]

theorem traceFree_orthogonal_chain_upper_bound (c : Set (PartialIsometry M))
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (p : AlgebraProjection M) (hp : ∀ v ∈ c, v.support ≤ p)
    (hq : ∀ v ∈ c, v.target ≤ p)
    (ho : ∀ v ∈ c, v.support.val*v.target.val=0) :
    ∃ v : PartialIsometry M, (∀ w ∈ c, w ≤ v) ∧ v.support ≤ p ∧ v.target ≤ p ∧
      v.support.val*v.target.val=0 := by
  let : Nonempty c := hne.to_subtype
  let : IsDirected c (· ≤ ·) := ⟨by
    intro u v
    rcases hc.total u.property v.property with h | h
    · exact ⟨v,h,le_rfl⟩
    · exact ⟨u,le_rfl,h⟩⟩
  obtain ⟨v,hv,hvp,hvq,hvo⟩ := traceFree_orthogonal_monotone_upper_bound
    (fun w : c => w.val) (fun _ _ h => h) p
    (fun w => hp w.val w.property) (fun w => hq w.val w.property)
    (fun w => ho w.val w.property)
  exact ⟨v,fun w hw => hv ⟨w,hw⟩,hvp,hvq,hvo⟩

theorem traceFree_exists_maximal_orthogonal (p : AlgebraProjection M) :
    ∃ v : PartialIsometry M, v.support ≤ p ∧ v.target ≤ p ∧
      v.support.val*v.target.val=0 ∧
      ∀ w : PartialIsometry M, w.support ≤ p → w.target ≤ p →
        w.support.val*w.target.val=0 → v ≤ w → w ≤ v := by
  let S : Set (PartialIsometry M) :=
    {v | v.support ≤ p ∧ v.target ≤ p ∧ v.support.val*v.target.val=0}
  obtain ⟨v,hv⟩ := zorn_le₀ S (by
    intro c hc hchain
    by_cases hne : c.Nonempty
    · obtain ⟨v,hcv,hvp,hvq,hvo⟩ := traceFree_orthogonal_chain_upper_bound c hchain hne p
        (fun w hw => (hc hw).1) (fun w hw => (hc hw).2.1) (fun w hw => (hc hw).2.2)
      exact ⟨v,⟨hvp,hvq,hvo⟩,hcv⟩
    · refine ⟨zero,⟨?_,?_,?_⟩,?_⟩
      · change p.val*0=0
        exact mul_zero _
      · apply (zero.target_le_iff_mul p).mpr
        exact mul_zero _
      · exact zero_mul _
      · intro w hw
        exact (hne ⟨w,hw⟩).elim)
  exact ⟨v,hv.1.1,hv.1.2.1,hv.1.2.2,fun w hp hq ho h => hv.2 ⟨hp,hq,ho⟩ h⟩

/-! Simultaneous least initial and final support bounds for arbitrary directed
partial-isometry nets. The actual ultralimit is chosen once for all bounds. -/

end PartialIsometry
end Tracial

/-! Complete actual partial isometries to unitaries in a finite factor.
The construction uses projection comparison and finiteness, without a trace. -/
open scoped CStarAlgebra
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
attribute [local instance] OAI.Generator.Tracial.unitaryPolarCStar
local instance unitaryPolarOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfactor hfinite in
theorem PartialIsometry.exists_unitary_extension (v : PartialIsometry M) :
    ∃ u : unitary M.toStarSubalgebra, (u : M.toStarSubalgebra)*v.support.val=v.val := by
  let p : AlgebraProjection M := ⟨1-v.support.val,v.support.property.one_sub⟩
  let q : AlgebraProjection M := ⟨1-v.target.val,v.target.property.one_sub⟩
  obtain ⟨w,hwp,hwq,hw⟩ := traceFree_exists_partialIsometry_comparison hfactor p q
  have hp : v.support.val*w.support.val=0 := by
    calc _ = v.support.val*(p.val*w.support.val) := by rw [hwp]
      _ = (v.support.val*p.val)*w.support.val := (mul_assoc _ _ _).symm
      _ = 0 := by
        change (v.support.val*(1-v.support.val))*w.support.val=0
        rw [v.support.property.mul_one_sub_self,zero_mul]
  have hq : v.target.val*w.target.val=0 := by
    calc _ = v.target.val*(q.val*w.target.val) := by rw [hwq]
      _ = (v.target.val*q.val)*w.target.val := (mul_assoc _ _ _).symm
      _ = 0 := by
        change (v.target.val*(1-v.target.val))*w.target.val=0
        rw [v.target.property.mul_one_sub_self,zero_mul]
  let a := v.patch w hp hq
  have hi : star a.val*a.val=1 := by
    rcases hw with hw | hw
    · rw [a.initial]
      change v.support.val+w.support.val=1
      rw [hw]
      change v.support.val+(1-v.support.val)=1
      abel
    · have hf : a.val*star a.val=1 := by
        change a.target.val=1
        rw [PartialIsometry.patch_target,hw]
        change v.target.val+(1-v.target.val)=1
        abel
      have h := hfinite (star a.val) (by simpa only [star_star] using hf)
      simpa only [star_star] using h
  exact ⟨⟨a.val,⟨hi,hfinite a.val hi⟩⟩,v.le_patch w hp hq⟩

end Tracial

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
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Tracial
variable {M : VonNeumannAlgebra H}

/-- The two equivalent halves are constructed by an actual partial isometry.
No trace, finite-isometry property, or separability is needed for this lemma. -/
theorem traceFree_exists_halving
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (p : AlgebraProjection M) :
    ∃ v : PartialIsometry M, v.support.val*v.target.val=0 ∧
      v.support.val+v.target.val=p.val := by
  obtain ⟨v,hvp,hvq,hvo,hmax⟩ := PartialIsometry.traceFree_exists_maximal_orthogonal p
  let t := orthogonalSum v.support v.target hvo
  have htp : t ≤ p := orthogonalSum_le hvo hvp hvq
  let r : AlgebraProjection M := ⟨p.val-t.val,t.property.sub_of_mul_eq_right p.property htp⟩
  have hrp : r ≤ p := by
    change p.val*(p.val-t.val)=p.val-t.val
    rw [mul_sub,p.property.isIdempotentElem.eq,htp]
  have htr : t.val*r.val=0 := by
    change t.val*(p.val-t.val)=0
    rw [mul_sub,projection_mul_of_le htp,t.property.isIdempotentElem.eq,sub_self]
  have hr0 : r.val=0 := by
    by_contra hr
    obtain ⟨q,s,hqr,hsr,hq0,hs0,hqs,_⟩ := traceFree_exists_orthogonal_split hdiff r hr
    obtain ⟨w,hwq,hws,hw0⟩ :=
      traceFree_exists_nonzero_partialIsometry_between_projections hfactor q s hq0 hs0
    have hwr : w.support ≤ r := hwq.trans hqr
    have hwtr : w.target ≤ r := hws.trans hsr
    have hvt : v.support ≤ t := le_orthogonalSum_left _ _ hvo
    have hvtt : v.target ≤ t := le_orthogonalSum_right _ _ hvo
    have hpw := projection_orthogonal_of_le htr hvt hwr
    have hqw := projection_orthogonal_of_le htr hvtt hwtr
    have hcross := projection_orthogonal_of_le htr hvt hwtr
    have hcross' := PartialIsometry.orthogonal_reverse _ _
      (projection_orthogonal_of_le htr hvtt hwr)
    have hwo := projection_orthogonal_of_le hqs hwq hws
    let u := v.patch w hpw hqw
    have hup : u.support ≤ p := orthogonalSum_le hpw hvp (hwr.trans hrp)
    have huq : u.target ≤ p := by
      change p.val*u.target.val=u.target.val
      rw [PartialIsometry.patch_target]
      rw [mul_add,hvq,show p.val*w.target.val=w.target.val from hwtr.trans hrp]
    have huo : u.support.val*u.target.val=0 := by
      rw [PartialIsometry.patch_target]
      change (v.support.val+w.support.val)*(v.target.val+w.target.val)=0
      rw [add_mul,mul_add,mul_add,hvo,hcross,hcross',hwo,add_zero,zero_add]
    have hvu : v ≤ u := v.le_patch w hpw hqw
    exact (v.patch_ne w hpw hqw hw0) (le_antisymm (hmax u hup huq huo hvu) hvu)
  exact ⟨v,hvo,(sub_eq_zero.mp hr0).symm⟩

end Tracial

end

/-! Finite partitions with explicit equivalence witnesses and compatible binary
refinement. The common initial projection is halved once and its two pieces
are transported to every old piece, so all new pieces remain equivalent. -/
section
open scoped BigOperators
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Refinement is performed on the common initial corner and transported. -/
def refine (E : EquivalentPartition p ι) (F : EquivalentPartition E.base κ) :
    EquivalentPartition p (ι × κ) where
  base := F.base
  leg a := (E.leg a.1).compose (F.leg a.2) (by rw [E.initial]; exact F.bound a.2)
  initial a := F.initial a.2
  cross a b hab := by
    change star ((E.leg a.1).val*(F.leg a.2).val)*
      ((E.leg b.1).val*(F.leg b.2).val)=0
    rw [star_mul]
    have hr : (star (F.leg a.2).val*star (E.leg a.1).val)*
        ((E.leg b.1).val*(F.leg b.2).val)=
        star (F.leg a.2).val*(star (E.leg a.1).val*(E.leg b.1).val)*(F.leg b.2).val := by
      simp only [mul_assoc]
    rw [hr]
    by_cases h : a.1=b.1
    · rw [h,(E.leg b.1).initial,E.initial,mul_assoc,
        ((F.leg b.2).target_le_iff_mul E.base).mp (F.bound b.2)]
      exact F.cross a.2 b.2 (fun hh => hab (Prod.ext h hh))
    · rw [E.cross a.1 b.1 h,mul_zero,zero_mul]
  total := by
    rw [Fintype.sum_prod_type]
    simp only [PartialIsometry.compose_target,← Finset.sum_mul,← Finset.mul_sum,F.total]
    have h (i : ι) : (E.leg i).val*E.base.val=(E.leg i).val := by
      rw [← E.initial i,(E.leg i).mul_support]
    simp only [h]
    exact E.total
  bound a := ((E.leg a.1).compose_target_le (F.leg a.2) _).trans (E.bound a.1)

theorem refine_parent (E : EquivalentPartition p ι) (F : EquivalentPartition E.base κ) (i : ι) :
    (∑ j, ((E.refine F).leg (i,j)).target.val)=(E.leg i).target.val := by
  change (∑ j, ((E.leg i).compose (F.leg j) (by rw [E.initial]; exact F.bound j)).target.val)=_
  simp only [PartialIsometry.compose_target,← Finset.sum_mul,← Finset.mul_sum,F.total]
  rw [← E.initial i,(E.leg i).mul_support]
  rfl

/-- Two equivalent orthogonal halves, as a family with a common initial corner. -/
def ofHalving (v : PartialIsometry M) (ho : v.support.val*v.target.val=0)
    (hp : v.support.val+v.target.val=p.val) : EquivalentPartition p Bool where
  base := v.support
  leg b := if b then v else PartialIsometry.onProjection v.support
  initial b := by cases b <;> rfl
  cross b c hbc := by
    have h : v.support.val*v.val=0 := by
      calc _ = v.support.val*(v.target.val*v.val) := by rw [v.target_mul]
           _ = 0 := by rw [← mul_assoc,ho,zero_mul]
    cases b <;> cases c
    · exact (hbc rfl).elim
    · simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,PartialIsometry.onProjection,
        v.support.property.isSelfAdjoint.star_eq] using h
    · simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,PartialIsometry.onProjection,
        star_mul,star_zero,v.support.property.isSelfAdjoint.star_eq] using congrArg star h
    · exact (hbc rfl).elim
  total := by
    simp only [Fintype.sum_bool,ite_true, if_true,Bool.false_eq_true,ite_false, if_false,
      PartialIsometry.onProjection_target]
    exact (add_comm _ _).trans hp
  bound b := by
    have he : orthogonalSum v.support v.target ho=p := Subtype.ext hp
    cases b
    · simpa only [Bool.false_eq_true,ite_false, if_false,PartialIsometry.onProjection_target,he]
        using le_orthogonalSum_left v.support v.target ho
    · simpa only [ite_true, if_true,he] using le_orthogonalSum_right v.support v.target ho

end EquivalentPartition
end Tracial

/-! Coherent dyadic equivalent partitions and matrix units, constructed from
scalar center and diffuseness without a trace. DyadicIndex is reused as a
finite binary index type; no tracial partition construction is used. -/
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Tracial
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

/-- Choose the actual two-leg partition supplied by trace-free halving. -/
def traceFreeBinaryPartition (p : AlgebraProjection M) : EquivalentPartition p Bool :=
  let h := traceFree_exists_halving hfactor hdiff p
  EquivalentPartition.ofHalving h.choose h.choose_spec.1 h.choose_spec.2

/-- A coherent family: each successor halves the previous common initial
projection once and transports that halving to all its equivalent pieces. -/
def traceFreeDyadicPartition (p : AlgebraProjection M) :
    (n : ℕ) → EquivalentPartition p (DyadicIndex n)
  | 0 => EquivalentPartition.singleton p
  | n+1 =>
    let E := traceFreeDyadicPartition p n
    E.refine (traceFreeBinaryPartition hfactor hdiff E.base)

end Tracial

end

/-! Actual sums of countable orthogonal partial isometries, including least
initial/final support identities. No trace or countable-cofinality premise. -/
namespace Tracial

section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

variable (a : ℕ → PartialIsometry M)
variable (hp : ∀ i j, i ≠ j → (a i).support.val*(a j).support.val=0)
variable (hq : ∀ i j, i ≠ j → (a i).target.val*(a j).target.val=0)

include hp hq in
/-- An actual infinite orthogonal sum, with least upper bound characterizations
for both support projections. It may be used to construct a shift. -/
theorem traceFree_orthogonal_sum :
    ∃ v : PartialIsometry M, (∀ i, a i ≤ v) ∧
      (∀ p : AlgebraProjection M, v.support ≤ p ↔ ∀ i, (a i).support ≤ p) ∧
      (∀ q : AlgebraProjection M, v.target ≤ q ↔ ∀ i, (a i).target ≤ q) := by
  obtain ⟨v,hv,hs,ht⟩ := traceFree_monotone_least_supports
    (orthogonalPartialSum a hp hq) (orthogonalPartialSum_monotone a hp hq)
  have hav (i : ℕ) : a i ≤ v :=
    (le_orthogonalPartialSum a hp hq i (i+1) (Nat.lt_succ_self i)).trans (hv (i+1))
  refine ⟨v,hav,?_,?_⟩
  · intro p
    refine ⟨fun h i => (support_mono (hav i)).trans h, fun h => hs p ?_⟩
    intro n
    change p.val*(orthogonalPartialSum a hp hq n).support.val=_
    rw [orthogonalPartialSum_support,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => h i)
  · intro q
    refine ⟨fun h i => (target_mono (hav i)).trans h, fun h => ht q ?_⟩
    intro n
    change q.val*(orthogonalPartialSum a hp hq n).target.val=_
    rw [orthogonalPartialSum_target,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => h i)

end PartialIsometry
end

/-! Projection equivalence and subequivalence are witnessed by actual partial
isometries in the original algebra. No dimension or trace oracle is used. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

theorem rangeLink_target (v w : PartialIsometry M) (h : v.support=w.support) :
    (rangeLink v w h).target=w.target :=
  compose_target_of_eq w v.adjoint ((adjoint_target v).trans h)

end PartialIsometry

/-! Finiteness excludes an infinite family of nonzero equivalent orthogonal
projections. The shift and both of its least supports are constructed. -/

/-! Finite comparison and cancellation with actual partial isometries.
No trace, dimension, or representation is assumed. -/
end Tracial

/-! Actual finite sums of orthogonal partial isometries and finite subsets of
equivalent partitions. The finite subset is arbitrary, without an index order. -/
open scoped BigOperators

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Pinching
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Finite pinching in the actual ambient algebra. The squared L2 energy
is a sum of the energies of the mutually orthogonal compression blocks.
These identities do not postulate a local-quantizing partition. -/

/-! Actual finite refinement of a corner partition by partitions of its blocks.
The dependent family of block sizes is flattened without changing any piece.
No small-energy partition is an input to these constructions. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace CornerPartition
variable {p : AlgebraProjection M}

theorem ofFamily_pinch {ι : Type*} [Fintype ι] (a : ι → AlgebraProjection M)
    (ha : ∀ i j, i ≠ j → (a i).val*(a j).val=0)
    (ht : ∑ i, (a i).val=p.val) (x : M.toStarSubalgebra) :
    (ofFamily a ha ht).pinch x = ∑ i, (a i).val*x*(a i).val := by
  exact Equiv.sum_comp (Fintype.equivFin ι).symm (fun i => (a i).val*x*(a i).val)

variable (Q : CornerPartition p) (R : (i : Fin Q.size) → CornerPartition (Q.piece i))

/-- All blocks are replaced by their chosen finite subpartitions. -/
def refineBlocks : CornerPartition p :=
  ofFamily (fun a : (i : Fin Q.size) × Fin (R i).size => (R a.1).piece a.2)
    (Q.blockFamily_orthogonal R) (Q.blockFamily_total R)

end CornerPartition

end

/-! Centered energy and the block scalar term that refinement preserves.
A blockwise descent applies to centered compressions, not to their full energy. -/

/-! Energy of compatible block refinements, including the scalar term.
The scalar term is necessary even when the original operator has trace zero. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)
variable (R : (i : Fin Q.size) → CornerPartition (Q.piece i))

/-- The part of the compression energy fixed by the current block traces. -/
def scalarEnergy (x : M.toStarSubalgebra) : ℝ :=
  ∑ i, ‖cornerScalar τ (Q.piece i) x‖^2 * (τ.trace (Q.piece i).val).re

end CornerPartition

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_SpectralPinching
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.vectorOrbitClosure_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual sign splitting inside a prescribed residual corner. -/
section
open scoped CStarAlgebra BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

attribute [local instance] OAI.Generator.Tracial.cornerCutCStar
attribute [local instance] OAI.Generator.Tracial.cornerCutOrder
attribute [local instance] OAI.Generator.Tracial.cornerCutPreorder
attribute [local instance] OAI.Generator.Tracial.cornerCutLE
attribute [local instance] OAI.Generator.Tracial.cornerCutStarOrder
theorem positiveSupport_le_corner (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x)
    (p : AlgebraProjection M) (hp : x*p.val=x) : positiveSupport x ≤ p := by
  apply (rangeProjection_le_iff _ p).mpr
  have h := congrArg star (positivePart_right_support x hx p hp)
  simpa only [star_mul,p.property.isSelfAdjoint.star_eq,
    (CFC.posPart_nonneg x).isSelfAdjoint.star_eq] using h

def cornerSpectralCut (p : AlgebraProjection M) (x : M.toStarSubalgebra) (t : ℝ) :
    AlgebraProjection M := positiveSupport (cornerSpectralShift p x t)

theorem cornerSpectralCut_le (p : AlgebraProjection M) (x : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) (t : ℝ) : cornerSpectralCut p x t ≤ p :=
  positiveSupport_le_corner _ (cornerSpectralShift_selfAdjoint p x hx t) p
    (cornerSpectralShift_support p x t)

namespace CornerPartition

theorem binary_pinch (p q : AlgebraProjection M) (hq : q ≤ p) (x : M.toStarSubalgebra) :
    (binary p q hq).pinch x = q.val*x*q.val+(p.val-q.val)*x*(p.val-q.val) := by
  rw [binary,ofFamily_pinch,Fintype.sum_bool]
  rfl

end CornerPartition

/-- The finite corner partition constructed from the shifted positive part. -/
def cornerSpectralPartition (p : AlgebraProjection M) (x : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) (t : ℝ) : CornerPartition p :=
  CornerPartition.binary p (cornerSpectralCut p x t) (cornerSpectralCut_le p x hx t)

/-- Its high block has the promised spectral lower bound. -/
theorem cornerSpectralCut_lower (p : AlgebraProjection M) (x : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) (t : ℝ) :
    0 ≤ (cornerSpectralCut p x t).val*x*(cornerSpectralCut p x t).val -
      (t : ℂ) • (cornerSpectralCut p x t).val := by
  have hc := positiveSupport_compression (cornerSpectralShift p x t)
    (cornerSpectralShift_selfAdjoint p x hx t)
  have hqp := cornerSpectralCut_le p x hx t
  have hleft : p.val*(cornerSpectralCut p x t).val=(cornerSpectralCut p x t).val := hqp
  have he : (cornerSpectralCut p x t).val * cornerSpectralShift p x t *
      (cornerSpectralCut p x t).val =
      (cornerSpectralCut p x t).val*x*(cornerSpectralCut p x t).val -
        (t : ℂ) • (cornerSpectralCut p x t).val := by
    simp only [cornerSpectralShift,mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
    simp only [← mul_assoc,projection_mul_of_le hqp]
    simp only [mul_assoc,hleft,(cornerSpectralCut p x t).property.isIdempotentElem.eq]
  rw [← he]
  exact hc.symm ▸ CFC.posPart_nonneg _

/-- The low block has the opposite shifted sign in the same corner. -/
theorem cornerSpectralCut_upper (p : AlgebraProjection M) (x : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) (t : ℝ) :
    let r := p.val-(cornerSpectralCut p x t).val
    r*x*r-(t : ℂ) • r ≤ 0 := by
  let q := cornerSpectralCut p x t
  let r : AlgebraProjection M := ⟨p.val-q.val,q.property.sub_of_mul_eq_right p.property
    (cornerSpectralCut_le p x hx t)⟩
  have hrp : r ≤ p := by
    change p.val*(p.val-q.val)=p.val-q.val
    rw [mul_sub,p.property.isIdempotentElem.eq,cornerSpectralCut_le p x hx t]
  have hrleft : p.val*r.val=r.val := hrp
  have hs := cornerSpectralShift_support p x t
  have hsl : p.val*cornerSpectralShift p x t=cornerSpectralShift p x t := by
    have h := congrArg star hs
    simpa only [star_mul,p.property.isSelfAdjoint.star_eq,
      (cornerSpectralShift_selfAdjoint p x hx t).star_eq] using h
  have hc : r.val*cornerSpectralShift p x t*r.val = -(cornerSpectralShift p x t)⁻ := by
    change (p.val-q.val)*cornerSpectralShift p x t*(p.val-q.val)=_
    have he : (p.val-q.val)*cornerSpectralShift p x t*(p.val-q.val) =
        (1-q.val)*cornerSpectralShift p x t*(1-q.val) := by
      simp only [sub_mul,mul_sub,one_mul,mul_one,hsl,hs,mul_assoc]
    rw [he]
    exact positiveSupport_complement_compression _ (cornerSpectralShift_selfAdjoint p x hx t)
  have he : r.val*cornerSpectralShift p x t*r.val=r.val*x*r.val-(t : ℂ) • r.val := by
    simp only [cornerSpectralShift,mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
    simp only [← mul_assoc,projection_mul_of_le hrp]
    simp only [mul_assoc,hrleft,r.property.isIdempotentElem.eq]
  change r.val*x*r.val-(t : ℂ) • r.val ≤ 0
  rw [← he,hc]
  exact neg_nonpos.mpr (CFC.negPart_nonneg _)

end

/-! The constructed spectral splitting preserves the compressed operator.
This is distinct from using that splitting to reduce other operators' energy. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace CornerPartition

theorem binary_pinch_of_commutes (p q : AlgebraProjection M) (hq : q ≤ p)
    (x : M.toStarSubalgebra) (hl : p.val*x=x) (hr : x*p.val=x)
    (hc : q.val*x=x*q.val) : (binary p q hq).pinch x=x := by
  have hqq : q.val*x*q.val=q.val*x := by
    rw [hc,mul_assoc,q.property.isIdempotentElem.eq]
  rw [binary_pinch]
  simp only [sub_mul,mul_sub,hl,hr,hqq]
  rw [hc]
  simp only [mul_assoc,projection_mul_of_le hq]
  abel

end CornerPartition

theorem cornerSpectralCut_commutes (p : AlgebraProjection M) (x : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) (t : ℝ) :
    (cornerSpectralCut p x t).val*(p.val*x*p.val)=
      (p.val*x*p.val)*(cornerSpectralCut p x t).val := by
  let q := cornerSpectralCut p x t
  have h := (positiveSupport_commutes (cornerSpectralShift p x t)
    (cornerSpectralShift_selfAdjoint p x hx t)).eq
  change q.val*(p.val*x*p.val-(t : ℂ) • p.val) =
    (p.val*x*p.val-(t : ℂ) • p.val)*q.val at h
  have hqp := cornerSpectralCut_le p x hx t
  have hleft : p.val*q.val=q.val := hqp
  have hright : q.val*p.val=q.val := projection_mul_of_le hqp
  simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,
    hright,hleft] at h
  exact sub_left_inj.mp h

theorem cornerSpectralPartition_pinch (p : AlgebraProjection M) (x : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) (t : ℝ) :
    (cornerSpectralPartition p x hx t).pinch x=p.val*x*p.val := by
  rw [← (cornerSpectralPartition p x hx t).pinch_corner_compression]
  apply CornerPartition.binary_pinch_of_commutes
  · simp only [← mul_assoc,p.property.isIdempotentElem.eq]
  · simp only [mul_assoc,p.property.isIdempotentElem.eq]
  · exact cornerSpectralCut_commutes p x hx t

end

/-! Interval bounds propagated through constructed spectral corner splits. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace SpectralInterval
variable {x : M.toStarSubalgebra} (I : SpectralInterval x) (hx : IsSelfAdjoint x)

def highProjection : AlgebraProjection M := cornerSpectralCut I.proj x I.midpoint

def lowProjection : AlgebraProjection M :=
  ⟨I.proj.val-(I.highProjection).val,
    (I.highProjection).property.sub_of_mul_eq_right I.proj.property
      (cornerSpectralCut_le I.proj x hx I.midpoint)⟩

theorem high_le (hx : IsSelfAdjoint x) : I.highProjection ≤ I.proj :=
  cornerSpectralCut_le I.proj x hx I.midpoint

theorem low_le : I.lowProjection hx ≤ I.proj := by
  change I.proj.val*(I.proj.val-(I.highProjection).val)=I.proj.val-I.highProjection.val
  rw [mul_sub,I.proj.property.isIdempotentElem.eq,I.high_le hx]

attribute [local instance] OAI.Generator.Tracial.intervalCStar
attribute [local instance] OAI.Generator.Tracial.intervalOrder
attribute [local instance] OAI.Generator.Tracial.intervalPreorder
attribute [local instance] OAI.Generator.Tracial.intervalLE
attribute [local instance] OAI.Generator.Tracial.intervalStarOrder
def high : SpectralInterval x where
  proj := I.highProjection
  lo := I.midpoint
  hi := I.hi
  lower := cornerSpectralCut_lower I.proj x hx I.midpoint
  upper := upper_bound_compress (I.high_le hx) x I.hi I.upper

def low : SpectralInterval x where
  proj := I.lowProjection hx
  lo := I.lo
  hi := I.midpoint
  lower := lower_bound_compress (I.low_le hx) x I.lo I.lower
  upper := cornerSpectralCut_upper I.proj x hx I.midpoint

def child (b : Bool) : SpectralInterval x := if b then I.high hx else I.low hx

theorem child_le (b : Bool) : (I.child hx b).proj ≤ I.proj := by
  cases b
  · exact I.low_le hx
  · exact I.high_le hx

theorem child_width (b : Bool) :
    (I.child hx b).hi-(I.child hx b).lo=(I.hi-I.lo)/2 := by
  cases b <;> dsimp [child,high,low,midpoint] <;> ring

theorem child_total : (I.child hx false).proj.val+(I.child hx true).proj.val=I.proj.val := by
  change (I.proj.val-(I.highProjection).val)+(I.highProjection).val=I.proj.val
  exact sub_add_cancel _ _

theorem child_orthogonal (b c : Bool) (h : b ≠ c) :
    (I.child hx b).proj.val*(I.child hx c).proj.val=0 := by
  have hl : I.proj.val*(I.highProjection).val=(I.highProjection).val := I.high_le hx
  have hr := projection_mul_of_le (I.high_le hx)
  cases b <;> cases c
  · exact (h rfl).elim
  · change (I.proj.val-(I.highProjection).val)*(I.highProjection).val=0
    rw [sub_mul,hl,(I.highProjection).property.isIdempotentElem.eq,sub_self]
  · change (I.highProjection).val*(I.proj.val-(I.highProjection).val)=0
    rw [mul_sub,hr,(I.highProjection).property.isIdempotentElem.eq,sub_self]
  · exact (h rfl).elim

theorem child_compression_total :
    (I.child hx false).proj.val*x*(I.child hx false).proj.val+
    (I.child hx true).proj.val*x*(I.child hx true).proj.val=I.proj.val*x*I.proj.val := by
  have h := cornerSpectralPartition_pinch I.proj x hx I.midpoint
  rw [cornerSpectralPartition,CornerPartition.binary_pinch] at h
  exact (add_comm _ _).trans h

end SpectralInterval

end

/-! Finite dyadic trees of actual spectral interval cuts. -/
section
open scoped CStarAlgebra BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace SpectralInterval
variable {x : M.toStarSubalgebra} (I : SpectralInterval x) (hx : IsSelfAdjoint x)

def level (I : SpectralInterval x) (hx : IsSelfAdjoint x) : (n : ℕ) → DyadicIndex n → SpectralInterval x
  | 0,_ => I
  | n+1,i => (level I hx n i.1).child hx i.2

theorem level_le : ∀ n i, (I.level hx n i).proj ≤ I.proj
  | 0,_ => le_refl _
  | n+1,i => ((I.level hx n i.1).child_le hx i.2).trans (level_le n i.1)

theorem level_width : ∀ n i,
    (I.level hx n i).hi-(I.level hx n i).lo = (I.hi-I.lo)/(2:ℝ)^n
  | 0,_ => by simp [level]
  | n+1,i => by
    change ((I.level hx n i.1).child hx i.2).hi-
      ((I.level hx n i.1).child hx i.2).lo=_
    rw [child_width,level_width n i.1,pow_succ,div_div]

theorem level_total : ∀ n, (∑ i : DyadicIndex n, (I.level hx n i).proj.val)=I.proj.val
  | 0 => by
    change (∑ _ : Unit, I.proj.val)=I.proj.val
    simp
  | n+1 => by
    change (∑ i : DyadicIndex n × Bool, ((I.level hx n i.1).child hx i.2).proj.val)=_
    rw [Fintype.sum_prod_type]
    have he (i : DyadicIndex n) :
        (∑ b : Bool, ((I.level hx n i).child hx b).proj.val)=(I.level hx n i).proj.val := by
      rw [Fintype.sum_bool,add_comm,child_total]
    simp only [he]
    exact level_total n

theorem level_orthogonal : ∀ n (i j : DyadicIndex n), i ≠ j →
    (I.level hx n i).proj.val*(I.level hx n j).proj.val=0
  | 0,i,j,h => (h (@Subsingleton.elim Unit _ i j)).elim
  | n+1,⟨i,b⟩,⟨j,c⟩,h => by
    change ((I.level hx n i).child hx b).proj.val*((I.level hx n j).child hx c).proj.val=0
    by_cases hij : i=j
    · subst j
      exact (I.level hx n i).child_orthogonal hx b c (fun hbc => h (by cases hbc; rfl))
    · exact orthogonal_subprojections (level_orthogonal n i j hij)
        ((I.level hx n i).child_le hx b) ((I.level hx n j).child_le hx c)

theorem level_compression_total : ∀ n,
    (∑ i : DyadicIndex n, (I.level hx n i).proj.val*x*(I.level hx n i).proj.val) =
      I.proj.val*x*I.proj.val
  | 0 => by
    change (∑ _ : Unit, I.proj.val*x*I.proj.val)=I.proj.val*x*I.proj.val
    simp
  | n+1 => by
    change (∑ i : DyadicIndex n × Bool, ((I.level hx n i.1).child hx i.2).proj.val*x*
      ((I.level hx n i.1).child hx i.2).proj.val)=_
    rw [Fintype.sum_prod_type]
    have he (i : DyadicIndex n) :
        (∑ b : Bool, ((I.level hx n i).child hx b).proj.val*x*
          ((I.level hx n i).child hx b).proj.val)=
        (I.level hx n i).proj.val*x*(I.level hx n i).proj.val := by
      rw [Fintype.sum_bool,add_comm,child_compression_total]
    simp only [he]
    exact level_compression_total n

def partition (n : ℕ) : CornerPartition I.proj :=
  CornerPartition.ofFamily (fun i : DyadicIndex n => (I.level hx n i).proj)
    (I.level_orthogonal hx n) (I.level_total hx n)

theorem partition_pinch (n : ℕ) : (I.partition hx n).pinch x=I.proj.val*x*I.proj.val := by
  rw [partition,CornerPartition.ofFamily_pinch]
  exact I.level_compression_total hx n

end SpectralInterval

/-! Finite spectral approximations constructed by successive sign cuts.
The approximation bound is proved from the leaf intervals. -/

namespace SpectralInterval
variable {x : M.toStarSubalgebra} (I : SpectralInterval x) (hx : IsSelfAdjoint x)

def approximant (n : ℕ) : M.toStarSubalgebra :=
  ∑ i : DyadicIndex n, ((I.level hx n i).lo : ℂ) • (I.level hx n i).proj.val

theorem approximant_error_sum (n : ℕ) :
    I.proj.val*x*I.proj.val-I.approximant hx n =
      ∑ i : DyadicIndex n, ((I.level hx n i).proj.val*x*(I.level hx n i).proj.val-
        ((I.level hx n i).lo : ℂ) • (I.level hx n i).proj.val) := by
  rw [Finset.sum_sub_distrib,I.level_compression_total hx]
  rfl

attribute [local instance] OAI.Generator.Tracial.approximationCStar
attribute [local instance] OAI.Generator.Tracial.approximationOrder
attribute [local instance] OAI.Generator.Tracial.approximationPreorder
attribute [local instance] OAI.Generator.Tracial.approximationLE
attribute [local instance] OAI.Generator.Tracial.approximationStarOrder
theorem approximant_error_nonneg (n : ℕ) :
    0 ≤ I.proj.val*x*I.proj.val-I.approximant hx n := by
  rw [I.approximant_error_sum hx]
  exact Finset.sum_nonneg (fun i _ => (I.level hx n i).lower)

theorem approximant_error_upper (n : ℕ) :
    I.proj.val*x*I.proj.val-I.approximant hx n ≤
      (((I.hi-I.lo)/(2:ℝ)^n : ℝ) : ℂ) • I.proj.val := by
  rw [I.approximant_error_sum hx]
  have he := Finset.sum_le_sum (s := (Finset.univ : Finset (DyadicIndex n)))
    (fun i _ => (I.level hx n i).error_upper)
  simp only [I.level_width hx] at he
  rw [← Finset.smul_sum,I.level_total hx] at he
  exact he

/-- Actual operator norm approximation, not an assumed energy budget. -/
theorem approximant_norm_error (n : ℕ) (hab : I.lo ≤ I.hi) :
    ‖I.proj.val*x*I.proj.val-I.approximant hx n‖ ≤ (I.hi-I.lo)/(2:ℝ)^n := by
  have hw : 0 ≤ (I.hi-I.lo)/(2:ℝ)^n := div_nonneg (sub_nonneg.mpr hab) (by positivity)
  calc ‖I.proj.val*x*I.proj.val-I.approximant hx n‖ ≤
      ‖(((I.hi-I.lo)/(2:ℝ)^n : ℝ) : ℂ) • I.proj.val‖ :=
        CStarAlgebra.norm_le_norm_of_le_of_nonneg (I.approximant_error_upper hx n)
          (I.approximant_error_nonneg hx n)
    _ = ((I.hi-I.lo)/(2:ℝ)^n)*‖I.proj.val‖ := by
      rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg hw]
    _ ≤ (I.hi-I.lo)/(2:ℝ)^n := by
      nlinarith only [mul_le_mul_of_nonneg_left I.proj.property.norm_le hw]

theorem exists_approximant (hab : I.lo ≤ I.hi) (ε : ℝ) (hε : 0 < ε) :
    ∃ n, ‖I.proj.val*x*I.proj.val-I.approximant hx n‖ < ε := by
  obtain ⟨n,hn⟩ := exists_nat_gt ((I.hi-I.lo)/ε)
  have hnp : (n : ℝ)<(2:ℝ)^n := by exact_mod_cast (show n < 2^n from Nat.lt_two_pow_self)
  have hbound : (I.hi-I.lo)/(2:ℝ)^n < ε := by
    rw [div_lt_iff₀ (by positivity : (0:ℝ)<2^n)]
    have hh := (div_lt_iff₀ hε).mp hn
    nlinarith [mul_lt_mul_of_pos_left hnp hε]
  exact ⟨n,(I.approximant_norm_error hx n hab).trans_lt hbound⟩

end SpectralInterval

end

/-! Constructed cuts preserve commutation with other operators. -/
section
open scoped CStarAlgebra
open UltrapowerBridge ContinuousLinearMap LinearMap
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem kernelProjection_commutes (x y : M.toStarSubalgebra)
    (hxy : Commute x y) (hxys : Commute x (star y)) :
    Commute (kernelProjection x).val y := by
  let k := x.val.ker.starProjection
  have hk : IsIdempotentElem k.toLinearMap :=
    (isStarProjection_starProjection (U := x.val.ker)).isIdempotentElem.toLinearMap
  have h₁ := kernel_invariant_of_commutes x.val y.val (congrArg Subtype.val hxy.eq)
  have h₂ : x.val.ker ∈ Module.End.invtSubmodule y.val.adjoint.toLinearMap := by
    exact kernel_invariant_of_commutes x.val (star y).val (congrArg Subtype.val hxys.eq)
  have hc : Commute k.toLinearMap y.val.toLinearMap := by
    apply (LinearMap.IsIdempotentElem.commute_iff hk).mpr
    change k.range ∈ Module.End.invtSubmodule y.val.toLinearMap ∧
      k.ker ∈ Module.End.invtSubmodule y.val.toLinearMap
    rw [Submodule.range_starProjection,Submodule.ker_starProjection]
    exact ⟨h₁,ContinuousLinearMap.orthogonal_mem_invtSubmodule h₂⟩
  apply Subtype.ext
  ext ξ
  exact congrArg (fun t : H →ₗ[ℂ] H => t ξ) hc.eq

attribute [local instance] OAI.Generator.Tracial.spectralCommutationCStar
attribute [local instance] OAI.Generator.Tracial.spectralCommutationOrder
attribute [local instance] OAI.Generator.Tracial.spectralCommutationStarOrder
theorem positiveSupport_commutes_of_commutes (x y : M.toStarSubalgebra)
    (hxy : Commute x y) (hxys : Commute x (star y)) :
    Commute (positiveSupport x).val y := by
  have hpos := hxy.cfcₙ_real (fun t : ℝ => t⁺)
  have hposs := hxys.cfcₙ_real (fun t : ℝ => t⁺)
  change Commute x⁺ y at hpos
  change Commute x⁺ (star y) at hposs
  have hs : IsSelfAdjoint x⁺ := (CFC.posPart_nonneg x).isSelfAdjoint
  have hk := kernelProjection_commutes x⁺ y hpos hposs
  change Commute (1-(kernelProjection (star x⁺)).val) y
  rw [hs.star_eq]
  exact (Commute.one_left y).sub_left hk

end

/-! Spectral interval partitions in the commutant of a prescribed operator. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem positiveSupport_commutes_of_selfAdjoint {x y : M.toStarSubalgebra}
    (hx : IsSelfAdjoint x) (hxy : Commute x y) :
    Commute (positiveSupport x).val y :=
  positiveSupport_commutes_of_commutes x y hxy (selfAdjoint_commutes_star_right hx hxy)

theorem cornerSpectralCut_commutes_with (p : AlgebraProjection M) (x y : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) (hxy : Commute x y) (hp : Commute p.val y) (t : ℝ) :
    Commute (cornerSpectralCut p x t).val y := by
  apply positiveSupport_commutes_of_selfAdjoint (cornerSpectralShift_selfAdjoint p x hx t)
  have hscalar : Commute ((t : ℂ) • p.val) y := by
    show ((t : ℂ) • p.val)*y=y*((t : ℂ) • p.val)
    rw [smul_mul_assoc,mul_smul_comm,hp.eq]
  exact ((hp.mul_left hxy).mul_left hp).sub_left hscalar

namespace SpectralInterval
variable {x y : M.toStarSubalgebra} (I : SpectralInterval x) (hx : IsSelfAdjoint x)

theorem child_commutes (hxy : Commute x y) (hp : Commute I.proj.val y) (b : Bool) :
    Commute (I.child hx b).proj.val y := by
  have hq := cornerSpectralCut_commutes_with I.proj x y hx hxy hp I.midpoint
  cases b
  · exact hp.sub_left hq
  · exact hq

theorem level_commutes (hxy : Commute x y) (hp : Commute I.proj.val y) :
    ∀ n i, Commute (I.level hx n i).proj.val y
  | 0,_ => hp
  | n+1,i => (I.level hx n i.1).child_commutes hx hxy (level_commutes hxy hp n i.1) i.2

theorem partition_commutes (hxy : Commute x y) (hp : Commute I.proj.val y)
    (n : ℕ) (i : Fin (I.partition hx n).size) :
    Commute ((I.partition hx n).piece i).val y :=
  I.level_commutes hx hxy hp n _

end SpectralInterval

/-- One constructed partition preserves the whole displayed commutant,
not a separately selected partition for each test operator. -/
theorem exists_finite_spectral_approximation_preserving_commutant (p : AlgebraProjection M)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (ε : ℝ) (hε : 0 < ε) :
    ∃ (Q : CornerPartition p) (c : Fin Q.size → ℝ),
      Q.pinch x=p.val*x*p.val ∧
      (∀ y : M.toStarSubalgebra, Commute x y → Commute p.val y →
        ∀ i, Commute (Q.piece i).val y) ∧
      ‖p.val*x*p.val-∑ i, (c i : ℂ) • (Q.piece i).val‖ < ε := by
  let I := initialSpectralInterval p x hx
  have hI : I.lo ≤ I.hi := neg_le_self (norm_nonneg _)
  obtain ⟨n,hn⟩ := I.exists_approximant hx hI ε hε
  let e := (Fintype.equivFin (DyadicIndex n)).symm
  refine ⟨I.partition hx n,fun i => (I.level hx n (e i)).lo,I.partition_pinch hx n,
    fun y hxy hp => I.partition_commutes hx hxy hp n,?_⟩
  have he := Equiv.sum_comp e (fun i => ((I.level hx n i).lo : ℂ) • (I.level hx n i).proj.val)
  change ‖p.val*x*p.val-∑ i, ((I.level hx n (e i)).lo : ℂ) •
    (I.level hx n (e i)).proj.val‖ < ε
  rw [he]
  exact hn

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_SpectralApproximation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Common finite refinements of two commuting corner partitions. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace CornerPartition
variable {p : AlgebraProjection M} (Q R : CornerPartition p)
variable (hc : ∀ i j, Commute (Q.piece i).val (R.piece j).val)

def joint : CornerPartition p := ofFamily (Q.jointPiece R hc)
  (Q.jointPiece_orthogonal R hc) (Q.jointPiece_total R hc)

end CornerPartition

/-! Simultaneous finite spectral approximation of two commuting self-adjoint
operators. The same actual partition is used for both. -/

end

/-! Finite spectral approximation for an actual normal operator. -/

/-! Transport constructed spectral partitions through an actual inclusion of
von Neumann algebras on the same Hilbert space. -/

/-! Finite simultaneous spectral approximation of any commuting self-adjoint
family, preserving a prior partition and the entire common commutant. -/

/-! Finite orthogonal families can be completed to unit partitions. Refining
blocks retains explicit disjoint index sets whose sums recover those blocks. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)
variable (R : (i : Fin Q.size) → CornerPartition (Q.piece i))

def blockIndices (i : Fin Q.size) : Finset (Fin (Q.refineBlocks R).size) :=
  Finset.univ.filter fun j =>
    ((Fintype.equivFin ((k : Fin Q.size) × Fin (R k).size)).symm j).1=i

end CornerPartition

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_LocalQuantization
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! An actual irreducible subalgebra and its constructed conditional
expectation give finite pinching partitions with energy arbitrarily close
to the expectation energy. No partition or expectation is supplied. -/
open scoped BigOperators

/-! Convert the source's decreasing irreducible chain into actual finite
pinching partitions. The chain and its irreducibility are explicit inputs;
its existence in an arbitrary factor is not asserted. -/
open scoped BigOperators

/-! Restrict a compatible unit partition to an actual corner, retaining
all pieces and the exact compression. -/
open scoped BigOperators

/-! Complete a corner partition by the complementary projection. This lets
the existing compatible refinement construction act on an actual p-corner. -/
open scoped BigOperators

/-! Transfer actual corner partitions along a concrete von Neumann
subalgebra inclusion, preserving pieces, pinching and tracial energy. -/
open scoped BigOperators
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

namespace CornerPartition
variable {p : AlgebraProjection N} (Q : CornerPartition p)

def mapInclusion (hNM : N ≤ M) : CornerPartition (includedProjection hNM p) where
  size := Q.size
  piece i := includedProjection hNM (Q.piece i)
  orthogonal i j hij := by
    change coordinateInclusion hNM (Q.piece i).val*coordinateInclusion hNM (Q.piece j).val=0
    rw [← map_mul,Q.orthogonal i j hij,map_zero]
  total := by
    change (∑ i,coordinateInclusion hNM (Q.piece i).val)=coordinateInclusion hNM p.val
    rw [← map_sum,Q.total]

/-- Unit partitions use the ambient identity, with no transport of the
underlying finite index set. -/
def includeUnit (Q : CornerPartition (identityProjection N)) (hNM : N ≤ M) :
    CornerPartition (identityProjection M) where
  size := Q.size
  piece := (Q.mapInclusion hNM).piece
  orthogonal := (Q.mapInclusion hNM).orthogonal
  total := (Q.mapInclusion hNM).total

end CornerPartition
end

/-! The two applications of orthogonal refinement in Popa A.1.2, equations
(2) and (3). The inner decreasing chain need only be irreducible in N;
irreducibility of its terms in the ambient M is not imposed. -/
open scoped BigOperators

/-! Nonzero local projections obtained from the constructed nested-chain
partition. This implements the finite squared-energy selection at the end
of A.1.2, while retaining the chain as a structural premise. -/
open scoped BigOperators

/-! Local quantization by finite matrix approximation and Bell pinching under represented trace-vector separability. -/
open scoped BigOperators
open UltrapowerBridge FiniteMatrixStage

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

/-! An actual positive normalized vector functional with arbitrarily small
multiplicative failure of cyclicity on a nonzero corner. No trace is assumed. -/
open scoped CStarAlgebra

/-! A full finite matrix partition can be rebased into every nonzero corner.
The legs are constructed partial isometries, not assumed matrix units. -/
open scoped BigOperators
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι : Type*} [Fintype ι]

theorem compose_base_target (E : EquivalentPartition p ι) (v : PartialIsometry M)
    (hv : v.target=E.base) (i : ι) :
    ((E.leg i).compose v (by rw [hv,E.initial])).target=(E.leg i).target := by
  apply Subtype.ext
  rw [PartialIsometry.compose_target,hv,← E.initial i,(E.leg i).mul_support]
  rfl

/-- Change the common initial corner by a displayed equivalence. -/
def rebase (E : EquivalentPartition p ι) (v : PartialIsometry M) (hv : v.target=E.base) :
    EquivalentPartition p ι where
  base := v.support
  leg i := (E.leg i).compose v (by rw [hv,E.initial])
  initial _ := rfl
  cross i j hij := by
    change star ((E.leg i).val*v.val)*((E.leg j).val*v.val)=0
    calc _ = star v.val*(star (E.leg i).val*(E.leg j).val)*v.val := by
           simp only [star_mul,mul_assoc]
         _ = 0 := by rw [E.cross i j hij,mul_zero,zero_mul]
  total := by simpa only [E.compose_base_target v hv] using E.total
  bound i := by rw [E.compose_base_target v hv]; exact E.bound i

end EquivalentPartition

end

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
-- module Solutions.OAIQ11_FG.FactorGeneration_PartialUnitaries
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Popa's extension order on actual supported partial unitaries, and its
exact L2 distance identity. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace PartialUnitary

def Extends (v w : PartialUnitary M) : Prop := w.val*v.support.val=v.val

end PartialUnitary

end

/-! Actual L2 limits of partial unitaries and upper bounds of increasing
sequences, using their exact support-trace distance. -/

/-! Actual orthogonal corner unitaries from dyadic trace cuts. These supply
weakly vanishing scalar matrix coefficients for the scalar-commutant case
of Popa's coordinate nonintertwining criterion. -/

/-! Popa 1308.3982v3, §1.5, scalar-target specialization. The sequence is
constructed from actual dyadic trace cuts in each nonzero corner; neither
nonintertwining nor Haar existence is an assumption. -/
open Filter
open scoped Topology
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end


