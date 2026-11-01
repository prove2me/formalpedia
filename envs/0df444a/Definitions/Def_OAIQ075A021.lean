-- Prove2me | Definitions.Def_OAIQ075A021
-- name    : OAIQ075A021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T08:16:23.678432+00:00
-- url     : https://prove2.me/theorems/d38dfa9d-7768-4be2-bd3f-7b23519fbaab
-- title:
--   Definitions bundle OAIQ075A021 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 49 declarations of OpenAI's Lean: 11 definitions and 38 theorems. The definitions and types are `OAI.Generator.Tracial.SpectralInterval.approximant`, `OAI.Generator.Tracial.SpectralInterval.child`, `OAI.Generator.Tracial.SpectralInterval.high`, `OAI.Generator.Tracial.SpectralInterval.level`, `OAI.Generator.Tracial.SpectralInterval.low`, `OAI.Generator.Tracial.SpectralInterval.lowProjection`, `OAI.Generator.Tracial.SpectralInterval.partition`, `OAI.Generator.Tracial.cornerSpectralPartition`, `OAI.Generator.Tracial.initialSpectralInterval`, `OAI.HochschildPatching.integerEval`, `OAI.HochschildPatching.splitFactor`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`BoundedHochschild_AlternatingMoments`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoundedHochschild/AlternatingMoments.lean), [`BoundedHochschild_MixedWords`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoundedHochschild/MixedWords.lean), [`BoundedHochschild_UltrapowerMoments`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoundedHochschild/UltrapowerMoments.lean), [`FactorGeneration_OrbitMinima`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/OrbitMinima.lean), [`FactorGeneration_ProjectionComparison`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/ProjectionComparison.lean), [`FactorGeneration_SpectralPinching`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/SpectralPinching.lean), [`FactorGeneration_Supports`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/Supports.lean), [`FactorGeneration_TraceTopology`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/TraceTopology.lean).
--
--   **Imports.** It imports the bundles `OAIQ075A013`, `OAIQ075A014`, `OAIQ075A015` and `OAIQ075A016` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ075A026`, `OAIQ075A027` and `OAIQ075A028`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ075A013
import Definitions.Def_OAIQ075A014
import Definitions.Def_OAIQ075A015
import Definitions.Def_OAIQ075A016

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





open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison

variable {M : Type*} [CStarAlgebra M]
variable {I : Type*} (F : I → M)
def splitFactor {K : ℕ} (v w : PartialUnitary M) (a : WordAtom I K) : M × M :=
  (atomPower v a*wordCoeff F a.2,atomPower w a*wordCoeff F a.2)
end HochschildPatching

 

 

open Filter Topology
open scoped ComplexOrder





open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_UltrapowerMoments
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered sequences and unitary moments in tracial ultrapowers. -/

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
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder
open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction





open scoped ComplexOrder BoundedContinuousFunction
namespace HochschildPatching
open HochschildComparison
variable {M A : Type*} [CStarAlgebra M] [CStarAlgebra A]
variable {I : Type*} {K : ℕ}

lemma wordCoeff_hom (φ : M →⋆ₐ[ℂ] A) (F : I → M) (a : Option I) :
    φ (wordCoeff F a)=wordCoeff (φ ∘ F) a := by cases a <;> simp [wordCoeff]
end HochschildPatching

 

 

open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction





open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_AlternatingMoments
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer powers, alternating words and graded free moments. -/

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
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder
namespace HochschildPatching
variable {I : Type*} {M : Type*} [CStarAlgebra M]

def integerEval (F : I → M) (u : unitary M) (a : Option I) (l : List (IntAtom I)) : M :=
  wordCoeff F a * (l.map (fun b => ((u^b.1 : unitary M):M)*wordCoeff F b.2)).prod

end HochschildPatching





end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_TraceTopology
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- The trace image of an operator-norm ball is norm closed in H. -/
theorem trace_ball_isClosed (C : ℝ) :
    IsClosed {ξ : H | ∃ b : M.toStarSubalgebra, ‖b‖ ≤ C ∧
      (b : H →L[ℂ] H) τ.vector = ξ} := by
  apply IsSeqClosed.isClosed
  intro ξ z hz hlim
  choose a ha he using hz
  have hC : 0 ≤ C := (norm_nonneg (a 0)).trans (ha 0)
  apply bounded_trace_limit τ a C hC ha z
  simpa only [he] using hlim

/-- Every point of the actual closed convex hull has an algebra representative
with the same operator norm bound. -/
theorem bounded_representative_of_closed_convexHull (s : Set H) (C : ℝ)
    (hs : ∀ ξ ∈ s, ∃ b : M.toStarSubalgebra, ‖b‖ ≤ C ∧
      (b : H →L[ℂ] H) τ.vector = ξ)
    {ξ : H} (hξ : ξ ∈ closure (convexHull ℝ s)) :
    ∃ b : M.toStarSubalgebra, ‖b‖ ≤ C ∧ (b : H →L[ℂ] H) τ.vector = ξ := by
  exact (closure_minimal (convexHull_min hs (trace_ball_convex τ C))
    (trace_ball_isClosed τ C)) hξ

/-! The actual closed convex unitary orbit in the coordinate trace Hilbert
space, with bounded representatives and conjugation invariance. -/

end

/-! The least-norm point of the actual orbit hull is represented in M and
fixed by every conjugating unitary; its trace and distance bounds are retained. -/
open scoped Topology
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_OrbitMinima
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The least-norm unitary-orbit point is scalar when the coordinate inclusion has scalar commutant. -/

/-! Irreducibility excludes disconnected nonzero ambient projections.
This gives the projection part of irreducibility in every nonzero corner. -/
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (P : StarSubalgebra ℂ M.toStarSubalgebra) [CompleteSpace P]
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : P, (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
  ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))

theorem baseVector_inner_eq_trace (a b : M.toStarSubalgebra) :
    inner ℂ (baseVector τ a) (baseVector τ b)=τ.trace (star a*b) := by
  change _ = inner ℂ τ.vector (star (a : H →L[ℂ] H) ((b : H →L[ℂ] H) τ.vector))
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  rfl

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Supports
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

attribute [local instance] OAI.Generator.Tracial.positiveSupportCStar
attribute [local instance] OAI.Generator.Tracial.positiveSupportOrder
local instance positiveSupportPreorder_r1c9d58_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance positiveSupportLE_r1c9d58_1 : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
attribute [local instance] OAI.Generator.Tracial.positiveSupportStarOrder
theorem positiveSupport_commutes (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    Commute (positiveSupport x).val x := by
  show (positiveSupport x).val*x=x*(positiveSupport x).val
  rw [positiveSupport_mul x hx,mul_positiveSupport x hx]

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
-- module Solutions.OAIQ075_KS.FactorGeneration_ProjectionComparison
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A nonzero coefficient linking two projections produces an actual nonzero
partial isometry between subprojections. Scalar center supplies such coefficients. -/

/-! Projection comparison and equal-trace equivalence in the actual factor.
Both polar decomposition and the maximal partial isometry are constructed. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))

theorem projection_eq_of_le_of_trace_eq {p q : AlgebraProjection M}
    (hpq : p ≤ q) (ht : τ.trace p.val=τ.trace q.val) : p=q := by
  let r : AlgebraProjection M := ⟨q.val-p.val,p.property.sub_of_mul_eq_right q.property hpq⟩
  have hz : τ.trace r.val=0 := by
    change τ.trace (q.val-p.val)=0
    rw [trace_sub,ht,sub_self]
  have hr : r.val=0 := by
    by_contra hn
    have hh := projection_trace_pos τ r.val r.property hn
    rw [hz,Complex.zero_re] at hh
    exact (lt_irrefl _ hh)
  exact Subtype.ext (sub_eq_zero.mp hr).symm

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_SpectralPinching
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual sign splitting inside a prescribed residual corner. -/
section
open scoped CStarAlgebra BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- The finite corner partition constructed from the shifted positive part. -/
def cornerSpectralPartition (p : AlgebraProjection M) (x : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) (t : ℝ) : CornerPartition p :=
  CornerPartition.binary p (cornerSpectralCut p x t) (cornerSpectralCut_le p x hx t)

attribute [local instance] OAI.Generator.Tracial.cornerCutCStar
attribute [local instance] OAI.Generator.Tracial.cornerCutOrder
attribute [local instance] OAI.Generator.Tracial.cornerCutPreorder
attribute [local instance] OAI.Generator.Tracial.cornerCutLE
attribute [local instance] OAI.Generator.Tracial.cornerCutStarOrder
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

local instance intervalCStar_r1c9d58_1 : CStarAlgebra M.toStarSubalgebra := {}
attribute [local instance] OAI.Generator.Tracial.intervalOrder
attribute [local instance] OAI.Generator.Tracial.intervalPreorder
attribute [local instance] OAI.Generator.Tracial.intervalLE
attribute [local instance] OAI.Generator.Tracial.intervalStarOrder
theorem lower_bound_compress {p q : AlgebraProjection M} (hqp : q ≤ p)
    (x : M.toStarSubalgebra) (t : ℝ)
    (h : 0 ≤ p.val*x*p.val-(t : ℂ) • p.val) :
    0 ≤ q.val*x*q.val-(t : ℂ) • q.val := by
  have hh := star_left_conjugate_nonneg h q.val
  rw [q.property.isSelfAdjoint.star_eq,compress_scalar_shift hqp] at hh
  exact hh

theorem upper_bound_compress {p q : AlgebraProjection M} (hqp : q ≤ p)
    (x : M.toStarSubalgebra) (t : ℝ)
    (h : p.val*x*p.val-(t : ℂ) • p.val ≤ 0) :
    q.val*x*q.val-(t : ℂ) • q.val ≤ 0 := by
  have hh := star_left_conjugate_nonneg (neg_nonneg.mpr h) q.val
  rw [q.property.isSelfAdjoint.star_eq,mul_neg,neg_mul,compress_scalar_shift hqp] at hh
  exact neg_nonneg.mp hh

namespace SpectralInterval
variable {x : M.toStarSubalgebra} (I : SpectralInterval x) (hx : IsSelfAdjoint x)

def lowProjection : AlgebraProjection M :=
  ⟨I.proj.val-(I.highProjection).val,
    (I.highProjection).property.sub_of_mul_eq_right I.proj.property
      (cornerSpectralCut_le I.proj x hx I.midpoint)⟩

theorem low_le : I.lowProjection hx ≤ I.proj := by
  change I.proj.val*(I.proj.val-(I.highProjection).val)=I.proj.val-I.highProjection.val
  rw [mul_sub,I.proj.property.isIdempotentElem.eq,I.high_le hx]

local instance intervalCStar_r1c9d58_2 : CStarAlgebra M.toStarSubalgebra := {}
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

attribute [local instance] OAI.Generator.Tracial.approximationCStar
attribute [local instance] OAI.Generator.Tracial.approximationOrder
attribute [local instance] OAI.Generator.Tracial.approximationPreorder
attribute [local instance] OAI.Generator.Tracial.approximationLE
attribute [local instance] OAI.Generator.Tracial.approximationStarOrder
theorem error_upper : I.proj.val*x*I.proj.val-(I.lo : ℂ) • I.proj.val ≤
    ((I.hi-I.lo : ℝ) : ℂ) • I.proj.val := by
  calc I.proj.val*x*I.proj.val-(I.lo : ℂ) • I.proj.val ≤
      (I.hi : ℂ) • I.proj.val-(I.lo : ℂ) • I.proj.val :=
        sub_le_sub_right (sub_nonpos.mp I.upper) _
    _ = _ := by rw [← sub_smul,Complex.ofReal_sub]

def approximant (n : ℕ) : M.toStarSubalgebra :=
  ∑ i : DyadicIndex n, ((I.level hx n i).lo : ℂ) • (I.level hx n i).proj.val

theorem approximant_error_sum (n : ℕ) :
    I.proj.val*x*I.proj.val-I.approximant hx n =
      ∑ i : DyadicIndex n, ((I.level hx n i).proj.val*x*(I.level hx n i).proj.val-
        ((I.level hx n i).lo : ℂ) • (I.level hx n i).proj.val) := by
  rw [Finset.sum_sub_distrib,I.level_compression_total hx]
  rfl

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

attribute [local instance] OAI.Generator.Tracial.approximationCStar
attribute [local instance] OAI.Generator.Tracial.approximationOrder
attribute [local instance] OAI.Generator.Tracial.approximationPreorder
attribute [local instance] OAI.Generator.Tracial.approximationLE
attribute [local instance] OAI.Generator.Tracial.approximationStarOrder
/-- Start the construction with the actual operator norm bounds in any corner. -/
def initialSpectralInterval (p : AlgebraProjection M) (x : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) : SpectralInterval x := by
  let oneP : AlgebraProjection M := ⟨1,IsStarProjection.one _⟩
  have hp : p ≤ oneP := one_mul _
  have hs (r : ℝ) : algebraMap ℝ M.toStarSubalgebra r=(r : ℂ) • (1 : M.toStarSubalgebra) := by
    rw [Algebra.algebraMap_eq_smul_one,Complex.coe_smul]
  refine ⟨p,-‖x‖,‖x‖,?_,?_⟩
  · apply lower_bound_compress hp x (-‖x‖)
    have h := hx.neg_algebraMap_norm_le_self
    rw [hs] at h
    change 0 ≤ 1*x*1-((-‖x‖ : ℝ) : ℂ) • (1 : M.toStarSubalgebra)
    simpa only [one_mul,mul_one,Complex.ofReal_neg,neg_smul] using sub_nonneg.mpr h
  · apply upper_bound_compress hp x ‖x‖
    have h := hx.le_algebraMap_norm_self
    rw [hs] at h
    change 1*x*1-(‖x‖ : ℂ) • (1 : M.toStarSubalgebra) ≤ 0
    simpa only [one_mul,mul_one] using sub_nonpos.mpr h

end

/-! Constructed cuts preserve commutation with other operators. -/
section
open scoped CStarAlgebra
open UltrapowerBridge ContinuousLinearMap LinearMap
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

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

end Generator.Tracial

end

end OAI
end


