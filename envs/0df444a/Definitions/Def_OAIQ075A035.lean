-- Prove2me | Definitions.Def_OAIQ075A035
-- name    : OAIQ075A035
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T08:56:46.429535+00:00
-- url     : https://prove2.me/theorems/96d3c982-70c1-4295-8e93-d291978f3218
-- title:
--   Definitions bundle OAIQ075A035 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 18 declarations of OpenAI's Lean: 18 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`BoundedHochschild_MixedWords`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoundedHochschild/MixedWords.lean), [`BoundedHochschild_UltrapowerMoments`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoundedHochschild/UltrapowerMoments.lean), [`FactorGeneration_MatrixRefinement`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/MatrixRefinement.lean), [`FactorGeneration_MatrixSequence`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/MatrixSequence.lean), [`FactorGeneration_OrbitMinima`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/OrbitMinima.lean), [`FactorGeneration_Subfactors`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/Subfactors.lean), [`KadisonSimilarity_Representation_CountableAmplification`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Representation/CountableAmplification.lean), [`KadisonSimilarity_Tracial_QuotientMomentLimit`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/QuotientMomentLimit.lean).
--
--   **Imports.** It imports the bundles `OAIQ075A031` and `OAIQ075A032` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ075A038`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ075A031
import Definitions.Def_OAIQ075A032

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_MixedWords
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

variable [PartialOrder M] [StarOrderedRing M]
variable (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))

include htr in
lemma momentBound_limit {K N : ℕ} {b : ℝ → ℝ} {v : ℕ → PartialUnitary M} {w : PartialUnitary M}
    (h1 : τ 1=1) (h : GNSTendsto τ (fun i => (v i : M)) atTop (w : M))
    (hb : ContinuousAt b ((τ w.support).re))
    (hv : ∀ i, MomentBound F τ (K := K) (N := N) b (v i)) :
    MomentBound F τ (K := K) (N := N) b w := by
  intro a ha
  have he := trace_tendsto_of_gns τ h1 (mixedEval_tendsto F τ htr h a.1 a.2.val)
  have hs := (h.star τ htr).mul τ htr h 1 (fun i => by simpa only [norm_star] using (v i).norm_le_one)
  have hst := (Complex.continuous_re.tendsto _).comp (trace_tendsto_of_gns τ h1 hs)
  exact le_of_tendsto_of_tendsto he.norm (hb.tendsto.comp hst) (Filter.Eventually.of_forall (fun i => hv i a ha))
end HochschildPatching

 

 

open scoped ComplexOrder





open Filter Topology
open scoped ComplexOrder





open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_UltrapowerMoments
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

lemma mixedEval_sequence (F : I → (ℕ →ᵇ M)) (u : ℕ → unitary M)
    (a : Option I) (l : List (WordAtom I K)) (n : ℕ) :
    mixedEval F (asPartialUnitary (HochschildUltrapower.unitarySequence u)) a l n=
      mixedEval (fun i => F i n) (asPartialUnitary (u n)) a l := by
  have hh := mixedEval_hom (evalSequence n) F (HochschildUltrapower.unitarySequence u) a l
  rw [eval_unitarySequence] at hh
  exact hh
end HochschildPatching

 

 

open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction





open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_OrbitMinima
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

include τ hirr in
/-- Every projection commuting with pPp inside pMp is either zero or p. -/
theorem corner_commutant_projection_trivial (p r : AlgebraProjection M)
    (hrp : r ≤ p)
    (hr : ∀ a : P, Commute r.val (p.val*(a : M.toStarSubalgebra)*p.val)) :
    r.val=0 ∨ r.val=p.val := by
  let s : AlgebraProjection M := ⟨p.val-r.val,r.property.sub_of_mul_eq_right p.property hrp⟩
  have hlink (a : P) : s.val*(a : M.toStarSubalgebra)*r.val=0 := by
    have hl : p.val*r.val=r.val := hrp
    have hright := projection_mul_of_le hrp
    have he := congrArg (fun z : M.toStarSubalgebra => z*r.val) (hr a).eq
    simp only [mul_assoc,hl,r.property.isIdempotentElem.eq] at he
    have he' : r.val*((p.val*(a : M.toStarSubalgebra))*r.val)=
        (p.val*(a : M.toStarSubalgebra))*r.val := by
      simpa only [mul_assoc,hl,r.property.isIdempotentElem.eq] using he
    have he'' : r.val*(a : M.toStarSubalgebra)*r.val=
        p.val*(a : M.toStarSubalgebra)*r.val := by
      simpa only [← mul_assoc,hright] using he'
    change (p.val-r.val)*(a : M.toStarSubalgebra)*r.val=0
    rw [sub_mul,sub_mul,he'',sub_self]
  rcases projection_eq_zero_or_eq_zero_of_no_links τ P hirr r s hlink with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h).symm

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Subfactors
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The actual von Neumann algebra of operators in N commuting with a finite
projection partition. Its double-commutant identity and completeness are
proved, so spectral approximation can be performed inside this algebra. -/

/-! Irreducibility passes to actual corners. Spectral approximation reduces
self-adjoint corner commutants to their projections; no corner-factor or
normalized-trace existence statement is assumed. -/

/-! The relative commutant of a finite block algebra consists of scalars on
each block. This statement is proved from coordinate irreducibility. -/

/-! Orthogonality to the prescribed subalgebra is stronger than global
centering. It is preserved by compressions and conjugations from that
subalgebra and removes every block scalar term exactly. -/

/-! A corner whose only projections are zero and its unit is scalar.
The proof constructs spectral approximations; minimality is not a scalar-corner axiom. -/

/-! Diffuseness descends to an irreducible von Neumann subalgebra of a
diffuse finite tracial algebra. Finiteness follows from the actual faithful trace. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P M : VonNeumannAlgebra H}

theorem irreducible_subalgebra_diffuse (τ : TracialRepresentation M) (hPM : P ≤ M)
    (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : P.toStarSubalgebra,coordinateInclusion hPM a*c=c*coordinateInclusion hPM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (p : P.toStarSubalgebra) (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : P.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q := by
  classical
  by_contra hn
  let pP : AlgebraProjection P := ⟨p,hp⟩
  have hmin : ∀ q : AlgebraProjection P,q ≤ pP → q.val=0 ∨ q.val=p := by
    intro q hq
    by_cases hq0 : q.val=0
    · exact Or.inl hq0
    by_cases hqp : q.val=p
    · exact Or.inr hqp
    exact False.elim (hn ⟨q.val,q.property,hq0,hqp,hq,projection_mul_of_le hq⟩)
  let pM := includedProjection hPM pP
  have hpM0 : pM.val ≠ 0 := by
    intro h
    apply hp0
    exact Subtype.ext (congrArg (fun b : M.toStarSubalgebra => b.val) h)
  obtain ⟨q,hq,hq0,hqp,hpq,hqp'⟩ := hdiff pM.val pM.property hpM0
  let Q : StarSubalgebra ℂ M.toStarSubalgebra := insideAlgebra (M := M) (P := P)
  have hirrQ : ∀ c : M.toStarSubalgebra,
      (∀ a : Q,(a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra) := by
    intro c hc
    exact hirr c (fun a => hc ⟨coordinateInclusion hPM a,a.property⟩)
  have hcomm : ∀ a : Q,Commute q (pM.val*(a : M.toStarSubalgebra)*pM.val) := by
    intro a
    let aP : P.toStarSubalgebra := ⟨a.val.val,a.property⟩
    obtain ⟨z,hz⟩ := corner_scalar_of_projections pP hmin (p*aP*p)
      (by change p*(p*aP*p)=p*aP*p; simp only [← mul_assoc,hp.isIdempotentElem.eq])
      (by change (p*aP*p)*p=p*aP*p; simp only [mul_assoc,hp.isIdempotentElem.eq])
    have he : pM.val*(a : M.toStarSubalgebra)*pM.val=z • pM.val := by
      exact Subtype.ext (congrArg (fun b : P.toStarSubalgebra => b.val) hz)
    rw [he]
    show q*(z • pM.val)=(z • pM.val)*q
    rw [mul_smul_comm,smul_mul_assoc,hqp',hpq]
  exact (corner_commutant_projection_trivial τ Q hirrQ pM ⟨q,hq⟩ hpq hcomm).elim hq0 hqp

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_MatrixRefinement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! A normal element of a diffuse finite factor has L2 approximations in
constructed full dyadic matrix algebras. No prescribed MASA is needed. -/
namespace Tracial
open scoped BigOperators

/-! A constructed full matrix algebra reduces the actual relative-commutant
expectation energy by a uniform factor for a centered nonzero element. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N D M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem expectation_energy_descent_of_unitary_approximation (hDM : D ≤ M)
    (u : unitary M.toStarSubalgebra) (v x : M.toStarSubalgebra)
    (hd : τ.norm₂ x ≤ τ.norm₂ (conjugateLinear u x-x))
    (hclose : τ.norm₂ ((u : M.toStarSubalgebra)-v) <
      τ.norm₂ x/(4*(‖x‖+1)))
    (hc : ∀ z : M.toStarSubalgebra,z.val ∈ D → v*z=z*v) :
    τ.norm₂ (conditionalExpectation τ hDM x)^2 ≤ (15/16 : ℝ)*τ.norm₂ x^2 := by
  let z := conditionalExpectation τ hDM x
  have hcomm := commutator_norm₂_approximation τ (u : M.toStarSubalgebra) v x z
    (hc z (conditionalExpectation_mem τ hDM x))
  have hdisp := displacement_le_commutator τ u x
  have hu := unitary_norm_le (u : M.toStarSubalgebra) u.property.1
  have hz := conditionalExpectation_norm_le τ hDM x
  have hn : 0 ≤ τ.norm₂ (x-z) := norm_nonneg _
  have hδ : 0 ≤ τ.norm₂ ((u : M.toStarSubalgebra)-v) := norm_nonneg _
  have hsmall : 4*(‖x‖+1)*τ.norm₂ ((u : M.toStarSubalgebra)-v) < τ.norm₂ x := by
    have h := (lt_div_iff₀ (by positivity : 0 < 4*(‖x‖+1))).mp hclose
    nlinarith
  have hr : τ.norm₂ x/4 ≤ τ.norm₂ (x-z) := by
    have h₁ := mul_le_mul_of_nonneg_right hu hn
    have h₂ := mul_le_mul_of_nonneg_right hz hδ
    nlinarith
  have hpy := conditionalExpectation_pythagoras τ hDM x
  change τ.norm₂ z^2+τ.norm₂ (x-z)^2=τ.norm₂ x^2 at hpy
  nlinarith [sq_nonneg (τ.norm₂ (x-z)-τ.norm₂ x/4),
    show 0 ≤ τ.norm₂ x from norm_nonneg _]

theorem exists_irreducible_matrix_energy_descent (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (x : M.toStarSubalgebra) (hx : x ≠ 0) (ht : τ.trace x=0) :
    ∃ k n : ℕ,n=2^k ∧ ∃ E : MatrixUnitSystem (Fin n) N.toStarSubalgebra,
      τ.norm₂ (conditionalExpectation τ (E.map (coordinateInclusion hNM)).relativeVonNeumann_le x)^2 ≤
        (15/16 : ℝ)*τ.norm₂ x^2 := by
  let P := insideAlgebra (M := M) (P := N)
  obtain ⟨u,hu⟩ := exists_strict_centered_displacement τ P (by
    intro c hc
    exact hirr c (fun a => hc ⟨coordinateInclusion hNM a,a.property⟩)) x hx ht
  let a : N.toStarSubalgebra := ⟨(u.val : M.toStarSubalgebra).val,u.property⟩
  let : IsStarNormal a := ⟨by
    apply Subtype.ext
    exact congrArg (fun b : M.toStarSubalgebra => b.val)
      (u.val.property.1.trans u.val.property.2.symm)⟩
  have hxpos : 0 < τ.norm₂ x := lt_of_le_of_ne (norm_nonneg _)
    (fun h => hx ((τ.norm₂_eq_zero_iff x).mp h.symm))
  obtain ⟨k,n,hn,E,c,hc⟩ := exists_normal_matrix_approximation (restrictedTrace τ hNM)
    hfactor hdiff a (τ.norm₂ x/(4*(‖x‖+1))) (by positivity)
  let F := E.map (coordinateInclusion hNM)
  let v : M.toStarSubalgebra := ∑ j,c j • F.entry j j
  refine ⟨k,n,hn,E,expectation_energy_descent_of_unitary_approximation τ
    F.relativeVonNeumann_le u.val v x hu.le ?_ ?_⟩
  · change τ.norm₂ (coordinateInclusion hNM (a-∑ j,c j • E.entry j j)) < _ at hc
    rw [map_sub,map_sum] at hc
    simp only [map_smul] at hc
    exact hc
  · intro z hz
    have hz' := ((F.relativeStar_mem z.val).mp hz).2
    change (∑ j,c j • F.entry j j)*z=z*(∑ j,c j • F.entry j j)
    simp only [Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun b : M.toStarSubalgebra => c j • b) (Subtype.ext (hz' j j))

end Tracial

/-! Concrete commutants reverse matrix-algebra inclusion. Expectations are
compatible with restriction to an intermediate represented subalgebra. -/

/-! Quantitative energy descent retaining a prescribed finite matrix algebra
in an irreducible inclusion. All expectations and refinements are constructed. -/
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_compatible_matrix_energy_descent (τ : TracialRepresentation M) (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (E : MatrixUnitSystem ι N.toStarSubalgebra) (o : ι)
    (x : M.toStarSubalgebra) (ht : τ.trace x=0)
    (hy : conditionalExpectation τ (E.map (coordinateInclusion hNM)).relativeVonNeumann_le x ≠ 0) :
    ∃ k n : ℕ,n=2^k ∧ ∃ F : MatrixUnitSystem (Fin n) N.toStarSubalgebra,
      ∃ hc : ∀ i j l m,Commute (E.entry i j) (F.entry l m),
        E.algebra ≤ (E.product F hc).algebra ∧
        τ.norm₂ (conditionalExpectation τ
          ((E.product F hc).map (coordinateInclusion hNM)).relativeVonNeumann_le x)^2 ≤
          (15/16 : ℝ)*τ.norm₂
            (conditionalExpectation τ (E.map (coordinateInclusion hNM)).relativeVonNeumann_le x)^2 := by
  let EM := E.map (coordinateInclusion hNM)
  let C := EM.relativeVonNeumann
  let hCM := EM.relativeVonNeumann_le
  let y := conditionalExpectation τ hCM x
  let yC : C.toStarSubalgebra := ⟨y.val,conditionalExpectation_mem τ hCM x⟩
  let τC := restrictedTrace τ hCM
  have hyC : yC ≠ 0 := by
    intro h
    apply hy
    exact Subtype.ext (congrArg (fun b : C.toStarSubalgebra => b.val) h)
  have htC : τC.trace yC=0 := (conditionalExpectation_trace τ hCM x).trans ht
  obtain ⟨k,n,hn,G,hG⟩ := exists_irreducible_matrix_energy_descent τC
    (E.relative_inclusion hNM) (E.relative_scalar_center o hfactor)
    (E.relative_diffuse o hdiff) (E.relative_irreducible hNM o hirr) yC hyC htC
  let F := G.map (coordinateInclusion E.relativeVonNeumann_le)
  have hc : ∀ i j l m,Commute (E.entry i j) (F.entry l m) := by
    intro i j l m
    apply Subtype.ext
    exact ((E.relativeStar_mem (G.entry l m).val).mp (G.entry l m).property).2 i j
  let GM := G.map (coordinateInclusion (E.relative_inclusion hNM))
  have hcM : ∀ i j l m,Commute (EM.entry i j)
      ((GM.map (coordinateInclusion hCM)).entry l m) := by
    intro i j l m
    apply Subtype.ext
    exact congrArg (fun b : N.toStarSubalgebra => b.val) (hc i j l m).eq
  have hproduct : ((E.product F hc).map (coordinateInclusion hNM)).relativeVonNeumann =
      GM.relativeVonNeumann := by
    convert EM.relative_product_inside GM hcM using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  let hDC := GM.relativeVonNeumann_le
  have he : conditionalExpectation τ (hDC.trans hCM) x =
      coordinateInclusion hCM (conditionalExpectation τC hDC yC) := by
    rw [← conditionalExpectation_tower τ (hDC.trans hCM) hCM hDC x]
    exact conditionalExpectation_restricted τ hCM hDC yC
  refine ⟨k,n,hn,F,hc,E.algebra_le_product_left F hc,?_⟩
  have hnorm : τ.norm₂ (conditionalExpectation τ (hDC.trans hCM) x)^2 ≤
      (15/16 : ℝ)*τ.norm₂ y^2 := by
    rw [he]
    exact hG
  simpa only [hproduct] using hnorm

end Tracial

/-! Reindex full matrix units without changing their actual algebra or
relative commutant. This keeps iterated constructions indexed by Fin n. -/

/-! An actual full matrix algebra of any positive finite size can be
constructed in the relative commutant. No commuting matrix units are assumed. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_MatrixSequence
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_vector _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.concreteRademacher_square _root_.OAI.KadisonSimilarity.concreteRademacher_star _root_.OAI.KadisonSimilarity.concreteStageEquiv_apply _root_.OAI.KadisonSimilarity.concreteTraceLinear_apply _root_.OAI.KadisonSimilarity.concreteTraceLinear_one _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.generatedMatrixVector_apply _root_.OAI.KadisonSimilarity.generatedStageEmbedding_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

theorem exists_refinement_descent (E : FiniteMatrixStage N) (τ : TracialRepresentation M)
    (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (x : M.toStarSubalgebra) (ht : τ.trace x=0) :
    ∃ F : FiniteMatrixStage N,E.units.algebra ≤ F.units.algebra ∧
      F.energy τ hNM x ≤ (15/16 : ℝ)*E.energy τ hNM x := by
  by_cases hz : conditionalExpectation τ (E.commutant_le hNM) x=0
  · refine ⟨E,le_rfl,?_⟩
    simp [energy,hz]
  · obtain ⟨k,n,hn,F,hc,hEF,hdesc⟩ := exists_compatible_matrix_energy_descent τ hNM
      hfactor hdiff hirr E.units ⟨0,E.positive⟩ x ht hz
    let G := E.units.product F hc
    let e := (Fintype.equivFin (Fin E.size × Fin n)).symm
    let S : FiniteMatrixStage N := ⟨Fintype.card (Fin E.size × Fin n),by
      simp only [Fintype.card_prod,Fintype.card_fin]
      rw [hn]
      exact Nat.mul_pos E.positive (by positivity),G.reindex e⟩
    refine ⟨S,?_,?_⟩
    · change E.units.algebra ≤ (G.reindex e).algebra
      rw [G.reindex_algebra]
      exact hEF
    · change τ.norm₂ (conditionalExpectation τ
        ((G.reindex e).map (coordinateInclusion hNM)).relativeVonNeumann_le x)^2 ≤ _
      simp only [G.mapped_reindex_relative e (coordinateInclusion hNM)]
      exact hdesc

end FiniteMatrixStage

end

/-! Iterated compatible full matrix refinements attain every positive
finite-family commutant expectation budget. The reduction factor is proved. -/
namespace FiniteMatrixStage

section
open scoped BigOperators
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
include hfactor hdiff hirr

theorem exists_finite_family_descent {σ : Type*} (S : Finset σ)
    (x : σ → M.toStarSubalgebra) (ht : ∀ s ∈ S,τ.trace (x s)=0) (E : FiniteMatrixStage N) :
    ∃ F : FiniteMatrixStage N,E.units.algebra ≤ F.units.algebra ∧
      ∀ s ∈ S,F.energy τ hNM (x s) ≤ (15/16 : ℝ)*E.energy τ hNM (x s) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨E,le_rfl,by simp⟩
  | @insert s S hs ih =>
    obtain ⟨F,hEF,hF⟩ := ih (fun t ht' => ht t (Finset.mem_insert_of_mem ht'))
    obtain ⟨G,hFG,hG⟩ := F.exists_refinement_descent τ hNM hfactor hdiff hirr (x s)
      (ht s (Finset.mem_insert_self s S))
    refine ⟨G,hEF.trans hFG,?_⟩
    intro t ht'
    rcases Finset.mem_insert.mp ht' with rfl | ht'
    · exact hG.trans (mul_le_mul_of_nonneg_left (E.energy_antitone F τ hNM hEF _) (by norm_num))
    · exact (F.energy_antitone G τ hNM hFG _).trans (hF t ht')

theorem exists_iterated_energy_descent {σ : Type*} (S : Finset σ)
    (x : σ → M.toStarSubalgebra) (ht : ∀ s ∈ S,τ.trace (x s)=0)
    (E : FiniteMatrixStage N) (r : ℕ) :
    ∃ F : FiniteMatrixStage N,E.units.algebra ≤ F.units.algebra ∧
      ∀ s ∈ S,F.energy τ hNM (x s) ≤ (15/16 : ℝ)^r*E.energy τ hNM (x s) := by
  induction r with
  | zero => exact ⟨E,le_rfl,by simp⟩
  | succ r ih =>
    obtain ⟨F,hEF,hF⟩ := ih
    obtain ⟨G,hFG,hG⟩ := exists_finite_family_descent τ hNM hfactor hdiff hirr S x ht F
    refine ⟨G,hEF.trans hFG,?_⟩
    intro s hs
    calc G.energy τ hNM (x s) ≤ (15/16 : ℝ)*F.energy τ hNM (x s) := hG s hs
      _ ≤ (15/16 : ℝ)*((15/16 : ℝ)^r*E.energy τ hNM (x s)) :=
        mul_le_mul_of_nonneg_left (hF s hs) (by norm_num)
      _ = _ := by rw [pow_succ]; ring

theorem exists_finite_matrix_energy_budget {σ : Type*} (S : Finset σ)
    (x : σ → M.toStarSubalgebra) (ht : ∀ s ∈ S,τ.trace (x s)=0)
    (E : FiniteMatrixStage N) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : FiniteMatrixStage N,E.units.algebra ≤ F.units.algebra ∧
      (∑ s ∈ S,F.energy τ hNM (x s)) < ε := by
  let A := ∑ s ∈ S,E.energy τ hNM (x s)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun s _ => E.energy_nonneg τ hNM (x s))
  obtain ⟨r,hr⟩ := exists_pow_lt_of_lt_one
    (show 0 < ε/(A+1) from div_pos hε (by positivity)) (by norm_num : (15/16 : ℝ) < 1)
  obtain ⟨F,hEF,hF⟩ := exists_iterated_energy_descent τ hNM hfactor hdiff hirr S x ht E r
  refine ⟨F,hEF,?_⟩
  have hbound : (∑ s ∈ S,F.energy τ hNM (x s)) ≤ (15/16 : ℝ)^r*A := by
    calc (∑ s ∈ S,F.energy τ hNM (x s)) ≤
        ∑ s ∈ S,(15/16 : ℝ)^r*E.energy τ hNM (x s) :=
          Finset.sum_le_sum (fun s hs => hF s hs)
      _ = _ := (Finset.mul_sum S _ _).symm
  have hsmall := (lt_div_iff₀ (by positivity : 0 < A+1)).mp hr
  have hp : 0 ≤ (15/16 : ℝ)^r := by positivity
  nlinarith

end

/-! A single increasing sequence of full matrix algebras simultaneously
kills every member of a supplied countable centered family in commutant L2. -/
open Filter
open scoped BigOperators Topology
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem exists_countable_matrix_refinement (τ : TracialRepresentation M) (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (x : ℕ → M.toStarSubalgebra) (ht : ∀ s,τ.trace (x s)=0) (E : FiniteMatrixStage N) :
    ∃ A : ℕ → FiniteMatrixStage N,A 0=E ∧
      Monotone (fun n => (A n).units.algebra) ∧
      (∀ n,(∑ s ∈ Finset.range n,(A n).energy τ hNM (x s)) < (1/2 : ℝ)^n) ∧
      ∀ s,Tendsto (fun n => (A n).energy τ hNM (x s)) atTop (𝓝 0) := by
  have hex (n : ℕ) (F : FiniteMatrixStage N) := exists_finite_matrix_energy_budget τ hNM
    hfactor hdiff hirr (Finset.range (n+1)) x (fun s _ => ht s) F
    ((1/2 : ℝ)^(n+1)) (by positivity)
  let next (n : ℕ) (F : FiniteMatrixStage N) := (hex n F).choose
  let A : ℕ → FiniteMatrixStage N := fun n => Nat.rec E (fun n F => next n F) n
  have hstep (n : ℕ) : (A n).units.algebra ≤ (A (n+1)).units.algebra ∧
      (∑ s ∈ Finset.range (n+1),(A (n+1)).energy τ hNM (x s)) < (1/2 : ℝ)^(n+1) :=
    (hex n (A n)).choose_spec
  have hbudget (n : ℕ) :
      (∑ s ∈ Finset.range n,(A n).energy τ hNM (x s)) < (1/2 : ℝ)^n := by
    cases n with
    | zero => simp
    | succ n => exact (hstep n).2
  refine ⟨A,rfl,monotone_nat_of_le_succ (fun n => (hstep n).1),hbudget,?_⟩
  intro s
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => (A n).energy_nonneg τ hNM (x s)))
    ?_ (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num))
  filter_upwards [eventually_ge_atTop (s+1)] with n hn
  exact (Finset.single_le_sum (fun t _ => (A n).energy_nonneg τ hNM (x t))
    (Finset.mem_range.mpr (by omega))).trans (hbudget n).le

end FiniteMatrixStage

/-! L2 separability supplies a countable centered dense family. The constructed
matrix sequence has scalar common relative commutant in the ambient algebra. -/
section
open Filter
open scoped Topology
namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem scalar_common_commutant_of_dense_energy_decay (τ : TracialRepresentation M) (hNM : N ≤ M)
    (A : ℕ → FiniteMatrixStage N) (x : ℕ → M.toStarSubalgebra)
    (hdense : ∀ b : M.toStarSubalgebra,τ.trace b=0 → ∀ ε : ℝ,0 < ε →
      ∃ s,τ.norm₂ (b-x s) < ε)
    (hlim : ∀ s,Tendsto (fun n => (A n).energy τ hNM (x s)) atTop (𝓝 0))
    (c : M.toStarSubalgebra) (hc : ∀ n,c.val ∈ (A n).commutant hNM) :
    c=τ.trace c • (1 : M.toStarSubalgebra) := by
  let y := c-τ.trace c • (1 : M.toStarSubalgebra)
  have hyt : τ.trace y=0 := by
    dsimp [y]
    rw [trace_sub,cornerTrace_smul,τ.trace_one,mul_one,sub_self]
  have hym (n : ℕ) : y.val ∈ (A n).commutant hNM :=
    ((A n).commutant hNM).sub_mem (hc n)
      (((A n).commutant hNM).smul_mem ((A n).commutant hNM).one_mem _)
  suffices y=0 from sub_eq_zero.mp this
  by_contra hy
  have hp : 0 < τ.norm₂ y := lt_of_le_of_ne (norm_nonneg _)
    (fun h => hy ((τ.norm₂_eq_zero_iff y).mp h.symm))
  obtain ⟨s,hs⟩ := hdense y hyt (τ.norm₂ y/4) (by positivity)
  obtain ⟨n,hn⟩ := ((tendsto_order.mp (hlim s)).2 ((τ.norm₂ y/4)^2) (by positivity)).exists
  let hDM := (A n).commutant_le hNM
  let z := conditionalExpectation τ hDM (x s)
  have hz : τ.norm₂ z < τ.norm₂ y/4 := by
    change τ.norm₂ z^2 < (τ.norm₂ y/4)^2 at hn
    nlinarith [show 0 ≤ τ.norm₂ z from norm_nonneg _]
  have hdiff : τ.norm₂ (y-z) ≤ τ.norm₂ (y-x s) := by
    have he : conditionalExpectation τ hDM (y-x s)=y-z := by
      change conditionalExpectationCLM τ hDM (y-x s)=y-z
      rw [map_sub]
      change conditionalExpectation τ hDM y-z=y-z
      rw [conditionalExpectation_fixed τ hDM y (hym n)]
    rw [← he]
    exact conditionalExpectation_norm₂_le τ hDM _
  have hadd := τ.norm₂_add_le (y-z) z
  rw [sub_add_cancel] at hadd
  linarith

theorem exists_irreducible_matrix_sequence (τ : TracialRepresentation M) (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) (E : FiniteMatrixStage N) :
    ∃ A : ℕ → FiniteMatrixStage N,A 0=E ∧
      Monotone (fun n => (A n).units.algebra) ∧
      ∀ c : M.toStarSubalgebra,(∀ n,c.val ∈ (A n).commutant hNM) →
        c=τ.trace c • (1 : M.toStarSubalgebra) := by
  let S : Set M.toStarSubalgebra := {b | τ.trace b=0}
  obtain ⟨x,hx,hdense⟩ := exists_countable_norm₂_dense τ S ⟨0,by change τ.trace 0=0; simp [TracialRepresentation.trace]⟩
    (hsep.mono (Set.image_subset_range _ _))
  obtain ⟨A,hA,hmono,_,hlim⟩ := exists_countable_matrix_refinement τ hNM hfactor hdiff hirr x hx E
  exact ⟨A,hA,hmono,scalar_common_commutant_of_dense_energy_decay τ hNM A x hdense hlim⟩

end FiniteMatrixStage

end

/-! The actual weakly closed star algebra generated by the increasing finite
matrix stages. Its ambient relative commutant is scalar. This does not yet
package a diffuse II1 subfactor or derive the representation hypotheses. -/
section
namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem exists_irreducible_matrix_generated_algebra
    (τ : TracialRepresentation M) (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
    ∃ A : ℕ → FiniteMatrixStage N,A 0=scalarStage N ∧
      Monotone (fun n => (A n).units.concreteAlgebra) ∧
      (∀ n,FiniteDimensional ℂ (A n).units.concreteAlgebra) ∧
      WOTClosed (generated A) ∧ generated A ≤ N.toStarSubalgebra ∧
      ∀ c : M.toStarSubalgebra,(∀ a : generated A,a.val*c.val=c.val*a.val) →
        c=τ.trace c • (1 : M.toStarSubalgebra) := by
  obtain ⟨A,hA,hmono,hscalar⟩ := exists_irreducible_matrix_sequence τ hNM hfactor hdiff hirr hsep (scalarStage N)
  exact ⟨A,hA,concrete_stage_monotone A hmono,fun n => (A n).units.concrete_finiteDimensional,
    generated_closed A,generated_le A,generated_relative_scalar A τ hNM hscalar⟩

end FiniteMatrixStage

end

/-! The constructed matrix-generated weak closure is an actual II1 factor.
Its bundled von Neumann algebra and faithful trace use the same operators. -/
section
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P M : VonNeumannAlgebra H}

theorem irreducible_subalgebra_isII1 (τ : TracialRepresentation M) (hPM : P ≤ M)
    (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : P.toStarSubalgebra,coordinateInclusion hPM a*c=c*coordinateInclusion hPM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra)) : IsII1Factor P.toStarSubalgebra where
  nonzero := tracial_nonzero τ
  weaklyClosed := vonNeumann_wotClosed P
  factor c hc := by
    obtain ⟨z,hz⟩ := hirr (coordinateInclusion hPM c) (fun a => by
      simpa only [map_mul] using congrArg (coordinateInclusion hPM) (hc a))
    refine ⟨z,?_⟩
    rw [Algebra.algebraMap_eq_smul_one]
    apply Subtype.ext
    exact congrArg (fun b : M.toStarSubalgebra => b.val) hz
  finite := tracial_isometry_coisometry (restrictedTrace τ hPM)
  diffuse := irreducible_subalgebra_diffuse τ hPM hdiff hirr

end Tracial

end

/-! Finite matrix stages strongly approximate the actual weakly generated
algebra. The approximants here have no operator norm bound. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CountableAmplification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite standard multiplicities exhaust the countable standard
representation.  The first-coordinate projections and all intertwining
identities below are constructed on the actual Hilbert direct sum. -/

noncomputable section
namespace KadisonSimilarity

open Filter ContinuousLinearMap
open scoped ENNReal Topology ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

@[simp] theorem countableRepresentation_apply (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    countableRepresentation σ a = countableAmplify (σ a) := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_QuotientMomentLimit
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.quotientGNSVector_mk _root_.OAI.KadisonSimilarity.tracialUltrapowerGNSInclusion_mk _root_.OAI.KadisonSimilarity.tracialUltrapowerMap_mk _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing coordinate moment limits to the actual tracial quotient. -/

noncomputable section
namespace KadisonSimilarity

open HochschildComparison HochschildPatching HochschildUltrapower BoundedHochschild
open TracialUltrapower Filter Topology
open scoped ComplexOrder BoundedContinuousFunction

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (τ : B →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
  (tr : ∀ a b, τ (a * b) = τ (b * a))

/-- The quotient step uses only the coordinate limits, with no factor or
freeness assumption. -/
theorem finiteQuotientMoments_of_limits (hω : (ω : Filter ℕ) ≤ atTop)
    (A : ℕ → (ℕ →ᵇ B)) (u : ℕ → unitary B)
    (hu : ∀ m K N : ℕ, ∀ a : BoundedWord (Fin m) K N, admissibleTail a.2.val →
      Tendsto (fun n => τ (mixedEval
        (fun i : Fin m => (1 / 2 : ℂ) • (A i.val n - τ (A i.val n) • 1))
        (asPartialUnitary (u n)) a.1 a.2.val)) atTop (𝓝 0)) :
    FiniteQuotientMoments τ h1 ω tr A u := by
  intro m K N a ha
  let D : Fin m → (ℕ →ᵇ B) := fun i => (1 / 2 : ℂ) • centeredSequence τ (A i.val)
  let x : ℕ →ᵇ B := mixedEval D (asPartialUnitary (unitarySequence u)) a.1 a.2.val
  have hx : sequenceTrace τ ω x = 0 := by
    apply tendsto_nhds_unique (tendsto_sequenceTrace τ h1 ω x)
    have hh := (hu m K N a ha).mono_left hω
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    change τ (mixedEval D (asPartialUnitary (unitarySequence u)) a.1 a.2.val n) = _
    rw [mixedEval_sequence]
    rfl
  let C : Fin m → Ultrapower τ h1 ω tr := fun i => quotientHom τ h1 ω tr (A i.val) -
    quotientTrace τ h1 ω tr (quotientHom τ h1 ω tr (A i.val)) • 1
  have hD : quotientHom τ h1 ω tr ∘ D = fun i => (1 / 2 : ℂ) • C i := by
    funext i
    change quotientHom τ h1 ω tr ((1 / 2 : ℂ) • centeredSequence τ (A i.val)) = _
    rw [map_smul, quotient_centeredSequence]
  have hm : mapUnitary (quotientHom τ h1 ω tr) (unitarySequence u) =
      quotientUnitary τ h1 ω tr u := rfl
  have ht : quotientTrace τ h1 ω tr (quotientHom τ h1 ω tr x) = 0 := hx
  change quotientTrace τ h1 ω tr (quotientHom τ h1 ω tr
    (mixedEval D (asPartialUnitary (unitarySequence u)) a.1 a.2.val)) = 0 at ht
  rw [mixedEval_hom, hD, hm, mixedEval_smul, map_smul, smul_eq_mul] at ht
  exact (mul_eq_zero.mp ht).resolve_left (pow_ne_zero _ (by norm_num))

end KadisonSimilarity

end

end OAI
end


