-- Prove2me | Definitions.Def_OAIQ075A031
-- name    : OAIQ075A031
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T08:50:29.624772+00:00
-- url     : https://prove2.me/theorems/5635ebf9-4ab5-4013-92ad-255816485850
-- title:
--   Definitions bundle OAIQ075A031 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 28 declarations of OpenAI's Lean: 1 definition and 27 theorems. The definitions and types are `OAI.Generator.Tracial.conditionalExpectationCLM`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`BoundedHochschild_AlternatingMoments`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoundedHochschild/AlternatingMoments.lean), [`BoundedHochschild_MixedWords`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoundedHochschild/MixedWords.lean), [`BoundedHochschild_UltrapowerMoments`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoundedHochschild/UltrapowerMoments.lean), [`FactorGeneration_EnergyDescent`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/EnergyDescent.lean), [`FactorGeneration_Expectations`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/Expectations.lean), [`FactorGeneration_MatrixAlgebras`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/MatrixAlgebras.lean), [`FactorGeneration_MatrixRefinement`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/MatrixRefinement.lean), [`FactorGeneration_OrbitMinima`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/OrbitMinima.lean), [`FactorGeneration_ProjectionComparison`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/ProjectionComparison.lean).
--
--   **Imports.** It imports the bundles `OAIQ075A026` and `OAIQ075A027` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ075A035` and `OAIQ075A036`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ075A026
import Definitions.Def_OAIQ075A027

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_MixedWords
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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
lemma mixedEval_tendsto {K : Type*} {r : ℕ} {f : Filter K}
    {v : K → PartialUnitary M} {w : PartialUnitary M}
    (h : GNSTendsto τ (fun i => (v i : M)) f (w : M))
    (a : Option I) (l : List (WordAtom I r)) :
    GNSTendsto τ (fun i => mixedEval F (v i) a l) f (mixedEval F w a l) := by
  apply GNSTendsto.mul τ htr (GNSTendsto.const τ (wordCoeff F a) f) _ ‖wordCoeff F a‖ (fun _ => le_rfl)
  exact wordProduct_tendsto τ htr (fun i => (v i).power) w.power
    (fun k => PartialUnitary.power_tendsto τ htr h k) (fun i k => (v i).norm_power_le_one k) _

end HochschildPatching

 

 

open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison

variable {M : Type*} [CStarAlgebra M]
variable {I : Type*} (F : I → M)
lemma mixedEval_split {K : ℕ} (v w : PartialUnitary M) (h : v.support*w.support=0) (a : Option I) (l : List (WordAtom I K)) :
    mixedEval F (v.orthogonalSum w h) a l=mixedEval F v a l+
      wordCoeff F a*(ProductTaylor.linearTerms (l.map (splitFactor F v w))).sum+
      wordCoeff F a*(ProductTaylor.quadraticTerms (l.map (splitFactor F v w))).sum := by
  rw [mixedEval,← totalProduct_split F v w h,ProductTaylor.total_eq_old_add_linear_add_quadratic,
    mul_add,mul_add,oldProduct_split]
  rfl

variable [PartialOrder M] (τ : M →ₚ[ℂ] ℂ)

lemma mixedEval_patch_bound {K N : ℕ} (v w : PartialUnitary M) (h : v.support*w.support=0)
    (a : Option I) (l : List (WordAtom I K)) (hlen : l.length ≤ N) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hlin : ∀ x ∈ ProductTaylor.linearTerms (l.map (splitFactor F v w)), ‖τ (wordCoeff F a*x)‖ ≤ c)
    (hquad : ∀ x ∈ ProductTaylor.quadraticTerms (l.map (splitFactor F v w)), ‖τ (wordCoeff F a*x)‖ ≤ d) :
    ‖τ (mixedEval F (v.orthogonalSum w h) a l)‖ ≤ ‖τ (mixedEval F v a l)‖+(N : ℝ)*c+(N : ℝ)^2*d := by
  rw [mixedEval_split,map_add,map_add]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_add_le _ _).trans
    apply add_le_add le_rfl
    apply (trace_list_sum_bound τ _ _ _ hlin).trans
    rw [ProductTaylor.linearTerms_length,List.length_map]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hc
  · apply (trace_list_sum_bound τ _ _ _ hquad).trans
    apply mul_le_mul_of_nonneg_right _ hd
    have hn := ProductTaylor.quadraticTerms_length_le (l.map (splitFactor F v w))
    rw [List.length_map] at hn
    exact_mod_cast hn.trans (Nat.pow_le_pow_left hlen 2)
end HochschildPatching

 

 

open Filter Topology
open scoped ComplexOrder





open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {I : Type*} (F : I → M)

variable (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
omit [StarOrderedRing M] in
include htr in
lemma linear_trace_bound {K N : ℕ} (v w : PartialUnitary M) (a : Option I)
    (l : List (WordAtom I K)) (hlen : l.length ≤ N) (c : ℝ)
    (hweak : ∀ j : LinearLabel I K N, ‖τ (linearCoeff F v j*w.power (linearPower j))‖ ≤ c)
    (x : M) (hx : x ∈ ProductTaylor.linearTerms (l.map (splitFactor F v w))) :
    ‖τ (wordCoeff F a*x)‖ ≤ c := by
  obtain ⟨pre,b,post,he,rfl⟩ := ProductTaylor.mem_linearTerms_map _ hx
  have hn := hlen
  rw [he,List.length_append,List.length_cons] at hn
  let j : LinearLabel I K N := (a,⟨pre,by omega⟩,b,⟨post,by omega⟩)
  have hh := hweak j
  have ht : τ (wordCoeff F a*(ProductTaylor.oldProduct (pre.map (splitFactor F v w))*
      (splitFactor F v w b).2*ProductTaylor.oldProduct (post.map (splitFactor F v w))))=
      τ (linearCoeff F v j*w.power (linearPower j)) := by
    simp only [oldProduct_split,splitFactor,linearCoeff,linearPower,mixedEval,atomPower,j]
    rw [show wordCoeff F a*(wordProduct v.power (evaluatedTail F pre)*
        (w.power (b.1.1,b.1.2.val)*wordCoeff F b.2)*wordProduct v.power (evaluatedTail F post))=
      (wordCoeff F a*wordProduct v.power (evaluatedTail F pre)*w.power (b.1.1,b.1.2.val))*
        (wordCoeff F b.2*wordProduct v.power (evaluatedTail F post)) by simp only [mul_assoc],htr]
    simp only [mul_assoc]
  rw [ht]
  exact hh

end HochschildPatching
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_UltrapowerMoments
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

lemma mixedEval_unitary_product (F : I → M) (u : unitary M) (a : Option I) (l : List (WordAtom I K)) :
    mixedEval F (asPartialUnitary u) a l=wordCoeff F a *
      (l.map (fun b => ((u^signedExponent (b.1.1,b.1.2.val) : unitary M):M)*wordCoeff F b.2)).prod := by
  unfold mixedEval
  congr 1
  induction l with
  | nil => rfl
  | cons b l ih =>
    change (asPartialUnitary u).power (b.1.1,b.1.2.val)*wordCoeff F b.2*
      wordProduct (asPartialUnitary u).power (evaluatedTail F l)=_
    rw [unitary_power_eq,ih]
    rfl

lemma mixedEval_hom (φ : M →⋆ₐ[ℂ] A) (F : I → M) (u : unitary M)
    (a : Option I) (l : List (WordAtom I K)) :
    φ (mixedEval F (asPartialUnitary u) a l)=
      mixedEval (φ ∘ F) (asPartialUnitary (mapUnitary φ u)) a l := by
  rw [mixedEval_unitary_product,mixedEval_unitary_product,map_mul,wordCoeff_hom,map_list_prod,List.map_map]
  congr 1
  congr 1
  apply List.map_congr_left
  intro b hb
  simp only [Function.comp_apply,map_mul,wordCoeff_hom,mapUnitary_zpow]

end HochschildPatching

 

 

open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction





namespace HochschildPatching
variable {K : ℕ}

lemma all_finite_words {M : Type*} [CStarAlgebra M]
    (τ : M → ℂ) (F : ℕ → M) (u : unitary M)
    (hfinite : ∀ m K N : ℕ, ∀ a : BoundedWord (Fin m) K N,
      admissibleTail a.2.val → τ (mixedEval (F ∘ Fin.val) (asPartialUnitary u) a.1 a.2.val)=0)
    (K : ℕ) (a : Option ℕ) (l : List (WordAtom ℕ K)) (hl : admissibleTail l) :
    τ (mixedEval F (asPartialUnitary u) a l)=0 := by
  obtain ⟨m,f,ha,hll⟩ := exists_finite_reindex a l
  let a' : BoundedWord (Fin m) K l.length := (a.map f,⟨l.map (mapAtom f id),by simp⟩)
  have hh := hfinite m K l.length a' (admissibleTail_map f id l hl)
  change τ (mixedEval (F ∘ Fin.val) (asPartialUnitary u) (a.map f) (l.map (mapAtom f id)))=0 at hh
  rw [← mixedEval_map F Fin.val id (fun _ => rfl),ha,hll] at hh
  exact hh
end HochschildPatching

 

 

open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_AlternatingMoments
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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
lemma integerEval_toIntAtom {K : ℕ} (F : I → M) (u : unitary M) (a : Option I) (l : List (WordAtom I K)) :
    integerEval F u a (l.map toIntAtom)=mixedEval F (asPartialUnitary u) a l := by
  rw [mixedEval_unitary_product]
  simp only [integerEval,List.map_map]
  rfl

lemma integer_moments_of_bounded (τ : M → ℂ) (F : I → M) (u : unitary M)
    (hm : ∀ K : ℕ, ∀ a : Option I, ∀ l : List (WordAtom I K),
      admissibleTail l → τ (mixedEval F (asPartialUnitary u) a l)=0)
    (a : Option I) (l : List (IntAtom I)) (hl : admissibleIntTail l)
    (hk : ∀ b ∈ l, b.1 ≠ 0) : τ (integerEval F u a l)=0 := by
  classical
  let s : Finset ℕ := (l.map (fun b => (exponentCode b.1).2)).toFinset
  obtain ⟨K,hK⟩ := s.exists_nat_subset_range
  let g : IntAtom I → WordAtom I (K+1) := fun b =>
    (( (exponentCode b.1).1, if h : (exponentCode b.1).2 < K+1 then ⟨(exponentCode b.1).2,h⟩ else ⟨0,Nat.zero_lt_succ K⟩),b.2)
  have hg (b : IntAtom I) (hb : b ∈ l) : toIntAtom (g b)=b := by
    have hh : (exponentCode b.1).2 < K := Finset.mem_range.mp (hK (List.mem_toFinset.mpr (List.mem_map.mpr ⟨b,hb,rfl⟩)))
    dsimp only [g,toIntAtom]
    rw [dite_eq_left (Nat.lt_succ_of_lt hh)]
    change (signedExponent (exponentCode b.1),b.2)=b
    rw [signed_exponentCode _ (hk b hb)]
  have hmap : (l.map g).map toIntAtom=l := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id l]
    exact List.map_congr_left hg
  have had : admissibleTail (l.map g) := by
    constructor
    · intro h; exact hl.1 (List.map_eq_nil_iff.mp h)
    · intro b hb
      rw [← List.map_dropLast] at hb
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
      exact hl.2 c hc
  have ht := hm (K+1) a (l.map g) had
  rw [← integerEval_toIntAtom,hmap] at ht
  exact ht
end HochschildPatching





end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_OrbitMinima
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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
/-- Nonzero ambient projections cannot have all their P matrix coefficients
zero in an irreducible inclusion. No comparison theorem is assumed. -/
theorem projection_eq_zero_or_eq_zero_of_no_links (r s : AlgebraProjection M)
    (hlink : ∀ a : P, s.val*(a : M.toStarSubalgebra)*r.val=0) :
    r.val=0 ∨ s.val=0 := by
  have htest : ∀ u : subalgebraUnitaries P,
      τ.trace (star s.val*conjugateLinear u.val r.val)=0 := by
    intro u
    change τ.trace (star s.val*((u.val : M.toStarSubalgebra)*r.val*
      star (u.val : M.toStarSubalgebra)))=0
    rw [s.property.isSelfAdjoint.star_eq,← mul_assoc,← mul_assoc,
      hlink ⟨u.val.val,u.property⟩,zero_mul]
    exact inner_zero_right _
  have hz := orbitHull_trace_test_zero τ (subalgebraUnitaries P) r.val s.val htest
    (scalar_mem_traceOrbitHull τ P hirr r.val)
  rw [map_smul,inner_smul_right,baseVector_inner_eq_trace,
    s.property.isSelfAdjoint.star_eq,mul_one] at hz
  rcases mul_eq_zero.mp hz with hr | hs
  · left
    by_contra hn
    have hp := projection_trace_pos τ r.val r.property hn
    rw [hr,Complex.zero_re] at hp
    exact (lt_irrefl 0 hp)
  · right
    by_contra hn
    have hp := projection_trace_pos τ s.val s.property hn
    rw [hs,Complex.zero_re] at hp
    exact (lt_irrefl 0 hp)

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_ProjectionComparison
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A nonzero coefficient linking two projections produces an actual nonzero
partial isometry between subprojections. Scalar center supplies such coefficients. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem exists_nonzero_partialIsometry_between_projections
    (τ : TracialRepresentation M)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (p q : AlgebraProjection M) (hp : p.val≠0) (hq : q.val≠0) :
    ∃ v : PartialIsometry M, v.support ≤ p ∧ v.target ≤ q ∧ v.support.val≠0 := by
  classical
  let P : StarSubalgebra ℂ M.toStarSubalgebra := ⊤
  let : CompleteSpace P := isClosed_univ.completeSpace_coe
  have hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : P, (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
      ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra) := by
    intro c hc
    exact hfactor c (fun a => hc ⟨a,StarSubalgebra.mem_top⟩)
  have hex : ∃ a : P, q.val*(a : M.toStarSubalgebra)*p.val≠0 := by
    by_contra hn
    have hz : ∀ a : P, q.val*(a : M.toStarSubalgebra)*p.val=0 := by
      simpa only [not_exists,not_not] using hn
    exact (projection_eq_zero_or_eq_zero_of_no_links τ P hirr p q hz).elim hp hq
  obtain ⟨a,ha⟩ := hex
  apply exists_partialIsometry_of_link p q (q.val*(a : M.toStarSubalgebra)*p.val)
  · rw [mul_assoc,p.property.isIdempotentElem.eq]
  · rw [← mul_assoc,← mul_assoc,q.property.isIdempotentElem.eq]
  · exact ha

end

/-! Projection comparison and equal-trace equivalence in the actual factor.
Both polar decomposition and the maximal partial isometry are constructed. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))

include τ hfactor in
theorem exists_partialIsometry_comparison (p q : AlgebraProjection M) :
    ∃ v : PartialIsometry M, v.support ≤ p ∧ v.target ≤ q ∧
      (v.support=p ∨ v.target=q) := by
  obtain ⟨v,hvp,hvq,hmax⟩ := PartialIsometry.exists_maximal_between τ p q
  let r : AlgebraProjection M :=
    ⟨p.val-v.support.val,v.support.property.sub_of_mul_eq_right p.property hvp⟩
  let s : AlgebraProjection M :=
    ⟨q.val-v.target.val,v.target.property.sub_of_mul_eq_right q.property hvq⟩
  have hrp : r ≤ p := by
    change p.val*(p.val-v.support.val)=p.val-v.support.val
    rw [mul_sub,p.property.isIdempotentElem.eq,hvp]
  have hsq : s ≤ q := by
    change q.val*(q.val-v.target.val)=q.val-v.target.val
    rw [mul_sub,q.property.isIdempotentElem.eq,hvq]
  have hzero : r.val=0 ∨ s.val=0 := by
    by_contra hn
    have hr : r.val≠0 := fun h => hn (Or.inl h)
    have hs : s.val≠0 := fun h => hn (Or.inr h)
    obtain ⟨w,hwr,hws,hw0⟩ :=
      exists_nonzero_partialIsometry_between_projections τ hfactor r s hr hs
    have hpw : v.support.val*w.support.val=0 := by
      calc _ = v.support.val*(r.val*w.support.val) := by rw [hwr]
           _ = (v.support.val*r.val)*w.support.val := (mul_assoc _ _ _).symm
           _ = 0 := by
             change (v.support.val*(p.val-v.support.val))*w.support.val=0
             rw [mul_sub,projection_mul_of_le hvp,v.support.property.isIdempotentElem.eq,
               sub_self,zero_mul]
    have hqw : v.target.val*w.target.val=0 := by
      calc _ = v.target.val*(s.val*w.target.val) := by rw [hws]
           _ = (v.target.val*s.val)*w.target.val := (mul_assoc _ _ _).symm
           _ = 0 := by
             change (v.target.val*(q.val-v.target.val))*w.target.val=0
             rw [mul_sub,projection_mul_of_le hvq,v.target.property.isIdempotentElem.eq,
               sub_self,zero_mul]
    let u := PartialIsometry.patch v w hpw hqw
    have hup : u.support ≤ p := by
      change p.val*(v.support.val+w.support.val)=v.support.val+w.support.val
      rw [mul_add,hvp,show p.val*w.support.val=w.support.val from hwr.trans hrp]
    have huq : u.target ≤ q := by
      apply (u.target_le_iff_mul q).mpr
      change q.val*(v.val+w.val)=v.val+w.val
      rw [mul_add,(v.target_le_iff_mul q).mp hvq,
        (w.target_le_iff_mul q).mp (hws.trans hsq)]
    have hvu : v ≤ u := v.le_patch w hpw hqw
    exact (v.patch_ne w hpw hqw hw0) (le_antisymm (hmax u hup huq hvu) hvu)
  refine ⟨v,hvp,hvq,?_⟩
  rcases hzero with hr | hs
  · exact Or.inl (Subtype.ext (sub_eq_zero.mp hr).symm)
  · exact Or.inr (Subtype.ext (sub_eq_zero.mp hs).symm)

include hfactor in
theorem exists_partialIsometry_of_trace_eq (p q : AlgebraProjection M)
    (ht : τ.trace p.val=τ.trace q.val) :
    ∃ v : M.toStarSubalgebra, star v*v=p.val ∧ v*star v=q.val := by
  obtain ⟨v,hvp,hvq,hfull⟩ := exists_partialIsometry_comparison τ hfactor p q
  have he := v.trace_support_eq_target τ
  have hboth : v.support=p ∧ v.target=q := by
    rcases hfull with hp | hq
    · refine ⟨hp,projection_eq_of_le_of_trace_eq τ hvq ?_⟩
      rw [← he,hp,ht]
    · refine ⟨projection_eq_of_le_of_trace_eq τ hvp ?_,hq⟩
      rw [he,hq,ht]
  exact ⟨v.val,v.initial.trans (congrArg (fun z : AlgebraProjection M => z.val) hboth.1),
    congrArg (fun z : AlgebraProjection M => z.val) hboth.2⟩

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_EnergyDescent
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Quantitative descent for a finite spectral pinching, and actual unitary
displacement from irreducibility. A compatible spectral partition in a
residual corner is not postulated as a local-quantization theorem. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-- The strict displacement used before finite spectral approximation in
Popa A.1.1, Step 1, in the scalar-commutant case. -/
theorem exists_strict_centered_displacement
    (P : StarSubalgebra ℂ M.toStarSubalgebra) [CompleteSpace P]
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : P, (a : M.toStarSubalgebra)*c = c*(a : M.toStarSubalgebra)) →
      ∃ z : ℂ, c = z • (1 : M.toStarSubalgebra))
    (x : M.toStarSubalgebra) (hx : x ≠ 0) (ht : τ.trace x = 0) :
    ∃ u : subalgebraUnitaries P, τ.norm₂ x < τ.norm₂ (conjugateLinear u.val x-x) := by
  by_contra hn
  push Not at hn
  let K : Set H := {ξ | τ.norm₂ x^2/2 ≤ (inner ℂ (baseVector τ x) ξ).re}
  have hclosed : IsClosed K := isClosed_le continuous_const
    (Complex.continuous_re.comp (continuous_const.inner continuous_id))
  have hconv : Convex ℝ K := by
    intro ξ hξ η hη s t hs ht' hst
    change τ.norm₂ x^2/2 ≤ (inner ℂ (baseVector τ x) (s • ξ+t • η)).re
    simp only [inner_add_right, inner_smul_right_eq_smul, Complex.add_re, Complex.smul_re,
      smul_eq_mul]
    change τ.norm₂ x^2/2 ≤ (inner ℂ (baseVector τ x) ξ).re at hξ
    change τ.norm₂ x^2/2 ≤ (inner ℂ (baseVector τ x) η).re at hη
    nlinarith [mul_le_mul_of_nonneg_left hξ hs, mul_le_mul_of_nonneg_left hη ht']
  have horbit : baseVector τ '' algebraOrbit (subalgebraUnitaries P) x ⊆ K := by
    rintro ξ ⟨a,⟨u,rfl⟩,rfl⟩
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (hn u) 2
    change τ.norm₂ (conjugateLinear u.val x-x)^2 ≤ τ.norm₂ x^2 at hsq
    have hid := norm_sub_sq (𝕜 := ℂ) (baseVector τ (conjugateLinear u.val x)) (baseVector τ x)
    change τ.norm₂ (conjugateLinear u.val x-x)^2 = τ.norm₂ (conjugateLinear u.val x)^2 -
      2*(inner ℂ (baseVector τ (conjugateLinear u.val x)) (baseVector τ x)).re + τ.norm₂ x^2 at hid
    rw [conjugate_norm₂] at hid
    have hisym : (inner ℂ (baseVector τ (conjugateLinear u.val x)) (baseVector τ x)).re =
        (inner ℂ (baseVector τ x) (baseVector τ (conjugateLinear u.val x))).re :=
      inner_re_symm (𝕜 := ℂ) _ _
    rw [hisym] at hid
    change τ.norm₂ x^2/2 ≤ (inner ℂ (baseVector τ x) (baseVector τ (conjugateLinear u.val x))).re
    linarith
  have hz : (0 : H) ∈ traceOrbitHull τ (subalgebraUnitaries P) x := by
    simpa only [ht, zero_smul, map_zero] using scalar_mem_traceOrbitHull τ P hirr x
  have hzero := (closure_minimal (convexHull_min horbit hconv) hclosed) hz
  change τ.norm₂ x^2/2 ≤ (inner ℂ (baseVector τ x) 0).re at hzero
  rw [inner_zero_right, Complex.zero_re] at hzero
  have hpos : 0 < τ.norm₂ x^2 := sq_pos_of_ne_zero (fun he => hx ((τ.norm₂_eq_zero_iff x).mp he))
  linarith

end

/-! The one-step energy decrease has pieces in the prescribed von Neumann
subalgebra. Irreducibility supplies the unitary, not an assumed energy budget. -/

/-! Strict displacement from zero in the actual closed convex orbit hull,
without imposing a scalar commutant on a block diagonal algebra. -/

/-! Actual compatible 63/64 descent for the orthogonal component of Popa
A.1.1 in an irreducible inclusion. Both displacement and finite spectral
partitions are constructed, and all pieces remain in the prescribed N. -/

/-! Geometric iteration and finite-family small-energy partitions for the
orthogonal component. No energy budget or block displacement is assumed. -/

/-! Assembly of the orthogonal budget with an explicitly controlled
subalgebra component. This constructs the further refinement; constructing
the initial subalgebra-component budget is not asserted here. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Expectations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The orthogonal subalgebra representative of a self-adjoint ambient
operator is constructed, with its operator norm bound. -/

/-! A bounded trace-preserving subalgebra projection from self-adjoint least-distance points. Tracial orthogonality gives uniqueness and the bimodule identities. -/
section
open scoped ComplexStarModule
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem conditionalExpectation_add (hNM : N ≤ M) (x y : M.toStarSubalgebra) :
    conditionalExpectation τ hNM (x+y)=conditionalExpectation τ hNM x+conditionalExpectation τ hNM y := by
  apply conditionalExpectation_eq_of_orthogonal τ hNM
  · exact N.add_mem (conditionalExpectation_mem τ hNM x) (conditionalExpectation_mem τ hNM y)
  · have h := (conditionalExpectation_orthogonal τ hNM x).add τ
      (conditionalExpectation_orthogonal τ hNM y)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    abel

theorem conditionalExpectation_smul (hNM : N ≤ M) (z : ℂ) (x : M.toStarSubalgebra) :
    conditionalExpectation τ hNM (z • x)=z • conditionalExpectation τ hNM x := by
  apply conditionalExpectation_eq_of_orthogonal τ hNM
  · exact N.smul_mem (conditionalExpectation_mem τ hNM x) z
  · simpa only [smul_sub] using (conditionalExpectation_orthogonal τ hNM x).smul τ z

def conditionalExpectationCLM (hNM : N ≤ M) : M.toStarSubalgebra →L[ℂ] M.toStarSubalgebra :=
  LinearMap.mkContinuous
    { toFun := conditionalExpectation τ hNM
      map_add' := conditionalExpectation_add τ hNM
      map_smul' := conditionalExpectation_smul τ hNM }
    2 (conditionalExpectation_bound τ hNM)

theorem conditionalExpectation_fixed (hNM : N ≤ M) (x : M.toStarSubalgebra) (hx : x.val ∈ N) :
    conditionalExpectation τ hNM x=x := by
  apply conditionalExpectation_eq_of_orthogonal τ hNM x x hx
  intro a
  simp only [sub_self,mul_zero]
  exact inner_zero_right _

theorem conditionalExpectation_selfAdjoint (hNM : N ≤ M)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    IsSelfAdjoint (conditionalExpectation τ hNM x) ∧ ‖conditionalExpectation τ hNM x‖ ≤ ‖x‖ := by
  obtain ⟨c,hc,hn,ho⟩ := exists_selfAdjoint_expectation τ hNM x hx
  rw [conditionalExpectation_eq_of_orthogonal τ hNM x (coordinateInclusion hNM c) c.property ho]
  exact ⟨included_selfAdjoint hNM c hc,hn⟩

end

/-! The constructed expectation preserves adjoints, is a bimodule map,
and is the orthogonal projection for the trace norm. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem conditionalExpectation_mul_left (hNM : N ≤ M) (a x : M.toStarSubalgebra)
    (ha : a.val ∈ N) : conditionalExpectation τ hNM (a*x)=a*conditionalExpectation τ hNM x := by
  apply conditionalExpectation_eq_of_orthogonal τ hNM
  · exact N.mul_mem ha (conditionalExpectation_mem τ hNM x)
  · simpa only [mul_sub] using (conditionalExpectation_orthogonal τ hNM x).mul_left τ a ha

theorem conditionalExpectation_mul_right (hNM : N ≤ M) (a x : M.toStarSubalgebra)
    (ha : a.val ∈ N) : conditionalExpectation τ hNM (x*a)=conditionalExpectation τ hNM x*a := by
  apply conditionalExpectation_eq_of_orthogonal τ hNM
  · exact N.mul_mem (conditionalExpectation_mem τ hNM x) ha
  · simpa only [sub_mul] using (conditionalExpectation_orthogonal τ hNM x).mul_right τ a ha

theorem conditionalExpectation_star (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    conditionalExpectation τ hNM (star x)=star (conditionalExpectation τ hNM x) := by
  apply conditionalExpectation_eq_of_orthogonal τ hNM
  · exact star_mem (conditionalExpectation_mem τ hNM x)
  · simpa only [star_sub] using (conditionalExpectation_orthogonal τ hNM x).adjoint τ

theorem conditionalExpectation_norm₂_le (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    τ.norm₂ (conditionalExpectation τ hNM x) ≤ τ.norm₂ x := by
  have h := conditionalExpectation_pythagoras τ hNM x
  nlinarith [sq_nonneg (τ.norm₂ (x-conditionalExpectation τ hNM x)),
    show 0 ≤ τ.norm₂ x from norm_nonneg _]

end

/-! Positivity of the constructed expectation. The negative spectral part
is an actual subalgebra test operator; tracial orthogonality eliminates it. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

attribute [local instance] OAI.Generator.Tracial.expectationPosCStar
attribute [local instance] OAI.Generator.Tracial.expectationPosOrder
local instance expectationPosPreorder_r116b36_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.expectationPosLE
attribute [local instance] OAI.Generator.Tracial.expectationPosStarOrder
theorem conditionalExpectation_nonneg (hNM : N ≤ M) (x : M.toStarSubalgebra) (hx : 0 ≤ x) :
    0 ≤ conditionalExpectation τ hNM x := by
  let c := conditionalExpectation τ hNM x
  have hc : IsSelfAdjoint c := (conditionalExpectation_selfAdjoint τ hNM x hx.isSelfAdjoint).1
  have hd := CFC.negPart_nonneg c
  have hmem := negPart_mem_inside c (conditionalExpectation_mem τ hNM x)
  have ho := conditionalExpectation_orthogonal τ hNM x ⟨c⁻,hmem⟩
  change τ.trace (c⁻*(x-c))=0 at ho
  rw [mul_sub,trace_sub,sub_eq_zero] at ho
  have hprod : c⁻*c= -(c⁻*c⁻) := by
    nth_rw 2 [← CFC.posPart_sub_negPart c hc]
    rw [mul_sub,CFC.negPart_mul_posPart,zero_sub]
  have hp := trace_mul_nonneg τ c⁻ x hd hx
  rw [ho,hprod] at hp
  have htrace : τ.trace (-(c⁻*c⁻))= -τ.trace (c⁻*c⁻) := map_neg (coordinateTraceLinear τ) _
  have hsq : (τ.trace (c⁻*c⁻)).re=τ.norm₂ c⁻^2 := by
    rw [norm₂_sq_trace τ,hd.isSelfAdjoint.star_eq]
  rw [htrace,Complex.neg_re,hsq] at hp
  have hz := (τ.norm₂_eq_zero_iff c⁻).mp (sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (τ.norm₂ c⁻)]))
  exact (CFC.negPart_eq_zero_iff c hc).mp hz

end

/-! The constructed expectation satisfies the Schwarz inequality and is
contractive in operator norm. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

attribute [local instance] OAI.Generator.Tracial.expectationContractiveCStar
attribute [local instance] OAI.Generator.Tracial.expectationContractiveOrder
attribute [local instance] OAI.Generator.Tracial.expectationContractivePreorder
attribute [local instance] OAI.Generator.Tracial.expectationContractiveLE
attribute [local instance] OAI.Generator.Tracial.expectationContractiveStarOrder
theorem conditionalExpectation_schwarz (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    star (conditionalExpectation τ hNM x)*conditionalExpectation τ hNM x ≤
      conditionalExpectation τ hNM (star x*x) := by
  let y := conditionalExpectation τ hNM x
  have hy : y.val ∈ N := conditionalExpectation_mem τ hNM x
  have hys : (star y).val ∈ N := star_mem hy
  have hp := conditionalExpectation_nonneg τ hNM (star (x-y)*(x-y)) (star_mul_self_nonneg _)
  have he : conditionalExpectation τ hNM (star (x-y)*(x-y))=
      conditionalExpectation τ hNM (star x*x)-star y*y := by
    simp only [star_sub,sub_mul,mul_sub]
    change conditionalExpectationCLM τ hNM _= _
    rw [map_sub,map_sub,map_sub]
    change conditionalExpectation τ hNM (star x*x)-conditionalExpectation τ hNM (star y*x)-
      (conditionalExpectation τ hNM (star x*y)-conditionalExpectation τ hNM (star y*y))= _
    rw [conditionalExpectation_mul_right τ hNM y (star x) hy,
      conditionalExpectation_star τ hNM,
      conditionalExpectation_mul_left τ hNM (star y) x hys,
      conditionalExpectation_fixed τ hNM (star y*y) (N.mul_mem hys hy)]
    change conditionalExpectation τ hNM (star x*x)-star y*y-(star y*y-star y*y)=
      conditionalExpectation τ hNM (star x*x)-star y*y
    abel
  rw [he] at hp
  exact sub_nonneg.mp hp

theorem conditionalExpectation_norm_le (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    ‖conditionalExpectation τ hNM x‖ ≤ ‖x‖ := by
  have h := CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (conditionalExpectation_schwarz τ hNM x) (star_mul_self_nonneg (conditionalExpectation τ hNM x))
  have hn := (conditionalExpectation_selfAdjoint τ hNM (star x*x)
    (star_mul_self_nonneg x).isSelfAdjoint).2
  rw [CStarRing.norm_star_mul_self] at h hn
  nlinarith [norm_nonneg x,norm_nonneg (conditionalExpectation τ hNM x)]

end

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
-- module Solutions.OAIQ075_KS.FactorGeneration_MatrixAlgebras
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))

include hfactor in
theorem exists_matrixUnits_for_partition {p : AlgebraProjection M}
    (Q : CornerPartition p) (hn : 0 < Q.size)
    (ht : ∀ i j, τ.trace (Q.piece i).val=τ.trace (Q.piece j).val) :
    ∃ E : Fin Q.size → Fin Q.size → M.toStarSubalgebra,
      (∀ i, E i i=(Q.piece i).val) ∧
      (∀ i j, star (E i j)=E j i) ∧
      (∀ i j k l, E i j*E k l=if j=k then E i l else 0) ∧
      (∑ i, E i i)=p.val := by
  classical
  let o : Fin Q.size := ⟨0,hn⟩
  have hv : ∀ i, ∃ v : M.toStarSubalgebra,
      star v*v=(Q.piece o).val ∧ v*star v=(Q.piece i).val := fun i =>
    exists_partialIsometry_of_trace_eq τ hfactor (Q.piece o) (Q.piece i) (ht o i)
  choose v hvi hvf using hv
  let V (i : Fin Q.size) : PartialIsometry M := ⟨Q.piece o,v i,hvi i⟩
  have htarget (i : Fin Q.size) : (V i).target=Q.piece i := Subtype.ext (hvf i)
  have hcross (i j : Fin Q.size) (hij : i≠j) : star (v i)*v j=0 := by
    exact (V i).adjoint.mul_eq_zero (V j) (by
      change (V i).target.val*(V j).target.val=0
      rw [htarget,htarget]
      exact Q.orthogonal i j hij)
  let E (i j : Fin Q.size) := v i*star (v j)
  refine ⟨E,hvf,?_,?_,?_⟩
  · intro i j
    simp only [E,star_mul,star_star]
  · intro i j k l
    by_cases hjk : j=k
    · subst k
      rw [ite_eq_left rfl]
      change (v i*star (v j))*(v j*star (v l))=v i*star (v l)
      calc _ = (v i*(star (v j)*v j))*star (v l) := by simp only [mul_assoc]
           _ = v i*star (v l) := by
             rw [hvi,show v i*(Q.piece o).val=v i from (V i).mul_support]
    · rw [ite_eq_right hjk]
      change (v i*star (v j))*(v k*star (v l))=0
      calc _ = (v i*(star (v j)*v k))*star (v l) := by simp only [mul_assoc]
           _ = 0 := by rw [hcross j k hjk,mul_zero,zero_mul]
  · simpa only [E,hvf] using Q.total

end Tracial

/-! The matrix-unit image in the original represented algebra, with its
finite dimensionality and weak-operator closedness proved. -/
open scoped BigOperators

/-! The actual relative commutant in M is a diffuse scalar-center von
Neumann algebra, with the restricted faithful trace available from M. -/

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
-- module Solutions.OAIQ075_KS.FactorGeneration_MatrixRefinement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_normal_matrix_approximation
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (x : M.toStarSubalgebra) [IsStarNormal x] (ε : ℝ) (hε : 0 < ε) :
    ∃ k n : ℕ,n=2^k ∧ ∃ E : MatrixUnitSystem (Fin n) M.toStarSubalgebra,
      ∃ c : Fin n → ℂ,τ.norm₂ (x-∑ j,c j • E.entry j j) < ε := by
  obtain ⟨Q,c,hc⟩ := exists_normal_spectral_approximation x (ε/2) (by positivity)
  obtain ⟨k,R,hn,ht,d,hd⟩ := exists_dyadic_spectral_sum_approximation τ hdiff Q
    (fun _ : Unit => c) (ε/2) (by positivity)
  obtain ⟨E,hdiag,hstar,hmul,hsum⟩ := exists_matrixUnits_for_partition τ hfactor R
    (by rw [hn]; positivity) (fun i j => (ht i).trans (ht j).symm)
  let F : MatrixUnitSystem (Fin R.size) M.toStarSubalgebra := ⟨E,hstar,hmul,hsum⟩
  refine ⟨k,R.size,hn,F,d (),?_⟩
  change τ.norm₂ (x-∑ j,d () j • E j j) < ε
  simp only [hdiag]
  have he : x-∑ j,d () j • (R.piece j).val =
      (x-∑ i,c i • (Q.piece i).val)+
      ((∑ i,c i • (Q.piece i).val)-∑ j,d () j • (R.piece j).val) := by abel
  rw [he]
  exact (τ.norm₂_add_le _ _).trans_lt (by
    have h₁ := (τ.norm₂_le_norm _).trans_lt hc
    have h₂ := hd ()
    linarith)

end

/-! A constructed full matrix algebra reduces the actual relative-commutant
expectation energy by a uniform factor for a centered nonzero element. -/
open UltrapowerBridge

end Tracial

/-! Concrete commutants reverse matrix-algebra inclusion. Expectations are
compatible with restriction to an intermediate represented subalgebra. -/

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


