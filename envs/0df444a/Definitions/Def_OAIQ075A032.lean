-- Prove2me | Definitions.Def_OAIQ075A032
-- name    : OAIQ075A032
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T08:45:34.094846+00:00
-- url     : https://prove2.me/theorems/0d30fc97-a7cd-4ce6-8938-bf12127470a4
-- title:
--   Definitions bundle OAIQ075A032 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 52 declarations of OpenAI's Lean: 10 definitions, 1 inductive type or structure and 41 theorems. The definitions and types are `OAI.KadisonSimilarity.AllQuotientMoments`, `OAI.KadisonSimilarity.FiniteFactorPresentation.FreePosition`, `OAI.KadisonSimilarity.FiniteQuotientMoments`, `OAI.KadisonSimilarity.TracialInclusionModel`, `OAI.KadisonSimilarity.concreteNestedTracialMatrices`, `OAI.KadisonSimilarity.countableRepresentation`, `OAI.KadisonSimilarity.generatedMatrixTrace`, `OAI.KadisonSimilarity.generatedStageTransition`, `OAI.KadisonSimilarity.normalGNSEquivalence`, `OAI.KadisonSimilarity.normalGNSRepresentation`, `OAI.KadisonSimilarity.sourceExpectation`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BoundedHochschild_FiniteMoments`, `BoundedHochschild_IncrementalPatching`, `BoundedHochschild_MixedWords`, `KadisonSimilarity_FreeProduct_ConstantConjugateFreeness`, `KadisonSimilarity_FreeProduct_TracialInclusionFreeness`, `KadisonSimilarity_Representation_CountableAmplification`, `KadisonSimilarity_Tracial_ConcreteMatrixTower`, `KadisonSimilarity_Tracial_ConstantMomentTransport`, `KadisonSimilarity_Tracial_FiniteFactorPresentation`, `KadisonSimilarity_Tracial_GeneratedFiniteFactorModel`, `KadisonSimilarity_Tracial_MatrixExpectationIdentification`, `KadisonSimilarity_Tracial_MatrixStageGrowth`, `KadisonSimilarity_Tracial_QuotientMomentLimit`, `KadisonSimilarity_Tracial_RelativeMatrixQuantization`, `KadisonSimilarity_Tracial_SourcePartialUnitaries`, `KadisonSimilarity_Tracial_SourceWeakPowers`, `KadisonSimilarity_Tracial_TracialInclusionModel`, `KadisonSimilarity_Tracial_TracialInclusionQuantization`.
--
--   **Imports.** It imports the published bundle `Def_KadisonSimilarity`; the bundles `OAIQ075A026`, `OAIQ075A027` and `OAIQ075A028` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ075A035` and `OAIQ075A036`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A026
import Definitions.Def_OAIQ075A027
import Definitions.Def_OAIQ075A028

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
lemma norm_mixedEval {K : ℕ} (hF : ∀ i, ‖F i‖ ≤ 1) (v : PartialUnitary M)
    (a : Option I) (l : List (WordAtom I K)) : ‖mixedEval F v a l‖ ≤ 1 := by
  apply (norm_mul_le_of_le (norm_wordCoeff F hF a) (norm_wordProduct_le_one _ v.norm_power_le_one _ ?_)).trans_eq (one_mul 1)
  rintro ka hk
  obtain ⟨kb,hkb,rfl⟩ := List.mem_map.mp hk
  exact norm_wordCoeff F hF kb.2

end HochschildPatching

 

 

open scoped ComplexOrder





open Filter Topology
open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison
variable {M : Type*} [CStarAlgebra M] [PartialOrder M]
variable {I : Type*} (F : I → M) (τ : M →ₚ[ℂ] ℂ)

omit [PartialOrder M] in
lemma support_wrapped_eval {K : ℕ} (hK : 0<K) (v : PartialUnitary M) (i : I) (l : List (WordAtom I K)) :
    mixedEval F v none (((true,⟨0,hK⟩),some i)::(l++[((false,⟨0,hK⟩),none)]))=
      star (v:M)*mixedEval F v (some i) l*(v:M) := by
  simp only [mixedEval,evaluatedTail,List.map_cons,List.map_append,List.map_nil,wordProduct_cons,
    wordProduct_append,wordProduct_nil,wordCoeff_none,wordCoeff_some,one_mul,mul_one,
    PartialUnitary.power,ite_true,Bool.false_eq_true,ite_false,zero_add,pow_one,mul_assoc]

lemma residual_centered_word_bound {K N : ℕ} {b : ℝ → ℝ} {v : PartialUnitary M}
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hF : ∀ i, τ (F i)=0) (hb : 0 ≤ b ((τ v.support).re))
    (hv : MomentBound F τ (K := K) (N := N) b v) (hK : 0<K)
    (i : I) (l : List (WordAtom I K)) (hl : ∀ a ∈ l, a.2 ≠ none) (hn : l.length+2 ≤ N) :
    ‖τ ((1-v.support)*mixedEval F v (some i) l*(1-v.support))‖ ≤ 2*b ((τ v.support).re) := by
  have hz := centered_word_bound F τ hF hb hv i l hl (by omega)
  have hlen : (((true,⟨0,hK⟩),some i)::(l++[((false,⟨0,hK⟩),none)]) : List (WordAtom I K)).length ≤ N := by
    simpa only [List.length_cons,List.length_append,List.length_singleton,List.length_nil,Nat.add_assoc] using hn
  have hw := hv (none,⟨_,hlen⟩) (support_wrapped_admissible hK i l hl)
  rw [support_wrapped_eval] at hw
  rw [normalized_corner_trace_eq τ htr]
  exact (norm_sub_le _ _).trans ((add_le_add hz hw).trans_eq (by ring))

omit [PartialOrder M] in
lemma mixedEval_zero {K : ℕ} (a : Option I) (l : List (WordAtom I K)) (hl : l ≠ []) :
    mixedEval F (0 : PartialUnitary M) a l=0 := by
  cases l with
  | nil => exact (hl rfl).elim
  | cons ka l =>
    rcases ka with ⟨⟨s,k⟩,j⟩
    simp only [mixedEval,evaluatedTail,List.map_cons,wordProduct_cons,PartialUnitary.power,PartialUnitary.coe_zero,star_zero,ite_self,zero_pow (Nat.succ_ne_zero _),zero_mul,mul_zero]
lemma momentBound_zero {K N : ℕ} {b : ℝ → ℝ} (hb : 0 ≤ b 0) :
    MomentBound F τ (K := K) (N := N) b 0 := by
  intro w hw
  rw [mixedEval_zero F _ _ hw.1,map_zero,norm_zero,PartialUnitary.support_zero,map_zero,Complex.zero_re]
  exact hb
end HochschildPatching

 

 

open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {I : Type*} (F : I → M)

variable (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
omit [StarOrderedRing M] in
include htr in
lemma residualScalar_bound {K N : ℕ} {b : ℝ → ℝ} {v : PartialUnitary M}
    (hF : ∀ i, τ (F i)=0) (hb : 0 ≤ b ((τ v.support).re))
    (hv : MomentBound F τ (K := K) (N := N) b v) (hK : 0<K)
    (hp : 0<(τ (1-v.support)).re)
    (i : I) (l : List (WordAtom I K)) (hl : ∀ a ∈ l, a.2 ≠ none) (hn : l.length+2 ≤ N) :
    ‖residualScalar τ v (mixedEval F v (some i) l)‖ ≤ 2*b ((τ v.support).re)/(τ (1-v.support)).re := by
  rw [residualScalar,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp,div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (residual_centered_word_bound F τ htr hF hb hv hK i l hl hn) (inv_nonneg.mpr hp.le)

include htr in
lemma quadratic_trace_bound {K N : ℕ} {b : ℝ → ℝ} (v w : PartialUnitary M)
    (horth : v.support*w.support=0) (hK : 0<K)
    (hF : ∀ i, ‖F i‖ ≤ 1) (hFτ : ∀ i, τ (F i)=0)
    (hb : 0 ≤ b ((τ v.support).re)) (hv : MomentBound F τ (K := K) (N := N) b v)
    (hp : 0<(τ (1-v.support)).re) (ε : ℝ)
    (hsmall : ∀ z : BoundedWord I K N,
      ‖τ.toPreGNS (w.support*mixedEval F v z.1 z.2.val*w.support-
        residualScalar τ v (mixedEval F v z.1 z.2.val) • w.support)‖ ≤ ε*‖τ.toPreGNS w.support‖)
    (a : Option I) (l : List (WordAtom I K)) (hlen : l.length ≤ N) (hl : admissibleTail l)
    (x : M) (hx : x ∈ ProductTaylor.quadraticTerms (l.map (splitFactor F v w))) :
    ‖τ (wordCoeff F a*x)‖ ≤ (ε+2*b ((τ v.support).re)/(τ (1-v.support)).re)*(τ w.support).re := by
  obtain ⟨pre,aa,middle,bb,post,he,rfl⟩ := ProductTaylor.mem_quadraticTerms_map _ hx
  obtain ⟨haa,hmid⟩ := admissible_middle hl he
  obtain ⟨i,hi⟩ := Option.ne_none_iff_exists'.mp haa
  have hn := hlen
  rw [he,List.length_append,List.length_cons,List.length_append,List.length_cons] at hn
  let z : BoundedWord I K N := (some i,⟨middle,by omega⟩)
  have hs := hsmall z
  have hc := residualScalar_bound F τ htr hFτ hb hv hK hp i middle hmid (by omega)
  have ht := small_compression_trace_bound τ htr w.support_proj
    (mixedEval F v a pre) (atomPower w aa) (mixedEval F v (some i) middle)
    (atomPower w bb) (mixedEval F (v.orthogonalSum w horth) bb.2 post)
    (residualScalar τ v (mixedEval F v (some i) middle)) ε
    (norm_mixedEval F hF v a pre) (w.norm_power_le_one _) (w.norm_power_le_one _)
    (norm_mixedEval F hF _ _ _) (w.power_support _) (w.support_power _) hs
  have heq : wordCoeff F a*(ProductTaylor.oldProduct (pre.map (splitFactor F v w))*(splitFactor F v w aa).2*
      ProductTaylor.oldProduct (middle.map (splitFactor F v w))*(splitFactor F v w bb).2*
      ProductTaylor.totalProduct (post.map (splitFactor F v w)))=
        mixedEval F v a pre*atomPower w aa*mixedEval F v (some i) middle*
          atomPower w bb*mixedEval F (v.orthogonalSum w horth) bb.2 post := by
    simp only [splitFactor,oldProduct_split,totalProduct_split F v w horth,mixedEval,hi,mul_assoc]
  rw [heq]
  exact ht.trans (mul_le_mul_of_nonneg_right (add_le_add le_rfl hc) (τ.map_nonneg w.support_proj.nonneg).1)
end HochschildPatching
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_IncrementalPatching
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Corner partial unitaries, incremental moment estimates and unitary completion. -/

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
open scoped ComplexOrder







open scoped ComplexOrder







open Filter Topology
open scoped ComplexOrder





open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))

variable {I : Type*} (F : I → M)
include htr in
lemma trace_mixedEval_patch {K : ℕ} (v w : PartialUnitary M) (horth : v.support*w.support=0)
    (hF : ∀ i, ‖F i‖ ≤ 1) (a : Option I) (l : List (WordAtom I K)) :
    ‖τ (mixedEval F (v.orthogonalSum w horth) a l)-τ (mixedEval F v a l)‖ ≤
      (l.length : ℝ)*(τ w.support).re := by
  have hh := trace_wordProduct_patch τ htr v w horth (evaluatedTail F l)
    (fun a ha => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha; exact norm_wordCoeff F hF b.2)
    (wordCoeff F a) (norm_wordCoeff F hF a)
  simpa only [mixedEval,evaluatedTail,List.length_map] using hh


end HochschildPatching
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FiniteMoments
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.SourcePartialUnitary.coe_map _root_.OAI.KadisonSimilarity.SourcePartialUnitary.map_zero _root_.OAI.KadisonSimilarity.SourcePartialUnitary.power_map _root_.OAI.KadisonSimilarity.SourcePartialUnitary.support_map _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small unitary moments, reindexing and simultaneous moment sequences. -/

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
open scoped ComplexOrder





open Filter Topology
open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison
variable {M : Type*} [CStarAlgebra M]
variable {I J : Type*} {K L : ℕ}

lemma mixedEval_smul (F : I → M) (c : ℂ) (v : PartialUnitary M)
    (a : Option I) (l : List (WordAtom I K)) :
    mixedEval (fun i => c • F i) v a l=c^wordCoeffNumber a l • mixedEval F v a l := by
  have ht (l : List (WordAtom I K)) :
      wordProduct v.power (evaluatedTail (fun i => c • F i) l)=
        c^(l.map (fun b => coeffNumber b.2)).sum • wordProduct v.power (evaluatedTail F l) := by
    induction l with
    | nil => simp [evaluatedTail]
    | cons b l ih =>
      change v.power (b.1.1,b.1.2.val)*wordCoeff (fun i => c • F i) b.2*
        wordProduct v.power (evaluatedTail (fun i => c • F i) l) =
        c^(coeffNumber b.2+(l.map (fun b => coeffNumber b.2)).sum) •
          (v.power (b.1.1,b.1.2.val)*wordCoeff F b.2*wordProduct v.power (evaluatedTail F l))
      rw [wordCoeff_smul,ih]
      simp only [pow_add,mul_smul_comm,smul_mul_assoc,smul_smul,mul_comm]
  unfold mixedEval wordCoeffNumber
  rw [wordCoeff_smul,ht,pow_add]
  simp only [mul_smul_comm,smul_mul_assoc,smul_smul,mul_comm]
end HochschildPatching

 

 

 

open Filter Topology
open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_QuotientMomentLimit
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

/-- All bounded finite words in the centered coefficient family vanish. -/
def FiniteQuotientMoments (A : ℕ → (ℕ →ᵇ B)) (u : ℕ → unitary B) : Prop :=
  ∀ m K N : ℕ, ∀ a : BoundedWord (Fin m) K N, admissibleTail a.2.val →
    quotientTrace τ h1 ω tr (mixedEval
      (fun i : Fin m => quotientHom τ h1 ω tr (A i.val) -
        quotientTrace τ h1 ω tr (quotientHom τ h1 ω tr (A i.val)) • 1)
      (asPartialUnitary (quotientUnitary τ h1 ω tr u)) a.1 a.2.val) = 0

/-- Every admissible mixed word in an indexed coefficient family vanishes. -/
def AllQuotientMoments {I : Type*} (A : I → (ℕ →ᵇ B)) (u : ℕ → unitary B) : Prop :=
  ∀ K : ℕ, ∀ a : Option I, ∀ l : List (WordAtom I K), admissibleTail l →
    quotientTrace τ h1 ω tr (mixedEval
      (fun i => quotientHom τ h1 ω tr (A i) -
        quotientTrace τ h1 ω tr (quotientHom τ h1 ω tr (A i)) • 1)
      (asPartialUnitary (quotientUnitary τ h1 ω tr u)) a l) = 0

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_ConstantConjugateFreeness
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Source quotient unitaries and the concrete conjugated constant embedding. -/

noncomputable section
namespace KadisonSimilarity
open HochschildPatching HochschildUltrapower
open scoped ComplexOrder BoundedContinuousFunction

section Inclusion
variable {A B R : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [CStarAlgebra R]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hA : τA 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trA : ∀ a b, τA (a * b) = τA (b * a))
  (trB : ∀ a b, τB (a * b) = τB (b * a))
  (φ : A →⋆ₐ[ℂ] B) (hφ : ∀ a, τB (φ a) = τA a)

/-- Ambient constant freeness supplies the exact published-input proposition,
with the witness retained in the source ultrapower. -/
theorem popaConjugateFreeness_of_constant_moments
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite) (ρ : R →⋆ₐ[ℂ] A)
    (u : ℕ → unitary A)
    (hu : ConstantIntegerMoments τB hB ω trB (fun n => mapUnitary φ (u n))) :
    Popa1995ConjugateFreenessInput τA τB hA hB ω trA trB φ hφ hω ρ := by
  refine ⟨quotientUnitary τA hA ω trA u, ?_⟩
  apply (hu.scalarFree τB hB ω trB (fun n => mapUnitary φ (u n))).mono le_rfl
  rintro x ⟨a, rfl⟩
  refine ⟨φ (ρ a), ?_⟩
  exact (conjugatedConstantEmbedding_coordinate τA τB hA hB ω trA trB φ hφ ρ u a).symm
end Inclusion

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ConcreteMatrixTower
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate maps for the actual increasing matrix stages. These maps
retain the concrete operators and their normalized traces. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N : VonNeumannAlgebra H}

variable (F : ℕ → FiniteMatrixStage N)

def generatedMatrixTrace (υ : TracialRepresentation N) :
    (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra →ₚ[ℂ] ℂ :=
  vectorPositiveFunctional (FiniteMatrixStage.generatedVonNeumann F) υ.vector

theorem generatedMatrixVector_inner (υ : TracialRepresentation N)
    (a b : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra) :
    inner ℂ (generatedMatrixVector F υ a) (generatedMatrixVector F υ b) =
      generatedMatrixTrace F υ (star a * b) :=
  baseVector_inner_trace (FiniteMatrixStage.generatedTrace F υ le_rfl) a b

theorem generatedMatrixTrace_dist (υ : TracialRepresentation N)
    (a b : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra) :
    dist (gnsTracialVector (generatedMatrixTrace F υ) a)
      (gnsTracialVector (generatedMatrixTrace F υ) b) =
      dist (generatedMatrixVector F υ a) (generatedMatrixVector F υ b) :=
  gns_dist_eq_of_trace_vectors (generatedMatrixTrace F υ) (generatedMatrixVector F υ)
    (generatedMatrixVector_inner F υ) a b

theorem generatedMatrixTrace_one (υ : TracialRepresentation N) :
    generatedMatrixTrace F υ 1 = 1 :=
  vectorPositiveFunctional_one _ υ.vector υ.norm_vector

theorem generatedMatrixTrace_tracial (υ : TracialRepresentation N)
    (a b : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra) :
    generatedMatrixTrace F υ (a * b) = generatedMatrixTrace F υ (b * a) :=
  (FiniteMatrixStage.generatedTrace F υ le_rfl).trace_mul_comm a b

theorem generatedMatrixTrace_faithful (υ : TracialRepresentation N)
    (a : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra)
    (ha : generatedMatrixTrace F υ (star a * a) = 0) : a = 0 := by
  have hz : generatedMatrixVector F υ a = 0 :=
    inner_self_eq_zero.mp ((generatedMatrixVector_inner F υ a a).trans ha)
  exact (FiniteMatrixStage.generatedTrace F υ le_rfl).separating a hz

variable [Nontrivial N.toStarSubalgebra]
  (hmono : Monotone (fun n => (F n).units.concreteAlgebra))

def generatedStageTransition (s t : ℕ) (h : s ≤ t) :
    Matrix (Fin (F s).size) (Fin (F s).size) ℂ →⋆ₐ[ℂ]
      Matrix (Fin (F t).size) (Fin (F t).size) ℂ :=
  (concreteStageEquiv (F t)).symm.toStarAlgHom.comp
    ((StarSubalgebra.inclusion (hmono h)).comp (concreteStageEquiv (F s)).toStarAlgHom)

theorem generatedStageTransition_compatible (s t : ℕ) (h : s ≤ t)
    (a : Matrix (Fin (F s).size) (Fin (F s).size) ℂ) :
    generatedStageEmbedding F t (generatedStageTransition F hmono s t h a) =
      generatedStageEmbedding F s a := by
  apply Subtype.ext
  change (F t).units.concreteHom
      ((concreteStageEquiv (F t)).symm
        (StarSubalgebra.inclusion (hmono h) (concreteStageEquiv (F s) a))) =
    (F s).units.concreteHom a
  have he := (concreteStageEquiv (F t)).apply_symm_apply
    (StarSubalgebra.inclusion (hmono h) (concreteStageEquiv (F s) a))
  exact congrArg (fun b : (F t).units.concreteAlgebra => (b : H →L[ℂ] H)) he

omit [Nontrivial N.toStarSubalgebra] in
theorem generatedStageEmbedding_trace (υ : TracialRepresentation N) (n : ℕ)
    (a : Matrix (Fin (F n).size) (Fin (F n).size) ℂ) :
    generatedMatrixTrace F υ (generatedStageEmbedding F n a) =
        (Fintype.card (Fin (F n).size) : ℂ)⁻¹ * Matrix.trace a := by
  change υ.trace ((F n).units.hom a) = _
  exact (F n).units.trace_hom υ ⟨0, (F n).positive⟩ a

include hmono in
omit [Nontrivial N.toStarSubalgebra] in
theorem generatedStage_concrete_approximation (υ : TracialRepresentation N)
    (a : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n b, dist (generatedMatrixVector F υ (generatedStageEmbedding F n b))
      (generatedMatrixVector F υ a) < ε := by
  obtain ⟨n, b, hb⟩ := FiniteMatrixStage.exists_stage_strong_approximation F hmono a
    {υ.vector} ε hε
  obtain ⟨m, hm⟩ := b.property
  change (F n).units.concreteHom m = (b : H →L[ℂ] H) at hm
  refine ⟨n, m, ?_⟩
  rw [dist_eq_norm, generatedMatrixVector_apply,
    generatedMatrixVector_apply]
  change ‖(F n).units.concreteHom m υ.vector - (a : H →L[ℂ] H) υ.vector‖ < ε
  rw [hm, norm_sub_rev]
  exact hb υ.vector (Finset.mem_singleton_self _)

include hmono in
omit [Nontrivial N.toStarSubalgebra] in
theorem generatedStage_vector_approximation (υ : TracialRepresentation N)
    (a : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n b, dist (gnsTracialVector (generatedMatrixTrace F υ) (generatedStageEmbedding F n b))
      (gnsTracialVector (generatedMatrixTrace F υ) a) < ε := by
  obtain ⟨n, b, hb⟩ := generatedStage_concrete_approximation F hmono υ a ε hε
  exact ⟨n, b, (generatedMatrixTrace_dist F υ _ _).trans_lt hb⟩

include hmono in
omit [Nontrivial N.toStarSubalgebra] in
theorem generatedStage_vectors_dense (υ : TracialRepresentation N) :
    Dense (⋃ n, Set.range (fun a =>
      gnsTracialVector (generatedMatrixTrace F υ) (generatedStageEmbedding F n a))) :=
  gns_vectors_dense_of_approximation (generatedMatrixTrace F υ)
    (fun n a => generatedStageEmbedding F n a)
    (generatedStage_vector_approximation F hmono υ)

/-- The matrix presentation required by the commutator argument comes
from the actual increasing matrix subalgebras and their weak closure. -/
def concreteNestedTracialMatrices (υ : TracialRepresentation N) :
    NestedTracialMatrices (A := fun n => Fin (F n).size)
      (generatedMatrixTrace F υ).toLinearMap
      (gnsTracialVector (generatedMatrixTrace F υ)) where
  embedding := generatedStageEmbedding F
  trace_embedding := generatedStageEmbedding_trace F υ
  inclusion := generatedStageTransition F hmono
  compatible := generatedStageTransition_compatible F hmono
  dense := generatedStage_vectors_dense F hmono υ

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixExpectationIdentification
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of finite matrix averaging with the constructed normal
conditional expectation, for the relative quantization argument. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M N : VonNeumannAlgebra H} (υ : TracialRepresentation M)

attribute [local instance] OAI.KadisonSimilarity.matrixExpectationClosed
theorem matrix_average_eq_conditionalExpectation {n : ℕ}
    (E : MatrixUnitSystem (Fin n) M.toStarSubalgebra) (hn : n ≠ 0)
    (x : M.toStarSubalgebra) :
    (matrixSystemOfUnits E).expectation x =
      conditionalExpectation υ E.relativeVonNeumann_le x := by
  let S := matrixSystemOfUnits E
  let ρ := vectorPositiveFunctional M υ.vector
  have htr : ∀ a b, ρ (a * b) = ρ (b * a) := υ.trace_mul_comm
  symm
  apply conditionalExpectation_eq_of_orthogonal υ E.relativeVonNeumann_le
  · apply (E.relativeStar_mem _).mpr
    refine ⟨(S.expectation x).property, fun i j => ?_⟩
    exact congrArg Subtype.val (S.commute_expectation x i j).eq.symm
  · intro a
    have hcomm (i j : Fin n) : Commute (a : M.toStarSubalgebra) (S.entry i j) := by
      apply Subtype.ext
      exact ((E.relativeStar_mem (a : M.toStarSubalgebra).val).mp a.property).2 i j |>.symm
    have ha : S.expectation (a : M.toStarSubalgebra) = a := S.expectation_eq_self hn _ hcomm
    change ρ ((a : M.toStarSubalgebra) * (x - S.expectation x)) = 0
    rw [mul_sub, map_sub, ← S.trace_adjoint ρ htr, ha, sub_self]

theorem matrix_preGNS_norm_sq (x : M.toStarSubalgebra) :
    ‖(vectorPositiveFunctional M υ.vector).toPreGNS x‖ ^ 2 = υ.norm₂ x ^ 2 := by
  rw [HochschildMatrixSystems.MatrixSystem.norm_sq, norm₂_sq_trace]
  rfl

theorem matrix_stage_energy_eq (hNM : N ≤ M) (E : FiniteMatrixStage N)
    (x : M.toStarSubalgebra) :
    E.energy υ hNM x =
      ‖(vectorPositiveFunctional M υ.vector).toPreGNS
        ((matrixSystemOfUnits (E.units.map (coordinateInclusion hNM))).expectation x)‖ ^ 2 := by
  rw [matrix_preGNS_norm_sq, matrix_average_eq_conditionalExpectation υ _
    (Nat.ne_of_gt E.positive)]
  rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixStageGrowth
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A full finite matrix stage has a minimal diagonal projection. This
is the obstruction to a diffuse generated algebra stabilizing at a stage. -/

noncomputable section
namespace KadisonSimilarity

open Generator

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

section Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N : VonNeumannAlgebra H} [Nontrivial N.toStarSubalgebra]

theorem concreteStage_finrank (E : FiniteMatrixStage N) :
    Module.finrank ℂ E.units.concreteAlgebra = E.size ^ 2 := by
  rw [← (concreteStageEquiv E).toAlgEquiv.toLinearEquiv.finrank_eq]
  simp only [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one, pow_two]

theorem concreteStage_size_le {E F : FiniteMatrixStage N}
    (h : E.units.concreteAlgebra ≤ F.units.concreteAlgebra) : E.size ≤ F.size := by
  have hd : E.size ^ 2 ≤ F.size ^ 2 := by
    rw [← concreteStage_finrank E, ← concreteStage_finrank F]
    exact LinearMap.finrank_le_finrank_of_injective
      (f := (StarSubalgebra.inclusion h).toLinearMap) (StarSubalgebra.inclusion_injective h)
  exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hd

end Concrete

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_RelativeMatrixQuantization
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.concreteRademacher_square _root_.OAI.KadisonSimilarity.concreteRademacher_star _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.normalRestriction_apply _root_.OAI.KadisonSimilarity.normalRestriction_coefficient _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative finite matrix averaging in an irreducible inclusion. The matrix
systems stay in the prescribed source algebra throughout the refinement. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N M : VonNeumannAlgebra H} [Nontrivial N.toStarSubalgebra]
  (υ : TracialRepresentation M) (hNM : N ≤ M)
  (hfactor : ∀ c : N.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
  (hdiff : ∀ p : N.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
  (hirr : ∀ c : M.toStarSubalgebra,
    (∀ a : N.toStarSubalgebra, coordinateInclusion hNM a * c = c * coordinateInclusion hNM a) →
    ∃ z : ℂ, c = z • 1)

local instance relativeMatrixAmbientClosed_rd28443_1 : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  infer_instance
attribute [local instance] OAI.KadisonSimilarity.relativeMatrixSourceClosed
theorem matrix_stage_size_le_of_algebra_le {E F : FiniteMatrixStage N}
    (h : E.units.algebra ≤ F.units.algebra) : E.size ≤ F.size := by
  apply concreteStage_size_le
  intro x hx
  let a : N.toStarSubalgebra := ⟨x, E.units.concreteAlgebra_le hx⟩
  exact (F.units.mem_concreteAlgebra a).mpr (h ((E.units.mem_concreteAlgebra a).mp hx))

omit [Nontrivial N.toStarSubalgebra] in
/-- A small phase-energy budget gives a nonzero compression in the source
algebra, with its exact trace retained in the ambient representation. -/
theorem exists_source_rankOne_compression {I : Type*} [Fintype I]
    (E : FiniteMatrixStage N) (x : I → M.toStarSubalgebra) {δ : ℝ}
    (hbudget : (∑ i,
      (‖(vectorPositiveFunctional M υ.vector).toPreGNS
          ((matrixSystemOfUnits (E.units.map (coordinateInclusion hNM))).expectation (x i))‖ ^ 2 +
        ‖(vectorPositiveFunctional M υ.vector).toPreGNS (x i)‖ ^ 2 / (E.size : ℝ))) < δ) :
    ∃ q : N.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧
      υ.trace (coordinateInclusion hNM q) = (E.size : ℂ)⁻¹ ∧
      ∀ i, ‖(vectorPositiveFunctional M υ.vector).toPreGNS
        (coordinateInclusion hNM q * x i * coordinateInclusion hNM q)‖ ^ 2 <
          δ * (υ.trace (coordinateInclusion hNM q)).re := by
  classical
  let S := matrixSystemOfUnits (E.units.map (coordinateInclusion hNM))
  let ρ := vectorPositiveFunctional M υ.vector
  have htr : ∀ a b, ρ (a * b) = ρ (b * a) := υ.trace_mul_comm
  have h1 : ρ 1 = 1 := υ.trace_one
  have hn := Nat.ne_of_gt E.positive
  obtain ⟨g, hg⟩ := S.exists_phase_energy_bound ρ htr hn x
  let q := (matrixSystemOfUnits E.units).rankOne g
  have hq : coordinateInclusion hNM q = S.rankOne g := map_matrix_rankOne E.units _ g
  have ht : υ.trace (coordinateInclusion hNM q) = (E.size : ℂ)⁻¹ := by
    rw [hq]
    exact S.trace_rankOne ρ htr h1 hn g
  refine ⟨q, (matrixSystemOfUnits E.units).rankOne_projection hn g, ?_, ht, ?_⟩
  · intro hz
    rw [hz, map_zero] at ht
    rw [show υ.trace 0 = 0 by simp [TracialRepresentation.trace]] at ht
    have hnC : (E.size : ℂ) ≠ 0 := by exact_mod_cast hn
    exact (inv_ne_zero hnC) ht.symm
  · intro i
    have hi := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset I)) =>
        sq_nonneg ‖ρ.toPreGNS (S.phaseCoefficient g (x j))‖) (Finset.mem_univ i)
    have hiδ : ‖ρ.toPreGNS (S.phaseCoefficient g (x i))‖ ^ 2 < δ :=
      hi.trans_lt (hg.trans_lt hbudget)
    rw [hq]
    change ‖ρ.toPreGNS (S.rankOne g * x i * S.rankOne g)‖ ^ 2 < δ * (ρ (S.rankOne g)).re
    rw [S.rankOne_compression_norm ρ htr hn, S.trace_rankOne ρ htr h1 hn]
    have he : (E.size : ℂ)⁻¹ = Complex.ofReal ((E.size : ℝ)⁻¹) := by simp
    rw [he, Complex.ofReal_re, mul_comm δ]
    exact mul_lt_mul_of_pos_left hiδ (inv_pos.mpr (by exact_mod_cast E.positive))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CountableAmplification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.amplify_neg _root_.OAI.KadisonSimilarity.amplify_smul _root_.OAI.KadisonSimilarity.boundedMatrixHom_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.coordinateCornerOperator_apply _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.matrixOfOperator_apply _root_.OAI.NaimarkZFC.gns_apply_coe
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

@[simp] theorem firstCopiesProjection_adjoint (n : ℕ) :
    (firstCopiesProjection (H := H) n).adjoint = firstCopiesProjection n := by
  simp only [firstCopiesProjection, adjoint_comp, adjoint_adjoint]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The countable standard amplification of a represented algebra. -/
def countableRepresentation (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    A →⋆ₐ[ℂ] (CountableCopies H →L[ℂ] CountableCopies H) where
  toFun a := countableAmplify (σ a)
  map_zero' := by ext x i; simp
  map_one' := by ext x i; simp
  map_add' a b := by ext x i; simp
  map_mul' a b := by ext x i; simp [mul_apply_eq_comp]
  commutes' c := by ext x i; simp [Algebra.algebraMap_eq_smul_one]
  map_star' a := by
    change countableAmplify (σ (star a)) = (countableAmplify (σ a)).adjoint
    rw [countableAmplify_adjoint, map_star, ContinuousLinearMap.star_eq_adjoint]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_GeneratedFiniteFactorModel
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed matrix subfactor in a normal trace representation
supplies the finite-factor model in the original representation. Only the
prescribed ultrapower free position remains a local input. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

universe u
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {P : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  (τ : P.toStarSubalgebra →ₚ[ℂ] ℂ) (υ : TracialRepresentation N)
  (e : P.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra)
  (he : ∀ a, υ.trace (e a) = τ a) (F : ℕ → FiniteMatrixStage N)

include he in
theorem generatedOriginalInclusion_trace
    (a : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra) :
    τ (generatedOriginalInclusion e F a) = generatedMatrixTrace F υ a := by
  change τ (e.symm (StarSubalgebra.inclusion (FiniteMatrixStage.generated_le F) a)) =
    υ.trace (StarSubalgebra.inclusion (FiniteMatrixStage.generated_le F) a)
  have h := he (e.symm (StarSubalgebra.inclusion (FiniteMatrixStage.generated_le F) a))
  simpa only [e.apply_symm_apply] using h.symm

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_FiniteFactorPresentation
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite diffuse branch has a constructed normal trace and an actual
irreducible matrix source. Its sole remaining local input is Popa freeness. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open BoundedHochschild.KadisonRingrose
open scoped ComplexOrder

section GNS
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (htr : ∀ a b, τ (a * b) = τ (b * a))
  (hf : ∀ a, τ (star a * a) = 0 → a = 0) (hnormal : HasNormalGNS τ)

def normalGNSRepresentation :
    TracialRepresentation (representationVonNeumannAlgebra τ.gnsStarAlgHom) :=
  (gnsTracialGeometry τ htr).normalTracialRepresentation h1
    (gnsTracialVector_injective τ hf) _ hnormal

def normalGNSEquivalence :
    A ≃⋆ₐ[ℂ] (representationVonNeumannAlgebra τ.gnsStarAlgHom).toStarSubalgebra :=
  equivalenceOfConcreteRange _ τ.gnsStarAlgHom
    ((gnsTracialGeometry τ htr).left_injective (gnsTracialVector_injective τ hf)) hnormal

theorem normalGNSRepresentation_trace (a : A) :
    (normalGNSRepresentation τ h1 htr hf hnormal).trace
      (normalGNSEquivalence τ htr hf hnormal a) = τ a :=
  (gnsTracialGeometry τ htr).normalTracialRepresentation_trace h1
    (gnsTracialVector_injective τ hf) _ hnormal a

end GNS

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : VonNeumannAlgebra H)

attribute [instance] FiniteFactorPresentation.normed FiniteFactorPresentation.innerProduct
  FiniteFactorPresentation.complete

namespace FiniteFactorPresentation
variable {P} (F : FiniteFactorPresentation P)

attribute [local instance] OAI.KadisonSimilarity.finitePresentationClosed
theorem normal : HasNormalGNS F.traceData.trace :=
  hasNormalGNS_of_predual (concretePredualEquiv P) F.traceData.trace F.traceData.normal_predual F.traceData.tracial

theorem trace_inclusion (a : (FiniteMatrixStage.generatedVonNeumann F.source.stages).toStarSubalgebra) :
    F.traceData.trace (F.inclusion a) = generatedMatrixTrace F.source.stages F.representation a :=
  generatedOriginalInclusion_trace F.traceData.trace F.representation F.equivalence
    F.trace_equivalence F.source.stages a

def FreePosition (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite) : Prop :=
  FiniteFactorFreeCornerInputs (generatedMatrixTrace F.source.stages F.representation) F.traceData.trace
    (generatedMatrixTrace_one F.source.stages F.representation) F.traceData.one ω
    (generatedMatrixTrace_tracial F.source.stages F.representation) F.traceData.tracial
    F.inclusion F.trace_inclusion hω

end FiniteFactorPresentation

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialInclusionModel
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous normal representations of a trace-preserving inclusion.
The source range is proved closed, retaining the given source algebra. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

universe u
variable {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

structure TracialInclusionModel (φ : A →⋆ₐ[ℂ] B) (τ : B →ₚ[ℂ] ℂ) where
  K : Type u
  [normed : NormedAddCommGroup K]
  [innerProduct : InnerProductSpace ℂ K]
  [complete : CompleteSpace K]
  N : VonNeumannAlgebra K
  M : VonNeumannAlgebra K
  le : N ≤ M
  representation : TracialRepresentation M
  sourceEquiv : A ≃⋆ₐ[ℂ] N.toStarSubalgebra
  ambientEquiv : B ≃⋆ₐ[ℂ] M.toStarSubalgebra
  compatible : ∀ a, coordinateInclusion le (sourceEquiv a) = ambientEquiv (φ a)
  trace_eq : ∀ b, representation.trace (ambientEquiv b) = τ b

attribute [instance] TracialInclusionModel.normed TracialInclusionModel.innerProduct
  TracialInclusionModel.complete

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialInclusionQuantization
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative local quantization in two abstract von Neumann algebras, through
one faithful normal representation of their given inclusion. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

universe u
variable {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {φ : A →⋆ₐ[ℂ] B} {τ : B →ₚ[ℂ] ℂ}

namespace TracialInclusionModel
variable (F : TracialInclusionModel φ τ)

omit [PartialOrder A] [StarOrderedRing A] [StarOrderedRing B] in
theorem source_factor
    (h : ∀ c : A, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • (1 : A)) :
    ∀ c : F.N.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1 := by
  intro c hc
  obtain ⟨b, rfl⟩ := F.sourceEquiv.surjective c
  have hb (a : A) : a * b = b * a := by
    apply F.sourceEquiv.injective
    change F.sourceEquiv (a * b) = F.sourceEquiv (b * a)
    rw [map_mul, map_mul]
    exact hc (F.sourceEquiv a)
  obtain ⟨z, rfl⟩ := h b hb
  refine ⟨z, ?_⟩
  change F.sourceEquiv (z • 1) = z • 1
  rw [map_smul, map_one]

omit [PartialOrder A] [StarOrderedRing A] [StarOrderedRing B] in
theorem source_diffuse
    (h : ∀ p : A, IsStarProjection p → p ≠ 0 →
      ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q) :
    ∀ p : F.N.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q := by
  intro p hp hp0
  let e := F.sourceEquiv
  obtain ⟨q, hq, hq0, hqp, hpq, hqp'⟩ := h (e.symm p) (hp.map e.symm)
    (fun hz => hp0 (by simpa only [map_zero, e.apply_symm_apply] using congrArg e hz))
  refine ⟨e q, hq.map e, ?_, ?_, ?_, ?_⟩
  · intro hz
    apply hq0
    apply e.injective
    change e q = e 0
    simpa only [map_zero] using hz
  · exact fun hz => hqp (by simpa only [e.symm_apply_apply] using congrArg e.symm hz)
  · simpa only [map_mul, e.apply_symm_apply] using congrArg e hpq
  · simpa only [map_mul, e.apply_symm_apply] using congrArg e hqp'

omit [PartialOrder A] [StarOrderedRing A] [StarOrderedRing B] in
theorem source_irreducible
    (h : ∀ c : B, (∀ a : A, φ a * c = c * φ a) → ∃ z : ℂ, c = z • 1) :
    ∀ c : F.M.toStarSubalgebra,
      (∀ a : F.N.toStarSubalgebra, coordinateInclusion F.le a * c =
        c * coordinateInclusion F.le a) → ∃ z : ℂ, c = z • 1 := by
  intro c hc
  obtain ⟨b, rfl⟩ := F.ambientEquiv.surjective c
  have hb (a : A) : φ a * b = b * φ a := by
    apply F.ambientEquiv.injective
    change F.ambientEquiv (φ a * b) = F.ambientEquiv (b * φ a)
    rw [map_mul, map_mul, ← F.compatible a]
    exact hc (F.sourceEquiv a)
  obtain ⟨z, rfl⟩ := h b hb
  refine ⟨z, ?_⟩
  change F.ambientEquiv (z • 1) = z • 1
  rw [map_smul, map_one]

end TracialInclusionModel

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_SourceWeakPowers
attribute [-instance] _root_.OAI.KadisonSimilarity.concretePredual_separable _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak powers in a prescribed diffuse source, tested against ambient
coefficients. Conditional expectation moves only the coefficients. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open HochschildComparison
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N M : VonNeumannAlgebra H} (υ : TracialRepresentation M) (hNM : N ≤ M)

def sourceExpectation (a : M.toStarSubalgebra) : N.toStarSubalgebra :=
  ⟨(conditionalExpectation υ hNM a).val, conditionalExpectation_mem υ hNM a⟩

attribute [local instance] OAI.KadisonSimilarity.weakPowersSourceClosed
theorem sourceExpectation_pairing (a : M.toStarSubalgebra) (b : N.toStarSubalgebra) :
    υ.trace (a * coordinateInclusion hNM b) =
      vectorPositiveFunctional N υ.vector (sourceExpectation υ hNM a * b) := by
  have h := conditionalExpectation_orthogonal υ hNM a
    ⟨coordinateInclusion hNM b, b.property⟩
  have he : υ.trace (coordinateInclusion hNM b * a) =
      υ.trace (coordinateInclusion hNM b * conditionalExpectation υ hNM a) := by
    apply sub_eq_zero.mp
    simpa only [mul_sub, trace_sub] using h
  calc
    _ = υ.trace (coordinateInclusion hNM b * a) := υ.trace_mul_comm _ _
    _ = υ.trace (coordinateInclusion hNM b * conditionalExpectation υ hNM a) := he
    _ = υ.trace (conditionalExpectation υ hNM a * coordinateInclusion hNM b) :=
      υ.trace_mul_comm _ _
    _ = _ := rfl

/-- Every nonzero source corner contains a partial unitary whose prescribed
nonzero powers are weakly small against any finite family from the ambient algebra. -/
theorem exists_source_partial_unitary_weak_powers
    (hfactor : ∀ c : N.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
    (hdiff : ∀ p : N.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (p : N.toStarSubalgebra) (hp : IsStarProjection p) (hp0 : p ≠ 0)
    {I : Type*} [Fintype I] (a : I → M.toStarSubalgebra) (k : I → Bool × ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w : PartialUnitary N.toStarSubalgebra, w.support = p ∧
      ∀ i, ‖υ.trace (a i * coordinateInclusion hNM (w.power (k i)))‖ <
        ε * (υ.trace (coordinateInclusion hNM p)).re := by
  let τN := restrictedTrace υ hNM
  let ρ := vectorPositiveFunctional N υ.vector
  have htr : ∀ a b, ρ (a * b) = ρ (b * a) := τN.trace_mul_comm
  have hf (a : N.toStarSubalgebra) (ha : ρ (star a * a) = 0) : a = 0 := by
    apply τN.separating a
    exact inner_self_eq_zero.mp ((baseVector_inner_trace τN a a).trans ha)
  have hminimal : HochschildDiffuse.NoMinimalProjections N.toStarSubalgebra := by
    intro q hq hq0
    obtain ⟨r, hr, hr0, hrq, hqr, _⟩ := hdiff q hq hq0
    exact ⟨r, hr, (hr.le_iff_mul_eq_right hq).mpr hqr, hr0, hrq⟩
  obtain ⟨w, hw, hweak⟩ := HochschildPatching.exists_partial_unitary_weak_powers p hp
    (concretePredualEquiv N) ρ (vectorPositiveFunctional_normal N υ.vector)
    (vectorPositiveFunctional_one N υ.vector υ.norm_vector) htr hf
    (fun b hb => hfactor b (fun x => (hb x).eq.symm)) hminimal hp0
    (fun i => sourceExpectation υ hNM (a i)) k hε
  refine ⟨w, hw, fun i => ?_⟩
  rw [sourceExpectation_pairing υ hNM]
  exact hweak i

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_SourcePartialUnitaries
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partial unitaries remain in the source while their moments are evaluated
in the ambient algebra. -/

noncomputable section
namespace KadisonSimilarity

open HochschildComparison HochschildPatching BoundedHochschild
open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N M : VonNeumannAlgebra H} (υ : TracialRepresentation M) (hNM : N ≤ M)

/-- Source trace-norm convergence is exactly convergence after inclusion. -/
theorem source_gns_tendsto {J : Type*} {l : Filter J}
    {a : J → N.toStarSubalgebra} {b : N.toStarSubalgebra}
    (h : GNSTendsto (vectorPositiveFunctional N υ.vector) a l b) :
    GNSTendsto (vectorPositiveFunctional M υ.vector)
      (fun j => coordinateInclusion hNM (a j)) l (coordinateInclusion hNM b) := by
  apply h.congr
  intro j
  exact (preGNS_norm_map_eq (vectorPositiveFunctional N υ.vector)
    (vectorPositiveFunctional M υ.vector) (coordinateInclusion hNM) (fun _ => rfl)
    (a j - b)).symm.trans (by rw [map_sub])

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ConstantMomentTransport
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A trace-preserving map reflects vanishing constant mixed moments. -/

noncomputable section
namespace KadisonSimilarity
open HochschildPatching HochschildUltrapower
open scoped ComplexOrder BoundedContinuousFunction

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hA : τA 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trA : ∀ a b, τA (a * b) = τA (b * a))
  (trB : ∀ a b, τB (a * b) = τB (b * a))
  (φ : A →⋆ₐ[ℂ] B) (ht : ∀ a, τB (φ a) = τA a)

include ht in
theorem constantIntegerMoments_of_map (u : ℕ → unitary A)
    (hu : ConstantIntegerMoments τB hB ω trB (fun n => mapUnitary φ (u n))) :
    ConstantIntegerMoments τA hA ω trA u := by
  let Φ := tracialUltrapowerMap τA τB hA hB ω trA trB φ ht
  let F : A → Ultrapower τA hA ω trA := fun a => constant τA hA ω trA a - τA a • 1
  let G : B → Ultrapower τB hB ω trB := fun b => constant τB hB ω trB b - τB b • 1
  have hFG : Φ ∘ F = G ∘ φ := by
    funext a
    change Φ (constant τA hA ω trA a - τA a • 1) = G (φ a)
    simp only [Φ, G, map_sub, map_smul, map_one, tracialUltrapowerMap_constant, ht]
  intro a l hl hk
  have hzero := hu (a.map φ) (l.map (fun b => (b.1, b.2.map φ)))
    (admissibleIntTail_reindex φ l hl) (by
      intro b hb
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
      exact hk c hc)
  change quotientTrace τB hB ω trB (integerEval G
    (quotientUnitary τB hB ω trB (fun n => mapUnitary φ (u n)))
    (a.map φ) (l.map (fun b => (b.1, b.2.map φ)))) = 0 at hzero
  rw [integerEval_reindex] at hzero
  change quotientTrace τA hA ω trA (integerEval F (quotientUnitary τA hA ω trA u) a l) = 0
  rw [← tracialUltrapowerMap_trace τA τB hA hB ω trA trB φ ht,
    integerEval_hom, hFG, mapUnitary_tracialUltrapowerMap]
  exact hzero

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialInclusionFreeness
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prescribed-source freeness for an abstract normal tracial inclusion. -/

noncomputable section
namespace KadisonSimilarity
open Generator Generator.Tracial
open UltrapowerBridge (TracialRepresentation)
open HochschildPatching HochschildUltrapower
open scoped ComplexOrder

universe u
variable {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {φ : A →⋆ₐ[ℂ] B} {τ : B →ₚ[ℂ] ℂ}

namespace TracialInclusionModel
variable (F : TracialInclusionModel φ τ)

local instance modelMomentAmbientClosed : IsClosed (F.M.toStarSubalgebra : Set (F.K →L[ℂ] F.K)) := by
  change IsClosed (F.M : Set (F.K →L[ℂ] F.K))
  infer_instance
local instance modelMomentSourceClosed : IsClosed (F.N.toStarSubalgebra : Set (F.K →L[ℂ] F.K)) := by
  change IsClosed (F.N : Set (F.K →L[ℂ] F.K))
  infer_instance

end TracialInclusionModel

end KadisonSimilarity

end

end OAI
end


