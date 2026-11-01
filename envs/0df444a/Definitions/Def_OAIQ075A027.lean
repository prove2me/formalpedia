-- Prove2me | Definitions.Def_OAIQ075A027
-- name    : OAIQ075A027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T08:32:59.413282+00:00
-- url     : https://prove2.me/theorems/42ec4695-7167-4c8f-930f-8ab588073832
-- title:
--   Definitions bundle OAIQ075A027 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 34 declarations of OpenAI's Lean: 8 definitions, 3 inductive types or structures and 23 theorems. The definitions and types are `OAI.KadisonSimilarity.ConstantIntegerMoments`, `OAI.KadisonSimilarity.FiniteFactorModel`, `OAI.KadisonSimilarity.FiniteFactorPresentation`, `OAI.KadisonSimilarity.FiniteFactorPresentation.inclusion`, `OAI.KadisonSimilarity.IrreducibleMatrixSource`, `OAI.KadisonSimilarity.concreteRademacher`, `OAI.KadisonSimilarity.dyadicCornerHom`, `OAI.KadisonSimilarity.firstCopiesProjection`, `OAI.KadisonSimilarity.generatedMatrixVector`, `OAI.KadisonSimilarity.generatedOriginalInclusion`, `OAI.KadisonSimilarity.generatedStageEmbedding`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BoundedHochschild_IncrementalPatching`, `BoundedHochschild_MatrixSystems`, `BoundedHochschild_MixedWords`, `BoundedHochschild_RelativeQuantization`, `FactorGeneration_SpectralApproximation`, `FactorGeneration_SpectralPinching`, `FactorGeneration_Subfactors`, `KadisonSimilarity_FreeProduct_ConstantConjugateFreeness`, `KadisonSimilarity_Representation_CountableAmplification`, `KadisonSimilarity_Representation_DyadicCornerHom`, `KadisonSimilarity_Representation_FactorAssembly`, `KadisonSimilarity_Tracial_ConcreteMatrixTower`, `KadisonSimilarity_Tracial_ConcreteRealSequence`, `KadisonSimilarity_Tracial_ConjugateMomentCriterion`, `KadisonSimilarity_Tracial_ConstantMomentLimit`, `KadisonSimilarity_Tracial_FiniteFactorPresentation`, `KadisonSimilarity_Tracial_GeneratedFiniteFactorModel`.
--
--   **Imports.** It imports the published bundle `Def_KadisonSimilarity`; the bundles `OAIQ075A020`, `OAIQ075A021`, `OAIQ075A022` and `OAIQ075A023` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ075A031`, `OAIQ075A032`, `OAIQ075A033` and `OAIQ075A034`; the statement `OAI.KadisonSimilarity.FiniteFactorModel.estimate`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A020
import Definitions.Def_OAIQ075A021
import Definitions.Def_OAIQ075A022
import Definitions.Def_OAIQ075A023

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





open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison

variable {M : Type*} [CStarAlgebra M]
variable {I : Type*} (F : I → M)
lemma totalProduct_split {K : ℕ} (v w : PartialUnitary M) (h : v.support*w.support=0) (l : List (WordAtom I K)) :
    ProductTaylor.totalProduct (l.map (splitFactor F v w))=wordProduct (v.orthogonalSum w h).power (evaluatedTail F l) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons,ProductTaylor.total_cons,evaluatedTail,wordProduct_cons,splitFactor,atomPower] at *
    rw [ih,PartialUnitary.power_orthogonalSum]
    simp only [add_mul]
end HochschildPatching

 

 

open Filter Topology
open scoped ComplexOrder





open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_MatrixSystems
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildMatrixSystems.MatrixSystem.commutant_closed _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix systems, expectations and rational projection approximation. -/

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
namespace HochschildMatrixSystems
open BoundedHochschild HochschildRigidity HochschildComparison
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

include e hτ htr hfaith in
 

theorem exists_matrixSystem (h1 : τ 1=1)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M) (n : ℕ) (hn : 0<n) :
    Nonempty (MatrixSystem M n) := by
  classical
  have hn' : (0 : ℝ)<n := by exact_mod_cast hn
  obtain ⟨p,hp,_hpp,hpo,hps,hpt⟩ := exists_partition_trace e τ hτ htr hfaith hdiff
    n (IsStarProjection.one M) (inv_nonneg.mpr hn'.le)
      (by rw [h1,Complex.one_re,mul_inv_cancel₀ (ne_of_gt hn')])
  let i0 : Fin n := ⟨0,hn⟩
  have ht : ∀ i, τ (p i0)=τ (p i) := by
    intro i
    apply Complex.ext
    · rw [hpt,hpt]
    · exact (Complex.nonneg_iff.mp (τ.map_nonneg (hp i0).nonneg)).2.symm.trans
        (Complex.nonneg_iff.mp (τ.map_nonneg (hp i).nonneg)).2
  choose v hv0 hv using fun i => exists_partialIso_of_equal_trace e τ hτ htr hfaith
    h1 hfactor (hp i0) (hp i) (ht i)
  have hvi : ∀ i, v i*p i0=v i := fun i => mul_of_initial_projection (hp i0) (hv0 i)
  have hvf : ∀ i, p i*v i=v i := by
    intro i
    rw [← hv i,mul_assoc,hv0 i,hvi i]
  have hvs : ∀ i, star (v i)*p i=star (v i) := by
    intro i
    simpa only [star_mul,(hp i).isSelfAdjoint.star_eq] using congrArg star (hvf i)
  have hcross : ∀ i j, i ≠ j → star (v i)*v j=0 := by
    intro i j hij
    calc
      star (v i)*v j = (star (v i)*p i)*(p j*v j) := by rw [hvs,hvf]
      _ = star (v i)*(p i*p j)*v j := by simp only [mul_assoc]
      _ = 0 := by rw [hpo i j hij,mul_zero,zero_mul]
  refine ⟨⟨fun i j => v i*star (v j),?_,?_,?_⟩⟩
  · intro i j
    simp only [star_mul,star_star]
  · intro i j k l
    by_cases h : j=k
    · subst k
      rw [ite_eq_left rfl]
      calc
        (v i*star (v j))*(v j*star (v l)) = v i*(star (v j)*v j)*star (v l) := by
          simp only [mul_assoc]
        _ = v i*star (v l) := by rw [hv0,hvi]
    · rw [ite_eq_right h]
      calc
        (v i*star (v j))*(v k*star (v l)) = v i*(star (v j)*v k)*star (v l) := by
          simp only [mul_assoc]
        _ = 0 := by rw [hcross j k h,mul_zero,zero_mul]
  · simpa only [hv] using hps

end HochschildMatrixSystems

 

 

 

open scoped ComplexOrder







open Filter Topology
open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_RelativeQuantization
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.matrixSystemOfColumns_diagonal _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe _root_.OAI.PopaCenter.expectation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative small corners, root phases and weak powers of unitaries. -/

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
open Filter Topology
open scoped ComplexOrder







open scoped BigOperators ComplexConjugate InnerProductSpace





open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder







open Filter Topology
open scoped ComplexOrder
namespace HochschildMatrixSystems

open BoundedHochschild HochschildRigidity HochschildSakai
universe u v
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable {I : Type v} [Fintype I]

include e in
theorem exists_unitary_weak_powers
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M)
    (a : I → M) (k : I → ℤ) (hk : ∀ i, k i ≠ 0) {ε : ℝ} (hε : 0<ε) :
    ∃ u : unitary M, ∀ i, ‖τ (a i*(u^(k i) : unitary M) : M)‖<ε := by
  classical
  let m : ℕ := 1+ ∑ i,(k i).natAbs
  have hm : 0 < m := by dsimp [m]; omega
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hkm (i : I) : (k i : ZMod m) ≠ 0 := by
    intro hz
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (k i) m).mp hz
    have hh := Int.natAbs_le_of_dvd_ne_zero hd (hk i)
    simp only [Int.natAbs_natCast] at hh
    have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset I)) =>
      Nat.zero_le (k j).natAbs) (Finset.mem_univ i)
    dsimp [m] at hh
    omega
  let B : ℝ := ∑ i,‖a i‖^2
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hε2 : 0<ε^2 := sq_pos_of_pos hε
  obtain ⟨n,hnR⟩ := exists_nat_gt (B/ε^2)
  have hn : 0<n := by exact_mod_cast (lt_of_le_of_lt (div_nonneg hB hε2.le) hnR)
  have hnRpos : (0:ℝ)<n := by exact_mod_cast hn
  obtain ⟨E⟩ := exists_matrixSystem e τ hτ htr hfaith h1 hfactor hdiff n hn
  obtain ⟨g,hg⟩ := E.exists_root_trace_energy τ h1 htr (Nat.ne_of_gt hn) a
    (fun i => (k i : ZMod m)) hkm
  refine ⟨E.rootUnitary g,fun i => ?_⟩
  have hsum : B/(n:ℝ)<ε^2 := by
    apply (div_lt_iff₀ hnRpos).mpr
    have hh := (div_lt_iff₀ hε2).mp hnR
    nlinarith
  have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset I)) =>
    sq_nonneg ‖τ (a j*E.diagonalRoot (k j : ZMod m) g)‖) (Finset.mem_univ i)
  have hh : ‖τ (a i*E.diagonalRoot (k i : ZMod m) g)‖^2<ε^2 := hi.trans_lt (hg.trans_lt hsum)
  change ‖τ (a i*((E.rootUnitary g)^(k i) : unitary M).val)‖<ε
  rw [E.rootUnitary_zpow]
  exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hh

end HochschildMatrixSystems
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_IncrementalPatching
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.PopaCorner.instStarOrderedRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.SourcePartialUnitary.coe_map _root_.OAI.KadisonSimilarity.SourcePartialUnitary.map_zero _root_.OAI.KadisonSimilarity.SourcePartialUnitary.power_map _root_.OAI.KadisonSimilarity.SourcePartialUnitary.support_map _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildSakai HochschildCorners HochschildComparison
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (q : M) (hq : IsStarProjection q)

variable [PartialOrder M] [StarOrderedRing M]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable {I : Type v} [Fintype I]
include e hq in
theorem exists_partial_unitary_weak_powers
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M) (hq0 : q ≠ 0)
    (a : I → M) (k : I → Bool × ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ w : PartialUnitary M, w.support=q ∧ ∀ i, ‖τ (a i*w.power (k i))‖<ε*(τ q).re := by
  let eC := cornerPredualEquiv q hq e
  let ρ := cornerTrace q hq τ
  let b : I → Corner q hq := fun i => ⟨q*a i*q,compress_mem_corner hq (a i)⟩
  have ht : 0<(τ q).re := HochschildDiffuse.projection_trace_pos τ hfaith hq hq0
  obtain ⟨u,hu⟩ := HochschildMatrixSystems.exists_unitary_weak_powers eC ρ
    (cornerTrace_normal q hq e τ hτ) (cornerTrace_one q hq τ hfaith hq0)
    (cornerTrace_tracial q hq τ htr) (cornerTrace_faithful q hq τ hfaith hq0)
    (corner_factor q hq e τ hτ h1 htr hfaith hfactor hdiff hq0)
    (corner_no_minimal q hq hdiff) b (fun i => signedExponent (k i)) (fun i => signedExponent_ne_zero _) hε
  refine ⟨ofCornerUnitary q hq u,ofCornerUnitary_support q hq u,fun i => ?_⟩
  let v : Corner q hq := (u^signedExponent (k i) : unitary (Corner q hq))
  have hvq : (v:M)*q=(v:M) := v.property.2
  have hqv : q*(v:M)=(v:M) := v.property.1
  have he : τ ((b i*v : Corner q hq):M)=τ (a i*(v:M)) := by
    change τ (q*a i*q*(v:M))=_
    calc
      _ = τ (q*(a i*(v:M))) := by rw [mul_assoc,mul_assoc,hqv]
      _ = τ ((a i*(v:M))*q) := htr _ _
      _ = _ := by rw [mul_assoc,hvq]
  have hh := hu i
  change ‖cornerTrace q hq τ (b i*v)‖<ε at hh
  rw [cornerTrace_apply,he,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht] at hh
  rw [ofCornerUnitary_power]
  have hh' := (mul_lt_mul_of_pos_left hh ht)
  simpa only [← mul_assoc,mul_inv_cancel₀ ht.ne',one_mul,mul_comm (τ q).re ε] using hh'
end HochschildPatching

 

 

 

open scoped ComplexOrder







open Filter Topology
open scoped ComplexOrder





open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
include htr in
lemma trace_wordProduct_patch (v w : PartialUnitary M) (horth : v.support*w.support=0)
    (l : List ((Bool × ℕ) × M)) (hl : ∀ a ∈ l, ‖a.2‖ ≤ 1)
    (A : M) (hA : ‖A‖ ≤ 1) :
    ‖τ (A*wordProduct (v.orthogonalSum w horth).power l)-τ (A*wordProduct v.power l)‖ ≤
      (l.length : ℝ)*(τ w.support).re := by
  induction l generalizing A with
  | nil => simp
  | cons a l ih =>
    obtain ⟨k,c⟩ := a
    have hc := hl (k,c) (List.mem_cons_self ..)
    have htail := fun a ha => hl a (List.mem_cons_of_mem _ ha)
    have hA' : ‖A*v.power k*c‖ ≤ 1 := by
      simpa only [one_mul] using norm_mul_le_of_le (norm_mul_le_of_le hA (v.norm_power_le_one k)) hc
    have hin := ih htail (A*v.power k*c) hA'
    have hnew := trace_supported_insertion τ htr w.support_proj A (w.power k)
      (c*wordProduct (v.orthogonalSum w horth).power l) hA (w.norm_power_le_one k)
      (by simpa only [one_mul] using norm_mul_le_of_le hc (norm_wordProduct_le_one _ (fun k => (v.orthogonalSum w horth).norm_power_le_one k) l htail))
      (w.support_power k)
    have he : A*wordProduct (v.orthogonalSum w horth).power ((k,c)::l)-A*wordProduct v.power ((k,c)::l)=
        (A*v.power k*c*wordProduct (v.orthogonalSum w horth).power l-A*v.power k*c*wordProduct v.power l)+
          A*w.power k*(c*wordProduct (v.orthogonalSum w horth).power l) := by
      rw [wordProduct_cons,wordProduct_cons,PartialUnitary.power_orthogonalSum]
      noncomm_ring
    rw [← map_sub,he,map_add,map_sub]
    apply (norm_add_le _ _).trans
    have hh := add_le_add hin hnew
    simpa only [List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul] using hh

end HochschildPatching
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_SpectralPinching
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual sign splitting inside a prescribed residual corner. -/

/-! The constructed spectral splitting preserves the compressed operator.
This is distinct from using that splitting to reduce other operators' energy. -/

/-! Interval bounds propagated through constructed spectral corner splits. -/

/-! Finite dyadic trees of actual spectral interval cuts. -/
section
open scoped CStarAlgebra BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-! Finite spectral approximations constructed by successive sign cuts.
The approximation bound is proved from the leaf intervals. -/

/-- An actual finite orthogonal spectral approximation of a compressed
self-adjoint operator. All projections and coefficients are constructed. -/
theorem exists_finite_spectral_approximation (p : AlgebraProjection M)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (ε : ℝ) (hε : 0 < ε) :
    ∃ (Q : CornerPartition p) (c : Fin Q.size → ℝ),
      Q.pinch x=p.val*x*p.val ∧
      ‖p.val*x*p.val-∑ i, (c i : ℂ) • (Q.piece i).val‖ < ε := by
  let I := initialSpectralInterval p x hx
  have hI : I.lo ≤ I.hi := neg_le_self (norm_nonneg _)
  obtain ⟨n,hn⟩ := I.exists_approximant hx hI ε hε
  let e := (Fintype.equivFin (DyadicIndex n)).symm
  refine ⟨I.partition hx n,fun i => (I.level hx n (e i)).lo,I.partition_pinch hx n,?_⟩
  have he := Equiv.sum_comp e (fun i => ((I.level hx n i).lo : ℂ) • (I.level hx n i).proj.val)
  change ‖p.val*x*p.val-∑ i, ((I.level hx n (e i)).lo : ℂ) •
    (I.level hx n (e i)).proj.val‖ < ε
  rw [he]
  exact hn

end

/-! Constructed cuts preserve commutation with other operators. -/

/-! Spectral interval partitions in the commutant of a prescribed operator. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

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
-- module Solutions.OAIQ075_KS.FactorGeneration_SpectralApproximation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Common finite refinements of two commuting corner partitions. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-! Simultaneous finite spectral approximation of two commuting self-adjoint
operators. The same actual partition is used for both. -/

theorem exists_joint_spectral_approximation (p : AlgebraProjection M)
    (a b : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hab : Commute a b) (hpa : Commute p.val a) (hpb : Commute p.val b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (S : CornerPartition p) (c d : Fin S.size → ℝ),
      ‖p.val*a*p.val-∑ i, (c i : ℂ) • (S.piece i).val‖ < ε ∧
      ‖p.val*b*p.val-∑ i, (d i : ℂ) • (S.piece i).val‖ < ε := by
  obtain ⟨Q,c,hQfix,hQ,hc⟩ := exists_finite_spectral_approximation_preserving_commutant p a ha ε hε
  obtain ⟨R,d,hRfix,hR,hd⟩ := exists_finite_spectral_approximation_preserving_commutant p b hb ε hε
  have hcross (i : Fin Q.size) (j : Fin R.size) : Commute (Q.piece i).val (R.piece j).val := by
    have hqp : Commute p.val (Q.piece i).val :=
      (hQ p.val hpa.symm (Commute.refl _) i).symm
    exact (hR (Q.piece i).val (hQ b hab hpb i).symm hqp j).symm
  let e := (Fintype.equivFin (Fin Q.size × Fin R.size)).symm
  refine ⟨Q.joint R hcross,fun i => c (e i).1,fun i => d (e i).2,?_,?_⟩
  · have he := Equiv.sum_comp e (fun i => (c i.1 : ℂ) • (Q.jointPiece R hcross i).val)
    change ‖p.val*a*p.val-∑ i, (c (e i).1 : ℂ) • (Q.jointPiece R hcross (e i)).val‖ < ε
    rw [he,Q.joint_sum_left R hcross (fun i => (c i : ℂ))]
    exact hc
  · have he := Equiv.sum_comp e (fun i => (d i.2 : ℂ) • (Q.jointPiece R hcross i).val)
    change ‖p.val*b*p.val-∑ i, (d (e i).2 : ℂ) • (Q.jointPiece R hcross (e i)).val‖ < ε
    rw [he,Q.joint_sum_right R hcross (fun i => (d i : ℂ))]
    exact hd

/-- Complex finite spectral sums are constructed from the joint real and
imaginary approximations. No small pinching-energy premise occurs. -/
theorem exists_complex_spectral_approximation (p : AlgebraProjection M)
    (a b : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hab : Commute a b) (hpa : Commute p.val a) (hpb : Commute p.val b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (S : CornerPartition p) (c : Fin S.size → ℂ),
      ‖p.val*(a+Complex.I • b)*p.val-∑ i, c i • (S.piece i).val‖ < ε := by
  obtain ⟨S,c,d,hc,hd⟩ := exists_joint_spectral_approximation p a b ha hb hab hpa hpb
    (ε/2) (half_pos hε)
  refine ⟨S,fun i => (c i : ℂ)+Complex.I*(d i : ℂ),?_⟩
  have he : p.val*(a+Complex.I • b)*p.val-
      (∑ i, ((c i : ℂ)+Complex.I*(d i : ℂ)) • (S.piece i).val) =
      (p.val*a*p.val-∑ i, (c i : ℂ) • (S.piece i).val)+
        Complex.I • (p.val*b*p.val-∑ i, (d i : ℂ) • (S.piece i).val) := by
    simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc,add_smul,
      mul_smul,Finset.sum_add_distrib,Finset.smul_sum,smul_sub]
    abel
  rw [he]
  have hn := norm_add_le (p.val*a*p.val-∑ i, (c i : ℂ) • (S.piece i).val)
    (Complex.I • (p.val*b*p.val-∑ i, (d i : ℂ) • (S.piece i).val))
  rw [norm_smul,Complex.norm_I,one_mul] at hn
  linarith

end

/-! Finite spectral approximation for an actual normal operator. -/
section
open scoped BigOperators ComplexStarModule
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem exists_normal_spectral_approximation (x : M.toStarSubalgebra) [IsStarNormal x]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (Q : CornerPartition (identityProjection M)) (c : Fin Q.size → ℂ),
      ‖x-∑ i, c i • (Q.piece i).val‖ < ε := by
  obtain ⟨Q,c,h⟩ := exists_complex_spectral_approximation (identityProjection M)
    (ℜ x) (ℑ x) (ℜ x).property (ℑ x).property (Commute.realPart_imaginaryPart x)
    (Commute.one_left _) (Commute.one_left _) ε hε
  refine ⟨Q,c,?_⟩
  simpa only [identityProjection,one_mul,mul_one,realPart_add_I_smul_imaginaryPart] using h

end

/-! Transport constructed spectral partitions through an actual inclusion of
von Neumann algebras on the same Hilbert space. -/

/-! Finite simultaneous spectral approximation of any commuting self-adjoint
family, preserving a prior partition and the entire common commutant. -/

/-! Finite orthogonal families can be completed to unit partitions. Refining
blocks retains explicit disjoint index sets whose sums recover those blocks. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Subfactors
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe
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
section
open scoped BigOperators ComplexStarModule
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem selfAdjoint_corner_scalar_of_projections (p : AlgebraProjection M)
    (hmin : ∀ q : AlgebraProjection M,q ≤ p → q.val=0 ∨ q.val=p.val)
    (c : M.toStarSubalgebra) (hc : IsSelfAdjoint c)
    (hl : p.val*c=c) (hr : c*p.val=c) : ∃ z : ℂ,c=z • p.val := by
  let L : Submodule ℂ M.toStarSubalgebra := Submodule.span ℂ {p.val}
  have hclosed : IsClosed (L : Set M.toStarSubalgebra) := L.closed_of_finiteDimensional
  have hm : c ∈ closure (L : Set M.toStarSubalgebra) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨Q,d,_,hd⟩ := exists_finite_spectral_approximation p c hc ε hε
    have hpieces (i : Fin Q.size) : (Q.piece i).val ∈ L := by
      rcases hmin (Q.piece i) (Q.piece_le i) with h | h
      · rw [h]; exact L.zero_mem
      · rw [h]; exact Submodule.subset_span (Set.mem_singleton _)
    refine ⟨∑ i,(d i : ℂ) • (Q.piece i).val,
      L.sum_mem (fun i _ => L.smul_mem _ (hpieces i)),?_⟩
    simpa only [dist_eq_norm,hl,hr] using hd
  rw [hclosed.closure_eq] at hm
  exact (Submodule.mem_span_singleton.mp hm).imp (fun z hz => hz.symm)

theorem corner_scalar_of_projections (p : AlgebraProjection M)
    (hmin : ∀ q : AlgebraProjection M,q ≤ p → q.val=0 ∨ q.val=p.val)
    (c : M.toStarSubalgebra) (hl : p.val*c=c) (hr : c*p.val=c) :
    ∃ z : ℂ,c=z • p.val := by
  have hsl : p.val*star c=star c := by
    simpa only [star_mul,p.property.isSelfAdjoint.star_eq] using congrArg star hr
  have hsr : star c*p.val=star c := by
    simpa only [star_mul,p.property.isSelfAdjoint.star_eq] using congrArg star hl
  obtain ⟨a,ha⟩ := selfAdjoint_corner_scalar_of_projections p hmin (ℜ c)
    (ℜ c).property (by simp [realPart_apply_coe,mul_add,hl,hsl])
    (by simp [realPart_apply_coe,add_mul,hr,hsr])
  obtain ⟨b,hb⟩ := selfAdjoint_corner_scalar_of_projections p hmin (ℑ c)
    (ℑ c).property (by simp [imaginaryPart_apply_coe,mul_sub,hl,hsl])
    (by simp [imaginaryPart_apply_coe,sub_mul,hr,hsr])
  refine ⟨a+Complex.I*b,?_⟩
  calc c = (ℜ c : M.toStarSubalgebra)+Complex.I • (ℑ c : M.toStarSubalgebra) :=
      (realPart_add_I_smul_imaginaryPart c).symm
    _ = (a+Complex.I*b) • p.val := by rw [ha,hb,smul_smul,add_smul]

end

/-! Diffuseness descends to an irreducible von Neumann subalgebra of a
diffuse finite tracial algebra. Finiteness follows from the actual faithful trace. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P M : VonNeumannAlgebra H}

theorem tracial_isometry_coisometry (τ : TracialRepresentation M)
    (v : M.toStarSubalgebra) (hv : star v*v=1) : v*star v=1 := by
  let p : AlgebraProjection M := ⟨v*star v,by
    constructor
    · change (v*star v)*(v*star v)=v*star v
      calc _ = v*(star v*v)*star v := by simp only [mul_assoc]
           _ = v*star v := by rw [hv,mul_one]
    · simp only [IsSelfAdjoint,star_mul,star_star]⟩
  have ht : τ.trace p.val=τ.trace (identityProjection M).val := by
    change τ.trace (v*star v)=τ.trace 1
    rw [τ.trace_mul_comm,hv]
  have h := projection_eq_of_le_of_trace_eq τ (p := p) (q := identityProjection M)
    (one_mul _) ht
  exact congrArg Subtype.val h

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ConjugateMomentCriterion
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer mixed moments imply freeness of a conjugated subalgebra. -/

noncomputable section
namespace KadisonSimilarity
open HochschildPatching

variable {B C : Type*} [CStarAlgebra B] [CStarAlgebra C]

omit [CStarAlgebra B] in
lemma conjugate_blocks_zero (σ : C →ₗ[ℂ] ℂ) (F : B → C) (u : unitary C)
    (hm : ∀ a : Option B, ∀ l : List (IntAtom B), admissibleIntTail l →
      (∀ b ∈ l, b.1 ≠ 0) → σ (integerEval F u a l) = 0)
    (p : B × B) (v : List (B × B)) :
    σ (((p :: v).map (conjugateMomentBlock F u)).prod) = 0 := by
  have hz := hm (some p.1) ((1, some p.2) :: conjugateMomentTail v)
    (intTail_cons (conjugateMomentTail_admissible v) 1 p.2) (by
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · norm_num
      · exact conjugateMomentTail_nonzero v b hb)
  simpa only [integerEval, List.map_cons, List.prod_cons, wordCoeff_some, zpow_one,
    conjugateMomentTail_eval, conjugateMomentBlock, mul_assoc] using hz

variable (σ : C →ₗ[ℂ] ℂ) (h1 : σ 1 = 1)
  (tr : ∀ a b, σ (a * b) = σ (b * a)) (φ : B →⋆ₐ[ℂ] C) (u : unitary C)

include h1 tr in
/-- The only moments needed for conjugate freeness are words with nonzero
integer powers and centered coefficients in the original algebra. -/
theorem scalarFree_conjugate_of_integer_moments
    (hm : ∀ a : Option B, ∀ l : List (IntAtom B), admissibleIntTail l →
      (∀ b ∈ l, b.1 ≠ 0) →
      σ (integerEval (fun b => φ b - σ (φ b) • 1) u a l) = 0) :
    ScalarFree σ φ.range
      (((Unitary.conjStarAlgAut ℂ C u).toStarAlgHom).comp φ).range := by
  apply scalarFree_of_even_cyclic h1 tr
  intro x xs hw he
  obtain ⟨v, hv, hn⟩ := even_conjugate_blocks σ tr φ u (x :: xs) hw he
  have hvne : v ≠ [] := by
    intro h
    simp only [h, List.length_nil, mul_zero, List.length_cons] at hn
    omega
  obtain ⟨p, w, rfl⟩ := List.exists_cons_of_ne_nil hvne
  rw [hv]
  exact conjugate_blocks_zero σ _ u hm p w

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ConstantMomentLimit
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace-density promotes countable quotient moments to every constant coefficient. -/

noncomputable section
namespace KadisonSimilarity
open HochschildPatching HochschildUltrapower BoundedHochschild Filter Topology
open scoped ComplexOrder BoundedContinuousFunction

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (τ : B →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
  (tr : ∀ a b, τ (a * b) = τ (b * a))

def ConstantIntegerMoments (u : ℕ → unitary B) : Prop :=
  ∀ a : Option B, ∀ l : List (IntAtom B), admissibleIntTail l →
    (∀ b ∈ l, b.1 ≠ 0) → quotientTrace τ h1 ω tr
      (integerEval (fun x => constant τ h1 ω tr x - τ x • 1)
        (quotientUnitary τ h1 ω tr u) a l) = 0

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

section Moments
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (τ : B →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
  (tr : ∀ a b, τ (a * b) = τ (b * a))

theorem ConstantIntegerMoments.scalarFree (u : ℕ → unitary B)
    (hu : ConstantIntegerMoments τ h1 ω tr u) :
    ScalarFree (quotientTrace τ h1 ω tr).toLinearMap (constant τ h1 ω tr).range
      (((Unitary.conjStarAlgAut ℂ (Ultrapower τ h1 ω tr)
        (quotientUnitary τ h1 ω tr u)).toStarAlgHom).comp (constant τ h1 ω tr)).range := by
  apply scalarFree_conjugate_of_integer_moments
    (quotientTrace τ h1 ω tr).toLinearMap (quotientTrace_one τ h1 ω tr)
    (quotientTrace_tracial τ h1 ω tr) (constant τ h1 ω tr)
    (quotientUnitary τ h1 ω tr u)
  intro a l hl hk
  simpa only [PositiveLinearMap.coe_toLinearMap, quotientTrace_constant] using hu a l hl hk
end Moments

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CountableAmplification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

/-- The orthogonal projection onto the first `n` copies. -/
def firstCopiesProjection (n : ℕ) : CountableCopies H →L[ℂ] CountableCopies H :=
  (firstCopiesInclusion n).comp (firstCopiesInclusion n).adjoint

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_DyadicCornerHom
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerAlgebra _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerAlgebra _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instAlgebra _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.Generator.Tracial.quotientInclusion_mk _root_.OAI.Generator.Tracial.quotientInclusion_trace _root_.OAI.Generator.Tracial.restrictedTrace_norm₂ _root_.OAI.Generator.Tracial.restrictedTrace_trace _root_.OAI.KadisonSimilarity.CStarCorner.mem_subalgebra _root_.OAI.KadisonSimilarity.CStarCorner.normalizedTrace_apply _root_.OAI.KadisonSimilarity.DihedralSpectralArc.corner_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialExpectation.corner_map_coe _root_.OAI.KadisonSimilarity.concreteTraceLinear_apply _root_.OAI.KadisonSimilarity.concreteTraceLinear_one _root_.OAI.KadisonSimilarity.cornerStarAlgHom_coe _root_.OAI.KadisonSimilarity.haarCornerLetter_mul_support _root_.OAI.KadisonSimilarity.haarCornerPower_mul _root_.OAI.KadisonSimilarity.haarCornerPower_mul_support _root_.OAI.KadisonSimilarity.haarCornerPower_zero _root_.OAI.KadisonSimilarity.mul_haarCornerPower _root_.OAI.KadisonSimilarity.star_haarCornerLetter _root_.OAI.KadisonSimilarity.star_haarCornerPower _root_.OAI.KadisonSimilarity.support_mul_haarCornerLetter _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite dyadic spectral sums form contractive unital star
homomorphisms into the original corner. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
open scoped BigOperators CStarAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}
  (τ : TracialRepresentation M)
  (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)

theorem dyadicProjection_le_root (p : AlgebraProjection M) (n : ℕ)
    (i : DyadicIndex n) : dyadicProjection τ hdiff p n i ≤ p := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => exact (dyadicProjection_le_parent τ hdiff p n i).trans (ih i.1)

theorem dyadicEval_supported (p : AlgebraProjection M) (n : ℕ)
    (c : DyadicIndex n → ℂ) :
    p.val * dyadicEval τ hdiff p n c = dyadicEval τ hdiff p n c ∧
      dyadicEval τ hdiff p n c * p.val = dyadicEval τ hdiff p n c := by
  constructor
  · simp only [dyadicEval, projectionSum, Finset.mul_sum, mul_smul_comm]
    exact Finset.sum_congr rfl (fun i _ => congrArg (c i • ·)
      (dyadicProjection_le_root τ hdiff p n i))
  · simp only [dyadicEval, projectionSum, Finset.sum_mul, smul_mul_assoc]
    exact Finset.sum_congr rfl (fun i _ => congrArg (c i • ·)
      (projection_mul_of_le (dyadicProjection_le_root τ hdiff p n i)))

attribute [local instance] OAI.KadisonSimilarity.dyadicAlgebra_closed
def dyadicCornerHom (p : AlgebraProjection M) (n : ℕ) :
    (DyadicIndex n → ℂ) →⋆ₐ[ℂ] CStarCorner p.val p.property where
  toFun c := ⟨dyadicEval τ hdiff p n c, dyadicEval_supported τ hdiff p n c⟩
  map_zero' := Subtype.ext (by simp [dyadicEval, projectionSum])
  map_one' := by
    apply Subtype.ext
    change dyadicEval τ hdiff p n 1 =
      ((1 : CStarCorner p.val p.property) : M.toStarSubalgebra)
    rw [CStarCorner.coe_one]
    simpa only [dyadicEval, projectionSum, Pi.one_apply, one_smul] using
      dyadicProjection_sum τ hdiff p n
  map_add' c d := Subtype.ext (by simp [dyadicEval, projectionSum, add_smul,
    Finset.sum_add_distrib])
  map_mul' c d := Subtype.ext (projectionSum_mul _
    (dyadicProjection_orthogonal τ hdiff p n) c d).symm
  commutes' c := Subtype.ext (by
    change dyadicEval τ hdiff p n (fun _ => c) =
      ((algebraMap ℂ (CStarCorner p.val p.property) c :
        CStarCorner p.val p.property) : M.toStarSubalgebra)
    rw [Algebra.algebraMap_eq_smul_one]
    change dyadicEval τ hdiff p n (fun _ => c) =
      c • ((1 : CStarCorner p.val p.property) : M.toStarSubalgebra)
    rw [CStarCorner.coe_one]
    have h := congrArg (c • ·) (dyadicEval_one τ hdiff p n)
    simpa only [dyadicEval, projectionSum, Finset.smul_sum, smul_smul, mul_one] using h)
  map_star' c := Subtype.ext (projectionSum_star _ c).symm

@[simp] theorem dyadicCornerHom_coe (p : AlgebraProjection M) (n : ℕ)
    (c : DyadicIndex n → ℂ) :
    (dyadicCornerHom τ hdiff p n c : M.toStarSubalgebra) =
      dyadicEval τ hdiff p n c := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ConcreteRealSequence
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_vector _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dyadic signs in a diffuse finite tracial von Neumann algebra form
the real tracial sequence required by the matrix-tower construction. The
underlying projections have compatible dyadic refinements and
orthogonality relations. -/

noncomputable section
namespace KadisonSimilarity

open UltrapowerBridge Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

variable (τ : TracialRepresentation M)
  (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)

/-- The successive dyadic signs, based at the identity projection. -/
def concreteRademacher (n : ℕ) : M.toStarSubalgebra :=
  dyadicRademacher τ hdiff ⟨1, IsStarProjection.one _⟩ n

@[simp] theorem concreteRademacher_star (n : ℕ) :
    star (concreteRademacher τ hdiff n) = concreteRademacher τ hdiff n :=
  dyadicRademacher_star τ hdiff ⟨1, IsStarProjection.one _⟩ n

@[simp] theorem concreteRademacher_square (n : ℕ) :
    concreteRademacher τ hdiff n * concreteRademacher τ hdiff n = 1 :=
  dyadicRademacher_sq τ hdiff ⟨1, IsStarProjection.one _⟩ n

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_FactorAssembly
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three factor branches

The finite branch records only the fixed trace, matrix presentation, and
local published inputs used in the preceding application. The alternatives
are the structural factor classification; no alternative assumes an
operator estimate. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonSimilarity.instIsClosedContinuousLinearMapComplexIdCoeStarSubalgebra_solutions_2
/-- The complete finite-factor presentation required for the application. -/
structure FiniteFactorModel (P : VonNeumannAlgebra H) where
  R : Type u
  [cstar : CStarAlgebra R]
  [order : PartialOrder R]
  [starOrder : StarOrderedRing R]
  traceR : R →ₚ[ℂ] ℂ
  traceP : P.toStarSubalgebra →ₚ[ℂ] ℂ
  oneR : traceR 1 = 1
  oneP : traceP 1 = 1
  tracialR : ∀ a b, traceR (a * b) = traceR (b * a)
  tracialP : ∀ a b, traceP (a * b) = traceP (b * a)
  faithfulR : ∀ a, traceR (star a * a) = 0 → a = 0
  /-- Normality of the chosen source trace in its native GNS model. -/
  normalR : HasNormalGNS traceR
  faithfulP : ∀ a, traceP (star a * a) = 0 → a = 0
  /-- Normality of the chosen finite trace, in its native faithful GNS model. -/
  normalP : HasNormalGNS traceP
  inclusion : R →⋆ₐ[ℂ] P.toStarSubalgebra
  trace_inclusion : ∀ a, traceP (inclusion a) = traceR a
  size : ℕ → ℕ
  [stageNonempty : ∀ j, Nonempty (Fin (size j))]
  matrices : NestedTracialMatrices (A := fun j => Fin (size j))
    traceR.toLinearMap (gnsTracialVector traceR)
  size_tendsto : Filter.Tendsto (fun j => (Fintype.card (Fin (size j)) : ℝ))
    Filter.atTop Filter.atTop
  omega : Ultrafilter ℕ
  omega_cofinite : (omega : Filter ℕ) ≤ Filter.cofinite
  localInputs : FiniteFactorFreeCornerInputs traceR traceP oneR oneP omega
    tracialR tracialP inclusion trace_inclusion omega_cofinite

attribute [instance] FiniteFactorModel.cstar FiniteFactorModel.order
  FiniteFactorModel.starOrder FiniteFactorModel.stageNonempty

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ConcreteMatrixTower
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.concreteRademacher_square _root_.OAI.KadisonSimilarity.concreteRademacher_star _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.normalRestriction_apply _root_.OAI.KadisonSimilarity.normalRestriction_coefficient
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

def generatedStageEmbedding (n : ℕ) :
    Matrix (Fin (F n).size) (Fin (F n).size) ℂ →⋆ₐ[ℂ]
      (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra :=
  (F n).units.concreteHom.codRestrict (FiniteMatrixStage.generated F)
    (fun a => FiniteMatrixStage.stage_le_generated F n ⟨a, rfl⟩)

@[simp] theorem generatedStageEmbedding_apply (n : ℕ)
    (a : Matrix (Fin (F n).size) (Fin (F n).size) ℂ) :
    ((generatedStageEmbedding F n a :
      (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra) : H →L[ℂ] H) =
      (F n).units.concreteHom a := rfl

def generatedMatrixVector (υ : TracialRepresentation N) :
    (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra →ₗ[ℂ] H :=
  baseVector (FiniteMatrixStage.generatedTrace F υ le_rfl)

@[simp] theorem generatedMatrixVector_apply (υ : TracialRepresentation N)
    (a : (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra) :
    generatedMatrixVector F υ a = (a : H →L[ℂ] H) υ.vector := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_GeneratedFiniteFactorModel
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

def generatedOriginalInclusion :
    (FiniteMatrixStage.generatedVonNeumann F).toStarSubalgebra →⋆ₐ[ℂ] P.toStarSubalgebra :=
  e.symm.toStarAlgHom.comp (StarSubalgebra.inclusion (FiniteMatrixStage.generated_le F))

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

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : VonNeumannAlgebra H)

/-- The actual increasing irreducible matrix source in a fixed normal representation. -/
structure IrreducibleMatrixSource {K : Type u} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (N : VonNeumannAlgebra K) where
  stages : ℕ → FiniteMatrixStage N
  monotone : Monotone (fun n => (stages n).units.concreteAlgebra)
  source_factor : IsII1Factor (FiniteMatrixStage.generated stages)
  irreducible : ∀ c : N.toStarSubalgebra,
    (∀ a : FiniteMatrixStage.generated stages, a.val * c.val = c.val * a.val) →
    ∃ z : ℂ, c = z • 1

attribute [local instance] OAI.KadisonSimilarity.finitePresentationClosed
/-- All finite-factor presentation data except the local free position.
The represented Hilbert space is bundled to keep the GNS implementation opaque. -/
structure FiniteFactorPresentation where
  traceData : NormalFiniteTrace P
  K : Type u
  [normed : NormedAddCommGroup K]
  [innerProduct : InnerProductSpace ℂ K]
  [complete : CompleteSpace K]
  N : VonNeumannAlgebra K
  representation : TracialRepresentation N
  equivalence : P.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra
  trace_equivalence : ∀ a, representation.trace (equivalence a) = traceData.trace a
  source : IrreducibleMatrixSource N

attribute [instance] FiniteFactorPresentation.normed FiniteFactorPresentation.innerProduct
  FiniteFactorPresentation.complete

namespace FiniteFactorPresentation
variable {P} (F : FiniteFactorPresentation P)

def inclusion : (FiniteMatrixStage.generatedVonNeumann F.source.stages).toStarSubalgebra →⋆ₐ[ℂ]
    P.toStarSubalgebra := generatedOriginalInclusion F.equivalence F.source.stages

end FiniteFactorPresentation

end KadisonSimilarity

end

end OAI
end


