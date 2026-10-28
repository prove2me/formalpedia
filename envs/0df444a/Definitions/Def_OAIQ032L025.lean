-- Prove2me | Definitions.Def_OAIQ032L025
-- name    : OAIQ032L025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T20:15:41.472063+00:00
-- url     : https://prove2.me/theorems/b99cace8-d5e2-42c8-9e15-3663ebe329d6
-- title:
--   Definitions bundle OAIQ032L025 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 79 declarations of OpenAI's Lean: 29 definitions, 3 instances and 47 theorems. The definitions and types are `OAI.Lech.FiniteModuleCech.reductionPositiveIso`, `OAI.Lech.IdealFiltered.quotientFunctor`, `OAI.Lech.IdealFiltered.quotientRowIso`, `OAI.Lech.IdealFiltered.rowIso`, `OAI.Lech.IdealFiltered.rowTermEquiv`, `OAI.Lech.IdealGraded.pieceEquiv`, `OAI.Lech.IdealGraded.toPiece`, `OAI.Lech.ProductSourceCover.chartLine`, `OAI.Lech.ProductSourceCover.ringProjector`, `OAI.Lech.ProductSourceCover.ringSections`, `OAI.Lech.ProductSourceCover.sourceCech`, `OAI.Lech.RootChartAtlas.L`, `OAI.Lech.RootChartAtlas.coordinate`, `OAI.Lech.RootChartAtlas.q`, `OAI.Lech.RootChartAtlas.toH`, `OAI.Lech.RootInvariants.chartCoordinate`, `OAI.Lech.RootInvariants.chartExtension`, `OAI.Lech.RootInvariants.chartFunction`, `OAI.Lech.RootInvariants.chartRing`, `OAI.Lech.RootInvariants.chartUnit`, `OAI.Lech.RootInvariants.overAlgebra`, `OAI.Lech.RootInvariants.overAlgebraEquiv`, `OAI.Lech.RootInvariants.productSection`, `OAI.Lech.RootInvariants.sectionX`, `OAI.Lech.RootInvariants.sectionY`, `OAI.Lech.RootInvariants.selected`, `OAI.Lech.UniversalFactorMap.chartMap`, `OAI.Lech.UniversalFactorMap.map`, `OAI.Lech.UniversalFactorMap.splittingMap`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_AlternatingCechUnaugmentedComplex`, `Multiplicity_CechReduction`, `Multiplicity_GradedChartCochains`, `Multiplicity_GradedLineBasisHasBasis`, `Multiplicity_IdealFilteredLayers`, `Multiplicity_IdealFilteredQuotient`, `Multiplicity_IdealFilteredRows`, `Multiplicity_IdealGradedRing`, `Multiplicity_LechFactorizationMap`, `Multiplicity_LechHomogeneousEval`, `Multiplicity_NativeDescentCanonicalAlg`, `Multiplicity_ProductSourceCoverHighThreshold`, `Multiplicity_ProductSourceCoverOrdinaryPositive`, `Multiplicity_RootCoactionT`, `Multiplicity_RootCoefficientEuler`, `Multiplicity_RootInvariantsWeightZero`, `Multiplicity_StandardFactorChartsL`, `Multiplicity_UniversalFactorMapMapChart`.
--
--   **Imports.** It imports the bundles `OAIQ032L019`, `OAIQ032L020` and `OAIQ032L021` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ032L028` and `OAIQ032L029`; the proofs of `OAI.Lech.LinearNormalization.generator_number_le_dimension`, `OAI.Lech.MinimalReduction.exists_minimal_reduction`, `OAI.Lech.MinimalReduction.shifted_colength_limit`, `OAI.Lech.Normalization.parameter_frobenius_multiplicity_enn`, `OAI.Lech.Normalization.parameter_multiplicity_pos`, `OAI.Lech.Primary.multiplicity_nonneg` and `OAI.Lech.PrimeFiltration.Factors.multiplicity_self`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ032L019
import Definitions.Def_OAIQ032L020
import Definitions.Def_OAIQ032L021

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealGradedRing
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.IdealGraded.reesGradedAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.SourceGraded.target_graded _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
namespace Lech.IdealGraded
open Polynomial DirectSum
variable {R : Type*} [CommRing R] (I : Ideal R)

def toPiece (i : ℕ) : Piece I i →ₗ[R ⧸ I] grade I i where
  toFun x := ⟨toRingR I i x, toRingR_mem I i x⟩
  map_add' x y := Subtype.ext ((toRingR I i).map_add x y)
  map_smul' a x := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    apply Subtype.ext
    change toRingR I i (r • x) = r • toRingR I i x
    exact (toRingR I i).map_smul r x

lemma toPiece_bijective (i : ℕ) : Function.Bijective (toPiece I i) := by
  constructor
  · intro x y h
    apply toRingR_injective I i
    exact congrArg Subtype.val h
  · rintro ⟨_, p, ⟨x, rfl⟩, rfl⟩
    exact ⟨(nextPower I i).mkQ x, rfl⟩

noncomputable def pieceEquiv (i : ℕ) : Piece I i ≃ₗ[R ⧸ I] grade I i :=
  LinearEquiv.ofBijective (toPiece I i) (toPiece_bijective I i)

instance gradeFinite [IsNoetherianRing R] (i : ℕ) : Module.Finite (R ⧸ I) (grade I i) :=
  Module.Finite.of_surjective (toPiece I i) (toPiece_bijective I i).2

end Lech.IdealGraded


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_GradedChartCochains
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian


namespace Lech.ImageCech
open SetLike Graded
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (G : ℕ → Submodule R A) [GradedAlgebra G]
  (H : ℕ → Submodule R B) [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A), g (r • a) = r • g a)
  {h : ℕ} (y : Fin h → A) (hy : ∀ i, y i ∈ G 1)


lemma mapTerm_naturality {s v : Finset (Fin h)} (hsv : s ⊆ v) (t : ℕ)
    (x : GradedChart.term G y s t) :
    mapTerm G H g hg y hy v t (GradedChart.restrict G y hy hsv t x) =
      restrict G H g y hy hsv t (mapTerm G H g hg y hy s t x) := by
  apply Subtype.ext
  exact AlgHom.congr_fun (TwistedLocalization.ambientMap_naturality G H g hg
    (GradedChart.denominator_dvd y hsv)) x.val


lemma mapCochains_naturality (n t : ℕ) (f : GradedChart.cochains G y n t) :
    mapCochains G H g hg y hy (n+1) t (GradedChart.d G y hy n t f) =
      d G H g y hy n t (mapCochains G H g hg y hy n t f) := by
  funext a
  change mapTerm G H g hg y hy (ActualCech.intersection a) t
    (∑ i : Fin (n+1), (-1 : R)^i.val • GradedChart.restrict G y hy
      (ActualCech.intersection_delete a i) t (f (a ∘ i.succAbove))) = _
  simp only [map_sum,map_smul,mapTerm_naturality]
  rfl

end Lech.ImageCech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_AlternatingCechUnaugmentedComplex
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.ProductSourceCover
open AddMonoidAlgebra
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ)


def ringSections (m : Fin n → ℤ) (s : Finset (Chart n)) : Submodule R (Ambient R n) :=
  (sections R n m s).comap (coeffLinearEquiv R).toLinearMap
lemma ringSections_mem (m : Fin n → ℤ) (s : Finset (Chart n)) (x : Ambient R n) :
    x∈ringSections R n m s ↔ ∀ e∈x.coeff.support,allowed n m s e := by
  exact Finsupp.mem_supported R x.coeff
lemma single_mem (m : Fin n → ℤ) (s : Finset (Chart n)) (e : Exponent n) (r : R)
    (he : allowed n m s e) : single e r∈ringSections R n m s := by
  rw [ringSections_mem]
  intro f hf
  have hfe : f=e := Finset.mem_singleton.mp (Finsupp.support_single_subset hf)
  exact hfe ▸ he
lemma mul_mem (m k : Fin n → ℤ) (s : Finset (Chart n)) (x y : Ambient R n)
    (hx : x∈ringSections R n m s) (hy : y∈ringSections R n k s) :
    x*y∈ringSections R n (m+k) s := by
  rw [mul_def]
  apply (ringSections R n (m+k) s).sum_mem
  intro e he
  apply (ringSections R n (m+k) s).sum_mem
  intro f hf
  exact single_mem R n (m+k) s (e+f) _
    (allowed_add n m k s e f ((ringSections_mem R n m s x).mp hx e he)
      ((ringSections_mem R n k s y).mp hy f hf))
lemma one_mem (s : Finset (Chart n)) : (1:Ambient R n)∈ringSections R n 0 s := by
  rw [one_def]
  apply single_mem
  intro i
  exact ⟨fun _ => le_refl _,fun _ => le_refl _⟩
lemma pow_mem (m : Fin n → ℤ) (s : Finset (Chart n)) (x : Ambient R n)
    (hx : x∈ringSections R n m s) (N : ℕ) : x^N∈ringSections R n (N • m) s := by
  induction N with
  | zero => simpa only [pow_zero,zero_smul] using one_mem R n s
  | succ N ih =>
    simpa only [pow_succ,succ_nsmul] using mul_mem R n (N • m) m s (x^N) x ih hx
lemma ringSections_mono (m : Fin n → ℤ) : Monotone (ringSections R n m) := by
  intro s t hst
  exact Submodule.comap_mono (sections_mono R n m hst)


def chartLine (m : Fin n → ℤ) (σ : Chart n) : ProductLinearChart.Ring R n →ₗ[R] Ambient R n :=
  (LinearMap.mulLeft R (ProductLaurent.monomialUnit R n (twistExponent n m σ):Ambient R n)).comp
    (ProductLaurent.chartMap R n σ).toLinearMap
lemma chartLine_monomial (m : Fin n → ℤ) (σ : Chart n) (e : Fin n →₀ ℕ) (r : R) :
    chartLine R n m σ (MvPolynomial.monomial e r)=single (affineExponent n m σ e) r := by
  change single (twistExponent n m σ) 1 * ProductLaurent.chartMap R n σ (MvPolynomial.monomial e r)=_
  rw [ProductLaurent.chartMap_monomial,single_mul_single,one_mul]
  rfl
lemma chartLine_mem (m : Fin n → ℤ) (σ : Chart n) (p : ProductLinearChart.Ring R n) :
    chartLine R n m σ p∈ringSections R n m {σ} := by
  rw [MvPolynomial.as_sum p,map_sum]
  apply (ringSections R n m {σ}).sum_mem
  intro e _
  rw [chartLine_monomial]
  exact single_mem R n m {σ} _ _ (affineExponent_allowed n m σ e)
 

theorem chartLine_range (m : Fin n → ℤ) (σ : Chart n) :
    (chartLine R n m σ).range=ringSections R n m {σ} := by
  apply le_antisymm
  · rintro _ ⟨p,rfl⟩;exact chartLine_mem R n m σ p
  · intro x hx
    refine ⟨∑ e∈x.coeff.support,MvPolynomial.monomial (affineCoordinates n m σ e) (x.coeff e),?_⟩
    rw [map_sum]
    calc
      _ = ∑ e∈x.coeff.support,single e (x.coeff e) := by
        apply Finset.sum_congr rfl
        intro e he
        rw [chartLine_monomial,affineExponent_coordinates n m σ e ((ringSections_mem R n m {σ} x).mp hx e he)]
      _ = x := AddMonoidAlgebra.sum_coeff_single x
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open AddMonoidAlgebra CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
def ringProjector (m : Fin n → ℤ) (σ : Chart n) : Ambient R n →ₗ[R] Ambient R n :=
  (coeffLinearEquiv R).symm.toLinearMap.comp
    ((projector R n m σ).comp (coeffLinearEquiv R).toLinearMap)
lemma ringProjector_coeff (m : Fin n → ℤ) (σ : Chart n) (x : Ambient R n) :
    (ringProjector R n m σ x).coeff=projector R n m σ x.coeff := by
  change (coeffLinearEquiv R) ((coeffLinearEquiv R).symm _)=_
  exact (coeffLinearEquiv R).apply_symm_apply _
lemma ringProjector_sum (m : Fin n → ℤ) (x : Ambient R n) : ∑ σ,ringProjector R n m σ x=x := by
  apply (coeffLinearEquiv R).injective
  change (coeffLinearEquiv R) (∑ σ,ringProjector R n m σ x)=x.coeff
  rw [map_sum]
  simpa only [coeffLinearEquiv_apply,ringProjector_coeff] using projector_sum R n m x.coeff
lemma ringProjector_mem (m : Fin n → ℤ) (hm : ∀ i,-1≤ m i) (s : Finset (Chart n))
    (σ : Chart n) (x : Ambient R n) (hx : x∈ringSections R n m (insert σ s)) :
    ringProjector R n m σ x∈ringSections R n m s := by
  change (ringProjector R n m σ x).coeff∈sections R n m s
  rw [ringProjector_coeff]
  exact projector_mem R n m hm s σ x.coeff hx
 

theorem ring_augmented_acyclic (m : Fin n → ℤ) (hm : ∀ i,-1≤ m i) :
    (AlternatingCech.complex R (Ambient R n) (ringSections R n m) (ringSections_mono R n m)).Acyclic :=
  AlternatingCech.projection_complex_acyclic R (Ambient R n) (ringSections R n m)
    (ringSections_mono R n m) (ringProjector R n m) (ringProjector_sum R n m)
      (ringProjector_mem R n m hm)
theorem ring_sorted_acyclic [LinearOrder (Chart n)] (m : Fin n → ℤ) (hm : ∀ i,-1≤ m i) :
    (AlternatingCech.sortedComplex R (Ambient R n) (ringSections R n m) (ringSections_mono R n m)).Acyclic := by
  intro j
  apply (ring_augmented_acyclic R n m hm j).of_iso
  convert AlternatingCech.cochainsSortedIso R (Ambient R n) (ringSections R n m) (ringSections_mono R n m) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
end Lech.ProductSourceCover
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverOrdinaryPositive
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.ProductSourceCover
open AddMonoidAlgebra Polynomial
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
lemma prod_mem {ι : Type*} (s : Finset ι) (x : ι → Ambient R n) (m : ι → Fin n → ℤ)
    (t : Finset (Chart n)) (h : ∀ i∈s,x i∈ringSections R n (m i) t) :
    (∏ i∈s,x i)∈ringSections R n (∑ i∈s,m i) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty,Finset.sum_empty] using one_mem R n t
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha,Finset.sum_insert ha]
    exact mul_mem R n (m a) (∑ i∈s,m i) t (x a) (∏ i∈s,x i)
      (h a (Finset.mem_insert_self _ _)) (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
lemma prod_variables (s : Finset (Fin n)) :
    (∏ i∈s,(ProductLaurent.variableUnit R n i:Ambient R n))=single (subsetExponent n s) (1:R) := by
  induction s using Finset.induction_on with
  | empty => simp [subsetExponent,←one_def]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha,subsetExponent,Finset.sum_insert ha,ih]
    change single (Finsupp.single a 1) 1 * single (subsetExponent n s) (1:R)=_
    rw [single_mul_single,one_mul]
    rfl
lemma polynomial_subproduct (s : Finset (Fin n)) :
    (∏ i∈s,(C (ProductLaurent.variableUnit R n i:Ambient R n)*Polynomial.X))=
      C (∏ i∈s,(ProductLaurent.variableUnit R n i:Ambient R n))*Polynomial.X^s.card := by
  rw [Finset.prod_mul_distrib,←map_prod]
  simp only [Finset.prod_const]
lemma subproduct_coeff_mem (s : Finset (Fin n)) (k : ℕ) :
    (∏ i∈s,(C (ProductLaurent.variableUnit R n i:Ambient R n)*Polynomial.X)).coeff k∈
      ringSections R n (fun _ => 1) ∅ := by
  rw [polynomial_subproduct,coeff_C_mul,coeff_X_pow,prod_variables]
  split_ifs
  · rw [mul_one];exact single_mem R n _ _ _ _ (subsetExponent_allowed n s)
  · rw [mul_zero];exact (ringSections R n _ _).zero_mem
 

lemma coefficient_mem (k : ℕ) : (ProductLaurent.binaryForm R n).coeff k∈
    ringSections R n (fun _ => 1) ∅ := by
  rw [ProductLaurent.binaryForm,Finset.prod_add_one,finsetSum_coeff]
  apply (ringSections R n _ _).sum_mem
  intro s _
  exact subproduct_coeff_mem R n s k
 

lemma coefficient_product_mem (s : Finset (Fin (n+1))) :
    (∏ k∈s,(ProductLaurent.binaryForm R n).coeff k)∈ringSections R n (fun _ => (s.card:ℤ)) ∅ := by
  have h := prod_mem R n s (fun k : Fin (n+1) => (ProductLaurent.binaryForm R n).coeff k)
    (fun _ _ => (1:ℤ)) ∅ (fun k _ => coefficient_mem R n k)
  have he : (∑ _∈s,fun _ : Fin n => (1:ℤ))=(fun _ : Fin n => (s.card:ℤ)) := by
    ext i
    simp
  rwa [he] at h
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open AddMonoidAlgebra
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
lemma multiply_level (m : Fin n → ℤ) (d N K : ℕ) (t : Finset (Chart n))
    (q x : Ambient R n) (hq : q∈ringSections R n (fun _ => (d:ℤ)) ∅)
    (hx : x∈ringSections R n (levelTwist n m d N) t) :
    q^K*x∈ringSections R n (levelTwist n m d (N+K)) t := by
  have hpow := pow_mem R n (fun _ => (d:ℤ)) t q
    ((ringSections_mono R n _ (Finset.empty_subset t)) hq) K
  have h := mul_mem R n (K • fun _ => (d:ℤ)) (levelTwist n m d N) t _ x hpow hx
  have he : (K • fun _ : Fin n => (d:ℤ))+levelTwist n m d N=levelTwist n m d (N+K) := by
    ext i
    change (K • (d:ℤ))+(m i+(N:ℤ)*(d:ℤ))=m i+((N+K:ℕ):ℤ)*(d:ℤ)
    rw [nsmul_eq_mul,Nat.cast_add]
    ring
  rwa [he] at h


end Lech.ProductSourceCover
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverHighThreshold
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.ProductSourceCover
open AddMonoidAlgebra CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
lemma chartUnit_inv_section (σ : Chart n) :
    (↑((ProductLaurent.chartUnit R n σ)⁻¹):Ambient R n)∈ringSections R n (fun _ => -1) {σ} := by
  rw [chartUnit_monomial,←ProductLaurent.monomialUnit_neg]
  change single (-(twistExponent n (fun _ => 1) σ)) (1:R)∈_
  apply single_mem
  intro i
  simp only [Finsupp.neg_apply,twistExponent_apply]
  cases hs : σ i <;> simp [hs]
lemma chartMap_zero_section (σ : Chart n) (a : ProductLinearChart.Ring R n) :
    ProductLaurent.chartMap R n σ a∈ringSections R n 0 {σ} := by
  have he : twistExponent n 0 σ=0 := by ext i;simp [twistExponent_apply]
  have h := chartLine_mem R n 0 σ a
  change (ProductLaurent.monomialUnit R n (twistExponent n 0 σ):Ambient R n)*ProductLaurent.chartMap R n σ a∈_ at h
  rw [he] at h
  simpa only [ProductLaurent.monomialUnit,←one_def,one_mul] using h

end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
 

def sourceCech (m : Fin n → ℤ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  AlternatingCech.unaugmentedComplex R (Ambient R n) (ringSections R n m) (ringSections_mono R n m)

end Lech.ProductSourceCover
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechHomogeneousEval
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.ProductSourceCover

section

section
open AddMonoidAlgebra
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
lemma chartLine_level (m : Fin n → ℤ) (σ : Chart n) (N : ℕ) (a : ProductLinearChart.Ring R n) :
    chartLine R n (levelTwist n m 1 N) σ a=
      (ProductLaurent.chartUnit R n σ:Ambient R n)^N*chartLine R n m σ a := by
  change (ProductLaurent.monomialUnit R n (twistExponent n (levelTwist n m 1 N) σ):Ambient R n)*_= _
  rw [twistExponent_level,ProductLaurent.monomialUnit_add,monomialUnit_nsmul,←chartUnit_monomial]
  simp only [Units.val_mul,Units.val_pow_eq_pow_val,AlgHom.toLinearMap_apply]
  change _=(ProductLaurent.chartUnit R n σ:Ambient R n)^N*
    ((ProductLaurent.monomialUnit R n (twistExponent n m σ):Ambient R n)*ProductLaurent.chartMap R n σ a)
  ring

end


open Polynomial
universe u
end


universe u
end Lech.ProductSourceCover


namespace Lech.UniversalSplitting
open Polynomial
universe u

attribute [instance] Data.ring Data.algebra


end Lech.UniversalSplitting

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootCoactionT
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.RootInvariants
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))

attribute [local instance] OAI.Lech.RootInvariants.instAlgebraS
attribute [local instance] OAI.Lech.RootInvariants.instIsScalarTowerS
lemma member_eq (ms : Fin n → ℤ) (x : module f n hn t v hv d ms) :
    (RootCoaction.weight f n hn t v hv d ms : RootCoaction.T f n t v d)*
      RootCoaction.hom f n hn t v hv d (x:d.S)=RootCoaction.right f n t v d (x:d.S) :=
  x.property

end Lech.RootInvariants

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootInvariantsWeightZero
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.RootInvariants

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


section
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))

attribute [local instance] OAI.Lech.RootInvariants.weightZeroOverAlgebra
attribute [local instance] OAI.Lech.RootInvariants.weightZeroOverScalarTower
def overAlgebra (ms : Fin n → ℤ) : Submodule (algebra f n hn t v hv d) d.S where
  carrier := module f n hn t v hv d ms
  zero_mem' := (module f n hn t v hv d ms).zero_mem
  add_mem' := (module f n hn t v hv d ms).add_mem
  smul_mem' a x hx := by
    change (RootCoaction.weight f n hn t v hv d ms : RootCoaction.T f n t v d)*
      RootCoaction.hom f n hn t v hv d ((a:d.S)*x)=RootCoaction.right f n t v d ((a:d.S)*x)
    have ha : RootCoaction.hom f n hn t v hv d (a:d.S)=RootCoaction.right f n t v d (a:d.S) := a.property
    change (RootCoaction.weight f n hn t v hv d ms : RootCoaction.T f n t v d)*
      RootCoaction.hom f n hn t v hv d x=RootCoaction.right f n t v d x at hx
    rw [map_mul,map_mul,ha,← mul_assoc,mul_comm _ (RootCoaction.right f n t v d (a:d.S)),mul_assoc,hx]

def overAlgebraEquiv (ms : Fin n → ℤ) :
    overAlgebra f n hn t v hv d ms ≃ₗ[A] module f n hn t v hv d ms :=
  LinearEquiv.refl A _


end


section
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))

attribute [local instance] OAI.Lech.RootInvariants.weightZeroSectionsAlgebra
lemma weight_single (i : Fin n) : RootCoaction.weight f n hn t v hv d (Pi.single i (1:ℤ))=
    RootCoaction.denominator f n hn t v hv d i := by
  classical
  rw [RootCoaction.weight_eq]
  simp [Pi.single_apply]

local instance weightZeroSectionsScalarTower_r93646d_1 : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
lemma denominator_hom_root (i : Fin n) :
    (RootCoaction.denominator f n hn t v hv d i : RootCoaction.T f n t v d)*
      RootCoaction.hom f n hn t v hv d (d.roots i)=RootCoaction.roots f n t v d i := by
  rw [RootCoaction.hom_root,RootGluing.rootShift,
    ← RootCoaction.denominator_val f n hn t v hv d i,Ring.inverse_unit]
  rw [mul_comm _ (RootCoaction.roots f n t v d i*_),mul_assoc,Units.inv_mul,mul_one]


def sectionX (i : Fin n) : overAlgebra f n hn t v hv d (Pi.single i (1:ℤ)) :=
  ⟨-d.roots i, by
    change (RootCoaction.weight f n hn t v hv d (Pi.single i (1:ℤ)) : RootCoaction.T f n t v d)*
      RootCoaction.hom f n hn t v hv d (-d.roots i)=RootCoaction.right f n t v d (-d.roots i)
    rw [weight_single,map_neg,map_neg,mul_neg,denominator_hom_root]
    rfl⟩

 
def sectionY (i : Fin n) : overAlgebra f n hn t v hv d (Pi.single i (1:ℤ)) :=
  ⟨1+algebraMap B d.S t*d.roots i, by
    change (RootCoaction.weight f n hn t v hv d (Pi.single i (1:ℤ)) : RootCoaction.T f n t v d)*
      RootCoaction.hom f n hn t v hv d (1+algebraMap B d.S t*d.roots i)=
        RootCoaction.right f n t v d (1+algebraMap B d.S t*d.roots i)
    simp only [weight_single,map_add,map_one,map_mul,AlgHom.commutes]
    change (RootCoaction.denominator f n hn t v hv d i : RootCoaction.T f n t v d)*
      (1+algebraMap B (RootCoaction.T f n t v d) t*RootCoaction.hom f n hn t v hv d (d.roots i))=
        1+RootCoaction.coord f n t v d*RootCoaction.roots f n t v d i
    calc
      _ = (RootCoaction.denominator f n hn t v hv d i : RootCoaction.T f n t v d)+
          algebraMap B (RootCoaction.T f n t v d) t*
            ((RootCoaction.denominator f n hn t v hv d i : RootCoaction.T f n t v d)*
              RootCoaction.hom f n hn t v hv d (d.roots i)) := by ring
      _ = _ := by rw [denominator_hom_root,RootCoaction.denominator_val];ring⟩

end


section
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))

attribute [local instance] OAI.Lech.RootInvariants.weightZeroDiagonalAlgebra
lemma leftUnit_eq : Units.map (algebraMap B (RootCoaction.T f n t v d)).toMonoidHom v=
    RootCoaction.unit f n t v d*RootCoaction.weight f n hn t v hv d (fun _ => (1:ℤ)) := by
  apply Units.ext
  simp only [Units.coe_map,Units.val_mul,RootCoaction.weight_eq,zpow_one,Units.coe_prod]
  have h := RootTransitions.value_product
    ((f.map (algebraMap A B)).map (algebraMap B (RootCoaction.T f n t v d)))
    ((natDegree_map_le.trans natDegree_map_le).trans hn)
    (RootCoaction.coord f n t v d) (algebraMap B (RootCoaction.T f n t v d) t)
    (RootCoaction.unit f n t v d) (RootCoaction.roots f n t v d) (RootCoaction.factorization f n t v d)
  have he := RootTransport.mapped_eval (f.map (algebraMap A B)) t v hv
    (C := RootCoaction.T f n t v d)
  rw [he] at h
  simpa only [RootCoaction.denominator_val, Units.coe_map] using h


end


open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))


attribute [local instance] OAI.Lech.RootInvariants.weightZeroProductSectionAlgebra
def selected (σ : Fin n → Bool) (i : Fin n) :
    overAlgebra f n hn t v hv d (Pi.single i (1:ℤ)) :=
  if σ i then sectionX f n hn t v hv d i else sectionY f n hn t v hv d i


local instance weightZeroProductSectionScalarTower_r93646d_1 : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
def productSection (σ : Fin n → Bool) :
    overAlgebra f n hn t v hv d (fun _ => (1:ℤ)) :=
  ⟨∏ i,(selected f n hn t v hv d σ i:d.S),by
    change (RootCoaction.weight f n hn t v hv d (fun _ => (1:ℤ)):RootCoaction.T f n t v d)*
      RootCoaction.hom f n hn t v hv d (∏ i,(selected f n hn t v hv d σ i:d.S))=
        RootCoaction.right f n t v d (∏ i,(selected f n hn t v hv d σ i:d.S))
    simp only [RootCoaction.weight_eq,zpow_one,Units.coe_prod,map_prod,← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    have hx := (selected f n hn t v hv d σ i).property
    change (RootCoaction.weight f n hn t v hv d (Pi.single i (1:ℤ)):RootCoaction.T f n t v d)*
      RootCoaction.hom f n hn t v hv d (selected f n hn t v hv d σ i:d.S)=
        RootCoaction.right f n t v d (selected f n hn t v hv d σ i:d.S) at hx
    rw [weight_single] at hx
    exact hx⟩


def chartFunction (σ : Fin n → Bool) : algebra f n hn t v hv d :=
  ⟨algebraMap B d.S (v:B)*(productSection f n hn t v hv d σ:d.S),by
    change RootCoaction.hom f n hn t v hv d _=RootCoaction.right f n t v d _
    rw [map_mul,map_mul,AlgHom.commutes]
    have hu := congrArg (fun u : (RootCoaction.T f n t v d)ˣ => (u:RootCoaction.T f n t v d))
      (leftUnit_eq f n hn t v hv d)
    change algebraMap B (RootCoaction.T f n t v d) (v:B)=
      RootCoaction.right f n t v d (algebraMap B d.S (v:B))*
        (RootCoaction.weight f n hn t v hv d (fun _ => (1:ℤ)):RootCoaction.T f n t v d) at hu
    rw [hu,mul_assoc]
    exact congrArg (_ * ·) (member_eq f n hn t v hv d _
      (overAlgebraEquiv f n hn t v hv d _ (productSection f n hn t v hv d σ)))⟩

end Lech.RootInvariants

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_StandardFactorChartsL
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.RootInvariants
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))

attribute [local instance] OAI.Lech.RootInvariants.instAlgebraS_1
abbrev chartRing (σ : Fin n → Bool) :=
  StandardFactorCharts.L (algebra f n hn t v hv d) n (chartFunction f n hn t v hv d) σ

def chartCoordinate (σ : Fin n → Bool) (i : Fin n) (b : Bool) : chartRing f n hn t v hv d σ :=
  StandardFactorCharts.coordinate (algebra f n hn t v hv d) n (chartFunction f n hn t v hv d) σ i b

def chartUnit (σ : Fin n → Bool) : (chartRing f n hn t v hv d σ)ˣ :=
  StandardFactorCharts.chartUnit (algebra f n hn t v hv d) n (chartFunction f n hn t v hv d) σ

end Lech.RootInvariants


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_NativeDescentCanonicalAlg
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.UniversalFactorMap
open Polynomial Lech.FactorDescent
open scoped TensorProduct
universe u
variable {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
  [Algebra A B] [Algebra A T]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
variable (w : Tˣ) (a b : Fin n → T)
  (hf : (f.map (algebraMap A T)).homogenize n=MvPolynomial.C (w:T)*∏ i,
    (MvPolynomial.C (a i)*MvPolynomial.X 0+MvPolynomial.C (b i)*MvPolynomial.X 1))

lemma factorization :
    (BinaryChange.normalized (f.map (algebraMap A B)) n t v).map (algebraMap B (R (A := A) (B := B) (T := T)))=
      ∏ i,(Polynomial.X-C (-includeT (a i)*((denominator f n hn t v hv w a b hf i)⁻¹).val)) := by
  rw [BinaryCover.map_normalized]
  exact FactorNormalization.normalized_factorization _ _ _ _ _ _ _ _ _ _

 

local instance instAlgebraS_r93646d_1 : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
def splittingMap : d.S →ₐ[B] R (A := A) (B := B) (T := T) :=
  (d.universal _ _ (factorization f n hn t v hv w a b hf)).choose

lemma splittingMap_root (i : Fin n) : splittingMap f n hn t v hv d w a b hf (d.roots i)=
    -includeT (a i)*((denominator f n hn t v hv w a b hf i)⁻¹).val :=
  (d.universal _ _ (factorization f n hn t v hv w a b hf)).choose_spec.1 i

 

def map [Module.FaithfullyFlat A B] : RootInvariants.algebra f n hn t v hv d →ₐ[A] T :=
  descended f n hn t v hv d (splittingMap f n hn t v hv d w a b hf) a b
    (denominator f n hn t v hv w a b hf) (denominator_val f n hn t v hv w a b hf)
    (splittingMap_root f n hn t v hv d w a b hf)

lemma map_include [Module.FaithfullyFlat A B] (x : RootInvariants.algebra f n hn t v hv d) :
    includeT (map f n hn t v hv d w a b hf x)=splittingMap f n hn t v hv d w a b hf (x:d.S) :=
  descended_include f n hn t v hv d _ _ _ _ _ _ x
end Lech.UniversalFactorMap


namespace Lech.UniversalFactorMap
open Polynomial Lech.FactorDescent
open scoped TensorProduct
universe u
variable {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
  [Algebra A B] [Algebra A T]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
variable (w : Tˣ) (a b : Fin n → T)
  (hf : (f.map (algebraMap A T)).homogenize n=MvPolynomial.C (w:T)*∏ i,
    (MvPolynomial.C (a i)*MvPolynomial.X 0+MvPolynomial.C (b i)*MvPolynomial.X 1))

local instance instAlgebraS_1_r93646d_1 : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
lemma recover_selected (σ : Fin n → Bool) (i : Fin n) :
    (denominator f n hn t v hv w a b hf i:R (A := A) (B := B) (T := T))*
      splittingMap f n hn t v hv d w a b hf (RootInvariants.selected f n hn t v hv d σ i:d.S)=
        includeT (if σ i then a i else b i) := by
  let μ := denominator f n hn t v hv w a b hf i
  have hμ : (μ:R (A := A) (B := B) (T := T))=algebraMap B _ t*includeT (a i)+includeT (b i) :=
    denominator_val f n hn t v hv w a b hf i
  have hx : (μ:R (A := A) (B := B) (T := T))*
      (-splittingMap f n hn t v hv d w a b hf (d.roots i))=includeT (a i) := by
    rw [splittingMap_root]
    change (μ:R (A := A) (B := B) (T := T))*(-(-includeT (a i)*(μ⁻¹).val))=includeT (a i)
    simp only [neg_mul,neg_neg]
    rw [mul_left_comm,Units.mul_inv,mul_one]
  simp only [RootInvariants.selected]
  split_ifs
  · change (μ:R (A := A) (B := B) (T := T))*splittingMap f n hn t v hv d w a b hf (-d.roots i)=_
    rw [map_neg]
    exact hx
  · change (μ:R (A := A) (B := B) (T := T))*splittingMap f n hn t v hv d w a b hf
      (1+algebraMap B d.S t*d.roots i)=_
    rw [map_add,map_one,map_mul,AlgHom.commutes]
    calc
      _ = (μ:R (A := A) (B := B) (T := T))-algebraMap B _ t*((μ:R (A := A) (B := B) (T := T))*
        (-splittingMap f n hn t v hv d w a b hf (d.roots i))) := by ring
      _ = includeT (b i) := by rw [hx,hμ];ring

 

lemma map_chartFunction [Module.FaithfullyFlat A B] (σ : Fin n → Bool) :
    map f n hn t v hv d w a b hf (RootInvariants.chartFunction f n hn t v hv d σ)=
      (w:T)*∏ i,if σ i then a i else b i := by
  apply includeT_injective (A := A) (B := B)
  rw [map_include]
  change splittingMap f n hn t v hv d w a b hf
    (algebraMap B d.S (v:B)*∏ i,(RootInvariants.selected f n hn t v hv d σ i:d.S))=_
  rw [map_mul,map_prod,AlgHom.commutes]
  have hvv := congrArg (fun u : (R (A := A) (B := B) (T := T))ˣ => (u:R (A := A) (B := B) (T := T)))
    (denominator_product f n hn t v hv w a b hf)
  simp only [Units.val_mul,Units.coe_map,Units.coe_prod] at hvv
  change includeT (w:T)*∏ i,(denominator f n hn t v hv w a b hf i:R (A := A) (B := B) (T := T))=
    algebraMap B (R (A := A) (B := B) (T := T)) (v:B) at hvv
  rw [←hvv,mul_assoc,←Finset.prod_mul_distrib]
  simp only [recover_selected,map_mul,map_prod]
end Lech.UniversalFactorMap


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_UniversalFactorMapMapChart
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical
namespace Lech.UniversalFactorMap
open Polynomial Lech.FactorDescent
open scoped TensorProduct
universe u
variable {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
  [Algebra A B] [Algebra A T] [Module.FaithfullyFlat A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
variable (σ : Fin n → Bool) (w : Tˣ) (a b : Fin n → T)
  (hf : (f.map (algebraMap A T)).homogenize n=MvPolynomial.C (w:T)*∏ i,
    (MvPolynomial.C (a i)*MvPolynomial.X 0+MvPolynomial.C (b i)*MvPolynomial.X 1))
  (hs : ∀ i,(if σ i then a i else b i)=1)

local instance mapChartAlgebra_r93646d_1 : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
include hs in
lemma map_chart_selected : map f n hn t v hv d w a b hf (RootInvariants.chartFunction f n hn t v hv d σ)=(w:T) := by
  rw [map_chartFunction]
  simp only [hs,Finset.prod_const_one,mul_one]

 

def chartMap : RootInvariants.chartRing f n hn t v hv d σ →ₐ[A] T :=
  IsLocalization.Away.liftAlgHom (RootInvariants.chartFunction f n hn t v hv d σ)
    (f := map f n hn t v hv d w a b hf)
    (by rw [map_chart_selected f n hn t v hv d σ w a b hf hs];exact w.isUnit)

lemma chartMap_from (x : RootInvariants.algebra f n hn t v hv d) :
    chartMap f n hn t v hv d σ w a b hf hs
      (algebraMap (RootInvariants.algebra f n hn t v hv d) (RootInvariants.chartRing f n hn t v hv d σ) x)=
        map f n hn t v hv d w a b hf x := by
  exact IsLocalization.Away.lift_eq (S := RootInvariants.chartRing f n hn t v hv d σ)
    (g := (map f n hn t v hv d w a b hf).toRingHom)
    (RootInvariants.chartFunction f n hn t v hv d σ)
    (by change IsUnit (map f n hn t v hv d w a b hf (RootInvariants.chartFunction f n hn t v hv d σ))
        rw [map_chart_selected f n hn t v hv d σ w a b hf hs]
        exact w.isUnit) x

lemma chartMap_unit : Units.map (chartMap f n hn t v hv d σ w a b hf hs).toMonoidHom
    (RootInvariants.chartUnit f n hn t v hv d σ)=w := by
  apply Units.ext
  change chartMap f n hn t v hv d σ w a b hf hs
    (StandardFactorCharts.chartUnit (RootInvariants.algebra f n hn t v hv d) n
      (RootInvariants.chartFunction f n hn t v hv d) σ:RootInvariants.chartRing f n hn t v hv d σ)=(w:T)
  rw [StandardFactorCharts.chartUnit_val,chartMap_from,map_chart_selected f n hn t v hv d σ w a b hf hs]



lemma chartMap_coordinate (i : Fin n) (κ : Bool) :
    chartMap f n hn t v hv d σ w a b hf hs (RootInvariants.chartCoordinate f n hn t v hv d σ i κ)=
      if κ then a i else b i := by
  have hinv : chartMap f n hn t v hv d σ w a b hf hs
      ((RootInvariants.chartUnit f n hn t v hv d σ)⁻¹).val=(w⁻¹).val := by
    have h := congrArg (fun u : Tˣ => (u⁻¹).val) (chartMap_unit f n hn t v hv d σ w a b hf hs)
    exact h
  change chartMap f n hn t v hv d σ w a b hf hs
    (algebraMap (RootInvariants.algebra f n hn t v hv d) (RootInvariants.chartRing f n hn t v hv d σ)
      (RootInvariants.chartFunction f n hn t v hv d (Function.update σ i κ))*
        ((RootInvariants.chartUnit f n hn t v hv d σ)⁻¹).val)=_
  rw [map_mul,chartMap_from,map_chartFunction,update_product n σ a b hs,hinv]
  rw [mul_right_comm,Units.mul_inv,one_mul]
end Lech.UniversalFactorMap


namespace Lech.RootChartAtlas
open Polynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
variable (σ : Fin n → Bool)
abbrev L := RootInvariants.chartRing (f R n k) n (hn R n k) t v hv d σ
abbrev coordinate := RootInvariants.chartCoordinate (f R n k) n (hn R n k) t v hv d σ

variable [Module.FaithfullyFlat (A R n k) B]

def toH : L R n k t v hv d σ →ₐ[A R n k] H R n k σ :=
  UniversalFactorMap.chartMap (f R n k) n (hn R n k) t v hv d σ
    ((ProductLinearChart.denominator R n σ k)⁻¹)
    (fun i => algebraMap (ProductLinearChart.Ring R n) (H R n k σ) (ProductLinearChart.a R n σ i))
    (fun i => algebraMap (ProductLinearChart.Ring R n) (H R n k σ) (ProductLinearChart.b R n σ i))
    (ProductLinearChart.target_factorization R n σ k)
    (source_selected R n k σ)

lemma toH_coordinate (i : Fin n) (b : Bool) :
    toH R n k t v hv d σ (coordinate R n k t v hv d σ i b)=
      if b then algebraMap (ProductLinearChart.Ring R n) (H R n k σ) (ProductLinearChart.a R n σ i)
        else algebraMap (ProductLinearChart.Ring R n) (H R n k σ) (ProductLinearChart.b R n σ i) :=
  UniversalFactorMap.chartMap_coordinate (f R n k) n (hn R n k) t v hv d σ _ _ _ _ _ i b

end Lech.RootChartAtlas
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechFactorizationMap
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.RootChartAtlas


open Polynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
variable [Module.FaithfullyFlat (A R n k) B]
abbrev q := RootInvariants.chartFunction (f R n k) n (hn R n k) t v hv d
end Lech.RootChartAtlas


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_GradedLineBasisHasBasis
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.RootInvariants
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
variable (σ : Fin n → Bool)
attribute [local instance] OAI.Lech.RootInvariants.gradedLineBasisAlgebra
abbrev chartExtension := chartRing f n hn t v hv d σ ⊗[algebra f n hn t v hv d] d.S

end Lech.RootInvariants


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CechReduction
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] {ι : Type} [Fintype ι] [LinearOrder ι]
variable (D : Diagram R ι) (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R)

variable (I : Ideal R)


def reductionPositiveIso :
    ((TensorIdeal.quotientFunctor I).mapHomologicalComplex (.up ℕ)).obj (positiveComplex D) ≅
      positiveComplex (reduction D I) :=
  Hom.isoOfComponents (fun q => (TensorIdeal.quotientPiEquiv I
    (fun s : Set.powersetCard ι (q+1) => D.obj s.val)).toModuleIso) (by
      intro q r h
      obtain rfl : q+1=r := h
      rw [positiveComplex_d]
      change _ ≫ ModuleCat.ofHom (d (reduction D I) (q+1)) =
        (TensorIdeal.quotientFunctor I).map ((positiveComplex D).d q (q+1)) ≫ _
      rw [positiveComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      induction x using Submodule.Quotient.induction_on with
      | _ x => exact (quotientPiEquiv_d D I (q+1) x).symm)


end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealFilteredRows
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.IdealFiltered
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))


instance rowFunctor_additive (p : ℤ) : (rowFunctor I F h s hd p).Additive := by
  unfold rowFunctor
  infer_instance

variable {ι : Type*} {c : ComplexShape ι} (K L : HomologicalComplex (ModuleCat.{u} R) c)
  (p : ℤ) [Module.Flat R (F.X p)] (f : K ⟶ L)
  (hr : ∀ q,(f.f q).hom.range=I^(order h s p) • (⊤ : Submodule R (L.X q)))
  (hi : ∀ q,Function.Injective (f.f q).hom)

def rowTermEquiv (q : ι) :
    ((F.X p) ⊗[R] (K.X q)) ≃ₗ[R] (rowFunctor I F h s hd p).obj (L.X q) :=
  TensorIdeal.equiv I (f.f q).hom (order h s p) (hr q) (F.X p) (hi q)

lemma rowTermEquiv_natural (q r : ι) (x : (F.X p) ⊗[R] (K.X q)) :
    ((rowFunctor I F h s hd p).map (L.d q r)).hom
      (rowTermEquiv I F h s hd K L p f hr hi q x) =
    rowTermEquiv I F h s hd K L p f hr hi r
      ((K.d q r).hom.lTensor (F.X p) x) := by
  apply Subtype.ext
  change (L.d q r).hom.lTensor (F.X p) ((f.f q).hom.lTensor (F.X p) x) =
    (f.f r).hom.lTensor (F.X p) ((K.d q r).hom.lTensor (F.X p) x)
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul a b =>
      simp only [LinearMap.lTensor_tmul]
      congr 1
      exact congrArg (fun g : K.X q ⟶ L.X r => g.hom b) (f.comm q r)

 
def rowIso :
    (((curriedTensor (ModuleCat.{u} R)).obj (F.X p)).mapHomologicalComplex c).obj K ≅
      ((rowFunctor I F h s hd p).mapHomologicalComplex c).obj L :=
  Hom.isoOfComponents (fun q => (rowTermEquiv I F h s hd K L p f hr hi q).toModuleIso) (by
    intro q r hqr
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact rowTermEquiv_natural I F h s hd K L p f hr hi q r x)

end Lech.IdealFiltered

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealFilteredLayers
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.IdealFiltered
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (p : ℤ) {M N : ModuleCat.{u} R} (f : M ⟶ N)

lemma rowMap_eq :
    ((rowFunctor I F h s hd p).map f).hom =
      TensorIdeal.restrictIdeal (I^(order h s p)) (f.hom.lTensor (F.X p)) := rfl

lemma rowMap_range (hf : f.hom.range=I • (⊤ : Submodule R N)) :
    ((rowFunctor I F h s hd p).map f).hom.range =
      I • (⊤ : Submodule R ((rowFunctor I F h s hd p).obj N)) := by
  rw [rowMap_eq]
  apply TensorIdeal.restrictIdeal_range
  simpa only [pow_one] using TensorIdeal.range_lTensor I f.hom 1
    (by simpa only [pow_one] using hf) (F.X p)

end Lech.IdealFiltered

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealFilteredQuotient
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.IdealFiltered
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ,(F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))

lemma quotientMap_id (Q : ModuleCat.{u} R) :
    quotientMap I F h s hd (𝟙 Q)=𝟙 (quotientComplex I F h s hd Q) := by
  apply Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      change Submodule.Quotient.mk ((F.X p ◁ 𝟙 Q).hom x)=Submodule.Quotient.mk x
      rw [whiskerLeft_id]
      rfl

lemma quotientMap_comp {Q Q' Q'' : ModuleCat.{u} R} (f : Q ⟶ Q') (g : Q' ⟶ Q'') :
    quotientMap I F h s hd (f ≫ g)=quotientMap I F h s hd f ≫ quotientMap I F h s hd g := by
  apply Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      change Submodule.Quotient.mk ((F.X p ◁ (f ≫ g)).hom x)=
        Submodule.Quotient.mk ((F.X p ◁ g).hom ((F.X p ◁ f).hom x))
      rw [whiskerLeft_comp]
      rfl

 
def quotientFunctor : ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj := quotientComplex I F h s hd
  map := quotientMap I F h s hd
  map_id := quotientMap_id I F h s hd
  map_comp := quotientMap_comp I F h s hd

instance quotientFunctor_additive : (quotientFunctor I F h s hd).Additive where
  map_add := by
    intro Q Q' f g
    apply Hom.ext
    funext p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
        change (term I F h s Q' p).mkQ ((F.X p ◁ (f+g)).hom x)=
          (term I F h s Q' p).mkQ ((F.X p ◁ f).hom x)+(term I F h s Q' p).mkQ ((F.X p ◁ g).hom x)
        rw [show F.X p ◁ (f+g)=F.X p ◁ f+F.X p ◁ g from
          ((curriedTensor (ModuleCat.{u} R)).obj (F.X p)).map_add]
        rfl

 
def quotientRowIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (p : ℤ) :
    (((curriedTensor (ModuleCat.{u} R)).obj (F.X p)).mapHomologicalComplex (.up ℤ)).obj
      (((TensorIdeal.quotientFunctor (I^(order h s p))).mapHomologicalComplex (.up ℤ)).obj K) ≅
      (HomologicalComplex₂.flip (((quotientFunctor I F h s hd).mapHomologicalComplex (.up ℤ)).obj K)).X p :=
  (NatIso.mapHomologicalComplex (TensorIdeal.tensorReductionIso (I^(order h s p)) (F.X p)) (.up ℤ)).app K
end Lech.IdealFiltered

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootCoefficientEuler
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace Lech.ProductSourceCover
open AddMonoidAlgebra
universe u
variable (R : Type u) [CommRing R] (n : ℕ)

lemma coordinate_ringSections (i : Fin n) (b : Bool) :
    (if b then (ProductLaurent.variableUnit R n i:Ambient R n) else 1)∈
      ringSections R n (Pi.single i 1) ∅ := by
  classical
  cases b
  · simp only [Bool.false_eq_true,ite_false]
    rw [one_def]
    apply single_mem
    rw [allowed_empty]
    intro j
    by_cases h : i=j <;> simp [h,eq_comm]
  · change single (Finsupp.single i 1) 1∈ringSections R n (Pi.single i 1) ∅
    apply single_mem
    rw [allowed_empty]
    intro j
    by_cases h : i=j <;> simp [h,eq_comm]

end Lech.ProductSourceCover

end

end OAI
end


