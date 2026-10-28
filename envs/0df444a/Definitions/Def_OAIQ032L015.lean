-- Prove2me | Definitions.Def_OAIQ032L015
-- name    : OAIQ032L015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T19:53:20.202485+00:00
-- url     : https://prove2.me/theorems/5982b2be-1575-4884-a6e2-cb3a4709aa11
-- title:
--   Definitions bundle OAIQ032L015 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 168 declarations of OpenAI's Lean: 56 definitions, 6 instances and 106 theorems. The definitions and types are `OAI.Lech.NormalizedLength.Tower.allModuleLength`, `OAI.Lech.NormalizedLength.Tower.torsionLength`, `OAI.Lech.PartialLaurent.negativeIndicator`, `OAI.Lech.PerfectDomainStages.fieldMap`, `OAI.Lech.PerfectDomainStages.originalToStage`, `OAI.Lech.PerfectDomainStages.rootStageFunctor`, `OAI.Lech.PerfectDomainStages.rootToStage`, `OAI.Lech.PerfectDomainStages.stage`, `OAI.Lech.PerfectDomainStages.stageComplex`, `OAI.Lech.PerfectDomainStages.stageFrobeniusIso`, `OAI.Lech.PerfectDomainStages.stageRootIso`, `OAI.Lech.PerfectDomainStages.tensorEquiv`, `OAI.Lech.PerfectDomainStages.tensorMap`, `OAI.Lech.PerfectDomainStages.tensorToStage`, `OAI.Lech.PerfectStages.tensorStageMap`, `OAI.Lech.ProductLaurent.naturalPart`, `OAI.Lech.ProductLaurent.signedExponent`, `OAI.Lech.ProductLaurent.uniformExponent`, `OAI.Lech.ProductLinearChart.chart`, `OAI.Lech.ProductLinearChart.denominator`, `OAI.Lech.ProductLinearChart.eval`, `OAI.Lech.ProductLinearChart.lift`, `OAI.Lech.ProductLinearChart.normalized`, `OAI.Lech.ProductLinearChart.target`, `OAI.Lech.ProductSourceCover.GlobalIndex`, `OAI.Lech.ProductSourceCover.affineCoordinates`, `OAI.Lech.ProductSourceCover.affineExponent`, `OAI.Lech.ProductSourceCover.allowed`, `OAI.Lech.ProductSourceCover.badVertex`, `OAI.Lech.ProductSourceCover.divisorCochains`, `OAI.Lech.ProductSourceCover.divisorInclusion`, `OAI.Lech.ProductSourceCover.endpointProjector`, `OAI.Lech.ProductSourceCover.exponentCons`, `OAI.Lech.ProductSourceCover.exponentInsert`, `OAI.Lech.ProductSourceCover.exponentSlice`, `OAI.Lech.ProductSourceCover.exponentTail`, `OAI.Lech.ProductSourceCover.faceLift`, `OAI.Lech.ProductSourceCover.faceProjection`, `OAI.Lech.ProductSourceCover.faceSlice`, `OAI.Lech.ProductSourceCover.faceVertexMap` and 16 more.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_AlternatingCechPost`, `Multiplicity_AlternatingCechPrismPrimitive`, `Multiplicity_AlternatingCechUnaugmentedComplex`, `Multiplicity_FrobeniusComplexStage`, `Multiplicity_KoszulConeFunctor`, `Multiplicity_LechFactorizationMap`, `Multiplicity_LechHomogeneousEval`, `Multiplicity_LechTorsionOf`, `Multiplicity_NativeDescentCanonicalAlg`, `Multiplicity_OrderedRootBasis`, `Multiplicity_PartialLaurentTotalDegree`, `Multiplicity_PerfectDomainStagesTensorTo`, `Multiplicity_PrincipalCoverRegularRegularMap`, `Multiplicity_ProductSourceCoverAllowedEmpty`, `Multiplicity_ProductSourceCoverFaceSlice`, `Multiplicity_ProductSourceCoverHighThreshold`, `Multiplicity_ProductSourceCoverOrdinaryPositive`, `Multiplicity_ReesRootPositivity`, `Multiplicity_RootChartAtlasGlobalCoefficient`, `Multiplicity_RootOverlap`, `Multiplicity_RootStageQuotient`, `Multiplicity_RootTowerLengthEq`, `Multiplicity_RootTowerRemainderExponent`, `Multiplicity_TowerRestrictedLength`, `Multiplicity_TraceConductorPerfectOrder`, `Multiplicity_TwistedLocalizationPieceMap`, `Multiplicity_UniversalFactorMapMapChart`.
--
--   **Imports.** It imports the published bundle `Def_DuttaDomain`; the bundles `OAIQ032L000`, `OAIQ032L001`, `OAIQ032L002`, `OAIQ032L003`, `OAIQ032L004`, `OAIQ032L006`, `OAIQ032L007` and `OAIQ032L008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ032L021`, `OAIQ032L022` and `OAIQ032L023`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L000
import Definitions.Def_OAIQ032L001
import Definitions.Def_OAIQ032L002
import Definitions.Def_OAIQ032L003
import Definitions.Def_OAIQ032L004
import Definitions.Def_OAIQ032L006
import Definitions.Def_OAIQ032L007
import Definitions.Def_OAIQ032L008

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechTorsionOf
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.PartialLaurent
open AddMonoidAlgebra
universe u
variable (R : Type u) [CommRing R] {h : ℕ} (s : Finset (Fin h))

lemma fromNat_injective : Function.Injective (fromNat s) := by
  intro a b hab
  funext i
  exact Int.natCast_inj.mp (congrArg (fun e : exponents s => e.val i) hab)
lemma toLaurent_injective : Function.Injective (algebraMap (Poly R (h := h)) (Laurent R s)) :=
  mapDomain_injective (fromNat_injective s)
def negativeIndicator : exponents s :=
  ⟨fun i => -(indicator s i : ℤ),by intro i hi; simp [indicator,hi]⟩
lemma indicator_add_negative : fromNat s (indicator s) + negativeIndicator s = 0 := by
  ext i
  simp [fromNat,negativeIndicator]


lemma clear_exponent (e : exponents s) :
    ∃ (n : ℕ) (a : Fin h → ℕ), e + fromNat s (n • indicator s) = fromNat s a := by
  let n := Finset.univ.sup (fun i => (-e.val i).toNat)
  have hb (i : Fin h) : (-e.val i).toNat ≤ n := Finset.le_sup (f := fun i => (-e.val i).toNat) (Finset.mem_univ i)
  have hpos (i : Fin h) : 0 ≤ e.val i + (n : ℤ) * (indicator s i : ℤ) := by
    by_cases hi : i ∈ s
    · simp only [indicator,ite_eq_left hi,Nat.cast_one,mul_one]
      have := hb i
      omega
    · simpa only [indicator,ite_eq_right hi,Nat.cast_zero,mul_zero,add_zero] using e.property i hi
  refine ⟨n,fun i => (e.val i + (n : ℤ) * (indicator s i : ℤ)).toNat,?_⟩
  ext i
  change e.val i + ((n • indicator s) i : ℤ) =
    ((e.val i + (n : ℤ) * (indicator s i : ℤ)).toNat : ℤ)
  rw [Int.toNat_of_nonneg (hpos i)]
  simp [Pi.smul_apply]
end Lech.PartialLaurent

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PartialLaurentTotalDegree
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
namespace Lech.PartialLaurent
open AddMonoidAlgebra HomogeneousLocalization
universe u
variable (R : Type u) [CommRing R] {h : ℕ} (s : Finset (Fin h))
lemma homogeneous_eq_grade (t : ℤ) : homogeneous R s t = laurentGrade R s t := by
  ext x
  rfl
lemma total_fromNat (a : Fin h → ℕ) : totalDegreeInt s (fromNat s a) = totalDegreeNat a := by
  change (∑ i,(a i : ℤ)) = ((∑ i,a i : ℕ) : ℤ)
  simp
lemma total_negative_indicator : totalDegreeInt s (negativeIndicator s) = -(s.card : ℤ) := by
  have hh := congrArg (totalDegreeInt s) (indicator_add_negative s)
  rw [map_add,map_zero,total_fromNat,total_indicator] at hh
  linarith
lemma inverse_denominator_homogeneous (n : ℕ) :
    single (n • negativeIndicator s) (1 : R) ∈ laurentGrade R s (-(n*s.card : ℕ) : ℤ) := by
  have ht : totalDegreeInt s (n • negativeIndicator s) = -(n*s.card : ℕ) := by
    rw [map_nsmul,total_negative_indicator]
    simp
  rw [←ht]
  exact single_mem_gradeBy _ _ _
end Lech.PartialLaurent


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TwistedLocalizationPieceMap
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
namespace Lech.TwistedLocalization
open SetLike Graded
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (G : ℕ → Submodule R A) [GradedAlgebra G]
  {f : A} {d : ℕ} (hf : f ∈ G d)
  (H : ℕ → Submodule R B) [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A), g (r • a) = r • g a)

variable {S D : Type u} [CommRing S] [CommRing D] [Algebra R S]
  [Algebra S D] [Algebra R D] [IsScalarTower R S D]
  (J : ℕ → Submodule S D) {a : D} {k : ℕ}

lemma piece_restrictScalars (t : ℕ) :
    piece (fun n => (J n).restrictScalars R) (f := a) (d := k) t =
      (piece J (f := a) (d := k) t).restrictScalars R := by
  unfold piece
  rw [Submodule.restrictScalars_iSup]
  congr 1

end Lech.TwistedLocalization


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_AlternatingCechPost
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
namespace Lech.UniversalCoefficientChart
open Polynomial
universe u v
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))

def form : (Ring R n k)[X] := Polynomial.ofFn (n+1) (coefficient R n k)

lemma form_coeff (j : Fin (n+1)) : (form R n k).coeff j=coefficient R n k j := by
  exact Polynomial.ofFn_coeff_eq_val_of_lt _ j.isLt
lemma form_degree : (form R n k).natDegree≤n :=
  Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) _)
lemma form_primitive : Ideal.span (Set.range (form R n k).coeff)=⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  apply Ideal.subset_span
  exact ⟨k,(form_coeff R n k k).trans (coefficient_self R n k)⟩

variable {T : Type v} [CommRing T] [Algebra R T]
def eval (c : Fin (n+1) → T) : Ring R n k →ₐ[R] T := MvPolynomial.aeval (fun j => c j)
lemma eval_coefficient (c : Fin (n+1) → T) (hc : c k=1) (j : Fin (n+1)) :
    eval R n k c (coefficient R n k j)=c j := by
  by_cases h : j=k
  · subst j
    simp [coefficient,eval,hc]
  · simp [coefficient,h,eval]

 

lemma eval_form (g : T[X]) (hg : g.natDegree≤n) (hk : g.coeff k=1) :
    (form R n k).map (eval R n k (fun j => g.coeff j)).toRingHom=g := by
  ext j
  rw [Polynomial.coeff_map]
  by_cases hj : j<n+1
  · rw [form_coeff R n k ⟨j,hj⟩]
    exact eval_coefficient R n k (fun j => g.coeff j) hk ⟨j,hj⟩
  · have hj' : n<j := by omega
    rw [coeff_eq_zero_of_natDegree_lt ((form_degree R n k).trans_lt hj'),map_zero,
      coeff_eq_zero_of_natDegree_lt (hg.trans_lt hj')]

lemma ext {φ ψ : Ring R n k →ₐ[R] T}
    (h : ∀ j : Fin (n+1),φ (coefficient R n k j)=ψ (coefficient R n k j)) : φ=ψ := by
  apply MvPolynomial.algHom_ext
  intro j
  simpa only [coefficient_other R n k j] using h j
end Lech.UniversalCoefficientChart


namespace Lech.ProductLinearChart
open Polynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (σ : Fin n → Bool)

lemma selected (i : Fin n) : (if σ i then a R n σ i else b R n σ i)=1 := by
  cases h : σ i <;> simp [a,b,h]

lemma product_degree : (product R n σ).natDegree≤n := by
  change (∏ i : Fin n,(C (a R n σ i)*Polynomial.X+C (b R n σ i))).natDegree≤n
  calc
    (∏ i : Fin n,(C (a R n σ i)*Polynomial.X+C (b R n σ i))).natDegree ≤
      ∑ i : Fin n,(C (a R n σ i)*Polynomial.X+C (b R n σ i)).natDegree := Polynomial.natDegree_prod_le Finset.univ (fun i : Fin n => C (a R n σ i)*Polynomial.X+C (b R n σ i))
    _ ≤ ∑ _ : Fin n,(1:ℕ) := by
      apply Finset.sum_le_sum
      intro i _
      exact linear_degree (a R n σ i) (b R n σ i)
    _ = n := by simp

lemma product_homogenize : (product R n σ).homogenize n=
    ∏ i : Fin n,(MvPolynomial.C (a R n σ i)*MvPolynomial.X 0+
      MvPolynomial.C (b R n σ i)*MvPolynomial.X 1) := by
  have h := homogenize_finsetProd (s := Finset.univ)
    (p := fun i : Fin n => C (a R n σ i)*Polynomial.X+C (b R n σ i)) (n := fun _ => 1)
    (fun i _ => linear_degree _ _)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one,
    product,homogenize_add,homogenize_C_mul,homogenize_X (by omega : (1:ℕ)≠0),
    Nat.sub_self,pow_zero,mul_one,homogenize_C,pow_one] using h

variable (k : Fin (n+1))
 

abbrev chart := Localization.Away ((product R n σ).coeff k)

def denominator : (chart R n σ k)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit ((product R n σ).coeff k)).unit
lemma denominator_val : (denominator R n σ k:chart R n σ k)=
    algebraMap (Ring R n) (chart R n σ k) ((product R n σ).coeff k) :=
  (IsLocalization.Away.algebraMap_isUnit ((product R n σ).coeff k)).unit_spec

def normalized : (chart R n σ k)[X] :=
  C ((denominator R n σ k)⁻¹).val*(product R n σ).map (algebraMap (Ring R n) (chart R n σ k))

lemma normalized_degree : (normalized R n σ k).natDegree≤n :=
  (natDegree_C_mul_le _ _).trans (natDegree_map_le.trans (product_degree R n σ))
lemma normalized_self : (normalized R n σ k).coeff k=1 := by
  rw [normalized,coeff_C_mul,coeff_map,←denominator_val,Units.inv_mul]

def target : UniversalCoefficientChart.Ring R n k →ₐ[R] chart R n σ k :=
  UniversalCoefficientChart.eval R n k (fun j => (normalized R n σ k).coeff j)

lemma target_form : (UniversalCoefficientChart.form R n k).map (target R n σ k).toRingHom=
    normalized R n σ k :=
  UniversalCoefficientChart.eval_form R n k _ (normalized_degree R n σ k) (normalized_self R n σ k)

lemma target_factorization :
    ((UniversalCoefficientChart.form R n k).map (target R n σ k).toRingHom).homogenize n=
      MvPolynomial.C ((denominator R n σ k)⁻¹).val*∏ i : Fin n,
        (MvPolynomial.C (algebraMap (Ring R n) (chart R n σ k) (a R n σ i))*MvPolynomial.X 0+
          MvPolynomial.C (algebraMap (Ring R n) (chart R n σ k) (b R n σ i))*MvPolynomial.X 1) := by
  rw [target_form,normalized,homogenize_C_mul,homogenize_map,product_homogenize]
  simp only [map_prod,map_add,map_mul,MvPolynomial.map_C,MvPolynomial.map_X]

instance targetAlgebra : Algebra (UniversalCoefficientChart.Ring R n k) (chart R n σ k) :=
  (target R n σ k).toRingHom.toAlgebra
instance targetTower :
    @IsScalarTower R (UniversalCoefficientChart.Ring R n k) (chart R n σ k)
      _ (targetAlgebra R n σ k).toSMul _ :=
  letI := targetAlgebra R n σ k
  IsScalarTower.of_algebraMap_eq fun r => ((target R n σ k).commutes r).symm

end Lech.ProductLinearChart


namespace Lech.ProductLinearChart
open Polynomial
universe u
variable (R : Type u) [CommRing R]
lemma rename_a (n : ℕ) (σ : Fin (n+1) → Bool) (i : Fin n) :
    MvPolynomial.rename Fin.succ (a R n (fun j => σ j.succ) i)=a R (n+1) σ i.succ := by
  cases hs : σ i.succ <;> simp [a,hs]
lemma rename_b (n : ℕ) (σ : Fin (n+1) → Bool) (i : Fin n) :
    MvPolynomial.rename Fin.succ (b R n (fun j => σ j.succ) i)=b R (n+1) σ i.succ := by
  cases hs : σ i.succ <;> simp [b,hs]
lemma rename_factor (n : ℕ) (σ : Fin (n+1) → Bool) (i : Fin n) :
    (C (a R n (fun j => σ j.succ) i)*Polynomial.X+C (b R n (fun j => σ j.succ) i)).map
      (MvPolynomial.rename Fin.succ).toRingHom=
    C (a R (n+1) σ i.succ)*Polynomial.X+C (b R (n+1) σ i.succ) := by
  simp only [Polynomial.map_add,Polynomial.map_mul,map_C,map_X]
  change C (MvPolynomial.rename Fin.succ (a R n (fun j => σ j.succ) i))*Polynomial.X+
    C (MvPolynomial.rename Fin.succ (b R n (fun j => σ j.succ) i))=_
  rw [rename_a,rename_b]
lemma product_succ (n : ℕ) (σ : Fin (n+1) → Bool) :
    product R (n+1) σ=(C (a R (n+1) σ 0)*Polynomial.X+C (b R (n+1) σ 0))*
      (product R n (fun i => σ i.succ)).map (MvPolynomial.rename Fin.succ).toRingHom := by
  rw [product,Fin.prod_univ_succ]
  apply congrArg ((C (a R (n+1) σ 0)*Polynomial.X+C (b R (n+1) σ 0))*·)
  rw [product,Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact (rename_factor R n σ i).symm
lemma finSucc_a (n : ℕ) (σ : Fin (n+1) → Bool) :
    MvPolynomial.finSuccEquiv R n (a R (n+1) σ 0)=(if σ 0 then C 1 else Polynomial.X) := by
  cases hs : σ 0 <;> simp [a,hs,MvPolynomial.finSuccEquiv_X_zero]
lemma finSucc_b (n : ℕ) (σ : Fin (n+1) → Bool) :
    MvPolynomial.finSuccEquiv R n (b R (n+1) σ 0)=(if σ 0 then Polynomial.X else C 1) := by
  cases hs : σ 0 <;> simp [b,hs,MvPolynomial.finSuccEquiv_X_zero]
lemma product_succ_coeff_zero (n : ℕ) (σ : Fin (n+1) → Bool) :
    MvPolynomial.finSuccEquiv R n ((product R (n+1) σ).coeff 0)=
      (if σ 0 then Polynomial.X else C 1)*C ((product R n (fun i => σ i.succ)).coeff 0) := by
  rw [product_succ,mul_coeff_zero]
  simp only [coeff_add,coeff_C_mul,coeff_X_zero,mul_zero,coeff_C_zero,zero_add,coeff_map]
  change MvPolynomial.finSuccEquiv R n (b R (n+1) σ 0 * MvPolynomial.rename Fin.succ
    ((product R n (fun i => σ i.succ)).coeff 0))=_
  rw [map_mul,finSucc_b,finSucc_rename]
lemma product_succ_coeff_succ (n : ℕ) (σ : Fin (n+1) → Bool) (j : ℕ) :
    MvPolynomial.finSuccEquiv R n ((product R (n+1) σ).coeff (j+1))=
      (if σ 0 then C 1 else Polynomial.X)*C ((product R n (fun i => σ i.succ)).coeff j)+
      (if σ 0 then Polynomial.X else C 1)*C ((product R n (fun i => σ i.succ)).coeff (j+1)) := by
  rw [product_succ,add_mul,coeff_add,mul_assoc,coeff_C_mul,coeff_X_mul,coeff_C_mul]
  simp only [coeff_map]
  change MvPolynomial.finSuccEquiv R n (a R (n+1) σ 0 * MvPolynomial.rename Fin.succ
    ((product R n (fun i => σ i.succ)).coeff j) + b R (n+1) σ 0 * MvPolynomial.rename Fin.succ
    ((product R n (fun i => σ i.succ)).coeff (j+1)))=_
  rw [map_add,map_mul,map_mul,finSucc_a,finSucc_b,finSucc_rename,finSucc_rename]
 

theorem coefficient_regular (n : ℕ) (σ : Fin n → Bool) (k : Fin (n+1)) :
    IsRegular ((product R n σ).coeff k) := by
  induction n with
  | zero =>
    have hk : k=0 := by apply Fin.ext; omega
    simp only [hk,product,Finset.univ_eq_empty,Finset.prod_empty,Fin.val_zero,coeff_one_zero]
    exact isRegular_one
  | succ n ih =>
    let p := (product R (n+1) σ).coeff k
    have hr : IsRegular (MvPolynomial.finSuccEquiv R n p) := by
      apply isRegular_iff_mem_nonZeroDivisors.mpr
      cases k using Fin.cases with
      | zero =>
        by_cases hs : σ 0=true
        · apply Polynomial.mem_nonzeroDivisors_of_coeff_mem 1
          simpa only [p,Fin.val_zero,product_succ_coeff_zero,hs,↓reduceIte,
            coeff_X_mul,coeff_C_zero] using (ih (fun i => σ i.succ) 0).mem_nonZeroDivisors
        · apply Polynomial.mem_nonzeroDivisors_of_coeff_mem 0
          simpa only [p,Fin.val_zero,product_succ_coeff_zero,hs,↓reduceIte,
            Bool.false_eq_true,C_1,one_mul,coeff_C_zero] using (ih (fun i => σ i.succ) 0).mem_nonZeroDivisors
      | succ k =>
        by_cases hs : σ 0=true
        · apply Polynomial.mem_nonzeroDivisors_of_coeff_mem 0
          simpa only [p,Fin.val_succ,product_succ_coeff_succ,hs,↓reduceIte,C_1,one_mul,
            coeff_add,coeff_X_mul_zero,coeff_C_zero,add_zero] using (ih (fun i => σ i.succ) k).mem_nonZeroDivisors
        · apply Polynomial.mem_nonzeroDivisors_of_coeff_mem 1
          simpa only [p,Fin.val_succ,product_succ_coeff_succ,hs,↓reduceIte,C_1,one_mul,
            Bool.false_eq_true,coeff_add,coeff_X_mul,coeff_C_zero,coeff_C_succ,add_zero] using
            (ih (fun i => σ i.succ) k).mem_nonZeroDivisors
    refine ⟨?_,?_⟩
    · intro x y h
      apply (MvPolynomial.finSuccEquiv R n).injective
      exact hr.left (by simpa only [map_mul] using congrArg (MvPolynomial.finSuccEquiv R n) h)
    · intro x y h
      apply (MvPolynomial.finSuccEquiv R n).injective
      exact hr.right (by simpa only [map_mul] using congrArg (MvPolynomial.finSuccEquiv R n) h)
end Lech.ProductLinearChart
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PrincipalCoverRegularRegularMap
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.ProductLaurent
open AddMonoidAlgebra Polynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ)

def signedExponent (σ : Fin n → Bool) : (Fin n →₀ ℕ) →+ Exponent n where
  toFun e := Finsupp.onFinset e.support (fun i => if σ i then -(e i:ℤ) else (e i:ℤ)) (by
    intro i hi
    by_contra he
    have hei : e i=0 := Finsupp.notMem_support_iff.mp he
    simp [hei] at hi)
  map_zero' := by ext i;simp
  map_add' a b := by
    ext i
    change (if σ i then -((a i+b i:ℕ):ℤ) else ((a i+b i:ℕ):ℤ))=
      (if σ i then -(a i:ℤ) else (a i:ℤ))+(if σ i then -(b i:ℤ) else (b i:ℤ))
    split_ifs <;> push_cast <;> abel
lemma signedExponent_apply (σ : Fin n → Bool) (e : Fin n →₀ ℕ) (i : Fin n) :
    signedExponent n σ e i=(if σ i then -(e i:ℤ) else (e i:ℤ)) := rfl
lemma signedExponent_injective (σ : Fin n → Bool) : Function.Injective (signedExponent n σ) := by
  intro a b h
  ext i
  have hi := congrArg (fun e : Exponent n => e i) h
  simp only [signedExponent_apply] at hi
  cases hs : σ i <;> simp [hs] at hi <;> exact hi


def uniformExponent (N : ℤ) : Exponent n := Finsupp.equivFunOnFinite.symm (fun _ => N)
lemma uniformExponent_apply (N : ℤ) (i : Fin n) : uniformExponent n N i=N := rfl
def naturalPart (e : Exponent n) : Fin n →₀ ℕ := e.mapRange Int.toNat (by rfl)
lemma naturalPart_lift (e : Exponent n) (h : ∀ i,0≤e i) :
    signedExponent n (fun _ => false) (naturalPart n e)=e := by
  ext i
  simp only [signedExponent_apply,Bool.false_eq_true,↓reduceIte,naturalPart,Finsupp.mapRange_apply,
    Int.toNat_of_nonneg (h i)]
end Lech.ProductLaurent


namespace Lech.ProductSourceCover
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
 

def allowed (m : Fin n → ℤ) (s : Finset (Chart n)) (e : Exponent n) : Prop :=
  ∀ i, ((∀ σ∈s,σ i=false) → 0≤e i) ∧ ((∀ σ∈s,σ i=true) → e i≤ m i)
def sections (m : Fin n → ℤ) (s : Finset (Chart n)) : Submodule R (LaurentModule R n) :=
  Finsupp.supported R R {e | allowed n m s e}
lemma allowed_mono (m : Fin n → ℤ) {s t : Finset (Chart n)} (hst : s⊆t) :
    ∀ e,allowed n m s e → allowed n m t e := by
  intro e he i
  exact ⟨fun h => (he i).1 (fun σ hs => h σ (hst hs)),fun h => (he i).2 (fun σ hs => h σ (hst hs))⟩
lemma sections_mono (m : Fin n → ℤ) : Monotone (sections R n m) := by
  intro s t hst
  exact Finsupp.supported_mono (allowed_mono n m hst)
 

def badVertex (m : Fin n → ℤ) (e : Exponent n) : Chart n := fun i => decide (m i<e i)
lemma badVertex_false (m : Fin n → ℤ) (e : Exponent n) (i : Fin n) (he : e i≤ m i) :
    badVertex n m e i=false := by simp [badVertex,not_lt_of_ge he]
lemma badVertex_true (m : Fin n → ℤ) (e : Exponent n) (i : Fin n) (he : m i<e i) :
    badVertex n m e i=true := by simp [badVertex,he]
lemma allowed_erase_bad (m : Fin n → ℤ) (hm : ∀ i,-1≤ m i) (s : Finset (Chart n))
    (e : Exponent n) (he : allowed n m (insert (badVertex n m e) s) e) : allowed n m s e := by
  intro i
  constructor
  · intro hs
    by_contra hneg
    have hv : badVertex n m e i=false := badVertex_false n m e i (by have:=hm i;omega)
    have hgood := (he i).1 (by intro σ hσ;rcases Finset.mem_insert.mp hσ with rfl|hσ;exact hv;exact hs σ hσ)
    exact hneg hgood
  · intro hs
    by_contra hneg
    have hv : badVertex n m e i=true := badVertex_true n m e i (by omega)
    have hgood := (he i).2 (by intro σ hσ;rcases Finset.mem_insert.mp hσ with rfl|hσ;exact hv;exact hs σ hσ)
    exact hneg hgood

def projector (m : Fin n → ℤ) (σ : Chart n) : LaurentModule R n →ₗ[R] LaurentModule R n where
  toFun x := x.filter (fun e => badVertex n m e=σ)
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul
lemma projector_apply (m : Fin n → ℤ) (σ : Chart n) (x : LaurentModule R n) (e : Exponent n) :
    projector R n m σ x e=if badVertex n m e=σ then x e else 0 := Finsupp.filter_apply _ _ _
lemma projector_sum (m : Fin n → ℤ) (x : LaurentModule R n) : ∑ σ,projector R n m σ x=x := by
  ext e
  simp only [Finsupp.finsetSum_apply,projector_apply]
  rw [Finset.sum_eq_single (badVertex n m e)]
  · simp
  · intro σ _ hσ
    simp [Ne.symm hσ]
  · simp
lemma projector_mem (m : Fin n → ℤ) (hm : ∀ i,-1≤ m i) (s : Finset (Chart n))
    (σ : Chart n) (x : LaurentModule R n) (hx : x∈sections R n m (insert σ s)) :
    projector R n m σ x∈sections R n m s := by
  rw [sections,Finsupp.mem_supported] at hx ⊢
  intro e he
  have he' : projector R n m σ x e≠0 := Finsupp.mem_support_iff.mp he
  rw [projector_apply] at he'
  split_ifs at he' with hv
  · subst σ
    exact allowed_erase_bad n m hm s e (hx (Finsupp.mem_support_iff.mpr he'))
  · exact (he' rfl).elim


end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
attribute [local instance] OAI.Lech.ProductSourceCover.endpointDecEq
def endpointProjector (j : Fin n) (b : Bool) : LaurentModule R n →ₗ[R] LaurentModule R n where
  toFun x := x.filter (fun e => decide (0≤e j)=b)
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul
omit [LinearOrder (Chart n)] in
lemma endpointProjector_apply (j : Fin n) (b : Bool) (x : LaurentModule R n) (e : Exponent n) :
    endpointProjector R n j b x e=if decide (0≤e j)=b then x e else 0 := Finsupp.filter_apply _ _ _
omit [LinearOrder (Chart n)] in
lemma endpointProjector_sum (j : Fin n) (x : LaurentModule R n) : ∑ b,endpointProjector R n j b x=x := by
  ext e
  simp only [Finsupp.finsetSum_apply,endpointProjector_apply]
  rw [Finset.sum_eq_single (decide (0≤e j))]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp
lemma endpoint_allowed_carrier (m : Fin n → ℤ) (j : Fin n) (hj : m j=-1)
    (s : Finset (Chart n)) (b : Bool) (e : Exponent n) (hb : decide (0≤e j)=b)
    (he : allowed n m (s∪s.image (endpointVertex n j b)) e) : allowed n m s e := by
  intro i
  by_cases hi : i=j
  · subst i
    cases b with
    | false =>
      have hneg : e j<0 := by have h := of_decide_eq_false hb; omega
      refine ⟨?_,fun _ => by omega⟩
      intro hs
      exact (he j).1 (by
        intro σ hσ
        rcases Finset.mem_union.mp hσ with hσ|hσ
        · exact hs σ hσ
        · obtain ⟨ρ,_,rfl⟩ := Finset.mem_image.mp hσ
          simp [endpointVertex])
    | true =>
      have hpos : 0≤e j := of_decide_eq_true hb
      refine ⟨fun _ => hpos,?_⟩
      intro hs
      exact (he j).2 (by
        intro σ hσ
        rcases Finset.mem_union.mp hσ with hσ|hσ
        · exact hs σ hσ
        · obtain ⟨ρ,_,rfl⟩ := Finset.mem_image.mp hσ
          simp [endpointVertex])
  · constructor
    · intro hs
      apply (he i).1
      intro σ hσ
      rcases Finset.mem_union.mp hσ with hσ|hσ
      · exact hs σ hσ
      · obtain ⟨ρ,hρ,rfl⟩ := Finset.mem_image.mp hσ
        simpa only [endpointVertex,Function.update_of_ne hi] using hs ρ hρ
    · intro hs
      apply (he i).2
      intro σ hσ
      rcases Finset.mem_union.mp hσ with hσ|hσ
      · exact hs σ hσ
      · obtain ⟨ρ,hρ,rfl⟩ := Finset.mem_image.mp hσ
        simpa only [endpointVertex,Function.update_of_ne hi] using hs ρ hρ
lemma endpointProjector_carrier (m : Fin n → ℤ) (j : Fin n) (hj : m j=-1)
    (s : Finset (Chart n)) (b : Bool) (x : LaurentModule R n)
    (hx : x∈sections R n m (s∪s.image (endpointVertex n j b))) :
    endpointProjector R n j b x∈sections R n m s := by
  rw [sections,Finsupp.mem_supported] at hx ⊢
  intro e he
  have he' : endpointProjector R n j b x e≠0 := Finsupp.mem_support_iff.mp he
  rw [endpointProjector_apply] at he'
  split_ifs at he' with hb
  · exact endpoint_allowed_carrier n m j hj s b e hb (hx (Finsupp.mem_support_iff.mpr he'))
  · exact (he' rfl).elim
lemma endpointProjector_zero (m : Fin n → ℤ) (j : Fin n) (hj : m j=-1)
    (s : Finset (Chart n)) (b : Bool) (x : LaurentModule R n)
    (hx : x∈sections R n m (s.image (endpointVertex n j b))) : endpointProjector R n j b x=0 := by
  rw [sections,Finsupp.mem_supported] at hx
  ext e
  rw [endpointProjector_apply,Finsupp.zero_apply]
  split_ifs with hb
  · by_contra he
    have ha := hx (Finsupp.mem_support_iff.mpr he) j
    cases b with
    | false =>
      have hneg : e j<0 := by have h := of_decide_eq_false hb; omega
      have hpos := ha.1 (by
        intro σ hσ
        obtain ⟨ρ,_,rfl⟩ := Finset.mem_image.mp hσ
        simp [endpointVertex])
      omega
    | true =>
      have hpos : 0≤e j := of_decide_eq_true hb
      have hneg := ha.2 (by
        intro σ hσ
        obtain ⟨ρ,_,rfl⟩ := Finset.mem_image.mp hσ
        simp [endpointVertex])
      omega
  · rfl


end Lech.ProductSourceCover


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_AlternatingCechPrismPrimitive
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
def exponentCons (k : ℤ) (e : Exponent n) : Exponent (n+1) :=
  Finsupp.equivFunOnFinite.symm (Fin.cons k (fun i => e i))
@[simp] lemma exponentCons_zero (k : ℤ) (e : Exponent n) : exponentCons n k e 0=k := rfl
@[simp] lemma exponentCons_succ (k : ℤ) (e : Exponent n) (i : Fin n) :
    exponentCons n k e i.succ=e i := rfl
lemma exponentCons_injective (k : ℤ) : Function.Injective (exponentCons n k) := by
  intro e f h
  ext i
  exact congrArg (fun z => z i.succ) h
def exponentTail (e : Exponent (n+1)) : Exponent n :=
  Finsupp.equivFunOnFinite.symm (fun i => e i.succ)
@[simp] lemma exponentTail_apply (e : Exponent (n+1)) (i : Fin n) : exponentTail n e i=e i.succ := rfl
lemma exponentCons_tail (e : Exponent (n+1)) : exponentCons n (e 0) (exponentTail n e)=e := by
  ext i
  exact Fin.cases rfl (fun _ => rfl) i
 

def exponentSlice (k : ℤ) : LaurentModule R (n+1) →ₗ[R] LaurentModule R n :=
  Finsupp.lcomapDomain (exponentCons n k) (exponentCons_injective n k)
def exponentInsert (k : ℤ) : LaurentModule R n →ₗ[R] LaurentModule R (n+1) :=
  Finsupp.lmapDomain R R (exponentCons n k)
@[simp] lemma exponentSlice_apply (k : ℤ) (x : LaurentModule R (n+1)) (e : Exponent n) :
    exponentSlice R n k x e=x (exponentCons n k e) := rfl
lemma exponentSlice_insert (k : ℤ) (x : LaurentModule R n) :
    exponentSlice R n k (exponentInsert R n k x)=x := by
  ext e
  exact Finsupp.mapDomain_apply (exponentCons_injective n k) x e
lemma exponentInsert_support (k : ℤ) (x : LaurentModule R n) (e : Exponent (n+1))
    (he : e∈(exponentInsert R n k x).support) : ∃ f∈x.support,exponentCons n k f=e := by
  have h := Finsupp.mapDomain_support (f:=exponentCons n k) (s:=x)
  exact Finset.mem_image.mp (h he)
lemma exponentSlice_mem (k : ℤ) (m : Fin n → ℤ) (s : Finset (Chart n))
    (x : LaurentModule R (n+1))
    (hx : x∈sections R (n+1) (Fin.cons k m) (s.image (trueFace n))) :
    exponentSlice R n k x∈sections R n m s := by
  rw [sections,Finsupp.mem_supported] at hx ⊢
  intro e he i
  have he' : exponentCons n k e∈x.support := Finsupp.mem_support_iff.mpr (by simpa only [exponentSlice_apply] using Finsupp.mem_support_iff.mp he)
  have ha := hx he' i.succ
  constructor
  · intro hs
    apply ha.1
    intro σ hσ
    obtain ⟨τ,hτ,rfl⟩ := Finset.mem_image.mp hσ
    exact hs τ hτ
  · intro hs
    apply ha.2
    intro σ hσ
    obtain ⟨τ,hτ,rfl⟩ := Finset.mem_image.mp hσ
    exact hs τ hτ
lemma exponentInsert_mem (k : ℤ) (m : Fin n → ℤ) (s : Finset (Chart (n+1)))
    (hs : s.Nonempty) (ht : ∀ σ∈s,σ 0=true) (x : LaurentModule R n)
    (hx : x∈sections R n m (s.image Fin.tail)) :
    exponentInsert R n k x∈sections R (n+1) (Fin.cons k m) s := by
  rw [sections,Finsupp.mem_supported] at hx ⊢
  intro e he
  obtain ⟨f,hf,rfl⟩ := exponentInsert_support R n k x e he
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · refine ⟨?_,fun _ => le_refl k⟩
    intro hh
    obtain ⟨σ,hσ⟩ := hs
    have h0 := hh σ hσ
    rw [ht σ hσ] at h0
    cases h0
  · have ha := hx hf j
    constructor
    · intro hh
      apply ha.1
      intro σ hσ
      obtain ⟨τ,hτ,rfl⟩ := Finset.mem_image.mp hσ
      exact hh τ hτ
    · intro hh
      apply ha.2
      intro σ hσ
      obtain ⟨τ,hτ,rfl⟩ := Finset.mem_image.mp hσ
      exact hh τ hτ
 

lemma neighbor_mem_iff (k : ℤ) (m : Fin n → ℤ) (s : Finset (Chart (n+1)))
    (x : LaurentModule R (n+1)) (hx : x∈sections R (n+1) (Fin.cons k m) s) :
    x∈sections R (n+1) (Fin.cons (k-1) m) s ↔
      ((∀ σ∈s,σ 0=true) → exponentSlice R n k x=0) := by
  rw [sections,Finsupp.mem_supported] at hx ⊢
  constructor
  · intro hl ht
    ext e
    change x (exponentCons n k e)=0
    by_contra he
    have ha := hl (Finsupp.mem_support_iff.mpr he) 0
    have hh := ha.2 ht
    simp only [Fin.cons_zero,exponentCons_zero] at hh
    omega
  · intro hl e he i
    refine Fin.cases ?_ (fun j => hx he j.succ) i
    refine ⟨(hx he 0).1,?_⟩
    intro ht
    have ha := (hx he 0).2 ht
    change e 0 ≤ k at ha
    by_contra hneg
    have hek : e 0=k := by change ¬e 0 ≤ k-1 at hneg;omega
    have hh := congrArg (fun z => z (exponentTail n e)) (hl ht)
    simp only [exponentSlice_apply,Finsupp.zero_apply,←hek,exponentCons_tail] at hh
    exact Finsupp.mem_support_iff.mp he hh
lemma neighbor_sections_le (k : ℤ) (m : Fin n → ℤ) (s : Finset (Chart (n+1))) :
    sections R (n+1) (Fin.cons (k-1) m) s ≤ sections R (n+1) (Fin.cons k m) s := by
  intro x hx
  rw [sections,Finsupp.mem_supported] at hx ⊢
  intro e he i
  refine Fin.cases ?_ (fun j => hx he j.succ) i
  exact ⟨(hx he 0).1,fun ht => le_trans ((hx he 0).2 ht) (by simp)⟩
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open AlternatingCech
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
def faceVertexMap : (Chart n → R) →ₗ[R] (Chart (n+1) → R) :=
  (basis R).constr R (fun σ => basis R (trueFace n σ))
lemma faceVertexMap_basis (σ : Chart n) : faceVertexMap R n (basis R σ)=basis R (trueFace n σ) := by
  simp [faceVertexMap]
def faceProjection : (Chart (n+1) → R) →ₗ[R] (Chart n → R) :=
  (basis R).constr R (fun σ => if σ 0=true then basis R (Fin.tail σ) else 0)
lemma faceProjection_basis (σ : Chart (n+1)) :
    faceProjection R n (basis R σ)=if σ 0=true then basis R (Fin.tail σ) else 0 := by
  simp only [faceProjection,Module.Basis.constr_basis]
def faceSlice (k : ℤ) (p : ℕ) : Alt R (LaurentModule R (n+1)) (ι:=Chart (n+1)) p →ₗ[R]
    Alt R (LaurentModule R n) (ι:=Chart n) p where
  toFun f := (exponentSlice R n k).compAlternatingMap (f.compLinearMap (faceVertexMap R n))
  map_add' f g := by apply AlternatingMap.ext;intro v;exact map_add (exponentSlice R n k) _ _
  map_smul' r f := by apply AlternatingMap.ext;intro v;exact map_smul (exponentSlice R n k) r _
lemma faceSlice_eval (k : ℤ) (p : ℕ) (f : Alt R (LaurentModule R (n+1)) (ι:=Chart (n+1)) p)
    (a : Fin p → Chart n) : evaluation R (LaurentModule R n) p (faceSlice R n k p f) a=
    exponentSlice R n k (evaluation R (LaurentModule R (n+1)) p f (trueFace n ∘ a)) := by
  change exponentSlice R n k (f (fun i => faceVertexMap R n (basis R (a i))))=_
  simp only [faceVertexMap_basis]
  rfl
def faceLift (k : ℤ) (p : ℕ) : Alt R (LaurentModule R n) (ι:=Chart n) p →ₗ[R]
    Alt R (LaurentModule R (n+1)) (ι:=Chart (n+1)) p where
  toFun f := (exponentInsert R n k).compAlternatingMap (f.compLinearMap (faceProjection R n))
  map_add' f g := by apply AlternatingMap.ext;intro v;exact map_add (exponentInsert R n k) _ _
  map_smul' r f := by apply AlternatingMap.ext;intro v;exact map_smul (exponentInsert R n k) r _
lemma faceLift_eval (k : ℤ) (p : ℕ) (f : Alt R (LaurentModule R n) (ι:=Chart n) p)
    (a : Fin p → Chart (n+1)) (ha : ∀ i,a i 0=true) :
    evaluation R (LaurentModule R (n+1)) p (faceLift R n k p f) a=
    exponentInsert R n k (evaluation R (LaurentModule R n) p f (Fin.tail ∘ a)) := by
  change exponentInsert R n k (f (fun i => faceProjection R n (basis R (a i))))=_
  simp only [faceProjection_basis,ha,ite_true]
  rfl
lemma faceLift_eval_zero (k : ℤ) (p : ℕ) (f : Alt R (LaurentModule R n) (ι:=Chart n) p)
    (a : Fin p → Chart (n+1)) (ha : ¬∀ i,a i 0=true) :
    evaluation R (LaurentModule R (n+1)) p (faceLift R n k p f) a=0 := by
  obtain ⟨i,hi⟩ := not_forall.mp ha
  change exponentInsert R n k (f (fun j => faceProjection R n (basis R (a j))))=0
  have hz : faceProjection R n (basis R (a i))=0 := by rw [faceProjection_basis,ite_eq_right hi]
  rw [f.map_coord_zero i hz,map_zero]
lemma faceSlice_mem (k : ℤ) (m : Fin n → ℤ) (p : ℕ)
    (f : Alt R (LaurentModule R (n+1)) (ι:=Chart (n+1)) p)
    (hf : f∈cochains R (LaurentModule R (n+1)) (sections R (n+1) (Fin.cons k m)) p) :
    faceSlice R n k p f∈cochains R (LaurentModule R n) (sections R n m) p := by
  intro a
  rw [faceSlice_eval]
  apply exponentSlice_mem R n k m
  have h := hf (trueFace n ∘ a)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [FiniteCoverCech.intersection,Finset.image_image,Function.comp_def]
lemma faceLift_mem (k : ℤ) (m : Fin n → ℤ) (p : ℕ) (hp : 0<p)
    (f : Alt R (LaurentModule R n) (ι:=Chart n) p)
    (hf : f∈cochains R (LaurentModule R n) (sections R n m) p) :
    faceLift R n k p f∈cochains R (LaurentModule R (n+1)) (sections R (n+1) (Fin.cons k m)) p := by
  intro a
  by_cases ha : ∀ i,a i 0=true
  · rw [faceLift_eval R n k p f a ha]
    apply exponentInsert_mem R n k m
    · exact ⟨a ⟨0,hp⟩,by simp [FiniteCoverCech.intersection]⟩
    · intro σ hσ
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hσ
      exact ha i
    · have h := hf (Fin.tail ∘ a)
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      simp only [FiniteCoverCech.intersection,Finset.image_image,Function.comp_def]
  · rw [faceLift_eval_zero R n k p f a ha]
    exact (sections R (n+1) (Fin.cons k m) _).zero_mem
end Lech.ProductSourceCover
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverFaceSlice
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
open AlternatingCech
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
abbrev divisorCochains (m : Fin n → ℤ) (p : ℕ) :=
  cochains R (LaurentModule R n) (sections R n m) p
def divisorInclusion (k : ℤ) (m : Fin n → ℤ) (p : ℕ) :
    divisorCochains R (n+1) (Fin.cons (k-1) m) p →ₗ[R] divisorCochains R (n+1) (Fin.cons k m) p :=
  Submodule.inclusion (by
    intro f hf a
    exact neighbor_sections_le R n k m _ (hf a))

end Lech.ProductSourceCover


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_AlternatingCechUnaugmentedComplex
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
open AlternatingCech CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
abbrev ordinarySections (m : Fin n → ℤ) := zeroAugmentation R (LaurentModule R n) (sections R n m)
abbrev ordinaryCochains (m : Fin n → ℤ) (p : ℕ) :=
  cochains R (LaurentModule R n) (ordinarySections R n m) p
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
open AddMonoidAlgebra
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
lemma allowed_add (m k : Fin n → ℤ) (s : Finset (Chart n)) (e f : Exponent n)
    (he : allowed n m s e) (hf : allowed n k s f) : allowed n (m+k) s (e+f) := by
  intro i
  exact ⟨fun h => add_nonneg ((he i).1 h) ((hf i).1 h),fun h => add_le_add ((he i).2 h) ((hf i).2 h)⟩


def twistExponent (m : Fin n → ℤ) (σ : Chart n) : Exponent n :=
  Finsupp.equivFunOnFinite.symm (fun i => if σ i then m i else 0)
lemma twistExponent_apply (m : Fin n → ℤ) (σ : Chart n) (i : Fin n) :
    twistExponent n m σ i=(if σ i then m i else 0) := rfl
def affineExponent (m : Fin n → ℤ) (σ : Chart n) (e : Fin n →₀ ℕ) : Exponent n :=
  twistExponent n m σ+ProductLaurent.signedExponent n σ e
lemma affineExponent_allowed (m : Fin n → ℤ) (σ : Chart n) (e : Fin n →₀ ℕ) :
    allowed n m {σ} (affineExponent n m σ e) := by
  intro i
  simp only [affineExponent,Finsupp.add_apply,twistExponent_apply,ProductLaurent.signedExponent_apply]
  cases hs : σ i <;> simp [hs]
def affineCoordinates (m : Fin n → ℤ) (σ : Chart n) (e : Exponent n) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => if σ i then (m i-e i).toNat else (e i).toNat)
lemma affineExponent_coordinates (m : Fin n → ℤ) (σ : Chart n) (e : Exponent n)
    (he : allowed n m {σ} e) : affineExponent n m σ (affineCoordinates n m σ e)=e := by
  ext i
  have hi := he i
  simp only [Finset.mem_singleton,forall_eq] at hi
  simp only [affineExponent,Finsupp.add_apply,twistExponent_apply,ProductLaurent.signedExponent_apply]
  change (if σ i then m i else 0)+(if σ i then -(↑(if σ i then (m i-e i).toNat else (e i).toNat):ℤ)
    else (↑(if σ i then (m i-e i).toNat else (e i).toNat):ℤ))=e i
  cases hs : σ i <;> simp only [hs,Bool.false_eq_true,↓reduceIte] at hi ⊢
  · rw [Int.toNat_of_nonneg (hi.1 trivial),zero_add]
  · rw [Int.toNat_of_nonneg (sub_nonneg.mpr (hi.2 trivial))];omega


end Lech.ProductSourceCover


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverAllowedEmpty
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
open AddMonoidAlgebra
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
lemma allowed_empty (m : Fin n → ℤ) (e : Exponent n) :
    allowed n m ∅ e ↔ ∀ i,0≤e i ∧ e i ≤ m i := by
  simp [allowed]
 
abbrev GlobalIndex (m : Fin n → ℤ) := {e : Exponent n // allowed n m ∅ e}
def globalIndexEquiv (m : Fin n → ℤ) : GlobalIndex n m ≃ (∀ i : Fin n,Set.Icc (0:ℤ) (m i)) where
  toFun e i := ⟨e.val i,(allowed_empty n m e.val).mp e.property i⟩
  invFun e := ⟨Finsupp.equivFunOnFinite.symm (fun i => (e i).val),
    (allowed_empty n m _).mpr (fun i => (e i).property)⟩
  left_inv e := by apply Subtype.ext;ext i;rfl
  right_inv e := by funext i;apply Subtype.ext;rfl
instance globalIndexFintype (m : Fin n → ℤ) : Fintype (GlobalIndex n m) :=
  Fintype.ofEquiv _ (globalIndexEquiv n m).symm
lemma globalIndex_card (m : Fin n → ℤ) : Fintype.card (GlobalIndex n m)=∏ i,(m i+1).toNat := by
  rw [Fintype.card_congr (globalIndexEquiv n m),Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  rw [Fintype.card_ofFinset]
  simp only [Int.card_Icc,sub_zero]


end Lech.ProductSourceCover


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverOrdinaryPositive
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
def subsetExponent (s : Finset (Fin n)) : Exponent n := ∑ i∈s,Finsupp.single i 1
lemma subsetExponent_apply (s : Finset (Fin n)) (j : Fin n) :
    subsetExponent n s j=if j∈s then 1 else 0 := by
  classical
  simp [subsetExponent,Finsupp.finsetSum_apply,Finsupp.single_apply]
lemma subsetExponent_allowed (s : Finset (Fin n)) :
    allowed n (fun _ => 1) ∅ (subsetExponent n s) := by
  intro i
  rw [subsetExponent_apply]
  split_ifs <;> simp
end Lech.ProductSourceCover


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverHighThreshold
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.ProductLinearChart
open Polynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (σ : Fin n → Bool)
lemma linear_content_top (i : Fin n) :
    (C (a R n σ i)*Polynomial.X+C (b R n σ i)).contentIdeal=⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  cases hs : σ i
  · have hi := (C (a R n σ i)*Polynomial.X+C (b R n σ i)).coeff_mem_contentIdeal 0
    simpa only [coeff_add,coeff_C_mul,coeff_X_zero,mul_zero,zero_add,coeff_C_zero,b,hs,Bool.false_eq_true,↓reduceIte] using hi
  · have hi := (C (a R n σ i)*Polynomial.X+C (b R n σ i)).coeff_mem_contentIdeal 1
    simpa only [coeff_add,coeff_C_mul,coeff_X_one,mul_one,coeff_C_succ,add_zero,a,hs,↓reduceIte] using hi
lemma product_content_top : (product R n σ).contentIdeal=⊤ := by
  apply Finset.prod_induction (fun i : Fin n => C (a R n σ i)*Polynomial.X+C (b R n σ i))
    (fun p : (Ring R n)[X] => p.contentIdeal=⊤)
  · intro p q hp hq
    exact contentIdeal_mul_eq_top_of_contentIdeal_eq_top hp hq
  · exact contentIdeal_one
  · intro i _
    exact linear_content_top R n σ i
 

lemma coefficients_span :
    Ideal.span (Set.range (fun k : Fin (n+1) => (product R n σ).coeff k))=⊤ := by
  apply top_unique
  rw [←product_content_top R n σ,contentIdeal_def,Ideal.span_le]
  intro r hr
  obtain ⟨j,hj,rfl⟩ := Polynomial.mem_coeffs_iff.mp hr
  by_cases h : j<n+1
  · exact Ideal.subset_span (Set.mem_range_self (⟨j,h⟩ : Fin (n+1)))
  · have hz : (product R n σ).coeff j=0 := coeff_eq_zero_of_natDegree_lt (by
      have hd := product_degree R n σ
      omega)
    exact ((Polynomial.mem_support_iff.mp hj) hz).elim
end Lech.ProductLinearChart


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechHomogeneousEval
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
lemma twistExponent_level (m : Fin n → ℤ) (σ : Chart n) (N : ℕ) :
    twistExponent n (levelTwist n m 1 N) σ=twistExponent n m σ+N • twistExponent n (fun _ => 1) σ := by
  ext i
  cases hs : σ i <;> simp [twistExponent_apply,levelTwist,hs]
end


open Polynomial
universe u
end


universe u
variable (R : Type u) [CommRing R] (n : ℕ)

def targetProduct (k : Fin (n+1)) (s : Finset (Fin (n+1))) : UniversalCoefficientChart.Ring R n k :=
  ∏ j∈s,UniversalCoefficientChart.coefficient R n k j
end Lech.ProductSourceCover


namespace Lech.UniversalSplitting
open Polynomial
universe u

attribute [instance] Data.ring Data.algebra


variable {R : Type u} [CommRing R] {n : ℕ} {f : R[X]}

lemma Data.finite (d : Data R n f) : Module.Finite R d.S :=
  Module.Finite.of_basis d.basis

lemma Data.free (d : Data R n f) : Module.Free R d.S :=
  Module.Free.of_basis d.basis

lemma Data.flat (d : Data R n f) : Module.Flat R d.S := by
  have := d.free
  exact Module.Flat.of_free

end Lech.UniversalSplitting

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootTowerRemainderExponent
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical

open scoped TensorProduct
open IsLocalRing

open MvPowerSeries IsLocalRing


namespace Lech.RootTower
variable (A : Type*) [CommRing A] [IsReduced A] (p : ℕ) [Fact p.Prime] [CharP A p]


def rootRing (n : ℕ) : Subring (PerfectClosure A p) := (rootMap A p n).range

end Lech.RootTower


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_NativeDescentCanonicalAlg
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
variable (f : A[X])
  (n : ℕ)
  (hn : f.natDegree≤n)
  (t : B)
  (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
variable (w : Tˣ) (a b : Fin n → T)
  (hf : (f.map (algebraMap A T)).homogenize n=MvPolynomial.C (w:T)*∏ i,
    (MvPolynomial.C (a i)*MvPolynomial.X 0+MvPolynomial.C (b i)*MvPolynomial.X 1))

include hv in
lemma value : ((f.map (algebraMap A B)).map (algebraMap B (R (A := A) (B := B) (T := T)))).eval
    (algebraMap B _ t)=(Units.map (algebraMap B (R (A := A) (B := B) (T := T))).toMonoidHom v:R (A := A) (B := B) (T := T)) := by
  rw [Polynomial.eval_map,eval₂_at_apply,hv]
  rfl


end Lech.UniversalFactorMap


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_UniversalFactorMapMapChart
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.ProductLinearChart
open Polynomial
universe u v
variable (R : Type u) [CommRing R] (n : ℕ) (σ : Fin n → Bool) (k : Fin (n+1))
variable {T : Type v} [CommRing T] [Algebra R T]

variable (x y : Fin n → T) (hs : ∀ i,(if σ i then x i else y i)=1)
def eval : Ring R n →ₐ[R] T := MvPolynomial.aeval fun i => if σ i then y i else x i

include hs in
lemma eval_a (i : Fin n) : eval R n σ x y (a R n σ i)=x i := by
  have h := hs i
  cases hi : σ i <;> simp [a,eval,hi] at h ⊢
  exact h.symm
include hs in
lemma eval_b (i : Fin n) : eval R n σ x y (b R n σ i)=y i := by
  have h := hs i
  cases hi : σ i <;> simp [b,eval,hi] at h ⊢
  exact h.symm
include hs in
lemma eval_product : (product R n σ).map (eval R n σ x y).toRingHom=
    ∏ i,(C (x i)*Polynomial.X+C (y i)) := by
  simp only [product,Polynomial.map_prod,Polynomial.map_add,Polynomial.map_mul,
    Polynomial.map_C,Polynomial.map_X,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
    eval_a R n σ x y hs,eval_b R n σ x y hs]

variable (c : UniversalCoefficientChart.Ring R n k →ₐ[R] T) (w : Tˣ)
variable (hf : ((UniversalCoefficientChart.form R n k).map c.toRingHom).homogenize n=
  MvPolynomial.C (w:T)*∏ i,(MvPolynomial.C (x i)*MvPolynomial.X 0+MvPolynomial.C (y i)*MvPolynomial.X 1))

include hs hf in
lemma eval_coeff : ∀ j : Fin (n+1),
    c (UniversalCoefficientChart.coefficient R n k j)=
      (w:T)*eval R n σ x y ((product R n σ).coeff j) := by
  have h := dehomogenize_factorization n _
    (natDegree_map_le.trans (UniversalCoefficientChart.form_degree R n k)) (w:T) x y hf
  rw [←eval_product R n σ x y hs] at h
  intro j
  have hh := congrArg (fun p : T[X] => p.coeff j) h
  simpa only [coeff_map,UniversalCoefficientChart.form_coeff,coeff_C_mul,
    AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using hh

include hs hf in
lemma eval_self : eval R n σ x y ((product R n σ).coeff k)=(w⁻¹).val := by
  have h := eval_coeff R n σ k x y hs c w hf k
  rw [UniversalCoefficientChart.coefficient_self,map_one] at h
  calc
    eval R n σ x y ((product R n σ).coeff k)=(w⁻¹).val*((w:T)*eval R n σ x y ((product R n σ).coeff k)) := by simp
    _ = (w⁻¹).val := by rw [←h,mul_one]

def lift : chart R n σ k →ₐ[R] T :=
  IsLocalization.Away.liftAlgHom ((product R n σ).coeff k)
    (f := eval R n σ x y)
    (by rw [eval_self R n σ k x y hs c w hf];exact (w⁻¹).isUnit)

lemma lift_from (z : Ring R n) :
    lift R n σ k x y hs c w hf (algebraMap (Ring R n) (chart R n σ k) z)=eval R n σ x y z := by
  exact IsLocalization.Away.lift_eq (S := chart R n σ k)
    (g := (eval R n σ x y).toRingHom) ((product R n σ).coeff k)
    (by change IsUnit (eval R n σ x y ((product R n σ).coeff k));rw [eval_self R n σ k x y hs c w hf];exact (w⁻¹).isUnit) z

lemma lift_denominator : Units.map (lift R n σ k x y hs c w hf).toMonoidHom (denominator R n σ k)=w⁻¹ := by
  apply Units.ext
  change lift R n σ k x y hs c w hf (denominator R n σ k:chart R n σ k)=(w⁻¹).val
  rw [denominator_val,lift_from,eval_self R n σ k x y hs c w hf]

lemma lift_target : (lift R n σ k x y hs c w hf).comp (target R n σ k)=c := by
  apply UniversalCoefficientChart.ext
  intro j
  rw [AlgHom.comp_apply]
  change lift R n σ k x y hs c w hf
    (UniversalCoefficientChart.eval R n k (fun j => (normalized R n σ k).coeff j)
      (UniversalCoefficientChart.coefficient R n k j))=_
  rw [UniversalCoefficientChart.eval_coefficient R n k _ (normalized_self R n σ k) j,
    normalized,coeff_C_mul,coeff_map,map_mul,lift_from]
  have hinv := congrArg (fun u : Tˣ => (u⁻¹).val) (lift_denominator R n σ k x y hs c w hf)
  change lift R n σ k x y hs c w hf ((denominator R n σ k)⁻¹).val=(w⁻¹)⁻¹.val at hinv
  rw [hinv,inv_inv]
  exact (eval_coeff R n σ k x y hs c w hf j).symm

lemma lift_X (i : Fin n) :
    lift R n σ k x y hs c w hf
      (algebraMap (Ring R n) (chart R n σ k) (MvPolynomial.X i))=
        if σ i then y i else x i := by
  rw [lift_from]
  exact MvPolynomial.aeval_X _ _

lemma hom_ext {φ ψ : chart R n σ k →ₐ[R] T}
    (h : ∀ i,φ (algebraMap (Ring R n) (chart R n σ k) (MvPolynomial.X i))=
      ψ (algebraMap (Ring R n) (chart R n σ k) (MvPolynomial.X i))) : φ=ψ := by
  have hh : φ.comp (IsScalarTower.toAlgHom R (Ring R n) (chart R n σ k))=
      ψ.comp (IsScalarTower.toAlgHom R (Ring R n) (chart R n σ k)) :=
    MvPolynomial.algHom_ext h
  apply AlgHom.ext
  have hr : φ.toRingHom=ψ.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers ((product R n σ).coeff k))
    apply RingHom.ext
    intro z
    exact AlgHom.congr_fun hh z
  exact RingHom.congr_fun hr

end Lech.ProductLinearChart


namespace Lech.RootChartAtlas
open Polynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
abbrev A := UniversalCoefficientChart.Ring R n k
abbrev f := UniversalCoefficientChart.form R n k
abbrev hn : (f R n k).natDegree≤n := UniversalCoefficientChart.form_degree R n k
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B)
  (v : Bˣ)
  (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
variable (σ : Fin n → Bool)
abbrev H := ProductLinearChart.chart R n σ k

lemma source_selected (i : Fin n) :
    (if σ i then algebraMap (ProductLinearChart.Ring R n) (H R n k σ) (ProductLinearChart.a R n σ i)
      else algebraMap (ProductLinearChart.Ring R n) (H R n k σ) (ProductLinearChart.b R n σ i))=1 := by
  have h := congrArg (algebraMap (ProductLinearChart.Ring R n) (H R n k σ)) (ProductLinearChart.selected R n σ i)
  cases hi : σ i <;> simpa only [hi,Bool.false_eq_true,↓reduceIte,map_one] using h

end Lech.RootChartAtlas
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechFactorizationMap
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
variable (t : B)
  (v : Bˣ)
  (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
variable [Module.FaithfullyFlat (A R n k) B]
lemma coordinate_regular (τ : Fin n → Bool) (i : Fin n) (b : Bool) :
    IsRegular (if b then ProductLinearChart.a R n τ i else ProductLinearChart.b R n τ i) := by
  cases b <;> cases ht : τ i <;> simp [ProductLinearChart.a,ProductLinearChart.b,ht, isRegular_one]
end Lech.RootChartAtlas


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootChartAtlasGlobalCoefficient
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
open MvPolynomial HomogeneousLocalization
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1)) (s : Finset (Fin (n+1)))
attribute [local instance] MvPolynomial.gradedAlgebra
lemma projectiveRemainder_evaluate (hk : k∈s) :
    ProjectiveCoefficientChart.evaluate R n k (projectiveRemainder R n k s)=targetProduct R n k s := by
  simp only [projectiveRemainder,map_prod,ProjectiveCoefficientChart.evaluate,MvPolynomial.aeval_X]
  rw [targetProduct,←Finset.mul_prod_erase s (UniversalCoefficientChart.coefficient R n k) hk,
    UniversalCoefficientChart.coefficient_self,one_mul]


end Lech.ProductSourceCover
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootTowerLengthEq
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct


namespace Lech.RootTower
variable {A B : Type*} [CommRing A] [IsReduced A] [CommRing B] [IsReduced B]
variable (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]

lemma perfectMap_root (f : A →+* B) (n : ℕ) (a : A) :
    perfectMap p f (rootMap A p n a) = rootMap B p n (f a) := by
  apply (injective_frobenius (PerfectClosure B p) p).iterate n
  rw [iterate_frobenius, iterate_frobenius, ← map_pow, rootMap_pow, rootMap_pow]
  exact PerfectRing.lift_comp_apply _ _ _ _

end Lech.RootTower


namespace Lech.RootTower
variable (A : Type*) [CommRing A] [IsDomain A] (p : ℕ) [Fact p.Prime] [CharP A p]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] [CharP K p]

instance perfectFractionAlgebra : Algebra (PerfectClosure A p) (PerfectClosure K p) :=
  (perfectMap p (algebraMap A K)).toAlgebra

end Lech.RootTower


namespace Lech.RootTower
variable {A B C : Type*} [CommRing A] [IsReduced A] [CommRing B] [IsReduced B]
  [CommRing C] [IsReduced C] (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p] [CharP C p]

lemma perfectMap_comp (f : A →+* B) (g : B →+* C) :
    (perfectMap p g).comp (perfectMap p f) = perfectMap p (g.comp f) := by
  ext x
  obtain ⟨⟨n,a⟩,rfl⟩ := PerfectClosure.mk_surjective A p x
  change perfectMap p g (perfectMap p f (rootMap A p n a)) =
    perfectMap p (g.comp f) (rootMap A p n a)
  simp only [perfectMap_root,RingHom.comp_apply]

end Lech.RootTower


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TraceConductorPerfectOrder
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct

open scoped TensorProduct nonZeroDivisors


namespace Lech.PerfectStages
open Lech.RootTower
open scoped TensorProduct
variable (A D L : Type*) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
  [Field L] [Algebra A D] [Algebra A L] [Algebra D L] [IsScalarTower A D L]
  (p : ℕ) [Fact p.Prime] [CharP A p] [CharP L p]

 
def tensorStageMap (n : ℕ) :
    let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
    (PerfectClosure A p) ⊗[A] D →ₐ[PerfectClosure A p] PerfectClosure L p := by
  let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
  let : Algebra A (PerfectClosure L p) :=
    ((rootMap L p n).comp (algebraMap A L)).toAlgebra
  let : IsScalarTower A (PerfectClosure A p) (PerfectClosure L p) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      exact (perfectMap_root p (algebraMap A L) n a).symm)
  let f : D →ₐ[A] PerfectClosure L p :=
    { __ := (rootMap L p n).comp (algebraMap D L)
      commutes' a := congrArg (rootMap L p n) (IsScalarTower.algebraMap_apply A D L a).symm }
  exact Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId (PerfectClosure A p) _) f

end Lech.PerfectStages


namespace Lech.PerfectDomainStages
open Lech.RootTower
open scoped TensorProduct
variable (A D : Type*) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
  [Algebra A D] (p : ℕ) [Fact p.Prime] [CharP A p] [CharP D p]

def stage (n : ℕ) : Subalgebra (PerfectClosure A p) (PerfectClosure D p) :=
  Algebra.adjoin (PerfectClosure A p) (Set.range (rootMap D p n))

def tensorMap (n : ℕ) :
    let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
    (PerfectClosure A p) ⊗[A] D →ₐ[PerfectClosure A p] PerfectClosure D p := by
  let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
  let : Algebra A (PerfectClosure D p) := ((rootMap D p n).comp (algebraMap A D)).toAlgebra
  let : IsScalarTower A (PerfectClosure A p) (PerfectClosure D p) :=
    IsScalarTower.of_algebraMap_eq' (by ext a; exact (perfectMap_root p _ n a).symm)
  let f : D →ₐ[A] PerfectClosure D p := { __ := rootMap D p n, commutes' _ := rfl }
  exact Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId (PerfectClosure A p) _) f

lemma tensorMap_apply (n : ℕ) (a : PerfectClosure A p) (d : D) :
    let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
    tensorMap A D p n (a ⊗ₜ[A] d) = perfectMap p (algebraMap A D) a * rootMap D p n d := rfl

lemma tensorMap_range (n : ℕ) :
    let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
    (tensorMap A D p n).range = stage A D p n := by
  let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    induction x using OAI.tensorInductionOn with
    | tmul a d =>
      change perfectMap p (algebraMap A D) a * rootMap D p n d ∈ _
      exact (stage A D p n).mul_mem ((stage A D p n).algebraMap_mem a)
        (Algebra.subset_adjoin ⟨d,rfl⟩)
    | add x y hx hy => simpa only [map_add] using (stage A D p n).add_mem hx hy
  · apply Algebra.adjoin_le
    rintro _ ⟨d,rfl⟩
    refine ⟨1 ⊗ₜ[A] d,?_⟩
    change tensorMap A D p n (1 ⊗ₜ[A] d) = _
    rw [tensorMap_apply,map_one,one_mul]

variable (L : Type*) [Field L] [Algebra A L] [Algebra D L] [IsScalarTower A D L]
  [CharP L p]

def fieldMap : PerfectClosure D p →ₐ[PerfectClosure A p] PerfectClosure L p where
  __ := perfectMap p (algebraMap D L)
  commutes' a := by
    change perfectMap p (algebraMap D L) (perfectMap p (algebraMap A D) a) = _
    rw [← RingHom.comp_apply,perfectMap_comp,← IsScalarTower.algebraMap_eq]
    rfl

end Lech.PerfectDomainStages
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PerfectDomainStagesTensorTo
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
namespace Lech.PerfectDomainStages
open Lech.RootTower
open scoped TensorProduct
variable (A D : Type*) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
  [Algebra A D] (p : ℕ) [Fact p.Prime] [CharP A p] [CharP D p]

def tensorToStage (n : ℕ) :
    let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
    (PerfectClosure A p) ⊗[A] D →ₐ[PerfectClosure A p] stage A D p n := by
  let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
  exact (tensorMap A D p n).codRestrict (stage A D p n) (by
    intro x
    rw [← tensorMap_range A D p n]
    exact ⟨x,rfl⟩)

lemma tensorToStage_bijective (n : ℕ) (hi : Function.Injective (tensorMap A D p n)) :
    Function.Bijective (tensorToStage A D p n) := by
  let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
  constructor
  · intro x y h
    exact hi (congrArg Subtype.val h)
  · intro b
    have hb := b.property
    have hb' : (b : PerfectClosure D p) ∈ (tensorMap A D p n).range :=
      (tensorMap_range A D p n).symm ▸ hb
    clear hb
    obtain ⟨x,hx⟩ := hb'
    exact ⟨x,Subtype.ext hx⟩

def tensorEquiv (n : ℕ) (hi : Function.Injective (tensorMap A D p n)) :
    let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
    (PerfectClosure A p) ⊗[A] D ≃ₐ[PerfectClosure A p] stage A D p n := by
  let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
  exact AlgEquiv.ofBijective (tensorToStage A D p n) (tensorToStage_bijective A D p n hi)

omit [IsDomain A] in
lemma original_mem_stage (n : ℕ) (d : D) : PerfectClosure.of D p d ∈ stage A D p n := by
  change rootMap D p 0 d ∈ _
  rw [← rootMap_transition D p 0 n (Nat.zero_le n) d]
  exact Algebra.subset_adjoin ⟨iterateFrobenius D p (n-0) d,rfl⟩

def originalToStage (n : ℕ) : D →+* stage A D p n :=
  (PerfectClosure.of D p).codRestrict (stage A D p n).toSubring (original_mem_stage A D p n)

def rootToStage (n : ℕ) : D →+* stage A D p n :=
  (rootMap D p n).codRestrict (stage A D p n).toSubring
    (fun d => Algebra.subset_adjoin ⟨d,rfl⟩)

omit [IsDomain A] in
lemma rootToStage_original (n : ℕ) :
    (rootToStage A D p n).comp (iterateFrobenius D p n) = originalToStage A D p n := by
  apply DFunLike.ext
  intro d
  apply Subtype.ext
  exact rootMap_transition D p 0 n (Nat.zero_le n) d

end Lech.PerfectDomainStages


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_KoszulConeFunctor
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian




namespace Lech.NormalizedLength.Tower
open CategoryTheory CategoryTheory.Limits
universe u
variable {P C : Type u} [CommRing P] [CommRing C]
 

noncomputable def torsionLength (T : Tower P) (f : P →+* C) (I : Ideal C) :
    Lech.TorsionLength I where
  value M := T.length ((ModuleCat.restrictScalars f).obj M)
  zero {M} hM := by
    have : Subsingleton M := ModuleCat.isZero_iff_subsingleton.mp hM
    let : Subsingleton ((ModuleCat.restrictScalars f).obj M) := by
      change Subsingleton M
      infer_instance
    exact T.length_zero
  additive {S} hS _ := by
    let : Mono S.f := hS.mono_f
    let : Epi S.g := hS.epi_g
    let S' := S.map (ModuleCat.restrictScalars f)
    have hS' : S'.ShortExact := hS.map (ModuleCat.restrictScalars f)
    let : Mono S'.f := hS'.mono_f
    let : Epi S'.g := hS'.epi_g
    exact T.length_eq_add_of_exact S'.f.hom S'.g.hom
      ((ModuleCat.mono_iff_injective S'.f).mp inferInstance)
      ((ModuleCat.epi_iff_surjective S'.g).mp inferInstance)
      (fun x => ⟨S'.moduleCat_exact_iff.mp hS'.exact x, fun ⟨y,hy⟩ => by
        rw [← hy]
        exact ConcreteCategory.congr_hom S'.zero y⟩)
end Lech.NormalizedLength.Tower


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TowerRestrictedLength
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open CategoryTheory
attribute [local instance] Classical.propDecidable


namespace Lech.NormalizedLength.Tower
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal DirectSum
universe u
variable {P C : Type u} [CommRing P] [CommRing C]
  (T : Tower P) (f : P →+* C)

 

noncomputable def allModuleLength (r : ℝ≥0∞) (hr : r ≠ 0) : Lech.AllModuleLength C where
  value M := r*T.length ((ModuleCat.restrictScalars f).obj M)
  zero h := by
    have hz := (T.torsionLength f ⊥).zero h
    change T.length ((ModuleCat.restrictScalars f).obj _) = 0 at hz
    rw [hz,mul_zero]
  additive h := by
    have ha := (T.torsionLength f ⊥).additive h ⟨1,by simp⟩
    change T.length ((ModuleCat.restrictScalars f).obj _) =
      T.length ((ModuleCat.restrictScalars f).obj _) +
        T.length ((ModuleCat.restrictScalars f).obj _) at ha
    rw [ha,mul_add]
  directSum_zero := by
    intro ι G _ _ hG
    have hz := T.restrictedLength_directSum_zero f G
      (fun i => (mul_eq_zero.mp (hG i)).resolve_left hr)
    rw [hz,mul_zero]
  iSup_zero := by
    intro ι M _ _ U hU
    have hz := T.restrictedLength_iSup_zero f U
      (fun i => (mul_eq_zero.mp (hU i)).resolve_left hr)
    rw [hz,mul_zero]
  directLimit_zero := by
    intro ι _ _ _ G _ _ g hG
    have hz := T.restrictedLength_directLimit_zero f G g
      (fun i => (mul_eq_zero.mp (hG i)).resolve_left hr)
    rw [hz,mul_zero]
end Lech.NormalizedLength.Tower


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusComplexStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ENNReal
namespace Lech.PerfectDomainStages
open Lech.RootTower
universe u
variable (A D : Type u) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
  [Algebra A D] (p : ℕ) [Fact p.Prime] [CharP A p] [CharP D p]

def stageFrobeniusIso (n : ℕ) (F : CochainComplex (ModuleCat.{u} D) ℤ) :
    (((ModuleCat.extendScalars (originalToStage A D p n)).mapHomologicalComplex _).obj F) ≅
      (((ModuleCat.extendScalars (rootToStage A D p n)).mapHomologicalComplex _).obj
        (Lech.frobeniusComplex D p n F)) := by
  rw [← rootToStage_original A D p n]
  exact (NatIso.mapHomologicalComplex
    (ModuleCat.extendScalarsComp (iterateFrobenius D p n)
      (rootToStage A D p n)) (.up ℤ)).app F
end Lech.PerfectDomainStages

namespace Lech.PerfectDomainStages
open Lech.RootTower
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D]
  [Algebra (MvPowerSeries (Fin h) k) D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]

def stageComplex (n : ℕ) (F : CochainComplex (ModuleCat.{u} D) ℤ) :
    CochainComplex (ModuleCat.{u} (PerfectClosure (MvPowerSeries (Fin h) k) p)) ℤ :=
  ((ModuleCat.restrictScalars (algebraMap (PerfectClosure (MvPowerSeries (Fin h) k) p)
      (stage (MvPowerSeries (Fin h) k) D p n))).mapHomologicalComplex _).obj
    (((ModuleCat.extendScalars (originalToStage (MvPowerSeries (Fin h) k) D p n)).mapHomologicalComplex _).obj F)

end Lech.PerfectDomainStages

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_OrderedRootBasis
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.UniversalSplitting
open Polynomial
universe u

theorem exists_power_data (n : ℕ) : ∀ (R : Type u) [CommRing R] [Nontrivial R]
    (f : R[X]), f.Monic → f.natDegree=n → ∃ d : Data R n f, ∃ b : Module.Basis (PowerIndex n) R d.S,
      ∀ e, b e=powerMonomial n d.roots e := by
  induction n with
  | zero =>
    intro R _ _ f hf hn
    have hf1 : f=1 := hf.natDegree_eq_zero.mp hn
    refine ⟨{
      S := R
      basis := Module.Basis.singleton (Fin 1) R
      roots := Fin.elim0
      factorization := by simp [hf1]
      universal := by
        intro T _ _ xs _
        refine ⟨Algebra.ofId R T, fun i => Fin.elim0 i, ?_⟩
        intro φ _
        ext },Module.Basis.singleton Unit R,?_⟩
    intro e
    simp [powerMonomial, Module.Basis.singleton_apply]
  | succ n ih =>
    intro R _ _ f hf hn
    let B := AdjoinRoot f
    let b : Module.Basis (Fin (n+1)) R B :=
      (AdjoinRoot.powerBasisAux' hf).reindex (finCongr hn)
    let : Nontrivial B := b.repr.symm.injective.nontrivial
    let g : B[X] := f.map (algebraMap R B) /ₘ (X-C (AdjoinRoot.root f))
    have hfac : f.map (algebraMap R B) = (X-C (AdjoinRoot.root f))*g := by
      apply Eq.symm
      exact (mul_divByMonic_eq_iff_isRoot).mpr (AdjoinRoot.isRoot_root f)
    have hg : g.Monic := (monic_X_sub_C _).of_mul_monic_left (hfac ▸ hf.map _)
    have hdeg : g.natDegree=n := by
      rw [show g = _ from rfl, natDegree_divByMonic _ (monic_X_sub_C _),
        hf.natDegree_map, natDegree_X_sub_C, hn]
      omega
    obtain ⟨d,bd,hbd⟩ := ih B g hg hdeg
    let : Algebra R d.S := ((algebraMap B d.S).comp (algebraMap R B)).toAlgebra
    let : IsScalarTower R B d.S := IsScalarTower.of_algebraMap_eq fun r => rfl
    let bb : Module.Basis (Fin (n+1) × Fin n.factorial) R d.S := b.smulTower d.basis
    let c : Module.Basis (Fin (n+1).factorial) R d.S :=
      bb.reindex (finProdFinEquiv.trans (finCongr (Nat.factorial_succ n).symm))
    let rs : Fin (n+1) → d.S := Fin.cons
      (algebraMap B d.S (AdjoinRoot.root f)) d.roots
    refine ⟨{
      S := d.S
      basis := c
      roots := rs
      factorization := ?_
      universal := ?_ },b.smulTower bd,?_⟩
    · have hmap := congrArg (Polynomial.map (algebraMap B d.S)) hfac
      rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
        Polynomial.map_C, d.factorization] at hmap
      simpa [rs, Fin.prod_univ_succ, Polynomial.map_map,
        IsScalarTower.algebraMap_eq R B d.S] using hmap

    · intro T _ _ xs hxs
      have hx0 : f.eval₂ (algebraMap R T) (xs 0)=0 := by
        rw [← Polynomial.eval_map, hxs, Fin.prod_univ_succ]
        simp
      let β : B →ₐ[R] T := AdjoinRoot.liftAlgHom f (Algebra.ofId R T) (xs 0) hx0
      have hβ : β (AdjoinRoot.root f)=xs 0 := AdjoinRoot.liftAlgHom_root _ _ _ _
      let : Algebra B T := β.toRingHom.toAlgebra
      let : IsScalarTower R B T := IsScalarTower.of_algebraMap_eq fun r => (β.commutes r).symm
      have hgxs : g.map (algebraMap B T)=∏ i : Fin n, (X-C (xs i.succ)) := by
        apply (monic_X_sub_C (xs 0)).isRegular.left
        have hmap := congrArg (Polynomial.map β.toRingHom) hfac
        rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
          Polynomial.map_C, show β.toRingHom (AdjoinRoot.root f)=xs 0 from hβ] at hmap
        have heq : (f.map (algebraMap R B)).map β.toRingHom =
            f.map (algebraMap R T) := by
          rw [Polynomial.map_map]
          congr 1
          exact β.comp_algebraMap
        rw [heq, hxs, Fin.prod_univ_succ] at hmap
        exact hmap.symm
      obtain ⟨φ, hφ, huniq⟩ := d.universal T (fun i => xs i.succ) hgxs
      refine ⟨φ.restrictScalars R, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · change φ (algebraMap B d.S (AdjoinRoot.root f))=xs 0
          rw [φ.commutes]
          exact hβ
        · exact hφ j
      · intro ψ hψ
        have hc : ψ.toRingHom.comp (algebraMap B d.S)=β.toRingHom := by
          apply AdjoinRoot.ringHom_ext
          · ext r
            change ψ ((algebraMap B d.S) ((algebraMap R B) r))=β ((algebraMap R B) r)
            rw [← IsScalarTower.algebraMap_apply R B d.S, ψ.commutes, β.commutes]
          · change ψ (algebraMap B d.S (AdjoinRoot.root f))=β (AdjoinRoot.root f)
            rw [hβ]
            exact hψ 0
        let ψB : d.S →ₐ[B] T := {
          toRingHom := ψ.toRingHom
          commutes' := fun b => DFunLike.congr_fun hc b }
        have hψB : ψB=φ := huniq ψB (fun i => hψ i.succ)
        ext x
        exact DFunLike.congr_fun hψB x

    · intro e
      change (b.smulTower bd) e =
        (algebraMap B d.S (AdjoinRoot.root f))^e.1.val * powerMonomial n d.roots e.2
      rw [Module.Basis.smulTower_apply,hbd]
      have hb (i : Fin (n+1)) : b i=(AdjoinRoot.root f)^i.val := by
        dsimp only [b]
        rw [Module.Basis.reindex_apply]
        exact (AdjoinRoot.powerBasis' hf).basis_eq_pow _
      rw [hb,Algebra.smul_def,map_pow]

end Lech.UniversalSplitting

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootOverlap
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ProjectiveRoot

open MvPolynomial HomogeneousLocalization ProductSourceCover
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra


lemma product_homogeneous (s : Finset (Fin (n+1))) :
    product R n s ∈ ProjectiveCoefficientChart.grading R n s.card := by
  simpa [product] using IsHomogeneous.prod s (fun j => X (R:=R) j)
    (fun _ => 1) (fun j _ => isHomogeneous_X R j)


end Lech.ProjectiveRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootPositivity
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
open ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (m : Fin n → ℤ) (hgen : Ideal.span (Set.range z)=I)
  (hflat : ∀ p,Module.Flat R (F.X p))

variable [LinearOrder (Chart n)]
  (ell : TorsionLength I)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
  (b : ℤ → ℕ)
  (B : ∀ p,Module.Basis (Fin (b p)) R (F.X p))
  (hp : ∀ p,Module.Projective R (F.X p))
  (hfin : ∀ p,Module.Finite R (F.X p))
  (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
  (hac : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic)


def rootAmbient (s : ℕ) (r : Fin n → ℤ) (l : ℤ) : Fin n → ℤ :=
  baseTwist (n+1) s (fun j => l-1-r j)

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootStageQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ENNReal
namespace Lech.PerfectDomainStages
open Lech.RootTower
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D] [Algebra (MvPowerSeries (Fin h) k) D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]

def rootStageFunctor (n : ℕ) :
    CochainComplex (ModuleCat.{u} D) ℤ ⥤
      CochainComplex (ModuleCat.{u} (PerfectClosure (MvPowerSeries (Fin h) k) p)) ℤ :=
  ((ModuleCat.extendScalars (rootToStage (MvPowerSeries (Fin h) k) D p n)).mapHomologicalComplex _) ⋙
    ((ModuleCat.restrictScalars (algebraMap (PerfectClosure (MvPowerSeries (Fin h) k) p)
      (stage (MvPowerSeries (Fin h) k) D p n))).mapHomologicalComplex _)

instance rootStageFunctor_preservesFiniteColimits (n : ℕ) :
    PreservesFiniteColimits (rootStageFunctor h k D p n) := by
  unfold rootStageFunctor
  infer_instance
instance rootStageFunctor_preservesZero (n : ℕ) :
    (rootStageFunctor h k D p n).PreservesZeroMorphisms := by
  unfold rootStageFunctor
  infer_instance

def stageRootIso (n : ℕ) (F : CochainComplex (ModuleCat.{u} D) ℤ) :
    stageComplex h k D p n F ≅ (rootStageFunctor h k D p n).obj (frobeniusComplex D p n F) :=
  ((ModuleCat.restrictScalars (algebraMap (PerfectClosure (MvPowerSeries (Fin h) k) p)
    (stage (MvPowerSeries (Fin h) k) D p n))).mapHomologicalComplex _).mapIso
      (stageFrobeniusIso (MvPowerSeries (Fin h) k) D p n F)

end Lech.PerfectDomainStages

end

end OAI
end


