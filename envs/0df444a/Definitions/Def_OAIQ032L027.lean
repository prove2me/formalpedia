-- Prove2me | Definitions.Def_OAIQ032L027
-- name    : OAIQ032L027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T20:20:21.876879+00:00
-- url     : https://prove2.me/theorems/610221c2-67a0-4c2a-b43e-18046e628a94
-- title:
--   Definitions bundle OAIQ032L027 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 22 declarations of OpenAI's Lean: 10 definitions and 12 theorems. The definitions and types are `OAI.Lech.ReesRoot.baseModule`, `OAI.Lech.ReesRoot.coefModule`, `OAI.Lech.ReesRoot.reesModule`, `OAI.Lech.RestrictedPolynomialCech.cochainsEquiv`, `OAI.Lech.RestrictedPolynomialCech.complex`, `OAI.Lech.RestrictedPolynomialImageCech.mapCochains`, `OAI.Lech.SourceGraded.exceptionalTermEquiv`, `OAI.Lech.SourceGraded.filteredReduction`, `OAI.Lech.SourceGraded.filteredReductionCochains`, `OAI.Lech.residueExtension`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_ExceptionalFibre`, `Multiplicity_FilteredFractionReesDenominator`, `Multiplicity_FilteredFractionReesDenominatorTheory`, `Multiplicity_GradedChartCochains`, `Multiplicity_LechCokernelComp`, `Multiplicity_LechTorsionOf`, `Multiplicity_ReesExceptionalSquare`, `Multiplicity_ResidueExtension`, `Multiplicity_RootFibreCech`.
--
--   **Imports.** It imports the bundles `OAIQ032L019`, `OAIQ032L020`, `OAIQ032L021`, `OAIQ032L022` and `OAIQ032L023` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ032L029`; the statement `OAI.Lech.ReesRoot.coefficientComparisonLinear_kernel_zero`; the proof of `OAI.Lech.dutta_domain`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ032L019
import Definitions.Def_OAIQ032L020
import Definitions.Def_OAIQ032L021
import Definitions.Def_OAIQ032L022
import Definitions.Def_OAIQ032L023

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechTorsionOf
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ} (z : Fin h → R)
  (hz : Ideal.span (Set.range z) = I)
attribute [local instance] MvPolynomial.gradedAlgebra

lemma mapR_surjective : Function.Surjective (mapR I z hz) :=
  IdealGraded.polynomialMap_surjective I z hz

attribute [local instance] Homogeneous.awayAddCommGroup
attribute [local instance] kernel_addCommGroup kernel_module

end Lech.SourceGraded


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_GradedChartCochains
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.RestrictedPolynomialCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex SetLike
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
attribute [local instance] MvPolynomial.gradedAlgebra

def cochainsEquiv (h n t : ℕ) : cochains R S h n t ≃ₗ[R]
    PartialLaurent.polynomialCochains S h n t :=
  LinearEquiv.piCongrRight (fun a => termEquiv R S h (ActualCech.intersection a) t)

lemma cochainsEquiv_d (h n t : ℕ) (f : cochains R S h n t) :
    cochainsEquiv R S h (n+1) t (d R S h n t f) =
      PartialLaurent.polynomialD S h n t (cochainsEquiv R S h n t f) := by
  funext a
  change termEquiv R S h (ActualCech.intersection a) t
    (∑ i : Fin (n+1), (-1 : R)^i.val • GradedChart.restrict _ _ _
      (ActualCech.intersection_delete a i) t (f (a ∘ i.succAbove))) = _
  simp only [map_sum,map_smul,termEquiv_naturality]
  change (∑ i : Fin (n+1), (-1 : R)^i.val • _) = ∑ i : Fin (n+1), (-1 : S)^i.val • _
  apply Finset.sum_congr rfl
  intro i _
  rw [← IsScalarTower.algebraMap_smul S, map_pow,map_neg,map_one]
  rfl

lemma d_square (h n t : ℕ) (f : cochains R S h n t) :
    d R S h (n+1) t (d R S h n t f)=0 := by
  apply (cochainsEquiv R S h (n+2) t).injective
  rw [cochainsEquiv_d,cochainsEquiv_d,PartialLaurent.polynomialD_square,map_zero]

def complex (h t : ℕ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (cochains R S h n t))
    (fun n => ModuleCat.ofHom (d R S h n t)) (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact d_square R S h n t f)

end Lech.RestrictedPolynomialCech


namespace Lech.RestrictedPolynomialImageCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex SetLike
universe u
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]
  {h : ℕ} (H : ℕ → Submodule R B) [GradedAlgebra H]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (g : (RestrictedPolynomialCech.grade R S h) →+*ᵍ H)
  (hg : ∀ (r : R) (a : MvPolynomial (Fin h) S), g (r • a) = r • g a)

def mapCochains (n t : ℕ) : RestrictedPolynomialCech.cochains R S h n t →ₗ[R] cochains H g n t :=
  ImageCech.mapCochains _ H g hg MvPolynomial.X (MvPolynomial.isHomogeneous_X S) n t

lemma mapCochains_surjective (hsurj : Function.Surjective g) (n t : ℕ) :
    Function.Surjective (mapCochains H g hg n t) :=
  ImageCech.mapCochains_surjective _ H g hg MvPolynomial.X
    (MvPolynomial.isHomogeneous_X S) hsurj n t

end Lech.RestrictedPolynomialImageCech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredFractionReesDenominator
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.projectiveAlgebra _root_.OAI.Lech.ReesRoot.projectiveTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.SourceGraded
open Lech.IdealGraded SetLike Graded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)

lemma mapR_X (i : Fin h) : mapR I z hz (MvPolynomial.X i)=generator I z hz i := by
  change MvPolynomial.aeval (generator I z hz) (MvPolynomial.X i)=_
  exact MvPolynomial.aeval_X _ _


lemma image_denominator_rees (s : Finset (Fin h)) :
    mapR I z hz (GradedChart.denominator MvPolynomial.X s) =
      FilteredFraction.quotientGraded I (FilteredFraction.reesDenominator I
        (FilteredCech.denominator_mem I z (coordinate_mem I z hz) s)) := by
  classical
  unfold GradedChart.denominator
  rw [map_prod]
  simp only [mapR_X]
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty,Finset.card_empty]
      change 1=Ideal.Quotient.mk (shifted I) (monomial I 0 ⟨1,_⟩)
      rw [show monomial I 0 ⟨1,by simp⟩=(1:reesAlgebra I) by
        apply Subtype.ext; change Polynomial.monomial 0 (1:R)=1; simp]
      exact (map_one _).symm
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi,ih]
      change Ideal.Quotient.mk (shifted I) (monomial I 1 ⟨z i,_⟩) *
        Ideal.Quotient.mk (shifted I) (monomial I s.card ⟨∏ j ∈ s,z j,_⟩) =
        Ideal.Quotient.mk (shifted I) (monomial I (insert i s).card ⟨∏ j ∈ insert i s,z j,_⟩)
      rw [←map_mul]
      congr 1
      apply Subtype.ext
      change Polynomial.monomial 1 (z i) * Polynomial.monomial s.card (∏ j ∈ s,z j)=
        Polynomial.monomial (insert i s).card (∏ j ∈ insert i s,z j)
      rw [Polynomial.monomial_mul_monomial,Finset.card_insert_of_notMem hi,Finset.prod_insert hi,Nat.add_comm 1]

attribute [local irreducible] TwistedLocalization.piece FilteredFraction.quotientGraded


def exceptionalTermEquiv (s : Finset (Fin h)) (t : ℕ) :
    FilteredFraction.exceptionalPiece I
      (FilteredCech.denominator_mem I z (coordinate_mem I z hz) s) t ≃ₗ[R]
    ImageCech.term (R := R) (A := MvPolynomial (Fin h) (R ⧸ I)) (B := IdealGraded.Ring I) (sourceGrade I h) (targetGrade I) (mapR I z hz)
      MvPolynomial.X s t :=
  TwistedLocalization.pieceCongr (R := R) (A := IdealGraded.Ring I) (targetGrade I)
    (f := FilteredFraction.quotientGraded I (FilteredFraction.reesDenominator I (FilteredCech.denominator_mem I z (coordinate_mem I z hz) s)))
    (q := mapR I z hz (GradedChart.denominator MvPolynomial.X s)) (d := s.card) (e := s.card)
    (image_denominator_rees I z hz s).symm rfl t


def filteredReduction (s : Finset (Fin h)) (t : ℕ) :
    FilteredCech.term I z t s →ₗ[R]
      ImageCech.term (R := R) (A := MvPolynomial (Fin h) (R ⧸ I)) (B := IdealGraded.Ring I) (sourceGrade I h) (targetGrade I) (mapR I z hz)
        MvPolynomial.X s t :=
  (exceptionalTermEquiv I z hz s t).toLinearMap.comp
    (FilteredFraction.layerMap I (FilteredCech.denominator_mem I z (coordinate_mem I z hz) s) t)

lemma filteredReduction_kernel (s : Finset (Fin h)) (t : ℕ) :
    (filteredReduction I z hz s t).ker =
      (FilteredCech.term I z (t+1) s).comap (FilteredCech.term I z t s).subtype := by
  rw [filteredReduction,LinearMap.ker_comp_of_ker_eq_bot _
    (LinearMap.ker_eq_bot.mpr (exceptionalTermEquiv I z hz s t).injective)]
  exact FilteredFraction.layerMap_kernel I (FilteredCech.denominator_mem I z (coordinate_mem I z hz) s) t
end Lech.SourceGraded


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredFractionReesDenominatorTheory
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.projectiveAlgebra _root_.OAI.Lech.ReesRoot.projectiveTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.SourceGraded
open Lech.IdealGraded SetLike Graded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] TwistedLocalization.piece FilteredFraction.quotientGraded

lemma exceptionalTermEquiv_restrict {s v : Finset (Fin h)} (hsv : s ⊆ v) (t : ℕ)
    (x : FilteredFraction.exceptionalPiece I
      (FilteredCech.denominator_mem I z (coordinate_mem I z hz) s) t) :
    exceptionalTermEquiv I z hz v t
      (FilteredFraction.exceptionalRestrict I
        (FilteredCech.denominator_mem I z (coordinate_mem I z hz) s)
        (FilteredCech.denominator_mem I z (coordinate_mem I z hz) v)
        (FilteredCech.denominator_mem I z (coordinate_mem I z hz) (v\s))
        (GradedChart.denominator_mul_sdiff z hsv)
        (by rw [Nat.add_comm,Finset.card_sdiff_add_card_eq_card hsv]) t x) =
    ImageCech.restrict (R := R) (A := MvPolynomial (Fin h) (R ⧸ I)) (B := IdealGraded.Ring I) (sourceGrade I h) (targetGrade I) (mapR I z hz)
      MvPolynomial.X (MvPolynomial.isHomogeneous_X (R ⧸ I)) hsv t
      (exceptionalTermEquiv I z hz s t x) := by
  unfold exceptionalTermEquiv FilteredFraction.exceptionalRestrict TwistedLocalization.imagePieceTo ImageCech.restrict
  apply TwistedLocalization.pieceCongr_pieceTo


lemma filteredReduction_naturality {s v : Finset (Fin h)} (hsv : s ⊆ v) (t : ℕ)
    (x : FilteredCech.term I z t s) :
    filteredReduction I z hz v t
      (LocalizationCech.restrict z (FilteredCech.term I z t)
        (FilteredCech.restriction_mem I z (coordinate_mem I z hz) t) hsv x) =
    ImageCech.restrict (R := R) (A := MvPolynomial (Fin h) (R ⧸ I)) (B := IdealGraded.Ring I) (sourceGrade I h) (targetGrade I) (mapR I z hz)
      MvPolynomial.X (MvPolynomial.isHomogeneous_X (R ⧸ I)) hsv t
      (filteredReduction I z hz s t x) := by
  change exceptionalTermEquiv I z hz v t
    (FilteredFraction.layerMap I (FilteredCech.denominator_mem I z (coordinate_mem I z hz) v) t
      (FilteredFraction.restrict I
        (FilteredCech.denominator_mem I z (coordinate_mem I z hz) s)
        (FilteredCech.denominator_mem I z (coordinate_mem I z hz) (v\s))
        (GradedChart.denominator_mul_sdiff z hsv)
        (by rw [Nat.add_comm,Finset.card_sdiff_add_card_eq_card hsv]) t x)) = _
  rw [FilteredFraction.layerMap_naturality I
    (FilteredCech.denominator_mem I z (coordinate_mem I z hz) s)
    (FilteredCech.denominator_mem I z (coordinate_mem I z hz) v)]
  exact exceptionalTermEquiv_restrict I z hz hsv t _
end Lech.SourceGraded


open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechCokernelComp
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex SetLike Graded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] TwistedLocalization.piece FilteredFraction.piece IdealGraded.polynomialMap

 
def filteredReductionCochains (n t : ℕ) :
    LocalizationCech.cochains z (FilteredCech.term I z t) n →ₗ[R]
      RestrictedPolynomialImageCech.cochains (R := R) (S := R ⧸ I) (B := IdealGraded.Ring I) (h := h)
        (targetGrade I) (mapR I z hz) n t :=
  LinearMap.pi (fun a => (filteredReduction I z hz (ActualCech.intersection a) t).comp
    (LinearMap.proj a))

lemma filteredReductionCochains_d (n t : ℕ)
    (x : LocalizationCech.cochains z (FilteredCech.term I z t) n) :
    filteredReductionCochains I z hz (n+1) t
      (LocalizationCech.d z (FilteredCech.term I z t)
        (FilteredCech.restriction_mem I z (coordinate_mem I z hz) t) n x) =
    RestrictedPolynomialImageCech.d (R := R) (S := R ⧸ I) (B := IdealGraded.Ring I) (h := h)
      (targetGrade I) (mapR I z hz) n t (filteredReductionCochains I z hz n t x) := by
  funext a
  change filteredReduction I z hz (ActualCech.intersection a) t
    (∑ i : Fin (n+1), (-1:R)^i.val •
      LocalizationCech.restrict z (FilteredCech.term I z t)
        (FilteredCech.restriction_mem I z (coordinate_mem I z hz) t)
        (ActualCech.intersection_delete a i) (x (a ∘ i.succAbove))) = _
  apply linearMap_sum_smul
  intro i
  exact filteredReduction_naturality I z hz (ActualCech.intersection_delete a i) t (x (a ∘ i.succAbove))


lemma filteredReductionCochains_kernel (n t : ℕ) :
    (filteredReductionCochains I z hz n t).ker =
      (LocalizationCech.inclusionLinear z (FilteredCech.term I z (t+1))
        (FilteredCech.term I z t) (fun _ => FilteredFraction.antitone I _ _ (Nat.le_succ t)) n).range := by
  ext x
  constructor
  · intro hx
    have hx' : ∀ a, (x a).val ∈ FilteredCech.term I z (t+1) (ActualCech.intersection a) := by
      intro a
      have ha : x a ∈ (filteredReduction I z hz (ActualCech.intersection a) t).ker :=
        congrFun hx a
      rw [filteredReduction_kernel] at ha
      exact ha
    exact ⟨fun a => ⟨(x a).val,hx' a⟩,rfl⟩
  · rintro ⟨y,rfl⟩
    change filteredReductionCochains I z hz n t
      (LocalizationCech.inclusionLinear z (FilteredCech.term I z (t+1))
        (FilteredCech.term I z t) (fun _ => FilteredFraction.antitone I _ _ (Nat.le_succ t)) n y)=0
    funext a
    apply (show _ ∈ (filteredReduction I z hz (ActualCech.intersection a) t).ker from ?_)
    rw [filteredReduction_kernel]
    exact (y a).property

end Lech.SourceGraded


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesExceptionalSquare
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open MvPolynomial HomogeneousLocalization IdealGraded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (hgen : Ideal.span (Set.range z)=I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

attribute [local instance] OAI.Lech.ReesRoot.concreteRing_p2
local instance baseModule_p1 (s : Finset (Fin (n+1))) : Module R (Ring I z hz s) :=
  Homogeneous.module (reesGrade I) (Submonoid.powers (denominator I z hz s))

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ExceptionalFibre
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory IdealGraded HomogeneousLocalization
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (hgen : Ideal.span (Set.range z)=I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
attribute [local instance] OAI.Lech.ReesRoot.coefRing
local instance coefModule (s : Finset (Fin (n+1))) : Module R (CoefficientRing I s) :=
  Homogeneous.module (SourceGraded.sourceGrade I (n+1)) (Submonoid.powers (coefficientDenominator I s))

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ResidueExtension
attribute [-instance] _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open IsLocalRing TensorProduct
namespace Lech
universe u
attribute [instance] ResidueExtension.commRing ResidueExtension.localRing
  ResidueExtension.noetherian ResidueExtension.algebra ResidueExtension.flat
  ResidueExtension.complete ResidueExtension.algClosed

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  (p : ℕ) [Fact p.Prime] [CharP R p] [IsAdicComplete (maximalIdeal R) R]

 

def residueExtension : ResidueExtension R := by
  let k := R ⧸ maximalIdeal R
  letI : Field k := Ideal.Quotient.field _
  let φ := ArbitraryCoefficientField.localSection R p
  letI : Algebra k R := φ.toAlgebra
  have hres : Function.Bijective (algebraMap k (ResidueField R)) := by
    have h : ∀ a : k,algebraMap k (ResidueField R) a=a :=
      ArbitraryCoefficientField.localSection_rightInverse R p
    exact ⟨fun a b hab => (h a).symm.trans (hab.trans (h b)), fun a => ⟨a,h a⟩⟩
  let K := AlgebraicClosure k
  let T := R ⊗[k] K
  letI : IsLocalRing T := ResidueTensor.isLocal k R K hres
  have hmax : (maximalIdeal R).map (algebraMap R T)=maximalIdeal T :=
    (ResidueTensor.maximalIdeal_eq_map k R K hres).symm
  have fg : (maximalIdeal T).FG := hmax ▸ (maximalIdeal R).fg_of_isNoetherianRing.map _
  let ψ : K →+* T := (Algebra.TensorProduct.includeRight (R:=k) (A:=R)).toRingHom
  have hψ : Function.Surjective ((residue T).comp ψ) :=
    ResidueTensor.residue_surjective k R K hres hmax.symm
  let S := AdicCompletion (maximalIdeal T) T
  letI : IsLocalRing S := AdicCompletion.isLocalRing_of_fg fg
  letI : IsNoetherianRing S := ResidueCompletion.noetherian fg ψ hψ
  letI : IsAdicComplete (maximalIdeal S) S := AdicCompletion.isAdicComplete_of_fg fg
  letI : IsScalarTower R T S := IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.Free R T := inferInstance
  letI : Module.Flat R S := ResidueCompletion.flat hmax inferInstance
  have hmaxS : (maximalIdeal R).map (algebraMap R S)=maximalIdeal S := by
    rw [AdicCompletion.maximalIdeal_eq_map_of_fg fg]
    calc
      (maximalIdeal R).map (algebraMap R S)=
          ((maximalIdeal R).map (algebraMap R T)).map (algebraMap T S) := by
            rw [Ideal.map_map]
            rfl
      _ = (maximalIdeal T).map (algebraMap T S) := congrArg (Ideal.map (algebraMap T S)) hmax
  let e : K ≃+* ResidueField S := RingEquiv.ofBijective
    ((residue S).comp (ResidueCompletion.coefficient ψ))
    ⟨RingHom.injective _,ResidueCompletion.coefficient_surjective fg ψ hψ⟩
  exact ⟨S,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,
    inferInstance,hmaxS,IsAlgClosed.of_ringEquiv K (ResidueField S) e⟩

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootFibreCech
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
attribute [local instance] OAI.Lech.ReesRoot.reesRing_p2
local instance reesModule_p2 (s : Finset (Fin (n+1))) : Module R (Ring I z hz s) :=
  Homogeneous.module (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))
attribute [local instance] OAI.Lech.ReesRoot.reesBaseAlgebra_p2
local instance reesScalarComm_p2 (s : Finset (Fin (n+1))) :
    SMulCommClass (ProjectiveRoot.Ring R n s) R (Ring I z hz s) where
  smul_comm a r b := by simp only [Algebra.smul_def]; exact mul_left_comm _ _ _

end Lech.ReesRoot

end

end OAI
end


