-- Prove2me | Definitions.Def_OAIQ032L012
-- name    : OAIQ032L012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T19:50:49.097162+00:00
-- url     : https://prove2.me/theorems/55633d14-484b-4f1a-9d5d-e3d9fe30ceac
-- title:
--   Definitions bundle OAIQ032L012 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 134 declarations of OpenAI's Lean: 69 definitions, 9 instances and 56 theorems. The definitions and types are `OAI.Lech.FilteredCech.augmentationIso`, `OAI.Lech.FilteredCech.augmentationRingIso`, `OAI.Lech.FilteredCech.augmented`, `OAI.Lech.FilteredCech.bicRowHomotopy`, `OAI.Lech.FilteredCech.bicRowHomotopyAt`, `OAI.Lech.FilteredCech.cochainHomotopy`, `OAI.Lech.FilteredCech.cochainPiIso`, `OAI.Lech.FilteredCech.complex`, `OAI.Lech.FilteredCech.diagram`, `OAI.Lech.FilteredCech.inclusion`, `OAI.Lech.FilteredCech.intersectionHomotopy`, `OAI.Lech.FilteredCech.positive`, `OAI.Lech.FilteredCech.positiveInclusion`, `OAI.Lech.FilteredCech.positiveRowHomotopy`, `OAI.Lech.FilteredCech.positiveXIso`, `OAI.Lech.FilteredCech.shiftedPositive`, `OAI.Lech.FilteredCech.twistStep`, `OAI.Lech.FilteredFraction.ExceptionalChart`, `OAI.Lech.FilteredFraction.ReesChart`, `OAI.Lech.FilteredFraction.chartAmbient`, `OAI.Lech.FilteredFraction.exceptionalPiece`, `OAI.Lech.FilteredFraction.quotientGraded`, `OAI.Lech.FilteredFraction.quotientTwist`, `OAI.Lech.FilteredFraction.reesAmbient`, `OAI.Lech.FilteredFraction.reesChartCommRing`, `OAI.Lech.FilteredFraction.reesChartModule`, `OAI.Lech.FilteredFraction.reesDenominator`, `OAI.Lech.FilteredFraction.reesEquiv`, `OAI.Lech.FilteredFraction.reesMap`, `OAI.Lech.FiniteComplex.dropShortComplex`, `OAI.Lech.FiniteComplex.dropShortComplexMap`, `OAI.Lech.Homogeneous.toZeroPiece`, `OAI.Lech.IdealGraded.grade`, `OAI.Lech.IdealGraded.polynomialMap`, `OAI.Lech.LocalizationCech.augmentationIso`, `OAI.Lech.LocalizationCech.cochains`, `OAI.Lech.LocalizationCech.complex`, `OAI.Lech.LocalizationCech.d`, `OAI.Lech.LocalizationCech.inclusion`, `OAI.Lech.LocalizationCech.inclusionLinear` and 29 more.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_FilteredCechAugmentationRing`, `Multiplicity_FilteredCechAugmented`, `Multiplicity_FilteredFractionReesDenominator`, `Multiplicity_FilteredFractionReesDenominatorTheory`, `Multiplicity_HomogeneousZeroPiece`, `Multiplicity_IdealGradedRing`, `Multiplicity_LechBoundedEquiv`, `Multiplicity_LechCokernelComp`, `Multiplicity_LechHomogeneousEval`, `Multiplicity_LechMapCochain`, `Multiplicity_LechPiIso`, `Multiplicity_LechTorsionOf`, `Multiplicity_PrimitiveChartFaithfullyFlat`, `Multiplicity_ProductSourceCoverRootSigned`, `Multiplicity_ReesExceptionalRing`, `Multiplicity_ReesRootMap`, `Multiplicity_RestrictedPolynomialImageCechComparisonHomology`, `Multiplicity_RootOverlap`, `Multiplicity_ScalarCechShift`, `Multiplicity_ScalarChartComparison`, `Multiplicity_SourceGradedThickeningNat`, `Multiplicity_TensorTotalHomologyProperty`, `Multiplicity_TotalGhostRowHom`.
--
--   **Imports.** It imports the bundles `OAIQ032L000`, `OAIQ032L002`, `OAIQ032L003` and `OAIQ032L004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ032L020`, `OAIQ032L021`, `OAIQ032L022` and `OAIQ032L023`; the statements `OAI.Lech.FilteredCech.positive_homology_powerTorsion`, `OAI.Lech.LinearNormalization.generator_number_le_dimension`, `OAI.Lech.SourceGraded.exists_uniform_geometric_stableImage` and `OAI.Lech.SourceGraded.finiteThickening_homology_zeroClass`; the proof of `OAI.Lech.SourceGraded.exists_uniform_geometric_stableImage`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ032L000
import Definitions.Def_OAIQ032L002
import Definitions.Def_OAIQ032L003
import Definitions.Def_OAIQ032L004

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechBoundedEquiv
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.IdealGraded.gradedAlgebra _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
open scoped Classical
variable {R : Type*} [CommRing R] (I : Ideal R)

lemma reesDecompose_support (p : reesAlgebra I) :
    (reesDecompose I p).support = (p : R[X]).support := by
  classical
  ext i
  simp only [DFinsupp.mem_support_iff, Polynomial.mem_support_iff, reesDecompose_apply]
  have he : component I i p = 0 ↔ (p : R[X]).coeff i = 0 := by
    rw [← Subtype.val_inj, ← Subtype.val_inj]
    simp only [component_coe, ZeroMemClass.coe_zero, Polynomial.monomial_eq_zero_iff]
  exact not_congr he

noncomputable instance reesDecomposition : Decomposition (reesGrade I) :=
  Decomposition.ofLinearMap _ (reesDecompose I)
    (by
      classical
      apply LinearMap.ext
      intro p
      apply Subtype.ext
      rw [LinearMap.comp_apply, DirectSum.coeLinearMap_eq_dfinsuppSum]
      change (∑ i ∈ (reesDecompose I p).support,
        (reesDecompose I p i : reesAlgebra I) : reesAlgebra I).val = (p : R[X])
      rw [reesDecompose_support]
      change (reesAlgebra I).val (∑ i ∈ (p : R[X]).support,
        (reesDecompose I p i : reesAlgebra I)) = (p : R[X])
      rw [map_sum]
      simp only [reesDecompose_apply]
      exact (Polynomial.as_sum_support p.val).symm)
    (by
      apply DirectSum.linearMap_ext
      intro i
      apply LinearMap.ext
      rintro ⟨p, x, rfl⟩
      simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, LinearMap.id_apply]
      change reesDecompose I (monomial I i x) = _
      convert reesDecompose_monomial I i x using 1
      all_goals try with_reducible_and_instances rfl
      rfl)

@[simp] lemma rees_decompose_val (p : reesAlgebra I) (i : ℕ) :
    ((decompose (reesGrade I) p i : reesAlgebra I) : R[X]) =
      Polynomial.monomial i (p.val.coeff i) := rfl


lemma shifted_homogeneous : SetLike.IsHomogeneous (reesGrade I) (shifted I) := by
  intro i p hp j
  change (Polynomial.monomial i (p.val.coeff i)).coeff j ∈ I ^ (j + 1)
  by_cases hij : i = j
  · subst j
    simpa using hp i
  · simp [Polynomial.coeff_monomial, hij]

end Lech.IdealGraded
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealGradedRing
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

instance gradedTower : IsScalarTower R (R ⧸ I) (Ring I) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

lemma quotientR_ker_homogeneous : (quotientR I).ker.IsHomogeneous (reesGrade I) := by
  rw [LinearMap.ker_restrictScalars, Submodule.ker_mkQ]
  exact shifted_homogeneous I

noncomputable instance imageGrading : Decomposition (Grading.imagePiece (reesGrade I) (quotientR I)) :=
  Grading.imageDecomposition (reesGrade I) (quotientR I)
    (shifted I).mkQ_surjective (quotientR_ker_homogeneous I)

def grade (i : ℕ) : Submodule (R ⧸ I) (Ring I) where
  toAddSubmonoid := (Grading.imagePiece (reesGrade I) (quotientR I) i).toAddSubmonoid
  smul_mem' a x hx := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    change r • x ∈ _
    exact (Grading.imagePiece (reesGrade I) (quotientR I) i).smul_mem r hx

noncomputable instance gradeDecomposition : Decomposition (grade I) where
  decompose' := decompose (Grading.imagePiece (reesGrade I) (quotientR I))
  left_inv := (decompose (Grading.imagePiece (reesGrade I) (quotientR I))).left_inv
  right_inv := (decompose (Grading.imagePiece (reesGrade I) (quotientR I))).right_inv

lemma grade_mul {i j : ℕ} {x y : Ring I} (hx : x ∈ grade I i) (hy : y ∈ grade I j) :
    x * y ∈ grade I (i + j) := by
  obtain ⟨_, ⟨a, rfl⟩, rfl⟩ := hx
  obtain ⟨_, ⟨b, rfl⟩, rfl⟩ := hy
  let c : ↥(I ^ (i + j)) := ⟨(a : R) * (b : R), by
    rw [pow_add]; exact Ideal.mul_mem_mul a.property b.property⟩
  refine ⟨monomial I (i + j) c, ⟨c, rfl⟩, ?_⟩
  change Ideal.Quotient.mk (shifted I) (monomial I (i + j) c) =
    Ideal.Quotient.mk (shifted I) (monomial I i a) *
      Ideal.Quotient.mk (shifted I) (monomial I j b)
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  exact (Polynomial.monomial_mul_monomial _ _ _ _).symm

end Lech.IdealGraded


namespace Lech.IdealGraded
open Polynomial DirectSum
variable {R : Type*} [CommRing R] (I : Ideal R)
noncomputable instance gradeGradedAlgebra : GradedAlgebra (grade I) where
  toDecomposition := gradeDecomposition I
  one_mem := by
    refine ⟨1, ?_, map_one (Ideal.Quotient.mk (shifted I))⟩
    exact ⟨⟨1, by simp⟩, by apply Subtype.ext; change Polynomial.monomial 0 (1 : R) = 1; simp⟩
  mul_mem := fun _ _ _ _ hx hy => grade_mul I hx hy

variable {ι : Type*} (z : ι → R) (hz : Ideal.span (Set.range z) = I)
lemma generator_mem (j : ι) : generator I z hz j ∈ grade I 1 :=
  ⟨_,⟨_,rfl⟩,rfl⟩

attribute [local instance] MvPolynomial.gradedAlgebra
 
def polynomialMap : MvPolynomial.homogeneousSubmodule ι (R ⧸ I) →+*ᵍ grade I :=
  Grading.polynomialMap (grade I) (generator I z hz) (generator_mem I z hz)

end Lech.IdealGraded


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechTorsionOf
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
namespace Lech
open CategoryTheory CategoryTheory.Limits MvPolynomial
universe u
variable {R : Type u} [CommRing R]

namespace SourceGraded
variable (I : Ideal R) {h : ℕ} (z : Fin h → R) (hz : Ideal.span (Set.range z) = I)
attribute [local instance] MvPolynomial.gradedAlgebra

lemma polynomialMap_smul (r : R ⧸ I) (a : MvPolynomial (Fin h) (R ⧸ I)) :
    IdealGraded.polynomialMap I z hz (r • a) =
      r • IdealGraded.polynomialMap I z hz a := by
  exact (aeval (IdealGraded.generator I z hz) :
    MvPolynomial (Fin h) (R ⧸ I) →ₐ[R ⧸ I] IdealGraded.Ring I).toLinearMap.map_smul r a

noncomputable def degreeMap (n : ℕ) :
    homogeneousSubmodule (Fin h) (R ⧸ I) n →ₗ[R ⧸ I] IdealGraded.grade I n :=
  Homogeneous.gradedMap (R := R ⧸ I) (A := MvPolynomial (Fin h) (R ⧸ I))
    (B := IdealGraded.Ring I) (homogeneousSubmodule (Fin h) (R ⧸ I)) (IdealGraded.grade I)
    (IdealGraded.polynomialMap I z hz) (polynomialMap_smul I z hz) n

variable (ell : TorsionLength I)

local instance kernel_addCommGroup (n : ℕ) :
    AddCommGroup ((degreeMap I z hz n).restrictScalars R).ker :=
  Submodule.addCommGroup (R := R)
    (M := homogeneousSubmodule (Fin h) (R ⧸ I) n)
    ((degreeMap I z hz n).restrictScalars R).ker
local instance kernel_module (n : ℕ) :
    Module R ((degreeMap I z hz n).restrictScalars R).ker :=
  Submodule.module (R := R)
    (M := homogeneousSubmodule (Fin h) (R ⧸ I) n)
    ((degreeMap I z hz n).restrictScalars R).ker

end SourceGraded
end Lech

attribute [local instance] Classical.propDecidable


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ} (z : Fin h → R)
  (hz : Ideal.span (Set.range z) = I)
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev targetGrade (n : ℕ) : Submodule R (IdealGraded.Ring I) :=
  (IdealGraded.grade I n).restrictScalars R
instance target_graded : GradedAlgebra (targetGrade I) := inferInstanceAs
  (GradedAlgebra (fun n => (IdealGraded.grade I n).restrictScalars R))

attribute [local instance] Homogeneous.awayAddCommGroup
attribute [local instance] kernel_addCommGroup kernel_module

end Lech.SourceGraded


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechPiIso
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


variable (G : ℕ → Submodule R A) [GradedAlgebra G]
  {f q c : A} {d e k : ℕ} (hf : f ∈ G d) (hc : c ∈ G k)
  (hfc : f*c=q) (hdeg : d+k=e)

variable (H : ℕ → Submodule R B) [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A), g (r • a) = r • g a)

omit [GradedAlgebra G] [GradedAlgebra H] in
@[simp] lemma ambientMap_algebraMap {f : A} (a : A) :
    ambientMap G H g hg (algebraMap A (Localization.Away f) a) =
      algebraMap B (Localization.Away (g f)) (g a) := by
  simp only [ambientMap,IsLocalization.Away.mapₐ_apply,IsLocalization.Away.map,
    IsLocalization.map_eq,algHom,RingHom.coe_mk,MonoidHom.coe_mk,OneHom.coe_mk]

end Lech.TwistedLocalization

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RestrictedPolynomialImageCechComparisonHomology
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.LocalizationCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {h : ℕ} (y : Fin h → A)
variable (F : (s : Finset (Fin h)) → Submodule R (ambient y s))
  (hF : ∀ {s v : Finset (Fin h)} (hsv : s ⊆ v) (x : F s),
    TwistedLocalization.ambientTo (R := R) (GradedChart.denominator_dvd y hsv) x ∈ F v)


abbrev cochains (n : ℕ) := (a : Fin n → Fin h) → F (ActualCech.intersection a)

 
def d (n : ℕ) : cochains y F n →ₗ[R] cochains y F (n+1) where
  toFun f a := ∑ i : Fin (n+1), (-1:R)^i.val •
    restrict y F hF (ActualCech.intersection_delete a i) (f (a ∘ i.succAbove))
  map_add' f g := by
    funext a
    simp only [Pi.add_apply,map_add,smul_add,Finset.sum_add_distrib]
  map_smul' r f := by
    funext a
    simp only [Pi.smul_apply,map_smul,RingHom.id_apply,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _

lemma intersection_comp_subset {N n : ℕ} (a : Fin N → Fin h) (b : Fin n → Fin N) :
    ActualCech.intersection (a ∘ b) ⊆ ActualCech.intersection a := by
  classical
  intro i hi
  simp only [ActualCech.intersection,Finset.mem_image,Finset.mem_univ,true_and] at hi ⊢
  obtain ⟨j,rfl⟩ := hi
  exact ⟨b j,rfl⟩

 
def toFixed {N n : ℕ} (a : Fin N → Fin h) (f : cochains y F n) :
    ActualCech.Row (ambient y (ActualCech.intersection a)) (ι := Fin N) n := fun b =>
  TwistedLocalization.ambientTo (R := R)
    (GradedChart.denominator_dvd y (intersection_comp_subset a b)) (f (a ∘ b)).val

lemma toFixed_self {n : ℕ} (a : Fin n → Fin h) (f : cochains y F n) :
    toFixed y F a f id=(f a).val := by
  change TwistedLocalization.ambientTo (R := R)
    (GradedChart.denominator_dvd y (intersection_comp_subset a id)) (f (a ∘ id)).val = _
  simp only [Function.comp_id]
  rw [TwistedLocalization.ambientTo_self]
  rfl

lemma toFixed_d {N n : ℕ} (a : Fin N → Fin h) (f : cochains y F n) :
    toFixed y F a (d y F hF n f) =
      ActualCech.delta (ambient y (ActualCech.intersection a)) n (toFixed y F a f) := by
  funext b
  change TwistedLocalization.ambientTo (R := R)
    (GradedChart.denominator_dvd y (intersection_comp_subset a b))
    ((∑ i : Fin (n+1), (-1:R)^i.val •
      restrict y F hF (ActualCech.intersection_delete (a ∘ b) i)
        (f ((a ∘ b) ∘ i.succAbove))).val) = _
  simp only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul]
  change (∑ i : Fin (n+1), _) = ∑ i : Fin (n+1), _
  apply Finset.sum_congr rfl
  intro i _
  have he := AlgHom.congr_fun (TwistedLocalization.ambientTo_comp (R := R)
    (GradedChart.denominator_dvd y (ActualCech.intersection_delete (a ∘ b) i))
    (GradedChart.denominator_dvd y (intersection_comp_subset a b)))
    (f ((a ∘ b) ∘ i.succAbove)).val
  change (-1:R)^i.val • ((TwistedLocalization.ambientTo (R := R)
    (GradedChart.denominator_dvd y (intersection_comp_subset a b))).comp
    (TwistedLocalization.ambientTo (R := R)
      (GradedChart.denominator_dvd y (ActualCech.intersection_delete (a ∘ b) i))))
      (f ((a ∘ b) ∘ i.succAbove)).val = _
  rw [he]
  simp only [Algebra.smul_def,map_pow,map_neg,map_one]
  rfl


lemma d_square (n : ℕ) (f : cochains y F n) :
    d y F hF (n+1) (d y F hF n f)=0 := by
  funext a
  apply Subtype.ext
  have he : toFixed y F a (d y F hF (n+1) (d y F hF n f))=0 := by
    rw [toFixed_d,toFixed_d,ActualCech.delta_square]
  have ha := congrFun he id
  rw [toFixed_self] at ha
  exact ha

 
def complex : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (cochains y F n))
    (fun n => ModuleCat.ofHom (d y F hF n)) (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact d_square y F hF n f)
end Lech.LocalizationCech


namespace Lech.IdealGraded
open Polynomial DirectSum
variable {R : Type*} [CommRing R] (I : Ideal R)

lemma monomial_mul (i j : ℕ) (a : ↥(I^i)) (b : ↥(I^j)) :
    monomial I i a * monomial I j b = monomial I (i+j)
      ⟨(a:R)*(b:R),by rw [pow_add]; exact Ideal.mul_mem_mul a.2 b.2⟩ := by
  apply Subtype.ext
  exact Polynomial.monomial_mul_monomial _ _ _ _

instance reesGradedAlgebra : GradedAlgebra (reesGrade I) where
  toDecomposition := reesDecomposition I
  one_mem := by
    refine ⟨⟨1,by simp⟩,?_⟩
    apply Subtype.ext
    simp
  mul_mem := by
    intro i j a b ha hb
    obtain ⟨x,rfl⟩ := ha
    obtain ⟨y,rfl⟩ := hb
    exact ⟨⟨(x:R)*(y:R),by rw [pow_add]; exact Ideal.mul_mem_mul x.2 y.2⟩,
      (monomial_mul I i j x y).symm⟩


@[simp] lemma evaluate_monomial (i : ℕ) (a : ↥(I^i)) :
    evaluate I (monomial I i a) = (a:R) := by
  change Polynomial.eval₂ (algebraMap R R) 1 (Polynomial.monomial i (a:R)) = _
  simp

end Lech.IdealGraded


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredFractionReesDenominator
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
namespace Lech.FilteredFraction

section
open Lech.IdealGraded SetLike Graded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {w : R} {d : ℕ} (hw : w ∈ I^d)


abbrev reesDenominator : reesAlgebra I := monomial I d ⟨w,hw⟩
lemma reesDenominator_mem : reesDenominator I hw ∈ reesGrade I d := ⟨⟨w,hw⟩,rfl⟩

 
def reesAmbient : Localization.Away (reesDenominator I hw) →ₐ[R] Localization.Away w := by
  letI : IsLocalization.Away ((evaluate I) (reesDenominator I hw)) (Localization.Away w) := by
    simpa only [reesDenominator,evaluate_monomial] using
      (inferInstance : IsLocalization.Away w (Localization.Away w))
  exact IsLocalization.Away.mapₐ _ _ (evaluate I) (reesDenominator I hw)

lemma reesAmbient_algebraMap (a : reesAlgebra I) :
    reesAmbient I hw (algebraMap (reesAlgebra I) (Localization.Away (reesDenominator I hw)) a) =
      algebraMap R (Localization.Away w) ((evaluate I) a) := by
  simp only [reesAmbient, IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map,
    IsLocalization.map_eq]
  rfl

lemma reesAmbient_fraction (t n : ℕ) (a : ↥(I^(n*d+t))) :
    reesAmbient I hw (TwistedLocalization.fraction (reesGrade I)
      (f := reesDenominator I hw) t n ⟨monomial I _ a,⟨a,rfl⟩⟩) = fraction I w d t n a := by
  have hd : reesAmbient I hw (algebraMap (reesAlgebra I)
      (Localization.Away (reesDenominator I hw)) ((reesDenominator I hw)^n)) =
      algebraMap R (Localization.Away w) (w^n) := by
    rw [reesAmbient_algebraMap,map_pow]
    simp only [reesDenominator,evaluate_monomial]
  simp only [TwistedLocalization.fraction,fraction,LinearMap.coe_mk,AddHom.coe_mk,
    Localization.mk_eq_mk']
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  rw [←hd,←map_mul,IsLocalization.mk'_spec,reesAmbient_algebraMap,evaluate_monomial]

lemma reesAmbient_mem (t : ℕ)
    (x : TwistedLocalization.piece (reesGrade I) (f := reesDenominator I hw) (d := d) t) :
    reesAmbient I hw x ∈ piece I w d t := by
  obtain ⟨n,a,ha⟩ := TwistedLocalization.exists_fraction (reesGrade I) (reesDenominator_mem I hw) t x
  obtain ⟨b,hb⟩ := a.property
  have hae : a = ⟨monomial I _ b,⟨b,rfl⟩⟩ := Subtype.ext hb.symm
  rw [←ha,hae,reesAmbient_fraction]
  exact fraction_mem I w d t n b

 
def reesMap (t : ℕ) :
    TwistedLocalization.piece (reesGrade I) (f := reesDenominator I hw) (d := d) t →ₗ[R]
      piece I w d t :=
  ((reesAmbient I hw).toLinearMap.comp
    (TwistedLocalization.piece (reesGrade I) (f := reesDenominator I hw) (d := d) t).subtype).codRestrict _
      (reesAmbient_mem I hw t)

lemma reesMap_surjective (t : ℕ) : Function.Surjective (reesMap I hw t) := by
  intro x
  obtain ⟨n,a,ha⟩ := exists_fraction I w d hw t x
  refine ⟨⟨TwistedLocalization.fraction (reesGrade I) (f := reesDenominator I hw) t n
    ⟨monomial I _ a,⟨a,rfl⟩⟩,TwistedLocalization.fraction_mem _ _ _ _⟩,?_⟩
  apply Subtype.ext
  exact (reesAmbient_fraction I hw t n a).trans ha

lemma fraction_zero_iff (t n : ℕ) (a : ↥(I^(n*d+t))) :
    fraction I w d t n a=0 ↔ ∃ k : ℕ, w^k*(a:R)=0 := by
  change Localization.mk (a:R) (⟨w^n,n,rfl⟩ : Submonoid.powers w)=0 ↔ _
  rw [Localization.mk_eq_mk',IsLocalization.mk'_eq_zero_iff]
  constructor
  · rintro ⟨⟨_,k,rfl⟩,hk⟩
    exact ⟨k,hk⟩
  · rintro ⟨k,hk⟩
    exact ⟨⟨w^k,k,rfl⟩,hk⟩

lemma reesMap_injective (t : ℕ) : Function.Injective (reesMap I hw t) := by
  apply (LinearMap.ker_eq_bot).mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  obtain ⟨n,a,ha⟩ := TwistedLocalization.exists_fraction (reesGrade I) (reesDenominator_mem I hw) t x
  obtain ⟨b,hb⟩ := a.property
  have hae : a = ⟨monomial I _ b,⟨b,rfl⟩⟩ := Subtype.ext hb.symm
  have he : fraction I w d t n b=0 := by
    have hh := congrArg Subtype.val hx
    change reesAmbient I hw x.val=0 at hh
    rw [←ha,hae,reesAmbient_fraction] at hh
    exact hh
  obtain ⟨k,hk⟩ := (fraction_zero_iff I (w := w) (d := d) t n b).mp he
  apply Subtype.ext
  rw [←ha,hae]
  change Localization.mk (monomial I _ b) (⟨(reesDenominator I hw)^n,n,rfl⟩ : Submonoid.powers _)=0
  rw [Localization.mk_eq_mk',IsLocalization.mk'_eq_zero_iff]
  refine ⟨⟨(reesDenominator I hw)^k,k,rfl⟩,?_⟩
  apply Subtype.ext
  change (Polynomial.monomial d w)^k * Polynomial.monomial (n*d+t) (b:R)=0
  rw [Polynomial.monomial_pow,Polynomial.monomial_mul_monomial,hk,Polynomial.monomial_zero_right]


def reesEquiv (t : ℕ) :
    TwistedLocalization.piece (reesGrade I) (f := reesDenominator I hw) (d := d) t ≃ₗ[R]
      piece I w d t :=
  LinearEquiv.ofBijective (reesMap I hw t) ⟨reesMap_injective I hw t,reesMap_surjective I hw t⟩
end


open Lech.IdealGraded SetLike Graded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {w : R} {d : ℕ} (hw : w ∈ I^d)

 
def quotientGraded : reesGrade I →+*ᵍ SourceGraded.targetGrade I where
  toRingHom := Ideal.Quotient.mk (shifted I)
  map_mem hx := ⟨_,hx,rfl⟩

lemma quotientGraded_apply (a : reesAlgebra I) :
    quotientGraded I a=Ideal.Quotient.mk (shifted I) a := rfl

lemma quotientGraded_smul (r : R) (a : reesAlgebra I) :
    quotientGraded I (r • a)=r • quotientGraded I a :=
  (quotientR I).map_smul r a

abbrev exceptionalPiece (t : ℕ) :=
  TwistedLocalization.piece (R := R) (SourceGraded.targetGrade I)
    (f := quotientGraded I (reesDenominator I hw)) (d := d) t

attribute [local irreducible] TwistedLocalization.piece TwistedLocalization.pieceMap TwistedLocalization.gradedMap quotientGraded
attribute [local instance] TwistedLocalization.kernelAdd TwistedLocalization.kernelModule
 
def quotientTwist (t : ℕ) :=
  TwistedLocalization.pieceMap (R := R) (A := reesAlgebra I) (B := IdealGraded.Ring I)
    (reesGrade I) (reesDenominator_mem I hw) (SourceGraded.targetGrade I) (quotientGraded I)
    (quotientGraded_smul I) t

end Lech.FilteredFraction


namespace Lech.LocalizationCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {h : ℕ} (y : Fin h → A)
  (F G : (s : Finset (Fin h)) → Submodule R (ambient y s))
  (hF : ∀ {s v : Finset (Fin h)} (hsv : s ⊆ v) (x : F s),
    TwistedLocalization.ambientTo (R := R) (GradedChart.denominator_dvd y hsv) x ∈ F v)
  (hG : ∀ {s v : Finset (Fin h)} (hsv : s ⊆ v) (x : G s),
    TwistedLocalization.ambientTo (R := R) (GradedChart.denominator_dvd y hsv) x ∈ G v)
  (hFG : ∀ s, F s ≤ G s)

 
def inclusionLinear (n : ℕ) : cochains y F n →ₗ[R] cochains y G n where
  toFun x a := ⟨(x a).val,hFG _ (x a).property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma inclusionLinear_injective (n : ℕ) : Function.Injective (inclusionLinear y F G hFG n) := by
  intro x x' hx
  funext a
  apply Subtype.ext
  exact congrArg (fun b : G (ActualCech.intersection a) => b.val) (congrFun hx a)

lemma inclusionLinear_d (n : ℕ) (x : cochains y F n) :
    inclusionLinear y F G hFG (n+1) (d y F hF n x)=
      d y G hG n (inclusionLinear y F G hFG n x) := by
  funext a
  apply Subtype.ext
  change ((∑ i : Fin (n+1),(-1:R)^i.val •
    restrict y F hF (ActualCech.intersection_delete a i) (x (a ∘ i.succAbove))).val) =
    ((∑ i : Fin (n+1),(-1:R)^i.val •
    restrict y G hG (ActualCech.intersection_delete a i)
      (inclusionLinear y F G hFG n x (a ∘ i.succAbove))).val)
  simp only [Submodule.coe_sum,Submodule.coe_smul]
  rfl

 
def inclusion : complex y F hF ⟶ complex y G hG :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (inclusionLinear y F G hFG n)) (fun n => by
    change (ModuleCat.ofHom (inclusionLinear y F G hFG n)) ≫
      (CochainComplex.of.d (fun n => ModuleCat.of R (cochains y G n))
        (fun n => ModuleCat.ofHom (d y G hG n)) n (n+1)) =
      (CochainComplex.of.d (fun n => ModuleCat.of R (cochains y F n))
        (fun n => ModuleCat.ofHom (d y F hF n)) n (n+1)) ≫
        ModuleCat.ofHom (inclusionLinear y F G hFG (n+1))
    rw [CochainComplex.of_d,CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (inclusionLinear_d y F G hF hG hFG n x).symm)
end Lech.LocalizationCech


namespace Lech.FilteredCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)


def complex (t : ℕ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  LocalizationCech.complex z (term I z t) (restriction_mem I z hz t)

 
def inclusion {s t : ℕ} (hst : s ≤ t) : complex I z hz t ⟶ complex I z hz s :=
  LocalizationCech.inclusion z (term I z t) (term I z s)
    (restriction_mem I z hz t) (restriction_mem I z hz s)
    (fun _ => FilteredFraction.antitone I _ _ hst)
end Lech.FilteredCech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredFractionReesDenominatorTheory
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
namespace Lech.FilteredFraction
open Lech.IdealGraded SetLike Graded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  {w v c : R} {d e k : ℕ} (hw : w ∈ I^d) (hv : v ∈ I^e) (hc : c ∈ I^k)
  (hwc : w*c=v) (hdeg : d+k=e)

include hwc hdeg in
lemma reesDenominator_mul : reesDenominator I hw * reesDenominator I hc =
    reesDenominator I hv := by
  apply Subtype.ext
  change Polynomial.monomial d w * Polynomial.monomial k c=Polynomial.monomial e v
  rw [Polynomial.monomial_mul_monomial,hwc,hdeg]

lemma reesAmbient_naturality :
    (reesAmbient I hv).comp (TwistedLocalization.ambientTo (R := R)
      (show reesDenominator I hw ∣ reesDenominator I hv from
        ⟨reesDenominator I hc,(reesDenominator_mul I hw hv hc hwc hdeg).symm⟩)) =
    (TwistedLocalization.ambientTo (R := R) (show w ∣ v from ⟨c,hwc.symm⟩)).comp
      (reesAmbient I hw) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (reesDenominator I hw))
  ext a
  change reesAmbient I hv (TwistedLocalization.ambientTo (R := R)
    (show reesDenominator I hw ∣ reesDenominator I hv from
      ⟨reesDenominator I hc,(reesDenominator_mul I hw hv hc hwc hdeg).symm⟩)
    (algebraMap (reesAlgebra I) _ a)) =
    TwistedLocalization.ambientTo (R := R) (show w ∣ v from ⟨c,hwc.symm⟩)
      (reesAmbient I hw (algebraMap (reesAlgebra I) _ a))
  simp only [TwistedLocalization.ambientTo_algebraMap,reesAmbient_algebraMap]


attribute [local irreducible] TwistedLocalization.piece quotientGraded TwistedLocalization.ambientMap TwistedLocalization.ambientTo
lemma quotientDenominator_mem {a : R} {n : ℕ} (ha : a ∈ I^n) :
    quotientGraded I (reesDenominator I ha) ∈ SourceGraded.targetGrade I n := by
  rw [quotientGraded_apply]
  exact ⟨reesDenominator I ha,reesDenominator_mem I ha,rfl⟩


end Lech.FilteredFraction


namespace Lech.FilteredCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)

lemma inclusion_comp {r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t) :
    inclusion I z hz hst ≫ inclusion I z hz hrs = inclusion I z hz (hrs.trans hst) := by
  ext n x
  rfl

instance inclusion_mono {s t : ℕ} (hst : s ≤ t) : Mono (inclusion I z hz hst) := by
  apply mono_of_mono_f
  intro n
  apply (ModuleCat.mono_iff_injective _).mpr
  exact LocalizationCech.inclusionLinear_injective z (term I z t) (term I z s)
    (fun _ => FilteredFraction.antitone I _ _ hst) n
end Lech.FilteredCech

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechCokernelComp
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)
  (ell : AllModuleLength R)

 

noncomputable def finiteThickening (t M : ℕ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  cokernel (FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_add_right t M))



noncomputable def finiteThickeningTransition (t : ℕ) {M N : ℕ} (hMN : M ≤ N) :
    finiteThickening I z hz t N ⟶ finiteThickening I z hz t M :=
  cokernel.map _ _
    (FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.add_le_add_left hMN t)) (𝟙 _)
    (by simp only [Category.comp_id,FilteredCech.inclusion_comp])

end Lech.SourceGraded


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorTotalHomologyProperty
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false
namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject


namespace Lech.LocalizationCech
open CategoryTheory
universe u
variable {R : Type u} [CommRing R] {h : ℕ} (y : Fin h → R)
  (F : ∀ s : Finset (Fin h), Submodule R (ambient y s))

 
noncomputable def augmentationIso : ModuleCat.of R (cochains y F 0) ≅ ModuleCat.of R (F ∅) := by
  have e := (LinearEquiv.piUnique R (fun a : Fin 0 → Fin h => ↥(F (ActualCech.intersection a)))).toModuleIso
  refine e ≪≫ eqToIso ?_
  have he : ActualCech.intersection (default : Fin 0 → Fin h) = ∅ := by
    simp [ActualCech.intersection]
  rw [he]
end Lech.LocalizationCech


namespace Lech.FilteredCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)

 
noncomputable def augmentationIso (t : ℕ) :
    (complex I z hz t).X 0 ≅ ModuleCat.of R ↥(I^t) := by
  refine (LocalizationCech.augmentationIso z (term I z t)) ≪≫ ?_
  have e := (FilteredFraction.augmentationEquiv I t).symm.toModuleIso
  convert e using 1
  all_goals try with_reducible_and_instances rfl
  simp only [term,GradedChart.denominator,Finset.prod_empty,Finset.card_empty]
  rfl

 
lemma augmentationIso_naturality {s t : ℕ} (hst : s ≤ t) :
    (inclusion I z hz hst).f 0 ≫ (augmentationIso I z hz s).hom =
      (augmentationIso I z hz t).hom ≫ ModuleCat.ofHom
        (Submodule.inclusion (show I^t ≤ I^s from Ideal.pow_le_pow_right hst)) := by
  apply (cancel_mono (augmentationIso I z hz s).inv).1
  simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
  apply (cancel_epi (augmentationIso I z hz t).inv).1
  simp only [Iso.inv_hom_id_assoc]
  ext a
  funext b
  apply Subtype.ext
  rfl
end Lech.FilteredCech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredCechAugmentationRing
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false
namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject

namespace Lech.FilteredCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)

 
noncomputable def augmentationRingIso :
    (complex I z hz 0).X 0 ≅ ModuleCat.of R R := by
  refine augmentationIso I z hz 0 ≪≫ ?_
  exact (show ↥(I^0) ≃ₗ[R] R from
    { toFun := Subtype.val
      invFun := fun r => ⟨r,by simp⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toModuleIso

lemma augmentationRingIso_naturality (M : ℕ) :
    (inclusion I z hz (Nat.zero_le M)).f 0 ≫ (augmentationRingIso I z hz).hom =
      (augmentationIso I z hz M).hom ≫ ModuleCat.ofHom (I^M).subtype := by
  dsimp only [augmentationRingIso,Iso.trans_hom]
  rw [←Category.assoc,augmentationIso_naturality,Category.assoc]
  rfl
end Lech.FilteredCech


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)

 

noncomputable def finiteThickeningZeroIso (M : ℕ) :
    (finiteThickening I z hz 0 M).X 0 ≅ ModuleCat.of R (R ⧸ I^M) := by
  unfold finiteThickening
  refine PreservesCokernel.iso (HomologicalComplex.eval (ModuleCat.{u} R) (.up ℕ) 0) _ ≪≫ ?_
  refine cokernel.mapIso _ (ModuleCat.ofHom (I^(0+M)).subtype)
    (FilteredCech.augmentationIso I z (coordinate_mem I z hz) (0+M))
    (FilteredCech.augmentationRingIso I z (coordinate_mem I z hz))
    (FilteredCech.augmentationRingIso_naturality I z (coordinate_mem I z hz) (0+M)) ≪≫ ?_
  exact idealCokernelIso (I^(0+M)) ≪≫
    (Submodule.quotEquivOfEq (I^(0+M)) (I^M) (by rw [Nat.zero_add])).toModuleIso

@[reassoc]
lemma finiteThickeningZeroIso_π (M : ℕ) :
    (cokernel.π (FilteredCech.inclusion I z (coordinate_mem I z hz)
      (Nat.le_add_right 0 M))).f 0 ≫ (finiteThickeningZeroIso I z hz M).hom =
      (FilteredCech.augmentationRingIso I z (coordinate_mem I z hz)).hom ≫
        ModuleCat.ofHom (I^M).mkQ := by
  let G := HomologicalComplex.eval (ModuleCat.{u} R) (.up ℕ) 0
  let f := FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_add_right 0 M)
  let e := cokernel.mapIso (G.map f) (ModuleCat.ofHom (I^(0+M)).subtype)
    (FilteredCech.augmentationIso I z (coordinate_mem I z hz) (0+M))
    (FilteredCech.augmentationRingIso I z (coordinate_mem I z hz))
    (FilteredCech.augmentationRingIso_naturality I z (coordinate_mem I z hz) (0+M))
  let e' := idealCokernelIso (I^(0+M)) ≪≫
    (Submodule.quotEquivOfEq (I^(0+M)) (I^M) (by rw [Nat.zero_add])).toModuleIso
  have hp : G.map (cokernel.π f) ≫ (PreservesCokernel.iso G f).hom ≫ e.hom ≫ e'.hom =
      (FilteredCech.augmentationRingIso I z (coordinate_mem I z hz)).hom ≫
        ModuleCat.ofHom (I^M).mkQ := by
    rw [PreservesCokernel.π_iso_hom_assoc]
    dsimp only [e,e',Iso.trans_hom]
    simp only [cokernel.mapIso_hom,cokernel.map,cokernel.π_desc_assoc,Category.assoc,idealCokernelIso_π_assoc]
    ext
    rfl
  exact hp



end Lech.SourceGraded


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)

noncomputable def augmentedThickening (M : ℕ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  (finiteThickening I z hz 0 M).extend ComplexShape.embeddingUpNat

lemma augmentedThickening_boundedBelow (M : ℕ) :
    ∀ i, i < (0 : ℤ) → IsZero ((augmentedThickening I z hz M).X i) := by
  intro i hi
  apply (finiteThickening I z hz 0 M).isZero_extend_X
  intro n hn
  change (n : ℤ)=i at hn
  omega



noncomputable def thickeningCech (M : ℕ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  FiniteComplex.dropBottom (augmentedThickening I z hz M) 0
    (augmentedThickening_boundedBelow I z hz M)

noncomputable def augmentedThickeningTransition {M N : ℕ} (hMN : M ≤ N) :
    augmentedThickening I z hz N ⟶ augmentedThickening I z hz M :=
  extendMap (finiteThickeningTransition I z hz 0 hMN) ComplexShape.embeddingUpNat

noncomputable def thickeningCechTransition {M N : ℕ} (hMN : M ≤ N) :
    thickeningCech I z hz N ⟶ thickeningCech I z hz M :=
  FiniteComplex.dropBottomMap (augmentedThickening I z hz N) 0
    (augmentedThickening_boundedBelow I z hz N)
    (augmentedThickening_boundedBelow I z hz M) (augmentedThickeningTransition I z hz hMN)

end Lech.SourceGraded


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredCechAugmented
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false
namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject

namespace Lech.FilteredCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)

def augmented (t : ℕ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  (complex I z hz t).extend ComplexShape.embeddingUpNat

lemma augmented_boundedBelow (t : ℕ) :
    ∀ i, i < (0 : ℤ) → IsZero ((augmented I z hz t).X i) := by
  intro i hi
  apply (complex I z hz t).isZero_extend_X
  intro n hn
  change (n : ℤ)=i at hn
  omega

 

def positive (t : ℕ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  FiniteComplex.dropBottom (augmented I z hz t) 0 (augmented_boundedBelow I z hz t)

lemma positive_boundedBelow (t : ℕ) :
    ∀ q, q≤(0 : ℤ) → IsZero ((positive I z hz t).X q) := by
  intro q hq
  exact FiniteComplex.dropBottom_boundedBelow _ _ _ q (by omega)

def positiveInclusion {s t : ℕ} (hst : s ≤ t) : positive I z hz t ⟶ positive I z hz s :=
  FiniteComplex.dropBottomMap (augmented I z hz t) 0 (augmented_boundedBelow I z hz t)
    (augmented_boundedBelow I z hz s) (extendMap (inclusion I z hz hst) ComplexShape.embeddingUpNat)

def positiveXIso (t n : ℕ) (hn : 0<n) :
    (positive I z hz t).X (n : ℤ) ≅ (complex I z hz t).X n :=
  FiniteComplex.dropBottomXIso _ _ _ (n : ℤ) (by omega) ≪≫
    (complex I z hz t).extendXIso ComplexShape.embeddingUpNat (i := n) rfl

@[reassoc] lemma positiveXIso_inclusion {s t : ℕ} (hst : s ≤ t) (n : ℕ) (hn : 0<n) :
    (positiveXIso I z hz t n hn).hom ≫ (inclusion I z hz hst).f n =
      (positiveInclusion I z hz hst).f (n : ℤ) ≫ (positiveXIso I z hz s n hn).hom := by
  have he := congrArg (fun f => f.f (n : ℤ))
    (FiniteComplex.dropBottomMap_ι (augmented I z hz t) 0 (augmented_boundedBelow I z hz t)
      (augmented_boundedBelow I z hz s) (extendMap (inclusion I z hz hst) ComplexShape.embeddingUpNat))
  dsimp only [positiveXIso,Iso.trans_hom,FiniteComplex.dropBottomXIso,asIso_hom,positiveInclusion]
  exact component_iso_square_p0
    ((complex I z hz t).extendXIso ComplexShape.embeddingUpNat (i := n) rfl)
    ((complex I z hz s).extendXIso ComplexShape.embeddingUpNat (i := n) rfl)
    _ _ _ _ _
    (extendMap_f (inclusion I z hz hst) ComplexShape.embeddingUpNat
      (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)) he

end Lech.FilteredCech


namespace Lech.TensorPi
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive MonoidalCategory
universe u
variable {R : Type u} [CommRing R] {J : Type} [Fintype J]
  {A B C : ModuleCat.{u} R} {Q Q' Q'' : J → ModuleCat.{u} R}
open scoped TensorProduct

attribute [local instance] OAI.Lech.TensorPi.instDecidableEq_solutions
lemma map_tensor (f : A ⟶ B) (g : ∀ j, Q j ⟶ Q' j) :
    map (fun j => f ⊗ₘ g j) = f ⊗ₘ piMap g := by
  apply ext
  intro x j
  induction x using OAI.tensorInductionOn with
  | tmul x y =>
    simp only [map_apply,TensorProduct.piRight_apply,TensorProduct.piRightHom_tmul,
      ModuleCat.MonoidalCategory.tensorHom_tmul]
    rfl
  | add x y hx hy => simp only [LinearMap.map_add,LinearEquiv.map_add,Pi.add_apply,hx,hy]

end Lech.TensorPi


namespace Lech.TensorPi
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive MonoidalCategory HomologicalComplex
open Lech.TensorTotal
universe u
variable {R : Type u} [CommRing R] {J : Type} [Fintype J]
  (F : CochainComplex (ModuleCat.{u} R) ℤ) {Q Q' : J → ModuleCat.{u} R}

 

def homotopy (inc : ∀ j, Q j ⟶ Q' j)
    (H : ∀ j, Homotopy (termTensorMap F (Q j) (inc j)) 0) :
    Homotopy (termTensorMap F (modulePi Q) (piMap inc)) 0 where
  hom p q := map (fun j => (H j).hom p q)
  zero p q hpq := by
    have hh : (fun j => (H j).hom p q) = (fun _ => 0) := funext (fun j => (H j).zero p q hpq)
    rw [hh,map_zero]
  comm p := by
    have hh : (fun j => (termTensorMap F (Q j) (inc j)).f p) =
        (fun j => ((termTensor (Q j)).obj F).d p (p+1) ≫ (H j).hom (p+1) p +
          (H j).hom p (p-1) ≫ ((termTensor (Q' j)).obj F).d (p-1) p) := by
      funext j
      have hj := (H j).comm p
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel p (p+1) from rfl),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (p-1) p by change p-1+1=p; omega),zero_f,add_zero] at hj
      exact hj
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel p (p+1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (p-1) p by change p-1+1=p; omega),zero_f,add_zero]
    change (𝟙 (F.X p) ⊗ₘ piMap inc) =
      (F.d p (p+1) ⊗ₘ 𝟙 (modulePi Q)) ≫ map (fun j => (H j).hom (p+1) p) +
        map (fun j => (H j).hom p (p-1)) ≫ (F.d (p-1) p ⊗ₘ 𝟙 (modulePi Q'))
    rw [←map_tensor]
    change map (fun j => (termTensorMap F (Q j) (inc j)).f p) = _
    rw [hh,map_add,map_comp,map_comp]
    change map (fun j => F.d p (p+1) ⊗ₘ 𝟙 (Q j)) ≫ _ +
      _ ≫ map (fun j => F.d (p-1) p ⊗ₘ 𝟙 (Q' j)) = _
    rw [map_tensor,map_tensor,piMap_id,piMap_id]
end Lech.TensorPi


namespace Lech.FilteredCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Lech.TensorTotal
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)
variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℕ)
  (H : ∀ i, Homotopy (z i ^ m • 𝟙 F) 0)

 

def intersectionHomotopy (t n : ℕ) (hn : 0<n) (a : Fin n → Fin h) :
    Homotopy (termTensorMap F (ModuleCat.of R (term I z (t+m) (ActualCech.intersection a)))
      (ModuleCat.ofHom (Submodule.inclusion (FilteredFraction.antitone I _ _ (Nat.le_add_right t m))))) 0 := by
  let i : Fin h := a ⟨0,hn⟩
  have hi : i ∈ ActualCech.intersection a := (ActualCech.mem_intersection a i).mpr ⟨⟨0,hn⟩,rfl⟩
  apply tensorDivisionHomotopy F (z i ^ m)
    (ModuleCat.ofHom (divide I z hz i hi t m)) _ _ (H i)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact smul_divide I z hz i hi t m x

def cochainPiIso (t n : ℕ) :
    (complex I z hz t).X n ≅ TensorPi.modulePi (fun a : Fin n → Fin h =>
      ModuleCat.of R (term I z t (ActualCech.intersection a))) := Iso.refl _

lemma cochainPiIso_inclusion {s t : ℕ} (hst : s≤t) (n : ℕ) :
    (cochainPiIso I z hz t n).hom ≫ TensorPi.piMap (fun a : Fin n → Fin h =>
      ModuleCat.ofHom (Submodule.inclusion (FilteredFraction.antitone I
        (GradedChart.denominator z (ActualCech.intersection a))
        (ActualCech.intersection a).card hst))) =
      (inclusion I z hz hst).f n ≫ (cochainPiIso I z hz s n).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

def cochainHomotopy (t n : ℕ) (hn : 0<n) :
    Homotopy (termTensorMap F ((complex I z hz (t+m)).X n)
      ((inclusion I z hz (Nat.le_add_right t m)).f n)) 0 := by
  let Q : (Fin n → Fin h) → ModuleCat.{u} R := fun a =>
    ModuleCat.of R (term I z (t+m) (ActualCech.intersection a))
  let Q' : (Fin n → Fin h) → ModuleCat.{u} R := fun a =>
    ModuleCat.of R (term I z t (ActualCech.intersection a))
  let inc : ∀ a, Q a ⟶ Q' a := fun _ =>
    ModuleCat.ofHom (Submodule.inclusion (FilteredFraction.antitone I _ _ (Nat.le_add_right t m)))
  have HH := TensorPi.homotopy (Q := Q) (Q' := Q') F inc
    (intersectionHomotopy I z hz F m H t n hn)
  exact coefficientHomotopyOfIso F (cochainPiIso I z hz (t+m) n) (cochainPiIso I z hz t n)
    _ _ (cochainPiIso_inclusion I z hz (Nat.le_add_right t m) n) HH

 

def positiveRowHomotopy (t : ℕ) (q : ℤ) :
    Homotopy (termTensorMap F ((positive I z hz (t+m)).X q)
      ((positiveInclusion I z hz (Nat.le_add_right t m)).f q)) 0 := by
  by_cases hq : q ≤ 0
  · have hf : (positiveInclusion I z hz (Nat.le_add_right t m)).f q=0 :=
      (positive_boundedBelow I z hz (t+m) q hq).eq_of_src _ _
    rw [hf,termTensorMap_zero]
  · have hn : 0<q.toNat := by omega
    have heq : (q.toNat:ℤ)=q := by omega
    have HH := coefficientHomotopyOfIso F (positiveXIso I z hz (t+m) q.toNat hn)
      (positiveXIso I z hz t q.toNat hn) _ _ (positiveXIso_inclusion I z hz _ q.toNat hn)
      (cochainHomotopy I z hz F m H t q.toNat hn)
    rw [heq] at HH
    exact HH
end Lech.FilteredCech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_HomogeneousZeroPiece
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.Homogeneous
open HomogeneousLocalization
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (G : ℕ → Submodule R A) [GradedAlgebra G]
  {f : A} {d : ℕ} (hf : f ∈ G d)
attribute [local instance] awayAddCommGroup

def toZeroPiece : Away G f →ₗ[R] TwistedLocalization.piece G (f:=f) (d:=d) 0 where
  toFun x := ⟨x.val,by
    obtain ⟨n,a,ha,rfl⟩ := Away.mk_surjective G hf x
    change Localization.mk a (⟨f^n,n,rfl⟩ : Submonoid.powers f) ∈ _
    exact TwistedLocalization.fraction_mem G 0 n
      ⟨a,by simpa only [Nat.add_zero,nsmul_eq_mul,Nat.cast_id] using ha⟩⟩
  map_add' x y := Subtype.ext (HomogeneousLocalization.val_add _ _)
  map_smul' r x := Subtype.ext (HomogeneousLocalization.val_smul _ r x)

lemma toZeroPiece_injective : Function.Injective (toZeroPiece G hf) := by
  intro x y hxy
  exact HomogeneousLocalization.val_injective _ (congrArg Subtype.val hxy)
end Lech.Homogeneous

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverRootSigned
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.Homogeneous
open HomogeneousLocalization
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (G : ℕ → Submodule R A) [GradedAlgebra G]


instance algebra (U : Submonoid A) : Algebra R (HomogeneousLocalization G U) :=
  Algebra.ofModule
    (fun r x y => by
      apply val_injective U
      simp only [val_mul,val_smul]
      exact smul_mul_assoc r x.val y.val)
    (fun r x y => by
      apply val_injective U
      simp only [val_mul,val_smul]
      exact mul_smul_comm r x.val y.val)

@[simp] lemma val_algebraMap (U : Submonoid A) (r : R) :
    (algebraMap R (HomogeneousLocalization G U) r).val =
      algebraMap R (Localization U) r := by
  change (r • (1 : HomogeneousLocalization G U)).val = _
  rw [val_smul,val_one,Algebra.smul_def,mul_one]

end Lech.Homogeneous


namespace Lech.ProjectiveCoefficientChart
open MvPolynomial HomogeneousLocalization
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
attribute [local instance] MvPolynomial.gradedAlgebra
def forward : UniversalCoefficientChart.Ring R n k →ₐ[R] Chart R n k :=
  MvPolynomial.aeval (fun j => coordinate R n k j)
def inclusion : Chart R n k →ₐ[R] Ambient R n k where
  toRingHom := algebraMap _ _
  commutes' r := Homogeneous.val_algebraMap (grading R n) (Submonoid.powers (X k)) r
def backward : Chart R n k →ₐ[R] UniversalCoefficientChart.Ring R n k :=
  (dehomogenize R n k).comp (inclusion R n k)
lemma backward_mk (d : ℕ) (p : MvPolynomial (Fin (n+1)) R)
    (hp : p∈grading R n (d • 1)) :
    backward R n k (Away.mk (grading R n) (isHomogeneous_X R k) d p hp)=evaluate R n k p := by
  change dehomogenize R n k (Localization.mk p ⟨X k ^ d,⟨d,rfl⟩⟩)=_
  have h : evaluate R n k (X k)*1=1 := by
    simp [evaluate,UniversalCoefficientChart.coefficient_self]
  convert (Localization.awayLift_mk (evaluate R n k).toRingHom (X k) p 1 h d) using 1
  · rfl
  · simp
lemma backward_coordinate (j : Fin (n+1)) :
    backward R n k (coordinate R n k j)=UniversalCoefficientChart.coefficient R n k j := by
  rw [coordinate,backward_mk]
  simp [evaluate]
lemma backward_forward (x : UniversalCoefficientChart.Ring R n k) :
    backward R n k (forward R n k x)=x := by
  have he : (backward R n k).comp (forward R n k)=AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro j
    simpa [forward] using (backward_coordinate R n k j).trans
      (UniversalCoefficientChart.coefficient_other R n k j)
  exact DFunLike.congr_fun he x
end Lech.ProjectiveCoefficientChart

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechHomogeneousEval
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.ProjectiveCoefficientChart

section
open MvPolynomial HomogeneousLocalization
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
attribute [local instance] MvPolynomial.gradedAlgebra
lemma forward_coefficient (j : Fin (n+1)) :
    forward R n k (UniversalCoefficientChart.coefficient R n k j)=coordinate R n k j := by
  by_cases h : j=k
  · subst j
    rw [UniversalCoefficientChart.coefficient_self,map_one,coordinate_self]
  · rw [UniversalCoefficientChart.coefficient, dite_eq_right h]
    simp [forward]
lemma inclusion_forward_evaluate (p : MvPolynomial (Fin (n+1)) R) :
    inclusion R n k (forward R n k (evaluate R n k p))=
      eval₂ (algebraMap R (Ambient R n k)) (fun j => (coordinate R n k j).val) p := by
  have he : (inclusion R n k).comp ((forward R n k).comp (evaluate R n k))=
      MvPolynomial.aeval (fun j => (coordinate R n k j).val) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply,evaluate,aeval_X,forward_coefficient]
    rfl
  exact DFunLike.congr_fun he p
lemma homogeneous_identity (d : ℕ) (p : MvPolynomial (Fin (n+1)) R)
    (hp : p.IsHomogeneous d) :
    (inclusion R n k (forward R n k (evaluate R n k p)))*
      algebraMap (MvPolynomial (Fin (n+1)) R) (Ambient R n k) (X k)^d=
      algebraMap _ _ p := by
  rw [inclusion_forward_evaluate,mul_comm]
  have hs := homogeneous_eval_scale (algebraMap R (Ambient R n k))
    (fun j => (coordinate R n k j).val)
    (algebraMap (MvPolynomial (Fin (n+1)) R) (Ambient R n k) (X k)) hp
  simp only [coordinate_mul] at hs
  rw [←hs]
  have he : MvPolynomial.aeval
      (fun j : Fin (n+1) => algebraMap (MvPolynomial (Fin (n+1)) R) (Ambient R n k) (X j))=
      IsScalarTower.toAlgHom R (MvPolynomial (Fin (n+1)) R) (Ambient R n k) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp
  exact DFunLike.congr_fun he p
lemma forward_backward (x : Chart R n k) : forward R n k (backward R n k x)=x := by
  obtain ⟨d,p,hp,rfl⟩ := Away.mk_surjective (grading R n) (isHomogeneous_X R k) x
  rw [backward_mk]
  apply HomogeneousLocalization.val_injective (Submonoid.powers (X k))
  change (inclusion R n k (forward R n k (evaluate R n k p)))=
    Localization.mk p (⟨X k ^ d,⟨d,rfl⟩⟩ : Submonoid.powers (X (R:=R) k))
  rw [Localization.mk_eq_mk',IsLocalization.eq_mk'_iff_mul_eq]
  change _ * algebraMap (MvPolynomial (Fin (n+1)) R) (Ambient R n k) (X k ^ d)=_
  rw [map_pow]
  exact homogeneous_identity R n k d p (by simpa using hp)
 

def equiv : UniversalCoefficientChart.Ring R n k ≃ₐ[R] Chart R n k :=
  AlgEquiv.ofAlgHom (forward R n k) (backward R n k)
    (AlgHom.ext (fun x => forward_backward R n k x))
    (AlgHom.ext (fun x => backward_forward R n k x))
end


open MvPolynomial HomogeneousLocalization
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
end Lech.ProjectiveCoefficientChart


namespace Lech.UniversalSplitting
open Polynomial
universe u

attribute [instance] Data.ring Data.algebra


end Lech.UniversalSplitting

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PrimitiveChartFaithfullyFlat
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.BinaryCover
open Polynomial
universe u

attribute [instance] Data.ring Data.algebra Data.chartAlgebra Data.tower

end Lech.BinaryCover


namespace Lech.RootGluing
open Polynomial
universe u
variable {B : Type u} [CommRing B]

lemma rootShift_comp (a b x : B) (ha : IsUnit (1+a*x))
    (hab : IsUnit (1+(a+b)*x)) :
    rootShift b (rootShift a x)=rootShift (a+b) x := by
  obtain ⟨d,hd⟩ := ha
  obtain ⟨e,he⟩ := hab
  have hden := denominator_comp a b x d hd
  simp only [rootShift,← hd,Ring.inverse_unit]
  rw [hden,← he]
  change x*(↑d⁻¹:B)*Ring.inverse ((e*d⁻¹:Bˣ):B)=x*Ring.inverse (e:B)
  rw [Ring.inverse_unit,Ring.inverse_unit]
  simp only [mul_inv_rev,inv_inv,Units.val_mul]
  calc
    x*(↑d⁻¹:B)*((d:B)*(↑e⁻¹:B))=x*((↑d⁻¹:B)*(d:B))*(↑e⁻¹:B) := by ring
    _ = x*(↑e⁻¹:B) := by rw [d.inv_mul,mul_one]

end Lech.RootGluing
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TotalGhostRowHom
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject


namespace Lech.FilteredCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open Lech.TensorTotal
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)
variable (F : CochainComplex (ModuleCat.{u} R) ℤ)

variable (m : ℕ) (H : ∀ i, Homotopy (z i ^ m • 𝟙 F) 0)

def bicRowHomotopy (t : ℕ) :
    TotalGhost.RowHomotopy ((tensorBic F).map (positiveInclusion I z hz (Nat.le_add_right t m))) :=
  TotalGhost.RowHomotopy.ofRows (positiveRowHomotopy I z hz F m H t)

def bicRowHomotopyAt (s t : ℕ) (he : t=s+m) :
    TotalGhost.RowHomotopy ((tensorBic F).map
      (positiveInclusion I z hz (by omega : s ≤ t))) := by
  subst t
  exact bicRowHomotopy I z hz F m H s

def twistStep (t n : ℕ) : positive I z hz (t+m*(n+1)) ⟶ positive I z hz (t+m*n) :=
  positiveInclusion I z hz (by rw [Nat.mul_succ]; omega)

end Lech.FilteredCech

open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechMapCochain
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false
namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex


namespace Lech.FiniteComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C : Type*} [Category C] [Abelian C]

lemma dropBottomMap_comp {F G H : CochainComplex C ℤ} (n : ℤ)
    (hf : ∀ i, i<n → IsZero (F.X i)) (hg : ∀ i, i<n → IsZero (G.X i))
    (hh : ∀ i, i<n → IsZero (H.X i)) (f : F ⟶ G) (g : G ⟶ H) :
    dropBottomMap F n hf hg f ≫ dropBottomMap G n hg hh g =
      dropBottomMap F n hf hh (f ≫ g) := by
  apply (cancel_mono (kernel.ι (bottomProjection H n hh))).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (dropBottomMap F n hf hg f ≫ ·) (dropBottomMap_ι G n hg hh g)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ g) (dropBottomMap_ι F n hf hg f)).trans
          ((Category.assoc _ _ _).trans (dropBottomMap_ι F n hf hh (f ≫ g)).symm))))

lemma dropBottomMap_zero {F G : CochainComplex C ℤ} (n : ℤ)
    (hf : ∀ i, i<n → IsZero (F.X i)) (hg : ∀ i, i<n → IsZero (G.X i)) :
    dropBottomMap F n hf hg (0 : F ⟶ G)=0 := by
  apply (cancel_mono (kernel.ι (bottomProjection G n hg))).mp
  exact (dropBottomMap_ι F n hf hg (0 : F ⟶ G)).trans
    ((comp_zero).trans (zero_comp).symm)

variable (S : ShortComplex (CochainComplex C ℤ)) (n : ℤ)
    (h₁ : ∀ i, i<n → IsZero (S.X₁.X i))
    (h₂ : ∀ i, i<n → IsZero (S.X₂.X i))
    (h₃ : ∀ i, i<n → IsZero (S.X₃.X i))

def dropShortComplex : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (dropBottomMap S.X₁ n h₁ h₂ S.f) (dropBottomMap S.X₂ n h₂ h₃ S.g)
    (by rw [dropBottomMap_comp,S.zero,dropBottomMap_zero])

end Lech.FiniteComplex


namespace Lech.FiniteComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C : Type*} [Category C] [Abelian C]

def dropShortComplexMap {S T : ShortComplex (CochainComplex C ℤ)} (n : ℤ)
    (hS₁ : ∀ i, i<n → IsZero (S.X₁.X i))
    (hS₂ : ∀ i, i<n → IsZero (S.X₂.X i))
    (hS₃ : ∀ i, i<n → IsZero (S.X₃.X i))
    (hT₁ : ∀ i, i<n → IsZero (T.X₁.X i))
    (hT₂ : ∀ i, i<n → IsZero (T.X₂.X i))
    (hT₃ : ∀ i, i<n → IsZero (T.X₃.X i)) (f : S ⟶ T) :
    dropShortComplex S n hS₁ hS₂ hS₃ ⟶ dropShortComplex T n hT₁ hT₂ hT₃ where
  τ₁ := dropBottomMap S.X₁ n hS₁ hT₁ f.τ₁
  τ₂ := dropBottomMap S.X₂ n hS₂ hT₂ f.τ₂
  τ₃ := dropBottomMap S.X₃ n hS₃ hT₃ f.τ₃
  comm₁₂ := by
    dsimp only [dropShortComplex]
    rw [dropBottomMap_comp,dropBottomMap_comp,f.comm₁₂]
  comm₂₃ := by
    dsimp only [dropShortComplex]
    rw [dropBottomMap_comp,dropBottomMap_comp,f.comm₂₃]
end Lech.FiniteComplex


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootOverlap
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


variable (k : Fin (n+1)) (s : Finset (Fin (n+1))) (hk : k ∈ s)
def coefficientMap : UniversalCoefficientChart.Ring R n k →+* Ring R n s :=
  (chartMap R n k s hk).comp (ProjectiveCoefficientChart.equiv R n k).toRingHom

@[instance_reducible] def coefficientAlgebra :
    Algebra (UniversalCoefficientChart.Ring R n k) (Ring R n s) :=
  (coefficientMap R n k s hk).toAlgebra


end Lech.ProjectiveRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootMap
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
  (z : Fin (n+1) → R) (hz : ∀ j, z j ∈ I)
attribute [local instance] MvPolynomial.gradedAlgebra

def generator (j : Fin (n+1)) : reesAlgebra I :=
  monomial I 1 ⟨z j,by simpa only [pow_one] using hz j⟩
lemma generator_mem (j : Fin (n+1)) : generator I z hz j ∈ reesGrade I 1 := ⟨_,rfl⟩

def gradedMap : ProjectiveCoefficientChart.grading R n →+*ᵍ reesGrade I :=
  Grading.polynomialMap (reesGrade I) (generator I z hz) (generator_mem I z hz)

@[simp] lemma gradedMap_X (j : Fin (n+1)) : gradedMap I z hz (X j) = generator I z hz j :=
  MvPolynomial.aeval_X _ _
@[simp] lemma gradedMap_C (r : R) : gradedMap I z hz (C r) = algebraMap R (reesAlgebra I) r :=
  MvPolynomial.aeval_C _ _


end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SourceGradedThickeningNat
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)

def thickeningNatSequence (M : ℕ) : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk
    (FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_add_right 0 M))
    (cokernel.π _) (cokernel.condition _)

def thickeningAugSequence (M : ℕ) : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  (thickeningNatSequence I z hz M).map (ComplexShape.embeddingUpNat.extendFunctor _)



def thickeningPositiveSequence (M : ℕ) : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  FiniteComplex.dropShortComplex (thickeningAugSequence I z hz M) 0
    (FilteredCech.augmented_boundedBelow I z (coordinate_mem I z hz) (0+M))
    (FilteredCech.augmented_boundedBelow I z (coordinate_mem I z hz) 0)
    (augmentedThickening_boundedBelow I z hz M)

def thickeningNatSequenceMap {M N : ℕ} (hMN : M≤N) :
    thickeningNatSequence I z hz N ⟶ thickeningNatSequence I z hz M where
  τ₁ := FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.add_le_add_left hMN 0)
  τ₂ := 𝟙 _
  τ₃ := finiteThickeningTransition I z hz 0 hMN
  comm₁₂ := by simp only [thickeningNatSequence,Category.comp_id,FilteredCech.inclusion_comp]
  comm₂₃ := by simp only [thickeningNatSequence,finiteThickeningTransition,
    cokernel.map,cokernel.π_desc,Category.id_comp]

def thickeningPositiveSequenceMap {M N : ℕ} (hMN : M≤N) :
    thickeningPositiveSequence I z hz N ⟶ thickeningPositiveSequence I z hz M :=
  FiniteComplex.dropShortComplexMap 0
    (FilteredCech.augmented_boundedBelow I z (coordinate_mem I z hz) (0+N))
    (FilteredCech.augmented_boundedBelow I z (coordinate_mem I z hz) 0)
    (augmentedThickening_boundedBelow I z hz N)
    (FilteredCech.augmented_boundedBelow I z (coordinate_mem I z hz) (0+M))
    (FilteredCech.augmented_boundedBelow I z (coordinate_mem I z hz) 0)
    (augmentedThickening_boundedBelow I z hz M)
    ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapShortComplex.map
      (thickeningNatSequenceMap I z hz hMN))

variable (F : CochainComplex (ModuleCat.{u} R) ℤ)

def thickeningTensorSequence (M : ℕ) : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  (thickeningPositiveSequence I z hz M).map (TensorTotal.Right.functor F)

def thickeningTensorSequenceMap {M N : ℕ} (hMN : M≤N) :
    thickeningTensorSequence I z hz F N ⟶ thickeningTensorSequence I z hz F M :=
  (TensorTotal.Right.functor F).mapShortComplex.map (thickeningPositiveSequenceMap I z hz hMN)
end Lech.SourceGraded


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ)



def geometricStructureMap (M : ℕ) :
    (TensorTotal.Right.functor F).obj (FilteredCech.positive I z (coordinate_mem I z hz) 0) ⟶
      (TensorTotal.Right.functor F).obj (thickeningCech I z hz M) :=
  (thickeningTensorSequence I z hz F M).g

@[reassoc] lemma geometricStructureMap_transition {M N : ℕ} (hMN : M≤N) :
    geometricStructureMap I z hz F N ≫
      (TensorTotal.Right.functor F).map (thickeningCechTransition I z hz hMN) =
      (thickeningTensorSequenceMap I z hz F hMN).τ₂ ≫ geometricStructureMap I z hz F M := by
  exact (thickeningTensorSequenceMap I z hz F hMN).comm₂₃.symm

end Lech.SourceGraded

open CochainComplex CochainComplex.HomComplex
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesExceptionalRing
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.FilteredFraction
open HomogeneousLocalization IdealGraded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {w : R} {d : ℕ} (hw : w ∈ I^d)
attribute [local instance] Homogeneous.awayAddCommGroup
attribute [local irreducible] quotientGraded Homogeneous.awayMap TwistedLocalization.piece TwistedLocalization.pieceMap TwistedLocalization.gradedMap

abbrev ReesChart := Away (reesGrade I) (reesDenominator I hw)
abbrev ExceptionalChart := Away (SourceGraded.targetGrade I) (quotientGraded I (reesDenominator I hw))
local instance reesChartCommRing : CommRing (ReesChart I hw) := inferInstance
local instance reesChartModule : Module R (ReesChart I hw) :=
  Homogeneous.module (reesGrade I) (Submonoid.powers (reesDenominator I hw))

attribute [local irreducible] TwistedLocalization.ambientMap
def chartAmbient :=
  TwistedLocalization.ambientMap (R:=R) (A:=reesAlgebra I) (B:=IdealGraded.Ring I)
    (reesGrade I) (SourceGraded.targetGrade I) (quotientGraded I)
    (quotientGraded_smul I) (f:=reesDenominator I hw)

end Lech.FilteredFraction

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ScalarChartComparison
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.FilteredCech
open CategoryTheory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ j,z j∈I)
def diagram (t : ℕ) : FiniteModuleCech.Diagram R (Fin h) where
  obj s := ModuleCat.of R (term I z t s)
  res hst := ModuleCat.ofHom (LocalizationCech.restrict z (term I z t) (restriction_mem I z hz t) hst)
  res_self s := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact AlgHom.congr_fun (TwistedLocalization.ambientTo_self (R:=R) (GradedChart.denominator z s)) x.val
  res_comp hst htv := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact LocalizationCech.restrict_comp z (term I z t) (restriction_mem I z hz t) hst htv

end Lech.FilteredCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ScalarCechShift
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.FilteredCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ j,z j∈I)

lemma positiveXIso_d (t n : ℕ) (hn : 0<n) :
    (positive I z hz t).d (n:ℤ) ((n+1:ℕ):ℤ) ≫ (positiveXIso I z hz t (n+1) (by omega)).hom=
      (positiveXIso I z hz t n hn).hom ≫ (complex I z hz t).d n (n+1) := by
  let κ := kernel.ι (FiniteComplex.bottomProjection (augmented I z hz t) 0 (augmented_boundedBelow I z hz t))
  change (positive I z hz t).d (n:ℤ) ((n+1:ℕ):ℤ) ≫ (κ.f _ ≫ _)=κ.f _ ≫ _ ≫ _
  dsimp only [positive,FiniteComplex.dropBottom]
  rw [←Category.assoc,←κ.comm,Category.assoc]
  change κ.f _ ≫ ((complex I z hz t).extend ComplexShape.embeddingUpNat).d _ _ ≫ _=_
  dsimp only [augmented] at κ ⊢
  rw [(complex I z hz t).extend_d_eq ComplexShape.embeddingUpNat
    (i:=n) (j:=n+1) (i':=(n:ℤ)) (j':=((n+1:ℕ):ℤ)) rfl rfl]
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]

lemma complex_d (t n : ℕ) :
    (complex I z hz t).d n (n+1)=ModuleCat.ofHom
      (LocalizationCech.d z (term I z t) (restriction_mem I z hz t) n) := by
  exact CochainComplex.of_d (fun q => ModuleCat.of R (LocalizationCech.cochains z (term I z t) q))
    (fun q => ModuleCat.ofHom (LocalizationCech.d z (term I z t) (restriction_mem I z hz t) q)) n

abbrev shiftedPositive (t : ℕ) := (positive I z hz t)⟦(1:ℤ)⟧
end Lech.FilteredCech

end

end OAI
end


