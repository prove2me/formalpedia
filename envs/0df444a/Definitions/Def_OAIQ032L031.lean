-- Prove2me | Definitions.Def_OAIQ032L031
-- name    : OAIQ032L031
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T20:44:52.435008+00:00
-- url     : https://prove2.me/theorems/ddef853b-0327-4d26-b44c-3f246e297830
-- title:
--   Definitions bundle OAIQ032L031 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 27 declarations of OpenAI's Lean: 9 definitions, 2 instances and 16 theorems. The definitions and types are `OAI.Lech.ProjectiveRoot.coeffToAmbient`, `OAI.Lech.ProjectiveRoot.coeffToAmbientModule`, `OAI.Lech.ProjectiveRoot.coefficientCech`, `OAI.Lech.ProjectiveRoot.coefficientEvaluation`, `OAI.Lech.ProjectiveRoot.integerCech`, `OAI.Lech.ProjectiveRoot.integerHomologyBasis`, `OAI.Lech.ProjectiveRoot.scalarAt`, `OAI.Lech.ProjectiveRoot.scalarMap`, `OAI.Lech.ProjectiveRoot.zeroAugGrid`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_ProductSourceCoverCechNat`, `Multiplicity_ReesCoordinate`, `Multiplicity_RootCechCoefficients`, `Multiplicity_RootCechProjective`, `Multiplicity_RootOverlap`, `Multiplicity_RootRestriction`, `Multiplicity_RootSectionDiagram`, `Multiplicity_RootTwist`.
--
--   **Imports.** It imports the bundles `OAIQ032L028` and `OAIQ032L029` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ032L032` and `OAIQ032L033`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ032L028
import Definitions.Def_OAIQ032L029

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverCechNat
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
open scoped BigOperators
open scoped Classical


namespace Lech.ProductSourceCover

section

section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]


theorem targetSigned_pure (m : Fin n → ℤ) :
    PureCohomology R (targetCech R n m) (negativeCount m+1) (signedRank m) :=
  pureCohomology_of_iso R (sourceCech R n m) (targetCech R n m)
    (cechNatCohomologyComparison R n m) _ _ (sourceSigned_pure R n m)


end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators Classical
universe u
end


open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
open scoped BigOperators Classical
universe u
end Lech.ProductSourceCover


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootOverlap
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.ReesRoot.projectiveAlgebra _root_.OAI.Lech.ReesRoot.projectiveTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


def coefficientEvaluation : MvPolynomial (Fin (n+1)) R →ₐ[R] GridAmbient R n :=
  MvPolynomial.aeval (fun j => embed R n (targetCoeff R n j))
lemma coefficientEvaluation_X (j : Fin (n+1)) :
    coefficientEvaluation R n (X j) = (targetUnit R n j : GridAmbient R n) := by
  rw [coefficientEvaluation, MvPolynomial.aeval_X, targetUnit_val]
lemma coefficientEvaluation_product (s : Finset (Fin (n+1))) :
    coefficientEvaluation R n (product R n s) = embed R n (denominator R n s) := by
  simp only [coefficientEvaluation, product, map_prod, MvPolynomial.aeval_X,
    denominator, AwayCover.denominator]
lemma coefficientEvaluation_unit (s : Finset (Fin (n+1))) :
    IsUnit (coefficientEvaluation R n (product R n s)) := by
  rw [coefficientEvaluation_product]
  exact denominator_unit R n s


def scalarAt (f : MvPolynomial (Fin (n+1)) R)
    (hu : IsUnit (coefficientEvaluation R n f)) :
    Away (ProjectiveCoefficientChart.grading R n) f →ₐ[R] GridAmbient R n where
  toRingHom := HomogeneousEval.evaluate (ProjectiveCoefficientChart.grading R n)
    (coefficientEvaluation R n).toRingHom f hu
  commutes' r := by
    change Localization.awayLift (coefficientEvaluation R n).toRingHom f hu
      (algebraMap R (Away (ProjectiveCoefficientChart.grading R n) f) r).val = _
    rw [Homogeneous.val_algebraMap]
    change Localization.awayLift (coefficientEvaluation R n).toRingHom f hu
      (algebraMap (MvPolynomial (Fin (n+1)) R) (Localization.Away f) (C r)) = _
    rw [IsLocalization.Away.lift_eq]
    exact (coefficientEvaluation R n).commutes r

 
def scalarMap (s : Finset (Fin (n+1))) : Ring R n s →ₐ[R] GridAmbient R n :=
  scalarAt R n (product R n s) (coefficientEvaluation_unit R n s)

lemma coefficientEvaluation_X_unit (k : Fin (n+1)) :
    IsUnit (coefficientEvaluation R n (X k)) := by
  rw [coefficientEvaluation_X]
  exact (targetUnit R n k).isUnit

variable (k : Fin (n+1)) (s : Finset (Fin (n+1))) (hk : k ∈ s)

lemma scalarMap_chart (a : ProjectiveCoefficientChart.Chart R n k) :
    scalarMap R n s (chartMap R n k s hk a) =
      scalarAt R n (X k) (coefficientEvaluation_X_unit R n k) a := by
  apply HomogeneousEval.evaluate_awayMap

lemma scalarAt_equiv :
    (scalarAt R n (X k) (coefficientEvaluation_X_unit R n k)).comp
      (ProjectiveCoefficientChart.equiv R n k).toAlgHom = gridTarget R n k := by
  apply UniversalCoefficientChart.ext
  intro j
  change scalarAt R n (X k) (coefficientEvaluation_X_unit R n k)
    (ProjectiveCoefficientChart.forward R n k
      (UniversalCoefficientChart.coefficient R n k j)) = _
  rw [ProjectiveCoefficientChart.forward_coefficient]
  change HomogeneousEval.evaluate _ _ _ _
    (Away.mk _ _ 1 (X j) _) = _
  refine (HomogeneousEval.evaluate_mk (ProjectiveCoefficientChart.grading R n)
    (coefficientEvaluation R n).toRingHom
    (show X k ∈ ProjectiveCoefficientChart.grading R n 1 from isHomogeneous_X R k)
    (coefficientEvaluation_X_unit R n k)
    (↑((targetUnit R n k)⁻¹) : GridAmbient R n)
    (by change coefficientEvaluation R n (X k) * _ = 1
        rw [coefficientEvaluation_X, Units.mul_inv]) 1 (X j)
    (show X j ∈ ProjectiveCoefficientChart.grading R n (1 • 1) from
      isHomogeneous_X R j)).trans ?_
  change coefficientEvaluation R n (X j) * _ ^ 1 = _
  rw [pow_one, coefficientEvaluation_X, gridTarget_coefficient, ←targetUnit_val]
  exact mul_comm _ _


lemma scalarMap_coefficient (a : UniversalCoefficientChart.Ring R n k) :
    scalarMap R n s (coefficientMap R n k s hk a) = gridTarget R n k a := by
  rw [coefficientMap, RingHom.comp_apply, scalarMap_chart]
  exact DFunLike.congr_fun (scalarAt_equiv R n k) a

instance ambientAlgebra (t : Finset (Fin (n+1))) : Algebra (Ring R n t) (GridAmbient R n) :=
  (scalarMap R n t).toRingHom.toAlgebra
instance ambientTower (t : Finset (Fin (n+1))) :
    IsScalarTower R (Ring R n t) (GridAmbient R n) :=
  IsScalarTower.of_algebraMap_eq' (scalarMap R n t).comp_algebraMap.symm


variable [hks : Fact (k ∈ s)]
local instance coeffToAmbient : Algebra (UniversalCoefficientChart.Ring R n k) (GridAmbient R n) :=
  gridTargetAlgebra R n k
local instance coeffToAmbientModule : Module (UniversalCoefficientChart.Ring R n k) (GridAmbient R n) := Algebra.toModule
attribute [local instance] OAI.Lech.ProjectiveRoot.canonicalRing
attribute [local instance] OAI.Lech.ProjectiveRoot.coeffToIntersection
local instance coeffTower : IsScalarTower (UniversalCoefficientChart.Ring R n k)
    (Ring R n s) (GridAmbient R n) :=
  IsScalarTower.of_algebraMap_eq fun a => (scalarMap_coefficient R n k s hks.out a).symm


end Lech.ProjectiveRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootRestriction
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.ReesRoot.projectiveAlgebra _root_.OAI.Lech.ReesRoot.projectiveTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

lemma scalarMap_restriction {s t : Finset (Fin (n+1))} (hst : s ⊆ t) (a : Ring R n s) :
    scalarMap R n t (ringRestriction R n hst a) = scalarMap R n s a := by
  exact HomogeneousEval.evaluate_awayMap _ _ (product_homogeneous R n (t \ s))
    (product_sdiff R n hst) (coefficientEvaluation_unit R n s)
    (coefficientEvaluation_unit R n t) a

end Lech.ProjectiveRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootTwist
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ProjectiveRoot
open MvPolynomial HomogeneousLocalization ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

lemma coefficient_grid_mem (k : Fin (n+1))
    (s : Finset (Fin (n+1))) (t : Finset (Chart n)) :
    (targetUnit R n k : GridAmbient R n) ∈ grid R n (fun _ => 1) s t := by
  refine ⟨0,targetCoeff R n k,?_,?_⟩
  · change targetCoeff R n k ∈ ringSections R n (fun _ => 1 + (0:ℤ)*(s.card:ℤ)) t
    simpa only [zero_mul,add_zero] using ringSections_mono R n (fun _ => 1)
      (Finset.empty_subset t) (coefficient_mem R n k)
  · rw [pow_zero,one_mul,targetUnit_val]

lemma coefficient_inverse_grid_mem (k : Fin (n+1))
    (s : Finset (Fin (n+1))) (hk : k ∈ s) (t : Finset (Chart n)) :
    (↑((targetUnit R n k)⁻¹) : GridAmbient R n) ∈ grid R n (fun _ => -1) s t := by
  refine ⟨1,denominator R n (s.erase k),?_,?_⟩
  · have hdeg : (fun _ : Fin n => ((s.erase k).card : ℤ)) =
        levelTwist n (fun _ => -1) s.card 1 := by
      ext i
      simp only [levelTwist,Int.natCast_one,one_mul]
      have hc := Finset.card_erase_add_one hk
      omega
    rw [←hdeg]
    exact ringSections_mono R n _ (Finset.empty_subset t) (coefficient_product_mem R n (s.erase k))
  · have hd : denominator R n s = targetCoeff R n k * denominator R n (s.erase k) :=
      (Finset.mul_prod_erase s (targetCoeff R n) hk).symm
    rw [pow_one,hd,map_mul,←targetUnit_val,mul_right_comm,Units.mul_inv,one_mul]

end Lech.ProjectiveRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesCoordinate
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ProjectiveRoot
open MvPolynomial HomogeneousLocalization ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

lemma scalarMap_ratio (s : Finset (Fin (n+1))) (k j : Fin (n+1)) (hk : k ∈ s) :
    scalarMap R n s (ratio R n s k j hk) =
      (↑((targetUnit R n k)⁻¹) : GridAmbient R n) * ↑(targetUnit R n j) := by
  rw [ratio,scalarMap_coefficient,gridTarget_coefficient,targetUnit_val]
end Lech.ProjectiveRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootCechProjective
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ProjectiveRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ)

variable [LinearOrder (Chart n)]

abbrev integerCech (m : Fin n → ℤ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  (targetCech R n m).extend ComplexShape.embeddingUpNat

omit [LinearOrder (Chart n)] in
lemma integer_bounded (m : Fin n → ℤ) : (integerCech R n m).IsStrictlyLE (n+1) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro q hq
  obtain ⟨j,rfl⟩ := Int.eq_ofNat_of_zero_le (show 0≤q by omega)
  apply IsZero.of_iso _ ((targetCech R n m).extendXIso ComplexShape.embeddingUpNat (i:=j) rfl)
  apply AlternatingCech.sortedComplex_bounded
  simpa only [Fintype.card_fin] using (show n+1<j by omega)

lemma integer_homology_projective (m : Fin n → ℤ) :
    Projective ((integerCech R n m).homology (negativeCount m+1)) := by
  obtain ⟨b⟩ := (targetSigned_pure R n m).2
  let : Module.Free R ((targetCech R n m).homology (negativeCount m+1)) := Module.Free.of_basis b
  apply Projective.of_iso ((targetCech R n m).extendHomologyIso ComplexShape.embeddingUpNat
    (j:=negativeCount m+1) (by simp)).symm
  infer_instance

lemma integer_pure (m : Fin n → ℤ) (q : ℤ) (hq : q≠negativeCount m+1) :
    IsZero ((integerCech R n m).homology q) := by
  cases q with
  | ofNat q =>
    exact ((targetSigned_pure R n m).1 q (by intro h; apply hq; simp only [h]; rfl)).of_iso
      ((targetCech R n m).extendHomologyIso ComplexShape.embeddingUpNat (j:=q) rfl)
  | negSucc q =>
    apply ((integerCech R n m).exactAt_iff_isZero_homology _).mp
    apply ExactAt.of_isZero
    exact ComplexExtension.negative_zero (targetCech R n m) q



end Lech.ProjectiveRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootCechCoefficients
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ProjectiveRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open ProductSourceCover
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
  (m : Fin n → ℤ) (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive]

abbrev coefficientCech := (F.mapHomologicalComplex (.up ℤ)).obj (integerCech R n m)

variable (M : ModuleCat.{u} R)

def integerHomologyBasis : Module.Basis (Fin (signedRank m)) R
    ((integerCech R n m).homology (negativeCount m+1)) :=
  (Classical.choice (targetSigned_pure R n m).2).map
    (((targetCech R n m).extendHomologyIso
      ComplexShape.embeddingUpNat (j:=negativeCount m+1) (by simp)).toLinearEquiv).symm



end Lech.ProjectiveRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootSectionDiagram
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ProjectiveRoot
open CategoryTheory CategoryTheory.Limits ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (m : Fin n → ℤ)

abbrev zeroAugGrid (s : Finset (Fin (n+1))) :=
  AlternatingCech.zeroAugmentation R (GridAmbient R n) (fun s => grid R n m s ∅) s

end Lech.ProjectiveRoot

end

end OAI
end


