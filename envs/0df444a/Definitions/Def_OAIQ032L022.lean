-- Prove2me | Definitions.Def_OAIQ032L022
-- name    : OAIQ032L022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T20:04:06.985978+00:00
-- url     : https://prove2.me/theorems/e98f0fde-8f3a-4227-aa2c-33b24f53df9b
-- title:
--   Definitions bundle OAIQ032L022 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 83 declarations of OpenAI's Lean: 58 definitions, 4 instances and 21 theorems. The definitions and types are `OAI.Lech.ProjectiveRoot.ratio`, `OAI.Lech.ReesRoot.CoefficientRing`, `OAI.Lech.ReesRoot.ExceptionalRing`, `OAI.Lech.ReesRoot.Ring`, `OAI.Lech.ReesRoot.ScalarCechSection`, `OAI.Lech.ReesRoot.baseAlgebra`, `OAI.Lech.ReesRoot.baseAlgebra`, `OAI.Lech.ReesRoot.baseAlgebra`, `OAI.Lech.ReesRoot.baseAlgebra`, `OAI.Lech.ReesRoot.baseAlgebra`, `OAI.Lech.ReesRoot.baseAlgebra`, `OAI.Lech.ReesRoot.baseAlgebra`, `OAI.Lech.ReesRoot.baseAlgebra`, `OAI.Lech.ReesRoot.baseAlgebra`, `OAI.Lech.ReesRoot.baseModule`, `OAI.Lech.ReesRoot.baseModule`, `OAI.Lech.ReesRoot.baseModule`, `OAI.Lech.ReesRoot.baseModule`, `OAI.Lech.ReesRoot.baseModule`, `OAI.Lech.ReesRoot.baseModule`, `OAI.Lech.ReesRoot.baseModule`, `OAI.Lech.ReesRoot.bundleBaseAlgebra`, `OAI.Lech.ReesRoot.bundleBaseModule`, `OAI.Lech.ReesRoot.bundleConcreteRing`, `OAI.Lech.ReesRoot.bundleProjectiveModule`, `OAI.Lech.ReesRoot.chartRename`, `OAI.Lech.ReesRoot.coefRing`, `OAI.Lech.ReesRoot.coefficientDenominator`, `OAI.Lech.ReesRoot.coefficientPModule`, `OAI.Lech.ReesRoot.coefficientReduction`, `OAI.Lech.ReesRoot.coefficientReductionAlg`, `OAI.Lech.ReesRoot.coefficientReductionLinear`, `OAI.Lech.ReesRoot.concreteRing`, `OAI.Lech.ReesRoot.concreteRing`, `OAI.Lech.ReesRoot.concreteRing`, `OAI.Lech.ReesRoot.concreteRing`, `OAI.Lech.ReesRoot.concreteRing`, `OAI.Lech.ReesRoot.concreteRing`, `OAI.Lech.ReesRoot.concreteRing`, `OAI.Lech.ReesRoot.concreteRing` and 18 more.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_CechCartierRange`, `Multiplicity_ExceptionalCoefficientSquare`, `Multiplicity_ExceptionalFibre`, `Multiplicity_ReesCoordinate`, `Multiplicity_ReesExceptionalSquare`, `Multiplicity_ReesRegular`, `Multiplicity_ReesRootBundle`, `Multiplicity_ReesRootCech`, `Multiplicity_ReesRootEuler`, `Multiplicity_ReesRootInclusion`, `Multiplicity_ReesRootIteration`, `Multiplicity_ReesRootLayerCech`, `Multiplicity_ReesRootLayers`, `Multiplicity_ReesRootMap`, `Multiplicity_ReesRootNilpotence`, `Multiplicity_ReesUlrichCech`, `Multiplicity_RootFibreCech`.
--
--   **Imports.** It imports the bundles `OAIQ032L011`, `OAIQ032L012`, `OAIQ032L013` and `OAIQ032L015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ032L026` and `OAIQ032L027`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ032L011
import Definitions.Def_OAIQ032L012
import Definitions.Def_OAIQ032L013
import Definitions.Def_OAIQ032L015

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootMap
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


abbrev denominator (s : Finset (Fin (n+1))) : reesAlgebra I :=
  gradedMap I z hz (ProjectiveRoot.product R n s)
lemma denominator_mem (s : Finset (Fin (n+1))) : denominator I z hz s ∈ reesGrade I s.card :=
  Graded.map_mem (gradedMap I z hz) (ProjectiveRoot.product_homogeneous R n s)
lemma denominator_val (s : Finset (Fin (n+1))) :
    (denominator I z hz s : Polynomial R) = Polynomial.monomial s.card (∏ j ∈ s, z j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [denominator,ProjectiveRoot.product,Finset.prod_empty,map_one,
        OneMemClass.coe_one,Finset.card_empty,Polynomial.monomial_zero_one]
  | @insert j s hjs ih =>
      change ((gradedMap I z hz) (∏ k ∈ insert j s, X k) : Polynomial R) = _
      rw [Finset.prod_insert hjs,map_mul,gradedMap_X]
      change (Polynomial.monomial 1 (z j)) * (denominator I z hz s : Polynomial R) = _
      rw [ih,Polynomial.monomial_mul_monomial,Finset.card_insert_of_notMem hjs,
        Finset.prod_insert hjs,Nat.add_comm 1]

abbrev Ring (s : Finset (Fin (n+1))) := Away (reesGrade I) (denominator I z hz s)

 
def map (s : Finset (Fin (n+1))) : ProjectiveRoot.Ring R n s →+* Ring I z hz s :=
  Away.map (gradedMap I z hz) (ProjectiveRoot.product R n s)

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootBundle
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ReesRoot
open MvPolynomial HomogeneousLocalization IdealGraded
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j, z j ∈ I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

lemma gradedMap_smul (r : R) (a : MvPolynomial (Fin (n+1)) R) :
    gradedMap I z hz (r • a) = r • gradedMap I z hz a :=
  (MvPolynomial.aeval (R:=R) (generator I z hz)).toLinearMap.map_smul r a

def mapAlg (s : Finset (Fin (n+1))) : ProjectiveRoot.Ring R n s →ₐ[R] Ring I z hz s where
  __ := map I z hz s
  commutes' r := by
    change map I z hz s (algebraMap R (ProjectiveRoot.Ring R n s) r) = algebraMap R (Ring I z hz s) r
    have he := (Homogeneous.awayMap (ProjectiveCoefficientChart.grading R n) (reesGrade I)
      (gradedMap I z hz) (gradedMap_smul I z hz) (ProjectiveRoot.product R n s)).map_smul r 1
    change map I z hz s (r • 1) = r • map I z hz s 1 at he
    simpa only [Algebra.algebraMap_eq_smul_one,map_one] using he

instance projectiveAlgebra (s : Finset (Fin (n+1))) :
    Algebra (ProjectiveRoot.Ring R n s) (Ring I z hz s) := (map I z hz s).toAlgebra
instance projectiveTower (s : Finset (Fin (n+1))) :
    IsScalarTower R (ProjectiveRoot.Ring R n s) (Ring I z hz s) :=
  IsScalarTower.of_algebraMap_eq' (mapAlg I z hz s).comp_algebraMap.symm


local instance bundleConcreteRing (support : Finset (Fin (n+1))) :
    CommRing (Ring I z hz support) := inferInstance
local instance bundleBaseAlgebra (support : Finset (Fin (n+1))) :
    Algebra R (Ring I z hz support) :=
  Homogeneous.algebra (reesGrade I) (Submonoid.powers (denominator I z hz support))
local instance bundleBaseModule (support : Finset (Fin (n+1))) :
    Module R (Ring I z hz support) :=
  Homogeneous.module (reesGrade I) (Submonoid.powers (denominator I z hz support))
local instance bundleProjectiveModule (support : Finset (Fin (n+1))) :
    Module (ProjectiveRoot.Ring R n support) (Ring I z hz support) :=
  (projectiveAlgebra I z hz support).toModule
local instance bundleScalarComm (support : Finset (Fin (n+1))) :
    SMulCommClass (ProjectiveRoot.Ring R n support) R (Ring I z hz support) where
  smul_comm coefficient scalar element := by
    simp only [Algebra.smul_def]
    exact mul_left_comm _ _ _

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesCoordinate
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
 
def ratio (s : Finset (Fin (n+1))) (k j : Fin (n+1)) (hk : k ∈ s) : Ring R n s :=
  coefficientMap R n k s hk (UniversalCoefficientChart.coefficient R n k j)
lemma ratio_mk (s : Finset (Fin (n+1))) (k j : Fin (n+1)) (hk : k ∈ s) :
    ratio R n s k j hk = Away.mk _ (product_homogeneous R n s) 1
      (X j * projectiveRemainder R n k s) (by
        have hc := Finset.card_erase_add_one hk
        have he : 1+(s.erase k).card=s.card := by omega
        simpa only [one_smul,he] using SetLike.mul_mem_graded (isHomogeneous_X R j)
          (projectiveRemainder_homogeneous R n k s)) := by
  change chartMap R n k s hk (ProjectiveCoefficientChart.forward R n k
    (UniversalCoefficientChart.coefficient R n k j)) = _
  rw [ProjectiveCoefficientChart.forward_coefficient]
  change awayMap _ _ _ (Away.mk _ _ 1 (X j) _) = _
  refine (awayMap_mk (ProjectiveCoefficientChart.grading R n)
    (projectiveRemainder_homogeneous R n k s) (product_eq R n k s hk) 1
    (show X k ∈ ProjectiveCoefficientChart.grading R n 1 from isHomogeneous_X R k)
    (X j) (show X j ∈ ProjectiveCoefficientChart.grading R n (1 • 1) from
      isHomogeneous_X R j)).trans ?_
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk,pow_one]
end Lech.ProjectiveRoot

namespace Lech.ReesRoot
open MvPolynomial HomogeneousLocalization IdealGraded ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j, z j ∈ I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
lemma generator_relation (k j : Fin (n+1)) :
    algebraMap R (reesAlgebra I) (z k) * generator I z hz j =
      algebraMap R (reesAlgebra I) (z j) * generator I z hz k := by
  apply Subtype.ext
  change Polynomial.C (z k) * Polynomial.monomial 1 (z j) =
    Polynomial.C (z j) * Polynomial.monomial 1 (z k)
  rw [Polynomial.C_mul_monomial,Polynomial.C_mul_monomial,mul_comm]

local instance concreteRing_p1 (s : Finset (Fin (n+1))) : CommRing (ReesRoot.Ring I z hz s) := inferInstance
local instance baseAlgebra_p1 (s : Finset (Fin (n+1))) : Algebra R (ReesRoot.Ring I z hz s) :=
  Homogeneous.algebra (reesGrade I) (Submonoid.powers (denominator I z hz s))

 

lemma ratio_relation (s : Finset (Fin (n+1))) (k j : Fin (n+1)) (hk : k ∈ s) :
    algebraMap R (ReesRoot.Ring I z hz s) (z k) *
      ReesRoot.map I z hz s (ProjectiveRoot.ratio R n s k j hk) =
        algebraMap R (ReesRoot.Ring I z hz s) (z j) := by
  rw [ProjectiveRoot.ratio_mk]
  change algebraMap R (ReesRoot.Ring I z hz s) (z k) * Away.map _ _ (Away.mk _ _ 1 _ _) = _
  rw [Away.map_mk]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul,Homogeneous.val_algebraMap,
    Homogeneous.val_algebraMap,Away.val_mk,Localization.mk_eq_mk']
  rw [IsScalarTower.algebraMap_apply R (reesAlgebra I) (Localization.Away (denominator I z hz s))]
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul,IsLocalization.mk'_eq_iff_eq_mul]
  change algebraMap (reesAlgebra I) (Localization.Away (denominator I z hz s))
    (algebraMap R (reesAlgebra I) (z k) *
      gradedMap I z hz (X j * projectiveRemainder R n k s)) =
    algebraMap R (Localization.Away (denominator I z hz s)) (z j) *
      algebraMap (reesAlgebra I) (Localization.Away (denominator I z hz s)) ((denominator I z hz s)^1)
  rw [IsScalarTower.algebraMap_apply R (reesAlgebra I) (Localization.Away (denominator I z hz s)),←map_mul]
  congr 1
  rw [map_mul,gradedMap_X,←mul_assoc,generator_relation,pow_one]
  rw [mul_assoc]
  congr 1
  rw [denominator,ProjectiveRoot.product_eq R n k s hk,map_mul,gradedMap_X]
end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRegular
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ReesRoot
open HomogeneousLocalization IdealGraded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j, z j ∈ I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
lemma denominator_eq (s : Finset (Fin (n+1))) :
    denominator I z hz s = FilteredFraction.reesDenominator I (product_mem I z hz s) :=
  Subtype.ext (denominator_val I z hz s)



end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootCech
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j, z j ∈ I) (m : Fin n → ℤ)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

local instance concreteRing_p4 (s : Finset (Fin (n+1))) : CommRing (Ring I z hz s) := inferInstance
local instance baseAlgebra_p4 (s : Finset (Fin (n+1))) : Algebra R (Ring I z hz s) :=
  Homogeneous.algebra (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))
local instance baseModule_p2 (s : Finset (Fin (n+1))) : Module R (Ring I z hz s) :=
  Homogeneous.module (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))
local instance projectiveModule_p1 (s : Finset (Fin (n+1))) :
    Module (ProjectiveRoot.Ring R n s) (Ring I z hz s) := (projectiveAlgebra I z hz s).toModule
local instance scalarComm_p1 (s : Finset (Fin (n+1))) :
    SMulCommClass (ProjectiveRoot.Ring R n s) R (Ring I z hz s) where
  smul_comm a r b := by
    simp only [Algebra.smul_def]
    exact mul_left_comm _ _ _
end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootInclusion
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ReesRoot
open ProductSourceCover
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j, z j ∈ I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
local instance concreteRing_p7 (s : Finset (Fin (n+1))) : CommRing (Ring I z hz s) := inferInstance
local instance baseAlgebra_p7 (s : Finset (Fin (n+1))) : Algebra R (Ring I z hz s) :=
  Homogeneous.algebra (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))
local instance baseModule_p5 (s : Finset (Fin (n+1))) : Module R (Ring I z hz s) :=
  Homogeneous.module (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))
local instance projectiveModule_p4 (s : Finset (Fin (n+1))) :
    Module (ProjectiveRoot.Ring R n s) (Ring I z hz s) := (projectiveAlgebra I z hz s).toModule
local instance scalarComm_p4 (s : Finset (Fin (n+1))) :
    SMulCommClass (ProjectiveRoot.Ring R n s) R (Ring I z hz s) where
  smul_comm a r b := by simp only [Algebra.smul_def]; exact mul_left_comm _ _ _

open CategoryTheory CategoryTheory.Limits

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootLayers
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j, z j ∈ I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
local instance concreteRing_p10 (s : Finset (Fin (n+1))) : CommRing (Ring I z hz s) := inferInstance
local instance baseAlgebra_p10 (s : Finset (Fin (n+1))) : Algebra R (Ring I z hz s) :=
  Homogeneous.algebra (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))
local instance baseModule_p8 (s : Finset (Fin (n+1))) : Module R (Ring I z hz s) :=
  Homogeneous.module (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))
local instance scalarComm_p7 (s : Finset (Fin (n+1))) :
    SMulCommClass (ProjectiveRoot.Ring R n s) R (Ring I z hz s) where
  smul_comm a r b := by simp only [Algebra.smul_def]; exact mul_left_comm _ _ _

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootIteration
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j, z j ∈ I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
local instance concreteRing_p8 (s : Finset (Fin (n+1))) : CommRing (Ring I z hz s) := inferInstance
local instance baseAlgebra_p8 (s : Finset (Fin (n+1))) : Algebra R (Ring I z hz s) :=
  Homogeneous.algebra (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))
local instance baseModule_p6 (s : Finset (Fin (n+1))) : Module R (Ring I z hz s) :=
  Homogeneous.module (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))
local instance scalarComm_p5 (s : Finset (Fin (n+1))) :
    SMulCommClass (ProjectiveRoot.Ring R n s) R (Ring I z hz s) where
  smul_comm a r b := by simp only [Algebra.smul_def]; exact mul_left_comm _ _ _

open CategoryTheory CategoryTheory.Limits HomologicalComplex

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CechCartierRange
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (m : Fin n → ℤ)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
local instance concreteRing_p0 (s : Finset (Fin (n+1))) : CommRing (Ring I z hz s) := inferInstance
local instance baseAlgebra_p0 (s : Finset (Fin (n+1))) : Algebra R (Ring I z hz s) :=
  Homogeneous.algebra (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))
local instance baseModule_p0 (s : Finset (Fin (n+1))) : Module R (Ring I z hz s) :=
  Homogeneous.module (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))
local instance projectiveModule_p0 (s : Finset (Fin (n+1))) :
    Module (ProjectiveRoot.Ring R n s) (Ring I z hz s) := (projectiveAlgebra I z hz s).toModule
local instance scalarComm_p0 (s : Finset (Fin (n+1))) :
    SMulCommClass (ProjectiveRoot.Ring R n s) R (Ring I z hz s) where
  smul_comm a r b := by simp only [Algebra.smul_def]; exact mul_left_comm _ _ _
end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesExceptionalSquare
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

local instance concreteRing_p2 (s : Finset (Fin (n+1))) : CommRing (Ring I z hz s) := inferInstance
local instance baseAlgebra_p2 (s : Finset (Fin (n+1))) : Algebra R (Ring I z hz s) :=
  Homogeneous.algebra (reesGrade I) (Submonoid.powers (denominator I z hz s))

abbrev exceptionalDenominator (s : Finset (Fin (n+1))) :=
  FilteredFraction.quotientGraded I (denominator I z hz s)
abbrev ExceptionalRing (s : Finset (Fin (n+1))) :=
  Away (SourceGraded.targetGrade I) (exceptionalDenominator I z hz s)

lemma exceptionalDenominator_mem (s : Finset (Fin (n+1))) :
    exceptionalDenominator I z hz s ∈ SourceGraded.targetGrade I s.card := by
  unfold exceptionalDenominator
  rw [FilteredFraction.quotientGraded_apply]
  exact ⟨denominator I z hz s,denominator_mem I z hz s,rfl⟩

def chartRename (s : Finset (Fin (n+1))) :
    Ring I z hz s ≃ₐ[R] FilteredFraction.ReesChart I (product_mem I z hz s) :=
  Homogeneous.awayCongr (reesGrade I) (denominator_eq I z hz s)

def exceptionalRename (s : Finset (Fin (n+1))) :
    ExceptionalRing I z hz s ≃ₐ[R] FilteredFraction.ExceptionalChart I (product_mem I z hz s) :=
  Homogeneous.awayCongr (SourceGraded.targetGrade I)
    (congrArg (FilteredFraction.quotientGraded I) (denominator_eq I z hz s))


end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ExceptionalCoefficientSquare
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open MvPolynomial HomogeneousLocalization IdealGraded CategoryTheory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (hgen : Ideal.span (Set.range z)=I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
abbrev coefficientDenominator (s : Finset (Fin (n+1))) :=
  CoefficientReduction.graded I (n+1) (ProjectiveRoot.product R n s)
abbrev CoefficientRing (s : Finset (Fin (n+1))) :=
  Away (SourceGraded.sourceGrade I (n+1)) (coefficientDenominator I s)

lemma coefficientDenominator_mem (s : Finset (Fin (n+1))) :
    coefficientDenominator I s ∈ SourceGraded.sourceGrade I (n+1) s.card :=
  Graded.map_mem (CoefficientReduction.graded I (n+1)) (ProjectiveRoot.product_homogeneous R n s)

def coefficientReduction (s : Finset (Fin (n+1))) :
    ProjectiveRoot.Ring R n s →ₗ[R] CoefficientRing I s :=
  CoefficientReduction.chartMap I (n+1) (ProjectiveRoot.product R n s)

lemma coefficientReduction_one (s : Finset (Fin (n+1))) : coefficientReduction I s 1=1 :=
  Homogeneous.awayMap_one _ _ _ (CoefficientReduction.graded_smul I (n+1)) _
lemma coefficientReduction_mul (s : Finset (Fin (n+1))) (a b : ProjectiveRoot.Ring R n s) :
    coefficientReduction I s (a*b)=coefficientReduction I s a * coefficientReduction I s b :=
  Homogeneous.awayMap_mul _ _ _ (CoefficientReduction.graded_smul I (n+1)) _ _ _

def coefficientReductionAlg (s : Finset (Fin (n+1))) :
    ProjectiveRoot.Ring R n s →ₐ[R] CoefficientRing I s where
  toFun := coefficientReduction I s
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := coefficientReduction_one I s
  map_mul' := coefficientReduction_mul I s
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul,coefficientReduction_one,Algebra.algebraMap_eq_smul_one]

lemma coefficientReduction_surjective (s : Finset (Fin (n+1))) :
    Function.Surjective (coefficientReduction I s) :=
  CoefficientReduction.chartMap_surjective I (n+1) (ProjectiveRoot.product_homogeneous R n s)

lemma coefficientReduction_mk (s : Finset (Fin (n+1))) (j : ℕ)
    (a : MvPolynomial (Fin (n+1)) R)
    (ha : a∈ProjectiveCoefficientChart.grading R n (j • s.card)) :
    coefficientReduction I s (Away.mk _ (ProjectiveRoot.product_homogeneous R n s) j a ha) =
      Away.mk _ (coefficientDenominator_mem I s) j (CoefficientReduction.graded I (n+1) a)
        (Graded.map_mem (CoefficientReduction.graded I (n+1)) ha) :=
  Homogeneous.awayMap_mk _ _ _ (CoefficientReduction.graded_smul I (n+1)) _ _ _ _



end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ExceptionalFibre
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
local instance coefRing (s : Finset (Fin (n+1))) : CommRing (CoefficientRing I s) := inferInstance
local instance exRing (s : Finset (Fin (n+1))) : CommRing (ExceptionalRing I z hz s) := inferInstance
local instance reesRing_p0 (s : Finset (Fin (n+1))) : CommRing (Ring I z hz s) := inferInstance
local instance exModule (s : Finset (Fin (n+1))) : Module R (ExceptionalRing I z hz s) :=
  Homogeneous.module (SourceGraded.targetGrade I) (Submonoid.powers (exceptionalDenominator I z hz s))
local instance exBaseAlgebra (s : Finset (Fin (n+1))) : Algebra R (ExceptionalRing I z hz s) :=
  Homogeneous.algebra (SourceGraded.targetGrade I) (Submonoid.powers (exceptionalDenominator I z hz s))

instance coefficientAlgebra (s : Finset (Fin (n+1))) :
    Algebra (ProjectiveRoot.Ring R n s) (CoefficientRing I s) :=
  (coefficientReductionAlg I s).toRingHom.toAlgebra
private local instance coefModule_rda1077_1 (s : Finset (Fin (n+1))) : Module R (CoefficientRing I s) :=
  Homogeneous.module (SourceGraded.sourceGrade I (n+1)) (Submonoid.powers (coefficientDenominator I s))
private local instance coefBaseAlgebra_rda1077_1 (s : Finset (Fin (n+1))) : Algebra R (CoefficientRing I s) :=
  Homogeneous.algebra (SourceGraded.sourceGrade I (n+1)) (Submonoid.powers (coefficientDenominator I s))
local instance coefficientPModule (s : Finset (Fin (n+1))) :
    Module (ProjectiveRoot.Ring R n s) (CoefficientRing I s) := (coefficientAlgebra I s).toModule
instance coefficientTower (s : Finset (Fin (n+1))) :
    IsScalarTower R (ProjectiveRoot.Ring R n s) (CoefficientRing I s) :=
  IsScalarTower.of_algebraMap_eq' (coefficientReductionAlg I s).comp_algebraMap.symm



def coefficientReductionLinear (s : Finset (Fin (n+1))) :
    ProjectiveRoot.Ring R n s →ₗ[ProjectiveRoot.Ring R n s] CoefficientRing I s :=
  Algebra.linearMap _ _

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootEuler
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
local instance concreteRing_p5 (s : Finset (Fin (n+1))) : CommRing (Ring I z hz s) := inferInstance
local instance baseAlgebra_p5 (s : Finset (Fin (n+1))) : Algebra R (Ring I z hz s) :=
  Homogeneous.algebra (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))

local instance baseModule_p3 (s : Finset (Fin (n+1))) : Module R (Ring I z hz s) :=
  Homogeneous.module (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))
local instance projectiveModule_p2 (s : Finset (Fin (n+1))) :
    Module (ProjectiveRoot.Ring R n s) (Ring I z hz s) := (projectiveAlgebra I z hz s).toModule
local instance scalarComm_p2 (s : Finset (Fin (n+1))) :
    SMulCommClass (ProjectiveRoot.Ring R n s) R (Ring I z hz s) where
  smul_comm a r b := by
    simp only [Algebra.smul_def]
    exact mul_left_comm _ _ _
end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootLayerCech
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
local instance concreteRing_p9 (s : Finset (Fin (n+1))) : CommRing (Ring I z hz s) := inferInstance

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootNilpotence
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j, z j ∈ I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
local instance concreteRing_p11 (s : Finset (Fin (n+1))) : CommRing (Ring I z hz s) := inferInstance
local instance baseAlgebra_p11 (s : Finset (Fin (n+1))) : Algebra R (Ring I z hz s) :=
  Homogeneous.algebra (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))
local instance baseModule_p9 (s : Finset (Fin (n+1))) : Module R (Ring I z hz s) :=
  Homogeneous.module (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))
local instance scalarComm_p8 (s : Finset (Fin (n+1))) :
    SMulCommClass (ProjectiveRoot.Ring R n s) R (Ring I z hz s) where
  smul_comm a r b := by simp only [Algebra.smul_def]; exact mul_left_comm _ _ _

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Lech.TensorTotal

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesUlrichCech
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits UniversalSplitting
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

abbrev ScalarCechSection (s : Finset (Fin (n+1))) := (hs : PLift s.Nonempty) → Ring I z hz s
end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootFibreCech
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
local instance reesRing_p2 (s : Finset (Fin (n+1))) : CommRing (Ring I z hz s) := inferInstance
local instance reesBaseAlgebra_p2 (s : Finset (Fin (n+1))) : Algebra R (Ring I z hz s) :=
  Homogeneous.algebra (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))
private local instance reesModule_rda1077_1 (s : Finset (Fin (n+1))) : Module R (Ring I z hz s) :=
  Homogeneous.module (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))
local instance reesPModule_p2 (s : Finset (Fin (n+1))) :
    Module (ProjectiveRoot.Ring R n s) (Ring I z hz s) := (projectiveAlgebra I z hz s).toModule

end Lech.ReesRoot

end

end OAI
end


