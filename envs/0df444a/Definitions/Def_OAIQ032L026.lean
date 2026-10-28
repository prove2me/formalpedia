-- Prove2me | Definitions.Def_OAIQ032L026
-- name    : OAIQ032L026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T20:16:29.69225+00:00
-- url     : https://prove2.me/theorems/6c0c8f53-40c4-4d14-8c10-69264110cb7d
-- title:
--   Definitions bundle OAIQ032L026 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 63 declarations of OpenAI's Lean: 37 definitions, 2 instances and 24 theorems. The definitions and types are `OAI.Lech.ProductSourceCover.ringEndpointProjector`, `OAI.Lech.ProjectiveRoot.baseBasisEquiv`, `OAI.Lech.ProjectiveRoot.ringRestriction`, `OAI.Lech.ReesRoot.baseAlgebra`, `OAI.Lech.ReesRoot.baseAlgebra`, `OAI.Lech.ReesRoot.baseAlgebra`, `OAI.Lech.ReesRoot.baseModule`, `OAI.Lech.ReesRoot.baseModule`, `OAI.Lech.ReesRoot.baseModule`, `OAI.Lech.ReesRoot.baseModule`, `OAI.Lech.ReesRoot.coefficientComparison`, `OAI.Lech.ReesRoot.coefficientComparisonLinear`, `OAI.Lech.ReesRoot.coefficientRestriction`, `OAI.Lech.ReesRoot.coefficientTargetRename`, `OAI.Lech.ReesRoot.concreteRing`, `OAI.Lech.ReesRoot.concreteRing`, `OAI.Lech.ReesRoot.concreteRing`, `OAI.Lech.ReesRoot.concreteRing`, `OAI.Lech.ReesRoot.exceptionalPModule`, `OAI.Lech.ReesRoot.exceptionalPSmul`, `OAI.Lech.ReesRoot.exceptionalProjectiveMap`, `OAI.Lech.ReesRoot.powerScalarDiagram`, `OAI.Lech.ReesRoot.projectiveModule`, `OAI.Lech.ReesRoot.reduction`, `OAI.Lech.ReesRoot.reductionLinear`, `OAI.Lech.ReesRoot.reesBaseAlgebra`, `OAI.Lech.ReesRoot.reesModule`, `OAI.Lech.ReesRoot.reesPModule`, `OAI.Lech.ReesRoot.restriction`, `OAI.Lech.ReesRoot.restrictionAlg`, `OAI.Lech.ReesRoot.scalarCechDiagram`, `OAI.Lech.ReesRoot.scalarCechObj`, `OAI.Lech.ReesRoot.scalarCechRes`, `OAI.Lech.ReesRoot.scalarChartEquiv`, `OAI.Lech.RootInvariants.algebraTensorEquivRight`, `OAI.Lech.RootInvariants.eulerMiddleEquiv`, `OAI.Lech.SourceGraded.chartMapR`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_ExceptionalCoefficientSquare`, `Multiplicity_ExceptionalFibre`, `Multiplicity_LechFactorizationMap`, `Multiplicity_LechTorsionOf`, `Multiplicity_ProductSourceCoverAllowedEmpty`, `Multiplicity_ReesExceptionalSquare`, `Multiplicity_ReesRegular`, `Multiplicity_ReesRootBundle`, `Multiplicity_ReesRootLayerCech`, `Multiplicity_ReesRootMap`, `Multiplicity_ReesRootPermutation`, `Multiplicity_ReesUlrichCech`, `Multiplicity_RootBaseProjective`, `Multiplicity_RootCoactionT`, `Multiplicity_RootInvariantsWeightZero`, `Multiplicity_RootLineEuler`, `Multiplicity_RootRestriction`, `Multiplicity_RootUlrichModule`, `Multiplicity_RootUlrichNaturality`, `Multiplicity_ScalarChartComparison`.
--
--   **Imports.** It imports the bundles `OAIQ032L020`, `OAIQ032L021` and `OAIQ032L022` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ032L028` and `OAIQ032L029`; the statements `OAI.Lech.ReesRoot.coefficientComparisonLinear_kernel_zero`, `OAI.Lech.ReesRoot.scalarEuler_value` and `OAI.Lech.ReesRoot.scalarHomology_value`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ032L020
import Definitions.Def_OAIQ032L021
import Definitions.Def_OAIQ032L022

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechTorsionOf
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

lemma mapR_smul (r : R) (a : MvPolynomial (Fin h) (R ⧸ I)) :
    mapR I z hz (r • a) = r • mapR I z hz a := by
  change IdealGraded.polynomialMap I z hz (r • a) =
    r • IdealGraded.polynomialMap I z hz a
  rw [← IsScalarTower.algebraMap_smul (R ⧸ I) r a,
    ← IsScalarTower.algebraMap_smul (R ⧸ I) r (IdealGraded.polynomialMap I z hz a)]
  exact polynomialMap_smul I z hz _ _

attribute [local instance] Homogeneous.awayAddCommGroup
def chartMapR (f : MvPolynomial (Fin h) (R ⧸ I)) :=
  Homogeneous.awayMap (R := R) (A := MvPolynomial (Fin h) (R ⧸ I))
    (B := IdealGraded.Ring I) (sourceGrade I h) (targetGrade I)
    (mapR I z hz) (mapR_smul I z hz) f

attribute [local instance] kernel_addCommGroup kernel_module

end Lech.SourceGraded


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverAllowedEmpty
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
open scoped BigOperators
open scoped Classical


namespace Lech.ProductSourceCover
open AddMonoidAlgebra CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
attribute [local instance] OAI.Lech.ProductSourceCover.endpointRingDecEq
def ringEndpointProjector (j : Fin n) (b : Bool) : Ambient R n →ₗ[R] Ambient R n :=
  (coeffLinearEquiv R).symm.toLinearMap.comp
    ((endpointProjector R n j b).comp (coeffLinearEquiv R).toLinearMap)
omit [LinearOrder (Chart n)] in
lemma ringEndpointProjector_coeff (j : Fin n) (b : Bool) (x : Ambient R n) :
    (ringEndpointProjector R n j b x).coeff=endpointProjector R n j b x.coeff := by
  change (coeffLinearEquiv R) ((coeffLinearEquiv R).symm _)=_
  exact (coeffLinearEquiv R).apply_symm_apply _
omit [LinearOrder (Chart n)] in
lemma ringEndpointProjector_sum (j : Fin n) (x : Ambient R n) : ∑ b,ringEndpointProjector R n j b x=x := by
  apply (coeffLinearEquiv R).injective
  change (coeffLinearEquiv R) (∑ b,ringEndpointProjector R n j b x)=x.coeff
  rw [map_sum]
  simpa only [coeffLinearEquiv_apply,ringEndpointProjector_coeff] using endpointProjector_sum R n j x.coeff
end Lech.ProductSourceCover


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
lemma finite [Module.FaithfullyFlat A B] (ms : Fin n → ℤ) :
    Module.Finite A (module f n hn t v hv d ms) := by
  let : Module.Finite B d.S := d.finite
  let : Module.Finite B (B ⊗[A] module f n hn t v hv d ms) :=
    Module.Finite.equiv (tensorEquiv f n hn t v hv d ms).symm
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B

lemma finitePresentation [Module.FaithfullyFlat A B] (ms : Fin n → ℤ) :
    Module.FinitePresentation A (module f n hn t v hv d ms) := by
  let : Module.Free B d.S := d.free
  let : Module.Finite B d.S := d.finite
  let : Module.FinitePresentation B d.S := Module.finitePresentation_of_projective B d.S
  let : Module.FinitePresentation B (B ⊗[A] module f n hn t v hv d ms) :=
    Module.FinitePresentation.of_equiv (tensorEquiv f n hn t v hv d ms).symm
  exact ModuleDescent.finitePresentation (B := B)

lemma flat [Module.FaithfullyFlat A B] (ms : Fin n → ℤ) :
    Module.Flat A (module f n hn t v hv d ms) := by
  let : Module.Flat B d.S := d.flat
  let : Module.Flat B (B ⊗[A] module f n hn t v hv d ms) :=
    Module.Flat.of_linearEquiv (tensorEquiv f n hn t v hv d ms)
  exact Module.Flat.of_flat_tensorProduct A (module f n hn t v hv d ms) B

lemma projective [Module.FaithfullyFlat A B] (ms : Fin n → ℤ) :
    Module.Projective A (module f n hn t v hv d ms) := by
  let := finitePresentation f n hn t v hv d ms
  let := flat f n hn t v hv d ms
  exact Module.Flat.projective_of_finitePresentation

lemma rankAtStalk [Module.FaithfullyFlat A B] (ms : Fin n → ℤ)
    (p : PrimeSpectrum A) : Module.rankAtStalk (module f n hn t v hv d ms) p=n.factorial := by
  obtain ⟨q,hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := B) p
  let : Nontrivial B := q.nontrivial
  let := flat f n hn t v hv d ms
  let := finite f n hn t v hv d ms
  let : Module.Free B d.S := d.free
  have he := congrFun (Module.rankAtStalk_eq_of_equiv (tensorEquiv f n hn t v hv d ms)) q
  rw [Module.rankAtStalk_baseChange,hq,Module.rankAtStalk_eq_finrank_of_free (R := B) (M := d.S)] at he
  exact he.trans (by simpa using Module.finrank_eq_card_basis d.basis)
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

attribute [local instance] OAI.Lech.RootInvariants.weightZeroRightBaseAlgebra
attribute [local instance] OAI.Lech.RootInvariants.weightZeroRightBaseScalarTower
def algebraTensorEquivRight [Module.Flat A B] :
    algebra f n hn t v hv d ⊗[A] B ≃ₐ[algebra f n hn t v hv d] d.S :=
  AlgEquiv.ofBijective (algebraBaseMapRight f n hn t v hv d) (by
    change Function.Bijective ((algebraBaseMapRight f n hn t v hv d).restrictScalars A)
    rw [algebraBaseMapRight_eq]
    exact (algebraTensorEquiv f n hn t v hv d).bijective.comp
      (Algebra.TensorProduct.comm A (algebra f n hn t v hv d) B).bijective)

lemma algebra_faithfullyFlat [Module.FaithfullyFlat A B] :
    Module.FaithfullyFlat (algebra f n hn t v hv d) d.S := by
  let : Module.FaithfullyFlat (algebra f n hn t v hv d) (algebra f n hn t v hv d ⊗[A] B) := inferInstance
  exact Module.FaithfullyFlat.of_linearEquiv _ _ (algebraTensorEquivRight f n hn t v hv d).symm.toLinearEquiv
end


open Polynomial
open scoped TensorProduct
universe u

end Lech.RootInvariants

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


namespace Lech.RootInvariants


open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))

attribute [local instance] OAI.Lech.RootInvariants.tensorWorkAlgebra
lemma weight_add (ms ns : Fin n → ℤ) : RootCoaction.weight f n hn t v hv d (ms+ns)=
    RootCoaction.weight f n hn t v hv d ms*RootCoaction.weight f n hn t v hv d ns := by
  simp only [RootCoaction.weight_eq,Pi.add_apply,zpow_add,Finset.prod_mul_distrib]

end Lech.RootInvariants

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootRestriction
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.projectiveAlgebra _root_.OAI.Lech.ReesRoot.projectiveTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


def ringRestriction {s t : Finset (Fin (n+1))} (hst : s ⊆ t) :
    Ring R n s →+* Ring R n t :=
  awayMap (ProjectiveCoefficientChart.grading R n) (product_homogeneous R n (t \ s))
    (product_sdiff R n hst)

end Lech.ProjectiveRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootMap
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.projectiveAlgebra _root_.OAI.Lech.ReesRoot.projectiveTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

lemma denominator_subsets {s t : Finset (Fin (n+1))} (hst : s ⊆ t) :
    denominator I z hz t = denominator I z hz s * denominator I z hz (t \ s) := by
  simpa only [denominator,map_mul] using
    congrArg (gradedMap I z hz) (ProjectiveRoot.product_sdiff R n hst)

def restriction {s t : Finset (Fin (n+1))} (hst : s ⊆ t) :
    Ring I z hz s →+* Ring I z hz t :=
  awayMap (reesGrade I) (denominator_mem I z hz (t \ s)) (denominator_subsets I z hz hst)

 

lemma map_restriction {s t : Finset (Fin (n+1))} (hst : s ⊆ t)
    (a : ProjectiveRoot.Ring R n s) :
    map I z hz t (ProjectiveRoot.ringRestriction R n hst a) =
      restriction I z hz hst (map I z hz s a) := by
  obtain ⟨j,b,hb,rfl⟩ := Away.mk_surjective _ (ProjectiveRoot.product_homogeneous R n s) a
  change Away.map _ _ (awayMap _ _ _ (Away.mk _ _ j b hb)) =
    awayMap _ _ _ (Away.map _ _ (Away.mk _ _ j b hb))
  rw [awayMap_mk,Away.map_mk,Away.map_mk,awayMap_mk]
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk,map_mul,map_pow,denominator]

lemma restriction_self (s : Finset (Fin (n+1))) (a : Ring I z hz s) :
    restriction I z hz (Finset.Subset.refl s) a = a := by
  have h1 : denominator I z hz s = denominator I z hz s * 1 := (mul_one _).symm
  exact (HomogeneousEval.awayMap_same _ _ (SetLike.one_mem_graded (reesGrade I)) _ h1 a).trans
    (HomogeneousEval.awayMap_one _ (denominator_mem I z hz s) h1 a)

lemma restriction_comp {s t v : Finset (Fin (n+1))}
    (hst : s ⊆ t) (htv : t ⊆ v) (a : Ring I z hz s) :
    restriction I z hz htv (restriction I z hz hst a) =
      restriction I z hz (hst.trans htv) a := by
  have h1 := denominator_subsets I z hz hst
  have h2 := denominator_subsets I z hz htv
  have h3 : denominator I z hz v = denominator I z hz s *
      (denominator I z hz (t \ s) * denominator I z hz (v \ t)) := by rw [h2,h1,mul_assoc]
  exact (HomogeneousEval.awayMap_comp _ (denominator_mem I z hz s)
    (denominator_mem I z hz (t \ s)) (denominator_mem I z hz (v \ t)) h1 h2 h3 a).trans
      (HomogeneousEval.awayMap_same _ _ _ _ _ _)

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootBundle
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

def restrictionAlg {s t : Finset (Fin (n+1))} (hst : s ⊆ t) :
    Ring I z hz s →ₐ[R] Ring I z hz t where
  __ := restriction I z hz hst
  commutes' r := HomogeneousEval.awayMap_algebraMap _ _ _ r

variable {s t v : Finset (Fin (n+1))} (hs : s.Nonempty) (ht : t.Nonempty)
  (hv : v.Nonempty) (m : Fin n → ℤ)

attribute [local instance] OAI.Lech.ReesRoot.bundleConcreteRing
attribute [local instance] OAI.Lech.ReesRoot.bundleBaseModule
attribute [local instance] OAI.Lech.ReesRoot.bundleProjectiveModule
def coefficientRestriction (hst : s ⊆ t) :
    Ring I z hz s →ₛₗ[ProjectiveRoot.ringRestriction R n hst] Ring I z hz t where
  toFun := restriction I z hz hst
  map_add' := map_add _
  map_smul' a b := by
    change restriction I z hz hst (map I z hz s a * b) =
      map I z hz t (ProjectiveRoot.ringRestriction R n hst a) * restriction I z hz hst b
    rw [map_mul,map_restriction]

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



theorem coordinate_smul_injective (s : Finset (Fin (n+1))) (k : Fin (n+1)) (hk : k ∈ s) :
    Function.Injective (fun x : Ring I z hz s => (z k) • x) := by
  change Function.Injective (fun x : Away (reesGrade I) (denominator I z hz s) => (z k) • x)
  rw [denominator_eq]
  apply FilteredFraction.chart_smul_injective
  exact Finset.dvd_prod_of_mem z hk

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesExceptionalSquare
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

lemma graded_square (a : MvPolynomial (Fin (n+1)) R) :
    FilteredFraction.quotientGraded I (gradedMap I z hz a) =
      SourceGraded.mapR I z hgen (CoefficientReduction.graded I (n+1) a) := by
  have hh : (FilteredFraction.quotientGraded I).toRingHom.comp (gradedMap I z hz).toRingHom =
      (SourceGraded.mapR I z hgen).toRingHom.comp (CoefficientReduction.graded I (n+1)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change FilteredFraction.quotientGraded I (gradedMap I z hz (C r)) = _
      rw [gradedMap_C]
      change quotientR I (algebraMap R (reesAlgebra I) r) =
        MvPolynomial.aeval (IdealGraded.generator I z hgen) (MvPolynomial.map (Ideal.Quotient.mk I) (C r))
      rw [MvPolynomial.map_C,MvPolynomial.aeval_C]
      exact IsScalarTower.algebraMap_apply R (R ⧸ I) (IdealGraded.Ring I) r
    · intro j
      change FilteredFraction.quotientGraded I (gradedMap I z hz (X j)) = _
      rw [gradedMap_X]
      change quotientR I (generator I z hz j) =
        MvPolynomial.aeval (IdealGraded.generator I z hgen) (MvPolynomial.map (Ideal.Quotient.mk I) (X j))
      rw [MvPolynomial.map_X,MvPolynomial.aeval_X]
      rfl
  exact RingHom.congr_fun hh a


attribute [local instance] OAI.Lech.ReesRoot.concreteRing_p2
attribute [local instance] OAI.Lech.ReesRoot.baseAlgebra_p2
def reduction (s : Finset (Fin (n+1))) : Ring I z hz s →ₐ[R] ExceptionalRing I z hz s :=
  (exceptionalRename I z hz s).symm.toAlgHom.comp
    ((FilteredFraction.chartReductionAlg I (product_mem I z hz s)).comp
      (chartRename I z hz s).toAlgHom)

lemma reduction_mk (s : Finset (Fin (n+1))) (j : ℕ) (a : reesAlgebra I)
    (ha : a ∈ reesGrade I (j • s.card)) :
    reduction I z hz s (Away.mk (reesGrade I) (denominator_mem I z hz s) j a ha) =
      Away.mk (SourceGraded.targetGrade I) (exceptionalDenominator_mem I z hz s) j
        (FilteredFraction.quotientGraded I a) (Graded.map_mem (FilteredFraction.quotientGraded I) ha) := by
  change (exceptionalRename I z hz s).symm
    (FilteredFraction.chartReduction I (product_mem I z hz s)
      (chartRename I z hz s (Away.mk (reesGrade I) (denominator_mem I z hz s) j a ha))) = _
  unfold chartRename
  rw [Homogeneous.awayCongr_mk _ _ _ (FilteredFraction.reesDenominator_mem I (product_mem I z hz s)),
      FilteredFraction.chartReduction_mk]
  unfold exceptionalRename
  exact Homogeneous.awayCongr_symm_mk _ _ _ _ _ _ _

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ExceptionalCoefficientSquare
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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



def coefficientTargetRename (s : Finset (Fin (n+1))) :
    Away (SourceGraded.targetGrade I) (SourceGraded.mapR I z hgen (coefficientDenominator I s)) ≃ₐ[R]
      ExceptionalRing I z hz s :=
  Homogeneous.awayCongr (SourceGraded.targetGrade I)
    (graded_square I z hz hgen (ProjectiveRoot.product R n s)).symm

def coefficientComparison (s : Finset (Fin (n+1))) :
    CoefficientRing I s →ₗ[R] ExceptionalRing I z hz s :=
  (coefficientTargetRename I z hz hgen s).toLinearMap.comp
    (SourceGraded.chartMapR I z hgen (coefficientDenominator I s))

lemma coefficientComparison_mk (s : Finset (Fin (n+1))) (j : ℕ)
    (a : MvPolynomial (Fin (n+1)) (R ⧸ I))
    (ha : a∈SourceGraded.sourceGrade I (n+1) (j • s.card)) :
    coefficientComparison I z hz hgen s (Away.mk _ (coefficientDenominator_mem I s) j a ha) =
      Away.mk _ (exceptionalDenominator_mem I z hz s) j (SourceGraded.mapR I z hgen a)
        (Graded.map_mem (SourceGraded.mapR I z hgen) ha) := by
  change coefficientTargetRename I z hz hgen s
    (Homogeneous.awayMap _ _ _ (SourceGraded.mapR_smul I z hgen) _ (Away.mk _ _ j a ha)) = _
  rw [Homogeneous.awayMap_mk]
  unfold coefficientTargetRename
  exact Homogeneous.awayCongr_mk _ _ _ _ _ _ _

lemma local_square (s : Finset (Fin (n+1))) (a : ProjectiveRoot.Ring R n s) :
    reduction I z hz s (map I z hz s a) =
      coefficientComparison I z hz hgen s (coefficientReduction I s a) := by
  obtain ⟨j,b,hb,rfl⟩ := Away.mk_surjective _ (ProjectiveRoot.product_homogeneous R n s) a
  change reduction I z hz s (Away.map (gradedMap I z hz) _ (Away.mk _ _ j b hb))=_
  rw [Away.map_mk,reduction_mk]
  rw [coefficientReduction_mk,coefficientComparison_mk]
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk]
  congr 1
  exact graded_square I z hz hgen b

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
attribute [local instance] OAI.Lech.ReesRoot.reesRing_p0
local instance reesModule_p0 (s : Finset (Fin (n+1))) : Module R (Ring I z hz s) :=
  Homogeneous.module (reesGrade I) (Submonoid.powers (denominator I z hz s))
local instance reesBaseAlgebra_p0 (s : Finset (Fin (n+1))) : Algebra R (Ring I z hz s) :=
  Homogeneous.algebra (reesGrade I) (Submonoid.powers (denominator I z hz s))

attribute [local instance] OAI.Lech.ReesRoot.exRing
attribute [local instance] OAI.Lech.ReesRoot.exBaseAlgebra
def exceptionalProjectiveMap (s : Finset (Fin (n+1))) :
    ProjectiveRoot.Ring R n s →ₐ[R] ExceptionalRing I z hz s :=
  (reduction I z hz s).comp (mapAlg I z hz s)
instance exceptionalAlgebra (s : Finset (Fin (n+1))) :
    Algebra (ProjectiveRoot.Ring R n s) (ExceptionalRing I z hz s) :=
  (exceptionalProjectiveMap I z hz s).toRingHom.toAlgebra
local instance exceptionalPSmul (s : Finset (Fin (n+1))) :
    SMul (ProjectiveRoot.Ring R n s) (ExceptionalRing I z hz s) :=
  ⟨fun a b => exceptionalProjectiveMap I z hz s a*b⟩
attribute [local instance] OAI.Lech.ReesRoot.exModule
local instance exceptionalPModule (s : Finset (Fin (n+1))) :
    Module (ProjectiveRoot.Ring R n s) (ExceptionalRing I z hz s) := (exceptionalAlgebra I z hz s).toModule
local instance reesPModule_p0 (s : Finset (Fin (n+1))) :
    Module (ProjectiveRoot.Ring R n s) (Ring I z hz s) := (projectiveAlgebra I z hz s).toModule
instance exceptionalTower (s : Finset (Fin (n+1))) :
    IsScalarTower R (ProjectiveRoot.Ring R n s) (ExceptionalRing I z hz s) :=
  IsScalarTower.of_algebraMap_eq' (exceptionalProjectiveMap I z hz s).comp_algebraMap.symm



def reductionLinear (s : Finset (Fin (n+1))) :
    Ring I z hz s →ₗ[ProjectiveRoot.Ring R n s] ExceptionalRing I z hz s where
  toFun := reduction I z hz s
  map_add' := map_add _
  map_smul' a b := by
    change reduction I z hz s (map I z hz s a * b) =
      reduction I z hz s (map I z hz s a) * reduction I z hz s b
    exact map_mul _ _ _

attribute [local instance] OAI.Lech.ReesRoot.coefRing
private local instance coefModule_rb6bc84_1 (s : Finset (Fin (n+1))) : Module R (CoefficientRing I s) :=
  Homogeneous.module (SourceGraded.sourceGrade I (n+1)) (Submonoid.powers (coefficientDenominator I s))
attribute [local instance] OAI.Lech.ReesRoot.coefficientPModule
def coefficientComparisonLinear (s : Finset (Fin (n+1))) :
    CoefficientRing I s →ₗ[ProjectiveRoot.Ring R n s] ExceptionalRing I z hz s where
  toFun := coefficientComparison I z hz hgen s
  map_add' := map_add _
  map_smul' a b := by
    obtain ⟨c,rfl⟩ := coefficientReduction_surjective I s b
    change coefficientComparison I z hz hgen s (coefficientReduction I s a * coefficientReduction I s c)=
      reduction I z hz s (map I z hz s a) * coefficientComparison I z hz hgen s (coefficientReduction I s c)
    rw [←coefficientReduction_mul,←local_square,←local_square,map_mul,map_mul]

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootLayerCech
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
attribute [local instance] OAI.Lech.ReesRoot.concreteRing_p9
local instance baseAlgebra_p9 (s : Finset (Fin (n+1))) : Algebra R (Ring I z hz s) :=
  Homogeneous.algebra (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))
local instance baseModule_p7 (s : Finset (Fin (n+1))) : Module R (Ring I z hz s) :=
  Homogeneous.module (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))
local instance scalarComm_p6 (s : Finset (Fin (n+1))) :
    SMulCommClass (ProjectiveRoot.Ring R n s) R (Ring I z hz s) where
  smul_comm a r b := by simp only [Algebra.smul_def]; exact mul_left_comm _ _ _

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootUlrichModule
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace Lech.RootInvariants
open Polynomial UniversalSplitting
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))

attribute [local instance] OAI.Lech.RootInvariants.rootUlrichModuleAlgebra
lemma tensorEquiv_one_tmul [Module.Flat A B] (ms : Fin n → ℤ)
    (x : module f n hn t v hv d ms) : tensorEquiv f n hn t v hv d ms (1 ⊗ₜ[A] x)=(x:d.S) := by
  change (1:B) • (x:d.S)=(x:d.S)
  exact one_smul B _



end Lech.RootInvariants

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootUlrichNaturality
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace Lech.ReesRoot
open UniversalSplitting ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
local instance concreteRing_p14 (s : Finset (Fin (n+1))) : CommRing (Ring I z hz s) := inferInstance
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
local instance concreteRing_p13 (s : Finset (Fin (n+1))) : CommRing (Ring I z hz s) := inferInstance
local instance baseAlgebra_p13 (s : Finset (Fin (n+1))) : Algebra R (Ring I z hz s) := inferInstance
local instance baseModule_p11 (s : Finset (Fin (n+1))) : Module R (Ring I z hz s) := inferInstance

abbrev scalarCechObj (s : Finset (Fin (n+1))) : ModuleCat.{u} R := ModuleCat.of R (ScalarCechSection I z hz s)

def scalarCechRes {s t : Finset (Fin (n+1))} (hst : s ⊆ t) :
    scalarCechObj I z hz s ⟶ scalarCechObj I z hz t :=
  ModuleCat.ofHom {
    toFun x ht := if hs : s.Nonempty then restrictionAlg I z hz hst (x ⟨hs⟩) else 0
    map_add' x y := by
      funext ht
      split_ifs with hs
      · exact (restrictionAlg I z hz hst).toRingHom.map_add (x ⟨hs⟩) (y ⟨hs⟩)
      · exact (add_zero 0).symm
    map_smul' r x := by
      funext ht
      split_ifs with hs
      · exact (restrictionAlg I z hz hst).toLinearMap.map_smul r (x ⟨hs⟩)
      · exact (smul_zero r).symm }

lemma scalarCechRes_apply {s t : Finset (Fin (n+1))} (hst : s ⊆ t)
    (hs : s.Nonempty) (ht : t.Nonempty) (x : ScalarCechSection I z hz s) :
    (scalarCechRes I z hz hst).hom x ⟨ht⟩=restriction I z hz hst (x ⟨hs⟩) := by
  change (if hs : s.Nonempty then _ else _)=_
  rw [dite_eq_left hs]
  rfl

def scalarCechDiagram : FiniteModuleCech.Diagram R (Fin (n+1)) where
  obj := scalarCechObj I z hz
  res := scalarCechRes I z hz
  res_self s := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext hs
    rw [scalarCechRes_apply I z hz _ hs.down hs.down,restriction_self]
    rfl
  res_comp {s t v} hst htv := by
    classical
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext hv
    obtain ⟨hv⟩ := hv
    by_cases hs : s.Nonempty
    · have ht := hs.mono hst
      change (scalarCechRes I z hz htv).hom ((scalarCechRes I z hz hst).hom x) ⟨hv⟩=_
      rw [scalarCechRes_apply I z hz htv ht hv,scalarCechRes_apply I z hz hst hs ht,
        scalarCechRes_apply I z hz (hst.trans htv) hs hv,restriction_comp]
    · change (if ht : t.Nonempty then restrictionAlg I z hz htv
          (if hs : s.Nonempty then _ else 0) else 0)=if hs : s.Nonempty then _ else 0
      rw [dite_eq_right hs]
      split_ifs
      · exact (restrictionAlg I z hz htv).toRingHom.map_zero
      · rfl

 
def powerScalarDiagram : FiniteModuleCech.Diagram R (Fin (n+1)) where
  obj s := ModuleCat.of R (PowerIndex n → ScalarCechSection I z hz s)
  res hst := ModuleCat.ofHom {
    toFun x e := (scalarCechRes I z hz hst).hom (x e)
    map_add' _ _ := by funext e; exact map_add _ _ _
    map_smul' r x := by
      funext e
      change (scalarCechRes I z hz hst).hom (r • x e)=r • (scalarCechRes I z hz hst).hom (x e)
      exact (scalarCechRes I z hz hst).hom.map_smul r (x e) }
  res_self s := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext e
    change (scalarCechRes I z hz (Finset.Subset.refl s)).hom (x e)=x e
    funext hs
    rw [scalarCechRes_apply I z hz _ hs.down hs.down,restriction_self]
  res_comp {s t v} hst htv := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext e
    have he : scalarCechRes I z hz hst ≫ scalarCechRes I z hz htv =
        scalarCechRes I z hz (hst.trans htv) := (scalarCechDiagram I z hz).res_comp hst htv
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom he) (x e)



end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootPermutation
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits ProductSourceCover
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j, z j∈I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
local instance concreteRing_p12 (s : Finset (Fin (n+1))) : CommRing (Ring I z hz s) := inferInstance
local instance baseAlgebra_p12 (s : Finset (Fin (n+1))) : Algebra R (Ring I z hz s) :=
  Homogeneous.algebra (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))

local instance baseModule_p10 (s : Finset (Fin (n+1))) : Module R (Ring I z hz s) :=
  Homogeneous.module (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))
local instance projectiveModule_p9 (s : Finset (Fin (n+1))) :
    Module (ProjectiveRoot.Ring R n s) (Ring I z hz s) := (projectiveAlgebra I z hz s).toModule
local instance scalarComm_p9 (s : Finset (Fin (n+1))) :
    SMulCommClass (ProjectiveRoot.Ring R n s) R (Ring I z hz s) where
  smul_comm a r b := by
    simp only [Algebra.smul_def]
    exact mul_left_comm _ _ _
end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootBaseProjective
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.ReesRoot.projectiveAlgebra _root_.OAI.Lech.ReesRoot.projectiveTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ProjectiveRoot
open HomogeneousLocalization MvPolynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

def baseBasisEquiv (s : Finset (Fin (n+1))) : Ring R n s ≃ₗ[R]
    ({e : PartialLaurent.exponents s // PartialLaurent.degree s e=0} →₀ R) :=
  (Homogeneous.zeroPieceEquiv (ProjectiveCoefficientChart.grading R n)
    (product_homogeneous R n s)).trans
    ((PartialLaurent.polynomialTwistEquiv R s 0).trans
      (PartialLaurent.homogeneousEquiv R s 0))

lemma ring_base_free (s : Finset (Fin (n+1))) : Module.Free R (Ring R n s) :=
  Module.Free.of_equiv (baseBasisEquiv R n s).symm

end Lech.ProjectiveRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootLineEuler
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace Lech.RootInvariants
open Polynomial
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))

variable [Module.FaithfullyFlat A B]

attribute [local instance] OAI.Lech.RootInvariants.lineEulerInstance1
def eulerMiddleEquiv (m : Fin n → ℤ) :
    B ⊗[A] (module f n hn t v hv d m × module f n hn t v hv d m) ≃ₗ[B] d.S × d.S :=
  TensorProduct.prodRight A B B _ _ ≪≫ₗ
    (tensorEquiv f n hn t v hv d m).prodCongr (tensorEquiv f n hn t v hv d m)

end Lech.RootInvariants

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ScalarChartComparison
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory HomogeneousLocalization IdealGraded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
local instance concreteRing_p15 (s : Finset (Fin (n+1))) : CommRing (Ring I z hz s) := inferInstance
local instance baseModule_p12 (s : Finset (Fin (n+1))) : Module R (Ring I z hz s) := inferInstance

def scalarChartEquiv (s : Finset (Fin (n+1))) :
    Ring I z hz s ≃ₗ[R] FilteredCech.term I z 0 s :=
  (chartRename I z hz s).toLinearEquiv.trans (FilteredFraction.chartEquiv I (product_mem I z hz s))

end Lech.ReesRoot

end

end OAI
end


