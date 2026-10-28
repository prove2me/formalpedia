-- Prove2me | Definitions.Def_OAIQ032L038
-- name    : OAIQ032L038
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T22:36:21.250031+00:00
-- url     : https://prove2.me/theorems/ed861291-6768-4b75-95ba-ed524697d78d
-- title:
--   Definitions bundle OAIQ032L038 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 26 declarations of OpenAI's Lean: 18 definitions and 8 theorems. The definitions and types are `OAI.Lech.ReesRoot.coordinateCechMap`, `OAI.Lech.ReesRoot.eulerCechLeft`, `OAI.Lech.ReesRoot.eulerCechRight`, `OAI.Lech.ReesRoot.powerSectionBasis`, `OAI.Lech.ReesRoot.quotientAtRowIso`, `OAI.Lech.ReesRoot.quotientShortComplex`, `OAI.Lech.ReesRoot.rootFibreMap`, `OAI.Lech.ReesRoot.rootLayerAt`, `OAI.Lech.ReesRoot.sectionChartModule`, `OAI.Lech.ReesRoot.sectionGroup`, `OAI.Lech.ReesRoot.sectionModule`, `OAI.Lech.ReesRoot.sectionModule`, `OAI.Lech.ReesRoot.sectionModule`, `OAI.Lech.ReesRoot.sectionsRestrictionRing`, `OAI.Lech.ReesRoot.ulrichCechEquiv`, `OAI.Lech.ReesRoot.unfilteredEuler`, `OAI.Lech.ReesRoot.zeroOrderIso`, `OAI.Lech.ReesRoot.zeroOrderTotalIso`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_ExceptionalFibre`, `Multiplicity_ReesRootCechEuler`, `Multiplicity_ReesRootEuler`, `Multiplicity_ReesRootEulerFunction`, `Multiplicity_ReesRootLayerTotal`, `Multiplicity_ReesRootPermutation`, `Multiplicity_ReesRootQuotient`, `Multiplicity_ReesRootUnfiltered`, `Multiplicity_ReesUlrichCech`, `Multiplicity_RootFibreCech`, `Multiplicity_RootUlrichNaturality`.
--
--   **Imports.** It imports the bundles `OAIQ032L034` and `OAIQ032L035` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ032L039`; the statements `OAI.Lech.ReesRoot.rootLayerAtTotal_negative`, `OAI.Lech.ReesRoot.rootLayerAtTotal_nonnegative`, `OAI.Lech.ReesRoot.unfilteredEuler_affine_step`, `OAI.Lech.ReesRoot.unfilteredEuler_diagonal` and `OAI.Lech.ReesRoot.unfilteredEuler_rank`; the proofs of `OAI.Lech.ReesRoot.ambient_euler_additive`, `OAI.Lech.ReesRoot.fibreCech_homology`, `OAI.Lech.ReesRoot.quotientAtTotal_euler`, `OAI.Lech.ReesRoot.quotientAtTotal_finite`, `OAI.Lech.ReesRoot.sum_estimate`, `OAI.Lech.ReesRoot.unfilteredEuler_affine_step` and `OAI.Lech.ReesRoot.unfilteredTotal_finite`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ032L034
import Definitions.Def_OAIQ032L035

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



attribute [local instance] OAI.Lech.ReesRoot.reesRing_p0
attribute [local instance] OAI.Lech.ReesRoot.reesModule_p0
attribute [local instance] OAI.Lech.ReesRoot.reesBaseAlgebra_p0
attribute [local instance] OAI.Lech.ReesRoot.reesPModule_p0
attribute [local instance] OAI.Lech.ReesRoot.sectionGroup_p1
private local instance reesScalarComm_ra03341_1 (s : Finset (Fin (n+1))) :
    SMulCommClass (ProjectiveRoot.Ring R n s) R (Ring I z hz s) where
  smul_comm a r b := by simp only [Algebra.smul_def]; exact mul_left_comm _ _ _
private local instance sectionModule_ra03341_1 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module R (Sections I z hz s hs m) := TensorProduct.leftModule
def rootFibreMap (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    RootFibreSections I s hs m →ₗ[R] ExceptionalSections I z hz s hs m :=
  TensorIdeal.fibreMap I (A:=ProjectiveRoot.Ring R n s) (B:=Ring I z hz s)
    (ProjectiveRoot.Sections R n s hs m)

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootEuler
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

attribute [local instance] OAI.Lech.ReesRoot.concreteRing_p5
attribute [local instance] OAI.Lech.ReesRoot.baseAlgebra_p5
attribute [local instance] OAI.Lech.ReesRoot.sectionChartModule_p0
attribute [local instance] OAI.Lech.ReesRoot.baseModule_p3
attribute [local instance] OAI.Lech.ReesRoot.projectiveModule_p2
attribute [local instance] OAI.Lech.ReesRoot.sectionModule_p4
lemma eulerLeft_baseChange (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) (i : Fin n) :
    (TensorProduct.prodRight (ProjectiveRoot.Ring R n s) (Ring I z hz s) (Ring I z hz s)
      (ProjectiveRoot.Sections R n s hs (Pi.single i 1+m))
      (ProjectiveRoot.Sections R n s hs (Pi.single i 1+m))).toLinearMap.comp
        ((ProjectiveRoot.eulerLeft R n s hs m i).baseChange (Ring I z hz s))=
      (eulerLeft I z hz s hs m i).comp (LinearEquiv.refl (Ring I z hz s) _).toLinearMap := by
  apply LinearMap.ext
  intro x
  induction x using OAI.tensorInductionOn with
  | tmul a x =>
      apply Prod.ext
      · rfl
      · change a ⊗ₜ[ProjectiveRoot.Ring R n s] (-ProjectiveRoot.coordinateMul R n s hs m i true x)=
          -(a ⊗ₜ[ProjectiveRoot.Ring R n s] (ProjectiveRoot.coordinateMul R n s hs m i true x))
        exact TensorProduct.tmul_neg _ _
  | add x y hx hy => simp only [map_add,hx,hy]

lemma eulerRight_baseChange (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) (i : Fin n) :
    (LinearEquiv.refl (Ring I z hz s) _).toLinearMap.comp
      ((ProjectiveRoot.eulerRight R n s hs m i).baseChange (Ring I z hz s))=
        (eulerRight I z hz s hs m i).comp
          (TensorProduct.prodRight (ProjectiveRoot.Ring R n s) (Ring I z hz s) (Ring I z hz s)
            (ProjectiveRoot.Sections R n s hs (Pi.single i 1+m))
            (ProjectiveRoot.Sections R n s hs (Pi.single i 1+m))).toLinearMap := by
  apply LinearMap.ext
  intro x
  induction x using OAI.tensorInductionOn with
  | tmul a x =>
      change a ⊗ₜ[ProjectiveRoot.Ring R n s]
        (ProjectiveRoot.coordinateMul R n s hs _ i true x.1+ProjectiveRoot.coordinateMul R n s hs _ i false x.2)=_
      rw [TensorProduct.tmul_add]
      rfl
  | add x y hx hy => simp only [map_add,hx,hy]

lemma euler_baseChange_shortExact (s : Finset (Fin (n+1))) (hs : s.Nonempty)
    (m : Fin n → ℤ) (i : Fin n) :
    Function.Injective ((ProjectiveRoot.eulerLeft R n s hs m i).baseChange (Ring I z hz s)) ∧
      Function.Exact ((ProjectiveRoot.eulerLeft R n s hs m i).baseChange (Ring I z hz s))
        ((ProjectiveRoot.eulerRight R n s hs m i).baseChange (Ring I z hz s)) ∧
      Function.Surjective ((ProjectiveRoot.eulerRight R n s hs m i).baseChange (Ring I z hz s)) := by
  let := (ProjectiveRoot.sections_properties R n hs (Pi.single i 1+(Pi.single i 1+m))).2.1
  obtain ⟨hi, he, hq⟩ := ProjectiveRoot.euler_shortExact R n s hs m i
  exact ModuleSequence.baseChange (Ring I z hz s)
    (ProjectiveRoot.eulerLeft R n s hs m i) (ProjectiveRoot.eulerRight R n s hs m i) hi he hq

attribute [local instance] OAI.Lech.ReesRoot.sectionGroup_p4
lemma euler_shortExact (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) (i : Fin n) :
    Function.Injective (eulerLeft I z hz s hs m i) ∧
      Function.Exact (eulerLeft I z hz s hs m i) (eulerRight I z hz s hs m i) ∧
        Function.Surjective (eulerRight I z hz s hs m i) := by
  obtain ⟨hi, he, hq⟩ := euler_baseChange_shortExact I z hz s hs m i
  apply ModuleSequence.transport
    (A := Ring I z hz s)
    (M := Ring I z hz s ⊗[ProjectiveRoot.Ring R n s] ProjectiveRoot.Sections R n s hs m)
    (N := Ring I z hz s ⊗[ProjectiveRoot.Ring R n s]
      (ProjectiveRoot.Sections R n s hs (Pi.single i 1+m) × ProjectiveRoot.Sections R n s hs (Pi.single i 1+m)))
    (P := Ring I z hz s ⊗[ProjectiveRoot.Ring R n s]
      ProjectiveRoot.Sections R n s hs (Pi.single i 1+(Pi.single i 1+m)))
    ((ProjectiveRoot.eulerLeft R n s hs m i).baseChange (Ring I z hz s))
    ((ProjectiveRoot.eulerRight R n s hs m i).baseChange (Ring I z hz s))
    (eulerLeft I z hz s hs m i) (eulerRight I z hz s hs m i)
    (LinearEquiv.refl _ _) (TensorProduct.prodRight _ (Ring I z hz s) (Ring I z hz s) _ _)
    (LinearEquiv.refl _ _)
  · exact eulerLeft_baseChange I z hz s hs m i
  · exact eulerRight_baseChange I z hz s hs m i
  · exact hi
  · exact he
  · exact hq

lemma coordinateMul_natural {s t : Finset (Fin (n+1))} (hs : s.Nonempty) (ht : t.Nonempty)
    (hst : s ⊆ t) (m : Fin n → ℤ) (i : Fin n) (b : Bool) (x : Sections I z hz s hs m) :
    sectionsRestriction I z hz hs ht (Pi.single i 1+m) hst (coordinateMul I z hz s hs m i b x)=
      coordinateMul I z hz t ht m i b (sectionsRestriction I z hz hs ht m hst x) := by
  induction x using OAI.tensorInductionOn with
  | tmul a x =>
      change sectionsRestriction I z hz hs ht _ hst
        (a ⊗ₜ[ProjectiveRoot.Ring R n s] ProjectiveRoot.coordinateMul R n s hs m i b x)=_
      rw [sectionsRestriction_tmul,ProjectiveRoot.coordinateMul_natural,sectionsRestriction_tmul]
      rfl
  | add x y hx hy => simp only [map_add,hx,hy]

lemma coordinateCechHom_natural (m : Fin n → ℤ) (i : Fin n) (b : Bool)
    {s t : Finset (Fin (n+1))} (hst : s ⊆ t) (x : cechObj I z hz m s) :
    (coordinateCechHom I z hz m i b t).hom ((cechRes I z hz m hst).hom x)=
      (cechRes I z hz (Pi.single i 1+m) hst).hom ((coordinateCechHom I z hz m i b s).hom x) := by
  classical
  funext ht
  by_cases hs : s.Nonempty
  · change coordinateMul I z hz t ht.down m i b ((cechRes I z hz m hst).hom x ht)=_
    rw [cechRes_apply I z hz m hst hs ht.down]
    change _=(cechRes I z hz (Pi.single i 1+m) hst).hom
      (fun hs => coordinateMul I z hz s hs.down m i b (x hs)) ht
    rw [cechRes_apply I z hz _ hst hs ht.down,coordinateMul_natural]
  · change coordinateMul I z hz t ht.down m i b (if hs : s.Nonempty then _ else 0)=
      if hs : s.Nonempty then _ else 0
    simp only [dite_eq_right hs,map_zero]

 
def coordinateCechMap (m : Fin n → ℤ) (i : Fin n) (b : Bool) :
    FiniteModuleCech.Map (cechDiagram I z hz m) (cechDiagram I z hz (Pi.single i 1+m)) where
  app s := coordinateCechHom I z hz m i b s
  naturality {s t} hst := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact coordinateCechHom_natural I z hz m i b hst
end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootCechEuler
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex FiniteModuleCech
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (m : Fin n → ℤ) (i : Fin n)

def eulerCechLeft : Map (cechDiagram I z hz m)
    (prodDiagram (cechDiagram I z hz (Pi.single i 1+m)) (cechDiagram I z hz (Pi.single i 1+m))) :=
  (coordinateCechMap I z hz m i false).prodLift (coordinateCechMap I z hz m i true).neg

def eulerCechRight : Map
    (prodDiagram (cechDiagram I z hz (Pi.single i 1+m)) (cechDiagram I z hz (Pi.single i 1+m)))
    (cechDiagram I z hz (Pi.single i 1+(Pi.single i 1+m))) :=
  (coordinateCechMap I z hz (Pi.single i 1+m) i true).prodDesc
    (coordinateCechMap I z hz (Pi.single i 1+m) i false)

lemma eulerCech_zero (s : Finset (Fin (n+1))) :
    (eulerCechLeft I z hz m i).app s ≫ (eulerCechRight I z hz m i).app s=0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext hs
  exact (euler_shortExact I z hz s hs.down m i).2.1.apply_apply_eq_zero (x hs)

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootUlrichNaturality
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
attribute [local instance] OAI.Lech.ReesRoot.concreteRing_p14
private local instance baseAlgebra_ra03341_1 (s : Finset (Fin (n+1))) : Algebra R (Ring I z hz s) := inferInstance
local instance sectionModule_p7 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module (Ring I z hz s) (Sections I z hz s hs m) := inferInstance

lemma sectionsRestriction_smul {s t : Finset (Fin (n+1))} (hs : s.Nonempty) (ht : t.Nonempty)
    (m : Fin n → ℤ) (hst : s ⊆ t) (a : Ring I z hz s) (x : Sections I z hz s hs m) :
    sectionsRestriction I z hz hs ht m hst (a • x)=
      restriction I z hz hst a • sectionsRestriction I z hz hs ht m hst x := by
  induction x using OAI.tensorInductionOn with
  | tmul b x =>
      simp only [TensorProduct.smul_tmul',smul_eq_mul,sectionsRestriction_tmul,map_mul]
  | add x y hx hy => rw [smul_add,map_add,map_add,hx,hy,smul_add]

 
def sectionsRestrictionRing {s t : Finset (Fin (n+1))} (hs : s.Nonempty) (ht : t.Nonempty)
    (m : Fin n → ℤ) (hst : s ⊆ t) :
    Sections I z hz s hs m →ₛₗ[restriction I z hz hst] Sections I z hz t ht m where
  toFun := sectionsRestriction I z hz hs ht m hst
  map_add' := map_add _
  map_smul' := sectionsRestriction_smul I z hz hs ht m hst

def powerSectionBasis (s : Finset (Fin (n+1))) (hs : s.Nonempty) :
    Module.Basis (PowerIndex n) (Ring I z hz s)
      (Sections I z hz s hs (fun i => (powerWeight n i:ℤ))) :=
  (ProjectiveRoot.powerSectionBasis R n s hs).baseChange (Ring I z hz s)

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesUlrichCech
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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



attribute [local instance] OAI.Lech.ReesRoot.concreteRing_p13
attribute [local instance] OAI.Lech.ReesRoot.baseAlgebra_p13
attribute [local instance] OAI.Lech.ReesRoot.baseModule_p11
def ulrichCechEquiv (s : Finset (Fin (n+1))) :
    cechObj I z hz (fun i => (powerWeight n i:ℤ)) s ≃ₗ[R] (powerScalarDiagram I z hz).obj s where
  toFun x e hs := (powerSectionBasis I z hz s hs.down).equivFun (x hs) e
  invFun x hs := (powerSectionBasis I z hz s hs.down).equivFun.symm (fun e => x e hs)
  left_inv x := by funext hs; exact LinearEquiv.symm_apply_apply _ _
  right_inv x := by funext e hs; exact congrFun (LinearEquiv.apply_symm_apply
      (powerSectionBasis I z hz s hs.down).equivFun (fun e => x e hs)) e
  map_add' x y := by funext e hs; exact congrFun (map_add (powerSectionBasis I z hz s hs.down).equivFun _ _) e
  map_smul' r x := by
    funext e hs
    exact congrFun (map_smul ((powerSectionBasis I z hz s hs.down).equivFun.restrictScalars R) r (x hs)) e

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootPermutation
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
attribute [local instance] OAI.Lech.ReesRoot.concreteRing_p12
attribute [local instance] OAI.Lech.ReesRoot.baseAlgebra_p12
local instance sectionChartModule_p6 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module (Ring I z hz s) (Sections I z hz s hs m) := inferInstance


attribute [local instance] OAI.Lech.ReesRoot.baseModule_p10
attribute [local instance] OAI.Lech.ReesRoot.projectiveModule_p9
attribute [local instance] OAI.Lech.ReesRoot.scalarComm_p9
local instance sectionModule_p5 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module R (Sections I z hz s hs m) := TensorProduct.leftModule

end Lech.ReesRoot

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
attribute [local instance] OAI.Lech.ReesRoot.reesModule_p2
attribute [local instance] OAI.Lech.ReesRoot.reesBaseAlgebra_p2
attribute [local instance] OAI.Lech.ReesRoot.reesPModule_p2
local instance sectionGroup_p12 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    AddCommGroup (Sections I z hz s hs m) := TensorProduct.addCommGroup
attribute [local instance] OAI.Lech.ReesRoot.reesScalarComm_p2
local instance sectionModule_p6 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module R (Sections I z hz s hs m) := TensorProduct.leftModule

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootLayerTotal
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ} [LinearOrder (Chart n)]
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (m : Fin n → ℤ)
  (hgen : Ideal.span (Set.range z)=I) (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (b : ℤ → ℕ) (B : ∀ p,Module.Basis (Fin (b p)) R (F.X p))
  (hflat : ∀ p,Module.Flat R (F.X p))


def rootLayerAt (r : Fin n → ℤ) (l : ℤ) : TotalGhost.Bic (R:=R) :=
  layerAt I z hz F (n+1) s hd (baseTwist (n+1) s (fun j => l-1-r j))

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootUnfiltered
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂ MonoidalCategory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ) (m : Fin n → ℤ)



def zeroOrderIso :
    enlargedAt I z hz F h 0 (IdealFiltered.zero_order_bound I F) m ≅ unfilteredAt I z hz F m :=
  Hom.isoOfComponents (fun p => Hom.isoOfComponents
    (fun q => (IdealFiltered.zeroTermEquiv I F h ((cechZ I z hz m).X q) p).toModuleIso)
    (by intro q r hqr; rfl)) (by
      intro p r hpr
      apply Hom.ext
      funext q
      rfl)

 
def zeroOrderTotalIso :
    (enlargedAt I z hz F h 0 (IdealFiltered.zero_order_bound I F) m).total (.up ℤ) ≅
      (TensorTotal.Right.functor F).obj (cechZ I z hz m) :=
  BicomplexTotal.functor.mapIso (zeroOrderIso I z hz F h m)

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootEulerFunction
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits FiniteModuleCech ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (ell : TorsionLength I) (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ)

 
def unfilteredEuler (m : Fin n → ℤ) : ℝ := tensorEuler ell F h (cechDiagram I z hz m)

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootQuotient
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂ MonoidalCategory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ,(F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (m : Fin n → ℤ)


def quotientShortComplex : ShortComplex (TotalGhost.Bic (R:=R)) :=
  ShortComplex.mk (ambientInclusion I z hz F h s hd m) (quotientProjection I z hz F h s hd m)
    (ambient_quotient_zero I z hz F h s hd m)


def quotientAtRowIso (p : ℤ) :
    (((curriedTensor (ModuleCat.{u} R)).obj (F.X p)).mapHomologicalComplex (.up ℤ)).obj
      (((TensorIdeal.quotientFunctor (I^(IdealFiltered.order h s p))).mapHomologicalComplex (.up ℤ)).obj
        (cechZ I z hz m)) ≅ (quotientAt I z hz F h s hd m).X p :=
  IdealFiltered.quotientRowIso I F h s hd (cechZ I z hz m) p

end Lech.ReesRoot

end

end OAI
end


