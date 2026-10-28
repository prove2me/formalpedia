-- Prove2me | Definitions.Def_OAIQ032L032
-- name    : OAIQ032L032
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T21:57:50.926412+00:00
-- url     : https://prove2.me/theorems/e689e8f1-7a92-49e6-b7b1-0438e8a59935
-- title:
--   Definitions bundle OAIQ032L032 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 43 declarations of OpenAI's Lean: 16 definitions, 2 instances and 25 theorems. The definitions and types are `OAI.Lech.ProductSourceCover.restriction`, `OAI.Lech.ProjectiveRoot.CechSection`, `OAI.Lech.ProjectiveRoot.Sections`, `OAI.Lech.ProjectiveRoot.cechDiagram`, `OAI.Lech.ProjectiveRoot.cechObj`, `OAI.Lech.ProjectiveRoot.cechRes`, `OAI.Lech.ProjectiveRoot.chartBaseChange`, `OAI.Lech.ProjectiveRoot.chartRestriction`, `OAI.Lech.ProjectiveRoot.coeffSectionsModule`, `OAI.Lech.ProjectiveRoot.coeffSectionsSMul`, `OAI.Lech.ProjectiveRoot.coordinateMul`, `OAI.Lech.ProjectiveRoot.overlapEquiv`, `OAI.Lech.ProjectiveRoot.reducedCech`, `OAI.Lech.ProjectiveRoot.sectionsRestriction`, `OAI.Lech.ProjectiveRoot.sectionsRestrictionBase`, `OAI.Lech.ProjectiveRoot.tensorAdd`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_ExceptionalRootCohomology`, `Multiplicity_ReducedRootCohomology`, `Multiplicity_RootChartAtlasGlobalCoefficient`, `Multiplicity_RootChartUlrich`, `Multiplicity_RootHomogeneousCoordinates`, `Multiplicity_RootOverlap`, `Multiplicity_RootPermutation`, `Multiplicity_RootProjectiveEuler`, `Multiplicity_RootRestriction`, `Multiplicity_RootSectionBase`, `Multiplicity_RootSectionDiagram`.
--
--   **Imports.** It imports the bundles `OAIQ032L030` and `OAIQ032L031` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ032L034`, `OAIQ032L035` and `OAIQ032L036`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ032L030
import Definitions.Def_OAIQ032L031

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootChartAtlasGlobalCoefficient
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ProjectiveRoot.ambientAlgebra _root_.OAI.Lech.ProjectiveRoot.ambientTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.RootChartAtlas
open Polynomial ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
variable [Module.FaithfullyFlat (A R n k) B]
include t v hv d in
lemma section_finitePresentation (m : Fin n → ℤ) :
    Module.FinitePresentation (A R n k) (sectionModule R n k m) := by
  let := RootInvariants.finitePresentation (f R n k) n (hn R n k) t v hv d m
  exact Module.FinitePresentation.of_equiv (globalSectionEquiv R n k t v hv d m)
include t v hv d in
lemma section_projective (m : Fin n → ℤ) :
    Module.Projective (A R n k) (sectionModule R n k m) := by
  let := RootInvariants.projective (f R n k) n (hn R n k) t v hv d m
  exact Module.Projective.of_equiv (globalSectionEquiv R n k t v hv d m)
include t v hv d in
lemma section_rank (m : Fin n → ℤ) (p : PrimeSpectrum (A R n k)) :
    Module.rankAtStalk (sectionModule R n k m) p=n.factorial := by
  rw [←congrFun (Module.rankAtStalk_eq_of_equiv (globalSectionEquiv R n k t v hv d m)) p]
  exact RootInvariants.rankAtStalk (f R n k) n (hn R n k) t v hv d m p
end Lech.RootChartAtlas


namespace Lech.ProductSourceCover
open Polynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
 

theorem sectionModule_properties (m : Fin n → ℤ) :
    Module.FinitePresentation (UniversalCoefficientChart.Ring R n k) (sectionModule R n k m) ∧
    Module.Projective (UniversalCoefficientChart.Ring R n k) (sectionModule R n k m) ∧
    ∀ p : PrimeSpectrum (UniversalCoefficientChart.Ring R n k),
      Module.rankAtStalk (sectionModule R n k m) p=n.factorial := by
  let f := UniversalCoefficientChart.form R n k
  let : Module.FaithfullyFlat (UniversalCoefficientChart.Ring R n k) (PrimitiveRootModule.chart f) :=
    PrimitiveChart.faithfullyFlat_away f (UniversalCoefficientChart.form_primitive R n k)
  exact ⟨RootChartAtlas.section_finitePresentation R n k (PrimitiveRootModule.coordinate f)
      (PrimitiveRootModule.valueUnit f) (PrimitiveRootModule.eval_valueUnit f)
      (PrimitiveRootModule.splitting f n (UniversalCoefficientChart.form_degree R n k)) m,
    RootChartAtlas.section_projective R n k (PrimitiveRootModule.coordinate f)
      (PrimitiveRootModule.valueUnit f) (PrimitiveRootModule.eval_valueUnit f)
      (PrimitiveRootModule.splitting f n (UniversalCoefficientChart.form_degree R n k)) m,
    RootChartAtlas.section_rank R n k (PrimitiveRootModule.coordinate f)
      (PrimitiveRootModule.valueUnit f) (PrimitiveRootModule.eval_valueUnit f)
      (PrimitiveRootModule.splitting f n (UniversalCoefficientChart.form_degree R n k)) m⟩
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))

attribute [local instance] OAI.Lech.ProductSourceCover.locTargetModule
def restriction (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (hk : k∈s) :
    sectionModule R n k m →ₗ[UniversalCoefficientChart.Ring R n k] overlapModule R n k m s hk :=
  Submodule.inclusion (grid_target_mono R n m ∅ (Finset.singleton_subset_iff.mpr hk))
lemma restriction_injective (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (hk : k∈s) :
    Function.Injective (restriction R n k m s hk) := Submodule.inclusion_injective _
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))


attribute [local instance] OAI.Lech.ProductSourceCover.localizedTarget
local instance localizedTargetModule_r855d54_1 : Module (UniversalCoefficientChart.Ring R n k) (GridAmbient R n) := Algebra.toModule
instance restriction_localized (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (hk : k∈s) :
    IsLocalizedModule (Submonoid.powers (targetProduct R n k s)) (restriction R n k m s hk) where
  map_units c := by
    obtain ⟨N,hN⟩ := c.property
    rw [Module.End.isUnit_iff]
    constructor
    · intro x y h
      apply Subtype.ext
      have he := congrArg Subtype.val h
      change gridTarget R n k (c:UniversalCoefficientChart.Ring R n k)*(x:GridAmbient R n)=
        gridTarget R n k (c:UniversalCoefficientChart.Ring R n k)*(y:GridAmbient R n) at he
      rw [←hN,map_pow,←targetProductUnit_val] at he
      exact (IsUnit.pow N (targetProductUnit R n k s).isUnit).mul_left_cancel he
    · intro x
      refine ⟨⟨_,inverse_mem_overlap R n k m s hk x N⟩,Subtype.ext ?_⟩
      change gridTarget R n k (c:UniversalCoefficientChart.Ring R n k)*
        ((↑((targetProductUnit R n k s)⁻¹):GridAmbient R n)^N*(x:GridAmbient R n))=(x:GridAmbient R n)
      rw [←hN,map_pow,←targetProductUnit_val,←mul_assoc,←mul_pow,Units.mul_inv,one_pow,one_mul]
  surj x := by
    obtain ⟨N,hN⟩ := (grid_localization_iff R n k m s hk x).mp x.property
    refine ⟨(⟨(targetProduct R n k s)^N • (x:GridAmbient R n),hN⟩,
      ⟨(targetProduct R n k s)^N,N,rfl⟩),Subtype.ext rfl⟩
  exists_of_eq h := by
    refine ⟨1,?_⟩
    simpa only [OneMemClass.coe_one,one_smul] using restriction_injective R n k m s hk h
end Lech.ProductSourceCover


end
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


variable (k : Fin (n+1)) (s : Finset (Fin (n+1))) (hk : k ∈ s)

include hk in
 

lemma scalar_mem (m : Fin n → ℤ) (a : Ring R n s) (x : GridAmbient R n)
    (hx : x ∈ grid R n m s ∅) :
    scalarMap R n s a * x ∈ grid R n m s ∅ := by
  let := coefficientAlgebra R n k s hk
  let := isLocalization R n k s hk
  obtain ⟨⟨b,c⟩,hb⟩ := IsLocalization.surj (Submonoid.powers (targetProduct R n k s)) a
  obtain ⟨N,hN⟩ := c.property
  change a * coefficientMap R n k s hk c = coefficientMap R n k s hk b at hb
  have he := congrArg (scalarMap R n s) hb
  rw [map_mul, scalarMap_coefficient, scalarMap_coefficient, ←hN, map_pow,
    ←targetProductUnit_val] at he
  have hbmem : gridTarget R n k b * x ∈ grid R n m s ∅ :=
    (overlapModule R n k m s hk).smul_mem b hx
  have hmem := inverse_mem_overlap R n k m s hk ⟨_,hbmem⟩ N
  have heq : scalarMap R n s a * x =
      (↑((targetProductUnit R n k s)⁻¹) : GridAmbient R n)^N * (gridTarget R n k b * x) := by
    rw [←he]
    calc
      _ = ((↑((targetProductUnit R n k s)⁻¹) : GridAmbient R n)^N *
          (targetProductUnit R n k s : GridAmbient R n)^N) * (scalarMap R n s a * x) := by
            rw [←mul_pow, Units.inv_mul, one_pow, one_mul]
      _ = _ := by ring
  rw [heq]
  exact hmem


def Sections (t : Finset (Fin (n+1))) (ht : t.Nonempty) (m : Fin n → ℤ) :
    Submodule (Ring R n t) (GridAmbient R n) where
  carrier := grid R n m t ∅
  zero_mem' := (grid R n m t ∅).zero_mem
  add_mem' := (grid R n m t ∅).add_mem
  smul_mem' a x hx := by
    obtain ⟨j,hj⟩ := ht
    exact scalar_mem R n j t hj m a x hx

variable [hks : Fact (k ∈ s)]
variable (hs : s.Nonempty) (m : Fin n → ℤ)
attribute [local instance] OAI.Lech.ProjectiveRoot.canonicalRing
attribute [local instance] OAI.Lech.ProjectiveRoot.coeffToIntersection
attribute [local instance] OAI.Lech.ProjectiveRoot.coeffToAmbient
attribute [local instance] OAI.Lech.ProjectiveRoot.coeffTower
local instance coeffSectionsSMul : SMul (UniversalCoefficientChart.Ring R n k) (Sections R n s hs m) :=
  (Sections R n s hs m).smul
attribute [local instance] OAI.Lech.ProjectiveRoot.coeffToAmbientModule
local instance coeffSectionsModule : Module (UniversalCoefficientChart.Ring R n k) (Sections R n s hs m) :=
  (Sections R n s hs m).module'
local instance coeffSectionsTower : IsScalarTower (UniversalCoefficientChart.Ring R n k)
    (Ring R n s) (Sections R n s hs m) := (Sections R n s hs m).isScalarTower
attribute [local instance] OAI.Lech.ProjectiveRoot.coeffToIntersectionModule
local instance tensorAdd : AddCommGroup (Ring R n s ⊗[UniversalCoefficientChart.Ring R n k]
    sectionModule R n k m) := TensorProduct.addCommGroup


def overlapEquiv : overlapModule R n k m s hks.out ≃ₗ[UniversalCoefficientChart.Ring R n k]
    Sections R n s hs m where
  toFun x := ⟨x.val,x.property⟩
  invFun x := ⟨x.val,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 
def chartRestriction : sectionModule R n k m →ₗ[UniversalCoefficientChart.Ring R n k]
    Sections R n s hs m :=
  (overlapEquiv R n k s hs m).toLinearMap.comp (ProductSourceCover.restriction R n k m s hks.out)

instance chartRestriction_localized :
    IsLocalizedModule (Submonoid.powers (targetProduct R n k s))
      (chartRestriction R n k s hs m) :=
  IsLocalizedModule.of_linearEquiv _ (ProductSourceCover.restriction R n k m s hks.out)
    (overlapEquiv R n k s hs m)


attribute [local instance] OAI.Lech.ProjectiveRoot.coeffLocalization
def chartBaseChange : Ring R n s ⊗[UniversalCoefficientChart.Ring R n k]
    sectionModule R n k m ≃ₗ[Ring R n s] Sections R n s hs m :=
  (IsLocalizedModule.isBaseChange (Submonoid.powers (targetProduct R n k s))
    (Ring R n s) (chartRestriction R n k s hs m)).equiv

lemma chartBaseChange_one (x : sectionModule R n k m) :
    chartBaseChange R n k s hs m (1 ⊗ₜ[UniversalCoefficientChart.Ring R n k] x) =
      chartRestriction R n k s hs m x := by
  exact (IsBaseChange.equiv_tmul _ _ _).trans (one_smul _ _)

include hks in
 

theorem Sections_properties :
    Module.FinitePresentation (Ring R n s) (Sections R n s hs m) ∧
    Module.Projective (Ring R n s) (Sections R n s hs m) ∧
    ∀ p : PrimeSpectrum (Ring R n s),
      Module.rankAtStalk (Sections R n s hs m) p = n.factorial := by
  obtain ⟨hfp,hpr,hr⟩ := sectionModule_properties R n k m
  let := hfp
  let := hpr
  refine ⟨Module.FinitePresentation.of_equiv (chartBaseChange R n k s hs m),
    Module.Projective.of_equiv (chartBaseChange R n k s hs m),?_⟩
  intro p
  rw [←Module.rankAtStalk_eq_of_equiv (chartBaseChange R n k s hs m), Module.rankAtStalk_baseChange]
  exact hr _


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

variable {s t v : Finset (Fin (n+1))} (hs : s.Nonempty) (ht : t.Nonempty) (hv : v.Nonempty)
variable (m : Fin n → ℤ)

 

def sectionsRestriction (hst : s ⊆ t) :
    Sections R n s hs m →ₛₗ[ringRestriction R n hst] Sections R n t ht m where
  toFun x := ⟨x.val,grid_target_mono R n m ∅ hst x.property⟩
  map_add' _ _ := rfl
  map_smul' a x := by
    apply Subtype.ext
    change scalarMap R n s a * x.val = scalarMap R n t (ringRestriction R n hst a) * x.val
    rw [scalarMap_restriction]

end Lech.ProjectiveRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootSectionBase
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.ReesRoot.projectiveAlgebra _root_.OAI.Lech.ReesRoot.projectiveTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ProjectiveRoot
open ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
variable {s t v : Finset (Fin (n+1))} (hs : s.Nonempty) (ht : t.Nonempty) (hv : v.Nonempty)
  (m : Fin n → ℤ)

def sectionsRestrictionBase (hst : s ⊆ t) :
    Sections R n s hs m →ₗ[R] Sections R n t ht m where
  toFun := sectionsRestriction R n hs ht m hst
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma sectionsRestrictionBase_self (x : Sections R n s hs m) :
    sectionsRestrictionBase R n hs hs m (Finset.Subset.refl s) x=x := rfl

set_option maxHeartbeats 1000000 in
lemma sectionsRestrictionBase_comp (hst : s ⊆ t) (htv : t ⊆ v) (x : Sections R n s hs m) :
    sectionsRestrictionBase R n ht hv m htv (sectionsRestrictionBase R n hs ht m hst x)=
      sectionsRestrictionBase R n hs hv m (hst.trans htv) x := rfl

end Lech.ProjectiveRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootSectionDiagram
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.ReesRoot.projectiveAlgebra _root_.OAI.Lech.ReesRoot.projectiveTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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

abbrev CechSection (s : Finset (Fin (n+1))) :=
  (hs : PLift s.Nonempty) → Sections R n s hs.down m
abbrev cechObj (s : Finset (Fin (n+1))) : ModuleCat.{u} R :=
  ModuleCat.of R (CechSection R n m s)

def cechRes {s t : Finset (Fin (n+1))} (hst : s ⊆ t) : cechObj R n m s ⟶ cechObj R n m t :=
  ModuleCat.ofHom {
    toFun x ht := if hs : s.Nonempty then sectionsRestrictionBase R n hs ht.down m hst (x ⟨hs⟩) else 0
    map_add' x y := by
      funext ht
      split_ifs <;> simp only [Pi.add_apply,map_add,add_zero]
    map_smul' r x := by
      funext ht
      split_ifs <;> simp only [Pi.smul_apply,map_smul,RingHom.id_apply,smul_zero] }

lemma cechRes_apply {s t : Finset (Fin (n+1))} (hst : s ⊆ t)
    (hs : s.Nonempty) (ht : t.Nonempty) (x : CechSection R n m s) :
    (cechRes R n m hst).hom x ⟨ht⟩ = sectionsRestrictionBase R n hs ht m hst (x ⟨hs⟩) := by
  change (if hs : s.Nonempty then _ else _) = _
  rw [dite_eq_left hs]

lemma cechRes_self (s : Finset (Fin (n+1))) :
    cechRes R n m (Finset.Subset.refl s) = 𝟙 (cechObj R n m s) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext hs
  exact (cechRes_apply R n m _ hs.down hs.down x).trans (sectionsRestrictionBase_self R n hs.down m (x hs))

lemma cechRes_comp {s t v : Finset (Fin (n+1))} (hst : s ⊆ t) (htv : t ⊆ v) :
    cechRes R n m hst ≫ cechRes R n m htv = cechRes R n m (hst.trans htv) := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext hv
  obtain ⟨hv⟩ := hv
  by_cases hs : s.Nonempty
  · have ht : t.Nonempty := hs.mono hst
    change (cechRes R n m htv).hom ((cechRes R n m hst).hom x) ⟨hv⟩ = _
    rw [cechRes_apply R n m htv ht hv,cechRes_apply R n m hst hs ht,
      cechRes_apply R n m (hst.trans htv) hs hv]
    exact sectionsRestrictionBase_comp R n hs ht hv m hst htv (x ⟨hs⟩)
  · change (if ht : t.Nonempty then
      sectionsRestrictionBase R n ht hv m htv (if hs : s.Nonempty then _ else 0) else 0) =
        if hs : s.Nonempty then _ else 0
    rw [dite_eq_right hs]
    split_ifs <;> simp only [map_zero]

def cechDiagram : FiniteModuleCech.Diagram R (Fin (n+1)) where
  obj := cechObj R n m
  res := cechRes R n m
  res_self := cechRes_self R n m
  res_comp := cechRes_comp R n m

end Lech.ProjectiveRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReducedRootCohomology
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ProjectiveRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex ProductSourceCover
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
  (m : Fin n → ℤ) (I : Ideal R)

abbrev reducedCech := FiniteModuleCech.complex (FiniteModuleCech.reduction (cechDiagram R n m) I)

end Lech.ProjectiveRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ExceptionalRootCohomology
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ProjectiveRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
  (m : Fin n → ℤ) (I : Ideal R)

omit [LinearOrder (Chart n)] in
lemma cech_empty_zero : IsZero ((cechDiagram R n m).obj ∅) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun f g => funext fun hs => ?_⟩
  exact (Finset.not_nonempty_empty hs.down).elim

end Lech.ProjectiveRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootHomogeneousCoordinates
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
variable [Module.FaithfullyFlat A B]
local instance homogeneousCoordinatesAlgebra_r855d54_1 : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
variable (C : Type u) [CommRing C] [Algebra (algebra f n hn t v hv d) C]
  (σ : Fin n → Bool) (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C)



local instance homogeneousCoordinatesTower_r855d54_1 : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
lemma commonBasis_homogeneous (m e : Fin n → ℕ) (he : ∀ i,e i ≤ m i) :
    (commonBasis f n hn t v hv d C σ φ (fun i => (m i:ℤ))).symm
      (1 ⊗ₜ[algebra f n hn t v hv d]
        ((overAlgebraEquiv f n hn t v hv d _).symm (homogeneousSection f n hn t v hv d m e he))) =
      ∏ i,φ (chartCoordinate f n hn t v hv d σ i true)^(e i)*
        φ (chartCoordinate f n hn t v hv d σ i false)^(m i-e i) := by
  classical
  let := algebra_faithfullyFlat f n hn t v hv d
  have hinj : Function.Injective (algebraMap C (commonExtension f n hn t v hv d C)) :=
    FaithfulSMul.algebraMap_injective C (commonExtension f n hn t v hv d C)
  apply hinj
  apply (commonWeight f n hn t v hv d C σ φ (fun i => (m i:ℤ))).mul_left_inj.mp
  rw [←commonBasis_value_apply,LinearEquiv.apply_symm_apply]
  change (1:C) ⊗ₜ[algebra f n hn t v hv d]
      (∏ i,(-d.roots i)^(e i)*(1+algebraMap B d.S t*d.roots i)^(m i-e i)) = _
  let inc : d.S →ₐ[algebra f n hn t v hv d] commonExtension f n hn t v hv d C :=
    Algebra.TensorProduct.includeRight
  change inc (∏ i,(-d.roots i)^(e i)*(1+algebraMap B d.S t*d.roots i)^(m i-e i)) = _
  rw [commonWeight_product f n hn t v hv d C σ φ (fun i => (m i:ℤ))]
  simp only [map_prod,map_mul,map_pow,Units.coe_prod,zpow_natCast,Units.val_pow_eq_pow_val]
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hx := commonCoordinate_relation f n hn t v hv d C σ φ i true
  have hy := commonCoordinate_relation f n hn t v hv d C σ φ i false
  change algebraMap C (commonExtension f n hn t v hv d C) (φ (chartCoordinate f n hn t v hv d σ i true))*
    (commonWeight f n hn t v hv d C σ φ (Pi.single i 1) : commonExtension f n hn t v hv d C)=inc (-d.roots i) at hx
  change algebraMap C (commonExtension f n hn t v hv d C) (φ (chartCoordinate f n hn t v hv d σ i false))*
    (commonWeight f n hn t v hv d C σ φ (Pi.single i 1) : commonExtension f n hn t v hv d C)=
      inc (1+algebraMap B d.S t*d.roots i) at hy
  rw [←hx,←hy,mul_pow,mul_pow]
  conv_rhs => rhs; rw [←Nat.add_sub_of_le (he i),pow_add]
  ring
end Lech.RootInvariants

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootChartUlrich
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace Lech.RootChartAtlas
open Polynomial ProductSourceCover UniversalSplitting
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
variable [Module.FaithfullyFlat (A R n k) B]

local instance instAlgebraAGridAmbient_r855d54_1 : Algebra (A R n k) (GridAmbient R n) := gridTargetAlgebra R n k
local instance instModuleAGridAmbient_r855d54_1 : Module (A R n k) (GridAmbient R n) := Algebra.toModule
local instance instAlgebraSubtypeSMemSubalgebraRingDGridAmbient_r855d54_1 : Algebra (D R n k t v hv d) (GridAmbient R n) := gridRootAlgebra R n k t v hv d
local instance instModuleSubtypeSMemSubalgebraRingDSubmoduleAlgebraFOverAlgebra_r855d54_1 (m : Fin n → ℤ) : Module (D R n k t v hv d)
    (RootInvariants.overAlgebra (f R n k) n (hn R n k) t v hv d m) := Submodule.module _
lemma globalCoefficientA_homogeneous (m e : Fin n → ℕ) (he : ∀ i,e i ≤ m i) :
    globalCoefficientA R n k t v hv d (fun i => (m i:ℤ))
      (RootInvariants.homogeneousSection (f R n k) n (hn R n k) t v hv d m e he)=
      ∏ i,embed R n (ProductLaurent.variableUnit R n i : ProductLaurent.Ring R n)^(e i) := by
  change (RootInvariants.commonBasis (f R n k) n (hn R n k) t v hv d
      (GridAmbient R n) (fun _ => false) (chartToGridD R n k t v hv d (fun _ => false))
      (fun i => (m i:ℤ))).symm
      (1 ⊗ₜ[D R n k t v hv d]
        ((RootInvariants.overAlgebraEquiv (f R n k) n (hn R n k) t v hv d _).symm
          (RootInvariants.homogeneousSection (f R n k) n (hn R n k) t v hv d m e he)))= _
  rw [RootInvariants.commonBasis_homogeneous]
  apply Finset.prod_congr rfl
  intro i hi
  have hx : chartToGridD R n k t v hv d (fun _ => false)
      (RootInvariants.chartCoordinate (f R n k) n (hn R n k) t v hv d (fun _ => false) i true)=
        embed R n (ProductLaurent.variableUnit R n i : ProductLaurent.Ring R n) := by
    change chartToGrid R n k t v hv d (fun _ => false)
      (coordinate R n k t v hv d (fun _ => false) i true)=_
    rw [chartToGrid_coordinate]
    simp only [↓reduceIte,chartScalar,AlgHom.comp_apply,ProductLaurent.chartMap_a,
      Bool.false_eq_true,Units.val_one,one_mul]
  have hy : chartToGridD R n k t v hv d (fun _ => false)
      (RootInvariants.chartCoordinate (f R n k) n (hn R n k) t v hv d (fun _ => false) i false)=1 := by
    change chartToGrid R n k t v hv d (fun _ => false)
      (coordinate R n k t v hv d (fun _ => false) i false)=_
    rw [chartToGrid_coordinate]
    simp only [Bool.false_eq_true,↓reduceIte,chartScalar,AlgHom.comp_apply,
      ProductLaurent.chartMap_b,Units.val_one,map_one]
  rw [hx,hy,one_pow,mul_one]

lemma globalCoefficientA_consecutive (e : PowerIndex n) :
    globalCoefficientA R n k t v hv d (fun i => (powerWeight n i:ℤ))
      (RootInvariants.consecutiveSection (f R n k) n (hn R n k) t v hv d e)=powerSection R n e := by
  have he : RootInvariants.consecutiveSection (f R n k) n (hn R n k) t v hv d e =
      RootInvariants.homogeneousSection (f R n k) n (hn R n k) t v hv d
        (powerWeight n) (powerExponent n e) (powerExponent_bound n e) := by
    apply Subtype.ext
    exact binaryPower_prod t n d.roots e
  rw [he,globalCoefficientA_homogeneous]
  rfl

include t v hv d in
lemma exists_consecutive_section_basis :
    ∃ b : Module.Basis (PowerIndex n) (A R n k)
      (sectionModule R n k (fun i => (powerWeight n i:ℤ))),
      ∀ e,(b e : GridAmbient R n)=powerSection R n e := by
  obtain ⟨b,hb⟩ := RootInvariants.exists_consecutive_basis (f R n k) n (hn R n k) t v hv d
  refine ⟨b.map (globalSectionEquiv R n k t v hv d _),?_⟩
  intro e
  rw [Module.Basis.map_apply,hb]
  exact globalCoefficientA_consecutive R n k t v hv d e
end Lech.RootChartAtlas

namespace Lech.ProductSourceCover
open UniversalSplitting
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
 

theorem exists_powerSection_basis :
    ∃ b : Module.Basis (PowerIndex n) (UniversalCoefficientChart.Ring R n k)
      (sectionModule R n k (fun i => (powerWeight n i:ℤ))),
      ∀ e,(b e : GridAmbient R n)=powerSection R n e := by
  let f := UniversalCoefficientChart.form R n k
  let : Module.FaithfullyFlat (UniversalCoefficientChart.Ring R n k) (PrimitiveRootModule.chart f) :=
    PrimitiveChart.faithfullyFlat_away f (UniversalCoefficientChart.form_primitive R n k)
  exact RootChartAtlas.exists_consecutive_section_basis R n k (PrimitiveRootModule.coordinate f)
    (PrimitiveRootModule.valueUnit f) (PrimitiveRootModule.eval_valueUnit f)
    (PrimitiveRootModule.splitting f n (UniversalCoefficientChart.form_degree R n k))
end Lech.ProductSourceCover

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootPermutation
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.ProductSourceCover
open AddMonoidAlgebra
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (σ : Equiv.Perm (Fin n))

lemma permuteGrid_embed (x : Ambient R n) :
    permuteGrid R n σ (embed R n x)=embed R n (ProductLaurent.permute R n σ x) :=
  IsLocalization.algEquivOfAlgEquiv_eq _ _

lemma permuteGrid_symm : (permuteGrid R n σ).symm=permuteGrid R n σ.symm := by
  apply AlgEquiv.coe_ringEquiv_injective
  apply RingEquiv.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (denominator R n Finset.univ))
  apply RingHom.ext
  intro x
  change (permuteGrid R n σ).symm (embed R n x)=permuteGrid R n σ.symm (embed R n x)
  apply (permuteGrid R n σ).injective
  rw [AlgEquiv.apply_symm_apply,permuteGrid_embed,permuteGrid_embed,←ProductLaurent.permute_symm,
    AlgEquiv.apply_symm_apply]

lemma permute_grid (m : Fin n → ℤ) (s : Finset (Fin (n+1)))
    (x : GridAmbient R n) (hx : x∈grid R n m s ∅) :
      permuteGrid R n σ x∈grid R n (permuteWeight n σ m) s ∅ := by
  obtain ⟨N,a,ha,he⟩ := hx
  refine ⟨N,ProductLaurent.permute R n σ a,permute_ringSections R n σ (levelTwist n m s.card N) a ha,?_⟩
  have h := congrArg (permuteGrid R n σ) he
  simpa only [map_mul,map_pow,permuteGrid_embed,permute_denominator] using h
end Lech.ProductSourceCover

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootProjectiveEuler
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.ReesRoot.projectiveAlgebra _root_.OAI.Lech.ReesRoot.projectiveTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace Lech.ProjectiveRoot
open ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

def coordinateMul (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) (i : Fin n) (b : Bool) :
    Sections R n s hs m →ₗ[Ring R n s] Sections R n s hs (Pi.single i 1+m) where
  toFun x := ⟨rootCoordinate R n i b*x.val,
    grid_mul_mem R n (Pi.single i 1) m s ∅ _ _ (rootCoordinate_mem R n s i b) x.property⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' a x := Subtype.ext (by
    change rootCoordinate R n i b*(scalarMap R n s a*x.val)=
      scalarMap R n s a*(rootCoordinate R n i b*x.val)
    ring)

section Intersection
variable (k : Fin (n+1)) (s : Finset (Fin (n+1))) (hs : s.Nonempty) [hks : Fact (k∈s)]

attribute [local instance] OAI.Lech.ProjectiveRoot.projectiveEulerInstance1
lemma chartBaseChange_tmul_val (m : Fin n → ℤ) (a : Ring R n s) (x : sectionModule R n k m) :
    (chartBaseChange R n k s hs m (a ⊗ₜ[UniversalCoefficientChart.Ring R n k] x):GridAmbient R n)=
      scalarMap R n s a*x.val := by
  have he : a ⊗ₜ[UniversalCoefficientChart.Ring R n k] x=
      a • ((1:Ring R n s) ⊗ₜ[UniversalCoefficientChart.Ring R n k] x) := by
    rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]
  rw [he,map_smul,chartBaseChange_one]
  rfl

lemma chartBaseChange_coordinateMul (m : Fin n → ℤ) (i : Fin n) (b : Bool)
    (a : Ring R n s) (x : sectionModule R n k m) :
    chartBaseChange R n k s hs (Pi.single i 1+m)
      (a ⊗ₜ[UniversalCoefficientChart.Ring R n k] ProductSourceCover.coordinateMul R n k m i b x)=
      coordinateMul R n s hs m i b (chartBaseChange R n k s hs m (a ⊗ₜ x)) := by
  apply Subtype.ext
  rw [chartBaseChange_tmul_val]
  change scalarMap R n s a*(rootCoordinate R n i b*x.val)=
    rootCoordinate R n i b*(chartBaseChange R n k s hs m (a ⊗ₜ[UniversalCoefficientChart.Ring R n k] x):GridAmbient R n)
  rw [chartBaseChange_tmul_val]
  ring

end Intersection



end Lech.ProjectiveRoot

end

end OAI
end


