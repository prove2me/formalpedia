-- Prove2me | Definitions.Def_OAIQ032L030
-- name    : OAIQ032L030
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T20:47:38.097464+00:00
-- url     : https://prove2.me/theorems/1b3db633-4a32-4ff7-a596-bd423c386a5f
-- title:
--   Definitions bundle OAIQ032L030 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 66 declarations of OpenAI's Lean: 15 definitions, 1 instance and 50 theorems. The definitions and types are `OAI.Lech.ProductSourceCover.coordinateMul`, `OAI.Lech.ProductSourceCover.eulerLeft`, `OAI.Lech.ProductSourceCover.eulerRight`, `OAI.Lech.ProductSourceCover.locTargetModule`, `OAI.Lech.ProductSourceCover.localizedTarget`, `OAI.Lech.ProductSourceCover.overlapModule`, `OAI.Lech.ProductSourceCover.permuteGrid`, `OAI.Lech.ProductSourceCover.powerSection`, `OAI.Lech.ProductSourceCover.sectionModule`, `OAI.Lech.ProductSourceCover.targetProductUnit`, `OAI.Lech.RootChartAtlas.globalSectionEquiv`, `OAI.Lech.RootChartAtlas.globalSectionMap`, `OAI.Lech.RootInvariants.coordinateMul`, `OAI.Lech.RootInvariants.eulerLeft`, `OAI.Lech.RootInvariants.eulerRight`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_GradedLineBasisHasBasis`, `Multiplicity_LechFactorizationMap`, `Multiplicity_LechHomogeneousEval`, `Multiplicity_LechSignedUnit`, `Multiplicity_RootChartAtlasGlobalCoefficient`, `Multiplicity_RootChartUlrich`, `Multiplicity_RootCoefficientEuler`, `Multiplicity_RootCoordinateMultiplication`, `Multiplicity_RootHomogeneousCoordinates`, `Multiplicity_RootInvariantsWeightZero`, `Multiplicity_RootLineEuler`, `Multiplicity_RootPermutation`.
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
-- module Solutions.OAIQ032_LECH.Multiplicity_LechHomogeneousEval
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootChartAtlas.gridRootAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
lemma localizedChart_injective (σ : Chart n) (k : Fin (n+1)) :
    Function.Injective (localizedChart R n σ k) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers ((ProductLinearChart.product R n σ).coeff k))
    (localizedChart R n σ k).toRingHom).mpr
  intro a b
  simp only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,localizedChart_algebraMap]
  constructor
  · intro h
    simpa only [localizedChart_algebraMap] using congrArg (localizedChart R n σ k) h
  · intro h
    exact congrArg (algebraMap (ProductLinearChart.Ring R n) (ProductLinearChart.chart R n σ k))
      (chartScalar_injective R n σ h)
end


open Polynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
instance gridTargetTower (k : Fin (n+1)) : IsScalarTower R (UniversalCoefficientChart.Ring R n k) (GridAmbient R n) :=
  IsScalarTower.of_algebraMap_eq' (gridTarget R n k).comp_algebraMap.symm

end


universe u
variable (R : Type u) [CommRing R] (n : ℕ)
lemma grid_one_mem (s : Finset (Fin (n+1))) (t : Finset (Chart n)) :
    (1:GridAmbient R n)∈grid R n 0 s t := by
  refine ⟨0,1,?_,by simp⟩
  rw [show levelTwist n 0 s.card 0=0 by ext i;simp [levelTwist]]
  exact one_mem R n t
lemma grid_zero_pow_mem (s : Finset (Fin (n+1))) (t : Finset (Chart n))
    (x : GridAmbient R n) (hx : x∈grid R n 0 s t) (N : ℕ) : x^N∈grid R n 0 s t := by
  induction N with
  | zero => simpa only [pow_zero] using grid_one_mem R n s t
  | succ N ih => simpa only [pow_succ,zero_add] using grid_mul_mem R n 0 0 s t _ _ ih hx

lemma targetProduct_map (k : Fin (n+1)) (s : Finset (Fin (n+1))) :
    gridTarget R n k (targetProduct R n k s)=
      (↑((targetUnit R n k)⁻¹):GridAmbient R n)^s.card*embed R n (denominator R n s) := by
  simp only [targetProduct,map_prod,gridTarget_coefficient,Finset.prod_mul_distrib,Finset.prod_const]
  change _ = _ * embed R n (∏ j∈s,targetCoeff R n j)
  rw [map_prod]
lemma targetProduct_relation (k : Fin (n+1)) (s : Finset (Fin (n+1))) :
    (targetUnit R n k:GridAmbient R n)^s.card*gridTarget R n k (targetProduct R n k s)=embed R n (denominator R n s) := by
  rw [targetProduct_map,←mul_assoc,←mul_pow,Units.mul_inv,one_pow,one_mul]
def targetProductUnit (k : Fin (n+1)) (s : Finset (Fin (n+1))) : (GridAmbient R n)ˣ :=
  (targetUnit R n k)⁻¹^s.card*(denominator_unit R n s).unit
lemma targetProductUnit_val (k : Fin (n+1)) (s : Finset (Fin (n+1))) :
    (targetProductUnit R n k s:GridAmbient R n)=gridTarget R n k (targetProduct R n k s) := by
  rw [targetProduct_map]
  simp only [targetProductUnit,Units.val_mul,Units.val_pow_eq_pow_val,IsUnit.unit_spec]
lemma targetProductUnit_inv_mem (k : Fin (n+1)) (s : Finset (Fin (n+1))) :
    (↑((targetProductUnit R n k s)⁻¹):GridAmbient R n)∈grid R n 0 s ∅ := by
  refine ⟨1,(targetCoeff R n k)^s.card,?_,?_⟩
  · have hp := pow_mem R n (fun _ => 1) ∅ (targetCoeff R n k) (coefficient_mem R n k) s.card
    have ht : s.card • (fun _ : Fin n => (1:ℤ))=levelTwist n 0 s.card 1 := by
      ext i
      simp [levelTwist]
    rw [←ht]
    exact hp
  · rw [pow_one,map_pow,←targetUnit_val]
    change (↑((denominator_unit R n s).unit):GridAmbient R n)*
      (↑(((targetUnit R n k)⁻¹^s.card*(denominator_unit R n s).unit)⁻¹):GridAmbient R n)=_
    rw [mul_inv_rev,Units.val_mul,←mul_assoc,Units.mul_inv,one_mul,inv_pow,inv_inv,Units.val_pow_eq_pow_val]
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
-- module Solutions.OAIQ032_LECH.Multiplicity_RootInvariantsWeightZero
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootChartAtlas.gridRootAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))


attribute [local instance] OAI.Lech.RootInvariants.weightZeroProductSectionAlgebra
lemma chartFunctions_span [Module.FaithfullyFlat A B] :
    Ideal.span (Set.range (chartFunction f n hn t v hv d))=⊤ := by
  classical
  let R := algebra f n hn t v hv d
  let I : Ideal R := Ideal.span (Set.range (chartFunction f n hn t v hv d))
  let J := I.map (algebraMap R d.S)
  let : Module.FaithfullyFlat R d.S := algebra_faithfullyFlat f n hn t v hv d
  have hp (σ : Fin n → Bool) : (∏ i,(selected f n hn t v hv d σ i:d.S))∈J := by
    have hq : (chartFunction f n hn t v hv d σ:d.S)∈J :=
      Ideal.mem_map_of_mem (algebraMap R d.S) (show chartFunction f n hn t v hv d σ∈I from
        Ideal.subset_span (Set.mem_range_self σ))
    have hm := J.mul_mem_left (algebraMap B d.S (v⁻¹:Bˣ)) hq
    simpa only [chartFunction_val,← mul_assoc,← map_mul,Units.inv_mul,map_one,one_mul] using hm
  have he : (∏ i : Fin n,∑ b : Bool,
      (if b then algebraMap B d.S t else 1)*(selected f n hn t v hv d (fun _ => b) i:d.S))=1 := by
    apply Finset.prod_eq_one
    intro i _
    simpa only [Fintype.sum_bool,selected,Bool.false_eq_true,↓reduceIte,one_mul,add_comm]
      using section_chart_generator f n hn t v hv d i
  rw [Fintype.prod_sum] at he
  have h1 : (1:d.S)∈J := by
    rw [← he]
    apply J.sum_mem
    intro σ _
    simp only [selected] at hp ⊢
    rw [Finset.prod_mul_distrib]
    exact J.mul_mem_left _ (hp σ)
  have hJ : J=⊤ := (Ideal.eq_top_iff_one J).mpr h1
  have hc := I.comap_map_eq_self_of_faithfullyFlat (B := d.S)
  change J.comap (algebraMap R d.S)=I at hc
  rw [hJ,Ideal.comap_top] at hc
  exact hc.symm

end Lech.RootInvariants

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechFactorizationMap
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootChartAtlas.gridRootAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
lemma localized_function_regular (σ τ : Fin n → Bool) :
    IsRegular (algebraMap (D R n k t v hv d) (L R n k t v hv d τ) (q R n k t v hv d σ)) := by
  have h : IsRegular (toH R n k t v hv d τ
      (algebraMap (D R n k t v hv d) (L R n k t v hv d τ) (q R n k t v hv d σ))) := by
    rw [toH_chartFunction]
    apply ((ProductLinearChart.denominator R n τ k)⁻¹).isUnit.isRegular.mul
    apply IsRegular.prod
    intro i _
    have h := PrincipalCoverRegular.regular_map
      (S := H R n k τ) (M := Submonoid.powers ((ProductLinearChart.product R n τ).coeff k))
      (coordinate_regular R n τ i (σ i))
    simpa only [apply_ite] using h
  constructor
  · intro x y hxy
    apply (equiv R n k t v hv d τ).injective
    change toH R n k t v hv d τ x = toH R n k t v hv d τ y
    exact h.left (by simpa only [map_mul] using congrArg (toH R n k t v hv d τ) hxy)
  · intro x y hxy
    apply (equiv R n k t v hv d τ).injective
    change toH R n k t v hv d τ x = toH R n k t v hv d τ y
    exact h.right (by simpa only [map_mul] using congrArg (toH R n k t v hv d τ) hxy)
 

theorem chartFunction_regular (σ : Fin n → Bool) : IsRegular (q R n k t v hv d σ) :=
  PrincipalCoverRegular.regular_of_cover (q R n k t v hv d)
    (RootInvariants.chartFunctions_span (f R n k) n (hn R n k) t v hv d) _
    (localized_function_regular R n k t v hv d σ)
end Lech.RootChartAtlas


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_GradedLineBasisHasBasis
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootChartAtlas.gridRootAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
variable [Module.FaithfullyFlat A B]
local instance coordinateWorkAlgebra_ra70f76_1 : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
variable (C : Type u) [CommRing C] [Algebra (algebra f n hn t v hv d) C]
omit [Module.FaithfullyFlat A B] in
lemma commonWeight_single (σ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C) (i : Fin n) :
    (commonWeight f n hn t v hv d C σ φ (Pi.single i (1:ℤ)):commonExtension f n hn t v hv d C)=
      (1:C) ⊗ₜ[algebra f n hn t v hv d] (selected f n hn t v hv d σ i:d.S) := by
  change commonCoefficients f n hn t v hv d C σ φ
    (chartWeight f n hn t v hv d σ (Pi.single i 1):chartExtension f n hn t v hv d σ)=_
  rw [chartWeight_single,chartSelectedUnit_val]
  exact (Algebra.TensorProduct.map_tmul φ (AlgHom.id _ _) _ _).trans (by rw [map_one];rfl)
local instance coordinateWorkTower_ra70f76_1 : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
lemma commonCoordinate_relation (σ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C) (i : Fin n) (b : Bool) :
    algebraMap C (commonExtension f n hn t v hv d C) (φ (chartCoordinate f n hn t v hv d σ i b))*
      (commonWeight f n hn t v hv d C σ φ (Pi.single i (1:ℤ)):commonExtension f n hn t v hv d C)=
        (1:C) ⊗ₜ[algebra f n hn t v hv d]
          ((if b then sectionX f n hn t v hv d i else sectionY f n hn t v hv d i):d.S) := by
  have h := congrArg (chartValue f n hn t v hv d σ (Pi.single i (1:ℤ)))
    (chart_section_relation f n hn t v hv d σ i b)
  rw [chartLineEquiv_apply,chartValue_tmul,chartValue_tmul] at h
  have hh := congrArg (commonCoefficients f n hn t v hv d C σ φ) h
  simp only [commonCoefficients,Algebra.TensorProduct.map_tmul,map_one,AlgHom.id_apply] at hh
  rw [commonWeight_single]
  change (φ (chartCoordinate f n hn t v hv d σ i b) ⊗ₜ[algebra f n hn t v hv d] (1:d.S))*
    ((1:C) ⊗ₜ[algebra f n hn t v hv d] (selected f n hn t v hv d σ i:d.S))=_
  rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
  simpa only [apply_ite] using hh
lemma chartTransition_single (σ τ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C)
    (ψ : chartRing f n hn t v hv d τ →ₐ[algebra f n hn t v hv d] C) (i : Fin n) :
    (chartTransition f n hn t v hv d C σ τ φ ψ (Pi.single i (1:ℤ)):C)=
      ψ (chartCoordinate f n hn t v hv d τ i (σ i)) := by
  let := algebra_faithfullyFlat f n hn t v hv d
  have hinj : Function.Injective (algebraMap C (commonExtension f n hn t v hv d C)) :=
    FaithfulSMul.algebraMap_injective C (commonExtension f n hn t v hv d C)
  apply hinj
  apply (commonWeight f n hn t v hv d C τ ψ (Pi.single i (1:ℤ))).mul_left_inj.mp
  rw [chartTransition_value,commonCoordinate_relation,commonWeight_single]
  cases hs : σ i <;> simp only [selected,hs,Bool.false_eq_true,↓reduceIte]
end Lech.RootInvariants
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechSignedUnit
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
variable [Module.FaithfullyFlat A B]
local instance signedWorkAlgebra_ra70f76_1 : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
variable (C : Type u) [CommRing C] [Algebra (algebra f n hn t v hv d) C]
lemma chartTransition_unit_value (σ τ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C)
    (ψ : chartRing f n hn t v hv d τ →ₐ[algebra f n hn t v hv d] C) (ms : Fin n → ℤ) :
    Units.map (algebraMap C (commonExtension f n hn t v hv d C)).toMonoidHom
      (chartTransition f n hn t v hv d C σ τ φ ψ ms)=
        commonWeight f n hn t v hv d C σ φ ms*(commonWeight f n hn t v hv d C τ ψ ms)⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq).mpr
  apply Units.ext
  exact chartTransition_value f n hn t v hv d C σ τ φ ψ ms
omit [Module.FaithfullyFlat A B] in
lemma commonWeight_product (σ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C) (ms : Fin n → ℤ) :
    commonWeight f n hn t v hv d C σ φ ms=
      ∏ i : Fin n,commonWeight f n hn t v hv d C σ φ (Pi.single i (1:ℤ))^ms i := by
  let : CommRing (chartExtension f n hn t v hv d σ) := Algebra.TensorProduct.instCommRing
  simp only [commonWeight]
  simp only [chartWeight_single]
  rw [chartWeight,map_prod]
  simp only [map_zpow]
 

lemma chartTransition_product (σ τ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C)
    (ψ : chartRing f n hn t v hv d τ →ₐ[algebra f n hn t v hv d] C) (ms : Fin n → ℤ) :
    chartTransition f n hn t v hv d C σ τ φ ψ ms=
      ∏ i : Fin n,chartTransition f n hn t v hv d C σ τ φ ψ (Pi.single i (1:ℤ))^ms i := by
  let := algebra_faithfullyFlat f n hn t v hv d
  apply Units.map_injective (FaithfulSMul.algebraMap_injective C (commonExtension f n hn t v hv d C))
  simp only [map_prod,map_zpow,chartTransition_unit_value]
  rw [commonWeight_product f n hn t v hv d C σ φ ms,
    commonWeight_product f n hn t v hv d C τ ψ ms]
  exact signedUnitProduct _ _ _


lemma coordinateTransition_val (σ τ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C)
    (ψ : chartRing f n hn t v hv d τ →ₐ[algebra f n hn t v hv d] C) (i : Fin n) :
    (coordinateTransition f n hn t v hv d C σ τ φ ψ i:C)=
      ψ (chartCoordinate f n hn t v hv d τ i (σ i)) :=
  chartTransition_single f n hn t v hv d C σ τ φ ψ i
end Lech.RootInvariants


namespace Lech.RootChartAtlas
open Polynomial ProductSourceCover
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
variable [Module.FaithfullyFlat (A R n k) B]
lemma chartToGrid_injective (σ : Chart n) : Function.Injective (chartToGrid R n k t v hv d σ) :=
  (localizedChart_injective R n σ k).comp (equiv R n k t v hv d σ).injective
lemma gridRootAlgebra_injective : Function.Injective (algebraMap (D R n k t v hv d) (GridAmbient R n)) := by
  have h : Function.Injective (algebraMap (D R n k t v hv d) (L R n k t v hv d (fun _ => false))) :=
    IsLocalization.injective (L R n k t v hv d (fun _ => false))
      (Submonoid.powers_le.mpr ((chartFunction_regular R n k t v hv d (fun _ => false)).mem_nonZeroDivisors))
  exact (chartToGrid_injective R n k t v hv d (fun _ => false)).comp h

lemma gridCoordinateTransition (σ : Chart n) (i : Fin n) :
    (RootInvariants.coordinateTransition (f R n k) n (hn R n k) t v hv d (GridAmbient R n)
      σ (fun _ => false) (chartToGridD R n k t v hv d σ) (chartToGridD R n k t v hv d (fun _ => false)) i:GridAmbient R n)=
      embed R n (if σ i then (ProductLaurent.variableUnit R n i:Ambient R n) else 1) := by
  rw [RootInvariants.coordinateTransition_val]
  change chartToGrid R n k t v hv d (fun _ => false) (coordinate R n k t v hv d (fun _ => false) i (σ i))=_
  rw [chartToGrid_coordinate]
  cases σ i <;> simp only [Bool.false_eq_true,↓reduceIte,chartScalar,AlgHom.comp_apply,
    ProductLaurent.chartMap_a,ProductLaurent.chartMap_b,Units.val_one,one_mul,map_one]
end Lech.RootChartAtlas


namespace Lech.RootInvariants
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
variable [Module.FaithfullyFlat A B]
local instance basisMapWorkAlgebra_ra70f76_1 : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
variable (C : Type u) [CommRing C] [Algebra (algebra f n hn t v hv d) C]
lemma commonBasis_from (σ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C) (ms : Fin n → ℤ)
    (l : chartRing f n hn t v hv d σ) :
    commonBasis f n hn t v hv d C σ φ ms (φ l)=
      commonInclusion f n hn t v hv d C σ φ ms (chartBasis f n hn t v hv d σ ms l) := by
  let : Algebra (chartRing f n hn t v hv d σ) C := φ.toRingHom.toAlgebra
  let : IsScalarTower (algebra f n hn t v hv d) (chartRing f n hn t v hv d σ) C :=
    IsScalarTower.of_algebraMap_eq (R := algebra f n hn t v hv d)
      (S := chartRing f n hn t v hv d σ) (A := C) fun a => (φ.commutes a).symm
  exact LineBasisExtension.extend_coefficient C (chartBasis f n hn t v hv d σ ms) l
lemma commonInclusion_coordinate (σ τ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C)
    (ψ : chartRing f n hn t v hv d τ →ₐ[algebra f n hn t v hv d] C) (ms : Fin n → ℤ)
    (z : chartModule f n hn t v hv d σ ms) :
    (commonBasis f n hn t v hv d C τ ψ ms).symm (commonInclusion f n hn t v hv d C σ φ ms z)=
      φ ((chartBasis f n hn t v hv d σ ms).symm z)*
        (chartTransition f n hn t v hv d C σ τ φ ψ ms:C) := by
  apply (commonBasis f n hn t v hv d C τ ψ ms).injective
  rw [LinearEquiv.apply_symm_apply]
  change _=commonBasis f n hn t v hv d C τ ψ ms
    (_*(LineBasisExtension.transition (commonBasis f n hn t v hv d C τ ψ ms)
      (commonBasis f n hn t v hv d C σ φ ms):C))
  rw [LineBasisExtension.transition_apply,commonBasis_from,LinearEquiv.apply_symm_apply]
end Lech.RootInvariants


namespace Lech.RootChartAtlas
open Polynomial ProductSourceCover
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
variable [Module.FaithfullyFlat (A R n k) B]
attribute [local instance] OAI.Lech.RootChartAtlas.gridLineRoot
lemma gridTransition (σ : Chart n) (m : Fin n → ℤ) :
    RootInvariants.chartTransition (f R n k) n (hn R n k) t v hv d (GridAmbient R n)
      σ (fun _ => false) (chartToGridD R n k t v hv d σ) (chartToGridD R n k t v hv d (fun _ => false)) m=
      Units.map (embed R n).toMonoidHom (ProductLaurent.monomialUnit R n (twistExponent n m σ)) := by
  rw [RootInvariants.chartTransition_product,←ProductLaurent.signedProduct,map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_zpow]
  congr 1
  apply Units.ext
  change (RootInvariants.coordinateTransition (f R n k) n (hn R n k) t v hv d (GridAmbient R n)
    σ (fun _ => false) (chartToGridD R n k t v hv d σ) (chartToGridD R n k t v hv d (fun _ => false)) i:GridAmbient R n)=_
  rw [gridCoordinateTransition]
  cases σ i <;> rfl

local instance gridLineModule_ra70f76_1 (m : Fin n → ℤ) : Module (D R n k t v hv d) (RootInvariants.overAlgebra (f R n k) n (hn R n k) t v hv d m) :=
  Submodule.module _
lemma gridCoefficient_apply (σ : Chart n) (m : Fin n → ℤ)
    (z : RootInvariants.chartModule (f R n k) n (hn R n k) t v hv d σ m) :
    gridCoefficient R n k t v hv d σ m z=
      localizedLine R n m σ k (toH R n k t v hv d σ ((RootInvariants.chartBasis (f R n k) n (hn R n k) t v hv d σ m).symm z)) := by
  change (RootInvariants.commonBasis (f R n k) n (hn R n k) t v hv d (GridAmbient R n) (fun _ => false) (chartToGridD R n k t v hv d (fun _ => false)) m).symm
    (RootInvariants.commonInclusion (f R n k) n (hn R n k) t v hv d (GridAmbient R n) σ (chartToGridD R n k t v hv d σ) m z)=_
  rw [RootInvariants.commonInclusion_coordinate,gridTransition,localizedLine_apply]
  change chartToGrid R n k t v hv d σ _ * embed R n (ProductLaurent.monomialUnit R n (twistExponent n m σ):Ambient R n)=_
  rw [mul_comm]
  rfl
 

theorem gridCoefficient_range (σ : Chart n) (m : Fin n → ℤ) (x : GridAmbient R n) :
    (∃ z,gridCoefficient R n k t v hv d σ m z=x) ↔ x∈grid R n m {k} {σ} := by
  rw [←localizedLine_range]
  constructor
  · rintro ⟨z,rfl⟩
    rw [gridCoefficient_apply]
    exact ⟨_,rfl⟩
  · rintro ⟨h,rfl⟩
    obtain ⟨a,ha⟩ := (equiv R n k t v hv d σ).surjective h
    refine ⟨RootInvariants.chartBasis (f R n k) n (hn R n k) t v hv d σ m a,?_⟩
    rw [gridCoefficient_apply,LinearEquiv.symm_apply_apply]
    exact congrArg (localizedLine R n m σ k) ha
end Lech.RootChartAtlas


namespace Lech.RootInvariants
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))

local instance propertiesWorkAlgebra_ra70f76_1 : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
lemma line_flat [Module.FaithfullyFlat A B] (ms : Fin n → ℤ) :
    Module.Flat (algebra f n hn t v hv d) (overAlgebra f n hn t v hv d ms) := by
  let := algebra_faithfullyFlat f n hn t v hv d
  let : Module.Flat d.S (d.S ⊗[algebra f n hn t v hv d] overAlgebra f n hn t v hv d ms) :=
    Module.Flat.of_linearEquiv (lineTensorEquiv f n hn t v hv d ms)
  exact Module.Flat.of_flat_tensorProduct _ _ d.S

end Lech.RootInvariants


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootChartAtlasGlobalCoefficient
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
variable [Module.FaithfullyFlat (A R n k) B]
attribute [local instance] OAI.Lech.RootChartAtlas.gridGlobalRoot
attribute [local instance] OAI.Lech.RootChartAtlas.gridGlobalModule
lemma globalCoefficient_local (m : Fin n → ℤ) (x : GridAmbient R n) :
    (∃ z,globalCoefficient R n k t v hv d m z=x) ↔ ∀ σ,x∈grid R n m {k} {σ} := by
  constructor
  · rintro ⟨z,rfl⟩ σ
    exact (gridCoefficient_range R n k t v hv d σ m _).mp ⟨_,gridCoefficient_from R n k t v hv d σ m z⟩
  · intro hx
    have hloc (σ : Chart n) : ∃ z,LocalizationImageCover.localMap (q R n k t v hv d) σ
        (chartToGridD R n k t v hv d σ) z=gridBasis R n k t v hv d (fun _ => false) m x := by
      obtain ⟨z,hz⟩ := (gridCoefficient_range R n k t v hv d σ m x).mpr (hx σ)
      refine ⟨z,?_⟩
      apply (gridBasis R n k t v hv d (fun _ => false) m).symm.injective
      rw [LinearEquiv.symm_apply_apply]
      exact hz
    obtain ⟨z,hz⟩ := (LocalizationImageCover.globalImage_iff (q R n k t v hv d)
      (RootInvariants.chartFunctions_span (f R n k) n (hn R n k) t v hv d)
      (chartToGridD R n k t v hv d) (gridBasis R n k t v hv d (fun _ => false) m x)).mpr hloc
    refine ⟨z,?_⟩
    change (gridBasis R n k t v hv d (fun _ => false) m).symm (1 ⊗ₜ[D R n k t v hv d] z)=x
    rw [hz,LinearEquiv.symm_apply_apply]
 

theorem globalCoefficient_range (m : Fin n → ℤ) (x : GridAmbient R n) :
    (∃ z,globalCoefficient R n k t v hv d m z=x) ↔ x∈grid R n m {k} ∅ := by
  rw [globalCoefficient_local]
  constructor
  · intro hx
    let : LinearOrder (Chart n) := LinearOrder.lift' (Fintype.equivFin (Chart n)) (Fintype.equivFin (Chart n)).injective
    exact AlternatingCech.empty_mem_of_singletons R (GridAmbient R n) (grid R n m {k})
      (grid_source_mono R n m {k}) (grid_source_acyclic R n m {k} (Finset.singleton_nonempty _) 1) x hx
  · intro hx σ
    exact grid_source_mono R n m {k} (Finset.empty_subset {σ}) hx
lemma globalCoefficient_injective (m : Fin n → ℤ) :
    Function.Injective (globalCoefficient R n k t v hv d m) := by
  let := RootInvariants.line_flat (f R n k) n (hn R n k) t v hv d m
  exact (gridBasis R n k t v hv d (fun _ => false) m).symm.injective.comp
    (LocalizationImageCover.global_injective (gridRootAlgebra_injective R n k t v hv d))
end Lech.RootChartAtlas


namespace Lech.RootChartAtlas
open Polynomial ProductSourceCover
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
variable [Module.FaithfullyFlat (A R n k) B]
attribute [local instance] OAI.Lech.RootChartAtlas.moduleTargetModule
lemma globalCoefficientA_range (m : Fin n → ℤ) (x : GridAmbient R n) :
    (∃ z,globalCoefficientA R n k t v hv d m z=x) ↔ x∈grid R n m {k} ∅ :=
  globalCoefficient_range R n k t v hv d m x
lemma globalCoefficientA_injective (m : Fin n → ℤ) :
    Function.Injective (globalCoefficientA R n k t v hv d m) :=
  globalCoefficient_injective R n k t v hv d m
attribute [local instance] OAI.Lech.RootChartAtlas.moduleWork
attribute [local instance] OAI.Lech.RootChartAtlas.moduleTarget
include t v hv d in
lemma grid_smul_mem (m : Fin n → ℤ) (a : A R n k) (x : GridAmbient R n)
    (hx : x∈grid R n m {k} ∅) : a • x∈grid R n m {k} ∅ := by
  obtain ⟨z,rfl⟩ := (globalCoefficientA_range R n k t v hv d m x).mpr hx
  exact (globalCoefficientA_range R n k t v hv d m _).mp ⟨a • z, map_smul _ _ _⟩
end Lech.RootChartAtlas


namespace Lech.ProductSourceCover
open Polynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))


attribute [local instance] OAI.Lech.ProductSourceCover.sectionModuleBase
def sectionModule (m : Fin n → ℤ) : Submodule (UniversalCoefficientChart.Ring R n k) (GridAmbient R n) where
  carrier := grid R n m {k} ∅
  zero_mem' := (grid R n m {k} ∅).zero_mem
  add_mem' := (grid R n m {k} ∅).add_mem
  smul_mem' a x hx := by
    let f := UniversalCoefficientChart.form R n k
    let : Module.FaithfullyFlat (UniversalCoefficientChart.Ring R n k) (PrimitiveRootModule.chart f) :=
      PrimitiveChart.faithfullyFlat_away f (UniversalCoefficientChart.form_primitive R n k)
    exact RootChartAtlas.grid_smul_mem R n k (PrimitiveRootModule.coordinate f)
      (PrimitiveRootModule.valueUnit f) (PrimitiveRootModule.eval_valueUnit f)
      (PrimitiveRootModule.splitting f n (UniversalCoefficientChart.form_degree R n k)) m a x hx
end Lech.ProductSourceCover


namespace Lech.RootChartAtlas
open Polynomial ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
variable [Module.FaithfullyFlat (A R n k) B]
local instance projTarget_ra70f76_1 : Algebra (A R n k) (GridAmbient R n) := gridTargetAlgebra R n k
local instance projTargetModule_ra70f76_1 : Module (A R n k) (GridAmbient R n) := Algebra.toModule
def globalSectionMap (m : Fin n → ℤ) :
    RootInvariants.module (f R n k) n (hn R n k) t v hv d m →ₗ[A R n k] sectionModule R n k m :=
  (globalCoefficientA R n k t v hv d m).codRestrict _
    (fun z => (globalCoefficientA_range R n k t v hv d m _).mp ⟨z,rfl⟩)
 

def globalSectionEquiv (m : Fin n → ℤ) :
    RootInvariants.module (f R n k) n (hn R n k) t v hv d m ≃ₗ[A R n k] sectionModule R n k m :=
  LinearEquiv.ofBijective (globalSectionMap R n k t v hv d m) ⟨by
    intro x y h
    exact globalCoefficientA_injective R n k t v hv d m (congrArg Subtype.val h), by
    intro x
    obtain ⟨z,hz⟩ := (globalCoefficientA_range R n k t v hv d m x).mpr x.property
    exact ⟨z,Subtype.ext hz⟩⟩
end Lech.RootChartAtlas


namespace Lech.ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
attribute [local instance] OAI.Lech.ProductSourceCover.locTarget
local instance locTargetModule : Module (UniversalCoefficientChart.Ring R n k) (GridAmbient R n) := Algebra.toModule
lemma grid_clear_target (m : Fin n → ℤ) (s : Finset (Fin (n+1)))
    (x : GridAmbient R n) (hx : x∈grid R n m s ∅) :
    ∃ N : ℕ,(targetProduct R n k s)^N • x∈grid R n m {k} ∅ := by
  obtain ⟨N,h,hh,he⟩ := hx
  refine ⟨N,s.card*N,h,?_,?_⟩
  · have ht : levelTwist n m (Finset.card {k}) (s.card*N)=levelTwist n m s.card N := by
      ext i
      simp only [levelTwist,Finset.card_singleton,Nat.cast_mul,Nat.cast_one,mul_one]
      ring
    rw [ht]
    exact hh
  · change embed R n (denominator R n {k})^(s.card*N)*
      (gridTarget R n k ((targetProduct R n k s)^N)*x)=embed R n h
    rw [map_pow,show embed R n (denominator R n {k})=(targetUnit R n k:GridAmbient R n) by
      rw [targetUnit_val];simp only [denominator,AwayCover.denominator,Finset.prod_singleton]]
    calc
      _ = ((targetUnit R n k:GridAmbient R n)^s.card*gridTarget R n k (targetProduct R n k s))^N*x := by
        rw [mul_pow,pow_mul,mul_assoc]
      _ = _ := by rw [targetProduct_relation,he]
 

theorem grid_localization_iff (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (hk : k∈s)
    (x : GridAmbient R n) : x∈grid R n m s ∅ ↔
      ∃ N : ℕ,(targetProduct R n k s)^N • x∈sectionModule R n k m := by
  constructor
  · exact grid_clear_target R n k m s x
  · rintro ⟨N,hN⟩
    have hloc : (targetProduct R n k s)^N • x∈grid R n m s ∅ :=
      grid_target_mono R n m ∅ (Finset.singleton_subset_iff.mpr hk) hN
    have hi := grid_zero_pow_mem R n s ∅ (↑((targetProductUnit R n k s)⁻¹):GridAmbient R n)
      (targetProductUnit_inv_mem R n k s) N
    have hm := grid_mul_mem R n 0 m s ∅ _ _ hi hloc
    have he : (↑((targetProductUnit R n k s)⁻¹):GridAmbient R n)^N*((targetProduct R n k s)^N • x)=x := by
      change (↑((targetProductUnit R n k s)⁻¹):GridAmbient R n)^N*
        (gridTarget R n k ((targetProduct R n k s)^N)*x)=x
      rw [map_pow,←targetProductUnit_val,←mul_assoc,←mul_pow,Units.inv_mul,one_pow,one_mul]
    simpa only [he,zero_add] using hm
 

def overlapModule (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (hk : k∈s) :
    Submodule (UniversalCoefficientChart.Ring R n k) (GridAmbient R n) where
  carrier := grid R n m s ∅
  zero_mem' := (grid R n m s ∅).zero_mem
  add_mem' := (grid R n m s ∅).add_mem
  smul_mem' a x hx := by
    obtain ⟨N,hN⟩ := (grid_localization_iff R n k m s hk x).mp hx
    apply (grid_localization_iff R n k m s hk (a • x)).mpr
    refine ⟨N,?_⟩
    have hh := (sectionModule R n k m).smul_mem a hN
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    change gridTarget R n k ((targetProduct R n k s)^N)*(gridTarget R n k a*x)=
      gridTarget R n k a*(gridTarget R n k ((targetProduct R n k s)^N)*x)
    ring

lemma inverse_mem_overlap (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (hk : k∈s)
    (x : overlapModule R n k m s hk) (N : ℕ) :
    (↑((targetProductUnit R n k s)⁻¹):GridAmbient R n)^N*(x:GridAmbient R n)∈overlapModule R n k m s hk := by
  have h := grid_mul_mem R n 0 m s ∅ _ _
    (grid_zero_pow_mem R n s ∅ _ (targetProductUnit_inv_mem R n k s) N) x.property
  change _∈grid R n m s ∅
  simpa only [zero_add] using h
end Lech.ProductSourceCover


namespace Lech.ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
local instance localizedTarget : Algebra (UniversalCoefficientChart.Ring R n k) (GridAmbient R n) := gridTargetAlgebra R n k
end Lech.ProductSourceCover


end
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
local instance homogeneousCoordinatesAlgebra_ra70f76_1 : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
variable (C : Type u) [CommRing C] [Algebra (algebra f n hn t v hv d) C]
  (σ : Fin n → Bool) (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C)

local instance homogeneousCoordinatesTower_ra70f76_1 : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
lemma commonBasis_value_apply (ms : Fin n → ℤ) (r : C) :
    commonValue f n hn t v hv d C ms (commonBasis f n hn t v hv d C σ φ ms r)=
      algebraMap C (commonExtension f n hn t v hv d C) r *
        (commonWeight f n hn t v hv d C σ φ ms : commonExtension f n hn t v hv d C) := by
  have hh : commonBasis f n hn t v hv d C σ φ ms r=
      r • commonBasis f n hn t v hv d C σ φ ms 1 := by
    simpa only [smul_eq_mul,mul_one] using (commonBasis f n hn t v hv d C σ φ ms).map_smul r 1
  rw [hh,map_smul,commonBasis_value]
  exact Algebra.smul_def (R := C) (A := commonExtension f n hn t v hv d C) _ _



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
namespace Lech.ProductSourceCover
open UniversalSplitting
universe u
variable (R : Type u) [CommRing R] (n : ℕ)

def powerSection (e : PowerIndex n) : GridAmbient R n :=
  ∏ i,embed R n (ProductLaurent.variableUnit R n i : ProductLaurent.Ring R n)^(powerExponent n e i)
end Lech.ProductSourceCover

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootLineEuler
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


attribute [local instance] OAI.Lech.RootInvariants.lineEulerInstance1
attribute [local instance] OAI.Lech.RootInvariants.lineEulerInstance2
def coordinateMul (m : Fin n → ℤ) (i : Fin n) (b : Bool) :
    module f n hn t v hv d m →ₗ[A] module f n hn t v hv d (Pi.single i 1+m) :=
  (overAlgebraEquiv f n hn t v hv d _).toLinearMap.comp
    (((mulLinear f n hn t v hv d (Pi.single i 1) m
      (if b then sectionX f n hn t v hv d i else sectionY f n hn t v hv d i)).restrictScalars A).comp
      (overAlgebraEquiv f n hn t v hv d m).symm.toLinearMap)

lemma coordinateMul_val (m : Fin n → ℤ) (i : Fin n) (b : Bool)
    (a : module f n hn t v hv d m) :
    (coordinateMul f n hn t v hv d m i b a : d.S)=
      (if b then -d.roots i else 1+algebraMap B d.S t*d.roots i)*(a:d.S) := by
  cases b <;> rfl

def eulerLeft (m : Fin n → ℤ) (i : Fin n) :
    module f n hn t v hv d m →ₗ[A]
      module f n hn t v hv d (Pi.single i 1+m) × module f n hn t v hv d (Pi.single i 1+m) :=
  (coordinateMul f n hn t v hv d m i false).prod (-coordinateMul f n hn t v hv d m i true)

def eulerRight (m : Fin n → ℤ) (i : Fin n) :
    module f n hn t v hv d (Pi.single i 1+m) × module f n hn t v hv d (Pi.single i 1+m) →ₗ[A]
      module f n hn t v hv d (Pi.single i 1+(Pi.single i 1+m)) :=
  (coordinateMul f n hn t v hv d (Pi.single i 1+m) i true).coprod
    (coordinateMul f n hn t v hv d (Pi.single i 1+m) i false)

variable [Module.FaithfullyFlat A B]

lemma eulerLeft_base_compat (m : Fin n → ℤ) (i : Fin n) :
    (eulerMiddleEquiv f n hn t v hv d (Pi.single i 1+m)).toLinearMap.comp
      ((eulerLeft f n hn t v hv d m i).baseChange B)=
      (SplitPair.left B (-d.roots i) (1+algebraMap B d.S t*d.roots i)).comp
        (tensorEquiv f n hn t v hv d m).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro b x
  change (b • (coordinateMul f n hn t v hv d m i false x:d.S),
    b • (-(coordinateMul f n hn t v hv d m i true x:d.S)))=_
  simp only [coordinateMul_val,Bool.false_eq_true,↓reduceIte,Algebra.smul_def,
    SplitPair.left,LinearMap.comp_apply]
  change (algebraMap B d.S b*((1+algebraMap B d.S t*d.roots i)*(x:d.S)),
    algebraMap B d.S b*(-(-d.roots i*(x:d.S))))=
    ((1+algebraMap B d.S t*d.roots i)*(b • (x:d.S)),-(-d.roots i*(b • (x:d.S))))
  apply Prod.ext <;> simp only [Algebra.smul_def] <;> ring

lemma eulerRight_base_compat (m : Fin n → ℤ) (i : Fin n) :
    (tensorEquiv f n hn t v hv d (Pi.single i 1+(Pi.single i 1+m))).toLinearMap.comp
      ((eulerRight f n hn t v hv d m i).baseChange B)=
      (SplitPair.right B (-d.roots i) (1+algebraMap B d.S t*d.roots i)).comp
        (eulerMiddleEquiv f n hn t v hv d (Pi.single i 1+m)).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro b x
  change b • ((coordinateMul f n hn t v hv d (Pi.single i 1+m) i true x.1:d.S)+
    (coordinateMul f n hn t v hv d (Pi.single i 1+m) i false x.2:d.S))=_
  simp only [coordinateMul_val,Bool.false_eq_true,↓reduceIte]
  change b • ((-d.roots i)*(x.1:d.S)+(1+algebraMap B d.S t*d.roots i)*(x.2:d.S))=
    (-d.roots i)*(b • (x.1:d.S))+(1+algebraMap B d.S t*d.roots i)*(b • (x.2:d.S))
  simp only [Algebra.smul_def]
  ring
lemma eulerLeft_injective (m : Fin n → ℤ) (i : Fin n) :
    Function.Injective (eulerLeft f n hn t v hv d m i) := by
  apply (Module.FaithfullyFlat.lTensor_injective_iff_injective A B _).mp
  have h : Function.Injective ((eulerMiddleEquiv f n hn t v hv d (Pi.single i 1+m)).toLinearMap.comp
      ((eulerLeft f n hn t v hv d m i).baseChange B)) := by
    rw [eulerLeft_base_compat]
    exact (SplitPair.left_injective B (-d.roots i) (1+algebraMap B d.S t*d.roots i)
      (algebraMap B d.S t) (by ring)).comp (tensorEquiv f n hn t v hv d m).injective
  intro a b hab
  exact h (congrArg (eulerMiddleEquiv f n hn t v hv d (Pi.single i 1+m)) hab)

lemma eulerRight_surjective (m : Fin n → ℤ) (i : Fin n) :
    Function.Surjective (eulerRight f n hn t v hv d m i) := by
  apply (Module.FaithfullyFlat.lTensor_surjective_iff_surjective A B _).mp
  intro y
  obtain ⟨x,hx⟩ := SplitPair.right_surjective B (-d.roots i) (1+algebraMap B d.S t*d.roots i)
    (algebraMap B d.S t) (by ring)
    (tensorEquiv f n hn t v hv d (Pi.single i 1+(Pi.single i 1+m)) y)
  refine ⟨(eulerMiddleEquiv f n hn t v hv d (Pi.single i 1+m)).symm x,?_⟩
  apply (tensorEquiv f n hn t v hv d (Pi.single i 1+(Pi.single i 1+m))).injective
  have he := DFunLike.congr_fun (eulerRight_base_compat f n hn t v hv d m i)
    ((eulerMiddleEquiv f n hn t v hv d (Pi.single i 1+m)).symm x)
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply] at he
  exact he.trans hx

 

lemma euler_exact (m : Fin n → ℤ) (i : Fin n) :
    Function.Exact (eulerLeft f n hn t v hv d m i) (eulerRight f n hn t v hv d m i) := by
  apply (Module.FaithfullyFlat.lTensor_exact_iff_exact A B _ _).mp
  change Function.Exact ((eulerLeft f n hn t v hv d m i).baseChange B)
    ((eulerRight f n hn t v hv d m i).baseChange B)
  exact (Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := tensorEquiv f n hn t v hv d m)
    (e₂ := eulerMiddleEquiv f n hn t v hv d (Pi.single i 1+m))
    (e₃ := tensorEquiv f n hn t v hv d (Pi.single i 1+(Pi.single i 1+m)))
    (eulerLeft_base_compat f n hn t v hv d m i).symm
    (eulerRight_base_compat f n hn t v hv d m i).symm).mp
      (SplitPair.exact B (-d.roots i) (1+algebraMap B d.S t*d.roots i) (algebraMap B d.S t) (by ring))
end Lech.RootInvariants

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootCoordinateMultiplication
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
private local instance coordinateInstance1_ra70f76_1 : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
variable (C : Type u) [CommRing C] [Algebra (algebra f n hn t v hv d) C]
  (σ : Fin n → Bool) (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C)

omit [Module.FaithfullyFlat A B] in
lemma commonWeight_add (m l : Fin n → ℤ) :
    commonWeight f n hn t v hv d C σ φ (m+l)=
      commonWeight f n hn t v hv d C σ φ m*commonWeight f n hn t v hv d C σ φ l := by
  simp only [commonWeight,chartWeight_add,map_mul]

private local instance coordinateInstance2_ra70f76_1 : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
lemma commonBasis_coordinateMul (m : Fin n → ℤ) (i : Fin n) (b : Bool)
    (x : module f n hn t v hv d m) :
    (commonBasis f n hn t v hv d C σ φ (Pi.single i 1+m)).symm
      (1 ⊗ₜ[algebra f n hn t v hv d] ((overAlgebraEquiv f n hn t v hv d _).symm
        (coordinateMul f n hn t v hv d m i b x)))=
      φ (chartCoordinate f n hn t v hv d σ i b)*
        (commonBasis f n hn t v hv d C σ φ m).symm
          (1 ⊗ₜ[algebra f n hn t v hv d] ((overAlgebraEquiv f n hn t v hv d m).symm x)) := by
  let := algebra_faithfullyFlat f n hn t v hv d
  let inc : d.S →ₐ[algebra f n hn t v hv d] commonExtension f n hn t v hv d C :=
    Algebra.TensorProduct.includeRight
  have hinj : Function.Injective (algebraMap C (commonExtension f n hn t v hv d C)) :=
    FaithfulSMul.algebraMap_injective C (commonExtension f n hn t v hv d C)
  have hx : inc (x:d.S)=
      algebraMap C (commonExtension f n hn t v hv d C)
        ((commonBasis f n hn t v hv d C σ φ m).symm
          (1 ⊗ₜ[algebra f n hn t v hv d] ((overAlgebraEquiv f n hn t v hv d m).symm x)))*
        (commonWeight f n hn t v hv d C σ φ m:commonExtension f n hn t v hv d C) := by
    rw [←commonBasis_value_apply,LinearEquiv.apply_symm_apply]
    rfl
  apply hinj
  apply (commonWeight f n hn t v hv d C σ φ (Pi.single i 1+m)).mul_left_inj.mp
  rw [←commonBasis_value_apply,LinearEquiv.apply_symm_apply]
  change inc (coordinateMul f n hn t v hv d m i b x:d.S)=_
  rw [coordinateMul_val,map_mul,hx]
  have hc := commonCoordinate_relation f n hn t v hv d C σ φ i b
  change algebraMap C (commonExtension f n hn t v hv d C) (φ (chartCoordinate f n hn t v hv d σ i b))*
    (commonWeight f n hn t v hv d C σ φ (Pi.single i 1):commonExtension f n hn t v hv d C)=
      inc (if b then -d.roots i else 1+algebraMap B d.S t*d.roots i) at hc
  rw [←hc,map_mul,commonWeight_add,Units.val_mul]
  ring
end Lech.RootInvariants

namespace Lech.RootChartAtlas
open Polynomial ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
variable [Module.FaithfullyFlat (A R n k) B]

private local instance coordinateInstance5_ra70f76_1 : Algebra (A R n k) (GridAmbient R n) := gridTargetAlgebra R n k
private local instance coordinateInstance6_ra70f76_1 : Module (A R n k) (GridAmbient R n) := Algebra.toModule
private local instance coordinateInstance7_ra70f76_1 : Algebra (D R n k t v hv d) (GridAmbient R n) := gridRootAlgebra R n k t v hv d
private local instance coordinateInstance9_ra70f76_1 (m : Fin n → ℤ) : Module (D R n k t v hv d)
    (RootInvariants.overAlgebra (f R n k) n (hn R n k) t v hv d m) := Submodule.module _
lemma globalCoefficientA_coordinateMul (m : Fin n → ℤ) (i : Fin n) (b : Bool)
    (x : RootInvariants.module (f R n k) n (hn R n k) t v hv d m) :
    globalCoefficientA R n k t v hv d (Pi.single i 1+m)
      (RootInvariants.coordinateMul (f R n k) n (hn R n k) t v hv d m i b x)=
      (if b then embed R n (ProductLaurent.variableUnit R n i:ProductLaurent.Ring R n) else 1)*
        globalCoefficientA R n k t v hv d m x := by
  change (RootInvariants.commonBasis (f R n k) n (hn R n k) t v hv d
      (GridAmbient R n) (fun _ => false) (chartToGridD R n k t v hv d (fun _ => false))
      (Pi.single i 1+m)).symm
      (1 ⊗ₜ[D R n k t v hv d]
        ((RootInvariants.overAlgebraEquiv (f R n k) n (hn R n k) t v hv d _).symm
          (RootInvariants.coordinateMul (f R n k) n (hn R n k) t v hv d m i b x)))= _
  rw [RootInvariants.commonBasis_coordinateMul]
  congr 1
  change chartToGrid R n k t v hv d (fun _ => false)
    (coordinate R n k t v hv d (fun _ => false) i b)=_
  rw [chartToGrid_coordinate]
  cases b <;> simp only [Bool.false_eq_true,↓reduceIte,chartScalar,AlgHom.comp_apply,
    ProductLaurent.chartMap_a,ProductLaurent.chartMap_b,Units.val_one,one_mul,map_one]
end Lech.RootChartAtlas

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootCoefficientEuler
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


def coordinateMul (k : Fin (n+1)) (m : Fin n → ℤ) (i : Fin n) (b : Bool) :
    sectionModule R n k m →ₗ[UniversalCoefficientChart.Ring R n k]
      sectionModule R n k (Pi.single i 1+m) where
  toFun x := ⟨rootCoordinate R n i b*x.val,
    grid_mul_mem R n (Pi.single i 1) m {k} ∅ _ _ (rootCoordinate_mem R n {k} i b) x.property⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' a x := Subtype.ext (by
    change rootCoordinate R n i b*(gridTarget R n k a*x.val)=
      gridTarget R n k a*(rootCoordinate R n i b*x.val)
    ring)

def eulerLeft (k : Fin (n+1)) (m : Fin n → ℤ) (i : Fin n) :
    sectionModule R n k m →ₗ[UniversalCoefficientChart.Ring R n k]
      sectionModule R n k (Pi.single i 1+m) × sectionModule R n k (Pi.single i 1+m) :=
  (coordinateMul R n k m i false).prod (-coordinateMul R n k m i true)
def eulerRight (k : Fin (n+1)) (m : Fin n → ℤ) (i : Fin n) :
    sectionModule R n k (Pi.single i 1+m) × sectionModule R n k (Pi.single i 1+m) →ₗ[UniversalCoefficientChart.Ring R n k]
      sectionModule R n k (Pi.single i 1+(Pi.single i 1+m)) :=
  (coordinateMul R n k (Pi.single i 1+m) i true).coprod
    (coordinateMul R n k (Pi.single i 1+m) i false)
end Lech.ProductSourceCover

namespace Lech.RootChartAtlas
open Polynomial ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
variable [Module.FaithfullyFlat (A R n k) B]

lemma globalSection_coordinateMul (m : Fin n → ℤ) (i : Fin n) (b : Bool)
    (x : RootInvariants.module (f R n k) n (hn R n k) t v hv d m) :
    globalSectionEquiv R n k t v hv d (Pi.single i 1+m)
      (RootInvariants.coordinateMul (f R n k) n (hn R n k) t v hv d m i b x)=
      coordinateMul R n k m i b (globalSectionEquiv R n k t v hv d m x) := by
  apply Subtype.ext
  exact globalCoefficientA_coordinateMul R n k t v hv d m i b x

include t v hv d in
lemma section_euler_shortExact (m : Fin n → ℤ) (i : Fin n) :
    Function.Injective (eulerLeft R n k m i) ∧ Function.Exact (eulerLeft R n k m i) (eulerRight R n k m i) ∧
      Function.Surjective (eulerRight R n k m i) := by
  apply ModuleSequence.transport
    (RootInvariants.eulerLeft (f R n k) n (hn R n k) t v hv d m i)
    (RootInvariants.eulerRight (f R n k) n (hn R n k) t v hv d m i)
    (eulerLeft R n k m i) (eulerRight R n k m i)
    (globalSectionEquiv R n k t v hv d m)
    ((globalSectionEquiv R n k t v hv d (Pi.single i 1+m)).prodCongr
      (globalSectionEquiv R n k t v hv d (Pi.single i 1+m)))
    (globalSectionEquiv R n k t v hv d (Pi.single i 1+(Pi.single i 1+m)))
  · apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact globalSection_coordinateMul R n k t v hv d m i false x
    · change globalSectionEquiv R n k t v hv d (Pi.single i 1+m)
        (-RootInvariants.coordinateMul (f R n k) n (hn R n k) t v hv d m i true x)=_
      rw [map_neg,globalSection_coordinateMul]
      rfl
  · apply LinearMap.ext
    intro x
    change globalSectionEquiv R n k t v hv d _
      (RootInvariants.coordinateMul (f R n k) n (hn R n k) t v hv d _ i true x.1+
        RootInvariants.coordinateMul (f R n k) n (hn R n k) t v hv d _ i false x.2)=_
    rw [map_add,globalSection_coordinateMul,globalSection_coordinateMul]
    rfl
  · exact RootInvariants.eulerLeft_injective (f R n k) n (hn R n k) t v hv d m i
  · exact RootInvariants.euler_exact (f R n k) n (hn R n k) t v hv d m i
  · exact RootInvariants.eulerRight_surjective (f R n k) n (hn R n k) t v hv d m i
end Lech.RootChartAtlas

namespace Lech.ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
theorem euler_shortExact (m : Fin n → ℤ) (i : Fin n) :
    Function.Injective (eulerLeft R n k m i) ∧ Function.Exact (eulerLeft R n k m i) (eulerRight R n k m i) ∧
      Function.Surjective (eulerRight R n k m i) := by
  let f := UniversalCoefficientChart.form R n k
  let : Module.FaithfullyFlat (UniversalCoefficientChart.Ring R n k) (PrimitiveRootModule.chart f) :=
    PrimitiveChart.faithfullyFlat_away f (UniversalCoefficientChart.form_primitive R n k)
  exact RootChartAtlas.section_euler_shortExact R n k (PrimitiveRootModule.coordinate f)
    (PrimitiveRootModule.valueUnit f) (PrimitiveRootModule.eval_valueUnit f)
    (PrimitiveRootModule.splitting f n (UniversalCoefficientChart.form_degree R n k)) m i
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

lemma permute_denominator (s : Finset (Fin (n+1))) :
    ProductLaurent.permute R n σ (denominator R n s)=denominator R n s := by
  simp only [denominator,AwayCover.denominator,map_prod,ProductLaurent.permute_coefficient]

lemma permute_powers :
    (Submonoid.powers (denominator R n Finset.univ)).map (ProductLaurent.permute R n σ)=
      Submonoid.powers (denominator R n Finset.univ) := by
  rw [Submonoid.map_powers,permute_denominator]

def permuteGrid : GridAmbient R n ≃ₐ[R] GridAmbient R n :=
  IsLocalization.algEquivOfAlgEquiv (GridAmbient R n) (GridAmbient R n)
    (ProductLaurent.permute R n σ) (permute_powers R n σ)

end Lech.ProductSourceCover

end

end OAI
end


