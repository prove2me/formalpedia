-- Prove2me | Definitions.Def_OAIQ3Vx009
-- name    : OAIQ3Vx009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T06:42:22.689874+00:00
-- url     : https://prove2.me/theorems/d2a3ae2b-8fd8-45d2-8716-b68fcb135eb1
-- title:
--   Definitions bundle OAIQ3Vx009 of the split of OpenAI, Strongly rational unitary vertex operator algebras and conformal nets
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinimalVertex.main`, carved from OpenAI's openai/math development (OpenAI, *Strongly rational unitary vertex operator algebras and conformal nets*, OpenAI Math Release, September 25, 2026, result family 280, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 99 declarations of OpenAI's Lean: 1 definition and 98 theorems. The definitions and types are `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.localStateSpace`.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory/VertexAlgebra, in whole or in part: `VertexAlgebra_CoefficientDifferentiated`, `VertexAlgebra_CoefficientSummableBound`, `VertexAlgebra_DiffeomorphismStressSmooth`, `VertexAlgebra_HighFieldGraph`, `VertexAlgebra_LocalImplementer`, `VertexAlgebra_LocalNormalMap`, `VertexAlgebra_Locality`, `VertexAlgebra_ObservableScalars`, `VertexAlgebra_PrimaryStressWeak`, `VertexAlgebra_RegularizerFactorAdd`, `VertexAlgebra_RotationConjugateCommutant`, `VertexAlgebra_SmoothConjugateInner`, `VertexAlgebra_SmoothConjugatePrimary`, `VertexAlgebra_SmoothEnergyPower`, `VertexAlgebra_StressCutoffNormalized`, `VertexAlgebra_StressCutoffNormalized2`, `VertexAlgebra_StressPropagatorDerivative`, `VertexAlgebra_StressSmoothness`, `VertexAlgebra_StrongContinuity`, `VertexAlgebra_SymmetricWeakCommute`.
--
--   **Imports.** It imports the published bundle `Def_VertexAlgebraNet`; the bundles `OAIQ3Vx006` and `OAIQ3Vx007` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ3Vx011`.
-- source:
--   OpenAI, Strongly rational unitary vertex operator algebras and conformal nets, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 280; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strongly-rational-unitary-vertex-operator-algebras-and-conformal-nets-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory/VertexAlgebra at commit adc7f12

import Mathlib
import Definitions.Def_VertexAlgebraNet
import Definitions.Def_OAIQ3Vx006
import Definitions.Def_OAIQ3Vx007

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_CoefficientDifferentiated
attribute [-instance] _root_.OAI.StronglyRationalVOA.SmoothCircleFamily.instCoeFunForallRealSmoothCircleFunction _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

universe u

noncomputable section
open scoped Topology
open Filter

namespace StronglyRationalVOA.CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (A : CFTTypeVOA V)

 

theorem hasSum_smeared_commutator_zero {a b : V} {d e : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {f g : SmoothCircleFunction} (hfg : Disjoint (tsupport f) (tsupport g))
    (r : ℤ) (x y : V) :
    HasSum (fun m : ℤ => f.coefficient m*g.coefficient (r-m)*
      inner ℂ x (A.physicalMode a d m (A.physicalMode b e (r-m) y)-
        A.physicalMode b e (r-m) (A.physicalMode a d m y))) 0 := by
  let c (j : ℕ) : ℂ := inner ℂ x
    (mode A.fields (mode A.fields a j b) (r+d+e-2-j) y)
  have Hj (j : ℕ) : HasSum (fun m : ℤ =>
      Ring.choose ((m : ℂ)+((d : ℂ)-1)) j * f.coefficient m*g.coefficient (r-m)*c j) 0 := by
    simpa only [zero_mul] using
      (SmoothCircleFunction.hasSum_choose_convolution_zero hfg ((d : ℂ)-1) j r).mul_right (c j)
  have H : HasSum (fun m : ℤ => ∑ j ∈ Finset.range (d+e),
      Ring.choose ((m : ℂ)+((d : ℂ)-1)) j * f.coefficient m*g.coefficient (r-m)*c j) 0 := by
    simpa only [Finset.sum_const_zero] using
      (hasSum_sum (s := Finset.range (d+e)) (fun j _ => Hj j))
  have he (m : ℤ) : f.coefficient m*g.coefficient (r-m)*
      inner ℂ x (A.physicalMode a d m (A.physicalMode b e (r-m) y)-
        A.physicalMode b e (r-m) (A.physicalMode a d m y)) =
      ∑ j ∈ Finset.range (d+e),
      Ring.choose ((m : ℂ)+((d : ℂ)-1)) j * f.coefficient m*g.coefficient (r-m)*c j := by
    rw [A.physicalMode_commutator_finite ha hb,inner_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [inner_smul_right,c]
    rw [show m+(r-m)+(d : ℤ)+e-2-j = r+d+e-2-j by omega]
    rw [show (m : ℂ)+d-1 = (m : ℂ)+((d : ℂ)-1) by ring]
    ring
  simpa only [he] using H

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)

 

theorem smearedMap_weak_commutation {a b : V} {d e : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hqa : A.IsQuasiPrimary a) (hqb : A.IsQuasiPrimary b)
    (hha : U.IsHermitian d a) (hhb : U.IsHermitian e b)
    (hea : A.PolynomialEnergyBound a) (heb : A.PolynomialEnergyBound b)
    {f g : SmoothCircleFunction} (hf : f.IsReal) (hg : g.IsReal)
    (hfg : Disjoint (tsupport f) (tsupport g)) (x y : V) :
    inner ℂ (A.smearedMap a d hea f.coefficient f.rapid_coefficients x)
      (A.smearedMap b e heb g.coefficient g.rapid_coefficients y) =
    inner ℂ (A.smearedMap b e heb g.coefficient g.rapid_coefficients x)
      (A.smearedMap a d hea f.coefficient f.rapid_coefficients y) := by
  have Hhom (D E : ℕ) (x y : V) (hx : x ∈ A.grade D) (hy : y ∈ A.grade E) :
      inner ℂ (A.smearedMap a d hea f.coefficient f.rapid_coefficients x)
        (A.smearedMap b e heb g.coefficient g.rapid_coefficients y) =
      inner ℂ (A.smearedMap b e heb g.coefficient g.rapid_coefficients x)
        (A.smearedMap a d hea f.coefficient f.rapid_coefficients y) := by
    let r : ℤ := (E : ℤ)-D
    have H1 := U.hasSum_smeared_inner_homogeneous ha hb hx hy hqa hha hea heb
      f.rapid_coefficients g.rapid_coefficients (SmoothCircleFunction.coefficient_real hf)
    have H2 := U.hasSum_smeared_inner_homogeneous hb ha hx hy hqb hhb heb hea
      g.rapid_coefficients f.rapid_coefficients (SmoothCircleFunction.coefficient_real hg)
    let R : ℤ ≃ ℤ :=
      { toFun := fun m => r-m
        invFun := fun m => r-m
        left_inv := fun m => by dsimp; omega
        right_inv := fun m => by dsimp; omega }
    have H2' := R.hasSum_iff.mpr H2
    have Hdiff := H1.sub H2'
    have Hz := A.hasSum_smeared_commutator_zero ha hb hfg r x y
    apply sub_eq_zero.mp
    apply Hdiff.unique
    convert Hz using 1
    all_goals try with_reducible_and_instances rfl
    ext m
    simp only [Function.comp_def,R,Equiv.coe_fn_mk]
    rw [show (E : ℤ)-D-(r-m) = m by dsimp [r]; omega]
    simp only [inner_sub_right]
    ring
  apply A.homogeneous_induction (P := fun x =>
      inner ℂ (A.smearedMap a d hea f.coefficient f.rapid_coefficients x)
        (A.smearedMap b e heb g.coefficient g.rapid_coefficients y) =
      inner ℂ (A.smearedMap b e heb g.coefficient g.rapid_coefficients x)
        (A.smearedMap a d hea f.coefficient f.rapid_coefficients y))
  · simp only [map_zero,inner_zero_left]
  · intro D x hx
    apply A.homogeneous_induction (P := fun y =>
        inner ℂ (A.smearedMap a d hea f.coefficient f.rapid_coefficients x)
          (A.smearedMap b e heb g.coefficient g.rapid_coefficients y) =
        inner ℂ (A.smearedMap b e heb g.coefficient g.rapid_coefficients x)
          (A.smearedMap a d hea f.coefficient f.rapid_coefficients y))
    · simp only [map_zero,inner_zero_right]
    · intro E y hy
      exact Hhom D E x y hx hy
    · intro y z hy hz
      simp only [map_add,inner_add_right,hy,hz]
  · intro x z hx hz
    simp only [map_add,inner_add_left,hx,hz]

end UnitaryStructure
end StronglyRationalVOA.CFTTypeVOA

open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_RegularizerFactorAdd
attribute [-instance] _root_.OAI.StronglyRationalVOA.SmoothCircleFamily.instCoeFunForallRealSmoothCircleFunction _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace

open scoped Topology
open UniformSpace

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma smoothSmear_weakCommutation (hc : A.toVertexAlgebra.C2Cofinite) {a b : V} {d e : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hqa : A.IsQuasiPrimary a) (hqb : A.IsQuasiPrimary b)
    (hha : U.IsHermitian d a) (hhb : U.IsHermitian e b)
    {f g : SmoothCircleFunction} (hf : f.IsReal) (hg : g.IsReal)
    (hfg : Disjoint (tsupport f) (tsupport g)) (x y : U.smoothEnergySpace) :
    inner ℂ (U.smoothSmear hc ha f.rapid_coefficients x : Completion V)
      (U.smoothSmear hc hb g.rapid_coefficients y : Completion V) =
    inner ℂ (U.smoothSmear hc hb g.rapid_coefficients x : Completion V)
      (U.smoothSmear hc ha f.rapid_coefficients y : Completion V) := by
  obtain ⟨C,hC,p,k,hM⟩ := (U.polynomialEnergyBounds hc a).physical A d
  obtain ⟨D,hD,q,l,hN⟩ := (U.polynomialEnergyBounds hc b).physical A e
  let M := A.smearedMap a d (U.polynomialEnergyBounds hc a) f.coefficient f.rapid_coefficients
  let N := A.smearedMap b e (U.polynomialEnergyBounds hc b) g.coefficient g.rapid_coefficients
  have hm (v : V) : ‖M v‖ ≤ ((∑' n : ℤ, ‖f.coefficient n‖*(1+|(n : ℝ)|)^p)*C)*‖(A.energyShift^(k+l)) v‖ :=
    (A.smearedMap_bound _ f.rapid_coefficients hM v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : k ≤ k+l) v)
        (mul_nonneg (tsum_nonneg fun n => by positivity) hC.le))
  have hn (v : V) : ‖N v‖ ≤ ((∑' n : ℤ, ‖g.coefficient n‖*(1+|(n : ℝ)|)^q)*D)*‖(A.energyShift^(k+l)) v‖ :=
    (A.smearedMap_bound _ g.rapid_coefficients hN v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : l ≤ k+l) v)
        (mul_nonneg (tsum_nonneg fun n => by positivity) hD.le))
  let xx : (U.energyPower (k+l)).domain := ⟨x,(iInf_le (fun r => (U.energyPower r).domain) (k+l)) x.property⟩
  let yy : (U.energyPower (k+l)).domain := ⟨y,(iInf_le (fun r => (U.energyPower r).domain) (k+l)) y.property⟩
  have hx : ((x : Completion V),U.energyPower (k+l) xx) ∈ (U.energyPower (k+l)).graph :=
    (U.energyPower (k+l)).mem_graph_iff.mpr ⟨xx,rfl,rfl⟩
  have hy : ((y : Completion V),U.energyPower (k+l) yy) ∈ (U.energyPower (k+l)).graph :=
    (U.energyPower (k+l)).mem_graph_iff.mpr ⟨yy,rfl,rfl⟩
  rw [U.smoothSmear_eq_extension hc ha f.rapid_coefficients hm x hx,
    U.smoothSmear_eq_extension hc hb g.rapid_coefficients hn y hy,
    U.smoothSmear_eq_extension hc hb g.rapid_coefficients hn x hx,
    U.smoothSmear_eq_extension hc ha f.rapid_coefficients hm y hy]
  exact U.sobolevExtension_weakCommutation (k+l) M N hm hn
    (U.smearedMap_weak_commutation ha hb hqa hqb hha hhb _ _ hf hg hfg) _ _
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_HighFieldGraph
attribute [-instance] _root_.OAI.StronglyRationalVOA.SmoothCircleFamily.instCoeFunForallRealSmoothCircleFunction _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
theorem highField_graph_invariant_firstOrderFlow (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e p : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hqa : A.IsQuasiPrimary a) (hqb : A.IsQuasiPrimary b)
    (hha : U.IsHermitian d a) (hhb : U.IsHermitian e b)
    {D : ℝ} (hD : 0 ≤ D)
    (hbnd : ∀ n v, ‖A.physicalMode b e n v‖ ≤ D*(1+|(n : ℝ)|)^p*‖A.energyShift v‖)
    {f g : SmoothCircleFunction} (hf : f.IsReal) (hg : g.IsReal)
    (hfg : Disjoint (tsupport f) (tsupport g)) (t : ℝ)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    let hs := U.smearedCore_essentialSelfAdjoint hb hqb hhb (U.polynomialEnergyBounds hc b)
      hbnd g.rapid_coefficients (SmoothCircleFunction.coefficient_real hg)
    (SymmetricOperator.flow (U.closedSmoothField hc b e g) hs t x,
      SymmetricOperator.flow (U.closedSmoothField hc b e g) hs t y) ∈
        (U.closedSmoothField hc a d f).graph := by
  classical
  dsimp only
  let M := A.smearedMap a d (U.polynomialEnergyBounds hc a) f.coefficient f.rapid_coefficients
  let N := A.smearedMap b e (U.polynomialEnergyBounds hc b) g.coefficient g.rapid_coefficients
  let T := (HilbertCore.operator N).closure
  let hs : IsSelfAdjoint T := U.smearedCore_essentialSelfAdjoint hb hqb hhb
    (U.polynomialEnergyBounds hc b) hbnd g.rapid_coefficients (SmoothCircleFunction.coefficient_real hg)
  obtain ⟨C,hC,q,k,hmb⟩ := (U.polynomialEnergyBounds hc a).physical A d
  let r := k+1
  have hm (v : V) : ‖M v‖ ≤ ((∑' n : ℤ, ‖f.coefficient n‖*(1+|(n : ℝ)|)^q)*C)*‖(A.energyShift^r) v‖ :=
    (A.smearedMap_bound _ f.rapid_coefficients hmb v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : k ≤ r) v)
        (mul_nonneg (tsum_nonneg fun n => by positivity) hC.le))
  have hn (v : V) : ‖N v‖ ≤ ((∑' n : ℤ, ‖g.coefficient n‖*(1+|(n : ℝ)|)^p)*D)*‖(A.energyShift^r) v‖ := by
    have hb' : ∀ n v, ‖A.physicalMode b e n v‖ ≤ D*(1+|(n : ℝ)|)^p*‖(A.energyShift^1) v‖ := by
      simpa only [pow_one] using hbnd
    exact (A.smearedMap_bound _ g.rapid_coefficients hb' v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : 1 ≤ r) v)
        (mul_nonneg (tsum_nonneg fun n => by positivity) hD))
  let K := U.smearedPowerCommutator hb (U.polynomialEnergyBounds hc b) g.rapid_coefficients r
  have hk := U.smearedPowerCommutator_bound hb (U.polynomialEnergyBounds hc b) hD hbnd g.rapid_coefficients r
  have hpair := U.smearedPowerCommutator_pairing hb hqb hhb (U.polynomialEnergyBounds hc b)
    g.rapid_coefficients (SmoothCircleFunction.coefficient_real hg) r
  have hcM := U.smearedCore_closable hc ha f.rapid_coefficients
  have hcN := U.smearedCore_closable hc hb g.rapid_coefficients
  choose B hB hBnd using fun s => SymmetricOperator.flow_regularizer_factor T hs
    (U.inverseSobolev r) (U.sobolevExtension r N) (U.sobolevExtension r K)
    (U.inverseSobolev_selfAdjoint r) (U.inverseSobolev_dense r)
    (U.sobolevExtension_inverse_graph r N hn hcN)
    (U.sobolevExtension_defect r N K hn hk hpair) s
  have hcore (z : U.smoothEnergySpace) :
      (SymmetricOperator.flow T hs t z,
        SymmetricOperator.flow T hs t (U.smoothSmear hc ha f.rapid_coefficients z : Completion V)) ∈
          (U.closedSmoothField hc a d f).graph := by
    exact SymmetricOperator.regularized_commutation_on_dense_core
      (U.closedSmoothField hc a d f) T hs U.smoothEnergySpace U.smoothEnergySpace_dense
      (U.smoothSmear hc ha f.rapid_coefficients) (U.smoothSmear hc hb g.rapid_coefficients)
      (U.smoothSmear_graph hc ha f.rapid_coefficients) (U.smoothSmear_graph hc hb g.rapid_coefficients)
      (U.smoothSmear_symmetric hc ha hqa hha f.rapid_coefficients (SmoothCircleFunction.coefficient_real hf))
      (U.smoothSmear_weakCommutation hc ha hb hqa hqb hha hhb hf hg hfg)
      (U.inverseSobolev r) (U.sobolevExtension r M)
      (U.inverseSobolev_selfAdjoint r) (U.inverseSobolev_dense r)
      (fun z => ⟨U.smoothEnergyPower r z,U.inverseSobolev_smoothEnergyPower r z⟩)
      (U.sobolevExtension_inverse_graph r M hm hcM) B hB (norm_nonneg _) hBnd
      (fun s z => U.firstOrderSmear_flow_smoothEnergySpace hb hqb hhb (U.polynomialEnergyBounds hc b)
        hD hbnd g.rapid_coefficients (SmoothCircleFunction.coefficient_real hg) s z.property) t z
  apply SymmetricOperator.graph_invariant_of_core (HilbertCore.operator M) hcM
    (SymmetricOperator.flow T hs t) ?_ hxy
  intro u v huv
  obtain ⟨w,hw,hMw⟩ := (HilbertCore.operator M).mem_graph_iff.mp huv
  obtain ⟨z,rfl⟩ := (HilbertCore.equiv V).surjective w
  have hh := hcore ⟨(z : Completion V),U.core_le_smoothEnergySpace (HilbertCore.equiv V z).property⟩
  rw [U.smoothSmear_coe] at hh
  dsimp only [Prod.fst,Prod.snd] at hw hMw
  rw [← hw,← hMw]
  simpa only [M, closedSmoothField, smoothSmearedField, HilbertCore.operator_apply, HilbertCore.equiv_coe] using hh
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

 

theorem highField_firstOrder_graph_entries_commute (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e p : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hqa : A.IsQuasiPrimary a) (hqb : A.IsQuasiPrimary b)
    (hha : U.IsHermitian d a) (hhb : U.IsHermitian e b)
    {D : ℝ} (hD : 0 ≤ D)
    (hbnd : ∀ n v, ‖A.physicalMode b e n v‖ ≤ D*(1+|(n : ℝ)|)^p*‖A.energyShift v‖)
    {f g : SmoothCircleFunction} (hf : f.IsReal) (hg : g.IsReal)
    (hfg : Disjoint (tsupport f) (tsupport g)) (i j k l : Bool) :
    ClosedGraphData.entry (U.closedSmoothField hc a d f) (U.closedSmoothField_isClosed hc ha f) i j *
        ClosedGraphData.entry (U.closedSmoothField hc b e g) (U.closedSmoothField_isClosed hc hb g) k l =
      ClosedGraphData.entry (U.closedSmoothField hc b e g) (U.closedSmoothField_isClosed hc hb g) k l *
        ClosedGraphData.entry (U.closedSmoothField hc a d f) (U.closedSmoothField_isClosed hc ha f) i j := by
  let hs := U.smearedCore_essentialSelfAdjoint hb hqb hhb (U.polynomialEnergyBounds hc b)
    hbnd g.rapid_coefficients (SmoothCircleFunction.coefficient_real hg)
  exact SymmetricOperator.graph_entries_commute_of_flow_invariant _ _
    (U.closedSmoothField_isClosed hc ha f) hs
    (fun t x y hxy => U.highField_graph_invariant_firstOrderFlow hc ha hb hqa hqb hha hhb
      hD hbnd hf hg hfg t hxy) i j k l

 

theorem highField_stress_graph_entries_commute (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hqa : A.IsQuasiPrimary a) (hha : U.IsHermitian d a)
    {f g : SmoothCircleFunction} (hf : f.IsReal) (hg : g.IsReal)
    (hfg : Disjoint (tsupport f) (tsupport g)) (i j k l : Bool) :
    ClosedGraphData.entry (U.closedSmoothField hc a d f) (U.closedSmoothField_isClosed hc ha f) i j *
        ClosedGraphData.entry (U.closedSmoothField hc A.conformalVector 2 g)
          (U.closedSmoothField_isClosed hc A.conformal_mem g) k l =
      ClosedGraphData.entry (U.closedSmoothField hc A.conformalVector 2 g)
          (U.closedSmoothField_isClosed hc A.conformal_mem g) k l *
        ClosedGraphData.entry (U.closedSmoothField hc a d f) (U.closedSmoothField_isClosed hc ha f) i j := by
  have hn : 0 ≤ 1+A.centralCharge.re := by linarith [U.centralCharge_nonneg]
  have hh : U.IsHermitian 2 A.conformalVector := by
    simp [IsHermitian,U.pct_conformal]
  apply U.highField_firstOrder_graph_entries_commute hc ha A.conformal_mem hqa
    A.conformal_quasiPrimary hha hh (p := 2) hn ?_ hf hg hfg i j k l
  intro n v
  simpa only [physicalMode,virasoroMode,Nat.cast_ofNat,show n+(2 : ℤ)-1=n+1 by omega] using U.virasoro_linear_energy n v
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open scoped ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction



lemma hasSum_power_commutator_zero (f : SmoothCircleFunction) (k : ℕ) (r : ℤ) :
    HasSum (fun m : ℤ => ((k : ℂ)*m-(r-m))*f.coefficient m*(f.power k).coefficient (r-m)) 0 := by
  have h1 := ((f.differentiated 1).coefficient_mul (f.power k) r).mul_left (k : ℂ)
  have h2 := f.coefficient_mul ((f.power k).differentiated 1) r
  have he : (k : ℂ)*((f.differentiated 1).mul (f.power k)).coefficient r =
      (f.mul ((f.power k).differentiated 1)).coefficient r := by
    change (k : ℂ)*fourierCoeffOn period_pos _ r = fourierCoeffOn period_pos _ r
    rw [← smul_eq_mul,← fourierCoeffOn.const_smul]
    congr 1
    ext t
    simp only [Pi.smul_apply,smul_eq_mul,mul_apply,differentiated_apply,iteratedDeriv_one]
    simpa only [mul_assoc] using f.derivative_power_balance k t
  have h := (h1.sub h2).mul_left (-Complex.I)
  rw [he,sub_self,mul_zero] at h
  apply h.congr_fun
  intro m
  simp only [coefficient_differentiated,pow_one]
  push_cast
  ring_nf
  norm_num [Complex.I_sq]
  ring
end StronglyRationalVOA.SmoothCircleFunction

namespace StronglyRationalVOA.CFTTypeVOA
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (A : CFTTypeVOA V)

lemma hasSum_primary_stress_commutator_zero {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hp : A.IsPrimary a) (hd : 1 ≤ d) (f : SmoothCircleFunction) (r : ℤ) (x y : V) :
    HasSum (fun m : ℤ => f.coefficient m*(f.power (d-1)).coefficient (r-m)*
      inner ℂ x (A.physicalMode A.conformalVector 2 m (A.physicalMode a d (r-m) y)-
        A.physicalMode a d (r-m) (A.physicalMode A.conformalVector 2 m y))) 0 := by
  have h := (f.hasSum_power_commutator_zero (d-1) r).mul_right
    (inner ℂ x (A.physicalMode a d r y))
  simp only [zero_mul] at h
  apply h.congr_fun
  intro m
  rw [show A.physicalMode A.conformalVector 2 m = A.virasoroMode m by
    unfold physicalMode virasoroMode; congr 1; omega]
  rw [A.virasoro_primary_physical_commutator ha hp,inner_smul_right]
  rw [show m+(r-m)=r by omega]
  rw [Nat.cast_sub hd,Nat.cast_one]
  push_cast
  ring
end StronglyRationalVOA.CFTTypeVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_PrimaryStressWeak
attribute [-instance] _root_.OAI.StronglyRationalVOA.SmoothCircleFamily.instCoeFunForallRealSmoothCircleFunction _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma primary_stress_weakCommutation (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a)
    (hh : U.IsHermitian d a) (hd : 1 ≤ d) {f : SmoothCircleFunction}
    (hf : f.IsReal) (x y : V) :
    inner ℂ (A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector)
      f.coefficient f.rapid_coefficients x)
      (A.smearedMap a d (U.polynomialEnergyBounds hc a)
        (f.power (d-1)).coefficient (f.power (d-1)).rapid_coefficients y) =
    inner ℂ (A.smearedMap a d (U.polynomialEnergyBounds hc a)
        (f.power (d-1)).coefficient (f.power (d-1)).rapid_coefficients x)
      (A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector)
        f.coefficient f.rapid_coefficients y) := by
  have hν : U.IsHermitian 2 A.conformalVector := by simp [IsHermitian,U.pct_conformal]
  exact U.smearedMap_weakCommutation_of_convolution A.conformal_mem ha
    A.conformal_quasiPrimary (hp 1 (by norm_num)) hν hh
    (U.polynomialEnergyBounds hc A.conformalVector) (U.polynomialEnergyBounds hc a)
    hf (SmoothCircleFunction.power_real hf (d-1))
    (fun r x y => A.hasSum_primary_stress_commutator_zero ha hp hd f r x y) x y
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma highField_graph_invariant_firstOrderFlow_of_weak (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e p : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hqa : A.IsQuasiPrimary a) (hqb : A.IsQuasiPrimary b)
    (hha : U.IsHermitian d a) (hhb : U.IsHermitian e b)
    {D : ℝ} (hD : 0 ≤ D)
    (hbnd : ∀ n v, ‖A.physicalMode b e n v‖ ≤ D*(1+|(n : ℝ)|)^p*‖A.energyShift v‖)
    {f g : SmoothCircleFunction} (hf : f.IsReal) (hg : g.IsReal)
    (hweak : ∀ x y : V,
      inner ℂ (A.smearedMap a d (U.polynomialEnergyBounds hc a) f.coefficient f.rapid_coefficients x)
        (A.smearedMap b e (U.polynomialEnergyBounds hc b) g.coefficient g.rapid_coefficients y) =
      inner ℂ (A.smearedMap b e (U.polynomialEnergyBounds hc b) g.coefficient g.rapid_coefficients x)
        (A.smearedMap a d (U.polynomialEnergyBounds hc a) f.coefficient f.rapid_coefficients y)) (t : ℝ)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    let hs := U.smearedCore_essentialSelfAdjoint hb hqb hhb (U.polynomialEnergyBounds hc b)
      hbnd g.rapid_coefficients (SmoothCircleFunction.coefficient_real hg)
    (SymmetricOperator.flow (U.closedSmoothField hc b e g) hs t x,
      SymmetricOperator.flow (U.closedSmoothField hc b e g) hs t y) ∈
        (U.closedSmoothField hc a d f).graph := by
  classical
  dsimp only
  let M := A.smearedMap a d (U.polynomialEnergyBounds hc a) f.coefficient f.rapid_coefficients
  let N := A.smearedMap b e (U.polynomialEnergyBounds hc b) g.coefficient g.rapid_coefficients
  let T := (HilbertCore.operator N).closure
  let hs : IsSelfAdjoint T := U.smearedCore_essentialSelfAdjoint hb hqb hhb
    (U.polynomialEnergyBounds hc b) hbnd g.rapid_coefficients (SmoothCircleFunction.coefficient_real hg)
  obtain ⟨C,hC,q,k,hmb⟩ := (U.polynomialEnergyBounds hc a).physical A d
  let r := k+1
  have hm (v : V) : ‖M v‖ ≤ ((∑' n : ℤ, ‖f.coefficient n‖*(1+|(n : ℝ)|)^q)*C)*‖(A.energyShift^r) v‖ :=
    (A.smearedMap_bound _ f.rapid_coefficients hmb v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : k ≤ r) v)
        (mul_nonneg (tsum_nonneg fun n => by positivity) hC.le))
  have hn (v : V) : ‖N v‖ ≤ ((∑' n : ℤ, ‖g.coefficient n‖*(1+|(n : ℝ)|)^p)*D)*‖(A.energyShift^r) v‖ := by
    have hb' : ∀ n v, ‖A.physicalMode b e n v‖ ≤ D*(1+|(n : ℝ)|)^p*‖(A.energyShift^1) v‖ := by
      simpa only [pow_one] using hbnd
    exact (A.smearedMap_bound _ g.rapid_coefficients hb' v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : 1 ≤ r) v)
        (mul_nonneg (tsum_nonneg fun n => by positivity) hD))
  let K := U.smearedPowerCommutator hb (U.polynomialEnergyBounds hc b) g.rapid_coefficients r
  have hk := U.smearedPowerCommutator_bound hb (U.polynomialEnergyBounds hc b) hD hbnd g.rapid_coefficients r
  have hpair := U.smearedPowerCommutator_pairing hb hqb hhb (U.polynomialEnergyBounds hc b)
    g.rapid_coefficients (SmoothCircleFunction.coefficient_real hg) r
  have hcM := U.smearedCore_closable hc ha f.rapid_coefficients
  have hcN := U.smearedCore_closable hc hb g.rapid_coefficients
  choose B hB hBnd using fun s => SymmetricOperator.flow_regularizer_factor T hs
    (U.inverseSobolev r) (U.sobolevExtension r N) (U.sobolevExtension r K)
    (U.inverseSobolev_selfAdjoint r) (U.inverseSobolev_dense r)
    (U.sobolevExtension_inverse_graph r N hn hcN)
    (U.sobolevExtension_defect r N K hn hk hpair) s
  have hcore (z : U.smoothEnergySpace) :
      (SymmetricOperator.flow T hs t z,
        SymmetricOperator.flow T hs t (U.smoothSmear hc ha f.rapid_coefficients z : Completion V)) ∈
          (U.closedSmoothField hc a d f).graph := by
    exact SymmetricOperator.regularized_commutation_on_dense_core
      (U.closedSmoothField hc a d f) T hs U.smoothEnergySpace U.smoothEnergySpace_dense
      (U.smoothSmear hc ha f.rapid_coefficients) (U.smoothSmear hc hb g.rapid_coefficients)
      (U.smoothSmear_graph hc ha f.rapid_coefficients) (U.smoothSmear_graph hc hb g.rapid_coefficients)
      (U.smoothSmear_symmetric hc ha hqa hha f.rapid_coefficients (SmoothCircleFunction.coefficient_real hf))
      (U.smoothSmear_weakCommutation_of_algebraic hc ha hb hweak)
      (U.inverseSobolev r) (U.sobolevExtension r M)
      (U.inverseSobolev_selfAdjoint r) (U.inverseSobolev_dense r)
      (fun z => ⟨U.smoothEnergyPower r z,U.inverseSobolev_smoothEnergyPower r z⟩)
      (U.sobolevExtension_inverse_graph r M hm hcM) B hB (norm_nonneg _) hBnd
      (fun s z => U.firstOrderSmear_flow_smoothEnergySpace hb hqb hhb (U.polynomialEnergyBounds hc b)
        hD hbnd g.rapid_coefficients (SmoothCircleFunction.coefficient_real hg) s z.property) t z
  apply SymmetricOperator.graph_invariant_of_core (HilbertCore.operator M) hcM
    (SymmetricOperator.flow T hs t) ?_ hxy
  intro u v huv
  obtain ⟨w,hw,hMw⟩ := (HilbertCore.operator M).mem_graph_iff.mp huv
  obtain ⟨z,rfl⟩ := (HilbertCore.equiv V).surjective w
  have hh := hcore ⟨(z : Completion V),U.core_le_smoothEnergySpace (HilbertCore.equiv V z).property⟩
  rw [U.smoothSmear_coe] at hh
  dsimp only [Prod.fst,Prod.snd] at hw hMw
  rw [← hw,← hMw]
  simpa only [M, closedSmoothField, smoothSmearedField, HilbertCore.operator_apply, HilbertCore.equiv_coe] using hh
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Filter
open scoped Topology

open Filter MeasureTheory
open scoped Topology

open MeasureTheory
open scoped Topology

open Filter MeasureTheory
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_SymmetricWeakCommute
attribute [-instance] _root_.OAI.StronglyRationalVOA.SmoothCircleFamily.instCoeFunForallRealSmoothCircleFunction _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)



lemma primary_power_graph_stressFlow (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a)
    (hh : U.IsHermitian d a) (hd : 1 ≤ d)
    {f : SmoothCircleFunction} (hf : f.IsReal) (t : ℝ)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d (f.power (d-1))).graph) :
    (SymmetricOperator.flow (U.closedSmoothField hc A.conformalVector 2 f)
        (U.stress_selfAdjoint hc hf) t x,
      SymmetricOperator.flow (U.closedSmoothField hc A.conformalVector 2 f)
        (U.stress_selfAdjoint hc hf) t y) ∈
      (U.closedSmoothField hc a d (f.power (d-1))).graph := by
  exact U.highField_graph_invariant_firstOrderFlow_of_weak hc ha A.conformal_mem
    (hp 1 (by norm_num)) A.conformal_quasiPrimary hh U.stress_hermitian
    (by linarith [U.centralCharge_nonneg]) U.stress_physical_bound
    (SmoothCircleFunction.power_real hf (d-1)) hf
    (fun v w => (U.primary_stress_weakCommutation hc ha hp hh hd hf v w).symm) t hxy

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)



theorem primary_power_graph_locality_of_localEstimate (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hp : A.IsPrimary a) (hqb : A.IsQuasiPrimary b)
    (hha : U.IsHermitian d a) (hhb : U.IsHermitian e b) (hd : 2 ≤ d)
    {f g : SmoothCircleFunction} (hf : f.IsReal) (hg : g.IsReal)
    (hfg : Disjoint (tsupport f) (tsupport g))
    (hlocal : U.PrimaryLocalEnergyEstimate hc ha f) (i j k l : Bool) :
    ClosedGraphData.entry (U.closedSmoothField hc a d (f.power (d-1)))
        (U.closedSmoothField_isClosed hc ha _) i j *
      ClosedGraphData.entry (U.closedSmoothField hc b e g)
        (U.closedSmoothField_isClosed hc hb _) k l =
    ClosedGraphData.entry (U.closedSmoothField hc b e g)
        (U.closedSmoothField_isClosed hc hb _) k l *
      ClosedGraphData.entry (U.closedSmoothField hc a d (f.power (d-1)))
        (U.closedSmoothField_isClosed hc ha _) i j := by
  obtain ⟨C,hC,hbound⟩ := hlocal
  have hfp := SmoothCircleFunction.power_real hf (d-1)
  have hsupport : Disjoint (tsupport (f.power (d-1))) (tsupport g) :=
    hfg.mono_left (SmoothCircleFunction.power_tsupport_subset f (by omega))
  let Q := U.smoothSmear hc hb g.rapid_coefficients
  let N := SymmetricOperator.onSubmodule U.smoothEnergySpace Q
  have hN : N.IsClosable := U.smoothSmear_core_closable hc hb g.rapid_coefficients
  have hNeq : N.closure = U.closedSmoothField hc b e g := U.smoothSmear_core hc hb g.rapid_coefficients
  have hPQ := SymmetricOperator.symmetric_weak_commute U.smoothEnergySpace
    (U.smoothSmear hc ha (f.power (d-1)).rapid_coefficients) Q
    (U.smoothSmear_symmetric hc ha (hp 1 (by norm_num)) hha _ (SmoothCircleFunction.coefficient_real hfp))
    (U.smoothSmear_symmetric hc hb hqb hhb _ (SmoothCircleFunction.coefficient_real hg))
    (U.smoothSmear_weakCommutation hc ha hb (hp 1 (by norm_num)) hqb hha hhb hfp hg hsupport)
  have he := SymmetricOperator.graph_entries_commute_of_local_energy U.smoothEnergySpace
    U.smoothEnergySpace_dense (U.smoothSmear hc ha (f.power (d-1)).rapid_coefficients) Q
    (U.smoothSmear hc A.conformal_mem f.rapid_coefficients)
    (U.closedSmoothField hc a d (f.power (d-1))) (U.closedSmoothField hc A.conformalVector 2 f) N
    (U.closedSmoothField_isClosed hc ha _)
    (U.closedSmoothField_symmetric hc ha (hp 1 (by norm_num)) hha hfp)
    (U.stress_selfAdjoint hc hf) hN (U.smoothSmear_graph hc ha _)
    (U.smoothSmear_graph hc A.conformal_mem _) (SymmetricOperator.onSubmodule_graph _ Q) hPQ
    (fun t _ _ hxy => U.primary_power_graph_stressFlow hc ha hp hha (by omega) hf t hxy)
    (fun t x y hxy => by
      rw [hNeq] at hxy ⊢
      exact U.highField_graph_invariant_firstOrderFlow hc hb A.conformal_mem hqb
        A.conformal_quasiPrimary hhb U.stress_hermitian (by linarith [U.centralCharge_nonneg])
        U.stress_physical_bound hg hf hfg.symm t hxy)
    (fun r _ x => U.stress_timeAverage_smooth hc hf r x.property) (d-1) hC
    (by simpa only [Nat.sub_add_cancel (show 1 ≤ d by omega)] using hbound) i j k l
  simpa only [hNeq] using he
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open MeasureTheory Set
open scoped ContDiff

open MeasureTheory Set Filter
open scoped Topology Interval

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_StressCutoffNormalized
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter

open UniformSpace Filter
open scoped Topology

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma smoothEnergyPower_inverse_next (r : ℕ) (x : U.smoothEnergySpace) :
    U.inverseSobolev 1 (U.smoothEnergyPower (r+1) x)=U.smoothEnergyPower r x := by
  apply U.inverseSobolev_injective r
  change (U.inverseSobolev r*U.inverseSobolev 1) (U.smoothEnergyPower (r+1) x)=_
  rw [U.inverseSobolev_mul,U.inverseSobolev_smoothEnergyPower,U.inverseSobolev_smoothEnergyPower]

lemma tendsto_smoothEnergyPower {ι : Type*} {l : Filter ι} (r : ℕ)
    (x : ι → U.smoothEnergySpace) (y : U.smoothEnergySpace)
    (hx : Tendsto (fun i => (x i : Completion V)) l (𝓝 (y : Completion V)))
    {C : ℝ} (hb : ∀ᶠ i in l, ‖U.smoothEnergyPower (r+1) (x i)‖ ≤ C) :
    Tendsto (fun i => U.smoothEnergyPower r (x i)) l (𝓝 (U.smoothEnergyPower r y)) := by
  have hb' : ∀ᶠ i in l,
      ‖U.smoothEnergyPower (r+1) (x i)-U.smoothEnergyPower (r+1) y‖ ≤
        C+‖U.smoothEnergyPower (r+1) y‖ := by
    filter_upwards [hb] with i hi
    have h1 := norm_sub_le (U.smoothEnergyPower (r+1) (x i)) (U.smoothEnergyPower (r+1) y)
    linarith
  apply tendsto_sub_nhds_zero_iff.mp
  exact U.tendsto_sobolev_of_extra_bound r
    (fun i => (x i : Completion V)-(y : Completion V))
    (fun i => U.smoothEnergyPower r (x i)-U.smoothEnergyPower r y)
    (fun i => U.smoothEnergyPower (r+1) (x i)-U.smoothEnergyPower (r+1) y)
    (fun i => by rw [map_sub,U.inverseSobolev_smoothEnergyPower,U.inverseSobolev_smoothEnergyPower])
    (fun i => by rw [map_sub,U.smoothEnergyPower_inverse_next,U.smoothEnergyPower_inverse_next])
    (tendsto_sub_nhds_zero_iff.mpr hx) hb'
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma smoothEnergyPower_eq_of_factor (Q B : Completion V →L[ℂ] Completion V) (r : ℕ)
    (hB : Q*U.inverseSobolev r=U.inverseSobolev r*B)
    (x y : U.smoothEnergySpace) (hy : (y : Completion V)=Q x) :
    U.smoothEnergyPower r y=B (U.smoothEnergyPower r x) := by
  apply U.inverseSobolev_injective r
  rw [U.inverseSobolev_smoothEnergyPower]
  change _ = (U.inverseSobolev r*B) _
  rw [← hB]
  change _ = Q (U.inverseSobolev r (U.smoothEnergyPower r x))
  rw [U.inverseSobolev_smoothEnergyPower,hy]

lemma stressPropagatorSmooth_bound (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    {r : ℕ} (hr : 1 ≤ r) (t : ℝ) (x : U.smoothEnergySpace) :
    ‖U.smoothEnergyPower r (U.stressPropagatorSmooth hc f t x)‖ ≤
      Real.exp ((f.bound (2+r)*((1+A.centralCharge.re)*r))*|t|)*‖U.smoothEnergyPower r x‖ := by
  obtain ⟨B,hB,hBn⟩ := U.stressPropagator_factor hc f hr t
  rw [U.smoothEnergyPower_eq_of_factor _ B r hB x (U.stressPropagatorSmooth hc f t x) rfl]
  exact B.le_of_opNorm_le hBn _

lemma stressCutoffEvolutionSmooth_bound (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    {r : ℕ} (hr : 1 ≤ r) (n : ℕ) (t : ℝ) (x : U.smoothEnergySpace) :
    ‖U.smoothEnergyPower r (U.stressCutoffEvolutionSmooth hc f n t x)‖ ≤
      Real.exp ((f.bound (2+r)*((1+A.centralCharge.re)*r))*|t|)*‖U.smoothEnergyPower r x‖ := by
  obtain ⟨B,hB,hBn⟩ := U.stressCutoff_evolution_factor hc f hr n t
  rw [U.smoothEnergyPower_eq_of_factor _ B r hB x (U.stressCutoffEvolutionSmooth hc f n t x) rfl]
  exact B.le_of_opNorm_le hBn _

lemma stressCutoffEvolutionSmooth_limit (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (r : ℕ) (t : ℝ) (x : U.smoothEnergySpace) :
    Tendsto (fun n => U.smoothEnergyPower r (U.stressCutoffEvolutionSmooth hc f n t x)) atTop
      (𝓝 (U.smoothEnergyPower r (U.stressPropagatorSmooth hc f t x))) := by
  apply U.tendsto_smoothEnergyPower r _ _ (U.stressPropagator_limit hc f t x)
  exact Filter.Eventually.of_forall (fun n => U.stressCutoffEvolutionSmooth_bound hc f (by omega : 1 ≤ r+1) n t x)
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter Set
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma stressCutoff_smooth_bound (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (n : ℕ) (t : ℝ) (x : U.smoothEnergySpace) :
    ‖U.stressCutoff hc n (f.rapid t) x‖ ≤
      (f.bound 2*(1+A.centralCharge.re))*‖U.smoothEnergyPower 1 x‖ := by
  rw [← U.inverseSobolev_smoothEnergyPower 1 x]
  have hn : ‖U.stressCutoff hc n (f.rapid t)*U.inverseSobolev 1‖ ≤ f.bound 2*(1+A.centralCharge.re) :=
    (U.stressCutoff_normalized_norm hc n (f.rapid t) le_rfl).trans
      (mul_le_mul_of_nonneg_right (f.seminorm_bound t 2) (by linarith [U.centralCharge_nonneg]))
  exact (U.stressCutoff hc n (f.rapid t)*U.inverseSobolev 1).le_of_opNorm_le hn _

lemma stressCutoff_derivative_bound (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (n : ℕ) {R t : ℝ} (ht : |t| ≤ R) (x : U.smoothEnergySpace) :
    ‖U.stressCutoff hc n (f.rapid t)
      (TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) t x)‖ ≤
      (f.bound 2*(1+A.centralCharge.re))*Real.exp ((f.bound 3*(1+A.centralCharge.re))*R)*
        ‖U.smoothEnergyPower 1 x‖ := by
  have h1 := U.stressCutoff_smooth_bound hc f n t (U.stressCutoffEvolutionSmooth hc f n t x)
  have h2 := U.stressCutoffEvolutionSmooth_bound hc f le_rfl n t x
  change ‖U.stressCutoff hc n (f.rapid t) (TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) t (x : Completion V))‖ ≤ _ at h1
  have hC : 0 ≤ 1+A.centralCharge.re := by linarith [U.centralCharge_nonneg]
  have hB := mul_nonneg (f.bound_nonneg 2) hC
  have hD := mul_nonneg (f.bound_nonneg 3) hC
  calc
    _ ≤ (f.bound 2*(1+A.centralCharge.re))*
        (Real.exp ((f.bound 3*(1+A.centralCharge.re))*|t|)*‖U.smoothEnergyPower 1 x‖) := by
      apply h1.trans
      exact mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_one,mul_one] using h2) hB
    _ ≤ _ := by
      have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht hD)
      exact (le_of_eq (mul_assoc (f.bound 2*(1+A.centralCharge.re))
        (Real.exp ((f.bound 3*(1+A.centralCharge.re))*|t|)) ‖U.smoothEnergyPower 1 x‖).symm).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hB) (norm_nonneg _))

lemma stressCutoff_evolution_sub_bound (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (n : ℕ) {R s t : ℝ} (hs : s ∈ Icc (-R) R) (ht : t ∈ Icc (-R) R)
    (x : U.smoothEnergySpace) :
    ‖TimeOrdered.evolution (fun q => U.stressCutoff hc n (f.rapid q)) t x-
      TimeOrdered.evolution (fun q => U.stressCutoff hc n (f.rapid q)) s x‖ ≤
      (f.bound 2*(1+A.centralCharge.re))*Real.exp ((f.bound 3*(1+A.centralCharge.re))*R)*
        ‖U.smoothEnergyPower 1 x‖*‖t-s‖ := by
  let : Nontrivial V := nontrivial_of_ne A.vacuum 0 A.vacuum_ne_zero
  let : Nontrivial (Completion V) := (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).injective.nontrivial
  apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun q _ => (TimeOrdered.evolution_apply_derivative
      (U.stressCutoff_continuous hc n f.rapid f.continuous)
      (show 0 ≤ (f.bound 2*(1+A.centralCharge.re))*(1+(n:ℝ)) by
        exact mul_nonneg (mul_nonneg (f.bound_nonneg 2) (by linarith [U.centralCharge_nonneg])) (by positivity))
      (U.stressPath_cutoff_bound hc f n) q (x : Completion V)).hasDerivWithinAt)
    (fun q hq => U.stressCutoff_derivative_bound hc f n (abs_le.mpr hq) x)
    (convex_Icc _ _) hs ht

lemma stressPropagator_sub_bound (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    {R s t : ℝ} (hs : s ∈ Icc (-R) R) (ht : t ∈ Icc (-R) R) (x : U.smoothEnergySpace) :
    ‖U.stressPropagator hc f t x-U.stressPropagator hc f s x‖ ≤
      (f.bound 2*(1+A.centralCharge.re))*Real.exp ((f.bound 3*(1+A.centralCharge.re))*R)*
        ‖U.smoothEnergyPower 1 x‖*‖t-s‖ := by
  exact le_of_tendsto ((U.stressPropagator_limit hc f t x).sub
    (U.stressPropagator_limit hc f s x)).norm
    (Filter.Eventually.of_forall (fun n => U.stressCutoff_evolution_sub_bound hc f n hs ht x))

lemma stressPropagator_smooth_continuous (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (x : U.smoothEnergySpace) : Continuous (fun t => U.stressPropagator hc f t x) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  let R := |s|+1
  let C := (f.bound 2*(1+A.centralCharge.re))*Real.exp ((f.bound 3*(1+A.centralCharge.re))*R)*
    ‖U.smoothEnergyPower 1 x‖
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg
    (mul_nonneg (f.bound_nonneg 2) (by linarith [U.centralCharge_nonneg])) (Real.exp_pos _).le) (norm_nonneg _)
  have hL : LipschitzOnWith ⟨C,hC⟩ (fun t => U.stressPropagator hc f t x) (Icc (-R) R) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro t ht q hq
    rw [dist_eq_norm,dist_eq_norm]
    change ‖U.stressPropagator hc f t x-U.stressPropagator hc f q x‖ ≤ C*‖t-q‖
    exact U.stressPropagator_sub_bound hc f hq ht x
  exact hL.continuousOn.continuousAt (Icc_mem_nhds (by dsimp [R]; linarith [neg_abs_le s])
    (by dsimp [R]; linarith [le_abs_self s]))

lemma stressPropagatorSmooth_continuous_power (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (r : ℕ) (x : U.smoothEnergySpace) :
    Continuous (fun t => U.smoothEnergyPower r (U.stressPropagatorSmooth hc f t x)) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  apply U.tendsto_smoothEnergyPower r (fun t => U.stressPropagatorSmooth hc f t x)
    (U.stressPropagatorSmooth hc f s x) (U.stressPropagator_smooth_continuous hc f x).continuousAt
    (C := Real.exp ((f.bound (2+(r+1))*((1+A.centralCharge.re)*(r+1)))*(|s|+1))*
      ‖U.smoothEnergyPower (r+1) x‖)
  have hne : ∀ᶠ t in 𝓝 s, |t| < |s|+1 := continuous_abs.continuousAt.eventually
    (gt_mem_nhds (by linarith : |s| < |s|+1))
  filter_upwards [hne] with t ht
  apply (U.stressPropagatorSmooth_bound hc f (by omega : 1 ≤ r+1) t x).trans
  have hC : 0 ≤ 1+A.centralCharge.re := by linarith [U.centralCharge_nonneg]
  have hD : 0 ≤ f.bound (2+(r+1))*((1+A.centralCharge.re)*(r+1)) :=
    mul_nonneg (f.bound_nonneg _) (mul_nonneg hC (by positivity))
  simpa only [Nat.cast_add,Nat.cast_one] using
    mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.le hD))
      (norm_nonneg (U.smoothEnergyPower (r+1) x))
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter Set MeasureTheory
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_StressCutoffNormalized2
attribute [-instance] _root_.OAI.StronglyRationalVOA.SmoothCircleFamily.instCoeFunForallRealSmoothCircleFunction _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma stressPropagatorDerivative_continuous (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (x : U.smoothEnergySpace) : Continuous (fun t => U.stressPropagatorDerivative hc f t x) := by
  exact (continuous_const (y := Complex.I)).smul ((U.stressNormalized_continuous hc f.rapid f.continuous
    (by norm_num : 1 ≤ 2)).clm_apply (U.stressPropagatorSmooth_continuous_power hc f 2 x))

lemma stressCutoff_derivative_limit (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (t : ℝ) (x : U.smoothEnergySpace) :
    Tendsto (fun n => U.stressCutoff hc n (f.rapid t)
      (TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) t x)) atTop
      (𝓝 (U.stressPropagatorDerivative hc f t x)) := by
  have h := (isBoundedBilinearMap_apply (𝕜 := ℂ)).continuous.tendsto
    (Complex.I • U.stressNormalized hc (f.rapid t) 2,
      U.smoothEnergyPower 2 (U.stressPropagatorSmooth hc f t x)) |>.comp
      ((U.stressCutoff_normalized_limit hc (f.rapid t)).prodMk_nhds
        (U.stressCutoffEvolutionSmooth_limit hc f 2 t x))
  convert h using 1
  · ext n
    change _ = U.stressCutoff hc n (f.rapid t)
      (U.inverseSobolev 2 (U.smoothEnergyPower 2 (U.stressCutoffEvolutionSmooth hc f n t x)))
    rw [U.inverseSobolev_smoothEnergyPower]
    rfl
  · rfl

lemma stressCutoff_integral_limit (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (a b : ℝ) (x : U.smoothEnergySpace) :
    Tendsto (fun n => ∫ t in a..b, U.stressCutoff hc n (f.rapid t)
      (TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) t x)) atTop
      (𝓝 (∫ t in a..b, U.stressPropagatorDerivative hc f t x)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => (f.bound 2*(1+A.centralCharge.re))*Real.exp ((f.bound 3*(1+A.centralCharge.re))*(|a|+|b|))*
      ‖U.smoothEnergyPower 1 x‖)
  · exact Eventually.of_forall (fun n => ((U.stressCutoff_continuous hc n f.rapid f.continuous).clm_apply
      (U.stressCutoff_evolution_continuous hc f n x)).aestronglyMeasurable)
  · apply Eventually.of_forall
    intro n
    apply Eventually.of_forall
    intro t ht
    have htab := uIoc_subset_uIcc ht
    have hr : |t| ≤ |a|+|b| := by
      rcases le_total a b with hab | hba
      · rw [uIcc_of_le hab] at htab
        exact (abs_le_max_abs_abs htab.1 htab.2).trans (max_le
          (le_add_of_nonneg_right (abs_nonneg b)) (le_add_of_nonneg_left (abs_nonneg a)))
      · rw [uIcc_of_ge hba] at htab
        exact (abs_le_max_abs_abs htab.1 htab.2).trans (max_le
          (le_add_of_nonneg_left (abs_nonneg a)) (le_add_of_nonneg_right (abs_nonneg b)))
    exact U.stressCutoff_derivative_bound hc f n hr x
  · exact intervalIntegrable_const
  · exact Eventually.of_forall (fun t _ => U.stressCutoff_derivative_limit hc f t x)

lemma stressPropagator_integral (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (a b : ℝ) (x : U.smoothEnergySpace) :
    (∫ t in a..b, U.stressPropagatorDerivative hc f t x)=
      U.stressPropagator hc f b x-U.stressPropagator hc f a x := by
  have hi := U.stressCutoff_integral_limit hc f a b x
  have he : ∀ n, (∫ t in a..b, U.stressCutoff hc n (f.rapid t)
      (TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) t x)) =
      TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) b x-
      TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) a x := by
    intro n
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => U.stressCutoff_evolution_derivative hc f n t x)
      (((U.stressCutoff_continuous hc n f.rapid f.continuous).clm_apply
        (U.stressCutoff_evolution_continuous hc f n x)).intervalIntegrable a b)
  simp_rw [he] at hi
  exact tendsto_nhds_unique hi ((U.stressPropagator_limit hc f b x).sub (U.stressPropagator_limit hc f a x))

 

lemma stressPropagator_derivative (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (t : ℝ) (x : U.smoothEnergySpace) :
    HasDerivAt (fun s => U.stressPropagator hc f s x) (U.stressPropagatorDerivative hc f t x) t := by
  have h := U.stressPropagatorDerivative_continuous hc f x
  have hd := intervalIntegral.integral_hasDerivAt_right (h.intervalIntegrable 0 t)
    h.stronglyMeasurable.stronglyMeasurableAtFilter h.continuousAt
  have he : (fun s => U.stressPropagator hc f s x)=
      (fun s => (∫ q in (0:ℝ)..s, U.stressPropagatorDerivative hc f q x)+U.stressPropagator hc f 0 x) := by
    funext s
    rw [U.stressPropagator_integral hc f 0 s x,sub_add_cancel]
  rw [he]
  exact hd.add_const _

lemma stressPropagatorDerivative_graph (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (t : ℝ) (x : U.smoothEnergySpace) :
    (U.stressPropagator hc f t x,(-Complex.I) • U.stressPropagatorDerivative hc f t x) ∈
      (U.closedSmearedOperator hc A.conformalVector 2 (f.coefficients t) (f.rapid t)).graph := by
  have hg := U.stressNormalized_graph hc (f.rapid t) (by norm_num : 1 ≤ 2)
    (U.smoothEnergyPower 2 (U.stressPropagatorSmooth hc f t x))
  rw [U.inverseSobolev_smoothEnergyPower] at hg
  simpa only [stressPropagatorDerivative,stressPropagatorSmooth,LinearMap.codRestrict_apply,
    LinearMap.comp_apply,Submodule.subtype_apply,ContinuousLinearMap.coe_coe,smul_smul,neg_mul,Complex.I_mul_I,neg_neg,one_smul] using hg
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Filter
open scoped Topology

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma normalizedField_continuous (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d p k : ℕ}
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n:ℝ)|)^p*‖(A.energyShift^k) v‖)
    {f : ℝ → ℤ → ℂ} (hf : ∀ t, RapidCoefficients (f t))
    (hl : ∀ t, Tendsto (fun s => coefficientSeminorm (fun n => f s n-f t n) p) (𝓝 t) (𝓝 0)) :
    Continuous (fun t => U.normalizedField hc a d k (hf t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun s => (U.normalizedField_sub hc hb (hf s) (hf t)) ▸ U.normalizedField_norm hc hC hb ((hf s).sub (hf t)))
  simpa only [zero_mul] using (hl t).mul_const C

 

lemma normalizedField_derivative (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d p k : ℕ}
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n:ℝ)|)^p*‖(A.energyShift^k) v‖)
    {f : ℝ → ℤ → ℂ} (hf : ∀ t, RapidCoefficients (f t)) {g : ℤ → ℂ} (hg : RapidCoefficients g)
    (t : ℝ) (hl : Tendsto (fun s => coefficientSeminorm
      (fun n => (((s-t)⁻¹ : ℝ):ℂ)*(f s n-f t n)-g n) p) (𝓝[≠] t) (𝓝 0)) :
    HasDerivAt (fun s => U.normalizedField hc a d k (hf s)) (U.normalizedField hc a d k hg) t := by
  rw [hasDerivAt_iff_tendsto_slope,tendsto_iff_norm_sub_tendsto_zero]
  have he (s : ℝ) : slope (fun q => U.normalizedField hc a d k (hf q)) t s-U.normalizedField hc a d k hg =
      U.normalizedField hc a d k ((((hf s).sub (hf t)).smul (((s-t)⁻¹ : ℝ):ℂ)).sub hg) := by
    rw [U.normalizedField_sub hc hb (((hf s).sub (hf t)).smul (((s-t)⁻¹ : ℝ):ℂ)) hg,
      U.normalizedField_smul hc hb ((hf s).sub (hf t)),U.normalizedField_sub hc hb (hf s) (hf t)]
    simp only [slope]
    rfl
  apply squeeze_zero (fun _ => norm_nonneg _) (fun s => he s ▸ U.normalizedField_norm hc hC hb _)
  simpa only [zero_mul] using hl.mul_const C
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma smoothSmear_weakCommutator_of_algebraic (hc : A.toVertexAlgebra.C2Cofinite)
    {a b c : V} {d e j : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hcj : c ∈ A.grade j)
    {f g h : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) (hh : RapidCoefficients h)
    (z : ℂ)
    (hweak : ∀ x y : V,
      inner ℂ (A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf x)
        (A.smearedMap b e (U.polynomialEnergyBounds hc b) g hg y)-
      inner ℂ (A.smearedMap b e (U.polynomialEnergyBounds hc b) g hg x)
        (A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf y)=
      z*inner ℂ (x:Completion V) (A.smearedMap c j (U.polynomialEnergyBounds hc c) h hh y))
    (x y : U.smoothEnergySpace) :
    inner ℂ (U.smoothSmear hc ha hf x : Completion V) (U.smoothSmear hc hb hg y : Completion V)-
      inner ℂ (U.smoothSmear hc hb hg x : Completion V) (U.smoothSmear hc ha hf y : Completion V)=
      z*inner ℂ (x:Completion V) (U.smoothSmear hc hcj hh y : Completion V) := by
  obtain ⟨C,hC,p,k,hM⟩ := (U.polynomialEnergyBounds hc a).physical A d
  obtain ⟨D,hD,q,l,hN⟩ := (U.polynomialEnergyBounds hc b).physical A e
  obtain ⟨E,hE,o,m,hQ⟩ := (U.polynomialEnergyBounds hc c).physical A j
  let M := A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf
  let N := A.smearedMap b e (U.polynomialEnergyBounds hc b) g hg
  let Q := A.smearedMap c j (U.polynomialEnergyBounds hc c) h hh
  have hm (v : V) : ‖M v‖ ≤ (coefficientSeminorm f p*C)*‖(A.energyShift^(k+l+m)) v‖ :=
    (A.smearedMap_bound _ hf hM v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : k ≤ k+l+m) v)
        (mul_nonneg (coefficientSeminorm_nonneg _ _) hC.le))
  have hn (v : V) : ‖N v‖ ≤ (coefficientSeminorm g q*D)*‖(A.energyShift^(k+l+m)) v‖ :=
    (A.smearedMap_bound _ hg hN v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : l ≤ k+l+m) v)
        (mul_nonneg (coefficientSeminorm_nonneg _ _) hD.le))
  have hq (v : V) : ‖Q v‖ ≤ (coefficientSeminorm h o*E)*‖(A.energyShift^(k+l+m)) v‖ :=
    (A.smearedMap_bound _ hh hQ v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : m ≤ k+l+m) v)
        (mul_nonneg (coefficientSeminorm_nonneg _ _) hE.le))
  rw [U.smoothSmear_eq_extension hc ha hf hm x (U.smoothEnergyPower_graph (k+l+m) x),
    U.smoothSmear_eq_extension hc hb hg hn y (U.smoothEnergyPower_graph (k+l+m) y),
    U.smoothSmear_eq_extension hc hb hg hn x (U.smoothEnergyPower_graph (k+l+m) x),
    U.smoothSmear_eq_extension hc ha hf hm y (U.smoothEnergyPower_graph (k+l+m) y),
    U.smoothSmear_eq_extension hc hcj hh hq y (U.smoothEnergyPower_graph (k+l+m) y),
    U.sobolevExtension_weakCommutator (k+l+m) M N Q hm hn hq z hweak,
    U.inverseSobolev_smoothEnergyPower]

lemma primary_stress_smoothCommutator (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a) (hh : U.IsHermitian d a)
    {f g h : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) (hhc : RapidCoefficients h)
    (hfr : ∀ n, star (f n)=f (-n)) (hgr : ∀ n, star (g n)=g (-n))
    (hconv : ∀ r : ℤ, HasSum (fun m : ℤ => (((d:ℂ)-1)*m-(r-m))*f m*g (r-m)) (-Complex.I*h r))
    (x y : U.smoothEnergySpace) :
    inner ℂ (U.smoothSmear hc A.conformal_mem hf x : Completion V)
      (U.smoothSmear hc ha hg y : Completion V)-
    inner ℂ (U.smoothSmear hc ha hg x : Completion V)
      (U.smoothSmear hc A.conformal_mem hf y : Completion V)=
    -Complex.I*inner ℂ (x:Completion V) (U.smoothSmear hc ha hhc y : Completion V) :=
  U.smoothSmear_weakCommutator_of_algebraic hc A.conformal_mem ha ha hf hg hhc (-Complex.I)
    (U.primary_stress_weakCommutator hc ha hp hh hf hg hhc hfr hgr hconv) x y
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction

lemma hasSum_primaryTransport (f g : SmoothCircleFunction) (d : ℕ) (r : ℤ) :
    HasSum (fun m : ℤ => (((d:ℂ)-1)*m-(r-m))*f.coefficient m*g.coefficient (r-m))
      (-Complex.I*(f.primaryTransport g d).coefficient r) := by
  have h1 := ((f.differentiated 1).coefficient_mul g r).mul_left ((d:ℂ)-1)
  have h2 := f.coefficient_mul (g.differentiated 1) r
  have h := (h1.sub h2).mul_left (-Complex.I)
  rw [primaryTransport,coefficient_add,coefficient_scale,coefficient_scale]
  rw [show ((d:ℂ)-1)*((f.differentiated 1).mul g).coefficient r +
    (-1)*(f.mul (g.differentiated 1)).coefficient r =
    ((d:ℂ)-1)*((f.differentiated 1).mul g).coefficient r -
    (f.mul (g.differentiated 1)).coefficient r by ring]
  apply h.congr_fun
  intro m
  simp only [coefficient_differentiated,pow_one]
  push_cast
  ring_nf
  norm_num [Complex.I_sq]
  ring
end StronglyRationalVOA.SmoothCircleFunction

open UniformSpace Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_StressPropagatorDerivative
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma stressPropagatorDerivative_smoothSmear (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (t : ℝ) (x : U.smoothEnergySpace) :
    U.stressPropagatorDerivative hc f t x=Complex.I •
      (U.smoothSmear hc A.conformal_mem (f.rapid t) (U.stressPropagatorSmooth hc f t x) : Completion V) := by
  have he := (U.closedSmearedOperator hc A.conformalVector 2 (f.coefficients t) (f.rapid t)).mem_graph_snd_inj
    (U.stressPropagatorDerivative_graph hc f t x)
    (U.smoothSmear_graph hc A.conformal_mem (f.rapid t) (U.stressPropagatorSmooth hc f t x)) rfl
  have h := congrArg (fun v : Completion V => Complex.I • v) he
  simpa only [smul_smul,mul_neg,Complex.I_mul_I,neg_neg,one_smul] using h

 

lemma smoothSmear_form_derivative (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d p k : ℕ} (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n:ℝ)|)^p*‖(A.energyShift^k) v‖)
    {g : ℝ → ℤ → ℂ} (hg : ∀ t, RapidCoefficients (g t)) {h : ℤ → ℂ} (hr : RapidCoefficients h)
    (t : ℝ) (hgr : ∀ n, star (g t n)=g t (-n))
    (hl : Tendsto (fun s => coefficientSeminorm
      (fun n => (((s-t)⁻¹:ℝ):ℂ)*(g s n-g t n)-h n) p) (𝓝[≠] t) (𝓝 0))
    (x y : ℝ → U.smoothEnergySpace) (dx dy : Completion V)
    (hx : HasDerivAt (fun s => (x s : Completion V)) dx t)
    (hy : HasDerivAt (fun s => (y s : Completion V)) dy t)
    (hyc : ContinuousAt (fun s => U.smoothEnergyPower k (y s)) t) :
    HasDerivAt (fun s => inner ℂ (x s : Completion V) (U.smoothSmear hc ha (hg s) (y s) : Completion V))
      (inner ℂ dx (U.smoothSmear hc ha (hg t) (y t) : Completion V)+
        inner ℂ (U.smoothSmear hc ha (hg t) (x t) : Completion V) dy+
        inner ℂ (x t : Completion V) (U.smoothSmear hc ha hr (y t) : Completion V)) t := by
  let P (s : ℝ) : U.smoothEnergySpace →ₗ[ℂ] Completion V :=
    U.smoothEnergySpace.subtype.comp (U.smoothSmear hc ha (hg s))
  have hd := U.normalizedField_derivative hc hC hb hg hr t hl
  have hPy : ContinuousAt (fun s => P s (y s)) t := by
    have hc' := hd.continuousAt.clm_apply hyc
    simpa only [P,LinearMap.comp_apply,Submodule.subtype_apply,
      U.smoothSmear_eq_normalized hc ha hb] using hc'
  have hP : Tendsto (fun s => (s-t)⁻¹ • (P s (y s)-P t (y s))) (𝓝[≠] t)
      (𝓝 (U.smoothSmear hc ha hr (y t) : Completion V)) := by
    have he (s : ℝ) : (s-t)⁻¹ • (P s (y s)-P t (y s))=
        slope (fun q => U.normalizedField hc a d k (hg q)) t s (U.smoothEnergyPower k (y s)) := by
      dsimp only [P,LinearMap.comp_apply,Submodule.subtype_apply]
      rw [U.smoothSmear_eq_normalized hc ha hb,U.smoothSmear_eq_normalized hc ha hb]
      simp only [slope,vsub_eq_sub,smul_apply,sub_apply]
    have ht := (isBoundedBilinearMap_apply (𝕜 := ℂ)).continuous.tendsto
      (U.normalizedField hc a d k hr,U.smoothEnergyPower k (y t)) |>.comp
      (hd.tendsto_slope.prodMk_nhds (hyc.mono_left nhdsWithin_le_nhds))
    simpa only [Function.comp_def,← he,← U.smoothSmear_eq_normalized hc ha hb] using ht
  exact SymmetricOperator.form_pairing_derivative U.smoothEnergySpace P x y t dx dy
    (U.smoothSmear hc ha hr (y t)) (U.smoothSmear_symmetric hc ha hq hh (hg t) hgr) hx hy hPy hP
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma primary_transport_form_derivative (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a) (hh : U.IsHermitian d a)
    (f : StressPath) {g : ℝ → ℤ → ℂ} (hg : ∀ t, RapidCoefficients (g t))
    {h : ℤ → ℂ} (hr : RapidCoefficients h) (t : ℝ)
    (hgr : ∀ n, star (g t n)=g t (-n))
    (hl : ∀ p, Tendsto (fun s => coefficientSeminorm
      (fun n => (((s-t)⁻¹:ℝ):ℂ)*(g s n-g t n)-h n) p) (𝓝[≠] t) (𝓝 0))
    (hconv : ∀ r : ℤ, HasSum (fun m : ℤ => (((d:ℂ)-1)*m-(r-m))*f.coefficients t m*g t (r-m)) (-Complex.I*h r))
    (x y : U.smoothEnergySpace) :
    HasDerivAt (fun s => inner ℂ (U.stressPropagator hc f s x)
      (U.smoothSmear hc ha (hg s) (U.stressPropagatorSmooth hc f s y) : Completion V)) 0 t := by
  obtain ⟨C,hC,p,k,hb⟩ := (U.polynomialEnergyBounds hc a).physical A d
  have hd := U.smoothSmear_form_derivative hc ha (hp 1 (by norm_num)) hh (le_of_lt hC) hb hg hr t hgr (hl p)
    (fun s => U.stressPropagatorSmooth hc f s x) (fun s => U.stressPropagatorSmooth hc f s y)
    _ _ (U.stressPropagator_derivative hc f t x) (U.stressPropagator_derivative hc f t y)
    (U.stressPropagatorSmooth_continuous_power hc f k y).continuousAt
  have hw := U.primary_stress_smoothCommutator hc ha hp hh (f.rapid t) (hg t) hr
    (f.real t) hgr hconv (U.stressPropagatorSmooth hc f t x) (U.stressPropagatorSmooth hc f t y)
  rw [U.stressPropagatorDerivative_smoothSmear hc f t x,
    U.stressPropagatorDerivative_smoothSmear hc f t y,
    inner_smul_left,inner_smul_right,Complex.conj_I] at hd
  have hz := congrArg (fun z : ℂ => -Complex.I*z) hw
  simp only [neg_mul_neg,← mul_assoc,Complex.I_mul_I,neg_one_mul] at hz
  have he : -Complex.I * inner ℂ
        (U.smoothSmear hc A.conformal_mem (f.rapid t) (U.stressPropagatorSmooth hc f t x) : Completion V)
        (U.smoothSmear hc ha (hg t) (U.stressPropagatorSmooth hc f t y) : Completion V) +
      Complex.I * inner ℂ
        (U.smoothSmear hc ha (hg t) (U.stressPropagatorSmooth hc f t x) : Completion V)
        (U.smoothSmear hc A.conformal_mem (f.rapid t) (U.stressPropagatorSmooth hc f t y) : Completion V) +
      inner ℂ (U.stressPropagatorSmooth hc f t x : Completion V)
        (U.smoothSmear hc ha hr (U.stressPropagatorSmooth hc f t y) : Completion V)=0 := by
    linear_combination hz
  rw [he] at hd
  exact hd

 
lemma primary_transport_form_constant (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a) (hh : U.IsHermitian d a)
    (f : StressPath) {g h : ℝ → ℤ → ℂ} (hg : ∀ t, RapidCoefficients (g t))
    (hr : ∀ t, RapidCoefficients (h t)) {S : Set ℝ} (hS : Convex ℝ S) (h0 : 0 ∈ S)
    (hgr : ∀ t ∈ S, ∀ n, star (g t n)=g t (-n))
    (hl : ∀ t ∈ S, ∀ p, Tendsto (fun s => coefficientSeminorm
      (fun n => (((s-t)⁻¹:ℝ):ℂ)*(g s n-g t n)-h t n) p) (𝓝[≠] t) (𝓝 0))
    (hconv : ∀ t ∈ S, ∀ r : ℤ, HasSum (fun m : ℤ => (((d:ℂ)-1)*m-(r-m))*f.coefficients t m*g t (r-m)) (-Complex.I*h t r))
    {t : ℝ} (ht : t ∈ S) (x y : U.smoothEnergySpace) :
    inner ℂ (U.stressPropagator hc f t x)
      (U.smoothSmear hc ha (hg t) (U.stressPropagatorSmooth hc f t y) : Completion V)=
    inner ℂ (x : Completion V) (U.smoothSmear hc ha (hg 0) y : Completion V) := by
  have hd (s : ℝ) (hs : s ∈ S) := U.primary_transport_form_derivative hc ha hp hh f hg (hr s)
    s (hgr s hs) (hl s hs) (hconv s hs) x y
  have he := hS.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hd s hs).hasDerivWithinAt) (fun _ _ => (norm_zero : ‖(0:ℂ)‖=0).le) h0 ht
  have hz : U.stressPropagatorSmooth hc f 0 y=y := by
    apply Subtype.ext
    change U.stressPropagator hc f 0 y=(y:Completion V)
    rw [U.stressPropagator_zero hc f,one_apply_eq_self]
  simpa only [zero_mul,norm_le_zero_iff,sub_eq_zero,U.stressPropagator_zero hc f,one_apply_eq_self,hz] using he

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Filter
open scoped Topology ContDiff

open Filter
open scoped Topology ContDiff

open Filter
open scoped Topology ContDiff

open Filter MeasureTheory Set
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_CoefficientSummableBound
attribute [-instance] _root_.OAI.StronglyRationalVOA.PositiveCircleGeometry.SmoothLift.instTopologicalSpace _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set

open Filter Set
open scoped Topology ContDiff

open UniformSpace Filter
open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction

lemma hasSum_cocycleDensity (f g : SmoothCircleFunction) :
    HasSum (fun m : ℤ => ((m:ℂ)^3-m)*f.coefficient m*g.coefficient (-m))
      (Complex.I*(f.cocycleDensity g).coefficient 0) := by
  have h := (((f.differentiated 3).coefficient_mul g 0).add
    ((f.differentiated 1).coefficient_mul g 0)).mul_left Complex.I
  rw [cocycleDensity]
  have he : ((f.differentiated 3).add (f.differentiated 1)).mul g =
      ((f.differentiated 3).mul g).add ((f.differentiated 1).mul g) := by
    apply ext; intro x; simp only [mul_apply,add_apply]; ring
  rw [he,coefficient_add]
  apply h.congr_fun
  intro m
  simp only [coefficient_differentiated,zero_sub,pow_one]
  ring_nf
  norm_num [Complex.I_sq]
end StronglyRationalVOA.SmoothCircleFunction
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma smoothSmear_weakCommutator_central_of_algebraic (hc : A.toVertexAlgebra.C2Cofinite)
    {a b c : V} {d e j : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hcj : c ∈ A.grade j)
    {f g h : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) (hh : RapidCoefficients h)
    (z w : ℂ)
    (hweak : ∀ x y : V,
      inner ℂ (A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf x)
        (A.smearedMap b e (U.polynomialEnergyBounds hc b) g hg y)-
      inner ℂ (A.smearedMap b e (U.polynomialEnergyBounds hc b) g hg x)
        (A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf y)=
      z*inner ℂ (x:Completion V) (A.smearedMap c j (U.polynomialEnergyBounds hc c) h hh y)+w*inner ℂ x y)
    (x y : U.smoothEnergySpace) :
    inner ℂ (U.smoothSmear hc ha hf x : Completion V) (U.smoothSmear hc hb hg y : Completion V)-
      inner ℂ (U.smoothSmear hc hb hg x : Completion V) (U.smoothSmear hc ha hf y : Completion V)=
      z*inner ℂ (x:Completion V) (U.smoothSmear hc hcj hh y : Completion V)+w*inner ℂ (x:Completion V) (y:Completion V) := by
  obtain ⟨C,hC,p,k,hM⟩ := (U.polynomialEnergyBounds hc a).physical A d
  obtain ⟨D,hD,q,l,hN⟩ := (U.polynomialEnergyBounds hc b).physical A e
  obtain ⟨E,hE,o,m,hQ⟩ := (U.polynomialEnergyBounds hc c).physical A j
  let M := A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf
  let N := A.smearedMap b e (U.polynomialEnergyBounds hc b) g hg
  let Q := A.smearedMap c j (U.polynomialEnergyBounds hc c) h hh
  have hm (v : V) : ‖M v‖ ≤ (coefficientSeminorm f p*C)*‖(A.energyShift^(k+l+m)) v‖ :=
    (A.smearedMap_bound _ hf hM v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : k ≤ k+l+m) v)
        (mul_nonneg (coefficientSeminorm_nonneg _ _) hC.le))
  have hn (v : V) : ‖N v‖ ≤ (coefficientSeminorm g q*D)*‖(A.energyShift^(k+l+m)) v‖ :=
    (A.smearedMap_bound _ hg hN v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : l ≤ k+l+m) v)
        (mul_nonneg (coefficientSeminorm_nonneg _ _) hD.le))
  have hq (v : V) : ‖Q v‖ ≤ (coefficientSeminorm h o*E)*‖(A.energyShift^(k+l+m)) v‖ :=
    (A.smearedMap_bound _ hh hQ v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : m ≤ k+l+m) v)
        (mul_nonneg (coefficientSeminorm_nonneg _ _) hE.le))
  rw [U.smoothSmear_eq_extension hc ha hf hm x (U.smoothEnergyPower_graph (k+l+m) x),
    U.smoothSmear_eq_extension hc hb hg hn y (U.smoothEnergyPower_graph (k+l+m) y),
    U.smoothSmear_eq_extension hc hb hg hn x (U.smoothEnergyPower_graph (k+l+m) x),
    U.smoothSmear_eq_extension hc ha hf hm y (U.smoothEnergyPower_graph (k+l+m) y),
    U.smoothSmear_eq_extension hc hcj hh hq y (U.smoothEnergyPower_graph (k+l+m) y),
    U.sobolevExtension_weakCommutator_central (k+l+m) M N Q hm hn hq z w hweak,
    U.inverseSobolev_smoothEnergyPower,U.inverseSobolev_smoothEnergyPower]

lemma stress_stress_weakCommutator (hc : A.toVertexAlgebra.C2Cofinite)
    (f g : SmoothCircleFunction) (hfr : f.IsReal) (hgr : g.IsReal) (x y : V) :
    inner ℂ (A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector) f.coefficient f.rapid_coefficients x)
      (A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector) g.coefficient g.rapid_coefficients y)-
    inner ℂ (A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector) g.coefficient g.rapid_coefficients x)
      (A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector) f.coefficient f.rapid_coefficients y)=
    -Complex.I*inner ℂ (x:Completion V)
      (A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector)
        (f.primaryTransport g 2).coefficient (f.primaryTransport g 2).rapid_coefficients y) +
      (A.centralCharge/12)*(Complex.I*(f.cocycleDensity g).coefficient 0)*inner ℂ x y := by
  have hν : U.IsHermitian 2 A.conformalVector := by simp [IsHermitian,U.pct_conformal]
  let M := A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector) f.coefficient f.rapid_coefficients
  let N := A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector) g.coefficient g.rapid_coefficients
  let Q := A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector)
    (f.primaryTransport g 2).coefficient (f.primaryTransport g 2).rapid_coefficients
  let c : ℂ := (A.centralCharge/12)*(Complex.I*(f.cocycleDensity g).coefficient 0)
  have hv (n : ℤ) : A.physicalMode A.conformalVector 2 n=A.virasoroMode n := by
    unfold physicalMode virasoroMode; congr 1; omega
  have Hhom (D E : ℕ) (x y : V) (hx : x ∈ A.grade D) (hy : y ∈ A.grade E) :
      inner ℂ (M x) (N y)-inner ℂ (N x) (M y) =
        -Complex.I*inner ℂ (x:Completion V) (Q y)+c*inner ℂ x y := by
    let r : ℤ := (E:ℤ)-D
    have H1 := U.hasSum_smeared_inner_homogeneous A.conformal_mem A.conformal_mem hx hy
      A.conformal_quasiPrimary hν (U.polynomialEnergyBounds hc A.conformalVector)
      (U.polynomialEnergyBounds hc A.conformalVector) f.rapid_coefficients g.rapid_coefficients
      (SmoothCircleFunction.coefficient_real hfr)
    have H2 := U.hasSum_smeared_inner_homogeneous A.conformal_mem A.conformal_mem hx hy
      A.conformal_quasiPrimary hν (U.polynomialEnergyBounds hc A.conformalVector)
      (U.polynomialEnergyBounds hc A.conformalVector) g.rapid_coefficients f.rapid_coefficients
      (SmoothCircleFunction.coefficient_real hgr)
    let R : ℤ ≃ ℤ :=
      { toFun := fun m => r-m
        invFun := fun m => r-m
        left_inv := fun m => by dsimp; omega
        right_inv := fun m => by dsimp; omega }
    have Hdiff := H1.sub (R.hasSum_iff.mpr H2)
    have Hz := (f.hasSum_primaryTransport g 2 r).mul_right (inner ℂ x (A.virasoroMode r y))
    have Hc : HasSum (fun m : ℤ => f.coefficient m*g.coefficient (r-m)*
        (if r=0 then (A.centralCharge/12)*((m:ℂ)^3-m) else 0)*inner ℂ x y)
        (c*inner ℂ x y) := by
      by_cases hr : r=0
      · simp only [hr,zero_sub,ite_eq_left]
        apply (((f.hasSum_cocycleDensity g).mul_left (A.centralCharge/12)).mul_right (inner ℂ x y)).congr_fun
        intro m; ring
      · have hin : inner ℂ x y=0 := U.grades_orthogonal (by intro he; apply hr; dsimp [r]; simp [he]) hx hy
        simp only [ite_eq_right hr,hin,mul_zero]
        exact hasSum_zero
    have He : HasSum (fun m : ℤ => f.coefficient m*g.coefficient (r-m)*inner ℂ x
        (A.virasoroMode m (A.virasoroMode (r-m) y)-
          A.virasoroMode (r-m) (A.virasoroMode m y)))
        (-Complex.I*inner ℂ (x:Completion V) (Q y)+c*inner ℂ x y) := by
      have hs := Hz.add Hc
      change HasSum _ (-Complex.I*inner ℂ (x:Completion V)
        (A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector)
          (f.primaryTransport g 2).coefficient (f.primaryTransport g 2).rapid_coefficients y)+_) 
      rw [U.inner_smearedMap_homogeneous A.conformal_mem hx hy,hv]
      change HasSum _ (-Complex.I*((f.primaryTransport g 2).coefficient r*inner ℂ x (A.virasoroMode r y))+c*inner ℂ x y)
      rw [← mul_assoc]
      apply hs.congr_fun
      intro m
      rw [A.virasoro_commutator,show m+(r-m)=r by omega,inner_add_right,inner_smul_right,inner_smul_right]
      push_cast
      norm_num
      split_ifs <;> ring
    apply Hdiff.unique
    convert He using 1
    all_goals try with_reducible_and_instances rfl
    ext m
    simp only [Function.comp_def,R,Equiv.coe_fn_mk]
    rw [show (E:ℤ)-D-(r-m)=m by dsimp [r]; omega]
    simp only [hv,inner_sub_right]
    ring
  change inner ℂ (M x) (N y)-inner ℂ (N x) (M y) =
    -Complex.I*inner ℂ (x:Completion V) (Q y)+c*inner ℂ x y
  apply A.homogeneous_induction (P := fun x => inner ℂ (M x) (N y)-inner ℂ (N x) (M y) =
    -Complex.I*inner ℂ (x:Completion V) (Q y)+c*inner ℂ x y)
  · simp only [map_zero,inner_zero_left,sub_self,Completion.coe_zero,mul_zero,add_zero]
  · intro D x hx
    apply A.homogeneous_induction (P := fun y => inner ℂ (M x) (N y)-inner ℂ (N x) (M y) =
      -Complex.I*inner ℂ (x:Completion V) (Q y)+c*inner ℂ x y)
    · simp
    · intro E y hy; exact Hhom D E x y hx hy
    · intro y z hy hz
      simp only [map_add,inner_add_right]
      linear_combination hy+hz
  · intro x z hx hz
    simp only [map_add,inner_add_left,Completion.coe_add]
    linear_combination hx+hz
lemma stress_stress_smoothCommutator (hc : A.toVertexAlgebra.C2Cofinite)
    (f g : SmoothCircleFunction) (hfr : f.IsReal) (hgr : g.IsReal) (x y : U.smoothEnergySpace) :
    inner ℂ (U.smoothSmear hc A.conformal_mem f.rapid_coefficients x : Completion V)
      (U.smoothSmear hc A.conformal_mem g.rapid_coefficients y : Completion V)-
    inner ℂ (U.smoothSmear hc A.conformal_mem g.rapid_coefficients x : Completion V)
      (U.smoothSmear hc A.conformal_mem f.rapid_coefficients y : Completion V)=
    -Complex.I*inner ℂ (x:Completion V)
      (U.smoothSmear hc A.conformal_mem (f.primaryTransport g 2).rapid_coefficients y : Completion V) +
      (A.centralCharge/12)*(Complex.I*(f.cocycleDensity g).coefficient 0)*inner ℂ (x:Completion V) (y:Completion V) := by
  exact U.smoothSmear_weakCommutator_central_of_algebraic hc A.conformal_mem A.conformal_mem A.conformal_mem
    f.rapid_coefficients g.rapid_coefficients (f.primaryTransport g 2).rapid_coefficients _ _
    (U.stress_stress_weakCommutator hc f g hfr hgr) x y

lemma stress_density_form_derivative (hc : A.toVertexAlgebra.C2Cofinite)
    (φ : PositiveCircleGeometry.SmoothLift) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : Function.Periodic g 1) (t : ℝ) (x y : U.smoothEnergySpace) :
    HasDerivAt (fun s => inner ℂ (U.stressPropagator hc φ.angularStressPath s x)
      (U.smoothSmear hc A.conformal_mem (φ.angularDensity g hg hp 1 s).rapid_coefficients
        (U.stressPropagatorSmooth hc φ.angularStressPath s y) : Completion V))
      ((A.centralCharge/12)*((φ.angularVelocity t).cocycleDensity (φ.angularDensity g hg hp 1 t)).coefficient 0*
        inner ℂ (x:Completion V) (y:Completion V)) t := by
  let f := φ.angularStressPath
  let G := φ.angularDensity g hg hp 1
  have hν : U.IsHermitian 2 A.conformalVector := by simp [IsHermitian,U.pct_conformal]
  obtain ⟨C,hC,p,k,hb⟩ := (U.polynomialEnergyBounds hc A.conformalVector).physical A 2
  have hd := U.smoothSmear_form_derivative hc A.conformal_mem A.conformal_quasiPrimary hν hC.le hb
    (fun s => (G s).rapid_coefficients) (G.timeDerivative t).rapid_coefficients t
    (SmoothCircleFunction.coefficient_real (φ.angularDensity_real g hg hp 1 t)) (G.seminorm_derivative t p)
    (fun s => U.stressPropagatorSmooth hc f s x) (fun s => U.stressPropagatorSmooth hc f s y)
    _ _ (U.stressPropagator_derivative hc f t x) (U.stressPropagator_derivative hc f t y)
    (U.stressPropagatorSmooth_continuous_power hc f k y).continuousAt
  have hw := U.stress_stress_smoothCommutator hc (φ.angularVelocity t) (G t)
    (φ.angularVelocity_real t) (φ.angularDensity_real g hg hp 1 t)
    (U.stressPropagatorSmooth hc f t x) (U.stressPropagatorSmooth hc f t y)
  have he : G.timeDerivative t=(φ.angularVelocity t).primaryTransport (G t) 2 :=
    φ.angularDensity_transport g hg hp 1 t
  rw [he,U.stressPropagatorDerivative_smoothSmear hc f t x,
    U.stressPropagatorDerivative_smoothSmear hc f t y,inner_smul_left,inner_smul_right,Complex.conj_I] at hd
  have hi := (U.stressPropagatorEquiv hc f t).inner_map_map (x:Completion V) (y:Completion V)
  change inner ℂ (U.stressPropagatorSmooth hc f t x : Completion V)
    (U.stressPropagatorSmooth hc f t y : Completion V)=inner ℂ (x:Completion V) (y:Completion V) at hi
  rw [hi] at hw
  convert hd using 1 <;> try rfl
  have hz := congrArg (fun z : ℂ => -Complex.I*z) hw
  simp only [mul_add,mul_sub,neg_mul_neg,← mul_assoc,Complex.I_mul_I,neg_one_mul] at hz
  linear_combination (norm := ring_nf) -hz
  norm_num [Complex.I_sq]
  dsimp [G,f,PositiveCircleGeometry.SmoothLift.angularStressPath,SmoothCircleFamily.toStressPath]
  ring
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Filter MeasureTheory Set
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_StressSmoothness
attribute [-instance] _root_.OAI.StronglyRationalVOA.PositiveCircleGeometry.SmoothLift.instTopologicalSpace _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set

open Filter MeasureTheory Set
open scoped Topology ContDiff

open Filter MeasureTheory Set
open scoped Topology ContDiff

open UniformSpace Filter
open scoped Topology ContDiff
namespace StronglyRationalVOA.CFTTypeVOA
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (A : CFTTypeVOA V)
lemma smearedMap_constant (a : V) (d : ℕ) (ha : A.PolynomialEnergyBound a) (c : ℂ) (v : V) :
    A.smearedMap a d ha (SmoothCircleFunction.constant c).coefficient
      (SmoothCircleFunction.constant c).rapid_coefficients v=c • (A.physicalMode a d 0 v:Completion V) := by
  rw [smearedMap_apply]
  simp only [SmoothCircleFunction.coefficient_constant,ite_smul,zero_smul]
  rw [tsum_eq_single (0:ℤ) (fun n hn => by simp only [ite_eq_right hn]),ite_eq_left rfl]
end StronglyRationalVOA.CFTTypeVOA
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma smooth_constant_bound (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d k : ℕ} (ha : a ∈ A.grade d) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ v, ‖A.physicalMode a d 0 v‖ ≤ C*‖(A.energyShift^k) v‖)
    (x : U.smoothEnergySpace) :
    ‖(U.smoothSmear hc ha (SmoothCircleFunction.constant 1).rapid_coefficients x:Completion V)‖ ≤
      C*‖U.smoothEnergyPower k x‖ := by
  have hM : ∀ v, ‖A.smearedMap a d (U.polynomialEnergyBounds hc a)
      (SmoothCircleFunction.constant 1).coefficient (SmoothCircleFunction.constant 1).rapid_coefficients v‖ ≤
      C*‖(A.energyShift^k) v‖ := by
    intro v
    simpa only [A.smearedMap_constant,one_smul,Completion.norm_coe] using hb v
  rw [U.smoothSmear_eq_extension hc ha _ hM x (U.smoothEnergyPower_graph k x)]
  exact (U.sobolevExtension k _).le_of_opNorm_le (U.sobolevExtension_norm k _ hC hM) _
lemma constant_stress_core (hc : A.toVertexAlgebra.C2Cofinite) (v : V) :
    A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector)
      (SmoothCircleFunction.constant 1).coefficient (SmoothCircleFunction.constant 1).rapid_coefficients v=
      (A.virasoroMode 0 v:Completion V) := by
  rw [A.smearedMap_constant,one_smul]
  rfl
lemma constant_stress_bound (hc : A.toVertexAlgebra.C2Cofinite) (v : V) :
    ‖A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector)
      (SmoothCircleFunction.constant 1).coefficient (SmoothCircleFunction.constant 1).rapid_coefficients v‖ ≤
      (1+A.centralCharge.re)*‖A.energyShift v‖ := by
  rw [U.constant_stress_core hc,Completion.norm_coe]
  simpa only [Int.cast_zero,abs_zero,add_zero,one_pow,mul_one] using U.virasoro_linear_energy 0 v
lemma constant_stress_extension (hc : A.toVertexAlgebra.C2Cofinite) :
    U.sobolevExtension 1 (A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector)
      (SmoothCircleFunction.constant 1).coefficient (SmoothCircleFunction.constant 1).rapid_coefficients)=
    1-U.inverseSobolev 1 := by
  have hb (v : V) := U.constant_stress_bound hc v
  have hb' : ∀ v, ‖A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector)
      (SmoothCircleFunction.constant 1).coefficient (SmoothCircleFunction.constant 1).rapid_coefficients v‖ ≤
      (1+A.centralCharge.re)*‖(A.energyShift^1) v‖ := by simpa only [pow_one] using hb
  apply ContinuousLinearMap.ext
  intro x
  refine Completion.denseRange_coe.induction_on x ?_ ?_
  · exact isClosed_eq (U.sobolevExtension 1 _).continuous (1-U.inverseSobolev 1).continuous
  · intro v
    rw [U.sobolevExtension_coe 1 _ hb',U.constant_stress_core hc]
    change (A.virasoroMode 0 (U.inverseCoreEnergy 1 v):Completion V)=(v:Completion V)-U.inverseSobolev 1 v
    rw [← U.inverseCoreEnergy_coe,← Completion.coe_sub]
    congr 1
    have he := U.energyShift_inverseCoreEnergy 1 v
    change U.inverseCoreEnergy 1 v+A.virasoroMode 0 (U.inverseCoreEnergy 1 v)=v at he
    exact eq_sub_of_add_eq' he
lemma smoothEnergyPower_one_constant_stress (hc : A.toVertexAlgebra.C2Cofinite) (x : U.smoothEnergySpace) :
    U.smoothEnergyPower 1 x=(x:Completion V)+
      (U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.constant 1).rapid_coefficients x:Completion V) := by
  have hb' : ∀ v, ‖A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector)
      (SmoothCircleFunction.constant 1).coefficient (SmoothCircleFunction.constant 1).rapid_coefficients v‖ ≤
      (1+A.centralCharge.re)*‖(A.energyShift^1) v‖ := by simpa only [pow_one] using U.constant_stress_bound hc
  rw [U.smoothSmear_eq_extension hc A.conformal_mem _ hb' x (U.smoothEnergyPower_graph 1 x),
    U.constant_stress_extension hc]
  change _=(x:Completion V)+(U.smoothEnergyPower 1 x-U.inverseSobolev 1 (U.smoothEnergyPower 1 x))
  rw [U.inverseSobolev_smoothEnergyPower]
  abel
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Filter UniformSpace
open scoped Topology ContDiff
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma stress_density_form_covariance (hc : A.toVertexAlgebra.C2Cofinite)
    (φ : PositiveCircleGeometry.SmoothLift) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : Function.Periodic g 1) (hpos : ∀ x, 0 < g x) (t : ℝ) (x y : U.smoothEnergySpace) :
    inner ℂ (U.stressPropagator hc φ.angularStressPath t x)
      (U.smoothSmear hc A.conformal_mem (φ.angularDensity g hg hp 1 t).rapid_coefficients
        (U.stressPropagatorSmooth hc φ.angularStressPath t y) : Completion V)=
    inner ℂ (x:Completion V)
      (U.smoothSmear hc A.conformal_mem (φ.angularDensity g hg hp 1 0).rapid_coefficients y : Completion V)+
      φ.anomalyShift g A.centralCharge t*inner ℂ (x:Completion V) (y:Completion V) := by
  let F : ℝ → ℂ := fun s => inner ℂ (U.stressPropagator hc φ.angularStressPath s x)
      (U.smoothSmear hc A.conformal_mem (φ.angularDensity g hg hp 1 s).rapid_coefficients
        (U.stressPropagatorSmooth hc φ.angularStressPath s y) : Completion V)-
      φ.anomalyShift g A.centralCharge s*inner ℂ (x:Completion V) (y:Completion V)
  have hd (s : ℝ) : HasDerivAt F 0 s := by
    have h := (U.stress_density_form_derivative hc φ g hg hp s x y).sub
      ((φ.anomalyShift_derivative hg hp hpos A.centralCharge s).mul_const
        (inner ℂ (x:Completion V) (y:Completion V)))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | simp only [sub_self]
  have he := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  dsimp only [F] at he
  simp only [φ.anomalyShift_zero,zero_mul,sub_zero,U.stressPropagatorSmooth_zero,
    U.stressPropagator_zero,one_apply_eq_self] at he
  exact sub_eq_iff_eq_add.mp he
lemma stress_density_smooth_covariance (hc : A.toVertexAlgebra.C2Cofinite)
    (φ : PositiveCircleGeometry.SmoothLift) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : Function.Periodic g 1) (hpos : ∀ x, 0 < g x) (t : ℝ) (y : U.smoothEnergySpace) :
    (U.smoothSmear hc A.conformal_mem (φ.angularDensity g hg hp 1 t).rapid_coefficients
      (U.stressPropagatorSmooth hc φ.angularStressPath t y) : Completion V)=
    U.stressPropagator hc φ.angularStressPath t
      (U.smoothSmear hc A.conformal_mem (φ.angularDensity g hg hp 1 0).rapid_coefficients y : Completion V)+
      φ.anomalyShift g A.centralCharge t • U.stressPropagator hc φ.angularStressPath t y := by
  let E := U.stressPropagatorEquiv hc φ.angularStressPath t
  apply E.symm.injective
  apply ext_inner_left ℂ
  intro z
  refine U.smoothEnergySpace_dense.denseRange_val.induction_on z ?_ ?_
  · exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  · intro w
    have h := U.stress_density_form_covariance hc φ g hg hp hpos t w y
    have hi := E.inner_map_map (w:Completion V)
      (E.symm (U.smoothSmear hc A.conformal_mem (φ.angularDensity g hg hp 1 t).rapid_coefficients
        (U.stressPropagatorSmooth hc φ.angularStressPath t y)))
    rw [E.apply_symm_apply] at hi
    change inner ℂ (w:Completion V)
        (E.symm (U.smoothSmear hc A.conformal_mem (φ.angularDensity g hg hp 1 t).rapid_coefficients
          (U.stressPropagatorSmooth hc φ.angularStressPath t y))) =
      inner ℂ (w:Completion V) (E.symm (E (U.smoothSmear hc A.conformal_mem
        (φ.angularDensity g hg hp 1 0).rapid_coefficients y)+φ.anomalyShift g A.centralCharge t • E y))
    rw [map_add,map_smul,E.symm_apply_apply,E.symm_apply_apply,inner_add_right,inner_smul_right]
    exact hi.symm.trans h
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_SmoothEnergyPower
attribute [-instance] _root_.OAI.StronglyRationalVOA.PositiveCircleGeometry.SmoothLift.instTopologicalSpace _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma smoothEnergyPower_zero (x : U.smoothEnergySpace) : U.smoothEnergyPower 0 x=(x:Completion V) := by
  have h := U.inverseSobolev_smoothEnergyPower 0 x
  rwa [U.inverseSobolev_zero,one_apply_eq_self] at h
lemma smoothEnergyPower_constant_stress (hc : A.toVertexAlgebra.C2Cofinite) (r : ℕ) (x : U.smoothEnergySpace) :
    U.smoothEnergyPower r x=
      ((((1:Module.End ℂ U.smoothEnergySpace)+U.smoothSmear hc A.conformal_mem
        (SmoothCircleFunction.constant 1).rapid_coefficients)^r) x:Completion V) := by
  induction r generalizing x with
  | zero => simpa only [pow_zero,Module.End.one_apply] using U.smoothEnergyPower_zero x
  | succ r ih =>
    rw [pow_succ]
    change _=((((1:Module.End ℂ U.smoothEnergySpace)+U.smoothSmear hc A.conformal_mem
        (SmoothCircleFunction.constant 1).rapid_coefficients)^r)
      (x+U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.constant 1).rapid_coefficients x):Completion V)
    rw [← ih]
    apply U.inverseSobolev_injective (r+1)
    rw [U.inverseSobolev_smoothEnergyPower]
    rw [Nat.add_comm r 1,← U.inverseSobolev_mul]
    change _=U.inverseSobolev 1 (U.inverseSobolev r (U.smoothEnergyPower r _))
    rw [U.inverseSobolev_smoothEnergyPower]
    change _=U.inverseSobolev 1 ((x:Completion V)+
      (U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.constant 1).rapid_coefficients x:Completion V))
    rw [← U.smoothEnergyPower_one_constant_stress hc,U.inverseSobolev_smoothEnergyPower]
lemma smoothSmear_smul (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) {f : ℤ → ℂ} (hf : RapidCoefficients f) (c : ℂ) :
    U.smoothSmear hc ha (hf.smul c)=c • U.smoothSmear hc ha hf := by
  obtain ⟨C,hC,p,k,hb⟩ := (U.polynomialEnergyBounds hc a).physical A d
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (U.smoothSmear hc ha (hf.smul c) x:Completion V)=c • (U.smoothSmear hc ha hf x:Completion V)
  rw [U.smoothSmear_eq_normalized hc ha hb,U.smoothSmear_eq_normalized hc ha hb,
    U.normalizedField_smul hc hb]
  rfl
lemma smoothSmear_constant (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (c : ℂ) :
    U.smoothSmear hc ha (SmoothCircleFunction.constant c).rapid_coefficients=
      c • U.smoothSmear hc ha (SmoothCircleFunction.constant 1).rapid_coefficients := by
  have he : (SmoothCircleFunction.constant c).coefficient=
      fun n => c*(SmoothCircleFunction.constant 1).coefficient n := by
    funext n
    simp only [SmoothCircleFunction.coefficient_constant,mul_ite,mul_one,mul_zero]
  conv_lhs => rw [show U.smoothSmear hc ha (SmoothCircleFunction.constant c).rapid_coefficients=
    U.smoothSmear hc ha ((SmoothCircleFunction.constant 1).rapid_coefficients.smul c) from by congr 1]
  exact U.smoothSmear_smul hc ha _ c
lemma primary_density_smooth_covariance (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {k : ℕ} (ha : a ∈ A.grade (k+1)) (hpa : A.IsPrimary a) (hh : U.IsHermitian (k+1) a)
    (φ : PositiveCircleGeometry.SmoothLift) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : Function.Periodic g 1) (t : ℝ) (y : U.smoothEnergySpace) :
    (U.smoothSmear hc ha (φ.angularDensity g hg hp k t).rapid_coefficients
      (U.stressPropagatorSmooth hc φ.angularStressPath t y):Completion V)=
      U.stressPropagator hc φ.angularStressPath t
        (U.smoothSmear hc ha (φ.angularDensity g hg hp k 0).rapid_coefficients y:Completion V) := by
  let G := φ.angularDensity g hg hp k
  apply U.primary_transport_smooth_covariance hc ha φ.angularStressPath (G 0).rapid_coefficients
    (G t).rapid_coefficients t
  intro x y
  apply U.primary_transport_form_constant hc ha hpa hh φ.angularStressPath
    (fun s => (G s).rapid_coefficients) (fun s => (G.timeDerivative s).rapid_coefficients)
    (S := Set.univ) convex_univ (Set.mem_univ 0) ?_ ?_ ?_ (Set.mem_univ t) x y
  · intro s _
    exact SmoothCircleFunction.coefficient_real (φ.angularDensity_real g hg hp k s)
  · intro s _ r
    exact G.seminorm_derivative s r
  · intro s _ r
    have he := (φ.angularVelocity s).hasSum_primaryTransport (G s) (k+1) r
    rw [← φ.angularDensity_transport g hg hp k s] at he
    exact he
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter
open scoped Topology ContDiff
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma primary_positive_local_bound (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {k : ℕ} (ha : a ∈ A.grade (k+1)) (hpa : A.IsPrimary a) (hh : U.IsHermitian (k+1) a)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ v, ‖A.physicalMode a (k+1) 0 v‖ ≤ C*‖(A.energyShift^k) v‖)
    (f : PositiveCircleGeometry.Field (2*Real.pi)) {M : ℝ}
    (hM : |f.frequency-f.stressScalar A.centralCharge.re| ≤ M) (x : U.smoothEnergySpace) :
    ‖(U.smoothSmear hc ha (f.smoothCircle.power k).rapid_coefficients x:Completion V)‖ ≤
      C*(1+M)^k*∑ j ∈ Finset.range (k+1),
        ‖(((U.smoothSmear hc A.conformal_mem f.smoothCircle.rapid_coefficients)^j) x:Completion V)‖ := by
  let e := U.stressPropagatorSmoothEquiv hc f.flattening.angularStressPath 1
  let P := U.smoothSmear hc ha (f.smoothCircle.power k).rapid_coefficients
  let P0 := U.smoothSmear hc ha (SmoothCircleFunction.constant 1).rapid_coefficients
  let T := U.smoothSmear hc A.conformal_mem f.smoothCircle.rapid_coefficients
  let L := U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.constant 1).rapid_coefficients
  have hg (y : U.smoothEnergySpace) : ‖P0 y‖ ≤ C*‖(((1:Module.End ℂ U.smoothEnergySpace)+L)^k) y‖ := by
    have h := U.smooth_constant_bound hc ha hC hb y
    rwa [U.smoothEnergyPower_constant_stress hc] at h
  have hP (y : U.smoothEnergySpace) : e (P y)=(f.frequency:ℂ)^k • P0 (e y) := by
    apply Subtype.ext
    have h := U.primary_density_smooth_covariance hc ha hpa hh f.flattening
      (fun z => f.unitParameter z^k) (f.unitParameter_smooth.pow k)
      (fun z => congrArg (fun w : ℝ => w^k) (f.unitParameter_periodic z)) 1 y
    rw [f.flattening_primary_zero,f.flattening_primary_one,U.smoothSmear_constant] at h
    exact h.symm
  have hT (y : U.smoothEnergySpace) :
      e (T y)=(f.frequency:ℂ) • L (e y)+(f.stressScalar A.centralCharge.re:ℂ) • e y := by
    apply Subtype.ext
    have h := U.stress_density_smooth_covariance hc f.flattening f.unitParameter
      f.unitParameter_smooth f.unitParameter_periodic f.unitParameter_pos 1 y
    rw [f.flattening_angular_zero,f.flattening_angular_one,U.smoothSmear_constant] at h
    have hcR : A.centralCharge=(A.centralCharge.re:ℂ) := Complex.ext rfl (by simp [U.centralCharge_nonneg.1])
    rw [hcR,f.flatteningShift] at h
    change (f.frequency:ℂ) • (L (e y):Completion V)=
      (e (T y):Completion V)+ ((-(f.stressScalar A.centralCharge.re):ℝ):ℂ) • (e y:Completion V) at h
    change (e (T y):Completion V)=(f.frequency:ℂ) • (L (e y):Completion V)+
      (f.stressScalar A.centralCharge.re:ℂ) • (e y:Completion V)
    rw [Complex.ofReal_neg,neg_smul,← sub_eq_add_neg] at h
    exact (eq_sub_iff_add_eq.mp h).symm
  exact LocalCovariance.bound_of_unitary_covariance e P P0 T L k hC hM hg hP hT x
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set MeasureTheory
open scoped ContDiff

open UniformSpace Filter
open scoped Topology ContDiff
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma smoothSmear_sub (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) :
    U.smoothSmear hc ha (hf.sub hg)=U.smoothSmear hc ha hf-U.smoothSmear hc ha hg := by
  obtain ⟨C,hC,p,k,hb⟩ := (U.polynomialEnergyBounds hc a).physical A d
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (U.smoothSmear hc ha (hf.sub hg) x:Completion V)=
    (U.smoothSmear hc ha hf x:Completion V)-(U.smoothSmear hc ha hg x:Completion V)
  rw [U.smoothSmear_eq_normalized hc ha hb,U.smoothSmear_eq_normalized hc ha hb,
    U.smoothSmear_eq_normalized hc ha hb,U.normalizedField_sub hc hb]
  rfl
lemma smoothSmear_add (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) :
    U.smoothSmear hc ha (hf.add hg)=U.smoothSmear hc ha hf+U.smoothSmear hc ha hg := by
  have h := U.smoothSmear_sub hc ha (hf.add hg) hg
  have he : (fun n => (f n+g n)-g n)=f := funext fun _ => add_sub_cancel_right _ _
  rw [show U.smoothSmear hc ha ((hf.add hg).sub hg)=U.smoothSmear hc ha hf from by congr 1] at h
  exact (eq_sub_iff_add_eq.mp h).symm
lemma smoothSmear_add_functions (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (f g : SmoothCircleFunction) :
    U.smoothSmear hc ha (f.add g).rapid_coefficients=
      U.smoothSmear hc ha f.rapid_coefficients+U.smoothSmear hc ha g.rapid_coefficients := by
  have he : (f.add g).coefficient=fun n => f.coefficient n+g.coefficient n := funext (f.coefficient_add g)
  rw [show U.smoothSmear hc ha (f.add g).rapid_coefficients=
    U.smoothSmear hc ha (f.rapid_coefficients.add g.rapid_coefficients) from by congr 1]
  exact U.smoothSmear_add hc ha _ _
lemma smoothSmear_family_continuous (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (f : SmoothCircleFamily) (x : U.smoothEnergySpace) :
    Continuous (fun t => (U.smoothSmear hc ha (f t).rapid_coefficients x:Completion V)) := by
  obtain ⟨C,hC,p,k,hb⟩ := (U.polynomialEnergyBounds hc a).physical A d
  simp_rw [U.smoothSmear_eq_normalized hc ha hb]
  exact (U.normalizedField_continuous hc hC.le hb (fun t => (f t).rapid_coefficients)
    (fun t => f.seminorm_continuous t p)).clm_apply continuous_const
lemma quadratic_stress_powers_continuous (hc : A.toVertexAlgebra.C2Cofinite)
    (g : SmoothCircleFunction) (j : ℕ) (x : U.smoothEnergySpace) :
    Continuous (fun t : ℝ => (((U.smoothSmear hc A.conformal_mem
      (g.quadraticFamily t).rapid_coefficients)^j) x:Completion V)) := by
  have he (t : ℝ) : U.smoothSmear hc A.conformal_mem (g.quadraticFamily t).rapid_coefficients=
      U.smoothSmear hc A.conformal_mem (g.power 2).rapid_coefficients+
      (t:ℂ) • U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.constant 1).rapid_coefficients := by
    change U.smoothSmear hc A.conformal_mem ((g.power 2).add (SmoothCircleFunction.constant (t:ℂ))).rapid_coefficients=_
    rw [U.smoothSmear_add_functions,U.smoothSmear_constant]
  simp_rw [he]
  exact U.smoothEnergySpace.subtypeL.continuous.comp
    (LocalCovariance.continuous_power_affine _ _ j x)
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

lemma primary_square_localEnergy (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hpa : A.IsPrimary a) (hh : U.IsHermitian d a) (hd : 2 ≤ d)
    {g : ℝ → ℝ} (hp : Function.Periodic g (2*Real.pi)) (hs : ContDiff ℝ ∞ g) :
    U.PrimaryLocalEnergyEstimate hc ha ((SmoothCircleFunction.ofRealPeriodic g hp hs).power 2) := by
  obtain ⟨C,hC,hb⟩ := U.optimal_quasiPrimary_energyBound hc ha (hpa 1 (by norm_num)) hh hd
  have hb0 (v : V) : ‖A.physicalMode a d 0 v‖ ≤ C*‖(A.energyShift^(d-1)) v‖ := by
    simpa only [Int.cast_zero,abs_zero,add_zero,one_pow,mul_one] using hb 0 v
  have he : d-1+1=d := by omega
  obtain ⟨M,hM⟩ := (isCompact_Icc : IsCompact (Icc 0 (2*Real.pi))).exists_bound_of_continuousOn hs.continuous.continuousOn
  obtain ⟨N,hN⟩ := (isCompact_Icc : IsCompact (Icc 0 (2*Real.pi))).exists_bound_of_continuousOn
    (contDiff_infty_iff_deriv.mp hs).2.continuous.continuousOn
  let K := (M^2+1)+|A.centralCharge.re|/24*(2*(M^2+1)+4*N^2)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  let F := SmoothCircleFunction.ofRealPeriodic g hp hs
  let B := C*(1+K)^(d-1)
  refine ⟨B,by dsimp only [B]; positivity,?_⟩
  intro x
  let P : ℝ → ℝ := fun t => ‖(U.smoothSmear hc ha
    (SmoothCircleFunction.powerFamily F.quadraticFamily (d-1) t).rapid_coefficients x:Completion V)‖
  let R : ℝ → ℝ := fun t => B*∑ j ∈ Finset.range d,
    ‖(((U.smoothSmear hc A.conformal_mem (F.quadraticFamily t).rapid_coefficients)^j) x:Completion V)‖
  have hP : Continuous P := (U.smoothSmear_family_continuous hc ha
    (SmoothCircleFunction.powerFamily F.quadraticFamily (d-1)) x).norm
  have hR : Continuous R := continuous_const.mul (continuous_finsetSum _
    (fun j _ => (U.quadratic_stress_powers_continuous hc F j x).norm))
  let ε : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  have hε1 (n : ℕ) : ε n ≤ 1 := by
    dsimp only [ε]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hbound (n : ℕ) : P (ε n) ≤ R (ε n) := by
    have hgeom := PositiveCircleGeometry.quadratic_uniform_anomaly hp hs SmoothCircleFunction.period_pos
      hM hN (hε n) (hε1 n) A.centralCharge.re
    have h := U.primary_positive_local_bound hc (he.symm ▸ ha) hpa (he.symm ▸ hh) hC.le
      (by simpa only [he] using hb0) (PositiveCircleGeometry.quadraticField hp hs (hε n)) hgeom x
    rw [PositiveCircleGeometry.quadratic_smoothCircle] at h
    simpa only [P,R,B,K,SmoothCircleFunction.powerFamily,he] using h
  have hlim := le_of_tendsto_of_tendsto (hP.continuousAt.tendsto.comp hεlim)
    (hR.continuousAt.tendsto.comp hεlim) (Eventually.of_forall hbound)
  simpa only [P,R,SmoothCircleFunction.powerFamily,SmoothCircleFunction.quadraticFamily_zero] using hlim
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma primary_realSquare_localEnergy (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a)
    (hh : U.IsHermitian d a) (hd : 2 ≤ d) {f : SmoothCircleFunction} (hf : f.IsReal) :
    U.PrimaryLocalEnergyEstimate hc ha (f.power 2) := by
  have h := U.primary_square_localEnergy hc ha hp hh hd (g := fun t => (f t).re)
    (fun t => congrArg Complex.re (f.periodic t)) (Complex.reCLM.contDiff.comp f.smooth)
  rwa [SmoothCircleFunction.real_reconstruct f hf] at h


end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_Locality
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
open Set MeasureTheory
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
namespace PrimaryTestField
variable {U}
lemma locality (F G : U.PrimaryTestField) (hc : A.toVertexAlgebra.C2Cofinite)
    (h : Disjoint (tsupport F.test) (tsupport G.test)) (i j k l : Bool) :
    ClosedGraphData.entry (F.field hc) (F.closed hc) i j *
      ClosedGraphData.entry (G.field hc) (G.closed hc) k l =
    ClosedGraphData.entry (G.field hc) (G.closed hc) k l *
      ClosedGraphData.entry (F.field hc) (F.closed hc) i j := by
  rcases F.kind with hw | ⟨hw,ha⟩ | ⟨hp,hd,b,hb,he⟩
  · obtain ⟨C,hC,hbound⟩ := U.current_linear_energyBound hc (hw ▸ F.homogeneous)
      F.quasiPrimary (hw ▸ F.hermitian)
    have HB : ∀ n v, ‖A.physicalMode F.state F.weight n v‖ ≤ C*(1+|(n:ℝ)|)^1*‖A.energyShift v‖ := by
      simpa only [hw,pow_one] using hbound
    exact (U.highField_firstOrder_graph_entries_commute hc G.homogeneous F.homogeneous
      G.quasiPrimary F.quasiPrimary G.hermitian F.hermitian hC.le HB
      G.real F.real h.symm k l i j).symm
  · change ClosedGraphData.entry (U.closedSmoothField hc F.state F.weight F.test) _ i j * _ = _
    have H := U.highField_stress_graph_entries_commute hc G.homogeneous G.quasiPrimary
      G.hermitian G.real F.real h.symm k l i j
    simpa only [field,hw,ha] using H.symm
  · change ClosedGraphData.entry (U.closedSmoothField hc F.state F.weight F.test) _ i j * _ = _
    have hs : tsupport (b.power 2) = tsupport F.test := by
      rw [he,SmoothCircleFunction.power_tsupport_eq _ (by omega : 0 < F.weight-1)]
    have H := U.primary_power_graph_locality_of_localEstimate hc F.homogeneous G.homogeneous hp
      G.quasiPrimary F.hermitian G.hermitian hd (SmoothCircleFunction.power_real hb 2) G.real
      (by rwa [hs]) (U.primary_realSquare_localEnergy hc F.homogeneous hp F.hermitian hd hb) i j k l
    simpa only [field,he] using H
end PrimaryTestField
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)


lemma primaryAlgebra_locality (hc : A.toVertexAlgebra.C2Cofinite)
    {O P : Set (AddCircle (2*Real.pi))} (h : Disjoint O P) :
    U.primaryAlgebra hc O ≤ (U.primaryAlgebra hc P).commutant := by
  apply (LocalOperatorAlgebra.generated_le_commutant_iff _ _).mpr
  rintro x ⟨F,hF,i,j,rfl⟩ y ⟨G,hG,k,l,rfl⟩
  have hFG := SmoothCircleFunction.disjoint_lift (h.mono hF hG)
  refine ⟨(F.locality G hc hFG i j k l).symm,?_⟩
  rw [ClosedGraphData.star_entry]
  exact (F.locality G hc hFG i j l k).symm
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction
 

lemma exists_even_power_difference (f χ : SmoothCircleFunction)
    (hf : f.IsReal) (hχ : χ.IsReal)
    (hcut : ∀ t, f t ≠ 0 → χ t = 1) {k : ℕ} (hk : 0 < k) :
    ∃ (C : ℝ) (g : SmoothCircleFunction), 0 < C ∧ g.IsReal ∧
      tsupport g.onCircle ⊆ tsupport χ.onCircle ∧
      ∀ t, f t = (C : ℂ) * (((g.power 2).power k) t - ((χ.power 2).power k) t) := by
  let : Fact (0 < 2*Real.pi) := ⟨period_pos⟩
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn f.smooth.continuous.continuousOn
  have hb (t : ℝ) : ‖f t‖ ≤ M := by
    let s := (AddCircle.equivIco (2*Real.pi) 0 (t : AddCircle (2*Real.pi))).val
    have hs : s ∈ Icc 0 (2*Real.pi) := by
      simpa only [s,mem_Icc,zero_add] using
        (⟨(AddCircle.equivIco (2*Real.pi) 0 (t : AddCircle (2*Real.pi))).property.1,
        (AddCircle.equivIco (2*Real.pi) 0 (t : AddCircle (2*Real.pi))).property.2.le⟩ :
        (AddCircle.equivIco (2*Real.pi) 0 (t : AddCircle (2*Real.pi))).val ∈ Icc 0 (0+2*Real.pi))
    have he : f s = f t := by
      have H := congrArg f.onCircle (AddCircle.coe_equivIco (p := 2*Real.pi) (a := 0) (y := (t : AddCircle (2*Real.pi))))
      simpa only [onCircle_coe] using H
    rw [← he]
    exact hM s hs
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hb 0)
  let C := M+1
  have hC : 0 < C := by dsimp [C]; linarith
  have hp (t : ℝ) : 0 < 1 + (f t).re / C := by
    have hr := (Complex.abs_re_le_norm (f t)).trans (hb t)
    have hh : -(M+1) < (f t).re := by rw [abs_le] at hr; linarith [hr.1]
    have hj : -1 < (f t).re/C := by
      apply (lt_div_iff₀ hC).mpr
      simpa only [neg_one_mul] using hh
    linarith
  let r : ℝ → ℝ := fun t => (1+(f t).re/C) ^ ((2*k : ℕ) : ℝ)⁻¹
  have hrs : ContDiff ℝ ∞ r := by
    apply (contDiff_const.add ((Complex.reCLM.contDiff.comp f.smooth).div_const C)).rpow_const_of_ne
    exact fun t => (hp t).ne'
  have hrp : Function.Periodic r (2*Real.pi) := by
    intro t
    dsimp [r]
    rw [f.periodic t]
  let g := ofRealPeriodic (fun t => (χ t).re * r t)
    (fun t => by dsimp only; rw [χ.periodic t,hrp t])
    ((Complex.reCLM.contDiff.comp χ.smooth).mul hrs)
  have hg (t : ℝ) : g t = χ t * (r t : ℂ) := by
    change (((χ t).re * r t : ℝ) : ℂ) = _
    rw [Complex.ofReal_mul]
    have he := congrArg (fun q : SmoothCircleFunction => q t) (real_reconstruct χ hχ)
    change ((χ t).re : ℂ) = χ t at he
    rw [he]
  refine ⟨C,g,hC,ofRealPeriodic_real _ _ _,?_,?_⟩
  · apply closure_mono
    intro x hx
    induction x using Quotient.inductionOn with | h t =>
    change g t ≠ 0 at hx
    change χ t ≠ 0
    intro ht
    apply hx
    rw [hg,ht,zero_mul]
  · intro t
    have hpw : r t ^ (2*k) = 1+(f t).re/C :=
      Real.rpow_inv_natCast_pow (hp t).le (by omega)
    have hrf : ((f t).re : ℂ) = f t := by
      have he := congrArg (fun q : SmoothCircleFunction => q t) (real_reconstruct f hf)
      exact he
    simp only [power_apply,hg,← pow_mul, mul_pow]
    by_cases hz : f t = 0
    · have hrz : r t = 1 := by simp [r,hz]
      simp [hz,hrz]
    · rw [hcut t hz,one_pow,one_mul]
      have hpw' : (r t : ℂ)^(2*k) = 1+f t/(C : ℂ) := by
        rw [← Complex.ofReal_pow,hpw,Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_div,hrf]
      rw [hpw']
      have hc' : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
      field_simp
      ring
end StronglyRationalVOA.SmoothCircleFunction

open Filter
open scoped Topology

open UniformSpace Filter
open scoped Topology

open UniformSpace Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_SmoothConjugateInner
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
open Set MeasureTheory
open Set
open MeasureTheory Filter

open Set MeasureTheory Filter UniformSpace
open scoped Topology

open Set UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma smoothSmear_scale (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (f : SmoothCircleFunction) (c : ℂ) :
    U.smoothSmear hc ha (f.scale c).rapid_coefficients=c • U.smoothSmear hc ha f.rapid_coefficients := by
  have he : (f.scale c).coefficient=fun n => c*f.coefficient n := funext (f.coefficient_scale c)
  rw [show U.smoothSmear hc ha (f.scale c).rapid_coefficients=
    U.smoothSmear hc ha (f.rapid_coefficients.smul c) from by congr 1]
  exact U.smoothSmear_smul hc ha _ c
lemma smoothSmear_linearCombination (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (f g h : SmoothCircleFunction) (c : ℂ)
    (he : ∀ t, f t=c*(g t-h t)) :
    U.smoothSmear hc ha f.rapid_coefficients =
      c • (U.smoothSmear hc ha g.rapid_coefficients-U.smoothSmear hc ha h.rapid_coefficients) := by
  have hf : f=(g.add (h.scale (-1))).scale c := by
    ext t
    simpa only [SmoothCircleFunction.scale_apply,SmoothCircleFunction.add_apply,neg_one_mul,sub_eq_add_neg] using he t
  rw [hf,U.smoothSmear_scale,U.smoothSmear_add_functions,U.smoothSmear_scale]
  module
 

lemma field_graph_invariant_linearCombination (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (f g h : SmoothCircleFunction) (c : ℂ) (he : ∀ t, f t=c*(g t-h t))
    (Q : Completion V →L[ℂ] Completion V)
    (hQ : ∀ x : U.smoothEnergySpace, Q x ∈ U.smoothEnergySpace)
    (hg : ∀ x y, (x,y) ∈ (U.closedSmoothField hc a d g).graph →
      (Q x,Q y) ∈ (U.closedSmoothField hc a d g).graph)
    (hh : ∀ x y, (x,y) ∈ (U.closedSmoothField hc a d h).graph →
      (Q x,Q y) ∈ (U.closedSmoothField hc a d h).graph)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    (Q x,Q y) ∈ (U.closedSmoothField hc a d f).graph := by
  let R := SymmetricOperator.restricted U.smoothEnergySpace Q hQ
  have hgc := SymmetricOperator.restricted_commutes_of_graph U.smoothEnergySpace
    (U.smoothSmear hc ha g.rapid_coefficients) Q hQ (U.closedSmoothField hc a d g)
    (U.smoothSmear_graph hc ha g.rapid_coefficients) hg
  have hhc := SymmetricOperator.restricted_commutes_of_graph U.smoothEnergySpace
    (U.smoothSmear hc ha h.rapid_coefficients) Q hQ (U.closedSmoothField hc a d h)
    (U.smoothSmear_graph hc ha h.rapid_coefficients) hh
  have hfc : U.smoothSmear hc ha f.rapid_coefficients*R=R*U.smoothSmear hc ha f.rapid_coefficients := by
    rw [U.smoothSmear_linearCombination hc ha f g h c he,smul_mul_assoc,mul_smul_comm,
      sub_mul,mul_sub,hgc,hhc]
  have hce := U.smoothSmear_core hc ha f.rapid_coefficients
  change (SymmetricOperator.onSubmodule U.smoothEnergySpace (U.smoothSmear hc ha f.rapid_coefficients)).closure =
    U.closedSmoothField hc a d f at hce
  rw [← hce] at hxy ⊢
  exact SymmetricOperator.onSubmodule_closure_graph_invariant _ _
    (U.smoothSmear_core_closable hc ha f.rapid_coefficients) Q hQ hfc hxy
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

lemma primary_difference_graph_invariant (hc : A.toVertexAlgebra.C2Cofinite)
    (F G : U.PrimaryTestField) (hs : G.state=F.state) (hw : G.weight=F.weight)
    (f : SmoothCircleFunction) (c : ℂ) (he : ∀ t, f t=c*(F.test t-G.test t))
    {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O)
    (hF : tsupport F.test.onCircle ⊆ O) (hG : tsupport G.test.onCircle ⊆ O)
    (Q : Completion V →L[ℂ] Completion V) (hQ : Q ∈ (U.primaryAlgebra hc O).commutant)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc F.state F.weight f).graph) :
    (Q x,Q y) ∈ (U.closedSmoothField hc F.state F.weight f).graph := by
  obtain ⟨ε,hε,hεF⟩ := F.test.exists_translation_radius hO hF
  obtain ⟨δ,hδ,hδG⟩ := G.test.exists_translation_radius hO hG
  let r : ℕ → ℝ := fun n => min ε δ/((n:ℝ)+1)
  have hr (n : ℕ) : 0 < r n := div_pos (lt_min hε hδ) (by positivity)
  have hrle (n : ℕ) : r n ≤ min ε δ :=
    div_le_self (le_of_lt (lt_min hε hδ)) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hl : Tendsto r atTop (𝓝 0) := by
    simpa only [zero_mul,mul_zero,mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (min ε δ)
  let R (n : ℕ) := SymmetricOperator.smoothConjugate U.conformalHamiltonian
    (U.energyOperator_selfAdjoint (fun d => d)) Q (r n) (hr n)
  have hRn (n : ℕ) : (R n x,R n y) ∈ (U.closedSmoothField hc F.state F.weight f).graph := by
    apply U.field_graph_invariant_linearCombination hc F.homogeneous f F.test G.test c he (R n)
      (fun z => U.smoothConjugate_smooth Q (r n) (hr n) z.property) _ _ hxy
    · intro u v huv
      exact U.smoothConjugate_preserves_primary_graph hc F Q hQ (r n) (hr n)
        (fun t ht => hεF t (ht.trans_le ((hrle n).trans (min_le_left ε δ)))) huv
    · intro u v huv
      have hG' : (u,v) ∈ (G.field hc).graph := by
        simpa only [PrimaryTestField.field,hs,hw] using huv
      have h := U.smoothConjugate_preserves_primary_graph hc G Q hQ (r n) (hr n)
        (fun t ht => hδG t (ht.trans_le ((hrle n).trans (min_le_right ε δ)))) hG'
      simpa only [PrimaryTestField.field,hs,hw] using h
  exact (U.closedSmoothField_isClosed hc F.homogeneous f).mem_of_tendsto
    ((SymmetricOperator.smoothConjugate_strong _ _ Q r hr hl x).prodMk_nhds
      (SymmetricOperator.smoothConjugate_strong _ _ Q r hr hl y)) (Eventually.of_forall hRn)
lemma primary_difference_entry_mem (hc : A.toVertexAlgebra.C2Cofinite)
    (F G : U.PrimaryTestField) (hs : G.state=F.state) (hw : G.weight=F.weight)
    (f : SmoothCircleFunction) (c : ℂ) (he : ∀ t, f t=c*(F.test t-G.test t))
    {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O)
    (hF : tsupport F.test.onCircle ⊆ O) (hG : tsupport G.test.onCircle ⊆ O) (i j : Bool) :
    ClosedGraphData.entry (U.closedSmoothField hc F.state F.weight f)
      (U.closedSmoothField_isClosed hc F.homogeneous f) i j ∈ U.primaryAlgebra hc O := by
  rw [← VonNeumannAlgebra.commutant_commutant (U.primaryAlgebra hc O),VonNeumannAlgebra.mem_commutant_iff]
  intro Q hQ
  apply ClosedGraphData.entry_commutes_of_graph_invariant
  · intro x y hxy
    exact U.primary_difference_graph_invariant hc F G hs hw f c he hO hF hG Q hQ hxy
  · intro x y hxy
    exact U.primary_difference_graph_invariant hc F G hs hw f c he hO hF hG Q.adjoint
      (star_mem hQ) hxy
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set MeasureTheory Filter
open scoped Topology ContDiff

open Set UniformSpace
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

lemma primary_real_entry_mem (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a)
    (hh : U.IsHermitian d a) (hd : 0 < d)
    (f : SmoothCircleFunction) (hf : f.IsReal)
    {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O) (hs : tsupport f.onCircle ⊆ O)
    (i j : Bool) : ClosedGraphData.entry (U.closedSmoothField hc a d f)
      (U.closedSmoothField_isClosed hc ha f) i j ∈ U.primaryAlgebra hc O := by
  have hq : A.IsQuasiPrimary a := hp 1 (by norm_num)
  by_cases hd1 : d=1
  · let F : U.PrimaryTestField := ⟨a,d,ha,hq,hh,f,hf,Or.inl hd1⟩
    exact LocalOperatorAlgebra.subset_generated _ ⟨F,hs,i,j,rfl⟩
  · have hd2 : 2 ≤ d := by omega
    let : Fact (0 < 2*Real.pi) := ⟨SmoothCircleFunction.period_pos⟩
    obtain ⟨χ,hχ,hχ1,hχO⟩ := SmoothCircleFunction.exists_real_cutoff isClosed_closure.isCompact hO hs
    have hcut (t : ℝ) (ht : f t ≠ 0) : χ t=1 := by
      have hm : (t : AddCircle (2*Real.pi)) ∈ Function.support f.onCircle := ht
      simpa only [SmoothCircleFunction.onCircle_coe,Pi.one_apply] using hχ1 (subset_closure hm)
    obtain ⟨C,g,hC,hg,hgχ,he⟩ := f.exists_even_power_difference χ hf hχ hcut (by omega : 0 < d-1)
    let F : U.PrimaryTestField := ⟨a,d,ha,hq,hh,(g.power 2).power (d-1),
      SmoothCircleFunction.power_real (SmoothCircleFunction.power_real hg 2) (d-1),
      Or.inr (Or.inr ⟨hp,hd2,g,hg,rfl⟩)⟩
    let G : U.PrimaryTestField := ⟨a,d,ha,hq,hh,(χ.power 2).power (d-1),
      SmoothCircleFunction.power_real (SmoothCircleFunction.power_real hχ 2) (d-1),
      Or.inr (Or.inr ⟨hp,hd2,χ,hχ,rfl⟩)⟩
    apply U.primary_difference_entry_mem hc F G rfl rfl f (C:ℂ) he hO _ _ i j
    · exact ((g.power 2).power_tsupport_circle_subset (by omega)).trans
        ((g.power_tsupport_circle_subset (by omega)).trans (hgχ.trans hχO))
    · exact ((χ.power 2).power_tsupport_circle_subset (by omega)).trans
        ((χ.power_tsupport_circle_subset (by omega)).trans hχO)
 

lemma primary_real_graph_invariant (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a)
    (hh : U.IsHermitian d a) (hd : 0 < d)
    (f : SmoothCircleFunction) (hf : f.IsReal)
    {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O) (hs : tsupport f.onCircle ⊆ O)
    {Q : Completion V →L[ℂ] Completion V} (hQ : Q ∈ (U.primaryAlgebra hc O).commutant)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    (Q x,Q y) ∈ (U.closedSmoothField hc a d f).graph := by
  apply ClosedGraphData.graph_invariant_of_entry_commutes _ (U.closedSmoothField_isClosed hc ha f) Q _ hxy
  intro i j
  exact ((VonNeumannAlgebra.mem_commutant_iff.mp hQ) _
    (U.primary_real_entry_mem hc ha hp hh hd f hf hO hs i j)).symm
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.SmoothCircleFunction
lemma rePart_real (f : SmoothCircleFunction) : f.rePart.IsReal := ofRealPeriodic_real _ _ _
lemma imPart_real (f : SmoothCircleFunction) : f.imPart.IsReal := ofRealPeriodic_real _ _ _
end StronglyRationalVOA.SmoothCircleFunction
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma field_graph_invariant_add_smul (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (f g h : SmoothCircleFunction) (c : ℂ) (he : ∀ t, f t=g t+c*h t)
    (Q : Completion V →L[ℂ] Completion V)
    (hQ : ∀ x : U.smoothEnergySpace, Q x ∈ U.smoothEnergySpace)
    (hg : ∀ x y, (x,y) ∈ (U.closedSmoothField hc a d g).graph →
      (Q x,Q y) ∈ (U.closedSmoothField hc a d g).graph)
    (hh : ∀ x y, (x,y) ∈ (U.closedSmoothField hc a d h).graph →
      (Q x,Q y) ∈ (U.closedSmoothField hc a d h).graph)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    (Q x,Q y) ∈ (U.closedSmoothField hc a d f).graph := by
  let R := SymmetricOperator.restricted U.smoothEnergySpace Q hQ
  have hgc := SymmetricOperator.restricted_commutes_of_graph U.smoothEnergySpace
    (U.smoothSmear hc ha g.rapid_coefficients) Q hQ (U.closedSmoothField hc a d g)
    (U.smoothSmear_graph hc ha g.rapid_coefficients) hg
  have hhc := SymmetricOperator.restricted_commutes_of_graph U.smoothEnergySpace
    (U.smoothSmear hc ha h.rapid_coefficients) Q hQ (U.closedSmoothField hc a d h)
    (U.smoothSmear_graph hc ha h.rapid_coefficients) hh
  have he' : f=g.add (h.scale c) := SmoothCircleFunction.ext he
  have hfc : U.smoothSmear hc ha f.rapid_coefficients*R=R*U.smoothSmear hc ha f.rapid_coefficients := by
    rw [he',U.smoothSmear_add_functions,U.smoothSmear_scale,add_mul,mul_add,
      smul_mul_assoc,mul_smul_comm,hgc,hhc]
  have hce := U.smoothSmear_core hc ha f.rapid_coefficients
  change (SymmetricOperator.onSubmodule U.smoothEnergySpace (U.smoothSmear hc ha f.rapid_coefficients)).closure =
    U.closedSmoothField hc a d f at hce
  rw [← hce] at hxy ⊢
  exact SymmetricOperator.onSubmodule_closure_graph_invariant _ _
    (U.smoothSmear_core_closable hc ha f.rapid_coefficients) Q hQ hfc hxy
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_SmoothConjugatePrimary
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
open Set MeasureTheory
open Set
open MeasureTheory Filter
open Set MeasureTheory Filter UniformSpace
open Set UniformSpace
open Set UniformSpace Filter
open Set MeasureTheory Filter
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma smoothConjugate_primary_real_graph (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a)
    (hh : U.IsHermitian d a) (hd : 0 < d)
    (f : SmoothCircleFunction) (hf : f.IsReal)
    {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O)
    (Q : Completion V →L[ℂ] Completion V) (hQ : Q ∈ (U.primaryAlgebra hc O).commutant)
    (ε : ℝ) (hε : 0 < ε)
    (hs : ∀ t : ℝ, |t| < ε → tsupport (f.translate t).onCircle ⊆ O)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    (SymmetricOperator.smoothConjugate U.conformalHamiltonian
       (U.energyOperator_selfAdjoint (fun d => d)) Q ε hε x,
     SymmetricOperator.smoothConjugate U.conformalHamiltonian
       (U.energyOperator_selfAdjoint (fun d => d)) Q ε hε y) ∈
       (U.closedSmoothField hc a d f).graph := by
  apply SymmetricOperator.conjugationIntegral_preserves_graph _ _ _ (U.closedSmoothField_isClosed hc ha f)
    Q _ _ _ _ _ _ _ hxy
  intro t ht x y hxy
  have ht' : |t| < ε := by
    have hk : SmoothRotationKernel.kernel ε hε t ≠ 0 := by
      intro h
      exact ht (by simp only [SmoothRotationKernel.jet_zero,h,Complex.ofReal_zero])
    have h := (SmoothRotationKernel.support ε hε).le hk
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using h
  apply U.conjugation_preserves_field_graph hc ha f t Q _ hxy
  intro u v huv
  exact U.primary_real_graph_invariant hc ha hp hh hd (f.translate (-t))
    (SmoothCircleFunction.translate_real hf (-t)) hO
    (hs (-t) (by simpa only [abs_neg] using ht')) hQ huv
 

lemma primary_complex_graph_invariant (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a)
    (hh : U.IsHermitian d a) (hd : 0 < d) (f : SmoothCircleFunction)
    {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O) (hs : tsupport f.onCircle ⊆ O)
    (Q : Completion V →L[ℂ] Completion V) (hQ : Q ∈ (U.primaryAlgebra hc O).commutant)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    (Q x,Q y) ∈ (U.closedSmoothField hc a d f).graph := by
  obtain ⟨ε,hε,hεF⟩ := f.rePart.exists_translation_radius hO (f.rePart_support.trans hs)
  obtain ⟨δ,hδ,hδG⟩ := f.imPart.exists_translation_radius hO (f.imPart_support.trans hs)
  let r : ℕ → ℝ := fun n => min ε δ/((n:ℝ)+1)
  have hr (n : ℕ) : 0 < r n := div_pos (lt_min hε hδ) (by positivity)
  have hrle (n : ℕ) : r n ≤ min ε δ :=
    div_le_self (le_of_lt (lt_min hε hδ)) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hl : Tendsto r atTop (𝓝 0) := by
    simpa only [zero_mul,mul_zero,mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (min ε δ)
  let R (n : ℕ) := SymmetricOperator.smoothConjugate U.conformalHamiltonian
    (U.energyOperator_selfAdjoint (fun d => d)) Q (r n) (hr n)
  have hRn (n : ℕ) : (R n x,R n y) ∈ (U.closedSmoothField hc a d f).graph := by
    apply U.field_graph_invariant_add_smul hc ha f f.rePart f.imPart Complex.I f.rePart_add_imPart (R n)
      (fun z => U.smoothConjugate_smooth Q (r n) (hr n) z.property) _ _ hxy
    · intro u v huv
      exact U.smoothConjugate_primary_real_graph hc ha hp hh hd f.rePart f.rePart_real hO Q hQ (r n) (hr n)
        (fun t ht => hεF t (ht.trans_le ((hrle n).trans (min_le_left ε δ)))) huv
    · intro u v huv
      exact U.smoothConjugate_primary_real_graph hc ha hp hh hd f.imPart f.imPart_real hO Q hQ (r n) (hr n)
        (fun t ht => hδG t (ht.trans_le ((hrle n).trans (min_le_right ε δ)))) huv
  exact (U.closedSmoothField_isClosed hc ha f).mem_of_tendsto
    ((SymmetricOperator.smoothConjugate_strong _ _ Q r hr hl x).prodMk_nhds
      (SymmetricOperator.smoothConjugate_strong _ _ Q r hr hl y)) (Eventually.of_forall hRn)
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma smoothConjugate_primary_complex_graph (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a)
    (hh : U.IsHermitian d a) (hd : 0 < d) (f : SmoothCircleFunction)
    {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O)
    (Q : Completion V →L[ℂ] Completion V) (hQ : Q ∈ (U.primaryAlgebra hc O).commutant)
    (ε : ℝ) (hε : 0 < ε)
    (hs : ∀ t : ℝ, |t| < ε → tsupport (f.translate t).onCircle ⊆ O)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    (SymmetricOperator.smoothConjugate U.conformalHamiltonian
       (U.energyOperator_selfAdjoint (fun d => d)) Q ε hε x,
     SymmetricOperator.smoothConjugate U.conformalHamiltonian
       (U.energyOperator_selfAdjoint (fun d => d)) Q ε hε y) ∈
       (U.closedSmoothField hc a d f).graph := by
  apply SymmetricOperator.conjugationIntegral_preserves_graph _ _ _ (U.closedSmoothField_isClosed hc ha f)
    Q _ _ _ _ _ _ _ hxy
  intro t ht x y hxy
  have ht' : |t| < ε := by
    have hk : SmoothRotationKernel.kernel ε hε t ≠ 0 := by
      intro h
      exact ht (by simp only [SmoothRotationKernel.jet_zero,h,Complex.ofReal_zero])
    have h := (SmoothRotationKernel.support ε hε).le hk
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using h
  apply U.conjugation_preserves_field_graph hc ha f t Q _ hxy
  intro u v huv
  exact U.primary_complex_graph_invariant hc ha hp hh hd (f.translate (-t)) hO
    (hs (-t) (by simpa only [abs_neg] using ht')) Q hQ huv
 

lemma all_primary_graph_invariant (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a)
    (hd : 0 < d) (f : SmoothCircleFunction)
    {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O) (hs : tsupport f.onCircle ⊆ O)
    (Q : Completion V →L[ℂ] Completion V) (hQ : Q ∈ (U.primaryAlgebra hc O).commutant)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    (Q x,Q y) ∈ (U.closedSmoothField hc a d f).graph := by
  obtain ⟨ε,hε,hεF⟩ := f.exists_translation_radius hO hs
  let r : ℕ → ℝ := fun n => ε/((n:ℝ)+1)
  have hr (n : ℕ) : 0 < r n := div_pos hε (by positivity)
  have hrle (n : ℕ) : r n ≤ ε := div_le_self hε.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hl : Tendsto r atTop (𝓝 0) := by
    simpa only [zero_mul,mul_zero,mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ε
  let R (n : ℕ) := SymmetricOperator.smoothConjugate U.conformalHamiltonian
    (U.energyOperator_selfAdjoint (fun d => d)) Q (r n) (hr n)
  have hRn (n : ℕ) : (R n x,R n y) ∈ (U.closedSmoothField hc a d f).graph := by
    apply U.primary_graph_invariant_of_hermitian hc ha hp f (R n)
      (fun z => U.smoothConjugate_smooth Q (r n) (hr n) z.property) _ hxy
    intro b hbd hbp hbh u v huv
    exact U.smoothConjugate_primary_complex_graph hc hbd hbp hbh hd f hO Q hQ (r n) (hr n)
      (fun t ht => hεF t (ht.trans_le (hrle n))) huv
  exact (U.closedSmoothField_isClosed hc ha f).mem_of_tendsto
    ((SymmetricOperator.smoothConjugate_strong _ _ Q r hr hl x).prodMk_nhds
      (SymmetricOperator.smoothConjugate_strong _ _ Q r hr hl y)) (Eventually.of_forall hRn)
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set UniformSpace Filter
open scoped Topology

open UniformSpace Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_LocalNormalMap
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
open Set MeasureTheory
open Set
open MeasureTheory Filter
open Set MeasureTheory Filter UniformSpace
open Set UniformSpace
open Set UniformSpace Filter
open Set MeasureTheory Filter

open Set

open Set

open UniformSpace

open Set UniformSpace Filter
open scoped Topology

open Set UniformSpace

open UniformSpace Set Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)


lemma localState_of_real (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hL : ∀ (O : Set (AddCircle (2*Real.pi))), IsOpen O → ∀ f : SmoothCircleFunction,
      f.IsReal → tsupport f.onCircle ⊆ O → ∀ Q : Completion V →L[ℂ] Completion V,
      Q ∈ (U.primaryAlgebra hc O).commutant → ∀ x y,
      (x,y) ∈ (U.closedSmoothField hc a d f).graph →
      (Q x,Q y) ∈ (U.closedSmoothField hc a d f).graph) : U.LocalState hc a d := by
  intro O hO f hs Q hQ x y hxy
  obtain ⟨ε,hε,hεF⟩ := f.rePart.exists_translation_radius hO (f.rePart_support.trans hs)
  obtain ⟨δ,hδ,hδG⟩ := f.imPart.exists_translation_radius hO (f.imPart_support.trans hs)
  let r : ℕ → ℝ := fun n => min ε δ/((n:ℝ)+1)
  have hr (n : ℕ) : 0 < r n := div_pos (lt_min hε hδ) (by positivity)
  have hrle (n : ℕ) : r n ≤ min ε δ :=
    div_le_self (le_of_lt (lt_min hε hδ)) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hl : Tendsto r atTop (𝓝 0) := by
    simpa only [zero_mul,mul_zero,mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (min ε δ)
  let R (n : ℕ) := SymmetricOperator.smoothConjugate U.conformalHamiltonian
    (U.energyOperator_selfAdjoint (fun d => d)) Q (r n) (hr n)
  have hRn (n : ℕ) : (R n x,R n y) ∈ (U.closedSmoothField hc a d f).graph := by
    apply U.field_graph_invariant_add_smul hc ha f f.rePart f.imPart Complex.I f.rePart_add_imPart (R n)
      (fun z => U.smoothConjugate_smooth Q (r n) (hr n) z.property) _ _ hxy
    · intro u v huv
      exact U.smoothConjugate_realLocal_graph hc ha hL f.rePart f.rePart_real hO Q hQ (r n) (hr n)
        (fun t ht => hεF t (ht.trans_le ((hrle n).trans (min_le_left ε δ)))) huv
    · intro u v huv
      exact U.smoothConjugate_realLocal_graph hc ha hL f.imPart f.imPart_real hO Q hQ (r n) (hr n)
        (fun t ht => hδG t (ht.trans_le ((hrle n).trans (min_le_right ε δ)))) huv
  exact (U.closedSmoothField_isClosed hc ha f).mem_of_tendsto
    ((SymmetricOperator.smoothConjugate_strong _ _ Q r hr hl x).prodMk_nhds
      (SymmetricOperator.smoothConjugate_strong _ _ Q r hr hl y)) (Eventually.of_forall hRn)
lemma stress_localState (hc : A.toVertexAlgebra.C2Cofinite) :
    U.LocalState hc A.conformalVector 2 := by
  apply U.localState_of_real hc A.conformal_mem
  intro O _ f hf hs Q hQ x y hxy
  let F : U.PrimaryTestField :=
    ⟨A.conformalVector,2,A.conformal_mem,A.conformal_quasiPrimary,U.stress_hermitian,
      f,hf,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩
  exact F.commutant_preserves_graph hc hs hQ hxy
lemma primary_localState (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a) (hd : 0 < d) :
    U.LocalState hc a d := by
  intro O hO f hs Q hQ x y hxy
  exact U.all_primary_graph_invariant hc ha hp hd f hO hs Q hQ hxy
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set
open scoped Topology

open UniformSpace Set

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_ObservableScalars
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
open Set MeasureTheory
open Set
open MeasureTheory Filter
open Set MeasureTheory Filter UniformSpace
open Set UniformSpace
open Set UniformSpace Filter
open Set MeasureTheory Filter
open UniformSpace Set Filter
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
def localStateSpace (hc : A.toVertexAlgebra.C2Cofinite) (d : ℕ) : Submodule ℂ V where
  carrier := {a | a ∈ A.grade d ∧ U.LocalState hc a d}
  zero_mem' := ⟨(A.grade d).zero_mem,U.localState_zero hc d⟩
  add_mem' := fun ha hb => ⟨(A.grade d).add_mem ha.1 hb.1,LocalState.add U hc ha.1 hb.1 ha.2 hb.2⟩
  smul_mem' := fun c _ ha => ⟨(A.grade d).smul_mem c ha.1,LocalState.smul U hc ha.1 ha.2 c⟩
lemma LocalState.virasoro_negative (hc : A.toVertexAlgebra.C2Cofinite)
    {b : V} {e : ℕ} (hb : b ∈ A.grade e) (hLb : U.LocalState hc b e)
    (n : ℕ) (hn : 0 < n) : U.LocalState hc (A.virasoroMode (-(n:ℤ)) b) (e+n) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  cases n with
  | zero =>
    simpa only [Nat.cast_one,A.virasoro_neg_one_eq_translation] using LocalState.translation U hc hLb
  | succ n =>
    have H := LocalState.negative_mode U hc n A.conformal_mem hb (U.stress_localState hc) hLb
    convert! H using 1
    · congr 2
      dsimp [CFTTypeVOA.virasoroMode]
      congr 1
      omega
    · omega
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

lemma grade_le_localStateSpace (hc : A.toVertexAlgebra.C2Cofinite) (d : ℕ) :
    A.grade d ≤ U.localStateSpace hc d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hd : d=0
    · subst d
      rw [A.grade_zero]
      exact Submodule.span_le.mpr (by
        intro a ha
        rcases Set.mem_singleton_iff.mp ha with rfl
        exact ⟨by rw [A.grade_zero]; exact Submodule.mem_span_singleton_self _,U.vacuum_localState hc⟩)
    · intro a ha
      obtain ⟨q,hq,hpq,y,hy,rfl⟩ := U.primary_decomposition ha
      apply (U.localStateSpace hc d).add_mem (show q ∈ U.localStateSpace hc d from
        ⟨hq,U.primary_localState hc hq hpq (by omega)⟩)
      have hK : A.lowerVirasoroSpace d ≤ U.localStateSpace hc d := by
        apply iSup_le
        intro n z hz
        obtain ⟨b,hb,rfl⟩ := Submodule.mem_map.mp hz
        have hbLocal := (ih (d-(n.val+1)) (by have := n.isLt; omega) hb).2
        have H := LocalState.virasoro_negative U hc hb hbLocal (n.val+1) (by omega)
        have he : d-(n.val+1)+(n.val+1)=d := by have := n.isLt; omega
        rw [he] at H
        refine ⟨A.virasoro_mem_grade hb _ (by have := n.isLt; omega),?_⟩
        simpa only [Nat.cast_add,Nat.cast_one] using H
      exact hK hy
lemma all_state_localState (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) : U.LocalState hc a d :=
  (U.grade_le_localStateSpace hc d ha).2
lemma all_state_entry_mem (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (f : SmoothCircleFunction)
    {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O) (hs : tsupport f.onCircle ⊆ O)
    (i j : Bool) : ClosedGraphData.entry (U.closedSmoothField hc a d f)
      (U.closedSmoothField_isClosed hc ha f) i j ∈ U.primaryAlgebra hc O := by
  rw [← VonNeumannAlgebra.commutant_commutant (U.primaryAlgebra hc O),VonNeumannAlgebra.mem_commutant_iff]
  intro Q hQ
  apply ClosedGraphData.entry_commutes_of_graph_invariant
  · intro x y hxy
    exact U.all_state_localState hc ha O hO f hs Q hQ x y hxy
  · intro x y hxy
    exact U.all_state_localState hc ha O hO f hs Q.adjoint (star_mem hQ) x y hxy
lemma localAlgebra_eq_primaryAlgebra (hc : A.toVertexAlgebra.C2Cofinite)
    {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O) :
    U.localAlgebra hc O=U.primaryAlgebra hc O := by
  apply le_antisymm _ (U.primaryAlgebra_le_localAlgebra hc O)
  apply LocalOperatorAlgebra.generated_le
  rintro x ⟨a,d,ha,f,hf,i,j,rfl⟩
  exact U.all_state_entry_mem hc ha f hO hf i j
lemma localAlgebra_locality (hc : A.toVertexAlgebra.C2Cofinite)
    {O P : Set (AddCircle (2*Real.pi))} (hO : IsOpen O) (hP : IsOpen P) (h : Disjoint O P) :
    U.localAlgebra hc O ≤ (U.localAlgebra hc P).commutant := by
  rw [U.localAlgebra_eq_primaryAlgebra hc hO,U.localAlgebra_eq_primaryAlgebra hc hP]
  exact U.primaryAlgebra_locality hc h


end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set

open UniformSpace Set
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma smearedMap_character (hc : A.toVertexAlgebra.C2Cofinite)
    (a : V) (d : ℕ) (n : ℤ) (v : V) :
    A.smearedMap a d (U.polynomialEnergyBounds hc a)
      ((SmoothCircleFunction.constant 1).modulate n).coefficient
      ((SmoothCircleFunction.constant 1).modulate n).rapid_coefficients v=
        (A.physicalMode a d n v : Completion V) := by
  rw [A.smearedMap_apply,tsum_eq_single n]
  · simp only [SmoothCircleFunction.modulate_coefficient,sub_self,
      SmoothCircleFunction.coefficient_constant_zero,one_smul]
  · intro j hj
    rw [SmoothCircleFunction.modulate_coefficient,SmoothCircleFunction.coefficient_constant,
      ite_eq_right (sub_ne_zero.mpr hj),zero_smul]
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set
open scoped Topology ContDiff

open UniformSpace Set Filter
open scoped Topology

open UniformSpace Set

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_RotationConjugateCommutant
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup _root_.OAI.StronglyRationalVOA.SmoothCircleLift.instTopologicalSpace _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
open Set MeasureTheory
open Set
open MeasureTheory Filter
open Set MeasureTheory Filter UniformSpace
open Set UniformSpace
open Set UniformSpace Filter
open Set MeasureTheory Filter
open UniformSpace Set Filter

open UniformSpace Set

open UniformSpace Set

open scoped ContDiff

open UniformSpace
open scoped ContDiff

open scoped ContDiff

open UniformSpace
open scoped ContDiff
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma diffeomorphism_primary_smooth (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {k : ℕ} (ha : a ∈ A.grade (k+1)) (hpa : A.IsPrimary a) (hh : U.IsHermitian (k+1) a)
    (F : SmoothCircleLift) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : Function.Periodic g (2*Real.pi)) (y : U.smoothEnergySpace) :
    U.smoothSmear hc ha (F.pushedTest g k hg hp).rapid_coefficients
      (U.diffeomorphismSmoothImplementer hc F y)=
    U.diffeomorphismSmoothImplementer hc F
      (U.smoothSmear hc ha (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients y) := by
  apply Subtype.ext
  have h := U.primary_density_smooth_covariance hc ha hpa hh F.unitLift
    (SmoothCircleLift.unitTest g) (SmoothCircleLift.unitTest_smooth g hg)
    (SmoothCircleLift.unitTest_periodic g hp) 1 y
  rw [F.angularTest_zero,F.angularTest_one] at h
  exact h
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_DiffeomorphismStressSmooth
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup _root_.OAI.StronglyRationalVOA.SmoothCircleLift.instTopologicalSpace _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
open Set MeasureTheory
open Set
open MeasureTheory Filter
open Set MeasureTheory Filter UniformSpace
open Set UniformSpace
open Set UniformSpace Filter
open Set MeasureTheory Filter
open UniformSpace Set Filter
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma diffeomorphism_stress_smooth (hc : A.toVertexAlgebra.C2Cofinite)
    (F : SmoothCircleLift) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : Function.Periodic g (2*Real.pi)) (hpos : ∀ x, 0 < g x) (y : U.smoothEnergySpace) :
    U.smoothSmear hc A.conformal_mem (F.pushedTest g 1 hg hp).rapid_coefficients
      (U.diffeomorphismSmoothImplementer hc F y)=
    U.diffeomorphismSmoothImplementer hc F
      (U.smoothSmear hc A.conformal_mem (SmoothCircleFunction.ofRealPeriodic g hp hg).rapid_coefficients y)+
      F.anomaly g A.centralCharge • U.diffeomorphismSmoothImplementer hc F y := by
  apply Subtype.ext
  have h := U.stress_density_smooth_covariance hc F.unitLift
    (SmoothCircleLift.unitTest g) (SmoothCircleLift.unitTest_smooth g hg)
    (SmoothCircleLift.unitTest_periodic g hp) (fun x => hpos (2*Real.pi*x)) 1 y
  rw [F.angularTest_zero,F.angularTest_one,F.anomaly_endpoint] at h
  exact h
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
open scoped ContDiff

open UniformSpace
open scoped ContDiff

open UniformSpace Set

open UniformSpace

open UniformSpace

open UniformSpace
open scoped ContDiff
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma diffeomorphism_deck_primary (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a) (hh : U.IsHermitian d a)
    (hd : 0 < d) (n : ℤ) (f : SmoothCircleFunction) (hf : f.IsReal) (y : U.smoothEnergySpace) :
    U.smoothSmear hc ha f.rapid_coefficients
      (U.diffeomorphismSmoothImplementer hc (SmoothCircleLift.rotation (n*(2*Real.pi))) y)=
    U.diffeomorphismSmoothImplementer hc (SmoothCircleLift.rotation (n*(2*Real.pi)))
      (U.smoothSmear hc ha f.rapid_coefficients y) := by
  cases d with
  | zero => omega
  | succ k =>
    have h := U.diffeomorphism_primary_smooth hc ha hp hh
      (SmoothCircleLift.rotation (n*(2*Real.pi))) (fun x => (f x).re)
      (Complex.reCLM.contDiff.comp f.smooth) (fun x => congrArg Complex.re (f.periodic x)) y
    simpa only [SmoothCircleLift.pushedTest,SmoothCircleLift.pushDensity_deck n k (g := fun x => (f x).re)
      (fun x => congrArg Complex.re (f.periodic x)),f.real_reconstruct hf] using h
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set

open UniformSpace Filter Set
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_StrongContinuity
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open UniformSpace Filter Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.PositiveCircleGeometry.SmoothLift

lemma identity_path_coefficients (t : ℝ) (n : ℤ) :
    identity.angularStressPath.coefficients t n=0 := by
  change (identity.angularVelocity t).coefficient n=0
  rw [identity_angularVelocity,SmoothCircleFunction.coefficient_zero_constant]
end StronglyRationalVOA.PositiveCircleGeometry.SmoothLift

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_LocalImplementer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open UniformSpace Set
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

lemma stressPropagator_commutes_of_graph (hc : A.toVertexAlgebra.C2Cofinite)
    (f : StressPath) (Q : Completion V →L[ℂ] Completion V)
    (hQ : ∀ t x y, (x,y) ∈ (U.closedSmearedOperator hc A.conformalVector 2
      (f.coefficients t) (f.rapid t)).graph →
      (Q x,Q y) ∈ (U.closedSmearedOperator hc A.conformalVector 2
        (f.coefficients t) (f.rapid t)).graph) (t : ℝ) :
    Q*U.stressPropagator hc f t=U.stressPropagator hc f t*Q := by
  have hp (x y : U.smoothEnergySpace) :
      inner ℂ (U.stressPropagator hc f t x) (Q (U.stressPropagator hc f t y))=
      inner ℂ (x:Completion V) (Q y) := by
    have hd (s : ℝ) : HasDerivAt (fun s =>
        inner ℂ (U.stressPropagator hc f s x) (Q (U.stressPropagator hc f s y))) 0 s := by
      have H := (U.stressPropagator_derivative hc f s x).inner ℂ
        ((Q.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (U.stressPropagator_derivative hc f s y))
      have he := SymmetricOperator.formalAdjoint_graph_pairing
        (SymmetricOperator.selfAdjoint_formal
          (U.stress_closedSmearedOperator_selfAdjoint hc (f.rapid s) (f.real s)))
        (U.smoothSmear_graph hc A.conformal_mem (f.rapid s) (U.stressPropagatorSmooth hc f s x))
        (hQ s _ _ (U.smoothSmear_graph hc A.conformal_mem (f.rapid s)
          (U.stressPropagatorSmooth hc f s y)))
      have hre (v : Completion V) : (Q.restrictScalars ℝ) v=Q v := rfl
      simp only [Function.comp_apply,hre] at H
      change inner ℂ
        (U.smoothSmear hc A.conformal_mem (f.rapid s) (U.stressPropagatorSmooth hc f s x) : Completion V)
        (Q (U.stressPropagator hc f s y))=
        inner ℂ (U.stressPropagator hc f s x)
        (Q (U.smoothSmear hc A.conformal_mem (f.rapid s) (U.stressPropagatorSmooth hc f s y) : Completion V)) at he
      rw [U.stressPropagatorDerivative_smoothSmear hc f s x,
        U.stressPropagatorDerivative_smoothSmear hc f s y,
        map_smul,inner_smul_left,inner_smul_right,Complex.conj_I,he] at H
      convert H using 1
      all_goals try with_reducible_and_instances rfl
      first | rfl | ring
    have he := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
      (fun s => (hd s).deriv) t 0
    simpa only [U.stressPropagator_zero,one_apply_eq_self] using he
  have hall (x y : Completion V) :
      inner ℂ (U.stressPropagator hc f t x) (Q (U.stressPropagator hc f t y))=
      inner ℂ x (Q y) := by
    refine U.smoothEnergySpace_dense.denseRange_val.induction_on x ?_ ?_
    · exact isClosed_eq ((U.stressPropagator hc f t).continuous.inner continuous_const)
        (continuous_id.inner continuous_const)
    · intro x
      refine U.smoothEnergySpace_dense.denseRange_val.induction_on y ?_ ?_
      · exact isClosed_eq (continuous_const.inner (Q.continuous.comp (U.stressPropagator hc f t).continuous))
          (continuous_const.inner Q.continuous)
      · intro y; exact hp x y
  ext y
  apply ext_inner_left ℂ
  intro z
  obtain ⟨x,rfl⟩ := (U.stressPropagatorEquiv hc f t).surjective z
  exact (hall x y).trans ((U.stressPropagatorEquiv hc f t).inner_map_map x (Q y)).symm
 
lemma angularStressPath_local_action (hc : A.toVertexAlgebra.C2Cofinite)
    (φ : PositiveCircleGeometry.SmoothLift)
    {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O)
    (hv : ∀ t, tsupport (φ.angularVelocity t).onCircle ⊆ Oᶜ)
    {Q : Completion V →L[ℂ] Completion V} (hQ : Q ∈ U.localAlgebra hc O)
    (t : ℝ) : Q*U.stressPropagator hc φ.angularStressPath t=
      U.stressPropagator hc φ.angularStressPath t*Q := by
  apply U.stressPropagator_commutes_of_graph hc φ.angularStressPath Q
  intro s x y hxy
  let T : U.PrimaryTestField :=
    ⟨A.conformalVector,2,A.conformal_mem,A.conformal_quasiPrimary,U.stress_hermitian,
      φ.angularVelocity s,φ.angularVelocity_real s,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩
  apply T.commutant_preserves_graph hc (hv s) _ hxy
  apply U.primaryAlgebra_locality hc disjoint_compl_right
  rwa [U.localAlgebra_eq_primaryAlgebra hc hO] at hQ
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
end


