-- Prove2me | Definitions.Def_OAIQ3Vx006
-- name    : OAIQ3Vx006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T06:37:03.218996+00:00
-- url     : https://prove2.me/theorems/b293b13c-41c7-401a-97d0-131dfc67b88c
-- title:
--   Definitions bundle OAIQ3Vx006 of the split of OpenAI, Strongly rational unitary vertex operator algebras and conformal nets
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinimalVertex.main`, carved from OpenAI's openai/math development (OpenAI, *Strongly rational unitary vertex operator algebras and conformal nets*, OpenAI Math Release, September 25, 2026, result family 280, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 88 declarations of OpenAI's Lean: 8 definitions and 80 theorems. The definitions and types are `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.PrimaryLocalEnergyEstimate`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.localNormalMap`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.modulatedSum`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.smoothCoreVector`, `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.smoothEnergyPowerLinear`, `OAI.StronglyRationalVOA.CFTTypeVOA.normalAt`, `OAI.StronglyRationalVOA.SmoothCircleFunction.modulate`, `OAI.StronglyRationalVOA.SmoothCircleFunction.translationTest`.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory/VertexAlgebra, in whole or in part: `VertexAlgebra_CoefficientDifferentiated`, `VertexAlgebra_InverseEnergySelf`, `VertexAlgebra_LocalNormalMap`, `VertexAlgebra_LocalNormalSeries`, `VertexAlgebra_ObservableScalars`, `VertexAlgebra_RegularizerFactorAdd`, `VertexAlgebra_SmoothConjugateInner`, `VertexAlgebra_SmoothConjugatePrimary`, `VertexAlgebra_SmoothEnergyPower`, `VertexAlgebra_SmoothSmearShift`, `VertexAlgebra_StressCutoffNormalized2`, `VertexAlgebra_StressSmoothness`, `VertexAlgebra_SymmetricWeakCommute`.
--
--   **Imports.** It imports the published bundle `Def_VertexAlgebraNet`; the bundles `OAIQ3Vx003` and `OAIQ3Vx004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ3Vx009` and `OAIQ3Vx010`.
-- source:
--   OpenAI, Strongly rational unitary vertex operator algebras and conformal nets, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 280; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strongly-rational-unitary-vertex-operator-algebras-and-conformal-nets-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory/VertexAlgebra at commit adc7f12

import Mathlib
import Definitions.Def_VertexAlgebraNet
import Definitions.Def_OAIQ3Vx003
import Definitions.Def_OAIQ3Vx004

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_InverseEnergySelf
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

namespace StronglyRationalVOA.SmoothCircleFunction


attribute [local instance] OAI.StronglyRationalVOA.SmoothCircleFunction.inverseEnergySelfProductPeriodPos
theorem coefficient_mul (f g : SmoothCircleFunction) (n : ℤ) :
    HasSum (fun m : ℤ => f.coefficient m*g.coefficient (n-m)) ((f.mul g).coefficient n) := by
  have hs : Summable (fourierCoeff f.toContinuousMap) := by
    rw [show fourierCoeff f.toContinuousMap = f.coefficient from funext f.fourierCoeff_toContinuousMap]
    exact (by simpa using f.rapid_coefficients 0 : Summable (fun m => ‖f.coefficient m‖)).of_norm
  simpa only [fourierCoeff_toContinuousMap,← toContinuousMap_mul] using
    FourierAnalysis.hasSum_coefficient_product f.toContinuousMap g.toContinuousMap hs n

end StronglyRationalVOA.SmoothCircleFunction

namespace StronglyRationalVOA.SmoothCircleFunction
open scoped ContDiff



theorem coefficient_deriv_zero (f : SmoothCircleFunction) :
    (f.differentiated 1).coefficient 0 = 0 := by
  rw [coefficient,fourierCoeffOn_eq_integral]
  have H : (∫ t in (0 : ℝ)..2*Real.pi, iteratedDeriv 1 f t) = 0 := by
    rw [iteratedDeriv_one]
    have hd : Differentiable ℝ (f : ℝ → ℂ) := by
      simpa only [iteratedDeriv_zero] using f.differentiable_iteratedDeriv 0
    rw [intervalIntegral.integral_deriv_eq_sub
      (fun x _ => hd x)
      (by simpa only [iteratedDeriv_one] using
        (f.continuous_iteratedDeriv 1).intervalIntegrable 0 (2*Real.pi))]
    have h := f.periodic 0
    simpa only [zero_add,sub_eq_zero] using h
  simp only [neg_zero,fourier_zero,one_smul,differentiated_apply,H,smul_zero]
end StronglyRationalVOA.SmoothCircleFunction

end

end OAI
end

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
namespace StronglyRationalVOA.SmoothCircleFunction
open scoped ContDiff
theorem coefficient_differentiated (f : SmoothCircleFunction) (k : ℕ) (n : ℤ) :
    (f.differentiated k).coefficient n = (Complex.I*(n : ℂ))^k*f.coefficient n := by
  by_cases hn : n = 0
  · subst n
    cases k with
    | zero => change fourierCoeffOn period_pos (iteratedDeriv 0 f) 0 = _; simp [coefficient]
    | succ k =>
      have h := (f.differentiated k).coefficient_deriv_zero
      have hd : (((f.differentiated k).differentiated 1) : ℝ → ℂ) =
          (f.differentiated (k+1) : ℝ → ℂ) := by
        change iteratedDeriv 1 (iteratedDeriv k f) = iteratedDeriv (k+1) f
        rw [iteratedDeriv_one,iteratedDeriv_succ]
      change fourierCoeffOn period_pos _ 0 = 0 at h
      rw [hd] at h
      simpa only [coefficient,Int.cast_zero,mul_zero,zero_pow k.succ_ne_zero,zero_mul] using h
  · exact (f.coefficient_iteratedDeriv k hn).symm

 
theorem differentiated_support (f : SmoothCircleFunction) (k : ℕ) :
    tsupport (f.differentiated k) ⊆ tsupport f := by
  change tsupport (iteratedDeriv k f) ⊆ tsupport f
  induction k with
  | zero => simp only [iteratedDeriv_zero,Set.Subset.rfl]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

 
theorem differentiated_mul_zero {f g : SmoothCircleFunction}
    (hfg : Disjoint (tsupport f) (tsupport g)) (k : ℕ) (t : ℝ) :
    f.differentiated k t * g t = 0 := by
  by_cases ht : t ∈ tsupport f
  · have htg : t ∉ tsupport g := fun hg => Set.disjoint_left.mp hfg ht hg
    rw [image_eq_zero_of_notMem_tsupport htg,mul_zero]
  · have htf : t ∉ tsupport (f.differentiated k) := fun hk => ht (f.differentiated_support k hk)
    rw [image_eq_zero_of_notMem_tsupport htf,zero_mul]

 

theorem hasSum_weighted_convolution_zero {f g : SmoothCircleFunction}
    (hfg : Disjoint (tsupport f) (tsupport g)) (k : ℕ) (n : ℤ) :
    HasSum (fun m : ℤ => (m : ℂ)^k*f.coefficient m*g.coefficient (n-m)) 0 := by
  have H := (f.differentiated k).coefficient_mul g n
  have hz : ((f.differentiated k).mul g).coefficient n = 0 := by
    unfold coefficient
    have he : (((f.differentiated k).mul g) : ℝ → ℂ) = 0 :=
      funext (f.differentiated_mul_zero hfg k)
    rw [he,fourierCoeffOn_eq_integral]
    simp
  rw [hz] at H
  simp only [coefficient_differentiated,mul_pow,mul_assoc] at H
  have HI := H.mul_left ((Complex.I^k)⁻¹)
  simpa only [mul_zero,← mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ Complex.I_ne_zero),one_mul] using HI

end StronglyRationalVOA.SmoothCircleFunction

namespace StronglyRationalVOA.SmoothCircleFunction

 
theorem hasSum_polynomial_convolution_zero {f g : SmoothCircleFunction}
    (hfg : Disjoint (tsupport f) (tsupport g)) (P : Polynomial ℂ) (n : ℤ) :
    HasSum (fun m : ℤ => P.eval (m : ℂ)*f.coefficient m*g.coefficient (n-m)) 0 := by
  classical
  have H : HasSum (fun m : ℤ => ∑ k ∈ P.support,
      P.coeff k * ((m : ℂ)^k*f.coefficient m*g.coefficient (n-m))) 0 := by
    simpa only [mul_zero,Finset.sum_const_zero] using
      (hasSum_sum (s := P.support) (fun k _ =>
        (hasSum_weighted_convolution_zero hfg k n).mul_left (P.coeff k)))
  have he (m : ℤ) : P.eval (m : ℂ)*f.coefficient m*g.coefficient (n-m) =
      ∑ k ∈ P.support, P.coeff k*((m : ℂ)^k*f.coefficient m*g.coefficient (n-m)) := by
    rw [Polynomial.eval_eq_sum,Polynomial.sum_def,Finset.sum_mul,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simpa only [he] using H

 

theorem hasSum_choose_convolution_zero {f g : SmoothCircleFunction}
    (hfg : Disjoint (tsupport f) (tsupport g)) (c : ℂ) (j : ℕ) (n : ℤ) :
    HasSum (fun m : ℤ => Ring.choose ((m : ℂ)+c) j * f.coefficient m*g.coefficient (n-m)) 0 := by
  let P : Polynomial ℂ := Polynomial.C ((j.factorial : ℂ)⁻¹) *
    ((descPochhammer ℤ j).map (Int.castRingHom ℂ)).comp (Polynomial.X+Polynomial.C c)
  have he (m : ℤ) : P.eval (m : ℂ) = Ring.choose ((m : ℂ)+c) j := by
    dsimp only [P]
    rw [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_comp,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_map,
      Ring.choose_eq_smul]
    have hh : Int.castRingHom ℂ = (RingHom.smulOneHom : ℤ →+* ℂ) := by
      ext i
      simp only [RingHom.smulOneHom_apply,zsmul_eq_mul,mul_one]
      rfl
    rw [hh,Polynomial.eval₂_smulOneHom_eq_smeval,smul_eq_mul]
  simpa only [he] using hasSum_polynomial_convolution_zero hfg P n

end StronglyRationalVOA.SmoothCircleFunction

open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_RegularizerFactorAdd
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

open scoped Topology
open UniformSpace

open UniformSpace

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma inverseSobolev_smoothEnergyPower (r : ℕ) (x : U.smoothEnergySpace) :
    U.inverseSobolev r (U.smoothEnergyPower r x) = (x : Completion V) :=
  U.inverseSobolev_on_graph r (U.smoothEnergyPower_graph r x)

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

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

 

def PrimaryLocalEnergyEstimate (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (f : SmoothCircleFunction) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x : U.smoothEnergySpace,
    ‖(U.smoothSmear hc ha (f.power (d-1)).rapid_coefficients x : Completion V)‖ ≤
      C*∑ j ∈ Finset.range d,
        ‖(((U.smoothSmear hc A.conformal_mem f.rapid_coefficients)^j) x : Completion V)‖

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open MeasureTheory Set
open scoped ContDiff

open MeasureTheory Set Filter
open scoped Topology Interval

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

open Filter
open scoped Topology

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma normalizedField_norm (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d p k : ℕ}
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n:ℝ)|)^p*‖(A.energyShift^k) v‖)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    ‖U.normalizedField hc a d k hf‖ ≤ coefficientSeminorm f p*C := by
  exact U.sobolevExtension_norm k _ (mul_nonneg (coefficientSeminorm_nonneg _ _) hC)
    (A.smearedMap_bound (U.polynomialEnergyBounds hc a) hf hb)

lemma normalizedField_sub (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d p k : ℕ}
    {C : ℝ} (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n:ℝ)|)^p*‖(A.energyShift^k) v‖)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) :
    U.normalizedField hc a d k (hf.sub hg)=U.normalizedField hc a d k hf-U.normalizedField hc a d k hg := by
  unfold normalizedField
  rw [← A.smearedMap_sub]
  exact U.sobolevExtension_sub k _ _ (A.smearedMap_bound _ hf hb) (A.smearedMap_bound _ hg hb)

lemma normalizedField_smul (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d p k : ℕ}
    {C : ℝ} (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n:ℝ)|)^p*‖(A.energyShift^k) v‖)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (c : ℂ) :
    U.normalizedField hc a d k (hf.smul c)=c • U.normalizedField hc a d k hf := by
  unfold normalizedField
  rw [A.smearedMap_smul]
  exact U.sobolevExtension_smul k _ (A.smearedMap_bound _ hf hb) c

lemma smoothSmear_eq_normalized (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d p k : ℕ}
    (ha : a ∈ A.grade d) {C : ℝ}
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n:ℝ)|)^p*‖(A.energyShift^k) v‖)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (x : U.smoothEnergySpace) :
    (U.smoothSmear hc ha hf x : Completion V)=U.normalizedField hc a d k hf (U.smoothEnergyPower k x) :=
  U.smoothSmear_eq_extension hc ha hf (A.smearedMap_bound _ hf hb) x (U.smoothEnergyPower_graph k x)

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter
open scoped Topology

open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction
attribute [local instance] OAI.StronglyRationalVOA.SmoothCircleFunction.instFactLtRealOfNatHMulPi
lemma coefficient_add (f g : SmoothCircleFunction) (n : ℤ) :
    (f.add g).coefficient n=f.coefficient n+g.coefficient n := by
  have he : (f.add g).toContinuousMap=f.toContinuousMap+g.toContinuousMap := by
    ext t
    induction t using QuotientAddGroup.induction_on
    rfl
  rw [← fourierCoeff_toContinuousMap,he]
  change fourierCoeff ((f.toContinuousMap : AddCircle (2*Real.pi) → ℂ)+(g.toContinuousMap : AddCircle (2*Real.pi) → ℂ)) n=_
  rw [fourierCoeff.add (f.toContinuousMap.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (g.toContinuousMap.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  simp only [Pi.add_apply,fourierCoeff_toContinuousMap]
lemma coefficient_scale (f : SmoothCircleFunction) (c : ℂ) (n : ℤ) :
    (f.scale c).coefficient n=c*f.coefficient n := by
  exact fourierCoeffOn.const_mul f c n period_pos



end StronglyRationalVOA.SmoothCircleFunction

open UniformSpace Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_StressSmoothness
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

open Filter MeasureTheory Set
open scoped Topology ContDiff

open Filter MeasureTheory Set
open scoped Topology ContDiff

open UniformSpace Filter
open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction
lemma coefficient_constant_zero (c : ℂ) : (constant c).coefficient 0=c := by
  rw [coefficient,fourierCoeffOn_eq_integral]
  simp only [neg_zero,fourier_zero,one_smul,constant_apply,intervalIntegral.integral_const,sub_zero]
  simp only [Complex.real_smul]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
lemma coefficient_zero_constant (n : ℤ) : (constant 0).coefficient n=0 := by
  simp [coefficient,fourierCoeffOn_eq_integral,constant]
lemma coefficient_constant (c : ℂ) (n : ℤ) : (constant c).coefficient n=if n=0 then c else 0 := by
  by_cases hn : n=0
  · subst n; simp [coefficient_constant_zero]
  · rw [ite_eq_right hn]
    have hd := coefficient_differentiated (constant c) 1 n
    have he : (constant c).differentiated 1=constant 0 := by
      apply ext; intro x
      simp only [differentiated_apply,iteratedDeriv_one,constant_apply]
      exact deriv_const x c
    rw [he,coefficient_zero_constant,pow_one] at hd
    exact (mul_eq_zero.mp hd.symm).resolve_left (mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr hn))
end StronglyRationalVOA.SmoothCircleFunction

open Filter UniformSpace
open scoped Topology ContDiff

open UniformSpace Filter
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_SmoothEnergyPower
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

open UniformSpace Filter
open scoped Topology ContDiff

open Set MeasureTheory
open scoped ContDiff

open UniformSpace Filter
open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction
lemma ofRealPeriodic_real (g : ℝ → ℝ) (hp : Function.Periodic g (2*Real.pi)) (hs : ContDiff ℝ ∞ g) :
    (ofRealPeriodic g hp hs).IsReal := fun _ => Complex.conj_ofReal _
end StronglyRationalVOA.SmoothCircleFunction

open UniformSpace Filter Set
open scoped Topology ContDiff

open UniformSpace Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction
lemma tsupport_lift_subset (f : SmoothCircleFunction) :
    tsupport f ⊆ (fun t : ℝ => (t : AddCircle (2*Real.pi))) ⁻¹' tsupport f.onCircle := by
  apply closure_minimal
  · intro t ht
    exact subset_closure ht
  · exact isClosed_closure.preimage (continuous_quotient_mk')
lemma disjoint_lift {f g : SmoothCircleFunction}
    (h : Disjoint (tsupport f.onCircle) (tsupport g.onCircle)) :
    Disjoint (tsupport f) (tsupport g) :=
  (h.preimage _).mono f.tsupport_lift_subset g.tsupport_lift_subset
end StronglyRationalVOA.SmoothCircleFunction

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

open Set UniformSpace Filter
open scoped Topology

open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction


lemma exists_real_cutoff {K O : Set (AddCircle (2*Real.pi))}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ χ : SmoothCircleFunction, χ.IsReal ∧ Set.EqOn χ.onCircle 1 K ∧
      tsupport χ.onCircle ⊆ O := by
  obtain ⟨V,hV,hKV,hVO,hVc⟩ := exists_open_between_and_isCompact_closure hK hO hKO
  obtain ⟨q,hq1,hqc,hqO,hq01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hVc hO hVO
  obtain ⟨ε,hε,hεK⟩ := compact_translation_radius hK hV hKV
  obtain ⟨δ,hδ,hδq⟩ := compact_translation_radius hqc hO hqO
  let r : ℝ := min ε δ/2
  have hr : 0 < r := half_pos (lt_min hε hδ)
  have hrε : r < ε := (half_lt_self (lt_min hε hδ)).trans_le (min_le_left ε δ)
  have hrδ : r < δ := (half_lt_self (lt_min hε hδ)).trans_le (min_le_right ε δ)
  let b : ℝ → ℝ := SmoothRotationKernel.kernel r hr
  have hbc : HasCompactSupport b := by
    change IsCompact (tsupport (SmoothRotationKernel.kernel r hr))
    rw [SmoothRotationKernel.tsupport]
    exact isCompact_closedBall 0 r
  have hbs : ContDiff ℝ ∞ b := (SmoothRotationKernel.bump r hr).contDiff_normed
  let ql : ℝ → ℝ := fun t => q (t : AddCircle (2*Real.pi))
  have hql : Continuous ql := q.continuous.comp continuous_quotient_mk'
  let w : ℝ → ℝ := fun t => ∫ s, b s * ql (t-s)
  have hws : ContDiff ℝ ∞ w := by
    exact hbc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hbs hql.locallyIntegrable
  have hwp : Function.Periodic w (2*Real.pi) := by
    intro t
    apply integral_congr_ae
    filter_upwards [] with s
    change b s * q ((t+2*Real.pi-s : ℝ) : AddCircle (2*Real.pi)) =
      b s * q ((t-s : ℝ) : AddCircle (2*Real.pi))
    congr 2
    rw [show t+2*Real.pi-s=(t-s)+2*Real.pi by ring,AddCircle.coe_add,AddCircle.coe_period,add_zero]
  let χ := ofRealPeriodic w hwp hws
  have hbe {s : ℝ} (hs : b s ≠ 0) : |s| < r := by
    have h : s ∈ Function.support (SmoothRotationKernel.kernel r hr) := hs
    rw [SmoothRotationKernel.support] at h
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using h
  have hcut : Set.EqOn χ.onCircle 1 K := by
    intro x hx
    induction x using Quotient.inductionOn with | h t =>
    change ((w t : ℝ) : ℂ)=1
    have he : w t=1 := by
      calc
        w t = ∫ s, b s := by
          apply integral_congr_ae
          filter_upwards [] with s
          by_cases hs : b s=0
          · simp only [hs,zero_mul]
          · have ht : ((t-s : ℝ) : AddCircle (2*Real.pi)) ∈ V := by
              rw [AddCircle.coe_sub]
              exact hεK (-s) (by simpa only [abs_neg] using (hbe hs).trans hrε) _ hx
            have he := hq1 (subset_closure ht)
            change ql (t-s)=1 at he
            rw [he,mul_one]
        _ = 1 := SmoothRotationKernel.integral r hr
    rw [he,Complex.ofReal_one]
  let S : Set (AddCircle (2*Real.pi)) :=
    (fun z : ℝ × AddCircle (2*Real.pi) => z.2+(z.1 : AddCircle (2*Real.pi))) ''
      (Metric.closedBall 0 r ×ˢ tsupport q)
  have hSc : IsCompact S := ((isCompact_closedBall (0 : ℝ) r).prod hqc).image
    (continuous_snd.add (continuous_quotient_mk'.comp continuous_fst))
  have hSO : S ⊆ O := by
    rintro _ ⟨⟨s,x⟩,⟨hs,hx⟩,rfl⟩
    apply hδq s _ x hx
    exact (by simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero] using hs : |s| ≤ r).trans_lt hrδ
  have hχS : tsupport χ.onCircle ⊆ S := by
    apply closure_minimal _ hSc.isClosed
    intro x hx
    by_contra hnot
    apply hx
    induction x using Quotient.inductionOn with | h t =>
    change ((w t : ℝ) : ℂ)=0
    have hz : w t=0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [] with s
      change b s * ql (t-s)=0
      by_cases hs : b s=0
      · simp only [hs,zero_mul]
      · have ht : ((t-s : ℝ) : AddCircle (2*Real.pi)) ∉ tsupport q := by
          intro ht
          apply hnot
          refine ⟨(s,((t-s : ℝ) : AddCircle (2*Real.pi))),⟨?_,ht⟩,?_⟩
          · simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero] using (hbe hs).le
          · change ((t-s : ℝ) : AddCircle (2*Real.pi))+(s : AddCircle (2*Real.pi))=t
            rw [← AddCircle.coe_add,sub_add_cancel]
        have he := image_eq_zero_of_notMem_tsupport ht
        change ql (t-s)=0 at he
        rw [he,mul_zero]
    rw [hz,Complex.ofReal_zero]
  exact ⟨χ,ofRealPeriodic_real _ _ _,hcut,hχS.trans hSO⟩
end StronglyRationalVOA.SmoothCircleFunction

open Set UniformSpace
open scoped Topology

open Set UniformSpace Filter
open scoped Topology

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

open Set UniformSpace Filter
open scoped Topology

open Set UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA
namespace CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
include U in
lemma physicalMode_sobolev_fixed_bound {a : V} {d k : ℕ} (ha : a ∈ A.grade d)
    {C : ℝ} (hC : 0 ≤ C)
    (n : ℤ) (hb : ∀ v, ‖A.physicalMode a d n v‖ ≤ C*‖(A.energyShift^k) v‖)
    (r : ℕ) (v : V) :
    ‖(A.energyShift^r) (A.physicalMode a d n v)‖ ≤
      C*(1+|(n : ℝ)|)^r*‖(A.energyShift^(k+r)) v‖ := by
  induction r generalizing v with
  | zero => simpa only [pow_zero,Module.End.one_apply,Nat.add_zero,mul_one] using hb v
  | succ r ih =>
    have he : A.energyShift (A.physicalMode a d n v) =
        (-(n : ℂ)) • A.physicalMode a d n v + A.physicalMode a d n (A.energyShift v) :=
      sub_eq_iff_eq_add.mp (A.energyShift_physical_commutator ha n v)
    rw [pow_succ,Module.End.mul_apply,he,map_add,map_smul]
    have hn : ‖-(n : ℂ)‖ = |(n : ℝ)| := by
      rw [norm_neg,← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs]
    have hp : (A.energyShift^(k+r)) (A.energyShift v) =
        (A.energyShift^(k+(r+1))) v := by
      rw [show k+(r+1)=k+r+1 by omega,pow_succ,Module.End.mul_apply]
    have hm := U.energyShift_pow_norm_mono (show k+r ≤ k+(r+1) by omega) v
    calc
      _ ≤ ‖(-(n : ℂ)) • (A.energyShift^r) (A.physicalMode a d n v)‖ +
          ‖(A.energyShift^r) (A.physicalMode a d n (A.energyShift v))‖ := norm_add_le _ _
      _ ≤ |(n : ℝ)| *(C*(1+|(n : ℝ)|)^r*‖(A.energyShift^(k+r)) v‖) +
          C*(1+|(n : ℝ)|)^r*‖(A.energyShift^(k+r)) (A.energyShift v)‖ := by
        rw [norm_smul,hn]
        exact add_le_add (mul_le_mul_of_nonneg_left (ih v) (abs_nonneg _)) (ih _)
      _ ≤ |(n : ℝ)| *(C*(1+|(n : ℝ)|)^r*‖(A.energyShift^(k+(r+1))) v‖) +
          C*(1+|(n : ℝ)|)^r*‖(A.energyShift^(k+(r+1))) v‖ := by
        rw [hp]
        gcongr
      _ = _ := by rw [pow_succ]; ring

include U in
lemma physicalMode_positive_shift_sobolev_bound {a : V} {d k p : ℕ}
    (ha : a ∈ A.grade d) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n:ℝ)|)^p*‖(A.energyShift^k) v‖)
    (R j r : ℕ) (n : ℤ) (v : V) :
    ‖(A.energyShift^r) (A.physicalMode a d n v)‖ ≤
      (C*(1+|((n-(j:ℤ):ℤ):ℝ)|)^(p+R+r)*(1+(j:ℝ))^(p+r)/(1+(j:ℝ))^R)*
        ‖(A.energyShift^(k+R+r)) v‖ := by
  have h := U.physicalMode_sobolev_fixed_bound ha (by positivity)
    n (U.physicalMode_positive_shift_bound ha hC hb R j n) r v
  apply h.trans
  have hnw : 1+|(n:ℝ)| ≤ (1+|((n-(j:ℤ):ℤ):ℝ)|)*(1+(j:ℝ)) := by
    simpa only [Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) j)] using frequency_weight_shift n j
  calc
    _ ≤ (C*(1+|((n-(j:ℤ):ℤ):ℝ)|)^(p+R)*(1+(j:ℝ))^p/(1+(j:ℝ))^R)*
        ((1+|((n-(j:ℤ):ℤ):ℝ)|)*(1+(j:ℝ)))^r*‖(A.energyShift^(k+R+r)) v‖ := by gcongr
    _ = _ := by simp only [mul_pow,pow_add]; ring

lemma weightedSmearedMap_positive_shift_bound {a : V} {d k p : ℕ}
    (ha : a ∈ A.grade d) (he : A.PolynomialEnergyBound a) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n:ℝ)|)^p*‖(A.energyShift^k) v‖)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (R j r : ℕ) (v : V) :
    ‖U.weightedSmearedMap ha he (hf.shift (j:ℤ)) r v‖ ≤
      ((∑' n : ℤ, ‖f n‖*(1+|(n:ℝ)|)^(p+R+r))*C*
        (1+(j:ℝ))^(p+r)/(1+(j:ℝ))^R)*‖(A.energyShift^(k+R+r)) v‖ := by
  rw [weightedSmearedMap_apply]
  have hs := U.summable_norm_sobolevSmear ha he (hf.shift (j:ℤ)) r v
  apply (norm_tsum_le_tsum_norm hs).trans
  have hsum : Summable (fun n : ℤ => ‖f (n-(j:ℤ))‖*(1+|((n-(j:ℤ):ℤ):ℝ)|)^(p+R+r)) :=
    (hf (p+R+r)).comp_injective (Equiv.subRight (j:ℤ)).injective
  calc
    _ ≤ ∑' n : ℤ, (‖f (n-(j:ℤ))‖*(1+|((n-(j:ℤ):ℤ):ℝ)|)^(p+R+r))*
        (C*(1+(j:ℝ))^(p+r)/(1+(j:ℝ))^R*‖(A.energyShift^(k+R+r)) v‖) := by
      apply Summable.tsum_le_tsum _ hs (hsum.mul_right _)
      intro n
      simp only [norm_smul,Completion.norm_coe]
      calc
        _ ≤ ‖f (n-(j:ℤ))‖*((C*(1+|((n-(j:ℤ):ℤ):ℝ)|)^(p+R+r)*
          (1+(j:ℝ))^(p+r)/(1+(j:ℝ))^R)*‖(A.energyShift^(k+R+r)) v‖) :=
            mul_le_mul_of_nonneg_left (U.physicalMode_positive_shift_sobolev_bound ha hC hb R j r n v)
              (norm_nonneg _)
        _ = _ := by ring
    _ = _ := by
      rw [tsum_mul_right]
      have hts := (Equiv.subRight (j:ℤ)).tsum_eq (fun n => ‖f n‖*(1+|(n:ℝ)|)^(p+R+r))
      simp only [Equiv.subRight_apply] at hts
      rw [hts]
      ring

include U in
lemma smearedMap_positive_shift_bound {a : V} {d k p : ℕ}
    (ha : a ∈ A.grade d) (he : A.PolynomialEnergyBound a) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n:ℝ)|)^p*‖(A.energyShift^k) v‖)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (R j : ℕ) (v : V) :
    ‖A.smearedMap a d he (fun n => f (n-(j:ℤ))) (hf.shift (j:ℤ)) v‖ ≤
      ((∑' n : ℤ, ‖f n‖*(1+|(n:ℝ)|)^(p+R))*C*
        (1+(j:ℝ))^p/(1+(j:ℝ))^R)*‖(A.energyShift^(k+R)) v‖ := by
  simpa only [weightedSmearedMap_apply,pow_zero,Module.End.one_apply,Nat.add_zero,smearedMap_apply] using
    U.weightedSmearedMap_positive_shift_bound ha he hC hb hf R j 0 v

lemma smoothEnergyPower_smoothSmear_eq_extension (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d K : ℕ} (ha : a ∈ A.grade d) {f : ℤ → ℂ} (hf : RapidCoefficients f)
    (r : ℕ) {C D : ℝ}
    (hm : ∀ v, ‖A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf v‖ ≤ C*‖(A.energyShift^K) v‖)
    (hn : ∀ v, ‖U.weightedSmearedMap ha (U.polynomialEnergyBounds hc a) hf r v‖ ≤ D*‖(A.energyShift^K) v‖)
    (x : U.smoothEnergySpace) :
    U.smoothEnergyPower r (U.smoothSmear hc ha hf x)=
      U.sobolevExtension K (U.weightedSmearedMap ha (U.polynomialEnergyBounds hc a) hf r)
        (U.smoothEnergyPower K x) := by
  have hg := U.sobolevExtension_graph K _ _ hm hn (U.energyPower r) (U.energyOperator_closed _)
    (U.smearedMap_energyGraph ha (U.polynomialEnergyBounds hc a) hf r) (U.smoothEnergyPower K x)
  rw [← U.smoothSmear_eq_extension hc ha hf hm x (U.smoothEnergyPower_graph K x)] at hg
  exact (U.energyPower r).mem_graph_snd_inj (U.smoothEnergyPower_graph r _) hg rfl

lemma smoothSmear_positive_shift_sobolev_bound (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d k p : ℕ} (ha : a ∈ A.grade d) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n:ℝ)|)^p*‖(A.energyShift^k) v‖)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (R j r : ℕ) (x : U.smoothEnergySpace) :
    ‖U.smoothEnergyPower r (U.smoothSmear hc ha (hf.shift (j:ℤ)) x)‖ ≤
      ((∑' n : ℤ, ‖f n‖*(1+|(n:ℝ)|)^(p+R+r))*C*
        (1+(j:ℝ))^(p+r)/(1+(j:ℝ))^R)*‖U.smoothEnergyPower (k+R+r) x‖ := by
  have hm : ∀ v, ‖A.smearedMap a d (U.polynomialEnergyBounds hc a) _ (hf.shift (j:ℤ)) v‖ ≤
      ((∑' n : ℤ, ‖f n‖*(1+|(n:ℝ)|)^(p+R))*C*
        (1+(j:ℝ))^p/(1+(j:ℝ))^R)*‖(A.energyShift^(k+R+r)) v‖ := by
    intro v
    exact (U.smearedMap_positive_shift_bound ha (U.polynomialEnergyBounds hc a) hC hb hf R j v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : k+R ≤ k+R+r) v) (by positivity))
  have hn := U.weightedSmearedMap_positive_shift_bound ha (U.polynomialEnergyBounds hc a) hC hb hf R j r
  rw [U.smoothEnergyPower_smoothSmear_eq_extension hc ha (hf.shift (j:ℤ)) r hm hn x]
  exact (U.sobolevExtension _ _).le_of_opNorm_le (U.sobolevExtension_norm _ _ (by positivity) hn) _
end CFTTypeVOA.UnitaryStructure
end StronglyRationalVOA

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA
lemma coefficientSeminorm_shift {f : ℤ → ℂ} (hf : RapidCoefficients f) (j : ℤ) (p : ℕ) :
    coefficientSeminorm (fun n => f (n-j)) p ≤ coefficientSeminorm f p*(1+|(j:ℝ)|)^p := by
  have hs : Summable (fun n : ℤ => ‖f (n-j)‖*(1+|((n-j:ℤ):ℝ)|)^p) :=
    (hf p).comp_injective (Equiv.subRight j).injective
  unfold coefficientSeminorm
  calc
    _ ≤ ∑' n : ℤ, (‖f (n-j)‖*(1+|((n-j:ℤ):ℝ)|)^p)*(1+|(j:ℝ)|)^p := by
      apply Summable.tsum_le_tsum _ ((hf.shift j) p) (hs.mul_right _)
      intro n
      calc
        _ ≤ ‖f (n-j)‖*((1+|((n-j:ℤ):ℝ)|)*(1+|(j:ℝ)|))^p := by
          gcongr
          exact frequency_weight_shift n j
        _ = _ := by rw [mul_pow]; ring
    _ = _ := by
      rw [tsum_mul_right]
      have he := (Equiv.subRight j).tsum_eq (fun n => ‖f n‖*(1+|(n:ℝ)|)^p)
      simp only [Equiv.subRight_apply] at he
      rw [he]

end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_SmoothSmearShift
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
namespace StronglyRationalVOA

namespace CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma smoothSmear_shift_bound (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d k p : ℕ} (ha : a ∈ A.grade d) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n:ℝ)|)^p*‖(A.energyShift^k) v‖)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (j : ℤ) (x : U.smoothEnergySpace) :
    ‖(U.smoothSmear hc ha (hf.shift j) x : Completion V)‖ ≤
      (coefficientSeminorm f p*C*(1+|(j:ℝ)|)^p)*‖U.smoothEnergyPower k x‖ := by
  rw [U.smoothSmear_eq_normalized hc ha hb (hf.shift j) x]
  calc
    _ ≤ (coefficientSeminorm (fun n => f (n-j)) p*C)*‖U.smoothEnergyPower k x‖ :=
      (U.normalizedField hc a d k (hf.shift j)).le_of_opNorm_le (U.normalizedField_norm hc hC hb (hf.shift j)) _
    _ ≤ _ := by
      have hs := coefficientSeminorm_shift hf j p
      calc
        _ ≤ (coefficientSeminorm f p*(1+|(j:ℝ)|)^p*C)*‖U.smoothEnergyPower k x‖ := by gcongr
        _ = _ := by ring

 

lemma summable_modulated_product (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g)
    (x : U.smoothEnergySpace) :
    Summable (fun j : ℕ => ((U.smoothSmear hc ha (hg.shift (-(j:ℤ))))
      (U.smoothSmear hc hb (hf.shift (j:ℤ)) x) : Completion V)) := by
  obtain ⟨C,hC,p,k,hA⟩ := (U.polynomialEnergyBounds hc a).physical A d
  obtain ⟨D,hD,q,l,hB⟩ := (U.polynomialEnergyBounds hc b).physical A e
  let R := p+q+k+2
  let K := (coefficientSeminorm g p*C)*(coefficientSeminorm f (q+R+k)*D)*
    ‖U.smoothEnergyPower (l+R+k) x‖
  have hFg := coefficientSeminorm_nonneg g p
  have hFf := coefficientSeminorm_nonneg f (q+R+k)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hs : Summable (fun j : ℕ => K/(1+(j:ℝ))^2) := by
    have ht := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    have ht' : Summable (fun j : ℕ => 1/(1+(j:ℝ))^2) := by
      simpa only [Nat.cast_add,Nat.cast_one,add_comm] using ht
    simpa only [mul_one_div] using ht'.mul_left K
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hs
  intro j
  have ho := U.smoothSmear_shift_bound hc ha hC.le hA hg (-(j:ℤ))
    (U.smoothSmear hc hb (hf.shift (j:ℤ)) x)
  simp only [Int.cast_neg,Int.cast_natCast,abs_neg,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) j)] at ho
  have hi := U.smoothSmear_positive_shift_sobolev_bound hc hb hD.le hB hf R j k x
  change _ ≤ (coefficientSeminorm f (q+R+k)*D*(1+(j:ℝ))^(q+k)/(1+(j:ℝ))^R)*
    ‖U.smoothEnergyPower (l+R+k) x‖ at hi
  apply ho.trans
  calc
    _ ≤ (coefficientSeminorm g p*C*(1+(j:ℝ))^p)*
      ((coefficientSeminorm f (q+R+k)*D*(1+(j:ℝ))^(q+k)/(1+(j:ℝ))^R)*
      ‖U.smoothEnergyPower (l+R+k) x‖) := by gcongr
    _ = _ := by
      dsimp [K,R]
      rw [show p+q+k+2=p+(q+k)+2 by omega]
      simp only [pow_add]
      field_simp
end CFTTypeVOA.UnitaryStructure
end StronglyRationalVOA

namespace StronglyRationalVOA.CFTTypeVOA
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (A : CFTTypeVOA V)
 
def normalAt (a b : V) (d e : ℕ) (k i : ℤ) (v : V) : V :=
  (∑ᶠ j : ℕ, A.physicalMode a d (i-1-j) (A.physicalMode b e (k-i+1+j) v))+
  (∑ᶠ j : ℕ, A.physicalMode b e (k-i-j) (A.physicalMode a d (i+j) v))

lemma normalAt_left_finite (a b : V) (d e : ℕ) (k i : ℤ) (v : V) :
    Function.HasFiniteSupport (fun j : ℕ => A.physicalMode a d (i-1-j)
      (A.physicalMode b e (k-i+1+j) v)) := by
  apply (mode_shift_hasFiniteSupport A.fields b v (k-i+e)).subset
  intro j hj
  change _ ≠ 0 at hj ⊢
  intro hz
  apply hj
  have he : k-i+1+(j:ℤ)+e-1=k-i+e+j := by omega
  simp only [physicalMode,he,hz,map_zero]

lemma normalAt_right_finite (a b : V) (d e : ℕ) (k i : ℤ) (v : V) :
    Function.HasFiniteSupport (fun j : ℕ => A.physicalMode b e (k-i-j)
      (A.physicalMode a d (i+j) v)) := by
  apply (mode_shift_hasFiniteSupport A.fields a v (i+d-1)).subset
  intro j hj
  change _ ≠ 0 at hj ⊢
  intro hz
  apply hj
  have he : i+(j:ℤ)+d-1=i+d-1+j := by omega
  simp only [physicalMode,he,hz,map_zero]

lemma normalAt_step (a b : V) (d e : ℕ) (k i : ℤ) (v : V) :
    A.normalAt a b d e k (i+1) v-A.normalAt a b d e k i v=
      A.physicalMode a d i (A.physicalMode b e (k-i) v)-
      A.physicalMode b e (k-i) (A.physicalMode a d i v) := by
  have hL := finsum_nat_split _ (A.normalAt_left_finite a b d e k (i+1) v) 1
  have hR := finsum_nat_split _ (A.normalAt_right_finite a b d e k i v) 1
  simp only [Finset.sum_range_one,Nat.cast_zero,sub_zero,add_zero,Nat.cast_add,Nat.cast_one] at hL hR
  have hi1 : i+1-1=i := by omega
  have hi2 : k-(i+1)+1=k-i := by omega
  have hj1 (j : ℕ) : i+1-1-(1+(j:ℤ))=i-1-j := by omega
  have hj2 (j : ℕ) : k-(i+1)+1+(1+(j:ℤ))=k-i+1+j := by omega
  have hj3 (j : ℕ) : k-i-(1+(j:ℤ))=k-(i+1)-j := by omega
  have hj4 (j : ℕ) : i+(1+(j:ℤ))=i+1+j := by omega
  simp only [hj1,hj2] at hL
  simp only [hj3,hj4] at hR
  dsimp only [normalAt]
  simp only [hi1,hi2] at hL ⊢
  rw [hL,hR]
  abel

lemma normalAt_vertex_product (a b : V) (d e : ℕ) (k : ℤ) (v : V) :
    A.normalAt a b d e k (1-(d:ℤ)) v=
      A.physicalMode (mode A.fields a (-1) b) (d+e) k v := by
  calc
    _ = ∑ᶠ j : ℕ, (A.physicalMode a d (1-(d:ℤ)-1-j)
        (A.physicalMode b e (k-(1-(d:ℤ))+1+j) v)+
        A.physicalMode b e (k-(1-(d:ℤ))-j) (A.physicalMode a d (1-(d:ℤ)+j) v)) :=
      (finsum_add_distrib (A.normalAt_left_finite a b d e k (1-(d:ℤ)) v)
        (A.normalAt_right_finite a b d e k (1-(d:ℤ)) v)).symm
    _ = _ := by
      rw [physicalMode,A.mode_normal_product]
      apply finsum_congr
      intro j
      simp only [physicalMode,Nat.cast_add]
      have h1 : 1-(d:ℤ)-1-j+d-1 = -1-j := by omega
      have h2 : k-(1-(d:ℤ))+1+j+e-1=k+((d:ℤ)+e)-1+j := by omega
      have h3 : k-(1-(d:ℤ))-j+e-1=k+((d:ℤ)+e)-1-1-j := by omega
      have h4 : 1-(d:ℤ)+j+d-1=j := by omega
      rw [h1,h2,h3,h4]

 

lemma normalAt_choose {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (k i : ℤ) (v : V) :
    A.normalAt a b d e k i v = A.physicalMode (mode A.fields a (-1) b) (d+e) k v+
      ∑ j ∈ Finset.range (d+e), Ring.choose ((i:ℂ)+d-1) (j+1) •
        mode A.fields (mode A.fields a j b) (k+d+e-2-j) v := by
  let P : ℤ → V := fun i => ∑ j ∈ Finset.range (d+e), Ring.choose ((i:ℂ)+d-1) (j+1) •
    mode A.fields (mode A.fields a j b) (k+d+e-2-j) v
  have hP (i : ℤ) : P (i+1)-P i =
      ∑ j ∈ Finset.range (d+e), Ring.choose ((i:ℂ)+d-1) j •
        mode A.fields (mode A.fields a j b) (k+d+e-2-j) v := by
    dsimp only [P]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← sub_smul]
    have hi : ((i+1:ℤ):ℂ)+d-1=((i:ℂ)+d-1)+1 := by push_cast; ring
    rw [hi,Ring.choose_succ_succ,add_sub_cancel_right]
  let F : ℤ → V := fun i => A.normalAt a b d e k i v-P i
  have hF (i : ℤ) : F (i+1)=F i := by
    have h := A.normalAt_step a b d e k i v
    rw [A.physicalMode_commutator_finite ha hb] at h
    have he : i+(k-i)+(d:ℤ)+e-2=k+d+e-2 := by omega
    simp only [he] at h
    have hp := hP i
    dsimp only [F]
    exact (sub_eq_sub_iff_sub_eq_sub.mpr (h.trans hp.symm))
  have hc (i : ℤ) : F i=F 0 := by
    induction i using Int.induction_on with
    | zero => rfl
    | succ n ih => exact (hF n).trans ih
    | pred n ih =>
      have hi : (-(n:ℤ)-1)+1=-(n:ℤ) := by omega
      have hh := hF (-(n:ℤ)-1)
      rw [hi] at hh
      exact hh.symm.trans ih
  have he := (hc i).trans (hc (1-(d:ℤ))).symm
  have hz : P (1-(d:ℤ))=0 := by
    dsimp only [P]
    have hi : ((1-(d:ℤ):ℤ):ℂ)+d-1=0 := by push_cast; ring
    simp only [hi,Ring.choose_zero_succ,zero_smul,Finset.sum_const_zero]
  dsimp only [F] at he
  rw [hz,sub_zero,A.normalAt_vertex_product] at he
  exact sub_eq_iff_eq_add.mp he

end StronglyRationalVOA.CFTTypeVOA

open UniformSpace
namespace StronglyRationalVOA.SmoothCircleFunction
 

lemma hasSum_choose_cutoff {χ f : SmoothCircleFunction}
    (hχ : Disjoint (tsupport (χ.add (constant (-1)))) (tsupport f))
    (c : ℂ) (j : ℕ) (k : ℤ) :
    HasSum (fun i : ℤ => Ring.choose ((i:ℂ)+c) j*χ.coefficient i*f.coefficient (k-i))
      (Ring.choose c j*f.coefficient k) := by
  have H := hasSum_choose_convolution_zero hχ c j k
  have hd : HasSum (fun i : ℤ => if i=0 then Ring.choose c j*f.coefficient k else 0)
      (Ring.choose c j*f.coefficient k) := hasSum_ite_eq 0 _
  have he (i : ℤ) : Ring.choose ((i:ℂ)+c) j*χ.coefficient i*f.coefficient (k-i)=
      Ring.choose ((i:ℂ)+c) j*(χ.add (constant (-1))).coefficient i*f.coefficient (k-i)+
        (if i=0 then Ring.choose c j*f.coefficient k else 0) := by
    rw [coefficient_add,coefficient_constant]
    split_ifs with hi
    · subst i; simp only [Int.cast_zero,zero_add,sub_zero]; ring
    · ring
  simpa only [he,zero_add] using H.add hd
end StronglyRationalVOA.SmoothCircleFunction

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
def smoothCoreVector (v : V) : U.smoothEnergySpace :=
  ⟨(v:Completion V),U.core_le_smoothEnergySpace (HilbertCore.equiv V v).property⟩
lemma smoothEnergyPower_core (r : ℕ) (v : V) :
    U.smoothEnergyPower r (U.smoothCoreVector v)=((A.energyShift^r) v : Completion V) :=
  U.energyPower_coe r v
lemma hasSum_smoothSmear_product_core (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) (y : V) :
    HasSum (fun n : ℤ => g n •
      (U.smoothSmear hc ha hf (U.smoothCoreVector (A.physicalMode b e n y)) : Completion V))
      (U.smoothSmear hc ha hf (U.smoothSmear hc hb hg (U.smoothCoreVector y)) : Completion V) := by
  obtain ⟨C,_,p,k,hA⟩ := (U.polynomialEnergyBounds hc a).physical A d
  have H := (U.normalizedField hc a d k hf).hasSum
    (U.summable_norm_sobolevSmear hb (U.polynomialEnergyBounds hc b) hg k y).of_norm.hasSum
  have he : U.smoothEnergyPower k (U.smoothSmear hc hb hg (U.smoothCoreVector y))=
      ∑' n : ℤ, g n • ((A.energyShift^k) (A.physicalMode b e n y) : Completion V) := by
    apply (U.energyPower k).mem_graph_snd_inj (U.smoothEnergyPower_graph k _)
      (U.smearedMap_energyGraph hb (U.polynomialEnergyBounds hc b) hg k y)
    exact U.smoothSmear_coe hc hb hg y
  rw [U.smoothSmear_eq_normalized hc ha hA hf,he]
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  rw [map_smul,U.smoothSmear_eq_normalized hc ha hA hf,U.smoothEnergyPower_core]

 

lemma hasSum_smoothSmear_product_matrix (hc : A.toVertexAlgebra.C2Cofinite)
    {a b x y : V} {d e D E : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hx : x ∈ A.grade D) (hy : y ∈ A.grade E)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) :
    HasSum (fun n : ℤ => f ((E:ℤ)-D-n)*g n*
      inner ℂ x (A.physicalMode a d ((E:ℤ)-D-n) (A.physicalMode b e n y)))
      (inner ℂ (x : Completion V)
        (U.smoothSmear hc ha hf (U.smoothSmear hc hb hg (U.smoothCoreVector y)) : Completion V)) := by
  have H := (innerSL ℂ (x : Completion V)).hasSum (U.hasSum_smoothSmear_product_core hc ha hb hf hg y)
  convert! H using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  change _ = inner ℂ (x : Completion V) (g n •
    (U.smoothSmear hc ha hf (U.smoothCoreVector (A.physicalMode b e n y)) : Completion V))
  dsimp only [smoothCoreVector]
  rw [inner_smul_right,U.smoothSmear_coe]
  by_cases hn : (E:ℤ) < n
  · have hz : A.physicalMode b e n y=0 := A.mode_eq_zero_of_negative_energy hb hy _ (by omega)
    simp only [hz,map_zero,inner_zero_right,mul_zero]
  · have hgrade : A.physicalMode b e n y ∈ A.grade ((E:ℤ)-n).toNat :=
      A.mode_mem_grade hb hy _ (by omega)
    have he : (((E:ℤ)-n).toNat : ℤ)-D=(E:ℤ)-D-n := by omega
    rw [U.inner_smearedMap_homogeneous ha hx hgrade,he]
    ring
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
include U in
lemma normal_diagonal_polynomial_bound (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (_ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (k : ℤ) (y : V) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ P : ℕ, ∀ r : ℤ,
      ‖A.physicalMode a d r (A.physicalMode b e (k-r) y)‖ ≤ K*(1+|(r:ℝ)|)^P := by
  obtain ⟨C,hC,p,l,hA⟩ := (U.polynomialEnergyBounds hc a).physical A d
  obtain ⟨D,hD,q,m,hB⟩ := (U.polynomialEnergyBounds hc b).physical A e
  refine ⟨C*D*(1+|(k:ℝ)|)^(q+l)*‖(A.energyShift^(m+l)) y‖,by positivity,p+(q+l),?_⟩
  intro r
  have hkr : 1+|((k-r:ℤ):ℝ)| ≤ (1+|(k:ℝ)|)*(1+|(r:ℝ)|) := by
    rw [Int.cast_sub]
    have hab : |(k:ℝ)-(r:ℝ)| ≤ |(k:ℝ)|+|(r:ℝ)| := by
      simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (k:ℝ) (-(r:ℝ))
    nlinarith [mul_nonneg (abs_nonneg (k:ℝ)) (abs_nonneg (r:ℝ))]
  calc
    _ ≤ C*(1+|(r:ℝ)|)^p*‖(A.energyShift^l) (A.physicalMode b e (k-r) y)‖ := hA r _
    _ ≤ C*(1+|(r:ℝ)|)^p*(D*(1+|((k-r:ℤ):ℝ)|)^(q+l)*‖(A.energyShift^(m+l)) y‖) := by
      gcongr
      exact U.physicalMode_sobolev_bound hb hD.le hB l (k-r) y
    _ ≤ C*(1+|(r:ℝ)|)^p*(D*((1+|(k:ℝ)|)*(1+|(r:ℝ)|))^(q+l)*‖(A.energyShift^(m+l)) y‖) := by gcongr
    _ = _ := by simp only [pow_add,mul_pow]; ring

include U in
lemma summable_norm_normal_left (hc : A.toVertexAlgebra.C2Cofinite)
    {a b y : V} {d e E : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hy : y ∈ A.grade E) (D : ℕ)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) :
    Summable (fun q : ℤ × ℕ => ‖(f q.1*g ((E:ℤ)-D-q.1)) •
      (A.physicalMode a d (q.1-1-q.2)
        (A.physicalMode b e ((E:ℤ)-D-q.1+1+q.2) y) : Completion V)‖) := by
  obtain ⟨K,hK,P,hF⟩ := U.normal_diagonal_polynomial_bound hc ha hb ((E:ℤ)-D) y
  have H := summable_norm_normal_triangle (F := fun r : ℤ =>
      (A.physicalMode a d r (A.physicalMode b e ((E:ℤ)-D-r) y) : Completion V))
    hK P D (fun r => by simpa only [Completion.norm_coe] using hF r)
    (fun r hr => by
      have hz : A.physicalMode b e ((E:ℤ)-D-r) y=0 :=
        A.mode_eq_zero_of_negative_energy hb hy _ (by omega)
      simp only [hz,map_zero,Completion.coe_zero]) hf hg ((E:ℤ)-D)
  convert! H using 1
  all_goals try with_reducible_and_instances rfl
  funext q
  have he : (E:ℤ)-D-(q.1-1-q.2)=(E:ℤ)-D-q.1+1+q.2 := by omega
  rw [he]

include U in
lemma summable_norm_normal_right (hc : A.toVertexAlgebra.C2Cofinite)
    {a b y : V} {d e E : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hy : y ∈ A.grade E) (D : ℕ)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) :
    Summable (fun q : ℤ × ℕ => ‖(f q.1*g ((E:ℤ)-D-q.1)) •
      (A.physicalMode b e ((E:ℤ)-D-q.1-q.2)
        (A.physicalMode a d (q.1+q.2) y) : Completion V)‖) := by
  obtain ⟨K,hK,P,hF⟩ := U.normal_diagonal_polynomial_bound hc hb ha ((E:ℤ)-D) y
  have H := summable_norm_normal_triangle (F := fun r : ℤ =>
      (A.physicalMode b e r (A.physicalMode a d ((E:ℤ)-D-r) y) : Completion V))
    hK P D (fun r => by simpa only [Completion.norm_coe] using hF r)
    (fun r hr => by
      have hz : A.physicalMode a d ((E:ℤ)-D-r) y=0 :=
        A.mode_eq_zero_of_negative_energy ha hy _ (by omega)
      simp only [hz,map_zero,Completion.coe_zero]) (hg.shift 1) hf ((E:ℤ)-D+1)
  let σ : ℤ × ℕ ≃ ℤ × ℕ := Equiv.prodCongr (Equiv.subLeft ((E:ℤ)-D+1)) (Equiv.refl ℕ)
  have H' := H.comp_injective σ.injective
  convert! H' using 1
  all_goals try with_reducible_and_instances rfl
  funext q
  simp only [Function.comp_apply,σ,Equiv.prodCongr_apply,Prod.map,Equiv.subLeft_apply,Equiv.refl_apply]
  have h1 : (E:ℤ)-D+1-q.1-1=(E:ℤ)-D-q.1 := by omega
  have h2 : (E:ℤ)-D+1-((E:ℤ)-D+1-q.1)=q.1 := by omega
  have h3 : (E:ℤ)-D-((E:ℤ)-D+1-q.1-1-q.2)=q.1+q.2 := by omega
  rw [h3,h1,h2,mul_comm]
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (A : CFTTypeVOA V)
lemma hasSum_normalAt_completion (a b : V) (d e : ℕ) (k i : ℤ) (v : V) :
    HasSum (fun j : ℕ =>
      (A.physicalMode a d (i-1-j) (A.physicalMode b e (k-i+1+j) v) : Completion V)+
      (A.physicalMode b e (k-i-j) (A.physicalMode a d (i+j) v) : Completion V))
      (A.normalAt a b d e k i v : Completion V) := by
  let Q : V →+ Completion V := (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).toLinearMap.toAddMonoidHom
  have hL := A.normalAt_left_finite a b d e k i v
  have hR := A.normalAt_right_finite a b d e k i v
  have hs (F : ℕ → V) (hF : Function.HasFiniteSupport F) :
      HasSum (fun j => Q (F j)) (Q (∑ᶠ j, F j)) := by
    have hQ : Function.HasFiniteSupport (fun j => Q (F j)) := hF.subset (by
      intro j hj hz
      exact hj (by change Q (F j)=0; rw [hz,map_zero]))
    have H : HasSum (fun j => Q (F j)) (∑' j, Q (F j)) :=
      (summable_of_hasFiniteSupport hQ).hasSum
    rw [tsum_eq_finsum hQ,← Q.map_finsum hF] at H
    exact H
  have hQ (w : V) : Q w=(w : Completion V) := rfl
  simpa only [hQ,normalAt,Completion.coe_add] using (hs _ hL).add (hs _ hR)
end StronglyRationalVOA.CFTTypeVOA

open UniformSpace

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_LocalNormalSeries
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

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma modulated_product_uniform_bound (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g)
    : ∃ m : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (j : ℕ) (x : U.smoothEnergySpace),
      ‖((U.smoothSmear hc ha (hg.shift (-(j:ℤ))))
        (U.smoothSmear hc hb (hf.shift (j:ℤ)) x) : Completion V)‖ ≤
        K/(1+(j:ℝ))^2*‖U.smoothEnergyPower m x‖ := by
  obtain ⟨C,hC,p,k,hA⟩ := (U.polynomialEnergyBounds hc a).physical A d
  obtain ⟨D,hD,q,l,hB⟩ := (U.polynomialEnergyBounds hc b).physical A e
  let R := p+q+k+2
  let K := (coefficientSeminorm g p*C)*(coefficientSeminorm f (q+R+k)*D)
  have hFg := coefficientSeminorm_nonneg g p
  have hFf := coefficientSeminorm_nonneg f (q+R+k)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨l+R+k,K,hK,?_⟩
  intro j x
  have ho := U.smoothSmear_shift_bound hc ha hC.le hA hg (-(j:ℤ))
    (U.smoothSmear hc hb (hf.shift (j:ℤ)) x)
  simp only [Int.cast_neg,Int.cast_natCast,abs_neg,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) j)] at ho
  have hi := U.smoothSmear_positive_shift_sobolev_bound hc hb hD.le hB hf R j k x
  change _ ≤ (coefficientSeminorm f (q+R+k)*D*(1+(j:ℝ))^(q+k)/(1+(j:ℝ))^R)*
    ‖U.smoothEnergyPower (l+R+k) x‖ at hi
  apply ho.trans
  calc
    _ ≤ (coefficientSeminorm g p*C*(1+(j:ℝ))^p)*
      ((coefficientSeminorm f (q+R+k)*D*(1+(j:ℝ))^(q+k)/(1+(j:ℝ))^R)*
      ‖U.smoothEnergyPower (l+R+k) x‖) := by gcongr
    _ = _ := by
      dsimp [K,R]
      rw [show p+q+k+2=p+(q+k)+2 by omega]
      simp only [pow_add]
      field_simp
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
include U in
lemma summable_norm_normal_left_shift (hc : A.toVertexAlgebra.C2Cofinite)
    {a b y : V} {d e E : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hy : y ∈ A.grade E) (D : ℕ) (c : ℤ)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) :
    Summable (fun q : ℤ × ℕ => ‖(f q.1*g ((E:ℤ)-D-q.1)) •
      (A.physicalMode a d (q.1+c-1-q.2)
        (A.physicalMode b e ((E:ℤ)-D-(q.1+c)+1+q.2) y) : Completion V)‖) := by
  have H := U.summable_norm_normal_left hc ha hb hy D (hf.shift c) (hg.shift (-c))
  let σ : ℤ × ℕ ≃ ℤ × ℕ := Equiv.prodCongr (Equiv.addRight c) (Equiv.refl ℕ)
  have H' := H.comp_injective σ.injective
  convert! H' using 1
  all_goals try with_reducible_and_instances rfl
  funext q
  simp only [Function.comp_apply,σ,Equiv.prodCongr_apply,Prod.map,Equiv.coe_addRight,Equiv.refl_apply]
  have h1 : q.1+c-c=q.1 := by omega
  have h2 : (E:ℤ)-D-(q.1+c)-(-c)=(E:ℤ)-D-q.1 := by omega
  rw [h1,h2]
include U in
lemma summable_norm_normal_right_shift (hc : A.toVertexAlgebra.C2Cofinite)
    {a b y : V} {d e E : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hy : y ∈ A.grade E) (D : ℕ) (c : ℤ)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) :
    Summable (fun q : ℤ × ℕ => ‖(f q.1*g ((E:ℤ)-D-q.1)) •
      (A.physicalMode b e ((E:ℤ)-D-(q.1+c)-q.2)
        (A.physicalMode a d (q.1+c+q.2) y) : Completion V)‖) := by
  have H := U.summable_norm_normal_right hc ha hb hy D (hf.shift c) (hg.shift (-c))
  let σ : ℤ × ℕ ≃ ℤ × ℕ := Equiv.prodCongr (Equiv.addRight c) (Equiv.refl ℕ)
  have H' := H.comp_injective σ.injective
  convert! H' using 1
  all_goals try with_reducible_and_instances rfl
  funext q
  simp only [Function.comp_apply,σ,Equiv.prodCongr_apply,Prod.map,Equiv.coe_addRight,Equiv.refl_apply]
  have h1 : q.1+c-c=q.1 := by omega
  have h2 : (E:ℤ)-D-(q.1+c)-(-c)=(E:ℤ)-D-q.1 := by omega
  rw [h1,h2]
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (A : CFTTypeVOA V)
 

lemma hasSum_normalAt_cutoff_shift {a b : V} {d e : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {χ f : SmoothCircleFunction}
    (hχ : Disjoint (tsupport (χ.add (SmoothCircleFunction.constant (-1)))) (tsupport f))
    (k c : ℤ) (v : V) :
    HasSum (fun i : ℤ => (χ.coefficient i*f.coefficient (k-i)) •
      (A.normalAt a b d e k (i+c) v : Completion V))
      (f.coefficient k • (A.normalAt a b d e k c v : Completion V)) := by
  classical
  have hs (s : Finset ℕ) (g : ℕ → V) :
      ((∑ j ∈ s, g j : V) : Completion V)=∑ j ∈ s, (g j : Completion V) :=
    map_sum (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V) g s
  let z : Completion V := A.physicalMode (mode A.fields a (-1) b) (d+e) k v
  let w (j : ℕ) : Completion V := mode A.fields (mode A.fields a j b) (k+d+e-2-j) v
  have H0 : HasSum (fun i : ℤ => (χ.coefficient i*f.coefficient (k-i)) • z)
      (f.coefficient k • z) := by
    have h := (SmoothCircleFunction.hasSum_choose_cutoff hχ 0 0 k).smul_const z
    simpa using h
  have Hj (j : ℕ) := (SmoothCircleFunction.hasSum_choose_cutoff hχ ((c:ℂ)+(d:ℂ)-1) (j+1) k).smul_const (w j)
  have H := H0.add (hasSum_sum (s := Finset.range (d+e)) (fun j _ => Hj j))
  have he (i : ℤ) : (χ.coefficient i*f.coefficient (k-i)) •
      (A.normalAt a b d e k (i+c) v : Completion V)=
      (χ.coefficient i*f.coefficient (k-i)) • z+
        ∑ j ∈ Finset.range (d+e),
          (Ring.choose ((i:ℂ)+((c:ℂ)+(d:ℂ)-1)) (j+1)*χ.coefficient i*f.coefficient (k-i)) • w j := by
    rw [A.normalAt_choose ha hb]
    simp only [Int.cast_add,Completion.coe_add,hs,Completion.coe_smul,smul_add,Finset.smul_sum,smul_smul]
    apply congrArg₂ (· + ·) rfl
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [w]
    congr 1
    rw [show (i:ℂ)+c+d-1=(i:ℂ)+((c:ℂ)+(d:ℂ)-1) by ring]
    ring
  have hz : f.coefficient k • (A.normalAt a b d e k c v : Completion V)=
      f.coefficient k • z+∑ j ∈ Finset.range (d+e),
        (Ring.choose ((c:ℂ)+(d:ℂ)-1) (j+1)*f.coefficient k) • w j := by
    rw [A.normalAt_choose ha hb]
    simp only [Completion.coe_add,hs,Completion.coe_smul,
      smul_add,Finset.smul_sum,smul_smul]
    apply congrArg₂ (· + ·) rfl
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [w]
    rw [mul_comm]
  rw [hz]
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  exact funext he
end StronglyRationalVOA.CFTTypeVOA

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma hasSum_modulated_left_matrix_shift (hc : A.toVertexAlgebra.C2Cofinite)
    {a b x y : V} {d e D E : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hx : x ∈ A.grade D) (hy : y ∈ A.grade E)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) (j : ℕ) (c : ℤ) :
    HasSum (fun i : ℤ => f i*g ((E:ℤ)-D-i)*
      inner ℂ x (A.physicalMode a d (i+c-1-j) (A.physicalMode b e ((E:ℤ)-D-(i+c)+1+j) y)))
      (inner ℂ (x:Completion V) (U.smoothSmear hc ha (hf.shift (c-(j+1:ℤ)))
        (U.smoothSmear hc hb (hg.shift ((j+1:ℤ)-c)) (U.smoothCoreVector y)) : Completion V)) := by
  have H := U.hasSum_smoothSmear_product_matrix hc ha hb hx hy
    (hf.shift (c-(j+1:ℤ))) (hg.shift ((j+1:ℤ)-c))
  have H' := (Equiv.subLeft ((E:ℤ)-D-c+j+1)).hasSum_iff.mpr H
  convert! H' using 1
  all_goals try with_reducible_and_instances rfl
  funext i
  simp only [Function.comp_apply,Equiv.subLeft_apply]
  have h1 : (E:ℤ)-D-((E:ℤ)-D-c+j+1-i)-(c-(j+1))=i := by omega
  have h2 : (E:ℤ)-D-c+j+1-i-((j+1)-c)=(E:ℤ)-D-i := by omega
  have h3 : (E:ℤ)-D-((E:ℤ)-D-c+j+1-i)=i+c-1-j := by omega
  have h4 : (E:ℤ)-D-c+j+1-i=(E:ℤ)-D-(i+c)+1+j := by omega
  rw [h1,h2,h3,h4]

lemma hasSum_modulated_right_matrix_shift (hc : A.toVertexAlgebra.C2Cofinite)
    {a b x y : V} {d e D E : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hx : x ∈ A.grade D) (hy : y ∈ A.grade E)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) (j : ℕ) (c : ℤ) :
    HasSum (fun i : ℤ => f i*g ((E:ℤ)-D-i)*
      inner ℂ x (A.physicalMode b e ((E:ℤ)-D-(i+c)-j) (A.physicalMode a d (i+c+j) y)))
      (inner ℂ (x:Completion V) (U.smoothSmear hc hb (hg.shift (-(j+c:ℤ)))
        (U.smoothSmear hc ha (hf.shift (j+c:ℤ)) (U.smoothCoreVector y)) : Completion V)) := by
  have H := U.hasSum_smoothSmear_product_matrix hc hb ha hx hy (hg.shift (-(j+c:ℤ))) (hf.shift (j+c:ℤ))
  have H' := (Equiv.addRight (j+c:ℤ)).hasSum_iff.mpr H
  convert! H' using 1
  all_goals try with_reducible_and_instances rfl
  funext i
  simp only [Function.comp_apply,Equiv.coe_addRight]
  have h1 : (E:ℤ)-D-(i+(j+c))-(-(j+c))=(E:ℤ)-D-i := by omega
  have h2 : i+(j+c)-(j+c)=i := by omega
  have h3 : (E:ℤ)-D-(i+(j+c))=(E:ℤ)-D-(i+c)-j := by omega
  have h4 : i+(j+c)=i+c+j := by omega
  rw [h1,h2,h3,h4,mul_comm (g _) (f _)]
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

lemma local_normal_series_matrix_shift (hc : A.toVertexAlgebra.C2Cofinite)
    {a b x y : V} {d e D E : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hx : x ∈ A.grade D) (hy : y ∈ A.grade E) (c : ℤ)
    {χ f : SmoothCircleFunction}
    (hχ : Disjoint (tsupport (χ.add (SmoothCircleFunction.constant (-1)))) (tsupport f)) :
    (∑' j : ℕ, inner ℂ (x:Completion V)
      (U.smoothSmear hc ha (χ.rapid_coefficients.shift (c-(j+1:ℤ)))
        (U.smoothSmear hc hb (f.rapid_coefficients.shift ((j+1:ℤ)-c)) (U.smoothCoreVector y)) : Completion V))+
    (∑' j : ℕ, inner ℂ (x:Completion V)
      (U.smoothSmear hc hb (f.rapid_coefficients.shift (-(j+c:ℤ)))
        (U.smoothSmear hc ha (χ.rapid_coefficients.shift (j+c:ℤ)) (U.smoothCoreVector y)) : Completion V)) =
    f.coefficient ((E:ℤ)-D)*inner ℂ x (A.normalAt a b d e ((E:ℤ)-D) c y) := by
  let L (i : ℤ) (j : ℕ) : ℂ := χ.coefficient i*f.coefficient ((E:ℤ)-D-i)*
    inner ℂ x (A.physicalMode a d (i+c-1-j) (A.physicalMode b e ((E:ℤ)-D-(i+c)+1+j) y))
  let R (i : ℤ) (j : ℕ) : ℂ := χ.coefficient i*f.coefficient ((E:ℤ)-D-i)*
    inner ℂ x (A.physicalMode b e ((E:ℤ)-D-(i+c)-j) (A.physicalMode a d (i+c+j) y))
  have hL : Summable (Function.uncurry L) := by
    have H := (innerSL ℂ (x:Completion V)).summable
      (U.summable_norm_normal_left_shift hc ha hb hy D c χ.rapid_coefficients f.rapid_coefficients).of_norm
    simp only [innerSL_apply_apply,inner_smul_right,Completion.inner_coe] at H
    convert! H using 1
    all_goals try with_reducible_and_instances rfl
  have hR : Summable (Function.uncurry R) := by
    have H := (innerSL ℂ (x:Completion V)).summable
      (U.summable_norm_normal_right_shift hc ha hb hy D c χ.rapid_coefficients f.rapid_coefficients).of_norm
    simp only [innerSL_apply_apply,inner_smul_right,Completion.inner_coe] at H
    convert! H using 1
    all_goals try with_reducible_and_instances rfl
  have hLR (i : ℤ) : (∑' j, L i j)+(∑' j, R i j)=
      χ.coefficient i*f.coefficient ((E:ℤ)-D-i)*inner ℂ x (A.normalAt a b d e ((E:ℤ)-D) (i+c) y) := by
    have H := ((innerSL ℂ (x:Completion V)).hasSum
      (A.hasSum_normalAt_completion a b d e ((E:ℤ)-D) (i+c) y)).mul_left
        (χ.coefficient i*f.coefficient ((E:ℤ)-D-i))
    have he : HasSum (fun j => L i j+R i j)
        (χ.coefficient i*f.coefficient ((E:ℤ)-D-i)*inner ℂ x (A.normalAt a b d e ((E:ℤ)-D) (i+c) y)) := by
      simpa only [L,R,innerSL_apply_apply,inner_add_right,Completion.inner_coe,mul_add] using H
    exact (Summable.tsum_add (hL.prod_factor i) (hR.prod_factor i)).symm.trans he.tsum_eq
  have hcut := (innerSL ℂ (x:Completion V)).hasSum (A.hasSum_normalAt_cutoff_shift ha hb hχ ((E:ℤ)-D) c y)
  have hcut' : HasSum (fun i : ℤ => χ.coefficient i*f.coefficient ((E:ℤ)-D-i)*
      inner ℂ x (A.normalAt a b d e ((E:ℤ)-D) (i+c) y))
      (f.coefficient ((E:ℤ)-D)*inner ℂ x (A.normalAt a b d e ((E:ℤ)-D) c y)) := by
    simpa only [innerSL_apply_apply,inner_smul_right,Completion.inner_coe] using hcut
  calc
    _ = (∑' j, ∑' i, L i j)+(∑' j, ∑' i, R i j) := by
      congr 1
      · apply tsum_congr; intro j
        exact (U.hasSum_modulated_left_matrix_shift hc ha hb hx hy χ.rapid_coefficients f.rapid_coefficients j c).tsum_eq.symm
      · apply tsum_congr; intro j
        exact (U.hasSum_modulated_right_matrix_shift hc ha hb hx hy χ.rapid_coefficients f.rapid_coefficients j c).tsum_eq.symm
    _ = (∑' i, ∑' j, L i j)+(∑' i, ∑' j, R i j) := by rw [hL.tsum_comm,hR.tsum_comm]
    _ = ∑' i, ((∑' j, L i j)+(∑' j, R i j)) := (Summable.tsum_add hL.prod hR.prod).symm
    _ = _ := by simp_rw [hLR]; exact hcut'.tsum_eq
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma summable_modulated_product_shift (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g)
    (r : ℤ) (x : U.smoothEnergySpace) :
    Summable (fun j : ℕ => ((U.smoothSmear hc ha (hg.shift (-(j+r:ℤ))))
      (U.smoothSmear hc hb (hf.shift (j+r:ℤ)) x) : Completion V)) := by
  have H := U.summable_modulated_product hc ha hb (hf.shift r) (hg.shift (-r)) x
  convert! H using 1
  all_goals try with_reducible_and_instances rfl
  funext j
  congr 4 <;> funext n <;> congr 1 <;> omega

def modulatedSum (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g)
    (r : ℤ) : U.smoothEnergySpace →ₗ[ℂ] Completion V where
  toFun := fun x => ∑' j : ℕ, ((U.smoothSmear hc ha (hg.shift (-(j+r:ℤ))))
    (U.smoothSmear hc hb (hf.shift (j+r:ℤ)) x) : Completion V)
  map_add' := by
    intro x y
    simp only [map_add,Submodule.coe_add]
    exact Summable.tsum_add (U.summable_modulated_product_shift hc ha hb hf hg r x)
      (U.summable_modulated_product_shift hc ha hb hf hg r y)
  map_smul' := by
    intro c x
    simp only [map_smul,Submodule.coe_smul]
    exact tsum_const_smul'' _

lemma modulatedSum_apply (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g)
    (r : ℤ) (x : U.smoothEnergySpace) :
    U.modulatedSum hc ha hb hf hg r x = ∑' j : ℕ,
      ((U.smoothSmear hc ha (hg.shift (-(j+r:ℤ))))
        (U.smoothSmear hc hb (hf.shift (j+r:ℤ)) x) : Completion V) := rfl
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
def smoothEnergyPowerLinear (r : ℕ) : U.smoothEnergySpace →ₗ[ℂ] Completion V :=
  (U.energyPower r).toFun.comp
    (Submodule.inclusion (iInf_le (fun k => (U.energyPower k).domain) r))
lemma smoothEnergyPowerLinear_apply (r : ℕ) (x : U.smoothEnergySpace) :
    U.smoothEnergyPowerLinear r x=U.smoothEnergyPower r x := rfl
lemma smoothEnergyPowerLinear_dense (r : ℕ) : DenseRange (U.smoothEnergyPowerLinear r) := by
  apply Completion.denseRange_coe.mono
  rintro z ⟨v,rfl⟩
  refine ⟨U.smoothCoreVector (U.inverseCoreEnergy r v),?_⟩
  rw [U.smoothEnergyPowerLinear_apply,U.smoothEnergyPower_core,U.energyShift_inverseCoreEnergy]
lemma smoothEnergyPower_inverse_add (r s : ℕ) (x : U.smoothEnergySpace) :
    U.inverseSobolev s (U.smoothEnergyPower (r+s) x)=U.smoothEnergyPower r x := by
  apply U.inverseSobolev_injective r
  change (U.inverseSobolev r*U.inverseSobolev s) (U.smoothEnergyPower (r+s) x)=_
  rw [U.inverseSobolev_mul,U.inverseSobolev_smoothEnergyPower,U.inverseSobolev_smoothEnergyPower]
lemma smoothEnergyPower_norm_add (r s : ℕ) (x : U.smoothEnergySpace) :
    ‖U.smoothEnergyPower r x‖ ≤ ‖U.inverseSobolev s‖*‖U.smoothEnergyPower (r+s) x‖ := by
  rw [← U.smoothEnergyPower_inverse_add r s x]
  exact (U.inverseSobolev s).le_opNorm _
 

lemma smooth_linear_eq_of_core (L M : U.smoothEnergySpace →ₗ[ℂ] Completion V)
    (hL : ∃ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖L x‖ ≤ C*‖U.smoothEnergyPower r x‖)
    (hM : ∃ s : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ x, ‖M x‖ ≤ D*‖U.smoothEnergyPower s x‖)
    (he : ∀ v : V, L (U.smoothCoreVector v)=M (U.smoothCoreVector v)) : L=M := by
  obtain ⟨r,C,hC,hL⟩ := hL
  obtain ⟨s,D,hD,hM⟩ := hM
  let Q := L-M
  let S := U.smoothEnergyPowerLinear (r+s)
  have hQ (x : U.smoothEnergySpace) : ‖Q x‖ ≤
      (C*‖U.inverseSobolev s‖+D*‖U.inverseSobolev r‖)*‖S x‖ := by
    have h1 := (hL x).trans (mul_le_mul_of_nonneg_left (U.smoothEnergyPower_norm_add r s x) hC)
    have h2 := (hM x).trans (mul_le_mul_of_nonneg_left (U.smoothEnergyPower_norm_add s r x) hD)
    rw [Nat.add_comm s r] at h2
    exact (norm_sub_le (L x) (M x)).trans (by change _ ≤ (C*‖U.inverseSobolev s‖+D*‖U.inverseSobolev r‖)*‖U.smoothEnergyPower (r+s) x‖; nlinarith)
  let B := Q.extendOfNorm S
  have hB (x : U.smoothEnergySpace) : B (S x)=Q x :=
    Q.extendOfNorm_eq (U.smoothEnergyPowerLinear_dense (r+s)) ⟨_,hQ⟩ x
  have hb (v : V) : B (v : Completion V)=0 := by
    have h := hB (U.smoothCoreVector (U.inverseCoreEnergy (r+s) v))
    have hs : S (U.smoothCoreVector (U.inverseCoreEnergy (r+s) v))=(v:Completion V) := by
      dsimp [S]
      rw [U.smoothEnergyPowerLinear_apply,U.smoothEnergyPower_core,U.energyShift_inverseCoreEnergy]
    rw [hs] at h
    simpa only [Q,LinearMap.sub_apply,he,sub_self] using h
  have hzero : B=0 := by
    ext x
    exact Completion.denseRange_coe.induction_on x
      (isClosed_eq B.continuous continuous_const) hb
  ext x
  have h := hB x
  rw [hzero] at h
  exact sub_eq_zero.mp h.symm
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma modulatedSum_sobolev_bound (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) (r : ℤ) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : U.smoothEnergySpace,
      ‖U.modulatedSum hc ha hb hf hg r x‖ ≤ C*‖U.smoothEnergyPower m x‖ := by
  obtain ⟨m,K,hK,h⟩ := U.modulated_product_uniform_bound hc ha hb (hf.shift r) (hg.shift (-r))
  have h' (j : ℕ) (x : U.smoothEnergySpace) :
      ‖(U.smoothSmear hc ha (hg.shift (-(j+r:ℤ)))
        (U.smoothSmear hc hb (hf.shift (j+r:ℤ)) x) : Completion V)‖ ≤
        K/(1+(j:ℝ))^2*‖U.smoothEnergyPower m x‖ := by
    convert! h j x using 1
    all_goals try with_reducible_and_instances rfl
    congr 5 <;> funext n <;> congr 1 <;> omega
  have hs : Summable (fun j : ℕ => K/(1+(j:ℝ))^2) := by
    have ht := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    have ht' : Summable (fun j : ℕ => 1/(1+(j:ℝ))^2) := by
      simpa only [Nat.cast_add,Nat.cast_one,add_comm] using ht
    simpa only [mul_one_div] using ht'.mul_left K
  refine ⟨m,∑' j : ℕ, K/(1+(j:ℝ))^2,tsum_nonneg (fun _ => by positivity),?_⟩
  intro x
  rw [U.modulatedSum_apply]
  calc
    _ ≤ ∑' j : ℕ, K/(1+(j:ℝ))^2*‖U.smoothEnergyPower m x‖ :=
      tsum_of_norm_bounded (hs.mul_right _).hasSum (fun j => h' j x)
    _ = _ := tsum_mul_right
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
def localNormalMap (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (f χ : SmoothCircleFunction) (c : ℤ) : U.smoothEnergySpace →ₗ[ℂ] Completion V :=
  U.modulatedSum hc ha hb f.rapid_coefficients χ.rapid_coefficients (1-c)+
  U.modulatedSum hc hb ha χ.rapid_coefficients f.rapid_coefficients c
lemma localNormalMap_matrix (hc : A.toVertexAlgebra.C2Cofinite)
    {a b x y : V} {d e D E : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hx : x ∈ A.grade D) (hy : y ∈ A.grade E) (c : ℤ)
    {χ f : SmoothCircleFunction}
    (hχ : Disjoint (tsupport (χ.add (SmoothCircleFunction.constant (-1)))) (tsupport f)) :
    inner ℂ (x:Completion V) (U.localNormalMap hc ha hb f χ c (U.smoothCoreVector y)) =
      f.coefficient ((E:ℤ)-D)*inner ℂ x (A.normalAt a b d e ((E:ℤ)-D) c y) := by
  unfold localNormalMap
  rw [LinearMap.add_apply,inner_add_right,U.modulatedSum_apply,U.modulatedSum_apply,
    inner_tsum_right (U.summable_modulated_product_shift hc ha hb f.rapid_coefficients χ.rapid_coefficients (1-c) _),
    inner_tsum_right (U.summable_modulated_product_shift hc hb ha χ.rapid_coefficients f.rapid_coefficients c _)]
  have h1 (j : ℕ) : -(j+(1-c):ℤ)=c-(j+1:ℤ) := by omega
  have h2 (j : ℕ) : (j+(1-c):ℤ)=(j+1:ℤ)-c := by omega
  simp_rw [h1,h2]
  exact U.local_normal_series_matrix_shift hc ha hb hx hy c hχ
lemma localNormalMap_core (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {χ f : SmoothCircleFunction}
    (hχ : Disjoint (tsupport (χ.add (SmoothCircleFunction.constant (-1)))) (tsupport f)) (y : V) :
    U.localNormalMap hc ha hb f χ (1-(d:ℤ)) (U.smoothCoreVector y)=
      A.smearedMap (mode A.fields a (-1) b) (d+e)
        (U.polynomialEnergyBounds hc _) f.coefficient f.rapid_coefficients y := by
  let L := U.localNormalMap hc ha hb f χ (1-(d:ℤ))
  let M := A.smearedMap (mode A.fields a (-1) b) (d+e)
    (U.polynomialEnergyBounds hc _) f.coefficient f.rapid_coefficients
  have hc0 : U.smoothCoreVector (0:V)=0 := by ext; simp only [smoothCoreVector,Completion.coe_zero,Submodule.coe_zero]
  have hca (v w : V) : U.smoothCoreVector (v+w)=U.smoothCoreVector v+U.smoothCoreVector w := by
    ext; simp only [smoothCoreVector,Completion.coe_add,Submodule.coe_add]
  have hn : mode A.fields a (-1) b ∈ A.grade (d+e) := A.mode_mem_grade ha hb (-1) (by omega)
  change L (U.smoothCoreVector y)=M y
  apply A.homogeneous_induction (P := fun y => L (U.smoothCoreVector y)=M y)
  · simp only [hc0,map_zero]
  · intro E y hy
    apply ext_inner_left ℂ
    intro x
    apply Completion.denseRange_coe.induction_on (p := fun x =>
      inner ℂ x (L (U.smoothCoreVector y))=inner ℂ x (M y)) x
      (isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const))
    intro x
    apply A.homogeneous_induction (P := fun x =>
      inner ℂ (x:Completion V) (L (U.smoothCoreVector y))=inner ℂ (x:Completion V) (M y))
    · simp only [Completion.coe_zero,inner_zero_left]
    · intro D x hx
      exact (U.localNormalMap_matrix hc ha hb hx hy (1-(d:ℤ)) hχ).trans (by
        rw [A.normalAt_vertex_product]
        exact (U.inner_smearedMap_homogeneous hn hx hy _ f.rapid_coefficients).symm)
    · intro x z hx hz
      simp only [Completion.coe_add,inner_add_left,hx,hz]
  · intro y z hy hz
    simp only [hca,map_add,hy,hz]
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma smooth_linear_add_bound (L M : U.smoothEnergySpace →ₗ[ℂ] Completion V)
    (hL : ∃ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖L x‖ ≤ C*‖U.smoothEnergyPower r x‖)
    (hM : ∃ s : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ x, ‖M x‖ ≤ D*‖U.smoothEnergyPower s x‖) :
    ∃ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖(L+M) x‖ ≤ C*‖U.smoothEnergyPower r x‖ := by
  obtain ⟨r,C,hC,hL⟩ := hL
  obtain ⟨s,D,hD,hM⟩ := hM
  refine ⟨r+s,C*‖U.inverseSobolev s‖+D*‖U.inverseSobolev r‖,by positivity,?_⟩
  intro x
  have h1 := (hL x).trans (mul_le_mul_of_nonneg_left (U.smoothEnergyPower_norm_add r s x) hC)
  have h2 := (hM x).trans (mul_le_mul_of_nonneg_left (U.smoothEnergyPower_norm_add s r x) hD)
  rw [Nat.add_comm s r] at h2
  exact (norm_add_le (L x) (M x)).trans (by nlinarith)
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

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
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma localNormalMap_bound (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (f χ : SmoothCircleFunction) (c : ℤ) :
    ∃ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖U.localNormalMap hc ha hb f χ c x‖ ≤ C*‖U.smoothEnergyPower r x‖ :=
  U.smooth_linear_add_bound _ _
    (U.modulatedSum_sobolev_bound hc ha hb f.rapid_coefficients χ.rapid_coefficients (1-c))
    (U.modulatedSum_sobolev_bound hc hb ha χ.rapid_coefficients f.rapid_coefficients c)
lemma smoothSmear_sobolev_bound (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    ∃ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : U.smoothEnergySpace,
      ‖(U.smoothSmear hc ha hf x : Completion V)‖ ≤ C*‖U.smoothEnergyPower r x‖ := by
  obtain ⟨C,hC,p,k,hA⟩ := (U.polynomialEnergyBounds hc a).physical A d
  refine ⟨k,coefficientSeminorm f p*C,mul_nonneg (coefficientSeminorm_nonneg f p) hC.le,?_⟩
  intro x
  rw [U.smoothSmear_eq_normalized hc ha hA hf]
  exact (U.normalizedField hc a d k hf).le_of_opNorm_le (U.normalizedField_norm hc hC.le hA hf) _
 

lemma localNormalMap_eq_smoothSmear (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {χ f : SmoothCircleFunction}
    (hχ : Disjoint (tsupport (χ.add (SmoothCircleFunction.constant (-1)))) (tsupport f))
    (x : U.smoothEnergySpace) :
    U.localNormalMap hc ha hb f χ (1-(d:ℤ)) x=
      (U.smoothSmear hc (A.mode_mem_grade (k := d+e) ha hb (-1) (by omega))
        f.rapid_coefficients x : Completion V) := by
  let hn := A.mode_mem_grade (k := d+e) ha hb (-1) (by omega)
  let M := U.smoothEnergySpace.subtype.comp (U.smoothSmear hc hn f.rapid_coefficients)
  have H : U.localNormalMap hc ha hb f χ (1-(d:ℤ))=M := by
    apply U.smooth_linear_eq_of_core _ _ (U.localNormalMap_bound hc ha hb f χ _)
      (U.smoothSmear_sobolev_bound hc hn f.rapid_coefficients)
    intro v
    exact (U.localNormalMap_core hc ha hb hχ v).trans (U.smoothSmear_coe hc hn f.rapid_coefficients v).symm
  exact congrArg (fun L => L x) H
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set
namespace StronglyRationalVOA.SmoothCircleFunction
def modulate (f : SmoothCircleFunction) (j : ℤ) : SmoothCircleFunction where
  toFun := fun t => fourier j (t : AddCircle (2*Real.pi))*f t
  periodic := by
    intro t
    simp only [AddCircle.coe_add,AddCircle.coe_period,add_zero]
    rw [f.periodic t]
  smooth := by
    apply ContDiff.mul _ f.smooth
    simp only [fourier_coe_apply]
    exact (((contDiff_const.mul Complex.ofRealCLM.contDiff).div_const _).cexp)
local instance instFactLtRealOfNatHMulPi_3_r68b81f_1 : Fact (0 < 2*Real.pi) := ⟨period_pos⟩
lemma modulate_coefficient (f : SmoothCircleFunction) (j n : ℤ) :
    (f.modulate j).coefficient n=f.coefficient (n-j) := by
  have h : (f.modulate j).toContinuousMap=(fourier j : C(AddCircle (2*Real.pi),ℂ))*f.toContinuousMap := by
    ext x
    induction x using Quotient.inductionOn with | h t => rfl
  rw [← fourierCoeff_toContinuousMap,h,FourierAnalysis.coefficient_character_mul,fourierCoeff_toContinuousMap]
end StronglyRationalVOA.SmoothCircleFunction

open Set
namespace StronglyRationalVOA.SmoothCircleFunction
lemma modulate_translate_support (f : SmoothCircleFunction) (j : ℤ) (t : ℝ) :
    tsupport ((f.modulate j).translate t).onCircle ⊆ tsupport (f.translate t).onCircle := by
  apply closure_mono
  intro x hx
  induction x using Quotient.inductionOn with | h s =>
  change fourier j ((s-t : ℝ) : AddCircle (2*Real.pi))*f (s-t) ≠ 0 at hx
  change f (s-t) ≠ 0
  exact (mul_ne_zero_iff.mp hx).2
 

attribute [local instance] OAI.StronglyRationalVOA.SmoothCircleFunction.instFactLtRealOfNatHMulPi_4
lemma exists_normal_cutoff (f : SmoothCircleFunction) {O : Set (AddCircle (2*Real.pi))}
    (hO : IsOpen O) (hf : tsupport f.onCircle ⊆ O) :
    ∃ χ : SmoothCircleFunction, tsupport χ.onCircle ⊆ O ∧
      Disjoint (tsupport (χ.add (constant (-1)))) (tsupport f) := by
  obtain ⟨W,hW,hfW,hWO,hWc⟩ := exists_open_between_and_isCompact_closure isClosed_closure.isCompact hO hf
  obtain ⟨χ,_,hχ1,hχO⟩ := exists_real_cutoff hWc hO hWO
  refine ⟨χ,hχO,disjoint_lift ?_⟩
  have hG : tsupport (χ.add (constant (-1))).onCircle ⊆ Wᶜ := by
    apply closure_minimal _ hW.isClosed_compl
    intro x hx hxW
    have he := hχ1 (subset_closure hxW)
    induction x using Quotient.inductionOn with | h t =>
    change χ t+(-1:ℂ) ≠ 0 at hx
    change χ t=1 at he
    exact hx (by rw [he]; ring)
  exact Set.disjoint_left.mpr (fun x hx hfx => hG hx (hfW hfx))
end StronglyRationalVOA.SmoothCircleFunction

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma modulatedSum_commutes (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) (r : ℤ)
    (Q : Completion V →L[ℂ] Completion V)
    (hQ : ∀ x : U.smoothEnergySpace, Q x ∈ U.smoothEnergySpace)
    (hA : ∀ j : ℤ, U.smoothSmear hc ha (hg.shift j)*SymmetricOperator.restricted U.smoothEnergySpace Q hQ =
      SymmetricOperator.restricted U.smoothEnergySpace Q hQ*U.smoothSmear hc ha (hg.shift j))
    (hB : ∀ j : ℤ, U.smoothSmear hc hb (hf.shift j)*SymmetricOperator.restricted U.smoothEnergySpace Q hQ =
      SymmetricOperator.restricted U.smoothEnergySpace Q hQ*U.smoothSmear hc hb (hf.shift j))
    (x : U.smoothEnergySpace) :
    U.modulatedSum hc ha hb hf hg r (SymmetricOperator.restricted U.smoothEnergySpace Q hQ x)=
      Q (U.modulatedSum hc ha hb hf hg r x) := by
  let R := SymmetricOperator.restricted U.smoothEnergySpace Q hQ
  have he (j : ℕ) : (U.smoothSmear hc ha (hg.shift (-(j+r:ℤ)))
      (U.smoothSmear hc hb (hf.shift (j+r:ℤ)) (R x)) : Completion V)=
      Q (U.smoothSmear hc ha (hg.shift (-(j+r:ℤ)))
        (U.smoothSmear hc hb (hf.shift (j+r:ℤ)) x)) := by
    have h (S T : Module.End ℂ U.smoothEnergySpace) (hS : S*R=R*S) (hT : T*R=R*T) :
        S*(T*R)=R*(S*T) := by rw [hT,← mul_assoc,hS,mul_assoc]
    exact congrArg (fun P : Module.End ℂ U.smoothEnergySpace => (P x : Completion V))
      (h _ _ (hA _) (hB _))
  rw [U.modulatedSum_apply,U.modulatedSum_apply]
  exact (tsum_congr he).trans (Q.hasSum (U.summable_modulated_product_shift hc ha hb hf hg r x).hasSum).tsum_eq
lemma localNormalMap_commutes (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (f χ : SmoothCircleFunction) (c : ℤ)
    (Q : Completion V →L[ℂ] Completion V)
    (hQ : ∀ x : U.smoothEnergySpace, Q x ∈ U.smoothEnergySpace)
    (hA : ∀ j : ℤ, U.smoothSmear hc ha (χ.rapid_coefficients.shift j)*SymmetricOperator.restricted U.smoothEnergySpace Q hQ =
      SymmetricOperator.restricted U.smoothEnergySpace Q hQ*U.smoothSmear hc ha (χ.rapid_coefficients.shift j))
    (hB : ∀ j : ℤ, U.smoothSmear hc hb (f.rapid_coefficients.shift j)*SymmetricOperator.restricted U.smoothEnergySpace Q hQ =
      SymmetricOperator.restricted U.smoothEnergySpace Q hQ*U.smoothSmear hc hb (f.rapid_coefficients.shift j))
    (x : U.smoothEnergySpace) :
    U.localNormalMap hc ha hb f χ c (SymmetricOperator.restricted U.smoothEnergySpace Q hQ x)=
      Q (U.localNormalMap hc ha hb f χ c x) := by
  dsimp only [localNormalMap,LinearMap.add_apply]
  rw [map_add,U.modulatedSum_commutes hc ha hb _ _ _ Q hQ hA hB,
    U.modulatedSum_commutes hc hb ha _ _ _ Q hQ hB hA]
lemma normal_product_graph_invariant (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {χ f : SmoothCircleFunction}
    (hχ : Disjoint (tsupport (χ.add (SmoothCircleFunction.constant (-1)))) (tsupport f))
    (Q : Completion V →L[ℂ] Completion V)
    (hQ : ∀ x : U.smoothEnergySpace, Q x ∈ U.smoothEnergySpace)
    (hA : ∀ j : ℤ, ∀ x y, (x,y) ∈ (U.closedSmoothField hc a d (χ.modulate j)).graph →
      (Q x,Q y) ∈ (U.closedSmoothField hc a d (χ.modulate j)).graph)
    (hB : ∀ j : ℤ, ∀ x y, (x,y) ∈ (U.closedSmoothField hc b e (f.modulate j)).graph →
      (Q x,Q y) ∈ (U.closedSmoothField hc b e (f.modulate j)).graph)
    {x y : Completion V}
    (hxy : (x,y) ∈ (U.closedSmoothField hc (mode A.fields a (-1) b) (d+e) f).graph) :
    (Q x,Q y) ∈ (U.closedSmoothField hc (mode A.fields a (-1) b) (d+e) f).graph := by
  let hn : mode A.fields a (-1) b ∈ A.grade (d+e) := A.mode_mem_grade ha hb (-1) (by omega)
  let R := SymmetricOperator.restricted U.smoothEnergySpace Q hQ
  have hcA (j : ℤ) : U.smoothSmear hc ha (χ.rapid_coefficients.shift j)*R=R*U.smoothSmear hc ha (χ.rapid_coefficients.shift j) := by
    have H := SymmetricOperator.restricted_commutes_of_graph U.smoothEnergySpace
      (U.smoothSmear hc ha (χ.modulate j).rapid_coefficients) Q hQ (U.closedSmoothField hc a d (χ.modulate j))
      (U.smoothSmear_graph hc ha (χ.modulate j).rapid_coefficients) (hA j)
    have he : (χ.modulate j).coefficient=fun n => χ.coefficient (n-j) := funext (χ.modulate_coefficient j)
    simpa only [he] using H
  have hcB (j : ℤ) : U.smoothSmear hc hb (f.rapid_coefficients.shift j)*R=R*U.smoothSmear hc hb (f.rapid_coefficients.shift j) := by
    have H := SymmetricOperator.restricted_commutes_of_graph U.smoothEnergySpace
      (U.smoothSmear hc hb (f.modulate j).rapid_coefficients) Q hQ (U.closedSmoothField hc b e (f.modulate j))
      (U.smoothSmear_graph hc hb (f.modulate j).rapid_coefficients) (hB j)
    have he : (f.modulate j).coefficient=fun n => f.coefficient (n-j) := funext (f.modulate_coefficient j)
    simpa only [he] using H
  have hcomm : U.smoothSmear hc hn f.rapid_coefficients*R=R*U.smoothSmear hc hn f.rapid_coefficients := by
    ext z
    have H := U.localNormalMap_commutes hc ha hb f χ (1-(d:ℤ)) Q hQ hcA hcB z
    rw [U.localNormalMap_eq_smoothSmear hc ha hb hχ,
      U.localNormalMap_eq_smoothSmear hc ha hb hχ] at H
    convert! H using 1
    all_goals try with_reducible_and_instances rfl

  have hce := U.smoothSmear_core hc hn f.rapid_coefficients
  change (SymmetricOperator.onSubmodule U.smoothEnergySpace (U.smoothSmear hc hn f.rapid_coefficients)).closure =
    U.closedSmoothField hc (mode A.fields a (-1) b) (d+e) f at hce
  rw [← hce] at hxy ⊢
  exact SymmetricOperator.onSubmodule_closure_graph_invariant _ _
    (U.smoothSmear_core_closable hc hn f.rapid_coefficients) Q hQ hcomm hxy
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)


lemma LocalState.normal_product (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hLa : U.LocalState hc a d) (hLb : U.LocalState hc b e) :
    U.LocalState hc (mode A.fields a (-1) b) (d+e) := by
  intro O hO f hf Q hQ x y hxy
  obtain ⟨χ,hχO,hχ⟩ := f.exists_normal_cutoff hO hf
  obtain ⟨ε,hε,hεF⟩ := f.exists_translation_radius hO hf
  obtain ⟨δ,hδ,hδF⟩ := χ.exists_translation_radius hO hχO
  let r : ℕ → ℝ := fun n => min ε δ/((n:ℝ)+1)
  have hr (n : ℕ) : 0 < r n := div_pos (lt_min hε hδ) (by positivity)
  have hrle (n : ℕ) : r n ≤ min ε δ :=
    div_le_self (le_min hε.le hδ.le) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hl : Tendsto r atTop (𝓝 0) := by
    simpa only [zero_mul,mul_zero,mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (min ε δ)
  let R (n : ℕ) := SymmetricOperator.smoothConjugate U.conformalHamiltonian
    (U.energyOperator_selfAdjoint (fun d => d)) Q (r n) (hr n)
  have hRn (n : ℕ) : (R n x,R n y) ∈
      (U.closedSmoothField hc (mode A.fields a (-1) b) (d+e) f).graph := by
    apply U.normal_product_graph_invariant hc ha hb hχ (R n)
      (fun z => U.smoothConjugate_smooth Q (r n) (hr n) z.property) _ _ hxy
    · intro j u v huv
      apply U.smoothConjugate_localState_graph hc ha hLa (χ.modulate j) hO Q hQ (r n) (hr n) _ huv
      intro t ht
      exact (χ.modulate_translate_support j t).trans
        (hδF t (ht.trans_le ((hrle n).trans (min_le_right _ _))))
    · intro j u v huv
      apply U.smoothConjugate_localState_graph hc hb hLb (f.modulate j) hO Q hQ (r n) (hr n) _ huv
      intro t ht
      exact (f.modulate_translate_support j t).trans
        (hεF t (ht.trans_le ((hrle n).trans (min_le_left _ _))))
  exact (U.closedSmoothField_isClosed hc (A.mode_mem_grade ha hb (-1) (by omega)) f).mem_of_tendsto
    ((SymmetricOperator.smoothConjugate_strong _ _ Q r hr hl x).prodMk_nhds
      (SymmetricOperator.smoothConjugate_strong _ _ Q r hr hl y)) (Eventually.of_forall hRn)
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set UniformSpace
namespace StronglyRationalVOA.SmoothCircleFunction
lemma differentiated_support_circle (f : SmoothCircleFunction) (k : ℕ) :
    tsupport (f.differentiated k).onCircle ⊆ tsupport f.onCircle := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  induction x using Quotient.inductionOn with | h t =>
  exact f.tsupport_lift_subset (f.differentiated_support k (subset_closure hx))
def translationTest (f : SmoothCircleFunction) (d : ℕ) : SmoothCircleFunction :=
  ((f.differentiated 1).scale Complex.I).add (f.scale (-(d:ℂ)))
lemma translationTest_coefficient (f : SmoothCircleFunction) (d : ℕ) (n : ℤ) :
    (f.translationTest d).coefficient n= (-((n:ℂ)+d))*f.coefficient n := by
  rw [translationTest,coefficient_add,coefficient_scale,coefficient_scale,coefficient_differentiated,pow_one]
  linear_combination (f.coefficient n*(n:ℂ))*(Complex.I_sq)
lemma translationTest_support (f : SmoothCircleFunction) (d : ℕ) :
    tsupport (f.translationTest d).onCircle ⊆ tsupport f.onCircle := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  have hf : f.onCircle x=0 := (Function.notMem_support.mp (fun h => hn (subset_closure h)))
  have hd : (f.differentiated 1).onCircle x=0 :=
    (Function.notMem_support.mp (fun h => hn (f.differentiated_support_circle 1 (subset_closure h))))
  induction x using Quotient.inductionOn with | h t =>
  change f t=0 at hf
  change f.differentiated 1 t=0 at hd
  exact hx (by change Complex.I * f.differentiated 1 t + (-(d:ℂ))*f t = 0; rw [hf,hd]; ring)
end StronglyRationalVOA.SmoothCircleFunction
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma closedSmoothField_translation (hc : A.toVertexAlgebra.C2Cofinite)
    (a : V) (d : ℕ) (f : SmoothCircleFunction) :
    U.closedSmoothField hc (A.toVertexAlgebra.translation a) (d+1) f=
      U.closedSmoothField hc a d (f.translationTest d) := by
  have h : A.smearedMap (A.toVertexAlgebra.translation a) (d+1) (U.polynomialEnergyBounds hc _) f.coefficient f.rapid_coefficients =
      A.smearedMap a d (U.polynomialEnergyBounds hc _) (f.translationTest d).coefficient (f.translationTest d).rapid_coefficients := by
    ext v
    simp only [CFTTypeVOA.smearedMap_apply]
    apply tsum_congr
    intro n
    rw [A.translation_physicalMode,LinearMap.smul_apply,Completion.coe_smul,f.translationTest_coefficient]
    simp only [smul_smul]
    congr 1
    ring
  exact congrArg (fun M : V →ₗ[ℂ] Completion V => (HilbertCore.operator M).closure) h
lemma LocalState.translation (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (hL : U.LocalState hc a d) :
    U.LocalState hc (A.toVertexAlgebra.translation a) (d+1) := by
  intro O hO f hf Q hQ x y hxy
  rw [U.closedSmoothField_translation] at hxy ⊢
  exact hL O hO (f.translationTest d) ((f.translationTest_support d).trans hf) Q hQ x y hxy
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set Filter
open scoped Topology

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
lemma LocalState.smul (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hL : U.LocalState hc a d) (c : ℂ) :
    U.LocalState hc (c • a) d := by
  apply LocalState.span U hc d (S := {a})
  · intro b hb
    rcases Set.mem_singleton_iff.mp hb with rfl
    exact ⟨ha,hL⟩
  · exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton a))
lemma translation_mem_grade {a : V} {d : ℕ} (ha : a ∈ A.grade d) :
    A.toVertexAlgebra.translation a ∈ A.grade (d+1) := by
  rw [← A.virasoro_neg_one_eq_translation]
  exact A.virasoro_mem_grade ha (-1) (by omega)
lemma LocalState.negative_mode (hc : A.toVertexAlgebra.C2Cofinite) (n : ℕ)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hLa : U.LocalState hc a d) (hLb : U.LocalState hc b e) :
    U.LocalState hc (mode A.fields a (-1-(n:ℤ)) b) (d+e+n) := by
  induction n generalizing a d with
  | zero => simpa only [Nat.cast_zero,sub_zero,add_zero] using LocalState.normal_product U hc ha hb hLa hLb
  | succ n ih =>
    have ht := LocalState.translation U hc hLa
    have htg := translation_mem_grade ha
    have H := ih htg ht
    have hm : mode A.fields (A.toVertexAlgebra.translation a) (-1-(n:ℤ)) b =
        ((n+1:ℕ):ℂ) • mode A.fields a (-1-((n+1:ℕ):ℤ)) b := by
      rw [A.translation_covariance,LinearMap.smul_apply]
      congr 1
      · push_cast
        ring
      · congr 2
        omega
    have hg : mode A.fields (A.toVertexAlgebra.translation a) (-1-(n:ℤ)) b ∈ A.grade (d+1+e+n) :=
      A.mode_mem_grade htg hb _ (by omega)
    have HH := LocalState.smul U hc hg H (((n+1:ℕ):ℂ)⁻¹)
    rw [hm,smul_smul,inv_mul_cancel₀ (by exact_mod_cast (Nat.succ_ne_zero n)),one_smul] at HH
    convert HH using 1
    all_goals try with_reducible_and_instances rfl
    omega
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set

open UniformSpace Set

open UniformSpace Set

open Set
open scoped Topology ContDiff

open UniformSpace Set Filter
open scoped Topology

open UniformSpace Set

end

end OAI
end


