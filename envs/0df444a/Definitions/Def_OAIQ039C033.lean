-- Prove2me | Definitions.Def_OAIQ039C033
-- name    : OAIQ039C033
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:19:37.698325+00:00
-- url     : https://prove2.me/theorems/799a9585-0171-4c95-a04e-82593feaadca
-- title:
--   Definitions bundle OAIQ039C033 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 29 declarations of OpenAI's Lean: 7 definitions and 22 theorems. The definitions and types are `OAI.Kadison.CyclicSpectral.scalarMultiplier`, `OAI.Kadison.Decomposable.FieldMember`, `OAI.Kadison.Decomposable.indicatorOperator`, `OAI.Kadison.PointwiseLift.field`, `OAI.Kadison.PointwiseLift.rationalField`, `OAI.Kadison.PointwiseLift.raw`, `OAI.Kadison.PointwiseLift.realField`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_CyclicSpectralUnitary`, `Commutator_DecomposableAlgebra`, `Commutator_DecomposableOperator`, `Commutator_DiagonalCommute`, `Commutator_FieldAdjoint`, `Commutator_FieldAlgebra`, `Commutator_HankelAlgebra`, `Commutator_PointwiseLinearLift`, `Commutator_PolarSupport`, `Commutator_ScalarIndicator`.
--
--   **Imports.** It imports the bundles `OAIQ039C022`, `OAIQ039C023` and `OAIQ039C024` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C043`, `OAIQ039C044`, `OAIQ039C045`, `OAIQ039C046` and `OAIQ039C051`; the statements `OAI.Kadison.CyclicSpectral.exists_gelfand_model`, `OAI.Kadison.CyclicSpectral.stableUnitary_intertwines`, `OAI.Kadison.Decomposable.exists_pointwise_starHom`, `OAI.Kadison.Decomposable.exists_starHom_fields`, `OAI.Kadison.Decomposable.factors_ae_of_central_geometry`, `OAI.Kadison.Decomposable.localized_matrix_commutator_bound`, `OAI.Kadison.Decomposable.uniform_commutator_in_central_model`, `OAI.Kadison.Decomposable.uniform_commutator_in_central_spectral_model_nonzero` and `OAI.Kadison.Decomposable.vector_indicator_of_scalar`; the proofs of `OAI.Kadison.CyclicSpectral.exists_gelfand_model`, `OAI.Kadison.CyclicSpectral.stableUnitary_intertwines`, `OAI.Kadison.Decomposable.uniform_commutator_in_central_spectral_model_nonzero`, `OAI.Kadison.Decomposable.vector_indicator_of_scalar`, `OAI.Kadison.PartialIsometryOrder.maximal_family_spans_of_full_support` and `OAI.Kadison.RelativeCornerQuantization.exists_polar_cut`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C022
import Definitions.Def_OAIQ039C023
import Definitions.Def_OAIQ039C024

section
-- module Solutions.OAIQ039_CM.Commutator_DecomposableOperator
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology ComplexOrder InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma operator_ae (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (f : Lp H 2 μ) :
    operator μ T hm hb f =ᵐ[μ] fun a => T a (f a) := act_ae μ T hm hb f

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CyclicSpectralUnitary
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.CyclicSpectral

variable {Ω H : Type*} [TopologicalSpace Ω] [T2Space Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (μ : Measure Ω)

def scalarMultiplier (f : C(Ω,ℂ)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  Decomposable.operator μ (fun x => (f x) • (1 : ℂ →L[ℂ] ℂ))
    (fun z => by
      change AEStronglyMeasurable (fun x => f x*z) μ
      exact (f.continuous.mul continuous_const).aestronglyMeasurable)
    (Eventually.of_forall (fun x => by
      simpa using f.norm_coe_le_norm x))

end Kadison.CyclicSpectral

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DecomposableAlgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma operator_eq_of_ae_apply (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (A : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hA : ∀ f : Lp H 2 μ,A f =ᵐ[μ] fun a => T a (f a)) :
    A=operator μ T hm hb := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  exact (hA f).trans (operator_ae μ T hm hb f).symm

lemma operator_mul (T S : Ω → H →L[ℂ] H)
    (hT : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    (hS : ∀ ξ : H,AEStronglyMeasurable (fun a => S a ξ) μ)
    {b c : ℝ} (hb0 : 0≤b) (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hc : ∀ᵐ a ∂μ,‖S a‖ ≤ c) :
    operator μ T hT hb*operator μ S hS hc=
      operator μ (fun a => T a*S a) (mul_measurable μ T S hT hS) (mul_bound μ T S hb0 hb hc) := by
  apply operator_eq_of_ae_apply
  intro f
  filter_upwards [operator_ae μ T hT hb (operator μ S hS hc f),operator_ae μ S hS hc f]
    with a ha hs
  change (operator μ T hT hb (operator μ S hS hc f)) a=_
  rw [ha,hs]
  rfl

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PointwiseLinearLift
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.PointwiseLift

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

variable (A : H →L[ℂ] Lp H 2 μ) (b : ℝ)

attribute [local instance] OAI.Kadison.PointwiseLift.instNormedSpaceRat_solutions
omit [CompleteSpace H] in
lemma good_ae (hbound : ∀ x : H,∀ᵐ a ∂μ,‖A x a‖≤b*‖x‖) : ∀ᵐ a ∂μ,Good μ A b a := by
  have ha (x y : RationalDense.subspace H) :
      ∀ᵐ a ∂μ,A ((x+y:H)) a=A (x:H) a+A (y:H) a := by
    rw [map_add]
    exact Lp.coeFn_add _ _
  have hs (r : ℚ) (x : RationalDense.subspace H) :
      ∀ᵐ a ∂μ,A (r • (x:H)) a=r • A (x:H) a := by
    rw [map_rat_smul]
    exact Lp.coeFn_smul _ _
  filter_upwards [ae_all_iff.mpr (fun x => ae_all_iff.mpr (ha x)),
    ae_all_iff.mpr (fun r => ae_all_iff.mpr (hs r)),
    ae_all_iff.mpr (fun x : RationalDense.subspace H => hbound (x:H))] with a ha hs hn
  exact ⟨ha,hs,hn⟩

def raw (a : Ω) (ha : Good μ A b a) : RationalDense.subspace H →L[ℚ] H :=
  ({toFun := fun x => A (x:H) a
    map_add' := ha.1
    map_smul' := ha.2.1} : RationalDense.subspace H →ₗ[ℚ] H).mkContinuous b ha.2.2

def rationalField (a : Ω) : H →L[ℚ] H := by
  classical
  exact if ha : Good μ A b a then (raw μ A b a ha).extend (RationalDense.subspace H).subtypeL else 0

lemma rationalField_subtype (a : Ω) (ha : Good μ A b a) (x : RationalDense.subspace H) :
    rationalField μ A b a (x:H)=A (x:H) a := by
  rw [rationalField,dite_eq_left ha]
  exact ContinuousLinearMap.extend_eq _ (RationalDense.dense H)
    isUniformEmbedding_subtype_val.isUniformInducing x

lemma rationalField_norm_le (hb : 0≤b) (a : Ω) : ‖rationalField μ A b a‖≤b := by
  by_cases ha : Good μ A b a
  · apply ContinuousLinearMap.opNorm_le_bound _ hb
    intro x
    exact (RationalDense.dense H).induction_on x
      (isClosed_le (rationalField μ A b a).continuous.norm (continuous_const.mul continuous_norm))
      (fun y => by
        change ‖rationalField μ A b a (y:H)‖≤b*‖(y:H)‖
        rw [rationalField_subtype μ A b a ha y]
        exact ha.2.2 y)
  · simp [rationalField,ha,hb]

lemma rationalField_ae (hb : 0≤b)
    (hbound : ∀ x : H,∀ᵐ a ∂μ,‖A x a‖≤b*‖x‖) (x : H) :
    (fun a => rationalField μ A b a x)=ᵐ[μ] A x := by
  obtain ⟨f,hf⟩ := RationalDense.exists_seq H x
  have hA : Tendsto (fun n => A (f n:H)) atTop (𝓝 (A x)) := A.continuous.tendsto x |>.comp hf
  obtain ⟨k,hk,hka⟩ := (tendstoInMeasure_of_tendsto_Lp hA).exists_seq_tendsto_ae
  filter_upwards [good_ae μ A b hbound,hka] with a ha hka
  have hcont := (ContinuousLinearMap.lipschitzWith_of_opNorm_le (K := ⟨b,hb⟩)
    (rationalField_norm_le μ A b hb a)).continuous
  have hf' := hcont.tendsto x |>.comp (hf.comp hk.tendsto_atTop)
  have he : (fun n => rationalField μ A b a (f (k n):H))=(fun n => A (f (k n):H) a) :=
    funext (fun n => rationalField_subtype μ A b a ha (f (k n)))
  change Tendsto (fun n => rationalField μ A b a (f (k n):H)) atTop
    (𝓝 (rationalField μ A b a x)) at hf'
  rw [he] at hf'
  exact tendsto_nhds_unique hf' hka

def realField (a : Ω) : H →L[ℝ] H :=
  (rationalField μ A b a).toLinearMap.toAddMonoidHom.toRealLinearMap (rationalField μ A b a).continuous

lemma realField_norm_le (hb : 0≤b) (a : Ω) : ‖realField μ A b a‖≤b := by
  apply ContinuousLinearMap.opNorm_le_bound _ hb
  intro x
  exact ((rationalField μ A b a).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (rationalField_norm_le μ A b hb a) (norm_nonneg x))

def field (a : Ω) : H →L[ℂ] H := ComplexLinearization.operator (realField μ A b a)

lemma field_norm_le (hb : 0≤b) (a : Ω) : ‖field μ A b a‖≤b :=
  (ComplexLinearization.norm_le _).trans (realField_norm_le μ A b hb a)

lemma field_ae (hb : 0≤b) (hbound : ∀ x : H,∀ᵐ a ∂μ,‖A x a‖≤b*‖x‖) (x : H) :
    (fun a => field μ A b a x)=ᵐ[μ] A x := by
  have hs : A (Complex.I • x)=Complex.I • A x := map_smul A _ _
  filter_upwards [rationalField_ae μ A b hb hbound x,
    rationalField_ae μ A b hb hbound (Complex.I • x),Lp.coeFn_smul Complex.I (A x)] with a hx hi hs'
  change (1/2:ℝ) • (rationalField μ A b a x-Complex.I • rationalField μ A b a (Complex.I • x))=_
  rw [hx,hi,hs,hs']
  dsimp only [Pi.smul_apply]
  simp only [smul_smul,Complex.I_mul_I,neg_one_smul,sub_neg_eq_add,smul_add]
  module

lemma field_measurable (hb : 0≤b)
    (hbound : ∀ x : H,∀ᵐ a ∂μ,‖A x a‖≤b*‖x‖) (x : H) :
    AEStronglyMeasurable (fun a => field μ A b a x) μ :=
  (Lp.aestronglyMeasurable (A x)).congr (field_ae μ A b hb hbound x).symm

end Kadison.PointwiseLift

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ScalarIndicator
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def indicatorOperator (s : Set Ω) (hs : MeasurableSet s) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  operator μ (s.indicator (fun _ => (1:H →L[ℂ] H)))
    (indicator_measurable μ s hs) (indicator_bound μ s)

lemma indicatorOperator_ae (s : Set Ω) (hs : MeasurableSet s) (f : Lp H 2 μ) :
    indicatorOperator μ s hs f =ᵐ[μ] s.indicator f := by
  classical
  filter_upwards [operator_ae μ _ (indicator_measurable μ s hs) (indicator_bound μ s) f] with a ha
  change indicatorOperator μ s hs f a=_ at ha ⊢
  rw [ha]
  by_cases hx : a∈s <;> simp [hx]

lemma indicatorOperator_norm_sq (s : Set Ω) (hs : MeasurableSet s) (f : Lp H 2 μ) :
    ‖indicatorOperator μ s hs f‖^2=∫ a in s,‖f a‖^2 ∂μ := by
  classical
  rw [l2_norm_sq,←integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [indicatorOperator_ae μ s hs f] with a ha
  rw [ha]
  by_cases hx : a∈s <;> simp [hx]

variable [IsFiniteMeasure μ]

lemma indicatorOperator_const (s : Set Ω) (hs : MeasurableSet s) (ξ : H) :
    indicatorOperator μ s hs (Lp.const 2 μ ξ)=indicatorConstLp 2 hs (measure_ne_top μ s) ξ := by
  classical
  apply Lp.ext
  filter_upwards [indicatorOperator_ae μ s hs (Lp.const 2 μ ξ),Lp.coeFn_const (p:=2) (μ:=μ) (c:=ξ),
    indicatorConstLp_coeFn (p:=2) (hs:=hs) (hμs:=measure_ne_top μ s) (c:=ξ)] with a ha hc hi
  rw [ha,hi]
  by_cases hx : a∈s
  · simp only [Set.indicator_of_mem hx]
    exact hc
  · simp [hx]

theorem local_constant_ae_bound (Y : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hcomm : ∀ (s : Set Ω) (hs : MeasurableSet s),Commute Y (indicatorOperator μ s hs))
    (ξ : H) : ∀ᵐ a ∂μ,‖Y (Lp.const 2 μ ξ) a‖≤‖Y‖*‖ξ‖ := by
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (Y (Lp.const 2 μ ξ)))).mp
    (Lp.memLp (Y (Lp.const 2 μ ξ)))
  have hh : (fun a => ‖Y (Lp.const 2 μ ξ) a‖^2) ≤ᵐ[μ] (fun _ => (‖Y‖*‖ξ‖)^2) := by
    apply ae_le_of_forall_setIntegral_le hi (integrable_const _)
    intro s hs hμs
    have he : indicatorOperator μ s hs (Y (Lp.const 2 μ ξ))=
        Y (indicatorConstLp 2 hs (measure_ne_top μ s) ξ) := by
      rw [←indicatorOperator_const μ s hs ξ]
      exact congrArg (fun A : Lp H 2 μ →L[ℂ] Lp H 2 μ => A (Lp.const 2 μ ξ)) (hcomm s hs).eq.symm
    calc
      (∫ a in s,‖Y (Lp.const 2 μ ξ) a‖^2 ∂μ)=
          ‖indicatorOperator μ s hs (Y (Lp.const 2 μ ξ))‖^2 :=
        (indicatorOperator_norm_sq μ s hs _).symm
      _=‖Y (indicatorConstLp 2 hs (measure_ne_top μ s) ξ)‖^2 := by rw [he]
      _≤(‖Y‖*‖indicatorConstLp 2 hs (measure_ne_top μ s) ξ‖)^2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg Y) (norm_nonneg _))).mpr (Y.le_opNorm _)
      _=‖Y‖^2*(∫ a in s,‖ξ‖^2 ∂μ) := by rw [mul_pow,indicator_norm_sq μ s hs (measure_ne_top μ s) ξ]
      _=(∫ a in s,(‖Y‖*‖ξ‖)^2 ∂μ) := by simp only [mul_pow,integral_const_mul]
  filter_upwards [hh] with a ha
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg Y) (norm_nonneg ξ))).mp ha

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DiagonalCommute
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma operator_commutes_indicator (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (s : Set Ω) (hs : MeasurableSet s) :
    Commute (operator μ T hm hb) (indicatorOperator μ s hs) := by
  classical
  change operator μ T hm hb*indicatorOperator μ s hs=
    indicatorOperator μ s hs*operator μ T hm hb
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [operator_ae μ T hm hb (indicatorOperator μ s hs f),
    indicatorOperator_ae μ s hs f,indicatorOperator_ae μ s hs (operator μ T hm hb f),
    operator_ae μ T hm hb f] with a ha hi hi' ha'
  change operator μ T hm hb (indicatorOperator μ s hs f) a=
    indicatorOperator μ s hs (operator μ T hm hb f) a
  rw [ha,hi,hi']
  by_cases hx : a∈s
  · simp only [Set.indicator_of_mem hx,ha']
  · simp [hx]

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FieldAdjoint
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [IsFiniteMeasure μ]

omit [CompleteSpace H] in
lemma operator_const_inner_indicator (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (ξ η : H) (s : Set Ω) (hs : MeasurableSet s) :
    inner ℂ (operator μ T hm hb (Lp.const 2 μ ξ))
      (indicatorOperator μ s hs (Lp.const 2 μ η))=∫ a in s,inner ℂ (T a ξ) η ∂μ := by
  classical
  rw [L2.inner_def,←integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [operator_ae μ T hm hb (Lp.const 2 μ ξ),
    Lp.coeFn_const 2 μ ξ,Lp.coeFn_const 2 μ η,
    indicatorOperator_ae μ s hs (Lp.const 2 μ η)] with a h1 h2 h3 h4
  rw [h1,h2,h4]
  by_cases ha : a∈s
  · simp only [Set.indicator_of_mem ha,h3,Function.const_apply]
  · simp [ha]

omit [CompleteSpace H] in
lemma const_inner_operator_indicator (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (ξ η : H) (s : Set Ω) (hs : MeasurableSet s) :
    inner ℂ (Lp.const 2 μ ξ)
      (operator μ T hm hb (indicatorOperator μ s hs (Lp.const 2 μ η)))=
      ∫ a in s,inner ℂ ξ (T a η) ∂μ := by
  classical
  rw [L2.inner_def,←integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [operator_ae μ T hm hb (indicatorOperator μ s hs (Lp.const 2 μ η)),
    Lp.coeFn_const 2 μ ξ,Lp.coeFn_const 2 μ η,
    indicatorOperator_ae μ s hs (Lp.const 2 μ η)] with a h1 h2 h3 h4
  rw [h1,h2,h4]
  by_cases ha : a∈s
  · simp only [Set.indicator_of_mem ha,h3,Function.const_apply]
  · simp [ha]

theorem adjoint_ae [TopologicalSpace.SeparableSpace H]
    (T U : Ω → H →L[ℂ] H)
    (hT : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    (hU : ∀ ξ,AEStronglyMeasurable (fun a => U a ξ) μ)
    {b c : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hc : ∀ᵐ a ∂μ,‖U a‖ ≤ c)
    (h : operator μ U hU hc=(operator μ T hT hb).adjoint) :
    ∀ᵐ a ∂μ,U a=(T a).adjoint := by
  have hp (ξ η : H) : ∀ᵐ a ∂μ,inner ℂ (U a ξ) η=inner ℂ ξ (T a η) := by
    apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
      (field_inner_integrable μ U hU hc ξ η)
      (field_inner_right_integrable μ T hT hb ξ η)
    intro s hs _
    rw [←operator_const_inner_indicator μ U hU hc ξ η s hs,
      ←const_inner_operator_indicator μ T hT hb ξ η s hs,h]
    exact ContinuousLinearMap.adjoint_inner_left _ _ _
  let v : ℕ → H := TopologicalSpace.denseSeq H
  have hv : DenseRange v := TopologicalSpace.denseRange_denseSeq H
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => hp (v i) (v j)))]
    with a ha
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_right ℂ
  intro η
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact hv.induction_on ξ
    (isClosed_eq ((U a).continuous.inner continuous_const)
      (continuous_id.inner continuous_const))
    (fun i => hv.induction_on η
      (isClosed_eq (continuous_const.inner continuous_id)
        (continuous_const.inner (T a).continuous)) (ha i))

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FieldAlgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def FieldMember (Q : Ω → VonNeumannAlgebra H) (A : Lp H 2 μ →L[ℂ] Lp H 2 μ) : Prop :=
  ∃ (T : Ω → H →L[ℂ] H) (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    (b : ℝ) (hb : ∀ᵐ a ∂μ,‖T a‖≤b),0≤b ∧ A=operator μ T hm hb ∧ ∀ᵐ a ∂μ,T a∈Q a

lemma fieldMember_mul (Q : Ω → VonNeumannAlgebra H)
    {A B : Lp H 2 μ →L[ℂ] Lp H 2 μ} (hA : FieldMember μ Q A)
    (hB : FieldMember μ Q B) : FieldMember μ Q (A*B) := by
  obtain ⟨T,hT,b,hb,hb0,rfl,hTm⟩ := hA
  obtain ⟨S,hS,c,hc,hc0,rfl,hSm⟩ := hB
  refine ⟨(fun a => T a*S a),mul_measurable μ T S hT hS,b*c,
    mul_bound μ T S hb0 hb hc,mul_nonneg hb0 hc0,operator_mul μ T S hT hS hb0 hb hc,?_⟩
  filter_upwards [hTm,hSm] with a ha hb
  exact (Q a).mul_mem ha hb

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HankelAlgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.DihedralCorner

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A]

variable (u d : unitary A)

lemma wave_add (n m : ℤ) : wave u (n+m)=wave u n*wave u m := by
  simp [wave, zpow_add]

end Kadison.DihedralCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PolarSupport
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.Polar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma leftSupport_le (T e : H →L[ℂ] H) (he : IsStarProjection e) (hT : e*T=T) :
    leftSupport T≤e := by
  apply ((isProjection_leftSupport T).le_iff_mul_eq_right he).mpr
  change e*(partialIsometry T*star (partialIsometry T))=_
  rw [←mul_assoc,mul_partialIsometry_of_mul T e hT]
  rfl

end Kadison.Polar

end

end
end

end OAI
end


