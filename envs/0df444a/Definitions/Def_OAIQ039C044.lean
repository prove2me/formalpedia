-- Prove2me | Definitions.Def_OAIQ039C044
-- name    : OAIQ039C044
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:25:07.480719+00:00
-- url     : https://prove2.me/theorems/6d74b3d9-6e4a-48f5-88c2-79fe27f29a0c
-- title:
--   Definitions bundle OAIQ039C044 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 10 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_DecomposableLimit`, `Commutator_DecomposableNorm`, `Commutator_FieldAlgebra`, `Commutator_HankelAlgebra`, `Commutator_ScalarField`, `Commutator_TightField`.
--
--   **Imports.** It imports the bundles `OAIQ039C032`, `OAIQ039C033` and `OAIQ039C034` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ039C054`; the proofs of `OAI.Kadison.Decomposable.commutant_ae_of_dense_commuting_fields`, `OAI.Kadison.Decomposable.exists_pointwise_starHom`, `OAI.Kadison.Decomposable.exists_starHom_fields`, `OAI.Kadison.Decomposable.matrix_commutator_bound_of_countable_factor_fields`, `OAI.Kadison.Decomposable.matrix_commutator_bound_of_factor_fields` and `OAI.Kadison.Decomposable.uniform_commutator_in_central_model`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C032
import Definitions.Def_OAIQ039C033
import Definitions.Def_OAIQ039C034

section
-- module Solutions.OAIQ039_CM.Commutator_DecomposableNorm
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

lemma operator_indicator_norm_sq (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b)
    (s : Set Ω) (hs : MeasurableSet s) (hμs : μ s≠⊤) (ξ : H) :
    ‖operator μ T hm hb (indicatorConstLp 2 hs hμs ξ)‖^2=∫ a in s,‖T a ξ‖^2 ∂μ := by
  classical
  rw [l2_norm_sq,←integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [operator_ae μ T hm hb (indicatorConstLp 2 hs hμs ξ),
    indicatorConstLp_coeFn (p:=2) (hs:=hs) (hμs:=hμs) (c:=ξ)] with a ha hc
  rw [ha,hc]
  by_cases hx : a∈s <;> simp [hx]

variable [IsFiniteMeasure μ]

lemma fixed_vector_ae_bound (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b d : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hd : 0≤d)
    (hn : ‖operator μ T hm hb‖≤d) (ξ : H) :
    ∀ᵐ a ∂μ,‖T a ξ‖≤d*‖ξ‖ := by
  have hmem : MemLp (fun a => T a ξ) 2 μ := by
    apply (memLp_const ξ).of_le_mul (hm ξ)
    filter_upwards [hb] with a ha
    exact ((T a).le_opNorm ξ).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
  have hi := (memLp_two_iff_integrable_sq_norm (hm ξ)).mp hmem
  have hle : (fun a => ‖T a ξ‖^2) ≤ᵐ[μ] (fun _ => (d*‖ξ‖)^2) := by
    apply ae_le_of_forall_setIntegral_le hi (integrable_const _) 
    intro s hs hμs
    let f := indicatorConstLp 2 hs hμs.ne ξ
    have hnorm : ‖operator μ T hm hb f‖≤d*‖f‖ :=
      ((operator μ T hm hb).le_opNorm f).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg f))
    calc
      (∫ a in s,‖T a ξ‖^2 ∂μ)=‖operator μ T hm hb f‖^2 :=
        (operator_indicator_norm_sq μ T hm hb s hs hμs.ne ξ).symm
      _≤(d*‖f‖)^2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hd (norm_nonneg f))).mpr hnorm
      _=d^2*(∫ a in s,‖ξ‖^2 ∂μ) := by rw [mul_pow,indicator_norm_sq μ s hs hμs.ne ξ]
      _=(∫ a in s,(d*‖ξ‖)^2 ∂μ) := by simp only [mul_pow,integral_const_mul]
  filter_upwards [hle] with a ha
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hd (norm_nonneg ξ))).mp ha

theorem operator_norm_le_iff_ae [TopologicalSpace.SeparableSpace H]
    (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b d : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hd : 0≤d) :
    ‖operator μ T hm hb‖≤d ↔ ∀ᵐ a ∂μ,‖T a‖≤d := by
  constructor
  · intro hn
    have htest (n : ℕ) := fixed_vector_ae_bound μ T hm hb hd hn (TopologicalSpace.denseSeq H n)
    filter_upwards [ae_all_iff.mpr htest] with a ha
    apply ContinuousLinearMap.opNorm_le_bound _ hd
    intro ξ
    exact (TopologicalSpace.denseRange_denseSeq H).induction_on ξ
      (isClosed_le (T a).continuous.norm (continuous_const.mul continuous_norm)) (ha)
  · exact operator_norm_le μ T hm hb hd

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DecomposableLimit
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
  [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

theorem mem_ae_of_bounded_strong_limit (Q : Ω → VonNeumannAlgebra H)
    (T : Ω → H →L[ℂ] H) (hT : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    {c : ℝ} (hc : ∀ᵐ a ∂μ,‖T a‖ ≤ c)
    (S : ℕ → Ω → H →L[ℂ] H)
    (hS : ∀ n ξ,AEStronglyMeasurable (fun a => S n a ξ) μ)
    {b : ℝ} (hb : 0≤b) (hSb : ∀ n,∀ᵐ a ∂μ,‖S n a‖≤b)
    (hmem : ∀ n,∀ᵐ a ∂μ,S n a∈Q a)
    (hlim : ∀ f,Tendsto (fun n => operator μ (S n) (hS n) (hSb n) f) atTop
      (𝓝 (operator μ T hT hc f))) : ∀ᵐ a ∂μ,T a∈Q a := by
  let v : ℕ → H := TopologicalSpace.denseSeq H
  let V : ℕ → Lp H 2 μ := fun j => Lp.constL 2 μ ℂ (v j)
  have hconst (j : ℕ) : V j =ᵐ[μ] fun _ => v j := Lp.coeFn_const 2 μ (v j)
  have hfinite (m : ℕ) : ∀ᵐ a ∂μ,∃ k : ℕ → ℕ,∀ j : Fin m,
      Tendsto (fun n => S (k n) a (v j)) atTop (𝓝 (T a (v j))) := by
    obtain ⟨k,hk,hka⟩ := exists_finite_test_subsequence μ
      (fun n (j : Fin m) => operator μ (S n) (hS n) (hSb n) (V j))
      (fun (j : Fin m) => operator μ T hT hc (V j)) (fun j => hlim (V j))
    filter_upwards [hka,ae_all_iff.mpr hconst,
      ae_all_iff.mpr (fun n => ae_all_iff.mpr (fun j : ℕ =>
        operator_ae μ (S n) (hS n) (hSb n) (V j))),
      ae_all_iff.mpr (fun j : ℕ => operator_ae μ T hT hc (V j))]
      with a hka hv hs ht
    refine ⟨k,fun j => ?_⟩
    have he (n : ℕ) : operator μ (S (k n)) (hS (k n)) (hSb (k n)) (V j) a=
        S (k n) a (v j) := by rw [hs,hv]
    have he' : operator μ T hT hc (V j) a=T a (v j) := by rw [ht,hv]
    simpa only [he,he'] using hka j
  filter_upwards [ae_all_iff.mpr hfinite,ae_all_iff.mpr hSb,ae_all_iff.mpr hmem]
    with a hf hba hma
  apply mem_vonNeumann_of_dense_finite_tests (Q a) v
    (TopologicalSpace.denseRange_denseSeq H) (T a) b hb
  intro m
  obtain ⟨k,hk⟩ := hf m
  have hevent : ∀ᶠ n in atTop,∀ j : Fin m,
      ‖S (k n) a (v j)-T a (v j)‖<1/((m:ℝ)+1) := by
    apply eventually_all.mpr
    intro j
    exact (tendsto_iff_norm_sub_tendsto_zero.mp (hk j)).eventually
      (gt_mem_nhds (by positivity : (0:ℝ)<1/((m:ℝ)+1)))
  obtain ⟨n,hn⟩ := hevent.exists
  exact ⟨S (k n) a,hma (k n),hba (k n),fun j => (hn j).le⟩

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ScalarField
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

lemma operator_smul (z : ℂ) (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) :
    operator μ (fun a => z • T a) (smul_measurable μ z T hm)
      (smul_field_bound μ z T hb)=z • operator μ T hm hb := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [operator_ae μ (fun a => z • T a) (smul_measurable μ z T hm)
    (smul_field_bound μ z T hb) f,operator_ae μ T hm hb f,
    Lp.coeFn_smul z (operator μ T hm hb f)] with a h1 h2 h3
  change operator μ (fun a => z • T a) (smul_measurable μ z T hm)
    (smul_field_bound μ z T hb) f a=(z • operator μ T hm hb f) a
  rw [h1,h3]
  change z • T a (f a)=z • operator μ T hm hb f a
  rw [h2]

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

lemma fieldMember_smul (Q : Ω → VonNeumannAlgebra H) (z : ℂ)
    {A : Lp H 2 μ →L[ℂ] Lp H 2 μ} (hA : FieldMember μ Q A) :
    FieldMember μ Q (z • A) := by
  obtain ⟨T,hT,b,hb,hb0,rfl,hTm⟩ := hA
  refine ⟨(fun a => z • T a),smul_measurable μ z T hT,‖z‖*b,
    smul_field_bound μ z T hb,mul_nonneg (norm_nonneg z) hb0,
    (operator_smul μ z T hT hb).symm,?_⟩
  filter_upwards [hTm] with a ha
  exact (Q a).smul_mem ha z

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

variable (hr : MulAut.conj d u=u⁻¹)

variable {p : A} (hp : IsStarProjection p)
  (hpform : p=(1/2 : ℂ) • (1+(d : A)))

@[simp] lemma cosine_zero : cosine u hp 0=1 := by
  apply Subtype.ext
  simp [hp.isIdempotentElem.eq]

end Kadison.DihedralCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TightField
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
  [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

omit [CompleteSpace H] [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
lemma operator_bound_irrel (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b c : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hc : ∀ᵐ a ∂μ,‖T a‖ ≤ c) :
    operator μ T hm hb=operator μ T hm hc := by
  apply operator_eq_of_ae_apply
  exact operator_ae μ T hm hb

lemma fieldMember_tight (Q : Ω → VonNeumannAlgebra H)
    {A : Lp H 2 μ →L[ℂ] Lp H 2 μ} (hA : FieldMember μ Q A)
    {c : ℝ} (hc : 0 ≤ c) (hAc : ‖A‖ ≤ c) :
    ∃ (T : Ω → H →L[ℂ] H) (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
      (hb : ∀ᵐ a ∂μ,‖T a‖ ≤ c),A=operator μ T hm hb ∧ ∀ᵐ a ∂μ,T a∈Q a := by
  obtain ⟨T,hm,b,hb,hb0,rfl,hmem⟩ := hA
  have hb' := (operator_norm_le_iff_ae μ T hm hb hc).mp hAc
  exact ⟨T,hm,hb',operator_bound_irrel μ T hm hb hb',hmem⟩

omit [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
lemma fieldMember_commutes_indicator (Q : Ω → VonNeumannAlgebra H)
    {A : Lp H 2 μ →L[ℂ] Lp H 2 μ} (hA : FieldMember μ Q A)
    (s : Set Ω) (hs : MeasurableSet s) : Commute A (indicatorOperator μ s hs) := by
  obtain ⟨T,hm,b,hb,_,rfl,_⟩ := hA
  exact operator_commutes_indicator μ T hm hb s hs

end Kadison.Decomposable

end

end
end

end OAI
end


