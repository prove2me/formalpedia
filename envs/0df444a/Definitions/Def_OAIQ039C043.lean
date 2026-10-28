-- Prove2me | Definitions.Def_OAIQ039C043
-- name    : OAIQ039C043
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:25:23.065156+00:00
-- url     : https://prove2.me/theorems/ed77ac80-19b4-42d9-ade8-6978309a07a0
-- title:
--   Definitions bundle OAIQ039C043 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 9 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_AddField`, `Commutator_DiagonalCommute`, `Commutator_FieldAlgebra`, `Commutator_KaplanskyFull`, `Commutator_ScalarIndicatorAdjoint`, `Commutator_StarField`.
--
--   **Imports.** It imports the bundles `OAIQ039C033` and `OAIQ039C034` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C054`, `OAIQ039C055` and `OAIQ039C056`; the proofs of `OAI.Kadison.Decomposable.exists_starHom_fields`, `OAI.Kadison.Decomposable.localized_matrix_commutator_bound` and `OAI.Kadison.Decomposable.uniform_commutator_in_central_model`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C033
import Definitions.Def_OAIQ039C034

section
-- module Solutions.OAIQ039_CM.Commutator_AddField
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

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma operator_add (T S : Ω → H →L[ℂ] H)
    (hT : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    (hS : ∀ ξ,AEStronglyMeasurable (fun a => S a ξ) μ)
    {b c : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hc : ∀ᵐ a ∂μ,‖S a‖ ≤ c) :
    operator μ (fun a => T a+S a) (add_measurable μ T S hT hS)
      (add_field_bound μ T S hb hc)=operator μ T hT hb+operator μ S hS hc := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [operator_ae μ (fun a => T a+S a) (add_measurable μ T S hT hS)
    (add_field_bound μ T S hb hc) f,operator_ae μ T hT hb f,operator_ae μ S hS hc f,
    Lp.coeFn_add (operator μ T hT hb f) (operator μ S hS hc f)] with a h1 h2 h3 h4
  change operator μ (fun a => T a+S a) (add_measurable μ T S hT hS)
    (add_field_bound μ T S hb hc) f a=(operator μ T hT hb f+operator μ S hS hc f) a
  rw [h1,h4]
  change T a (f a)+S a (f a)=operator μ T hT hb f a+operator μ S hS hc f a
  rw [h2,h3]

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

variable [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

theorem exists_field_of_commutes_indicator (Y : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hcomm : ∀ (s : Set Ω) (hs : MeasurableSet s),Commute Y (indicatorOperator μ s hs)) :
    ∃ (T : Ω → H →L[ℂ] H) (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
      (hb : ∀ᵐ a ∂μ,‖T a‖≤‖Y‖),Y=operator μ T hm hb := by
  let A := Y.comp (Lp.constL 2 μ ℂ)
  have hA : ∀ ξ : H,∀ᵐ a ∂μ,‖A ξ a‖≤‖Y‖*‖ξ‖ := fun ξ =>
    local_constant_ae_bound μ Y hcomm ξ
  let T := PointwiseLift.field μ A ‖Y‖
  have hm := PointwiseLift.field_measurable μ A ‖Y‖ (norm_nonneg Y) hA
  have hb : ∀ᵐ a ∂μ,‖T a‖≤‖Y‖ := Eventually.of_forall
    (PointwiseLift.field_norm_le μ A ‖Y‖ (norm_nonneg Y))
  let M := operator μ T hm hb
  have he (ξ : H) : M (Lp.const 2 μ ξ)=Y (Lp.const 2 μ ξ) := by
    apply Lp.ext
    filter_upwards [operator_ae μ T hm hb (Lp.const 2 μ ξ),
      Lp.coeFn_const (p:=2) (μ:=μ) (c:=ξ),
      PointwiseLift.field_ae μ A ‖Y‖ (norm_nonneg Y) hA ξ] with a ha hc hf
    change M (Lp.const 2 μ ξ) a=T a ((Lp.const 2 μ ξ) a) at ha
    change T a ξ=Y (Lp.const 2 μ ξ) a at hf
    rw [ha,hc]
    exact hf
  have hM : M=Y := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.induction (by norm_num : (2:ENNReal)≠⊤) (fun f => M f=Y f)
    · intro ξ s hs hμs
      rw [Lp.simpleFunc.coe_indicatorConst,←indicatorOperator_const μ s hs ξ]
      calc
        M (indicatorOperator μ s hs (Lp.const 2 μ ξ))=
            indicatorOperator μ s hs (M (Lp.const 2 μ ξ)) :=
          congrArg (fun B : Lp H 2 μ →L[ℂ] Lp H 2 μ => B (Lp.const 2 μ ξ))
            (operator_commutes_indicator μ T hm hb s hs).eq
        _=indicatorOperator μ s hs (Y (Lp.const 2 μ ξ)) := by rw [he]
        _=Y (indicatorOperator μ s hs (Lp.const 2 μ ξ)) :=
          congrArg (fun B : Lp H 2 μ →L[ℂ] Lp H 2 μ => B (Lp.const 2 μ ξ)) (hcomm s hs).eq.symm
    · intro f g hf hg hd hMf hMg
      simp only [map_add,hMf,hMg]
    · exact isClosed_eq M.continuous Y.continuous
  exact ⟨T,hm,hb,hM.symm⟩

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ScalarIndicatorAdjoint
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma indicatorOperator_selfAdjoint (s : Set Ω) (hs : MeasurableSet s) :
    IsSelfAdjoint (indicatorOperator (H:=H) μ s hs) := by
  classical
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_left,L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [indicatorOperator_ae μ s hs f,indicatorOperator_ae μ s hs g]
    with a hf hg
  rw [hf,hg]
  by_cases ha : a∈s <;> simp [ha]

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_StarField
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

lemma adjoint_measurable (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) :
    ∀ ξ,AEStronglyMeasurable (fun a => (T a).adjoint ξ) μ := by
  let A := operator μ T hm hb
  have hcomm (s : Set Ω) (hs : MeasurableSet s) :
      Commute A.adjoint (indicatorOperator μ s hs) := by
    have h := congrArg star (operator_commutes_indicator μ T hm hb s hs).symm
    change A.adjoint*indicatorOperator μ s hs=indicatorOperator μ s hs*A.adjoint
    simpa only [A,star_mul,(indicatorOperator_selfAdjoint (H:=H) μ s hs).star_eq,ContinuousLinearMap.star_eq_adjoint] using h
  obtain ⟨U,hU,hUb,he⟩ := exists_field_of_commutes_indicator μ A.adjoint hcomm
  have hea := adjoint_ae μ T U hm hU hb hUb he.symm
  intro ξ
  apply (hU ξ).congr
  filter_upwards [hea] with a ha
  rw [ha]

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

lemma fieldMember_const (Q : Ω → VonNeumannAlgebra H) (T : H →L[ℂ] H)
    (hmem : ∀ᵐ a ∂μ,T∈Q a) :
    FieldMember μ Q (operator μ (fun _ => T) (fun _ => aestronglyMeasurable_const)
      (Eventually.of_forall (fun _ => le_rfl))) :=
  ⟨(fun _ => T),(fun _ => aestronglyMeasurable_const),‖T‖,
    Eventually.of_forall (fun _ => le_rfl),norm_nonneg T,rfl,hmem⟩

lemma fieldMember_zero (Q : Ω → VonNeumannAlgebra H) : FieldMember μ Q 0 := by
  have he : (0 : Lp H 2 μ →L[ℂ] Lp H 2 μ)=
      operator μ (fun _ => (0:H →L[ℂ] H)) (fun _ => aestronglyMeasurable_const)
        (Eventually.of_forall (fun _ => le_rfl)) := by
    apply operator_eq_of_ae_apply
    intro f
    filter_upwards [Lp.coeFn_zero H 2 μ] with a ha
    exact ha
  rw [he]
  exact fieldMember_const μ Q 0 (Eventually.of_forall (fun a => (Q a).zero_mem))

lemma fieldMember_one (Q : Ω → VonNeumannAlgebra H) : FieldMember μ Q 1 := by
  have he : (1 : Lp H 2 μ →L[ℂ] Lp H 2 μ)=
      operator μ (fun _ => (1:H →L[ℂ] H)) (fun _ => aestronglyMeasurable_const)
        (Eventually.of_forall (fun _ => le_rfl)) := by
    apply operator_eq_of_ae_apply
    intro f
    exact Eventually.of_forall (fun _ => rfl)
  rw [he]
  exact fieldMember_const μ Q 1 (Eventually.of_forall (fun a => (Q a).one_mem))

lemma fieldMember_add (Q : Ω → VonNeumannAlgebra H)
    {A B : Lp H 2 μ →L[ℂ] Lp H 2 μ} (hA : FieldMember μ Q A)
    (hB : FieldMember μ Q B) : FieldMember μ Q (A+B) := by
  obtain ⟨T,hT,b,hb,hb0,rfl,hTm⟩ := hA
  obtain ⟨S,hS,c,hc,hc0,rfl,hSm⟩ := hB
  refine ⟨(fun a => T a+S a),add_measurable μ T S hT hS,b+c,
    add_field_bound μ T S hb hc,add_nonneg hb0 hc0,(operator_add μ T S hT hS hb hc).symm,?_⟩
  filter_upwards [hTm,hSm] with a ha hb
  exact (Q a).add_mem ha hb

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_KaplanskyFull
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.Kaplansky

open OperatorAmplification

attribute [local instance] OAI.Kadison.Kaplansky.instDecidableEqFinOfNatNat_solutions
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma offDiagonal_selfAdjoint (a : H →L[ℂ] H) : IsSelfAdjoint (offDiagonal a) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  simp only [ContinuousLinearMap.coe_coe,PiLp.inner_apply,Fin.sum_univ_two,
    offDiagonal_zero,offDiagonal_one,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_right]
  exact add_comm _ _

end Kadison.Kaplansky

end

end
end

end OAI
end


