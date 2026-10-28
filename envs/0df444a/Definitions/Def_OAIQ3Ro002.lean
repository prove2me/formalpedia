-- Prove2me | Definitions.Def_OAIQ3Ro002
-- name    : OAIQ3Ro002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T06:39:50.40234+00:00
-- url     : https://prove2.me/theorems/50b60261-8943-405a-9c7a-e94cd89f694f
-- title:
--   Definitions bundle OAIQ3Ro002 of the split of OpenAI, Rokhlin's multiple-mixing problem for one transformation
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Rokhlin.mixing_all_finite_orders`, carved from OpenAI's openai/math development (OpenAI, *Rokhlin's multiple-mixing problem for one transformation*, OpenAI Math Release, September 23, 2026, result family 145, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 82 declarations of OpenAI's Lean: 38 definitions, 6 instances and 38 theorems. The definitions and types are `OAI.Rokhlin.ArrayObjects.weakInitialLaws`, `OAI.Rokhlin.BorelFibreEnumeration.restrictGraph`, `OAI.Rokhlin.BorelFibreEnumeration.sumFibreEquiv`, `OAI.Rokhlin.ComplementSplit.partition`, `OAI.Rokhlin.ComplementSplit.singleton`, `OAI.Rokhlin.ComplementSplit.singletonFor`, `OAI.Rokhlin.HilbertCode.atBase`, `OAI.Rokhlin.JoiningOperator.contraction`, `OAI.Rokhlin.MeasurablePolarRectangle.HasHaarNormalization`, `OAI.Rokhlin.MeasurableSection`, `OAI.Rokhlin.TriplePartition.split`, `OAI.Rokhlin.TriplePartition.swapAB`, `OAI.Rokhlin.TriplePartition.swapPA`, `OAI.Rokhlin.TriplePartition.swapPB`, `OAI.Rokhlin.codeSlotEquivProjective`, `OAI.Rokhlin.exactCircleTuples`, `OAI.Rokhlin.exactCodeEquivTransport`, `OAI.Rokhlin.exactCodeSpan`, `OAI.Rokhlin.exactCodeVectors`, `OAI.Rokhlin.exactProjectiveMatching`, `OAI.Rokhlin.exactProjectiveSlot`, `OAI.Rokhlin.exactProjectiveTuples`, `OAI.Rokhlin.labelOrbit`, `OAI.Rokhlin.labelShiftFirst`, `OAI.Rokhlin.localCodeEquivGroup`, `OAI.Rokhlin.localCodeEquivSlot`, `OAI.Rokhlin.localGraphTimeEquiv`, `OAI.Rokhlin.localProjectiveMatching`, `OAI.Rokhlin.localProjectiveTransport`, `OAI.Rokhlin.measurableCircleTime`, `OAI.Rokhlin.movingFibreSum`, `OAI.Rokhlin.pairPartition`, `OAI.Rokhlin.productTupleKernel`, `OAI.Rokhlin.projectiveCharacter`, `OAI.Rokhlin.projectiveRep`, `OAI.Rokhlin.projectiveTime`, `OAI.Rokhlin.singletonSplit`, `OAI.Rokhlin.tupleProjectivize`.
--
--   **Sources.** They come from these modules of lean/OAI/Dynamics/MultipleMixing, in whole or in part: [`MultipleMixing_ExactLines`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/ExactLines.lean), [`MultipleMixing_FibreMeasures`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/FibreMeasures.lean), [`MultipleMixing_HilbertCodes`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/HilbertCodes.lean), [`MultipleMixing_Joinings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Joinings.lean), [`MultipleMixing_OrbitCancellation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/OrbitCancellation.lean), [`MultipleMixing_Tensors`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Tensors.lean), [`MultipleMixing_WeakLimits`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/WeakLimits.lean).
--
--   **Imports.** It imports the bundles `OAIQ3Ro000` and `OAIQ3Ro001` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.Rokhlin.ArrayObjects.Object.Rolled.exists_raw_finite_levels`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_column_contraction_projection`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_row_contraction_projection`, `OAI.Rokhlin.MeasurablePolarRectangle.torus_coordinates` and `OAI.Rokhlin.local_moving_cancellation`; the proofs of `OAI_Rokhlin_ArrayObjects_Object_Rolled_exists_commonLocalLineGraph`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.exists_raw_finite_levels`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_active_commutes`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_active_intersections`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_column_contraction_projection`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_exact_split_span`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_polar_a_field`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_polar_b_field`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_polar_data`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_restricted_fixed_squares`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_row_contraction_projection`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.rawCounting_partial_unitary`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_correlation_forces_coefficient`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_correlation_zero`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_row_active_to_column_exact`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_row_indicators_equal`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_row_line_projection`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.saturated_correlation_zero`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.slot_conditional_exactness`, `OAI.Rokhlin.ArrayObjects.compact_zero_entropy_no_witness`, `OAI.Rokhlin.MeasurablePolarRectangle.torus_coordinates` and `OAI.Rokhlin.local_moving_cancellation`.
-- source:
--   OpenAI, Rokhlin's multiple-mixing problem for one transformation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 145; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rokhlins-multiple-mixing-problem-for-one-transformation-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Dynamics/MultipleMixing at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ3Ro000
import Definitions.Def_OAIQ3Ro001

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_HilbertCodes
attribute [-instance] _root_.OAI.Rokhlin.StrongUnitary.measurableSpace _root_.OAI.Rokhlin.StrongUnitary.topology _root_.OAI.Rokhlin.submodule_completeSpace_inf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma exists_rayCanonical (t : ℕ → H) (ht : DenseRange t) {v : H} (hv : v ≠ 0) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ RayCanonical t (a • v) := by
  have hex := exists_inner_ne_zero_of_dense t ht hv
  let n := Nat.find hex
  let z := inner ℂ (t n) v
  have hz : z ≠ 0 := Nat.find_spec hex
  have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let a : ℂ := (‖z‖ : ℂ) / z
  have han : ‖a‖ = 1 := by
    dsimp [a]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hnz,div_self hnz.ne']
  refine ⟨a,han,n,?_,?_,?_⟩
  · intro m hm
    rw [inner_smul_right,not_ne_iff.mp (Nat.find_min hex hm),mul_zero]
  · have he : inner ℂ (t n) (a • v) = (‖z‖ : ℂ) := by
      rw [inner_smul_right]
      exact div_mul_cancel₀ _ hz
    rw [he,Complex.ofReal_re]
    exact hnz
  · have he : inner ℂ (t n) (a • v) = (‖z‖ : ℂ) := by
      rw [inner_smul_right]
      exact div_mul_cancel₀ _ hz
    rw [he,Complex.ofReal_im]

end

section
open MeasureTheory ProbabilityTheory Set Topology
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

variable {P U Y : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] {κ : Kernel U Y} [IsMarkovKernel κ]
  {u : P → U}

namespace HilbertCode

def atBase (q : HilbertCode κ) (a : U) (h : q.base = a) : Lp ℂ 2 (κ a) := h ▸ q.decode
end HilbertCode

def MeasurableSection (v : ∀ p, Lp ℂ 2 (κ (u p))) : Prop :=
  Measurable (fun p => HilbertCode.encode (u p) (v p))

end

section
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

attribute [local instance] OAI.Rokhlin.instMeasurableSpaceCircle_circleLp
lemma circleLp_norm [IsProbabilityMeasure μ] (f : X → Circle) (hf : Measurable f) :
    ‖circleLp μ f hf‖ = 1 := by
  have hn : ∀ᵐ x ∂μ, ‖circleLp μ f hf x‖ = ‖(1 : ℂ)‖ := by
    filter_upwards [circleLp_coe μ f hf] with x hx
    rw [hx,Circle.norm_coe,norm_one]
  rw [Lp.norm_def,eLpNorm_congr_norm_ae hn,eLpNorm_const (1 : ℂ) (by norm_num) (IsProbabilityMeasure.ne_zero μ)]
  simp

lemma circleLp_ne_zero [IsProbabilityMeasure μ] (f : X → Circle) (hf : Measurable f) :
    circleLp μ f hf ≠ 0 := by
  intro h
  have hn := circleLp_norm μ f hf
  simp only [h,norm_zero,zero_ne_one] at hn

end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)

omit [DecidableEq I] in
lemma normalized_exact_codes (p : P)
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (f : I → Y → Circle) (hf : ∀ i, Measurable (f i)) (c : Circle)
    (he : ∀ᵐ y ∂Λ p, ∏ i, f i (y i) = c) :
    ∃ (a : I → HilbertCode κ) (d : I → ℂ), (p,a) ∈ exactCodeSet κ Λ u ∧
      ∀ i, ‖d i‖ = 1 ∧ a i = HilbertCode.encode (u p i)
        (d i • circleLp (κ (u p i)) (f i) (hf i)) := by
  have hc (i) := exists_rayCanonical (hilbertTests (κ (u p i)))
    (hilbertTests_dense (κ (u p i))) (circleLp_ne_zero (κ (u p i)) (f i) (hf i))
  choose d hd hdcan using hc
  let a : I → HilbertCode κ := fun i => HilbertCode.encode (u p i)
    (d i • circleLp (κ (u p i)) (f i) (hf i))
  have hrepr (i) : (fun y => HilbertCode.representative (a i,y)) =ᵐ[κ (u p i)]
      (fun y => d i * (f i y : ℂ)) := by
    filter_upwards [HilbertCode.representative_eq_decode (a i),
      Lp.coeFn_smul (d i) (circleLp (κ (u p i)) (f i) (hf i)),
      circleLp_coe (κ (u p i)) (f i) (hf i)] with y h1 h2 h3
    change HilbertCode.representative (a i,y) =
      (HilbertCode.decode (HilbertCode.encode (u p i) (d i • circleLp (κ (u p i)) (f i) (hf i))) : Lp ℂ 2 (κ (u p i))) y at h1
    rw [HilbertCode.decode_encode] at h1
    exact h1.trans (h2.trans (congrArg (d i * ·) h3))
  have heprod : (fun y => ∏ i, HilbertCode.representative (a i,y i)) =ᵐ[Λ p]
      (fun _ => (∏ i, d i) * (c : ℂ)) := by
    filter_upwards [ae_all_iff.mpr (fun i => (hm i).quasiMeasurePreserving.ae_eq_comp (hrepr i)),he]
      with y hy he
    have hcoe : (∏ i, (f i (y i) : ℂ)) = (c : ℂ) :=
      (map_prod Circle.coeHom (fun i => f i (y i)) Finset.univ).symm.trans
        (congrArg (fun z : Circle => (z : ℂ)) he)
    calc
      (∏ i, HilbertCode.representative (a i,y i)) = ∏ i, d i * (f i (y i) : ℂ) :=
        Finset.prod_congr rfl (fun i _ => hy i)
      _ = (∏ i, d i) * (∏ i, (f i (y i) : ℂ)) := Finset.prod_mul_distrib
      _ = (∏ i, d i) * (c : ℂ) := congrArg ((∏ i, d i) * ·) hcoe
  refine ⟨a,d,⟨fun _ => rfl,?_,?_⟩,fun i => ⟨hd i,rfl⟩⟩
  · intro i
    constructor
    · change RayCanonical (hilbertTests (κ (u p i)))
        (HilbertCode.decode (HilbertCode.encode (u p i) (d i • circleLp (κ (u p i)) (f i) (hf i))))
      rw [HilbertCode.decode_encode]
      exact hdcan i
    · change ∀ᵐ y ∂κ (u p i), ‖HilbertCode.representative (a i,y)‖ = 1
      filter_upwards [hrepr i] with y hy
      rw [hy,norm_mul,hd i,Circle.norm_coe,one_mul]
  · change ‖∫ y, ∏ i, HilbertCode.representative (a i,y i) ∂Λ p‖ = 1
    rw [integral_congr_ae heprod,integral_const]
    simp only [probReal_univ,one_smul,norm_mul,norm_prod,hd,Finset.prod_const_one,
      Circle.norm_coe,one_mul]
end

section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp

lemma circleOfValue_coe {z : ℂ} (h : ‖z‖ = 1) : (circleOfValue z : ℂ) = z := by
  classical
  change (if ‖z‖ = 1 then z else (1 : ℂ)) = z
  exact ite_eq_left h

variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)

namespace HilbertCode
variable {κ}
lemma circleRep_coe (q : HilbertCode κ) (y : Y)
    (h : ‖representative (κ := κ) (q,y)‖ = 1) :
    (circleRep (κ := κ) q y : ℂ) = representative (κ := κ) (q,y) :=
  circleOfValue_coe (z := representative (κ := κ) (q,y)) h
lemma circleRep_ae (q : HilbertCode κ) (hq : IsUnimodular q) :
    (fun y => (circleRep (κ := κ) q y : ℂ)) =ᵐ[κ q.base] (fun y => representative (κ := κ) (q,y)) :=
  hq.mono fun _ h => circleOfValue_coe h
end HilbertCode

omit [DecidableEq I] in
lemma exactCode_circle_tuple {p : P} {a : I → HilbertCode κ}
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (ha : (p,a) ∈ exactCodeSet κ Λ u) :
    ∃ c : Circle, ∀ᵐ y ∂Λ p, ∏ i, HilbertCode.circleRep (κ := κ) (a i) (y i) = c := by
  let c : Circle := ⟨exactCodeMean κ Λ (p,a),mem_sphere_zero_iff_norm.mpr ha.2.2⟩
  have hn (i) : ∀ᵐ y ∂Λ p, ‖HilbertCode.representative (κ := κ) (a i,y i)‖ = 1 := by
    have h : ∀ᵐ y ∂κ (u p i), ‖HilbertCode.representative (κ := κ) (a i,y)‖ = 1 := by
      rw [←ha.1 i]
      exact (ha.2.1 i).2
    exact (hm i).quasiMeasurePreserving.ae h
  have hnp : ∀ᵐ y ∂Λ p, ‖∏ i, HilbertCode.representative (κ := κ) (a i,y i)‖ = 1 :=
    HilbertCode.ae_norm_prod_representative (κ := κ) (Λ p) a hn
  have hmean : ‖∫ y, ∏ i, HilbertCode.representative (κ := κ) (a i,y i) ∂Λ p‖ = 1 := ha.2.2
  have he : (fun y => ∏ i, HilbertCode.representative (κ := κ) (a i,y i)) =ᵐ[Λ p]
      (fun _ => exactCodeMean κ Λ (p,a)) :=
    ae_eq_mean_of_norm_mean_eq_one (μ := Λ p) _ hnp hmean
  refine ⟨c,?_⟩
  filter_upwards [he,ae_all_iff.mpr hn] with y hy hn
  apply Circle.coe_injective
  change ((∏ i, HilbertCode.circleRep (κ := κ) (a i) (y i) : Circle) : ℂ) = exactCodeMean κ Λ (p,a)
  change Circle.coeHom (∏ i, HilbertCode.circleRep (κ := κ) (a i) (y i)) = _
  rw [map_prod]
  exact (Finset.prod_congr rfl (fun i _ => HilbertCode.circleRep_coe (κ := κ) (a i) (y i) (hn i))).trans hy
end

namespace HilbertCode

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] {κ : Kernel U Y} [IsMarkovKernel κ]

lemma unitPhase_norm (q : UnitCode κ) : ‖unitPhase q‖ = 1 := by
  have hz : coefficient q.val (firstCoefficient q) ≠ 0 := Nat.find_spec (unitCode_exists_coefficient q)
  simp only [unitPhase,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_norm]
  exact div_self (norm_ne_zero_iff.mpr hz)

lemma unitPhase_canonical (q : UnitCode κ) :
    RayCanonical (hilbertTests (κ q.val.base)) (unitPhase q • q.val.decode) := by
  have hz : coefficient q.val (firstCoefficient q) ≠ 0 := Nat.find_spec (unitCode_exists_coefficient q)
  refine ⟨firstCoefficient q,?_,?_,?_⟩
  · intro n hn
    rw [inner_smul_right,←coefficient_eq]
    rw [not_ne_iff.mp (Nat.find_min (unitCode_exists_coefficient q) hn),mul_zero]
  · rw [inner_smul_right,←coefficient_eq]
    unfold unitPhase
    rw [div_mul_cancel₀ _ hz,Complex.ofReal_re]
    exact norm_pos_iff.mpr hz
  · rw [inner_smul_right,←coefficient_eq]
    unfold unitPhase
    rw [div_mul_cancel₀ _ hz,Complex.ofReal_im]

lemma normalizeUnit_canonical (q : UnitCode κ) : (normalizeUnit q).IsCanonical := by
  change RayCanonical _ (decode (encode _ _))
  rw [decode_encode]
  exact unitPhase_canonical q

lemma normalizeUnit_representative (q : UnitCode κ) :
    (fun y => representative (normalizeUnit q,y)) =ᵐ[κ q.val.base]
      fun y => unitPhase q * representative (q.val,y) := by
  have hr := representative_eq_decode (normalizeUnit q)
  change (fun y => representative (normalizeUnit q,y)) =ᵐ[κ q.val.base]
    fun y => (decode (encode _ (unitPhase q • q.val.decode)) : Lp ℂ 2 (κ q.val.base)) y at hr
  rw [decode_encode] at hr
  filter_upwards [hr,Lp.coeFn_smul (unitPhase q) q.val.decode,representative_eq_decode q.val]
    with y h1 h2 h3
  exact h1.trans (h2.trans (congrArg (unitPhase q * ·) h3.symm))

lemma normalizeUnit_unimodular (q : UnitCode κ) : (normalizeUnit q).IsUnimodular := by
  filter_upwards [normalizeUnit_representative q,q.property] with y h1 h2
  rw [h1,norm_mul,unitPhase_norm,h2,mul_one]

lemma transport_base (F : U → U) (E : Y ≃ᵐ Y) (q : HilbertCode κ) :
    (transport F E q).base = F q.base := rfl
lemma transport_canonical (F : U → U) (E : Y ≃ᵐ Y) (q : HilbertCode κ) :
    (transport F E q).IsCanonical := normalizeUnit_canonical _
lemma transport_unimodular (F : U → U) (E : Y ≃ᵐ Y) (q : HilbertCode κ) :
    (transport F E q).IsUnimodular := normalizeUnit_unimodular _

lemma transport_representative (F : U → U) (E : Y ≃ᵐ Y) (q : HilbertCode κ)
    (hq : q.IsUnimodular)
    (hE : MeasurePreserving E (κ q.base) (κ (F q.base))) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ (fun y => representative (transport F E q,y)) =ᵐ[κ (F q.base)]
      (fun y => c * representative (q,E.symm y)) := by
  let r : UnitCode κ := ⟨transportRaw F E q,transportRaw_unimodular F E q⟩
  refine ⟨unitPhase r,unitPhase_norm r,?_⟩
  have hinv := MeasurePreserving.symm E hE
  have hrep := hinv.quasiMeasurePreserving.ae (circleRep_ae q hq)
  filter_upwards [normalizeUnit_representative r,transportRaw_representative F E q,hrep]
    with y h1 h2 h3
  exact h1.trans (congrArg (unitPhase r * ·) (h2.trans h3))

lemma transport_inverse (F : U ≃ᵐ U) (E : Y ≃ᵐ Y) (q : HilbertCode κ)
    (hq : q.IsUnimodular) (hc : q.IsCanonical)
    (hE : MeasurePreserving E (κ q.base) (κ (F q.base))) :
    transport F.symm E.symm (transport F E q) = q := by
  have hinv : MeasurePreserving E.symm (κ (transport F E q).base)
      (κ (F.symm (transport F E q).base)) := by
    simpa only [transport_base,F.symm_apply_apply] using MeasurePreserving.symm E hE
  obtain ⟨c,hc1,hr⟩ := transport_representative F E q hq hE
  obtain ⟨d,hd1,hs⟩ := transport_representative F.symm E.symm (transport F E q)
    (transport_unimodular F E q) hinv
  have hs' : (fun y => representative (transport F.symm E.symm (transport F E q),y)) =ᵐ[κ q.base]
      (fun y => d * representative (transport F E q,E y)) := by
    simpa only [transport_base,F.symm_apply_apply,MeasurableEquiv.symm_symm] using hs
  apply eq_of_decode_smul (by simp only [transport_base,F.symm_apply_apply])
    (transport_canonical _ _ _) hc (a := d*c) (by rw [norm_mul,hd1,hc1,mul_one])
  simp only [transport_base,F.symm_apply_apply]
  filter_upwards [hs',hE.quasiMeasurePreserving.ae hr] with y h1 h2
  rw [h1,h2,E.symm_apply_apply,mul_assoc]
end HilbertCode

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)

omit [IsMarkovKernel Λ] in

lemma exactCode_transport (F : U → U) (E : Y ≃ᵐ Y) (p p' : P)
    (hu : ∀ i, u p' i = F (u p i))
    (hκ : ∀ i, MeasurePreserving E (κ (u p i)) (κ (F (u p i))))
    (hΛ : MeasurePreserving (fun y : I → Y => fun i => E (y i)) (Λ p) (Λ p'))
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (q : I → HilbertCode κ) (hq : (p,q) ∈ exactCodeSet κ Λ u) :
    (p',fun i => HilbertCode.transport F E (q i)) ∈ exactCodeSet κ Λ u := by
  classical
  have hkq (i) : MeasurePreserving E (κ (q i).base) (κ (F (q i).base)) := by
    rw [hq.1 i]; exact hκ i
  choose c hc hrep using fun i => HilbertCode.transport_representative F E (q i) (hq.2.1 i).2 (hkq i)
  refine ⟨fun i => by rw [HilbertCode.transport_base,hq.1 i,hu i],
    fun i => ⟨HilbertCode.transport_canonical _ _ _,HilbertCode.transport_unimodular _ _ _⟩,?_⟩
  have hr (i) : ∀ᵐ y ∂Λ p,
      HilbertCode.representative (HilbertCode.transport F E (q i),E (y i)) =
      c i * HilbertCode.representative (q i,y i) := by
    have hh := (hkq i).quasiMeasurePreserving.ae (hrep i)
    have hh' : ∀ᵐ y ∂κ (u p i),
        HilbertCode.representative (HilbertCode.transport F E (q i),E y) =
          c i * HilbertCode.representative (q i,y) := by
      rw [←hq.1 i]
      simpa only [E.symm_apply_apply] using hh
    exact (hm i).quasiMeasurePreserving.ae hh'
  have he : (fun y : I → Y => ∏ i, HilbertCode.representative
      (HilbertCode.transport F E (q i),E (y i))) =ᵐ[Λ p]
      (fun y => (∏ i, c i) * ∏ i, HilbertCode.representative (q i,y i)) := by
    filter_upwards [ae_all_iff.mpr hr] with y hy
    rw [←Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => hy i)
  have hmeas : AEStronglyMeasurable (fun y : I → Y => ∏ i,
      HilbertCode.representative (HilbertCode.transport F E (q i),y i)) (Λ p') := by
    apply Measurable.aestronglyMeasurable
    apply Finset.measurable_prod
    intro i _
    exact HilbertCode.measurable_representative.comp (measurable_const.prodMk (measurable_pi_apply i))
  change ‖∫ y, ∏ i, HilbertCode.representative (HilbertCode.transport F E (q i),y i) ∂Λ p'‖ = 1
  rw [←hΛ.hasLaw.integral_comp hmeas]
  simp only [Function.comp_def]
  rw [integral_congr_ae he,integral_const_mul,norm_mul]
  have hn : ‖∏ i, c i‖ = 1 := by rw [norm_prod]; simp only [hc,Finset.prod_const_one]
  rw [hn,one_mul]
  exact hq.2.2

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Joinings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section

namespace TriplePartition
variable {I : Type*} [Fintype I] [DecidableEq I] (s : TriplePartition I)
lemma card_eq : s.P.card + s.A.card + s.B.card = Fintype.card I := by
  rw [← Finset.card_union_of_disjoint s.disjointPA,
    ← Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨s.disjointPB,s.disjointAB⟩),
    s.cover,Finset.card_univ]
lemma cardP : s.P.card + 2 ≤ Fintype.card I := by
  have := s.card_eq
  have := Finset.card_pos.mpr s.nonemptyA
  have := Finset.card_pos.mpr s.nonemptyB
  omega
end TriplePartition

open MeasureTheory
end

namespace StrongUnitary
open MeasureTheory Filter Topology
open scoped Topology
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SecondCountableTopology E]

instance borelSpace : BorelSpace (E ≃ₗᵢ[ℂ] H) := ⟨rfl⟩

end StrongUnitary

section
open MeasureTheory ProbabilityTheory ContinuousLinearMap
variable {Ω Z X Y C D H₁ H₂ H₃ H₄ : Type*}
  [MeasurableSpace Ω] [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace C] [MeasurableSpace D]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [SecondCountableTopology H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] [SecondCountableTopology H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃] [SecondCountableTopology H₃]
  [NormedAddCommGroup H₄] [InnerProductSpace ℂ H₄] [CompleteSpace H₄] [SecondCountableTopology H₄]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {μX : Measure X} {μY : Measure Y} {μC : Measure C} {μD : Measure D}
  [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
  [IsProbabilityMeasure μC] [IsProbabilityMeasure μD]
  {x : Ω → X} {y : Ω → Y} {c : Ω → C} {d : Ω → D}
  {F : X → H₂ →L[ℂ] H₁} {G : Y → H₄ →L[ℂ] H₃}
  {K : C → H₃ →L[ℂ] H₁} {N : D → H₄ →L[ℂ] H₂}

def MeasurablePolarRectangle.HasHaarNormalization
    (R : MeasurablePolarRectangle μ μX μY μC μD F G K N x y c d) : Prop :=
  ∃ (a₀ : H₂ ≃ₗᵢ[ℂ] H₁) (b₀ : H₄ ≃ₗᵢ[ℂ] H₃) (d₀ : H₄ ≃ₗᵢ[ℂ] H₂)
    (S : Subgroup (H₄ ≃ₗᵢ[ℂ] H₄)),
    IsClosed (S : Set (H₄ ≃ₗᵢ[ℂ] H₄)) ∧
    (μX.map R.a.unitary).map (StrongUnitary.normalizeA a₀ d₀) =
      (μY.map R.b.unitary).map (StrongUnitary.normalizeB b₀) ∧
    (μC.map R.p.unitary).map (StrongUnitary.normalizeC a₀ b₀ d₀) =
      (μD.map R.q.unitary).map (StrongUnitary.normalizeD d₀) ∧
    ((μX.map R.a.unitary).map (StrongUnitary.normalizeA a₀ d₀)).support = S ∧
    ((μC.map R.p.unitary).map (StrongUnitary.normalizeC a₀ b₀ d₀)).support = S ∧
    (∀ u ∈ S, ∀ v ∈ S, u * v = v * u) ∧
    (∀ u ∈ S, ((μX.map R.a.unitary).map (StrongUnitary.normalizeA a₀ d₀)).map (u * ·) =
      (μX.map R.a.unitary).map (StrongUnitary.normalizeA a₀ d₀))

end

namespace TriplePartition
variable {I : Type*} [Fintype I] [DecidableEq I]
abbrev swapPA (s : TriplePartition I) : TriplePartition I where
  P := s.A
  A := s.P
  B := s.B
  nonemptyP := s.nonemptyA
  nonemptyA := s.nonemptyP
  nonemptyB := s.nonemptyB
  disjointPA := s.disjointPA.symm
  disjointPB := s.disjointAB
  disjointAB := s.disjointPB
  cover := by simpa only [Finset.union_comm s.A s.P] using s.cover

abbrev swapAB (s : TriplePartition I) : TriplePartition I where
  P := s.P
  A := s.B
  B := s.A
  nonemptyP := s.nonemptyP
  nonemptyA := s.nonemptyB
  nonemptyB := s.nonemptyA
  disjointPA := s.disjointPB
  disjointPB := s.disjointPA
  disjointAB := s.disjointAB.symm
  cover := by simpa only [Finset.union_assoc,Finset.union_comm s.B s.A] using s.cover

abbrev swapPB (s : TriplePartition I) : TriplePartition I where
  P := s.B
  A := s.A
  B := s.P
  nonemptyP := s.nonemptyB
  nonemptyA := s.nonemptyA
  nonemptyB := s.nonemptyP
  disjointPA := s.disjointAB.symm
  disjointPB := s.disjointPB.symm
  disjointAB := s.disjointPA.symm
  cover := by simpa only [Finset.union_assoc,Finset.union_left_comm,Finset.union_comm] using s.cover
end TriplePartition

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Tensors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

namespace JoiningOperator
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped InnerProductSpace ENNReal
variable {Ω U X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure Ω}
  {η : Measure U} {ν : Measure X} {ρ : Measure Y}
  {u : Ω → U} {x : Ω → X} {y : Ω → Y}
  [SFinite η] [SFinite ρ]

def contraction (hx : MeasurePreserving x μ ν)
    (huy : MeasurePreserving (fun ω => (u ω, y ω)) μ (η.prod ρ))
    (g : Lp ℂ 2 η) (h : Lp ℂ 2 ρ) : Lp ℂ 2 ν :=
  operator hx huy (tensorLp g h)

end JoiningOperator


end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_ExactLines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
variable {I : Type*} [Fintype I] [DecidableEq I]

namespace ComplementSplit
variable {P : Finset I}
abbrev partition (s : ComplementSplit P) : TriplePartition I :=
  ⟨P,s.A,s.B,s.nonemptyP,s.nonemptyA,s.nonemptyB,s.disjointPA,s.disjointPB,s.disjointAB,s.cover⟩

def singleton (P : Finset I) (hP : P.Nonempty) (s : I) (hs : s ∉ P)
    (hb : (P ∪ {s})ᶜ.Nonempty) : ComplementSplit P where
  A := {s}
  B := (P ∪ {s})ᶜ
  nonemptyP := hP
  nonemptyA := Finset.singleton_nonempty s
  nonemptyB := hb
  disjointPA := Finset.disjoint_singleton_right.mpr hs
  disjointPB := Finset.disjoint_left.mpr (by
    intro i hi hh
    exact Finset.mem_compl.mp hh (Finset.mem_union_left _ hi))
  disjointAB := Finset.disjoint_left.mpr (by
    intro i hi hh
    exact Finset.mem_compl.mp hh (Finset.mem_union_right _ hi))
  cover := Finset.union_compl _

end ComplementSplit
end

namespace ComplementSplit
variable {I : Type*} [Fintype I] [DecidableEq I] {R : Finset I}

lemma two_le_card_compl (s : ComplementSplit R) : 2 ≤ Rᶜ.card := by
  have h := s.partition.cardP
  change R.card + 2 ≤ Fintype.card I at h
  have hc := Finset.card_compl R
  omega

lemma rest_nonempty (s : ComplementSplit R) (i : ↥(Rᶜ)) : (R ∪ {(i : I)})ᶜ.Nonempty := by
  obtain ⟨j,hj,hji⟩ := Finset.exists_mem_ne (by have := two_le_card_compl s; omega : 1 < Rᶜ.card) (i : I)
  refine ⟨j,?_⟩
  simp only [Finset.mem_compl,Finset.mem_union,Finset.mem_singleton,not_or] at *
  exact ⟨hj,hji⟩

abbrev singletonFor (s : ComplementSplit R) (i : ↥(Rᶜ)) : ComplementSplit R :=
  ComplementSplit.singleton R s.nonemptyP i (Finset.mem_compl.mp i.property) (rest_nonempty s i)

end ComplementSplit

section
open MeasureTheory ProbabilityTheory Set
variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U) (hu : Measurable u)

def productTupleKernel : Kernel P (I → Y) :=
  FiniteKernel.pi (fun i => κ.comap (fun p => u p i) ((measurable_pi_apply i).comp hu))
instance instIsMarkovKernelForallProductTupleKernel : IsMarkovKernel (productTupleKernel κ u hu) := inferInstanceAs (IsMarkovKernel (FiniteKernel.pi _))

end

section
open MeasureTheory ProbabilityTheory Set
variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y))
  (u : P → I → U)

def exactCodeEquivTransport (F : U ≃ᵐ U) (E : Y ≃ᵐ Y) (p p' : P)
    (hu : ∀ i, u p' i = F (u p i))
    (hκ : ∀ i, MeasurePreserving E (κ (u p i)) (κ (F (u p i))))
    (hΛ : MeasurePreserving (fun y : I → Y => fun i => E (y i)) (Λ p) (Λ p'))
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hm' : ∀ i, MeasurePreserving (fun y : I → Y => y i) (Λ p') (κ (u p' i))) :
    {q : I → HilbertCode κ // (p,q) ∈ exactCodeSet κ Λ u} ≃
      {q : I → HilbertCode κ // (p',q) ∈ exactCodeSet κ Λ u} := by
  have hu' (i) : u p i = F.symm (u p' i) := by rw [hu i,F.symm_apply_apply]
  have hκ' (i) : MeasurePreserving E.symm (κ (u p' i)) (κ (F.symm (u p' i))) := by
    rw [hu i,F.symm_apply_apply]
    exact MeasurePreserving.symm E (hκ i)
  have hΛ' : MeasurePreserving (fun y : I → Y => fun i => E.symm (y i)) (Λ p') (Λ p) :=
    MeasurePreserving.symm (MeasurableEquiv.piCongrRight (fun _ : I => E)) hΛ
  refine {
    toFun := fun q => ⟨fun i => HilbertCode.transport F E (q.val i),
      exactCode_transport κ Λ u F E p p' hu hκ hΛ hm q.val q.property⟩
    invFun := fun q => ⟨fun i => HilbertCode.transport F.symm E.symm (q.val i),
      exactCode_transport κ Λ u F.symm E.symm p' p hu' hκ' hΛ' hm' q.val q.property⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro q
    apply Subtype.ext
    funext i
    apply HilbertCode.transport_inverse F E (q.val i) (q.property.2.1 i).2 (q.property.2.1 i).1
    rw [q.property.1 i]
    exact hκ i
  · intro q
    apply Subtype.ext
    funext i
    have h := HilbertCode.transport_inverse F.symm E.symm (q.val i)
      (q.property.2.1 i).2 (q.property.2.1 i).1
    apply h
    rw [q.property.1 i]
    exact hκ' i
end

section
open MeasureTheory Set
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable (Y : Type*) [MeasurableSpace Y]

instance measurableCircleCoeFun : CoeFun (MeasurableCircle Y) (fun _ => Y → Circle) := ⟨fun f => f.val⟩
lemma measurableCircle_measurable (f : MeasurableCircle Y) : Measurable (f : Y → Circle) := f.property
variable {Y} (μ : Measure Y)

lemma projectiveCircle_eq_iff (f g : Y → Circle) (hf : Measurable f) (hg : Measurable g) :
    projectiveCircle μ f hf = projectiveCircle μ g hg ↔
      ∃ c : Circle, f =ᵐ[μ] fun y => c*g y := by
  change (QuotientGroup.mk (⟨f,hf⟩ : MeasurableCircle Y) =
    QuotientGroup.mk (⟨g,hg⟩ : MeasurableCircle Y)) ↔ _
  rw [QuotientGroup.eq]
  change (∃ c : Circle, (fun y => (f y)⁻¹ * g y) =ᵐ[μ] fun _ => c) ↔ _
  constructor
  · rintro ⟨c,hc⟩
    refine ⟨c⁻¹,?_⟩
    filter_upwards [hc] with y hy
    apply eq_inv_mul_iff_mul_eq.mpr
    exact (mul_comm c (f y)).trans (inv_mul_eq_iff_eq_mul.mp hy).symm
  · rintro ⟨c,hc⟩
    refine ⟨c⁻¹,?_⟩
    filter_upwards [hc] with y hy
    rw [hy,mul_inv_rev]
    simp [mul_comm]

lemma projectiveCircle_one : projectiveCircle μ (fun _ : Y => 1) measurable_const = 1 := rfl
end

section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {Y I : Type*} [MeasurableSpace Y] [Fintype I]

def exactCircleTuples (μ : Measure (I → Y)) : Subgroup (I → MeasurableCircle Y) where
  carrier := {f | ∃ c : Circle, ∀ᵐ y ∂μ, ∏ i, f i (y i) = c}
  one_mem' := ⟨1,Filter.Eventually.of_forall fun _ => by simp⟩
  mul_mem' := by
    rintro f g ⟨c,hc⟩ ⟨d,hd⟩
    refine ⟨c*d,?_⟩
    filter_upwards [hc,hd] with y hy hz
    change (∏ i, f i (y i) * g i (y i)) = c*d
    rw [Finset.prod_mul_distrib,hy,hz]
  inv_mem' := by
    rintro f ⟨c,hc⟩
    refine ⟨c⁻¹,?_⟩
    filter_upwards [hc] with y hy
    change (∏ i, (f i (y i))⁻¹) = c⁻¹
    rw [Finset.prod_inv_distrib,hy]

def tupleProjectivize (ν : I → Measure Y) : (I → MeasurableCircle Y) →*
    (∀ i, ProjectiveCircle (ν i)) where
  toFun := fun f i => QuotientGroup.mk (f i)
  map_one' := rfl
  map_mul' := fun _ _ => rfl

def exactProjectiveTuples (μ : Measure (I → Y)) (ν : I → Measure Y) :
    Subgroup (∀ i, ProjectiveCircle (ν i)) :=
  (exactCircleTuples μ).map (tupleProjectivize ν)

def exactProjectiveSlot (μ : Measure (I → Y)) (ν : I → Measure Y) (i : I) :
    exactProjectiveTuples μ ν →* ProjectiveCircle (ν i) where
  toFun := fun a => a.val i
  map_one' := rfl
  map_mul' := fun _ _ => rfl

variable [DecidableEq I]
lemma exactCircleTuples_constant_of_slot (hk : 3 ≤ Fintype.card I)
    (μ : Measure (I → Y)) [IsProbabilityMeasure μ] (ν : I → Measure Y)
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) μ (ν i))
    (hind : ∀ i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) μ)
    (f : I → MeasurableCircle Y) (hf : f ∈ exactCircleTuples μ)
    (i : I) (hi : projectiveCircle (ν i) (f i) (measurableCircle_measurable Y (f i)) = 1) :
    ∀ j, projectiveCircle (ν j) (f j) (measurableCircle_measurable Y (f j)) = 1 := by
  have hpm (j : I) : Measurable (fun y : I → Y => (f j (y j) : ℂ)) :=
    measurable_subtype_coe.comp ((measurableCircle_measurable Y (f j)).comp (measurable_pi_apply j))
  have hpn (j : I) : ∀ᵐ y ∂μ, ‖(f j (y j) : ℂ)‖ = 1 :=
    Filter.Eventually.of_forall fun _ => Circle.norm_coe _
  have hpi (j : I) : iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Y => (f t (y t) : ℂ)) μ :=
    (hind j).comp (fun t y => (f t y : ℂ))
      (fun t => measurable_subtype_coe.comp (measurableCircle_measurable Y (f t)))
  obtain ⟨c,hc⟩ := hf
  have hc' : ∀ᵐ y ∂μ, ∏ j, (f j (y j) : ℂ) = (c : ℂ) := by
    filter_upwards [hc] with y hy
    exact (map_prod Circle.coeHom _ _).symm.trans (congrArg (fun a : Circle => (a : ℂ)) hy)
  have hx := exact_tuple_dichotomy hk (fun j (y : I → Y) => (f j (y j) : ℂ))
    (fun j => (hpm j).aestronglyMeasurable) hpn hpi (c : ℂ) (Circle.norm_coe c) hc'
  have hi' : ∃ d : Circle, (f i : Y → Circle) =ᵐ[ν i] fun _ => d := by
    rw [←projectiveCircle_one (ν i),projectiveCircle_eq_iff] at hi
    simpa only [mul_one] using hi
  obtain ⟨d,hd⟩ := hi'
  have hdi : (fun y : I → Y => (f i (y i) : ℂ)) =ᵐ[μ] fun _ => (d : ℂ) :=
    ((hm i).quasiMeasurePreserving.ae_eq_comp hd).mono fun _ h => congrArg (fun a : Circle => (a : ℂ)) h
  rcases hx with hz | he
  · have hh := hz i
    rw [integral_congr_ae hdi,integral_const,probReal_univ,one_smul] at hh
    have hn := Circle.norm_coe d
    rw [hh,norm_zero] at hn
    norm_num at hn
  · intro j
    let a : Circle := ⟨∫ y, (f j (y j) : ℂ) ∂μ,mem_sphere_zero_iff_norm.mpr (he j).2⟩
    have hj : ∀ᵐ y ∂μ, f j (y j) = a :=
      (he j).1.mono fun _ h => Circle.coe_injective h
    have hj' : (f j : Y → Circle) =ᵐ[ν j] fun _ => a := by
      rw [←(hm j).map_eq]
      apply (ae_map_iff (hm j).measurable.aemeasurable
        (measurableSet_eq_fun (measurableCircle_measurable Y (f j)) measurable_const)).mpr
      exact hj
    rw [←projectiveCircle_one (ν j),projectiveCircle_eq_iff]
    exact ⟨a,by simpa only [mul_one] using hj'⟩
lemma exactProjectiveSlot_injective (hk : 3 ≤ Fintype.card I)
    (μ : Measure (I → Y)) [IsProbabilityMeasure μ] (ν : I → Measure Y)
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) μ (ν i))
    (hind : ∀ i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) μ) (i : I) :
    Function.Injective (exactProjectiveSlot μ ν i) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  obtain ⟨f,hf,hfa⟩ := a.property
  have hi : projectiveCircle (ν i) (f i) (measurableCircle_measurable Y (f i)) = 1 := by
    change tupleProjectivize ν f i = 1
    rw [hfa]
    exact ha
  apply Subtype.ext
  funext j
  have hj := exactCircleTuples_constant_of_slot hk μ ν hm hind f hf i hi j
  change (a : ∀ j, ProjectiveCircle (ν j)) j = 1
  rw [←hfa]
  exact hj

def exactProjectiveMatching (hk : 3 ≤ Fintype.card I)
    (μ : Measure (I → Y)) [IsProbabilityMeasure μ] (ν : I → Measure Y)
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) μ (ν i))
    (hind : ∀ i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) μ) (i j : I) :
    (exactProjectiveSlot μ ν i).range ≃* (exactProjectiveSlot μ ν j).range :=
  (MonoidHom.ofInjective (exactProjectiveSlot_injective hk μ ν hm hind i)).symm.trans
    (MonoidHom.ofInjective (exactProjectiveSlot_injective hk μ ν hm hind j))
end

section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)
namespace HilbertCode
variable {κ}

lemma projective_injective {u : U} {q r : HilbertCode κ}
    (hbq : q.base = u) (hbr : r.base = u)
    (hcq : q.IsCanonical) (hcr : r.IsCanonical)
    (huq : q.IsUnimodular) (hur : r.IsUnimodular)
    (he : projective u q = projective u r) : q = r := by
  obtain ⟨c,hc⟩ := (projectiveCircle_eq_iff (κ u) _ _ _ _).mp he
  have hq := circleRep_ae q huq
  have hr := circleRep_ae r hur
  rw [hbq] at hq
  rw [hbr] at hr
  apply eq_of_decode_smul (hbq.trans hbr.symm) hcq hcr (Circle.norm_coe c)
  rw [hbq]
  filter_upwards [hc,hq,hr] with y hy hqy hry
  rw [←hqy,hy]
  change (c : ℂ) * (circleRep r y : ℂ) = (c : ℂ) * representative (r,y)
  rw [hry]

lemma projective_encode_phase {u : U} (f : Y → Circle) (hf : Measurable f)
    (d : ℂ) (hd : ‖d‖ = 1) (q : HilbertCode κ)
    (he : q = encode u (d • circleLp (κ u) f hf)) (hu : q.IsUnimodular) :
    projective u q = projectiveCircle (κ u) f hf := by
  let c : Circle := ⟨d,mem_sphere_zero_iff_norm.mpr hd⟩
  apply (projectiveCircle_eq_iff (κ u) _ _ _ _).mpr
  refine ⟨c,?_⟩
  have hb : q.base = u := by rw [he]; rfl
  have hr := representative_eq_decode (encode u (d • circleLp (κ u) f hf))
  change (fun y => representative (encode u (d • circleLp (κ u) f hf),y)) =ᵐ[κ u]
    fun y => (decode (encode u (d • circleLp (κ u) f hf)) : Lp ℂ 2 (κ u)) y at hr
  rw [decode_encode] at hr
  have hcircle := circleRep_ae q hu
  rw [hb] at hcircle
  filter_upwards [hcircle,hr,Lp.coeFn_smul d (circleLp (κ u) f hf),circleLp_coe (κ u) f hf]
    with y h1 h2 h3 h4
  apply Circle.coe_injective
  change (circleRep q y : ℂ) = d * (f y : ℂ)
  exact h1.trans ((congrArg (fun z : HilbertCode κ => representative (z,y)) he).trans
    (h2.trans (h3.trans (congrArg (d * ·) h4))))
end HilbertCode

omit [DecidableEq I] in
lemma exact_code_projective_mem {p : P} {a : I → HilbertCode κ}
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (ha : (p,a) ∈ exactCodeSet κ Λ u) :
    (fun i => HilbertCode.projective (u p i) (a i)) ∈
      exactProjectiveTuples (Λ p) (fun i => κ (u p i)) := by
  obtain ⟨c,hc⟩ := exactCode_circle_tuple κ Λ u hm ha
  refine ⟨(fun i => ⟨HilbertCode.circleRep (a i),HilbertCode.measurable_circleRep_fixed (a i)⟩),?_,rfl⟩
  exact ⟨c,hc⟩

omit [DecidableEq I] in
lemma exact_projective_has_codes (p : P)
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (v : exactProjectiveTuples (Λ p) (fun i => κ (u p i))) :
    ∃ a : I → HilbertCode κ, (p,a) ∈ exactCodeSet κ Λ u ∧
      ∀ i, HilbertCode.projective (u p i) (a i) = v.val i := by
  obtain ⟨f,hf,hfv⟩ := v.property
  obtain ⟨c,hc⟩ := hf
  obtain ⟨a,d,ha,hd⟩ := normalized_exact_codes κ Λ u p hm
    (fun i => f i) (fun i => (measurableCircle_measurable Y (f i))) c hc
  refine ⟨a,ha,?_⟩
  intro i
  have he := HilbertCode.projective_encode_phase (κ := κ) (f i) (measurableCircle_measurable Y (f i))
    (d i) (hd i).1 (a i) (hd i).2 (ha.2.1 i).2
  exact he.trans (congrFun hfv i)
end

section
open MeasureTheory ProbabilityTheory Set
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)

omit [DecidableEq I] in
lemma codeSlot_projective_range (p : P)
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i))) (i : I) :
    {g : ProjectiveCircle (κ (u p i)) | ∃ q : ExactCodeSlot κ Λ u p i,
      HilbertCode.projective (u p i) q.val = g} =
      (exactProjectiveSlot (Λ p) (fun j => κ (u p j)) i).range := by
  ext g
  constructor
  · rintro ⟨q,hq⟩
    obtain ⟨a,ha,hai⟩ := q.property
    let v : exactProjectiveTuples (Λ p) (fun j => κ (u p j)) :=
      ⟨fun j => HilbertCode.projective (u p j) (a j),exact_code_projective_mem κ Λ u hm ha⟩
    exact ⟨v,by change HilbertCode.projective (u p i) (a i) = g; rw [hai,hq]⟩
  · rintro ⟨v,hv⟩
    obtain ⟨a,ha,he⟩ := exact_projective_has_codes κ Λ u p hm v
    exact ⟨⟨a i,a,ha,rfl⟩,(he i).trans hv⟩

omit [DecidableEq I] [IsMarkovKernel Λ] in
lemma codeSlot_projective_injective (p : P) (i : I) :
    Function.Injective (fun q : ExactCodeSlot κ Λ u p i => HilbertCode.projective (u p i) q.val) := by
  intro q r he
  obtain ⟨a,ha,hai⟩ := q.property
  obtain ⟨b,hb,hbi⟩ := r.property
  apply Subtype.ext
  change HilbertCode.projective (u p i) q.val = HilbertCode.projective (u p i) r.val at he
  rw [←hai,←hbi] at he ⊢
  exact HilbertCode.projective_injective (ha.1 i) (hb.1 i)
    (ha.2.1 i).1 (hb.2.1 i).1 (ha.2.1 i).2 (hb.2.1 i).2 he

def codeSlotEquivProjective (p : P)
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i))) (i : I) :
    ExactCodeSlot κ Λ u p i ≃ (exactProjectiveSlot (Λ p) (fun j => κ (u p j)) i).range := by
  let f : ExactCodeSlot κ Λ u p i →
      (exactProjectiveSlot (Λ p) (fun j => κ (u p j)) i).range := fun q =>
    ⟨HilbertCode.projective (u p i) q.val,by
      exact (Set.ext_iff.mp (codeSlot_projective_range κ Λ u p hm i) _).mp ⟨q,rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro q r he
    exact codeSlot_projective_injective κ Λ u p i (congrArg Subtype.val he)
  · intro v
    have hv := v.property
    have hv := (Set.ext_iff.mp (codeSlot_projective_range κ Λ u p hm i) v.val).mpr hv
    obtain ⟨q,hq⟩ := hv
    exact ⟨q,Subtype.ext hq⟩

end

section
open MeasureTheory ProbabilityTheory Set
variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y))
  (u : P → I → U)

lemma exactSlot_transport (F : U → U) (E : Y ≃ᵐ Y) (p p' : P)
    (hu : ∀ i, u p' i = F (u p i))
    (hκ : ∀ i, MeasurePreserving E (κ (u p i)) (κ (F (u p i))))
    (hΛ : MeasurePreserving (fun y : I → Y => fun i => E (y i)) (Λ p) (Λ p'))
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (i : I) (q : HilbertCode κ)
    (hq : ∃ a : I → HilbertCode κ, (p,a) ∈ exactCodeSet κ Λ u ∧ a i = q) :
    ∃ a : I → HilbertCode κ, (p',a) ∈ exactCodeSet κ Λ u ∧ a i = HilbertCode.transport F E q := by
  obtain ⟨a,ha,hai⟩ := hq
  exact ⟨fun j => HilbertCode.transport F E (a j),
    exactCode_transport κ Λ u F E p p' hu hκ hΛ hm a ha,congrArg _ hai⟩

def localGraphTimeEquiv (F : U ≃ᵐ U) (E : Y ≃ᵐ Y) (p p' : P)
    (hu : ∀ i, u p' i = F (u p i))
    (hκ : ∀ i, MeasurePreserving E (κ (u p i)) (κ (F (u p i))))
    (hΛ : MeasurePreserving (fun y : I → Y => fun i => E (y i)) (Λ p) (Λ p'))
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (S : Set (U × HilbertCode κ)) (i : I)
    (hS : ∀ q, (u p i,q) ∈ S ↔ ∃ a : I → HilbertCode κ, (p,a) ∈ exactCodeSet κ Λ u ∧ a i = q)
    (hS' : ∀ q, (F (u p i),q) ∈ S ↔ ∃ a : I → HilbertCode κ, (p',a) ∈ exactCodeSet κ Λ u ∧ a i = q) :
    {q : HilbertCode κ // (u p i,q) ∈ S} ≃ {q : HilbertCode κ // (F (u p i),q) ∈ S} := by
  have hu' (i) : u p i = F.symm (u p' i) := by rw [hu i,F.symm_apply_apply]
  have hκ' (i) : MeasurePreserving E.symm (κ (u p' i)) (κ (F.symm (u p' i))) := by
    rw [hu i,F.symm_apply_apply]; exact MeasurePreserving.symm E (hκ i)
  have hΛ' : MeasurePreserving (fun y : I → Y => fun i => E.symm (y i)) (Λ p') (Λ p) :=
    MeasurePreserving.symm (MeasurableEquiv.piCongrRight (fun _ : I => E)) hΛ
  refine {
    toFun := fun q => ⟨HilbertCode.transport F E q.val,
      (hS' _).mpr (exactSlot_transport κ Λ u F E p p' hu hκ hΛ (hm p) i q.val ((hS _).mp q.property))⟩
    invFun := fun q => ⟨HilbertCode.transport F.symm E.symm q.val,
      (hS _).mpr (exactSlot_transport κ Λ u F.symm E.symm p' p hu' hκ' hΛ' (hm p') i q.val ((hS' _).mp q.property))⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro q
    obtain ⟨a,ha,hai⟩ := (hS _).mp q.property
    apply Subtype.ext
    apply HilbertCode.transport_inverse F E q.val
    · rw [←hai]; exact (ha.2.1 i).2
    · rw [←hai]; exact (ha.2.1 i).1
    · rw [←hai,ha.1 i]; exact hκ i
  · intro q
    obtain ⟨a,ha,hai⟩ := (hS' _).mp q.property
    apply Subtype.ext
    apply HilbertCode.transport_inverse F.symm E.symm q.val
    · rw [←hai]; exact (ha.2.1 i).2
    · rw [←hai]; exact (ha.2.1 i).1
    · rw [←hai,ha.1 i]; exact hκ' i
end

namespace TriplePartition
variable {I : Type*} [Fintype I] [DecidableEq I]
abbrev split (s : TriplePartition I) : ComplementSplit s.P :=
  ⟨s.A,s.B,s.nonemptyP,s.nonemptyA,s.nonemptyB,s.disjointPA,s.disjointPB,s.disjointAB,s.cover⟩
end TriplePartition

section
variable {I : Type*} [Fintype I] [DecidableEq I]
noncomputable def singletonSplit (hk : 3 ≤ Fintype.card I) (i : I) : ComplementSplit ({i} : Finset I) := by
  have hi : (({i} : Finset I)ᶜ).Nonempty := by
    apply Finset.card_pos.mp
    have hc := Finset.card_compl ({i} : Finset I)
    simp only [Finset.card_singleton] at hc
    omega
  let j := hi.choose
  have hj : j ∉ ({i} : Finset I) := Finset.mem_compl.mp hi.choose_spec
  exact ComplementSplit.singleton {i} (Finset.singleton_nonempty i) j hj
    (by simpa only [Finset.singleton_union] using pair_complement_nonempty hk i j)

abbrev pairPartition (hk : 3 ≤ Fintype.card I) (j t : I) (hjt : j ≠ t) : TriplePartition I :=
  (ComplementSplit.singleton {j} (Finset.singleton_nonempty j) t
    (by simpa only [Finset.mem_singleton] using Ne.symm hjt)
    (by simpa only [Finset.singleton_union] using pair_complement_nonempty hk j t)).partition.swapPB.swapAB

end

section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp

variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)

def exactCodeVectors (p : P) (i : I) : Set (Lp ℂ 2 (κ (u p i))) :=
  {v | ∃ a : I → HilbertCode κ, (p,a) ∈ exactCodeSet κ Λ u ∧ a i = HilbertCode.encode (u p i) v}

def exactCodeSpan (p : P) (i : I) : Submodule ℂ (Lp ℂ 2 (κ (u p i))) :=
  (Submodule.span ℂ (exactCodeVectors κ Λ u p i)).topologicalClosure

end

open MeasureTheory Set

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_FibreMeasures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory Set
open scoped ENNReal BigOperators
variable {U Z : Type*} [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Z] [StandardBorelSpace Z]

namespace BorelFibreEnumeration
variable {S : Set (U × Z)} (E : BorelFibreEnumeration S)

instance indexMeasure_sigmaFinite (ν : Measure U) [SigmaFinite ν] : SigmaFinite (E.indexMeasure ν) := by
  apply SigmaFinite.of_map (E.indexMeasure ν) measurable_subtype_coe.aemeasurable
  change SigmaFinite (Measure.map Subtype.val ((ν.prod Measure.count).comap Subtype.val))
  rw [map_comap_subtype_coe E.measurable_indexDomain]
  infer_instance

instance measure_sigmaFinite (ν : Measure U) [SigmaFinite ν] : SigmaFinite (E.measure ν) :=
  E.measurableEmbedding_point.sigmaFinite_map

end BorelFibreEnumeration
end

namespace Kernel
open MeasureTheory ProbabilityTheory
variable {A B C D E F : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C] [MeasurableSpace D] [MeasurableSpace E] [MeasurableSpace F]

instance depMap_sfinite (κ : ProbabilityTheory.Kernel A B) [IsSFiniteKernel κ]
    (f : A × B → C) : IsSFiniteKernel (depMap κ f) := by
  unfold depMap
  infer_instance

end Kernel

section
open MeasureTheory

def labelShiftFirst : LabelOrbitVector ≃ᵐ LabelOrbitVector where
  toFun c p := c (p.1+1,p.2)
  invFun c p := c (p.1-1,p.2)
  left_inv c := by funext p; simp
  right_inv c := by funext p; simp
  measurable_toFun := Measurable.of_eval fun p => measurable_pi_apply _
  measurable_invFun := Measurable.of_eval fun p => measurable_pi_apply _

variable {Z H : Type*} [MeasurableSpace Z] (ξ : Measure Z)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (U : H →ₗᵢ[ℂ] Lp ℂ 2 ξ) (D S : H ≃ₗᵢ[ℂ] H) (v : H)

def labelOrbit (z : Z) : LabelOrbitVector := fun p => labelOrbitLP ξ U D S v p z
end

namespace BorelFibreEnumeration
open MeasureTheory Set
open scoped ENNReal
variable {U Z : Type*} [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Z] [StandardBorelSpace Z]
  {S : Set (U × Z)} (E : BorelFibreEnumeration S)

def restrictGraph (Q : Set (U × Z)) (hQ : MeasurableSet Q) : BorelFibreEnumeration (S ∩ Q) where
  domain n := {u | u ∈ E.domain n ∧ (u,E.section_ n u) ∈ Q}
  section_ := E.section_
  measurable_domain n := (E.measurable_domain n).inter ((measurable_id.prodMk (E.measurable_section n)) hQ)
  measurable_section := E.measurable_section
  mem n u hu := ⟨E.mem n u hu.1,hu.2⟩
  cover u z hz := by
    obtain ⟨n,hn,he⟩ := E.cover u z hz.1
    exact ⟨n,⟨hn,by rw [he]; exact hz.2⟩,he⟩
  unique u n m hn hm he := E.unique u n m hn.1 hm.1 he

end BorelFibreEnumeration

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_OrbitCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory ProbabilityTheory Set
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U) (S : Set (U × HilbertCode κ))

omit [DecidableEq I] in
lemma localProjectiveGroup_eq (p : P) (i : I)
    (hm : ∀ j, MeasurePreserving (fun y : I → Y => y j) (Λ p) (κ (u p j)))
    (hS : {q | ∃ a, (p,a) ∈ exactCodeSet κ Λ u ∧ a i = q} = {q | (u p i,q) ∈ S}) :
    localProjectiveGroup κ S (u p i) = (exactProjectiveSlot (Λ p) (fun j => κ (u p j)) i).range := by
  unfold localProjectiveGroup
  have he : {g : ProjectiveCircle (κ (u p i)) | ∃ q, (u p i,q) ∈ S ∧ HilbertCode.projective (u p i) q = g} =
      {g | ∃ q : ExactCodeSlot κ Λ u p i, HilbertCode.projective (u p i) q.val = g} := by
    ext g
    constructor
    · rintro ⟨q,hq,he⟩
      exact ⟨⟨q,(Set.ext_iff.mp hS q).mpr hq⟩,he⟩
    · rintro ⟨q,he⟩
      exact ⟨q.val,(Set.ext_iff.mp hS q.val).mp q.property,he⟩
  rw [he,codeSlot_projective_range κ Λ u p hm i,Subgroup.closure_eq]

omit [DecidableEq I] in
def localCodeEquivSlot (p : P) (i : I)
    (hS : {q | ∃ a, (p,a) ∈ exactCodeSet κ Λ u ∧ a i = q} = {q | (u p i,q) ∈ S}) :
    {q // (u p i,q) ∈ S} ≃ ExactCodeSlot κ Λ u p i := Equiv.setCongr hS.symm

omit [DecidableEq I] in

def localCodeEquivGroup (p : P) (i : I)
    (hm : ∀ j, MeasurePreserving (fun y : I → Y => y j) (Λ p) (κ (u p j)))
    (hS : {q | ∃ a, (p,a) ∈ exactCodeSet κ Λ u ∧ a i = q} = {q | (u p i,q) ∈ S}) :
    {q // (u p i,q) ∈ S} ≃ localProjectiveGroup κ S (u p i) :=
  (localCodeEquivSlot κ Λ u S p i hS).trans ((codeSlotEquivProjective κ Λ u p hm i).trans
    (MulEquiv.subgroupCongr (localProjectiveGroup_eq κ Λ u S p i hm hS).symm).toEquiv)

def localProjectiveMatching (hk : 3 ≤ Fintype.card I) (p : P)
    (hm : ∀ j, MeasurePreserving (fun y : I → Y => y j) (Λ p) (κ (u p j)))
    (hind : ∀ j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Y => y t) (Λ p)) (i j : I)
    (hSi : {q | ∃ a, (p,a) ∈ exactCodeSet κ Λ u ∧ a i = q} = {q | (u p i,q) ∈ S})
    (hSj : {q | ∃ a, (p,a) ∈ exactCodeSet κ Λ u ∧ a j = q} = {q | (u p j,q) ∈ S}) :
    localProjectiveGroup κ S (u p i) ≃* localProjectiveGroup κ S (u p j) :=
  (MulEquiv.subgroupCongr (localProjectiveGroup_eq κ Λ u S p i hm hSi)).trans
    ((exactProjectiveMatching hk (Λ p) (fun j => κ (u p j)) hm hind i j).trans
      (MulEquiv.subgroupCongr (localProjectiveGroup_eq κ Λ u S p j hm hSj).symm))
end

section
open MeasureTheory ProbabilityTheory Set
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y] (κ : Kernel U Y) [IsMarkovKernel κ]
    (S : Set (U × HilbertCode κ)) (a b : U)
    (e : {q // (a,q) ∈ S} ≃ {q // (b,q) ∈ S})
    (F : ProjectiveCircle (κ a) ≃* ProjectiveCircle (κ b))
    (he : ∀ q, F (HilbertCode.projective a q.val) = HilbertCode.projective b (e q).val)
include he in
lemma localProjectiveGroup_map :
    (localProjectiveGroup κ S a).map F.toMonoidHom = localProjectiveGroup κ S b := by
  unfold localProjectiveGroup
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨f,⟨q,hq,rfl⟩,rfl⟩
    exact ⟨(e ⟨q,hq⟩).val,(e ⟨q,hq⟩).property,(he ⟨q,hq⟩).symm⟩
  · rintro ⟨q,hq,rfl⟩
    refine ⟨HilbertCode.projective a (e.symm ⟨q,hq⟩).val,
      ⟨(e.symm ⟨q,hq⟩).val,(e.symm ⟨q,hq⟩).property,rfl⟩,?_⟩
    change F (HilbertCode.projective a (e.symm ⟨q,hq⟩).val) = _
    simpa only [e.apply_symm_apply] using he (e.symm ⟨q,hq⟩)

def localProjectiveTransport : localProjectiveGroup κ S a ≃* localProjectiveGroup κ S b :=
  (F.subgroupMap (localProjectiveGroup κ S a)).trans
    (MulEquiv.subgroupCongr (localProjectiveGroup_map κ S a b e F he))

end

section
open MeasureTheory ProbabilityTheory Set
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {Y : Type*} [MeasurableSpace Y]

def measurableCircleTime (E : Y ≃ᵐ Y) : MeasurableCircle Y ≃* MeasurableCircle Y where
  toFun f := ⟨(f : Y → Circle) ∘ E.symm,(measurableCircle_measurable Y f).comp E.symm.measurable⟩
  invFun f := ⟨(f : Y → Circle) ∘ E,(measurableCircle_measurable Y f).comp E.measurable⟩
  left_inv f := Subtype.ext (by funext y; exact congrArg f (E.symm_apply_apply y))
  right_inv f := Subtype.ext (by funext y; exact congrArg f (E.apply_symm_apply y))
  map_mul' f g := rfl

lemma measurableCircleTime_phase (E : Y ≃ᵐ Y) (μ ν : Measure Y)
    (hE : MeasurePreserving E μ ν) : (phaseSubgroup μ).map (measurableCircleTime E) = phaseSubgroup ν := by
  ext f
  constructor
  · rintro ⟨g,⟨c,hg⟩,rfl⟩
    exact ⟨c,(MeasurePreserving.symm E hE).quasiMeasurePreserving.ae_eq_comp hg⟩
  · rintro ⟨c,hf⟩
    refine ⟨(measurableCircleTime E).symm f,⟨c,hE.quasiMeasurePreserving.ae_eq_comp hf⟩,
      (measurableCircleTime E).apply_symm_apply f⟩

def projectiveTime (E : Y ≃ᵐ Y) (μ ν : Measure Y) (hE : MeasurePreserving E μ ν) :
    ProjectiveCircle μ ≃* ProjectiveCircle ν :=
  QuotientGroup.congr (phaseSubgroup μ) (phaseSubgroup ν) (measurableCircleTime E) (measurableCircleTime_phase E μ ν hE)

end

section
open MeasureTheory Set
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
attribute [local instance] Classical.propDecidable
variable {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)

def projectiveRep (g : ProjectiveCircle μ) : MeasurableCircle Y :=
  if g = 1 then 1 else Quotient.out g

def projectiveCharacter (g : ProjectiveCircle μ) (y : Y) : ℂ := projectiveRep μ g y

end

namespace BorelFibreEnumeration
open MeasureTheory Set
open scoped BigOperators

section
attribute [local instance] Classical.propDecidable
variable {U Z W : Type*} [MeasurableSpace U] [MeasurableSpace Z] [MeasurableSpace W]
variable {S : Set (U × Z)} (E : BorelFibreEnumeration S)

def sumFibreEquiv (a : U) : {n : ℕ // a ∈ E.domain n} ≃ {z : Z // (a,z) ∈ S} :=
  Equiv.ofBijective (fun n => ⟨E.section_ n.val a,E.mem n.val a n.property⟩) (by
    constructor
    · intro n m h
      exact Subtype.ext (E.unique a n.val m.val n.property m.property (congrArg Subtype.val h))
    · intro z
      obtain ⟨n,hn,he⟩ := E.cover a z.val z.property
      exact ⟨⟨n,hn⟩,Subtype.ext he⟩)

end

end BorelFibreEnumeration

section
open MeasureTheory Set Filter
open scoped Topology
variable {U Z C : Type*} [MeasurableSpace U] [MeasurableSpace Z]
    [MeasurableSpace C] [MeasurableSingletonClass C]
    {S : Set (U × Z)} (E : BorelFibreEnumeration S)
    (ψ : U × Z → C) (hψ : Measurable ψ) (D : C ≃ C) (b : C)
    (F : ℕ → U × Z → ℝ)
def movingFibreSum (n : ℕ) (a : U) : ℝ :=
  (E.restrictLevel ψ hψ ((D.symm^[n]) b)).fibreSum (F n) a

end

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_WeakLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped Topology BigOperators
namespace ArrayObjects
universe u
variable {I : Type u} [Fintype I] [retained15 : DecidableEq I]
    {X : StandardSpace.{u}} [TopologicalSpace X] [retained16 : CompactSpace X] [retained17 : T2Space X]
    [SecondCountableTopology X] [retained18 : MetrizableSpace X] [BorelSpace X]
    (T : X ≃ₜ X) (d : ℕ → I → ℕ) (μ : ProbabilityMeasure X)

variable (hμ : MeasurePreserving T μ μ)
    (hrect : ∀ J : Finset I, J ≠ Finset.univ → ∀ s : J → Set X,
      (∀ j, MeasurableSet (s j)) → Tendsto
        (fun b => (μ : Measure X) (⋂ j : J, (T^[d b j]) ⁻¹' s j)) atTop
        (𝓝 (∏ j : J, (μ : Measure X) (s j))))

def weakInitialLaws : InitialLaws I X T.toMeasurableEquiv where
  law n := weakArrayLaw T d (Ultrafilter.of atTop) μ n
  probability _ := inferInstance
  invariant n := ⟨(continuous_array_amap T.continuous n).measurable,
    congrArg Subtype.val (weakArrayLaw_invariant T d (Ultrafilter.of atTop) μ hμ n)⟩
  consistent n a i := congrArg Subtype.val (weakArrayLaw_consistent T d (Ultrafilter.of atTop) μ hμ n a i)
  proper n J hJ := congrArg Subtype.val (weakArrayLaw_proper T d (Ultrafilter.of atTop) μ
    (weakArrayLaw_proper_input T d μ hrect) n J hJ)

end ArrayObjects

end Rokhlin

end

end OAI
end


