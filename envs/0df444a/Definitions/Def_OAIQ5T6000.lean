-- Prove2me | Definitions.Def_OAIQ5T6000
-- name    : OAIQ5T6000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T02:54:38.257101+00:00
-- url     : https://prove2.me/theorems/13faf7c6-2258-4f52-a436-fd68d1341d4a
-- title:
--   Definitions bundle OAIQ5T6000 of the split of OpenAI, Weak and strong normalization in pure type systems
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PureTypeSystem.weak_implies_strong`, carved from OpenAI's openai/math development (OpenAI, *Weak and strong normalization in pure type systems*, OpenAI Math Release, September 25, 2026, result family 245, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1551 declarations of OpenAI's Lean: 601 definitions, 83 inductive types or structures, 14 instances and 853 theorems. The definitions and types are `OAI.FiniteClassical.Derives`, `OAI.FiniteClassical.Formula`, `OAI.FiniteClassical.Formula.chain`, `OAI.FiniteClassical.Formula.conj`, `OAI.FiniteClassical.Formula.eval`, `OAI.FiniteClassical.Formula.neg`, `OAI.FiniteClassical.Formula.sign`, `OAI.FiniteClassical.Formula.support`, `OAI.PureTypeSystem.ActiveLayer`, `OAI.PureTypeSystem.ActualPlain.Key`, `OAI.PureTypeSystem.ActualPlain.Key.domainNode`, `OAI.PureTypeSystem.ActualPlain.Key.target`, `OAI.PureTypeSystem.ActualPlain.Node`, `OAI.PureTypeSystem.ActualPlain.Space`, `OAI.PureTypeSystem.ActualPlain.measure`, `OAI.PureTypeSystem.ActualPlain.prefixEquiv`, `OAI.PureTypeSystem.ActualPlain.schema`, `OAI.PureTypeSystem.ArgsStep`, `OAI.PureTypeSystem.AxProfile`, `OAI.PureTypeSystem.Candidates.ActualType`, `OAI.PureTypeSystem.Candidates.Bottom`, `OAI.PureTypeSystem.Candidates.Candidate`, `OAI.PureTypeSystem.Candidates.ExpansionClosed`, `OAI.PureTypeSystem.Candidates.Ground`, `OAI.PureTypeSystem.Candidates.IsCandidate`, `OAI.PureTypeSystem.Candidates.Meet`, `OAI.PureTypeSystem.Candidates.ProductTest`, `OAI.PureTypeSystem.Candidates.RawProduct`, `OAI.PureTypeSystem.Candidates.SignedCandidate`, `OAI.PureTypeSystem.Candidates.SignedCandidate.set`, `OAI.PureTypeSystem.Candidates.SignedCandidate.wrap`, `OAI.PureTypeSystem.Candidates.StackAt`, `OAI.PureTypeSystem.Candidates.TestedStack`, `OAI.PureTypeSystem.Candidates.Top`, `OAI.PureTypeSystem.ComponentInterface`, `OAI.PureTypeSystem.ComponentInterface.Admissible`, `OAI.PureTypeSystem.ComponentInterface.Transported`, `OAI.PureTypeSystem.ComponentInterface.Transports`, `OAI.PureTypeSystem.ContextEquivalent`, `OAI.PureTypeSystem.ContextTower` and 644 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `TypeSystem_Basic`, `TypeSystem_Bounds`, `TypeSystem_Candidates`, `TypeSystem_Channels`, `TypeSystem_Components`, `TypeSystem_Congruence`, `TypeSystem_Contexts`, `TypeSystem_Diagonal`, `TypeSystem_Equivalence`, `TypeSystem_Evaluation`, `TypeSystem_Interface`, `TypeSystem_Labelled`, `TypeSystem_Logic`, `TypeSystem_Normalization`, `TypeSystem_ObservationCandidates`, `TypeSystem_ObservationReduction`, `TypeSystem_OneChild`, `TypeSystem_Pairs`, `TypeSystem_Plain`, `TypeSystem_Potential`, `TypeSystem_Profiles`, `TypeSystem_Reduction`, `TypeSystem_Relational`, `TypeSystem_Relations`, `TypeSystem_Response`, `TypeSystem_Restriction`, `TypeSystem_Signed`, `TypeSystem_Spaces`, `TypeSystem_Specialization`, `TypeSystem_Substitution`, `TypeSystem_Typing`, `TypeSystem_Values`, `TypeSystem_Wrappers`.
--
--   **Imports.** It imports the published bundle `Def_TypeSystemNormalization`.
--
--   **Imported by** (directly, in this split): the statements `OAI.PureTypeSystem.Labelled.DoubleCode.Formed.access_recovery`, `OAI_PureTypeSystem_Labelled_RelationalCode_Formed_extensional_elim`, `OAI_PureTypeSystem_Labelled_RelationalCode_Formed_extensional_formula`, `OAI_PureTypeSystem_Labelled_RelationalCode_Formed_probeFor_evaluation`, `OAI_PureTypeSystem_Labelled_RelationalCode_Formed_probeFor_typed`, `OAI_PureTypeSystem_Labelled_RelationalCode_Formed_recoverLift_formula`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.classPred_typed`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.class_query`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.class_witness_intro`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.delta_congr`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.delta_valid`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_diagonalBody_family`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_diagonalPred_exact`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_diagonalPred_extensional`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_diagonalQ_elim`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_diagonalQ_formula`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.edge_classes_witness_elim`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_edge_congr`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.edge_query`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.edge_to_tagged`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_edge_witness_core`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_edge_witness_elim`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.feature_propertyG`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.goodBody_family`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.good_backward`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.good_forward`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.induction_builder`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_lift_congr`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_lift_validStep`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_negative_induction`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_observation_equivalence`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.pair_comparison`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.pair_evaluation`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.pair_left_backward`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.pair_left_equivalent`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_pair_left_forward`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_pair_right_equivalent`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.pair_right_forward`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.parameter_query`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_part_exact`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_part_propertyG`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_positive_shift`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_positive_shift_step`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.probe_exact`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.probe_respStep`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_probe_response`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.propertyBody_family`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.propertyG_roundRespect`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.propertyR_respect`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.property_formula`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.property_respect`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_qBody_family`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_qConsequence_respect`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_qStep_respect`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_queries_family`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.relation_backward`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.relation_tagged_same`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.relational_bottom`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_responsePair_R_backward`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.responsePair_R_equivalent`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_responsePair_left`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.responsePair_pred_compare`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_responsePair_pred_compare_at`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.responsePair_pred_extensional`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_responsePair_right`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_responsePred_evaluation`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_responsePred_extensional`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_responsePred_typed`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.responseProbe_compare`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_response_elim`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_round_relation`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.sb_equivalent`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_sb_law`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_shiftPred_evaluation`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_shiftPred_exact`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_shiftPred_respect`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_shiftPred_typed`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_shift_compare_at`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_shift_induction`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.shift_predecessor`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.tag_witness_incompatible`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.union_at_witness`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_wfQ_imp`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_wfQ_member` and `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.wfQ_step`; the proofs of `OAI.PureTypeSystem.Labelled.DoubleCode.Formed.access_recovery`, `OAI_PureTypeSystem_Labelled_RelationalCode_Formed_extensional_elim`, `OAI_PureTypeSystem_Labelled_RelationalCode_Formed_extensional_formula`, `OAI_PureTypeSystem_Labelled_RelationalCode_Formed_probeFor_evaluation`, `OAI_PureTypeSystem_Labelled_RelationalCode_Formed_probeFor_typed`, `OAI_PureTypeSystem_Labelled_RelationalCode_Formed_recoverLift_formula`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.classPred_typed`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.class_query`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.class_witness_intro`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.delta_congr`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.delta_valid`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_diagonalBody_family`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_diagonalPred_exact`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_diagonalPred_extensional`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_diagonalQ_elim`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_diagonalQ_formula`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.edge_classes_witness_elim`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_edge_congr`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.edge_query`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.edge_to_tagged`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_edge_witness_core`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_edge_witness_elim`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.feature_propertyG`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.goodBody_family`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.good_backward`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.good_forward`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.induction_builder`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_lift_congr`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_lift_validStep`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_negative_induction`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_observation_equivalence`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.pair_comparison`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.pair_evaluation`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.pair_left_backward`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.pair_left_equivalent`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_pair_left_forward`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_pair_right_equivalent`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.pair_right_forward`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.parameter_query`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_part_exact`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_part_propertyG`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_positive_shift`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_positive_shift_step`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.probe_exact`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.probe_respStep`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_probe_response`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.propertyBody_family`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.propertyG_roundRespect`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.propertyR_respect`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.property_formula`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.property_respect`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_qBody_family`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_qConsequence_respect`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_qStep_respect`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_queries_family`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.relation_backward`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.relation_tagged_same`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.relational_bottom`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_responsePair_R_backward`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.responsePair_R_equivalent`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_responsePair_left`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.responsePair_pred_compare`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_responsePair_pred_compare_at`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.responsePair_pred_extensional`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_responsePair_right`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_responsePred_evaluation`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_responsePred_extensional`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_responsePred_typed`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.responseProbe_compare`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_response_elim`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_round_relation`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.sb_equivalent`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_sb_law`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_shiftPred_evaluation`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_shiftPred_exact`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_shiftPred_respect`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_shiftPred_typed`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_shift_compare_at`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_shift_induction`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.shift_predecessor`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.tag_witness_incompatible`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.union_at_witness`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_wfQ_imp`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_wfQ_member`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.wfQ_step` and `OAI.PureTypeSystem.weak_implies_strong`.
-- source:
--   OpenAI, Weak and strong normalization in pure type systems, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 245; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-and-strong-normalization-in-pure-type-systems-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_TypeSystemNormalization

section
-- module Solutions.OAIQ5_T6.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). -/
noncomputable instance starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Full annotated PTS syntax, modulo alpha-renaming via de Bruijn indices.
Contexts are stored newest-first, each declaration in its prefix context.
No functionality assumptions on axioms or product rules.
-/

namespace PureTypeSystem

universe u


namespace HasType

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M A : Expr S}

theorem valid (h : HasType P Γ M A) : ValidContext P Γ := by
  induction h with
  | ax _ => exact .nil
  | var h ih => exact .cons ih h
  | weaken _ h _ ih => exact .cons ih h
  | product _ _ _ ih _ => exact ih
  | abstraction _ _ _ ih => exact ih
  | application _ _ ih _ => exact ih
  | conversion _ _ _ ih _ => exact ih

end HasType

namespace Expr

variable {S : Type u}

@[simp] theorem liftRen_zero (ρ : Nat → Nat) : liftRen ρ 0 = 0 := rfl
@[simp] theorem liftRen_succ (ρ : Nat → Nat) (n : Nat) :
    liftRen ρ (n + 1) = ρ n + 1 := rfl

@[simp] theorem liftRen_id : liftRen id = id := by
  funext n
  cases n <;> rfl

theorem liftRen_comp (ρ τ : Nat → Nat) : liftRen (ρ ∘ τ) = liftRen ρ ∘ liftRen τ := by
  funext n
  cases n <;> rfl

@[simp] theorem rename_id (M : Expr S) : rename id M = M := by
  induction M with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp [rename, ihf, iha]
  | lam A b ihA ihb => simp [rename, ihA, ihb]
  | pi A B ihA ihB => simp [rename, ihA, ihB]

theorem rename_comp (M : Expr S) (ρ τ : Nat → Nat) :
    rename ρ (rename τ M) = rename (ρ ∘ τ) M := by
  induction M generalizing ρ τ with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp only [rename, ihf, iha]
  | lam A b ihA ihb => simp only [rename, ihA, ihb, liftRen_comp]
  | pi A B ihA ihB => simp only [rename, ihA, ihB, liftRen_comp]

@[simp] theorem liftSub_zero (σ : Nat → Expr S) : liftSub σ 0 = var 0 := rfl
@[simp] theorem liftSub_succ (σ : Nat → Expr S) (n : Nat) :
    liftSub σ (n + 1) = rename Nat.succ (σ n) := rfl

@[simp] theorem liftSub_var : liftSub (var : Nat → Expr S) = var := by
  funext n
  cases n <;> rfl

@[simp] theorem subst_var (M : Expr S) : subst var M = M := by
  induction M with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp [subst, ihf, iha]
  | lam A b ihA ihb => simp [subst, ihA, ihb]
  | pi A B ihA ihB => simp [subst, ihA, ihB]

theorem subst_rename (M : Expr S) (σ : Nat → Expr S) (ρ : Nat → Nat) :
    subst σ (rename ρ M) = subst (σ ∘ ρ) M := by
  have hlift : ∀ (σ : Nat → Expr S) (ρ : Nat → Nat),
      liftSub σ ∘ liftRen ρ = liftSub (σ ∘ ρ) := by
    intro σ ρ
    funext n
    cases n <;> rfl
  induction M generalizing σ ρ with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp only [rename, subst, ihf, iha]
  | lam A b ihA ihb => simp only [rename, subst, ihA, ihb, hlift]
  | pi A B ihA ihB => simp only [rename, subst, ihA, ihB, hlift]

theorem rename_subst (M : Expr S) (ρ : Nat → Nat) (σ : Nat → Expr S) :
    rename ρ (subst σ M) = subst (fun n => rename ρ (σ n)) M := by
  have hlift : ∀ (ρ : Nat → Nat) (σ : Nat → Expr S),
      (fun n => rename (liftRen ρ) (liftSub σ n)) =
        liftSub (fun n => rename ρ (σ n)) := by
    intro ρ σ
    funext n
    cases n with
    | zero => rfl
    | succ n =>
        simp only [liftSub_succ, rename_comp]
        rfl
  induction M generalizing ρ σ with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp only [subst, rename, ihf, iha]
  | lam A b ihA ihb => simp only [subst, rename, ihA, ihb, hlift]
  | pi A B ihA ihB => simp only [subst, rename, ihA, ihB, hlift]

theorem subst_subst (M : Expr S) (σ τ : Nat → Expr S) :
    subst σ (subst τ M) = subst (fun n => subst σ (τ n)) M := by
  have hlift : ∀ (σ τ : Nat → Expr S),
      (fun n => subst (liftSub σ) (liftSub τ n)) =
        liftSub (fun n => subst σ (τ n)) := by
    intro σ τ
    funext n
    cases n with
    | zero => rfl
    | succ n =>
        simp only [liftSub_succ, subst_rename, rename_subst]
        rfl
  induction M generalizing σ τ with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp only [subst, ihf, iha]
  | lam A b ihA ihb => simp only [subst, ihA, ihb, hlift]
  | pi A B ihA ihB => simp only [subst, ihA, ihB, hlift]

theorem instantiate_rename (b a : Expr S) (ρ : Nat → Nat) :
    (b.rename (liftRen ρ)).instantiate (a.rename ρ) = (b.instantiate a).rename ρ := by
  simp only [instantiate, subst_rename, rename_subst]
  congr 1
  funext n
  cases n <;> rfl

theorem instantiate_subst (b a : Expr S) (σ : Nat → Expr S) :
    (b.subst (liftSub σ)).instantiate (a.subst σ) = (b.instantiate a).subst σ := by
  simp only [instantiate, subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [liftSub_succ, subst_rename]
      exact subst_var (σ n)

end Expr

namespace Beta

variable {S : Type u} {M N : Expr S}

theorem rename (h : Beta M N) (ρ : Nat → Nat) : Beta (M.rename ρ) (N.rename ρ) := by
  induction h generalizing ρ with
  | head A b a =>
      simpa only [Expr.rename, ← Expr.instantiate_rename] using
        (Beta.head (A.rename ρ) (b.rename (Expr.liftRen ρ)) (a.rename ρ))
  | app_left _ ih => exact .app_left (ih ρ)
  | app_right _ ih => exact .app_right (ih ρ)
  | lam_domain _ ih => exact .lam_domain (ih ρ)
  | lam_body _ ih => exact .lam_body (ih (Expr.liftRen ρ))
  | pi_domain _ ih => exact .pi_domain (ih ρ)
  | pi_body _ ih => exact .pi_body (ih (Expr.liftRen ρ))

theorem subst (h : Beta M N) (σ : Nat → Expr S) : Beta (M.subst σ) (N.subst σ) := by
  induction h generalizing σ with
  | head A b a =>
      simpa only [Expr.subst, ← Expr.instantiate_subst] using
        (Beta.head (A.subst σ) (b.subst (Expr.liftSub σ)) (a.subst σ))
  | app_left _ ih => exact .app_left (ih σ)
  | app_right _ ih => exact .app_right (ih σ)
  | lam_domain _ ih => exact .lam_domain (ih σ)
  | lam_body _ ih => exact .lam_body (ih (Expr.liftSub σ))
  | pi_domain _ ih => exact .pi_domain (ih σ)
  | pi_body _ ih => exact .pi_body (ih (Expr.liftSub σ))

end Beta

end PureTypeSystem

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Reduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem

universe u

/-- Parallel reduction is used only to establish the beta metatheory. -/
inductive Parallel {S : Type u} : Expr S → Expr S → Prop
  | var (n) : Parallel (.var n) (.var n)
  | sort (s) : Parallel (.sort s) (.sort s)
  | app {f f' a a'} : Parallel f f' → Parallel a a' →
      Parallel (.app f a) (.app f' a')
  | lam {A A' b b'} : Parallel A A' → Parallel b b' →
      Parallel (.lam A b) (.lam A' b')
  | pi {A A' B B'} : Parallel A A' → Parallel B B' →
      Parallel (.pi A B) (.pi A' B')
  | head {b b' a a'} (A) : Parallel b b' → Parallel a a' →
      Parallel (.app (.lam A b) a) (b'.instantiate a')

namespace Parallel

variable {S : Type u} {M N : Expr S}

@[refl] theorem refl (M : Expr S) : Parallel M M := by
  induction M with
  | var n => exact .var n
  | sort s => exact .sort s
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | pi _ _ ihA ihB => exact .pi ihA ihB

theorem of_beta (h : Beta M N) : Parallel M N := by
  induction h with
  | head A b a => exact .head A (refl b) (refl a)
  | app_left _ ih => exact .app ih (refl _)
  | app_right _ ih => exact .app (refl _) ih
  | lam_domain _ ih => exact .lam ih (refl _)
  | lam_body _ ih => exact .lam (refl _) ih
  | pi_domain _ ih => exact .pi ih (refl _)
  | pi_body _ ih => exact .pi (refl _) ih

theorem rename (h : Parallel M N) (ρ : Nat → Nat) :
    Parallel (M.rename ρ) (N.rename ρ) := by
  induction h generalizing ρ with
  | var n => exact .var _
  | sort s => exact .sort _
  | app _ _ ihf iha => exact .app (ihf ρ) (iha ρ)
  | lam _ _ ihA ihb => exact .lam (ihA ρ) (ihb (Expr.liftRen ρ))
  | pi _ _ ihA ihB => exact .pi (ihA ρ) (ihB (Expr.liftRen ρ))
  | head A _ _ ihb iha =>
      simpa only [Expr.rename, ← Expr.instantiate_rename] using
        (Parallel.head (A.rename ρ) (ihb (Expr.liftRen ρ)) (iha ρ))

theorem subst (h : Parallel M N) (σ τ : Nat → Expr S)
    (hστ : ∀ n, Parallel (σ n) (τ n)) : Parallel (M.subst σ) (N.subst τ) := by
  have hlift (σ τ : Nat → Expr S) (hστ : ∀ n, Parallel (σ n) (τ n)) :
      ∀ n, Parallel (Expr.liftSub σ n) (Expr.liftSub τ n) := by
    intro n
    cases n with
    | zero => exact .var 0
    | succ n => exact (hστ n).rename Nat.succ
  induction h generalizing σ τ with
  | var n => exact hστ n
  | sort s => exact .sort s
  | app _ _ ihf iha => exact .app (ihf σ τ hστ) (iha σ τ hστ)
  | lam _ _ ihA ihb => exact .lam (ihA σ τ hστ) (ihb _ _ (hlift σ τ hστ))
  | pi _ _ ihA ihB => exact .pi (ihA σ τ hστ) (ihB _ _ (hlift σ τ hστ))
  | head A _ _ ihb iha =>
      simpa only [Expr.subst, ← Expr.instantiate_subst] using
        (Parallel.head (A.subst σ) (ihb _ _ (hlift σ τ hστ)) (iha σ τ hστ))

theorem instantiate {b b' a a' : Expr S} (hb : Parallel b b') (ha : Parallel a a') :
    Parallel (b.instantiate a) (b'.instantiate a') := by
  apply hb.subst
  intro n
  cases n with
  | zero => exact ha
  | succ n => exact .var n

end Parallel

namespace Expr

variable {S : Type u}

/-- Takahashi's complete development, including type annotations. -/
def develop : Expr S → Expr S
  | var n => var n
  | sort s => sort s
  | app (lam _ b) a => (develop b).instantiate (develop a)
  | app f a => app (develop f) (develop a)
  | lam A b => lam (develop A) (develop b)
  | pi A B => pi (develop A) (develop B)

end Expr

namespace Parallel

variable {S : Type u} {M N : Expr S}

theorem triangle (h : Parallel M N) : Parallel N M.develop := by
  induction h with
  | var n => exact .var n
  | sort s => exact .sort s
  | @app f f' a a' hf ha ihf iha =>
      cases f with
      | var n => exact .app ihf iha
      | sort s => exact .app ihf iha
      | app f b => exact .app ihf iha
      | pi A B => exact .app ihf iha
      | lam A b =>
          cases hf with
          | lam hA hb =>
              cases ihf with
              | lam ihA ihb => exact .head _ ihb iha
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | pi _ _ ihA ihB => exact .pi ihA ihB
  | head A _ _ ihb iha => exact ihb.instantiate iha

theorem diamond {a b c : Expr S} (hab : Parallel a b) (hac : Parallel a c) :
    ∃ d, Parallel b d ∧ Parallel c d := ⟨a.develop, hab.triangle, hac.triangle⟩

end Parallel

abbrev Reduces {S : Type u} := Relation.ReflTransGen (@Beta S)

namespace Reduces

variable {S : Type u} {f f' a a' A A' b b' : Expr S}

theorem app (hf : Reduces f f') (ha : Reduces a a') :
    Reduces (.app f a) (.app f' a') := by
  exact (hf.lift (fun x => Expr.app x a) (fun _ _ h => Beta.app_left h)).trans
    (ha.lift (fun x => Expr.app f' x) (fun _ _ h => Beta.app_right h))

theorem lam (hA : Reduces A A') (hb : Reduces b b') :
    Reduces (.lam A b) (.lam A' b') := by
  exact (hA.lift (fun x => Expr.lam x b) (fun _ _ h => Beta.lam_domain h)).trans
    (hb.lift (fun x => Expr.lam A' x) (fun _ _ h => Beta.lam_body h))

theorem pi (hA : Reduces A A') (hb : Reduces b b') :
    Reduces (.pi A b) (.pi A' b') := by
  exact (hA.lift (fun x => Expr.pi x b) (fun _ _ h => Beta.pi_domain h)).trans
    (hb.lift (fun x => Expr.pi A' x) (fun _ _ h => Beta.pi_body h))

theorem rename {M N : Expr S} (h : Reduces M N) (ρ : Nat → Nat) :
    Reduces (M.rename ρ) (N.rename ρ) := h.lift _ (fun _ _ h => h.rename ρ)

theorem subst {M N : Expr S} (h : Reduces M N) (σ : Nat → Expr S) :
    Reduces (M.subst σ) (N.subst σ) := h.lift _ (fun _ _ h => h.subst σ)

end Reduces

namespace Parallel

variable {S : Type u} {M N : Expr S}

theorem reduces (h : Parallel M N) : Reduces M N := by
  induction h with
  | var n => exact .refl
  | sort s => exact .refl
  | app _ _ ihf iha => exact Reduces.app ihf iha
  | lam _ _ ihA ihb => exact Reduces.lam ihA ihb
  | pi _ _ ihA ihB => exact Reduces.pi ihA ihB
  | head A _ _ ihb iha =>
      exact (Reduces.app (Reduces.lam .refl ihb) iha).tail (.head _ _ _)

theorem rtc_reduces {M N : Expr S} (h : Relation.ReflTransGen Parallel M N) :
    Reduces M N := Relation.reflTransGen_closed (fun _ _ h => h.reduces) _ _ h

end Parallel

namespace Reduces

variable {S : Type u} {M N : Expr S}

theorem parallel (h : Reduces M N) : Relation.ReflTransGen Parallel M N :=
  Relation.ReflTransGen.mono (fun _ _ h => Parallel.of_beta h) _ _ h

theorem confluent {a b c : Expr S} (hab : Reduces a b) (hac : Reduces a c) :
    Relation.Join Reduces b c := by
  have hd : ∀ a b c : Expr S, Parallel a b → Parallel a c →
      ∃ d, Relation.ReflGen Parallel b d ∧ Relation.ReflTransGen Parallel c d := by
    intro a b c hab hac
    obtain ⟨d, hb, hc⟩ := Parallel.diamond hab hac
    exact ⟨d, .single hb, .single hc⟩
  obtain ⟨d, hb, hc⟩ := Relation.church_rosser hd hab.parallel hac.parallel
  exact ⟨d, Parallel.rtc_reduces hb, Parallel.rtc_reduces hc⟩

end Reduces

namespace Converts

variable {S : Type u} {M N : Expr S}

theorem join (h : Converts M N) : Relation.Join Reduces M N := by
  induction h with
  | rel a b h => exact ⟨b, .single h, .refl⟩
  | refl a => exact ⟨a, .refl, .refl⟩
  | symm a b _ ih =>
      obtain ⟨c, ha, hb⟩ := ih
      exact ⟨c, hb, ha⟩
  | trans a b c _ _ ih₁ ih₂ =>
      obtain ⟨d, ha, hb⟩ := ih₁
      obtain ⟨e, hb', hc⟩ := ih₂
      obtain ⟨f, hd, he⟩ := Reduces.confluent hb hb'
      exact ⟨f, ha.trans hd, hc.trans he⟩

end Converts

namespace Normal

variable {S : Type u} {M N : Expr S}

theorem reduces_eq (hM : Normal M) (h : Reduces M N) : M = N := by
  induction h with
  | refl => rfl
  | @tail N N' _ h ih => exact False.elim (hM N' (ih ▸ h))

theorem eq_of_converts (hM : Normal M) (hN : Normal N) (h : Converts M N) : M = N := by
  obtain ⟨K, hMK, hNK⟩ := h.join
  exact (hM.reduces_eq hMK).trans (hN.reduces_eq hNK).symm

end Normal

namespace Reduces

variable {S : Type u} {A B N : Expr S}

theorem pi_inv (h : Reduces (.pi A B) N) :
    ∃ A' B', N = .pi A' B' ∧ Reduces A A' ∧ Reduces B B' := by
  induction h with
  | refl => exact ⟨A, B, rfl, .refl, .refl⟩
  | tail _ h ih =>
      obtain ⟨A', B', rfl, hA, hB⟩ := ih
      cases h with
      | pi_domain h => exact ⟨_, _, rfl, hA.tail h, hB⟩
      | pi_body h => exact ⟨_, _, rfl, hA, hB.tail h⟩

theorem converts {M N : Expr S} (h : Reduces M N) : Converts M N :=
  Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ h

end Reduces

namespace Converts

variable {S : Type u}

theorem product_compatibility {A B A' B' : Expr S}
    (h : Converts (.pi A B) (.pi A' B')) : Converts A A' ∧ Converts B B' := by
  obtain ⟨T, hT, hT'⟩ := h.join
  obtain ⟨D, E, hDE, hA, hB⟩ := hT.pi_inv
  obtain ⟨D', E', hDE', hA', hB'⟩ := hT'.pi_inv
  have heq := Expr.pi.inj (hDE.symm.trans hDE')
  obtain ⟨rfl, rfl⟩ := heq
  exact ⟨.trans _ _ _ hA.converts (.symm _ _ hA'.converts),
    .trans _ _ _ hB.converts (.symm _ _ hB'.converts)⟩

end Converts

namespace Normal

variable {S : Type u}

theorem var (n : Nat) : Normal (.var n : Expr S) := by
  intro N h
  cases h

theorem sort (s : S) : Normal (.sort s) := by
  intro N h
  cases h

end Normal

namespace StronglyNormalizing

variable {S : Type u} {M N : Expr S}

theorem step (hM : StronglyNormalizing M) (h : Beta M N) : StronglyNormalizing N :=
  hM.inv h

theorem reduces (hM : StronglyNormalizing M) (h : Reduces M N) : StronglyNormalizing N := by
  induction h with
  | refl => exact hM
  | tail _ h ih => exact ih.step h

end StronglyNormalizing

namespace Expr

variable {S : Type u}

def apps (f : Expr S) : List (Expr S) → Expr S
  | [] => f
  | a :: as => apps (.app f a) as

@[simp] theorem apps_nil (f : Expr S) : apps f [] = f := rfl
@[simp] theorem apps_cons (f a : Expr S) (as : List (Expr S)) :
    apps f (a :: as) = apps (.app f a) as := rfl

theorem apps_append (f : Expr S) (as bs : List (Expr S)) :
    apps f (as ++ bs) = apps (apps f as) bs := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => exact ih (.app f a)

end Expr

/-- Exactly one reduction step in one term of an argument list. -/
inductive ArgsStep {S : Type u} : List (Expr S) → List (Expr S) → Prop
  | head {a a' as} : Beta a a' → ArgsStep (a :: as) (a' :: as)
  | tail {a as as'} : ArgsStep as as' → ArgsStep (a :: as) (a :: as')

def StronglyNormalizingArgs {S : Type u} (as : List (Expr S)) : Prop :=
  Acc (fun bs as => ArgsStep as bs) as

namespace Beta

variable {S : Type u} {f f' : Expr S}

theorem apps (h : Beta f f') (as : List (Expr S)) :
    Beta (f.apps as) (f'.apps as) := by
  induction as generalizing f f' with
  | nil => exact h
  | cons a as ih => exact ih (.app_left h)

/-- If the head is not a lambda, a spine step comes from its head or an argument. -/
theorem apps_inv {as : List (Expr S)} {N : Expr S}
    (hf : ∀ A b, f ≠ .lam A b) (h : Beta (f.apps as) N) :
    (∃ f', Beta f f' ∧ N = f'.apps as) ∨
    (∃ as', ArgsStep as as' ∧ N = f.apps as') := by
  induction as generalizing f N with
  | nil => exact .inl ⟨N, h, rfl⟩
  | cons a as ih =>
      obtain ⟨g, hg, rfl⟩ | ⟨as', has, rfl⟩ :=
        ih (f := .app f a) (by intro A b heq; cases heq) h
      · cases hg with
        | head A b a => exact False.elim (hf A b rfl)
        | app_left hg => exact .inl ⟨_, hg, rfl⟩
        | app_right hg => exact .inr ⟨_, .head hg, rfl⟩
      · exact .inr ⟨_, .tail has, rfl⟩

end Beta

namespace ArgsStep

variable {S : Type u} {as bs : List (Expr S)}

theorem apps (h : ArgsStep as bs) (f : Expr S) : Beta (f.apps as) (f.apps bs) := by
  induction h generalizing f with
  | head h => exact (Beta.app_right h).apps _
  | tail h ih => exact ih (.app f _)

end ArgsStep

namespace Reduces

variable {S : Type u} {f f' : Expr S}

theorem apps (h : Reduces f f') (as : List (Expr S)) :
    Reduces (f.apps as) (f'.apps as) := h.lift _ (fun _ _ h => h.apps as)

end Reduces

namespace StronglyNormalizingArgs

variable {S : Type u}

theorem nil : StronglyNormalizingArgs ([] : List (Expr S)) := by
  apply Acc.intro
  intro bs h
  cases h

theorem cons {a : Expr S} {as : List (Expr S)} (ha : StronglyNormalizing a)
    (has : StronglyNormalizingArgs as) : StronglyNormalizingArgs (a :: as) := by
  induction ha generalizing as with
  | intro a ha iha =>
      induction has with
      | intro as has ihas =>
          apply Acc.intro
          intro bs h
          cases h with
          | head h => exact iha _ h (Acc.intro _ has)
          | tail h => exact ihas _ h

theorem of_forall {as : List (Expr S)} (h : ∀ a ∈ as, StronglyNormalizing a) :
    StronglyNormalizingArgs as := by
  induction as with
  | nil => exact nil
  | cons a as ih =>
      exact cons (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

theorem head {a : Expr S} {as : List (Expr S)}
    (h : StronglyNormalizingArgs (a :: as)) : StronglyNormalizing a :=
  Subrelation.accessible (fun h => ArgsStep.head h)
    (InvImage.accessible (fun a => a :: as) h)

theorem tail {a : Expr S} {as : List (Expr S)}
    (h : StronglyNormalizingArgs (a :: as)) : StronglyNormalizingArgs as :=
  Subrelation.accessible (fun h => ArgsStep.tail h)
    (InvImage.accessible (fun as => a :: as) h)

theorem of_mem {a : Expr S} {as : List (Expr S)}
    (h : StronglyNormalizingArgs as) (ha : a ∈ as) : StronglyNormalizing a := by
  induction as with
  | nil => cases ha
  | cons b bs ih =>
      rcases List.mem_cons.mp ha with rfl | ha
      · exact h.head
      · exact ih h.tail ha

end StronglyNormalizingArgs

namespace StronglyNormalizing

variable {S : Type u}

/-- The source's head-expansion lemma, with any finite argument spine.
The proof uses nested accessibility induction, not a raised recursion budget
or an assumed maximal reduction height. -/
theorem head_expansion {A b a : Expr S} {as : List (Expr S)}
    (hA : StronglyNormalizing A) (hb : StronglyNormalizing b)
    (ha : StronglyNormalizing a) (has : StronglyNormalizingArgs as)
    (hc : StronglyNormalizing ((b.instantiate a).apps as)) :
    StronglyNormalizing ((Expr.app (.lam A b) a).apps as) := by
  induction hA generalizing b a as with
  | intro A hA ihA =>
      induction hb generalizing a as with
      | intro b hb ihb =>
          induction ha generalizing as with
          | intro a ha iha =>
              induction has with
              | intro as has ihas =>
                  apply Acc.intro
                  intro N hN
                  obtain ⟨f, hf, rfl⟩ | ⟨bs, hbs, rfl⟩ :=
                    hN.apps_inv (by intro D c heq; cases heq)
                  · cases hf with
                    | head => exact hc
                    | app_left hf =>
                        cases hf with
                        | lam_domain h =>
                            exact ihA _ h (Acc.intro _ hb) (Acc.intro _ ha)
                              (Acc.intro _ has) hc
                        | lam_body h =>
                            exact ihb _ h (Acc.intro _ ha) (Acc.intro _ has)
                              (hc.step ((h.subst (Expr.single a)).apps as))
                    | app_right h =>
                        exact iha _ h (Acc.intro _ has)
                          (hc.reduces ((Parallel.instantiate (Parallel.refl b)
                            (Parallel.of_beta h)).reduces.apps as))
                  · exact ihas _ hbs (hc.step (hbs.apps _))

end StronglyNormalizing

namespace Expr
variable {S : Type u}
/-- Only literal syntax descent, including both annotations. -/
inductive Child : Expr S → Expr S → Prop
  | app_left (f a) : Child f (.app f a)
  | app_right (f a) : Child a (.app f a)
  | lam_domain (D m) : Child D (.lam D m)
  | lam_body (D m) : Child m (.lam D m)
  | pi_domain (D E) : Child D (.pi D E)
  | pi_body (D E) : Child E (.pi D E)

inductive Subterm : Expr S → Expr S → Prop
  | refl (M) : Subterm M M
  | tail {M N L} : Subterm M N → Child N L → Subterm M L

end Expr

end PureTypeSystem

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Typing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem

universe u

/-- A declaration's type viewed in the full newest-first context. -/
inductive Lookup {S : Type u} : List (Expr S) → Nat → Expr S → Prop
  | zero (A Γ) : Lookup (A :: Γ) 0 (A.rename Nat.succ)
  | succ {Γ n A} (B) : Lookup Γ n A → Lookup (B :: Γ) (n + 1) (A.rename Nat.succ)

namespace HasType

variable {S : Type u} {P : Specification S}

theorem sort_of_valid {Γ : List (Expr S)} (hΓ : ValidContext P Γ)
    {s t : S} (hst : P.axioms s t) : HasType P Γ (.sort s) (.sort t) := by
  induction hΓ with
  | nil => exact .ax hst
  | cons _ hA ih => exact .weaken ih hA

/-- Domain generation alone precedes substitution and does not need
any exchange or context-substitution theorem. -/
theorem product_domain {Γ : List (Expr S)} {M T : Expr S} (h : HasType P Γ M T) :
    ∀ A B, M = .pi A B → ∃ s, HasType P Γ A (.sort s) := by
  induction h with
  | ax h => intro A B heq; cases heq
  | var h ih => intro A B heq; cases heq
  | @weaken Γ M T C s hM hC ihM ihC =>
      intro A B heq
      cases M with
      | var n => cases heq
      | sort t => cases heq
      | app f a => cases heq
      | lam D b => cases heq
      | pi D E =>
          obtain ⟨rfl, rfl⟩ := Expr.pi.inj heq
          obtain ⟨t, ht⟩ := ihM D E rfl
          exact ⟨t, .weaken ht hC⟩
  | product hA hB hr ihA ihB =>
      intro A B heq
      cases heq
      exact ⟨_, hA⟩
  | abstraction hb hT ihb ihT => intro A B heq; cases heq
  | application hf ha ihf iha => intro A B heq; cases heq
  | conversion hM hB hconv ihM ihB => exact ihM

end HasType

namespace Converts

variable {S : Type u} {M N : Expr S}

theorem subst (h : Converts M N) (σ : Nat → Expr S) :
    Converts (M.subst σ) (N.subst σ) := by
  induction h with
  | rel a b h => exact .rel _ _ (h.subst σ)
  | refl a => exact .refl _
  | symm a b _ ih => exact .symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

theorem rename (h : Converts M N) (ρ : Nat → Nat) :
    Converts (M.rename ρ) (N.rename ρ) := by
  induction h with
  | rel a b h => exact .rel _ _ (h.rename ρ)
  | refl a => exact .refl _
  | symm a b _ ih => exact .symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

end Converts

/-- A simultaneous substitution respects each declared variable's exact type.
This is a premise only of the substitution metatheorem, not of the main target. -/
def TypedSubstitution {S : Type u} (P : Specification S)
    (Γ Δ : List (Expr S)) (σ : Nat → Expr S) : Prop :=
  ∀ n A, Lookup Γ n A → HasType P Δ (σ n) (A.subst σ)

namespace TypedSubstitution

variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)}
    {σ : Nat → Expr S}

theorem tail {A : Expr S} (hσ : TypedSubstitution P (A :: Γ) Δ σ) :
    TypedSubstitution P Γ Δ (σ ∘ Nat.succ) := by
  intro n B hB
  have h := hσ (n + 1) (B.rename Nat.succ) (.succ A hB)
  simpa only [Expr.subst_rename, Function.comp_def] using h

theorem lift {A : Expr S} {s : S} (hσ : TypedSubstitution P Γ Δ σ)
    (hA : HasType P Δ (A.subst σ) (.sort s)) :
    TypedSubstitution P (A :: Γ) (A.subst σ :: Δ) (Expr.liftSub σ) := by
  intro n B hn
  cases hn with
  | zero =>
      have ht := HasType.var hA
      simpa only [Expr.liftSub_zero, Expr.subst_rename, Expr.rename_subst,
        Expr.liftSub_succ, Function.comp_def] using ht
  | succ C hn =>
      have ht := HasType.weaken (hσ _ _ hn) hA
      simpa only [Expr.liftSub_succ, Expr.rename_subst, Expr.subst_rename,
        Function.comp_def] using ht

end TypedSubstitution

namespace HasType

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M T : Expr S}

theorem subst (h : HasType P Γ M T) {Δ : List (Expr S)}
    (hΔ : ValidContext P Δ) (σ : Nat → Expr S) (hσ : TypedSubstitution P Γ Δ σ) :
    HasType P Δ (M.subst σ) (T.subst σ) := by
  induction h generalizing Δ σ with
  | ax h => exact sort_of_valid hΔ h
  | var h ih => exact hσ _ _ (.zero _ _)
  | weaken hM hA ihM ihA =>
      simpa only [Expr.subst_rename] using ihM hΔ (σ ∘ Nat.succ) hσ.tail
  | product hA hB hr ihA ihB =>
      have hA' := ihA hΔ σ hσ
      exact .product hA' (ihB (.cons hΔ hA') _ (hσ.lift hA')) hr
  | @abstraction Γ A b B s hb hprod ihb ihprod =>
      have hprod' := ihprod hΔ σ hσ
      obtain ⟨t, hA'⟩ := hprod'.product_domain _ _ rfl
      exact .abstraction (ihb (.cons hΔ hA') _ (hσ.lift hA')) hprod'
  | application hf ha ihf iha =>
      simpa only [Expr.subst, Expr.instantiate_subst] using
        (HasType.application (ihf hΔ σ hσ) (iha hΔ σ hσ))
  | conversion hM hB hconv ihM ihB =>
      exact .conversion (ihM hΔ σ hσ) (ihB hΔ σ hσ) (hconv.subst σ)

end HasType

namespace Expr

variable {S : Type u}

theorem subst_var_rename (M : Expr S) (ρ : Nat → Nat) :
    M.subst (var ∘ ρ) = M.rename ρ := by
  rw [← subst_rename, subst_var]

@[simp] theorem subst_lift_single (M a : Expr S) :
    (M.rename Nat.succ).subst (single a) = M := by
  rw [subst_rename]
  exact subst_var M

end Expr

namespace HasType

variable {S : Type u} {P : Specification S}

theorem lookup {Γ : List (Expr S)} (hΓ : ValidContext P Γ)
    {n : Nat} {A : Expr S} (hn : Lookup Γ n A) : HasType P Γ (.var n) A := by
  induction hΓ generalizing n A with
  | nil => cases hn
  | cons hΓ hB ih =>
      cases hn with
      | zero => exact .var hB
      | succ _ hn => exact .weaken (ih hn) hB

end HasType

namespace TypedSubstitution

variable {S : Type u} {P : Specification S}

theorem weaken {Γ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) :
    TypedSubstitution P Γ (A :: Γ) (Expr.var ∘ Nat.succ) := by
  intro n B hn
  simpa only [Expr.subst_var_rename, Function.comp_apply, Expr.rename] using
    (HasType.weaken (HasType.lookup hA.valid hn) hA)

theorem single {Γ : List (Expr S)} {a A : Expr S} (ha : HasType P Γ a A) :
    TypedSubstitution P (A :: Γ) Γ (Expr.single a) := by
  intro n B hn
  cases hn with
  | zero => simpa only [Expr.single, Expr.subst_lift_single] using ha
  | succ _ hn =>
      simpa only [Expr.single, Expr.subst_lift_single] using HasType.lookup ha.valid hn

end TypedSubstitution

namespace HasType

section

variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)}

theorem rename {M A : Expr S} (h : HasType P Γ M A)
    (hΔ : ValidContext P Δ) (ρ : Nat → Nat)
    (hρ : ∀ n B, Lookup Γ n B → HasType P Δ (.var (ρ n)) (B.rename ρ)) :
    HasType P Δ (M.rename ρ) (A.rename ρ) := by
  have hσ : TypedSubstitution P Γ Δ (Expr.var ∘ ρ) := by
    intro n B hn
    simpa only [Expr.subst_var_rename, Function.comp_apply] using hρ n B hn
  simpa only [Expr.subst_var_rename] using h.subst hΔ (Expr.var ∘ ρ) hσ

theorem instantiate {A b B a : Expr S}
    (hb : HasType P (A :: Γ) b B) (ha : HasType P Γ a A) :
    HasType P Γ (b.instantiate a) (B.instantiate a) :=
  hb.subst ha.valid _ (TypedSubstitution.single ha)

theorem weaken_under {A D b B : Expr S} {s t : S}
    (hb : HasType P (A :: Γ) b B) (hA : HasType P Γ A (.sort s))
    (hD : HasType P Γ D (.sort t)) :
    HasType P (A.rename Nat.succ :: D :: Γ)
      (b.rename (Expr.liftRen Nat.succ)) (B.rename (Expr.liftRen Nat.succ)) := by
  have hA' : HasType P (D :: Γ) (A.subst (Expr.var ∘ Nat.succ)) (.sort s) := by
    simpa only [Expr.subst_var_rename, Expr.rename] using HasType.weaken hA hD
  have hσ := (TypedSubstitution.weaken hD).lift hA'
  have h := hb.subst (.cons (.cons hD.valid hD) hA') _ hσ
  have heq : Expr.liftSub (Expr.var ∘ Nat.succ : Nat → Expr S) =
      Expr.var ∘ Expr.liftRen Nat.succ := by
    funext n
    cases n <;> rfl
  simpa only [heq, Expr.subst_var_rename] using h

theorem context_head_conversion {A A' b B : Expr S} {s t : S}
    (hb : HasType P (A :: Γ) b B) (hA : HasType P Γ A (.sort s))
    (hA' : HasType P Γ A' (.sort t)) (hc : Converts A A') :
    HasType P (A' :: Γ) b B := by
  have hσ : TypedSubstitution P (A :: Γ) (A' :: Γ) Expr.var := by
    intro n D hn
    rw [Expr.subst_var]
    cases hn with
    | zero =>
        exact .conversion (.var hA') (.weaken hA hA')
          (.symm _ _ (hc.rename Nat.succ))
    | succ _ hn => exact .weaken (lookup hA.valid hn) hA'
  simpa only [Expr.subst_var] using hb.subst (.cons hA'.valid hA') _ hσ

end

variable {S : Type u} {P : Specification S}

/-- Generation is stated up to conversion, without any functionality premise. -/
def Generation (P : Specification S) (Γ : List (Expr S))
    (M T : Expr S) : Prop :=
  match M with
  | .var n => ∃ A, Lookup Γ n A ∧ Converts T A
  | .sort s => ∃ t, P.axioms s t ∧ Converts T (.sort t)
  | .app f a => ∃ A B, HasType P Γ f (.pi A B) ∧ HasType P Γ a A ∧
      Converts T (B.instantiate a)
  | .lam A b => ∃ B s, HasType P (A :: Γ) b B ∧
      HasType P Γ (.pi A B) (.sort s) ∧ Converts T (.pi A B)
  | .pi A B => ∃ s₁ s₂ s₃, HasType P Γ A (.sort s₁) ∧
      HasType P (A :: Γ) B (.sort s₂) ∧ P.rule s₁ s₂ s₃ ∧
      Converts T (.sort s₃)

theorem generation {Γ : List (Expr S)} {M T : Expr S}
    (h : HasType P Γ M T) : Generation P Γ M T := by
  induction h with
  | ax h => exact ⟨_, h, .refl _⟩
  | var h ih => exact ⟨_, .zero _ _, .refl _⟩
  | @weaken Γ M T D s hM hD ihM ihD =>
      cases M with
      | var n =>
          obtain ⟨A, hA, hc⟩ := ihM
          exact ⟨_, .succ D hA, hc.rename Nat.succ⟩
      | sort t =>
          obtain ⟨t', ht, hc⟩ := ihM
          exact ⟨t', ht, hc.rename Nat.succ⟩
      | app f a =>
          obtain ⟨A, B, hf, ha, hc⟩ := ihM
          refine ⟨_, _, .weaken hf hD, .weaken ha hD, ?_⟩
          simpa only [Expr.instantiate_rename] using hc.rename Nat.succ
      | lam A b =>
          obtain ⟨B, t, hb, hPi, hc⟩ := ihM
          obtain ⟨r, hA⟩ := hPi.product_domain _ _ rfl
          exact ⟨_, t, hb.weaken_under hA hD, .weaken hPi hD,
            hc.rename Nat.succ⟩
      | pi A B =>
          obtain ⟨t₁, t₂, t₃, hA, hB, hr, hc⟩ := ihM
          exact ⟨t₁, t₂, t₃, .weaken hA hD, hB.weaken_under hA hD,
            hr, hc.rename Nat.succ⟩
  | product hA hB hr ihA ihB => exact ⟨_, _, _, hA, hB, hr, .refl _⟩
  | abstraction hb hPi ihb ihPi => exact ⟨_, _, hb, hPi, .refl _⟩
  | application hf ha ihf iha => exact ⟨_, _, hf, ha, .refl _⟩
  | @conversion Γ M A B s hM hB hc ihM ihB =>
      cases M with
      | var n =>
          obtain ⟨D, hD, hd⟩ := ihM
          exact ⟨D, hD, .trans _ _ _ (.symm _ _ hc) hd⟩
      | sort t =>
          obtain ⟨r, hr, hd⟩ := ihM
          exact ⟨r, hr, .trans _ _ _ (.symm _ _ hc) hd⟩
      | app f a =>
          obtain ⟨D, E, hf, ha, hd⟩ := ihM
          exact ⟨D, E, hf, ha, .trans _ _ _ (.symm _ _ hc) hd⟩
      | lam D b =>
          obtain ⟨E, r, hb, hPi, hd⟩ := ihM
          exact ⟨E, r, hb, hPi, .trans _ _ _ (.symm _ _ hc) hd⟩
      | pi D E =>
          obtain ⟨r₁, r₂, r₃, hD, hE, hr, hd⟩ := ihM
          exact ⟨r₁, r₂, r₃, hD, hE, hr, .trans _ _ _ (.symm _ _ hc) hd⟩

theorem generation_pi {Γ : List (Expr S)} {A B T : Expr S}
    (h : HasType P Γ (.pi A B) T) :
    ∃ s₁ s₂ s₃, HasType P Γ A (.sort s₁) ∧
      HasType P (A :: Γ) B (.sort s₂) ∧ P.rule s₁ s₂ s₃ ∧
      Converts T (.sort s₃) := h.generation

theorem generation_lam {Γ : List (Expr S)} {A b T : Expr S}
    (h : HasType P Γ (.lam A b) T) :
    ∃ B s, HasType P (A :: Γ) b B ∧ HasType P Γ (.pi A B) (.sort s) ∧
      Converts T (.pi A B) := h.generation

theorem generation_app {Γ : List (Expr S)} {f a T : Expr S}
    (h : HasType P Γ (.app f a) T) :
    ∃ A B, HasType P Γ f (.pi A B) ∧ HasType P Γ a A ∧
      Converts T (B.instantiate a) := h.generation

/-- Correctness of types, including the unsorted literal-sort alternative. -/
theorem regularity {Γ : List (Expr S)} {M A : Expr S} (h : HasType P Γ M A) :
    (∃ s, A = .sort s) ∨ (∃ s, HasType P Γ A (.sort s)) := by
  induction h with
  | ax h => exact .inl ⟨_, rfl⟩
  | var h ih => exact .inr ⟨_, .weaken h h⟩
  | weaken hM hD ihM ihD =>
      obtain ⟨s, rfl⟩ | ⟨s, hA⟩ := ihM
      · exact .inl ⟨s, rfl⟩
      · exact .inr ⟨s, .weaken hA hD⟩
  | product hA hB hr ihA ihB => exact .inl ⟨_, rfl⟩
  | abstraction hb hPi ihb ihPi => exact .inr ⟨_, hPi⟩
  | application hf ha ihf iha =>
      obtain ⟨s, heq⟩ | ⟨s, hPi⟩ := ihf
      · cases heq
      · obtain ⟨s₁, s₂, s₃, hA, hB, hr, hc⟩ := hPi.generation_pi
        exact .inr ⟨s₂, hB.instantiate ha⟩
  | conversion hM hA hc ihM ihA => exact .inr ⟨_, hA⟩

theorem product_type_sorted {Γ : List (Expr S)} {M A B : Expr S}
    (h : HasType P Γ M (.pi A B)) : ∃ s, HasType P Γ (.pi A B) (.sort s) := by
  obtain ⟨s, heq⟩ | hs := h.regularity
  · cases heq
  · exact hs

end HasType

namespace Converts

variable {S : Type u}

theorem pi {A A' B B' : Expr S} (hA : Converts A A') (hB : Converts B B') :
    Converts (.pi A B) (.pi A' B') := by
  obtain ⟨D, hD, hD'⟩ := hA.join
  obtain ⟨E, hE, hE'⟩ := hB.join
  exact .trans _ _ _ (hD.pi hE).converts (.symm _ _ (hD'.pi hE').converts)

theorem pi_not_sort {A B : Expr S} {s : S} : ¬ Converts (.pi A B) (.sort s) := by
  intro h
  obtain ⟨N, hN, hs⟩ := h.join
  have heq := (Normal.sort s).reduces_eq hs
  obtain ⟨D, E, hDE, _, _⟩ := hN.pi_inv
  cases heq.trans hDE

theorem sort_inj {s t : S} (h : Converts (Expr.sort s) (.sort t)) : s = t :=
  Expr.sort.inj ((Normal.sort s).eq_of_converts (Normal.sort t) h)

theorem instantiate_right {a a' : Expr S} (h : Converts a a') (B : Expr S) :
    Converts (B.instantiate a) (B.instantiate a') := by
  induction h with
  | rel a a' h =>
      exact (Parallel.instantiate (Parallel.refl B) (Parallel.of_beta h)).reduces.converts
  | refl a => exact .refl _
  | symm a b h ih => exact .symm _ _ ih
  | trans a b c hab hbc ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

end Converts

namespace HasType

variable {S : Type u} {P : Specification S}

theorem application_type_sorted_aux {Γ : List (Expr S)} {M T : Expr S}
    (h : HasType P Γ M T) :
    ∀ f a, M = .app f a → ∃ s, HasType P Γ T (.sort s) := by
  induction h with
  | ax h => intro f a heq; cases heq
  | var h ih => intro f a heq; cases heq
  | @weaken Γ M T D s hM hD ihM ihD =>
      intro f a heq
      cases M with
      | var n => cases heq
      | sort t => cases heq
      | lam A b => cases heq
      | pi A B => cases heq
      | app g b =>
          obtain ⟨r, hr⟩ := ihM g b rfl
          exact ⟨r, .weaken hr hD⟩
  | product hA hB hr ihA ihB => intro f a heq; cases heq
  | abstraction hb hPi ihb ihPi => intro f a heq; cases heq
  | application hf ha ihf iha =>
      intro f a heq
      obtain ⟨s, hPi⟩ := hf.product_type_sorted
      obtain ⟨s₁, s₂, s₃, hA, hB, hr, hc⟩ := hPi.generation_pi
      exact ⟨s₂, hB.instantiate ha⟩
  | conversion hM hT hc ihM ihT => intro f a heq; exact ⟨_, hT⟩

theorem application_type_sorted {Γ : List (Expr S)} {f a T : Expr S}
    (h : HasType P Γ (.app f a) T) : ∃ s, HasType P Γ T (.sort s) :=
  h.application_type_sorted_aux f a rfl

theorem abstraction_type_sorted {Γ : List (Expr S)} {A b T : Expr S}
    (h : HasType P Γ (.lam A b) T) : ∃ s, HasType P Γ T (.sort s) := by
  obtain ⟨s, hT⟩ | hs := h.regularity
  · obtain ⟨B, t, hb, hPi, hc⟩ := h.generation_lam
    subst T
    exact False.elim (Converts.pi_not_sort (.symm _ _ hc))
  · exact hs

/-- Reconstructing a sorted expression at its original expected type does not
require a sorting of a terminal (unsorted) sort. -/
theorem conversion_from_sort {Γ : List (Expr S)} {M T : Expr S} {s : S}
    (h : HasType P Γ M (.sort s))
    (hT : (∃ t, T = .sort t) ∨ ∃ t, HasType P Γ T (.sort t))
    (hc : Converts T (.sort s)) : HasType P Γ M T := by
  obtain ⟨t, rfl⟩ | ⟨t, ht⟩ := hT
  · have heq := hc.sort_inj
    subst t
    exact h
  · exact .conversion h ht (.symm _ _ hc)

/-- Subject reduction at the exact original type, including binder annotations. -/
theorem subject_reduction {Γ : List (Expr S)} {M N T : Expr S}
    (h : HasType P Γ M T) (hr : Beta M N) : HasType P Γ N T := by
  induction hr generalizing Γ T with
  | head A b a =>
      obtain ⟨r, hT⟩ := h.application_type_sorted
      obtain ⟨D, E, hf, ha, hc⟩ := h.generation_app
      obtain ⟨B, s, hb, hPi, hp⟩ := hf.generation_lam
      obtain ⟨hDA, hEB⟩ := hp.product_compatibility
      obtain ⟨t, hA⟩ := hPi.product_domain A B rfl
      have haA := HasType.conversion ha hA hDA
      have hresult := hb.instantiate haA
      exact .conversion hresult hT (.trans _ _ _
        (.symm _ _ (hEB.subst (Expr.single a))) (.symm _ _ hc))
  | app_left hr ih =>
      obtain ⟨r, hT⟩ := h.application_type_sorted
      obtain ⟨A, B, hf, ha, hc⟩ := h.generation_app
      exact .conversion (.application (ih hf) ha) hT (.symm _ _ hc)
  | @app_right f a a' hr ih =>
      obtain ⟨r, hT⟩ := h.application_type_sorted
      obtain ⟨A, B, hf, ha, hc⟩ := h.generation_app
      exact .conversion (.application hf (ih ha)) hT (.trans _ _ _
        (.symm _ _ ((show Converts a a' from .rel _ _ hr).instantiate_right B)) (.symm _ _ hc))
  | @lam_domain A A' b hr ih =>
      obtain ⟨r, hT⟩ := h.abstraction_type_sorted
      obtain ⟨B, s, hb, hPi, hc⟩ := h.generation_lam
      obtain ⟨s₁, s₂, s₃, hA, hB, hrule, hs⟩ := hPi.generation_pi
      have hA' := ih hA
      have heq : Converts A A' := .rel _ _ hr
      have hb' := hb.context_head_conversion hA hA' heq
      have hB' := hB.context_head_conversion hA hA' heq
      have hp' := HasType.product hA' hB' hrule
      exact .conversion (.abstraction hb' hp') hT (.trans _ _ _
        (.symm _ _ (heq.pi (.refl B))) (.symm _ _ hc))
  | lam_body hr ih =>
      obtain ⟨r, hT⟩ := h.abstraction_type_sorted
      obtain ⟨B, s, hb, hPi, hc⟩ := h.generation_lam
      exact .conversion (.abstraction (ih hb) hPi) hT (.symm _ _ hc)
  | pi_domain hr ih =>
      obtain ⟨s₁, s₂, s₃, hA, hB, hrule, hc⟩ := h.generation_pi
      have hA' := ih hA
      have hB' := hB.context_head_conversion hA hA' (.rel _ _ hr)
      exact (HasType.product hA' hB' hrule).conversion_from_sort h.regularity hc
  | pi_body hr ih =>
      obtain ⟨s₁, s₂, s₃, hA, hB, hrule, hc⟩ := h.generation_pi
      exact (HasType.product hA (ih hB) hrule).conversion_from_sort h.regularity hc

theorem subject_reduces {Γ : List (Expr S)} {M N T : Expr S}
    (h : HasType P Γ M T) (hr : Reduces M N) : HasType P Γ N T := by
  induction hr with
  | refl => exact h
  | tail _ hr ih => exact ih.subject_reduction hr

end HasType

namespace Normal

variable {S : Type u} {M : Expr S}

theorem of_map {f : Expr S → Expr S}
    (hf : ∀ {a b}, Beta a b → Beta (f a) (f b)) (h : Normal (f M)) : Normal M :=
  fun N hN => h (f N) (hf hN)

theorem app_left {f a : Expr S} (h : Normal (.app f a)) : Normal f :=
  of_map Beta.app_left h

theorem app_right {f a : Expr S} (h : Normal (.app f a)) : Normal a :=
  of_map Beta.app_right h

theorem lam_domain {A b : Expr S} (h : Normal (.lam A b)) : Normal A :=
  of_map Beta.lam_domain h

theorem lam_body {A b : Expr S} (h : Normal (.lam A b)) : Normal b :=
  of_map Beta.lam_body h

theorem pi_domain {A B : Expr S} (h : Normal (.pi A B)) : Normal A :=
  of_map Beta.pi_domain h

theorem pi_body {A B : Expr S} (h : Normal (.pi A B)) : Normal B :=
  of_map Beta.pi_body h

theorem pi {A B : Expr S} (hA : Normal A) (hB : Normal B) : Normal (.pi A B) := by
  intro N h
  cases h with
  | pi_domain h => exact hA _ h
  | pi_body h => exact hB _ h

theorem lam {A b : Expr S} (hA : Normal A) (hb : Normal b) : Normal (.lam A b) := by
  intro N h
  cases h with
  | lam_domain h => exact hA _ h
  | lam_body h => exact hb _ h

end Normal

namespace Expr

variable {S : Type u}

/-- Choice of the unique full beta normal form when it exists. The fallback
is irrelevant on legal syntax under the standing system-wide WN hypothesis. -/
noncomputable def normalForm (M : Expr S) : Expr S := by
  classical
  exact if h : WeaklyNormalizing M then Classical.choose h else M

theorem normalForm_spec {M : Expr S} (h : WeaklyNormalizing M) :
    Reduces M M.normalForm ∧ Normal M.normalForm := by
  rw [normalForm, dite_eq_left h]
  exact Classical.choose_spec h

theorem normalForm_eq {M N : Expr S} (hr : Reduces M N) (hn : Normal N) :
    M.normalForm = N := by
  have h : WeaklyNormalizing M := ⟨N, hr, hn⟩
  obtain ⟨hm, hnm⟩ := normalForm_spec h
  exact hnm.eq_of_converts hn (.trans _ _ _ (.symm _ _ hm.converts) hr.converts)

@[simp] theorem normalForm_of_normal {M : Expr S} (h : Normal M) : M.normalForm = M :=
  normalForm_eq .refl h

theorem normalForm_converts {M N : Expr S} (hM : WeaklyNormalizing M)
    (hN : WeaklyNormalizing N) (hc : Converts M N) : M.normalForm = N.normalForm := by
  obtain ⟨hm, hnm⟩ := normalForm_spec hM
  obtain ⟨hn, hnn⟩ := normalForm_spec hN
  exact hnm.eq_of_converts hnn (.trans _ _ _ (.symm _ _ hm.converts)
    (.trans _ _ _ hc hn.converts))

theorem normalForm_pi {A B : Expr S}
    (hA : WeaklyNormalizing A) (hB : WeaklyNormalizing B) :
    (Expr.pi A B).normalForm = .pi A.normalForm B.normalForm :=
  normalForm_eq ((normalForm_spec hA).1.pi (normalForm_spec hB).1)
    ((normalForm_spec hA).2.pi (normalForm_spec hB).2)

end Expr

namespace HasType

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M A : Expr S}

theorem weaklyNormalizing (h : HasType P Γ M A) (hw : SystemWeaklyNormalizing P) :
    WeaklyNormalizing M := hw Γ h.valid M ⟨A, .inl h⟩

theorem type_weaklyNormalizing (h : HasType P Γ M A) (hw : SystemWeaklyNormalizing P) :
    WeaklyNormalizing A := hw Γ h.valid A ⟨M, .inr h⟩

theorem normalForm (h : HasType P Γ M A) (hw : SystemWeaklyNormalizing P) :
    HasType P Γ M.normalForm A :=
  h.subject_reduces (Expr.normalForm_spec (h.weaklyNormalizing hw)).1

end HasType

/-- The variable-headed spines used by the manuscript. -/
inductive Neutral {S : Type u} : Expr S → Prop
  | var (n) : Neutral (.var n)
  | app {f a} : Neutral f → Neutral (.app f a)

namespace HasType

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)}

theorem sort_cannot_have_product_type {s : S} {A B : Expr S}
    (h : HasType P Γ (.sort s) (.pi A B)) : False := by
  obtain ⟨t, ht, hc⟩ := h.generation
  exact Converts.pi_not_sort hc

theorem product_cannot_have_product_type {A B D E : Expr S}
    (h : HasType P Γ (.pi A B) (.pi D E)) : False := by
  obtain ⟨s₁, s₂, s₃, hA, hB, hr, hc⟩ := h.generation_pi
  exact Converts.pi_not_sort hc

theorem lambda_cannot_have_sort_type {A b : Expr S} {s : S}
    (h : HasType P Γ (.lam A b) (.sort s)) : False := by
  obtain ⟨B, t, hb, hPi, hc⟩ := h.generation_lam
  exact Converts.pi_not_sort (.symm _ _ hc)

/-- No functionality is needed for neutral uniqueness: the declaration fixes
its head type, and product compatibility fixes every successive codomain. -/
theorem neutral_unique {M A B : Expr S} (hn : Neutral M)
    (hA : HasType P Γ M A) (hB : HasType P Γ M B) : Converts A B := by
  induction hn generalizing A B with
  | var n =>
      obtain ⟨D, hD, hcD⟩ := hA.generation
      obtain ⟨E, hE, hcE⟩ := hB.generation
      have heq : D = E := by
        clear hA hB hcD hcE
        induction hD generalizing E with
        | zero A Γ => cases hE; rfl
        | succ C hD ih =>
            cases hE with
            | succ _ hE => exact congrArg (Expr.rename Nat.succ) (ih _ hE)
      subst E
      exact .trans _ _ _ hcD (.symm _ _ hcE)
  | @app f a hn ih =>
      obtain ⟨D, E, hf, ha, hc⟩ := hA.generation_app
      obtain ⟨D', E', hf', ha', hc'⟩ := hB.generation_app
      have he := (ih hf hf').product_compatibility.2
      exact .trans _ _ _ hc (.trans _ _ _ (he.subst (Expr.single a)) (.symm _ _ hc'))

theorem normal_shape {M T : Expr S} (h : HasType P Γ M T) (hn : Normal M) :
    (∃ s, M = .sort s) ∨ Neutral M ∨ (∃ A B, M = .pi A B) ∨
      (∃ A b, M = .lam A b) := by
  induction M generalizing T with
  | var n => exact .inr (.inl (.var n))
  | sort s => exact .inl ⟨s, rfl⟩
  | lam A b ihA ihb => exact .inr (.inr (.inr ⟨A, b, rfl⟩))
  | pi A B ihA ihB => exact .inr (.inr (.inl ⟨A, B, rfl⟩))
  | app f a ihf iha =>
      obtain ⟨D, E, hf, ha, hc⟩ := h.generation_app
      obtain ⟨s, rfl⟩ | hnf | ⟨A, B, rfl⟩ | ⟨A, b, rfl⟩ := ihf hf hn.app_left
      · exact False.elim hf.sort_cannot_have_product_type
      · exact .inr (.inl (.app hnf))
      · exact False.elim hf.product_cannot_have_product_type
      · exact False.elim (hn _ (.head A b a))

theorem sorted_normal_shape {M : Expr S} {s : S}
    (h : HasType P Γ M (.sort s)) (hn : Normal M) :
    (∃ t, M = .sort t) ∨ Neutral M ∨ (∃ A B, M = .pi A B) := by
  obtain h | h | h | ⟨A, b, rfl⟩ := h.normal_shape hn
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr h)
  · exact False.elim h.lambda_cannot_have_sort_type

end HasType

/-! Finite syntax-directed typing trees, with all generation witnesses
retained; no functionality or unique sort choices are imposed. -/

inductive TypingTree {S : Type u} (P : Specification S) :
    List (Expr S) → Expr S → Expr S → Type u
  | var {Γ n A T} (typing : HasType P Γ (.var n) T)
      (declaration : Lookup Γ n A) (convert : Converts T A) : TypingTree P Γ (.var n) T
  | sort {Γ s t T} (typing : HasType P Γ (.sort s) T)
      (axioms : P.axioms s t) (convert : Converts T (.sort t)) : TypingTree P Γ (.sort s) T
  | product {Γ A B a b c T} (typing : HasType P Γ (.pi A B) T)
      (domain : TypingTree P Γ A (.sort a)) (body : TypingTree P (A :: Γ) B (.sort b))
      (rule : P.rule a b c) (convert : Converts T (.sort c)) : TypingTree P Γ (.pi A B) T
  | abstraction {Γ A b B a s T} (typing : HasType P Γ (.lam A b) T)
      (annotation : TypingTree P Γ A (.sort a)) (body : TypingTree P (A :: Γ) b B)
      (product : HasType P Γ (.pi A B) (.sort s)) (convert : Converts T (.pi A B)) :
      TypingTree P Γ (.lam A b) T
  | application {Γ f a A B T} (typing : HasType P Γ (.app f a) T)
      (function : TypingTree P Γ f (.pi A B)) (argument : TypingTree P Γ a A)
      (convert : Converts T (B.instantiate a)) : TypingTree P Γ (.app f a) T

namespace TypingTree
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M T : Expr S}

/-- Root expected judgment, including the potentially unsorted final sort. -/
theorem typing (t : TypingTree P Γ M T) : HasType P Γ M T := by
  cases t with
  | var h _ _ => exact h
  | sort h _ _ => exact h
  | product h _ _ _ _ => exact h
  | abstraction h _ _ _ _ => exact h
  | application h _ _ _ => exact h

/-- Retarget only the root; all core data and all children are unchanged. -/
def retarget {T' : Expr S} (t : TypingTree P Γ M T)
    (ht : HasType P Γ M T') (hc : Converts T' T) : TypingTree P Γ M T' := by
  cases t with
  | var _ hd he => exact .var ht hd (.trans _ _ _ hc he)
  | sort _ ha he => exact .sort ht ha (.trans _ _ _ hc he)
  | product _ d b hr he => exact .product ht d b hr (.trans _ _ _ hc he)
  | abstraction _ d b hp he => exact .abstraction ht d b hp (.trans _ _ _ hc he)
  | application _ f a he => exact .application ht f a (.trans _ _ _ hc he)

/-- Generation proves existence of finite stored trees without eliminating a
Prop-valued typing derivation into data or assuming unique formation triples. -/
theorem nonempty (h : HasType P Γ M T) : Nonempty (TypingTree P Γ M T) := by
  induction M generalizing Γ T with
  | var n =>
      obtain ⟨A, hd, hc⟩ := h.generation
      exact ⟨.var h hd hc⟩
  | sort s =>
      obtain ⟨t, ha, hc⟩ := h.generation
      exact ⟨.sort h ha hc⟩
  | pi A B ihA ihB =>
      obtain ⟨a, b, c, hA, hB, hr, hc⟩ := h.generation_pi
      exact ⟨.product h (ihA hA).some (ihB hB).some hr hc⟩
  | lam A b ihA ihb =>
      obtain ⟨B, s, hb, hp, hc⟩ := h.generation_lam
      obtain ⟨a, a', c, hA, _, _, _⟩ := hp.generation_pi
      exact ⟨.abstraction h (ihA hA).some (ihb hb).some hp hc⟩
  | app f a ihf iha =>
      obtain ⟨A, B, hf, ha, hc⟩ := h.generation_app
      exact ⟨.application h (ihf hf).some (iha ha).some hc⟩

noncomputable def ofTyping (h : HasType P Γ M T) : TypingTree P Γ M T := (nonempty h).some

/-- A genuine variable renaming sends declarations to declarations, rather
than merely to terms that happen to have convertible types. -/
def DeclRenaming (Γ Δ : List (Expr S)) (ρ : Nat → Nat) : Prop :=
  ∀ n A, Lookup Γ n A → Lookup Δ (ρ n) (A.rename ρ)

namespace DeclRenaming
variable {Δ : List (Expr S)} {ρ : Nat → Nat}
theorem typed (h : DeclRenaming Γ Δ ρ) (hΔ : ValidContext P Δ) :
    ∀ n A, Lookup Γ n A → HasType P Δ (.var (ρ n)) (A.rename ρ) :=
  fun n A hn => HasType.lookup hΔ (h n A hn)

theorem lift (h : DeclRenaming Γ Δ ρ) (A : Expr S) :
    DeclRenaming (A :: Γ) (A.rename ρ :: Δ) (Expr.liftRen ρ) := by
  intro n B hn
  cases hn with
  | zero =>
      simpa only [Expr.liftRen, Expr.rename_comp, Function.comp_def] using Lookup.zero (A.rename ρ) Δ
  | succ _ hn =>
      have hh := Lookup.succ (A.rename ρ) (h _ _ hn)
      simpa only [Expr.liftRen, Expr.rename_comp, Function.comp_def] using hh
end DeclRenaming

/-- Thinning/reindexing transports every stored witness and preserves the
whole tree shape. Binder annotations are transported too. -/
noncomputable def rename (t : TypingTree P Γ M T) {Δ : List (Expr S)} (hΔ : ValidContext P Δ)
    (ρ : Nat → Nat) (hρ : DeclRenaming Γ Δ ρ) :
    TypingTree P Δ (M.rename ρ) (T.rename ρ) := by
  induction t generalizing Δ ρ with
  | var h hd hc => exact .var (h.rename hΔ ρ (hρ.typed hΔ)) (hρ _ _ hd) (hc.rename ρ)
  | sort h ha hc => exact .sort (h.rename hΔ ρ (hρ.typed hΔ)) ha (hc.rename ρ)
  | @product Γ A B a b c T h d e hr hc ihd ihe =>
      have hA : HasType P Δ (A.rename ρ) (.sort a) := d.typing.rename hΔ ρ (hρ.typed hΔ)
      exact .product (h.rename hΔ ρ (hρ.typed hΔ)) (ihd hΔ ρ hρ)
        (ihe (.cons hΔ hA) _ (hρ.lift A)) hr (hc.rename ρ)
  | @abstraction Γ A b B a s T h d e hp hc ihd ihe =>
      have hA : HasType P Δ (A.rename ρ) (.sort a) := d.typing.rename hΔ ρ (hρ.typed hΔ)
      exact .abstraction (h.rename hΔ ρ (hρ.typed hΔ)) (ihd hΔ ρ hρ)
        (ihe (.cons hΔ hA) _ (hρ.lift A)) (hp.rename hΔ ρ (hρ.typed hΔ)) (hc.rename ρ)
  | application h f a hc ihf iha =>
      apply TypingTree.application (h.rename hΔ ρ (hρ.typed hΔ)) (ihf hΔ ρ hρ) (iha hΔ ρ hρ)
      simpa only [Expr.instantiate_rename] using hc.rename ρ

namespace DeclRenaming
variable {Δ : List (Expr S)}
theorem weaken (A : Expr S) : DeclRenaming Γ (A :: Γ) Nat.succ :=
  fun _ _ h => .succ A h
end DeclRenaming

/-- Substitution carries stored trees at all declaration occurrences. -/
abbrev StoredSubstitution (P : Specification S) (Γ Δ : List (Expr S))
    (σ : Nat → Expr S) : Type u :=
  ∀ n A, Lookup Γ n A → TypingTree P Δ (σ n) (A.subst σ)

namespace StoredSubstitution
variable {Δ : List (Expr S)} {σ : Nat → Expr S}
theorem typed (ts : StoredSubstitution P Γ Δ σ) : TypedSubstitution P Γ Δ σ :=
  fun n A hn => (ts n A hn).typing

noncomputable def lift (ts : StoredSubstitution P Γ Δ σ) {A : Expr S} {s : S}
    (hA : HasType P Δ (A.subst σ) (.sort s)) :
    StoredSubstitution P (A :: Γ) (A.subst σ :: Δ) (Expr.liftSub σ) :=
  fun n => match n with
  | 0 => fun B hn => by
      have he : B = A.rename Nat.succ := by cases hn; rfl
      have he' : B.subst (Expr.liftSub σ) = (A.subst σ).rename Nat.succ := by
        rw [he,Expr.subst_rename,Expr.rename_subst]
        rfl
      exact .var (he'.symm ▸ HasType.var hA) (.zero _ _) (by rw [he']; exact .refl _)
  | n+1 => fun B hn => by
      let hex : ∃ B', Lookup Γ n B' ∧ B = B'.rename Nat.succ := by
        cases hn with
        | succ _ h => exact ⟨_, h, rfl⟩
      let tt := (ts _ _ hex.choose_spec.1).rename (.cons hA.valid hA) Nat.succ (DeclRenaming.weaken _)
      have he : B.subst (Expr.liftSub σ) = (hex.choose.subst σ).rename Nat.succ := by
        calc
          B.subst (Expr.liftSub σ) = (hex.choose.rename Nat.succ).subst (Expr.liftSub σ) :=
            congrArg (Expr.subst (Expr.liftSub σ)) hex.choose_spec.2
          _ = (hex.choose.subst σ).rename Nat.succ := by
            rw [Expr.subst_rename,Expr.rename_subst]
            rfl
      exact tt.retarget (he.symm ▸ tt.typing) (by rw [he]; exact .refl _)

end StoredSubstitution

/-- Capture-avoiding substitution grafts the given trees at variables. It
retains core choices and recurses through the annotation at each binder. -/
noncomputable def subst (t : TypingTree P Γ M T) {Δ : List (Expr S)}
    (hΔ : ValidContext P Δ) (σ : Nat → Expr S) (ts : StoredSubstitution P Γ Δ σ) :
    TypingTree P Δ (M.subst σ) (T.subst σ) := by
  induction t generalizing Δ σ with
  | var h hd hc => exact (ts _ _ hd).retarget (h.subst hΔ σ ts.typed) (hc.subst σ)
  | sort h ha hc => exact .sort (h.subst hΔ σ ts.typed) ha (hc.subst σ)
  | @product Γ A B a b c T h d e hr hc ihd ihe =>
      have hA : HasType P Δ (A.subst σ) (.sort a) := d.typing.subst hΔ σ ts.typed
      exact .product (h.subst hΔ σ ts.typed) (ihd hΔ σ ts)
        (ihe (.cons hΔ hA) _ (ts.lift hA)) hr (hc.subst σ)
  | @abstraction Γ A b B a s T h d e hp hc ihd ihe =>
      have hA : HasType P Δ (A.subst σ) (.sort a) := d.typing.subst hΔ σ ts.typed
      exact .abstraction (h.subst hΔ σ ts.typed) (ihd hΔ σ ts)
        (ihe (.cons hΔ hA) _ (ts.lift hA)) (hp.subst hΔ σ ts.typed) (hc.subst σ)
  | application h f a hc ihf iha =>
      apply TypingTree.application (h.subst hΔ σ ts.typed) (ihf hΔ σ ts) (iha hΔ σ ts)
      simpa only [Expr.instantiate_subst] using hc.subst σ

end TypingTree

namespace Expr
variable {S : Type u}
def ProperPart (N M : Expr S) : Prop := ∃ K, Child K M ∧ Subterm N K
@[simp] theorem subst_apps (M : Expr S) (ns : List (Expr S)) (σ : Nat → Expr S) :
    (M.apps ns).subst σ = (M.subst σ).apps (ns.map (Expr.subst σ)) := by
  induction ns generalizing M with
  | nil => rfl
  | cons n ns ih => exact ih (.app M n)
end Expr

namespace Normal

variable {S : Type u}

theorem rename {M : Expr S} (h : Normal M) (ρ : Nat → Nat) :
    Normal (M.rename ρ) := by
  induction M generalizing ρ with
  | var n => exact Normal.var _
  | sort s => exact Normal.sort _
  | pi A B ihA ihB => exact (ihA h.pi_domain ρ).pi (ihB h.pi_body _)
  | lam A b ihA ihb => exact (ihA h.lam_domain ρ).lam (ihb h.lam_body _)
  | app f a ihf iha =>
      have hf := ihf h.app_left ρ
      have ha := iha h.app_right ρ
      cases f with
      | lam D b => exact False.elim (h _ (.head D b a))
      | var n | sort s | app f b | pi D B =>
          intro N hN
          cases hN with
          | app_left hr => exact hf _ hr
          | app_right hr => exact ha _ hr

end Normal

end PureTypeSystem

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Contexts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem

universe u

deriving instance Countable for Expr

namespace Expr

variable {S : Type u}

/-- Every free index is below the context length. -/
def Scoped : Nat → Expr S → Prop
  | n, .var i => i < n
  | _, .sort _ => True
  | n, .app M N => Scoped n M ∧ Scoped n N
  | n, .lam A b => Scoped n A ∧ Scoped (n+1) b
  | n, .pi A B => Scoped n A ∧ Scoped (n+1) B

namespace Scoped

variable {n m : Nat} {M : Expr S}

theorem rename (h : Scoped n M) (ρ : Nat → Nat)
    (hρ : ∀ i, i < n → ρ i < m) : Scoped m (M.rename ρ) := by
  induction M generalizing n m ρ with
  | var i => exact hρ i h
  | sort _ => trivial
  | app M N ihM ihN => exact ⟨ihM h.1 _ hρ, ihN h.2 _ hρ⟩
  | lam A b ihA ihb | pi A b ihA ihb =>
      refine ⟨ihA h.1 _ hρ, ihb h.2 _ ?_⟩
      intro i hi
      cases i with
      | zero => exact Nat.zero_lt_succ _
      | succ i => exact Nat.succ_lt_succ (hρ i (Nat.lt_of_succ_lt_succ hi))

theorem rename_congr (h : Scoped n M) {ρ τ : Nat → Nat}
    (he : ∀ i, i < n → ρ i = τ i) : M.rename ρ = M.rename τ := by
  induction M generalizing n ρ τ with
  | var i => exact congrArg Expr.var (he i h)
  | sort _ => rfl
  | app M N ihM ihN => exact congrArg₂ Expr.app (ihM h.1 he) (ihN h.2 he)
  | lam A b ihA ihb | pi A b ihA ihb =>
      have hl : ∀ i, i < n+1 → liftRen ρ i = liftRen τ i := by
        intro i hi
        cases i with
        | zero => rfl
        | succ i => exact congrArg Nat.succ (he i (Nat.lt_of_succ_lt_succ hi))
      simp only [Expr.rename, ihA h.1 he, ihb h.2 hl]

theorem subst (h : Scoped n M) (σ : Nat → Expr S)
    (hσ : ∀ i, i < n → Scoped m (σ i)) : Scoped m (M.subst σ) := by
  induction M generalizing n m σ with
  | var i => exact hσ i h
  | sort _ => trivial
  | app M N ihM ihN => exact ⟨ihM h.1 _ hσ, ihN h.2 _ hσ⟩
  | lam A b ihA ihb | pi A b ihA ihb =>
      refine ⟨ihA h.1 _ hσ, ihb h.2 _ ?_⟩
      intro i hi
      cases i with
      | zero => exact Nat.zero_lt_succ _
      | succ i =>
          exact (hσ i (Nat.lt_of_succ_lt_succ hi)).rename Nat.succ
            (fun _ hi => Nat.succ_lt_succ hi)

theorem instantiate {b a : Expr S} (hb : Scoped (n+1) b) (ha : Scoped n a) :
    Scoped n (b.instantiate a) := by
  apply hb.subst
  intro i hi
  cases i with
  | zero => exact ha
  | succ i => exact Nat.lt_of_succ_lt_succ hi

end Scoped

/-- Reversal identifies de Bruijn indices in a finite context with fixed levels.
Outside that context it is the identity. -/
def reverseIndex (n i : Nat) : Nat := if i < n then n - 1 - i else i

theorem reverseIndex_lt {n i : Nat} (hi : i < n) : reverseIndex n i < n := by
  simp only [reverseIndex, ite_eq_left hi]
  omega

theorem reverseIndex_involutive (n : Nat) : Function.Involutive (reverseIndex n) := by
  intro i
  unfold reverseIndex
  split_ifs <;> omega

@[simp] theorem reverseIndex_twice (n : Nat) (M : Expr S) :
    (M.rename (reverseIndex n)).rename (reverseIndex n) = M := by
  rw [rename_comp]
  have he : reverseIndex n ∘ reverseIndex n = id := funext (reverseIndex_involutive n)
  rw [he, rename_id]

theorem Scoped.reverseIndex {n : Nat} {M : Expr S} (h : Scoped n M) :
    Scoped n (M.rename (reverseIndex n)) :=
  h.rename _ (fun _ hi => reverseIndex_lt hi)

theorem Scoped.reverseIndex_succ {n : Nat} {M : Expr S} (h : Scoped n M) :
    M.rename (Expr.reverseIndex (n+1)) = (M.rename (Expr.reverseIndex n)).rename Nat.succ := by
  rw [rename_comp]
  apply h.rename_congr
  intro i hi
  simp only [Function.comp_apply, Expr.reverseIndex, ite_eq_left hi]
  rw [ite_eq_left (Nat.lt_succ_of_lt hi)]
  omega

end Expr

namespace HasType

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M A : Expr S}

theorem scope (h : HasType P Γ M A) : M.Scoped Γ.length ∧ A.Scoped Γ.length := by
  induction h with
  | ax _ => exact ⟨True.intro, True.intro⟩
  | var _ ih =>
      exact ⟨Nat.zero_lt_succ _, ih.1.rename Nat.succ (fun _ hi => Nat.succ_lt_succ hi)⟩
  | weaken _ _ ih _ =>
      exact ⟨ih.1.rename Nat.succ (fun _ hi => Nat.succ_lt_succ hi),
        ih.2.rename Nat.succ (fun _ hi => Nat.succ_lt_succ hi)⟩
  | product _ _ _ ihA ihB => exact ⟨⟨ihA.1, ihB.1⟩, True.intro⟩
  | abstraction _ _ ihb ihPi => exact ⟨⟨ihPi.1.1, ihb.1⟩, ihPi.1⟩
  | application _ _ ihf iha => exact ⟨⟨ihf.1, iha.1⟩, ihf.2.2.instantiate iha.1⟩
  | conversion _ _ _ ihM ihB => exact ⟨ihM.1, ihB.1⟩

end HasType

namespace WeaklyNormalizing

variable {S : Type u} {M : Expr S}

theorem rename (h : WeaklyNormalizing M) (ρ : Nat → Nat) :
    WeaklyNormalizing (M.rename ρ) := by
  obtain ⟨N, hr, hn⟩ := h
  exact ⟨N.rename ρ, Reduces.rename hr ρ, hn.rename ρ⟩

theorem reverseIndex_iff (n : Nat) :
    WeaklyNormalizing (M.rename (Expr.reverseIndex n)) ↔ WeaklyNormalizing M := by
  constructor
  · intro h
    simpa only [Expr.reverseIndex_twice] using h.rename (Expr.reverseIndex n)
  · intro h
    exact h.rename _

end WeaklyNormalizing

/-- Finite prefixes of a common context, using fixed-level names when viewed
outside a prefix. Every sortable fixed-level expression is declared arbitrarily
late. Bound variables remain de Bruijn indices and are never declared here. -/
structure ContextTower {S : Type u} (P : Specification S) where
  context : Nat → List (Expr S)
  valid : ∀ n, ValidContext P (context n)
  length : ∀ n, (context n).length = n
  step : ∀ n, ∃ A s, HasType P (context n) A (.sort s) ∧ context (n+1) = A :: context n
  saturated : ∀ (n : Nat) (A : Expr S) (s : S), HasType P (context n) (A.rename (Expr.reverseIndex n)) (.sort s) →
    ∀ lower, ∃ m, n ≤ m ∧ lower ≤ m ∧
      context (m+1) = A.rename (Expr.reverseIndex m) :: context m

namespace ContextTowerConstruction

variable {S : Type u} (P : Specification S)

structure Stage (n : Nat) where
  context : List (Expr S)
  valid : ValidContext P context
  length : context.length = n

variable [Countable S]

noncomputable def enumeration : Nat → Expr S := by
  letI : Nonempty (Expr S) := ⟨.var 0⟩
  exact (exists_surjective_nat (Expr S)).choose

theorem enumeration_surjective : Function.Surjective (enumeration (S := S)) := by
  let : Nonempty (Expr S) := ⟨.var 0⟩
  exact (exists_surjective_nat (Expr S)).choose_spec

noncomputable def scheduled (n : Nat) : Expr S := enumeration (Nat.unpair n).1

theorem scheduled_late (A : Expr S) (lower : Nat) :
    ∃ m, lower ≤ m ∧ scheduled m = A := by
  obtain ⟨k, hk⟩ := enumeration_surjective A
  exact ⟨Nat.pair k lower, Nat.right_le_pair _ _, by simpa only [scheduled, Nat.unpair_pair]⟩

variable {s₀ t₀ : S} (h₀ : P.axioms s₀ t₀)

noncomputable def next {n : Nat} (Γ : Stage P n) :
    {A : Expr S // ∃ s, HasType P Γ.context A (.sort s)} := by
  classical
  let A : Expr S := (scheduled n).rename (Expr.reverseIndex n)
  exact if ht : ∃ s, HasType P Γ.context A (.sort s) then ⟨A, ht⟩
    else ⟨.sort s₀, t₀, HasType.sort_of_valid Γ.valid h₀⟩

noncomputable def stages : (n : Nat) → Stage P n
  | 0 => ⟨[], .nil, rfl⟩
  | n+1 =>
      let Γ := stages n
      let A := next P h₀ Γ
      ⟨A.val :: Γ.context, .cons Γ.valid A.property.choose_spec,
        by simp only [List.length_cons, Γ.length]⟩

noncomputable def contexts (n : Nat) : List (Expr S) := (stages P h₀ n).context

theorem valid (n : Nat) : ValidContext P (contexts P h₀ n) := (stages P h₀ n).valid

theorem length (n : Nat) : (contexts P h₀ n).length = n := (stages P h₀ n).length

theorem step (n : Nat) : ∃ A s, HasType P (contexts P h₀ n) A (.sort s) ∧
    contexts P h₀ (n+1) = A :: contexts P h₀ n :=
  ⟨(next P h₀ (stages P h₀ n)).val, _, (next P h₀ (stages P h₀ n)).property.choose_spec, rfl⟩

theorem rename_next {n : Nat} {M A : Expr S}
    (h : HasType P (contexts P h₀ n) (M.rename (Expr.reverseIndex n))
      (A.rename (Expr.reverseIndex n))) :
    HasType P (contexts P h₀ (n+1)) (M.rename (Expr.reverseIndex (n+1)))
      (A.rename (Expr.reverseIndex (n+1))) := by
  have hm : M.Scoped n := by
    have hh := h.scope.1.reverseIndex
    rw [length, Expr.reverseIndex_twice] at hh
    exact hh
  have ha : A.Scoped n := by
    have hh := h.scope.2.reverseIndex
    rw [length, Expr.reverseIndex_twice] at hh
    exact hh
  obtain ⟨D, s, ht, he⟩ := step P h₀ n
  rw [he, hm.reverseIndex_succ, ha.reverseIndex_succ]
  exact .weaken h ht

theorem rename_mono {n m : Nat} {M A : Expr S}
    (h : HasType P (contexts P h₀ n) (M.rename (Expr.reverseIndex n))
      (A.rename (Expr.reverseIndex n))) (hnm : n ≤ m) :
    HasType P (contexts P h₀ m) (M.rename (Expr.reverseIndex m))
      (A.rename (Expr.reverseIndex m)) := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact rename_next P h₀ ih

theorem at_scheduled {n : Nat} (s : S)
    (h : HasType P (contexts P h₀ n) ((scheduled n).rename (Expr.reverseIndex n)) (.sort s)) :
    contexts P h₀ (n+1) = (scheduled n).rename (Expr.reverseIndex n) :: contexts P h₀ n := by
  classical
  have ht : ∃ t, HasType P (stages P h₀ n).context
      ((scheduled n).rename (Expr.reverseIndex n)) (.sort t) := ⟨s,h⟩
  simp only [contexts, stages, next, dite_eq_left ht]

theorem saturated (n : Nat) (A : Expr S) (s : S)
    (h : HasType P (contexts P h₀ n) (A.rename (Expr.reverseIndex n)) (.sort s))
    (lower : Nat) : ∃ m, n ≤ m ∧ lower ≤ m ∧
      contexts P h₀ (m+1) = A.rename (Expr.reverseIndex m) :: contexts P h₀ m := by
  obtain ⟨m, hm, he⟩ := scheduled_late A (max n lower)
  have hnm : n ≤ m := (le_max_left _ _).trans hm
  have hlm : lower ≤ m := (le_max_right _ _).trans hm
  have ht : HasType P (contexts P h₀ m) (A.rename (Expr.reverseIndex m)) (.sort s) :=
    rename_mono P h₀ (A := .sort s) h hnm
  refine ⟨m, hnm, hlm, ?_⟩
  have hs : HasType P (contexts P h₀ m)
      ((scheduled m).rename (Expr.reverseIndex m)) (.sort s) := by
    rw [he]
    exact ht
  calc
    contexts P h₀ (m+1) = (scheduled m).rename (Expr.reverseIndex m) :: contexts P h₀ m :=
      at_scheduled P h₀ s hs
    _ = A.rename (Expr.reverseIndex m) :: contexts P h₀ m :=
      congrArg (fun B : Expr S => B.rename (Expr.reverseIndex m) :: contexts P h₀ m) he

noncomputable def tower : ContextTower P where
  context := contexts P h₀
  valid := valid P h₀
  length := length P h₀
  step := step P h₀
  saturated := saturated P h₀

end ContextTowerConstruction

namespace ContextTower

variable {S : Type u} {P : Specification S} (Ω : ContextTower P)

/-- A global judgment is witnessed in a finite prefix of the tower. -/
def HasType (M A : Expr S) : Prop :=
  ∃ n, PureTypeSystem.HasType P (Ω.context n) (M.rename (Expr.reverseIndex n))
    (A.rename (Expr.reverseIndex n))

theorem at_next {n : Nat} {M A : Expr S}
    (h : PureTypeSystem.HasType P (Ω.context n) (M.rename (Expr.reverseIndex n))
      (A.rename (Expr.reverseIndex n))) :
    PureTypeSystem.HasType P (Ω.context (n+1)) (M.rename (Expr.reverseIndex (n+1)))
      (A.rename (Expr.reverseIndex (n+1))) := by
  have hm : M.Scoped n := by
    have hh := h.scope.1.reverseIndex
    rw [Ω.length, Expr.reverseIndex_twice] at hh
    exact hh
  have ha : A.Scoped n := by
    have hh := h.scope.2.reverseIndex
    rw [Ω.length, Expr.reverseIndex_twice] at hh
    exact hh
  obtain ⟨D, s, ht, he⟩ := Ω.step n
  rw [he, hm.reverseIndex_succ, ha.reverseIndex_succ]
  exact .weaken h ht

theorem at_mono {n m : Nat} {M A : Expr S}
    (h : PureTypeSystem.HasType P (Ω.context n) (M.rename (Expr.reverseIndex n))
      (A.rename (Expr.reverseIndex n))) (hnm : n ≤ m) :
    PureTypeSystem.HasType P (Ω.context m) (M.rename (Expr.reverseIndex m))
      (A.rename (Expr.reverseIndex m)) := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact Ω.at_next ih

namespace HasType

variable {Ω : ContextTower P} {M A : Expr S}

theorem weaklyNormalizing (h : Ω.HasType M A) (hw : SystemWeaklyNormalizing P) :
    WeaklyNormalizing M := by
  obtain ⟨n, ht⟩ := h
  exact (WeaklyNormalizing.reverseIndex_iff n).mp (hw _ ht.valid _ ⟨_, Or.inl ht⟩)

theorem type_weaklyNormalizing (h : Ω.HasType M A) (hw : SystemWeaklyNormalizing P) :
    WeaklyNormalizing A := by
  obtain ⟨n, ht⟩ := h
  exact (WeaklyNormalizing.reverseIndex_iff n).mp (hw _ ht.valid _ ⟨_, Or.inr ht⟩)

theorem common {N B : Expr S} (h : Ω.HasType M A) (k : Ω.HasType N B) :
    ∃ n, PureTypeSystem.HasType P (Ω.context n) (M.rename (Expr.reverseIndex n))
      (A.rename (Expr.reverseIndex n)) ∧
      PureTypeSystem.HasType P (Ω.context n) (N.rename (Expr.reverseIndex n))
      (B.rename (Expr.reverseIndex n)) := by
  obtain ⟨n, ht⟩ := h
  obtain ⟨m, kt⟩ := k
  exact ⟨max n m, Ω.at_mono ht (le_max_left _ _), Ω.at_mono kt (le_max_right _ _)⟩

end HasType

end ContextTower

namespace ContextTower.HasType

variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable {M N A B : Expr S}

theorem application (hf : Ω.HasType M (.pi A B)) (ha : Ω.HasType N A) :
    Ω.HasType (.app M N) (B.instantiate N) := by
  obtain ⟨n, hf, ha⟩ := hf.common ha
  refine ⟨n, ?_⟩
  simpa only [Expr.rename, Expr.instantiate_rename] using
    PureTypeSystem.HasType.application hf ha

theorem conversion {s : S} (hM : Ω.HasType M A) (hB : Ω.HasType B (.sort s))
    (hc : Converts A B) : Ω.HasType M B := by
  obtain ⟨n, hM, hB⟩ := hM.common hB
  exact ⟨n, .conversion hM hB (hc.rename _)⟩

theorem subject_reduces (h : Ω.HasType M A) (hr : Reduces M N) : Ω.HasType N A := by
  obtain ⟨n, h⟩ := h
  exact ⟨n, h.subject_reduces (hr.rename _)⟩

theorem regularity (h : Ω.HasType M A) :
    (∃ s, A = .sort s) ∨ (∃ s, Ω.HasType A (.sort s)) := by
  obtain ⟨n, h⟩ := h
  obtain ⟨s, he⟩ | ⟨s, hs⟩ := h.regularity
  · left
    refine ⟨s, ?_⟩
    have he' := congrArg (Expr.rename (Expr.reverseIndex n)) he
    simpa only [Expr.reverseIndex_twice, Expr.rename] using he'
  · exact .inr ⟨s, n, hs⟩

theorem normalForm (h : Ω.HasType M A) (hw : SystemWeaklyNormalizing P) :
    Ω.HasType M.normalForm A :=
  h.subject_reduces (Expr.normalForm_spec (h.weaklyNormalizing hw)).1

theorem normalize_type (h : Ω.HasType M A) (hw : SystemWeaklyNormalizing P) :
    Ω.HasType M A.normalForm := by
  obtain ⟨s, rfl⟩ | ⟨s, hA⟩ := h.regularity
  · simpa only [Expr.normalForm_of_normal (Normal.sort s)] using h
  · exact .conversion h (hA.normalForm hw)
      (Expr.normalForm_spec (h.type_weaklyNormalizing hw)).1.converts

end ContextTower.HasType

/-! Finite generic contexts may have arbitrary raw actual images in the
saturated tower. Every such substitution is witnessed in one finite prefix;
no normalization or strong-normalization of the images is assumed. -/
namespace ContextTower
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)

def TypedSubstitution (Γ : List (Expr S)) (σ : Nat → Expr S) : Prop :=
  ∀ n A, Lookup Γ n A → Ω.HasType (σ n) (A.subst σ)

namespace TypedSubstitution
variable {Ω} {Γ : List (Expr S)} {σ : Nat → Expr S}

theorem tail {A : Expr S} (h : Ω.TypedSubstitution (A :: Γ) σ) :
    Ω.TypedSubstitution Γ (σ ∘ Nat.succ) := by
  intro n B hn
  have hh := h (n+1) (B.rename Nat.succ) (.succ A hn)
  simpa only [Expr.subst_rename, Function.comp_apply] using hh

/-- One common stage suffices for every declaration image, despite the
substitution being presented as a total function on indices. -/
theorem common_stage (h : Ω.TypedSubstitution Γ σ) :
    ∃ k, ∀ n A, Lookup Γ n A →
      PureTypeSystem.HasType P (Ω.context k) ((σ n).rename (Expr.reverseIndex k))
        ((A.subst σ).rename (Expr.reverseIndex k)) := by
  induction Γ generalizing σ with
  | nil => exact ⟨0, fun _ _ hn => nomatch hn⟩
  | cons B Γ ih =>
      obtain ⟨k, hk⟩ := ih h.tail
      obtain ⟨m, hm⟩ := h 0 (B.rename Nat.succ) (.zero B Γ)
      refine ⟨max k m, ?_⟩
      intro n A hn
      cases hn with
      | zero => exact Ω.at_mono hm (le_max_right k m)
      | succ B hn =>
          have hh := Ω.at_mono (hk _ _ hn) (le_max_left k m)
          simpa only [Expr.subst_rename, Function.comp_apply] using hh

/-- Extension assigns a raw term to the fresh generic binder. -/
theorem cons {A a : Expr S} (h : Ω.TypedSubstitution Γ σ)
    (ha : Ω.HasType a (A.subst σ)) : Ω.TypedSubstitution (A :: Γ) (fun n => match n with
      | 0 => a | n+1 => σ n) := by
  intro n B hn
  cases hn with
  | zero => simpa only [Expr.subst_rename, Function.comp_def] using ha
  | succ A hn => simpa only [Expr.subst_rename, Function.comp_def] using h _ _ hn
end TypedSubstitution

namespace HasType
variable {Ω} {Γ : List (Expr S)} {M A : Expr S} {σ : Nat → Expr S}

/-- Arbitrary typed substitution from a finite generic context to the tower. -/
theorem subst (h : PureTypeSystem.HasType P Γ M A) (hσ : Ω.TypedSubstitution Γ σ) :
    Ω.HasType (M.subst σ) (A.subst σ) := by
  obtain ⟨k, hk⟩ := TypedSubstitution.common_stage hσ
  refine ⟨k, ?_⟩
  have hh := h.subst (Ω.valid k) (fun n => (σ n).rename (Expr.reverseIndex k)) (fun n B hn => by
    simpa only [← Expr.rename_subst] using hk n B hn)
  simpa only [← Expr.rename_subst] using hh
end HasType

namespace TypedSubstitution
variable {Ω} {Γ : List (Expr S)} {σ τ : Nat → Expr S}

theorem comp {Δ : List (Expr S)} (h : Ω.TypedSubstitution Δ τ)
    (hσ : PureTypeSystem.TypedSubstitution P Γ Δ σ) :
    Ω.TypedSubstitution Γ (fun n => (σ n).subst τ) := by
  intro n A hn
  simpa only [Expr.subst_subst] using HasType.subst (hσ n A hn) h

end TypedSubstitution

end ContextTower
end PureTypeSystem

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Candidates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem

universe u

namespace Candidates

variable {S : Type u} {P : Specification S} (Ω : ContextTower P)

/-- Source actual types: a normal sorted expression, or a literal sort. -/
def ActualType (T : Expr S) : Prop :=
  (Normal T ∧ ∃ s, Ω.HasType T (.sort s)) ∨ ∃ s, T = .sort s

def Top (T : Expr S) : Set (Expr S) :=
  {M | Ω.HasType M T ∧ StronglyNormalizing M}

/-- Tests follow the exact normal successive types, not other typings. -/
inductive TestedStack : Expr S → List (Expr S) → Prop
  | nil (T) : TestedStack T []
  | cons {D E n ns} : n ∈ Top Ω D →
      TestedStack (E.instantiate n).normalForm ns → TestedStack (.pi D E) (n :: ns)

def Ground (T : Expr S) : Set (Expr S) :=
  {M | Ω.HasType M T ∧ ∀ ns, TestedStack Ω T ns → StronglyNormalizing (M.apps ns)}

variable {Ω} {T M : Expr S}

theorem ground_le_top : Ground Ω T ⊆ Top Ω T := by
  intro M h
  exact ⟨h.1, h.2 [] (.nil T)⟩

theorem ground_application (hw : SystemWeaklyNormalizing P) {D E n : Expr S}
    (h : M ∈ Ground Ω (.pi D E)) (hn : n ∈ Top Ω D) :
    .app M n ∈ Ground Ω (E.instantiate n).normalForm := by
  refine ⟨(h.1.application hn.1).normalize_type hw, ?_⟩
  intro ns hs
  exact h.2 (n :: ns) (.cons hn hs)

/-- Head expansion, with exact typing and SN of every annotation/spine component. -/
def ExpansionClosed (Ω : ContextTower P) (T : Expr S) (C : Set (Expr S)) : Prop :=
  ∀ (D b n : Expr S) (ns : List (Expr S)),
    Ω.HasType ((Expr.app (.lam D b) n).apps ns) T →
    StronglyNormalizing D → StronglyNormalizing b → StronglyNormalizing n →
    StronglyNormalizingArgs ns → (b.instantiate n).apps ns ∈ C →
    (Expr.app (.lam D b) n).apps ns ∈ C

structure IsCandidate (Ω : ContextTower P) (T : Expr S) (C : Set (Expr S)) : Prop where
  lower : Ground Ω T ⊆ C
  upper : C ⊆ Top Ω T
  expansion : ExpansionClosed Ω T C

theorem top_candidate : IsCandidate Ω T (Top Ω T) where
  lower := ground_le_top
  upper := Set.Subset.rfl
  expansion := fun _ _ _ _ ht hD hb hn hns hc =>
    ⟨ht, StronglyNormalizing.head_expansion hD hb hn hns hc.2⟩

/-- The bounded intersection makes the empty meet the typed top. -/
def Meet (Ω : ContextTower P) (T : Expr S) (Cs : Set (Set (Expr S))) : Set (Expr S) :=
  {M | M ∈ Top Ω T ∧ ∀ C ∈ Cs, M ∈ C}

theorem meet_candidate {Cs : Set (Set (Expr S))}
    (hCs : ∀ C ∈ Cs, IsCandidate Ω T C) : IsCandidate Ω T (Meet Ω T Cs) where
  lower := fun _ h => ⟨ground_le_top h, fun C hC => (hCs C hC).lower h⟩
  upper := fun _ h => h.1
  expansion := by
    intro D b n ns ht hD hb hn hns hc
    refine ⟨⟨ht, StronglyNormalizing.head_expansion hD hb hn hns hc.1.2⟩, ?_⟩
    intro C hC
    exact (hCs C hC).expansion D b n ns ht hD hb hn hns (hc.2 C hC)

def Bottom (Ω : ContextTower P) (T : Expr S) : Set (Expr S) :=
  Meet Ω T {C | IsCandidate Ω T C}

theorem bottom_candidate : IsCandidate Ω T (Bottom Ω T) :=
  meet_candidate (fun _ h => h)

theorem bottom_le {C : Set (Expr S)} (hC : IsCandidate Ω T C) : Bottom Ω T ⊆ C :=
  fun _ h => h.2 C hC

/-- Arbitrary indexed product tests. -/
def ProductTest (Ω : ContextTower P) (D E : Expr S) (A : Set (Expr S))
    (Cs : Expr S → Set (Set (Expr S))) : Set (Expr S) :=
  {M | M ∈ Top Ω (.pi D E) ∧ ∀ n ∈ A, ∀ C ∈ Cs n, Expr.app M n ∈ C}

theorem productTest_candidate (hw : SystemWeaklyNormalizing P)
    {D E : Expr S} {A : Set (Expr S)} {Cs : Expr S → Set (Set (Expr S))}
    (hA : A ⊆ Top Ω D)
    (hCs : ∀ n ∈ A, ∀ C ∈ Cs n, IsCandidate Ω (E.instantiate n).normalForm C) :
    IsCandidate Ω (.pi D E) (ProductTest Ω D E A Cs) where
  lower := by
    intro M h
    refine ⟨ground_le_top h, ?_⟩
    intro n hn C hC
    exact (hCs n hn C hC).lower (ground_application hw h (hA hn))
  upper := fun _ h => h.1
  expansion := by
    intro D' b a ns ht hD hb ha hns hc
    refine ⟨⟨ht, StronglyNormalizing.head_expansion hD hb ha hns hc.1.2⟩, ?_⟩
    intro n hn C hC
    have ht' := (ht.application (hA hn).1).normalize_type hw
    have hsn : StronglyNormalizingArgs (ns ++ [n]) := by
      apply StronglyNormalizingArgs.of_forall
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hns.of_mem hx
      · have he : x = n := List.mem_singleton.mp hx
        exact he.symm ▸ (hA hn).2
    have hc' := hc.2 n hn C hC
    have he : (Expr.app (.lam D' b) a).apps (ns ++ [n]) =
        .app ((Expr.app (.lam D' b) a).apps ns) n := by
      simp only [Expr.apps_append, Expr.apps]
    have he' : (b.instantiate a).apps (ns ++ [n]) = .app ((b.instantiate a).apps ns) n := by
      simp only [Expr.apps_append, Expr.apps]
    rw [← he] at ht'
    rw [← he'] at hc'
    rw [← he]
    exact (hCs n hn C hC).expansion D' b a (ns ++ [n]) ht' hD hb ha hsn hc'

end Candidates

end PureTypeSystem

namespace PureTypeSystem.Candidates
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) (T : Expr S)

abbrev Candidate := {X : Set (Expr S) // IsCandidate Ω T X}

noncomputable instance instInfSetCandidate : InfSet (Candidate Ω T) where
  sInf Cs := ⟨Meet Ω T (Subtype.val '' Cs), meet_candidate (by
    rintro X ⟨x,_,rfl⟩
    exact x.property)⟩

noncomputable instance instCompleteLatticeCandidate : CompleteLattice (Candidate Ω T) := completeLatticeOfInf _ (by
  intro Cs
  constructor
  · intro x hx M hM
    exact hM.2 x.val ⟨x,hx,rfl⟩
  · intro x hx M hM
    refine ⟨x.property.upper hM,?_⟩
    rintro X ⟨y,hy,rfl⟩
    exact hx hy hM)

/-- Changing coordinate order changes no candidate sets. -/
def SignedCandidate (b : Bool) : Type u := if b then (Candidate Ω T)ᵒᵈ else Candidate Ω T

noncomputable instance instCompleteLatticeSignedCandidate (b : Bool) : CompleteLattice (SignedCandidate Ω T b) := by
  cases b with
  | false => exact inferInstanceAs (CompleteLattice (Candidate Ω T))
  | true => exact inferInstanceAs (CompleteLattice (Candidate Ω T)ᵒᵈ)

namespace SignedCandidate
variable {Ω T} {b : Bool}

def set (X : SignedCandidate Ω T b) : Set (Expr S) := by
  cases b <;> exact X.val

def wrap (X : Candidate Ω T) : SignedCandidate Ω T b := by
  cases b <;> exact X

@[simp] theorem set_wrap (X : Candidate Ω T) : (wrap (b := b) X).set = X.val := by
  cases b <;> rfl

theorem candidate (X : SignedCandidate Ω T b) : IsCandidate Ω T X.set := by
  cases b <;> exact X.property

theorem order (X Y : SignedCandidate Ω T b) :
    X ≤ Y ↔ if b then Y.set ⊆ X.set else X.set ⊆ Y.set := by
  cases b <;> rfl

end SignedCandidate
end PureTypeSystem.Candidates

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Profiles
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate _root_.OAI.PureTypeSystem.instCountableExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem

universe u

/-- Sorts assigned to the full normal form. -/
def Profile {S : Type u} (P : Specification S) (Γ : List (Expr S))
    (T : Expr S) : Set S := {s | HasType P Γ T.normalForm (.sort s)}

def AxProfile {S : Type u} (P : Specification S) (s : S) : Set S :=
  {t | P.axioms s t}

def OutProfile {S : Type u} (P : Specification S) (I J : Set S) : Set S :=
  {c | ∃ a ∈ I, ∃ b ∈ J, P.rule a b c}

/-- Semantic feasible profiles. Normal witnesses are retained, rather than
assuming the manuscript's characterization of this finite set. -/
def FeasibleProfile {S : Type u} (P : Specification S) (I : Set S) : Prop :=
  I.Nonempty ∧ ∃ Γ T, ValidContext P Γ ∧ Normal T ∧ Profile P Γ T = I

structure ProfileTriple {S : Type u} (P : Specification S) (I J K : Set S) : Prop where
  domain : FeasibleProfile P I
  codomain : FeasibleProfile P J
  product : FeasibleProfile P K
  output : K = OutProfile P I J

/-- The sign is true for a domain edge and false for a positive edge. -/
inductive PrimaryEdge {S : Type u} (P : Specification S) :
    Set S → Set S → Bool → Prop
  | inclusion {I J} : FeasibleProfile P I → FeasibleProfile P J →
      J ⊂ I → PrimaryEdge P I J false
  | domain {I J K} : ProfileTriple P I J K → PrimaryEdge P I K true
  | codomain {I J K} : ProfileTriple P I J K → PrimaryEdge P J K false

/-- Finite directed walks, with repeated edges permitted and parity retained. -/
inductive SignedPath {V : Type*} (E : V → V → Bool → Prop) : V → V → Bool → Prop
  | nil (v) : SignedPath E v v false
  | cons {u v w p q} : E u v p → SignedPath E v w q →
      SignedPath E u w (Bool.xor p q)

def Reach {V : Type*} (E : V → V → Bool → Prop) (v w : V) : Prop :=
  ∃ b, SignedPath E v w b

def PositivePath {V : Type*} (E : V → V → Bool → Prop) : V → V → Prop :=
  Relation.ReflTransGen (fun v w => E v w false)

/-- A full strongly connected component, not merely a connected subset. -/
def IsComponent {V : Type*} (E : V → V → Bool → Prop) (C : Set V) : Prop :=
  ∃ r ∈ C, ∀ v, v ∈ C ↔ Reach E r v ∧ Reach E v r

namespace SignedPath

variable {V : Type*} {E : V → V → Bool → Prop}

theorem singleton {v w : V} {p : Bool} (h : E v w p) : SignedPath E v w p := by
  simpa only [Bool.xor_false] using SignedPath.cons h (.nil w)

theorem append {v w z : V} {p q : Bool}
    (h : SignedPath E v w p) (k : SignedPath E w z q) :
    SignedPath E v z (Bool.xor p q) := by
  induction h with
  | nil v => simpa using k
  | cons he ht ih => simpa only [Bool.xor_assoc] using SignedPath.cons he (ih k)

theorem parity_unique {v w : V} {p q : Bool}
    (h : SignedPath E v w p) (k : SignedPath E v w q)
    (hr : Reach E w v) (hodd : ¬ SignedPath E v v true) : p = q := by
  obtain ⟨r, hr⟩ := hr
  have hpr := h.append hr
  have hqr := k.append hr
  cases p <;> cases q <;> cases r <;> simp_all

end SignedPath

namespace Reach

variable {V : Type*} {E : V → V → Bool → Prop} {v w z : V}

theorem refl (v : V) : Reach E v v := ⟨false, .nil v⟩

theorem trans (h : Reach E v w) (k : Reach E w z) : Reach E v z := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq⟩ := k
  exact ⟨_, hp.append hq⟩

theorem single {p : Bool} (h : E v w p) : Reach E v w := ⟨p, .singleton h⟩

end Reach

namespace PositivePath

variable {V : Type*} {E : V → V → Bool → Prop} {v w : V}

theorem parity (h : PositivePath E v w) : SignedPath E v w false := by
  induction h with
  | refl => exact .nil _
  | tail _ he ih => exact ih.append (.singleton he)

theorem reach (h : PositivePath E v w) : Reach E v w := ⟨false, h.parity⟩

end PositivePath

namespace IsComponent

variable {V : Type*} {E : V → V → Bool → Prop} {C : Set V} {v w z : V}

theorem connected (h : IsComponent E C) (hv : v ∈ C) (hw : w ∈ C) : Reach E v w := by
  obtain ⟨r, hr, hc⟩ := h
  exact ((hc v).1 hv).2.trans ((hc w).1 hw).1

theorem between (h : IsComponent E C) (hv : v ∈ C) (hw : w ∈ C)
    (hvz : Reach E v z) (hzw : Reach E z w) : z ∈ C := by
  obtain ⟨r, hr, hc⟩ := h
  exact (hc z).2 ⟨((hc v).1 hv).1.trans hvz, hzw.trans ((hc w).1 hw).2⟩

end IsComponent

/-- Positive closure of the sort-profile seeds. -/
def ObservationLayers {S : Type u} (P : Specification S) (C : Set (Set S)) :
    Set (Set S) := {I | ∃ s, {s} ∈ C ∧ (AxProfile P s).Nonempty ∧
      PositivePath (PrimaryEdge P) (AxProfile P s) I}

inductive SecondaryEdge {S : Type u} (P : Specification S) (C : Set (Set S)) :
    Set S → Set S → Bool → Prop
  | positive {I J} : I ∈ ObservationLayers P C → J ∈ ObservationLayers P C →
      PrimaryEdge P I J false → SecondaryEdge P C I J false
  | negative {I J K} : I ∈ ObservationLayers P C → J ∈ ObservationLayers P C →
      K ∈ ObservationLayers P C → ProfileTriple P I J K →
      SecondaryEdge P C I K true

def DirectLayer {S : Type u} (P : Specification S) (C : Set (Set S))
    (I : Set S) : Prop := I ∈ ObservationLayers P C ∧
      ∃ J ∈ C, ∃ K ∈ C, ProfileTriple P I J K

def ActiveLayer {S : Type u} (P : Specification S) (C : Set (Set S))
    (I : Set S) : Prop := ∃ D, DirectLayer P C D ∧ Reach (SecondaryEdge P C) I D

def PlainLayer {S : Type u} (P : Specification S) (C : Set (Set S))
    (I : Set S) : Prop :=
  (∃ D, DirectLayer P C D ∧ SignedPath (SecondaryEdge P C) I D false) ∧
  (∃ D, DirectLayer P C D ∧ SignedPath (SecondaryEdge P C) I D true)

def FreeLayer {S : Type u} (P : Specification S) (C : Set (Set S))
    (I : Set S) (sign : Bool) : Prop := ¬ PlainLayer P C I ∧
      ∃ D, DirectLayer P C D ∧ SignedPath (SecondaryEdge P C) I D sign

/-- The finite-graph obstruction excluded by system-wide weak normalization.
It is not an extra hypothesis on the normalization theorem. -/

def ForbiddenConfiguration {S : Type u} (P : Specification S) (C : Set (Set S)) : Prop :=
  ∃ D : Set (Set S), IsComponent (SecondaryEdge P C) D ∧
    (∀ I ∈ D, PlainLayer P C I) ∧
    (∃ I ∈ D, ∃ K ∈ D, SecondaryEdge P C I K true) ∧
    ∃ I J K s, ProfileTriple P I J K ∧ J ∈ D ∧ K ∈ D ∧ {s} ∈ D ∧
      (AxProfile P s).Nonempty ∧ PositivePath (PrimaryEdge P) (AxProfile P s) I

namespace PlainLayer

variable {S : Type u} {P : Specification S} {C : Set (Set S)} {I J : Set S}

theorem active (h : PlainLayer P C I) : ActiveLayer P C I := by
  obtain ⟨D, hD, hp⟩ := h.1
  exact ⟨D, hD, false, hp⟩

theorem predecessor {b : Bool} (h : PlainLayer P C J) (e : SecondaryEdge P C I J b) :
    PlainLayer P C I := by
  obtain ⟨⟨D, hD, hp⟩, ⟨D', hD', hp'⟩⟩ := h
  cases b with
  | false => exact ⟨⟨D, hD, .cons e hp⟩, ⟨D', hD', .cons e hp'⟩⟩
  | true => exact ⟨⟨D', hD', .cons e hp'⟩, ⟨D, hD, .cons e hp⟩⟩

end PlainLayer

namespace FreeLayer

variable {S : Type u} {P : Specification S} {C : Set (Set S)} {I J : Set S}

theorem active {s : Bool} (h : FreeLayer P C I s) : ActiveLayer P C I := by
  obtain ⟨D, hD, hp⟩ := h.2
  exact ⟨D, hD, s, hp⟩

theorem sign_unique {s t : Bool} (h : FreeLayer P C I s) (k : FreeLayer P C I t) : s = t := by
  obtain ⟨hn, D, hD, hp⟩ := h
  obtain ⟨_, D', hD', hp'⟩ := k
  cases s <;> cases t
  · rfl
  · exact False.elim (hn ⟨⟨D, hD, hp⟩, ⟨D', hD', hp'⟩⟩)
  · exact False.elim (hn ⟨⟨D', hD', hp'⟩, ⟨D, hD, hp⟩⟩)
  · rfl

theorem edge_sign {s t b : Bool} (h : FreeLayer P C I s) (k : FreeLayer P C J t)
    (e : SecondaryEdge P C I J b) : s = Bool.xor b t := by
  obtain ⟨D, hD, hp⟩ := k.2
  exact h.sign_unique ⟨h.1, D, hD, .cons e hp⟩

theorem direct_sign {s : Bool} (h : FreeLayer P C I s) (hd : DirectLayer P C I) :
    s = false := h.sign_unique ⟨h.1, I, hd, .nil I⟩

end FreeLayer

namespace Expr

variable {S : Type u}

@[simp] theorem normalForm_idem (M : Expr S) : M.normalForm.normalForm = M.normalForm := by
  classical
  by_cases h : WeaklyNormalizing M
  · exact normalForm_of_normal (normalForm_spec h).2
  · simp only [normalForm, dite_eq_right h]

theorem normalForm_rename {M : Expr S} (h : WeaklyNormalizing M) (ρ : Nat → Nat) :
    (M.rename ρ).normalForm = M.normalForm.rename ρ :=
  normalForm_eq ((normalForm_spec h).1.rename ρ) ((normalForm_spec h).2.rename ρ)

end Expr

namespace HasType

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)}

theorem lookup_sorted (hΓ : ValidContext P Γ) {n : Nat} {A : Expr S}
    (hn : Lookup Γ n A) : ∃ s, HasType P Γ A (.sort s) := by
  induction hΓ generalizing n A with
  | nil => cases hn
  | cons hΓ hB ih =>
      cases hn with
      | zero => exact ⟨_, .weaken hB hB⟩
      | succ _ hn =>
          obtain ⟨s, hs⟩ := ih hn
          exact ⟨s, .weaken hs hB⟩

theorem neutral_type_sorted {M A : Expr S} (hn : Neutral M)
    (ht : HasType P Γ M A) : ∃ s, HasType P Γ A (.sort s) := by
  cases hn with
  | var n =>
      obtain ⟨D, hD, hc⟩ := ht.generation
      obtain ⟨s, hs⟩ := lookup_sorted ht.valid hD
      obtain ⟨t, rfl⟩ | hA := ht.regularity
      · obtain ⟨Q, hDQ, hsQ⟩ := (show Converts D (.sort t) from .symm _ _ hc).join
        have heq := (Normal.sort t).reduces_eq hsQ
        subst Q
        exact ⟨s, hs.subject_reduces hDQ⟩
      · exact hA
  | app _ => exact ht.application_type_sorted

end HasType

namespace Profile

variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)}

@[simp] theorem normalForm (T : Expr S) : Profile P Γ T.normalForm = Profile P Γ T := by
  simp only [Profile, Expr.normalForm_idem]

theorem of_normal {T : Expr S} (hn : Normal T) :
    Profile P Γ T = {s | HasType P Γ T (.sort s)} := by
  simp only [Profile, Expr.normalForm_of_normal hn]

theorem sort (hΓ : ValidContext P Γ) (s : S) :
    Profile P Γ (.sort s) = AxProfile P s := by
  rw [of_normal (Normal.sort s)]
  ext t
  constructor
  · intro h
    obtain ⟨u, hu, hc⟩ := h.generation
    have he := hc.sort_inj
    subst u
    exact hu
  · exact HasType.sort_of_valid hΓ

theorem neutral {M : Expr S} {s : S} (hn : Normal M) (hne : Neutral M)
    (ht : HasType P Γ M (.sort s)) : Profile P Γ M = {s} := by
  rw [of_normal hn]
  ext t
  constructor
  · intro h
    exact (ht.neutral_unique hne h).sort_inj.symm
  · intro h
    have he : t = s := h
    subst t
    exact ht

theorem neutral_axiom {M : Expr S} {s : S} (hne : Neutral M)
    (ht : HasType P Γ M (.sort s)) : (AxProfile P s).Nonempty := by
  obtain ⟨t, ht⟩ := ht.neutral_type_sorted hne
  obtain ⟨u, hu, hc⟩ := ht.generation
  exact ⟨u, hu⟩

theorem pi {A B : Expr S} (hnA : Normal A) (hnB : Normal B) :
    Profile P Γ (.pi A B) = OutProfile P (Profile P Γ A) (Profile P (A :: Γ) B) := by
  rw [of_normal (hnA.pi hnB), of_normal hnA, of_normal hnB]
  ext s
  constructor
  · intro ht
    obtain ⟨a, b, c, hA, hB, hr, hc⟩ := ht.generation_pi
    have he := hc.sort_inj
    subst c
    exact ⟨a, hA, b, hB, hr⟩
  · rintro ⟨a, hA, b, hB, hr⟩
    exact .product hA hB hr

theorem converts {A B : Expr S} (hA : WeaklyNormalizing A) (hB : WeaklyNormalizing B)
    (hc : Converts A B) : Profile P Γ A = Profile P Γ B := by
  simp only [Profile, Expr.normalForm_converts hA hB hc]

theorem growth (hw : SystemWeaklyNormalizing P) {T : Expr S}
    (hT : WeaklyNormalizing T) (hΔ : ValidContext P Δ) (σ : Nat → Expr S)
    (hσ : TypedSubstitution P Γ Δ σ) : Profile P Γ T ⊆ Profile P Δ (T.subst σ) := by
  intro s hs
  have ht : HasType P Δ (T.normalForm.subst σ) (.sort s) :=
    hs.subst hΔ σ hσ
  have hr := (Expr.normalForm_spec hT).1.subst σ
  have hrn := (Expr.normalForm_spec (ht.weaklyNormalizing hw)).1
  have hn := (Expr.normalForm_spec (ht.weaklyNormalizing hw)).2
  have heq := Expr.normalForm_eq (hr.trans hrn) hn
  change HasType P Δ (T.subst σ).normalForm (.sort s)
  rw [heq]
  exact ht.normalForm hw

theorem feasible {T : Expr S} (hT : WeaklyNormalizing T)
    (hne : (Profile P Γ T).Nonempty) : FeasibleProfile P (Profile P Γ T) := by
  obtain ⟨s, hs⟩ := hne
  exact ⟨⟨s, hs⟩, Γ, T.normalForm, hs.valid, (Expr.normalForm_spec hT).2, normalForm T⟩

end Profile

/-! Finite component order for the exact signed graphs of the manuscript. -/
namespace Reach
variable {V : Type u} (E : V → V → Bool → Prop)

def component (v : V) : Set V := {w | Reach E v w ∧ Reach E w v}

theorem mem_component (v : V) : v ∈ component E v := ⟨.refl v, .refl v⟩

theorem component_isComponent (v : V) : IsComponent E (component E v) :=
  ⟨v, mem_component E v, fun _ => Iff.rfl⟩

theorem component_eq {v w : V} (h : Reach E v w) (k : Reach E w v) :
    component E v = component E w := by
  ext z
  exact ⟨fun hz => ⟨k.trans hz.1, hz.2.trans h⟩,
    fun hz => ⟨h.trans hz.1, hz.2.trans k⟩⟩

variable [Fintype V]
open Classical

noncomputable def predecessors (v : V) : Finset V := Finset.univ.filter fun w => Reach E w v
noncomputable def rank (v : V) : Nat := (predecessors E v).card

@[simp] theorem mem_predecessors {v w : V} : w ∈ predecessors E v ↔ Reach E w v := by
  simp [predecessors]

theorem rank_mono {v w : V} (h : Reach E v w) : rank E v ≤ rank E w := by
  apply Finset.card_le_card
  intro z hz
  exact (mem_predecessors E).mpr (((mem_predecessors E).mp hz).trans h)

theorem reverse_of_rank_eq {v w : V} (h : Reach E v w) (he : rank E v = rank E w) :
    Reach E w v := by
  have hs : predecessors E v ⊆ predecessors E w := by
    intro z hz
    exact (mem_predecessors E).mpr (((mem_predecessors E).mp hz).trans h)
  have he' := Finset.eq_of_subset_of_card_le hs (le_of_eq he.symm)
  apply (mem_predecessors E).mp
  rw [he']
  exact (mem_predecessors E).mpr (.refl _)

theorem component_eq_of_rank_eq {v w : V} (h : Reach E v w)
    (he : rank E v = rank E w) : component E v = component E w :=
  component_eq E h (reverse_of_rank_eq E h he)

end Reach

namespace PlainLayer
variable {S : Type u} {P : Specification S} {C : Set (Set S)} {I J : Set S}

theorem predecessor_path (h : PlainLayer P C J) (hp : Reach (SecondaryEdge P C) I J) :
    PlainLayer P C I := by
  obtain ⟨b, hp⟩ := hp
  induction hp with
  | nil => exact h
  | cons he _ ih => exact (ih h).predecessor he

theorem component_plain (h : PlainLayer P C I) :
    ∀ J ∈ Reach.component (SecondaryEdge P C) I, PlainLayer P C J := by
  intro J hJ
  exact h.predecessor_path hJ.2
end PlainLayer

namespace IsComponent
variable {V : Type u} {E : V → V → Bool → Prop} {C : Set V}
open Classical

noncomputable def signing (hc : IsComponent E C) (v : V) : Bool :=
  if h : v ∈ C then (hc.connected hc.choose_spec.1 h).choose else false

theorem signing_path (hc : IsComponent E C) {v : V} (hv : v ∈ C) :
    SignedPath E hc.choose v (hc.signing v) := by
  unfold signing
  rw [dite_eq_left hv]
  exact (hc.connected hc.choose_spec.1 hv).choose_spec

theorem signing_cross (hc : IsComponent E C)
    (hn : ∀ v ∈ C, ¬ SignedPath E v v true)
    {v w : V} {p : Bool} (hv : v ∈ C) (hw : w ∈ C) (hp : SignedPath E v w p) :
    hc.signing w = Bool.xor (hc.signing v) p := by
  exact (hc.signing_path hw).parity_unique ((hc.signing_path hv).append hp)
    (hc.connected hw hc.choose_spec.1) (hn _ hc.choose_spec.1)
end IsComponent
end PureTypeSystem

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Potential
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Profile paths and the no-expanding-neutral-leaf dependency. -/

namespace PureTypeSystem
universe u
namespace Profile
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)}

theorem nonempty_of_sorted (hw : SystemWeaklyNormalizing P) {M : Expr S} {s : S}
    (h : HasType P Γ M (.sort s)) : (Profile P Γ M).Nonempty :=
  ⟨s, h.normalForm hw⟩

theorem context_head_conversion {A A' M : Expr S} {s t : S}
    (hA : HasType P Γ A (.sort s)) (hA' : HasType P Γ A' (.sort t))
    (hc : Converts A A') : Profile P (A :: Γ) M = Profile P (A' :: Γ) M := by
  ext r
  exact ⟨fun h => HasType.context_head_conversion h hA hA' hc,
    fun h => HasType.context_head_conversion h hA' hA (.symm _ _ hc)⟩

theorem inclusion_path {I J : Set S} (hI : FeasibleProfile P I)
    (hJ : FeasibleProfile P J) (h : J ⊆ I) : PositivePath (PrimaryEdge P) I J := by
  classical
  by_cases he : I = J
  · subst J; exact .refl
  · exact .single (.inclusion hI hJ (Set.ssubset_iff_subset_ne.mpr ⟨h, Ne.symm he⟩))

theorem triple (hw : SystemWeaklyNormalizing P) {D E : Expr S} {s : S}
    (h : HasType P Γ (.pi D E) (.sort s)) :
    ProfileTriple P (Profile P Γ D) (Profile P (D :: Γ) E) (Profile P Γ (.pi D E)) := by
  obtain ⟨a, b, c, hD, hE, _, _⟩ := h.generation_pi
  have wD := hD.weaklyNormalizing hw
  have wE := hE.weaklyNormalizing hw
  have hD' := hD.normalForm hw
  have he : Profile P (D.normalForm :: Γ) E = Profile P (D :: Γ) E :=
    (context_head_conversion hD hD' (Expr.normalForm_spec wD).1.converts).symm
  refine ⟨feasible wD (nonempty_of_sorted hw hD),
    feasible wE (nonempty_of_sorted hw hE),
    feasible (h.weaklyNormalizing hw) (nonempty_of_sorted hw h), ?_⟩
  calc
    Profile P Γ (.pi D E) = Profile P Γ (.pi D.normalForm E.normalForm) := by
      rw [← Expr.normalForm_pi wD wE, Profile.normalForm]
    _ = OutProfile P (Profile P Γ D.normalForm)
        (Profile P (D.normalForm :: Γ) E.normalForm) :=
      pi (Expr.normalForm_spec wD).2 (Expr.normalForm_spec wE).2
    _ = OutProfile P (Profile P Γ D) (Profile P (D :: Γ) E) := by
      rw [Profile.normalForm, Profile.normalForm, he]

/-- The exact positive ascent from an instantiated codomain to its product.
It uses all sortings rather than choosing a functional specification. -/
theorem instantiate_product_path (hw : SystemWeaklyNormalizing P)
    {D E n : Expr S} {s : S} (h : HasType P Γ (.pi D E) (.sort s))
    (hn : HasType P Γ n D) :
    PositivePath (PrimaryEdge P) (Profile P Γ (E.instantiate n))
      (Profile P Γ (.pi D E)) := by
  obtain ⟨a, b, c, hD, hE, _, _⟩ := h.generation_pi
  have hout := hE.instantiate hn
  have hg := growth hw (hE.weaklyNormalizing hw) hn.valid _ (TypedSubstitution.single hn)
  have hp := inclusion_path
    (feasible (hout.weaklyNormalizing hw) (nonempty_of_sorted hw hout))
    (feasible (hE.weaklyNormalizing hw) (nonempty_of_sorted hw hE)) hg
  exact hp.trans (.single (.codomain (triple hw h)))
end Profile

namespace Expr
variable {S : Type u}
def head : Expr S → Expr S
  | .app f _ => head f
  | M => M
@[simp] theorem head_apps (M : Expr S) (ns : List (Expr S)) : (M.apps ns).head = M.head := by
  induction ns generalizing M with
  | nil => rfl
  | cons n ns ih => exact ih (.app M n)
end Expr

namespace HasType
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)}

/-- Reading a neutral spine backwards gives a positive path from the exact
result-type profile to the declaration-type profile of its head. -/
theorem neutral_profile_ascent (hw : SystemWeaklyNormalizing P)
    {M T : Expr S} (hn : Neutral M) (h : HasType P Γ M T) :
    ∃ n D, M.head = .var n ∧ Lookup Γ n D ∧
      PositivePath (PrimaryEdge P) (Profile P Γ T) (Profile P Γ D) := by
  induction hn generalizing T with
  | var n =>
      obtain ⟨D, hD, hc⟩ := h.generation
      refine ⟨n, D, rfl, hD, ?_⟩
      rw [Profile.converts (h.type_weaklyNormalizing hw)
        ((HasType.lookup h.valid hD).type_weaklyNormalizing hw) hc]
      exact .refl
  | @app f a hnf ih =>
      obtain ⟨D, E, hf, ha, hc⟩ := h.generation_app
      obtain ⟨s, hp⟩ := hf.product_type_sorted
      obtain ⟨n, A, hh, hl, hr⟩ := ih hf
      refine ⟨n, A, hh, hl, ?_⟩
      rw [Profile.converts (h.type_weaklyNormalizing hw)
        ((HasType.application hf ha).type_weaklyNormalizing hw) hc]
      exact (Profile.instantiate_product_path hw hp ha).trans hr

/-- This is the precise seed generated when a normal neutral type can be
changed at its head by substitution. The sort axiom is derived, not assumed. -/
theorem neutral_profile_seed (hw : SystemWeaklyNormalizing P)
    {M : Expr S} {s : S} (hn : Neutral M) (hM : Normal M)
    (h : HasType P Γ M (.sort s)) :
    Profile P Γ M = {s} ∧ (AxProfile P s).Nonempty ∧
      ∃ n D, M.head = .var n ∧ Lookup Γ n D ∧
        PositivePath (PrimaryEdge P) (AxProfile P s) (Profile P Γ D) := by
  refine ⟨Profile.neutral hM hn h, Profile.neutral_axiom hn h, ?_⟩
  simpa only [Profile.sort h.valid] using neutral_profile_ascent hw hn h
end HasType

namespace Neutral
variable {S : Type u} {M N : Expr S}

theorem rename (h : Neutral M) (ρ : Nat → Nat) : Neutral (M.rename ρ) := by
  induction h with
  | var n => exact .var _
  | app h ih => exact .app ih

theorem subst_of_head (h : Neutral M) (σ : Nat → Expr S)
    (hh : ∀ n, M.head = .var n → Neutral (σ n)) : Neutral (M.subst σ) := by
  induction h with
  | var n => exact hh n rfl
  | app h ih => exact .app (ih hh)

theorem beta (h : Neutral M) (hr : Beta M N) : Neutral N := by
  induction h generalizing N with
  | var n => cases hr
  | @app f a h ih =>
      cases hr with
      | app_left hr => exact .app (ih hr)
      | app_right _ => exact .app h
      | head => cases h

theorem reduces (h : Neutral M) (hr : Reduces M N) : Neutral N := by
  induction hr with
  | refl => exact h
  | tail _ hr ih => exact ih.beta hr

theorem normalForm (h : Neutral M) (hw : WeaklyNormalizing M) : Neutral M.normalForm :=
  h.reduces (Expr.normalForm_spec hw).1
end Neutral

/- A typed renaming preserves exact profiles of sorted types. The reverse
inclusion uses neutral uniqueness; it does not falsely assume functionality. -/
namespace Profile
variable {S : Type u} {P : Specification S}

theorem rename_normal {Γ Δ : List (Expr S)} {T : Expr S} {s : S}
    (hT : HasType P Γ T (.sort s)) (hn : Normal T)
    (hΔ : ValidContext P Δ) (ρ : Nat → Nat)
    (hρ : ∀ n B, Lookup Γ n B → HasType P Δ (.var (ρ n)) (B.rename ρ)) :
    Profile P Δ (T.rename ρ) = Profile P Γ T := by
  induction T generalizing Γ Δ s ρ with
  | var n =>
      rw [neutral (hn.rename ρ) (.var _) (hT.rename hΔ ρ hρ), neutral hn (.var _) hT]
  | sort t =>
      exact (sort hΔ t).trans (sort hT.valid t).symm
  | app f a ihf iha =>
      have hneutral : Neutral (.app f a) := by
        obtain ⟨t, he⟩ | h | ⟨D, E, he⟩ := hT.sorted_normal_shape hn
        · cases he
        · exact h
        · cases he
      rw [neutral (hn.rename ρ) (hneutral.rename ρ) (hT.rename hΔ ρ hρ),
        neutral hn hneutral hT]
  | lam A b ihA ihb => exact False.elim hT.lambda_cannot_have_sort_type
  | pi A B ihA ihB =>
      obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
      have hA' := hA.rename hΔ ρ hρ
      have hr : ∀ n D, Lookup (A :: Γ) n D →
          HasType P (A.rename ρ :: Δ) (.var (Expr.liftRen ρ n))
            (D.rename (Expr.liftRen ρ)) := by
        intro n D hD
        cases hD with
        | zero =>
            simpa only [Expr.liftRen, Expr.rename_comp, Function.comp_def] using HasType.var hA'
        | succ _ hD =>
            simpa only [Expr.liftRen, Expr.rename_comp, Function.comp_def, Expr.rename] using
              HasType.weaken (hρ _ _ hD) hA'
      rw [Expr.rename, pi (hn.pi_domain.rename ρ) (hn.pi_body.rename _), pi hn.pi_domain hn.pi_body,
        ihA hA hn.pi_domain hΔ ρ hρ,
        ihB hB hn.pi_body (.cons hΔ hA') _ hr]

theorem rename (hw : SystemWeaklyNormalizing P)
    {Γ Δ : List (Expr S)} {T : Expr S} {s : S}
    (hT : HasType P Γ T (.sort s)) (hΔ : ValidContext P Δ) (ρ : Nat → Nat)
    (hρ : ∀ n B, Lookup Γ n B → HasType P Δ (.var (ρ n)) (B.rename ρ)) :
    Profile P Δ (T.rename ρ) = Profile P Γ T := by
  rw [← normalForm T, ← normalForm (T.rename ρ), Expr.normalForm_rename (hT.weaklyNormalizing hw) ρ]
  exact rename_normal (hT.normalForm hw) (Expr.normalForm_spec (hT.weaklyNormalizing hw)).2 hΔ ρ hρ

theorem weaken (hw : SystemWeaklyNormalizing P) {Γ : List (Expr S)}
    {T D : Expr S} {s t : S} (hT : HasType P Γ T (.sort s))
    (hD : HasType P Γ D (.sort t)) :
    Profile P (D :: Γ) (T.rename Nat.succ) = Profile P Γ T :=
  rename hw hT (.cons hD.valid hD) Nat.succ
    (fun _ _ hn => .weaken (HasType.lookup hD.valid hn) hD)
end Profile

/-- Every image which can replace a neutral head originates at the chosen
outer binder profile. Ordinary one-variable substitution, and every lifting
of it through additional binders, have this property. -/
def SingleSource {S : Type u} (P : Specification S) (Γ : List (Expr S))
    (σ : Nat → Expr S) (I : Set S) : Prop :=
  ∀ n D, Lookup Γ n D → ¬ Neutral (σ n) → Profile P Γ D = I

namespace SingleSource
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)}
    {σ : Nat → Expr S} {I : Set S}

theorem single (hw : SystemWeaklyNormalizing P) {D q : Expr S} {s : S}
    (hD : HasType P Γ D (.sort s)) :
    SingleSource P (D :: Γ) (Expr.single q) (Profile P Γ D) := by
  intro n A hn hbad
  cases hn with
  | zero => exact Profile.weaken hw hD hD
  | succ _ _ => exact False.elim (hbad (.var _))

theorem lift (hw : SystemWeaklyNormalizing P) (h : SingleSource P Γ σ I)
    {D : Expr S} {s : S} (hD : HasType P Γ D (.sort s)) :
    SingleSource P (D :: Γ) (Expr.liftSub σ) I := by
  intro n A hn hbad
  cases hn with
  | zero => exact False.elim (hbad (.var 0))
  | succ _ hn =>
      obtain ⟨t, hA⟩ := HasType.lookup_sorted hD.valid hn
      rw [Profile.weaken hw hA hD]
      exact h _ _ hn (fun hh => hbad (hh.rename Nat.succ))
end SingleSource

namespace ForbiddenConfiguration
variable {S : Type u} {P : Specification S} {C D : Set (Set S)}

/-- The source's critical neutral-leaf argument. No beta-normal neutral leaf
in this component can become a product under substitution of the outer
binder: doing so would produce exactly the excluded graph configuration. -/
theorem of_neutral_expansion (hw : SystemWeaklyNormalizing P)
    (hD : IsComponent (SecondaryEdge P C) D) (hplain : ∀ I ∈ D, PlainLayer P C I)
    (hneg : ∃ I ∈ D, ∃ K ∈ D, SecondaryEdge P C I K true)
    {I J K : Set S} (htr : ProfileTriple P I J K) (hJ : J ∈ D) (hK : K ∈ D)
    {Γ Δ : List (Expr S)} (hΔ : ValidContext P Δ) {σ : Nat → Expr S}
    (hσ : TypedSubstitution P Γ Δ σ) (hsrc : SingleSource P Γ σ I)
    {M A B : Expr S} {s : S} (h : HasType P Γ M (.sort s))
    (hn : Normal M) (hne : Neutral M) (hM : Profile P Γ M ∈ D)
    (he : (M.subst σ).normalForm = .pi A B) : ForbiddenConfiguration P C := by
  obtain ⟨hp, hax, n, F, hh, hf, hpath⟩ := h.neutral_profile_seed hw hne hn
  have hbad : ¬ Neutral (σ n) := by
    intro hs
    have hM' := hne.subst_of_head σ (by
      intro m hm
      have heq : m = n := by simpa only [hh, Expr.var.injEq] using hm.symm
      exact heq.symm ▸ hs)
    have hnorm := hM'.normalForm ((h.subst hΔ σ hσ).weaklyNormalizing hw)
    rw [he] at hnorm
    cases hnorm
  have hF := hsrc n F hf hbad
  rw [hF] at hpath
  exact ⟨D, hD, hplain, hneg, I, J, K, s, htr, hJ, hK, hp ▸ hM, hax, hpath⟩
end ForbiddenConfiguration

namespace ObservationLayers
variable {S : Type u} {P : Specification S} {C : Set (Set S)} {I J : Set S}
theorem positive (h : I ∈ ObservationLayers P C) (hp : PositivePath (PrimaryEdge P) I J) :
    J ∈ ObservationLayers P C := by
  obtain ⟨s, hs, hax, hpath⟩ := h
  exact ⟨s, hs, hax, hpath.trans hp⟩

theorem secondary (h : I ∈ ObservationLayers P C) (hp : PositivePath (PrimaryEdge P) I J) :
    PositivePath (SecondaryEdge P C) I J := by
  induction hp with
  | refl => exact .refl
  | @tail J K hp he ih =>
      exact .tail ih (.positive (positive h hp) (positive h (.tail hp he)) he)
end ObservationLayers

namespace ActiveLayer
variable {S : Type u} {P : Specification S} {C : Set (Set S)} {I J : Set S}

theorem layer (h : ActiveLayer P C I) : I ∈ ObservationLayers P C := by
  obtain ⟨D, hD, b, hp⟩ := h
  cases hp with
  | nil => exact hD.1
  | cons he _ => cases he with
    | positive hI _ _ => exact hI
    | negative hI _ _ _ => exact hI

theorem predecessor (h : ActiveLayer P C J) (hp : Reach (SecondaryEdge P C) I J) :
    ActiveLayer P C I := by
  obtain ⟨D, hD, hr⟩ := h
  exact ⟨D, hD, hp.trans hr⟩
end ActiveLayer

namespace IsComponent
variable {S : Type u} {P : Specification S} {C D : Set (Set S)}

/-- Interpolation of a counted post-substitution codomain through the
original product triple. -/
theorem codomain_interpolation (hD : IsComponent (SecondaryEdge P C) D)
    (hl : ∀ X ∈ D, X ∈ ObservationLayers P C)
    {I J K J' : Set S} (htr : ProfileTriple P I J K) (hK : K ∈ D) (hJ' : J' ∈ D)
    (hJJ' : PositivePath (PrimaryEdge P) J' J) : J ∈ D := by
  have hJH := ObservationLayers.positive (hl J' hJ') hJJ'
  exact hD.between hJ' hK (ObservationLayers.secondary (hl J' hJ') hJJ').reach
    (Reach.single (.positive hJH (hl K hK) (.codomain htr)))

/-- Domain interpolation also needs the post open codomain to be active;
this is exactly the side condition in the source potential, not a stronger
assumption that every domain dependency is retained. -/
theorem domain_interpolation (hD : IsComponent (SecondaryEdge P C) D)
    (hl : ∀ X ∈ D, X ∈ ObservationLayers P C)
    (ha : ∀ X ∈ D, ActiveLayer P C X)
    {I J K I' J' : Set S} (htr : ProfileTriple P I J K) (hK : K ∈ D)
    (hI' : I' ∈ D) (hJ' : ActiveLayer P C J')
    (hII' : PositivePath (PrimaryEdge P) I' I)
    (hJJ' : PositivePath (PrimaryEdge P) J' J) :
    I ∈ D ∧ ActiveLayer P C J := by
  have hIH := ObservationLayers.positive (hl I' hI') hII'
  have hJH := ObservationLayers.positive hJ'.layer hJJ'
  have hKH := hl K hK
  exact ⟨hD.between hI' hK (ObservationLayers.secondary (hl I' hI') hII').reach
    (Reach.single (.negative hIH hJH hKH htr)),
    (ha K hK).predecessor (Reach.single (.positive hJH hKH (.codomain htr)))⟩
end IsComponent

namespace Profile
variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)}
theorem growth_path (hw : SystemWeaklyNormalizing P) {T : Expr S} {s : S}
    (hT : HasType P Γ T (.sort s)) (hΔ : ValidContext P Δ) (σ : Nat → Expr S)
    (hσ : TypedSubstitution P Γ Δ σ) :
    PositivePath (PrimaryEdge P) (Profile P Δ (T.subst σ)) (Profile P Γ T) := by
  have ht := hT.subst hΔ σ hσ
  exact inclusion_path (feasible (ht.weaklyNormalizing hw) (nonempty_of_sorted hw ht))
    (feasible (hT.weaklyNormalizing hw) (nonempty_of_sorted hw hT))
    (growth hw (hT.weaklyNormalizing hw) hΔ σ hσ)
end Profile

/-- Context conversion as exact equality of all judgments on unchanged
syntax. Both contexts are required valid. This auxiliary relation carries
no semantic or normalization assumption. -/
structure ContextEquivalent {S : Type u} (P : Specification S)
    (Γ Δ : List (Expr S)) : Prop where
  valid_left : ValidContext P Γ
  valid_right : ValidContext P Δ
  typing : ∀ (M A : Expr S), HasType P Γ M A ↔ HasType P Δ M A

namespace ContextEquivalent
variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)}
theorem symm (h : ContextEquivalent P Γ Δ) : ContextEquivalent P Δ Γ :=
  ⟨h.valid_right, h.valid_left, fun _ _ => (h.typing _ _).symm⟩

theorem profile (h : ContextEquivalent P Γ Δ) (M : Expr S) :
    Profile P Γ M = Profile P Δ M := by
  ext s
  exact h.typing _ _

theorem cons (h : ContextEquivalent P Γ Δ) {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) : ContextEquivalent P (A :: Γ) (A :: Δ) := by
  have lift_dir {Γ Δ : List (Expr S)} (h : ContextEquivalent P Γ Δ)
      (hA : HasType P Γ A (.sort s)) :
      ∀ M B, HasType P (A :: Γ) M B → HasType P (A :: Δ) M B := by
    intro M B ht
    have hA' := (h.typing _ _).1 hA
    have hs : TypedSubstitution P (A :: Γ) (A :: Δ) Expr.var := by
      intro n D hn
      rw [Expr.subst_var]
      cases hn with
      | zero => exact .var hA'
      | succ _ hn => exact .weaken ((h.typing _ _).1 (HasType.lookup h.valid_left hn)) hA'
    simpa only [Expr.subst_var] using ht.subst (.cons h.valid_right hA') _ hs
  have hA' := (h.typing _ _).1 hA
  exact ⟨.cons h.valid_left hA, .cons h.valid_right hA',
    fun M B => ⟨lift_dir h hA M B, lift_dir h.symm hA' M B⟩⟩

theorem head_conversion {A B : Expr S} {s t : S}
    (hA : HasType P Γ A (.sort s)) (hB : HasType P Γ B (.sort t))
    (hc : Converts A B) : ContextEquivalent P (A :: Γ) (B :: Γ) :=
  ⟨.cons hA.valid hA, .cons hB.valid hB, fun _ _ =>
    ⟨fun h => h.context_head_conversion hA hB hc,
      fun h => h.context_head_conversion hB hA (.symm _ _ hc)⟩⟩
end ContextEquivalent

namespace PlainObservations
open Classical
variable {S : Type u}
/-- The exact source syntax-tree potential. Its recursive child conditions
retain the active-open-codomain guard on a counted domain. -/
noncomputable def potential (P : Specification S) (C D : Set (Set S))
    (Γ : List (Expr S)) : Expr S → Nat
  | .pi A B => by
      classical
      exact 1 +
      (if Profile P Γ A ∈ D ∧ ActiveLayer P C (Profile P (A :: Γ) B)
       then potential P C D Γ A else 0) +
      (if Profile P (A :: Γ) B ∈ D then potential P C D (A :: Γ) B else 0)
  | _ => 1

variable {P : Specification S} {C D : Set (Set S)}

theorem potential_context {Γ Δ : List (Expr S)} {T : Expr S} {s : S}
    (hT : HasType P Γ T (.sort s)) (h : ContextEquivalent P Γ Δ) :
    potential P C D Γ T = potential P C D Δ T := by
  induction T generalizing Γ Δ s with
  | var n | sort t | app f a | lam A b => rfl
  | pi A B ihA ihB =>
      obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
      simp only [potential]
      rw [h.profile A, (h.cons hA).profile B, ihA hA h, ihB hB (h.cons hA)]

/-- Normalizing a product does not change the contexts in which its child
contributions are measured: raw and normalized annotations are context
convertible. This keeps the dependent codomain count honest. -/
theorem potential_normalized_pi (hw : SystemWeaklyNormalizing P)
    {Γ : List (Expr S)} {A B : Expr S} {s : S}
    (h : HasType P Γ (.pi A B) (.sort s)) :
    potential P C D Γ (Expr.pi A B).normalForm = 1 +
      (if Profile P Γ A ∈ D ∧ ActiveLayer P C (Profile P (A :: Γ) B)
       then potential P C D Γ A.normalForm else 0) +
      (if Profile P (A :: Γ) B ∈ D then potential P C D (A :: Γ) B.normalForm else 0) := by
  classical
  obtain ⟨a, b, c, hA, hB, _, _⟩ := h.generation_pi
  have wA := hA.weaklyNormalizing hw
  have wB := hB.weaklyNormalizing hw
  have hc := ContextEquivalent.head_conversion hA (hA.normalForm hw) (Expr.normalForm_spec wA).1.converts
  have hp := (potential_context (C := C) (D := D) (hB.normalForm hw) hc).symm
  rw [Expr.normalForm_pi wA wB, potential, ← hc.profile B.normalForm, hp,
    Profile.normalForm, Profile.normalForm]

/-- The full potential inequality. The outer triple and its codomain/product
vertices are fixed exactly as in the source legal-frame argument. SingleSource
is proved above for the actual one-variable substitution and all binder lifts. -/
theorem potential_subst_le (hw : SystemWeaklyNormalizing P)
    (hno : ¬ ForbiddenConfiguration P C)
    (hD : IsComponent (SecondaryEdge P C) D) (hplain : ∀ I ∈ D, PlainLayer P C I)
    (hneg : ∃ I ∈ D, ∃ K ∈ D, SecondaryEdge P C I K true)
    {I J K : Set S} (htr : ProfileTriple P I J K) (hJ : J ∈ D) (hK : K ∈ D)
    {Γ Δ : List (Expr S)} (hΔ : ValidContext P Δ) {σ : Nat → Expr S}
    (hσ : TypedSubstitution P Γ Δ σ) (hsrc : SingleSource P Γ σ I)
    {T : Expr S} {s : S} (hT : HasType P Γ T (.sort s)) (hn : Normal T)
    (hTC : Profile P Γ T ∈ D) :
    potential P C D Δ (T.subst σ).normalForm ≤ potential P C D Γ T := by
  classical
  have ha : ∀ X ∈ D, ActiveLayer P C X := fun X hX => (hplain X hX).active
  have hl : ∀ X ∈ D, X ∈ ObservationLayers P C := fun X hX => (ha X hX).layer
  have leaf {Γ Δ : List (Expr S)} {σ : Nat → Expr S} {M : Expr S} {s : S}
      (hΔ : ValidContext P Δ) (hσ : TypedSubstitution P Γ Δ σ)
      (hsrc : SingleSource P Γ σ I) (hM : HasType P Γ M (.sort s))
      (hn : Normal M) (hne : Neutral M) (hMC : Profile P Γ M ∈ D) :
      potential P C D Δ (M.subst σ).normalForm = 1 := by
    cases he : (M.subst σ).normalForm with
    | pi A B =>
        exact False.elim (hno (ForbiddenConfiguration.of_neutral_expansion hw hD hplain hneg
          htr hJ hK hΔ hσ hsrc hM hn hne hMC he))
    | var n | sort t | app f a | lam A b => rfl
  induction T generalizing Γ Δ σ s with
  | var n => exact le_of_eq (leaf hΔ hσ hsrc hT hn (.var n) hTC)
  | sort t => simp only [Expr.subst, Expr.normalForm_of_normal (Normal.sort t), potential, le_refl]
  | lam A b => exact False.elim hT.lambda_cannot_have_sort_type
  | app f a ihf iha =>
      have hneutral : Neutral (.app f a) := by
        obtain ⟨t, he⟩ | h | ⟨A, B, he⟩ := hT.sorted_normal_shape hn
        · cases he
        · exact h
        · cases he
      exact le_of_eq (leaf hΔ hσ hsrc hT hn hneutral hTC)
  | pi A B ihA ihB =>
      obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
      have hA' := hA.subst hΔ σ hσ
      have hΔ' : ValidContext P (A.subst σ :: Δ) := .cons hΔ hA'
      have hσ' := hσ.lift hA'
      have hB' := hB.subst hΔ' _ hσ'
      have htr' := Profile.triple hw hT
      have hAp := Profile.growth_path hw hA hΔ σ hσ
      have hBp := Profile.growth_path hw hB hΔ' _ hσ'
      rw [Expr.subst, potential_normalized_pi hw (hT.subst hΔ σ hσ), potential]
      apply Nat.add_le_add
      · apply Nat.add_le_add_left
        split_ifs with hc hc'
        · exact ihA hΔ hσ hsrc hA hn.pi_domain hc'.1
        · obtain ⟨hAC, hBa⟩ := hD.domain_interpolation hl ha htr' hTC hc.1 hc.2 hAp hBp
          exact False.elim (hc' ⟨hAC, hBa⟩)
        · exact Nat.zero_le _
        · exact le_rfl
      · split_ifs with hc hc'
        · exact ihB hΔ' hσ' (hsrc.lift hw hA) hB hn.pi_body hc'
        · exact False.elim (hc' (hD.codomain_interpolation hl htr' hTC hc hBp))
        · exact Nat.zero_le _
        · exact le_rfl

/-- Exact legal-frame potential drop in the negative plain component,
including the strict syntactic-child inequality. -/
theorem frame_potential_drop (hw : SystemWeaklyNormalizing P)
    (hno : ¬ ForbiddenConfiguration P C)
    (hD : IsComponent (SecondaryEdge P C) D) (hplain : ∀ I ∈ D, PlainLayer P C I)
    (hneg : ∃ I ∈ D, ∃ K ∈ D, SecondaryEdge P C I K true)
    {Γ : List (Expr S)} {A B n : Expr S} {s : S}
    (hT : HasType P Γ (.pi A B) (.sort s)) (hnT : Normal (.pi A B))
    (hn : HasType P Γ n A) (hK : Profile P Γ (.pi A B) ∈ D)
    (hL : Profile P Γ (B.instantiate n) ∈ D) :
    potential P C D Γ (B.instantiate n).normalForm ≤ potential P C D (A :: Γ) B ∧
      potential P C D (A :: Γ) B < potential P C D Γ (.pi A B) := by
  have ha : ∀ X ∈ D, ActiveLayer P C X := fun X hX => (hplain X hX).active
  have hl : ∀ X ∈ D, X ∈ ObservationLayers P C := fun X hX => (ha X hX).layer
  obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
  have htr := Profile.triple hw hT
  have hp := Profile.growth_path hw hB hn.valid _ (TypedSubstitution.single hn)
  have hJ := hD.codomain_interpolation hl htr hK hL hp
  refine ⟨potential_subst_le hw hno hD hplain hneg htr hJ hK hn.valid
    (TypedSubstitution.single hn) (SingleSource.single hw hA) hB hnT.pi_body hJ, ?_⟩
  simp only [potential, ite_eq_left hJ]
  omega

/-- The potential counts positions, so valid thinning does not change it.
The equality is exact also under every dependent binder. -/
theorem potential_rename (hw : SystemWeaklyNormalizing P)
    {Γ Δ : List (Expr S)} {T : Expr S} {s : S}
    (hT : HasType P Γ T (.sort s)) (hΔ : ValidContext P Δ) (ρ : Nat → Nat)
    (hρ : ∀ n B, Lookup Γ n B → HasType P Δ (.var (ρ n)) (B.rename ρ)) :
    potential P C D Δ (T.rename ρ) = potential P C D Γ T := by
  induction T generalizing Γ Δ s ρ with
  | var n | sort t | app f a | lam A b => rfl
  | pi A B ihA ihB =>
      obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
      have hA' := hA.rename hΔ ρ hρ
      have hr : ∀ n E, Lookup (A :: Γ) n E →
          HasType P (A.rename ρ :: Δ) (.var (Expr.liftRen ρ n))
            (E.rename (Expr.liftRen ρ)) := by
        intro n E hE
        cases hE with
        | zero =>
            simpa only [Expr.liftRen, Expr.rename_comp, Function.comp_def] using HasType.var hA'
        | succ _ hE =>
            simpa only [Expr.liftRen, Expr.rename_comp, Function.comp_def, Expr.rename] using
              HasType.weaken (hρ _ _ hE) hA'
      simp only [Expr.rename, potential]
      rw [Profile.rename hw hA hΔ ρ hρ,
        Profile.rename hw hB (.cons hΔ hA') _ hr,
        ihA hA hΔ ρ hρ, ihB hB (.cons hΔ hA') _ hr]

end PlainObservations

namespace ContextTower

section
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)

/-- The source profile on syntax with fixed global variable names. -/
def profile (T : Expr S) : Set S := {s | Ω.HasType T.normalForm (.sort s)}

variable (hw : SystemWeaklyNormalizing P)
include hw

theorem profile_at_next {n : Nat} {T : Expr S} {s : S}
    (ht : PureTypeSystem.HasType P (Ω.context n) (T.rename (Expr.reverseIndex n)) (.sort s)) :
    Profile P (Ω.context (n+1)) (T.rename (Expr.reverseIndex (n+1))) =
      Profile P (Ω.context n) (T.rename (Expr.reverseIndex n)) := by
  have hs : T.Scoped n := by
    have h := ht.scope.1.reverseIndex
    rwa [Ω.length, Expr.reverseIndex_twice] at h
  obtain ⟨D, t, hD, he⟩ := Ω.step n
  rw [he, hs.reverseIndex_succ]
  exact Profile.weaken hw ht hD

theorem profile_at_mono {n m : Nat} {T : Expr S} {s : S}
    (ht : PureTypeSystem.HasType P (Ω.context n) (T.rename (Expr.reverseIndex n)) (.sort s))
    (h : n ≤ m) :
    Profile P (Ω.context m) (T.rename (Expr.reverseIndex m)) =
      Profile P (Ω.context n) (T.rename (Expr.reverseIndex n)) := by
  induction h with
  | refl => rfl
  | @step m h ih => exact (Ω.profile_at_next hw (Ω.at_mono (A := .sort s) ht h)).trans ih

/-- A single available sorting fixes the exact profile at every later
prefix. Extra sorting rules cannot appear merely by weakening. -/
theorem profile_at {n : Nat} {T : Expr S} {s : S}
    (ht : PureTypeSystem.HasType P (Ω.context n) (T.rename (Expr.reverseIndex n)) (.sort s)) :
    Ω.profile T = Profile P (Ω.context n) (T.rename (Expr.reverseIndex n)) := by
  have w : WeaklyNormalizing T := (show Ω.HasType T (.sort s) from ⟨n, ht⟩).weaklyNormalizing hw
  ext t
  constructor
  · rintro ⟨m, hm⟩
    have hn := Ω.at_mono (A := .sort t) hm (le_max_left m n)
    change PureTypeSystem.HasType P (Ω.context (max m n))
      (T.normalForm.rename (Expr.reverseIndex (max m n))) (.sort t) at hn
    rw [← Expr.normalForm_rename w] at hn
    have he := Ω.profile_at_mono hw ht (le_max_right m n)
    exact he ▸ hn
  · intro hn
    refine ⟨n, ?_⟩
    change PureTypeSystem.HasType P (Ω.context n) (T.normalForm.rename (Expr.reverseIndex n)) (.sort t)
    rw [← Expr.normalForm_rename w]
    exact hn

omit hw in
theorem profile_normalForm (T : Expr S) : Ω.profile T.normalForm = Ω.profile T := by
  simp only [profile, Expr.normalForm_idem]

theorem profile_feasible {T : Expr S} {s : S} (ht : Ω.HasType T (.sort s)) :
    FeasibleProfile P (Ω.profile T) := by
  obtain ⟨n, hn⟩ := ht
  change PureTypeSystem.HasType P (Ω.context n) (T.rename (Expr.reverseIndex n)) (.sort s) at hn
  rw [Ω.profile_at hw hn]
  exact Profile.feasible (hn.weaklyNormalizing hw) (Profile.nonempty_of_sorted hw hn)

theorem potential_at_next (C D : Set (Set S)) {n : Nat} {T : Expr S} {s : S}
    (ht : PureTypeSystem.HasType P (Ω.context n) (T.rename (Expr.reverseIndex n)) (.sort s)) :
    PlainObservations.potential P C D (Ω.context (n+1)) (T.rename (Expr.reverseIndex (n+1))) =
      PlainObservations.potential P C D (Ω.context n) (T.rename (Expr.reverseIndex n)) := by
  have hs : T.Scoped n := by
    have h := ht.scope.1.reverseIndex
    rwa [Ω.length, Expr.reverseIndex_twice] at h
  obtain ⟨A, t, hA, he⟩ := Ω.step n
  rw [he, hs.reverseIndex_succ]
  exact PlainObservations.potential_rename hw ht (.cons hA.valid hA) Nat.succ
    (fun _ _ hn => .weaken (PureTypeSystem.HasType.lookup hA.valid hn) hA)

theorem potential_at_mono (C D : Set (Set S)) {n m : Nat} {T : Expr S} {s : S}
    (ht : PureTypeSystem.HasType P (Ω.context n) (T.rename (Expr.reverseIndex n)) (.sort s))
    (h : n ≤ m) :
    PlainObservations.potential P C D (Ω.context m) (T.rename (Expr.reverseIndex m)) =
      PlainObservations.potential P C D (Ω.context n) (T.rename (Expr.reverseIndex n)) := by
  induction h with
  | refl => rfl
  | @step m h ih =>
      exact (Ω.potential_at_next hw C D (Ω.at_mono (A := .sort s) ht h)).trans ih

noncomputable def potential (C D : Set (Set S)) (T : Expr S) : Nat :=
  if h : ∃ n s, PureTypeSystem.HasType P (Ω.context n) (T.rename (Expr.reverseIndex n)) (.sort s)
  then PlainObservations.potential P C D (Ω.context h.choose) (T.rename (Expr.reverseIndex h.choose))
  else 1

theorem potential_at (C D : Set (Set S)) {n : Nat} {T : Expr S} {s : S}
    (ht : PureTypeSystem.HasType P (Ω.context n) (T.rename (Expr.reverseIndex n)) (.sort s)) :
    Ω.potential C D T =
      PlainObservations.potential P C D (Ω.context n) (T.rename (Expr.reverseIndex n)) := by
  have h : ∃ m t, PureTypeSystem.HasType P (Ω.context m) (T.rename (Expr.reverseIndex m)) (.sort t) :=
    ⟨n, s, ht⟩
  rw [potential, dite_eq_left h]
  obtain ⟨t, hT⟩ := h.choose_spec
  exact (Ω.potential_at_mono hw C D hT (le_max_left h.choose n)).symm.trans
    (Ω.potential_at_mono hw C D ht (le_max_right h.choose n))

/-- Formation data for a global legal frame, retaining the open codomain
profile instead of imposing functionality. -/
theorem frame_profiles {A B q : Expr S} {s : S}
    (hT : Ω.HasType (.pi A B) (.sort s)) (hq : Ω.HasType q A) :
    ∃ J, ProfileTriple P (Ω.profile A) J (Ω.profile (.pi A B)) ∧
      PositivePath (PrimaryEdge P) (Ω.profile (B.instantiate q)) J := by
  obtain ⟨n, hT, hq⟩ := hT.common hq
  change PureTypeSystem.HasType P (Ω.context n)
    (.pi (A.rename (Expr.reverseIndex n)) (B.rename (Expr.liftRen (Expr.reverseIndex n)))) (.sort s) at hT
  obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
  have hQ := hB.instantiate hq
  rw [Expr.instantiate_rename] at hQ
  have htr := Profile.triple hw hT
  have hp := Profile.growth_path hw hB hq.valid _ (TypedSubstitution.single hq)
  change PositivePath (PrimaryEdge P)
    (Profile P (Ω.context n) ((B.rename (Expr.liftRen (Expr.reverseIndex n))).instantiate
      (q.rename (Expr.reverseIndex n)))) _ at hp
  rw [Expr.instantiate_rename] at hp
  refine ⟨Profile P (A.rename (Expr.reverseIndex n) :: Ω.context n)
    (B.rename (Expr.liftRen (Expr.reverseIndex n))), ?_, ?_⟩
  · rw [Ω.profile_at hw hA, Ω.profile_at hw (T := .pi A B) hT]
    exact htr
  · rw [Ω.profile_at hw hQ]
    exact hp

omit hw in
theorem domain_sorted {A B : Expr S} {s : S}
    (hT : Ω.HasType (.pi A B) (.sort s)) : ∃ a, Ω.HasType A (.sort a) := by
  obtain ⟨n, hT⟩ := hT
  obtain ⟨a, b, c, hA, _, _, _⟩ := hT.generation_pi
  exact ⟨a, n, hA⟩

omit hw in
theorem frame_target_sorted {A B q : Expr S} {s : S}
    (hT : Ω.HasType (.pi A B) (.sort s)) (hq : Ω.HasType q A) :
    ∃ b, Ω.HasType (B.instantiate q) (.sort b) := by
  obtain ⟨n, hT, hq⟩ := hT.common hq
  obtain ⟨a, b, c, _, hB, _, _⟩ := hT.generation_pi
  refine ⟨b, n, ?_⟩
  have h := hB.instantiate hq
  change PureTypeSystem.HasType P (Ω.context n)
    ((B.rename (Expr.liftRen (Expr.reverseIndex n))).instantiate (q.rename (Expr.reverseIndex n)))
    (.sort b) at h
  rw [Expr.instantiate_rename] at h
  exact h

/-- Global form of the source strict target-potential inequality. -/
theorem frame_target_drop {C D : Set (Set S)}
    (hno : ¬ ForbiddenConfiguration P C)
    (hD : IsComponent (SecondaryEdge P C) D) (hplain : ∀ I ∈ D, PlainLayer P C I)
    (hneg : ∃ I ∈ D, ∃ K ∈ D, SecondaryEdge P C I K true)
    {A B q : Expr S} {s : S} (hT : Ω.HasType (.pi A B) (.sort s))
    (hN : Normal (.pi A B)) (hq : Ω.HasType q A)
    (hK : Ω.profile (.pi A B) ∈ D) (hL : Ω.profile (B.instantiate q) ∈ D) :
    Ω.potential C D (B.instantiate q).normalForm < Ω.potential C D (.pi A B) := by
  obtain ⟨n, hT, hq⟩ := hT.common hq
  change PureTypeSystem.HasType P (Ω.context n)
    (.pi (A.rename (Expr.reverseIndex n)) (B.rename (Expr.liftRen (Expr.reverseIndex n)))) (.sort s) at hT
  obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
  have hQ := hB.instantiate hq
  rw [Expr.instantiate_rename] at hQ
  have wQ : WeaklyNormalizing (B.instantiate q) :=
    (show Ω.HasType (B.instantiate q) (.sort b) from ⟨n, hQ⟩).weaklyNormalizing hw
  have hQN := hQ.normalForm hw
  rw [Expr.normalForm_rename wQ] at hQN
  rw [Ω.potential_at hw C D hQN, Ω.potential_at hw C D (T := .pi A B) hT,
    ← Expr.normalForm_rename wQ, ← Expr.instantiate_rename]
  rw [Ω.profile_at hw (T := .pi A B) hT] at hK
  rw [Ω.profile_at hw hQ, ← Expr.instantiate_rename] at hL
  have hh := PlainObservations.frame_potential_drop hw hno hD hplain hneg hT
    (hN.rename _) hq hK hL
  exact lt_of_le_of_lt hh.1 hh.2

/-- Every active same-component domain is counted, even when a frame exits
its component. This is why the potential's guard is activity, not membership
of the open codomain in the component. -/
theorem frame_domain_drop {C D : Set (Set S)}
    {A B q : Expr S} {s : S} (hT : Ω.HasType (.pi A B) (.sort s)) (hq : Ω.HasType q A)
    (hK : ActiveLayer P C (Ω.profile (.pi A B)))
    (hL : ActiveLayer P C (Ω.profile (B.instantiate q)))
    (hI : Ω.profile A ∈ D) :
    Ω.potential C D A < Ω.potential C D (.pi A B) := by
  obtain ⟨n, hT, hq⟩ := hT.common hq
  change PureTypeSystem.HasType P (Ω.context n)
    (.pi (A.rename (Expr.reverseIndex n)) (B.rename (Expr.liftRen (Expr.reverseIndex n)))) (.sort s) at hT
  obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
  have hQ := hB.instantiate hq
  rw [Expr.instantiate_rename] at hQ
  have hp := Profile.growth_path hw hB hq.valid _ (TypedSubstitution.single hq)
  change PositivePath (PrimaryEdge P)
    (Profile P (Ω.context n) ((B.rename (Expr.liftRen (Expr.reverseIndex n))).instantiate
      (q.rename (Expr.reverseIndex n)))) _ at hp
  rw [Expr.instantiate_rename, ← Ω.profile_at hw hQ] at hp
  have hJH := ObservationLayers.positive hL.layer hp
  have hJ := hK.predecessor (Reach.single (SecondaryEdge.positive hJH hK.layer
    (by rw [Ω.profile_at hw (T := .pi A B) hT]; exact .codomain (Profile.triple hw hT))))
  have hc : Profile P (Ω.context n) (A.rename (Expr.reverseIndex n)) ∈ D ∧
      ActiveLayer P C (Profile P (A.rename (Expr.reverseIndex n) :: Ω.context n)
        (B.rename (Expr.liftRen (Expr.reverseIndex n)))) := by
    exact ⟨Ω.profile_at hw hA ▸ hI, hJ⟩
  rw [Ω.potential_at hw C D hA, Ω.potential_at hw C D (T := .pi A B) hT]
  simp only [Expr.rename, PlainObservations.potential, ite_eq_left hc]
  omega

end

variable {S : Type u} {P : Specification S} (Ω : ContextTower P)

/-- Substitution of a typed normal generic expression can only grow its exact
profile. The common-stage reduction keeps nonfunctional sort choices. -/
theorem profile_subst_growth (hw : SystemWeaklyNormalizing P) {Γ : List (Expr S)}
    {T : Expr S} {s : S} {σ : Nat → Expr S} (ht : PureTypeSystem.HasType P Γ T (.sort s))
    (hσ : Ω.TypedSubstitution Γ σ) : Profile P Γ T ⊆ Ω.profile (T.subst σ) := by
  obtain ⟨k, hk⟩ := TypedSubstitution.common_stage hσ
  let σ' := fun n => (σ n).rename (Expr.reverseIndex k)
  have hs : PureTypeSystem.TypedSubstitution P Γ (Ω.context k) σ' := by
    intro n A hn
    simpa only [σ', ← Expr.rename_subst] using hk n A hn
  have hT := ht.subst (Ω.valid k) σ' hs
  have hp := Profile.growth hw (ht.weaklyNormalizing hw) (Ω.valid k) σ' hs
  have he : T.subst σ' = (T.subst σ).rename (Expr.reverseIndex k) := (Expr.rename_subst _ _ _).symm
  rw [he] at hT hp
  rwa [Ω.profile_at hw hT]

end ContextTower
end PureTypeSystem

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Interface
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact local obligations used when advancing a primary component.
This is an internal interface, not a hypothesis of the main PTS theorem. -/
namespace PureTypeSystem
universe u v

/-- Expected types include unsorted literal sorts (the regularity alternative). -/
def Expected {S : Type u} (P : Specification S) (Γ : List (Expr S)) (A : Expr S) : Prop :=
  (∃ s, A = .sort s) ∨ ∃ s, HasType P Γ A (.sort s)
namespace Expected
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {A D : Expr S}
theorem sorted {s : S} (h : HasType P Γ A (.sort s)) : Expected P Γ A := .inr ⟨s,h⟩
theorem wn (hw : SystemWeaklyNormalizing P) (h : Expected P Γ A) : WeaklyNormalizing A := by
  rcases h with ⟨s,rfl⟩ | ⟨s,h⟩
  · exact ⟨_,.refl,Normal.sort s⟩
  · exact h.weaklyNormalizing hw
end Expected

namespace Expr
variable {S : Type u}
def extend (σ : Nat → Expr S) (n : Expr S) : Nat → Expr S
  | 0 => n
  | i+1 => σ i
@[simp] theorem extend_zero (σ : Nat → Expr S) (n : Expr S) : extend σ n 0 = n := rfl
@[simp] theorem extend_succ (σ : Nat → Expr S) (n : Expr S) (i : Nat) : extend σ n (i+1) = σ i := rfl
@[simp] theorem subst_raise_extend (M n : Expr S) (σ : Nat → Expr S) :
    (M.rename Nat.succ).subst (extend σ n) = M.subst σ := by
  rw [subst_rename]; rfl
@[simp] theorem instantiate_extended (M n : Expr S) (σ : Nat → Expr S) :
    (M.subst (liftSub σ)).instantiate n = M.subst (extend σ n) := by
  rw [instantiate,subst_subst]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i => exact subst_lift_single (σ i) n
end Expr

/-- Ground=top has already been proved on U; U is predecessor closed and
contains every strict predecessor of the component currently processed. -/
structure Processed {S : Type u} {P : Specification S} (Ω : ContextTower P)
    (U C : Set (Set S)) : Prop where
  disjoint : Disjoint U C
  closed : ∀ {I J}, J ∈ U → Reach (PrimaryEdge P) I J → I ∈ U
  before : ∀ {I J}, J ∈ C → Reach (PrimaryEdge P) I J → I ∈ U ∨ I ∈ C
  invariant : ∀ {T}, Candidates.ActualType Ω T → Ω.profile T ∈ U →
    Candidates.Ground Ω T = Candidates.Top Ω T

/-- Environments carry arbitrary typed raw images. Extension collections are
nonempty, and retain old parameters. Product tests range over all listed
extensions; specialization can select the normal argument's tested payload. -/
structure ComponentInterface {S : Type u} {P : Specification S} (Ω : ContextTower P)
    (hw : SystemWeaklyNormalizing P) (C : Set (Set S)) where
  Env : List (Expr S) → Type v
  images : {Γ : List (Expr S)} → Env Γ → Nat → Expr S
  typed : ∀ {Γ} (e : Env Γ), Ω.TypedSubstitution Γ (images e)
  inhabit : ∀ {Γ} (σ : Nat → Expr S), Ω.TypedSubstitution Γ σ →
    ∃ e : Env Γ, images e = σ
  Ext : {Γ : List (Expr S)} → {D : Expr S} → Env Γ → Env (D :: Γ) → Expr S → Prop
  ext_images : ∀ {Γ D} {e : Env Γ} {e' : Env (D :: Γ)} {n}, Ext e e' n →
    images e' = Expr.extend (images e) n
  extend : ∀ {Γ D s} (e : Env Γ), HasType P Γ D (.sort s) → ∀ n,
    Ω.HasType n (D.subst (images e)) → ∃ e' : Env (D :: Γ), Ext e e' n
  R : {Γ : List (Expr S)} → Expr S → Env Γ → Set (Expr S)
  candidate : ∀ {Γ A} (e : Env Γ), Expected P Γ A →
    Candidates.IsCandidate Ω (A.subst (images e)).normalForm (R A e)
  conversion : ∀ {Γ A B} (e : Env Γ), Expected P Γ A → Expected P Γ B →
    Converts A B → R A e = R B e
  outside : ∀ {Γ A} (e : Env Γ), Expected P Γ A →
    (Profile P Γ A ∉ C ∨ Ω.profile (A.subst (images e)) ∉ C) →
    R A e = Candidates.Top Ω (A.subst (images e)).normalForm
  weakening : ∀ {Γ D A s} {e : Env Γ} {e' : Env (D :: Γ)} {n},
    HasType P Γ D (.sort s) → Expected P Γ A → Ext e e' n →
    R (A.rename Nat.succ) e' = R A e
  product_intro : ∀ {Γ D E s} (e : Env Γ), HasType P Γ (.pi D E) (.sort s) →
    Profile P Γ (.pi D E) ∈ C → Ω.profile ((Expr.pi D E).subst (images e)) ∈ C →
    ∀ h, h ∈ Candidates.Top Ω ((Expr.pi D E).subst (images e)).normalForm →
    (∀ n, n ∈ R D e → ∀ e' : Env (D :: Γ), Ext e e' n → Expr.app h n ∈ R E e') →
    h ∈ R (.pi D E) e
  specialization : ∀ {Γ D E s N} (e : Env Γ), HasType P Γ (.pi D E) (.sort s) →
    HasType P Γ N D → Profile P Γ (.pi D E) ∈ C →
    Ω.profile ((Expr.pi D E).subst (images e)) ∈ C →
    ∀ h, h ∈ R (.pi D E) e → N.subst (images e) ∈ R D e →
    Expr.app h (N.subst (images e)) ∈ R (E.instantiate N) e

namespace ComponentInterface
open Candidates
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable {hw : SystemWeaklyNormalizing P} {U C : Set (Set S)}
variable (J : ComponentInterface.{u,v} Ω hw C)

def Admissible {Γ : List (Expr S)} (e : J.Env Γ) : Prop :=
  ∀ i B, Lookup Γ i B →
    (Profile P Γ B ∈ C → J.images e i ∈ J.R B e) ∧
    (Profile P Γ B ∈ U → StronglyNormalizing (J.images e i)) ∧
    (Profile P Γ B ∉ U → Profile P Γ B ∉ C →
      J.images e i ∈ Ground Ω (B.subst (J.images e)).normalForm)

end ComponentInterface

namespace Expected
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable {Γ : List (Expr S)} {A : Expr S} {σ : Nat → Expr S}
theorem subst_wn (h : Expected P Γ A) (hw : SystemWeaklyNormalizing P)
    (hσ : Ω.TypedSubstitution Γ σ) : WeaklyNormalizing (A.subst σ) := by
  rcases h with ⟨s,rfl⟩ | ⟨s,h⟩
  · exact ⟨_,.refl,Normal.sort s⟩
  · exact (ContextTower.HasType.subst h hσ).weaklyNormalizing hw

end Expected

namespace ContextTower
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)
variable (hw : SystemWeaklyNormalizing P)
include hw
theorem profile_subst_path {Γ : List (Expr S)} {T : Expr S} {s : S} {σ : Nat → Expr S}
    (ht : PureTypeSystem.HasType P Γ T (.sort s)) (hσ : Ω.TypedSubstitution Γ σ) :
    PositivePath (PrimaryEdge P) (Ω.profile (T.subst σ)) (Profile P Γ T) :=
  Profile.inclusion_path (Ω.profile_feasible hw (HasType.subst ht hσ))
    (Profile.feasible (ht.weaklyNormalizing hw) (Profile.nonempty_of_sorted hw ht))
    (Ω.profile_subst_growth hw ht hσ)

theorem profile_instantiate_product_path {D E n : Expr S} {s : S}
    (hp : Ω.HasType (.pi D E) (.sort s)) (hn : Ω.HasType n D) :
    PositivePath (PrimaryEdge P) (Ω.profile (E.instantiate n)) (Ω.profile (.pi D E)) := by
  obtain ⟨k,hp,hn⟩ := hp.common hn
  obtain ⟨a,b,c,_,hE,_,_⟩ := hp.generation_pi
  have hEn := hE.instantiate hn
  change PureTypeSystem.HasType P (Ω.context k)
    ((E.rename (Expr.liftRen (Expr.reverseIndex k))).instantiate (n.rename (Expr.reverseIndex k))) (.sort b) at hEn
  rw [Expr.instantiate_rename] at hEn
  rw [Ω.profile_at hw hEn,Ω.profile_at hw hp]
  simpa only [Expr.rename,Expr.instantiate_rename] using Profile.instantiate_product_path hw hp hn
end ContextTower

namespace Candidates
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable (hw : SystemWeaklyNormalizing P)
include hw
/-- G propagates through the normal form of a raw dependent product. -/
theorem ground_application_subst {Γ : List (Expr S)} {D E n h : Expr S} {s : S}
    {σ : Nat → Expr S} (hp : HasType P Γ (.pi D E) (.sort s))
    (hσ : Ω.TypedSubstitution Γ σ)
    (hh : h ∈ Ground Ω ((Expr.pi D E).subst σ).normalForm)
    (hn : n ∈ Top Ω (D.subst σ).normalForm) :
    Expr.app h n ∈ Ground Ω (E.subst (Expr.extend σ n)).normalForm := by
  obtain ⟨a,b,c,hD,hE,_,_⟩ := hp.generation_pi
  have hraw := ContextTower.HasType.subst hp hσ
  have hwraw := hraw.weaklyNormalizing hw
  change WeaklyNormalizing (.pi (D.subst σ) (E.subst (Expr.liftSub σ))) at hwraw
  have hrawD := ContextTower.HasType.subst hD hσ
  have hnr : Ω.HasType n (D.subst σ) := hn.1.conversion hrawD
    (.symm _ _ (Expr.normalForm_spec (hrawD.weaklyNormalizing hw)).1.converts)
  have hparts : WeaklyNormalizing (D.subst σ) ∧
      WeaklyNormalizing (E.subst (Expr.liftSub σ)) := by
    obtain ⟨normal, reduction, hnormal⟩ := hwraw
    obtain ⟨domain, body, rfl, hdomain, hbody⟩ := Reduces.pi_inv reduction
    exact ⟨⟨domain, hdomain, hnormal.pi_domain⟩, ⟨body, hbody, hnormal.pi_body⟩⟩
  have htarget : Ω.HasType (E.subst (Expr.extend σ n)) (.sort b) :=
    ContextTower.HasType.subst hE (hσ.cons hnr)
  have hnf : ((Expr.pi D E).subst σ).normalForm =
      .pi (D.subst σ).normalForm (E.subst (Expr.liftSub σ)).normalForm :=
    Expr.normalForm_pi hparts.1 hparts.2
  rw [hnf] at hh
  have hout := ground_application hw hh hn
  have hpN := hraw.normalForm hw
  rw [hnf] at hpN
  obtain ⟨t,ht⟩ := Ω.frame_target_sorted hpN hn.1
  have hr : Reduces (E.subst (Expr.extend σ n))
      ((E.subst (Expr.liftSub σ)).normalForm.instantiate n) := by
    rw [← Expr.instantiate_extended]
    exact (Expr.normalForm_spec hparts.2).1.subst (Expr.single n)
  have he := Expr.normalForm_converts (htarget.weaklyNormalizing hw)
    (ht.weaklyNormalizing hw) hr.converts
  rwa [he]
end Candidates

namespace ComponentInterface
open Candidates
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable {hw : SystemWeaklyNormalizing P} {U C : Set (Set S)}
variable (J : ComponentInterface.{u,v} Ω hw C)

/-- The extra neutral invariant is exactly the G-prefix invariant in the
manuscript's spine argument. -/
def Transported {Γ : List (Expr S)} (M A : Expr S) (e : J.Env Γ) : Prop :=
  M.subst (J.images e) ∈ J.R A e ∧
    (Neutral M → Profile P Γ A ∉ C →
      M.subst (J.images e) ∈ Ground Ω (A.subst (J.images e)).normalForm)

end ComponentInterface
end PureTypeSystem

namespace PureTypeSystem.Candidates
universe u
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable (hw : SystemWeaklyNormalizing P)
include hw

theorem application_subst_type {Γ : List (Expr S)} {D E n h : Expr S} {s : S}
    {σ : Nat → Expr S} (hp : HasType P Γ (.pi D E) (.sort s))
    (hσ : Ω.TypedSubstitution Γ σ)
    (hh : Ω.HasType h ((Expr.pi D E).subst σ).normalForm)
    (hn : Ω.HasType n (D.subst σ).normalForm) :
    Ω.HasType (.app h n) (E.subst (Expr.extend σ n)).normalForm := by
  obtain ⟨a,b,c,hD,hE,_,_⟩ := hp.generation_pi
  have hraw := ContextTower.HasType.subst hp hσ
  have hrawD := ContextTower.HasType.subst hD hσ
  have hhr := hh.conversion hraw
    (.symm _ _ (Expr.normalForm_spec (hraw.weaklyNormalizing hw)).1.converts)
  have hnr := hn.conversion hrawD
    (.symm _ _ (Expr.normalForm_spec (hrawD.weaklyNormalizing hw)).1.converts)
  have hout := (hhr.application hnr).normalize_type hw
  simpa only [Expr.instantiate_extended] using hout

def RawProduct (Ω : ContextTower P) (D E : Expr S) (σ : Nat → Expr S)
    (X : Set (Expr S)) (Y : Expr S → Bool → Set (Expr S)) : Set (Expr S) :=
  {h | h ∈ Top Ω ((Expr.pi D E).subst σ).normalForm ∧
    ∀ n ∈ X, ∀ b, Expr.app h n ∈ Y n b}

theorem rawProduct_candidate {Γ : List (Expr S)} {D E : Expr S} {s : S}
    {σ : Nat → Expr S} {X : Set (Expr S)} {Y : Expr S → Bool → Set (Expr S)}
    (hp : HasType P Γ (.pi D E) (.sort s)) (hσ : Ω.TypedSubstitution Γ σ)
    (hX : IsCandidate Ω (D.subst σ).normalForm X)
    (hY : ∀ n ∈ X, ∀ b, IsCandidate Ω (E.subst (Expr.extend σ n)).normalForm (Y n b)) :
    IsCandidate Ω ((Expr.pi D E).subst σ).normalForm (RawProduct Ω D E σ X Y) where
  lower := by
    intro h hh
    refine ⟨ground_le_top hh,?_⟩
    intro n hn b
    exact (hY n hn b).lower (ground_application_subst hw hp hσ hh (hX.upper hn))
  upper := fun _ hh => hh.1
  expansion := by
    intro D' m a ns ht hD hm ha hns hc
    refine ⟨⟨ht,StronglyNormalizing.head_expansion hD hm ha hns hc.1.2⟩,?_⟩
    intro n hn b
    have ht' := application_subst_type hw hp hσ ht (hX.upper hn).1
    have hsn : StronglyNormalizingArgs (ns ++ [n]) := by
      apply StronglyNormalizingArgs.of_forall
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hns.of_mem hx
      · exact (List.mem_singleton.mp hx).symm ▸ (hX.upper hn).2
    have hc' := hc.2 n hn b
    have ht'' : Ω.HasType ((Expr.app (.lam D' m) a).apps (ns ++ [n]))
        (E.subst (Expr.extend σ n)).normalForm := by
      simpa only [Expr.apps_append,Expr.apps] using ht'
    have hc'' : (m.instantiate a).apps (ns ++ [n]) ∈ Y n b := by
      simpa only [Expr.apps_append,Expr.apps] using hc'
    simpa only [Expr.apps_append,Expr.apps] using
      (hY n hn b).expansion D' m a (ns ++ [n]) ht'' hD hm ha hsn hc'' 
end PureTypeSystem.Candidates

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Spaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem

universe u

/-! Set-theoretic free observation spaces.
The four fixed sets are normal keys, tagged plain payloads, base observations,
and exit observations. The construction is independent of any typing choices. -/
namespace FreeObservations

variable (Q V B O : Type u)

inductive Payload (Y : Type u) : Type u
  | none : Payload Y
  | opposite : Y → Payload Y
  | plain : V → Payload Y

abbrev Frame (Y : Type u) : Type u := Q × Payload V Y
abbrev ContinueStack (Y : Type u) : Type u := List (Frame Q V Y)
abbrev ExitStack (Y : Type u) : Type u := ContinueStack Q V Y × Frame Q V Y

@[ext] structure Table (Y : Type u) : Type u where
  continuing : ContinueStack Q V Y → B
  exiting : ExitStack Q V Y → O

namespace Payload

variable {V : Type u} {X Y Z : Type u}

def map (f : X → Y) : Payload V X → Payload V Y
  | none => none
  | opposite x => opposite (f x)
  | plain v => plain v

@[simp] theorem map_id (p : Payload V X) : map id p = p := by cases p <;> rfl
@[simp] theorem map_comp (f : X → Y) (g : Y → Z) (p : Payload V X) :
    map g (map f p) = map (g ∘ f) p := by cases p <;> rfl

theorem map_injective {f : X → Y} (hf : Function.Injective f) :
    Function.Injective (map (V := V) f) := by
  intro p q he
  cases p <;> cases q <;> simp_all [map, hf.eq_iff]

theorem map_surjective {f : X → Y} (hf : Function.Surjective f) :
    Function.Surjective (map (V := V) f) := by
  intro p
  cases p with
  | none => exact ⟨.none, rfl⟩
  | plain v => exact ⟨.plain v, rfl⟩
  | opposite y => obtain ⟨x, rfl⟩ := hf y; exact ⟨.opposite x, rfl⟩

end Payload

variable {Q V B O} {X Y Z : Type u}

def mapFrame (f : X → Y) (a : Frame Q V X) : Frame Q V Y :=
  (a.1, Payload.map f a.2)

def mapContinue (f : X → Y) : ContinueStack Q V X → ContinueStack Q V Y :=
  List.map (mapFrame f)

def mapExit (f : X → Y) (a : ExitStack Q V X) : ExitStack Q V Y :=
  (mapContinue f a.1, mapFrame f a.2)

@[simp] theorem mapFrame_id (a : Frame Q V X) : mapFrame id a = a := by
  cases a; simp [mapFrame]

@[simp] theorem mapFrame_comp (f : X → Y) (g : Y → Z) (a : Frame Q V X) :
    mapFrame g (mapFrame f a) = mapFrame (g ∘ f) a := by
  simp [mapFrame]

@[simp] theorem mapContinue_id (a : ContinueStack Q V X) : mapContinue id a = a := by
  induction a with
  | nil => rfl
  | cons a as ih => simpa only [mapContinue, List.map_cons, mapFrame_id] using congrArg (List.cons a) ih

@[simp] theorem mapContinue_comp (f : X → Y) (g : Y → Z) (a : ContinueStack Q V X) :
    mapContinue g (mapContinue f a) = mapContinue (g ∘ f) a := by
  simp only [mapContinue, List.map_map]
  congr 1
  funext a
  exact mapFrame_comp f g a

@[simp] theorem mapExit_id (a : ExitStack Q V X) : mapExit id a = a := by
  cases a; simp [mapExit]

@[simp] theorem mapExit_comp (f : X → Y) (g : Y → Z) (a : ExitStack Q V X) :
    mapExit g (mapExit f a) = mapExit (g ∘ f) a := by
  simp [mapExit]

theorem mapFrame_injective {f : X → Y} (hf : Function.Injective f) :
    Function.Injective (mapFrame (Q := Q) (V := V) f) := by
  intro p q he
  change (p.1, Payload.map f p.2) = (q.1, Payload.map f q.2) at he
  exact Prod.ext (congrArg (fun z : Q × Payload V Y => z.1) he)
    (Payload.map_injective hf (congrArg (fun z : Q × Payload V Y => z.2) he))

theorem mapFrame_surjective {f : X → Y} (hf : Function.Surjective f) :
    Function.Surjective (mapFrame (Q := Q) (V := V) f) := by
  intro p
  obtain ⟨v, hv⟩ := Payload.map_surjective hf p.2
  exact ⟨(p.1,v), Prod.ext rfl hv⟩

theorem mapContinue_injective {f : X → Y} (hf : Function.Injective f) :
    Function.Injective (mapContinue (Q := Q) (V := V) f) :=
  List.map_injective_iff.mpr (mapFrame_injective hf)

theorem mapContinue_surjective {f : X → Y} (hf : Function.Surjective f) :
    Function.Surjective (mapContinue (Q := Q) (V := V) f) :=
  List.map_surjective_iff.mpr (mapFrame_surjective hf)

theorem mapExit_injective {f : X → Y} (hf : Function.Injective f) :
    Function.Injective (mapExit (Q := Q) (V := V) f) := by
  intro p q he
  exact Prod.ext (mapContinue_injective hf (congrArg Prod.fst he))
    (mapFrame_injective hf (congrArg Prod.snd he))

theorem mapExit_surjective {f : X → Y} (hf : Function.Surjective f) :
    Function.Surjective (mapExit (Q := Q) (V := V) f) := by
  intro p
  obtain ⟨s, hs⟩ := mapContinue_surjective hf p.1
  obtain ⟨a, ha⟩ := mapFrame_surjective hf p.2
  exact ⟨(s,a), Prod.ext hs ha⟩

namespace Table

def relabel (f : X → Y) (t : Table Q V B O Y) : Table Q V B O X where
  continuing := t.continuing ∘ mapContinue f
  exiting := t.exiting ∘ mapExit f

@[simp] theorem relabel_id (t : Table Q V B O X) : relabel id t = t := by
  ext <;> simp [relabel]

@[simp] theorem relabel_comp (f : X → Y) (g : Y → Z) (t : Table Q V B O Z) :
    relabel f (relabel g t) = relabel (g ∘ f) t := by
  ext <;> simp [relabel]

def default (b : B) (o : O) : Table Q V B O X where
  continuing := fun _ => b
  exiting := fun _ => o

@[simp] theorem relabel_default (f : X → Y) (b : B) (o : O) :
    relabel (Q := Q) (V := V) f (default b o) = default b o := rfl

theorem relabel_injective {f : X → Y} (hf : Function.Surjective f) :
    Function.Injective (relabel (Q := Q) (V := V) (B := B) (O := O) f) := by
  intro a b h
  apply Table.ext
  · funext s
    obtain ⟨t, rfl⟩ := mapContinue_surjective hf s
    exact congrFun (congrArg Table.continuing h) t
  · funext s
    obtain ⟨t, rfl⟩ := mapExit_surjective hf s
    exact congrFun (congrArg Table.exiting h) t

theorem relabel_surjective {f : X → Y} (hf : Function.Injective f) (b : B) (o : O) :
    Function.Surjective (relabel (Q := Q) (V := V) (B := B) (O := O) f) := by
  intro t
  obtain ⟨c, hc⟩ := (mapContinue_injective hf).surjective_comp_right' (fun _ => b) t.continuing
  obtain ⟨e, he⟩ := (mapExit_injective hf).surjective_comp_right' (fun _ => o) t.exiting
  exact ⟨⟨c,e⟩, Table.ext hc he⟩

/-- Exact factorization through a surjective payload map, simultaneously
at all finite lengths. No continuity/topology is assumed. -/
theorem relabel_range_iff {f : X → Y} (hf : Function.Surjective f) (t : Table Q V B O X) :
    (∃ s, relabel f s = t) ↔
      (∀ a b, mapContinue f a = mapContinue f b → t.continuing a = t.continuing b) ∧
      (∀ a b, mapExit f a = mapExit f b → t.exiting a = t.exiting b) := by
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨fun _ _ he => congrArg s.continuing he, fun _ _ he => congrArg s.exiting he⟩
  · rintro ⟨hc, he⟩
    classical
    let c : ContinueStack Q V Y → ContinueStack Q V X := fun a => (mapContinue_surjective hf a).choose
    let e : ExitStack Q V Y → ExitStack Q V X := fun a => (mapExit_surjective hf a).choose
    have ch : ∀ a, mapContinue f (c a) = a := fun a => (mapContinue_surjective hf a).choose_spec
    have eh : ∀ a, mapExit f (e a) = a := fun a => (mapExit_surjective hf a).choose_spec
    refine ⟨⟨t.continuing ∘ c, t.exiting ∘ e⟩, ?_⟩
    apply Table.ext
    · funext a
      exact hc _ _ (ch _)
    · funext a
      exact he _ _ (eh _)

/-- Prefix a continue frame. Its slicing operation commutes with relabeling. -/
def slice (t : Table Q V B O X) (a : Frame Q V X) : Table Q V B O X where
  continuing := fun ns => t.continuing (a :: ns)
  exiting := fun ns => t.exiting (a :: ns.1, ns.2)

@[simp] theorem slice_relabel (f : X → Y) (t : Table Q V B O Y) (a : Frame Q V X) :
    (relabel f t).slice a = relabel f (t.slice (mapFrame f a)) := rfl

end Table

variable (Q V B O) in
@[reducible] def Stage : ℕ → Type u
  | 0 => PEmpty
  | n + 1 => Table Q V B O (Table Q V B O (Stage n))

variable (Q V B O) in
def step : ∀ n, Stage Q V B O n → Stage Q V B O (n + 1)
  | 0 => PEmpty.elim
  | n + 1 => Table.relabel (Table.relabel (step n))

variable (b : B) (o : O)

include b o in
theorem step_injective (n : ℕ) : Function.Injective (step Q V B O n) := by
  induction n with
  | zero => intro x; exact x.elim
  | succ n ih => exact Table.relabel_injective (Table.relabel_surjective ih b o)

variable (Q V B O) in
def inclusion (n m : ℕ) (h : n ≤ m) : Stage Q V B O n → Stage Q V B O m :=
  Nat.leRecOn h (fun {k} => step Q V B O k)

@[simp] theorem inclusion_self (n : ℕ) (x : Stage Q V B O n) :
    inclusion Q V B O n n le_rfl x = x := Nat.leRecOn_self x

@[simp] theorem inclusion_succ (n : ℕ) (x : Stage Q V B O n) :
    inclusion Q V B O n (n+1) (Nat.le_succ n) x = step Q V B O n x :=
  Nat.leRecOn_succ' x

theorem inclusion_trans {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k) (x : Stage Q V B O n) :
    inclusion Q V B O m k h' (inclusion Q V B O n m h x) =
      inclusion Q V B O n k (h.trans h') x := (Nat.leRecOn_trans h h' x).symm

instance stageDirectedSystem : DirectedSystem (Stage Q V B O) (inclusion Q V B O · · ·) where
  map_self := fun {_} x => inclusion_self _ x
  map_map := fun {_ _ _} h h' x => inclusion_trans h h' x

include b o in
theorem inclusion_injective {n m : ℕ} (h : n ≤ m) :
    Function.Injective (inclusion Q V B O n m h) := by
  induction m, h using Nat.le_induction with
  | base => intro x y he; simpa only [inclusion_self] using he
  | succ m hm ih =>
    intro x y he
    simp only [inclusion, Nat.leRecOn_succ hm] at he
    exact ih (step_injective b o m he)

@[reducible] local instance functionFunLike (α β : Type u) : FunLike (α → β) α β where
  coe := fun f => f
  coe_injective := fun _ _ h => h

local instance stageCoeDirectedSystem : DirectedSystem (Stage Q V B O)
    (fun i j h => @DFunLike.coe (Stage Q V B O i → Stage Q V B O j) _ _
      (functionFunLike _ _) (inclusion Q V B O i j h)) := stageDirectedSystem

variable (Q V B O) in
abbrev Minus := DirectLimit (Stage Q V B O) (inclusion Q V B O)
variable (Q V B O) in
abbrev Plus := Table Q V B O (Minus Q V B O)

variable (Q V B O) in
def embed (n : ℕ) (x : Stage Q V B O n) : Minus Q V B O := ⟦⟨n,x⟩⟧

include b o in
theorem embed_injective (n : ℕ) : Function.Injective (embed Q V B O n) :=
  DirectLimit.mk_injective _ (fun _ _ h => inclusion_injective b o h) n

@[simp] theorem embed_inclusion {n m : ℕ} (h : n ≤ m) (x : Stage Q V B O n) :
    embed Q V B O m (inclusion Q V B O n m h x) = embed Q V B O n x :=
  DirectLimit.mk_apply n m x h

@[simp] theorem embed_step (n : ℕ) (x : Stage Q V B O n) :
    embed Q V B O (n+1) (step Q V B O n x) = embed Q V B O n x := by
  rw [← inclusion_succ]; exact embed_inclusion _ _

theorem exists_embed (x : Minus Q V B O) : ∃ n y, embed Q V B O n y = x := by
  obtain ⟨n,y,rfl⟩ := DirectLimit.exists_eq_mk _ x
  exact ⟨n,y,rfl⟩

theorem exists_embed_succ (x : Minus Q V B O) : ∃ n y, embed Q V B O (n+1) y = x := by
  obtain ⟨n,y,rfl⟩ := exists_embed x
  exact ⟨n, step Q V B O n y, embed_step n y⟩

variable (Q V B O) in
def restrict (n : ℕ) : Plus Q V B O → Table Q V B O (Stage Q V B O n) :=
  Table.relabel (embed Q V B O n)

include b o in
theorem restrict_surjective (n : ℕ) : Function.Surjective (restrict Q V B O n) :=
  Table.relabel_surjective (embed_injective b o n) b o

@[simp] theorem restrict_compat (n : ℕ) (p : Plus Q V B O) :
    Table.relabel (step Q V B O n) (restrict Q V B O (n+1) p) = restrict Q V B O n p := by
  rw [restrict, Table.relabel_comp]
  congr 1
  funext x
  exact embed_step n x

theorem restrict_inclusion {n m : ℕ} (h : n ≤ m) (p : Plus Q V B O) :
    Table.relabel (inclusion Q V B O n m h) (restrict Q V B O m p) = restrict Q V B O n p := by
  rw [restrict, Table.relabel_comp]
  congr 1
  funext x
  exact embed_inclusion h x

variable (Q V B O) in
def stageBehavior : ∀ n, Stage Q V B O n → Table Q V B O (Plus Q V B O)
  | 0 => PEmpty.elim
  | n+1 => Table.relabel (restrict Q V B O n)

include b o in
theorem stageBehavior_injective (n : ℕ) : Function.Injective (stageBehavior Q V B O n) := by
  cases n with
  | zero => intro x; exact x.elim
  | succ n => exact Table.relabel_injective (restrict_surjective b o n)

theorem stageBehavior_step (n : ℕ) (x : Stage Q V B O n) :
    stageBehavior Q V B O (n+1) (step Q V B O n x) = stageBehavior Q V B O n x := by
  cases n with
  | zero => exact x.elim
  | succ n =>
    change Table.relabel _ (Table.relabel _ x) = _
    rw [Table.relabel_comp]
    congr 1
    funext p
    exact restrict_compat n p

theorem stageBehavior_inclusion {n m : ℕ} (h : n ≤ m) (x : Stage Q V B O n) :
    stageBehavior Q V B O m (inclusion Q V B O n m h x) = stageBehavior Q V B O n x := by
  induction m, h using Nat.le_induction with
  | base => rw [inclusion_self]
  | succ m hm ih =>
    simp only [inclusion, Nat.leRecOn_succ hm, stageBehavior_step]
    exact ih

variable (Q V B O) in
def behavior : Minus Q V B O → Table Q V B O (Plus Q V B O) :=
  DirectLimit.lift (inclusion Q V B O) (stageBehavior Q V B O)
    (fun _ _ h x => (stageBehavior_inclusion h x).symm)

@[simp] theorem behavior_embed (n : ℕ) (x : Stage Q V B O n) :
    behavior Q V B O (embed Q V B O n x) = stageBehavior Q V B O n x := rfl

include b o in
theorem behavior_injective : Function.Injective (behavior Q V B O) :=
  DirectLimit.lift_injective _ _ _ (stageBehavior_injective b o)

variable (Q V) in
def plusDefault (b : B) (o : O) : Plus Q V B O := Table.default b o
variable (Q V) in
def minusDefault (b : B) (o : O) : Minus Q V B O :=
  embed Q V B O 1 (Table.default b o)

@[simp] theorem behavior_default :
    behavior Q V B O (minusDefault Q V b o) = Table.default b o := rfl

/-- Slicing represented behaviors preserves the same finite stage. -/
theorem slice_range (x : Minus Q V B O) (a : Frame Q V (Plus Q V B O)) :
    ∃ y, behavior Q V B O y = (behavior Q V B O x).slice a := by
  obtain ⟨n,x,rfl⟩ := exists_embed_succ x
  refine ⟨embed Q V B O (n+1) (x.slice (mapFrame (restrict Q V B O n) a)), ?_⟩
  exact (Table.slice_relabel _ x a).symm

noncomputable def minusSlice (x : Minus Q V B O) (a : Frame Q V (Plus Q V B O)) : Minus Q V B O :=
  (slice_range x a).choose

@[simp] theorem behavior_minusSlice (x : Minus Q V B O) (a : Frame Q V (Plus Q V B O)) :
    behavior Q V B O (minusSlice x a) = (behavior Q V B O x).slice a := (slice_range x a).choose_spec

end FreeObservations

end PureTypeSystem

/-! Prefix observation spaces in the all-path plain construction.
Unrolling the exit spaces gives a single table of base observations.
Only domain feedback needs to be well founded; continuing paths themselves
may have arbitrary length and cycles. The required well-foundedness follows
from profile components and the syntax potential. -/

namespace PureTypeSystem.PlainSpaces
universe u

structure Schema (N : Type u) where
  Key : N → Type u
  target : (n : N) → Key n → N
  domain : (n : N) → Key n → Option N

namespace Schema
variable {N : Type u} (F : Schema N)

inductive Path : N → Type u
  | nil (n : N) : Path n
  | cons {n : N} (a : F.Key n) (p : Path (F.target n a)) : Path n

/-- The occurrence of a payload along a raw finite path. Certificates of a
particular domain introduce no computational information. -/
inductive Slot : {n : N} → F.Path n → N → Type u
  | head {n : N} {a : F.Key n} {p : F.Path (F.target n a)} {d : N}
      (h : F.domain n a = some d) : Slot (.cons a p) d
  | tail {n : N} {a : F.Key n} {p : F.Path (F.target n a)} {d : N}
      (s : Slot p d) : Slot (.cons a p) d

/-- A domain can be used after any finite number of continuation frames. -/
inductive Dependency : N → N → Prop
  | head {n : N} (a : F.Key n) {d : N} (h : F.domain n a = some d) : Dependency d n
  | tail {n d : N} (a : F.Key n) (h : Dependency d (F.target n a)) : Dependency d n

namespace Slot
variable {F}
theorem dependency {n d : N} {p : F.Path n} (s : F.Slot p d) : F.Dependency d n := by
  induction s with
  | head h => exact .head _ h
  | tail s ih => exact .tail _ ih
end Slot

abbrev Parameters (K : N → Type u) {n : N} (p : F.Path n) : Type u :=
  (d : N) → F.Slot p d → K d

abbrev FrameParameters (K : N → Type u) {n : N} (a : F.Key n) : Type u :=
  (d : N) → F.domain n a = some d → K d

abbrev Table (K : N → Type u) (B : Type u) (n : N) : Type u :=
  (p : F.Path n) → F.Parameters K p → B

noncomputable def Space (hw : WellFounded F.Dependency) (B : Type u) : N → Type u :=
  hw.fix fun n rec => (p : F.Path n) → ((d : N) → (s : F.Slot p d) → rec d s.dependency) → B

theorem space_eq (hw : WellFounded F.Dependency) (B : Type u) (n : N) :
    F.Space hw B n = F.Table (F.Space hw B) B n :=
  hw.fix_eq _ n

noncomputable def unfold (hw : WellFounded F.Dependency) (B : Type u) (n : N) :
    F.Space hw B n ≃ F.Table (F.Space hw B) B n :=
  Equiv.cast (F.space_eq hw B n)

namespace Parameters
variable {F} {K : N → Type u} {n : N}
def nil : F.Parameters K (.nil n) := fun _ s => nomatch s

def head {a : F.Key n} {p : F.Path (F.target n a)}
    (xs : F.Parameters K (.cons a p)) : F.FrameParameters K a :=
  fun _ h => xs _ (.head h)

def tail {a : F.Key n} {p : F.Path (F.target n a)}
    (xs : F.Parameters K (.cons a p)) : F.Parameters K p :=
  fun _ h => xs _ (.tail h)

def cons {a : F.Key n} {p : F.Path (F.target n a)}
    (x : F.FrameParameters K a) (xs : F.Parameters K p) : F.Parameters K (.cons a p)
  | _, .head h => x _ h
  | _, .tail s => xs _ s

@[simp] theorem head_cons {a : F.Key n} {p : F.Path (F.target n a)}
    (x : F.FrameParameters K a) (xs : F.Parameters K p) : (cons x xs).head = x := rfl
@[simp] theorem tail_cons {a : F.Key n} {p : F.Path (F.target n a)}
    (x : F.FrameParameters K a) (xs : F.Parameters K p) : (cons x xs).tail = xs := rfl
@[simp] theorem cons_head_tail {a : F.Key n} {p : F.Path (F.target n a)}
    (xs : F.Parameters K (.cons a p)) : cons xs.head xs.tail = xs := by
  funext d s
  cases s <;> rfl

theorem nil_unique (xs : F.Parameters K (.nil n)) : xs = nil := by
  funext d s
  cases s
end Parameters

/-- Splitting all-path tables at their first frame. -/
noncomputable def prefixEquiv (hw : WellFounded F.Dependency) (B : Type u) (n : N) :
    F.Space hw B n ≃ B × ((a : F.Key n) → F.FrameParameters (F.Space hw B) a →
      F.Space hw B (F.target n a)) where
  toFun t :=
    ⟨F.unfold hw B n t (.nil n) Parameters.nil,
     fun a x => (F.unfold hw B (F.target n a)).symm
       (fun p xs => F.unfold hw B n t (.cons a p) (Parameters.cons x xs))⟩
  invFun t := (F.unfold hw B n).symm (fun p xs => match p with
    | .nil _ => t.1
    | .cons a p => F.unfold hw B (F.target n a) (t.2 a xs.head) p xs.tail)
  left_inv t := by
    apply (F.unfold hw B n).injective
    simp only [Equiv.apply_symm_apply]
    funext p xs
    cases p with
    | nil n => rw [Parameters.nil_unique xs]
    | cons a p => simp only [Parameters.cons_head_tail]
  right_inv t := by
    apply Prod.ext
    · simp only [Equiv.apply_symm_apply]
    · funext a x
      apply (F.unfold hw B (F.target n a)).injective
      simp only [Equiv.apply_symm_apply]
      funext p xs
      rfl

/-- Constant tables give compatible distinguished parameters with no
additional choice of an inhabitant at any recursive node. -/
noncomputable def distinguished (hw : WellFounded F.Dependency) {B : Type u} (b : B) (n : N) :
    F.Space hw B n := (F.unfold hw B n).symm (fun _ _ => b)

@[simp] theorem distinguished_base (hw : WellFounded F.Dependency) {B : Type u}
    (b : B) (n : N) : (F.prefixEquiv hw B n (F.distinguished hw b n)).1 = b := by
  simp only [prefixEquiv, distinguished, Equiv.coe_fn_mk, Equiv.apply_symm_apply]

@[simp] theorem distinguished_next (hw : WellFounded F.Dependency) {B : Type u}
    (b : B) (n : N) (a : F.Key n) (x : F.FrameParameters (F.Space hw B) a) :
    (F.prefixEquiv hw B n (F.distinguished hw b n)).2 a x =
      F.distinguished hw b (F.target n a) := by
  simp only [prefixEquiv, distinguished, Equiv.coe_fn_mk, Equiv.apply_symm_apply]
end Schema
end PureTypeSystem.PlainSpaces

namespace PureTypeSystem.FreeObservations

universe u
variable {Q V B O : Type u}

/-- Membership in a specified finite minus stage, not just in the limit. -/
def InStage (n : ℕ) (x : Minus Q V B O) : Prop :=
  ∃ y : Stage Q V B O n, embed Q V B O n y = x

/-- The finite observation equivalence on unrestricted plus tables. -/
def Agree (n : ℕ) (p q : Plus Q V B O) : Prop :=
  restrict Q V B O n p = restrict Q V B O n q

namespace InStage

theorem mono {n m : ℕ} (h : n ≤ m) {x : Minus Q V B O} (hx : InStage n x) :
    InStage m x := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨inclusion Q V B O n m h y, embed_inclusion h y⟩

theorem not_zero (x : Minus Q V B O) : ¬ InStage 0 x := by
  rintro ⟨a, _⟩
  exact a.elim

theorem exists_stage (x : Minus Q V B O) : ∃ n, InStage n x :=
  exists_embed x

end InStage

namespace Agree

theorem mono {n m : ℕ} (h : n ≤ m) {p q : Plus Q V B O} (hpq : Agree m p q) :
    Agree n p q := by
  unfold Agree at *
  rw [← restrict_inclusion h p, ← restrict_inclusion h q, hpq]

theorem refl (n : ℕ) (p : Plus Q V B O) : Agree n p p := rfl

end Agree

/-- Exact characterization at a specified stage, used for the uniform
bound at a minus lambda. -/
theorem inStage_succ_iff (b : B) (o : O) (n : ℕ) (x : Minus Q V B O) :
    InStage (n+1) x ↔
      (∀ a a', mapContinue (restrict Q V B O n) a = mapContinue (restrict Q V B O n) a' →
          (behavior Q V B O x).continuing a = (behavior Q V B O x).continuing a') ∧
      (∀ a a', mapExit (restrict Q V B O n) a = mapExit (restrict Q V B O n) a' →
          (behavior Q V B O x).exiting a = (behavior Q V B O x).exiting a') := by
  constructor
  · rintro ⟨y, rfl⟩
    exact (Table.relabel_range_iff (restrict_surjective b o n) _).mp ⟨y, rfl⟩
  · intro h
    obtain ⟨y, hy⟩ := (Table.relabel_range_iff (restrict_surjective b o n) _).mpr h
    exact ⟨y, behavior_injective b o (by exact hy)⟩

/-- A table with the uniform finite invariance is represented at exactly the
promised next stage. This is stronger than mere totality in the colimit. -/
theorem exists_inStage_behavior (b : B) (o : O) (n : ℕ)
    (t : Table Q V B O (Plus Q V B O))
    (hc : ∀ a a', mapContinue (restrict Q V B O n) a = mapContinue (restrict Q V B O n) a' →
      t.continuing a = t.continuing a')
    (he : ∀ a a', mapExit (restrict Q V B O n) a = mapExit (restrict Q V B O n) a' →
      t.exiting a = t.exiting a') :
    ∃ x, InStage (n+1) x ∧ behavior Q V B O x = t := by
  obtain ⟨y, hy⟩ := (Table.relabel_range_iff (restrict_surjective b o n) t).mpr ⟨hc, he⟩
  exact ⟨embed Q V B O (n+1) y, ⟨y, rfl⟩, hy⟩

/-- Slicing remains in the same finite minus stage. -/
theorem inStage_minusSlice (b : B) (o : O) {n : ℕ} {x : Minus Q V B O} (hx : InStage n x)
    (a : Frame Q V (Plus Q V B O)) : InStage n (minusSlice x a) := by
  cases n with
  | zero => exact False.elim (InStage.not_zero x hx)
  | succ n =>
      obtain ⟨y, rfl⟩ := hx
      refine ⟨y.slice (mapFrame (restrict Q V B O n) a), ?_⟩
      apply behavior_injective b o
      rw [behavior_minusSlice]
      exact (Table.slice_relabel _ y a).symm

/-- A raw lambda table. Its body is selected by a continuing first frame;
its exit operation is selected by the unique terminal frame. Gates and
invalid-frame defaults can be included in these two functions. -/
def lambdaTable (base : B)
    (body : Frame Q V (Plus Q V B O) → Minus Q V B O)
    (exit : Frame Q V (Plus Q V B O) → O) : Table Q V B O (Plus Q V B O) where
  continuing
    | [] => base
    | a :: as => (behavior Q V B O (body a)).continuing as
  exiting
    | ([], a) => exit a
    | (a :: as, e) => (behavior Q V B O (body a)).exiting (as, e)

/-- The representability step at a minus lambda. The finite level is uniform
across *all* first frames and all stack lengths, not a pointwise bound. -/
theorem lambdaTable_representable (b : B) (o : O) (n : ℕ) (base : B)
    (body : Frame Q V (Plus Q V B O) → Minus Q V B O)
    (exit : Frame Q V (Plus Q V B O) → O)
    (hb : ∀ a, InStage (n+1) (body a))
    (hc : ∀ a a', mapFrame (restrict Q V B O n) a = mapFrame (restrict Q V B O n) a' →
      body a = body a')
    (he : ∀ a a', mapFrame (restrict Q V B O n) a = mapFrame (restrict Q V B O n) a' →
      exit a = exit a') :
    ∃ x, InStage (n+1) x ∧ behavior Q V B O x = lambdaTable base body exit := by
  apply exists_inStage_behavior b o n
  · intro as as' ha
    cases as with
    | nil =>
        cases as' with
        | nil => rfl
        | cons a as' => cases ha
    | cons a as =>
        cases as' with
        | nil => cases ha
        | cons a' as' =>
            have hh := List.cons.inj ha
            change (behavior Q V B O (body a)).continuing as =
              (behavior Q V B O (body a')).continuing as'
            rw [← hc a a' hh.1]
            exact ((inStage_succ_iff b o n (body a)).mp (hb a)).1 as as' hh.2
  · rintro ⟨as,e⟩ ⟨as',e'⟩ ha
    have hh := Prod.mk.inj ha
    cases as with
    | nil =>
        cases as' with
        | nil => exact he e e' hh.2
        | cons a as' => cases hh.1
    | cons a as =>
        cases as' with
        | nil => cases hh.1
        | cons a' as' =>
            have hs := List.cons.inj hh.1
            change (behavior Q V B O (body a)).exiting (as,e) =
              (behavior Q V B O (body a')).exiting (as',e')
            rw [← hc a a' hs.1]
            apply ((inStage_succ_iff b o n (body a)).mp (hb a)).2
            exact Prod.ext hs.2 hh.2

def FrameBound (n : Nat) (a : Frame Q V (Minus Q V B O)) : Prop :=
  ∀ x, a.2 = .opposite x → InStage n x

def ContinueBound (n : Nat) (as : ContinueStack Q V (Minus Q V B O)) : Prop :=
  ∀ a ∈ as, FrameBound n a

def ExitBound (n : Nat) (a : ExitStack Q V (Minus Q V B O)) : Prop :=
  ContinueBound n a.1 ∧ FrameBound n a.2

namespace FrameBound
variable {n m : Nat} {a : Frame Q V (Minus Q V B O)}
theorem mono (h : n ≤ m) (ha : FrameBound n a) : FrameBound m a :=
  fun x hx => (ha x hx).mono h

theorem exists_preimage (ha : FrameBound n a) :
    ∃ a' : Frame Q V (Stage Q V B O n), mapFrame (_root_.OAI.PureTypeSystem.FreeObservations.embed Q V B O n) a' = a := by
  rcases a with ⟨q,p⟩
  cases p with
  | none => exact ⟨(q,.none),rfl⟩
  | plain v => exact ⟨(q,.plain v),rfl⟩
  | opposite x =>
      obtain ⟨y,hy⟩ := ha x rfl
      exact ⟨(q,.opposite y), congrArg (fun x => (q,Payload.opposite x)) hy⟩

theorem embed (n : Nat) (a : Frame Q V (Stage Q V B O n)) :
    FrameBound n (mapFrame (FreeObservations.embed Q V B O n) a) := by
  rcases a with ⟨q,p⟩
  cases p with
  | none => intro x h; cases h
  | plain v => intro x h; cases h
  | opposite x =>
      intro y hy
      have he : FreeObservations.embed Q V B O n x = y := Payload.opposite.inj hy
      exact ⟨x,he⟩
end FrameBound

namespace ContinueBound
variable {n m : Nat} {as : ContinueStack Q V (Minus Q V B O)}
theorem mono (h : n ≤ m) (ha : ContinueBound n as) : ContinueBound m as :=
  fun a hm => (ha a hm).mono h

theorem exists_preimage (ha : ContinueBound n as) :
    ∃ as' : ContinueStack Q V (Stage Q V B O n), mapContinue (_root_.OAI.PureTypeSystem.FreeObservations.embed Q V B O n) as' = as := by
  induction as with
  | nil => exact ⟨[],rfl⟩
  | cons a as ih =>
      obtain ⟨a',ha'⟩ := (ha a (List.mem_cons_self)).exists_preimage
      obtain ⟨as',has'⟩ := ih (fun a h => ha a (List.mem_cons_of_mem _ h))
      exact ⟨a' :: as', congrArg₂ List.cons ha' has'⟩

theorem embed (n : Nat) (as : ContinueStack Q V (Stage Q V B O n)) :
    ContinueBound n (mapContinue (FreeObservations.embed Q V B O n) as) := by
  intro a ha
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
  exact FrameBound.embed n x

theorem cons (a : Frame Q V (Minus Q V B O)) (ha : FrameBound n a)
    (has : ContinueBound n as) : ContinueBound n (a :: as) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ha
  · exact has x hx
end ContinueBound

namespace Agree
variable {n m : Nat} {p q : Plus Q V B O}
theorem continuing (h : Agree n p q) {as : ContinueStack Q V (Minus Q V B O)}
    (ha : ContinueBound n as) : p.continuing as = q.continuing as := by
  obtain ⟨as',rfl⟩ := ha.exists_preimage
  exact congrArg (fun t : Table Q V B O (Stage Q V B O n) => t.continuing as') h

theorem exiting (h : Agree n p q) {as : ExitStack Q V (Minus Q V B O)}
    (ha : ExitBound n as) : p.exiting as = q.exiting as := by
  obtain ⟨as',has'⟩ := ha.1.exists_preimage
  obtain ⟨a',ha'⟩ := ha.2.exists_preimage
  have hh := congrArg (fun t : Table Q V B O (Stage Q V B O n) => t.exiting (as',a')) h
  change p.exiting (mapContinue _ as',mapFrame _ a') = q.exiting (mapContinue _ as',mapFrame _ a') at hh
  simpa only [has',ha'] using hh

theorem of_observations
    (hc : ∀ as, ContinueBound n as → p.continuing as = q.continuing as)
    (he : ∀ as, ExitBound n as → p.exiting as = q.exiting as) : Agree n p q := by
  apply Table.ext
  · funext as
    exact hc _ (ContinueBound.embed n as)
  · funext as
    exact he _ ⟨ContinueBound.embed n as.1,FrameBound.embed n as.2⟩

theorem slice (h : Agree n p q) (hmn : m ≤ n)
    (a : Frame Q V (Minus Q V B O)) (ha : FrameBound n a) : Agree m (p.slice a) (q.slice a) := by
  apply of_observations
  · intro as has
    exact h.continuing (ContinueBound.cons a ha (has.mono hmn))
  · intro as has
    exact h.exiting ⟨ContinueBound.cons a ha (has.1.mono hmn),has.2.mono hmn⟩

theorem all_levels_eq (h : ∀ n, Agree n p q) : p = q := by
  have bound_frame (a : Frame Q V (Minus Q V B O)) : ∃ n, FrameBound n a := by
    rcases a with ⟨key,payload⟩
    cases payload with
    | none => exact ⟨0, fun _ hh => by cases hh⟩
    | plain v => exact ⟨0, fun _ hh => by cases hh⟩
    | opposite x =>
        obtain ⟨n,hn⟩ := InStage.exists_stage x
        exact ⟨n,fun y hy => Payload.opposite.inj hy ▸ hn⟩
  have bound_stack (as : ContinueStack Q V (Minus Q V B O)) : ∃ n, ContinueBound n as := by
    induction as with
    | nil => exact ⟨0, fun _ hh => by cases hh⟩
    | cons a as ih =>
        obtain ⟨n,hn⟩ := bound_frame a
        obtain ⟨m,hm⟩ := ih
        exact ⟨max n m,ContinueBound.cons a (hn.mono (le_max_left _ _)) (hm.mono (le_max_right _ _))⟩
  apply Table.ext
  · funext as
    obtain ⟨n,hn⟩ := bound_stack as
    exact (h n).continuing hn
  · funext as
    obtain ⟨n,hn⟩ := bound_stack as.1
    obtain ⟨m,hm⟩ := bound_frame as.2
    exact (h (max n m)).exiting ⟨hn.mono (le_max_left _ _),hm.mono (le_max_right _ _)⟩
end Agree

variable (b : B) (o : O)
include b o

theorem minusSlice_eq_of_restrict {n : Nat} {x : Minus Q V B O} (hx : InStage (n+1) x)
    {a a' : Frame Q V (Plus Q V B O)}
    (ha : mapFrame (restrict Q V B O n) a = mapFrame (restrict Q V B O n) a') :
    minusSlice x a = minusSlice x a' := by
  apply behavior_injective b o
  rw [behavior_minusSlice,behavior_minusSlice]
  apply Table.ext
  · funext as
    apply ((inStage_succ_iff b o n x).mp hx).1
    exact congrArg (fun a => a :: mapContinue (restrict Q V B O n) as) ha
  · funext as
    apply ((inStage_succ_iff b o n x).mp hx).2
    exact Prod.ext (congrArg (fun a => a :: mapContinue (restrict Q V B O n) as.1) ha) rfl

theorem minusExit_eq_of_restrict {n : Nat} {x : Minus Q V B O} (hx : InStage (n+1) x)
    {a a' : Frame Q V (Plus Q V B O)}
    (ha : mapFrame (restrict Q V B O n) a = mapFrame (restrict Q V B O n) a') :
    (behavior Q V B O x).exiting ([],a) = (behavior Q V B O x).exiting ([],a') := by
  apply ((inStage_succ_iff b o n x).mp hx).2
  exact Prod.ext rfl ha

end PureTypeSystem.FreeObservations

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Plain
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual plain observation spaces: the domain-feedback relation is well
founded for the source PTS syntax and exact source graph exclusion. -/
namespace PureTypeSystem
universe u
namespace ActualPlain
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)
variable (C : Set (Set S))

structure Node where
  type : Expr S
  normal : Normal type
  sorted : ∃ s, Ω.HasType type (.sort s)
  plain : PlainLayer P C (Ω.profile type)

structure Key (T : Node Ω C) where
  domain : Expr S
  body : Expr S
  product : T.type = .pi domain body
  argument : Expr S
  normal : Normal argument
  typed : Ω.HasType argument domain
  active : ActiveLayer P C (Ω.profile (body.instantiate argument))

variable {Ω C}
variable (hw : SystemWeaklyNormalizing P)

namespace Key
variable {T : Node Ω C} (a : Key Ω C T)

theorem sorted : ∃ s, Ω.HasType (.pi a.domain a.body) (.sort s) := by
  simpa only [← a.product] using T.sorted

include hw

theorem target_reach : Reach (SecondaryEdge P C)
    (Ω.profile (a.body.instantiate a.argument)) (Ω.profile T.type) := by
  obtain ⟨s, hs⟩ := a.sorted
  obtain ⟨J, hj, hp⟩ := Ω.frame_profiles hw hs a.typed
  have hJ := ObservationLayers.positive a.active.layer hp
  exact (ObservationLayers.secondary a.active.layer hp).reach.trans (.single (.positive hJ T.plain.active.layer
    (a.product ▸ PrimaryEdge.codomain hj)))

theorem open_active : ∃ J, ProfileTriple P (Ω.profile a.domain) J (Ω.profile T.type) ∧
    ActiveLayer P C J := by
  obtain ⟨s, hs⟩ := a.sorted
  obtain ⟨J, hj, hp⟩ := Ω.frame_profiles hw hs a.typed
  have hJ := ObservationLayers.positive a.active.layer hp
  have he : SecondaryEdge P C J (Ω.profile T.type) false :=
    .positive hJ T.plain.active.layer (a.product ▸ PrimaryEdge.codomain hj)
  exact ⟨J, a.product ▸ hj, T.plain.active.predecessor (.single he)⟩

theorem domain_edge (ha : ActiveLayer P C (Ω.profile a.domain)) :
    SecondaryEdge P C (Ω.profile a.domain) (Ω.profile T.type) true := by
  obtain ⟨J, hj, hJ⟩ := a.open_active hw
  exact .negative ha.layer hJ.layer T.plain.active.layer hj

noncomputable def target : Node Ω C where
  type := (a.body.instantiate a.argument).normalForm
  normal := by
    obtain ⟨s, hs⟩ := a.sorted
    obtain ⟨b, hb⟩ := Ω.frame_target_sorted hs a.typed
    exact (Expr.normalForm_spec (hb.weaklyNormalizing hw)).2
  sorted := by
    obtain ⟨s, hs⟩ := a.sorted
    obtain ⟨b, hb⟩ := Ω.frame_target_sorted hs a.typed
    exact ⟨b, hb.normalForm hw⟩
  plain := by
    rw [Ω.profile_normalForm]
    exact T.plain.predecessor_path (a.target_reach hw)

noncomputable def domainNode (ha : ActiveLayer P C (Ω.profile a.domain)) : Node Ω C where
  type := a.domain
  normal := by
    have hh := T.normal
    rw [a.product] at hh
    exact hh.pi_domain
  sorted := by
    obtain ⟨s, hs⟩ := a.sorted
    exact Ω.domain_sorted hs
  plain := T.plain.predecessor (a.domain_edge hw ha)

@[simp] theorem target_profile : Ω.profile (a.target hw).type =
    Ω.profile (a.body.instantiate a.argument) := Ω.profile_normalForm _

@[simp] theorem domainNode_type (ha : ActiveLayer P C (Ω.profile a.domain)) :
    (a.domainNode hw ha).type = a.domain := rfl
end Key

noncomputable def schema : PlainSpaces.Schema (Node Ω C) where
  Key := Key Ω C
  target := fun _ a => a.target hw
  domain := fun _ a => if ha : ActiveLayer P C (Ω.profile a.domain)
    then some (a.domainNode hw ha) else none

variable {hw}

namespace Schema

theorem target_reach {n : Node Ω C} (a : (schema hw).Key n) :
    Reach (SecondaryEdge P C) (Ω.profile ((schema hw).target n a).type) (Ω.profile n.type) := by
  simpa only [schema, Key.target, ContextTower.profile_normalForm] using a.target_reach hw

theorem domain_eq {n d : Node Ω C} {a : (schema hw).Key n}
    (he : (schema hw).domain n a = some d) :
    ∃ ha : ActiveLayer P C (Ω.profile a.domain), d = a.domainNode hw ha := by
  change (if ha : ActiveLayer P C (Ω.profile a.domain) then some (a.domainNode hw ha) else none) = some d at he
  split at he
  · rename_i ha
    exact ⟨ha, (Option.some.inj he).symm⟩
  · cases he

theorem dependency_path {n d : Node Ω C} (hd : (schema hw).Dependency d n) :
    ∃ I K, SecondaryEdge P C I K true ∧ Reach (SecondaryEdge P C) (Ω.profile d.type) I ∧
      Reach (SecondaryEdge P C) K (Ω.profile n.type) := by
  induction hd with
  | @head n a d he =>
    obtain ⟨ha, rfl⟩ := domain_eq he
    exact ⟨Ω.profile a.domain, Ω.profile n.type, a.domain_edge hw ha, .refl _, .refl _⟩
  | @tail n d a hd ih =>
    obtain ⟨I, K, he, hi, hk⟩ := ih
    exact ⟨I, K, he, hi, hk.trans (target_reach a)⟩

theorem dependency_reach {n d : Node Ω C} (hd : (schema hw).Dependency d n) :
    Reach (SecondaryEdge P C) (Ω.profile d.type) (Ω.profile n.type) := by
  obtain ⟨I, K, he, hi, hk⟩ := dependency_path hd
  exact hi.trans ((Reach.single he).trans hk)

theorem dependency_negative {n d : Node Ω C} (hd : (schema hw).Dependency d n)
    {D : Set (Set S)} (hD : IsComponent (SecondaryEdge P C) D)
    (hn : Ω.profile n.type ∈ D) (hd' : Ω.profile d.type ∈ D) :
    ∃ I ∈ D, ∃ K ∈ D, SecondaryEdge P C I K true := by
  obtain ⟨I, K, he, hi, hk⟩ := dependency_path hd
  exact ⟨I, hD.between hd' hn hi ((Reach.single he).trans hk), K,
    hD.between hd' hn (hi.trans (.single he)) hk, he⟩

variable (hw)

theorem dependency_drop (hno : ¬ ForbiddenConfiguration P C)
    {n d : Node Ω C} (hd : (schema hw).Dependency d n)
    {D : Set (Set S)} (hD : IsComponent (SecondaryEdge P C) D)
    (hplain : ∀ I ∈ D, PlainLayer P C I)
    (hn : Ω.profile n.type ∈ D) (hd' : Ω.profile d.type ∈ D) :
    Ω.potential C D d.type < Ω.potential C D n.type := by
  induction hd with
  | @head n a d he =>
    obtain ⟨ha, rfl⟩ := domain_eq he
    obtain ⟨s, hs⟩ := a.sorted
    have hh := Ω.frame_domain_drop hw hs a.typed
      (a.product ▸ n.plain.active) a.active hd'
    simpa only [Key.domainNode, ← a.product] using hh
  | @tail n d a hd ih =>
    have htarget : Ω.profile ((schema hw).target n a).type ∈ D :=
      hD.between hd' hn (dependency_reach hd) (target_reach a)
    have hneg := dependency_negative hd hD htarget hd'
    have hh := ih htarget hd'
    obtain ⟨s, hs⟩ := a.sorted
    have hnN : Normal (.pi a.domain a.body) := a.product ▸ n.normal
    have hdrop := Ω.frame_target_drop hw hno hD hplain hneg hs hnN a.typed
      (a.product ▸ hn) (by simpa only [schema, Key.target, ContextTower.profile_normalForm] using htarget)
    exact hh.trans (by simpa only [schema, Key.target, ← a.product] using hdrop)

end Schema

variable [Fintype S]

noncomputable def measure (n : Node Ω C) : Nat × Nat :=
  (Reach.rank (SecondaryEdge P C) (Ω.profile n.type),
   Ω.potential C (Reach.component (SecondaryEdge P C) (Ω.profile n.type)) n.type)

/-- All domain feedback, including feedback reached after arbitrarily many
continuing frames, is strictly well founded. No bound on path length is used. -/
theorem dependency_wellFounded (hno : ¬ ForbiddenConfiguration P C) :
    WellFounded (schema (Ω := Ω) (C := C) hw).Dependency := by
  apply ((Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.onFun (f := measure (Ω := Ω) (C := C))).mono
  intro d n hd
  have hr := Schema.dependency_reach hd
  have hle := Reach.rank_mono (SecondaryEdge P C) hr
  change Prod.Lex (· < ·) (· < ·)
    (Reach.rank (SecondaryEdge P C) (Ω.profile d.type),
      Ω.potential C (Reach.component (SecondaryEdge P C) (Ω.profile d.type)) d.type)
    (Reach.rank (SecondaryEdge P C) (Ω.profile n.type),
      Ω.potential C (Reach.component (SecondaryEdge P C) (Ω.profile n.type)) n.type)
  rcases lt_or_eq_of_le hle with hlt | he
  · exact .left _ _ hlt
  · have hc := Reach.component_eq_of_rank_eq (SecondaryEdge P C) hr he
    have hdn : Ω.profile d.type ∈ Reach.component (SecondaryEdge P C) (Ω.profile n.type) :=
      ⟨Reach.reverse_of_rank_eq (SecondaryEdge P C) hr he, hr⟩
    have hdrop := Schema.dependency_drop hw hno hd
      (Reach.component_isComponent (SecondaryEdge P C) (Ω.profile n.type))
      n.plain.component_plain (Reach.mem_component _ _) hdn
    rw [he, hc]
    exact .right _ hdrop

/-- The actual (not postulated) plain observation space of every normalized
plain actual type. The base parameter B is the set of candidate assignments
when used by the component interpretation. -/
noncomputable def Space (hno : ¬ ForbiddenConfiguration P C) (B : Type u)
    (n : Node Ω C) : Type u :=
  (schema hw).Space (dependency_wellFounded hno) B n

noncomputable def prefixEquiv (hno : ¬ ForbiddenConfiguration P C) (B : Type u)
    (n : Node Ω C) : Space (hw := hw) hno B n ≃
      B × ((a : (schema hw).Key n) →
        (schema hw).FrameParameters (Space (hw := hw) hno B) a →
        Space (hw := hw) hno B ((schema hw).target n a)) :=
  (schema hw).prefixEquiv (dependency_wellFounded hno) B n

end ActualPlain
end PureTypeSystem

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Values
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual candidate bases and the three kinds of observation values.
Plain indices retain their exact normalized expression tag. All coordinates
are candidates, rather than arbitrary sets of terms. -/
namespace PureTypeSystem
universe u

namespace PrimaryEdge
variable {S : Type u} {P : Specification S} {I J : Set S} {b : Bool}
theorem target_feasible (h : PrimaryEdge P I J b) : FeasibleProfile P J := by
  cases h with
  | inclusion _ h _ => exact h
  | domain h => exact h.product
  | codomain h => exact h.product
end PrimaryEdge

namespace ObservationLayers
variable {S : Type u} {P : Specification S} {C : Set (Set S)} {I : Set S}
theorem nonempty (h : I ∈ ObservationLayers P C) : I.Nonempty := by
  obtain ⟨s, hs, hn, hp⟩ := h
  cases hp with
  | refl => exact hn
  | tail _ he => exact he.target_feasible.1
end ObservationLayers

namespace ActiveLayer
variable {S : Type u} {P : Specification S} {C : Set (Set S)} {I : Set S}
theorem nonempty (h : ActiveLayer P C I) : I.Nonempty := ObservationLayers.nonempty h.layer

theorem classify (h : ActiveLayer P C I) :
    PlainLayer P C I ∨ FreeLayer P C I false ∨ FreeLayer P C I true := by
  classical
  by_cases hp : PlainLayer P C I
  · exact .inl hp
  · obtain ⟨D, hd, b, hb⟩ := h
    cases b with
    | false => exact .inr (.inl ⟨hp, D, hd, hb⟩)
    | true => exact .inr (.inr ⟨hp, D, hd, hb⟩)
end ActiveLayer

namespace ObservationValues
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)

abbrev Candidate (T : Expr S) := {A : Set (Expr S) // Candidates.IsCandidate Ω T A}
abbrev ActualType := {T : Expr S // Candidates.ActualType Ω T}
abbrev Base := (T : ActualType Ω) → Candidate Ω T.val

def topBase : Base Ω := fun T => ⟨Candidates.Top Ω T.val, Candidates.top_candidate⟩

/-- The exact coordinate update used at product syntax. -/
noncomputable def Base.update (b : Base Ω) (T : ActualType Ω) (A : Candidate Ω T.val) : Base Ω :=
  Function.update b T A

@[simp] theorem Base.update_same (b : Base Ω) (T : ActualType Ω) (A : Candidate Ω T.val) :
    Base.update Ω b T A T = A := by simp [Base.update]

@[simp] theorem Base.update_other (b : Base Ω) (T U : ActualType Ω) (A : Candidate Ω T.val)
    (h : U ≠ T) : Base.update Ω b T A U = b U := by simp [Base.update, h]

variable [Fintype S] (C : Set (Set S)) {hw : SystemWeaklyNormalizing P}
variable (hno : ¬ ForbiddenConfiguration P C)

abbrev PlainValue := (T : ActualPlain.Node Ω C) × ActualPlain.Space (hw := hw) hno (Base Ω) T
abbrev Plus := FreeObservations.Plus (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω) (Option (PlainValue (hw := hw) Ω C hno))
abbrev Minus := FreeObservations.Minus (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω) (Option (PlainValue (hw := hw) Ω C hno))

inductive RawValue : Type u
  | plain : PlainValue (hw := hw) Ω C hno → RawValue
  | plus : Plus (hw := hw) Ω C hno → RawValue
  | minus : Minus (hw := hw) Ω C hno → RawValue

/-- The tag and sign checks for an actual normalized type. -/
def Fits (T : Expr S) : RawValue (hw := hw) Ω C hno → Prop
  | .plain x => x.1.type = T
  | .plus _ => FreeLayer P C (Ω.profile T) false
  | .minus _ => FreeLayer P C (Ω.profile T) true

abbrev Value (T : Expr S) := {v : RawValue (hw := hw) Ω C hno // Fits (hw := hw) Ω C hno T v}

structure ActiveType where
  type : Expr S
  normal : Normal type
  sorted : ∃ s, Ω.HasType type (.sort s)
  active : ActiveLayer P C (Ω.profile type)

namespace ActiveType
variable {Ω C hno}
noncomputable abbrev ofActual (T : ActualType Ω) (ha : ActiveLayer P C (Ω.profile T.val)) :
    ActiveType Ω C where
  type := T.val
  normal := by rcases T.property with h | ⟨s, h⟩; exact h.1; exact h ▸ Normal.sort s
  sorted := by
    obtain ⟨s, hs⟩ := ha.nonempty
    have hn : Normal T.val := by
      rcases T.property with h | ⟨s, h⟩; exact h.1; exact h ▸ Normal.sort s
    exact ⟨s, by simpa only [ContextTower.profile, Set.mem_ofPred_eq,
      Expr.normalForm_of_normal hn] using hs⟩
  active := ha

end ActiveType

noncomputable def plainDefault (T : ActualPlain.Node Ω C) : ActualPlain.Space (hw := hw) hno (Base Ω) T :=
  (ActualPlain.schema hw).distinguished (ActualPlain.dependency_wellFounded hno) (topBase Ω) T

noncomputable def distinguished (T : ActiveType Ω C) : Value (hw := hw) Ω C hno T.type := by
  by_cases hp : PlainLayer P C (Ω.profile T.type)
  · let n : ActualPlain.Node Ω C := ⟨T.type, T.normal, T.sorted, hp⟩
    exact ⟨.plain ⟨n, plainDefault (hw := hw) Ω C hno n⟩, rfl⟩
  · by_cases hf : FreeLayer P C (Ω.profile T.type) false
    · exact ⟨.plus (FreeObservations.plusDefault _ _ (topBase Ω) none), hf⟩
    · have hm : FreeLayer P C (Ω.profile T.type) true := by
        rcases T.active.classify with h | h | h
        · exact False.elim (hp h)
        · exact False.elim (hf h)
        · exact h
      exact ⟨.minus (FreeObservations.minusDefault _ _ (topBase Ω) none), hm⟩

noncomputable def RawValue.base : RawValue (hw := hw) Ω C hno → Base Ω
  | .plain p => (ActualPlain.prefixEquiv hno (Base Ω) p.1 p.2).1
  | .plus p => p.continuing []
  | .minus m => (FreeObservations.behavior _ _ _ _ m).continuing []

/-- Updating only the base keeps every nonempty observation unchanged. -/
noncomputable def withBase (T : ActiveType Ω C) (b : Base Ω) : Value (hw := hw) Ω C hno T.type := by
  by_cases hp : PlainLayer P C (Ω.profile T.type)
  · let n : ActualPlain.Node Ω C := ⟨T.type, T.normal, T.sorted, hp⟩
    let e := ActualPlain.prefixEquiv (hw := hw) hno (Base Ω) n
    exact ⟨.plain ⟨n, e.symm (b, (e (plainDefault (hw := hw) Ω C hno n)).2)⟩, rfl⟩
  · by_cases hf : FreeLayer P C (Ω.profile T.type) false
    · exact ⟨.plus ⟨(fun s => if s = [] then b else topBase Ω), fun _ => none⟩, hf⟩
    · have hm : FreeLayer P C (Ω.profile T.type) true := by
        rcases T.active.classify with h | h | h
        · exact False.elim (hp h)
        · exact False.elim (hf h)
        · exact h
      exact ⟨.minus (FreeObservations.embed _ _ _ _ 1
        ⟨(fun s => if s = [] then b else topBase Ω), fun _ => none⟩), hm⟩

theorem withBase_base (T : ActiveType Ω C) (b : Base Ω) :
    RawValue.base (hw := hw) Ω C hno (withBase (hw := hw) Ω C hno T b).val = b := by
  unfold withBase
  split
  · simp only [RawValue.base, Equiv.apply_symm_apply]
  · split
    · simp only [RawValue.base, ↓reduceIte]
    · simp only [RawValue.base, FreeObservations.behavior_embed, FreeObservations.stageBehavior,
        FreeObservations.Table.relabel, Function.comp_apply, FreeObservations.mapContinue,
        List.map_nil, ↓reduceIte]

/-- Invalid exit tags receive exactly the distinguished target. -/
noncomputable def project (T : ActiveType Ω C) (v : RawValue (hw := hw) Ω C hno) : Value (hw := hw) Ω C hno T.type :=
  if h : Fits (hw := hw) Ω C hno T.type v then ⟨v, h⟩ else distinguished (hw := hw) Ω C hno T

@[simp] theorem project_valid (T : ActiveType Ω C) (v : Value (hw := hw) Ω C hno T.type) :
    project (hw := hw) Ω C hno T v.val = v := by
  simp only [project, v.property, dite_true, Subtype.coe_eta]

end ObservationValues
end PureTypeSystem

namespace PureTypeSystem.ObservationValues
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

namespace RawValue

def LevelEq (n : Nat) : RawValue (hw := hw) Ω C hno → RawValue (hw := hw) Ω C hno → Prop
  | .plain p, .plain q => p = q
  | .plus p, .plus q => FreeObservations.Agree n p q
  | .minus p, .minus q => p = q
  | _, _ => False

def Bounded (n : Nat) : RawValue (hw := hw) Ω C hno → Prop
  | .minus p => FreeObservations.InStage n p
  | _ => True

variable {Ω C hno}
theorem level_refl (n : Nat) (v : RawValue (hw := hw) Ω C hno) : LevelEq _ _ _ n v v := by
  cases v <;> exact rfl

theorem level_mono {n m : Nat} (h : n ≤ m) {v w : RawValue (hw := hw) Ω C hno}
    (he : LevelEq _ _ _ m v w) : LevelEq _ _ _ n v w := by
  cases v <;> cases w <;> try exact he
  exact FreeObservations.Agree.mono h he

theorem bounded_mono {n m : Nat} (h : n ≤ m) {v : RawValue (hw := hw) Ω C hno}
    (hv : Bounded _ _ _ n v) : Bounded _ _ _ m v := by
  cases v <;> try trivial
  exact FreeObservations.InStage.mono h hv

theorem exists_bound (v : RawValue (hw := hw) Ω C hno) : ∃ n, Bounded _ _ _ n v := by
  cases v with
  | plain p => exact ⟨0, trivial⟩
  | plus p => exact ⟨0, trivial⟩
  | minus p => exact FreeObservations.InStage.exists_stage p

theorem level_base {n : Nat} {v w : RawValue (hw := hw) Ω C hno}
    (he : LevelEq _ _ _ n v w) : base _ _ _ v = base _ _ _ w := by
  cases v <;> cases w <;> try exact False.elim he
  · exact congrArg (fun p => (ActualPlain.prefixEquiv hno (Base Ω) p.1 p.2).1) he
  · exact congrFun (congrArg FreeObservations.Table.continuing he) []
  · exact congrArg (fun p => (FreeObservations.behavior _ _ _ _ p).continuing []) he
end RawValue
end PureTypeSystem.ObservationValues

namespace PureTypeSystem
universe u
namespace FreeLayer
variable {S : Type u} {P : Specification S} {C : Set (Set S)} {I J : Set S}
theorem path_sign {s t b : Bool} (h : FreeLayer P C I s) (k : FreeLayer P C J t)
    (e : SignedPath (SecondaryEdge P C) I J b) : s = Bool.xor b t := by
  obtain ⟨D, hd, hp⟩ := k.2
  exact h.sign_unique ⟨h.1, D, hd, e.append hp⟩
end FreeLayer

namespace ObservationValues
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)
variable (C : Set (Set S)) (hw : SystemWeaklyNormalizing P)

/-- A frame's key has the exact normalized domain and active target. -/
structure FrameKey (T : ActiveType Ω C) where
  domain : Expr S
  body : Expr S
  product : T.type = .pi domain body
  argument : Expr S
  normal : Normal argument
  typed : Ω.HasType argument domain
  active : ActiveLayer P C (Ω.profile (body.instantiate argument))

namespace FrameKey
variable {Ω C} {T : ActiveType Ω C} (a : FrameKey Ω C T)

theorem sorted : ∃ s, Ω.HasType (.pi a.domain a.body) (.sort s) :=
  a.product ▸ T.sorted

theorem target_sorted : ∃ s, Ω.HasType (a.body.instantiate a.argument) (.sort s) := by
  obtain ⟨s, hs⟩ := a.sorted
  exact Ω.frame_target_sorted hs a.typed

include hw

theorem profile_data : ∃ J,
    ProfileTriple P (Ω.profile a.domain) J (Ω.profile T.type) ∧
    PositivePath (PrimaryEdge P) (Ω.profile (a.body.instantiate a.argument)) J ∧
    ActiveLayer P C J := by
  obtain ⟨s, hs⟩ := a.sorted
  obtain ⟨J, hf, hp⟩ := Ω.frame_profiles hw hs a.typed
  rw [← a.product] at hf
  have hj := ObservationLayers.positive a.active.layer hp
  exact ⟨J, hf, hp, T.active.predecessor (.single (.positive hj T.active.layer (.codomain hf)))⟩

theorem target_path : PositivePath (SecondaryEdge P C)
    (Ω.profile (a.body.instantiate a.argument)) (Ω.profile T.type) := by
  obtain ⟨J, hf, hp, hj⟩ := a.profile_data hw
  exact .tail (ObservationLayers.secondary a.active.layer hp)
    (.positive hj.layer T.active.layer (.codomain hf))

theorem domain_active (hd : Ω.profile a.domain ∈ ObservationLayers P C) :
    ActiveLayer P C (Ω.profile a.domain) := by
  obtain ⟨J, hf, _, hj⟩ := a.profile_data hw
  exact T.active.predecessor (.single (.negative hd hj.layer T.active.layer hf))

theorem domain_edge (hd : ActiveLayer P C (Ω.profile a.domain)) :
    SecondaryEdge P C (Ω.profile a.domain) (Ω.profile T.type) true := by
  obtain ⟨J, hf, _, hj⟩ := a.profile_data hw
  exact .negative hd.layer hj.layer T.active.layer hf

noncomputable def target : ActiveType Ω C where
  type := (a.body.instantiate a.argument).normalForm
  normal := by
    obtain ⟨s, hs⟩ := a.target_sorted
    exact (Expr.normalForm_spec (hs.weaklyNormalizing hw)).2
  sorted := by
    obtain ⟨s, hs⟩ := a.target_sorted
    exact ⟨s, hs.normalForm hw⟩
  active := by simpa only [ContextTower.profile_normalForm] using a.active

theorem plain_domain (hp : PlainLayer P C (Ω.profile T.type))
    (hd : ActiveLayer P C (Ω.profile a.domain)) : PlainLayer P C (Ω.profile a.domain) :=
  hp.predecessor (a.domain_edge hw hd)

theorem free_target_sign {s t : Bool}
    (hT : FreeLayer P C (Ω.profile T.type) s)
    (hL : FreeLayer P C (Ω.profile (a.target hw).type) t) : t = s := by
  have hl : FreeLayer P C (Ω.profile (a.body.instantiate a.argument)) t := by
    simpa only [target, ContextTower.profile_normalForm] using hL
  simpa using hl.path_sign hT (a.target_path hw).parity

theorem free_domain_sign {s t : Bool}
    (hT : FreeLayer P C (Ω.profile T.type) s)
    (hI : FreeLayer P C (Ω.profile a.domain) t) : t = !s := by
  have h := hI.edge_sign hT (a.domain_edge hw hI.active)
  simpa using h

end FrameKey

variable [Fintype S] {hw} (hno : ¬ ForbiddenConfiguration P C)

/-- Absence is mandatory at inactive domains. There are no latent values. -/
def PayloadFits (D : Expr S) (p : Option (RawValue (hw := hw) Ω C hno)) : Prop :=
  match p with
  | none => ¬ ActiveLayer P C (Ω.profile D)
  | some v => Fits Ω C hno D v

namespace Fits
variable {Ω C hno} {T : Expr S} {v : RawValue (hw := hw) Ω C hno}
theorem active (h : Fits Ω C hno T v) : ActiveLayer P C (Ω.profile T) := by
  cases v with
  | plain p => exact h ▸ p.1.plain.active
  | plus p => exact h.active
  | minus p => exact h.active
end Fits

abbrev PlusFrame := FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno)
  (Minus (hw := hw) Ω C hno)
abbrev MinusFrame := FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno)
  (Plus (hw := hw) Ω C hno)

def plusPayload : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno)
    (Minus (hw := hw) Ω C hno) → Option (RawValue (hw := hw) Ω C hno)
  | .none => none
  | .opposite m => some (.minus m)
  | .plain p => some (.plain p)

def minusPayload : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno)
    (Plus (hw := hw) Ω C hno) → Option (RawValue (hw := hw) Ω C hno)
  | .none => none
  | .opposite p => some (.plus p)
  | .plain p => some (.plain p)

/-- Exact gates for continue/exit operations at free lambdas. -/
def Gate (T : ActiveType Ω C) (q : Expr S)
    (p : Option (RawValue (hw := hw) Ω C hno)) (exit : Bool) : Prop :=
  ∃ a : FrameKey Ω C T, a.argument = q ∧ PayloadFits Ω C hno a.domain p ∧
    (PlainLayer P C (Ω.profile (a.target hw).type) ↔ exit = true)

end ObservationValues

namespace Converts
variable {S : Type u}
theorem app {f f' a a' : Expr S} (hf : Converts f f') (ha : Converts a a') :
    Converts (.app f a) (.app f' a') := by
  obtain ⟨g, hg, hg'⟩ := hf.join
  obtain ⟨b, hb, hb'⟩ := ha.join
  exact .trans _ _ _ (hg.app hb).converts (.symm _ _ (hg'.app hb').converts)

theorem lam {A A' b b' : Expr S} (hA : Converts A A') (hb : Converts b b') :
    Converts (.lam A b) (.lam A' b') := by
  obtain ⟨D, hD, hD'⟩ := hA.join
  obtain ⟨c, hc, hc'⟩ := hb.join
  exact .trans _ _ _ (hD.lam hc).converts (.symm _ _ (hD'.lam hc').converts)
end Converts

namespace Expr.Scoped
variable {S : Type u} {n : Nat} {M : Expr S}
theorem subst_converts (hM : Scoped n M) {σ τ : Nat → Expr S}
    (hc : ∀ i, i < n → Converts (σ i) (τ i)) : Converts (M.subst σ) (M.subst τ) := by
  induction M generalizing n σ τ with
  | var i => exact hc i hM
  | sort s => exact .refl _
  | app f a ihf iha => exact .app (ihf hM.1 hc) (iha hM.2 hc)
  | lam A b ihA ihb | pi A b ihA ihb =>
    have he : ∀ i, i < n+1 → Converts (Expr.liftSub σ i) (Expr.liftSub τ i) := by
      intro i hi
      cases i with
      | zero => exact .refl _
      | succ i => exact (hc i (Nat.lt_of_succ_lt_succ hi)).rename Nat.succ
    first
    | exact .lam (ihA hM.1 hc) (ihb hM.2 he)
    | exact .pi (ihA hM.1 hc) (ihb hM.2 he)
end Expr.Scoped

namespace Lookup
variable {S : Type u} {Γ : List (Expr S)} {n : Nat}

theorem unique {A B : Expr S} (hA : Lookup Γ n A) (hB : Lookup Γ n B) : A = B := by
  induction hA generalizing B with
  | zero => cases hB; rfl
  | succ A h ih => cases hB with
    | succ _ hB => exact congrArg (Expr.rename Nat.succ) (ih hB)
end Lookup

namespace ContextTower.HasType
variable {S : Type u} {P : Specification S} {Ω : ContextTower P} {M A : Expr S}

theorem actual_type (h : Ω.HasType M A) (hw : SystemWeaklyNormalizing P) :
    Candidates.ActualType Ω A.normalForm := by
  rcases h.regularity with ⟨s, rfl⟩ | ⟨s, hs⟩
  · exact .inr ⟨s, Expr.normalForm_of_normal (Normal.sort s)⟩
  · exact .inl ⟨(Expr.normalForm_spec (hs.weaklyNormalizing hw)).2, s, hs.normalForm hw⟩

theorem actual_expression {s : S} (h : Ω.HasType M (.sort s)) (hw : SystemWeaklyNormalizing P) :
    Candidates.ActualType Ω M.normalForm :=
  .inl ⟨(Expr.normalForm_spec (h.weaklyNormalizing hw)).2, s, h.normalForm hw⟩
end ContextTower.HasType

namespace ObservationValues
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

namespace Parameter

def Bounded (n : Nat) (p : Option (RawValue (hw := hw) Ω C hno)) : Prop :=
  ∀ v, p = some v → RawValue.Bounded Ω C hno n v

def LevelEq (n : Nat) : Option (RawValue (hw := hw) Ω C hno) → Option (RawValue (hw := hw) Ω C hno) → Prop
  | none, none => True
  | some v, some w => RawValue.LevelEq Ω C hno n v w
  | _, _ => False

variable {Ω C hno}
theorem level_refl (n : Nat) (p : Option (RawValue (hw := hw) Ω C hno)) : LevelEq _ _ _ n p p := by
  cases p with
  | none => trivial
  | some p => exact p.level_refl n

theorem level_mono {n m : Nat} (h : n ≤ m) {p q : Option (RawValue (hw := hw) Ω C hno)}
    (he : LevelEq _ _ _ m p q) : LevelEq _ _ _ n p q := by
  cases p <;> cases q <;> try exact he
  exact RawValue.level_mono h he

theorem bounded_mono {n m : Nat} (h : n ≤ m) {p : Option (RawValue (hw := hw) Ω C hno)}
    (he : Bounded _ _ _ n p) : Bounded _ _ _ m p := fun v hv => RawValue.bounded_mono h (he v hv)

theorem exists_bound (p : Option (RawValue (hw := hw) Ω C hno)) : ∃ n, Bounded _ _ _ n p := by
  cases p with
  | none => exact ⟨0, fun _ h => by cases h⟩
  | some p =>
    obtain ⟨n, hn⟩ := p.exists_bound
    exact ⟨n, fun _ h => Option.some.inj h ▸ hn⟩
end Parameter

/-- Typed raw substitutions with precisely one observation parameter per
active actual declaration and none at inactive declarations. -/
structure Environment (Γ : List (Expr S)) where
  images : Nat → Expr S
  typed : Ω.TypedSubstitution Γ images
  parameters : Nat → Option (RawValue (hw := hw) Ω C hno)
  lawful : ∀ n A, Lookup Γ n A → PayloadFits Ω C hno (A.subst images).normalForm (parameters n)

namespace Environment
variable {Ω C hno} {Γ : List (Expr S)} (e : Environment (hw := hw) Ω C hno Γ)

def Bounded (k : Nat) : Prop := ∀ n, n < Γ.length → Parameter.Bounded Ω C hno k (e.parameters n)

def ImageCompatible (f : Environment (hw := hw) Ω C hno Γ) : Prop :=
  ∀ n, n < Γ.length → Converts (e.images n) (f.images n)

def LevelEq (k : Nat) (f : Environment (hw := hw) Ω C hno Γ) : Prop :=
  ImageCompatible e f ∧ ∀ n, n < Γ.length → Parameter.LevelEq Ω C hno k (e.parameters n) (f.parameters n)

theorem bounded_mono {k l : Nat} (hkl : k ≤ l) (he : e.Bounded k) : e.Bounded l :=
  fun n hn => Parameter.bounded_mono hkl (he n hn)

theorem exists_bound : ∃ k, e.Bounded k := by
  have hh : ∀ n, ∃ k, ∀ i, i < n → Parameter.Bounded Ω C hno k (e.parameters i) := by
    intro n
    induction n with
    | zero => exact ⟨0, fun _ h => by omega⟩
    | succ n ih =>
      obtain ⟨k, hk⟩ := ih
      obtain ⟨l, hl⟩ := Parameter.exists_bound (e.parameters n)
      refine ⟨max k l, fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact Parameter.bounded_mono (le_max_left k l) (hk i hi)
      · exact Parameter.bounded_mono (le_max_right k l) hl
  exact hh Γ.length

theorem level_refl (k : Nat) : e.LevelEq k e :=
  ⟨fun _ _ => .refl _, fun _ _ => Parameter.level_refl _ _⟩

theorem level_mono {k l : Nat} {f : Environment (hw := hw) Ω C hno Γ}
    (hkl : k ≤ l) (he : e.LevelEq l f) : e.LevelEq k f :=
  ⟨he.1, fun n hn => Parameter.level_mono hkl (he.2 n hn)⟩

/-- Binding a raw actual term does not normalize or evaluate its syntax. -/
def cons {A a : Expr S} (ha : Ω.HasType a (A.subst e.images))
    (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno (A.subst e.images).normalForm p) :
    Environment (hw := hw) Ω C hno (A :: Γ) where
  images := fun n => match n with | 0 => a | n+1 => e.images n
  typed := e.typed.cons ha
  parameters := fun n => match n with | 0 => p | n+1 => e.parameters n
  lawful := by
    intro n B hn
    cases hn with
    | zero => simpa only [Expr.subst_rename, Function.comp_def] using hp
    | succ A hn => simpa only [Expr.subst_rename, Function.comp_def] using e.lawful _ _ hn

theorem bounded_cons {A a : Expr S} (ha : Ω.HasType a (A.subst e.images))
    (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno (A.subst e.images).normalForm p)
    {k : Nat} (he : e.Bounded k) (hb : Parameter.Bounded Ω C hno k p) :
    (e.cons ha p hp).Bounded k := by
  intro n hn
  cases n with
  | zero => exact hb
  | succ n => exact he n (Nat.lt_of_succ_lt_succ hn)

theorem actual_expr_eq {f : Environment (hw := hw) Ω C hno Γ} (he : e.ImageCompatible f)
    {M A : Expr S} (ht : HasType P Γ M A) :
    (M.subst e.images).normalForm = (M.subst f.images).normalForm :=
  Expr.normalForm_converts ((ContextTower.HasType.subst ht e.typed).weaklyNormalizing hw)
    ((ContextTower.HasType.subst ht f.typed).weaklyNormalizing hw)
    (ht.scope.1.subst_converts he)

theorem actual_type_eq {f : Environment (hw := hw) Ω C hno Γ} (he : e.ImageCompatible f)
    {M A : Expr S} (ht : HasType P Γ M A) :
    (A.subst e.images).normalForm = (A.subst f.images).normalForm :=
  Expr.normalForm_converts ((ContextTower.HasType.subst ht e.typed).type_weaklyNormalizing hw)
    ((ContextTower.HasType.subst ht f.typed).type_weaklyNormalizing hw)
    (ht.scope.2.subst_converts he)
end Environment
end ObservationValues

namespace WeaklyNormalizing
variable {S : Type u} {A B : Expr S}
theorem pi_domain (h : WeaklyNormalizing (.pi A B)) : WeaklyNormalizing A := by
  obtain ⟨N,hr,hn⟩ := h
  obtain ⟨D,E,rfl,hD,_⟩ := Reduces.pi_inv hr
  exact ⟨D,hD,hn.pi_domain⟩
theorem pi_body (h : WeaklyNormalizing (.pi A B)) : WeaklyNormalizing B := by
  obtain ⟨N,hr,hn⟩ := h
  obtain ⟨D,E,rfl,_,hE⟩ := Reduces.pi_inv hr
  exact ⟨E,hE,hn.pi_body⟩
end WeaklyNormalizing

namespace Expr
variable {S : Type u}
theorem instantiate_liftSub (E : Expr S) (σ : Nat → Expr S) (n : Expr S) :
    (E.subst (liftSub σ)).instantiate n =
      E.subst (fun i => match i with | 0 => n | i+1 => σ i) := by
  rw [instantiate, subst_subst]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i => simpa only [liftSub_succ, subst_rename, Function.comp_def, single] using subst_var (σ i)
end Expr

namespace ContextTower.HasType
variable {S : Type u} {P : Specification S} {Ω : ContextTower P} {M A : Expr S} {s : S}
theorem denormalize_type (h : Ω.HasType M A.normalForm) (hA : Ω.HasType A (.sort s))
    (hw : SystemWeaklyNormalizing P) : Ω.HasType M A :=
  h.conversion hA (.symm _ _ (Expr.normalForm_spec (hA.weaklyNormalizing hw)).1.converts)
end ContextTower.HasType

namespace ObservationValues
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

namespace PayloadFits
variable {Ω C hno}
theorem exists_of_actual (T : ActualType Ω) : ∃ p, PayloadFits (hw := hw) Ω C hno T.val p := by
  by_cases ha : ActiveLayer P C (Ω.profile T.val)
  · exact ⟨some (distinguished (hw := hw) Ω C hno (.ofActual T ha)).val,
      (distinguished (hw := hw) Ω C hno (.ofActual T ha)).property⟩
  · exact ⟨none,ha⟩
end PayloadFits

/-- A product's exact stored formation data and its raw environment. -/
structure ProductInstance where
  context : List (Expr S)
  domain : Expr S
  body : Expr S
  domainSort : S
  bodySort : S
  resultSort : S
  domainTyping : HasType P context domain (.sort domainSort)
  bodyTyping : HasType P (domain :: context) body (.sort bodySort)
  rule : P.rule domainSort bodySort resultSort
  environment : Environment (hw := hw) Ω C hno context

namespace ProductInstance
variable {Ω C hno} (t : ProductInstance (hw := hw) Ω C hno)
def rawDomain : Expr S := t.domain.subst t.environment.images
def rawBody : Expr S := t.body.subst (Expr.liftSub t.environment.images)
noncomputable def domainNF : Expr S := t.rawDomain.normalForm
noncomputable def bodyNF : Expr S := t.rawBody.normalForm
def rawTarget (n : Expr S) : Expr S :=
  t.body.subst (fun i => match i with | 0 => n | i+1 => t.environment.images i)
noncomputable def targetNF (n : Expr S) : Expr S := (t.rawTarget n).normalForm

theorem rawDomain_typed : Ω.HasType t.rawDomain (.sort t.domainSort) :=
  ContextTower.HasType.subst t.domainTyping t.environment.typed

theorem rawProduct_typed : Ω.HasType (.pi t.rawDomain t.rawBody) (.sort t.resultSort) :=
  ContextTower.HasType.subst (HasType.product t.domainTyping t.bodyTyping t.rule) t.environment.typed

theorem product_nf : (Expr.pi t.rawDomain t.rawBody).normalForm = .pi t.domainNF t.bodyNF :=
  Expr.normalForm_pi (t.rawProduct_typed.weaklyNormalizing hw).pi_domain
    (t.rawProduct_typed.weaklyNormalizing hw).pi_body

theorem product_typed : Ω.HasType (.pi t.domainNF t.bodyNF) (.sort t.resultSort) := by
  rw [← t.product_nf]
  exact t.rawProduct_typed.normalForm hw

theorem rawArgument {n : Expr S} (hn : Ω.HasType n t.domainNF) : Ω.HasType n t.rawDomain :=
  hn.denormalize_type t.rawDomain_typed hw

noncomputable def extend {n : Expr S} (hn : Ω.HasType n t.domainNF)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno t.domainNF p) :
    Environment (hw := hw) Ω C hno (t.domain :: t.context) :=
  t.environment.cons (t.rawArgument hn) p hp

theorem rawTarget_typed {n : Expr S} (hn : Ω.HasType n t.domainNF) :
    Ω.HasType (t.rawTarget n) (.sort t.bodySort) :=
  ContextTower.HasType.subst t.bodyTyping (t.environment.typed.cons (t.rawArgument hn))

theorem target_typed {n : Expr S} (hn : Ω.HasType n t.domainNF) :
    Ω.HasType (t.targetNF n) (.sort t.bodySort) := (t.rawTarget_typed hn).normalForm hw

theorem target_eq {n : Expr S} (hn : Ω.HasType n t.domainNF) :
    t.targetNF n = (t.bodyNF.instantiate n).normalForm := by
  have hr : Reduces (t.rawTarget n) (t.bodyNF.instantiate n) := by
    rw [rawTarget, ← Expr.instantiate_liftSub]
    exact (Expr.normalForm_spec (t.rawProduct_typed.weaklyNormalizing hw).pi_body).1.subst (Expr.single n)
  obtain ⟨s,hs⟩ := Ω.frame_target_sorted t.product_typed hn
  exact Expr.normalForm_converts ((t.rawTarget_typed hn).weaklyNormalizing hw)
    (hs.weaklyNormalizing hw) hr.converts

/-- The tester set uses the domain Read precisely at this primary component. -/
noncomputable def testers (d : Candidate Ω t.domainNF) : Set (Expr S) :=
  if Ω.profile t.domainNF ∈ C then d.val else Candidates.Top Ω t.domainNF

theorem testers_top (d : Candidate Ω t.domainNF) : t.testers d ⊆ Candidates.Top Ω t.domainNF := by
  unfold testers
  split
  · exact d.property.upper
  · exact Set.Subset.rfl

/-- Every raw tester and every matching payload has its own body Read.
This quantification is over all payloads, not only semantic realizers. -/
abbrev BodyReads := ∀ (n : Expr S), Ω.HasType n t.domainNF →
  (p : Option (RawValue (hw := hw) Ω C hno)) → PayloadFits Ω C hno t.domainNF p → Candidate Ω (t.targetNF n)

noncomputable def fibers (b : t.BodyReads) (n : Expr S) : Set (Set (Expr S)) :=
  if hn : Ω.HasType n t.domainNF then
    if Ω.profile (t.targetNF n) ∈ C then
      {U | ∃ p hp, U = (b n hn p hp).val}
    else {Candidates.Top Ω (t.targetNF n)}
  else ∅

theorem fibers_candidate (d : Candidate Ω t.domainNF) (b : t.BodyReads)
    {n : Expr S} (hn : n ∈ t.testers d) {U : Set (Expr S)} (hU : U ∈ t.fibers b n) :
    Candidates.IsCandidate Ω (t.bodyNF.instantiate n).normalForm U := by
  have ht := (t.testers_top d hn).1
  rw [← t.target_eq ht]
  simp only [fibers, ht, dite_true] at hU
  split_ifs at hU with hc
  · obtain ⟨p,hp,rfl⟩ := hU
    exact (b n ht p hp).property
  · have he : U = Candidates.Top Ω (t.targetNF n) := hU
    rw [he]
    exact Candidates.top_candidate

noncomputable def candidate (d : Candidate Ω t.domainNF) (b : t.BodyReads) :
    Candidate Ω (.pi t.domainNF t.bodyNF) :=
  ⟨Candidates.ProductTest Ω t.domainNF t.bodyNF (t.testers d) (t.fibers b),
    Candidates.productTest_candidate hw (t.testers_top d) (fun _ hn _ hU => t.fibers_candidate d b hn hU)⟩

theorem candidate_body (d : Candidate Ω t.domainNF) (b : t.BodyReads) {M n : Expr S}
    (hM : M ∈ (t.candidate d b).val) (hn : n ∈ t.testers d)
    (hc : Ω.profile (t.targetNF n) ∈ C)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno t.domainNF p) :
    Expr.app M n ∈ (b n (t.testers_top d hn).1 p hp).val := by
  apply hM.2 n hn
  simp only [fibers, (t.testers_top d hn).1, dite_true, hc, ite_true, if_true, Set.mem_ofPred_eq]
  exact ⟨p,hp,rfl⟩

theorem candidate_outside (d : Candidate Ω t.domainNF) (b : t.BodyReads) {M n : Expr S}
    (hM : M ∈ (t.candidate d b).val) (hn : n ∈ t.testers d)
    (hc : Ω.profile (t.targetNF n) ∉ C) :
    Expr.app M n ∈ Candidates.Top Ω (t.targetNF n) := by
  apply hM.2 n hn
  simp only [fibers, (t.testers_top d hn).1, dite_true, hc, ite_false, if_false, Set.mem_singleton_iff]
end ProductInstance
end ObservationValues
end PureTypeSystem

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Evaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Total observation operations. The minus lambda pack is provisional off the
representable behaviors; the finite-bound theorem proves that the evaluator
never takes that provisional branch. -/
namespace PureTypeSystem
universe u

namespace ActualPlain.Node
variable {S : Type u} {P : Specification S} {Ω : ContextTower P} {C : Set (Set S)}
@[ext] theorem ext {n m : ActualPlain.Node Ω C} (h : n.type = m.type) : n = m := by
  cases n; cases m; cases h; rfl
end ActualPlain.Node

namespace ObservationValues
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

namespace ActiveType
variable {Ω C}
abbrev plainNode (T : ActiveType Ω C) (hp : PlainLayer P C (Ω.profile T.type)) : ActualPlain.Node Ω C :=
  ⟨T.type, T.normal, T.sorted, hp⟩
omit [Fintype S] in
@[ext] theorem ext {T U : ActiveType Ω C} (h : T.type = U.type) : T = U := by
  cases T; cases U; cases h; rfl
end ActiveType

namespace Value
variable {Ω C hno}
def plain (n : ActualPlain.Node Ω C) (p : ActualPlain.Space (hw := hw) hno (Base Ω) n) :
    Value (hw := hw) Ω C hno n.type := ⟨.plain ⟨n,p⟩, rfl⟩

theorem plain_exists (n : ActualPlain.Node Ω C) (v : Value (hw := hw) Ω C hno n.type) :
    ∃ p, plain n p = v := by
  rcases v with ⟨v,hv⟩
  cases v with
  | plain p =>
    have he : p.1 = n := ActualPlain.Node.ext hv
    rcases p with ⟨m,p⟩
    dsimp at he
    subst m
    exact ⟨p,rfl⟩
  | plus p => exact False.elim (hv.1 n.plain)
  | minus p => exact False.elim (hv.1 n.plain)

noncomputable def asPlain (n : ActualPlain.Node Ω C) (v : Value (hw := hw) Ω C hno n.type) :
    ActualPlain.Space (hw := hw) hno (Base Ω) n := (plain_exists n v).choose

@[simp] theorem plain_asPlain (n : ActualPlain.Node Ω C) (v : Value (hw := hw) Ω C hno n.type) :
    plain n (asPlain n v) = v := (plain_exists n v).choose_spec

@[simp] theorem asPlain_plain (n : ActualPlain.Node Ω C) (p : ActualPlain.Space (hw := hw) hno (Base Ω) n) :
    asPlain n (plain n p) = p := by
  have he := congrArg Subtype.val (plain_asPlain n (plain n p))
  exact eq_of_heq (Sigma.mk.inj (RawValue.plain.inj he)).2

theorem plus_exists {T : Expr S} (hT : FreeLayer P C (Ω.profile T) false)
    (v : Value (hw := hw) Ω C hno T) : ∃ p, v.val = .plus p := by
  rcases v with ⟨v,hv⟩
  cases v with
  | plain p => exact False.elim (hT.1 (hv ▸ p.1.plain))
  | plus p => exact ⟨p,rfl⟩
  | minus p => exact False.elim (Bool.noConfusion (hT.sign_unique hv))

theorem minus_exists {T : Expr S} (hT : FreeLayer P C (Ω.profile T) true)
    (v : Value (hw := hw) Ω C hno T) : ∃ p, v.val = .minus p := by
  rcases v with ⟨v,hv⟩
  cases v with
  | plain p => exact False.elim (hT.1 (hv ▸ p.1.plain))
  | plus p => exact False.elim (Bool.noConfusion (hT.sign_unique hv))
  | minus p => exact ⟨p,rfl⟩

noncomputable def asPlus {T : Expr S} (hT : FreeLayer P C (Ω.profile T) false)
    (v : Value (hw := hw) Ω C hno T) : Plus (hw := hw) Ω C hno := (plus_exists hT v).choose
noncomputable def asMinus {T : Expr S} (hT : FreeLayer P C (Ω.profile T) true)
    (v : Value (hw := hw) Ω C hno T) : Minus (hw := hw) Ω C hno := (minus_exists hT v).choose

@[simp] theorem asPlus_spec {T : Expr S} (hT : FreeLayer P C (Ω.profile T) false)
    (v : Value (hw := hw) Ω C hno T) : v.val = .plus (asPlus hT v) := (plus_exists hT v).choose_spec
@[simp] theorem asMinus_spec {T : Expr S} (hT : FreeLayer P C (Ω.profile T) true)
    (v : Value (hw := hw) Ω C hno T) : v.val = .minus (asMinus hT v) := (minus_exists hT v).choose_spec
end Value

namespace ActualPlainKey
variable {Ω C hno}

/-- Decode a plain frame's unique optional domain coordinate. -/
noncomputable def payload {n : ActualPlain.Node Ω C} (a : ActualPlain.Key Ω C n)
    (p : (ActualPlain.schema hw).FrameParameters (ActualPlain.Space (hw := hw) hno (Base Ω)) a) :
    Option (RawValue (hw := hw) Ω C hno) :=
  if h : ActiveLayer P C (Ω.profile a.domain) then
    some (.plain ⟨a.domainNode hw h, p _ (by simp only [ActualPlain.schema, h, dite_true])⟩)
  else none

theorem payload_fits {n : ActualPlain.Node Ω C} (a : ActualPlain.Key Ω C n)
    (p : (ActualPlain.schema hw).FrameParameters (ActualPlain.Space (hw := hw) hno (Base Ω)) a) :
    PayloadFits Ω C hno a.domain (payload a p) := by
  unfold payload
  split
  · rfl
  · assumption

/-- Encode the matching typed plain payload without changing its tag. -/
noncomputable def parameters {n : ActualPlain.Node Ω C} (a : ActualPlain.Key Ω C n)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    (ActualPlain.schema hw).FrameParameters (ActualPlain.Space (hw := hw) hno (Base Ω)) a := by
  cases p with
  | none =>
    intro d hd
    exact False.elim (hp (ActualPlain.Schema.domain_eq hd).choose)
  | some v =>
    intro d hd
    apply Value.asPlain d
    refine ⟨v,?_⟩
    obtain ⟨ha,rfl⟩ := ActualPlain.Schema.domain_eq hd
    exact hp

@[simp] theorem payload_parameters {n : ActualPlain.Node Ω C} (a : ActualPlain.Key Ω C n)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    payload a (parameters a p hp) = p := by
  unfold payload
  split
  · rename_i ha
    cases p with
    | none => exact False.elim (hp ha)
    | some v =>
      simpa only [parameters, Value.plain] using
        congrArg (fun w : Value (hw := hw) Ω C hno a.domain => some w.val)
          (Value.plain_asPlain (a.domainNode hw ha) ⟨v,hp⟩)
  · rename_i ha
    cases p with
    | none => rfl
    | some v => exact False.elim (ha hp.active)

end ActualPlainKey

namespace FrameKey
variable {Ω C hno}
omit [Fintype S] in
@[ext] theorem ext {T : ActiveType Ω C} {a b : FrameKey Ω C T}
    (h : a.argument = b.argument) : a = b := by
  cases a with
  | mk D E ht q hn hh hact =>
    cases b with
    | mk D' E' ht' q' hn' hh' hact' =>
      obtain ⟨rfl,rfl⟩ := Expr.pi.inj (ht.symm.trans ht')
      cases h
      rfl

abbrev plainKey {T : ActiveType Ω C} (a : FrameKey Ω C T)
    (hT : PlainLayer P C (Ω.profile T.type)) : ActualPlain.Key Ω C (T.plainNode hT) :=
  ⟨a.domain,a.body,a.product,a.argument,a.normal,a.typed,a.active⟩

omit [Fintype S] in
theorem free_target {T : ActiveType Ω C} (a : FrameKey Ω C T) {sgn : Bool}
    (hT : FreeLayer P C (Ω.profile T.type) sgn)
    (ht : ¬ PlainLayer P C (Ω.profile (a.target hw).type)) :
    FreeLayer P C (Ω.profile (a.target hw).type) sgn := by
  rcases (a.target hw).active.classify with h | h | h
  · exact False.elim (ht h)
  · exact a.free_target_sign hw hT h ▸ h
  · exact a.free_target_sign hw hT h ▸ h
end FrameKey

/-- A represented minus behavior is packed without changing any observation. -/
noncomputable def packMinus
    (t : FreeObservations.Table (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω)
      (Option (PlainValue (hw := hw) Ω C hno)) (Plus (hw := hw) Ω C hno)) : Minus (hw := hw) Ω C hno :=
  if h : ∃ x, FreeObservations.behavior _ _ _ _ x = t then h.choose
  else FreeObservations.minusDefault _ _ (topBase Ω) none

theorem packMinus_spec
    (t : FreeObservations.Table (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω)
      (Option (PlainValue (hw := hw) Ω C hno)) (Plus (hw := hw) Ω C hno))
    (h : ∃ x, FreeObservations.behavior _ _ _ _ x = t) :
    FreeObservations.behavior _ _ _ _ (packMinus Ω C hno t) = t := by
  simp only [packMinus, h, dite_true]
  exact h.choose_spec

theorem packMinus_stage {n : Nat}
    (t : FreeObservations.Table (Expr S) (PlainValue (hw := hw) Ω C hno) (Base Ω)
      (Option (PlainValue (hw := hw) Ω C hno)) (Plus (hw := hw) Ω C hno))
    (h : ∃ x, FreeObservations.InStage n x ∧ FreeObservations.behavior _ _ _ _ x = t) :
    FreeObservations.InStage n (packMinus Ω C hno t) := by
  obtain ⟨x,hx,he⟩ := h
  have hp := packMinus_spec Ω C hno t ⟨x,he⟩
  have hh := FreeObservations.behavior_injective (topBase Ω) (none : Option (PlainValue (hw := hw) Ω C hno))
    (hp.trans he.symm)
  exact hh ▸ hx
end ObservationValues
end PureTypeSystem


namespace PureTypeSystem.ObservationValues
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

namespace Gate
variable {Ω C hno} {T : ActiveType Ω C} {q : Expr S}
variable {p : Option (RawValue (hw := hw) Ω C hno)} {exit : Bool}
noncomputable def frame (h : Gate Ω C hno T q p exit) : FrameKey Ω C T := h.choose

theorem argument (h : Gate Ω C hno T q p exit) : h.frame.argument = q := h.choose_spec.1
theorem payload (h : Gate Ω C hno T q p exit) : PayloadFits Ω C hno h.frame.domain p := h.choose_spec.2.1

theorem plain (h : Gate Ω C hno T q p true) :
    PlainLayer P C (Ω.profile (h.frame.target hw).type) := h.choose_spec.2.2.mpr rfl

theorem not_plain (h : Gate Ω C hno T q p false) :
    ¬ PlainLayer P C (Ω.profile (h.frame.target hw).type) := fun hp => Bool.noConfusion (h.choose_spec.2.2.mp hp)

theorem unique (h : Gate Ω C hno T q p exit) (a : FrameKey Ω C T) (ha : a.argument = q) :
    h.frame = a := FrameKey.ext (h.argument.trans ha.symm)
end Gate

abbrev LambdaAction (T : ActiveType Ω C) := (a : FrameKey Ω C T) →
  (p : Option (RawValue (hw := hw) Ω C hno)) → PayloadFits Ω C hno a.domain p →
  Value (hw := hw) Ω C hno (a.target hw).type

noncomputable def tagPlain (T : ActiveType Ω C) (hp : PlainLayer P C (Ω.profile T.type))
    (v : Value (hw := hw) Ω C hno T.type) : PlainValue (hw := hw) Ω C hno :=
  ⟨T.plainNode hp, Value.asPlain (T.plainNode hp) v⟩

theorem tagPlain_spec (T : ActiveType Ω C) (hp : PlainLayer P C (Ω.profile T.type))
    (v : Value (hw := hw) Ω C hno T.type) : RawValue.plain (tagPlain Ω C hno T hp v) = v.val :=
  congrArg Subtype.val (Value.plain_asPlain (T.plainNode hp) v)

/-- The actual plain prefix operation, with the unique optional payload. -/
noncomputable def plainLambda (T : ActiveType Ω C) (hp : PlainLayer P C (Ω.profile T.type))
    (act : LambdaAction (hw := hw) Ω C hno T) : Value (hw := hw) Ω C hno T.type := by
  let n := T.plainNode hp
  apply Value.plain n
  refine (ActualPlain.prefixEquiv (hw := hw) hno (Base Ω) n).symm ⟨topBase Ω, fun a p => ?_⟩
  let a' : FrameKey Ω C T := ⟨a.domain,a.body,a.product,a.argument,a.normal,a.typed,a.active⟩
  exact Value.asPlain (a.target hw)
    (act a' (ActualPlainKey.payload a p) (ActualPlainKey.payload_fits a p))

/-- The same gate is used for plus and minus exits; the opposite payload
space differs, but the exact plain target tag is always retained. -/
noncomputable def lambdaExit {X : Type u}
    (decode : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) X →
      Option (RawValue (hw := hw) Ω C hno))
    (T : ActiveType Ω C) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) X) :
    Option (PlainValue (hw := hw) Ω C hno) :=
  if h : Gate Ω C hno T a.1 (decode a.2) true then
    some (tagPlain Ω C hno (h.frame.target hw) h.plain (act h.frame (decode a.2) h.payload))
  else none

noncomputable def plusContinue (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.profile T.type) false) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : PlusFrame (hw := hw) Ω C hno) : Plus (hw := hw) Ω C hno :=
  if h : Gate Ω C hno T a.1 (plusPayload Ω C hno a.2) false then
    Value.asPlus (h.frame.free_target hT h.not_plain) (act h.frame _ h.payload)
  else FreeObservations.plusDefault _ _ (topBase Ω) none

noncomputable def minusContinue (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.profile T.type) true) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : MinusFrame (hw := hw) Ω C hno) : Minus (hw := hw) Ω C hno :=
  if h : Gate Ω C hno T a.1 (minusPayload Ω C hno a.2) false then
    Value.asMinus (h.frame.free_target hT h.not_plain) (act h.frame _ h.payload)
  else FreeObservations.minusDefault _ _ (topBase Ω) none

noncomputable def plusLambda (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.profile T.type) false) (act : LambdaAction (hw := hw) Ω C hno T) :
    Plus (hw := hw) Ω C hno where
  continuing
    | [] => topBase Ω
    | a :: as => (plusContinue Ω C hno T hT act a).continuing as
  exiting
    | ([], a) => lambdaExit Ω C hno (plusPayload Ω C hno) T act a
    | (a :: as, e) => (plusContinue Ω C hno T hT act a).exiting (as,e)

noncomputable def minusLambdaBehavior (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.profile T.type) true) (act : LambdaAction (hw := hw) Ω C hno T) :=
  FreeObservations.lambdaTable (topBase Ω) (minusContinue Ω C hno T hT act)
    (lambdaExit Ω C hno (minusPayload Ω C hno) T act)

noncomputable def lambdaValue (T : ActiveType Ω C) (act : LambdaAction (hw := hw) Ω C hno T) :
    Value (hw := hw) Ω C hno T.type := by
  by_cases hp : PlainLayer P C (Ω.profile T.type)
  · exact plainLambda Ω C hno T hp act
  · by_cases hf : FreeLayer P C (Ω.profile T.type) false
    · exact ⟨.plus (plusLambda Ω C hno T hf act),hf⟩
    · have hm : FreeLayer P C (Ω.profile T.type) true := by
        rcases T.active.classify with h | h | h
        · exact False.elim (hp h)
        · exact False.elim (hf h)
        · exact h
      exact ⟨.minus (packMinus Ω C hno (minusLambdaBehavior Ω C hno T hm act)),hm⟩

namespace FrameKey
variable {Ω C hno} {T : ActiveType Ω C} (a : FrameKey Ω C T)

noncomputable def plusParameter (hT : FreeLayer P C (Ω.profile T.type) false)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) (Minus (hw := hw) Ω C hno) := by
  cases p with
  | none => exact .none
  | some v =>
    cases v with
    | plain p => exact .plain p
    | minus m => exact .opposite m
    | plus v => exact False.elim (Bool.noConfusion (a.free_domain_sign hw hT hp))

noncomputable def minusParameter (hT : FreeLayer P C (Ω.profile T.type) true)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) (Plus (hw := hw) Ω C hno) := by
  cases p with
  | none => exact .none
  | some v =>
    cases v with
    | plain p => exact .plain p
    | plus m => exact .opposite m
    | minus v => exact False.elim (Bool.noConfusion (a.free_domain_sign hw hT hp))

@[simp] theorem plusPayload_parameter (hT : FreeLayer P C (Ω.profile T.type) false)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    plusPayload Ω C hno (a.plusParameter hT p hp) = p := by
  cases p with
  | none => rfl
  | some v =>
    cases v with
    | plain p => rfl
    | minus m => rfl
    | plus v => exact False.elim (Bool.noConfusion (a.free_domain_sign hw hT hp))

@[simp] theorem minusPayload_parameter (hT : FreeLayer P C (Ω.profile T.type) true)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    minusPayload Ω C hno (a.minusParameter hT p hp) = p := by
  cases p with
  | none => rfl
  | some v =>
    cases v with
    | plain p => rfl
    | plus m => rfl
    | minus v => exact False.elim (Bool.noConfusion (a.free_domain_sign hw hT hp))
end FrameKey

noncomputable def exitValue (T : ActiveType Ω C) (out : Option (PlainValue (hw := hw) Ω C hno)) :
    Value (hw := hw) Ω C hno T.type :=
  match out with
  | none => distinguished (hw := hw) Ω C hno T
  | some p => project (hw := hw) Ω C hno T (.plain p)

/-- Plain application, separated to keep dependent prefix casts abstract. -/
noncomputable def plainApply (T : ActiveType Ω C) (hT : PlainLayer P C (Ω.profile T.type))
    (v : Value (hw := hw) Ω C hno T.type) (a : FrameKey Ω C T)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    Value (hw := hw) Ω C hno (a.target hw).type := by
  let n := T.plainNode hT
  let a' := a.plainKey hT
  let ps := ActualPlainKey.parameters a' p hp
  exact Value.plain (a'.target hw)
    ((ActualPlain.prefixEquiv (hw := hw) hno (Base Ω) n (Value.asPlain n v)).2 a' ps)

/-- Exact application: plain next, free continue slice, or checked exit. -/
noncomputable def applyValue (T : ActiveType Ω C) (v : Value (hw := hw) Ω C hno T.type)
    (a : FrameKey Ω C T) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p) : Value (hw := hw) Ω C hno (a.target hw).type := by
  by_cases hT : PlainLayer P C (Ω.profile T.type)
  · exact plainApply Ω C hno T hT v a p hp
  · by_cases hF : FreeLayer P C (Ω.profile T.type) false
    · let f := Value.asPlus hF v
      let key : PlusFrame (hw := hw) Ω C hno := (a.argument, a.plusParameter hF p hp)
      by_cases hA : PlainLayer P C (Ω.profile (a.target hw).type)
      · exact exitValue Ω C hno (a.target hw) (f.exiting ([],key))
      · exact ⟨.plus (f.slice key), a.free_target hF hA⟩
    · have hM : FreeLayer P C (Ω.profile T.type) true := by
        rcases T.active.classify with h | h | h
        · exact False.elim (hT h)
        · exact False.elim (hF h)
        · exact h
      let f := Value.asMinus hM v
      let key : MinusFrame (hw := hw) Ω C hno := (a.argument, a.minusParameter hM p hp)
      by_cases hA : PlainLayer P C (Ω.profile (a.target hw).type)
      · exact exitValue Ω C hno (a.target hw) ((FreeObservations.behavior _ _ _ _ f).exiting ([],key))
      · exact ⟨.minus (FreeObservations.minusSlice f key), a.free_target hM hA⟩
end PureTypeSystem.ObservationValues


namespace PureTypeSystem
universe u

namespace ObservationValues
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

namespace Environment
variable {Ω C hno} {Γ : List (Expr S)} (e : Environment (hw := hw) Ω C hno Γ)

noncomputable abbrev actualType {M T : Expr S} (h : HasType P Γ M T) : ActualType Ω :=
  ⟨(T.subst e.images).normalForm, (ContextTower.HasType.subst h e.typed).actual_type hw⟩

noncomputable abbrev activeType {M T : Expr S} (h : HasType P Γ M T)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)) : ActiveType Ω C :=
  .ofActual (e.actualType h) ha

noncomputable abbrev actualExpression {M : Expr S} {s : S} (h : HasType P Γ M (.sort s)) : ActualType Ω :=
  ⟨(M.subst e.images).normalForm, (ContextTower.HasType.subst h e.typed).actual_expression hw⟩

theorem type_convert_eq {M T N U : Expr S} (hM : HasType P Γ M T)
    (hN : HasType P Γ N U) (hc : Converts T U) :
    (T.subst e.images).normalForm = (U.subst e.images).normalForm :=
  Expr.normalForm_converts ((ContextTower.HasType.subst hM e.typed).type_weaklyNormalizing hw)
    ((ContextTower.HasType.subst hN e.typed).type_weaklyNormalizing hw) (hc.subst _)

theorem expression_convert_eq {M T N U : Expr S} (hM : HasType P Γ M T)
    (hN : HasType P Γ N U) (hc : Converts M N) :
    (M.subst e.images).normalForm = (N.subst e.images).normalForm :=
  Expr.normalForm_converts ((ContextTower.HasType.subst hM e.typed).weaklyNormalizing hw)
    ((ContextTower.HasType.subst hN e.typed).weaklyNormalizing hw) (hc.subst _)
end Environment

namespace ProductInstance
variable {Ω C hno}
noncomputable def ofFormation {Γ : List (Expr S)} {D E : Expr S} {s : S}
    (hp : HasType P Γ (.pi D E) (.sort s)) (e : Environment (hw := hw) Ω C hno Γ) :
    ProductInstance (hw := hw) Ω C hno :=
  let h := hp.generation_pi
  { context := Γ
    domain := D
    body := E
    domainSort := h.choose
    bodySort := h.choose_spec.choose
    resultSort := h.choose_spec.choose_spec.choose
    domainTyping := h.choose_spec.choose_spec.choose_spec.1
    bodyTyping := h.choose_spec.choose_spec.choose_spec.2.1
    rule := h.choose_spec.choose_spec.choose_spec.2.2.1
    environment := e }

noncomputable def ofFunction {Γ : List (Expr S)} {f D E : Expr S}
    (hf : HasType P Γ f (.pi D E)) (e : Environment (hw := hw) Ω C hno Γ) :
    ProductInstance (hw := hw) Ω C hno :=
  ofFormation hf.product_type_sorted.choose_spec e

variable (t : ProductInstance (hw := hw) Ω C hno)

theorem frame_domain {T : ActiveType Ω C} (he : T.type = .pi t.domainNF t.bodyNF)
    (a : FrameKey Ω C T) : a.domain = t.domainNF := (Expr.pi.inj (a.product.symm.trans he)).1

theorem frame_body {T : ActiveType Ω C} (he : T.type = .pi t.domainNF t.bodyNF)
    (a : FrameKey Ω C T) : a.body = t.bodyNF := (Expr.pi.inj (a.product.symm.trans he)).2

noncomputable def frameEnvironment {T : ActiveType Ω C} (he : T.type = .pi t.domainNF t.bodyNF)
    (a : FrameKey Ω C T) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p) : Environment (hw := hw) Ω C hno (t.domain :: t.context) :=
  t.extend (t.frame_domain he a ▸ a.typed) p (t.frame_domain he a ▸ hp)

theorem frame_type {T : ActiveType Ω C} (he : T.type = .pi t.domainNF t.bodyNF)
    (a : FrameKey Ω C T) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p) :
    (t.body.subst (t.frameEnvironment he a p hp).images).normalForm = (a.target hw).type := by
  change t.targetNF a.argument = (a.body.instantiate a.argument).normalForm
  rw [t.target_eq (t.frame_domain he a ▸ a.typed), t.frame_body he a]

/-- A function's normalized argument frame, formed at the exact stored
product, not at an independently chosen derivation of that product. -/
noncomputable def argumentFrame {T : ActiveType Ω C} (he : T.type = .pi t.domainNF t.bodyNF)
    {n : Expr S} (hn : Ω.HasType n t.domainNF)
    (ha : ActiveLayer P C (Ω.profile (t.targetNF n))) : FrameKey Ω C T where
  domain := t.domainNF
  body := t.bodyNF
  product := he
  argument := n.normalForm
  normal := (Expr.normalForm_spec (hn.weaklyNormalizing hw)).2
  typed := hn.normalForm hw
  active := by
    have h1 : (t.bodyNF.instantiate n).normalForm = (t.bodyNF.instantiate n.normalForm).normalForm := by
      have hs := t.target_typed hn
      have hn' := hn.normalForm hw
      have hs' := t.target_typed hn'
      rw [t.target_eq hn] at hs
      rw [t.target_eq hn'] at hs'
      obtain ⟨s, hb⟩ := Ω.frame_target_sorted t.product_typed hn
      obtain ⟨s', hb'⟩ := Ω.frame_target_sorted t.product_typed hn'
      exact Expr.normalForm_converts (hb.weaklyNormalizing hw) (hb'.weaklyNormalizing hw)
        ((Expr.normalForm_spec (hn.weaklyNormalizing hw)).1.converts.instantiate_right t.bodyNF)
    rw [t.target_eq hn, h1] at ha
    simpa only [ContextTower.profile_normalForm] using ha

theorem argumentFrame_type {T : ActiveType Ω C} (he : T.type = .pi t.domainNF t.bodyNF)
    {n : Expr S} (hn : Ω.HasType n t.domainNF)
    (ha : ActiveLayer P C (Ω.profile (t.targetNF n))) :
    ((t.argumentFrame he hn ha).target hw).type = t.targetNF n := by
  change (t.bodyNF.instantiate n.normalForm).normalForm = t.targetNF n
  rw [t.target_eq hn]
  obtain ⟨s, hb⟩ := Ω.frame_target_sorted t.product_typed hn
  obtain ⟨s', hb'⟩ := Ω.frame_target_sorted t.product_typed (hn.normalForm hw)
  exact Expr.normalForm_converts (hb'.weaklyNormalizing hw) (hb.weaklyNormalizing hw)
    (.symm _ _ ((Expr.normalForm_spec (hn.weaklyNormalizing hw)).1.converts.instantiate_right t.bodyNF))
end ProductInstance
end ObservationValues
end PureTypeSystem


/-! Syntax recursion for Val/Read. `PreResult` uses the totalized minus pack;
the source semantics additionally needs the uniform finite-bound theorem,
which must rule out its fallback at every actual lambda. -/
namespace PureTypeSystem.ObservationValues
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

namespace PayloadFits
variable {Ω C hno} {T : Expr S} {p : Option (RawValue (hw := hw) Ω C hno)}
noncomputable def value (hp : PayloadFits Ω C hno T p) (ha : ActiveLayer P C (Ω.profile T)) :
    Value (hw := hw) Ω C hno T := by
  cases p with
  | none => exact False.elim (hp ha)
  | some v => exact ⟨v,hp⟩

theorem value_spec (hp : PayloadFits Ω C hno T p) (ha : ActiveLayer P C (Ω.profile T)) :
    some (hp.value ha).val = p := by
  cases p with
  | none => exact False.elim (hp ha)
  | some v => rfl
end PayloadFits

structure PreResult {Γ : List (Expr S)} (M T : Expr S) (e : Environment (hw := hw) Ω C hno Γ) where
  val : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm) →
    Value (hw := hw) Ω C hno (T.subst e.images).normalForm
  read : Candidate Ω (M.subst e.images).normalForm

namespace PreResult
variable {Ω C hno} {Γ : List (Expr S)} {M T : Expr S} {e : Environment (hw := hw) Ω C hno Γ}
noncomputable def parameter (r : PreResult Ω C hno M T e) : Option (RawValue (hw := hw) Ω C hno) :=
  if ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm) then some (r.val ha).val else none

theorem parameter_fits (r : PreResult Ω C hno M T e) :
    PayloadFits Ω C hno (T.subst e.images).normalForm r.parameter := by
  unfold parameter
  split
  · exact (r.val _).property
  · assumption

/-- The source base Read clause. For nonliteral expected types this extra
coordinate is unused; no additional semantic assertion is made about it. -/
noncomputable def baseRead (h : HasType P Γ M T)
    (v : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm) →
      Value (hw := hw) Ω C hno (T.subst e.images).normalForm) :
    Candidate Ω (M.subst e.images).normalForm :=
  if _hm : Ω.profile (M.subst e.images).normalForm ∈ C then
    if hs : ∃ s : S, T = .sort s ∧ ({s} : Set S) ∈ C then
      if ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm) then
        (RawValue.base Ω C hno (v ha).val) (e.actualExpression (hs.choose_spec.1 ▸ h))
      else ⟨_, Candidates.top_candidate⟩
    else ⟨_, Candidates.top_candidate⟩
  else ⟨_, Candidates.top_candidate⟩

noncomputable def baseResult (h : HasType P Γ M T)
    (v : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm) →
      Value (hw := hw) Ω C hno (T.subst e.images).normalForm) : PreResult Ω C hno M T e :=
  ⟨v, baseRead h v⟩

noncomputable def lookup {n : Nat} {A : Expr S} (h : HasType P Γ (.var n) T)
    (hd : Lookup Γ n A) (hc : Converts T A) (e : Environment (hw := hw) Ω C hno Γ) :
    PreResult Ω C hno (.var n) T e := by
  apply baseResult h
  intro ha
  have he : (T.subst e.images).normalForm = (A.subst e.images).normalForm :=
    e.type_convert_eq h (HasType.lookup h.valid hd) hc
  have hp := e.lawful n A hd
  rw [← he] at hp
  exact hp.value ha

noncomputable def sort {s t : S} (h : HasType P Γ (.sort s) T)
    (_ha : P.axioms s t) (_hc : Converts T (.sort t))
    (e : Environment (hw := hw) Ω C hno Γ) : PreResult Ω C hno (.sort s) T e where
  val ha := distinguished Ω C hno (e.activeType h ha)
  read := ⟨_, Candidates.top_candidate⟩

noncomputable abbrev productData {D E : Expr S} {a b c : S}
    (hd : HasType P Γ D (.sort a)) (hb : HasType P (D :: Γ) E (.sort b))
    (hr : P.rule a b c) (e : Environment (hw := hw) Ω C hno Γ) :
    ProductInstance (hw := hw) Ω C hno := ⟨Γ,D,E,a,b,c,hd,hb,hr,e⟩

noncomputable def productCandidate {D E : Expr S} {a b c : S}
    (hd : HasType P Γ D (.sort a)) (hb : HasType P (D :: Γ) E (.sort b))
    (hr : P.rule a b c)
    (ed : ∀ e : Environment (hw := hw) Ω C hno Γ, PreResult Ω C hno D (.sort a) e)
    (eb : ∀ e : Environment (hw := hw) Ω C hno (D :: Γ), PreResult Ω C hno E (.sort b) e)
    (e : Environment (hw := hw) Ω C hno Γ) : Candidate Ω (Expr.pi D E |>.subst e.images).normalForm := by
  let t := productData hd hb hr e
  let pc := t.candidate (ed e).read (fun n hn p hp => (eb (t.extend hn p hp)).read)
  exact ⟨pc.val,t.product_nf.symm ▸ pc.property⟩

noncomputable def product {D E : Expr S} {a b c : S} (h : HasType P Γ (.pi D E) T)
    (hd : HasType P Γ D (.sort a)) (hb : HasType P (D :: Γ) E (.sort b))
    (hr : P.rule a b c) (_hc : Converts T (.sort c))
    (ed : ∀ e : Environment (hw := hw) Ω C hno Γ, PreResult Ω C hno D (.sort a) e)
    (eb : ∀ e : Environment (hw := hw) Ω C hno (D :: Γ), PreResult Ω C hno E (.sort b) e)
    (e : Environment (hw := hw) Ω C hno Γ) : PreResult Ω C hno (.pi D E) T e := by
  let pc := productCandidate hd hb hr ed eb e
  refine ⟨?_, ?_⟩
  · intro ha
    if hh : ({c} : Set S) ∈ C ∧ Ω.profile (Expr.pi D E |>.subst e.images).normalForm ∈ C then
      exact withBase Ω C hno (e.activeType h ha)
        (Base.update Ω (topBase Ω) (e.actualExpression (.product hd hb hr)) pc)
    else exact distinguished Ω C hno (e.activeType h ha)
  · exact if Ω.profile (Expr.pi D E |>.subst e.images).normalForm ∈ C then pc
      else ⟨_, Candidates.top_candidate⟩

noncomputable def abstractionAction {D m E : Expr S} {s : S} (h : HasType P Γ (.lam D m) T)
    (hp : HasType P Γ (.pi D E) (.sort s)) (hc : Converts T (.pi D E))
    (eb : ∀ e : Environment (hw := hw) Ω C hno (D :: Γ), PreResult Ω C hno m E e)
    (e : Environment (hw := hw) Ω C hno Γ) (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)) :
    LambdaAction (hw := hw) Ω C hno (e.activeType h ha) := by
  let t := ProductInstance.ofFormation hp e
  let A := e.activeType h ha
  have he : A.type = .pi t.domainNF t.bodyNF := by
    exact (Expr.normalForm_converts ((ContextTower.HasType.subst h e.typed).type_weaklyNormalizing hw)
      ((ContextTower.HasType.subst hp e.typed).weaklyNormalizing hw) (hc.subst e.images)).trans t.product_nf
  intro k p hk
  let e' := t.frameEnvironment he k p hk
  have he' : (E.subst e'.images).normalForm = (k.target hw).type := t.frame_type he k p hk
  have ha' : ActiveLayer P C (Ω.profile (E.subst e'.images).normalForm) := he' ▸ (k.target hw).active
  exact ⟨((eb e').val ha').val, he' ▸ ((eb e').val ha').property⟩

noncomputable def abstraction {D m E : Expr S} {s : S} (h : HasType P Γ (.lam D m) T)
    (hp : HasType P Γ (.pi D E) (.sort s)) (hc : Converts T (.pi D E))
    (eb : ∀ e : Environment (hw := hw) Ω C hno (D :: Γ), PreResult Ω C hno m E e)
    (e : Environment (hw := hw) Ω C hno Γ) : PreResult Ω C hno (.lam D m) T e :=
  baseResult h fun ha => lambdaValue Ω C hno (e.activeType h ha) (abstractionAction h hp hc eb e ha)

noncomputable def applicationValue {f n D E : Expr S} (h : HasType P Γ (.app f n) T)
    (hf : HasType P Γ f (.pi D E)) (hn : HasType P Γ n D) (hc : Converts T (E.instantiate n))
    (ef : ∀ e : Environment (hw := hw) Ω C hno Γ, PreResult Ω C hno f (.pi D E) e)
    (en : ∀ e : Environment (hw := hw) Ω C hno Γ, PreResult Ω C hno n D e)
    (e : Environment (hw := hw) Ω C hno Γ) (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)) :
    Value (hw := hw) Ω C hno (T.subst e.images).normalForm := by
  let Ta := e.activeType h ha
  by_cases hF : ActiveLayer P C (Ω.profile (Expr.pi D E |>.subst e.images).normalForm)
  · let t := ProductInstance.ofFunction hf e
    let Fa := e.activeType hf hF
    have he : Fa.type = .pi t.domainNF t.bodyNF := t.product_nf
    have hn' : Ω.HasType (n.subst e.images) t.domainNF :=
      (ContextTower.HasType.subst hn e.typed).normalize_type hw
    have ht : (T.subst e.images).normalForm = t.targetNF (n.subst e.images) := by
      have hh := e.type_convert_eq h (HasType.application hf hn) hc
      simpa only [ProductInstance.targetNF, ProductInstance.rawTarget,
        t, ProductInstance.ofFunction, ProductInstance.ofFormation,
        ← Expr.instantiate_subst, Expr.instantiate_liftSub] using hh
    have ha' : ActiveLayer P C (Ω.profile (t.targetNF (n.subst e.images))) := ht ▸ ha
    let k := t.argumentFrame he hn' ha'
    have hk : (k.target hw).type = (T.subst e.images).normalForm :=
      (t.argumentFrame_type he hn' ha').trans ht.symm
    let v := applyValue Ω C hno Fa ((ef e).val hF) k (en e).parameter (en e).parameter_fits
    exact ⟨v.val, hk ▸ v.property⟩
  · exact distinguished Ω C hno Ta
noncomputable def application {f n D E : Expr S} (h : HasType P Γ (.app f n) T)
    (hf : HasType P Γ f (.pi D E)) (hn : HasType P Γ n D) (hc : Converts T (E.instantiate n))
    (ef : ∀ e : Environment (hw := hw) Ω C hno Γ, PreResult Ω C hno f (.pi D E) e)
    (en : ∀ e : Environment (hw := hw) Ω C hno Γ, PreResult Ω C hno n D e)
    (e : Environment (hw := hw) Ω C hno Γ) : PreResult Ω C hno (.app f n) T e :=
  baseResult h fun ha => applicationValue h hf hn hc ef en e ha
end PreResult

/-- Structural recursion retaining every stored role choice.
The annotation child at a lambda is immaterial to its observation value,
but is retained in the input tree for the fundamental normalization lemma.
Representability follows from the uniform finite-bound theorem. -/
noncomputable def preEvaluate {Γ : List (Expr S)} {M T : Expr S} (t : TypingTree P Γ M T) :
    ∀ e : Environment (hw := hw) Ω C hno Γ, PreResult Ω C hno M T e := by
  induction t with
  | var h hd hc => exact PreResult.lookup h hd hc
  | sort h ha hc => exact PreResult.sort h ha hc
  | product h d b hr hc ihd ihb => exact PreResult.product h d.typing b.typing hr hc ihd ihb
  | abstraction h d b hp hc ihd ihb => exact PreResult.abstraction h hp hc ihb
  | application h f a hc ihf iha => exact PreResult.application h f.typing a.typing hc ihf iha

end PureTypeSystem.ObservationValues

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Bounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.ObservationValues

section
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

namespace RawValue
variable {Ω C hno}

theorem level_fits {n : Nat} {T : Expr S} {v w : RawValue (hw := hw) Ω C hno}
    (he : LevelEq Ω C hno n v w) : Fits Ω C hno T v ↔ Fits Ω C hno T w := by
  cases v <;> cases w <;> try exact False.elim he
  · exact he ▸ Iff.rfl
  · rfl
  · rfl

theorem level_eq_of_plain {n : Nat} {T : Expr S} (hT : PlainLayer P C (Ω.profile T))
    {v w : RawValue (hw := hw) Ω C hno} (hv : Fits Ω C hno T v)
    (he : LevelEq Ω C hno n v w) : v = w := by
  cases v with
  | plus p => exact False.elim (hv.1 hT)
  | minus p => exact False.elim (hv.1 hT)
  | plain p =>
    cases w with
    | plain q => exact congrArg RawValue.plain he
    | plus _ | minus _ => exact False.elim he

theorem bounded_of_not_minus {n : Nat} {T : Expr S}
    (hT : ¬ FreeLayer P C (Ω.profile T) true)
    {v : RawValue (hw := hw) Ω C hno} (hv : Fits Ω C hno T v) : Bounded Ω C hno n v := by
  cases v with
  | plain _ | plus _ => trivial
  | minus _ => exact False.elim (hT hv)
end RawValue

namespace Parameter
variable {Ω C hno}

theorem level_fits {n : Nat} {T : Expr S} {p q : Option (RawValue (hw := hw) Ω C hno)}
    (he : LevelEq Ω C hno n p q) : PayloadFits Ω C hno T p ↔ PayloadFits Ω C hno T q := by
  cases p <;> cases q <;> try exact False.elim he
  · rfl
  · exact RawValue.level_fits he

theorem bounded_of_not_minus {n : Nat} {T : Expr S}
    (hT : ¬ FreeLayer P C (Ω.profile T) true)
    {p : Option (RawValue (hw := hw) Ω C hno)} (hp : PayloadFits Ω C hno T p) : Bounded Ω C hno n p := by
  intro v hv
  subst p
  exact RawValue.bounded_of_not_minus hT hp

theorem bounded_none (n : Nat) : Bounded (hw := hw) Ω C hno n none := fun _ h => by cases h
end Parameter

namespace Value
variable {Ω C hno}
theorem level_asPlus {n : Nat} {T : Expr S} (hT : FreeLayer P C (Ω.profile T) false)
    {v w : Value (hw := hw) Ω C hno T}
    (he : RawValue.LevelEq Ω C hno n v.val w.val) :
    FreeObservations.Agree n (asPlus hT v) (asPlus hT w) := by
  rw [asPlus_spec hT v, asPlus_spec hT w] at he
  exact he

theorem level_asMinus {n : Nat} {T : Expr S} (hT : FreeLayer P C (Ω.profile T) true)
    {v w : Value (hw := hw) Ω C hno T}
    (he : RawValue.LevelEq Ω C hno n v.val w.val) : asMinus hT v = asMinus hT w := by
  rw [asMinus_spec hT v, asMinus_spec hT w] at he
  exact he

theorem bounded_asMinus {n : Nat} {T : Expr S} (hT : FreeLayer P C (Ω.profile T) true)
    {v : Value (hw := hw) Ω C hno T} (hv : RawValue.Bounded Ω C hno n v.val) :
    FreeObservations.InStage n (asMinus hT v) := by
  rw [asMinus_spec hT v] at hv
  exact hv
end Value

theorem distinguished_bounded (T : ActiveType Ω C) :
    RawValue.Bounded Ω C hno 1 (distinguished (hw := hw) Ω C hno T).val := by
  unfold distinguished
  split
  · trivial
  · split
    · trivial
    · exact ⟨_,rfl⟩

theorem withBase_bounded (T : ActiveType Ω C) (b : Base Ω) :
    RawValue.Bounded Ω C hno 1 (withBase (hw := hw) Ω C hno T b).val := by
  unfold withBase
  split
  · trivial
  · split
    · trivial
    · exact ⟨_,rfl⟩

namespace Gate
variable {Ω C hno}
theorem level_iff {n : Nat} {T : ActiveType Ω C} {q : Expr S} {e : Bool}
    {p p' : Option (RawValue (hw := hw) Ω C hno)} (he : Parameter.LevelEq Ω C hno n p p') :
    Gate Ω C hno T q p e ↔ Gate Ω C hno T q p' e := by
  constructor
  · rintro ⟨a,ha,hp,hf⟩
    exact ⟨a,ha,(Parameter.level_fits he).mp hp,hf⟩
  · rintro ⟨a,ha,hp,hf⟩
    exact ⟨a,ha,(Parameter.level_fits he).mpr hp,hf⟩
end Gate

theorem plusPayload_bounded {n : Nat} (a : PlusFrame (hw := hw) Ω C hno)
    (ha : FreeObservations.FrameBound n a) : Parameter.Bounded Ω C hno n (plusPayload Ω C hno a.2) := by
  rcases a with ⟨q,p⟩
  cases p with
  | none => exact Parameter.bounded_none n
  | plain p => intro v hv; cases hv; trivial
  | opposite p => intro v hv; cases hv; exact ha p rfl

theorem minusPayload_bounded (n : Nat) (a : MinusFrame (hw := hw) Ω C hno) :
    Parameter.Bounded Ω C hno n (minusPayload Ω C hno a.2) := by
  rcases a with ⟨q,p⟩
  cases p with
  | none => exact Parameter.bounded_none n
  | plain p | opposite p => intro v hv; cases hv; trivial

theorem minusFrame_restrict {n : Nat} {a a' : MinusFrame (hw := hw) Ω C hno}
    (ha : FreeObservations.mapFrame (FreeObservations.restrict _ _ _ _ n) a =
      FreeObservations.mapFrame (FreeObservations.restrict _ _ _ _ n) a') :
    a.1 = a'.1 ∧ Parameter.LevelEq Ω C hno n (minusPayload Ω C hno a.2) (minusPayload Ω C hno a'.2) := by
  rcases a with ⟨q,p⟩
  rcases a' with ⟨q',p'⟩
  have hh := Prod.mk.inj ha
  refine ⟨hh.1,?_⟩
  cases p <;> cases p' <;> dsimp only [FreeObservations.Payload.map, minusPayload,
    Parameter.LevelEq, RawValue.LevelEq] at hh ⊢
  all_goals first | exact True.intro | exact FreeObservations.Payload.plain.inj hh.2 |
    exact FreeObservations.Payload.opposite.inj hh.2 | cases hh.2

/-- The local induction hypotheses used at a lambda. -/
def ActionBound (T : ActiveType Ω C) (k l : Nat) (act : LambdaAction (hw := hw) Ω C hno T) : Prop :=
  ∀ a p hp, Parameter.Bounded Ω C hno k p → RawValue.Bounded Ω C hno l (act a p hp).val

def ActionRelated (T : ActiveType Ω C) (k l : Nat)
    (act act' : LambdaAction (hw := hw) Ω C hno T) : Prop :=
  ∀ a p p' hp hp', Parameter.Bounded Ω C hno k p → Parameter.Bounded Ω C hno k p' →
    Parameter.LevelEq Ω C hno l p p' → RawValue.LevelEq Ω C hno k (act a p hp).val (act' a p' hp').val

namespace LambdaAction
variable {Ω C hno}
theorem frame_congr {T : ActiveType Ω C} (act : LambdaAction (hw := hw) Ω C hno T)
    {a b : FrameKey Ω C T} (he : a = b) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p) (hq : PayloadFits Ω C hno b.domain p) :
    (act a p hp).val = (act b p hq).val := by
  cases he
  rfl
end LambdaAction

namespace ActionRelated
variable {Ω C hno}
theorem gates {T : ActiveType Ω C} {k l : Nat} {act act' : LambdaAction (hw := hw) Ω C hno T}
    (hr : ActionRelated Ω C hno T k l act act')
    {q q' : Expr S} (hq : q = q') {ex : Bool}
    {p p' : Option (RawValue (hw := hw) Ω C hno)}
    (h : Gate Ω C hno T q p ex) (h' : Gate Ω C hno T q' p' ex)
    (hb : Parameter.Bounded Ω C hno k p) (hb' : Parameter.Bounded Ω C hno k p')
    (he : Parameter.LevelEq Ω C hno l p p') :
    RawValue.LevelEq Ω C hno k (act h.frame p h.payload).val (act' h'.frame p' h'.payload).val := by
  have hf : h.frame = h'.frame := FrameKey.ext (h.argument.trans (hq.trans h'.argument.symm))
  have hp' : PayloadFits Ω C hno h.frame.domain p' := hf.symm ▸ h'.payload
  have hh := hr h.frame p p' h.payload hp' hb hb' he
  rw [LambdaAction.frame_congr act' hf p' hp' h'.payload] at hh
  exact hh
end ActionRelated

theorem minusContinue_bounded {T : ActiveType Ω C}
    (hT : FreeLayer P C (Ω.profile T.type) true) {k l : Nat} (hl : 1 ≤ l)
    {act : LambdaAction (hw := hw) Ω C hno T} (hb : ActionBound Ω C hno T k l act)
    (a : MinusFrame (hw := hw) Ω C hno) :
    FreeObservations.InStage l (minusContinue Ω C hno T hT act a) := by
  unfold minusContinue
  split
  · exact Value.bounded_asMinus _ (hb _ _ _ (minusPayload_bounded Ω C hno k a))
  · exact FreeObservations.InStage.mono hl ⟨_,rfl⟩

theorem minusContinue_level {T : ActiveType Ω C}
    (hT : FreeLayer P C (Ω.profile T.type) true) {k l : Nat}
    {act act' : LambdaAction (hw := hw) Ω C hno T} (hr : ActionRelated Ω C hno T k l act act')
    {a a' : MinusFrame (hw := hw) Ω C hno}
    (ha : FreeObservations.mapFrame (FreeObservations.restrict _ _ _ _ l) a =
      FreeObservations.mapFrame (FreeObservations.restrict _ _ _ _ l) a') :
    minusContinue Ω C hno T hT act a = minusContinue Ω C hno T hT act' a' := by
  have hh := minusFrame_restrict Ω C hno ha
  have hg : Gate Ω C hno T a.1 (minusPayload Ω C hno a.2) false ↔
      Gate Ω C hno T a'.1 (minusPayload Ω C hno a'.2) false := by
    rw [hh.1]
    exact Gate.level_iff hh.2
  unfold minusContinue
  by_cases h : Gate Ω C hno T a.1 (minusPayload Ω C hno a.2) false
  · have h' := hg.mp h
    rw [dite_eq_left h,dite_eq_left h']
    have he := hr.gates hh.1 h h' (minusPayload_bounded Ω C hno k a)
      (minusPayload_bounded Ω C hno k a') hh.2
    rw [Value.asMinus_spec (h.frame.free_target hT h.not_plain) (act _ _ _),
      Value.asMinus_spec (h'.frame.free_target hT h'.not_plain) (act' _ _ _)] at he
    exact he
  · rw [dite_eq_right h,dite_eq_right (mt hg.mpr h)]

theorem lambdaExit_level {X : Type u}
    (decode : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) X →
      Option (RawValue (hw := hw) Ω C hno))
    {T : ActiveType Ω C} {k l : Nat} {act act' : LambdaAction (hw := hw) Ω C hno T}
    (hr : ActionRelated Ω C hno T k l act act')
    {a a' : FreeObservations.Frame (Expr S) (PlainValue (hw := hw) Ω C hno) X}
    (hq : a.1 = a'.1) (hb : Parameter.Bounded Ω C hno k (decode a.2))
    (hb' : Parameter.Bounded Ω C hno k (decode a'.2))
    (he : Parameter.LevelEq Ω C hno l (decode a.2) (decode a'.2)) :
    lambdaExit Ω C hno decode T act a = lambdaExit Ω C hno decode T act' a' := by
  have hg : Gate Ω C hno T a.1 (decode a.2) true ↔ Gate Ω C hno T a'.1 (decode a'.2) true := by
    rw [hq]
    exact Gate.level_iff he
  unfold lambdaExit
  by_cases h : Gate Ω C hno T a.1 (decode a.2) true
  · have h' := hg.mp h
    rw [dite_eq_left h,dite_eq_left h']
    have hh := hr.gates hq h h' hb hb' he
    rw [← tagPlain_spec Ω C hno (h.frame.target hw) h.plain (act _ _ _),
      ← tagPlain_spec Ω C hno (h'.frame.target hw) h'.plain (act' _ _ _)] at hh
    exact congrArg some hh
  · rw [dite_eq_right h,dite_eq_right (mt hg.mpr h)]

/-- Uniform body estimates prove the *exact* minus lambda table is in the
colimit, so no fallback in `packMinus` is used. -/
theorem minusLambda_representable {T : ActiveType Ω C}
    (hT : FreeLayer P C (Ω.profile T.type) true) {k l : Nat} (hl : 1 ≤ l)
    {act : LambdaAction (hw := hw) Ω C hno T} (hb : ActionBound Ω C hno T k l act)
    (hr : ActionRelated Ω C hno T k l act act) :
    ∃ x, FreeObservations.InStage (l+1) x ∧
      FreeObservations.behavior _ _ _ _ x = minusLambdaBehavior Ω C hno T hT act := by
  apply FreeObservations.lambdaTable_representable (topBase Ω) none l
  · intro a
    exact (minusContinue_bounded Ω C hno hT hl hb a).mono (Nat.le_succ l)
  · intro a a' ha
    exact minusContinue_level Ω C hno hT hr ha
  · intro a a' ha
    have hh := minusFrame_restrict Ω C hno ha
    exact lambdaExit_level Ω C hno (minusPayload Ω C hno) hr hh.1
      (minusPayload_bounded Ω C hno k a) (minusPayload_bounded Ω C hno k a') hh.2

namespace Value
variable {Ω C hno}
theorem level_asPlain {n : Nat} (T : ActualPlain.Node Ω C)
    {v w : Value (hw := hw) Ω C hno T.type}
    (he : RawValue.LevelEq Ω C hno n v.val w.val) : asPlain T v = asPlain T w := by
  have hh : v = w := Subtype.ext (RawValue.level_eq_of_plain T.plain v.property he)
  exact congrArg (asPlain T) hh
end Value

namespace ActualPlainKey
variable {Ω C hno}
theorem payload_bounded {T : ActualPlain.Node Ω C} (a : ActualPlain.Key Ω C T)
    (p : (ActualPlain.schema hw).FrameParameters (ActualPlain.Space (hw := hw) hno (Base Ω)) a)
    (k : Nat) : Parameter.Bounded Ω C hno k (payload a p) := by
  unfold payload
  split
  · intro v hv
    cases hv
    trivial
  · exact Parameter.bounded_none k
end ActualPlainKey

theorem plainLambda_level {T : ActiveType Ω C} (hT : PlainLayer P C (Ω.profile T.type))
    {k l : Nat} {act act' : LambdaAction (hw := hw) Ω C hno T}
    (hr : ActionRelated Ω C hno T k l act act') :
    RawValue.LevelEq Ω C hno k (plainLambda Ω C hno T hT act).val
      (plainLambda Ω C hno T hT act').val := by
  unfold plainLambda
  change Sigma.mk _ _ = Sigma.mk _ _
  congr 1
  apply congrArg (ActualPlain.prefixEquiv (hw := hw) hno (Base Ω) (T.plainNode hT)).symm
  apply Prod.ext
  · rfl
  funext a p
  apply Value.level_asPlain
  exact hr _ _ _ _ _ (ActualPlainKey.payload_bounded a p k)
    (ActualPlainKey.payload_bounded a p k) (Parameter.level_refl l _)

theorem plusContinue_level {T : ActiveType Ω C}
    (hT : FreeLayer P C (Ω.profile T.type) false) {k l : Nat}
    {act act' : LambdaAction (hw := hw) Ω C hno T} (hr : ActionRelated Ω C hno T k l act act')
    (a : PlusFrame (hw := hw) Ω C hno) (ha : FreeObservations.FrameBound k a) :
    FreeObservations.Agree k (plusContinue Ω C hno T hT act a) (plusContinue Ω C hno T hT act' a) := by
  unfold plusContinue
  split
  · exact Value.level_asPlus _ (hr _ _ _ _ _ (plusPayload_bounded Ω C hno a ha)
      (plusPayload_bounded Ω C hno a ha) (Parameter.level_refl l _))
  · exact .refl _ _

theorem plusLambda_level {T : ActiveType Ω C}
    (hT : FreeLayer P C (Ω.profile T.type) false) {k l : Nat}
    {act act' : LambdaAction (hw := hw) Ω C hno T} (hr : ActionRelated Ω C hno T k l act act') :
    FreeObservations.Agree k (plusLambda Ω C hno T hT act) (plusLambda Ω C hno T hT act') := by
  apply FreeObservations.Agree.of_observations
  · intro as has
    cases as with
    | nil => rfl
    | cons a as =>
      exact (plusContinue_level Ω C hno hT hr a (has a List.mem_cons_self)).continuing
        (fun x hx => has x (List.mem_cons_of_mem _ hx))
  · rintro ⟨as,e⟩ ⟨has,hes⟩
    cases as with
    | nil =>
      exact lambdaExit_level Ω C hno (plusPayload Ω C hno) hr rfl
        (plusPayload_bounded Ω C hno e hes) (plusPayload_bounded Ω C hno e hes) (Parameter.level_refl l _)
    | cons a as =>
      exact (plusContinue_level Ω C hno hT hr a (has a List.mem_cons_self)).exiting
        ⟨fun x hx => has x (List.mem_cons_of_mem _ hx),hes⟩

theorem minusLambdaBehavior_level {T : ActiveType Ω C}
    (hT : FreeLayer P C (Ω.profile T.type) true) {k l : Nat}
    {act act' : LambdaAction (hw := hw) Ω C hno T} (hr : ActionRelated Ω C hno T k l act act') :
    minusLambdaBehavior Ω C hno T hT act = minusLambdaBehavior Ω C hno T hT act' := by
  unfold minusLambdaBehavior
  congr 1
  · funext a
    exact minusContinue_level Ω C hno hT hr rfl
  · funext a
    exact lambdaExit_level Ω C hno (minusPayload Ω C hno) hr rfl
      (minusPayload_bounded Ω C hno k a) (minusPayload_bounded Ω C hno k a) (Parameter.level_refl l _)

theorem lambdaValue_bounded {T : ActiveType Ω C} {k l : Nat} (hl : 1 ≤ l)
    {act : LambdaAction (hw := hw) Ω C hno T} (hb : ActionBound Ω C hno T k l act)
    (hr : ActionRelated Ω C hno T k l act act) :
    RawValue.Bounded Ω C hno (l+1) (lambdaValue Ω C hno T act).val := by
  unfold lambdaValue
  split
  · trivial
  · split
    · trivial
    · exact packMinus_stage Ω C hno _ (minusLambda_representable Ω C hno _ hl hb hr)

theorem lambdaValue_level {T : ActiveType Ω C} {k l : Nat}
    {act act' : LambdaAction (hw := hw) Ω C hno T} (hr : ActionRelated Ω C hno T k l act act') :
    RawValue.LevelEq Ω C hno k (lambdaValue Ω C hno T act).val (lambdaValue Ω C hno T act').val := by
  unfold lambdaValue
  split
  · exact plainLambda_level Ω C hno _ hr
  · split
    · exact plusLambda_level Ω C hno _ hr
    · exact congrArg (packMinus Ω C hno) (minusLambdaBehavior_level Ω C hno _ hr)

namespace RawValue
variable {Ω C hno}
theorem level_eq_of_not_plus {n : Nat} {T : Expr S} (hT : ¬ FreeLayer P C (Ω.profile T) false)
    {v w : RawValue (hw := hw) Ω C hno} (hv : Fits Ω C hno T v)
    (he : LevelEq Ω C hno n v w) : v = w := by
  cases v <;> cases w <;> dsimp only [LevelEq] at he
  all_goals first | exact False.elim he | exact False.elim (hT hv) |
    exact congrArg RawValue.plain he | exact congrArg RawValue.minus he
end RawValue

namespace Parameter
variable {Ω C hno}
theorem level_eq_of_not_plus {n : Nat} {T : Expr S} (hT : ¬ FreeLayer P C (Ω.profile T) false)
    {p q : Option (RawValue (hw := hw) Ω C hno)} (hp : PayloadFits Ω C hno T p)
    (he : LevelEq Ω C hno n p q) : p = q := by
  cases p <;> cases q
  · rfl
  · exact False.elim he
  · exact False.elim he
  · exact congrArg some (RawValue.level_eq_of_not_plus hT hp he)
end Parameter

theorem minusFrame_restrict_of_level {n : Nat} {a a' : MinusFrame (hw := hw) Ω C hno}
    (hq : a.1 = a'.1)
    (he : Parameter.LevelEq Ω C hno n (minusPayload Ω C hno a.2) (minusPayload Ω C hno a'.2)) :
    FreeObservations.mapFrame (FreeObservations.restrict _ _ _ _ n) a =
      FreeObservations.mapFrame (FreeObservations.restrict _ _ _ _ n) a' := by
  rcases a with ⟨q,p⟩
  rcases a' with ⟨q',p'⟩
  cases p <;> cases p' <;> dsimp only [minusPayload,Parameter.LevelEq,RawValue.LevelEq] at he
  all_goals first | exact False.elim he |
    exact Prod.ext hq rfl |
    exact Prod.ext hq (congrArg FreeObservations.Payload.plain he) |
    exact Prod.ext hq (congrArg FreeObservations.Payload.opposite he)

namespace FrameKey
variable {Ω C hno} {T : ActiveType Ω C} (a : FrameKey Ω C T)
theorem plusParameter_bound (hT : FreeLayer P C (Ω.profile T.type) false)
    {n : Nat} (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p)
    (hb : Parameter.Bounded Ω C hno n p) :
    FreeObservations.FrameBound n (a.argument,a.plusParameter hT p hp) := by
  cases p with
  | none => intro x hx; cases hx
  | some v =>
    cases v with
    | plain p => intro x hx; cases hx
    | plus p => exact False.elim (Bool.noConfusion (a.free_domain_sign hw hT hp))
    | minus p =>
      intro x hx
      have hh : p = x := FreeObservations.Payload.opposite.inj hx
      exact hh ▸ hb _ rfl

theorem minusParameter_level (hT : FreeLayer P C (Ω.profile T.type) true)
    {n : Nat} (p p' : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p) (hp' : PayloadFits Ω C hno a.domain p')
    (he : Parameter.LevelEq Ω C hno n p p') :
    FreeObservations.mapFrame (FreeObservations.restrict _ _ _ _ n) (a.argument,a.minusParameter hT p hp) =
      FreeObservations.mapFrame (FreeObservations.restrict _ _ _ _ n) (a.argument,a.minusParameter hT p' hp') := by
  apply minusFrame_restrict_of_level Ω C hno
  · rfl
  · simpa only [minusPayload_parameter] using he
end FrameKey

theorem applyValue_bounded {T : ActiveType Ω C} {n : Nat} (v : Value (hw := hw) Ω C hno T.type)
    (hv : RawValue.Bounded Ω C hno n v.val) (a : FrameKey Ω C T)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    RawValue.Bounded Ω C hno n (applyValue Ω C hno T v a p hp).val := by
  unfold applyValue
  split
  · trivial
  · split
    · split
      · rename_i ht
        exact RawValue.bounded_of_not_minus (fun h => h.1 ht) (exitValue Ω C hno _ _).property
      · trivial
    · split
      · rename_i ht
        exact RawValue.bounded_of_not_minus (fun h => h.1 ht) (exitValue Ω C hno _ _).property
      · exact FreeObservations.inStage_minusSlice (topBase Ω) none (Value.bounded_asMinus _ hv) _

theorem applyValue_level {T : ActiveType Ω C} {k j r : Nat}
    (v v' : Value (hw := hw) Ω C hno T.type) (hv : RawValue.Bounded Ω C hno j v.val)
    (hvv : RawValue.LevelEq Ω C hno (max k r) v.val v'.val) (a : FrameKey Ω C T)
    (p p' : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p) (hp' : PayloadFits Ω C hno a.domain p')
    (hb : Parameter.Bounded Ω C hno r p) (hpp : Parameter.LevelEq Ω C hno j p p') :
    RawValue.LevelEq Ω C hno k (applyValue Ω C hno T v a p hp).val
      (applyValue Ω C hno T v' a p' hp').val := by
  unfold applyValue
  by_cases hT : PlainLayer P C (Ω.profile T.type)
  · rw [dite_eq_left hT,dite_eq_left hT]
    have hvv' : v = v' := Subtype.ext (RawValue.level_eq_of_plain hT v.property hvv)
    have hpp' : p = p' := Parameter.level_eq_of_not_plus
      (fun hf => hf.1 (a.plain_domain hw hT hf.active)) hp hpp
    subst v'
    subst p'
    exact RawValue.level_refl k _
  · rw [dite_eq_right hT,dite_eq_right hT]
    by_cases hF : FreeLayer P C (Ω.profile T.type) false
    · rw [dite_eq_left hF,dite_eq_left hF]
      have hpp' : p = p' := Parameter.level_eq_of_not_plus
        (fun hf => Bool.noConfusion (a.free_domain_sign hw hF hf)) hp hpp
      subst p'
      have hh := Value.level_asPlus hF hvv
      have ha := (a.plusParameter_bound hF p hp hb).mono (le_max_right k r)
      split
      · have he := hh.exiting (as := ([],(a.argument,a.plusParameter hF p hp)))
          ⟨fun x hx => False.elim (List.not_mem_nil hx),ha⟩
        dsimp only
        rw [he]
        exact RawValue.level_refl k _
      · exact hh.slice (le_max_left k r) _ ha
    · rw [dite_eq_right hF,dite_eq_right hF]
      have hM : FreeLayer P C (Ω.profile T.type) true := by
        rcases T.active.classify with hh | hh | hh
        · exact False.elim (hT hh)
        · exact False.elim (hF hh)
        · exact hh
      have hh := Value.level_asMinus hM hvv
      have hs := (Value.bounded_asMinus hM hv).mono (Nat.le_succ j)
      have ha := a.minusParameter_level hM p p' hp hp' hpp
      split
      · dsimp only
        rw [← hh]
        have he := FreeObservations.minusExit_eq_of_restrict (topBase Ω) none hs ha
        rw [he]
        exact RawValue.level_refl k _
      · change FreeObservations.minusSlice _ _ = FreeObservations.minusSlice _ _
        rw [← hh]
        exact FreeObservations.minusSlice_eq_of_restrict (topBase Ω) none hs ha

namespace Environment
variable {Ω C hno} {Γ : List (Expr S)}

theorem level_cons {e f : Environment (hw := hw) Ω C hno Γ} {k : Nat}
    (he : e.LevelEq k f) {A a b : Expr S} (ha : Ω.HasType a (A.subst e.images))
    (hb : Ω.HasType b (A.subst f.images)) (hab : Converts a b)
    (p q : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno (A.subst e.images).normalForm p)
    (hq : PayloadFits Ω C hno (A.subst f.images).normalForm q)
    (hpq : Parameter.LevelEq Ω C hno k p q) :
    (e.cons ha p hp).LevelEq k (f.cons hb q hq) := by
  constructor
  · intro n hn
    cases n with
    | zero => exact hab
    | succ n => exact he.1 n (Nat.lt_of_succ_lt_succ hn)
  · intro n hn
    cases n with
    | zero => exact hpq
    | succ n => exact he.2 n (Nat.lt_of_succ_lt_succ hn)
end Environment

namespace Value
variable {Ω C hno}
@[simp] theorem cast_val {T U : Expr S} (h : T = U) (v : Value (hw := hw) Ω C hno T) :
    (h ▸ v).val = v.val := by subst U; rfl
end Value

theorem lambdaValue_level_of_type_eq {T U : ActiveType Ω C} (hTU : T.type = U.type)
    {k l : Nat} (act : LambdaAction (hw := hw) Ω C hno T)
    (act' : LambdaAction (hw := hw) Ω C hno U)
    (hr : ∀ (a : FrameKey Ω C T) (a' : FrameKey Ω C U), a.argument = a'.argument →
      ∀ p p' hp hp', Parameter.Bounded Ω C hno k p → Parameter.Bounded Ω C hno k p' →
      Parameter.LevelEq Ω C hno l p p' →
      RawValue.LevelEq Ω C hno k (act a p hp).val (act' a' p' hp').val) :
    RawValue.LevelEq Ω C hno k (lambdaValue Ω C hno T act).val (lambdaValue Ω C hno U act').val := by
  have hu := ActiveType.ext hTU
  subst U
  exact lambdaValue_level Ω C hno (fun a p p' hp hp' hb hb' he => hr a a rfl p p' hp hp' hb hb' he)

theorem applyValue_level_of_type_eq {T U : ActiveType Ω C} (hTU : T.type = U.type)
    {k j r : Nat} (v : Value (hw := hw) Ω C hno T.type) (v' : Value (hw := hw) Ω C hno U.type)
    (hv : RawValue.Bounded Ω C hno j v.val)
    (hvv : RawValue.LevelEq Ω C hno (max k r) v.val v'.val)
    (a : FrameKey Ω C T) (a' : FrameKey Ω C U) (hq : a.argument = a'.argument)
    (p p' : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p) (hp' : PayloadFits Ω C hno a'.domain p')
    (hb : Parameter.Bounded Ω C hno r p) (hpp : Parameter.LevelEq Ω C hno j p p') :
    RawValue.LevelEq Ω C hno k (applyValue Ω C hno T v a p hp).val
      (applyValue Ω C hno U v' a' p' hp').val := by
  have hu := ActiveType.ext hTU
  subst U
  have ha := FrameKey.ext hq
  subst a'
  exact applyValue_level Ω C hno v v' hv hvv a p p' hp hp' hb hpp

namespace PreResult
variable {Ω C hno} {Γ : List (Expr S)} {M T : Expr S}
variable {e f : Environment (hw := hw) Ω C hno Γ}

theorem parameter_eq (r : PreResult Ω C hno M T e)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)) :
    r.parameter = some (r.val ha).val := dite_eq_left ha

theorem parameter_bounded {k : Nat} (r : PreResult Ω C hno M T e)
    (hb : ∀ ha, RawValue.Bounded Ω C hno k (r.val ha).val) :
    Parameter.Bounded Ω C hno k r.parameter := by
  unfold parameter
  split
  · intro v hv
    exact Option.some.inj hv ▸ hb _
  · exact Parameter.bounded_none k

theorem val_bounded {k : Nat} (r : PreResult Ω C hno M T e)
    (hb : Parameter.Bounded Ω C hno k r.parameter)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)) :
    RawValue.Bounded Ω C hno k (r.val ha).val := hb _ (r.parameter_eq ha)

theorem parameter_level {k : Nat} (r : PreResult Ω C hno M T e) (q : PreResult Ω C hno M T f)
    (ht : (T.subst e.images).normalForm = (T.subst f.images).normalForm)
    (hv : ∀ ha hb, RawValue.LevelEq Ω C hno k (r.val ha).val (q.val hb).val) :
    Parameter.LevelEq Ω C hno k r.parameter q.parameter := by
  unfold parameter
  by_cases ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)
  · have hb := ht ▸ ha
    rw [dite_eq_left ha,dite_eq_left hb]
    exact hv ha hb
  · have hb : ¬ ActiveLayer P C (Ω.profile (T.subst f.images).normalForm) := ht ▸ ha
    rw [dite_eq_right ha,dite_eq_right hb]
    trivial

theorem val_level {k : Nat} (r : PreResult Ω C hno M T e) (q : PreResult Ω C hno M T f)
    (hr : Parameter.LevelEq Ω C hno k r.parameter q.parameter)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (hb : ActiveLayer P C (Ω.profile (T.subst f.images).normalForm)) :
    RawValue.LevelEq Ω C hno k (r.val ha).val (q.val hb).val := by
  rw [r.parameter_eq ha,q.parameter_eq hb] at hr
  exact hr

 theorem baseRead_level {k : Nat} (h : HasType P Γ M T) (he : e.ImageCompatible f)
    (v : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm) →
      Value (hw := hw) Ω C hno (T.subst e.images).normalForm)
    (w : ActiveLayer P C (Ω.profile (T.subst f.images).normalForm) →
      Value (hw := hw) Ω C hno (T.subst f.images).normalForm)
    (hv : ∀ ha hb, RawValue.LevelEq Ω C hno k (v ha).val (w hb).val) :
    (baseRead h v).val = (baseRead h w).val := by
  have hM := e.actual_expr_eq he h
  have hT := e.actual_type_eq he h
  by_cases hm : Ω.profile (M.subst e.images).normalForm ∈ C
  · have hm' : Ω.profile (M.subst f.images).normalForm ∈ C := hM ▸ hm
    by_cases hs : ∃ s : S, T = .sort s ∧ ({s} : Set S) ∈ C
    · by_cases ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)
      · have hb : ActiveLayer P C (Ω.profile (T.subst f.images).normalForm) := hT ▸ ha
        simp only [baseRead, Environment.actualExpression, hm, hm', hs, ha, hb, dite_true]
        have hbase := RawValue.level_base (hv ha hb)
        have hX : e.actualExpression (hs.choose_spec.1 ▸ h) =
            f.actualExpression (hs.choose_spec.1 ▸ h) := Subtype.ext hM
        dsimp only [Environment.actualExpression] at hX
        rw [hbase]
        exact congrArg (fun X : ActualType Ω => ((RawValue.base Ω C hno (w hb).val) X).val) hX
      · have hb : ¬ ActiveLayer P C (Ω.profile (T.subst f.images).normalForm) := hT ▸ ha
        simp only [baseRead, Environment.actualExpression, hm, hm', hs, ha, hb, dite_true, dite_false]
        exact congrArg (Candidates.Top Ω) hM
    · simp only [baseRead, Environment.actualExpression, hm, hm', hs, dite_true, dite_false]
      exact congrArg (Candidates.Top Ω) hM
  · have hm' : Ω.profile (M.subst f.images).normalForm ∉ C := hM ▸ hm
    simp only [baseRead, Environment.actualExpression, hm, hm', dite_false]
    exact congrArg (Candidates.Top Ω) hM

end PreResult

namespace ProductInstance
variable {Ω C hno}
theorem domain_not_minus (t : ProductInstance (hw := hw) Ω C hno)
    (hC : IsComponent (PrimaryEdge P) C) {n : Expr S} (hn : Ω.HasType n t.domainNF)
    (hK : Ω.profile (.pi t.domainNF t.bodyNF) ∈ C) (hL : Ω.profile (t.targetNF n) ∈ C) :
    ¬ FreeLayer P C (Ω.profile t.domainNF) true := by
  intro hm
  obtain ⟨J,hf,hp⟩ := Ω.frame_profiles hw t.product_typed hn
  have hL' : Ω.profile (t.bodyNF.instantiate n) ∈ C := by
    rw [t.target_eq hn,ContextTower.profile_normalForm] at hL
    exact hL
  have hJ := hC.between hL' hK hp.reach (.single (.codomain hf))
  exact Bool.noConfusion (hm.direct_sign ⟨hm.active.layer,J,hJ,_,hK,hf⟩)

theorem targetNF_eq {t t' : ProductInstance (hw := hw) Ω C hno}
    (hD : t.domainNF = t'.domainNF) (hE : t.bodyNF = t'.bodyNF)
    {n : Expr S} (hn : Ω.HasType n t.domainNF) : t.targetNF n = t'.targetNF n := by
  rw [t.target_eq hn,t'.target_eq (hD ▸ hn),hE]

theorem testers_eq {t t' : ProductInstance (hw := hw) Ω C hno}
    (hD : t.domainNF = t'.domainNF) (d : Candidate Ω t.domainNF) (d' : Candidate Ω t'.domainNF)
    (hd : Ω.profile t.domainNF ∈ C → d.val = d'.val) : t.testers d = t'.testers d' := by
  unfold testers
  by_cases hh : Ω.profile t.domainNF ∈ C
  · have hh' : Ω.profile t'.domainNF ∈ C := hD ▸ hh
    rw [ite_eq_left hh,ite_eq_left hh']
    exact hd hh
  · have hh' : Ω.profile t'.domainNF ∉ C := hD ▸ hh
    rw [ite_eq_right hh,ite_eq_right hh',hD]

theorem fibers_eq {t t' : ProductInstance (hw := hw) Ω C hno}
    (hD : t.domainNF = t'.domainNF) (hE : t.bodyNF = t'.bodyNF)
    (b : t.BodyReads) (b' : t'.BodyReads)
    (hb : ∀ n hn p hp, Ω.profile (t.targetNF n) ∈ C →
        (b n hn p hp).val = (b' n (hD ▸ hn) p (hD ▸ hp)).val) :
    t.fibers b = t'.fibers b' := by
  funext n
  unfold fibers
  by_cases hn : Ω.HasType n t.domainNF
  · have hn' : Ω.HasType n t'.domainNF := hD ▸ hn
    rw [dite_eq_left hn,dite_eq_left hn']
    have ht := targetNF_eq hD hE hn
    by_cases hc : Ω.profile (t.targetNF n) ∈ C
    · have hc' : Ω.profile (t'.targetNF n) ∈ C := ht ▸ hc
      rw [ite_eq_left hc,ite_eq_left hc']
      ext U
      constructor
      · rintro ⟨p,hp,rfl⟩
        exact ⟨p,hD ▸ hp,hb n hn p hp hc⟩
      · rintro ⟨p,hp,rfl⟩
        exact ⟨p,hD.symm ▸ hp,(hb n hn p (hD.symm ▸ hp) hc).symm⟩
    · have hc' : Ω.profile (t'.targetNF n) ∉ C := ht ▸ hc
      rw [ite_eq_right hc,ite_eq_right hc',ht]
  · have hn' : ¬ Ω.HasType n t'.domainNF := hD ▸ hn
    rw [dite_eq_right hn,dite_eq_right hn']

theorem candidate_eq {t t' : ProductInstance (hw := hw) Ω C hno}
    (hD : t.domainNF = t'.domainNF) (hE : t.bodyNF = t'.bodyNF)
    (d : Candidate Ω t.domainNF) (d' : Candidate Ω t'.domainNF)
    (b : t.BodyReads) (b' : t'.BodyReads)
    (hd : Ω.profile t.domainNF ∈ C → d.val = d'.val)
    (hb : ∀ n hn p hp, Ω.profile (t.targetNF n) ∈ C →
        (b n hn p hp).val = (b' n (hD ▸ hn) p (hD ▸ hp)).val) :
    (t.candidate d b).val = (t'.candidate d' b').val := by
  change Candidates.ProductTest Ω t.domainNF t.bodyNF (t.testers d) (t.fibers b) =
    Candidates.ProductTest Ω t'.domainNF t'.bodyNF (t'.testers d') (t'.fibers b')
  rw [testers_eq hD d d' hd,fibers_eq hD hE b b' hb,hD,hE]
end ProductInstance

abbrev Evaluator (Γ : List (Expr S)) (M T : Expr S) :=
  ∀ e : Environment (hw := hw) Ω C hno Γ, PreResult Ω C hno M T e

/-- The exact three uniform finite-bound assertions, expressed without
identifying dependent candidate/value indices by extra axioms. -/
structure Uniform {Γ : List (Expr S)} {M T : Expr S}
    (ev : Evaluator (hw := hw) Ω C hno Γ M T) (F : Nat → Nat) : Prop where
  growth : ∀ k, k+1 ≤ F k
  bounded : ∀ k e, e.Bounded k → Parameter.Bounded Ω C hno (F k) (ev e).parameter
  compare : ∀ k e f, e.Bounded k → f.Bounded k → e.LevelEq (F k) f →
    Parameter.LevelEq Ω C hno k (ev e).parameter (ev f).parameter ∧ (ev e).read.val = (ev f).read.val

namespace Uniform
variable {Ω C hno} {Γ : List (Expr S)} {M T : Expr S}
variable {ev : Evaluator (hw := hw) Ω C hno Γ M T} {F : Nat → Nat}
theorem val_bounded (h : Uniform Ω C hno ev F) (k : Nat) (e : Environment (hw := hw) Ω C hno Γ)
    (he : e.Bounded k) (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)) :
    RawValue.Bounded Ω C hno (F k) ((ev e).val ha).val :=
  (ev e).val_bounded (h.bounded k e he) ha

theorem val_level (h : Uniform Ω C hno ev F) (k : Nat) (e f : Environment (hw := hw) Ω C hno Γ)
    (he : e.Bounded k) (hf : f.Bounded k) (hef : e.LevelEq (F k) f)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (hb : ActiveLayer P C (Ω.profile (T.subst f.images).normalForm)) :
    RawValue.LevelEq Ω C hno k ((ev e).val ha).val ((ev f).val hb).val :=
  (ev e).val_level (ev f) (h.compare k e f he hf hef).1 ha hb
end Uniform

namespace PreResult
variable {Ω C hno} {Γ : List (Expr S)} {M T : Expr S}
theorem lookup_parameter {n : Nat} {A : Expr S} (h : HasType P Γ (.var n) T)
    (hd : Lookup Γ n A) (hc : Converts T A) (e : Environment (hw := hw) Ω C hno Γ) :
    (lookup h hd hc e).parameter = e.parameters n := by
  have ht := e.type_convert_eq h (HasType.lookup h.valid hd) hc
  have hp := e.lawful n A hd
  rw [← ht] at hp
  by_cases ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)
  · rw [parameter_eq _ ha]
    exact hp.value_spec ha
  · rw [show (lookup h hd hc e).parameter = none from dite_eq_right ha]
    cases hh : e.parameters n with
    | none => rfl
    | some v =>
      rw [hh] at hp
      exact False.elim (ha hp.active)

theorem lookup_uniform {n : Nat} {A : Expr S} (h : HasType P Γ (.var n) T)
    (hd : Lookup Γ n A) (hc : Converts T A) :
    Uniform (hw := hw) Ω C hno (lookup h hd hc) (fun k => k+1) := by
  constructor
  · intro k; exact le_refl _
  · intro k e he
    rw [lookup_parameter]
    exact Parameter.bounded_mono (Nat.le_succ k) (he n h.scope.1)
  · intro k e f he hf hef
    have hparam : Parameter.LevelEq Ω C hno k (lookup h hd hc e).parameter (lookup h hd hc f).parameter := by
      rw [lookup_parameter,lookup_parameter]
      exact Parameter.level_mono (Nat.le_succ k) (hef.2 n h.scope.1)
    refine ⟨hparam,?_⟩
    apply baseRead_level h hef.1
    intro ha hb
    exact val_level _ _ hparam ha hb

theorem sort_uniform {s t : S} (h : HasType P Γ (.sort s) T)
    (ha : P.axioms s t) (hc : Converts T (.sort t)) :
    Uniform (hw := hw) Ω C hno (sort h ha hc) (fun k => k+1) := by
  constructor
  · intro k; exact le_refl _
  · intro k e _
    apply parameter_bounded
    intro ht
    exact RawValue.bounded_mono (Nat.succ_le_succ (Nat.zero_le k)) (distinguished_bounded Ω C hno _)
  · intro k e f _ _ hef
    constructor
    · apply parameter_level _ _ (e.actual_type_eq hef.1 h)
      intro ht ht'
      have hh : e.activeType h ht = f.activeType h ht' := ActiveType.ext (e.actual_type_eq hef.1 h)
      change RawValue.LevelEq Ω C hno k (distinguished Ω C hno (e.activeType h ht)).val
        (distinguished Ω C hno (f.activeType h ht')).val
      rw [hh]
      exact RawValue.level_refl k _
    · exact congrArg (Candidates.Top Ω) (e.actual_expr_eq hef.1 h)
theorem abstractionAction_bounded {D m E : Expr S} {s : S} (h : HasType P Γ (.lam D m) T)
    (hp : HasType P Γ (.pi D E) (.sort s)) (hc : Converts T (.pi D E))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) m E) {B : Nat → Nat}
    (hb : Uniform Ω C hno eb B) (k : Nat) (e : Environment (hw := hw) Ω C hno Γ)
    (he : e.Bounded k) (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)) :
    ActionBound Ω C hno (e.activeType h ha) k (B k) (abstractionAction h hp hc eb e ha) := by
  intro a p hp' hbp
  dsimp only [abstractionAction]
  apply hb.val_bounded
  dsimp only [ProductInstance.frameEnvironment, ProductInstance.extend]
  exact Environment.bounded_cons _ _ _ _ he hbp

theorem abstractionAction_level {D m E : Expr S} {s : S} (h : HasType P Γ (.lam D m) T)
    (hp : HasType P Γ (.pi D E) (.sort s)) (hc : Converts T (.pi D E))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) m E) {B : Nat → Nat}
    (hb : Uniform Ω C hno eb B) (k : Nat) (e f : Environment (hw := hw) Ω C hno Γ)
    (he : e.Bounded k) (hf : f.Bounded k) (hef : e.LevelEq (B k) f)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (ha' : ActiveLayer P C (Ω.profile (T.subst f.images).normalForm))
    (a : FrameKey Ω C (e.activeType h ha)) (a' : FrameKey Ω C (f.activeType h ha'))
    (hq : a.argument = a'.argument)
    (p p' : Option (RawValue (hw := hw) Ω C hno))
    (hp' : PayloadFits Ω C hno a.domain p) (hp'' : PayloadFits Ω C hno a'.domain p')
    (hbp : Parameter.Bounded Ω C hno k p) (hbp' : Parameter.Bounded Ω C hno k p')
    (hpp : Parameter.LevelEq Ω C hno (B k) p p') :
    RawValue.LevelEq Ω C hno k (abstractionAction h hp hc eb e ha a p hp').val
      (abstractionAction h hp hc eb f ha' a' p' hp'').val := by
  dsimp only [abstractionAction]
  apply hb.val_level
  · dsimp only [ProductInstance.frameEnvironment, ProductInstance.extend]
    exact Environment.bounded_cons _ _ _ _ he hbp
  · dsimp only [ProductInstance.frameEnvironment, ProductInstance.extend]
    exact Environment.bounded_cons _ _ _ _ hf hbp'
  · dsimp only [ProductInstance.frameEnvironment, ProductInstance.extend]
    apply Environment.level_cons hef
    · exact hq ▸ .refl _
    · exact hpp

theorem abstraction_val_level {D m E : Expr S} {s : S} (h : HasType P Γ (.lam D m) T)
    (hp : HasType P Γ (.pi D E) (.sort s)) (hc : Converts T (.pi D E))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) m E) {B : Nat → Nat}
    (hb : Uniform Ω C hno eb B) (k : Nat) (e f : Environment (hw := hw) Ω C hno Γ)
    (he : e.Bounded k) (hf : f.Bounded k) (hef : e.LevelEq (B k) f)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (ha' : ActiveLayer P C (Ω.profile (T.subst f.images).normalForm)) :
    RawValue.LevelEq Ω C hno k ((abstraction h hp hc eb e).val ha).val
      ((abstraction h hp hc eb f).val ha').val := by
  apply lambdaValue_level_of_type_eq Ω C hno (e.actual_type_eq hef.1 h)
  exact abstractionAction_level h hp hc eb hb k e f he hf hef ha ha'

theorem abstraction_uniform {D m E : Expr S} {s : S} (h : HasType P Γ (.lam D m) T)
    (hp : HasType P Γ (.pi D E) (.sort s)) (hc : Converts T (.pi D E))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) m E) {B : Nat → Nat}
    (hb : Uniform Ω C hno eb B) :
    Uniform Ω C hno (abstraction h hp hc eb) (fun k => B k + 1) := by
  constructor
  · intro k
    exact le_trans (hb.growth k) (Nat.le_succ _)
  · intro k e he
    apply parameter_bounded
    intro ha
    apply lambdaValue_bounded Ω C hno (by have := hb.growth k; omega)
    · exact abstractionAction_bounded h hp hc eb hb k e he ha
    · intro a p p' hp' hp'' hbp hbp' hpp
      exact abstractionAction_level h hp hc eb hb k e e he he (e.level_refl _) ha ha
        a a rfl p p' hp' hp'' hbp hbp' hpp
  · intro k e f he hf hef
    have hf' := e.level_mono (Nat.le_succ (B k)) hef
    constructor
    · apply parameter_level _ _ (e.actual_type_eq hef.1 h)
      exact abstraction_val_level h hp hc eb hb k e f he hf hf'
    · apply baseRead_level h hef.1
      exact abstraction_val_level h hp hc eb hb k e f he hf hf'

def appBound (F N : Nat → Nat) (k : Nat) : Nat :=
  1 + max (max (max k (F k)) (N k)) (max (F (max k (N k))) (N (max k (F k))))

 theorem applicationValue_bounded {f n D E : Expr S} (h : HasType P Γ (.app f n) T)
    (hf : HasType P Γ f (.pi D E)) (hn : HasType P Γ n D) (hc : Converts T (E.instantiate n))
    (ef : Evaluator (hw := hw) Ω C hno Γ f (.pi D E)) (en : Evaluator (hw := hw) Ω C hno Γ n D)
    {F N : Nat → Nat} (huf : Uniform Ω C hno ef F) (_hun : Uniform Ω C hno en N)
    (k : Nat) (e : Environment (hw := hw) Ω C hno Γ) (he : e.Bounded k)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)) :
    RawValue.Bounded Ω C hno (appBound F N k) (applicationValue h hf hn hc ef en e ha).val := by
  dsimp only [applicationValue]
  split
  ·
    apply RawValue.bounded_mono (m := appBound F N k) (n := F k) (by unfold appBound; omega)
    apply applyValue_bounded
    exact huf.val_bounded k e he _
  · exact RawValue.bounded_mono (by unfold appBound; omega) (distinguished_bounded Ω C hno _)

 theorem applicationValue_level {f n D E : Expr S} (h : HasType P Γ (.app f n) T)
    (hf : HasType P Γ f (.pi D E)) (hn : HasType P Γ n D) (hc : Converts T (E.instantiate n))
    (ef : Evaluator (hw := hw) Ω C hno Γ f (.pi D E)) (en : Evaluator (hw := hw) Ω C hno Γ n D)
    {F N : Nat → Nat} (huf : Uniform Ω C hno ef F) (hun : Uniform Ω C hno en N)
    (k : Nat) (e e' : Environment (hw := hw) Ω C hno Γ) (he : e.Bounded k) (he' : e'.Bounded k)
    (hee : e.LevelEq (appBound F N k) e')
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (ha' : ActiveLayer P C (Ω.profile (T.subst e'.images).normalForm)) :
    RawValue.LevelEq Ω C hno k (applicationValue h hf hn hc ef en e ha).val
      (applicationValue h hf hn hc ef en e' ha').val := by
  have ht := e.actual_type_eq hee.1 hf
  by_cases hF : ActiveLayer P C (Ω.profile (Expr.pi D E |>.subst e.images).normalForm)
  · have hF' : ActiveLayer P C (Ω.profile (Expr.pi D E |>.subst e'.images).normalForm) := ht ▸ hF
    simp only [applicationValue, hF, hF', dite_true]
    apply applyValue_level_of_type_eq Ω C hno (j := F k) (r := N k) ht
    · exact huf.val_bounded k e he _
    · exact huf.val_level (max k (N k)) e e'
        (e.bounded_mono (le_max_left _ _) he) (e'.bounded_mono (le_max_left _ _) he')
        (e.level_mono (by unfold appBound; omega) hee) _ _
    · exact e.actual_expr_eq hee.1 hn
    · exact hun.bounded k e he
    · apply Parameter.level_mono (le_max_right k (F k))
      exact (hun.compare (max k (F k)) e e'
        (e.bounded_mono (le_max_left _ _) he) (e'.bounded_mono (le_max_left _ _) he')
        (e.level_mono (by unfold appBound; omega) hee)).1
  · have hF' : ¬ ActiveLayer P C (Ω.profile (Expr.pi D E |>.subst e'.images).normalForm) := ht ▸ hF
    simp only [applicationValue, hF, hF', dite_false]
    have hA : e.activeType h ha = e'.activeType h ha' := ActiveType.ext (e.actual_type_eq hee.1 h)
    have hv := congrArg (fun A : ActiveType Ω C => (distinguished (hw := hw) Ω C hno A).val) hA
    rw [hv]
    exact RawValue.level_refl k _

 theorem application_uniform {f n D E : Expr S} (h : HasType P Γ (.app f n) T)
    (hf : HasType P Γ f (.pi D E)) (hn : HasType P Γ n D) (hc : Converts T (E.instantiate n))
    (ef : Evaluator (hw := hw) Ω C hno Γ f (.pi D E)) (en : Evaluator (hw := hw) Ω C hno Γ n D)
    {F N : Nat → Nat} (huf : Uniform Ω C hno ef F) (hun : Uniform Ω C hno en N) :
    Uniform Ω C hno (application h hf hn hc ef en) (appBound F N) := by
  constructor
  · intro k; unfold appBound; omega
  · intro k e he
    apply parameter_bounded
    exact applicationValue_bounded h hf hn hc ef en huf hun k e he
  · intro k e e' he he' hee
    constructor
    · apply parameter_level _ _ (e.actual_type_eq hee.1 h)
      exact applicationValue_level h hf hn hc ef en huf hun k e e' he he' hee
    · apply baseRead_level h hee.1
      exact applicationValue_level h hf hn hc ef en huf hun k e e' he he' hee

end PreResult

omit [Fintype S] in
theorem Base.update_congr {T U : ActualType Ω} (b : Base Ω) (hTU : T = U)
    (d : Candidate Ω T.val) (e : Candidate Ω U.val) (hde : d.val = e.val) :
    Base.update Ω b T d = Base.update Ω b U e := by
  subst U
  have hd : d = e := Subtype.ext hde
  subst e
  rfl

theorem withBase_level_of_type_eq {T U : ActiveType Ω C} (hTU : T.type = U.type)
    {b b' : Base Ω} (hbb : b = b') (k : Nat) :
    RawValue.LevelEq (hw := hw) Ω C hno k (withBase Ω C hno T b).val (withBase Ω C hno U b').val := by
  have ht := ActiveType.ext hTU
  subst U
  subst b'
  exact RawValue.level_refl k _

theorem distinguished_level_of_type_eq {T U : ActiveType Ω C} (hTU : T.type = U.type) (k : Nat) :
    RawValue.LevelEq (hw := hw) Ω C hno k (distinguished Ω C hno T).val (distinguished Ω C hno U).val := by
  have ht := ActiveType.ext hTU
  subst U
  exact RawValue.level_refl k _

namespace PreResult
variable {Ω C hno} {Γ : List (Expr S)} {T : Expr S}
def productBound (D B : Nat → Nat) (k : Nat) : Nat := 1 + max k (max (D k) (B k))

theorem productCandidate_level {D E : Expr S} {a b c : S}
    (hd : HasType P Γ D (.sort a)) (hb : HasType P (D :: Γ) E (.sort b)) (hr : P.rule a b c)
    (ed : Evaluator (hw := hw) Ω C hno Γ D (.sort a))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) E (.sort b))
    (hC : IsComponent (PrimaryEdge P) C)
    {F B : Nat → Nat} (hud : Uniform Ω C hno ed F) (hub : Uniform Ω C hno eb B)
    (k : Nat) (e f : Environment (hw := hw) Ω C hno Γ)
    (he : e.Bounded k) (hf : f.Bounded k) (hef : e.LevelEq (productBound F B k) f)
    (hK : Ω.profile (Expr.pi D E |>.subst e.images).normalForm ∈ C) :
    (productCandidate hd hb hr ed eb e).val = (productCandidate hd hb hr ed eb f).val := by
  let t := productData hd hb hr e
  let u := productData hd hb hr f
  have hp := e.actual_expr_eq hef.1 (HasType.product hd hb hr)
  have hdu := Expr.pi.inj ((t.product_nf.symm.trans hp).trans u.product_nf)
  have hk : Ω.profile (.pi t.domainNF t.bodyNF) ∈ C := t.product_nf ▸ hK
  apply ProductInstance.candidate_eq hdu.1 hdu.2
  · intro _
    exact (hud.compare k e f he hf (e.level_mono (by unfold productBound; omega) hef)).2
  · intro n hn p hpn hc
    have hnb := t.domain_not_minus hC hn hk hc
    have hbp : Parameter.Bounded Ω C hno k p := Parameter.bounded_of_not_minus hnb hpn
    apply (hub.compare k (t.extend hn p hpn) (u.extend (hdu.1 ▸ hn) p (hdu.1 ▸ hpn)) ?_ ?_ ?_).2
    · dsimp only [ProductInstance.extend]
      exact Environment.bounded_cons _ _ _ _ he hbp
    · dsimp only [ProductInstance.extend]
      exact Environment.bounded_cons _ _ _ _ hf hbp
    · dsimp only [ProductInstance.extend]
      apply Environment.level_cons (e.level_mono (by unfold productBound; omega) hef)
      · exact .refl _
      · exact Parameter.level_refl _ _

theorem product_val_level {D E : Expr S} {a b c : S} (h : HasType P Γ (.pi D E) T)
    (hd : HasType P Γ D (.sort a)) (hb : HasType P (D :: Γ) E (.sort b)) (hr : P.rule a b c)
    (hc : Converts T (.sort c))
    (ed : Evaluator (hw := hw) Ω C hno Γ D (.sort a))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) E (.sort b))
    (hC : IsComponent (PrimaryEdge P) C)
    {F B : Nat → Nat} (hud : Uniform Ω C hno ed F) (hub : Uniform Ω C hno eb B)
    (k : Nat) (e f : Environment (hw := hw) Ω C hno Γ)
    (he : e.Bounded k) (hf : f.Bounded k) (hef : e.LevelEq (productBound F B k) f)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (ha' : ActiveLayer P C (Ω.profile (T.subst f.images).normalForm)) :
    RawValue.LevelEq Ω C hno k ((product h hd hb hr hc ed eb e).val ha).val
      ((product h hd hb hr hc ed eb f).val ha').val := by
  have hp := e.actual_expr_eq hef.1 h
  have ht := e.actual_type_eq hef.1 h
  by_cases hh : ({c} : Set S) ∈ C ∧ Ω.profile (Expr.pi D E |>.subst e.images).normalForm ∈ C
  · have hh' : ({c} : Set S) ∈ C ∧ Ω.profile (Expr.pi D E |>.subst f.images).normalForm ∈ C := hp ▸ hh
    simp only [product,hh,hh']
    apply withBase_level_of_type_eq Ω C hno ht
    apply Base.update_congr Ω _ (Subtype.ext hp)
    exact productCandidate_level hd hb hr ed eb hC hud hub k e f he hf hef hh.2
  · have hh' : ¬ (({c} : Set S) ∈ C ∧ Ω.profile (Expr.pi D E |>.subst f.images).normalForm ∈ C) := hp ▸ hh
    simp only [product,hh,hh',dite_false]
    exact distinguished_level_of_type_eq Ω C hno ht k

theorem product_uniform {D E : Expr S} {a b c : S} (h : HasType P Γ (.pi D E) T)
    (hd : HasType P Γ D (.sort a)) (hb : HasType P (D :: Γ) E (.sort b)) (hr : P.rule a b c)
    (hc : Converts T (.sort c))
    (ed : Evaluator (hw := hw) Ω C hno Γ D (.sort a))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) E (.sort b))
    (hC : IsComponent (PrimaryEdge P) C)
    {F B : Nat → Nat} (hud : Uniform Ω C hno ed F) (hub : Uniform Ω C hno eb B) :
    Uniform Ω C hno (product h hd hb hr hc ed eb) (productBound F B) := by
  constructor
  · intro k; unfold productBound; omega
  · intro k e _
    apply parameter_bounded
    intro ha
    dsimp only [product]
    split
    · exact RawValue.bounded_mono (by unfold productBound; omega) (withBase_bounded Ω C hno _ _)
    · exact RawValue.bounded_mono (by unfold productBound; omega) (distinguished_bounded Ω C hno _)
  · intro k e f he hf hef
    constructor
    · apply parameter_level _ _ (e.actual_type_eq hef.1 h)
      exact product_val_level h hd hb hr hc ed eb hC hud hub k e f he hf hef
    · have hp := e.actual_expr_eq hef.1 h
      by_cases hh : Ω.profile (Expr.pi D E |>.subst e.images).normalForm ∈ C
      · have hh' : Ω.profile (Expr.pi D E |>.subst f.images).normalForm ∈ C := hp ▸ hh
        simp only [product,hh,hh',ite_true, if_true]
        exact productCandidate_level hd hb hr ed eb hC hud hub k e f he hf hef hh
      · have hh' : Ω.profile (Expr.pi D E |>.subst f.images).normalForm ∉ C := hp ▸ hh
        simp only [product,hh,hh',ite_false, if_false]
        exact congrArg (Candidates.Top Ω) hp
end PreResult
end

universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

/-- The manuscript's finite-bound lemma for every stored typing tree. No
normalization or candidate restriction is imposed on the raw environment. -/
theorem preEvaluate_uniform {Γ : List (Expr S)} {M T : Expr S}
    (hC : IsComponent (PrimaryEdge P) C) (t : TypingTree P Γ M T) :
    ∃ F, Uniform (hw := hw) Ω C hno (preEvaluate Ω C hno t) F := by
  induction t with
  | var h hd hc => exact ⟨_,PreResult.lookup_uniform h hd hc⟩
  | sort h ha hc => exact ⟨_,PreResult.sort_uniform h ha hc⟩
  | product h d b hr hc ihd ihb =>
    obtain ⟨F,hF⟩ := ihd
    obtain ⟨B,hB⟩ := ihb
    exact ⟨_,PreResult.product_uniform h d.typing b.typing hr hc _ _ hC hF hB⟩
  | abstraction h d b hp hc _ ihb =>
    obtain ⟨B,hB⟩ := ihb
    exact ⟨_,PreResult.abstraction_uniform h hp hc _ hB⟩
  | application h f a hc ihf iha =>
    obtain ⟨F,hF⟩ := ihf
    obtain ⟨N,hN⟩ := iha
    exact ⟨_,PreResult.application_uniform h f.typing a.typing hc _ _ hF hN⟩

namespace RawValue
variable {Ω C hno}
theorem all_levels_eq {v w : RawValue (hw := hw) Ω C hno}
    (h : ∀ n, LevelEq Ω C hno n v w) : v = w := by
  cases v <;> cases w <;> try exact False.elim (h 0)
  · exact congrArg _ (h 0)
  · exact congrArg _ (FreeObservations.Agree.all_levels_eq h)
  · exact congrArg _ (h 0)
end RawValue
namespace Parameter
variable {Ω C hno}
theorem all_levels_eq {v w : Option (RawValue (hw := hw) Ω C hno)}
    (h : ∀ n, LevelEq Ω C hno n v w) : v = w := by
  cases v <;> cases w <;> try exact False.elim (h 0)
  · rfl
  · exact congrArg some (RawValue.all_levels_eq h)
end Parameter

namespace Environment
variable {Ω C hno} {Γ : List (Expr S)}
def Compatible (e f : Environment (hw := hw) Ω C hno Γ) : Prop :=
  e.ImageCompatible f ∧ ∀ n, n < Γ.length → e.parameters n = f.parameters n

theorem Compatible.level {e f : Environment (hw := hw) Ω C hno Γ}
    (h : e.Compatible f) (k : Nat) : e.LevelEq k f := by
  refine ⟨h.1, fun n hn => ?_⟩
  rw [h.2 n hn]
  exact Parameter.level_refl _ _
end Environment

namespace Uniform
variable {Ω C hno} {Γ : List (Expr S)} {M T : Expr S}
variable {ev : Evaluator (hw := hw) Ω C hno Γ M T} {F : Nat → Nat}
theorem compatible (h : Uniform Ω C hno ev F)
    (e f : Environment (hw := hw) Ω C hno Γ) (hef : e.Compatible f) :
    (ev e).parameter = (ev f).parameter ∧ (ev e).read.val = (ev f).read.val := by
  obtain ⟨i,hi⟩ := e.exists_bound
  obtain ⟨j,hj⟩ := f.exists_bound
  have hc (k : Nat) := h.compare (max k (max i j)) e f
    (e.bounded_mono (by omega) hi) (f.bounded_mono (by omega) hj)
    (hef.level _)
  constructor
  · apply Parameter.all_levels_eq
    intro k
    exact Parameter.level_mono (le_max_left _ _) (hc k).1
  · exact (hc 0).2
end Uniform

/-- Compatible-image invariance, including arbitrary raw non-SN images. -/
theorem preEvaluate_compatible {Γ : List (Expr S)} {M T : Expr S}
    (hC : IsComponent (PrimaryEdge P) C) (t : TypingTree P Γ M T)
    (e f : Environment (hw := hw) Ω C hno Γ) (hef : e.Compatible f) :
    (preEvaluate Ω C hno t e).parameter = (preEvaluate Ω C hno t f).parameter ∧
    (preEvaluate Ω C hno t e).read.val = (preEvaluate Ω C hno t f).read.val := by
  obtain ⟨F,hF⟩ := preEvaluate_uniform Ω C hno hC t
  exact hF.compatible e f hef

end PureTypeSystem.ObservationValues

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Labelled
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate _root_.OAI.PureTypeSystem.instCountableExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/- Labelled beta reduction retains every annotation.
These are definitions, not an extension of the PTS specification. -/
namespace PureTypeSystem.Labelled

universe u

inductive Mode
  | data
  | proof
  deriving DecidableEq

inductive Label
  | dd
  | dp
  | pp
  deriving DecidableEq

def Label.domain : Label → Mode
  | .dd | .dp => .data
  | .pp => .proof

def Label.result : Label → Mode
  | .dd => .data
  | .dp | .pp => .proof

inductive Expr (S : Type u) : Type u
  | var : Nat → Expr S
  | sort : S → Expr S
  | app : Label → Expr S → Expr S → Expr S
  | lam : Label → Expr S → Expr S → Expr S
  | pi : Label → Expr S → Expr S → Expr S
  deriving DecidableEq

namespace Expr
variable {S : Type u}

abbrev liftRen := PureTypeSystem.Expr.liftRen

def rename (ρ : Nat → Nat) : Expr S → Expr S
  | .var n => .var (ρ n)
  | .sort s => .sort s
  | .app l f a => .app l (rename ρ f) (rename ρ a)
  | .lam l A b => .lam l (rename ρ A) (rename (liftRen ρ) b)
  | .pi l A B => .pi l (rename ρ A) (rename (liftRen ρ) B)

def liftSub (σ : Nat → Expr S) : Nat → Expr S
  | 0 => .var 0
  | n+1 => (σ n).rename Nat.succ

def subst (σ : Nat → Expr S) : Expr S → Expr S
  | .var n => σ n
  | .sort s => .sort s
  | .app l f a => .app l (subst σ f) (subst σ a)
  | .lam l A b => .lam l (subst σ A) (subst (liftSub σ) b)
  | .pi l A B => .pi l (subst σ A) (subst (liftSub σ) B)

def single (a : Expr S) : Nat → Expr S
  | 0 => a
  | n+1 => .var n

def instantiate (b a : Expr S) : Expr S := b.subst (single a)

def erase : Expr S → PureTypeSystem.Expr S
  | .var n => .var n
  | .sort s => .sort s
  | .app _ f a => .app f.erase a.erase
  | .lam _ A b => .lam A.erase b.erase
  | .pi _ A B => .pi A.erase B.erase

@[simp] theorem rename_id (M : Expr S) : M.rename id = M := by
  induction M <;> simp_all [rename, liftRen, PureTypeSystem.Expr.liftRen_id]

theorem rename_comp (M : Expr S) (ρ τ : Nat → Nat) :
    (M.rename τ).rename ρ = M.rename (ρ ∘ τ) := by
  induction M generalizing ρ τ <;>
    simp_all only [rename, Function.comp_apply, PureTypeSystem.Expr.liftRen_comp]

@[simp] theorem subst_var (M : Expr S) : M.subst .var = M := by
  have h : liftSub (var : Nat → Expr S) = var := by funext n; cases n <;> rfl
  induction M <;> simp_all only [subst]

theorem subst_rename (M : Expr S) (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (M.rename ρ).subst σ = M.subst (σ ∘ ρ) := by
  have h : ∀ (σ : Nat → Expr S) (ρ : Nat → Nat),
      liftSub σ ∘ liftRen ρ = liftSub (σ ∘ ρ) := by
    intro σ ρ; funext n; cases n <;> rfl
  induction M generalizing σ ρ <;> simp_all only [rename, subst, Function.comp_apply]

theorem rename_subst (M : Expr S) (ρ : Nat → Nat) (σ : Nat → Expr S) :
    (M.subst σ).rename ρ = M.subst (fun n => (σ n).rename ρ) := by
  have h : ∀ (ρ : Nat → Nat) (σ : Nat → Expr S),
      (fun n => (liftSub σ n).rename (liftRen ρ)) = liftSub (fun n => (σ n).rename ρ) := by
    intro ρ σ; funext n; cases n with
    | zero => rfl
    | succ n => simp only [liftSub, rename_comp]; rfl
  induction M generalizing ρ σ <;> simp_all only [subst, rename]

theorem subst_subst (M : Expr S) (σ τ : Nat → Expr S) :
    (M.subst τ).subst σ = M.subst (fun n => (τ n).subst σ) := by
  have h : ∀ (σ τ : Nat → Expr S),
      (fun n => (liftSub τ n).subst (liftSub σ)) = liftSub (fun n => (τ n).subst σ) := by
    intro σ τ; funext n; cases n with
    | zero => rfl
    | succ n => simp only [liftSub, subst_rename, rename_subst]; rfl
  induction M generalizing σ τ <;> simp_all only [subst]

theorem instantiate_subst (b a : Expr S) (σ : Nat → Expr S) :
    (b.subst (liftSub σ)).instantiate (a.subst σ) = (b.instantiate a).subst σ := by
  simp only [instantiate, subst_subst]
  congr 1; funext n; cases n with
  | zero => rfl
  | succ n => simp only [liftSub, subst_rename]; exact subst_var (σ n)

@[simp] theorem erase_rename (M : Expr S) (ρ : Nat → Nat) :
    (M.rename ρ).erase = M.erase.rename ρ := by
  induction M generalizing ρ <;> simp_all only [rename, erase, PureTypeSystem.Expr.rename]

end Expr

inductive Beta {S : Type u} : Expr S → Expr S → Prop
  | head (l A b a) : Beta (.app l (.lam l A b) a) (b.instantiate a)
  | app_left {l f f' a} : Beta f f' → Beta (.app l f a) (.app l f' a)
  | app_right {l f a a'} : Beta a a' → Beta (.app l f a) (.app l f a')
  | lam_domain {l A A' b} : Beta A A' → Beta (.lam l A b) (.lam l A' b)
  | lam_body {l A b b'} : Beta b b' → Beta (.lam l A b) (.lam l A b')
  | pi_domain {l A A' B} : Beta A A' → Beta (.pi l A B) (.pi l A' B)
  | pi_body {l A B B'} : Beta B B' → Beta (.pi l A B) (.pi l A B')

def Converts {S : Type u} : Expr S → Expr S → Prop := Relation.EqvGen Beta
abbrev Reduces {S : Type u} : Expr S → Expr S → Prop := Relation.ReflTransGen Beta

namespace Beta
variable {S : Type u} {M N : Expr S}

theorem subst (h : Beta M N) (σ : Nat → Expr S) : Beta (M.subst σ) (N.subst σ) := by
  induction h generalizing σ with
  | head l A b a =>
      simpa only [Expr.subst, ← Expr.instantiate_subst] using
        (Beta.head l (A.subst σ) (b.subst (Expr.liftSub σ)) (a.subst σ))
  | app_left h ih => exact .app_left (ih σ)
  | app_right h ih => exact .app_right (ih σ)
  | lam_domain h ih => exact .lam_domain (ih σ)
  | lam_body h ih => exact .lam_body (ih _)
  | pi_domain h ih => exact .pi_domain (ih σ)
  | pi_body h ih => exact .pi_body (ih _)

end Beta

inductive Parallel {S : Type u} : Expr S → Expr S → Prop
  | var (n) : Parallel (.var n) (.var n)
  | sort (s) : Parallel (.sort s) (.sort s)
  | app {l f f' a a'} : Parallel f f' → Parallel a a' →
      Parallel (.app l f a) (.app l f' a')
  | lam {l A A' b b'} : Parallel A A' → Parallel b b' →
      Parallel (.lam l A b) (.lam l A' b')
  | pi {l A A' B B'} : Parallel A A' → Parallel B B' →
      Parallel (.pi l A B) (.pi l A' B')
  | head {l b b' a a'} (A) : Parallel b b' → Parallel a a' →
      Parallel (.app l (.lam l A b) a) (b'.instantiate a')

namespace Parallel

variable {S : Type u} {M N : Expr S}

@[refl] theorem refl (M : Expr S) : Parallel M M := by
  induction M with
  | var n => exact .var n
  | sort s => exact .sort s
  | app _ _ _ ihf iha => exact .app ihf iha
  | lam _ _ _ ihA ihb => exact .lam ihA ihb
  | pi _ _ _ ihA ihB => exact .pi ihA ihB

end Parallel

namespace Expr

variable {S : Type u}

/-- Complete development contracts only matching-labelled redexes. -/
def develop : Expr S → Expr S
  | var n => var n
  | sort s => sort s
  | app l (lam k A b) a =>
      if l = k then (develop b).instantiate (develop a)
      else app l (lam k (develop A) (develop b)) (develop a)
  | app l f a => app l (develop f) (develop a)
  | lam l A b => lam l (develop A) (develop b)
  | pi l A B => pi l (develop A) (develop B)

end Expr

inductive HasType {S : Type u} (P : Specification S) :
    List (Expr S) → Expr S → Expr S → Prop
  | ax {s t} : P.axioms s t → HasType P [] (.sort s) (.sort t)
  | var {Γ A s} : HasType P Γ A (.sort s) →
      HasType P (A :: Γ) (.var 0) (A.rename Nat.succ)
  | weaken {Γ M B A s} : HasType P Γ M B → HasType P Γ A (.sort s) →
      HasType P (A :: Γ) (M.rename Nat.succ) (B.rename Nat.succ)
  | product {l Γ A B s₁ s₂ s₃} : HasType P Γ A (.sort s₁) →
      HasType P (A :: Γ) B (.sort s₂) → P.rule s₁ s₂ s₃ →
      HasType P Γ (.pi l A B) (.sort s₃)
  | abstraction {l Γ A b B s} : HasType P (A :: Γ) b B →
      HasType P Γ (.pi l A B) (.sort s) →
      HasType P Γ (.lam l A b) (.pi l A B)
  | application {l Γ f a A B} : HasType P Γ f (.pi l A B) →
      HasType P Γ a A → HasType P Γ (.app l f a) (B.instantiate a)
  | conversion {Γ M A B s} : HasType P Γ M A → HasType P Γ B (.sort s) →
      Converts A B → HasType P Γ M B

inductive ValidContext {S : Type u} (P : Specification S) : List (Expr S) → Prop
  | nil : ValidContext P []
  | cons {Γ A s} : ValidContext P Γ → HasType P Γ A (.sort s) →
      ValidContext P (A :: Γ)

namespace HasType

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M A : Expr S}

theorem valid (h : HasType P Γ M A) : ValidContext P Γ := by
  induction h with
  | ax _ => exact .nil
  | var h ih => exact .cons ih h
  | weaken _ h _ ih => exact .cons ih h
  | product _ _ _ ih _ => exact ih
  | abstraction _ _ _ ih => exact ih
  | application _ _ ih _ => exact ih
  | conversion _ _ _ ih _ => exact ih

end HasType

namespace Expr
variable {S : Type u}
@[simp] theorem liftSub_zero (σ : Nat → Expr S) : liftSub σ 0 = var 0 := rfl
@[simp] theorem liftSub_succ (σ : Nat → Expr S) (n : Nat) :
    liftSub σ (n+1) = (σ n).rename Nat.succ := rfl
end Expr

inductive Lookup {S : Type u} : List (Expr S) → Nat → Expr S → Prop
  | zero (A Γ) : Lookup (A :: Γ) 0 (A.rename Nat.succ)
  | succ {Γ n A} (B) : Lookup Γ n A → Lookup (B :: Γ) (n + 1) (A.rename Nat.succ)

namespace HasType

variable {S : Type u} {P : Specification S}

theorem sort_of_valid {Γ : List (Expr S)} (hΓ : ValidContext P Γ)
    {s t : S} (hst : P.axioms s t) : HasType P Γ (.sort s) (.sort t) := by
  induction hΓ with
  | nil => exact .ax hst
  | cons _ hA ih => exact .weaken ih hA

/-- Domain generation alone precedes substitution and does not need
any exchange or context-substitution theorem. -/
theorem product_domain {Γ : List (Expr S)} {M T : Expr S} (h : HasType P Γ M T) :
    ∀ l A B, M = .pi l A B → ∃ s, HasType P Γ A (.sort s) := by
  induction h with
  | ax h => intro l A B heq; cases heq
  | var h ih => intro l A B heq; cases heq
  | @weaken Γ M T C s hM hC ihM ihC =>
      intro l A B heq
      cases M with
      | var n => cases heq
      | sort t => cases heq
      | app k f a => cases heq
      | lam k D b => cases heq
      | pi k D E =>
          obtain ⟨rfl, rfl, rfl⟩ := Expr.pi.inj heq
          obtain ⟨t, ht⟩ := ihM k D E rfl
          exact ⟨t, .weaken ht hC⟩
  | product hA hB hr ihA ihB =>
      intro l A B heq
      cases heq
      exact ⟨_, hA⟩
  | abstraction hb hT ihb ihT => intro l A B heq; cases heq
  | application hf ha ihf iha => intro l A B heq; cases heq
  | conversion hM hB hconv ihM ihB => exact ihM

end HasType

namespace Converts

variable {S : Type u} {M N : Expr S}

theorem subst (h : Converts M N) (σ : Nat → Expr S) :
    Converts (M.subst σ) (N.subst σ) := by
  induction h with
  | rel a b h => exact .rel _ _ (h.subst σ)
  | refl a => exact .refl _
  | symm a b _ ih => exact .symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

end Converts

/-- A simultaneous substitution respects each declared variable's exact type.
This is a premise only of the substitution metatheorem, not of the main target. -/
def TypedSubstitution {S : Type u} (P : Specification S)
    (Γ Δ : List (Expr S)) (σ : Nat → Expr S) : Prop :=
  ∀ n A, Lookup Γ n A → HasType P Δ (σ n) (A.subst σ)

namespace TypedSubstitution

variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)}
    {σ : Nat → Expr S}

theorem tail {A : Expr S} (hσ : TypedSubstitution P (A :: Γ) Δ σ) :
    TypedSubstitution P Γ Δ (σ ∘ Nat.succ) := by
  intro n B hB
  have h := hσ (n + 1) (B.rename Nat.succ) (.succ A hB)
  simpa only [Expr.subst_rename, Function.comp_def] using h

theorem lift {A : Expr S} {s : S} (hσ : TypedSubstitution P Γ Δ σ)
    (hA : HasType P Δ (A.subst σ) (.sort s)) :
    TypedSubstitution P (A :: Γ) (A.subst σ :: Δ) (Expr.liftSub σ) := by
  intro n B hn
  cases hn with
  | zero =>
      have ht := HasType.var hA
      simpa only [Expr.liftSub_zero, Expr.subst_rename, Expr.rename_subst,
        Expr.liftSub_succ, Function.comp_def] using ht
  | succ C hn =>
      have ht := HasType.weaken (hσ _ _ hn) hA
      simpa only [Expr.liftSub_succ, Expr.rename_subst, Expr.subst_rename,
        Function.comp_def] using ht

end TypedSubstitution

namespace HasType

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M T : Expr S}

theorem subst (h : HasType P Γ M T) {Δ : List (Expr S)}
    (hΔ : ValidContext P Δ) (σ : Nat → Expr S) (hσ : TypedSubstitution P Γ Δ σ) :
    HasType P Δ (M.subst σ) (T.subst σ) := by
  induction h generalizing Δ σ with
  | ax h => exact sort_of_valid hΔ h
  | var h ih => exact hσ _ _ (.zero _ _)
  | weaken hM hA ihM ihA =>
      simpa only [Expr.subst_rename] using ihM hΔ (σ ∘ Nat.succ) hσ.tail
  | product hA hB hr ihA ihB =>
      have hA' := ihA hΔ σ hσ
      exact .product hA' (ihB (.cons hΔ hA') _ (hσ.lift hA')) hr
  | @abstraction l Γ A b B s hb hprod ihb ihprod =>
      have hprod' := ihprod hΔ σ hσ
      obtain ⟨t, hA'⟩ := hprod'.product_domain _ _ _ rfl
      exact .abstraction (ihb (.cons hΔ hA') _ (hσ.lift hA')) hprod'
  | application hf ha ihf iha =>
      simpa only [Expr.subst, Expr.instantiate_subst] using
        (HasType.application (ihf hΔ σ hσ) (iha hΔ σ hσ))
  | conversion hM hB hconv ihM ihB =>
      exact .conversion (ihM hΔ σ hσ) (ihB hΔ σ hσ) (hconv.subst σ)

end HasType

namespace Expr

variable {S : Type u}

theorem subst_var_rename (M : Expr S) (ρ : Nat → Nat) :
    M.subst (var ∘ ρ) = M.rename ρ := by
  rw [← subst_rename, subst_var]

@[simp] theorem subst_lift_single (M a : Expr S) :
    (M.rename Nat.succ).subst (single a) = M := by
  rw [subst_rename]
  exact subst_var M

end Expr

namespace HasType

variable {S : Type u} {P : Specification S}

theorem lookup {Γ : List (Expr S)} (hΓ : ValidContext P Γ)
    {n : Nat} {A : Expr S} (hn : Lookup Γ n A) : HasType P Γ (.var n) A := by
  induction hΓ generalizing n A with
  | nil => cases hn
  | cons hΓ hB ih =>
      cases hn with
      | zero => exact .var hB
      | succ _ hn => exact .weaken (ih hn) hB

end HasType

namespace HasType

variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)}

theorem rename {M A : Expr S} (h : HasType P Γ M A)
    (hΔ : ValidContext P Δ) (ρ : Nat → Nat)
    (hρ : ∀ n B, Lookup Γ n B → HasType P Δ (.var (ρ n)) (B.rename ρ)) :
    HasType P Δ (M.rename ρ) (A.rename ρ) := by
  have hσ : TypedSubstitution P Γ Δ (Expr.var ∘ ρ) := by
    intro n B hn
    simpa only [Expr.subst_var_rename, Function.comp_apply] using hρ n B hn
  simpa only [Expr.subst_var_rename] using h.subst hΔ (Expr.var ∘ ρ) hσ

end HasType

def Normal {S : Type u} (M : Expr S) : Prop := ∀ N, ¬ Beta M N

namespace HasType

variable {S : Type u} {P : Specification S}

/-- Generation is stated up to conversion, without any functionality premise. -/
def Generation (P : Specification S) (Γ : List (Expr S))
    (M T : Expr S) : Prop :=
  match M with
  | .var n => ∃ A, Lookup Γ n A ∧ Converts T A
  | .sort s => ∃ t, P.axioms s t ∧ Converts T (.sort t)
  | .app l f a => ∃ A B, HasType P Γ f (.pi l A B) ∧ HasType P Γ a A ∧
      Converts T (B.instantiate a)
  | .lam l A b => ∃ B s, HasType P (A :: Γ) b B ∧
      HasType P Γ (.pi l A B) (.sort s) ∧ Converts T (.pi l A B)
  | .pi _l A B => ∃ s₁ s₂ s₃, HasType P Γ A (.sort s₁) ∧
      HasType P (A :: Γ) B (.sort s₂) ∧ P.rule s₁ s₂ s₃ ∧
      Converts T (.sort s₃)

end HasType

/-- Modes are a separate syntax discipline on the labelled PTS. This keeps
metatheory independent of mode well-formedness and proves preservation below. -/
def modeCons (m : Mode) (γ : Nat → Mode) : Nat → Mode
  | 0 => m
  | n+1 => γ n

inductive WellModed {S : Type u} : (Nat → Mode) → Expr S → Mode → Prop
  | var {γ} (n) : WellModed γ (.var n) (γ n)
  | sort {γ} (s) : WellModed γ (.sort s) .data
  | app {γ l f a} : WellModed γ f l.result → WellModed γ a l.domain →
      WellModed γ (.app l f a) l.result
  | lam {γ l A b} : WellModed γ A .data → WellModed (modeCons l.domain γ) b l.result →
      WellModed γ (.lam l A b) l.result
  | pi {γ l A B} : WellModed γ A .data → WellModed (modeCons l.domain γ) B .data →
      WellModed γ (.pi l A B) .data

namespace WellModed
variable {S : Type u} {γ δ : Nat → Mode} {M : Expr S} {m : Mode}
theorem rename (h : WellModed γ M m) (ρ : Nat → Nat) (hρ : ∀ n, δ (ρ n) = γ n) :
    WellModed δ (M.rename ρ) m := by
  have hlift {γ δ : Nat → Mode} (ρ : Nat → Nat) (hρ : ∀ n, δ (ρ n) = γ n)
      (i : Mode) : ∀ n, modeCons i δ (Expr.liftRen ρ n) = modeCons i γ n := by
    intro n; cases n with
    | zero => rfl
    | succ n => exact hρ n
  induction h generalizing δ ρ with
  | var n => simpa only [Expr.rename, hρ n] using WellModed.var (γ := δ) (ρ n)
  | sort s => exact .sort s
  | app hf ha ihf iha => exact .app (ihf ρ hρ) (iha ρ hρ)
  | lam hA hb ihA ihb => exact .lam (ihA ρ hρ) (ihb _ (hlift ρ hρ _))
  | pi hA hB ihA ihB => exact .pi (ihA ρ hρ) (ihB _ (hlift ρ hρ _))

end WellModed

namespace Expr
variable {S : Type u}
def weight : Expr S → Nat
  | .var _ | .sort _ => 1
  | .app _ f a => 1 + f.weight + a.weight
  | .lam _ A b => 1 + A.weight + b.weight
  | .pi _ A B => 1 + A.weight + B.weight

/-- A terminal contains data/data labels only. -/
inductive AllData : Expr S → Prop
  | var (n) : AllData (.var n)
  | sort (s) : AllData (.sort s)
  | app {f a} : AllData f → AllData a → AllData (.app .dd f a)
  | lam {A b} : AllData A → AllData b → AllData (.lam .dd A b)
  | pi {A B} : AllData A → AllData B → AllData (.pi .dd A B)

namespace AllData
theorem rename {M : Expr S} (h : AllData M) (ρ : Nat → Nat) : AllData (M.rename ρ) := by
  induction h generalizing ρ with
  | var n => exact .var _
  | sort s => exact .sort s
  | app hf ha ihf iha => exact .app (ihf ρ) (iha ρ)
  | lam hA hb ihA ihb => exact .lam (ihA ρ) (ihb _)
  | pi hA hB ihA ihB => exact .pi (ihA ρ) (ihB _)
end AllData

/-- A positive telescope ending in an all-data terminal. The source uses
constant telescopes; the no-normal-proof argument also permits dependency. -/
inductive Positive : Expr S → Prop
  | terminal {T} : AllData T → Positive T
  | step (D) {E} : Positive E → Positive (.pi .dp D E)

/-- The normal target family used in the no-normal-proof obstruction. -/
def Target (T : Expr S) : Prop := Positive T ∧ PureTypeSystem.Normal T.erase

inductive Neutral : Expr S → Prop
  | var (n) : Neutral (.var n)
  | app {l f a} : Neutral f → Neutral (.app l f a)
end Expr

/-- Only proof variables are constrained. Each is a proof/proof converter
whose first argument is one of the positive normal targets. This includes
exactly the context shape used by the source, and is stable under data
extensions. No converter result is assumed inhabited. -/
def ProofContext {S : Type u} (Γ : List (Expr S)) (γ : Nat → Mode) : Prop :=
  ∀ n A, Lookup Γ n A → γ n = .proof →
    ∃ R F, A = .pi .pp R F ∧ R.Target

end PureTypeSystem.Labelled

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Wrappers
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate _root_.OAI.PureTypeSystem.instCountableExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/- Concrete labelled term operations for wrappers. -/
namespace PureTypeSystem.Labelled
universe u

namespace Expr
variable {S : Type u}
def data (M : PureTypeSystem.Expr S) : Expr S :=
  match M with
  | .var n => .var n
  | .sort s => .sort s
  | .app f a => .app .dd (data f) (data a)
  | .lam A b => .lam .dd (data A) (data b)
  | .pi A B => .pi .dd (data A) (data B)

@[simp] theorem erase_data (M : PureTypeSystem.Expr S) : (Expr.data M).erase = M := by
  induction M <;> simp_all [data, erase]

@[simp] theorem data_rename (M : PureTypeSystem.Expr S) (ρ : Nat → Nat) :
    (Expr.data (M.rename ρ)) = (Expr.data M).rename ρ := by
  induction M generalizing ρ <;> simp_all [data, rename, PureTypeSystem.Expr.rename]

@[simp] theorem data_subst (M : PureTypeSystem.Expr S) (σ : Nat → PureTypeSystem.Expr S) :
    (Expr.data (M.subst σ)) = (Expr.data M).subst (data ∘ σ) := by
  have hl (σ : Nat → PureTypeSystem.Expr S) :
      data ∘ PureTypeSystem.Expr.liftSub σ = liftSub (data ∘ σ) := by
    funext n; cases n <;> simp [PureTypeSystem.Expr.liftSub, liftSub, data]
  induction M generalizing σ <;>
    simp_all only [data, subst, PureTypeSystem.Expr.subst, Function.comp_apply]

@[simp] theorem data_instantiate (b a : PureTypeSystem.Expr S) :
    (Expr.data (b.instantiate a)) = (Expr.data b).instantiate (Expr.data a) := by
  have h : data ∘ PureTypeSystem.Expr.single a = single (Expr.data a) := by
    funext n; cases n <;> rfl
  simp only [PureTypeSystem.Expr.instantiate, data_subst, h, instantiate]

theorem data_allData (M : PureTypeSystem.Expr S) : (Expr.data M).AllData := by
  induction M with
  | var n => exact .var n
  | sort s => exact .sort s
  | app f a hf ha => exact .app hf ha
  | lam A b hA hb => exact .lam hA hb
  | pi A B hA hB => exact .pi hA hB

/-- Nondependent labelled arrow; its codomain is shifted, not captured. -/
def arrow (l : Label) (A B : Expr S) : Expr S := .pi l A (B.rename Nat.succ)
def constLam (l : Label) (A b : Expr S) : Expr S := .lam l A (b.rename Nat.succ)

@[simp] theorem arrow_rename (l : Label) (A B : Expr S) (ρ : Nat → Nat) :
    (arrow l A B).rename ρ = arrow l (A.rename ρ) (B.rename ρ) := by
  simp only [arrow, rename, rename_comp]
  rfl

@[simp] theorem arrow_subst (l : Label) (A B : Expr S) (σ : Nat → Expr S) :
    (arrow l A B).subst σ = arrow l (A.subst σ) (B.subst σ) := by
  simp only [arrow, subst, subst_rename, rename_subst]
  rfl

@[simp] theorem constLam_rename (l : Label) (A b : Expr S) (ρ : Nat → Nat) :
    (constLam l A b).rename ρ = constLam l (A.rename ρ) (b.rename ρ) := by
  simp only [constLam, rename, rename_comp]
  rfl

@[simp] theorem constLam_subst (l : Label) (A b : Expr S) (σ : Nat → Expr S) :
    (constLam l A b).subst σ = constLam l (A.subst σ) (b.subst σ) := by
  simp only [constLam, subst, subst_rename, rename_subst]
  rfl

@[simp] theorem instantiate_raise (M a : Expr S) : (M.rename Nat.succ).instantiate a = M :=
  subst_lift_single M a
end Expr

namespace Beta
variable {S : Type u} {M N : PureTypeSystem.Expr S}
theorem data (h : PureTypeSystem.Beta M N) : Beta (Expr.data M) (Expr.data N) := by
  induction h with
  | head A b a =>
      simpa only [Expr.data, Expr.data_instantiate] using
        (Beta.head .dd (Expr.data A) (Expr.data b) (Expr.data a))
  | app_left h ih => exact .app_left ih
  | app_right h ih => exact .app_right ih
  | lam_domain h ih => exact .lam_domain ih
  | lam_body h ih => exact .lam_body ih
  | pi_domain h ih => exact .pi_domain ih
  | pi_body h ih => exact .pi_body ih
end Beta
namespace Converts
variable {S : Type u} {M N : PureTypeSystem.Expr S}
theorem data (h : PureTypeSystem.Converts M N) : Converts (Expr.data M) (Expr.data N) := by
  induction h with
  | rel a b h => exact .rel _ _ (Beta.data h)
  | refl a => exact .refl _
  | symm a b h ih => exact .symm _ _ ih
  | trans a b c h h' ih ih' => exact .trans _ _ _ ih ih'
end Converts

namespace HasType
variable {S : Type u} {P : Specification S}
theorem data {Γ : List (PureTypeSystem.Expr S)} {M A : PureTypeSystem.Expr S}
    (h : PureTypeSystem.HasType P Γ M A) : HasType P (Γ.map Expr.data) (Expr.data M) (Expr.data A) := by
  induction h with
  | ax h => exact .ax h
  | var h ih => simpa only [List.map_cons, Expr.data, Expr.data_rename] using HasType.var ih
  | weaken h hA ih ihA =>
      simpa only [List.map_cons, Expr.data_rename] using HasType.weaken ih ihA
  | product hA hB hr ihA ihB => exact .product ihA ihB hr
  | abstraction hb hp ihb ihp => exact .abstraction ihb ihp
  | application hf ha ihf iha =>
      simpa only [Expr.data, Expr.data_instantiate] using HasType.application ihf iha
  | conversion h hA hc ih ihA => exact .conversion ih ihA (Converts.data hc)

end HasType

/-- Sorting at a profile records all source sorting judgments, not an exact
profile assertion; wrappers intentionally permit profile growth. -/
def SortedAt {S : Type u} (P : Specification S) (Γ : List (Expr S))
    (A : Expr S) (I : Set S) : Prop := ∀ s ∈ I, HasType P Γ A (.sort s)

end PureTypeSystem.Labelled

/-! Finite simultaneous normal data witnesses.
Feasibility is semantic, so these lemmas do not assume a profile-generation
conjecture. The extra inhabitants are genuine fresh context variables. -/
namespace PureTypeSystem

section
universe u

namespace Lookup
variable {S : Type u} {Γ Δ : List (Expr S)} {n : Nat} {A : Expr S}
theorem append_right (h : Lookup Γ n A) (Δ : List (Expr S)) : Lookup (Γ ++ Δ) n A := by
  induction h with
  | zero => exact .zero _ _
  | succ C h ih => exact .succ C ih

theorem append_left (h : Lookup Δ n A) (Γ : List (Expr S)) :
    Lookup (Γ ++ Δ) (n + Γ.length) (A.rename (fun i => i + Γ.length)) := by
  induction Γ with
  | nil => simpa only [List.length_nil, List.nil_append, Nat.add_zero, ← Function.id_def, Expr.rename_id] using h
  | cons B Γ ih =>
      have hh := Lookup.succ B ih
      simpa only [List.length_cons, List.cons_append, Expr.rename_comp, Function.comp_def,
        Nat.add_assoc, Nat.succ_eq_add_one] using hh
end Lookup

namespace ValidContext
variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)}
theorem append (hΓ : ValidContext P Γ) (hΔ : ValidContext P Δ) : ValidContext P (Γ ++ Δ) := by
  induction hΓ with
  | nil => exact hΔ
  | cons hΓ hA ih =>
      apply ValidContext.cons ih
      have hh := hA.rename ih id (fun n A hn => by
        simpa only [Expr.rename_id, id_eq] using HasType.lookup ih (hn.append_right Δ))
      simpa only [Expr.rename_id] using hh
end ValidContext

namespace HasType
variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)} {M A : Expr S}
theorem append_right (h : HasType P Γ M A) (hΔ : ValidContext P Δ) :
    HasType P (Γ ++ Δ) M A := by
  have hv := h.valid.append hΔ
  simpa only [Expr.rename_id] using h.rename hv id (fun n B hn => by
    simpa only [Expr.rename_id, id_eq] using HasType.lookup hv (hn.append_right Δ))

theorem append_left (h : HasType P Δ M A) (hΓ : ValidContext P Γ) :
    HasType P (Γ ++ Δ) (M.rename (fun i => i + Γ.length)) (A.rename (fun i => i + Γ.length)) :=
  h.rename (hΓ.append h.valid) _ (fun _ _ hn => HasType.lookup (hΓ.append h.valid) (hn.append_left Γ))
end HasType

/-- An actual normal witness of a feasible profile, with a declared inhabitant.
All the sorting judgments, rather than one selected sort, are retained. -/
def HasWitness {S : Type u} (P : Specification S) (Γ : List (Expr S)) (I : Set S) : Prop :=
  ∃ T e : Expr S, Normal T ∧ (∀ s ∈ I, HasType P Γ T (.sort s)) ∧ HasType P Γ e T

namespace HasWitness
variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)} {I : Set S}
theorem append_left (h : HasWitness P Δ I) (hΓ : ValidContext P Γ) : HasWitness P (Γ ++ Δ) I := by
  obtain ⟨T, e, hT, hs, he⟩ := h
  exact ⟨_, _, hT.rename _, fun s hi => (hs s hi).append_left hΓ, he.append_left hΓ⟩

theorem append_right (h : HasWitness P Γ I) (hΔ : ValidContext P Δ) : HasWitness P (Γ ++ Δ) I := by
  obtain ⟨T, e, hT, hs, he⟩ := h
  exact ⟨T, e, hT, fun s hi => (hs s hi).append_right hΔ, he.append_right hΔ⟩
end HasWitness

namespace FeasibleProfile
variable {S : Type u} {P : Specification S} {I : Set S}
theorem witness (h : FeasibleProfile P I) : ∃ Γ, ValidContext P Γ ∧ HasWitness P Γ I := by
  obtain ⟨⟨s, hs⟩, Γ, T, hΓ, hn, hp⟩ := h
  have ht : ∀ a ∈ I, HasType P Γ T (.sort a) := by
    intro a ha
    rw [← hp] at ha
    simpa only [Profile, Set.mem_ofPred_eq, Expr.normalForm_of_normal hn] using ha
  exact ⟨T :: Γ, .cons hΓ (ht s hs), _, _, hn.rename _,
    fun a ha => .weaken (ht a ha) (ht s hs), .var (ht s hs)⟩

theorem finite_witnesses (F : Finset (Set S)) (hF : ∀ I ∈ F, FeasibleProfile P I) :
    ∃ Γ, ValidContext P Γ ∧ ∀ I ∈ F, HasWitness P Γ I := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨[], .nil, by simp⟩
  | @insert I F hi ih =>
      obtain ⟨Γ, hv, hw⟩ := ih (fun J hJ => hF J (Finset.mem_insert_of_mem hJ))
      obtain ⟨Δ, hd, hI⟩ := (hF I (Finset.mem_insert_self _ _)).witness
      refine ⟨Δ ++ Γ, hd.append hv, ?_⟩
      intro J hJ
      rcases Finset.mem_insert.mp hJ with rfl | hJ
      · exact hI.append_right hv
      · exact (hw J hJ).append_left hd
end FeasibleProfile

namespace Labelled
/-- The data context has no proof-mode declarations. Its finite witness terms
are literal all-data embeddings and their erased types are normal. -/
structure DataWitnessContext {S : Type u} (P : Specification S) (F : Finset (Set S)) where
  context : List (Expr S)
  valid : ValidContext P context
  allData : ∀ A ∈ context, A.AllData
  witness : ∀ I ∈ F, ∃ T e : Expr S, T.AllData ∧ e.AllData ∧
    PureTypeSystem.Normal T.erase ∧ SortedAt P context T I ∧ HasType P context e T

namespace ValidContext
variable {S : Type u} {P : Specification S} {Γ : List (PureTypeSystem.Expr S)}
theorem data (h : PureTypeSystem.ValidContext P Γ) : ValidContext P (Γ.map Expr.data) := by
  induction h with
  | nil => exact .nil
  | cons hΓ hA ih => exact .cons ih (HasType.data hA)
end ValidContext

noncomputable def DataWitnessContext.ofFeasible {S : Type u} {P : Specification S}
    (F : Finset (Set S)) (hF : ∀ I ∈ F, FeasibleProfile P I) : DataWitnessContext P F := by
  let hh := FeasibleProfile.finite_witnesses F hF
  let Γ := hh.choose
  have hv : PureTypeSystem.ValidContext P Γ := hh.choose_spec.1
  refine ⟨Γ.map Expr.data, ValidContext.data hv, ?_, ?_⟩
  · intro A hA
    obtain ⟨B, _, rfl⟩ := List.mem_map.mp hA
    exact Expr.data_allData B
  · intro I hi
    obtain ⟨T, e, hT, hs, he⟩ := hh.choose_spec.2 I hi
    exact ⟨Expr.data T, Expr.data e, Expr.data_allData T, Expr.data_allData e,
      by simpa only [Expr.erase_data] using hT, fun s hs' => HasType.data (hs s hs'), HasType.data he⟩

end Labelled
end

/- Finite signed-path choices for channels. -/

end PureTypeSystem

namespace PureTypeSystem.Labelled

section
universe u
open Classical

/-- A legal mode-preserving change of names. No hypotheses about convertibility
or proof existence are packed into the map. -/
structure Embedding {S : Type u} (P : Specification S) (Γ : List (Expr S))
    (γ : Nat → Mode) (Δ : List (Expr S)) (δ : Nat → Mode) where
  names : Nat → Nat
  valid : ValidContext P Δ
  typed : ∀ n A, Lookup Γ n A → HasType P Δ (.var (names n)) (A.rename names)
  modes : ∀ n, δ (names n) = γ n

namespace Embedding
variable {S : Type u} {P : Specification S}
    {Γ Δ Θ : List (Expr S)} {γ δ θ : Nat → Mode}

def refl (hv : ValidContext P Γ) (γ : Nat → Mode) : Embedding P Γ γ Γ γ where
  names := id
  valid := hv
  typed n A hn := by simpa only [Expr.rename_id,id_eq] using HasType.lookup hv hn
  modes _ := rfl

theorem typing (e : Embedding P Γ γ Δ δ) {M A : Expr S} (h : HasType P Γ M A) :
    HasType P Δ (M.rename e.names) (A.rename e.names) := h.rename e.valid e.names e.typed

theorem moded (e : Embedding P Γ γ Δ δ) {M : Expr S} {m : Mode}
    (h : WellModed γ M m) : WellModed δ (M.rename e.names) m := h.rename _ e.modes

def comp (e : Embedding P Γ γ Δ δ) (f : Embedding P Δ δ Θ θ) : Embedding P Γ γ Θ θ where
  names := f.names ∘ e.names
  valid := f.valid
  typed n A hn := by simpa only [Expr.rename_comp,Expr.rename,Function.comp_apply] using f.typing (e.typed n A hn)
  modes n := (f.modes _).trans (e.modes n)

def cons {A : Expr S} {s : S} (hA : HasType P Γ A (.sort s)) (d : Mode) :
    Embedding P Γ γ (A :: Γ) (modeCons d γ) where
  names := Nat.succ
  valid := .cons hA.valid hA
  typed _n _B hn := .weaken (HasType.lookup hA.valid hn) hA
  modes _ := rfl

def lift (e : Embedding P Γ γ Δ δ) {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (d : Mode) :
    Embedding P (A :: Γ) (modeCons d γ) (A.rename e.names :: Δ) (modeCons d δ) where
  names := Expr.liftRen e.names
  valid := .cons e.valid (e.typing hA)
  typed n B hn := by
    cases hn with
    | zero =>
      simpa only [Expr.rename_comp,Expr.liftRen,PureTypeSystem.Expr.liftRen,Function.comp_def,Expr.rename] using HasType.var (e.typing hA)
    | succ D hn =>
      simpa only [Expr.rename_comp,Expr.liftRen,PureTypeSystem.Expr.liftRen,Function.comp_def,Expr.rename] using HasType.weaken (e.typed _ _ hn) (e.typing hA)
  modes n := by cases n with | zero => rfl | succ n => exact e.modes n
end Embedding

/-- All finite feasible witnesses with their one fixed choice of terminal type.
The types remain fixed (up to renaming) during proof-context extensions. -/
structure WitnessFamily {S : Type u} (P : Specification S) (Γ : List (Expr S))
    (γ : Nat → Mode) where
  type : Set S → Expr S
  value : Set S → Expr S
  allData : ∀ I, FeasibleProfile P I → (type I).AllData
  normal : ∀ I, FeasibleProfile P I → PureTypeSystem.Normal (type I).erase
  sorted : ∀ I, FeasibleProfile P I → SortedAt P Γ (type I) I
  typed : ∀ I, FeasibleProfile P I → HasType P Γ (value I) (type I)
  type_mode : ∀ I, FeasibleProfile P I → WellModed γ (type I) .data
  value_mode : ∀ I, FeasibleProfile P I → WellModed γ (value I) .data

namespace WitnessFamily
variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)} {γ δ : Nat → Mode}

def rename (W : WitnessFamily P Γ γ) (e : Embedding P Γ γ Δ δ) : WitnessFamily P Δ δ where
  type I := (W.type I).rename e.names
  value I := (W.value I).rename e.names
  allData I hI := (W.allData I hI).rename _
  normal I hI := by simpa only [Expr.erase_rename] using (W.normal I hI).rename e.names
  sorted I hI s hs := e.typing (W.sorted I hI s hs)
  typed I hI := e.typing (W.typed I hI)
  type_mode I hI := e.moded (W.type_mode I hI)
  value_mode I hI := e.moded (W.value_mode I hI)

end WitnessFamily

/-- A term transformer under one temporary proof input. No product rule is
postulated for its input/output pair; that rule generally does not exist. -/
def Transfer {S : Type u} (P : Specification S) (Γ : List (Expr S)) (γ : Nat → Mode)
    (A B : Expr S) : Prop :=
  ∃ t, HasType P (A :: Γ) t (B.rename Nat.succ) ∧ WellModed (modeCons .proof γ) t .proof

namespace Transfer
variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)} {γ δ : Nat → Mode}
    {A B C D : Expr S} {s t r : S}

theorem rename (h : Transfer P Γ γ A B) (e : Embedding P Γ γ Δ δ)
    (hA : HasType P Γ A (.sort s)) : Transfer P Δ δ (A.rename e.names) (B.rename e.names) := by
  obtain ⟨M,ht,hm⟩ := h
  refine ⟨M.rename (Expr.liftRen e.names),?_,(e.lift hA .proof).moded hm⟩
  simpa only [Embedding.lift,Expr.rename_comp,Expr.liftRen,PureTypeSystem.Expr.liftRen,Function.comp_def] using (e.lift hA .proof).typing ht

end Transfer

end

section
universe u
variable {S : Type u} {P : Specification S}

/-- An actual labelled inhabitant, retaining its typing and proof mode. -/
def Proves (P : Specification S) (Γ : List (Expr S)) (γ : Nat → Mode) (A : Expr S) : Prop :=
  ∃ p, HasType P Γ p A ∧ WellModed γ p .proof

end

universe u
open Classical
variable {S : Type u} {P : Specification S}

/-- The converter-routing construction retains its finite admissible context,
its exact renaming of the original input, and the normal positive carried type. -/
def Carries (Γ : List (Expr S)) (γ : Nat → Mode) (T : Expr S) (J : Set S) : Prop :=
  ∃ Δ δ, ∃ e : Embedding P Γ γ Δ δ, ProofContext Δ δ ∧ ∃ U : Expr S,
    U.Target ∧ WellModed δ U .data ∧ SortedAt P Δ U J ∧
    Transfer P Δ δ (T.rename e.names) U

/-- The fixed terminals are exactly the codomains of the internal domain edges
of the logic SCC. This includes the chosen logical bottom. -/
def TerminalProfile (P : Specification S) (C : Set (Set S)) (J : Set S) : Prop :=
  ∃ I K, ProfileTriple P I J K ∧ I ∈ C ∧ K ∈ C

theorem TerminalProfile.feasible {C : Set (Set S)} {J : Set S}
    (h : TerminalProfile P C J) : FeasibleProfile P J := by
  obtain ⟨I,K,ht,_,_⟩ := h
  exact ht.codomain

/-- Uniform proof transport records open callbacks, not a meta-level implication
between propositions. Every operation returns an actual typed term. -/
def ProofParity {Γ : List (Expr S)} {γ : Nat → Mode}
    (W : WitnessFamily P Γ γ) (C : Set (Set S)) (A B : Expr S) (b : Bool) : Prop :=
  ∀ (Δ : List (Expr S)) (δ : Nat → Mode) (e : Embedding P Γ γ Δ δ),
    match b with
    | false =>
      (Proves P Δ δ (A.rename e.names) → Proves P Δ δ (B.rename e.names)) ∧
      (∀ J, TerminalProfile P C J →
        Transfer P Δ δ (A.rename e.names) ((W.type J).rename e.names) →
        Transfer P Δ δ (B.rename e.names) ((W.type J).rename e.names))
    | true =>
      (∀ J, TerminalProfile P C J →
        Transfer P Δ δ (A.rename e.names) ((W.type J).rename e.names) →
        Proves P Δ δ (B.rename e.names)) ∧
      (∀ J, TerminalProfile P C J → Proves P Δ δ (A.rename e.names) →
        Transfer P Δ δ (B.rename e.names) ((W.type J).rename e.names))

/-- A continuation is tested after every legal extension; callbacks are actual
open terms with one proof input, not arbitrary functions on inhabitation. -/
def Continuation {Γ : List (Expr S)} {γ : Nat → Mode} (W : WitnessFamily P Γ γ)
    (C : Set (Set S)) (Q : Expr S) : Prop :=
  ∀ (Δ : List (Expr S)) (δ : Nat → Mode) (e : Embedding P Γ γ Δ δ)
    J, TerminalProfile P C J →
    Transfer P Δ δ (Q.rename e.names) ((W.type J).rename e.names) →
    Proves P Δ δ ((W.type J).rename e.names)

/-- The extraction property proved for sorted stable telescopes. It is not an
extra PTS rule: the following constructors explicitly build its proof terms. -/
def StableExtraction {Γ : List (Expr S)} {γ : Nat → Mode} (W : WitnessFamily P Γ γ)
    (C : Set (Set S)) (Q : Expr S) : Prop :=
  ∀ (Δ : List (Expr S)) (δ : Nat → Mode) (e : Embedding P Γ γ Δ δ),
    Continuation (W.rename e) C (Q.rename e.names) → Proves P Δ δ (Q.rename e.names)

/-- Fixed hygienic wrapper syntax. The code is selected once from a path, never
reselected when an input is substituted or its sorting profile grows. -/
inductive ProofWrapper (S : Type u)
  | identity
  | positive : ProofWrapper S → Expr S → ProofWrapper S
  | negative : ProofWrapper S → Expr S → ProofWrapper S

namespace ProofWrapper

def apply : ProofWrapper S → Expr S → Expr S
  | .identity,T => T
  | .positive R D,T => Expr.arrow .dp D (R.apply T)
  | .negative R F,T => Expr.arrow .pp (R.apply T) F

def rename (ρ : Nat → Nat) : ProofWrapper S → ProofWrapper S
  | .identity => .identity
  | .positive R D => .positive (R.rename ρ) (D.rename ρ)
  | .negative R F => .negative (R.rename ρ) (F.rename ρ)

def subst (σ : Nat → Expr S) : ProofWrapper S → ProofWrapper S
  | .identity => .identity
  | .positive R D => .positive (R.subst σ) (D.subst σ)
  | .negative R F => .negative (R.subst σ) (F.subst σ)

def containsNegative : ProofWrapper S → Bool
  | .identity => false
  | .positive R _ => R.containsNegative
  | .negative _ _ => true

/-- A path certificate retaining exactly its terminals, witness types and edge
roles. Inclusion is a literal identity; there is no type-level cast. -/
inductive Formed {Γ : List (Expr S)} {γ : Nat → Mode} (W : WitnessFamily P Γ γ)
    (C : Set (Set S)) (I : Set S) : Set S → Bool → ProofWrapper S → Prop
  | identity : Formed W C I I false .identity
  | inclusion {J K b R} : Formed W C I J b R → K ⊆ J → Formed W C I K b R
  | positive {A J K b R} : Formed W C I J b R → ProfileTriple P A J K →
      Formed W C I K b (.positive R (W.type A))
  | negative {J B K b R} : Formed W C I J b R → ProfileTriple P J B K → J ∈ C → K ∈ C →
      Formed W C I K (!b) (.negative R (W.type B))

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {W : WitnessFamily P Γ γ}
    {C : Set (Set S)} {I J K : Set S} {a b : Bool} {R : ProofWrapper S}

theorem rename {Δ : List (Expr S)} {δ : Nat → Mode}
    (h : Formed W C I J b R) (e : Embedding P Γ γ Δ δ) :
    Formed (W.rename e) C I J b (R.rename e.names) := by
  induction h with
  | identity => exact .identity
  | inclusion h hh ih => exact ih.inclusion hh
  | positive h ht ih => exact ih.positive ht
  | negative h ht hi hk ih => exact ih.negative ht hi hk

end Formed
end ProofWrapper
end PureTypeSystem.Labelled

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Logic
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate _root_.OAI.PureTypeSystem.instCountableExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.Labelled

section
universe u
open Classical
variable {S : Type u} {P : Specification S}

/-- Quantification uses the displayed direct-vertex annotation throughout. -/
structure QuantifierRoute {Γ : List (Expr S)} {γ : Nat → Mode}
    (W : WitnessFamily P Γ γ) (C : Set (Set S)) (b I : Set S) where
  codomain : Set S
  product : Set S
  triple : ProfileTriple P I codomain product
  inCode : ProofWrapper S
  inFormed : inCode.Formed W C b codomain false
  outCode : ProofWrapper S
  outFormed : outCode.Formed W C product b false

namespace QuantifierRoute
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {W : WitnessFamily P Γ γ}
    {C : Set (Set S)} {b I : Set S}
def rename (R : QuantifierRoute W C b I) (e : Embedding P Γ γ Δ δ) :
    QuantifierRoute (W.rename e) C b I where
  codomain := R.codomain
  product := R.product
  triple := R.triple
  inCode := R.inCode.rename e.names
  inFormed := R.inFormed.rename e
  outCode := R.outCode.rename e.names
  outFormed := R.outFormed.rename e

end QuantifierRoute

/-- Actual finite ambient context data for the source's classical logical
calculus. All fields are constructed below from fixed graph paths and terms. -/
structure LogicSetup (P : Specification S) (Γ : List (Expr S)) (γ : Nat → Mode)
    (C : Set (Set S)) where
  witnesses : WitnessFamily P Γ γ
  converters : ∀ J J', TerminalProfile P C J → TerminalProfile P C J' →
    Transfer P Γ γ (witnesses.type J) (witnesses.type J')
  base : Set S
  domain : Set S
  product : Set S
  triple : ProfileTriple P domain base product
  domain_mem : domain ∈ C
  base_mem : base ∈ C
  product_mem : product ∈ C
  inCode : ProofWrapper S
  inFormed : inCode.Formed witnesses C base domain false
  outCode : ProofWrapper S
  outFormed : outCode.Formed witnesses C product base false
  quantifiers : ∀ I, DirectLayer P C I → QuantifierRoute witnesses C base I

namespace LogicSetup

section
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}

def rename (L : LogicSetup P Γ γ C) (e : Embedding P Γ γ Δ δ) : LogicSetup P Δ δ C where
  witnesses := L.witnesses.rename e
  converters J J' hJ hJ' := by
    obtain ⟨s,hs⟩ := hJ.feasible.1
    exact (L.converters J J' hJ hJ').rename e (L.witnesses.sorted J hJ.feasible s hs)
  base := L.base
  domain := L.domain
  product := L.product
  triple := L.triple
  domain_mem := L.domain_mem
  base_mem := L.base_mem
  product_mem := L.product_mem
  inCode := L.inCode.rename e.names
  inFormed := L.inFormed.rename e
  outCode := L.outCode.rename e.names
  outFormed := L.outFormed.rename e
  quantifiers I hI := (L.quantifiers I hI).rename e

def bottom (L : LogicSetup P Γ γ C) : Expr S := L.witnesses.type L.base

def Formula (L : LogicSetup P Γ γ C) (A : Expr S) : Prop :=
  SortedAt P Γ A L.base ∧ WellModed γ A .data ∧ StableExtraction L.witnesses C A

variable (L : LogicSetup P Γ γ C) {A B : Expr S}

def imp (A B : Expr S) : Expr S :=
  L.outCode.apply (Expr.arrow .pp (L.inCode.apply A) B)

end

variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I : Set S} {T Q : Expr S} {s : S}

/-- The route is selected by its original direct annotation, not by a later
sorting profile of the domain. -/
def all (R : QuantifierRoute L.witnesses C L.base I) (T Q : Expr S) : Expr S :=
  R.outCode.apply (.pi .dp T ((R.inCode.rename Nat.succ).apply Q))

end LogicSetup
end

section
universe u
variable {S : Type u} {P : Specification S}

/-- Logical equivalence retains two actual typed open proof transformers.
No data term is ever replaced using this relation. -/
def Equivalent (P : Specification S) (Γ : List (Expr S)) (γ : Nat → Mode) (A B : Expr S) : Prop :=
  Transfer P Γ γ A B ∧ Transfer P Γ γ B A

/-- A fixed all-positive data path, with its original dummy argument values. -/
inductive PositiveDataWrapper (S : Type u)
  | identity
  | step : PositiveDataWrapper S → Expr S → Expr S → PositiveDataWrapper S
namespace PositiveDataWrapper

def apply : PositiveDataWrapper S → Expr S → Expr S
  | .identity,T => T
  | .step R D _,T => Expr.arrow .dd D (R.apply T)

def inject : PositiveDataWrapper S → Expr S → Expr S
  | .identity,t => t
  | .step R D _,t => Expr.constLam .dd D (R.inject t)

def project : PositiveDataWrapper S → Expr S → Expr S
  | .identity,w => w
  | .step R _ e,w => R.project (.app .dd w e)

def rename (ρ : Nat → Nat) : PositiveDataWrapper S → PositiveDataWrapper S
  | .identity => .identity
  | .step R D e => .step (R.rename ρ) (D.rename ρ) (e.rename ρ)

def subst (σ : Nat → Expr S) : PositiveDataWrapper S → PositiveDataWrapper S
  | .identity => .identity
  | .step R D e => .step (R.subst σ) (D.subst σ) (e.subst σ)

inductive Formed {Γ : List (Expr S)} {γ : Nat → Mode} (W : WitnessFamily P Γ γ)
    (I : Set S) : Set S → PositiveDataWrapper S → Prop
  | identity : Formed W I I .identity
  | inclusion {J K R} : Formed W I J R → K ⊆ J → Formed W I K R
  | positive {A J K R} : Formed W I J R → ProfileTriple P A J K →
      Formed W I K (.step R (W.type A) (W.value A))
end PositiveDataWrapper

structure DataTail (S : Type u) where
  sort : S
  positive : PositiveDataWrapper S
  encode : ProofWrapper S
  decode : ProofWrapper S

namespace DataTail

def carrier (U : DataTail S) : Expr S := U.positive.apply (.sort U.sort)
def send (U : DataTail S) (Q : Expr S) : Expr S := U.positive.inject (U.encode.apply Q)
def read (U : DataTail S) (w : Expr S) : Expr S := U.decode.apply (U.positive.project w)
def rename (U : DataTail S) (ρ : Nat → Nat) : DataTail S :=
  ⟨U.sort,U.positive.rename ρ,U.encode.rename ρ,U.decode.rename ρ⟩
def subst (U : DataTail S) (σ : Nat → Expr S) : DataTail S :=
  ⟨U.sort,U.positive.subst σ,U.encode.subst σ,U.decode.subst σ⟩

structure Formed {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) (J : Set S) (U : DataTail S) : Prop where
  mem : {U.sort} ∈ C
  nonempty : (AxProfile P U.sort).Nonempty
  positive : U.positive.Formed L.witnesses (AxProfile P U.sort) J
  encode : U.encode.Formed L.witnesses C L.base {U.sort} false
  decode : U.decode.Formed L.witnesses C {U.sort} L.base false
  negative : U.decode.containsNegative = true

end DataTail
end

section
universe u
variable {S : Type u}

/-- A retained data path, with fixed tail codes and fixed positive witnesses. -/
inductive DataWrapper (S : Type u) : Bool → Type u
  | identity : DataWrapper S false
  | positive {b} : DataWrapper S b → Expr S → Expr S → DataWrapper S b
  | negative {b} : DataWrapper S b → DataTail S → DataWrapper S (!b)
namespace DataWrapper

def apply {b} : DataWrapper S b → Expr S → Expr S
  | .identity,T => T
  | .positive R D _,T => Expr.arrow .dd D (R.apply T)
  | .negative R U,T => Expr.arrow .dd (R.apply T) U.carrier

def rename {b} (ρ : Nat → Nat) : DataWrapper S b → DataWrapper S b
  | .identity => .identity
  | .positive R D e => .positive (R.rename ρ) (D.rename ρ) (e.rename ρ)
  | .negative R U => .negative (R.rename ρ) (U.rename ρ)

def subst {b} (σ : Nat → Expr S) : DataWrapper S b → DataWrapper S b
  | .identity => .identity
  | .positive R D e => .positive (R.subst σ) (D.subst σ) (e.subst σ)
  | .negative R U => .negative (R.subst σ) (U.subst σ)

def depth {b} : DataWrapper S b → Nat
  | .identity => 0
  | .positive R _ _ => R.depth + 1
  | .negative R _ => R.depth + 1

theorem depth_rename {b} (R : DataWrapper S b) (ρ : Nat → Nat) :
    (R.rename ρ).depth = R.depth := by
  induction R <;> simp_all only [rename,depth]

def argRen (b : Bool) (ρ : Nat → Nat) : Nat → Nat := if b then Expr.liftRen ρ else ρ
def argSub (b : Bool) (σ : Nat → Expr S) : Nat → Expr S := if b then Expr.liftSub σ else σ

mutual
  def build {b} : DataWrapper S b → Expr S → Expr S → Expr S
    | .identity,_,a => a
    | .positive R D _,T,a => Expr.constLam .dd D (R.build T a)
    | @negative _ b R U,T,a =>
        .lam .dd (R.apply T) ((U.rename Nat.succ).send
          ((R.rename Nat.succ).observe (T.rename Nat.succ) (.var 0)
            (a.rename (argRen (!b) Nat.succ))))
  termination_by R _ _ => R.depth
  decreasing_by all_goals simp [depth_rename,depth]
  def observe {b} : DataWrapper S b → Expr S → Expr S → Expr S → Expr S
    | .identity,_,w,a => a.instantiate w
    | .positive R _ e,T,w,a => R.observe T (.app .dd w e) a
    | .negative R U,T,w,a => U.read (.app .dd w (R.build T a))
  termination_by R _ _ _ => R.depth
  decreasing_by all_goals simp [depth]
end

end DataWrapper
end

universe u
variable {S : Type u} {P : Specification S}

namespace LogicSetup
variable {Γ Δ Θ : List (Expr S)} {γ δ θ : Nat → Mode} {C : Set (Set S)}

/-- A raw callback with uniform stable instances in every subsequent context.
This is an internal syntax interface, not a hypothesis on the PTS. -/
def Family (L : LogicSetup P Γ γ C) (T Q : Expr S) : Prop :=
  ∀ (Δ : List (Expr S)) (δ : Nat → Mode) (e : Embedding P Γ γ Δ δ)
    (a : Expr S), HasType P Δ a (T.rename e.names) → WellModed δ a .data →
    (L.rename e).Formula ((Q.rename (Expr.liftRen e.names)).instantiate a)

/-- Even builders accept a raw data element; odd builders accept a raw callback. -/
def DataArg (L : LogicSetup P Γ γ C) (b : Bool) (T a : Expr S) : Prop :=
  if b then L.Family T a else HasType P Γ a T ∧ WellModed γ a .data

end LogicSetup

namespace DataWrapper
inductive Formed {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) (I : Set S) : (J : Set S) → {b : Bool} → DataWrapper S b → Prop
  | identity : Formed L I I .identity
  | inclusion {J K b} {R : DataWrapper S b} : Formed L I J R → K ⊆ J → Formed L I K R
  | positive {A J K b} {R : DataWrapper S b} : Formed L I J R → ProfileTriple P A J K →
      Formed L I K (.positive R (L.witnesses.type A) (L.witnesses.value A))
  | negative {J B K b} {R : DataWrapper S b} {U : DataTail S} :
      Formed L I J R → ProfileTriple P J B K → U.Formed L B → Formed L I K (.negative R U)

/-- Concatenate retained wrapper syntax, never selecting new positive witnesses. -/
def reindex {b c : Bool} (h : b = c) (R : DataWrapper S b) : DataWrapper S c := h ▸ R
@[simp] theorem apply_reindex {b c : Bool} (h : b = c) (R : DataWrapper S b) (T : Expr S) :
    (reindex h R).apply T = R.apply T := by cases h; rfl
@[simp] theorem rename_reindex {b c : Bool} (h : b = c) (R : DataWrapper S b) (ρ : Nat → Nat) :
    (reindex h R).rename ρ = reindex h (R.rename ρ) := by cases h; rfl

def append {b : Bool} (R : DataWrapper S b) : {c : Bool} → DataWrapper S c → DataWrapper S (b.xor c)
  | _, .identity => reindex (by cases b <;> rfl) R
  | _, .positive Q D e => .positive (R.append Q) D e
  | _, @negative _ c Q U => reindex (by cases b <;> cases c <;> rfl) (.negative (R.append Q) U)

end DataWrapper
end PureTypeSystem.Labelled

/- A small finite compiler for the propositional term construction.
It has no type-theoretic assumptions. -/
namespace FiniteClassical
universe u
inductive Formula (α : Type u) where
  | atom : α → Formula α
  | bot : Formula α
  | imp : Formula α → Formula α → Formula α
  deriving DecidableEq
namespace Formula
variable {α : Type u}
def neg (A : Formula α) := imp A bot
def eval (v : α → Bool) : Formula α → Bool
  | atom a => v a
  | bot => false
  | imp A B => !(A.eval v) || B.eval v

def sign (A : Formula α) (b : Bool) := if b then A else A.neg

def support [DecidableEq α] : Formula α → Finset α
  | atom a => {a}
  | bot => ∅
  | imp A B => A.support ∪ B.support
end Formula
open Formula
variable {α : Type u}

inductive Derives : Set (Formula α) → Formula α → Prop
  | ax {Γ A} : A ∈ Γ → Derives Γ A
  | intro {Γ A B} : Derives (insert A Γ) B → Derives Γ (.imp A B)
  | elim {Γ A B} : Derives Γ (.imp A B) → Derives Γ A → Derives Γ B
  | dne {Γ A} : Derives Γ A.neg.neg → Derives Γ A

end FiniteClassical

namespace PureTypeSystem.Labelled
universe u v
open Classical
variable {S : Type u} {P : Specification S}
namespace LogicSetup
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) {α : Type v}

 def interpret (a : α → Expr S) : FiniteClassical.Formula α → Expr S
  | .atom i => a i
  | .bot => L.bottom
  | .imp A B => L.imp (interpret a A) (interpret a B)

end LogicSetup
end PureTypeSystem.Labelled

namespace FiniteClassical.Formula
universe u
variable {α : Type u}
def conj (A B : Formula α) : Formula α := (A.imp B.neg).neg
def chain (hs : List (Formula α)) (Q : Formula α) : Formula α := hs.foldr .imp Q
end FiniteClassical.Formula

namespace PureTypeSystem.Labelled

section
universe u v
variable {S : Type u} {P : Specification S}
namespace LogicSetup
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C)
def top : Expr S := L.imp L.bottom L.bottom
def neg (A : Expr S) : Expr S := L.imp A L.bottom
def conj (A B : Expr S) : Expr S := L.neg (L.imp A (L.neg B))
def disj (A B : Expr S) : Expr S := L.neg (L.conj (L.neg A) (L.neg B))
def iff (A B : Expr S) : Expr S := L.conj (L.imp A B) (L.imp B A)

end LogicSetup
end

universe u
variable {S : Type u} {P : Specification S}
namespace Expr
/-- Composition of one-variable open terms, preserving the common ambient
context. No logical equivalence is used as a data equality. -/
def compose (f g : Expr S) : Expr S := (f.rename (liftRen Nat.succ)).instantiate g

end Expr

/-- An ordinary raw data callback. Its uniformity is a consequence of the
already proved labelled substitution theorem. -/
def DataMap (P : Specification S) (Γ : List (Expr S)) (γ : Nat → Mode)
    (T U f : Expr S) : Prop :=
  HasType P (T :: Γ) f (U.rename Nat.succ) ∧ WellModed (modeCons .data γ) f .data

namespace DataWrapper

def evalCallback (R : DataWrapper S true) (T w : Expr S) : Expr S :=
  (R.rename Nat.succ).observe (T.rename Nat.succ) (w.rename Nat.succ) (.var 0)

def reencode (R R' : DataWrapper S true) (T w : Expr S) : Expr S :=
  R'.build T (R.evalCallback T w)

def cancelFormula (b : Bool) (a q : Expr S) : Expr S :=
  if b then a.instantiate q else q.instantiate a

end DataWrapper

namespace DataWrapper

def reencodeBody (R R' : DataWrapper S true) (T : Expr S) : Expr S :=
  reencode (R.rename Nat.succ) (R'.rename Nat.succ) (T.rename Nat.succ) (.var 0)

end DataWrapper

/-- Raw code for the already constructed logical operations. This separates
syntax naturality from the dependent typing certificate of a logic setup. -/
structure LogicCode (S : Type u) where
  bottom : Expr S
  into : ProofWrapper S
  out : ProofWrapper S
namespace LogicCode
variable (L : LogicCode S)
def rename (ρ : Nat → Nat) : LogicCode S := ⟨L.bottom.rename ρ,L.into.rename ρ,L.out.rename ρ⟩
def subst (σ : Nat → Expr S) : LogicCode S := ⟨L.bottom.subst σ,L.into.subst σ,L.out.subst σ⟩
def imp (A B : Expr S) := L.out.apply (Expr.arrow .pp (L.into.apply A) B)
def neg (A : Expr S) := L.imp A L.bottom
def top := L.imp L.bottom L.bottom
def conj (A B : Expr S) := L.neg (L.imp A (L.neg B))
def disj (A B : Expr S) := L.neg (L.conj (L.neg A) (L.neg B))
def iff (A B : Expr S) := L.conj (L.imp A B) (L.imp B A)
def cond (G A B : Expr S) := L.disj (L.conj G A) (L.conj (L.neg G) B)
def sign (b : Bool) (A : Expr S) := if b then A else L.neg A

end LogicCode
namespace LogicSetup
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C)
def code : LogicCode S := ⟨L.bottom,L.inCode,L.outCode⟩
end LogicSetup

namespace DataWrapper
/-- The other slot of odd evaluation, exposed as an actual raw callback. -/
def contraCallback (R : DataWrapper S true) (T t : Expr S) : Expr S :=
  (R.rename Nat.succ).observe (T.rename Nat.succ) (.var 0) (t.rename Nat.succ)

end DataWrapper
end PureTypeSystem.Labelled

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Channels
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.Labelled
universe u
variable {S : Type u} {P : Specification S}

structure DoubleCode (S : Type u) where
  first : DataWrapper S true
  second : DataWrapper S true
namespace DoubleCode
variable (R : DoubleCode S)
def rename (ρ : Nat → Nat) : DoubleCode S := ⟨R.first.rename ρ,R.second.rename ρ⟩
def subst (σ : Nat → Expr S) : DoubleCode S := ⟨R.first.subst σ,R.second.subst σ⟩
def carrier (T : Expr S) := R.second.apply (R.first.apply T)
def emb (L : LogicCode S) (b : Bool) (T t : Expr S) :=
  R.second.build (R.first.apply T) ((L.rename Nat.succ).sign b (R.first.contraCallback T t))
def bit (L : LogicCode S) (T v : Expr S) :=
  R.second.observe (R.first.apply T) v (R.first.build T (L.top.rename Nat.succ))
def eval (T v Q : Expr S) := R.second.observe (R.first.apply T) v (R.first.build T Q)
def recover (L : LogicCode S) (T v Q : Expr S) :=
  L.cond (R.bit L T v) (R.eval T v Q) (L.neg (R.eval T v Q))

variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) (I J K : Set S)
structure Formed : Prop where
  first : R.first.Formed L I J
  second : R.second.Formed L J K
end DoubleCode

/-- The fixed odd paths of the first (and later probe) observation channel. -/
structure ChannelCode (S : Type u) where
  logical : DataWrapper S true
  raw : DataWrapper S true
  predicate : DataWrapper S true

namespace ChannelCode
variable (R : ChannelCode S)
def rename (ρ : Nat → Nat) : ChannelCode S :=
  ⟨R.logical.rename ρ,R.raw.rename ρ,R.predicate.rename ρ⟩
def subst (σ : Nat → Expr S) : ChannelCode S :=
  ⟨R.logical.subst σ,R.raw.subst σ,R.predicate.subst σ⟩
def logicalType (T : Expr S) := R.logical.apply T
def rawType (T : Expr S) := R.raw.apply T
def predicateType (T : Expr S) := R.predicate.apply (R.raw.apply T)
def toRaw (T y : Expr S) := DataWrapper.reencode R.logical R.raw T y
def toLog (T c : Expr S) := DataWrapper.reencode R.raw R.logical T c
def round (T y : Expr S) := R.toLog T (R.toRaw T y)
def eval (T p y : Expr S) := R.predicate.observe (R.rawType T) p (R.toRaw T y)
def pred (T Q : Expr S) :=
  R.predicate.build (R.rawType T) (Q.compose (DataWrapper.reencodeBody R.raw R.logical T))

variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) (I J K H : Set S)
structure Formed : Prop where
  logical : R.logical.Formed L I J
  raw : R.raw.Formed L I K
  predicate : R.predicate.Formed L K H

end ChannelCode

/-- All roles use fixed path syntax selected once from the forbidden
configuration. In particular the shared raw wrapper is not
reselected when constructing a query, bundle, or the second channel. -/
structure ChannelSetup {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) where
  seed : S
  domain : Set S
  codomain : Set S
  base : Set S
  rawVertex : Set S
  tailVertex : Set S
  funVertex : Set S
  logicalVertex : Set S
  predVertex : Set S
  mainTriple : ProfileTriple P domain codomain base
  funTriple : ProfileTriple P rawVertex tailVertex funVertex
  ax : (AxProfile P seed).Nonempty
  directLogical : DirectLayer P C logicalVertex
  directPred : DirectLayer P C predVertex
  initialParity : Bool
  initial : DataWrapper S initialParity
  initialFormed : initial.Formed L {seed} base
  channel : ChannelCode S
  channelFormed : channel.Formed L base logicalVertex rawVertex predVertex
  returnPath : DataWrapper S true
  returnFormed : returnPath.Formed L rawVertex base
  funPath : DataWrapper S false
  funFormed : funPath.Formed L funVertex codomain
  lifting : PositiveDataWrapper S
  liftingFormed : lifting.Formed L.witnesses (AxProfile P seed) domain
  tail : DataTail S
  tailFormed : tail.Formed L tailVertex

namespace ChannelSetup
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
  {L : LogicSetup P Γ γ C}

def doubled (K : ChannelSetup L) : DoubleCode S := ⟨K.returnPath,K.channel.raw⟩
end ChannelSetup

namespace DoubleCode
variable (R : DoubleCode S)

def bitBody (L : LogicCode S) (T : Expr S) : Expr S :=
  (R.rename Nat.succ).bit (L.rename Nat.succ) (T.rename Nat.succ) (.var 0)
def recBody (L : LogicCode S) (T Q : Expr S) : Expr S :=
  (R.rename Nat.succ).recover (L.rename Nat.succ) (T.rename Nat.succ) (.var 0) (Q.rename (Expr.liftRen Nat.succ))

def tower : Nat → Expr S → Expr S
  | 0,T => T
  | n+1,T => R.carrier (tower n T)
def embed (L : LogicCode S) : List Bool → Expr S → Expr S → Expr S
  | [],_,t => t
  | b::bs,T,t => R.emb L b (R.tower bs.length T) (embed L bs T t)
def recoveryBody (L : LogicCode S) : Nat → Expr S → Expr S → Expr S
  | 0,_,Q => Q
  | n+1,T,Q => R.recBody L (R.tower n T) (recoveryBody L n T Q)
def tagBody (L : LogicCode S) : List Bool → Expr S → Expr S
  | [],_ => L.top.rename Nat.succ
  | b::bs,T => (L.rename Nat.succ).conj
      ((L.rename Nat.succ).sign b (R.bitBody L (R.tower bs.length T)))
      (R.recBody L (R.tower bs.length T) (tagBody L bs T))

end DoubleCode

/-- Nine distinct finite query strings. Index zero is the payload tag. -/
def queryBits (q : Fin 9) : List Bool :=
  [q.val.testBit 0,q.val.testBit 1,q.val.testBit 2,q.val.testBit 3]

def queryTag (t : Fin 8) : Fin 9 := ⟨t.val+1,by omega⟩

namespace DoubleCode
variable (R : DoubleCode S)
def big (T : Expr S) := R.tower 4 T
def bpType (T : Expr S) := R.first.apply (R.big T)
def paramType (T : Expr S) := R.second.apply (R.bpType T)
def tagged (L : LogicCode S) (q : Fin 9) (T t : Expr S) := R.embed L (queryBits q) T t

def encodeBody (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T p : Expr S) :=
  (L.rename Nat.succ).disj
    ((L.rename Nat.succ).conj (R.tagBody L (queryBits 0) T)
      (R.recoveryBody L 4 T (U.evalCallback T p)))
    (R.tagBody L (queryBits (queryTag t)) T)
def encode (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T p : Expr S) :=
  R.first.build (R.big T) (R.encodeBody U L t T p)
def mark (L : LogicCode S) (t : Fin 8) (T c₀ bp : Expr S) :=
  R.first.observe (R.big T) bp (R.tagged L (queryTag t) T c₀)
def query (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T o p : Expr S) :=
  R.second.observe (R.bpType T) o (R.encode U L t T p)

def embedBody (L : LogicCode S) (q : Fin 9) (T : Expr S) :=
  (R.rename Nat.succ).tagged (L.rename Nat.succ) q (T.rename Nat.succ) (.var 0)
def decoderBody (L : LogicCode S) (T bp : Expr S) :=
  (R.first.evalCallback (R.big T) bp).compose (R.embedBody L 0 T)
def decode (U : DataWrapper S true) (L : LogicCode S) (T bp : Expr S) :=
  U.build T (R.decoderBody L T bp)

end DoubleCode

/-- The A-independent syntax of the common probe type. -/
structure ProbeCode (S : Type u) where
  seed : S
  initialParity : Bool
  initial : DataWrapper S initialParity
  raw : DataWrapper S true
  back : DataWrapper S true
  funPath : DataWrapper S false
  lifting : PositiveDataWrapper S
  tail : DataTail S

namespace ProbeCode
variable (R : ProbeCode S)
def rename (ρ : Nat → Nat) : ProbeCode S :=
  ⟨R.seed,R.initialParity,R.initial.rename ρ,R.raw.rename ρ,R.back.rename ρ,
    R.funPath.rename ρ,R.lifting.rename ρ,R.tail.rename ρ⟩
def subst (σ : Nat → Expr S) : ProbeCode S :=
  ⟨R.seed,R.initialParity,R.initial.subst σ,R.raw.subst σ,R.back.subst σ,
    R.funPath.subst σ,R.lifting.subst σ,R.tail.subst σ⟩
def doubled : DoubleCode S := ⟨R.back,R.raw⟩
def rawType (A : Expr S) := R.raw.apply (R.initial.apply A)
def paramType (A : Expr S) := R.doubled.paramType (R.rawType A)
def singleType (A : Expr S) := R.doubled.carrier (R.paramType A)
def funType (A : Expr S) := Expr.arrow .dd (R.singleType A) R.tail.carrier
def domain := R.lifting.apply (.sort R.seed)
def body := (R.funPath.rename Nat.succ).apply
  ((R.rename Nat.succ).funType ((R.lifting.rename Nat.succ).project (.var 0)))
def carrier := Expr.pi .dd R.domain R.body

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
  (L : LogicSetup P Γ γ C) (I J k p n g : Set S)
structure Formed : Prop where
  mainTriple : ProfileTriple P I J k
  funTriple : ProfileTriple P p n g
  ax : (AxProfile P R.seed).Nonempty
  initial : R.initial.Formed L {R.seed} k
  raw : R.raw.Formed L k p
  back : R.back.Formed L p k
  funPath : R.funPath.Formed L g J
  lifting : R.lifting.Formed L.witnesses (AxProfile P R.seed) I
  tail : R.tail.Formed L n

end ProbeCode

namespace ChannelSetup
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)} {L : LogicSetup P Γ γ C}
def probe (K : ChannelSetup L) : ProbeCode S :=
  ⟨K.seed,K.initialParity,K.initial,K.channel.raw,K.returnPath,K.funPath,K.lifting,K.tail⟩
end ChannelSetup
end PureTypeSystem.Labelled

namespace PureTypeSystem

namespace Labelled
universe u
variable {S : Type u} {P : Specification S}
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)} {L : LogicSetup P Γ γ C}

/-- The parity-matched return is retained alongside, not substituted for,
the fixed channel paths. -/
structure ChannelReturn (K : ChannelSetup L) where
  route : DataWrapper S K.initialParity
  formed : route.Formed L K.base {K.seed}

namespace ChannelReturn
variable {K : ChannelSetup L} (R : ChannelReturn K)
def evenLoop : DataWrapper S false := DataWrapper.reindex (by cases K.initialParity <;> rfl)
  (R.route.append K.initial)
def fourth : DataWrapper S true := K.returnPath.append R.evenLoop
def firstDouble (_R : ChannelReturn K) : DoubleCode S := K.doubled
def outerDouble : DoubleCode S := ⟨R.fourth,K.channel.logical⟩
/-- Specific source A0: two fixed odd-pair detours followed by the matched return. -/
def type : Expr S := R.route.apply (K.returnPath.apply (K.channel.raw.apply
    (K.returnPath.apply (K.channel.raw.apply K.probe.carrier))))

end ChannelReturn
end Labelled
end PureTypeSystem

namespace PureTypeSystem.Labelled

universe u
variable {S : Type u} {P : Specification S}

/-- The two fixed proof paths implementing a direct-domain universal. -/
structure QuantifierCode (S : Type u) where
  into : ProofWrapper S
  out : ProofWrapper S
namespace QuantifierCode
variable (K : QuantifierCode S)
def rename (ρ : Nat → Nat) : QuantifierCode S := ⟨K.into.rename ρ,K.out.rename ρ⟩
def subst (σ : Nat → Expr S) : QuantifierCode S := ⟨K.into.subst σ,K.out.subst σ⟩
def all (T Q : Expr S) := K.out.apply (.pi .dp T ((K.into.rename Nat.succ).apply Q))
end QuantifierCode
namespace QuantifierRoute
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {W : WitnessFamily P Γ γ}
    {C : Set (Set S)} {b I : Set S}
def code (R : QuantifierRoute W C b I) : QuantifierCode S := ⟨R.inCode,R.outCode⟩
end QuantifierRoute
end PureTypeSystem.Labelled

namespace PureTypeSystem.Labelled
universe u
variable {S : Type u} {P : Specification S}
namespace LogicCode
variable (L : LogicCode S)
def guardBody (G Q : Expr S) := (L.rename Nat.succ).imp G Q
def guardAll (K : QuantifierCode S) (T G Q : Expr S) := K.all T (L.guardBody G Q)
end LogicCode
end PureTypeSystem.Labelled

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Components
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem

section
universe u v

namespace ComponentInterface
open Candidates
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable {hw : SystemWeaklyNormalizing P} {U C : Set (Set S)}
variable (J : ComponentInterface.{u,v} Ω hw C)

def Transports (M : Expr S) : Prop :=
  ∀ (Γ : List (Expr S)) A, HasType P Γ M A →
    ∀ e : J.Env Γ, J.Admissible (U := U) e → J.Transported M A e

end ComponentInterface

namespace Candidates
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)
/-- A single finite prefix supporting every exact typing of a tested stack. -/
inductive StackAt (k : Nat) : Expr S → List (Expr S) → Prop
  | nil (T) : StackAt k T []
  | cons {D E n ns} :
      HasType P (Ω.context k) (n.rename (Expr.reverseIndex k)) (D.rename (Expr.reverseIndex k)) →
      StronglyNormalizing n → StackAt k (E.instantiate n).normalForm ns →
      StackAt k (.pi D E) (n :: ns)
end Candidates

namespace ComponentInterface

section
open Candidates
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable {hw : SystemWeaklyNormalizing P} {U C : Set (Set S)}
variable (J : ComponentInterface.{u,v} Ω hw C)

@[simp] theorem identity_actual {k : Nat} {e : J.Env (Ω.context k)}
    (he : J.images e = Expr.var ∘ Expr.reverseIndex k) (T : Expr S) :
    (T.rename (Expr.reverseIndex k)).subst (J.images e) = T := by
  rw [he,Expr.subst_var_rename,Expr.reverseIndex_twice]

end

open Candidates

end ComponentInterface
end

universe u v
open Classical Candidates

end PureTypeSystem

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Congruence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.ObservationValues
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

theorem lambdaValue_congr {T U : ActiveType Ω C} (hTU : T.type = U.type)
    (act : LambdaAction (hw := hw) Ω C hno T) (act' : LambdaAction (hw := hw) Ω C hno U)
    (hr : ∀ (a : FrameKey Ω C T) (a' : FrameKey Ω C U), a.argument = a'.argument →
      ∀ p hp hp', (act a p hp).val = (act' a' p hp').val) :
    (lambdaValue Ω C hno T act).val = (lambdaValue Ω C hno U act').val := by
  have hu := ActiveType.ext hTU
  subst U
  have he : act = act' := by
    funext a p hp
    exact Subtype.ext (hr a a rfl p hp hp)
  rw [he]

theorem applyValue_congr {T U : ActiveType Ω C} (hTU : T.type = U.type)
    (v : Value (hw := hw) Ω C hno T.type) (v' : Value (hw := hw) Ω C hno U.type)
    (hvv : v.val = v'.val) (a : FrameKey Ω C T) (a' : FrameKey Ω C U)
    (hq : a.argument = a'.argument) (p p' : Option (RawValue (hw := hw) Ω C hno)) (hpp : p = p')
    (hp : PayloadFits Ω C hno a.domain p) (hp' : PayloadFits Ω C hno a'.domain p') :
    (applyValue Ω C hno T v a p hp).val = (applyValue Ω C hno U v' a' p' hp').val := by
  have hu := ActiveType.ext hTU
  subst U
  have hv : v = v' := Subtype.ext hvv
  have ha : a = a' := FrameKey.ext hq
  subst v'
  subst a'
  subst p'
  rfl

theorem withBase_congr {T U : ActiveType Ω C} (hTU : T.type = U.type)
    (b b' : Base Ω) (hbb : b = b') :
    (withBase (hw := hw) Ω C hno T b).val = (withBase Ω C hno U b').val := by
  have hu := ActiveType.ext hTU
  subst U
  subst b'
  rfl

theorem distinguished_congr {T U : ActiveType Ω C} (hTU : T.type = U.type) :
    (distinguished (hw := hw) Ω C hno T).val = (distinguished Ω C hno U).val := by
  have hu := ActiveType.ext hTU
  subst U
  rfl

namespace PreResult

section
variable {Ω C hno} {Γ Δ : List (Expr S)} {M M' T T' : Expr S}
variable {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno Δ}

theorem parameter_congr (r : PreResult Ω C hno M T e) (q : PreResult Ω C hno M' T' f)
    (hT : (T.subst e.images).normalForm = (T'.subst f.images).normalForm)
    (hv : ∀ ha hb, (r.val ha).val = (q.val hb).val) : r.parameter = q.parameter := by
  by_cases ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)
  · have hb : ActiveLayer P C (Ω.profile (T'.subst f.images).normalForm) := hT ▸ ha
    rw [r.parameter_eq ha,q.parameter_eq hb,hv ha hb]
  · have hb : ¬ ActiveLayer P C (Ω.profile (T'.subst f.images).normalForm) := hT ▸ ha
    simp only [parameter,ha,hb,dite_false]

theorem val_congr (r : PreResult Ω C hno M T e) (q : PreResult Ω C hno M' T' f)
    (hr : r.parameter = q.parameter)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (hb : ActiveLayer P C (Ω.profile (T'.subst f.images).normalForm)) :
    (r.val ha).val = (q.val hb).val := by
  rw [r.parameter_eq ha,q.parameter_eq hb] at hr
  exact Option.some.inj hr

/-- A cross-context form of base projection congruence. The literal-sort
condition is retained: arbitrary retargeting preserves Val, not every unused
Read coordinate. -/
theorem baseRead_congr (h : HasType P Γ M T) (h' : HasType P Δ M' T')
    (hM : (M.subst e.images).normalForm = (M'.subst f.images).normalForm)
    (hT : (T.subst e.images).normalForm = (T'.subst f.images).normalForm)
    (hS : (∃ s : S, T = .sort s ∧ ({s} : Set S) ∈ C) ↔
      (∃ s : S, T' = .sort s ∧ ({s} : Set S) ∈ C))
    (v : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm) →
      Value (hw := hw) Ω C hno (T.subst e.images).normalForm)
    (w : ActiveLayer P C (Ω.profile (T'.subst f.images).normalForm) →
      Value (hw := hw) Ω C hno (T'.subst f.images).normalForm)
    (hv : ∀ ha hb, (v ha).val = (w hb).val) :
    (baseRead h v).val = (baseRead h' w).val := by
  by_cases hm : Ω.profile (M.subst e.images).normalForm ∈ C
  · have hm' : Ω.profile (M'.subst f.images).normalForm ∈ C := hM ▸ hm
    by_cases hs : ∃ s : S, T = .sort s ∧ ({s} : Set S) ∈ C
    · have hs' := hS.mp hs
      by_cases ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)
      · have hb : ActiveLayer P C (Ω.profile (T'.subst f.images).normalForm) := hT ▸ ha
        simp only [baseRead,hm,hm',hs,hs',ha,hb,dite_true]
        have hX : e.actualExpression (hs.choose_spec.1 ▸ h) =
            f.actualExpression (hs'.choose_spec.1 ▸ h') := Subtype.ext hM
        rw [hv ha hb]
        exact congrArg (fun X : ActualType Ω => ((RawValue.base Ω C hno (w hb).val) X).val) hX
      · have hb : ¬ ActiveLayer P C (Ω.profile (T'.subst f.images).normalForm) := hT ▸ ha
        simp only [baseRead,hm,hm',hs,hs',ha,hb,dite_true,dite_false]
        exact congrArg (Candidates.Top Ω) hM
    · have hs' := mt hS.mpr hs
      simp only [baseRead,hm,hm',hs,hs',dite_true,dite_false]
      exact congrArg (Candidates.Top Ω) hM
  · have hm' : Ω.profile (M'.subst f.images).normalForm ∉ C := hM ▸ hm
    simp only [baseRead,hm,hm',dite_false]
    exact congrArg (Candidates.Top Ω) hM
end

variable {Ω C hno} {Γ Δ : List (Expr S)} {T T' : Expr S}

 theorem abstractionAction_congr {D m E D' m' E' : Expr S} {s s' : S}
    (h : HasType P Γ (.lam D m) T) (h' : HasType P Δ (.lam D' m') T')
    (hp : HasType P Γ (.pi D E) (.sort s)) (hp' : HasType P Δ (.pi D' E') (.sort s'))
    (hc : Converts T (.pi D E)) (hc' : Converts T' (.pi D' E'))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) m E)
    (eb' : Evaluator (hw := hw) Ω C hno (D' :: Δ) m' E')
    (e : Environment (hw := hw) Ω C hno Γ) (e' : Environment (hw := hw) Ω C hno Δ)
    (hb : ∀ n n' (hn : Ω.HasType n (D.subst e.images)) (hn' : Ω.HasType n' (D'.subst e'.images)),
      n = n' → ∀ p hp hp' ha ha',
        ((eb (e.cons hn p hp)).val ha).val = ((eb' (e'.cons hn' p hp')).val ha').val)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (ha' : ActiveLayer P C (Ω.profile (T'.subst e'.images).normalForm))
    (a : FrameKey Ω C (e.activeType h ha)) (a' : FrameKey Ω C (e'.activeType h' ha'))
    (haa : a.argument = a'.argument) (p : Option (RawValue (hw := hw) Ω C hno))
    (hpa : PayloadFits Ω C hno a.domain p) (hpa' : PayloadFits Ω C hno a'.domain p) :
    (abstractionAction h hp hc eb e ha a p hpa).val =
      (abstractionAction h' hp' hc' eb' e' ha' a' p hpa').val := by
  dsimp only [abstractionAction,ProductInstance.frameEnvironment,ProductInstance.extend]
  exact hb a.argument a'.argument _ _ haa p _ _ _ _

 theorem abstraction_val_congr {D m E D' m' E' : Expr S} {s s' : S}
    (h : HasType P Γ (.lam D m) T) (h' : HasType P Δ (.lam D' m') T')
    (hp : HasType P Γ (.pi D E) (.sort s)) (hp' : HasType P Δ (.pi D' E') (.sort s'))
    (hc : Converts T (.pi D E)) (hc' : Converts T' (.pi D' E'))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) m E)
    (eb' : Evaluator (hw := hw) Ω C hno (D' :: Δ) m' E')
    (e : Environment (hw := hw) Ω C hno Γ) (e' : Environment (hw := hw) Ω C hno Δ)
    (hT : (T.subst e.images).normalForm = (T'.subst e'.images).normalForm)
    (hb : ∀ n n' (hn : Ω.HasType n (D.subst e.images)) (hn' : Ω.HasType n' (D'.subst e'.images)),
      n = n' → ∀ p hp hp' ha ha',
        ((eb (e.cons hn p hp)).val ha).val = ((eb' (e'.cons hn' p hp')).val ha').val)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (ha' : ActiveLayer P C (Ω.profile (T'.subst e'.images).normalForm)) :
    ((abstraction h hp hc eb e).val ha).val =
      ((abstraction h' hp' hc' eb' e').val ha').val := by
  apply lambdaValue_congr Ω C hno hT
  exact abstractionAction_congr h h' hp hp' hc hc' eb eb' e e' hb ha ha'

 theorem application_val_congr {f n D E f' n' D' E' : Expr S}
    (h : HasType P Γ (.app f n) T) (h' : HasType P Δ (.app f' n') T')
    (hf : HasType P Γ f (.pi D E)) (hf' : HasType P Δ f' (.pi D' E'))
    (hn : HasType P Γ n D) (hn' : HasType P Δ n' D')
    (hc : Converts T (E.instantiate n)) (hc' : Converts T' (E'.instantiate n'))
    (ef : Evaluator (hw := hw) Ω C hno Γ f (.pi D E))
    (ef' : Evaluator (hw := hw) Ω C hno Δ f' (.pi D' E'))
    (en : Evaluator (hw := hw) Ω C hno Γ n D)
    (en' : Evaluator (hw := hw) Ω C hno Δ n' D')
    (e : Environment (hw := hw) Ω C hno Γ) (e' : Environment (hw := hw) Ω C hno Δ)
    (hT : (T.subst e.images).normalForm = (T'.subst e'.images).normalForm)
    (hF : (Expr.pi D E |>.subst e.images).normalForm = (Expr.pi D' E' |>.subst e'.images).normalForm)
    (hN : (n.subst e.images).normalForm = (n'.subst e'.images).normalForm)
    (hvf : ∀ ha ha', ((ef e).val ha).val = ((ef' e').val ha').val)
    (hvn : (en e).parameter = (en' e').parameter)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (ha' : ActiveLayer P C (Ω.profile (T'.subst e'.images).normalForm)) :
    ((application h hf hn hc ef en e).val ha).val =
      ((application h' hf' hn' hc' ef' en' e').val ha').val := by
  by_cases hA : ActiveLayer P C (Ω.profile (Expr.pi D E |>.subst e.images).normalForm)
  · have hA' : ActiveLayer P C (Ω.profile (Expr.pi D' E' |>.subst e'.images).normalForm) := hF ▸ hA
    dsimp only [application,baseResult,applicationValue]
    simp only [dite_eq_left hA,dite_eq_left hA']
    apply applyValue_congr Ω C hno hF _ _ (hvf _ _) _ _ hN _ _ hvn
  · have hA' : ¬ ActiveLayer P C (Ω.profile (Expr.pi D' E' |>.subst e'.images).normalForm) := hF ▸ hA
    dsimp only [application,baseResult,applicationValue]
    simp only [dite_eq_right hA,dite_eq_right hA']
    exact distinguished_congr Ω C hno hT

 theorem productCandidate_congr {D E D' E' : Expr S} {a b c a' b' c' : S}
    (hd : HasType P Γ D (.sort a)) (hb : HasType P (D :: Γ) E (.sort b)) (hr : P.rule a b c)
    (hd' : HasType P Δ D' (.sort a')) (hb' : HasType P (D' :: Δ) E' (.sort b')) (hr' : P.rule a' b' c')
    (ed : Evaluator (hw := hw) Ω C hno Γ D (.sort a))
    (ed' : Evaluator (hw := hw) Ω C hno Δ D' (.sort a'))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) E (.sort b))
    (eb' : Evaluator (hw := hw) Ω C hno (D' :: Δ) E' (.sort b'))
    (e : Environment (hw := hw) Ω C hno Γ) (e' : Environment (hw := hw) Ω C hno Δ)
    (hD : (D.subst e.images).normalForm = (D'.subst e'.images).normalForm)
    (hE : (E.subst (Expr.liftSub e.images)).normalForm = (E'.subst (Expr.liftSub e'.images)).normalForm)
    (hvd : Ω.profile (D.subst e.images).normalForm ∈ C → (ed e).read.val = (ed' e').read.val)
    (hvb : ∀ n (hn : Ω.HasType n (D.subst e.images)) (hn' : Ω.HasType n (D'.subst e'.images))
        p hp hp', Ω.profile (E.subst (e.cons hn p hp).images).normalForm ∈ C →
        (eb (e.cons hn p hp)).read.val = (eb' (e'.cons hn' p hp')).read.val) :
    (productCandidate hd hb hr ed eb e).val = (productCandidate hd' hb' hr' ed' eb' e').val := by
  dsimp only [productCandidate]
  apply ProductInstance.candidate_eq (t := productData hd hb hr e) (t' := productData hd' hb' hr' e') hD hE
  · exact hvd
  · intro n hn p hp hh
    exact hvb n _ _ p _ _ hh
 theorem product_val_congr {D E D' E' : Expr S} {a b c a' b' c' : S}
    (h : HasType P Γ (.pi D E) T) (h' : HasType P Δ (.pi D' E') T')
    (hd : HasType P Γ D (.sort a)) (hb : HasType P (D :: Γ) E (.sort b)) (hr : P.rule a b c)
    (hd' : HasType P Δ D' (.sort a')) (hb' : HasType P (D' :: Δ) E' (.sort b')) (hr' : P.rule a' b' c')
    (hc : Converts T (.sort c)) (hc' : Converts T' (.sort c'))
    (ed : Evaluator (hw := hw) Ω C hno Γ D (.sort a))
    (ed' : Evaluator (hw := hw) Ω C hno Δ D' (.sort a'))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) E (.sort b))
    (eb' : Evaluator (hw := hw) Ω C hno (D' :: Δ) E' (.sort b'))
    (e : Environment (hw := hw) Ω C hno Γ) (e' : Environment (hw := hw) Ω C hno Δ)
    (hT : (T.subst e.images).normalForm = (T'.subst e'.images).normalForm)
    (hM : (Expr.pi D E |>.subst e.images).normalForm = (Expr.pi D' E' |>.subst e'.images).normalForm)
    (hcc : ({c} : Set S) ∈ C ↔ ({c'} : Set S) ∈ C)
    (hpc : Ω.profile (Expr.pi D E |>.subst e.images).normalForm ∈ C →
      (productCandidate hd hb hr ed eb e).val = (productCandidate hd' hb' hr' ed' eb' e').val)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (ha' : ActiveLayer P C (Ω.profile (T'.subst e'.images).normalForm)) :
    ((product h hd hb hr hc ed eb e).val ha).val =
      ((product h' hd' hb' hr' hc' ed' eb' e').val ha').val := by
  by_cases hh : ({c} : Set S) ∈ C ∧ Ω.profile (Expr.pi D E |>.subst e.images).normalForm ∈ C
  · have hh' : ({c'} : Set S) ∈ C ∧ Ω.profile (Expr.pi D' E' |>.subst e'.images).normalForm ∈ C :=
      ⟨hcc.mp hh.1,hM ▸ hh.2⟩
    simp only [product,dite_eq_left hh,dite_eq_left hh']
    apply withBase_congr Ω C hno hT
    apply Base.update_congr Ω _ (Subtype.ext hM)
    exact hpc hh.2
  · have hh' : ¬ (({c'} : Set S) ∈ C ∧ Ω.profile (Expr.pi D' E' |>.subst e'.images).normalForm ∈ C) :=
      fun hcc' => hh ⟨hcc.mpr hcc'.1,hM.symm ▸ hcc'.2⟩
    simp only [product,dite_eq_right hh,dite_eq_right hh']
    exact distinguished_congr Ω C hno hT

 theorem product_read_congr {D E D' E' : Expr S} {a b c a' b' c' : S}
    (h : HasType P Γ (.pi D E) T) (h' : HasType P Δ (.pi D' E') T')
    (hd : HasType P Γ D (.sort a)) (hb : HasType P (D :: Γ) E (.sort b)) (hr : P.rule a b c)
    (hd' : HasType P Δ D' (.sort a')) (hb' : HasType P (D' :: Δ) E' (.sort b')) (hr' : P.rule a' b' c')
    (hc : Converts T (.sort c)) (hc' : Converts T' (.sort c'))
    (ed : Evaluator (hw := hw) Ω C hno Γ D (.sort a))
    (ed' : Evaluator (hw := hw) Ω C hno Δ D' (.sort a'))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) E (.sort b))
    (eb' : Evaluator (hw := hw) Ω C hno (D' :: Δ) E' (.sort b'))
    (e : Environment (hw := hw) Ω C hno Γ) (e' : Environment (hw := hw) Ω C hno Δ)
    (hM : (Expr.pi D E |>.subst e.images).normalForm = (Expr.pi D' E' |>.subst e'.images).normalForm)
    (hpc : Ω.profile (Expr.pi D E |>.subst e.images).normalForm ∈ C →
      (productCandidate hd hb hr ed eb e).val = (productCandidate hd' hb' hr' ed' eb' e').val) :
    (product h hd hb hr hc ed eb e).read.val = (product h' hd' hb' hr' hc' ed' eb' e').read.val := by
  by_cases hh : Ω.profile (Expr.pi D E |>.subst e.images).normalForm ∈ C
  · have hh' : Ω.profile (Expr.pi D' E' |>.subst e'.images).normalForm ∈ C := hM ▸ hh
    simp only [product,ite_eq_left hh,ite_eq_left hh']
    exact hpc hh
  · have hh' : Ω.profile (Expr.pi D' E' |>.subst e'.images).normalForm ∉ C := hM ▸ hh
    simp only [product,ite_eq_right hh,ite_eq_right hh']
    exact congrArg (Candidates.Top Ω) hM
end PreResult
end PureTypeSystem.ObservationValues

namespace PureTypeSystem
universe u
namespace Expr
variable {S : Type u} {M : Expr S} {n : Nat}
theorem Scoped.subst_congr (h : Scoped n M) {σ τ : Nat → Expr S}
    (he : ∀ i, i < n → σ i = τ i) : M.subst σ = M.subst τ := by
  induction M generalizing n σ τ with
  | var i => exact he i h
  | sort s => rfl
  | app f a ihf iha => exact congrArg₂ Expr.app (ihf h.1 he) (iha h.2 he)
  | lam D m ihD ihm =>
    apply congrArg₂ Expr.lam (ihD h.1 he)
    apply ihm h.2
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact congrArg (Expr.rename Nat.succ) (he i (by omega))
  | pi D E ihD ihE =>
    apply congrArg₂ Expr.pi (ihD h.1 he)
    apply ihE h.2
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact congrArg (Expr.rename Nat.succ) (he i (by omega))

@[simp] theorem rename_eq_sort (M : Expr S) (ρ : Nat → Nat) (s : S) :
    M.rename ρ = .sort s ↔ M = .sort s := by
  cases M <;> simp [rename]
end Expr

namespace ObservationValues
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

namespace Environment
variable {Ω C hno} {Γ Δ : List (Expr S)}
/-- Matching old raw images and parameters under declaration reindexing.
No equality is imposed on undeclared indices. -/
def Reindexed (e : Environment (hw := hw) Ω C hno Γ)
    (f : Environment (hw := hw) Ω C hno Δ) (ρ : Nat → Nat) : Prop :=
  ∀ i, i < Γ.length → e.images i = f.images (ρ i) ∧ e.parameters i = f.parameters (ρ i)

namespace Reindexed
variable {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno Δ}
variable {ρ : Nat → Nat} (he : e.Reindexed f ρ)
include he
 theorem raw_eq {M : Expr S} (hm : M.Scoped Γ.length) :
    M.subst e.images = (M.rename ρ).subst f.images := by
  rw [Expr.subst_rename]
  apply hm.subst_congr
  exact fun n hn => (he n hn).1
 theorem expr_eq {M T : Expr S} (h : HasType P Γ M T) :
    (M.subst e.images).normalForm = (M.rename ρ |>.subst f.images).normalForm :=
  congrArg Expr.normalForm (he.raw_eq h.scope.1)
 theorem type_eq {M T : Expr S} (h : HasType P Γ M T) :
    (T.subst e.images).normalForm = (T.rename ρ |>.subst f.images).normalForm :=
  congrArg Expr.normalForm (he.raw_eq h.scope.2)
 theorem cons {A : Expr S} {n m : Expr S}
    (hn : Ω.HasType n (A.subst e.images)) (hm : Ω.HasType m (A.rename ρ |>.subst f.images))
    (hnm : n = m) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno (A.subst e.images).normalForm p)
    (hp' : PayloadFits Ω C hno (A.rename ρ |>.subst f.images).normalForm p) :
    (e.cons hn p hp).Reindexed (f.cons hm p hp') (Expr.liftRen ρ) := by
  intro i hi
  cases i with
  | zero => exact ⟨hnm,rfl⟩
  | succ i => exact he i (Nat.lt_of_succ_lt_succ hi)
end Reindexed
end Environment

 theorem preEvaluate_rename {Γ : List (Expr S)} {M T : Expr S} (t : TypingTree P Γ M T)
    {Δ : List (Expr S)} (hΔ : ValidContext P Δ) (ρ : Nat → Nat) (hρ : TypingTree.DeclRenaming Γ Δ ρ)
    (e : Environment (hw := hw) Ω C hno Γ) (f : Environment (hw := hw) Ω C hno Δ)
    (hef : e.Reindexed f ρ) :
    (preEvaluate Ω C hno t e).parameter = (preEvaluate Ω C hno (t.rename hΔ ρ hρ) f).parameter ∧
    (preEvaluate Ω C hno t e).read.val = (preEvaluate Ω C hno (t.rename hΔ ρ hρ) f).read.val := by
  induction t generalizing Δ ρ with
  | var ht hd hc =>
      have hparam : (PreResult.lookup ht hd hc e).parameter =
          (PreResult.lookup (ht.rename hΔ ρ (hρ.typed hΔ)) (hρ _ _ hd) (hc.rename ρ) f).parameter := by
        exact (PreResult.lookup_parameter ht hd hc e).trans
          ((hef _ ht.scope.1).2.trans (PreResult.lookup_parameter
            (ht.rename hΔ ρ (hρ.typed hΔ)) (hρ _ _ hd) (hc.rename ρ) f).symm)
      refine ⟨hparam,?_⟩
      apply PreResult.baseRead_congr ht (ht.rename hΔ ρ (hρ.typed hΔ))
        (hef.expr_eq ht) (hef.type_eq ht)
      · simp only [Expr.rename_eq_sort]
      · exact fun ha hb => PreResult.val_congr _ _ hparam ha hb
  | sort ht ha hc =>
      constructor
      · apply PreResult.parameter_congr _ _ (hef.type_eq ht)
        intro hs hs'
        exact distinguished_congr Ω C hno (hef.type_eq ht)
      · exact congrArg (Candidates.Top Ω) (hef.expr_eq ht)
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      have hh : HasType P Δ (D.rename ρ) (.sort a) := d.typing.rename hΔ ρ (hρ.typed hΔ)
      have he := hef.type_eq ht
      have hv : ∀ ha ha', ((preEvaluate Ω C hno (.abstraction ht d b hp hc) e).val ha).val =
          ((preEvaluate Ω C hno ((TypingTree.abstraction ht d b hp hc).rename hΔ ρ hρ) f).val ha').val := by
        apply PreResult.abstraction_val_congr ht (ht.rename hΔ ρ (hρ.typed hΔ)) hp
          (hp.rename hΔ ρ (hρ.typed hΔ)) hc (hc.rename ρ) _ _ e f he
        intro n m hn hm hnm p hpp hpp' ha ha'
        apply PreResult.val_congr
        exact (ihb (.cons hΔ hh) (Expr.liftRen ρ) (hρ.lift D)
          (e.cons hn p hpp) (f.cons hm p hpp') (hef.cons hn hm hnm p hpp hpp')).1
      constructor
      · exact PreResult.parameter_congr _ _ he hv
      · apply PreResult.baseRead_congr ht (ht.rename hΔ ρ (hρ.typed hΔ)) (hef.expr_eq ht) he
        · simp only [Expr.rename_eq_sort]
        · exact hv
  | @application Γ g n D E T ht gtr ntr hc ihg ihn =>
      have hg := ihg hΔ ρ hρ e f hef
      have hn := ihn hΔ ρ hρ e f hef
      have he := hef.type_eq ht
      have hv : ∀ ha ha', ((preEvaluate Ω C hno (.application ht gtr ntr hc) e).val ha).val =
          ((preEvaluate Ω C hno ((TypingTree.application ht gtr ntr hc).rename hΔ ρ hρ) f).val ha').val := by
        apply PreResult.application_val_congr ht (ht.rename hΔ ρ (hρ.typed hΔ)) gtr.typing
          (gtr.typing.rename hΔ ρ (hρ.typed hΔ)) ntr.typing (ntr.typing.rename hΔ ρ (hρ.typed hΔ))
          hc _ _ _ _ _ e f he (hef.type_eq gtr.typing) (hef.expr_eq ntr.typing)
        · exact fun ha ha' => PreResult.val_congr _ _ hg.1 ha ha'
        · exact hn.1
      constructor
      · exact PreResult.parameter_congr _ _ he hv
      · apply PreResult.baseRead_congr ht (ht.rename hΔ ρ (hρ.typed hΔ)) (hef.expr_eq ht) he
        · simp only [Expr.rename_eq_sort]
        · exact hv
  | @product Γ D E a b c T ht d btr hr hc ihd ihb =>
      have hh : HasType P Δ (D.rename ρ) (.sort a) := d.typing.rename hΔ ρ (hρ.typed hΔ)
      have hb := btr.typing.rename (.cons hΔ hh) (Expr.liftRen ρ) ((hρ.lift D).typed (.cons hΔ hh))
      have hm := hef.expr_eq ht
      have he := hef.type_eq ht
      have hDE := Expr.pi.inj (hef.raw_eq ht.scope.1)
      have hpc : ∀ (_ : Ω.profile (Expr.pi D E |>.subst e.images).normalForm ∈ C),
          (PreResult.productCandidate d.typing btr.typing hr (preEvaluate Ω C hno d)
            (preEvaluate Ω C hno btr) e).val =
          (PreResult.productCandidate hh hb hr (preEvaluate Ω C hno (d.rename hΔ ρ hρ))
            (preEvaluate Ω C hno (btr.rename (.cons hΔ hh) (Expr.liftRen ρ) (hρ.lift D))) f).val := by
        intro _
        apply PreResult.productCandidate_congr d.typing btr.typing hr hh hb hr _ _ _ _ e f
          (congrArg Expr.normalForm hDE.1) (congrArg Expr.normalForm hDE.2)
        · intro _
          exact (ihd hΔ ρ hρ e f hef).2
        · intro n hn hn' p hp hp' _
          exact (ihb (.cons hΔ hh) (Expr.liftRen ρ) (hρ.lift D)
            (e.cons hn p hp) (f.cons hn' p hp') (hef.cons hn hn' rfl p hp hp')).2
      constructor
      · apply PreResult.parameter_congr _ _ he
        apply PreResult.product_val_congr ht (ht.rename hΔ ρ (hρ.typed hΔ)) d.typing btr.typing hr hh hb hr
          hc (hc.rename ρ) _ _ _ _ e f he hm Iff.rfl hpc
      · exact PreResult.product_read_congr ht (ht.rename hΔ ρ (hρ.typed hΔ)) d.typing btr.typing hr hh hb hr
          hc (hc.rename ρ) _ _ _ _ e f hm hpc

end ObservationValues

namespace TypingTree
variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)} {M T : Expr S}
/-- Context conversion retains every nonvariable core and all sort choices. -/
noncomputable def recontext (t : TypingTree P Γ M T) (h : ContextEquivalent P Γ Δ) :
    TypingTree P Δ M T := by
  induction t generalizing Δ with
  | var ht hd hc =>
      have ht' := (h.typing _ _).mp ht
      let g := ht'.generation
      exact .var ht' g.choose_spec.1 g.choose_spec.2
  | sort ht ha hc => exact .sort ((h.typing _ _).mp ht) ha hc
  | product ht d b hr hc ihd ihb =>
      exact .product ((h.typing _ _).mp ht) (ihd h) (ihb (h.cons d.typing)) hr hc
  | abstraction ht d b hp hc ihd ihb =>
      exact .abstraction ((h.typing _ _).mp ht) (ihd h) (ihb (h.cons d.typing)) ((h.typing _ _).mp hp) hc
  | application ht g n hc ihg ihn => exact .application ((h.typing _ _).mp ht) (ihg h) (ihn h) hc
end TypingTree

namespace ObservationValues
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)
namespace Environment
variable {Ω C hno} {Γ Δ : List (Expr S)}
def SameData (e : Environment (hw := hw) Ω C hno Γ)
    (f : Environment (hw := hw) Ω C hno Δ) : Prop := e.images = f.images ∧ e.parameters = f.parameters
namespace SameData
variable {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno Δ}
variable (he : e.SameData f)
include he
theorem raw_eq (M : Expr S) : M.subst e.images = M.subst f.images := congrArg (M.subst) he.1
theorem expr_eq (M : Expr S) : (M.subst e.images).normalForm = (M.subst f.images).normalForm :=
  congrArg Expr.normalForm (he.raw_eq M)
theorem cons {A : Expr S} {n m : Expr S}
    (hn : Ω.HasType n (A.subst e.images)) (hm : Ω.HasType m (A.subst f.images))
    (hnm : n = m) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno (A.subst e.images).normalForm p)
    (hp' : PayloadFits Ω C hno (A.subst f.images).normalForm p) :
    (e.cons hn p hp).SameData (f.cons hm p hp') := by
  constructor
  · funext i; cases i with
    | zero => exact hnm
    | succ i => exact congrFun he.1 i
  · funext i; cases i with
    | zero => rfl
    | succ i => exact congrFun he.2 i
end SameData
end Environment

theorem preEvaluate_recontext {Γ : List (Expr S)} {M T : Expr S} (t : TypingTree P Γ M T)
    {Δ : List (Expr S)} (h : ContextEquivalent P Γ Δ)
    (e : Environment (hw := hw) Ω C hno Γ) (f : Environment (hw := hw) Ω C hno Δ)
    (hef : e.SameData f) :
    (preEvaluate Ω C hno t e).parameter = (preEvaluate Ω C hno (t.recontext h) f).parameter ∧
    (preEvaluate Ω C hno t e).read.val = (preEvaluate Ω C hno (t.recontext h) f).read.val := by
  induction t generalizing Δ with
  | var ht hd hc =>
      have ht' := (h.typing _ _).mp ht
      let g := ht'.generation
      have hparam : (PreResult.lookup ht hd hc e).parameter =
          (PreResult.lookup ht' g.choose_spec.1 g.choose_spec.2 f).parameter := by
        rw [PreResult.lookup_parameter, PreResult.lookup_parameter]
        exact congrFun hef.2 _
      refine ⟨hparam,?_⟩
      apply PreResult.baseRead_congr ht ht' (hef.expr_eq _) (hef.expr_eq _)
      · exact Iff.rfl
      · exact fun ha hb => PreResult.val_congr _ _ hparam ha hb
  | sort ht ha hc =>
      constructor
      · apply PreResult.parameter_congr _ _ (hef.expr_eq _)
        intro hs hs'
        exact distinguished_congr Ω C hno (hef.expr_eq _)
      · exact congrArg (Candidates.Top Ω) (hef.expr_eq _)
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      have he := hef.expr_eq T
      have hv : ∀ ha ha', ((preEvaluate Ω C hno (.abstraction ht d b hp hc) e).val ha).val =
          ((preEvaluate Ω C hno ((TypingTree.abstraction ht d b hp hc).recontext h) f).val ha').val := by
        apply PreResult.abstraction_val_congr ht ((h.typing _ _).mp ht) hp ((h.typing _ _).mp hp)
          hc hc _ _ e f he
        intro n m hn hm hnm p hpp hpp' ha ha'
        apply PreResult.val_congr
        exact (ihb (h.cons d.typing) (e.cons hn p hpp) (f.cons hm p hpp') (hef.cons hn hm hnm p hpp hpp')).1
      constructor
      · exact PreResult.parameter_congr _ _ he hv
      · apply PreResult.baseRead_congr ht ((h.typing _ _).mp ht) (hef.expr_eq _) he
        · exact Iff.rfl
        · exact hv
  | @application Γ g n D E T ht gtr ntr hc ihg ihn =>
      have hg := ihg h e f hef
      have hn := ihn h e f hef
      have he := hef.expr_eq T
      have hv : ∀ ha ha', ((preEvaluate Ω C hno (.application ht gtr ntr hc) e).val ha).val =
          ((preEvaluate Ω C hno ((TypingTree.application ht gtr ntr hc).recontext h) f).val ha').val := by
        apply PreResult.application_val_congr ht ((h.typing _ _).mp ht) gtr.typing
          ((h.typing _ _).mp gtr.typing) ntr.typing ((h.typing _ _).mp ntr.typing)
          hc hc _ _ _ _ e f he (hef.expr_eq _) (hef.expr_eq _)
        · exact fun ha ha' => PreResult.val_congr _ _ hg.1 ha ha'
        · exact hn.1
      constructor
      · exact PreResult.parameter_congr _ _ he hv
      · apply PreResult.baseRead_congr ht ((h.typing _ _).mp ht) (hef.expr_eq _) he
        · exact Iff.rfl
        · exact hv
  | @product Γ D E a b c T ht d btr hr hc ihd ihb =>
      have hh := (h.typing _ _).mp d.typing
      have hb := ((h.cons d.typing).typing _ _).mp btr.typing
      have hm := hef.expr_eq (.pi D E)
      have he := hef.expr_eq T
      have hDE := Expr.pi.inj (hef.raw_eq (.pi D E))
      have hpc : ∀ (_ : Ω.profile (Expr.pi D E |>.subst e.images).normalForm ∈ C),
          (PreResult.productCandidate d.typing btr.typing hr (preEvaluate Ω C hno d)
            (preEvaluate Ω C hno btr) e).val =
          (PreResult.productCandidate hh hb hr (preEvaluate Ω C hno (d.recontext h))
            (preEvaluate Ω C hno (btr.recontext (h.cons d.typing))) f).val := by
        intro _
        apply PreResult.productCandidate_congr d.typing btr.typing hr hh hb hr _ _ _ _ e f
          (congrArg Expr.normalForm hDE.1) (congrArg Expr.normalForm hDE.2)
        · intro _
          exact (ihd h e f hef).2
        · intro n hn hn' p hp hp' _
          exact (ihb (h.cons d.typing) (e.cons hn p hp) (f.cons hn' p hp') (hef.cons hn hn' rfl p hp hp')).2
      constructor
      · apply PreResult.parameter_congr _ _ he
        apply PreResult.product_val_congr ht ((h.typing _ _).mp ht) d.typing btr.typing hr hh hb hr
          hc hc _ _ _ _ e f he hm Iff.rfl hpc
      · exact PreResult.product_read_congr ht ((h.typing _ _).mp ht) d.typing btr.typing hr hh hb hr
          hc hc _ _ _ _ e f hm hpc
end ObservationValues

namespace Expr
variable {S : Type u}
def consSub (n : Expr S) (σ : Nat → Expr S) : Nat → Expr S
  | 0 => n
  | i+1 => σ i
end Expr
namespace ContextTower
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)
theorem profile_sort (s : S) : Ω.profile (.sort s) = AxProfile P s := by
  ext t
  change (∃ n, PureTypeSystem.HasType P (Ω.context n) ((Expr.sort s).normalForm.rename (Expr.reverseIndex n))
    ((Expr.sort t).rename (Expr.reverseIndex n))) ↔ P.axioms s t
  simp only [Expr.normalForm_of_normal (Normal.sort s),Expr.rename]
  constructor
  · rintro ⟨n,hn⟩
    obtain ⟨u,ha,hc⟩ := hn.generation
    exact hc.sort_inj ▸ ha
  · intro h; exact ⟨0,PureTypeSystem.HasType.sort_of_valid (Ω.valid 0) h⟩
end ContextTower
namespace FeasibleProfile
variable {S : Type u} {P : Specification S}
theorem singleton {s : S} (h : (AxProfile P s).Nonempty) : FeasibleProfile P {s} := by
  obtain ⟨t,ht⟩ := h
  have hs : HasType P [] (.sort s) (.sort t) := .ax ht
  have hv : HasType P [.sort s] (.var 0) (.sort s) := .var hs
  exact ⟨Set.singleton_nonempty s,[.sort s],.var 0,hv.valid,Normal.var 0,
    Profile.neutral (Normal.var 0) (.var 0) hv⟩
end FeasibleProfile

namespace ObservationValues
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) (C : Set (Set S))
/-- Goodness is deliberately independent of observation parameters. -/
def baseGood (M T : Expr S) (σ : Nat → Expr S) (v : Prop) : Prop :=
  Ω.profile (M.subst σ) ∈ C →
    ∃ s, T = .sort s ∧ ({s} : Set S) ∈ C ∧
      (ActiveLayer P C (Ω.profile (T.subst σ)) → v) ∧
      (¬ ActiveLayer P C (Ω.profile (T.subst σ)) → Neutral M)

noncomputable def goodness {Γ : List (Expr S)} {M T : Expr S}
    (t : TypingTree P Γ M T) (σ : Nat → Expr S) : Prop × Prop :=
  match t with
  | .var _ _ _ => (True,baseGood Ω C M T σ True)
  | .sort _ _ _ => (True,True)
  | @TypingTree.product _ _ _ D E _ _ c _ _ d e _ _ =>
    let g := (Ω.profile (D.subst σ) ∈ C → (goodness d σ).2) ∧
      ∀ n, Ω.HasType n (D.subst σ) → Ω.profile (E.subst (Expr.consSub n σ)) ∈ C →
        (goodness e (Expr.consSub n σ)).2
    ((({c} : Set S) ∈ C ∧ Ω.profile (Expr.pi D E |>.subst σ) ∈ C) → g,
      Ω.profile (Expr.pi D E |>.subst σ) ∈ C → g)
  | @TypingTree.abstraction _ _ _ D m E _ _ _ _ _ b _ _ =>
    let g := ∀ n, Ω.HasType n (D.subst σ) → ActiveLayer P C (Ω.profile (E.subst (Expr.consSub n σ))) →
      (goodness b (Expr.consSub n σ)).1
    (g,baseGood Ω C M T σ g)
  | @TypingTree.application _ _ _ g n D E _ _ f a _ =>
    let v := if ActiveLayer P C (Ω.profile (Expr.pi D E |>.subst σ)) then
      (goodness f σ).1 ∧ (ActiveLayer P C (Ω.profile (D.subst σ)) → (goodness a σ).1)
      else Neutral (.app g n)
    (v,baseGood Ω C M T σ v)

abbrev ValGood {Γ : List (Expr S)} {M T : Expr S} (t : TypingTree P Γ M T) (σ : Nat → Expr S) : Prop :=
  (goodness Ω C t σ).1
abbrev ReadGood {Γ : List (Expr S)} {M T : Expr S} (t : TypingTree P Γ M T) (σ : Nat → Expr S) : Prop :=
  (goodness Ω C t σ).2

def Relevant (Γ : List (Expr S)) (M : Expr S) : Prop :=
  ∃ K ∈ C, Reach (PrimaryEdge P) (Profile P Γ M) K
namespace Relevant
variable {Ω C}
theorem pred {Γ Δ : List (Expr S)} {M N : Expr S} (h : Relevant (P := P) C Γ M)
    (hp : Reach (PrimaryEdge P) (Profile P Δ N) (Profile P Γ M)) : Relevant (P := P) C Δ N := by
  obtain ⟨K,hK,hp'⟩ := h
  exact ⟨K,hK,hp.trans hp'⟩
end Relevant

variable (hw : SystemWeaklyNormalizing P) (hC : IsComponent (PrimaryEdge P) C)
include hw hC
theorem relevant_actual_mem {Γ : List (Expr S)} {M : Expr S} {s : S} {σ : Nat → Expr S}
    (ht : HasType P Γ M (.sort s)) (hσ : Ω.TypedSubstitution Γ σ)
    (hr : Relevant (P := P) C Γ M) (hm : Ω.profile (M.subst σ) ∈ C) : Profile P Γ M ∈ C := by
  obtain ⟨K,hK,hp⟩ := hr
  have hg := Ω.profile_subst_growth hw ht hσ
  have hga := ContextTower.HasType.subst ht hσ
  have hpath := Profile.inclusion_path (Ω.profile_feasible hw hga)
    (Profile.feasible (ht.weaklyNormalizing hw) (Profile.nonempty_of_sorted hw ht)) hg
  exact hC.between hm hK hpath.reach hp

theorem normal_baseGood {Γ : List (Expr S)} {M : Expr S} {s : S} {σ : Nat → Expr S}
    (h : HasType P Γ M (.sort s)) (hn : Normal M) (hne : Neutral M)
    (hσ : Ω.TypedSubstitution Γ σ) (hr : Relevant (P := P) C Γ M) {v : Prop}
    (hv : ActiveLayer P C (Ω.profile (Expr.sort s |>.subst σ)) → v) :
    baseGood Ω C M (.sort s) σ v := by
  intro hm
  have hp := relevant_actual_mem Ω C hw hC h hσ hr hm
  rw [Profile.neutral hn hne h] at hp
  exact ⟨s,rfl,hp,hv,fun _ => hne⟩

theorem normal_good {Γ : List (Expr S)} {M T : Expr S} (t : TypingTree P Γ M T)
    (hn : Normal M) (σ : Nat → Expr S) (hσ : Ω.TypedSubstitution Γ σ) :
    (ActiveLayer P C (Ω.profile (T.subst σ)) → ValGood Ω C t σ) ∧
    (∀ s, T = .sort s → Relevant (P := P) C Γ M → ReadGood Ω C t σ) := by
  induction t generalizing σ with
  | var ht hd hc =>
      refine ⟨fun _ => trivial,?_⟩
      intro s hs hr
      subst hs
      exact normal_baseGood Ω C hw hC ht hn (.var _) hσ hr (fun _ => trivial)
  | sort ht ha hc => exact ⟨fun _ => trivial,fun _ _ _ => trivial⟩
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      have hv : ValGood Ω C (.abstraction ht d b hp hc) σ := by
        intro n hn' ha
        exact (ihb hn.lam_body (Expr.consSub n σ) (hσ.cons hn')).1 ha
      refine ⟨fun _ => hv,?_⟩
      intro s hs _
      exact False.elim ((hs ▸ ht).lambda_cannot_have_sort_type)
  | @application Γ g n D E T ht f a hc ihf iha =>
      have hne : Neutral (.app g n) := by
        obtain ⟨s,he⟩ | hne | ⟨D,E,he⟩ | ⟨D,m,he⟩ := ht.normal_shape hn
        · cases he
        · exact hne
        · cases he
        · cases he
      have hv : ValGood Ω C (.application ht f a hc) σ := by
        dsimp only [ValGood,goodness]
        split
        · rename_i hf
          exact ⟨(ihf hn.app_left σ hσ).1 hf,fun ha => (iha hn.app_right σ hσ).1 ha⟩
        · exact hne
      refine ⟨fun _ => hv,?_⟩
      intro s hs hr
      subst hs
      exact normal_baseGood Ω C hw hC ht hn hne hσ hr (fun _ => hv)
  | @product Γ D E a b c T ht d e hr hc ihd ihe =>
      have hpi : HasType P Γ (.pi D E) (.sort c) := .product d.typing e.typing hr
      have hp := Profile.triple hw hpi
      have hg : Relevant (P := P) C Γ (.pi D E) →
          (Ω.profile (D.subst σ) ∈ C → ReadGood Ω C d σ) ∧
          (∀ n, Ω.HasType n (D.subst σ) → Ω.profile (E.subst (Expr.consSub n σ)) ∈ C →
            ReadGood Ω C e (Expr.consSub n σ)) := by
        intro hrel
        constructor
        · intro _
          exact (ihd hn.pi_domain σ hσ).2 a rfl (hrel.pred (.single (.domain hp)))
        · intro n hn' _
          exact (ihe hn.pi_body (Expr.consSub n σ) (hσ.cons hn')).2 b rfl
            (hrel.pred (.single (.codomain hp)))
      constructor
      · intro hat hcc
        have hconv : (T.subst σ).normalForm = .sort c :=
          (Expr.normalForm_converts ((ContextTower.HasType.subst ht hσ).type_weaklyNormalizing hw)
            ((ContextTower.HasType.subst hpi hσ).type_weaklyNormalizing hw) (hc.subst σ)).trans
              (Expr.normalForm_of_normal (Normal.sort c))
        have hax : (AxProfile P c).Nonempty := by
          have hh := hat.nonempty
          rwa [← Ω.profile_normalForm (T.subst σ),hconv,Ω.profile_sort] at hh
        have hs : ({c} : Set S) ⊆ Profile P Γ (.pi D E) := by
          intro r hr'
          have he : r = c := hr'
          subst r
          exact hpi.normalForm hw
        exact hg ⟨{c},hcc.1,(Profile.inclusion_path hp.product (FeasibleProfile.singleton hax) hs).reach⟩
      · intro _ _ hrel
        exact fun _ => hg hrel

end ObservationValues
end PureTypeSystem

namespace PureTypeSystem.ObservationValues
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

/-- Normal-syntax values forget all stored generation choices; normal Reads
also forget their literal sort choice. No functionality hypothesis is used. -/
theorem normal_tree_independence {Γ : List (Expr S)} {M T : Expr S}
    (t : TypingTree P Γ M T) : Normal M →
    ∀ {U : Expr S} (t' : TypingTree P Γ M U) (e : Environment (hw := hw) Ω C hno Γ),
    (Converts T U → (preEvaluate Ω C hno t e).parameter = (preEvaluate Ω C hno t' e).parameter) ∧
    (∀ s s', T = .sort s → U = .sort s' →
      (preEvaluate Ω C hno t e).read.val = (preEvaluate Ω C hno t' e).read.val) := by
  induction t with
  | @var Γ n A T ht hd hc =>
      intro _ U t' e
      cases t' with
      | var ht' hd' hc' =>
          have hv : (PreResult.lookup ht hd hc e).parameter = (PreResult.lookup ht' hd' hc' e).parameter := by
            rw [PreResult.lookup_parameter,PreResult.lookup_parameter]
          refine ⟨fun _ => hv,?_⟩
          intro s s' hs hs'
          have he : s = s' := (hs ▸ hs' ▸ HasType.neutral_unique (.var n) ht ht').sort_inj
          subst s'; subst T; subst U
          apply PreResult.baseRead_congr ht ht' rfl rfl Iff.rfl
          exact fun ha hb => PreResult.val_congr _ _ hv ha hb
  | sort ht ha hc =>
      intro _ U t' e
      cases t' with
      | sort ht' ha' hc' =>
          constructor
          · intro hh
            apply PreResult.parameter_congr _ _ (e.type_convert_eq ht ht' hh)
            intro _ _
            exact distinguished_congr Ω C hno (e.type_convert_eq ht ht' hh)
          · exact fun _ _ _ _ => rfl
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      intro hn U t' e
      cases t' with
      | @abstraction _ _ _ E' a' s' _ ht' d' b' hp' hc' =>
          constructor
          · intro hh
            have hproducts : Converts (.pi D E) (.pi D E') := .trans _ _ _ (.symm _ _ hc) (.trans _ _ _ hh hc')
            have hEE := hproducts.product_compatibility.2
            apply PreResult.parameter_congr _ _ (e.type_convert_eq ht ht' hh)
            apply PreResult.abstraction_val_congr ht ht' hp hp' hc hc' _ _ e e (e.type_convert_eq ht ht' hh)
            intro n n' hnt hn' he p hpa hpb hact hact'
            subst n'
            exact PreResult.val_congr _ _ ((ihb hn.lam_body b' (e.cons hnt p hpa)).1 hEE) hact hact'
          · intro r r' hs _
            exact False.elim ((hs ▸ ht).lambda_cannot_have_sort_type)
  | @application Γ g n D E T ht f a hc ihf iha =>
      intro hn U t' e
      cases t' with
      | @application _ _ _ D' E' _ ht' f' a' hc' =>
          have hg : Neutral g := by
            obtain ⟨s,he⟩ | hne | ⟨D,E,he⟩ | ⟨D,m,he⟩ := ht.normal_shape hn
            · cases he
            · cases hne with | app hne => exact hne
            · cases he
            · cases he
          have hF := HasType.neutral_unique hg f.typing f'.typing
          have hD := hF.product_compatibility.1
          have hv : ∀ (hh : Converts T U),
              (preEvaluate Ω C hno (.application ht f a hc) e).parameter =
              (preEvaluate Ω C hno (.application ht' f' a' hc') e).parameter := by
            intro hh
            apply PreResult.parameter_congr _ _ (e.type_convert_eq ht ht' hh)
            apply PreResult.application_val_congr ht ht' f.typing f'.typing a.typing a'.typing hc hc'
              _ _ _ _ e e (e.type_convert_eq ht ht' hh) (e.type_convert_eq f.typing f'.typing hF) rfl
            · exact fun ha hb => PreResult.val_congr _ _ ((ihf hn.app_left f' e).1 hF) ha hb
            · exact (iha hn.app_right a' e).1 hD
          refine ⟨hv,?_⟩
          intro s s' hs hs'
          have hh := HasType.neutral_unique (.app hg) ht ht'
          have he : s = s' := (hs ▸ hs' ▸ hh).sort_inj
          subst s'; subst T; subst U
          apply PreResult.baseRead_congr ht ht' rfl rfl Iff.rfl
          exact fun ha hb => PreResult.val_congr _ _ (hv hh) ha hb
  | @product Γ D E a b c T ht d bt hr hc ihd ihb =>
      intro hn U t' e
      cases t' with
      | @product _ _ _ a' b' c' _ ht' d' bt' hr' hc' =>
          have hpc : (PreResult.productCandidate d.typing bt.typing hr (preEvaluate Ω C hno d)
              (preEvaluate Ω C hno bt) e).val =
              (PreResult.productCandidate d'.typing bt'.typing hr' (preEvaluate Ω C hno d')
                (preEvaluate Ω C hno bt') e).val := by
            apply PreResult.productCandidate_congr d.typing bt.typing hr d'.typing bt'.typing hr' _ _ _ _ e e rfl rfl
            · exact fun _ => (ihd hn.pi_domain d' e).2 a a' rfl rfl
            · intro n hn' hn'' p hp hp' _
              exact (ihb hn.pi_body bt' (e.cons hn' p hp)).2 b b' rfl rfl
          constructor
          · intro hh
            have hsorts : Converts (.sort c) (.sort c') := .trans _ _ _ (.symm _ _ hc) (.trans _ _ _ hh hc')
            have he : c = c' := hsorts.sort_inj
            apply PreResult.parameter_congr _ _ (e.type_convert_eq ht ht' hh)
            apply PreResult.product_val_congr ht ht' d.typing bt.typing hr d'.typing bt'.typing hr'
              hc hc' _ _ _ _ e e (e.type_convert_eq ht ht' hh) rfl
            · exact he ▸ Iff.rfl
            · exact fun _ => hpc
          · intro _ _ _ _
            exact PreResult.product_read_congr ht ht' d.typing bt.typing hr d'.typing bt'.typing hr'
              hc hc' _ _ _ _ e e rfl (fun _ => hpc)
end PureTypeSystem.ObservationValues

namespace PureTypeSystem
universe u

namespace Neutral
variable {S : Type u} {M : Expr S} {ρ : Nat → Nat}
theorem of_rename (h : Neutral (M.rename ρ)) : Neutral M := by
  induction M with
  | var n => exact .var n
  | sort s => cases h
  | lam D m ihD ihm => cases h
  | pi D E ihD ihE => cases h
  | app f n ihf ihn => cases h with | app h => exact .app (ihf h)
theorem rename_iff : Neutral (M.rename ρ) ↔ Neutral M := ⟨of_rename,fun h => h.rename ρ⟩
end Neutral
namespace Expr
variable {S : Type u}
theorem consSub_liftRen (n : Expr S) (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (consSub n σ) ∘ liftRen ρ = consSub n (σ ∘ ρ) := by
  funext i; cases i <;> rfl
end Expr
namespace ObservationValues
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) (C : Set (Set S))

theorem baseGood_rename {M T : Expr S} (ρ : Nat → Nat) (σ : Nat → Expr S) (v : Prop) :
    baseGood Ω C (M.rename ρ) (T.rename ρ) σ v ↔ baseGood Ω C M T (σ ∘ ρ) v := by
  simp only [baseGood,Expr.subst_rename,Expr.rename_eq_sort,Neutral.rename_iff]

theorem goodness_rename {Γ : List (Expr S)} {M T : Expr S} (t : TypingTree P Γ M T)
    {Δ : List (Expr S)} (hΔ : ValidContext P Δ) (ρ : Nat → Nat) (hρ : TypingTree.DeclRenaming Γ Δ ρ)
    (σ : Nat → Expr S) :
    goodness Ω C (t.rename hΔ ρ hρ) σ = goodness Ω C t (σ ∘ ρ) := by
  induction t generalizing Δ ρ σ with
  | var ht hd hc =>
      apply Prod.ext
      · rfl
      · exact propext (baseGood_rename Ω C ρ σ True)
  | sort ht ha hc => rfl
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      have hh : HasType P Δ (D.rename ρ) (.sort a) := d.typing.rename hΔ ρ (hρ.typed hΔ)
      have hb (n : Expr S) := ihb (.cons hΔ hh) (Expr.liftRen ρ) (hρ.lift D) (Expr.consSub n σ)
      simp only [Expr.consSub_liftRen] at hb
      have hv : (∀ n, Ω.HasType n ((D.rename ρ).subst σ) →
          ActiveLayer P C (Ω.profile ((E.rename (Expr.liftRen ρ)).subst (Expr.consSub n σ))) →
          (goodness Ω C (b.rename (.cons hΔ hh) (Expr.liftRen ρ) (hρ.lift D)) (Expr.consSub n σ)).1) ↔
          (∀ n, Ω.HasType n (D.subst (σ ∘ ρ)) →
          ActiveLayer P C (Ω.profile (E.subst (Expr.consSub n (σ ∘ ρ)))) →
          (goodness Ω C b (Expr.consSub n (σ ∘ ρ))).1) := by
        simp only [Expr.subst_rename,Expr.consSub_liftRen,hb]
      apply Prod.ext
      · exact propext hv
      · change baseGood Ω C (Expr.lam D m |>.rename ρ) (T.rename ρ) σ _ = _
        exact (propext (baseGood_rename Ω C ρ σ _)).trans
          (congrArg (baseGood Ω C (.lam D m) T (σ ∘ ρ)) (propext hv))
  | @application Γ g n D E T ht f a hc ihf iha =>
      have hg := ihf hΔ ρ hρ σ
      have hn := iha hΔ ρ hρ σ
      have hv : (goodness Ω C ((TypingTree.application ht f a hc).rename hΔ ρ hρ) σ).1 =
          (goodness Ω C (.application ht f a hc) (σ ∘ ρ)).1 := by
        change (if ActiveLayer P C (Ω.profile ((Expr.pi D E |>.rename ρ).subst σ)) then
          (goodness Ω C (f.rename hΔ ρ hρ) σ).1 ∧
            (ActiveLayer P C (Ω.profile ((D.rename ρ).subst σ)) → (goodness Ω C (a.rename hΔ ρ hρ) σ).1)
          else Neutral ((Expr.app g n).rename ρ)) =
          (if ActiveLayer P C (Ω.profile ((Expr.pi D E).subst (σ ∘ ρ))) then
            (goodness Ω C f (σ ∘ ρ)).1 ∧
              (ActiveLayer P C (Ω.profile (D.subst (σ ∘ ρ))) → (goodness Ω C a (σ ∘ ρ)).1)
            else Neutral (.app g n))
        rw [hg,hn]
        rw [Expr.subst_rename,Expr.subst_rename]
        split
        · rfl
        · exact propext Neutral.rename_iff
      apply Prod.ext hv
      change baseGood Ω C (Expr.app g n |>.rename ρ) (T.rename ρ) σ _ = _
      exact (propext (baseGood_rename Ω C ρ σ _)).trans
        (congrArg (baseGood Ω C (.app g n) T (σ ∘ ρ)) hv)
  | @product Γ D E a b c T ht d bt hr hc ihd ihb =>
      have hh : HasType P Δ (D.rename ρ) (.sort a) := d.typing.rename hΔ ρ (hρ.typed hΔ)
      have hd := ihd hΔ ρ hρ σ
      have hb (n : Expr S) := ihb (.cons hΔ hh) (Expr.liftRen ρ) (hρ.lift D) (Expr.consSub n σ)
      simp only [Expr.consSub_liftRen] at hb
      let g : Prop := (Ω.profile ((D.rename ρ).subst σ) ∈ C →
          (goodness Ω C (d.rename hΔ ρ hρ) σ).2) ∧
          ∀ n, Ω.HasType n ((D.rename ρ).subst σ) →
            Ω.profile ((E.rename (Expr.liftRen ρ)).subst (Expr.consSub n σ)) ∈ C →
              (goodness Ω C (bt.rename (.cons hΔ hh) (Expr.liftRen ρ) (hρ.lift D)) (Expr.consSub n σ)).2
      let g' : Prop := (Ω.profile (D.subst (σ ∘ ρ)) ∈ C → (goodness Ω C d (σ ∘ ρ)).2) ∧
          ∀ n, Ω.HasType n (D.subst (σ ∘ ρ)) → Ω.profile (E.subst (Expr.consSub n (σ ∘ ρ))) ∈ C →
            (goodness Ω C bt (Expr.consSub n (σ ∘ ρ))).2
      have he : g = g' := by
        dsimp only [g,g']
        simp only [hd,hb,Expr.subst_rename,Expr.consSub_liftRen]
      change ((({c} : Set S) ∈ C ∧ Ω.profile ((Expr.pi D E |>.rename ρ).subst σ) ∈ C) → g,
        Ω.profile ((Expr.pi D E |>.rename ρ).subst σ) ∈ C → g) =
        ((({c} : Set S) ∈ C ∧ Ω.profile (Expr.pi D E |>.subst (σ ∘ ρ)) ∈ C) → g',
        Ω.profile (Expr.pi D E |>.subst (σ ∘ ρ)) ∈ C → g')
      simp only [Expr.subst_rename,he]

theorem valGood_retarget {Γ : List (Expr S)} {M T T' : Expr S} (t : TypingTree P Γ M T)
    (ht : HasType P Γ M T') (hc : Converts T' T) (σ : Nat → Expr S) :
    ValGood Ω C (t.retarget ht hc) σ ↔ ValGood Ω C t σ := by
  cases t <;> exact Iff.rfl
end ObservationValues

namespace ContextTower
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)
theorem profile_converts {A B : Expr S} (hA : WeaklyNormalizing A) (hB : WeaklyNormalizing B)
    (hc : Converts A B) : Ω.profile A = Ω.profile B := by
  rw [← Ω.profile_normalForm A,← Ω.profile_normalForm B,Expr.normalForm_converts hA hB hc]

variable (hw : SystemWeaklyNormalizing P)
include hw

theorem instantiate_profile_ascent {Γ : List (Expr S)} {D E n : Expr S} {s : S}
    (hp : PureTypeSystem.HasType P Γ (.pi D E) (.sort s))
    (hn : PureTypeSystem.HasType P Γ n D) {σ : Nat → Expr S} (hσ : Ω.TypedSubstitution Γ σ) :
    PositivePath (PrimaryEdge P) (Ω.profile ((E.instantiate n).subst σ))
      (Ω.profile (Expr.pi D E |>.subst σ)) := by
  have hp' := ContextTower.HasType.subst hp hσ
  have hn' := ContextTower.HasType.subst hn hσ
  obtain ⟨J,htr,hpath⟩ := Ω.frame_profiles hw hp' hn'
  rw [← Expr.instantiate_subst]
  exact hpath.trans (.single (.codomain htr))

theorem neutral_profile_ascent {Γ : List (Expr S)} {M T : Expr S}
    (hne : Neutral M) (ht : PureTypeSystem.HasType P Γ M T)
    {σ : Nat → Expr S} (hσ : Ω.TypedSubstitution Γ σ) :
    ∃ n D, M.head = .var n ∧ Lookup Γ n D ∧
      PositivePath (PrimaryEdge P) (Ω.profile (T.subst σ)) (Ω.profile (D.subst σ)) := by
  induction hne generalizing T with
  | var n =>
      obtain ⟨D,hd,hc⟩ := ht.generation
      refine ⟨n,D,rfl,hd,?_⟩
      rw [Ω.profile_converts ((ContextTower.HasType.subst ht hσ).type_weaklyNormalizing hw)
        ((ContextTower.HasType.subst (PureTypeSystem.HasType.lookup ht.valid hd) hσ).type_weaklyNormalizing hw)
        (hc.subst σ)]
      exact .refl
  | @app f a hnf ih =>
      obtain ⟨D,E,hf,ha,hc⟩ := ht.generation_app
      obtain ⟨s,hp⟩ := hf.product_type_sorted
      obtain ⟨n,A,hh,hl,hr⟩ := ih hf
      refine ⟨n,A,hh,hl,?_⟩
      rw [Ω.profile_converts ((ContextTower.HasType.subst ht hσ).type_weaklyNormalizing hw)
        ((ContextTower.HasType.subst (PureTypeSystem.HasType.application hf ha) hσ).type_weaklyNormalizing hw)
        (hc.subst σ)]
      exact (Ω.instantiate_profile_ascent hw hp ha hσ).trans hr
end ContextTower

namespace ObservationValues
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) (C : Set (Set S))
    (hw : SystemWeaklyNormalizing P)
/-- Only nonneutral replacements need the activity guard. Variables that
remain neutral are harmless even at a skipped clause. -/
def SubstitutionGuard (Γ : List (Expr S)) (σ ξ : Nat → Expr S) : Prop :=
  ∀ n D, Lookup Γ n D → ¬ Neutral (σ n) → Ω.profile (D.subst ξ) ∈ ObservationLayers P C →
    ActiveLayer P C (Ω.profile (D.subst ξ))

include hw
 theorem neutral_subst_of_inactive {Γ : List (Expr S)} {M T : Expr S}
    (hne : Neutral M) (ht : HasType P Γ M T) {σ ξ : Nat → Expr S}
    (hξ : Ω.TypedSubstitution Γ ξ) (hguard : SubstitutionGuard Ω C Γ σ ξ)
    (hH : Ω.profile (T.subst ξ) ∈ ObservationLayers P C)
    (hina : ¬ ActiveLayer P C (Ω.profile (T.subst ξ))) : Neutral (M.subst σ) := by
  apply hne.subst_of_head
  intro n hhead
  by_contra hn
  obtain ⟨i,D,hhead',hd,hpath⟩ := Ω.neutral_profile_ascent hw hne ht hξ
  have he : i = n := Expr.var.inj (hhead'.symm.trans hhead)
  subst i
  have hI := ObservationLayers.positive hH hpath
  exact hina ((hguard n D hd hn hI).predecessor (ObservationLayers.secondary hH hpath).reach)

 theorem skipped_application_subst {Γ : List (Expr S)} {f a D E T : Expr S}
    (h : HasType P Γ (.app f a) T) (hf : HasType P Γ f (.pi D E)) (ha : HasType P Γ a D)
    (hc : Converts T (E.instantiate a)) (hne : Neutral (.app f a))
    {σ ξ : Nat → Expr S} (hξ : Ω.TypedSubstitution Γ ξ)
    (hguard : SubstitutionGuard Ω C Γ σ ξ)
    (hactive : ActiveLayer P C (Ω.profile (T.subst ξ)))
    (hina : ¬ ActiveLayer P C (Ω.profile (Expr.pi D E |>.subst ξ))) :
    Neutral (Expr.app f a |>.subst σ) := by
  have hF : Ω.profile (Expr.pi D E |>.subst ξ) ∈ ObservationLayers P C := by
    obtain ⟨s,hp⟩ := hf.product_type_sorted
    have he := Ω.profile_converts ((ContextTower.HasType.subst h hξ).type_weaklyNormalizing hw)
      ((ContextTower.HasType.subst (HasType.application hf ha) hξ).type_weaklyNormalizing hw) (hc.subst ξ)
    exact ObservationLayers.positive (he ▸ hactive.layer) (Ω.instantiate_profile_ascent hw hp ha hξ)
  have hnf : Neutral f := by cases hne; assumption
  exact .app (neutral_subst_of_inactive Ω C hw hnf hf hξ hguard hF hina)

 theorem skipped_read_subst {Γ : List (Expr S)} {M : Expr S} {s : S}
    (h : HasType P Γ M (.sort s)) (hne : Neutral M)
    {σ ξ : Nat → Expr S} (hξ : Ω.TypedSubstitution Γ ξ)
    (hguard : SubstitutionGuard Ω C Γ σ ξ) (hs : ({s} : Set S) ∈ C)
    (hina : ¬ ActiveLayer P C (AxProfile P s)) : Neutral (M.subst σ) := by
  have hH : AxProfile P s ∈ ObservationLayers P C :=
    ⟨s,hs,Profile.neutral_axiom hne h,.refl⟩
  apply neutral_subst_of_inactive Ω C hw hne h hξ hguard
  · simpa only [Expr.subst,Ω.profile_sort] using hH
  · simpa only [Expr.subst,Ω.profile_sort] using hina
end ObservationValues
end PureTypeSystem

namespace PureTypeSystem.ObservationValues
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

theorem distinguished_base (T : ActiveType Ω C) :
    RawValue.base (hw := hw) Ω C hno (distinguished (hw := hw) Ω C hno T).val = topBase Ω := by
  unfold distinguished
  split
  · exact (ActualPlain.schema hw).distinguished_base _ _ _
  · split
    · rfl
    · rfl

namespace PreResult
variable {Ω C hno} {Γ : List (Expr S)} {M : Expr S} {s : S}
    {e : Environment (hw := hw) Ω C hno Γ}
theorem baseRead_eq (h : HasType P Γ M (.sort s))
    (v : ActiveLayer P C (Ω.profile (Expr.sort s |>.subst e.images).normalForm) →
      Value (hw := hw) Ω C hno (Expr.sort s |>.subst e.images).normalForm)
    (hM : Ω.profile (M.subst e.images).normalForm ∈ C) (hs : ({s} : Set S) ∈ C)
    (ha : ActiveLayer P C (Ω.profile (Expr.sort s |>.subst e.images).normalForm)) :
    (baseRead h v).val = ((RawValue.base Ω C hno (v ha).val) (e.actualExpression h)).val := by
  have hex : ∃ s', Expr.sort s = Expr.sort s' ∧ ({s'} : Set S) ∈ C := ⟨s,rfl,hs⟩
  simp only [baseRead,dite_eq_left hM,dite_eq_left hex,dite_eq_left ha]

theorem product_read_base {D E : Expr S} {a b c : S}
    (h : HasType P Γ (.pi D E) (.sort s))
    (hd : HasType P Γ D (.sort a)) (hb : HasType P (D :: Γ) E (.sort b))
    (hr : P.rule a b c) (hc : Converts (.sort s) (.sort c))
    (ed : Evaluator (hw := hw) Ω C hno Γ D (.sort a))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) E (.sort b))
    (e : Environment (hw := hw) Ω C hno Γ)
    (hm : Ω.profile (Expr.pi D E |>.subst e.images).normalForm ∈ C) (hs : ({s} : Set S) ∈ C)
    (ha : ActiveLayer P C (Ω.profile (Expr.sort s |>.subst e.images).normalForm)) :
    (product h hd hb hr hc ed eb e).read.val =
      ((RawValue.base Ω C hno ((product h hd hb hr hc ed eb e).val ha).val) (e.actualExpression h)).val := by
  have hh : ({c} : Set S) ∈ C ∧ Ω.profile (Expr.pi D E |>.subst e.images).normalForm ∈ C := ⟨hc.sort_inj ▸ hs,hm⟩
  dsimp only [product]
  rw [ite_eq_left hm,dite_eq_left hh,withBase_base]
  simp only [Base.update_same]
end PreResult

theorem preEvaluate_read_base {Γ : List (Expr S)} {M : Expr S} {s : S}
    (t : TypingTree P Γ M (.sort s)) (e : Environment (hw := hw) Ω C hno Γ)
    (hM : Ω.profile (M.subst e.images).normalForm ∈ C) (hs : ({s} : Set S) ∈ C)
    (ha : ActiveLayer P C (Ω.profile (Expr.sort s |>.subst e.images).normalForm)) :
    (preEvaluate Ω C hno t e).read.val =
      ((RawValue.base Ω C hno ((preEvaluate Ω C hno t e).val ha).val) (e.actualExpression t.typing)).val := by
  cases t with
  | var ht hd hc => exact PreResult.baseRead_eq ht _ hM hs ha
  | sort ht hax hc =>
      change (Candidates.Top Ω (Expr.sort _ |>.subst e.images).normalForm) = _
      rw [show ((preEvaluate Ω C hno (.sort ht hax hc) e).val ha).val =
        (distinguished Ω C hno (e.activeType ht ha)).val from rfl,distinguished_base]
      rfl
  | product ht d b hr hc => exact PreResult.product_read_base ht d.typing b.typing hr hc _ _ e hM hs ha
  | abstraction ht d b hp hc => exact PreResult.baseRead_eq ht _ hM hs ha
  | application ht f a hc => exact PreResult.baseRead_eq ht _ hM hs ha

omit hno [Fintype S] in
theorem baseGood_active_iff {M : Expr S} {s : S} {σ : Nat → Expr S} {v : Prop}
    (hm : Ω.profile (M.subst σ) ∈ C) (hs : ({s} : Set S) ∈ C)
    (ha : ActiveLayer P C (Ω.profile (Expr.sort s |>.subst σ))) :
    baseGood Ω C M (.sort s) σ v ↔ v := by
  constructor
  · intro h
    obtain ⟨s',_,_,hv,_⟩ := h hm
    exact hv ha
  · intro hv _
    exact ⟨s,rfl,hs,fun _ => hv,fun hn => False.elim (hn ha)⟩

omit hno [Fintype S] in
theorem readGood_active_iff {Γ : List (Expr S)} {M : Expr S} {s : S}
    (t : TypingTree P Γ M (.sort s)) {σ : Nat → Expr S}
    (hm : Ω.profile (M.subst σ) ∈ C) (hs : ({s} : Set S) ∈ C)
    (ha : ActiveLayer P C (Ω.profile (Expr.sort s |>.subst σ))) :
    ReadGood Ω C t σ ↔ ValGood Ω C t σ := by
  cases t with
  | var ht hd hc => exact baseGood_active_iff Ω C hm hs ha
  | sort ht hax hc => exact Iff.rfl
  | product ht d b hr hc =>
      dsimp only [ReadGood,ValGood,goodness]
      have hc' := hc.sort_inj
      simp only [← hc',hm,hs,true_and,true_implies]
  | abstraction ht d b hp hc => exact baseGood_active_iff Ω C hm hs ha
  | application ht f a hc => exact baseGood_active_iff Ω C hm hs ha
end PureTypeSystem.ObservationValues

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Relations
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.Labelled
universe u
variable {S : Type u} {P : Specification S}
namespace ChannelCode
variable (R : ChannelCode S)
/-- The predicate-variable callback P ↦ P@y. -/
def evalPredBody (T y : Expr S) := (R.rename Nat.succ).eval (T.rename Nat.succ) (.var 0) (y.rename Nat.succ)
def compareBody (L : LogicCode S) (T y z : Expr S) :=
  (L.rename Nat.succ).iff (R.evalPredBody T y) (R.evalPredBody T z)
/-- Source observational relation, with its actual Good predicate callback. -/
def relation (L : LogicCode S) (K : QuantifierCode S) (T G y z : Expr S) :=
  L.guardAll K (R.predicateType T) G (R.compareBody L T y z)

end ChannelCode

/-- Five odd segments and the original source channel for tagged copies. -/
structure ThreeCopyCode (S : Type u) where
  source : DataWrapper S true
  first : DataWrapper S true
  inner : DoubleCode S
  outer : DoubleCode S
namespace ThreeCopyCode
variable (R : ThreeCopyCode S)
def rename (ρ : Nat → Nat) : ThreeCopyCode S :=
  ⟨R.source.rename ρ,R.first.rename ρ,R.inner.rename ρ,R.outer.rename ρ⟩
def subst (σ : Nat → Expr S) : ThreeCopyCode S :=
  ⟨R.source.subst σ,R.first.subst σ,R.inner.subst σ,R.outer.subst σ⟩
def firstType (T : Expr S) := R.first.apply T
def middleType (T : Expr S) := R.inner.carrier (R.firstType T)
def carrier (T : Expr S) := R.outer.carrier (R.middleType T)
def bitInner (L : LogicCode S) (T y : Expr S) :=
  R.outer.recover L (R.middleType T) y (R.inner.bitBody L (R.firstType T))
def bitOuter (L : LogicCode S) (T y : Expr S) := R.outer.bit L (R.middleType T) y
def observe (L : LogicCode S) (T y a : Expr S) :=
  R.outer.recover L (R.middleType T) y
    (R.inner.recBody L (R.firstType T) (R.first.contraCallback T a))
def tagged (L : LogicCode S) (t : Fin 3) (T x : Expr S) :=
  R.outer.emb L (t == 2) (R.middleType T)
    (R.inner.emb L (t == 1) (R.firstType T) (DataWrapper.reencode R.source R.first T x))

variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
structure Formed (L : LogicSetup P Γ γ C) (I X J₁ J₂ J₃ J₄ J₅ : Set S) : Prop where
  source : R.source.Formed L I X
  first : R.first.Formed L I J₁
  inner : R.inner.Formed L J₁ J₂ J₃
  outer : R.outer.Formed L J₃ J₄ J₅
end ThreeCopyCode

namespace ChannelCode
variable (R : ChannelCode S)
def roundRespectBody (L : LogicCode S) (T p : Expr S) :=
  (L.rename Nat.succ).iff ((R.rename Nat.succ).eval (T.rename Nat.succ) (p.rename Nat.succ) (.var 0))
    ((R.rename Nat.succ).eval (T.rename Nat.succ) (p.rename Nat.succ)
      ((R.rename Nat.succ).round (T.rename Nat.succ) (.var 0)))
def roundRespect (L : LogicCode S) (K : QuantifierCode S) (T p : Expr S) :=
  K.all (R.logicalType T) (R.roundRespectBody L T p)
def goodBody (L : LogicCode S) (K : QuantifierCode S) (T Q : Expr S) :=
  (L.rename Nat.succ).conj
    ((R.rename Nat.succ).roundRespect (L.rename Nat.succ) (K.rename Nat.succ) (T.rename Nat.succ) (.var 0)) Q

end ChannelCode

namespace ChannelCode
variable (R : ChannelCode S)

/-- Source class callback w ↦ (w ∼ y); G retains its predicate binder. -/
def classBody (L : LogicCode S) (K : QuantifierCode S) (T G y : Expr S) :=
  (R.rename Nat.succ).relation (L.rename Nat.succ) (K.rename Nat.succ) (T.rename Nat.succ)
    (G.rename (Expr.liftRen Nat.succ)) (.var 0) (y.rename Nat.succ)
def classPred (L : LogicCode S) (K : QuantifierCode S) (T G y : Expr S) :=
  R.pred T (R.classBody L K T G y)
def unionBody (L : LogicCode S) (K : QuantifierCode S) (T G y z : Expr S) :=
  (L.rename Nat.succ).disj (R.classBody L K T G y) (R.classBody L K T G z)
def unionPred (L : LogicCode S) (K : QuantifierCode S) (T G y z : Expr S) :=
  R.pred T (R.unionBody L K T G y z)

end ChannelCode

namespace LogicCode
variable (L : LogicCode S)
def negBody (Q : Expr S) := (L.rename Nat.succ).neg Q
def ex (K : QuantifierCode S) (T Q : Expr S) := L.neg (K.all T (L.negBody Q))
end LogicCode

namespace ChannelCode
variable (R : ChannelCode S)

def evalBody (T p : Expr S) := (R.rename Nat.succ).eval (T.rename Nat.succ) (p.rename Nat.succ) (.var 0)
def predCompareBody (L : LogicCode S) (T p q : Expr S) :=
  (L.rename Nat.succ).iff (R.evalBody T p) (R.evalBody T q)
def predCompare (L : LogicCode S) (K : QuantifierCode S) (T p q : Expr S) :=
  K.all (R.logicalType T) (R.predCompareBody L T p q)

end ChannelCode

end PureTypeSystem.Labelled

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Pairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.Labelled

section
universe u
variable {S : Type u} {P : Specification S}
namespace ChannelCode
variable (R : ChannelCode S)

/-- Class and edge query tags in the source's fixed seven structural tags. -/
def classTag (t : Fin 3) : Fin 7 := ⟨t.val+1,by omega⟩
def edgeTag (t : Bool) : Fin 7 := if t then 5 else 4

def isClass (L : LogicCode S) (KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (t : Fin 3) (y : Expr S) :=
  (Q (classTag t)).instantiate (R.classPred L KP T G y)
def edge (L : LogicCode S) (KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (t : Bool) (y z : Expr S) :=
  L.conj (R.isClass L KP T G Q 0 y)
    (L.conj (R.isClass L KP T G Q (if t then 2 else 1) z)
      ((Q (edgeTag t)).instantiate (R.unionPred L KP T G y z)))
def formExBody (L : LogicCode S) (KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p z : Expr S) :=
  (L.rename Nat.succ).conj
    ((R.rename Nat.succ).edge (L.rename Nat.succ) (KP.rename Nat.succ) (T.rename Nat.succ)
      (G.rename (Expr.liftRen Nat.succ)) (fun t => (Q t).rename (Expr.liftRen Nat.succ)) false (.var 0) (z.rename Nat.succ))
    ((R.rename Nat.succ).eval (T.rename Nat.succ) (p.rename Nat.succ) (.var 0))
def pairForm (L : LogicCode S) (KY KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p a z : Expr S) :=
  L.disj (L.ex KY (R.logicalType T) (R.formExBody L KP T G Q p z))
    (R.edge L KP T G Q true a z)
def pairBody (L : LogicCode S) (KY KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p a : Expr S) :=
  (R.rename Nat.succ).pairForm (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ)
    (T.rename Nat.succ) (G.rename (Expr.liftRen Nat.succ))
    (fun t => (Q t).rename (Expr.liftRen Nat.succ)) (p.rename Nat.succ) (a.rename Nat.succ) (.var 0)
def pairPred (L : LogicCode S) (KY KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p a : Expr S) := R.pred T (R.pairBody L KY KP T G Q p a)

end ChannelCode

namespace DoubleCode
variable (R : DoubleCode S)

-- This body exposes the decoded predicate as a data map on exact BP values.
def decodeMap (U : DataWrapper S true) (L : LogicCode S) (T : Expr S) :=
  (R.rename Nat.succ).decode (U.rename Nat.succ) (L.rename Nat.succ) (T.rename Nat.succ) (.var 0)

def bpBottom (L : LogicCode S) (T : Expr S) := R.first.build (R.big T) (L.bottom.rename Nat.succ)
def dummy (L : LogicCode S) (T : Expr S) := R.second.build (R.bpType T) (L.top.rename Nat.succ)
def isDummy (L : LogicCode S) (T o : Expr S) := R.second.observe (R.bpType T) o (R.bpBottom L T)
def markBody (L : LogicCode S) (t : Fin 8) (T c₀ : Expr S) :=
  R.first.contraCallback (R.big T) (R.tagged L (queryTag t) T c₀)
def pointBody (U : DataWrapper S true) (L : LogicCode S) (T c₀ c : Expr S) :=
  (L.rename Nat.succ).conj (R.markBody L 7 T c₀)
    ((U.contraCallback T c).compose (R.decodeMap U L T))
def point (U : DataWrapper S true) (L : LogicCode S) (T c₀ c : Expr S) :=
  R.second.build (R.bpType T) (R.pointBody U L T c₀ c)

end DoubleCode

namespace DoubleCode
variable (R : DoubleCode S)
/-- Source Bundle is a fixed data term; no non-dummy proof enters its code. -/
def bundleBody (L : LogicCode S) (A d m y : Expr S) :=
  (L.rename Nat.succ).cond (R.first.contraCallback A d)
    (R.first.contraCallback A m) (R.first.contraCallback A y)
def bundle (L : LogicCode S) (A d m y : Expr S) := R.second.build (R.first.apply A) (R.bundleBody L A d m y)
/-- The outer access predicate, with the exact inner data callback `fi`. -/
def accessBody (L : LogicCode S) (A guard w fi : Expr S) :=
  (L.rename Nat.succ).cond guard (L.top.rename Nat.succ)
    ((R.second.evalCallback (R.first.apply A) w).compose fi)
def accessProbe (L : LogicCode S) (A guard w fi : Expr S) :=
  R.first.build A (R.accessBody L A guard w fi)
def access (L : LogicCode S) (A guard w fi : Expr S) :=
  R.second.observe (R.first.apply A) w (R.accessProbe L A guard w fi)

end DoubleCode

namespace DoubleCode
variable (R : DoubleCode S)
def dummyBody (L : LogicCode S) (T : Expr S) :=
  R.second.contraCallback (R.bpType T) (R.bpBottom L T)
def queryBody (U : DataWrapper S true) (L : LogicCode S) (T p : Expr S) :=
  R.second.contraCallback (R.bpType T) (R.encode U L 7 T p)
def innerBody (U : DataWrapper S true) (L : LogicCode S) (T p : Expr S) :=
  (L.rename Nat.succ).cond (R.dummyBody L T) (L.bottom.rename Nat.succ)
    (R.queryBody U L T p)
def innerProbe (U : DataWrapper S true) (L : LogicCode S) (T p : Expr S) :=
  R.first.build (R.paramType T) (R.innerBody U L T p)

end DoubleCode

namespace DoubleCode

section
variable (R : DoubleCode S)

def innerMap (U : DataWrapper S true) (L : LogicCode S) (T : Expr S) :=
  (R.rename Nat.succ).innerProbe (U.rename Nat.succ) (L.rename Nat.succ) (T.rename Nat.succ) (.var 0)
/-- The genuine predicate binder of qry_t(m,P), distinct from the parameter
binder used by Access. -/
def queryPredBody (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T m : Expr S) :=
  (R.rename Nat.succ).query (U.rename Nat.succ) (L.rename Nat.succ) t
    (T.rename Nat.succ) (m.rename Nat.succ) (.var 0)

def accessMap (U : DataWrapper S true) (L : LogicCode S) (T pMap : Expr S) :=
  (R.innerMap U L T).compose pMap
def recoverAccess (U : DataWrapper S true) (L : LogicCode S) (T w pMap : Expr S) :=
  R.access L (R.paramType T) (R.dummyBody L T) w (R.accessMap U L T pMap)
end

end DoubleCode
namespace ProbeCode

section
variable (R : ProbeCode S)
def atType (A : Expr S) := R.funPath.apply (R.funType A)
def specialize (A v : Expr S) := Expr.app .dd v (R.lifting.inject A)
def readBody (w : Expr S) := (R.tail.rename Nat.succ).read (.app .dd (.var 0) (w.rename Nat.succ))
def observe (A v w : Expr S) := R.funPath.observe (R.funType A) (R.specialize A v) (R.readBody w)

end

variable (R : ProbeCode S)
/-- Ordinary data abstraction on the single bundle, before even wrapping. -/
def funBuild (A Q : Expr S) : Expr S := .lam .dd (R.singleType A) ((R.tail.rename Nat.succ).send Q)
def wrappedBuild (A Q : Expr S) := R.funPath.build (R.funType A) (R.funBuild A Q)

end ProbeCode
end

universe u
variable {S : Type u} {P : Specification S}
namespace ProbeCode
variable (R : ProbeCode S)
/-- Uniform V constructor. Q binds w:Single(z-down), then z:Z. -/
def uniform (Q : Expr S) : Expr S := .lam .dd R.domain
  ((R.rename Nat.succ).wrappedBuild ((R.lifting.rename Nat.succ).project (.var 0)) Q)

end ProbeCode
end PureTypeSystem.Labelled

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Relational
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.Labelled

section
universe u
variable {S : Type u} {P : Specification S}

/-- Fixed syntax shared by both source logical channels and the A-independent
probe type. The raw path is literally shared, not an isomorphism hypothesis. -/
structure RelationalCode (S : Type u) where
  probe : ProbeCode S
  logical : DataWrapper S true
  predicate : DataWrapper S true
namespace RelationalCode
variable (R : RelationalCode S)
def rename (ρ : Nat → Nat) : RelationalCode S :=
  ⟨R.probe.rename ρ,R.logical.rename ρ,R.predicate.rename ρ⟩
def subst (σ : Nat → Expr S) : RelationalCode S :=
  ⟨R.probe.subst σ,R.logical.subst σ,R.predicate.subst σ⟩
def channel : ChannelCode S := ⟨R.logical,R.probe.raw,R.predicate⟩
def baseType (A : Expr S) := R.probe.initial.apply A
def queryBody (L : LogicCode S) (t : Fin 7) (A m : Expr S) :=
  R.probe.doubled.queryPredBody R.predicate L t.castSucc (R.probe.rawType A) m
def goodBody (L : LogicCode S) (KY : QuantifierCode S) (A m : Expr S) :=
  R.channel.goodBody L KY (R.baseType A) (R.queryBody L 0 A m)
def pair (L : LogicCode S) (KY KP : QuantifierCode S) (A m p a : Expr S) :=
  R.channel.pairPred L KY KP (R.baseType A) (R.goodBody L KY A m)
    (fun t => R.queryBody L t A m) p a
/-- The source's fixed c_top in the raw wrapper, used only by the markers. -/
def rawTop (L : LogicCode S) (A : Expr S) :=
  R.probe.raw.build (R.baseType A) (L.top.rename Nat.succ)
def point (L : LogicCode S) (A y : Expr S) :=
  R.probe.doubled.point R.predicate L (R.probe.rawType A) (R.rawTop L A)
    (R.channel.toRaw (R.baseType A) y)
def bundle (L : LogicCode S) (A m y : Expr S) :=
  R.probe.doubled.bundle L (R.probe.paramType A)
    (R.probe.doubled.dummy L (R.probe.rawType A)) m (R.point L A y)
def diamond (L : LogicCode S) (A m v y : Expr S) :=
  R.probe.observe A v (R.bundle L A m y)
def partBody (L : LogicCode S) (A m v : Expr S) :=
  (R.rename Nat.succ).diamond (L.rename Nat.succ) (A.rename Nat.succ)
    (m.rename Nat.succ) (v.rename Nat.succ) (.var 0)
def part (L : LogicCode S) (A m v : Expr S) :=
  R.channel.pred (R.baseType A) (R.partBody L A m v)
def sb (L : LogicCode S) (KY KP : QuantifierCode S) (A m v a : Expr S) :=
  R.probe.doubled.query R.predicate L 6 (R.probe.rawType A) m
    (R.pair L KY KP A m (R.part L A m v) a)
def liftBody (L : LogicCode S) (KY KP : QuantifierCode S) (A m a : Expr S) :=
  (R.rename Nat.succ).sb (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ)
    (A.rename Nat.succ) (m.rename Nat.succ) (.var 0) (a.rename Nat.succ)
def lift (L : LogicCode S) (KY KP : QuantifierCode S) (A m a : Expr S) :=
  R.logical.build R.probe.carrier (R.liftBody L KY KP A m a)

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) (I J k p n g j h : Set S)
structure Formed : Prop where
  probe : R.probe.Formed L I J k p n g
  channel : R.channel.Formed L k j p h
end RelationalCode

namespace ChannelSetup
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C}
def relational (K : ChannelSetup L) : RelationalCode S :=
  ⟨K.probe,K.channel.logical,K.channel.predicate⟩
end ChannelSetup
end

section
universe u
variable {S : Type u}
namespace RelationalCode
variable (R : RelationalCode S)
/-- The genuine logical-element binder in i@lift_m(y). -/
def liftEvalBody (L : LogicCode S) (KY KP : QuantifierCode S) (A m i : Expr S) :=
  (R.channel.rename Nat.succ).eval (R.probe.carrier.rename Nat.succ) (i.rename Nat.succ)
    ((R.rename Nat.succ).lift (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ)
      (A.rename Nat.succ) (m.rename Nat.succ) (.var 0))
def predLift (L : LogicCode S) (KY KP : QuantifierCode S) (A m i : Expr S) :=
  R.channel.pred (R.baseType A) (R.liftEvalBody L KY KP A m i)
/-- The data parameter binder, not an assumed semantic universal. -/
def predLiftMap (L : LogicCode S) (KY KP : QuantifierCode S) (A i : Expr S) :=
  (R.rename Nat.succ).predLift (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ)
    (A.rename Nat.succ) (.var 0) (i.rename Nat.succ)
def recoverLift (L : LogicCode S) (KY KP : QuantifierCode S) (A i w : Expr S) :=
  R.probe.doubled.recoverAccess R.predicate L (R.probe.rawType A) w (R.predLiftMap L KY KP A i)
def recoverLiftBody (L : LogicCode S) (KY KP : QuantifierCode S) (A i : Expr S) :=
  (R.rename Nat.succ).recoverLift (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ)
    (A.rename Nat.succ) (i.rename Nat.succ) (.var 0)
/-- The source z_i: the body abstracts z:Z, then w:Single(z↓).
No distinguished A or m occurs in this term. -/
def probeFor (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) :=
  R.probe.uniform ((R.rename Nat.succ).recoverLiftBody (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ)
    ((R.probe.lifting.rename Nat.succ).project (.var 0)) (i.rename Nat.succ))
def le (L : LogicCode S) (KY KP : QuantifierCode S) (i x : Expr S) :=
  R.logical.observe R.probe.carrier x (R.probeFor L KY KP i)
end RelationalCode

end

section
universe u
variable {S : Type u} {P : Specification S}

namespace RelationalCode
variable (R : RelationalCode S)
/-- Binder i:P_X for le(i,x). -/
def leBody (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) :=
  (R.rename Nat.succ).le (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) (.var 0) (x.rename Nat.succ)
def xCompareBody (L : LogicCode S) (KY KP : QuantifierCode S) (x y : Expr S) :=
  (L.rename Nat.succ).iff (R.leBody L KY KP x) (R.leBody L KY KP y)
def xCompare (L : LogicCode S) (KY KP : QuantifierCode S) (x y : Expr S) :=
  KP.all (R.channel.predicateType R.probe.carrier) (R.xCompareBody L KY KP x y)

end RelationalCode
end

section
universe u
namespace RelationalCode
variable {S : Type u} (R : RelationalCode S)
def extStep (L : LogicCode S) (KY KP : QuantifierCode S) (i x y : Expr S) :=
  L.imp (R.xCompare L KY KP x y)
    (L.iff (R.channel.eval R.probe.carrier i x) (R.channel.eval R.probe.carrier i y))
def extAtBody (L : LogicCode S) (KY KP : QuantifierCode S) (i x : Expr S) :=
  (R.rename Nat.succ).extStep (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ)
    (i.rename Nat.succ) (x.rename Nat.succ) (.var 0)
def extAt (L : LogicCode S) (KY KP : QuantifierCode S) (i x : Expr S) :=
  KY.all (R.channel.logicalType R.probe.carrier) (R.extAtBody L KY KP i x)
def extBody (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) :=
  (R.rename Nat.succ).extAt (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ)
    (i.rename Nat.succ) (.var 0)
def extensional (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) :=
  KY.all (R.channel.logicalType R.probe.carrier) (R.extBody L KY KP i)
def validStep (L : LogicCode S) (KY KP : QuantifierCode S) (x i i' : Expr S) :=
  L.imp (R.channel.predCompare L KY R.probe.carrier i i')
    (L.iff (R.le L KY KP i x) (R.le L KY KP i' x))
def validAtBody (L : LogicCode S) (KY KP : QuantifierCode S) (x i : Expr S) :=
  (R.rename Nat.succ).validStep (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ)
    (x.rename Nat.succ) (i.rename Nat.succ) (.var 0)
def validAt (L : LogicCode S) (KY KP : QuantifierCode S) (x i : Expr S) :=
  KP.all (R.channel.predicateType R.probe.carrier) (R.validAtBody L KY KP x i)
def validBody (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) :=
  (R.rename Nat.succ).validAt (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ)
    (x.rename Nat.succ) (.var 0)
def valid (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) :=
  KP.all (R.channel.predicateType R.probe.carrier) (R.validBody L KY KP x)

end RelationalCode
end

universe u
end PureTypeSystem.Labelled

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Specialization
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.Labelled

section
universe u
variable {S : Type u}
/-- The exact three-copy observations at the special carrier. -/
structure ObservationCode (S : Type u) where
  relational : RelationalCode S
  inner : DoubleCode S
  outer : DoubleCode S
namespace ObservationCode
variable (O : ObservationCode S)
def rename (ρ : Nat → Nat) : ObservationCode S :=
  ⟨O.relational.rename ρ,O.inner.rename ρ,O.outer.rename ρ⟩
def subst (σ : Nat → Expr S) : ObservationCode S :=
  ⟨O.relational.subst σ,O.inner.subst σ,O.outer.subst σ⟩
def copies : ThreeCopyCode S := ⟨O.relational.logical,O.relational.probe.raw,O.inner,O.outer⟩
def carrier := O.copies.carrier O.relational.probe.carrier
def tagged (L : LogicCode S) (t : Fin 3) (x : Expr S) :=
  O.copies.tagged L t O.relational.probe.carrier x
def bitInner (L : LogicCode S) (y : Expr S) := O.copies.bitInner L O.relational.probe.carrier y
def bitOuter (L : LogicCode S) (y : Expr S) := O.copies.bitOuter L O.relational.probe.carrier y
def observe (L : LogicCode S) (KY KP : QuantifierCode S) (i y : Expr S) :=
  O.copies.observe L O.relational.probe.carrier y (O.relational.probeFor L KY KP i)
def observeBody (L : LogicCode S) (KY KP : QuantifierCode S) (y : Expr S) :=
  (O.rename Nat.succ).observe (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ)
    (.var 0) (y.rename Nat.succ)
def compareBody (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) :=
  (L.rename Nat.succ).iff (O.observeBody L KY KP y) (O.observeBody L KY KP z)
def compare (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) :=
  KP.all (O.relational.channel.predicateType O.relational.probe.carrier) (O.compareBody L KY KP y z)
def ae (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) :=
  L.conj (L.iff (O.bitInner L y) (O.bitInner L z))
    (L.conj (L.iff (O.bitOuter L y) (O.bitOuter L z)) (O.compare L KY KP y z))

end ObservationCode
end

section
universe u v
variable {S : Type u} {P : Specification S} {α : Type v}
namespace LogicCode
variable (L : LogicCode S)
/-- Right-associated finite disjunction used by the source query object. -/
def choices (xs : List α) (mark property : α → Expr S) : Expr S :=
  xs.foldr (fun t Q => L.disj (L.conj (mark t) (property t)) Q) L.bottom

end LogicCode
end

section
universe u
variable {S : Type u} {P : Specification S}
namespace DoubleCode
variable (R : DoubleCode S)
/-- The source's seven structural branches; evaluation tag 7 is excluded. -/
def realizationBody (U : DataWrapper S true) (L : LogicCode S) (T c : Expr S) (Q : Fin 7 → Expr S) :=
  (L.rename Nat.succ).choices (List.finRange 7)
    (fun t => R.markBody L t.castSucc T c) (fun t => (Q t).compose (R.decodeMap U L T))
def realization (U : DataWrapper S true) (L : LogicCode S) (T c : Expr S) (Q : Fin 7 → Expr S) :=
  R.second.build (R.bpType T) (R.realizationBody U L T c Q)

end DoubleCode
end

section
universe u
structure SpecializedCode (S : Type u) where
  observation : ObservationCode S
  type : Expr S
namespace SpecializedCode
variable {S : Type u} (B : SpecializedCode S)
def rename (ρ : Nat → Nat) : SpecializedCode S := ⟨B.observation.rename ρ,B.type.rename ρ⟩
def subst (σ : Nat → Expr S) : SpecializedCode S := ⟨B.observation.subst σ,B.type.subst σ⟩
def relational := B.observation.relational
def baseType := B.relational.baseType B.type
def xType := B.relational.channel.logicalType B.relational.probe.carrier
def yType := B.observation.carrier
def predType := B.relational.channel.predicateType B.baseType
def xPredType := B.relational.channel.predicateType B.relational.probe.carrier
def ev (v y : Expr S) := B.relational.channel.eval B.baseType v y
def gStep (L : LogicCode S) (KY KP : QuantifierCode S) (v y z : Expr S) :=
  L.imp (B.observation.ae L KY KP y z) (L.iff (B.ev v y) (B.ev v z))
def gAtBody (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) :=
  (B.rename Nat.succ).gStep (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) (v.rename Nat.succ) (y.rename Nat.succ) (.var 0)
def gAt (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) :=
  KY.all B.yType (B.gAtBody L KY KP v y)
def gBody (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  (B.rename Nat.succ).gAt (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) (v.rename Nat.succ) (.var 0)
def propertyG (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  KY.all B.yType (B.gBody L KY KP v)
def cStep (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x w : Expr S) :=
  L.iff (B.ev v w) (B.observation.ae L KY KP w (B.observation.tagged L t x))
def cAtBody (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) :=
  (B.rename Nat.succ).cStep (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) t (v.rename Nat.succ) (x.rename Nat.succ) (.var 0)
def cAt (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) :=
  KY.all B.yType (B.cAtBody L KY KP t v x)
def cBody (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) :=
  (B.rename Nat.succ).cAt (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) t (v.rename Nat.succ) (.var 0)
def propertyC (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) :=
  L.ex KY B.xType (B.cBody L KY KP t v)
def eStep (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x w : Expr S) :=
  L.iff (B.ev v w) (L.disj (B.observation.ae L KY KP w (B.observation.tagged L 0 x)) (B.observation.ae L KY KP w (B.observation.tagged L t x)))
def eAtBody (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) :=
  (B.rename Nat.succ).eStep (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) t (v.rename Nat.succ) (x.rename Nat.succ) (.var 0)
def eAt (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) :=
  KY.all B.yType (B.eAtBody L KY KP t v x)
def eBody (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) :=
  (B.rename Nat.succ).eAt (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) t (v.rename Nat.succ) (.var 0)
def propertyE (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) :=
  L.ex KY B.xType (B.eBody L KY KP t v)
def rPredStep (L : LogicCode S) (_KY _KP : QuantifierCode S) (v x : Expr S) :=
  B.ev v (B.observation.tagged L 1 x)
def rPredBody (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  (B.rename Nat.succ).rPredStep (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) (v.rename Nat.succ) (.var 0)
def rPred (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  B.relational.channel.pred B.relational.probe.carrier (B.rPredBody L KY KP v)
def rStep (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) :=
  L.imp (B.relational.valid L KY KP x) (L.imp (B.ev v (B.observation.tagged L 2 x)) (B.relational.le L KY KP (B.rPred L KY KP v) x))
def rBody (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  (B.rename Nat.succ).rStep (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) (v.rename Nat.succ) (.var 0)
def rAll (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  KY.all B.xType (B.rBody L KY KP v)
def propertyR (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  L.imp (B.relational.extensional L KY KP (B.rPred L KY KP v)) (B.rAll L KY KP v)
end SpecializedCode
end

universe u
variable {S : Type u} {P : Specification S}
namespace ObservationCode
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (O : ObservationCode S) (L : LogicSetup P Γ γ C) (I J k p n g j h : Set S)
structure Formed : Prop where
  relational : O.relational.Formed L I J k p n g j h
  inner : O.inner.Formed L p k p
  outer : O.outer.Formed L p k j
end ObservationCode

end PureTypeSystem.Labelled

namespace PureTypeSystem.Labelled
universe u
variable {S : Type u} {P : Specification S}

namespace SpecializedCode

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (B : SpecializedCode S) (L : LogicSetup P Γ γ C) (I J k p n g j h : Set S)
structure Formed : Prop where
  observation : B.observation.Formed L I J k p n g j h
  type_sorted : HasType P Γ B.type (.sort B.relational.probe.seed)
  type_mode : WellModed γ B.type .data
  shape : B.yType = B.relational.channel.logicalType B.baseType
  outer_second_shape : B.observation.outer.second = B.relational.logical
  outer_first_shape : B.observation.outer.first.apply (B.observation.copies.middleType B.relational.probe.carrier) = B.baseType
end

variable (B : SpecializedCode S)
/-- The seven source structural tags G,C0,Cl,Cr,El,Er,R, in that order. -/
def property (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (v : Expr S) :=
  match t.val with
  | 0 => B.propertyG L KY KP v
  | 1 => B.propertyC L KY KP 0 v
  | 2 => B.propertyC L KY KP 1 v
  | 3 => B.propertyC L KY KP 2 v
  | 4 => B.propertyE L KY KP 1 v
  | 5 => B.propertyE L KY KP 2 v
  | _ => B.propertyR L KY KP v

def propertyBody (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) :=
  (B.rename Nat.succ).property (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) t (.var 0)

/-- This is m0 itself, with no recursive occurrence in its seven properties. -/
def parameter (L : LogicCode S) (KY KP : QuantifierCode S) :=
  B.relational.probe.doubled.realization B.relational.predicate L (B.relational.probe.rawType B.type)
    (B.relational.rawTop L B.type) (B.propertyBody L KY KP)

end SpecializedCode
end PureTypeSystem.Labelled

namespace PureTypeSystem.Labelled

section
universe u
variable {S : Type u} {P : Specification S}

namespace SpecializedCode
variable (B : SpecializedCode S)

def decoded (L : LogicCode S) (t : Fin 7) (v : Expr S) :=
  B.relational.probe.doubled.decode B.relational.predicate L (B.relational.probe.rawType B.type)
    (B.relational.probe.doubled.encode B.relational.predicate L t.castSucc (B.relational.probe.rawType B.type) v)
end SpecializedCode
end

universe u
end PureTypeSystem.Labelled

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Equivalence
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.Labelled

section
universe u
variable {S : Type u} {P : Specification S}
namespace SpecializedCode
variable (B : SpecializedCode S)
def query (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (v : Expr S) :=
  B.relational.probe.doubled.query B.relational.predicate L t.castSucc (B.relational.probe.rawType B.type)
    (B.parameter L KY KP) v
def predCompare (L : LogicCode S) (KY : QuantifierCode S) (v w : Expr S) :=
  B.relational.channel.predCompare L KY B.baseType v w
end SpecializedCode

namespace SpecializedCode
variable (B : SpecializedCode S)
def round (y : Expr S) := B.relational.channel.round B.baseType y
end SpecializedCode

namespace SpecializedCode
variable (B : SpecializedCode S)
def good (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  L.conj (B.relational.channel.roundRespect L KY B.baseType v) (B.query L KY KP 0 v)
def goodBody (L : LogicCode S) (KY KP : QuantifierCode S) :=
  B.relational.goodBody L KY B.type (B.parameter L KY KP)
def relation (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) :=
  B.relational.channel.relation L KP B.baseType (B.goodBody L KY KP) y z

end SpecializedCode
end

section
universe u
variable {S : Type u}
namespace SpecializedCode
variable (B : SpecializedCode S)
def queries (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) :=
  B.relational.queryBody L t B.type (B.parameter L KY KP)
def classPred (L : LogicCode S) (KY KP : QuantifierCode S) (y : Expr S) :=
  B.relational.channel.classPred L KP B.baseType (B.goodBody L KY KP) y
def unionPred (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) :=
  B.relational.channel.unionPred L KP B.baseType (B.goodBody L KY KP) y z
def isClass (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (y : Expr S) :=
  B.relational.channel.isClass L KP B.baseType (B.goodBody L KY KP) (B.queries L KY KP) t y
def edge (L : LogicCode S) (KY KP : QuantifierCode S) (t : Bool) (y z : Expr S) :=
  B.relational.channel.edge L KP B.baseType (B.goodBody L KY KP) (B.queries L KY KP) t y z
def pairForm (L : LogicCode S) (KY KP : QuantifierCode S) (p a z : Expr S) :=
  B.relational.channel.pairForm L KY KP B.baseType (B.goodBody L KY KP) (B.queries L KY KP) p a z
def pair (L : LogicCode S) (KY KP : QuantifierCode S) (p a : Expr S) :=
  B.relational.pair L KY KP B.type (B.parameter L KY KP) p a

end SpecializedCode
end

universe u
variable {S : Type u} {P : Specification S}
inductive ObservationFeature (S : Type u) where
  | inner | outer | probe (i : Expr S)
namespace ObservationFeature
def rename (f : ObservationFeature S) (ρ : Nat → Nat) : ObservationFeature S :=
  match f with | .inner => .inner | .outer => .outer | .probe i => .probe (i.rename ρ)
def subst (f : ObservationFeature S) (σ : Nat → Expr S) : ObservationFeature S :=
  match f with | .inner => .inner | .outer => .outer | .probe i => .probe (i.subst σ)
end ObservationFeature
namespace SpecializedCode
variable (B : SpecializedCode S)
def feature (L : LogicCode S) (KY KP : QuantifierCode S) (f : ObservationFeature S) (y : Expr S) :=
  match f with
  | .inner => B.observation.bitInner L y
  | .outer => B.observation.bitOuter L y
  | .probe i => B.observation.observe L KY KP i y
def featureBody (L : LogicCode S) (KY KP : QuantifierCode S) (f : ObservationFeature S) :=
  (B.rename Nat.succ).feature (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) (f.rename Nat.succ) (.var 0)
def featurePred (L : LogicCode S) (KY KP : QuantifierCode S) (f : ObservationFeature S) :=
  B.relational.channel.pred B.baseType (B.featureBody L KY KP f)
def FeatureFormed (Γ : List (Expr S)) (γ : Nat → Mode) (f : ObservationFeature S) : Prop :=
  match f with
  | .inner | .outer => True
  | .probe i => HasType P Γ i (B.relational.channel.predicateType B.relational.probe.carrier) ∧ WellModed γ i .data

end SpecializedCode

namespace SpecializedCode
variable (B : SpecializedCode S)
def formExBody (L : LogicCode S) (KY KP : QuantifierCode S) (p z : Expr S) :=
  B.relational.channel.formExBody L KP B.baseType (B.goodBody L KY KP) (B.queries L KY KP) p z

end SpecializedCode
end PureTypeSystem.Labelled

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Response
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.Labelled
universe u
variable {S : Type u} {P : Specification S}

namespace SpecializedCode
variable (B : SpecializedCode S)
def diamond (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) :=
  B.relational.diamond L B.type (B.parameter L KY KP) v y
def part (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  B.relational.part L B.type (B.parameter L KY KP) v
def sb (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) :=
  B.relational.sb L KY KP B.type (B.parameter L KY KP) v y
def lift (L : LogicCode S) (KY KP : QuantifierCode S) (y : Expr S) :=
  B.relational.lift L KY KP B.type (B.parameter L KY KP) y

end SpecializedCode

namespace SpecializedCode
variable (B : SpecializedCode S)
def respStep (L : LogicCode S) (KY KP : QuantifierCode S) (v y z : Expr S) :=
  L.imp (B.relation L KY KP y z) (L.iff (B.diamond L KY KP v y) (B.diamond L KY KP v z))
def respAtBody (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) :=
  (B.rename Nat.succ).respStep (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) (v.rename Nat.succ) (y.rename Nat.succ) (.var 0)
def respAt (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) :=
  KY.all B.yType (B.respAtBody L KY KP v y)
def respBody (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  (B.rename Nat.succ).respAt (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) (v.rename Nat.succ) (.var 0)
def response (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  KY.all B.yType (B.respBody L KY KP v)
end SpecializedCode

namespace SpecializedCode
variable (B : SpecializedCode S)
def responsePredStep (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) :=
  B.diamond L KY KP v (B.observation.tagged L 0 x)
def responsePredBody (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  (B.rename Nat.succ).responsePredStep (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) (v.rename Nat.succ) (.var 0)
def responsePred (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  B.relational.channel.pred B.relational.probe.carrier (B.responsePredBody L KY KP v)
end SpecializedCode

end PureTypeSystem.Labelled

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Diagonal
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.Labelled
universe u
variable {S : Type u} {P : Specification S}
namespace SpecializedCode
variable (B : SpecializedCode S)

def delta (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) :=
  B.lift L KY KP (B.observation.tagged L 0 x)
def shiftPredStep (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) :=
  B.relational.channel.eval B.relational.probe.carrier v (B.delta L KY KP x)
def shiftPredBody (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  (B.rename Nat.succ).shiftPredStep (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) (v.rename Nat.succ) (.var 0)
def shiftPred (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  B.relational.channel.pred B.relational.probe.carrier (B.shiftPredBody L KY KP v)

def qStep (L : LogicCode S) (KY KP : QuantifierCode S) (x i : Expr S) :=
  L.imp (B.relational.extensional L KY KP i) (L.imp (B.relational.le L KY KP i x) (B.relational.channel.eval B.relational.probe.carrier i (B.delta L KY KP x)))
def qBody (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) :=
  (B.rename Nat.succ).qStep (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) (i.rename Nat.succ) (.var 0)
def diagonalQ (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) :=
  KP.all B.xPredType (B.qBody L KY KP i)
def diagonalBody (L : LogicCode S) (KY KP : QuantifierCode S) :=
  (L.rename Nat.succ).neg ((B.rename Nat.succ).diagonalQ (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) (.var 0))
def diagonalPred (L : LogicCode S) (KY KP : QuantifierCode S) :=
  B.relational.channel.pred B.relational.probe.carrier (B.diagonalBody L KY KP)
end SpecializedCode

namespace SpecializedCode
variable (B : SpecializedCode S)
def indStep (L : LogicCode S) (KY KP : QuantifierCode S) (i x : Expr S) :=
  L.imp (B.relational.valid L KY KP x) (L.imp (B.relational.le L KY KP i x) (B.relational.channel.eval B.relational.probe.carrier i x))
def indBody (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) :=
  (B.rename Nat.succ).indStep (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) (i.rename Nat.succ) (.var 0)
def induction (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) :=
  KY.all B.xType (B.indBody L KY KP i)

def wfStep (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  B.induction L KY KP (B.responsePred L KY KP v)
def wfBody (L : LogicCode S) (KY KP : QuantifierCode S) :=
  (B.rename Nat.succ).wfStep (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) (.var 0)
def wf (L : LogicCode S) (KY KP : QuantifierCode S) :=
  B.relational.logical.build B.relational.probe.carrier (B.wfBody L KY KP)
end SpecializedCode

end PureTypeSystem.Labelled

namespace PureTypeSystem.Labelled.ChannelReturn
universe u
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {γ : Nat → Mode}
  {C : Set (Set S)} {L : LogicSetup P Γ γ C} {K : ChannelSetup L} (R : ChannelReturn K)
def specialized : SpecializedCode S := ⟨⟨K.relational,R.firstDouble,R.outerDouble⟩,R.type⟩
end PureTypeSystem.Labelled.ChannelReturn

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Substitution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem
universe u
namespace Expr
variable {S : Type u}
def compSub (σ ξ : Nat → Expr S) : Nat → Expr S := fun n => (σ n).subst ξ
@[simp] theorem subst_compSub (M : Expr S) (σ ξ : Nat → Expr S) :
    (M.subst σ).subst ξ = M.subst (compSub σ ξ) := subst_subst M ξ σ
@[simp] theorem lift_comp_cons (σ ξ : Nat → Expr S) (n : Expr S) :
    compSub (liftSub σ) (consSub n ξ) = consSub n (compSub σ ξ) := by
  funext i; cases i with
  | zero => rfl
  | succ i => simp only [compSub,liftSub_succ,subst_rename,Function.comp_def,consSub]
@[simp] theorem raise_subst_cons (M n : Expr S) (ξ : Nat → Expr S) :
    (M.rename Nat.succ).subst (consSub n ξ) = M.subst ξ := by
  rw [subst_rename]; rfl
end Expr
namespace ObservationValues
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) (C : Set (Set S))

namespace SubstitutionGuard
variable {Ω C} {Γ Δ : List (Expr S)} {σ ξ : Nat → Expr S}
theorem lift (hg : SubstitutionGuard Ω C Γ σ (Expr.compSub σ ξ)) (D n : Expr S) :
    SubstitutionGuard Ω C (D :: Γ) (Expr.liftSub σ)
      (Expr.compSub (Expr.liftSub σ) (Expr.consSub n ξ)) := by
  rw [Expr.lift_comp_cons]
  intro i A hi hne hH
  cases hi with
  | zero => exact False.elim (hne (.var 0))
  | succ D hi =>
      have hne' : ¬ Neutral (σ _) := fun h => hne (h.rename Nat.succ)
      simpa only [Expr.raise_subst_cons] using hg _ _ hi hne' (by
        simpa only [Expr.raise_subst_cons] using hH)
end SubstitutionGuard

/-- Goodness assumptions on the values grafted at declarations. -/
def GoodReplacement {Γ Δ : List (Expr S)} {σ : Nat → Expr S}
    (ts : TypingTree.StoredSubstitution P Γ Δ σ) (ξ : Nat → Expr S) : Prop :=
  ∀ i A (hi : Lookup Γ i A), ActiveLayer P C (Ω.profile (A.subst (Expr.compSub σ ξ))) →
    ValGood Ω C (ts i A hi) ξ

 theorem goodReplacement_lift {Γ Δ : List (Expr S)} {σ ξ : Nat → Expr S}
    (ts : TypingTree.StoredSubstitution P Γ Δ σ) (hg : GoodReplacement Ω C ts ξ)
    {D : Expr S} {s : S} (hD : HasType P Δ (D.subst σ) (.sort s)) (n : Expr S) :
    GoodReplacement Ω C (ts.lift hD) (Expr.consSub n ξ) := by
  intro i A hi ha
  cases i with
  | zero =>
      have he : A = D.rename Nat.succ := by cases hi; rfl
      subst A
      exact True.intro
  | succ i =>
      let hex : ∃ A', Lookup Γ i A' ∧ A = A'.rename Nat.succ := by
        cases hi with | succ _ hi => exact ⟨_,hi,rfl⟩
      have he := hex.choose_spec.2
      have hgood := hg i hex.choose hex.choose_spec.1
      have hh : ActiveLayer P C (Ω.profile (hex.choose.subst (Expr.compSub σ ξ))) := by
        rw [Expr.lift_comp_cons,he,Expr.raise_subst_cons] at ha
        exact ha
      have hr := congrArg Prod.fst (goodness_rename Ω C (ts i hex.choose hex.choose_spec.1)
        (.cons hD.valid hD) Nat.succ (TypingTree.DeclRenaming.weaken _) (Expr.consSub n ξ))
      have hgr : ValGood Ω C ((ts i hex.choose hex.choose_spec.1).rename (.cons hD.valid hD)
          Nat.succ (TypingTree.DeclRenaming.weaken _)) (Expr.consSub n ξ) := by
        rw [show ValGood Ω C _ _ = _ from hr]
        exact hgood hh
      let tt := (ts i hex.choose hex.choose_spec.1).rename (.cons hD.valid hD)
        Nat.succ (TypingTree.DeclRenaming.weaken _)
      have he' : A.subst (Expr.liftSub σ) = (hex.choose.subst σ).rename Nat.succ := by
        calc
          A.subst (Expr.liftSub σ) = (hex.choose.rename Nat.succ).subst (Expr.liftSub σ) :=
            congrArg (Expr.subst (Expr.liftSub σ)) he
          _ = (hex.choose.subst σ).rename Nat.succ := by
            rw [Expr.subst_rename,Expr.rename_subst]; rfl
      exact (valGood_retarget Ω C tt (he'.symm ▸ tt.typing)
        (by rw [he']; exact .refl _) (Expr.consSub n ξ)).mpr hgr

 theorem neutral_readGood {Γ : List (Expr S)} {M : Expr S} {s : S}
    (t : TypingTree P Γ M (.sort s)) (hne : Neutral M) (ξ : Nat → Expr S)
    (hs : ({s} : Set S) ∈ C) (ha : ¬ ActiveLayer P C (AxProfile P s)) : ReadGood Ω C t ξ := by
  have hbase (v : Prop) : baseGood Ω C M (.sort s) ξ v := by
    intro _
    refine ⟨s,rfl,hs,?_,fun _ => hne⟩
    intro hh
    exact False.elim (ha (by simpa only [Expr.subst,Ω.profile_sort] using hh))
  cases t with
  | var ht hd hc => exact hbase True
  | sort ht hax hc => cases hne
  | product ht d b hr hc => cases hne
  | abstraction ht d b hp hc => cases hne
  | application ht f a hc => exact hbase _
end ObservationValues
end PureTypeSystem

namespace PureTypeSystem.ObservationValues

section
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

namespace PreResult
variable {Ω C hno} {Γ : List (Expr S)} {M T U : Expr S}

 theorem sort_val_retarget {s t : S} (h : HasType P Γ (.sort s) T)
    (h' : HasType P Γ (.sort s) U) (ht : P.axioms s t) (hc : Converts T (.sort t))
    (hc' : Converts U (.sort t)) (e : Environment (hw := hw) Ω C hno Γ)
    (he : (T.subst e.images).normalForm = (U.subst e.images).normalForm)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (hb : ActiveLayer P C (Ω.profile (U.subst e.images).normalForm)) :
    ((sort h ht hc e).val ha).val = ((sort h' ht hc' e).val hb).val :=
  distinguished_congr Ω C hno he

 theorem lookup_val_retarget {n : Nat} {A : Expr S} (h : HasType P Γ (.var n) T)
    (h' : HasType P Γ (.var n) U) (hd : Lookup Γ n A) (hc : Converts T A)
    (hc' : Converts U A) (e : Environment (hw := hw) Ω C hno Γ)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (hb : ActiveLayer P C (Ω.profile (U.subst e.images).normalForm)) :
    ((lookup h hd hc e).val ha).val = ((lookup h' hd hc' e).val hb).val := by
  apply Option.some.inj
  rw [← parameter_eq _ ha,← parameter_eq _ hb,lookup_parameter,lookup_parameter]

 theorem abstractionAction_retarget {D m E : Expr S} {s : S}
    (h : HasType P Γ (.lam D m) T) (h' : HasType P Γ (.lam D m) U)
    (hp : HasType P Γ (.pi D E) (.sort s)) (hc : Converts T (.pi D E))
    (hc' : Converts U (.pi D E))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) m E)
    (e : Environment (hw := hw) Ω C hno Γ)
    (he : (T.subst e.images).normalForm = (U.subst e.images).normalForm)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (hb : ActiveLayer P C (Ω.profile (U.subst e.images).normalForm))
    (a : FrameKey Ω C (e.activeType h ha)) (b : FrameKey Ω C (e.activeType h' hb))
    (hab : a.argument = b.argument) (p : Option (RawValue (hw := hw) Ω C hno))
    (hpa : PayloadFits Ω C hno a.domain p) (hpb : PayloadFits Ω C hno b.domain p) :
    (abstractionAction h hp hc eb e ha a p hpa).val =
      (abstractionAction h' hp hc' eb e hb b p hpb).val := by
  have hA : (e.activeType h ha).type = (ProductInstance.ofFormation hp e).domainNF.pi
      (ProductInstance.ofFormation hp e).bodyNF :=
    (Expr.normalForm_converts ((ContextTower.HasType.subst h e.typed).type_weaklyNormalizing hw)
      ((ContextTower.HasType.subst hp e.typed).weaklyNormalizing hw) (hc.subst e.images)).trans
      (ProductInstance.ofFormation hp e).product_nf
  have hB : (e.activeType h' hb).type = (ProductInstance.ofFormation hp e).domainNF.pi
      (ProductInstance.ofFormation hp e).bodyNF :=
    he.symm.trans hA
  have hee : (ProductInstance.ofFormation hp e).frameEnvironment hA a p hpa =
      (ProductInstance.ofFormation hp e).frameEnvironment hB b p hpb := by
    dsimp only [ProductInstance.frameEnvironment,ProductInstance.extend,Environment.cons]
    congr 1
    funext n
    cases n <;> simp only [hab]
  dsimp only [abstractionAction]
  apply val_congr
  exact congrArg (fun ee : Environment (hw := hw) Ω C hno (D :: Γ) => (eb ee).parameter) hee

 theorem abstraction_val_retarget {D m E : Expr S} {s : S}
    (h : HasType P Γ (.lam D m) T) (h' : HasType P Γ (.lam D m) U)
    (hp : HasType P Γ (.pi D E) (.sort s)) (hc : Converts T (.pi D E))
    (hc' : Converts U (.pi D E))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) m E)
    (e : Environment (hw := hw) Ω C hno Γ)
    (he : (T.subst e.images).normalForm = (U.subst e.images).normalForm)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (hb : ActiveLayer P C (Ω.profile (U.subst e.images).normalForm)) :
    ((abstraction h hp hc eb e).val ha).val = ((abstraction h' hp hc' eb e).val hb).val := by
  apply lambdaValue_congr Ω C hno he
  exact abstractionAction_retarget h h' hp hc hc' eb e he ha hb

 theorem product_val_retarget {D E : Expr S} {a b c : S}
    (h : HasType P Γ (.pi D E) T) (h' : HasType P Γ (.pi D E) U)
    (hd : HasType P Γ D (.sort a)) (hb : HasType P (D :: Γ) E (.sort b))
    (hr : P.rule a b c) (hc : Converts T (.sort c)) (hc' : Converts U (.sort c))
    (ed : Evaluator (hw := hw) Ω C hno Γ D (.sort a))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) E (.sort b))
    (e : Environment (hw := hw) Ω C hno Γ)
    (he : (T.subst e.images).normalForm = (U.subst e.images).normalForm)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (hu : ActiveLayer P C (Ω.profile (U.subst e.images).normalForm)) :
    ((product h hd hb hr hc ed eb e).val ha).val = ((product h' hd hb hr hc' ed eb e).val hu).val := by
  dsimp only [product]
  split
  · exact withBase_congr Ω C hno he _ _ rfl
  · exact distinguished_congr Ω C hno he

 theorem application_val_retarget {f n D E : Expr S}
    (h : HasType P Γ (.app f n) T) (h' : HasType P Γ (.app f n) U)
    (hf : HasType P Γ f (.pi D E)) (hn : HasType P Γ n D)
    (hc : Converts T (E.instantiate n)) (hc' : Converts U (E.instantiate n))
    (ef : Evaluator (hw := hw) Ω C hno Γ f (.pi D E))
    (en : Evaluator (hw := hw) Ω C hno Γ n D)
    (e : Environment (hw := hw) Ω C hno Γ)
    (he : (T.subst e.images).normalForm = (U.subst e.images).normalForm)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (hu : ActiveLayer P C (Ω.profile (U.subst e.images).normalForm)) :
    ((application h hf hn hc ef en e).val ha).val = ((application h' hf hn hc' ef en e).val hu).val := by
  dsimp only [application,baseResult,applicationValue]
  split
  · rfl
  · exact distinguished_congr Ω C hno he
end PreResult

 theorem preEvaluate_retarget_val {Γ : List (Expr S)} {M T U : Expr S} (t : TypingTree P Γ M T)
    (h : HasType P Γ M U) (hc : Converts U T) (e : Environment (hw := hw) Ω C hno Γ)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (hb : ActiveLayer P C (Ω.profile (U.subst e.images).normalForm)) :
    ((preEvaluate Ω C hno t e).val ha).val =
      ((preEvaluate Ω C hno (t.retarget h hc) e).val hb).val := by
  have he := e.type_convert_eq t.typing h (.symm _ _ hc)
  cases t with
  | var ht hd ht' => exact PreResult.lookup_val_retarget ht h hd ht' (.trans _ _ _ hc ht') e ha hb
  | sort ht ht' htc => exact PreResult.sort_val_retarget ht h ht' htc (.trans _ _ _ hc htc) e he ha hb
  | product ht d b hr htc => exact PreResult.product_val_retarget ht h d.typing b.typing hr htc (.trans _ _ _ hc htc) _ _ e he ha hb
  | abstraction ht d b hp htc => exact PreResult.abstraction_val_retarget ht h hp htc (.trans _ _ _ hc htc) _ e he ha hb
  | application ht f n htc => exact PreResult.application_val_retarget ht h f.typing n.typing htc (.trans _ _ _ hc htc) _ _ e he ha hb

 theorem preEvaluate_retarget_parameter {Γ : List (Expr S)} {M T U : Expr S}
    (t : TypingTree P Γ M T) (h : HasType P Γ M U) (hc : Converts U T)
    (e : Environment (hw := hw) Ω C hno Γ) :
    (preEvaluate Ω C hno t e).parameter = (preEvaluate Ω C hno (t.retarget h hc) e).parameter := by
  apply PreResult.parameter_congr _ _ (e.type_convert_eq t.typing h (.symm _ _ hc))
  exact preEvaluate_retarget_val Ω C hno t h hc e

namespace Environment
variable {Ω C hno} {Γ Δ : List (Expr S)} {σ : Nat → Expr S}
structure Assigned (e : Environment (hw := hw) Ω C hno Γ)
    (f : Environment (hw := hw) Ω C hno Δ) (ts : TypingTree.StoredSubstitution P Γ Δ σ) : Prop where
  images : e.images = Expr.compSub σ f.images
  parameters : ∀ i A (hi : Lookup Γ i A),
    e.parameters i = (preEvaluate Ω C hno (ts i A hi) f).parameter

namespace Assigned
variable {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno Δ}
variable {ts : TypingTree.StoredSubstitution P Γ Δ σ} (he : e.Assigned f ts)
include he
 theorem raw_eq (M : Expr S) : M.subst e.images = (M.subst σ).subst f.images := by
  rw [he.images,Expr.subst_compSub]
 theorem normal_eq (M : Expr S) :
    (M.subst e.images).normalForm = ((M.subst σ).subst f.images).normalForm :=
  congrArg Expr.normalForm (he.raw_eq M)

 theorem cons {D : Expr S} {s : S} (hD : HasType P Δ (D.subst σ) (.sort s))
    (n : Expr S) (hn : Ω.HasType n (D.subst e.images)) (hn' : Ω.HasType n ((D.subst σ).subst f.images))
    (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno (D.subst e.images).normalForm p)
    (hp' : PayloadFits Ω C hno ((D.subst σ).subst f.images).normalForm p) :
    (e.cons hn p hp).Assigned (f.cons hn' p hp') (ts.lift hD) := by
  constructor
  · change Expr.consSub n e.images = Expr.compSub (Expr.liftSub σ) (Expr.consSub n f.images)
    rw [Expr.lift_comp_cons,he.images]
  · intro i A hi
    cases i with
    | zero =>
        have heA : A = D.rename Nat.succ := by cases hi; rfl
        have he' : A.subst (Expr.liftSub σ) = (D.subst σ).rename Nat.succ := by
          rw [heA,Expr.subst_rename,Expr.rename_subst]; rfl
        exact (PreResult.lookup_parameter (he'.symm ▸ HasType.var hD) (.zero _ _)
          (by rw [he']; exact .refl _) (f.cons hn' p hp')).symm
    | succ i =>
        let hex : ∃ A', Lookup Γ i A' ∧ A = A'.rename Nat.succ := by
          cases hi with | succ _ hi => exact ⟨_,hi,rfl⟩
        let tt := (ts i hex.choose hex.choose_spec.1).rename (.cons hD.valid hD)
          Nat.succ (TypingTree.DeclRenaming.weaken _)
        have he' : A.subst (Expr.liftSub σ) = (hex.choose.subst σ).rename Nat.succ := by
          calc
            A.subst (Expr.liftSub σ) = (hex.choose.rename Nat.succ).subst (Expr.liftSub σ) :=
              congrArg (Expr.subst (Expr.liftSub σ)) hex.choose_spec.2
            _ = (hex.choose.subst σ).rename Nat.succ := by
              rw [Expr.subst_rename,Expr.rename_subst]; rfl
        have hr := (preEvaluate_rename Ω C hno (ts i hex.choose hex.choose_spec.1)
          (.cons hD.valid hD) Nat.succ (TypingTree.DeclRenaming.weaken _) f (f.cons hn' p hp')
          (fun _ _ => ⟨rfl,rfl⟩)).1
        exact (he.parameters i hex.choose hex.choose_spec.1).trans
          (hr.trans (preEvaluate_retarget_parameter Ω C hno tt (he'.symm ▸ tt.typing)
            (by rw [he']; exact .refl _) (f.cons hn' p hp')))
end Assigned
end Environment

 theorem preEvaluate_read_outside {Γ : List (Expr S)} {M T : Expr S}
    (t : TypingTree P Γ M T) (e : Environment (hw := hw) Ω C hno Γ)
    (hm : Ω.profile (M.subst e.images).normalForm ∉ C) :
    (preEvaluate Ω C hno t e).read.val = Candidates.Top Ω (M.subst e.images).normalForm := by
  cases t with
  | var ht hd hc => exact by simp only [preEvaluate,PreResult.lookup,PreResult.baseResult,PreResult.baseRead,dite_eq_right hm]
  | sort ht ha hc => rfl
  | product ht d b hr hc => exact by simp only [preEvaluate,PreResult.product,ite_eq_right hm]
  | abstraction ht d b hp hc => exact by simp only [preEvaluate,PreResult.abstraction,PreResult.baseResult,PreResult.baseRead,dite_eq_right hm]
  | application ht f a hc => exact by simp only [preEvaluate,PreResult.application,PreResult.baseResult,PreResult.baseRead,dite_eq_right hm]

 theorem preEvaluate_neutral_read_inactive {Γ : List (Expr S)} {M : Expr S} {s : S}
    (t : TypingTree P Γ M (.sort s)) (e : Environment (hw := hw) Ω C hno Γ)
    (hne : Neutral M) (ha : ¬ ActiveLayer P C (Ω.profile (Expr.sort s |>.subst e.images).normalForm)) :
    (preEvaluate Ω C hno t e).read.val = Candidates.Top Ω (M.subst e.images).normalForm := by
  have hb (v : ActiveLayer P C (Ω.profile (Expr.sort s |>.subst e.images).normalForm) →
      Value (hw := hw) Ω C hno (Expr.sort s |>.subst e.images).normalForm) :
      (PreResult.baseRead t.typing v).val = Candidates.Top Ω (M.subst e.images).normalForm := by
    simp only [PreResult.baseRead,dite_eq_right ha]
    split <;> try rfl
    split <;> rfl
  cases t with
  | var ht hd hc => exact hb _
  | sort ht ha hc => cases hne
  | product ht d b hr hc => cases hne
  | abstraction ht d b hp hc => cases hne
  | application ht f a hc => exact hb _
end

section
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) (C : Set (Set S))

 theorem readGood_outside {Γ : List (Expr S)} {M T : Expr S} (t : TypingTree P Γ M T)
    (ξ : Nat → Expr S) (hm : Ω.profile (M.subst ξ) ∉ C) : ReadGood Ω C t ξ := by
  cases t with
  | var ht hd hc => exact fun h => False.elim (hm h)
  | sort ht ha hc => trivial
  | product ht d b hr hc => exact fun h => False.elim (hm h)
  | abstraction ht d b hp hc => exact fun h => False.elim (hm h)
  | application ht f a hc => exact fun h => False.elim (hm h)

abbrev ProductGood {Γ : List (Expr S)} {D E : Expr S} {a b : S}
    (d : TypingTree P Γ D (.sort a)) (e : TypingTree P (D :: Γ) E (.sort b)) (ξ : Nat → Expr S) : Prop :=
  (Ω.profile (D.subst ξ) ∈ C → ReadGood Ω C d ξ) ∧
    ∀ n, Ω.HasType n (D.subst ξ) → Ω.profile (E.subst (Expr.consSub n ξ)) ∈ C →
      ReadGood Ω C e (Expr.consSub n ξ)

 theorem goodness_subst (hw : SystemWeaklyNormalizing P)
    {Γ : List (Expr S)} {M T : Expr S} (t : TypingTree P Γ M T)
    {Δ : List (Expr S)} (hΔ : ValidContext P Δ) (σ : Nat → Expr S)
    (ts : TypingTree.StoredSubstitution P Γ Δ σ) (ξ : Nat → Expr S)
    (hξ : Ω.TypedSubstitution Δ ξ)
    (hguard : SubstitutionGuard Ω C Γ σ (Expr.compSub σ ξ)) (hg : GoodReplacement Ω C ts ξ) :
    (ActiveLayer P C (Ω.profile (T.subst (Expr.compSub σ ξ))) →
      ValGood Ω C t (Expr.compSub σ ξ) → ValGood Ω C (t.subst hΔ σ ts) ξ) ∧
    (ReadGood Ω C t (Expr.compSub σ ξ) → ReadGood Ω C (t.subst hΔ σ ts) ξ) := by
  induction t generalizing Δ σ ξ with
  | @var Γ i A T ht hd hc =>
      have hcomp := hξ.comp ts.typed
      have hprof := Ω.profile_converts ((ContextTower.HasType.subst ht hcomp).type_weaklyNormalizing hw)
        ((ContextTower.HasType.subst (HasType.lookup ht.valid hd) hcomp).type_weaklyNormalizing hw)
        (hc.subst (Expr.compSub σ ξ))
      have hv : ActiveLayer P C (Ω.profile (T.subst (Expr.compSub σ ξ))) →
          ValGood Ω C ((TypingTree.var ht hd hc).subst hΔ σ ts) ξ := by
        intro ha
        change ValGood Ω C ((ts i A hd).retarget (ht.subst hΔ σ ts.typed) (hc.subst σ)) ξ
        exact (valGood_retarget Ω C _ _ _ _).mpr (hg i A hd (hprof ▸ ha))
      refine ⟨fun ha _ => hv ha,?_⟩
      intro hr
      by_cases hm : Ω.profile ((Expr.var i).subst (Expr.compSub σ ξ)) ∈ C
      · obtain ⟨s,he,hs,_,_⟩ := hr hm
        subst T
        by_cases ha : ActiveLayer P C (Ω.profile (Expr.sort s |>.subst (Expr.compSub σ ξ)))
        · exact (readGood_active_iff Ω C ((TypingTree.var ht hd hc).subst hΔ σ ts)
            (by exact hm) hs (by exact ha)).mpr (hv ha)
        · apply neutral_readGood Ω C _ _ ξ hs (by simpa only [Expr.subst,Ω.profile_sort] using ha)
          exact skipped_read_subst Ω C hw ht (.var i) hcomp hguard hs
            (by simpa only [Expr.subst,Ω.profile_sort] using ha)
      · exact readGood_outside Ω C _ ξ hm
  | sort ht ha hc => exact ⟨fun _ _ => trivial,fun _ => trivial⟩
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      have hD := d.typing.subst hΔ σ ts.typed
      let bs := b.subst (.cons hΔ hD) (Expr.liftSub σ) (ts.lift hD)
      have hbody : ValGood Ω C (.abstraction ht d b hp hc) (Expr.compSub σ ξ) →
          ValGood Ω C ((TypingTree.abstraction ht d b hp hc).subst hΔ σ ts) ξ := by
        intro hb n hn ha
        have hn' : Ω.HasType n (D.subst (Expr.compSub σ ξ)) := by simpa only [Expr.subst_compSub] using hn
        have hi := (ihb (.cons hΔ hD) (Expr.liftSub σ) (ts.lift hD) (Expr.consSub n ξ)
          (hξ.cons hn) (hguard.lift D n) (goodReplacement_lift Ω C ts hg hD n)).1
        apply hi
        · simpa only [Expr.subst_compSub] using ha
        · rw [Expr.lift_comp_cons]
          exact hb n hn' (by simpa only [Expr.subst_compSub,Expr.lift_comp_cons] using ha)
      refine ⟨fun _ => hbody,?_⟩
      intro hr hm
      have hm' : Ω.profile (Expr.lam D m |>.subst (Expr.compSub σ ξ)) ∈ C := by
        simpa only [Expr.subst_compSub] using hm
      obtain ⟨s',he,hs,hv,hn⟩ := hr hm'
      subst T
      exact False.elim ht.lambda_cannot_have_sort_type
  | @application Γ f n D E T ht ft nt hc ihf ihn =>
      have hcomp := hξ.comp ts.typed
      have hv : ActiveLayer P C (Ω.profile (T.subst (Expr.compSub σ ξ))) →
          ValGood Ω C (.application ht ft nt hc) (Expr.compSub σ ξ) →
          ValGood Ω C ((TypingTree.application ht ft nt hc).subst hΔ σ ts) ξ := by
        intro ha hg'
        change (if ActiveLayer P C (Ω.profile (Expr.pi D E |>.subst (Expr.compSub σ ξ))) then
          ValGood Ω C ft (Expr.compSub σ ξ) ∧
            (ActiveLayer P C (Ω.profile (D.subst (Expr.compSub σ ξ))) → ValGood Ω C nt (Expr.compSub σ ξ))
          else Neutral (.app f n)) at hg'
        change (if ActiveLayer P C (Ω.profile ((Expr.pi D E |>.subst σ).subst ξ)) then
          ValGood Ω C (ft.subst hΔ σ ts) ξ ∧
            (ActiveLayer P C (Ω.profile ((D.subst σ).subst ξ)) → ValGood Ω C (nt.subst hΔ σ ts) ξ)
          else Neutral ((Expr.app f n).subst σ))
        simp only [Expr.subst_compSub]
        split <;> rename_i hF
        · rw [ite_eq_left hF] at hg'
          exact ⟨(ihf hΔ σ ts ξ hξ hguard hg).1 hF hg'.1,
            fun hA => (ihn hΔ σ ts ξ hξ hguard hg).1 hA (hg'.2 hA)⟩
        · rw [ite_eq_right hF] at hg'
          exact skipped_application_subst Ω C hw ht ft.typing nt.typing hc hg' hcomp hguard ha hF
      refine ⟨hv,?_⟩
      intro hr hm
      have hm' : Ω.profile (Expr.app f n |>.subst (Expr.compSub σ ξ)) ∈ C := by
        simpa only [Expr.subst_compSub] using hm
      obtain ⟨s,he,hs,hval,hne⟩ := hr hm'
      subst T
      refine ⟨s,rfl,hs,?_,?_⟩
      · intro ha
        apply hv (by exact ha)
        exact hval (by exact ha)
      · intro ha
        have hax : ¬ ActiveLayer P C (AxProfile P s) := by simpa only [Expr.subst,Ω.profile_sort] using ha
        exact skipped_read_subst Ω C hw ht (hne (by exact ha)) hcomp hguard hs hax
  | @product Γ D E a b c T ht d bt hr hc ihd ihb =>
      have hD := d.typing.subst hΔ σ ts.typed
      have hpg : ProductGood Ω C d bt (Expr.compSub σ ξ) →
          ProductGood Ω C (d.subst hΔ σ ts) (bt.subst (.cons hΔ hD) (Expr.liftSub σ) (ts.lift hD)) ξ := by
        intro hh
        constructor
        · intro hm
          exact (ihd hΔ σ ts ξ hξ hguard hg).2 (hh.1 (by simpa only [Expr.subst_compSub] using hm))
        · intro n hn hm
          have hn' : Ω.HasType n (D.subst (Expr.compSub σ ξ)) := by simpa only [Expr.subst_compSub] using hn
          apply (ihb (.cons hΔ hD) (Expr.liftSub σ) (ts.lift hD) (Expr.consSub n ξ)
            (hξ.cons hn) (hguard.lift D n) (goodReplacement_lift Ω C ts hg hD n)).2
          rw [Expr.lift_comp_cons]
          exact hh.2 n hn' (by simpa only [Expr.subst_compSub,Expr.lift_comp_cons] using hm)
      constructor
      · intro _ hv hgate
        apply hpg
        apply hv
        change ({c} : Set S) ∈ C ∧ Ω.profile (((Expr.pi D E).subst σ).subst ξ) ∈ C at hgate
        simpa only [Expr.subst_compSub] using hgate
      · intro hr' hm
        apply hpg
        apply hr'
        change Ω.profile (((Expr.pi D E).subst σ).subst ξ) ∈ C at hm
        simpa only [Expr.subst_compSub] using hm

end

universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

 theorem baseRead_substitution {Γ Δ : List (Expr S)} {M T : Expr S} {σ : Nat → Expr S}
    (ht : HasType P Γ M T) (t' : TypingTree P Δ (M.subst σ) (T.subst σ))
    (e : Environment (hw := hw) Ω C hno Γ) (f : Environment (hw := hw) Ω C hno Δ)
    (he : e.images = Expr.compSub σ f.images)
    (hg : SubstitutionGuard Ω C Γ σ e.images)
    (v : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm) →
      Value (hw := hw) Ω C hno (T.subst e.images).normalForm) (G : Prop)
    (hr : baseGood Ω C M T e.images G)
    (hv : ∀ ha hb, G → (v ha).val = ((preEvaluate Ω C hno t' f).val hb).val) :
    (PreResult.baseRead ht v).val = (preEvaluate Ω C hno t' f).read.val := by
  have hM : (M.subst e.images).normalForm = ((M.subst σ).subst f.images).normalForm := by
    rw [he,Expr.subst_compSub]
  by_cases hm : Ω.profile (M.subst e.images).normalForm ∈ C
  · have hm' : Ω.profile ((M.subst σ).subst f.images).normalForm ∈ C := hM ▸ hm
    obtain ⟨s,hs,hsC,hval,hne⟩ := hr (by simpa only [Ω.profile_normalForm] using hm)
    subst T
    by_cases ha : ActiveLayer P C (Ω.profile (Expr.sort s |>.subst e.images).normalForm)
    · refine Eq.trans (PreResult.baseRead_eq ht v hm hsC ha)
        (Eq.trans ?_ (preEvaluate_read_base Ω C hno t' f hm' hsC ha).symm)
      have hX : e.actualExpression ht = f.actualExpression t'.typing := Subtype.ext hM
      rw [hv ha ha (hval (by simpa only [Ω.profile_normalForm] using ha))]
      exact congrArg (fun X : ActualType Ω =>
        ((RawValue.base Ω C hno ((preEvaluate Ω C hno t' f).val ha).val) X).val) hX
    · have hnew := skipped_read_subst Ω C hw ht
        (hne (by simpa only [Ω.profile_normalForm] using ha)) e.typed hg hsC
        (by simpa only [Expr.subst,Ω.profile_normalForm,Ω.profile_sort] using ha)
      refine Eq.trans ?_ (preEvaluate_neutral_read_inactive Ω C hno t' f hnew ha).symm
      have hex : ∃ s', Expr.sort s = Expr.sort s' ∧ ({s'} : Set S) ∈ C := ⟨s,rfl,hsC⟩
      simp only [PreResult.baseRead,dite_eq_left hm,dite_eq_left hex,dite_eq_right ha]
      exact congrArg (Candidates.Top Ω) hM
  · have hm' : Ω.profile ((M.subst σ).subst f.images).normalForm ∉ C := hM ▸ hm
    rw [preEvaluate_read_outside Ω C hno t' f hm']
    simp only [PreResult.baseRead,dite_eq_right hm]
    exact congrArg (Candidates.Top Ω) hM

 theorem preEvaluate_subst {Γ : List (Expr S)} {M T : Expr S} (t : TypingTree P Γ M T)
    {Δ : List (Expr S)} (hΔ : ValidContext P Δ) (σ : Nat → Expr S)
    (ts : TypingTree.StoredSubstitution P Γ Δ σ)
    (e : Environment (hw := hw) Ω C hno Γ) (f : Environment (hw := hw) Ω C hno Δ)
    (he : e.Assigned f ts) (hg : SubstitutionGuard Ω C Γ σ e.images) :
    (∀ ha hb, ValGood Ω C t e.images →
      ((preEvaluate Ω C hno t e).val ha).val =
        ((preEvaluate Ω C hno (t.subst hΔ σ ts) f).val hb).val) ∧
    (ReadGood Ω C t e.images →
      (preEvaluate Ω C hno t e).read.val = (preEvaluate Ω C hno (t.subst hΔ σ ts) f).read.val) := by
  induction t generalizing Δ σ with
  | @var Γ i A T ht hd hc =>
      have hp : (preEvaluate Ω C hno (.var ht hd hc) e).parameter =
          (preEvaluate Ω C hno ((TypingTree.var ht hd hc).subst hΔ σ ts) f).parameter := by
        exact (PreResult.lookup_parameter ht hd hc e).trans
          ((he.parameters i A hd).trans (preEvaluate_retarget_parameter Ω C hno
            (ts i A hd) (ht.subst hΔ σ ts.typed) (hc.subst σ) f))
      have hv : ∀ ha hb, ValGood Ω C (.var ht hd hc) e.images →
          ((preEvaluate Ω C hno (.var ht hd hc) e).val ha).val =
            ((preEvaluate Ω C hno ((TypingTree.var ht hd hc).subst hΔ σ ts) f).val hb).val :=
        fun ha hb _ => PreResult.val_congr _ _ hp ha hb
      exact ⟨hv,fun hr => baseRead_substitution Ω C hno ht _ e f he.images hg _ _ hr hv⟩
  | sort ht ha hc =>
      exact ⟨fun _ _ _ => distinguished_congr Ω C hno (he.normal_eq _),
        fun _ => congrArg (Candidates.Top Ω) (he.normal_eq _)⟩
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      have hD := d.typing.subst hΔ σ ts.typed
      have hv : ∀ ha hb, ValGood Ω C (.abstraction ht d b hp hc) e.images →
          ((preEvaluate Ω C hno (.abstraction ht d b hp hc) e).val ha).val =
            ((preEvaluate Ω C hno ((TypingTree.abstraction ht d b hp hc).subst hΔ σ ts) f).val hb).val := by
        intro ha hb hgood
        apply PreResult.abstraction_val_congr ht (ht.subst hΔ σ ts.typed) hp
          (hp.subst hΔ σ ts.typed) hc (hc.subst σ) _ _ e f (he.normal_eq _)
        intro n n' hn hn' hnn p hp hp' ha' hb'
        subst n'
        have hae := he.cons hD n hn hn' p hp hp'
        have hgu : SubstitutionGuard Ω C (D :: Γ) (Expr.liftSub σ) (e.cons hn p hp).images := by
          rw [hae.images]
          apply SubstitutionGuard.lift
          rwa [← he.images]
        exact (ihb (.cons hΔ hD) (Expr.liftSub σ) (ts.lift hD)
          (e.cons hn p hp) (f.cons hn' p hp') hae hgu).1 ha' hb'
          (hgood n hn (by
            change ActiveLayer P C (Ω.profile (E.subst (Expr.consSub n e.images)).normalForm) at ha'
            simpa only [Ω.profile_normalForm] using ha'))
      exact ⟨hv,fun hr => baseRead_substitution Ω C hno ht _ e f he.images hg _ _ hr hv⟩
  | @application Γ g n D E T ht gt nt hc ihg ihn =>
      have hv : ∀ ha hb, ValGood Ω C (.application ht gt nt hc) e.images →
          ((preEvaluate Ω C hno (.application ht gt nt hc) e).val ha).val =
            ((preEvaluate Ω C hno ((TypingTree.application ht gt nt hc).subst hΔ σ ts) f).val hb).val := by
        intro ha hb hgood
        by_cases hF : ActiveLayer P C (Ω.profile (Expr.pi D E |>.subst e.images))
        · change (if ActiveLayer P C (Ω.profile (Expr.pi D E |>.subst e.images)) then
            ValGood Ω C gt e.images ∧ (ActiveLayer P C (Ω.profile (D.subst e.images)) → ValGood Ω C nt e.images)
            else Neutral (.app g n)) at hgood
          rw [ite_eq_left hF] at hgood
          apply PreResult.application_val_congr ht (ht.subst hΔ σ ts.typed) gt.typing
            (gt.typing.subst hΔ σ ts.typed) nt.typing (nt.typing.subst hΔ σ ts.typed)
            hc _ _ _ _ _ e f (he.normal_eq _) (he.normal_eq _) (he.normal_eq _)
          · exact fun hA hB => (ihg hΔ σ ts e f he hg).1 hA hB hgood.1
          · apply PreResult.parameter_congr _ _ (he.normal_eq _)
            intro hA hB
            exact (ihn hΔ σ ts e f he hg).1 hA hB (hgood.2 (by simpa only [Ω.profile_normalForm] using hA))
        · have hF' : ¬ ActiveLayer P C (Ω.profile (((Expr.pi D E).subst σ).subst f.images).normalForm) := by
            rw [← he.normal_eq _ ,Ω.profile_normalForm]
            exact hF
          have hF0 : ¬ ActiveLayer P C (Ω.profile (Expr.pi D E |>.subst e.images).normalForm) := by
            simpa only [Ω.profile_normalForm] using hF
          change ((PreResult.application ht gt.typing nt.typing hc _ _ e).val ha).val =
            ((PreResult.application (ht.subst hΔ σ ts.typed) (gt.typing.subst hΔ σ ts.typed)
              (nt.typing.subst hΔ σ ts.typed) _ _ _ f).val hb).val
          change ¬ ActiveLayer P C (Ω.profile ((Expr.pi (D.subst σ) (E.subst (Expr.liftSub σ))).subst f.images).normalForm) at hF'
          simp only [PreResult.application,PreResult.baseResult,PreResult.applicationValue,dite_eq_right hF0,dite_eq_right hF']
          exact distinguished_congr Ω C hno (he.normal_eq T)
      exact ⟨hv,fun hr => baseRead_substitution Ω C hno ht _ e f he.images hg _ _ hr hv⟩
  | @product Γ D E a b c T ht d bt hr hc ihd ihb =>
      have hD := d.typing.subst hΔ σ ts.typed
      have hB := bt.typing.subst (.cons hΔ hD) (Expr.liftSub σ) (ts.lift hD).typed
      have hpc : ProductGood Ω C d bt e.images →
          (PreResult.productCandidate d.typing bt.typing hr (preEvaluate Ω C hno d)
            (preEvaluate Ω C hno bt) e).val =
          (PreResult.productCandidate hD hB hr (preEvaluate Ω C hno (d.subst hΔ σ ts))
            (preEvaluate Ω C hno (bt.subst (.cons hΔ hD) (Expr.liftSub σ) (ts.lift hD))) f).val := by
        intro hgood
        have hDE := Expr.pi.inj (he.raw_eq (.pi D E))
        apply PreResult.productCandidate_congr d.typing bt.typing hr hD hB hr _ _ _ _ e f
          (congrArg Expr.normalForm hDE.1) (congrArg Expr.normalForm hDE.2)
        · intro hm
          exact (ihd hΔ σ ts e f he hg).2 (hgood.1 (by simpa only [Ω.profile_normalForm] using hm))
        · intro n hn hn' p hp hp' hm
          have hae := he.cons hD n hn hn' p hp hp'
          have hgu : SubstitutionGuard Ω C (D :: Γ) (Expr.liftSub σ) (e.cons hn p hp).images := by
            rw [hae.images]
            apply SubstitutionGuard.lift
            rwa [← he.images]
          exact (ihb (.cons hΔ hD) (Expr.liftSub σ) (ts.lift hD)
            (e.cons hn p hp) (f.cons hn' p hp') hae hgu).2
            (hgood.2 n hn (by
              change Ω.profile (E.subst (Expr.consSub n e.images)).normalForm ∈ C at hm
              simpa only [Ω.profile_normalForm] using hm))
      constructor
      · intro ha hb hv
        by_cases hs : ({c} : Set S) ∈ C
        · apply PreResult.product_val_congr ht (ht.subst hΔ σ ts.typed) d.typing bt.typing hr
            hD hB hr hc (hc.subst σ) _ _ _ _ e f (he.normal_eq _) (he.normal_eq _) Iff.rfl
          intro hm
          exact hpc (hv ⟨hs,by simpa only [Ω.profile_normalForm] using hm⟩)
        · have hgate : ¬ (({c} : Set S) ∈ C ∧ Ω.profile (Expr.pi D E |>.subst e.images).normalForm ∈ C) := fun h => hs h.1
          have hgate' : ¬ (({c} : Set S) ∈ C ∧ Ω.profile (((Expr.pi D E).subst σ).subst f.images).normalForm ∈ C) := fun h => hs h.1
          change ((PreResult.product ht d.typing bt.typing hr hc _ _ e).val ha).val =
            ((PreResult.product (ht.subst hΔ σ ts.typed) hD hB hr (hc.subst σ) _ _ f).val hb).val
          change ¬ (({c} : Set S) ∈ C ∧ Ω.profile ((Expr.pi (D.subst σ) (E.subst (Expr.liftSub σ))).subst f.images).normalForm ∈ C) at hgate'
          simp only [PreResult.product,dite_eq_right hgate,dite_eq_right hgate']
          exact distinguished_congr Ω C hno (he.normal_eq T)
      · intro hgood
        apply PreResult.product_read_congr ht (ht.subst hΔ σ ts.typed) d.typing bt.typing hr
          hD hB hr hc (hc.subst σ) _ _ _ _ e f (he.normal_eq _)
        intro hm
        exact hpc (hgood (by simpa only [Ω.profile_normalForm] using hm))
end PureTypeSystem.ObservationValues

namespace PureTypeSystem
universe u
namespace Expr
variable {S : Type u}
@[simp] theorem comp_single (n : Expr S) (ξ : Nat → Expr S) :
    compSub (single n) ξ = consSub (n.subst ξ) ξ := by
  funext i; cases i <;> rfl
end Expr
namespace TypingTree.StoredSubstitution
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {n D : Expr S}
noncomputable def single (t : TypingTree P Γ n D) :
    StoredSubstitution P (D :: Γ) Γ (Expr.single n) :=
  fun i => match i with
  | 0 => fun A hi => by
      have he : A = D.rename Nat.succ := by cases hi; rfl
      have he' : A.subst (Expr.single n) = D := by rw [he,Expr.subst_lift_single]
      exact t.retarget (he'.symm ▸ t.typing) (by rw [he']; exact .refl _)
  | i+1 => fun A hi => by
      let hex : ∃ B, Lookup Γ i B ∧ A = B.rename Nat.succ := by
        cases hi with | succ _ hi => exact ⟨_,hi,rfl⟩
      have he : A.subst (Expr.single n) = hex.choose := by
        exact (congrArg (Expr.subst (Expr.single n)) hex.choose_spec.2).trans
          (Expr.subst_lift_single hex.choose n)
      exact .var (he.symm ▸ HasType.lookup t.typing.valid hex.choose_spec.1)
        hex.choose_spec.1 (by rw [he]; exact .refl _)
end TypingTree.StoredSubstitution
namespace ObservationValues
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

omit [Fintype S] in
 theorem goodness_recontext {Γ : List (Expr S)} {M T : Expr S} (t : TypingTree P Γ M T)
    {Δ : List (Expr S)} (h : ContextEquivalent P Γ Δ) (ξ : Nat → Expr S) :
    goodness Ω C (t.recontext h) ξ = goodness Ω C t ξ := by
  induction t generalizing Δ ξ with
  | var ht hd hc => rfl
  | sort ht ha hc => rfl
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      have hv : (∀ n, Ω.HasType n (D.subst ξ) → ActiveLayer P C (Ω.profile (E.subst (Expr.consSub n ξ))) →
          (goodness Ω C (b.recontext (h.cons d.typing)) (Expr.consSub n ξ)).1) =
        (∀ n, Ω.HasType n (D.subst ξ) → ActiveLayer P C (Ω.profile (E.subst (Expr.consSub n ξ))) →
          (goodness Ω C b (Expr.consSub n ξ)).1) := by simp only [ihb]
      exact congrArg (fun G => (G,baseGood Ω C (.lam D m) T ξ G)) hv
  | @application Γ f n D E T ht ft nt hc ihf ihn =>
      have hv : (if ActiveLayer P C (Ω.profile ((Expr.pi D E).subst ξ)) then
          (goodness Ω C (ft.recontext h) ξ).1 ∧
            (ActiveLayer P C (Ω.profile (D.subst ξ)) → (goodness Ω C (nt.recontext h) ξ).1)
          else Neutral (.app f n)) =
        (if ActiveLayer P C (Ω.profile ((Expr.pi D E).subst ξ)) then
          (goodness Ω C ft ξ).1 ∧
            (ActiveLayer P C (Ω.profile (D.subst ξ)) → (goodness Ω C nt ξ).1)
          else Neutral (.app f n)) := by simp only [ihf,ihn]
      exact congrArg (fun G => (G,baseGood Ω C (.app f n) T ξ G)) hv
  | @product Γ D E a b c T ht d b hr hc ihd ihb =>
      have hg : ((Ω.profile (D.subst ξ) ∈ C → (goodness Ω C (d.recontext h) ξ).2) ∧
          ∀ n, Ω.HasType n (D.subst ξ) → Ω.profile (E.subst (Expr.consSub n ξ)) ∈ C →
            (goodness Ω C (b.recontext (h.cons d.typing)) (Expr.consSub n ξ)).2) =
        ((Ω.profile (D.subst ξ) ∈ C → (goodness Ω C d ξ).2) ∧
          ∀ n, Ω.HasType n (D.subst ξ) → Ω.profile (E.subst (Expr.consSub n ξ)) ∈ C →
            (goodness Ω C b (Expr.consSub n ξ)).2) := by simp only [ihd,ihb]
      exact congrArg (fun G => ((({c} : Set S) ∈ C ∧ Ω.profile ((Expr.pi D E).subst ξ) ∈ C → G),
        (Ω.profile ((Expr.pi D E).subst ξ) ∈ C → G))) hg

omit [Fintype S] in
 theorem single_guard {Γ : List (Expr S)} {n D : Expr S} (ξ : Nat → Expr S)
    (ha : Ω.profile (D.subst ξ) ∈ ObservationLayers P C → ActiveLayer P C (Ω.profile (D.subst ξ))) :
    SubstitutionGuard Ω C (D :: Γ) (Expr.single n) (Expr.consSub (n.subst ξ) ξ) := by
  intro i A hi hne hH
  cases hi with
  | zero => simpa only [Expr.raise_subst_cons] using ha (by simpa only [Expr.raise_subst_cons] using hH)
  | succ D hi => exact False.elim (hne (.var _))

omit [Fintype S] in
 theorem single_goodReplacement {Γ : List (Expr S)} {n D : Expr S}
    (t : TypingTree P Γ n D) (ξ : Nat → Expr S)
    (hg : ActiveLayer P C (Ω.profile (D.subst ξ)) → ValGood Ω C t ξ) :
    GoodReplacement Ω C (TypingTree.StoredSubstitution.single t) ξ := by
  intro i A hi ha
  cases i with
  | zero =>
      have he : A = D.rename Nat.succ := by cases hi; rfl
      have he' : A.subst (Expr.single n) = D := by rw [he,Expr.subst_lift_single]
      exact (valGood_retarget Ω C t (he'.symm ▸ t.typing) (by rw [he']; exact .refl _) ξ).mpr (hg (by
        simpa only [Expr.comp_single,he,Expr.raise_subst_cons] using ha))
  | succ i => exact True.intro

 theorem single_assigned {Γ : List (Expr S)} {n D : Expr S} (t : TypingTree P Γ n D)
    (e : Environment (hw := hw) Ω C hno Γ) :
    (e.cons (ContextTower.HasType.subst t.typing e.typed) (preEvaluate Ω C hno t e).parameter
      (preEvaluate Ω C hno t e).parameter_fits).Assigned e (TypingTree.StoredSubstitution.single t) := by
  constructor
  · exact (Expr.comp_single n e.images).symm
  · intro i A hi
    cases i with
    | zero =>
        have he : A = D.rename Nat.succ := by cases hi; rfl
        have he' : A.subst (Expr.single n) = D := by rw [he,Expr.subst_lift_single]
        exact preEvaluate_retarget_parameter Ω C hno t (he'.symm ▸ t.typing)
          (by rw [he']; exact .refl _) e
    | succ i =>
        let hex : ∃ B, Lookup Γ i B ∧ A = B.rename Nat.succ := by
          cases hi with | succ _ hi => exact ⟨_,hi,rfl⟩
        have he : A.subst (Expr.single n) = hex.choose := by
          exact (congrArg (Expr.subst (Expr.single n)) hex.choose_spec.2).trans
            (Expr.subst_lift_single hex.choose n)
        exact (PreResult.lookup_parameter (he.symm ▸ HasType.lookup t.typing.valid hex.choose_spec.1)
          hex.choose_spec.1 (by rw [he]; exact .refl _) e).symm
end ObservationValues
end PureTypeSystem

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_ObservationReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.ObservationValues
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

namespace Value
variable {Ω C hno}
@[simp] theorem asPlus_plus {T : Expr S} (hT : FreeLayer P C (Ω.profile T) false)
    (p : Plus (hw := hw) Ω C hno) : asPlus hT ⟨.plus p,hT⟩ = p :=
  RawValue.plus.inj (asPlus_spec hT ⟨.plus p,hT⟩).symm
@[simp] theorem asMinus_minus {T : Expr S} (hT : FreeLayer P C (Ω.profile T) true)
    (p : Minus (hw := hw) Ω C hno) : asMinus hT ⟨.minus p,hT⟩ = p :=
  RawValue.minus.inj (asMinus_spec hT ⟨.minus p,hT⟩).symm
end Value

theorem plain_beta (T : ActiveType Ω C) (hT : PlainLayer P C (Ω.profile T.type))
    (act : LambdaAction (hw := hw) Ω C hno T) (a : FrameKey Ω C T)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    plainApply Ω C hno T hT (plainLambda Ω C hno T hT act) a p hp = act a p hp := by
  simp only [plainApply,plainLambda,Value.asPlain_plain,Equiv.apply_symm_apply]
  simp only [ActualPlainKey.payload_parameters]
  exact Value.plain_asPlain (ActualPlain.Key.target hw (a.plainKey hT)) (act a p hp)

theorem exitValue_tag (T : ActiveType Ω C) (hT : PlainLayer P C (Ω.profile T.type))
    (v : Value (hw := hw) Ω C hno T.type) :
    exitValue Ω C hno T (some (tagPlain Ω C hno T hT v)) = v := by
  simp only [exitValue,tagPlain_spec,project_valid]

theorem lambdaExit_parameter {X : Type u}
    (decode : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) X →
      Option (RawValue (hw := hw) Ω C hno))
    (T : ActiveType Ω C) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : FrameKey Ω C T) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p)
    (q : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) X) (hq : decode q = p)
    (ht : PlainLayer P C (Ω.profile (a.target hw).type)) :
    lambdaExit Ω C hno decode T act (a.argument,q) =
      some (tagPlain Ω C hno (a.target hw) ht (act a p hp)) := by
  have hg : Gate Ω C hno T a.argument (decode q) true :=
    ⟨a,rfl,hq.symm ▸ hp,⟨fun _ => rfl,fun _ => ht⟩⟩
  simp only [lambdaExit,dite_eq_left hg]
  subst p
  have H : ∀ (k : FrameKey Ω C T), k = a →
      ∀ (hpk : PayloadFits Ω C hno k.domain (decode q))
        (htk : PlainLayer P C (Ω.profile (k.target hw).type)),
      some (tagPlain Ω C hno (k.target hw) htk (act k (decode q) hpk)) =
        some (tagPlain Ω C hno (a.target hw) ht (act a (decode q) hp)) := by
    intro k hk
    subst k
    intro hpk htk
    rfl
  exact H hg.frame (Gate.unique hg a rfl) hg.payload hg.plain

theorem plusContinue_gate (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.profile T.type) false) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : FrameKey Ω C T) (q : PlusFrame (hw := hw) Ω C hno) (hqa : q.1 = a.argument)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p)
    (hq : plusPayload Ω C hno q.2 = p)
    (ht : ¬ PlainLayer P C (Ω.profile (a.target hw).type)) :
    plusContinue Ω C hno T hT act q = Value.asPlus (a.free_target hT ht) (act a p hp) := by
  rcases q with ⟨n,v⟩
  dsimp only at hqa hq
  subst n
  subst p
  have hg : Gate Ω C hno T a.argument (plusPayload Ω C hno v) false :=
    ⟨a,rfl,hp,⟨fun h => False.elim (ht h),fun h => Bool.noConfusion h⟩⟩
  simp only [plusContinue,dite_eq_left hg]
  have H : ∀ (k : FrameKey Ω C T), k = a →
      ∀ (hpk : PayloadFits Ω C hno k.domain (plusPayload Ω C hno v))
        (htk : ¬ PlainLayer P C (Ω.profile (k.target hw).type)),
      Value.asPlus (k.free_target hT htk) (act k (plusPayload Ω C hno v) hpk) =
        Value.asPlus (a.free_target hT ht) (act a (plusPayload Ω C hno v) hp) := by
    intro k hk
    subst k
    intro hpk htk
    rfl
  exact H hg.frame (Gate.unique hg a rfl) hg.payload hg.not_plain

 theorem plusContinue_parameter (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.profile T.type) false) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : FrameKey Ω C T) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p)
    (ht : ¬ PlainLayer P C (Ω.profile (a.target hw).type)) :
    plusContinue Ω C hno T hT act (a.argument,a.plusParameter hT p hp) =
      Value.asPlus (a.free_target hT ht) (act a p hp) :=
  plusContinue_gate Ω C hno T hT act a _ rfl p hp (a.plusPayload_parameter hT p hp) ht

theorem minusContinue_gate (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.profile T.type) true) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : FrameKey Ω C T) (q : MinusFrame (hw := hw) Ω C hno) (hqa : q.1 = a.argument)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p)
    (hq : minusPayload Ω C hno q.2 = p)
    (ht : ¬ PlainLayer P C (Ω.profile (a.target hw).type)) :
    minusContinue Ω C hno T hT act q = Value.asMinus (a.free_target hT ht) (act a p hp) := by
  rcases q with ⟨n,v⟩
  dsimp only at hqa hq
  subst n
  subst p
  have hg : Gate Ω C hno T a.argument (minusPayload Ω C hno v) false :=
    ⟨a,rfl,hp,⟨fun h => False.elim (ht h),fun h => Bool.noConfusion h⟩⟩
  simp only [minusContinue,dite_eq_left hg]
  have H : ∀ (k : FrameKey Ω C T), k = a →
      ∀ (hpk : PayloadFits Ω C hno k.domain (minusPayload Ω C hno v))
        (htk : ¬ PlainLayer P C (Ω.profile (k.target hw).type)),
      Value.asMinus (k.free_target hT htk) (act k (minusPayload Ω C hno v) hpk) =
        Value.asMinus (a.free_target hT ht) (act a (minusPayload Ω C hno v) hp) := by
    intro k hk
    subst k
    intro hpk htk
    rfl
  exact H hg.frame (Gate.unique hg a rfl) hg.payload hg.not_plain

 theorem minusContinue_parameter (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.profile T.type) true) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : FrameKey Ω C T) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p)
    (ht : ¬ PlainLayer P C (Ω.profile (a.target hw).type)) :
    minusContinue Ω C hno T hT act (a.argument,a.minusParameter hT p hp) =
      Value.asMinus (a.free_target hT ht) (act a p hp) :=
  minusContinue_gate Ω C hno T hT act a _ rfl p hp (a.minusPayload_parameter hT p hp) ht

theorem plusLambda_slice (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.profile T.type) false) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : PlusFrame (hw := hw) Ω C hno) :
    (plusLambda Ω C hno T hT act).slice a = plusContinue Ω C hno T hT act a := by
  rfl

theorem minusLambda_slice (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.profile T.type) true) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : MinusFrame (hw := hw) Ω C hno) :
    (minusLambdaBehavior Ω C hno T hT act).slice a =
      FreeObservations.behavior _ _ _ _ (minusContinue Ω C hno T hT act a) := by
  rfl

/-- The raw lambda equation. The sole representability premise is supplied
below from the proved uniform finite-bound lemma for an actual body tree. -/
theorem lambda_beta (T : ActiveType Ω C) (act : LambdaAction (hw := hw) Ω C hno T)
    (hr : ∀ hT : FreeLayer P C (Ω.profile T.type) true,
      ∃ x, FreeObservations.behavior _ _ _ _ x = minusLambdaBehavior Ω C hno T hT act)
    (a : FrameKey Ω C T) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p) :
    applyValue Ω C hno T (lambdaValue Ω C hno T act) a p hp = act a p hp := by
  by_cases hT : PlainLayer P C (Ω.profile T.type)
  · simp only [applyValue,lambdaValue,dite_eq_left hT]
    exact plain_beta Ω C hno T hT act a p hp
  · by_cases hF : FreeLayer P C (Ω.profile T.type) false
    · by_cases hA : PlainLayer P C (Ω.profile (a.target hw).type)
      · simp only [applyValue,lambdaValue,dite_eq_right hT,dite_eq_left hF,dite_eq_left hA,Value.asPlus_plus,plusLambda]
        rw [lambdaExit_parameter Ω C hno _ T act a p hp _ (a.plusPayload_parameter hF p hp) hA]
        exact exitValue_tag Ω C hno _ hA _
      · simp only [applyValue,lambdaValue,dite_eq_right hT,dite_eq_left hF,dite_eq_right hA,Value.asPlus_plus]
        apply Subtype.ext
        change RawValue.plus ((plusLambda Ω C hno T hF act).slice
          (a.argument,a.plusParameter hF p hp)) = _
        rw [plusLambda_slice,plusContinue_parameter Ω C hno T hF act a p hp hA]
        exact (Value.asPlus_spec (a.free_target hF hA) (act a p hp)).symm
    · have hM : FreeLayer P C (Ω.profile T.type) true := by
        rcases T.active.classify with h | h | h
        · exact False.elim (hT h)
        · exact False.elim (hF h)
        · exact h
      have hb := packMinus_spec Ω C hno (minusLambdaBehavior Ω C hno T hM act) (hr hM)
      by_cases hA : PlainLayer P C (Ω.profile (a.target hw).type)
      · simp only [applyValue,lambdaValue,dite_eq_right hT,dite_eq_right hF,dite_eq_left hA,Value.asMinus_minus]
        rw [hb]
        change exitValue Ω C hno (a.target hw)
          (lambdaExit Ω C hno (minusPayload Ω C hno) T act (a.argument,a.minusParameter hM p hp)) = _
        rw [lambdaExit_parameter Ω C hno _ T act a p hp _ (a.minusPayload_parameter hM p hp) hA]
        exact exitValue_tag Ω C hno _ hA _
      · simp only [applyValue,lambdaValue,dite_eq_right hT,dite_eq_right hF,dite_eq_right hA,Value.asMinus_minus]
        apply Subtype.ext
        change RawValue.minus (FreeObservations.minusSlice
          (packMinus Ω C hno (minusLambdaBehavior Ω C hno T hM act))
          (a.argument,a.minusParameter hM p hp)) = _
        rw [Value.asMinus_spec (a.free_target hM hA) (act a p hp)]
        apply congrArg RawValue.minus
        apply FreeObservations.behavior_injective (topBase Ω) none
        rw [FreeObservations.behavior_minusSlice,hb,minusLambda_slice,
          minusContinue_parameter Ω C hno T hM act a p hp hA]

namespace PreResult
variable {Ω C hno} {Γ : List (Expr S)} {T : Expr S}
theorem abstraction_beta {D m E : Expr S} {s : S} (h : HasType P Γ (.lam D m) T)
    (hp : HasType P Γ (.pi D E) (.sort s)) (hc : Converts T (.pi D E))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) m E) {B : Nat → Nat}
    (hub : Uniform Ω C hno eb B) (e : Environment (hw := hw) Ω C hno Γ)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (a : FrameKey Ω C (e.activeType h ha)) (p : Option (RawValue (hw := hw) Ω C hno))
    (hpp : PayloadFits Ω C hno a.domain p) :
    applyValue Ω C hno (e.activeType h ha) ((abstraction h hp hc eb e).val ha) a p hpp =
      abstractionAction h hp hc eb e ha a p hpp := by
  apply lambda_beta
  intro hT
  obtain ⟨k,hk⟩ := e.exists_bound
  obtain ⟨v,_,hv⟩ := minusLambda_representable Ω C hno hT (by have := hub.growth k; omega)
    (abstractionAction_bounded h hp hc eb hub k e hk ha)
    (fun a p p' hp' hp'' hbp hbp' hpp =>
      abstractionAction_level h hp hc eb hub k e e hk hk (e.level_refl _) ha ha a a rfl
        p p' hp' hp'' hbp hbp' hpp)
  exact ⟨v,hv⟩

theorem application_frame {f n A B : Expr S} (h : HasType P Γ (.app f n) T)
    (hf : HasType P Γ f (.pi A B)) (hn : HasType P Γ n A) (hc : Converts T (B.instantiate n))
    (ef : Evaluator (hw := hw) Ω C hno Γ f (.pi A B))
    (en : Evaluator (hw := hw) Ω C hno Γ n A)
    (e : Environment (hw := hw) Ω C hno Γ)
    (hF : ActiveLayer P C (Ω.profile ((Expr.pi A B).subst e.images).normalForm))
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)) :
    ∃ (k : FrameKey Ω C (e.activeType hf hF))
      (hp : PayloadFits Ω C hno k.domain (en e).parameter),
      k.argument = (n.subst e.images).normalForm ∧ k.domain = (A.subst e.images).normalForm ∧
      ((application h hf hn hc ef en e).val ha).val =
        (applyValue Ω C hno _ ((ef e).val hF) k (en e).parameter hp).val := by
  unfold application baseResult applicationValue
  simp only [dite_eq_left hF]
  exact ⟨_,(en e).parameter_fits,rfl,rfl,rfl⟩

theorem abstractionAction_raw {D m E : Expr S} {s : S}
    (h : HasType P Γ (.lam D m) T) (hp : HasType P Γ (.pi D E) (.sort s))
    (hc : Converts T (.pi D E)) (b : TypingTree P (D :: Γ) m E)
    (hC : IsComponent (PrimaryEdge P) C)
    (e : Environment (hw := hw) Ω C hno Γ)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (k : FrameKey Ω C (e.activeType h ha))
    (p : Option (RawValue (hw := hw) Ω C hno)) (hpp : PayloadFits Ω C hno k.domain p)
    (n : Expr S) (hn : Ω.HasType n (D.subst e.images))
    (hp' : PayloadFits Ω C hno (D.subst e.images).normalForm p)
    (hkn : Converts k.argument n)
    (ha' : ActiveLayer P C (Ω.profile (E.subst (Expr.consSub n e.images)).normalForm)) :
    (abstractionAction h hp hc (preEvaluate Ω C hno b) e ha k p hpp).val =
      ((preEvaluate Ω C hno b (e.cons hn p hp')).val ha').val := by
  unfold abstractionAction
  apply val_congr
  apply (preEvaluate_compatible Ω C hno hC b _ _ ?_).1
  constructor
  · intro i hi
    cases i with
    | zero => exact hkn
    | succ i => exact .refl _
  · intro i hi
    cases i <;> rfl
end PreResult

 theorem application_abstraction_beta {Γ : List (Expr S)} {D m E A B n T : Expr S} {a s : S}
    (ht : HasType P Γ (.app (.lam D m) n) T)
    (hf : HasType P Γ (.lam D m) (.pi A B))
    (d : TypingTree P Γ D (.sort a)) (b : TypingTree P (D :: Γ) m E)
    (hp : HasType P Γ (.pi D E) (.sort s)) (hcF : Converts (.pi A B) (.pi D E))
    (nt : TypingTree P Γ n A) (hc : Converts T (B.instantiate n))
    (hC : IsComponent (PrimaryEdge P) C) (e : Environment (hw := hw) Ω C hno Γ)
    (hF : ActiveLayer P C (Ω.profile ((Expr.pi A B).subst e.images).normalForm))
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)) :
    ∃ (hnD : Ω.HasType (n.subst e.images) (D.subst e.images))
      (hpp : PayloadFits Ω C hno (D.subst e.images).normalForm (preEvaluate Ω C hno nt e).parameter)
      (hb : ActiveLayer P C (Ω.profile (E.subst (Expr.consSub (n.subst e.images) e.images)).normalForm)),
      (Ω.profile (D.subst e.images) ∈ ObservationLayers P C → ActiveLayer P C (Ω.profile (D.subst e.images))) ∧
      ((preEvaluate Ω C hno (.application ht (.abstraction hf d b hp hcF) nt hc) e).val ha).val =
        ((preEvaluate Ω C hno b (e.cons hnD (preEvaluate Ω C hno nt e).parameter hpp)).val hb).val := by
  obtain ⟨k,hpk,hkn,hkD,hval⟩ := PreResult.application_frame ht hf nt.typing hc
    (preEvaluate Ω C hno (.abstraction hf d b hp hcF)) (preEvaluate Ω C hno nt) e hF ha
  have hnD : HasType P Γ n D := .conversion nt.typing d.typing hcF.product_compatibility.1
  have hAD := e.type_convert_eq nt.typing hnD hcF.product_compatibility.1
  have hpp : PayloadFits Ω C hno (D.subst e.images).normalForm (preEvaluate Ω C hno nt e).parameter :=
    hAD ▸ (preEvaluate Ω C hno nt e).parameter_fits
  have hbT : Converts T (E.instantiate n) := .trans _ _ _ hc (hcF.product_compatibility.2.subst (Expr.single n))
  have heT := e.type_convert_eq ht (b.typing.instantiate hnD) hbT
  have heT' : (T.subst e.images).normalForm =
      (E.subst (Expr.consSub (n.subst e.images) e.images)).normalForm := by
    simpa only [Expr.instantiate,Expr.subst_compSub,Expr.comp_single] using heT
  have hb : ActiveLayer P C (Ω.profile (E.subst (Expr.consSub (n.subst e.images) e.images)).normalForm) := heT' ▸ ha
  refine ⟨ContextTower.HasType.subst hnD e.typed,hpp,hb,?_,?_⟩
  · intro hH
    have heD : Ω.profile k.domain = Ω.profile (D.subst e.images) := by rw [hkD,hAD,Ω.profile_normalForm]
    rw [← heD]
    exact k.domain_active hw (heD.symm ▸ hH)
  · obtain ⟨F,hB⟩ := preEvaluate_uniform Ω C hno hC b
    refine hval.trans ?_
    rw [show ((preEvaluate Ω C hno (.abstraction hf d b hp hcF) e).val hF) =
      (PreResult.abstraction hf hp hcF (preEvaluate Ω C hno b) e).val hF from rfl,
      PreResult.abstraction_beta hf hp hcF _ hB e hF k _ hpk]
    apply PreResult.abstractionAction_raw hf hp hcF b hC e hF k _ hpk
      (n.subst e.images) (ContextTower.HasType.subst hnD e.typed) hpp _ hb
    rw [hkn]
    exact .symm _ _ (Expr.normalForm_spec ((ContextTower.HasType.subst nt.typing e.typed).weaklyNormalizing hw)).1.converts

/-- Exact tree transport at a fixed root expectation. Only good observations
are equated; raw environments and values are otherwise unrestricted. -/
structure GoodTransport {Γ : List (Expr S)} {M N T : Expr S}
    (t : TypingTree P Γ M T) (t' : TypingTree P Γ N T) : Prop where
  val : ∀ (e : Environment (hw := hw) Ω C hno Γ)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)),
    ValGood Ω C t e.images → ValGood Ω C t' e.images ∧
      ((preEvaluate Ω C hno t e).val ha).val = ((preEvaluate Ω C hno t' e).val ha).val
  read : ∀ (e : Environment (hw := hw) Ω C hno Γ), ReadGood Ω C t e.images →
    ReadGood Ω C t' e.images ∧ (preEvaluate Ω C hno t e).read.val = (preEvaluate Ω C hno t' e).read.val

 theorem baseRead_transport {Γ : List (Expr S)} {M N T : Expr S}
    (ht : HasType P Γ M T) (t' : TypingTree P Γ N T)
    (e : Environment (hw := hw) Ω C hno Γ)
    (hMN : (M.subst e.images).normalForm = (N.subst e.images).normalForm)
    (hne : Neutral M → Neutral N)
    (v : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm) →
      Value (hw := hw) Ω C hno (T.subst e.images).normalForm) (G : Prop)
    (hr : baseGood Ω C M T e.images G)
    (hv : ∀ ha, G → ValGood Ω C t' e.images ∧ (v ha).val = ((preEvaluate Ω C hno t' e).val ha).val) :
    ReadGood Ω C t' e.images ∧ (PreResult.baseRead ht v).val = (preEvaluate Ω C hno t' e).read.val := by
  by_cases hm : Ω.profile (M.subst e.images).normalForm ∈ C
  · have hm' : Ω.profile (N.subst e.images).normalForm ∈ C := hMN ▸ hm
    obtain ⟨s,hs,hsC,hval,hn⟩ := hr (by simpa only [Ω.profile_normalForm] using hm)
    subst T
    by_cases ha : ActiveLayer P C (Ω.profile (Expr.sort s |>.subst e.images).normalForm)
    · have hvg := hv ha (hval (by simpa only [Ω.profile_normalForm] using ha))
      refine ⟨(readGood_active_iff Ω C t' (by simpa only [Ω.profile_normalForm] using hm') hsC
        (by simpa only [Ω.profile_normalForm] using ha)).mpr hvg.1,?_⟩
      refine Eq.trans (PreResult.baseRead_eq ht v hm hsC ha)
        (Eq.trans ?_ (preEvaluate_read_base Ω C hno t' e hm' hsC ha).symm)
      rw [hvg.2]
      exact congrArg (fun X : ActualType Ω =>
        ((RawValue.base Ω C hno ((preEvaluate Ω C hno t' e).val ha).val) X).val) (Subtype.ext hMN)
    · have hn' := hne (hn (by simpa only [Ω.profile_normalForm] using ha))
      refine ⟨neutral_readGood Ω C t' hn' e.images hsC (by simpa only [Expr.subst,Ω.profile_sort,Ω.profile_normalForm] using ha),?_⟩
      have hex : ∃ s', Expr.sort s = Expr.sort s' ∧ ({s'} : Set S) ∈ C := ⟨s,rfl,hsC⟩
      rw [preEvaluate_neutral_read_inactive Ω C hno t' e hn' ha]
      simp only [PreResult.baseRead,dite_eq_left hm,dite_eq_left hex,dite_eq_right ha]
      exact congrArg (Candidates.Top Ω) hMN
  · have hm' : Ω.profile (N.subst e.images).normalForm ∉ C := hMN ▸ hm
    refine ⟨readGood_outside Ω C t' e.images (by simpa only [Ω.profile_normalForm] using hm'),?_⟩
    rw [preEvaluate_read_outside Ω C hno t' e hm']
    simp only [PreResult.baseRead,dite_eq_right hm]
    exact congrArg (Candidates.Top Ω) hMN

 theorem root_transport {Γ : List (Expr S)} {D m E A B n T : Expr S} {a s : S}
    (ht : HasType P Γ (.app (.lam D m) n) T)
    (hf : HasType P Γ (.lam D m) (.pi A B))
    (d : TypingTree P Γ D (.sort a)) (b : TypingTree P (D :: Γ) m E)
    (hp : HasType P Γ (.pi D E) (.sort s)) (hcF : Converts (.pi A B) (.pi D E))
    (nt : TypingTree P Γ n A) (hc : Converts T (B.instantiate n))
    (hC : IsComponent (PrimaryEdge P) C) :
    ∃ t' : TypingTree P Γ (m.instantiate n) T,
      GoodTransport (hw := hw) Ω C hno (.application ht (.abstraction hf d b hp hcF) nt hc) t' := by
  have hnD : HasType P Γ n D := .conversion nt.typing d.typing hcF.product_compatibility.1
  let ntD := nt.retarget hnD (.symm _ _ hcF.product_compatibility.1)
  let ts := TypingTree.StoredSubstitution.single ntD
  let bt := b.subst ht.valid (Expr.single n) ts
  have ht' := ht.subject_reduction (.head D m n)
  have hc' : Converts T (E.instantiate n) := .trans _ _ _ hc (hcF.product_compatibility.2.subst (Expr.single n))
  let t' := bt.retarget ht' hc'
  refine ⟨t',?_⟩
  have hval : ∀ (e : Environment (hw := hw) Ω C hno Γ)
      (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)),
      ValGood Ω C (.application ht (.abstraction hf d b hp hcF) nt hc) e.images →
      ValGood Ω C t' e.images ∧
      ((preEvaluate Ω C hno (.application ht (.abstraction hf d b hp hcF) nt hc) e).val ha).val =
        ((preEvaluate Ω C hno t' e).val ha).val := by
    intro e ha hg
    have hF : ActiveLayer P C (Ω.profile ((Expr.pi A B).subst e.images)) := by
      by_contra hh
      change (if ActiveLayer P C (Ω.profile ((Expr.pi A B).subst e.images)) then _ else _) at hg
      rw [ite_eq_right hh] at hg
      cases hg with | app hf => cases hf
    change (if ActiveLayer P C (Ω.profile ((Expr.pi A B).subst e.images)) then _ else _) at hg
    rw [ite_eq_left hF] at hg
    obtain ⟨hraw,hpp,hbody,hguard,hbeta⟩ := application_abstraction_beta Ω C hno ht hf d b hp hcF nt hc hC e
      (by simpa only [Ω.profile_normalForm] using hF) ha
    let er := e.cons (ContextTower.HasType.subst hnD e.typed) (preEvaluate Ω C hno ntD e).parameter
      (preEvaluate Ω C hno ntD e).parameter_fits
    have herimages : er.images = Expr.consSub (n.subst e.images) e.images := by
      funext i; cases i <;> rfl
    have hpEq : (preEvaluate Ω C hno nt e).parameter = (preEvaluate Ω C hno ntD e).parameter :=
      preEvaluate_retarget_parameter Ω C hno nt hnD (.symm _ _ hcF.product_compatibility.1) e
    have heren : (e.cons hraw (preEvaluate Ω C hno nt e).parameter hpp).Compatible er := by
      constructor
      · intro i hi; exact .refl _
      · intro i hi; cases i with
        | zero => exact hpEq
        | succ i => rfl
    have hgoodB : ValGood Ω C b er.images := hg.1 (n.subst e.images) hraw
      (by simpa only [Ω.profile_normalForm] using hbody)
    have heT := e.type_convert_eq ht bt.typing hc'
    have haBt : ActiveLayer P C (Ω.profile ((E.instantiate n).subst e.images).normalForm) := heT ▸ ha
    have hsGuard : SubstitutionGuard Ω C (D :: Γ) (Expr.single n) er.images := single_guard Ω C e.images hguard
    have hgoodN : GoodReplacement Ω C ts e.images := single_goodReplacement Ω C ntD e.images (by
      intro hD
      apply (valGood_retarget Ω C nt hnD (.symm _ _ hcF.product_compatibility.1) e.images).mpr
      apply hg.2
      have heD := e.type_convert_eq nt.typing hnD hcF.product_compatibility.1
      rw [← Ω.profile_normalForm,heD,Ω.profile_normalForm]
      exact hD)
    have hgoodBt : ValGood Ω C bt e.images := (goodness_subst Ω C hw b ht.valid (Expr.single n) ts e.images e.typed
      (by simpa only [Expr.comp_single,←herimages] using hsGuard) hgoodN).1
      (by simpa only [Expr.comp_single,Ω.profile_normalForm] using hbody)
      (by simpa only [Expr.comp_single,←herimages] using hgoodB)
    refine ⟨(valGood_retarget Ω C bt ht' hc' e.images).mpr hgoodBt,?_⟩
    refine hbeta.trans (Eq.trans ?_ (preEvaluate_retarget_val Ω C hno bt ht' hc' e haBt ha))
    refine Eq.trans (PreResult.val_congr _ _ (preEvaluate_compatible Ω C hno hC b _ _ heren).1 hbody hbody) ?_
    exact (preEvaluate_subst Ω C hno b ht.valid (Expr.single n) ts er e (single_assigned Ω C hno ntD e) hsGuard).1
      hbody haBt hgoodB
  refine ⟨hval,?_⟩
  intro e hr
  apply baseRead_transport Ω C hno ht t' e
    (e.expression_convert_eq ht ht' (.rel _ _ (.head D m n)))
    (fun h => by cases h with | app hf => cases hf) _ _ hr
  exact hval e

namespace Environment
variable {Ω C hno} {Γ : List (Expr S)}
@[simp] theorem cons_images (e : Environment (hw := hw) Ω C hno Γ) {D n : Expr S}
    (hn : Ω.HasType n (D.subst e.images)) p hp :
    (e.cons hn p hp).images = Expr.consSub n e.images := by
  funext i; cases i <;> rfl
end Environment

namespace GoodTransport
variable {Ω C hno} {Γ : List (Expr S)} {M N T : Expr S}
 theorem refl (t : TypingTree P Γ M T) : GoodTransport (hw := hw) Ω C hno t t :=
  ⟨fun _ _ h => ⟨h,rfl⟩,fun _ h => ⟨h,rfl⟩⟩
 theorem parameter_eq {t : TypingTree P Γ M T} {t' : TypingTree P Γ N T}
    (h : GoodTransport (hw := hw) Ω C hno t t') (e : Environment (hw := hw) Ω C hno Γ)
    (hg : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm) → ValGood Ω C t e.images) :
    (preEvaluate Ω C hno t e).parameter = (preEvaluate Ω C hno t' e).parameter := by
  apply PreResult.parameter_congr _ _ rfl
  intro ha ha'
  exact (h.val e ha (hg ha)).2
end GoodTransport

 theorem application_transport {Γ : List (Expr S)} {f n f' n' D E T : Expr S}
    (ht : HasType P Γ (.app f n) T) (ht' : HasType P Γ (.app f' n') T)
    (ft : TypingTree P Γ f (.pi D E)) (ft' : TypingTree P Γ f' (.pi D E))
    (nt : TypingTree P Γ n D) (nt' : TypingTree P Γ n' D)
    (hc : Converts T (E.instantiate n)) (hc' : Converts T (E.instantiate n'))
    (hf : GoodTransport (hw := hw) Ω C hno ft ft') (hn : GoodTransport (hw := hw) Ω C hno nt nt')
    (hff : Converts f f') (hnn : Converts n n') (hne : Neutral f → Neutral f') :
    GoodTransport (hw := hw) Ω C hno (.application ht ft nt hc) (.application ht' ft' nt' hc') := by
  have hval : ∀ (e : Environment (hw := hw) Ω C hno Γ)
      (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)),
      ValGood Ω C (.application ht ft nt hc) e.images →
      ValGood Ω C (.application ht' ft' nt' hc') e.images ∧
      ((preEvaluate Ω C hno (.application ht ft nt hc) e).val ha).val =
      ((preEvaluate Ω C hno (.application ht' ft' nt' hc') e).val ha).val := by
    intro e ha hg
    change (if ActiveLayer P C (Ω.profile ((Expr.pi D E).subst e.images)) then _ else _) at hg
    change (if ActiveLayer P C (Ω.profile ((Expr.pi D E).subst e.images)) then _ else _) ∧ _
    by_cases hF : ActiveLayer P C (Ω.profile ((Expr.pi D E).subst e.images))
    · rw [ite_eq_left hF] at hg ⊢
      have hFa : ActiveLayer P C (Ω.profile ((Expr.pi D E).subst e.images).normalForm) := by
        simpa only [Ω.profile_normalForm] using hF
      refine ⟨⟨(hf.val e hFa hg.1).1,fun haD => (hn.val e
        (by simpa only [Ω.profile_normalForm] using haD) (hg.2 haD)).1⟩,?_⟩
      apply PreResult.application_val_congr ht ht' ft.typing ft'.typing nt.typing nt'.typing hc hc'
        _ _ _ _ e e rfl rfl (e.expression_convert_eq nt.typing nt'.typing hnn)
      · exact fun _ _ => (hf.val e hFa hg.1).2
      · exact hn.parameter_eq e (fun haD => hg.2 (by simpa only [Ω.profile_normalForm] using haD))
    · rw [ite_eq_right hF] at hg ⊢
      refine ⟨?_,?_⟩
      · cases hg with | app hg => exact .app (hne hg)
      · have hFa : ¬ ActiveLayer P C (Ω.profile ((Expr.pi D E).subst e.images).normalForm) := by
          simpa only [Ω.profile_normalForm] using hF
        simp only [preEvaluate,PreResult.application,PreResult.baseResult,PreResult.applicationValue,dite_eq_right hFa]
  refine ⟨hval,?_⟩
  intro e hr
  apply baseRead_transport Ω C hno ht (.application ht' ft' nt' hc') e
    (e.expression_convert_eq ht ht' (.app hff hnn))
    (fun hh => by cases hh with | app hh => exact .app (hne hh)) _ _ hr
  exact hval e

 theorem abstraction_transport {Γ : List (Expr S)} {D m E D' m' E' T : Expr S} {a a' s s' : S}
    (ht : HasType P Γ (.lam D m) T) (ht' : HasType P Γ (.lam D' m') T)
    (d : TypingTree P Γ D (.sort a)) (d' : TypingTree P Γ D' (.sort a'))
    (b : TypingTree P (D :: Γ) m E) (b' : TypingTree P (D' :: Γ) m' E')
    (hp : HasType P Γ (.pi D E) (.sort s)) (hp' : HasType P Γ (.pi D' E') (.sort s'))
    (hc : Converts T (.pi D E)) (hc' : Converts T (.pi D' E'))
    (hD : Converts D D') (hm : Converts m m') (hE : Converts E E')
    (hb : ∀ (e : Environment (hw := hw) Ω C hno Γ) n
      (hn : Ω.HasType n (D.subst e.images)) (hn' : Ω.HasType n (D'.subst e.images))
      p hpp hpp' ha ha', ValGood Ω C b (e.cons hn p hpp).images →
        ValGood Ω C b' (e.cons hn' p hpp').images ∧
        ((preEvaluate Ω C hno b (e.cons hn p hpp)).val ha).val =
        ((preEvaluate Ω C hno b' (e.cons hn' p hpp')).val ha').val) :
    GoodTransport (hw := hw) Ω C hno (.abstraction ht d b hp hc) (.abstraction ht' d' b' hp' hc') := by
  have hval : ∀ (e : Environment (hw := hw) Ω C hno Γ)
      (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)),
      ValGood Ω C (.abstraction ht d b hp hc) e.images →
      ValGood Ω C (.abstraction ht' d' b' hp' hc') e.images ∧
      ((preEvaluate Ω C hno (.abstraction ht d b hp hc) e).val ha).val =
      ((preEvaluate Ω C hno (.abstraction ht' d' b' hp' hc') e).val ha).val := by
    intro e ha hg
    have hnold {n : Expr S} (hn : Ω.HasType n (D'.subst e.images)) : Ω.HasType n (D.subst e.images) :=
      .conversion hn (ContextTower.HasType.subst d.typing e.typed) (.symm _ _ (hD.subst e.images))
    have hEeq (n : Expr S) (hn : Ω.HasType n (D'.subst e.images)) :
        (E.subst (Expr.consSub n e.images)).normalForm = (E'.subst (Expr.consSub n e.images)).normalForm :=
      Expr.normalForm_converts ((ContextTower.HasType.subst b.typing (e.typed.cons (hnold hn))).type_weaklyNormalizing hw)
        ((ContextTower.HasType.subst b'.typing (e.typed.cons hn)).type_weaklyNormalizing hw)
        (hE.subst (Expr.consSub n e.images))
    refine ⟨?_,?_⟩
    · intro n hn ha'
      have haold : ActiveLayer P C (Ω.profile (E.subst (Expr.consSub n e.images)).normalForm) := by
        rw [hEeq n hn,Ω.profile_normalForm]; exact ha'
      obtain ⟨pa,hpD⟩ := PayloadFits.exists_of_actual (hw := hw) (C := C) (hno := hno) (e.actualExpression d.typing)
      have hDD := e.expression_convert_eq d.typing d'.typing hD
      have hpD' : PayloadFits Ω C hno (D'.subst e.images).normalForm pa := hDD ▸ hpD
      exact (hb e n (hnold hn) hn pa hpD hpD' haold
        (by simpa only [Ω.profile_normalForm,Environment.cons_images] using ha') (hg n (hnold hn)
          (by simpa only [Ω.profile_normalForm] using haold))).1
    · apply PreResult.abstraction_val_congr ht ht' hp hp' hc hc' _ _ e e rfl
      intro n n' hn hn' he p hpp hpp' haB haB'
      subst n'
      exact (hb e n hn hn' p hpp hpp' haB haB' (hg n hn
        (by simpa only [Ω.profile_normalForm,Environment.cons_images] using haB))).2
  refine ⟨hval,?_⟩
  intro e hr
  apply baseRead_transport Ω C hno ht (.abstraction ht' d' b' hp' hc') e
    (e.expression_convert_eq ht ht' (.lam hD hm)) (fun hn => by cases hn) _ _ hr
  exact hval e

 theorem product_transport {Γ : List (Expr S)} {D E D' E' T : Expr S} {a q c : S}
    (ht : HasType P Γ (.pi D E) T) (ht' : HasType P Γ (.pi D' E') T)
    (d : TypingTree P Γ D (.sort a)) (d' : TypingTree P Γ D' (.sort a))
    (b : TypingTree P (D :: Γ) E (.sort q)) (b' : TypingTree P (D' :: Γ) E' (.sort q))
    (hr : P.rule a q c) (hc : Converts T (.sort c))
    (hD : Converts D D') (hE : Converts E E')
    (hd : ∀ (e : Environment (hw := hw) Ω C hno Γ), ReadGood Ω C d e.images →
      ReadGood Ω C d' e.images ∧ (preEvaluate Ω C hno d e).read.val = (preEvaluate Ω C hno d' e).read.val)
    (hb : ∀ (e : Environment (hw := hw) Ω C hno Γ) n
      (hn : Ω.HasType n (D.subst e.images)) (hn' : Ω.HasType n (D'.subst e.images))
      p hpp hpp', ReadGood Ω C b (e.cons hn p hpp).images →
        ReadGood Ω C b' (e.cons hn' p hpp').images ∧
        (preEvaluate Ω C hno b (e.cons hn p hpp)).read.val =
        (preEvaluate Ω C hno b' (e.cons hn' p hpp')).read.val) :
    GoodTransport (hw := hw) Ω C hno (.product ht d b hr hc) (.product ht' d' b' hr hc) := by
  have hdata (e : Environment (hw := hw) Ω C hno Γ) :
      (D.subst e.images).normalForm = (D'.subst e.images).normalForm ∧
      (E.subst (Expr.liftSub e.images)).normalForm = (E'.subst (Expr.liftSub e.images)).normalForm := by
    have hpi := e.expression_convert_eq ht ht' (.pi hD hE)
    have hwp := (ContextTower.HasType.subst ht e.typed).weaklyNormalizing hw
    have hwp' := (ContextTower.HasType.subst ht' e.typed).weaklyNormalizing hw
    rw [Expr.subst,Expr.subst,Expr.normalForm_pi hwp.pi_domain hwp.pi_body,
      Expr.normalForm_pi hwp'.pi_domain hwp'.pi_body] at hpi
    exact Expr.pi.inj hpi
  have hchildren (e : Environment (hw := hw) Ω C hno Γ)
      (hg : ProductGood Ω C d b e.images) :
      ProductGood Ω C d' b' e.images ∧
      (PreResult.productCandidate d.typing b.typing hr (preEvaluate Ω C hno d) (preEvaluate Ω C hno b) e).val =
      (PreResult.productCandidate d'.typing b'.typing hr (preEvaluate Ω C hno d') (preEvaluate Ω C hno b') e).val := by
    have hnold {n : Expr S} (hn : Ω.HasType n (D'.subst e.images)) : Ω.HasType n (D.subst e.images) :=
      .conversion hn (ContextTower.HasType.subst d.typing e.typed) (.symm _ _ (hD.subst e.images))
    have hEeq (n : Expr S) (hn : Ω.HasType n (D'.subst e.images)) :
        (E.subst (Expr.consSub n e.images)).normalForm = (E'.subst (Expr.consSub n e.images)).normalForm :=
      Expr.normalForm_converts ((ContextTower.HasType.subst b.typing (e.typed.cons (hnold hn))).weaklyNormalizing hw)
        ((ContextTower.HasType.subst b'.typing (e.typed.cons hn)).weaklyNormalizing hw)
        (hE.subst (Expr.consSub n e.images))
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro hD'
      apply (hd e (hg.1 ?_)).1
      rw [← Ω.profile_normalForm,(hdata e).1,Ω.profile_normalForm]
      exact hD'
    · intro n hn hE'
      have hEold : Ω.profile (E.subst (Expr.consSub n e.images)) ∈ C := by
        rw [← Ω.profile_normalForm,hEeq n hn,Ω.profile_normalForm]; exact hE'
      obtain ⟨p,hp⟩ := PayloadFits.exists_of_actual (hw := hw) (C := C) (hno := hno) (e.actualExpression d.typing)
      have hp' : PayloadFits Ω C hno (D'.subst e.images).normalForm p := (hdata e).1 ▸ hp
      have hh := (hb e n (hnold hn) hn p hp hp' (by
        simpa only [Environment.cons_images] using hg.2 n (hnold hn) hEold)).1
      simpa only [Environment.cons_images] using hh
    · apply PreResult.productCandidate_congr d.typing b.typing hr d'.typing b'.typing hr _ _ _ _ e e
        (hdata e).1 (hdata e).2
      · intro hD
        exact (hd e (hg.1 (by simpa only [Ω.profile_normalForm] using hD))).2
      · intro n hn hn' p hp hp' hE
        exact (hb e n hn hn' p hp hp' (hg.2 n hn
          (by simpa only [Ω.profile_normalForm,Environment.cons_images] using hE))).2
  constructor
  · intro e ha hg
    have hM := e.expression_convert_eq ht ht' (.pi hD hE)
    refine ⟨?_,?_⟩
    · intro hgate
      exact (hchildren e (hg ⟨hgate.1,by
        rw [← Ω.profile_normalForm,hM,Ω.profile_normalForm]; exact hgate.2⟩)).1
    · by_cases hs : ({c} : Set S) ∈ C
      · apply PreResult.product_val_congr ht ht' d.typing b.typing hr d'.typing b'.typing hr hc hc
          _ _ _ _ e e rfl hM Iff.rfl
        intro hm
        exact (hchildren e (hg ⟨hs,by simpa only [Ω.profile_normalForm] using hm⟩)).2
      · have hgate : ¬ (({c} : Set S) ∈ C ∧ Ω.profile ((Expr.pi D E).subst e.images).normalForm ∈ C) :=
          fun h => hs h.1
        have hgate' : ¬ (({c} : Set S) ∈ C ∧ Ω.profile ((Expr.pi D' E').subst e.images).normalForm ∈ C) :=
          fun h => hs h.1
        simp only [preEvaluate,PreResult.product,dite_eq_right hgate,dite_eq_right hgate']
  · intro e hg
    have hM := e.expression_convert_eq ht ht' (.pi hD hE)
    refine ⟨?_,?_⟩
    · intro hm
      exact (hchildren e (hg (by rw [← Ω.profile_normalForm,hM,Ω.profile_normalForm]; exact hm))).1
    · apply PreResult.product_read_congr ht ht' d.typing b.typing hr d'.typing b'.typing hr hc hc
        _ _ _ _ e e hM
      intro hm
      exact (hchildren e (hg (by simpa only [Ω.profile_normalForm] using hm))).2

 theorem reduction_transport (hC : IsComponent (PrimaryEdge P) C)
    {Γ : List (Expr S)} {M N T : Expr S} (t : TypingTree P Γ M T) (hr : Beta M N) :
    ∃ t' : TypingTree P Γ N T, GoodTransport (hw := hw) Ω C hno t t' := by
  induction hr generalizing Γ T with
  | head D m n =>
      cases t with
      | application ht ft nt hc =>
          cases ft with
          | abstraction hf d b hp hcF =>
              exact root_transport Ω C hno ht hf d b hp hcF nt hc hC
  | app_left hr ih =>
      cases t with
      | application ht ft nt hc =>
          obtain ⟨ft',hft⟩ := ih ft
          have ht' := ht.subject_reduction (.app_left hr)
          exact ⟨.application ht' ft' nt hc,application_transport Ω C hno ht ht' ft ft' nt nt hc hc
            hft (.refl nt) (.rel _ _ hr) (.refl _) (fun hn => hn.beta hr)⟩
  | app_right hr ih =>
      cases t with
      | @application Γ f n D E T ht ft nt hc =>
          obtain ⟨nt',hnt⟩ := ih nt
          have ht' := ht.subject_reduction (.app_right hr)
          have hc' : Converts T (E.instantiate _) := .trans _ _ _ hc ((show Converts _ _ from .rel _ _ hr).instantiate_right E)
          exact ⟨.application ht' ft nt' hc',application_transport Ω C hno ht ht' ft ft nt nt' hc hc'
            (.refl ft) hnt (.refl _) (.rel _ _ hr) (fun hn => hn)⟩
  | @lam_domain D D' m hr ih =>
      cases t with
      | @abstraction Γ _ _ E a s T ht d b hp hc =>
          obtain ⟨d',_⟩ := ih d
          let hctx := ContextEquivalent.head_conversion d.typing d'.typing (.rel _ _ hr)
          let b' := b.recontext hctx
          have ht' := ht.subject_reduction (.lam_domain hr)
          have hp' := hp.subject_reduction (.pi_domain hr)
          have hc' : Converts T (.pi D' E) := .trans _ _ _ hc (.rel _ _ (.pi_domain hr))
          refine ⟨.abstraction ht' d' b' hp' hc',abstraction_transport Ω C hno ht ht' d d' b b' hp hp'
            hc hc' (.rel _ _ hr) (.refl _) (.refl _) ?_⟩
          intro e n hn hn' p hpp hpp' ha ha' hg
          refine ⟨?_,?_⟩
          · change (goodness Ω C (b.recontext hctx) (e.cons hn' p hpp').images).1
            rw [goodness_recontext]
            simpa only [Environment.cons_images] using hg
          · apply PreResult.val_congr
            exact (preEvaluate_recontext Ω C hno b hctx (e.cons hn p hpp) (e.cons hn' p hpp') ⟨rfl,rfl⟩).1
  | lam_body hr ih =>
      cases t with
      | abstraction ht d b hp hc =>
          obtain ⟨b',hb⟩ := ih b
          have ht' := ht.subject_reduction (.lam_body hr)
          refine ⟨.abstraction ht' d b' hp hc,abstraction_transport Ω C hno ht ht' d d b b' hp hp
            hc hc (.refl _) (.rel _ _ hr) (.refl _) ?_⟩
          intro e n hn hn' p hpp hpp' ha ha' hg
          exact hb.val (e.cons hn p hpp) ha hg
  | @pi_domain D D' E hr ih =>
      cases t with
      | @product Γ _ _ a b c T ht d bt hrule hc =>
          obtain ⟨d',hd⟩ := ih d
          let hctx := ContextEquivalent.head_conversion d.typing d'.typing (.rel _ _ hr)
          let b' := bt.recontext hctx
          have ht' := ht.subject_reduction (.pi_domain hr)
          refine ⟨.product ht' d' b' hrule hc,product_transport Ω C hno ht ht' d d' bt b' hrule hc
            (.rel _ _ hr) (.refl _) hd.read ?_⟩
          intro e n hn hn' p hpp hpp' hg
          refine ⟨?_,?_⟩
          · change (goodness Ω C (bt.recontext hctx) (e.cons hn' p hpp').images).2
            rw [goodness_recontext]
            simpa only [Environment.cons_images] using hg
          · exact (preEvaluate_recontext Ω C hno bt hctx (e.cons hn p hpp) (e.cons hn' p hpp') ⟨rfl,rfl⟩).2
  | pi_body hr ih =>
      cases t with
      | product ht d bt hrule hc =>
          obtain ⟨b',hb⟩ := ih bt
          have ht' := ht.subject_reduction (.pi_body hr)
          refine ⟨.product ht' d b' hrule hc,product_transport Ω C hno ht ht' d d bt b' hrule hc
            (.refl _) (.rel _ _ hr) (fun e hg => ⟨hg,rfl⟩) ?_⟩
          intro e n hn hn' p hpp hpp' hg
          exact hb.read (e.cons hn p hpp) hg

namespace GoodTransport
variable {Ω C hno} {Γ : List (Expr S)} {M N L T : Expr S}
 theorem trans {t : TypingTree P Γ M T} {t' : TypingTree P Γ N T} {t'' : TypingTree P Γ L T}
    (h : GoodTransport (hw := hw) Ω C hno t t') (h' : GoodTransport (hw := hw) Ω C hno t' t'') :
    GoodTransport (hw := hw) Ω C hno t t'' := by
  constructor
  · intro e ha hg
    have hh := h.val e ha hg
    have hh' := h'.val e ha hh.1
    exact ⟨hh'.1,hh.2.trans hh'.2⟩
  · intro e hg
    have hh := h.read e hg
    have hh' := h'.read e hh.1
    exact ⟨hh'.1,hh.2.trans hh'.2⟩
end GoodTransport

 theorem reduces_transport (hC : IsComponent (PrimaryEdge P) C)
    {Γ : List (Expr S)} {M N T : Expr S} (t : TypingTree P Γ M T) (hr : Reduces M N) :
    ∃ t' : TypingTree P Γ N T, GoodTransport (hw := hw) Ω C hno t t' := by
  induction hr with
  | refl => exact ⟨t,.refl t⟩
  | tail _ h ih =>
      obtain ⟨t',ht⟩ := ih
      obtain ⟨t'',ht'⟩ := reduction_transport Ω C hno hC t' h
      exact ⟨t'',ht.trans ht'⟩

/-- The good part of any stored tree is transported to a normal stored tree. -/
theorem normalize_transport (hC : IsComponent (PrimaryEdge P) C)
    {Γ : List (Expr S)} {M T : Expr S} (t : TypingTree P Γ M T) :
    ∃ t' : TypingTree P Γ M.normalForm T, GoodTransport (hw := hw) Ω C hno t t' :=
  reduces_transport Ω C hno hC t (Expr.normalForm_spec (t.typing.weaklyNormalizing hw)).1

/-- An arbitrary good literal-sort Read equals its normal-syntax interpretation,
even for a different literal expected sort in a nonfunctional specification. -/
theorem good_normal_read (hC : IsComponent (PrimaryEdge P) C)
    {Γ : List (Expr S)} {M : Expr S} {s r : S} (t : TypingTree P Γ M (.sort s))
    (t' : TypingTree P Γ M.normalForm (.sort r))
    (e : Environment (hw := hw) Ω C hno Γ) (hg : ReadGood Ω C t e.images) :
    (preEvaluate Ω C hno t e).read.val = (preEvaluate Ω C hno t' e).read.val := by
  obtain ⟨tn,htn⟩ := normalize_transport Ω C hno hC t
  have hn := (Expr.normalForm_spec (t.typing.weaklyNormalizing hw)).2
  exact (htn.read e hg).2.trans ((normal_tree_independence Ω C hno tn hn t' e).2 s r rfl rfl)
end PureTypeSystem.ObservationValues

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_ObservationCandidates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.ObservationValues

section
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

/-- Normalizing the generic expression before a raw typed substitution leaves
its actual normal form unchanged. -/
theorem normal_subst_eq {Γ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (e : Environment (hw := hw) Ω C hno Γ) :
    (A.normalForm.subst e.images).normalForm = (A.subst e.images).normalForm :=
  Expr.normalForm_converts ((ContextTower.HasType.subst (hA.normalForm hw) e.typed).weaklyNormalizing hw)
    ((ContextTower.HasType.subst hA e.typed).weaklyNormalizing hw)
    (.symm _ _ ((Expr.normalForm_spec (hA.weaklyNormalizing hw)).1.converts.subst e.images))

noncomputable def normalRead {Γ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (e : Environment (hw := hw) Ω C hno Γ) :
    Candidate Ω (A.subst e.images).normalForm :=
  ⟨(preEvaluate Ω C hno (TypingTree.ofTyping (hA.normalForm hw)) e).read.val,
    normal_subst_eq Ω C hno hA e ▸ (preEvaluate Ω C hno (TypingTree.ofTyping (hA.normalForm hw)) e).read.property⟩

theorem normalRead_eq {Γ : List (Expr S)} {A : Expr S} {s r : S}
    (hA : HasType P Γ A (.sort s)) (t : TypingTree P Γ A.normalForm (.sort r))
    (e : Environment (hw := hw) Ω C hno Γ) :
    (normalRead Ω C hno hA e).val = (preEvaluate Ω C hno t e).read.val :=
  (normal_tree_independence Ω C hno _ (Expr.normalForm_spec (hA.weaklyNormalizing hw)).2 t e).2 s r rfl rfl

theorem preEvaluate_read_cast_expr {Γ : List (Expr S)} {M N T : Expr S}
    (he : M = N) (t : TypingTree P Γ M T)
    (e : Environment (hw := hw) Ω C hno Γ) :
    (preEvaluate Ω C hno (he ▸ t) e).read.val = (preEvaluate Ω C hno t e).read.val := by
  subst N
  rfl

theorem normalRead_eq_of_nf {Γ : List (Expr S)} {A N : Expr S} {s r : S}
    (hA : HasType P Γ A (.sort s)) (t : TypingTree P Γ N (.sort r)) (hn : A.normalForm = N)
    (e : Environment (hw := hw) Ω C hno Γ) :
    (normalRead Ω C hno hA e).val = (preEvaluate Ω C hno t e).read.val :=
  (normalRead_eq Ω C hno hA (hn.symm ▸ t) e).trans
    (preEvaluate_read_cast_expr Ω C hno hn.symm t e)

theorem normalRead_congr {Γ : List (Expr S)} {A B : Expr S} {s r : S}
    (hA : HasType P Γ A (.sort s)) (hB : HasType P Γ B (.sort r)) (hc : Converts A B)
    (e : Environment (hw := hw) Ω C hno Γ) :
    (normalRead Ω C hno hA e).val = (normalRead Ω C hno hB e).val := by
  have he := Expr.normalForm_converts (hA.weaklyNormalizing hw) (hB.weaklyNormalizing hw) hc
  exact normalRead_eq_of_nf Ω C hno hA (TypingTree.ofTyping (hB.normalForm hw)) he e

theorem read_outside {Γ : List (Expr S)} {M T : Expr S} (t : TypingTree P Γ M T)
    (e : Environment (hw := hw) Ω C hno Γ) (ho : Ω.profile (M.subst e.images).normalForm ∉ C) :
    (preEvaluate Ω C hno t e).read.val = Candidates.Top Ω (M.subst e.images).normalForm := by
  cases t <;> simp only [preEvaluate,PreResult.lookup,PreResult.sort,PreResult.product,
    PreResult.abstraction,PreResult.application,PreResult.baseResult,PreResult.baseRead,ho,ite_false, if_false,dite_false]

theorem normalRead_outside {Γ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (e : Environment (hw := hw) Ω C hno Γ)
    (ho : Ω.profile (A.subst e.images) ∉ C) :
    (normalRead Ω C hno hA e).val = Candidates.Top Ω (A.subst e.images).normalForm := by
  have hh := read_outside Ω C hno (TypingTree.ofTyping (hA.normalForm hw)) e (by
    rw [normal_subst_eq Ω C hno hA e,Ω.profile_normalForm]; exact ho)
  exact hh.trans (congrArg (Candidates.Top Ω) (normal_subst_eq Ω C hno hA e))

theorem normalRead_sort {Γ : List (Expr S)} {s r : S}
    (hs : HasType P Γ (.sort s) (.sort r)) (e : Environment (hw := hw) Ω C hno Γ) :
    (normalRead Ω C hno hs e).val = Candidates.Top Ω (.sort s) := by
  obtain ⟨t,ha,hc⟩ := hs.generation
  let tree : TypingTree P Γ (.sort s) (.sort r) := .sort hs ha hc
  exact (normalRead_eq_of_nf Ω C hno hs tree (Expr.normalForm_of_normal (Normal.sort s)) e).trans (by
    simp only [tree,preEvaluate,PreResult.sort,Expr.subst,Expr.normalForm_of_normal (Normal.sort s)])

/-- The component entry is generic-normal Read; other generic profiles and
unsorted literal expected sorts use exactly typed top. -/
noncomputable def R {Γ : List (Expr S)} (A : Expr S) (e : Environment (hw := hw) Ω C hno Γ) : Set (Expr S) :=
  if Profile P Γ A ∈ C then
    if hs : ∃ s, HasType P Γ A (.sort s) then (normalRead Ω C hno hs.choose_spec e).val
    else Candidates.Top Ω (A.subst e.images).normalForm
  else Candidates.Top Ω (A.subst e.images).normalForm

theorem R_candidate {Γ : List (Expr S)} (A : Expr S) (e : Environment (hw := hw) Ω C hno Γ) :
    Candidates.IsCandidate Ω (A.subst e.images).normalForm (R Ω C hno A e) := by
  unfold R
  split
  · split
    · exact (normalRead Ω C hno _ e).property
    · exact Candidates.top_candidate
  · exact Candidates.top_candidate

theorem R_of_sorted {Γ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (e : Environment (hw := hw) Ω C hno Γ)
    (hg : Profile P Γ A ∈ C) :
    R Ω C hno A e = (normalRead Ω C hno hA e).val := by
  simp only [R,hg,dite_true,show ∃ s, HasType P Γ A (.sort s) from ⟨s,hA⟩]
  exact normalRead_congr Ω C hno _ hA (.refl _) e

theorem R_outside {Γ : List (Expr S)} (A : Expr S) (e : Environment (hw := hw) Ω C hno Γ)
    (ho : Profile P Γ A ∉ C ∨ Ω.profile (A.subst e.images) ∉ C) :
    R Ω C hno A e = Candidates.Top Ω (A.subst e.images).normalForm := by
  unfold R
  split_ifs with hg hs
  · exact normalRead_outside Ω C hno hs.choose_spec e (ho.resolve_left (not_not.mpr hg))
  · rfl
  · rfl

theorem R_sort {Γ : List (Expr S)} (s : S) (e : Environment (hw := hw) Ω C hno Γ) :
    R Ω C hno (.sort s) e = Candidates.Top Ω (.sort s) := by
  unfold R
  split_ifs with hg hs
  · exact normalRead_sort Ω C hno hs.choose_spec e
  · simp only [Expr.subst,Expr.normalForm_of_normal (Normal.sort s)]
  · simp only [Expr.subst,Expr.normalForm_of_normal (Normal.sort s)]

namespace Environment
variable {Ω C hno}
noncomputable def ofImages {Γ : List (Expr S)} (σ : Nat → Expr S)
    (hσ : Ω.TypedSubstitution Γ σ) : Environment (hw := hw) Ω C hno Γ where
  images := σ
  typed := hσ
  parameters := fun i => if hi : ∃ A, Lookup Γ i A then
    (PayloadFits.exists_of_actual (hno := hno) ⟨_,(hσ _ _ hi.choose_spec).actual_type hw⟩).choose else none
  lawful := by
    intro i A hi
    simp only [dite_eq_left (show ∃ B, Lookup Γ i B from ⟨A,hi⟩)]
    have he := Lookup.unique (show Lookup Γ i (Exists.choose (show ∃ B, Lookup Γ i B from ⟨A,hi⟩)) from
      (show ∃ B, Lookup Γ i B from ⟨A,hi⟩).choose_spec) hi
    simpa only [he] using (PayloadFits.exists_of_actual (hno := hno)
      ⟨_,(hσ _ _ (show ∃ B, Lookup Γ i B from ⟨A,hi⟩).choose_spec).actual_type hw⟩).choose_spec

def Ext {Γ : List (Expr S)} {D : Expr S} (e : Environment (hw := hw) Ω C hno Γ)
    (f : Environment (hw := hw) Ω C hno (D :: Γ)) (n : Expr S) : Prop :=
  f.images = Expr.extend e.images n ∧ ∀ i, f.parameters (i+1) = e.parameters i

theorem Ext.reindexed {Γ : List (Expr S)} {D n : Expr S}
    {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno (D :: Γ)}
    (he : e.Ext f n) : e.Reindexed f Nat.succ := by
  intro i _
  exact ⟨(congrFun he.1 (i+1)).symm,(he.2 i).symm⟩

theorem cons_ext {Γ : List (Expr S)} {D n : Expr S} (e : Environment (hw := hw) Ω C hno Γ)
    (hn : Ω.HasType n (D.subst e.images)) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno (D.subst e.images).normalForm p) : e.Ext (e.cons hn p hp) n :=
  ⟨rfl,fun _ => rfl⟩

theorem extend_exists {Γ : List (Expr S)} {D n : Expr S} (e : Environment (hw := hw) Ω C hno Γ)
    (hn : Ω.HasType n (D.subst e.images)) : ∃ f : Environment (hw := hw) Ω C hno (D :: Γ), e.Ext f n := by
  obtain ⟨p,hp⟩ := PayloadFits.exists_of_actual (hno := hno) ⟨_,hn.actual_type hw⟩
  exact ⟨e.cons hn p hp,e.cons_ext hn p hp⟩
theorem ext_data {Γ : List (Expr S)} {e f : Environment (hw := hw) Ω C hno Γ}
    (hi : e.images = f.images) (hp : e.parameters = f.parameters) : e = f := by
  cases e; cases f
  cases hi; cases hp
  rfl

theorem Ext.payload {Γ : List (Expr S)} {D n : Expr S}
    {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno (D :: Γ)}
    (he : e.Ext f n) : PayloadFits Ω C hno (D.subst e.images).normalForm (f.parameters 0) := by
  have hp := f.lawful 0 _ (.zero D Γ)
  simpa only [he.1,Expr.subst_raise_extend] using hp

theorem Ext.eq_cons {Γ : List (Expr S)} {D n : Expr S}
    {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno (D :: Γ)}
    (he : e.Ext f n) (hn : Ω.HasType n (D.subst e.images)) :
    f = e.cons hn (f.parameters 0) he.payload := by
  apply ext_data he.1
  funext i
  cases i with
  | zero => rfl
  | succ i => exact he.2 i

end Environment

theorem R_sorted_conversion {Γ : List (Expr S)} {A B : Expr S} {s r : S}
    (hA : HasType P Γ A (.sort s)) (hB : HasType P Γ B (.sort r)) (hc : Converts A B)
    (e : Environment (hw := hw) Ω C hno Γ) : R Ω C hno A e = R Ω C hno B e := by
  have hp := Profile.converts (P := P) (Γ := Γ) (hA.weaklyNormalizing hw) (hB.weaklyNormalizing hw) hc
  by_cases ha : Profile P Γ A ∈ C
  · rw [R_of_sorted Ω C hno hA e ha,R_of_sorted Ω C hno hB e (hp ▸ ha)]
    exact normalRead_congr Ω C hno hA hB hc e
  · rw [R_outside Ω C hno A e (.inl ha),R_outside Ω C hno B e (.inl (hp ▸ ha))]
    exact congrArg (Candidates.Top Ω) (Expr.normalForm_converts
      ((ContextTower.HasType.subst hA e.typed).weaklyNormalizing hw)
      ((ContextTower.HasType.subst hB e.typed).weaklyNormalizing hw) (hc.subst e.images))

theorem R_normalForm {Γ : List (Expr S)} {A : Expr S} (hA : Expected P Γ A)
    (e : Environment (hw := hw) Ω C hno Γ) : R Ω C hno A e = R Ω C hno A.normalForm e := by
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩
  · rw [Expr.normalForm_of_normal (Normal.sort s)]
  · exact R_sorted_conversion Ω C hno hA (hA.normalForm hw)
      (Expr.normalForm_spec (hA.weaklyNormalizing hw)).1.converts e

theorem R_conversion {Γ : List (Expr S)} {A B : Expr S}
    (hA : Expected P Γ A) (hB : Expected P Γ B) (hc : Converts A B)
    (e : Environment (hw := hw) Ω C hno Γ) : R Ω C hno A e = R Ω C hno B e := by
  rw [R_normalForm Ω C hno hA e,R_normalForm Ω C hno hB e,
    Expr.normalForm_converts (hA.wn hw) (hB.wn hw) hc]

theorem normalRead_weaken {Γ : List (Expr S)} {A D : Expr S} {s r : S}
    (hA : HasType P Γ A (.sort s)) (hD : HasType P Γ D (.sort r))
    {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno (D :: Γ)}
    {n : Expr S} (he : e.Ext f n) :
    (normalRead Ω C hno (HasType.weaken hA hD) f).val = (normalRead Ω C hno hA e).val := by
  let t := TypingTree.ofTyping (hA.normalForm hw)
  have hh := normalRead_eq_of_nf Ω C hno (HasType.weaken hA hD)
    (t.rename (.cons hD.valid hD) Nat.succ (TypingTree.DeclRenaming.weaken D))
    (Expr.normalForm_rename (hA.weaklyNormalizing hw) Nat.succ) f
  exact hh.trans (preEvaluate_rename Ω C hno t (.cons hD.valid hD) Nat.succ
    (TypingTree.DeclRenaming.weaken D) e f he.reindexed).2.symm

theorem R_weakening {Γ : List (Expr S)} {A D : Expr S} {r : S}
    (hA : Expected P Γ A) (hD : HasType P Γ D (.sort r))
    {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno (D :: Γ)}
    {n : Expr S} (he : e.Ext f n) : R Ω C hno (A.rename Nat.succ) f = R Ω C hno A e := by
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩
  · exact (R_sort Ω C hno s f).trans (R_sort Ω C hno s e).symm
  · have hp := Profile.weaken hw hA hD
    by_cases ha : Profile P Γ A ∈ C
    · rw [R_of_sorted Ω C hno (HasType.weaken hA hD) f (hp ▸ ha),R_of_sorted Ω C hno hA e ha]
      exact normalRead_weaken Ω C hno hA hD he
    · rw [R_outside Ω C hno _ f (.inl (hp ▸ ha)),R_outside Ω C hno _ e (.inl ha),
        he.1,Expr.subst_raise_extend]

theorem normalRead_recontext {Γ Δ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (h : ContextEquivalent P Γ Δ)
    (e : Environment (hw := hw) Ω C hno Γ) (f : Environment (hw := hw) Ω C hno Δ)
    (he : e.SameData f) :
    (normalRead Ω C hno hA e).val = (normalRead Ω C hno ((h.typing _ _).mp hA) f).val := by
  let t := TypingTree.ofTyping (hA.normalForm hw)
  exact (preEvaluate_recontext Ω C hno t h e f he).2.trans
    (normalRead_eq Ω C hno ((h.typing _ _).mp hA) (t.recontext h) f).symm

theorem R_recontext {Γ Δ : List (Expr S)} {A : Expr S} (hA : Expected P Γ A)
    (h : ContextEquivalent P Γ Δ)
    (e : Environment (hw := hw) Ω C hno Γ) (f : Environment (hw := hw) Ω C hno Δ)
    (he : e.SameData f) : R Ω C hno A e = R Ω C hno A f := by
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩
  · exact (R_sort Ω C hno s e).trans (R_sort Ω C hno s f).symm
  · have hp : Profile P Γ A = Profile P Δ A := by
      ext s; exact h.typing _ _
    by_cases ha : Profile P Γ A ∈ C
    · rw [R_of_sorted Ω C hno hA e ha,R_of_sorted Ω C hno ((h.typing _ _).mp hA) f (hp ▸ ha)]
      exact normalRead_recontext Ω C hno hA h e f he
    · rw [R_outside Ω C hno _ e (.inl ha),R_outside Ω C hno _ f (.inl (hp ▸ ha)),he.1]

end

section
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)
variable (hC : IsComponent (PrimaryEdge P) C)
include hC

theorem R_eq_normalRead_relevant {Γ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (hr : Relevant (P := P) C Γ A)
    (e : Environment (hw := hw) Ω C hno Γ) : R Ω C hno A e = (normalRead Ω C hno hA e).val := by
  by_cases hg : Profile P Γ A ∈ C
  · exact R_of_sorted Ω C hno hA e hg
  · have ha : Ω.profile (A.subst e.images) ∉ C := fun ha =>
      hg (relevant_actual_mem Ω C hw hC hA e.typed hr ha)
    exact (R_outside Ω C hno A e (.inl hg)).trans (normalRead_outside Ω C hno hA e ha).symm

theorem R_eq_read_normal {Γ : List (Expr S)} {A : Expr S} {s : S}
    (t : TypingTree P Γ A (.sort s)) (hn : Normal A) (hr : Relevant (P := P) C Γ A)
    (e : Environment (hw := hw) Ω C hno Γ) : R Ω C hno A e = (preEvaluate Ω C hno t e).read.val :=
  (R_eq_normalRead_relevant Ω C hno hC t.typing hr e).trans
    (normalRead_eq_of_nf Ω C hno t.typing t (Expr.normalForm_of_normal hn) e)

theorem R_eq_read_good {Γ : List (Expr S)} {A : Expr S} {s : S}
    (t : TypingTree P Γ A (.sort s)) (hr : Relevant (P := P) C Γ A)
    (e : Environment (hw := hw) Ω C hno Γ) (hg : ReadGood Ω C t e.images) :
    R Ω C hno A e = (preEvaluate Ω C hno t e).read.val :=
  (R_eq_normalRead_relevant Ω C hno hC t.typing hr e).trans
    (good_normal_read Ω C hno hC t (TypingTree.ofTyping (t.typing.normalForm hw)) e hg).symm

theorem normal_product_candidate {Γ : List (Expr S)} {D E : Expr S} {a b c : S}
    (d : TypingTree P Γ D (.sort a)) (q : TypingTree P (D :: Γ) E (.sort b)) (hr : P.rule a b c)
    (hn : Normal (.pi D E)) (hg : Profile P Γ (.pi D E) ∈ C)
    (e : Environment (hw := hw) Ω C hno Γ) (ha : Ω.profile ((Expr.pi D E).subst e.images) ∈ C) :
    R Ω C hno (.pi D E) e = (PreResult.productCandidate d.typing q.typing hr
      (preEvaluate Ω C hno d) (preEvaluate Ω C hno q) e).val := by
  let t : TypingTree P Γ (.pi D E) (.sort c) :=
    .product (.product d.typing q.typing hr) d q hr (.refl _)
  have he := R_eq_read_normal Ω C hno hC t hn ⟨_,hg,.refl _⟩ e
  exact he.trans (by
    simp only [t,preEvaluate,PreResult.product,Ω.profile_normalForm,ha,ite_true, if_true])

theorem normal_product_iff {Γ : List (Expr S)} {D E : Expr S} {s : S}
    (hp : HasType P Γ (.pi D E) (.sort s)) (hn : Normal (.pi D E))
    (hg : Profile P Γ (.pi D E) ∈ C) (e : Environment (hw := hw) Ω C hno Γ)
    (ha : Ω.profile ((Expr.pi D E).subst e.images) ∈ C) (h : Expr S) :
    h ∈ R Ω C hno (.pi D E) e ↔
      h ∈ Candidates.Top Ω ((Expr.pi D E).subst e.images).normalForm ∧
      ∀ n, n ∈ R Ω C hno D e → ∀ f : Environment (hw := hw) Ω C hno (D :: Γ),
        e.Ext f n → Expr.app h n ∈ R Ω C hno E f := by
  obtain ⟨a,b,c,hD,hE,hr,_⟩ := hp.generation_pi
  let d := TypingTree.ofTyping hD
  let q := TypingTree.ofTyping hE
  let t := PreResult.productData hD hE hr e
  let bd : t.BodyReads := fun n hn p hp => (preEvaluate Ω C hno q (t.extend hn p hp)).read
  have hf := Profile.triple hw hp
  have hdrel : Relevant (P := P) C Γ D := ⟨_,hg,.single (.domain hf)⟩
  have herel : Relevant (P := P) C (D :: Γ) E := ⟨_,hg,.single (.codomain hf)⟩
  have hrd := R_eq_read_normal Ω C hno hC d hn.pi_domain hdrel e
  have htest : t.testers (preEvaluate Ω C hno d e).read = R Ω C hno D e := by
    unfold ProductInstance.testers
    split_ifs with hc
    · exact hrd.symm
    · exact (R_outside Ω C hno D e (.inr (by simpa only [t,PreResult.productData,
        ProductInstance.domainNF,ProductInstance.rawDomain,Ω.profile_normalForm] using hc))).symm
  have hre : ∀ f : Environment (hw := hw) Ω C hno (D :: Γ),
      R Ω C hno E f = (preEvaluate Ω C hno q f).read.val :=
    fun f => R_eq_read_normal Ω C hno hC q hn.pi_body herel f
  rw [normal_product_candidate Ω C hno hC d q hr hn hg e ha]
  change h ∈ (t.candidate (preEvaluate Ω C hno d e).read bd).val ↔ _
  constructor
  · intro hh
    refine ⟨?_,?_⟩
    · exact t.product_nf.symm ▸ hh.1
    · intro n hnr f he
      have hnt : n ∈ t.testers (preEvaluate Ω C hno d e).read := htest.symm ▸ hnr
      have hnty := (t.testers_top _ hnt).1
      have hfcons := he.eq_cons (t.rawArgument hnty)
      rw [hfcons,hre]
      by_cases hc : Ω.profile (t.targetNF n) ∈ C
      · exact t.candidate_body _ bd hh hnt hc (f.parameters 0) he.payload
      · have hout := t.candidate_outside _ bd hh hnt hc
        have heo := read_outside Ω C hno q (t.extend hnty (f.parameters 0) he.payload) hc
        exact heo.symm ▸ hout
  · rintro ⟨hht,hbody⟩
    refine ⟨t.product_nf ▸ hht,?_⟩
    intro n hn U hU
    have hnty := (t.testers_top _ hn).1
    have hnr : n ∈ R Ω C hno D e := htest ▸ hn
    simp only [ProductInstance.fibers,hnty,dite_true] at hU
    split_ifs at hU with hc
    · obtain ⟨p,hp,rfl⟩ := hU
      rw [← hre]
      exact hbody n hnr (t.extend hnty p hp) (e.cons_ext (t.rawArgument hnty) p hp)
    · have heU : U = Candidates.Top Ω (t.targetNF n) := hU
      rw [heU]
      obtain ⟨p,hp⟩ := PayloadFits.exists_of_actual (hno := hno) ⟨_,(t.rawArgument hnty).actual_type hw⟩
      have hmem := hbody n hnr (t.extend hnty p hp) (e.cons_ext (t.rawArgument hnty) p hp)
      rw [hre,read_outside Ω C hno q (t.extend hnty p hp) hc] at hmem
      exact hmem

end

section
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

namespace Environment
variable {Ω C hno}
theorem Ext.argument {Γ : List (Expr S)} {D n : Expr S}
    {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno (D :: Γ)}
    (he : e.Ext f n) : Ω.HasType n (D.subst e.images) := by
  have hh := f.typed 0 _ (.zero D Γ)
  simpa only [he.1,Expr.extend_zero,Expr.subst_raise_extend] using hh

theorem Ext.convert_domain {Γ : List (Expr S)} {D D' n : Expr S} {a b : S}
    (hD : HasType P Γ D (.sort a)) (hD' : HasType P Γ D' (.sort b)) (hc : Converts D D')
    {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno (D :: Γ)}
    (he : e.Ext f n) : ∃ g : Environment (hw := hw) Ω C hno (D' :: Γ), e.Ext g n ∧ f.SameData g := by
  have ht := ContextTower.HasType.subst hD' e.typed
  have hnf := Expr.normalForm_converts ((ContextTower.HasType.subst hD e.typed).weaklyNormalizing hw)
    (ht.weaklyNormalizing hw) (hc.subst e.images)
  have hn := he.argument.conversion ht (hc.subst e.images)
  let g := e.cons hn (f.parameters 0) (hnf ▸ he.payload)
  refine ⟨g,e.cons_ext hn _ _,he.1,?_⟩
  funext i
  cases i with
  | zero => rfl
  | succ i => exact he.2 i
end Environment

theorem normalRead_compatible (hC : IsComponent (PrimaryEdge P) C)
    {Γ : List (Expr S)} {A : Expr S} {s : S} (hA : HasType P Γ A (.sort s))
    (e f : Environment (hw := hw) Ω C hno Γ) (he : e.Compatible f) :
    (normalRead Ω C hno hA e).val = (normalRead Ω C hno hA f).val :=
  (preEvaluate_compatible Ω C hno hC (TypingTree.ofTyping (hA.normalForm hw)) e f he).2

theorem R_compatible (hC : IsComponent (PrimaryEdge P) C)
    {Γ : List (Expr S)} {A : Expr S} (hA : Expected P Γ A)
    (e f : Environment (hw := hw) Ω C hno Γ) (he : e.Compatible f) :
    R Ω C hno A e = R Ω C hno A f := by
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩
  · exact (R_sort Ω C hno s e).trans (R_sort Ω C hno s f).symm
  · by_cases hc : Profile P Γ A ∈ C
    · rw [R_of_sorted Ω C hno hA e hc,R_of_sorted Ω C hno hA f hc]
      exact normalRead_compatible Ω C hno hC hA e f he
    · rw [R_outside Ω C hno A e (.inl hc),R_outside Ω C hno A f (.inl hc),
        e.actual_expr_eq he.1 hA]

theorem R_binder_conversion {Γ : List (Expr S)} {D D' E E' n : Expr S} {a b s r : S}
    (hD : HasType P Γ D (.sort a)) (hD' : HasType P Γ D' (.sort b)) (hc : Converts D D')
    (hE : HasType P (D :: Γ) E (.sort s)) (hE' : HasType P (D' :: Γ) E' (.sort r))
    (hh : Converts E E') (e : Environment (hw := hw) Ω C hno Γ)
    (f : Environment (hw := hw) Ω C hno (D :: Γ)) (g : Environment (hw := hw) Ω C hno (D' :: Γ))
    (_he : e.Ext f n) (_he' : e.Ext g n) (heq : f.SameData g) :
    R Ω C hno E f = R Ω C hno E' g := by
  let hctx := ContextEquivalent.head_conversion hD hD' hc
  exact (R_recontext Ω C hno (.sorted hE) hctx f g heq).trans
    (R_sorted_conversion Ω C hno ((hctx.typing _ _).mp hE) hE' hh g)

end

section
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)
variable (hC : IsComponent (PrimaryEdge P) C)
include hC

theorem product_iff {Γ : List (Expr S)} {D E : Expr S} {s : S}
    (hp : HasType P Γ (.pi D E) (.sort s))
    (hg : Profile P Γ (.pi D E) ∈ C) (e : Environment (hw := hw) Ω C hno Γ)
    (ha : Ω.profile ((Expr.pi D E).subst e.images) ∈ C) (h : Expr S) :
    h ∈ R Ω C hno (.pi D E) e ↔
      h ∈ Candidates.Top Ω ((Expr.pi D E).subst e.images).normalForm ∧
      ∀ n, n ∈ R Ω C hno D e → ∀ f : Environment (hw := hw) Ω C hno (D :: Γ),
        e.Ext f n → Expr.app h n ∈ R Ω C hno E f := by
  obtain ⟨a,b,c,hD,hE,hr,_⟩ := hp.generation_pi
  have hDN := hD.normalForm hw
  have hEN := hE.normalForm hw
  have cD := (Expr.normalForm_spec (hD.weaklyNormalizing hw)).1.converts
  have cE := (Expr.normalForm_spec (hE.weaklyNormalizing hw)).1.converts
  let ctx := ContextEquivalent.head_conversion hD hDN cD
  have hEN' := (ctx.typing _ _).mp hEN
  have hpn : HasType P Γ (.pi D.normalForm E.normalForm) (.sort c) := .product hDN hEN' hr
  have nc := Converts.pi cD cE
  have hn : Normal (.pi D.normalForm E.normalForm) := .pi
    (Expr.normalForm_spec (hD.weaklyNormalizing hw)).2 (Expr.normalForm_spec (hE.weaklyNormalizing hw)).2
  have hprof := Profile.converts (P := P) (Γ := Γ) (hp.weaklyNormalizing hw) (hpn.weaklyNormalizing hw) nc
  have haprof := Ω.profile_converts ((ContextTower.HasType.subst hp e.typed).weaklyNormalizing hw)
    ((ContextTower.HasType.subst hpn e.typed).weaklyNormalizing hw) (nc.subst e.images)
  have hnf := Expr.normalForm_converts ((ContextTower.HasType.subst hp e.typed).weaklyNormalizing hw)
    ((ContextTower.HasType.subst hpn e.typed).weaklyNormalizing hw) (nc.subst e.images)
  have hR := R_sorted_conversion Ω C hno hp hpn nc e
  have hRD := R_normalForm Ω C hno (.sorted hD) e
  rw [hR,normal_product_iff Ω C hno hC hpn hn (hprof ▸ hg) e (haprof ▸ ha) h,hnf]
  constructor
  · rintro ⟨ht,hbody⟩
    refine ⟨ht,?_⟩
    intro n hnr f he
    obtain ⟨g,heg,hfg⟩ := he.convert_domain hD hDN cD
    have hmem := hbody n (hRD ▸ hnr) g heg
    have heq := R_binder_conversion Ω C hno hD hDN cD hE hEN' cE e f g he heg hfg
    exact heq.symm ▸ hmem
  · rintro ⟨ht,hbody⟩
    refine ⟨ht,?_⟩
    intro n hnr g heg
    obtain ⟨f,hef,hgf⟩ := heg.convert_domain hDN hD (.symm _ _ cD)
    have hmem := hbody n (hRD.symm ▸ hnr) f hef
    have heq := R_binder_conversion Ω C hno hD hDN cD hE hEN' cE e f g hef heg ⟨hgf.1.symm,hgf.2.symm⟩
    exact heq ▸ hmem

theorem product_intro {Γ : List (Expr S)} {D E : Expr S} {s : S}
    (e : Environment (hw := hw) Ω C hno Γ) (hp : HasType P Γ (.pi D E) (.sort s))
    (hg : Profile P Γ (.pi D E) ∈ C) (ha : Ω.profile ((Expr.pi D E).subst e.images) ∈ C)
    (h : Expr S) (ht : h ∈ Candidates.Top Ω ((Expr.pi D E).subst e.images).normalForm)
    (hb : ∀ n, n ∈ R Ω C hno D e → ∀ f : Environment (hw := hw) Ω C hno (D :: Γ),
      e.Ext f n → Expr.app h n ∈ R Ω C hno E f) : h ∈ R Ω C hno (.pi D E) e :=
  (product_iff Ω C hno hC hp hg e ha h).mpr ⟨ht,hb⟩

end

section
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)
variable (hC : IsComponent (PrimaryEdge P) C)
include hC

theorem product_argument_active {Γ : List (Expr S)} {D E N : Expr S} {s : S}
    (hp : HasType P Γ (.pi D E) (.sort s)) (hN : HasType P Γ N D)
    (e : Environment (hw := hw) Ω C hno Γ)
    (hpC : Ω.profile ((Expr.pi D E).subst e.images) ∈ C)
    (hNC : Ω.profile ((E.instantiate N).subst e.images) ∈ C)
    (hD : Ω.profile (D.subst e.images) ∈ ObservationLayers P C) :
    ActiveLayer P C (Ω.profile (D.subst e.images)) := by
  obtain ⟨J,hf,hpath⟩ := Ω.frame_profiles hw (ContextTower.HasType.subst hp e.typed)
    (ContextTower.HasType.subst hN e.typed)
  have hJC : J ∈ C := hC.between (by simpa only [Expr.instantiate_subst] using hNC)
    hpC hpath.reach (.single (.codomain hf))
  exact ⟨_,⟨hD,J,hJC,_,hpC,hf⟩,.refl _⟩

theorem R_instantiate_normal {Γ : List (Expr S)} {D E N : Expr S} {a b c : S}
    (hD : HasType P Γ D (.sort a)) (hE : HasType P (D :: Γ) E (.sort b)) (hr : P.rule a b c)
    (n : TypingTree P Γ N D) (hnE : Normal E) (hnN : Normal N)
    (e : Environment (hw := hw) Ω C hno Γ)
    (hg : Profile P Γ (.pi D E) ∈ C) (ha : Ω.profile ((Expr.pi D E).subst e.images) ∈ C)
    (hNC : Ω.profile ((E.instantiate N).subst e.images) ∈ C) :
    R Ω C hno E (e.cons (ContextTower.HasType.subst n.typing e.typed)
      (preEvaluate Ω C hno n e).parameter (preEvaluate Ω C hno n e).parameter_fits) =
    R Ω C hno (E.instantiate N) e := by
  let q := TypingTree.ofTyping hE
  let f := e.cons (ContextTower.HasType.subst n.typing e.typed)
    (preEvaluate Ω C hno n e).parameter (preEvaluate Ω C hno n e).parameter_fits
  let ts := TypingTree.StoredSubstitution.single n
  let qt := q.subst hD.valid (Expr.single N) ts
  have hp := HasType.product hD hE hr
  have hrel : Relevant (P := P) C (D :: Γ) E := ⟨_,hg,.single (.codomain (Profile.triple hw hp))⟩
  have hrelN : Relevant (P := P) C Γ (E.instantiate N) :=
    ⟨_,hg,(Profile.instantiate_product_path hw hp n.typing).reach⟩
  have hgood : ReadGood Ω C q f.images := (normal_good Ω C hw hC q hnE f.images f.typed).2 b rfl hrel
  have hgN : ActiveLayer P C (Ω.profile (D.subst e.images)) → ValGood Ω C n e.images :=
    (normal_good Ω C hw hC n hnN e.images e.typed).1
  have hguard : SubstitutionGuard Ω C (D :: Γ) (Expr.single N) f.images :=
    single_guard Ω C e.images (product_argument_active Ω C hno hC hp n.typing e ha hNC)
  have hfi : f.images = Expr.consSub (N.subst e.images) e.images := by
    funext i; cases i <;> rfl
  have hgR := single_goodReplacement Ω C n e.images hgN
  have hgood' : ReadGood Ω C qt e.images := (goodness_subst Ω C hw q hD.valid (Expr.single N) ts
    e.images e.typed (by simpa only [Expr.comp_single,←hfi] using hguard) hgR).2
      (by simpa only [Expr.comp_single,←hfi] using hgood)
  have heval := (preEvaluate_subst Ω C hno q hD.valid (Expr.single N) ts f e
    (single_assigned Ω C hno n e) hguard).2 hgood
  exact (R_eq_read_normal Ω C hno hC q hnE hrel f).trans (heval.trans
    (R_eq_read_good Ω C hno hC qt hrelN e hgood').symm)

theorem specialization {Γ : List (Expr S)} {D E N : Expr S} {s : S}
    (e : Environment (hw := hw) Ω C hno Γ) (hp : HasType P Γ (.pi D E) (.sort s))
    (hN : HasType P Γ N D) (hg : Profile P Γ (.pi D E) ∈ C)
    (ha : Ω.profile ((Expr.pi D E).subst e.images) ∈ C) (h : Expr S)
    (hh : h ∈ R Ω C hno (.pi D E) e) (hn : N.subst e.images ∈ R Ω C hno D e) :
    Expr.app h (N.subst e.images) ∈ R Ω C hno (E.instantiate N) e := by
  obtain ⟨a,b,c,hD,hE,hr,_⟩ := hp.generation_pi
  have hNN := hN.normalForm hw
  let n := TypingTree.ofTyping hNN
  let pn := (preEvaluate Ω C hno n e).parameter
  have pp := (preEvaluate Ω C hno n e).parameter_fits
  let f := e.cons (ContextTower.HasType.subst hN e.typed) pn pp
  let g := e.cons (ContextTower.HasType.subst hNN e.typed) pn pp
  have hm := ((product_iff Ω C hno hC hp hg e ha h).mp hh).2 (N.subst e.images) hn f
    (e.cons_ext _ pn pp)
  have hnE := (Expr.normalForm_spec (hE.weaklyNormalizing hw)).2
  have hnN := (Expr.normalForm_spec (hN.weaklyNormalizing hw)).2
  have cE := (Expr.normalForm_spec (hE.weaklyNormalizing hw)).1.converts
  have cN := (Expr.normalForm_spec (hN.weaklyNormalizing hw)).1.converts
  have hp' : HasType P Γ (.pi D E.normalForm) (.sort c) := .product hD (hE.normalForm hw) hr
  have cP : Converts (.pi D E) (.pi D E.normalForm) := .pi (.refl _) cE
  have cT : Converts (E.instantiate N) (E.normalForm.instantiate N.normalForm) :=
    .trans _ _ _ (cE.subst (Expr.single N)) (cN.instantiate_right E.normalForm)
  have hT := hE.instantiate hN
  have hT' := (hE.normalForm hw).instantiate hNN
  have hRT := R_sorted_conversion Ω C hno hT hT' cT e
  by_cases htC : Ω.profile ((E.normalForm.instantiate N.normalForm).subst e.images) ∈ C
  · have hgg := Profile.converts (P := P) (Γ := Γ) (hp.weaklyNormalizing hw) (hp'.weaklyNormalizing hw) cP
    have haa := Ω.profile_converts ((ContextTower.HasType.subst hp e.typed).weaklyNormalizing hw)
      ((ContextTower.HasType.subst hp' e.typed).weaklyNormalizing hw) (cP.subst e.images)
    have hfg : f.Compatible g := by
      constructor
      · intro i hi
        cases i with
        | zero => exact cN.subst e.images
        | succ i => exact .refl _
      · intro i hi; cases i <;> rfl
    have hrE := (R_normalForm Ω C hno (.sorted hE) f).trans
      ((R_compatible Ω C hno hC (.sorted (hE.normalForm hw)) f g hfg).trans
      (R_instantiate_normal Ω C hno hC hD (hE.normalForm hw) hr n hnE hnN e (hgg ▸ hg) (haa ▸ ha) htC))
    exact hRT.symm ▸ (hrE ▸ hm)
  · have hmem := (R_candidate Ω C hno E f).upper hm
    have he : (E.subst f.images).normalForm = ((E.instantiate N).subst e.images).normalForm := by
      congr 1
      rw [← Expr.instantiate_subst,Expr.instantiate_liftSub]
      rfl
    have hnf := Expr.normalForm_converts ((ContextTower.HasType.subst hT e.typed).weaklyNormalizing hw)
      ((ContextTower.HasType.subst hT' e.typed).weaklyNormalizing hw) (cT.subst e.images)
    rw [hRT,R_outside Ω C hno _ e (.inr htC)]
    exact (hnf ▸ he ▸ hmem)

end

universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

/-- The actual observation interpretation, with arbitrary typed raw images and
all matching payload extensions. No component interface law is assumed. -/
noncomputable def componentInterface (hC : IsComponent (PrimaryEdge P) C) : ComponentInterface Ω hw C where
  Env := Environment (hw := hw) Ω C hno
  images := Environment.images
  typed := Environment.typed
  inhabit σ hσ := ⟨Environment.ofImages σ hσ,rfl⟩
  Ext := Environment.Ext
  ext_images he := he.1
  extend e _ _ hn := e.extend_exists hn
  R := R Ω C hno
  candidate e _ := R_candidate Ω C hno _ e
  conversion e ha hb hc := R_conversion Ω C hno ha hb hc e
  outside e _ ho := R_outside Ω C hno _ e ho
  weakening hd he hx := R_weakening Ω C hno he hd hx
  product_intro e hp hg ha h ht hb := product_intro Ω C hno hC e hp hg ha h ht hb
  specialization e hp hN hg ha h hh hn := specialization Ω C hno hC e hp hN hg ha h hh hn

end PureTypeSystem.ObservationValues

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_OneChild
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.OneChildInterpretation

section
universe u
open Classical Candidates
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) (C : Set (Set S))

abbrev Bits := Nat → Bool

def extendBit (θ : Bits) (b : Bool) : Bits
  | 0 => b
  | n+1 => θ n

def head : Expr S → Option Nat
  | .var n => some n
  | .app f _ => head f
  | _ => none

/-- Both choices are tested at each binder. Specialization will select the
extreme choice given by the unique internal support path. -/
noncomputable def eval (Γ : List (Expr S)) (A : Expr S) (σ : Nat → Expr S) (θ : Bits) : Set (Expr S) :=
  if Profile P Γ A ∈ C ∧ Ω.profile (A.subst σ) ∈ C then
    match A with
    | .pi D E => RawProduct Ω D E σ (eval Γ D σ θ)
        (fun n b => eval (D :: Γ) E (Expr.extend σ n) (extendBit θ b))
    | A => match head A with
      | none => Top Ω (A.subst σ).normalForm
      | some i => if θ i then Top Ω (A.subst σ).normalForm else Bottom Ω (A.subst σ).normalForm
  else Top Ω (A.subst σ).normalForm

@[simp] theorem head_rename (A : Expr S) (ρ : Nat → Nat) :
    head (A.rename ρ) = (head A).map ρ := by
  induction A with
  | app f n ihf ihn => exact ihf
  | var i => rfl
  | sort s => rfl
  | lam D m ihD ihm => rfl
  | pi D E ihD ihE => rfl

theorem head_subst {A : Expr S} {i : Nat} (hi : head A = some i) (σ : Nat → Expr S) :
    head (A.subst σ) = head (σ i) := by
  induction A with
  | var j => cases hi; rfl
  | app f n ihf ihn => exact ihf hi
  | sort s => cases hi
  | pi D E ihD ihE => cases hi
  | lam D m ihD ihm => cases hi

theorem head_beta {A B : Expr S} {i : Nat} (hi : head A = some i) (hr : Beta A B) :
    head B = some i := by
  induction hr with
  | head D m n => cases hi
  | app_left hr ih => exact ih hi
  | app_right hr ih => exact hi
  | lam_domain hr ih => cases hi
  | lam_body hr ih => cases hi
  | pi_domain hr ih => cases hi
  | pi_body hr ih => cases hi

theorem head_reduces {A B : Expr S} {i : Nat} (hi : head A = some i) (hr : Reduces A B) :
    head B = some i := by
  induction hr with
  | refl => exact hi
  | tail hr hs ih => exact head_beta ih hs

theorem head_normalForm {A : Expr S} {i : Nat} (hi : head A = some i) (hw : WeaklyNormalizing A) :
    head A.normalForm = some i := head_reduces hi (Expr.normalForm_spec hw).1

theorem eval_pi (Γ : List (Expr S)) (D E : Expr S) (σ : Nat → Expr S) (θ : Bits) :
    eval Ω C Γ (.pi D E) σ θ =
      if Profile P Γ (.pi D E) ∈ C ∧ Ω.profile ((Expr.pi D E).subst σ) ∈ C then
        RawProduct Ω D E σ (eval Ω C Γ D σ θ)
          (fun n b => eval Ω C (D :: Γ) E (Expr.extend σ n) (extendBit θ b))
      else Top Ω ((Expr.pi D E).subst σ).normalForm := rfl

theorem eval_head {Γ : List (Expr S)} {A : Expr S} {σ : Nat → Expr S} {θ : Bits} {i : Nat}
    (hg : Profile P Γ A ∈ C) (ha : Ω.profile (A.subst σ) ∈ C) (hi : head A = some i) :
    eval Ω C Γ A σ θ = if θ i then Top Ω (A.subst σ).normalForm else Bottom Ω (A.subst σ).normalForm := by
  cases A <;> simp only [eval,ite_eq_left (And.intro hg ha)]
  all_goals first | (cases hi <;> rfl) | (rw [hi])

theorem eval_sort (Γ : List (Expr S)) (s : S) (σ : Nat → Expr S) (θ : Bits) :
    eval Ω C Γ (.sort s) σ θ = Top Ω (.sort s) := by
  simp only [eval,head,ite_self,Expr.subst,Expr.normalForm_of_normal (Normal.sort s)]

variable (hw : SystemWeaklyNormalizing P)
include hw

theorem eval_candidate {Γ : List (Expr S)} {A : Expr S} {s : S}
    {σ : Nat → Expr S} (hA : HasType P Γ A (.sort s)) (hσ : Ω.TypedSubstitution Γ σ) (θ : Bits) :
    IsCandidate Ω (A.subst σ).normalForm (eval Ω C Γ A σ θ) := by
  induction A generalizing Γ s σ θ with
  | pi D E ihD ihE =>
    rw [eval]
    split
    · obtain ⟨a,b,c,hD,hE,_,_⟩ := hA.generation_pi
      have hX := ihD hD hσ θ
      apply rawProduct_candidate hw hA hσ hX
      intro n hn bit
      have hrawD := ContextTower.HasType.subst hD hσ
      have ht := (hX.upper hn).1.conversion hrawD
        (.symm _ _ (Expr.normalForm_spec (hrawD.weaklyNormalizing hw)).1.converts)
      exact ihE hE (hσ.cons ht) (extendBit θ bit)
    · exact top_candidate
  | var i =>
    simp only [eval,head]
    split
    · split <;> first | exact top_candidate | exact bottom_candidate
    · exact top_candidate
  | sort s => simp only [eval,head,ite_self]; exact top_candidate
  | lam D m ihD ihm => simp only [eval,head,ite_self]; exact top_candidate
  | app f n ihf ihn =>
    simp only [eval]
    split
    · cases hh : head (.app f n) with
      | none => exact top_candidate
      | some i =>
        change IsCandidate Ω (Expr.subst σ (.app f n)).normalForm
          (if θ i then Top Ω (Expr.subst σ (.app f n)).normalForm else Bottom Ω (Expr.subst σ (.app f n)).normalForm)
        split <;> first | exact top_candidate | exact bottom_candidate
    · exact top_candidate

omit hw in
theorem eval_outside {Γ : List (Expr S)} {A : Expr S} {σ : Nat → Expr S} {θ : Bits}
    (ho : Profile P Γ A ∉ C ∨ Ω.profile (A.subst σ) ∉ C) :
    eval Ω C Γ A σ θ = Top Ω (A.subst σ).normalForm := by
  have hn : ¬ (Profile P Γ A ∈ C ∧ Ω.profile (A.subst σ) ∈ C) :=
    fun h => ho.elim (fun hn => hn h.1) (fun hn => hn h.2)
  cases A <;> simp only [eval,ite_eq_right hn]

def dropSupport : Option (Nat × Bool) → Option (Nat × Bool)
  | some (0,_) => none
  | some (n+1,p) => some (n,p)
  | none => none

def flipSupport : Option (Nat × Bool) → Option (Nat × Bool) :=
  Option.map (fun (n,p) => (n,!p))

noncomputable def support (Γ : List (Expr S)) (A : Expr S) : Option (Nat × Bool) :=
  if Profile P Γ A ∈ C then
    match A with
    | .pi D E => if Profile P Γ D ∈ C then flipSupport (support Γ D)
        else dropSupport (support (D :: Γ) E)
    | A => (head A).map (fun i => (i,false))
  else none

structure Environment (Γ : List (Expr S)) where
  images : Nat → Expr S
  typed : Ω.TypedSubstitution Γ images
  bits : Bits

noncomputable def R {Γ : List (Expr S)} (A : Expr S) (e : Environment Ω Γ) : Set (Expr S) :=
  eval Ω C Γ A.normalForm e.images e.bits

theorem normal_subst_eq {Γ : List (Expr S)} {A : Expr S}
    (hA : Expected P Γ A) (e : Environment Ω Γ) :
    (A.normalForm.subst e.images).normalForm = (A.subst e.images).normalForm := by
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩
  · rw [Expr.normalForm_of_normal (Normal.sort s)]
  · exact Expr.normalForm_converts
      ((ContextTower.HasType.subst (hA.normalForm hw) e.typed).weaklyNormalizing hw)
      ((ContextTower.HasType.subst hA e.typed).weaklyNormalizing hw)
      (.symm _ _ ((Expr.normalForm_spec (hA.weaklyNormalizing hw)).1.converts.subst e.images))

theorem R_candidate {Γ : List (Expr S)} {A : Expr S} (hA : Expected P Γ A) (e : Environment Ω Γ) :
    IsCandidate Ω (A.subst e.images).normalForm (R Ω C A e) := by
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩
  · simp only [R,Expr.normalForm_of_normal (Normal.sort s),eval,head,ite_self]
    exact top_candidate
  · rw [← normal_subst_eq Ω hw (.sorted hA) e]
    exact eval_candidate Ω C hw (hA.normalForm hw) e.typed e.bits

theorem R_conversion {Γ : List (Expr S)} {A B : Expr S}
    (hA : Expected P Γ A) (hB : Expected P Γ B) (hc : Converts A B) (e : Environment Ω Γ) :
    R Ω C A e = R Ω C B e := by
  simp only [R,Expr.normalForm_converts (hA.wn hw) (hB.wn hw) hc]

end

section
universe u
open Classical Candidates
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) (C : Set (Set S))
variable (hw : SystemWeaklyNormalizing P)

theorem eval_recontext {Γ Δ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (hc : ContextEquivalent P Γ Δ)
    (σ : Nat → Expr S) (θ : Bits) : eval Ω C Γ A σ θ = eval Ω C Δ A σ θ := by
  induction A generalizing Γ Δ s σ θ with
  | pi D E ihD ihE =>
    obtain ⟨a,b,c,hD,hE,_,_⟩ := hA.generation_pi
    have hp : Profile P Γ (.pi D E) = Profile P Δ (.pi D E) := Set.ext (fun s => hc.typing _ _)
    rw [eval_pi,eval_pi,hp]
    congr 1
    apply congrArg₂ (RawProduct Ω D E σ) (ihD hD hc σ θ)
    funext n bit
    exact ihE hE (hc.cons hD) _ _
  | var i =>
    have hp : Profile P Γ (.var i) = Profile P Δ (.var i) := Set.ext (fun s => hc.typing _ _)
    simp only [eval,hp]
  | sort s => rw [eval_sort,eval_sort]
  | app f n ihf ihn =>
    have hp : Profile P Γ (.app f n) = Profile P Δ (.app f n) := Set.ext (fun s => hc.typing _ _)
    simp only [eval,hp]
  | lam D m ihD ihm => exact False.elim hA.lambda_cannot_have_sort_type

include hw in
theorem eval_rename {Γ Δ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (hΔ : ValidContext P Δ)
    (ρ : Nat → Nat) (hρ : TypingTree.DeclRenaming Γ Δ ρ)
    (σ τ : Nat → Expr S) (θ ψ : Bits) (hσ : τ ∘ ρ = σ) (hθ : ψ ∘ ρ = θ) :
    eval Ω C Γ A σ θ = eval Ω C Δ (A.rename ρ) τ ψ := by
  induction A generalizing Γ Δ s ρ σ τ θ ψ with
  | pi D E ihD ihE =>
    obtain ⟨a,b,c,hD,hE,_,_⟩ := hA.generation_pi
    have hp := Profile.rename hw hA hΔ ρ (hρ.typed hΔ)
    have he (M : Expr S) : (M.rename ρ).subst τ = M.subst σ := by rw [Expr.subst_rename,hσ]
    rw [eval_pi]
    change _ = eval Ω C Δ (.pi (D.rename ρ) (E.rename (Expr.liftRen ρ))) τ ψ
    rw [eval_pi]
    have hraw : (Expr.pi (D.rename ρ) (E.rename (Expr.liftRen ρ))).subst τ = (Expr.pi D E).subst σ := he (.pi D E)
    have hX := ihD hD hΔ ρ hρ σ τ θ ψ hσ hθ
    have hY : (fun n bit => eval Ω C (D :: Γ) E (Expr.extend σ n) (extendBit θ bit)) =
        (fun n bit => eval Ω C (D.rename ρ :: Δ) (E.rename (Expr.liftRen ρ))
          (Expr.extend τ n) (extendBit ψ bit)) := by
      funext n bit
      apply ihE hE (.cons hΔ (hD.rename hΔ ρ (hρ.typed hΔ))) _ (hρ.lift D)
      · funext i; cases i with
        | zero => rfl
        | succ i => exact congrFun hσ i
      · funext i; cases i with
        | zero => rfl
        | succ i => exact congrFun hθ i
    change Profile P Δ (Expr.pi (D.rename ρ) (E.rename (Expr.liftRen ρ))) = _ at hp
    rw [hp,hraw]
    congr 1
    unfold RawProduct
    rw [hraw,hX,hY]
  | sort s => rw [eval_sort,Expr.rename,eval_sort]
  | var i =>
    have hp := Profile.rename hw hA hΔ ρ (hρ.typed hΔ)
    have he : (.var (ρ i) : Expr S).subst τ = Expr.subst σ (.var i) := congrFun hσ i
    change Profile P Δ (.var (ρ i)) = _ at hp
    simp only [eval,Expr.rename,hp,he,head]
    rw [show ψ (ρ i) = θ i from congrFun hθ i]
  | lam D m ihD ihm => exact False.elim hA.lambda_cannot_have_sort_type
  | app f n ihf ihn =>
    have hp := Profile.rename hw hA hΔ ρ (hρ.typed hΔ)
    have he : ((Expr.app f n).rename ρ).subst τ = (Expr.app f n).subst σ := by rw [Expr.subst_rename,hσ]
    simp only [Expr.rename] at hp he ⊢
    simp only [eval,hp,he,head,head_rename]
    cases hh : head f with
    | none => rfl
    | some i => simp only [Option.map_some]; rw [show ψ (ρ i) = θ i from congrFun hθ i]

namespace Environment
variable {Ω}
def Ext {Γ : List (Expr S)} {D : Expr S} (e : Environment Ω Γ) (f : Environment Ω (D :: Γ)) (n : Expr S) : Prop :=
  f.images = Expr.extend e.images n ∧ ∀ i, f.bits (i+1) = e.bits i
end Environment

theorem R_sort {Γ : List (Expr S)} (s : S) (e : Environment Ω Γ) :
    R Ω C (.sort s) e = Top Ω (.sort s) := by
  rw [R,Expr.normalForm_of_normal (Normal.sort s),eval_sort]

include hw in
theorem R_weakening {Γ : List (Expr S)} {D A n : Expr S} {s : S}
    {e : Environment Ω Γ} {f : Environment Ω (D :: Γ)}
    (hD : HasType P Γ D (.sort s)) (hA : Expected P Γ A) (he : e.Ext f n) :
    R Ω C (A.rename Nat.succ) f = R Ω C A e := by
  rcases hA with ⟨a,rfl⟩ | ⟨a,hA⟩
  · exact (R_sort Ω C a f).trans (R_sort Ω C a e).symm
  · rw [R,R,Expr.normalForm_rename (hA.weaklyNormalizing hw)]
    symm
    apply eval_rename Ω C hw (hA.normalForm hw) (.cons hD.valid hD) Nat.succ (TypingTree.DeclRenaming.weaken D)
    · rw [he.1]; rfl
    · exact funext (fun i => he.2 i)

end

section
universe u
open Classical Candidates
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) (C : Set (Set S))
variable (hw : SystemWeaklyNormalizing P)
include hw

theorem normal_product {Γ : List (Expr S)} {D E : Expr S} {s : S}
    (hp : HasType P Γ (.pi D E) (.sort s)) (σ : Nat → Expr S)
    (hσ : Ω.TypedSubstitution Γ σ) (θ : Bits) :
    eval Ω C Γ (Expr.pi D E).normalForm σ θ =
      if Profile P Γ (.pi D E) ∈ C ∧ Ω.profile ((Expr.pi D E).subst σ) ∈ C then
        RawProduct Ω D E σ (eval Ω C Γ D.normalForm σ θ)
          (fun n b => eval Ω C (D :: Γ) E.normalForm (Expr.extend σ n) (extendBit θ b))
      else Top Ω ((Expr.pi D E).subst σ).normalForm := by
  obtain ⟨a,b,c,hD,hE,hr,_⟩ := hp.generation_pi
  have hDN := hD.normalForm hw
  have hEN := hE.normalForm hw
  have cD := (Expr.normalForm_spec (hD.weaklyNormalizing hw)).1.converts
  have cE := (Expr.normalForm_spec (hE.weaklyNormalizing hw)).1.converts
  let ctx := ContextEquivalent.head_conversion hD hDN cD
  have hEN' := (ctx.typing _ _).mp hEN
  have hpn : HasType P Γ (.pi D.normalForm E.normalForm) (.sort c) := .product hDN hEN' hr
  have nc := Converts.pi cD cE
  have he : Profile P Γ (.pi D E) = Profile P Γ (.pi D.normalForm E.normalForm) :=
    Profile.converts (hp.weaklyNormalizing hw) (hpn.weaklyNormalizing hw) nc
  have hrw := (ContextTower.HasType.subst hp hσ).weaklyNormalizing hw
  have hnw := (ContextTower.HasType.subst hpn hσ).weaklyNormalizing hw
  have hnf := Expr.normalForm_converts hrw hnw (nc.subst σ)
  have hae : Ω.profile ((Expr.pi D E).subst σ) = Ω.profile ((Expr.pi D.normalForm E.normalForm).subst σ) := by
    rw [←Ω.profile_normalForm ((Expr.pi D E).subst σ),←Ω.profile_normalForm ((Expr.pi D.normalForm E.normalForm).subst σ),hnf]
  rw [Expr.normalForm_pi (hD.weaklyNormalizing hw) (hE.weaklyNormalizing hw),eval_pi,←he,←hae]
  split
  · unfold RawProduct
    rw [←hnf]
    simp_rw [←eval_recontext Ω C hEN ctx]
  · exact congrArg (Top Ω) hnf.symm

theorem R_outside {Γ : List (Expr S)} {A : Expr S} (hA : Expected P Γ A)
    (e : Environment Ω Γ) (ho : Profile P Γ A ∉ C ∨ Ω.profile (A.subst e.images) ∉ C) :
    R Ω C A e = Top Ω (A.subst e.images).normalForm := by
  have hnf := normal_subst_eq Ω hw hA e
  rw [R,eval_outside Ω C,hnf]
  rcases ho with ho | ho
  · exact .inl (by rwa [Profile.normalForm])
  · exact .inr (by
      rw [←Ω.profile_normalForm (A.normalForm.subst e.images),hnf,Ω.profile_normalForm]
      exact ho)

theorem product_iff {Γ : List (Expr S)} {D E : Expr S} {s : S}
    (hp : HasType P Γ (.pi D E) (.sort s)) (hg : Profile P Γ (.pi D E) ∈ C)
    (e : Environment Ω Γ) (ha : Ω.profile ((Expr.pi D E).subst e.images) ∈ C) (h : Expr S) :
    h ∈ R Ω C (.pi D E) e ↔
      h ∈ Top Ω ((Expr.pi D E).subst e.images).normalForm ∧
      ∀ n, n ∈ R Ω C D e → ∀ f : Environment Ω (D :: Γ), e.Ext f n → Expr.app h n ∈ R Ω C E f := by
  rw [R,normal_product Ω C hw hp e.images e.typed e.bits,ite_eq_left ⟨hg,ha⟩]
  obtain ⟨a,b,c,hD,hE,_,_⟩ := hp.generation_pi
  constructor
  · rintro ⟨ht,hbody⟩
    refine ⟨ht,?_⟩
    intro n hn f he
    have hb : f.bits = extendBit e.bits (f.bits 0) := by
      funext i; cases i with
      | zero => rfl
      | succ i => exact he.2 i
    change Expr.app h n ∈ eval Ω C (D :: Γ) E.normalForm f.images f.bits
    rw [he.1,hb]
    exact hbody n hn (f.bits 0)
  · rintro ⟨ht,hbody⟩
    refine ⟨ht,?_⟩
    intro n hn bit
    have hrawD := ContextTower.HasType.subst hD e.typed
    have hnt := ((R_candidate Ω C hw (.sorted hD) e).upper hn).1.conversion hrawD
      (.symm _ _ (Expr.normalForm_spec (hrawD.weaklyNormalizing hw)).1.converts)
    let f : Environment Ω (D :: Γ) := ⟨Expr.extend e.images n,e.typed.cons hnt,extendBit e.bits bit⟩
    exact hbody n hn f ⟨rfl,fun _ => rfl⟩

end

section
universe u
open Classical
variable {S : Type u} {P : Specification S} (C : Set (Set S))

/-- Replaced supported heads are assigned the extremum appropriate to the
comparison direction and path parity. Unreplaced heads retain their bit. -/
def CompatibleBits (r : Option (Nat × Bool)) (dir : Bool) (σ : Nat → Expr S) (θ ψ : Bits) : Prop :=
  ∀ i p, r = some (i,p) → (∃ j, σ i = .var j ∧ θ i = ψ j) ∨ θ i = Bool.xor dir p

def Below {α : Type*} (dir : Bool) (X Y : Set α) : Prop := if dir then Y ⊆ X else X ⊆ Y

theorem support_outside {Γ : List (Expr S)} {A : Expr S} (h : Profile P Γ A ∉ C) :
    support (P := P) C Γ A = none := by cases A <;> simp only [support,ite_eq_right h]

theorem support_head {Γ : List (Expr S)} {A : Expr S} {i : Nat}
    (hg : Profile P Γ A ∈ C) (hi : head A = some i) : support (P := P) C Γ A = some (i,false) := by
  cases A <;> simp only [support,ite_eq_left hg]
  all_goals first | (cases hi <;> rfl) | (rw [hi]; rfl)

theorem bits_domain {Γ : List (Expr S)} {D E : Expr S} {dir : Bool}
    {σ : Nat → Expr S} {θ ψ : Bits} (hg : Profile P Γ (.pi D E) ∈ C)
    (hb : CompatibleBits (support (P := P) C Γ (.pi D E)) dir σ θ ψ) :
    CompatibleBits (support (P := P) C Γ D) (!dir) σ θ ψ := by
  intro i p hi
  by_cases hd : Profile P Γ D ∈ C
  · have hp : support (P := P) C Γ (.pi D E) = some (i,!p) := by
      rw [support,ite_eq_left hg,ite_eq_left hd,flipSupport,hi]; rfl
    rcases hb i (!p) hp with h | h
    · exact .inl h
    · right
      have he : Bool.xor dir (!p) = Bool.xor (!dir) p := by cases dir <;> cases p <;> rfl
      exact h.trans he
  · rw [support_outside C hd] at hi
    cases hi

theorem bits_body (hw : SystemWeaklyNormalizing P)
    (hno : ∀ {I J K}, ProfileTriple P I J K → I ∈ C → J ∈ C → K ∈ C → False)
    {Γ : List (Expr S)} {D E : Expr S} {s : S} {dir : Bool}
    {σ : Nat → Expr S} {θ ψ : Bits} (hp : HasType P Γ (.pi D E) (.sort s))
    (hg : Profile P Γ (.pi D E) ∈ C)
    (hb : CompatibleBits (support (P := P) C Γ (.pi D E)) dir σ θ ψ) (bit : Bool) :
    CompatibleBits (support (P := P) C (D :: Γ) E) dir (Expr.liftSub σ) (extendBit θ bit) (extendBit ψ bit) := by
  intro i p hi
  by_cases hd : Profile P Γ D ∈ C
  · have he : Profile P (D :: Γ) E ∉ C := fun he => hno (Profile.triple hw hp) hd he hg
    rw [support_outside C he] at hi
    cases hi
  · cases i with
    | zero => exact .inl ⟨0,rfl,rfl⟩
    | succ i =>
      have hh : support (P := P) C Γ (.pi D E) = some (i,p) := by
        rw [support,ite_eq_left hg,ite_eq_right hd,hi]; rfl
      rcases hb i p hh with ⟨j,hj,he⟩ | he
      · left
        exact ⟨j+1,by rw [Expr.liftSub_succ,hj]; rfl,he⟩
      · exact .inr he

noncomputable def chosenBit (Γ : List (Expr S)) (A : Expr S) : Bool :=
  match support (P := P) C Γ A with
  | some (0,p) => p
  | _ => true

theorem bits_single (Γ : List (Expr S)) (A N : Expr S) (θ : Bits) :
    CompatibleBits (support (P := P) C Γ A) false (Expr.single N) (extendBit θ (chosenBit (P := P) C Γ A)) θ := by
  intro i p hi
  cases i with
  | zero =>
    right
    simp only [extendBit,chosenBit,hi,Bool.false_xor]
  | succ i => exact .inl ⟨i,rfl,rfl⟩

end

section
universe u
open Classical Candidates
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) (C : Set (Set S))
variable (hw : SystemWeaklyNormalizing P)
include hw

theorem subst_profile_path {Γ Δ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (hΔ : ValidContext P Δ) (δ : Nat → Expr S)
    (hδ : TypedSubstitution P Γ Δ δ) :
    PositivePath (PrimaryEdge P) (Profile P Δ (A.subst δ)) (Profile P Γ A) :=
  Profile.inclusion_path
    (Profile.feasible ((hA.subst hΔ δ hδ).weaklyNormalizing hw) (Profile.nonempty_of_sorted hw (hA.subst hΔ δ hδ)))
    (Profile.feasible (hA.weaklyNormalizing hw) (Profile.nonempty_of_sorted hw hA))
    (Profile.growth hw (hA.weaklyNormalizing hw) hΔ δ hδ)

theorem neutral_compare {Γ Δ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (hΔ : ValidContext P Δ) (δ : Nat → Expr S)
    (hδ : TypedSubstitution P Γ Δ δ) (e : Environment Ω Δ) (θ : Bits) (dir : Bool) {i : Nat}
    (hi : head A = some i) (hg : Profile P Γ A ∈ C)
    (hp : Profile P Δ (A.subst δ) ∈ C)
    (ha : Ω.profile (A.subst (fun i => (δ i).subst e.images)) ∈ C)
    (hb : CompatibleBits (support (P := P) C Γ A) dir δ θ e.bits) :
    Below dir (eval Ω C Γ A (fun i => (δ i).subst e.images) θ) (R Ω C (A.subst δ) e) := by
  have ht := hA.subst hΔ δ hδ
  have hcomp : ((A.subst δ).subst e.images) = A.subst (fun i => (δ i).subst e.images) := Expr.subst_subst _ _ _
  have hc := R_candidate Ω C hw (.sorted ht) e
  rw [hcomp] at hc
  rw [eval_head Ω C hg ha hi]
  rcases hb i false (support_head C hg hi) with ⟨j,hj,hbit⟩ | hbit
  · have hhead : head (A.subst δ).normalForm = some j :=
      head_normalForm (by rw [head_subst hi,hj]; rfl) (ht.weaklyNormalizing hw)
    have hnf := normal_subst_eq Ω hw (.sorted ht) e
    have ha' : Ω.profile (((A.subst δ).normalForm).subst e.images) ∈ C := by
      rw [←Ω.profile_normalForm (((A.subst δ).normalForm).subst e.images),hnf,Ω.profile_normalForm,hcomp]
      exact ha
    have he : R Ω C (A.subst δ) e =
        if e.bits j then Top Ω (A.subst (fun i => (δ i).subst e.images)).normalForm
        else Bottom Ω (A.subst (fun i => (δ i).subst e.images)).normalForm := by
      rw [R,eval_head Ω C (by rwa [Profile.normalForm]) ha' hhead,hnf,hcomp]
    rw [he,hbit]
    cases dir <;> exact Set.Subset.rfl
  · simp only [Bool.xor_false] at hbit
    rw [hbit]
    cases dir with
    | false => exact bottom_le hc
    | true => exact hc.upper

omit hw in
@[simp] theorem head_apps (M : Expr S) (ns : List (Expr S)) : head (M.apps ns) = head M := by
  induction ns generalizing M with
  | nil => rfl
  | cons n ns ih => exact ih _

omit hw in
theorem normal_app_head {Γ : List (Expr S)} {f n : Expr S} {s : S}
    (ht : HasType P Γ (.app f n) (.sort s)) (hn : Normal (.app f n)) :
    ∃ i, head (.app f n) = some i := by
  have hneutral {M : Expr S} (h : Neutral M) : ∃ i, head M = some i := by
    induction h with
    | var i => exact ⟨i,rfl⟩
    | app h ih => exact ih
  obtain ⟨s,he⟩ | h | ⟨D,E,he⟩ := ht.sorted_normal_shape hn
  · cases he
  · exact hneutral h
  · cases he

variable (hC : IsComponent (PrimaryEdge P) C)
variable (hno : ∀ {I J K}, ProfileTriple P I J K → I ∈ C → J ∈ C → K ∈ C → False)
include hC hno hw

/-- The one-child polarity comparison at a generic normal type. The post-type
may have arbitrary newly exposed normal constructors. -/
theorem compare_subst {Γ Δ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (hN : Normal A)
    (hrel : ∃ K ∈ C, Reach (PrimaryEdge P) (Profile P Γ A) K)
    (hΔ : ValidContext P Δ) (δ : Nat → Expr S) (hδ : TypedSubstitution P Γ Δ δ)
    (e : Environment Ω Δ) (θ : Bits) (dir : Bool)
    (hb : CompatibleBits (support (P := P) C Γ A) dir δ θ e.bits) :
    Below dir (eval Ω C Γ A (fun i => (δ i).subst e.images) θ) (R Ω C (A.subst δ) e) := by
  induction A generalizing Γ Δ s δ θ dir with
  | var i =>
    have ht := hA.subst hΔ δ hδ
    have he : (((Expr.var i).subst δ).subst e.images) = (Expr.var i).subst (fun i => (δ i).subst e.images) := Expr.subst_subst _ _ _
    have hpa := Ω.profile_subst_path hw ht e.typed
    have hpg := subst_profile_path hw hA hΔ δ hδ
    by_cases ha : Ω.profile ((Expr.var i).subst (fun i => (δ i).subst e.images)) ∈ C
    swap
    · rw [eval_outside Ω C (.inr ha),R_outside Ω C hw (.sorted ht) e (.inr (by rwa [he])),he]
      cases dir <;> exact Set.Subset.rfl
    have hg : Profile P Γ (Expr.var i) ∈ C := by
      obtain ⟨K,hK,hpath⟩ := hrel
      rw [he] at hpa
      exact hC.between ha hK (hpa.reach.trans hpg.reach) hpath
    have hp : Profile P Δ ((Expr.var i).subst δ) ∈ C := by
      rw [he] at hpa
      exact hC.between ha hg hpa.reach hpg.reach
    exact neutral_compare Ω C hw hA hΔ δ hδ e θ dir rfl hg hp ha hb
  | app f n ihf ihn =>
    have ht := hA.subst hΔ δ hδ
    have he : (((Expr.app f n).subst δ).subst e.images) = (Expr.app f n).subst (fun i => (δ i).subst e.images) := Expr.subst_subst _ _ _
    have hpa := Ω.profile_subst_path hw ht e.typed
    have hpg := subst_profile_path hw hA hΔ δ hδ
    by_cases ha : Ω.profile ((Expr.app f n).subst (fun i => (δ i).subst e.images)) ∈ C
    swap
    · rw [eval_outside Ω C (.inr ha),R_outside Ω C hw (.sorted ht) e (.inr (by rwa [he])),he]
      cases dir <;> exact Set.Subset.rfl
    have hg : Profile P Γ (Expr.app f n) ∈ C := by
      obtain ⟨K,hK,hpath⟩ := hrel
      rw [he] at hpa
      exact hC.between ha hK (hpa.reach.trans hpg.reach) hpath
    have hp : Profile P Δ ((Expr.app f n).subst δ) ∈ C := by
      rw [he] at hpa
      exact hC.between ha hg hpa.reach hpg.reach

    obtain ⟨i,hi⟩ := normal_app_head hA hN
    exact neutral_compare Ω C hw hA hΔ δ hδ e θ dir hi hg hp ha hb
  | sort a =>
    have ht := hA.subst hΔ δ hδ
    have he : (((Expr.sort a).subst δ).subst e.images) = (Expr.sort a).subst (fun i => (δ i).subst e.images) := Expr.subst_subst _ _ _
    have hpa := Ω.profile_subst_path hw ht e.typed
    have hpg := subst_profile_path hw hA hΔ δ hδ
    by_cases ha : Ω.profile ((Expr.sort a).subst (fun i => (δ i).subst e.images)) ∈ C
    swap
    · rw [eval_outside Ω C (.inr ha),R_outside Ω C hw (.sorted ht) e (.inr (by rwa [he])),he]
      cases dir <;> exact Set.Subset.rfl
    have hg : Profile P Γ (Expr.sort a) ∈ C := by
      obtain ⟨K,hK,hpath⟩ := hrel
      rw [he] at hpa
      exact hC.between ha hK (hpa.reach.trans hpg.reach) hpath
    have hp : Profile P Δ ((Expr.sort a).subst δ) ∈ C := by
      rw [he] at hpa
      exact hC.between ha hg hpa.reach hpg.reach

    rw [eval_sort,Expr.subst,R_sort]
    cases dir <;> exact Set.Subset.rfl
  | lam D m ihD ihm =>
    have ht := hA.subst hΔ δ hδ
    have he : (((Expr.lam D m).subst δ).subst e.images) = (Expr.lam D m).subst (fun i => (δ i).subst e.images) := Expr.subst_subst _ _ _
    have hpa := Ω.profile_subst_path hw ht e.typed
    have hpg := subst_profile_path hw hA hΔ δ hδ
    by_cases ha : Ω.profile ((Expr.lam D m).subst (fun i => (δ i).subst e.images)) ∈ C
    swap
    · rw [eval_outside Ω C (.inr ha),R_outside Ω C hw (.sorted ht) e (.inr (by rwa [he])),he]
      cases dir <;> exact Set.Subset.rfl
    have hg : Profile P Γ (Expr.lam D m) ∈ C := by
      obtain ⟨K,hK,hpath⟩ := hrel
      rw [he] at hpa
      exact hC.between ha hK (hpa.reach.trans hpg.reach) hpath
    have hp : Profile P Δ ((Expr.lam D m).subst δ) ∈ C := by
      rw [he] at hpa
      exact hC.between ha hg hpa.reach hpg.reach
    exact False.elim hA.lambda_cannot_have_sort_type
  | pi D E ihD ihE =>
    have ht := hA.subst hΔ δ hδ
    have he : (((Expr.pi D E).subst δ).subst e.images) = (Expr.pi D E).subst (fun i => (δ i).subst e.images) := Expr.subst_subst _ _ _
    have hpa := Ω.profile_subst_path hw ht e.typed
    have hpg := subst_profile_path hw hA hΔ δ hδ
    by_cases ha : Ω.profile ((Expr.pi D E).subst (fun i => (δ i).subst e.images)) ∈ C
    swap
    · rw [eval_outside Ω C (.inr ha),R_outside Ω C hw (.sorted ht) e (.inr (by rwa [he])),he]
      cases dir <;> exact Set.Subset.rfl
    have hg : Profile P Γ (Expr.pi D E) ∈ C := by
      obtain ⟨K,hK,hpath⟩ := hrel
      rw [he] at hpa
      exact hC.between ha hK (hpa.reach.trans hpg.reach) hpath
    have hp : Profile P Δ ((Expr.pi D E).subst δ) ∈ C := by
      rw [he] at hpa
      exact hC.between ha hg hpa.reach hpg.reach

    obtain ⟨a,b,c,hD,hE,hr,_⟩ := hA.generation_pi
    have hDn := hN.pi_domain
    have hEn := hN.pi_body
    have tr := Profile.triple hw hA
    have relD : ∃ K ∈ C, Reach (PrimaryEdge P) (Profile P Γ D) K := ⟨_,hg,.single (.domain tr)⟩
    have relE : ∃ K ∈ C, Reach (PrimaryEdge P) (Profile P (D :: Γ) E) K := ⟨_,hg,.single (.codomain tr)⟩
    have hδD := hD.subst hΔ δ hδ
    have dom := ihD hD hDn relD hΔ δ hδ e θ (!dir) (bits_domain C hg hb)
    have body (n : Expr S) (hn : n ∈ R Ω C (D.subst δ) e) (bit : Bool) :
        Below dir (eval Ω C (D :: Γ) E (Expr.extend (fun i => (δ i).subst e.images) n) (extendBit θ bit))
          (eval Ω C (D.subst δ :: Δ) (E.subst (Expr.liftSub δ)).normalForm
            (Expr.extend e.images n) (extendBit e.bits bit)) := by
      have hrawD := ContextTower.HasType.subst hδD e.typed
      have hnt := ((R_candidate Ω C hw (.sorted hδD) e).upper hn).1.conversion hrawD
        (.symm _ _ (Expr.normalForm_spec (hrawD.weaklyNormalizing hw)).1.converts)
      let f : Environment Ω (D.subst δ :: Δ) := ⟨Expr.extend e.images n,e.typed.cons hnt,extendBit e.bits bit⟩
      have hbody := ihE hE hEn relE (.cons hΔ hδD) (Expr.liftSub δ) (hδ.lift hδD)
        f (extendBit θ bit) dir (bits_body C hw hno hA hg hb bit)
      have hei : (fun i => (Expr.liftSub δ i).subst f.images) = Expr.extend (fun i => (δ i).subst e.images) n := by
        funext i
        cases i with
        | zero => rfl
        | succ i => exact Expr.subst_raise_extend (δ i) n e.images
      rw [hei] at hbody
      exact hbody
    rw [eval_pi,ite_eq_left ⟨hg,ha⟩,R,Expr.subst,normal_product Ω C hw ht _ e.typed e.bits,ite_eq_left ⟨hp,by change Ω.profile (((Expr.pi D E).subst δ).subst e.images) ∈ C; rwa [he]⟩]
    change Below dir (RawProduct Ω D E _ _ _) (RawProduct Ω (D.subst δ) (E.subst (Expr.liftSub δ)) e.images _ _)
    have hraw : ((Expr.pi (D.subst δ) (E.subst (Expr.liftSub δ))).subst e.images).normalForm =
        ((Expr.pi D E).subst (fun i => (δ i).subst e.images)).normalForm := congrArg Expr.normalForm he
    cases dir with
    | false =>
      intro h hh
      refine ⟨hraw.symm ▸ hh.1,?_⟩
      intro n hn bit
      exact body n hn bit (hh.2 n (dom hn) bit)
    | true =>
      intro h hh
      refine ⟨hraw ▸ hh.1,?_⟩
      intro n hn bit
      exact body n (dom hn) bit (hh.2 n (dom hn) bit)

end

universe u
open Classical Candidates
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) (C : Set (Set S))
variable (hw : SystemWeaklyNormalizing P) (hC : IsComponent (PrimaryEdge P) C)
variable (hno : ∀ {I J K}, ProfileTriple P I J K → I ∈ C → J ∈ C → K ∈ C → False)
include hw hC hno

theorem specialization {Γ : List (Expr S)} {D E N : Expr S} {s : S}
    (e : Environment Ω Γ) (hp : HasType P Γ (.pi D E) (.sort s))
    (hN : HasType P Γ N D) (hg : Profile P Γ (.pi D E) ∈ C)
    (ha : Ω.profile ((Expr.pi D E).subst e.images) ∈ C) (h : Expr S)
    (hh : h ∈ R Ω C (.pi D E) e) (hn : N.subst e.images ∈ R Ω C D e) :
    Expr.app h (N.subst e.images) ∈ R Ω C (E.instantiate N) e := by
  obtain ⟨a,b,c,hD,hE,hr,_⟩ := hp.generation_pi
  let bit := chosenBit (P := P) C (D :: Γ) E.normalForm
  let f : Environment Ω (D :: Γ) := ⟨Expr.extend e.images (N.subst e.images),
    e.typed.cons (ContextTower.HasType.subst hN e.typed),extendBit e.bits bit⟩
  have hm := ((product_iff Ω C hw hp hg e ha h).mp hh).2 (N.subst e.images) hn f ⟨rfl,fun _ => rfl⟩
  have hrel : ∃ K ∈ C, Reach (PrimaryEdge P) (Profile P (D :: Γ) E.normalForm) K := by
    rw [Profile.normalForm]
    exact ⟨_,hg,.single (.codomain (Profile.triple hw hp))⟩
  have hc := compare_subst Ω C hw hC hno (hE.normalForm hw)
    (Expr.normalForm_spec (hE.weaklyNormalizing hw)).2 hrel hD.valid (Expr.single N)
    (TypedSubstitution.single hN) e f.bits false (bits_single C (D :: Γ) E.normalForm N e.bits)
  have he : (fun i => (Expr.single N i).subst e.images) = f.images := by
    funext i; cases i <;> rfl
  rw [he] at hc
  have hout := hc hm
  have ht := hE.instantiate hN
  have ht' := (hE.normalForm hw).instantiate hN
  have cE := (Expr.normalForm_spec (hE.weaklyNormalizing hw)).1.converts.subst (Expr.single N)
  exact (R_conversion Ω C hw (.sorted ht) (.sorted ht') cE e).symm ▸ hout

/-- One-child components need no relational exclusion: both fresh extremes
are tested, and polarity selects one of those tests at specialization. -/
noncomputable def componentInterface : ComponentInterface Ω hw C where
  Env := Environment Ω
  images := Environment.images
  typed := Environment.typed
  inhabit σ hσ := ⟨⟨σ,hσ,fun _ => false⟩,rfl⟩
  Ext := Environment.Ext
  ext_images he := he.1
  extend e _ n hn := ⟨⟨Expr.extend e.images n,e.typed.cons hn,extendBit e.bits false⟩,rfl,fun _ => rfl⟩
  R := R Ω C
  candidate e hA := R_candidate Ω C hw hA e
  conversion e ha hb hc := R_conversion Ω C hw ha hb hc e
  outside e ht ho := R_outside Ω C hw ht e ho
  weakening hd he hx := R_weakening Ω C hw hd he hx
  product_intro e hp hg ha h ht hb := (product_iff Ω C hw hp hg e ha h).mpr ⟨ht,hb⟩
  specialization e hp hN hg ha h hh hn := specialization Ω C hw hC hno e hp hN hg ha h hh hn

end PureTypeSystem.OneChildInterpretation

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Restriction
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate _root_.OAI.PureTypeSystem.instCountableExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem

universe u

namespace Expr

variable {S T U : Type u}

def mapSort (f : S → T) : Expr S → Expr T
  | var n => var n
  | sort s => sort (f s)
  | app M N => app (mapSort f M) (mapSort f N)
  | lam A M => lam (mapSort f A) (mapSort f M)
  | pi A B => pi (mapSort f A) (mapSort f B)

@[simp] theorem mapSort_id (M : Expr S) : M.mapSort id = M := by
  induction M <;> simp_all only [mapSort, id_eq]

@[simp] theorem mapSort_comp (M : Expr S) (f : S → T) (g : T → U) :
    (M.mapSort f).mapSort g = M.mapSort (g ∘ f) := by
  induction M <;> simp_all only [mapSort, Function.comp_apply]

@[simp] theorem mapSort_rename (M : Expr S) (f : S → T) (ρ : Nat → Nat) :
    (M.rename ρ).mapSort f = (M.mapSort f).rename ρ := by
  induction M generalizing ρ <;> simp_all only [mapSort, rename]

@[simp] theorem mapSort_liftSub (f : S → T) (σ : Nat → Expr S) :
    mapSort f ∘ liftSub σ = liftSub (mapSort f ∘ σ) := by
  funext n
  cases n <;> simp only [Function.comp_apply, liftSub, mapSort, mapSort_rename]

@[simp] theorem mapSort_subst (M : Expr S) (f : S → T) (σ : Nat → Expr S) :
    (M.subst σ).mapSort f = (M.mapSort f).subst (mapSort f ∘ σ) := by
  induction M generalizing σ <;>
    simp_all only [mapSort, subst, Function.comp_apply, mapSort_liftSub]

@[simp] theorem mapSort_single (f : S → T) (a : Expr S) :
    mapSort f ∘ single a = single (a.mapSort f) := by
  funext n
  cases n <;> rfl

@[simp] theorem mapSort_instantiate (b a : Expr S) (f : S → T) :
    (b.instantiate a).mapSort f = (b.mapSort f).instantiate (a.mapSort f) := by
  simp only [instantiate, mapSort_subst, mapSort_single]

end Expr

namespace Specification

variable {S : Type u}

def restrict (P : Specification S) (A : Finset (S × S)) (R : Finset (S × S × S)) :
    Specification S where
  axioms s t := P.axioms s t ∧ (s,t) ∈ A
  rule a b c := P.rule a b c ∧ (a,b,c) ∈ R

def on (P : Specification S) (D : Set S) : Specification D where
  axioms s t := P.axioms s.val t.val
  rule a b c := P.rule a.val b.val c.val

end Specification

end PureTypeSystem

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Signed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.SignedInterpretation

section
universe u
open Classical Candidates
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)
variable {C : Set (Set S)} (hC : IsComponent (PrimaryEdge P) C)
variable (hw : SystemWeaklyNormalizing P)
variable (hno : ∀ I ∈ C, ¬ SignedPath (PrimaryEdge P) I I true)

abbrev Vector := (T : Expr S) → SignedCandidate Ω T (hC.signing (Ω.profile T))

noncomputable def value (v : Vector Ω hC) (T : Expr S) : Set (Expr S) :=
  if Ω.profile T ∈ C then (v T).set else Top Ω T

theorem value_candidate (v : Vector Ω hC) (T : Expr S) :
    IsCandidate Ω T (value Ω hC v T) := by
  unfold value; split
  · exact (v T).candidate
  · exact top_candidate

theorem value_forward {v w : Vector Ω hC} (hv : v ≤ w) {T : Expr S}
    (hs : Ω.profile T ∈ C → hC.signing (Ω.profile T) = false) :
    value Ω hC v T ⊆ value Ω hC w T := by
  unfold value; split
  · have hh := (SignedCandidate.order (v T) (w T)).mp (hv T)
    simpa only [hs ‹_›,Bool.false_eq_true,ite_false, if_false] using hh
  · exact Set.Subset.rfl

theorem value_backward {v w : Vector Ω hC} (hv : v ≤ w) {T : Expr S}
    (hs : Ω.profile T ∈ C → hC.signing (Ω.profile T) = true) :
    value Ω hC w T ⊆ value Ω hC v T := by
  unfold value; split
  · have hh := (SignedCandidate.order (v T) (w T)).mp (hv T)
    simpa only [hs ‹_›,ite_true, if_true] using hh
  · exact Set.Subset.rfl

noncomputable def stepCandidate (v : Vector Ω hC) (T : Expr S) : Candidate Ω T :=
  match T with
  | .pi D E =>
    if Normal (.pi D E) ∧ (∃ s, Ω.HasType (.pi D E) (.sort s)) ∧ Ω.profile (.pi D E) ∈ C then
      ⟨ProductTest Ω D E (value Ω hC v D) (fun n => {value Ω hC v (E.instantiate n).normalForm}),
        productTest_candidate hw (value_candidate Ω hC v D).upper (by
          intro n _ X hX
          rcases Set.mem_singleton_iff.mp hX with rfl
          exact value_candidate Ω hC v _)⟩
    else ⟨Top Ω (.pi D E),top_candidate⟩
  | T => ⟨Top Ω T,top_candidate⟩

noncomputable def step (v : Vector Ω hC) : Vector Ω hC :=
  fun T => SignedCandidate.wrap (stepCandidate Ω hC hw v T)

include hno in
theorem step_monotone : Monotone (step Ω hC hw) := by
  intro v w hv T
  apply (SignedCandidate.order _ _).mpr
  simp only [step,SignedCandidate.set_wrap]
  cases T with
  | sort s => cases hC.signing (Ω.profile (.sort s)) <;> exact Set.Subset.rfl
  | var i => cases hC.signing (Ω.profile (.var i)) <;> exact Set.Subset.rfl
  | lam D E => cases hC.signing (Ω.profile (.lam D E)) <;> exact Set.Subset.rfl
  | app f n => cases hC.signing (Ω.profile (.app f n)) <;> exact Set.Subset.rfl
  | pi D E =>
    dsimp only [stepCandidate]
    by_cases H : Normal (.pi D E) ∧ (∃ s, Ω.HasType (.pi D E) (.sort s)) ∧ Ω.profile (.pi D E) ∈ C
    · simp only [ite_eq_left H]
      obtain ⟨hn,⟨s,ht⟩,hpC⟩ := H
      have hd : ∀ hD : Ω.profile D ∈ C,
          hC.signing (Ω.profile (.pi D E)) = Bool.xor (hC.signing (Ω.profile D)) true := by
        intro hD
        obtain ⟨a,b,c,hD',hE,hr,hconv⟩ := ht.choose_spec.generation_pi
        have hf := Profile.triple hw ht.choose_spec
        have hglob : ProfileTriple P (Ω.profile D)
            (Profile P (D.rename (Expr.reverseIndex ht.choose) :: Ω.context ht.choose)
              (E.rename (Expr.liftRen (Expr.reverseIndex ht.choose)))) (Ω.profile (.pi D E)) := by
          rw [Ω.profile_at hw hD',Ω.profile_at hw ht.choose_spec]
          exact hf
        exact hC.signing_cross hno hD hpC (.singleton (.domain hglob))
      have he : ∀ n, Ω.HasType n D → Ω.profile (E.instantiate n).normalForm ∈ C →
          hC.signing (Ω.profile (E.instantiate n).normalForm) = hC.signing (Ω.profile (.pi D E)) := by
        intro n hn hnc
        rw [Ω.profile_normalForm] at hnc ⊢
        simpa only [Bool.xor_false] using
          (hC.signing_cross hno hnc hpC (Ω.profile_instantiate_product_path hw ht hn).parity).symm
      have flip (a b : Bool) (h : a = Bool.xor b true) : b = !a := by
        cases a <;> cases b <;> cases h <;> rfl
      cases hs : hC.signing (Ω.profile (.pi D E)) with
      | false =>
        simp only [Bool.false_eq_true,ite_false, if_false]
        intro h hh
        refine ⟨hh.1,?_⟩
        intro n hn X hX
        rcases Set.mem_singleton_iff.mp hX with rfl
        have hn' : n ∈ value Ω hC v D := value_backward Ω hC hv (by
          intro hc
          simpa only [hs,Bool.not_false,Bool.not_true] using flip _ _ (hd hc)) hn
        have hout := hh.2 n hn' _ (Set.mem_singleton _)
        exact value_forward Ω hC hv (fun hc => (he n (value_candidate Ω hC w D |>.upper hn).1 hc).trans hs) hout
      | true =>
        simp only [ite_true, if_true]
        intro h hh
        refine ⟨hh.1,?_⟩
        intro n hn X hX
        rcases Set.mem_singleton_iff.mp hX with rfl
        have hn' : n ∈ value Ω hC w D := value_forward Ω hC hv (by
          intro hc
          simpa only [hs,Bool.not_false,Bool.not_true] using flip _ _ (hd hc)) hn
        have hout := hh.2 n hn' _ (Set.mem_singleton _)
        exact value_backward Ω hC hv (fun hc => (he n (value_candidate Ω hC v D |>.upper hn).1 hc).trans hs) hout
    · simp only [ite_eq_right H]
      cases hC.signing (Ω.profile (.pi D E)) <;> exact Set.Subset.rfl

noncomputable def operator : Vector Ω hC →o Vector Ω hC :=
  ⟨step Ω hC hw,step_monotone Ω hC hw hno⟩

noncomputable def fixed : Vector Ω hC := (operator Ω hC hw hno).lfp

noncomputable def actual (T : Expr S) : Set (Expr S) := value Ω hC (fixed Ω hC hw hno) T

theorem actual_candidate (T : Expr S) : IsCandidate Ω T (actual Ω hC hw hno T) :=
  value_candidate Ω hC _ T

theorem actual_outside {T : Expr S} (ho : Ω.profile T ∉ C) : actual Ω hC hw hno T = Top Ω T := by
  simp only [actual,value,ho,ite_false, if_false]

theorem actual_product {D E : Expr S} {s : S} (hn : Normal (.pi D E))
    (ht : Ω.HasType (.pi D E) (.sort s)) (hc : Ω.profile (.pi D E) ∈ C) :
    actual Ω hC hw hno (.pi D E) =
      ProductTest Ω D E (actual Ω hC hw hno D) (fun n => {actual Ω hC hw hno (E.instantiate n).normalForm}) := by
  have he := congrArg (fun v : Vector Ω hC => (v (.pi D E)).set) (operator Ω hC hw hno).map_lfp
  change (step Ω hC hw (fixed Ω hC hw hno) (.pi D E)).set = _ at he
  dsimp only [step,SignedCandidate.set_wrap,stepCandidate] at he
  rw [ite_eq_left (show Normal (.pi D E) ∧ (∃ s, Ω.HasType (.pi D E) (.sort s)) ∧
    Ω.profile (.pi D E) ∈ C from ⟨hn,⟨s,ht⟩,hc⟩)] at he
  simpa only [actual,value,hc,ite_true, if_true,SignedCandidate.set_wrap,fixed] using he.symm
end

universe u
open Classical Candidates
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)
variable {C : Set (Set S)} (hC : IsComponent (PrimaryEdge P) C)
variable (hw : SystemWeaklyNormalizing P)
variable (hno : ∀ I ∈ C, ¬ SignedPath (PrimaryEdge P) I I true)

abbrev Environment (Γ : List (Expr S)) := {σ : Nat → Expr S // Ω.TypedSubstitution Γ σ}

noncomputable def R {Γ : List (Expr S)} (A : Expr S) (e : Environment Ω Γ) : Set (Expr S) :=
  if Profile P Γ A ∈ C then actual Ω hC hw hno (A.subst e.val).normalForm
  else Top Ω (A.subst e.val).normalForm

theorem R_candidate {Γ : List (Expr S)} (A : Expr S) (e : Environment Ω Γ) :
    IsCandidate Ω (A.subst e.val).normalForm (R Ω hC hw hno A e) := by
  unfold R; split
  · exact actual_candidate Ω hC hw hno _
  · exact top_candidate

theorem R_outside {Γ : List (Expr S)} (A : Expr S) (e : Environment Ω Γ)
    (ho : Profile P Γ A ∉ C ∨ Ω.profile (A.subst e.val) ∉ C) :
    R Ω hC hw hno A e = Top Ω (A.subst e.val).normalForm := by
  unfold R; split
  · exact actual_outside Ω hC hw hno (by
      rw [Ω.profile_normalForm]; exact ho.resolve_left (not_not.mpr ‹_›))
  · rfl

theorem R_conversion {Γ : List (Expr S)} {A B : Expr S}
    (e : Environment Ω Γ) (hA : Expected P Γ A) (hB : Expected P Γ B) (hc : Converts A B) :
    R Ω hC hw hno A e = R Ω hC hw hno B e := by
  have hwa : WeaklyNormalizing A := by
    rcases hA with ⟨s,rfl⟩ | ⟨s,h⟩
    · exact ⟨_,.refl,Normal.sort s⟩
    · exact h.weaklyNormalizing hw
  have hwb : WeaklyNormalizing B := by
    rcases hB with ⟨s,rfl⟩ | ⟨s,h⟩
    · exact ⟨_,.refl,Normal.sort s⟩
    · exact h.weaklyNormalizing hw
  have hp := Profile.converts (P := P) (Γ := Γ) hwa hwb hc
  have hn := Expr.normalForm_converts (hA.subst_wn hw e.property) (hB.subst_wn hw e.property) (hc.subst e.val)
  simp only [R,hp,hn]

theorem actual_sort (s : S) : actual Ω hC hw hno (.sort s) = Top Ω (.sort s) := by
  by_cases hc : Ω.profile (.sort s) ∈ C
  · have he := congrArg (fun v : Vector Ω hC => (v (.sort s)).set) (operator Ω hC hw hno).map_lfp
    change (step Ω hC hw (fixed Ω hC hw hno) (.sort s)).set = _ at he
    simpa only [step,stepCandidate,SignedCandidate.set_wrap,actual,value,hc,ite_true, if_true,fixed] using he.symm
  · exact actual_outside Ω hC hw hno hc

theorem R_sort {Γ : List (Expr S)} (s : S) (e : Environment Ω Γ) :
    R Ω hC hw hno (.sort s) e = Top Ω (.sort s) := by
  simp only [R,Expr.subst,Expr.normalForm_of_normal (Normal.sort s),actual_sort,ite_self]

theorem R_weakening {Γ : List (Expr S)} {D A n : Expr S} {s : S}
    {e : Environment Ω Γ} {f : Environment Ω (D :: Γ)}
    (hD : HasType P Γ D (.sort s)) (hA : Expected P Γ A)
    (he : f.val = Expr.extend e.val n) :
    R Ω hC hw hno (A.rename Nat.succ) f = R Ω hC hw hno A e := by
  rcases hA with ⟨a,rfl⟩ | ⟨a,hA⟩
  · exact (R_sort Ω hC hw hno a f).trans (R_sort Ω hC hw hno a e).symm
  · simp only [R,Profile.weaken hw hA hD,he,Expr.subst_raise_extend]

theorem R_before {Γ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (e : Environment Ω Γ)
    (hp : ∃ K ∈ C, Reach (PrimaryEdge P) (Profile P Γ A) K) :
    R Ω hC hw hno A e = actual Ω hC hw hno (A.subst e.val).normalForm := by
  unfold R; split
  · rfl
  · rename_i hn
    refine (actual_outside Ω hC hw hno ?_).symm
    rw [Ω.profile_normalForm]
    intro ha
    obtain ⟨K,hK,hp⟩ := hp
    exact hn (hC.between ha hK (Ω.profile_subst_path hw hA e.property).reach hp)

/-- The actual fixed point tests precisely every raw argument; normalization of
its codomain commutes with this specialization by confluence. -/
theorem actual_raw_product {Γ : List (Expr S)} {D E : Expr S} {s : S}
    (hp : HasType P Γ (.pi D E) (.sort s)) (e : Environment Ω Γ)
    (ha : Ω.profile ((Expr.pi D E).subst e.val) ∈ C) (h : Expr S) :
    h ∈ actual Ω hC hw hno ((Expr.pi D E).subst e.val).normalForm ↔
    h ∈ Top Ω ((Expr.pi D E).subst e.val).normalForm ∧
      ∀ n, n ∈ actual Ω hC hw hno (D.subst e.val).normalForm →
        Expr.app h n ∈ actual Ω hC hw hno (E.subst (Expr.extend e.val n)).normalForm := by
  obtain ⟨a,b,c,hD,hE,_,_⟩ := hp.generation_pi
  have hraw := ContextTower.HasType.subst hp e.property
  have hwraw := hraw.weaklyNormalizing hw
  change WeaklyNormalizing (.pi (D.subst e.val) (E.subst (Expr.liftSub e.val))) at hwraw
  have hparts : WeaklyNormalizing (D.subst e.val) ∧
      WeaklyNormalizing (E.subst (Expr.liftSub e.val)) := by
    obtain ⟨normal, reduction, hnormal⟩ := hwraw
    obtain ⟨domain, body, rfl, hdomain, hbody⟩ := Reduces.pi_inv reduction
    exact ⟨⟨domain, hdomain, hnormal.pi_domain⟩, ⟨body, hbody, hnormal.pi_body⟩⟩
  have hnf := Expr.normalForm_pi hparts.1 hparts.2
  have hpN := hraw.normalForm hw
  change Ω.HasType (Expr.pi (D.subst e.val) (E.subst (Expr.liftSub e.val))).normalForm (.sort s) at hpN
  rw [hnf] at hpN
  have hNC : Ω.profile (.pi (D.subst e.val).normalForm (E.subst (Expr.liftSub e.val)).normalForm) ∈ C := by
    rw [← hnf,Ω.profile_normalForm]; exact ha
  have hnormal : Normal (.pi (D.subst e.val).normalForm (E.subst (Expr.liftSub e.val)).normalForm) :=
    .pi (Expr.normalForm_spec hparts.1).2 (Expr.normalForm_spec hparts.2).2
  have hbody (n : Expr S) (hn : n ∈ actual Ω hC hw hno (D.subst e.val).normalForm) :
      (E.subst (Expr.extend e.val n)).normalForm =
        ((E.subst (Expr.liftSub e.val)).normalForm.instantiate n).normalForm := by
    have hnt := (actual_candidate Ω hC hw hno _).upper hn |>.1
    have hrawD := ContextTower.HasType.subst hD e.property
    have hnr := hnt.conversion hrawD
      (.symm _ _ (Expr.normalForm_spec (hrawD.weaklyNormalizing hw)).1.converts)
    have htarget := ContextTower.HasType.subst hE (e.property.cons hnr)
    obtain ⟨t,ht⟩ := Ω.frame_target_sorted hpN hnt
    have hr : Reduces (E.subst (Expr.extend e.val n))
        ((E.subst (Expr.liftSub e.val)).normalForm.instantiate n) := by
      rw [← Expr.instantiate_extended]
      exact (Expr.normalForm_spec hparts.2).1.subst (Expr.single n)
    exact Expr.normalForm_converts (htarget.weaklyNormalizing hw) (ht.weaklyNormalizing hw) hr.converts
  change h ∈ actual Ω hC hw hno (Expr.pi (D.subst e.val) (E.subst (Expr.liftSub e.val))).normalForm ↔ _
  change h ∈ actual Ω hC hw hno (Expr.pi (D.subst e.val) (E.subst (Expr.liftSub e.val))).normalForm ↔
    h ∈ Top Ω (Expr.pi (D.subst e.val) (E.subst (Expr.liftSub e.val))).normalForm ∧ _
  rw [hnf,actual_product Ω hC hw hno hnormal hpN hNC]
  constructor
  · rintro ⟨ht,hb⟩
    refine ⟨ht,?_⟩
    intro n hn
    rw [hbody n hn]
    exact hb n hn _ (Set.mem_singleton _)
  · rintro ⟨ht,hb⟩
    refine ⟨ht,?_⟩
    intro n hn X hX
    rcases Set.mem_singleton_iff.mp hX with rfl
    rw [← hbody n hn]
    exact hb n hn

theorem product_intro {Γ : List (Expr S)} {D E : Expr S} {s : S}
    (e : Environment Ω Γ) (hp : HasType P Γ (.pi D E) (.sort s))
    (hg : Profile P Γ (.pi D E) ∈ C) (ha : Ω.profile ((Expr.pi D E).subst e.val) ∈ C)
    (h : Expr S) (ht : h ∈ Top Ω ((Expr.pi D E).subst e.val).normalForm)
    (hb : ∀ n, n ∈ R Ω hC hw hno D e → ∀ f : Environment Ω (D :: Γ),
      f.val = Expr.extend e.val n → Expr.app h n ∈ R Ω hC hw hno E f) :
    h ∈ R Ω hC hw hno (.pi D E) e := by
  obtain ⟨a,b,c,hD,hE,_,_⟩ := hp.generation_pi
  have hf := Profile.triple hw hp
  have hd := R_before Ω hC hw hno hD e ⟨_,hg,.single (.domain hf)⟩
  simp only [R,hg,ite_true, if_true]
  apply (actual_raw_product Ω hC hw hno hp e ha h).mpr
  refine ⟨ht,?_⟩
  intro n hn
  have hnt := (actual_candidate Ω hC hw hno _).upper hn |>.1
  have hrawD := ContextTower.HasType.subst hD e.property
  have hnr := hnt.conversion hrawD
    (.symm _ _ (Expr.normalForm_spec (hrawD.weaklyNormalizing hw)).1.converts)
  let f : Environment Ω (D :: Γ) := ⟨Expr.extend e.val n,e.property.cons hnr⟩
  have he := R_before Ω hC hw hno hE f ⟨_,hg,.single (.codomain hf)⟩
  have hh := hb n (hd.symm ▸ hn) f rfl
  exact he ▸ hh

theorem specialization {Γ : List (Expr S)} {D E N : Expr S} {s : S}
    (e : Environment Ω Γ) (hp : HasType P Γ (.pi D E) (.sort s)) (hN : HasType P Γ N D)
    (hg : Profile P Γ (.pi D E) ∈ C) (ha : Ω.profile ((Expr.pi D E).subst e.val) ∈ C)
    (h : Expr S) (hh : h ∈ R Ω hC hw hno (.pi D E) e)
    (hn : N.subst e.val ∈ R Ω hC hw hno D e) :
    Expr.app h (N.subst e.val) ∈ R Ω hC hw hno (E.instantiate N) e := by
  obtain ⟨a,b,c,hD,hE,_,_⟩ := hp.generation_pi
  have hf := Profile.triple hw hp
  have hd := R_before Ω hC hw hno hD e ⟨_,hg,.single (.domain hf)⟩
  have he := R_before Ω hC hw hno (hE.instantiate hN) e
    ⟨_,hg,(Profile.instantiate_product_path hw hp hN).reach⟩
  simp only [R,hg,ite_true, if_true] at hh
  have hout := (actual_raw_product Ω hC hw hno hp e ha h).mp hh |>.2 _ (hd ▸ hn)
  rw [he,← Expr.instantiate_subst,Expr.instantiate_extended]
  exact hout

noncomputable def componentInterface : ComponentInterface Ω hw C where
  Env := Environment Ω
  images := Subtype.val
  typed := Subtype.property
  inhabit σ hσ := ⟨⟨σ,hσ⟩,rfl⟩
  Ext e f n := f.val = Expr.extend e.val n
  ext_images he := he
  extend e _ _ hn := ⟨⟨_,e.property.cons hn⟩,rfl⟩
  R := R Ω hC hw hno
  candidate e _ := R_candidate Ω hC hw hno _ e
  conversion e ha hb hc := R_conversion Ω hC hw hno e ha hb hc
  outside e _ ho := R_outside Ω hC hw hno _ e ho
  weakening hd he hx := R_weakening Ω hC hw hno hd he hx
  product_intro e hp hg ha h ht hb := product_intro Ω hC hw hno e hp hg ha h ht hb
  specialization e hp hn hg ha h hh hN := specialization Ω hC hw hno e hp hn hg ha h hh hN

end PureTypeSystem.SignedInterpretation

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem

section
universe u
open Classical

/-- Relational exclusion for finite profile components. This internal
proposition is proved from weak normalization, not assumed in the main theorem. -/
def RelationalExclusion {S : Type u} (P : Specification S) : Prop :=
  ∀ C, IsComponent (PrimaryEdge P) C →
    (∃ I ∈ C, SignedPath (PrimaryEdge P) I I true) →
    (∃ I J K, ProfileTriple P I J K ∧ I ∈ C ∧ J ∈ C ∧ K ∈ C) →
    ¬ ForbiddenConfiguration P C

end

universe u
open Labelled
end PureTypeSystem

end OAI
end


