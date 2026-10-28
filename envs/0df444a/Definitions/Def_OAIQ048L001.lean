-- Prove2me | Definitions.Def_OAIQ048L001
-- name    : OAIQ048L001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T13:18:14.855924+00:00
-- url     : https://prove2.me/theorems/44d653e8-5302-4d35-9334-e89b36af55f7
-- title:
--   Definitions bundle OAIQ048L001 of the split of OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LogConcaveSampling.exact_source_main`, carved from OpenAI's openai/math development (OpenAI, *Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)*, OpenAI Math Release, September 26, 2026, result family 139, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 415 declarations of OpenAI's Lean: 253 definitions, 8 inductive types or structures, 23 instances and 131 theorems. The definitions and types are `OAI.LogConcaveSampling.CycleTrace.weight`, `OAI.LogConcaveSampling.FinitePicard.nodeLp`, `OAI.LogConcaveSampling.Frontier.Consistent`, `OAI.LogConcaveSampling.Frontier.History`, `OAI.LogConcaveSampling.Frontier.Incoming`, `OAI.LogConcaveSampling.Frontier.Live`, `OAI.LogConcaveSampling.Frontier.Outgoing`, `OAI.LogConcaveSampling.Frontier.Spectator`, `OAI.LogConcaveSampling.Frontier.graphStep`, `OAI.LogConcaveSampling.Frontier.historyEquiv`, `OAI.LogConcaveSampling.Frontier.historyOf`, `OAI.LogConcaveSampling.Frontier.inputCoordinates`, `OAI.LogConcaveSampling.Frontier.outputCoordinates`, `OAI.LogConcaveSampling.Frontier.splitIncoming`, `OAI.LogConcaveSampling.Frontier.splitOutgoing`, `OAI.LogConcaveSampling.GlobalODE.triangularEquiv`, `OAI.LogConcaveSampling.GlobalODE.variationalField`, `OAI.LogConcaveSampling.GraphSchedule.Adjacent`, `OAI.LogConcaveSampling.GraphSchedule.finDecEqC`, `OAI.LogConcaveSampling.GraphSchedule.finDecEqRUp`, `OAI.LogConcaveSampling.GraphSchedule.finDecEqRank`, `OAI.LogConcaveSampling.GraphSchedule.finDecEqTG`, `OAI.LogConcaveSampling.GraphSchedule.finDecEqTGI`, `OAI.LogConcaveSampling.GraphSchedule.finDecEqUp`, `OAI.LogConcaveSampling.GraphSchedule.length`, `OAI.LogConcaveSampling.GraphSchedule.rankExtend`, `OAI.LogConcaveSampling.GraphSchedule.stageEquiv`, `OAI.LogConcaveSampling.JetCalculus.TimeSmooth`, `OAI.LogConcaveSampling.JetCalculus.linearScore`, `OAI.LogConcaveSampling.JetCalculus.spaceBasis`, `OAI.LogConcaveSampling.LogPowerRate`, `OAI.LogConcaveSampling.LowerBound.BlockIndex`, `OAI.LogConcaveSampling.LowerBound.Rotations`, `OAI.LogConcaveSampling.LowerBound.blockCoefficient`, `OAI.LogConcaveSampling.LowerBound.blockLeft`, `OAI.LogConcaveSampling.LowerBound.blockMatrix`, `OAI.LogConcaveSampling.LowerBound.blockRight`, `OAI.LogConcaveSampling.LowerBound.blockTolerance`, `OAI.LogConcaveSampling.LowerBound.cosineAmplitude`, `OAI.LogConcaveSampling.LowerBound.cosineColumn` and 221 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `LogConcave_Analysis_CenteringPotential`, `LogConcave_Analysis_InterpolationHessianBudget`, `LogConcave_Analysis_InterpolationPotential`, `LogConcave_Complexity_CenteringStateBudget`, `LogConcave_Complexity_CenteringStateBudgetNonneg`, `LogConcave_Complexity_HarmonicCorrectionBudget`, `LogConcave_Complexity_KernelAnalyticNormalizedBudget`, `LogConcave_Complexity_OccurrenceBudget`, `LogConcave_Complexity_PolynomialBudget`, `LogConcave_Dynamics_Curve`, `LogConcave_Dynamics_TriangularEquiv`, `LogConcave_Dynamics_VariationalField`, `LogConcave_JetEstimates_ArrayMatrix`, `LogConcave_JetEstimates_ArrayRelabel`, `LogConcave_JetEstimates_Bound`, `LogConcave_JetEstimates_ContractLeftSplit`, `LogConcave_JetEstimates_Extend`, `LogConcave_JetEstimates_Extension`, `LogConcave_JetEstimates_ForestTensor`, `LogConcave_JetEstimates_JetMaterial`, `LogConcave_JetEstimates_JetRightSlice`, `LogConcave_JetEstimates_LogDegree`, `LogConcave_JetEstimates_Material`, `LogConcave_JetEstimates_MatrixArray`, `LogConcave_JetEstimates_ProperSplit`, `LogConcave_JetEstimates_ReindexedMatrix`, `LogConcave_JetEstimates_Slice`, `LogConcave_JetEstimates_SpaceBasis`, `LogConcave_JetEstimates_SplitBundle`, `LogConcave_JetEstimates_SplitIndex`, `LogConcave_JetEstimates_Squared`, `LogConcave_JetEstimates_TensorExpression`, `LogConcave_JetEstimates_TensorTerm`, `LogConcave_JetEstimates_WireStep`, `LogConcave_LowerBounds_DensityCoefficient`, `LogConcave_LowerBounds_LinearHistory`, `LogConcave_LowerBounds_Theta`, `LogConcave_LowerBounds_TranscriptRejection`, `LogConcave_LowerBounds_WeightedEvaluation`, `LogConcave_Numerics_CenteringStateQuadratureBudget`, `LogConcave_Numerics_ChainTaylor`, `LogConcave_Numerics_ChildNoise`, `LogConcave_Numerics_Cost`, `LogConcave_Numerics_Forward`, `LogConcave_Numerics_NodeLp`, `LogConcave_Numerics_ScalarPicard`, `LogConcave_Numerics_VelocityWorkCoefficient`, `LogConcave_OraclePrograms_CircuitD`, `LogConcave_OraclePrograms_MeanSize`, `LogConcave_OraclePrograms_Program`, `LogConcave_OraclePrograms_RoutineKind`, `LogConcave_OraclePrograms_Shape`, `LogConcave_OraclePrograms_TerminalMean`, `LogConcave_Sampling_AnalyticBase`, `LogConcave_Sampling_AngleNodes`, `LogConcave_Sampling_CenteringVelocityInterpolationRms`, `LogConcave_Sampling_ChangingChain`, `LogConcave_Sampling_ClosedFieldMean`, `LogConcave_Sampling_ConditionalSlotEmbedding`, `LogConcave_Sampling_CoordinateRank`, `LogConcave_Sampling_Correlation`, `LogConcave_Sampling_FDerivTimePartial`, `LogConcave_Sampling_FinSnocSlots`, `LogConcave_Sampling_IdentityOutputEmbedding`, `LogConcave_Sampling_InterpolationResidual`, `LogConcave_Sampling_Jet`, `LogConcave_Sampling_JointSpace`, `LogConcave_Sampling_JointU`, `LogConcave_Sampling_KernelTransportAction`, `LogConcave_Sampling_MaterialScalar`, `LogConcave_Sampling_MatrixColor`, `LogConcave_Sampling_MeanMaterialVector`, `LogConcave_Sampling_MixingEnvelope`, `LogConcave_Sampling_NoiseKernel`, `LogConcave_Sampling_NormalizedDirection`, `LogConcave_Sampling_NormalizedScoreMajorant`, `LogConcave_Sampling_NormalizedTensor`, `LogConcave_Sampling_NormalizedTensorMajorantScale`, `LogConcave_Sampling_NumericalLayerCount`, `LogConcave_Sampling_NumericalScalars`, `LogConcave_Sampling_PolynomialGrowth`, `LogConcave_Sampling_ProbabilityNodes`, `LogConcave_Sampling_ProbabilityNormalizedTerm`, `LogConcave_Sampling_ProbabilityVelocity`, `LogConcave_Sampling_Reindex`, `LogConcave_Sampling_SampleCorrelation`, `LogConcave_Sampling_ScoreSlots`, `LogConcave_Sampling_SmoothTimeLocalization`, `LogConcave_Sampling_SpatialTensor`, `LogConcave_Sampling_SpatialTensorContinuous`, `LogConcave_Sampling_StateLaw`, `LogConcave_Sampling_TapeSnocEquiv`, `LogConcave_Sampling_TensorGrad`, `LogConcave_Sampling_TensorVector`, `LogConcave_Sampling_TerminalTransportConstant`, `LogConcave_Sampling_TiltedExpectation`, `LogConcave_Sampling_TopScale`, `LogConcave_Sampling_TransportCorrectionMajorant`, `LogConcave_Sampling_UnitUniform`, `LogConcave_TensorGraphs_Chain`, `LogConcave_TensorGraphs_History`, `LogConcave_TensorGraphs_IncidentMatrix`, `LogConcave_TensorGraphs_Live`, `LogConcave_TensorGraphs_RankEquiv`, `LogConcave_TensorGraphs_Vertex`.
--
--   **Imports.** It imports the published bundle `Def_LogConcaveQuery`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ048L002` and `OAIQ048L003`.
-- source:
--   OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 139; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Subpolynomial-query-complexity-for-well-conditioned-log-concave-sampling-September-26-2026/article.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_LogConcaveQuery

section
-- module Solutions.OAIQ048_LC.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h

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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_Curve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.GlobalODE
open Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {a b : ℝ} {f : ℝ → E → E} {K : ℝ≥0}
  (hL : ∀ t∈Icc a b,LipschitzWith K (f t))

lemma right_deriv {α : ℝ → E}
    (hd : ∀ t∈Icc a b, HasDerivWithinAt α (f t (α t)) (Icc a b) t)
    (t : ℝ) (ht : t∈Ico a b) : HasDerivWithinAt α (f t (α t)) (Ici t) t := by
  apply (hd t ⟨ht.1,ht.2.le⟩).mono_of_mem_nhdsWithin
  exact inter_mem (Filter.mem_of_superset self_mem_nhdsWithin (Ici_subset_Ici.mpr ht.1))
    (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds ht.2))

include hL in

theorem trajectory_dist_right {α β : ℝ → E}
    (hα : ContinuousOn α (Icc a b))
    (hdα : ∀ t∈Icc a b,HasDerivWithinAt α (f t (α t)) (Icc a b) t)
    (hβ : ContinuousOn β (Icc a b))
    (hdβ : ∀ t∈Icc a b,HasDerivWithinAt β (f t (β t)) (Icc a b) t)
    (t : ℝ) (ht : t∈Icc a b) :
    dist (α t) (β t) ≤ dist (α a) (β a)*Real.exp ((K:ℝ)*(t-a)) := by
  exact dist_le_of_trajectories_ODE_of_mem (s:=fun _ => univ)
    (fun t ht => (hL t ⟨ht.1,ht.2.le⟩).lipschitzOnWith) hα
    (right_deriv hdα) (fun _ _ => mem_univ _) hβ (right_deriv hdβ)
    (fun _ _ => mem_univ _) le_rfl t ht

end LogConcaveSampling.GlobalODE
namespace LogConcaveSampling.GlobalODE
open Set Function
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {a b : ℝ} {f : ℝ → E → E} {K : ℝ≥0}
  (hL : ∀ t∈Icc a b,LipschitzWith K (f t))

include hL in
lemma trajectory_dist_left {α β : ℝ → E}
    (hα : ContinuousOn α (Icc a b))
    (hdα : ∀ t∈Icc a b,HasDerivWithinAt α (f t (α t)) (Icc a b) t)
    (hβ : ContinuousOn β (Icc a b))
    (hdβ : ∀ t∈Icc a b,HasDerivWithinAt β (f t (β t)) (Icc a b) t)
    (t : ℝ) (ht : t∈Icc a b) :
    dist (α t) (β t) ≤ dist (α b) (β b)*Real.exp ((K:ℝ)*(b-t)) := by
  have hmap : MapsTo Neg.neg (Icc (-b) (-a)) (Icc a b) :=
    fun _ h => ⟨le_neg.mp h.2,neg_le.mp h.1⟩
  have hL' : ∀ t∈Icc (-b) (-a),LipschitzWith K (fun z => -f (-t) z) := by
    intro u hu
    exact (hL (-u) (hmap hu)).neg
  have hd {γ : ℝ → E}
      (hh : ∀ t∈Icc a b,HasDerivWithinAt γ (f t (γ t)) (Icc a b) t)
      (u : ℝ) (hu : u∈Icc (-b) (-a)) :
      HasDerivWithinAt (γ ∘ Neg.neg) (-f (-u) (γ (-u))) (Icc (-b) (-a)) u := by
    convert! HasFDerivWithinAt.comp_hasDerivWithinAt u (hh (-u) (hmap hu))
      (hasDerivAt_neg u).hasDerivWithinAt hmap using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hh := trajectory_dist_right hL' (hα.comp continuousOn_neg hmap) (hd hdα)
    (hβ.comp continuousOn_neg hmap) (hd hdβ) (-t) ⟨neg_le_neg ht.2,neg_le_neg ht.1⟩
  simpa only [Function.comp_apply,neg_neg,sub_neg_eq_add,neg_add_eq_sub] using hh

include hL in
lemma trajectory_dist {α β : ℝ → E}
    (hα : ContinuousOn α (Icc a b))
    (hdα : ∀ t∈Icc a b,HasDerivWithinAt α (f t (α t)) (Icc a b) t)
    (hβ : ContinuousOn β (Icc a b))
    (hdβ : ∀ t∈Icc a b,HasDerivWithinAt β (f t (β t)) (Icc a b) t)
    (s t : Icc a b) :
    dist (α t) (β t) ≤ dist (α s) (β s)*Real.exp ((K:ℝ)*|(t:ℝ)-(s:ℝ)|) := by
  by_cases hst : (s:ℝ)≤t
  · have hsub : Icc (s:ℝ) b ⊆ Icc a b := Icc_subset_Icc_left s.2.1
    have hh := trajectory_dist_right (fun u hu => hL u (hsub hu)) (hα.mono hsub)
      (fun u hu => (hdα u (hsub hu)).mono hsub) (hβ.mono hsub)
      (fun u hu => (hdβ u (hsub hu)).mono hsub) t ⟨hst,t.2.2⟩
    simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using hh
  · have hts : (t:ℝ) ≤ s := (lt_of_not_ge hst).le
    have hsub : Icc a (s:ℝ) ⊆ Icc a b := Icc_subset_Icc_right s.2.2
    have hh := trajectory_dist_left (fun u hu => hL u (hsub hu)) (hα.mono hsub)
      (fun u hu => (hdα u (hsub hu)).mono hsub) (hβ.mono hsub)
      (fun u hu => (hdβ u (hsub hu)).mono hsub) t ⟨t.2.1,hts⟩
    simpa only [abs_of_nonpos (sub_nonpos.mpr hts),neg_sub] using hh

end LogConcaveSampling.GlobalODE
namespace LogConcaveSampling.GlobalODE
open Set Function
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (s : Icc a b) {A : ℝ → E →L[ℝ] E} (hA : Continuous A)
    {K : ℝ≥0} (hK : ∀ t∈Icc a b,‖A t‖≤K)

omit [CompleteSpace E] in
include hK in
lemma linear_field_lipschitz (t : ℝ) (ht : t∈Icc a b) :
    LipschitzWith K (fun J : E →L[ℝ] E => (A t).comp J) := by
  apply LipschitzWith.of_dist_le_mul
  intro J L
  rw [dist_eq_norm,←ContinuousLinearMap.comp_sub,dist_eq_norm]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right (hK t ht) (norm_nonneg _))

end LogConcaveSampling.GlobalODE
namespace LogConcaveSampling.GlobalODE
open Set Function Metric
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {f : ℝ → E → E} {D : ℝ → E → E →L[ℝ] E}

lemma uniform_taylor_compact (hD : Continuous (uncurry D))
    (hf : ∀ t z,HasFDerivAt (f t) (D t z) z) (a b R ε : ℝ) (hε : 0<ε) :
    ∃ δ>0,∀ t∈Icc a b,∀ x : E,‖x‖≤R → ∀ v : E,‖v‖<δ →
      ‖f t (x+v)-f t x-D t x v‖≤ε*‖v‖ := by
  let S : Set (ℝ × E) := Icc a b ×ˢ closedBall (0:E) (R+1)
  have hS : IsCompact S := isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (hS.uniformContinuousOn_of_continuous hD.continuousOn) ε hε
  refine ⟨min 1 δ,lt_min zero_lt_one hδ,fun t ht x hx v hv => ?_⟩
  have hv1 : ‖v‖<1 := lt_of_lt_of_le hv (min_le_left _ _)
  have hvδ : ‖v‖<δ := lt_of_lt_of_le hv (min_le_right _ _)
  have hxin : (t,x)∈S := ⟨ht,by simpa [mem_closedBall,dist_zero_right] using (by linarith : ‖x‖≤R+1)⟩
  have hbound : ∀ z∈closedBall x ‖v‖,‖D t z-D t x‖≤ε := by
    intro z hz
    have hzx : ‖z-x‖≤‖v‖ := by simpa only [mem_closedBall,dist_eq_norm] using hz
    have hzin : (t,z)∈S := by
      refine ⟨ht,?_⟩
      simp only [mem_closedBall,dist_zero_right]
      have hn : ‖z‖≤‖z-x‖+‖x‖ := by simpa [add_comm] using norm_le_insert' z x
      linarith
    have hdist : dist (t,z) (t,x)<δ := by
      simp only [dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,norm_zero]
      exact max_lt hδ (hzx.trans_lt hvδ)
    simpa only [dist_eq_norm,uncurry_apply_pair] using (hclose (t,z) hzin (t,x) hxin hdist).le
  have hm := (convex_closedBall x ‖v‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => ((hf t z).sub (D t x).hasFDerivAt).hasFDerivWithinAt)
    hbound (mem_closedBall_self (norm_nonneg v))
    (show x+v∈closedBall x ‖v‖ by simp [mem_closedBall,dist_eq_norm])
  have he : (f t (x+v)-D t x (x+v))-(f t x-D t x x)=
      f t (x+v)-f t x-D t x v := by rw [map_add]; abel
  simpa only [Pi.sub_apply,he,add_sub_cancel_left] using hm
end LogConcaveSampling.GlobalODE
namespace LogConcaveSampling.GlobalODE
open Set Function Filter Metric
open scoped Topology

lemma gronwallBound_zero_linear (K ε t : ℝ) :
    gronwallBound 0 K ε t=ε*gronwallBound 0 K 1 t := by
  unfold gronwallBound
  split_ifs <;> ring

end LogConcaveSampling.GlobalODE

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_FDerivTimePartial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open Set Filter Metric Function
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma hasFDerivAt_of_time_partial {f g : ℝ → E → F} {s : Set (ℝ × E)}
    (hs : IsOpen s) {t : ℝ} {x : E} (hp : (t,x)∈s)
    (hg : ContinuousAt (uncurry g) (t,x))
    (ht : ∀ p∈s,HasDerivAt (fun u => f u p.2) (g p.1 p.2) p.1)
    {D : E →L[ℝ] F} (hx : HasFDerivAt (f t) D x) :
    HasFDerivAt (uncurry f)
      (((ContinuousLinearMap.fst ℝ ℝ E).smulRight (g t x))+
        D.comp (ContinuousLinearMap.snd ℝ ℝ E)) (t,x) := by
  apply HasFDerivAt.of_isLittleO
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hgε : ∀ᶠ q in 𝓝 (t,x),q∈s ∧ ‖g q.1 q.2-g t x‖<ε/2 := by
    filter_upwards [hs.mem_nhds hp,(Metric.tendsto_nhds.mp hg) (ε/2) (by positivity)] with q hq hq'
    exact ⟨hq,by simpa [dist_eq_norm,Function.uncurry] using hq'⟩
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hgε
  have hxε := (Asymptotics.isLittleO_iff.mp hx.isLittleO) (by positivity : 0<ε/2)
  filter_upwards [Metric.ball_mem_nhds (t,x) hδ,
    (continuous_snd.tendsto (t,x)) hxε] with q hq hqx
  have hqt : |q.1-t|<δ := lt_of_le_of_lt (le_max_left _ _) (by
    simpa [mem_ball,dist_eq_norm,Prod.norm_def,Real.norm_eq_abs] using hq)
  have hqxδ : ‖q.2-x‖<δ := lt_of_le_of_lt (le_max_right _ _) (by
    simpa [mem_ball,dist_eq_norm,Prod.norm_def,Real.norm_eq_abs] using hq)
  have hc (u : ℝ) (hu : u∈closedBall t |q.1-t|) :
      (u,q.2)∈s ∧ ‖g u q.2-g t x‖<ε/2 := by
    apply hball
    have hu' : |u-t|≤|q.1-t| := by simpa [mem_closedBall,dist_eq_norm,Real.norm_eq_abs] using hu
    simpa [mem_ball,dist_eq_norm,Prod.norm_def,Real.norm_eq_abs] using
      (max_lt (hu'.trans_lt hqt) hqxδ)
  have hd (u : ℝ) (hu : u∈closedBall t |q.1-t|) :
      HasFDerivWithinAt (fun v => f v q.2-v •g t x)
        ((1 : ℝ →L[ℝ] ℝ).smulRight (g u q.2-g t x))
        (closedBall t |q.1-t|) u := by
    convert! ((ht (u,q.2) (hc u hu).1).sub
      ((hasDerivAt_id u).smul_const (g t x))).hasFDerivAt.hasFDerivWithinAt using 1
    all_goals try with_reducible_and_instances rfl
    ext
    simp
  have htime := (convex_closedBall t |q.1-t|).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hd (fun u hu => by simpa using (hc u hu).2.le)
    (mem_closedBall_self (abs_nonneg _))
    (show q.1∈closedBall t |q.1-t| by simp [mem_closedBall,dist_eq_norm,Real.norm_eq_abs])
  have htime' : ‖f q.1 q.2-f t q.2-(q.1-t) •g t x‖≤(ε/2)*|q.1-t| := by
    have he : f q.1 q.2-f t q.2-(q.1-t) •g t x=
        f q.1 q.2-q.1 •g t x-(f t q.2-t •g t x) := by rw [sub_smul]; abel
    simpa only [he,Real.norm_eq_abs] using htime
  have he : f q.1 q.2-f t x-((q.1-t) •g t x+D (q.2-x))=
      (f q.1 q.2-f t q.2-(q.1-t) •g t x)+(f t q.2-f t x-D (q.2-x)) := by abel
  change ‖f q.1 q.2-f t x-((q.1-t) •g t x+D (q.2-x))‖≤ε*‖q-(t,x)‖
  rw [he]
  apply (norm_add_le _ _).trans
  apply (add_le_add htime' hqx).trans
  change ε/2*|q.1-t|+ε/2*‖q.2-x‖≤ε*max |q.1-t| ‖q.2-x‖
  have he0 : 0≤ε/2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (le_max_left |q.1-t| ‖q.2-x‖) he0,
    mul_le_mul_of_nonneg_left (le_max_right |q.1-t| ‖q.2-x‖) he0]
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_TriangularEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.GlobalODE
open Set Function Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def triangularEquiv (v : E) (J : E ≃L[ℝ] E) : (ℝ × E) ≃L[ℝ] (ℝ × E) where
  toLinearEquiv :=
    { toFun := fun p => (p.1,p.1 •v+J p.2)
      invFun := fun p => (p.1,J.symm (p.2-p.1 •v))
      left_inv := fun p => by simp
      right_inv := fun p => by simp
      map_add' := fun p q => by simp [add_smul]; abel
      map_smul' := fun c p => by simp [smul_add,smul_smul] }
  continuous_toFun := continuous_fst.prodMk
    ((continuous_fst.smul continuous_const).add (J.continuous.comp continuous_snd))
  continuous_invFun := continuous_fst.prodMk
    (J.symm.continuous.comp (continuous_snd.sub (continuous_fst.smul continuous_const)))

end LogConcaveSampling.GlobalODE

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_PolynomialGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
namespace LogConcaveSampling
open scoped RealInnerProductSpace

def tiltedIntegral {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Point d → ℝ) (h : Point d → E) (θ : Point d) : E :=
  ∫ z, Real.exp (inner ℝ θ z-H z) • h z

section
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def tiltDerivativeIntegrand (h : Point d → E) (z : Point d) : Point d →L[ℝ] E :=
  (innerSL ℝ z).smulRight (h z)

lemma continuous_tiltDerivativeIntegrand {h : Point d → E} (hh : Continuous h) :
    Continuous (tiltDerivativeIntegrand h) := by
  exact isBoundedBilinearMap_smulRight.continuous.comp
    ((innerSL ℝ).continuous.prodMk hh)

end
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_UnitUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
@[fun_prop] lemma measurable_fin_snoc {X : Type*} [MeasurableSpace X] (n : ℕ) :
    Measurable (fun p : (Fin n → X) × X => Fin.snoc (α := fun _ : Fin (n+1) => X) p.1 p.2) := by
  apply Measurable.of_eval
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using (measurable_snd : Measurable (Prod.snd : (Fin n → X) × X → X))
  · simp only [Fin.snoc_castSucc]
    fun_prop

end LogConcaveSampling

namespace LogConcaveSampling
open ProbabilityTheory

def unitUniform : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance instIsProbabilityMeasureRealUnitUniform : IsProbabilityMeasure unitUniform := by
  constructor
  simp [unitUniform]

variable {E : Type*} [MeasurableSpace E]

def acceptanceEvent (a : E → ℝ) : Set (E × ℝ) := {p | p.2 ≤ a p.1}

def rejectionPick (a : E → ℝ) (fallback : E) : (n : ℕ) → (Fin n → E × ℝ) → E
  | 0, _ => fallback
  | n+1, tape =>
      if (tape (Fin.last n)).2 ≤ a (tape (Fin.last n)).1 then (tape (Fin.last n)).1
      else rejectionPick a fallback n (fun i => tape i.castSucc)

@[fun_prop] lemma measurable_rejectionPick {a : E → ℝ} (ha : Measurable a) (fallback : E) (n : ℕ) :
    Measurable (rejectionPick a fallback n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      apply Measurable.ite
      · exact measurableSet_le ((measurable_pi_apply (Fin.last n)).snd)
          (ha.comp ((measurable_pi_apply (Fin.last n)).fst))
      · exact (measurable_pi_apply (Fin.last n)).fst
      · exact ih.comp (Measurable.of_eval fun index => measurable_pi_apply index.castSucc)

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_Bound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
namespace TensorEnergy
open scoped BigOperators

variable {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]

lemma dot_sq (u v : I → ℝ) :
    (∑ i, u i*v i)^2 ≤ (∑ i, (u i)^2)*(∑ i, (v i)^2) :=
  Finset.sum_mul_sq_le_sq_mul_sq _ _ _

universe u v w

end TensorEnergy
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TiltedExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
namespace LogConcaveSampling
open scoped RealInnerProductSpace

def tiltedExpectation {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Point d → ℝ) (h : Point d → E) (θ : Point d) : E :=
  (tiltedIntegral H (fun _ => (1:ℝ)) θ)⁻¹ • tiltedIntegral H h θ

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_InterpolationPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

lemma integral_scaled_affine_add {d : ℕ} {μ : Measure (Point d)} [IsProbabilityMeasure μ]
    {h : Point d → Point d} (hi : Integrable (fun z => z) μ) (hh : Integrable h μ)
    (c r : ℝ) (y : Point d) :
    (∫ z,c • (z-y)+r • h z ∂μ)=c • ((∫ z,z ∂μ)-y)+r • ∫ z,h z ∂μ := by
  have hi₁ : Integrable (fun z => c • (z-y)) μ := (hi.sub (integrable_const y)).smul c
  have hi₂ : Integrable (fun z => r • h z) μ := hh.smul r
  rw [integral_add hi₁ hi₂,integral_smul,integral_smul,
    integral_sub hi (integrable_const y),integral_const,probReal_univ,one_smul]

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_Extension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.TensorEnergy
open scoped BigOperators

variable {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]

noncomputable def zeroExtension (e : K ↪ I) (v : K → ℝ) (i : I) : ℝ := by
  classical
  exact ∑ k, if e k=i then v k else 0

omit [Fintype I] in
lemma zeroExtension_apply (e : K ↪ I) (v : K → ℝ) (k : K) :
    zeroExtension e v (e k)=v k := by
  classical
  simp [zeroExtension,e.injective.eq_iff]

lemma dot_zeroExtension (e : K ↪ I) (v : K → ℝ) (g : I → ℝ) :
    (∑ i, g i*zeroExtension e v i)=∑ k,g (e k)*v k := by
  classical
  simp only [zeroExtension,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  simp [mul_ite]

lemma energy_zeroExtension (e : K ↪ I) (v : K → ℝ) :
    (∑ i, (zeroExtension e v i)^2)=∑ k,(v k)^2 := by
  simp only [pow_two]
  rw [dot_zeroExtension]
  simp only [zeroExtension_apply]

end LogConcaveSampling.TensorEnergy

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ConditionalSlotEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

def conditionalSlotEmbedding {ι : Type*} (d : ℕ) (s : ι → Bool) :
    (ι → Fin d) ↪ (ι → Fin d ⊕ Fin d) where
  toFun a i := if s i then Sum.inr (a i) else Sum.inl (a i)
  inj' := by
    intro a c h
    funext i
    have hi := congrFun h i
    cases hs : s i <;> simpa [hs] using hi

end LogConcaveSampling

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

lemma normalized_energy_factor {a : ℝ} (ha : a≠0) (B : ℝ) {j k : ℕ}
    (hj : 0<j) (hk : 0<k) :
    ((a^(j+k-1))⁻¹)^2*(B*a)^(j+k)=B^(j+k)/(a^(j+k-2)) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  have h1 : j.succ+k.succ-1=j+k+1 := by omega
  have h2 : j.succ+k.succ-2=j+k := by omega
  have h3 : j.succ+k.succ=(j+k)+2 := by omega
  rw [h1,h2,h3,mul_pow]
  simp only [pow_add,pow_one,pow_two]
  field_simp

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_MaterialScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators RealInnerProductSpace

lemma covariance_third_diagonal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {g h : Ω → ℝ} (hg : MemLp g 2 μ) (hh : MemLp h 2 μ)
    (hgg : MemLp (fun z => (g z)^2) 2 μ) (hgh : MemLp (fun z => g z*h z) 2 μ) :
    cov[g,(fun z => g z*h z);μ]-cov[g,g;μ]*(∫z,h z ∂μ)-
      (∫z,g z ∂μ)*cov[g,h;μ]=
      cov[(fun z => (g z)^2),h;μ]-2*(∫z,g z ∂μ)*cov[g,h;μ] := by
  rw [covariance_eq_sub hg hgh,covariance_eq_sub hg hg,
    covariance_eq_sub hg hh,covariance_eq_sub hgg hh]
  simp only [Pi.mul_apply,pow_two,←mul_assoc]
  ring

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_ProperSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped BigOperators Classical Matrix.Norms.L2Operator

universe u
variable {S : Type u} [Fintype S] {d : ℕ}

def ProperSplit (S : Type u) :=
  {p : S → Bool // (∃s,p s=true) ∧ (∃s,p s=false)}
instance instFintypeProperSplit : Fintype (ProperSplit S) := inferInstanceAs (Fintype {_p : S → Bool // _})

def InSlots (p : ProperSplit S) := {s : S // p.val s=true}
def OutSlots (p : ProperSplit S) := {s : S // ¬p.val s=true}
instance instFintypeInSlots (p : ProperSplit S) : Fintype (InSlots p) := inferInstanceAs (Fintype {_s : S // _})
instance instFintypeOutSlots (p : ProperSplit S) : Fintype (OutSlots p) := inferInstanceAs (Fintype {_s : S // _})
instance instNonemptyInSlots (p : ProperSplit S) : Nonempty (InSlots p) := by
  obtain ⟨s,hs⟩ := p.property.1
  exact ⟨s,hs⟩
instance instNonemptyOutSlots (p : ProperSplit S) : Nonempty (OutSlots p) := by
  obtain ⟨s,hs⟩ := p.property.2
  exact ⟨s,by simp [hs]⟩

def splitEquiv (p : ProperSplit S) : S ≃ InSlots p ⊕ OutSlots p :=
  (Equiv.sumCompl (fun s => p.val s=true)).symm

def splitMatrix (T : (S → Fin d) → ℝ) (p : ProperSplit S) :
    Matrix (OutSlots p → Fin d) (InSlots p → Fin d) ℝ :=
  fun o i => T (fun s => Sum.elim i o (splitEquiv p s))

def splitEnvelope (T : (S → Fin d) → ℝ) : ℝ :=
  ∑p : ProperSplit S, ‖splitMatrix T p‖

section arbitrary
variable {I O : Type u} [Fintype I] [Fintype O] [Nonempty I] [Nonempty O]

def properOfEquiv (e : S ≃ I ⊕ O) : ProperSplit S :=
  ⟨fun s => (e s).isLeft, by
    constructor
    · obtain ⟨i⟩ := ‹Nonempty I›
      exact ⟨e.symm (Sum.inl i),by simp⟩
    · obtain ⟨o⟩ := ‹Nonempty O›
      exact ⟨e.symm (Sum.inr o),by simp⟩⟩

def leftOfEquiv (e : S ≃ I ⊕ O) : I ≃ InSlots (properOfEquiv e) where
  toFun i := ⟨e.symm (Sum.inl i),by simp [properOfEquiv]⟩
  invFun s := (e s.val).getLeft s.property
  left_inv i := by simp
  right_inv s := by
    apply Subtype.ext
    apply e.injective
    simp only [Equiv.apply_symm_apply]
    exact Sum.inl_getLeft _ _

def rightOfEquiv (e : S ≃ I ⊕ O) : O ≃ OutSlots (properOfEquiv e) where
  toFun o := ⟨e.symm (Sum.inr o),by simp [properOfEquiv]⟩
  invFun s := (e s.val).getRight (by simpa [properOfEquiv] using s.property)
  left_inv o := by simp
  right_inv s := by
    apply Subtype.ext
    apply e.injective
    simp only [Equiv.apply_symm_apply]
    exact Sum.inr_getRight _ _

omit [Fintype S] [Fintype I] [Fintype O] in
lemma splitEquiv_ofEquiv (e : S ≃ I ⊕ O) (s : S) :
    splitEquiv (properOfEquiv e) s =
      Sum.map (leftOfEquiv e) (rightOfEquiv e) (e s) := by
  apply (splitEquiv (properOfEquiv e)).symm.injective
  simp only [Equiv.symm_apply_apply]
  cases h : e s with
  | inl i =>
    have he : e.symm (Sum.inl i)=s := e.symm_apply_eq.mpr h.symm
    change s=e.symm (Sum.inl i)
    exact he.symm
  | inr o =>
    have he : e.symm (Sum.inr o)=s := e.symm_apply_eq.mpr h.symm
    change s=e.symm (Sum.inr o)
    exact he.symm

end arbitrary

end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_WireStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.TensorEnergy
open scoped BigOperators

def wireStep {I O S X Y : Type*} [DecidableEq S]
    (A : O → I → ℝ) (ei : X ≃ I×S) (eo : Y ≃ O×S) : Y → X → ℝ :=
  fun y x => A (eo y).1 (ei x).1 * if (eo y).2=(ei x).2 then 1 else 0

def circuit {D : ℕ → Type*} [∀k,Fintype (D k)] [DecidableEq (D 0)]
    (A : ∀k,D (k+1) → D k → ℝ) : ∀n,D n → D 0 → ℝ
  | 0 => fun i j => if i=j then 1 else 0
  | n+1 => fun i j => ∑k,A n i k*circuit A n k j

end LogConcaveSampling.TensorEnergy
namespace LogConcaveSampling.TensorEnergy
open scoped BigOperators Classical

variable {D : ℕ → Type*} [∀k,Fintype (D k)] [DecidableEq (D 0)]

abbrev Path (n : ℕ) := ∀k : Fin (n+1),D k.val

def pathWeight (A : ∀k,D (k+1) → D k → ℝ) (n : ℕ) (h : Path (D:=D) n) : ℝ :=
  ∏k : Fin n,A k.val (h k.succ) (h k.castSucc)

end LogConcaveSampling.TensorEnergy

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_ContractLeftSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators

universe u
variable {Ai Ao Bi Bo : Type u} [Fintype Ai] [Fintype Ao] [Fintype Bi] [Fintype Bo] {d : ℕ}

def contractLeftSplit : ((Ai ⊕ Ao) ⊕ Unit) ≃ (Ai ⊕ Unit) ⊕ Ao where
  toFun := Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr) (Sum.inl ∘ Sum.inr)
  invFun := Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr) (Sum.inl ∘ Sum.inr)
  left_inv s := by rcases s with (s|s)|s <;> rfl
  right_inv s := by rcases s with (s|s)|s <;> rfl

def contractRightSplit : ((Bi ⊕ Bo) ⊕ Unit) ≃ Bi ⊕ (Unit ⊕ Bo) where
  toFun := Sum.elim (Sum.elim Sum.inl (Sum.inr ∘ Sum.inr)) (Sum.inr ∘ Sum.inl)
  invFun := Sum.elim (Sum.inl ∘ Sum.inl) (Sum.elim Sum.inr (Sum.inl ∘ Sum.inr))
  left_inv s := by rcases s with (s|s)|s <;> rfl
  right_inv s := by rcases s with s|(s|s) <;> rfl

def appendCoordinate (I : Type u) : (I → Fin d) × Fin d ≃ (I ⊕ Unit → Fin d) :=
  ((Equiv.refl _).prodCongr (Equiv.funUnique Unit (Fin d)).symm).trans
    (Equiv.sumArrowEquivProdArrow I Unit (Fin d)).symm

def prependCoordinate (O : Type u) : Fin d × (O → Fin d) ≃ (Unit ⊕ O → Fin d) :=
  (((Equiv.funUnique Unit (Fin d)).symm).prodCongr (Equiv.refl _)).trans
    (Equiv.sumArrowEquivProdArrow Unit O (Fin d)).symm

def singleContract {S T : Type u}
    (A : (S ⊕ Unit → Fin d) → ℝ) (B : (T ⊕ Unit → Fin d) → ℝ) :
    (S ⊕ T → Fin d) → ℝ := fun c =>
  ∑z : Fin d,A (Sum.elim (fun s => c (Sum.inl s)) (fun _ => z))*
    B (Sum.elim (fun t => c (Sum.inr t)) (fun _ => z))

section partition
variable {S T : Type u} [Fintype S] [Fintype T]
local instance leftInDec (p : S ⊕ T → Bool) : DecidableEq {s : S // p (Sum.inl s)=true} := Classical.decEq _
local instance leftOutDec (p : S ⊕ T → Bool) : DecidableEq {s : S // ¬p (Sum.inl s)=true} := Classical.decEq _
local instance rightInDec (p : S ⊕ T → Bool) : DecidableEq {t : T // p (Sum.inr t)=true} := Classical.decEq _
local instance rightOutDec (p : S ⊕ T → Bool) : DecidableEq {t : T // ¬p (Sum.inr t)=true} := Classical.decEq _

def partEquiv (p : S → Bool) : S ≃ {s // p s=true} ⊕ {s // ¬p s=true} :=
  (Equiv.sumCompl (fun s => p s=true)).symm

def outputCoords (p : ProperSplit (S ⊕ T)) :
    (OutSlots p → Fin d) ≃
      ({s : S // ¬p.val (Sum.inl s)=true} → Fin d) ×
      ({t : T // ¬p.val (Sum.inr t)=true} → Fin d) :=
  (Equiv.arrowCongr Equiv.subtypeSum (Equiv.refl (Fin d))).trans
    (Equiv.sumArrowEquivProdArrow _ _ (Fin d))

def inputCoords (p : ProperSplit (S ⊕ T)) :
    (InSlots p → Fin d) ≃
      ({s : S // p.val (Sum.inl s)=true} → Fin d) ×
      ({t : T // p.val (Sum.inr t)=true} → Fin d) :=
  (Equiv.arrowCongr Equiv.subtypeSum (Equiv.refl (Fin d))).trans
    (Equiv.sumArrowEquivProdArrow _ _ (Fin d))

omit [Fintype S] [Fintype T] in
lemma splitOrientation [Nonempty S] [Nonempty T] (p : ProperSplit (S ⊕ T)) :
    (Nonempty {s : S // ¬p.val (Sum.inl s)=true} ∧
      Nonempty {t : T // p.val (Sum.inr t)=true}) ∨
    (Nonempty {s : S // p.val (Sum.inl s)=true} ∧
      Nonempty {t : T // ¬p.val (Sum.inr t)=true}) := by
  by_cases hs : Nonempty {s : S // ¬p.val (Sum.inl s)=true}
  · by_cases ht : Nonempty {t : T // p.val (Sum.inr t)=true}
    · exact Or.inl ⟨hs,ht⟩
    · right
      constructor
      · obtain ⟨s,h⟩ := p.property.1
        cases s with
        | inl s => exact ⟨s,h⟩
        | inr t => exact (ht ⟨t,h⟩).elim
      · obtain ⟨t⟩ := ‹Nonempty T›
        exact ⟨t,fun h => ht ⟨t,h⟩⟩
  · right
    constructor
    · obtain ⟨s⟩ := ‹Nonempty S›
      exact ⟨s,by by_contra h; exact hs ⟨s,h⟩⟩
    · obtain ⟨s,h⟩ := p.property.2
      cases s with
      | inl s => exact (hs ⟨s,by simp [h]⟩).elim
      | inr t => exact ⟨t,by simp [h]⟩

omit [Fintype S] [Fintype T] in
lemma part_colors_left (p : ProperSplit (S ⊕ T))
    (o : OutSlots p → Fin d) (i : InSlots p → Fin d) (s : S) :
    Sum.elim (inputCoords p i).1 (outputCoords p o).1
        (partEquiv (fun s : S => p.val (Sum.inl s)) s) =
      Sum.elim i o (splitEquiv p (Sum.inl s)) := by
  change Sum.elim (fun x : {s : S // p.val (Sum.inl s)=true} => i ⟨Sum.inl x.val,x.property⟩)
      (fun x : {s : S // ¬p.val (Sum.inl s)=true} => o ⟨Sum.inl x.val,x.property⟩)
      (if h : p.val (Sum.inl s)=true then Sum.inl ⟨s,h⟩ else Sum.inr ⟨s,h⟩) =
    Sum.elim i o (if h : p.val (Sum.inl s)=true
      then Sum.inl ⟨Sum.inl s,h⟩ else Sum.inr ⟨Sum.inl s,h⟩)
  split <;> rfl

omit [Fintype S] [Fintype T] in
lemma part_colors_right (p : ProperSplit (S ⊕ T))
    (o : OutSlots p → Fin d) (i : InSlots p → Fin d) (t : T) :
    Sum.elim (inputCoords p i).2 (outputCoords p o).2
        (partEquiv (fun t : T => p.val (Sum.inr t)) t) =
      Sum.elim i o (splitEquiv p (Sum.inr t)) := by
  change Sum.elim (fun x : {t : T // p.val (Sum.inr t)=true} => i ⟨Sum.inr x.val,x.property⟩)
      (fun x : {t : T // ¬p.val (Sum.inr t)=true} => o ⟨Sum.inr x.val,x.property⟩)
      (if h : p.val (Sum.inr t)=true then Sum.inl ⟨t,h⟩ else Sum.inr ⟨t,h⟩) =
    Sum.elim i o (if h : p.val (Sum.inr t)=true
      then Sum.inl ⟨Sum.inr t,h⟩ else Sum.inr ⟨Sum.inr t,h⟩)
  split <;> rfl

end partition

end LogConcaveSampling.TensorEnergy

end

end

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators Matrix.Norms.L2Operator

universe u
variable {S : Type u} [Fintype S] {d : ℕ}

lemma nonempty_properSplit (hS : 2≤Fintype.card S) : Nonempty (ProperSplit S) := by
  let : Nontrivial S := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨s,t,hst⟩ := exists_pair_ne S
  exact ⟨⟨fun x => decide (x=s),⟨s,by simp⟩,⟨t,by simp [Ne.symm hst]⟩⟩⟩

end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_NormalizedTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators RealInnerProductSpace NNReal

universe u

lemma list_split_perm {S I O : Type u} [Fintype I] [Fintype O]
    (l : List S) (hl : l.Nodup) (hall : ∀s,s∈l) (e : S ≃ I ⊕ O) :
    (l.map e).Perm ((Finset.univ.toList : List I).map Sum.inl ++
      (Finset.univ.toList : List O).map Sum.inr) := by
  apply (List.perm_ext_iff_of_nodup (hl.map e.injective) ?_).mpr
  · intro s
    constructor
    · intro _
      cases s <;> simp
    · intro _
      exact List.mem_map.mpr ⟨e.symm s,hall _,e.apply_symm_apply _⟩
  · simp only [List.nodup_append]
    refine ⟨(Finset.nodup_toList _).map Sum.inl_injective,
      (Finset.nodup_toList _).map Sum.inr_injective,?_⟩
    intro a ha b hb
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    obtain ⟨o,ho,rfl⟩ := List.mem_map.mp hb
    exact Sum.inl_ne_inr

def normalizedTensorMajorant (n : ℕ) (a : ℝ) : ℝ :=
  Real.sqrt (((n+1:ℕ):ℝ)^(2*(n+1))*(2*Real.pi^2)^n*
    ((n.factorial:ℝ)^2)^2/a^(n-2))

lemma normalizedTensorMajorant_nonneg (n : ℕ) (a : ℝ) :
    0≤normalizedTensorMajorant n a := Real.sqrt_nonneg _

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

universe u

lemma list_length_full {S : Type u} [Fintype S] (l : List S)
    (hl : l.Nodup) (hall : ∀s,s∈l) : l.length=Fintype.card S := by
  have he : l.toFinset=Finset.univ := Finset.eq_univ_of_forall (fun s => List.mem_toFinset.mpr (hall s))
  rw [←List.toFinset_card_of_nodup hl,he,Finset.card_univ]

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_SmoothTimeLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Filter Metric
open scoped Topology

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem smooth_time_localization {A : ℝ × E → G} {t : ℝ}
    (ht0 : -1<t) (ht1 : t<1)
    (hA : ∀p : ℝ × E, -1<p.1 → p.1<1 → ContDiffAt ℝ (⊤:ℕ∞) A p) :
    ∃B : ℝ × E → G, ContDiff ℝ (⊤:ℕ∞) B ∧
      ∀ᶠs in nhds t, ∀y,B (s,y)=A (s,y) := by
  let δ := min (t+1) (1-t)/2
  have hd : 0<δ := half_pos (lt_min (by linarith) (by linarith))
  have hd0 : δ<t+1 := by
    have := min_le_left (t+1) (1-t)
    dsimp [δ] at *
    linarith
  have hd1 : δ<1-t := by
    have := min_le_right (t+1) (1-t)
    dsimp [δ] at *
    linarith
  let c : ContDiffBump t := ⟨δ/2,δ,half_pos hd,half_lt_self hd⟩
  let B : ℝ × E → G := fun p => c p.1 • A p
  refine ⟨B,?_,?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p.1∈tsupport c
    · rw [c.tsupport_eq] at hp
      have hb : |p.1-t|≤δ := by simpa only [mem_closedBall,Real.dist_eq,c] using hp
      have hlo : -1<p.1 := by have := (abs_le.mp hb).1; linarith
      have hhi : p.1<1 := by have := (abs_le.mp hb).2; linarith
      exact (c.contDiff.contDiffAt.comp p contDiffAt_fst).smul (hA p hlo hhi)
    · have he : c=ᶠ[nhds p.1]0 := notMem_tsupport_iff_eventuallyEq.mp hp
      apply (contDiffAt_const (c:=(0:G))).congr_of_eventuallyEq
      filter_upwards [he.comp_tendsto continuousAt_fst] with q hq
      change c q.1=0 at hq
      simp [B,hq]
  · filter_upwards [c.eventuallyEq_one] with s hs
    intro y
    simp [B,hs]

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_SpaceBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling.JetCalculus
open scoped Classical BigOperators RealInnerProductSpace

abbrev spaceBasis (d : ℕ) := EuclideanSpace.basisFun (Fin d) ℝ

def linearScore {d : ℕ} (i : Fin d) (y : Point d) : ℝ := inner ℝ (spaceBasis d i) y

lemma linearScore_smooth {d : ℕ} (i : Fin d) : ContDiff ℝ (⊤:ℕ∞) (linearScore i) :=
  (innerSL ℝ (spaceBasis d i)).contDiff

end LogConcaveSampling.JetCalculus

end

end

section

noncomputable section
namespace LogConcaveSampling.JetCalculus
open Filter
open scoped Topology Classical BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι κ : Type*} [Fintype ι]

def TimeSmooth (f : ℝ × E → ℝ) : Prop :=
  ∀p : ℝ × E,-1<p.1 → p.1<1 → ContDiffAt ℝ (⊤:ℕ∞) f p

lemma TimeSmooth.localize {f : ℝ × E → ℝ} (hf : TimeSmooth f) {p : ℝ × E}
    (h0 : -1<p.1) (h1 : p.1<1) :
    ∃g : ℝ × E → ℝ, ContDiff ℝ (⊤:ℕ∞) g ∧ g=ᶠ[nhds p]f := by
  obtain ⟨g,hg,he⟩ := smooth_time_localization h0 h1 hf
  refine ⟨g,hg,?_⟩
  have hh := (continuousAt_fst (p:=p)).eventually he
  filter_upwards [hh] with q hq
  exact hq q.2

end LogConcaveSampling.JetCalculus

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_JointSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

def jointSpace {d : ℕ} (i : Fin d) : ℝ × Point d :=
  (0,EuclideanSpace.basisFun (Fin d) ℝ i)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_JetRightSlice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling.JetCalculus
open scoped Classical BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

lemma hasDerivAt_inv_nat_pow {t : ℝ} (ht : t≠0) (q : ℕ) :
    HasDerivAt (fun s : ℝ => (s^q)⁻¹) (-(q:ℝ)*t⁻¹*(t^q)⁻¹) t := by
  induction q with
  | zero => simpa using (hasDerivAt_const t (1:ℝ))
  | succ q ih =>
    have hh : HasDerivAt (fun s : ℝ => (s^q)⁻¹*s⁻¹)
        (-(q:ℝ)*t⁻¹*(t^q)⁻¹*t⁻¹+(t^q)⁻¹*(-1/t^2)) t :=
      ih.mul ((hasDerivAt_id t).inv ht)
    have hf : (fun s : ℝ => (s^(q+1))⁻¹)=fun s => (s^q)⁻¹*s⁻¹ := by
      funext s
      simp [pow_succ,mul_comm]
    rw [hf]
    have he : -(q:ℝ)*t⁻¹*(t^q)⁻¹*t⁻¹+(t^q)⁻¹*(-1/t^2)=
        -((q+1:ℕ):ℝ)*t⁻¹*(t^(q+1))⁻¹ := by
      simp only [Nat.cast_add,Nat.cast_one,pow_succ,mul_inv_rev]
      field_simp
      ring
    rwa [he] at hh

end LogConcaveSampling.JetCalculus

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_JointU
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Filter
open scoped Topology Classical BigOperators NNReal RealInnerProductSpace

lemma split_power_cancel {κ : Type*} [DecidableEq κ] (l : List κ) (s : Finset κ)
    {ρ : ℝ} (hρ : ρ≠0) :
    (ρ^l.length)⁻¹*ρ^(l.filter (fun j => j∈s)).length*
      ρ^((l.filter (fun j => j∉s)).length+1)=ρ := by
  have hl : l.length=(l.filter (fun j => j∈s)).length+(l.filter (fun j => j∉s)).length := by
    simpa only [←decide_not] using l.length_eq_length_filter_add (fun j => decide (j∈s))
  rw [hl,pow_add,pow_succ]
  field_simp

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_InterpolationResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

lemma integrable_lipschitz_comp_of_integrable {Ω E G : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] [NormedAddCommGroup E] [NormedAddCommGroup G]
    {X : Ω → E} (hX : Integrable X μ) {g : E → G} {L : ℝ≥0} (hg : LipschitzWith L g) :
    Integrable (fun ω => g (X ω)) μ := by
  apply ((integrable_const ‖g 0‖).add (hX.norm.const_mul (L:ℝ))).mono'
    (hg.continuous.comp_aestronglyMeasurable hX.aestronglyMeasurable)
  filter_upwards [] with ω
  have hh := hg.dist_le_mul (X ω) 0
  rw [dist_eq_norm,dist_zero_right] at hh
  calc
    ‖g (X ω)‖ ≤ ‖g 0‖+‖g (X ω)-g 0‖ := norm_le_norm_add_norm_sub' _ _
    _ ≤ ‖g 0‖+(L:ℝ)*‖X ω‖ := by linarith

end LogConcaveSampling

open Function MeasureTheory Set Filter
open scoped Topology NNReal

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ProbabilityVelocity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open Set Function MeasureTheory
open scoped Topology

def interpolationPath {d : ℕ} (t : ℝ) (p : Point d × Point d) : Point d :=
  t • p.1+Real.sqrt (1-t^2) • p.2

def interpolationPathDerivative {d : ℕ} (t : ℝ) (p : Point d × Point d) : Point d :=
  p.1-(t/Real.sqrt (1-t^2)) • p.2

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_VariationalField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.GlobalODE
open Set Function Filter Metric
open scoped Topology NNReal

def variationalField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (p : E × (E →L[ℝ] E)) : E × (E →L[ℝ] E) :=
  (f p.1,(fderiv ℝ f p.1).comp p.2)

lemma variationalField_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {n : ℕ} (hf : ContDiff ℝ ((n:WithTop ℕ∞)+1) f) :
    ContDiff ℝ (n:WithTop ℕ∞) (variationalField f) :=
  ((hf.of_le (by exact_mod_cast Nat.le_succ n)).comp contDiff_fst).prodMk
    (((hf.fderiv_right le_rfl).comp contDiff_fst).clm_comp contDiff_snd)

end LogConcaveSampling.GlobalODE

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_CoordinateRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open Filter
open scoped Topology Classical BigOperators

lemma eq_zero_of_continuous_pos {f g : ℝ → ℝ}
    (hf : ContinuousAt f 0) (hg : ContinuousAt g 0)
    (he : ∀t,0<t → t<1 → f t=g t) : f 0=g 0 := by
  have hfg : f=ᶠ[nhdsWithin 0 (Set.Ioi 0)]g := by
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1))] with t h0 h1
    exact he t h0 h1
  exact tendsto_nhds_unique (hf.mono_left nhdsWithin_le_nhds)
    ((hg.mono_left nhdsWithin_le_nhds).congr' hfg.symm)

lemma extra_list_nodup {ι : Type*} {l : List ι} (hl : l.Nodup) :
    (Sum.inr ()::l.map (Sum.inl (β:=Unit))).Nodup := by
  simp only [List.nodup_cons]
  refine ⟨?_,hl.map Sum.inl_injective⟩
  simp

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_TensorExpression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

inductive TensorExpression : ℕ → Type
  | jet (q : ℕ) : TensorExpression (q+2)
  | perm {n : ℕ} (e : Fin n ≃ Fin n) (A : TensorExpression n) : TensorExpression n
  | contract {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
      (A : TensorExpression (m+1)) (B : TensorExpression (n+1)) : TensorExpression (m+n)
  | adjoint {n : ℕ} (hn : 2≤n) (A : TensorExpression (n+1)) : TensorExpression n

namespace TensorExpression

def weight {n : ℕ} : TensorExpression n → ℕ
  | .jet q => q
  | .perm _ A => A.weight
  | .contract _ _ A B => A.weight+B.weight
  | .adjoint _ A => A.weight+1

end TensorExpression
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal

structure TensorAtom (S : Type) where
  rank : ℕ
  expression : TensorExpression rank
  labels : Fin rank ≃ S

namespace TensorAtom

variable {S T : Type}

def relabel (A : TensorAtom S) (e : S ≃ T) : TensorAtom T :=
  ⟨A.rank,A.expression,A.labels.trans e⟩

def reindex (A : TensorAtom S) {n : ℕ} (e : Fin n ≃ S) : TensorExpression n := by
  rcases A with ⟨m,A,eA⟩
  have h : m=n := by simpa using Fintype.card_congr (eA.trans e.symm)
  subst m
  exact .perm (eA.trans e.symm) A

lemma reindex_weight (A : TensorAtom S) {n : ℕ} (e : Fin n ≃ S) :
    (A.reindex e).weight=A.expression.weight := by
  rcases A with ⟨m,A,eA⟩
  have h : m=n := by simpa using Fintype.card_congr (eA.trans e.symm)
  subst m
  rfl

def lastEquiv {n : ℕ} (e : Fin n ≃ S) : Fin (n+1) ≃ S ⊕ Unit :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr e (Equiv.ofUnique (Fin 1) Unit))

@[simp] lemma lastEquiv_castSucc {n : ℕ} (e : Fin n ≃ S) (j : Fin n) :
    lastEquiv e j.castSucc=Sum.inl (e j) := by simp [lastEquiv]

@[simp] lemma lastEquiv_last {n : ℕ} (e : Fin n ≃ S) :
    lastEquiv e (Fin.last n)=Sum.inr () := by simp [lastEquiv,Equiv.ofUnique]

lemma lastEquiv_snoc {d n : ℕ} (e : Fin n ≃ S) (c : S → Fin d) (k : Fin d) :
    (Fin.snoc (c ∘ e) k) ∘ (lastEquiv e).symm=Sum.elim c (fun _ => k) := by
  funext s
  apply Equiv.surjective (lastEquiv e) |>.forall.mpr ?_ s
  intro j
  simp only [Function.comp_apply,Equiv.symm_apply_apply]
  induction j using Fin.lastCases <;> simp

def contract [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
    (A : TensorAtom (S ⊕ Unit)) (B : TensorAtom (T ⊕ Unit)) : TensorAtom (S ⊕ T) :=
  let eS := (Fintype.equivFin S).symm
  let eT := (Fintype.equivFin T).symm
  ⟨Fintype.card S+Fintype.card T,
    .contract (Fintype.card_pos) (Fintype.card_pos) (A.reindex (lastEquiv eS)) (B.reindex (lastEquiv eT)),
    finSumFinEquiv.symm.trans (Equiv.sumCongr eS eT)⟩

lemma contract_weight [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
    (A : TensorAtom (S ⊕ Unit)) (B : TensorAtom (T ⊕ Unit)) :
    (A.contract B).expression.weight=A.expression.weight+B.expression.weight := by
  simp only [contract,TensorExpression.weight,reindex_weight]

def adjoint [Fintype S] (hn : 2≤Fintype.card S) (A : TensorAtom (S ⊕ Unit)) : TensorAtom S :=
  ⟨Fintype.card S,.adjoint hn (A.reindex (lastEquiv (Fintype.equivFin S).symm)),
    (Fintype.equivFin S).symm⟩

lemma adjoint_weight [Fintype S] (hn : 2≤Fintype.card S) (A : TensorAtom (S ⊕ Unit)) :
    (A.adjoint hn).expression.weight=A.expression.weight+1 := by
  simp only [adjoint,TensorExpression.weight,reindex_weight]

end TensorAtom
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_SpatialTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical

universe u

def selectList {K : Type u} (p : K → Prop) [DecidablePred p] : List K → List {k // p k}
  | [] => []
  | k::l => if h : p k then ⟨k,h⟩::selectList p l else selectList p l

lemma map_selectList {K : Type u} (p : K → Prop) [DecidablePred p] (l : List K) :
    (selectList p l).map Subtype.val=l.filter (fun k => decide (p k)) := by
  induction l with
  | nil => rfl
  | cons k l ih => by_cases h:p k <;> simp [selectList,h,ih]

lemma selectList_nodup {K : Type u} (p : K → Prop) [DecidablePred p]
    {l : List K} (hl : l.Nodup) : (selectList p l).Nodup := by
  apply List.Nodup.of_map (f:=Subtype.val)
  rw [map_selectList]
  exact hl.filter _

lemma selectList_full {K : Type u} (p : K → Prop) [DecidablePred p]
    {l : List K} (hall : ∀k,k∈l) : ∀ k : {k // p k}, k∈selectList p l := by
  intro k
  have hh : k.val∈(selectList p l).map Subtype.val := by
    rw [map_selectList]
    simp [hall,k.property]
  obtain ⟨z,hz,hzk⟩ := List.mem_map.mp hh
  have he : z=k := Subtype.ext hzk
  rwa [he] at hz

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators

namespace TensorAtom
variable {S : Type}

def jetList (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l) (hne : l≠[]) : TensorAtom (S ⊕ Unit) :=
  match l,hN,hall,hne with
  | [],_,_,he => (he rfl).elim
  | a::l,hN,hall,_ => ⟨l.length+2,.jet l.length,
      lastEquiv (List.Nodup.getEquivOfForallMemList (a::l) hN hall)⟩

lemma jetList_weight (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l) (hne : l≠[]) :
    (jetList l hN hall hne).expression.weight=l.length-1 := by
  cases l with
  | nil => exact (hne rfl).elim
  | cons a l => rfl

def swapLast : (S ⊕ Unit) ⊕ Unit ≃ (S ⊕ Unit) ⊕ Unit :=
  (Equiv.sumAssoc S Unit Unit).trans ((Equiv.sumCongr (Equiv.refl S) (Equiv.sumComm Unit Unit)).trans
    (Equiv.sumAssoc S Unit Unit).symm)

@[simp] lemma swapLast_left (s : S) : swapLast (Sum.inl (Sum.inl s))=Sum.inl (Sum.inl s) := rfl
@[simp] lemma swapLast_inner : (swapLast (S:=S)) (Sum.inl (Sum.inr ()))=Sum.inr () := rfl
@[simp] lemma swapLast_outer : (swapLast (S:=S)) (Sum.inr ())=Sum.inl (Sum.inr ()) := rfl

def extendedU (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l) : TensorAtom ((S ⊕ Unit) ⊕ Unit) :=
  (jetList (Sum.inr ()::l.map Sum.inl) (extra_list_nodup hN)
    (by intro s; cases s <;> simp [hall]) (by simp)).relabel swapLast

lemma extendedU_weight (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l) :
    (extendedU l hN hall).expression.weight=l.length := by
  simp only [extendedU,relabel,jetList_weight,List.length_cons,List.length_map,Nat.add_sub_cancel]

end TensorAtom
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators

lemma selectList_lengths {S : Type} (P : S → Prop) [DecidablePred P] (l : List S) :
    (selectList P l).length+(selectList (fun s => ¬P s) l).length=l.length := by
  induction l with
  | nil => rfl
  | cons s l ih => by_cases hs:P s <;> simp [selectList,hs] <;> omega

namespace TensorAtom
variable {S : Type}

def splitLabels (a : Finset S) : {s // s∈a} ⊕ ({s // s∉a} ⊕ Unit) ≃ S ⊕ Unit :=
  (Equiv.sumAssoc _ _ _).symm.trans (Equiv.sumCongr (Equiv.sumCompl (fun s => s∈a)) (Equiv.refl Unit))

@[simp] lemma splitLabels_left (a : Finset S) (s : {s // s∈a}) :
    splitLabels a (Sum.inl s)=Sum.inl s.val := rfl
@[simp] lemma splitLabels_right (a : Finset S) (s : {s // s∉a}) :
    splitLabels a (Sum.inr (Sum.inl s))=Sum.inl s.val := rfl
@[simp] lemma splitLabels_field (a : Finset S) :
    splitLabels a (Sum.inr (Sum.inr ()))=Sum.inr () := rfl

variable [Fintype S]

def splitProduct (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l)
    (a : Finset S) (ha : a.Nonempty) : TensorAtom (S ⊕ Unit) := by
  letI : Nonempty {s // s∈a} := ⟨⟨ha.choose,ha.choose_spec⟩⟩
  exact ((jetList (selectList (fun s => s∈a) l) (selectList_nodup _ hN)
    (selectList_full _ hall) (by
      intro he
      have hh := selectList_full (fun s => s∈a) hall ⟨ha.choose,ha.choose_spec⟩
      simp [he] at hh)).contract
    (extendedU (selectList (fun s => s∉a) l) (selectList_nodup _ hN)
      (selectList_full _ hall))).relabel (splitLabels a)

lemma splitProduct_weight (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l)
    (a : Finset S) (ha : a.Nonempty) :
    (splitProduct l hN hall a ha).expression.weight=l.length-1 := by
  let : Nonempty {s // s∈a} := ⟨⟨ha.choose,ha.choose_spec⟩⟩
  dsimp only [splitProduct,relabel]
  rw [contract_weight,jetList_weight,extendedU_weight]
  have hp : 0<(selectList (fun s => s∈a) l).length := by
    apply List.length_pos_iff.mpr
    intro he
    have hh := selectList_full (fun s => s∈a) hall ⟨ha.choose,ha.choose_spec⟩
    simp [he] at hh
  have hs := selectList_lengths (fun s => s∈a) l
  omega

end TensorAtom
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_SplitIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal

namespace TensorAtom
variable {S : Type} [Fintype S]

lemma jetCard (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l) (hne : l≠[]) :
    2≤Fintype.card (S ⊕ Unit) := by
  have he := Fintype.card_congr (List.Nodup.getEquivOfForallMemList l hN hall)
  have hp := List.length_pos_iff.mpr hne
  simp only [Fintype.card_fin] at he
  simp only [Fintype.card_sum,Fintype.card_unit]
  omega

abbrev SplitIndex (l : List S) := ↥(l.toFinset.powerset.erase ∅)

omit [Fintype S] in
lemma splitIndex_nonempty {l : List S} (a : SplitIndex l) : a.val.Nonempty :=
  Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp a.property).1

def splitAtom (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l) (a : SplitIndex l) : TensorAtom (S ⊕ Unit) :=
  splitProduct l hN hall a.val (splitIndex_nonempty a)

lemma splitAtom_weight (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l) (a : SplitIndex l) :
    (splitAtom l hN hall a).expression.weight=l.length-1 := splitProduct_weight _ _ _ _ _

end TensorAtom
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_TensorTerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal

lemma polynomialTime_smooth {d : ℕ} (P : Polynomial ℝ) :
    ContDiff ℝ (⊤:ℕ∞) (fun p : ℝ × Point d => P.eval p.1) := by
  have hP : ContDiff ℝ (⊤:ℕ∞) (fun t : ℝ => P.eval t) := by
    simpa using P.contDiff_aeval (𝕜:=ℝ) (⊤:ℕ∞)
  exact hP.comp contDiff_fst

structure TensorTerm (S : Type) where
  power : ℕ
  coefficient : Polynomial ℝ
  atom : TensorAtom S

namespace TensorTerm
variable {S T : Type}

def relabel (A : TensorTerm S) (e : S ≃ T) : TensorTerm T :=
  ⟨A.power,A.coefficient,A.atom.relabel e⟩

def scale (A : TensorTerm S) (n : ℕ) (P : Polynomial ℝ) : TensorTerm S :=
  ⟨n+A.power,P*A.coefficient,A.atom⟩

def adjoint [Fintype S] (hn : 2≤Fintype.card S) (A : TensorTerm (S ⊕ Unit)) : TensorTerm S :=
  ⟨A.power,A.coefficient,A.atom.adjoint hn⟩

def contract [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
    (A : TensorTerm (S ⊕ Unit)) (B : TensorTerm (T ⊕ Unit)) : TensorTerm (S ⊕ T) :=
  ⟨A.power+B.power,A.coefficient*B.coefficient,A.atom.contract B.atom⟩

end TensorTerm

structure TensorSum (S : Type) where
  index : Type
  finite : Fintype index
  term : index → TensorTerm S

namespace TensorSum
variable {S T : Type}
instance instFintypeIndex (A : TensorSum S) : Fintype A.index := A.finite

def weightLE (A : TensorSum S) (w : ℕ) : Prop := ∀i,(A.term i).atom.expression.weight≤w

def pure (A : TensorAtom S) : TensorSum S := ⟨Unit,inferInstance,fun _ => ⟨0,1,A⟩⟩

def add (A B : TensorSum S) : TensorSum S := ⟨A.index ⊕ B.index,inferInstance,Sum.elim A.term B.term⟩

def relabel (A : TensorSum S) (e : S ≃ T) : TensorSum T :=
  ⟨A.index,A.finite,fun i => (A.term i).relabel e⟩

def scale (A : TensorSum S) (n : ℕ) (P : Polynomial ℝ) : TensorSum S :=
  ⟨A.index,A.finite,fun i => (A.term i).scale n P⟩

def adjoint [Fintype S] (hn : 2≤Fintype.card S) (A : TensorSum (S ⊕ Unit)) : TensorSum S :=
  ⟨A.index,A.finite,fun i => (A.term i).adjoint hn⟩

def contract [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
    (A : TensorSum (S ⊕ Unit)) (B : TensorSum (T ⊕ Unit)) : TensorSum (S ⊕ T) :=
  ⟨A.index × B.index,inferInstance,fun i => (A.term i.1).contract (B.term i.2)⟩

end TensorSum
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal

namespace TensorAtom

def one : TensorAtom (Unit ⊕ Unit) :=
  (jetList [()] (by simp) (by intro s; cases s; simp) (by simp)).relabel (Equiv.sumComm Unit Unit)

lemma one_weight : one.expression.weight=0 := rfl

variable {S : Type} [Fintype S] [Nonempty S]

def insertOne (A : TensorAtom (S ⊕ Unit)) : TensorAtom (S ⊕ Unit) :=
  (one.contract A).relabel (Equiv.sumComm Unit S)

lemma insertOne_weight (A : TensorAtom (S ⊕ Unit)) :
    (A.insertOne).expression.weight=A.expression.weight := by
  simp only [insertOne,relabel,contract_weight,one_weight,zero_add]

end TensorAtom

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_Material
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal

namespace TensorSum
variable {S T : Type}
lemma weightLE_pure (A : TensorAtom S) {w : ℕ} (h : A.expression.weight≤w) :
    (pure A).weightLE w := fun _ => h
lemma weightLE_add {A B : TensorSum S} {w : ℕ} (hA : A.weightLE w) (hB : B.weightLE w) :
    (A.add B).weightLE w := by
  intro i; cases i with
  | inl i => exact hA i
  | inr i => exact hB i
lemma weightLE_scale {A : TensorSum S} {w : ℕ} (hA : A.weightLE w) (n : ℕ) (P : Polynomial ℝ) :
    (A.scale n P).weightLE w := hA
lemma weightLE_relabel {A : TensorSum S} {w : ℕ} (hA : A.weightLE w) (e : S ≃ T) :
    (A.relabel e).weightLE w := hA
lemma weightLE_adjoint [Fintype S] (hn : 2≤Fintype.card S) {A : TensorSum (S ⊕ Unit)}
    {w : ℕ} (hA : A.weightLE w) : (A.adjoint hn).weightLE (w+1) := by
  intro i
  change ((A.term i).atom.adjoint hn).expression.weight≤w+1
  rw [TensorAtom.adjoint_weight]
  exact Nat.add_le_add_right (hA i) 1
lemma weightLE_contract [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
    {A : TensorSum (S ⊕ Unit)} {B : TensorSum (T ⊕ Unit)} {w z : ℕ}
    (hA : A.weightLE w) (hB : B.weightLE z) : (A.contract B).weightLE (w+z) := by
  intro i
  change ((A.term i.1).atom.contract (B.term i.2).atom).expression.weight≤w+z
  rw [TensorAtom.contract_weight]
  exact Nat.add_le_add (hA _) (hB _)
lemma weightLE_mono {A : TensorSum S} {w z : ℕ} (hA : A.weightLE w) (h : w≤z) :
    A.weightLE z := fun i => (hA i).trans h
end TensorSum

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_JetMaterial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal

namespace TensorAtom
variable {S T : Type}

@[simp] lemma lastEquiv_symm_inl {n : ℕ} (e : Fin n ≃ S) (s : S) :
    (lastEquiv e).symm (Sum.inl s)=(e.symm s).castSucc := by
  apply (lastEquiv e).injective
  simp
@[simp] lemma lastEquiv_symm_inr {n : ℕ} (e : Fin n ≃ S) (s : Unit) :
    (lastEquiv e).symm (Sum.inr s)=Fin.last n := by
  cases s
  apply (lastEquiv e).injective
  simp

variable [Fintype S]
def jetMaterial (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l) (hne : l≠[]) : TensorSum (S ⊕ Unit) :=
  (TensorSum.pure ((extendedU l hN hall).adjoint (jetCard l hN hall hne))).add
    ⟨SplitIndex l,inferInstance,fun a => ⟨1,Polynomial.C 2*Polynomial.X,splitAtom l hN hall a⟩⟩

lemma jetMaterial_weight (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l) (hne : l≠[]) :
    (jetMaterial l hN hall hne).weightLE ((jetList l hN hall hne).expression.weight+2) := by
  apply TensorSum.weightLE_add
  · apply TensorSum.weightLE_pure
    rw [adjoint_weight,extendedU_weight,jetList_weight]
    have := List.length_pos_iff.mpr hne
    omega
  · intro a
    change (splitAtom l hN hall a).expression.weight≤_
    rw [splitAtom_weight,jetList_weight]
    omega

end TensorAtom

namespace TensorExpression

def atom {n : ℕ} (A : TensorExpression n) : TensorAtom (Fin n) := ⟨n,A,Equiv.refl _⟩
@[simp] lemma atom_weight {n : ℕ} (A : TensorExpression n) : A.atom.expression.weight=A.weight := rfl

end TensorExpression
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal

namespace TensorSum
variable {S : Type}

def combine {I : Type} [Fintype I] (f : I → TensorSum S) : TensorSum S :=
  ⟨(i : I) × (f i).index,inferInstance,fun a => (f a.1).term a.2⟩

lemma weightLE_combine {I : Type} [Fintype I] {f : I → TensorSum S} {w : ℕ}
    (h : ∀i,(f i).weightLE w) : (combine f).weightLE w := fun a => h a.1 a.2

end TensorSum
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

namespace TensorSum
variable {S : Type} [Fintype S] [Nonempty S]

def insertOne (A : TensorSum (S ⊕ Unit)) : TensorSum (S ⊕ Unit) :=
  ((pure TensorAtom.one).contract A).relabel (Equiv.sumComm Unit S)

end TensorSum
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_PolynomialBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped BigOperators

def polynomialBudget (P : Polynomial ℝ) : ℝ := ∑n ∈ P.support,|P.coeff n|

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_TensorGraphs_Vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

section
namespace LogConcaveSampling.TraceOpening

abbrev Vertex (n : ℕ) (H : Type*) := Sum (Fin (n+1)) H

def level {n : ℕ} {H : Type*} (left : H → Fin (n+1)) : Vertex n H → ℕ
  | Sum.inl i => 2*i.val
  | Sum.inr h => 2*(left h).val+1

def orderKey {V : Type*} [Fintype V] (r : V → ℕ) (v : V) : ℕ :=
  r v*(Fintype.card V+1)+(Fintype.equivFin V v).val

end LogConcaveSampling.TraceOpening

end
section
namespace LogConcaveSampling

def traceMomentOrder (d j : ℕ) (c p : ℝ) : ℕ :=
  ⌈p/2+((j:ℝ)+c)*Real.log ((d:ℝ)+1)⌉₊

end LogConcaveSampling

end
end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_TensorGraphs_Live
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

section
namespace LogConcaveSampling.Frontier

variable {E : Type*} (a b : E → ℕ)

abbrev Live (k : ℕ) := {e : E // a e≤k ∧ k<b e}
abbrev Incoming (k : ℕ) := {e : E // b e=k+1}
abbrev Outgoing (k : ℕ) := {e : E // a e=k+1}
abbrev Spectator (k : ℕ) := {e : E // a e≤k ∧ k+1<b e}

def splitIncoming (hab : ∀e,a e<b e) (k : ℕ) :
    Live a b k ≃ Incoming b k ⊕ Spectator a b k where
  toFun e := if h : b e.val=k+1 then Sum.inl ⟨e.val,h⟩ else
    Sum.inr ⟨e.val,e.property.1,by have := e.property.2; omega⟩
  invFun e := match e with
    | Sum.inl e => ⟨e.val,by have := hab e.val; have := e.property; omega,
        by have := e.property; omega⟩
    | Sum.inr e => ⟨e.val,e.property.1,by have := e.property.2; omega⟩
  left_inv e := by
    dsimp only
    split_ifs <;> rfl
  right_inv e := by
    cases e with
    | inl e => simp only [e.property,dite_eq_left]
    | inr e =>
      have hn : b e.val≠k+1 := by have := e.property.2; omega
      simp [hn]

def splitOutgoing (hab : ∀e,a e<b e) (k : ℕ) :
    Live a b (k+1) ≃ Outgoing a k ⊕ Spectator a b k where
  toFun e := if h : a e.val=k+1 then Sum.inl ⟨e.val,h⟩ else
    Sum.inr ⟨e.val,by have := e.property.1; omega,e.property.2⟩
  invFun e := match e with
    | Sum.inl e => ⟨e.val,by have := e.property; omega,
        by have := hab e.val; have := e.property; omega⟩
    | Sum.inr e => ⟨e.val,by have := e.property.1; omega,e.property.2⟩
  left_inv e := by
    dsimp only
    split_ifs <;> rfl
  right_inv e := by
    cases e with
    | inl e => simp only [e.property,dite_eq_left]
    | inr e =>
      have hn : a e.val≠k+1 := by have := e.property.1; omega
      simp [hn]

def inputCoordinates {C : Type*} (hab : ∀e,a e<b e) (k : ℕ) :
    (Live a b k → C) ≃ (Incoming b k → C) × (Spectator a b k → C) :=
  (Equiv.arrowCongr (splitIncoming a b hab k) (Equiv.refl C)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

def outputCoordinates {C : Type*} (hab : ∀e,a e<b e) (k : ℕ) :
    (Live a b (k+1) → C) ≃ (Outgoing a k → C) × (Spectator a b k → C) :=
  (Equiv.arrowCongr (splitOutgoing a b hab k) (Equiv.refl C)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

end LogConcaveSampling.Frontier

end
end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_TensorGraphs_History
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.Frontier
open scoped Classical

variable {E C : Type*} (a b : E → ℕ)

abbrev History (n : ℕ) := ∀k : Fin (n+1),Live a b k.val → C

def Consistent {n : ℕ} (h : History (C:=C) a b n) : Prop :=
  ∀k (hk : k<n) (e : Spectator a b k),
    h ⟨k+1,by omega⟩ ⟨e.val,by change a e.val≤k+1; have := e.property.1; omega,e.property.2⟩ =
    h ⟨k,by omega⟩ ⟨e.val,e.property.1,by change k<b e.val; have := e.property.2; omega⟩

def historyOf {n : ℕ} (c : E → C) : History (C:=C) a b n := fun _ e => c e.val

lemma historyOf_consistent {n : ℕ} (c : E → C) :
    Consistent a b (historyOf (n:=n) a b c) := by
  intro k hk e
  rfl

lemma consistent_color {n : ℕ} (hab : ∀e,a e<b e) (han : ∀e,a e≤n)
    {h : History (C:=C) a b n} (hh : Consistent a b h) (e : E)
    (k : ℕ) (hak : a e≤k) (hkn : k≤n) (hkb : k<b e) :
    h ⟨k,by omega⟩ ⟨e,hak,hkb⟩ =
    h ⟨a e,by have := han e; omega⟩ ⟨e,le_rfl,hab e⟩ := by
  induction k,hak using Nat.le_induction with
  | base => rfl
  | succ k hak ih =>
    have hk : k<n := by omega
    have he : a e≤k ∧ k+1<b e := ⟨hak,hkb⟩
    exact (hh k hk ⟨e,he⟩).trans (ih (by omega) (by omega))

noncomputable def historyEquiv {n : ℕ} (hab : ∀e,a e<b e) (han : ∀e,a e≤n) :
    (E → C) ≃ {h : History (C:=C) a b n // Consistent a b h} where
  toFun c := ⟨historyOf a b c,historyOf_consistent a b c⟩
  invFun h e := h.val ⟨a e,by have := han e; omega⟩ ⟨e,le_rfl,hab e⟩
  left_inv c := rfl
  right_inv h := by
    apply Subtype.ext
    funext k e
    exact (consistent_color a b hab han h.property e.val k.val
      e.property.1 (by have := k.isLt; omega) e.property.2).symm

end LogConcaveSampling.Frontier
namespace LogConcaveSampling.Frontier
open scoped BigOperators Classical
open TensorEnergy

variable {E C : Type*} [Fintype E] [Fintype C]
    (a b : E → ℕ) (hab : ∀e,a e<b e)

def graphStep (A : ∀k,(Outgoing a k → C) → (Incoming b k → C) → ℝ) (k : ℕ) :
    (Live a b (k+1) → C) → (Live a b k → C) → ℝ :=
  wireStep (A k) (inputCoordinates a b hab k) (outputCoordinates a b hab k)

end LogConcaveSampling.Frontier
namespace LogConcaveSampling.GraphSchedule
open scoped Classical

variable {V U : Type*} [Fintype V] (key : V → ℕ) (src dst : U → V)

def length : ℕ := Finset.univ.sup key+1

lemma key_lt_length (v : V) : key v<length key :=
  lt_of_le_of_lt (Finset.le_sup (f:=key) (Finset.mem_univ v)) (Nat.lt_succ_self _)

end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.GraphSchedule
open scoped Classical

variable {V U : Type*} [Fintype V] (key : V → ℕ) (src dst : U → V)

def Adjacent (u v : V) : Prop :=
  ∃e,(src e=u ∧ dst e=v) ∨ (src e=v ∧ dst e=u)

end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.GraphSchedule
open scoped Classical

variable {V U C : Type*} [Fintype V] (key : V → ℕ) (src dst : U → V)
local instance finDecEqC (d : ℕ) : DecidableEq (Fin d) := Classical.decEq _

end LogConcaveSampling.GraphSchedule

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_TensorGraphs_RankEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.GraphSchedule
open scoped BigOperators Classical
open TensorEnergy

variable {V U : Type*} [Fintype V] [Fintype U]
local instance finDecEqUp (d : ℕ) : DecidableEq (Fin d) := Classical.decEq _

end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.GraphSchedule
open scoped BigOperators Classical
open TensorEnergy

variable {V U : Type*} [Fintype V] [Fintype U]
local instance finDecEqRUp (d : ℕ) : DecidableEq (Fin d) := Classical.decEq _

end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.TraceOpening
open scoped Classical

variable {V : Type*} [Fintype V]

noncomputable def rankEquiv (key : V → ℕ) (hkey : Function.Injective key) :
    V ≃ Fin (Fintype.card V) := by
  letI : LinearOrder V := LinearOrder.lift' key hkey
  exact (Fintype.orderIsoFinOfCardEq V rfl).symm.toEquiv

end LogConcaveSampling.TraceOpening
namespace LogConcaveSampling.GraphSchedule
open scoped Classical

variable {V : Type*} [Fintype V] [Nonempty V]

lemma length_equiv_val (e : V ≃ Fin (Fintype.card V)) :
    length (fun v => (e v).val)=Fintype.card V := by
  have hc : 0<Fintype.card V := Fintype.card_pos
  apply Nat.le_antisymm
  · unfold length
    have hh : Finset.univ.sup (fun v => (e v).val)<Fintype.card V := by
      exact (Finset.sup_lt_iff hc).mpr (fun v _ => (e v).isLt)
    omega
  · let v := e.symm ⟨Fintype.card V-1,by omega⟩
    have hv : (e v).val=Fintype.card V-1 := by simp [v]
    have hh := key_lt_length (fun w => (e w).val) v
    rw [hv] at hh
    omega
end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.GraphSchedule
open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [Nonempty V]

noncomputable def stageEquiv (e : V ≃ Fin (Fintype.card V)) :
    V ≃ Fin (length (fun v => (e v).val)) :=
  e.trans (finCongr (length_equiv_val e).symm)

end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.GraphSchedule
open scoped BigOperators Classical
open TensorEnergy

variable {V U : Type*} [Fintype V] [Fintype U] [Nonempty V]
local instance finDecEqRank (d : ℕ) : DecidableEq (Fin d) := Classical.decEq _

end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.GraphSchedule
variable {V : Type*} [Fintype V]

noncomputable def rankExtend (e : V ≃ Fin (Fintype.card V)) {D : ℕ → Type*}
    (z : ∀k,D k) (a : ∀v,D (e v).val) (k : ℕ) : D k :=
  if hk : k<Fintype.card V then
    cast (congrArg D (congrArg Fin.val (e.apply_symm_apply ⟨k,hk⟩))) (a (e.symm ⟨k,hk⟩))
  else z k

end LogConcaveSampling.GraphSchedule

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_TensorGraphs_IncidentMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.GraphSchedule
open scoped BigOperators Classical
open TensorEnergy

variable {V U : Type*} [Fintype V] [Fintype U] [Nonempty V]
local instance finDecEqTG (d : ℕ) : DecidableEq (Fin d) := Classical.decEq _

end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.GraphSchedule
open MeasureTheory TensorEnergy
open scoped BigOperators Classical ENNReal

variable {Ω P H U : Type*} [MeasurableSpace Ω] [Fintype P] [Fintype H] [Fintype U]
    [Nonempty P]
local instance finDecEqTGI (d : ℕ) : DecidableEq (Fin d) := Classical.decEq _

end LogConcaveSampling.GraphSchedule

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_TensorGraphs_Chain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling.CycleTrace
open scoped BigOperators

lemma row_index_odd {s : ℕ} (t : Fin (s+1)) (ht : t.val≠0) : (2*t.val-1)%2≠0 := by
  omega

end LogConcaveSampling.CycleTrace

end

end

section

noncomputable section
namespace LogConcaveSampling.CycleTrace
open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]

def weight (A : Matrix I J ℝ) {n : ℕ} (i k : I)
    (r : Fin n → I) (c : Fin (n+1) → J) : ℝ :=
  ∏ t : Fin (n+1), A (Fin.cons (α := fun _ => I) i r t) (c t) * A (Fin.snoc (α := fun _ => I) r k t) (c t)

end LogConcaveSampling.CycleTrace

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ScoreSlots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

def scoreSlots (e : ℕ) : ((Fin e ⊕ Unit) ⊕ Unit) ≃ Fin (e+2) where
  toFun := Sum.elim (Sum.elim (fun k => ⟨k.val+2,by omega⟩) (fun _ => ⟨0,by omega⟩))
    (fun _ => ⟨1,by omega⟩)
  invFun k := if h0 : k.val=0 then Sum.inl (Sum.inr ()) else
    if h1 : k.val=1 then Sum.inr () else Sum.inl (Sum.inl ⟨k.val-2,by omega⟩)
  left_inv := by
    intro t
    rcases t with (k|u)|u
    · simp only [Sum.elim_inl,Fin.val_mk,Nat.add_eq_zero_iff,OfNat.ofNat_ne_zero,and_false,
        ↓reduceDIte]
      have hn : k.val+2≠1 := by omega
      simp only [hn,↓reduceDIte,Nat.add_sub_cancel]
    · cases u; rfl
    · cases u; rfl
  right_inv := by
    intro k
    dsimp only []
    split_ifs with h0 h1
    · apply Fin.ext; exact h0.symm
    · apply Fin.ext; exact h1.symm
    · apply Fin.ext; dsimp; omega

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators

universe u

def contractSpatialSlots {K S T : Type u} (p : K → Prop) [DecidablePred p] :
    (({k // p k} ⊕ S) ⊕ ({k // ¬p k} ⊕ T)) ≃ K ⊕ (S ⊕ T) :=
  (Equiv.sumSumSumComm {k // p k} S {k // ¬p k} T).trans
    ((Equiv.sumCompl p).sumCongr (Equiv.refl (S ⊕ T)))

@[simp] lemma contractSpatialSlots_ll {K S T : Type u} (p : K → Prop) [DecidablePred p]
    (k : {k // p k}) : contractSpatialSlots (S:=S) (T:=T) p (Sum.inl (Sum.inl k))=Sum.inl k.val := rfl
@[simp] lemma contractSpatialSlots_lr {K S T : Type u} (p : K → Prop) [DecidablePred p]
    (s : S) : contractSpatialSlots (T:=T) p (Sum.inl (Sum.inr s))=Sum.inr (Sum.inl s) := rfl
@[simp] lemma contractSpatialSlots_rl {K S T : Type u} (p : K → Prop) [DecidablePred p]
    (k : {k // ¬p k}) : contractSpatialSlots (S:=S) (T:=T) p (Sum.inr (Sum.inl k))=Sum.inl k.val := rfl
@[simp] lemma contractSpatialSlots_rr {K S T : Type u} (p : K → Prop) [DecidablePred p]
    (t : T) : contractSpatialSlots (S:=S) p (Sum.inr (Sum.inr t))=Sum.inr (Sum.inr t) := rfl

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators

def spatialFieldSlots {K S : Type} {a b : ℕ} (h : K ⊕ S ≃ Fin a ⊕ Fin b) (e : ℕ) :
    (Fin e ⊕ K) ⊕ (S ⊕ Unit) ≃ (Fin a ⊕ Fin b) ⊕ (Unit ⊕ Fin e) :=
  (Equiv.sumAssoc (Fin e) K (S ⊕ Unit)).trans
    (((Equiv.refl (Fin e)).sumCongr (Equiv.sumAssoc K S Unit).symm).trans
      ((Equiv.sumComm (Fin e) ((K ⊕ S) ⊕ Unit)).trans
        ((Equiv.sumAssoc (K ⊕ S) Unit (Fin e)).trans (h.sumCongr (Equiv.refl (Unit ⊕ Fin e))))))

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal

def lastSlot (n : ℕ) : Fin n ⊕ Unit ≃ Fin (n+1) where
  toFun := Sum.elim Fin.castSucc (fun _ => Fin.last n)
  invFun := Fin.lastCases (Sum.inr ()) Sum.inl
  left_inv := by intro t; cases t <;> simp
  right_inv := by intro t; induction t using Fin.lastCases <;> simp

def scoreSpatialSlots (h : ℕ) : ((Fin h ⊕ Unit) ⊕ Unit) ≃ Fin (h+1) ⊕ (Empty ⊕ Unit) :=
  (lastSlot h).sumCongr (Equiv.emptySum Empty Unit).symm

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_ReindexedMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal NNReal Matrix.Norms.L2Operator

namespace TensorEnergy
def reindexedMatrix {I J K L : Type} (A : Matrix I J ℝ) (e : K ≃ I) (f : L ≃ J) :
    Matrix K L ℝ := fun k l => A (e k) (f l)

def splitFin {S : Type} [Fintype S] (p : ProperSplit S) :
    S ≃ Fin (Fintype.card (OutSlots p)) ⊕ Fin (Fintype.card (InSlots p)) :=
  (splitEquiv p).trans ((Equiv.sumComm (InSlots p) (OutSlots p)).trans
    ((Fintype.equivFin (OutSlots p)).sumCongr (Fintype.equivFin (InSlots p))))

end TensorEnergy

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_AnalyticBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal

def analyticBase (d j n : ℕ) : ℝ := (n:ℝ)+j+Real.log ((d:ℝ)+1)+1

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal

def adjointConstant (C s : ℕ) : ℕ := 100*C*(s+2)

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators

def scoreContractSlots (K S : Type) : K ⊕ (Empty ⊕ S) ≃ K ⊕ S :=
  (Equiv.refl K).sumCongr (Equiv.emptySum Empty S)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_Reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open scoped NNReal

lemma normalizedTensorMajorant_le {a : ℝ} (ha : 0 < a) (n : ℕ) :
    normalizedTensorMajorant n a ≤
      (10*((n:ℝ)+1))^(4*(n+1))*((Real.sqrt a)⁻¹)^(n-2) := by
  let B : ℝ := 10*((n:ℝ)+1)
  have hB : 1≤B := by dsimp [B]; nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  have hnB : (n:ℝ)≤B := by dsimp [B]; nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  have hn1B : (n:ℝ)+1≤B := by dsimp [B]; nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  have hpB : 2*Real.pi^2≤B^2 := by
    have hb10 : 10≤B := by dsimp [B]; nlinarith [Nat.cast_nonneg (α:=ℝ) n]
    nlinarith [Real.pi_lt_four,Real.pi_pos]
  have hfac : (n.factorial:ℝ)≤(n:ℝ)^n := by exact_mod_cast Nat.factorial_le_pow n
  have hfB : (n.factorial:ℝ)≤B^n :=
    hfac.trans (pow_le_pow_left₀ (Nat.cast_nonneg n) hnB n)
  have hhf : ((n.factorial:ℝ)^2)^2≤B^(4*n) := by
    have hh := pow_le_pow_left₀ (by positivity : (0:ℝ)≤n.factorial) hfB 4
    simpa only [←pow_mul,show 2*2=4 from rfl,Nat.mul_comm n 4] using hh
  have hhp : (2*Real.pi^2)^n≤B^(2*n) := by
    simpa only [←pow_mul] using pow_le_pow_left₀ (by positivity : 0≤2*Real.pi^2) hpB n
  have hhn : (((n+1:ℕ):ℝ)^(2*(n+1)))≤B^(2*(n+1)) := by
    simpa only [Nat.cast_add,Nat.cast_one] using pow_le_pow_left₀ (by positivity : 0≤(n:ℝ)+1) hn1B (2*(n+1))
  have hnum : (((n+1:ℕ):ℝ)^(2*(n+1))*(2*Real.pi^2)^n*((n.factorial:ℝ)^2)^2)≤
      B^(8*(n+1)) := by
    calc
      _ ≤ B^(2*(n+1))*B^(2*n)*B^(4*n) :=
        mul_le_mul (mul_le_mul hhn hhp (by positivity) (by positivity)) hhf
          (by positivity) (by positivity)
      _ = B^(2*(n+1)+2*n+4*n) := by rw [pow_add,pow_add]
      _ ≤ _ := pow_le_pow_right₀ hB (by omega)
  have hR : (((Real.sqrt a)⁻¹)^(n-2))^2=(a^(n-2))⁻¹ := by
    calc
      _ = (((Real.sqrt a)⁻¹)^2)^(n-2) := by simp only [←pow_mul]; congr 1; omega
      _ = (a⁻¹)^(n-2) := by rw [inv_pow,Real.sq_sqrt ha.le]
      _ = _ := inv_pow a (n-2)
  unfold normalizedTensorMajorant
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  change _≤(B^(4*(n+1))*((Real.sqrt a)⁻¹)^(n-2))^2
  conv_rhs => rw [mul_pow,hR,←pow_mul,show 4*(n+1)*2=8*(n+1) from by omega,←div_eq_mul_inv]
  exact div_le_div_of_nonneg_right hnum (pow_nonneg ha.le _)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_NormalizedScoreMajorant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal NNReal

lemma normalizedTensorMajorant_order_budget {a : ℝ} (ha : 0<a) (ha1 : a≤1)
    (e n : ℕ) (hn : n≤e+2) :
    normalizedTensorMajorant n a≤
      (40*((e:ℝ)+3))^(12*(e+1))*((Real.sqrt a)⁻¹)^e := by
  have hR : 1≤(Real.sqrt a)⁻¹ := (one_le_inv₀ (Real.sqrt_pos.mpr ha)).mpr
    (by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt ha1)
  have hB : 1≤40*((e:ℝ)+3) := by nlinarith [Nat.cast_nonneg (α:=ℝ) e]
  apply (normalizedTensorMajorant_le ha n).trans
  apply mul_le_mul
  · apply (pow_le_pow_left₀ (by positivity : 0≤10*((n:ℝ)+1))
      (show 10*((n:ℝ)+1)≤40*((e:ℝ)+3) by
        have hn' : (n:ℝ)≤(e:ℝ)+2 := by exact_mod_cast hn
        nlinarith [Nat.cast_nonneg (α:=ℝ) e]) _).trans
    exact pow_le_pow_right₀ hB (by omega)
  · exact pow_le_pow_right₀ hR (by omega)
  · positivity
  · positivity

def normalizedScoreMajorant (e : ℕ) (a : ℝ) : ℝ :=
  2+normalizedTensorMajorant (e+2) a+normalizedTensorMajorant (e+1) a

lemma normalizedScoreMajorant_nonneg (e : ℕ) (a : ℝ) : 0≤normalizedScoreMajorant e a :=
  add_nonneg (add_nonneg (by norm_num) (normalizedTensorMajorant_nonneg _ _))
    (normalizedTensorMajorant_nonneg _ _)

lemma normalizedScoreMajorant_budget {a : ℝ} (ha : 0<a) (ha1 : a≤1) (e : ℕ) :
    normalizedScoreMajorant e a≤
      (40*((e:ℝ)+3))^(16*(e+1))*((Real.sqrt a)⁻¹)^e := by
  let B : ℝ := 40*((e:ℝ)+3)
  let R : ℝ := (Real.sqrt a)⁻¹
  have hB : 4≤B := by dsimp [B]; nlinarith [Nat.cast_nonneg (α:=ℝ) e]
  have hB1 : 1≤B := by linarith
  have hR : 1≤R := (one_le_inv₀ (Real.sqrt_pos.mpr ha)).mpr
    (by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt ha1)
  have hP : 1≤B^(12*(e+1))*R^e := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hB1) (one_le_pow₀ hR)
  have hn1 := normalizedTensorMajorant_order_budget ha ha1 e (e+2) le_rfl
  have hn2 := normalizedTensorMajorant_order_budget ha ha1 e (e+1) (by omega)
  change normalizedScoreMajorant e a≤B^(16*(e+1))*R^e
  calc
    _ ≤ 4*(B^(12*(e+1))*R^e) := by dsimp [normalizedScoreMajorant]; linarith
    _ ≤ B*(B^(12*(e+1))*R^e) := mul_le_mul_of_nonneg_right hB (by positivity)
    _ = B^(12*(e+1)+1)*R^e := by rw [pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB1 (by omega)) (by positivity)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_FinSnocSlots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal NNReal

def finSnocSlots (m : ℕ) : Fin (m+1) ≃ Fin m ⊕ Unit :=
  finSumFinEquiv.symm.trans ((Equiv.refl (Fin m)).sumCongr finOneEquiv)

namespace TensorExpression

def profileConstant {n : ℕ} : TensorExpression n → ℕ
  | .jet q => 100*(q+3)
  | .perm _ A => 4*(A.profileConstant+n+1)
  | .contract (m:=m) (n:=n) _ _ A B =>
      4*(4*(4*(A.profileConstant+m+2)+4*(B.profileConstant+n+2)+m+n+1)+m+n+1)
  | .adjoint (n:=n) _ A => adjointConstant (4*(A.profileConstant+n+2)) n

end TensorExpression
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_Slice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal NNReal

namespace TensorSum
variable {S : Type} [Fintype S]

def momentBudget (A : TensorSum S) (d j : ℕ) (p : ℝ≥0∞) : ℝ≥0∞ :=
  ∑i,ENNReal.ofReal (polynomialBudget (A.term i).coefficient)*
    ((4*((A.term i).atom.expression.profileConstant:ℝ≥0∞))*
      ENNReal.ofReal (p.toReal+j+Real.log ((d:ℝ)+1)+1))^
        ((A.term i).atom.expression.profileConstant*(j+1))

end TensorSum
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_MatrixColor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal

def matrixZeroColor (d : ℕ) : (Fin d × Fin d) ≃ (Fin 0 ⊕ (Unit ⊕ Unit) → Fin d) where
  toFun p := Sum.elim Fin.elim0 (Sum.elim (fun _ => p.1) (fun _ => p.2))
  invFun c := (c (Sum.inr (Sum.inl ())),c (Sum.inr (Sum.inr ())))
  left_inv p := rfl
  right_inv c := by
    funext s
    rcases s with s | (s | s)
    · exact Fin.elim0 s
    · cases s; rfl
    · cases s; rfl

def matrixOneColor (d : ℕ) : (Fin d × Fin d × Fin d) ≃ (Fin 1 ⊕ (Unit ⊕ Unit) → Fin d) where
  toFun p := Sum.elim (fun _ => p.2.1) (Sum.elim (fun _ => p.1) (fun _ => p.2.2))
  invFun c := (c (Sum.inr (Sum.inl ())),c (Sum.inl 0),c (Sum.inr (Sum.inr ())))
  left_inv p := rfl
  right_inv c := by
    funext s
    rcases s with s | (s | s)
    · have hs : s=0 := Subsingleton.elim _ _
      subst s; rfl
    · cases s; rfl
    · cases s; rfl

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_InterpolationHessianBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal ENNReal RealInnerProductSpace

def interpolationHessianBudget : ℝ≥0 := ⟨1+Real.pi^2/4,by positivity⟩

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ClosedFieldMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

lemma norm_integral_sub_map_mean_le {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {μ : Measure (Point d)} [IsProbabilityMeasure μ]
    {f : Point d → E} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hi : Integrable (fun z : Point d => z) μ) :
    ‖(∫ z,f z ∂μ)-f (∫ z,z ∂μ)‖ ≤ (L:ℝ)*(∫ z,‖z-∫ w,w ∂μ‖ ∂μ) := by
  have hfi : Integrable f μ := integrable_lipschitz_comp_of_integrable hi hf
  have hd := hi.sub (integrable_const (∫ w,w ∂μ))
  have he : (∫ z,f z-f (∫ w,w ∂μ) ∂μ)=(∫ z,f z ∂μ)-f (∫ w,w ∂μ) := by
    rw [integral_sub hfi (integrable_const _),integral_const,probReal_univ,one_smul]
  rw [← he]
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_const_mul]
  apply integral_mono (hfi.sub (integrable_const _)).norm (hd.norm.const_mul _)
  intro z
  simpa only [dist_eq_norm,Pi.sub_apply] using hf.dist_le_mul z (∫ w,w ∂μ)

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_Extend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.TensorEnergy
open Function
open scoped Classical BigOperators

def zeroExtend {I J : Type*} (e : I ↪ J) (f : I → ℝ) : J → ℝ :=
  Function.extend e f (fun _ => 0)

@[simp] lemma zeroExtend_apply {I J : Type*} (e : I ↪ J) (f : I → ℝ) (i : I) :
    zeroExtend e f (e i)=f i := e.injective.extend_apply f _ i

end LogConcaveSampling.TensorEnergy

end

end

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open Function
open scoped Classical BigOperators

def slotEmbedding {S : Type*} {d D : ℕ} (e : S → Fin d ↪ Fin D) :
    (S → Fin d) ↪ (S → Fin D) where
  toFun c s := e s (c s)
  inj' := by intro a b h; funext s; exact (e s).injective (congrFun h s)

@[simp] lemma slotEmbedding_apply {S : Type*} {d D : ℕ} (e : S → Fin d ↪ Fin D)
    (c : S → Fin d) (s : S) : slotEmbedding e c s=e s (c s) := rfl

end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_ForestTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators

def forestTensor {d n : ℕ} {S : Type} (P : Fin n → Type) [∀i,Fintype (P i)]
    (A : (S ⊕ Fin n → Fin d) → ℝ)
    (B : ∀i,(P i ⊕ Unit → Fin d) → ℝ) (c : S ⊕ (Σi,P i) → Fin d) : ℝ :=
  ∑a : Fin n → Fin d,A (Sum.elim (fun s => c (Sum.inl s)) a) *
    ∏i,B i (Sum.elim (fun p => c (Sum.inr ⟨i,p⟩)) (fun _ => a i))

def forestRoot {n : ℕ} (S : Type) : S ⊕ Fin (n+1) ≃ (S ⊕ Unit) ⊕ Fin n where
  toFun := Sum.elim (fun s => Sum.inl (Sum.inl s))
    (Fin.cases (Sum.inl (Sum.inr ())) Sum.inr)
  invFun := Sum.elim (Sum.elim Sum.inl (fun _ => Sum.inr 0)) (fun i => Sum.inr i.succ)
  left_inv := by
    intro s
    rcases s with s|i
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  right_inv := by
    rintro ((s|u)|i) <;> rfl

def forestBranches {n : ℕ} (P : Fin (n+1) → Type) :
    (Σi,P i) ≃ P 0 ⊕ (Σi : Fin n,P i.succ) where
  toFun p := Fin.cases (fun z => Sum.inl z) (fun i z => Sum.inr ⟨i,z⟩) p.1 p.2
  invFun := Sum.elim (fun z => ⟨0,z⟩) (fun z => ⟨z.1.succ,z.2⟩)
  left_inv := by
    rintro ⟨i,z⟩
    revert z
    refine Fin.cases ?_ (fun i => ?_) i <;> intro z <;> rfl
  right_inv := by rintro (z|⟨i,z⟩) <;> rfl

def forestShuffle (S T : Type) : (S ⊕ Unit) ⊕ T ≃ (S ⊕ T) ⊕ Unit :=
  ((Equiv.sumAssoc S Unit T).trans
    ((Equiv.refl S).sumCongr (Equiv.sumComm Unit T))).trans (Equiv.sumAssoc S T Unit).symm

def forestOutput {n : ℕ} (S : Type) (P : Fin (n+1) → Type) :
    (S ⊕ (Σi : Fin n,P i.succ)) ⊕ P 0 ≃ S ⊕ (Σi,P i) :=
  ((Equiv.sumAssoc S (Σi : Fin n,P i.succ) (P 0)).trans
    ((Equiv.refl S).sumCongr (Equiv.sumComm _ _))).trans
      ((Equiv.refl S).sumCongr (forestBranches P).symm)

def forestColours (d n : ℕ) : (Fin (n+1) → Fin d) ≃ Fin d × (Fin n → Fin d) where
  toFun a := (a 0,fun i => a i.succ)
  invFun a := Fin.cons a.1 a.2
  left_inv a := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv a := rfl

lemma forestTensor_succ {d n : ℕ} {S : Type} (P : Fin (n+1) → Type) [∀i,Fintype (P i)]
    (A : (S ⊕ Fin (n+1) → Fin d) → ℝ) (B : ∀i,(P i ⊕ Unit → Fin d) → ℝ)
    (c : S ⊕ (Σi,P i) → Fin d) :
    forestTensor P A B c = singleContract
      (fun z => forestTensor (fun i : Fin n => P i.succ)
        (fun a => A (a ∘ forestRoot S)) (fun i => B i.succ) (z ∘ forestShuffle S _))
      (B 0) (c ∘ forestOutput S P) := by
  unfold forestTensor singleContract
  rw [←(forestColours d n).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [show ∀a,(forestColours d n).symm a=Fin.cons a.1 a.2 from fun _ => rfl,
    Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  have hA : Sum.elim (fun s => c (Sum.inl s)) (Fin.cons z a) =
      (Sum.elim
        (fun s => Sum.elim
          (fun s => (c ∘ forestOutput S P) (Sum.inl s)) (fun _ => z)
            (forestShuffle S (Σi : Fin n,P i.succ) (Sum.inl s))) a) ∘ forestRoot S := by
    funext s
    rcases s with s|i
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  rw [hA]
  have hB (i : Fin n) :
      B i.succ (Sum.elim (fun p => c (Sum.inr ⟨i.succ,p⟩)) (fun _ => a i)) =
      B i.succ (Sum.elim
        (fun p => Sum.elim (fun s => (c ∘ forestOutput S P) (Sum.inl s)) (fun _ => z)
          (forestShuffle S (Σi : Fin n,P i.succ) (Sum.inr ⟨i,p⟩))) (fun _ => a i)) := rfl
  simp only [hB]
  have h0 : B 0 (Sum.elim (fun p => c (Sum.inr ⟨0,p⟩)) (fun _ => z)) =
      B 0 (Sum.elim (fun p => (c ∘ forestOutput S P) (Sum.inr p)) (fun _ => z)) := rfl
  rw [h0]
  simp only [Function.comp_def]
  ring

end LogConcaveSampling.TensorEnergy

end

end

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators RealInnerProductSpace

def multilinearTensor {d : ℕ} {I : Type} (A : ContinuousMultilinearMap ℝ (fun _ : I => Point d) (Point d))
    (c : Unit ⊕ I → Fin d) : ℝ :=
  inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl ())))
    (A (fun i => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr i))))

lemma multilinear_coordinate_expansion {d : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (A : ContinuousMultilinearMap ℝ (fun _ : I => Point d) (Point d))
    (v : I → Point d) (o : Fin d) :
    inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ o) (A v) =
      ∑a : I → Fin d,
        inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ o)
          (A (fun i => EuclideanSpace.basisFun (Fin d) ℝ (a i))) *
        ∏i,inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ (a i)) (v i) := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hv : v=fun i => ∑j : Fin d,inner ℝ (b j) (v i) • b j := by
    funext i
    exact (b.sum_repr' (v i)).symm
  conv_lhs => rw [hv]
  rw [A.map_sum]
  simp only [inner_sum,A.map_smul_univ,inner_smul_right]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

lemma multilinearTensor_compAlong {d n : ℕ} (c : OrderedFinpartition n)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Point d) (Point d))
    (B : ∀i,ContinuousMultilinearMap ℝ (fun _ : Fin (c.partSize i) => Point d) (Point d))
    (a : Unit ⊕ Fin n → Fin d) :
    multilinearTensor (c.compAlongOrderedFinpartition A B) a =
      forestTensor (fun i => Fin (c.partSize i)) (multilinearTensor A)
        (fun i q => multilinearTensor (B i) (q ∘ Equiv.sumComm Unit (Fin (c.partSize i))))
        (a ∘ (Equiv.refl Unit).sumCongr c.equivSigma) := by
  unfold multilinearTensor forestTensor
  rw [OrderedFinpartition.compAlongOrderFinpartition_apply,multilinear_coordinate_expansion]
  exact Fintype.sum_equiv (Equiv.refl _) _ _ (fun _ => rfl)

end LogConcaveSampling.TensorEnergy

end

end

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators RealInnerProductSpace

def arrayTensor {d : ℕ} {S I : Type}
    (A : ContinuousMultilinearMap ℝ (fun _ : I => Point d) ((S → Fin d) → ℝ))
    (c : S ⊕ I → Fin d) : ℝ :=
  A (fun i => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr i)))
    (fun s => c (Sum.inl s))

end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_Squared
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators

namespace TensorEnergy

def squared {S : Type} [Fintype S] {d : ℕ} (T : (S → Fin d) → ℝ) : ℝ := ∑c,(T c)^2
end TensorEnergy
open TensorEnergy

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal
open TensorEnergy

def insideZeroColor (K S : Type) (d : ℕ) :
    ((K ⊕ S → Fin d) × Fin d) ≃ (K ⊕ (S ⊕ Unit) → Fin d) where
  toFun p := Sum.elim (fun k => p.1 (Sum.inl k)) (Sum.elim (fun s => p.1 (Sum.inr s)) (fun _ => p.2))
  invFun c := (Sum.elim (fun k => c (Sum.inl k)) (fun s => c (Sum.inr (Sum.inl s))),c (Sum.inr (Sum.inr ())))
  left_inv p := by apply Prod.ext; funext a; cases a <;> rfl; rfl
  right_inv c := by funext a; rcases a with a | (a | a); rfl; rfl; cases a; rfl

def insideOneColor (K S : Type) (d : ℕ) :
    ((K ⊕ S → Fin d) × Fin d × Fin d) ≃ ((Unit ⊕ K) ⊕ (S ⊕ Unit) → Fin d) where
  toFun p := Sum.elim (Sum.elim (fun _ => p.2.1) (fun k => p.1 (Sum.inl k)))
    (Sum.elim (fun s => p.1 (Sum.inr s)) (fun _ => p.2.2))
  invFun c := (Sum.elim (fun k => c (Sum.inl (Sum.inr k))) (fun s => c (Sum.inr (Sum.inl s))),
    c (Sum.inl (Sum.inl ())),c (Sum.inr (Sum.inr ())))
  left_inv p := by apply Prod.ext; funext a; cases a <;> rfl; rfl
  right_inv c := by funext a; rcases a with (a | a) | (a | a); cases a; rfl; rfl; rfl; cases a; rfl

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_SplitBundle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators

lemma _root_.OAI.OrderedFinpartition.sum_partSize {n : ℕ} (c : OrderedFinpartition n) :
    ∑i,c.partSize i=n := by
  simpa using Fintype.card_congr c.equivSigma

lemma _root_.OAI.OrderedFinpartition.unique_of_partSize_eq {n : ℕ} (c : OrderedFinpartition n)
    (i : Fin c.length) (hi : c.partSize i=n) (j : Fin c.length) : j=i := by
  by_contra hji
  have hs := Finset.sum_erase_add Finset.univ (fun k => c.partSize k) (Finset.mem_univ i)
  rw [_root_.OAI.OrderedFinpartition.sum_partSize c,hi] at hs
  have hz : ∑k∈Finset.univ.erase i,c.partSize k=0 := by omega
  have hh := Finset.single_le_sum (fun k (_ : k∈Finset.univ.erase i) => Nat.zero_le (c.partSize k))
    (Finset.mem_erase.mpr ⟨hji,Finset.mem_univ j⟩)
  rw [hz] at hh
  have := c.partSize_pos j
  omega

lemma _root_.OAI.OrderedFinpartition.length_eq_one_of_partSize_eq {n : ℕ} (c : OrderedFinpartition n)
    (i : Fin c.length) (hi : c.partSize i=n) : c.length=1 := by
  have hp : 0 < c.length := Nat.zero_lt_of_lt i.isLt
  have hle : c.length≤1 := by
    by_contra h
    have hgt : 1 < c.length := by omega
    have he := (_root_.OAI.OrderedFinpartition.unique_of_partSize_eq c i hi ⟨0,hp⟩).trans
      (_root_.OAI.OrderedFinpartition.unique_of_partSize_eq c i hi ⟨1,hgt⟩).symm
    have hh := congrArg Fin.val he
    change (0:ℕ)=1 at hh
    omega
  omega

lemma partition_majorant_linear {n : ℕ} {M B N : ℕ → ℝ} {z : ℝ}
    (hM : ∀k,0≤M k) (hB : ∀k,0≤B k) (hz : 0≤z)
    (hN : ∀k<n,N k=B k) (hNz : N n=z) :
    (∑c : OrderedFinpartition n,M c.length*∏i,N (c.partSize i))≤
      (Fintype.card (OrderedFinpartition n):ℝ)*M 1*z+
        ∑c : OrderedFinpartition n,M c.length*∏i,B (c.partSize i) := by
  have hb (c : OrderedFinpartition n) : M c.length*(∏i,N (c.partSize i))≤
      M 1*z+M c.length*∏i,B (c.partSize i) := by
    by_cases hh : ∃i,c.partSize i=n
    · obtain ⟨i,hi⟩ := hh
      have hp : (∏j,N (c.partSize j))=z := by
        rw [Finset.prod_eq_single i]
        · rw [hi,hNz]
        · intro j _ hji
          exact (hji (_root_.OAI.OrderedFinpartition.unique_of_partSize_eq c i hi j)).elim
        · simp
      have hMl : M c.length=M 1 := congrArg M (_root_.OAI.OrderedFinpartition.length_eq_one_of_partSize_eq c i hi)
      rw [hp,hMl]
      exact le_add_of_nonneg_right (mul_nonneg (hM 1) (Finset.prod_nonneg (fun j _ => hB _)))
    · have hp : (∏i,N (c.partSize i))=∏i,B (c.partSize i) := by
        apply Finset.prod_congr rfl
        intro i _
        exact hN _ (lt_of_le_of_ne (c.partSize_le i) (fun he => hh ⟨i,he⟩))
      rw [hp]
      exact le_add_of_nonneg_left (mul_nonneg (hM 1) hz)
  calc
    _ ≤ ∑c : OrderedFinpartition n,(M 1*z+M c.length*∏i,B (c.partSize i)) :=
      Finset.sum_le_sum (fun c _ => hb c)
    _ = _ := by rw [Finset.sum_add_distrib]; simp [mul_assoc]
end LogConcaveSampling.TensorEnergy

end

end

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open Set Function
open scoped BigOperators Classical Matrix.Norms.L2Operator

universe u
variable {S : Type u} [Fintype S] {d : ℕ}

abbrev SplitBundle (S : Type u) [Fintype S] (d : ℕ) :=
  ∀p : ProperSplit S, Matrix (OutSlots p → Fin d) (InSlots p → Fin d) ℝ

def splitBundleLinear : ((S → Fin d) → ℝ) →ₗ[ℝ] SplitBundle S d where
  toFun T p := splitMatrix T p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def splitBundle : ((S → Fin d) → ℝ) →L[ℝ] SplitBundle S d :=
  splitBundleLinear.toContinuousLinearMap

end LogConcaveSampling.TensorEnergy

end

end

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators

lemma _root_.OAI.OrderedFinpartition.sum_pred_partSize {n : ℕ} (c : OrderedFinpartition n) :
    (∑i,(c.partSize i-1))+c.length=n := by
  have he : (∑i,(c.partSize i-1))+(∑_i : Fin c.length,1)=∑i,c.partSize i := by
    rw [←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (c.partSize_pos i))
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one,
    _root_.OAI.OrderedFinpartition.sum_partSize c] using he

lemma partition_scale {n : ℕ} (hn : 0<n) (c : OrderedFinpartition n)
    (A B : ℕ → ℝ) (R : ℝ) :
    (A c.length/R^(c.length-1))*(∏i,B (c.partSize i)/R^(c.partSize i-1))=
      (A c.length*(∏i,B (c.partSize i)))/R^(n-1) := by
  rw [Finset.prod_div_distrib,←mul_div_mul_comm,Finset.prod_pow_eq_pow_sum,←pow_add]
  have he : c.length-1+(∑i,(c.partSize i-1))=n-1 := by
    have := _root_.OAI.OrderedFinpartition.sum_pred_partSize c
    have := c.length_pos hn
    omega
  rw [he]

lemma partition_sum_scale {n : ℕ} (hn : 0<n) (A B : ℕ → ℝ) (R : ℝ) :
    (∑c : OrderedFinpartition n,(A c.length/R^(c.length-1))*(∏i,B (c.partSize i)/R^(c.partSize i-1)))=
      (∑c : OrderedFinpartition n,A c.length*(∏i,B (c.partSize i)))/R^(n-1) := by
  simp only [partition_scale hn,Finset.sum_div]

lemma gronwallBound_div (δ K ε t q : ℝ) :
    gronwallBound (δ/q) K (ε/q) t=gronwallBound δ K ε t/q := by
  by_cases hK : K=0
  · simp only [hK,gronwallBound_K0]; ring
  · simp only [gronwallBound_of_K_ne_0 hK]; ring
end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_SpatialTensorContinuous
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Function
open scoped Classical BigOperators RealInnerProductSpace

namespace TensorEnergy

lemma multilinearTensor_id_higher {d n : ℕ} (y : Point d) :
    multilinearTensor (iteratedFDeriv ℝ (n+2) (id : Point d → Point d) y)=0 := by
  funext c
  simp only [multilinearTensor,iteratedFDeriv_succ_apply_right,fderiv_id,
    iteratedFDeriv_succ_const,Pi.zero_apply,zero_apply]
  simp

end TensorEnergy
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_NormalizedTensorMajorantScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set
open scoped NNReal

lemma normalizedTensorMajorant_scale {n : ℕ} {a R : ℝ} (hR : 0<R) (ha : R^2≤a) :
    normalizedTensorMajorant n a≤normalizedTensorMajorant n 1/R^(n-2) := by
  let C : ℝ := ((n+1:ℕ):ℝ)^(2*(n+1))*(2*Real.pi^2)^n*((n.factorial:ℝ)^2)^2
  have hC : 0≤C := by dsimp [C]; positivity
  have hden : 0<(R^2)^(n-2) := pow_pos (sq_pos_of_pos hR) _
  have he : (R^2)^(n-2)=(R^(n-2))^2 := by rw [←pow_mul,←pow_mul]; congr 1; omega
  calc
    _ ≤ Real.sqrt (C/(R^2)^(n-2)) := by
      apply Real.sqrt_le_sqrt
      exact div_le_div_of_nonneg_left hC hden (pow_le_pow_left₀ (sq_nonneg R) ha _)
    _ = _ := by
      rw [Real.sqrt_div hC,he,Real.sqrt_sq (pow_nonneg hR.le _)]
      simp [normalizedTensorMajorant,C]

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_MatrixArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function
open scoped NNReal BigOperators

namespace TensorEnergy
lemma multilinearTensor_const_smul {d n : ℕ} (a : ℝ)
    (f : Point d → Point d) (hf : ContDiff ℝ (⊤:ℕ∞) f) (y : Point d) :
    multilinearTensor (iteratedFDeriv ℝ n (fun z => a • f z) y)=
      fun c => a*multilinearTensor (iteratedFDeriv ℝ n f y) c := by
  funext c
  rw [iteratedFDeriv_const_smul_apply' (hf.contDiffAt.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤)))]
  simp [multilinearTensor,real_inner_smul_right]
end TensorEnergy

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators RealInnerProductSpace

def matrixArray (d : ℕ) : (Point d →L[ℝ] Point d) →L[ℝ] ((Unit ⊕ Unit → Fin d) → ℝ) :=
  ContinuousLinearMap.pi fun c =>
    (innerSL ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl ())))).comp
      (ContinuousLinearMap.apply ℝ (Point d) (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr ()))))

def jacobianSlots (n : ℕ) : (Unit ⊕ Unit) ⊕ Fin n ≃ Unit ⊕ Fin (n+1) where
  toFun := Sum.elim (Sum.elim Sum.inl (fun _ => Sum.inr (Fin.last n)))
    (fun i => Sum.inr i.castSucc)
  invFun := Sum.elim (fun u => Sum.inl (Sum.inl u))
    (Fin.lastCases (Sum.inl (Sum.inr ())) Sum.inr)
  left_inv := by rintro ((u|u)|i) <;> simp
  right_inv := by
    rintro (u|i)
    · rfl
    · refine Fin.lastCases ?_ (fun i => ?_) i <;> simp

@[simp] lemma jacobianSlots_symm_out (n : ℕ) :
    (jacobianSlots n).symm (Sum.inl ())=Sum.inl (Sum.inl ()) := rfl
@[simp] lemma jacobianSlots_symm_last (n : ℕ) :
    (jacobianSlots n).symm (Sum.inr (Fin.last n))=Sum.inl (Sum.inr ()) := by simp [jacobianSlots]
@[simp] lemma jacobianSlots_symm_init {n : ℕ} (i : Fin n) :
    (jacobianSlots n).symm (Sum.inr i.castSucc)=Sum.inr i := by simp [jacobianSlots]

end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_ArrayRelabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators RealInnerProductSpace

def arrayRelabel {d : ℕ} {S T : Type} [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T] (e : S ≃ T) :
    ((S → Fin d) → ℝ) →L[ℝ] ((T → Fin d) → ℝ) :=
  ContinuousLinearMap.pi (fun c => ContinuousLinearMap.proj (c ∘ e))

end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TensorGrad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators
open TensorEnergy

def gradSpatialSlots (K S : Type) : ((K ⊕ Unit) ⊕ S) ≃ K ⊕ (S ⊕ Unit) where
  toFun := Sum.elim (Sum.elim Sum.inl (fun u => Sum.inr (Sum.inr u))) (fun s => Sum.inr (Sum.inl s))
  invFun := Sum.elim (fun k => Sum.inl (Sum.inl k)) (Sum.elim Sum.inr (fun u => Sum.inl (Sum.inr u)))
  left_inv a := by rcases a with (a | a) | a <;> rfl
  right_inv a := by rcases a with a | (a | a) <;> rfl

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal
open TensorEnergy

def productEnergyBudget (C E : ℕ → ℝ) (j : ℕ) : ℝ :=
  2^j*∑s∈(Finset.univ : Finset (Fin j)).powerset,(C s.card)^2*E (j-s.card+1)

def adjointEnergyBudget (K : ℝ) (C E : ℕ → ℝ) (j : ℕ) : ℝ :=
  2*(E (j+1)+K*E j+2^j*∑s∈(Finset.univ : Finset (Fin j)).powerset.erase ∅,
    (C s.card)^2*E (j-s.card))

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TensorVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace
open TensorEnergy

def leftCoordinates (d e : ℕ) : Fin d ↪ Fin (d+e) := ⟨Fin.castAdd e,Fin.castAdd_injective d e⟩
def rightCoordinates (d e : ℕ) : Fin e ↪ Fin (d+e) := ⟨Fin.natAdd d,Fin.natAdd_injective e d⟩

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace
open TensorEnergy

def pairLabels {D : ℕ} (i j : Fin D) : Unit ⊕ Unit → Fin D := Sum.elim (fun _ => i) (fun _ => j)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_ChainTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def chainTaylor (J : ℕ → ℝ → E) (n : ℕ) (a x : ℝ) : E :=
  ∑k∈Finset.range (n+1),((k.factorial:ℝ)⁻¹*(x-a)^k) • J k a

end LogConcaveSampling.Quadrature

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_CenteringPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy Quadrature

def centeringGradientBound (lam : ℝ≥0) (r T : ℝ) (h : 0≤(Real.pi^2/2)*T*((lam:ℝ)*r)) : ℝ≥0 :=
  (1+‖r*T‖₊*⟨(Real.pi^2/2)*T*((lam:ℝ)*r),h⟩)+1

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TransportCorrectionMajorant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy

def harmonicGradientBound : ℝ≥0 := ⟨2+Real.pi^2,by positivity⟩

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_CenteringStateBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory TensorEnergy Quadrature
open scoped Classical BigOperators NNReal RealInnerProductSpace

local instance centeringStateBudgetDecidableEqUnit : DecidableEq Unit := Classical.decEq _

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_CenteringStateBudgetNonneg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory TensorEnergy Quadrature
open scoped Classical BigOperators NNReal RealInnerProductSpace

local instance centeringStateBudgetNonnegDecidableEqUnit : DecidableEq Unit := Classical.decEq _

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_HarmonicCorrectionBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy Quadrature

local instance instDecidableEqUnit_solutions_4 : DecidableEq Unit := Classical.decEq _

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_AngleNodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy Quadrature

local instance instDecidableEqUnit_solutions_5 : DecidableEq Unit := Classical.decEq _

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_LogDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal ENNReal

namespace TensorSum
variable {S : Type} [Fintype S]

def logDegree (A : TensorSum S) (j : ℕ) : ℕ :=
  ∑i,(A.term i).atom.expression.profileConstant*(j+1)

def logCoefficient (A : TensorSum S) (j : ℕ) (p : ℝ≥0∞) : ℝ :=
  ∑i,polynomialBudget (A.term i).coefficient*
    (4*((A.term i).atom.expression.profileConstant:ℝ)*(p.toReal+j+1))^
      ((A.term i).atom.expression.profileConstant*(j+1))

end TensorSum
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_MeanMaterialVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal

def probabilityTimeClamp (T t : ℝ) : ℝ := min (max t 0) T

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ProbabilityNodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy Quadrature

local instance instDecidableEqUnit_solutions_6 : DecidableEq Unit := Classical.decEq _

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory TensorEnergy Quadrature
open scoped Classical BigOperators NNReal RealInnerProductSpace

local instance instDecidableEqUnit_solutions_7 : DecidableEq Unit := Classical.decEq _

def finiteCoordinateProjection {I J : Type*} [Fintype I] [Fintype J]
    (e : I ↪ J) : EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ I :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => PiLp.proj 2 (fun _ : J => ℝ) (e i)))

def meanOutputEmbedding (d : ℕ) : Fin d ↪ (Unit → Fin (d+d)) :=
  ⟨fun i _ => leftCoordinates d d i,fun _ _ h => (leftCoordinates d d).injective (congrFun h ())⟩

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators NNReal

def probabilityMeanLipschitz (lam : ℝ≥0) (r : ℝ) : ℝ≥0 :=
  ⟨(Real.pi^2/2)*(lam:ℝ)*r^2,by positivity⟩

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TerminalTransportConstant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function MeasureTheory ProbabilityTheory
open scoped NNReal

def terminalTransportConstant : ℝ :=
  2*(|gronwallBound 0 (Real.pi^2+1) 1 1|+1)+1

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_NodeLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.FinitePicard
open MeasureTheory
open scoped BigOperators NNReal RealInnerProductSpace

variable {Ω E I : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]
  [NormedAddCommGroup E]

lemma lipschitz_zero_shift {K : ℝ≥0} {φ : E → E} (hφ : LipschitzWith K φ) :
    LipschitzWith K (fun x => φ x-φ 0) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_sub_right] using hφ.dist_le_mul x y

def nodeLp {K : ℝ≥0} {φ : E → E} (hφ : LipschitzWith K φ) (f : Lp E 2 ν) : Lp E 2 ν :=
  (lipschitz_zero_shift hφ).compLp (by simp) f + Lp.const 2 ν (φ 0)

end LogConcaveSampling.FinitePicard

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_KernelTransportAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory TensorEnergy Quadrature
open scoped Classical BigOperators NNReal

local instance instDecidableEqUnit_solutions_9 : DecidableEq Unit := Classical.decEq _

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_ArrayMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set Filter MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

namespace TensorSum

def matrixComp (A B : TensorSum (Unit ⊕ Unit)) : TensorSum (Unit ⊕ Unit) :=
  A.contract (B.relabel (Equiv.sumComm Unit Unit))

lemma matrixComp_weight {A B : TensorSum (Unit ⊕ Unit)} {u v : ℕ}
    (hA : A.weightLE u) (hB : B.weightLE v) : (A.matrixComp B).weightLE (u+v) :=
  weightLE_contract hA (weightLE_relabel hB _)

def firstMatrix : TensorSum (Unit ⊕ Unit) :=
  (pure (TensorAtom.jetList [()] (by simp) (by intro u; cases u; simp) (by simp))).relabel
    (Equiv.sumComm Unit Unit)

lemma firstMatrix_weight : firstMatrix.weightLE 0 := by
  apply weightLE_relabel
  apply weightLE_pure
  simp only [TensorAtom.jetList_weight,List.length_singleton,Nat.sub_self,le_refl]

end TensorSum

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_Jet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory Set
open scoped NNReal ENNReal

namespace TimeJet
variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def jet (f : ℝ × X → E) : ℕ → ℝ × X → E
  | 0 => f
  | n+1 => fun p => fderiv ℝ (jet f n) p (1,0)

end TimeJet

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_IdentityOutputEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory TensorEnergy Quadrature
open scoped Classical BigOperators NNReal RealInnerProductSpace

local instance identityOutputEmbeddingDecidableEqUnit : DecidableEq Unit :=
  Classical.decEq _

def identityOutputEmbedding (d : ℕ) : Fin d ↪ (Unit → Fin d) :=
  ⟨fun i _ => i,fun _ _ h => congrFun h ()⟩

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_CenteringVelocityInterpolationRms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature TensorEnergy
open scoped Classical BigOperators NNReal RealInnerProductSpace

local instance centeringVelocityInterpolationRmsDecidableEqUnit : DecidableEq Unit := Classical.decEq _

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_CenteringStateQuadratureBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature TensorEnergy
open scoped Classical BigOperators NNReal

local instance instDecidableEqUnit_solutions_10 : DecidableEq Unit := Classical.decEq _

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_CircuitD
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal

def circuitGrowthConstant : ℝ := 8*(terminalTransportConstant+1)*(Real.pi+1)
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ProbabilityNormalizedTerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

def probabilityNormalizedTerm (d k n : ℕ) (h : ℝ) : ℝ :=
  (1+Real.log ((d:ℝ)+1))^k*(2*h)^(n+1)

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory Quadrature
open scoped NNReal BigOperators

def numericalContractionCoefficient (Ap Ah Lp : ℝ≥0) : ℝ :=
  1+((Ap:ℝ)+Ah+Lp)*(Real.pi^2/2)
def numericalErrorCoefficient (C J : ℝ) : ℝ :=
  1+4*|C|+|J|+2*circuitGrowthConstant

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_KernelAnalyticNormalizedBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling
open Filter Asymptotics
open scoped Topology

def dimensionLog (d : ℕ) : ℝ := 1+Real.log ((d:ℝ)+1)

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Filter Asymptotics
open scoped Topology

def LogPowerRate (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∃k : ℕ, f =O[atTop] (fun d => dimensionLog d^k*(d:ℝ)^(-a))

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_Program
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace LogConcaveSampling.OracleCompiler

namespace Program
variable {Ω O : Type*} [MeasurableSpace Ω] [MeasurableSpace O] {d q : ℕ}

def mask (n : ℕ) (h : Transcript d q) : Transcript d q :=
  fun i => if i.val < n then h i else 0

end Program
end LogConcaveSampling.OracleCompiler

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace LogConcaveSampling.SeedCompiler

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def slotSum (a : ι → ℝ) (g : ι → E) : E := ∑ i, a i • g i

def slotTransform (c : ℝ) (a : ι → ℝ) (g : ι → E) : ι → E :=
  fun i => g i - (c * a i) • slotSum a g

def restored (c : ℝ) (a : ι → ℝ) : ((ι → E) × E) →L[ℝ] (ι → E) :=
  ContinuousLinearMap.pi fun i =>
    ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (ι → E) E)) -
    (c * a i) • (∑ j, a j •
      ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℝ (ι → E) E))) -
    a i • ContinuousLinearMap.snd ℝ (ι → E) E

omit [DecidableEq ι] in
@[simp] lemma restored_apply (c : ℝ) (a : ι → ℝ) (g : ι → E) (z : E) (i : ι) :
    restored c a (g,z) i = slotTransform c a g i - a i • z := by
  simp [restored, slotTransform, slotSum]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def sqrtCoefficient (a : ι → ℝ) : ℝ := 1 / (1 + Real.sqrt (1 - ∑ i, a i ^ 2))

end LogConcaveSampling.SeedCompiler

namespace LogConcaveSampling.SeedCompiler
variable {ι E O : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def ShiftInvariant (r : ℝ) (v : ι → ℝ) (M : E → (ι → E) → O) : Prop :=
  ∀ x Δ g, M (x + r • Δ) (fun i => g i + v i • Δ) = M x g

end LogConcaveSampling.SeedCompiler

namespace LogConcaveSampling.SeedCompiler
variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def inverseCoefficient (a : ι → ℝ) : ℝ :=
  -sqrtCoefficient a / Real.sqrt (1 - ∑ i, a i ^ 2)

end LogConcaveSampling.SeedCompiler

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_TerminalMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace LogConcaveSampling.SeedCompiler
open OracleCompiler
open OracleCompiler.Program

def terminalShift (n : ℕ) : Fin (n+1) → ℝ := fun i => if i = 0 then -1 else 0

end LogConcaveSampling.SeedCompiler

end
end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_Forward
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal

def samplingEnvelope (d k n N : ℕ) (C q h : ℝ) : ℝ :=
  4*(2*C*dimensionLog d^k*(2*h)^(n+1)+circuitGrowthConstant*q^N)^2

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_ChildNoise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory OracleCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def childNoise (n w : ℝ) : ℝ := n/(2*(w+1))

def reserve (n w : ℝ) {k : ℕ} (a : Fin k → ℝ) : ℝ :=
  Real.sqrt (n^2-(childNoise n w)^2*∑i,a i^2)

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def declaredNoise (n A : ℝ) : ℝ := n/(2*A)
def declaredReserve (n A : ℝ) {k : ℕ} (a : Fin k → ℝ) : ℝ :=
  Real.sqrt (n^2-(declaredNoise n A)^2*∑i,a i^2)

end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_Cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open Set MeasureTheory
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma sqrt_one_sub_sq_gap {ρ : ℝ} (hρ : ρ∈Icc (0:ℝ) 1) :
    1-ρ≤Real.sqrt (1-ρ^2) := by
  have hp : 0≤1-ρ^2 := by nlinarith [hρ.1,hρ.2]
  have hs := Real.sq_sqrt hp
  nlinarith [Real.sqrt_nonneg (1-ρ^2),hρ.1,hρ.2]

lemma mean_direct_ratio {ρ T θ : ℝ} (hT : 1/2≤T) (hT1 : T<1)
    (hρ : ρ∈Icc (0:ℝ) T) (hθ : θ^2≤Real.sqrt (1-T^2)) :
    0<Real.sqrt (1-ρ^2) ∧ |(1-ρ*Real.cos θ/T)/Real.sqrt (1-ρ^2)|≤3 := by
  have hT0 : 0<T := by linarith
  have hρ1 : ρ<1 := hρ.2.trans_lt hT1
  have hp : 0<1-ρ^2 := by nlinarith [hρ.1]
  have hs : 0<Real.sqrt (1-ρ^2) := Real.sqrt_pos.mpr hp
  have hc := Real.one_sub_sq_div_two_le_cos (x:=θ)
  have hcos := Real.cos_le_one θ
  have hn : 0≤1-ρ*Real.cos θ/T := by
    rw [sub_nonneg,div_le_iff₀ hT0,one_mul]
    exact (mul_le_mul_of_nonneg_left hcos hρ.1).trans (by simpa using hρ.2)
  have hτ := sqrt_one_sub_sq_gap ⟨hρ.1,hρ1.le⟩
  have hθ' : θ^2≤Real.sqrt (1-ρ^2) := hθ.trans (Real.sqrt_le_sqrt (by nlinarith [hρ.1,hρ.2]))
  have hr : ρ*Real.cos θ≥ρ*(1-θ^2/2) := mul_le_mul_of_nonneg_left hc hρ.1
  have hd : (1-ρ*Real.cos θ/T)≤3*Real.sqrt (1-ρ^2) := by
    have hm₁ := mul_le_mul_of_nonneg_left hθ' hρ.1
    have hm₂ := mul_le_mul_of_nonneg_right hρ.2 (Real.sqrt_nonneg (1-ρ^2))
    have hm₃ := mul_le_mul_of_nonneg_right hT (Real.sqrt_nonneg (1-ρ^2))
    have hnum : T-ρ*Real.cos θ≤3*Real.sqrt (1-ρ^2)*T := by nlinarith
    calc
      1-ρ*Real.cos θ/T=(T-ρ*Real.cos θ)/T := by rw [sub_div,div_self hT0.ne']
      _≤3*Real.sqrt (1-ρ^2) := (div_le_iff₀ hT0).mpr hnum
  refine ⟨hs,?_⟩
  rw [abs_of_nonneg (div_nonneg hn hs.le),div_le_iff₀ hs]
  exact hd

lemma sample_direct_ratio {ρ T : ℝ} (_hT : 0≤T) (hT1 : T<1) (hρ : ρ∈Icc (0:ℝ) T) :
    0<Real.sqrt (1-ρ^2) ∧ |(1-ρ*T)/Real.sqrt (1-ρ^2)|≤2 := by
  have hρ1 : ρ<1 := hρ.2.trans_lt hT1
  have hp : 0<1-ρ^2 := by nlinarith [hρ.1]
  have hs : 0<Real.sqrt (1-ρ^2) := Real.sqrt_pos.mpr hp
  have hn : 0≤1-ρ*T := by nlinarith [hρ.1,mul_nonneg hρ.1 (sub_nonneg.mpr hT1.le)]
  have hτ := sqrt_one_sub_sq_gap ⟨hρ.1,hρ1.le⟩
  refine ⟨hs,?_⟩
  rw [abs_of_nonneg (div_nonneg hn hs.le),div_le_iff₀ hs]
  nlinarith [mul_nonneg hρ.1 (sub_nonneg.mpr hρ.2),sq_nonneg (1-ρ)]

end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_RoutineKind
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open scoped Classical

inductive RoutineKind where
  | mean | sample
  deriving DecidableEq

structure RoutineLabel where
  kind : RoutineKind
  b : ℝ
  p : ℝ

def RoutineLabel.terminal (L : RoutineLabel) : Prop := L.p≤L.b

inductive RoutineStep (t : ℝ) : RoutineLabel → RoutineLabel → Prop where
  | meanFinal (b p : ℝ) : RoutineStep t ⟨.mean,b,p⟩ ⟨.mean,b+t,p⟩
  | sampleFinal (b p : ℝ) : RoutineStep t ⟨.sample,b,p⟩ ⟨.mean,b,p⟩
  | internal (k k' : RoutineKind) (b p : ℝ) :
      RoutineStep t ⟨k,b,p⟩ ⟨k',b-10*t,p-1/4⟩

def RoutineLabel.rank (t : ℝ) (L : RoutineLabel) : ℕ :=
  2*⌈(L.p-L.b)/t⌉₊+(match L.kind with | .mean => 0 | .sample => 1)

lemma ceil_gap_drop {t x y : ℝ} (ht : 0<t) (hx : 0<x) (hy : y≤x-t) :
    ⌈y/t⌉₊<⌈x/t⌉₊ := by
  have hp : 0<x/t := div_pos hx ht
  have hxy : y/t≤x/t-1 := by
    simpa only [sub_div,div_self ht.ne'] using (div_le_div_of_nonneg_right hy ht.le)
  have hn : 0<⌈x/t⌉₊ := Nat.ceil_pos.mpr hp
  have hc := Nat.le_ceil (x/t)
  have hm : y/t≤(⌈x/t⌉₊-1:ℕ) := by
    rw [Nat.cast_sub (by omega : 1≤⌈x/t⌉₊),Nat.cast_one]
    linarith
  exact lt_of_le_of_lt (Nat.ceil_le.mpr hm) (Nat.sub_lt hn (by omega))

lemma RoutineStep.rank_lt {t : ℝ} (ht : 0<t) (hs : t≤1/44)
    {P C : RoutineLabel} (hP : ¬P.terminal) (h : RoutineStep t P C) :
    C.rank t<P.rank t := by
  cases h with
  | meanFinal b p =>
    have hd := ceil_gap_drop ht (show 0<p-b by simpa [RoutineLabel.terminal] using hP)
      (y:=p-(b+t)) (by linarith)
    simp only [RoutineLabel.rank]
    omega
  | sampleFinal b p => simp [RoutineLabel.rank]
  | internal k k' b p =>
    have hd := ceil_gap_drop ht (show 0<p-b by simpa [RoutineLabel.terminal] using hP)
      (y:=p-1/4-(b-10*t)) (by linarith)
    cases k <;> cases k' <;> simp only [RoutineLabel.rank] <;> omega

end LogConcaveSampling.OracleCompiler

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_NumericalLayerCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling

def numericalLayerCount (J : ℝ) : ℕ := ⌈10*(J+2)⌉₊

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_Correlation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling
open Filter Quadrature
open scoped Topology

def sourceCorrelation (a : ℝ) (d : ℕ) : ℝ := Real.sqrt (1-((d:ℝ)^(-a))^2)

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_SampleCorrelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical NNReal

variable {d : ℕ}

def sampleCorrelation (η : ℝ) : ℝ := (Real.sqrt (1+η^2/4))⁻¹

lemma sampleCorrelation_properties {η : ℝ} (hη : 0<η) (hη1 : η≤1) :
    1/2 ≤ sampleCorrelation η ∧ sampleCorrelation η<1 ∧
      (sampleCorrelation η)⁻¹*Real.sqrt (1-(sampleCorrelation η)^2)=η/2 := by
  let q := Real.sqrt (1+η^2/4)
  have hq : 0<q := Real.sqrt_pos.mpr (by positivity)
  have hq2 : q^2=1+η^2/4 := Real.sq_sqrt (by positivity)
  have hq1 : 1<q := by nlinarith [sq_pos_of_pos hη]
  have hqle : q≤2 := by nlinarith [sq_nonneg (η-1)]
  have ht : sampleCorrelation η=q⁻¹ := rfl
  rw [ht]
  refine ⟨(le_inv_comm₀ (by norm_num) hq).mpr (by simpa using hqle),
    (inv_lt_one₀ hq).mpr hq1,?_⟩
  rw [inv_inv]
  have hinside : 0≤1-(q⁻¹)^2 := by
    have hu : q⁻¹≤1 := (inv_le_one₀ hq).mpr hq1.le
    nlinarith [inv_nonneg.mpr hq.le]
  have hc : (q*Real.sqrt (1-(q⁻¹)^2))^2=(η/2)^2 := by
    rw [mul_pow,Real.sq_sqrt hinside]
    field_simp
    nlinarith [hq2]
  nlinarith [mul_nonneg hq.le (Real.sqrt_nonneg (1-(q⁻¹)^2))]

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_ScalarPicard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def scalarPicard (k : ℕ) (f : ℕ → ℕ) (a : ℕ) : ℕ → ℕ
  | 0 => a
  | N+1 => a+k*f (scalarPicard k f a N)

def vectorPicard (k : ℕ) (f : ℕ × ℕ → ℕ × ℕ) (a : ℕ × ℕ) : ℕ → ℕ × ℕ
  | 0 => a
  | N+1 => (a.1+k*(f (vectorPicard k f a N)).1,a.2+k*(f (vectorPicard k f a N)).2)

def flowWork (k N x y : ℕ) : ℕ := scalarPicard k (fun z => 1+x+z) y N

def kernelWork (p q N x y g : ℕ) : ℕ :=
  p*(1+x+flowWork p N x (flowWork q N x (flowWork p N x y+g)))

def velocityWork (p q m N x : ℕ) (z : ℕ × ℕ) : ℕ × ℕ :=
  (p*(m+1)*kernelWork p q N x z.1 z.2,2+2*x+z.1)

def meanWork (p q m N nc Nc x y g : ℕ) : ℕ :=
  g+(nc+1)*(1+x+(vectorPicard (nc+1) (velocityWork p q m N x) (y,g) Nc).1)

end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_VelocityWorkCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open scoped BigOperators

def velocityWorkCoefficient (q m N : ℕ) : ℕ := 4+(m+1)*(q+1)^N

end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_OccurrenceBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter Quadrature MeanTree
open scoped Topology Classical

def occurrenceDegree (N Nc : ℕ) : ℕ := max (Nc*(2*N+2)) N

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_LowerBounds_TranscriptRejection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof

open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise

namespace LogConcaveSampling.LowerBound

abbrev Rotations (d : ℕ) := Matrix.orthogonalGroup (Fin d) ℝ

theorem orthogonal_entry_bound {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M ∈ Matrix.orthogonalGroup (Fin d) ℝ) (i j : Fin d) : |M i j| ≤ 1 := by
  have h := congrArg (fun A : Matrix (Fin d) (Fin d) ℝ => A i i)
    ((Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).mp hM)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
  have ht : (M i j)^2 ≤ ∑ k, M i k * M i k := by
    simpa only [pow_two] using
      (Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin d))) => mul_self_nonneg (M i k))
        (Finset.mem_univ j))
  rw [h] at ht
  nlinarith [sq_abs (M i j), abs_nonneg (M i j)]

theorem orthogonal_group_isCompact (d : ℕ) :
    IsCompact (Matrix.orthogonalGroup (Fin d) ℝ : Set (Matrix (Fin d) (Fin d) ℝ)) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_unitary (R := Matrix (Fin d) (Fin d) ℝ)
  · apply (Metric.isBounded_iff_subset_closedBall (0 : Matrix (Fin d) (Fin d) ℝ)).mpr
    refine ⟨1,?_⟩
    intro M hM
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (Matrix.norm_le_iff (by norm_num)).mpr
    intro i j
    exact orthogonal_entry_bound hM i j

instance rotations_compactSpace (d : ℕ) : CompactSpace (Rotations d) :=
  isCompact_iff_compactSpace.mp (orthogonal_group_isCompact d)

instance rotations_measurableSpace (d : ℕ) : MeasurableSpace (Rotations d) := borel _
instance rotations_borelSpace (d : ℕ) : BorelSpace (Rotations d) := ⟨rfl⟩

instance rotations_secondCountable (d : ℕ) : SecondCountableTopology (Rotations d) := by
  let : SecondCountableTopology (Matrix (Fin d) (Fin d) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  exact (Topology.IsEmbedding.subtypeVal (p := fun M : Matrix (Fin d) (Fin d) ℝ =>
    M ∈ Matrix.orthogonalGroup (Fin d) ℝ)).isInducing.secondCountableTopology

instance rotations_measurableMul (d : ℕ) : MeasurableMul₂ (Rotations d) :=
  ⟨continuous_mul.measurable⟩

def rotationHaar (d : ℕ) : Measure (Rotations d) :=
  Measure.haarMeasure (⟨⟨Set.univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts (Rotations d))

instance rotationHaar_probability (d : ℕ) : IsProbabilityMeasure (rotationHaar d) := by
  constructor
  exact Measure.haarMeasure_self

instance rotationHaar_isHaar (d : ℕ) : (rotationHaar d).IsHaarMeasure := by
  unfold rotationHaar
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

end LogConcaveSampling.LowerBound

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_NormalizedDirection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise

namespace LogConcaveSampling

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

def normalizedDirection (w x : H) : H := if x = 0 then w else ‖x‖⁻¹ • x

@[fun_prop] theorem measurable_normalizedDirection (w : H) :
    Measurable (normalizedDirection w) := by
  unfold normalizedDirection
  exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] in
@[simp] theorem norm_normalizedDirection {w : H} (hw : ‖w‖ = 1) (x : H) :
    ‖normalizedDirection w x‖ = 1 := by
  unfold normalizedDirection
  split_ifs with hx
  · exact hw
  · exact norm_smul_inv_norm hx

end LogConcaveSampling

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_StateLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory

namespace LogConcaveSampling

section Iteration
variable {S : ℕ → Type*} {R H C : Type*}
    [∀ n, MeasurableSpace (S n)] [MeasurableSpace R] [MeasurableSpace H] [MeasurableSpace C]

def stateLaw (μ : Measure (S 0)) (γ : Measure R)
    (step : (n : ℕ) → S n × R → S (n+1)) : (n : ℕ) → Measure (S n)
  | 0 => μ
  | n+1 => ((stateLaw μ γ step n).prod γ).map (step n)

end Iteration
end LogConcaveSampling

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TapeSnocEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory

namespace LogConcaveSampling

def tapeSnocEquiv {R : Type*} [MeasurableSpace R] (n : ℕ) :
    (Fin n → R) × R ≃ᵐ (Fin (n+1) → R) :=
  MeasurableEquiv.prodComm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => R) (Fin.last n)).symm

@[simp] lemma tapeSnocEquiv_apply {R : Type*} [MeasurableSpace R] (n : ℕ)
    (p : (Fin n → R) × R) :
    tapeSnocEquiv n p = Fin.snoc (α := fun _ : Fin (n+1) => R) p.1 p.2 := by
  exact Fin.insertNth_last' p.2 p.1

def seedTapeSnoc {Ω R : Type*} [MeasurableSpace Ω] [MeasurableSpace R] (n : ℕ) :
    ((Ω × (Fin n → R)) × R) ≃ᵐ Ω × (Fin (n+1) → R) :=
  MeasurableEquiv.prodAssoc.trans ((MeasurableEquiv.refl Ω).prodCongr (tapeSnocEquiv n))

@[simp] lemma seedTapeSnoc_apply {Ω R : Type*} [MeasurableSpace Ω] [MeasurableSpace R]
    (n : ℕ) (p : (Ω × (Fin n → R)) × R) :
    seedTapeSnoc n p = (p.1.1, Fin.snoc (α := fun _ : Fin (n+1) => R) p.1.2 p.2) := by
  change (p.1.1, tapeSnocEquiv n (p.1.2,p.2)) = _
  rw [tapeSnocEquiv_apply]

section Run
variable {S : ℕ → Type*} {Ω R : Type*}
  [∀ n, MeasurableSpace (S n)] [MeasurableSpace Ω] [MeasurableSpace R]

def stateRun (init : Ω → S 0) (step : (n : ℕ) → S n × R → S (n+1)) :
    (n : ℕ) → Ω × (Fin n → R) → S n
  | 0, p => init p.1
  | n+1, p => step n (stateRun init step n (p.1,Fin.init p.2),p.2 (Fin.last n))

omit [∀ n, MeasurableSpace (S n)] in
@[simp] lemma stateRun_snoc (init : Ω → S 0) (step : (n : ℕ) → S n × R → S (n+1))
    (n : ℕ) (p : (Ω × (Fin n → R)) × R) :
    stateRun init step (n+1) (seedTapeSnoc n p) =
      step n (stateRun init step n p.1,p.2) := by
  simp [stateRun, Fin.init_snoc]

end Run
end LogConcaveSampling

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_LowerBounds_LinearHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory

namespace LogConcaveSampling.LowerBound
section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def powerHull (L : E →ₗ[ℝ] E) : ℕ → Submodule ℝ E → Submodule ℝ E
  | 0, K => K
  | n+1, K => K ⊔ (powerHull L n K).map L

def tapeHull {n : ℕ} (t : Fin n → E × E) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range (fun i => (t i).1) ∪ Set.range (fun i => (t i).2))

end
end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound
section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
def orbitHull {ι : Type*} (L : E →ₗ[ℝ] E) (n : ℕ) (t : ι → E) : Submodule ℝ E :=
  Submodule.span ℝ {v | ∃ i : ι, ∃ j : ℕ, j ≤ n ∧ v = (L^[j]) (t i)}

end
end LogConcaveSampling.LowerBound

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_LowerBounds_Theta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory
open WithLp

open scoped BigOperators

namespace LogConcaveSampling.LowerBound

def theta (d k : ℕ) : ℝ := ((k : ℝ) + 1 / 2) * Real.pi / d

def eigenvalue (d k : ℕ) : ℝ := (3 + Real.cos (theta d k)) / 2

def weight (d n k : ℕ) : ℝ := Real.cos (n * theta d k)

theorem eigenvalue_bounds (d k : ℕ) : 1 ≤ eigenvalue d k ∧ eigenvalue d k ≤ 2 := by
  constructor <;> dsimp [eigenvalue]
  · linarith [Real.neg_one_le_cos (theta d k)]
  · linarith [Real.cos_le_one (theta d k)]

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound

def cosineAmplitude (j : ℕ) : ℝ := if j = 0 then 1 else Real.sqrt 2

def cosineColumn (d j k : ℕ) : ℝ :=
  cosineAmplitude j * Real.cos ((j : ℝ) * theta d k) / Real.sqrt d

end LogConcaveSampling.LowerBound

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LogConcaveSampling.LowerBound
open scoped BigOperators

def gaussianRow (b : ℕ) : Measure (Fin b → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

instance gaussianRow_probability (b : ℕ) : IsProbabilityMeasure (gaussianRow b) := by
  unfold gaussianRow
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

def gaussianRows (d b : ℕ) : Measure (Fin d → Fin b → ℝ) :=
  Measure.pi fun _ => gaussianRow b

instance gaussianRows_probability (d b : ℕ) : IsProbabilityMeasure (gaussianRows d b) := by
  unfold gaussianRows
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

def gaussianRowSum {d b : ℕ} (c : Fin d → ℝ) (i j : Fin b)
    (x : Fin d → Fin b → ℝ) : ℝ := ∑ k, c k * (x k i * x k j)

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound
open scoped BigOperators

def rowDeviationEnergy {ι : Type*} [Fintype ι] {d b : ℕ}
    (c : ι → Fin d → ℝ) (a z : ι → Fin b) (x : Fin d → Fin b → ℝ) : ℝ :=
  ∑ i, (gaussianRowSum (c i) (a i) (z i) x -
    (if a i = z i then (1 : ℝ) else 0) * ∑ k, c i k) ^ 2

end LogConcaveSampling.LowerBound

open scoped BigOperators
open Matrix

namespace LogConcaveSampling.LowerBound

def matrixEnergy {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℝ) : ℝ :=
  ∑ i, ∑ j, (M i j) ^ 2

end LogConcaveSampling.LowerBound

open scoped BigOperators
open Polynomial

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_LowerBounds_WeightedEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open WithLp
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Matrix
open scoped BigOperators
open Polynomial

namespace LogConcaveSampling.LowerBound

def weightedEvaluation {κ : Type*} (c g : κ → ℝ) : ℝ[X] →ₗ[ℝ] (κ → ℝ) where
  toFun p k := g k * p.eval (c k)
  map_add' p q := by ext k; simp [Polynomial.eval_add, mul_add]
  map_smul' a p := by ext k; simp [Polynomial.eval_smul]; ring

def spectralPowers : Polynomial.Sequence ℝ where
  elems' n := ((Polynomial.X + Polynomial.C 3) * Polynomial.C (1 / 2 : ℝ)) ^ n
  degree_eq' n := by
    rw [Polynomial.degree_pow, Polynomial.degree_mul_C (by norm_num), Polynomial.degree_X_add_C]
    simp

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound
open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators

abbrev BlockIndex (q : ℕ) := Fin (q+1) × Fin (q+1)

def blockMatrix {d q : ℕ} (x : Fin d → Fin (q+1) → ℝ) : Matrix (Fin d) (BlockIndex q) ℝ :=
  fun k ij => cosineColumn d ij.2 k * x k ij.1

def blockCoefficient (d q : ℕ) (v : Bool × BlockIndex q × BlockIndex q) (k : Fin d) : ℝ :=
  (if v.1 then weight d (2*q+1) k else 1) * cosineColumn d v.2.1.2 k * cosineColumn d v.2.2.2 k

def blockLeft (q : ℕ) (v : Bool × BlockIndex q × BlockIndex q) : Fin (q+1) := v.2.1.1

def blockRight (q : ℕ) (v : Bool × BlockIndex q × BlockIndex q) : Fin (q+1) := v.2.2.1

def blockTolerance (d q : ℕ) : ℝ := 40 * ((q : ℝ) + 1)^2 / Real.sqrt d

def krylovSpace {d q : ℕ} (x : Fin d → Fin (q+1) → ℝ) : Submodule ℝ (Fin d → ℝ) :=
  Submodule.span ℝ {v | ∃ i : Fin (q+1), ∃ j : ℕ, j ≤ q ∧
    v = fun k => x k i * eigenvalue d k ^ j}

end LogConcaveSampling.LowerBound

open scoped BigOperators

namespace LogConcaveSampling.LowerBound

def spectralDecay : ℝ := 3 - 2 * Real.sqrt 2

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound

def cosineCorrelation (d n j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range d, Real.cos ((n : ℝ) * theta d k) * Real.cos ((j : ℝ) * theta d k)

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound

def targetVariance (d k : ℕ) : ℝ≥0 :=
  ⟨(eigenvalue d k)⁻¹, inv_nonneg.mpr (by linarith [(eigenvalue_bounds d k).1])⟩

def targetGaussian (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi (fun k : Fin d => gaussianReal 0 (targetVariance d k))

instance targetGaussian_probability (d : ℕ) : IsProbabilityMeasure (targetGaussian d) := by
  unfold targetGaussian
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

def diagonalStatistic {d : ℕ} (c : Fin d → ℝ) (u : Fin d → ℝ) : ℝ := ∑ k, c k * (u k)^2

def separationThreshold (d q : ℕ) : ℝ := 160 * ((q : ℝ)+1)^2 * Real.sqrt d

def separationEvent (d q : ℕ) : Set (Fin d → ℝ) :=
  {u | diagonalStatistic (fun _ : Fin d => 1) u ≤ 2*d ∧
    separationThreshold d q < |diagonalStatistic (fun k : Fin d => weight d (2*q+1) k) u|}

end LogConcaveSampling.LowerBound

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_LowerBounds_DensityCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open WithLp
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Matrix
open Polynomial
open scoped BigOperators

namespace LogConcaveSampling.LowerBound
open Matrix WithLp ProbabilityTheory
open scoped RealInnerProductSpace

def densityCoefficient (d : ℕ) : ℝ≥0∞ :=
  ∏ k : Fin d, ENNReal.ofReal ((Real.sqrt (2*Real.pi*(targetVariance d k : ℝ)))⁻¹)

end LogConcaveSampling.LowerBound

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_MeanSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeanTree MeasureTheory Quadrature
open scoped Classical NNReal

variable {d : ℕ}

def MeanSize (lam q r σ : ℝ) : Prop :=
  0 < r ∧ r ≤ 1 ∧ 0 < σ ∧ lam*r^2 ≤ q ∧ lam*r ≤ q*σ

def SampleSize (lam q r η : ℝ) : Prop :=
  0 < r ∧ r ≤ 1 ∧ 0 < η ∧ η ≤ 1 ∧ lam*r^2 ≤ q*η

end LogConcaveSampling.OracleCompiler

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_NumericalScalars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter Quadrature
open scoped Classical NNReal

structure NumericalScalars where
  lam : ℝ≥0
  r : ℝ
  s : ℝ

def NumericalScalars.small (v : NumericalScalars) (bound : ℝ) : Prop :=
  0<v.r ∧ 0<v.s ∧ (v.lam:ℝ)*v.r^2≤bound ∧ (v.lam:ℝ)*v.r/v.s≤bound

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_Shape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open Filter
open scoped Classical Topology

def anchorSize (κ t : ℝ) (q : ℕ → ℝ) (d : ℕ) : ℝ := q d/((d:ℝ)^(-(κ*t)))

end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open scoped Classical

def RoutineLabel.Admissible (t K : ℝ) (L : RoutineLabel) : Prop :=
  0≤L.p ∧ L.p≤K ∧ 1/2+40*t*L.p≤L.b

end LogConcaveSampling.OracleCompiler

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_NoiseKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical ENNReal

variable {d : ℕ}

def kernelAction {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (κ : Kernel E F) (f : F → ℝ) : E → ℝ := fun x => ∫z,f z ∂κ x

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical

variable {E : Type*} [MeasurableSpace E]

def markovChain (κ : Kernel E E) (μ : Measure E) : ℕ → Measure E
  | 0 => μ
  | n+1 => κ ∘ₘ markovChain κ μ n

instance markovChain_probability (κ : Kernel E E) [IsMarkovKernel κ]
    (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (markovChain κ μ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure μ)
  | succ n ih => let := ih; exact inferInstanceAs (IsProbabilityMeasure (κ ∘ₘ markovChain κ μ n))

def markovAction (κ : Kernel E E) (n : ℕ) (f : E → ℝ) : E → ℝ :=
  (kernelAction κ)^[n] f

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ChangingChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical

variable {E R : Type*} [MeasurableSpace E] [MeasurableSpace R]

def changingChain (κ : ℕ → Kernel E E) (μ : Measure E) : ℕ → Measure E
  | 0 => μ
  | n+1 => κ n ∘ₘ changingChain κ μ n

instance changingChain_probability (κ : ℕ → Kernel E E) [∀n,IsMarkovKernel (κ n)]
    (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) : IsProbabilityMeasure (changingChain κ μ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure μ)
  | succ n ih => let := ih; exact inferInstanceAs (IsProbabilityMeasure (κ n ∘ₘ changingChain κ μ n))

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical

variable {d : ℕ}

def descentScale (h : ℝ) (j : ℕ) : ℝ := h/2^j
@[simp] lemma descentScale_zero (h : ℝ) : descentScale h 0=h := by simp [descentScale]
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TopScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter
open scoped Topology

def topScale (κ : ℝ) (d : ℕ) : ℝ := (d:ℝ)^(-κ)/4
def proximalRounds (κ : ℝ) (d : ℕ) : ℕ := ⌈40*(1+κ)*dimensionLog d/topScale κ d⌉₊+1
def descentRounds (d : ℕ) : ℕ := ⌈20*dimensionLog d/Real.log 2⌉₊

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_MixingEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter
open scoped Topology

def mixingEnvelope (κ : ℝ) (d : ℕ) : ℝ :=
  (2*(d:ℝ))*(d:ℝ)^(-(20*(1+κ)))*(topScale κ d)⁻¹

end LogConcaveSampling

end

end

end OAI
end


