-- Prove2me | Definitions.Def_OAIQ048L002
-- name    : OAIQ048L002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T13:25:37.924974+00:00
-- url     : https://prove2.me/theorems/fb196374-631e-4e4c-af35-c96aae4c2e49
-- title:
--   Definitions bundle OAIQ048L002 of the split of OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LogConcaveSampling.exact_source_main`, carved from OpenAI's openai/math development (OpenAI, *Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)*, OpenAI Math Release, September 26, 2026, result family 139, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 594 declarations of OpenAI's Lean: 241 definitions, 12 inductive types or structures, 14 instances and 327 theorems. The definitions and types are `OAI.LogConcaveSampling.CalibratedMeanCircuit`, `OAI.LogConcaveSampling.CycleTrace.colorEquiv`, `OAI.LogConcaveSampling.CycleTrace.decodeTraceSlot`, `OAI.LogConcaveSampling.CycleTrace.decodeWire`, `OAI.LogConcaveSampling.CycleTrace.encodeSlot`, `OAI.LogConcaveSampling.CycleTrace.encodeWire`, `OAI.LogConcaveSampling.CycleTrace.fieldPosition`, `OAI.LogConcaveSampling.CycleTrace.liftField`, `OAI.LogConcaveSampling.CycleTrace.primaryPair`, `OAI.LogConcaveSampling.CycleTrace.rowAt`, `OAI.LogConcaveSampling.CycleTrace.scorePosition`, `OAI.LogConcaveSampling.CycleTrace.slotEquivAt`, `OAI.LogConcaveSampling.EulerGeometry.law`, `OAI.LogConcaveSampling.FinitePicard.stepLp`, `OAI.LogConcaveSampling.GlobalODE.backwardTest`, `OAI.LogConcaveSampling.GlobalODE.flowHomeomorph`, `OAI.LogConcaveSampling.GlobalODE.flowLinearization`, `OAI.LogConcaveSampling.GlobalODE.flowSpatialCoefficient`, `OAI.LogConcaveSampling.GlobalODE.fundamental`, `OAI.LogConcaveSampling.GlobalODE.fundamentalEquiv`, `OAI.LogConcaveSampling.GlobalODE.spaceTimeBackward`, `OAI.LogConcaveSampling.GlobalODE.spaceTimeForward`, `OAI.LogConcaveSampling.GlobalODE.spaceTimeHomeomorph`, `OAI.LogConcaveSampling.GraphSchedule.absorb`, `OAI.LogConcaveSampling.GraphSchedule.close`, `OAI.LogConcaveSampling.GraphSchedule.cutColorEquiv`, `OAI.LogConcaveSampling.GraphSchedule.edgeDecEqC`, `OAI.LogConcaveSampling.GraphSchedule.edgeDecEqRUp`, `OAI.LogConcaveSampling.GraphSchedule.edgeDecEqRank`, `OAI.LogConcaveSampling.GraphSchedule.edgeDecEqT`, `OAI.LogConcaveSampling.GraphSchedule.edgeDecEqTG`, `OAI.LogConcaveSampling.GraphSchedule.edgeDecEqUp`, `OAI.LogConcaveSampling.GraphSchedule.incidentMatrix`, `OAI.LogConcaveSampling.GraphSchedule.incidentSplit`, `OAI.LogConcaveSampling.GraphSchedule.inputEdges`, `OAI.LogConcaveSampling.GraphSchedule.outputEdges`, `OAI.LogConcaveSampling.JetCalculus.cadj`, `OAI.LogConcaveSampling.JetCalculus.euler`, `OAI.LogConcaveSampling.JetCalculus.gadj`, `OAI.LogConcaveSampling.JetCalculus.materialIter` and 213 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `LogConcave_Analysis_AffinePotential`, `LogConcave_Analysis_GaussianMarginalLowerTail`, `LogConcave_Analysis_InterpolationPotential`, `LogConcave_Analysis_Law`, `LogConcave_Dynamics_Curve`, `LogConcave_Dynamics_FullProbabilityFlow`, `LogConcave_Dynamics_SmoothFlowJoint`, `LogConcave_Dynamics_SpaceTimeForward`, `LogConcave_Dynamics_TriangularEquiv`, `LogConcave_Dynamics_Truncated`, `LogConcave_Dynamics_VariationalField`, `LogConcave_JetEstimates_AllSplitBound`, `LogConcave_JetEstimates_ForestTensor`, `LogConcave_JetEstimates_GadjScalar`, `LogConcave_JetEstimates_JetMaterial`, `LogConcave_JetEstimates_JetRightSlice`, `LogConcave_JetEstimates_Material`, `LogConcave_JetEstimates_Mdir`, `LogConcave_JetEstimates_MixedJetAdd`, `LogConcave_JetEstimates_PolySmooth`, `LogConcave_JetEstimates_SpaceBasis`, `LogConcave_JetEstimates_SplitBundle`, `LogConcave_JetEstimates_SplitIndex`, `LogConcave_JetEstimates_TensorExpression`, `LogConcave_JetEstimates_TensorTerm`, `LogConcave_LowerBounds_CouplingNoise`, `LogConcave_LowerBounds_FrameTransport`, `LogConcave_LowerBounds_HardEigenOutput`, `LogConcave_LowerBounds_LinearHistory`, `LogConcave_LowerBounds_PrefixSpace`, `LogConcave_LowerBounds_RevealRotation`, `LogConcave_LowerBounds_RotationIsometry`, `LogConcave_LowerBounds_RoundFrames`, `LogConcave_LowerBounds_SpectrumOperator`, `LogConcave_LowerBounds_TranscriptRejection`, `LogConcave_Numerics_BaseVariation`, `LogConcave_Numerics_Basis`, `LogConcave_Numerics_BasisDerivative`, `LogConcave_Numerics_ChildNoise`, `LogConcave_Numerics_CompileDeclaredRootShift`, `LogConcave_Numerics_CompositeAngle`, `LogConcave_Numerics_Cost`, `LogConcave_Numerics_Forward`, `LogConcave_Numerics_LogMeshLength`, `LogConcave_Numerics_NodeLp`, `LogConcave_Numerics_NodePolynomial`, `LogConcave_Numerics_Picard`, `LogConcave_Numerics_RowGaussian`, `LogConcave_Numerics_RowTape`, `LogConcave_Numerics_ScalarPicard`, `LogConcave_OraclePrograms_CalibratedMeanCircuit`, `LogConcave_OraclePrograms_CircuitParameters`, `LogConcave_OraclePrograms_Expression`, `LogConcave_OraclePrograms_Fresh`, `LogConcave_OraclePrograms_FullTape`, `LogConcave_OraclePrograms_IndependentSeq`, `LogConcave_OraclePrograms_MeanCorrect`, `LogConcave_OraclePrograms_MeanSize`, `LogConcave_OraclePrograms_Program`, `LogConcave_OraclePrograms_ReservedProgram`, `LogConcave_OraclePrograms_RoutineBudget`, `LogConcave_OraclePrograms_SeedProgram`, `LogConcave_OraclePrograms_Shape`, `LogConcave_OraclePrograms_SlotTransformAddShift`, `LogConcave_OraclePrograms_StandaloneCorrect`, `LogConcave_OraclePrograms_TerminalMean`, `LogConcave_OraclePrograms_TerminalMeanProgram`, `LogConcave_OraclePrograms_TopProgram`, `LogConcave_Sampling_AdjointCoordinateContinuous`, `LogConcave_Sampling_AnalyticBase`, `LogConcave_Sampling_ClosedFieldMean`, `LogConcave_Sampling_ConditionalFieldMean`, `LogConcave_Sampling_ConditionalPositionMoment`, `LogConcave_Sampling_ConditionalSlotEmbedding`, `LogConcave_Sampling_CoordinateRank`, `LogConcave_Sampling_Directional`, `LogConcave_Sampling_DirectionalBasisSum`, `LogConcave_Sampling_JointConditionalLawProperties`, `LogConcave_Sampling_JointPosition`, `LogConcave_Sampling_JointSpace`, `LogConcave_Sampling_JointU`, `LogConcave_Sampling_MaterialScalar`, `LogConcave_Sampling_NoiseKernel`, `LogConcave_Sampling_PolynomialGrowth`, `LogConcave_Sampling_PrimitiveField`, `LogConcave_Sampling_ProbabilityNodes`, `LogConcave_Sampling_ScoreSlots`, `LogConcave_Sampling_SpatialTensor`, `LogConcave_Sampling_TiltedExpectation`, `LogConcave_Sampling_TranslationIntegrationByParts`, `LogConcave_TensorGraphs_Chain`, `LogConcave_TensorGraphs_FieldPosition`, `LogConcave_TensorGraphs_History`, `LogConcave_TensorGraphs_IncidentMatrix`, `LogConcave_TensorGraphs_RankEquiv`.
--
--   **Imports.** It imports the published bundle `Def_LogConcaveQuery`; the bundles `OAIQ048L000` and `OAIQ048L001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ048L004`; the statements `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.meanFrom_correct`, `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.sampleFrom_squared`, `OAI.LogConcaveSampling.OracleCompiler.exists_source_numerical_ready`, `OAI.LogConcaveSampling.OracleCompiler.uniform_routine_accuracy`, `OAI.LogConcaveSampling.kernelCorrectionPicard_rms`, `OAI.LogConcaveSampling.probabilityAnchored_marginal_rms` and `OAI.LogConcaveSampling.sampleMeanCircuit_rms`; the proofs of `OAI.LogConcaveSampling.OracleCompiler.uniform_routine_accuracy` and `OAI.LogConcaveSampling.stationaryMeanTarget_law`.
-- source:
--   OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 139; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Subpolynomial-query-complexity-for-well-conditioned-log-concave-sampling-September-26-2026/article.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_OAIQ048L000
import Definitions.Def_OAIQ048L001

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

section
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma growth_tiltDerivativeIntegrand {h : Point d → E} (hg : HasPolynomialGrowth h) :
    HasPolynomialGrowth (tiltDerivativeIntegrand h) := by
  obtain ⟨C,hC,n,hn⟩ := hg
  refine ⟨2*C,by positivity,n+1,fun z => ?_⟩
  have hb : ‖tiltDerivativeIntegrand h z‖ ≤ ‖z‖ * ‖h z‖ := by
    simp [tiltDerivativeIntegrand, ContinuousLinearMap.norm_smulRight_apply]
  have hr : ‖z‖ ≤ 1+‖z‖^(n+1) := by
    by_cases hz : ‖z‖ ≤ 1
    · have hh : 0 ≤ ‖z‖^(n+1) := by positivity
      linarith
    · have hz' : 1 ≤ ‖z‖ := le_of_not_ge hz
      have hn' : 1 ≤ ‖z‖^n := one_le_pow₀ hz'
      have hh := mul_le_mul_of_nonneg_left hn' (norm_nonneg z)
      rw [← pow_succ',mul_one] at hh
      linarith
  calc
    _ ≤ ‖z‖ * (C*(1+‖z‖^n)) := hb.trans (mul_le_mul_of_nonneg_left (hn z) (norm_nonneg z))
    _ ≤ 2*C*(1+‖z‖^(n+1)) := by
      have hr' := mul_le_mul_of_nonneg_left hr hC
      have hp : ‖z‖*‖z‖^n = ‖z‖^(n+1) := (pow_succ' _ _).symm
      have hnon : 0 ≤ C*‖z‖^(n+1) := by positivity
      nlinarith [mul_nonneg hC (show 0 ≤ 1+‖z‖^(n+1) by positivity)]

theorem hasFDerivAt_tiltedIntegral (H : Point d → ℝ) {h : Point d → E}
    (hH : Continuous H) (hh : Continuous h) (ht : HasGaussianLowerTail H)
    (hg : HasPolynomialGrowth h) (θ : Point d) :
    HasFDerivAt (tiltedIntegral H h) (tiltedIntegral H (tiltDerivativeIntegrand h) θ) θ := by
  obtain ⟨m,hm,C,hT⟩ := ht
  have ht : HasGaussianLowerTail H := ⟨m,hm,C,hT⟩
  obtain ⟨K,hK,n,hg'⟩ := growth_tiltDerivativeIntegrand hg
  let M := ‖θ‖+1
  let B := Real.exp (C+M^2/(2*m))*K
  let b : Point d → ℝ := fun z => B*(Real.exp (-(m/2)*‖z‖^2)+
    ‖z‖^n*Real.exp (-(m/2)*‖z‖^2))
  have hi : Integrable b := ((integrable_gaussian_envelope d (b := m/2) (by positivity)).add
    (integrable_norm_pow_gaussian d n (b := m/2) (by positivity))).const_mul B
  have hd : ∀ z θ', HasFDerivAt
      (fun t : Point d => Real.exp (inner ℝ t z-H z) • h z)
      (Real.exp (inner ℝ θ' z-H z) • tiltDerivativeIntegrand h z) θ' := by
    intro z θ'
    have hh' := (((innerSL ℝ z).hasFDerivAt (x := θ')).sub_const (H z)).exp.smul_const (h z)
    convert! hh' using 1
    · funext t
      simp only [innerSL_apply_apply, real_inner_comm t z]
    · ext t
      simp [tiltDerivativeIntegrand,real_inner_comm,smul_smul]
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun t z => Real.exp (inner ℝ t z-H z) • tiltDerivativeIntegrand h z)
    (bound := b) (Metric.ball_mem_nhds θ (show (0:ℝ)<1 by norm_num))
  · exact Filter.Eventually.of_forall fun t => (integrable_tilted H hH hh ht hg t).aestronglyMeasurable
  · exact integrable_tilted H hH hh ht hg θ
  · exact (integrable_tilted H hH (continuous_tiltDerivativeIntegrand hh) ht
      (growth_tiltDerivativeIntegrand hg) θ).aestronglyMeasurable
  · filter_upwards [] with z t ht'
    have htm : ‖t‖ ≤ M := by
      have hb : ‖t-θ‖ < 1 := by simpa [dist_eq_norm] using ht'
      have hn := norm_add_le (t-θ) θ
      simp only [sub_add_cancel] at hn
      dsimp [M]
      linarith
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    have he := mul_le_mul (gaussian_tilt_bound hm (by dsimp [M]; positivity) hT htm z)
      (hg' z) (norm_nonneg _) (by positivity)
    change _ ≤ B*(Real.exp (-(m/2)*‖z‖^2)+‖z‖^n*Real.exp (-(m/2)*‖z‖^2))
    convert! he using 1; dsimp [B]; ring
  · exact hi
  · exact Filter.Eventually.of_forall fun z θ' _ => hd z θ'

end
end LogConcaveSampling

end UpperProof
end
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

def algorithm (A : Program Ω d q (Point d)) : OracleAlgorithm Ω d q where
  query := A.query
  query_measurable := A.query_measurable
  output := A.output
  output_measurable := A.output_measurable

end Program
end LogConcaveSampling.OracleCompiler

namespace LogConcaveSampling.OracleCompiler.Program
variable {Ω O R : Type*} [MeasurableSpace Ω] [MeasurableSpace O] [MeasurableSpace R]
  {d q r : ℕ}

lemma measurable_leftTrace : Measurable (leftTrace (d:=d) (q:=q) (r:=r)) := by
  exact Measurable.of_eval fun index => measurable_pi_apply (Fin.castAdd r index)
lemma measurable_rightTrace : Measurable (rightTrace (d:=d) (q:=q) (r:=r)) := by
  exact Measurable.of_eval fun index => measurable_pi_apply (Fin.natAdd q index)

def seq (A : Program Ω d q O) (B : Program (Ω × O) d r R) :
    Program Ω d (q+r) R where
  query i p := Fin.addCases
    (fun j => A.query j (p.1, leftTrace p.2))
    (fun j => B.query j ((p.1, A.output (p.1,leftTrace p.2)), rightTrace p.2)) i
  query_measurable i := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.addCases_left, Function.comp_def] using (A.query_measurable j).comp
        (measurable_fst.prodMk (measurable_leftTrace.comp measurable_snd))
    · simpa only [Fin.addCases_right, Function.comp_def] using (B.query_measurable j).comp
        ((measurable_fst.prodMk (A.output_measurable.comp
          (measurable_fst.prodMk (measurable_leftTrace.comp measurable_snd)))).prodMk
          (measurable_rightTrace.comp measurable_snd))
  output p := B.output ((p.1,A.output (p.1,leftTrace p.2)), rightTrace p.2)
  output_measurable := B.output_measurable.comp
    ((measurable_fst.prodMk (A.output_measurable.comp
      (measurable_fst.prodMk (measurable_leftTrace.comp measurable_snd)))).prodMk
        (measurable_rightTrace.comp measurable_snd))

def map (A : Program Ω d q O) (f : Ω × O → R) (hf : Measurable f) : Program Ω d q R where
  query := A.query
  query_measurable := A.query_measurable
  output p := f (p.1,A.output p)
  output_measurable := hf.comp (measurable_fst.prodMk A.output_measurable)

def seedMap {Ξ : Type*} [MeasurableSpace Ξ] (A : Program Ω d q O)
    (f : Ξ → Ω) (hf : Measurable f) : Program Ξ d q O where
  query i p := A.query i (f p.1, p.2)
  query_measurable i := (A.query_measurable i).comp
    ((hf.comp measurable_fst).prodMk measurable_snd)
  output p := A.output (f p.1,p.2)
  output_measurable := A.output_measurable.comp
    ((hf.comp measurable_fst).prodMk measurable_snd)

def oneQuery (x : Ω → Point d) (hx : Measurable x)
    (f : Ω × Reply d → O) (hf : Measurable f) : Program Ω d 1 O where
  query _ p := x p.1
  query_measurable _ := hx.comp measurable_fst
  output p := f (p.1,p.2 0)
  output_measurable := hf.comp (measurable_fst.prodMk
    ((measurable_pi_apply 0).comp measurable_snd))

end LogConcaveSampling.OracleCompiler.Program

end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_AffinePotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory Function
open scoped Classical NNReal RealInnerProductSpace

variable {d : ℕ}

namespace OracleCompiler.Program
variable {Ω O : Type*} [MeasurableSpace Ω] [MeasurableSpace O] {q : ℕ}

def affineReplies (s : ℝ) (H : Transcript d q) : Transcript d q :=
  fun i => ((H i).1,s • (H i).2)

lemma measurable_affineReplies (s : ℝ) : Measurable (affineReplies (d:=d) (q:=q) s) := by
  unfold affineReplies
  fun_prop

@[simp] lemma affineReplies_zero (s : ℝ) : affineReplies (d:=d) (q:=q) s 0=0 := by
  ext i <;> simp [affineReplies]

def affineOracle (A : Program Ω d q O) (a : Ω → Point d) (ha : Measurable a) (s : ℝ) :
    Program Ω d q O where
  query i p := a p.1+s • A.query i (p.1,affineReplies s p.2)
  query_measurable i := (ha.comp measurable_fst).add
    (((A.query_measurable i).comp (measurable_fst.prodMk
      ((measurable_affineReplies s).comp measurable_snd))).const_smul s)
  output p := A.output (p.1,affineReplies s p.2)
  output_measurable := A.output_measurable.comp (measurable_fst.prodMk
    ((measurable_affineReplies s).comp measurable_snd))

end OracleCompiler.Program
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_MixedJetAdd
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

namespace LogConcaveSampling.JetCalculus
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

lemma jet_smul {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (v : ι → E) (l : List ι) (c : ℝ) :
    jet (fun i => c • v i) l f=fun x => c^l.length*jet v l f x := by
  induction l with
  | nil => simp [jet]
  | cons i l ih =>
    simp only [jet,ih,List.length_cons]
    rw [dir_const_mul ((smooth_jet hf v l).differentiable (by simp)),dir_smul]
    funext x
    simp only [pow_succ,dir]
    ring

end LogConcaveSampling.JetCalculus

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

lemma tilted_partition_pos {d : ℕ} {H : Point d → ℝ} (hH : Continuous H)
    (ht : HasGaussianLowerTail H) (θ : Point d) :
    0 < tiltedIntegral H (fun _ => (1:ℝ)) θ := by
  have hi := integrable_tilted H hH continuous_const ht (growth_const (1:ℝ)) θ
  simp only [smul_eq_mul,mul_one] at hi
  simpa only [tiltedIntegral,smul_eq_mul,mul_one] using integral_exp_pos hi

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_PrimitiveField
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

lemma jointImage_norm_sq {d : ℕ} (u v : Point d) :
    ‖(EuclideanSpace.sumEquivProd.symm (u,v) : JointPoint d)‖^2=‖u‖^2+‖v‖^2 := by
  simp [EuclideanSpace.sumEquivProd,WithLp.prod_norm_sq_eq_of_L2]

lemma jointImage_contDiff {d : ℕ} {f : Point d → Point d} (hf : ContDiff ℝ 1 f) (L : ℝ) :
    ContDiff ℝ 1 (jointImage f L) := by
  exact EuclideanSpace.sumEquivProd.symm.contDiff.comp
    (contDiff_id.prodMk (show ContDiff ℝ 1 (fun z => L⁻¹ • f z) by fun_prop))

lemma jointImage_lipschitz {d : ℕ} {f : Point d → Point d} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hL : L≠0) : LipschitzWith 2 (jointImage f L) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have he : jointImage f L u-jointImage f L v=
      EuclideanSpace.sumEquivProd.symm (u-v,(L:ℝ)⁻¹ • (f u-f v)) := by
    rw [jointImage,jointImage,← map_sub]
    congr 1
    simp only [Prod.mk_sub_mk,smul_sub]
  have hL0 : (L:ℝ)≠0 := by exact_mod_cast hL
  have hb : ‖(L:ℝ)⁻¹ • (f u-f v)‖ ≤ ‖u-v‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr L.coe_nonneg)]
    have hh := mul_le_mul_of_nonneg_left (hf.dist_le_mul u v) (inv_nonneg.mpr L.coe_nonneg)
    simpa only [dist_eq_norm,← mul_assoc,inv_mul_cancel₀ hL0,one_mul] using hh
  rw [dist_eq_norm,he]
  have hs := jointImage_norm_sq (u-v) ((L:ℝ)⁻¹ • (f u-f v))
  have hbs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hb
  simp only [NNReal.coe_ofNat,dist_eq_norm]
  nlinarith [norm_nonneg (EuclideanSpace.sumEquivProd.symm
    (u-v,(L:ℝ)⁻¹ • (f u-f v)) : JointPoint d),norm_nonneg (u-v),sq_nonneg ‖u-v‖]

lemma jointConditionalLaw_properties {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2 ≤ 1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    let μ := jointConditionalLaw F x r ρ y ((lam:ℝ)*r)
    IsProbabilityMeasure μ ∧ Appell.HasExpMoments μ ∧
      HasPoincare μ (2*Real.pi^2*(1-ρ^2)) := by
  let L : ℝ≥0 := lam*(NNReal.mk r hr.le)
  have hL : L≠0 := mul_ne_zero hlam.ne' (by intro h; exact hr.ne' (congrArg (fun t : ℝ≥0 => (t:ℝ)) h))
  have hK := jointImage_lipschitz (primitiveField_lipschitz hF x hr.le) hL
  have hS := jointImage_contDiff (primitiveField_contDiff hF x r) (L:ℝ)
  have hp : IsProbabilityMeasure (gibbs (conditionalPotential F x r ρ y)) :=
    conditionalLaw_probability hF x hr.le hl hρ0 hρ1 y
  change IsProbabilityMeasure ((gibbs (conditionalPotential F x r ρ y)).map
      (jointImage (primitiveField F x r) (L:ℝ))) ∧ _
  refine ⟨Measure.isProbabilityMeasure_map hS.continuous.aemeasurable,?_,?_⟩
  · exact (conditionalLaw_hasExpMoments hF x hr.le hl hρ0 hρ1 y).map_lipschitz hK
  · have hh := (conditionalLaw_hasPoincare hF x hr.le hl hρ0 hρ1 y).map
      (by obtain ⟨ha,_⟩ := probability_time hρ0 hρ1; positivity) hS hK
    change HasPoincare ((gibbs (conditionalPotential F x r ρ y)).map
      (jointImage (primitiveField F x r) (L:ℝ))) _
    convert hh using 1; norm_num; ring

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_JointPosition
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

lemma jointPair_inner {d : ℕ} (u v w z : Point d) :
    inner ℝ (EuclideanSpace.sumEquivProd.symm (u,v) : JointPoint d)
      (EuclideanSpace.sumEquivProd.symm (w,z)) = inner ℝ u w+inner ℝ v z := by
  have he := jointImage_norm_sq (u+w) (v+z)
  rw [show (u+w,v+z)=(u,v)+(w,z) from rfl,map_add,norm_add_sq_real] at he
  rw [jointImage_norm_sq,jointImage_norm_sq,norm_add_sq_real,norm_add_sq_real] at he
  linarith

lemma jointPosition_inner {d : ℕ} (u : Point d) (f : Point d → Point d) (L : ℝ) (z : Point d) :
    inner ℝ (jointPosition d u) (jointImage f L z)=inner ℝ u z := by
  change inner ℝ (EuclideanSpace.sumEquivProd.symm (u,0) : JointPoint d)
      (EuclideanSpace.sumEquivProd.symm (z,L⁻¹ • f z))=_
  rw [jointPair_inner,inner_zero_left,add_zero]

lemma jointField_inner {d : ℕ} (u : Point d) (f : Point d → Point d) (L : ℝ) (z : Point d) :
    inner ℝ (jointField d u) (jointImage f L z)=L⁻¹*inner ℝ u (f z) := by
  change inner ℝ (EuclideanSpace.sumEquivProd.symm (0,u) : JointPoint d)
      (EuclideanSpace.sumEquivProd.symm (z,L⁻¹ • f z))=_
  rw [jointPair_inner,inner_zero_left,zero_add,inner_smul_right]

lemma joint_laplace_one {d : ℕ} {μ : Measure (Point d)} {f : Point d → Point d}
    (hf : Continuous f) (L : ℝ) (θ : Point d) :
    Appell.laplace (μ.map (jointImage f L)) (fun _ => (1:ℝ)) (jointPosition d θ)=
      Appell.laplace μ (fun _ => (1:ℝ)) θ := by
  have hS : Continuous (jointImage f L) := by
    unfold jointImage
    fun_prop
  rw [Appell.laplace,integral_map hS.aemeasurable (by fun_prop)]
  simp only [jointPosition_inner,Appell.laplace]

lemma joint_normalizedLaplace {d : ℕ} {μ : Measure (Point d)} {f : Point d → Point d}
    (hf : Continuous f) (L : ℝ) (u θ : Point d) :
    Appell.normalizedLaplace (μ.map (jointImage f L))
      (fun z => inner ℝ (jointField d u) z) (jointPosition d θ)=
      L⁻¹*Appell.normalizedLaplace μ (fun z => inner ℝ u (f z)) θ := by
  have hS : Continuous (jointImage f L) := by
    unfold jointImage
    fun_prop
  have hn : Appell.laplace (μ.map (jointImage f L))
      (fun z => inner ℝ (jointField d u) z) (jointPosition d θ)=
      L⁻¹*Appell.laplace μ (fun z => inner ℝ u (f z)) θ := by
    rw [Appell.laplace,integral_map hS.aemeasurable (by fun_prop)]
    simp only [jointPosition_inner,jointField_inner,smul_eq_mul]
    rw [show (fun z : Point d => Real.exp (inner ℝ θ z)*(L⁻¹*inner ℝ u (f z)))=
      fun z => L⁻¹*(Real.exp (inner ℝ θ z)*inner ℝ u (f z)) by funext z; ring,
      integral_const_mul,Appell.laplace]
    rfl
  unfold Appell.normalizedLaplace
  rw [joint_laplace_one hf,hn]
  ring

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ConditionalFieldMean
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
open scoped RealInnerProductSpace Topology

theorem conditionalFieldMean_logLaplace {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (u y h : Point d) :
    conditionalMeanScalar F x r ρ (fun z => inner ℝ u (primitiveField F x r z)) (y+h)=
      ((lam:ℝ)*r)*JetCalculus.dir (jointField d u)
        (fun θ => Real.log (Appell.laplace (jointConditionalLaw F x r ρ y ((lam:ℝ)*r))
          (fun _ => (1:ℝ)) θ)) (jointPosition d ((ρ/(1-ρ^2)) • h)) := by
  obtain ⟨hp,hm,_⟩ := jointConditionalLaw_properties hF x hr hlam hl hρ0 hρ1 y
  let := hp
  rw [Appell.dir_log_laplace hm]
  change _=((lam:ℝ)*r)*Appell.normalizedLaplace
    ((gibbs (conditionalPotential F x r ρ y)).map (jointImage (primitiveField F x r) ((lam:ℝ)*r)))
      (fun z => inner ℝ (jointField d u) z) (jointPosition d ((ρ/(1-ρ^2)) • h))
  rw [joint_normalizedLaplace (primitiveField_contDiff hF x r).continuous,
    ← mul_assoc,mul_inv_cancel₀ (by positivity : (lam:ℝ)*r≠0),one_mul]
  exact conditionalMeanScalar_shift hF x hr.le hl hρ0 hρ1 _ y h

theorem conditionalFieldMean_jet {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (u y : Point d) {ι : Type*} (v : ι → Point d) (l : List ι) :
    JetCalculus.jet v l
      (conditionalMeanScalar F x r ρ (fun z => inner ℝ u (primitiveField F x r z))) y=
      ((lam:ℝ)*r)*(ρ/(1-ρ^2))^l.length*
        JetCalculus.jet (fun i => jointPosition d (v i)) l
          (JetCalculus.dir (jointField d u)
            (fun θ => Real.log (Appell.laplace (jointConditionalLaw F x r ρ y ((lam:ℝ)*r))
              (fun _ => (1:ℝ)) θ))) 0 := by
  obtain ⟨hp,hm,_⟩ := jointConditionalLaw_properties hF x hr hlam hl hρ0 hρ1 y
  let := hp
  let f : JointPoint d → ℝ := fun θ => Real.log
    (Appell.laplace (jointConditionalLaw F x r ρ y ((lam:ℝ)*r)) (fun _ => (1:ℝ)) θ)
  have hfs : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Appell.contDiff_laplace hm continuous_const (Appell.HasGrowth.const _)).log
      (fun θ => (Appell.laplace_one_pos hm θ).ne')
  have hds := JetCalculus.smooth_dir hfs (jointField d u)
  let B : Point d →L[ℝ] JointPoint d := (ρ/(1-ρ^2)) • jointPosition d
  have hcomp : ContDiff ℝ (⊤ : ℕ∞) (fun h => JetCalculus.dir (jointField d u) f (B h+0)) :=
    hds.comp (by fun_prop)
  have hs := conditionalMeanScalar_smooth hF x hr.le hl hρ0 hρ1
    (continuous_const.inner (primitiveField_contDiff hF x r).continuous)
    (primitiveField_inner_growth hF x u hr.le)
  have htrans := congrFun (JetCalculus.jet_comp_affine hs (ContinuousLinearMap.id ℝ (Point d))
    y v l) 0
  have he : (fun h => conditionalMeanScalar F x r ρ
      (fun z => inner ℝ u (primitiveField F x r z)) (h+y))=
      fun h => ((lam:ℝ)*r)*JetCalculus.dir (jointField d u) f (B h+0) := by
    funext h
    simpa only [add_comm h y,B,smul_apply,map_smul,add_zero]
      using conditionalFieldMean_logLaplace hF x hr hlam hl hρ0 hρ1 u y h
  simp only [ContinuousLinearMap.id_apply,zero_add] at htrans
  rw [← htrans,he,JetCalculus.jet_const_mul hcomp,
    JetCalculus.jet_comp_affine hds B 0]
  simp only [map_zero,zero_add]
  have hB : (fun i => B (v i))=fun i => (ρ/(1-ρ^2)) • jointPosition d (v i) := rfl
  rw [hB,JetCalculus.jet_smul hds]
  ring

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TranslationIntegrationByParts
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
open MeasureTheory Filter
open scoped Topology RealInnerProductSpace

theorem translation_integration_by_parts {d : ℕ} {H : Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ 1 H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (v : Point d) :
    Integrable (fun z => inner ℝ (gradient H z) v * Real.exp (-H z)) ∧
      (∫ z,inner ℝ (gradient H z) v * Real.exp (-H z))=0 := by
  obtain ⟨m,hm,C,ht⟩ := ht
  let F : ℝ → Point d → ℝ := fun t z => Real.exp (-H (z+t • v))
  let F' : ℝ → Point d → ℝ := fun t z =>
    -(inner ℝ (gradient H (z+t • v)) v)*Real.exp (-H (z+t • v))
  have hgc : Continuous (gradient H) := hL.continuous
  have hd (z : Point d) (t : ℝ) : HasDerivAt (fun t => F t z) (F' t z) t := by
    have hh := (hH.differentiable (by norm_num) (z+t • v)).hasFDerivAt.comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const v).const_add z)
    have hh' : HasDerivAt (fun t => H (z+t • v)) (inner ℝ (gradient H (z+t • v)) v) t := by
      convert! hh using 1
      all_goals try with_reducible_and_instances rfl
      rw [one_smul,inner_gradient_left]
    convert! hh'.neg.exp using 1
    all_goals try with_reducible_and_instances rfl
    simp only [F',mul_comm,Pi.neg_apply]
  have hi : Integrable (F 0) := by
    simpa [F] using integrable_tilted H hH.continuous continuous_const
      ⟨m,hm,C,ht⟩ (growth_const (1:ℝ)) 0
  let A : ℝ := (‖gradient H 0‖+(K:ℝ)*‖v‖+(K:ℝ))*‖v‖*Real.exp (C+m*‖v‖^2)
  have hb (z : Point d) (t : ℝ) (ht' : t∈Set.Ioo (-1:ℝ) 1) :
      ‖F' t z‖ ≤ A*((1+‖z‖)*Real.exp (-(m/2)*‖z‖^2)) := by
    have hat : |t|≤1 := (abs_le.mpr ⟨ht'.1.le,ht'.2.le⟩)
    have hv : ‖t • v‖≤‖v‖ := by
      rw [norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right hat (norm_nonneg v)).trans_eq (one_mul _)
    have hn : ‖z+t • v‖≤‖z‖+‖v‖ := (norm_add_le _ _).trans (add_le_add le_rfl hv)
    have hn' : ‖z‖≤‖z+t • v‖+‖v‖ := by
      calc
        ‖z‖=‖(z+t • v)-t • v‖ := by congr 1; abel
        _ ≤ ‖z+t • v‖+‖t • v‖ := norm_sub_le _ _
        _ ≤ _ := add_le_add le_rfl hv
    have hs : ‖z‖^2≤2*‖z+t • v‖^2+2*‖v‖^2 := by
      have hh := pow_le_pow_left₀ (norm_nonneg z) hn' 2
      nlinarith [sq_nonneg (‖z+t • v‖-‖v‖)]
    have he : Real.exp (-H (z+t • v))≤
        Real.exp (C+m*‖v‖^2)*Real.exp (-(m/2)*‖z‖^2) := by
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hs hm.le
      nlinarith [ht (z+t • v)]
    have hg : ‖gradient H (z+t • v)‖ ≤
        (‖gradient H 0‖+(K:ℝ)*‖v‖+(K:ℝ))*(1+‖z‖) := by
      have hh := hL.dist_le_mul (z+t • v) 0
      rw [dist_zero_right] at hh
      have hh' := norm_add_le (gradient H (z+t • v)-gradient H 0) (gradient H 0)
      rw [sub_add_cancel,←dist_eq_norm] at hh'
      have hk := mul_le_mul_of_nonneg_left hn K.coe_nonneg
      nlinarith [mul_nonneg (norm_nonneg (gradient H 0)) (norm_nonneg z),
        mul_nonneg (mul_nonneg K.coe_nonneg (norm_nonneg v)) (norm_nonneg z)]
    dsimp [F']
    rw [abs_mul,abs_neg,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (‖gradient H (z+t • v)‖*‖v‖)*Real.exp (-H (z+t • v)) :=
        mul_le_mul_of_nonneg_right (abs_real_inner_le_norm _ _) (by positivity)
      _ ≤ (((‖gradient H 0‖+(K:ℝ)*‖v‖+(K:ℝ))*(1+‖z‖))*‖v‖)*
          (Real.exp (C+m*‖v‖^2)*Real.exp (-(m/2)*‖z‖^2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hg (norm_nonneg v)) he (by positivity) (by positivity)
      _ = _ := by dsimp [A]; ring
  have hint : Integrable (fun z : Point d => A*((1+‖z‖)*Real.exp (-(m/2)*‖z‖^2))) := by
    have hh := ((integrable_gaussian_envelope d (b:=m/2) (by positivity)).add
      (integrable_norm_pow_gaussian d 1 (b:=m/2) (by positivity))).const_mul A
    simpa [add_mul] using hh
  have hp := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=(volume:Measure (Point d))) (F:=F) (F':=F')
    (bound:=fun z => A*((1+‖z‖)*Real.exp (-(m/2)*‖z‖^2)))
    (x₀:=(0:ℝ)) (s:=Set.Ioo (-1:ℝ) 1) (Ioo_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall fun t =>
      (Real.continuous_exp.comp (hH.continuous.comp
        (continuous_id.add continuous_const)).neg).aestronglyMeasurable)
    hi
    (by
      have hh : Continuous (fun z => -(inner ℝ (gradient H z) v)*Real.exp (-H z)) :=
        (hgc.inner continuous_const).neg.mul (Real.continuous_exp.comp hH.continuous.neg)
      simpa [F'] using hh.aestronglyMeasurable)
    (Filter.Eventually.of_forall hb) hint (Filter.Eventually.of_forall fun z t _ => hd z t)
  have he (t : ℝ) : (∫ z,F t z)=∫ z,Real.exp (-H z) := by
    exact integral_add_right_eq_self (fun z => Real.exp (-H z)) (t • v)
  have hh := hp.2.unique ((hasDerivAt_const (0:ℝ) (∫ z,Real.exp (-H z))).congr_of_eventuallyEq
    (Filter.Eventually.of_forall he))
  refine ⟨?_,?_⟩
  · simpa [F',neg_mul] using hp.1.neg
  · simpa only [F',zero_smul,add_zero,neg_mul,integral_neg,neg_eq_zero] using hh

lemma integral_gradient_gibbs_zero {d : ℕ} {H : Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ 1 H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) :
    (∫ z,gradient H z ∂gibbs H)=0 := by
  have hd : Integrable (fun z => Real.exp (-H z)) := by
    simpa using integrable_tilted H hH.continuous continuous_const ht (growth_const (1:ℝ)) 0
  have hi : Integrable (fun z => Real.exp (-H z) • gradient H z) := by
    simpa using integrable_tilted H hH.continuous hL.continuous ht (growth_of_lipschitz hL) 0
  have hz : (∫ z,Real.exp (-H z) • gradient H z)=0 := by
    apply ext_inner_right ℝ
    intro v
    rw [inner_zero_left,real_inner_comm,←integral_inner hi]
    simpa [inner_smul_right,mul_comm,real_inner_comm] using
      (translation_integration_by_parts hH ht hL v).2
  rw [integral_gibbs_vector hH.continuous hd,hz,smul_zero]
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

lemma conditionalPotential_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) (r ρ : ℝ) (y : Point d) :
    ContDiff ℝ 2 (conditionalPotential F x r ρ y) :=
  (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).div_const _).add
    (hF.smooth.comp (contDiff_const.add (contDiff_id.const_smul r)))

lemma conditionalPotential_gradient {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) (r ρ : ℝ) (y z : Point d) :
    gradient (conditionalPotential F x r ρ y) z=
      (1/(1-ρ^2)) • (z-ρ • y)+r • primitiveField F x r z := by
  apply HasGradientAt.gradient
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hg := (hasStrictFDerivAt_norm_sq (z-ρ • y)).hasFDerivAt.comp z
    ((hasFDerivAt_id z).sub_const (ρ • y))
  have hh := (hF.smooth.differentiable (by norm_num) (x+r • z)).hasFDerivAt.comp z
    (((hasFDerivAt_id z).const_smul r).const_add x)
  have hd := (hg.const_smul (1/(2*(1-ρ^2)))).add hh
  convert! hd using 1
  · funext w
    simp only [conditionalPotential,Pi.add_apply,Pi.smul_apply,Function.comp_apply,smul_eq_mul,id_eq]
    ring
  ext v
  simp only [add_apply,smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,smul_eq_mul,InnerProductSpace.toDual_apply_apply,
    inner_add_left,real_inner_smul_left,innerSL_apply_apply,map_smul,←toDual_gradient,
    primitiveField]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma conditionalPotential_gradient_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r) (ha : 0<1-ρ^2)
    (y : Point d) : LipschitzWith ⟨1/(1-ρ^2)+(lam:ℝ)*r^2,by positivity⟩
      (gradient (conditionalPotential F x r ρ y)) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simp only [conditionalPotential_gradient hF,dist_eq_norm]
  have he : (1/(1-ρ^2)) • (u-ρ • y)+r • primitiveField F x r u-
      ((1/(1-ρ^2)) • (v-ρ • y)+r • primitiveField F x r v)=
      (1/(1-ρ^2)) • (u-v)+r • (primitiveField F x r u-primitiveField F x r v) := by
    simp only [smul_sub]; abel
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hr,
    abs_of_pos (div_pos zero_lt_one ha)]
  have hh := (primitiveField_lipschitz hF x hr).dist_le_mul u v
  simp only [dist_eq_norm,NNReal.coe_mul,NNReal.coe_mk] at hh
  have hb := mul_le_mul_of_nonneg_left hh hr
  change _ ≤ (1/(1-ρ^2)+(lam:ℝ)*r^2)*‖u-v‖
  nlinarith

lemma conditional_identity_integrable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    Integrable (fun z => z) (gibbs (conditionalPotential F x r ρ y)) := by
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  exact (Appell.HasGrowth.lipschitz (LipschitzWith.id (α:=Point d))).integrable
    continuous_id.aestronglyMeasurable
    (conditionalLaw_hasExpMoments hF x hr hl hρ0 hρ1 y).hasMoments

theorem conditional_mean_identity {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    (∫ z,z ∂gibbs (conditionalPotential F x r ρ y))=
      ρ • y-((1-ρ^2)*r) • conditionalFieldMean F x r ρ y := by
  have ha := (probability_time hρ0 hρ1).1
  let μ := gibbs (conditionalPotential F x r ρ y)
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  have hz := integral_gradient_gibbs_zero
    ((conditionalPotential_smooth hF x r ρ y).of_le (by norm_num))
    (conditional_hasGaussianLowerTail hF x hr hl hρ0 hρ1 y)
    (conditionalPotential_gradient_lipschitz hF x hr ha y)
  have hi := conditional_identity_integrable hF x hr hl hρ0 hρ1 y
  have hf := conditionalField_integrable hF x hr hl hρ0 hρ1 y
  simp_rw [conditionalPotential_gradient hF] at hz
  have he := integral_scaled_affine_add (μ:=μ) hi hf (1/(1-ρ^2)) r (ρ • y)
  rw [he] at hz
  change (1/(1-ρ^2)) • ((∫ z,z ∂μ)-ρ • y)+r • conditionalFieldMean F x r ρ y=0 at hz
  have hh := congrArg (fun z : Point d => (1-ρ^2) • z) hz
  rw [smul_add,smul_smul,smul_smul,smul_zero,mul_one_div_cancel ha.ne',one_smul] at hh
  apply eq_sub_iff_add_eq.mpr
  have hh' : (∫ z,z ∂μ)+((1-ρ^2)*r) • conditionalFieldMean F x r ρ y-ρ • y=0 := by
    convert! hh using 1; abel
  exact sub_eq_zero.mp hh'
end LogConcaveSampling
namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

lemma hasGradientAt_log_tiltedIntegral {d : ℕ} {H : Point d → ℝ}
    (hH : Continuous H) (ht : HasGaussianLowerTail H) (θ : Point d) :
    HasGradientAt (fun θ => Real.log (tiltedIntegral H (fun _ => (1:ℝ)) θ))
      (tiltedExpectation H (fun z => z) θ) θ := by
  have hd := (hasFDerivAt_tiltedIntegral H hH continuous_const ht (growth_const (1:ℝ)) θ).log
    (tilted_partition_pos hH ht θ).ne'
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  ext v
  have hi := integrable_tilted H hH continuous_id ht (growth_of_lipschitz (LipschitzWith.id (α:=Point d))) θ
  have hiD := integrable_tilted H hH (continuous_tiltDerivativeIntegrand continuous_const) ht
    (growth_tiltDerivativeIntegrand (growth_const (1:ℝ))) θ
  simp only [tiltedExpectation,InnerProductSpace.toDual_apply_apply,real_inner_smul_left,
    smul_apply,smul_eq_mul]
  congr 1
  rw [real_inner_comm]
  simp only [tiltedIntegral]
  simp only [id_eq] at hi
  rw [←integral_inner (𝕜:=ℝ) hi v]
  change (∫ z,inner ℝ v (Real.exp (inner ℝ θ z-H z) • z))=
    (∫ z,Real.exp (inner ℝ θ z-H z) • tiltDerivativeIntegrand (fun _ => (1:ℝ)) z) v
  rw [ContinuousLinearMap.integral_apply hiD]
  apply integral_congr_ae
  filter_upwards [] with z
  simp [tiltDerivativeIntegrand,real_inner_comm,mul_comm,real_inner_smul_right]

lemma quadraticTilt_eq_tilted {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (H : Point d → ℝ) (h : Point d → E) (θ : Point d) (c : ℝ) :
    quadraticTilt H h (θ,c)=tiltedIntegral (fun z => H z+c*‖z‖^2) h θ := by
  unfold quadraticTilt tiltedIntegral
  congr 1; funext z; congr 2; dsimp; ring

lemma hasGradientAt_interpolationPotential {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    HasGradientAt (interpolationPotential F x r ρ)
      (y+(r*ρ) • conditionalFieldMean F x r ρ y) y := by
  have ha := (probability_time hρ0 hρ1).1
  let a := 1-ρ^2
  let H := fun z => primitivePotential F x r z+(ρ^2/(2*a))*‖z‖^2
  have hc : Continuous H := (hF.continuous_potential x r).add
    (continuous_const.mul (continuous_norm.pow 2))
  have ht : HasGaussianLowerTail H := by
    obtain ⟨m,hm,C,hC⟩ := hF.hasGaussianLowerTail x hr (by linarith)
    refine ⟨m,hm,C,fun z => ?_⟩
    have hp : 0≤(ρ^2/(2*a))*‖z‖^2 := by dsimp [a]; positivity
    dsimp [H]; linarith [hC z]
  have hd := (hasGradientAt_log_tiltedIntegral hc ht ((ρ/a) • y)).hasFDerivAt.comp y
    ((hasFDerivAt_id y).const_smul (ρ/a))
  have hn := ((hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_smul (1/(2*a))).sub hd
  have he : tiltedExpectation H (fun z => z) ((ρ/a) • y)=
      ρ • y-(a*r) • conditionalFieldMean F x r ρ y := by
    rw [←conditional_mean_identity hF x hr hl hρ0 hρ1 y]
    rw [conditional_integral_quadratic hF x hr (by linarith)
      (by linarith) y]
    simp only [quadraticExpectation,conditionalParameter,quadraticTilt_eq_tilted,a,tiltedExpectation,H]
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert! hn using 1
  · funext z
    simp only [interpolationPotential,conditionalParameter,quadraticTilt_eq_tilted,
      Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Function.comp_apply,H,a]
    ring
  ext v
  simp only [sub_apply,smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,smul_eq_mul,InnerProductSpace.toDual_apply_apply,
    real_inner_smul_left,inner_add_left,inner_smul_right,he,inner_sub_left,
    innerSL_apply_apply]
  dsimp [a]
  field_simp
  ring

lemma interpolationPotential_gradient {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    gradient (interpolationPotential F x r ρ) y=
      y+(r*ρ) • conditionalFieldMean F x r ρ y :=
  (hasGradientAt_interpolationPotential hF x hr hl hρ0 hρ1 y).gradient
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_GaussianMarginalLowerTail
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
open scoped RealInnerProductSpace NNReal

lemma interpolationPotential_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    ContDiff ℝ (⊤ : ℕ∞) (interpolationPotential F x r ρ) := by
  let g := fun y => y+(r*ρ) • conditionalFieldMean F x r ρ y
  have hg : ContDiff ℝ (⊤ : ℕ∞) g :=
    contDiff_id.add ((conditionalFieldMean_smooth hF x hr hl hρ0 hρ1).const_smul (r*ρ))
  have hd : ∀y,HasFDerivAt (interpolationPotential F x r ρ) ((innerSL ℝ) (g y)) y := by
    intro y
    exact (hasGradientAt_interpolationPotential hF x hr hl hρ0 hρ1 y).hasFDerivAt
  apply contDiff_infty_iff_fderiv.mpr
  refine ⟨fun y => (hd y).differentiableAt,?_⟩
  have he : fderiv ℝ (interpolationPotential F x r ρ)=fun y => (innerSL ℝ) (g y) :=
    funext (fun y => (hd y).fderiv)
  rw [he]
  exact (innerSL ℝ).contDiff.comp hg

end LogConcaveSampling

end

end

end

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
open Set Function
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {a b : ℝ} {f : ℝ → E → E} {K : ℝ≥0}
  (hL : ∀ t∈Icc a b,LipschitzWith K (f t))

variable [CompleteSpace E] (hf : Continuous (uncurry f))

lemma flow_continuous (s : Icc a b) (x : E) : Continuous (flow hL hf s x) :=
  (exists_curve s hf hL x).choose_spec.1

lemma flow_initial (s : Icc a b) (x : E) : flow hL hf s x s=x :=
  (exists_curve s hf hL x).choose_spec.2.1

lemma flow_deriv (s : Icc a b) (x : E) (t : ℝ) (ht : t∈Icc a b) :
    HasDerivWithinAt (flow hL hf s x) (f t (flow hL hf s x t)) (Icc a b) t :=
  (exists_curve s hf hL x).choose_spec.2.2 t ht

lemma flow_lipschitz (s t : Icc a b) :
    LipschitzWith ⟨Real.exp ((K:ℝ)*|(t:ℝ)-(s:ℝ)|), (Real.exp_pos _).le⟩
      (fun x => flow hL hf s x t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := trajectory_dist hL (flow_continuous hL hf s x).continuousOn
    (flow_deriv hL hf s x) (flow_continuous hL hf s y).continuousOn
    (flow_deriv hL hf s y) s t
  rw [flow_initial,flow_initial,mul_comm] at hh
  exact hh

lemma flow_cocycle (s t u : Icc a b) (x : E) :
    flow hL hf t (flow hL hf s x t) u=flow hL hf s x u := by
  have hh := trajectory_dist hL
    (flow_continuous hL hf t (flow hL hf s x t)).continuousOn
    (flow_deriv hL hf t (flow hL hf s x t))
    (flow_continuous hL hf s x).continuousOn (flow_deriv hL hf s x) t u
  rw [flow_initial,dist_self,zero_mul,dist_le_zero] at hh
  exact hh

def flowHomeomorph (s t : Icc a b) : E ≃ₜ E where
  toFun x := flow hL hf s x t
  invFun y := flow hL hf t y s
  left_inv x := by dsimp; rw [flow_cocycle,flow_initial]
  right_inv y := by dsimp; rw [flow_cocycle,flow_initial]
  continuous_toFun := (flow_lipschitz hL hf s t).continuous
  continuous_invFun := (flow_lipschitz hL hf t s).continuous
end LogConcaveSampling.GlobalODE
namespace LogConcaveSampling.GlobalODE
open Set Function
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (s : Icc a b) {A : ℝ → E →L[ℝ] E} (hA : Continuous A)
    {K : ℝ≥0} (hK : ∀ t∈Icc a b,‖A t‖≤K)

def fundamental : ℝ → E →L[ℝ] E :=
  flow (linear_field_lipschitz hK) ((hA.comp continuous_fst).clm_comp continuous_snd) s (ContinuousLinearMap.id ℝ E)

lemma fundamental_continuous : Continuous (fundamental s hA hK) :=
  flow_continuous _ _ _ _

lemma fundamental_initial : fundamental s hA hK s=ContinuousLinearMap.id ℝ E :=
  flow_initial _ _ _ _

lemma fundamental_deriv (t : ℝ) (ht : t∈Icc a b) :
    HasDerivWithinAt (fundamental s hA hK) ((A t).comp (fundamental s hA hK t)) (Icc a b) t :=
  flow_deriv _ _ _ _ t ht

lemma fundamental_apply_deriv (v : E) (t : ℝ) (ht : t∈Icc a b) :
    HasDerivWithinAt (fun u => fundamental s hA hK u v)
      (A t (fundamental s hA hK t v)) (Icc a b) t := by
  simpa using (fundamental_deriv s hA hK t ht).clm_apply (hasDerivWithinAt_const t (Icc a b) v)

lemma fundamental_apply_initial (v : E) : fundamental s hA hK s v=v := by
  rw [fundamental_initial]; rfl

lemma fundamental_apply_bound (v : E) (t : Icc a b) :
    ‖fundamental s hA hK t v‖≤‖v‖*Real.exp ((K:ℝ)*|(t:ℝ)-(s:ℝ)|) := by
  have hL : ∀ t∈Icc a b,LipschitzWith K (fun v : E => A t v) := by
    intro t ht
    exact (A t).lipschitz.weaken (hK t ht)
  have hh := trajectory_dist hL
    ((fundamental_continuous s hA hK).clm_apply continuous_const).continuousOn
    (fundamental_apply_deriv s hA hK v)
    (continuousOn_const (c:=(0:E))) (fun t ht => by simpa using hasDerivWithinAt_const t (Icc a b) (0:E)) s t
  simpa [fundamental_apply_initial,dist_zero_right] using hh

lemma fundamental_norm_bound (t : Icc a b) :
    ‖fundamental s hA hK t‖≤Real.exp ((K:ℝ)*|(t:ℝ)-(s:ℝ)|) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro v
  simpa only [mul_comm] using fundamental_apply_bound s hA hK v t
end LogConcaveSampling.GlobalODE
namespace LogConcaveSampling.GlobalODE
open Set Function Filter Metric
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [ProperSpace E]
    {a b : ℝ} (hab : a≤b) {f : ℝ → E → E} (hc : Continuous (uncurry f))
    {K : ℝ≥0} (hL : ∀ t∈Icc a b,LipschitzWith K (f t))
    {D : ℝ → E → E →L[ℝ] E} (hD : Continuous (uncurry D))
    (hf : ∀ t z,HasFDerivAt (f t) (D t z) z)

def flowSpatialCoefficient (x : E) (u : ℝ) : E →L[ℝ] E :=
  D u (flow hL hc ⟨a,le_rfl,hab⟩ x u)

omit [ProperSpace E] in
include hD in
lemma flowSpatialCoefficient_continuous (x : E) :
    Continuous (flowSpatialCoefficient hab hc hL (D:=D) x) :=
  hD.comp (continuous_id.prodMk (flow_continuous hL hc ⟨a,le_rfl,hab⟩ x))

omit [ProperSpace E] in
include hf in
lemma flowSpatialCoefficient_bound (x : E) (u : ℝ) (hu : u∈Icc a b) :
    ‖flowSpatialCoefficient hab hc hL (D:=D) x u‖≤K := by
  rw [show flowSpatialCoefficient hab hc hL (D:=D) x u =
      fderiv ℝ (f u) (flow hL hc ⟨a,le_rfl,hab⟩ x u) from (hf u _).fderiv.symm]
  exact norm_fderiv_le_of_lipschitz ℝ (hL u hu)

def flowLinearization (x : E) : ℝ → E →L[ℝ] E :=
  fundamental ⟨a,le_rfl,hab⟩ (flowSpatialCoefficient_continuous hab hc hL hD x)
    (flowSpatialCoefficient_bound hab hc hL hf x)

include hD hf in

theorem flow_hasFDerivAt_left (x : E) (t : Icc a b) :
    HasFDerivAt (fun z => flow hL hc ⟨a,le_rfl,hab⟩ z t)
      (flowLinearization hab hc hL hD hf x t) x := by
  let s : Icc a b := ⟨a,le_rfl,hab⟩
  let α (z : E) := flow hL hc s z
  let A (u : ℝ) := D u (α x u)
  have hA : Continuous A := hD.comp (continuous_id.prodMk (flow_continuous hL hc s x))
  have hK : ∀ u∈Icc a b,‖A u‖≤K := by
    intro u hu
    rw [show A u=fderiv ℝ (f u) (α x u) from (hf u (α x u)).fderiv.symm]
    exact norm_fderiv_le_of_lipschitz ℝ (hL u hu)
  let J := fundamental s hA hK
  change HasFDerivAt _ (J t) x
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  apply Asymptotics.isLittleO_iff.mpr
  intro c hcpos
  obtain ⟨R,hR⟩ := isCompact_Icc.exists_bound_of_continuousOn (flow_continuous hL hc s x).continuousOn
  let B := Real.exp ((K:ℝ)*(b-a))
  have hB : 0<B := Real.exp_pos _
  let G := gronwallBound 0 (K:ℝ) 1 ((t:ℝ)-a)
  let ε := c/(B*(|G|+1))
  have hε : 0<ε := div_pos hcpos (mul_pos hB (by positivity))
  obtain ⟨δ,hδ,hT⟩ := uniform_taylor_compact hD hf a b R ε hε
  filter_upwards [Metric.ball_mem_nhds (0:E) (div_pos hδ hB)] with v hv
  have hvδ : ‖v‖<δ/B := by simpa only [mem_ball,dist_zero_right] using hv
  have hΔ (u : Icc a b) : ‖α (x+v) u-α x u‖≤B*‖v‖ := by
    have hh := (flow_lipschitz hL hc s u).dist_le_mul (x+v) x
    simp only [dist_eq_norm,add_sub_cancel_left] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (by
        change |(u:ℝ)-a|≤b-a
        rw [abs_of_nonneg (sub_nonneg.mpr u.2.1)]
        linarith [u.2.2]) K.coe_nonneg)) (norm_nonneg v))
  let w (u : ℝ) := α (x+v) u-α x u-J u v
  let w' (u : ℝ) := f u (α (x+v) u)-f u (α x u)-A u (J u v)
  have hw : Continuous w := ((flow_continuous hL hc s (x+v)).sub
    (flow_continuous hL hc s x)).sub ((fundamental_continuous s hA hK).clm_apply continuous_const)
  have hwd (u : ℝ) (hu : u∈Icc a b) : HasDerivWithinAt w (w' u) (Icc a b) u :=
    ((flow_deriv hL hc s (x+v) u hu).sub (flow_deriv hL hc s x u hu)).sub
      (fundamental_apply_deriv s hA hK v u hu)
  have hw0 : w a=0 := by
    change flow hL hc s (x+v) s-flow hL hc s x s-fundamental s hA hK s v=0
    rw [flow_initial,flow_initial,fundamental_apply_initial]
    abel
  have hwb (u : ℝ) (hu : u∈Icc a b) : ‖w' u‖≤(K:ℝ)*‖w u‖+ε*B*‖v‖ := by
    let Δ := α (x+v) u-α x u
    have hsmall : ‖Δ‖<δ := (hΔ ⟨u,hu⟩).trans_lt (by simpa only [mul_comm] using (lt_div_iff₀ hB).mp hvδ)
    have he := hT u hu (α x u) (hR u hu) Δ hsmall
    have hid : α x u+Δ=α (x+v) u := by dsimp [Δ]; abel
    rw [hid] at he
    have heq : w' u=A u (w u)+(f u (α (x+v) u)-f u (α x u)-A u Δ) := by
      dsimp [w',w,Δ]
      simp only [map_sub]
      abel
    rw [heq]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact (A u).le_of_opNorm_le (hK u hu) _
    · exact (he.trans (mul_le_mul_of_nonneg_left (hΔ ⟨u,hu⟩) hε.le)).trans_eq (by ring)
  have hwd' (u : ℝ) (hu : u∈Ico a b) : HasDerivWithinAt w (w' u) (Ici u) u := by
    apply (hwd u ⟨hu.1,hu.2.le⟩).mono_of_mem_nhdsWithin
    exact inter_mem (Filter.mem_of_superset self_mem_nhdsWithin (Ici_subset_Ici.mpr hu.1))
      (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hu.2))
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hw.continuousOn hwd'
    (by simp [hw0] : ‖w a‖≤(0:ℝ)) (fun u hu => hwb u ⟨hu.1,hu.2.le⟩) t t.2
  rw [gronwallBound_zero_linear] at hg
  change ‖w t‖ ≤ c*‖v‖
  calc
    _ ≤ (ε*B*‖v‖)*G := hg
    _ ≤ (ε*B*‖v‖)*(|G|+1) := mul_le_mul_of_nonneg_left (by linarith [le_abs_self G]) (by positivity)
    _ = c*‖v‖ := by dsimp [ε]; field_simp
end LogConcaveSampling.GlobalODE
namespace LogConcaveSampling.GlobalODE
open Set Function Filter Metric
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b : ℝ} {f : ℝ → E → E} {K : ℝ≥0}
  (hL : ∀ t∈Icc a b,LipschitzWith K (f t)) (hc : Continuous (uncurry f))

lemma flow_joint_continuous (s : Icc a b) :
    Continuous (fun p : E × Icc a b => flow hL hc s p.1 p.2) := by
  apply continuous_prod_of_continuous_lipschitzWith _
    ⟨Real.exp ((K:ℝ)*(b-a)),(Real.exp_pos _).le⟩
  · intro x
    exact (flow_continuous hL hc s x).comp continuous_subtype_val
  · intro t
    apply (flow_lipschitz hL hc s t).weaken
    change Real.exp _ ≤ Real.exp _
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
    rw [abs_le]
    constructor <;> linarith [s.2.1,s.2.2,t.2.1,t.2.2]

variable (hab : a≤b) {A B : ℝ → E →L[ℝ] E}
  (hA : Continuous A) (hB : Continuous B)
  (hKA : ∀ t∈Icc a b,‖A t‖≤K) (hKB : ∀ t∈Icc a b,‖B t‖≤K)

lemma fundamental_difference_bound {δ : ℝ} (hδ : 0≤δ)
    (hAB : ∀ t∈Icc a b,‖A t-B t‖≤δ) (t : Icc a b) :
    ‖fundamental ⟨a,le_rfl,hab⟩ hA hKA t-fundamental ⟨a,le_rfl,hab⟩ hB hKB t‖ ≤
      gronwallBound 0 (K:ℝ) (δ*Real.exp ((K:ℝ)*(b-a))) ((t:ℝ)-a) := by
  let s : Icc a b := ⟨a,le_rfl,hab⟩
  let J := fundamental s hA hKA
  let L := fundamental s hB hKB
  let w (u : ℝ) := J u-L u
  let w' (u : ℝ) := (A u).comp (J u)-(B u).comp (L u)
  have hd (u : ℝ) (hu : u∈Icc a b) : HasDerivWithinAt w (w' u) (Icc a b) u :=
    (fundamental_deriv s hA hKA u hu).sub (fundamental_deriv s hB hKB u hu)
  have hn (u : ℝ) (hu : u∈Icc a b) :
      ‖w' u‖≤(K:ℝ)*‖w u‖+δ*Real.exp ((K:ℝ)*(b-a)) := by
    have he : w' u=(A u).comp (w u)+(A u-B u).comp (L u) := by
      dsimp [w',w]
      simp only [ContinuousLinearMap.comp_sub,ContinuousLinearMap.sub_comp]
      abel
    rw [he]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (hKA u hu) (norm_nonneg _))
    · apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
      apply mul_le_mul (hAB u hu) _ (norm_nonneg _) hδ
      apply (fundamental_norm_bound s hB hKB ⟨u,hu⟩).trans
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
      change |u-a|≤b-a
      rw [abs_of_nonneg (sub_nonneg.mpr hu.1)]
      linarith [hu.2]
  apply norm_le_gronwallBound_of_norm_deriv_right_le
    ((fundamental_continuous s hA hKA).sub (fundamental_continuous s hB hKB)).continuousOn
    (fun u hu => ?_) (by
      change ‖fundamental s hA hKA s-fundamental s hB hKB s‖≤0
      rw [fundamental_initial,fundamental_initial,sub_self,norm_zero]) (fun u hu => hn u ⟨hu.1,hu.2.le⟩) t t.2
  apply (hd u ⟨hu.1,hu.2.le⟩).mono_of_mem_nhdsWithin
  exact inter_mem (Filter.mem_of_superset self_mem_nhdsWithin (Ici_subset_Ici.mpr hu.1))
    (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hu.2))
end LogConcaveSampling.GlobalODE
namespace LogConcaveSampling.GlobalODE
open Set Function Filter Metric
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {X : Type*} [TopologicalSpace X] {a b : ℝ} (hab : a≤b)
  {K : ℝ≥0} {A : X → ℝ → E →L[ℝ] E}
  (hA : ∀ x,Continuous (A x))
  (hK : ∀ x t,t∈Icc a b → ‖A x t‖≤K)
  (hpA : Continuous (fun p : X × Icc a b => A p.1 p.2))

include hpA in
lemma fundamental_parameter_continuous (t : Icc a b) :
    Continuous (fun x => fundamental ⟨a,le_rfl,hab⟩ (hA x) (hK x) t) := by
  let P (x : X) : C(Icc a b,E →L[ℝ] E) :=
    ⟨fun u => A x u,(hA x).comp continuous_subtype_val⟩
  have hP : Continuous P := ContinuousMap.continuous_of_continuous_uncurry P hpA
  rw [continuous_iff_continuousAt]
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let B := Real.exp ((K:ℝ)*(b-a))
  let G := gronwallBound 0 (K:ℝ) 1 ((t:ℝ)-a)
  have hC : 0<B*(|G|+1) := mul_pos (Real.exp_pos _) (by positivity)
  filter_upwards [((Metric.tendsto_nhds (u:=P) (a:=P x)).mp (hP.tendsto x)) (ε/(B*(|G|+1))) (div_pos hε hC)] with y hy
  have hh := fundamental_difference_bound hab (hA y) (hA x) (hK y) (hK x)
    (dist_nonneg (x:=P y) (y:=P x)) (fun u hu => by
      rw [←dist_eq_norm]
      exact ContinuousMap.dist_apply_le_dist (f:=P y) (g:=P x) ⟨u,hu⟩) t
  rw [gronwallBound_zero_linear] at hh
  rw [dist_eq_norm]
  calc
    _ ≤ (dist (P y) (P x)*B)*G := hh
    _ ≤ (dist (P y) (P x)*B)*(|G|+1) :=
      mul_le_mul_of_nonneg_left (by linarith [le_abs_self G]) (mul_nonneg dist_nonneg (Real.exp_pos _).le)
    _ < ε := by
      rw [mul_assoc]
      exact (lt_div_iff₀ hC).mp hy
end LogConcaveSampling.GlobalODE
namespace LogConcaveSampling.GlobalODE
open Set Function
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [ProperSpace E] {a b : ℝ} (hab : a≤b)
    {f : ℝ → E → E} (hc : Continuous (uncurry f))
    {K : ℝ≥0} (hL : ∀ t∈Icc a b,LipschitzWith K (f t))
    {D : ℝ → E → E →L[ℝ] E} (hD : Continuous (uncurry D))
    (hf : ∀ t z,HasFDerivAt (f t) (D t z) z)

omit [ProperSpace E] in
lemma flowLinearization_continuous_initial (t : Icc a b) :
    Continuous (fun x => flowLinearization hab hc hL hD hf x t) := by
  apply fundamental_parameter_continuous hab
    (flowSpatialCoefficient_continuous hab hc hL hD)
    (flowSpatialCoefficient_bound hab hc hL hf) _ t
  exact hD.comp ((continuous_subtype_val.comp continuous_snd).prodMk
    (flow_joint_continuous hL hc ⟨a,le_rfl,hab⟩))

include hD hf in

lemma flow_contDiff_one_left (t : Icc a b) :
    ContDiff ℝ 1 (fun x => flow hL hc ⟨a,le_rfl,hab⟩ x t) :=
  contDiff_one_iff_hasFDerivAt.mpr ⟨fun x => flowLinearization hab hc hL hD hf x t,
    flowLinearization_continuous_initial hab hc hL hD hf t,
    fun x => flow_hasFDerivAt_left hab hc hL hD hf x t⟩
end LogConcaveSampling.GlobalODE
namespace LogConcaveSampling.GlobalODE
open Set Function
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} {A : ℝ → E →L[ℝ] E} (hA : Continuous A)
    {K : ℝ≥0} (hK : ∀ t∈Icc a b,‖A t‖≤K)

lemma fundamental_cocycle (s t u : Icc a b) (v : E) :
    fundamental t hA hK u (fundamental s hA hK t v)=fundamental s hA hK u v := by
  have hL : ∀ t∈Icc a b,LipschitzWith K (A t) := fun t ht =>
    (A t).lipschitz.weaken (by exact_mod_cast hK t ht)
  have hh := trajectory_dist hL
    ((fundamental_continuous t hA hK).clm_apply continuous_const).continuousOn
    (fundamental_apply_deriv t hA hK (fundamental s hA hK t v))
    ((fundamental_continuous s hA hK).clm_apply continuous_const).continuousOn
    (fundamental_apply_deriv s hA hK v) t u
  rw [fundamental_apply_initial,dist_self,zero_mul,dist_le_zero] at hh
  exact hh

def fundamentalEquiv (s t : Icc a b) : E ≃L[ℝ] E where
  toLinearEquiv :=
    { (fundamental s hA hK t).toLinearMap with
      invFun := fundamental t hA hK s
      left_inv := fun v => by
        change fundamental t hA hK s (fundamental s hA hK t v)=v
        rw [fundamental_cocycle,fundamental_apply_initial]
      right_inv := fun v => by
        change fundamental s hA hK t (fundamental t hA hK s v)=v
        rw [fundamental_cocycle,fundamental_apply_initial] }
  continuous_toFun := (fundamental s hA hK t).continuous
  continuous_invFun := (fundamental t hA hK s).continuous

end LogConcaveSampling.GlobalODE

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_SpaceTimeForward
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
open Set Function Filter Metric
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (hab : a≤b) {f : ℝ → E → E} (hc : Continuous (uncurry f))
    {K : ℝ≥0} (hL : ∀ t∈Icc a b,LipschitzWith K (f t))

def spaceTimeForward (p : ℝ × E) : ℝ × E :=
  (p.1,flow hL hc ⟨a,le_rfl,hab⟩ p.2 (projIcc a b hab p.1))
def spaceTimeBackward (p : ℝ × E) : ℝ × E :=
  (p.1,flow hL hc (projIcc a b hab p.1) p.2 a)

lemma spaceTimeForward_continuous : Continuous (spaceTimeForward hab hc hL) :=
  continuous_fst.prodMk ((flow_joint_continuous hL hc ⟨a,le_rfl,hab⟩).comp
    (continuous_snd.prodMk ((continuous_projIcc (h:=hab)).comp continuous_fst)))

lemma spaceTime_left_inverse : LeftInverse (spaceTimeBackward hab hc hL) (spaceTimeForward hab hc hL) := by
  intro p
  apply Prod.ext
  · rfl
  change flow hL hc (projIcc a b hab p.1)
    (flow hL hc ⟨a,le_rfl,hab⟩ p.2 (projIcc a b hab p.1)) a=p.2
  rw [flow_cocycle hL hc ⟨a,le_rfl,hab⟩ (projIcc a b hab p.1) ⟨a,le_rfl,hab⟩,flow_initial]
lemma spaceTime_right_inverse : RightInverse (spaceTimeBackward hab hc hL) (spaceTimeForward hab hc hL) := by
  intro p
  apply Prod.ext
  · rfl
  change flow hL hc ⟨a,le_rfl,hab⟩ (flow hL hc (projIcc a b hab p.1) p.2 a)
    (projIcc a b hab p.1)=p.2
  rw [flow_cocycle hL hc (projIcc a b hab p.1) ⟨a,le_rfl,hab⟩ (projIcc a b hab p.1),flow_initial]

lemma spaceTimeBackward_continuous : Continuous (spaceTimeBackward hab hc hL) := by
  apply continuous_fst.prodMk
  rw [continuous_iff_continuousAt]
  intro p
  let z := (spaceTimeBackward hab hc hL p).2
  let B := Real.exp ((K:ℝ)*(b-a))
  have hB : 0<B := Real.exp_pos _
  have he : flow hL hc ⟨a,le_rfl,hab⟩ z (projIcc a b hab p.1)=p.2 :=
    congrArg Prod.snd (spaceTime_right_inverse hab hc hL p)
  have hh : Continuous (fun q : ℝ × E =>
      q.2-flow hL hc ⟨a,le_rfl,hab⟩ z (projIcc a b hab q.1)) :=
    continuous_snd.sub ((flow_continuous hL hc ⟨a,le_rfl,hab⟩ z).comp
      (continuous_subtype_val.comp ((continuous_projIcc (h:=hab)).comp continuous_fst)))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hn : ∀ᶠ q in 𝓝 p,‖q.2-flow hL hc ⟨a,le_rfl,hab⟩ z (projIcc a b hab q.1)‖<ε/B := by
    have he0 : p.2-flow hL hc ⟨a,le_rfl,hab⟩ z (projIcc a b hab p.1)=0 := by rw [he,sub_self]
    simpa only [he0,dist_zero_right] using (Metric.tendsto_nhds.mp (hh.tendsto p)) (ε/B) (div_pos hε hB)
  filter_upwards [hn] with q hq
  have hdist := (flow_lipschitz hL hc (projIcc a b hab q.1) ⟨a,le_rfl,hab⟩).dist_le_mul q.2
    (flow hL hc ⟨a,le_rfl,hab⟩ z (projIcc a b hab q.1))
  rw [flow_cocycle hL hc ⟨a,le_rfl,hab⟩ (projIcc a b hab q.1) ⟨a,le_rfl,hab⟩,flow_initial] at hdist
  change dist (flow hL hc (projIcc a b hab q.1) q.2 a) z<ε
  apply hdist.trans_lt
  have hmax : Real.exp ((K:ℝ)*|a-(projIcc a b hab q.1:ℝ)|)≤B := by
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
    rw [abs_of_nonpos (sub_nonpos.mpr (projIcc a b hab q.1).2.1)]
    linarith [(projIcc a b hab q.1).2.2]
  apply (mul_le_mul_of_nonneg_right hmax dist_nonneg).trans_lt
  rw [dist_eq_norm,mul_comm]
  exact (lt_div_iff₀ hB).mp hq

def spaceTimeHomeomorph : (ℝ × E) ≃ₜ (ℝ × E) where
  toFun := spaceTimeForward hab hc hL
  invFun := spaceTimeBackward hab hc hL
  left_inv := spaceTime_left_inverse hab hc hL
  right_inv := spaceTime_right_inverse hab hc hL
  continuous_toFun := spaceTimeForward_continuous hab hc hL
  continuous_invFun := spaceTimeBackward_continuous hab hc hL
end LogConcaveSampling.GlobalODE

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

variable [CompleteSpace E] [ProperSpace E]
    {a b : ℝ} (hab : a≤b) {f : ℝ → E → E} (hc : Continuous (uncurry f))
    {K : ℝ≥0} (hL : ∀ t∈Icc a b,LipschitzWith K (f t))
    {D : ℝ → E → E →L[ℝ] E} (hD : Continuous (uncurry D))
    (hf : ∀ t z,HasFDerivAt (f t) (D t z) z)

omit [ProperSpace E] in
lemma spaceTimeForward_time_deriv (p : ℝ × E) (hp : p.1∈Ioo a b) :
    HasDerivAt (fun t => (spaceTimeForward hab hc hL (t,p.2)).2)
      (f p.1 (spaceTimeForward hab hc hL p).2) p.1 := by
  have hpi : p.1∈Icc a b := ⟨hp.1.le,hp.2.le⟩
  have hh := (flow_deriv hL hc ⟨a,le_rfl,hab⟩ p.2 p.1 hpi).hasDerivAt
    (Icc_mem_nhds hp.1 hp.2)
  have he : (spaceTimeForward hab hc hL p).2=flow hL hc ⟨a,le_rfl,hab⟩ p.2 p.1 := by
    simp [spaceTimeForward,projIcc_of_mem _ hpi]
  rw [he]
  apply hh.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds hp.1 hp.2] with t ht
  simp [spaceTimeForward,projIcc_of_mem _ ht]

theorem spaceTimeForward_hasFDerivAt (p : ℝ × E) (hp : p.1∈Ioo a b) :
    HasFDerivAt (spaceTimeForward hab hc hL)
      (triangularEquiv (f p.1 (spaceTimeForward hab hc hL p).2)
        (fundamentalEquiv (flowSpatialCoefficient_continuous hab hc hL hD p.2)
          (flowSpatialCoefficient_bound hab hc hL hf p.2) ⟨a,le_rfl,hab⟩
            ⟨p.1,hp.1.le,hp.2.le⟩) : (ℝ × E) →L[ℝ] (ℝ × E)) p := by
  let J := flowLinearization hab hc hL hD hf p.2 p.1
  have hsp : HasFDerivAt (fun z => (spaceTimeForward hab hc hL (p.1,z)).2) J p.2 := by
    simpa [spaceTimeForward,projIcc_of_mem _ ⟨hp.1.le,hp.2.le⟩] using
      flow_hasFDerivAt_left hab hc hL hD hf p.2 ⟨p.1,hp.1.le,hp.2.le⟩
  have hg : Continuous (fun q : ℝ × E => f q.1 (spaceTimeForward hab hc hL q).2) :=
    hc.comp (continuous_fst.prodMk (spaceTimeForward_continuous hab hc hL).snd)
  have hh := LogConcaveSampling.hasFDerivAt_of_time_partial
    (f:=fun t z => (spaceTimeForward hab hc hL (t,z)).2)
    (g:=fun t z => f t (spaceTimeForward hab hc hL (t,z)).2)
    (isOpen_Ioo.prod isOpen_univ) (show p∈Ioo a b ×ˢ (univ:Set E) from ⟨hp,mem_univ _⟩)
    hg.continuousAt (fun q hq => spaceTimeForward_time_deriv hab hc hL q hq.1) hsp
  convert! hasFDerivAt_fst.prodMk hh using 1
  all_goals try with_reducible_and_instances rfl

end LogConcaveSampling.GlobalODE
namespace LogConcaveSampling.GlobalODE
open Set Function Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (hab : a≤b) {f : ℝ → E → E} (hc : Continuous (uncurry f))
    {K : ℝ≥0} (hL : ∀ t∈Icc a b,LipschitzWith K (f t))

def backwardTest (T : Icc a b) (φ : E → ℝ) (p : ℝ × E) : ℝ :=
  φ (flow hL hc ⟨a,le_rfl,hab⟩ (spaceTimeBackward hab hc hL p).2 T)

end LogConcaveSampling.GlobalODE

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_Truncated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.LinearGrowthODE
open Set Function Filter
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def truncated (f : E → E) (n : ℕ) (x : E) : E := PoincareCutoff.cutoff n x • f x

lemma truncated_smooth {f : E → E} (hf : ContDiff ℝ 1 f) (n : ℕ) :
    ContDiff ℝ 1 (truncated f n) := (PoincareCutoff.cutoff_smooth n).smul hf

lemma truncated_lipschitz {f : E → E} (hf : ContDiff ℝ 1 f) (n : ℕ) :
    ∃ L : ℝ≥0,LipschitzWith L (truncated f n) :=
  ContDiff.lipschitzWith_of_hasCompactSupport
    ((PoincareCutoff.cutoff_compact n).smul_right (f':=f)) (truncated_smooth hf n) (by norm_num)

lemma cutoff_eq_one {n : ℕ} {x : E} (hx : ‖x‖≤(n:ℝ)+1) :
    PoincareCutoff.cutoff n x=1 := by
  apply (PoincareCutoff.bump (E:=E)).one_of_mem_closedBall
  rw [Metric.mem_closedBall,dist_zero_right]
  change ‖((n:ℝ)+1)⁻¹ • x‖≤1
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact (inv_mul_le_iff₀ (by positivity : 0<(n:ℝ)+1)).mpr (by simpa using hx)

lemma truncated_eq {f : E → E} {n : ℕ} {x : E} (hx : ‖x‖≤(n:ℝ)+1) :
    truncated f n x=f x := by simp [truncated,cutoff_eq_one hx]

lemma truncated_growth {f : E → E} {K B : ℝ}
    (hg : ∀x,‖f x‖≤K*‖x‖+B) (n : ℕ) (x : E) :
    ‖truncated f n x‖≤K*‖x‖+B := by
  rw [truncated,norm_smul,Real.norm_eq_abs,abs_of_nonneg (PoincareCutoff.cutoff_nonneg n x)]
  exact (mul_le_of_le_one_left (norm_nonneg _) (PoincareCutoff.cutoff_le_one n x)).trans (hg x)

theorem exists_curve {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b) (x : E) :
    ∃α : ℝ → E,Continuous α ∧ α a=x ∧
      (∀t∈Icc a b,HasDerivWithinAt α (f (α t)) (Icc a b) t) ∧
      ∀t∈Icc a b,‖α t‖≤gronwallBound ‖x‖ K B (t-a) := by
  obtain ⟨n,hn⟩ := exists_nat_gt (gronwallBound ‖x‖ K B (b-a))
  obtain ⟨L,hL⟩ := truncated_lipschitz hf n
  have hc : Continuous (uncurry (fun (_ : ℝ) => truncated f n)) :=
    (truncated_smooth hf n).continuous.comp continuous_snd
  obtain ⟨α,hα,hα0,hαd⟩ := GlobalODE.exists_curve (f:=fun _ => truncated f n)
    (⟨a,le_rfl,hab⟩ : Icc a b) hc (fun _ _ => hL) x
  have hb : ∀t∈Icc a b,‖α t‖≤gronwallBound ‖x‖ K B (t-a) :=
    norm_le_gronwallBound_of_norm_deriv_right_le hα.continuousOn
      (GlobalODE.right_deriv hαd) (by rw [hα0])
      (fun t _ => truncated_growth hg n (α t))
  have he (t : ℝ) (ht : t∈Icc a b) : truncated f n (α t)=f (α t) := by
    apply truncated_eq
    exact (hb t ht).trans ((gronwallBound_mono (norm_nonneg x) hB hK
      (sub_le_sub_right ht.2 a)).trans (by linarith))
  exact ⟨α,hα,hα0,fun t ht => (he t ht) ▸ hαd t ht,hb⟩

end LogConcaveSampling.LinearGrowthODE

end

end

section

noncomputable section
namespace LogConcaveSampling.LinearGrowthODE
open Set Function Filter Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E]

def flow {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b) (x : E) : ℝ → E :=
  (exists_curve hf hK hB hg hab x).choose
end LogConcaveSampling.LinearGrowthODE

end

end

section

noncomputable section
namespace LogConcaveSampling.LinearGrowthODE
open Set Function Filter Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma truncated_continuous {f : E → E} (hf : ContDiff ℝ 1 f) (n : ℕ) :
    Continuous (uncurry (fun (_ : ℝ) => truncated f n)) :=
  (truncated_smooth hf n).continuous.comp continuous_snd

end LogConcaveSampling.LinearGrowthODE

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_Directional
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
open scoped RealInnerProductSpace
open MeasureTheory

lemma directional_smooth {d : ℕ} {f : Point d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : Point d) :
    ContDiff ℝ (⊤ : ℕ∞) (directional v f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma directional_directional {d : ℕ} {f : Point d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (u v x : Point d) :
    directional u (directional v f) x=(fderiv ℝ (fderiv ℝ f) x u) v := by
  have hdf : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hf.fderiv_right (by simp)
  unfold directional
  rw [fderiv_clm_apply (hdf.differentiable (by norm_num) x) (differentiableAt_const _)]
  simp

lemma directional_commute {d : ℕ} {f : Point d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (u v : Point d) :
    directional u (directional v f)=directional v (directional u f) := by
  funext x
  rw [directional_directional hf,directional_directional hf]
  exact ((hf.contDiffAt (x:=x)).isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (show (2:ℕ∞)≤⊤ from le_top))).eq u v

lemma directional_gradient {d : ℕ} (H : Point d → ℝ) (v x : Point d) :
    directional v H x=inner ℝ (gradient H x) v := by
  rw [directional,←toDual_gradient,InnerProductSpace.toDual_apply_apply]

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ConditionalPositionMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical BigOperators NNReal RealInnerProductSpace

lemma conditionalMeanScalar_joint_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2<1) {h : Point d → ℝ} (hc : Continuous h)
    (hg : Appell.HasGrowth h) (p : ℝ × Point d) (hp : p.1^2<1) :
    ContDiffAt ℝ (⊤:ℕ∞) (fun q : ℝ × Point d => conditionalMeanScalar F x r q.1 h q.2) p := by
  obtain ⟨m,hm,C,ht⟩ := hF.hasGaussianLowerTail x hr hl
  have hp' : 0 < m +(conditionalParameter p).2 := by dsimp [conditionalParameter]; positivity
  have hh := (contDiffAt_quadraticExpectation (hF.continuous_potential x r)
    hc ht hg (conditionalParameter p) hp').comp p (conditionalParameter_smooth hp)
  apply hh.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt (continuous_fst.pow 2) continuous_const).mem_nhds hp] with q hq
  exact conditional_integral_quadratic hF x hr hl hq q.2 h

def conditionalPositionMoment {d : ℕ} {ι : Type*} [DecidableEq ι]
    (F : Point d → ℝ) (x : Point d) (r : ℝ) (v : ι → Point d) (s : Finset ι)
    (p : ℝ × Point d) : ℝ :=
  conditionalMeanScalar F x r p.1 (fun z => ∏i∈s,inner ℝ (v i) z) p.2

def conditionalMixedMoment {d : ℕ} {ι : Type*} [DecidableEq ι]
    (F : Point d → ℝ) (x : Point d) (r : ℝ) (u : Point d)
    (v : ι → Point d) (s : Finset ι) (p : ℝ × Point d) : ℝ :=
  conditionalMeanScalar F x r p.1
    (fun z => (∏i∈s,inner ℝ (v i) z)*inner ℝ u (primitiveField F x r z)) p.2

lemma conditionalPositionMoment_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2<1) {ι : Type*} [DecidableEq ι]
    (v : ι → Point d) (s : Finset ι) (p : ℝ × Point d) (hp : p.1^2<1) :
    ContDiffAt ℝ (⊤:ℕ∞) (conditionalPositionMoment F x r v s) p :=
  conditionalMeanScalar_joint_smooth hF x hr hl
    (continuous_finsetProd _ (fun _ _ => continuous_const.inner continuous_id))
    (Appell.HasGrowth.prod s (fun i _ => Appell.HasGrowth.linear (innerSL ℝ (v i)))) p hp

lemma conditionalMixedMoment_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2<1) {ι : Type*} [DecidableEq ι]
    (u : Point d) (v : ι → Point d) (s : Finset ι) (p : ℝ × Point d) (hp : p.1^2<1) :
    ContDiffAt ℝ (⊤:ℕ∞) (conditionalMixedMoment F x r u v s) p :=
  conditionalMeanScalar_joint_smooth hF x hr hl
    ((continuous_finsetProd _ (fun _ _ => continuous_const.inner continuous_id)).mul
      (continuous_const.inner (primitiveField_contDiff hF x r).continuous))
    ((Appell.HasGrowth.prod s (fun i _ => Appell.HasGrowth.linear (innerSL ℝ (v i)))).mul
      (primitiveField_inner_growth hF x u hr)) p hp

end LogConcaveSampling

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

lemma conditionalFieldMean_jet_U {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (u y : Point d) {ι : Type*} (v : ι → Point d) (l : List ι) :
    JetCalculus.jet v l
      (conditionalMeanScalar F x r ρ (fun z => inner ℝ u (primitiveField F x r z))) y=
      ρ^l.length*conditionalU F x r ρ y u ((lam:ℝ)*r) v l := by
  rw [conditionalFieldMean_jet hF x hr hlam hl hρ0 hρ1 u y v l]
  simp only [conditionalU,div_pow]
  ring

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
open MeasureTheory
open scoped Classical NNReal RealInnerProductSpace

lemma quadraticTilt_derivative_apply {d : ℕ} {H h : Point d → ℝ}
    (hH : Continuous H) (hh : Continuous h) {m C : ℝ}
    (ht : ∀z,m*‖z‖^2≤H z+C) (hg : HasPolynomialGrowth h)
    (p : Point d × ℝ) (hp : 0 < m + p.2) (v : Point d × ℝ) :
    quadraticTilt H (quadraticDerivative h) p v=
      quadraticTilt H (fun z => quadraticLinear z v*h z) p := by
  unfold quadraticTilt
  rw [ContinuousLinearMap.integral_apply (integrable_quadraticTilt hH
    (continuous_quadraticDerivative hh) ht (growth_quadraticDerivative hg) p hp)]
  rfl

theorem fderiv_quadraticExpectation {d : ℕ} {H h : Point d → ℝ}
    (hH : Continuous H) (hh : Continuous h) {m C : ℝ}
    (ht : ∀z,m*‖z‖^2≤H z+C) (hg : HasPolynomialGrowth h)
    (p : Point d × ℝ) (hp : 0 < m + p.2) (v : Point d × ℝ) :
    fderiv ℝ (quadraticExpectation H h) p v=
      quadraticExpectation H (fun z => quadraticLinear z v*h z) p-
      quadraticExpectation H (fun z => quadraticLinear z v) p*quadraticExpectation H h p := by
  have h1 := hasFDerivAt_quadraticTilt hH continuous_const ht (growth_const (1:ℝ)) p hp
  have hh' := hasFDerivAt_quadraticTilt hH hh ht hg p hp
  have hZ := (quadratic_partition_pos hH ht p hp).ne'
  have hq := ((hasDerivAt_inv hZ).comp_hasFDerivAt p h1).mul hh'
  change HasFDerivAt (quadraticExpectation H h) _ p at hq
  rw [hq.fderiv]
  simp only [add_apply,smul_apply,Function.comp_apply,
    smul_eq_mul,quadraticTilt_derivative_apply hH hh ht hg p hp,
    quadraticTilt_derivative_apply hH continuous_const ht (growth_const (1:ℝ)) p hp,mul_one,
    quadraticExpectation]
  ring

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical NNReal RealInnerProductSpace

lemma hasDerivAt_conditionalParameter_time {d : ℕ} (y : Point d) {ρ : ℝ} (hρ : ρ^2<1) :
    HasDerivAt (fun t => conditionalParameter (t,y))
      (((1+ρ^2)/(1-ρ^2)^2) • y,ρ/(1-ρ^2)^2) ρ := by
  have ha : 1-ρ^2≠0 := by linarith
  have hi := hasDerivAt_id ρ
  have hd := (hasDerivAt_const ρ (1:ℝ)).sub (hi.pow 2)
  have hA := (hi.div hd ha).smul_const y
  have hB := (hi.pow 2).div (hd.const_mul 2) (mul_ne_zero (by norm_num) ha)
  convert hA.prodMk hB using 1
  · rfl
  · apply Prod.ext
    · dsimp
      congr 1
      field_simp
      ring
    · dsimp
      field_simp
      ring

theorem deriv_conditional_integral {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2<1) (hρ : ρ^2<1) (y : Point d)
    {h : Point d → ℝ} (hh : Continuous h) (hg : HasPolynomialGrowth h) :
    deriv (fun t => ∫z,h z ∂gibbs (conditionalPotential F x r t y)) ρ=
      (∫z,(((1+ρ^2)/(1-ρ^2)^2)*inner ℝ y z-(ρ/(1-ρ^2)^2)*‖z‖^2)*h z
        ∂gibbs (conditionalPotential F x r ρ y))-
      (∫z,((1+ρ^2)/(1-ρ^2)^2)*inner ℝ y z-(ρ/(1-ρ^2)^2)*‖z‖^2
        ∂gibbs (conditionalPotential F x r ρ y))*(∫z,h z ∂gibbs (conditionalPotential F x r ρ y)) := by
  let H := primitivePotential F x r
  let p := conditionalParameter (ρ,y)
  let q := (((1+ρ^2)/(1-ρ^2)^2) • y,ρ/(1-ρ^2)^2)
  obtain ⟨m,hm,C,ht⟩ := hF.hasGaussianLowerTail x hr hl
  have hH : Continuous H := hF.continuous_potential x r
  have hp : 0 < m+p.2 := by dsimp [p,conditionalParameter]; positivity
  have hqe := (contDiffAt_quadraticExpectation hH hh ht hg p hp).differentiableAt (by simp)
  have he : (fun t => ∫z,h z ∂gibbs (conditionalPotential F x r t y))=ᶠ[nhds ρ]
      (fun t => quadraticExpectation H h (conditionalParameter (t,y))) := by
    have hb : ∀ᶠt in nhds ρ,t^2<1 := (isOpen_lt (continuous_id.pow 2) continuous_const).mem_nhds hρ
    filter_upwards [hb] with t ht
    exact conditional_integral_quadratic hF x hr hl ht y h
  have hd := hqe.hasFDerivAt.comp_hasDerivAt ρ (hasDerivAt_conditionalParameter_time y hρ)
  have hd' := hd.congr_of_eventuallyEq he
  rw [hd'.deriv]
  change fderiv ℝ (quadraticExpectation H h) p q=_
  rw [fderiv_quadraticExpectation hH hh ht hg p hp q]
  have hq (z : Point d) : quadraticLinear z q=
      ((1+ρ^2)/(1-ρ^2)^2)*inner ℝ y z-(ρ/(1-ρ^2)^2)*‖z‖^2 := by
    simp only [quadraticLinear_apply,q,inner_smul_left,starRingEnd_apply,star_trivial]
  simp_rw [hq]
  rw [←conditional_integral_quadratic hF x hr hl hρ y,
    ←conditional_integral_quadratic hF x hr hl hρ y,
    ←conditional_integral_quadratic hF x hr hl hρ y]

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped Classical NNReal RealInnerProductSpace

theorem conditionalIntegral_dir_cov {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (v y : Point d) {f : Point d → ℝ}
    (hfc : Continuous f) (hfg : Appell.HasGrowth f) :
    JetCalculus.dir v
      (conditionalMeanScalar F x r ρ f) y=
      (ρ/(1-ρ^2))*cov[(fun z => inner ℝ v z),
        f;gibbs (conditionalPotential F x r ρ y)] := by
  let μ := gibbs (conditionalPotential F x r ρ y)
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  have hm := conditionalLaw_hasExpMoments hF x hr hl hρ0 hρ1 y
  have hmean := conditionalMeanScalar_smooth hF x hr hl hρ0 hρ1 hfc hfg
  have hs := Appell.smooth_normalizedLaplace hm hfc hfg
  have he : (fun h => conditionalMeanScalar F x r ρ f (h+y))=
      fun h => Appell.normalizedLaplace μ f ((ρ/(1-ρ^2)) • h) := by
    funext h
    simpa only [add_comm h y] using conditionalMeanScalar_shift hF x hr hl hρ0 hρ1 f y h
  have htr := congrFun (JetCalculus.dir_comp_affine
    (hmean.differentiable (by simp)) (ContinuousLinearMap.id ℝ (Point d)) y v) 0
  simp only [ContinuousLinearMap.id_apply,zero_add] at htr
  rw [← htr,he]
  let B : Point d →L[ℝ] Point d := (ρ/(1-ρ^2)) • ContinuousLinearMap.id ℝ (Point d)
  have heB : (fun h => Appell.normalizedLaplace μ f ((ρ/(1-ρ^2)) • h))=
      fun h => Appell.normalizedLaplace μ f (B h+0) := by
    funext h; simp [B]
  rw [heB]
  rw [JetCalculus.dir_comp_affine (hs.differentiable (by simp))]
  simp only [map_zero,zero_add]
  change JetCalculus.dir ((ρ/(1-ρ^2)) • v) (Appell.normalizedLaplace μ f) 0=_
  rw [JetCalculus.dir_smul]
  change (ρ/(1-ρ^2))*JetCalculus.dir v (Appell.normalizedLaplace μ f) 0=_
  rw [Appell.dir_normalizedLaplace_zero hm hfc hfg]

theorem conditionalU_one_cov {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (u v y : Point d) :
    conditionalU F x r ρ y u ((lam:ℝ)*r) (fun _ : Unit => v) [()]=
      (1/(1-ρ^2))*cov[(fun z => inner ℝ v z),
        (fun z => inner ℝ u (primitiveField F x r z));gibbs (conditionalPotential F x r ρ y)] := by
  obtain ⟨hp,hm,hP⟩ := jointConditionalLaw_properties hF x hr hlam hl hρ0 hρ1 y
  let := hp
  have hL : (lam:ℝ)*r≠0 := by positivity
  simp only [conditionalU,List.length_singleton,pow_one,JetCalculus.jet]
  rw [Appell.dir_log_laplace hm]
  have hg : Appell.HasGrowth (fun z : JointPoint d => inner ℝ (jointField d u) z) :=
    Appell.HasGrowth.linear (innerSL ℝ (jointField d u))
  rw [Appell.dir_normalizedLaplace_zero hm (by fun_prop) hg]
  unfold jointConditionalLaw
  rw [covariance_map_fun (by fun_prop) (by fun_prop)
    ((jointImage_contDiff (primitiveField_contDiff hF x r) _).continuous.aemeasurable)]
  simp only [jointPosition_inner,jointField_inner,covariance_const_mul_right]
  field_simp

lemma conditional_observable_memLp {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d)
    {f : Point d → ℝ} (hf : Continuous f) (hg : Appell.HasGrowth f) :
    MemLp f 2 (gibbs (conditionalPotential F x r ρ y)) := by
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  exact hg.memLp hf.aestronglyMeasurable
    (conditionalLaw_hasExpMoments hF x hr hl hρ0 hρ1 y).hasMoments

lemma conditional_covariance_eq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {g h : Point d → ℝ} (gc : Continuous g) (gg : Appell.HasGrowth g)
    (hc : Continuous h) (hg : Appell.HasGrowth h) :
    (fun y => cov[g,h;gibbs (conditionalPotential F x r ρ y)])=
      fun y => conditionalMeanScalar F x r ρ (fun z => g z*h z) y-
        conditionalMeanScalar F x r ρ g y*conditionalMeanScalar F x r ρ h y := by
  funext y
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  exact covariance_eq_sub (conditional_observable_memLp hF x hr hl hρ0 hρ1 y gc gg)
    (conditional_observable_memLp hF x hr hl hρ0 hρ1 y hc hg)

lemma conditional_covariance_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {g h : Point d → ℝ} (gc : Continuous g) (gg : Appell.HasGrowth g)
    (hc : Continuous h) (hg : Appell.HasGrowth h) :
    ContDiff ℝ (⊤:ℕ∞) (fun y => cov[g,h;gibbs (conditionalPotential F x r ρ y)]) := by
  rw [conditional_covariance_eq hF x hr hl hρ0 hρ1 gc gg hc hg]
  exact (conditionalMeanScalar_smooth hF x hr hl hρ0 hρ1 (gc.mul hc) (gg.mul hg)).sub
    ((conditionalMeanScalar_smooth hF x hr hl hρ0 hρ1 gc gg).mul
      (conditionalMeanScalar_smooth hF x hr hl hρ0 hρ1 hc hg))

lemma directional_conditional_covariance {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {g h : Point d → ℝ} (gc : Continuous g) (gg : Appell.HasGrowth g)
    (hc : Continuous h) (hg : Appell.HasGrowth h) (v y : Point d) :
    directional v (fun y => cov[g,h;gibbs (conditionalPotential F x r ρ y)]) y=
      (ρ/(1-ρ^2))*(cov[(fun z => inner ℝ v z),(fun z => g z*h z);
          gibbs (conditionalPotential F x r ρ y)]-
        cov[(fun z => inner ℝ v z),g;gibbs (conditionalPotential F x r ρ y)]*
          conditionalMeanScalar F x r ρ h y-
        conditionalMeanScalar F x r ρ g y*
          cov[(fun z => inner ℝ v z),h;gibbs (conditionalPotential F x r ρ y)]) := by
  rw [conditional_covariance_eq hF x hr hl hρ0 hρ1 gc gg hc hg]
  have hgd := (conditionalMeanScalar_smooth hF x hr hl hρ0 hρ1 gc gg).differentiable (by simp)
  have hhd := (conditionalMeanScalar_smooth hF x hr hl hρ0 hρ1 hc hg).differentiable (by simp)
  have hpd := (conditionalMeanScalar_smooth hF x hr hl hρ0 hρ1 (gc.mul hc) (gg.mul hg)).differentiable (by simp)
  simp only [directional]
  change (fderiv ℝ (conditionalMeanScalar F x r ρ (g*h)-
    conditionalMeanScalar F x r ρ g*conditionalMeanScalar F x r ρ h) y) v=_
  rw [((hpd y).hasFDerivAt.sub ((hgd y).hasFDerivAt.mul (hhd y).hasFDerivAt)).fderiv]
  simp only [sub_apply,add_apply,smul_apply,smul_eq_mul]
  change JetCalculus.dir v _ y-(conditionalMeanScalar F x r ρ g y*JetCalculus.dir v _ y+
    conditionalMeanScalar F x r ρ h y*JetCalculus.dir v _ y)=_
  rw [conditionalIntegral_dir_cov hF x hr hl hρ0 hρ1 v y (gc.mul hc) (gg.mul hg),
    conditionalIntegral_dir_cov hF x hr hl hρ0 hρ1 v y hc hg,
    conditionalIntegral_dir_cov hF x hr hl hρ0 hρ1 v y gc gg]
  change (ρ/(1-ρ^2))*cov[(fun z => inner ℝ v z),g*h;gibbs (conditionalPotential F x r ρ y)]-
    (conditionalMeanScalar F x r ρ g y*((ρ/(1-ρ^2))*cov[(fun z => inner ℝ v z),h;gibbs (conditionalPotential F x r ρ y)])+
    conditionalMeanScalar F x r ρ h y*((ρ/(1-ρ^2))*cov[(fun z => inner ℝ v z),g;gibbs (conditionalPotential F x r ρ y)]))=
    (ρ/(1-ρ^2))*(cov[(fun z => inner ℝ v z),g*h;gibbs (conditionalPotential F x r ρ y)]-
    cov[(fun z => inner ℝ v z),g;gibbs (conditionalPotential F x r ρ y)]*conditionalMeanScalar F x r ρ h y-
    conditionalMeanScalar F x r ρ g y*cov[(fun z => inner ℝ v z),h;gibbs (conditionalPotential F x r ρ y)])
  ring

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators RealInnerProductSpace

lemma covariance_inner_synthesis {d : ℕ} {μ : Measure (Point d)} [IsProbabilityMeasure μ]
    (hm : Appell.HasExpMoments μ) {f : Point d → ℝ} (hf : MemLp f 2 μ) (v : Point d) :
    (∑i : Fin d,inner ℝ v ((EuclideanSpace.basisFun (Fin d) ℝ) i)*
      cov[(fun z => inner ℝ ((EuclideanSpace.basisFun (Fin d) ℝ) i) z),f;μ])=
      cov[(fun z => inner ℝ v z),f;μ] := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hi (i : Fin d) : MemLp (fun z => inner ℝ (b i) z) 2 μ :=
    (Appell.HasGrowth.linear (innerSL ℝ (b i))).memLp (by fun_prop) hm.hasMoments
  have hh := covariance_fun_sum_left (fun i => (hi i).const_mul (inner ℝ v (b i))) hf
  simp only [covariance_const_mul_left] at hh
  simpa only [b.sum_inner_mul_inner v] using hh.symm

lemma covariance_norm_sq_sum {d : ℕ} {μ : Measure (Point d)} [IsProbabilityMeasure μ]
    (hm : Appell.HasExpMoments μ) {f : Point d → ℝ} (hf : MemLp f 2 μ) :
    (∑i : Fin d,cov[(fun z => (inner ℝ ((EuclideanSpace.basisFun (Fin d) ℝ) i) z)^2),f;μ])=
      cov[(fun z => ‖z‖^2),f;μ] := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hi (i : Fin d) : MemLp (fun z => (inner ℝ (b i) z)^2) 2 μ :=
    ((Appell.HasGrowth.linear (innerSL ℝ (b i))).pow 2).memLp (by fun_prop) hm.hasMoments
  have hh := covariance_fun_sum_left hi hf
  simpa only [b.sum_sq_inner_right] using hh.symm

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

def materialScalar {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ)
    (A : ℝ → Point d → ℝ) (ρ : ℝ) (y : Point d) : ℝ :=
  deriv (fun t => A t y) ρ-r*directional (conditionalFieldMean F x r ρ y) (A ρ) y

lemma deriv_conditional_integral_cov {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d)
    {f : Point d → ℝ} (fc : Continuous f) (fg : Appell.HasGrowth f) :
    deriv (fun t => conditionalMeanScalar F x r t f y) ρ=
      ((1+ρ^2)/(1-ρ^2)^2)*cov[(fun z => inner ℝ y z),f;gibbs (conditionalPotential F x r ρ y)]-
      (ρ/(1-ρ^2)^2)*cov[(fun z => ‖z‖^2),f;gibbs (conditionalPotential F x r ρ y)] := by
  let μ := gibbs (conditionalPotential F x r ρ y)
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  have hm := (conditionalLaw_hasExpMoments hF x hr hl hρ0 hρ1 y).hasMoments
  have hg : Appell.HasGrowth (fun z : Point d => inner ℝ y z) := Appell.HasGrowth.linear (innerSL ℝ y)
  have hn : Appell.HasGrowth (fun z : Point d => ‖z‖^2) := by
    exact ⟨1,by norm_num,2,fun z => by simp only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖z‖)]; linarith⟩
  have gm : MemLp (fun z : Point d => inner ℝ y z) 2 μ := hg.memLp (by fun_prop) hm
  have nm : MemLp (fun z : Point d => ‖z‖^2) 2 μ := hn.memLp (by fun_prop) hm
  have fm : MemLp f 2 μ := fg.memLp fc.aestronglyMeasurable hm
  let A := (1+ρ^2)/(1-ρ^2)^2
  let B := ρ/(1-ρ^2)^2
  have qm : MemLp (fun z : Point d => A*inner ℝ y z-B*‖z‖^2) 2 μ :=
    (gm.const_mul A).sub (nm.const_mul B)
  change deriv (fun t => ∫z,f z ∂gibbs (conditionalPotential F x r t y)) ρ=_
  rw [deriv_conditional_integral hF x hr (by linarith)
    (by have := (probability_time hρ0 hρ1).1; linarith) y fc fg]
  have hq := covariance_eq_sub qm fm
  simp only [Pi.mul_apply] at hq
  rw [←hq,covariance_fun_sub_left (gm.const_mul A) (nm.const_mul B) fm]
  simp only [covariance_const_mul_left,A,B]
  rfl

lemma directional_position_covariance {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (v y : Point d)
    {f : Point d → ℝ} (fc : Continuous f) (fg : Appell.HasGrowth f) :
    directional v (fun y => cov[(fun z => inner ℝ v z),f;gibbs (conditionalPotential F x r ρ y)]) y=
      (ρ/(1-ρ^2))*(cov[(fun z => (inner ℝ v z)^2),f;gibbs (conditionalPotential F x r ρ y)]-
        2*conditionalMeanScalar F x r ρ (fun z => inner ℝ v z) y*
          cov[(fun z => inner ℝ v z),f;gibbs (conditionalPotential F x r ρ y)]) := by
  let μ := gibbs (conditionalPotential F x r ρ y)
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  have hm := (conditionalLaw_hasExpMoments hF x hr hl hρ0 hρ1 y).hasMoments
  have hg : Appell.HasGrowth (fun z : Point d => inner ℝ v z) := Appell.HasGrowth.linear (innerSL ℝ v)
  have gm : MemLp (fun z : Point d => inner ℝ v z) 2 μ := hg.memLp (by fun_prop) hm
  have fm : MemLp f 2 μ := fg.memLp fc.aestronglyMeasurable hm
  rw [directional_conditional_covariance hF x hr hl hρ0 hρ1 (by fun_prop) hg fc fg]
  exact congrArg (fun z => (ρ/(1-ρ^2))*z) (covariance_third_diagonal gm fm ((hg.pow 2).memLp (by fun_prop) hm)
    ((hg.mul fg).memLp ((show Continuous (fun z => inner ℝ v z) by fun_prop).mul fc).aestronglyMeasurable hm))

theorem material_conditional_expectation {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {f : Point d → ℝ} (fc : Continuous f) (fg : Appell.HasGrowth f) (y : Point d) :
    materialScalar F x r (fun t => conditionalMeanScalar F x r t f) ρ y=
      tensorAdjoint (interpolationPotential F x r ρ) (EuclideanSpace.basisFun (Fin d) ℝ)
        (fun i y => (1/(1-ρ^2))*cov[(fun z => inner ℝ ((EuclideanSpace.basisFun (Fin d) ℝ) i) z),f;
          gibbs (conditionalPotential F x r ρ y)]) y := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  let μ := gibbs (conditionalPotential F x r ρ y)
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  have hm := conditionalLaw_hasExpMoments hF x hr hl hρ0 hρ1 y
  have fm : MemLp f 2 μ := fg.memLp fc.aestronglyMeasurable hm.hasMoments
  let a := 1-ρ^2
  have ha : a≠0 := (probability_time hρ0 hρ1).1.ne'
  let M := conditionalFieldMean F x r ρ y
  let C (v : Point d) := cov[(fun z => inner ℝ v z),f;μ]
  let S (i : Fin d) := cov[(fun z => (inner ℝ (b i) z)^2),f;μ]
  let m (i : Fin d) := conditionalMeanScalar F x r ρ (fun z => inner ℝ (b i) z) y
  let w := y+(r*ρ) • M
  have hi (i : Fin d) : Appell.HasGrowth (fun z : Point d => inner ℝ (b i) z) :=
    Appell.HasGrowth.linear (innerSL ℝ (b i))
  have hD (i : Fin d) : directional (b i)
      (fun y => (1/a)*cov[(fun z => inner ℝ (b i) z),f;gibbs (conditionalPotential F x r ρ y)]) y=
      (1/a)*(ρ/a)*(S i-2*m i*C (b i)) := by
    have hdc := (conditional_covariance_smooth hF x hr hl hρ0 hρ1 (by fun_prop) (hi i) fc fg).differentiable (by simp)
    change JetCalculus.dir (b i) (fun y => (1/a)*cov[(fun z => inner ℝ (b i) z),f;gibbs (conditionalPotential F x r ρ y)]) y=_
    rw [JetCalculus.dir_const_mul hdc]
    change (1/a)*directional (b i) (fun y => cov[(fun z => inner ℝ (b i) z),f;gibbs (conditionalPotential F x r ρ y)]) y=_
    rw [directional_position_covariance hF x hr hl hρ0 hρ1 (b i) y fc fg]
    dsimp [S,m,C,μ,a]
    ring
  have hme (i : Fin d) : m i=ρ*inner ℝ y (b i)-(a*r)*inner ℝ M (b i) := by
    dsimp [m,conditionalMeanScalar]
    rw [integral_inner (conditional_identity_integrable hF x hr hl hρ0 hρ1 y) (b i),
      conditional_mean_identity hF x hr hl hρ0 hρ1 y]
    simp only [inner_sub_right,inner_smul_right]
    rw [real_inner_comm (b i) y,real_inner_comm (b i) M]
  have hsum (v : Point d) : (∑i : Fin d,inner ℝ v (b i)*C (b i))=C v :=
    covariance_inner_synthesis hm fm v
  have hmSum : (∑i : Fin d,m i*C (b i))=ρ*C y-(a*r)*C M := by
    simp only [hme,sub_mul,mul_assoc,Finset.sum_sub_distrib,←Finset.mul_sum,hsum]
  have hsSum : (∑i : Fin d,S i)=cov[(fun z => ‖z‖^2),f;μ] := covariance_norm_sq_sum hm fm
  have hwSum : (∑i : Fin d,inner ℝ w (b i)*C (b i))=C y+(r*ρ)*C M := by
    simp only [w,inner_add_left,real_inner_smul_left,add_mul,mul_assoc,
      Finset.sum_add_distrib,←Finset.mul_sum,hsum]
  rw [materialScalar,deriv_conditional_integral_cov hF x hr hl hρ0 hρ1 y fc fg]
  change _-r*JetCalculus.dir M (conditionalMeanScalar F x r ρ f) y=_
  rw [conditionalIntegral_dir_cov hF x hr hl hρ0 hρ1 M y fc fg]
  have hAdj : tensorAdjoint (interpolationPotential F x r ρ) b
      (fun i y => (1/a)*cov[(fun z => inner ℝ (b i) z),f;gibbs (conditionalPotential F x r ρ y)]) y=
      -((1/a)*(ρ/a))*cov[(fun z => ‖z‖^2),f;μ]+
        (2*(1/a)*(ρ/a))*(ρ*C y-(a*r)*C M)+(1/a)*(C y+(r*ρ)*C M) := by
    unfold tensorAdjoint adjointCoordinate
    simp only [hD,directional_gradient,interpolationPotential_gradient hF x hr hl hρ0 hρ1]
    calc
      _=(∑i : Fin d,(-((1/a)*(ρ/a))*S i+
          (2*(1/a)*(ρ/a))*(m i*C (b i))+(1/a)*(inner ℝ w (b i)*C (b i)))) := by
        apply Finset.sum_congr rfl
        intro i _
        change -((1/a)*(ρ/a)*(S i-2*m i*C (b i)))+inner ℝ w (b i)*((1/a)*C (b i))=_
        ring
      _=_ := by
        simp only [Finset.sum_add_distrib,←Finset.mul_sum,hsSum,hmSum,hwSum]
  rw [hAdj]
  change ((1+ρ^2)/a^2)*C y-(ρ/a^2)*cov[(fun z => ‖z‖^2),f;μ]-r*((ρ/a)*C M)=_
  dsimp [a]
  field_simp [show 1-ρ^2≠0 from ha]
  ring

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped Classical NNReal RealInnerProductSpace

lemma conditionalLaw_probability_sq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2 ≤ 1/2) (hρ : ρ^2<1) (y : Point d) :
    IsProbabilityMeasure (gibbs (conditionalPotential F x r ρ y)) := by
  have ha : 0<1-ρ^2 := by linarith
  have ha1 : 1-ρ^2≤1 := by nlinarith [sq_nonneg ρ]
  have hs := conditional_smallness hl ha ha1
  have hsmall : (lam:ℝ)*(r*Real.sqrt (1-ρ^2))^2 < 1 := by linarith
  have hrad : 0 ≤ r*Real.sqrt (1-ρ^2) := mul_nonneg hr (Real.sqrt_nonneg _)
  have : IsProbabilityMeasure (gibbs (primitivePotential F (x+r • (ρ • y))
      (r*Real.sqrt (1-ρ^2)))) := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential _ _)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential _ hrad hsmall))
  rw [← conditionalLaw_map hF x r ρ y ha]
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

lemma conditionalLaw_hasExpMoments_sq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2 ≤ 1/2) (hρ : ρ^2<1) (y : Point d) :
    Appell.HasExpMoments (gibbs (conditionalPotential F x r ρ y)) := by
  have ha : 0<1-ρ^2 := by linarith
  have ha1 : 1-ρ^2≤1 := by nlinarith [sq_nonneg ρ]
  have hs := conditional_smallness hl ha ha1
  have hsmall : (lam:ℝ)*(r*Real.sqrt (1-ρ^2))^2 < 1 := by linarith
  have hrad : 0 ≤ r*Real.sqrt (1-ρ^2) := mul_nonneg hr (Real.sqrt_nonneg _)
  rw [← conditionalLaw_map hF x r ρ y ha]
  apply (hF.hasExpMoments (x+r • (ρ • y)) hrad hsmall).map_lipschitz
    (K := ⟨Real.sqrt (1-ρ^2),Real.sqrt_nonneg _⟩)
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simp only [dist_eq_norm,add_sub_add_left_eq_sub,← smul_sub,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  rfl

lemma conditionalFieldMean_inner_sq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ : ρ^2<1) (u y : Point d) :
    inner ℝ u (conditionalFieldMean F x r ρ y)=
      conditionalMeanScalar F x r ρ (fun z => inner ℝ u (primitiveField F x r z)) y := by
  let := conditionalLaw_probability_sq hF x hr hl hρ y
  have hi : Integrable (primitiveField F x r) (gibbs (conditionalPotential F x r ρ y)) :=
    (Appell.HasGrowth.lipschitz (primitiveField_lipschitz hF x hr)).integrable
      (primitiveField_contDiff hF x r).continuous.aestronglyMeasurable
      (conditionalLaw_hasExpMoments_sq hF x hr hl hρ y).hasMoments
  exact (integral_inner hi u).symm

theorem material_conditionalFieldMean {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (u y : Point d) :
    materialScalar F x r (fun t y => inner ℝ u (conditionalFieldMean F x r t y)) ρ y=
      tensorAdjoint (interpolationPotential F x r ρ) (EuclideanSpace.basisFun (Fin d) ℝ)
        (fun i y => conditionalU F x r ρ y u ((lam:ℝ)*r)
          (fun _ : Unit => (EuclideanSpace.basisFun (Fin d) ℝ) i) [()]) y := by
  have hρ : ρ^2<1 := by have := (probability_time hρ0 hρ1).1; linarith
  have he : (fun t => inner ℝ u (conditionalFieldMean F x r t y))=ᶠ[nhds ρ]
      (fun t => conditionalMeanScalar F x r t (fun z => inner ℝ u (primitiveField F x r z)) y) := by
    filter_upwards [(isOpen_lt (continuous_id.pow 2) continuous_const).mem_nhds hρ] with t ht
    exact conditionalFieldMean_inner_sq hF x hr.le hl ht u y
  have hs : (fun y => inner ℝ u (conditionalFieldMean F x r ρ y))=
      conditionalMeanScalar F x r ρ (fun z => inner ℝ u (primitiveField F x r z)) :=
    funext (conditionalFieldMean_inner hF x hr.le hl hρ0 hρ1 u)
  have hu : (fun i y => conditionalU F x r ρ y u ((lam:ℝ)*r)
      (fun _ : Unit => (EuclideanSpace.basisFun (Fin d) ℝ) i) [()])=
      (fun i y => (1/(1-ρ^2))*cov[(fun z => inner ℝ ((EuclideanSpace.basisFun (Fin d) ℝ) i) z),
        (fun z => inner ℝ u (primitiveField F x r z));gibbs (conditionalPotential F x r ρ y)]) :=
    funext fun i => funext fun y => conditionalU_one_cov hF x hr hlam hl hρ0 hρ1 u _ y
  rw [hu]
  unfold materialScalar
  rw [he.deriv_eq]
  dsimp only
  rw [hs]
  exact material_conditional_expectation hF x hr.le hl hρ0 hρ1
    (continuous_const.inner (primitiveField_contDiff hF x r).continuous)
    (primitiveField_inner_growth hF x u hr.le) y

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_JointConditionalLawProperties
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
open scoped Topology Classical BigOperators NNReal RealInnerProductSpace

lemma jointConditionalLaw_properties_sq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ : ρ^2<1) (y : Point d) :
    IsProbabilityMeasure (jointConditionalLaw F x r ρ y ((lam:ℝ)*r)) ∧
      Appell.HasExpMoments (jointConditionalLaw F x r ρ y ((lam:ℝ)*r)) := by
  let L : ℝ≥0 := lam*(NNReal.mk r hr.le)
  have hL : L≠0 := mul_ne_zero hlam.ne' (by intro h; exact hr.ne' (congrArg (fun t : ℝ≥0 => (t:ℝ)) h))
  have hK := jointImage_lipschitz (primitiveField_lipschitz hF x hr.le) hL
  let := conditionalLaw_probability_sq hF x hr.le hl hρ y
  change IsProbabilityMeasure ((gibbs (conditionalPotential F x r ρ y)).map
      (jointImage (primitiveField F x r) (L:ℝ))) ∧ _
  exact ⟨Measure.isProbabilityMeasure_map hK.continuous.aemeasurable,
    (conditionalLaw_hasExpMoments_sq hF x hr.le hl hρ y).map_lipschitz hK⟩

lemma conditionalU_normalized_jet_sq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ : ρ^2<1)
    {ι : Type*} (v : ι → Point d) (l : List ι) (u y : Point d) :
    conditionalU F x r ρ y u ((lam:ℝ)*r) v l=
      ((1-ρ^2)^l.length)⁻¹*JetCalculus.jet v l
        (Appell.normalizedLaplace (gibbs (conditionalPotential F x r ρ y))
          (fun z => inner ℝ u (primitiveField F x r z))) 0 := by
  obtain ⟨hp,hJ⟩ := jointConditionalLaw_properties_sq hF x hr hlam hl hρ y
  let := hp
  let := conditionalLaw_probability_sq hF x hr.le hl hρ y
  have hc : Continuous (fun z => inner ℝ u (primitiveField F x r z)) :=
    continuous_const.inner (primitiveField_contDiff hF x r).continuous
  have hg := primitiveField_inner_growth hF x u hr.le
  have hC := Appell.smooth_normalizedLaplace (conditionalLaw_hasExpMoments_sq hF x hr.le hl hρ y) hc hg
  have hJC := Appell.smooth_normalizedLaplace hJ
    (show Continuous (fun z : JointPoint d => inner ℝ (jointField d u) z) by fun_prop)
    (Appell.HasGrowth.linear (innerSL ℝ (jointField d u)))
  have hh := congrFun (JetCalculus.jet_comp_affine hJC (jointPosition d) 0 v l) 0
  simp only [add_zero,map_zero] at hh
  have hf : (fun z => Appell.normalizedLaplace (jointConditionalLaw F x r ρ y ((lam:ℝ)*r))
      (fun z => inner ℝ (jointField d u) z) (jointPosition d z))=fun z =>
      ((lam:ℝ)*r)⁻¹*Appell.normalizedLaplace (gibbs (conditionalPotential F x r ρ y))
        (fun z => inner ℝ u (primitiveField F x r z)) z := by
    funext z
    exact joint_normalizedLaplace (primitiveField_contDiff hF x r).continuous _ _ z
  rw [hf,JetCalculus.jet_const_mul hC] at hh
  unfold conditionalU
  rw [Appell.dir_log_laplace hJ,←hh]
  dsimp only at hh
  have hL : (lam:ℝ)*r≠0 := by positivity
  field_simp [hL]

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_Mdir
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
variable {ι κ : Type*} [Fintype ι]

lemma jet_dir {f : E → ℝ} (hf : ContDiff ℝ (⊤:ℕ∞) f)
    (v : κ → E) (l : List κ) (w : E) : jet v l (dir w f)=dir w (jet v l f) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [jet,ih]
    exact dir_dir (smooth_jet hf v l) (v i) w

def mdir (w : E) (b : ι → E) (r : ℝ) (M : ι → E → ℝ) (f : E → ℝ) : E → ℝ :=
  fun p => dir w f p-r*∑ i, M i p*dir (b i) f p

theorem mdir_jet [DecidableEq κ] (w : E) (b : ι → E) (r : ℝ)
    {M : ι → E → ℝ} (hM : ∀i,ContDiff ℝ (⊤:ℕ∞) (M i))
    {f : E → ℝ} (hf : ContDiff ℝ (⊤:ℕ∞) f)
    (v : κ → E) (l : List κ) (hl : l.Nodup) :
    mdir w b r M (jet v l f)=fun p => jet v l (mdir w b r M f) p+
      r*∑s∈l.toFinset.powerset.erase ∅,∑i,
        jet v (l.filter (fun j => j∈s)) (M i) p*
          dir (b i) (jet v (l.filter (fun j => j∉s)) f) p := by
  have hm : ContDiff ℝ (⊤:ℕ∞) (fun p => ∑i,M i p*dir (b i) f p) :=
    ContDiff.sum fun i _ => (hM i).mul (smooth_dir hf _)
  have he : jet v l (mdir w b r M f)=fun p => dir w (jet v l f) p-
      r*∑i,∑s∈l.toFinset.powerset,
        jet v (l.filter (fun j => j∈s)) (M i) p*
          dir (b i) (jet v (l.filter (fun j => j∉s)) f) p := by
    unfold mdir
    rw [jet_sub (smooth_dir hf w) (contDiff_const.mul hm),jet_const_mul hm,
      jet_dir hf,jet_sum Finset.univ (fun i _ => (hM i).mul (smooth_dir hf _))]
    simp_rw [jet_mul (hM _) (smooth_dir hf _) v l hl,jet_dir hf]
  rw [he]
  funext p
  dsimp only
  rw [Finset.sum_comm]
  rw [←Finset.add_sum_erase _ _ (by simp : (∅:Finset κ)∈l.toFinset.powerset)]
  simp only [Finset.notMem_empty,decide_false,List.filter_false,not_false_eq_true,decide_true,
    List.filter_true,jet]
  unfold mdir
  ring

end LogConcaveSampling.JetCalculus

end

end

section

noncomputable section
namespace LogConcaveSampling.JetCalculus
open scoped Classical BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

def cadj (v : E) (s f : E → ℝ) : E → ℝ := fun p => -dir v f p+s p*f p

def gadj (b : ι → E) (s V : ι → E → ℝ) : E → ℝ := fun p => ∑i,cadj (b i) (s i) (V i) p

lemma smooth_cadj (v : E) {s f : E → ℝ} (hs : ContDiff ℝ (⊤:ℕ∞) s)
    (hf : ContDiff ℝ (⊤:ℕ∞) f) : ContDiff ℝ (⊤:ℕ∞) (cadj v s f) :=
  (smooth_dir hf v).neg.add (hs.mul hf)

end LogConcaveSampling.JetCalculus

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_AllSplitBound
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
open scoped Classical

universe u

def AllSplitBound {S : Type u} [Fintype S] {d : ℕ}
    (T : (S → Fin d) → ℝ) (M : ℝ) : Prop :=
  ∀(I O : Type u) [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O] [Nonempty I] [Nonempty O]
    (e : S ≃ I ⊕ O),
    Bound (fun (o : O → Fin d) (i : I → Fin d) => T (fun s => Sum.elim i o (e s))) (M^2)
end LogConcaveSampling.TensorEnergy

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_AdjointCoordinateContinuous
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
open scoped RealInnerProductSpace NNReal

lemma jet_directional {d : ℕ} {ι : Type*} {f : Point d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : ι → Point d) (l : List ι) (u : Point d) :
    JetCalculus.jet v l (directional u f)=directional u (JetCalculus.jet v l f) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [JetCalculus.jet,ih]
    change directional (v i) (directional u (JetCalculus.jet v l f))=
      directional u (directional (v i) (JetCalculus.jet v l f))
    exact directional_commute (JetCalculus.smooth_jet hf v l) (v i) u

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_PolySmooth
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
open scoped RealInnerProductSpace NNReal

structure PolySmooth {d : ℕ} (f : Point d → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) f
  growth : ∀l : List (Point d),HasPolynomialGrowth (JetCalculus.jet id l f)

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_DirectionalBasisSum
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
open scoped Classical BigOperators RealInnerProductSpace

lemma directional_basis_sum {d : ℕ} (v : Point d) (f : Point d → ℝ) :
    directional v f=fun x => ∑i : Fin d,
      (EuclideanSpace.basisFun (Fin d) ℝ).repr v i *
        directional (EuclideanSpace.basisFun (Fin d) ℝ i) f x := by
  funext x
  unfold directional
  conv_lhs => arg 2; rw [←(EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v]
  simp only [map_sum,map_smul,smul_eq_mul]

lemma basis_jet_growth_all {d : ℕ} {f : Point d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ∀l : List (Fin d),HasPolynomialGrowth
      (JetCalculus.jet (EuclideanSpace.basisFun (Fin d) ℝ) l f))
    (l : List (Point d)) : HasPolynomialGrowth (JetCalculus.jet id l f) := by
  induction l generalizing f with
  | nil => exact hg []
  | cons v l ih =>
    change HasPolynomialGrowth (directional v (JetCalculus.jet id l f))
    rw [←jet_directional hf,directional_basis_sum,
      JetCalculus.jet_sum Finset.univ (fun i _ =>
        contDiff_const.mul (directional_smooth hf _))]
    apply Appell.HasGrowth.sum
    intro i _
    rw [JetCalculus.jet_const_mul (directional_smooth hf _)]
    apply Appell.HasGrowth.mul (growth_const _)
    apply ih (directional_smooth hf _)
    intro k
    have hh := hg (k++[i])
    have he : JetCalculus.jet (EuclideanSpace.basisFun (Fin d) ℝ) [i] f=
        directional (EuclideanSpace.basisFun (Fin d) ℝ i) f := rfl
    rw [JetCalculus.jet_append,he] at hh
    exact hh

lemma PolySmooth.of_basis_growth {d : ℕ} {f : Point d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ∀l : List (Fin d),HasPolynomialGrowth
      (JetCalculus.jet (EuclideanSpace.basisFun (Fin d) ℝ) l f)) : PolySmooth f :=
  ⟨hf,basis_jet_growth_all hf hg⟩

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
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace NNReal

namespace JetCalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma dir_right_slice_at {A : ℝ × E → ℝ} {t : ℝ} {y : E}
    (hA : DifferentiableAt ℝ A (t,y)) (v : E) :
    dir v (fun z => A (t,z)) y=dir (0,v) A (t,y) := by
  have hh := hA.hasFDerivAt.comp y ((hasFDerivAt_const t y).prodMk (hasFDerivAt_id y))
  unfold dir
  change (fderiv ℝ (A ∘ Prod.mk t) y) v=_
  rw [hh.fderiv]
  simp

lemma dir_left_slice_at {A : ℝ × E → ℝ} {t : ℝ} {y : E}
    (hA : DifferentiableAt ℝ A (t,y)) :
    deriv (fun s => A (s,y)) t=dir (1,0) A (t,y) := by
  have hh := hA.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
  exact hh.deriv

end JetCalculus

lemma joint_mdir_eq_material {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ)
    {A : ℝ × Point d → ℝ} {ρ : ℝ} {y : Point d}
    (hA : DifferentiableAt ℝ A (ρ,y)) :
    JetCalculus.mdir (1,0) (fun i => (0,EuclideanSpace.basisFun (Fin d) ℝ i)) r
      (fun i p => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)
        (conditionalFieldMean F x r p.1 p.2)) A (ρ,y)=
      materialScalar F x r (fun t y => A (t,y)) ρ y := by
  unfold JetCalculus.mdir materialScalar
  rw [JetCalculus.dir_left_slice_at hA,directional_basis_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  rw [←JetCalculus.dir_right_slice_at hA]
  simp only [OrthonormalBasis.repr_apply_apply]
  rfl

lemma dir_inner_map {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℕ} {A : E → Point d} {y : E} (hA : DifferentiableAt ℝ A y) (u : Point d) (v : E) :
    JetCalculus.dir v (fun z => inner ℝ u (A z)) y=inner ℝ u ((fderiv ℝ A y) v) := by
  unfold JetCalculus.dir
  change (fderiv ℝ ((innerSL ℝ u) ∘ A) y) v=_
  rw [((innerSL ℝ u).hasFDerivAt.comp y hA.hasFDerivAt).fderiv]
  rfl

theorem conditionalFieldMean_directional_symm {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0<ρ) (hρ1 : ρ<1) (y u v : Point d) :
    JetCalculus.dir v (fun y => inner ℝ u (conditionalFieldMean F x r ρ y)) y=
      JetCalculus.dir u (fun y => inner ℝ v (conditionalFieldMean F x r ρ y)) y := by
  have hm := (conditionalFieldMean_smooth hF x hr.le hl hρ0.le hρ1).differentiable (by simp)
  rw [dir_inner_map (hm y),dir_inner_map (hm y)]
  have hg : gradient (interpolationPotential F x r ρ)=
      fun y => y+(r*ρ) • conditionalFieldMean F x r ρ y :=
    funext (interpolationPotential_gradient hF x hr.le hl hρ0.le hρ1)
  have hd : fderiv ℝ (gradient (interpolationPotential F x r ρ)) y=
      ContinuousLinearMap.id ℝ (Point d)+(r*ρ) • fderiv ℝ (conditionalFieldMean F x r ρ) y := by
    rw [hg]
    exact ((hasFDerivAt_id y).add ((hm y).hasFDerivAt.const_smul (r*ρ))).fderiv
  have hsym := ContDiff.isSymmetric_gradient_derivative
    ((interpolationPotential_smooth hF x hr.le hl hρ0.le hρ1).of_le (by norm_cast)) y u v
  change inner ℝ ((fderiv ℝ (gradient (interpolationPotential F x r ρ)) y) u) v=
    inner ℝ u ((fderiv ℝ (gradient (interpolationPotential F x r ρ)) y) v) at hsym
  rw [hd] at hsym
  simp only [add_apply,smul_apply,ContinuousLinearMap.id_apply,
    inner_add_left,inner_add_right,real_inner_smul_left,inner_smul_right] at hsym
  rw [real_inner_comm v ((fderiv ℝ (conditionalFieldMean F x r ρ) y) u)] at hsym
  have hp : 0 < r*ρ := mul_pos hr hρ0
  nlinarith

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling.JetCalculus
open scoped Classical BigOperators RealInnerProductSpace

def euler {d : ℕ} (f : Point d → ℝ) (y : Point d) : ℝ :=
  ∑i,linearScore i y*dir (spaceBasis d i) f y

lemma dir_linearScore {d : ℕ} (i : Fin d) (v y : Point d) :
    dir v (linearScore i) y=inner ℝ (spaceBasis d i) v := by
  change (fderiv ℝ (innerSL ℝ (spaceBasis d i)) y) v=_
  rw [(innerSL ℝ (spaceBasis d i)).fderiv]
  rfl

lemma smooth_euler {d : ℕ} {f : Point d → ℝ} (hf : ContDiff ℝ (⊤:ℕ∞) f) :
    ContDiff ℝ (⊤:ℕ∞) (euler f) :=
  ContDiff.sum fun i _ => (linearScore_smooth i).mul (smooth_dir hf _)

lemma dir_euler {d : ℕ} {f : Point d → ℝ} (hf : ContDiff ℝ (⊤:ℕ∞) f) (v : Point d) :
    dir v (euler f)=fun y => euler (dir v f) y+dir v f y := by
  unfold euler
  rw [dir_sum Finset.univ (fun i _ => ((linearScore_smooth i).mul (smooth_dir hf _)).differentiable (by simp))]
  simp_rw [dir_mul ((linearScore_smooth _).differentiable (by simp))
    ((smooth_dir hf _).differentiable (by simp)),dir_dir hf v]
  funext y
  simp only [dir_linearScore,Finset.sum_add_distrib]
  have he : (∑i,inner ℝ (spaceBasis d i) v*dir (spaceBasis d i) f y)=dir v f y := by
    simpa only [OrthonormalBasis.repr_apply_apply,spaceBasis,dir,directional] using (congrFun (directional_basis_sum v f) y).symm
  rw [he]
  ring

lemma jet_euler {d : ℕ} {κ : Type*} {f : Point d → ℝ}
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (v : κ → Point d) (l : List κ) :
    jet v l (euler f)=fun y => euler (jet v l f) y+(l.length:ℝ)*jet v l f y := by
  induction l with
  | nil => simp [jet]
  | cons i l ih =>
    simp only [jet,ih]
    rw [dir_add ((smooth_euler (smooth_jet hf v l)).differentiable (by simp))
      ((contDiff_const.mul (smooth_jet hf v l)).differentiable (by simp)),
      dir_euler (smooth_jet hf v l),dir_const_mul ((smooth_jet hf v l).differentiable (by simp))]
    funext y
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    ring

lemma gadj_linearScore {d : ℕ} (f : Point d → ℝ) :
    gadj (spaceBasis d) linearScore (fun i => dir (spaceBasis d i) f)=
      fun y => -(∑i,dir (spaceBasis d i) (dir (spaceBasis d i) f) y)+euler f y := by
  funext y
  simp [gadj,cadj,euler,Finset.sum_add_distrib,Finset.sum_neg_distrib]

lemma jet_gadj_linearScore {d : ℕ} {κ : Type*} {f : Point d → ℝ}
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (v : κ → Point d) (l : List κ) :
    jet v l (gadj (spaceBasis d) linearScore (fun i => dir (spaceBasis d i) f))=
      fun y => gadj (spaceBasis d) linearScore (fun i => dir (spaceBasis d i) (jet v l f)) y+
        (l.length:ℝ)*jet v l f y := by
  rw [gadj_linearScore]
  have hs : ContDiff ℝ (⊤:ℕ∞) (fun y => ∑i,dir (spaceBasis d i) (dir (spaceBasis d i) f) y) :=
    ContDiff.sum fun i _ => smooth_dir (smooth_dir hf _) _
  have he : (fun y => -(∑i,dir (spaceBasis d i) (dir (spaceBasis d i) f) y)+euler f y)=
      fun y => (-1)*(∑i,dir (spaceBasis d i) (dir (spaceBasis d i) f) y)+euler f y := by
    funext y; ring
  rw [he,jet_add (contDiff_const.mul hs) (smooth_euler hf),jet_const_mul hs,
    jet_sum Finset.univ (fun i _ => smooth_dir (smooth_dir hf _) _),jet_euler hf,gadj_linearScore]
  simp_rw [jet_dir (smooth_dir hf _),jet_dir hf]
  funext y
  ring

lemma gadj_perturb {d : ℕ} (M : Fin d → Point d → ℝ) (c : ℝ) (f : Point d → ℝ) :
    gadj (spaceBasis d) (fun i y => linearScore i y+c*M i y) (fun i => dir (spaceBasis d i) f)=
      fun y => gadj (spaceBasis d) linearScore (fun i => dir (spaceBasis d i) f) y+
        c*∑i,M i y*dir (spaceBasis d i) f y := by
  unfold gadj cadj
  funext y
  rw [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem jet_gadj_gradient {d : ℕ} {κ : Type*} [DecidableEq κ]
    {M : Fin d → Point d → ℝ} (hM : ∀i,ContDiff ℝ (⊤:ℕ∞) (M i))
    {f : Point d → ℝ} (hf : ContDiff ℝ (⊤:ℕ∞) f) (c : ℝ)
    (v : κ → Point d) (l : List κ) (hl : l.Nodup) :
    jet v l (gadj (spaceBasis d) (fun i y => linearScore i y+c*M i y)
      (fun i => dir (spaceBasis d i) f))=
      fun y => gadj (spaceBasis d) (fun i y => linearScore i y+c*M i y)
        (fun i => dir (spaceBasis d i) (jet v l f)) y+
        (l.length:ℝ)*jet v l f y+
        c*∑s∈l.toFinset.powerset.erase ∅,∑i,
          jet v (l.filter (fun j => j∈s)) (M i) y*
            dir (spaceBasis d i) (jet v (l.filter (fun j => j∉s)) f) y := by
  have hs : ContDiff ℝ (⊤:ℕ∞) (fun y => ∑i,M i y*dir (spaceBasis d i) f y) :=
    ContDiff.sum fun i _ => (hM i).mul (smooth_dir hf _)
  have hga : ContDiff ℝ (⊤:ℕ∞)
      (gadj (spaceBasis d) linearScore (fun i => dir (spaceBasis d i) f)) :=
    ContDiff.sum fun i _ => smooth_cadj _ (linearScore_smooth i) (smooth_dir hf _)
  rw [gadj_perturb,jet_add hga (contDiff_const.mul hs),jet_const_mul hs,
    jet_gadj_linearScore hf,jet_sum Finset.univ (fun i _ => (hM i).mul (smooth_dir hf _))]
  simp_rw [jet_mul (hM _) (smooth_dir hf _) v l hl,jet_dir hf]
  funext y
  rw [Finset.sum_comm,←Finset.add_sum_erase _ _ (by simp : (∅:Finset κ)∈l.toFinset.powerset)]
  simp only [Finset.notMem_empty,decide_false,List.filter_false,not_false_eq_true,decide_true,List.filter_true,jet]
  rw [gadj_perturb]
  ring

end LogConcaveSampling.JetCalculus

end

end

section

noncomputable section
namespace LogConcaveSampling.JetCalculus
open scoped Classical BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

lemma smooth_dir_at {f : E → ℝ} {p : E} (hf : ContDiffAt ℝ (⊤:ℕ∞) f p) (v : E) :
    ContDiffAt ℝ (⊤:ℕ∞) (dir v f) p :=
  (hf.fderiv_right (by simp)).clm_apply contDiffAt_const

lemma dir_dir_at {f : E → ℝ} {p : E} (hf : ContDiffAt ℝ (⊤:ℕ∞) f p) (v w : E) :
    dir v (dir w f) p=dir w (dir v f) p := by
  have hs : ContDiffAt ℝ (⊤:ℕ∞) (fderiv ℝ f) p := hf.fderiv_right (by simp)
  have hd := hs.differentiableAt (by simp)
  change (fderiv ℝ (fun y => fderiv ℝ f y w) p) v =
    (fderiv ℝ (fun y => fderiv ℝ f y v) p) w
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  simpa only [add_apply,ContinuousLinearMap.comp_apply,
    zero_apply,ContinuousLinearMap.map_zero,zero_add,
    ContinuousLinearMap.flip_apply,fderiv_const_apply] using
    (hf.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr (show (2:ℕ∞)≤⊤ from le_top))).eq v w

lemma dir_add_at {f g : E → ℝ} {p : E} (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ g p) (v : E) :
    dir v (fun x => f x+g x) p=dir v f p+dir v g p := by
  unfold dir
  rw [show (fun x => f x+g x)=f+g from rfl,fderiv_add hf hg]
  rfl

lemma dir_sub_at {f g : E → ℝ} {p : E} (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ g p) (v : E) :
    dir v (fun x => f x-g x) p=dir v f p-dir v g p := by
  unfold dir
  rw [show (fun x => f x-g x)=f-g from rfl,fderiv_sub hf hg]
  rfl

lemma dir_mul_at {f g : E → ℝ} {p : E} (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ g p) (v : E) :
    dir v (fun x => f x*g x) p=dir v f p*g p+f p*dir v g p := by
  unfold dir
  rw [show (fun x => f x*g x)=f*g from rfl,(hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

lemma dir_const_mul_at {f : E → ℝ} {p : E} (hf : DifferentiableAt ℝ f p) (v : E) (c : ℝ) :
    dir v (fun x => c*f x) p=c*dir v f p := by
  unfold dir
  rw [hf.hasFDerivAt.const_mul c |>.fderiv]
  rfl

lemma dir_sum_at {N : Type*} (s : Finset N) {f : N → E → ℝ} {p : E}
    (hf : ∀n∈s,DifferentiableAt ℝ (f n) p) (v : E) :
    dir v (fun x => ∑n∈s,f n x) p=∑n∈s,dir v (f n) p := by
  simp only [dir,(HasFDerivAt.fun_sum (fun n hn => (hf n hn).hasFDerivAt)).fderiv,sum_apply]

lemma smooth_mdir_at (w : E) (b : ι → E) (r : ℝ) {M : ι → E → ℝ} {f : E → ℝ} {p : E}
    (hM : ∀i,ContDiffAt ℝ (⊤:ℕ∞) (M i) p) (hf : ContDiffAt ℝ (⊤:ℕ∞) f p) :
    ContDiffAt ℝ (⊤:ℕ∞) (mdir w b r M f) p :=
  (smooth_dir_at hf w).sub (contDiffAt_const.mul
    (ContDiffAt.sum fun i _ => (hM i).mul (smooth_dir_at hf _)))

lemma mdir_sum_at {N : Type*} (s : Finset N) (w : E) (b : ι → E) (r : ℝ)
    (M : ι → E → ℝ) {f : N → E → ℝ} {p : E} (hf : ∀n∈s,DifferentiableAt ℝ (f n) p) :
    mdir w b r M (fun p => ∑n∈s,f n p) p=∑n∈s,mdir w b r M (f n) p := by
  unfold mdir
  simp_rw [dir_sum_at s hf]
  simp only [Finset.sum_sub_distrib,Finset.mul_sum]
  rw [Finset.sum_comm]

lemma mdir_add_at (w : E) (b : ι → E) (r : ℝ) (M : ι → E → ℝ)
    {f g : E → ℝ} {p : E} (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    mdir w b r M (fun p => f p+g p) p=mdir w b r M f p+mdir w b r M g p := by
  unfold mdir
  simp_rw [dir_add_at hf hg]
  simp only [mul_add,Finset.sum_add_distrib]
  ring

lemma mdir_const_mul_at (w : E) (b : ι → E) (r : ℝ) (M : ι → E → ℝ)
    {f : E → ℝ} {p : E} (hf : DifferentiableAt ℝ f p) (c : ℝ) :
    mdir w b r M (fun p => c*f p) p=c*mdir w b r M f p := by
  unfold mdir
  simp_rw [dir_const_mul_at hf]
  have he : (∑i,M i p*(c*dir (b i) f p))=c*∑i,M i p*dir (b i) f p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  ring

lemma mdir_mul_at (w : E) (b : ι → E) (r : ℝ) (M : ι → E → ℝ)
    {f g : E → ℝ} {p : E} (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    mdir w b r M (fun p => f p*g p) p=
      mdir w b r M f p*g p+f p*mdir w b r M g p := by
  unfold mdir
  simp_rw [dir_mul_at hf hg]
  have he : (∑i,M i p*(dir (b i) f p*g p+f p*dir (b i) g p))=
      (∑i,M i p*dir (b i) f p)*g p+f p*∑i,M i p*dir (b i) g p := by
    rw [Finset.mul_sum,Finset.sum_mul,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  ring

lemma mdir_dir_at (w : E) (b : ι → E) (r : ℝ) {M : ι → E → ℝ} {f : E → ℝ} {p : E}
    (hM : ∀i,ContDiffAt ℝ (⊤:ℕ∞) (M i) p) (hf : ContDiffAt ℝ (⊤:ℕ∞) f p) (v : E) :
    mdir w b r M (dir v f) p=dir v (mdir w b r M f) p+
      r*∑i,dir v (M i) p*dir (b i) f p := by
  have hMi : ∀i,DifferentiableAt ℝ (M i) p := fun i => (hM i).differentiableAt (by simp)
  have hdf : ∀z,DifferentiableAt ℝ (dir z f) p := fun z => (smooth_dir_at hf z).differentiableAt (by simp)
  have hterm (i : ι) : DifferentiableAt ℝ (fun y => M i y*dir (b i) f y) p :=
    (hMi i).mul (hdf (b i))
  have hsum : DifferentiableAt ℝ (fun y => ∑i,M i y*dir (b i) f y) p :=
    DifferentiableAt.fun_sum fun i _ => hterm i
  have he : dir v (mdir w b r M f) p=dir v (dir w f) p-
      r*∑i,(dir v (M i) p*dir (b i) f p+M i p*dir v (dir (b i) f) p) := by
    unfold mdir
    rw [dir_sub_at (hdf w) (hsum.const_mul r),dir_const_mul_at hsum,
      dir_sum_at Finset.univ (fun i _ => hterm i)]
    simp_rw [dir_mul_at (hMi _) (hdf _)]
  rw [he]
  unfold mdir
  simp_rw [dir_dir_at hf v]
  rw [Finset.sum_add_distrib]
  ring

lemma smooth_cadj_at (v : E) {s f : E → ℝ} {p : E}
    (hs : ContDiffAt ℝ (⊤:ℕ∞) s p) (hf : ContDiffAt ℝ (⊤:ℕ∞) f p) :
    ContDiffAt ℝ (⊤:ℕ∞) (cadj v s f) p :=
  (smooth_dir_at hf v).neg.add (hs.mul hf)

lemma gadj_mul_at (b : ι → E) (s : ι → E → ℝ) {V : ι → E → ℝ} {p : E}
    (hV : ∀i,DifferentiableAt ℝ (V i) p) {f : E → ℝ} (hf : DifferentiableAt ℝ f p) :
    gadj b s (fun i p => V i p*f p) p=gadj b s V p*f p-∑i,V i p*dir (b i) f p := by
  unfold gadj cadj
  simp_rw [dir_mul_at (hV _) hf]
  rw [Finset.sum_mul,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma gadj_sum_at {N : Type*} (a : Finset N) (b : ι → E) (s : ι → E → ℝ)
    {V : N → ι → E → ℝ} {p : E} (hV : ∀n∈a,∀i,DifferentiableAt ℝ (V n i) p) :
    gadj b s (fun i p => ∑n∈a,V n i p) p=∑n∈a,gadj b s (V n) p := by
  unfold gadj cadj
  simp_rw [dir_sum_at a (fun n hn => hV n hn _)]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib,Finset.sum_neg_distrib]

theorem mdir_cadj_at (w : E) (b : ι → E) (r : ℝ)
    {M s : ι → E → ℝ} {f : E → ℝ} {p : E}
    (hM : ∀i,ContDiffAt ℝ (⊤:ℕ∞) (M i) p)
    (hs : ∀i,ContDiffAt ℝ (⊤:ℕ∞) (s i) p) (hf : ContDiffAt ℝ (⊤:ℕ∞) f p) (i : ι)
    (hsi : mdir w b r M (s i) p=r*gadj b s (fun k => dir (b i) (M k)) p) :
    mdir w b r M (cadj (b i) (s i) f) p=
      cadj (b i) (s i) (mdir w b r M f) p+
        r*gadj b s (fun k p => dir (b i) (M k) p*f p) p := by
  have hdf := smooth_dir_at hf (b i)
  have hMi (k : ι) := smooth_dir_at (hM k) (b i)
  have he : cadj (b i) (s i) f=fun p => (-1)*dir (b i) f p+s i p*f p := by
    funext p; simp [cadj]
  rw [he,mdir_add_at w b r M ((contDiffAt_const.mul hdf).differentiableAt (by simp))
    (((hs i).mul hf).differentiableAt (by simp))]
  rw [mdir_const_mul_at w b r M (hdf.differentiableAt (by simp)),
      mdir_mul_at w b r M ((hs i).differentiableAt (by simp)) (hf.differentiableAt (by simp)),
      mdir_dir_at w b r hM hf,hsi,
      gadj_mul_at b s (fun k => (hMi k).differentiableAt (by simp)) (hf.differentiableAt (by simp))]
  simp only [cadj]
  ring

theorem mdir_gadj_at (w : E) (b : ι → E) (r : ℝ)
    {M s V : ι → E → ℝ} {p : E}
    (hM : ∀i,ContDiffAt ℝ (⊤:ℕ∞) (M i) p)
    (hs : ∀i,ContDiffAt ℝ (⊤:ℕ∞) (s i) p) (hV : ∀i,ContDiffAt ℝ (⊤:ℕ∞) (V i) p)
    (hscore : ∀i,mdir w b r M (s i) p=r*gadj b s (fun k => dir (b i) (M k)) p) :
    mdir w b r M (gadj b s V) p=
      gadj b s (fun i => mdir w b r M (V i)) p+
      r*gadj b s (fun k p => ∑i,dir (b i) (M k) p*V i p) p := by
  change mdir w b r M (fun p => ∑i,cadj (b i) (s i) (V i) p) p=_
  rw [mdir_sum_at Finset.univ w b r M (fun i _ =>
    (smooth_cadj_at (b i) (hs i) (hV i)).differentiableAt (by simp))]
  simp_rw [mdir_cadj_at w b r hM hs (hV _) _ (hscore _)]
  have hD (i k : ι) : DifferentiableAt ℝ (fun p => dir (b i) (M k) p*V i p) p :=
    ((smooth_dir_at (hM k) (b i)).mul (hV i)).differentiableAt (by simp)
  rw [gadj_sum_at Finset.univ b s (fun i _ k => hD i k)]
  simp only [Finset.sum_add_distrib,Finset.mul_sum,gadj]

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

lemma dir_eventuallyEq {f g : E → ℝ} {p : E} (h : f=ᶠ[nhds p]g) (v : E) :
    dir v f=ᶠ[nhds p]dir v g := by
  filter_upwards [h.fderiv (𝕜:=ℝ)] with y hy
  simp only [dir,hy]

lemma jet_eventuallyEq {f g : E → ℝ} {p : E} (h : f=ᶠ[nhds p]g) (v : κ → E) (l : List κ) :
    jet v l f=ᶠ[nhds p]jet v l g := by
  induction l with
  | nil => exact h
  | cons i l ih => exact dir_eventuallyEq ih (v i)

lemma mdir_eventuallyEq (w : E) (b : ι → E) (r : ℝ)
    {M N : ι → E → ℝ} {f g : E → ℝ} {p : E}
    (hM : ∀i,M i=ᶠ[nhds p]N i) (hf : f=ᶠ[nhds p]g) :
    mdir w b r M f=ᶠ[nhds p]mdir w b r N g := by
  have hMd : ∀ᶠy in nhds p,∀i,M i y=N i y := eventually_all.mpr hM
  have hfd : ∀ᶠy in nhds p,∀i,dir (b i) f y=dir (b i) g y :=
    eventually_all.mpr (fun i => dir_eventuallyEq hf (b i))
  filter_upwards [hMd,hfd,dir_eventuallyEq hf w] with y hM hf hw
  simp only [mdir,hM,hf,hw]

lemma smooth_jet_at {f : E → ℝ} {p : E} (hf : ContDiffAt ℝ (⊤:ℕ∞) f p)
    (v : κ → E) (l : List κ) : ContDiffAt ℝ (⊤:ℕ∞) (jet v l f) p := by
  induction l with
  | nil => exact hf
  | cons i l ih => exact smooth_dir_at ih (v i)

theorem mdir_jet_time [DecidableEq κ] (w : ℝ × E) (b : ι → ℝ × E) (r : ℝ)
    {M : ι → ℝ × E → ℝ} (hM : ∀i,TimeSmooth (M i))
    {f : ℝ × E → ℝ} (hf : TimeSmooth f)
    (v : κ → ℝ × E) (l : List κ) (hl : l.Nodup)
    {p : ℝ × E} (h0 : -1<p.1) (h1 : p.1<1) :
    mdir w b r M (jet v l f) p=jet v l (mdir w b r M f) p+
      r*∑s∈l.toFinset.powerset.erase ∅,∑i,
        jet v (l.filter (fun j => j∈s)) (M i) p*
          dir (b i) (jet v (l.filter (fun j => j∉s)) f) p := by
  choose N hN heN using fun i => (hM i).localize h0 h1
  obtain ⟨g,hg,heg⟩ := hf.localize h0 h1
  have hleft := (mdir_eventuallyEq w b r heN (jet_eventuallyEq heg v l)).eq_of_nhds
  have hright := (jet_eventuallyEq (mdir_eventuallyEq w b r heN heg) v l).eq_of_nhds
  rw [←hleft,congrFun (mdir_jet w b r hN hg v l hl) p,hright]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  rw [(jet_eventuallyEq (heN i) v _).eq_of_nhds,
    (dir_eventuallyEq (jet_eventuallyEq heg v _) (b i)).eq_of_nhds]

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

lemma tensorAdjoint_scalar {d : ℕ} {ι : Type*} [Fintype ι]
    (H : Point d → ℝ) (b : ι → Point d) {V : ι → Point d → ℝ}
    (hV : ∀i,Differentiable ℝ (V i)) (c : ℝ) :
    tensorAdjoint H b (fun i y => c*V i y)=fun y => c*tensorAdjoint H b V y := by
  unfold tensorAdjoint adjointCoordinate
  change (fun y => ∑i, (-JetCalculus.dir (b i) (fun z => c*V i z) y+
    directional (b i) H y*(c*V i y)))=_
  simp_rw [JetCalculus.dir_const_mul (hV _)]
  funext y
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change -(c*JetCalculus.dir (b i) (V i) y)+directional (b i) H y*(c*V i y)=
    c*(-JetCalculus.dir (b i) (V i) y+directional (b i) H y*V i y)
  ring

lemma conditionalU_one_eq_dir {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0<ρ) (hρ1 : ρ<1)
    (u v : Point d) :
    (fun y => conditionalU F x r ρ y u ((lam:ℝ)*r) (fun _ : Unit => v) [()])=
      fun y => ρ⁻¹*JetCalculus.dir v (fun z => inner ℝ u (conditionalFieldMean F x r ρ z)) y := by
  funext y
  have hh := conditionalFieldMean_jet_U hF x hr hlam hl hρ0.le hρ1 u y
    (fun _ : Unit => v) [()]
  have hm : conditionalMeanScalar F x r ρ (fun z => inner ℝ u (primitiveField F x r z))=
      fun y => inner ℝ u (conditionalFieldMean F x r ρ y) :=
    (funext (conditionalFieldMean_inner hF x hr.le hl hρ0.le hρ1 u)).symm
  rw [hm] at hh
  simp only [JetCalculus.jet,List.length_singleton,pow_one] at hh
  rw [hh]
  field_simp [hρ0.ne']

lemma material_score_algebra {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (u y : Point d) :
    materialScalar F x r (fun t z => inner ℝ u z+r*t*inner ℝ u (conditionalFieldMean F x r t z)) ρ y=
      r*ρ*materialScalar F x r (fun t z => inner ℝ u (conditionalFieldMean F x r t z)) ρ y := by
  let m := fun t z => inner ℝ u (conditionalFieldMean F x r t z)
  have hsq : ρ^2<1 := by have := (probability_time hρ0 hρ1).1; linarith
  have hj : DifferentiableAt ℝ (fun p : ℝ × Point d => m p.1 p.2) (ρ,y) :=
    ((innerSL ℝ u).contDiff.contDiffAt.comp (ρ,y)
    (conditionalFieldMean_joint_smooth hF x hr (by linarith) (ρ,y) hsq)).differentiableAt (by simp)
  have hi : DifferentiableAt ℝ (fun t : ℝ => (t,y)) ρ :=
    differentiableAt_id.prodMk (differentiableAt_const y)
  have ht : DifferentiableAt ℝ (fun t => m t y) ρ := by
    have hh := hj.comp ρ hi
    exact hh
  have hs : Differentiable ℝ (m ρ) :=
    ((innerSL ℝ u).contDiff.comp (conditionalFieldMean_smooth hF x hr hl hρ0 hρ1)).differentiable (by simp)
  have htd : deriv (fun t => inner ℝ u y+r*t*m t y) ρ=
      r*m ρ y+(r*ρ)*deriv (fun t => m t y) ρ := by
    have hh := (hasDerivAt_const ρ (inner ℝ u y)).add
      (((hasDerivAt_id ρ).const_mul r).mul ht.hasDerivAt)
    simpa only [Pi.add_def,Pi.mul_def,id_eq,mul_one,zero_add] using hh.deriv
  have hsd : directional (conditionalFieldMean F x r ρ y)
      (fun z => inner ℝ u z+r*ρ*m ρ z) y=
      m ρ y+(r*ρ)*directional (conditionalFieldMean F x r ρ y) (m ρ) y := by
    unfold directional
    have hh := (innerSL ℝ u).hasFDerivAt.add ((hs y).hasFDerivAt.const_mul (r*ρ))
    change (fderiv ℝ (((innerSL ℝ u) : Point d → ℝ) + fun z => (r*ρ)*m ρ z) y) _=_
    rw [hh.fderiv]
    simp [m]
  change deriv (fun t => inner ℝ u y+r*t*m t y) ρ-
    r*directional (conditionalFieldMean F x r ρ y) (fun z => inner ℝ u z+r*ρ*m ρ z) y=
    r*ρ*(deriv (fun t => m t y) ρ-r*directional (conditionalFieldMean F x r ρ y) (m ρ) y)
  rw [htd,hsd]
  ring

theorem material_interpolation_score {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0<ρ) (hρ1 : ρ<1) (u y : Point d) :
    materialScalar F x r (fun t z => inner ℝ u z+r*t*inner ℝ u (conditionalFieldMean F x r t z)) ρ y=
      r*tensorAdjoint (interpolationPotential F x r ρ) (EuclideanSpace.basisFun (Fin d) ℝ)
        (fun i => JetCalculus.dir u (fun z => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)
          (conditionalFieldMean F x r ρ z))) y := by
  rw [material_score_algebra hF x hr.le hl hρ0.le hρ1,
    material_conditionalFieldMean hF x hr hlam hl hρ0.le hρ1]
  have he : (fun i y => conditionalU F x r ρ y u ((lam:ℝ)*r)
      (fun _ : Unit => EuclideanSpace.basisFun (Fin d) ℝ i) [()])=
      fun i y => ρ⁻¹*JetCalculus.dir u (fun z => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)
        (conditionalFieldMean F x r ρ z)) y := by
    funext i y
    rw [congrFun (conditionalU_one_eq_dir hF x hr hlam hl hρ0 hρ1 u _) y]
    rw [conditionalFieldMean_directional_symm hF x hr hl hρ0 hρ1]
  have hD (i : Fin d) : Differentiable ℝ (JetCalculus.dir u (fun z =>
      inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i) (conditionalFieldMean F x r ρ z))) :=
    (JetCalculus.smooth_dir ((innerSL ℝ _).contDiff.comp
      (conditionalFieldMean_smooth hF x hr.le hl hρ0.le hρ1)) u).differentiable (by simp)
  rw [he,tensorAdjoint_scalar _ _ hD]
  field_simp [hρ0.ne']

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

def jointMean {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ) (i : Fin d)
    (p : ℝ × Point d) : ℝ :=
  inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i) (conditionalFieldMean F x r p.1 p.2)

def jointScore {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ) (i : Fin d)
    (p : ℝ × Point d) : ℝ :=
  inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i) p.2+r*p.1*jointMean F x r i p

lemma jointMean_smooth_at {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) {p : ℝ × Point d} (hp : p.1^2<1) (i : Fin d) :
    ContDiffAt ℝ (⊤:ℕ∞) (jointMean F x r i) p :=
  (innerSL ℝ _).contDiff.contDiffAt.comp p
    (conditionalFieldMean_joint_smooth hF x hr (by linarith) p hp)

lemma jointScore_smooth_at {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) {p : ℝ × Point d} (hp : p.1^2<1) (i : Fin d) :
    ContDiffAt ℝ (⊤:ℕ∞) (jointScore F x r i) p :=
  ((innerSL ℝ _).contDiff.contDiffAt.comp p contDiffAt_snd).add
    ((contDiffAt_const.mul contDiffAt_fst).mul (jointMean_smooth_at hF x hr hl hp i))

lemma joint_gadj_slice {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {V : Fin d → ℝ × Point d → ℝ} {y : Point d}
    (hV : ∀i,DifferentiableAt ℝ (V i) (ρ,y)) :
    JetCalculus.gadj jointSpace (jointScore F x r) V (ρ,y)=
      tensorAdjoint (interpolationPotential F x r ρ) (EuclideanSpace.basisFun (Fin d) ℝ)
        (fun i z => V i (ρ,z)) y := by
  unfold JetCalculus.gadj JetCalculus.cadj tensorAdjoint adjointCoordinate
  apply Finset.sum_congr rfl
  intro i _
  simp only [jointSpace]
  rw [←JetCalculus.dir_right_slice_at (hV i)]
  have hs : directional (EuclideanSpace.basisFun (Fin d) ℝ i)
      (interpolationPotential F x r ρ) y=jointScore F x r i (ρ,y) := by
    rw [directional_gradient,
      interpolationPotential_gradient hF x hr hl hρ0 hρ1]
    simp only [jointScore,jointMean,inner_add_left,real_inner_smul_left]
    congr 1
    · exact real_inner_comm _ _
    · congr 1
      exact real_inner_comm _ _
  rw [hs]
  rfl

lemma joint_score_transport {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0<ρ) (hρ1 : ρ<1)
    (y : Point d) (i : Fin d) :
    JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (jointScore F x r i) (ρ,y)=
      r*JetCalculus.gadj jointSpace (jointScore F x r)
        (fun k => JetCalculus.dir (jointSpace i) (jointMean F x r k)) (ρ,y) := by
  have hp : ρ^2<1 := by have := (probability_time hρ0.le hρ1).1; linarith
  have hm := joint_mdir_eq_material F x r ((jointScore_smooth_at hF x hr.le hl (p:=(ρ,y)) hp i).differentiableAt (by simp))
  change JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (jointScore F x r i) (ρ,y)=_ at hm
  rw [hm]
  rw [joint_gadj_slice hF x hr.le hl hρ0.le hρ1 (fun k =>
    (JetCalculus.smooth_dir_at (jointMean_smooth_at hF x hr.le hl hp k) _).differentiableAt (by simp))]
  have he : (fun k z => JetCalculus.dir (jointSpace i) (jointMean F x r k) (ρ,z))=
      fun k => JetCalculus.dir (EuclideanSpace.basisFun (Fin d) ℝ i)
        (fun z => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ k) (conditionalFieldMean F x r ρ z)) := by
    funext k z
    exact (JetCalculus.dir_right_slice_at
      ((jointMean_smooth_at hF x hr.le hl (p:=(ρ,z)) hp k).differentiableAt (by simp)) _).symm
  rw [he]
  exact material_interpolation_score hF x hr hlam hl hρ0 hρ1 _ y

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_GadjScalar
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

namespace JetCalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

lemma gadj_scalar (b : ι → E) (s : ι → E → ℝ) {V : ι → E → ℝ}
    (hV : ∀i,Differentiable ℝ (V i)) (c : ℝ) :
    gadj b s (fun i y => c*V i y)=fun y => c*gadj b s V y := by
  unfold gadj cadj
  simp_rw [dir_const_mul (hV _)]
  funext y
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end JetCalculus

lemma conditionalU_eq_scaled_jet {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0<ρ) (hρ1 : ρ<1)
    {κ : Type*} (v : κ → Point d) (l : List κ) (u : Point d) :
    (fun y => conditionalU F x r ρ y u ((lam:ℝ)*r) v l)=
      fun y => (ρ^l.length)⁻¹*JetCalculus.jet v l
        (fun z => inner ℝ u (conditionalFieldMean F x r ρ z)) y := by
  funext y
  have hh := conditionalFieldMean_jet_U hF x hr hlam hl hρ0.le hρ1 u y v l
  have hm : conditionalMeanScalar F x r ρ (fun z => inner ℝ u (primitiveField F x r z))=
      fun y => inner ℝ u (conditionalFieldMean F x r ρ y) :=
    (funext (conditionalFieldMean_inner hF x hr.le hl hρ0.le hρ1 u)).symm
  rw [hm] at hh
  rw [hh]
  field_simp [hρ0.ne']

lemma conditionalU_smooth_pos {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0<ρ) (hρ1 : ρ<1)
    {κ : Type*} (v : κ → Point d) (l : List κ) (u : Point d) :
    ContDiff ℝ (⊤:ℕ∞) (fun y => conditionalU F x r ρ y u ((lam:ℝ)*r) v l) := by
  rw [conditionalU_eq_scaled_jet hF x hr hlam hl hρ0 hρ1]
  exact contDiff_const.mul (JetCalculus.smooth_jet
    ((innerSL ℝ u).contDiff.comp (conditionalFieldMean_smooth hF x hr.le hl hρ0.le hρ1)) v l)

lemma mean_jet_eq_scaled_U {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {κ : Type*} (v : κ → Point d) (l : List κ) (i : Fin d) :
    JetCalculus.jet v l (fun z => jointMean F x r i (ρ,z))=
      fun y => ρ^l.length*conditionalU F x r ρ y (EuclideanSpace.basisFun (Fin d) ℝ i)
        ((lam:ℝ)*r) v l := by
  funext y
  have hm : conditionalMeanScalar F x r ρ
      (fun z => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i) (primitiveField F x r z))=
      fun y => jointMean F x r i (ρ,y) :=
    (funext (conditionalFieldMean_inner hF x hr.le hl hρ0 hρ1 _)).symm
  rw [←hm]
  exact conditionalFieldMean_jet_U hF x hr hlam hl hρ0 hρ1 _ y v l

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
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

namespace JetCalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {κ : Type*}

lemma jet_right_slice_at {A : ℝ × E → ℝ} {t : ℝ}
    (hA : ∀y,ContDiffAt ℝ (⊤:ℕ∞) A (t,y)) (v : κ → E) (l : List κ) :
    jet v l (fun y => A (t,y))=fun y => jet (fun i => (0,v i)) l A (t,y) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [jet,ih]
    funext y
    exact dir_right_slice_at ((smooth_jet_at (hA y) _ l).differentiableAt (by simp)) _

end JetCalculus

lemma jointMean_timeSmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (i : Fin d) : JetCalculus.TimeSmooth (jointMean F x r i) := by
  intro p h0 h1
  exact jointMean_smooth_at hF x hr hl (by nlinarith) i

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

namespace JetCalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

lemma gadj_right_slice_at (b : ι → E) (s : ι → ℝ × E → ℝ)
    {V : ι → ℝ × E → ℝ} {t : ℝ} {y : E}
    (hV : ∀i,DifferentiableAt ℝ (V i) (t,y)) :
    gadj (fun i => (0,b i)) s V (t,y)=gadj b (fun i z => s i (t,z))
      (fun i z => V i (t,z)) y := by
  unfold gadj cadj
  apply Finset.sum_congr rfl
  intro i _
  rw [dir_right_slice_at (hV i)]

end JetCalculus

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling.JetCalculus
open scoped Classical BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

lemma mdir_time_at (b : ι → E) (r : ℝ) (M : ι → ℝ × E → ℝ)
    {c : ℝ → ℝ} {t : ℝ} (hc : DifferentiableAt ℝ c t) (y : E) :
    mdir (1,0) (fun i => (0,b i)) r M (fun p => c p.1) (t,y)=deriv c t := by
  have hd : DifferentiableAt ℝ (fun p : ℝ × E => c p.1) (t,y) :=
    hc.comp (t,y) differentiableAt_fst
  unfold mdir
  rw [←dir_left_slice_at hd]
  have hs (i : ι) : dir (0,b i) (fun p : ℝ × E => c p.1) (t,y)=0 := by
    rw [←dir_right_slice_at hd]
    simp [dir]
  simp only [hs,mul_zero,Finset.sum_const_zero,sub_zero]

lemma mdir_time_mul_at (b : ι → E) (r : ℝ) (M : ι → ℝ × E → ℝ)
    {c : ℝ → ℝ} {A : ℝ × E → ℝ} {t : ℝ} {y : E}
    (hc : DifferentiableAt ℝ c t) (hA : DifferentiableAt ℝ A (t,y)) :
    mdir (1,0) (fun i => (0,b i)) r M (fun p => c p.1*A p) (t,y)=
      deriv c t*A (t,y)+c t*mdir (1,0) (fun i => (0,b i)) r M A (t,y) := by
  have hd : DifferentiableAt ℝ (fun p : ℝ × E => c p.1) (t,y) :=
    hc.comp (t,y) differentiableAt_fst
  rw [mdir_mul_at _ _ _ _ hd hA,mdir_time_at b r M hc]

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

def jointU {d : ℕ} {κ : Type*} (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (v : κ → Point d) (l : List κ) (i : Fin d) (p : ℝ × Point d) : ℝ :=
  conditionalU F x r p.1 p.2 (EuclideanSpace.basisFun (Fin d) ℝ i) L v l

end LogConcaveSampling

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

lemma truncated_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → E} {k : ℕ} (hf : ContDiff ℝ (k:WithTop ℕ∞) f) (n : ℕ) :
    ContDiff ℝ (k:WithTop ℕ∞) (LinearGrowthODE.truncated f n) :=
  (((PoincareCutoff.bump (E:=E)).contDiff).comp (contDiff_id.const_smul _)).smul hf

theorem autonomous_flow_contDiff (n : ℕ) :
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      {f : E → E} (hf : ContDiff ℝ (n:WithTop ℕ∞) f) {K : ℝ≥0}
      (hL : LipschitzWith K f) {a b : ℝ} (hab : a≤b) (t : Icc a b),
      ContDiff ℝ (n:WithTop ℕ∞) (fun x => flow (fun _ _ => hL)
        (hf.continuous.comp continuous_snd) ⟨a,le_rfl,hab⟩ x t) := by
  induction n with
  | zero =>
    intro E _ _ _ f hf K hL a b hab t
    exact contDiff_zero.mpr (flow_lipschitz (fun _ _ => hL)
      (hf.continuous.comp continuous_snd) ⟨a,le_rfl,hab⟩ t).continuous
  | succ n ih =>
    intro E _ _ _ f hf K hL a b hab t
    have hf1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast Nat.succ_pos n)
    let hc : Continuous (uncurry (fun (_ : ℝ) => f)) := hf.continuous.comp continuous_snd
    let hD : Continuous (uncurry (fun (_ : ℝ) => fderiv ℝ f)) :=
      (hf1.continuous_fderiv (by norm_num)).comp continuous_snd
    let hd : ∀ (u : ℝ) (z : E),HasFDerivAt f (fderiv ℝ f z) z :=
      fun _ z => (hf1.differentiable (by norm_num) z).hasFDerivAt
    cases n with
    | zero =>
      exact flow_contDiff_one_left hab hc (fun _ _ => hL) hD hd t
    | succ m =>
      let J := flowLinearization hab hc (fun _ _ => hL) hD hd
      let X := fun x => flow (fun _ _ => hL) hc ⟨a,le_rfl,hab⟩ x
      have hXd (x : E) : HasFDerivAt (fun z => X z t) (J x t) x :=
        flow_hasFDerivAt_left hab hc (fun _ _ => hL) hD hd x t
      change ContDiff ℝ (((m+1:ℕ):WithTop ℕ∞)+1) (fun x => X x t)
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨fun x => J x t,?_,hXd⟩
      apply contDiff_iff_contDiffAt.mpr
      intro x₀
      let V := variationalField f
      have hV : ContDiff ℝ ((m+1:ℕ):WithTop ℕ∞) V := variationalField_smooth (by simpa using hf)
      have hV1 : ContDiff ℝ 1 V := hV.of_le (by exact_mod_cast Nat.succ_pos m)
      obtain ⟨A,hA⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (flow_continuous (fun _ _ => hL) hc ⟨a,le_rfl,hab⟩ (0:E)).continuousOn
      let C := Real.exp ((K:ℝ)*(b-a))
      have hC : 0<C := Real.exp_pos _
      obtain ⟨N,hN⟩ := exists_nat_gt (max (A+C*(‖x₀‖+1)) C)
      let W := LinearGrowthODE.truncated V N
      have hW : ContDiff ℝ ((m+1:ℕ):WithTop ℕ∞) W := truncated_contDiff hV N
      obtain ⟨L,hWL⟩ := LinearGrowthODE.truncated_lipschitz hV1 N
      have hWc : Continuous (uncurry (fun (_ : ℝ) => W)) := hW.continuous.comp continuous_snd
      let Z (p : E × (E →L[ℝ] E)) := flow (fun _ _ => hWL) hWc ⟨a,le_rfl,hab⟩ p t
      have hZ : ContDiff ℝ ((m+1:ℕ):WithTop ℕ∞) Z := ih hW hWL hab t
      have hloc : (fun x => J x t) =ᶠ[𝓝 x₀]
          (fun x => (Z (x,ContinuousLinearMap.id ℝ E)).2) := by
        filter_upwards [Metric.ball_mem_nhds x₀ zero_lt_one] with x hx
        have hxn : ‖x‖≤‖x₀‖+1 := by
          have hh := norm_le_norm_add_norm_sub x₀ x
          rw [←dist_eq_norm, dist_comm] at hh
          linarith [Metric.mem_ball.mp hx]
        have hb (u : Icc a b) : ‖(X x u,J x u)‖≤(N:ℝ)+1 := by
          have hu : |(u:ℝ)-a|≤b-a := by
            rw [abs_of_nonneg (sub_nonneg.mpr u.2.1)]; linarith [u.2.2]
          have hex : Real.exp ((K:ℝ)*|(u:ℝ)-a|)≤C :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu K.coe_nonneg)
          have hX : ‖X x u‖≤A+C*(‖x₀‖+1) := by
            have hs := (flow_lipschitz (fun _ _ => hL) hc ⟨a,le_rfl,hab⟩ u).dist_le_mul x 0
            simp only [dist_zero_right] at hs
            have hn : ‖X x u‖≤‖X 0 u‖+dist (X x u) (X 0 u) := by
              simpa only [dist_eq_norm, norm_sub_rev] using
                (norm_le_norm_add_norm_sub (X 0 u) (X x u))
            exact hn.trans (add_le_add (hA u u.2) (hs.trans
              (mul_le_mul hex hxn (norm_nonneg _) hC.le)))
          have hJ : ‖J x u‖≤C :=
            (fundamental_norm_bound ⟨a,le_rfl,hab⟩
              (flowSpatialCoefficient_continuous hab hc (fun _ _ => hL) hD x)
              (flowSpatialCoefficient_bound hab hc (fun _ _ => hL) hd x) u).trans hex
          rw [Prod.norm_def]
          exact (max_le_max hX hJ).trans (by linarith)
        have he (u : ℝ) (hu : u∈Icc a b) : W (X x u,J x u)=V (X x u,J x u) :=
          LinearGrowthODE.truncated_eq (hb ⟨u,hu⟩)
        have hcP : Continuous (fun u => (X x u,J x u)) :=
          (flow_continuous (fun _ _ => hL) hc _ x).prodMk
            (fundamental_continuous ⟨a,le_rfl,hab⟩
              (flowSpatialCoefficient_continuous hab hc (fun _ _ => hL) hD x)
              (flowSpatialCoefficient_bound hab hc (fun _ _ => hL) hd x))
        have hdP (u : ℝ) (hu : u∈Icc a b) :
            HasDerivWithinAt (fun u => (X x u,J x u)) (W (X x u,J x u)) (Icc a b) u := by
          rw [he u hu]
          exact (flow_deriv (fun _ _ => hL) hc _ x u hu).prodMk
            (fundamental_deriv ⟨a,le_rfl,hab⟩
              (flowSpatialCoefficient_continuous hab hc (fun _ _ => hL) hD x)
              (flowSpatialCoefficient_bound hab hc (fun _ _ => hL) hd x) u hu)
        have hs := trajectory_dist (fun (_ : ℝ) _ => hWL) hcP.continuousOn hdP
          (flow_continuous (fun _ _ => hWL) hWc ⟨a,le_rfl,hab⟩ (x,ContinuousLinearMap.id ℝ E)).continuousOn
          (flow_deriv (fun _ _ => hWL) hWc ⟨a,le_rfl,hab⟩ (x,ContinuousLinearMap.id ℝ E))
          ⟨a,le_rfl,hab⟩ t
        have hi : (X x a,J x a)=(x,ContinuousLinearMap.id ℝ E) := by
          apply Prod.ext
          · exact flow_initial (fun _ _ => hL) hc ⟨a,le_rfl,hab⟩ x
          · exact fundamental_initial ⟨a,le_rfl,hab⟩
              (flowSpatialCoefficient_continuous hab hc (fun _ _ => hL) hD x)
              (flowSpatialCoefficient_bound hab hc (fun _ _ => hL) hd x)
        rw [show (⟨a,le_rfl,hab⟩ : Icc a b).val=a from rfl,hi,flow_initial,
          dist_self,zero_mul,dist_le_zero] at hs
        exact congrArg Prod.snd hs
      exact (hZ.comp (contDiff_id.prodMk contDiff_const)).snd.contDiffAt.congr_of_eventuallyEq hloc
end LogConcaveSampling.GlobalODE

end

end

section

noncomputable section
namespace LogConcaveSampling.GlobalODE
open Set Function Filter Metric
open scoped Topology NNReal

theorem smooth_flow_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} {f : ℝ → E → E}
    (hf : ContDiff ℝ (n:WithTop ℕ∞) (uncurry f)) {K : ℝ≥0} {a b : ℝ}
    (hL : ∀t∈Icc a b,LipschitzWith K (f t)) (hab : a≤b) (t : Icc a b) :
    ContDiff ℝ (n:WithTop ℕ∞) (fun x => flow hL hf.continuous ⟨a,le_rfl,hab⟩ x t) := by
  cases n with
  | zero => exact contDiff_zero.mpr (flow_lipschitz hL hf.continuous _ t).continuous
  | succ n =>
    let V : ℝ × E → ℝ × E := fun p => (1,f p.1 p.2)
    have hV : ContDiff ℝ ((n+1:ℕ):WithTop ℕ∞) V := contDiff_const.prodMk hf
    have hV1 : ContDiff ℝ 1 V := hV.of_le (by exact_mod_cast Nat.succ_pos n)
    let X := fun x => flow hL hf.continuous ⟨a,le_rfl,hab⟩ x
    apply contDiff_iff_contDiffAt.mpr
    intro x₀
    obtain ⟨A,hA⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((flow_continuous hL hf.continuous ⟨a,le_rfl,hab⟩ (0:E)).continuousOn :
        ContinuousOn (X 0) (Icc a b))
    let C := Real.exp ((K:ℝ)*(b-a))
    have hC : 0<C := Real.exp_pos _
    obtain ⟨N,hN⟩ := exists_nat_gt (max (max |a| |b|) (A+C*(‖x₀‖+1)))
    let W := LinearGrowthODE.truncated V N
    have hW : ContDiff ℝ ((n+1:ℕ):WithTop ℕ∞) W := truncated_contDiff hV N
    obtain ⟨L,hWL⟩ := LinearGrowthODE.truncated_lipschitz hV1 N
    have hWc : Continuous (uncurry (fun (_ : ℝ) => W)) := hW.continuous.comp continuous_snd
    let Z (p : ℝ × E) := flow (fun _ _ => hWL) hWc ⟨a,le_rfl,hab⟩ p t
    have hZ : ContDiff ℝ ((n+1:ℕ):WithTop ℕ∞) Z := autonomous_flow_contDiff _ hW hWL hab t
    have he : (fun x => X x t) =ᶠ[𝓝 x₀] (fun x => (Z (a,x)).2) := by
      filter_upwards [ball_mem_nhds x₀ zero_lt_one] with x hx
      have hxn : ‖x‖≤‖x₀‖+1 := by
        have hh := norm_le_norm_add_norm_sub x₀ x
        rw [←dist_eq_norm,dist_comm] at hh
        linarith [mem_ball.mp hx]
      have hb (u : Icc a b) : ‖((u:ℝ),X x u)‖≤(N:ℝ)+1 := by
        have hu : |(u:ℝ)-a|≤b-a := by
          rw [abs_of_nonneg (sub_nonneg.mpr u.2.1)]; linarith [u.2.2]
        have hex : Real.exp ((K:ℝ)*|(u:ℝ)-a|)≤C :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu K.coe_nonneg)
        have hX : ‖X x u‖≤A+C*(‖x₀‖+1) := by
          have hs := (flow_lipschitz hL hf.continuous ⟨a,le_rfl,hab⟩ u).dist_le_mul x 0
          simp only [dist_zero_right] at hs
          have hn : ‖X x u‖≤‖X 0 u‖+dist (X x u) (X 0 u) := by
            simpa only [dist_eq_norm,norm_sub_rev] using (norm_le_norm_add_norm_sub (X 0 u) (X x u))
          exact hn.trans (add_le_add (hA u u.2) (hs.trans
            (mul_le_mul hex hxn (norm_nonneg _) hC.le)))
        have hau : |(u:ℝ)| ≤ max |a| |b| := by
          rw [abs_le]
          exact ⟨by linarith [neg_abs_le a,le_max_left |a| |b|,u.2.1],
            by linarith [le_abs_self b,le_max_right |a| |b|,u.2.2]⟩
        rw [Prod.norm_def,Real.norm_eq_abs]
        exact (max_le_max hau hX).trans (by linarith)
      have heW (u : ℝ) (hu : u∈Icc a b) : W (u,X x u)=V (u,X x u) :=
        LinearGrowthODE.truncated_eq (hb ⟨u,hu⟩)
      have hcP : Continuous (fun u => (u,X x u)) :=
        continuous_id.prodMk (flow_continuous hL hf.continuous _ x)
      have hdP (u : ℝ) (hu : u∈Icc a b) :
          HasDerivWithinAt (fun u => (u,X x u)) (W (u,X x u)) (Icc a b) u := by
        rw [heW u hu]
        exact (hasDerivWithinAt_id u (Icc a b)).prodMk (flow_deriv hL hf.continuous _ x u hu)
      have hs := trajectory_dist (fun (_ : ℝ) _ => hWL) hcP.continuousOn hdP
        (flow_continuous (fun _ _ => hWL) hWc ⟨a,le_rfl,hab⟩ (a,x)).continuousOn
        (flow_deriv (fun _ _ => hWL) hWc ⟨a,le_rfl,hab⟩ (a,x)) ⟨a,le_rfl,hab⟩ t
      have hi : (a,X x a)=(a,x) := by rw [show X x a=x from flow_initial hL hf.continuous _ x]
      rw [show (⟨a,le_rfl,hab⟩ : Icc a b).val=a from rfl,hi,flow_initial,
        dist_self,zero_mul,dist_le_zero] at hs
      exact congrArg Prod.snd hs
    exact (hZ.comp (contDiff_const.prodMk contDiff_id)).snd.contDiffAt.congr_of_eventuallyEq he

end LogConcaveSampling.GlobalODE

namespace LogConcaveSampling.GlobalODE
open Set Function
open scoped Topology NNReal

theorem smooth_flow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} {f : ℝ → E → E}
    (hf : ContDiff ℝ (n:WithTop ℕ∞) (uncurry f)) {K : ℝ≥0} {a b : ℝ}
    (hL : ∀t∈Icc a b,LipschitzWith K (f t)) (hab : a≤b) (s t : Icc a b) :
    ContDiff ℝ (n:WithTop ℕ∞) (fun x => flow hL hf.continuous s x t) := by
  cases n with
  | zero => exact contDiff_zero.mpr (flow_lipschitz hL hf.continuous s t).continuous
  | succ n =>
    have hf1 : ContDiff ℝ 1 (uncurry f) := hf.of_le (by exact_mod_cast Nat.succ_pos n)
    let D : ℝ → E → E →L[ℝ] E := fun u x =>
      (fderiv ℝ (uncurry f) (u,x)).comp (ContinuousLinearMap.inr ℝ ℝ E)
    have hD : Continuous (uncurry D) :=
      (hf1.continuous_fderiv (by norm_num)).clm_comp continuous_const
    have hd (u : ℝ) (z : E) : HasFDerivAt (f u) (D u z) z := by
      exact ((hf1.differentiable (by norm_num) (u,z)).hasFDerivAt).comp z
        ((hasFDerivAt_const u z).prodMk (hasFDerivAt_id z))
    have hi (u : Icc a b) : ContDiff ℝ ((n+1:ℕ):WithTop ℕ∞)
        (fun x => flow hL hf.continuous u x a) := by
      let H := flowHomeomorph hL hf.continuous ⟨a,le_rfl,hab⟩ u
      let J (x : E) := fundamentalEquiv
        (flowSpatialCoefficient_continuous hab hf.continuous hL hD x)
        (flowSpatialCoefficient_bound hab hf.continuous hL hd x) ⟨a,le_rfl,hab⟩ u
      have hJ (x : E) : HasFDerivAt H (J x : E →L[ℝ] E) x :=
        flow_hasFDerivAt_left hab hf.continuous hL hD hd x u
      exact H.contDiff_symm hJ (smooth_flow_left hf hL hab u)
    have hh := (smooth_flow_left hf hL hab t).comp (hi s)
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    exact (flow_cocycle hL hf.continuous s ⟨a,le_rfl,hab⟩ t x).symm
end LogConcaveSampling.GlobalODE

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_SmoothFlowJoint
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

theorem smooth_flow_joint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : ℝ → E → E}
    (hf : ContDiff ℝ (⊤:ℕ∞) (uncurry f)) {K : ℝ≥0} {a b : ℝ}
    (hL : ∀t∈Icc a b,LipschitzWith K (f t)) (s : Icc a b)
    (p₀ : ℝ × E) (hp₀ : p₀.1∈Ioo a b) :
    ContDiffAt ℝ (⊤:ℕ∞) (fun p : ℝ × E => flow hL hf.continuous s p.2 p.1) p₀ := by
  apply contDiffAt_infty.mpr
  intro n
  let V : ℝ × (ℝ × E) → ℝ × (ℝ × E) := fun p => (0,(p.1,p.1 • f p.2.1 p.2.2))
  have hV : ContDiff ℝ (⊤:ℕ∞) V :=
    contDiff_const.prodMk (contDiff_fst.prodMk (contDiff_fst.smul (hf.comp contDiff_snd)))
  let X := fun x => flow hL hf.continuous s x
  obtain ⟨A,hA⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((flow_continuous hL hf.continuous s (0:E)).continuousOn : ContinuousOn (X 0) (Icc a b))
  let C := Real.exp ((K:ℝ)*(b-a))
  have hC : 0<C := Real.exp_pos _
  obtain ⟨N,hN⟩ := exists_nat_gt (max (b-a) (max (max |a| |b|) (A+C*(‖p₀.2‖+1))))
  let W := LinearGrowthODE.truncated V N
  have hW : ContDiff ℝ (n:WithTop ℕ∞) W := truncated_contDiff (hV.of_le (WithTop.coe_le_coe.mpr le_top)) N
  obtain ⟨L,hWL⟩ := LinearGrowthODE.truncated_lipschitz (hV.of_le (by norm_num)) N
  have hWc : Continuous (uncurry (fun (_ : ℝ) => W)) := hW.continuous.comp continuous_snd
  let Z (p : ℝ × (ℝ × E)) := flow (fun _ _ => hWL) hWc (⟨0,le_rfl,by norm_num⟩ : Icc (0:ℝ) 1) p 1
  have hZ : ContDiff ℝ (n:WithTop ℕ∞) Z := autonomous_flow_contDiff _ hW hWL (by norm_num) ⟨1,by norm_num,le_rfl⟩
  have he : (fun p : ℝ × E => X p.2 p.1) =ᶠ[𝓝 p₀]
      (fun p => (Z (p.1-s,((s:ℝ),p.2))).2.2) := by
    have hn : Ioo a b ×ˢ ball p₀.2 1 ∈ 𝓝 p₀ :=
      (isOpen_Ioo.prod isOpen_ball).mem_nhds ⟨hp₀,mem_ball_self zero_lt_one⟩
    filter_upwards [hn] with p hp
    have hpt : p.1∈Icc a b := ⟨hp.1.1.le,hp.1.2.le⟩
    have hxn : ‖p.2‖≤‖p₀.2‖+1 := by
      have hh := norm_le_norm_add_norm_sub p₀.2 p.2
      rw [←dist_eq_norm,dist_comm] at hh
      linarith [mem_ball.mp hp.2]
    let q : ℝ → ℝ := fun u => (s:ℝ)+(p.1-s)*u
    have hq (u : ℝ) (hu : u∈Icc (0:ℝ) 1) : q u∈Icc a b := by
      have hc := (convex_Icc a b) s.2 hpt (show 0≤1-u by linarith [hu.2]) hu.1 (show 1-u+u=1 by ring)
      convert! hc using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [q]
      ring
    have hqb (u : ℝ) (hu : u∈Icc (0:ℝ) 1) : ‖(p.1-s,(q u,X p.2 (q u)))‖≤(N:ℝ)+1 := by
      have htime (v : Icc a b) : |(v:ℝ)-s|≤b-a := by
        rw [abs_le]; constructor <;> linarith [v.2.1,v.2.2,s.2.1,s.2.2]
      have hex : Real.exp ((K:ℝ)*|q u-s|)≤C :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (htime ⟨q u,hq u hu⟩) K.coe_nonneg)
      have hX : ‖X p.2 (q u)‖≤A+C*(‖p₀.2‖+1) := by
        have hs := (flow_lipschitz hL hf.continuous s ⟨q u,hq u hu⟩).dist_le_mul p.2 0
        simp only [dist_zero_right] at hs
        have hh : ‖X p.2 (q u)‖≤‖X 0 (q u)‖+dist (X p.2 (q u)) (X 0 (q u)) := by
          simpa only [dist_eq_norm,norm_sub_rev] using (norm_le_norm_add_norm_sub (X 0 (q u)) (X p.2 (q u)))
        exact hh.trans (add_le_add (hA (q u) (hq u hu))
          (hs.trans (mul_le_mul hex hxn (norm_nonneg _) hC.le)))
      have hqt : |q u| ≤ max |a| |b| := by
        rw [abs_le]
        constructor <;> linarith [(hq u hu).1,(hq u hu).2,
          neg_abs_le a,le_abs_self b,le_max_left |a| |b|,le_max_right |a| |b|]
      simp only [Prod.norm_def,Real.norm_eq_abs]
      exact (max_le_max (htime ⟨p.1,hpt⟩) (max_le_max hqt hX)).trans (by linarith)
    let P : ℝ → ℝ × (ℝ × E) := fun u => (p.1-s,(q u,X p.2 (q u)))
    have hqc : Continuous q := by dsimp [q]; fun_prop
    have hPc : Continuous P := continuous_const.prodMk
      (hqc.prodMk ((flow_continuous hL hf.continuous s p.2).comp hqc))
    have hPd (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
        HasDerivWithinAt P (W (P u)) (Icc (0:ℝ) 1) u := by
      have heW : W (P u)=V (P u) := LinearGrowthODE.truncated_eq (hqb u hu)
      rw [heW]
      have hdq : HasDerivWithinAt q (p.1-s) (Icc (0:ℝ) 1) u := by
        convert! (hasDerivWithinAt_const u (Icc (0:ℝ) 1) (s:ℝ)).add
          ((hasDerivWithinAt_id u (Icc (0:ℝ) 1)).const_mul (p.1-s)) using 1
        all_goals try with_reducible_and_instances rfl
        simp
      have hdX := (flow_deriv hL hf.continuous s p.2 (q u) (hq u hu)).scomp u hdq hq
      exact (hasDerivWithinAt_const u (Icc (0:ℝ) 1) (p.1-s)).prodMk (hdq.prodMk hdX)
    have h0 : P 0=(p.1-s,((s:ℝ),p.2)) := by
      dsimp [P,q]
      simp only [mul_zero,add_zero]
      rw [show X p.2 s=p.2 from flow_initial hL hf.continuous s p.2]
    have h1 : P 1=(p.1-s,(p.1,X p.2 p.1)) := by
      dsimp [P]
      rw [show q 1=p.1 by dsimp [q]; ring]
    have hs := trajectory_dist (fun (_ : ℝ) _ => hWL) hPc.continuousOn hPd
      (flow_continuous (fun _ _ => hWL) hWc (⟨0,le_rfl,by norm_num⟩ : Icc (0:ℝ) 1) (p.1-s,((s:ℝ),p.2))).continuousOn
      (flow_deriv (fun _ _ => hWL) hWc (⟨0,le_rfl,by norm_num⟩ : Icc (0:ℝ) 1) (p.1-s,((s:ℝ),p.2)))
      (⟨0,le_rfl,by norm_num⟩ : Icc (0:ℝ) 1) (⟨1,by norm_num,le_rfl⟩ : Icc (0:ℝ) 1)
    change dist (P 1) (Z (p.1-s,((s:ℝ),p.2)))≤dist (P 0) _ * _ at hs
    rw [h0,flow_initial,dist_self,zero_mul,dist_le_zero,h1] at hs
    exact congrArg (fun z => z.2.2) hs
  exact ((hZ.comp ((contDiff_fst.sub contDiff_const).prodMk
    (contDiff_const.prodMk contDiff_snd))).snd.snd).contDiffAt.congr_of_eventuallyEq he
end LogConcaveSampling.GlobalODE

end

end

section

noncomputable section
namespace LogConcaveSampling.GlobalODE
open Set Function Filter
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {f : ℝ → E → E}
  (hf : ContDiff ℝ (⊤:ℕ∞) (uncurry f)) {K : ℝ≥0} {a b : ℝ}
  (hab : a≤b) (hL : ∀t∈Icc a b,LipschitzWith K (f t))

lemma spaceTimeForward_smooth (p : ℝ × E) (hp : p.1∈Ioo a b) :
    ContDiffAt ℝ (⊤:ℕ∞) (spaceTimeForward hab hf.continuous hL) p := by
  have hh := contDiffAt_fst.prodMk (smooth_flow_joint hf hL ⟨a,le_rfl,hab⟩ p hp)
  apply hh.congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (Icc_mem_nhds hp.1 hp.2)] with q hq
  simp only [spaceTimeForward,projIcc_of_mem _ hq]

lemma spaceTimeBackward_smooth (p : ℝ × E) (hp : p.1∈Ioo a b) :
    ContDiffAt ℝ (⊤:ℕ∞) (spaceTimeBackward hab hf.continuous hL) p := by
  let D := fun t => fderiv ℝ (f t)
  have hD : Continuous (uncurry D) := by
    have hh := hf.continuous_fderiv (by norm_num)
    have he : uncurry D=fun p : ℝ × E => (fderiv ℝ (uncurry f) p).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
      funext p
      have hg : HasFDerivAt (fun z : E => (p.1,z)) (ContinuousLinearMap.inr ℝ ℝ E) p.2 := by
        convert! (hasFDerivAt_const (𝕜:=ℝ) p.1 p.2).prodMk (hasFDerivAt_id (𝕜:=ℝ) p.2) using 1
        all_goals try with_reducible_and_instances rfl
      exact ((hf.differentiable (by norm_num) p).hasFDerivAt.comp p.2 hg).fderiv
    rw [he]
    exact hh.clm_comp continuous_const
  have hd (t : ℝ) (z : E) : HasFDerivAt (f t) (D t z) z :=
    ((hf.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num) z).hasFDerivAt
  let H := spaceTimeHomeomorph hab hf.continuous hL
  have hp' : (H.symm p).1∈Ioo a b := hp
  exact H.toOpenPartialHomeomorph.contDiffAt_symm (Set.mem_univ p)
    (spaceTimeForward_hasFDerivAt hab hf.continuous hL hD hd (H.symm p) hp')
    (spaceTimeForward_smooth hf hab hL (H.symm p) hp')

lemma backward_flow_smooth (T : Icc a b) (p : ℝ × E) (hp : p.1∈Ioo a b) :
    ContDiffAt ℝ (⊤:ℕ∞)
      (fun p : ℝ × E => flow hL hf.continuous (projIcc a b hab p.1) p.2 T) p := by
  have hA : ContDiff ℝ (⊤:ℕ∞)
      (fun y => flow hL hf.continuous ⟨a,le_rfl,hab⟩ y T) := by
    apply contDiff_infty.mpr
    intro n
    exact smooth_flow (hf.of_le (WithTop.coe_le_coe.mpr le_top)) hL hab _ T
  have hh := hA.contDiffAt.comp p ((spaceTimeBackward_smooth hf hab hL p hp).snd)
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  funext q
  exact (flow_cocycle hL hf.continuous (projIcc a b hab q.1) ⟨a,le_rfl,hab⟩ T q.2).symm
end LogConcaveSampling.GlobalODE

end

end

section

noncomputable section
namespace LogConcaveSampling.GlobalODE
open Set Function
open scoped Topology NNReal

lemma flow_restrict {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b c d : ℝ} {f g : ℝ → E → E} {K L : ℝ≥0}
    (hf : Continuous (uncurry f)) (hg : Continuous (uncurry g))
    (hL : ∀t∈Icc a b,LipschitzWith K (f t))
    (hJ : ∀t∈Icc c d,LipschitzWith L (g t)) (hsub : Icc a b ⊆ Icc c d)
    (he : ∀t∈Icc a b,∀x,f t x=g t x) (s t : Icc a b) (x : E) :
    flow hL hf s x t=flow hJ hg ⟨s,hsub s.2⟩ x t := by
  have hh := trajectory_dist hL (flow_continuous hL hf s x).continuousOn
    (flow_deriv hL hf s x) (flow_continuous hJ hg ⟨s,hsub s.2⟩ x).continuousOn
    (fun u hu => (he u hu _) ▸ (flow_deriv hJ hg ⟨s,hsub s.2⟩ x u (hsub hu)).mono hsub) s t
  simpa only [flow_initial,dist_self,zero_mul,dist_le_zero] using hh
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
open MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical BigOperators NNReal RealInnerProductSpace

lemma conditionalU_moments_sq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ : ρ^2<1)
    {ι : Type*} [DecidableEq ι] (v : ι → Point d) (l : List ι) (hlN : l.Nodup) (u y : Point d) :
    conditionalU F x r ρ y u ((lam:ℝ)*r) v l=
      ((1-ρ^2)^l.length)⁻¹*∑s∈l.toFinset.powerset,
        Appell.inverseMoment (fun t => conditionalPositionMoment F x r v t (ρ,y)) s*
          conditionalMixedMoment F x r u v (l.toFinset\s) (ρ,y) := by
  let := conditionalLaw_probability_sq hF x hr.le hl hρ y
  rw [conditionalU_normalized_jet_sq hF x hr hlam hl hρ]
  rw [Appell.jet_normalizedLaplace_zero_moments
    (conditionalLaw_hasExpMoments_sq hF x hr.le hl hρ y)
    (continuous_const.inner (primitiveField_contDiff hF x r).continuous)
    (primitiveField_inner_growth hF x u hr.le) v l hlN]
  rfl

theorem conditionalU_joint_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    {ι : Type*} [DecidableEq ι] (v : ι → Point d) (l : List ι) (hlN : l.Nodup)
    (u : Point d) (p : ℝ × Point d) (hp : p.1^2<1) :
    ContDiffAt ℝ (⊤:ℕ∞) (fun q : ℝ × Point d => conditionalU F x r q.1 q.2 u ((lam:ℝ)*r) v l) p := by
  have hl' : (lam:ℝ)*r^2<1 := by linarith
  have hM (s : Finset ι) := conditionalPositionMoment_smooth hF x hr.le hl' v s p hp
  have hI (s : Finset ι) := Appell.inverseMoment_contDiffAt hM s
  have hX (s : Finset ι) := conditionalMixedMoment_smooth hF x hr.le hl' u v s p hp
  have hS : ContDiffAt ℝ (⊤:ℕ∞)
      (fun q => ∑s∈l.toFinset.powerset,
        Appell.inverseMoment (fun t => conditionalPositionMoment F x r v t q) s*
          conditionalMixedMoment F x r u v (l.toFinset\s) q) p :=
    ContDiffAt.sum (fun s _ => (hI s).mul (hX _))
  have hA : ContDiffAt ℝ (⊤:ℕ∞) (fun q : ℝ × Point d => ((1-q.1^2)^l.length)⁻¹) p :=
    ((contDiffAt_const.sub (contDiffAt_fst.pow 2)).pow _).inv
      (pow_ne_zero _ (by linarith))
  apply (hA.mul hS).congr_of_eventuallyEq
  filter_upwards [(isOpen_lt (continuous_fst.pow 2) continuous_const).mem_nhds hp] with q hq
  exact conditionalU_moments_sq hF x hr hlam hl hq v l hlN u q.2

lemma jointU_timeSmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    {ι : Type*} [DecidableEq ι] (v : ι → Point d) (l : List ι) (hlN : l.Nodup) (i : Fin d) :
    JetCalculus.TimeSmooth (jointU F x r ((lam:ℝ)*r) v l i) := by
  intro p h0 h1
  exact conditionalU_joint_smooth hF x hr hlam hl v l hlN _ p (by nlinarith)

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Filter
open scoped Topology Classical BigOperators

namespace JetCalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]
lemma smooth_gadj_at (b : ι → E) {s V : ι → E → ℝ} {p : E}
    (hs : ∀i,ContDiffAt ℝ (⊤:ℕ∞) (s i) p) (hV : ∀i,ContDiffAt ℝ (⊤:ℕ∞) (V i) p) :
    ContDiffAt ℝ (⊤:ℕ∞) (gadj b s V) p :=
  ContDiffAt.sum (fun i _ => smooth_cadj_at (b i) (hs i) (hV i))
end JetCalculus

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma joint_score_transport_nonneg {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (y : Point d) (i : Fin d) :
    JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (jointScore F x r i) (ρ,y)=
      r*JetCalculus.gadj jointSpace (jointScore F x r)
        (fun k => JetCalculus.dir (jointSpace i) (jointMean F x r k)) (ρ,y) := by
  rcases hρ0.eq_or_lt with hz|hpos
  · subst ρ
    have hM := jointMean_smooth_at hF x hr.le hl (p:=(0,y)) (by norm_num)
    have hS := jointScore_smooth_at hF x hr.le hl (p:=(0,y)) (by norm_num)
    have ha := JetCalculus.smooth_mdir_at (1,0) jointSpace r hM (hS i)
    have hb := (contDiffAt_const (c:=r)).mul (JetCalculus.smooth_gadj_at jointSpace hS
      (fun k => JetCalculus.smooth_dir_at (hM k) (jointSpace i)))
    have hc : ContinuousAt (fun t : ℝ => (t,y)) 0 := continuousAt_id.prodMk continuousAt_const
    exact eq_zero_of_continuous_pos (ha.continuousAt.comp (f:=fun t : ℝ => (t,y)) hc)
      (hb.continuousAt.comp (f:=fun t : ℝ => (t,y)) hc)
      (fun t h0 h1 => joint_score_transport hF x hr hlam hl h0 h1 y i)
  · exact joint_score_transport hF x hr hlam hl hpos hρ1 y i

theorem physical_material_adjoint_nonneg {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {V : Fin d → ℝ × Point d → ℝ} {y : Point d}
    (hV : ∀i,ContDiffAt ℝ (⊤:ℕ∞) (V i) (ρ,y)) :
    JetCalculus.mdir (1,0) jointSpace r (jointMean F x r)
      (JetCalculus.gadj jointSpace (jointScore F x r) V) (ρ,y)=
      JetCalculus.gadj jointSpace (jointScore F x r)
        (fun i => JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (V i)) (ρ,y)+
      r*JetCalculus.gadj jointSpace (jointScore F x r)
        (fun k p => ∑i,JetCalculus.dir (jointSpace i) (jointMean F x r k) p*V i p) (ρ,y) := by
  have hp : ρ^2<1 := by have := (probability_time hρ0 hρ1).1; linarith
  exact JetCalculus.mdir_gadj_at _ _ _ (jointMean_smooth_at hF x hr.le hl hp)
    (jointScore_smooth_at hF x hr.le hl hp) hV (joint_score_transport_nonneg hF x hr hlam hl hρ0 hρ1 y)

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

namespace TensorExpression

def eval {d : ℕ} (base : ∀q : ℕ,(Fin (q+2) → Fin d) → Point d → ℝ)
    (H : Point d → ℝ) {n : ℕ} : TensorExpression n → (Fin n → Fin d) → Point d → ℝ
  | .jet q,c => base q c
  | .perm e A,c => A.eval base H (c ∘ e)
  | .contract (m:=m) (n:=n) _ _ A B,c => fun y =>
      ∑z : Fin d,A.eval base H (Fin.snoc (fun i : Fin m => c (Fin.castAdd n i)) z) y*
        B.eval base H (Fin.snoc (fun i : Fin n => c (Fin.natAdd m i)) z) y
  | .adjoint _ A,c => tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun z => A.eval base H (Fin.snoc c z))

end TensorExpression
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

namespace TensorExpression

def jointBase {d : ℕ} (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (q : ℕ) (c : Fin (q+2) → Fin d) (p : ℝ × Point d) : ℝ :=
  L⁻¹*jointU F x r L (fun j : Fin (q+1) => JetCalculus.spaceBasis d (c j.castSucc))
    (List.finRange (q+1)) (c (Fin.last (q+1))) p

lemma jointBase_timeSmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (q : ℕ) (c : Fin (q+2) → Fin d) :
    JetCalculus.TimeSmooth (jointBase F x r ((lam:ℝ)*r) q c) := by
  intro p h0 h1
  exact contDiffAt_const.mul (jointU_timeSmooth hF x hr hlam hl _ _
    (List.nodup_finRange _) _ p h0 h1)

end TensorExpression
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

namespace TensorExpression

def jointEval {d : ℕ} (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    {n : ℕ} : TensorExpression n → (Fin n → Fin d) → (ℝ × Point d) → ℝ
  | .jet q,c => jointBase F x r L q c
  | .perm e A,c => A.jointEval F x r L (c ∘ e)
  | .contract (m:=m) (n:=n) _ _ A B,c => fun p =>
      ∑z : Fin d,A.jointEval F x r L (Fin.snoc (fun i : Fin m => c (Fin.castAdd n i)) z) p*
        B.jointEval F x r L (Fin.snoc (fun i : Fin n => c (Fin.natAdd m i)) z) p
  | .adjoint _ A,c => JetCalculus.gadj jointSpace (jointScore F x r)
      (fun z => A.jointEval F x r L (Fin.snoc c z))

lemma jointEval_timeSmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) {n : ℕ} (A : TensorExpression n)
    (c : Fin n → Fin d) : JetCalculus.TimeSmooth (A.jointEval F x r ((lam:ℝ)*r) c) := by
  induction A with
  | jet q => exact jointBase_timeSmooth hF x hr hlam hl q c
  | perm e A ih => exact ih _
  | contract hm hn A B ihA ihB =>
    intro p h0 h1
    exact ContDiffAt.sum (fun z _ => (ihA _ p h0 h1).mul (ihB _ p h0 h1))
  | adjoint hn A ih =>
    intro p h0 h1
    exact JetCalculus.smooth_gadj_at jointSpace (jointScore_smooth_at hF x hr.le hl (by nlinarith))
      (fun z => ih _ p h0 h1)

end TensorExpression
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal

namespace TensorAtom

variable {S T : Type}

def eval {d : ℕ} (A : TensorAtom S) (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (c : S → Fin d) : ℝ × Point d → ℝ := A.expression.jointEval F x r L (c ∘ A.labels)

lemma relabel_eval {d : ℕ} (A : TensorAtom S) (e : S ≃ T) (F : Point d → ℝ)
    (x : Point d) (r L : ℝ) (c : T → Fin d) :
    (A.relabel e).eval F x r L c=A.eval F x r L (c ∘ e) := rfl

lemma reindex_eval {d n : ℕ} (A : TensorAtom S) (e : Fin n ≃ S) (F : Point d → ℝ)
    (x : Point d) (r L : ℝ) (c : Fin n → Fin d) :
    (A.reindex e).jointEval F x r L c=A.eval F x r L (c ∘ e.symm) := by
  rcases A with ⟨m,A,eA⟩
  have h : m=n := by simpa using Fintype.card_congr (eA.trans e.symm)
  subst m
  rfl

lemma contract_eval {d : ℕ} [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
    (A : TensorAtom (S ⊕ Unit)) (B : TensorAtom (T ⊕ Unit)) (F : Point d → ℝ)
    (x : Point d) (r L : ℝ) (c : S ⊕ T → Fin d) (p : ℝ × Point d) :
    (A.contract B).eval F x r L c p=
      ∑ k : Fin d,A.eval F x r L (Sum.elim (fun s => c (Sum.inl s)) (fun _ => k)) p *
        B.eval F x r L (Sum.elim (fun t => c (Sum.inr t)) (fun _ => k)) p := by
  dsimp only [contract,eval,TensorExpression.jointEval]
  apply Finset.sum_congr rfl
  intro k _
  rw [reindex_eval,reindex_eval]
  congr 1
  · congr 1
    convert lastEquiv_snoc (Fintype.equivFin S).symm (fun s => c (Sum.inl s)) k using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext j
    simp [Function.comp_def]
  · congr 1
    convert lastEquiv_snoc (Fintype.equivFin T).symm (fun t => c (Sum.inr t)) k using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext j
    simp [Function.comp_def]

lemma adjoint_eval {d : ℕ} [Fintype S] (hn : 2≤Fintype.card S) (A : TensorAtom (S ⊕ Unit))
    (F : Point d → ℝ) (x : Point d) (r L : ℝ) (c : S → Fin d) :
    (A.adjoint hn).eval F x r L c=
      JetCalculus.gadj jointSpace (jointScore F x r)
        (fun k => A.eval F x r L (Sum.elim c (fun _ => k))) := by
  dsimp only [adjoint,eval,TensorExpression.jointEval]
  congr 1
  funext k
  rw [reindex_eval,lastEquiv_snoc]
  rfl

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
open MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

universe u

def spatialTensor {d : ℕ} {S K : Type u} (F : (S → Fin d) → Point d → ℝ)
    (l : List K) (y : Point d) (c : K ⊕ S → Fin d) : ℝ :=
  JetCalculus.jet (fun k => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl k))) l
    (F (fun s => c (Sum.inr s))) y

def spatialEnvelope {d : ℕ} {S : Type} [Fintype S]
    (F : (S → Fin d) → Point d → ℝ) (j : ℕ) (y : Point d) : ℝ :=
  TensorEnergy.splitEnvelope (spatialTensor F (List.finRange j) y)

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators

lemma conditionalU_map {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ : ℝ)
    (y u : Point d) (L : ℝ) {S T : Type*} (v : T → Point d) (e : S → T) (l : List S) :
    conditionalU F x r ρ y u L v (l.map e)=conditionalU F x r ρ y u L (v ∘ e) l := by
  unfold conditionalU
  simp only [List.length_map,JetCalculus.jet_map,Function.comp_def]

lemma jointU_map {d : ℕ} (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    {S T : Type*} (v : T → Point d) (e : S → T) (l : List S) (i : Fin d) :
    jointU F x r L v (l.map e) i=jointU F x r L (v ∘ e) l i := by
  funext p
  exact conditionalU_map F x r p.1 p.2 _ L v e l

namespace TensorAtom
variable {S : Type}

lemma jetList_eval {d : ℕ} (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l) (hne : l≠[])
    (F : Point d → ℝ) (x : Point d) (r L : ℝ) (c : S ⊕ Unit → Fin d) :
    (jetList l hN hall hne).eval F x r L c=
      fun p => L⁻¹*jointU F x r L (fun s => JetCalculus.spaceBasis d (c (Sum.inl s)))
        l (c (Sum.inr ())) p := by
  cases l with
  | nil => exact (hne rfl).elim
  | cons a l =>
    let e := List.Nodup.getEquivOfForallMemList (a::l) hN hall
    change (fun p => L⁻¹*jointU F x r L
      (fun j : Fin (l.length+1) => JetCalculus.spaceBasis d (c (lastEquiv e j.castSucc)))
      (List.finRange (l.length+1)) (c (lastEquiv e (Fin.last (l.length+1)))) p)=_
    simp only [lastEquiv_castSucc]
    rw [show lastEquiv e (Fin.last (l.length+1))=Sum.inr () from lastEquiv_last e]
    have he : (List.finRange (a::l).length).map e=(a::l) := by
      change (List.finRange (a::l).length).map (a::l).get=(a::l)
      exact List.map_get_finRange (a::l)
    have hh := jointU_map F x r L (fun s => JetCalculus.spaceBasis d (c (Sum.inl s))) e
      (List.finRange (a::l).length) (c (Sum.inr ()))
    rw [he] at hh
    rw [hh]
    rfl

lemma extendedU_eval {d : ℕ} (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l)
    (F : Point d → ℝ) (x : Point d) (r L : ℝ) (c : (S ⊕ Unit) ⊕ Unit → Fin d) :
    (extendedU l hN hall).eval F x r L c=fun p => L⁻¹*
      jointU F x r L (Sum.elim (fun s => JetCalculus.spaceBasis d (c (Sum.inl (Sum.inl s))))
        (fun _ : Unit => JetCalculus.spaceBasis d (c (Sum.inr ()))))
        (Sum.inr ()::l.map Sum.inl) (c (Sum.inl (Sum.inr ()))) p := by
  rw [extendedU,relabel_eval,jetList_eval]
  funext p
  congr 2
  funext s
  cases s <;> rfl

end TensorAtom
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators

lemma jointU_selectList {d : ℕ} (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    {S : Type} (v : S → Point d) (l : List S) (P : S → Prop) [DecidablePred P] (i : Fin d) :
    jointU F x r L (fun s : {s // P s} => v s.val) (selectList P l) i=
      jointU F x r L v (l.filter (fun s => decide (P s))) i := by
  rw [←map_selectList P l,jointU_map]
  rfl

namespace TensorAtom
variable {S : Type}

variable [Fintype S]

lemma splitProduct_eval {d : ℕ} (l : List S) (hN : l.Nodup) (hall : ∀s,s∈l)
    (a : Finset S) (ha : a.Nonempty) (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (c : S ⊕ Unit → Fin d) (p : ℝ × Point d) :
    (splitProduct l hN hall a ha).eval F x r L c p=
      ∑ k : Fin d,(L⁻¹*jointU F x r L (fun s => JetCalculus.spaceBasis d (c (Sum.inl s)))
        (l.filter (fun s => s∈a)) k p)*
      (L⁻¹*jointU F x r L
        (Sum.elim (fun s => JetCalculus.spaceBasis d (c (Sum.inl s)))
          (fun _ : Unit => JetCalculus.spaceBasis d k))
        (Sum.inr ()::(l.filter (fun s => s∉a)).map Sum.inl) (c (Sum.inr ())) p) := by
  let : Nonempty {s // s∈a} := ⟨⟨ha.choose,ha.choose_spec⟩⟩
  dsimp only [splitProduct]
  rw [relabel_eval,contract_eval]
  apply Finset.sum_congr rfl
  intro k _
  rw [jetList_eval,extendedU_eval]
  simp only [Function.comp_apply,Sum.elim_inl,Sum.elim_inr,splitLabels_left,splitLabels_right,splitLabels_field]
  congr 1
  · rw [jointU_selectList F x r L (fun s => JetCalculus.spaceBasis d (c (Sum.inl s))) l (fun s => s∈a) k]
  · have he : (Sum.inr ()::(selectList (fun s => s∉a) l).map Sum.inl).map
        (Sum.map Subtype.val id)=Sum.inr ()::(l.filter (fun s => s∉a)).map Sum.inl := by
      simp only [List.map_cons,Sum.map_inr,id_eq,List.map_map]
      rw [←map_selectList (fun s => s∉a) l,List.map_map]
      rfl
    have hh := jointU_map F x r L
      (Sum.elim (fun s => JetCalculus.spaceBasis d (c (Sum.inl s)))
        (fun _ : Unit => JetCalculus.spaceBasis d k)) (Sum.map Subtype.val id)
      (Sum.inr ()::(selectList (fun s => s∉a) l).map Sum.inl) (c (Sum.inr ()))
    rw [he] at hh
    rw [hh]
    congr 2
    funext s
    cases s <;> rfl

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

namespace JetCalculus
lemma gadj_scalar_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (b : ι → E) (s : ι → E → ℝ) {V : ι → E → ℝ} {p : E}
    (hV : ∀i,DifferentiableAt ℝ (V i) p) (c : ℝ) :
    gadj b s (fun i y => c*V i y) p=c*gadj b s V p := by
  unfold gadj cadj
  simp_rw [dir_const_mul_at (hV _)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
end JetCalculus

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators

namespace JetCalculus

lemma dir_time {d : ℕ} (P : Polynomial ℝ) (v : ℝ × Point d) (p : ℝ × Point d) :
    dir v (fun q : ℝ × Point d => P.eval q.1) p=P.derivative.eval p.1*v.1 := by
  have hh := (P.hasDerivAt p.1).comp_hasFDerivAt p (hasFDerivAt_fst (𝕜:=ℝ) (p:=p))
  simp only [Function.comp_def] at hh
  change (fderiv ℝ (fun q : ℝ × Point d => P.eval q.1) p) v=_
  rw [hh.fderiv]
  rfl

lemma mdir_time {d : ℕ} (P : Polynomial ℝ) (r : ℝ) (M : Fin d → ℝ × Point d → ℝ)
    (p : ℝ × Point d) :
    mdir (1,0) jointSpace r M (fun q : ℝ × Point d => P.eval q.1) p=P.derivative.eval p.1 := by
  unfold mdir
  simp only [dir_time,jointSpace,mul_zero,Finset.sum_const_zero,sub_zero,mul_one]

lemma gadj_time_at {d : ℕ} (P : Polynomial ℝ) (s : Fin d → ℝ × Point d → ℝ)
    {V : Fin d → ℝ × Point d → ℝ} {p : ℝ × Point d}
    (hV : ∀i,DifferentiableAt ℝ (V i) p) :
    gadj jointSpace s (fun i q => P.eval q.1*V i q) p=P.eval p.1*gadj jointSpace s V p := by
  have hP : DifferentiableAt ℝ (fun q : ℝ × Point d => P.eval q.1) p :=
    P.differentiable.differentiableAt.comp p differentiableAt_fst
  unfold gadj cadj
  simp_rw [dir_mul_at hP (hV _),dir_time]
  simp only [jointSpace,mul_zero,zero_mul,zero_add]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end JetCalculus
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

namespace TensorTerm
variable {S T : Type}

def eval {d : ℕ} (A : TensorTerm S) (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (c : S → Fin d) (p : ℝ × Point d) : ℝ :=
  (r*L)^A.power*A.coefficient.eval p.1*A.atom.eval F x r L c p

lemma timeSmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (A : TensorTerm S) (c : S → Fin d) :
    JetCalculus.TimeSmooth (A.eval F x r ((lam:ℝ)*r) c) := by
  intro p h0 h1
  exact (contDiffAt_const.mul ((polynomialTime_smooth A.coefficient).contDiffAt)).mul
    (A.atom.expression.jointEval_timeSmooth hF x hr hlam hl _ p h0 h1)

lemma scale_eval {d : ℕ} (A : TensorTerm S) (n : ℕ) (P : Polynomial ℝ)
    (F : Point d → ℝ) (x : Point d) (r L : ℝ) (c : S → Fin d) (p : ℝ × Point d) :
    (A.scale n P).eval F x r L c p=(r*L)^n*P.eval p.1*A.eval F x r L c p := by
  simp only [scale,eval,pow_add,Polynomial.eval_mul]
  ring

lemma adjoint_eval {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    [Fintype S] (hn : 2≤Fintype.card S) (A : TensorTerm (S ⊕ Unit)) (c : S → Fin d) (y : Point d) :
    (A.adjoint hn).eval F x r ((lam:ℝ)*r) c (ρ,y)=
      JetCalculus.gadj jointSpace (jointScore F x r)
        (fun k => A.eval F x r ((lam:ℝ)*r) (Sum.elim c (fun _ => k))) (ρ,y) := by
  have hA (k : Fin d) : ContDiffAt ℝ (⊤:ℕ∞)
      (A.atom.eval F x r ((lam:ℝ)*r) (Sum.elim c (fun _ => k))) (ρ,y) :=
    A.atom.expression.jointEval_timeSmooth hF x hr hlam hl
    ((Sum.elim c (fun _ => k)) ∘ A.atom.labels) (ρ,y) (by dsimp; linarith) hρ1
  unfold eval adjoint
  rw [TensorAtom.adjoint_eval]
  have he : (fun k p => (r*((lam:ℝ)*r))^A.power*A.coefficient.eval p.1*
      A.atom.eval F x r ((lam:ℝ)*r) (Sum.elim c (fun _ => k)) p)=
      fun k p => (r*((lam:ℝ)*r))^A.power*(A.coefficient.eval p.1*
        A.atom.eval F x r ((lam:ℝ)*r) (Sum.elim c (fun _ => k)) p) := by
    funext k p; ring
  rw [he,JetCalculus.gadj_scalar_at _ _ (fun k =>
    (((polynomialTime_smooth A.coefficient).contDiffAt).mul (hA k)).differentiableAt (by simp)),
    JetCalculus.gadj_time_at _ _ (fun k => (hA k).differentiableAt (by simp))]
  ring

lemma contract_eval {d : ℕ} [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
    (A : TensorTerm (S ⊕ Unit)) (B : TensorTerm (T ⊕ Unit))
    (F : Point d → ℝ) (x : Point d) (r L : ℝ) (c : S ⊕ T → Fin d) (p : ℝ × Point d) :
    (A.contract B).eval F x r L c p=
      ∑k : Fin d,A.eval F x r L (Sum.elim (fun s => c (Sum.inl s)) (fun _ => k)) p*
        B.eval F x r L (Sum.elim (fun t => c (Sum.inr t)) (fun _ => k)) p := by
  simp only [contract,eval,TensorAtom.contract_eval,pow_add,Polynomial.eval_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

end TensorTerm

namespace TensorSum
variable {S T : Type}

def eval {d : ℕ} (A : TensorSum S) (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (c : S → Fin d) (p : ℝ × Point d) : ℝ := ∑i,(A.term i).eval F x r L c p

lemma timeSmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (A : TensorSum S) (c : S → Fin d) :
    JetCalculus.TimeSmooth (A.eval F x r ((lam:ℝ)*r) c) := by
  intro p h0 h1
  exact ContDiffAt.sum (fun i _ => (A.term i).timeSmooth hF x hr hlam hl c p h0 h1)

lemma pure_eval {d : ℕ} (A : TensorAtom S) (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (c : S → Fin d) : (pure A).eval F x r L c=A.eval F x r L c := by
  funext p
  change (∑ _ : Unit, (r*L)^0*(1 : Polynomial ℝ).eval p.1*A.eval F x r L c p)=_
  simp

lemma add_eval {d : ℕ} (A B : TensorSum S) (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (c : S → Fin d) (p : ℝ × Point d) :
    (A.add B).eval F x r L c p=A.eval F x r L c p+B.eval F x r L c p := by
  change (∑ i : A.index ⊕ B.index, (Sum.elim A.term B.term i).eval F x r L c p)=_
  rw [Fintype.sum_sum_type]
  rfl

lemma scale_eval {d : ℕ} (A : TensorSum S) (n : ℕ) (P : Polynomial ℝ)
    (F : Point d → ℝ) (x : Point d) (r L : ℝ) (c : S → Fin d) (p : ℝ × Point d) :
    (A.scale n P).eval F x r L c p=(r*L)^n*P.eval p.1*A.eval F x r L c p := by
  simp only [scale,eval,TensorTerm.scale_eval,Finset.mul_sum]
  rfl

lemma adjoint_eval {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    [Fintype S] (hn : 2≤Fintype.card S) (A : TensorSum (S ⊕ Unit)) (c : S → Fin d) (y : Point d) :
    (A.adjoint hn).eval F x r ((lam:ℝ)*r) c (ρ,y)=
      JetCalculus.gadj jointSpace (jointScore F x r)
        (fun k => A.eval F x r ((lam:ℝ)*r) (Sum.elim c (fun _ => k))) (ρ,y) := by
  unfold eval adjoint
  simp_rw [TensorTerm.adjoint_eval hF x hr hlam hl hρ0 hρ1]
  symm
  apply JetCalculus.gadj_sum_at
  intro i _ k
  exact ((A.term i).timeSmooth hF x hr hlam hl _ (ρ,y) (by dsimp; linarith) hρ1).differentiableAt (by simp)

lemma contract_eval {d : ℕ} [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
    (A : TensorSum (S ⊕ Unit)) (B : TensorSum (T ⊕ Unit))
    (F : Point d → ℝ) (x : Point d) (r L : ℝ) (c : S ⊕ T → Fin d) (p : ℝ × Point d) :
    (A.contract B).eval F x r L c p=
      ∑k : Fin d,A.eval F x r L (Sum.elim (fun s => c (Sum.inl s)) (fun _ => k)) p*
        B.eval F x r L (Sum.elim (fun t => c (Sum.inr t)) (fun _ => k)) p := by
  change (∑ i : A.index × B.index, ((A.term i.1).contract (B.term i.2)).eval F x r L c p)=_
  simp only [TensorTerm.contract_eval,Fintype.sum_prod_type,eval,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext b
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

end TensorSum
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal

lemma jointMean_direction {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (y : Point d) (i k : Fin d) :
    JetCalculus.dir (jointSpace i) (jointMean F x r k) (ρ,y)=
      ρ*jointU F x r ((lam:ℝ)*r) (fun _ : Unit => JetCalculus.spaceBasis d i) [()] k (ρ,y) := by
  have hm := jointMean_timeSmooth hF x hr.le hl k (ρ,y) (by dsimp; linarith) hρ1
  change JetCalculus.dir (0,JetCalculus.spaceBasis d i) (jointMean F x r k) (ρ,y)=_
  rw [←JetCalculus.dir_right_slice_at (hm.differentiableAt (by simp))]
  have hh := congrFun (mean_jet_eq_scaled_U hF x hr hlam hl hρ0 hρ1
    (fun _ : Unit => JetCalculus.spaceBasis d i) [()] k) y
  simpa only [JetCalculus.jet,List.length_cons,List.length_nil,zero_add,pow_one,jointU] using hh

namespace TensorAtom

lemma one_eval {d : ℕ} (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (c : Unit ⊕ Unit → Fin d) :
    one.eval F x r L c=fun p => L⁻¹*jointU F x r L
      (fun _ : Unit => JetCalculus.spaceBasis d (c (Sum.inr ()))) [()] (c (Sum.inl ())) p := by
  rw [one,relabel_eval,jetList_eval]
  rfl

variable {S : Type} [Fintype S] [Nonempty S]

lemma insertOne_eval {d : ℕ} (A : TensorAtom (S ⊕ Unit)) (F : Point d → ℝ)
    (x : Point d) (r L : ℝ) (c : S ⊕ Unit → Fin d) (p : ℝ × Point d) :
    A.insertOne.eval F x r L c p=∑i : Fin d,
      (L⁻¹*jointU F x r L (fun _ : Unit => JetCalculus.spaceBasis d i) [()] (c (Sum.inr ())) p)*
      A.eval F x r L (Sum.elim (fun s => c (Sum.inl s)) (fun _ => i)) p := by
  rw [insertOne,relabel_eval,contract_eval]
  apply Finset.sum_congr rfl
  intro i _
  rw [one_eval]
  rfl

lemma insertOne_mean {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (A : TensorAtom (S ⊕ Unit)) (c : S ⊕ Unit → Fin d) (y : Point d) :
    ∑i : Fin d,JetCalculus.dir (jointSpace i) (jointMean F x r (c (Sum.inr ()))) (ρ,y)*
      A.eval F x r ((lam:ℝ)*r) (Sum.elim (fun s => c (Sum.inl s)) (fun _ => i)) (ρ,y)=
      ((lam:ℝ)*r)*ρ*A.insertOne.eval F x r ((lam:ℝ)*r) c (ρ,y) := by
  rw [insertOne_eval,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [jointMean_direction hF x hr hlam hl hρ0 hρ1]
  have hL : (lam:ℝ)*r≠0 := ne_of_gt (mul_pos (by exact_mod_cast hlam) hr)
  field_simp

end TensorAtom

namespace JetCalculus
lemma gadj_slice_congr_at {d : ℕ} (s : Fin d → ℝ × Point d → ℝ)
    {V W : Fin d → ℝ × Point d → ℝ} {ρ : ℝ} {y : Point d}
    (hV : ∀i,DifferentiableAt ℝ (V i) (ρ,y)) (hW : ∀i,DifferentiableAt ℝ (W i) (ρ,y))
    (he : ∀i z,V i (ρ,z)=W i (ρ,z)) : gadj jointSpace s V (ρ,y)=gadj jointSpace s W (ρ,y) := by
  unfold gadj cadj
  apply Finset.sum_congr rfl
  intro i _
  change -dir (0,spaceBasis d i) (V i) (ρ,y)+_ = -dir (0,spaceBasis d i) (W i) (ρ,y)+_
  rw [←dir_right_slice_at (hV i),←dir_right_slice_at (hW i),show (fun z => V i (ρ,z))=(fun z => W i (ρ,z)) from funext (he i),he i y]
end JetCalculus
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

namespace TensorAtom
variable {S T : Type}

def HasMaterial (A : TensorAtom S) (B : TensorSum S) : Prop :=
  ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}, Primitive F lam →
    ∀(x : Point d) {r ρ : ℝ}, 0 < r → 0<lam → (lam:ℝ)*r^2≤1/2 → 0≤ρ → ρ<1 →
      ∀(c : S → Fin d) (y : Point d),
        JetCalculus.mdir (1,0) jointSpace r (jointMean F x r)
          (A.eval F x r ((lam:ℝ)*r) c) (ρ,y)=B.eval F x r ((lam:ℝ)*r) c (ρ,y)

lemma timeSmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 < r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (A : TensorAtom S) (c : S → Fin d) :
    JetCalculus.TimeSmooth (A.eval F x r ((lam:ℝ)*r) c) :=
  A.expression.jointEval_timeSmooth hF x hr hlam hl _

lemma HasMaterial.relabel {A : TensorAtom S} {B : TensorSum S} (h : A.HasMaterial B) (e : S ≃ T) :
    (A.relabel e).HasMaterial (B.relabel e) := by
  intro d F lam hF x r ρ hr hlam hl h0 h1 c y
  exact h hF x hr hlam hl h0 h1 (c ∘ e) y

lemma HasMaterial.contract [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
    {A : TensorAtom (S ⊕ Unit)} {B : TensorAtom (T ⊕ Unit)}
    {DA : TensorSum (S ⊕ Unit)} {DB : TensorSum (T ⊕ Unit)}
    (hA : A.HasMaterial DA) (hB : B.HasMaterial DB) :
    (A.contract B).HasMaterial ((DA.contract (TensorSum.pure B)).add ((TensorSum.pure A).contract DB)) := by
  intro d F lam hF x r ρ hr hlam hl h0 h1 c y
  have hsA (k : Fin d) := A.timeSmooth hF x hr hlam hl
    (Sum.elim (fun s => c (Sum.inl s)) (fun _ => k)) (ρ,y) (by dsimp; linarith) h1
  have hsB (k : Fin d) := B.timeSmooth hF x hr hlam hl
    (Sum.elim (fun s => c (Sum.inr s)) (fun _ => k)) (ρ,y) (by dsimp; linarith) h1
  have he : (A.contract B).eval F x r ((lam:ℝ)*r) c=fun p =>
      ∑k : Fin d,A.eval F x r ((lam:ℝ)*r) (Sum.elim (fun s => c (Sum.inl s)) (fun _ => k)) p*
        B.eval F x r ((lam:ℝ)*r) (Sum.elim (fun s => c (Sum.inr s)) (fun _ => k)) p :=
    funext (contract_eval A B F x r _ c)
  rw [he,JetCalculus.mdir_sum_at Finset.univ _ _ _ _ (fun k _ => ((hsA k).mul (hsB k)).differentiableAt (by simp))]
  simp_rw [JetCalculus.mdir_mul_at _ _ _ _ ((hsA _).differentiableAt (by simp)) ((hsB _).differentiableAt (by simp)),
    hA hF x hr hlam hl h0 h1,hB hF x hr hlam hl h0 h1]
  rw [TensorSum.add_eval,TensorSum.contract_eval,TensorSum.contract_eval]
  simp_rw [TensorSum.pure_eval]
  exact Finset.sum_add_distrib

lemma HasMaterial.adjoint [Fintype S] [Nonempty S] (hn : 2≤Fintype.card S)
    {A : TensorAtom (S ⊕ Unit)} {DA : TensorSum (S ⊕ Unit)} (hA : A.HasMaterial DA) :
    (A.adjoint hn).HasMaterial ((DA.adjoint hn).add
      ((TensorSum.pure (A.insertOne.adjoint hn)).scale 1 Polynomial.X)) := by
  intro d F lam hF x r ρ hr hlam hl h0 h1 c y
  let L : ℝ := (lam:ℝ)*r
  let V : Fin d → ℝ × Point d → ℝ := fun k => A.eval F x r L (Sum.elim c (fun _ => k))
  let W : Fin d → ℝ × Point d → ℝ := fun k => DA.eval F x r L (Sum.elim c (fun _ => k))
  have hV (k : Fin d) : ContDiffAt ℝ (⊤:ℕ∞) (V k) (ρ,y) :=
    A.timeSmooth hF x hr hlam hl _ (ρ,y) (by dsimp; linarith) h1
  have hW (k : Fin d) : ContDiffAt ℝ (⊤:ℕ∞) (W k) (ρ,y) :=
    DA.timeSmooth hF x hr hlam hl _ (ρ,y) (by dsimp; linarith) h1
  have hp : ρ^2<1 := by nlinarith
  have hM := jointMean_smooth_at hF x hr.le hl (p:=(ρ,y)) hp
  have hda : JetCalculus.gadj jointSpace (jointScore F x r)
      (fun k => JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (V k)) (ρ,y)=
      JetCalculus.gadj jointSpace (jointScore F x r) W (ρ,y) := by
    apply JetCalculus.gadj_slice_congr_at _
    · intro k; exact (JetCalculus.smooth_mdir_at _ _ _ hM (hV k)).differentiableAt (by simp)
    · intro k; exact (hW k).differentiableAt (by simp)
    · intro k z; exact hA hF x hr hlam hl h0 h1 _ z
  let I : Fin d → ℝ × Point d → ℝ := fun k => A.insertOne.eval F x r L (Sum.elim c (fun _ => k))
  have hI (k : Fin d) : ContDiffAt ℝ (⊤:ℕ∞) (I k) (ρ,y) :=
    A.insertOne.timeSmooth hF x hr hlam hl _ (ρ,y) (by dsimp; linarith) h1
  have hdi : JetCalculus.gadj jointSpace (jointScore F x r)
      (fun k p => ∑i,JetCalculus.dir (jointSpace i) (jointMean F x r k) p*V i p) (ρ,y)=
      L*ρ*JetCalculus.gadj jointSpace (jointScore F x r) I (ρ,y) := by
    rw [←JetCalculus.gadj_scalar_at _ _ (fun k => (hI k).differentiableAt (by simp)) (L*ρ)]
    apply JetCalculus.gadj_slice_congr_at _
    · intro k; exact (ContDiffAt.sum (fun i _ =>
        (JetCalculus.smooth_dir_at (hM k) _).mul (hV i))).differentiableAt (by simp)
    · intro k; exact (contDiffAt_const.mul (hI k)).differentiableAt (by simp)
    · intro k z
      have hh := insertOne_mean hF x hr hlam hl h0 h1 A (Sum.elim c (fun _ => k)) z
      simpa only [Sum.elim_inl,Sum.elim_inr] using hh
  rw [adjoint_eval,physical_material_adjoint_nonneg hF x hr hlam hl h0 h1 hV]
  change JetCalculus.gadj jointSpace (jointScore F x r)
      (fun k => JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (V k)) (ρ,y)+
      r*JetCalculus.gadj jointSpace (jointScore F x r)
        (fun k p => ∑i,JetCalculus.dir (jointSpace i) (jointMean F x r k) p*V i p) (ρ,y)=_
  rw [hda,hdi,TensorSum.add_eval,TensorSum.adjoint_eval hF x hr hlam hl h0 h1,
    TensorSum.scale_eval,TensorSum.pure_eval,adjoint_eval]
  simp only [pow_one,Polynomial.eval_X]
  dsimp only [W,I,L]
  ring

end TensorAtom
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

lemma HasMaterial.congr {A A' : TensorAtom S} {B : TensorSum S}
    (h : A.HasMaterial B)
    (he : ∀{d : ℕ} (F : Point d → ℝ) (x : Point d) (r L : ℝ) (c : S → Fin d),
      A'.eval F x r L c=A.eval F x r L c) : A'.HasMaterial B := by
  intro d F lam hF x r ρ hr hlam hl h0 h1 c y
  rw [he]
  exact h hF x hr hlam hl h0 h1 c y

end TensorAtom

namespace TensorExpression

lemma atom_eval {d n : ℕ} (A : TensorExpression n) (F : Point d → ℝ) (x : Point d) (r L : ℝ)
    (c : Fin n → Fin d) : A.atom.eval F x r L c=A.jointEval F x r L c := rfl
end TensorExpression
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal

namespace TensorExpression

lemma atom_contract_eval {d m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    [Nonempty (Fin m)] [Nonempty (Fin n)] (A : TensorExpression (m+1)) (B : TensorExpression (n+1))
    (F : Point d → ℝ) (x : Point d) (r L : ℝ) (c : Fin (m+n) → Fin d) :
    (TensorExpression.contract hm hn A B).atom.eval F x r L c=
      (((A.atom.relabel (TensorAtom.lastEquiv (Equiv.refl (Fin m)))).contract
        (B.atom.relabel (TensorAtom.lastEquiv (Equiv.refl (Fin n))))).relabel finSumFinEquiv).eval F x r L c := by
  rw [TensorAtom.relabel_eval]
  funext p
  rw [TensorAtom.contract_eval]
  change (∑k : Fin d,A.jointEval F x r L _ p*B.jointEval F x r L _ p)=_
  apply Finset.sum_congr rfl
  intro k _
  simp only [TensorAtom.relabel_eval,atom_eval]
  congr 2
  · funext j
    induction j using Fin.lastCases <;> simp [TensorExpression.atom]
    rfl
  · funext j
    induction j using Fin.lastCases <;> simp [TensorExpression.atom]
    rfl

lemma atom_adjoint_eval {d n : ℕ} (hn : 2≤n) (A : TensorExpression (n+1))
    (F : Point d → ℝ) (x : Point d) (r L : ℝ) (c : Fin n → Fin d) :
    (TensorExpression.adjoint hn A).atom.eval F x r L c=
      ((A.atom.relabel (TensorAtom.lastEquiv (Equiv.refl (Fin n)))).adjoint
        (by simpa using hn)).eval F x r L c := by
  rw [TensorAtom.adjoint_eval]
  change JetCalculus.gadj jointSpace (jointScore F x r) (fun k => A.jointEval F x r L (Fin.snoc c k))=_
  congr 1
  funext k
  rw [TensorAtom.relabel_eval,atom_eval]
  congr 1
  funext j
  induction j using Fin.lastCases <;> simp

end TensorExpression
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Filter
open scoped Topology Classical BigOperators NNReal

namespace JetCalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

def materialIter (w : E) (b : ι → E) (r : ℝ) (M : ι → E → ℝ) : ℕ → (E → ℝ) → E → ℝ
  | 0,f => f
  | n+1,f => mdir w b r M (materialIter w b r M n f)

end JetCalculus

end LogConcaveSampling

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

namespace LogConcaveSampling.GraphSchedule
open scoped Classical

variable {V U : Type*} [Fintype V] (key : V → ℕ) (src dst : U → V)

def absorb (first _last : V) (q : ℕ) : Edge (U:=U) q → ℕ
  | Sum.inl e => max (key (src e)+1) (key (dst e)+1)
  | Sum.inr (Sum.inl _) => key first+1
  | Sum.inr (Sum.inr _) => length key+1

include key in
lemma emit_lt_absorb (hkey : Function.Injective key) (hne : ∀e,src e≠dst e)
    (first last : V) (q : ℕ) (e : Edge (U:=U) q) :
    emit key src dst first last q e<absorb key src dst first last q e := by
  rcases e with e | (i|i)
  · exact min_lt_max.mpr (by
      intro he
      have hh : key (src e)=key (dst e) := by omega
      exact hne e (hkey hh))
  · exact Nat.zero_lt_succ _
  · exact Nat.add_lt_add_right (key_lt_length key last) 1

noncomputable def inputEdges (first last : V) (q : ℕ) :
    Frontier.Live (emit key src dst first last q) (absorb key src dst first last q) 0 ≃ Fin q where
  toFun e := by
    rcases e with ⟨e,he⟩
    rcases e with e | (i|i)
    · simp only [emit] at he
      omega
    · exact i
    · simp only [emit] at he
      omega
  invFun i := ⟨Sum.inr (Sum.inl i),Nat.zero_le _,Nat.zero_lt_succ _⟩
  left_inv e := by
    rcases e with ⟨e,he⟩
    rcases e with e | (i|i)
    · simp only [emit] at he
      omega
    · rfl
    · simp only [emit] at he
      omega
  right_inv i := rfl

noncomputable def outputEdges (first last : V) (q : ℕ) :
    Frontier.Live (emit key src dst first last q) (absorb key src dst first last q)
      (length key) ≃ Fin q where
  toFun e := by
    rcases e with ⟨e,he⟩
    rcases e with e | (i|i)
    · have hs := key_lt_length key (src e)
      have ht := key_lt_length key (dst e)
      simp only [absorb] at he
      omega
    · have hs := key_lt_length key first
      simp only [absorb] at he
      omega
    · exact i
  invFun i := ⟨Sum.inr (Sum.inr i),key_lt_length key last,Nat.lt_succ_self _⟩
  left_inv e := by
    rcases e with ⟨e,he⟩
    rcases e with e | (i|i)
    · have hs := key_lt_length key (src e)
      have ht := key_lt_length key (dst e)
      simp only [absorb] at he
      omega
    · have hs := key_lt_length key first
      simp only [absorb] at he
      omega
    · rfl
  right_inv i := rfl

noncomputable def close {C : Type*} (first last : V) (q : ℕ) :
    (Frontier.Live (emit key src dst first last q) (absorb key src dst first last q) 0 → C) ≃
      (Frontier.Live (emit key src dst first last q) (absorb key src dst first last q)
        (length key) → C) :=
  Equiv.arrowCongr ((inputEdges key src dst first last q).trans
    (outputEdges key src dst first last q).symm) (Equiv.refl C)

end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.GraphSchedule
open scoped Classical

variable {V U C : Type*} [Fintype V] (key : V → ℕ) (src dst : U → V)
local instance edgeDecEqC (q : ℕ) : DecidableEq (Edge (U:=U) q) := Classical.decEq _

noncomputable def cutColorEquiv (q : ℕ) :
    (U ⊕ Fin q → C) ≃
      {c : Edge (U:=U) q → C // ∀i : Fin q,c (Sum.inr (Sum.inr i))=c (Sum.inr (Sum.inl i))} where
  toFun c := ⟨duplicate c,fun _ => rfl⟩
  invFun c := Sum.elim (fun u => c.val (Sum.inl u)) (fun i => c.val (Sum.inr (Sum.inl i)))
  left_inv c := by funext e; cases e <;> rfl
  right_inv c := by
    apply Subtype.ext
    funext e
    rcases e with e | (i|i)
    · rfl
    · rfl
    · exact (c.property i).symm

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
local instance edgeDecEqUp (q : ℕ) : DecidableEq (Edge (U:=U) q) := Classical.decEq _
end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.GraphSchedule
open scoped BigOperators Classical
open TensorEnergy

variable {V U : Type*} [Fintype V] [Fintype U]
local instance edgeDecEqRUp (q : ℕ) : DecidableEq (Edge (U:=U) q) := Classical.decEq _
end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.GraphSchedule
open scoped BigOperators Classical
open TensorEnergy

variable {V U : Type*} [Fintype V] [Fintype U] [Nonempty V]
local instance edgeDecEqRank (q : ℕ) : DecidableEq (Edge (U:=U) q) := Classical.decEq _
end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.GraphSchedule
open scoped Classical

variable {V U : Type*} [Fintype V] (key : V → ℕ) (src dst : U → V)

lemma incidentAt_iff (hkey : Function.Injective key) (first last v : V) (q : ℕ)
    (t : Edge (U:=U) q) :
    IncidentAt src dst first last v q t ↔
      absorb key src dst first last q t=key v+1 ∨ emit key src dst first last q t=key v+1 := by
  rcases t with u | (i|i)
  · simp only [IncidentAt,absorb,emit]
    constructor
    · rintro (hs|ht)
      · rw [hs]; omega
      · rw [ht]; omega
    · intro h
      have he : key (src u)=key v ∨ key (dst u)=key v := by omega
      exact he.imp (fun hh => hkey hh) (fun hh => hkey hh)
  · simp only [IncidentAt,absorb,emit]
    constructor
    · intro h; exact Or.inl (congrArg (fun w => key w+1) h)
    · rintro (h|h)
      · exact hkey (by omega)
      · omega
  · simp only [IncidentAt,absorb,emit]
    have hv := key_lt_length key v
    constructor
    · intro h; exact Or.inr (congrArg (fun w => key w+1) h)
    · rintro (h|h)
      · omega
      · exact hkey (by omega)

noncomputable def incidentSplit (hkey : Function.Injective key) (hne : ∀u,src u≠dst u)
    (first last v : V) (q : ℕ) :
    {t : Edge (U:=U) q // IncidentAt src dst first last v q t} ≃
      Frontier.Incoming (absorb key src dst first last q) (key v) ⊕
      Frontier.Outgoing (emit key src dst first last q) (key v) where
  toFun t := if h : absorb key src dst first last q t.val=key v+1 then Sum.inl ⟨t.val,h⟩
    else Sum.inr ⟨t.val,((incidentAt_iff key src dst hkey first last v q t.val).mp t.property).resolve_left h⟩
  invFun t := match t with
    | Sum.inl t => ⟨t.val,(incidentAt_iff key src dst hkey first last v q t.val).mpr (Or.inl t.property)⟩
    | Sum.inr t => ⟨t.val,(incidentAt_iff key src dst hkey first last v q t.val).mpr (Or.inr t.property)⟩
  left_inv t := by dsimp only; split_ifs <;> rfl
  right_inv t := by
    rcases t with t|t
    · simp only [t.property,dite_eq_left]
    · have hn : absorb key src dst first last q t.val≠key v+1 := by
        have hh := emit_lt_absorb key src dst hkey hne first last q t.val
        have ht := t.property
        omega
      simp [hn]
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
open scoped Classical

variable {V U : Type*} [Fintype V] [Fintype U]
    (key : V → ℕ) (src dst : U → V)
local instance edgeDecEqT (q : ℕ) : DecidableEq (Edge (U:=U) q) := Classical.decEq _

noncomputable def incidentMatrix (hkey : Function.Injective key) (hne : ∀u,src u≠dst u)
    (first last v : V) (q d : ℕ)
    (T : ({t : Edge (U:=U) q // IncidentAt src dst first last v q t} → Fin d) → ℝ) :
    (Frontier.Outgoing (emit key src dst first last q) (key v) → Fin d) →
      (Frontier.Incoming (absorb key src dst first last q) (key v) → Fin d) → ℝ :=
  fun o i => T (fun t => Sum.elim i o (incidentSplit key src dst hkey hne first last v q t))

end LogConcaveSampling.GraphSchedule
namespace LogConcaveSampling.GraphSchedule
open scoped BigOperators Classical
open TensorEnergy

variable {V U : Type*} [Fintype V] [Fintype U] [Nonempty V]
local instance edgeDecEqTG (q : ℕ) : DecidableEq (Edge (U:=U) q) := Classical.decEq _
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

def primaryPair (s : ℕ) : (Fin (s+1) × Fin 2) ≃ Primary s :=
  finProdFinEquiv.trans (finCongr (by omega))

@[simp] lemma primaryPair_val (s : ℕ) (t : Fin (s+1)) (z : Fin 2) :
    (primaryPair s (t,z)).val = 2*t.val+z.val := by
  simp [primaryPair,finProdFinEquiv,add_comm]

lemma row_bundle {s : ℕ} (a b : ℕ) (t : Fin (s+1)) (ht : t.val≠0) :
    bundle a b ⟨2*t.val-1,row_index_lt t ht⟩ = a := by
  simp only [bundle, row_index_odd t ht, ite_false]

def encodeWire {s a b : ℕ} : CycleWire s a b → Wire s a b
  | Sum.inl (t,j) => if ht : t.val=0 then Sum.inr j else
      Sum.inl ⟨⟨2*t.val-1,row_index_lt t ht⟩,Fin.cast (row_bundle a b t ht).symm j⟩
  | Sum.inr (t,j) =>
      Sum.inl ⟨⟨2*t.val,col_index_lt t⟩,Fin.cast (col_bundle a b t).symm j⟩

def decodeWire {s a b : ℕ} : Wire s a b → CycleWire s a b
  | Sum.inl ⟨k,j⟩ => if hk : k.val%2=0 then
      Sum.inr (⟨k.val/2,by omega⟩,Fin.cast (by simp only [bundle,hk,ite_true]) j)
    else Sum.inl (⟨k.val/2+1,by omega⟩,Fin.cast (by simp only [bundle,hk,ite_false]) j)
  | Sum.inr j => Sum.inl (0,j)

lemma decode_encode {s a b : ℕ} (w : CycleWire s a b) : decodeWire (encodeWire w)=w := by
  rcases w with ⟨t,j⟩ | ⟨t,j⟩
  · by_cases ht : t.val=0
    · have he : t=0 := Fin.ext ht
      simp [encodeWire,decodeWire,he]
    · have ho := row_index_odd t ht
      simp only [encodeWire,dite_eq_right ht,decodeWire,dite_eq_right ho,Fin.cast_cast,Fin.cast_eq_self]
      congr 2
      apply Fin.ext
      dsimp only
      omega
  · simp only [encodeWire,decodeWire,Nat.mul_mod_right,dite_eq_left,Fin.cast_cast,Fin.cast_eq_self]
    congr 2
    apply Fin.ext
    dsimp only
    omega

lemma encode_decode {s a b : ℕ} (w : Wire s a b) : encodeWire (decodeWire w)=w := by
  rcases w with ⟨k,j⟩ | j
  · by_cases hk : k.val%2=0
    · simp only [decodeWire,dite_eq_left hk,encodeWire]
      congr 1
      apply Sigma.ext
      · apply Fin.ext
        dsimp only
        omega
      · exact (Fin.heq_ext_iff (by congr 1; apply Fin.ext; dsimp; omega)).mpr rfl
    · have hp : k.val/2+1≠0 := by omega
      simp only [decodeWire,dite_eq_right hk,encodeWire,Fin.val_mk,dite_eq_right hp]
      congr 1
      apply Sigma.ext
      · apply Fin.ext
        dsimp only
        omega
      · exact (Fin.heq_ext_iff (by congr 1; apply Fin.ext; dsimp; omega)).mpr rfl
  · rfl

end LogConcaveSampling.CycleTrace

end

end

section

noncomputable section
namespace LogConcaveSampling.CycleTrace
open AdjointRemoval
open scoped Classical BigOperators

variable {s a b : ℕ}

lemma right_row_bundle (t : Fin (s+1)) (ht : t.val≠s) :
    bundle a b ⟨2*t.val+1,right_row_lt t ht⟩=a := by simp [bundle]

def encodeSlot (t : Fin (s+1)) (z : Fin 2) :
    Fin a ⊕ Fin b → ChainSlot (bundle a b) a (primaryPair s (t,z))
  | Sum.inl j => if hz : z.val=0 then
      if ht : t.val=0 then ⟨Sum.inr (Sum.inl j),by
        change 0=primaryPair s (t,z)
        apply Fin.ext
        simp only [Fin.val_zero,primaryPair_val]
        omega⟩
      else ⟨Sum.inl ⟨⟨2*t.val-1,row_index_lt t ht⟩,Fin.cast (row_bundle a b t ht).symm j⟩,by
        apply Or.inr
        apply Fin.ext
        simp only [Fin.val_succ,primaryPair_val]
        omega⟩
    else if ht : t.val=s then ⟨Sum.inr (Sum.inr j),by
        change Fin.last (2*s+1)=primaryPair s (t,z)
        apply Fin.ext
        simp only [Fin.val_last,primaryPair_val]
        omega⟩
      else ⟨Sum.inl ⟨⟨2*t.val+1,right_row_lt t ht⟩,Fin.cast (right_row_bundle t ht).symm j⟩,by
        apply Or.inl
        apply Fin.ext
        simp only [Fin.val_castSucc,primaryPair_val]
        omega⟩
  | Sum.inr j => ⟨Sum.inl ⟨⟨2*t.val,col_index_lt t⟩,Fin.cast (col_bundle a b t).symm j⟩,by
      change ((⟨2*t.val,col_index_lt t⟩ : Fin (2*s+1)).castSucc=primaryPair s (t,z)) ∨
        ((⟨2*t.val,col_index_lt t⟩ : Fin (2*s+1)).succ=primaryPair s (t,z))
      fin_cases z
      · exact Or.inl (Fin.ext (by simp))
      · exact Or.inr (Fin.ext (by simp))⟩

def decodeTraceSlot : TraceEdge (bundle (s:=s) a b) a → Fin a ⊕ Fin b
  | Sum.inl ⟨k,j⟩ => if hk : k.val%2=0 then
      Sum.inr (Fin.cast (by simp only [bundle,hk,ite_true]) j)
    else Sum.inl (Fin.cast (by simp only [bundle,hk,ite_false]) j)
  | Sum.inr (Sum.inl j) => Sum.inl j
  | Sum.inr (Sum.inr j) => Sum.inl j

lemma decode_encodeSlot (t : Fin (s+1)) (z : Fin 2) (j : Fin a ⊕ Fin b) :
    decodeTraceSlot (encodeSlot t z j).val=j := by
  rcases j with j | j
  · by_cases hz : z.val=0
    · by_cases ht : t.val=0
      · simp only [encodeSlot,dite_eq_left hz,dite_eq_left ht,decodeTraceSlot]
      · simp only [encodeSlot,dite_eq_left hz,dite_eq_right ht,decodeTraceSlot,
          dite_eq_right (row_index_odd t ht),Fin.cast_cast,Fin.cast_eq_self]
    · by_cases ht : t.val=s
      · simp only [encodeSlot,dite_eq_right hz,dite_eq_left ht,decodeTraceSlot]
      · have ho : (2*t.val+1)%2≠0 := by omega
        simp only [encodeSlot,dite_eq_right hz,dite_eq_right ht,decodeTraceSlot,
          dite_eq_right ho,Fin.cast_cast,Fin.cast_eq_self]
  · simp [encodeSlot,decodeTraceSlot]

lemma encode_decodeSlot (t : Fin (s+1)) (z : Fin 2)
    (u : ChainSlot (bundle a b) a (primaryPair s (t,z))) :
    encodeSlot t z (decodeTraceSlot u.val)=u := by
  apply Subtype.ext
  rcases u with ⟨⟨k,j⟩| (j|j),hu⟩
  · have hv : k.val=2*t.val+z.val ∨ k.val+1=2*t.val+z.val := by
      change k.castSucc=primaryPair s (t,z) ∨ k.succ=primaryPair s (t,z) at hu
      rcases hu with h|h
      · exact Or.inl (by simpa only [Fin.val_castSucc,primaryPair_val] using congrArg Fin.val h)
      · exact Or.inr (by simpa only [Fin.val_succ,primaryPair_val] using congrArg Fin.val h)
    by_cases hk : k.val%2=0
    · have he : 2*t.val=k.val := by omega
      simp only [decodeTraceSlot,dite_eq_left hk,encodeSlot]
      congr 1
      apply Sigma.ext (Fin.ext he)
      exact (Fin.heq_ext_iff (congrArg (bundle a b) (Fin.ext he))).mpr rfl
    · by_cases hz : z.val=0
      · have ht : t.val≠0 := by omega
        have he : 2*t.val-1=k.val := by omega
        simp only [decodeTraceSlot,dite_eq_right hk,encodeSlot,dite_eq_left hz,dite_eq_right ht]
        congr 1
        apply Sigma.ext (Fin.ext he)
        exact (Fin.heq_ext_iff (congrArg (bundle a b) (Fin.ext he))).mpr rfl
      · have ht : t.val≠s := by omega
        have he : 2*t.val+1=k.val := by omega
        simp only [decodeTraceSlot,dite_eq_right hk,encodeSlot,dite_eq_right hz,dite_eq_right ht]
        congr 1
        apply Sigma.ext (Fin.ext he)
        exact (Fin.heq_ext_iff (congrArg (bundle a b) (Fin.ext he))).mpr rfl
  · have hv : 0=2*t.val+z.val := by
      change 0=primaryPair s (t,z) at hu
      simpa only [Fin.val_zero,primaryPair_val] using congrArg Fin.val hu
    have hz : z.val=0 := by omega
    have ht : t.val=0 := by omega
    simp only [decodeTraceSlot,encodeSlot,dite_eq_left hz,dite_eq_left ht]
  · have hv : 2*s+1=2*t.val+z.val := by
      change Fin.last (2*s+1)=primaryPair s (t,z) at hu
      simpa only [Fin.val_last,primaryPair_val] using congrArg Fin.val hu
    have hz : z.val≠0 := by omega
    have ht : t.val=s := by omega
    simp only [decodeTraceSlot,encodeSlot,dite_eq_right hz,dite_eq_left ht]

def slotEquivAt (i : Primary s) : (Fin a ⊕ Fin b) ≃ ChainSlot (bundle a b) a i where
  toFun u := ⟨(encodeSlot ((primaryPair s).symm i).1 ((primaryPair s).symm i).2 u).val,by
    have h := (encodeSlot ((primaryPair s).symm i).1 ((primaryPair s).symm i).2 u).property
    simpa only [Prod.eta,Equiv.apply_symm_apply] using h⟩
  invFun u := decodeTraceSlot u.val
  left_inv u := decode_encodeSlot _ _ u
  right_inv u := by
    apply Subtype.ext
    let v : ChainSlot (bundle a b) a
        (primaryPair s (((primaryPair s).symm i).1,((primaryPair s).symm i).2)) :=
      ⟨u.val,by simpa only [Prod.eta,Equiv.apply_symm_apply] using u.property⟩
    change (encodeSlot ((primaryPair s).symm i).1 ((primaryPair s).symm i).2
      (decodeTraceSlot u.val)).val=u.val
    exact congrArg (fun w : ChainSlot (bundle a b) a
      (primaryPair s (((primaryPair s).symm i).1,((primaryPair s).symm i).2)) => w.val)
      (encode_decodeSlot _ _ v)

@[simp] lemma slotEquivAt_pair (t : Fin (s+1)) (z : Fin 2) (u : Fin a ⊕ Fin b) :
    slotEquivAt (primaryPair s (t,z)) u=encodeSlot t z u := by
  apply Subtype.ext
  change (encodeSlot ((primaryPair s).symm (primaryPair s (t,z))).1
    ((primaryPair s).symm (primaryPair s (t,z))).2 u).val = _
  rw [Equiv.symm_apply_apply]

def rowAt (t : Fin (s+1)) (z : Fin 2) : Fin (s+1) :=
  if z.val=0 then t else advance t

end LogConcaveSampling.CycleTrace

end

end

section

noncomputable section
namespace LogConcaveSampling.CycleTrace
open AdjointRemoval MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator

variable {s a b d : ℕ}

def colorEquiv (s a b d : ℕ) :
    TraceColors (bundle (s:=s) a b) a d ≃ (RowColors s a d × RowColors s b d) where
  toFun c := (fun t j => c (encodeWire (Sum.inl (t,j))),
    fun t j => c (encodeWire (Sum.inr (t,j))))
  invFun rc w := Sum.elim (fun x => rc.1 x.1 x.2) (fun x => rc.2 x.1 x.2) (decodeWire w)
  left_inv c := by
    funext w
    change Sum.elim (fun x => c (encodeWire (Sum.inl x)))
      (fun x => c (encodeWire (Sum.inr x))) (decodeWire w)=c w
    conv_rhs => rw [←encode_decode w]
    cases decodeWire w <;> rfl
  right_inv rc := by
    apply Prod.ext <;> funext t j <;>
      simp only [decode_encode,Sum.elim_inl,Sum.elim_inr]

def liftField (F : (Fin a ⊕ Fin b → Fin d) → Fin d → Point d → ℝ)
    (i : Primary s) (c : ChainSlot (bundle a b) a i → Fin d) : Fin d → Point d → ℝ :=
  F (c ∘ slotEquivAt i)

end LogConcaveSampling.CycleTrace

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_TensorGraphs_FieldPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.CycleTrace
open AdjointRemoval MeasureTheory TensorEnergy
open scoped Classical BigOperators NNReal ENNReal Matrix.Norms.L2Operator

variable {s a b d : ℕ}

def fieldPosition (v : Fin d → Point d)
    (F : (Fin a ⊕ Fin b → Fin d) → Fin d → Point d → ℝ)
    (e : ℕ) (x : Point d) (c : (Fin a ⊕ Fin b) ⊕ (Unit ⊕ Fin e) → Fin d) : ℝ :=
  JetCalculus.jet (fun k => v (c (Sum.inr (Sum.inr k)))) (List.finRange e)
    (F (fun t => c (Sum.inl t)) (c (Sum.inr (Sum.inl ())))) x

def scorePosition (H : Point d → ℝ) (v : Fin d → Point d)
    (e : ℕ) (x : Point d) (c : Fin (e+2) → Fin d) : ℝ :=
  JetCalculus.jet (fun k : Fin e => v (c ⟨k.val+2,by omega⟩)) (List.finRange e)
    (directional (v (c ⟨0,by omega⟩)) (directional (v (c ⟨1,by omega⟩)) H)) x

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
open MeasureTheory
open scoped Classical BigOperators NNReal

def scoreField {d : ℕ} (H : Point d → ℝ) (c : Empty ⊕ Unit → Fin d) : Point d → ℝ :=
  directional (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr ()))) H

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

def TameAt {S : Type} [Fintype S] {d : ℕ} (μ : Measure (Point d))
    (F : (S → Fin d) → Point d → ℝ) (k C : ℕ) (R : ℝ≥0∞) : Prop :=
  ∀j n,2≤n → (∫⁻x,ENNReal.ofReal (spatialEnvelope F j x)^n ∂μ)≤
    (((C:ℝ≥0∞)*ENNReal.ofReal (analyticBase d j n))^(C*(j+1))*R^(k+j))^n

structure TameScore {d : ℕ} (H : Point d → ℝ) (R : ℝ≥0∞) where
  bound : ℕ → ℝ
  nonneg : ∀e,0≤bound e
  hessian : ∀e y,TensorEnergy.AllSplitBound
    (CycleTrace.scorePosition H (EuclideanSpace.basisFun (Fin d) ℝ) e y) (bound e)
  spatial : ∀e,0<e → ∀y,TensorEnergy.AllSplitBound
    (spatialTensor (scoreField H) (List.finRange e) y) (bound e)
  budget : ∀e,ENNReal.ofReal (bound e)≤(40*((e:ℝ≥0∞)+3))^(16*(e+1))*R^e

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
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

lemma integral_abs_center_le_sqrt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ z, |f z-∫ w,f w ∂μ| ∂μ) ≤ Real.sqrt (Var[f;μ]) := by
  have hm := (hf.sub (memLp_const (∫ w,f w ∂μ))).norm
  have hh := integral_mul_sq_le hm (memLp_const (1:ℝ) (μ:=μ))
  simp only [Pi.sub_apply,Real.norm_eq_abs,mul_one,one_pow,integral_const,
    probReal_univ,smul_eq_mul,sq_abs] at hh
  rw [← variance_eq_integral hf.aemeasurable] at hh
  exact (Real.le_sqrt (integral_nonneg (fun _ => abs_nonneg _)) (variance_nonneg f μ)).2 hh

lemma poincare_integral_norm_center {d : ℕ} {μ : Measure (Point d)}
    [IsProbabilityMeasure μ] {β : ℝ} (hβ : 0≤β) (hP : HasPoincare μ β)
    (hm : Appell.HasMoments μ) :
    (∫ z, ‖z-∫ w,w ∂μ‖ ∂μ) ≤ (d:ℝ)*Real.sqrt β := by
  classical
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hi : Integrable (fun z : Point d => z) μ :=
    (Appell.HasGrowth.linear (ContinuousLinearMap.id ℝ (Point d))).integrable
      continuous_id.aestronglyMeasurable hm
  have hei (i : Fin d) : Integrable (fun z => |inner ℝ (b i) (z-∫ w,w ∂μ)|) μ :=
    ((innerSL ℝ (b i)).integrable_comp (hi.sub (integrable_const _))).norm
  have hv (i : Fin d) : (∫ z, |inner ℝ (b i) (z-∫ w,w ∂μ)| ∂μ) ≤ Real.sqrt β := by
    have hmi : MemLp (fun z => inner ℝ (b i) z) 2 μ :=
      (Appell.HasGrowth.linear (innerSL ℝ (b i))).memLp (by fun_prop) hm
    have hp := hP.lipschitz_variance hβ (innerSL ℝ (b i)).contDiff
      (innerSL ℝ (b i)).lipschitz hmi
    simp only [coe_nnnorm,innerSL_apply_norm,b.norm_eq_one,one_pow,mul_one] at hp
    have hh := (integral_abs_center_le_sqrt hmi).trans (Real.sqrt_le_sqrt hp)
    simpa only [inner_sub_right,integral_inner hi] using hh
  calc
    _ ≤ ∫ z, ∑ i : Fin d, |inner ℝ (b i) (z-∫ w,w ∂μ)| ∂μ := by
      apply integral_mono (hi.sub (integrable_const _)).norm (integrable_finsetSum _ (fun i _ => hei i))
      intro z
      change ‖z-∫ w,w ∂μ‖ ≤ _
      calc
        _ = ‖∑ i : Fin d, inner ℝ (b i) (z-∫ w,w ∂μ) • b i‖ := by
          exact congrArg norm (by simpa only [b.repr_apply_apply] using (b.sum_repr (z-∫ w,w ∂μ)).symm)
        _ ≤ ∑ i : Fin d, ‖inner ℝ (b i) (z-∫ w,w ∂μ) • b i‖ := norm_sum_le _ _
        _ = _ := by simp only [norm_smul,b.norm_eq_one,mul_one,Real.norm_eq_abs]
    _ = ∑ i : Fin d, ∫ z, |inner ℝ (b i) (z-∫ w,w ∂μ)| ∂μ := integral_finsetSum _ (fun i _ => hei i)
    _ ≤ ∑ _i : Fin d, Real.sqrt β := Finset.sum_le_sum (fun i _ => hv i)
    _ = _ := by simp

end LogConcaveSampling

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

lemma conditionalFieldMean_center_error {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    ‖conditionalFieldMean F x r ρ y-primitiveField F x r
      (ρ • y-((1-ρ^2)*r) • conditionalFieldMean F x r ρ y)‖ ≤
      ((lam:ℝ)*r)*((d:ℝ)*Real.sqrt ((Real.pi^2/2)*(1-ρ^2))) := by
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  have hh := norm_integral_sub_map_mean_le (primitiveField_lipschitz hF x hr)
    (conditional_identity_integrable hF x hr hl hρ0 hρ1 y)
  have hb := poincare_integral_norm_center
    (mul_nonneg (by positivity) (probability_time hρ0 hρ1).1.le)
    (conditionalLaw_hasPoincare hF x hr hl hρ0 hρ1 y)
    (conditionalLaw_hasExpMoments hF x hr hl hρ0 hρ1 y).hasMoments
  have hg := hh.trans (mul_le_mul_of_nonneg_left hb (mul_nonneg lam.coe_nonneg hr))
  simpa only [conditional_mean_identity hF x hr hl hρ0 hρ1 y,NNReal.coe_mul,NNReal.coe_mk,conditionalFieldMean] using hg

lemma conditionalFieldMean_error {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    ‖conditionalFieldMean F x r ρ y-primitiveField F x r y‖ ≤
      ((lam:ℝ)*r)*((d:ℝ)*Real.sqrt ((Real.pi^2/2)*(1-ρ^2)))+
      ((lam:ℝ)*r)*((1-ρ)*‖y‖+((1-ρ^2)*r)*‖conditionalFieldMean F x r ρ y‖) := by
  let M := conditionalFieldMean F x r ρ y
  let z := ρ • y-((1-ρ^2)*r) • M
  have he := conditionalFieldMean_center_error hF x hr hl hρ0 hρ1 y
  have hh := (primitiveField_lipschitz hF x hr).dist_le_mul z y
  rw [dist_eq_norm,dist_eq_norm] at hh
  have hb : ‖z-y‖≤(1-ρ)*‖y‖+((1-ρ^2)*r)*‖M‖ := by
    have hz : z-y=-( (1-ρ) • y+((1-ρ^2)*r) • M) := by
      dsimp [z]; simp only [sub_smul,one_smul]; abel
    rw [hz,norm_neg]
    exact (norm_add_le _ _).trans_eq (by rw [norm_smul,norm_smul,Real.norm_eq_abs,
      Real.norm_eq_abs,abs_of_nonneg (by linarith),abs_of_nonneg
        (mul_nonneg (probability_time hρ0 hρ1).1.le hr)])
  calc
    _ ≤ ‖M-primitiveField F x r z‖+‖primitiveField F x r z-primitiveField F x r y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add he (hh.trans (mul_le_mul_of_nonneg_left hb (mul_nonneg lam.coe_nonneg hr)))

end LogConcaveSampling

namespace LogConcaveSampling
open MeasureTheory

lemma conditionalFieldMean_norm_bound {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    ‖conditionalFieldMean F x r ρ y‖ ≤
      2*(‖primitiveField F x r y‖+((lam:ℝ)*r)*
        ((d:ℝ)*Real.sqrt ((Real.pi^2/2)*(1-ρ^2)))+((lam:ℝ)*r)*(1-ρ)*‖y‖) := by
  have hh := conditionalFieldMean_error hF x hr hl hρ0 hρ1 y
  have ht := norm_le_norm_add_norm_sub' (conditionalFieldMean F x r ρ y) (primitiveField F x r y)
  have hc : ((lam:ℝ)*r)*((1-ρ^2)*r)≤1/2 := by
    have hb := mul_le_mul_of_nonneg_left (probability_time hρ0 hρ1).2
      (mul_nonneg lam.coe_nonneg (sq_nonneg r))
    nlinarith
  have hb := mul_le_mul_of_nonneg_right hc (norm_nonneg (conditionalFieldMean F x r ρ y))
  nlinarith

lemma conditionalFieldMean_endpoint_error {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    ‖conditionalFieldMean F x r ρ y-primitiveField F x r y‖ ≤
      ((lam:ℝ)*r)*((d:ℝ)*Real.sqrt ((Real.pi^2/2)*(1-ρ^2)))+
      ((lam:ℝ)*r)*((1-ρ)*‖y‖+((1-ρ^2)*r)*
        (2*(‖primitiveField F x r y‖+((lam:ℝ)*r)*
          ((d:ℝ)*Real.sqrt ((Real.pi^2/2)*(1-ρ^2)))+((lam:ℝ)*r)*(1-ρ)*‖y‖))) := by
  apply (conditionalFieldMean_error hF x hr hl hρ0 hρ1 y).trans
  gcongr
  · exact mul_nonneg (probability_time hρ0 hρ1).1.le hr
  · exact conditionalFieldMean_norm_bound hF x hr hl hρ0 hρ1 y
end LogConcaveSampling

namespace LogConcaveSampling
open MeasureTheory Filter
open scoped Topology

lemma conditionalFieldMean_tendsto_endpoint {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) {ι : Type*} {l : Filter ι} {ρ : ι → ℝ}
    {y : ι → Point d} {y₀ : Point d} (ht : Tendsto ρ l (𝓝 1)) (hy : Tendsto y l (𝓝 y₀))
    (hρ : ∀ᶠ i in l,0≤ρ i ∧ ρ i<1) :
    Tendsto (fun i => conditionalFieldMean F x r (ρ i) (y i)) l (𝓝 (primitiveField F x r y₀)) := by
  have hg := (primitiveField_contDiff hF x r).continuous.continuousAt.tendsto.comp hy
  have he : Tendsto (fun i => conditionalFieldMean F x r (ρ i) (y i)-primitiveField F x r (y i)) l (𝓝 0) := by
    apply squeeze_zero_norm' (hρ.mono (fun i hi => conditionalFieldMean_endpoint_error hF x hr hl hi.1 hi.2 (y i)))
    have hsq : Tendsto (fun i => 1-ρ i^2) l (𝓝 0) := by
      simpa using (tendsto_const_nhds (x:=(1:ℝ))).sub (ht.pow 2)
    have hs : Tendsto (fun i => Real.sqrt ((Real.pi^2/2)*(1-ρ i^2))) l (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hsq).sqrt
    convert! ((tendsto_const_nhds.mul (tendsto_const_nhds.mul hs)).add
      (tendsto_const_nhds.mul (((tendsto_const_nhds.sub ht).mul hy.norm).add
        ((hsq.mul tendsto_const_nhds).mul
          (tendsto_const_nhds.mul ((hg.norm.add
            (tendsto_const_nhds.mul (tendsto_const_nhds.mul hs))).add
              ((tendsto_const_nhds.mul (tendsto_const_nhds.sub ht)).mul hy.norm))))))) using 1; simp
  simpa only [Function.comp_apply,sub_add_cancel,zero_add] using he.add hg
end LogConcaveSampling
namespace LogConcaveSampling
open Set Filter Function
open scoped Topology

def closedFieldMean {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ : ℝ)
    (y : Point d) : Point d :=
  if ρ<1 then conditionalFieldMean F x r ρ y else primitiveField F x r y

lemma closedFieldMean_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) :
    Continuous (fun p : Icc (0:ℝ) 1 × Point d => closedFieldMean F x r p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have ht : Continuous (fun p : Icc (0:ℝ) 1 × Point d => (p.1:ℝ)) := continuous_subtype_val.comp continuous_fst
  have hy : Continuous (fun p : Icc (0:ℝ) 1 × Point d => p.2) := continuous_snd
  by_cases hp : (p.1:ℝ)<1
  · have hs := (conditionalFieldMean_joint_smooth hF x hr (by linarith) ((p.1:ℝ),p.2)
      (by have ha := (probability_time p.1.2.1 hp).1; linarith)).continuousAt
    have he : (fun q : Icc (0:ℝ) 1 × Point d => closedFieldMean F x r q.1 q.2) =ᶠ[𝓝 p]
        (fun q => conditionalFieldMean F x r q.1 q.2) := by
      filter_upwards [ht.continuousAt (eventually_lt_nhds hp)] with q hq
      change (q.1:ℝ)<1 at hq
      simp only [closedFieldMean,ite_eq_left hq]
    exact ((hs.comp (f:=fun q : Icc (0:ℝ) 1 × Point d => ((q.1:ℝ),q.2)) (ht.continuousAt.prodMk hy.continuousAt))).congr_of_eventuallyEq he
  · have hp1 : (p.1:ℝ)=1 := le_antisymm p.1.2.2 (le_of_not_gt hp)
    change Tendsto _ (𝓝 p) (𝓝 (closedFieldMean F x r p.1 p.2))
    rw [closedFieldMean,ite_eq_right hp]
    apply Filter.Tendsto.if
    · apply conditionalFieldMean_tendsto_endpoint hF x hr hl
      · simpa only [hp1] using (ht.continuousAt (x:=p)).tendsto.mono_left inf_le_left
      · exact hy.continuousAt.tendsto.mono_left inf_le_left
      · filter_upwards [self_mem_nhdsWithin] with q hq
        exact ⟨q.1.2.1,hq⟩
    · exact ((primitiveField_contDiff hF x r).continuous.comp hy).continuousAt.tendsto.mono_left inf_le_left

def fullProbabilityVelocity {d : ℕ} (F : Point d → ℝ) (x : Point d) (r t : ℝ)
    (z : Point d) : Point d :=
  -r • closedFieldMean F x r (projIcc 0 1 (by norm_num) t) z

lemma fullProbabilityVelocity_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) : Continuous (uncurry (fullProbabilityVelocity F x r)) := by
  have ht : Continuous (fun p : ℝ × Point d => projIcc (0:ℝ) 1 (by norm_num) p.1) :=
    continuous_projIcc.comp continuous_fst
  exact (continuous_const (y:=(-r:ℝ))).smul ((closedFieldMean_continuous hF x hr hl).comp
    (ht.prodMk continuous_snd))

lemma fullProbabilityVelocity_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (t : ℝ) :
    LipschitzWith ⟨(Real.pi^2/2)*(lam:ℝ)*r^2,by positivity⟩ (fullProbabilityVelocity F x r t) := by
  let s := projIcc 0 1 (by norm_num) t
  by_cases hs : (s:ℝ)<1
  · have he : fullProbabilityVelocity F x r t=probabilityVelocity F x r s := by
      funext z
      simp only [fullProbabilityVelocity,closedFieldMean,probabilityVelocity,s,ite_eq_left hs]
    rw [he]
    exact probabilityVelocity_lipschitz hF x hr hl ⟨s.2.1,le_rfl⟩ hs
  · have he : fullProbabilityVelocity F x r t=fun z => -r • primitiveField F x r z := by
      funext z
      simp only [fullProbabilityVelocity,closedFieldMean,s,ite_eq_right hs]
    rw [he]
    apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [dist_eq_norm,← smul_sub,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg hr]
    have hh := (primitiveField_lipschitz hF x hr).dist_le_mul u v
    rw [dist_eq_norm] at hh
    calc
      _ ≤ r*((lam:ℝ)*r*dist u v) := mul_le_mul_of_nonneg_left hh hr
      _ ≤ ((Real.pi^2/2)*(lam:ℝ)*r^2)*dist u v := by
        have hp : 1≤Real.pi^2/2 := by nlinarith [Real.pi_gt_three]
        have hnon : 0≤(lam:ℝ)*r^2*dist u v := by positivity
        nlinarith
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Dynamics_FullProbabilityFlow
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
open Set Function MeasureTheory Filter ProbabilityTheory
open scoped Topology

def fullProbabilityFlow {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (t : ℝ) (z : Point d) : Point d :=
  GlobalODE.flow (a:=0) (b:=1) (fun t _ => fullProbabilityVelocity_lipschitz hF x hr hl t)
    (fullProbabilityVelocity_continuous hF x hr hl) ⟨0,le_rfl,by norm_num⟩ z t

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_LogMeshLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.Quadrature
open Real

lemma logMeshStep_pos {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h) :
    0<logMeshStep T h :=
  div_pos (logMeshLength_pos hT0 hT1) (by exact_mod_cast logMeshCount_pos hT0 hT1 hh)

lemma logMeshNode_last {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h) :
    logMeshNode T h (logMeshCount T h)=T := by
  have hN : (logMeshCount T h:ℝ)≠0 := by
    exact_mod_cast ne_of_gt (logMeshCount_pos hT0 hT1 hh)
  dsimp [logMeshNode,logMeshStep,logMeshLength]
  rw [neg_mul, mul_div_cancel₀ _ hN,neg_neg,Real.exp_log (by linarith : 0<1-T)]
  ring

lemma logMeshNode_sub {T h : ℝ} (j : ℕ) :
    logMeshNode T h (j+1)-logMeshNode T h j=
      (1-logMeshNode T h j)*(1-Real.exp (-logMeshStep T h)) := by
  have he : -((j+1:ℕ):ℝ)*logMeshStep T h=
      -(j:ℝ)*logMeshStep T h+(-logMeshStep T h) := by push_cast; ring
  simp only [logMeshNode,he,Real.exp_add]
  ring

lemma logMeshNode_strictMono {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h) :
    StrictMono (logMeshNode T h) := by
  apply strictMono_nat_of_lt_succ
  intro j
  have hs := logMeshStep_pos hT0 hT1 hh
  have he : Real.exp (-logMeshStep T h)<1 := by
    rw [Real.exp_lt_one_iff]; linarith
  have hp : 0<1-logMeshNode T h j := by
    simpa only [logMeshNode,sub_sub_cancel] using Real.exp_pos (-(j:ℝ)*logMeshStep T h)
  have hd : 0<logMeshNode T h (j+1)-logMeshNode T h j := by
    rw [logMeshNode_sub]
    exact mul_pos hp (by linarith)
  linarith

lemma logMeshNode_mem {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    {j : ℕ} (hj : j≤logMeshCount T h) : logMeshNode T h j∈Set.Icc 0 T := by
  have hm := (logMeshNode_strictMono hT0 hT1 hh).monotone
  constructor
  · simpa only [logMeshNode_zero] using hm (Nat.zero_le j)
  · simpa only [logMeshNode_last hT0 hT1 hh] using hm hj

end LogConcaveSampling.Quadrature

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
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace NNReal

namespace JetCalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma jet_finRange_eq_iteratedFDeriv {n : ℕ} {f : E → ℝ}
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (v : Fin n → E) (x : E) :
    jet v (List.finRange n) f x=iteratedFDeriv ℝ n f x v := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [List.finRange_succ]
    simp only [jet,jet_map]
    have he : jet (v ∘ Fin.succ) (List.finRange n) f=fun z => iteratedFDeriv ℝ n f z (Fin.tail v) :=
      funext (fun z => ih _ z)
    rw [he,(hf.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n) x).iteratedFDeriv_succ_apply_left']
    rfl
end JetCalculus

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
namespace LogConcaveSampling
open Set Function
open scoped Classical BigOperators RealInnerProductSpace NNReal

namespace JetCalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma time_deriv_spatial_jet {ι : Type*} {A : ℝ × E → ℝ}
    (hA : ContDiff ℝ (⊤:ℕ∞) A) (v : ι → E) (l : List ι) (t : ℝ) (y : E) :
    HasDerivAt (fun u => jet v l (fun z => A (u,z)) y)
      (jet v l (fun z => dir (1,0) A (t,z)) y) t := by
  let J := jet (fun i => (0,v i)) l A
  have hJ := smooth_jet hA (fun i => (0,v i)) l
  have he : (fun u => jet v l (fun z => A (u,z)) y)=fun u => J (u,y) := by
    funext u
    exact congrFun (jet_right_slice_at (fun z => hA.contDiffAt) v l) y
  rw [he]
  have hj := ((hJ.differentiable (by simp) (t,y)).hasFDerivAt).comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
  have hd : jet v l (fun z => dir (1,0) A (t,z)) y=dir (1,0) J (t,y) := by
    rw [jet_right_slice_at (fun z => (smooth_dir hA (1,0)).contDiffAt),jet_dir hA]
  exact hd.symm ▸ hj
end JetCalculus

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_Basis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set Polynomial
open scoped BigOperators

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def interpolation (u : I → ℝ) (f : I → E) (t : ℝ) : E :=
  ∑i,basis u i t • f i

lemma basis_continuous (u : I → ℝ) (i : I) : Continuous (basis u i) :=
  Polynomial.continuous _

lemma exists_basis_budget (u : I → ℝ) :
    ∃C : ℝ,1≤C ∧ ∀t∈Icc (0:ℝ) 1,∑i,|basis u i t|≤C := by
  have hc : Continuous (fun t => ∑i,|basis u i t|) :=
    continuous_finsetSum _ (fun i _ => (basis_continuous u i).abs)
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 1,le_max_right _ _,fun t ht => ?_⟩
  have hn : 0≤∑i,|basis u i t| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hh : (∑i,|basis u i t|)≤C := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg hn] using hC t ht
  exact hh.trans (le_max_left _ _)
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set
open scoped BigOperators

variable {I Ω E : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ν : Measure Ω} [SFinite ν]

lemma weights_abs_bound (u : I → ℝ) {C θ : ℝ} (hθ0 : 0≤θ) (hθ1 : θ≤1)
    (hC : ∀t∈Icc (0:ℝ) 1,∑i,|basis u i t|≤C) :
    ∑i,|weight u i 0 θ|≤(Fintype.card I:ℝ)*C*θ := by
  have hb (i : I) : |weight u i 0 θ|≤C*θ := by
    have hw := intervalIntegral.norm_integral_le_of_norm_le_const (a:=0) (b:=θ)
      (f:=basis u i) (C:=C) (fun t ht => by
        rw [uIoc_of_le hθ0] at ht
        have hc := (Finset.single_le_sum (fun j _ => abs_nonneg (basis u j t)) (Finset.mem_univ i)).trans
          (hC t ⟨ht.1.le,ht.2.trans hθ1⟩)
        simpa only [Real.norm_eq_abs] using hc)
    simpa only [weight,Real.norm_eq_abs,sub_zero,abs_of_nonneg hθ0] using hw
  calc
    _ ≤ ∑_i : I,C*θ := Finset.sum_le_sum (fun i _ => hb i)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

def cellQuadrature (u : I → ℝ) (v : I → E) (ℓ θ : ℝ) : E :=
  ∑i,(ℓ*weight u i 0 θ) • v i

end LogConcaveSampling.Quadrature

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_CompositeAngle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory
open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
lemma compositeAngle_mem {N : ℕ} {u : I → ℝ} (hu : ∀i,u i∈Icc (0:ℝ) 1)
    (i : Fin N × I) (c : Fin N) : compositeAngle u i c∈Icc (0:ℝ) 1 := by
  unfold compositeAngle
  split_ifs <;> simp_all

lemma compositeWeight_budget {N : ℕ} {u : I → ℝ} (hu : ∀i,u i∈Icc (0:ℝ) 1)
    {ℓ : Fin N → ℝ} (hℓ : ∀c,0≤ℓ c) (hsum : (∑c,ℓ c)≤1)
    {C : ℝ} (hC : 0≤C) (hbasis : ∀t∈Icc (0:ℝ) 1,∑j,|basis u j t|≤C)
    (i : Fin N × I) : ∑j,|compositeWeight u ℓ i j|≤(Fintype.card I:ℝ)*C := by
  rw [Fintype.sum_prod_type]
  have hc (c : Fin N) : ∑j,|compositeWeight u ℓ i (c,j)|≤ℓ c*((Fintype.card I:ℝ)*C) := by
    simp only [compositeWeight,abs_mul,abs_of_nonneg (hℓ c),←Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (hℓ c)
    have ht := compositeAngle_mem hu i c
    exact (weights_abs_bound u ht.1 ht.2 hbasis).trans
      (mul_le_of_le_one_right (mul_nonneg (Nat.cast_nonneg _) hC) ht.2)
  calc
    _ ≤ ∑c,ℓ c*((Fintype.card I:ℝ)*C) := Finset.sum_le_sum (fun c _ => hc c)
    _ = (∑c,ℓ c)*((Fintype.card I:ℝ)*C) := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_of_le_one_left (mul_nonneg (Nat.cast_nonneg _) hC) hsum

end LogConcaveSampling.Quadrature

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
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

lemma probabilityNodes_mem {n : ℕ} (hn : 0<n) (i : Fin (n+1)) : probabilityNodes n i∈Icc (0:ℝ) 1 := by
  have hp : (0:ℝ)<n := by exact_mod_cast hn
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hp.le
  · apply (div_le_iff₀ hp).mpr
    simp only [one_mul]
    exact_mod_cast Nat.le_of_lt_succ i.2

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators

lemma probabilityCellLength_pos {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (c : Fin (logMeshCount T h)) : 0<probabilityCellLength T h c :=
  sub_pos.mpr (logMeshNode_strictMono hT0 hT1 hh (Nat.lt_succ_self _))

lemma probabilityCellLength_sum {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h) :
    (∑c,probabilityCellLength T h c)=T := by
  unfold probabilityCellLength
  rw [Fin.sum_univ_eq_sum_range (fun j => logMeshNode T h (j+1)-logMeshNode T h j),
    Finset.sum_range_sub,logMeshNode_last hT0 hT1 hh,
    logMeshNode_zero,sub_zero]

lemma probabilityNodeTime_mem {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    {n : ℕ} (hn : 0<n) (i : ProbabilityNode T h n) : probabilityNodeTime T h n i∈Icc 0 T := by
  have ha := logMeshNode_mem hT0 hT1 hh i.1.2.le
  have hb := logMeshNode_mem hT0 hT1 hh (Nat.succ_le_of_lt i.1.2)
  have hu := probabilityNodes_mem hn i.2
  have hl := (probabilityCellLength_pos hT0 hT1 hh i.1).le
  have hc := mul_le_mul_of_nonneg_left hu.2 hl
  have h0 := mul_nonneg hl hu.1
  dsimp only [probabilityNodeTime,probabilityCellLength] at *
  rcases ha with ⟨ha0,haT⟩
  rcases hb with ⟨hb0,hbT⟩
  simp only [Nat.succ_eq_add_one,mul_one] at hbT hc
  constructor <;> linarith

lemma probabilityWeight_budget (n : ℕ) (hn : 0<n) :
    ∃A : ℝ,0≤A ∧ ∀{T h : ℝ},0<T → T<1 → 0<h →
      ∀i : ProbabilityNode T h n,∑j,|probabilityWeight T h n i j|≤A := by
  obtain ⟨C,hC,hC'⟩ := exists_basis_budget (probabilityNodes n)
  refine ⟨(Fintype.card (Fin (n+1)):ℝ)*C,by positivity,?_⟩
  intro T h hT0 hT1 hh i
  exact compositeWeight_budget (probabilityNodes_mem hn)
    (fun c => (probabilityCellLength_pos hT0 hT1 hh c).le)
    (by rw [probabilityCellLength_sum hT0 hT1 hh]; exact hT1.le)
    (by linarith) hC' i

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators NNReal

def probabilityPicard {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r T h : ℝ) (n N : ℕ) : Point d → ProbabilityNode T h n → Point d :=
  nodes (probabilityWeight T h n)
    (fun j => probabilityMeanVelocity F x r (probabilityNodeTime T h n j))
    (fun y _ => y) N

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators NNReal

lemma harmonicWeight_budget (n : ℕ) (hn : 0<n) :
    ∃A : ℝ≥0,∀z : ℝ,0≤z → z≤1 → ∀i,∑j,|harmonicWeight n z i j|≤A := by
  obtain ⟨C,hC,hC'⟩ := exists_basis_budget (probabilityNodes n)
  have hC0 : 0≤C := by linarith
  refine ⟨⟨(n+1:ℕ)*C,by positivity⟩,?_⟩
  intro z hz hz1 i
  have hi := probabilityNodes_mem hn i
  have hb (j : Fin (n+1)) : |harmonicWeight n z i j|≤C := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=0) (b:=probabilityNodes n i)
      (f:=fun v => Real.sin (z*(probabilityNodes n i-v))*basis (probabilityNodes n) j v)
      (C:=C) (fun v hv => by
        rw [uIoc_of_le hi.1] at hv
        rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
        have he := (Finset.single_le_sum (fun k _ => abs_nonneg (basis (probabilityNodes n) k v))
          (Finset.mem_univ j)).trans (hC' v ⟨hv.1.le,hv.2.trans hi.2⟩)
        exact (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)).trans
          (by simpa only [one_mul] using he))
    rw [sub_zero,abs_of_nonneg hi.1] at hh
    dsimp only [harmonicWeight]
    rw [abs_mul,abs_of_nonneg hz]
    have hh' : |∫v in 0..probabilityNodes n i,
        Real.sin (z*(probabilityNodes n i-v))*basis (probabilityNodes n) j v|≤C*probabilityNodes n i := by
      simpa only [Real.norm_eq_abs] using hh
    have he : |∫v in 0..probabilityNodes n i,
        Real.sin (z*(probabilityNodes n i-v))*basis (probabilityNodes n) j v|≤C :=
      hh'.trans (mul_le_of_le_one_right hC0 hi.2)
    exact (mul_le_mul_of_nonneg_left he hz).trans (mul_le_of_le_one_left hC0 hz1)
  calc
    _ ≤ ∑j : Fin (n+1),C := Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; norm_cast

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

variable [NormedSpace ℝ E] [Fintype I]

def stepLp (w : I → I → ℝ) (φ : I → E → E) {K : ℝ≥0}
    (hφ : ∀i,LipschitzWith K (φ i)) (a z : I → Lp E 2 ν) : I → Lp E 2 ν :=
  step w (fun j => nodeLp (hφ j)) a z

end LogConcaveSampling.FinitePicard

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_NodePolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory Polynomial
open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

def zeroHermitePolynomial (u : I → ℝ) (i₀ : I) (v : I → ℝ) : ℝ[X] :=
  ∑i,C (v i)*zeroHermiteBasis u i₀ i

end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory Polynomial
open scoped BigOperators

variable {I E Ω : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace Ω] {μ : Measure Ω}

def zeroHermiteInterpolation (u : I → ℝ) (i₀ : I) (v : I → E) (t : ℝ) : E :=
  ∑i,(zeroHermiteBasis u i₀ i).eval t • v i

def zeroHermiteAction (u : I → ℝ) (i₀ : I) (v : I → E) (t : ℝ) : E :=
  ∑i,(zeroHermiteRegularized u i₀ i).eval t • v i

end LogConcaveSampling.Quadrature

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_BasisDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory Polynomial
open scoped BigOperators

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def derivativeInterpolation (u : I → ℝ) (v : I → E) (t : ℝ) : E :=
  ∑i,basisDerivative u i t • v i

end LogConcaveSampling.Quadrature

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_Picard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open Set MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators NNReal

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def picard {I : Type*} [Fintype I] (w : I → I → ℝ)
    (φ : I → MeanTree X d → MeanTree X d) (a : I → MeanTree X d) :
    ℕ → I → MeanTree X d
  | 0 => a
  | k+1 => fun i => add (a i) (sumFamily (fun j => scale (w i j) (φ j (picard w φ a k j))))

def probability (r T h : ℝ) (n N : ℕ) (s : ProbabilityNode T h n)
    (x y : MeanTree X d) (i : ProbabilityNode T h n) : MeanTree X d :=
  picard (reanchorWeight (probabilityWeight T h n) s)
    (fun j E => scale (-r) (conditional r (probabilityNodeTime T h n j) x E))
    (fun _ => y) N i

def harmonic (r ρ z : ℝ) (n N : ℕ) (x y g : MeanTree X d) (i : Fin (n+1)) : MeanTree X d :=
  picard (harmonicWeight n z) (fun _ E => scale ρ (scale (-r) (conditional r ρ x E)))
    (fun j => add (scale (Real.cos (z*probabilityNodes n j)) y)
      (scale (Real.sin (z*probabilityNodes n j)) g)) N i

def kernelCorrection (r T h v : ℝ) (n N : ℕ) (s e : ProbabilityNode T h n)
    (x y g : MeanTree X d) : MeanTree X d :=
  let b := probability r T h n N e x y s
  let w := harmonic r (probabilityNodeTime T h n s) v n N x b g (Fin.last n)
  sumFamily (fun j => scale (reanchorWeight (probabilityWeight T h n) s e j)
    (scale (-r) (conditional r (probabilityNodeTime T h n j) x
      (probability r T h n N s x w j))))

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open Set MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators NNReal

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def kernelAction (r T h ψ : ℝ) (n m N : ℕ) (s e : ProbabilityNode T h n)
    (x y g : MeanTree X d) : MeanTree X d :=
  sumFamily (fun j : Fin (m+1) => scale (derivativeWeight (angleNodes m) j/ψ)
    (kernelCorrection r T h (ψ*angleNodes m j) n N s e x y g))

def kernelQuadrature (r T h ψ : ℝ) (n m N : ℕ) (e : ProbabilityNode T h n)
    (w : ProbabilityNode T h n → ℝ) (x y g : MeanTree X d) : MeanTree X d :=
  sumFamily (fun j => scale (w j) (kernelAction r T h ψ n m N j e x y g))

def velocity (r T h ψ s : ℝ) (n m N : ℕ) (e : ProbabilityNode T h (n+1))
    (x : MeanTree X d) (p : MeanTree X d × MeanTree X d) : MeanTree X d × MeanTree X d :=
  (scale (-(r*s)⁻¹) (kernelQuadrature r T h ψ (n+1) m N e (terminalQuadratureWeight T h n) x p.1 p.2),
    scale s⁻¹ (add (conditional r T x p.1) (scale (-1) (mean r x))))

def pairEval (F : Point d → ℝ) (p : MeanTree X d × MeanTree X d) (z : X) : Point d × Point d :=
  (eval F p.1 z,eval F p.2 z)

def pairPicard {I : Type*} [Fintype I] (w : I → I → ℝ)
    (φ : MeanTree X d × MeanTree X d → MeanTree X d × MeanTree X d)
    (a : MeanTree X d × MeanTree X d) : ℕ → I → MeanTree X d × MeanTree X d
  | 0 => fun _ => a
  | k+1 => fun i =>
    (add a.1 (sumFamily (fun j => scale (w i j) (φ (pairPicard w φ a k j)).1)),
     add a.2 (sumFamily (fun j => scale (w i j) (φ (pairPicard w φ a k j)).2)))

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open Set MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators NNReal

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def centeringStates (r T h ψ s : ℝ) (n m N nc Nc : ℕ)
    (e : ProbabilityNode T h (n+1)) (x y g : MeanTree X d) (i : Fin (nc+1)) :
    MeanTree X d × MeanTree X d :=
  pairPicard (centeringWeight nc) (velocity r T h ψ s n m N e x) (y,g) Nc i

def meanCircuit (r T h ψ s : ℝ) (n m N nc Nc : ℕ)
    (e : ProbabilityNode T h (n+1)) (x y g : MeanTree X d) : MeanTree X d :=
  add (scale s g) (sumFamily (fun j => scale (Quadrature.weight (probabilityNodes nc) j 0 1)
    (conditional r T x (centeringStates r T h ψ s n m N nc Nc e x y g j).1)))

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma centers_mean (P : ℝ → (X → Point d) → Prop) (r : ℝ) (E : MeanTree X d)
    (hr : P r (base E)) (hE : centers P E) : centers P (mean r E) := by
  intro i
  exact ⟨hr,hE⟩

lemma centers_conditional (P : ℝ → (X → Point d) → Prop) (r ρ : ℝ) (x y : MeanTree X d)
    (hr : P (r*Real.sqrt (1-ρ^2)) (fun z => base x z+(r*ρ) • base y z))
    (hx : centers P x) (hy : centers P y) : centers P (conditional r ρ x y) := by
  apply centers_mean
  · simpa only [base_add,base_scale] using hr
  · exact (centers_add _ _ _).2 ⟨hx,(centers_scale _ _ _).2 hy⟩

lemma centers_sumFin (P : ℝ → (X → Point d) → Prop) (k : ℕ) (E : Fin k → MeanTree X d)
    (h : ∀i,centers P (E i)) : centers P (sumFin k E) := by
  induction k with
  | zero => exact centers_zero _
  | succ k ih => exact (centers_add _ _ _).2 ⟨h 0,ih _ (fun i => h i.succ)⟩

lemma centers_sumFamily {I : Type*} [Fintype I] (P : ℝ → (X → Point d) → Prop)
    (E : I → MeanTree X d) (h : ∀i,centers P (E i)) : centers P (sumFamily E) :=
  centers_sumFin P _ _ (fun _ => h _)

lemma picard_shape {I : Type*} [Fintype I] (P : ℝ → (X → Point d) → Prop)
    (w : I → I → ℝ) (φ : I → MeanTree X d → MeanTree X d) (a : I → MeanTree X d)
    (ha : ∀i,centers P (a i))
    (hφ : ∀i j E,base E=base (a j) → centers P E →
      base (φ i E)=(fun _ => 0) ∧ centers P (φ i E)) (N : ℕ) (i : I) :
    base (picard w φ a N i)=base (a i) ∧ centers P (picard w φ a N i) := by
  induction N generalizing i with
  | zero => exact ⟨rfl,ha i⟩
  | succ N ih =>
    have hc (j : I) := hφ j j (picard w φ a N j) (ih j).1 (ih j).2
    constructor
    · funext z
      simp only [picard,base_add,base_sumFamily,base_scale,(hc _).1,smul_zero,Finset.sum_const_zero,add_zero]
    · apply (centers_add _ _ _).2
      refine ⟨ha i,centers_sumFamily _ _ ?_⟩
      intro j
      exact (centers_scale _ _ _).2 (hc j).2
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory Quadrature
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

@[simp] lemma centersBound_zero (A : ℝ) : centersBound A (zero : MeanTree X d) := by simp [zero]
@[simp] lemma centersBound_scale (A s : ℝ) (E : MeanTree X d) :
    centersBound A (scale s E) ↔ centersBound A E := by cases E; rfl
@[simp] lemma centersBound_add (A : ℝ) (E D : MeanTree X d) :
    centersBound A (add E D) ↔ centersBound A E ∧ centersBound A D := by
  cases E with | node k b hb a r C =>
    cases D with | node l e he c s B =>
      simp only [add,centersBound,Fin.forall_fin_add]
      simp
@[simp] lemma centersBound_mean (A r : ℝ) (E : MeanTree X d) :
    centersBound A (mean r E) ↔ weight E≤A ∧ centersBound A E := by
  simp [mean,centersBound]

end LogConcaveSampling.MeanTree

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

def terminalMean (d : ℕ) (r σ : ℝ) :
    Program (Point d × (Fin 2 → Point d)) d 1 (Point d) :=
  oneQuery (fun p => p.1 + r • p.2 0) (by fun_prop)
    (fun p => p.2.2 + σ • p.1.2 1) (by fun_prop)

end LogConcaveSampling.SeedCompiler

end
end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_Law
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.EulerGeometry
open MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical NNReal

variable {d : ℕ}

lemma measurable_iterate_map {T : Point d → Point d} (hT : Measurable T)
    (σ : ℝ) (n : ℕ) (x : Point d) :
    Measurable (fun g : PiLp 2 (fun _ : Fin n => Point d) => iterate T σ n x g.ofLp) := by
  have h (n : ℕ) : Measurable (iterate T σ n x) := by
    induction n with
    | zero => exact measurable_const
    | succ n ih =>
      exact (hT.comp (ih.comp (Measurable.of_eval (fun index => measurable_pi_apply index.castSucc)))).add
        ((measurable_pi_apply (Fin.last n)).const_smul σ)
  exact (h n).comp (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin n => Point d)).measurable

def law (T : Point d → Point d) (σ : ℝ) (n : ℕ) (x : Point d) : Measure (Point d) :=
  (stdGaussian (PiLp 2 (fun _ : Fin n => Point d))).map (fun g => iterate T σ n x g.ofLp)

lemma law_probability {T : Point d → Point d} (hT : Measurable T) (σ : ℝ) (n : ℕ) (x : Point d) :
    IsProbabilityMeasure (law T σ n x) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_iterate_map hT σ n x).aemeasurable).mpr inferInstance

end LogConcaveSampling.EulerGeometry

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

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling

def transcriptRejection {d : ℕ} : (q : ℕ) →
    ((Fin q → Point d × ℝ) × (Fin q → ℝ)) → Point d
  | 0, _ => 0
  | n+1, p =>
      if (p.1 (Fin.last n)).2 ≤ Real.exp (-(p.2 (Fin.last n))+
          gaussianProposalPotential d (p.1 (Fin.last n)).1) then (p.1 (Fin.last n)).1
      else transcriptRejection n (fun i => p.1 i.castSucc,fun i => p.2 i.castSucc)

@[fun_prop] lemma measurable_transcriptRejection (d q : ℕ) :
    Measurable (transcriptRejection (d := d) q) := by
  induction q with
  | zero => exact measurable_const
  | succ n ih =>
      apply Measurable.ite
      · apply measurableSet_le
        · fun_prop
        · exact Real.measurable_exp.comp (((measurable_pi_apply (Fin.last n)).comp measurable_snd).neg.add
            ((gaussianProposalPotential_admissible d).smooth.continuous.measurable.comp
            (((measurable_pi_apply (Fin.last n)).comp measurable_fst).fst)))
      · fun_prop
      · exact ih.comp ((Measurable.of_eval fun index =>
          (measurable_pi_apply index.castSucc).comp measurable_fst).prodMk
          (Measurable.of_eval fun index => (measurable_pi_apply index.castSucc).comp measurable_snd))

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_LowerBounds_RotationIsometry
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
open Matrix WithLp ProbabilityTheory
open scoped RealInnerProductSpace

def rotationIsometry {d : ℕ} (O : Rotations d) : Point d ≃ₗᵢ[ℝ] Point d :=
  Unitary.linearIsometryEquiv
    (Unitary.map (StarMonoidHom.ofClass (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ))) O)

@[simp] theorem rotationIsometry_apply {d : ℕ} (O : Rotations d) (x : Point d) :
    rotationIsometry O x = toLp 2 ((O : Matrix (Fin d) (Fin d) ℝ) *ᵥ ofLp x) := rfl

def rotationFromIsometry {d : ℕ} (T : Point d ≃ₗᵢ[ℝ] Point d) : Rotations d :=
  Unitary.map (StarMonoidHom.ofClass
    (A := Point d →L[ℝ] Point d) (B := Matrix (Fin d) (Fin d) ℝ)
    ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).symm.toStarAlgHom))
    (Unitary.linearIsometryEquiv.symm T)

@[simp] theorem rotationIsometry_from {d : ℕ} (T : Point d ≃ₗᵢ[ℝ] Point d) :
    rotationIsometry (rotationFromIsometry T) = T := by
  apply Unitary.linearIsometryEquiv.symm.injective
  simp only [rotationIsometry, MulEquiv.symm_apply_apply]
  apply Subtype.ext
  change (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ))
    ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).symm (T : Point d →L[ℝ] Point d)) = _
  exact (Matrix.toEuclideanCLM).apply_symm_apply _

@[simp] theorem rotationIsometry_mul {d : ℕ} (O P : Rotations d) (x : Point d) :
    rotationIsometry (O * P) x = rotationIsometry O (rotationIsometry P x) := by
  simp only [rotationIsometry_apply]
  change toLp 2 (((O : Matrix (Fin d) (Fin d) ℝ) * (P : Matrix (Fin d) (Fin d) ℝ)) *ᵥ ofLp x) = _
  rw [← Matrix.mulVec_mulVec]

@[fun_prop] theorem continuous_rotation_apply {d : ℕ} :
    Continuous (fun p : Rotations d × Point d => rotationIsometry p.1 p.2) := by
  simp only [rotationIsometry_apply]
  fun_prop

instance rotationHaar_rightInvariant (d : ℕ) : (rotationHaar d).IsMulRightInvariant := by
  constructor
  intro P
  have : IsProbabilityMeasure ((rotationHaar d).map (· * P)) :=
    (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability))
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace
    ((rotationHaar d).map (· * P)) (rotationHaar d)
  have hm := congrArg (fun μ : Measure (Rotations d) => μ Set.univ) h
  simp only [measure_univ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_one] at hm
  have hc : (((rotationHaar d).map (· * P)).haarScalarFactor (rotationHaar d)) = 1 := by
    exact ENNReal.coe_injective hm.symm
  rw [hc, one_smul] at h
  exact h

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound
open ProbabilityTheory

@[simp] theorem rotationIsometry_one {d : ℕ} (x : Point d) :
    rotationIsometry (1 : Rotations d) x = x := by
  simp [rotationIsometry_apply]

@[simp] theorem rotationIsometry_inv_apply {d : ℕ} (O : Rotations d) (x : Point d) :
    rotationIsometry O⁻¹ x = (rotationIsometry O).symm x := by
  apply (rotationIsometry O).injective
  rw [← rotationIsometry_mul, mul_inv_cancel, rotationIsometry_one,
    LinearIsometryEquiv.apply_symm_apply]

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound
open scoped RealInnerProductSpace

def sphereSection {d : ℕ} (w v : Point d) : Rotations d :=
  rotationFromIsometry (Submodule.reflection (ℝ ∙ (w-v))ᗮ)

@[simp] theorem sphereSection_apply {d : ℕ} (w v x : Point d) :
    rotationIsometry (sphereSection w v) x =
      x - (2 * (inner ℝ (w-v) x / ‖w-v‖^2)) • (w-v) := by
  rw [sphereSection, rotationIsometry_from, Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply]
  simp only [neg_sub, two_smul, two_mul, add_smul, RCLike.ofReal_real_eq_id, id_eq]

theorem sphereSection_sends {d : ℕ} {w v : Point d} (h : ‖w‖ = ‖v‖) :
    rotationIsometry (sphereSection w v) w = v := by
  rw [sphereSection, rotationIsometry_from]
  exact Submodule.reflection_sub h

end LogConcaveSampling.LowerBound

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_LowerBounds_RevealRotation
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
open ProbabilityTheory
open scoped RealInnerProductSpace

def subspaceStabilizer {d : ℕ} (E : Submodule ℝ (Point d)) : Subgroup (Rotations d) where
  carrier := {O | ∀ x ∈ E, rotationIsometry O x = x}
  one_mem' := by intro x _; exact rotationIsometry_one x
  mul_mem' := by
    intro O P hO hP x hx
    rw [rotationIsometry_mul, hP x hx, hO x hx]
  inv_mem' := by
    intro O hO x hx
    rw [rotationIsometry_inv_apply]
    exact (rotationIsometry O).symm_apply_eq.mpr (hO x hx).symm

@[simp] theorem mem_subspaceStabilizer {d : ℕ} (E : Submodule ℝ (Point d)) (O : Rotations d) :
    O ∈ subspaceStabilizer E ↔ ∀ x ∈ E, rotationIsometry O x = x := Iff.rfl

theorem subspaceStabilizer_isClosed {d : ℕ} (E : Submodule ℝ (Point d)) :
    IsClosed (subspaceStabilizer E : Set (Rotations d)) := by
  have he : (subspaceStabilizer E : Set (Rotations d)) =
      ⋂ x : E, {O : Rotations d | rotationIsometry O x = x} := by
    ext O
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨fun h x => h x x.property, fun h x hx => h ⟨x,hx⟩⟩
  rw [he]
  exact isClosed_iInter (fun _ => isClosed_eq (by fun_prop) continuous_const)

instance subspaceStabilizer_compactSpace {d : ℕ} (E : Submodule ℝ (Point d)) :
    CompactSpace (subspaceStabilizer E) :=
  isCompact_iff_compactSpace.mp (subspaceStabilizer_isClosed E).isCompact

instance subspaceStabilizer_secondCountable {d : ℕ} (E : Submodule ℝ (Point d)) :
    SecondCountableTopology (subspaceStabilizer E) :=
  (Topology.IsEmbedding.subtypeVal (p := fun O : Rotations d =>
    O ∈ subspaceStabilizer E)).isInducing.secondCountableTopology

instance subspaceStabilizer_measurableMul {d : ℕ} (E : Submodule ℝ (Point d)) :
    MeasurableMul₂ (subspaceStabilizer E) := ⟨continuous_mul.measurable⟩

instance subspaceStabilizer_measurableInv {d : ℕ} (E : Submodule ℝ (Point d)) :
    MeasurableInv (subspaceStabilizer E) := ⟨continuous_inv.measurable⟩

def subspaceHaar {d : ℕ} (E : Submodule ℝ (Point d)) : Measure (subspaceStabilizer E) :=
  Measure.haarMeasure (⟨⟨Set.univ, isCompact_univ⟩, by simp⟩ :
    PositiveCompacts (subspaceStabilizer E))

instance subspaceHaar_probability {d : ℕ} (E : Submodule ℝ (Point d)) :
    IsProbabilityMeasure (subspaceHaar E) := ⟨Measure.haarMeasure_self⟩

instance subspaceHaar_isHaar {d : ℕ} (E : Submodule ℝ (Point d)) :
    (subspaceHaar E).IsHaarMeasure := by
  unfold subspaceHaar
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

instance subspaceHaar_rightInvariant {d : ℕ} (E : Submodule ℝ (Point d)) :
    (subspaceHaar E).IsMulRightInvariant := by
  constructor
  intro P
  have : IsProbabilityMeasure ((subspaceHaar E).map (· * P)) :=
    (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability))
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace
    ((subspaceHaar E).map (· * P)) (subspaceHaar E)
  have hm := congrArg (fun μ : Measure (subspaceStabilizer E) => μ Set.univ) h
  simp only [measure_univ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_one] at hm
  have hc : ((subspaceHaar E).map (· * P)).haarScalarFactor (subspaceHaar E) = 1 :=
    ENNReal.coe_injective hm.symm
  rw [hc, one_smul] at h
  exact h

lemma stabilizer_map_orthogonal {d : ℕ} (E : Submodule ℝ (Point d))
    (O : subspaceStabilizer E) {x : Point d} (hx : x ∈ Eᗮ) :
    rotationIsometry O.1 x ∈ Eᗮ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  have hf := O.property y hy
  rw [← hf, LinearIsometryEquiv.inner_map_map]
  exact E.inner_right_of_mem_orthogonal hy hx

def complementIsometry {d : ℕ} (E : Submodule ℝ (Point d))
    (O : subspaceStabilizer E) : Eᗮ ≃ₗᵢ[ℝ] Eᗮ where
  toFun x := ⟨rotationIsometry O.1 x, stabilizer_map_orthogonal E O x.property⟩
  invFun x := ⟨rotationIsometry (O⁻¹).1 x, stabilizer_map_orthogonal E (O⁻¹) x.property⟩
  left_inv x := by
    apply Subtype.ext
    change rotationIsometry (O.1)⁻¹ (rotationIsometry O.1 (x : Point d)) = (x : Point d)
    rw [rotationIsometry_inv_apply, LinearIsometryEquiv.symm_apply_apply]
  right_inv x := by
    apply Subtype.ext
    change rotationIsometry O.1 (rotationIsometry (O.1)⁻¹ (x : Point d)) = (x : Point d)
    rw [rotationIsometry_inv_apply, LinearIsometryEquiv.apply_symm_apply]
  map_add' x y := by apply Subtype.ext; exact map_add (rotationIsometry O.1) (x : Point d) (y : Point d)
  map_smul' c x := by apply Subtype.ext; exact map_smul (rotationIsometry O.1) c (x : Point d)
  norm_map' x := (rotationIsometry O.1).norm_map x

@[simp] theorem complementIsometry_apply_coe {d : ℕ} (E : Submodule ℝ (Point d))
    (O : subspaceStabilizer E) (x : Eᗮ) :
    (complementIsometry E O x : Point d) = rotationIsometry O.1 x := rfl

@[fun_prop] theorem continuous_complementIsometry_apply {d : ℕ} (E : Submodule ℝ (Point d)) :
    Continuous (fun p : subspaceStabilizer E × Eᗮ => complementIsometry E p.1 p.2) := by
  have h₁ : Continuous (fun p : subspaceStabilizer E × Eᗮ => (p.1.1, (p.2 : Point d))) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  have h₂ := (continuous_rotation_apply (d := d)).comp h₁
  exact h₂.subtype_mk _

lemma sphereSection_mem_subspaceStabilizer {d : ℕ} (E : Submodule ℝ (Point d))
    {x y : Point d} (hx : x ∈ Eᗮ) (hy : y ∈ Eᗮ) :
    sphereSection x y ∈ subspaceStabilizer E := by
  intro z hz
  rw [sphereSection_apply, E.inner_left_of_mem_orthogonal hz (Eᗮ.sub_mem hx hy)]
  simp

def complementSection {d : ℕ} (E : Submodule ℝ (Point d)) (x y : Eᗮ) :
    subspaceStabilizer E :=
  ⟨sphereSection x y, sphereSection_mem_subspaceStabilizer E x.property y.property⟩

lemma complementSection_sends {d : ℕ} (E : Submodule ℝ (Point d)) {x y : Eᗮ}
    (h : ‖x‖ = ‖y‖) : complementIsometry E (complementSection E x y) x = y := by
  apply Subtype.ext
  exact sphereSection_sends h

@[simp] theorem complementIsometry_mul {d : ℕ} (E : Submodule ℝ (Point d))
    (O P : subspaceStabilizer E) (x : Eᗮ) :
    complementIsometry E (O * P) x = complementIsometry E O (complementIsometry E P x) := by
  apply Subtype.ext
  exact rotationIsometry_mul O.1 P.1 x

@[simp] theorem complementIsometry_inv {d : ℕ} (E : Submodule ℝ (Point d))
    (O : subspaceStabilizer E) (x : Eᗮ) :
    complementIsometry E (O⁻¹) x = (complementIsometry E O).symm x := rfl

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound
open scoped RealInnerProductSpace

lemma stabilizer_sup_line {d : ℕ} (E : Submodule ℝ (Point d)) (w : Point d)
    {O : Rotations d} (hE : O ∈ subspaceStabilizer E) (hw : rotationIsometry O w = w) :
    O ∈ subspaceStabilizer (E ⊔ ℝ ∙ w) := by
  intro x hx
  rcases Submodule.mem_sup.mp hx with ⟨a,ha,b,hb,rfl⟩
  rcases Submodule.mem_span_singleton.mp hb with ⟨c,rfl⟩
  rw [map_add, hE a ha, map_smul, hw]

def residualInclusion {d : ℕ} (E : Submodule ℝ (Point d)) (w : Point d)
    (O : subspaceStabilizer (E ⊔ ℝ ∙ w)) : subspaceStabilizer E :=
  ⟨O.1, fun x hx => O.property x ((show E ≤ E ⊔ ℝ ∙ w from le_sup_left) hx)⟩

@[fun_prop] theorem continuous_residualInclusion {d : ℕ}
    (E : Submodule ℝ (Point d)) (w : Point d) : Continuous (residualInclusion E w) := by
  exact continuous_subtype_val.subtype_mk _

@[simp] theorem residualInclusion_mul {d : ℕ} (E : Submodule ℝ (Point d)) (w : Point d)
    (O P : subspaceStabilizer (E ⊔ ℝ ∙ w)) :
    residualInclusion E w (O * P) = residualInclusion E w O * residualInclusion E w P := rfl

def complementCocycle {d : ℕ} (E : Submodule ℝ (Point d)) (w : Eᗮ)
    (P : subspaceStabilizer E) (v : Eᗮ) (hv : ‖v‖ = ‖w‖) :
    subspaceStabilizer (E ⊔ ℝ ∙ (w : Point d)) :=
  ⟨((complementSection E w (complementIsometry E P v))⁻¹ * P *
      complementSection E w v).1, by
    apply stabilizer_sup_line E w
    · exact ((complementSection E w (complementIsometry E P v))⁻¹ * P *
        complementSection E w v).property
    · have he : complementIsometry E
          ((complementSection E w (complementIsometry E P v))⁻¹ * P *
            complementSection E w v) w = w := by
        rw [complementIsometry_mul, complementIsometry_mul, complementSection_sends E hv.symm,
          complementIsometry_inv]
        apply (complementIsometry E _).symm_apply_eq.mpr
        symm
        apply complementSection_sends
        rw [LinearIsometryEquiv.norm_map, hv]
      exact congrArg Subtype.val he⟩

def revealComplement {d : ℕ} (E : Submodule ℝ (Point d)) (w : Eᗮ)
    (p : subspaceStabilizer E × subspaceStabilizer (E ⊔ ℝ ∙ (w : Point d))) :
    subspaceStabilizer E :=
  complementSection E w (complementIsometry E p.1 w) * residualInclusion E w p.2

end LogConcaveSampling.LowerBound

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_LowerBounds_PrefixSpace
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
namespace LowerBound

def prefixSpace (d k : ℕ) : Submodule ℝ (Point d) where
  carrier := {x | ∀ i : Fin d, k ≤ i.val → x i = 0}
  zero_mem' := by intro i _; rfl
  add_mem' := by intro x y hx hy i hi; simp [hx i hi, hy i hi]
  smul_mem' := by intro c x hx i hi; simp [hx i hi]

@[simp] theorem mem_prefixSpace {d k : ℕ} (x : Point d) :
    x ∈ prefixSpace d k ↔ ∀ i : Fin d, k ≤ i.val → x i = 0 := Iff.rfl

def coordinateVector {d : ℕ} (i : Fin d) : Point d := EuclideanSpace.single i 1

@[simp] theorem coordinateVector_apply {d : ℕ} (i j : Fin d) :
    coordinateVector i j = if j = i then 1 else 0 := by
  simp [coordinateVector, eq_comm]

@[simp] theorem coordinateVector_norm {d : ℕ} (i : Fin d) : ‖coordinateVector i‖ = 1 := by
  simp [coordinateVector]

@[simp] theorem inner_coordinateVector {d : ℕ} (i : Fin d) (x : Point d) :
    inner ℝ (coordinateVector i) x = x i := by
  simp [coordinateVector, EuclideanSpace.inner_single_left]

@[simp] theorem prefixSpace_zero (d : ℕ) : prefixSpace d 0 = ⊥ := by
  ext x
  simp only [mem_prefixSpace, zero_le, forall_true_left, Submodule.mem_bot]
  exact ⟨fun h => by ext i; exact h i, fun h i => by simp [h]⟩

lemma coordinateVector_orthogonal_prefix {d k : ℕ} (hk : k < d) :
    coordinateVector ⟨k,hk⟩ ∈ (prefixSpace d k)ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro y hy
  rw [inner_coordinateVector]
  exact hy ⟨k,hk⟩ le_rfl

end LowerBound
end LogConcaveSampling

namespace LogConcaveSampling.LowerBound
open ProbabilityTheory

instance subspaceHaar_invInvariant {d : ℕ} (E : Submodule ℝ (Point d)) :
    (subspaceHaar E).IsInvInvariant := by
  constructor
  have : IsProbabilityMeasure (subspaceHaar E).inv := by
    unfold Measure.inv
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace
    (subspaceHaar E).inv (subspaceHaar E)
  have hm := congrArg (fun μ : Measure (subspaceStabilizer E) => μ Set.univ) h
  simp only [measure_univ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_one] at hm
  have hc : (subspaceHaar E).inv.haarScalarFactor (subspaceHaar E) = 1 :=
    ENNReal.coe_injective hm.symm
  rw [hc, one_smul] at h
  exact h

def gaussianSection {d : ℕ} (E : Submodule ℝ (Point d)) (e : Eᗮ)
    (g : Point d) : subspaceStabilizer E :=
  complementSection E e (normalizedDirection e (Eᗮ.orthogonalProjectionOnto g))

def gaussianForward {d : ℕ} (E : Submodule ℝ (Point d)) (e : Eᗮ)
    (p : Point d × subspaceStabilizer (E ⊔ ℝ ∙ (e : Point d))) : subspaceStabilizer E :=
  gaussianSection E e p.1 * residualInclusion E e p.2

def gaussianBackward {d : ℕ} (E : Submodule ℝ (Point d)) (e w : Eᗮ)
    (p : Point d × subspaceStabilizer (E ⊔ ℝ ∙ (e : Point d))) : subspaceStabilizer E :=
  complementSection E e w * residualInclusion E e p.2 * (gaussianSection E e p.1)⁻¹

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound

def remainingHaar {d : ℕ} (E : Submodule ℝ (Point d)) : Measure (Rotations d) :=
  (subspaceHaar E).map Subtype.val

instance remainingHaar_probability {d : ℕ} (E : Submodule ℝ (Point d)) :
    IsProbabilityMeasure (remainingHaar E) := by
  unfold remainingHaar
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

def ambientBackward {d : ℕ} (E : Submodule ℝ (Point d)) (e w : Eᗮ)
    (p : Point d × Rotations d) : Rotations d :=
  (complementSection E e w).1 * p.2 * (gaussianSection E e p.1).1⁻¹

def prefixUnit {d k : ℕ} (hk : k < d) : (prefixSpace d k)ᗮ :=
  ⟨coordinateVector ⟨k,hk⟩, coordinateVector_orthogonal_prefix hk⟩

@[simp] lemma norm_prefixUnit {d k : ℕ} (hk : k < d) : ‖prefixUnit hk‖ = 1 := by
  exact coordinateVector_norm _

abbrev Frames (d : ℕ) := Rotations d × Rotations d

def frameCompletion {d : ℕ} (F : Frames d) (H : Rotations d) : Rotations d :=
  F.1 * H * F.2⁻¹

@[fun_prop] lemma measurable_frameCompletion {d : ℕ} :
    Measurable (fun p : Frames d × Rotations d => frameCompletion p.1 p.2) := by
  unfold frameCompletion
  fun_prop

def flagDirection {d k : ℕ} (hk : k < d) (x : Point d) : (prefixSpace d k)ᗮ :=
  normalizedDirection (prefixUnit hk) ((prefixSpace d k)ᗮ.orthogonalProjectionOnto x)

@[fun_prop] lemma measurable_flagDirection {d k : ℕ} (hk : k < d) :
    Measurable (flagDirection hk) := by
  exact (measurable_normalizedDirection _).comp (by fun_prop)

@[simp] lemma norm_flagDirection {d k : ℕ} (hk : k < d) (x : Point d) :
    ‖flagDirection hk x‖ = 1 := norm_normalizedDirection (norm_prefixUnit hk) _

def inverseFrameUpdate {d k : ℕ} (hk : k < d) (F : Frames d) (x g : Point d) : Frames d :=
  (F.1 * (complementSection (prefixSpace d k) (prefixUnit hk)
      (flagDirection hk (rotationIsometry F.1⁻¹ x))).1,
   F.2 * (gaussianSection (prefixSpace d k) (prefixUnit hk) (rotationIsometry F.2⁻¹ g)).1)

@[simp] lemma frameCompletion_swap {d : ℕ} (F : Frames d) (H : Rotations d) :
    frameCompletion F.swap H⁻¹ = (frameCompletion F H)⁻¹ := by
  simp [frameCompletion]; group

def forwardFrameUpdate {d k : ℕ} (hk : k < d) (F : Frames d) (y g : Point d) : Frames d :=
  (inverseFrameUpdate hk F.swap y g).swap

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound
open scoped RealInnerProductSpace

def frameSpace {d : ℕ} (O : Rotations d) (E : Submodule ℝ (Point d)) : Submodule ℝ (Point d) :=
  E.map (rotationIsometry O).toLinearEquiv.toLinearMap

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound

def extendFrame {d k : ℕ} (hk : k < d) (O : Rotations d) (x : Point d) : Rotations d :=
  O * (complementSection (prefixSpace d k) (prefixUnit hk)
    (flagDirection hk (rotationIsometry O⁻¹ x))).1

def filledObservation {d k : ℕ} (O : Rotations d) (x g : Point d) : Point d :=
  if (prefixSpace d k)ᗮ.orthogonalProjectionOnto (rotationIsometry O⁻¹ x) = 0 then g else x

@[fun_prop] lemma measurable_filledObservation {d k : ℕ} :
    Measurable (fun p : Rotations d × Point d × Point d => filledObservation (k := k) p.1 p.2.1 p.2.2) := by
  unfold filledObservation
  exact Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const) (by fun_prop) (by fun_prop)

end LogConcaveSampling.LowerBound

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_LowerBounds_FrameTransport
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

def frameTransport {d : ℕ} (F : Frames d) : Point d ≃ₗᵢ[ℝ] Point d :=
  rotationIsometry (frameCompletion F 1)

@[fun_prop] lemma measurable_frameTransport {d : ℕ} :
    Measurable (fun p : Frames d × Point d => frameTransport p.1 p.2) := by
  have continuous_completion : Continuous
      (fun pair : Frames d × Point d => frameCompletion pair.1 1) := by
    unfold frameCompletion
    exact (continuous_fst.fst.mul continuous_const).mul continuous_fst.snd.inv
  exact ((continuous_rotation_apply (d := d)).comp
    (continuous_completion.prodMk continuous_snd)).measurable

def CompatibleFrames {d : ℕ} (E : Submodule ℝ (Point d)) (F F' : Frames d) : Prop :=
  F.1⁻¹ * F'.1 ∈ subspaceStabilizer E ∧ F.2⁻¹ * F'.2 ∈ subspaceStabilizer E

end LogConcaveSampling.LowerBound

open MeasureTheory ProbabilityTheory

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_LowerBounds_RoundFrames
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

def roundFrames {d k : ℕ} (hk : k+1 < d) (Λ : Point d →L[ℝ] Point d)
    (F : Frames d) (x : Point d) (r : Point d × Point d × Point d) : Frames d :=
  let F₁ := inverseFrameUpdate (Nat.lt_of_succ_lt hk) F x r.1
  let u := (frameTransport F₁).symm x
  let y := Λ u
  forwardFrameUpdate hk F₁ (filledObservation (k := k+1) F₁.2 y r.2.1) r.2.2

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound
open scoped RealInnerProductSpace

def linearReply {d : ℕ} (Λ : Point d →L[ℝ] Point d) (O : Rotations d) (x : Point d) :
    ℝ × Point d :=
  let u := (rotationIsometry O).symm x
  (⟪u,Λ u⟫ / 2, rotationIsometry O (Λ u))

@[fun_prop] lemma measurable_linearReply {d : ℕ} (Λ : Point d →L[ℝ] Point d) :
    Measurable (fun p : Rotations d × Point d => linearReply Λ p.1 p.2) := by
  unfold linearReply
  simp only [← rotationIsometry_inv_apply]
  fun_prop

def roundCoordinate {d k : ℕ} (hk : k+1 < d) (F : Frames d) (x g : Point d) : Point d :=
  (frameTransport (inverseFrameUpdate (Nat.lt_of_succ_lt hk) F x g)).symm x

end LogConcaveSampling.LowerBound

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
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

def linearHistory {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ} (A : OracleAlgorithm Ω d q)
    (Λ : Point d →L[ℝ] Point d) (O : Rotations d) (ω : Ω) : ℕ → Transcript d q
  | 0 => 0
  | n+1 =>
    let h := linearHistory A Λ O ω n
    if hn : n < q then Function.update h ⟨n,hn⟩ (linearReply Λ O (A.query ⟨n,hn⟩ (ω,h))) else h

abbrev RevealState (Ω : Type*) (d q n : ℕ) :=
  Ω × Frames d × Transcript d q × (Fin n → Point d × Point d)

abbrev RoundRandom (d : ℕ) := Point d × Point d × Point d

def roundRandomLaw (d : ℕ) : Measure (RoundRandom d) :=
  (stdGaussian (Point d)).prod ((stdGaussian (Point d)).prod (stdGaussian (Point d)))

instance roundRandomLaw_probability (d : ℕ) : IsProbabilityMeasure (roundRandomLaw d) := by
  unfold roundRandomLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

def initialRevealState {Ω : Type*} {d q : ℕ} (ω : Ω) : RevealState Ω d q 0 :=
  (ω,(1,1),0,Fin.elim0)

def revealStep {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d)
    (n : ℕ) (p : RevealState Ω d q n × RoundRandom d) : RevealState Ω d q (n+1) :=
  let s := p.1
  let r := p.2
  let t := Fin.snoc (α := fun _ : Fin (n+1) => Point d × Point d) s.2.2.2 (r.1,r.2.1)
  if hn : n < q then
    let hk : 2*n+1 < d := by omega
    let x := A.query ⟨n,hn⟩ (s.1,s.2.2.1)
    let F := roundFrames hk Λ s.2.1 x r
    let u := roundCoordinate hk s.2.1 x r.1
    let reply := (⟪u,Λ u⟫ / 2,frameTransport F (Λ u))
    (s.1,F,Function.update s.2.2.1 ⟨n,hn⟩ reply,t)
  else (s.1,s.2.1,s.2.2.1,t)

def HistoryConsistent {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (Λ : Point d →L[ℝ] Point d) (n : ℕ)
    (s : RevealState Ω d q n) : Prop :=
  ∀ H ∈ subspaceStabilizer (prefixSpace d (2*n)),
    s.2.2.1 = linearHistory A Λ (frameCompletion s.2.1 H) s.1 n

def completeRevealState {Ω : Type*} {d q : ℕ} (n : ℕ)
    (p : RevealState Ω d q n × Rotations d) : Ω × Rotations d :=
  (p.1.1,frameCompletion p.1.2.1 p.2)

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound

def finishFrame {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (hd : 2*q < d)
    (p : RevealState Ω d q q × Point d) : Frames d :=
  inverseFrameUpdate hd p.1.2.1 (A.output (p.1.1,p.1.2.2.1)) p.2

def finishComplete {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (hd : 2*q < d)
    (p : (RevealState Ω d q q × Point d) × Rotations d) : Ω × Rotations d :=
  (p.1.1.1,frameCompletion (finishFrame A hd p.1) p.2)

def finishCoordinate {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (hd : 2*q < d)
    (p : RevealState Ω d q q × Point d) : Point d :=
  (frameTransport (finishFrame A hd p)).symm (A.output (p.1.1,p.1.2.2.1))

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound

def roundGood {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (hd : 2*q+1 ≤ d) (n : ℕ)
    (p : RevealState Ω d q n × RoundRandom d) : Prop :=
  if hn : n < q then
    let hk : 2*n < d := by omega
    (prefixSpace d (2*n))ᗮ.orthogonalProjectionOnto (rotationIsometry p.1.2.1.2⁻¹ p.2.1) ≠ 0 ∧
    (prefixSpace d (2*n+1))ᗮ.orthogonalProjectionOnto
      (rotationIsometry (inverseFrameUpdate hk p.1.2.1
        (A.query ⟨n,hn⟩ (p.1.1,p.1.2.2.1)) p.2.1).2⁻¹ p.2.2.1) ≠ 0
  else True

def SpanConsistent {Ω : Type*} {d q : ℕ} (Λ : Point d →L[ℝ] Point d) (n : ℕ)
    (s : RevealState Ω d q n) : Prop :=
  frameSpace s.2.1.2 (prefixSpace d (2*n)) ≤ powerHull Λ.toLinearMap n (tapeHull s.2.2.2)

end LogConcaveSampling.LowerBound

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_LowerBounds_CouplingNoise
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

abbrev CouplingNoise (Ω : Type*) (d q : ℕ) :=
  ((Ω × (Fin q → RoundRandom d)) × Point d) × Rotations d

def couplingLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (d q : ℕ) :
    Measure (CouplingNoise Ω d q) :=
  ((μ.prod (Measure.pi (fun _ : Fin q => roundRandomLaw d))).prod
    (stdGaussian (Point d))).prod (remainingHaar (prefixSpace d (2*q+1)))

instance couplingLaw_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d q : ℕ) :
    IsProbabilityMeasure (couplingLaw μ d q) := by unfold couplingLaw; infer_instance

def couplingState {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (Λ : Point d →L[ℝ] Point d) (hd : 2*q+1 ≤ d)
    (p : CouplingNoise Ω d q) : (RevealState Ω d q q × Point d) × Rotations d :=
  ((stateRun initialRevealState (revealStep A Λ hd) q p.1.1,p.1.2),p.2)

def couplingColumns {Ω : Type*} {d q : ℕ} (p : CouplingNoise Ω d q) : Fin (q+q+1) → Point d :=
  Fin.snoc (α := fun _ : Fin (q+q+1) => Point d)
    (Fin.append (fun i => (p.1.1.2 i).1) (fun i => (p.1.1.2 i).2.1)) p.1.2

end LogConcaveSampling.LowerBound

open WithLp

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_LowerBounds_SpectrumOperator
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
open scoped RealInnerProductSpace
open Matrix WithLp

def spectrumOperator (d : ℕ) : Point d →L[ℝ] Point d :=
  Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (Matrix.diagonal (fun k : Fin d => eigenvalue d k))

@[simp] theorem spectrumOperator_apply {d : ℕ} (x : Point d) (k : Fin d) :
    spectrumOperator d x k = eigenvalue d k * x k := by
  change (Matrix.diagonal (fun k : Fin d => eigenvalue d k) *ᵥ ofLp x) k = _
  exact Matrix.mulVec_diagonal _ _ _

def quadraticOperator {d : ℕ} (O : Rotations d) : Point d →L[ℝ] Point d :=
  (rotationIsometry O).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((spectrumOperator d).comp (rotationIsometry O).symm.toContinuousLinearEquiv.toContinuousLinearMap)

def quadraticPotential {d : ℕ} (O : Rotations d) (x : Point d) : ℝ :=
  inner ℝ x (quadraticOperator O x) / 2

end LogConcaveSampling.LowerBound

end LowerProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_LowerBounds_HardEigenOutput
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
open WithLp
open scoped RealInnerProductSpace

def hardEigenOutput {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (p : Ω × Rotations d) : Fin d → ℝ :=
  ofLp ((rotationIsometry p.2).symm (A.run (quadraticPotential p.2) p.1))

end LogConcaveSampling.LowerBound

end LowerProof

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_Forward
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable
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

namespace MeanTree
variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def forward (r T h : ℝ) (n N : ℕ) (x y : MeanTree X d)
    (i : ProbabilityNode T h n) : MeanTree X d :=
  picard (probabilityWeight T h n)
    (fun j E => scale (-r) (conditional r (probabilityNodeTime T h n j) x E))
    (fun _ => y) N i

end MeanTree

def sampleMeanCircuit {d : ℕ} (F : Point d → ℝ) (x : Point d) (r T h : ℝ)
    (n N : ℕ) (e : ProbabilityNode T h n) (z : Point d) : Point d :=
  T⁻¹ • probabilityPicard F x r T h n N z e

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open Set MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def oriented (Y G : X → Point d) (θ : ℝ) : X → Point d :=
  fun z => Real.cos θ • Y z+Real.sin θ • G z

omit [MeasurableSpace X] in
@[simp] lemma oriented_zero (Y G : X → Point d) : oriented Y G 0=Y := by
  funext z; simp [oriented]

def DirectCenter (r T v : ℝ) (x Y G : X → Point d) (r' : ℝ) (b : X → Point d) : Prop :=
  ∃ρ∈Icc (0:ℝ) T,∃θ,|θ|≤v ∧ r'=r*Real.sqrt (1-ρ^2) ∧
    b=fun z => x z+(r*ρ) • oriented Y G θ z

lemma conditional_centers_direct {r T v ρ θ : ℝ} {x Y G : X → Point d}
    (xE yE : MeanTree X d) (hx : base xE=x) (hy : base yE=oriented Y G θ)
    (hρ : ρ∈Icc (0:ℝ) T) (hθ : |θ|≤v)
    (hxc : centers (DirectCenter r T v x Y G) xE)
    (hyc : centers (DirectCenter r T v x Y G) yE) :
    centers (DirectCenter r T v x Y G) (conditional r ρ xE yE) := by
  apply centers_conditional _ _ _ _ _ _ hxc hyc
  exact ⟨ρ,hρ,θ,hθ,rfl,by rw [hx,hy]⟩

lemma probability_centers_direct {r T h v θ : ℝ} {n N : ℕ}
    (hn : 0<n) (hT : 0<T) (hT1 : T<1) (hh : 0<h)
    {x Y G : X → Point d} (xE yE : MeanTree X d)
    (hx : base xE=x) (hy : base yE=oriented Y G θ) (hθ : |θ|≤v)
    (hxc : centers (DirectCenter r T v x Y G) xE)
    (hyc : centers (DirectCenter r T v x Y G) yE)
    (s i : ProbabilityNode T h n) :
    base (probability r T h n N s xE yE i)=base yE ∧
      centers (DirectCenter r T v x Y G) (probability r T h n N s xE yE i) := by
  apply picard_shape _ _ _ _ (fun _ => hyc)
  intro j k E he hc
  refine ⟨by simp,?_⟩
  apply (centers_scale _ _ _).2
  exact conditional_centers_direct xE E hx (he.trans hy)
    (probabilityNodeTime_mem hT hT1 hh hn j) hθ hxc hc

lemma forward_centers_direct {r T h v θ : ℝ} {n N : ℕ}
    (hn : 0<n) (hT : 0<T) (hT1 : T<1) (hh : 0<h)
    {x Y G : X → Point d} (xE yE : MeanTree X d)
    (hx : base xE=x) (hy : base yE=oriented Y G θ) (hθ : |θ|≤v)
    (hxc : centers (DirectCenter r T v x Y G) xE)
    (hyc : centers (DirectCenter r T v x Y G) yE)
    (i : ProbabilityNode T h n) :
    base (forward r T h n N xE yE i)=base yE ∧
      centers (DirectCenter r T v x Y G) (forward r T h n N xE yE i) := by
  apply picard_shape _ _ _ _ (fun _ => hyc)
  intro j k E he hc
  refine ⟨by simp,?_⟩
  apply (centers_scale _ _ _).2
  exact conditional_centers_direct xE E hx (he.trans hy)
    (probabilityNodeTime_mem hT hT1 hh hn j) hθ hxc hc

lemma harmonic_centers_direct {r T v ρ θ : ℝ} {n N : ℕ} (hn : 0<n)
    {x Y G : X → Point d} (xE yE gE : MeanTree X d)
    (hx : base xE=x) (hy : base yE=Y) (hg : base gE=G)
    (hρ : ρ∈Icc (0:ℝ) T) (hθ : |θ|≤v)
    (hxc : centers (DirectCenter r T v x Y G) xE)
    (hyc : centers (DirectCenter r T v x Y G) yE)
    (hgc : centers (DirectCenter r T v x Y G) gE) (i : Fin (n+1)) :
    base (harmonic r ρ θ n N xE yE gE i)=oriented Y G (θ*probabilityNodes n i) ∧
      centers (DirectCenter r T v x Y G) (harmonic r ρ θ n N xE yE gE i) := by
  have ha : ∀j : Fin (n+1), base (add (scale (Real.cos (θ*probabilityNodes n j)) yE)
      (scale (Real.sin (θ*probabilityNodes n j)) gE))=oriented Y G (θ*probabilityNodes n j) := by
    intro j; simp only [base_add,base_scale,hy,hg]; rfl
  have hp := picard_shape (DirectCenter r T v x Y G) (harmonicWeight n θ)
    (fun _ E => scale ρ (scale (-r) (conditional r ρ xE E)))
    (fun j => add (scale (Real.cos (θ*probabilityNodes n j)) yE)
      (scale (Real.sin (θ*probabilityNodes n j)) gE))
    (fun _ => (centers_add _ _ _).2 ⟨(centers_scale _ _ _).2 hyc,(centers_scale _ _ _).2 hgc⟩) ?_ N i
  · exact ⟨hp.1.trans (ha i),hp.2⟩
  · intro j k E he hc
    refine ⟨by simp,?_⟩
    apply (centers_scale _ _ _).2
    apply (centers_scale _ _ _).2
    apply conditional_centers_direct xE E hx (he.trans (ha k)) hρ _ hxc hc
    rw [abs_mul,abs_of_nonneg (probabilityNodes_mem hn k).1]
    exact (mul_le_mul_of_nonneg_left (probabilityNodes_mem hn k).2 (abs_nonneg θ)).trans (by simpa using hθ)

lemma kernelCorrection_centers_direct {r T h v θ : ℝ} {n N : ℕ}
    (hn : 0<n) (hT : 0<T) (hT1 : T<1) (hh : 0<h)
    {x Y G : X → Point d} (xE yE gE : MeanTree X d)
    (hx : base xE=x) (hy : base yE=Y) (hg : base gE=G)
    (hθ : |θ|≤v)
    (hxc : centers (DirectCenter r T v x Y G) xE)
    (hyc : centers (DirectCenter r T v x Y G) yE)
    (hgc : centers (DirectCenter r T v x Y G) gE) (s e : ProbabilityNode T h n) :
    base (kernelCorrection r T h θ n N s e xE yE gE)=(fun _ => 0) ∧
      centers (DirectCenter r T v x Y G) (kernelCorrection r T h θ n N s e xE yE gE) := by
  have hv : 0≤v := (abs_nonneg _).trans hθ
  have hb := probability_centers_direct (N:=N) hn hT hT1 hh xE yE hx
    (by simpa using hy : base yE=oriented Y G 0) (by simpa using hv) hxc hyc e s
  have hw := harmonic_centers_direct (N:=N) hn xE (probability r T h n N e xE yE s) gE hx
    (hb.1.trans hy) hg (probabilityNodeTime_mem hT hT1 hh hn s) hθ hxc hb.2 hgc (Fin.last n)
  have vlast : probabilityNodes n (Fin.last n)=1 := by
    simp [probabilityNodes,hn.ne']
  rw [vlast,mul_one] at hw
  constructor
  · funext z
    simp only [kernelCorrection,base_sumFamily,base_scale,base_conditional,smul_zero,Finset.sum_const_zero]
  · unfold kernelCorrection
    apply centers_sumFamily
    intro j
    apply (centers_scale _ _ _).2
    apply (centers_scale _ _ _).2
    have hp := probability_centers_direct (N:=N) hn hT hT1 hh xE
      (harmonic r (probabilityNodeTime T h n s) θ n N xE (probability r T h n N e xE yE s) gE (Fin.last n))
      hx hw.1 hθ hxc hw.2 s j
    exact conditional_centers_direct _ _ hx (hp.1.trans hw.1)
      (probabilityNodeTime_mem hT hT1 hh hn j) hθ hxc hp.2

lemma kernelQuadrature_centers_direct {r T h ψ v : ℝ} {n m N : ℕ}
    (hn : 0<n) (hT : 0<T) (hT1 : T<1) (hh : 0<h)
    {x Y G : X → Point d} (xE yE gE : MeanTree X d)
    (hx : base xE=x) (hy : base yE=Y) (hg : base gE=G)
    (hψ : ∀j : Fin (m+1),|ψ*angleNodes m j|≤v)
    (hxc : centers (DirectCenter r T v x Y G) xE)
    (hyc : centers (DirectCenter r T v x Y G) yE)
    (hgc : centers (DirectCenter r T v x Y G) gE)
    (e : ProbabilityNode T h n) (w : ProbabilityNode T h n → ℝ) :
    base (kernelQuadrature r T h ψ n m N e w xE yE gE)=(fun _ => 0) ∧
      centers (DirectCenter r T v x Y G) (kernelQuadrature r T h ψ n m N e w xE yE gE) := by
  have hk (i : ProbabilityNode T h n) (j : Fin (m+1)) :=
    kernelCorrection_centers_direct (N:=N) hn hT hT1 hh xE yE gE hx hy hg (hψ j) hxc hyc hgc i e
  constructor
  · funext z
    simp only [kernelQuadrature,kernelAction,base_sumFamily,base_scale,(hk _ _).1,smul_zero,Finset.sum_const_zero]
  · apply centers_sumFamily
    intro i
    apply (centers_scale _ _ _).2
    apply centers_sumFamily
    intro j
    exact (centers_scale _ _ _).2 (hk i j).2
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open Set MeasureTheory Quadrature
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma pairPicard_shape {I : Type*} [Fintype I] (P : ℝ → (X → Point d) → Prop)
    (w : I → I → ℝ) (φ : MeanTree X d × MeanTree X d → MeanTree X d × MeanTree X d)
    (a : MeanTree X d × MeanTree X d)
    (ha : centers P a.1 ∧ centers P a.2)
    (hφ : ∀p,base p.1=base a.1 → base p.2=base a.2 → centers P p.1 → centers P p.2 →
      base (φ p).1=(fun _ => 0) ∧ base (φ p).2=(fun _ => 0) ∧
      centers P (φ p).1 ∧ centers P (φ p).2)
    (N : ℕ) (i : I) :
    base (pairPicard w φ a N i).1=base a.1 ∧ base (pairPicard w φ a N i).2=base a.2 ∧
      centers P (pairPicard w φ a N i).1 ∧ centers P (pairPicard w φ a N i).2 := by
  induction N generalizing i with
  | zero => exact ⟨rfl,rfl,ha⟩
  | succ N ih =>
    have hp (j : I) := hφ (pairPicard w φ a N j) (ih j).1 (ih j).2.1 (ih j).2.2.1 (ih j).2.2.2
    refine ⟨?_,?_,?_,?_⟩
    · funext z
      simp only [pairPicard,base_add,base_sumFamily,base_scale,(hp _).1,smul_zero,Finset.sum_const_zero,add_zero]
    · funext z
      simp only [pairPicard,base_add,base_sumFamily,base_scale,(hp _).2.1,smul_zero,Finset.sum_const_zero,add_zero]
    · exact (centers_add _ _ _).2 ⟨ha.1,centers_sumFamily _ _ (fun j => (centers_scale _ _ _).2 (hp j).2.2.1)⟩
    · exact (centers_add _ _ _).2 ⟨ha.2,centers_sumFamily _ _ (fun j => (centers_scale _ _ _).2 (hp j).2.2.2)⟩

lemma velocity_centers_direct {r T h ψ v s : ℝ} {n m N : ℕ}
    (hT : 0<T) (hT1 : T<1) (hh : 0<h) (hv : 0≤v)
    {x Y G : X → Point d} (xE yE gE : MeanTree X d)
    (hx : base xE=x) (hy : base yE=Y) (hg : base gE=G)
    (hψ : ∀j : Fin (m+1),|ψ*angleNodes m j|≤v)
    (hxc : centers (DirectCenter r T v x Y G) xE)
    (hyc : centers (DirectCenter r T v x Y G) yE)
    (hgc : centers (DirectCenter r T v x Y G) gE)
    (e : ProbabilityNode T h (n+1)) :
    base (velocity r T h ψ s n m N e xE (yE,gE)).1=(fun _ => 0) ∧
    base (velocity r T h ψ s n m N e xE (yE,gE)).2=(fun _ => 0) ∧
    centers (DirectCenter r T v x Y G) (velocity r T h ψ s n m N e xE (yE,gE)).1 ∧
    centers (DirectCenter r T v x Y G) (velocity r T h ψ s n m N e xE (yE,gE)).2 := by
  have hk := kernelQuadrature_centers_direct (N:=N) (Nat.succ_pos n) hT hT1 hh xE yE gE hx hy hg hψ hxc hyc hgc e (terminalQuadratureWeight T h n)
  have hm : centers (DirectCenter r T v x Y G) (mean r xE) := by
    apply centers_mean _ _ _ _ hxc
    refine ⟨0,⟨by norm_num,hT.le⟩,0,by simpa using hv,?_,?_⟩
    · simp
    · simpa only [mul_zero,zero_smul,add_zero] using hx
  have hc := conditional_centers_direct xE yE hx (by simpa using hy : base yE=oriented Y G 0)
    ⟨hT.le,le_rfl⟩ (by simpa using hv : |(0:ℝ)|≤v) hxc hyc
  refine ⟨?_,?_,?_,?_⟩
  · funext z; simp only [velocity,base_scale,hk.1,smul_zero]
  · funext z; simp only [velocity,base_scale,base_add,base_conditional,base_mean,smul_zero,add_zero]
  · exact (centers_scale _ _ _).2 hk.2
  · exact (centers_scale _ _ _).2 ((centers_add _ _ _).2 ⟨hc,(centers_scale _ _ _).2 hm⟩)

lemma centeringStates_centers_direct {r T h ψ v s : ℝ} {n m N nc Nc : ℕ}
    (hT : 0<T) (hT1 : T<1) (hh : 0<h) (hv : 0≤v)
    {x Y G : X → Point d} (xE yE gE : MeanTree X d)
    (hx : base xE=x) (hy : base yE=Y) (hg : base gE=G)
    (hψ : ∀j : Fin (m+1),|ψ*angleNodes m j|≤v)
    (hxc : centers (DirectCenter r T v x Y G) xE)
    (hyc : centers (DirectCenter r T v x Y G) yE)
    (hgc : centers (DirectCenter r T v x Y G) gE)
    (e : ProbabilityNode T h (n+1)) (i : Fin (nc+1)) :
    base (centeringStates r T h ψ s n m N nc Nc e xE yE gE i).1=Y ∧
    base (centeringStates r T h ψ s n m N nc Nc e xE yE gE i).2=G ∧
    centers (DirectCenter r T v x Y G) (centeringStates r T h ψ s n m N nc Nc e xE yE gE i).1 ∧
    centers (DirectCenter r T v x Y G) (centeringStates r T h ψ s n m N nc Nc e xE yE gE i).2 := by
  have hp := pairPicard_shape (DirectCenter r T v x Y G) (centeringWeight nc)
    (velocity r T h ψ s n m N e xE) (yE,gE) ⟨hyc,hgc⟩
    (fun p hp hq hpc hqc => velocity_centers_direct hT hT1 hh hv xE p.1 p.2 hx
      (hp.trans hy) (hq.trans hg) hψ hxc hpc hqc e) Nc i
  exact ⟨hp.1.trans hy,hp.2.1.trans hg,hp.2.2⟩

lemma meanCircuit_centers_direct {r T h ψ v s : ℝ} {n m N nc Nc : ℕ}
    (hT : 0<T) (hT1 : T<1) (hh : 0<h) (hv : 0≤v)
    {x Y G : X → Point d} (xE yE gE : MeanTree X d)
    (hx : base xE=x) (hy : base yE=Y) (hg : base gE=G)
    (hψ : ∀j : Fin (m+1),|ψ*angleNodes m j|≤v)
    (hxc : centers (DirectCenter r T v x Y G) xE)
    (hyc : centers (DirectCenter r T v x Y G) yE)
    (hgc : centers (DirectCenter r T v x Y G) gE)
    (e : ProbabilityNode T h (n+1)) :
    base (meanCircuit r T h ψ s n m N nc Nc e xE yE gE)=(fun z => s • G z) ∧
    centers (DirectCenter r T v x Y G) (meanCircuit r T h ψ s n m N nc Nc e xE yE gE) := by
  have hp (i : Fin (nc+1)) := centeringStates_centers_direct (N:=N) (Nc:=Nc) (s:=s) hT hT1 hh hv xE yE gE hx hy hg hψ hxc hyc hgc e i
  constructor
  · funext z
    simp only [meanCircuit,base_add,base_scale,base_sumFamily,base_conditional,hg,
      smul_zero,Finset.sum_const_zero,add_zero]
  · apply (centers_add _ _ _).2
    refine ⟨(centers_scale _ _ _).2 hgc,centers_sumFamily _ _ ?_⟩
    intro j
    apply (centers_scale _ _ _).2
    exact conditional_centers_direct xE _ hx (by simpa using (hp j).1 : base _=oriented Y G 0)
      ⟨hT.le,le_rfl⟩ (by simpa using hv : |(0:ℝ)|≤v) hxc (hp j).2.2.1
end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_Expression
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory

namespace LogConcaveSampling.OracleCompiler

inductive Expression (X : Type*) [MeasurableSpace X] (d : ℕ) where
  | noise (base : X → Point d) (measurable_base : Measurable base) (noise : ℝ)
  | add (a : ℝ) (center : Expression X d) (k q : ℕ)
      (child : Program (Point d × (Fin k → Point d)) d q (Point d))
      (P : (Fin k → Point d) → (Fin k → Point d)) (measurable_P : Measurable P)
      (rest : Expression X d)

namespace Expression
variable {X : Type*} [MeasurableSpace X] {d : ℕ}

@[reducible] def slots : Expression X d → ℕ
  | .noise .. => 1
  | .add _ C k _ _ _ _ T => C.slots + (k + T.slots)

@[reducible] def calls : Expression X d → ℕ
  | .noise .. => 0
  | .add _ C _ q _ _ _ T => C.calls + (q + T.calls)

def leftBlock {c k t : ℕ} (g : Fin (c+(k+t)) → Point d) : Fin c → Point d :=
  fun i => g (Fin.castAdd (k+t) i)
def middleBlock {c k t : ℕ} (g : Fin (c+(k+t)) → Point d) : Fin k → Point d :=
  fun i => g (Fin.natAdd c (Fin.castAdd t i))
def rightBlock {c k t : ℕ} (g : Fin (c+(k+t)) → Point d) : Fin t → Point d :=
  fun i => g (Fin.natAdd c (Fin.natAdd k i))

lemma measurable_leftBlock (c k t : ℕ) : Measurable (leftBlock (d:=d) (c:=c) (k:=k) (t:=t)) := by
  unfold leftBlock
  fun_prop
lemma measurable_middleBlock (c k t : ℕ) : Measurable (middleBlock (d:=d) (c:=c) (k:=k) (t:=t)) := by
  unfold middleBlock
  fun_prop
lemma measurable_rightBlock (c k t : ℕ) : Measurable (rightBlock (d:=d) (c:=c) (k:=k) (t:=t)) := by
  unfold rightBlock
  fun_prop

def compile : (C : Expression X d) →
    Program (X × (Fin C.slots → Point d)) d C.calls (Point d)
  | .noise b hb n => Program.pure (fun z => b z.1+n • z.2 0) (by fun_prop)
  | .add a C k q M P hP T => by
      let Ω := X × (Fin (C.slots+(k+T.slots)) → Point d)
      let A : Program Ω d C.calls (Point d) := C.compile.seedMap
        (fun z => (z.1,leftBlock z.2)) (by
          exact measurable_fst.prodMk ((measurable_leftBlock _ _ _).comp measurable_snd))
      let B : Program (Ω × Point d) d q (Point d) := M.seedMap
        (fun z => (z.2,P (middleBlock z.1.2))) (by
          exact measurable_snd.prodMk (hP.comp ((measurable_middleBlock _ _ _).comp
            (measurable_snd.comp measurable_fst))))
      let D : Program ((Ω × Point d) × Point d) d T.calls (Point d) :=
        (T.compile.seedMap (fun z => (z.1.1.1,rightBlock z.1.1.2)) (by
          exact (measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
            ((measurable_rightBlock _ _ _).comp (measurable_snd.comp
              (measurable_fst.comp measurable_fst))))).map
          (fun z => a • z.1.2+z.2) (by fun_prop)
      exact A.seq (B.seq D)

def eval (V : Point d → ℝ) : (C : Expression X d) → X → (Fin C.slots → Point d) → Point d
  | .noise b _ n, x, g => b x+n • g 0
  | .add a C _ _ M P _ T, x, g =>
      a • M.run V (C.eval V x (leftBlock g),P (middleBlock g))+
        T.eval V x (rightBlock g)

end Expression
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler.Program
open MeasureTheory

variable {Ω O R Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace O]
  [MeasurableSpace R] [MeasurableSpace Ξ] {d q r : ℕ}

structure Equivariant (A : Program Ω d q O) (f : Ω → Ω) (τ : O → O) : Prop where
  query : ∀i ω h,A.query i (f ω,h)=A.query i (ω,h)
  output : ∀ω h,A.output (f ω,h)=τ (A.output (ω,h))

end LogConcaveSampling.OracleCompiler.Program

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler.Expression
open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def shiftSlots {n : ℕ} (v : Fin n → ℝ) (Δ : Point d) (g : Fin n → Point d) : Fin n → Point d :=
  fun i => g i+v i • Δ

def moveSeed {n : ℕ} (f : X → X) (v : Fin n → ℝ) (Δ : Point d)
    (z : X × (Fin n → Point d)) : X × (Fin n → Point d) := (f z.1,shiftSlots v Δ z.2)

end LogConcaveSampling.OracleCompiler.Expression

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_SeedProgram
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeasureTheory
open scoped Classical BigOperators

structure SeedProgram (d : ℕ) where
  slots : ℕ
  calls : ℕ
  program : Program (Point d × (Fin slots → Point d)) d calls (Point d)
  shift : Fin slots → ℝ

namespace SeedProgram
variable {d : ℕ}
def damping (M : SeedProgram d) (D : ℝ) :
    (Fin M.slots → Point d) → (Fin M.slots → Point d) :=
  SeedCompiler.slotTransform (SeedCompiler.sqrtCoefficient (fun i => M.shift i/(2*D)))
    (fun i => M.shift i/(2*D))
lemma measurable_damping (M : SeedProgram d) (D : ℝ) : Measurable (M.damping D) := by
  unfold damping SeedCompiler.slotTransform SeedCompiler.slotSum
  fun_prop
end SeedProgram
end LogConcaveSampling.OracleCompiler

end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_ChildNoise
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable
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

def compileTerms (D : ℝ) : (k : ℕ) → (Fin k → ℝ) → (Fin k → Expression X d) →
    (Fin k → SeedProgram d) → Expression X d → Expression X d
  | 0,_,_,_,E => E
  | k+1,a,C,M,E =>
    .add (a 0) (C 0) (M 0).slots (M 0).calls (M 0).program
      ((M 0).damping D) ((M 0).measurable_damping D)
      (compileTerms D k (fun i => a i.succ) (fun i => C i.succ) (fun i => M i.succ) E)

def compile (D : ℝ) (M : ℝ → ℝ → SeedProgram d) : MeanTree X d → ℝ → Expression X d
  | .node k b hb a r C,n =>
    let w := ∑i,|a i|
    compileTerms D k a (fun i => compile D M (C i) (r i/(2*D)))
      (fun i => M (r i) (childNoise n w)) (.noise b hb (reserve n w a))

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def compileDeclared (D A : ℝ) (M : ℝ → ℝ → SeedProgram d) :
    MeanTree X d → ℝ → Expression X d
  | .node k b hb a r C,n =>
    compileTerms D k a (fun i => compileDeclared D A M (C i) (r i/(2*D)))
      (fun i => M (r i) (declaredNoise n A)) (.noise b hb (declaredReserve n A a))

def compileDeclaredRoot (D A Af : ℝ) (Mf Mi : ℝ → ℝ → SeedProgram d) :
    MeanTree X d → ℝ → Expression X d
  | .node k b hb a r C,n =>
    compileTerms D k a (fun i => compileDeclared D A Mi (C i) (r i/(2*D)))
      (fun i => Mf (r i) (declaredNoise n Af)) (.noise b hb (declaredReserve n Af a))

end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_RowTape
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

abbrev RowTape {k : ℕ} (C : Fin k → Expression X d) (M : Fin k → SeedProgram d) :=
  ∀i,(Fin (C i).slots → Point d) × (Fin (M i).slots → Point d)

def rowLaw {k : ℕ} (C : Fin k → Expression X d) (M : Fin k → SeedProgram d) : Measure (RowTape C M) :=
  Measure.pi fun i => (Measure.pi fun _ : Fin (C i).slots => stdGaussian (Point d)).prod
    (Measure.pi fun _ : Fin (M i).slots => stdGaussian (Point d))

instance instIsProbabilityMeasureRowTapeRowLaw {k : ℕ} (C : Fin k → Expression X d) (M : Fin k → SeedProgram d) :
    IsProbabilityMeasure (rowLaw C M) := by unfold rowLaw; infer_instance

def concatTerms (D : ℝ) : (k : ℕ) → (a : Fin k → ℝ) → (C : Fin k → Expression X d) →
    (M : Fin k → SeedProgram d) → (E : Expression X d) →
    RowTape C M × (Fin E.slots → Point d) → (Fin (compileTerms D k a C M E).slots → Point d)
  | 0,_,_,_,_,z => z.2
  | k+1,a,C,M,E,z => Fin.append (z.1 0).1 (Fin.append (z.1 0).2
      (concatTerms D k (fun i => a i.succ) (fun i => C i.succ) (fun i => M i.succ) E
        ((fun i => z.1 i.succ),z.2)))

end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_SlotTransformAddShift
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw
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
open OracleCompiler OracleCompiler.Expression

namespace SeedCompiler

variable {k d : ℕ}

lemma measurable_slotTransform (c : ℝ) (a : Fin k → ℝ) :
    Measurable (slotTransform (E:=Point d) c a) := by
  unfold slotTransform slotSum
  fun_prop

end SeedCompiler
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_RowGaussian
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler
open scoped Classical BigOperators

variable {d k : ℕ}

def rowGaussian (a : Fin k → ℝ) (τ ρ n : ℝ) :
    (Fin k → Point d) × (Fin 1 → Point d) → Point d :=
  fun z => n⁻¹ • ((∑i,a i • (τ • z.1 i))+ρ • z.2 0)

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler Coupling SeedCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def DeclaredValid (D A : ℝ) (P : ℝ → ℝ → Prop) : MeanTree X d → ℝ → Prop
  | .node _ _ _ a r C,n => 0<n ∧ (∑i,|a i|)≤A ∧
      ∀i,P (r i) (declaredNoise n A) ∧ DeclaredValid D A P (C i) (r i/(2*D))

def declaredError (F : Point d → ℝ) (D A : ℝ) (K : ℝ → ℝ → ℝ)
    (B : ℝ → ℝ → Point d → ℝ) : MeanTree X d → ℝ → X → ℝ
  | .node _ _ _ a r C,n,x => (∑i,|a i|)*(∑i,|a i| *
      (2*(K (r i) (declaredNoise n A))^2 * declaredError F D A K B (C i) (r i/(2*D)) x+
       2*B (r i) (declaredNoise n A) ((C i).eval F x)))

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler Coupling SeedCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def DeclaredRootValid (D A Af : ℝ) (Pf Pi : ℝ → ℝ → Prop) : MeanTree X d → ℝ → Prop
  | .node _ _ _ a r C,n => 0<n ∧ (∑i,|a i|)≤Af ∧
      ∀i,Pf (r i) (declaredNoise n Af) ∧ DeclaredValid D A Pi (C i) (r i/(2*D))

def declaredRootError (F : Point d → ℝ) (D A Af : ℝ) (Kf Ki : ℝ → ℝ → ℝ)
    (Bf Bi : ℝ → ℝ → Point d → ℝ) : MeanTree X d → ℝ → X → ℝ
  | .node _ _ _ a r C,n,x => (∑i,|a i|)*(∑i,|a i| *
      (2*(Kf (r i) (declaredNoise n Af))^2 * declaredError F D A Ki Bi (C i) (r i/(2*D)) x+
       2*Bf (r i) (declaredNoise n Af) ((C i).eval F x)))

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open Set MeasureTheory Quadrature
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma centers_mono {P Q : ℝ → (X → Point d) → Prop} (E : MeanTree X d)
    (h : ∀r b,P r b → Q r b) (hE : centers P E) : centers Q E := by
  induction E with | node k b hb a r C ih =>
    intro i
    exact ⟨h _ _ (hE i).1,ih i (hE i).2⟩

def rootScales (P : ℝ → Prop) : MeanTree X d → Prop
  | .node _ _ _ _ r _ => ∀i,P (r i)

@[simp] lemma rootScales_anchor (P : ℝ → Prop) (b : X → Point d) (hb : Measurable b) :
    rootScales P (anchor b hb) := by intro i; exact Fin.elim0 i
@[simp] lemma rootScales_scale (P : ℝ → Prop) (c : ℝ) (E : MeanTree X d) :
    rootScales P (scale c E) ↔ rootScales P E := by cases E; rfl

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open Set MeasureTheory
open scoped Classical BigOperators NNReal

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def centerValues (F : Point d → ℝ) (Q : ℝ) : MeanTree X d → X → Prop
  | .node _ _ _ _ _ C,z => ∀i,circuitD F ((C i).eval F z)≤Q ∧ centerValues F Q (C i) z

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def ErrorLimits (F : Point d → ℝ) (D A : ℝ) (K : ℝ → ℝ → ℝ)
    (B : ℝ → ℝ → Point d → ℝ) (L R : ℝ) : MeanTree X d → ℝ → X → Prop
  | .node _ _ _ _ r C,n,x => ∀i,
      (K (r i) (declaredNoise n A))^2≤L^2 ∧
      B (r i) (declaredNoise n A) ((C i).eval F x)≤R ∧
      ErrorLimits F D A K B L R (C i) (r i/(2*D)) x

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory OracleCompiler OracleCompiler.Expression SeedCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def DriftData : MeanTree X d → Type
  | .node k _ _ _ _ C => ℝ × ((i : Fin k) → DriftData (C i))

def DriftData.root : (E : MeanTree X d) → DriftData E → ℝ
  | .node ..,p => p.1

def DriftValid (f : Point d → X → X) : (E : MeanTree X d) → DriftData E → Prop
  | .node _ b _ _ _ C,p => (∀Δ x,b (f Δ x)=b x+p.1 • Δ) ∧ ∀i,DriftValid f (C i) (p.2 i)

def compileTermsShift (D : ℝ) : (k : ℕ) → (a : Fin k → ℝ) →
    (C : Fin k → Expression X d) → (M : Fin k → SeedProgram d) → (E : Expression X d) →
    ((i : Fin k) → Fin (C i).slots → ℝ) → ((i : Fin k) → Fin (M i).slots → ℝ) →
    (Fin E.slots → ℝ) → Fin (compileTerms D k a C M E).slots → ℝ
  | 0,_,_,_,_,_,_,w => w
  | k+1,a,C,M,E,u,v,w => Fin.append (u 0) (Fin.append (v 0)
      (compileTermsShift D k (fun i => a i.succ) (fun i => C i.succ) (fun i => M i.succ) E
        (fun i => u i.succ) (fun i => v i.succ) w))

def inverseChildShift (D r c : ℝ) (M : SeedProgram d) : Fin M.slots → ℝ :=
  fun i => (c/r)*slotTransform (inverseCoefficient (fun j => M.shift j/(2*D)))
    (fun j => M.shift j/(2*D)) M.shift i

def compileDeclaredShift (D A : ℝ) (M : ℝ → ℝ → SeedProgram d) :
    (E : MeanTree X d) → (n : ℝ) → DriftData E → Fin (compileDeclared D A M E n).slots → ℝ
  | .node k b hb a r C,n,p =>
    compileTermsShift D k a (fun i => compileDeclared D A M (C i) (r i/(2*D)))
      (fun i => M (r i) (declaredNoise n A)) (.noise b hb (declaredReserve n A a))
      (fun i => compileDeclaredShift D A M (C i) (r i/(2*D)) (p.2 i))
      (fun i => inverseChildShift D (r i) ((p.2 i).root (C i)) (M (r i) (declaredNoise n A)))
      (fun _ => 0)

def ShiftReady (D A : ℝ) (P : ℝ → ℝ → Prop) : MeanTree X d → ℝ → Prop
  | .node _ _ _ _ r C,n => ∀i,r i≠0 ∧ P (r i) (declaredNoise n A) ∧ ShiftReady D A P (C i) (r i/(2*D))

end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_Cost
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory OracleCompiler OracleCompiler.Expression SeedCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def cost : MeanTree X d → ℕ
  | .node _ _ _ _ _ C => ∑i,(1+cost (C i))

@[simp] lemma cost_anchor (b : X → Point d) (hb : Measurable b) : cost (anchor b hb)=0 := by simp [cost,anchor]
@[simp] lemma cost_zero : cost (zero : MeanTree X d)=0 := by simp [zero]
@[simp] lemma cost_scale (s : ℝ) (E : MeanTree X d) : cost (scale s E)=cost E := by cases E; rfl
@[simp] lemma cost_add (E D : MeanTree X d) : cost (add E D)=cost E+cost D := by
  cases E; cases D
  simp only [cost,add,Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right]
@[simp] lemma cost_mean (r : ℝ) (E : MeanTree X d) : cost (mean r E)=1+cost E := by simp [cost,mean]
@[simp] lemma cost_conditional (r ρ : ℝ) (E D : MeanTree X d) : cost (conditional r ρ E D)=1+cost E+cost D := by
  simp [conditional,Nat.add_assoc]
@[simp] lemma cost_sumFin (k : ℕ) (E : Fin k → MeanTree X d) : cost (sumFin k E)=∑i,cost (E i) := by
  induction k with
  | zero => simp [sumFin]
  | succ k ih => simp [sumFin,ih,Fin.sum_univ_succ]
@[simp] lemma cost_sumFamily {I : Type*} [Fintype I] (E : I → MeanTree X d) :
    cost (sumFamily E)=∑i,cost (E i) := by
  rw [sumFamily,cost_sumFin]
  exact Fintype.sum_equiv (Fintype.equivFin I).symm _ _ (fun _ => rfl)

def DriftBound (R : ℝ) : (E : MeanTree X d) → DriftData E → Prop
  | .node _ _ _ _ r C,p => ∀i,|((p.2 i).root (C i))/(r i)|≤R ∧ DriftBound R (C i) (p.2 i)

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open Set MeasureTheory
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

theorem exists_driftData (f : Point d → X → X) (R : ℝ) (E : MeanTree X d) (c : ℝ)
    (hc : ∀Δ z,base E (f Δ z)=base E z+c • Δ)
    (hE : centers (fun r b => ∃c : ℝ,(∀Δ z,b (f Δ z)=b z+c • Δ) ∧ |c/r|≤R) E) :
    ∃p : DriftData E,DriftValid f E p ∧ p.root E=c ∧ DriftBound R E p := by
  induction E generalizing c with | node k b hb a r C ih =>
    choose c' hshift hratio using fun i => (hE i).1
    have hh (i : Fin k) := ih i (c' i) (hshift i) (hE i).2
    choose p hp hroot hbound using hh
    exact ⟨(c,p),⟨hc,hp⟩,rfl,fun i => ⟨by simpa only [hroot i] using hratio i,hbound i⟩⟩

omit [MeasurableSpace X] in
lemma DirectCenter.shift {r T v α r' : ℝ} {x Y G b : X → Point d}
    (f : Point d → X → X)
    (hx : ∀Δ z,x (f Δ z)=x z+r • Δ)
    (hY : ∀Δ z,Y (f Δ z)=Y z-α • Δ)
    (hG : ∀Δ z,G (f Δ z)=G z)
    (hb : DirectCenter r T v x Y G r' b) :
    ∃ρ∈Icc (0:ℝ) T,∃θ,|θ|≤v ∧ r'=r*Real.sqrt (1-ρ^2) ∧
      ∀Δ z,b (f Δ z)=b z+(r*(1-ρ*Real.cos θ*α)) • Δ := by
  obtain ⟨ρ,hρ,θ,hθ,hr,hb⟩ := hb
  refine ⟨ρ,hρ,θ,hθ,hr,?_⟩
  intro Δ z
  rw [hb]
  simp only [hx,hY,hG,oriented,smul_add,smul_sub,smul_smul]
  module

omit [MeasurableSpace X] in
lemma DirectCenter.mean_shift {r T v r' : ℝ} (hr : 0 < r) (hT : 1/2≤T) (hT1 : T<1)
    (hv : v^2≤Real.sqrt (1-T^2)) {x Y G b : X → Point d}
    (f : Point d → X → X)
    (hx : ∀Δ z,x (f Δ z)=x z+r • Δ)
    (hY : ∀Δ z,Y (f Δ z)=Y z-T⁻¹ • Δ)
    (hG : ∀Δ z,G (f Δ z)=G z)
    (hb : DirectCenter r T v x Y G r' b) :
    0 < r' ∧ ∃c : ℝ,(∀Δ z,b (f Δ z)=b z+c • Δ) ∧ |c/r'|≤3 := by
  obtain ⟨ρ,hρ,θ,hθ,hr',hshift⟩ := hb.shift f hx hY hG
  have hθ' : θ^2≤Real.sqrt (1-T^2) := by
    have hpow := pow_le_pow_left₀ (abs_nonneg θ) hθ 2
    simp only [sq_abs] at hpow
    exact hpow.trans hv
  obtain ⟨hτ,hbound⟩ := mean_direct_ratio hT hT1 hρ hθ'
  refine ⟨hr' ▸ mul_pos hr hτ,r*(1-ρ*Real.cos θ*T⁻¹),hshift,?_⟩
  rw [hr',mul_div_mul_left _ _ hr.ne']
  simpa only [div_eq_mul_inv] using hbound
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open Set MeasureTheory Quadrature
open scoped Classical BigOperators

variable {d : ℕ}

abbrev MeanInput (d : ℕ) := Point d × (Point d × Point d)
abbrev SampleInput (d : ℕ) := Point d × Point d

def meanInputMove (r T : ℝ) (Δ : Point d) (z : MeanInput d) : MeanInput d :=
  (z.1+r • Δ,(z.2.1-T⁻¹ • Δ,z.2.2))
def sampleInputMove (r T : ℝ) (Δ : Point d) (z : SampleInput d) : SampleInput d :=
  (z.1+r • Δ,z.2-T • Δ)

def literalMean (r T h ψ σ : ℝ) (n m N nc Nc : ℕ) (e : ProbabilityNode T h (n+1)) :
    MeanTree (MeanInput d) d :=
  meanCircuit r T h ψ (σ/2) n m N nc Nc e
    (anchor Prod.fst (by fun_prop)) (anchor (fun z => z.2.1) (by fun_prop))
    (anchor (fun z => z.2.2) (by fun_prop))

def literalSample (r T h : ℝ) (n N : ℕ) (e : ProbabilityNode T h n) :
    MeanTree (SampleInput d) d :=
  scale T⁻¹ (forward r T h n N (anchor Prod.fst (by fun_prop))
    (anchor Prod.snd (by fun_prop)) e)

lemma literalMean_geometry {r T h ψ σ v : ℝ} {n m N nc Nc : ℕ}
    (hT : 0<T) (hT1 : T<1) (hh : 0<h) (hv : 0≤v)
    (hψ : ∀j : Fin (m+1),|ψ*angleNodes m j|≤v) (e : ProbabilityNode T h (n+1)) :
    base (literalMean (d:=d) r T h ψ σ n m N nc Nc e)=(fun z => (σ/2) • z.2.2) ∧
    centers (DirectCenter r T v Prod.fst (fun z : MeanInput d => z.2.1) (fun z => z.2.2))
      (literalMean r T h ψ σ n m N nc Nc e) := by
  exact meanCircuit_centers_direct hT hT1 hh hv _ _ _ rfl rfl rfl hψ
    (centers_anchor _ _ _) (centers_anchor _ _ _) (centers_anchor _ _ _) e

lemma literalSample_geometry {r T h : ℝ} {n N : ℕ} (hn : 0<n)
    (hT : 0<T) (hT1 : T<1) (hh : 0<h) (e : ProbabilityNode T h n) :
    base (literalSample (d:=d) r T h n N e)=(fun z => T⁻¹ • z.2) ∧
    centers (DirectCenter r T 0 Prod.fst Prod.snd (fun _ : SampleInput d => 0))
      (literalSample r T h n N e) := by
  have hg := forward_centers_direct (r:=r) (N:=N) (v:=0) (θ:=0) (x:=Prod.fst) (Y:=Prod.snd) (G:=fun _ : SampleInput d => 0) hn hT hT1 hh
    (anchor (Prod.fst : SampleInput d → Point d) (by fun_prop)) (anchor Prod.snd (by fun_prop))
    rfl (by simp only [base_anchor,oriented_zero]) (by norm_num) (centers_anchor _ _ _) (centers_anchor _ _ _) e
  exact ⟨by simp only [literalSample,base_scale,hg.1,base_anchor],
    (centers_scale _ _ _).2 hg.2⟩

theorem literalMean_drift {r T h ψ σ v : ℝ} {n m N nc Nc : ℕ}
    (hr : 0 < r) (hT : 1/2≤T) (hT1 : T<1) (hh : 0<h) (hv : 0≤v)
    (hvsmall : v^2≤Real.sqrt (1-T^2))
    (hψ : ∀j : Fin (m+1),|ψ*angleNodes m j|≤v) (e : ProbabilityNode T h (n+1)) :
    ∃p : DriftData (literalMean (d:=d) r T h ψ σ n m N nc Nc e),
      DriftValid (meanInputMove r T) _ p ∧ p.root _=0 ∧ DriftBound 3 _ p := by
  have hg := literalMean_geometry (d:=d) (r:=r) (σ:=σ) (N:=N) (nc:=nc) (Nc:=Nc)
    (by linarith : 0<T) hT1 hh hv hψ e
  apply exists_driftData (meanInputMove r T) 3 _ 0
  · intro Δ z
    rw [hg.1]
    simp [meanInputMove]
  · apply centers_mono _ (fun r' b hb => ?_) hg.2
    exact (hb.mean_shift hr hT hT1 hvsmall (meanInputMove r T)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)).2

theorem literalSample_drift {r T h : ℝ} {n N : ℕ}
    (hr : 0 < r) (hn : 0<n) (hT : 0<T) (hT1 : T<1) (hh : 0<h)
    (e : ProbabilityNode T h n) :
    ∃p : DriftData (literalSample (d:=d) r T h n N e),
      DriftValid (sampleInputMove r T) _ p ∧ p.root _ = -1 ∧ DriftBound 2 _ p := by
  have hg := literalSample_geometry (d:=d) (r:=r) (N:=N) hn hT hT1 hh e
  apply exists_driftData (sampleInputMove r T) 2 _ (-1)
  · intro Δ z
    rw [hg.1]
    simp only [sampleInputMove,smul_sub,smul_smul,inv_mul_cancel₀ hT.ne',one_smul,neg_one_smul]
    rfl
  · apply centers_mono _ (fun r' b hb => ?_) hg.2
    obtain ⟨ρ,hρ,θ,hθ,hr',hshift⟩ := hb.shift (sampleInputMove r T)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    have hθ0 : θ=0 := abs_nonpos_iff.mp hθ
    refine ⟨r*(1-ρ*T),?_,?_⟩
    · simpa only [hθ0,Real.cos_zero,mul_one] using hshift
    · rw [hr',mul_div_mul_left _ _ hr.ne']
      exact (sample_direct_ratio hT.le hT1 hρ).2
end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_CompileDeclaredRootShift
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory OracleCompiler OracleCompiler.Expression SeedCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def compileDeclaredRootShift (D A Af : ℝ) (Mf Mi : ℝ → ℝ → SeedProgram d) :
    (E : MeanTree X d) → (n : ℝ) → DriftData E → Fin (compileDeclaredRoot D A Af Mf Mi E n).slots → ℝ
  | .node k b hb a r C,n,p =>
    compileTermsShift D k a (fun i => compileDeclared D A Mi (C i) (r i/(2*D)))
      (fun i => Mf (r i) (declaredNoise n Af)) (.noise b hb (declaredReserve n Af a))
      (fun i => compileDeclaredShift D A Mi (C i) (r i/(2*D)) (p.2 i))
      (fun i => inverseChildShift D (r i) ((p.2 i).root (C i)) (Mf (r i) (declaredNoise n Af)))
      (fun _ => 0)

def RootShiftReady (D A Af : ℝ) (Pf Pi : ℝ → ℝ → Prop) : MeanTree X d → ℝ → Prop
  | .node _ _ _ _ r C,n => ∀i,r i≠0 ∧ Pf (r i) (declaredNoise n Af) ∧ ShiftReady D A Pi (C i) (r i/(2*D))

end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_BaseVariation
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory OracleCompiler OracleCompiler.Expression
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def BaseVariation (B : ℝ) (x y : X) : MeanTree X d → Prop
  | .node _ b _ _ _ C => ‖b x-b y‖ ≤ B ∧ ∀i,BaseVariation B x y (C i)

end LogConcaveSampling.MeanTree

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_ReservedProgram
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeasureTheory Program Expression
open scoped Classical BigOperators

variable {d : ℕ}

structure ReservedProgram (d : ℕ) where
  slots : ℕ
  calls : ℕ
  pre : Program (Point d × (Fin slots → Point d)) d calls (Point d)
  shift : Fin slots → ℝ
  reserve : ℝ

namespace ReservedProgram

def full (S : ReservedProgram d) : SeedProgram d where
  slots := S.slots+1
  calls := S.calls
  program := (S.pre.seedMap (fun z : Point d × (Fin (S.slots+1) → Point d) =>
    (z.1,fun i => z.2 (Fin.castAdd 1 i))) (by fun_prop)).map
    (fun z => z.2+S.reserve • z.1.2 (Fin.natAdd S.slots 0)) (by fun_prop)
  shift := Fin.append S.shift (fun _ => 0)

def extraShift (S : ReservedProgram d) (c : ℝ) : Fin (S.slots+1) → ℝ :=
  Fin.append S.shift (fun _ => c)

end ReservedProgram

def sampleParent (E : Expression (Point d × Point d) d) (v : Fin E.slots → ℝ)
    (T η : ℝ) : ReservedProgram d where
  slots := 1+E.slots
  calls := E.calls
  pre := E.compile.seedMap (fun z : Point d × (Fin (1+E.slots) → Point d) =>
    ((z.1,z.2 (Fin.castAdd E.slots 0)),fun i => z.2 (Fin.natAdd 1 i))) (by fun_prop)
  shift := Fin.append (fun _ => -T) v
  reserve := η/2

def meanParent (S : SeedProgram d)
    (E : Expression (Point d × (Point d × Point d)) d)
    (u : Fin S.slots → ℝ) (v : Fin E.slots → ℝ) (T : ℝ) : SeedProgram d where
  slots := S.slots+(1+E.slots)
  calls := S.calls+E.calls
  program :=
    (S.program.seedMap (fun z : Point d × (Fin (S.slots+(1+E.slots)) → Point d) =>
      (z.1,leftBlock z.2)) (by unfold leftBlock; fun_prop)).seq
    (E.compile.seedMap (fun z =>
      ((z.1.1,(T • z.2,middleBlock z.1.2 0)),rightBlock z.1.2)) (by unfold middleBlock rightBlock; fun_prop))
  shift := Fin.append u (Fin.append (fun _ => 0) v)

end LogConcaveSampling.OracleCompiler

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_TerminalMeanProgram
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory OracleCompiler Program Coupling
open scoped Classical BigOperators NNReal

variable {d : ℕ}

def terminalMeanProgram (d : ℕ) (r σ : ℝ) : SeedProgram d where
  slots := 2
  calls := 1
  program := SeedCompiler.terminalMean d r σ
  shift := SeedCompiler.terminalShift 1

def terminalReservedProgram (d : ℕ) (r η : ℝ) : ReservedProgram d where
  slots := 2
  calls := 1
  pre := oneQuery (fun p => p.1+r • p.2 0) (by fun_prop)
    (fun p => p.1.2 0-r • p.2.2+(Real.sqrt 3*η/2) • p.1.2 1) (by fun_prop)
  shift := SeedCompiler.terminalShift 1
  reserve := η/2

abbrev gaussianTape (d n : ℕ) : Measure (Fin n → Point d) :=
  Measure.pi fun _ => stdGaussian (Point d)

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_CircuitParameters
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeanTree Quadrature
open scoped Classical

structure CircuitParameters where
  n : ℕ
  m : ℕ
  N : ℕ
  nc : ℕ
  Nc : ℕ
  T : ℝ
  h : ℝ
  ψ : ℝ
  v : ℝ
  D : ℝ
  A : ℝ
  Af : ℝ
  T_lower : 1/2≤T
  T_upper : T<1
  h_pos : 0<h
  v_nonneg : 0≤v
  angle_bound : ∀j : Fin (m+1),|ψ*angleNodes m j|≤v
  angle_small : v^2≤Real.sqrt (1-T^2)

namespace CircuitParameters
variable (C : CircuitParameters) {d : ℕ}

def meanEndpoint : ProbabilityNode C.T C.h (C.n+1) :=
  probabilityEndpoint (by linarith [C.T_lower]) C.T_upper C.h_pos (C.n+1)

def meanTree (r σ : ℝ) : MeanTree (MeanInput d) d :=
  literalMean r C.T C.h C.ψ σ C.n C.m C.N C.nc C.Nc C.meanEndpoint

def meanDrift (r σ : ℝ) (hr : 0 < r) : DriftData (C.meanTree (d:=d) r σ) :=
  (literalMean_drift hr C.T_lower C.T_upper C.h_pos C.v_nonneg C.angle_small C.angle_bound C.meanEndpoint).choose

def sampleEndpoint (η : ℝ) (hη : 0<η) (hη1 : η≤1) :
    ProbabilityNode (sampleCorrelation η) C.h (C.n+1) :=
  probabilityEndpoint (by linarith [(sampleCorrelation_properties hη hη1).1])
    (sampleCorrelation_properties hη hη1).2.1 C.h_pos (C.n+1)

def sampleTree (r η : ℝ) (hη : 0<η) (hη1 : η≤1) : MeanTree (SampleInput d) d :=
  literalSample r (sampleCorrelation η) C.h (C.n+1) C.N (C.sampleEndpoint η hη hη1)

def sampleDrift (r η : ℝ) (hr : 0 < r) (hη : 0<η) (hη1 : η≤1) :
    DriftData (C.sampleTree (d:=d) r η hη hη1) :=
  (literalSample_drift hr (Nat.succ_pos C.n)
    (by linarith [(sampleCorrelation_properties hη hη1).1])
    (sampleCorrelation_properties hη hη1).2.1 C.h_pos (C.sampleEndpoint η hη hη1)).choose

def meanCenterBudget (r σ : ℝ) : ℝ := C.A*(r/σ+r^2)
def sampleCenterBudget (r : ℝ) : ℝ := C.A*r^2
def sampleFinalBudget (r : ℝ) : ℝ := C.Af*r

def meanFrom (Mf Mi : ℝ → ℝ → SeedProgram d) (S : ℝ → ℝ → ReservedProgram d)
    (r σ : ℝ) : SeedProgram d :=
  if hr : 0 < r then
    let E := C.meanTree r σ
    let p := C.meanDrift r σ hr
    let noise := Real.sqrt 3*σ/2
    let B := compileDeclaredRoot C.D (C.meanCenterBudget r σ) C.Af Mf Mi E noise
    let v := compileDeclaredRootShift C.D (C.meanCenterBudget r σ) C.Af Mf Mi E noise p
    let R := Real.sqrt (1-C.T^2)
    let anchor := S r (R/C.T)
    meanParent anchor.full B (anchor.extraShift (-2*R/C.T)) v C.T
  else terminalMeanProgram d r σ

def sampleFrom (Mf Mi : ℝ → ℝ → SeedProgram d) (r η : ℝ) : ReservedProgram d :=
  if hv : 0 < r ∧ 0<η ∧ η≤1 then
    let E := C.sampleTree r η hv.2.1 hv.2.2
    let p := C.sampleDrift r η hv.1 hv.2.1 hv.2.2
    let noise := η/Real.sqrt 2
    let B := compileDeclaredRoot C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r) Mf Mi E noise
    let v := compileDeclaredRootShift C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r) Mf Mi E noise p
    sampleParent B v (sampleCorrelation η) η
  else terminalReservedProgram d r η
end CircuitParameters

def RoutineValue (d : ℕ) : RoutineKind → Type
  | .mean => ℝ → ℝ → SeedProgram d
  | .sample => ℝ → ℝ → ReservedProgram d

def constructRoutine (d : ℕ) (C : CircuitParameters) {t : ℝ} (ht : 0<t) (hs : t≤1/44)
    (L : RoutineLabel) : RoutineValue d L.kind :=
  if _ : L.terminal then
    match L.kind with
    | .mean => terminalMeanProgram d
    | .sample => terminalReservedProgram d
  else
    match hk : L.kind with
    | .mean => C.meanFrom
        (constructRoutine d C ht hs ⟨.mean,L.b+t,L.p⟩)
        (constructRoutine d C ht hs ⟨.mean,L.b-10*t,L.p-1/4⟩)
        (constructRoutine d C ht hs ⟨.sample,L.b-10*t,L.p-1/4⟩)
    | .sample => C.sampleFrom
        (constructRoutine d C ht hs ⟨.mean,L.b,L.p⟩)
        (constructRoutine d C ht hs ⟨.mean,L.b-10*t,L.p-1/4⟩)
termination_by L.rank t
decreasing_by
  all_goals apply RoutineStep.rank_lt ht hs (by assumption)
  · simpa only [←hk] using (RoutineStep.meanFinal (t:=t) L.b L.p)
  · simpa only [←hk] using (RoutineStep.internal (t:=t) RoutineKind.mean RoutineKind.mean L.b L.p)
  · simpa only [←hk] using (RoutineStep.internal (t:=t) RoutineKind.mean RoutineKind.sample L.b L.p)
  · simpa only [←hk] using (RoutineStep.sampleFinal (t:=t) L.b L.p)
  · simpa only [←hk] using (RoutineStep.internal (t:=t) RoutineKind.sample RoutineKind.mean L.b L.p)
end LogConcaveSampling.OracleCompiler

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_ScalarPicard
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling
open MeanTree OracleCompiler MeasureTheory OracleCompiler.Expression OracleCompiler.Program
open scoped Classical BigOperators

variable {d : ℕ}

namespace OracleCompiler
structure MeanBudget (B : ℕ) (r : ℝ) (S : SeedProgram d) : Prop where
  slots : S.slots≤B
  calls : S.calls≤B
  energy : (∑j,S.shift j^2)≤(B:ℝ)
  equiv : ∀Δ,S.program.Equivariant (moveSeed (fun x => x+r • Δ) S.shift Δ) id
structure SampleBudget (B : ℕ) (r η : ℝ) (S : ReservedProgram d) : Prop where
  slots : S.slots≤B
  calls : S.calls≤B
  energy : (∑j,S.shift j^2)≤(B:ℝ)
  equiv : ∀Δ,S.pre.Equivariant (moveSeed (fun x => x+r • Δ) S.shift Δ) (fun y => y-Δ)
  reserve : S.reserve=η/2

end OracleCompiler
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_CalibratedMeanCircuit
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter Set MeasureTheory Quadrature ProbabilityTheory
open scoped Classical BigOperators NNReal

def CalibratedMeanCircuit {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T h ψ s : ℝ} (hr : 0 < r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (n N : ℕ) (err : ℝ) : Prop :=
  let e := probabilityEndpoint hT0 hT1 hh (n+1)
  let μ := gibbs (centeringPotential F x r T)
  ∃X : StationaryPath μ
    (skewLieField (centeringPotential F x r T)
      (jointSkew (centeringKernel hF x hr hl hT0.le hT1) s)),
    (∀i,Integrable (fun y => ‖stationaryPicard n N
      (centeringVelocityJoint F x r T h ψ s n n N e) y i-X.path y (probabilityNodes n i)‖^2) μ) ∧
    (∀i,(∫y,‖stationaryPicard n N
      (centeringVelocityJoint F x r T h ψ s n n N e) y i-X.path y (probabilityNodes n i)‖^2 ∂μ)≤
      (circuitD F x)^2*err) ∧
    Measurable (stationaryMeanTarget hF x hr hl hT0.le hT1 X) ∧
    μ.map (stationaryMeanTarget hF x hr hl hT0.le hT1 X)=
      (stdGaussian (Point d)).map (fun g => primitiveExpectedField F x r+s • g) ∧
    Integrable (fun y => ‖centeringMeanCircuit F x r T h ψ s n n N n N e y-
      stationaryMeanTarget hF x hr hl hT0.le hT1 X y‖^2) μ ∧
    (∫y,‖centeringMeanCircuit F x r T h ψ s n n N n N e y-
      stationaryMeanTarget hF x hr hl hT0.le hT1 X y‖^2 ∂μ)≤(s*circuitD F x)^2*err

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_Fresh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler.Program
open MeasureTheory ProbabilityTheory Function
open scoped Classical

variable {E R : Type*} [MeasurableSpace E] [MeasurableSpace R] {d q : ℕ}

def fresh (A : ℕ → Program (E × R) d q E) :
    (n : ℕ) → Program (E × (Fin n → R)) d (q*n) E
  | 0 => pure Prod.fst measurable_fst
  | n+1 =>
      (((fresh A n).seedMap (fun p : E × (Fin (n+1) → R) => (p.1,Fin.init p.2))
        (measurable_fst.prodMk (Measurable.of_eval
          (fun index => (measurable_pi_apply index.castSucc).comp measurable_snd)))).seq
        ((A n).seedMap (fun p : (E × (Fin (n+1) → R)) × E => (p.2,p.1.2 (Fin.last n)))
          (by fun_prop)))

end LogConcaveSampling.OracleCompiler.Program

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
open MeanTree Quadrature FinitePicard
open scoped Classical BigOperators NNReal

def fixedProbabilityBudget (n : ℕ) : ℝ :=
  (probabilityWeight_budget (n+1) (Nat.succ_pos n)).choose

def fixedHarmonicBudget (n : ℕ) : ℝ≥0 :=
  (harmonicWeight_budget (n+1) (Nat.succ_pos n)).choose

def fixedCenteringBudget (n : ℕ) : ℝ :=
  1+(∑i : Fin (n+1),∑j,|centeringWeight n i j|)+
      ∑j,|Quadrature.weight (probabilityNodes n) j 0 1|

namespace CircuitParameters
variable (C : CircuitParameters)

def quadratureBudget : ℝ := ∑j,|terminalQuadratureWeight C.T C.h C.n j|
def derivativeBudget : ℝ := ∑j : Fin (C.m+1),|derivativeWeight (angleNodes C.m) j/C.ψ|
def actualA : ℝ :=
  1+2*fixedCenteringBudget C.nc*(C.quadratureBudget*C.derivativeBudget*
    (2*fixedProbabilityBudget C.n)+2)+4*fixedProbabilityBudget C.n+fixedHarmonicBudget C.n
def actualAf : ℝ := 1+fixedCenteringBudget C.nc+2*fixedProbabilityBudget C.n

end CircuitParameters
end LogConcaveSampling.OracleCompiler

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_MeanCorrect
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeasureTheory ProbabilityTheory Coupling
open scoped Classical NNReal

variable {d : ℕ}

structure MeanCorrect (F : Point d → ℝ) (lam q K e : ℝ)
    (M : ℝ → ℝ → SeedProgram d) : Prop where
  lip : ∀r σ,MeanSize lam q r σ → ∀x y g,
    ‖(M r σ).program.run F (x,g)-(M r σ).program.run F (y,g)‖≤lam*K*‖x-y‖
  error : ∀r σ,MeanSize lam q r σ → ∀x,
    SquaredAt (gaussianTape d (M r σ).slots) (stdGaussian (Point d))
      (fun g => (M r σ).program.run F (x,g))
      (fun g => primitiveExpectedField F x r+σ • g) (σ^2*e^2*(circuitD F x)^2)

structure SampleCorrect (F : Point d → ℝ) (lam q K e : ℝ) (ηmin : ℝ)
    (S : ℝ → ℝ → ReservedProgram d) : Prop where
  lip : ∀r η,SampleSize lam q r η → ηmin≤η → ∀x y g,
    ‖(S r η).pre.run F (x,g)-(S r η).pre.run F (y,g)‖≤lam*r*K*‖x-y‖
  error : ∀r η,SampleSize lam q r η → ηmin≤η → ∀x,
    SquaredAt (gaussianTape d (S r η).slots)
      ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d)))
      (fun g => (S r η).pre.run F (x,g))
      (fun z => z.1+(Real.sqrt 3*η/2) • z.2) (e^2*(circuitD F x)^2)

end LogConcaveSampling.OracleCompiler

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_FullTape
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler.ReservedProgram
open MeasureTheory ProbabilityTheory Function Coupling
open scoped Classical NNReal

variable {d : ℕ}

def fullTape (k : ℕ) (z : (Fin k → Point d) × Point d) : Fin (k+1) → Point d :=
  Fin.append z.1 (fun _ => z.2)

end LogConcaveSampling.OracleCompiler.ReservedProgram

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler.CircuitParameters
open MeanTree

variable (C : CircuitParameters) {d : ℕ}

def depthBound : ℕ := 4*(C.N+1)^2

end LogConcaveSampling.OracleCompiler.CircuitParameters

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeanTree Coupling
open scoped Classical NNReal

namespace CircuitParameters
variable (C : CircuitParameters) {d : ℕ}

def compilerError (H Kf q ei ef : ℝ) : ℝ :=
  2*(1+2*H)*(C.Af*Kf*q*ei+ef)

def meanError (H Kf q es ei ef en : ℝ) : ℝ :=
  2*(C.Af*Kf*H*q)*es+10*(20+16*circuitGrowthConstant^2)*C.compilerError H Kf q ei ef+2*en

def sampleError (H Kf q ei ef en : ℝ) : ℝ :=
  20*C.compilerError H Kf q ei ef+2*en

end CircuitParameters
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeanTree Coupling MeasureTheory ProbabilityTheory
open scoped Classical NNReal

variable {d : ℕ}

namespace CircuitParameters
variable (C : CircuitParameters)

def MeanNumericalReady {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (q en : ℝ) (hq : q≤1/4) : Prop :=
  ∀x r σ,∀hs : MeanSize lam q r σ,
    CalibratedMeanCircuit (r:=r) (T:=C.T) (h:=C.h) (ψ:=C.ψ) (s:=σ/2)
      hF x hs.1 (by linarith [hs.2.2.2.1] : (lam:ℝ)*r^2≤1/2)
      (by linarith [C.T_lower]) C.T_upper C.h_pos C.n C.N (en^2)

def SampleNumericalReady {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (q en : ℝ) : Prop :=
  ∀x r η,∀hs : SampleSize lam q r η,∀hl : (lam:ℝ)*r^2≤1/2,
    Integrable (fun Y => ‖sampleMeanCircuit F x r (sampleCorrelation η) C.h
      (C.n+1) C.N (C.sampleEndpoint η hs.2.2.1 hs.2.2.2.1) Y-
      (sampleCorrelation η)⁻¹ • fullProbabilityFlow hF x hs.1.le hl (sampleCorrelation η) Y‖^2)
      (stdGaussian (Point d)) ∧
    (∫Y,‖sampleMeanCircuit F x r (sampleCorrelation η) C.h
      (C.n+1) C.N (C.sampleEndpoint η hs.2.2.1 hs.2.2.2.1) Y-
      (sampleCorrelation η)⁻¹ • fullProbabilityFlow hF x hs.1.le hl (sampleCorrelation η) Y‖^2
      ∂stdGaussian (Point d))≤(circuitD F x)^2*en^2

end CircuitParameters
end LogConcaveSampling.OracleCompiler

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_IndependentSeq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler.Program
open MeasureTheory ProbabilityTheory Function
open scoped Classical

variable {Ω E R : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace R] {d q r : ℕ}

def independentSeq (A : Program Ω d q E) (B : Program (E × R) d r E) :
    Program (Ω × R) d (q+r) E :=
  (A.seedMap Prod.fst measurable_fst).seq
    (B.seedMap (fun p => (p.2,p.1.2)) (by fun_prop))

end LogConcaveSampling.OracleCompiler.Program

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_RoutineBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeanTree
open scoped Classical

variable {d : ℕ}

def RoutineBudget (B : ℕ) (η₀ η₁ : ℝ) : {k : RoutineKind} → RoutineValue d k → Prop
  | .mean,M => ∀r σ,MeanBudget B r (M r σ)
  | .sample,S => ∀r η,η=η₀ ∨ η=η₁ → SampleBudget B r η (S r η)

end LogConcaveSampling.OracleCompiler

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
open Filter Quadrature
open scoped Classical Topology

structure SourceShape (κ t w : ℝ) (n N d : ℕ) (C : CircuitParameters) : Prop where
  n_eq : C.n=n
  m_eq : C.m=n
  N_eq : C.N=N
  nc_eq : C.nc=n
  Nc_eq : C.Nc=N
  T_eq : C.T=sourceCorrelation (κ*t) d
  h_eq : C.h=(d:ℝ)^(-(κ*w))
  ψ_eq : C.ψ=(d:ℝ)^(-(4*(κ*t)))
  D_eq : C.D=(d:ℝ)^(κ*t)
  A_eq : C.A=C.actualA
  Af_eq : C.Af=C.actualAf

def sourceA (κ t w : ℝ) (n d : ℕ) : ℝ :=
  1+2*fixedCenteringBudget n*((∑j,|terminalQuadratureWeight (sourceCorrelation (κ*t) d)
    ((d:ℝ)^(-(κ*w))) n j|)*(∑j : Fin (n+1),|derivativeWeight (angleNodes n) j/
      ((d:ℝ)^(-(4*(κ*t))))|)*(2*fixedProbabilityBudget n)+2)+
    4*fixedProbabilityBudget n+fixedHarmonicBudget n

def sourceAf (n : ℕ) : ℝ := 1+fixedCenteringBudget n+2*fixedProbabilityBudget n

end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open Filter
open scoped Classical Topology

def meanFinalSize (κ t : ℝ) (n : ℕ) (q : ℕ → ℝ) (d : ℕ) : ℝ :=
  (1+4*sourceAf n)*(d:ℝ)^(-(κ*t))*q d

def sampleFinalSize (n : ℕ) (q : ℕ → ℝ) (d : ℕ) : ℝ := (1+4*sourceAf n)*q d

def internalSize (κ t w : ℝ) (n : ℕ) (q : ℕ → ℝ) (d : ℕ) : ℝ :=
  q d*(1+16*(d:ℝ)^(κ*t)*sourceA κ t w n d/((d:ℝ)^(-(κ*t))))

end LogConcaveSampling.OracleCompiler

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_StandaloneCorrect
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open Filter MeanTree MeasureTheory ProbabilityTheory
open scoped Classical NNReal Topology

variable {d : ℕ}

def StandaloneCorrect (F : Point d → ℝ) (lam q K e ηmin : ℝ) :
    {k : RoutineKind} → RoutineValue d k → Prop
  | .mean,M => MeanCorrect F lam q K e M
  | .sample,S => SampleCorrect F lam q K e ηmin S

def UniformAccuracy (κ t w : ℝ) (_ : ℝ) (n N : ℕ) (ht : 0 < t) (hts : t≤1/44)
    (L : RoutineLabel) : Prop :=
  ∀q : ℕ → ℝ,LogPowerRate q (κ*L.b) → (∀ᶠ d : ℕ in atTop,0 < q d) →
  ∃K : ℝ,0 ≤ K ∧ ∃e : ℕ → ℝ,LogPowerRate e (κ*L.p) ∧
    (∀ᶠ d : ℕ in atTop,0 < e d) ∧
    ∀ᶠ d : ℕ in atTop,∀C : CircuitParameters,SourceShape κ t w n N d C →
      ∀{F : Point d → ℝ} {lam : ℝ≥0},∀_ : Primitive F lam,0 < lam → (lam:ℝ)≤1 →
      StandaloneCorrect F lam (q d) K (e d) ((d:ℝ)^(-(κ*t))) (constructRoutine d C ht hts L)

end LogConcaveSampling.OracleCompiler

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_NoiseKernel
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable
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

def noiseKernel (s : ℝ) : Kernel (Point d) (Point d) :=
  (Kernel.id ×ₖ Kernel.const (Point d) (stdGaussian (Point d))).map (fun p => p.1+s • p.2)

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical NNReal

variable {d : ℕ}

namespace OracleCompiler

def proximalProgram (S : ReservedProgram d) (h : ℝ) :
    Program (Point d × (Fin S.full.slots → Point d)) d S.full.calls (Point d) :=
  (((S.full.program.seedMap (fun p : Point d × (Fin S.full.slots → Point d) => (0,p.2))
      (by fun_prop)).affineOracle Prod.fst measurable_fst (Real.sqrt h))).map
    (fun p => p.1.1+Real.sqrt h • p.2) (by fun_prop)

def approximateProximalKernel (S : ReservedProgram d) (h : ℝ)
    (V : Point d → ℝ) (_hV : Admissible V) : Kernel (Point d) (Point d) :=
  (Kernel.id ×ₖ Kernel.const (Point d) (gaussianTape d S.full.slots)).map
    ((proximalProgram S h).run V)

end OracleCompiler
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical ENNReal

variable {d : ℕ}

namespace OracleCompiler

def halvingProgram (S : ReservedProgram d) (h : ℝ) :
    Program (Point d × (Fin S.full.slots → Point d)) d S.full.calls (Point d) :=
  (proximalProgram S h).map (fun p => (1/2:ℝ) • (p.1.1+p.2)) (by fun_prop)

def approximateHalvingKernel (S : ReservedProgram d) (h : ℝ)
    (V : Point d → ℝ) (hV : Admissible V) : Kernel (Point d) (Point d) :=
  (Kernel.id ×ₖ approximateProximalKernel S h V hV).map (fun p => (1/2:ℝ) • (p.1+p.2))

end OracleCompiler
end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_OraclePrograms_TopProgram
attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeasureTheory ProbabilityTheory Function
open scoped Classical NNReal

variable {d : ℕ}

def topProgram (S : ReservedProgram d) (h : ℝ) (N J : ℕ) :=
  (Program.fresh (fun _ => proximalProgram S h) N).independentSeq
    (Program.fresh (fun j => halvingProgram S (descentScale h j)) J)

def topSeedLaw (S : ReservedProgram d) (N J : ℕ) :=
  ((Measure.dirac (0:Point d)).prod (Measure.pi (fun _ : Fin N => gaussianTape d S.full.slots))).prod
    (Measure.pi (fun _ : Fin J => gaussianTape d S.full.slots))

instance topSeedLaw_probability (S : ReservedProgram d) (N J : ℕ) :
    IsProbabilityMeasure (topSeedLaw S N J) := by unfold topSeedLaw; infer_instance

end LogConcaveSampling.OracleCompiler

end

end

end OAI
end


