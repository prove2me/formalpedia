-- Prove2me | Definitions.Def_QAlgorithms_Defs_ContinuousOraclePrograms
-- name    : QAlgorithms_Defs_ContinuousOraclePrograms
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:20:38.448184+00:00
-- url     : https://prove2.me/theorems/aa7d563b-2bee-438f-a52b-36e6aba40ffa
-- title:
--   ContinuousOraclePrograms
-- statement:
--   ContinuousOraclePrograms
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ContinuousOraclePrograms.lean

import Definitions.Def_QAlgorithms_Defs_ContinuousGradientOracles
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace QAlgorithms.StochasticOptimization

variable {n m d k b w M K N c out : ℕ}

/-- Operational continuous-value quantum program, 2308.01582 pp.3,9–13.
Known unitaries are input independent; only query steps apply the supplied
oracle or inverse. Measurement discards the measured register and resets
the next fresh subroutine. Natural-valued draws admit unbounded geometric
execution. diverge retains missing terminal mass. -/
inductive ContinuousOracleProgram (d : ℕ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  | output (v : Vector d)
  | known (U : H ≃ₗᵢ[ℂ] H) (next : ContinuousOracleProgram d H)
  | query (inverse : Bool) (next : ContinuousOracleProgram d H)
  | measure (next : Vector d → ContinuousOracleProgram d H)
  | naturalDraw (mu : Measure ℕ) (probability : IsProbabilityMeasure mu)
      (next : ℕ → ContinuousOracleProgram d H)
  | bind (first : ContinuousOracleProgram d H)
      (next : Vector d → ContinuousOracleProgram d H)
  | fresh (next : ContinuousOracleProgram d H)
  | diverge

/-- Execute a supplied unitary with public reset/value registers,
2308.01582 pp.3–4. The distribution is its actual measured preparation,
not a freely supplied sampler law; the unitary is the only query action. -/
def samplingOracleOfUnitary {d : ℕ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (R : SamplingRegisters d H)
    (U : H ≃ₗᵢ[ℂ] H) : QuantumSamplingOracle d H R where
  distribution := R.measurement.born (U R.zero)
  probability := by
    constructor
    rw [R.measurement.born_eq _ Set.univ MeasurableSet.univ,R.measurement.total]
    simp [R.zero_norm]
  unitary := U
  law := rfl

/-- Actual terminal output/query-count law, 2308.01582 pp.9–13.
Both forward and inverse applications add one; all fresh subroutine calls
compose by their operational laws. Nontermination contributes no output mass. -/
def programLaw {d : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {R : SamplingRegisters d H} (O : QuantumSamplingOracle d H R) :
    ContinuousOracleProgram d H → H → Measure (Vector d × ℕ)
  | .output v, _ => Measure.dirac (v,0)
  | .known U next, psi => programLaw O next (U psi)
  | .query inv next, psi =>
      (programLaw O next (if inv then O.unitary.symm psi else O.unitary psi)).map
        (fun vq => (vq.1, vq.2 + 1))
  | .measure next, psi => (R.measurement.born psi).bind (fun v => programLaw O (next v) R.zero)
  | .naturalDraw mu _ next, psi => mu.bind (fun j => programLaw O (next j) psi)
  | .bind first next, psi => (programLaw O first psi).bind (fun vq =>
      (programLaw O (next vq.1) R.zero).map (fun wq => (wq.1, vq.2 + wq.2)))
  | .fresh next, _ => programLaw O next R.zero
  | .diverge, _ => 0

/-- Source's standing measurability convention for classical controls,
2308.01582 pp.3,9–13. This excludes Measure.bind's nonmeasurable-map default;
it is a physical well-formedness obligation, never accuracy or a cost bound. -/
def IsMeasurableProgram {d : ℕ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {R : SamplingRegisters d H} (O : QuantumSamplingOracle d H R) :
    ContinuousOracleProgram d H → Prop
  | .output _ => True
  | .known _ next => IsMeasurableProgram O next
  | .query _ next => IsMeasurableProgram O next
  | .measure next =>
      Measurable (fun v => programLaw O (next v) R.zero) ∧ ∀ v, IsMeasurableProgram O (next v)
  | .naturalDraw _ _ next =>
      Measurable (fun j => programLaw O (next j) R.zero) ∧ ∀ j, IsMeasurableProgram O (next j)
  | .bind first next => IsMeasurableProgram O first ∧
      Measurable (fun vq : Vector d × ℕ =>
        (programLaw O (next vq.1) R.zero).map (fun wq => (wq.1,vq.2+wq.2))) ∧
      ∀ v, IsMeasurableProgram O (next v)
  | .fresh next => IsMeasurableProgram O next
  | .diverge => True

/-- Well-formed operational output/count law, 2308.01582 pp.9–13.
The explicit guard is the source's measurability standing convention. -/
def executionLaw {d : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : ContinuousOracleProgram d H) {R : SamplingRegisters d H} (O : QuantumSamplingOracle d H R)
    (hP : IsMeasurableProgram O P) : Measure (Vector d × ℕ) :=
  programLaw O P R.zero

/-- Operational execution using the original coherent gradient oracle,
2308.01582 pp.13–14. For the expanded accelerated program R must be the
public output/reset registers of its Gaussian layout. This keeps every
query equal to the original O_g and every measurement in the proper
smoothed value register, despite retaining all shifted-query garbage. -/
def gradientExecutionLaw {d : ℕ} {H W : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [CompleteSpace W] {G : GradientRegisters d H W}
    {f : Vector d → ℝ} (P : ContinuousOracleProgram d H)
    (R : SamplingRegisters d H) (O : QuantumStochasticGradientOracle d f H W G)
    (hP : IsMeasurableProgram (samplingOracleOfUnitary R O.unitary) P) :
    Measure (Vector d × ℕ) :=
  executionLaw P (samplingOracleOfUnitary R O.unitary) hP

/-- Extended expected calls, with infinity for positive nontermination
mass (2308.01582 pp.10–12). -/
def expectedCalls (law : Measure (Vector d × ℕ)) : ℝ≥0∞ :=
  if law Set.univ = 1 then ∫⁻ vq, (vq.2 : ℝ≥0∞) ∂law else ⊤

/-- Sanity check for the modeled source objects (arxiv-2308.01582v2, PDF pp.3,10,12,13). -/
example {d : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {R : SamplingRegisters d H} (O : QuantumSamplingOracle d H R) (v : Vector d) :
    programLaw O (.output v) R.zero = Measure.dirac (v,0) := rfl

/-- Sanity check for the modeled source objects (arxiv-2308.01582v2, PDF pp.3,10,12,13). -/
example {d : ℕ} : expectedCalls (0 : Measure (Vector d × ℕ)) = ⊤ := by
  simp [expectedCalls]

end QAlgorithms.StochasticOptimization


