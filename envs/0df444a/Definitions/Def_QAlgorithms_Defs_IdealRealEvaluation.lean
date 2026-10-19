-- Prove2me | Definitions.Def_QAlgorithms_Defs_IdealRealEvaluation
-- name    : QAlgorithms_Defs_IdealRealEvaluation
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:38:02.136032+00:00
-- url     : https://prove2.me/theorems/6e743267-c3cc-49aa-9f5a-c90bcf3d9e4e
-- title:
--   IdealRealEvaluation
-- statement:
--   IdealRealEvaluation
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\IdealRealEvaluation.lean

import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters
import Definitions.Def_QAlgorithms_Defs_NonconvexObjectiveGeometry
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

open MeasureTheory
open scoped ENNReal
namespace QAlgorithms.Nonconvex

/-- Implementation helper; source: arxiv-2007.10253v3 PDF p.3. -/
abbrev Register (d : ℕ) (W : Type) := RealRegisters.Hilbert ((Vector d × ℝ) × W)

/-- A unitary realization of Eq.(2) on a label register for query locations and real output values, mapping clean |x,0> to |x,f(x)> and extending linearly. A semantic ideal real-label Hilbert register or changing finite meshes embedded in it is required. Specify only the guaranteed clean interface, with inverse uncomputation; no free controlled oracle or unproved arbitrary dirty-register action. Source: arxiv-2007.10253v3 PDF p.3; arxiv-2007.10253v3 PDF p.20. -/
def IsRealEvaluationOracle {d : ℕ} {W : Type} (w0 : W)
    (U : Register d W ≃ₗᵢ[ℂ] Register d W) (f : Vector d → ℝ) : Prop :=
  ∀ x, U (lp.single 2 ((x,0),w0) 1) = lp.single 2 ((x,f x),w0) 1

/-- Implementation helper; source: arxiv-2007.10253v3 PDF p.3. -/
structure Instrument (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  outcomes : ℕ
  op : Fin outcomes → H →L[ℂ] H
  complete : ∀ psi, ∑ j, ‖op j psi‖^2 = ‖psi‖^2

/-- Known quantum operations, clean evaluations/inverses, measurements, classical feedback and returned real vectors. Code, workspace and non-query unitaries must be chosen independently of f before input/oracle quantification. This source-specific syntax structurally counts all oracle applications including those compiling gradient and wave evolution, rather than attaching a free cost field. Source: arxiv-2007.10253v3 PDF p.3; arxiv-2007.10253v3 PDF p.4; arxiv-2007.10253v3 PDF p.18; arxiv-2007.10253v3 PDF p.20; arxiv-2007.10253v3 PDF p.24. -/
inductive EvaluationProgram (d : ℕ) (W : Type) where
  | output (x : Vector d)
  | known (U : Register d W ≃ₗᵢ[ℂ] Register d W) (next : EvaluationProgram d W)
  | query (inverse : Bool) (next : EvaluationProgram d W)
  | measure (M : Instrument (Register d W)) (next : Fin M.outcomes → EvaluationProgram d W)
  | draw (mu : Measure (Vector d)) (probability : IsProbabilityMeasure mu)
      (next : Vector d → EvaluationProgram d W)
  | reset (next : EvaluationProgram d W)
  | diverge

/-- Linear branch semantics on subnormalized vectors for the program's returned point and actual number of calls. Derive Born weights from normalized states/unitaries and lawful measurements; include the joint correct-output and bounded-resource event. Account for failure/termination without default zero expectations or arbitrary declared success probabilities. Source: arxiv-2007.10253v3 PDF p.3; arxiv-2007.10253v3 PDF p.18; arxiv-2007.10253v3 PDF p.19; arxiv-2007.10253v3 PDF p.20; arxiv-2007.10253v3 PDF p.23; arxiv-2007.10253v3 PDF p.24. -/
def evaluationBranchLaw {d : ℕ} {W : Type} (zero : Register d W) (zero_unit : ‖zero‖ = 1)
    (U : Register d W ≃ₗᵢ[ℂ] Register d W) :
    EvaluationProgram d W → Register d W → Measure (Vector d × ℕ)
  | .output x, psi => ENNReal.ofReal (‖psi‖^2) • Measure.dirac (x,0)
  | .known V next, psi => evaluationBranchLaw zero zero_unit U next (V psi)
  | .query inv next, psi =>
      (evaluationBranchLaw zero zero_unit U next (if inv then U.symm psi else U psi)).map
        (fun vq => (vq.1,vq.2+1))
  | .measure M next, psi => ∑ j, evaluationBranchLaw zero zero_unit U (next j) (M.op j psi)
  | .draw mu _ next, psi => mu.bind (fun x => evaluationBranchLaw zero zero_unit U (next x) psi)
  | .reset next, psi => ENNReal.ofReal (‖psi‖^2) • evaluationBranchLaw zero zero_unit U next zero
  | .diverge, _ => 0

/-- Measurability predicate on the actual program observation/feedback kernels, with lawful normalized instruments and guarded measures; prevents Measure.map/bind default-zero artifacts. Source: arxiv-2007.10253v3 PDF p.3; arxiv-2007.10253v3 PDF p.18; arxiv-2007.10253v3 PDF p.19; arxiv-2007.10253v3 PDF p.20; arxiv-2007.10253v3 PDF p.23; arxiv-2007.10253v3 PDF p.24. -/
def IsEvaluationProgramMeasurable {d : ℕ} {W : Type} (zero : Register d W) (zero_unit : ‖zero‖ = 1)
    (U : Register d W ≃ₗᵢ[ℂ] Register d W) : EvaluationProgram d W → Prop
  | .output _ => True
  | .known _ next => IsEvaluationProgramMeasurable zero zero_unit U next
  | .query _ next => IsEvaluationProgramMeasurable zero zero_unit U next
  | .measure _ next => ∀ j, IsEvaluationProgramMeasurable zero zero_unit U (next j)
  | .draw _ _ next =>
      (∀ psi, Measurable (fun x => evaluationBranchLaw zero zero_unit U (next x) psi)) ∧
        ∀ x, IsEvaluationProgramMeasurable zero zero_unit U (next x)
  | .reset next => IsEvaluationProgramMeasurable zero zero_unit U next
  | .diverge => True

/-- Computed returned-point/call-count subprobability measure, with normalized initial and
reset states and measurable classical feedback. Missing mass records divergence/failure;
the high-probability joint event, rather than a normalization axiom, controls that mass.
Source: arxiv-2007.10253v3 PDF pp.3–4,18–20. -/
def evaluationExecutionLaw {d : ℕ} {W : Type} (zero : Register d W)
    (zero_unit : ‖zero‖ = 1) (U : Register d W ≃ₗᵢ[ℂ] Register d W)
    (P : EvaluationProgram d W) (start : Register d W) (_start_unit : ‖start‖ = 1)
    (_measurable : IsEvaluationProgramMeasurable zero zero_unit U P) : Measure (Vector d × ℕ) :=
  evaluationBranchLaw zero zero_unit U P start

example {d : ℕ} {W : Type} (zero : Register d W) (zero_unit : ‖zero‖ = 1)
    (U V : Register d W ≃ₗᵢ[ℂ] Register d W) (x : Vector d) (psi : Register d W) :
    evaluationBranchLaw zero zero_unit U (.output x) psi =
      evaluationBranchLaw zero zero_unit V (.output x) psi := rfl

end QAlgorithms.Nonconvex


