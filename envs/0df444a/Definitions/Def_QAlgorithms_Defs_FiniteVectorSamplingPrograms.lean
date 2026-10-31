-- Prove2me | Definitions.Def_QAlgorithms_Defs_FiniteVectorSamplingPrograms
-- name    : QAlgorithms_Defs_FiniteVectorSamplingPrograms
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T04:13:32.455177+00:00
-- url     : https://prove2.me/theorems/ce57b527-1bc1-4e01-94ae-cf72dce032c6
-- title:
--   prove2quantum library: Defs.FiniteVectorSamplingPrograms
-- statement:
--   Shared definitions of the prove2quantum Lean library (`QAlgorithms.Defs.FiniteVectorSamplingPrograms`), reused by its paper formalizations.
--
--   - `SamplingProgram`: Oracle-independent operations, plain O/O† queries, finite-outcome measurement instruments and terminal vector estimates. Observed values such as ζ may select subsequent known circuits. Extend retained-query semantics with vector output; reuse FiniteOracleStep with control=false and QuantumInstrument. Program fields contain operations/decoding, never desired accuracy or budget guarantees. Source: arxiv-2607.25492v2 PDF p.7; arxiv-2607.25492v2 PDF p.19; arxiv-2607.25492v2 PDF p.24.
--   - `executionLaw`: Computed finite Born/Kraus law of returned decoded vector and counted forward/inverse sampler applications; known operations do not contribute queries. Source: arxiv-2607.25492v2 PDF p.6; arxiv-2607.25492v2 PDF p.23; arxiv-2607.25492v2 PDF p.24.
--   - `SamplingProgram.bind`: Substitute a classical continuation at each returned estimate, retaining state and actual queries. Source: arxiv-2607.25492v2 PDF p.7.
--   - `measuredSamples`: Execute exactly `n` fresh reset/query/measure operations, storing only the publicly decoded observations in chronological order. Source: arxiv-2607.25492v2 PDF pp.4,5,7.
--   - `outputProbability`: Sum the computed execution branch probabilities for decoded estimates in the supplied event. Success for every compatible hidden distribution/oracle is a theorem. Source: arxiv-2607.25492v2 PDF p.6; arxiv-2607.25492v2 PDF p.23; arxiv-2607.25492v2 PDF p.24.
--   - `worstCaseQueries`: Maximum actual sampler/adjoint-call counter over positive-probability branches of finite adaptive execution; not expected count or arbitrary numeric budget. Source: arxiv-2607.25492v2 PDF p.6; arxiv-2607.25492v2 PDF p.23; arxiv-2607.25492v2 PDF p.24.
-- source:
--   prove2quantum Lean library, module QAlgorithms.Defs.FiniteVectorSamplingPrograms

import Definitions.Def_QAlgorithms_Defs_HeavyTailSamplingData
import Definitions.Def_QAlgorithms_Defs_FiniteOraclePrograms
import Definitions.Def_QAlgorithms_Defs_QuantumInstruments

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.HeavyTail

/-- Oracle-independent operations, plain O/O† queries, finite-outcome measurement instruments and terminal vector estimates. Observed values such as ζ may select subsequent known circuits. Extend retained-query semantics with vector output; reuse FiniteOracleStep with control=false and QuantumInstrument. Program fields contain operations/decoding, never desired accuracy or budget guarantees. Source: arxiv-2607.25492v2 PDF p.7; arxiv-2607.25492v2 PDF p.19; arxiv-2607.25492v2 PDF p.24. -/
inductive SamplingProgram (d : ℕ) (J I : Type) [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] where
  | output (v : EuclideanSpace ℝ (Fin d))
  | apply (step : FiniteOracleStep (fun _ : Fin 1 => J) (fun _ => false) I)
      (next : SamplingProgram d J I)
  | measure (outcomes : ℕ) (M : CopyMeasurements.QuantumInstrument I (Fin outcomes))
      (next : Fin outcomes → SamplingProgram d J I)
  /-- Discard the old registers, prepare the specified basis reference, make one
  plain forward sampler call, measure computational basis, retain only `read`,
  and reset the registers. An explicit operation, not a supplied sampling law.
  Source: arxiv-2607.25492v2 PDF pp.4,7,24. -/
  | sample (zero : I) (work : ℕ) (layout : I ≃ J × Fin work)
      (outcomes : ℕ) (read : J → Fin outcomes)
      (next : Fin outcomes → SamplingProgram d J I)

/-- Computed finite Born/Kraus law of returned decoded vector and counted forward/inverse sampler applications; known operations do not contribute queries. Source: arxiv-2607.25492v2 PDF p.6; arxiv-2607.25492v2 PDF p.23; arxiv-2607.25492v2 PDF p.24. -/
def executionLaw {d : ℕ} {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (O : Matrix J J ℂ) : SamplingProgram d J I → Matrix I I ℂ →
      List ((EuclideanSpace ℝ (Fin d) × Matrix I I ℂ) × ℕ)
  | .output v, rho => [((v,rho),0)]
  | .apply s next, rho =>
    (executionLaw O next (conjSuperop (s.mat (fun _ => O)) rho)).map fun l =>
      (l.1,l.2 + match s with | .known _ => 0 | .query _ _ _ _ => 1 | .controlledQuery _ _ _ _ _ => 1)
  | .measure _ M next, rho => (List.finRange _).flatMap fun z =>
      executionLaw O (next z) (CopyMeasurements.instrumentBranch M z rho)
  | .sample zero work layout _ read next, rho =>
    let reset := pureDensity (ket zero)
    let step : FiniteOracleStep (fun _ : Fin 1 => J) (fun _ => false) I :=
      .query 0 false work layout
    let prepared := conjSuperop (step.mat (fun _ => O)) (rho.trace • reset)
    (Finset.univ.toList : List I).flatMap fun i =>
      (executionLaw O (next (read (layout i).1)) (prepared i i • reset)).map
        fun l => (l.1, l.2 + 1)

/-- Substitute a classical continuation at each returned estimate, retaining
state and actual queries. Source: arxiv-2607.25492v2 PDF p.7. -/
def SamplingProgram.bind {d : ℕ} {J I : Type} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (P : SamplingProgram d J I)
    (f : EuclideanSpace ℝ (Fin d) → SamplingProgram d J I) : SamplingProgram d J I :=
  match P with
  | .output v => f v
  | .apply step next => .apply step (next.bind f)
  | .measure outcomes M next => .measure outcomes M (fun z => (next z).bind f)
  | .sample zero work layout outcomes read next =>
      .sample zero work layout outcomes read (fun z => (next z).bind f)

/-- Execute exactly `n` fresh reset/query/measure operations, storing only the
publicly decoded observations in chronological order. Source:
arxiv-2607.25492v2 PDF pp.4,5,7. -/
def measuredSamples {d : ℕ} {J I : Type} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (zero : I) (work : ℕ) (layout : I ≃ J × Fin work)
    (outcomes : ℕ) (read : J → Fin outcomes)
    (decode : Fin outcomes → EuclideanSpace ℝ (Fin d)) :
    (n : ℕ) → ((Fin n → EuclideanSpace ℝ (Fin d)) → SamplingProgram d J I) →
      SamplingProgram d J I
  | 0, next => next (fun i => Fin.elim0 i)
  | n+1, next => .sample zero work layout outcomes read fun z =>
      measuredSamples zero work layout outcomes read decode n
        (fun tail => next (Fin.cons (decode z) tail))

/-- Sum the computed execution branch probabilities for decoded estimates in the supplied event. Success for every compatible hidden distribution/oracle is a theorem. Source: arxiv-2607.25492v2 PDF p.6; arxiv-2607.25492v2 PDF p.23; arxiv-2607.25492v2 PDF p.24. -/
def outputProbability {d : ℕ} {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (P : SamplingProgram d J I) (O : Matrix J J ℂ) (_unitary : O ∈ Matrix.unitaryGroup J ℂ)
    (rho : Matrix I I ℂ) (_density : IsDensityMatrix rho)
    (event : EuclideanSpace ℝ (Fin d) → Prop) : ℝ :=
  ((executionLaw O P rho).map fun l => if event l.1.1 then l.1.2.trace.re else 0).sum

/-- Maximum actual sampler/adjoint-call counter over positive-probability branches of finite adaptive execution; not expected count or arbitrary numeric budget. Source: arxiv-2607.25492v2 PDF p.6; arxiv-2607.25492v2 PDF p.23; arxiv-2607.25492v2 PDF p.24. -/
def worstCaseQueries {d : ℕ} {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (P : SamplingProgram d J I) (O : Matrix J J ℂ) (_unitary : O ∈ Matrix.unitaryGroup J ℂ)
    (rho : Matrix I I ℂ) (_density : IsDensityMatrix rho) : ℕ :=
  (executionLaw O P rho).foldl (fun q l => if 0 < l.1.2.trace.re then max q l.2 else q) 0

example {d : ℕ} {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (O : Matrix J J ℂ) (hO : O ∈ Matrix.unitaryGroup J ℂ)
    (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho) (v : EuclideanSpace ℝ (Fin d)) :
    worstCaseQueries (.output v) O hO rho hrho = 0 := by simp [worstCaseQueries,executionLaw]

end QAlgorithms.HeavyTail


