-- Prove2me | Definitions.Def_QAlgorithms_Defs_RetainedQueryPrograms
-- name    : QAlgorithms_Defs_RetainedQueryPrograms
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:23:10.856488+00:00
-- url     : https://prove2.me/theorems/ba3f3c61-afb5-45f8-8177-35c611e81f7f
-- title:
--   RetainedQueryPrograms
-- statement:
--   RetainedQueryPrograms
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\RetainedQueryPrograms.lean

import Definitions.Def_QAlgorithms_Defs_QuantumInstruments
import Definitions.Def_QAlgorithms_Defs_FiniteOraclePrograms
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.RetainedOracle

/-- QAlgorithms.RetainedOracle.QueryProgram: arxiv-2609.35660v1 PDF p.1, arxiv-2609.35660v1 PDF p.9, arxiv-2609.35660v1 PDF p.10, arxiv-2609.35660v1 PDF p.16. Source domains are explicit below. -/
inductive QueryProgram {r : ℕ} (J : Fin r → Type) [∀ k, Fintype (J k)]
    [∀ k, DecidableEq (J k)] (control : Fin r → Bool)
    (I : Type) [Fintype I] [DecidableEq I] where
  | halt (success : Bool)
  | apply (step : FiniteOracleStep J control I) (next : QueryProgram J control I)
  | instrument (outcomes : ℕ) (M : CopyMeasurements.QuantumInstrument I (Fin outcomes))
      (next : Fin outcomes → QueryProgram J control I)

/-- QAlgorithms.RetainedOracle.QueryLeaf: arxiv-2609.35660v1 PDF p.1, arxiv-2609.35660v1 PDF p.9, arxiv-2609.35660v1 PDF p.10, arxiv-2609.35660v1 PDF p.16. Source domains are explicit below. -/
abbrev QueryLeaf (I : Type) := (Bool × Matrix I I ℂ) × ℕ

/-- QAlgorithms.RetainedOracle.queryProgramLaw: arxiv-2609.35660v1 PDF p.1, arxiv-2609.35660v1 PDF p.9, arxiv-2609.35660v1 PDF p.10, arxiv-2609.35660v1 PDF p.16. Source domains are explicit below. -/
def queryProgramLaw {r : ℕ} {J : Fin r → Type} [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)]
    {control : Fin r → Bool} {I : Type} [Fintype I] [DecidableEq I]
    (O : (k : Fin r) → Matrix (J k) (J k) ℂ) (weight : Fin r → ℕ) :
    QueryProgram J control I → Matrix I I ℂ → List (QueryLeaf I)
  | .halt b, rho => [((b,rho),0)]
  | .apply step next, rho =>
      (queryProgramLaw O weight next (conjSuperop (step.mat O) rho)).map fun leaf =>
        (leaf.1,leaf.2+match step with
          | .known _ => 0
          | .query k _ _ _ => weight k
          | .controlledQuery k _ _ _ _ => weight k)
  | .instrument _ M next, rho => (List.finRange _).flatMap fun o =>
      queryProgramLaw O weight (next o) (CopyMeasurements.instrumentBranch M o rho)

/-- QAlgorithms.RetainedOracle.worstCaseQueries: arxiv-2609.35660v1 PDF p.1, arxiv-2609.35660v1 PDF p.9, arxiv-2609.35660v1 PDF p.16. Source domains are explicit below. -/
def worstCaseQueries {r : ℕ} {J : Fin r → Type} [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)]
    {control : Fin r → Bool} {I : Type} [Fintype I] [DecidableEq I]
    (P : QueryProgram J control I) (O : (k : Fin r) → Matrix (J k) (J k) ℂ)
    (weight : Fin r → ℕ) (rho : Matrix I I ℂ) : ℕ :=
  ((queryProgramLaw O weight P rho).filter fun leaf => decide (0 < leaf.1.2.trace.re)).foldl
    (fun maximum leaf => max maximum leaf.2) 0

/-- QAlgorithms.RetainedOracle.retainedOutput: arxiv-2609.35660v1 PDF p.1, arxiv-2609.35660v1 PDF p.9, arxiv-2609.35660v1 PDF p.10, arxiv-2609.35660v1 PDF p.16. Source domains are explicit below. -/
def retainedOutput {r : ℕ} {J : Fin r → Type} [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)]
    {control : Fin r → Bool} {I : Type} [Fintype I] [DecidableEq I] {N w : ℕ}
    (layout : I ≃ Fin N × Fin w) (P : QueryProgram J control I)
    (O : (k : Fin r) → Matrix (J k) (J k) ℂ) (rho : Matrix I I ℂ) (b : Bool) :
    Matrix (Fin N) (Fin N) ℂ :=
  traceRight (((queryProgramLaw O (fun _ => 0) P rho).map
    (fun (leaf : QueryLeaf I) => if leaf.1.1 = b then leaf.1.2 else 0)).sum |>.submatrix layout.symm layout.symm)

example {r : ℕ} {J : Fin r → Type} [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)]
    {control : Fin r → Bool} {I : Type} [Fintype I] [DecidableEq I]
    (O : (k : Fin r) → Matrix (J k) (J k) ℂ) (weight : Fin r → ℕ) (rho : Matrix I I ℂ) :
    queryProgramLaw O weight (.halt false : QueryProgram J control I) rho = [((false,rho),0)] := rfl

end QAlgorithms.RetainedOracle


