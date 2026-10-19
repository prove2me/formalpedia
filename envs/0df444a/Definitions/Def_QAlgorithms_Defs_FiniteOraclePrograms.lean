-- Prove2me | Definitions.Def_QAlgorithms_Defs_FiniteOraclePrograms
-- name    : QAlgorithms_Defs_FiniteOraclePrograms
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:20:37.29398+00:00
-- url     : https://prove2.me/theorems/da7d45dc-0f96-42b2-a827-7e4a0719c488
-- title:
--   FiniteOraclePrograms
-- statement:
--   FiniteOraclePrograms
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\FiniteOraclePrograms.lean

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
import Definitions.Def_QAlgorithms_Defs_SamplingUtilities
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms

/-- Known full-register unitary or named oracle slot, explicit finite-register factorization/permutation into oracle and untouched work factors, and forward/adjoint flag. Source: arxiv-2111.09787v2 PDF p.7; arxiv-1504.06987v3 PDF p.8. -/
inductive FiniteOracleStep {r : ℕ} (J : Fin r → Type) [∀ k, Fintype (J k)]
    [∀ k, DecidableEq (J k)] (allowControl : Fin r → Bool)
    (I : Type) [Fintype I] [DecidableEq I] where
  | known (U : Matrix.unitaryGroup I ℂ)
  | query (k : Fin r) (adjoint : Bool) (w : ℕ) (layout : I ≃ J k × Fin w)
  | controlledQuery (k : Fin r) (allowed : allowControl k = true) (adjoint : Bool)
      (w : ℕ) (layout : I ≃ Bool × (J k × Fin w))

/-- Compute the lifted actual matrix of the known or named-query step using its finite factorization and forward/adjoint flag. Source: arxiv-2111.09787v2 PDF p.7; arxiv-1504.06987v3 PDF p.8. -/
def FiniteOracleStep.mat {r : ℕ} {J : Fin r → Type} [∀ k, Fintype (J k)]
    [∀ k, DecidableEq (J k)] {ctl : Fin r → Bool} {I : Type} [Fintype I] [DecidableEq I]
    (O : (k : Fin r) → Matrix (J k) (J k) ℂ) :
    FiniteOracleStep J ctl I → Matrix I I ℂ
  | .known U => U
  | .query k adj w layout =>
      (Matrix.kronecker (if adj then star (O k) else O k) (1 : Matrix (Fin w) (Fin w) ℂ)).submatrix layout layout
  | .controlledQuery k _ adj w layout =>
      (controlled (Matrix.kronecker (if adj then star (O k) else O k)
        (1 : Matrix (Fin w) (Fin w) ℂ))).submatrix layout layout

/-- A list of FiniteOracleStep, applied chronologically. Source: arxiv-2111.09787v2 PDF p.7; arxiv-1504.06987v3 PDF p.8. -/
abbrev FiniteOracleCircuit {r : ℕ} (J : Fin r → Type) [∀ k, Fintype (J k)]
    [∀ k, DecidableEq (J k)] (ctl : Fin r → Bool) (I : Type) [Fintype I] [DecidableEq I] :=
  List (FiniteOracleStep J ctl I)

/-- Evaluate the concrete step list as its reversed matrix product, so first listed step acts first. Source: arxiv-2111.09787v2 PDF p.7; arxiv-1504.06987v3 PDF p.8. -/
def FiniteOracleCircuit.unitary {r : ℕ} {J : Fin r → Type} [∀ k, Fintype (J k)]
    [∀ k, DecidableEq (J k)] {ctl : Fin r → Bool} {I : Type} [Fintype I] [DecidableEq I]
    (c : FiniteOracleCircuit J ctl I) (O : (k : Fin r) → Matrix (J k) (J k) ℂ) : Matrix I I ℂ :=
  (c.map (FiniteOracleStep.mat O)).reverse.prod

/-- Count occurrences of the specified oracle slot in the actual list; adjoints and authorized controls each count one. Source: arxiv-2111.09787v2 PDF p.7; arxiv-1504.06987v3 PDF p.8. -/
def FiniteOracleCircuit.queryCount {r : ℕ} {J : Fin r → Type} [∀ k, Fintype (J k)]
    [∀ k, DecidableEq (J k)] {ctl : Fin r → Bool} {I : Type} [Fintype I] [DecidableEq I]
    (c : FiniteOracleCircuit J ctl I) (k : Fin r) : ℕ :=
  c.countP fun s => match s with
    | .known _ => false
    | .query j _ _ _ => decide (j = k)
    | .controlledQuery j _ _ _ _ => decide (j = k)

/-- Operational helper FiniteEstimatorRound for the source construction. Source: arxiv-2111.09787v2 PDF p.7; arxiv-1504.06987v3 PDF p.8. -/
structure FiniteEstimatorRound {r : ℕ} (J : Fin r → Type) [∀ k, Fintype (J k)]
    [∀ k, DecidableEq (J k)] (ctl : Fin r → Bool) (S I : Type)
    [Fintype S] [Fintype I] [DecidableEq I] where
  copies : ℕ
  anc : ℕ
  layout : I ≃ (Fin copies → S) × Qubits anc
  circuit : FiniteOracleCircuit J ctl I

/-- An oracle algorithm on finite sample/value/work registers with a fixed zero start, oracle-independent unitary steps, U_P or U_P† steps, B_X or B_X† steps, and computational-basis measurement/classical processing. Source: arxiv-2111.09787v2 PDF p.7; arxiv-2111.09787v2 PDF p.10; arxiv-2111.09787v2 PDF p.11. -/
structure FiniteQuantumEstimator {r : ℕ} (J : Fin r → Type) [∀ k, Fintype (J k)]
    [∀ k, DecidableEq (J k)] (ctl : Fin r → Bool) (S I A : Type)
    [Fintype S] [Fintype I] [DecidableEq I] where
  rounds : List (FiniteEstimatorRound J ctl S I)
  decode : (Fin rounds.length → I) → A

/-- For an estimator's fixed round/repetition program count fresh supplied sampler-state preparations/copies actually consumed; sum over repetitions. Source: arxiv-1504.06987v3 PDF p.8. -/
def finiteEstimatorCopyCount {r : ℕ} {J : Fin r → Type} [∀ k, Fintype (J k)]
    [∀ k, DecidableEq (J k)] {ctl : Fin r → Bool} {S I A : Type}
    [Fintype S] [Fintype I] [DecidableEq I] (E : FiniteQuantumEstimator J ctl S I A) : ℕ :=
  (E.rounds.map fun q => q.copies).sum

/-- Aggregate FiniteOracleCircuit.queryCount over actual estimator rounds/repetitions, separately for each slot. Source: arxiv-2111.09787v2 PDF p.7; arxiv-2111.09787v2 PDF p.11; arxiv-1504.06987v3 PDF p.8. -/
def finiteEstimatorQueryCount {r : ℕ} {J : Fin r → Type} [∀ k, Fintype (J k)]
    [∀ k, DecidableEq (J k)] {ctl : Fin r → Bool} {S I A : Type}
    [Fintype S] [Fintype I] [DecidableEq I] (E : FiniteQuantumEstimator J ctl S I A) (k : Fin r) : ℕ :=
  (E.rounds.map fun q => q.circuit.queryCount k).sum

/-- The measured circuit's Born law pushed through a declared finite real/vector decoding; independent repetitions use finite product laws and classical median pushforward. Source: arxiv-1504.06987v3 PDF p.8; arxiv-2111.09787v2 PDF p.11. -/
def finiteEstimatorLaw {r : ℕ} {J : Fin r → Type} [∀ k, Fintype (J k)]
    [∀ k, DecidableEq (J k)] {ctl : Fin r → Bool} {S I A : Type}
    [Fintype S] [Fintype I] [DecidableEq I] [DecidableEq A]
    (E : FiniteQuantumEstimator J ctl S I A) (psi : EuclideanSpace ℂ S) (hpsi : IsState psi)
    (O : (k : Fin r) → Matrix (J k) (J k) ℂ)
    (hO : ∀ k, O k ∈ Matrix.unitaryGroup (J k) ℂ) (a : A) : ℝ :=
  ∑ z : Fin E.rounds.length → I, if E.decode z = a then
    ∏ i, let q := E.rounds.get i
         prob (act (q.circuit.unitary O) (WithLp.toLp 2 fun x =>
           if (q.layout x).2 = (fun _ => false)
           then tensorPow q.copies psi (q.layout x).1 else 0)) (z i)
  else 0

/-- Sanity test. Source: arxiv-2111.09787v2 PDF p.7; arxiv-1504.06987v3 PDF p.8. -/
example {r : ℕ} {J : Fin r → Type} [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)]
    (ctl : Fin r → Bool) (I : Type) [Fintype I] [DecidableEq I]
    (O : (k : Fin r) → Matrix (J k) (J k) ℂ) (k : Fin r) :
    FiniteOracleCircuit.unitary ([] : FiniteOracleCircuit J ctl I) O = 1 ∧
      FiniteOracleCircuit.queryCount ([] : FiniteOracleCircuit J ctl I) k = 0 := by constructor <;> rfl

/-- Sanity test. Source: arxiv-2111.09787v2 PDF p.7; arxiv-1504.06987v3 PDF p.8. -/
example {r : ℕ} {J : Fin r → Type} [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)]
    {ctl : Fin r → Bool} {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix.unitaryGroup I ℂ) (O O2 : (k : Fin r) → Matrix (J k) (J k) ℂ) :
    FiniteOracleCircuit.unitary ([.known U] : FiniteOracleCircuit J ctl I) O =
      FiniteOracleCircuit.unitary ([.known U] : FiniteOracleCircuit J ctl I) O2 := rfl

end QAlgorithms


