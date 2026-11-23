-- Prove2me | Definitions.Def_ITPIRPreproc_MatchVec_CompilerInvariants
-- name    : ITPIRPreproc_MatchVec_CompilerInvariants
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:44:45.945609+00:00
-- url     : https://prove2.me/theorems/5e8588fc-0b6f-44ef-a2e7-0612ddad2bcb
-- title:
--   One-round interfaces for the §4.2 OCHP-to-PIR compiler
-- statement:
--   This module isolates the one-round quantities in the adaptive experiment of §3 that are used by the proof of the compiler in §4.2.
--
--   For round $j\ge0$ (zero-based), `roundAt` is the complete retrieval record produced from the preceding history and the independent coins assigned to that round. `RoundFailure` is the event that its decoded value is not the requested database bit.
--
--   `StepPrivate` asserts the paper's one-step privacy invariant in distribution-factorization form: for every prefix of queries, there is an adversary-independent law for the next query, and the joint probability of the adversary's coins, the prefix and the next query factors into the coin probability, the prefix probability and that law. No division by a prefix probability occurs, so zero-probability prefixes are included.
--
--   Finally, `PerRoundCorrect S n lam δ` says that each individual round has failure probability at most $\delta$. The compiler proof first establishes this stronger assertion and then applies a union bound over $T$ rounds.
--
--   **Formalization Note** These are proof interfaces for §4.2, not additional cryptographic assumptions on a scheme.
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572 (October 2026), Lemma 4.2 proof, printed pp.14–15 (PDF pp.16–17), privacy invariant and per-pool correctness argument; adaptive experiment of §3, printed p.10 (PDF p.12).

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_Model

open MeasureTheory
open scoped ENNReal

namespace ITPIRPreproc.MatchVec

open WordRAM

/-- Retrieval round `j`, indexed from zero, with all coins and the adaptive adversary made
explicit. -/
noncomputable def roundAt (S : Scheme) (n lam : ℕ) (D : Fin n → Bool) (A : Adversary n)
    (ω : Tapes) (j : ℕ) : Round n :=
  let h := history S n lam D A ω j
  runRound S n lam D (currentState S n lam D ω h)
    (A (tape ω 0) (h.map Round.query)) (tape ω (j + 2))

/-- Failure of the `j`-th retrieval: the decoder's output is not the requested database bit. -/
def RoundFailure (S : Scheme) (n lam : ℕ) (D : Fin n → Bool) (A : Adversary n)
    (ω : Tapes) (j : ℕ) : Prop :=
  (roundAt S n lam D A ω j).output ≠ some (D (roundAt S n lam D A ω j).index)

/-- One-step query factorization: conditioned on a query prefix, the next query has an
adversary-independent simulator law. The prefix probability is unnormalized, so the assertion
also makes sense when that prefix has probability zero. -/
def StepPrivate (S : Scheme) (n lam : ℕ) : Prop :=
  ∀ D : Fin n → Bool, ∃ step : ℕ → List (List Bool) → List Bool → ℝ≥0∞,
    ∀ (A : Adversary n), A.IsMeasurable → ∀ (j : ℕ) (B : Set (ℕ → Bool)), MeasurableSet B →
      ∀ (qs : List (List Bool)) (q : List Bool),
        tapeLaw {ω | tape ω 0 ∈ B ∧ (history S n lam D A ω j).map Round.query = qs ∧
          (roundAt S n lam D A ω j).query = q} =
          coinTape B * tapeLaw {ω | (history S n lam D A ω j).map Round.query = qs} *
            step j qs q

/-- The error of every individual retrieval round is at most `δ`. -/
def PerRoundCorrect (S : Scheme) (n lam : ℕ) (δ : ℝ≥0∞) : Prop :=
  ∀ (D : Fin n → Bool) (A : Adversary n), A.IsMeasurable → ∀ j : ℕ,
    tapeLaw {ω | RoundFailure S n lam D A ω j} ≤ δ

@[simp] lemma history_succ_roundAt (S : Scheme) (n lam : ℕ) (D : Fin n → Bool) (A : Adversary n)
    (ω : Tapes) (j : ℕ) :
    history S n lam D A ω (j + 1) = history S n lam D A ω j ++ [roundAt S n lam D A ω j] := by
  rfl

end ITPIRPreproc.MatchVec


