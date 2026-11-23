-- Prove2me | Definitions.Def_ITPIRPreproc_MatchVec_CompilerRoundModels
-- name    : ITPIRPreproc_MatchVec_CompilerRoundModels
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:33:37.628913+00:00
-- url     : https://prove2.me/theorems/d16c8414-505e-4e0e-b178-511cc3ff95ac
-- title:
--   Conditional round interfaces for the §4.2 compiler
-- statement:
--   This module supplies two reusable conditional-probability interfaces for the generic compiler of §4.2.
--
--   For a scheme $S$, `IndexUniformStep` says that after fixing a query prefix, an event of the adversary's coins, and the current target $i$, the next-query law does not depend on $i$, the adversary, or its coins:
--   $$
--   \Pr[B,\ H_j=qs,\ A(\alpha,qs)=i,\ Q_j=q]
--    =\Pr[B,\ H_j=qs,\ A(\alpha,qs)=i]\,\operatorname{step}_j(qs,q).
--   $$
--   This is the per-index form of the uniform-bank and uniform-query argument. Measurability of the conditioning events is included explicitly.
--
--   `FailureModeled` isolates the correctness calculation. On each positive-probability query prefix it supplies a probability space with $s$ events $B_\ell$ such that each has measure at most $7/8$, their measures multiply on their intersection, and decoding failure is contained in $\bigcap_\ell B_\ell$. Consequently its modeled failure probability is at most $(7/8)^s$. Prefixes are required to be measurable so that these conditional bounds can be summed to an unconditional per-round bound.
--
--   The sample type `Fin s → Fin 8` is merely a common finite type: the probability measure and events are unrestricted, so this does not require each bad event to have probability exactly $7/8$. Positive-prefix conditioning avoids division by zero.
--
--   **Formalization Note** These interfaces deliberately stop short of `StepPrivate` and `PerRoundCorrect`: separate transfer theorems perform the adaptive-prefix and independent-pool probability arguments.
-- source:
--   Dujmovic--Lai--Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572, §4.2, printed pp.12--15 (PDF pp.14--17): the per-pool conditional privacy invariant and the independent failure events in the correctness proof.

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_CompilerInvariants
import Definitions.Def_ITPIRPreproc_MatchVec_Efficiency

open MeasureTheory
open scoped ENNReal

namespace ITPIRPreproc.MatchVec

/-- The query prefix of length `j`, before retrieval `j`. -/
def queryPrefix (S : Scheme) (n lam : ℕ) (D : Fin n → Bool) (A : Adversary n)
    (j : ℕ) (qs : List (List Bool)) : Set Tapes :=
  {ω | (history S n lam D A ω j).map Round.query = qs}

/-- The same prefix, together with an adversary-coin event and the current target `i`. -/
def indexedPrefix (S : Scheme) (n lam : ℕ) (D : Fin n → Bool) (A : Adversary n)
    (j : ℕ) (B : Set (ℕ → Bool)) (qs : List (List Bool)) (i : Fin n) : Set Tapes :=
  {ω | tape ω 0 ∈ B ∧ A (tape ω 0) qs = i ∧ ω ∈ queryPrefix S n lam D A j qs}

/-- Conditional on any fixed query prefix and on the current target, the next query has a law
which is independent of the target, the adversary and its coins. This is the per-index form of
the bank invariant in §4.2. The measurability clauses permit the finite target and countable
prefix decompositions used by the probability proofs. -/
def IndexUniformStep (S : Scheme) (n lam : ℕ) : Prop :=
  ∀ D : Fin n → Bool, ∃ step : ℕ → List (List Bool) → List Bool → ℝ≥0∞,
    (∀ (A : Adversary n), A.IsMeasurable → ∀ (j : ℕ) (B : Set (ℕ → Bool)),
      MeasurableSet B → ∀ (qs : List (List Bool)) (i : Fin n),
        MeasurableSet (indexedPrefix S n lam D A j B qs i)) ∧
    (∀ (A : Adversary n), A.IsMeasurable → ∀ (j : ℕ) (B : Set (ℕ → Bool)),
      MeasurableSet B → ∀ (qs : List (List Bool)) (q : List Bool) (i : Fin n),
        MeasurableSet (indexedPrefix S n lam D A j B qs i ∩
          {ω | (roundAt S n lam D A ω j).query = q})) ∧
    ∀ (A : Adversary n), A.IsMeasurable → ∀ (j : ℕ) (B : Set (ℕ → Bool)),
      MeasurableSet B → ∀ (qs : List (List Bool)) (q : List Bool) (i : Fin n),
        tapeLaw (indexedPrefix S n lam D A j B qs i ∩
            {ω | (roundAt S n lam D A ω j).query = q}) =
          tapeLaw (indexedPrefix S n lam D A j B qs i) * step j qs q

/-- A probability model of one retrieval's `s` independent unsuccessful pool attempts. An
actual decoding failure is contained in the intersection of all `bad` events. Independence and
the individual bounds imply failure probability at most `(7/8)^s`. The finite type
`Fin s → Fin 8` is only a convenient common sample type; the measure and events are arbitrary. -/
structure IndependentPoolFailure (s : ℕ) where
  μ : Measure (Fin s → Fin 8)
  prob : IsProbabilityMeasure μ
  failure : Set (Fin s → Fin 8)
  bad : Fin s → Set (Fin s → Fin 8)
  failure_subset : failure ⊆ Set.iInter fun ℓ => bad ℓ
  bad_le : ∀ ℓ, μ (bad ℓ) ≤ (7 / 8 : ℝ≥0∞)
  bad_indep : μ (Set.iInter fun ℓ => bad ℓ) = ∏ ℓ, μ (bad ℓ)

/-- For every positive-probability query prefix, the actual conditional failure law has an
independent-pool model. Requiring this only on positive prefixes avoids any division by zero.
The measurable-prefix clause allows reconstruction of the unconditional per-round bound. -/
def FailureModeled (S : Scheme) (n lam s : ℕ) : Prop :=
  ∀ (D : Fin n → Bool) (A : Adversary n), A.IsMeasurable → ∀ j : ℕ,
    (∀ qs : List (List Bool), MeasurableSet (queryPrefix S n lam D A j qs)) ∧
    ∀ qs : List (List Bool), 0 < tapeLaw (queryPrefix S n lam D A j qs) →
      ∃ M : IndependentPoolFailure s,
        tapeLaw (queryPrefix S n lam D A j qs ∩
            {ω | RoundFailure S n lam D A ω j}) =
          tapeLaw (queryPrefix S n lam D A j qs) * M.μ M.failure

end ITPIRPreproc.MatchVec


