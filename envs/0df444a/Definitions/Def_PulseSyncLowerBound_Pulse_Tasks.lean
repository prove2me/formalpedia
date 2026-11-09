-- Prove2me | Definitions.Def_PulseSyncLowerBound_Pulse_Tasks
-- name    : PulseSyncLowerBound_Pulse_Tasks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:59:37.510288+00:00
-- url     : https://prove2.me/theorems/307ed76d-efe6-49cb-acc4-dfae171f9e51
-- title:
--   Pulse intervals, integer lifts, and non-trivial counting
-- statement:
--   For a real skew $\sigma\ge1$ and natural stabilisation bound $T$, every permitted execution must admit infinitely many integer intervals $[a_k,b_k]$ with $a_0\le T$. Each interval has width at most $\sigma$ and contains exactly one pulse of each never-crashing process. Consecutive intervals satisfy $a_{k+1}>b_k+\sigma$, with no non-faulty pulse strictly between them. There is no upper bound on a later gap.
--
--   For natural $\sigma$ and $q>\max\{2\sigma,1\}$, a lift of counting outputs agrees modulo $q$, has pairwise distance at most $\sigma$, and has increments in $[0,q)$. N1 requires such a lift in every execution with at most $f$ total crashes. N2 requires one crash-free infinite execution and one process whose output changes infinitely often. Non-trivial counting is their conjunction.
--
--   These predicates impose task correctness on the separate operational model. Lift witnesses on natural times extend arbitrarily to earlier negative integer times; no lift condition is imposed there or before $T$.
-- source:
--   Joel Rybicki, STOC 2027 submission #508 (October 2026), pinned published-basis artifact; Definitions 1, 4, 5; PDF p.5,7 / printed p.3,5; papers/stoc2027-508/source.pdf; SHA-256 5237f877941c17d0913977954f4f4b6ccba70f65ceae5dc47f15029dbd68765f.

import Definitions.Def_PulseSyncLowerBound_Pulse_Model

noncomputable section

namespace PulseSyncLowerBound.Pulse

variable {n : ℕ}

/-- A pulse in round zero is evaluated on the arbitrary initial state too. -/
def Pulses {P : Protocol n Bool} (e : Execution P) (i : Fin n) (t : ℕ) : Prop :=
  ∃ s, e.config t i = some s ∧ P.output i s = true

/-- Definition 1, PDF 5 / printed 3: the first interval starts by T;
no upper bound is imposed on any later pulse gap. -/
def PulseExecution {P : Protocol n Bool} (e : Execution P) (σ : ℝ) (T : ℕ) : Prop :=
  ∃ a b : ℕ → ℕ, a 0 ≤ T ∧ ∀ k,
    a k ≤ b k ∧ (b k : ℝ) - (a k : ℝ) ≤ σ ∧
    (∀ i, Nonfaulty e i → ∃! t : ℕ, a k ≤ t ∧ t ≤ b k ∧ Pulses e i t) ∧
    (b k : ℝ) + σ < (a (k + 1) : ℝ) ∧
    (∀ i, Nonfaulty e i → ∀ t, b k < t → t < a (k + 1) → ¬ Pulses e i t)

def PulseResilient (P : Protocol n Bool) (f : ℕ) (σ : ℝ) (T : ℕ) : Prop :=
  ∀ e : Execution P, AtMostCrashes e f → PulseExecution e σ T

/-- Definition 4, PDF 7 / printed 5. Only non-faulty processes and t ≥ T
are constrained; natural-time witnesses extend arbitrarily to negative integers. -/
def HasLift {q : ℕ} {P : Protocol n (Fin q)} (e : Execution P) (σ T : ℕ) : Prop :=
  ∃ L : Fin n → ℕ → ℤ, ∀ t, T ≤ t →
    (∀ i, Nonfaulty e i → ∀ s, e.config t i = some s →
      (P.output i s : ℤ) = L i t % (q : ℤ)) ∧
    (∀ i j, Nonfaulty e i → Nonfaulty e j → |L i t - L j t| ≤ (σ : ℤ)) ∧
    (∀ i, Nonfaulty e i →
      0 ≤ L i (t + 1) - L i t ∧ L i (t + 1) - L i t < (q : ℤ))

/-- N1 alone; no progress conclusion is assumed. -/
def LiftResilient {q : ℕ} (P : Protocol n (Fin q)) (f σ T : ℕ) : Prop :=
  ∀ e : Execution P, AtMostCrashes e f → HasLift e σ T

/-- N2 is existential over a crash-free infinite run and one process. -/
def Nontrivial {q : ℕ} (P : Protocol n (Fin q)) : Prop :=
  ∃ e : Execution P, AtMostCrashes e 0 ∧ ∃ i : Fin n, ∀ N : ℕ, ∃ t ≥ N,
    ∃ s s', e.config t i = some s ∧ e.config (t + 1) i = some s' ∧
      P.output i s ≠ P.output i s'

def CountingResilient {q : ℕ} (P : Protocol n (Fin q)) (f σ T : ℕ) : Prop :=
  LiftResilient P f σ T ∧ Nontrivial P

end PulseSyncLowerBound.Pulse


