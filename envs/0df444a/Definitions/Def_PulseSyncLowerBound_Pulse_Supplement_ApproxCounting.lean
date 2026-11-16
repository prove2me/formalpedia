-- Prove2me | Definitions.Def_PulseSyncLowerBound_Pulse_Supplement_ApproxCounting
-- name    : PulseSyncLowerBound_Pulse_Supplement_ApproxCounting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:29:55.547689+00:00
-- url     : https://prove2.me/theorems/c72ce10f-2b63-4b59-946c-501421d48a2c
-- title:
--   Definition 3 — σ-paths and σ-approximate q-counting
-- statement:
--   Work in the synchronous crash-fault model of the base mission: $n$ processes with permanent identities, finite nonempty local state sets, a deterministic time-independent transition, every initial configuration allowed, and $f$-resilience counted as the number of processes that ever crash in the infinite execution. A process is non-faulty if it never crashes. Let the outputs be $\varphi(i,t)\in\mathbb Z_q=\{0,1,\dots,q-1\}$.
--
--   For $\sigma\in\mathbb N$, a set $I\subseteq\mathbb Z_q$ is a **$\sigma$-path** if
--
--   $$I=\{c+k \bmod q : 0\le k\le\sigma\}\quad\text{for some } c\in\mathbb Z_q,$$
--
--   that is, an arc of $\sigma+1$ consecutive residues of the $q$-cycle read in the increasing direction.
--
--   Let $\Phi(t)$ be the set of outputs of the non-faulty processes in round $t$. A protocol is an **$f$-resilient $\sigma$-approximate $q$-counting protocol that stabilises in $T$ rounds** if every execution with at most $f$ crashes satisfies, for all $t\ge T$:
--
--   1. (A1) $\sigma$-agreement: $\Phi(t)$ is contained in some $\sigma$-path of $\mathbb Z_q$;
--   2. (A2) progress: $\varphi(i,t+1)=\varphi(i,t)+1 \bmod q$ for every non-faulty process $i$.
--
--   For $\sigma=0$ this is exact synchronous counting; for $\sigma\ge1$ it is a self-stabilising analogue of cycle agreement. It is the task solved by the upper bound of Section 7 (Theorem 20).
--
--   **Formalization Note** The source states the definition for $q>\max\{2\sigma,1\}$; this range is a parameter assumption of the theorems that use the predicate, not a clause of the predicate, so it cannot make the predicate vacuous. Outputs are `Fin q`; the output of process $i$ in round $t$ is the protocol's output map applied to its state `e.config t i`. The model (`Protocol`, `Execution`, `Nonfaulty`, `AtMostCrashes`) is the published base definition `PulseSyncLowerBound_Pulse_Model`, imported unchanged.
-- source:
--   Joel Rybicki, STOC 2027 submission #508 (October 2026), pinned published-basis artifact; §2.2.1, σ-path and Definition 3; PDF p.6 / printed p.4; papers/stoc2027-508/source.pdf; SHA-256 5237f877941c17d0913977954f4f4b6ccba70f65ceae5dc47f15029dbd68765f. Model: §2, PDF p.5 / printed p.3.

import Definitions.Def_PulseSyncLowerBound_Pulse_Model

noncomputable section

namespace PulseSyncLowerBound.Pulse.Supplement

open PulseSyncLowerBound.Pulse

variable {n : ℕ}

/-- §2.2.1, PDF 6 / printed 4: `I ⊆ Z_q` is a σ-path if
`I = {c + k mod q : 0 ≤ k ≤ σ}` for some `c ∈ Z_q`, a clockwise arc of σ + 1 residues. -/
def SigmaPath (q σ : ℕ) (c : Fin q) : Set (Fin q) :=
  {x | ∃ k : ℕ, k ≤ σ ∧ (x : ℕ) = ((c : ℕ) + k) % q}

/-- Φ(t): the outputs of the non-faulty (never-crashing) processes in round t. -/
def NonfaultyOutputs {q : ℕ} {P : Protocol n (Fin q)} (e : Execution P) (t : ℕ) :
    Set (Fin q) :=
  {x | ∃ i, Nonfaulty e i ∧ ∃ s, e.config t i = some s ∧ P.output i s = x}

/-- Definition 3, PDF 6 / printed 4, for one execution: for all t ≥ T,
(A1) Φ(t) is contained in some σ-path of Z_q, and
(A2) every non-faulty process advances its output by one modulo q.
The source's side condition q > max{2σ, 1} is a parameter range, not part of the predicate. -/
def ApproxCountingExecution {q : ℕ} {P : Protocol n (Fin q)} (e : Execution P)
    (σ T : ℕ) : Prop :=
  ∀ t, T ≤ t →
    (∃ c : Fin q, NonfaultyOutputs e t ⊆ SigmaPath q σ c) ∧
    (∀ i, Nonfaulty e i → ∀ s s', e.config t i = some s → e.config (t + 1) i = some s' →
      (P.output i s' : ℕ) = ((P.output i s : ℕ) + 1) % q)

/-- Definition 3: `P` is an f-resilient σ-approximate q-counting protocol that stabilises
in T rounds: every execution with at most f crashes satisfies A1 and A2 from round T on. -/
def ApproxCountingResilient {q : ℕ} (P : Protocol n (Fin q)) (f σ T : ℕ) : Prop :=
  ∀ e : Execution P, AtMostCrashes e f → ApproxCountingExecution e σ T

end PulseSyncLowerBound.Pulse.Supplement


