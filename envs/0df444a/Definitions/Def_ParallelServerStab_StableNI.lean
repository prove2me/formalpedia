-- Prove2me | Definitions.Def_ParallelServerStab_StableNI
-- name    : ParallelServerStab_StableNI
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:23:30.070981+00:00
-- url     : https://prove2.me/theorems/a5067bde-f3f5-4ba6-98df-6258d7df524b
-- title:
--   The ordered queue process under a non-idling $\mathbf p$-allocation policy, and its stability
-- statement:
--   There are $s$ servers, each with its own infinite buffer. Jobs arrive in a Poisson stream of rate $\lambda$, service times are i.i.d. exponential with rate $\mu$, and $\rho=\lambda/(s\mu)$ is the traffic intensity. After every event the servers are relabelled by increasing queue length (the job in service counted), servers with equal queues receiving consecutive labels in uniformly random order. The **ordered queue process** $Q(t)=(Q_1(t),\dots,Q_s(t))$, $Q_1\le\dots\le Q_s$, is then a continuous-time Markov chain.
--
--   Under the **non-idling $\mathbf p$-allocation policy** (Definition 1), for an allocation vector $\mathbf p=(p_1,\dots,p_s)$, an arriving job joins an idle server whenever there is one, and otherwise joins the server of rank $i$ with probability $p_i$. From an ordered state $x$ the chain therefore moves:
--
--   1. at rate $\lambda$, to $x$ with one more job at an idle server, if some server is idle;
--   2. otherwise at rate $\lambda p_i$, to the re-sorted vector $\mathcal R(x+e_i)$, for each rank $i$;
--   3. at rate $\mu$, to $\mathcal R(x-e_i)$, for each rank $i$ with $x_i\ge1$.
--
--   Its exit rate is $\lambda+\mu\cdot\#\{i: x_i\ge1\}$. The system is **stable** (the paper's $\rho\in S^{NI}(\mathbf p)$) when $Q$ is positive recurrent; here this means that the chain started empty returns to the empty state with probability one and the expected return time is finite.
--
--   This is the model of all stability statements of the mission: Theorem 2 and Proposition 2 bound the set of $\rho$ for which the system is stable under $\mathbf p_{p,2}$.
--
--   **Formalization Note** States are monotone vectors `Fin s → ℕ` with 0-based ranks. Re-sorting is built in: `arrive x i` adds the job at the last rank of $i$'s tie block and `depart x i` removes one at the first rank of the block, which is $\mathcal R(x\pm e_i)$ and the same for every server of the block. An arrival that finds idle servers is assigned to one of them uniformly (all give the same ordered state). The CTMC is given by its jump chain `jumpNI` (the next event drawn with probability proportional to its rate) and exit rates `rateNI`; no event is a self-loop. Stability is positive recurrence of the **empty state**, through the published `ProcessingNetworks.Stability.Recurrent` and `meanReturnTime`: the ordered chain is not irreducible (under J2SQ$^{NI}$ the shortest queue never exceeds $1$ from the empty state), so positive recurrence of every state would be false for every $\rho$.
-- source:
--   Moyal–Perry, Stability of Parallel Server Systems, arXiv:1904.10331v1, §3, pp.6–7 (model, ordered state space, Definition 1, tie rule); §3.1, pp.7–8 (stability regions S(p), S^NI(p))

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions

namespace ParallelServerStab

open scoped ENNReal

/-- The jump chain of a continuous-time Markov chain whose transitions out of a state `x` are
finitely many events `e : E`, event `e` occurring at rate `w e` and moving the chain to
`target e`: the next state is `target e` with probability `w e / ∑ₑ' w e'`.

**Formalization Note.** If every rate is `0` (no event can occur) the chain stays at `x`
(`PMF.pure x`); this fallback is never reached by the chains of this mission under their
standing positivity assumptions (`λ, μ > 0`). Negative rates are read as `0`
(`ENNReal.ofReal`). -/
noncomputable def jumpOfRates {E X : Type*} [Fintype E] (w : E → ℝ) (target : E → X)
    (x : X) : PMF X :=
  if h : (∑' e, ENNReal.ofReal (w e)) ≠ 0 then
    (PMF.normalize (fun e => ENNReal.ofReal (w e)) h
      (by rw [tsum_fintype]; exact ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top)).map
      target
  else PMF.pure x

/-- The ordered state space `ℛ(ℤ^s₊)` (Moyal–Perry, Stability of Parallel Server Systems,
arXiv:1904.10331v1, §3, p. 7): queue-length vectors `Q = (Q₁, …, Q_s)` listed in increasing
order, the servers being relabelled after every event so that `Q₁ ≤ ⋯ ≤ Q_s`.

**Formalization Note.** A state is a monotone `x : Fin s → ℕ`; ranks are 0-based, `x 0` being
the shortest queue (the paper's `Q₁`). Queue sizes count the job in service. -/
abbrev QState (s : ℕ) : Type := {x : Fin s → ℕ // Monotone x}

/-- The empty state `(0, …, 0)`. -/
def empty (s : ℕ) : QState s := ⟨fun _ => 0, fun _ _ _ => le_rfl⟩

/-- The largest rank whose queue has the same length as rank `i` (the last server of `i`'s tie
block). -/
def lastTied {s : ℕ} (x : Fin s → ℕ) (i : Fin s) : Fin s :=
  (Finset.univ.filter (fun k => x k = x i)).max' ⟨i, by simp⟩

/-- The smallest rank whose queue has the same length as rank `i` (the first server of `i`'s
tie block). -/
def firstTied {s : ℕ} (x : Fin s → ℕ) (i : Fin s) : Fin s :=
  (Finset.univ.filter (fun k => x k = x i)).min' ⟨i, by simp⟩

lemma le_lastTied {s : ℕ} (x : Fin s → ℕ) (i k : Fin s) (h : x k = x i) : k ≤ lastTied x i :=
  Finset.le_max' _ _ (by simp [h])

lemma firstTied_le {s : ℕ} (x : Fin s → ℕ) (i k : Fin s) (h : x k = x i) : firstTied x i ≤ k :=
  Finset.min'_le _ _ (by simp [h])

lemma lastTied_eq {s : ℕ} (x : Fin s → ℕ) (i : Fin s) : x (lastTied x i) = x i := by
  have := Finset.max'_mem (Finset.univ.filter (fun k => x k = x i)) ⟨i, by simp⟩
  simpa [lastTied] using this

lemma firstTied_eq {s : ℕ} (x : Fin s → ℕ) (i : Fin s) : x (firstTied x i) = x i := by
  have := Finset.min'_mem (Finset.univ.filter (fun k => x k = x i)) ⟨i, by simp⟩
  simpa [firstTied] using this

/-- The ordered state after a job joins the server of rank `i` (Moyal–Perry,
arXiv:1904.10331v1, §3, p. 7): `ℛ(x + e_i)`. Servers with equal queues have consecutive ranks
and are labelled uniformly at random, so after re-sorting the result is the same for every
server of `i`'s tie block; it is `x + e_k` for the **last** rank `k` of the block, which keeps
the vector ordered. -/
def arrive {s : ℕ} (x : QState s) (i : Fin s) : QState s :=
  ⟨fun j => if j = lastTied x.1 i then x.1 j + 1 else x.1 j, by
    intro a b hab
    have hx := x.2
    by_cases ha : a = lastTied x.1 i <;> by_cases hb : b = lastTied x.1 i
    · subst ha; subst hb; simp
    · simp only [ha, hb, if_true, if_false]
      subst ha
      have hlt : lastTied x.1 i < b := lt_of_le_of_ne hab (Ne.symm hb)
      have hle : x.1 (lastTied x.1 i) ≤ x.1 b := hx hab
      rcases Nat.lt_or_ge (x.1 (lastTied x.1 i)) (x.1 b) with h | h
      · omega
      · have heq : x.1 b = x.1 i := by rw [← lastTied_eq x.1 i]; omega
        exact absurd (le_lastTied x.1 i b heq) (not_le.mpr hlt)
    · simp only [ha, hb, if_true, if_false]
      subst hb; exact Nat.le_succ_of_le (hx hab)
    · simp only [ha, hb, if_false]
      exact hx hab⟩

/-- The ordered state after a departure from the server of rank `i` (Moyal–Perry,
arXiv:1904.10331v1, §3, pp. 6–7): `ℛ(x − e_i)` for `x i ≥ 1`. After re-sorting the result is
`x − e_j` for the **first** rank `j` of `i`'s tie block, which keeps the vector ordered.

**Formalization Note.** Natural-number subtraction: at `x i = 0` the state is unchanged; the
chain below only uses `depart x i` when `x i ≥ 1`. -/
def depart {s : ℕ} (x : QState s) (i : Fin s) : QState s :=
  ⟨fun j => if j = firstTied x.1 i then x.1 j - 1 else x.1 j, by
    intro a b hab
    have hx := x.2
    by_cases ha : a = firstTied x.1 i <;> by_cases hb : b = firstTied x.1 i
    · subst ha; subst hb; simp
    · simp only [ha, hb, if_true, if_false]
      subst ha
      exact le_trans (Nat.sub_le _ _) (hx hab)
    · simp only [ha, hb, if_true, if_false]
      subst hb
      have hlt : a < firstTied x.1 i := lt_of_le_of_ne hab ha
      have hle : x.1 a ≤ x.1 (firstTied x.1 i) := hx hab
      rcases Nat.lt_or_ge (x.1 a) (x.1 (firstTied x.1 i)) with h | h
      · omega
      · have heq : x.1 a = x.1 i := by rw [← firstTied_eq x.1 i]; omega
        exact absurd (firstTied_le x.1 i a heq) (not_le.mpr hlt)
    · simp only [ha, hb, if_false]
      exact hx hab⟩

/-- The number `n₊(x) = #{i : x i ≥ 1}` of busy servers in state `x`. -/
def busyCount {s : ℕ} (x : QState s) : ℕ :=
  (Finset.univ.filter (fun i => 1 ≤ x.1 i)).card

/-- The number of idle servers in state `x`. -/
def idleCount {s : ℕ} (x : QState s) : ℕ :=
  (Finset.univ.filter (fun i => x.1 i = 0)).card

/-- The total event rate (exit rate) of the ordered queue process in state `x` (Moyal–Perry,
arXiv:1904.10331v1, §3, p. 6): arrivals at rate `λ`, and each busy server completes a service
at rate `μ`, so `λ + μ · n₊(x)`. -/
noncomputable def rateNI (s : ℕ) (lam μ : ℝ) (x : QState s) : ℝ :=
  lam + μ * (busyCount x : ℝ)

/-- The rates of the events out of state `x` under the **non-idling** `p`-allocation policy
(Moyal–Perry, arXiv:1904.10331v1, Definition 1, p. 7). The event `Sum.inl i` is "an arrival
joins the server of rank `i`", the event `Sum.inr i` is "the server of rank `i` completes a
service":
1. if some server is idle, the arrival joins an idle server, chosen uniformly among the idle
   ones (rate `λ / #idle` for each idle rank, `0` for the busy ones);
2. otherwise it joins rank `i` with probability `p_i` (rate `λ p_i`);
3. each busy rank completes a service at rate `μ`.

**Formalization Note.** Ties are resolved by `arrive`/`depart` (`eventTarget`): routing to any
server of a tie block yields the same ordered state, which is the paper's uniform labelling
inside the block (p. 7). For `p ∈ Π_s` (nonnegative, summing to `1`) the rates sum to
`rateNI s lam μ x`. -/
noncomputable def eventRateNI (s : ℕ) (pv : Fin s → ℝ) (lam μ : ℝ) (x : QState s) :
    Fin s ⊕ Fin s → ℝ
  | Sum.inl i =>
      if ∃ j, x.1 j = 0 then (if x.1 i = 0 then lam / (idleCount x : ℝ) else 0)
      else lam * pv i
  | Sum.inr i => if 1 ≤ x.1 i then μ else 0

/-- The state reached by each event: `arrive x i` for an arrival to rank `i`, `depart x i` for a
departure from rank `i`. -/
def eventTarget {s : ℕ} (x : QState s) : Fin s ⊕ Fin s → QState s
  | Sum.inl i => arrive x i
  | Sum.inr i => depart x i

/-- The jump chain of the ordered queue process `ℛ(Q)` under the non-idling `p`-allocation
policy (Moyal–Perry, Stability of Parallel Server Systems, arXiv:1904.10331v1, §3, Definition
1, p. 7, and §3.1, p. 7: `Q` is an `ℛ(ℤ^s₊)`-valued CTMC). From `x`, the next state is the
target of an event drawn with probability proportional to its rate (`eventRateNI`).

**Formalization Note.** The CTMC is given by its jump chain `jumpNI` and its exit rates
`rateNI`. No event is a self-loop (an arrival adds a job, a departure removes one), so this is
exactly the embedded chain of the paper's CTMC. -/
noncomputable def jumpNI (s : ℕ) (pv : Fin s → ℝ) (lam μ : ℝ) (x : QState s) : PMF (QState s) :=
  jumpOfRates (eventRateNI s pv lam μ x) (eventTarget x) x

/-- Stability of the parallel-server system under the non-idling `p`-allocation policy
(Moyal–Perry, Stability of Parallel Server Systems, arXiv:1904.10331v1, §3.1, pp. 7–8: "`Q` is
stable in the sense that it is a positive recurrent CTMC"; `ρ ∈ S^NI(p)`): the empty state of
the ordered queue process is positive recurrent — the jump chain started empty returns to the
empty state with probability one, and the mean return time of the continuous-time chain
(holding times `1/rateNI` included) is finite.

**Formalization Note.** The ordered chain is not irreducible on `ℛ(ℤ^s₊)` (under J2SQ^NI the
shortest queue never exceeds `1` from the empty state), so "positive recurrent" is read as
positive recurrence of the empty state, the class the paper's chain starts in. `Recurrent` and
`meanReturnTime` are the published `ProcessingNetworks.Stability` definitions. -/
def StableNI (s : ℕ) (pv : Fin s → ℝ) (lam μ : ℝ) : Prop :=
  ProcessingNetworks.Stability.Recurrent (jumpNI s pv lam μ) (empty s) ∧
    ProcessingNetworks.Stability.meanReturnTime (jumpNI s pv lam μ) (rateNI s lam μ)
      (empty s) < ⊤

end ParallelServerStab


