-- Prove2me | Definitions.Def_TemporalAgg_Supplement_ataState
-- name    : TemporalAgg_Supplement_ataState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:16:54.460045+00:00
-- url     : https://prove2.me/theorems/31f7a19e-56fe-4c05-9520-a2a8b8dbd417
-- title:
--   Aligned Temporal Aggregation (ATA) with parameter $\alpha$
-- statement:
--   Fix an integer $\alpha\ge2$ and $n$ objects. Every object $u$ carries a **period** $\pi(u)\in\mathbb N\cup\{\infty\}$ and the time $\mathrm{last}(u)$ at which its current realization was sampled. After time $0$ every object has $\pi(u)=\infty$ and $\mathrm{last}(u)=0$. At each time $t\ge1$, given the adversary's sample set $A_t$:
--
--   1. every $u\in A_t$ is sampled by the adversary: $\pi(u):=0$, $\mathrm{last}(u):=t$;
--   2. write $t=k\cdot\alpha^p$ with $k\ge1$ not divisible by $\alpha$ and $p\ge0$; the algorithm samples every object with $\pi(u)\le p$ and sets $\pi(u):=p$, $\mathrm{last}(u):=t$.
--
--   The **algorithmic samples** of time $t$ are the objects sampled in step 2 (objects just sampled by the adversary have period $0\le p$ and are among them). The sampling of all objects at time $0$ is neither adversarial nor algorithmic. ATA is deterministic given the adversary's sample sets $(A_t)_{t\ge1}$; the mission records $\mathrm{last}_t(u)$ at the end of every step and the number $\mathrm{alg}_t$ of algorithmic samples at time $t$.
--
--   Objects sampled at time $0$ are resampled only after the adversary samples them; resampling times are aligned to multiples of powers of $\alpha$, so that at any time the realizations come from few time steps that depend only on $t$.
--
--   **Formalization Note** The exponent $p$ is `padicValNat α t`, the largest $p$ with $\alpha^p\mid t$ (Mathlib characterizes it for every $\alpha\ne1$, not only primes), which is the unique $p$ of the decomposition $t=k\alpha^p$, $\alpha\nmid k$. Periods live in `ℕ∞`, with $\top=\infty$.
-- source:
--   Haeupler, Paramonov, Temporal Aggregation: Maintaining Randomness against Adaptive Adversaries, STOC 2027 submission (manuscript of 2026-11-03, sha256 42ebf866…), §3.2, p.18 (box "Aligned Temporal Aggregation (ATA)")

import Mathlib

namespace TemporalAgg.Supplement

/-! Aligned Temporal Aggregation (Haeupler, Paramonov, *Temporal Aggregation: Maintaining
Randomness against Adaptive Adversaries*, STOC 2027 submission, manuscript of 2026-11-03,
sha256 42ebf866…, §3.2, p.18).

Integer parameter `α ≥ 2`. Every object `u` has a *period* in `ℕ ∪ {∞}`; objects sampled at time 0
have period `∞`.
* When the adversary samples an object, its period is set to `0`.
* At time `t = k·αᵖ` with `k ≥ 1` not divisible by `α` and `p ≥ 0`, the algorithm samples all
  objects with period `≤ p` and sets their period to `p`. -/

/-- State of ATA at the end of a time step: the period of every object (`⊤` is `∞`) and the time
step `last u` at which the current realization of `u` was sampled. -/
structure ATAState (n : ℕ) where
  period : Fin n → ℕ∞
  last : Fin n → ℕ

/-- The state after time 0: every object is sampled at time 0 and has period `∞`. -/
def ataInit (n : ℕ) : ATAState n :=
  ⟨fun _ => ⊤, fun _ => 0⟩

/-- The adversary's samples at time `t`: every `u ∈ A` is sampled (its realization now comes from
time `t`) and its period is set to `0`. -/
def ataAdversary {n : ℕ} (t : ℕ) (A : Finset (Fin n)) (s : ATAState n) : ATAState n :=
  ⟨fun u => if u ∈ A then 0 else s.period u, fun u => if u ∈ A then t else s.last u⟩

/-- The objects the algorithm samples at time `t ≥ 1`, from the state `s` reached after the
adversary's samples of time `t`: those of period `≤ p`, where `p = padicValNat α t` is the
exponent in `t = k·αᵖ`, `α ∤ k`.

**Formalization Note** `padicValNat α t` is, for `α ≥ 2` and `t ≥ 1`, the largest `p` with
`αᵖ ∣ t` (Mathlib's `pow_dvd_iff_le_padicValNat` needs only `α ≠ 1`, not primality), which is
exactly the unique `p` with `t = k·αᵖ`, `k ≥ 1`, `α ∤ k`. Objects just sampled by the adversary
have period `0 ≤ p` and are therefore sampled again by the algorithm at the same time step; these
samples are algorithmic and are counted. -/
noncomputable def ataAlgSet {n : ℕ} (α t : ℕ) (s : ATAState n) : Finset (Fin n) :=
  by classical exact Finset.univ.filter (fun u => s.period u ≤ ((padicValNat α t : ℕ) : ℕ∞))

/-- One time step `t ≥ 1` of ATA: the adversary samples `A`, then the algorithm samples every
object of period `≤ p` (`p = padicValNat α t`) and sets its period to `p`. -/
noncomputable def ataStep {n : ℕ} (α t : ℕ) (A : Finset (Fin n)) (s : ATAState n) : ATAState n :=
  let s' := ataAdversary t A s
  let S := ataAlgSet α t s'
  ⟨fun u => if u ∈ S then ((padicValNat α t : ℕ) : ℕ∞) else s'.period u,
   fun u => if u ∈ S then t else s'.last u⟩

/-- **ATA against the adversarial sample sets `A t` (`t ≥ 1`)**: `ataState α A t` is the state at
the end of time step `t`. ATA is deterministic given the adversary's sample sets.

**Formalization Note** `A 0` is unused: the sampling of all objects at time 0 is neither
adversarial nor algorithmic (§1.2, p.3). -/
noncomputable def ataState {n : ℕ} (α : ℕ) (A : ℕ → Finset (Fin n)) : ℕ → ATAState n
  | 0 => ataInit n
  | t + 1 => ataStep α (t + 1) (A (t + 1)) (ataState α A t)

/-- Under ATA, `ataLast α A t u` is the time step at which the realization of object `u` current at
the end of time step `t` was sampled. -/
noncomputable def ataLast {n : ℕ} (α : ℕ) (A : ℕ → Finset (Fin n)) (t : ℕ) (u : Fin n) : ℕ :=
  (ataState α A t).last u

/-- The number of algorithmic samples ATA performs at time step `t ≥ 1` (adversarially sampled
objects re-sampled by the algorithm at the same step included); `0` at time 0. -/
noncomputable def ataAlg {n : ℕ} (α : ℕ) (A : ℕ → Finset (Fin n)) : ℕ → ℕ
  | 0 => 0
  | t + 1 => (ataAlgSet α (t + 1) (ataAdversary (t + 1) (A (t + 1)) (ataState α A t))).card

end TemporalAgg.Supplement


