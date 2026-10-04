-- Prove2me | Definitions.Def_BellWilliams2001_ThresholdPolicy_Threshold
-- name    : BellWilliams2001_ThresholdPolicy_Threshold
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T07:14:57.983364+00:00
-- url     : https://prove2.me/theorems/82aa8b01-1f17-4077-87c3-68501412d608
-- title:
--   The threshold policy of Definition 5.1 with threshold $L^r=[c\log r]$
-- statement:
--   Fix a constant $c$ and let $L^r=[c\log r]$, the integer part of $c\log r$. An allocation $T$ of system $r$, with queue lengths $Q=(Q_1,Q_2)$, follows the **threshold policy** of Definition 5.1 if for every sample path and every $t\ge0$
--   $$T_1(t)=\big|\{s\in(0,t]: Q_1(s)>H_2(s)\}\big|,\quad T_2(t)=\big|\{s\in(0,t]: Q_1(s)>L^r\}\big|,\quad T_3(t)=\big|\{s\in(0,t]: Q_1(s)\le L^r,\ Q_2(s)>0\}\big|,$$
--   where $|\cdot|$ is Lebesgue measure and $H_2(s)\in\{0,1\}$ equals $1$ exactly when server 2 holds an unfinished class 1 job at time $s$, that is, when $T_2(s)>\eta_2^r\big(S_2^r(T_2(s))\big)$: the time server 2 has spent on activity 2 exceeds the total requirement of the activity 2 jobs it has completed.
--
--   The three relations say: (i) server 1 works exactly when there is a class 1 job not held by server 2, so it is never idle when there are jobs in buffer 1 or at server 1; (ii) server 2 serves class 1 with preemptive-resume priority exactly when the number of class 1 jobs exceeds $L^r$, and otherwise serves class 2 when there is a class 2 job and idles when there is none. The service protocol of p. 610 (a server keeps a started job until it is complete, does not start a new class 1 job while it holds one, and server 1 cannot work on a class 1 job held by server 2) is what makes $H_2$ the right correction in the first relation.
--
--   **Formalization Note** Lebesgue measure is applied as an outer measure, so no measurability condition is attached to the three sets. The policy is used for the systems with $L^r\ge1$; for $L^r=0$ the rule would have both servers competing for a single class 1 job.
-- source:
--   Bell and Williams, Dynamic scheduling of a system with two parallel servers in heavy traffic with resource pooling, Ann. Appl. Probab. 11 (2001), p. 621, Definition 5.1; p. 610, service protocol

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Model

open MeasureTheory
open scoped ENNReal

namespace BellWilliams2001.ThresholdPolicy

namespace SystemSequence

variable {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)

/-- The threshold `L^r = [c log r]`, the integer part of `c log r` (Definition 5.1, p. 621).
Since `r ≥ 1`, `log r ≥ 0`. -/
noncomputable def threshold (c : ℝ) (n : ℕ) : ℕ :=
  ⌊c * Real.log (M.r n)⌋₊

/-- `H₂(s) ∈ {0, 1}`: `1` exactly when server 2 holds an unfinished (in progress or suspended)
class 1 job at time `s`, i.e. the cumulative activity 2 service `T₂(s)` exceeds the total service
requirement `η^r_2(S^r_2(T₂(s)))` of the activity 2 jobs it has completed (service protocol,
p. 610: a server keeps a job it has started until the job is complete, and does not start a new
class 1 job while it holds one). -/
noncomputable def serverTwoHolds (n : ℕ) (T : Allocation Ω) (ω : Ω) (s : ℝ) : ℝ :=
  if M.eta n 1 ω (renewalCount (M.eta n 1 ω) (T ω 1 s)).toNat < T ω 1 s then 1 else 0

/-- The allocation `T` of the `n`-th system follows the **threshold policy** of Definition 5.1
(p. 621) with threshold `L^r = [c log r]`, under the service protocol of p. 610. For every sample
path and every `t ≥ 0` (with `Q = Q^r` the queue lengths of `T` and `|·|` Lebesgue measure):
* `T₁(t) = |{s ∈ (0,t] : Q₁(s) > H₂(s)}|` — server 1 works exactly when there is a class 1 job
  that server 2 does not hold (rule (i): server 1 is never idle when there are jobs in buffer 1
  or at server 1);
* `T₂(t) = |{s ∈ (0,t] : Q₁(s) > L^r}|` — server 2 serves class 1, with preemptive-resume
  priority, exactly when the number of class 1 jobs exceeds `L^r` (rule (ii));
* `T₃(t) = |{s ∈ (0,t] : Q₁(s) ≤ L^r, Q₂(s) > 0}|` — otherwise server 2 serves class 2 when
  there is a class 2 job, and idles when there is none (rule (ii)).
Lebesgue measure is the outer measure, so no measurability side condition enters. -/
def IsThreshold (c : ℝ) (n : ℕ) (T : Allocation Ω) : Prop :=
  ∀ ω t, 0 ≤ t →
    T ω 0 t = (volume {s ∈ Set.Ioc 0 t | M.serverTwoHolds n T ω s < M.queue n T ω 0 s}).toReal ∧
    T ω 1 t = (volume {s ∈ Set.Ioc 0 t | (M.threshold c n : ℝ) < M.queue n T ω 0 s}).toReal ∧
    T ω 2 t = (volume {s ∈ Set.Ioc 0 t |
      M.queue n T ω 0 s ≤ (M.threshold c n : ℝ) ∧ 0 < M.queue n T ω 1 s}).toReal

end SystemSequence

end BellWilliams2001.ThresholdPolicy


