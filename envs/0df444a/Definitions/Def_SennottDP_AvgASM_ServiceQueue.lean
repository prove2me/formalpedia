-- Prove2me | Definitions.Def_SennottDP_AvgASM_ServiceQueue
-- name    : SennottDP_AvgASM_ServiceQueue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T09:33:34.197342+00:00
-- url     : https://prove2.me/theorems/a2232008-62f4-4a39-89b5-7f2f562b73e0
-- title:
--   Single-server queue with service rate control and Bernoulli arrivals (Sennott Ex. 2.1.2, §8.5)
-- statement:
--   Packets arrive to a single-server queue in discrete time slots: in each slot one packet arrives with probability $p$ and none with probability $1-p$, where $0<p<1$. The state $i\in\{0,1,2,\dots\}$ is the number of packets in the system.
--
--   In state $0$ there is no decision (a single null action), the cost is $0$, and $P_{00}=1-p$, $P_{01}=p$. In a state $i\ge1$ the controller chooses a service rate $a$ from the allowable rates $a_1<\dots<a_M$, all in $(0,1)$; a service is completed in the slot with probability $a$. The cost is $C(i,a)=Hi+C(a)$, with holding cost rate $H>0$ and service cost $C(a)\ge0$, and
--   $$P_{i,i-1}(a)=a(1-p),\qquad P_{ii}(a)=ap+(1-a)(1-p),\qquad P_{i,i+1}(a)=(1-a)p .$$
--
--   The policy $d(a)$ always serves at the fixed rate $a$. It is the open-loop benchmark against which the computed optimal policies of Section 8.5 are compared.
--
--   **Formalization Note** Actions are real numbers; the null action in state $0$ is encoded as $0$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 18 Example 2.1.2 and (2.3); p. 181 Section 8.5; p. 182

import Mathlib
import Definitions.Def_SennottDP_AvgASM_Model

namespace SennottDP.AvgASM

open scoped ENNReal NNReal

/-- The data of the single-server queue with service rate control and Bernoulli arrivals
(Example 2.1.2, p. 18, as specialized in Section 8.5, p. 181): in each slot a single packet
arrives with probability `p` and none with probability `1 − p`, where `0 < p < 1`; the holding
cost is `H(i) = H i` for a positive constant `H`; in a nonempty buffer the controller chooses a
service rate `a` from the allowable rates `a_1 < ⋯ < a_M`, all in `(0, 1)`, at a nonnegative
cost `C(a)` per slot. -/
structure ServiceQueueData where
  /-- the arrival probability `p` -/
  p : ℝ
  p_pos : 0 < p
  p_lt_one : p < 1
  /-- the holding cost rate `H > 0`, `H(i) = H i` -/
  H : ℝ≥0
  H_pos : 0 < H
  /-- the allowable service rates -/
  rates : Finset ℝ
  rates_nonempty : rates.Nonempty
  rates_pos : ∀ a ∈ rates, 0 < a
  rates_lt_one : ∀ a ∈ rates, a < 1
  /-- the service cost `C(a)` -/
  serviceCost : ℝ → ℝ≥0

namespace ServiceQueueData

variable (Q : ServiceQueueData)

open Classical in
/-- The MDC of the single-server queue with service rate control (Example 2.1.2, p. 18) with
Bernoulli(`p`) arrivals (Section 8.5, p. 181). The state `i ∈ {0, 1, 2, …}` is the number of
packets in the system. In state `0` there is a single (null) action, encoded as the real number
`0`, the cost is `0`, and `P_00 = 1 − p`, `P_01 = p`. In state `i ≥ 1` the actions are the
allowable rates `a`, the cost is `C(i, a) = H i + C(a)`, and (2.3) with `p_0 = 1 − p`, `p_1 = p`
gives `P_{i,i−1}(a) = a(1 − p)`, `P_{i,i}(a) = ap + (1 − a)(1 − p)`, `P_{i,i+1}(a) = (1 − a)p`. -/
noncomputable def toMDC : MDC ℕ ℝ where
  A i := if i = 0 then {0} else Q.rates
  A_nonempty i := by
    by_cases h : i = 0
    · simp [h]
    · simp only [h, if_false]; exact Q.rates_nonempty
  C i a := if i = 0 then 0 else Q.H * (i : ℝ≥0) + Q.serviceCost a
  P i a j :=
    if i = 0 then
      ENNReal.ofReal (1 - Q.p) * (if j = 0 then 1 else 0) + ENNReal.ofReal Q.p * (if j = 1 then 1 else 0)
    else
      ENNReal.ofReal (a * (1 - Q.p)) * (if j = i - 1 then 1 else 0) +
        ENNReal.ofReal (a * Q.p + (1 - a) * (1 - Q.p)) * (if j = i then 1 else 0) +
        ENNReal.ofReal ((1 - a) * Q.p) * (if j = i + 1 then 1 else 0)
  P_sum i a ha := by
    have hp0 := Q.p_pos.le
    have hp1 := Q.p_lt_one.le
    by_cases h : i = 0
    · simp only [h, if_true]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
      simp only [tsum_ite_eq, mul_one]
      rw [← ENNReal.ofReal_add (by linarith) hp0]
      simp
    · simp only [h, if_false] at ha ⊢
      have ha0 := (Q.rates_pos a ha).le
      have ha1 := (Q.rates_lt_one a ha).le
      rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
        ENNReal.tsum_mul_left]
      simp only [tsum_ite_eq, mul_one]
      rw [← ENNReal.ofReal_add (by positivity) (by nlinarith),
        ← ENNReal.ofReal_add (by nlinarith) (by nlinarith)]
      have : a * (1 - Q.p) + (a * Q.p + (1 - a) * (1 - Q.p)) + (1 - a) * Q.p = 1 := by ring
      rw [this, ENNReal.ofReal_one]

/-- The policy `d(a)` that always serves at rate `a ∈ {a_1, …, a_M}` (p. 182); in state `0` it
takes the null action. -/
noncomputable def serveAt (a : ℝ) (ha : a ∈ Q.rates) : StationaryPolicy Q.toMDC where
  f i := if i = 0 then 0 else a
  mem i := by
    by_cases h : i = 0
    · simp [toMDC, h]
    · simp [toMDC, h, ha]

end ServiceQueueData

end SennottDP.AvgASM


