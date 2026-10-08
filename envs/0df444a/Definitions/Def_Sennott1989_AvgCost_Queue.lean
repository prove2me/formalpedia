-- Prove2me | Definitions.Def_Sennott1989_AvgCost_Queue
-- name    : Sennott1989_AvgCost_Queue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:31.023794+00:00
-- url     : https://prove2.me/theorems/35ca78fd-1635-4228-b465-39c3363e61c1
-- title:
--   Example 2 (p. 631): the queue with variable service rates aβ, its cost structure C(0) = Q(0), C(i, a) = Q(i) + B(a), transition law (13) and arrival moments λ^(k)
-- statement:
--   The queueing model with variable service rates of Sennott (1989), Example 2. Time is slotted. In each slot $i$ customers arrive with probability $p_i$ ($\sum_i p_i=1$), independently across slots. The state is the number of customers waiting at the beginning of a slot. When the system is nonempty the server chooses one of finitely many decision variables $a$ and serves at rate $a\beta$, $0<a\beta<1$: the customer in service completes in the slot with probability $a\beta$. There is no decision in state $0$. The discounted optimality equations (13) of the paper correspond to the transition law
--   $$P_{0j}=p_j,\qquad P_{i,\,i-1+k}(a)=a\beta\,p_k+(1-a\beta)\,p_{k-1}\quad(i\ge1,\ k\ge0),$$
--   with $p_{-1}=0$; states below $i-1$ are not reached from $i$.
--
--   **Cost structure** (p. 631). $B(a)>0$ is the cost of serving at rate $a\beta$; $n\ge0$ is a fixed integer and $Q$ a polynomial of degree $n$ that is nonnegative and increasing on $i\ge0$; the cost is
--   $$C(0)=Q(0),\qquad C(i,a)=Q(i)+B(a),\quad i\ge1.$$
--
--   **Moments.** $\lambda^{(k)}=\sum_i i^kp_i$ ($k\ge1$) is the $k$th moment of the arrival process (moments need not be finite), and $\lambda=\lambda^{(1)}=\sum_i ip_i$ is the mean number of arrivals per slot.
--
--   This model is the application of the paper: Proposition 8 gives conditions on $\lambda$ under which it has an average cost optimal stationary policy.
--
--   **Formalization Note** The model is a `SennottDP.Discounted.MDC ℕ Act` with $A_i$ the whole finite nonempty set `Act` of decision variables for every $i$, including $i=0$: in state $0$ every decision has the same cost $Q(0)$ and the same row $(p_j)$, so the choice there is immaterial (this is how "no decision in state 0" is represented). A decision $x$ carries a real parameter $a(x)$, and the rate is the product $a(x)\beta$. Costs are stored as nonnegative reals (`Real.toNNReal`, the identity here since $Q\ge0$ on $\mathbb N$ and $B>0$). "Degree $n$" is `Q.degree = n`, which excludes $Q=0$; nonnegativity and monotonicity are required on the states $0,1,2,\dots$. The row sums $\sum_jP_{ij}(a)=1$ are proved in the file. $\lambda^{(k)}$ is a real `tsum`; "$\lambda^{(k)}<\infty$" is the summability of $i^kp_i$, which every statement using $\lambda^{(k)}$ assumes.
-- source:
--   Sennott, Average Cost Optimal Stationary Policies in Infinite State Markov Decision Processes with Unbounded Costs, Oper. Res. 37(4):626–633 (1989), DOI 10.1287/opre.37.4.626, p. 631, Example 2, (13), cost structure and λ^(k); λ = Σ i p_i from Example 1, p. 631

import Mathlib
import Definitions.Def_SennottDP_Discounted_MDC

open scoped ENNReal NNReal

namespace Sennott1989.AvgCost

/-- Sennott (1989), §3, Example 2, p. 631: the data of the queueing model with variable service
rates under "the above cost structure".

* `p i` is the probability of `i` customers arriving in a slot (`∑_i p_i = 1`); arrivals in
  different slots are independent.
* `Act` is the finite nonempty set of decision variables; deciding `x` serves at rate
  `a(x) β`, with `0 < a(x) β < 1`.
* `B x > 0` is the cost of serving at rate `a(x) β`.
* `n ≥ 0` is a fixed integer and `Q` a polynomial of degree `n`, nonnegative and increasing on the
  states `i = 0, 1, 2, …`. -/
structure QueueData (Act : Type) [Fintype Act] [Nonempty Act] where
  /-- the arrival law: `p i` is the probability of `i` arrivals in a slot -/
  p : ℕ → ℝ≥0
  /-- `∑_i p_i = 1` -/
  p_hasSum : HasSum p 1
  /-- the decision parameter `a` of each decision variable -/
  a : Act → ℝ
  /-- the constant `β`; the service rate under decision `x` is `a(x) β` -/
  β : ℝ
  /-- `0 < a(x) β` -/
  rate_pos : ∀ x, 0 < a x * β
  /-- `a(x) β < 1` -/
  rate_lt_one : ∀ x, a x * β < 1
  /-- `B(x) > 0`, the cost of serving at rate `a(x) β` -/
  B : Act → ℝ
  /-- `B(x) > 0` -/
  B_pos : ∀ x, 0 < B x
  /-- the integer `n ≥ 0` -/
  n : ℕ
  /-- the holding cost polynomial `Q` -/
  Q : Polynomial ℝ
  /-- `Q` has degree exactly `n` (so `Q ≠ 0`) -/
  Q_degree : Q.degree = n
  /-- `Q(i) ≥ 0` for `i ≥ 0` -/
  Q_nonneg : ∀ i : ℕ, 0 ≤ Q.eval (i : ℝ)
  /-- `Q(i)` is increasing in `i ≥ 0` -/
  Q_mono : Monotone fun i : ℕ => Q.eval (i : ℝ)

namespace QueueData

variable {Act : Type} [Fintype Act] [Nonempty Act]

/-- The service rate `a(x) β` of decision `x`, as an element of `[0, ∞]`. -/
noncomputable def rate (q : QueueData Act) (x : Act) : ℝ≥0∞ :=
  ENNReal.ofReal (q.a x * q.β)

/-- The arrival law shifted by one, `k ↦ p_{k−1}`, with the paper's convention `p_{−1} = 0`. -/
def pPrev (q : QueueData Act) (k : ℕ) : ℝ≥0 :=
  if k = 0 then 0 else q.p (k - 1)

/-- Sennott (1989), (13), p. 631: the transition probabilities of the queue. In state `0` there
is no service and the next state is the number of arrivals: `P_{0j} = p_j`. In a state `i ≥ 1`
under decision `x`, the next state is `i − 1 + k` (`k ≥ 0`) with probability
`a(x)β p_k + (1 − a(x)β) p_{k−1}` (where `p_{−1} = 0`), and states `j < i − 1` are not reached. -/
noncomputable def trans (q : QueueData Act) (i : ℕ) (x : Act) (j : ℕ) : ℝ≥0∞ :=
  if i = 0 then (q.p j : ℝ≥0∞)
  else if j + 1 < i then 0
  else q.rate x * (q.p (j + 1 - i) : ℝ≥0∞) + (1 - q.rate x) * (q.pPrev (j + 1 - i) : ℝ≥0∞)

/-- Sennott (1989), p. 631, "the above cost structure": `C(0) = Q(0)` and
`C(i, x) = Q(i) + B(x)` for `i ≥ 1`. -/
noncomputable def cost (q : QueueData Act) (i : ℕ) (x : Act) : ℝ≥0 :=
  if i = 0 then Real.toNNReal (q.Q.eval 0) else Real.toNNReal (q.Q.eval (i : ℝ) + q.B x)

lemma tsum_p (q : QueueData Act) : ∑' k, (q.p k : ℝ≥0∞) = 1 := by
  rw [← ENNReal.coe_tsum q.p_hasSum.summable, q.p_hasSum.tsum_eq, ENNReal.coe_one]

lemma tsum_pPrev (q : QueueData Act) : ∑' k, (q.pPrev k : ℝ≥0∞) = 1 := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  simpa [pPrev] using q.tsum_p

lemma rate_le_one (q : QueueData Act) (x : Act) : q.rate x ≤ 1 := by
  unfold rate
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (q.rate_lt_one x).le

lemma trans_sum (q : QueueData Act) (i : ℕ) (x : Act) : ∑' j, q.trans i x j = 1 := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simpa [trans] using q.tsum_p
  · rw [← (ENNReal.summable (f := fun k => q.trans i x (k + (i - 1)))).sum_add_tsum_nat_add']
    have h1 : ∑ j ∈ Finset.range (i - 1), q.trans i x j = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have : j + 1 < i := by simp at hj; omega
      simp [trans, hi.ne', this]
    have h2 : ∀ k, q.trans i x (k + (i - 1)) =
        q.rate x * (q.p k : ℝ≥0∞) + (1 - q.rate x) * (q.pPrev k : ℝ≥0∞) := by
      intro k
      have e1 : ¬ (k + (i - 1) + 1 < i) := by omega
      have e2 : k + (i - 1) + 1 - i = k := by omega
      simp only [trans, hi.ne', if_false, e1, e2]
    rw [h1, zero_add, tsum_congr h2, ENNReal.tsum_add, ENNReal.tsum_mul_left,
      ENNReal.tsum_mul_left, q.tsum_p, q.tsum_pPrev, mul_one, mul_one,
      add_tsub_cancel_of_le (q.rate_le_one x)]

/-- Sennott (1989), §3, Example 2, p. 631: the queue as a Markov decision chain on the states
`0, 1, 2, …` (the number of customers waiting at the beginning of a slot), with every decision
variable available in every state, cost `cost` and transition law (13).

**Formalization Note** The paper makes no decision in state `0`. Here every decision variable is
formally available in state `0`, but all of them have the same cost `Q(0)` and the same transition
row `(p_j)`, so the choice in state `0` is immaterial. -/
noncomputable def toMDC (q : QueueData Act) : SennottDP.Discounted.MDC ℕ Act where
  A _ := Finset.univ
  A_nonempty _ := Finset.univ_nonempty
  C := q.cost
  P := q.trans
  P_sum i x _ := q.trans_sum i x

/-- Sennott (1989), p. 631: the `k`th moment of the arrival process, `λ^(k) = ∑_i i^k p_i`, as a
real number. It is a genuine value when `i ↦ i^k p_i` is summable; "`λ^(k) < ∞`" is that
summability (the real `tsum` of a non-summable family is `0`). -/
noncomputable def moment (q : QueueData Act) (k : ℕ) : ℝ :=
  ∑' i : ℕ, (i : ℝ) ^ k * (q.p i : ℝ)

/-- Sennott (1989), p. 631 (Example 1: "`λ = Σ i p_i`"): the mean number of arrivals per slot,
`λ = λ^(1)`. -/
noncomputable def lam (q : QueueData Act) : ℝ :=
  q.moment 1

end QueueData

end Sennott1989.AvgCost


