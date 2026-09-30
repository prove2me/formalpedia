-- Prove2me | Definitions.Def_RevenueManagement_singleResource
-- name    : RevenueManagement_singleResource
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T00:27:43.791993+00:00
-- url     : https://prove2.me/theorems/a23b7c2e-29c2-48d8-b2e0-7eacf2c36875
-- title:
--   Single-resource capacity control, Chapter 2: the static, dynamic and choice-based value functions, protection levels, booking limits, bid prices, and efficient offer sets
-- statement:
--   The three single-resource models of Chapter 2 of Talluri and van Ryzin, with capacity $C$
--   and remaining capacity $x$.
--
--   **Static model** (Sect. 2.2.2). Classes $1, \dots, n$ with prices $p_1 \ge p_2 \ge \dots$
--   arrive in stages, the lowest class first; the demand $D_j$ of class $j$ has a probability
--   mass function $f_j$ on $\mathbb N$ (`IsPmf`). The value function $V_j(x)$ with $j$ stages
--   remaining is the Bellman equation (2.3),
--   $V_j(x) = \mathbb E\big[\max_{0 \le u \le \min\{D_j, x\}} \{p_j u + V_{j-1}(x-u)\}\big]$,
--   $V_0 = 0$ (`staticValue`), and $\Delta V_j(x) = V_j(x) - V_j(x-1)$ is the expected marginal
--   value of capacity (`staticDelta`). A quantity $u$ is a stage-optimal decision at stage $j+1$
--   with $x$ units remaining and demand $d$ if it attains the inner maximum (`IsStageOptimal`).
--   The optimal protection level (2.4) is $y_j^* = \max\{x : p_{j+1} < \Delta V_j(x)\}$
--   (`protLevel`, the search over $x = 1, \dots, C$, and $0$ when the set is empty), the nested
--   booking limit (2.6) is $b_j^* = C - y_{j-1}^*$ (`bookLimit`), and the bid price (2.7) is
--   $\pi_{j+1}(x) = \Delta V_j(x)$ (`bidPrice`). The bid-price control `bidControl` accepts at
--   stage $j+1$ the largest $z \le \min\{d, x\}$ such that $p_{j+1} \ge \pi_{j+1}(x+1-z)$, the
--   bid price of the $z$-th unit allocated, and nothing when $p_{j+1} < \pi_{j+1}(x)$.
--
--   **Dynamic model** (Sect. 2.5). In each of $T$ periods at most one request arrives, of class
--   $j$ with probability $\lambda_j(t)$ (`IsArrivalModel`). The value function (2.17) is
--   $V_t(x) = V_{t+1}(x) + \mathbb E\big[\max_{u \in \{0,1\}} (R(t) - \Delta V_{t+1}(x))\,u\big]$
--   with $R(t) = p_j$ with probability $\lambda_j(t)$ and $0$ otherwise, $V_{T+1} = 0$ and
--   $V_t(0) = 0$ (`dynValue`, `dynDelta`). A decision $u \in \{0, 1\}$ for a class-$j$ request is
--   optimal if it maximizes $(p_j - \Delta V_{t+1}(x))\,u$ (`IsDynOptimal`). The time-dependent
--   protection levels (2.19) are $y_j^*(t) = \max\{x : p_{j+1} < \Delta V_{t+1}(x)\}$
--   (`dynProtLevel`), the booking limits (2.20) $b_j^*(t) = C - y_{j-1}^*(t)$ (`dynBookLimit`),
--   and the bid prices (2.18) $\pi_t(x) = \Delta V_t(x)$ (`dynBidPrice`).
--
--   **Choice model** (Sect. 2.6.2). Classes are `Fin n`; when the set $S$ is offered an arriving
--   customer buys class $j \in S$ with probability $P_j(S)$ (`IsChoiceModel`: nonnegative,
--   $\sum_{j \in S} P_j(S) \le 1$). $Q(S) = \sum_{j \in S} P_j(S)$ is the purchase probability
--   (`purchaseProb`) and $R(S) = \sum_{j \in S} P_j(S) p_j$ the expected revenue
--   (`expRevenue`). With arrival probability $\lambda_t$ the value function (2.26) is
--   $V_t(x) = \max_{S \subseteq N} \lambda_t (R(S) - Q(S)\Delta V_{t+1}(x)) + V_{t+1}(x)$,
--   $V_{T+1} = 0$, $V_t(0) = 0$ (`choiceValue`, `choiceDelta`); `choiceObj` is the objective
--   of a set $S$ and `IsChoiceOptimal` says $S$ maximizes it. Definition 2.1: a set $T$ is
--   **inefficient** (`IsInefficient`) if probabilities $\alpha(S)$ over the subsets satisfy
--   $\sum_S \alpha(S) Q(S) \le Q(T)$ and $R(T) < \sum_S \alpha(S) R(S)$, and **efficient**
--   (`IsEfficient`) otherwise.
--
--   **Formalization Note** Stages, periods and capacities are natural numbers and the value
--   functions are defined for all of them, so the book's ranges ($x \le C$, $t \le T$,
--   $j \le n$) appear as hypotheses of the theorems; prices and pmfs are indexed by all of
--   $\mathbb N$, and the results about stage $j$ only involve the data of stages up to $j$. The
--   dynamic and choice value functions recurse on the number of periods to go, and
--   $V_t$ is the value with $T + 1 - t$ periods to go. Eq. (2.17) is taken literally as an
--   expectation over $R(t)$, including the no-arrival term, which vanishes when prices are
--   nonnegative. The choice model is defined by its compact form (2.26), which is (2.24)
--   after $\sum_{j \in S} P_j(S) + P_0(S) = 1$, and the maximization ranges over all subsets
--   including the empty offer set. In the bid-price control the $z$-th unit allocated has bid
--   price $\pi_{j+1}(x + 1 - z)$; the book prints $\pi_{j+1}(x - z)$, which is one unit off from
--   the protection-level control (2.5) it is meant to reproduce.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, Sect. 2.2.1-2.2.2 pp. 35-40 (Eq. 2.1-2.7), Sect. 2.5.1-2.5.2 pp. 58-61 (Eq. 2.17-2.20), Sect. 2.6.2 pp. 66-68 (Eq. 2.24-2.27, Definition 2.1)

import Mathlib

namespace RevenueManagement

/-! ### Single-resource capacity control, Chapter 2 of Talluri and van Ryzin -/

/-! #### The static model, Sect. 2.2 -/

/-- A probability mass function on `ℕ`: nonnegative and summing to one. -/
def IsPmf (f : ℕ → ℝ) : Prop := (∀ d, 0 ≤ f d) ∧ HasSum f 1

/-- The value function `V_j(x)` of the static model, Eq. (2.3): `j` stages (classes) remain, `x`
units of capacity remain, class `j` with price `p j` and demand pmf `f j` arrives at stage `j`, and
`V_0 = 0`. The decision `u` is taken after the demand `d` is seen, `0 ≤ u ≤ min {d, x}`. -/
noncomputable def staticValue (p : ℕ → ℝ) (f : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | j + 1, x => ∑' d, f (j + 1) d *
      (Finset.range (min d x + 1)).sup' ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩
        (fun u => p (j + 1) * u + staticValue p f j (x - u))

/-- The expected marginal value of capacity `ΔV_j(x) = V_j(x) − V_j(x − 1)`, meaningful for `x ≥ 1`. -/
noncomputable def staticDelta (p : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (j x : ℕ) : ℝ :=
  staticValue p f j x - staticValue p f j (x - 1)

/-- `u` is an optimal quantity to accept at stage `j + 1` with `x` units remaining and demand `d`:
it is feasible and maximizes `p_{j+1} u + V_j(x − u)` over `0 ≤ u ≤ min {d, x}`, the inner
optimization of (2.3). -/
def IsStageOptimal (p : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (j x d u : ℕ) : Prop :=
  u ≤ min d x ∧ ∀ u' ≤ min d x,
    p (j + 1) * u' + staticValue p f j (x - u') ≤ p (j + 1) * u + staticValue p f j (x - u)

open Classical in
/-- The optimal protection level `y_j* = max {x : p_{j+1} < ΔV_j(x)}` of Eq. (2.4), the search over
`x = 1, …, C` and `0` when the set is empty. For `j = 0` it is `0`. -/
noncomputable def protLevel (p : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (C j : ℕ) : ℕ :=
  ((Finset.range (C + 1)).filter (fun x => 1 ≤ x ∧ p (j + 1) < staticDelta p f j x)).sup id

/-- The nested booking limit `b_j* = C − y_{j−1}*` of Eq. (2.6). -/
noncomputable def bookLimit (p : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (C j : ℕ) : ℕ :=
  C - protLevel p f C (j - 1)

/-- The stage-`j` bid price `π_j(x) = ΔV_{j−1}(x)` of Eq. (2.7). -/
noncomputable def bidPrice (p : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (j x : ℕ) : ℝ :=
  staticDelta p f (j - 1) x

open Classical in
/-- The bid-price control at stage `j + 1`: accept `z` units when `p_{j+1}` is at least the bid
price `π_{j+1}(x + 1 − z)` of the `z`-th unit allocated, i.e. the largest such `z ≤ min {d, x}`, and
`0` when `p_{j+1} < π_{j+1}(x)`. -/
noncomputable def bidControl (p : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (j x d : ℕ) : ℕ :=
  ((Finset.range (min d x + 1)).filter
    (fun z => z = 0 ∨ bidPrice p f (j + 1) (x + 1 - z) ≤ p (j + 1))).sup id

/-! #### The dynamic model, Sect. 2.5 -/

/-- Arrival probabilities `λ_j(t)` of the dynamic model: at most one request per period, class `j`
with probability `λ_j(t)`, none with the remaining probability. -/
def IsArrivalModel (lam : ℕ → ℕ → ℝ) (n : ℕ) : Prop :=
  (∀ j t, 0 ≤ lam j t) ∧ ∀ t, ∑ j ∈ Finset.Icc 1 n, lam j t ≤ 1

/-- The dynamic value function with `k` periods to go (period `t = T + 1 − k`), Eq. (2.17):
`V(x) = V'(x) + E[max_{u ∈ {0,1}} (R(t) − ΔV'(x)) u]` where `V'` is the value with `k − 1` periods
to go and `R(t) = p_j` with probability `λ_j(t)`, `0` otherwise; `V(0) = 0` and `V = 0` with no
period to go. -/
noncomputable def dynValueGo (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T : ℕ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | k + 1, x + 1 =>
      dynValueGo lam p n T k (x + 1) +
        ((∑ j ∈ Finset.Icc 1 n, lam j (T - k) *
            max (p j - (dynValueGo lam p n T k (x + 1) - dynValueGo lam p n T k x)) 0) +
          (1 - ∑ j ∈ Finset.Icc 1 n, lam j (T - k)) *
            max (0 - (dynValueGo lam p n T k (x + 1) - dynValueGo lam p n T k x)) 0)

/-- `V_t(x)` of the dynamic model, Eq. (2.17), for periods `t = 1, …, T + 1`: `V_{T+1} = 0`. -/
noncomputable def dynValue (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T t x : ℕ) : ℝ :=
  dynValueGo lam p n T (T + 1 - t) x

/-- `ΔV_t(x) = V_t(x) − V_t(x − 1)`. -/
noncomputable def dynDelta (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T t x : ℕ) : ℝ :=
  dynValue lam p n T t x - dynValue lam p n T t (x - 1)

/-- `u ∈ {0, 1}` is an optimal decision for a class-`j` request in period `t` with `x` units
remaining: it maximizes `(p_j − ΔV_{t+1}(x)) u` over `u ∈ {0, 1}`, the inner optimization of
(2.17). -/
def IsDynOptimal (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T t x j u : ℕ) : Prop :=
  u ≤ 1 ∧ ∀ u' ≤ 1, (p j - dynDelta lam p n T (t + 1) x) * u' ≤ (p j - dynDelta lam p n T (t + 1) x) * u

open Classical in
/-- The time-dependent protection level `y_j*(t) = max {x : p_{j+1} < ΔV_{t+1}(x)}` of Eq. (2.19),
the search over `x = 1, …, C` and `0` when the set is empty. -/
noncomputable def dynProtLevel (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T C t j : ℕ) : ℕ :=
  ((Finset.range (C + 1)).filter
    (fun x => 1 ≤ x ∧ p (j + 1) < dynDelta lam p n T (t + 1) x)).sup id

/-- The time-dependent booking limit `b_j*(t) = C − y_{j−1}*(t)` of Eq. (2.20). -/
noncomputable def dynBookLimit (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T C t j : ℕ) : ℕ :=
  C - dynProtLevel lam p n T C t (j - 1)

/-- The bid price `π_t(x) = ΔV_t(x)` of Eq. (2.18). -/
noncomputable def dynBidPrice (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T t x : ℕ) : ℝ :=
  dynDelta lam p n T t x

/-! #### The choice model, Sect. 2.6.2 -/

/-- A discrete-choice model on the classes `Fin n`: `P S j` is the probability that an arriving
customer buys class `j` when the set `S` is offered, with `∑_{j ∈ S} P S j ≤ 1` (the rest is the
no-purchase probability `P_0(S)`). -/
def IsChoiceModel {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ) : Prop :=
  (∀ S j, 0 ≤ P S j) ∧ ∀ S, ∑ j ∈ S, P S j ≤ 1

/-- The total purchase probability `Q(S) = ∑_{j ∈ S} P_j(S)`. -/
def purchaseProb {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ j ∈ S, P S j

/-- The expected revenue `R(S) = ∑_{j ∈ S} P_j(S) p_j` from offering `S`. -/
def expRevenue {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ) (p : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ j ∈ S, P S j * p j

/-- The choice-model value function with `k` periods to go (period `t = T + 1 − k`), Eq. (2.26):
`V(x) = max_{S ⊆ N} λ_t (R(S) − Q(S) ΔV'(x)) + V'(x)`, with `V(0) = 0` and `V = 0` with no period
to go. -/
noncomputable def choiceValueGo {n : ℕ} (lam : ℕ → ℝ) (P : Finset (Fin n) → Fin n → ℝ)
    (p : Fin n → ℝ) (T : ℕ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | k + 1, x + 1 =>
      (Finset.univ : Finset (Finset (Fin n))).sup' Finset.univ_nonempty (fun S =>
        lam (T - k) * (expRevenue P p S - purchaseProb P S *
          (choiceValueGo lam P p T k (x + 1) - choiceValueGo lam P p T k x))) +
        choiceValueGo lam P p T k (x + 1)

/-- `V_t(x)` of the choice model, Eq. (2.24)/(2.26), for `t = 1, …, T + 1`: `V_{T+1} = 0`. -/
noncomputable def choiceValue {n : ℕ} (lam : ℕ → ℝ) (P : Finset (Fin n) → Fin n → ℝ)
    (p : Fin n → ℝ) (T t x : ℕ) : ℝ :=
  choiceValueGo lam P p T (T + 1 - t) x

/-- `ΔV_t(x) = V_t(x) − V_t(x − 1)` for the choice model. -/
noncomputable def choiceDelta {n : ℕ} (lam : ℕ → ℝ) (P : Finset (Fin n) → Fin n → ℝ)
    (p : Fin n → ℝ) (T t x : ℕ) : ℝ :=
  choiceValue lam P p T t x - choiceValue lam P p T t (x - 1)

/-- The objective `λ_t (R(S) − Q(S) ΔV_{t+1}(x))` of (2.26) for the offer set `S` in period `t`
with `x` units remaining. -/
noncomputable def choiceObj {n : ℕ} (lam : ℕ → ℝ) (P : Finset (Fin n) → Fin n → ℝ)
    (p : Fin n → ℝ) (T t x : ℕ) (S : Finset (Fin n)) : ℝ :=
  lam t * (expRevenue P p S - purchaseProb P S * choiceDelta lam P p T (t + 1) x)

/-- `S` is an optimal offer set in period `t` with `x` units remaining: it maximizes (2.26). -/
def IsChoiceOptimal {n : ℕ} (lam : ℕ → ℝ) (P : Finset (Fin n) → Fin n → ℝ) (p : Fin n → ℝ)
    (T t x : ℕ) (S : Finset (Fin n)) : Prop :=
  ∀ S', choiceObj lam P p T t x S' ≤ choiceObj lam P p T t x S

/-- Definition 2.1: `T'` is inefficient if a randomization `α` over the subsets of `N` yields at
most the purchase probability `Q(T')` and strictly more revenue than `R(T')`. -/
def IsInefficient {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ) (p : Fin n → ℝ)
    (T' : Finset (Fin n)) : Prop :=
  ∃ α : Finset (Fin n) → ℝ, (∀ S, 0 ≤ α S) ∧ ∑ S, α S = 1 ∧
    ∑ S, α S * purchaseProb P S ≤ purchaseProb P T' ∧
    expRevenue P p T' < ∑ S, α S * expRevenue P p S

/-- Definition 2.1: a set is efficient if it is not inefficient. -/
def IsEfficient {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ) (p : Fin n → ℝ)
    (S : Finset (Fin n)) : Prop :=
  ¬ IsInefficient P p S

end RevenueManagement


