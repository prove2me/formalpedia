-- Prove2me | Definitions.Def_LowerFareFirst_Critical_Model
-- name    : LowerFareFirst_Critical_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:38.784296+00:00
-- url     : https://prove2.me/theorems/7dcb6681-5e26-4d3c-a10b-fdec245b61ad
-- title:
--   §1, p. 28, Eqs. (2a)–(2b) — fare classes booking low before high, optimal value Z_m(n), ΔZ_m(n), critical values k_m
-- statement:
--   This file fixes the model of Wollmer's single-leg seat management problem in which the lower fare classes book first.
--
--   **Fare classes and demands.** There are $c \ge 2$ fare classes, numbered $1, \dots, c$ from the highest fare to the lowest; class $m$ pays the fare $r_m$, with
--   $$r_1 > r_2 > \cdots > r_c > 0 .$$
--   The demand of class $m$ is a random number $D_m \in \{0, 1, 2, \dots\}$ of future booking requests, defined on a probability space $(\Omega, \mu)$. We write
--   $$P[D_m = i], \qquad P[D_m \ge n], \qquad P[D_m \le i]$$
--   for the probabilities of the corresponding events. Only the marginal law of each $D_m$ enters the model.
--
--   **The booking process.** All seats form one pool; $n$ denotes the number of empty seats. Requests arrive class by class, the lowest class first: all requests of class $m$ arrive before those of classes $1, \dots, m-1$.
--
--   **Optimal value.** $Z_m(n)$ is the expected revenue under an optimal policy when $n$ seats are empty and reservations may be accepted for classes $1, \dots, m$ only. It is defined by the dynamic-programming recursion
--   $$Z_0(n) = 0, \qquad Z_m(n) = \mathbb E\Big[\max_{0 \le x \le \min(D_m, n)} \big( r_m x + Z_{m-1}(n - x) \big)\Big] \quad (m \ge 1):$$
--   after observing the $D_m$ requests of class $m$, the airline accepts $x$ of them, earns $r_m x$, and classes $1, \dots, m-1$ then face $n - x$ empty seats.
--
--   **Marginal seat value.** For $n \ge 1$,
--   $$\Delta Z_m(n) = Z_m(n) - Z_m(n-1).$$
--
--   **Critical values** (Eqs. (2a)–(2b)). $k_1 = 0$ and, for $m > 1$,
--   $$k_m = \max\{\, n \ge 1 \mid r_m < \Delta Z_{m-1}(n) \,\}.$$
--   The predicate "$k$ is the critical value of class $m$" says that $k$ is the greatest element of this set.
--
--   **The critical-value rule.** For a class $m$ and a number $k$, the rule "reject a class-$m$ request when $n \le k$ and accept it when $n \ge k + 1$" accepts $\min(D_m, (n-k)^+)$ of the $D_m$ requests. The predicate *the critical-value rule is optimal for class $m$ with critical value $k$* states that, for every number $n$ of empty seats, every realized demand $d$ and every admissible $x \le \min(d, n)$,
--   $$r_m x + Z_{m-1}(n-x) \le r_m \min(d, (n-k)^+) + Z_{m-1}\big(n - \min(d, (n-k)^+)\big),$$
--   with strict inequality whenever $x > (n-k)^+$: the rule attains the maximum in the recursion for $Z_m(n)$, and accepting more requests than it does is strictly worse.
--
--   **Standing assumptions** (§1). The model predicate bundles: $\mu$ is a probability measure; each $D_m$ is measurable; $c \ge 2$; $r_1 > r_2 > \cdots > r_c$; $r_2 < r_1 P[D_1 \ge 1]$ (so that a class 2 reservation is refused when $n = 1$); and $r_c > 0$.
--
--   These objects are shared by every statement of the mission: Eqs. (3)–(6), Lemma 1 and Theorems 1–2 of the paper are statements about $Z_m$, $\Delta Z_m$ and $k_m$.
--
--   **Formalization Note.** Classes are indexed by natural numbers starting at $1$; fares and demands are sequences $r : \mathbb N \to \mathbb R$ and $D : \mathbb N \to \Omega \to \mathbb N$, of which only the entries $1, \dots, c$ are constrained. The paper defines $Z_m(n)$ in words; the recursion above is its reading. The inner maximum lets the number of accepted requests depend on the realized $D_m$; this is no advantage over deciding request by request, since the maximizer $\min(D_m,(n-k_m)^+)$ is "accept while more than $k_m$ seats remain", which the goal theorem proves. Independence of $D_1, \dots, D_c$ is not assumed, as the recursion reads only the marginal laws; for independent demands, the setting of the paper, $Z_m$ is the optimal expected revenue. The integrand of the recursion is bounded and depends on $\omega$ only through $D_m(\omega)$, so it is integrable once $D_m$ is measurable. $\Delta Z_m(n)$ is only used at $n \ge 1$ (at $n = 0$ the natural-number subtraction would give $0$). The assumption $r_c > 0$ is an addition to the page: with $r_c \le 0$ and unbounded demand, the maximum in (2b) need not exist.
-- source:
--   Wollmer (1992), Operations Research 40(1), §1, p. 28, Eqs. (2a)–(2b); §3, p. 28; proof of Lemma 1, p. 29

import Mathlib

namespace LowerFareFirst.Critical

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `P[D_m = i]` (Wollmer 1992, p. 28): the probability that fare class `m` has exactly `i` future booking
requests. -/
noncomputable def probEq (μ : Measure Ω) (D : ℕ → Ω → ℕ) (m i : ℕ) : ℝ :=
  μ.real {ω | D m ω = i}

/-- `P[D_m ≥ n]`. -/
noncomputable def probGe (μ : Measure Ω) (D : ℕ → Ω → ℕ) (m n : ℕ) : ℝ :=
  μ.real {ω | n ≤ D m ω}

/-- `P[D_m ≤ i]`. -/
noncomputable def probLe (μ : Measure Ω) (D : ℕ → Ω → ℕ) (m i : ℕ) : ℝ :=
  μ.real {ω | D m ω ≤ i}

/-- `Z_m(n)` (p. 28): the expected revenue under an optimal policy when `n` seats are empty and reservations
may be accepted for classes `1, …, m` only, lower classes booking first. `Z_0 = 0`; class `m` books first, `x`
of its `D_m` requests are accepted (`x ≤ min(D_m, n)`), earning `r_m x`, and classes `1, …, m - 1` then face
`n - x` empty seats. -/
noncomputable def Z (μ : Measure Ω) (D : ℕ → Ω → ℕ) (r : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | m + 1, n =>
      ∫ ω, (Finset.range (min (D (m + 1) ω) n + 1)).sup' Finset.nonempty_range_add_one
        (fun x => r (m + 1) * (x : ℝ) + Z μ D r m (n - x)) ∂μ

/-- `ΔZ_m(n) = Z_m(n) - Z_m(n - 1)` for `n ≥ 1` (p. 28). Only used at `n ≥ 1`. -/
noncomputable def dZ (μ : Measure Ω) (D : ℕ → Ω → ℕ) (r : ℕ → ℝ) (m n : ℕ) : ℝ :=
  Z μ D r m n - Z μ D r m (n - 1)

/-- `k` is the critical value `k_m = max {n | r_m < ΔZ_{m-1}(n)}` of class `m > 1` (Eq. (2b), p. 28),
`n` ranging over `n ≥ 1`. -/
def IsCriticalValue (μ : Measure Ω) (D : ℕ → Ω → ℕ) (r : ℕ → ℝ) (m k : ℕ) : Prop :=
  IsGreatest {n : ℕ | 1 ≤ n ∧ r m < dZ μ D r (m - 1) n} k

/-- The critical-value rule is optimal for class `m` with critical value `k` (§3, p. 28: "an optimal policy is
to reject a class m request if n ≤ k_m and accept it if n ≥ k_m + 1"): for every number `n` of empty seats and
every number `d` of class-`m` requests, accepting `min(d, (n - k)⁺)` of them (accept while more than `k` seats
remain) attains the maximum in the recursion for `Z_m(n)`, and accepting more than `(n - k)⁺` is strictly
worse. -/
def CriticalRuleOptimal (μ : Measure Ω) (D : ℕ → Ω → ℕ) (r : ℕ → ℝ) (m k : ℕ) : Prop :=
  ∀ n d x : ℕ, x ≤ min d n →
    r m * (x : ℝ) + Z μ D r (m - 1) (n - x)
        ≤ r m * ((min d (n - k) : ℕ) : ℝ) + Z μ D r (m - 1) (n - min d (n - k)) ∧
      (n - k < x →
        r m * (x : ℝ) + Z μ D r (m - 1) (n - x)
          < r m * ((min d (n - k) : ℕ) : ℝ) + Z μ D r (m - 1) (n - min d (n - k)))

/-- The standing assumptions of §1 (p. 28) for `c` fare classes: `μ` is a probability measure; the demands are
measurable; there are at least two classes; the fares are strictly decreasing, `r_1 > r_2 > ⋯ > r_c`;
`r_2 < r_1 P[D_1 ≥ 1]` (p. 28); and the lowest fare is positive (added: it makes the maximum in (2b) exist). -/
structure IsSeatModel (μ : Measure Ω) (D : ℕ → Ω → ℕ) (r : ℕ → ℝ) (c : ℕ) : Prop where
  isProb : IsProbabilityMeasure μ
  meas : ∀ m, Measurable (D m)
  two_le : 2 ≤ c
  fare_strictAnti : ∀ m, 1 ≤ m → m < c → r (m + 1) < r m
  fare_pos : 0 < r c
  two_class : r 2 < r 1 * probGe μ D 1 1

end LowerFareFirst.Critical


