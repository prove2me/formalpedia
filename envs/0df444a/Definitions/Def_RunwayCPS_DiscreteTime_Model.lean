-- Prove2me | Definitions.Def_RunwayCPS_DiscreteTime_Model
-- name    : RunwayCPS_DiscreteTime_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:14:18.623785+00:00
-- url     : https://prove2.me/theorems/2b2269d4-06d8-41e3-b568-ecdf8dce1003
-- title:
--   §2, §6, §6.1: discrete-time runway instance, k-CPS sequences, feasible schedules with pairwise separations, separable cost, triangle and polygon inequalities
-- statement:
--   This file fixes the discrete-time runway scheduling model of Balakrishnan and Chandran.
--
--   **Instance.** There are $n$ aircraft, labelled in first-come-first-served (FCFS) order. All data are integer multiples of a fixed time period and are measured in periods. The instance consists of
--
--   1. the maximum position shift $k\in\mathbb N$;
--   2. the minimum separations $\delta_{ab}\in\mathbb N$ between a leading aircraft $a$ and a trailing aircraft $b$;
--   3. a time window $[e_a,l_a]$ (integers) for each aircraft $a$;
--   4. a finite set of precedence pairs $(x,y)$, meaning that $x$ must land before $y$;
--   5. a cost $c_a(t)\in\mathbb R$ of landing aircraft $a$ at period $t$.
--
--   **Schedules.** A sequence is a bijection $\sigma$ from positions to aircraft; it is **$k$-CPS** if every aircraft sits at most $k$ positions from its FCFS position, $|\sigma(p)-p|\le k$. A **feasible schedule** is a $k$-CPS sequence $\sigma$ together with integer landing times $t_p$ by position such that every precedence pair is respected, every aircraft lands inside its window, $e_{\sigma(p)}\le t_p\le l_{\sigma(p)}$, and every pair of aircraft is separated:
--   $$
--   t_q-t_p\;\ge\;\delta_{\sigma(p)\sigma(q)}\qquad\text{for all positions } p<q .
--   $$
--   The **cost** of a schedule is $\sum_p c_{\sigma(p)}(t_p)$.
--
--   **Inequalities on separations.** The *triangle inequality* is $\delta_{ac}\le\delta_{ab}+\delta_{bc}$ for all $a,b,c$. The *polygon inequalities of three or more hops* require, for every $m\ge 3$ and every chain $x_0,\dots,x_m$ of distinct aircraft,
--   $$
--   \delta_{x_0x_m}\;\le\;\sum_{i=0}^{m-1}\delta_{x_ix_{i+1}} ;
--   $$
--   the quadrilateral inequality is the case $m=3$. They do not include the triangle inequality.
--
--   These are the objects every statement of the mission is about; separation is required for all pairs, not only consecutive ones, because the triangle inequality is not assumed.
--
--   **Formalization Note** Aircraft and positions are $0$-based (`Fin n`): label $a$ is the paper's aircraft $a+1$. Times, windows and separations are natural numbers (periods); the separation constraint is written $t_p+\delta\le t_q$. The polygon inequalities are not stated in the paper as a hypothesis of §6.2; §7 asserts them for mixed operations, and they are needed for Lemma 5.
-- source:
--   Balakrishnan & Chandran, Algorithms for Scheduling Runway Operations Under Constrained Position Shifting, Oper. Res. 58(6) (2010), pp. 1651–1652, §2 items 1–4; p. 1656, §6 (integer data); p. 1657, §6.1 (costs c(a, t_a)); p. 1660, §7 (polygon inequalities)

import Mathlib
import Definitions.Def_RunwayCPS_Makespan_Network

namespace RunwayCPS.DiscreteTime

/-- A discrete-time runway scheduling instance with `n` aircraft (§2, §6, §6.1). All data are
integer multiples of one time period and are measured in periods. Aircraft are labelled
`0, …, n-1` in FCFS order (label `a` is the paper's aircraft `a + 1`). `k` is the maximum
position shift, `δ a b` the minimum separation (in periods) between leading aircraft `a` and
trailing aircraft `b`, `[e a, l a]` the time window of aircraft `a`, `(x, y) ∈ prec` means
that `x` must land before `y`, and `c a t` is the cost of landing aircraft `a` at period `t`. -/
structure Instance (n : ℕ) where
  k : ℕ
  δ : Fin n → Fin n → ℕ
  e : Fin n → ℕ
  l : Fin n → ℕ
  prec : Finset (Fin n × Fin n)
  c : Fin n → ℕ → ℝ

variable {n : ℕ}

/-- A feasible discrete-time schedule (§2, §6): a `k`-CPS sequence `σ` (position ↦ aircraft)
with integer landing times by position `t`, satisfying the time windows, the **pairwise**
minimum separations between every leading and every trailing aircraft (`t q - t p ≥ δ`
for `p < q`), and the precedence constraints. The triangle inequality is not assumed. -/
def IsFeasible (I : Instance n) (σ : Fin n → Fin n) (t : Fin n → ℕ) : Prop :=
  RunwayCPS.Makespan.IsCPS I.k σ ∧
  (∀ p : Fin n, I.e (σ p) ≤ t p ∧ t p ≤ I.l (σ p)) ∧
  (∀ p q : Fin n, p < q → t p + I.δ (σ p) (σ q) ≤ t q) ∧
  RunwayCPS.Makespan.RespectsPrec I.prec σ

/-- The cost of a schedule (§6.1): the sum over positions of the cost of landing the aircraft
in that position at its landing time, `∑_p c_{σ p}(t p)`. -/
def cost (I : Instance n) (σ : Fin n → Fin n) (t : Fin n → ℕ) : ℝ :=
  ∑ p : Fin n, I.c (σ p) (t p)

/-- The set of costs of feasible schedules. -/
def scheduleCosts (I : Instance n) : Set ℝ :=
  {x | ∃ σ t, IsFeasible I σ t ∧ x = cost I σ t}

/-- The triangle inequality for the separations (§2 item 2): `δ_ac ≤ δ_ab + δ_bc` for all
aircraft `a, b, c`. -/
def TriangleIneq (δ : Fin n → Fin n → ℕ) : Prop :=
  ∀ a b c : Fin n, δ a c ≤ δ a b + δ b c

/-- The polygon inequalities of three or more hops (§2 item 2, §7): for every `m ≥ 3` and
every chain `x 0, x 1, …, x m` of `m + 1` distinct aircraft,
`δ (x 0) (x m) ≤ ∑_{i < m} δ (x i) (x (i+1))`. The quadrilateral inequality is `m = 3`.
The triangle inequality (`m = 2`) is **not** part of this hypothesis. -/
def PolygonIneq (δ : Fin n → Fin n → ℕ) : Prop :=
  ∀ m : ℕ, 3 ≤ m → ∀ x : Fin (m + 1) → Fin n, Function.Injective x →
    δ (x 0) (x (Fin.last m)) ≤ ∑ i : Fin m, δ (x i.castSucc) (x i.succ)

end RunwayCPS.DiscreteTime


