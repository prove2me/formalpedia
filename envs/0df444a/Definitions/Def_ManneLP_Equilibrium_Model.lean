-- Prove2me | Definitions.Def_ManneLP_Equilibrium_Model
-- name    : ManneLP_Equilibrium_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:36:26.657837+00:00
-- url     : https://prove2.me/theorems/6dd539df-cc44-4ee7-bf07-adc317cd097a
-- title:
--   §2–§3 — Manne's inventory model: stock levels 0..T, admissible pairs (i, j), demand law pₙ, terminal stock max(0, k − n), costs C₁, C₂, C₃
-- statement:
--   This file sets up the single-item inventory model of Manne (1960), §2–§3.
--
--   At the start of each month the **initial stock** $i$ is observed; the decision-maker then chooses a **production quantity** $j$, so that the **available stock** is $k=i+j$. The month's **demand** $n\in\{0,1,2,\dots\}$ is drawn independently of everything else, with $\Pr(n)=p_n$, where $p_n\ge 0$ and $\sum_n p_n=1$. Backlogs are ruled out, so the **terminal stock** is
--   $$
--   t=\max(0,\,k-n),
--   $$
--   and it becomes next month's initial stock. A model consists of:
--
--   1. a positive integer $T$, the upper limit on inventory accumulation; the stock levels are $0,1,\dots,T$;
--   2. a finite set $A$ of **admissible pairs** $(i,j)$ of nonnegative integers, the pairs that carry an unknown $x_{ij}$ in the linear program. Every admissible pair has $i+j\le T$, so the terminal stock never exceeds $T$, and producing nothing, $(i,0)$, is admissible at every stock level $i\le T$;
--   3. the demand law $(p_n)_{n\ge 0}$;
--   4. three real cost functions: $C_1(i)$ attached to the initial stock, $C_2(j)$ attached to the production quantity, and $C_3(m)$ attached to the shortage level $m=n-k$, an integer that is negative when demand falls short of the available stock. No convexity, sign or monotonicity is assumed of $C_1,C_2,C_3$.
--
--   The file also defines the admissible actions at stock level $i$, $\{j : (i,j)\in A\}$, and the probability that the terminal stock equals $t$ when the available stock is $k$,
--   $$
--   \Pr\big(\max(0,k-n)=t\big)=\sum_{n:\ \max(0,k-n)=t} p_n .
--   $$
--
--   Every statement of the mission is made in this model.
--
--   **Formalization Note** Stock levels and production quantities are natural numbers; the shortage level $n-k$ is an integer. In $\mathbb N$, truncated subtraction $k-n$ is exactly $\max(0,k-n)$, which is how the terminal stock is computed. The demand law is a function $p:\mathbb N\to\mathbb R$ with `HasSum p 1`; the demand is not assumed bounded. The admissible set is a parameter rather than all of $\{i+j\le T\}$ because §6 adds a capacity limit $j\in\{0,1\}$. Reading of the page: the condition $i+j\le T$ is how §2's requirement "$t=\max(0,k-n)\le T$" holds whatever the demand, and §3 (5) lets $k$ run over $0,\dots,T$; the condition $(i,0)\in A$ (producing nothing is always possible) is implicit in §2 and holds in §6.
-- source:
--   Manne, Linear Programming and Sequential Decisions, Management Science 6 (1960), pp. 260–261 (PDF pp. 3–4), §2 and §3, DF: yᵢ, xᵢⱼ, zₖ, pₙ

import Mathlib

namespace ManneLP.Equilibrium

/-- Manne's single-item inventory model (Manne 1960, §2–§3, pp. 260–261).

* `T` is the positive integer upper limit on inventory accumulation; stock levels are
  `0, 1, …, T`.
* `A` is the finite set of admissible pairs `(i, j)` (initial stock `i`, production `j`) that
  carry an unknown `xᵢⱼ`. Every admissible pair has available stock `k = i + j ≤ T`, so the
  terminal stock `max(0, k − n)` never exceeds `T`; producing nothing is admissible at every
  stock level `i ≤ T`.
* `p n` is the probability that `n` units are demanded in a month (serially independent).
* `C₁ i`, `C₂ j`, `C₃ m` are the costs attached to the initial stock `i`, the production
  quantity `j` and the shortage level `m = n − k` (an integer, negative when demand is below the
  available stock). No convexity, sign or monotonicity is assumed. -/
structure Model where
  T : ℕ
  T_pos : 0 < T
  A : Finset (ℕ × ℕ)
  A_le : ∀ a ∈ A, a.1 + a.2 ≤ T
  zero_mem : ∀ i, i ≤ T → (i, 0) ∈ A
  p : ℕ → ℝ
  p_nonneg : ∀ n, 0 ≤ p n
  p_hasSum : HasSum p 1
  C₁ : ℕ → ℝ
  C₂ : ℕ → ℝ
  C₃ : ℤ → ℝ

/-- The stock levels `0, 1, …, T`. -/
def states (M : Model) : Finset ℕ := Finset.range (M.T + 1)

/-- The production quantities admissible at initial stock `i`: those `j` with `(i, j) ∈ A`. -/
def actions (M : Model) (i : ℕ) : Finset ℕ :=
  (Finset.range (M.T + 1)).filter (fun j => (i, j) ∈ M.A)

/-- The probability that the month-end stock `max(0, k − n)` equals `t` when the available stock
is `k` and the demand `n` has law `p`. In `ℕ`, truncated subtraction `k - n` is exactly
`max(0, k − n)`. -/
noncomputable def termProb (M : Model) (k t : ℕ) : ℝ :=
  ∑' n : ℕ, if k - n = t then M.p n else 0

end ManneLP.Equilibrium


