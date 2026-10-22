-- Prove2me | Definitions.Def_DynamicOnlineLP_LowerBound_OnlineLP
-- name    : DynamicOnlineLP_LowerBound_OnlineLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T19:56:51.035087+00:00
-- url     : https://prove2.me/theorems/783db213-d3c3-4865-bab0-43538bb9e5f7
-- title:
--   Online linear programming in the random permutation model: offline LP (1), OPT, online algorithms for (2), expected online value
-- statement:
--   An instance of **online linear programming** consists of $n$ columns indexed by $t$, each with an objective coefficient $\pi_t$ and a constraint column $a_t=(a_{1t},\dots,a_{mt})\in\mathbb R^m$, and a right-hand side $b\in\mathbb R^m$. The **offline linear program** is
--
--   $$\mathrm{OPT}=\max\ \sum_{t}\pi_t x_t\quad\text{s.t.}\quad \sum_t a_{it}x_t\le b_i\ (i=1,\dots,m),\qquad 0\le x_t\le 1 .$$
--
--   In the **online** problem the columns arrive one at a time in the order $\sigma(1),\dots,\sigma(n)$, where $\sigma$ is a uniformly random permutation of the columns (the random permutation model). At each time $t$ an **online algorithm** sees the number of columns $n$ and the right-hand side $b$ (both known in advance) and the columns revealed so far, $(\pi_{\sigma(1)},a_{\sigma(1)}),\dots,(\pi_{\sigma(t)},a_{\sigma(t)})$, and must irrevocably choose $x_t\in[0,1]$ so that the online constraint
--
--   $$\sum_{s\le t} a_{i\sigma(s)}\,x_s\le b_i\qquad(i=1,\dots,m)$$
--
--   holds. It never sees the columns that have not yet arrived. Its value on the order $\sigma$ is $\sum_t \pi_{\sigma(t)}x_t$, and its **expected online value** is the average of this value over all $n!$ arrival orders. An algorithm is $c$-competitive when its expected online value is at least $c\cdot\mathrm{OPT}$.
--
--   This file defines feasibility for the offline problem, its objective and optimal value $\mathrm{OPT}$, online algorithms, the decisions an online algorithm makes on a given arrival order, its value on that order, and its expected value over a uniformly random order.
--
--   **Formalization Note** $\mathrm{OPT}$ is a real `sSup` over the feasible set; for $b\ge 0$ the set contains $x=0$ and the objective is bounded, so it is the true, attained optimum, and it is only used with $b\ge 0$. An algorithm is a function `propose` of $(n, b, \text{revealed columns as a list, current last})$ returning a real number; a proposal that would violate $0\le x_t\le 1$ or the online constraint is replaced by $x_t=0$ (a rejection), so every run satisfies the online constraint, and an algorithm whose proposals always satisfy it runs unchanged. The algorithm's own earlier decisions are a function of the revealed prefix and are therefore not a separate input. Algorithms are deterministic and fractional: the expected decisions of a randomized algorithm (averaged over its internal randomness, which is independent of the instance) form a deterministic fractional algorithm with the same expected value that still satisfies the online constraint, because the constraint is linear. Times are 0-based in Lean. The expectation over $\sigma$ is the finite average $\frac1{n!}\sum_{\sigma}$ over `Equiv.Perm (Fin n)`.
-- source:
--   Agrawal, Wang, Ye, A Dynamic Near-Optimal Algorithm for Online Linear Programming, Oper. Res. 62(4), 2014, p. 876, Eqs. (1)–(2); p. 877, Assumptions 1–2 and Definition 1

import Mathlib

namespace DynamicOnlineLP.LowerBound

/-- Feasibility for the offline linear program (1) of Agrawal–Wang–Ye 2014 (p. 876) on a finite
set of columns `ι`: `∑_t a_{it} x_t ≤ b_i` for every row `i`, and `0 ≤ x_t ≤ 1` for every column. -/
def IsFeasible {ι : Type} [Fintype ι] {m : ℕ} (a : ι → Fin m → ℝ) (b : Fin m → ℝ)
    (x : ι → ℝ) : Prop :=
  (∀ i : Fin m, ∑ t, a t i * x t ≤ b i) ∧ ∀ t, 0 ≤ x t ∧ x t ≤ 1

/-- Objective `∑_t π_t x_t` of (1). -/
def objective {ι : Type} [Fintype ι] (π : ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ t, π t * x t

/-- `OPT`, the optimal value of the offline problem (1), as the supremum of the objective over the
feasible set. When `0 ≤ b` the feasible set contains `x = 0` and the objective is bounded by
`∑ |π_t|`, so this is the true (attained) optimum; every statement of the mission uses it only for
such `b`. -/
noncomputable def OPT {ι : Type} [Fintype ι] {m : ℕ} (π : ι → ℝ) (a : ι → Fin m → ℝ)
    (b : Fin m → ℝ) : ℝ :=
  sSup (objective π '' {x : ι → ℝ | IsFeasible a b x})

/-- A deterministic online algorithm for the online LP (2) with `m` constraints. At each time it
is given the total number of columns `n` (Assumption 2), the right-hand side `b`, and the list of
the columns `(π_1, a_1), …, (π_t, a_t)` revealed so far in arrival order (the current column last),
and proposes the decision `x_t`. It is never given the unrevealed columns. Its own earlier decisions
are a function of these data, so it does not need them as an input. -/
structure OnlineAlgorithm (m : ℕ) where
  /-- `propose n b revealed` is the proposed value of the current decision. -/
  propose : ℕ → (Fin m → ℝ) → List (ℝ × (Fin m → ℝ)) → ℝ

/-- The column `(π_{σ(s)}, a_{σ(s)})` arriving at (0-based) time `s` when the columns of the
instance arrive in the order `σ`; `(0, 0)` for `s ≥ n` (never used). -/
def arrival {m n : ℕ} (π : Fin n → ℝ) (a : Fin n → Fin m → ℝ) (σ : Equiv.Perm (Fin n))
    (s : ℕ) : ℝ × (Fin m → ℝ) :=
  if h : s < n then (π (σ ⟨s, h⟩), a (σ ⟨s, h⟩)) else (0, 0)

/-- The decisions of the online algorithm `A` on the instance `(π, a, b)` with arrival order `σ`,
after the first `t` arrivals: `decisions A π a b σ t s` is the decision `x_s` made at (0-based) time
`s` for `s < t`, and `0` for `s ≥ t`.

At time `t` the algorithm sees `n`, `b` and the revealed columns `arrival … 0, …, arrival … t`
and proposes `p`. The proposal is carried out when it satisfies the online constraint (2), i.e.
`0 ≤ p ≤ 1` and `∑_{s<t} a_{i,σ(s)} x_s + a_{i,σ(t)} p ≤ b_i` for every `i`; otherwise
`x_t = 0` (the column is rejected, as in step 2(b) of the paper's algorithm DLA). An algorithm
whose proposals always satisfy (2) is therefore run unchanged, and every run satisfies (2). -/
noncomputable def decisions {m n : ℕ} (A : OnlineAlgorithm m) (π : Fin n → ℝ)
    (a : Fin n → Fin m → ℝ) (b : Fin m → ℝ) (σ : Equiv.Perm (Fin n)) : ℕ → ℕ → ℝ
  | 0 => fun _ => 0
  | t + 1 =>
    let prev := decisions A π a b σ t
    let p := A.propose n b ((List.range (t + 1)).map (arrival π a σ))
    let xt : ℝ :=
      if 0 ≤ p ∧ p ≤ 1 ∧
          ∀ i : Fin m, ∑ s ∈ Finset.range t, (arrival π a σ s).2 i * prev s
            + (arrival π a σ t).2 i * p ≤ b i
      then p else 0
    fun s => if s < t then prev s else if s = t then xt else 0

/-- The value `∑_{t=1}^{n} π_{σ(t)} x_t` collected by the online algorithm `A` when the columns
arrive in the order `σ`. -/
noncomputable def onlineValue {m n : ℕ} (A : OnlineAlgorithm m) (π : Fin n → ℝ)
    (a : Fin n → Fin m → ℝ) (b : Fin m → ℝ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ s ∈ Finset.range n, (arrival π a σ s).1 * decisions A π a b σ n s

/-- The expected online value `E_σ[∑_t π_{σ(t)} x_t]` in the random permutation model
(Assumption 1, Definition 1): the average of `onlineValue` over all `n!` arrival orders `σ`. -/
noncomputable def expectedOnlineValue {m n : ℕ} (A : OnlineAlgorithm m) (π : Fin n → ℝ)
    (a : Fin n → Fin m → ℝ) (b : Fin m → ℝ) : ℝ :=
  (∑ σ : Equiv.Perm (Fin n), onlineValue A π a b σ) / (Nat.factorial n : ℝ)

end DynamicOnlineLP.LowerBound


