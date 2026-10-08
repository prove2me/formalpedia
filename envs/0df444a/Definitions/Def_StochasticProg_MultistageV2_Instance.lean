-- Prove2me | Definitions.Def_StochasticProg_MultistageV2_Instance
-- name    : StochasticProg_MultistageV2_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T16:22:04.565989+00:00
-- url     : https://prove2.me/theorems/f041717c-c438-4a7f-b9c4-8902d66411a6
-- title:
--   Multistage stochastic linear program on a scenario tree
-- statement:
--   Let $T$ be a finite scenario tree with $H$ stages, ancestor map $a(\cdot)$ and root $1$. A *multistage stochastic linear program* on $T$ consists of, for every node $k$ at stage $t$, a cost vector $c^t_k\in\mathbb{R}^n$, a right-hand side $h^t_k\in\mathbb{R}^m$, a technology matrix $T^{t-1}_k\in\mathbb{R}^{m\times n}$ and a probability $p^t_k>0$, together with a stage recourse matrix $W^t\in\mathbb{R}^{m\times n}$; the probabilities of the nodes of each stage sum to $1$. Node $k$'s decision $x^t_k\ge 0$ is subject to $W^t x^t_k = h^t_k - T^{t-1}_k x^{t-1}_{a(k)}$ (for the root, $W^1x^1 = h^1$). Upper bounds on variables are rows of $W^t$ with slack columns.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed. (2011), Ch. 6, §6.1, problem (3.4.1) and subproblems (1.1)–(1.5), p. 267 (PDF p. 288)

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree

namespace StochasticProg.MultistageV2

/-- A multistage stochastic linear program (3.4.1) over a finite scenario tree `T`, in the
notation of Birge & Louveaux §6.1, (1.1)–(1.5), p. 267. Node `k` at stage `t` carries the
decision `x^t_k ∈ ℝⁿ`, `x^t_k ≥ 0`, subject to the standard-form constraint (1.2)
`W^t x^t_k = h^t_k - T^{t-1}_k x^{t-1}_{a(k)}`; `W` is the stage-dependent recourse matrix
`W^t` (no scenario index in the book), `Tmat`, `h`, `c` are the scenario data
`T^{t-1}_k`, `h^t_k`, `c^t_k`, and `p k` is the (unconditional) probability `p^t_k` of
scenario `k`, which enters the method only through the ratios `p^t_k / p^{t-1}_j` of Step 2
(p. 268). All stages use the same dimensions `n`, `m` (pad a smaller stage with dummy variables forced to
0 by extra independent rows, e.g. `v = 0`; zero columns or zero rows would break the theorem's `hbdd`/`hrank`).
Upper bounds on the variables are *not* a separate field: as in (1.1)–(1.5), whose only sign
constraint is (1.5) `x ≥ 0`, any bound `x_i ≤ u_i` is a row of `W^t` with a slack column; the
hypothesis "all `x_t` have finite upper bounds" is stated in the theorem. -/
structure Instance (H n m : ℕ) (T : Multistage.Tree H) where
  /-- stage cost `c^t_k` -/
  c : T.Node → Fin n → ℝ
  /-- recourse matrix `W^t` -/
  W : Fin H → Matrix (Fin m) (Fin n) ℝ
  /-- technology matrix `T^{t-1}_k` linking node `k` to its ancestor `a(k)` -/
  Tmat : T.Node → Matrix (Fin m) (Fin n) ℝ
  /-- right-hand side `h^t_k` (for the root, the book's initial condition `b = h^1 - T^0 x^0`) -/
  h : T.Node → Fin m → ℝ
  /-- scenario probability `p^t_k` -/
  p : T.Node → ℝ
  hp_pos : ∀ k, 0 < p k
  hp_sum : ∀ t : Fin H, ∑ k ∈ Finset.univ.filter (fun k => T.stage k = t), p k = 1

end StochasticProg.MultistageV2


