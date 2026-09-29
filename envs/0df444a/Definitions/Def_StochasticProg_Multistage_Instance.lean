-- Prove2me | Definitions.Def_StochasticProg_Multistage_Instance
-- name    : StochasticProg_Multistage_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:07:54.589984+00:00
-- url     : https://prove2.me/theorems/a59042f3-52f5-4c10-a743-7fc13ce219a8
-- title:
--   Multistage recourse instance and its deterministic-equivalent LP
-- statement:
--   A **multistage stochastic linear program** over a scenario tree `T`, in the notation of
--   Birge & Louveaux's Eqs. (1.1)-(1.5) (p. 288) and the deterministic-equivalent problem
--   (3.4.1) it refers to.
--
--   `Instance H n m T` carries, for every node $k$: the stage cost $c^t_k \in \mathbb R^n$
--   (`c`), the recourse matrix $W^t \in \mathbb R^{m\times n}$ depending on the stage only
--   (`W`, matching the book's $W_t$, which carries no scenario subscript — fixed recourse per
--   stage), the transition matrix $T^{t-1}_k \in \mathbb R^{m\times n}$ (`Tmat`), the
--   right-hand side $h^t_k \in \mathbb R^m$ (`h`), the unconditional node probability $p^t_k$
--   (`p`, positive and summing to $1$ within each stage), and a finite upper bound $u^t_k \in
--   \mathbb R^n$ on $x^t_k$ (`ub`) — Theorem 1's hypothesis "all $x_t$ have finite upper
--   bounds" is exactly `ub` being real- rather than extended-real-valued.
--
--   `transitionTerm inst j xp` is $T^{t-1}_jx^{t-1}_{a(j)}$ for a non-root $j$, and $0$ for the
--   root (the book's initial-condition reading $b=h^1-T^0x^0$, p. 288 footnote to Step 0).
--   `LocalFeasible inst j xp xj` is node $j$'s own feasible region (1.2), (1.5) given its
--   parent's decision $xp$ — no cuts yet. `Feasible inst x` is the tree-wide feasible region of
--   the deterministic equivalent (3.4.1): every node feasible given its own parent's decision.
--   `obj inst x` is (3.4.1)'s objective, $\sum_k p^t_k (c^t_k)^Tx^t_k$.
--
--   **Formalization Note.** Every stage shares one decision dimension $n$ and one constraint
--   dimension $m$ (the book allows these to vary by stage; fixed here to a single reusable
--   `Fin n`/`Fin m` pair — see `MODERATION_NOTES.md`).
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, p. 288, Chapter 6, Section 6.1, Eqs. (1.1)-(1.5); Section 3.4, problem (3.4.1)

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree

namespace StochasticProg.Multistage

open scoped Matrix

variable {H n m : ℕ}

/-- A multistage stochastic linear program over a scenario tree `T`, in the notation of
Birge & Louveaux (3.4.1)/(1.1)-(1.5), p. 288. Every stage shares the same decision dimension
`n` and constraint dimension `m` (a convention: the book allows `x^t_k` to have its own
dimension per stage, fixed here for a single reusable `Fin n`/`Fin m` pair — see
`MODERATION_NOTES.md`). `W` is the recourse matrix `W^t` of Eq. (1.2), a function of the stage
only ("fixed recourse", matching the book's `Wt` carrying no scenario subscript); `Tmat`,
`h`, `c` are the scenario-dependent `T^{t-1}_k`, `h^t_k`, `c^t_k`. `p` is the *unconditional*
probability of reaching node `k` (the book's `p^t_k` is used only through ratios `p^t_k /
p^{t-1}_j`, which are the same whether `p` is read as conditional or unconditional, so long as
it is consistent up the tree — `hp_sum` pins the unconditional reading). `ub` is the finite
upper bound on `x^t_k` that Theorem 1 assumes ("all `x_t` have finite upper bounds", p. 289);
its being valued in `ℝ` rather than `ℝ ∪ {∞}` is exactly what makes it finite. -/
structure Instance (H n m : ℕ) (T : Tree H) where
  c : T.Node → Fin n → ℝ
  W : Fin H → Matrix (Fin m) (Fin n) ℝ
  Tmat : T.Node → Matrix (Fin m) (Fin n) ℝ
  h : T.Node → Fin m → ℝ
  p : T.Node → ℝ
  hp_pos : ∀ k, 0 < p k
  hp_sum : ∀ t : Fin H, ∑ k ∈ Finset.univ.filter (fun k => T.stage k = t), p k = 1
  ub : T.Node → Fin n → ℝ

variable {T : Tree H} (inst : Instance H n m T)

/-- The transition term entering node `j`'s equality constraint (1.2): `T^{t-1}_j x^{t-1}_{a(j)}`
for a non-root `j`, and the book's initial-condition reading `b = h^1 - T^0 x^0` (i.e. no
transition term at all) for the root (p. 288, footnote to Step 0). -/
def transitionTerm (j : T.Node) (xp : Fin n → ℝ) : Fin m → ℝ :=
  if (T.stage j).val = 0 then 0 else Matrix.mulVec (inst.Tmat j) xp

/-- Node `j`'s own feasible region given its parent's decision `xp` (`0` when `j` is the
root): bounds `0 ≤ x^t_j ≤ ub^t_j` (1.5) and the equality constraint (1.2). Does not include
any cuts (1.3)-(1.4); those are added by the algorithm and live in
`Def_StochasticProg_Multistage_Algorithm`. -/
def LocalFeasible (j : T.Node) (xp : Fin n → ℝ) (xj : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ xj i ∧ xj i ≤ inst.ub j i) ∧
    Matrix.mulVec (inst.W (T.stage j)) xj = inst.h j - transitionTerm inst j xp

/-- The tree-wide feasible region of the deterministic equivalent (3.4.1): an assignment of a
decision to every node, feasible for its own parent's decision at every node. This is the
object Theorem 1's "optimal solution of (3.4.1)" and the algorithm's termination test refer
to; it carries no cuts, unlike the algorithm's intermediate `LocalFeasible`. -/
def Feasible (x : T.Node → Fin n → ℝ) : Prop :=
  ∀ j : T.Node, LocalFeasible inst j (x (T.anc j)) (x j)

/-- The deterministic-equivalent objective of (3.4.1): the probability-weighted sum of every
node's own stage cost, `∑_k p_k (c^t_k)ᵀ x^t_k`. -/
def obj (x : T.Node → Fin n → ℝ) : ℝ :=
  ∑ j : T.Node, inst.p j * dotProduct (inst.c j) (x j)

end StochasticProg.Multistage


