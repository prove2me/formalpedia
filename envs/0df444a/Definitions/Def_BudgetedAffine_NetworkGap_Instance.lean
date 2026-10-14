-- Prove2me | Definitions.Def_BudgetedAffine_NetworkGap_Instance
-- name    : BudgetedAffine_NetworkGap_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:25:49.297325+00:00
-- url     : https://prove2.me/theorems/ce54b70c-a1b7-4c63-9ea2-9e315c3970c0
-- title:
--   (7.2) — the bipartite lot-sizing family with m = 2k nodes, and the affine solution of App. D, p. 37
-- statement:
--   **The family of instances (7.2).** Let $m=2k$. The nodes form a bipartite network $(J_1,J_2)$ with $|J_1|=|J_2|=k=m/2$. The data are
--   $$c_i=\begin{cases}0 & i\in J_1\\ 1 & i\in J_2\end{cases},\qquad K_i=1\ \ (i\in[m]),\qquad d_{ij}=\begin{cases}0 & i\in J_1,\ j\in J_2\\ \infty&\text{otherwise,}\end{cases}$$
--   and the uncertainty set is the budget of uncertainty set
--   $$\mathcal U=\Big\{h\in[0,1]^m\ \Big|\ \sum_{i=1}^m h_i\le m/2\Big\}.$$
--   The arcs of finite distance are the $k^2$ pairs $(i,j)$ with $i\in J_1$, $j\in J_2$; along them inventory moves from $J_1$ to $J_2$ at zero cost.
--
--   **The affine solution of App. D, p. 37.** For $k\ge 1$ write $m$ for the last node of $J_2$. The solution is
--   $$x_i=1\ (i\ne m),\quad x_m=0,\qquad y_{ij}(h)=0\ (i\in J_1,\ j\in J_2\setminus\{m\}),\quad y_{im}(h)=1-h_i\ (i\in J_1),$$
--   that is, $y(h)=Ph+q$ where the row of $P$ for arc $(i,m)$ is $-e_i$, all other rows are $0$, $q_{im}=1$ and all other entries of $q$ are $0$.
--
--   This family is the paper's witness that affine policies can be arbitrarily worse than fully adjustable ones once the recourse matrix has negative entries.
--
--   **Formalization Note** The paper's "$m$ is even" is written $m=2k$. Nodes are `Fin k ⊕ Fin k`: `Sum.inl i` is the $(i+1)$-st node of $J_1$ and `Sum.inr j` the $(j+1)$-st node of $J_2$ (0-based indices); arcs are `Fin k × Fin k`, the pair $(i,j)$ going from `Sum.inl i` to `Sum.inr j`. The distances $d_{ij}=\infty$ are encoded by omitting those arcs (see the definition of the lot-sizing problem); the kept arcs carry $d=0$. The affine solution is defined for $k=n+1$, and the paper's node $m$ is the last $J_2$ node `Sum.inr (Fin.last n)`.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, eq. (7.2), p. 28; App. D, affine solution, p. 37

import Mathlib
import Definitions.Def_BudgetedAffine_NetworkGap_LotSizing

namespace BudgetedAffine.NetworkGap

/-- Nodes of the bipartite network with `m = 2k` nodes: `Sum.inl i` is the `i`-th node of
`J₁`, `Sum.inr j` the `j`-th node of `J₂` (`|J₁| = |J₂| = k = m/2`). -/
abbrev Node (k : ℕ) := Fin k ⊕ Fin k

/-- Arcs of finite distance: `(i, j)` goes from the `J₁`-node `i` to the `J₂`-node `j`. -/
abbrev Arc (k : ℕ) := Fin k × Fin k

/-- The uncertainty set of (7.2): `{h ∈ [0,1]^m | ∑_i h_i ≤ m/2}` with `m/2 = k`. -/
def budgetSet (k : ℕ) : Set (Node k → ℝ) :=
  {h | (∀ v, 0 ≤ h v ∧ h v ≤ 1) ∧ ∑ v, h v ≤ (k : ℝ)}

/-- The family of instances (7.2) of the lot-sizing problem (7.1): `c_i = 0` on `J₁`,
`c_i = 1` on `J₂`, `K_i = 1`, `d_ij = 0` for `i ∈ J₁, j ∈ J₂` (the only arcs kept; every other
distance is `∞`), and `U = budgetSet k`. -/
def lotSizingFamily (k : ℕ) : LotSizing (Node k) (Arc k) where
  src a := Sum.inl a.1
  tgt a := Sum.inr a.2
  c := Sum.elim (fun _ => 0) (fun _ => 1)
  K := fun _ => 1
  d := fun _ => 0
  U := budgetSet k

/-- First stage of the affine solution of App. D, p. 37, for `k = n + 1`: `x_i = 1` at every
node except the last `J₂` node `Fin.last n` (the paper's node `m`), where `x_m = 0`. -/
def ubX (n : ℕ) : Node (n + 1) → ℝ :=
  Sum.elim (fun _ => 1) (fun j => if j = Fin.last n then 0 else 1)

/-- Linear part of the affine solution of App. D, p. 37: the row of arc `(i, m)` is `−e_i`
(the `J₁`-node `i`), every other entry is `0`. -/
def ubP (n : ℕ) : Matrix (Arc (n + 1)) (Node (n + 1)) ℝ :=
  fun a v => if a.2 = Fin.last n ∧ v = Sum.inl a.1 then -1 else 0

/-- Constant part of the affine solution of App. D, p. 37: `q_{im} = 1`, every other entry
`0`; together with `ubP`, `y_{im}(h) = 1 − h_i` and `y_{ij}(h) = 0` for `j ≠ m`. -/
def ubQ (n : ℕ) : Arc (n + 1) → ℝ :=
  fun a => if a.2 = Fin.last n then 1 else 0

end BudgetedAffine.NetworkGap


