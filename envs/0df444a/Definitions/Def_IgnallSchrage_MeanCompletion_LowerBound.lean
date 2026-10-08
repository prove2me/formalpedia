-- Prove2me | Definitions.Def_IgnallSchrage_MeanCompletion_LowerBound
-- name    : IgnallSchrage_MeanCompletion_LowerBound
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:31:33.316306+00:00
-- url     : https://prove2.me/theorems/1c9e29aa-a06a-48f8-a20a-3c1be23a56cf
-- title:
--   $T_r$, $S_r$, their minima $\hat T_r$, $\hat S_r$ over orderings of $\bar J_r$, and $LB(J_r)$ (pp. 405–406)
-- statement:
--   Fix a node $J_r$ (a partial sequence of $r$ jobs), let $\bar J_r$ be the set of the $n-r$ jobs not in $J_r$, let $k$ be the last job of $J_r$ and $d_k$ its completion time on machine $B$, and let $d_i$ ($i\in J_r$) be the completion times of the jobs of $J_r$ processed in order as early as possible.
--
--   For an ordering $(i_1,\dots,i_{n-r})$ of $\bar J_r$ define
--   $$
--   T_r=\sum_{p=1}^{n-r}\Big[\sum_{j\in J_r}a_j+(n-r-p+1)\,a_{i_p}+b_{i_p}\Big],
--   $$
--   and for an ordering $(j_1,\dots,j_{n-r})$ of $\bar J_r$ define
--   $$
--   S_r=\sum_{p=1}^{n-r}\Big[\max\Big(d_k,\ \sum_{j\in J_r}a_j+\min_{i\in\bar J_r}a_i\Big)+(n-r-p+1)\,b_{j_p}\Big].
--   $$
--   Let $\hat T_r$ and $\hat S_r$ be the minima of $T_r$ and $S_r$ over all orderings of $\bar J_r$. The **lower bound** of the node is
--   $$
--   LB(J_r)=\sum_{i\in J_r}d_i+\max(\hat T_r,\hat S_r).
--   $$
--
--   $T_r$ is the sum of the completion times of the jobs of $\bar J_r$ when they are processed in the order $i_1,\dots$ and machine $A$ dominates; $S_r$ is a corresponding quantity when machine $B$ dominates. $LB$ is the bound with which the branch-and-bound procedure ranks its nodes.
--
--   **Formalization Note** $\hat T_r$ and $\hat S_r$ are defined as minima over all permutations of the list of the jobs of $\bar J_r$, not by a sorted order; that the sorted orders attain them is a separate statement. Positions are 0-based: with $q=p-1$ and $n-r$ the length of the ordering, the coefficient $n-r-p+1$ is $(n-r)-q$, computed in $\mathbb R$. The value of $\min_{\bar J_r}a_i$ when $\bar J_r=\emptyset$ is a placeholder $0$ (there $S_r$ is an empty sum). $LB$ is intended for $1\le r\le n-1$; at the root, $d_k$ is read as $0$, and the procedure never ranks the root. In the scan the bars over $\bar J_r$ in the subscripts of $\min$ are not visible; the definitions follow the paper's text ("$i_1,\dots,i_{n-r}$ is a permutation of the integers in $\bar J_r$").
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), p. 405, "M=2; A Lower Bound on Mean Completion Time for All Nodes Emanating from a Given Node", definitions of T_r and S_r; p. 406, T̂_r, Ŝ_r and LB(J_r)

import Mathlib
import Definitions.Def_IgnallSchrage_MeanCompletion_Node

namespace IgnallSchrage.MeanCompletion

/-- The jobs of `J̄` (those not in the node `J`), listed in increasing index. -/
def unscheduledList {n : ℕ} (J : List (Fin n)) : List (Fin n) :=
  (List.finRange n).filter (fun j => decide (j ∉ J))

/-- The orderings `(i_1, …, i_{n-r})` of `J̄_r`: all permutations of the list of the jobs not
in `J`. -/
def orderings {n : ℕ} (J : List (Fin n)) : Finset (List (Fin n)) :=
  (unscheduledList J).permutations.toFinset

lemma orderings_nonempty {n : ℕ} (J : List (Fin n)) : (orderings J).Nonempty :=
  ⟨unscheduledList J, List.mem_toFinset.mpr (List.mem_permutations.mpr (List.Perm.refl _))⟩

/-- `min_{i ∈ J̄} a_i`, the least machine-A time of an IgnallSchrage.Makespan.unscheduled job. Its value `0` when
`J̄ = ∅` is a placeholder: there `S_r` is an empty sum and does not use it. -/
def minUnscheduledA {n : ℕ} (a : Fin n → ℝ) (J : List (Fin n)) : ℝ :=
  if h : (IgnallSchrage.Makespan.unscheduled J).Nonempty then (IgnallSchrage.Makespan.unscheduled J).inf' h a else 0

/-- `T_r` of p. 405 for the node `J = J_r` and an ordering `l = (i_1, …, i_{n-r})` of `J̄_r`:
`T_r = Σ_{p=1}^{n-r} [Σ_{j ∈ J_r} a_j + (n - r - p + 1) a_{i_p} + b_{i_p}]`.
With the 0-based position `q = p - 1` of `l` and `l.length = n - r`, the coefficient
`n - r - p + 1` is `l.length - q`. -/
def Tval {n : ℕ} (a b : Fin n → ℝ) (J : List (Fin n)) (l : List (Fin n)) : ℝ :=
  ∑ q : Fin l.length,
    ((J.map a).sum + ((l.length : ℝ) - (q : ℝ)) * a l[q] + b l[q])

/-- `S_r` of p. 405 for the node `J = J_r`, with last job `k`, and an ordering
`l = (j_1, …, j_{n-r})` of `J̄_r`:
`S_r = Σ_{p=1}^{n-r} [max(d_k, Σ_{j ∈ J_r} a_j + min_{i ∈ J̄_r} a_i) + (n - r - p + 1) b_{j_p}]`.
The coefficient is `l.length - q` for the 0-based position `q = p - 1`. -/
def Sval {n : ℕ} (a b : Fin n → ℝ) (J : List (Fin n)) (l : List (Fin n)) : ℝ :=
  ∑ q : Fin l.length,
    (max (lastCompletion a b J) ((J.map a).sum + minUnscheduledA a J)
      + ((l.length : ℝ) - (q : ℝ)) * b l[q])

/-- `T̂_r` (p. 406): the minimum of `T_r` over all orderings of `J̄_r`. -/
def That {n : ℕ} (a b : Fin n → ℝ) (J : List (Fin n)) : ℝ :=
  (orderings J).inf' (orderings_nonempty J) (Tval a b J)

/-- `Ŝ_r` (p. 406): the minimum of `S_r` over all orderings of `J̄_r`. -/
def Shat {n : ℕ} (a b : Fin n → ℝ) (J : List (Fin n)) : ℝ :=
  (orderings J).inf' (orderings_nonempty J) (Sval a b J)

/-- The lower bound of p. 406 of a node `J = J_r`:
`LB(J_r) = Σ_{i ∈ J_r} d_i + max(T̂_r, Ŝ_r)`.
It is meant for `1 ≤ r ≤ n - 1`; at the root (`r = 0`, no last job `k`) `d_k` is read as `0`,
and the procedure never ranks the root, so that value is never used. -/
def lowerBound {n : ℕ} (a b : Fin n → ℝ) (J : List (Fin n)) : ℝ :=
  nodeCompletionSum a b J + max (That a b J) (Shat a b J)

end IgnallSchrage.MeanCompletion


