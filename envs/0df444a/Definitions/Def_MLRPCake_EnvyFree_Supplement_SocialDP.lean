-- Prove2me | Definitions.Def_MLRPCake_EnvyFree_Supplement_SocialDP
-- name    : MLRPCake_EnvyFree_Supplement_SocialDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:03:20.62074+00:00
-- url     : https://prove2.me/theorems/2e1f95da-bbde-46f9-b531-1d0dfaf9ca23
-- title:
--   §7, pp. 19–20 — dynamic program over an ordered grid and the social-welfare algorithm
-- statement:
--   **Dynamic program.** Given grid points $0=g_0\le g_1\le\dots$ and a combination rule $\oplus$, the table
--   $$D(1,t)=v_1(g_0,g_t),\qquad D(k+1,t)=\max_{0\le s\le t}\ D(k,s)\oplus v_{k+1}(g_s,g_t)$$
--   is the best value of allocating $[0,g_t]$ to the first $k$ agents in MLRP order with cuts on the grid. The predecessor index is the first maximizer; backtracking from $(n,T)$ yields cut points, agent $k$ receiving $[x_{k-1},x_k]$. With $\oplus=+$ this is $M(k,t)$ of §7; with $\oplus=\times$ it is $H(k,t)$ of §9. Predecessor index $0$ is allowed so that agents may receive empty pieces. The memoized program makes $G+(n-1)\,G(G+1)/2$ Eval queries on a grid of $G$ points.
--
--   **Social-welfare algorithm.** For $\eta>0$ and Lipschitz constant $\lambda$, each switching point $p_{ij}$, $i<j$, is localized with precision $\gamma=\eta/(n\lambda)$, and $\hat p_{ij}$ is the left endpoint of the returned interval. The grid $\hat P=\{\hat p_{ij}\}\cup\{0,1\}$ is sorted increasingly and the program with $\oplus=+$ is run from entry $(n,|\hat P|-1)$. Its work is the localization queries for the $n(n-1)/2$ pairs plus the dynamic-programming operations.
--
--   **Formalization Note** The work is counted as Robertson–Webb queries and table operations of the memoized program.
-- source:
--   Barman & Rathi, Fair Cake Division Under Monotone Likelihood Ratios, arXiv:2006.00481v3, pp. 19–20, proof of Theorem 3 (estimates p̂_ij, set P̂, dynamic program M(k,t))

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model
import Definitions.Def_MLRPCake_EnvyFree_Supplement_SwitchPoints

namespace MLRPCake.EnvyFree.Supplement
open MeasureTheory MLRPCake.EnvyFree
open Classical

variable {n : ℕ}

/-! ### Dynamic programs over an ordered grid (§7, p. 20 and §9, p. 23) -/

/-- The first index `s ∈ {0, …, t}` maximizing `h s`. -/
noncomputable def argmaxUpTo (h : ℕ → ℝ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => if h (argmaxUpTo h t) < h (t + 1) then t + 1 else argmaxUpTo h t

/-- Candidate value of predecessor index `s` when agent `k` (0-based) receives
`[g s, g t]`: `comb(prev s, Eval_k(g s, g t))`. -/
noncomputable def dpCand (f : Fin n → ℝ → ℝ) (comb : ℝ → ℝ → ℝ) (g : ℕ → ℝ) (prev : ℕ → ℝ)
    (k t s : ℕ) : ℝ :=
  comb (prev s) (eval f k (g s) (g t))

/-- The dynamic-programming table on the grid `g 0 = 0 ≤ g 1 ≤ …`: `dpVal f comb g k t` is the
best value of allocating `[0, g t]` among the first `k` agents in order, with cuts on the grid:
`dpVal 1 t = Eval_0(g 0, g t)` and
`dpVal (k+1) t = max_{0 ≤ s ≤ t} comb(dpVal k s, Eval_k(g s, g t))`.
With `comb = (+)` this is `M(k,t)` of §7, with `comb = (·)` it is `H(k,t)` of §9. -/
noncomputable def dpVal (f : Fin n → ℝ → ℝ) (comb : ℝ → ℝ → ℝ) (g : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | 1, t => eval f 0 (g 0) (g t)
  | k + 2, t =>
    dpCand f comb g (dpVal f comb g (k + 1)) (k + 1) t
      (argmaxUpTo (dpCand f comb g (dpVal f comb g (k + 1)) (k + 1) t) t)

/-- The predecessor index chosen by the dynamic program at entry `(k, t)` (`0` for `k ≤ 1`). -/
noncomputable def dpPred (f : Fin n → ℝ → ℝ) (comb : ℝ → ℝ → ℝ) (g : ℕ → ℝ) : ℕ → ℕ → ℕ
  | k + 2, t => argmaxUpTo (dpCand f comb g (dpVal f comb g (k + 1)) (k + 1) t) t
  | _, _ => 0

/-- Backtracking from entry `(n, T)`: `dpBack m` is the grid index of cut point `n - m`. -/
noncomputable def dpBack (f : Fin n → ℝ → ℝ) (comb : ℝ → ℝ → ℝ) (g : ℕ → ℝ) (T : ℕ) : ℕ → ℕ
  | 0 => T
  | m + 1 => dpPred f comb g (n - m) (dpBack f comb g T m)

/-- The cut points output by the dynamic program from entry `(n, T)`: cut point `k` is
`g (dpBack (n - k))`; agent `k` (0-based) receives `[x k, x (k+1)]`. -/
noncomputable def dpCuts (f : Fin n → ℝ → ℝ) (comb : ℝ → ℝ → ℝ) (g : ℕ → ℝ) (T : ℕ) : ℕ → ℝ :=
  fun k => g (dpBack f comb g T (n - k))

/-- Operations of the memoized dynamic program on a grid of `G` points with `n` agents:
`G` Eval queries for the first row, and for each of the other `n - 1` rows and each `t < G`,
`t + 1` candidates (one Eval query each). -/
def dpQueries (n G : ℕ) : ℕ := G + (n - 1) * (G * (G + 1) / 2)

/-! ### Social welfare algorithm (proof of Theorem 3, pp. 19–20) -/

/-- The pairs `(i, j)` of agents with `i < j < n`. -/
def pairs (n : ℕ) : Finset (ℕ × ℕ) := (Finset.range n ×ˢ Finset.range n).filter (fun p => p.1 < p.2)

/-- The localization precision `η/(nλ)` used for every switching point. -/
noncomputable def swGamma (n : ℕ) (lam η : ℝ) : ℝ := η / (n * lam)

/-- `P̂ = {p̂_{ij} : i < j} ∪ {0, 1}`, where `p̂_{ij}` is the left endpoint of the interval of
length at most `η/(nλ)` returned by the localization of `p_{ij}`. -/
noncomputable def swGridSet (f : Fin n → ℝ → ℝ) (lam η : ℝ) : Finset ℝ :=
  insert 0 (insert 1 ((pairs n).image (fun p => locLeft f p.1 p.2 (swGamma n lam η))))

/-- `P̂` sorted increasingly: `p̂_0 < p̂_1 < … < p̂_{|P̂|-1}`. -/
noncomputable def swGrid (f : Fin n → ℝ → ℝ) (lam η : ℝ) : List ℝ :=
  (swGridSet f lam η).sort (· ≤ ·)

/-- The `t`-th point of the sorted grid `P̂`. -/
noncomputable def swPoint (f : Fin n → ℝ → ℝ) (lam η : ℝ) (t : ℕ) : ℝ :=
  (swGrid f lam η).getD t 1

/-- The allocation returned by the social-welfare algorithm (cut points, agents in MLRP order):
the dynamic program with `comb = (+)` on `P̂`, read off from entry `(n, |P̂| - 1)`. -/
noncomputable def swOutput (f : Fin n → ℝ → ℝ) (lam η : ℝ) : ℕ → ℝ :=
  dpCuts f (· + ·) (swPoint f lam η) ((swGrid f lam η).length - 1)

/-- Work of the social-welfare algorithm: the localization queries for the `n(n-1)/2`
switching points plus the dynamic-programming operations on `P̂`. -/
noncomputable def swCost (f : Fin n → ℝ → ℝ) (lam η : ℝ) : ℕ :=
  (pairs n).card * locQueries (swGamma n lam η) + dpQueries n (swGrid f lam η).length

end MLRPCake.EnvyFree.Supplement


