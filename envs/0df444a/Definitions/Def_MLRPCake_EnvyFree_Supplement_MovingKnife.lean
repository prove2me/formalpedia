-- Prove2me | Definitions.Def_MLRPCake_EnvyFree_Supplement_MovingKnife
-- name    : MLRPCake_EnvyFree_Supplement_MovingKnife
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:04:31.739059+00:00
-- url     : https://prove2.me/theorems/2156c7b7-498c-4a25-96db-035ea9c59f35
-- title:
--   §8, pp. 21–22 — moving-knife functions MK_i, feasibility, and the egalitarian binary search
-- statement:
--   **Moving knife.** $\mathrm{MK}_0(\tau)=0$ and $\mathrm{MK}_i(\tau)=\mathrm{Cut}_i(\mathrm{MK}_{i-1}(\tau),\tau)$: agents $1,\dots,n$ in MLRP order successively cut a piece they value at $\tau$ (or the rest of the cake, if their value of it is less than $\tau$).
--
--   **Feasibility.** A target $\tau$ is feasible if $v_i(\mathrm{MK}_{i-1}(\tau),\mathrm{MK}_i(\tau))=\tau$ for every agent $i$.
--
--   **Egalitarian algorithm.** For $\eta>0$ let $m=\lceil 1/\eta\rceil$. A binary search over target indices starts from $(lo,hi)=(0,m+1)$ and, while $hi>lo+1$, tests feasibility of $\lfloor(lo+hi)/2\rfloor/m$ ($n$ Cut and $n$ Eval queries), keeping $lo:=mid$ if feasible and $hi:=mid$ otherwise. After $\lceil\log_2(m+1)\rceil$ iterations it outputs the moving-knife cut points at $\tau=lo/m$, with the leftover piece $[\mathrm{MK}_n(\tau),1]$ added to the last agent's interval. It makes $2n\lceil\log_2(m+1)\rceil+n$ queries.
--
--   **Formalization Note** The grid $\{k/m\}$ has mesh at most $\eta$ for every real $\eta>0$; the paper's grid $\{k\eta\}_{k=0}^{1/\eta}$ presupposes $1/\eta\in\mathbb N$. The upper sentinel $(m+1)/m>1$ is never tested; the paper's assertion that $\tau=1$ is infeasible fails for $n=1$.
-- source:
--   Barman & Rathi, Fair Cake Division Under Monotone Likelihood Ratios, arXiv:2006.00481v3, pp. 21–22, §8 (recursion MK_i, feasibility of τ, binary search, proof of Theorem 4)

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model

namespace MLRPCake.EnvyFree.Supplement
open MeasureTheory MLRPCake.EnvyFree
open Classical

variable {n : ℕ}

/-! ### Moving knife and egalitarian welfare algorithm (§8, pp. 21–22) -/

/-- §8, p. 21: the moving-knife functions `MK_0(τ) = 0`, `MK_{i+1}(τ) = Cut_{i}(MK_i(τ), τ)`
(agent `i` 0-based, so `mk f i` is the paper's `MK_i`). -/
noncomputable def mk (f : Fin n → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | i + 1, τ => cut f i (mk f i τ) τ

/-- §8, p. 21: the target `τ` is feasible iff every agent receives value exactly `τ` from the
moving-knife procedure: `v_i(MK_{i-1}(τ), MK_i(τ)) = τ` for all agents. -/
def ewFeasible (f : Fin n → ℝ → ℝ) (τ : ℝ) : Prop :=
  ∀ i < n, eval f i (mk f i τ) (mk f (i + 1) τ) = τ

/-- The mesh denominator `m = ⌈1/η⌉`; the candidate targets are `k/m`, a grid of mesh at most `η`. -/
noncomputable def ewMesh (η : ℝ) : ℕ := ⌈1 / η⌉₊

/-- Binary search for the largest feasible index `k ∈ {0, …, m}`: the pair `(lo, hi)` after `s`
iterations, starting from `(0, m + 1)`. Each iteration with `hi > lo + 1` tests feasibility of
`⌊(lo + hi)/2⌋ / m` (`n` Cut and `n` Eval queries) and keeps `lo := mid` if it is feasible,
`hi := mid` otherwise. -/
noncomputable def ewIter (f : Fin n → ℝ → ℝ) (η : ℝ) : ℕ → ℕ × ℕ
  | 0 => (0, ewMesh η + 1)
  | s + 1 =>
    let p := ewIter f η s
    if p.2 ≤ p.1 + 1 then p
    else if ewFeasible f (((p.1 + p.2) / 2 : ℕ) / (ewMesh η : ℝ)) then ((p.1 + p.2) / 2, p.2)
    else (p.1, (p.1 + p.2) / 2)

/-- Number of binary-search iterations: `⌈log₂(m + 1)⌉`. -/
noncomputable def ewSteps (η : ℝ) : ℕ := Nat.clog 2 (ewMesh η + 1)

/-- The target `k₀/m` found by the binary search. -/
noncomputable def ewTarget (f : Fin n → ℝ → ℝ) (η : ℝ) : ℝ :=
  ((ewIter f η (ewSteps η)).1 : ℝ) / ewMesh η

/-- The allocation returned (agents in MLRP order): the moving-knife cut points at the found
target, with the leftover piece `[MK_n, 1]` given to the last agent (cut point `n` set to `1`). -/
noncomputable def ewOutput (f : Fin n → ℝ → ℝ) (η : ℝ) : ℕ → ℝ :=
  coalesce n (fun k => mk f k (ewTarget f η))

/-- Robertson–Webb queries of the egalitarian algorithm: `n` Cut and `n` Eval queries per
binary-search iteration and `n` Cut queries for the output. -/
noncomputable def ewCost (n : ℕ) (η : ℝ) : ℕ := ewSteps η * (2 * n) + n

end MLRPCake.EnvyFree.Supplement


