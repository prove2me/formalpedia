-- Prove2me | Definitions.Def_MLRPCake_EnvyFree_Supplement_SwitchPoints
-- name    : MLRPCake_EnvyFree_Supplement_SwitchPoints
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:02:21.243798+00:00
-- url     : https://prove2.me/theorems/54f4c08d-7b56-4cb7-96b4-4ae1d711e775
-- title:
--   §7, pp. 18–19 — switching points p_ij, the set P, and the binary search localizing a switching point
-- statement:
--   For two value densities $f_i, f_j$ let $L_{ij}=\{x\in[0,1] : f_j(x)\ge f_i(x)\}$. The **switching point** is
--   $$p_{ij}=\inf L_{ij},$$
--   and for an instance with agents in MLRP order $P=\{p_{ij} : i<j\}\cup\{0,1\}$.
--
--   The localization procedure of Corollary 1 works with the dyadic mesh $h=2^{-K}$ and cells $B_k=[(k-1)h,kh]$, $k\ge1$. A cell test compares $v_i(B_k)$ and $v_j(B_k)$ with two Eval queries. A binary search over the indices $\{0,\dots,2^K\}$ starts from $(lo,hi)=(0,2^K)$ and, while $hi>lo+1$, tests the cell $m=\lfloor (lo+hi)/2\rfloor$, setting $hi:=m$ if $v_i(B_m)\le v_j(B_m)$ and $lo:=m$ otherwise. For precision $\gamma$ it runs $K=\lceil\log_2(2/\gamma)\rceil$ iterations and returns the interval $[\max(0,(lo-1)h),\ hi\cdot h]$; it makes $2K$ Eval queries.
--
--   **Formalization Note** The switching point is a real infimum; for normalized densities the set $L_{ij}$ is nonempty and bounded below, so the infimum is the paper's. The dyadic mesh replaces the paper's cells of width $\gamma/2$, which presuppose that $2/\gamma$ is an integer.
-- source:
--   Barman & Rathi, Fair Cake Division Under Monotone Likelihood Ratios, arXiv:2006.00481v3, pp. 18–19, §7 (definition of L_ij, p_ij and P) and proof of Corollary 1

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model

namespace MLRPCake.EnvyFree.Supplement
open MeasureTheory MLRPCake.EnvyFree
open Classical

variable {n : ℕ}

/-! ### Switching points (§7, p. 18) -/

/-- §7, p. 18: the switching point `p_{ij} = inf L_{ij}` of two densities, where
`L_{ij} = {x ∈ [0,1] : f_j(x) ≥ f_i(x)}`. -/
noncomputable def switchPt (fi fj : ℝ → ℝ) : ℝ :=
  sInf {x | x ∈ Set.Icc (0:ℝ) 1 ∧ fi x ≤ fj x}

/-- §7, p. 18: `P = {p_{ij} : 1 ≤ i < j ≤ n} ∪ {0, 1}` (agents 0-based here). -/
def switchSet (f : Fin n → ℝ → ℝ) : Set ℝ :=
  {p | ∃ i j : Fin n, i < j ∧ p = switchPt (f i) (f j)} ∪ {0, 1}

/-! ### Localization of a switching point (proof of Corollary 1, pp. 18–19) -/

/-- The cell test of the binary search: with mesh `2^{-K}`, cell `k ≥ 1` is
`B_k = [(k-1)/2^K, k/2^K]`, and the test, answered by two Eval queries, is
`v_i(B_k) ≤ v_j(B_k)`. -/
def cellTest (f : Fin n → ℝ → ℝ) (i j K k : ℕ) : Prop :=
  eval f i (((k:ℝ) - 1) / 2 ^ K) ((k:ℝ) / 2 ^ K) ≤ eval f j (((k:ℝ) - 1) / 2 ^ K) ((k:ℝ) / 2 ^ K)

/-- Binary search over the cell indices `{0, …, 2^K}`: the pair `(lo, hi)` after `s` iterations.
Each iteration that has `hi > lo + 1` performs one cell test at `m = ⌊(lo + hi)/2⌋` and keeps
`hi := m` if the test succeeds, `lo := m` otherwise. -/
noncomputable def locIter (f : Fin n → ℝ → ℝ) (i j K : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 2 ^ K)
  | s + 1 =>
    let p := locIter f i j K s
    if p.2 ≤ p.1 + 1 then p
    else if cellTest f i j K ((p.1 + p.2) / 2) then (p.1, (p.1 + p.2) / 2)
    else ((p.1 + p.2) / 2, p.2)

/-- Number of iterations (and the mesh exponent) used for precision `γ`:
`K = ⌈log₂(2/γ)⌉`, so that the mesh `2^{-K}` is at most `γ/2`. -/
noncomputable def locSteps (γ : ℝ) : ℕ := ⌈Real.logb 2 (2 / γ)⌉₊

/-- Left endpoint `max(0, (lo - 1)·2^{-K})` of the interval returned for precision `γ`. -/
noncomputable def locLeft (f : Fin n → ℝ → ℝ) (i j : ℕ) (γ : ℝ) : ℝ :=
  max 0 ((((locIter f i j (locSteps γ) (locSteps γ)).1 : ℝ) - 1) / 2 ^ locSteps γ)

/-- Right endpoint `hi·2^{-K}` of the interval returned for precision `γ`. -/
noncomputable def locRight (f : Fin n → ℝ → ℝ) (i j : ℕ) (γ : ℝ) : ℝ :=
  ((locIter f i j (locSteps γ) (locSteps γ)).2 : ℝ) / 2 ^ locSteps γ

/-- Robertson–Webb queries made by the localization: two Eval queries per iteration. -/
noncomputable def locQueries (γ : ℝ) : ℕ := 2 * locSteps γ

end MLRPCake.EnvyFree.Supplement


