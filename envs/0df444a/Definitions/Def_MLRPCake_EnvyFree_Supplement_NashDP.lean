-- Prove2me | Definitions.Def_MLRPCake_EnvyFree_Supplement_NashDP
-- name    : MLRPCake_EnvyFree_Supplement_NashDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:05:04.857821+00:00
-- url     : https://prove2.me/theorems/208c88a9-1468-48e6-b38f-5011657ec9a4
-- title:
--   §9, pp. 22–23 — value grid c_t and the Nash-product dynamic program
-- statement:
--   For $\varepsilon>0$ the value grid is
--   $$c_0=0,\qquad c_t=\min_i \mathrm{Cut}_i\Big(c_{t-1},\frac{\varepsilon}{8n}\Big),$$
--   so that every cell $[c_{t-1},c_t]$ is worth at most $\varepsilon/(8n)$ to every agent; once $c_t=1$ the grid stays at $1$. The algorithm uses the grid points $c_0,\dots,c_N$ with $N=\lceil 8n^2/\varepsilon\rceil+1$ and runs the dynamic program with products, $H(1,t)=v_1(0,c_t)$, $H(k+1,t)=\max_{0\le s\le t}H(k,s)\,v_{k+1}(c_s,c_t)$, from entry $(n,N)$. Its work is $n$ Cut queries per grid point plus the dynamic-programming operations.
--
--   **Formalization Note** The paper bounds the number of grid points by $8n^2/\varepsilon$; the fixed length $\lceil 8n^2/\varepsilon\rceil+1$ covers that bound with an integer index.
-- source:
--   Barman & Rathi, Fair Cake Division Under Monotone Likelihood Ratios, arXiv:2006.00481v3, pp. 22–23, proof of Theorem 5 (points c_t, dynamic program H(k,t))

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model
import Definitions.Def_MLRPCake_EnvyFree_Supplement_SocialDP

namespace MLRPCake.EnvyFree.Supplement
open MeasureTheory MLRPCake.EnvyFree
open Classical

variable {n : ℕ}

/-! ### Nash social welfare algorithm (§9, pp. 22–23) -/

/-- `min(1, min_{k' < k} Cut_{k'}(ℓ, τ))`. -/
noncomputable def minCut (f : Fin n → ℝ → ℝ) (ℓ τ : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => min (minCut f ℓ τ k) (cut f k ℓ τ)

/-- §9, pp. 22–23: the value grid `c_0 = 0`, `c_t = min_i Cut_i(c_{t-1}, ε/(8n))`. -/
noncomputable def nashGrid (f : Fin n → ℝ → ℝ) (ε : ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => minCut f (nashGrid f ε t) (ε / (8 * n)) n

/-- Last grid index used: `N = ⌈8n²/ε⌉ + 1`. -/
noncomputable def nashLen (n : ℕ) (ε : ℝ) : ℕ := ⌈8 * (n : ℝ) ^ 2 / ε⌉₊ + 1

/-- The allocation returned (agents in MLRP order): the dynamic program with `comb = (·)` on
`c_0, …, c_N`, read off from entry `(n, N)`. -/
noncomputable def nashOutput (f : Fin n → ℝ → ℝ) (ε : ℝ) : ℕ → ℝ :=
  dpCuts f (· * ·) (nashGrid f ε) (nashLen n ε)

/-- Work of the Nash algorithm: `n` Cut queries per grid point and the dynamic-programming
operations on the `N + 1` grid points. -/
noncomputable def nashCost (n : ℕ) (ε : ℝ) : ℕ := n * nashLen n ε + dpQueries n (nashLen n ε + 1)

end MLRPCake.EnvyFree.Supplement


