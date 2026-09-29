-- Prove2me | Definitions.Def_ApproxMWM_Scaling_Params
-- name    : ApproxMWM_Scaling_Params
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:05:36.347282+00:00
-- url     : https://prove2.me/theorems/19ad158d-be05-4548-81a6-113f52541c4d
-- title:
--   Scales, granularities $\delta_i$, truncated weights $w_i$ and $\mathrm{scale}(e)$
-- statement:
--   The scaling algorithm is parametrized by a weight bound $N=2^L\ge1$ and an accuracy $\epsilon'=2^{-g}$ with $g\ge2$ (so $\epsilon'\le1/4$ is a power of two). There are $L+1$ scales $i=0,\dots,L$ with $L=\log N$. For a weight function $w:E\to\{1,\dots,N\}$ define
--
--   1. the granularity $\delta_i=\delta_0/2^i$ with $\delta_0=\epsilon'N$;
--   2. the truncated weight $w_i(e)=\delta_i\lfloor w(e)/\delta_i\rfloor$;
--   3. the thresholds $\mu_i=N/2^{i+1}+\delta_i$ for $i<L$ and $\mu_L=0$ (Definition 3.9);
--   4. $\mathrm{scale}(e)$, the index $i$ with $w(e)\in[\mu_i,\mu_{i-1})$ (Definition 3.9), with the convention $\mu_{-1}=+\infty$;
--   5. the value ending scale $i$: the free vertices' $y$-values are run down to $N/2^{i+2}-\delta_i/2$ if $i<L$ and to $0$ if $i=L$ (Figure 2);
--   6. $\gamma=\log\epsilon'^{-1}=g$ (Definition 3.10).
--
--   These quantities fix the arithmetic of every scale of the algorithm.
--
--   **Formalization Note** $N$ and $\epsilon'$ are given through the exponents $L$ and $g$, so $\log N$ and $\log\epsilon'^{-1}$ are exact. Since $\mu_i=(N/2^i)(1/2+\epsilon')$ decreases in $i$ and $\mu_L=0$, $\mathrm{scale}(e)$ is computed as the least $i$ with $\mu_i\le w(e)$; this agrees with Definition 3.9 under the convention $\mu_{-1}=+\infty$, which the page leaves implicit. Thresholds $\mu_i$ for $i>L$ are also set to $0$ and are never used.
-- source:
--   Duan and Pettie, Linear-Time Approximation for Maximum Weight Matching, J. ACM 61(1), Article 1 (2014), https://doi.org/10.1145/2529989, p. 1:12 (δ_i, w_i, L = log N), p. 1:14 Figure 2 (end-of-scale values), p. 1:17 Definition 3.9, p. 1:18 Definition 3.10 (γ)

import Mathlib

namespace ApproxMWM.Scaling

/-- The parameters of the scaling algorithm (p. 1:12): the weight bound `N = 2^L` (a power of two,
`N ≥ 1`) and `ε' = 2^{-g}` with `g ≥ 2`, i.e. `ε' ≤ 1/4` a power of two. Then `L = log N` and
`γ = log ε'⁻¹ = g` (Definition 3.10). -/
structure Params where
  L : ℕ
  g : ℕ
  two_le_g : 2 ≤ g

namespace Params

variable (P : Params)

/-- `N = 2^L`. -/
def N : ℝ := 2 ^ P.L

/-- `ε' = (1/2)^g`. -/
noncomputable def eps' : ℝ := (1 / 2 : ℝ) ^ P.g

/-- `δ_i = δ_0 / 2^i` with `δ_0 = ε' N` (p. 1:12). -/
noncomputable def δ (i : ℕ) : ℝ := P.eps' * P.N / 2 ^ i

/-- `μ_i = N / 2^{i+1} + δ_i` for `i < L` and `μ_i = 0` for `i ≥ L` (Definition 3.9, p. 1:17). -/
noncomputable def μ (i : ℕ) : ℝ := if i < P.L then P.N / 2 ^ (i + 1) + P.δ i else 0

/-- The value that ends scale `i` (Figure 2): the free vertices' `y`-values are run down to
`N / 2^{i+2} - δ_i / 2` if `i < L`, and to `0` if `i = L`. -/
noncomputable def target (i : ℕ) : ℝ := if i < P.L then P.N / 2 ^ (i + 2) - P.δ i / 2 else 0

end Params

variable {V : Type*}

/-- The truncated weight `w_i(e) = δ_i ⌊w(e) / δ_i⌋` used at scale `i` (p. 1:12). -/
noncomputable def truncW (P : Params) (w : Sym2 V → ℕ) (i : ℕ) (e : Sym2 V) : ℝ :=
  P.δ i * ⌊(w e : ℝ) / P.δ i⌋

/-- `scale(e)` (Definition 3.9, p. 1:17): the `i` with `w(e) ∈ [μ_i, μ_{i-1})`, with the convention
`μ_{-1} = +∞`. Since `μ` is decreasing and `μ_L = 0`, this is the least `i` with `μ_i ≤ w(e)`. -/
noncomputable def scaleOf (P : Params) (w : Sym2 V → ℕ) (e : Sym2 V) : ℕ :=
  @Nat.find (fun i => P.μ i ≤ (w e : ℝ)) (Classical.decPred _)
    ⟨P.L, by simp [Params.μ]⟩

end ApproxMWM.Scaling


