-- Prove2me | Definitions.Def_CritContracts_SSParams
-- name    : CritContracts_SSParams
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:43:35.090399+00:00
-- url     : https://prove2.me/theorems/1e7c7db3-28cb-411c-85fa-ad3ead3dc667
-- title:
--   The parameters $W$, $L$, $\Delta$, $\varepsilon$, the ternary mass $Q(\sigma)$ and the encoder intervals $I_\sigma$
-- statement:
--   For a Subset Sum instance with positive integer weights $w_1,\dots,w_k$ and target $T$, the reduction of Appendix B.1.1 uses
--   $$W=\sum_{i=1}^k w_i,\qquad L=3^{-k},\qquad \Delta=\frac{3^{-3k}}{10^{20}\,k\,W^4},\qquad \varepsilon=\frac{\Delta L}{8},$$
--   and it assumes without loss of generality that $k\ge1$ and $1\le T\le W-1$. For $\sigma\in\{0,1\}^k$ the **ternary mass** and the **encoder interval** are
--   $$Q(\sigma)=\sum_{i:\sigma_i=1}2\cdot3^{-i},\qquad I_\sigma=\Bigl[\tfrac12+\Delta Q(\sigma)+\tfrac{\Delta L}{4},\ \tfrac12+\Delta Q(\sigma)+\tfrac{3\Delta L}{4}\Bigr].$$
--   The module also defines the payment vector $\lambda=(x,1-x)$ on the line $\lambda_1+\lambda_2=1$.
--
--   **Formalization Note** The parameters are rationals. Items are $0,\dots,k-1$ in Lean and $1,\dots,k$ in the paper, so the paper's $3^{-i}$ is `tern i` $=3^{-(i+1)}$ and $Q(\sigma)=\sum_{\sigma_i}2\cdot3^{-(i+1)}$; for $k=3$ this gives $Q(011)=8/27$ and $Q(100)=2/3$ as in Figure 7. `SSRange ws T` is the WLOG condition together with the positivity of the weights.
-- source:
--   Ezra–Feldman–Molina–Schlesinger, Sources of Complexity in Multi-Agent Combinatorial Contracts, STOC 2027 submission (manuscript sha256 430be35c86352b23f05ee0e9126d1318096922c9cbe07d419ee38e38bfcba346), Appendix B.1.1, p.33 (PDF p.34): W, L, Δ, ε and the WLOG k ≥ 1, 1 ≤ T ≤ W − 1; p.35 (PDF p.36): Q(σ) and I_σ

import Mathlib

set_option autoImplicit false

namespace CritContracts

/-- The **parameters of the reduction** of Appendix B.1.1 (Ezra–Feldman–Molina–Schlesinger, *Sources of Complexity
in Multi-Agent Combinatorial Contracts*, STOC 2027 submission (manuscript sha256 430be35c…), p.33, PDF p.34), for a
Subset Sum instance with weights `ws = [w₁, …, w_k]`: the total weight `W = Σ wᵢ`, `L = 3^{−k}`,
`Δ = 3^{−3k}/(10^{20} k W⁴)` and `ε = ΔL/8`. This declaration is `Δ`. -/
def Delta (ws : List ℕ) : ℚ :=
  (1 / 3 : ℚ) ^ (3 * ws.length) / (10 ^ 20 * (ws.length : ℚ) * (ws.sum : ℚ) ^ 4)

/-- `W = Σᵢ wᵢ` (p.33). -/
def totalW (ws : List ℕ) : ℚ := (ws.sum : ℚ)

/-- `L = 3^{−k}` (p.33). -/
def Lpar (ws : List ℕ) : ℚ := (1 / 3 : ℚ) ^ ws.length

/-- `ε = ΔL/8` (p.33). -/
def epsPar (ws : List ℕ) : ℚ := Delta ws * Lpar ws / 8

/-- `3^{−(i+1)}`: the paper's `3^{−i}` for the item written `i` here (0-based) and `i + 1` in the paper. -/
def tern (i : ℕ) : ℚ := (1 / 3 : ℚ) ^ (i + 1)

/-- The paper's assumption "without loss of generality `k ≥ 1` and `1 ≤ T ≤ W − 1`" for a Subset Sum instance
with positive integer weights (p.33). -/
def SSRange (ws : List ℕ) (T : ℕ) : Prop :=
  1 ≤ ws.length ∧ (∀ w ∈ ws, 0 < w) ∧ 1 ≤ T ∧ T + 1 ≤ ws.sum

/-- The **ternary mass** `Q(σ) = Σ_{i : σᵢ = 1} 2·3^{−i}` of `σ ∈ {0,1}^k` (p.35). -/
def Qmass {k : ℕ} (σ : Fin k → Bool) : ℚ := ∑ i : Fin k, if σ i then 2 * tern i else 0

/-- The **encoder interval** `I_σ = [½ + ΔQ(σ) + ΔL/4, ½ + ΔQ(σ) + 3ΔL/4]` (p.35). -/
def encInterval (ws : List ℕ) (σ : Fin ws.length → Bool) : Set ℝ :=
  Set.Icc ((1 / 2 + Delta ws * Qmass σ + Delta ws * Lpar ws / 4 : ℚ) : ℝ)
    ((1 / 2 + Delta ws * Qmass σ + 3 * Delta ws * Lpar ws / 4 : ℚ) : ℝ)

/-- The payment vector `λ = (x, 1 − x)` on the line `λ₁ + λ₂ = 1` (pp.35–36). -/
def linePay (x : ℝ) : Fin 2 → ℝ := ![x, 1 - x]

end CritContracts


