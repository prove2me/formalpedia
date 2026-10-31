-- Prove2me | Definitions.Def_CompetitionComplexity_Gamma
-- name    : CompetitionComplexity_Gamma
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:28:35.50786+00:00
-- url     : https://prove2.me/theorems/e4e09425-7f4c-4c09-9cb8-2e3de9f17b64
-- title:
--   The convex function $\Gamma^\varepsilon_{n,m}$ on the open orthant and the vector $Y$ of (10)
-- statement:
--   Fix $\varepsilon>0$ and integers $n\ge2$, $m\ge3$. On the open orthant $\mathbb R^{m-1}_+=\{x=(x_1,\dots,x_{m-1}): x_i>0\ \text{for all } i\}$ define
--   $$
--   \Gamma^\varepsilon_{n,m}(x)=\varepsilon+x_1^n+\sum_{i=1}^{m-2}x_i\Bigl(\varepsilon+\Bigl(\frac{x_{i+1}}{x_i}\Bigr)^n\Bigr)-x_{m-1}(n-1-\varepsilon).
--   $$
--   With $\rho_{\varepsilon,j}$ the recursion (9), let
--   $$
--   Y_j=\prod_{k=0}^{j-1}\rho_{\varepsilon,m-k}\qquad(j\ge0), \tag{10}
--   $$
--   so that $Y_0=1$, $Y_1=\rho_{\varepsilon,m}$, $Y_2=\rho_{\varepsilon,m}\rho_{\varepsilon,m-1}$, and $Y_m=\rho_{\varepsilon,m}\cdots\rho_{\varepsilon,1}$. The vector $Y=(Y_1,\dots,Y_{m-1})$ is the unique minimizer of $\Gamma^\varepsilon_{n,m}$ (Proposition 2). The function $\Gamma^\varepsilon_{n,m}$ is the objective (1) restricted to the first $m$ coordinates of $\delta$ after the tail has been optimized out.
--
--   **Formalization Note** The orthant is open: $\Gamma$ divides by $x_i$, and Lean's $x/0=0$ would silently change it on the boundary. A point of $\mathbb R^{m-1}$ is a function on `Fin (m-1)`, whose coordinate $i$ is the paper's $x_{i+1}$; the formula is written with the paper's 1-based indices. Display (10) lists $j\in\{1,\dots,m-1\}$; the same product at $j=m$ is the $Y_m$ that Proposition 3 uses (its proof uses $Y_m/Y_{m-1}=\rho_{\varepsilon,1}=1$).
-- source:
--   Brustle, Correa, Dütting, Verdugo, The Competition Complexity of Dynamic Pricing, accepted manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), doi:10.1287/moor.2022.0230, §5, definition of Γ^ε_{n,m}, p.15; display (10), p.15; Y_m in Proposition 3, p.17

import Mathlib
import Definitions.Def_CompetitionComplexity_Recursion

namespace CompetitionComplexity

/-- **The positive orthant `ℝ^{m−1}_+`** of §5, p.15: vectors `(x₁, …, x_{m−1})` with every
coordinate strictly positive.

**Formalization Note.** The orthant is open: `Γ^ε_{n,m}` divides by `xᵢ`, and the proof of
Proposition 2 (p.16) shows the minimizer is "strictly positive" to place it "in this region".
Coordinate `i : Fin (m − 1)` is the paper's `x_{i+1}`. -/
def orthant (m : ℕ) : Set (Fin (m - 1) → ℝ) :=
  {x | ∀ i, 0 < x i}

/-- The paper's 1-based coordinate `xᵢ` (`1 ≤ i ≤ m − 1`) of `x : Fin (m − 1) → ℝ`; `0` for
other `i` (never used). -/
noncomputable def xi {m : ℕ} (x : Fin (m - 1) → ℝ) (i : ℕ) : ℝ :=
  if h : 1 ≤ i ∧ i ≤ m - 1 then x ⟨i - 1, by omega⟩ else 0

/-- **The function `Γ^ε_{n,m} : ℝ^{m−1}_+ → ℝ`.**
Brustle, Correa, Dütting, Verdugo, *The Competition Complexity of Dynamic Pricing*, accepted
manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), §5, p.15:
`Γ^ε_{n,m}(x) = ε + x₁ⁿ + Σ_{i=1}^{m−2} xᵢ(ε + (xᵢ₊₁/xᵢ)ⁿ) − x_{m−1}(n − 1 − ε)`.

**Formalization Note.** Indices are the paper's (1-based, via `xi`). The formula is used only on
the open orthant `orthant m`, where no division by zero occurs. -/
noncomputable def Gamma (ε : ℝ) (n m : ℕ) (x : Fin (m - 1) → ℝ) : ℝ :=
  ε + xi x 1 ^ n + ∑ i ∈ Finset.Icc 1 (m - 2), xi x i * (ε + (xi x (i + 1) / xi x i) ^ n)
    - xi x (m - 1) * ((n : ℝ) - 1 - ε)

/-- **The products `Yⱼ = Π_{k=0}^{j−1} ρ_{ε,m−k}` of (10)**, §5, p.15: `Y₁ = ρ_{ε,m}` and
`Yⱼ = Π_{k=0}^{j−1} ρ_{ε,m−k}`.

**Formalization Note.** Defined for every `j ≥ 0` by the same product (`Y₀ = 1`, the empty
product). Display (10) gives `j ∈ {1, …, m − 1}`; Proposition 3 (p.17) also uses `Yₘ`, and its
proof uses `Yₘ/Y_{m−1} = ρ_{ε,1} = 1`, which is the product formula at `j = m`. -/
noncomputable def Yseq (ε : ℝ) (n m j : ℕ) : ℝ :=
  ∏ k ∈ Finset.range j, rho ε n (m - k)

/-- **The vector `Y = (Y₁, …, Y_{m−1})` of (10)**, p.15, as a point of `ℝ^{m−1}`
(coordinate `i : Fin (m − 1)` is `Y_{i+1}`). -/
noncomputable def Yvec (ε : ℝ) (n m : ℕ) : Fin (m - 1) → ℝ :=
  fun i => Yseq ε n m (i.val + 1)

end CompetitionComplexity


