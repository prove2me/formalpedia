-- Prove2me | Definitions.Def_CongestionTaxes_Assumption1
-- name    : CongestionTaxes_Assumption1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:31:47.26853+00:00
-- url     : https://prove2.me/theorems/3e8adc9c-41f5-4b9a-bb75-260f7b7ec8ef
-- title:
--   Assumption 1 — non-decreasing semi-convex resource cost
-- statement:
--   A **resource cost** is a function $\ell:\mathbb N\to\mathbb R_{>0}$, extended to $\mathbb N_0$ by $\ell(0)=0$. It satisfies **Assumption 1** if it is non-decreasing and **semi-convex**, that is, $x\ell(x)$ is convex:
--
--   $$
--   (x+1)\ell(x+1)-x\ell(x)\;\ge\;x\ell(x)-(x-1)\ell(x-1)\qquad\text{for all }x\in\mathbb N,\ x\ge 2 .
--   $$
--
--   Every result of the paper is stated for sets of costs satisfying this assumption; it covers, for example, all polynomials with nonnegative coefficients.
--
--   **Formalization Note** A cost is a function $\mathbb N\to\mathbb R$ with $\ell(0)=0$ (the paper's extension, p.5), positive and non-decreasing on $x\ge1$; semi-convexity is written at $x+1$ for $x\ge1$ to avoid natural-number subtraction.
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, Assumption 1 and footnote 4, p.5; extension ℓ(0) = 0, p.5

import Mathlib

namespace CongestionTaxes

/-- **Assumption 1** (Paccagnan, Gairing, *In Congestion Games, Taxes Achieve Optimal
Approximation*, arXiv:2105.07480v2, Assumption 1 and footnote 4, p.5): the resource cost
`ℓ : ℕ → ℝ>0` is non-decreasing and semi-convex, i.e. `x ℓ(x)` is convex:
`(x+1)ℓ(x+1) − xℓ(x) ≥ xℓ(x) − (x−1)ℓ(x−1)` for all `x ∈ ℕ`, `x ≥ 2`.

**Formalization Note** The paper's `ℕ` excludes `0`, and p.5 extends every cost to `ℕ₀` by
`ℓ(0) = 0`; the clause `ℓ 0 = 0` records that extension, so a cost is a function `ℕ → ℝ` that is
positive on `x ≥ 1` and vanishes at `0`. Monotonicity is required on `x ≥ 1` only, as on the
paper's `ℕ`. Semi-convexity is written at `x + 1` for `x ≥ 1` (that is, at the paper's `x ≥ 2`)
to avoid natural-number subtraction. -/
def Assumption1 (ℓ : ℕ → ℝ) : Prop :=
  ℓ 0 = 0 ∧ (∀ x : ℕ, 1 ≤ x → 0 < ℓ x) ∧ (∀ x : ℕ, 1 ≤ x → ℓ x ≤ ℓ (x + 1)) ∧
    ∀ x : ℕ, 1 ≤ x →
      ((x : ℝ) + 1) * ℓ (x + 1) - (x : ℝ) * ℓ x ≤
        ((x : ℝ) + 2) * ℓ (x + 2) - ((x : ℝ) + 1) * ℓ (x + 1)

end CongestionTaxes


