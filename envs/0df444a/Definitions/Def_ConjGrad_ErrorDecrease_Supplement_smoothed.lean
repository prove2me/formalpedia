-- Prove2me | Definitions.Def_ConjGrad_ErrorDecrease_Supplement_smoothed
-- name    : ConjGrad_ErrorDecrease_Supplement_smoothed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T01:52:27.584189+00:00
-- url     : https://prove2.me/theorems/c4889116-3ccf-41d1-b485-1264445cc178
-- title:
--   The smoothed estimates $\bar x_i$ and weights $c_i$ of (7:2)
-- statement:
--   For the cg-method started at $x_0$, with the scalars $b_i=|r_{i+1}|^2/|r_i|^2$ of (5:1e), the weights $c_i$ and the **smoothed estimates** $\bar x_i$ are defined by the recursion (7:2):
--
--   $$c_0=1,\quad c_{i+1}=1+b_ic_i,\qquad \bar x_0=x_0,\quad \bar x_{i+1}=\frac{x_{i+1}+b_ic_i\bar x_i}{c_{i+1}} .$$
--
--   The residual of $\bar x_i$ is $\bar r_i=k-A\bar x_i$. These are the second set of estimates of §7: their residuals are proportional to the conjugate gradients and minimize the squared residual on $P_i$ (Theorems 7:1–7:5).
--
--   **Formalization Note** `cgBeta A k x₀ i` is $b_i$ read off the published iteration `cgIter` (with $t/0=0$, so $b_i=0$ once $r_i=0$); `smoothC A k x₀ i` is $c_i$ and `smoothX A k x₀ i` is $\bar x_i$. Since $b_i\ge0$, every $c_i\ge1$ and (7:2b) never divides by zero.
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 418, eqs. (7:2a), (7:2b); eq. (5:1e) on p. 414 (PDF p. 10)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter

open Matrix

namespace ConjGrad.ErrorDecrease.Supplement

/-- The scalar `bᵢ = |rᵢ₊₁|² / |rᵢ|²` of the cg-method, eq. (5:1e), read off the published
iteration `cgIter`. Lean's `t / 0 = 0` makes it `0` once `rᵢ = 0`. -/
noncomputable def cgBeta {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k x₀ : Fin n → ℝ) (i : ℕ) : ℝ :=
  ((cgIter A k x₀ (i + 1)).r ⬝ᵥ (cgIter A k x₀ (i + 1)).r) /
    ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r)

/-- The pair `(cᵢ, x̄ᵢ)` of §7, defined by the recursion (7:2) (p. 418):
`c₀ = 1`, `cᵢ₊₁ = 1 + bᵢcᵢ` (7:2a); `x̄₀ = x₀`, `x̄ᵢ₊₁ = (xᵢ₊₁ + bᵢcᵢx̄ᵢ)/cᵢ₊₁` (7:2b),
where `xᵢ` and `bᵢ` are those of the cg-method started at `x₀`. -/
noncomputable def smoothed {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k x₀ : Fin n → ℝ) :
    ℕ → ℝ × (Fin n → ℝ)
  | 0 => (1, x₀)
  | i + 1 =>
    let s := smoothed A k x₀ i
    let bc := cgBeta A k x₀ i * s.1
    (1 + bc, (1 + bc)⁻¹ • ((cgIter A k x₀ (i + 1)).x + bc • s.2))

/-- The weight `cᵢ` of (7:2a). -/
noncomputable def smoothC {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k x₀ : Fin n → ℝ) (i : ℕ) : ℝ :=
  (smoothed A k x₀ i).1

/-- The smoothed estimate `x̄ᵢ` of (7:2b). Its residual is `r̄ᵢ = k − Ax̄ᵢ`. -/
noncomputable def smoothX {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k x₀ : Fin n → ℝ) (i : ℕ) :
    Fin n → ℝ :=
  (smoothed A k x₀ i).2

end ConjGrad.ErrorDecrease.Supplement


