-- Prove2me | Definitions.Def_L0BnB_Relax_bigMObj
-- name    : L0BnB_Relax_bigMObj
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:42:48.04109+00:00
-- url     : https://prove2.me/theorems/3431ae52-7747-447c-8edf-3c3e503ac270
-- title:
--   Objective of the Big-M formulation B(M), eq. (2)
-- statement:
--   For $(\beta,z)\in\mathbb R^p\times\mathbb R^p$ the objective of the Big-M formulation (2) is
--
--   $$\frac12\|y-X\beta\|_2^2+\lambda_0\sum_{i\in[p]}z_i+\lambda_2\|\beta\|_2^2 .$$
--
--
--   **Formalization Note** $\|\beta\|_2^2$ is written as $\sum_i\beta_i^2$.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, eq. (2), p. 5

import Mathlib
import Definitions.Def_L0BnB_Relax_rss

namespace L0BnB.Relax

/-- **Objective of the Big-M formulation B(M)**, eq. (2).
Hazimeh, Mazumder, Saab, *Sparse Regression at Scale: Branch-and-Bound rooted in First-Order
Optimization*, arXiv:2004.06152v2, eq. (2), p. 5: "`min_{β,z} (1/2)‖y − Xβ‖²₂ + λ0 Σ_{i∈[p]} zi + λ2‖β‖²₂`".

`bigMObj X y lam0 lam2 β z = ½‖y − Xβ‖²₂ + λ₀ ∑ᵢ zᵢ + λ₂ ∑ᵢ βᵢ²`.

**Formalization Note.** `‖β‖²₂` is written as `∑ᵢ βᵢ²` and `½‖y − Xβ‖²₂` as `rss`
(paper.md Reading 5). -/
noncomputable def bigMObj {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 : ℝ) (β z : Fin p → ℝ) : ℝ :=
  rss X y β + lam0 * ∑ i, z i + lam2 * ∑ i, β i ^ 2

end L0BnB.Relax


