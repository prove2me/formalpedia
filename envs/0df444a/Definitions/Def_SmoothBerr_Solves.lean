-- Prove2me | Definitions.Def_SmoothBerr_Solves
-- name    : SmoothBerr_Solves
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:15.214143+00:00
-- url     : https://prove2.me/theorems/ff030cb8-09da-4ab6-a9b4-852846ceeca5
-- title:
--   Forward-error success $\|\tilde x-\hat A^{-1}b\|_2\le\frac1{20}\|\hat A^{-1}b\|_2$
-- statement:
--   For a square matrix $M$, a right-hand side $b$ and a candidate solution $\tilde x$, the output $\tilde x$ **solves the system to forward error $1/20$** if
--   $$
--   \|\tilde x-M^{-1}b\|_2\le\frac1{20}\,\|M^{-1}b\|_2 .
--   $$
--   This is the success criterion of Theorems 2.1 and 4.1. The definition also counts a sample with singular $M$ as a success, since the criterion is undefined there.
--
--   **Formalization Note** The vector norm is the published Euclidean norm `ApproxVI.euclNorm` ($\sqrt{\sum_i x_i^2}$ on `Fin n → ℝ`). Mathlib's matrix inverse is total ($M^{-1}=0$ when $\det M=0$); the disjunct "$M$ is singular" makes a success requirement ask less of an algorithm, so a lower bound assuming it is at least as strong as the printed one. In the paper's hard instances $M$ is almost surely invertible.
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), Theorem 2.1, p.3; Theorem 4.1, p.5 (‖x̃ − Â^{−1}b‖₂ ≤ (1/20)‖Â^{−1}b‖₂)

import Mathlib
import Definitions.Def_ApproxVI_euclNorm

open Matrix

namespace SmoothBerr

/-- **Success of a linear-system solver** (Dereziński, Mahoney, Meyer, Musco, *From smoothed
analysis to backward error: The power of adaptive perturbations*, manuscript of 3 Nov 2026,
sha256 9575cd20…, Theorem 2.1, p.3, and Theorem 4.1, p.5): the output `x̃` for the system
`M x = b` satisfies the forward-error bound
`‖x̃ − M⁻¹b‖₂ ≤ (1/20)‖M⁻¹b‖₂`, or `M` is singular.

**Formalization Note** Mathlib's matrix inverse is total (`M⁻¹ = 0` when `det M = 0`). On a
singular `M` the paper's condition is undefined, and the disjunct `¬ IsUnit M.det` counts such a
sample as a success: a success requirement then asks less of an algorithm, so a lower bound
assuming it is stronger than the printed one. `ApproxVI.euclNorm` is the Euclidean norm (published). -/
def Solves {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) : Prop :=
  ¬ IsUnit M.det ∨ ApproxVI.euclNorm (x - M⁻¹ *ᵥ b) ≤ (1 / 20) * ApproxVI.euclNorm (M⁻¹ *ᵥ b)

end SmoothBerr


