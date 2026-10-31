-- Prove2me | Definitions.Def_RobustToDynamics_alpha1
-- name    : RobustToDynamics_alpha1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:20.703473+00:00
-- url     : https://prove2.me/theorems/772d61c1-af11-4ef0-98a1-45d277b7f3b6
-- title:
--   The inner level $\alpha_1=\min_i b_i^2/(a_i^TM^{-1}a_i)$ of (2.15)
-- statement:
--   Let $M$ be a real $n\times n$ matrix, $A\in\mathbb R^{m\times n}$ with rows $a_1^T,\dots,a_m^T$, and $b\in\mathbb R^m$. Display (2.15) sets
--   $$
--   \alpha_1=\min_{i}\ \frac{b_i^2}{a_i^TM^{-1}a_i},
--   $$
--   the minimum taken over the rows with $a_i\neq0$. With $M\succ0$ and the origin interior to $P$, $E(\alpha_1)\subseteq P$.
--
--   **Formalization Note** At a zero row the printed quotient has denominator $0$; such a row constrains nothing, so it is left out of the minimum (a reading of (2.15)). If $A$ has no nonzero row, $\alpha_1=1$ by convention. $M^{-1}$ is Mathlib's matrix inverse, the true inverse when $M$ is invertible.
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, Theorem 2.7, proof, Step 2, display (2.15), p.15

import Mathlib

open Matrix

namespace RobustToDynamics

open Classical in
/-- **The inner-ellipsoid level `α₁` of (2.15).**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, Theorem 2.7, proof,
Step 2, display (2.15), p.15:
"α1 = min_{i∈{1,...,m}} {b2i /η2i} = min_{i∈{1,...,m}} { b2i / (aTi M−1ai) }",
where `aᵢᵀ` is the `i`-th row of `A`.

`alpha1 M A b` is the minimum of `bᵢ² / (aᵢᵀ M⁻¹ aᵢ)` over the rows `i` with `aᵢ ≠ 0`.

**Formalization Note.** At a zero row `aᵢ = 0` the printed quotient has denominator `0` and is
undefined; such a row constrains nothing (`0 ≤ bᵢ`), so the minimum is taken over the nonzero rows
only (reading). If `A` has no nonzero row, the value is `1` by convention (then `P` is `ℝⁿ` or
empty and any level works). `M⁻¹` is Mathlib's `Matrix.inv`, the true inverse whenever `M` is
invertible (e.g. positive definite). -/
noncomputable def alpha1 {m n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : ℝ :=
  if h : (Finset.univ.filter fun i : Fin m => A i ≠ 0).Nonempty then
    (Finset.univ.filter fun i : Fin m => A i ≠ 0).inf' h
      (fun i => b i ^ 2 / (A i ⬝ᵥ (M⁻¹ *ᵥ A i)))
  else 1

end RobustToDynamics


