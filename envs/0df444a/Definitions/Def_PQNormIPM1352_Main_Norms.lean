-- Prove2me | Definitions.Def_PQNormIPM1352_Main_Norms
-- name    : PQNormIPM1352_Main_Norms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:06:03.607786+00:00
-- url     : https://prove2.me/theorems/2e275412-a22a-41da-8446-7e945badd86b
-- title:
--   Real-exponent $\ell_p$ norms, the conjugate exponent $p^*$ and the $p\to q$ operator norm
-- statement:
--   For a real exponent $p \ge 1$ and a vector $x \in \mathbb R^\iota$ (a finite index set $\iota$), the $\ell_p$ norm is
--
--   $$\|x\|_p = \Big(\sum_{i} |x(i)|^p\Big)^{1/p},$$
--
--   and for $p > 1$ the conjugate exponent is $p^* = p/(p-1)$, the solution of $1/p + 1/p^* = 1$.
--
--   For a real $m \times n$ matrix $A$ and exponents $p, q \ge 1$, the **$p \to q$ norm** is
--
--   $$\|A\|_{p\to q} = \max_{x \in \mathbb R^n,\ \|x\|_p = 1} \|Ax\|_q .$$
--
--   It is the quantity the mission's algorithm approximates. For $p = q = 2$ it is the largest singular value of $A$.
--
--   **Formalization Note** The norm is defined as the supremum of the set $\{\|Ax\|_q : \|x\|_p = 1\}$. For $n \ge 1$ this set is nonempty, bounded and its supremum is attained, so the supremum is the maximum of the paper. For $n = 0$ the set is empty and Lean's convention gives the value $0$; no non-degenerate instance is affected. Powers are real powers (`Real.rpow`), with no restriction to integer exponents.
-- source:
--   Marco Pirazzini, Daniel Spielman, A Fast and Accurate Algorithm for the p → q Norm of Sparse Non-Negative Matrices, STOC 2027 submission #1352 (October 2026), §1, p. 1 (definition of ‖A‖_{p→q}); §2.1.1, p. 3 (‖x‖_p and p*)

import Mathlib

/-!
# Real-exponent `ℓ_p` norms and the `p → q` operator norm

Pirazzini–Spielman, *A Fast and Accurate Algorithm for the p → q Norm of Sparse Non-Negative
Matrices*, STOC 2027 submission #1352: §1, p. 1 (definition of `‖A‖_{p→q}`) and §2.1.1, p. 3
(`‖x‖_p`, the conjugate exponent `p*`).
-/

open Matrix

namespace PQNormIPM1352.Main

noncomputable section

/-- The `ℓ_p` norm with a real exponent: `‖x‖_p = (∑ᵢ |x(i)|^p)^{1/p}` (§2.1.1, p. 3). Used for
real `p ≥ 1`. -/
def pNorm {ι : Type*} [Fintype ι] (p : ℝ) (x : ι → ℝ) : ℝ :=
  (∑ i, |x i| ^ p) ^ (1 / p)

/-- The conjugate exponent `p* = p / (p − 1)`, the solution of `1/p + 1/p* = 1` for `p > 1`
(§2.1.1, p. 3). -/
def conjExp (p : ℝ) : ℝ := p / (p - 1)

/-- The `p → q` norm `‖A‖_{p→q} = max_{x : ‖x‖_p = 1} ‖Ax‖_q` of a real `m × n` matrix (§1, p. 1),
encoded as the supremum of `{‖Ax‖_q : ‖x‖_p = 1}` over `ℝⁿ`. For `n ≥ 1` and `p ≥ 1` the set is
nonempty, bounded and its supremum is attained; for `n = 0` it is empty and Lean's `sSup ∅ = 0`. -/
def opNormPQ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (p q : ℝ) : ℝ :=
  sSup {t : ℝ | ∃ x : Fin n → ℝ, pNorm p x = 1 ∧ t = pNorm q (A *ᵥ x)}

end

end PQNormIPM1352.Main


