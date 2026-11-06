-- Prove2me | Definitions.Def_LawLocalComp_IsMonotoneNorm
-- name    : LawLocalComp_IsMonotoneNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:09:53.895662+00:00
-- url     : https://prove2.me/theorems/82e39c53-6242-4fa4-a717-e1d9f3f808ff
-- title:
--   Norm monotone on the nonnegative orthant
-- statement:
--   A function $g:\mathbb R^d\to\mathbb R$ is a **norm monotone on $\mathbb R^d_+$** if it is a norm,
--   1. $g(x)=0\Rightarrow x=0$,
--   2. $g(cx)=|c|\,g(x)$,
--   3. $g(x+y)\le g(x)+g(y)$,
--
--   and $0\le x\le y$ (coordinatewise) implies $g(x)\le g(y)$. The norm need not be symmetric under coordinate permutations.
--
--   **Formalization Note** The norm is a predicate on functions, not a typeclass instance: $\mathbb R^d$ (`Fin d → ℝ`) already carries Mathlib's sup norm, which is the maximum norm $\|\cdot\|_\infty$ of (14).
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), §1, p.2; §2, p.3

import Mathlib

namespace LawLocalComp

/-- **A norm monotone on the nonnegative orthant.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), §1, p.2 ("any norm g monotone on Rd +"; "The norm need not be symmetric"); §2, p.3.

`IsMonotoneNorm g` for `g : ℝ^d → ℝ`: `g` is a norm (definite, absolutely homogeneous, subadditive)
and `0 ≤ x ≤ y` coordinatewise implies `g x ≤ g y`.

**Formalization Note.** The norm is a predicate on functions rather than a `Norm` instance, because
`Fin d → ℝ` already carries Mathlib's sup norm `‖·‖`; that ambient norm is the maximum norm of
(14). Nonnegativity of `g` follows from the axioms. -/
def IsMonotoneNorm {d : ℕ} (g : (Fin d → ℝ) → ℝ) : Prop :=
  (∀ x, g x = 0 → x = 0) ∧ (∀ (c : ℝ) x, g (c • x) = |c| * g x) ∧
    (∀ x y, g (x + y) ≤ g x + g y) ∧ ∀ x y, 0 ≤ x → x ≤ y → g x ≤ g y

end LawLocalComp


