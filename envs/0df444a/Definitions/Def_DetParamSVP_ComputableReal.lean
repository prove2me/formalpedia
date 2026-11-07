-- Prove2me | Definitions.Def_DetParamSVP_ComputableReal
-- name    : DetParamSVP_ComputableReal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:34.201076+00:00
-- url     : https://prove2.me/theorems/4e94c602-9a60-42b9-8e88-5956b28a3e3b
-- title:
--   Computable real numbers
-- statement:
--   A real number $p$ is **computable** if an algorithm, given $r\in\mathbb Z_{>0}$, returns a rational number $a_r$ with $|a_r-p|\le2^{-r}$.
--
--   Theorems 1.1 and 3.5 assume the exponent $p$ of the norm to be computable; the reduction uses the approximations only to compute its integer parameters.
--
--   **Formalization Note** The algorithm is a Mathlib-`Computable` function $r\mapsto(a,b)\in\mathbb Z\times\mathbb N$, and the pair stands for the rational $a/(b+1)$; every rational has this form. The error bound is required for $r\ge1$, as printed.
-- source:
--   Hirahara–Lin–Liu–Ogitsuka, Deterministic Parameterized Inapproximability of the Shortest Vector and Minimum Distance Problems, STOC 2027 submission (manuscript sha256 4584f5e2…), §2.1, p.10, and footnote 1, p.2

import Mathlib

set_option autoImplicit false

namespace DetParamSVP

/-- A **computable real number**: some algorithm, given `r ∈ ℤ_{>0}`, returns a rational
approximation of `p` with error at most `2^{-r}`.

Hirahara–Lin–Liu–Ogitsuka, *Deterministic Parameterized Inapproximability of the Shortest Vector
and Minimum Distance Problems*, STOC 2027 submission (manuscript sha256 4584f5e2…), §2.1, p.10: "A
real number is computable if an algorithm, given r ∈ Z>0, returns a rational approximation with
error at most 2−r." (also footnote 1, p.2).

**Formalization Note.** The algorithm is a Mathlib-`Computable` function `a : ℕ → ℤ × ℕ`, and the
pair `(a, b)` stands for the rational `a / (b + 1)`; every rational has this form. The condition is
required for `r ≥ 1`, as printed. -/
def IsComputableReal (p : ℝ) : Prop :=
  ∃ a : ℕ → ℤ × ℕ, Computable a ∧
    ∀ r : ℕ, 1 ≤ r → |((a r).1 : ℝ) / (((a r).2 : ℝ) + 1) - p| ≤ 1 / 2 ^ r

end DetParamSVP


