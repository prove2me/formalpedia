-- Prove2me | Definitions.Def_CubicProductLB_Supplement_ListedMonomialP
-- name    : CubicProductLB_Supplement_ListedMonomialP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:36:51.369128+00:00
-- url     : https://prove2.me/theorems/c71cd037-b36e-4dea-acc4-a65fb03fb061
-- title:
--   Listed monomial over $\mathbb F_p$
-- statement:
--   A **listed monomial** over $\mathbb F_p$ is an expression $a\,x_1^{e_1}\cdots x_n^{e_n}$ with $a \in \mathbb F_p$, $a \ne 0$, and arbitrary exponents $e_i \ge 0$. Its occurrence cost is $e_1+\dots+e_n$.
--
--   **Formalization Note** The base mission's listed monomial over $\mathbb F_3$, with the field replaced by $\mathbb F_p$, as Section 15.14 requires.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Definition 2, p.4; Section 15.14, p.65

import Mathlib

namespace CubicProductLB.Supplement

/-- A listed monomial `a x_1^{e_1} ⋯ x_n^{e_n}` with `a ≠ 0` over `F_p` (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Definition 2, p.4, used over
`F_p` in Section 15.14, p.65).

**Formalization Note** Arbitrary exponents are allowed, as in Definition 2. This is the base
mission's `CubicProductLB.ListedMonomial` with `ZMod 3` replaced by `ZMod p`. -/
structure ListedMonomialP (p n : ℕ) where
  /-- the coefficient `a` -/
  coeff : ZMod p
  /-- `a ≠ 0` -/
  coeff_ne : coeff ≠ 0
  /-- the exponents `e_1, …, e_n` -/
  exps : Fin n → ℕ

end CubicProductLB.Supplement


