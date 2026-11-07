-- Prove2me | Definitions.Def_CubicProductLB_ListedMonomial
-- name    : CubicProductLB_ListedMonomial
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:12:46.285012+00:00
-- url     : https://prove2.me/theorems/43bcb177-1812-4e2b-b158-d8975453d330
-- title:
--   A listed monomial $a x_1^{e_1} \cdots x_n^{e_n}$, $a \ne 0$
-- statement:
--   A **listed monomial** is an expression $a x_1^{e_1} \cdots x_n^{e_n}$ with a nonzero coefficient $a \in \mathbb F_3$ and arbitrary exponents $e_1, \dots, e_n \ge 0$. Exponents are not reduced: they are part of the syntax that the occurrence cost measures.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Definition 2, p.4

import Mathlib

namespace CubicProductLB

/-- A listed monomial `a x_1^{e_1} ⋯ x_n^{e_n}` with `a ≠ 0` over `F_3`
(Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Definition 2, p.4).

**Formalization Note** Arbitrary exponents are allowed, as on the page. -/
structure ListedMonomial (n : ℕ) where
  /-- the coefficient `a` -/
  coeff : ZMod 3
  /-- `a ≠ 0` -/
  coeff_ne : coeff ≠ 0
  /-- the exponents `e_1, …, e_n` -/
  exps : Fin n → ℕ

end CubicProductLB


