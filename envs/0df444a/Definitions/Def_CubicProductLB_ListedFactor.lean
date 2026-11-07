-- Prove2me | Definitions.Def_CubicProductLB_ListedFactor
-- name    : CubicProductLB_ListedFactor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:14:42.779963+00:00
-- url     : https://prove2.me/theorems/f2e48386-2719-460e-88da-e046adcaad2c
-- title:
--   A listed factor, its value and its occurrence cost
-- statement:
--   A **listed factor** is a finite list of listed monomial occurrences, so repeated terms are separate occurrences. Its **value** at $x$ is the sum of its monomials at $x$. Its **occurrence cost** is
--   $$\sum_{a x^{e} \text{ listed}} (e_1 + \cdots + e_n),$$
--   the sum over the listed occurrences. A constant monomial has cost zero.
--
--   **Formalization Note** A factor is a `List`, not a polynomial, because the cost is syntactic: the same monomial listed twice costs twice as much, and a listing need not be collected.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Definition 2, p.4

import Mathlib
import Definitions.Def_CubicProductLB_ListedMonomial

namespace CubicProductLB

/-- A listed factor: a finite list of listed monomial occurrences
(Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Definition 2, p.4: "Repeated terms, nonsymmetric factors, arbitrary powers, and either
nonzero coefficient in F3 are allowed").

**Formalization Note** A `List`, so a repeated term is two occurrences and costs twice. -/
abbrev ListedFactor (n : ℕ) := List (ListedMonomial n)

/-- The function a listed factor computes: the sum of its monomial occurrences. -/
def ListedFactor.eval {n : ℕ} (l : ListedFactor n) (x : Fin n → ZMod 3) : ZMod 3 :=
  (l.map fun m => m.coeff * ∏ i, x i ^ m.exps i).sum

/-- The occurrence cost of a factor: the sum of `e_1 + ⋯ + e_n` over its listed monomial
occurrences (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Definition 2, p.4). A constant monomial has cost `0`. -/
def ListedFactor.cost {n : ℕ} (l : ListedFactor n) : ℕ :=
  (l.map fun m => ∑ i, m.exps i).sum

end CubicProductLB


