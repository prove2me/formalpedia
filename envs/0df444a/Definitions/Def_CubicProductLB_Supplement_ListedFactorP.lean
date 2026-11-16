-- Prove2me | Definitions.Def_CubicProductLB_Supplement_ListedFactorP
-- name    : CubicProductLB_Supplement_ListedFactorP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:37:22.683525+00:00
-- url     : https://prove2.me/theorems/99785a59-d1e1-4616-937e-7db445bc99b0
-- title:
--   Listed factor over $\mathbb F_p$, its value and occurrence cost
-- statement:
--   A **listed factor** over $\mathbb F_p$ is a finite list of listed monomial occurrences. It computes the function $x \mapsto \sum a\,x_1^{e_1}\cdots x_n^{e_n}$ (sum over the list), and its **occurrence cost** is the sum of $e_1+\dots+e_n$ over the occurrences. Repeated terms count with multiplicity; constant monomials cost $0$.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Definition 2, p.4; Section 15.14, p.65 ("total variable-occurrence cost")

import Mathlib
import Definitions.Def_CubicProductLB_Supplement_ListedMonomialP

namespace CubicProductLB.Supplement

/-- A listed factor over `F_p`: a finite list of listed monomial occurrences (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Definition 2, p.4,
used over `F_p` in Section 15.14, p.65).

**Formalization Note** A `List`, so a repeated term is two occurrences and costs twice. -/
abbrev ListedFactorP (p n : ℕ) := List (ListedMonomialP p n)

/-- The function a listed factor computes: the sum of its monomial occurrences. -/
def ListedFactorP.eval {p n : ℕ} (l : ListedFactorP p n) (x : Fin n → ZMod p) : ZMod p :=
  (l.map fun m => m.coeff * ∏ i, x i ^ m.exps i).sum

/-- The occurrence cost of a factor: the sum of `e_1 + ⋯ + e_n` over its listed monomial occurrences
(Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Definition 2, p.4; "total variable-occurrence cost", p.65). A constant monomial has cost `0`. -/
def ListedFactorP.cost {p n : ℕ} (l : ListedFactorP p n) : ℕ :=
  (l.map fun m => ∑ i, m.exps i).sum

end CubicProductLB.Supplement


