-- Prove2me | Definitions.Def_ResultantVNP_IsProjection
-- name    : ResultantVNP_IsProjection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:25:13.42536+00:00
-- url     : https://prove2.me/theorems/f15106a1-abff-41c1-b85b-9abf75ee4efc
-- title:
--   Projection of a polynomial
-- statement:
--   A polynomial $f$ is a **projection** of a polynomial $g$ if substituting variables of $f$ or field constants for the variables of $g$ gives $f$. Several variables of $g$ may be replaced by the same variable of $f$.
--
--   Projections are the reductions of Valiant's theory: VNP-hardness of a family under p-projections is defined from them.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Section 3.1, p.14

import Mathlib

namespace ResultantVNP

/-- `f` is a **projection** of `g`: substituting variables or field constants for the variables of
`g` gives `f`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Section 3.1, p.14: "A polynomial f is a projection of g if substituting variables or field
constants for the variables of g gives f."

**Formalization Note** `ρ v = inl x` substitutes the variable `x` of `f` for `v`, `ρ v = inr a` the
constant `a ∈ ℂ`; several variables of `g` may receive the same variable. -/
def IsProjection {σ τ : Type} (f : MvPolynomial σ ℂ) (g : MvPolynomial τ ℂ) : Prop :=
  ∃ ρ : τ → σ ⊕ ℂ,
    MvPolynomial.aeval (fun v => Sum.elim MvPolynomial.X MvPolynomial.C (ρ v)) g = f

end ResultantVNP


