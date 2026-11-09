-- Prove2me | Definitions.Def_ResultantVNP_form
-- name    : ResultantVNP_form
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:28:04.683204+00:00
-- url     : https://prove2.me/theorems/c66f8c3f-7d41-47d7-a430-cd0d00a5ac21
-- title:
--   The form $f_i(x)=\sum_{|e|=d_i} c_{i,e}x^e$ with given coefficients
-- statement:
--   Given complex coefficients $c=(c_{i,e})$, one for each coefficient variable $u_{i,e}$, the $i$-th form is the homogeneous polynomial
--
--   $$
--   f_i(x)=\sum_{|e|=d_i} c_{i,e}\,x^e\in\mathbb C[x_1,\dots,x_n]
--   $$
--
--   of degree $d_i$ (or the zero polynomial). Property 1 of the resultant speaks about the common zeros of $f_1,\dots,f_n$.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Definition 2.1, p.11

import Mathlib
import Definitions.Def_ResultantVNP_CoeffVar

namespace ResultantVNP

/-- The form `f_i(x) = ∑_{|e| = d_i} c_{i,e} x^e` with complex coefficients `c : CoeffVar d → ℂ`: the
`i`-th homogeneous polynomial of degree `d_i` in `n` variables `x = (x₁, …, xₙ)` over `ℂ`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Definition 2.1, p.11: "for i ∈ [n], let f_i(𝒙) = Σ_{|𝒆|=d_i} c_{i,𝒆} 𝒙^𝒆 be a homogeneous
polynomial of degree d_i in n variables 𝒙 = (x₁, …, xₙ) over ℂ."

**Formalization Note** Variables are indexed by `Fin n` (0-based). -/
noncomputable def form {n : ℕ} (d : Fin n → ℕ) (c : CoeffVar d → ℂ) (i : Fin n) :
    MvPolynomial (Fin n) ℂ :=
  ∑ e : {e : Fin n →₀ ℕ // ∑ j, e j = d i}, MvPolynomial.monomial e.1 (c ⟨i, e⟩)

end ResultantVNP


