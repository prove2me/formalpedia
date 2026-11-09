-- Prove2me | Definitions.Def_ResultantVNP_IsMultivariateResultant
-- name    : ResultantVNP_IsMultivariateResultant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:31:00.13524+00:00
-- url     : https://prove2.me/theorems/a87caaba-63e1-49ce-a4a2-bfd01825a558
-- title:
--   The three defining properties of the multivariate resultant
-- statement:
--   Let $d_1,\dots,d_n$ be positive integers. An integral polynomial $R\in\mathbb Z[u]$ in the coefficient variables $u_{i,e}$ **has the properties of the multivariate resultant** $\mathrm{Res}_{d_1,\dots,d_n}$ if:
--
--   1. for every choice of coefficients $c_{i,e}\in\mathbb C$, $R(c)=0$ if and only if the system $f_1(x)=\dots=f_n(x)=0$ has a nontrivial solution $x\in\mathbb C^n\setminus\{0\}$, where $f_i=\sum_{|e|=d_i}c_{i,e}x^e$;
--   2. $R$ evaluated at the coefficients of $(x_1^{d_1},\dots,x_n^{d_n})$ equals $1$;
--   3. $R$ is irreducible, even when viewed as a polynomial in $\mathbb C[u]$.
--
--   By Definition 2.1 the multivariate resultant is the unique integral polynomial with these properties.
--
--   **Formalization Note** In properties 1 and 3, $R$ is mapped to $\mathbb C[u]$ by the canonical ring map $\mathbb Z\to\mathbb C$. The coefficient vector of $(x_1^{d_1},\dots,x_n^{d_n})$ is $u_{i,e}\mapsto 1$ if $e=d_i\mathbf e_i$ and $0$ otherwise.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Definition 2.1, p.11

import Mathlib
import Definitions.Def_ResultantVNP_form

namespace ResultantVNP

/-- `R ∈ ℤ[u]` **satisfies the three defining properties of the multivariate resultant**
`Res_{d₁,…,dₙ}` (Definition 2.1):

1. for every choice of coefficients `c_{i,e} ∈ ℂ`, `Res(f₁, …, fₙ) = 0` if and only if
   `f₁(x) = ⋯ = fₙ(x) = 0` has a nontrivial solution `x ∈ ℂⁿ \ {0}`, where `Res(f₁, …, fₙ)` is the
   evaluation of `R` at `u_{i,e} ↦ c_{i,e}`;
2. `Res(x₁^{d₁}, …, xₙ^{dₙ}) = 1`;
3. `R` is irreducible, even when viewed as a polynomial in `ℂ[u]`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Definition 2.1, p.11.

**Formalization Note** In (1) and (3) `R` is mapped to `ℂ[u]` by `Int.castRingHom ℂ`. In (2) the
coefficient vector of `(x₁^{d₁}, …, xₙ^{dₙ})` is `u_{i,e} ↦ 1` if `e = d_i·e_i` and `0` otherwise.
Clause (3) is the printed condition (irreducibility in `ℂ[u]`); irreducibility in `ℤ[u]` is not
stated separately. -/
def IsMultivariateResultant {n : ℕ} (d : Fin n → ℕ) (R : MvPolynomial (CoeffVar d) ℤ) : Prop :=
  (∀ c : CoeffVar d → ℂ,
      MvPolynomial.eval c (MvPolynomial.map (Int.castRingHom ℂ) R) = 0 ↔
        ∃ x : Fin n → ℂ, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (form d c i) = 0) ∧
    MvPolynomial.eval
        (fun v : CoeffVar d => if v.2.1 = Finsupp.single v.1 (d v.1) then (1 : ℤ) else 0) R = 1 ∧
    Irreducible (MvPolynomial.map (Int.castRingHom ℂ) R)

end ResultantVNP


