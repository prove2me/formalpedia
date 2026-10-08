-- Prove2me | Definitions.Def_SemialgebraicSDP_Psatz_Gram
-- name    : SemialgebraicSDP_Psatz_Gram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:00.828999+00:00
-- url     : https://prove2.me/theorems/7ad41dd5-e823-4901-8ca7-922cc6e4e568
-- title:
--   Monomials of degree $\le D$, the vector $z$ and the Gram polynomial $z^TQz$ of (3.5)
-- statement:
--   Fix natural numbers $n$ and $D$. Let $\mathrm{Mon}(n,D)$ be the finite set of exponent vectors $\alpha=(\alpha_1,\dots,\alpha_n)\in\mathbb N^n$ with $\alpha_1+\dots+\alpha_n\le D$, and let $z$ be the vector indexed by $\mathrm{Mon}(n,D)$ whose $\alpha$-entry is the monomial $x^\alpha=x_1^{\alpha_1}\cdots x_n^{\alpha_n}$:
--   $$
--   z=[1,x_1,x_2,\dots,x_n,x_1x_2,\dots,x_n^D].
--   $$
--   For a real matrix $Q$ with rows and columns indexed by $\mathrm{Mon}(n,D)$, the **Gram polynomial** of $Q$ is
--   $$
--   z^TQz=\sum_{\alpha,\beta\in\mathrm{Mon}(n,D)} Q_{\alpha\beta}\,x^{\alpha}x^{\beta}\in\mathbb R[x_1,\dots,x_n],
--   $$
--   the sum running over all ordered pairs $(\alpha,\beta)$. This is the representation $F(x)=z^TQz$ of (3.5), the basis of the Gram matrix method: a polynomial of degree $2d$ is a sum of squares exactly when it equals $z^TQz$ for some positive semidefinite $Q$ over the monomials of degree at most $d$.
--
--   **Formalization Note** $\mathrm{Mon}(n,D)$ is the subtype of maps $\alpha:\{1,\dots,n\}\to\{0,\dots,D\}$ with $\sum_i\alpha_i\le D$, a finite type; each $\alpha$ is turned into a finitely supported exponent vector to form the monomial.
-- source:
--   Parrilo, Semidefinite programming relaxations for semialgebraic problems, Math. Program. Ser. B 96 (2003) 293–320, p. 298, §3.2, (3.5)

import Mathlib

namespace SemialgebraicSDP.Psatz

open MvPolynomial

/-- Exponent vectors of the monomials of total degree at most `D` in `n` variables
(§3.2, (3.5), p. 298): `α : Fin n → {0, …, D}` with `α₁ + ⋯ + αₙ ≤ D`. A finite type. -/
abbrev Mon (n D : ℕ) : Type := {α : Fin n → Fin (D + 1) // ∑ i, (α i : ℕ) ≤ D}

/-- The exponent vector of `α : Mon n D` as a finitely supported function `Fin n →₀ ℕ`. -/
noncomputable def Mon.toFinsupp {n D : ℕ} (α : Mon n D) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (α.1 i : ℕ))

/-- The vector `z` of (3.5) (p. 298): its `α`-entry is the monomial `x^α = x₁^{α₁} ⋯ xₙ^{αₙ}`, for every
monomial of total degree at most `D`. -/
noncomputable def monVec (n D : ℕ) (α : Mon n D) : MvPolynomial (Fin n) ℝ :=
  monomial α.toFinsupp 1

/-- The polynomial `zᵀQz` of (3.5) (p. 298) for a real matrix `Q` indexed by the monomials of total
degree at most `D`: `∑_{α, β} z_α Q_{αβ} z_β`, summed over all ordered pairs `(α, β)`. -/
noncomputable def gramPoly {n D : ℕ} (Q : Matrix (Mon n D) (Mon n D) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ α, ∑ β, monVec n D α * C (Q α β) * monVec n D β

end SemialgebraicSDP.Psatz


