-- Prove2me | Definitions.Def_BorderDiffEq_shift
-- name    : BorderDiffEq_shift
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:25:18.268789+00:00
-- url     : https://prove2.me/theorems/701f1062-afd0-4b3c-8e57-a0631eef09e9
-- title:
--   The shift $\Phi_y(g)(z,x)=g(y+zx)$, equation (18)
-- statement:
--   Let $y=(y_1,\dots,y_n)$, $x=(x_1,\dots,x_n)$ and $z$ be fresh variables. For a polynomial $g(x)$ over a commutative ring $R$, the **shift** is
--   $$
--   \Phi_y(g)(y,z,x):=g(y+zx),
--   $$
--   obtained by replacing every $x_l$ by $y_l+z\,x_l$. The coefficient of $z^q$ in $\Phi_y(g)$ is the degree-$q$ homogeneous part in $x$ of $g(y+x)$. The paper writes $D=\partial/\partial z$ and regards polynomials in $(y,z,x)$ as univariate polynomials in $z$.
--
--   **Formalization Note** A polynomial in $(y,z,x)$ is a `Polynomial` in $z$ over `MvPolynomial (σ ⊕ σ) R`, with $y_l$ = `X (Sum.inl l)` and $x_l$ = `X (Sum.inr l)`. Then $D$ is `Polynomial.derivative` and "mod $z^{d+1}$" is divisibility by `X ^ (d+1)`.
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), §5.1, p.30, equation (18)

import Mathlib

namespace BorderDiffEq

/-- **The shift `Φ_y`, equation (18)** (Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of
Structured Algebraic Circuits via Differential Equations*, manuscript (STOC 2027 submission), §5.1,
p.30, (18)): `Φ_y(g)(z, x) := g(y + z x)`, i.e. every variable `xₗ` is replaced by `yₗ + z·xₗ`.

**Formalization Note.** A polynomial in `(y, z, x)` over `R` is a univariate polynomial in `z` (the
`Polynomial` variable) over `MvPolynomial (σ ⊕ σ) R`, with `yₗ = X (Sum.inl l)` and
`xₗ = X (Sum.inr l)`. Then `D = ∂/∂z` is `Polynomial.derivative` and "mod `z^{d+1}`" is
divisibility by `Polynomial.X ^ (d+1)`. -/
noncomputable def shift {R : Type} [CommRing R] {σ : Type} (g : MvPolynomial σ R) :
    Polynomial (MvPolynomial (σ ⊕ σ) R) :=
  MvPolynomial.aeval
    (fun l => Polynomial.C (MvPolynomial.X (Sum.inl l)) +
      Polynomial.X * Polynomial.C (MvPolynomial.X (Sum.inr l))) g

end BorderDiffEq


