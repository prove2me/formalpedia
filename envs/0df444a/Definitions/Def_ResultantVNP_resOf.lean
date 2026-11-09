-- Prove2me | Definitions.Def_ResultantVNP_resOf
-- name    : ResultantVNP_resOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:36:17.362249+00:00
-- url     : https://prove2.me/theorems/6b32f7d6-27f9-466e-b467-159298d7f0e3
-- title:
--   $\mathrm{Res}(f_1,\dots,f_n)$ of given forms
-- statement:
--   For forms $f_1,\dots,f_n\in\mathbb C[x_1,\dots,x_n]$ and a degree vector $d$, $\mathrm{Res}_d(f_1,\dots,f_n)$ is the resultant $\mathrm{Res}_d$ evaluated by replacing each variable $u_{i,e}$ with the coefficient $[x^e]f_i$.
--
--   This is the notation $\mathrm{Res}(f_1,\dots,f_n)$ of Definition 2.1; when $f_i$ is homogeneous of degree $d_i$, these are all of its coefficients. It is used to state the properties of Lemma 2.6.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Definition 2.1, p.11

import Mathlib
import Definitions.Def_ResultantVNP_ResultantSystem

namespace ResultantVNP

/-- **`Res(f₁, …, fₙ)` of given forms**: the resultant `Res_{d₁,…,dₙ}` evaluated at the coefficients
of `f₁, …, fₙ ∈ ℂ[x₁, …, xₙ]`, i.e. with each `u_{i,e}` replaced by the coefficient `[x^e] f_i`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Definition 2.1, p.11: "the notation Res(f₁, …, fₙ) means the evaluation of Res by replacing
each variable u_{i,𝒆} with the corresponding coefficient c_{i,𝒆} of f_i."

**Formalization Note** For a form `f_i` homogeneous of degree `d_i` the coefficients `[x^e] f_i` with
`|e| = d_i` are all its coefficients; statements using `resOf` assume this homogeneity. -/
noncomputable def resOf (𝓡 : ResultantSystem) {n : ℕ} (d : Fin n → ℕ)
    (f : Fin n → MvPolynomial (Fin n) ℂ) : ℂ :=
  MvPolynomial.eval (fun v : CoeffVar d => (f v.1).coeff v.2.1)
    (MvPolynomial.map (Int.castRingHom ℂ) (𝓡.res d))

end ResultantVNP


