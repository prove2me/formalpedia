-- Prove2me | Definitions.Def_BoundEntGauss_wwGamma
-- name    : BoundEntGauss_wwGamma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:48:26.15866+00:00
-- url     : https://prove2.me/theorems/a4b55255-521f-4496-ad71-4ea7c6ed43fd
-- title:
--   The five-parameter family of covariance matrices $\gamma(a,b,c,e,f)$
-- statement:
--   For real $a,b,c,e,f$ write $q=ce-a$. The covariance matrix $\gamma(a,b,c,e,f)$ of two modes for Alice and two for Bob, in coordinates $(x_1,p_1,x_2,p_2\mid x_3,p_3,x_4,p_4)$, is the real symmetric $8\times8$ matrix with diagonal
--
--   $$
--   \gamma_{11}=\gamma_{33}=\frac{bq+ef}{aq},\quad \gamma_{22}=\gamma_{44}=\frac ab,\quad \gamma_{55}=\gamma_{77}=\frac{cf}{q},\quad \gamma_{66}=\gamma_{88}=\frac{abe+bc+f}{abf},
--   $$
--
--   off-diagonal entries
--
--   $$
--   \gamma_{15}=\frac fq,\qquad \gamma_{37}=-\frac fq,\qquad \gamma_{28}=\gamma_{46}=-\frac1b
--   $$
--
--   (with their transposes), and all other entries zero. At $(a,b,c,e,f)=(1,1,2,1,1)$ it is the integer example (9).
--
--   The paper defines this matrix by a construction: with $d=(bc+f)/a$, apply $R$, $C$, $S$ and their products to $\Omega_1$ of Eq. (11) to obtain eight vectors $\Omega_k$, set $\Lambda_k=\gamma\Omega_k$ (known, since $\gamma$ commutes with $R,C,S$ and $(\gamma+i\sigma)\Omega_1=0$), and put $\gamma=\Lambda\Omega^{-1}$. The closed form above is the result of that construction; the milestone *family_construction* proves that it is the unique matrix meeting the construction's conditions.
--
--   **Formalization Note** The closed form is used instead of a matrix inverse, so that the definition is explicit and tied to (11) by a theorem. Entries divide by $a$, $b$, $abf$ and $q$; every statement about the family assumes $a,b,c,e,f>0$ and $a\ne ce$.
-- source:
--   Werner, Wolf, Bound entangled Gaussian states, arXiv:quant-ph/0009118v1, Section IV, Eq. (11), p. 4 (construction γ = ΛΩ⁻¹ described on p. 4 before Eq. (10))

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P68

open QAlgorithms.Papers.Independent.Intakenext100.P68 (CovarianceBlocks)

namespace BoundEntGauss

/-- **The five-parameter family of covariance matrices γ(a, b, c, e, f) of Section IV.**
Werner, Wolf, *Bound entangled Gaussian states*, arXiv:quant-ph/0009118v1, Section IV,
Eq. (11), p. 4.

Write `q = c·e − a`. In the coordinates `(x₁, p₁, x₂, p₂ | x₃, p₃, x₄, p₄)` the matrix
`γ(a, b, c, e, f)` is real symmetric with diagonal

  `γ₁₁ = γ₃₃ = (b·q + e·f)/(a·q)`, `γ₂₂ = γ₄₄ = a/b`,
  `γ₅₅ = γ₇₇ = c·f/q`, `γ₆₆ = γ₈₈ = (a·b·e + b·c + f)/(a·b·f)`,

off-diagonal entries `γ₁₅ = f/q`, `γ₃₇ = −f/q`, `γ₂₈ = γ₄₆ = −1/b` (and their transposes), and
all other entries zero. At `(a, b, c, e, f) = (1, 1, 2, 1, 1)` it is the integer matrix (9).

The paper defines this matrix through Ω₁ of (11): with `d = (b·c + f)/a`, the eight vectors
`Ω_k = T Ω₁` (`T` ranging over the products of `R`, `C`, `S`) form the columns of `Ω`, the vectors
`Λ_k = γ Ω_k = T γ Ω₁ = −i T σ Ω₁` (known because `γ` commutes with `T` and `(γ + iσ)Ω₁ = 0`) the
columns of `Λ`, and `γ = Λ Ω⁻¹`.

**Formalization Note.** Reading: the family is given in closed form. The closed form was computed
symbolically from the construction `γ = Λ Ω⁻¹` (planning evidence
`planning_numerics/explicit_check.out`), and the milestone `BoundEntGauss.family_construction`
states that it is the unique real symmetric matrix commuting with `R`, `C`, `S` and having
`Ω₁` in the null space of `γ + iσ`, together with `a·d = b·c + f`; so the definition is tied to (11)
by a theorem rather than trusted. `d` is eliminated by `d = (b·c + f)/a`. The entries divide by
`a`, `b`, `a·b·f` and `q`; every theorem about the family assumes `a, b, c, e, f > 0` and
`a ≠ c·e` (the goal `a < c·e`), so no division by zero occurs where it is used. Alice's block `A`,
Bob's block `B`, and the cross block `C` (rows Alice, columns Bob) are assembled by the published
`covarianceBlockMatrix` as `[[A, C], [Cᵀ, B]]`. -/
noncomputable def wwGamma (a b c e f : ℝ) : CovarianceBlocks 2 2 where
  A := Matrix.diagonal (fun p => ![(b * (c * e - a) + e * f) / (a * (c * e - a)), a / b] p.2)
  B := Matrix.diagonal (fun p => ![c * f / (c * e - a), (a * b * e + b * c + f) / (a * b * f)] p.2)
  C := fun p q =>
    if p = (0, 0) ∧ q = (0, 0) then f / (c * e - a)
    else if p = (1, 0) ∧ q = (1, 0) then -(f / (c * e - a))
    else if p = (0, 1) ∧ q = (1, 1) then -(1 / b)
    else if p = (1, 1) ∧ q = (0, 1) then -(1 / b)
    else 0

end BoundEntGauss


