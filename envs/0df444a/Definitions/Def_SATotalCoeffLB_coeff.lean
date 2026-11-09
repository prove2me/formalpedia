-- Prove2me | Definitions.Def_SATotalCoeffLB_coeff
-- name    : SATotalCoeffLB_coeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:18:55.716761+00:00
-- url     : https://prove2.me/theorems/e22df6dc-7df6-443a-a5d2-5d8612f9dcb9
-- title:
--   Coefficient of a multilinear monomial
-- statement:
--   For $f$ in the Boolean quotient ring over a finite set $V$ and $S \subseteq V$, the **coefficient of the monomial** $\prod_{v\in S} v$ in $f$ is
--
--   $$
--   \widehat f(S) = \frac{1}{2^{|V|}} \sum_{x \in \mathbb F_2^V} f(x) \prod_{v \in S} (-1)^{x_v}.
--   $$
--
--   Since the monomials are orthonormal for the uniform average over the cube, $f = \sum_{S \subseteq V} \widehat f(S) \prod_{v \in S} v$ is the unique multilinear representative of $f$, and $\widehat f(S)$ is its coefficient on $\prod_{v\in S} v$ (the Walsh–Fourier coefficient). Theorem 3 bounds these coefficients of every equation by $1/2$ in absolute value.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), p.9 (Theorem 3: coefficients of a multilinear polynomial), p.24 (Coefficient Norm)

import Mathlib
import Definitions.Def_SATotalCoeffLB_monomial

namespace SATotalCoeffLB

/-- **The coefficient of the multilinear monomial `∏_{v ∈ S} v`** in an element `f` of the Boolean
quotient ring (the coefficients of the multilinear polynomial `f`, p.9 and "Coefficient Norm",
p.24, of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178)):
`coeff f S = 2^{-|V|} ∑_{x} f(x) ∏_{v ∈ S} (-1)^{x v}`.

**Formalization Note** The monomials are orthonormal for the uniform average over the cube, so this
is the coefficient of `∏_{v∈S} v` in the unique multilinear representative of `f` (its
Walsh–Fourier coefficient in the `±1` basis). -/
noncomputable def coeff {V : Type*} [Fintype V] [DecidableEq V] (f : CubeFn V) (S : Finset V) : ℝ :=
  ((2 : ℝ) ^ Fintype.card V)⁻¹ * ∑ x : V → ZMod 2, f x * monomial S x

end SATotalCoeffLB


