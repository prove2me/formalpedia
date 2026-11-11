-- Prove2me | Definitions.Def_ChowFormsCH_gcdOutputPoly
-- name    : ChowFormsCH_gcdOutputPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:20.228386+00:00
-- url     : https://prove2.me/theorems/d0524ee9-4fae-45d6-97e6-05807cde7dc0
-- title:
--   Input and output layout of the GCD circuits of Lemma 2.13
-- statement:
--   The GCD circuit with index $(m,d,h)$ takes as input the coefficients of two polynomials $f,g\in\mathbb Z[x_1,\dots,x_m]$ of degree at most $d$ (the $\binom{d+m}{d}$ monomials of degree at most $d$, in a fixed order), followed by $m-1$ integers $a_2,\dots,a_m$; every integer uses a sign bit and $h+1$ magnitude bits. Its output is the list of the $\binom{d+m}{d}$ coefficients of a polynomial $h$ of degree at most $d$, each an integer with a sign bit and $w$ magnitude bits.
--
--   **Formalization Note** The bit length $h$ of the input integers is implicit in the paper and is made an index; the output width $w$ is chosen by the family and computable from the index.
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), Lemma 2.13, p.15

import Mathlib
import Definitions.Def_ChowFormsCH_expList

set_option autoImplicit false

namespace ChowFormsCH

/-- The input bits of the GCD circuit of Lemma 2.13 with index `(m, d, h)`
(Andrews–Garg–Oliveira–Schost, *Some algebraic and geometric computations in CH via Chow forms*,
arXiv:2611.05289, held version, sha256 75e796c6…, Lemma 2.13, p.15: "The circuits take as input
2·C(d+m, d) integers representing the coefficients of two m-variate polynomials of degree d with
integer coefficients f, g. The circuits also take as input m − 1 integers, denoted a2, . . . , am."):
the coefficients of `f`, then those of `g` (monomials of degree at most `d` in the order of
`expList m d`), then `a₂, …, a_m`; every integer with `h + 1` magnitude bits (`intBits`).

**Formalization Note** The bit length of the integers is implicit in the paper; it is the index
`h` (integers of height at most `h`). -/
def gcdInput (m d h : ℕ) (fc gc : Fin (expList m d).length → ℤ) (a : Fin (m - 1) → ℤ) :
    List Bool :=
  (List.ofFn fun j : Fin (expList m d).length => intBits (h + 1) (fc j)).flatten
    ++ (List.ofFn fun j : Fin (expList m d).length => intBits (h + 1) (gc j)).flatten
    ++ (List.ofFn fun e : Fin (m - 1) => intBits (h + 1) (a e)).flatten

/-- The number of input bits of the GCD circuit, the length of `gcdInput`. -/
def gcdInputLength (m d h : ℕ) : ℕ := (2 * (expList m d).length + (m - 1)) * (h + 2)

/-- The output polynomial `h ∈ ℤ[x₁, …, x_m]` of degree at most `d` of the GCD circuit (Lemma 2.13,
p.15: "The circuits computes C(d+m, d) integers representing an m-variate polynomial h of degree at
most d"), read from the output bits `y`: coefficient `j` (order of `expList m d`) is the integer in
bits `j(w+1), …, j(w+1) + w` (`intBits` format), `w` chosen by the family. -/
noncomputable def gcdOutputPoly (m d w : ℕ) (y : ℕ → Bool) : MvPolynomial (Fin m) ℤ :=
  densePoly m d (fun j => decodeInt w y ((j : ℕ) * (w + 1)))

end ChowFormsCH


