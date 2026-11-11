-- Prove2me | Definitions.Def_ChowFormsCH_liftOutputPoly
-- name    : ChowFormsCH_liftOutputPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:13.254068+00:00
-- url     : https://prove2.me/theorems/b5178f60-95fa-44b9-821f-906f8e3d344c
-- title:
--   Input and output layout of the factor-lifting circuits of Lemma 2.18
-- statement:
--   The lifting circuit with index $(d,m,e,k,h)$ takes as input the $\binom{d+m+1}{d}\binom{e+k}{e}$ coefficients of a polynomial $P\in\mathbb Z[w_1,\dots,w_k][y,x_1,\dots,x_m]$ of degree at most $e$ in $w$ and at most $d$ in $(y,x)$, then the $(d+1)\binom{e+k}{k}$ coefficients of $Q\in\mathbb Z[w_1,\dots,w_k][y]$ of degree at most $e$ in $w$ and at most $d$ in $y$; every integer uses a sign bit and $h+1$ magnitude bits. Its output is the list of the $\binom{d+m+1}{d}\binom{e+k}{e}$ coefficients of a polynomial $R$ of the same shape as $P$, each with a sign bit and $w$ magnitude bits.
--
--   **Formalization Note** The variables are $w_1,\dots,w_k$ and $y,x_1,\dots,x_m$ (in Lean: `Sum.inl` for $w$, `Sum.inr 0` for $y$). The bit length $h$ is made an index; the output width $w$ is chosen by the family and computable from the index.
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), Lemma 2.18, p.18

import Mathlib
import Definitions.Def_ChowFormsCH_expList

set_option autoImplicit false

namespace ChowFormsCH

/-- The polynomial `P ∈ R[w₁, …, w_k][y, x₁, …, x_m]` with coefficient data `c β γ` on the monomial
`(y, x)^β · w^γ`, `β` of degree at most `d` in `(y, x₁, …, x_m)` (order of `expList (m+1) d`) and `γ`
of degree at most `e` in `w` (order of `expList k e`) (Andrews–Garg–Oliveira–Schost, *Some algebraic
and geometric computations in CH via Chow forms*, arXiv:2611.05289, held version, sha256 75e796c6…,
Lemma 2.18, p.18).

**Formalization Note** The variables are `w₁, …, w_k` (`Sum.inl`) and `y, x₁, …, x_m` (`Sum.inr 0`
is `y`, `Sum.inr (j+1)` is `x_{j+1}`). -/
noncomputable def liftPoly {R : Type*} [CommSemiring R] (k m d e : ℕ)
    (c : Fin (expList (m + 1) d).length → Fin (expList k e).length → R) :
    MvPolynomial (Fin k ⊕ Fin (m + 1)) R :=
  ∑ β : Fin (expList (m + 1) d).length, ∑ γ : Fin (expList k e).length,
    MvPolynomial.monomial
      (expToFinsupp (Sum.elim ((expList k e).get γ) ((expList (m + 1) d).get β))) (c β γ)

/-- The polynomial `Q ∈ R[w₁, …, w_k][y]` with coefficient data `c i γ` on `y^i · w^γ`, `0 ≤ i ≤ d`,
`γ` of degree at most `e` in `w` (Lemma 2.18, p.18), in the variables of `liftPoly`. -/
noncomputable def liftQPoly {R : Type*} [CommSemiring R] (k m d e : ℕ)
    (c : Fin (d + 1) → Fin (expList k e).length → R) : MvPolynomial (Fin k ⊕ Fin (m + 1)) R :=
  ∑ i : Fin (d + 1), ∑ γ : Fin (expList k e).length,
    MvPolynomial.monomial
      (expToFinsupp (Sum.elim ((expList k e).get γ) (Pi.single (0 : Fin (m + 1)) (i : ℕ)))) (c i γ)

/-- The input bits of the lifting circuit of Lemma 2.18 with index `(d, m, e, k, h)` (p.18: "The
circuit takes as input C(d+m+1, d) · C(e+k, e) integers, representing the coefficients of a
polynomial P … The circuit also takes as input (d + 1) · C(e+k, k) integers, representing the
coefficients of a polynomial Q"): the coefficients of `P` (outer loop over `β`, inner over `γ`),
then those of `Q` (outer loop over `i`, inner over `γ`), each with `h + 1` magnitude bits.

**Formalization Note** The bit length of the integers is implicit in the paper; it is the index
`h`. -/
def liftInput (k m d e h : ℕ) (pc : Fin (expList (m + 1) d).length → Fin (expList k e).length → ℤ)
    (qc : Fin (d + 1) → Fin (expList k e).length → ℤ) : List Bool :=
  (List.ofFn fun β : Fin (expList (m + 1) d).length =>
      (List.ofFn fun γ : Fin (expList k e).length => intBits (h + 1) (pc β γ)).flatten).flatten
    ++ (List.ofFn fun i : Fin (d + 1) =>
      (List.ofFn fun γ : Fin (expList k e).length => intBits (h + 1) (qc i γ)).flatten).flatten

/-- The number of input bits of the lifting circuit, the length of `liftInput`. -/
def liftInputLength (k m d e h : ℕ) : ℕ :=
  ((expList (m + 1) d).length + (d + 1)) * (expList k e).length * (h + 2)

/-- The output polynomial `R` of the lifting circuit (Lemma 2.18, p.18: "C(d+m+1, d) · C(e+k, e)
integers representing … R of degree at most d in y, x1, . . . , xm and at most e in w1, . . . , wk"),
read from the output bits `y`: coefficient `(β, γ)` is the integer in bits
`(β · |γ-list| + γ)(w+1), …` (`intBits` format, `w` chosen by the family), in the variables of
`liftPoly`. -/
noncomputable def liftOutputPoly (k m d e w : ℕ) (y : ℕ → Bool) :
    MvPolynomial (Fin k ⊕ Fin (m + 1)) ℤ :=
  liftPoly k m d e (fun β γ =>
    decodeInt w y (((β : ℕ) * (expList k e).length + (γ : ℕ)) * (w + 1)))

end ChowFormsCH


