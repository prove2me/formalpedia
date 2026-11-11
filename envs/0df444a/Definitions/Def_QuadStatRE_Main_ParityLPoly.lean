-- Prove2me | Definitions.Def_QuadStatRE_Main_ParityLPoly
-- name    : QuadStatRE_Main_ParityLPoly
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:44:37.665949+00:00
-- url     : https://prove2.me/theorems/2730a8ac-d243-440f-9dc0-c99884fd9b2b
-- title:
--   $\oplus\mathsf L/\mathsf{poly}$ function families and the parameters $(n,\lambda)$ (footnote 1, §2.5)
-- statement:
--   A **function family** $f=\{f_n\}$, $f_n:\{0,1\}^n\to\{0,1\}^{\ell(n)}$, is in $\oplus\mathsf L/\mathsf{poly}$ (footnote 1, p. 2) when each output bit of $f_n$ is computed by a polynomial-size **mod-2 branching program** (a directed acyclic graph with edges labelled by literals or $1$, whose output is the parity of the number of source–sink paths whose labels all evaluate to one) and these programs can be generated in time polynomial in $n$. Here such a family is given by a generator $n\mapsto \mathrm{gen}(n)$, a list of mod-2 branching programs on $n$ variables (the published `QuadraticRE.Rep`), together with one fixed Turing machine that computes the bit encoding of $\mathrm{gen}(n)$ from $1^n$ in time polynomial in $n$; then $f_n=\mathrm{gen}(n).\mathrm{eval}$ and $\ell(n)$ is the number of programs.
--
--   With a security parameter, the public parameters of an encoding are the pair $(n,\lambda)$, $n,\lambda\in\mathbb N$ (§2.5, p. 15: "the same uniformity and efficiency requirements apply jointly to $n$ and $\lambda$"), presented to machines as $1^n0\,1^\lambda0$; time polynomial in this string's length is time polynomial in $n$ and $\lambda$.
--
--   **Formalization Note.** The published branching programs have no parallel edges; subdividing an edge does not change the class. Every $\lambda\in\mathbb N$ is allowed, including $\lambda=0$ (the published `QuadraticRE.Param` forces $\lambda\ge1$ and is not used).
-- source:
--   Applebaum, Quadratic Statistical Randomized Encoding for All Functions, STOC 2027 submission (manuscript sha256 000cbf4e…), p. 2, footnote 1; p. 15, §2.5

import Mathlib
import Definitions.Def_QuadraticRE_PolyTimeFn

namespace QuadStatRE.Main

open QuadraticRE

/-- A function family in `⊕L/poly` (Applebaum, *Quadratic Statistical Randomized Encoding for All
Functions*, STOC 2027 submission, footnote 1, p. 2): `f_n : {0,1}^n → {0,1}^{ℓ(n)}` with "each output
bit computed by a polynomial-size branching program" with the parity acceptance condition, and
"these branching programs can be generated in time polynomial in the input length `n`".

`gen n` is the list of mod-2 branching programs for `f_n` (one per output bit), on `n` input
variables; `poly` is one fixed machine that maps `1^n` to the token encoding of `gen n` in time
polynomial in `n` (which also bounds the programs' size by a polynomial). The function is
`f_n = (gen n).eval`. -/
structure ParityLPolyFamily where
  gen : ℕ → Rep
  hN : ∀ n, (gen n).N = n
  poly : PolyTimeFn encNat (fun n => encTokens (repTokens (gen n)))

/-- The public parameters `(n, λ)` of a family of encodings with a security parameter (§2.5, p. 15:
"the same uniformity and efficiency requirements apply jointly to `n` and `λ`"). Every `λ ∈ ℕ` is
allowed, including `λ = 0`. -/
structure NLam where
  n : ℕ
  lam : ℕ

/-- The bit encoding of `(n, λ)`: `1^n 0 1^λ 0`, both numbers in unary, so that "time polynomial in
`n` and `λ`" is time polynomial in the length of this string. -/
def encNLam (p : NLam) : List Bool := encNat p.n ++ encNat p.lam

end QuadStatRE.Main


