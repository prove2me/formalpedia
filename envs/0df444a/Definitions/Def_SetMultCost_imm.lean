-- Prove2me | Definitions.Def_SetMultCost_imm
-- name    : SetMultCost_imm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:52:53.027186+00:00
-- url     : https://prove2.me/theorems/8d4963c8-6d9d-4450-bf2b-b219449e0844
-- title:
--   Iterated Matrix Multiplication $\mathrm{IMM}_{n,d}$
-- statement:
--   Let $X^{(1)},\dots,X^{(d)}$ be $n\times n$ matrices of $dn^2$ distinct variables, the matrices being the parts of the partition. The **Iterated Matrix Multiplication polynomial** is the $(1,1)$ entry of the product:
--
--   $$\mathrm{IMM}_{n,d}=\big(X^{(1)}X^{(2)}\cdots X^{(d)}\big)_{1,1}.$$
--
--   It is the explicit hard polynomial of the mission: set-multilinear of degree $d$ and computed by a small algebraic branching program.
--
--   **Formalization Note** A polynomial in `MvPolynomial`, with variables $(i,a,b)$ for the entry $(a,b)$ of $X^{(i)}$. Indices start at $0$, so the entry is $(0,0)$. All $dn^2$ variables are in the type even though some do not occur. At $n=0$ there is no such entry and the value is $0$; statements assume $n\ge1$.
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), §2, p.8

import Mathlib

namespace SetMultCost

/-- The `d n²` variables of `IMM_{n,d}`: `(i, a, b)` is the `(a, b)` entry of the matrix `X⁽ⁱ⁾`.
The part of a variable is its first coordinate, `Prod.fst`. -/
abbrev IMMVar (n d : ℕ) := Fin d × Fin n × Fin n

/-- **Iterated Matrix Multiplication.** Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), §2, p.8: "The polynomial IMMn,d is the (1, 1)th entry
of the matrix product X(1) · X(2) · · · X(d)", with `d` matrices, "each of dimension n × n" with
"n² distinct variable entries".

**Formalization Note.** A polynomial in `MvPolynomial`, over any commutative ring. Indices start at
`0`, so the `(1, 1)` entry is `(0, 0)`. `n = 0` has no such entry and returns `0`; every statement
assumes `n ≥ 1`. -/
noncomputable def imm (F : Type*) [CommRing F] (n d : ℕ) : MvPolynomial (IMMVar n d) F :=
  if h : 0 < n then
    (List.ofFn fun i : Fin d =>
      (Matrix.of fun a b : Fin n => (MvPolynomial.X (i, a, b) : MvPolynomial (IMMVar n d) F))).prod
      ⟨0, h⟩ ⟨0, h⟩
  else 0

end SetMultCost


