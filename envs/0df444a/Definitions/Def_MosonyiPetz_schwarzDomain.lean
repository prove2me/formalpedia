-- Prove2me | Definitions.Def_MosonyiPetz_schwarzDomain
-- name    : MosonyiPetz_schwarzDomain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:42:14.073111+00:00
-- url     : https://prove2.me/theorems/2e62f419-81be-4785-b1a8-02b85ccd4d98
-- title:
--   Schwarz-equality set $\{X: f(XX^*)=f(X)f(X^*),\ f(X^*X)=f(X^*)f(X)\}$
-- statement:
--   For a map $f:\mathcal B(\mathcal H)\to\mathcal B(\mathcal K)$ let
--
--   $$\mathcal A_f=\{X:\ f(XX^*)=f(X)f(X^*)\ \text{and}\ f(X^*X)=f(X^*)f(X)\}.$$
--
--   Lemma 1 uses $\mathcal A_{T^*}\subset\mathcal B(\mathcal K)$ and $\mathcal A_\alpha\subset\mathcal B(\mathcal H)$. For a unital 2-positive map this is its multiplicative domain (Choi).
--
--   **Formalization Note** $X^*$ is the conjugate transpose.
-- source:
--   Mosonyi–Petz, Structure of sufficient quantum coarse-grainings, arXiv:quant-ph/0312221v1, Lemma 1, p.8

import Mathlib

open scoped Matrix

namespace MosonyiPetz

/-- **The two-sided Schwarz-equality set of a map (A_{T*}, A_α in Lemma 1).**
Mosonyi–Petz, *Structure of sufficient quantum coarse-grainings*, arXiv:quant-ph/0312221v1, Lemma 1, p.8: "A_{T*} := {X ∈ B(K) : T*(XX*) = T*(X)T*(X*) and T*(X*X) = T*(X*)T*(X)}" and
"A_α := {A ∈ B(H) : α(AA*) = α(A)α(A*) and α(A*A) = α(A*)α(A)}".

`schwarzDomain f = {X | f (X * Xᴴ) = f X * f Xᴴ ∧ f (Xᴴ * X) = f Xᴴ * f X}`; the paper's sets are
`schwarzDomain T*` and `schwarzDomain α`.

**Formalization Note.** `X*` is the conjugate transpose `Xᴴ`. -/
def schwarzDomain {I J : Type*} [Fintype I] [Fintype J]
    (f : Matrix I I ℂ → Matrix J J ℂ) : Set (Matrix I I ℂ) :=
  {X | f (X * Xᴴ) = f X * f Xᴴ ∧ f (Xᴴ * X) = f Xᴴ * f X}

end MosonyiPetz


