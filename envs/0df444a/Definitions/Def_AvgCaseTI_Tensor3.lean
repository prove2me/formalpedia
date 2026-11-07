-- Prove2me | Definitions.Def_AvgCaseTI_Tensor3
-- name    : AvgCaseTI_Tensor3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:41:25.5027+00:00
-- url     : https://prove2.me/theorems/4f803fa5-259d-4226-ae87-67c1df70048d
-- title:
--   3-way arrays $T(n\times n\times n,q)$ and the bilinear map $g_A$
-- statement:
--   A **3-way array** $A=(a_{i,j,k})\in T(n\times n\times n,\mathbb F)$ has entries $a_{i,j,k}\in\mathbb F$ for $i,j,k\in[n]$. It is the table of **structure constants** of the bilinear map $g_A:\mathbb F^n\times\mathbb F^n\to\mathbb F^n$ defined on basis vectors by
--   $$
--   g_A(e_i,e_j)=\sum_{k\in[n]}a_{i,j,k}\,e_k,\qquad\text{so}\qquad g_A(x,y)_k=\sum_{i,j}x_i\,y_j\,a_{i,j,k}.
--   $$
--   An element of $U\otimes U\otimes U^*$ with $U\cong\mathbb F_q^n$ is, after fixing a basis, such an array: it is the multiplication of an $n$-dimensional algebra over $\mathbb F_q$. No associativity, commutativity or unit is assumed.
--
--   **Formalization Note** Indices run over `Fin n`; `A i j k` is $a_{i,j,k}$ and `mulMap A x y` is $g_A(x,y)$.
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), §3.1, p.16 (PDF p.18); §2.3, p.15 (PDF p.17)

import Mathlib

set_option autoImplicit false

namespace AvgCaseTI

/-- **3-way arrays and the bilinear map they represent.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), §3.1, p.16 (PDF p.18):
"A is represented by its structure constants, that is, … a 3-way array A = (a_{i,j,k}) ∈ T(n × n × n, q),
so the bilinear map g_A : F_q^n × F_q^n → F_q^n represented by A is defined by
g_A(e_i, e_j) = Σ_{k∈[n]} a_{i,j,k} e_k."

`Tensor3 K n` is the space of `n × n × n` arrays over `K`, with `A i j k = a_{i,j,k}`.

**Formalization Note.** Indices run over `Fin n`. No associativity, commutativity or unit is
assumed (p.2: "We shall not assume these conditions"). -/
abbrev Tensor3 (K : Type*) (n : ℕ) := Fin n → Fin n → Fin n → K

/-- The multiplication `g_A(x, y) = Σ_{i,j} x_i y_j Σ_k a_{i,j,k} e_k` of the algebra with structure
constants `A` (§3.1, p.16). -/
def mulMap {K : Type*} [CommRing K] {n : ℕ} (A : Tensor3 K n) (x y : Fin n → K) : Fin n → K :=
  fun k => ∑ i, ∑ j, x i * y j * A i j k

end AvgCaseTI


