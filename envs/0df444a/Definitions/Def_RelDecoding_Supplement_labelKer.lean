-- Prove2me | Definitions.Def_RelDecoding_Supplement_labelKer
-- name    : RelDecoding_Supplement_labelKer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:11:22.021234+00:00
-- url     : https://prove2.me/theorems/d838140c-c865-4ab5-9ec9-22e7d33e6c35
-- title:
--   Label matrix $A=[w_1\cdots w_s]$, relation code $K_A=\ker A$ and ordered products $W(c)$
-- statement:
--   Let $K$ be a field and let $w_1,\dots,w_s$ be **labels** of the marked generators, vectors in $K^\kappa$ for a finite coordinate set $\kappa$.
--
--   1. The **label matrix** is $A=[w_1\cdots w_s]$, the $\kappa\times s$ matrix whose $i$-th column is $w_i$.
--   2. The **relation code** is $K_A=\ker A=\{c\in K^s:\ \sum_i c_i w_i=0\}$.
--   3. A label $(x,z)\in K^n\times K^n$ is read as the column vector $(x,z)\in K^{2n}$, $x$-part first.
--   4. For matrices $a_1,\dots,a_s$ and $c\in(\mathbb Z/q)^s$ the **ordered product** is
--   $$W(c)=a_1^{c_1}\cdots a_s^{c_s},$$
--   with factors in increasing index order and exponents the representatives $c_i\in\{0,\dots,q-1\}$.
--
--   These are the objects of eqs. (81)–(82), (153)–(154) and (254): $K_A$ records which ordered products of the marked terms are scalar, and $W_L(c)=\zeta_L(c)I$ for $c\in K_L$ defines their phases. Here $K=\mathbb F_2$ for Pauli and Majorana labels and $K=\mathbb F_p$ for Weyl labels.
--
--   **Formalization Note** The kernel is `LinearMap.ker` of `Matrix.mulVecLin`. The empty ordered product is the identity.
-- source:
--   Shang, Stilck França, From Simple Sources to Quantum Advantage: Homomorphic Polynomial Transduction via Relative Decoding, arXiv:2609.35101 (held version, sha256 d2be7859…), eqs. (81)–(82), p.23; (153)–(154), p.35; (254), p.46 (pdf_pages 23, 35, 46)

import Mathlib

set_option autoImplicit false

namespace RelDecoding.Supplement

/-- The **label matrix** `A = [w₁ ⋯ w_s]` whose `i`-th column is the label `wᵢ ∈ K^κ` of the
`i`-th marked generator. Shang, Stilck França, *From Simple Sources to Quantum Advantage:
Homomorphic Polynomial Transduction via Relative Decoding*, arXiv:2609.35101 (held version, sha256
d2be7859…), eqs. (81), (153), (254), pp.23, 35, 46.

**Formalization Note.** The field `K` is `ZMod 2` for Pauli and Majorana labels and `ZMod p` for
Weyl labels; the row index type `κ` is the label coordinate set. -/
def labelMatrix {K κ : Type*} {s : ℕ} (w : Fin s → κ → K) : Matrix κ (Fin s) K :=
  Matrix.of fun k i => w i k

/-- The **relation code** `K_A = ker A ⊆ K^s` of the label matrix `A = [w₁ ⋯ w_s]`: the vectors
`c` with `Σᵢ cᵢ wᵢ = 0`. Shang, Stilck França, arXiv:2609.35101 (held version, sha256 d2be7859…),
eqs. (81), (153), (254), pp.23, 35, 46. -/
def labelKer {K κ : Type*} [Field K] {s : ℕ} (w : Fin s → κ → K) : Submodule K (Fin s → K) :=
  LinearMap.ker (labelMatrix w).mulVecLin

/-- A label `(x, z) ∈ K^n × K^n` read as the column vector `(x, z) ∈ K^{2n}`, X-part first
(the coordinates `Fin n ⊕ Fin n`). Used for Pauli labels (`K = F₂`, eq. (77)) and Weyl labels
(`K = F_p`, eq. (226)). -/
def pairVec {K : Type*} {n : ℕ} (u : (Fin n → K) × (Fin n → K)) : Fin n ⊕ Fin n → K :=
  Sum.elim u.1 u.2

/-- The **ordered product** `W(c) = a₁^{c₁} ⋯ a_s^{c_s}` of a family of matrices `a₁, …, a_s`
for a label vector `c ∈ (ℤ/q)^s`, with factors in increasing index order and exponents the
representatives `cᵢ ∈ {0, …, q − 1}`. Shang, Stilck França, arXiv:2609.35101 (held version, sha256
d2be7859…), eqs. (82), (154), pp.23, 35 (with `q = 2`, so `cᵢ ∈ {0, 1}`).

**Formalization Note.** The empty product (`s = 0`) is the identity. -/
def orderedProd {N : Type*} [Fintype N] [DecidableEq N] {s q : ℕ}
    (a : Fin s → Matrix N N ℂ) (c : Fin s → ZMod q) : Matrix N N ℂ :=
  (List.ofFn fun i => a i ^ (c i).val).prod

end RelDecoding.Supplement


