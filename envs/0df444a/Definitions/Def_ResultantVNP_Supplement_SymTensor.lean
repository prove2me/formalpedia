-- Prove2me | Definitions.Def_ResultantVNP_Supplement_SymTensor
-- name    : ResultantVNP_Supplement_SymTensor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:55:51.721905+00:00
-- url     : https://prove2.me/theorems/a0ddeca7-d0a7-452c-bc52-1af0e4ca7748
-- title:
--   Integer symmetric cubic tensors, $\mathrm{Det}_n(A)$ and $\mathrm{Det}_n(A)\bmod 2^k$
-- statement:
--   An integer **symmetric cubic tensor** of dimension $n$ is given by one integer $a_{\{i,j,k\}}$ for each unordered triple of indices; its entry $a_{ijk}$ is the value at the triple $\{i,j,k\}$, so it does not change when the index positions are permuted. $\mathrm{Det}_n(A)\in\mathbb Z$ is the tensor determinant evaluated at these entries.
--
--   1. The **explicit binary code** of $A$ lists $n$ and then $a_{ijk}$ for all $i\le j\le k$ in signed binary.
--   2. The number of nonzero entries of $A$ is the number of triples $(i,j,k)\in[n]^3$ with $a_{ijk}\ne0$.
--   3. $\mathrm{DetMod}$ maps the word $\langle\mathrm{code}(A),1^k\rangle$, for $n\ge1$ and $k\ge1$, to $\mathrm{Det}_n(A)\bmod 2^k\in\{0,\dots,2^k-1\}$ written in binary, and every other word to the empty word.
--
--   These are the objects of Theorems 1.8, 1.11 and 4.6.
--
--   **Formalization Note** Unordered triples are size-3 multisets of `Fin n` (0-based). The determinant is the evaluation of the base mission's integral polynomial `symTensorDet`. Valid instances have $n\ge1$.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Section 4.1, p.19; Theorem 4.6 and Section 4.2, p.21; Theorem 1.11, p.7

import Mathlib
import Definitions.Def_ResultantVNP_symTensorDet
import Definitions.Def_ResultantVNP_Supplement_Reductions

set_option autoImplicit false

namespace ResultantVNP

namespace Supplement

open ApproxPolySatCH.Main

/-- **Explicitly encoded integer symmetric cubic tensors, their determinant `Det_n(A) ∈ ℤ`, the
number of nonzero entries, and the modular function `DetMod`.**

A symmetric cubic tensor of dimension `n` is given by one integer per unordered triple of indices
`{i, j, k}` (`Sym (Fin n) 3`); its entry `a_{ijk}` is the value at the triple `{i, j, k}`, so it is
unchanged by permuting the index positions. `Det_n(A)` is the evaluation of the integral polynomial
`symTensorDet 𝓡 n` at these entries.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real
Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Section 4.1, p.19
("Det_n(C) mod 2^k ∈ {0, …, 2^k − 1}, where C is an integer symmetric cubic tensor of dimension n
with binary-encoded entries, and k ≥ 1 is supplied in unary"), Theorem 4.6 and Section 4.2, p.21,
Theorem 1.11, p.7.

**Formalization Note** Code: `encodeNat n`, then for `i ≤ j ≤ k < n` (lexicographic) the signed
binary `encodeInt` of `a_{ijk}`, one entry per unordered triple. Valid instances have `n ≥ 1`. -/
structure SymTensor where
  n : ℕ
  a : Sym (Fin n) 3 → ℤ

/-- The entry `a_{ijk}` of the symmetric tensor. -/
def SymTensor.entry (A : SymTensor) (i j k : Fin A.n) : ℤ :=
  A.a (i ::ₛ j ::ₛ k ::ₛ Sym.nil)

/-- `Det_n(A) ∈ ℤ`. -/
noncomputable def SymTensor.det (𝓡 : ResultantSystem) (A : SymTensor) : ℤ :=
  MvPolynomial.eval A.a (symTensorDet 𝓡 A.n)

/-- The number of nonzero entries `a_{ijk}` of the `n × n × n` array. -/
def SymTensor.nonzeroEntries (A : SymTensor) : ℕ :=
  (Finset.univ.filter (fun t : Fin A.n × Fin A.n × Fin A.n => A.entry t.1 t.2.1 t.2.2 ≠ 0)).card

/-- Binary code of a symmetric tensor: `n`, then `a_{ijk}` for `i ≤ j ≤ k`. -/
def SymTensor.encode (A : SymTensor) : Word :=
  encodeNat A.n ++ (List.finRange A.n).flatMap (fun i =>
    ((List.finRange A.n).filter (fun j => decide (i ≤ j))).flatMap (fun j =>
      ((List.finRange A.n).filter (fun k => decide (j ≤ k))).flatMap (fun k =>
        encodeInt (A.entry i j k))))

/-- `DetMod(A, 1^k) = Det_n(A) mod 2^k ∈ {0, …, 2^k − 1}` in binary (`Nat.bits`), on the words
`⟨code A, 1^k⟩` with `n ≥ 1` and `k ≥ 1`; every other word is mapped to `[]`. -/
noncomputable def DetMod (𝓡 : ResultantSystem) (w : Word) : Word := by
  classical
  exact if h : ∃ (A : SymTensor) (k : ℕ), 1 ≤ A.n ∧ 1 ≤ k ∧
      w = pairW A.encode (List.replicate k true) then
    (Int.toNat (SymTensor.det 𝓡 (Classical.choose h) %
      2 ^ (Classical.choose (Classical.choose_spec h)))).bits
  else []

end Supplement

end ResultantVNP


