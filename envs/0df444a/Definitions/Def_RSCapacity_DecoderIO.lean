-- Prove2me | Definitions.Def_RSCapacity_DecoderIO
-- name    : RSCapacity_DecoderIO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:27:51.419561+00:00
-- url     : https://prove2.me/theorems/643d437c-7c97-4398-b14a-ba8413c83bdc
-- title:
--   Input and output layout of the decoders on the algebraic RAM
-- statement:
--   The paper counts **field operations** and names no machine. The machine is the published algebraic RAM over a field $F$ (definition `MatroidSensOracle_AlgRAM`): word cells holding $w$-bit words and field cells holding elements of $F$, every executed instruction costing one step. This definition fixes how instances are written into memory and how the output is read.
--
--   1. **List recovery** (Theorem 1.1): word cells $[n,k,A,|S_1|,\dots,|S_n|]$; field cells $[\alpha_1,\dots,\alpha_n]$ followed by the elements of $S_1,\dots,S_n$, each list duplicate-free and in some order.
--   2. **Sparse list recovery** (Theorem 5.4): word cells $[n,k,A,K,r,|S_1|,\dots,|S_n|]$ and the same field cells.
--   3. **Differential equation** (Theorem 5.2): word cells $[r,K,t]$ followed by the exponent vectors (length $r+2$ each) of the $t$ monomials of $Q$; field cells the $t$ nonzero coefficients in the same order. Any order of the monomials is a valid input.
--   4. **Output**: at halt, word cell $0$ holds the number $N$ of output polynomials and field cell $jk+a$ ($0\le j<N$, $0\le a<k$) holds the coefficient of $X^a$ of the $j$-th one. The machine **outputs exactly** a set $\mathcal L$ when the decoded list has no repetitions and its members are exactly the elements of $\mathcal L$.
--
--   **Formalization Note** Words are read as integers (`BitVec.ofInt`), and $N$ is read unsigned. The agreement threshold $A$ is an input word, as in Definition 3.1.
-- source:
--   Jeronimo, Algorithmic List Decoding at Capacity and Optimal Proximity Gaps for Reed–Solomon Codes, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), Theorem 1.1, pp.1–2 (PDF 3–4); Definition 3.1, p.11 (PDF 13); Theorems 5.2 and 5.4, p.21 (PDF 23)

import Mathlib

open Polynomial

set_option autoImplicit false

namespace RSCapacity

/-!
# Input and output layout of the decoders on the algebraic RAM

Jeronimo, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…): Theorem 1.1,
pp.1–2 (PDF 3–4), Theorem 5.2, p.21 (PDF 23), Theorem 5.4, p.21 (PDF 23). The paper counts "field
operations" and names no machine; the machine is the published algebraic RAM
`MatroidSensOracle.aexec` (definition `MatroidSensOracle_AlgRAM`), whose memory is a pair of a
word memory `ℤ → BitVec w` and a field memory `ℤ → F`. This module fixes how an instance is
written into that memory and how the output list is read from it.

**Formalization Note.**
* **List-recovery input** (Theorem 1.1): word cells `[n, k, A, |S_1|, …, |S_n|]`; field cells
  `[α_1, …, α_n] ++ S_1 ++ ⋯ ++ S_n`. Each list is given as a duplicate-free `List F` (some order of
  the set S_i; the theorems quantify over every order). The agreement threshold A is an input
  word, as in Definition 3.1 ("an agreement threshold A").
* **Sparse list recovery input** (Theorem 5.4): word cells `[n, k, A, K, r, |S_1|, …, |S_n|]`,
  the same field cells.
* **Differential-equation input** (Theorem 5.2): word cells `[r, K, t]` followed by the exponent
  vectors (each of length r + 2) of the t monomials of Q, and field cells holding the t
  coefficients, in the same order. `SparseRep ts Q` says that `ts` lists the support of `Q` with
  its coefficients, in some order.
* **Output**: at halt, word cell 0 holds the number N of output polynomials (read unsigned) and the
  field cells `j·k + a` (0 ≤ j < N, 0 ≤ a < k) hold the coefficient of X^a of the j-th output
  polynomial. `OutputsExactly k st L` says the decoded list has no repetitions and its members are
  exactly the elements of `L`.
-/

/-- Word cells of a list-recovery instance: `[n, k, A, |S_1|, …, |S_n|]`. -/
def listInstanceWords {F : Type*} {n : ℕ} (k A : ℕ) (S : Fin n → List F) : List ℤ :=
  [(n : ℤ), (k : ℤ), (A : ℤ)] ++ (List.finRange n).map fun i => ((S i).length : ℤ)

/-- Word cells of a sparse list-recovery instance with parameters K, r (Theorem 5.4):
`[n, k, A, K, r, |S_1|, …, |S_n|]`. -/
def sparseInstanceWords {F : Type*} {n : ℕ} (k A K r : ℕ) (S : Fin n → List F) : List ℤ :=
  [(n : ℤ), (k : ℤ), (A : ℤ), (K : ℤ), (r : ℤ)] ++
    (List.finRange n).map fun i => ((S i).length : ℤ)

/-- Field cells of a list-recovery instance: `[α_1, …, α_n] ++ S_1 ++ ⋯ ++ S_n`. -/
def listInstanceFields {F : Type*} {n : ℕ} (α : Fin n → F) (S : Fin n → List F) : List F :=
  (List.finRange n).map α ++ (List.finRange n).flatMap S

/-- `ts` lists the monomials of `Q` with their coefficients: distinct exponent vectors, nonzero
coefficients, and `Q = ∑ c X^e`. Any order is allowed. -/
def SparseRep {F : Type*} [Field F] {ι : Type*} (ts : List ((ι →₀ ℕ) × F))
    (Q : MvPolynomial ι F) : Prop :=
  (ts.map Prod.fst).Nodup ∧ (∀ t ∈ ts, t.2 ≠ 0) ∧
    Q = (ts.map fun t => MvPolynomial.monomial t.1 t.2).sum

/-- Word cells of a differential-equation instance (Theorem 5.2): `[r, K, t]` followed by the
exponent vectors of the t monomials, each written as its r + 2 entries. -/
def diffEqWords {F : Type*} (r K : ℕ) (ts : List ((Fin (r + 2) →₀ ℕ) × F)) : List ℤ :=
  [(r : ℤ), (K : ℤ), (ts.length : ℤ)] ++
    ts.flatMap fun t => (List.finRange (r + 2)).map fun j => ((t.1 j : ℕ) : ℤ)

/-- The list of polynomials of degree below `k` written in a halted memory: word cell 0 holds
their number N, field cell `j·k + a` the coefficient of X^a of the j-th polynomial. -/
noncomputable def decodedList {F : Type*} [Field F] {w : ℕ} (k : ℕ)
    (st : (ℤ → BitVec w) × (ℤ → F)) : List F[X] :=
  (List.range (st.1 0).toNat).map fun j =>
    ∑ a ∈ Finset.range k, C (st.2 ((j * k + a : ℕ) : ℤ)) * X ^ a

/-- The halted memory `st` outputs exactly the set `L`: the decoded list has no repetitions and
its members are the elements of `L`. -/
def OutputsExactly {F : Type*} [Field F] {w : ℕ} (k : ℕ) (st : (ℤ → BitVec w) × (ℤ → F))
    (L : Set F[X]) : Prop :=
  (decodedList k st).Nodup ∧ ∀ P : F[X], P ∈ decodedList k st ↔ P ∈ L

end RSCapacity


