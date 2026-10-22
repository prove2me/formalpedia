-- Prove2me | Definitions.Def_QMaxCutSDP_Rounding_Pauli
-- name    : QMaxCutSDP_Rounding_Pauli
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:46.425218+00:00
-- url     : https://prove2.me/theorems/b78fe56e-62b3-43d4-b71e-7949f963a1bb
-- title:
--   Definitions 1 and 3 — Pauli matrices, strings, and weight
-- statement:
--   A Pauli string chooses one of $I$, $X$, $Y$, and $Z$ for each of $n$ qubits and acts by their tensor product. Its weight is the number of nonidentity choices. The index set $P_n(k)$ contains exactly the strings of weight at most $k$, including the identity string.
--
--   $$P_n(k)=\{s:\{0,\ldots,n-1\}\to\{I,X,Y,Z\}:\operatorname{weight}(s)\le k\}.$$
--
--   This standalone definition supplies the general Pauli representation used by the paper's Quantum Max Cut Hamiltonian and Lasserre matrix.
--
--   **Formalization Note** The basis is indexed by `Fin n → Fin 2`; the label 0 is $I$, 1 is $X$, 2 is $Y$, and 3 is $Z$. The matrix of a string is the product of its one-qubit entries, equivalent to its tensor product after fixing the basis ordering.
-- source:
--   Lee, Optimizing quantum circuit parameters via SDP, arXiv:2209.00789v1, p. 2, Definition 1; p. 3, Definition 3

import Mathlib

open Matrix

namespace QMaxCutSDP.Rounding

abbrev BitString (n : ℕ) := Fin n → Fin 2
abbrev State (n : ℕ) := BitString n → ℂ
abbrev Operator (n : ℕ) := Matrix (BitString n) (BitString n) ℂ

/-- Definition 1, p. 2. Indices 0,1,2,3 name I,X,Y,Z. -/
def pauli (a : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  if a = 0 then !![1, 0; 0, 1]
  else if a = 1 then !![0, 1; 1, 0]
  else if a = 2 then !![0, -Complex.I; Complex.I, 0]
  else !![1, 0; 0, -1]

def pauliString {n : ℕ} (s : Fin n → Fin 4) : Operator n :=
  fun x y => ∏ i : Fin n, pauli (s i) (x i) (y i)

def pauliPairString {n : ℕ} (a : Fin 4) (i j : Fin n) : Fin n → Fin 4 :=
  fun t => if t = i ∨ t = j then a else 0

def pauliAt {n : ℕ} (a : Fin 4) (i : Fin n) : Operator n :=
  pauliString (fun t => if t = i then a else 0)

/-- Definition 3, p. 3. The zero string is the identity. -/
def weight {n : ℕ} (s : Fin n → Fin 4) : ℕ :=
  (Finset.univ.filter fun i => s i ≠ 0).card

def PIndex (n k : ℕ) := {s : Fin n → Fin 4 // weight s ≤ k}

end QMaxCutSDP.Rounding


