-- Prove2me | Definitions.Def_UnifLattice_FastVf_Encoding
-- name    : UnifLattice_FastVf_Encoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T07:20:08.402219+00:00
-- url     : https://prove2.me/theorems/ae86bba4-29db-4d5a-bdda-d17f80a65b10
-- title:
--   Bit-string encodings of the inputs (pp, BP_g, m, indices) and outputs (integer matrices) of the algorithms of Lemmas 3.10, 3.12 and Theorem 3.13
-- statement:
--   The paper's algorithms are measured in the length of their input (p. 16: efficient means polynomial time in the length of the input). To state their running times, inputs and outputs are bit strings:
--
--   - $m$, $\ell$, $w$ are written in unary, so each is at most the input length;
--   - $W$, $V$ and every $M_{\tau,b}$ are written one bit per entry, in lexicographic order of the index;
--   - the reading order $\pi$ is the list $\pi(1),\dots,\pi(3\ell)$, each in unary; the entries of $s,t\in\{-1,0,1\}^w$ use the code $0\mapsto00$, $1\mapsto01$, $-1\mapsto11$;
--   - an index $i\in[2^\ell]$ is its associated bit string $(i_1,\dots,i_\ell)$;
--   - an integer matrix is the list of its entries in lexicographic order of the index, each entry a sign bit followed by the number of binary digits of its absolute value in unary and then those digits.
--
--   The input of Theorem 3.13's algorithm is the code of $pp$ followed by the code of $BP_g$, of length at least $\max(m,w,\ell)$ and at most a polynomial in $m,w,\ell$; no object of size $L=2^\ell$ appears in any input.
--
--   **Formalization Note.** `encParams m pp`, `encROBP B`, `encInput m pp B`, `encIndex ℓ i`, `encInt`, `encSq` ($m\times m$), `encVf` ($m^3\times m$) and `encMhat` ($m^4\times m^6$). `encNat` is the unary code of `QAlgorithms.Complexity`. All codes are injective for fixed dimensions and computable in polynomial time from the objects; output codes carry the integer entries in plain binary.
-- source:
--   Wee, Wichs, Wu, SNARGs and ABE for Uniform Computations via Lattice Encodings, STOC 2027 submission (manuscript sha256 fd77662e…), p. 16 (efficient algorithms), p. 22 (Lemma 3.10), p. 24 (Lemma 3.12, Theorem 3.13)

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_UnifLattice_FastVf_Notation
import Definitions.Def_UnifLattice_FastVf_VectorCommitment
import Definitions.Def_UnifLattice_FastVf_QuadraticCommitment
import Definitions.Def_UnifLattice_FastVf_ROBP

open Matrix

/-!
# Bit-string encodings of the inputs and outputs of the algorithms of Lemma 3.10, Lemma 3.12 and
Theorem 3.13

Wee, Wichs, Wu, *SNARGs and ABE for Uniform Computations via Lattice Encodings*, STOC 2027
submission (manuscript sha256 fd77662e…), p. 16 ("efficient": polynomial time in the length of the
input), p. 22 (Lemma 3.10), p. 24 (Lemma 3.12, Theorem 3.13).

The algorithms are functions `List Bool → List Bool` (time is measured by
`QAlgorithms.Complexity.PolyTimeComputable`). Inputs:
* `m`, `ℓ`, `w` in unary (`encNat`), so that each is at most the input length;
* the bits of `W`, `V`, `M_{τ,b}` one per entry, in lexicographic order of the index;
* the reading order `π` as the list of `π(τ)` in unary;
* the entries of `s, t ∈ {−1,0,1}^w` with the code `0 ↦ 00`, `1 ↦ 01`, `−1 ↦ 11`;
* an index `i ∈ [2^ℓ]` as its associated bit string (`ℓ` bits, most significant first).
Outputs: integer matrices, entry by entry in lexicographic order of the index, each entry a sign
bit followed by the binary digits of its absolute value, prefixed by their number in unary.
No object of size `L = 2^ℓ` is part of any input.
-/

namespace UnifLattice.FastVf

open QAlgorithms.Complexity

/-- All pairs, lexicographically. -/
def pairs {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  xs.flatMap fun x => ys.map fun y => (x, y)

/-- The bits of a `{0,1}`-matrix, row by row. -/
def encBitMatrix {ρ κ : Type} (rows : List ρ) (cols : List κ) (A : Matrix ρ κ (Fin 2)) :
    List Bool :=
  rows.flatMap fun i => cols.map fun j => decide (A i j = 1)

/-- The columns `[2m³]` of `W` and `V`, in lexicographic order. -/
def colList (m : ℕ) : List (Col m) :=
  pairs (List.finRange 2) (pairs (List.finRange m) (pairs (List.finRange m) (List.finRange m)))

/-- Code of the commitment parameters: `m` in unary, then the bits of `W`, then those of `V`. -/
def encParams (m : ℕ) (pp : CommitParams m) : List Bool :=
  encNat m ++ encBitMatrix (List.finRange m) (colList m) pp.W ++
    encBitMatrix (List.finRange m) (colList m) pp.V

/-- Two-bit code of an element of `{−1, 0, 1}`. -/
def encSign : SignType → List Bool
  | .zero => [false, false]
  | .pos => [false, true]
  | .neg => [true, true]

/-- Code of a branching program `(π, {M_{τ,b}}, s, t)`: `ℓ` and `w` in unary, `π(0), …, π(3ℓ−1)` in
unary, the bits of `M_{τ,0}` and `M_{τ,1}` for `τ = 0, …, 3ℓ−1`, then `s` and `t`. -/
def encROBP (B : ROBP) : List Bool :=
  encNat B.ℓ ++ encNat B.w ++
    (List.finRange (3 * B.ℓ)).flatMap (fun τ => encNat (B.π τ).val) ++
    (List.finRange (3 * B.ℓ)).flatMap (fun τ => (List.finRange 2).flatMap fun b =>
      encBitMatrix (List.finRange B.w) (List.finRange B.w) (B.M τ b)) ++
    (List.finRange B.w).flatMap (fun a => encSign (B.s a)) ++
    (List.finRange B.w).flatMap (fun a => encSign (B.t a))

/-- The input of Theorem 3.13's algorithm: `pp = (W, V)` together with `BP_g`. -/
def encInput (m : ℕ) (pp : CommitParams m) (B : ROBP) : List Bool :=
  encParams m pp ++ encROBP B

/-- Self-delimiting signed binary code of an integer: sign bit (`true` for negative), the number of
binary digits of `|z|` in unary, then those digits (least significant first, `Nat.bits`). -/
def encInt (z : ℤ) : List Bool :=
  decide (z < 0) :: (List.replicate (Nat.bits z.natAbs).length true ++ false :: Nat.bits z.natAbs)

/-- Code of an integer matrix: its entries in the given row and column orders. -/
def encIntMatrix {ρ κ : Type} (rows : List ρ) (cols : List κ) (A : Matrix ρ κ ℤ) : List Bool :=
  rows.flatMap fun i => cols.flatMap fun j => encInt (A i j)

/-- Code of an `m × m` integer matrix. -/
def encSq {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) : List Bool :=
  encIntMatrix (List.finRange m) (List.finRange m) A

/-- Code of an `m³ × m` integer matrix such as `V_f` (rows `Fin m × (Fin m × Fin m)`). -/
def encVf {m : ℕ} (A : Matrix (Fin m × (Fin m × Fin m)) (Fin m) ℤ) : List Bool :=
  encIntMatrix (pairs (List.finRange m) (pairs (List.finRange m) (List.finRange m)))
    (List.finRange m) A

/-- The index set `[m⁶]` of `vec(A) ⊗ vec(B) ⊗ vec(C)`, lexicographically. -/
def k6List (m : ℕ) : List (K6 m) :=
  let sq := pairs (List.finRange m) (List.finRange m)
  pairs (pairs sq sq) sq

/-- Code of an `m⁴ × m⁶` integer matrix such as `M̂` of Lemma 3.12 (rows: the index
`(column, row)` of `vec` of an `m³ × m` matrix). -/
def encMhat {m : ℕ} (A : Matrix (Fin m × (Fin m × (Fin m × Fin m))) (K6 m) ℤ) : List Bool :=
  encIntMatrix
    (pairs (List.finRange m) (pairs (List.finRange m) (pairs (List.finRange m) (List.finRange m))))
    (k6List m) A

/-- Code of an index `i ∈ [2^ℓ]`: its associated bit string `(i₁, …, i_ℓ)`, most significant bit
first. -/
def encIndex (ℓ : ℕ) (i : Fin (2 ^ ℓ)) : List Bool :=
  List.ofFn fun t => decide (assocBit ℓ i t = 1)

end UnifLattice.FastVf


