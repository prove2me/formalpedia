-- Prove2me | Definitions.Def_ModLatSVP_encModule
-- name    : ModLatSVP_encModule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:14:43.898215+00:00
-- url     : https://prove2.me/theorems/dc6aa5af-7d9e-4423-828c-bfe7312e0c9a
-- title:
--   Binary encodings of field data, module inputs, chain data and integer vectors
-- statement:
--   Inputs and outputs are binary strings built from self-delimiting codes of natural numbers, integers and rationals.
--
--   1. An **integer vector** is encoded coordinate by coordinate; an integer matrix row by row.
--   2. The **field data** are encoded as the degree $d$, the $d^3$ entries of the multiplication table, and the involution matrix.
--   3. The **module input** is the field data, the dimension $N$, the rational Gram matrix $G$ (row by row) and the action matrices $A_1,\dots,A_d$.
--   4. The **chain data** are the number of levels followed by each level's field data and inclusion matrix.
--   5. A CVP target $t\in\mathbb Q^N$ is appended coordinate by coordinate.
--
--   The **input length** $\ell$ in all running-time and space bounds is the length of the whole input string; it bounds the paper's bit length $B$ ("the field data and action matrices are included in the input bit length B"), the chain data when supplied, the target length $\ell(t)$, and $N$.
--
--   **Formalization Note** The codes are the published $\texttt{encodeNat}$, $\texttt{encodeInt}$, $\texttt{encodeRat}$ of $\texttt{ExponomialAssortment.FPTAS}$ and $\texttt{SpikyCVP.encMat}$, $\texttt{SpikyCVP.encVec}$; sizes come first, so a string determines the instance. The paper leaves the bit encoding open.
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), §2.1, p.11 (PDF p.11); §2.2, p.12; Theorem 3.4, p.20; Lemma 3.6, p.21

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine
import Definitions.Def_SpikyCVP_encInst
import Definitions.Def_ModLatSVP_RepresentsChain

open ExponomialAssortment.FPTAS

namespace ModLatSVP

/-- The self-delimiting binary encoding of an integer vector, coordinate by coordinate (the output of SVP
and CVP: "A lattice vector B_L x is represented by its integer coordinate vector x ∈ ℤ^m", §2.1, p.11).
Kim, Lee, Son, *Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions*,
STOC 2027 submission (manuscript sha256 e7151fad…). -/
def encIntVec {n : ℕ} (x : Fin n → ℤ) : List Bool :=
  (List.finRange n).flatMap fun i => encodeInt (x i)

/-- The row-major encoding of an integer matrix. -/
def encIntMat {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : List Bool :=
  (List.finRange m).flatMap fun i => encIntVec (A i)

/-- The encoding of a multiplication table `c_{ijk}`. -/
def encTable {d : ℕ} (c : Fin d → Fin d → Fin d → ℤ) : List Bool :=
  (List.finRange d).flatMap fun i => (List.finRange d).flatMap fun j => encIntVec (c i j)

/-- The field data: the degree `d`, the multiplication table and the involution matrix of an integral
basis (Lemma 3.6, p.21: "given by an integral basis of 𝒪_K, its multiplication table, and its
involution ⋆"). -/
def encField (d : ℕ) (c : Fin d → Fin d → Fin d → ℤ) (S : Matrix (Fin d) (Fin d) ℤ) : List Bool :=
  encodeNat d ++ encTable c ++ encIntMat S

/-- The module input of §2.2, p.12: the field data, the lattice dimension `N`, the rational Gram matrix
`G` (row-major, the published `SpikyCVP.encMat`) and the action matrices `A_1, …, A_d`.

**Formalization Note.** "The field data and action matrices are included in the input bit length B"
(p.12); the input length `ℓ` used for budgets is the length of this list (with the chain data and the
target appended where a statement has them). Every encoder is self-delimiting and the sizes come first,
so the list determines the instance. -/
def encModule (d N : ℕ) (c : Fin d → Fin d → Fin d → ℤ) (S : Matrix (Fin d) (Fin d) ℤ)
    (G : Matrix (Fin N) (Fin N) ℚ) (A : Fin d → Matrix (Fin N) (Fin N) ℤ) : List Bool :=
  encField d c S ++ encodeNat N ++ SpikyCVP.encMat G ++ (List.finRange d).flatMap fun i => encIntMat (A i)

/-- The encoding of one level of a chain: its field data and its inclusion matrix into `K`. -/
def encLevel {d : ℕ} (L : FieldLevel d) : List Bool :=
  encField L.e L.c L.S ++ encIntMat L.incl

/-- The encoding of the chain data `K₁, …, K_h`: the length `h`, then the levels. -/
def encChain {d : ℕ} (Ls : List (FieldLevel d)) : List Bool :=
  encodeNat Ls.length ++ Ls.flatMap encLevel

end ModLatSVP


