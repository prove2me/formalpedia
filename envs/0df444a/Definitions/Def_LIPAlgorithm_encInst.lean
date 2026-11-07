-- Prove2me | Definitions.Def_LIPAlgorithm_encInst
-- name    : LIPAlgorithm_encInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:31.588252+00:00
-- url     : https://prove2.me/theorems/2f2068f3-17ae-45f7-bd8a-6465a4d4d5b7
-- title:
--   Binary encodings of instances and of lists of matrices
-- statement:
--   Fix self-delimiting binary encodings of the instance $(n,G_1,G_2)$: first $n$, then the entries of $G_1$ and of $G_2$ in row-major order. A list of matrices is encoded by its length followed by the matrices. Rational Gram matrices and bit strings have similar encodings.
--
--   The input length $\ell$ of the instance is at least $2n^2$, because each entry takes at least two bits, so a polynomial in the number $n$ and the bit length of the Gram matrices is the same as a polynomial in $\ell$.
--
--   **Formalization Note** The encoders build on the published $\texttt{encodeNat}$, $\texttt{encodeInt}$, $\texttt{encodeRat}$ of $\texttt{ExponomialAssortment.FPTAS}$. The paper leaves the bit encoding open.
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), §2.2, p.10; Remark 2.2, p.10

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine
import Definitions.Def_LIPAlgorithm_Gram

open ExponomialAssortment.FPTAS

namespace LIPAlgorithm

/-- The row-major self-delimiting binary encoding of an integer matrix: the input format of §2.2, p.10
(the paper leaves the bit encoding open; "bits is the encoding length of the input Gram matrices",
Remark 2.2, p.10). The dimension is not repeated, since `encInst` writes it once. -/
def encG {n : ℕ} (G : Gram n) : List Bool :=
  (List.finRange n).flatMap fun i => (List.finRange n).flatMap fun j => encodeInt (G i j)

/-- The input of the main theorem: `n`, then `G₁`, then `G₂`.

**Formalization Note.** The encoders are self-delimiting, so a machine can tell where the instance ends
and a further string begins. Every entry costs at least two bits, so the length is at least `2n²`, and
"poly(n, bits)" of Remark 2.2, p.10 is the same as a polynomial in this length. -/
def encInst {n : ℕ} (G₁ G₂ : Gram n) : List Bool :=
  encodeNat n ++ encG G₁ ++ encG G₂

/-- The output format of the all-isomorphisms problem: the number of matrices, then the matrices. -/
def encMatList {n : ℕ} (Us : List (Gram n)) : List Bool :=
  encodeNat Us.length ++ Us.flatMap encG

/-- The row-major encoding of a rational Gram matrix, preceded by its rank (Theorem 5.12, p.27). -/
def encRatGram {r : ℕ} (G : RatGram r) : List Bool :=
  encodeNat r ++
    (List.finRange r).flatMap fun i => (List.finRange r).flatMap fun j => encodeRat (G i j)

/-- A self-delimiting encoding of a bit string (the canonical strings of Theorems 5.12 and 5.14). -/
def encString (s : List Bool) : List Bool :=
  encodeNat s.length ++ s

end LIPAlgorithm


