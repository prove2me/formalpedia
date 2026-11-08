-- Prove2me | Definitions.Def_SpikyCVP_encInst
-- name    : SpikyCVP_encInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:38:00.212479+00:00
-- url     : https://prove2.me/theorems/2fdad6c0-cd94-4cc6-93a1-45a89076afe3
-- title:
--   Binary encodings of CVP instances and of rational vectors
-- statement:
--   An instance of exact $\mathrm{CVP}_p$ with error parameter is encoded as a binary string: first the dimension $n$, then the entries of the basis $B\in\mathbb Q^{n\times n}$ in row-major order, then the coordinates of the target $t\in\mathbb Q^n$, and finally $\delta\in\mathbb Q$. A rational vector, such as the output, is encoded coordinate by coordinate. The instance of the Euclidean subroutine omits $\delta$.
--
--   The **input length** $\ell$ (the paper's $|I|$) is the length of this string, $\delta$ included: a rational $\delta\le 1/2$ can have a numerator and denominator much longer than $\log(1/\delta)$, and an algorithm has to read them.
--
--   **Formalization Note** The encoders build on the published self-delimiting codes $\texttt{encodeNat}$, $\texttt{encodeInt}$, $\texttt{encodeRat}$ of $\texttt{ExponomialAssortment.FPTAS}$, so a machine can tell where the instance ends and a string of coins begins. The paper leaves the bit encoding open.
-- source:
--   Aggarwal, Morolia, How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector Problem, STOC 2027 submission (manuscript sha256 535c3bcc…), §1.1, p.3 (PDF p.5); §2.1, p.10 (PDF p.12); Definition 2.9, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine

open ExponomialAssortment.FPTAS

namespace SpikyCVP

/-- The self-delimiting binary encoding of a rational vector, coordinate by coordinate. Aggarwal, Morolia,
*How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector Problem*, STOC 2027
submission (manuscript sha256 535c3bcc…), Definition 2.9, p.15: the inputs and the output of `CVPp` are
rational vectors. The dimension is not repeated, since the instance writes it once. -/
def encVec {n : ℕ} (t : Fin n → ℚ) : List Bool :=
  (List.finRange n).flatMap fun j => encodeRat (t j)

/-- The row-major self-delimiting binary encoding of a rational `n × n` basis. -/
def encMat {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) : List Bool :=
  (List.finRange n).flatMap fun i => (List.finRange n).flatMap fun j => encodeRat (B i j)

/-- The input of `CVP2` in Theorem 2.10, p.15: `n`, then the basis, then the target. -/
def encCVP {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (t : Fin n → ℚ) : List Bool :=
  encodeNat n ++ encMat B ++ encVec t

/-- The input of Theorem 1.1, p.3: `n`, the basis, the target and the error parameter `δ`.

**Formalization Note.** `|I|`, "the bit length of the input" (p.3, p.10), is the length of this list,
`δ` included: a rational `δ ≤ 1/2` can have a code much longer than `log(1/δ)`, and the machine has to
read it. The encoders are self-delimiting, so a machine can tell where the instance ends and a further
string (the coins) begins. -/
def encInst {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (t : Fin n → ℚ) (δ : ℚ) : List Bool :=
  encCVP B t ++ encodeRat δ

end SpikyCVP


