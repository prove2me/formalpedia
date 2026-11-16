-- Prove2me | Definitions.Def_PolyEulerFlow_Supplement_encodeNatVec
-- name    : PolyEulerFlow_Supplement_encodeNatVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:03:38.080213+00:00
-- url     : https://prove2.me/theorems/17b27f22-d789-4e0a-b434-05722975403b
-- title:
--   Binary encodings of integer tuples, rationals and certificates; $\ell(x)$ on $\mathbb N^d$; the classes P and PSPACE on $\mathbb N^d$
-- statement:
--   Integers are read in their canonical binary word $\mathrm{bin}(x)$ (most significant bit first, $0$ written as one bit). A word $w$ is made **self-delimiting** by writing every bit $b$ as the block $1b$ and ending with the block $00$; this copy has length $2|w|+2$.
--
--   1. A tuple $x=(x_1,\dots,x_d)\in\mathbb N^d$ is encoded by the self-delimiting copies of $\mathrm{bin}(x_1),\dots,\mathrm{bin}(x_d)$ in order, a word of length $\sum_i(2\ell(x_i)+2)$.
--   2. For $x\in\mathbb N^d$, $\ell(x)=\max_i\ell(x_i)$ is the maximal binary length of the coordinates, with $\ell(0)=1$.
--   3. A natural number $s$ in **unary** is the self-delimiting copy of $1^s$.
--   4. A rational $q$ is encoded by the self-delimiting copies of its sign bit, of the binary word of $|\mathrm{num}(q)|$ and of the binary word of $\mathrm{den}(q)$ (lowest terms); a rational vector coordinate after coordinate.
--   5. A language $L\subseteq\mathbb N^d$ is in $\mathsf P$ if a multi-stack Turing machine decides membership in time polynomial in the length of the encoding of the input, and in $\mathsf{PSPACE}$ if a multi-stack machine halting on every input decides it with total stack length bounded by a polynomial in that length. $\mathsf{PSPACE}$ also denotes the class of polynomial-space languages over $\{0,1\}$.
--
--   These are the standard complexity classes for integer inputs used in Theorems 8–11 and 20 (p.5: inputs $x\in\mathbb N^d$ with fixed $d$; integers in binary).
--
--   **Formalization Note** The machine model is Mathlib's `Turing.FinTM2` (`TM2ComputableInPolyTime`), as in the published `PvsNP`; polynomial space is the published `OptimalQueuingComplexity.Restless.InPSPACE`. The paper fixes no encoding of tuples; any self-delimiting encoding of linear length gives the same classes. The outer $\max(1,\cdot)$ in $\ell$ only matters for $d=0$.
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow: Polynomial Dynamics for P and PSPACE (manuscript, STOC 2027 submission, sha256 c4e01b2beb237b48b48e97294deb3c15dae11d39c5f136914567c5ca2ae1b119), §2.1, p.5 (PDF 7): ℓ(x) on ℕ^d; Theorems 8, 9, 20, pp.6–7, 21 (PDF 8–9, 23)

import Mathlib
import Definitions.Def_PolyEulerFlow_TwoStackDecider
import Definitions.Def_OptimalQueuingComplexity_Restless_PSPACEComplete

namespace PolyEulerFlow.Supplement

open PolyEulerFlow

/-- A self-delimiting copy of a bit word: every bit `b` becomes the block `1b`, and the word ends with the block `00`.
Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), p.5 (PDF 7).
**Formalization Note.** The paper fixes no encoding of tuples; any self-delimiting binary encoding of linear length gives the same
complexity classes. -/
def tagBits (w : List Bool) : List Bool :=
  w.flatMap (fun b => [true, b]) ++ [false, false]

/-- The binary encoding of `x ∈ ℕ^d`: the self-delimiting copies of the canonical binary words of its coordinates, in order.
Its length is `Σ_i (2ℓ(x_i) + 2)`. -/
def encodeNatVec {d : ℕ} (x : Fin d → ℕ) : List Bool :=
  (List.finRange d).flatMap (fun i => tagBits (binWord (x i)))

/-- `ℓ(x)` for `x ∈ ℕ^d`: the maximal binary length of the coordinates, with `ℓ(0) = 1` (p.5).
**Formalization Note.** The outer `max 1` only matters for `d = 0`. -/
def vecLength {d : ℕ} (x : Fin d → ℕ) : ℕ :=
  max 1 (Finset.univ.sup fun i => inputLength (x i))

/-- The unary word of `s`: `s` ones, made self-delimiting. -/
def unaryWord (s : ℕ) : List Bool :=
  tagBits (List.replicate s true)

/-- The binary encoding of a rational: sign bit, binary numerator, binary denominator, each self-delimiting. -/
def encodeRat (q : ℚ) : List Bool :=
  tagBits [decide (q < 0)] ++ tagBits (binWord q.num.natAbs) ++ tagBits (binWord q.den)

/-- The binary encoding of a rational vector, coordinate after coordinate. -/
def encodeRatVec {m : ℕ} (v : Fin m → ℚ) : List Bool :=
  (List.finRange m).flatMap (fun i => encodeRat (v i))

/-- `L ∈ P` for a language `L ⊆ ℕ^d` (p.6, Theorem 8): a multi-stack machine decides membership in time polynomial in the
length of the binary encoding of the input. -/
def InP {d : ℕ} (L : Set (Fin d → ℕ)) : Prop :=
  ∃ χ : (Fin d → ℕ) → Bool,
    Nonempty (Turing.TM2ComputableInPolyTime (encodeNatVec : (Fin d → ℕ) → List Bool) Computability.encodeBool χ) ∧
      ∀ x, x ∈ L ↔ χ x = true

/-- `L ∈ PSPACE` for a language `L ⊆ ℕ^d` (p.7, Theorem 9), with the published polynomial-space notion. -/
def InPSPACE {d : ℕ} (L : Set (Fin d → ℕ)) : Prop :=
  OptimalQueuingComplexity.Restless.InPSPACE (encodeNatVec : (Fin d → ℕ) → List Bool) (fun x => x ∈ L)

/-- The class PSPACE of languages over `{0,1}` (p.21, Theorem 20). -/
def PSPACEClass : Set (Language Bool) :=
  {L | OptimalQueuingComplexity.Restless.InPSPACE (id : List Bool → List Bool) (fun w => w ∈ L)}

end PolyEulerFlow.Supplement


