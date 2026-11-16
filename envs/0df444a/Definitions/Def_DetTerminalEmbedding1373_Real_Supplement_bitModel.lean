-- Prove2me | Definitions.Def_DetTerminalEmbedding1373_Real_Supplement_bitModel
-- name    : DetTerminalEmbedding1373_Real_Supplement_bitModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:16:03.760485+00:00
-- url     : https://prove2.me/theorems/5cf9549f-0b8e-4446-a380-e70885ae4810
-- title:
--   Heights of rationals and the binary inputs of the two-phase bit algorithm
-- statement:
--   This file fixes the finite-bit input model of Theorem 1.3.
--
--   1. **Height.** A rational $a=p/q$ in lowest terms with $q>0$ has height at most $B$ if $|p|\le 2^B$ and $q\le 2^B$. A rational vector has coordinate height at most $B$ if each coordinate does.
--   2. **Binary codes.** A rational vector $v\in\mathbb Q^d$ is written as $d$ in self-delimiting binary followed by its coordinates, each as its reduced signed numerator and its denominator in binary (the published codes `encBin` and `encRat`). A bit string $w$ is made self-delimiting by writing its length in binary first.
--   3. **Preprocessing input.** The input of the preprocessing phase is $n$, $d$, the terminals $x_1,\dots,x_n\in\mathbb Q^d$, the accuracy $\varepsilon\in\mathbb Q$ and the integer $S$, in that order, all in binary.
--   4. **Query input.** The input of the query phase is the bit string $D$ stored by the preprocessing phase (self-delimited), followed by the query $q\in\mathbb Q^d$ in binary.
--
--   The machines that run on these inputs are Mathlib's multi-stack Turing machines with Boolean input and output alphabets and finite stack alphabets (published `RevRedSAT.FiniteAlphabets`), and "outputs $w'$ on $w$ within $t$ steps" is the published `HMBinPacking.OutputsWithin`.
--
--   **Formalization Note** The paper defines the height of a nonzero rational only; under this definition $0=0/1$ has height at most every $B$. Section 7 (p. 23) uses the binary length of $|p|$ and $q$ instead, which differs by at most one bit; Theorem 1.3 is stated with the §1.1 notion. All codes have length linear in the heights, so the inputs are not padded.
-- source:
--   Vladimir Braverman, Kuan Cheng, Jiaqing Zhu, STOC 2027 submission #1373 (October 2026), p. 4 (definition of height before Theorem 1.3) and p. 23 (§7, finite-bit input); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1373.pdf

import Mathlib
import Definitions.Def_DetTerminalEmbedding1373_Real_Supplement_roundedProjection
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RevRedSAT_FiniteAlphabets
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding

set_option autoImplicit false

namespace DetTerminalEmbedding1373.Real.Supplement

open QAlgorithms.LocalHamiltonian

/-- Height, §1.1, p. 4: a rational `p/q` in lowest terms (`q > 0`) has height at most `B` iff
`|p| ≤ 2^B` and `q ≤ 2^B`. Zero (`0/1`) has height at most every `B`. -/
def HeightLE (a : ℚ) (B : ℕ) : Prop := a.num.natAbs ≤ 2 ^ B ∧ a.den ≤ 2 ^ B

/-- Every coordinate of a rational vector has height at most `B`. -/
def VecHeightLE {d : ℕ} (v : Fin d → ℚ) (B : ℕ) : Prop := ∀ k, HeightLE (v k) B

/-- Binary code of a rational vector: its length in self-delimiting binary, then each coordinate as
a reduced signed numerator and a denominator in binary (published `encBin`, `encRat`). -/
def vecBits {d : ℕ} (v : Fin d → ℚ) : List Bool :=
  encBin d ++ (List.ofFn v).flatMap encRat

/-- A bit string made self-delimiting: its length in binary, then the string. -/
def wordBits (w : List Bool) : List Bool := encBin w.length ++ w

/-- Input of the preprocessing phase of Theorem 1.3: `n`, `d`, the terminals `x₁, …, xₙ ∈ ℚᵈ`,
the accuracy `ε ∈ ℚ` and the integer `S`, all in binary. -/
def preprocessingInput {n d : ℕ} (x : Fin n → Fin d → ℚ) (ε : ℚ) (S : ℕ) : List Bool :=
  encBin n ++ encBin d ++ (List.ofFn x).flatMap vecBits ++ encRat ε ++ encBin S

/-- Input of the query phase: the stored data `D` written by preprocessing, then the query
`q ∈ ℚᵈ` in binary. -/
def queryInput {d : ℕ} (D : List Bool) (q : Fin d → ℚ) : List Bool :=
  wordBits D ++ vecBits q

end DetTerminalEmbedding1373.Real.Supplement


