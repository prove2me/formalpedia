-- Prove2me | Definitions.Def_UnitaryQIPPSPACE_Bits
-- name    : UnitaryQIPPSPACE_Bits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:27:17.080767+00:00
-- url     : https://prove2.me/theorems/4a1d1b88-4135-4d67-8098-3ec15c0654d7
-- title:
--   Computational basis labels of $n$ qubits
-- statement:
--   An $n$-qubit register is $(\mathbb C^2)^{\otimes n}=\mathbb C^{2^n}$ with computational basis $\{|x\rangle : x\in\{0,1\}^n\}$. A basis label is a bit string $x=x_0x_1\cdots x_{n-1}$; qubit $0$ is the leftmost. Operators on $n$ qubits are $2^n\times 2^n$ matrices indexed by these labels.
--
--   The module also fixes small conventions used throughout: the word of a label (the input format of a Turing machine), the label $|j\rangle$ of a number $j<2^n$ in binary with the most significant bit on qubit $0$, the bitwise XOR $x\oplus y$, the all-zero label $0^n$, the splitting of $a+b$ qubits into the first $a$ and the last $b$, and the binary code of a natural number used inside descriptions.
--
--   **Formalization Note** A label is a function $\{0,\dots,n-1\}\to\{0,1\}$.
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), §2 (notation), p.9 (PDF p.11)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace UnitaryQIPPSPACE

/-- **Computational basis of `n` qubits** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*,
arXiv:2611.02819, held version sha256 9e357a00…, §2, p. 9 (PDF p. 11): an `n`-qubit register is
`(ℂ²)^{⊗n} = ℂ^{2^n}` with computational basis `{|x⟩ : x ∈ {0,1}^n}`). A basis label is a bit string
`x : Fin n → Bool`; qubit `0` is the first (leftmost) qubit of `|x⟩ = |x₀ x₁ ⋯ x_{n-1}⟩`.

**Formalization Note** Operators on `n` qubits are matrices indexed by `Bits n`. -/
abbrev Bits (n : ℕ) : Type := Fin n → Bool

/-- The bit string of a basis label, as a word `x₀ x₁ ⋯ x_{n-1}` (the input format of a Turing
machine). -/
def Bits.toStr {n : ℕ} (x : Bits n) : Str := List.ofFn x

/-- The basis label of the number `j < 2^n` in binary, most significant bit first: qubit `i`
carries bit `n - 1 - i` of `j`, so `|j⟩` is the `j`-th computational basis state in the usual
order `|0⋯00⟩, |0⋯01⟩, …` (used for `H_d = span{|0⟩, …, |d-1⟩}` in Theorem 4.6, p. 25). -/
def Bits.ofNat (n j : ℕ) : Bits n := fun i => Nat.testBit j (n - 1 - i.val)

/-- Bitwise XOR of two basis labels, `x ⊕ y`. -/
def Bits.xor {n : ℕ} (x y : Bits n) : Bits n := fun i => Bool.xor (x i) (y i)

/-- The all-zero basis label `0^n`. -/
def Bits.zero (n : ℕ) : Bits n := fun _ => false

/-- Splitting `a + b` qubits into the first `a` and the last `b` (`x ↦ (x_{<a}, x_{≥a})`); its
inverse is concatenation `Fin.append`. -/
def Bits.splitEquiv (a b : ℕ) : Bits (a + b) ≃ Bits a × Bits b :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow (Fin a) (Fin b) Bool)

/-- Binary code of a natural number (little-endian, no trailing zeros), the self-delimiting
component of descriptions handed to and produced by Turing machines. -/
def natCode (i : ℕ) : Str := Nat.bits i

end UnitaryQIPPSPACE


