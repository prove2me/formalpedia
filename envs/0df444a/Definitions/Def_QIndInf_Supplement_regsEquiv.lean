-- Prove2me | Definitions.Def_QIndInf_Supplement_regsEquiv
-- name    : QIndInf_Supplement_regsEquiv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:20:18.739332+00:00
-- url     : https://prove2.me/theorems/8be566a6-28ad-4297-b4f0-49da4acd739b
-- title:
--   Registers as blocks of qubit wires
-- statement:
--   The computational basis of $n$ qubits is indexed both by bit strings $y\in\{0,1\}^n$ (the wires of a circuit) and by $\{0,\dots,2^n-1\}$ (the register $R$ of the base mission); the two are identified by reading $y$ as a binary number, qubit $0$ least significant. The $j$ registers $R_1,\dots,R_j$ of $n$ qubits each are identified with $jn$ wires: register $R_{i}$ is the block of wires $n(i-1),\dots,ni-1$. A wire string of length $a+b$ is split into its first $a$ and last $b$ wires, and an outcome $x\in\{0,\dots,2^k-1\}$ of a measurement with $k$ outcome bits is written as the bit string of length $k$ a learner reads.
--
--   These relabellings connect the circuit model of Theorems 4.4 and 5.5 with the register-indexed states of the base mission; they change no trace distance or probability.
-- source:
--   Hiroka, Hsieh, Shirakawa, Universal Inductive Inference of Quantum States, arXiv:2609.36912 (PDF of 2026-11-02, sha256 ac6387756651cc50c671f36acf1ef987db0df0c463581cd948250204441f6925), §4.1, p.18 (R_i n-qubit registers; ρ_{R1…Rm} an mn-qubit state)

import Mathlib
import Definitions.Def_QIndInf_QuantumProcess

set_option autoImplicit false

namespace QIndInf.Supplement

/-- The computational basis of `n` qubits as bit strings `Fin n → Bool` and as the index
`Fin (2^n)` of a register `Reg n` (binary digits, qubit `0` least significant).

**Formalization Note.** A circuit acts on wires (bits `Fin n → Bool`); the published register type
of the base mission is `Reg n = Fin (2^n)`. This bijection only relabels basis states. -/
def bitsEquiv (n : ℕ) : (Fin n → Bool) ≃ QIndInf.Reg n :=
  (Equiv.arrowCongr (Equiv.refl (Fin n)) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- Splitting `a + b` wires into the first `a` and the last `b`. -/
def splitEquiv (a b : ℕ) : (Fin (a + b) → Bool) ≃ (Fin a → Bool) × (Fin b → Bool) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow (Fin a) (Fin b) Bool)

/-- **`j` registers of `n` qubits as `j · n` wires**: register `R_{i+1}` (coordinate `i : Fin j`)
is the block of wires `n·i, …, n·i + n − 1`, in order.

arXiv:2609.36912 (PDF of 2026-11-02), §4.1, p.18 ("for each i ∈ [m], let R_i be an n-qubit
register"; `ρ_{R₁…R_m}` is an `mn`-qubit state). -/
def regsEquiv (n j : ℕ) : (Fin (j * n) → Bool) ≃ QIndInf.Regs n j :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans
    ((Equiv.curry (Fin j) (Fin n) Bool).trans
      (Equiv.arrowCongr (Equiv.refl (Fin j)) (bitsEquiv n)))

/-- A classical outcome `x ∈ Fin (2^k)` (`k` outcome bits) written as the bit string of length
`k` a learner reads. -/
def outcomeStr {k : ℕ} (x : Fin (2 ^ k)) : List Bool :=
  List.ofFn ((bitsEquiv k).symm x)

end QIndInf.Supplement


