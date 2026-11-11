-- Prove2me | Definitions.Def_PelagicFF_hadamardN
-- name    : PelagicFF_hadamardN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:54:45.16468+00:00
-- url     : https://prove2.me/theorems/06e27886-85ac-4d50-809a-70c5d1be94fd
-- title:
--   The phase state $|\psi_f\rangle$, the sign unitary $U_g$ and $H^{\otimes n}$
-- statement:
--   Let $N=2^n$ and index the computational basis of $n$ qubits by $x\in\{0,1\}^n$.
--
--   1. The **binary phase state** of $f:\{0,1\}^n\to\{-1,1\}$ is $|\psi_f\rangle=N^{-1/2}\sum_x f(x)|x\rangle$.
--   2. The **diagonal unitary** of $g$ is $U_g:|x\rangle\mapsto g(x)|x\rangle$.
--   3. The **Hadamard transform** on all $n$ qubits is $H^{\otimes n}$, with matrix entries $\langle y|H^{\otimes n}|x\rangle=2^{-n/2}(-1)^{x\cdot y}$.
--
--   These are the ingredients of the quantum protocol for $\mathrm{PFF}_n$ (§4.1).
--
--   **Formalization Note** Vectors are amplitude functions on `Fin n → Bool`, operators are matrices on it; the module's main declaration is `hadamardN`, with `phaseState` and `signDiag`.
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), §4.1, p.27

import Mathlib
import Definitions.Def_Cotype

open OAI.Cotype

namespace PelagicFF

/-- The `n`-qubit binary phase state `|ψ_f⟩ = N^{−1/2} ∑ₓ f(x)|x⟩` (`N = 2ⁿ`) of a Boolean function
`f : {0,1}ⁿ → {−1,1}`, as its amplitude vector in the computational basis `Fin n → Bool`.
arXiv:2610.05585 (held version, sha256 4564aef3…), §4.1, p.27. -/
noncomputable def phaseState {n : ℕ} (f : (Fin n → Bool) → Bool) : (Fin n → Bool) → ℂ :=
  fun x => ((Real.sqrt (2 ^ n))⁻¹ : ℂ) * (sign (f x) : ℂ)

/-- The diagonal unitary `U_g : |x⟩ ↦ g(x)|x⟩` of a Boolean function `g : {0,1}ⁿ → {−1,1}`.
arXiv:2610.05585 (held version, sha256 4564aef3…), §4.1, p.27. -/
noncomputable def signDiag {n : ℕ} (g : (Fin n → Bool) → Bool) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  Matrix.diagonal (fun x => (sign (g x) : ℂ))

/-- The `n`-fold Hadamard transform `H^{⊗n}` in the computational basis: the entry in row `y` and
column `x` is `2^{−n/2} (−1)^{x·y}` with `x·y = #{i | xᵢ ∧ yᵢ}` (mod 2).
arXiv:2610.05585 (held version, sha256 4564aef3…), §4.1, p.27 ("applies Hadamard gates to all n
qubits").

**Formalization Note.** This is the matrix of the tensor power of the one-qubit Hadamard
`2^{−1/2}[[1, 1], [1, −1]]`; the module also defines `phaseState` and `signDiag`. -/
noncomputable def hadamardN (n : ℕ) : Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  fun y x => ((Real.sqrt (2 ^ n))⁻¹ : ℂ) * (-1) ^ (Finset.univ.filter (fun i => x i && y i)).card

end PelagicFF


