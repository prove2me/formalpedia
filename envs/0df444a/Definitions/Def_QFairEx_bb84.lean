-- Prove2me | Definitions.Def_QFairEx_bb84
-- name    : QFairEx_bb84
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:22:26.040782+00:00
-- url     : https://prove2.me/theorems/232f1269-79dd-4c06-8f72-d7c81f5573e6
-- title:
--   BB84 states $H^\theta X^x|0\rangle$
-- statement:
--   The Hadamard gate is $H=\frac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$ and the Pauli gate $X=\begin{pmatrix}0&1\\1&0\end{pmatrix}$. For bits $\theta,x\in\{0,1\}$ the **BB84 state** is
--   $$|\phi\rangle=H^\theta X^x|0\rangle\in\{|0\rangle,|1\rangle,|+\rangle,|-\rangle\},$$
--   where $\theta$ is the basis and $x$ the bit within the basis. For strings $\theta,x\in\{0,1\}^n$, the **parallel challenge state** is $|\phi_1\rangle\otimes\cdots\otimes|\phi_n\rangle$ with $|\phi_i\rangle=H^{\theta_i}X^{x_i}|0\rangle$.
--
--   These are the challenges of the BB84 basis-guessing game, the information-theoretic core of the impossibility proof.
--
--   **Formalization Note** Bits are Booleans; $H^0=X^0=I$. An $n$-qubit register has basis $\{0,1\}^n$, written `Fin n → Fin 2`.
-- source:
--   Chung, Lee, Raizes, Thyagarajan, Quantum Fair Exchange, STOC 2027 submission (manuscript of 2026-11-02, sha256 0099b883bc58c8a8ab3f2031fadc6e6c71b4ef1289bb55028fbbebcd070a9b6e), §4.2.1, p.21; Algorithm 4.4, step 2, p.21

import Mathlib
import Definitions.Def_QFairEx_SupportedOn

namespace QFairEx

open Matrix

/-- The Hadamard gate `H = (1/√2) [[1, 1], [1, −1]]` on a qubit (basis `Fin 2`). -/
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • !![1, 1; 1, -1]

/-- The Pauli `X` gate `[[0, 1], [1, 0]]`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The computational basis state `|0⟩`. -/
def ket0 : Fin 2 → ℂ := ![1, 0]

/-- **BB84 state** `|ϕ⟩ = H^θ X^x |0⟩`.
Chung, Lee, Raizes, Thyagarajan, *Quantum Fair Exchange*, STOC 2027 submission (manuscript of
2026-11-02, sha256 0099b883…), §4.2.1, p.21: "A BB84 state is one of {|0⟩, |1⟩, |+⟩, |−⟩}. We
write it as |ϕ⟩ = H^θ X^x |0⟩, θ, x ∈ {0, 1}, where θ specifies the basis and x specifies the
bit within that basis."

**Formalization Note.** Bits are `Bool` (`false = 0`, `true = 1`); `M^false = 1`, `M^true = M`.
So `bb84 false x = |x⟩` and `bb84 true false = |+⟩`, `bb84 true true = |−⟩`. -/
noncomputable def bb84 (θ x : Bool) : Fin 2 → ℂ :=
  ((if θ then hadamard else 1) * (if x then pauliX else 1)) *ᵥ ket0

/-- **The parallel challenge state** `|ϕ₁⟩ ⊗ ⋯ ⊗ |ϕ_n⟩`, `|ϕ_i⟩ = H^{θ_i} X^{x_i} |0⟩`, on `n`
qubits with basis `Fin n → Fin 2` (Algorithm 4.4, step 2, p.21). -/
noncomputable def bb84Vec {n : ℕ} (θ x : Fin n → Bool) : (Fin n → Fin 2) → ℂ :=
  fun a => ∏ i, bb84 (θ i) (x i) (a i)

end QFairEx


