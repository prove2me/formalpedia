-- Prove2me | Definitions.Def_QPACLarge_psiF
-- name    : QPACLarge_psiF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:06:20.404176+00:00
-- url     : https://prove2.me/theorems/2f4d451e-4b2c-4bc5-b043-5680364f4104
-- title:
--   The prepared state $|\psi_F\rangle$
-- statement:
--   After one Hadamard on the label qubit and Hadamards on the input register controlled on the flag, the quantum example becomes
--   $$
--   |\psi_F\rangle = \frac{1}{\sqrt2}|\bot\rangle + \frac{1}{\sqrt{2N}} \sum_x F(x)\, |x\rangle_{\mathrm{lab}}, \qquad N = 2^n,\ F = (-1)^f .
--   $$
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 3.2.2, Step 2, p.24

import Mathlib
import Definitions.Def_QPACLarge_sgn
import Definitions.Def_QAlgorithms_Defs_Basic

namespace QPACLarge

open QAlgorithms

/-- **The prepared state `|ψ_F⟩`.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 3.2.2, Step 2, p.24: "`|ψ_F⟩ ≜ (1/√2)|⊥⟩ + (1/√(2N)) Σₓ F(x)|x⟩_lab`", with
`N = 2ⁿ` and `F = (−1)^f`.

**Formalization Note.** A vector of the label space `{⊥} ∪ {0,1}ⁿ` (`Option (Qubits n)`), as an
amplitude function. -/
noncomputable def psiF {n : ℕ} (f : Qubits n → Bool) : Option (Qubits n) → ℂ
  | none => ((Real.sqrt 2)⁻¹ : ℝ)
  | some x => ((Real.sqrt (2 * 2 ^ n))⁻¹ * sgn (f x) : ℝ)

end QPACLarge


