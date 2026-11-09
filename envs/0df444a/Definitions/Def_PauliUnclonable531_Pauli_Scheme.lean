-- Prove2me | Definitions.Def_PauliUnclonable531_Pauli_Scheme
-- name    : PauliUnclonable531_Pauli_Scheme
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:05:02.333226+00:00
-- url     : https://prove2.me/theorems/fd2a5b0f-8d2f-4b54-84a1-da4556cef1e7
-- title:
--   The concrete one-bit encryption scheme
-- statement:
--   For a supported key k, write Pₖ for its tensor Pauli. Encrypt the bit m as the density matrix and decrypt with the outcome effects
--
--   $$\rho_{k,m}=2^{-n}(I+(-1)^mP_k),\qquad Q_{k,m}=\tfrac12(I+(-1)^mP_k).$$
--
--   Outcome 0 denotes eigenvalue +1 and outcome 1 denotes −1. Scheme is only a data record of a key mass, an encryption matrix, and two decryption effects; it contains no correctness, efficiency, or security assertion. The concrete scheme uses the exact uniform mass from Keys and the displayed matrices. Its validity and implementation are theorem conclusions, rather than assumptions in this definition.
-- source:
--   Prabhanjan Ananth, Seyoon Ragavan, Amit Sahai, STOC 2027 submission #531 (October 2026), Definitions 2.9–2.11, pp.14–15; §3, p.15

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Keys

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli

/-- Ciphertext and decryption effects of §3, p.15. -/
noncomputable def ciphertext {n : ℕ} (k : Key n) (m : Fin 2) : Op (Bits n) :=
  ((2 : ℂ)^n)⁻¹ • (1 + sign m • pauli k.val)

noncomputable def decryptEffect {n : ℕ} (k : Key n) (m : Fin 2) : Op (Bits n) :=
  (1/2 : ℂ) • (1 + sign m • pauli k.val)

/-- Data of a one-bit scheme. No correctness, efficiency, or security conclusion is a field. -/
structure Scheme (n : ℕ) where
  gen : Key n → ℝ
  enc : Key n → Fin 2 → Op (Bits n)
  dec : Key n → Fin 2 → Op (Bits n)

noncomputable def explicitScheme (n : ℕ) : Scheme n :=
  ⟨keyMass n, ciphertext, decryptEffect⟩

end PauliUnclonable531.Pauli


