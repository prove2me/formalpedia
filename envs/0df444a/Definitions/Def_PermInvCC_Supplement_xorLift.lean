-- Prove2me | Definitions.Def_PermInvCC_Supplement_xorLift
-- name    : PermInvCC_Supplement_xorLift
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:55:58.373203+00:00
-- url     : https://prove2.me/theorems/e1413bce-ec34-4cb7-b618-c87186ff4f9a
-- title:
--   The XOR communication problem $F^{\oplus}_s(A,B)=\psi(A\oplus B)$
-- statement:
--   Let $\psi : \{0,1\}^s \to \{-1,+1,*\}$ be a partial function. The associated **XOR communication problem** gives Alice $A \in \{0,1\}^s$ and Bob $B \in \{0,1\}^s$ and asks for
--
--   $$F^{\oplus}_s(A,B) := \psi(A \oplus B),$$
--
--   where $\oplus$ is bitwise XOR. The value is undefined exactly when $\psi$ is undefined at $A \oplus B$.
--
--   XOR problems are invariant under masking both inputs by the same string, which is what the permutation and tree encodings of Section 5 exploit.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), eq. (5.2), p.23 (PDF p.26)

import Mathlib

namespace PermInvCC

namespace Supplement

/-- The **XOR communication problem** `F⊕_s(A, B) := ψ(A ⊕ B)` of a partial function
`ψ : {0,1}^s → {−1, +1, ∗}` (Y. Huang and Z. Ye, *Quantum Advantage of Permutation-Invariant Functions in Communication
Complexity*, arXiv:2609.40116, held version sha256 fe1797dd…, eq. (5.2), p.23). It is undefined precisely when `ψ`
is undefined at `A ⊕ B`.

**Formalization Note.** Bits are `Bool` (`true` = `1`), `⊕` is the coordinatewise `xor`;
outputs are `Option Bool` (`none` = `∗`, `some true` = `+1`). -/
def xorLift {s : ℕ} (ψ : (Fin s → Bool) → Option Bool) :
    (Fin s → Bool) → (Fin s → Bool) → Option Bool :=
  fun A B => ψ (fun i => xor (A i) (B i))

end Supplement

end PermInvCC


