-- Prove2me | Definitions.Def_ITPIRPreproc_MatchVec_ActivationPaddedEncoding
-- name    : ITPIRPreproc_MatchVec_ActivationPaddedEncoding
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:31:45.903038+00:00
-- url     : https://prove2.me/theorems/bfafc29e-474b-410e-b888-6aa1a39af1a8
-- title:
--   Claim 6.2.4 — length-correct activation codes on real and placeholder sizes
-- statement:
--   Length-correct wrappers for the concrete activation codes. On a real size the key is its row-major Boolean matrix followed by its activation vector, and hint/answer vectors use two bits per $\mathbb F_3$ coordinate. On the placeholder sizes of `actFamily`, false padding gives exactly the lengths required by `OfflineEfficiency.CodesProps`: $(\lfloor\log_2m\rfloor+1)\dim$ for a key and $2\dim$ for a hint or answer. `ActCode.impl` combines these codes with the public table and seven programs.
-- source:
--   Claim 6.2.4(i), printed p.23 (PDF p.25), together with the universally quantified code-length interface `OfflineEfficiency.CodesProps`; the placeholder branch is Definition `actFamily`, printed pp.20–21.

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_ActivationEncoding

open scoped ENNReal

namespace ITPIRPreproc.MatchVec

open WordRAM

namespace ActCode

/-- Fixed-width key code. The placeholder branch is padded to the advertised length. -/
noncomputable def encKey (dim : ℕ → ℕ)
    (u v : ∀ h : ℕ, Fin (2 ^ h) → Fin (dim h) → ZMod 6) (m : ℕ)
    (K : (actFamily dim u v m).Key) : List Bool :=
  if hm : 2 ^ Nat.log 2 m = m then
    encActKeyRaw (h := Nat.log 2 m) (d := dim (Nat.log 2 m)) (cast (by
      unfold actFamily
      rw [dif_pos hm]
      exact castOCHPKey hm _) K)
  else List.replicate ((Nat.log 2 m + 1) * dim (Nat.log 2 m)) false

/-- Two-bit-per-coordinate hint code. The placeholder branch is padded to length `2 * dim`. -/
noncomputable def encHint (dim : ℕ → ℕ)
    (u v : ∀ h : ℕ, Fin (2 ^ h) → Fin (dim h) → ZMod 6) (m : ℕ)
    (z : (actFamily dim u v m).HintVal) : List Bool :=
  if hm : 2 ^ Nat.log 2 m = m then
    encF3Vec (d := dim (Nat.log 2 m)) (cast (by
      unfold actFamily
      rw [dif_pos hm]
      exact castOCHPHintVal hm _) z)
  else List.replicate (2 * dim (Nat.log 2 m)) false

/-- One-bit secret code, with the empty code on the placeholder branch. -/
noncomputable def encSecret (dim : ℕ → ℕ)
    (u v : ∀ h : ℕ, Fin (2 ^ h) → Fin (dim h) → ZMod 6) (m : ℕ)
    (s : (actFamily dim u v m).Secret) : List Bool :=
  if hm : 2 ^ Nat.log 2 m = m then
    encF2 (cast (by
      unfold actFamily
      rw [dif_pos hm]
      exact castOCHPSecret hm _) s)
  else []

/-- Two-bit-per-coordinate answer code. The placeholder branch is padded to length `2 * dim`. -/
noncomputable def encAns (dim : ℕ → ℕ)
    (u v : ∀ h : ℕ, Fin (2 ^ h) → Fin (dim h) → ZMod 6) (m : ℕ)
    (a : (actFamily dim u v m).AnsVal) : List Bool :=
  if hm : 2 ^ Nat.log 2 m = m then
    encF3Vec (d := dim (Nat.log 2 m)) (cast (by
      unfold actFamily
      rw [dif_pos hm]
      exact castOCHPAnsVal hm _) a)
  else List.replicate (2 * dim (Nat.log 2 m)) false

/-- Assemble the activation implementation with length-correct codes on every size. -/
noncomputable def impl (dim : ℕ → ℕ)
    (u v : ∀ h : ℕ, Fin (2 ^ h) → Fin (dim h) → ZMod 6)
    (p : ActPrograms) : OCHPImpl (actFamily dim u v) where
  encKey := encKey dim u v
  encHint := encHint dim u v
  encSecret := encSecret dim u v
  encAns := encAns dim u v
  table := actTable dim u v
  tableProg := p.table
  sampleKey := p.sampleKey
  sampleCompat := p.sampleCompat
  testCompat := p.testCompat
  query := p.query
  answer := p.answer
  decode := p.decode
  streamInit := [Instr.halt]
  streamChunk := [Instr.halt]

end ActCode

end ITPIRPreproc.MatchVec


