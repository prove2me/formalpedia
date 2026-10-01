-- Prove2me | Definitions.Def_CK_CKLaneN1b_Cert
-- name    : CK_CKLaneN1b_Cert
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T08:15:14.134305+00:00
-- url     : https://prove2.me/theorems/8835a9f8-e342-4254-84e0-e3489c4256ce
-- title:
--   Courtade–Kumar proof module `CKLaneN1b.Cert` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1b.Cert` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1b.Cert` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1b.Cert (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1b/Cert.lean)

import Definitions.Def_CK_CKLaneN1b_CapChecker

-- ===== source module CKLaneN1b.Cert =====
section

/-!
# Lane N1b: certificate trees over an archived leaf box

A certificate is a binary refinement of a box (splits in `a`, `b` or `t`) whose leaves are
plane cells (`PCCell`), cap cells (`CapCell`) or irrelevant cells (`b1 - a0 < 1/50`).
`checkCert_sound : checkCert B t = true → Sem B` has no other hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneN1b

open GeneralCK

/-- Stored fixed-point log bound `z / 2^48`. -/
def fx (z : ℤ) : ℚ := (z : ℚ) / 281474976710656

/-- A certificate tree. -/
inductive Cert where
  | pc (c : PCCell)
  | cap (c : CapCell)
  | out
  | splitA (m : ℚ) (l r : Cert)
  | splitB (m : ℚ) (l r : Cert)
  | splitT (m : ℚ) (l r : Cert)
  deriving Repr

/-- The Boolean certificate checker. -/
def checkCert : Box → Cert → Bool
  | B, .pc c => PCCell.ok B c
  | B, .cap c => CapCell.ok B c
  | B, .out => decide (B.b1 - B.a0 < DMIN)
  | B, .splitA m l r =>
      decide (B.a0 ≤ m ∧ m ≤ B.a1) && checkCert { B with a1 := m } l &&
        checkCert { B with a0 := m } r
  | B, .splitB m l r =>
      decide (B.b0 ≤ m ∧ m ≤ B.b1) && checkCert { B with b1 := m } l &&
        checkCert { B with b0 := m } r
  | B, .splitT m l r =>
      decide (B.t0 ≤ m ∧ m ≤ B.t1) && checkCert { B with t1 := m } l &&
        checkCert { B with t0 := m } r

/-- Unconditional soundness of the certificate checker. -/
theorem checkCert_sound : ∀ (B : Box) (t : Cert), checkCert B t = true → Sem B
  | B, .pc c, h => PCCell.ok_sound h
  | B, .cap c, h => CapCell.ok_sound h
  | B, .out, h => sem_of_outside (of_decide_eq_true h)
  | B, .splitA m l r, h => by
      simp only [checkCert, Bool.and_eq_true] at h
      exact sem_splitA (checkCert_sound _ l h.1.2) (checkCert_sound _ r h.2)
  | B, .splitB m l r, h => by
      simp only [checkCert, Bool.and_eq_true] at h
      exact sem_splitB (checkCert_sound _ l h.1.2) (checkCert_sound _ r h.2)
  | B, .splitT m l r, h => by
      simp only [checkCert, Bool.and_eq_true] at h
      exact sem_splitT (checkCert_sound _ l h.1.2) (checkCert_sound _ r h.2)

end CKLaneN1b

end


