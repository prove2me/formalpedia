-- Prove2me | Definitions.Def_MultiSelectPandora_Supplement_ClaimsClosed
-- name    : MultiSelectPandora_Supplement_ClaimsClosed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:32:12.161905+00:00
-- url     : https://prove2.me/theorems/f065f9f6-fc64-4686-82b0-60baa275346a
-- title:
--   A policy claims a box closed with positive probability
-- statement:
--   A state policy $\pi$ **claims a box closed with positive probability from $(U,\alpha)$** if there is a state reached with positive probability from $(U,\alpha)$ at which $\pi$ stops with a box claimed closed.
--
--   With $\hat k=1$, this is the condition "claims $\hat k$ boxes closed with positive probability" in the definition of the phase threshold (Definition 4.2).
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; preprint basis, sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Definition 4.2, p.18 (PDF p.19)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_Supplement_Reach

namespace MultiSelectPandora.Supplement

/-- **The policy claims a box closed with positive probability from `(U, α)`.** Beyhaghi–Han–Luqman, *Multi-Selection Pandora's Box with Nonobligatory Inspection*, manuscript (STOC 2027 submission), Definition 4.2,
p.18 (PDF p.19), with `k̂ = 1`: at some state reached with positive probability, the policy stops with a box claimed
closed. -/
def ClaimsClosed (I : Inst) {k : ℕ} (π : StPolicy I k) (U : Finset (Fin I.n)) (α : Fin k → ℝ) : Prop :=
  ∃ V β i, Reach I π U α V β ∧ π V β = .claimStop i

end MultiSelectPandora.Supplement


