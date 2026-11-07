-- Prove2me | Definitions.Def_MultiSelectPandora_RawSSDP_terminal
-- name    : MultiSelectPandora_RawSSDP_terminal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:10:09.971988+00:00
-- url     : https://prove2.me/theorems/60fd2c2d-1979-4045-a22a-114131c8ab69
-- title:
--   The terminal reward of a state
-- statement:
--   The terminal reward $h(I)$ of state $I$, as a real number.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §3.1, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_MultiSelectPandora_RawSSDP

namespace MultiSelectPandora

/-- **The terminal reward `h` of a state.** Beyhaghi–Han–Luqman manuscript, §3.1, p.7 (PDF p.8). -/
noncomputable def RawSSDP.terminal (S : RawSSDP) (st : ℕ) : ℝ := ((S.h.getD st 0 : ℚ) : ℝ)

end MultiSelectPandora


