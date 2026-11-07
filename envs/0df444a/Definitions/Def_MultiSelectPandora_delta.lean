-- Prove2me | Definitions.Def_MultiSelectPandora_delta
-- name    : MultiSelectPandora_delta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:16:41.478196+00:00
-- url     : https://prove2.me/theorems/b9e68699-86a8-4937-b1c7-eb96beeec0cf
-- title:
--   The small grid width $\delta$
-- statement:
--   $\delta:=\theta\varepsilon^2$, the width of the additive grid for small values.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §3.3, p.14 (PDF p.15); p.33 (PDF p.34)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_theta

namespace MultiSelectPandora

/-- **The small grid width `δ = θ ε²`.** Beyhaghi–Han–Luqman manuscript, §3.3, p.14 (PDF p.15), and p.33 (PDF p.34). -/
noncomputable def delta (I : Inst) (k : ℕ) (ε : ℝ) : ℝ := theta I k ε * ε ^ 2

end MultiSelectPandora


