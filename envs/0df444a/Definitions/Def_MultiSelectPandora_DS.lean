-- Prove2me | Definitions.Def_MultiSelectPandora_DS
-- name    : MultiSelectPandora_DS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:18:28.052187+00:00
-- url     : https://prove2.me/theorems/4b3257fa-99f7-48b2-b1ff-3955228a0db8
-- title:
--   The small-value rounding $D^S$
-- statement:
--   $D^S(v)=\lfloor v/(\theta\varepsilon^2)\rfloor\cdot\theta\varepsilon^2$: a value rounded down to the small grid.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §3.3, p.14 (PDF p.15)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_delta

namespace MultiSelectPandora

/-- **The small-value rounding `D^S(v) = ⌊v/(θε²)⌋ · θε²`.** Beyhaghi–Han–Luqman manuscript, §3.3, p.14 (PDF p.15). -/
noncomputable def DS (I : Inst) (k : ℕ) (ε v : ℝ) : ℝ := (⌊v / delta I k ε⌋ : ℝ) * delta I k ε

end MultiSelectPandora


