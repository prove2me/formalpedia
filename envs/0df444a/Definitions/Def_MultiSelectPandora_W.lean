-- Prove2me | Definitions.Def_MultiSelectPandora_W
-- name    : MultiSelectPandora_W
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:07:26.616692+00:00
-- url     : https://prove2.me/theorems/265bcbfe-60b1-4ab2-bbe6-d2c974068342
-- title:
--   The value $W(U,\alpha)$ with obligatory inspection
-- statement:
--   $W(U,\alpha)=\mathrm{OPT}(U,\alpha,0)$ is the optimal expected utility of $P(U,\alpha,0)$: Pandora's box with $k$ selections, no closed claim allowed, and outside options $\alpha$.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.3, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_optState

namespace MultiSelectPandora

/-- **`W(U, α)`, the optimal expected utility of `P(U, α, 0)`.** Beyhaghi–Han–Luqman manuscript, §2.3, p.6 (PDF p.7):
Pandora's box with `k` selections and obligatory inspection, from the outside options `α`. -/
noncomputable def W (I : Inst) {k : ℕ} (U : Finset (Fin I.n)) (α : Fin k → ℝ) : ℝ := optState I U α 0

end MultiSelectPandora


