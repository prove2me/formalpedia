-- Prove2me | Definitions.Def_MultiSelectPandora_capped
-- name    : MultiSelectPandora_capped
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:07:28.009198+00:00
-- url     : https://prove2.me/theorems/f7e504d7-ba5a-448e-b290-857a6041fe9c
-- title:
--   The capped value $\kappa_i$
-- statement:
--   The capped value of box $i$ is $\kappa_i=\min\{v_i,\sigma_i\}$, here at each support position.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.3, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_resv

namespace MultiSelectPandora

/-- **The capped value `κ_i = min{v_i, σ_i}`**, at a support position. Beyhaghi–Han–Luqman manuscript, §2.3, p.6 (PDF p.7). -/
noncomputable def capped (I : Inst) (i : Fin I.n) (j : Fin (I.s i)) : ℝ := min (I.val i j) (resv I i)

end MultiSelectPandora


