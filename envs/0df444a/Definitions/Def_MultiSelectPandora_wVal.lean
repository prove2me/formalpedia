-- Prove2me | Definitions.Def_MultiSelectPandora_wVal
-- name    : MultiSelectPandora_wVal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:20:57.574585+00:00
-- url     : https://prove2.me/theorems/9fc41562-3ed3-4196-8953-e4b3cffa3d80
-- title:
--   The value $w_i$
-- statement:
--   $w_i:=D^S(v_i)$ if $v_i<\theta$, and $w_i:=v_i$ otherwise, here at each support position. Small values are rounded down and large values are kept.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §3.3, p.14 (PDF p.15)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_theta
import Definitions.Def_MultiSelectPandora_DS

namespace MultiSelectPandora

/-- **The value `w_i`**: `D^S(v_i)` if `v_i < θ`, and `v_i` otherwise. Beyhaghi–Han–Luqman manuscript, §3.3, p.14 (PDF p.15). -/
noncomputable def wVal (I : Inst) (k : ℕ) (ε : ℝ) (i : Fin I.n) (j : Fin (I.s i)) : ℝ :=
  if I.val i j < theta I k ε then DS I k ε (I.val i j) else I.val i j

end MultiSelectPandora


