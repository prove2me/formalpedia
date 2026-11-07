-- Prove2me | Definitions.Def_MultiSelectPandora_bVal
-- name    : MultiSelectPandora_bVal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:21:32.782201+00:00
-- url     : https://prove2.me/theorems/dc6700e8-d9b9-4a17-b8c7-34d921b697a4
-- title:
--   The closed-claim constant $b_i$
-- statement:
--   $b_i:=D^S(E[v_i])$.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §3.3, p.14 (PDF p.15)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_Inst_mean
import Definitions.Def_MultiSelectPandora_DS

namespace MultiSelectPandora

/-- **The constant `b_i = D^S(E[v_i])`.** Beyhaghi–Han–Luqman manuscript, §3.3, p.14 (PDF p.15). -/
noncomputable def bVal (I : Inst) (k : ℕ) (ε : ℝ) (i : Fin I.n) : ℝ := DS I k ε (I.mean i)

end MultiSelectPandora


