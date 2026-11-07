-- Prove2me | Definitions.Def_MultiSelectPandora_Inst_dp
-- name    : MultiSelectPandora_Inst_dp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:09:46.004597+00:00
-- url     : https://prove2.me/theorems/d0dad32f-f263-468d-8073-fc637dfdd910
-- title:
--   The dynamic program of Table 1 for an instance
-- statement:
--   The program of Table 1 for an instance: $w=x=$ the value of the box and $b_i=E[v_i]$.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Table 1, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_Inst_mean
import Definitions.Def_MultiSelectPandora_DPData

namespace MultiSelectPandora

/-- **The dynamic program of Table 1 for an instance `I`.** Beyhaghi–Han–Luqman manuscript, Table 1, p.7 (PDF p.8). -/
noncomputable def Inst.dp (I : Inst) : DPData I.n I.s := ⟨I.c, I.prob, I.val, I.val, I.mean⟩

end MultiSelectPandora


