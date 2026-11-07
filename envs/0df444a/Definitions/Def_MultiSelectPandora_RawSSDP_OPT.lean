-- Prove2me | Definitions.Def_MultiSelectPandora_RawSSDP_OPT
-- name    : MultiSelectPandora_RawSSDP_OPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:14:19.811562+00:00
-- url     : https://prove2.me/theorems/c39e689c-8ba4-454f-ae61-a51356b372b7
-- title:
--   $\mathrm{OPT}$ of a table
-- statement:
--   $\mathrm{OPT}:=\mathrm{DP}_1(I_0,A)$, the expected total reward of an optimal policy from the initial state with all actions available.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), p.8 (PDF p.9)

import Mathlib
import Definitions.Def_MultiSelectPandora_RawSSDP
import Definitions.Def_MultiSelectPandora_RawSSDP_dp

namespace MultiSelectPandora

/-- **`OPT := DP_1(I_0, A)`.** Beyhaghi–Han–Luqman manuscript, p.8 (PDF p.9). -/
noncomputable def RawSSDP.OPT (S : RawSSDP) : ℝ := S.dp S.T S.init ∅

end MultiSelectPandora


