-- Prove2me | Definitions.Def_MultiSelectPandora_IS
-- name    : MultiSelectPandora_IS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:23:49.14579+00:00
-- url     : https://prove2.me/theorems/1277674a-66a7-4648-af84-8fff97344eab
-- title:
--   The small-value discretization $I^S$
-- statement:
--   $I^S$ is the dynamic program of Table 1 with $v_i$ replaced by $w_i$ and $E[v_i]$ replaced by $b_i$, in both the transition and the marginal reward.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Definition 3.19, p.14 (PDF p.15)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_DPData
import Definitions.Def_MultiSelectPandora_wVal
import Definitions.Def_MultiSelectPandora_bVal

namespace MultiSelectPandora

/-- **The program `I^S`.** Beyhaghi–Han–Luqman manuscript, Definition 3.19, p.14 (PDF p.15): "the SSDP of Table 1 with `v_i`
replaced by `w_i` and `E[v_i]` replaced by `b_i`". -/
noncomputable def IS (I : Inst) (k : ℕ) (ε : ℝ) : DPData I.n I.s :=
  ⟨I.c, I.prob, wVal I k ε, wVal I k ε, bVal I k ε⟩

end MultiSelectPandora


