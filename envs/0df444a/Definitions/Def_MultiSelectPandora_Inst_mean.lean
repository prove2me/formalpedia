-- Prove2me | Definitions.Def_MultiSelectPandora_Inst_mean
-- name    : MultiSelectPandora_Inst_mean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:01:59.209353+00:00
-- url     : https://prove2.me/theorems/4e3d5f21-5838-4d7e-a707-36d4d542e99d
-- title:
--   The mean $E[v_i]$
-- statement:
--   The mean of box $i$ is
--   $$E[v_i]=\sum_j \mathrm{prob}_{ij}\,\mathrm{val}_{ij}.$$
--   A box claimed closed contributes this quantity in expectation, since the decision to select it does not depend on $v_i$.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.1, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst

namespace MultiSelectPandora

/-- **The mean `E[v_i]`.** Beyhaghi–Han–Luqman manuscript, §2.1, p.5 (PDF p.6). -/
noncomputable def Inst.mean (I : Inst) (i : Fin I.n) : ℝ := ∑ j, I.prob i j * I.val i j

end MultiSelectPandora


