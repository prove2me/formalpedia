-- Prove2me | Definitions.Def_MultiSelectPandora_OPTC
-- name    : MultiSelectPandora_OPTC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:09:36.417269+00:00
-- url     : https://prove2.me/theorems/63c66087-45f1-4423-baff-52c3f2575956
-- title:
--   The closed-claim value $\mathrm{OPT}_C$
-- statement:
--   $\mathrm{OPT}_C$ is the utility of the policy that selects the $k$ boxes of largest mean without inspecting any box: the sum of the $k$ largest means, padded by zeros.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Lemma 3.8, p.9 (PDF p.10)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_Inst_mean
import Definitions.Def_MultiSelectPandora_topSum

namespace MultiSelectPandora

/-- **`OPT_C`, the utility of selecting the `k` boxes of largest mean without inspecting any box.** Beyhaghi–Han–Luqman
manuscript, Lemma 3.8, p.9 (PDF p.10). -/
noncomputable def OPTC (I : Inst) (k : ℕ) : ℝ := topSum k (List.ofFn I.mean)

end MultiSelectPandora


