-- Prove2me | Definitions.Def_MultiSelectPandora_OPThat
-- name    : MultiSelectPandora_OPThat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:11:14.874881+00:00
-- url     : https://prove2.me/theorems/2bac9370-ffdf-4f25-98a9-6d628d17b458
-- title:
--   The estimate $\widehat{\mathrm{OPT}}$
-- statement:
--   $\widehat{\mathrm{OPT}}=W(M,0)+\mathrm{OPT}_C$. By Lemma 3.8, $\mathrm{OPT}\le\widehat{\mathrm{OPT}}\le2\,\mathrm{OPT}$.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), p.9 (PDF p.10)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_W
import Definitions.Def_MultiSelectPandora_OPTC

namespace MultiSelectPandora

/-- **The estimate `OPT^ = W(M, 0) + OPT_C`.** Beyhaghi–Han–Luqman manuscript, p.9 (PDF p.10). -/
noncomputable def OPThat (I : Inst) (k : ℕ) : ℝ := W I Finset.univ (0 : Fin k → ℝ) + OPTC I k

end MultiSelectPandora


