-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0065PaddedInputs_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0065PaddedInputs_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T00:08:42.155436+00:00
-- url     : https://prove2.me/theorems/b2a779cc-c30d-4c28-b112-eff177c69633
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0065PaddedInputs (piece 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0065PaddedInputs (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0065PaddedInputs (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0065PaddedInputs (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0065PaddedInputs (piece 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0065StableWitnesses



/-! The six positive alpha intervals widened by 16777216 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisZero0065PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisZero0065StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerBAlpha : DyadicInterval precision := ⟨1773100709187079002379621286748650664284642978777, 1773100709187079002379621286748650664284676533210⟩
def centerBInput : Inputs precision :=
  { E8TAxisZero0065StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisZero0065StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisZero0065StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨722148521667251324704281592559239947598863483467, 722148521667251324704281592559239947598897037900⟩
def centerCInput : Inputs precision :=
  { E8TAxisZero0065StableWitnesses.centerCInput with alpha := centerCAlpha }

end GeneralCK.Certificates.E8TAxisZero0065PaddedInputs


