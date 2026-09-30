-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0059PaddedInputs_part00
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0059PaddedInputs_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:47:16.078567+00:00
-- url     : https://prove2.me/theorems/eafb1cd3-80df-435a-89f2-159cf18e2357
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0059PaddedInputs (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0059PaddedInputs (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0059PaddedInputs (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0059PaddedInputs (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0059PaddedInputs (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0059StableWitnesses

/-! The six positive alpha intervals widened by 16777216 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisZero0059PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisZero0059StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerBAlpha : DyadicInterval precision := ⟨1982589189183638945330647538915323850639115452363, 1982589189183638945330647538915323850639149006796⟩
def centerBInput : Inputs precision :=
  { E8TAxisZero0059StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisZero0059StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisZero0059StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨792145084263579129855347152782070571944229890787, 792145084263579129855347152782070571944263445220⟩
def centerCInput : Inputs precision :=
  { E8TAxisZero0059StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisZero0059StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisZero0059StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨791938512842554261609794269869582385953276129350, 791938512842554261609794269869582385953309683783⟩
def centerDInput : Inputs precision :=
  { E8TAxisZero0059StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisZero0059StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisZero0059StableWitnesses.centerDLogWitness = true := by decide

end GeneralCK.Certificates.E8TAxisZero0059PaddedInputs


