-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0070PaddedInputs_part00
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0070PaddedInputs_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:43:17.15027+00:00
-- url     : https://prove2.me/theorems/8d5d4355-93d2-43e8-b846-a235af6f2537
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0070PaddedInputs (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0070PaddedInputs (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0070PaddedInputs (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0070PaddedInputs (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0070PaddedInputs (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0070StableWitnesses

/-! The six positive alpha intervals widened by 16777216 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisZero0070PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisZero0070StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerBAlpha : DyadicInterval precision := ⟨1604634301185043853054582563588557416108314861880, 1604634301185043853054582563588557416108348416313⟩
def centerBInput : Inputs precision :=
  { E8TAxisZero0070StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisZero0070StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisZero0070StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨665670958141235826866978701625655109648381776052, 665670958141235826866978701625655109648415330485⟩
def centerCInput : Inputs precision :=
  { E8TAxisZero0070StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisZero0070StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisZero0070StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨665477300625433477361232002502002625345904689903, 665477300625433477361232002502002625345938244336⟩
def centerDInput : Inputs precision :=
  { E8TAxisZero0070StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisZero0070StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisZero0070StableWitnesses.centerDLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1587858894860446235976143311582642247749970131357, 1621480652225727667592799454759990618247413284248⟩
def wholeBInput : Inputs precision :=
  { E8TAxisZero0070StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisZero0070StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisZero0070StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨659917674403335303398947154306570012946005250351, 671440902009004248126867720023776049226276500860⟩
def wholeCInput : Inputs precision :=
  { E8TAxisZero0070StableWitnesses.wholeCInput with alpha := wholeCAlpha }

end GeneralCK.Certificates.E8TAxisZero0070PaddedInputs


