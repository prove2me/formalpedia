-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0065StableWitnesses
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0065StableWitnesses
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:10:34.835245+00:00
-- url     : https://prove2.me/theorems/d1c6b086-ff28-4d7f-b280-11108988a708
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0065StableWitnesses` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0065StableWitnesses` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0065StableWitnesses` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0065StableWitnesses (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0065StableWitnesses.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0065StableWitnesses_part00

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0065StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def wholeBAlpha : DyadicInterval precision := ⟨1755682615968192604006724080732632442415725328902, 1790577155268251264318358183860781884375991453423⟩
def wholeBExp : DyadicInterval precision := ⟨126077209366697777120126321300719760996015969096, 132243658317910108282970638394685413084573618561⟩
def wholeBLog : DyadicInterval precision := ⟨120932964172539280471025078043449528589273314215, 126598709706290185816284609458792175714656533056⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨126077209366697777120126321300719761545771782984, scale precision, 132243658317910108282970638394685412534817804673, scale precision,
    0, 512, 0, 512, ⟨-3581154310536502528636716367721563775124817127775, -3581154310536502528636716367721563775124815030622⟩, ⟨-3511365231936385208013448161465264878755780234868, -3511365231936385208013448161465264878755778137715⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0065StableWitnesses


