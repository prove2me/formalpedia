-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0058StableWitnesses
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0058StableWitnesses
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:21:03.026683+00:00
-- url     : https://prove2.me/theorems/8f2c1f73-e6dd-4074-ab2c-f7d48ec658a6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0058StableWitnesses` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0058StableWitnesses` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0058StableWitnesses` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0058StableWitnesses (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0058StableWitnesses.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0058StableWitnesses_part00

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0058StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def wholeBExp : DyadicInterval precision := ⟨90075620461155625479445933360596292562576573043, 94656915849614517468722431185936370177487098420⟩
def wholeBLog : DyadicInterval precision := ⟨87408866356896010681788141047106498620180794323, 91717839814575753064654839892652257885364251183⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨90075620461155625479445933360596293112332386931, scale precision, 94656915849614517468722431185936369627731284532, scale precision,
    0, 512, 0, 512, ⟨-4072576851342575988616116524744481193249545562570, -4072576851342575988616116524744481193249543465417⟩, ⟨-4000072635352994001013412331631239103451117423255, -4000072635352994001013412331631239103451115326102⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0058StableWitnesses


