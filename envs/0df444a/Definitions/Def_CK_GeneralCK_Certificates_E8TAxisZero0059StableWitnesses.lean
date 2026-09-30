-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0059StableWitnesses
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0059StableWitnesses
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:24:34.498694+00:00
-- url     : https://prove2.me/theorems/16838221-4950-4fa2-bb9a-1dc58cf490c4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0059StableWitnesses` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0059StableWitnesses` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0059StableWitnesses` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0059StableWitnesses (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0059StableWitnesses.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0059StableWitnesses_part00

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0059StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1964566720915303568265002566982811316140955122603, 2000654635874828483152190903567570468179077468487⟩
def wholeBExp : DyadicInterval precision := ⟨94576856631551132389347987250451794057312945784, 99364758494610413242620804050350958107765410810⟩
def wholeBLog : DyadicInterval precision := ⟨91642648448020760238509852839706620888976505285, 96132642441103135872971199892542468584709881596⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨94576856631551132389347987250451794607068759672, scale precision, 99364758494610413242620804050350957558009596922, scale precision,
    0, 512, 0, 512, ⟨-4001309271749656966304381807135140944853564384039, -4001309271749656966304381807135140944853562286886⟩, ⟨-3929133441830607136530005133965622624195855087313, -3929133441830607136530005133965622624195852990160⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0059StableWitnesses


