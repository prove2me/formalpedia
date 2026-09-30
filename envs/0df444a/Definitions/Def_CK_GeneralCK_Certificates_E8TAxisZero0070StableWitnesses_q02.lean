-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0070StableWitnesses_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0070StableWitnesses_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:59:54.517287+00:00
-- url     : https://prove2.me/theorems/32b9b47e-ceab-4e44-adf5-3c73218ca594
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0070StableWitnesses (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0070StableWitnesses (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0070StableWitnesses (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0070StableWitnesses (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0070StableWitnesses (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0070StableWitnesses_q01

namespace GeneralCK.Certificates.E8TAxisZero0070StableWitnesses
open DyadicInterval E8TAxisStableInterval
set_option maxRecDepth 100000
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨659917674403335303398947154306570012946022027567, 671440902009004248126867720023776049226259723644⟩
def wholeCExp : DyadicInterval precision := ⟨583113988827986525171167068164318273703777149267, 592382009410612930615839145836493983293758080466⟩
def wholeCLog : DyadicInterval precision := ⟨490692434409458928876431019351388739891276992838, 497302293015079090720897450218278679747777485235⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨583113988827986525171167068164318274253532963155, scale precision, 592382009410612930615839145836493982744002266578, scale precision,
    0, 512, 0, 512, ⟨-1342881804018008496253735440047552099830414076747, -1342881804018008496253735440047552099830411979594⟩, ⟨-1319835348806670606797894308613140024535709142512, -1319835348806670606797894308613140024535707045359⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1587858894860446235976143311582642247749986908573, 1621480652225727667592799454759990618247396507032⟩
def wholeBExp : DyadicInterval precision := ⟨158903251675320738035825572853393161165096756993, 166385172499093390938202185071882484034692793653⟩
def wholeBLog : DyadicInterval precision := ⟨150843956919355702479650421140762543422956226422, 157576639748373200749695980667750104182903754501⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨158903251675320738035825572853393161714852570881, scale precision, 166385172499093390938202185071882483484936979765, scale precision,
    0, 512, 0, 512, ⟨-3242961304451455335185598909519981241551135035276, -3242961304451455335185598909519981241551132938123⟩, ⟨-3175717789720892471952286623165284490671004771443, -3175717789720892471952286623165284490671002674290⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

end GeneralCK.Certificates.E8TAxisZero0070StableWitnesses


