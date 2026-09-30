-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0067StableWitnesses_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0067StableWitnesses_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:42:08.429565+00:00
-- url     : https://prove2.me/theorems/f61bad43-9b28-447e-84da-26edd9459080
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0067StableWitnesses (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0067StableWitnesses (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0067StableWitnesses (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0067StableWitnesses (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0067StableWitnesses (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0067StableWitnesses_q01

namespace GeneralCK.Certificates.E8TAxisZero0067StableWitnesses
open DyadicInterval E8TAxisStableInterval
set_option maxRecDepth 100000
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨693511205829020257423882496604739492695821414414, 705232195447749529846185115854158530882609513903⟩
def wholeCExp : DyadicInterval precision := ⟨556763640442969877903307630244600432196176329900, 565765939962058116901418666290376204947661904598⟩
def wholeCLog : DyadicInterval precision := ⟨471734646474082036318131261500638378838631284483, 478239054014281969770673762969782323901449402529⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨556763640442969877903307630244600432745932143788, scale precision, 565765939962058116901418666290376204397906090710, scale precision,
    0, 512, 0, 512, ⟨-1410464390895499059692370231708317063208326205746, -1410464390895499059692370231708317063208324108593⟩, ⟨-1387022411658040514847764993209478983971500023954, -1387022411658040514847764993209478983971497926801⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1687792230159663909779056938834163267773279649832, 1722207537783939284051018161965604178270685889103⟩
def wholeBExp : DyadicInterval precision := ⟨138442527176722213024059573691808629251161388270, 145118564043866684838885550097705947306201030064⟩
def wholeBLog : DyadicInterval precision := ⟨132272190786316562849960840484993253946287174871, 138357864920265176276282420721216898953574725790⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨138442527176722213024059573691808629800917202158, scale precision, 145118564043866684838885550097705946756445216176, scale precision,
    0, 512, 0, 512, ⟨-3444415075567878568102036323931208362345001513111, -3444415075567878568102036323931208362344999415958⟩, ⟨-3375584460319327819558113877668326530009921893862, -3375584460319327819558113877668326530009919796709⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

end GeneralCK.Certificates.E8TAxisZero0067StableWitnesses


