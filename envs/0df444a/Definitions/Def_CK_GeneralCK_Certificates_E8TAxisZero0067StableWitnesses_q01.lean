-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0067StableWitnesses_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0067StableWitnesses_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:35:32.106355+00:00
-- url     : https://prove2.me/theorems/038049c1-5889-44eb-a8b6-e7727408b4e1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0067StableWitnesses (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0067StableWitnesses (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0067StableWitnesses (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0067StableWitnesses (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0067StableWitnesses (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0067StableWitnesses_q00

namespace GeneralCK.Certificates.E8TAxisZero0067StableWitnesses
open DyadicInterval E8TAxisStableInterval
set_option maxRecDepth 100000
def centerCExpWitness : ExpWitness precision :=
  ⟨561253440122644206774504521715991475159343049332, scale precision, 561253440122644206774504521715991476258854677109, scale precision,
    0, 512, 0, 512, ⟨-1398725956890982740223581726209546071473133612411, -1398725956890982740223581726209546071473131515258⟩, ⟨-1398725956890982740223581726209546068610009880093, -1398725956890982740223581726209546068610007782940⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1704968122347080814948624045692654969064877823851, 1704968122347080814948624045692654969064877823852⟩
def centerBExp : DyadicInterval precision := ⟨141747406577024884146444594530339844197429774445, 141747406577024884146444594530339846396453029998⟩
def centerBLog : DyadicInterval precision := ⟨135287986621489912865141689470010609166953491882, 135287986621489912865141689470010611365976747435⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨141747406577024884146444594530339844747185588333, scale precision, 141747406577024884146444594530339845846697216110, scale precision,
    0, 512, 0, 512, ⟨-3409936244694161629897248091385309943798072198708, -3409936244694161629897248091385309943798070101555⟩, ⟨-3409936244694161629897248091385309932461441193842, -3409936244694161629897248091385309932461439096689⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨693511205829020257423882496604739492695821414414, 704837076587479092158941059188951191105662022839⟩
def wholeDExp : DyadicInterval precision := ⟨557064765387537285209117120927584102725232557331, 565765939962058116901418666290376204947661904598⟩
def wholeDLog : DyadicInterval precision := ⟨471952686082951260798866870121334518051885287659, 478239054014281969770673762969782323901449402529⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨557064765387537285209117120927584103274988371219, scale precision, 565765939962058116901418666290376204397906090710, scale precision,
    0, 512, 0, 512, ⟨-1409674153174958184317882118377902383653651143312, -1409674153174958184317882118377902383653649046159⟩, ⟨-1387022411658040514847764993209478983971500023954, -1387022411658040514847764993209478983971497926801⟩⟩
end GeneralCK.Certificates.E8TAxisZero0067StableWitnesses


