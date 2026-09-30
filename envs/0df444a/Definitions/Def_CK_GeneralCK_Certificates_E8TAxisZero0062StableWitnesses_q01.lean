-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0062StableWitnesses_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0062StableWitnesses_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:34:29.651258+00:00
-- url     : https://prove2.me/theorems/d1899d09-d20b-4e6b-a1b3-9b591354fa56
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0062StableWitnesses (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0062StableWitnesses (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0062StableWitnesses (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0062StableWitnesses (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0062StableWitnesses (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0062StableWitnesses_q00

namespace GeneralCK.Certificates.E8TAxisZero0062StableWitnesses
open DyadicInterval E8TAxisStableInterval
set_option maxRecDepth 100000
def centerCExpWitness : ExpWitness precision :=
  ⟨518805130142806436748687029750699748336760909114, scale precision, 518805130142806436748687029750699749436272536891, scale precision,
    0, 512, 0, 512, ⟨-1513664624236456124910134966050543613263689928325, -1513664624236456124910134966050543613263687831172⟩, ⟨-1513664624236456124910134966050543610166307210043, -1513664624236456124910134966050543610166305112890⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1876965577002086047564386724248516624714020356787, 1876965577002086047564386724248516624714020356788⟩
def centerBExp : DyadicInterval precision := ⟨112019815353976191716123862023179485494978941137, 112019815353976191716123862023179487694002196690⟩
def centerBLog : DyadicInterval precision := ⟨107934300509666094433933604389802079020377989599, 107934300509666094433933604389802081219401245152⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨112019815353976191716123862023179486044734755025, scale precision, 112019815353976191716123862023179487144246382802, scale precision,
    0, 512, 0, 512, ⟨-3753931154004172095128773448497033256600603327184, -3753931154004172095128773448497033256600601230031⟩, ⟨-3753931154004172095128773448497033242255480197115, -3753931154004172095128773448497033242255478099962⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨750806424999049798752938234956163650116084001297, 762469961061176672454638714549067897721941573493⟩
def wholeDExp : DyadicInterval precision := ⟨514818014850194000087183801285808384916278939514, 523100967242339682629524513379347097451596710168⟩
def wholeDLog : DyadicInterval precision := ⟨441040166381185817721359138930122616152471066865, 447152665109602019123525890115620511802318039062⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨514818014850194000087183801285808385466034753402, scale precision, 523100967242339682629524513379347096901840896280, scale precision,
    0, 512, 0, 512, ⟨-1524939922122353344909277429098135797004569717344, -1524939922122353344909277429098135797004567620191⟩, ⟨-1501612849998099597505876469912327298696195936143, -1501612849998099597505876469912327298696193838990⟩⟩
end GeneralCK.Certificates.E8TAxisZero0062StableWitnesses


