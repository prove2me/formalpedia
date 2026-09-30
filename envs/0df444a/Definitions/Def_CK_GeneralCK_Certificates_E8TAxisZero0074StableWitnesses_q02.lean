-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0074StableWitnesses_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0074StableWitnesses_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:39:51.409695+00:00
-- url     : https://prove2.me/theorems/7d222099-3408-4756-9fa2-19ab28e42c24
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0074StableWitnesses (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0074StableWitnesses (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0074StableWitnesses (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0074StableWitnesses (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0074StableWitnesses (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0074StableWitnesses_q01

namespace GeneralCK.Certificates.E8TAxisZero0074StableWitnesses
open DyadicInterval E8TAxisStableInterval
set_option maxRecDepth 100000
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨615985792935344704096715461380744242879788980549, 627259614167087449859646268174292653717877577320⟩
def wholeCExp : DyadicInterval precision := ⟨619456707788915396279231795820783166562864949143, 629087614762237432177832619094338713110027667137⟩
def wholeCLog : DyadicInterval precision := ⟨516442217407178209762297451045170045954452475711, 523190605620864448684409715253755541203210012554⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨619456707788915396279231795820783167112620763031, scale precision, 629087614762237432177832619094338712560271853249, scale precision,
    0, 512, 0, 512, ⟨-1254519228334174899719292536348585308732810560731, -1254519228334174899719292536348585308732808463578⟩, ⟨-1231971585870689408193430922761488484482381679326, -1231971585870689408193430922761488484482379582173⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1458553519812871335103393647216521494219408109578, 1490989288915208105794532223244031738659815900255⟩
def wholeBExp : DyadicInterval precision := ⟨189970189966061363702036052536952022089734334097, 198592318493871213883856995355578141720334372525⟩
def wholeBLog : DyadicInterval precision := ⟨178599126021686680927547529039288241162025991358, 186209594458958596667063557514777784347923070369⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨189970189966061363702036052536952022639490147985, scale precision, 198592318493871213883856995355578141170578558637, scale precision,
    0, 512, 0, 512, ⟨-2981978577830416211589064446488063481549080754958, -2981978577830416211589064446488063481549078657805⟩, ⟨-2917107039625742670206787294433042984392996018337, -2917107039625742670206787294433042984392993921184⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

end GeneralCK.Certificates.E8TAxisZero0074StableWitnesses


