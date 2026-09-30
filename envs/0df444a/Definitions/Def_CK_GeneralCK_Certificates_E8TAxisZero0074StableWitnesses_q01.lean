-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0074StableWitnesses_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0074StableWitnesses_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:33:29.489233+00:00
-- url     : https://prove2.me/theorems/3e6d1aa5-4296-461c-9c9d-efe4aacdaa91
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0074StableWitnesses (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0074StableWitnesses (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0074StableWitnesses (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0074StableWitnesses (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0074StableWitnesses (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0074StableWitnesses_q00

namespace GeneralCK.Certificates.E8TAxisZero0074StableWitnesses
open DyadicInterval E8TAxisStableInterval
set_option maxRecDepth 100000
def centerCExpWitness : ExpWitness precision :=
  ⟨624260250820734232483487843934177037112624537372, scale precision, 624260250820734232483487843934177038212136165149, scale precision,
    0, 512, 0, 512, ⟨-1243229809362588863797950668849628870531899482511, -1243229809362588863797950668849628870531897385358⟩, ⟨-1243229809362588863797950668849628867957751853941, -1243229809362588863797950668849628867957749756788⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1474731613796848174839420339042273044204714042720, 1474731613796848174839420339042273044204714042721⟩
def centerBExp : DyadicInterval precision := ⟨194243994103149141824528274649774670312014681241, 194243994103149141824528274649774672511037936794⟩
def centerBLog : DyadicInterval precision := ⟨182376425397288727342961979936284917699480258685, 182376425397288727342961979936284919898503514238⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨194243994103149141824528274649774670861770495129, scale precision, 194243994103149141824528274649774671961282122906, scale precision,
    0, 512, 0, 512, ⟨-2949463227593696349678840678084546092545819686734, -2949463227593696349678840678084546092545817589581⟩, ⟨-2949463227593696349678840678084546084273038581301, -2949463227593696349678840678084546084273036484148⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨615985792935344704096715461380744242879788980549, 626879646060933815899481326077700461408842647973⟩
def wholeDExp : DyadicInterval precision := ⟨619778890111929048152500802482413362411072053473, 629087614762237432177832619094338713110027667137⟩
def wholeDLog : DyadicInterval precision := ⟨516668475441837355502384214637433233345583580834, 523190605620864448684409715253755541203210012554⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨619778890111929048152500802482413362960827867361, scale precision, 629087614762237432177832619094338712560271853249, scale precision,
    0, 512, 0, 512, ⟨-1253759292121867631798962652155400924114066448699, -1253759292121867631798962652155400924114064351546⟩, ⟨-1231971585870689408193430922761488484482381679326, -1231971585870689408193430922761488484482379582173⟩⟩
end GeneralCK.Certificates.E8TAxisZero0074StableWitnesses


