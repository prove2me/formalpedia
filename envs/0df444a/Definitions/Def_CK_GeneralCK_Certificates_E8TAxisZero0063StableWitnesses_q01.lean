-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0063StableWitnesses_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0063StableWitnesses_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:35:56.548823+00:00
-- url     : https://prove2.me/theorems/78aed29c-f1fe-42cc-9bf1-667a7a0cce64
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0063StableWitnesses (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0063StableWitnesses (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0063StableWitnesses (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0063StableWitnesses (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0063StableWitnesses (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0063StableWitnesses_q00

namespace GeneralCK.Certificates.E8TAxisZero0063StableWitnesses
open DyadicInterval E8TAxisStableInterval
set_option maxRecDepth 100000
def centerCExpWitness : ExpWitness precision :=
  ⟨527127981516568675852540508495744759236181574692, scale precision, 527127981516568675852540508495744760335693202469, scale precision,
    0, 512, 0, 512, ⟨-1490404785686365345136963854707905137378737476719, -1490404785686365345136963854707905137378735379566⟩, ⟨-1490404785686365345136963854707905134330259496784, -1490404785686365345136963854707905134330257399631⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1842135243688328357296763336306999735664797015243, 1842135243688328357296763336306999735664797015244⟩
def centerBExp : DyadicInterval precision := ⟨117488392414070192117296672785596538735392996147, 117488392414070192117296672785596540934416251700⟩
def centerBLog : DyadicInterval precision := ⟨113004760927215812678647019866708749572724720662, 113004760927215812678647019866708751771747976215⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨117488392414070192117296672785596539285148810035, scale precision, 117488392414070192117296672785596540384660437812, scale precision,
    0, 512, 0, 512, ⟨-3684270487376656714593526672613999478168304892183, -3684270487376656714593526672613999478168302795030⟩, ⟨-3684270487376656714593526672613999464490885265935, -3684270487376656714593526672613999464490883168782⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨739212305620516788391447838602016614455786978945, 750806424999049798752938234956163650116084001298⟩
def wholeDExp : DyadicInterval precision := ⟨523100967242339682629524513379347095252573454615, 531466696428681553786643034174516971757505971701⟩
def wholeDLog : DyadicInterval precision := ⟨447152665109602019123525890115620509603294783509, 453300409610535438784277685833236609207550076241⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨523100967242339682629524513379347095802329268503, scale precision, 531466696428681553786643034174516971207750157813, scale precision,
    0, 512, 0, 512, ⟨-1501612849998099597505876469912327301768142166202, -1501612849998099597505876469912327301768140069049⟩, ⟨-1478424611241033576782895677204033227399779389680, -1478424611241033576782895677204033227399777292527⟩⟩
end GeneralCK.Certificates.E8TAxisZero0063StableWitnesses


