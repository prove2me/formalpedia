-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0066StableWitnesses_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0066StableWitnesses_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T20:16:08.74318+00:00
-- url     : https://prove2.me/theorems/30759ad2-214d-46d7-a20a-3e0756f2ba44
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0066StableWitnesses (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0066StableWitnesses (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0066StableWitnesses (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0066StableWitnesses (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0066StableWitnesses (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0066StableWitnesses_q00

namespace GeneralCK.Certificates.E8TAxisZero0066StableWitnesses
open DyadicInterval E8TAxisStableInterval
set_option maxRecDepth 100000
def centerCExpWitness : ExpWitness precision :=
  ⟨552596077439797026498222740403016663194295131794, scale precision, 552596077439797026498222740403016664293806759571, scale precision,
    0, 512, 0, 512, ⟨-1421445371561217451621140077410228158315162726870, -1421445371561217451621140077410228158315160629717⟩, ⟨-1421445371561217451621140077410228155407183264357, -1421445371561217451621140077410228155407181167204⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1738916649804500981877594317565483720828248966351, 1738916649804500981877594317565483720828248966352⟩
def centerBExp : DyadicInterval precision := ⟨135312862408374151028181176107282666592259496479, 135312862408374151028181176107282668791282752032⟩
def centerBLog : DyadicInterval precision := ⟨129410534887335683299088832674040682072880277295, 129410534887335683299088832674040684271903532848⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨135312862408374151028181176107282667142015310367, scale precision, 135312862408374151028181176107282668241526938144, scale precision,
    0, 512, 0, 512, ⟨-3477833299609001963755188635130967447594360377675, -3477833299609001963755188635130967447594358280522⟩, ⟨-3477833299609001963755188635130967435718637584888, -3477833299609001963755188635130967435718635487735⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨704837076587479092158941059188951191105662022838, 716228578308099727358082939138935890959899212495⟩
def wholeDExp : DyadicInterval precision := ⟨548448150163327086956497611001597701687768128576, 557064765387537285209117120927584104924255812884⟩
def wholeDLog : DyadicInterval precision := ⟨465700648921796470149242465934935275052804228156, 471952686082951260798866870121334520250908543212⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨548448150163327086956497611001597702237523942464, scale precision, 557064765387537285209117120927584104374499998996, scale precision,
    0, 512, 0, 512, ⟨-1432457156616199454716165878277871783384785766055, -1432457156616199454716165878277871783384783668902⟩, ⟨-1409674153174958184317882118377902380768999045198, -1409674153174958184317882118377902380768996948045⟩⟩
end GeneralCK.Certificates.E8TAxisZero0066StableWitnesses


