-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0069StableWitnesses_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0069StableWitnesses_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:36:47.929422+00:00
-- url     : https://prove2.me/theorems/c47c25fc-dfd5-482d-8631-5754eec13634
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0069StableWitnesses (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0069StableWitnesses (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0069StableWitnesses (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0069StableWitnesses (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0069StableWitnesses (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0069StableWitnesses_q00

namespace GeneralCK.Certificates.E8TAxisZero0069StableWitnesses
open DyadicInterval E8TAxisStableInterval
set_option maxRecDepth 100000
def centerCExpWitness : ExpWitness precision :=
  ⟨578823085436792228932409230670413864915161339854, scale precision, 578823085436792228932409230670413866014672967631, scale precision,
    0, 512, 0, 512, ⟨-1353676176585136845683897008774775832529410283394, -1353676176585136845683897008774775832529408186241⟩, ⟨-1353676176585136845683897008774775829753194053096, -1353676176585136845683897008774775829753191955943⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1637817266757676828673598708592026054607677417310, 1637817266757676828673598708592026054607677417311⟩
def centerBExp : DyadicInterval precision := ⟨155390236297048833115175313530739248860346858624, 155390236297048833115175313530739251059370114177⟩
def centerBLog : DyadicInterval precision := ⟨147672001971055420739937412048827325817433791069, 147672001971055420739937412048827328016457046622⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨155390236297048833115175313530739249410102672512, scale precision, 155390236297048833115175313530739250509614300289, scale precision,
    0, 512, 0, 512, ⟨-3275634533515353657347197417184052114386009080447, -3275634533515353657347197417184052114386006983294⟩, ⟨-3275634533515353657347197417184052104044702685954, -3275634533515353657347197417184052104044700588801⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨671052481512572809340093335645151882932874114537, 682249998762477519670394645145297230397519416514⟩
def wholeDExp : DyadicInterval precision := ⟨574552180098098577953261580846255152671904481505, 583424017396714902499808941799093865790753691861⟩
def wholeDLog : DyadicInterval precision := ⟨484559560373994267607098493867261016455641847521, 490914027605645316992013980560028282815828884161⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨574552180098098577953261580846255153221660295393, scale precision, 583424017396714902499808941799093865240997877973, scale precision,
    0, 512, 0, 512, ⟨-1364499997524955039340789290290594462193466430073, -1364499997524955039340789290290594462193464332920⟩, ⟨-1342104963025145618680186671290303764488587902438, -1342104963025145618680186671290303764488585805285⟩⟩
end GeneralCK.Certificates.E8TAxisZero0069StableWitnesses


