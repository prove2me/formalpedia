-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0069StableWitnesses_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0069StableWitnesses_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:42:24.207149+00:00
-- url     : https://prove2.me/theorems/c22c424a-e7a1-4352-8922-d54d1bf002d0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0069StableWitnesses (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0069StableWitnesses (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0069StableWitnesses (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0069StableWitnesses (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0069StableWitnesses (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0069StableWitnesses_q01

namespace GeneralCK.Certificates.E8TAxisZero0069StableWitnesses
open DyadicInterval E8TAxisStableInterval
set_option maxRecDepth 100000
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨671052481512572809340093335645151882932874114537, 682640618143014187111337022065288110830276268788⟩
def wholeCExp : DyadicInterval precision := ⟨574245138029433207622338239115460179824844088407, 583424017396714902499808941799093865790753691861⟩
def wholeCLog : DyadicInterval precision := ⟨484339145608237259642998456852700263189071473693, 490914027605645316992013980560028282815828884161⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨574245138029433207622338239115460180374599902295, scale precision, 583424017396714902499808941799093865240997877973, scale precision,
    0, 512, 0, 512, ⟨-1365281236286028374222674044130576223059727856721, -1365281236286028374222674044130576223059725759568⟩, ⟨-1342104963025145618680186671290303764488587902438, -1342104963025145618680186671290303764488585805285⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1620903550425908375993486831338272100554127446794, 1654799518693000536357843956327185517074350138484⟩
def wholeBExp : DyadicInterval precision := ⟨151820689458754004437475082095501806176513974245, 159028793201307320320006313149470074082714132214⟩
def wholeBLog : DyadicInterval precision := ⟨144441937121773249280251983095422539606292751669, 150957182965409784487798469398587559283229806635⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨151820689458754004437475082095501806726269788133, scale precision, 159028793201307320320006313149470073532958318326, scale precision,
    0, 512, 0, 512, ⟨-3309599037386001072715687912654371039440924836020, -3309599037386001072715687912654371039440922738867⟩, ⟨-3241807100851816751986973662676544196055906578528, -3241807100851816751986973662676544196055904481375⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

end GeneralCK.Certificates.E8TAxisZero0069StableWitnesses


