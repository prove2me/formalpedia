-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0063StableWitnesses_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0063StableWitnesses_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:16:54.494872+00:00
-- url     : https://prove2.me/theorems/2ceab2ed-238f-4199-b555-3339bf86c641
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0063StableWitnesses (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0063StableWitnesses (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0063StableWitnesses (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0063StableWitnesses (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0063StableWitnesses (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0063StableWitnesses_q01

namespace GeneralCK.Certificates.E8TAxisZero0063StableWitnesses
open DyadicInterval E8TAxisStableInterval
set_option maxRecDepth 100000
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨739212305620516788391447838602016614455786978945, 751210942589115006793580070789280304680337908202⟩
def wholeCExp : DyadicInterval precision := ⟨522811477336964667107020654074320760190186003221, 531466696428681553786643034174516971757505971701⟩
def wholeCLog : DyadicInterval precision := ⟨446939463317789946567087405274514277504009553203, 453300409610535438784277685833236609207550076241⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨522811477336964667107020654074320760739941817109, scale precision, 531466696428681553786643034174516971207750157813, scale precision,
    0, 512, 0, 512, ⟨-1502421885178230013587160141578560610897500475324, -1502421885178230013587160141578560610897498378171⟩, ⟨-1478424611241033576782895677204033227399779389680, -1478424611241033576782895677204033227399777292527⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1824495374570930919170744191160351916966852304993, 1859828251952921885867973435369595190236319949018⟩
def wholeBExp : DyadicInterval precision := ⟨114677913381301034261077228997777987021594188711, 120358996857378975373786880754258496756855698653⟩
def wholeBLog : DyadicInterval precision := ⟨110401084205762731741360858601684594553266818760, 115659359130999489572274282285664239926399575571⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨114677913381301034261077228997777987571350002599, scale precision, 120358996857378975373786880754258496207099884765, scale precision,
    0, 512, 0, 512, ⟨-3719656503905843771735946870739190387478951041035, -3719656503905843771735946870739190387478948943882⟩, ⟨-3648990749141861838341488382320703827258101481812, -3648990749141861838341488382320703827258099384659⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

end GeneralCK.Certificates.E8TAxisZero0063StableWitnesses


