-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0058StableWitnesses_part00
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0058StableWitnesses_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:15:15.390041+00:00
-- url     : https://prove2.me/theorems/18c4530f-8152-477d-a53a-a919cc69a9c5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0058StableWitnesses (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0058StableWitnesses (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0058StableWitnesses (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0058StableWitnesses (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0058StableWitnesses (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0058StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨803852177515934255585547919467375235228063974291, 803852177515934255585547919467375235228063974292⟩
def centerDExp : DyadicInterval precision := ⟨486474140463139135434442039725801311744313926422, 486474140463139135434442039725801313943337181975⟩
def centerDLog : DyadicInterval precision := ⟨419927923473864759956554512738531498009528841884, 419927923473864759956554512738531500208552097437⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨486474140463139135434442039725801312294069740310, scale precision, 486474140463139135434442039725801313393581368087, scale precision,
    0, 512, 0, 512, ⟨-1607704355031868511171095838934750472107746123950, -1607704355031868511171095838934750472107744026797⟩, ⟨-1607704355031868511171095838934750468804511870366, -1607704355031868511171095838934750468804509773213⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨804060019052222955603745304378160261963058384750, 804060019052222955603745304378160261963058384751⟩
def centerCExp : DyadicInterval precision := ⟨486335796238792409801666963790294327677300323534, 486335796238792409801666963790294329876323579087⟩
def centerCLog : DyadicInterval precision := ⟨419824124703485712153002108890292522326759878945, 419824124703485712153002108890292524525783134498⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨486335796238792409801666963790294328227056137422, scale precision, 486335796238792409801666963790294329326567765199, scale precision,
    0, 512, 0, 512, ⟨-1608120038104445911207490608756320525578204767763, -1608120038104445911207490608756320525578202670610⟩, ⟨-1608120038104445911207490608756320522274030868396, -1608120038104445911207490608756320522274028771243⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2018142095127181724495121752491622092576891271504, 2018142095127181724495121752491622092576891271505⟩
def centerBExp : DyadicInterval precision := ⟨92340422383972883036384198256775796454370098414, 92340422383972883036384198256775798653393353967⟩
def centerBLog : DyadicInterval precision := ⟨89540631485436919909715046768671294851254920669, 89540631485436919909715046768671297050278176222⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨92340422383972883036384198256775797004125912302, scale precision, 92340422383972883036384198256775798103637540079, scale precision,
    0, 512, 0, 512, ⟨-4036284190254363448990243504983244193854946109432, -4036284190254363448990243504983244193854944012279⟩, ⟨-4036284190254363448990243504983244176452621073724, -4036284190254363448990243504983244176452618976571⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨797886217135535601213561462349015058648188303747, 809836502735595761416983074307699172577520882056⟩
def wholeDExp : DyadicInterval precision := ⟨482506534178222248007502303634473306418081574606, 490462045819898463991457369988920388736986392916⟩
def wholeDLog : DyadicInterval precision := ⟨416948124396604742320674577430730284979084793064, 422916858198723400101802834922666848815462481446⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨482506534178222248007502303634473306967837388494, scale precision, 490462045819898463991457369988920388187230579028, scale precision,
    0, 512, 0, 512, ⟨-1619673005471191522833966148615398346820241033264, -1619673005471191522833966148615398346820238936111⟩, ⟨-1595772434271071202427122924698030115658189688259, -1595772434271071202427122924698030115658187591106⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨797886217135535601213561462349015058648188303747, 810253489605667947136320376142758288753586638141⟩
def wholeCExp : DyadicInterval precision := ⟨482231280986029817170095062515022023240643869896, 490462045819898463991457369988920388736986392916⟩
def wholeCLog : DyadicInterval precision := ⟨416741174920059242179572611210238239439892019474, 422916858198723400101802834922666848815462481446⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨482231280986029817170095062515022023790399683784, scale precision, 490462045819898463991457369988920388187230579028, scale precision,
    0, 512, 0, 512, ⟨-1620506979211335894272640752285516579173323025305, -1620506979211335894272640752285516579173320928152⟩, ⟨-1595772434271071202427122924698030115658189688259, -1595772434271071202427122924698030115658187591106⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2000036317676497000506706165815619555969669750235, 2036288425671287994308058262372240592164802855643⟩

end GeneralCK.Certificates.E8TAxisZero0058StableWitnesses


