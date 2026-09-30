-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0061StableWitnesses_part00
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0061StableWitnesses_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:13:55.231789+00:00
-- url     : https://prove2.me/theorems/c6092d65-5880-4fa7-8c7a-bbe3a774bb16
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0061StableWitnesses (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0061StableWitnesses (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0061StableWitnesses (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0061StableWitnesses (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0061StableWitnesses (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0061StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨768328048611850508777866556237345596219489900939, 768328048611850508777866556237345596219489900940⟩
def centerDExp : DyadicInterval precision := ⟨510707457819051547382306257729904114775482130573, 510707457819051547382306257729904116974505386126⟩
def centerDLog : DyadicInterval precision := ⟨437997216266833750200638020923159195569100090572, 437997216266833750200638020923159197768123346125⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨510707457819051547382306257729904115325237944461, scale precision, 510707457819051547382306257729904116424749572238, scale precision,
    0, 512, 0, 512, ⟨-1536656097223701017555733112474691194012227940995, -1536656097223701017555733112474691194012225843842⟩, ⟨-1536656097223701017555733112474691190865733759918, -1536656097223701017555733112474691190865731662765⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨768532126029018358725434979921864197183472223956, 768532126029018358725434979921864197183472223957⟩
def centerCExp : DyadicInterval precision := ⟨510564852016541236919719099847316115854112721662, 510564852016541236919719099847316118053135977215⟩
def centerCLog : DyadicInterval precision := ⟨437891534698957666579652059536631708039609937460, 437891534698957666579652059536631710238633193013⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨510564852016541236919719099847316116403868535550, scale precision, 510564852016541236919719099847316117503380163327, scale precision,
    0, 512, 0, 512, ⟨-1537064252058036717450869959843728395940632010468, -1537064252058036717450869959843728395940629913315⟩, ⟨-1537064252058036717450869959843728392793258982510, -1537064252058036717450869959843728392793256885357⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1911991258293262566946163008006444663073783273907, 1911991258293262566946163008006444663073783273908⟩
def centerBExp : DyadicInterval precision := ⟨106777228888616263205275389672161585250011908171, 106777228888616263205275389672161587449035163724⟩
def centerBLog : DyadicInterval precision := ⟨103056806692937110732138662144390812131343362728, 103056806692937110732138662144390814330366618281⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨106777228888616263205275389672161585799767722059, scale precision, 106777228888616263205275389672161586899279349836, scale precision,
    0, 512, 0, 512, ⟨-3823982516586525133892326016012889333672290147187, -3823982516586525133892326016012889333672288050034⟩, ⟨-3823982516586525133892326016012889318622845045585, -3823982516586525133892326016012889318622842948432⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨762469961061176672454638714549067897721941573492, 774203834768265108571628471566363912561698867071⟩
def wholeDExp : DyadicInterval precision := ⟨506617451172271417683927781753795729433033108588, 514818014850194000087183801285808387115302195067⟩
def wholeDLog : DyadicInterval precision := ⟨434963177842048586751554818318029031715400615655, 441040166381185817721359138930122618351494322418⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨506617451172271417683927781753795729982788922476, scale precision, 514818014850194000087183801285808386565546381179, scale precision,
    0, 512, 0, 512, ⟨-1548407669536530217143256943132727826709346957757, -1548407669536530217143256943132727826709344860604⟩, ⟨-1524939922122353344909277429098135793883198673776, -1524939922122353344909277429098135793883196576623⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨762469961061176672454638714549067897721941573492, 774613246448220558536692060304546312326761250431⟩
def wholeCExp : DyadicInterval precision := ⟨506333692325937324659679685745915126991647090952, 514818014850194000087183801285808387115302195067⟩
def wholeCLog : DyadicInterval precision := ⟨434752446733309387933512762274426294045705836785, 441040166381185817721359138930122618351494322418⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨506333692325937324659679685745915127541402904840, scale precision, 514818014850194000087183801285808386565546381179, scale precision,
    0, 512, 0, 512, ⟨-1549226492896441117073384120609092626240360519419, -1549226492896441117073384120609092626240358422266⟩, ⟨-1524939922122353344909277429098135793883198673776, -1524939922122353344909277429098135793883196576623⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide


end GeneralCK.Certificates.E8TAxisZero0061StableWitnesses


