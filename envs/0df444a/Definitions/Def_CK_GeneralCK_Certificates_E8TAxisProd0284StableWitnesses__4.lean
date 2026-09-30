-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0284StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0284StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T22:19:32.626022+00:00
-- url     : https://prove2.me/theorems/03c762ca-ea92-4cb2-a3cb-b2514a2772bd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0284StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0285StableWitnesses, GeneralCK.Certificates.E8TAxisProd02…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0284StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0285StableWitnesses, GeneralCK.Certificates.E8TAxisProd0286StableWitnesses, GeneralCK.Certificates.E8TAxisProd0287StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0284StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0285StableWitnesses, GeneralCK.Certificates.E8TAxisProd0286StableWitnesses, GeneralCK.Certificates.E8TAxisProd0287StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0284StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0285StableWitnesses, GeneralCK.Certificates.E8TAxisProd0286StableWitnesses, GeneralCK.Certificates.E8TAxisProd0287StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0284StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0285StableWitnesses, GeneralCK/Certificates/E8TAxisProd0286StableWitnesses, GeneralCK/Certificates/E8TAxisProd0287StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0284StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0284StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4273758705152157645723775860095423839948701825, 4273758705152157645723775860095423839948701826⟩
def centerAExp : DyadicInterval precision := ⟨1452979066123426753084482090982379267943336487380, 1452979066123426753084482090982379270142359742933⟩
def centerALog : DyadicInterval precision := ⟨1008768229300280628272830658947964075013109562599, 1008768229300280628272830658947964077212132818152⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1452979066123426753084482090982379268493092301268, scale precision, 1452979066123426753084482090982379269592603929045, scale precision,
    0, 128, 0, 128, ⟨-8547517410304315291447551720190848232878905189, -8547517410304315291447551720190848232876808036⟩, ⟨-8547517410304315291447551720190847126917999264, -8547517410304315291447551720190847126915902111⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨768328048611850508777866556237345596219489900939, 768328048611850508777866556237345596219489900940⟩
def centerDExp : DyadicInterval precision := ⟨510707457819051547382306257729904114775482130573, 510707457819051547382306257729904116974505386126⟩
def centerDLog : DyadicInterval precision := ⟨437997216266833750200638020923159195569100090572, 437997216266833750200638020923159197768123346125⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨510707457819051547382306257729904115325237944461, scale precision, 510707457819051547382306257729904116424749572238, scale precision,
    1, 128, 1, 128, ⟨-1536656097223701017555733112474691194012227940995, -1536656097223701017555733112474691194012225843842⟩, ⟨-1536656097223701017555733112474691190865733759918, -1536656097223701017555733112474691190865731662765⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨773845670258415869355804518631050612706205348469, 773845670258415869355804518631050612706205348470⟩
def centerCExp : DyadicInterval precision := ⟨506865821562752572493480595971727788487042637961, 506865821562752572493480595971727790686065893514⟩
def centerCLog : DyadicInterval precision := ⟨435147603079357958531637403446579781009422729474, 435147603079357958531637403446579783208445985027⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨506865821562752572493480595971727789036798451849, scale precision, 506865821562752572493480595971727790136310079626, scale precision,
    1, 128, 1, 128, ⟨-1547691340516831738711609037262101226997582786745, -1547691340516831738711609037262101226997580689592⟩, ⟨-1547691340516831738711609037262101223827240704286, -1547691340516831738711609037262101223827238607133⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1919936162189103388223857410683006220404818693026, 1919936162189103388223857410683006220404818693027⟩
def centerBExp : DyadicInterval precision := ⟨105622608442404791555110702110841724894054340672, 105622608442404791555110702110841727093077596225⟩
def centerBLog : DyadicInterval precision := ⟨101980402997055739338556625803435390842735888054, 101980402997055739338556625803435393041759143607⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨105622608442404791555110702110841725443810154560, scale precision, 105622608442404791555110702110841726543321782337, scale precision,
    3, 128, 3, 128, ⟨-3839872324378206776447714821366012448416617981713, -3839872324378206776447714821366012448416615884560⟩, ⟨-3839872324378206776447714821366012433202658887560, -3839872324378206776447714821366012433202656790407⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨4115470352964345628383522602588716836376905846, 4432047174048269527644776165804031130864675905⟩
def wholeAExp : DyadicInterval precision := ⟨1452664369350591901250217311774540048662792202314, 1453293830838237185210198542808669484539789010133⟩
def wholeALog : DyadicInterval precision := ⟨1008610412272733567070593870872814919869682069664, 1008926063354791867585944205900164502304869828050⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1452664369350591901250217311774540049212548016202, scale precision, 1453293830838237185210198542808669483990033196245, scale precision,
    0, 128, 0, 128, ⟨-8864094348096539055289552331608062814830647821, -8864094348096539055289552331608062814828550668⟩, ⟨-8230940705928691256767045205177433119894175747, -8230940705928691256767045205177433119892078594⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨762469961061176672454638714549067897721941573492, 774203834768265108571628471566363912561698867071⟩
def wholeDExp : DyadicInterval precision := ⟨506617451172271417683927781753795729433033108588, 514818014850194000087183801285808387115302195067⟩
def wholeDLog : DyadicInterval precision := ⟨434963177842048586751554818318029031715400615655, 441040166381185817721359138930122618351494322418⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨506617451172271417683927781753795729982788922476, scale precision, 514818014850194000087183801285808386565546381179, scale precision,
    1, 128, 1, 128, ⟨-1548407669536530217143256943132727826709346957757, -1548407669536530217143256943132727826709344860604⟩, ⟨-1524939922122353344909277429098135793883198673776, -1524939922122353344909277429098135793883196576623⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨767766946107848329958628014138329444898139812157, 779943459500497611886243416284385039295143534453⟩
def wholeCExp : DyadicInterval precision := ⟨502653850587515589754757690063236631364713593875, 511099751978162098288491019776577288369561576403⟩
def wholeCLog : DyadicInterval precision := ⟨432016887803755774881374782382181413890820089436, 438287896166415310833875147215761043266088027427⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨502653850587515589754757690063236631914469407763, scale precision, 511099751978162098288491019776577287819805762515, scale precision,
    1, 128, 1, 128, ⟨-1559886919000995223772486832568770080188742045946, -1559886919000995223772486832568770080188739948793⟩, ⟨-1535533892215696659917256028276658888224241126757, -1535533892215696659917256028276658888224239029604⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1902073470780820433122810981938889256892679686227, 1937846263865564398631128344737629430206240659376⟩
def wholeBExp : DyadicInterval precision := ⟨103065351307377808115490598495901961960164403069, 108236293759101304255683111739375453689130530219⟩
def wholeBLog : DyadicInterval precision := ⟨99593554460042141096933830792152458031002374347, 104415898111877252931691918102953497082812072612⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨103065351307377808115490598495901962509920216957, scale precision, 108236293759101304255683111739375453139374716331, scale precision,
    3, 128, 3, 128, ⟨-3875692527731128797262256689475258868208206264238, -3875692527731128797262256689475258868208204167085⟩, ⟨-3804146941561640866245621963877778506362073885390, -3804146941561640866245621963877778506362071788237⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0284StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0285StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0285StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4273758705152157645723775860095423839948701825, 4273758705152157645723775860095423839948701826⟩
def centerAExp : DyadicInterval precision := ⟨1452979066123426753084482090982379267943336487380, 1452979066123426753084482090982379270142359742933⟩
def centerALog : DyadicInterval precision := ⟨1008768229300280628272830658947964075013109562599, 1008768229300280628272830658947964077212132818152⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1452979066123426753084482090982379268493092301268, scale precision, 1452979066123426753084482090982379269592603929045, scale precision,
    0, 128, 0, 128, ⟨-8547517410304315291447551720190848232878905189, -8547517410304315291447551720190848232876808036⟩, ⟨-8547517410304315291447551720190847126917999264, -8547517410304315291447551720190847126915902111⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨756629458111635987963421694655899447515956153847, 756629458111635987963421694655899447515956153848⟩
def centerDExp : DyadicInterval precision := ⟨518949168719742299502489786080534463489111235356, 518949168719742299502489786080534465688134490909⟩
def centerDLog : DyadicInterval precision := ⟨444091993825822657919630218920559695762275777424, 444091993825822657919630218920559697961299032977⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨518949168719742299502489786080534464038867049244, scale precision, 518949168719742299502489786080534465138378677021, scale precision,
    1, 128, 1, 128, ⟨-1513258916223271975926843389311798896580174863487, -1513258916223271975926843389311798896580172766334⟩, ⟨-1513258916223271975926843389311798893483651849057, -1513258916223271975926843389311798893483649751904⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨762113950735165688108779380788454049404430609299, 762113950735165688108779380788454049404430609300⟩
def centerCExp : DyadicInterval precision := ⟨515068887209922911179124463254728419132718614498, 515068887209922911179124463254728421331741870051⟩
def centerCLog : DyadicInterval precision := ⟨441225676399731894826901675345794257096992581281, 441225676399731894826901675345794259296015836834⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨515068887209922911179124463254728419682474428386, scale precision, 515068887209922911179124463254728420781986056163, scale precision,
    1, 128, 1, 128, ⟨-1524227901470331376217558761576908100368787632660, -1524227901470331376217558761576908100368785535507⟩, ⟨-1524227901470331376217558761576908097248936901692, -1524227901470331376217558761576908097248934804539⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1884867692578302269074437898549189604325850446220, 1884867692578302269074437898549189604325850446221⟩
def centerBExp : DyadicInterval precision := ⟨110814993402791670807828798642635550614945350986, 110814993402791670807828798642635552813968606539⟩
def centerBLog : DyadicInterval precision := ⟨106814821824654375213167797519651844144615034673, 106814821824654375213167797519651846343638290226⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨110814993402791670807828798642635551164701164874, scale precision, 110814993402791670807828798642635552264212792651, scale precision,
    3, 128, 3, 128, ⟨-3769735385156604538148875797098379215902246271328, -3769735385156604538148875797098379215902244174175⟩, ⟨-3769735385156604538148875797098379201401157610703, -3769735385156604538148875797098379201401155513550⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨4115470352964345628383522602588716836376905846, 4432047174048269527644776165804031130864675905⟩
def wholeAExp : DyadicInterval precision := ⟨1452664369350591901250217311774540048662792202314, 1453293830838237185210198542808669484539789010133⟩
def wholeALog : DyadicInterval precision := ⟨1008610412272733567070593870872814919869682069664, 1008926063354791867585944205900164502304869828050⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1452664369350591901250217311774540049212548016202, scale precision, 1453293830838237185210198542808669483990033196245, scale precision,
    0, 128, 0, 128, ⟨-8864094348096539055289552331608062814830647821, -8864094348096539055289552331608062814828550668⟩, ⟨-8230940705928691256767045205177433119894175747, -8230940705928691256767045205177433119892078594⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨750806424999049798752938234956163650116084001297, 762469961061176672454638714549067897721941573493⟩
def wholeDExp : DyadicInterval precision := ⟨514818014850194000087183801285808384916278939514, 523100967242339682629524513379347097451596710168⟩
def wholeDLog : DyadicInterval precision := ⟨441040166381185817721359138930122616152471066865, 447152665109602019123525890115620511802318039062⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨514818014850194000087183801285808385466034753402, scale precision, 523100967242339682629524513379347096901840896280, scale precision,
    1, 128, 1, 128, ⟨-1524939922122353344909277429098135797004569717344, -1524939922122353344909277429098135797004567620191⟩, ⟨-1501612849998099597505876469912327298696195936143, -1501612849998099597505876469912327298696193838990⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨756071718559389743494109049976208766155978014438, 768175004601111508805576807505928586677554639558⟩
def wholeCExp : DyadicInterval precision := ⟨510814428486735487400488284538229114886484758973, 519345403596912176590077873188575390014968713019⟩
def wholeCLog : DyadicInterval precision := ⟨438076484518207476305631270601929957909164364057, 444384371700980139966377102034572023341216671464⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨510814428486735487400488284538229115436240572861, scale precision, 519345403596912176590077873188575389465212899131, scale precision,
    1, 128, 1, 128, ⟨-1536350009202223017611153615011857174928027961421, -1536350009202223017611153615011857174928025864268⟩, ⟨-1512143437118779486988218099952417530764876817253, -1512143437118779486988218099952417530764874720100⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1867101987241776673065952633983770746225505804155, 1902683364366205758745751601618170960911474691521⟩
def wholeBExp : DyadicInterval precision := ⟨108145996109375667402280847961522197730486990329, 113542096498610068009314789561191511751181337193⟩
def wholeBLog : DyadicInterval precision := ⟨104331824231657771760808035344178928951583347978, 109347526170830653111116471066465796613409538910⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨108145996109375667402280847961522198280242804217, scale precision, 113542096498610068009314789561191511201425523305, scale precision,
    3, 128, 3, 128, ⟨-3805366728732411517491503203236341929252435119317, -3805366728732411517491503203236341929252433022164⟩, ⟨-3734203974483553346131905267967541485374615030749, -3734203974483553346131905267967541485374612933596⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0285StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0286StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0286StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3957182113162240766624229437560720104187299711, 3957182113162240766624229437560720104187299712⟩
def centerAExp : DyadicInterval precision := ⟨1453608663518239684990297266292415545523124059933, 1453608663518239684990297266292415547722147315486⟩
def centerALog : DyadicInterval precision := ⟨1009083914440550911538268226967653949061006604559, 1009083914440550911538268226967653951260029860112⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1453608663518239684990297266292415546072879873821, scale precision, 1453608663518239684990297266292415547172391501598, scale precision,
    0, 128, 0, 128, ⟨-7914364226324481533248458875121440761116590109, -7914364226324481533248458875121440761114492956⟩, ⟨-7914364226324481533248458875121439655634705892, -7914364226324481533248458875121439655632608739⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨768328048611850508777866556237345596219489900939, 768328048611850508777866556237345596219489900940⟩
def centerDExp : DyadicInterval precision := ⟨510707457819051547382306257729904114775482130573, 510707457819051547382306257729904116974505386126⟩
def centerDLog : DyadicInterval precision := ⟨437997216266833750200638020923159195569100090572, 437997216266833750200638020923159197768123346125⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨510707457819051547382306257729904115325237944461, scale precision, 510707457819051547382306257729904116424749572238, scale precision,
    1, 128, 1, 128, ⟨-1536656097223701017555733112474691194012227940995, -1536656097223701017555733112474691194012225843842⟩, ⟨-1536656097223701017555733112474691190865733759918, -1536656097223701017555733112474691190865731662765⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨773436420167445659481162755501297158250424721668, 773436420167445659481162755501297158250424721669⟩
def centerCExp : DyadicInterval precision := ⟨507149766479545728423459608902194406949595644951, 507149766479545728423459608902194409148618900504⟩
def centerCLog : DyadicInterval precision := ⟨435358415359408595283630482617555378015725886954, 435358415359408595283630482617555380214749142507⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨507149766479545728423459608902194407499351458839, scale precision, 507149766479545728423459608902194408598863086616, scale precision,
    1, 128, 1, 128, ⟨-1546872840334891318962325511002594318085134021626, -1546872840334891318962325511002594318085131924473⟩, ⟨-1546872840334891318962325511002594314916566962204, -1546872840334891318962325511002594314916564865051⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1919324681810648577039983645500212138710933858141, 1919324681810648577039983645500212138710933858142⟩
def centerBExp : DyadicInterval precision := ⟨105711028709330625329238318777482848373424706319, 105711028709330625329238318777482850572447961872⟩
def centerBLog : DyadicInterval precision := ⟨102062861500117460741577289537406440836792979028, 102062861500117460741577289537406443035816234581⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨105711028709330625329238318777482848923180520207, scale precision, 105711028709330625329238318777482850022692147984, scale precision,
    3, 128, 3, 128, ⟨-3838649363621297154079967291000424285022485577878, -3838649363621297154079967291000424285022483480725⟩, ⟨-3838649363621297154079967291000424269821251951830, -3838649363621297154079967291000424269821249854677⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 4115470352964345628383522602588716836376905847⟩
def wholeAExp : DyadicInterval precision := ⟨1453293830838237185210198542808669482340765754580, 1453923564186661310665317018859587709527417053272⟩
def wholeALog : DyadicInterval precision := ⟨1008926063354791867585944205900164500105846572497, 1009241782561842849966002591658486094460586802138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453293830838237185210198542808669482890521568468, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-8230940705928691256767045205177434225615544793, -8230940705928691256767045205177434225613447640⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨762469961061176672454638714549067897721941573492, 774203834768265108571628471566363912561698867071⟩
def wholeDExp : DyadicInterval precision := ⟨506617451172271417683927781753795729433033108588, 514818014850194000087183801285808387115302195067⟩
def wholeDLog : DyadicInterval precision := ⟨434963177842048586751554818318029031715400615655, 441040166381185817721359138930122618351494322418⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨506617451172271417683927781753795729982788922476, scale precision, 514818014850194000087183801285808386565546381179, scale precision,
    1, 128, 1, 128, ⟨-1548407669536530217143256943132727826709346957757, -1548407669536530217143256943132727826709344860604⟩, ⟨-1524939922122353344909277429098135793883198673776, -1524939922122353344909277429098135793883196576623⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨767358973211500545538712928359387946918017972497, 779532923806291282212280406133176824784846191170⟩
def wholeCExp : DyadicInterval precision := ⟨502936320779601792371406173432229285821611883184, 511385174940146311547669422936068777047240307906⟩
def wholeCLog : DyadicInterval precision := ⟨432227054956256559943801532482254806885047100930, 438499350924704734769794268858068553194477385161⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨502936320779601792371406173432229286371367697072, scale precision, 511385174940146311547669422936068776497484494018, scale precision,
    1, 128, 1, 128, ⟨-1559065847612582564424560812266353651167249600422, -1559065847612582564424560812266353651167247503269⟩, ⟨-1534717946423001091077425856718775892264874860792, -1534717946423001091077425856718775892264872763639⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1901463634123536824162919442570279331410929518189, 1937233183913287840024540317050383821804286464345⟩
def wholeBExp : DyadicInterval precision := ⟨103151856601205818443859538406106668925089583841, 108326658364775654627891049025127644111646520735⟩
def wholeBLog : DyadicInterval precision := ⟨99674359011401707897886690543105551761177305380, 104500029491594320902401731788442632941923043292⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨103151856601205818443859538406106669474845397729, scale precision, 108326658364775654627891049025127643561890706847, scale precision,
    3, 128, 3, 128, ⟨-3874466367826575680049080634100767651397760217862, -3874466367826575680049080634100767651397758120709⟩, ⟨-3802927268247073648325838885140558655404765952640, -3802927268247073648325838885140558655404763855487⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0286StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0287StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0287StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3957182113162240766624229437560720104187299711, 3957182113162240766624229437560720104187299712⟩
def centerAExp : DyadicInterval precision := ⟨1453608663518239684990297266292415545523124059933, 1453608663518239684990297266292415547722147315486⟩
def centerALog : DyadicInterval precision := ⟨1009083914440550911538268226967653949061006604559, 1009083914440550911538268226967653951260029860112⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1453608663518239684990297266292415546072879873821, scale precision, 1453608663518239684990297266292415547172391501598, scale precision,
    0, 128, 0, 128, ⟨-7914364226324481533248458875121440761116590109, -7914364226324481533248458875121440761114492956⟩, ⟨-7914364226324481533248458875121439655634705892, -7914364226324481533248458875121439655632608739⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨756629458111635987963421694655899447515956153847, 756629458111635987963421694655899447515956153848⟩
def centerDExp : DyadicInterval precision := ⟨518949168719742299502489786080534463489111235356, 518949168719742299502489786080534465688134490909⟩
def centerDLog : DyadicInterval precision := ⟨444091993825822657919630218920559695762275777424, 444091993825822657919630218920559697961299032977⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨518949168719742299502489786080534464038867049244, scale precision, 518949168719742299502489786080534465138378677021, scale precision,
    1, 128, 1, 128, ⟨-1513258916223271975926843389311798896580174863487, -1513258916223271975926843389311798896580172766334⟩, ⟨-1513258916223271975926843389311798893483651849057, -1513258916223271975926843389311798893483649751904⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨761707161537246254456047650563886810414845204692, 761707161537246254456047650563886810414845204693⟩
def centerCExp : DyadicInterval precision := ⟨515355691936333253720494673900186676137946850482, 515355691936333253720494673900186678336970106035⟩
def centerCLog : DyadicInterval precision := ⟨441437728114587167153712558135115263741815898245, 441437728114587167153712558135115265940839153798⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨515355691936333253720494673900186676687702664370, scale precision, 515355691936333253720494673900186677787214292147, scale precision,
    1, 128, 1, 128, ⟨-1523414323074492508912095301127773622388748696879, -1523414323074492508912095301127773622388746599726⟩, ⟨-1523414323074492508912095301127773619270634219045, -1523414323074492508912095301127773619270632121892⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1884259485661907920693696184742913736489441816579, 1884259485661907920693696184742913736489441816580⟩
def centerBExp : DyadicInterval precision := ⟨110907263571350488223507013288220507216724053239, 110907263571350488223507013288220509415747308792⟩
def centerBLog : DyadicInterval precision := ⟨106900586385731383152887305957097322128630355560, 106900586385731383152887305957097324327653611113⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨110907263571350488223507013288220507766479867127, scale precision, 110907263571350488223507013288220508865991494904, scale precision,
    3, 128, 3, 128, ⟨-3768518971323815841387392369485827480223396864770, -3768518971323815841387392369485827480223394767617⟩, ⟨-3768518971323815841387392369485827465734372498691, -3768518971323815841387392369485827465734370401538⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 4115470352964345628383522602588716836376905847⟩
def wholeAExp : DyadicInterval precision := ⟨1453293830838237185210198542808669482340765754580, 1453923564186661310665317018859587709527417053272⟩
def wholeALog : DyadicInterval precision := ⟨1008926063354791867585944205900164500105846572497, 1009241782561842849966002591658486094460586802138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453293830838237185210198542808669482890521568468, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-8230940705928691256767045205177434225615544793, -8230940705928691256767045205177434225613447640⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨750806424999049798752938234956163650116084001297, 762469961061176672454638714549067897721941573493⟩
def wholeDExp : DyadicInterval precision := ⟨514818014850194000087183801285808384916278939514, 523100967242339682629524513379347097451596710168⟩
def wholeDLog : DyadicInterval precision := ⟨441040166381185817721359138930122616152471066865, 447152665109602019123525890115620511802318039062⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨514818014850194000087183801285808385466034753402, scale precision, 523100967242339682629524513379347096901840896280, scale precision,
    1, 128, 1, 128, ⟨-1524939922122353344909277429098135797004569717344, -1524939922122353344909277429098135797004567620191⟩, ⟨-1501612849998099597505876469912327298696195936143, -1501612849998099597505876469912327298696193838990⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨755666190130685222728180668015462529393116495008, 767766946107848329958628014138329444898139812158⟩
def wholeCExp : DyadicInterval precision := ⟨511099751978162098288491019776577286170538320850, 519633693078741343203556538531702537329355606210⟩
def wholeCLog : DyadicInterval precision := ⟨438287896166415310833875147215761041067064771874, 444597060961543393279078530102797406766570753685⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨511099751978162098288491019776577286720294134738, scale precision, 519633693078741343203556538531702536779599792322, scale precision,
    1, 128, 1, 128, ⟨-1535533892215696659917256028276658891368320219030, -1535533892215696659917256028276658891368318121877⟩, ⟨-1511332380261370445456361336030925057240012088725, -1511332380261370445456361336030925057240009991572⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1866495511738476614912647845304495047761287388659, 1902073470780820433122810981938889256892679686228⟩
def wholeBExp : DyadicInterval precision := ⟨108236293759101304255683111739375451490107274666, 113636368145152325120593715857054955887961921129⟩
def wholeBLog : DyadicInterval precision := ⟨104415898111877252931691918102953494883788817059, 109434999324583928422048527764199788664869591893⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨108236293759101304255683111739375452039863088554, scale precision, 113636368145152325120593715857054955338206107241, scale precision,
    3, 128, 3, 128, ⟨-3804146941561640866245621963877778521208646956683, -3804146941561640866245621963877778521208644859530⟩, ⟨-3732991023476953229825295690608990088452048711691, -3732991023476953229825295690608990088452046614538⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0287StableWitnesses

end


