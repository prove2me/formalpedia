-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0325StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0325StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T20:53:04.57401+00:00
-- url     : https://prove2.me/theorems/e58405bd-9dfa-4642-9d07-954ef665cb5c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0325StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0326StableWitnesses, GeneralCK.Certificates.E8TAxisProd03…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0325StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0326StableWitnesses, GeneralCK.Certificates.E8TAxisProd0327StableWitnesses, GeneralCK.Certificates.E8TAxisProd0328StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0325StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0326StableWitnesses, GeneralCK.Certificates.E8TAxisProd0327StableWitnesses, GeneralCK.Certificates.E8TAxisProd0328StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0325StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0326StableWitnesses, GeneralCK.Certificates.E8TAxisProd0327StableWitnesses, GeneralCK.Certificates.E8TAxisProd0328StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0325StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0326StableWitnesses, GeneralCK/Certificates/E8TAxisProd0327StableWitnesses, GeneralCK/Certificates/E8TAxisProd0328StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0325StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0325StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3640605953424817106904235978836837760282897367, 3640605953424817106904235978836837760282897368⟩
def centerAExp : DyadicInterval precision := ⟨1454238532866739696576544033316540574868034513622, 1454238532866739696576544033316540577067057769175⟩
def centerALog : DyadicInterval precision := ⟨1009399667722954236284698895375438337347134637797, 1009399667722954236284698895375438339546157893350⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1454238532866739696576544033316540575417790327510, scale precision, 1454238532866739696576544033316540576517301955287, scale precision,
    0, 128, 0, 128, ⟨-7281211906849634213808471957673676073068378631, -7281211906849634213808471957673676073066281478⟩, ⟨-7281211906849634213808471957673674968065307991, -7281211906849634213808471957673674968063210838⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨710524563403850356500890582610538039823374015368, 710524563403850356500890582610538039823374015369⟩
def centerDExp : DyadicInterval precision := ⟨552745918518612785766768712299414359359889019406, 552745918518612785766768712299414361558912274959⟩
def centerDLog : DyadicInterval precision := ⟨468822363559667384554973018042110607773397723001, 468822363559667384554973018042110609972420978554⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨552745918518612785766768712299414359909644833294, scale precision, 552745918518612785766768712299414361009156461071, scale precision,
    1, 128, 1, 128, ⟨-1421049126807700713001781165221076081100344655889, -1421049126807700713001781165221076081100342558736⟩, ⟨-1421049126807700713001781165221076078193153502733, -1421049126807700713001781165221076078193151405580⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨715086447325439475174723394572269012211100984170, 715086447325439475174723394572269012211100984171⟩
def centerCExp : DyadicInterval precision := ⟨549306020426568321581538832004566191446026868685, 549306020426568321581538832004566193645050124238⟩
def centerCLog : DyadicInterval precision := ⟨466324301967493276197074460859827055112269730311, 466324301967493276197074460859827057311292985864⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨549306020426568321581538832004566191995782682573, scale precision, 549306020426568321581538832004566193095294310350, scale precision,
    1, 128, 1, 128, ⟨-1430172894650878950349446789144538025884901389504, -1430172894650878950349446789144538025884899292351⟩, ⟨-1430172894650878950349446789144538022959504644329, -1430172894650878950349446789144538022959502547176⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1745438297018927534561981280363914201137666567387, 1745438297018927534561981280363914201137666567388⟩
def centerBExp : DyadicInterval precision := ⟨134110624091933082136670206076357105371286737535, 134110624091933082136670206076357107570309993088⟩
def centerBLog : DyadicInterval precision := ⟨128309758905640797356437118806164668194320863617, 128309758905640797356437118806164670393344119170⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨134110624091933082136670206076357105921042551423, scale precision, 134110624091933082136670206076357107020554179200, scale precision,
    3, 128, 3, 128, ⟨-3490876594037855069123962560727828408266425698810, -3490876594037855069123962560727828408266423601657⟩, ⟨-3490876594037855069123962560727828396284242667890, -3490876594037855069123962560727828396284240570737⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3482318024844347500022322904444928295572395252, 3798893981423257492988718450954299577395465181⟩
def wholeAExp : DyadicInterval precision := ⟨1453923564186661310665317018859587707328393797719, 1454553569581723058392238696431353226318692924653⟩
def wholeALog : DyadicInterval precision := ⟨1009241782561842849966002591658486092261563546585, 1009557569928173087760872372803888452026676915366⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453923564186661310665317018859587707878149611607, scale precision, 1454553569581723058392238696431353225768937110765, scale precision,
    0, 128, 0, 128, ⟨-7597787962846514985977436901908599707413204648, -7597787962846514985977436901908599707411107495⟩, ⟨-6964636049688695000044645808889856038763968154, -6964636049688695000044645808889856038761871001⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨704837076587479092158941059188951191105662022838, 716228578308099727358082939138935890959899212495⟩
def wholeDExp : DyadicInterval precision := ⟨548448150163327086956497611001597701687768128576, 557064765387537285209117120927584104924255812884⟩
def wholeDLog : DyadicInterval precision := ⟨465700648921796470149242465934935275052804228156, 471952686082951260798866870121334520250908543212⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨548448150163327086956497611001597702237523942464, scale precision, 557064765387537285209117120927584104374499998996, scale precision,
    1, 128, 1, 128, ⟨-1432457156616199454716165878277871783384785766055, -1432457156616199454716165878277871783384783668902⟩, ⟨-1409674153174958184317882118377902380768999045198, -1409674153174958184317882118377902380768996948045⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨709187760133762498890382215058194219119912807034, 721002934992365362306809053633544693986704408118⟩
def wholeCExp : DyadicInterval precision := ⟨544876547247851763273770634032890867843485487175, 553758012945093357002741555662217582168358257393⟩
def wholeCLog : DyadicInterval precision := ⟨463101306975057858506244255700798469923094870407, 469556536557443266903848819351227690187699790593⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨544876547247851763273770634032890868393241301063, scale precision, 553758012945093357002741555662217581618602443505, scale precision,
    1, 128, 1, 128, ⟨-1442005869984730724613618107267089389447998973462, -1442005869984730724613618107267089389447996876309⟩, ⟨-1418375520267524997780764430116388436788887798831, -1418375520267524997780764430116388436788885701678⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1728115692693053516165256357166509114046150241291, 1762821356311411369254373393413045567533624830832⟩
def wholeBExp : DyadicInterval precision := ⟨130958053370962518886081223346872127462863794145, 137327725485643907527755950555576739679318339103⟩
def wholeBLog : DyadicInterval precision := ⟨125419304209820776284899920330798764199167302256, 131253497497244193434084011746101140256874298056⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨130958053370962518886081223346872128012619608033, scale precision, 137327725485643907527755950555576739129562525215, scale precision,
    3, 128, 3, 128, ⟨-3525642712622822738508746786826091141202566572441, -3525642712622822738508746786826091141202564475288⟩, ⟨-3456231385386107032330512714333018222241560034578, -3456231385386107032330512714333018222241557937425⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0325StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0326StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0326StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3324030191359282881556817859241043973740987770, 3324030191359282881556817859241043973740987771⟩
def centerAExp : DyadicInterval precision := ⟨1454868674354870198336951421367206718659928330939, 1454868674354870198336951421367206720858951586492⟩
def centerALog : DyadicInterval precision := ⟨1009715489181788885783740077569471416073335956070, 1009715489181788885783740077569471418272359211623⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1454868674354870198336951421367206719209684144827, scale precision, 1454868674354870198336951421367206720309195772604, scale precision,
    0, 128, 0, 128, ⟨-6648060382718565763113635718482088499745256643, -6648060382718565763113635718482088499743159490⟩, ⟨-6648060382718565763113635718482087395220791593, -6648060382718565763113635718482087395218694440⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨721949241039261777105100229686264310385356161447, 721949241039261777105100229686264310385356161448⟩
def centerDExp : DyadicInterval precision := ⟨544171400918647169539408046331758482200227109223, 544171400918647169539408046331758484399250364776⟩
def centerDLog : DyadicInterval precision := ⟨462587568506596564045749998967475930132416323351, 462587568506596564045749998967475932331439578904⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨544171400918647169539408046331758482749982923111, scale precision, 544171400918647169539408046331758483849494550888, scale precision,
    1, 128, 1, 128, ⟨-1443898482078523554210200459372528622247213277149, -1443898482078523554210200459372528622247211179996⟩, ⟨-1443898482078523554210200459372528619294213465789, -1443898482078523554210200459372528619294211368636⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨726138401848208530510351953917022565035490294200, 726138401848208530510351953917022565035490294201⟩
def centerCExp : DyadicInterval precision := ⟨541060764918498579022071367606480125823132597048, 541060764918498579022071367606480128022155852601⟩
def centerCLog : DyadicInterval precision := ⟨460319138626403000604377013164127065169287432440, 460319138626403000604377013164127067368310687993⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨541060764918498579022071367606480126372888410936, scale precision, 541060764918498579022071367606480127472400038713, scale precision,
    1, 128, 1, 128, ⟨-1452276803696417061020703907834045131555970152549, -1452276803696417061020703907834045131555968055396⟩, ⟨-1452276803696417061020703907834045128585993121406, -1452276803696417061020703907834045128585991024253⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1779069064604852499668366947178498976076001659316, 1779069064604852499668366947178498976076001659317⟩
def centerBExp : DyadicInterval precision := ⟨128078428938362310091888017588710579360210703148, 128078428938362310091888017588710581559233958701⟩
def centerBLog : DyadicInterval precision := ⟨122774097176940007287474385286924840469772472368, 122774097176940007287474385286924842668795727921⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨128078428938362310091888017588710579909966517036, scale precision, 128078428938362310091888017588710581009478144813, scale precision,
    3, 128, 3, 128, ⟨-3558138129209704999336733894356997958425262313845, -3558138129209704999336733894356997958425260216692⟩, ⟨-3558138129209704999336733894356997945878746420573, -3558138129209704999336733894356997945878744323420⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978073808, 3482318024844347500022322904444928295572395253⟩
def wholeAExp : DyadicInterval precision := ⟨1454553569581723058392238696431353224119669669100, 1455183847209450510423929547351191477780877052172⟩
def wholeALog : DyadicInterval precision := ⟨1009557569928173087760872372803888449827653659813, 1009873425488092576137085252579843092274389747387⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1454553569581723058392238696431353224669425482988, scale precision, 1455183847209450510423929547351191477231121238284, scale precision,
    0, 128, 0, 128, ⟨-6964636049688695000044645808889857143527710010, -6964636049688695000044645808889857143525612857⟩, ⟨-6331484897294127007240142282170268789814576090, -6331484897294127007240142282170268789812478937⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨716228578308099727358082939138935890959899212494, 727686670816724440524685346233204921246428500689⟩
def wholeDExp : DyadicInterval precision := ⟨539915612896337333160506278237532711076442060493, 548448150163327086956497611001597703886791384129⟩
def wholeDLog : DyadicInterval precision := ⟨459483149562382791203438629890379326034218128951, 465700648921796470149242465934935277251827483709⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨539915612896337333160506278237532711626197874381, scale precision, 548448150163327086956497611001597703337035570241, scale precision,
    1, 128, 1, 128, ⟨-1455373341633448881049370692466409843980996201432, -1455373341633448881049370692466409843980994104279⟩, ⟨-1432457156616199454716165878277871780454813181077, -1432457156616199454716165878277871780454811083924⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨720206400288607958471211247095533072076427912698, 732088450015273885412168945467779610187390537764⟩
def wholeCExp : DyadicInterval precision := ⟨536673131676134175886659866352304689528622889653, 545470798661596717495093304191272547527528181741⟩
def wholeCLog : DyadicInterval precision := ⟨457113461540330669166646829324555651878222987574, 463534112130964182759725604875119320414808570135⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨536673131676134175886659866352304690078378703541, scale precision, 545470798661596717495093304191272546977772367853, scale precision,
    1, 128, 1, 128, ⟨-1464176900030547770824337890935559221871911334991, -1464176900030547770824337890935559221871909237838⟩, ⟨-1440412800577215916942422494191066142679874224668, -1440412800577215916942422494191066142679872127515⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1761630872613749578315223637688046152944331403158, 1796565156237215979596483990466467059040684533887⟩
def wholeBExp : DyadicInterval precision := ⟨125048314545172815726990485764531017095437862828, 131171574157568086265269840137981128146725360080⟩
def wholeBLog : DyadicInterval precision := ⟨119985471733263886206512940327500585293060409009, 125615252692523699847363260387482011339991550216⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨125048314545172815726990485764531017645193676716, scale precision, 131171574157568086265269840137981127596969546192, scale precision,
    3, 128, 3, 128, ⟨-3593130312474431959192967980932934124506638821909, -3593130312474431959192967980932934124506636724756⟩, ⟨-3523261745227499156630447275376092299763335045734, -3523261745227499156630447275376092299763332948581⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0326StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0327StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0327StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3324030191359282881556817859241043973740987770, 3324030191359282881556817859241043973740987771⟩
def centerAExp : DyadicInterval precision := ⟨1454868674354870198336951421367206718659928330939, 1454868674354870198336951421367206720858951586492⟩
def centerALog : DyadicInterval precision := ⟨1009715489181788885783740077569471416073335956070, 1009715489181788885783740077569471418272359211623⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1454868674354870198336951421367206719209684144827, scale precision, 1454868674354870198336951421367206720309195772604, scale precision,
    0, 128, 0, 128, ⟨-6648060382718565763113635718482088499745256643, -6648060382718565763113635718482088499743159490⟩, ⟨-6648060382718565763113635718482087395220791593, -6648060382718565763113635718482087395218694440⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨710524563403850356500890582610538039823374015368, 710524563403850356500890582610538039823374015369⟩
def centerDExp : DyadicInterval precision := ⟨552745918518612785766768712299414359359889019406, 552745918518612785766768712299414361558912274959⟩
def centerDLog : DyadicInterval precision := ⟨468822363559667384554973018042110607773397723001, 468822363559667384554973018042110609972420978554⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨552745918518612785766768712299414359909644833294, scale precision, 552745918518612785766768712299414361009156461071, scale precision,
    1, 128, 1, 128, ⟨-1421049126807700713001781165221076081100344655889, -1421049126807700713001781165221076081100342558736⟩, ⟨-1421049126807700713001781165221076078193153502733, -1421049126807700713001781165221076078193151405580⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨714689340292978742994152896412594565063755978532, 714689340292978742994152896412594565063755978533⟩
def centerCExp : DyadicInterval precision := ⟨549604607247417253311370623336825087982281555936, 549604607247417253311370623336825090181304811489⟩
def centerCLog : DyadicInterval precision := ⟨466541305682120000621106617472176027510370102319, 466541305682120000621106617472176029709393357872⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨549604607247417253311370623336825088532037369824, scale precision, 549604607247417253311370623336825089631548997601, scale precision,
    1, 128, 1, 128, ⟨-1429378680585957485988305792825189131589416729765, -1429378680585957485988305792825189131589414632612⟩, ⟨-1429378680585957485988305792825189128665609281519, -1429378680585957485988305792825189128665607184366⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1744845065637816851773622135486744767521042307059, 1744845065637816851773622135486744767521042307060⟩
def centerBExp : DyadicInterval precision := ⟨134219540744142823873873299531141381387917246861, 134219540744142823873873299531141383586940502414⟩
def centerBLog : DyadicInterval precision := ⟨128409517748529986281771445376243208952670731293, 128409517748529986281771445376243211151693986846⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨134219540744142823873873299531141381937673060749, scale precision, 134219540744142823873873299531141383037184688526, scale precision,
    3, 128, 3, 128, ⟨-3489690131275633703547244270973489541028315519206, -3489690131275633703547244270973489541028313422053⟩, ⟨-3489690131275633703547244270973489529055855806177, -3489690131275633703547244270973489529055853709024⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978073808, 3482318024844347500022322904444928295572395253⟩
def wholeAExp : DyadicInterval precision := ⟨1454553569581723058392238696431353224119669669100, 1455183847209450510423929547351191477780877052172⟩
def wholeALog : DyadicInterval precision := ⟨1009557569928173087760872372803888449827653659813, 1009873425488092576137085252579843092274389747387⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1454553569581723058392238696431353224669425482988, scale precision, 1455183847209450510423929547351191477231121238284, scale precision,
    0, 128, 0, 128, ⟨-6964636049688695000044645808889857143527710010, -6964636049688695000044645808889857143525612857⟩, ⟨-6331484897294127007240142282170268789814576090, -6331484897294127007240142282170268789812478937⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨704837076587479092158941059188951191105662022838, 716228578308099727358082939138935890959899212495⟩
def wholeDExp : DyadicInterval precision := ⟨548448150163327086956497611001597701687768128576, 557064765387537285209117120927584104924255812884⟩
def wholeDLog : DyadicInterval precision := ⟨465700648921796470149242465934935275052804228156, 471952686082951260798866870121334520250908543212⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨548448150163327086956497611001597702237523942464, scale precision, 557064765387537285209117120927584104374499998996, scale precision,
    1, 128, 1, 128, ⟨-1432457156616199454716165878277871783384785766055, -1432457156616199454716165878277871783384783668902⟩, ⟨-1409674153174958184317882118377902380768999045198, -1409674153174958184317882118377902380768996948045⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨708791845014549479361058033027622614364779931304, 720604627137442571971635842887643880059900459959⟩
def wholeCExp : DyadicInterval precision := ⟨545173622203440533669542480593903941326890606539, 554058116025949159776372340721239701662571647584⟩
def wholeCLog : DyadicInterval precision := ⟨463317688611057747267494064599643733478612100586, 469774160370831638064378918173986661931356670914⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨545173622203440533669542480593903941876646420427, scale precision, 554058116025949159776372340721239701112815833696, scale precision,
    1, 128, 1, 128, ⟨-1441209254274885143943271685775287761593587546897, -1441209254274885143943271685775287761593585449744⟩, ⟨-1417583690029098958722116066055245227279407941867, -1417583690029098958722116066055245227279405844714⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1727524551440626723836549661300995685643731303917, 1762226079877476289842927684052120418677636043986⟩
def wholeBExp : DyadicInterval precision := ⟨131064776485844737456511339257400013878834120014, 137438861765964433784518696587861868669407655362⟩
def wholeBLog : DyadicInterval precision := ⟨125517247524620304996542505988065007764074209408, 131355084454864415903821387611524444059135724543⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨131064776485844737456511339257400014428589933902, scale precision, 137438861765964433784518696587861868119651841474, scale precision,
    3, 128, 3, 128, ⟨-3524452159754952579685855368104240843485593148320, -3524452159754952579685855368104240843485591051167⟩, ⟨-3455049102881253447673099322601991365441453206333, -3455049102881253447673099322601991365441451109180⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0327StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0328StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0328StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3007454792385135386557447160398116569795982507, 3007454792385135386557447160398116569795982508⟩
def centerAExp : DyadicInterval precision := ⟨1455499088168743985690617101081856958065120579782, 1455499088168743985690617101081856960264143835335⟩
def centerALog : DyadicInterval precision := ⟨1010031378851376569271247815372298287995916580825, 1010031378851376569271247815372298290194939836378⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1455499088168743985690617101081856958614876393670, scale precision, 1455499088168743985690617101081856959714388021447, scale precision,
    0, 128, 0, 128, ⟨-6014909584770270773114894320796233691616047245, -6014909584770270773114894320796233691613950092⟩, ⟨-6014909584770270773114894320796232587569979939, -6014909584770270773114894320796232587567882786⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨745000746231477256788872225997272556554271720183, 745000746231477256788872225997272556554271720184⟩
def centerDExp : DyadicInterval precision := ⟨527273459613343376350322664808293438125402667750, 527273459613343376350322664808293440324425923303⟩
def centerDLog : DyadicInterval precision := ⟨450222147616224759094825146719602335307459476714, 450222147616224759094825146719602337506482732267⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨527273459613343376350322664808293438675158481638, scale precision, 527273459613343376350322664808293439774670109415, scale precision,
    1, 128, 1, 128, ⟨-1490001492462954513577744451994545114632362931693, -1490001492462954513577744451994545114632360834540⟩, ⟨-1490001492462954513577744451994545111584726046197, -1490001492462954513577744451994545111584723949044⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨748835603695682943212133512379222300965856727374, 748835603695682943212133512379222300965856727375⟩
def centerCExp : DyadicInterval precision := ⟨524513664929833673196846490383192269926345243430, 524513664929833673196846490383192272125368498983⟩
def centerCLog : DyadicInterval precision := ⟨448192634262458970710164415493436875949346145357, 448192634262458970710164415493436878148369400910⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨524513664929833673196846490383192270476101057318, scale precision, 524513664929833673196846490383192271575612685095, scale precision,
    1, 128, 1, 128, ⟨-1497671207391365886424267024758444603463550708658, -1497671207391365886424267024758444603463548611505⟩, ⟨-1497671207391365886424267024758444600399878297996, -1497671207391365886424267024758444600399876200843⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1847573647831560465445161454183859740748349566279, 1847573647831560465445161454183859740748349566280⟩
def centerBExp : DyadicInterval precision := ⟨116617264209956905654985387570158540275313689171, 116617264209956905654985387570158542474336944724⟩
def centerBLog : DyadicInterval precision := ⟨112198228522628319027475837749280606032720861693, 112198228522628319027475837749280608231744117246⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨116617264209956905654985387570158540825069503059, scale precision, 116617264209956905654985387570158541924581130836, scale precision,
    3, 128, 3, 128, ⟨-3695147295663120930890322908367719488386494994742, -3695147295663120930890322908367719488386492897589⟩, ⟨-3695147295663120930890322908367719474606905367538, -3695147295663120930890322908367719474606903270385⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2849167218250950044280193223065006085312260897, 3165742448647063503620071141085134670978073809⟩
def wholeAExp : DyadicInterval precision := ⟨1455183847209450510423929547351191475581853796619, 1455814397256041217437249255499380274426951865358⟩
def wholeALog : DyadicInterval precision := ⟨1009873425488092576137085252579843090075366491834, 1010189349275934740575240882696318024149327762719⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1455183847209450510423929547351191476131609610507, scale precision, 1455814397256041217437249255499380273877196051470, scale precision,
    0, 128, 0, 128, ⟨-6331484897294127007240142282170269894099816297, -6331484897294127007240142282170269894097719144⟩, ⟨-5698334436501900088560386446130011618722097206, -5698334436501900088560386446130011618720000053⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨739212305620516788391447838602016614455786978945, 750806424999049798752938234956163650116084001298⟩
def wholeDExp : DyadicInterval precision := ⟨523100967242339682629524513379347095252573454615, 531466696428681553786643034174516971757505971701⟩
def wholeDLog : DyadicInterval precision := ⟨447152665109602019123525890115620509603294783509, 453300409610535438784277685833236609207550076241⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨523100967242339682629524513379347095802329268503, scale precision, 531466696428681553786643034174516971207750157813, scale precision,
    1, 128, 1, 128, ⟨-1501612849998099597505876469912327301768142166202, -1501612849998099597505876469912327301768140069049⟩, ⟨-1478424611241033576782895677204033227399779389680, -1478424611241033576782895677204033227399777292527⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨742834361291372729891888239281078093017880189845, 754855386585398468500627975800350234813760938711⟩
def wholeCExp : DyadicInterval precision := ⟨520210571891979109741571502838567208045673840893, 528838934636989681341346835359242054633795187274⟩
def wholeCLog : DyadicInterval precision := ⟨445022567785922596974052891693358792351683124551, 451372123952011486061135753011893104665648278821⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨520210571891979109741571502838567208595429654781, scale precision, 528838934636989681341346835359242054084039373386, scale precision,
    1, 128, 1, 128, ⟨-1509710773170796937001255951600700471172030218896, -1509710773170796937001255951600700471172028121743⟩, ⟨-1485668722582745459783776478562156184516453810190, -1485668722582745459783776478562156184516451713037⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1829917287311471905349548649499246234872039055077, 1865282740747114709560789611291861752887150191839⟩
def wholeBExp : DyadicInterval precision := ⟨113825118278592471637931064216425558084901236744, 119469280422197957283106737942538028131445662546⟩
def wholeBLog : DyadicInterval precision := ⟨109610121822576387562790882916441633562079707771, 114837107272358414470650904838073592750288894353⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨113825118278592471637931064216425558634657050632, scale precision, 119469280422197957283106737942538027581689848658, scale precision,
    3, 128, 3, 128, ⟨-3730565481494229419121579222583723512833103867784, -3730565481494229419121579222583723512833101770631⟩, ⟨-3659834574622943810699097298998492463018760153793, -3659834574622943810699097298998492463018758056640⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0328StableWitnesses

end


