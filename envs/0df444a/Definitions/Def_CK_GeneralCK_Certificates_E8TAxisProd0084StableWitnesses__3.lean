-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0084StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0084StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:39:03.121528+00:00
-- url     : https://prove2.me/theorems/25cb311f-d34b-4eca-93e1-44a4deca489c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0084StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0085StableWitnesses, GeneralCK.Certificates.E8TAxisProd00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0084StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0085StableWitnesses, GeneralCK.Certificates.E8TAxisProd0086StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0084StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0085StableWitnesses, GeneralCK.Certificates.E8TAxisProd0086StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0084StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0085StableWitnesses, GeneralCK.Certificates.E8TAxisProd0086StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0084StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0085StableWitnesses, GeneralCK/Certificates/E8TAxisProd0086StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0084StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0084StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2849167218250950044280193223065006085312260897, 2849167218250950044280193223065006085312260898⟩
def centerAExp : DyadicInterval precision := ⟨1455814397256041217437249255499380272227928609805, 1455814397256041217437249255499380274426951865358⟩
def centerALog : DyadicInterval precision := ⟨1010189349275934740575240882696318021950304507166, 1010189349275934740575240882696318024149327762719⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1455814397256041217437249255499380272777684423693, scale precision, 1455814397256041217437249255499380273877196051470, scale precision,
    0, 128, 0, 128, ⟨-5698334436501900088560386446130012722529043537, -5698334436501900088560386446130012722526946384⟩, ⟨-5698334436501900088560386446130011618722097206, -5698334436501900088560386446130011618720000053⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨130992033893699994791369923976531926829092122734, 130992033893699994791369923976531926829092122735⟩
def centerDExp : DyadicInterval precision := ⟨1221656411836274069288773586476386668146918568609, 1221656411836274069288773586476386670345941824162⟩
def centerDLog : DyadicInterval precision := ⟨887906164936387943905585824070712899195502313636, 887906164936387943905585824070712901394525569189⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1221656411836274069288773586476386668696674382497, scale precision, 1221656411836274069288773586476386669796186010274, scale precision,
    0, 128, 0, 128, ⟨-261984067787399989582739847953063854315873506824, -261984067787399989582739847953063854315871409671⟩, ⟨-261984067787399989582739847953063853000497081267, -261984067787399989582739847953063853000494984114⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨133868355831339897742652088998044695120727790875, 133868355831339897742652088998044695120727790876⟩
def centerCExp : DyadicInterval precision := ⟨1216857278405476926883467746628918246413988186780, 1216857278405476926883467746628918248613011442333⟩
def centerCLog : DyadicInterval precision := ⟨885289762419703268531171103588051492381868591853, 885289762419703268531171103588051494580891847406⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1216857278405476926883467746628918246963744000668, scale precision, 1216857278405476926883467746628918248063255628445, scale precision,
    0, 128, 0, 128, ⟨-267736711662679795485304177996089390901738683440, -267736711662679795485304177996089390901736586287⟩, ⟨-267736711662679795485304177996089389581174577215, -267736711662679795485304177996089389581172480062⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨267394683788496671523088778869818964226188093548, 267394683788496671523088778869818964226188093549⟩
def centerBExp : DyadicInterval precision := ⟨1013638863902541394655891421818773588804921832282, 1013638863902541394655891421818773591003945087835⟩
def centerBLog : DyadicInterval precision := ⟨769966907297493862546476590491917510535344241055, 769966907297493862546476590491917512734367496608⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1013638863902541394655891421818773589354677646170, scale precision, 1013638863902541394655891421818773590454189273947, scale precision,
    0, 128, 0, 128, ⟨-534789367576993343046177557739637929245035302311, -534789367576993343046177557739637929245033205158⟩, ⟨-534789367576993343046177557739637927659719169034, -534789367576993343046177557739637927659717071881⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 3165742448647063503620071141085134670978073809⟩
def wholeAExp : DyadicInterval precision := ⟨1455183847209450510423929547351191475581853796619, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1009873425488092576137085252579843090075366491834, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1455183847209450510423929547351191476131609610507, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-6331484897294127007240142282170269894099816297, -6331484897294127007240142282170269894097719144⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨126999067220414009923202423697912773180597398746, 134987245269836870215393179468011326867547174259⟩
def wholeDExp : DyadicInterval precision := ⟨1214995512532168524628632240632930002334514119327, 1228350054579566692017908102915209767793957734212⟩
def wholeDLog : DyadicInterval precision := ⟨884273498322789745939213484257675325137621613543, 891547615580027951955449639520829064234092557127⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1214995512532168524628632240632930002884269933215, scale precision, 1228350054579566692017908102915209767244201920324, scale precision,
    0, 128, 0, 128, ⟨-269974490539673740430786358936022654396389215748, -269974490539673740430786358936022654396387118595⟩, ⟨-253998134440828019846404847395825545707091570879, -253998134440828019846404847395825545707089473726⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨129554310903328861618553401759095070205044128551, 138185076934533291384460203659823029201118705569⟩
def wholeCExp : DyadicInterval precision := ⟨1209690199028879381733560717407416113431654050014, 1224062337940262835884041942228948969667752895904⟩
def wholeCLog : DyadicInterval precision := ⟨881373656190846597166423362808244089366623664363, 889216072642414855396552704879363497020149421829⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1209690199028879381733560717407416113981409863902, scale precision, 1224062337940262835884041942228948969117997082016, scale precision,
    0, 128, 0, 128, ⟨-276370153869066582768920407319646059066432501109, -276370153869066582768920407319646059066430403956⟩, ⟨-259108621806657723237106803518190139753693796050, -259108621806657723237106803518190139753691698897⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨258856523389556057576596003104549794743303155871, 275952890023213657918162872037315490194966272903⟩
def wholeBExp : DyadicInterval precision := ⟨1001836852022489929581002918286635590698941039778, 1025551774732822142853509456880829106965098227895⟩
def wholeBLog : DyadicInterval precision := ⟨762981480182706404259605652287855778593802742651, 776984276000630970805974684708486431437270820557⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1001836852022489929581002918286635591248696853666, scale precision, 1025551774732822142853509456880829106415342414007, scale precision,
    0, 128, 0, 128, ⟨-551905780046427315836325744074630981191929468767, -551905780046427315836325744074630981191927371614⟩, ⟨-517713046779112115153192006209099588703156888168, -517713046779112115153192006209099588703154791015⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0084StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0085StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0085StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1899443256066344012630337314537754309230277491, 1899443256066344012630337314537754309230277492⟩
def centerAExp : DyadicInterval precision := ⟨1457707683773513925477741956702213444480153619489, 1457707683773513925477741956702213446679176875042⟩
def centerALog : DyadicInterval precision := ⟨1011137530350683182654731711817158197559546439255, 1011137530350683182654731711817158199758569694808⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1457707683773513925477741956702213445029909433377, scale precision, 1457707683773513925477741956702213446129421061154, scale precision,
    0, 128, 0, 128, ⟨-3798886512132688025260674629075509169648258520, -3798886512132688025260674629075509169646161367⟩, ⟨-3798886512132688025260674629075508067274948598, -3798886512132688025260674629075508067272851445⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨183130084206664803338173257357542686520853245489, 183130084206664803338173257357542686520853245490⟩
def centerDExp : DyadicInterval precision := ⟨1137529777074302590783266488860820386533899110215, 1137529777074302590783266488860820388732922365768⟩
def centerDLog : DyadicInterval precision := ⟨841349102754395012997791326891731422922496904416, 841349102754395012997791326891731425121520159969⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1137529777074302590783266488860820387083654924103, scale precision, 1137529777074302590783266488860820388183166551880, scale precision,
    0, 128, 0, 128, ⟨-366260168413329606676346514715085373748035442635, -366260168413329606676346514715085373748033345482⟩, ⟨-366260168413329606676346514715085372335379636478, -366260168413329606676346514715085372335377539325⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨185064426463719250346989728470101064961088652396, 185064426463719250346989728470101064961088652397⟩
def centerCExp : DyadicInterval precision := ⟨1134522647737562452972969427658519787540728101147, 1134522647737562452972969427658519789739751356700⟩
def centerCLog : DyadicInterval precision := ⟨839657138242594801957739836814033177473451261900, 839657138242594801957739836814033179672474517453⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1134522647737562452972969427658519788090483915035, scale precision, 1134522647737562452972969427658519789189995542812, scale precision,
    0, 128, 0, 128, ⟨-370128852927438500693979456940202130630378426531, -370128852927438500693979456940202130630376329378⟩, ⟨-370128852927438500693979456940202129213978280209, -370128852927438500693979456940202129213976183056⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨375007629872915579465429227647113556197499662127, 375007629872915579465429227647113556197499662128⟩
def centerBExp : DyadicInterval precision := ⟨874837748939270527343756194198458032057629107576, 874837748939270527343756194198458034256652363129⟩
def centerBLog : DyadicInterval precision := ⟨685620983558290487877774249648825815788860131768, 685620983558290487877774249648825817987883387321⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨874837748939270527343756194198458032607384921464, scale precision, 874837748939270527343756194198458033706896549241, scale precision,
    0, 128, 0, 128, ⟨-750015259745831158930858455294227113313420986373, -750015259745831158930858455294227113313418889220⟩, ⟨-750015259745831158930858455294227111476579759290, -750015259745831158930858455294227111476577662137⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1266295042977660303900587558721132456011189595, 2532592299075639559542598685704412299858871782⟩
def wholeAExp : DyadicInterval precision := ⟨1456445219907862366338488118605723266224391715309, 1458971240300741788424025014233787500747732609133⟩
def wholeALog : DyadicInterval precision := ⟨1010505341326056445575717809135292020753352555862, 1011769992837296815097311935000023819380660234895⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1456445219907862366338488118605723266774147529197, scale precision, 1458971240300741788424025014233787500197976795245, scale precision,
    0, 128, 0, 128, ⟨-5065184598151279119085197371408825151383222183, -5065184598151279119085197371408825151381125030⟩, ⟨-2532590085955320607801175117442264361314133481, -2532590085955320607801175117442264361312036328⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨175078047236001450214222015517899197240067851934, 191194719185872429583518944051791718612165764689⟩
def wholeDExp : DyadicInterval precision := ⟨1125044909933745912773463128462173913192954107499, 1150133363234016597447468800724884781224161812840⟩
def wholeDLog : DyadicInterval precision := ⟨834311627217828832252519695712052888541875377369, 848419291580521843596292009329506550515087162287⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1125044909933745912773463128462173913742709921387, scale precision, 1150133363234016597447468800724884780674405998952, scale precision,
    0, 128, 0, 128, ⟨-382389438371744859167037888103583437938498754820, -382389438371744859167037888103583437938496657667⟩, ⟨-350156094472002900428444031035798393781549051388, -350156094472002900428444031035798393781546954235⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨176365549723902348143424292968104815592821027151, 193778155013554683299889988710244792947684043084⟩
def wholeCExp : DyadicInterval precision := ⟨1121074541873184918683835318833754694517347845501, 1148108738982243371695955789645787237386737500354⟩
def wholeCLog : DyadicInterval precision := ⟨832066487812359628690065743459079145574258516651, 847285848658893358182028839792376454409643592298⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1121074541873184918683835318833754695067103659389, scale precision, 1148108738982243371695955789645787236836981686466, scale precision,
    0, 128, 0, 128, ⟨-387556310027109366599779977420489586612064583726, -387556310027109366599779977420489586612062486573⟩, ⟨-352731099447804696286848585936209630485823482272, -352731099447804696286848585936209630485821385119⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨357368151647964377800168166755575814690708449890, 392760784790180292139123525495050640775660750372⟩
def wholeBExp : DyadicInterval precision := ⟨853840182486705188164996754687631265688701292587, 896212258825935063445621868699349683882669134745⟩
def wholeBLog : DyadicInterval precision := ⟨672426534142843849849723373732993900147555703175, 698931057061302088777017185007738619376053928466⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨853840182486705188164996754687631266238457106475, scale precision, 896212258825935063445621868699349683332913320857, scale precision,
    0, 128, 0, 128, ⟨-785521569580360584278247050990101282492328885879, -785521569580360584278247050990101282492326788726⟩, ⟨-714736303295928755600336333511151628484901510184, -714736303295928755600336333511151628484899413031⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0085StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0086StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0086StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1899443256066344012630337314537754309230277491, 1899443256066344012630337314537754309230277492⟩
def centerAExp : DyadicInterval precision := ⟨1457707683773513925477741956702213444480153619489, 1457707683773513925477741956702213446679176875042⟩
def centerALog : DyadicInterval precision := ⟨1011137530350683182654731711817158197559546439255, 1011137530350683182654731711817158199758569694808⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1457707683773513925477741956702213445029909433377, scale precision, 1457707683773513925477741956702213446129421061154, scale precision,
    0, 128, 0, 128, ⟨-3798886512132688025260674629075509169648258520, -3798886512132688025260674629075509169646161367⟩, ⟨-3798886512132688025260674629075508067274948598, -3798886512132688025260674629075508067272851445⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨167038046908639942077002110251729919039591159538, 167038046908639942077002110251729919039591159539⟩
def centerDExp : DyadicInterval precision := ⟨1162857440134179458176971713073092284742695293446, 1162857440134179458176971713073092286941718548999⟩
def centerDLog : DyadicInterval precision := ⟨855522544774716820728738318780154511038543003600, 855522544774716820728738318780154513237566259153⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1162857440134179458176971713073092285292451107334, scale precision, 1162857440134179458176971713073092286391962735111, scale precision,
    0, 128, 0, 128, ⟨-334076093817279884154004220503459838770127067543, -334076093817279884154004220503459838770124970390⟩, ⟨-334076093817279884154004220503459837388239667764, -334076093817279884154004220503459837388237570611⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨168966579214564108507863584541420384906064698992, 168966579214564108507863584541420384906064698993⟩
def centerCExp : DyadicInterval precision := ⟨1159792576655074951020382451607634707890152449828, 1159792576655074951020382451607634710089175705381⟩
def centerCLog : DyadicInterval precision := ⟨853814729464122702015098104940602687386091102459, 853814729464122702015098104940602689585114358012⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1159792576655074951020382451607634708439908263716, scale precision, 1159792576655074951020382451607634709539419891493, scale precision,
    0, 128, 0, 128, ⟨-337933158429128217015727169082840770504900031660, -337933158429128217015727169082840770504897934507⟩, ⟨-337933158429128217015727169082840769119360861462, -337933158429128217015727169082840769119358764309⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨341181664743207029901761625605753194818793566138, 341181664743207029901761625605753194818793566139⟩
def centerBExp : DyadicInterval precision := ⟨916285290296825158783368498693788598941704995641, 916285290296825158783368498693788601140728251194⟩
def centerBLog : DyadicInterval precision := ⟨711321275186003626837213087546784675085785460207, 711321275186003626837213087546784677284808715760⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨916285290296825158783368498693788599491460809529, scale precision, 916285290296825158783368498693788600590972437306, scale precision,
    0, 128, 0, 128, ⟨-682363329486414059803523251211506390514464663146, -682363329486414059803523251211506390514462565993⟩, ⟨-682363329486414059803523251211506388760711698564, -682363329486414059803523251211506388760709601411⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1266295042977660303900587558721132456011189595, 2532592299075639559542598685704412299858871782⟩
def wholeAExp : DyadicInterval precision := ⟨1456445219907862366338488118605723266224391715309, 1458971240300741788424025014233787500747732609133⟩
def wholeALog : DyadicInterval precision := ⟨1010505341326056445575717809135292020753352555862, 1011769992837296815097311935000023819380660234895⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1456445219907862366338488118605723266774147529197, scale precision, 1458971240300741788424025014233787500197976795245, scale precision,
    0, 128, 0, 128, ⟨-5065184598151279119085197371408825151383222183, -5065184598151279119085197371408825151381125030⟩, ⟨-2532590085955320607801175117442264361314133481, -2532590085955320607801175117442264361312036328⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨159009523631476834293416684122073812609720086984, 175078047236001450214222015517899197240067851935⟩
def wholeDExp : DyadicInterval precision := ⟨1150133363234016597447468800724884779025138557287, 1175703819620526499056916402241341507477966942436⟩
def wholeDLog : DyadicInterval precision := ⟨848419291580521843596292009329506548316063906734, 862659221266056220624571274243273532289421478776⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1150133363234016597447468800724884779574894371175, scale precision, 1175703819620526499056916402241341506928211128548, scale precision,
    0, 128, 0, 128, ⟨-350156094472002900428444031035798395178724453502, -350156094472002900428444031035798395178722356349⟩, ⟨-318019047262953668586833368244147624536047149377, -318019047262953668586833368244147624536045052224⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨160293339111948018245674211080042528839685011782, 177653362642421903985383099533020772929530993742⟩
def wholeCExp : DyadicInterval precision := ⟨1146087191884889049255178951498653938876466375429, 1173640104298104188087122023740267537433953667589⟩
def wholeCLog : DyadicInterval precision := ⟨846153250717279300440655301955098258182650149252, 861515091957746564471801711065111147886994049810⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1146087191884889049255178951498653939426222189317, scale precision, 1173640104298104188087122023740267536884197853701, scale precision,
    0, 128, 0, 128, ⟨-355306725284843807970766199066041546560117046452, -355306725284843807970766199066041546560114949299⟩, ⟨-320586678223896036491348422160085056994775326659, -320586678223896036491348422160085056994773229506⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨323745279710826766446985521470106618369709766890, 358721125013013616465942719726870605036528329662⟩
def wholeBExp : DyadicInterval precision := ⟨894554471427663164708455914071574105789360909730, 938411625610146292314081985138210584633840883331⟩
def wholeBLog : DyadicInterval precision := ⟨697903064989442090312621735187922062299371825205, 724858293078083165410598662537004366869231215761⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨894554471427663164708455914071574106339116723618, scale precision, 938411625610146292314081985138210584084085069443, scale precision,
    0, 128, 0, 128, ⟨-717442250026027232931885439453741210971235569386, -717442250026027232931885439453741210971233472233⟩, ⟨-647490559421653532893971042940213235883219529213, -647490559421653532893971042940213235883217432060⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0086StableWitnesses

end


