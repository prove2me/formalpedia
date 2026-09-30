-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0070StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0070StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:46:31.264463+00:00
-- url     : https://prove2.me/theorems/bccb8d7e-ee75-40e0-bf04-8a0d7b393ea4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0070StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0071StableWitnesses, GeneralCK.Certificates.E8TAxisProd00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0070StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0071StableWitnesses, GeneralCK.Certificates.E8TAxisProd0072StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0070StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0071StableWitnesses, GeneralCK.Certificates.E8TAxisProd0072StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0070StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0071StableWitnesses, GeneralCK.Certificates.E8TAxisProd0072StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0070StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0071StableWitnesses, GeneralCK/Certificates/E8TAxisProd0072StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0070StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0070StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4432047174048269527644776165804031130864675904, 4432047174048269527644776165804031130864675905⟩
def centerAExp : DyadicInterval precision := ⟨1452664369350591901250217311774540048662792202314, 1452664369350591901250217311774540050861815457867⟩
def centerALog : DyadicInterval precision := ⟨1008610412272733567070593870872814919869682069664, 1008610412272733567070593870872814922068705325217⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1452664369350591901250217311774540049212548016202, scale precision, 1452664369350591901250217311774540050312059643979, scale precision,
    0, 128, 0, 128, ⟨-8864094348096539055289552331608062814830647821, -8864094348096539055289552331608062814828550668⟩, ⟨-8864094348096539055289552331608061708630152947, -8864094348096539055289552331608061708628055794⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨171538997309695458050826399408847654410041355932, 171538997309695458050826399408847654410041355933⟩
def centerCExp : DyadicInterval precision := ⟨1155717006400697186159529709117728916448560790677, 1155717006400697186159529709117728918647584046230⟩
def centerCLog : DyadicInterval precision := ⟨851540628411629728550962471590575925564239217522, 851540628411629728550962471590575927763262473075⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1155717006400697186159529709117728916998316604565, scale precision, 1155717006400697186159529709117728918097828232342, scale precision,
    0, 128, 0, 128, ⟨-343077994619390916101652798817695309515296358059, -343077994619390916101652798817695309515294260906⟩, ⟨-343077994619390916101652798817695308124871162824, -343077994619390916101652798817695308124869065671⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨343873197344268921505429276325898414392065692615, 343873197344268921505429276325898414392065692616⟩
def centerBExp : DyadicInterval precision := ⟨912916596877989280495260089158425707662336373662, 912916596877989280495260089158425709861359629215⟩
def centerBLog : DyadicInterval precision := ⟨709249246894175130239058694383132542466437596151, 709249246894175130239058694383132544665460851704⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨912916596877989280495260089158425708212092187550, scale precision, 912916596877989280495260089158425709311603815327, scale precision,
    0, 128, 0, 128, ⟨-687746394688537843010858552651796829664244620263, -687746394688537843010858552651796829664242523110⟩, ⟨-687746394688537843010858552651796827904020247351, -687746394688537843010858552651796827904018150198⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 5065202303167835215808940955361609459283110735⟩
def wholeAExp : DyadicInterval precision := ⟨1451406261215048238048665418490328880814971300707, 1453923564186661310665317018859587709527417053272⟩
def wholeALog : DyadicInterval precision := ⟨1007979314346565773386485143059333172819831600857, 1009241782561842849966002591658486094460586802138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1451406261215048238048665418490328881364727114595, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-10130404606335670431617881910723219472146955901, -10130404606335670431617881910723219472144858748⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨162861817784200237565871966520572794999609887195, 180229928962105787157545353371120701075525520159⟩
def wholeCExp : DyadicInterval precision := ⟨1142053299983816464308427514740350847627507001189, 1169522177914865128352659833859980549396374698749⟩
def wholeCLog : DyadicInterval precision := ⟨843890583993838071132742594415801782037440985357, 859229422313229852746433528080764617965719577944⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1142053299983816464308427514740350848177262815077, scale precision, 1169522177914865128352659833859980548846618884861, scale precision,
    0, 128, 0, 128, ⟨-360459857924211574315090706742241402854582320051, -360459857924211574315090706742241402854580222898⟩, ⟨-325723635568400475131743933041145589312214593157, -325723635568400475131743933041145589312212496004⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨326421309931081011329908709873818033517884938468, 361429001373380832629520534349533653251055519395⟩
def wholeBExp : DyadicInterval precision := ⟨891245737101262683231821777009961823640143117119, 934981420214208148924752773574616557474551697550⟩
def wholeBLog : DyadicInterval precision := ⟨695849158323487264058235982453080193899714236712, 722767868800246844242748713431166336975735521191⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨891245737101262683231821777009961824189898931007, scale precision, 934981420214208148924752773574616556924795883662, scale precision,
    0, 128, 0, 128, ⟨-722858002746761665259041068699067307403624418569, -722858002746761665259041068699067307403622321416⟩, ⟨-652842619862162022659817419747636066176428691796, -652842619862162022659817419747636066176426594643⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0070StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0071StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0071StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978073808, 3165742448647063503620071141085134670978073809⟩
def centerAExp : DyadicInterval precision := ⟨1455183847209450510423929547351191475581853796619, 1455183847209450510423929547351191477780877052172⟩
def centerALog : DyadicInterval precision := ⟨1009873425488092576137085252579843090075366491834, 1009873425488092576137085252579843092274389747387⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1455183847209450510423929547351191476131609610507, scale precision, 1455183847209450510423929547351191477231121238284, scale precision,
    0, 128, 0, 128, ⟨-6331484897294127007240142282170269894099816297, -6331484897294127007240142282170269894097719144⟩, ⟨-6331484897294127007240142282170268789814576090, -6331484897294127007240142282170268789812478937⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨186354394939751837427234698441450889506082638516, 186354394939751837427234698441450889506082638517⟩
def centerCExp : DyadicInterval precision := ⟨1132521681823606051222395651713336554434258106725, 1132521681823606051222395651713336556633281362278⟩
def centerCLog : DyadicInterval precision := ⟨838530206342391626211135227062589235496945292736, 838530206342391626211135227062589237695968548289⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1132521681823606051222395651713336554984013920613, scale precision, 1132521681823606051222395651713336556083525548390, scale precision,
    0, 128, 0, 128, ⟨-372708789879503674854469396882901779721617663297, -372708789879503674854469396882901779721615566144⟩, ⟨-372708789879503674854469396882901778302714987921, -372708789879503674854469396882901778302712890768⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨376369150439637581292147110637812924897628710625, 376369150439637581292147110637812924897628710626⟩
def centerBExp : DyadicInterval precision := ⟨873209285966443987375362429931403537239211520159, 873209285966443987375362429931403539438234775712⟩
def centerBLog : DyadicInterval precision := ⟨684601940199811848940075121318506259999733598991, 684601940199811848940075121318506262198756854544⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨873209285966443987375362429931403537788967334047, scale precision, 873209285966443987375362429931403538888478961824, scale precision,
    0, 128, 0, 128, ⟨-752738300879275162584294221275625850715391861723, -752738300879275162584294221275625850715389764570⟩, ⟨-752738300879275162584294221275625848875125077934, -752738300879275162584294221275625848875122980781⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 3798893981423257492988718450954299577395465181⟩
def wholeAExp : DyadicInterval precision := ⟨1453923564186661310665317018859587707328393797719, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1009241782561842849966002591658486092261563546585, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453923564186661310665317018859587707878149611607, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-7597787962846514985977436901908599707413204648, -7597787962846514985977436901908599707411107495⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨177653362642421903985383099533020772929530993741, 195070384091725537299207625964822441604096874998⟩
def wholeCExp : DyadicInterval precision := ⟨1119093832522548353760792784395684184277949257102, 1146087191884889049255178951498653941075489630982⟩
def wholeCLog : DyadicInterval precision := ⟨830945157630913290200624245407414187859975664587, 846153250717279300440655301955098260381673404805⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1119093832522548353760792784395684184827705070990, scale precision, 1146087191884889049255178951498653940525733817094, scale precision,
    0, 128, 0, 128, ⟨-390140768183451074598415251929644883926158742953, -390140768183451074598415251929644883926156645800⟩, ⟨-355306725284843807970766199066041545158009025667, -355306725284843807970766199066041545158006928514⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨358721125013013616465942719726870605036528329661, 394131280415088114324880764542299808171984852990⟩
def wholeBExp : DyadicInterval precision := ⟨852240338090969698012242422231538055945424350287, 894554471427663164708455914071574107988384165283⟩
def wholeBLog : DyadicInterval precision := ⟨671416323310479763794961458183140403243502794967, 697903064989442090312621735187922064498395080758⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨852240338090969698012242422231538056495180164175, scale precision, 894554471427663164708455914071574107438628351395, scale precision,
    0, 128, 0, 128, ⟨-788262560830176228649761529084599617286743569007, -788262560830176228649761529084599617286741471854⟩, ⟨-717442250026027232931885439453741209174879846413, -717442250026027232931885439453741209174877749260⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0071StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0072StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0072StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978073808, 3165742448647063503620071141085134670978073809⟩
def centerAExp : DyadicInterval precision := ⟨1455183847209450510423929547351191475581853796619, 1455183847209450510423929547351191477780877052172⟩
def centerALog : DyadicInterval precision := ⟨1009873425488092576137085252579843090075366491834, 1009873425488092576137085252579843092274389747387⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1455183847209450510423929547351191476131609610507, scale precision, 1455183847209450510423929547351191477231121238284, scale precision,
    0, 128, 0, 128, ⟨-6331484897294127007240142282170269894099816297, -6331484897294127007240142282170269894097719144⟩, ⟨-6331484897294127007240142282170268789814576090, -6331484897294127007240142282170268789812478937⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨170252638495234241027575132082892085370180792619, 170252638495234241027575132082892085370180792620⟩
def centerCExp : DyadicInterval precision := ⟨1157753235436019582024414064717411361587718781511, 1157753235436019582024414064717411363786742037064⟩
def centerCLog : DyadicInterval precision := ⟨852677252977656561354010438411630507207655061058, 852677252977656561354010438411630509406678316611⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1157753235436019582024414064717411362137474595399, scale precision, 1157753235436019582024414064717411363236986223176, scale precision,
    0, 128, 0, 128, ⟨-340505276990468482055150264165784171434352507943, -340505276990468482055150264165784171434350410790⟩, ⟨-340505276990468482055150264165784170046372759689, -340505276990468482055150264165784170046370662536⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨342527124855344147975691026216652607152220235330, 342527124855344147975691026216652607152220235331⟩
def centerBExp : DyadicInterval precision := ⟨914599775845407951141658852493733684778068654548, 914599775845407951141658852493733686977091910101⟩
def centerBLog : DyadicInterval precision := ⟨710284909980464209864602503695014410309771527727, 710284909980464209864602503695014412508794783280⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨914599775845407951141658852493733685327824468436, scale precision, 914599775845407951141658852493733686427336096213, scale precision,
    0, 128, 0, 128, ⟨-685054249710688295951382052433305215182933995783, -685054249710688295951382052433305215182931898630⟩, ⟨-685054249710688295951382052433305213425949042693, -685054249710688295951382052433305213425946945540⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 3798893981423257492988718450954299577395465181⟩
def wholeAExp : DyadicInterval precision := ⟨1453923564186661310665317018859587707328393797719, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1009241782561842849966002591658486092261563546585, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453923564186661310665317018859587707878149611607, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-7597787962846514985977436901908599707413204648, -7597787962846514985977436901908599707411107495⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨161577436401748847597890018140472027124415234621, 178941488288963307887393676781801825848635031176⟩
def wholeCExp : DyadicInterval precision := ⟨1144068714643020262775623526541037562798580998780, 1171579559607242623643396951962840840340700091833⟩
def wholeCLog : DyadicInterval precision := ⟨845021496309331141540576730411200639800338817897, 860371826143762983574909401721668987473088645056⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1144068714643020262775623526541037563348336812668, scale precision, 1171579559607242623643396951962840839790944277945, scale precision,
    0, 128, 0, 128, ⟨-357882976577926615774787353563603652399561988954, -357882976577926615774787353563603652399559891801⟩, ⟨-323154872803497695195780036280944053563031722542, -323154872803497695195780036280944053563029625389⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨325083004739724723125590110073889241739908452155, 360074740751160892894090487962528567327495184604⟩
def wholeBExp : DyadicInterval precision := ⟨892898965645121959397532364804649247711416359290, 936695324557495237835579476887656905665291637098⟩
def wholeBLog : DyadicInterval precision := ⟨696875765659682097297052894707441000419020320750, 723812724390392070070417718976900628291755173688⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨892898965645121959397532364804649248261172173178, scale precision, 936695324557495237835579476887656905115535823210, scale precision,
    0, 128, 0, 128, ⟨-720149481502321785788180975925057135554834572546, -720149481502321785788180975925057135554832475393⟩, ⟨-650166009479449446251180220147778482622048087847, -650166009479449446251180220147778482622045990694⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0072StableWitnesses

end


