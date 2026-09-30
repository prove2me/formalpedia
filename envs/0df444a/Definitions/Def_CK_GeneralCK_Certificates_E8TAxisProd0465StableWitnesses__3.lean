-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0465StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0465StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T00:34:05.44868+00:00
-- url     : https://prove2.me/theorems/13a3f945-0ffa-446c-a0b5-bae9195c00d4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0465StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0466StableWitnesses, GeneralCK.Certificates.E8TAxisProd04…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0465StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0466StableWitnesses, GeneralCK.Certificates.E8TAxisProd0467StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0465StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0466StableWitnesses, GeneralCK.Certificates.E8TAxisProd0467StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0465StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0466StableWitnesses, GeneralCK.Certificates.E8TAxisProd0467StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0465StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0466StableWitnesses, GeneralCK/Certificates/E8TAxisProd0467StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0465StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0465StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4906913324212444341793886191975635191530054563, 4906913324212444341793886191975635191530054564⟩
def centerAExp : DyadicInterval precision := ⟨1451720686451934407431403951699999116082005297895, 1451720686451934407431403951699999118281028553448⟩
def centerALog : DyadicInterval precision := ⟨1008137063309063130766142500412726798681612460495, 1008137063309063130766142500412726800880635716048⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1451720686451934407431403951699999116631761111783, scale precision, 1451720686451934407431403951699999117731272739560, scale precision,
    0, 128, 0, 128, ⟨-9813826648424888683587772383951270936520944858, -9813826648424888683587772383951270936518847705⟩, ⟨-9813826648424888683587772383951269829601370550, -9813826648424888683587772383951269829599273397⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨643330890011571853191447487766205018317129467057, 643330890011571853191447487766205018317129467058⟩
def centerDExp : DyadicInterval precision := ⟨605981822530277187962366989116632506149582094264, 605981822530277187962366989116632508348605349817⟩
def centerDLog : DyadicInterval precision := ⟨506947743551831449885580746844042863375923706013, 506947743551831449885580746844042865574946961566⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨605981822530277187962366989116632506699337908152, scale precision, 605981822530277187962366989116632507798849535929, scale precision,
    1, 128, 1, 128, ⟨-1286661780023143706382894975532410037960156226204, -1286661780023143706382894975532410037960154129051⟩, ⟨-1286661780023143706382894975532410035308363739178, -1286661780023143706382894975532410035308361642025⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨649276738953348387774508130050341530747643969840, 649276738953348387774508130050341530747643969841⟩
def centerCExp : DyadicInterval precision := ⟨601071177871152136564041856376246417861112930510, 601071177871152136564041856376246420060136186063⟩
def centerCLog : DyadicInterval precision := ⟨503472285536859444360023422421589829095962575199, 503472285536859444360023422421589831294985830752⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨601071177871152136564041856376246418410868744398, scale precision, 601071177871152136564041856376246419510380372175, scale precision,
    1, 128, 1, 128, ⟨-1298553477906696775549016260100683062832017568352, -1298553477906696775549016260100683062832015471199⟩, ⟨-1298553477906696775549016260100683060158560408167, -1298553477906696775549016260100683060158558311014⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1547583038368076402169654534904713027664834715928, 1547583038368076402169654534904713027664834715929⟩
def centerBExp : DyadicInterval precision := ⟨175813036087368104750680597158149719300283972552, 175813036087368104750680597158149721499307228105⟩
def centerBLog : DyadicInterval precision := ⟨166016471980955445380001042995894772527760260681, 166016471980955445380001042995894774726783516234⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨175813036087368104750680597158149719850039786440, scale precision, 175813036087368104750680597158149720949551414217, scale precision,
    3, 128, 3, 128, ⟨-3095166076736152804339309069809426059899690087688, -3095166076736152804339309069809426059899687990535⟩, ⟨-3095166076736152804339309069809426050759650873179, -3095166076736152804339309069809426050759648776026⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨4748624479255801076876082777124010865681651338, 5065202303167835215808940955361609459283110735⟩
def wholeAExp : DyadicInterval precision := ⟨1451406261215048238048665418490328880814971300707, 1452035179538035812075122148102075718654446240893⟩
def wholeALog : DyadicInterval precision := ⟨1007979314346565773386485143059333172819831600857, 1008294829281404787796718047455216465384960373552⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1451406261215048238048665418490328881364727114595, scale precision, 1452035179538035812075122148102075718104690427005, scale precision,
    0, 128, 0, 128, ⟨-10130404606335670431617881910723219472146955901, -10130404606335670431617881910723219472144858748⟩, ⟨-9497248958511602153752165554248021178024436730, -9497248958511602153752165554248021178022339577⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨637832247480472324939326434952621888088060941844, 648844592727412176647428020776866274458569907209⟩
def wholeDExp : DyadicInterval precision := ⟨601426740197304508434017275821189105530124808412, 610558820864912509175272747825498146169006720984⟩
def wholeDLog : DyadicInterval precision := ⟨503724208829984298099852655433700219831811463479, 510179642243321146984571771117295507804948082651⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨601426740197304508434017275821189106079880622300, scale precision, 610558820864912509175272747825498145619250907096, scale precision,
    1, 128, 1, 128, ⟨-1297689185454824353294856041553732550253079171733, -1297689185454824353294856041553732550253077074580⟩, ⟨-1275664494960944649878652869905243774860166148623, -1275664494960944649878652869905243774860164051470⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨643570302158419402762879584302270293330774637331, 654999444949650692225884277785961188367767393852⟩
def wholeCExp : DyadicInterval precision := ⟨596382411441572791003170645402394367212234065864, 605783320329306778067622524559805833916716464476⟩
def wholeCLog : DyadicInterval precision := ⟨500146128754795280057904653274814042559777307587, 506807415841710827876377431725930573022323739804⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨596382411441572791003170645402394367761989879752, scale precision, 605783320329306778067622524559805833366960650588, scale precision,
    1, 128, 1, 128, ⟨-1309998889899301384451768555571922378082773794201, -1309998889899301384451768555571922378082771697048⟩, ⟨-1287140604316838805525759168604540585335219611966, -1287140604316838805525759168604540585335217514813⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1531059044732848403809149521898466992152956339306, 1564181954805026104320258952767099483735001597994⟩
def wholeBExp : DyadicInterval precision := ⟨171864479510836960838701406091225640444183199061, 179833871019339745830008048921670442185953899889⟩
def wholeBLog : DyadicInterval precision := ⟨162487650261338679235687748103713148327999254662, 169601154369591997507405827222391081510471659257⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨171864479510836960838701406091225640993939012949, scale precision, 179833871019339745830008048921670441636198086001, scale precision,
    3, 128, 3, 128, ⟨-3128363909610052208640517905534198972145019258819, -3128363909610052208640517905534198972145017161666⟩, ⟨-3062118089465696807618299043796933979838073394468, -3062118089465696807618299043796933979838071297315⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0465StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0466StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0466StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4590335763975281399345081579386246932603875055, 4590335763975281399345081579386246932603875056⟩
def centerAExp : DyadicInterval precision := ⟨1452349740496526708002027977982130829907047701826, 1452349740496526708002027977982130832106070957379⟩
def centerALog : DyadicInterval precision := ⟨1008452612267868520487407126245153689838327381286, 1008452612267868520487407126245153692037350636839⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1452349740496526708002027977982130830456803515714, scale precision, 1452349740496526708002027977982130831556315143491, scale precision,
    0, 128, 0, 128, ⟨-9180671527950562798690163158772494418428866641, -9180671527950562798690163158772494418426769488⟩, ⟨-9180671527950562798690163158772493311988730734, -9180671527950562798690163158772493311986633581⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨654373479606638252589496685135113086385905445322, 654373479606638252589496685135113086385905445323⟩
def centerDExp : DyadicInterval precision := ⟨596893494903452163994038347155718252372053594473, 596893494903452163994038347155718254571076850026⟩
def centerDLog : DyadicInterval precision := ⟨500509053273440340443871498920685505225663393173, 500509053273440340443871498920685507424686648726⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨596893494903452163994038347155718252921809408361, scale precision, 596893494903452163994038347155718254021321036138, scale precision,
    1, 128, 1, 128, ⟨-1308746959213276505178993370270226174117896339520, -1308746959213276505178993370270226174117894242367⟩, ⟨-1308746959213276505178993370270226171425727538920, -1308746959213276505178993370270226171425725441767⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨659965952290649731310764645839874352547045921528, 659965952290649731310764645839874352547045921529⟩
def centerCExp : DyadicInterval precision := ⟨592342874309458690429554095630504123717930847735, 592342874309458690429554095630504125916954103288⟩
def centerCLog : DyadicInterval precision := ⟨497274445011408714542987629143749193324824516974, 497274445011408714542987629143749195523847772527⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨592342874309458690429554095630504124267686661623, scale precision, 592342874309458690429554095630504125367198289400, scale precision,
    1, 128, 1, 128, ⟨-1319931904581299462621529291679748706450518463675, -1319931904581299462621529291679748706450516366522⟩, ⟨-1319931904581299462621529291679748703737667319591, -1319931904581299462621529291679748703737665222438⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1579712321002756774487879929782396250845380098135, 1579712321002756774487879929782396250845380098136⟩
def centerBExp : DyadicInterval precision := ⟨168250449627402983632638823285316247324357493155, 168250449627402983632638823285316249523380748708⟩
def centerBLog : DyadicInterval precision := ⟨159250309520495494425830800798197631061730216282, 159250309520495494425830800798197633260753471835⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨168250449627402983632638823285316247874113307043, scale precision, 168250449627402983632638823285316248973624934820, scale precision,
    3, 128, 3, 128, ⟨-3159424642005513548975759859564792506466195865736, -3159424642005513548975759859564792506466193768583⟩, ⟨-3159424642005513548975759859564792496915326623965, -3159424642005513548975759859564792496915324526812⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨4432047174048269527644776165804031130864675904, 4748624479255801076876082777124010865681651339⟩
def wholeAExp : DyadicInterval precision := ⟨1452035179538035812075122148102075716455422985340, 1452664369350591901250217311774540050861815457867⟩
def wholeALog : DyadicInterval precision := ⟨1008294829281404787796718047455216463185937117999, 1008610412272733567070593870872814922068705325217⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1452035179538035812075122148102075717005178799228, scale precision, 1452664369350591901250217311774540050312059643979, scale precision,
    0, 128, 0, 128, ⟨-9497248958511602153752165554248022284704265776, -9497248958511602153752165554248022284702168623⟩, ⟨-8864094348096539055289552331608061708630152947, -8864094348096539055289552331608061708628055794⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨648844592727412176647428020776866274458569907208, 659917674403335303398947154306570012946022027568⟩
def wholeDExp : DyadicInterval precision := ⟨592382009410612930615839145836493981094734824913, 601426740197304508434017275821189107729148063965⟩
def wholeDLog : DyadicInterval precision := ⟨497302293015079090720897450218278677548754229682, 503724208829984298099852655433700222030834719032⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨592382009410612930615839145836493981644490638801, scale precision, 601426740197304508434017275821189107179392250077, scale precision,
    1, 128, 1, 128, ⟨-1319835348806670606797894308613140027248381064907, -1319835348806670606797894308613140027248378967754⟩, ⟨-1297689185454824353294856041553732547581202554253, -1297689185454824353294856041553732547581200457100⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨654229053852446988667848133809557594352805518260, 665719375461188393838370759128844286171122549363⟩
def wholeCExp : DyadicInterval precision := ⟨587697490185059010019478590980626950852315388366, 597011476725021492713305914757895054582913506909⟩
def wholeCLog : DyadicInterval precision := ⟨493965077623775741990113284158565769535470397703, 500592820321492206435592408256845580124776990318⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨587697490185059010019478590980626951402071202254, scale precision, 597011476725021492713305914757895054033157693021, scale precision,
    1, 128, 1, 128, ⟨-1331438750922376787676741518257688573709393422130, -1331438750922376787676741518257688573709391324977⟩, ⟨-1308458107704893977335696267619115187359793698927, -1308458107704893977335696267619115187359791601774⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1563044622907844287293104039396809878921268868737, 1596452730610449915622854998723802488519956714776⟩
def wholeBExp : DyadicInterval precision := ⟨164439896853410812953231380549826610612365040628, 172132175611494670117194362716041871786514757936⟩
def wholeBLog : DyadicInterval precision := ⟨155829145056363187160571603776831435777043671690, 162727159473890019091318074144283724707686035394⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨164439896853410812953231380549826611162120854516, scale precision, 172132175611494670117194362716041871236758944048, scale precision,
    3, 128, 3, 128, ⟨-3192905461220899831245709997447604981926009869241, -3192905461220899831245709997447604981926007772088⟩, ⟨-3126089245815688574586208078793619753174794250346, -3126089245815688574586208078793619753174792153193⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0466StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0467StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0467StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4590335763975281399345081579386246932603875055, 4590335763975281399345081579386246932603875056⟩
def centerAExp : DyadicInterval precision := ⟨1452349740496526708002027977982130829907047701826, 1452349740496526708002027977982130832106070957379⟩
def centerALog : DyadicInterval precision := ⟨1008452612267868520487407126245153689838327381286, 1008452612267868520487407126245153692037350636839⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1452349740496526708002027977982130830456803515714, scale precision, 1452349740496526708002027977982130831556315143491, scale precision,
    0, 128, 0, 128, ⟨-9180671527950562798690163158772494418428866641, -9180671527950562798690163158772494418426769488⟩, ⟨-9180671527950562798690163158772493311988730734, -9180671527950562798690163158772493311986633581⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨643330890011571853191447487766205018317129467057, 643330890011571853191447487766205018317129467058⟩
def centerDExp : DyadicInterval precision := ⟨605981822530277187962366989116632506149582094264, 605981822530277187962366989116632508348605349817⟩
def centerDLog : DyadicInterval precision := ⟨506947743551831449885580746844042863375923706013, 506947743551831449885580746844042865574946961566⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨605981822530277187962366989116632506699337908152, scale precision, 605981822530277187962366989116632507798849535929, scale precision,
    1, 128, 1, 128, ⟨-1286661780023143706382894975532410037960156226204, -1286661780023143706382894975532410037960154129051⟩, ⟨-1286661780023143706382894975532410035308363739178, -1286661780023143706382894975532410035308361642025⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨648892604381083239522078435711286355003183092692, 648892604381083239522078435711286355003183092693⟩
def centerCExp : DyadicInterval precision := ⟨601387226668128754654644655156009912687699296374, 601387226668128754654644655156009914886722551927⟩
def centerCLog : DyadicInterval precision := ⟨503696214818515445257483558009630809546606582737, 503696214818515445257483558009630811745629838290⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨601387226668128754654644655156009913237455110262, scale precision, 601387226668128754654644655156009914336966738039, scale precision,
    1, 128, 1, 128, ⟨-1297785208762166479044156871422572711342393319155, -1297785208762166479044156871422572711342391222002⟩, ⟨-1297785208762166479044156871422572708670341148770, -1297785208762166479044156871422572708670339051617⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1547016872199801815324804148493082701553069738627, 1547016872199801815324804148493082701553069738628⟩
def centerBExp : DyadicInterval precision := ⟨175949304101880647544103663740907984043998273183, 175949304101880647544103663740907986243021528736⟩
def centerBLog : DyadicInterval precision := ⟨166138102625626739304136271335254057600769902894, 166138102625626739304136271335254059799793158447⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨175949304101880647544103663740907984593754087071, scale precision, 175949304101880647544103663740907985693265714848, scale precision,
    3, 128, 3, 128, ⟨-3094033744399603630649608296986165407672620775536, -3094033744399603630649608296986165407672618678383⟩, ⟨-3094033744399603630649608296986165398539660276130, -3094033744399603630649608296986165398539658178977⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨4432047174048269527644776165804031130864675904, 4748624479255801076876082777124010865681651339⟩
def wholeAExp : DyadicInterval precision := ⟨1452035179538035812075122148102075716455422985340, 1452664369350591901250217311774540050861815457867⟩
def wholeALog : DyadicInterval precision := ⟨1008294829281404787796718047455216463185937117999, 1008610412272733567070593870872814922068705325217⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1452035179538035812075122148102075717005178799228, scale precision, 1452664369350591901250217311774540050312059643979, scale precision,
    0, 128, 0, 128, ⟨-9497248958511602153752165554248022284704265776, -9497248958511602153752165554248022284702168623⟩, ⟨-8864094348096539055289552331608061708630152947, -8864094348096539055289552331608061708628055794⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨637832247480472324939326434952621888088060941844, 648844592727412176647428020776866274458569907209⟩
def wholeDExp : DyadicInterval precision := ⟨601426740197304508434017275821189105530124808412, 610558820864912509175272747825498146169006720984⟩
def wholeDLog : DyadicInterval precision := ⟨503724208829984298099852655433700219831811463479, 510179642243321146984571771117295507804948082651⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨601426740197304508434017275821189106079880622300, scale precision, 610558820864912509175272747825498145619250907096, scale precision,
    1, 128, 1, 128, ⟨-1297689185454824353294856041553732550253079171733, -1297689185454824353294856041553732550253077074580⟩, ⟨-1275664494960944649878652869905243774860166148623, -1275664494960944649878652869905243774860164051470⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨643187256389327373999400012702566255441633014946, 654614212348041610451796176400532717217365395563⟩
def wholeCExp : DyadicInterval precision := ⟨596696891440356916967491903122863047707319799938, 606100943736283097014906634825296434299286482784⟩
def wholeCLog : DyadicInterval precision := ⟨500369454222818035570276471166145712437919616931, 507031947767145693047493296758041183095370781091⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨596696891440356916967491903122863048257075613826, scale precision, 606100943736283097014906634825296433749530668896, scale precision,
    1, 128, 1, 128, ⟨-1309228424696083220903592352801065435781259756397, -1309228424696083220903592352801065435781257659244⟩, ⟨-1286374512778654747998800025405132509557631422505, -1286374512778654747998800025405132509557629325352⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1530495459705123933741161012530517214526812079567, 1563613245708246331042400130007245441226398462522⟩
def wholeBExp : DyadicInterval precision := ⟨171998285637164833816452506105016460717459336335, 179972619780108543028402320872481119979333402335⟩
def wholeBLog : DyadicInterval precision := ⟨162607372264285474871551176352716969529642973862, 169724695820757069929313149600939229268003615583⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨171998285637164833816452506105016461267215150223, scale precision, 179972619780108543028402320872481119429577588447, scale precision,
    3, 128, 3, 128, ⟨-3127226491416492662084800260014490887124176058314, -3127226491416492662084800260014490887124173961161⟩, ⟨-3060990919410247867482322025061034424589229328429, -3060990919410247867482322025061034424589227231276⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0467StableWitnesses

end


