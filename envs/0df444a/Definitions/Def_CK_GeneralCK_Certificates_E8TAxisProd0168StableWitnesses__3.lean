-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0168StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0168StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:03:19.610227+00:00
-- url     : https://prove2.me/theorems/8f55a29b-5632-4950-80e6-f507bcea350a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0168StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0169StableWitnesses, GeneralCK.Certificates.E8TAxisProd01…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0168StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0169StableWitnesses, GeneralCK.Certificates.E8TAxisProd0170StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0168StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0169StableWitnesses, GeneralCK.Certificates.E8TAxisProd0170StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0168StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0169StableWitnesses, GeneralCK.Certificates.E8TAxisProd0170StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0168StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0169StableWitnesses, GeneralCK/Certificates/E8TAxisProd0170StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0168StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0168StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4748624479255801076876082777124010865681651338, 4748624479255801076876082777124010865681651339⟩
def centerAExp : DyadicInterval precision := ⟨1452035179538035812075122148102075716455422985340, 1452035179538035812075122148102075718654446240893⟩
def centerALog : DyadicInterval precision := ⟨1008294829281404787796718047455216463185937117999, 1008294829281404787796718047455216465384960373552⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1452035179538035812075122148102075717005178799228, scale precision, 1452035179538035812075122148102075718104690427005, scale precision,
    0, 128, 0, 128, ⟨-9497248958511602153752165554248022284704265776, -9497248958511602153752165554248022284702168623⟩, ⟨-9497248958511602153752165554248021178024436730, -9497248958511602153752165554248021178022339577⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨314063896595388511688731668307850747220145675387, 314063896595388511688731668307850747220145675388⟩
def centerDExp : DyadicInterval precision := ⟨950926933437474332245963667891130159890397626751, 950926933437474332245963667891130162089420882304⟩
def centerDLog : DyadicInterval precision := ⟨732460073978448216291062163497299207879791564564, 732460073978448216291062163497299210078814820117⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨950926933437474332245963667891130160440153440639, scale precision, 950926933437474332245963667891130161539665068416, scale precision,
    0, 128, 0, 128, ⟨-628127793190777023377463336615701495285224847764, -628127793190777023377463336615701495285222750611⟩, ⟨-628127793190777023377463336615701493595359950940, -628127793190777023377463336615701493595357853787⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨319067775302505002942167197477318956392189084598, 319067775302505002942167197477318956392189084599⟩
def centerCExp : DyadicInterval precision := ⟨944437623369668716532295615577670201364561462342, 944437623369668716532295615577670203563584717895⟩
def centerCLog : DyadicInterval precision := ⟨728523411874105531042506919726053314031235703942, 728523411874105531042506919726053316230258959495⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨944437623369668716532295615577670201914317276230, scale precision, 944437623369668716532295615577670203013828904007, scale precision,
    0, 128, 0, 128, ⟨-638135550605010005884334394954637913635117267856, -638135550605010005884334394954637913635115170703⟩, ⟨-638135550605010005884334394954637911933641167691, -638135550605010005884334394954637911933639070538⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨667657033903226664628577081635735345666694295097, 667657033903226664628577081635735345666694295098⟩
def centerBExp : DyadicInterval precision := ⟨586141216084479440908240245054632350482183446880, 586141216084479440908240245054632352681206702433⟩
def centerBLog : DyadicInterval precision := ⟨492854711509522614734690079199105860300082645974, 492854711509522614734690079199105862499105901527⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨586141216084479440908240245054632351031939260768, scale precision, 586141216084479440908240245054632352131450888545, scale precision,
    1, 128, 1, 128, ⟨-1335314067806453329257154163271470692704166850955, -1335314067806453329257154163271470692704164753802⟩, ⟨-1335314067806453329257154163271470689962612426588, -1335314067806453329257154163271470689962610329435⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨4432047174048269527644776165804031130864675904, 5065202303167835215808940955361609459283110735⟩
def wholeAExp : DyadicInterval precision := ⟨1451406261215048238048665418490328880814971300707, 1452664369350591901250217311774540050861815457867⟩
def wholeALog : DyadicInterval precision := ⟨1007979314346565773386485143059333172819831600857, 1008610412272733567070593870872814922068705325217⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1451406261215048238048665418490328881364727114595, scale precision, 1452664369350591901250217311774540050312059643979, scale precision,
    0, 128, 0, 128, ⟨-10130404606335670431617881910723219472146955901, -10130404606335670431617881910723219472144858748⟩, ⟨-8864094348096539055289552331608061708630152947, -8864094348096539055289552331608061708628055794⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨305741530935075953839244385929164159203164552709, 322408132378444526209018649139695484921606350583⟩
def wholeDExp : DyadicInterval precision := ⟨940130328208408204655831711119657709679621898349, 961818742565408613466907997915298000639465600973⟩
def wholeDLog : DyadicInterval precision := ⟨725904575743015811666185701912516249682142746744, 739043717569107002066769324458966200204494229375⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨940130328208408204655831711119657710229377712237, scale precision, 961818742565408613466907997915298000089709787085, scale precision,
    0, 128, 0, 128, ⟨-644816264756889052418037298279390970697849535889, -644816264756889052418037298279390970697847438736⟩, ⟨-611483061870151907678488771858328317570965873209, -611483061870151907678488771858328317570963776056⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨310399396699256950984041451612067022294184943489, 327760197752559038439133554083214572857831243690⟩
def wholeCExp : DyadicInterval precision := ⟨933269907762331493937873102670555718357930866115, 955707528249466688044958580985006769096163752102⟩
def wholeCLog : DyadicInterval precision := ⟨721723725432976317515070165492696006907252905980, 735353396338611872578012864905443975754921531117⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨933269907762331493937873102670555718907686680003, scale precision, 955707528249466688044958580985006768546407938214, scale precision,
    0, 128, 0, 128, ⟨-655520395505118076878267108166429146576581707053, -655520395505118076878267108166429146576579609900⟩, ⟨-620798793398513901968082903224134043747664968112, -620798793398513901968082903224134043747662870959⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨647980579214740243359080085226675394933456121061, 687529878621090320563368693304056095064406256155⟩
def wholeBExp : DyadicInterval precision := ⟨570415840366179700931987830009237639371719009057, 602138266124564985796045504476526792080478882833⟩
def wholeBLog : DyadicInterval precision := ⟨481587430565019411758778013281044179856011339851, 504228209368539430865336432831296616152565169367⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨570415840366179700931987830009237639921474822945, scale precision, 602138266124564985796045504476526791530723068945, scale precision,
    1, 128, 1, 128, ⟨-1375059757242180641126737386608112191537380724122, -1375059757242180641126737386608112191537378626969⟩, ⟨-1295961158429480486718160170453350788532553613972, -1295961158429480486718160170453350788532551516819⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0168StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0169StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0169StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4748624479255801076876082777124010865681651338, 4748624479255801076876082777124010865681651339⟩
def centerAExp : DyadicInterval precision := ⟨1452035179538035812075122148102075716455422985340, 1452035179538035812075122148102075718654446240893⟩
def centerALog : DyadicInterval precision := ⟨1008294829281404787796718047455216463185937117999, 1008294829281404787796718047455216465384960373552⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1452035179538035812075122148102075717005178799228, scale precision, 1452035179538035812075122148102075718104690427005, scale precision,
    0, 128, 0, 128, ⟨-9497248958511602153752165554248022284704265776, -9497248958511602153752165554248022284702168623⟩, ⟨-9497248958511602153752165554248021178024436730, -9497248958511602153752165554248021178022339577⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨297440437897247181273022509268442947544064301498, 297440437897247181273022509268442947544064301499⟩
def centerDExp : DyadicInterval precision := ⟨972806985794329725044362385369131888111738659096, 972806985794329725044362385369131890310761914649⟩
def centerDLog : DyadicInterval precision := ⟨745655734605380757184922339086747309072128874695, 745655734605380757184922339086747311271152130248⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨972806985794329725044362385369131888661494472984, scale precision, 972806985794329725044362385369131889761006100761, scale precision,
    0, 128, 0, 128, ⟨-594880875794494362546045018536885895914058159347, -594880875794494362546045018536885895914056062194⟩, ⟨-594880875794494362546045018536885894262201143797, -594880875794494362546045018536885894262199046644⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨302418574378361264530542065283107656816601291467, 302418574378361264530542065283107656816601291468⟩
def centerCExp : DyadicInterval precision := ⟨966202397900889825408189436492161263615904004057, 966202397900889825408189436492161265814927259610⟩
def centerCLog : DyadicInterval precision := ⟨741685106540152535630082306642679341672945644182, 741685106540152535630082306642679343871968899735⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨966202397900889825408189436492161264165659817945, scale precision, 966202397900889825408189436492161265265171445722, scale precision,
    0, 128, 0, 128, ⟨-604837148756722529061084130566215314464777868830, -604837148756722529061084130566215314464775771677⟩, ⟨-604837148756722529061084130566215312801629394192, -604837148756722529061084130566215312801627297039⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨629255614472596085420192037271306667028995528127, 629255614472596085420192037271306667028995528128⟩
def centerBExp : DyadicInterval precision := ⟨617767009112922215558428698190913365023078207701, 617767009112922215558428698190913367222101463254⟩
def centerBLog : DyadicInterval precision := ⟨515255023764927942687938897563520949413897856708, 515255023764927942687938897563520951612921112261⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨617767009112922215558428698190913365572834021589, scale precision, 617767009112922215558428698190913366672345649366, scale precision,
    1, 128, 1, 128, ⟨-1258511228945192170840384074542613335358594128375, -1258511228945192170840384074542613335358592031222⟩, ⟨-1258511228945192170840384074542613332757390081289, -1258511228945192170840384074542613332757387984136⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨4432047174048269527644776165804031130864675904, 5065202303167835215808940955361609459283110735⟩
def wholeAExp : DyadicInterval precision := ⟨1451406261215048238048665418490328880814971300707, 1452664369350591901250217311774540050861815457867⟩
def wholeALog : DyadicInterval precision := ⟨1007979314346565773386485143059333172819831600857, 1008610412272733567070593870872814922068705325217⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1451406261215048238048665418490328881364727114595, scale precision, 1452664369350591901250217311774540050312059643979, scale precision,
    0, 128, 0, 128, ⟨-10130404606335670431617881910723219472146955901, -10130404606335670431617881910723219472144858748⟩, ⟨-8864094348096539055289552331608061708630152947, -8864094348096539055289552331608061708628055794⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨289160022559818845156424937767397025574157886773, 305741530935075953839244385929164159203164552710⟩
def wholeDExp : DyadicInterval precision := ⟨961818742565408613466907997915297998440442345420, 983892922446469118853387927975743981788878518423⟩
def wholeDLog : DyadicInterval precision := ⟨739043717569107002066769324458966198005470973822, 752296360822110031467471195763059032944457639560⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨961818742565408613466907997915297998990198159308, scale precision, 983892922446469118853387927975743981239122704535, scale precision,
    0, 128, 0, 128, ⟨-611483061870151907678488771858328319241694434782, -611483061870151907678488771858328319241692337629⟩, ⟨-578320045119637690312849875534794050331694399297, -578320045119637690312849875534794050331692302144⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨293794542745046640067294646993992613811650700680, 311065356778871966878476064924676045947074876451⟩
def wholeCExp : DyadicInterval precision := ⟨954836953605768478136583660933222259959491038325, 977672686556378899154880479700583295723941235784⟩
def wholeCLog : DyadicInterval precision := ⟨734826931578135891858752030942795396823343722323, 748574071273698567109675504566805886553367665726⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨954836953605768478136583660933222260509246852213, scale precision, 977672686556378899154880479700583295174185421896, scale precision,
    0, 128, 0, 128, ⟨-622130713557743933756952129849352092735623284393, -622130713557743933756952129849352092735621187240⟩, ⟨-587589085490093280134589293987985226801484439496, -587589085490093280134589293987985226801482342343⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨609948203639037705369913311370273420421707818260, 648748572864415542117577149154744914777379027746⟩
def wholeBExp : DyadicInterval precision := ⟨601505772209256427663378332296369223387593795359, 634306776250422930396265232704260359146160872976⟩
def wholeBLog : DyadicInterval precision := ⟨503780198753649825212650489384180270857996995440, 526834701390773474742213048548690858214134543494⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨601505772209256427663378332296369223937349609247, scale precision, 634306776250422930396265232704260358596405059088, scale precision,
    1, 128, 1, 128, ⟨-1297497145728831084235154298309489830890521883498, -1297497145728831084235154298309489830890519786345⟩, ⟨-1219896407278075410739826622740546839576728306204, -1219896407278075410739826622740546839576726209051⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0169StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0170StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0170StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4115470352964345628383522602588716836376905846, 4115470352964345628383522602588716836376905847⟩
def centerAExp : DyadicInterval precision := ⟨1453293830838237185210198542808669482340765754580, 1453293830838237185210198542808669484539789010133⟩
def centerALog : DyadicInterval precision := ⟨1008926063354791867585944205900164500105846572497, 1008926063354791867585944205900164502304869828050⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1453293830838237185210198542808669482890521568468, scale precision, 1453293830838237185210198542808669483990033196245, scale precision,
    0, 128, 0, 128, ⟨-8230940705928691256767045205177434225615544793, -8230940705928691256767045205177434225613447640⟩, ⟨-8230940705928691256767045205177433119894175747, -8230940705928691256767045205177433119892078594⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨314063896595388511688731668307850747220145675387, 314063896595388511688731668307850747220145675388⟩
def centerDExp : DyadicInterval precision := ⟨950926933437474332245963667891130159890397626751, 950926933437474332245963667891130162089420882304⟩
def centerDLog : DyadicInterval precision := ⟨732460073978448216291062163497299207879791564564, 732460073978448216291062163497299210078814820117⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨950926933437474332245963667891130160440153440639, scale precision, 950926933437474332245963667891130161539665068416, scale precision,
    0, 128, 0, 128, ⟨-628127793190777023377463336615701495285224847764, -628127793190777023377463336615701495285222750611⟩, ⟨-628127793190777023377463336615701493595359950940, -628127793190777023377463336615701493595357853787⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨318400131926743274789312092208504137548932536123, 318400131926743274789312092208504137548932536124⟩
def centerCExp : DyadicInterval precision := ⟨945300893914836998357902081669710585621452481639, 945300893914836998357902081669710587820475737192⟩
def centerCLog : DyadicInterval precision := ⟨729047716473560833944230808607896295606555554959, 729047716473560833944230808607896297805578810512⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨945300893914836998357902081669710586171208295527, scale precision, 945300893914836998357902081669710587270719923304, scale precision,
    0, 128, 0, 128, ⟨-636800263853486549578624184417008275947827257329, -636800263853486549578624184417008275947825160176⟩, ⟨-636800263853486549578624184417008274247904984320, -636800263853486549578624184417008274247902887167⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨666881744294968058583905837260024005407900219115, 666881744294968058583905837260024005407900219116⟩
def centerBExp : DyadicInterval precision := ⟨586763412229379887261482556585796288512624099669, 586763412229379887261482556585796290711647355222⟩
def centerBLog : DyadicInterval precision := ⟨493298735502760789086524174179148128077586958226, 493298735502760789086524174179148130276610213779⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨586763412229379887261482556585796289062379913557, scale precision, 586763412229379887261482556585796290161891541334, scale precision,
    1, 128, 1, 128, ⟨-1333763488589936117167811674520048012185125145005, -1333763488589936117167811674520048012185123047852⟩, ⟨-1333763488589936117167811674520048009446477828611, -1333763488589936117167811674520048009446475731458⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 4432047174048269527644776165804031130864675905⟩
def wholeAExp : DyadicInterval precision := ⟨1452664369350591901250217311774540048662792202314, 1453923564186661310665317018859587709527417053272⟩
def wholeALog : DyadicInterval precision := ⟨1008610412272733567070593870872814919869682069664, 1009241782561842849966002591658486094460586802138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1452664369350591901250217311774540049212548016202, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-8864094348096539055289552331608062814830647821, -8864094348096539055289552331608062814828550668⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨305741530935075953839244385929164159203164552709, 322408132378444526209018649139695484921606350583⟩
def wholeDExp : DyadicInterval precision := ⟨940130328208408204655831711119657709679621898349, 961818742565408613466907997915298000639465600973⟩
def wholeDLog : DyadicInterval precision := ⟨725904575743015811666185701912516249682142746744, 739043717569107002066769324458966200204494229375⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨940130328208408204655831711119657710229377712237, scale precision, 961818742565408613466907997915298000089709787085, scale precision,
    0, 128, 0, 128, ⟨-644816264756889052418037298279390970697849535889, -644816264756889052418037298279390970697847438736⟩, ⟨-611483061870151907678488771858328317570965873209, -611483061870151907678488771858328317570963776056⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨309733574902450231722473605348773919922730774135, 327090680858758583373932802371003276516688738836⟩
def wholeCExp : DyadicInterval precision := ⟨934125365302252464635631009739543171538932793379, 956578715624353311846366700153450027496848179143⟩
def wholeCLog : DyadicInterval precision := ⟨722245708143222885807268476168971919129511248401, 735880041861580198236598054257202697746267990456⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨934125365302252464635631009739543172088688607267, scale precision, 956578715624353311846366700153450026947092365255, scale precision,
    0, 128, 0, 128, ⟨-654181361717517166747865604742006553893508281819, -654181361717517166747865604742006553893506184666⟩, ⟨-619467149804900463444947210697547839005522287695, -619467149804900463444947210697547839005520190542⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨647212879114126499197397516204537987317879341455, 686746784135662041361783775179230530642546345198⟩
def wholeBExp : DyadicInterval precision := ⟨571027442729152088477736821499906453948904178830, 602771182979807624150637266322980185386907568295⟩
def wholeBLog : DyadicInterval precision := ⟨482027272914487729614436700641673713627561505347, 504676382132539218648431185351501379566213600007⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨571027442729152088477736821499906454498659992718, scale precision, 602771182979807624150637266322980184837151754407, scale precision,
    1, 128, 1, 128, ⟨-1373493568271324082723567550358461062692152247912, -1373493568271324082723567550358461062692150150759⟩, ⟨-1294425758228252998394795032409075973302801148168, -1294425758228252998394795032409075973302799051015⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0170StableWitnesses

end


