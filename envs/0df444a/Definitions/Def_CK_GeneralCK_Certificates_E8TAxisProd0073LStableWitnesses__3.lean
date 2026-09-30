-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0073LStableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0073LStableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:55:11.924328+00:00
-- url     : https://prove2.me/theorems/caac0408-bfe2-45c4-8efe-bb3aaa02c5ee
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0073LStableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0074LStableWitnesses, GeneralCK.Certificates.E8TAxisProd…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0073LStableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0074LStableWitnesses, GeneralCK.Certificates.E8TAxisProd0079LStableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0073LStableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0074LStableWitnesses, GeneralCK.Certificates.E8TAxisProd0079LStableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0073LStableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0074LStableWitnesses, GeneralCK.Certificates.E8TAxisProd0079LStableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0073LStableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0074LStableWitnesses, GeneralCK/Certificates/E8TAxisProd0079LStableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0073LStableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0073LStableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨146987038246024121844160689604839910465058611105, 146987038246024121844160689604839910465058611106⟩
def centerDExp : DyadicInterval precision := ⟨1195206770736568477483493079521979997730413799104, 1195206770736568477483493079521979999929437054657⟩
def centerDLog : DyadicInterval precision := ⟨873427709257314482190114267347085618455089893048, 873427709257314482190114267347085620654113148601⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1195206770736568477483493079521979998280169612992, scale precision, 1195206770736568477483493079521979999379681240769, scale precision,
    0, 128, 0, 128, ⟨-293974076492048243688321379209679821602360967033, -293974076492048243688321379209679821602358869880⟩, ⟨-293974076492048243688321379209679820257875574543, -293974076492048243688321379209679820257873477390⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨151793204428990519680479714806454905835579669975, 151793204428990519680479714806454905835579669976⟩
def centerCExp : DyadicInterval precision := ⟨1187371660386271689613059689204247777739503787638, 1187371660386271689613059689204247779938527043191⟩
def centerCLog : DyadicInterval precision := ⟨869111110035990056794995987856395923011127238339, 869111110035990056794995987856395925210150493892⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1187371660386271689613059689204247778289259601526, scale precision, 1187371660386271689613059689204247779388771229303, scale precision,
    0, 128, 0, 128, ⟨-303586408857981039360959429612909812347839013204, -303586408857981039360959429612909812347836916051⟩, ⟨-303586408857981039360959429612909810994481763851, -303586408857981039360959429612909810994479666698⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨302418574378361264530542065283107656816601291467, 302418574378361264530542065283107656816601291468⟩
def centerBExp : DyadicInterval precision := ⟨966202397900889825408189436492161263615904004057, 966202397900889825408189436492161265814927259610⟩
def centerBLog : DyadicInterval precision := ⟨741685106540152535630082306642679341672945644182, 741685106540152535630082306642679343871968899735⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨966202397900889825408189436492161264165659817945, scale precision, 966202397900889825408189436492161265265171445722, scale precision,
    0, 128, 0, 128, ⟨-604837148756722529061084130566215314464777868830, -604837148756722529061084130566215314464775771677⟩, ⟨-604837148756722529061084130566215312801629394192, -604837148756722529061084130566215312801627297039⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨142984678294030808430193174439689638732873799524, 150991919513477176104051187712444417195036210429⟩
def wholeDExp : DyadicInterval precision := ⟨1188674354540648287330851150581954941407642534204, 1201770939647839765988959733979548166667559706770⟩
def wholeDLog : DyadicInterval precision := ⟨869829687869058094079061307765923601161168618874, 877034319321159546816789449956018118197948476500⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1188674354540648287330851150581954941957398348092, scale precision, 1201770939647839765988959733979548166117803892882, scale precision,
    0, 128, 0, 128, ⟨-301983839026954352208102375424888835066010507244, -301983839026954352208102375424888835066008410091⟩, ⟨-285969356588061616860386348879379276797177794708, -285969356588061616860386348879379276797175697555⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨147467489505837704641503792021720686236046886404, 156121957346193227048614553218993580561696370782⟩
def wholeCExp : DyadicInterval precision := ⟨1180358811440768658950622231710701791494263630449, 1194421209022043368884451180509721980390860244292⟩
def wholeCLog : DyadicInterval precision := ⟨865236677222023209284269496790597802576901961489, 872995494151319611040382737657176578920259390319⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1180358811440768658950622231710701792044019444337, scale precision, 1194421209022043368884451180509721979841104430404, scale precision,
    0, 128, 0, 128, ⟨-312243914692386454097229106437987161804092755862, -312243914692386454097229106437987161804090658709⟩, ⟨-294934979011675409283007584043441371799409996249, -294934979011675409283007584043441371799407899096⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨293794542745046640067294646993992613811650700680, 311065356778871966878476064924676045947074876451⟩
def wholeBExp : DyadicInterval precision := ⟨954836953605768478136583660933222259959491038325, 977672686556378899154880479700583295723941235784⟩
def wholeBLog : DyadicInterval precision := ⟨734826931578135891858752030942795396823343722323, 748574071273698567109675504566805886553367665726⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨954836953605768478136583660933222260509246852213, scale precision, 977672686556378899154880479700583295174185421896, scale precision,
    0, 128, 0, 128, ⟨-622130713557743933756952129849352092735623284393, -622130713557743933756952129849352092735621187240⟩, ⟨-587589085490093280134589293987985226801484439496, -587589085490093280134589293987985226801482342343⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0073LStableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0074LStableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0074LStableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨146987038246024121844160689604839910465058611105, 146987038246024121844160689604839910465058611106⟩
def centerDExp : DyadicInterval precision := ⟨1195206770736568477483493079521979997730413799104, 1195206770736568477483493079521979999929437054657⟩
def centerDLog : DyadicInterval precision := ⟨873427709257314482190114267347085618455089893048, 873427709257314482190114267347085620654113148601⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1195206770736568477483493079521979998280169612992, scale precision, 1195206770736568477483493079521979999379681240769, scale precision,
    0, 128, 0, 128, ⟨-293974076492048243688321379209679821602360967033, -293974076492048243688321379209679821602358869880⟩, ⟨-293974076492048243688321379209679820257875574543, -293974076492048243688321379209679820257873477390⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨151152168188588714247505756782027955273628105135, 151152168188588714247505756782027955273628105136⟩
def centerCExp : DyadicInterval precision := ⟨1188413714933753390339161340964427309810948877257, 1188413714933753390339161340964427312009972132810⟩
def centerCLog : DyadicInterval precision := ⟨869685944983208143333250737008605383438384831253, 869685944983208143333250737008605385637408086806⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1188413714933753390339161340964427310360704691145, scale precision, 1188413714933753390339161340964427311460216318922, scale precision,
    0, 128, 0, 128, ⟨-302304336377177428495011513564055911223342541298, -302304336377177428495011513564055911223340444145⟩, ⟨-302304336377177428495011513564055909871171976395, -302304336377177428495011513564055909871169879242⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨301754388141818385817694246745563158170096807648, 301754388141818385817694246745563158170096807649⟩
def centerBExp : DyadicInterval precision := ⟨967080987493072674010041745298622021186391084773, 967080987493072674010041745298622023385414340326⟩
def centerBLog : DyadicInterval precision := ⟨742213930405550974699829492928828113005135247299, 742213930405550974699829492928828115204158502852⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨967080987493072674010041745298622021736146898661, scale precision, 967080987493072674010041745298622022835658526438, scale precision,
    0, 128, 0, 128, ⟨-603508776283636771635388493491126317171013418994, -603508776283636771635388493491126317171011321841⟩, ⟨-603508776283636771635388493491126315509375908752, -603508776283636771635388493491126315509373811599⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨142984678294030808430193174439689638732873799524, 150991919513477176104051187712444417195036210429⟩
def wholeDExp : DyadicInterval precision := ⟨1188674354540648287330851150581954941407642534204, 1201770939647839765988959733979548166667559706770⟩
def wholeDLog : DyadicInterval precision := ⟨869829687869058094079061307765923601161168618874, 877034319321159546816789449956018118197948476500⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1188674354540648287330851150581954941957398348092, scale precision, 1201770939647839765988959733979548166117803892882, scale precision,
    0, 128, 0, 128, ⟨-301983839026954352208102375424888835066010507244, -301983839026954352208102375424888835066008410091⟩, ⟨-285969356588061616860386348879379276797177794708, -285969356588061616860386348879379276797175697555⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨146826895900187411258321839193929239531070706025, 155480465510961978161806974473057541859913965830⟩
def wholeCExp : DyadicInterval precision := ⟨1181395447964627495733780322911049524889188799936, 1195468726228719232833614102862965394992580531747⟩
def wholeCLog : DyadicInterval precision := ⟨865810041652312317067648650979185486527488236654, 873571808438861005643647858596413661476389570519⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1181395447964627495733780322911049525438944613824, scale precision, 1195468726228719232833614102862965394442824717859, scale precision,
    0, 128, 0, 128, ⟨-310960931021923956323613948946115084399930654501, -310960931021923956323613948946115084399928557348⟩, ⟨-293653791800374822516643678387858478390047068667, -293653791800374822516643678387858478390044971514⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨293132078860916054207893698498414517389571821029, 310399396699256950984041451612067022294184943490⟩
def wholeBExp : DyadicInterval precision := ⟨955707528249466688044958580985006766897140496549, 978559399909553102312605645338368437955031930639⟩
def wholeBLog : DyadicInterval precision := ⟨735353396338611872578012864905443973555898275564, 749105274602030926303810202237700050377074436901⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨955707528249466688044958580985006767446896310437, scale precision, 978559399909553102312605645338368437405276116751, scale precision,
    0, 128, 0, 128, ⟨-620798793398513901968082903224134045429076903000, -620798793398513901968082903224134045429074805847⟩, ⟨-586264157721832108415787396996829033958071363656, -586264157721832108415787396996829033958069266503⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0074LStableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0079LStableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0079LStableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3482318024844347500022322904444928295572395252, 3482318024844347500022322904444928295572395253⟩
def centerAExp : DyadicInterval precision := ⟨1454553569581723058392238696431353224119669669100, 1454553569581723058392238696431353226318692924653⟩
def centerALog : DyadicInterval precision := ⟨1009557569928173087760872372803888449827653659813, 1009557569928173087760872372803888452026676915366⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1454553569581723058392238696431353224669425482988, scale precision, 1454553569581723058392238696431353225768937110765, scale precision,
    0, 128, 0, 128, ⟨-6964636049688695000044645808889857143527710010, -6964636049688695000044645808889857143525612857⟩, ⟨-6964636049688695000044645808889856038763968154, -6964636049688695000044645808889856038761871001⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨146987038246024121844160689604839910465058611105, 146987038246024121844160689604839910465058611106⟩
def centerDExp : DyadicInterval precision := ⟨1195206770736568477483493079521979997730413799104, 1195206770736568477483493079521979999929437054657⟩
def centerDLog : DyadicInterval precision := ⟨873427709257314482190114267347085618455089893048, 873427709257314482190114267347085620654113148601⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1195206770736568477483493079521979998280169612992, scale precision, 1195206770736568477483493079521979999379681240769, scale precision,
    0, 128, 0, 128, ⟨-293974076492048243688321379209679821602360967033, -293974076492048243688321379209679821602358869880⟩, ⟨-293974076492048243688321379209679820257875574543, -293974076492048243688321379209679820257873477390⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨150511198341013630851419609066001297730265276594, 150511198341013630851419609066001297730265276595⟩
def centerCExp : DyadicInterval precision := ⟨1189456575934549264937210812741714606440031623038, 1189456575934549264937210812741714608639054878591⟩
def centerCLog : DyadicInterval precision := ⟨870260998532776390051009757785720139128374067740, 870260998532776390051009757785720141327397323293⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1189456575934549264937210812741714606989787436926, scale precision, 1189456575934549264937210812741714608089299064703, scale precision,
    0, 128, 0, 128, ⟨-301022396682027261702839218132002596136024123635, -301022396682027261702839218132002596136022026482⟩, ⟨-301022396682027261702839218132002594785039079899, -301022396682027261702839218132002594785036982746⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨301090336219049733479024143974588845684788984672, 301090336219049733479024143974588845684788984673⟩
def centerBExp : DyadicInterval precision := ⟨967960198093100774725826814412892945283814203732, 967960198093100774725826814412892947482837459285⟩
def centerBLog : DyadicInterval precision := ⟨742742936575026580338283659927493989573932517243, 742742936575026580338283659927493991772955772796⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨967960198093100774725826814412892945833570017620, scale precision, 967960198093100774725826814412892946933081645397, scale precision,
    0, 128, 0, 128, ⟨-602180672438099466958048287949177692199643129766, -602180672438099466958048287949177692199641032613⟩, ⟨-602180672438099466958048287949177690539514906079, -602180672438099466958048287949177690539512808926⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978073808, 3798893981423257492988718450954299577395465181⟩
def wholeAExp : DyadicInterval precision := ⟨1453923564186661310665317018859587707328393797719, 1455183847209450510423929547351191477780877052172⟩
def wholeALog : DyadicInterval precision := ⟨1009241782561842849966002591658486092261563546585, 1009873425488092576137085252579843092274389747387⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453923564186661310665317018859587707878149611607, scale precision, 1455183847209450510423929547351191477231121238284, scale precision,
    0, 128, 0, 128, ⟨-7597787962846514985977436901908599707413204648, -7597787962846514985977436901908599707411107495⟩, ⟨-6331484897294127007240142282170268789814576090, -6331484897294127007240142282170268789812478937⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨142984678294030808430193174439689638732873799524, 150991919513477176104051187712444417195036210429⟩
def wholeDExp : DyadicInterval precision := ⟨1188674354540648287330851150581954941407642534204, 1201770939647839765988959733979548166667559706770⟩
def wholeDLog : DyadicInterval precision := ⟨869829687869058094079061307765923601161168618874, 877034319321159546816789449956018118197948476500⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1188674354540648287330851150581954941957398348092, scale precision, 1201770939647839765988959733979548166117803892882, scale precision,
    0, 128, 0, 128, ⟨-301983839026954352208102375424888835066010507244, -301983839026954352208102375424888835066008410091⟩, ⟨-285969356588061616860386348879379276797177794708, -285969356588061616860386348879379276797175697555⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨146186366769016461692580822654652725928794126921, 154839041989814261300191813798023029202199323051⟩
def wholeCExp : DyadicInterval precision := ⟨1182432884363077636122480154710369181060591516506, 1196517056547333167756892797013132405219715785827⟩
def wholeCLog : DyadicInterval precision := ⟨866383623384107335437155153607563627951624042581, 874148342644455436859287811626984685974685540606⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1182432884363077636122480154710369181610347330394, scale precision, 1196517056547333167756892797013132404669959971939, scale precision,
    0, 128, 0, 128, ⟨-309678083979628522600383627596046059083904665113, -309678083979628522600383627596046059083902567960⟩, ⟨-292372733538032923385161645309305451186082767903, -292372733538032923385161645309305451186080670750⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨292469745339287832750898622949857188568070755119, 309733574902450231722473605348773919922730774136⟩
def wholeBExp : DyadicInterval precision := ⟨956578715624353311846366700153450025297824923590, 979446742750594530073246032069957402733356641105⟩
def wholeBLog : DyadicInterval precision := ⟨735880041861580198236598054257202695547244734903, 749636661828918999346616613489288630844364976411⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨956578715624353311846366700153450025847580737478, scale precision, 979446742750594530073246032069957402183600827217, scale precision,
    0, 128, 0, 128, ⟨-619467149804900463444947210697547840685402906000, -619467149804900463444947210697547840685400808847⟩, ⟨-584939490678575665501797245899714376315813094168, -584939490678575665501797245899714376315810997015⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0079LStableWitnesses

end


