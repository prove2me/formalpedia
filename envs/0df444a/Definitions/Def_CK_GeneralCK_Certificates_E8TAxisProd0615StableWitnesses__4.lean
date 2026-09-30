-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0615StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0615StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:26:47.365185+00:00
-- url     : https://prove2.me/theorems/8cf30ca5-c744-4656-8108-83bcdfab82fe
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0615StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0616StableWitnesses, GeneralCK.Certificates.E8TAxisProd06…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0615StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0616StableWitnesses, GeneralCK.Certificates.E8TAxisProd0617StableWitnesses, GeneralCK.Certificates.E8TAxisProd0618StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0615StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0616StableWitnesses, GeneralCK.Certificates.E8TAxisProd0617StableWitnesses, GeneralCK.Certificates.E8TAxisProd0618StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0615StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0616StableWitnesses, GeneralCK.Certificates.E8TAxisProd0617StableWitnesses, GeneralCK.Certificates.E8TAxisProd0618StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0615StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0616StableWitnesses, GeneralCK/Certificates/E8TAxisProd0617StableWitnesses, GeneralCK/Certificates/E8TAxisProd0618StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0615StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0615StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨791434261379870553054051158387221052157038226, 791434261379870553054051158387221052157038227⟩
def centerAExp : DyadicInterval precision := ⟨1459919625655795613670423245226319210257330755284, 1459919625655795613670423245226319212456354010837⟩
def centerALog : DyadicInterval precision := ⟨1012244519327522357560934184367326742088532965455, 1012244519327522357560934184367326744287556221008⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1459919625655795613670423245226319210807086569172, scale precision, 1459919625655795613670423245226319211906598196949, scale precision,
    0, 128, 0, 128, ⟨-1582868522759741106108102316774442654666670423, -1582868522759741106108102316774442654664573270⟩, ⟨-1582868522759741106108102316774441553963579636, -1582868522759741106108102316774441553961482483⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨665477300625433477361232002502002625345921467119, 665477300625433477361232002502002625345921467120⟩
def centerDExp : DyadicInterval precision := ⟨587892208188294475401269251844616962692532348577, 587892208188294475401269251844616964891555604130⟩
def centerDLog : DyadicInterval precision := ⟨494103945124224218680176638976803110922563855190, 494103945124224218680176638976803113121587110743⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨587892208188294475401269251844616963242288162465, scale precision, 587892208188294475401269251844616964341799790242, scale precision,
    1, 128, 1, 128, ⟨-1330954601250866954722464005004005252058538439621, -1330954601250866954722464005004005252058536342468⟩, ⟨-1330954601250866954722464005004005249325149526009, -1330954601250866954722464005004005249325147428856⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨666445776493314386337445349861623137231736382128, 666445776493314386337445349861623137231736382129⟩
def centerCExp : DyadicInterval precision := ⟨587113581222691424063770193338998468583031687942, 587113581222691424063770193338998470782054943495⟩
def centerCLog : DyadicInterval precision := ⟨493548570755353700863779027977562245620300144755, 493548570755353700863779027977562247819323400308⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨587113581222691424063770193338998469132787501830, scale precision, 587113581222691424063770193338998470232299129607, scale precision,
    1, 128, 1, 128, ⟨-1332891552986628772674890699723246275831980772692, -1332891552986628772674890699723246275831978675539⟩, ⟨-1332891552986628772674890699723246273094966852976, -1332891552986628772674890699723246273094964755823⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1605783942493403854348775546974689081446001115822, 1605783942493403854348775546974689081446001115823⟩
def centerBExp : DyadicInterval precision := ⟨162353456095440654288146216501901354608380267898, 162353456095440654288146216501901356807403523451⟩
def centerBLog : DyadicInterval precision := ⟨153952512545251082213801714309363252771880003434, 153952512545251082213801714309363254970903258987⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨162353456095440654288146216501901355158136081786, scale precision, 162353456095440654288146216501901356257647709563, scale precision,
    3, 128, 3, 128, ⟨-3211567884986807708697551093949378167840890981495, -3211567884986807708697551093949378167840888884342⟩, ⟨-3211567884986807708697551093949378157943115578945, -3211567884986807708697551093949378157943113481792⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨633147383168915695688804483341311756669124066, 949721161203312387564849132921065893757597831⟩
def wholeAExp : DyadicInterval precision := ⟨1459603428780171974367103696970164794154811336420, 1460235890986607494244084883518378978984154367596⟩
def wholeALog : DyadicInterval precision := ⟨1012086326714990166522051059359330288660433386585, 1012402729061596953461092784027353939761000525628⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1459603428780171974367103696970164794704567150308, scale precision, 1460235890986607494244084883518378978434398553708, scale precision,
    0, 128, 0, 128, ⟨-1899442322406624775129698265842132337987013411, -1899442322406624775129698265842132337984916258⟩, ⟨-1266294766337831391377608966682622963106949258, -1266294766337831391377608966682622963104852105⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨659917674403335303398947154306570012946022027567, 671052481512572809340093335645151882932874114538⟩
def wholeDExp : DyadicInterval precision := ⟨583424017396714902499808941799093863591730436308, 592382009410612930615839145836493983293758080466⟩
def wholeDLog : DyadicInterval precision := ⟨490914027605645316992013980560028280616805628608, 497302293015079090720897450218278679747777485235⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨583424017396714902499808941799093864141486250196, scale precision, 592382009410612930615839145836493982744002266578, scale precision,
    1, 128, 1, 128, ⟨-1342104963025145618680186671290303767242910652864, -1342104963025145618680186671290303767242908555711⟩, ⟨-1319835348806670606797894308613140024535709142512, -1319835348806670606797894308613140024535707045359⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨660690260676224183795332600748161552670416546141, 672217970774525288215831189543872211298063768046⟩
def wholeCExp : DyadicInterval precision := ⟨582494244284225118961304614507201350433366919722, 591756044514588397283910671184992170718308597362⟩
def wholeCLog : DyadicInterval precision := ⟨490249370708909790765975365625319691481054030442, 496856801295002452776809895620651483036174757534⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨582494244284225118961304614507201350983122733610, scale precision, 591756044514588397283910671184992170168552783474, scale precision,
    1, 128, 1, 128, ⟨-1344435941549050576431662379087744423975488174937, -1344435941549050576431662379087744423975486077784⟩, ⟨-1321380521352448367590665201496323103983063435214, -1321380521352448367590665201496323103983061338061⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1589003646964395474952013628326868085637101326745, 1622635100284105953974446604147280203381626931229⟩
def wholeBExp : DyadicInterval precision := ⟨158652412788345856816171354517550971669187848507, 166124727132751026065802885358414607296273038532⟩
def wholeBLog : DyadicInterval precision := ⟨150617698763501161521385842369339943206305972712, 157342795613960037025681137243319039720429168029⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨158652412788345856816171354517550972218943662395, scale precision, 166124727132751026065802885358414606746517224644, scale precision,
    3, 128, 3, 128, ⟨-3245270200568211907948893208294560411827590259037, -3245270200568211907948893208294560411827588161884⟩, ⟨-3178007293928790949904027256653736166437662893254, -3178007293928790949904027256653736166437660796101⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0615StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0616StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0616StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨474860522247948771940036538063380708083792495, 474860522247948771940036538063380708083792496⟩
def centerAExp : DyadicInterval precision := ⟨1460552224796057874071550301380937639903048136016, 1460552224796057874071550301380937642102071391569⟩
def centerALog : DyadicInterval precision := ⟨1012560955921529836431094652635425273892829583853, 1012560955921529836431094652635425276091852839406⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1460552224796057874071550301380937640452803949904, scale precision, 1460552224796057874071550301380937641552315577681, scale precision,
    0, 128, 0, 128, ⟨-949721044495897543880073076126761966281808906, -949721044495897543880073076126761966279711753⟩, ⟨-949721044495897543880073076126760866055458229, -949721044495897543880073076126760866053361076⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨699165997627898866254694872768746753397359927635, 699165997627898866254694872768746753397359927636⟩
def centerDExp : DyadicInterval precision := ⟨561404751706234480105216227684808901745528779369, 561404751706234480105216227684808903944552034922⟩
def centerDLog : DyadicInterval precision := ⟨475091591069212524269724099885343165971571379074, 475091591069212524269724099885343168170594634627⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨561404751706234480105216227684808902295284593257, scale precision, 561404751706234480105216227684808903394796221034, scale precision,
    1, 128, 1, 128, ⟨-1398331995255797732509389745537493508225896930926, -1398331995255797732509389745537493508225894833773⟩, ⟨-1398331995255797732509389745537493505363544876768, -1398331995255797732509389745537493505363542779615⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨699756999215241399956480375366813049264509736540, 699756999215241399956480375366813049264509736541⟩
def centerCExp : DyadicInterval precision := ⟨560950893896557431694174874036330607228706168308, 560950893896557431694174874036330609427729423861⟩
def centerCLog : DyadicInterval precision := ⟨474763652832919709558875341353191238295813664521, 474763652832919709558875341353191240494836920074⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨560950893896557431694174874036330607778461982196, scale precision, 560950893896557431694174874036330608877973609973, scale precision,
    1, 128, 1, 128, ⟨-1399513998430482799912960750733626099961354493977, -1399513998430482799912960750733626099961352396824⟩, ⟨-1399513998430482799912960750733626097096686549341, -1399513998430482799912960750733626097096684452188⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1705556462727371314097646533383415684499544911638, 1705556462727371314097646533383415684499544911639⟩
def centerBExp : DyadicInterval precision := ⟨141633329167482383651203293734464770261650938568, 141633329167482383651203293734464772460674194121⟩
def centerBLog : DyadicInterval precision := ⟨135183991391749447569046009143598652242593175085, 135183991391749447569046009143598654441616430638⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨141633329167482383651203293734464770811406752456, scale precision, 141633329167482383651203293734464771910918380233, scale precision,
    3, 128, 3, 128, ⟨-3411112925454742628195293066766831374671971872762, -3411112925454742628195293066766831374671969775609⟩, ⟨-3411112925454742628195293066766831363326209870936, -3411112925454742628195293066766831363326207773783⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨316573674294471837011765157253655004433778636, 633147383168915695688804483341311756669124067⟩
def wholeAExp : DyadicInterval precision := ⟨1460235890986607494244084883518378976785131112043, 1460868627107607697638964738615285410683914502614⟩
def wholeALog : DyadicInterval precision := ⟨1012402729061596953461092784027353937561977270075, 1012719199911638357989124323230052395461166191557⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1460235890986607494244084883518378977334886925931, scale precision, 1460868627107607697638964738615285410134158688726, scale precision,
    0, 128, 0, 128, ⟨-1266294766337831391377608966682624063571644160, -1266294766337831391377608966682624063569547007⟩, ⟨-633147348588943674023530314507309458874576803, -633147348588943674023530314507309458872479650⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨693511205829020257423882496604739492695821414414, 704837076587479092158941059188951191105662022839⟩
def wholeDExp : DyadicInterval precision := ⟨557064765387537285209117120927584102725232557331, 565765939962058116901418666290376204947661904598⟩
def wholeDLog : DyadicInterval precision := ⟨471952686082951260798866870121334518051885287659, 478239054014281969770673762969782323901449402529⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨557064765387537285209117120927584103274988371219, scale precision, 565765939962058116901418666290376204397906090710, scale precision,
    1, 128, 1, 128, ⟨-1409674153174958184317882118377902383653651143312, -1409674153174958184317882118377902383653649046159⟩, ⟨-1387022411658040514847764993209478983971500023954, -1387022411658040514847764993209478983971497926801⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨693904058069515033255127039781986599918628876746, 705627393751618059150757717755430214801700087812⟩
def wholeCExp : DyadicInterval precision := ⟨556462617777575322832484395908592605947898281082, 565461865470576534734447866887954416311809893031⟩
def wholeCLog : DyadicInterval precision := ⟨471516648406539346781320580255734413453366902263, 478019823605741052943043982346050642347649132311⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨556462617777575322832484395908592606497654094970, scale precision, 565461865470576534734447866887954415762054079143, scale precision,
    1, 128, 1, 128, ⟨-1411254787503236118301515435510860431047288012749, -1411254787503236118301515435510860431047285915596⟩, ⟨-1387808116139030066510254079563973198416351272856, -1387808116139030066510254079563973198416349175703⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1688378377367966863591789527183587307558995694116, 1722798026884796605435096683569979212267277830611⟩
def wholeBExp : DyadicInterval precision := ⟨138330702760915949654728162557281371483105085978, 145002208736712170093120437717821030738026092635⟩
def wholeBLog : DyadicInterval precision := ⟨132170038922506050147871637075504653905643715389, 138252015616296873326282854296881004964627914630⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨138330702760915949654728162557281372032860899866, scale precision, 145002208736712170093120437717821030188270278747, scale precision,
    3, 128, 3, 128, ⟨-3445596053769593210870193367139958430342876960431, -3445596053769593210870193367139958430342874863278⟩, ⟨-3376756754735933727183579054367174609576911172396, -3376756754735933727183579054367174609576909075243⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0616StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0617StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0617StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨474860522247948771940036538063380708083792495, 474860522247948771940036538063380708083792496⟩
def centerAExp : DyadicInterval precision := ⟨1460552224796057874071550301380937639903048136016, 1460552224796057874071550301380937642102071391569⟩
def centerALog : DyadicInterval precision := ⟨1012560955921529836431094652635425273892829583853, 1012560955921529836431094652635425276091852839406⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1460552224796057874071550301380937640452803949904, scale precision, 1460552224796057874071550301380937641552315577681, scale precision,
    0, 128, 0, 128, ⟨-949721044495897543880073076126761966281808906, -949721044495897543880073076126761966279711753⟩, ⟨-949721044495897543880073076126760866055458229, -949721044495897543880073076126760866053361076⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨687872580056255843160164202748380391008755458653, 687872580056255843160164202748380391008755458654⟩
def centerDExp : DyadicInterval precision := ⟨570148394211525905172999746249825252784123887881, 570148394211525905172999746249825254983147143434⟩
def centerDLog : DyadicInterval precision := ⟨481395051335389284017617212273304505633359993607, 481395051335389284017617212273304507832383249160⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨570148394211525905172999746249825253333879701769, scale precision, 570148394211525905172999746249825254433391329546, scale precision,
    1, 128, 1, 128, ⟨-1375745160112511686320328405496760783426739862143, -1375745160112511686320328405496760783426737764990⟩, ⟨-1375745160112511686320328405496760780608284069625, -1375745160112511686320328405496760780608281972472⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨688460206550326127935087978212372974843458648686, 688460206550326127935087978212372974843458648687⟩
def centerCExp : DyadicInterval precision := ⟨569690098959337062602789450418839198610082306992, 569690098959337062602789450418839200809105562545⟩
def centerCLog : DyadicInterval precision := ⟨481065331743748299401679581970839135983277191342, 481065331743748299401679581970839138182300446895⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨569690098959337062602789450418839199159838120880, scale precision, 569690098959337062602789450418839200259349748657, scale precision,
    1, 128, 1, 128, ⟨-1376920413100652255870175956424745951097279915508, -1376920413100652255870175956424745951097277818355⟩, ⟨-1376920413100652255870175956424745948276556776391, -1376920413100652255870175956424745948276554679238⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1671849052970953610058849103865138337028696289048, 1671849052970953610058849103865138337028696289049⟩
def centerBExp : DyadicInterval precision := ⟨148319483633444473887449258147491395887670734398, 148319483633444473887449258147491398086693989951⟩
def centerBLog : DyadicInterval precision := ⟨141266763480305004671486768193992100854399781920, 141266763480305004671486768193992103053423037473⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨148319483633444473887449258147491396437426548286, scale precision, 148319483633444473887449258147491397536938176063, scale precision,
    3, 128, 3, 128, ⟨-3343698105941907220117698207730276679474544512361, -3343698105941907220117698207730276679474542415208⟩, ⟨-3343698105941907220117698207730276668640242740978, -3343698105941907220117698207730276668640240643825⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨316573674294471837011765157253655004433778636, 633147383168915695688804483341311756669124067⟩
def wholeAExp : DyadicInterval precision := ⟨1460235890986607494244084883518378976785131112043, 1460868627107607697638964738615285410683914502614⟩
def wholeALog : DyadicInterval precision := ⟨1012402729061596953461092784027353937561977270075, 1012719199911638357989124323230052395461166191557⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1460235890986607494244084883518378977334886925931, scale precision, 1460868627107607697638964738615285410134158688726, scale precision,
    0, 128, 0, 128, ⟨-1266294766337831391377608966682624063571644160, -1266294766337831391377608966682624063569547007⟩, ⟨-633147348588943674023530314507309458874576803, -633147348588943674023530314507309458872479650⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨682249998762477519670394645145297230397519416513, 693511205829020257423882496604739492695821414415⟩
def wholeDExp : DyadicInterval precision := ⟨565765939962058116901418666290376202748638649045, 574552180098098577953261580846255154870927737058⟩
def wholeDLog : DyadicInterval precision := ⟨478239054014281969770673762969782321702426146976, 484559560373994267607098493867261018654665103074⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨565765939962058116901418666290376203298394462933, scale precision, 574552180098098577953261580846255154321171923170, scale precision,
    1, 128, 1, 128, ⟨-1387022411658040514847764993209478986811787730860, -1387022411658040514847764993209478986811785633707⟩, ⟨-1364499997524955039340789290290594459396613333134, -1364499997524955039340789290290594459396611235981⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨682640618143014187111337022065288110830276268787, 694296988583586797328139099438936365019573763196⟩
def wholeCExp : DyadicInterval precision := ⟨565157893869583595889082362262848653747310898340, 574245138029433207622338239115460182023867343960⟩
def wholeCLog : DyadicInterval precision := ⟨477800634505195911312537547708483727876471045232, 484339145608237259642998456852700265388094729246⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨565157893869583595889082362262848654297066712228, scale precision, 574245138029433207622338239115460181474111530072, scale precision,
    1, 128, 1, 128, ⟨-1388593977167173594656278198877872731460820342886, -1388593977167173594656278198877872731460818245733⟩, ⟨-1365281236286028374222674044130576220261379315583, -1365281236286028374222674044130576220261377218430⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1654799518693000536357843956327185517074350138483, 1688964600286453078456680412066824107088343719898⟩
def wholeBExp : DyadicInterval precision := ⟨144885931711580192725987711574601810207659644672, 151820689458754004437475082095501808375537229798⟩
def wholeBLog : DyadicInterval precision := ⟨138146229867118218390038705381545358014676197031, 144441937121773249280251983095422541805316007222⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨144885931711580192725987711574601810757415458560, scale precision, 151820689458754004437475082095501807825781415910, scale precision,
    3, 128, 3, 128, ⟨-3377929200572906156913360824133648219722216702456, -3377929200572906156913360824133648219722214605303⟩, ⟨-3309599037386001072715687912654371028856477815069, -3309599037386001072715687912654371028856475717916⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0617StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0618StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0618StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨474860522247948771940036538063380708083792495, 474860522247948771940036538063380708083792496⟩
def centerAExp : DyadicInterval precision := ⟨1460552224796057874071550301380937639903048136016, 1460552224796057874071550301380937642102071391569⟩
def centerALog : DyadicInterval precision := ⟨1012560955921529836431094652635425273892829583853, 1012560955921529836431094652635425276091852839406⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1460552224796057874071550301380937640452803949904, scale precision, 1460552224796057874071550301380937641552315577681, scale precision,
    0, 128, 0, 128, ⟨-949721044495897543880073076126761966281808906, -949721044495897543880073076126761966279711753⟩, ⟨-949721044495897543880073076126760866055458229, -949721044495897543880073076126760866053361076⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨676643340013426075185609328596269506214112195118, 676643340013426075185609328596269506214112195119⟩
def centerDExp : DyadicInterval precision := ⟨578977364869803800462989438501500576320691752033, 578977364869803800462989438501500578519715007586⟩
def centerDLog : DyadicInterval precision := ⟨487732559398326774108745629110692920177628439235, 487732559398326774108745629110692922376651694788⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨578977364869803800462989438501500576870447565921, scale precision, 578977364869803800462989438501500577969959193698, scale precision,
    1, 128, 1, 128, ⟨-1353286680026852150371218657192539013815963666390, -1353286680026852150371218657192539013815961569237⟩, ⟨-1353286680026852150371218657192539011040487211240, -1353286680026852150371218657192539011040485114087⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨677227642218405178699068699056696330316256073066, 677227642218405178699068699056696330316256073067⟩
def centerCExp : DyadicInterval precision := ⟨578514604475545607981789535231086411608882755648, 578514604475545607981789535231086413807906011201⟩
def centerCLog : DyadicInterval precision := ⟨487401067735498338562948564401982239208312419021, 487401067735498338562948564401982241407335674574⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨578514604475545607981789535231086412158638569536, scale precision, 578514604475545607981789535231086413258150197313, scale precision,
    1, 128, 1, 128, ⟨-1354455284436810357398137398113392662021361489834, -1354455284436810357398137398113392662021359392681⟩, ⟨-1354455284436810357398137398113392659243664899586, -1354455284436810357398137398113392659243662802433⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1638396732156115452144292769362534404102153219767, 1638396732156115452144292769362534404102153219768⟩
def centerBExp : DyadicInterval precision := ⟨155267064934933812078811072429928836533384186003, 155267064934933812078811072429928838732407441556⟩
def centerBLog : DyadicInterval precision := ⟨147560663663731261157574652954919079730978998267, 147560663663731261157574652954919081930002253820⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨155267064934933812078811072429928837083139999891, scale precision, 155267064934933812078811072429928838182651627668, scale precision,
    3, 128, 3, 128, ⟨-3276793464312230904288585538725068813379062497919, -3276793464312230904288585538725068813379060400766⟩, ⟨-3276793464312230904288585538725068803029552478303, -3276793464312230904288585538725068803029550381150⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨316573674294471837011765157253655004433778636, 633147383168915695688804483341311756669124067⟩
def wholeAExp : DyadicInterval precision := ⟨1460235890986607494244084883518378976785131112043, 1460868627107607697638964738615285410683914502614⟩
def wholeALog : DyadicInterval precision := ⟨1012402729061596953461092784027353937561977270075, 1012719199911638357989124323230052395461166191557⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1460235890986607494244084883518378977334886925931, scale precision, 1460868627107607697638964738615285410134158688726, scale precision,
    0, 128, 0, 128, ⟨-1266294766337831391377608966682624063571644160, -1266294766337831391377608966682624063569547007⟩, ⟨-633147348588943674023530314507309458874576803, -633147348588943674023530314507309458872479650⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨671052481512572809340093335645151882932874114537, 682249998762477519670394645145297230397519416514⟩
def wholeDExp : DyadicInterval precision := ⟨574552180098098577953261580846255152671904481505, 583424017396714902499808941799093865790753691861⟩
def wholeDLog : DyadicInterval precision := ⟨484559560373994267607098493867261016455641847521, 490914027605645316992013980560028282815828884161⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨574552180098098577953261580846255153221660295393, scale precision, 583424017396714902499808941799093865240997877973, scale precision,
    1, 128, 1, 128, ⟨-1364499997524955039340789290290594462193466430073, -1364499997524955039340789290290594462193464332920⟩, ⟨-1342104963025145618680186671290303764488587902438, -1342104963025145618680186671290303764488585805285⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨671440902009004248126867720023776049226259723643, 683031314619084692486505731858778884216162998376⟩
def wholeCExp : DyadicInterval precision := ⟨573938199493266823029006887170810434136973719899, 583113988827986525171167068164318275902800404820⟩
def wholeCLog : DyadicInterval precision := ⟨484118771935031274225078963723325307699800761813, 490692434409458928876431019351388742090300248391⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨573938199493266823029006887170810434686729533787, scale precision, 583113988827986525171167068164318275353044590932, scale precision,
    1, 128, 1, 128, ⟨-1366062629238169384973011463717557769832249585490, -1366062629238169384973011463717557769832247488337⟩, ⟨-1342881804018008496253735440047552097074626914977, -1342881804018008496253735440047552097074624817824⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1621480652225727667592799454759990618247396507031, 1655381305130276662974154815244741246774159253667⟩
def wholeBExp : DyadicInterval precision := ⟨151699865691894397774659456155015896291726742272, 158903251675320738035825572853393163364120012546⟩
def wholeBLog : DyadicInterval precision := ⟨144332479301226728302503501574231019240004440703, 150843956919355702479650421140762545621979481975⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨151699865691894397774659456155015896841482556160, scale precision, 158903251675320738035825572853393162814364198658, scale precision,
    3, 128, 3, 128, ⟨-3310762610260553325948309630489482498844758141831, -3310762610260553325948309630489482498844756044678⟩, ⟨-3242961304451455335185598909519981231438453090014, -3242961304451455335185598909519981231438450992861⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0618StableWitnesses

end


