-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0383StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0383StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T00:15:09.428167+00:00
-- url     : https://prove2.me/theorems/24cea079-a743-408d-b251-b3539f9feeb7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0383StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0384StableWitnesses, GeneralCK.Certificates.E8TAxisProd03…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0383StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0384StableWitnesses, GeneralCK.Certificates.E8TAxisProd0385StableWitnesses, GeneralCK.Certificates.E8TAxisProd0386StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0383StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0384StableWitnesses, GeneralCK.Certificates.E8TAxisProd0385StableWitnesses, GeneralCK.Certificates.E8TAxisProd0386StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0383StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0384StableWitnesses, GeneralCK.Certificates.E8TAxisProd0385StableWitnesses, GeneralCK.Certificates.E8TAxisProd0386StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0383StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0384StableWitnesses, GeneralCK/Certificates/E8TAxisProd0385StableWitnesses, GeneralCK/Certificates/E8TAxisProd0386StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0383StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0383StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨827900739799584217789378743685278152778005680170, 827900739799584217789378743685278152778005680171⟩
def centerDExp : DyadicInterval precision := ⟨470725140515848859951996893419642374006683999039, 470725140515848859951996893419642376205707254592⟩
def centerDLog : DyadicInterval precision := ⟨408063947160780491089293755661542510045178856930, 408063947160780491089293755661542512244202112483⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨470725140515848859951996893419642374556439812927, scale precision, 470725140515848859951996893419642375655951440704, scale precision,
    1, 128, 1, 128, ⟨-1655801479599168435578757487370556307262887510703, -1655801479599168435578757487370556307262885413550⟩, ⟨-1655801479599168435578757487370556303849137307135, -1655801479599168435578757487370556303849135209982⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨828953100486956427713233645674588868200021498126, 828953100486956427713233645674588868200021498127⟩
def centerCExp : DyadicInterval precision := ⟨470047732984152732336382952893188305343416458594, 470047732984152732336382952893188307542439714147⟩
def centerCLog : DyadicInterval precision := ⟨407551478431281725178987671986887343804721288870, 407551478431281725178987671986887346003744544423⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨470047732984152732336382952893188305893172272482, scale precision, 470047732984152732336382952893188306992683900259, scale precision,
    1, 128, 1, 128, ⟨-1657906200973912855426467291349177738109379003282, -1657906200973912855426467291349177738109376906129⟩, ⟨-1657906200973912855426467291349177734690709086381, -1657906200973912855426467291349177734690706989228⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2090958717024806202556632141490830086669084421239, 2090958717024806202556632141490830086669084421240⟩
def centerBExp : DyadicInterval precision := ⟨83582626563511533980907775891254418574409202941, 83582626563511533980907775891254420773432458494⟩
def centerBLog : DyadicInterval precision := ⟨81279985268076077202324556630773136018868926416, 81279985268076077202324556630773138217892181969⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨83582626563511533980907775891254419124165016829, scale precision, 83582626563511533980907775891254420223676644606, scale precision,
    4, 128, 4, 128, ⟨-4181917434049612405113264282981660182951041072121, -4181917434049612405113264282981660182951038974968⟩, ⟨-4181917434049612405113264282981660163725298709988, -4181917434049612405113264282981660163725296612835⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨821860677686075647293949968540300351172223479071, 833959591445470778384083818034390997094871334899⟩
def wholeDExp : DyadicInterval precision := ⟨466838367135635595432846250236128801963479725593, 474632069948069015840646238761706424600391594793⟩
def wholeDLog : DyadicInterval precision := ⟨405121100734994108525530084726425875355168584540, 411016094834480306545789264008568525844426144161⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨466838367135635595432846250236128802513235539481, scale precision, 474632069948069015840646238761706424050635780905, scale precision,
    1, 128, 1, 128, ⟨-1667919182890941556768167636068781995910829813032, -1667919182890941556768167636068781995910827715879⟩, ⟨-1643721355372151294587899937080600700651623031325, -1643721355372151294587899937080600700651620934172⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨822699912785279912774534199131224920830855176310, 835226426890574751213532654125372779347916601829⟩
def wholeCExp : DyadicInterval precision := ⟨466029753532540862090271280350588479586796887867, 474087288828889409126792989251665628088010778074⟩
def wholeCLog : DyadicInterval precision := ⟨404508118609269361109892836107281644959499173003, 410604805814938456591878660716913003836404083763⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨466029753532540862090271280350588480136552701755, scale precision, 474087288828889409126792989251665627538254964186, scale precision,
    1, 128, 1, 128, ⟨-1670452853781149502427065308250745560419906623236, -1670452853781149502427065308250745560419904526083⟩, ⟨-1645399825570559825549068398262449839966941174146, -1645399825570559825549068398262449839966939076993⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2072697921322096428265495070747192562019105547627, 2109255328468702952723541225435170056881228666919⟩
def wholeBExp : DyadicInterval precision := ⟨81515858417544749862430306575135636867240081917, 85697595596340978801113781081935525790527974890⟩
def wholeBLog : DyadicInterval precision := ⟨79323711987329917054760310596488847181106280509, 83279175309703449264939172345809133332654846437⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨81515858417544749862430306575135637416995895805, scale precision, 85697595596340978801113781081935525240772161002, scale precision,
    4, 128, 4, 128, ⟨-4218510656937405905447082450870340123619056076747, -4218510656937405905447082450870340123619053979594⟩, ⟨-4145395842644192856530990141494385114662581281148, -4145395842644192856530990141494385114662579183995⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0383StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0384StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0384StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1108008086961741616166050582946352244611295173, 1108008086961741616166050582946352244611295174⟩
def centerAExp : DyadicInterval precision := ⟨1459287300336296999564987921182920319954750140059, 1459287300336296999564987921182920322153773395612⟩
def centerALog : DyadicInterval precision := ⟨1011928151219685967171369581941982746115885093399, 1011928151219685967171369581941982748314908348952⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1459287300336296999564987921182920320504505953947, scale precision, 1459287300336296999564987921182920321604017581724, scale precision,
    0, 128, 0, 128, ⟨-2216016173923483232332101165892705039813657726, -2216016173923483232332101165892705039811560573⟩, ⟨-2216016173923483232332101165892703938633620121, -2216016173923483232332101165892703938631522968⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨815839300550668055994007428828159575323513310288, 815839300550668055994007428828159575323513310289⟩
def centerDExp : DyadicInterval precision := ⟨478559189448815119699945348173357163995361504812, 478559189448815119699945348173357166194384760365⟩
def centerDLog : DyadicInterval precision := ⟨413977501179630865966571380465000387295391805362, 413977501179630865966571380465000389494415060915⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨478559189448815119699945348173357164545117318700, scale precision, 478559189448815119699945348173357165644628946477, scale precision,
    1, 128, 1, 128, ⟨-1631678601101336111988014857656319152325961100681, -1631678601101336111988014857656319152325959003528⟩, ⟨-1631678601101336111988014857656319148968094237626, -1631678601101336111988014857656319148968092140473⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨817303659808294550000266892216337446347281111568, 817303659808294550000266892216337446347281111569⟩
def centerCExp : DyadicInterval precision := ⟨477601159874987686998985565507304547375068086276, 477601159874987686998985565507304549574091341829⟩
def centerCLog : DyadicInterval precision := ⟨413255612672237390596882418823715221595515512482, 413255612672237390596882418823715223794538768035⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨477601159874987686998985565507304547924823900164, scale precision, 477601159874987686998985565507304549024335527941, scale precision,
    1, 128, 1, 128, ⟨-1634607319616589100000533784432674894376864508879, -1634607319616589100000533784432674894376862411726⟩, ⟨-1634607319616589100000533784432674891012262034545, -1634607319616589100000533784432674891012259937392⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2055718970607439368039864481664047663122367176999, 2055718970607439368039864481664047663122367177000⟩
def centerBExp : DyadicInterval precision := ⟨87712086665062320110587245290087908297332523278, 87712086665062320110587245290087910496355778831⟩
def centerBLog : DyadicInterval precision := ⟨85180848278828755560629945036044238895976536091, 85180848278828755560629945036044241094999791644⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨87712086665062320110587245290087908847088337166, scale precision, 87712086665062320110587245290087909946599964943, scale precision,
    4, 128, 4, 128, ⟨-4111437941214878736079728963328095335405035341609, -4111437941214878736079728963328095335405033244456⟩, ⟨-4111437941214878736079728963328095317084435463547, -4111437941214878736079728963328095317084433366394⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨949721161203312387564849132921065893757597830, 1266295042977660303900587558721132456011189596⟩
def wholeAExp : DyadicInterval precision := ⟨1458971240300741788424025014233787498548709353580, 1459603428780171974367103696970164796353834591973⟩
def wholeALog : DyadicInterval precision := ⟨1011769992837296815097311935000023817181636979342, 1012086326714990166522051059359330290859456642138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1458971240300741788424025014233787499098465167468, scale precision, 1459603428780171974367103696970164795804078778085, scale precision,
    0, 128, 0, 128, ⟨-2532590085955320607801175117442265462732722054, -2532590085955320607801175117442265462730624901⟩, ⟨-1899442322406624775129698265842131237045475062, -1899442322406624775129698265842131237043377909⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨809836502735595761416983074307699172577520882055, 821860677686075647293949968540300351172223479072⟩
def wholeDExp : DyadicInterval precision := ⟨474632069948069015840646238761706422401368339240, 482506534178222248007502303634473308617104830159⟩
def wholeDLog : DyadicInterval precision := ⟨411016094834480306545789264008568523645402888608, 416948124396604742320674577430730287178108048617⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨474632069948069015840646238761706422951124153128, scale precision, 482506534178222248007502303634473308067349016271, scale precision,
    1, 128, 1, 128, ⟨-1643721355372151294587899937080600704037272982110, -1643721355372151294587899937080600704037270884957⟩, ⟨-1619673005471191522833966148615398343489844592111, -1619673005471191522833966148615398343489842494958⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨811087731675774606554228965565346465431325919799, 823539509859430523244296081108954404821923089898⟩
def wholeCExp : DyadicInterval precision := ⟨473542898439744410988485104098145144239144916325, 481681068707005795963659712017581727364624724787⟩
def wholeCLog : DyadicInterval precision := ⟨410193696130617163810602601810729206945372436045, 416327409235512029873697156562179998839711286688⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨473542898439744410988485104098145144788900730213, scale precision, 481681068707005795963659712017581726814868910899, scale precision,
    1, 128, 1, 128, ⟨-1647079019718861046488592162217908811340565782861, -1647079019718861046488592162217908811340563685708⟩, ⟨-1622175463351549213108457931130692929194600987594, -1622175463351549213108457931130692929194598890441⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2037530651059979506425611856463181752288569434996, 2073945358355583370179844590123450346530242728895⟩
def wholeBExp : DyadicInterval precision := ⟨85551429271079398229205787359921123905210051611, 89922628268102502592658833753886083088496345572⟩
def wholeBLog : DyadicInterval precision := ⟨83141098447720451170806673649633558112942247118, 87264748902140259361355498422233846567259295154⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨85551429271079398229205787359921124454965865499, scale precision, 89922628268102502592658833753886082538740531684, scale precision,
    4, 128, 4, 128, ⟨-4147890716711166740359689180246900702452135821595, -4147890716711166740359689180246900702452133724442⟩, ⟨-4075061302119959012851223712926363495642024946902, -4075061302119959012851223712926363495642022849749⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0384StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0385StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0385StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1108008086961741616166050582946352244611295173, 1108008086961741616166050582946352244611295174⟩
def centerAExp : DyadicInterval precision := ⟨1459287300336296999564987921182920319954750140059, 1459287300336296999564987921182920322153773395612⟩
def centerALog : DyadicInterval precision := ⟨1011928151219685967171369581941982746115885093399, 1011928151219685967171369581941982748314908348952⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1459287300336296999564987921182920320504505953947, scale precision, 1459287300336296999564987921182920321604017581724, scale precision,
    0, 128, 0, 128, ⟨-2216016173923483232332101165892705039813657726, -2216016173923483232332101165892705039811560573⟩, ⟨-2216016173923483232332101165892703938633620121, -2216016173923483232332101165892703938631522968⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨803852177515934255585547919467375235228063974291, 803852177515934255585547919467375235228063974292⟩
def centerDExp : DyadicInterval precision := ⟨486474140463139135434442039725801311744313926422, 486474140463139135434442039725801313943337181975⟩
def centerDLog : DyadicInterval precision := ⟨419927923473864759956554512738531498009528841884, 419927923473864759956554512738531500208552097437⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨486474140463139135434442039725801312294069740310, scale precision, 486474140463139135434442039725801313393581368087, scale precision,
    1, 128, 1, 128, ⟨-1607704355031868511171095838934750472107746123950, -1607704355031868511171095838934750472107744026797⟩, ⟨-1607704355031868511171095838934750468804511870366, -1607704355031868511171095838934750468804509773213⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨805307535111995155808449527656326775752019200841, 805307535111995155808449527656326775752019200842⟩
def centerCExp : DyadicInterval precision := ⟨485506246527390756000463331343540038537854436545, 485506246527390756000463331343540040736877692098⟩
def centerCLog : DyadicInterval precision := ⟨419201564277597401999923900457138297218555592729, 419201564277597401999923900457138299417578848282⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨485506246527390756000463331343540039087610250433, scale precision, 485506246527390756000463331343540040187121878210, scale precision,
    1, 128, 1, 128, ⟨-1610615070223990311616899055312653553158949202455, -1610615070223990311616899055312653553158947105302⟩, ⟨-1610615070223990311616899055312653549849129698063, -1610615070223990311616899055312653549849127600910⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2020001411490027776842553725049273865334462379908, 2020001411490027776842553725049273865334462379909⟩
def centerBExp : DyadicInterval precision := ⟨92105770823331967958946681393062672427208382873, 92105770823331967958946681393062674626231638426⟩
def centerBLog : DyadicInterval precision := ⟨89319907934320925979627456089949217674664191845, 89319907934320925979627456089949219873687447398⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨92105770823331967958946681393062672976964196761, scale precision, 92105770823331967958946681393062674076475824538, scale precision,
    3, 128, 3, 128, ⟨-4040002822980055553685107450098547739392255681734, -4040002822980055553685107450098547739392253584581⟩, ⟨-4040002822980055553685107450098547721945595935053, -4040002822980055553685107450098547721945593837900⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨949721161203312387564849132921065893757597830, 1266295042977660303900587558721132456011189596⟩
def wholeAExp : DyadicInterval precision := ⟨1458971240300741788424025014233787498548709353580, 1459603428780171974367103696970164796353834591973⟩
def wholeALog : DyadicInterval precision := ⟨1011769992837296815097311935000023817181636979342, 1012086326714990166522051059359330290859456642138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1458971240300741788424025014233787499098465167468, scale precision, 1459603428780171974367103696970164795804078778085, scale precision,
    0, 128, 0, 128, ⟨-2532590085955320607801175117442265462732722054, -2532590085955320607801175117442265462730624901⟩, ⟨-1899442322406624775129698265842131237045475062, -1899442322406624775129698265842131237043377909⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨797886217135535601213561462349015058648188303747, 809836502735595761416983074307699172577520882056⟩
def wholeDExp : DyadicInterval precision := ⟨482506534178222248007502303634473306418081574606, 490462045819898463991457369988920388736986392916⟩
def wholeDLog : DyadicInterval precision := ⟨416948124396604742320674577430730284979084793064, 422916858198723400101802834922666848815462481446⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨482506534178222248007502303634473306967837388494, scale precision, 490462045819898463991457369988920388187230579028, scale precision,
    1, 128, 1, 128, ⟨-1619673005471191522833966148615398346820241033264, -1619673005471191522833966148615398346820238936111⟩, ⟨-1595772434271071202427122924698030115658189688259, -1595772434271071202427122924698030115658187591106⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨799129776074145010927973484050916306597305645699, 811504986947922929239925947523306949641647503036⟩
def wholeCExp : DyadicInterval precision := ⟨481406109595430094083723777098491178433322826272, 489628109307077895065295537232838891084320038236⟩
def wholeCLog : DyadicInterval precision := ⟨416120593054930848909036220004116033053952326748, 422292328133333896884740329317328100045931867015⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨481406109595430094083723777098491178983078640160, scale precision, 489628109307077895065295537232838890534564224348, scale precision,
    1, 128, 1, 128, ⟨-1623009973895845858479851895046613900952300676971, -1623009973895845858479851895046613900952298579818⟩, ⟨-1598259552148290021855946968101832611553634204002, -1598259552148290021855946968101832611553632106849⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2001891418568329185984063018994951661508980170849, 2038151832608710153241578346642140254192064315095⟩
def wholeBExp : DyadicInterval precision := ⟨89846221179162959037049744831137882822425954917, 94416922374013343216834104402173949352699684449⟩
def wholeBLog : DyadicInterval precision := ⟨87192768697894052964319011343168134816602666883, 91492427110769098957899019788050945658723500265⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨89846221179162959037049744831137883372181768805, scale precision, 94416922374013343216834104402173948802943870561, scale precision,
    4, 128, 3, 128, ⟨-4076303665217420306483156693284280517326843257421, -4076303665217420306483156693284280517326841160268⟩, ⟨-4003782837136658371968126037989903314508162490595, -4003782837136658371968126037989903314508160393442⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0385StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0386StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0386StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨815839300550668055994007428828159575323513310288, 815839300550668055994007428828159575323513310289⟩
def centerDExp : DyadicInterval precision := ⟨478559189448815119699945348173357163995361504812, 478559189448815119699945348173357166194384760365⟩
def centerDLog : DyadicInterval precision := ⟨413977501179630865966571380465000387295391805362, 413977501179630865966571380465000389494415060915⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨478559189448815119699945348173357164545117318700, scale precision, 478559189448815119699945348173357165644628946477, scale precision,
    1, 128, 1, 128, ⟨-1631678601101336111988014857656319152325961100681, -1631678601101336111988014857656319152325959003528⟩, ⟨-1631678601101336111988014857656319148968094237626, -1631678601101336111988014857656319148968092140473⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨816885158970042083573180224344496659056599387751, 816885158970042083573180224344496659056599387752⟩
def centerCExp : DyadicInterval precision := ⟨477874760295526702448848688297713084048763790333, 477874760295526702448848688297713086247787045886⟩
def centerCLog : DyadicInterval precision := ⟨413461810742753416806987835828550089824275397450, 413461810742753416806987835828550092023298653003⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨477874760295526702448848688297713084598519604221, scale precision, 477874760295526702448848688297713085698031231998, scale precision,
    1, 128, 1, 128, ⟨-1633770317940084167146360448688993319794537883517, -1633770317940084167146360448688993319794535786364⟩, ⟨-1633770317940084167146360448688993316431861764639, -1633770317940084167146360448688993316431859667486⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2055096512488563733964154809223569187138902254365, 2055096512488563733964154809223569187138902254366⟩
def centerBExp : DyadicInterval precision := ⟨87786832199042820456060664408301107290817068412, 87786832199042820456060664408301109489840323965⟩
def centerBLog : DyadicInterval precision := ⟨85251360231697541123247594662759318005558960386, 85251360231697541123247594662759320204582215939⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨87786832199042820456060664408301107840572882300, scale precision, 87786832199042820456060664408301108940084510077, scale precision,
    4, 128, 4, 128, ⟨-4110193024977127467928309618447138383430306017844, -4110193024977127467928309618447138383430303920691⟩, ⟨-4110193024977127467928309618447138365125305096784, -4110193024977127467928309618447138365125302999631⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨809836502735595761416983074307699172577520882055, 821860677686075647293949968540300351172223479072⟩
def wholeDExp : DyadicInterval precision := ⟨474632069948069015840646238761706422401368339240, 482506534178222248007502303634473308617104830159⟩
def wholeDLog : DyadicInterval precision := ⟨411016094834480306545789264008568523645402888608, 416948124396604742320674577430730287178108048617⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨474632069948069015840646238761706422951124153128, scale precision, 482506534178222248007502303634473308067349016271, scale precision,
    1, 128, 1, 128, ⟨-1643721355372151294587899937080600704037272982110, -1643721355372151294587899937080600704037270884957⟩, ⟨-1619673005471191522833966148615398343489844592111, -1619673005471191522833966148615398343489842494958⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨810670565907037876488723624342609025957453549729, 823119666057822658831317205669290242800543416658⟩
def wholeCExp : DyadicInterval precision := ⟨473815044798853576550160006882288800781261049815, 481956125833086315749853067000388604141989821689⟩
def wholeCLog : DyadicInterval precision := ⟨410399228548753046178086963627619341997529913574, 416534269861794695463570304080147452369298648452⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨473815044798853576550160006882288801331016863703, scale precision, 481956125833086315749853067000388603592234007801, scale precision,
    1, 128, 1, 128, ⟨-1646239332115645317662634411338580487296831887807, -1646239332115645317662634411338580487296829790654⟩, ⟨-1621341131814075752977447248685218050247808221166, -1621341131814075752977447248685218050247806124013⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2036909515398171016267466700791932631192310746611, 2073321618255447963217864367100428326243128250291⟩
def wholeBExp : DyadicInterval precision := ⟨85624483773334840911141550550571817411048785394, 89999094683791895900249242910123605207623445955⟩
def wholeBLog : DyadicInterval precision := ⟨83210111435141980110766583593979199952176605055, 87336781446813071146796007410725082786331093231⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨85624483773334840911141550550571817960804599282, scale precision, 89999094683791895900249242910123604657867632067, scale precision,
    4, 128, 4, 128, ⟨-4146643236510895926435728734200856661869893942891, -4146643236510895926435728734200856661869891845738⟩, ⟨-4073819030796342032534933401583865253457099160010, -4073819030796342032534933401583865253457097062857⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0386StableWitnesses

end


