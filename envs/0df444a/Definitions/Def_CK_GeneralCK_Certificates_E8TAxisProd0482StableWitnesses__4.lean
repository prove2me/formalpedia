-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0482StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0482StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:49:02.464741+00:00
-- url     : https://prove2.me/theorems/45041cb8-43fb-4a0d-83b0-872756575e3f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0482StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0483StableWitnesses, GeneralCK.Certificates.E8TAxisProd04…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0482StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0483StableWitnesses, GeneralCK.Certificates.E8TAxisProd0484StableWitnesses, GeneralCK.Certificates.E8TAxisProd0485StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0482StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0483StableWitnesses, GeneralCK.Certificates.E8TAxisProd0484StableWitnesses, GeneralCK.Certificates.E8TAxisProd0485StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0482StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0483StableWitnesses, GeneralCK.Certificates.E8TAxisProd0484StableWitnesses, GeneralCK.Certificates.E8TAxisProd0485StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0482StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0483StableWitnesses, GeneralCK/Certificates/E8TAxisProd0484StableWitnesses, GeneralCK/Certificates/E8TAxisProd0485StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0482StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0482StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨703306740623328259332614447048113828017570229168, 703306740623328259332614447048113828017570229169⟩
def centerCExp : DyadicInterval precision := ⟨558232590990884519310453326069836990948559978526, 558232590990884519310453326069836993147583234079⟩
def centerCLog : DyadicInterval precision := ⟨472797981782765576837385458561255455965752412778, 472797981782765576837385458561255458164775668331⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨558232590990884519310453326069836991498315792414, scale precision, 558232590990884519310453326069836992597827420191, scale precision,
    1, 128, 1, 128, ⟨-1406613481246656518665228894096227657474450202065, -1406613481246656518665228894096227657474448104912⟩, ⟨-1406613481246656518665228894096227654595832811762, -1406613481246656518665228894096227654595830714609⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1710854858747083230294860544880871831812665093297, 1710854858747083230294860544880871831812665093298⟩
def centerBExp : DyadicInterval precision := ⟨140610113766949584080091168983579921417380032150, 140610113766949584080091168983579923616403287703⟩
def centerBLog : DyadicInterval precision := ⟨134250876929258701039764858428359430366761556841, 134250876929258701039764858428359432565784812394⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨140610113766949584080091168983579921967135846038, scale precision, 140610113766949584080091168983579923066647473815, scale precision,
    3, 128, 3, 128, ⟨-3421709717494166460589721089761743669339493613718, -3421709717494166460589721089761743669339491516565⟩, ⟨-3421709717494166460589721089761743657911168856625, -3421709717494166460589721089761743657911166759472⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨697443255443293703209440688032823366239633830262, 709187760133762498890382215058194219119912807035⟩
def wholeCExp : DyadicInterval precision := ⟨553758012945093357002741555662217579969335001840, 562729822514083996006476491737807535134451847509⟩
def wholeCLog : DyadicInterval precision := ⟨469556536557443266903848819351227687988676535040, 476048609731171512453988408824795765049422238625⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨553758012945093357002741555662217580519090815728, scale precision, 562729822514083996006476491737807534584696033621, scale precision,
    1, 128, 1, 128, ⟨-1418375520267524997780764430116388439690765526459, -1418375520267524997780764430116388439690763429306⟩, ⟨-1394886510886587406418881376065646731051462699922, -1394886510886587406418881376065646731051460602769⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1693657103013463375347989217518727202281841180984, 1728115692693053516165256357166509114046150241292⟩
def wholeBExp : DyadicInterval precision := ⟨137327725485643907527755950555576737480295083550, 143958530240901270872294781448537316302804128087⟩
def wholeBLog : DyadicInterval precision := ⟨131253497497244193434084011746101138057851042503, 137302230452029500151783167128877713473733911694⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨137327725485643907527755950555576738030050897438, scale precision, 143958530240901270872294781448537315753048314199, scale precision,
    3, 128, 3, 128, ⟨-3456231385386107032330512714333018233943043027744, -3456231385386107032330512714333018233943040930591⟩, ⟨-3387314206026926750695978435037454398982430109434, -3387314206026926750695978435037454398982428012281⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0482StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0483StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0483StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨691989641959829054725386149046998800087065196006, 691989641959829054725386149046998800087065196007⟩
def centerCExp : DyadicInterval precision := ⟨566945200853312232666565377693660803518989738796, 566945200853312232666565377693660805718012994349⟩
def centerCLog : DyadicInterval precision := ⟨479088961870417822942788075538787709930462497911, 479088961870417822942788075538787712129485753464⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨566945200853312232666565377693660804068745552684, scale precision, 566945200853312232666565377693660805168257180461, scale precision,
    1, 128, 1, 128, ⟨-1383979283919658109450772298093997601591321357570, -1383979283919658109450772298093997601591319260417⟩, ⟨-1383979283919658109450772298093997598756941523607, -1383979283919658109450772298093997598756939426454⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1677108403571415417115395925685594467915595732573, 1677108403571415417115395925685594467915595732574⟩
def centerBExp : DyadicInterval precision := ⟨147255832750209297724118665493713677996692658476, 147255832750209297724118665493713680195715914029⟩
def centerBLog : DyadicInterval precision := ⟨140300791999408090096498134251459363534924937813, 140300791999408090096498134251459365733948193366⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨147255832750209297724118665493713678546448472364, scale precision, 147255832750209297724118665493713679645960100141, scale precision,
    3, 128, 3, 128, ⟨-3354216807142830834230791851371188941287472289700, -3354216807142830834230791851371188941287470192547⟩, ⟨-3354216807142830834230791851371188930374912737738, -3354216807142830834230791851371188930374910640585⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨686159666796967221200657712583137752365028557877, 697836892256037058417321656034605662930316568548⟩
def wholeCExp : DyadicInterval precision := ⟨562426775952085976433246998731028264936148254480, 571486415639431013232450674881352924757621799325⟩
def wholeCLog : DyadicInterval precision := ⟨475829792756913659120118223119573271672438095049, 482357262748874645606607404198004595361621207323⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨562426775952085976433246998731028265485904068368, scale precision, 571486415639431013232450674881352924207865985437, scale precision,
    1, 128, 1, 128, ⟨-1395673784512074116834643312069211327289209524691, -1395673784512074116834643312069211327289207427538⟩, ⟨-1372319333593934442401315425166275503324129694043, -1372319333593934442401315425166275503324127596890⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1660038421706511897822969580392909836447726577272, 1694244005002628028641414978021063750581771776771⟩
def wholeBExp : DyadicInterval precision := ⟨143842956469623283927534762601991069294371648369, 150736147985821126282281715965901366514694326057⟩
def wholeBLog : DyadicInterval precision := ⟨137197016171759128747790559401771224269130320807, 143459125366241291366182114618108041692512110327⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨143842956469623283927534762601991069844127462257, scale precision, 150736147985821126282281715965901365964938512169, scale precision,
    3, 128, 3, 128, ⟨-3388488010005256057282829956042127506749282283336, -3388488010005256057282829956042127506749280186183⟩, ⟨-3320076843413023795645939160785819667565153323964, -3320076843413023795645939160785819667565151226811⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0483StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0484StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0484StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨681127397117516990032046507647359981419121827548, 681127397117516990032046507647359981419121827549⟩
def centerCExp : DyadicInterval precision := ⟨575435502961254404477311991573987723114016340572, 575435502961254404477311991573987725313039596125⟩
def centerCLog : DyadicInterval precision := ⟨485193481659081687280110987324281767389333048822, 485193481659081687280110987324281769588356304375⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨575435502961254404477311991573987723663772154460, scale precision, 575435502961254404477311991573987724763283782237, scale precision,
    1, 128, 1, 128, ⟨-1362254794235033980064093015294719964234524596025, -1362254794235033980064093015294719964234522498872⟩, ⟨-1362254794235033980064093015294719961441964811321, -1362254794235033980064093015294719961441962714168⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1644195781104204969199498720673843689015645898787, 1644195781104204969199498720673843689015645898788⟩
def centerBExp : DyadicInterval precision := ⟨154039781922795957669676285564457597384542820523, 154039781922795957669676285564457599583566076076⟩
def centerBLog : DyadicInterval precision := ⟨146450822002213661365276676797977692414780465373, 146450822002213661365276676797977694613803720926⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨154039781922795957669676285564457597934298634411, scale precision, 154039781922795957669676285564457599033810262188, scale precision,
    3, 128, 3, 128, ⟨-3288391562208409938398997441347687383247276743953, -3288391562208409938398997441347687383247274646800⟩, ⟨-3288391562208409938398997441347687372815308948349, -3288391562208409938398997441347687372815306851196⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨675329288864423820177837302820238471781047681443, 686942528671712951188642664631073628138066256370⟩
def wholeCExp : DyadicInterval precision := ⟨570874503410018429906005369867655703723462406831, 580019430524322541687096084699971845484966371527⟩
def wholeCLog : DyadicInterval precision := ⟨481917296886368902883035266330168854202670761912, 488478752767867072479533858432485929323520752381⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨570874503410018429906005369867655704273218220719, scale precision, 580019430524322541687096084699971844935210557639, scale precision,
    1, 128, 1, 128, ⟨-1373885057343425902377285329262147257683569026258, -1373885057343425902377285329262147257683566929105⟩, ⟨-1350658577728847640355674605640476942176851400958, -1350658577728847640355674605640476942176849303805⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1627256144769237695411136395123532003715512102016, 1661203483741545126463908302306172714863958472495⟩
def wholeBExp : DyadicInterval precision := ⟨150496015457705116779311993365428520350255689685, 157652309003256544148525824143611650339200818704⟩
def wholeBLog : DyadicInterval precision := ⟨143241427812570651915614029318057366061067739506, 149715250853360510911651937699727429177307883551⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨150496015457705116779311993365428520900011503573, scale precision, 157652309003256544148525824143611649789445004816, scale precision,
    3, 128, 3, 128, ⟨-3322406967483090252927816604612345435066723939271, -3322406967483090252927816604612345435066721842118⟩, ⟨-3254512289538475390822272790247064002334563125226, -3254512289538475390822272790247064002334561028073⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0484StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0485StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0485StableWitnesses

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

def centerCAlpha : DyadicInterval precision := ⟨669936195056029783926589259363398542058948564808, 669936195056029783926589259363398542058948564809⟩
def centerCExp : DyadicInterval precision := ⟨584315930208506933649112899744190579068529285898, 584315930208506933649112899744190581267552541451⟩
def centerCLog : DyadicInterval precision := ⟨491551335783949311757249624080811585681495358799, 491551335783949311757249624080811587880518614352⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨584315930208506933649112899744190579618285099786, scale precision, 584315930208506933649112899744190580717796727563, scale precision,
    1, 128, 1, 128, ⟨-1339872390112059567853178518726797085492957423702, -1339872390112059567853178518726797085492955326549⟩, ⟨-1339872390112059567853178518726797082742838932688, -1339872390112059567853178518726797082742836835535⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1610961422763246269981965243876127880323625822806, 1610961422763246269981965243876127880323625822807⟩
def centerBExp : DyadicInterval precision := ⟨161207222673789942496972762792964073504084040639, 161207222673789942496972762792964075703107296192⟩
def centerBLog : DyadicInterval precision := ⟨152920515568667923205705389263616768578360389409, 152920515568667923205705389263616770777383644962⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨161207222673789942496972762792964074053839854527, scale precision, 161207222673789942496972762792964075153351482304, scale precision,
    3, 128, 3, 128, ⟨-3221922845526492539963930487752255765631328524068, -3221922845526492539963930487752255765631326426915⟩, ⟨-3221922845526492539963930487752255755663176864312, -3221922845526492539963930487752255755663174767159⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨664170604356148777566692885139367032399673075376, 675718546647557729610870280728316915673612630621⟩
def wholeCExp : DyadicInterval precision := ⟨579710546909111830060882595310196767071242541169, 588944391466983465608803865955127969246717034464⟩
def wholeCLog : DyadicInterval precision := ⟨488257609782341490024429700321298660726237471224, 494854104967280797095451782711959473615897983076⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨579710546909111830060882595310196767620998355057, scale precision, 588944391466983465608803865955127968696961220576, scale precision,
    1, 128, 1, 128, ⟨-1351437093295115459221740561456633832733209411925, -1351437093295115459221740561456633832733207314772⟩, ⟨-1328341208712297555133385770278734063435094421358, -1328341208712297555133385770278734063435092324205⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1594159195088642481552023836766490869778453736004, 1627834140397050486508809146235155684453644639948⟩
def wholeBExp : DyadicInterval precision := ⟨157527661427959579746386171747715852526463261562, 164956818921044295790491242147040254004404703104⟩
def wholeBLog : DyadicInterval precision := ⟨149602735518873574988222580538710532583495960265, 156293714270974927969249608627502328389392066360⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨157527661427959579746386171747715853076219075450, scale precision, 164956818921044295790491242147040253454648889216, scale precision,
    3, 128, 3, 128, ⟨-3255668280794100973017618292470311374007785154887, -3255668280794100973017618292470311374007783057734⟩, ⟨-3188318390177284963104047673532981734686124594305, -3188318390177284963104047673532981734686122497152⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0485StableWitnesses

end


