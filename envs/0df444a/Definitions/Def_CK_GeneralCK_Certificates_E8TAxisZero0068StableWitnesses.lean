-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0068StableWitnesses
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0068StableWitnesses
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:58:43.386628+00:00
-- url     : https://prove2.me/theorems/9f694167-b656-4e32-8384-7e0b10a4898e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0068StableWitnesses` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0068StableWitnesses` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0068StableWitnesses` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0068StableWitnesses (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0068StableWitnesses.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisZero0068StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0068StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨687872580056255843160164202748380391008755458653, 687872580056255843160164202748380391008755458654⟩
def centerDExp : DyadicInterval precision := ⟨570148394211525905172999746249825252784123887881, 570148394211525905172999746249825254983147143434⟩
def centerDLog : DyadicInterval precision := ⟨481395051335389284017617212273304505633359993607, 481395051335389284017617212273304507832383249160⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨570148394211525905172999746249825253333879701769, scale precision, 570148394211525905172999746249825254433391329546, scale precision,
    0, 512, 0, 512, ⟨-1375745160112511686320328405496760783426739862143, -1375745160112511686320328405496760783426737764990⟩, ⟨-1375745160112511686320328405496760780608284069625, -1375745160112511686320328405496760780608281972472⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨688068436136319988740290484994143958559223918478, 688068436136319988740290484994143958559223918479⟩
def centerCExp : DyadicInterval precision := ⟨569995603323698386149835536660754735559872581040, 569995603323698386149835536660754737758895836593⟩
def centerCLog : DyadicInterval precision := ⟨481285134505958845134115259150065001493702037991, 481285134505958845134115259150065003692725293544⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨569995603323698386149835536660754736109628394928, scale precision, 569995603323698386149835536660754737209140022705, scale precision,
    0, 512, 0, 512, ⟨-1376136872272639977480580969988287918528054534148, -1376136872272639977480580969988287918528052436995⟩, ⟨-1376136872272639977480580969988287915708843236920, -1376136872272639977480580969988287915708841139767⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1671265065795329294893386048741113267810290674681, 1671265065795329294893386048741113267810290674682⟩
def centerBExp : DyadicInterval precision := ⟨148438062078596721356242994319740382421442704938, 148438062078596721356242994319740384620465960491⟩
def centerBLog : DyadicInterval precision := ⟨141374412837812492936159887741650595395005644978, 141374412837812492936159887741650597594028900531⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨148438062078596721356242994319740382971198518826, scale precision, 148438062078596721356242994319740384070710146603, scale precision,
    0, 512, 0, 512, ⟨-3342530131590658589786772097482226541033405840117, -3342530131590658589786772097482226541033403742964⟩, ⟨-3342530131590658589786772097482226530207758955764, -3342530131590658589786772097482226530207756858611⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨682249998762477519670394645145297230397519416513, 693511205829020257423882496604739492695821414415⟩
def wholeDExp : DyadicInterval precision := ⟨565765939962058116901418666290376202748638649045, 574552180098098577953261580846255154870927737058⟩
def wholeDLog : DyadicInterval precision := ⟨478239054014281969770673762969782321702426146976, 484559560373994267607098493867261018654665103074⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨565765939962058116901418666290376203298394462933, scale precision, 574552180098098577953261580846255154321171923170, scale precision,
    0, 512, 0, 512, ⟨-1387022411658040514847764993209478986811787730860, -1387022411658040514847764993209478986811785633707⟩, ⟨-1364499997524955039340789290290594459396613333134, -1364499997524955039340789290290594459396611235981⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨682249998762477519670394645145297230397519416513, 693904058069515033255127039781986599918628876747⟩
def wholeCExp : DyadicInterval precision := ⟨565461865470576534734447866887954414112786637478, 574552180098098577953261580846255154870927737058⟩
def wholeCLog : DyadicInterval precision := ⟨478019823605741052943043982346050640148625876758, 484559560373994267607098493867261018654665103074⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨565461865470576534734447866887954414662542451366, scale precision, 574552180098098577953261580846255154321171923170, scale precision,
    0, 512, 0, 512, ⟨-1387808116139030066510254079563973201258166331283, -1387808116139030066510254079563973201258164234130⟩, ⟨-1364499997524955039340789290290594459396613333134, -1364499997524955039340789290290594459396611235981⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1654217810898346064287549940535695499864388161209, 1688378377367966863591789527183587307558995694117⟩
def wholeBExp : DyadicInterval precision := ⟨145002208736712170093120437717821028539002837082, 151941593105828630131100607052587173587087617892⟩
def wholeBLog : DyadicInterval precision := ⟨138252015616296873326282854296881002765604659077, 144551459102907459974958207324412423028084186303⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨145002208736712170093120437717821029088758650970, scale precision, 151941593105828630131100607052587173037331804004, scale precision,
    0, 512, 0, 512, ⟨-3376756754735933727183579054367174620659073701232, -3376756754735933727183579054367174620659071604079⟩, ⟨-3308435621796692128575099881071390994440765012391, -3308435621796692128575099881071390994440762915238⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0068StableWitnesses

end


