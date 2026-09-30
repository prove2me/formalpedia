-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0093LStableWitnesses
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0093LStableWitnesses
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:45:50.029233+00:00
-- url     : https://prove2.me/theorems/3fa30c38-02f2-44db-9ad9-5ac92379de17
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0093LStableWitnesses` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0093LStableWitnesses` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0093LStableWitnesses` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0093LStableWitnesses (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0093LStableWitnesses.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0093LStableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0093LStableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨949721161203312387564849132921065893757597830, 949721161203312387564849132921065893757597831⟩
def centerAExp : DyadicInterval precision := ⟨1459603428780171974367103696970164794154811336420, 1459603428780171974367103696970164796353834591973⟩
def centerALog : DyadicInterval precision := ⟨1012086326714990166522051059359330288660433386585, 1012086326714990166522051059359330290859456642138⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1459603428780171974367103696970164794704567150308, scale precision, 1459603428780171974367103696970164795804078778085, scale precision,
    0, 128, 0, 128, ⟨-1899442322406624775129698265842132337987013411, -1899442322406624775129698265842132337984916258⟩, ⟨-1899442322406624775129698265842131237045475062, -1899442322406624775129698265842131237043377909⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨147947977192305285151037266483750355395872960819, 147947977192305285151037266483750355395872960820⟩
def centerCExp : DyadicInterval precision := ⟨1193636104125204856193515609809341352181311235515, 1193636104125204856193515609809341354380334491068⟩
def centerCLog : DyadicInterval precision := ⟨872563402639052654175980727475644966542783894219, 872563402639052654175980727475644968741807149772⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1193636104125204856193515609809341352731067049403, scale precision, 1193636104125204856193515609809341353830578677180, scale precision,
    0, 128, 0, 128, ⟨-295895954384610570302074532967500711464874248583, -295895954384610570302074532967500711464872151430⟩, ⟨-295895954384610570302074532967500710118619691849, -295895954384610570302074532967500710118617594696⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨298435465575850061418406400238001510943089159635, 298435465575850061418406400238001510943089159636⟩
def centerBExp : DyadicInterval precision := ⟨971483263490538796532098524079893513274919110751, 971483263490538796532098524079893515473942366304⟩
def centerBLog : DyadicInterval precision := ⟨744860786713891993512603520293301662555029559329, 744860786713891993512603520293301664754052814882⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨971483263490538796532098524079893513824674924639, scale precision, 971483263490538796532098524079893514924186552416, scale precision,
    0, 128, 0, 128, ⟨-596870931151700122836812800476003022713233268131, -596870931151700122836812800476003022713231170978⟩, ⟨-596870931151700122836812800476003021059125467563, -596870931151700122836812800476003021059123370410⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨633147383168915695688804483341311756669124066, 1266295042977660303900587558721132456011189596⟩
def wholeAExp : DyadicInterval precision := ⟨1458971240300741788424025014233787498548709353580, 1460235890986607494244084883518378978984154367596⟩
def wholeALog : DyadicInterval precision := ⟨1011769992837296815097311935000023817181636979342, 1012402729061596953461092784027353939761000525628⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1458971240300741788424025014233787499098465167468, scale precision, 1460235890986607494244084883518378978434398553708, scale precision,
    0, 128, 0, 128, ⟨-2532590085955320607801175117442265462732722054, -2532590085955320607801175117442265462730624901⟩, ⟨-1266294766337831391377608966682622963106949258, -1266294766337831391377608966682622963104852105⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨143624889310919960230471164280159196827619120959, 152274025350693602568853898076835468511984896975⟩
def wholeCExp : DyadicInterval precision := ⟨1186590648121264655519234724293073078026798068284, 1200718528834184853391310342751497743292312020017⟩
def wholeCLog : DyadicInterval precision := ⟨868680127166861396265070107977234574165265067362, 876456682575976142298361162756131022378492315572⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1186590648121264655519234724293073078576553882172, scale precision, 1200718528834184853391310342751497742742556206129, scale precision,
    0, 128, 0, 128, ⟨-304548050701387205137707796153670937701094856104, -304548050701387205137707796153670937701092758951⟩, ⟨-287249778621839920460942328560318392986082445794, -287249778621839920460942328560318392986080348641⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨289821708815072720468221936650414567978851753460, 307071664425993428826262081180784357445038659394⟩
def wholeBExp : DyadicInterval precision := ⟨960069605044216067758791316721619524932751404449, 983002422228797412925137426354919001783949206612⟩
def wholeBLog : DyadicInterval precision := ⟨737988433917165373290026871067955246872246107010, 751764052223558962742893770839715829786720136548⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨960069605044216067758791316721619525482507218337, scale precision, 983002422228797412925137426354919001234193392724, scale precision,
    0, 128, 0, 128, ⟨-614143328851986857652524162361568715726964586767, -614143328851986857652524162361568715726962489614⟩, ⟨-579643417630145440936443873300829135140342355811, -579643417630145440936443873300829135140340258658⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0093LStableWitnesses

end


