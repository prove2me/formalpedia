-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0014LStableWitnesses
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0014LStableWitnesses
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:42:11.947671+00:00
-- url     : https://prove2.me/theorems/13cfb578-970a-4dad-bc3e-498465aceb95
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0014LStableWitnesses` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0014LStableWitnesses` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0014LStableWitnesses` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0014LStableWitnesses (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0014LStableWitnesses.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisZero0014LStableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0014LStableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨31267200348904696457307982674063696220740721928, 31267200348904696457307982674063696220740721929⟩
def centerDExp : DyadicInterval precision := ⟨1400286211626589820319241330818486752934221908277, 1400286211626589820319241330818486755133245163830⟩
def centerDLog : DyadicInterval precision := ⟨982102976909830661899905108025873367774131782082, 982102976909830661899905108025873369973155037635⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1400286211626589820319241330818486753483977722165, scale precision, 1400286211626589820319241330818486754583489349942, scale precision,
    0, 128, 0, 128, ⟨-62534400697809392914615965348127393015271633153, -62534400697809392914615965348127393015269536000⟩, ⟨-62534400697809392914615965348127391867693351715, -62534400697809392914615965348127391867691254562⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨31900691842861117148641121052156610708022140335, 31900691842861117148641121052156610708022140336⟩
def centerCExp : DyadicInterval precision := ⟨1399072822616023578041193496129700238971405782963, 1399072822616023578041193496129700241170429038516⟩
def centerCLog : DyadicInterval precision := ⟨981483173424308358396608524356379725853646427545, 981483173424308358396608524356379728052669683098⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1399072822616023578041193496129700239521161596851, scale precision, 1399072822616023578041193496129700240620673224628, scale precision,
    0, 128, 0, 128, ⟨-63801383685722234297282242104313221990332106278, -63801383685722234297282242104313221990330009125⟩, ⟨-63801383685722234297282242104313220841758552219, -63801383685722234297282242104313220841756455066⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨63202231685683724521698212813643199826137726861, 63202231685683724521698212813643199826137726862⟩
def centerBExp : DyadicInterval precision := ⟨1340409256081553079614888826970387048119917900471, 1340409256081553079614888826970387050318941156024⟩
def centerBLog : DyadicInterval precision := ⟨951199663346770944854486307685196671136676105237, 951199663346770944854486307685196673335699360790⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1340409256081553079614888826970387048669673714359, scale precision, 1340409256081553079614888826970387049769185342136, scale precision,
    0, 128, 0, 128, ⟨-126404463371367449043396425627286400251697178099, -126404463371367449043396425627286400251695080946⟩, ⟨-126404463371367449043396425627286399052855826498, -126404463371367449043396425627286399052853729345⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨30079440410711523067074041860544926828153469388, 32455008327171042732967145611016798201694283383⟩
def wholeDExp : DyadicInterval precision := ⟨1398011947908555347946217879565997676739193473356, 1402564082875305177309105820725636622954765925773⟩
def wholeDLog : DyadicInterval precision := ⟨980941059342323278062008541570423721439995577604, 983265812352629886822137551849227704024579594240⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1398011947908555347946217879565997677288949287244, scale precision, 1402564082875305177309105820725636622405010111885, scale precision,
    0, 128, 0, 128, ⟨-64910016654342085465934291222033596978112187156, -64910016654342085465934291222033596978110090003⟩, ⟨-60158880821423046134148083721089853083450724046, -60158880821423046134148083721089853083448626893⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨30079440410711523067074041860544926828153469388, 33722058512096993179876642907656112194100953005⟩
def wholeCExp : DyadicInterval precision := ⟨1395590032716025290009393524680954277187454628194, 1402564082875305177309105820725636622954765925773⟩
def wholeCLog : DyadicInterval precision := ⟨979702690389748541410966442879284111953914387888, 983265812352629886822137551849227704024579594240⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1395590032716025290009393524680954277737210442082, scale precision, 1402564082875305177309105820725636622405010111885, scale precision,
    0, 128, 0, 128, ⟨-67444117024193986359753285815312224963922903349, -67444117024193986359753285815312224963920806196⟩, ⟨-60158880821423046134148083721089853083450724046, -60158880821423046134148083721089853083448626893⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨60188545809212462208685209789842065762909125936, 66216541218794318359769368435683091619506928348⟩
def wholeBExp : DyadicInterval precision := ⟨1334891524860804688449536572422174664416406754026, 1345948645971501065352234789101807194386932620126⟩
def wholeBLog : DyadicInterval precision := ⟨948318728069008013098756834967766541840282395334, 954086205956751408227534441305632532191714754037⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1334891524860804688449536572422174664966162567914, scale precision, 1345948645971501065352234789101807193837176806238, scale precision,
    0, 128, 0, 128, ⟨-132433082437588636719538736871366183840913267173, -132433082437588636719538736871366183840911170020⟩, ⟨-120377091618424924417370419579684130928865602004, -120377091618424924417370419579684130928863504851⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0014LStableWitnesses

end


