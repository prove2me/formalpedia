-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060StableWitnesses_part00
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0060StableWitnesses_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:37:10.896229+00:00
-- url     : https://prove2.me/theorems/565a604c-eb0d-4b09-9b7c-beb74e3cf540
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0060StableWitnesses (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0060StableWitnesses (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0060StableWitnesses (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0060StableWitnesses (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0060StableWitnesses (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0060StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨780097432743148472065827322615976914715321380242, 780097432743148472065827322615976914715321380243⟩
def centerDExp : DyadicInterval precision := ⟨502547949796029941349747428157944022560728851116, 502547949796029941349747428157944024759752106669⟩
def centerDLog : DyadicInterval precision := ⟨431938086327136521229594192068681255335127784667, 431938086327136521229594192068681257534151040220⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨502547949796029941349747428157944023110484665004, scale precision, 502547949796029941349747428157944024209996292781, scale precision,
    0, 512, 0, 512, ⟨-1560194865486296944131654645231953831029434576104, -1560194865486296944131654645231953831029432478951⟩, ⟨-1560194865486296944131654645231953827831853042018, -1560194865486296944131654645231953827831850944865⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨780302749375020803322004326544532573936944449017, 780302749375020803322004326544532573936944449018⟩
def centerCExp : DyadicInterval precision := ⟨502406770401010920638545397604251120352174633421, 502406770401010920638545397604251122551197888974⟩
def centerCLog : DyadicInterval precision := ⟨431833027201078351661688404062680421897483575976, 431833027201078351661688404062680424096506831529⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨502406770401010920638545397604251120901930447309, scale precision, 502406770401010920638545397604251122001442075086, scale precision,
    0, 512, 0, 512, ⟨-1560605498750041606644008653089065149473129983701, -1560605498750041606644008653089065149473127886548⟩, ⟨-1560605498750041606644008653089065146274649909522, -1560605498750041606644008653089065146274647812369⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1947202382862639918215810953415690042136342417126, 1947202382862639918215810953415690042136342417127⟩
def centerBExp : DyadicInterval precision := ⟨101754172713382642991149368428876123404542430222, 101754172713382642991149368428876125603565685775⟩
def centerBLog : DyadicInterval precision := ⟨98368235829451879881322711072959204906496372117, 98368235829451879881322711072959207105519627670⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨101754172713382642991149368428876123954298244110, scale precision, 101754172713382642991149368428876125053809871887, scale precision,
    0, 512, 0, 512, ⟨-3894404765725279836431621906831380092168863510776, -3894404765725279836431621906831380092168861413623⟩, ⟨-3894404765725279836431621906831380076376508254871, -3894404765725279836431621906831380076376506157718⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨774203834768265108571628471566363912561698867070, 786008954924549138888839394711577924172029077197⟩
def wholeDExp : DyadicInterval precision := ⟨498498909896069833132911032342083543572056459341, 506617451172271417683927781753795731632056364141⟩
def wholeDLog : DyadicInterval precision := ⟨428921977795889549222947679819138372580498428270, 434963177842048586751554818318029033914423871208⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨498498909896069833132911032342083544121812273229, scale precision, 506617451172271417683927781753795731082300550253, scale precision,
    0, 512, 0, 512, ⟨-1572017909849098277777678789423155849955836091904, -1572017909849098277777678789423155849955833994751⟩, ⟨-1548407669536530217143256943132727823537450607677, -1548407669536530217143256943132727823537448510524⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨774203834768265108571628471566363912561698867070, 786420860938926515611690405994600979308948226563⟩
def wholeCExp : DyadicInterval precision := ⟨498217997670246024363587701457700234897185519816, 506617451172271417683927781753795731632056364141⟩
def wholeCLog : DyadicInterval precision := ⟨428712496680093539525893343105067599121618685863, 434963177842048586751554818318029033914423871208⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨498217997670246024363587701457700235446941333704, scale precision, 506617451172271417683927781753795731082300550253, scale precision,
    0, 512, 0, 512, ⟨-1572841721877853031223380811989201960230583165181, -1572841721877853031223380811989201960230581068028⟩, ⟨-1548407669536530217143256943132727823537450607677, -1548407669536530217143256943132727823537448510524⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide


end GeneralCK.Certificates.E8TAxisZero0060StableWitnesses


