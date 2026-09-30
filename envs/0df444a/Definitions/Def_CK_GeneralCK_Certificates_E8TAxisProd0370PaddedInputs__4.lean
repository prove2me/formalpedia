-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0370PaddedInputs__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0370PaddedInputs__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T03:43:38.06785+00:00
-- url     : https://prove2.me/theorems/0047349e-629d-4b19-bbcf-d4184cbf77d8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0370PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0371PaddedInputs, GeneralCK.Certificates.E8TAxisProd0372Padd…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0370PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0371PaddedInputs, GeneralCK.Certificates.E8TAxisProd0372PaddedInputs, GeneralCK.Certificates.E8TAxisProd0373PaddedInputs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0370PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0371PaddedInputs, GeneralCK.Certificates.E8TAxisProd0372PaddedInputs, GeneralCK.Certificates.E8TAxisProd0373PaddedInputs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0370PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0371PaddedInputs, GeneralCK.Certificates.E8TAxisProd0372PaddedInputs, GeneralCK.Certificates.E8TAxisProd0373PaddedInputs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0370PaddedInputs (+3 modules: GeneralCK/Certificates/E8TAxisProd0371PaddedInputs, GeneralCK/Certificates/E8TAxisProd0372PaddedInputs, GeneralCK/Certificates/E8TAxisProd0373PaddedInputs).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0368StableWitnesses__3
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0371StableWitnesses__4

-- ===== source module GeneralCK.Certificates.E8TAxisProd0370PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0370PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0370StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨791434261379870553054051158387221052156972690, 791434261379870553054051158387221052157103763⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0370StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0370StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0370StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2272179104174789024264049982992992854235275380311, 2272179104174789024264049982992992854235275511384⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0370StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0370StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0370StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨890437364192039962805983563859612299580840755675, 890437364192039962805983563859612299580840886748⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0370StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0370StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0370StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨889351442612263296687940979624415955523303291316, 889351442612263296687940979624415955523303422389⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0370StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0370StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0370StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨633147383168915695688804483341311756669058530, 949721161203312387564849132921065893757663367⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0370StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0370StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0370StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2253613386607212014265448009956055049263997402547, 2290770337055073476941082054148223152539229280042⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0370StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0370StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0370StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨883984925531161516812957497582224991376607103597, 896910984800584647324265506680046400576443343336⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0370StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0370StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0370StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨883118980747789020882084464779538700246874339730, 895603670620266646532188138393358736598408129174⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0370StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0370StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0370StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0370PaddedInputs

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0371PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0371PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0371StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨791434261379870553054051158387221052156972690, 791434261379870553054051158387221052157103763⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0371StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0371StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0371StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2235707511266571263602811989954015911090043250840, 2235707511266571263602811989954015911090043381913⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0371StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0371StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0371StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨877985269044036004613849530214564711171289992897, 877985269044036004613849530214564711171290123970⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0371StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0371StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0371StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨876906193579724784222253173988686333103955999176, 876906193579724784222253173988686333103956130249⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0371StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0371StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0371StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨633147383168915695688804483341311756669058530, 949721161203312387564849132921065893757663367⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0371StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0371StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0371StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2217194753359098092659874061683458584647200855400, 2254247680487392150548432768341741895440974409904⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0371StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0371StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0371StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨871573482342784998286909426230622712841626354984, 884418040819471962986432007479179994034843282827⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0371StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0371StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0371StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨870712988176454679833831807012927217752922878482, 883118980747789020882084464779538700246874470803⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0371StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0371StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0371StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0371PaddedInputs

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0372PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0372PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0372StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨1108008086961741616166050582946352244611229637, 1108008086961741616166050582946352244611360710⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0372StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0372StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0372StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2199973365094012093526255090073266749657963026264, 2199973365094012093526255090073266749657963157337⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0372StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0372StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0372StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨866040646673123429325711732787629329102573950700, 866040646673123429325711732787629329102574081773⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0372StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0372StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0372StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨864539270161105163740168296694370154034029282629, 864539270161105163740168296694370154034029413702⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0372StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0372StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0372StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨949721161203312387564849132921065893757532294, 1266295042977660303900587558721132456011255132⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0372StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0372StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0372StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2181516396628795029617879208831763354977444188498, 2218459689576389178421868795077660563662849989975⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0372StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0372StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0372StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨859667728502263967555650964721109420572533184290, 872434353989953295608084315149513908246795256316⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0372StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0372StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0372StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨858384943750592238779991986336301839154815927780, 870712988176454679833831807012927217752923009555⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0372StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0372StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0372StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0372PaddedInputs

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0373PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0373PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0373StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨1108008086961741616166050582946352244611229637, 1108008086961741616166050582946352244611360710⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0373StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0373StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0373StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2163719277504426508991730451778428615015575401296, 2163719277504426508991730451778428615015575532369⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0373StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0373StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0373StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨853741887007587829040784011798955937251135310678, 853741887007587829040784011798955937251135441751⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0373StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0373StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0373StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨852249911794452062012049136358764955095133723948, 852249911794452062012049136358764955095133855021⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0373StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0373StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0373StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨949721161203312387564849132921065893757532294, 1266295042977660303900587558721132456011255132⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0373StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0373StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0373StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2145323063632182011460624595069210509308471503347, 2182146908269555204328257309661848741942720834126⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0373StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0373StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0373StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨847408844063416313893716486071623707147098640765, 860095510318109513278476642346114951551390488274⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0373StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0373StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0373StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨846134075813431409586727826645377644661771904234, 858384943750592238779991986336301839154816058853⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0373StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0373StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0373StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0373PaddedInputs

end


