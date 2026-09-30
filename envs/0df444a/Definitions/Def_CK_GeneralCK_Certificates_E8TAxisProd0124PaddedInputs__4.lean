-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0124PaddedInputs__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0124PaddedInputs__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T22:34:48.491574+00:00
-- url     : https://prove2.me/theorems/f7a12c7a-e8f5-48a5-9160-dc8622ed38de
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0124PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0125PaddedInputs, GeneralCK.Certificates.E8TAxisProd0126Padd…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0124PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0125PaddedInputs, GeneralCK.Certificates.E8TAxisProd0126PaddedInputs, GeneralCK.Certificates.E8TAxisProd0127PaddedInputs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0124PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0125PaddedInputs, GeneralCK.Certificates.E8TAxisProd0126PaddedInputs, GeneralCK.Certificates.E8TAxisProd0127PaddedInputs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0124PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0125PaddedInputs, GeneralCK.Certificates.E8TAxisProd0126PaddedInputs, GeneralCK.Certificates.E8TAxisProd0127PaddedInputs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0124PaddedInputs (+3 modules: GeneralCK/Certificates/E8TAxisProd0125PaddedInputs, GeneralCK/Certificates/E8TAxisProd0126PaddedInputs, GeneralCK/Certificates/E8TAxisProd0127PaddedInputs).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0123StableWitnesses__3
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0126StableWitnesses__3

-- ===== source module GeneralCK.Certificates.E8TAxisProd0124PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0124PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0124StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨3482318024844347500022322904444928295572329716, 3482318024844347500022322904444928295572460789⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0124StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0124StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0124StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨913545490769002202556189311216984808216475743992, 913545490769002202556189311216984808216475875065⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0124StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0124StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0124StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨419615890677429762820570771768227803313969468659, 419615890677429762820570771768227803313969599732⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0124StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0124StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0124StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨415811666137855580659299169097621045230774822172, 415811666137855580659299169097621045230774953245⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0124StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0124StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0124StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978008272, 3798893981423257492988718450954299577395530717⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0124StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0124StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0124StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨891252197999596923310947393377686358564274858673, 936091811347084158792453157371867683459498721433⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0124StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0124StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0124StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨410633201084391467870583087491309252328333373271, 428630511643972528454174557156597790389313990873⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0124StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0124StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0124StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨407186672849656374487538180028229486749867969559, 424465904280623337412236094991656409259795161586⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0124StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0124StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0124StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0124PaddedInputs

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0125PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0125PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0125StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨3482318024844347500022322904444928295572329716, 3482318024844347500022322904444928295572460789⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0125StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0125StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0125StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨870067865119628732220524935486271699505259783791, 870067865119628732220524935486271699505259914864⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0125StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0125StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0125StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨402369216265234178540924143771536001746223043149, 402369216265234178540924143771536001746223174222⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0125StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0125StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0125StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨398590295572446657843406049747194007801292686537, 398590295572446657843406049747194007801292817610⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0125StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0125StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0125StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978008272, 3798893981423257492988718450954299577395530717⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0125StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0125StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0125StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨848259152079208575771423146945791430608398951167, 892121725246422063302923523336912933495849510590⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0125StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0125StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0125StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨393445944234935066641568268781061070501103909073, 411323059691667375415976645368632603658563331688⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0125StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0125StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0125StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨390021907983024779256146395473341757167804125161, 407186672849656374487538180028229486749868100632⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0125StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0125StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0125StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0125PaddedInputs

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0126PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0126PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0126StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨2849167218250950044280193223065006085312195361, 2849167218250950044280193223065006085312326434⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0126StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0126StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0126StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨912666501870168905412732512241707366121460863231, 912666501870168905412732512241707366121460994304⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0126StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0126StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0126StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨418923789944494851264925608228606449078018364629, 418923789944494851264925608228606449078018495702⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0126StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0126StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0126StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨415811666137855580659299169097621045230774822172, 415811666137855580659299169097621045230774953245⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0126StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0126StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0126StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858806245, 3165742448647063503620071141085134670978139345⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0126StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0126StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0126StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨890383053906861011304981145854085152341339245394, 935202829477217853128384102912426720386644420207⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0126StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0126StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0126StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨409943527226177432185621695170239210992121453077, 427935929430565485324672558056114698713985848217⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0126StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0126StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0126StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨407186672849656374487538180028229486749867969559, 424465904280623337412236094991656409259795161586⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0126StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0126StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0126StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0126PaddedInputs

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0127PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0127PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0127StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨2849167218250950044280193223065006085312195361, 2849167218250950044280193223065006085312326434⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0127StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0127StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0127StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨869208030928855990633759988506863837488527156449, 869208030928855990633759988506863837488527287522⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0127StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0127StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0127StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨401681734325522873829587829920180725980264857535, 401681734325522873829587829920180725980264988608⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0127StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0127StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0127StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨398590295572446657843406049747194007801292686537, 398590295572446657843406049747194007801292817610⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0127StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0127StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0127StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858806245, 3165742448647063503620071141085134670978139345⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0127StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0127StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0127StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨847408844063416313893716486071623707147098640765, 891252197999596923310947393377686358564274989746⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0127StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0127StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0127StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨392760784790180292139123525495050640775660684835, 410633201084391467870583087491309252328333504344⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0127StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0127StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0127StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨390021907983024779256146395473341757167804125161, 407186672849656374487538180028229486749868100632⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0127StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0127StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0127StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0127PaddedInputs

end


