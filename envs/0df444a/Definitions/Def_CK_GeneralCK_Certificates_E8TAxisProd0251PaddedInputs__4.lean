-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0251PaddedInputs__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0251PaddedInputs__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T03:48:46.796672+00:00
-- url     : https://prove2.me/theorems/33df17b5-b73b-4ef3-9a0a-d2d7a5682757
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0251PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0252PaddedInputs, GeneralCK.Certificates.E8TAxisProd0253Padd…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0251PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0252PaddedInputs, GeneralCK.Certificates.E8TAxisProd0253PaddedInputs, GeneralCK.Certificates.E8TAxisProd0254PaddedInputs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0251PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0252PaddedInputs, GeneralCK.Certificates.E8TAxisProd0253PaddedInputs, GeneralCK.Certificates.E8TAxisProd0254PaddedInputs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0251PaddedInputs (+3 modules: GeneralCK.Certificates.E8TAxisProd0252PaddedInputs, GeneralCK.Certificates.E8TAxisProd0253PaddedInputs, GeneralCK.Certificates.E8TAxisProd0254PaddedInputs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0251PaddedInputs (+3 modules: GeneralCK/Certificates/E8TAxisProd0252PaddedInputs, GeneralCK/Certificates/E8TAxisProd0253PaddedInputs, GeneralCK/Certificates/E8TAxisProd0254PaddedInputs).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0250StableWitnesses__4
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0254StableWitnesses__3

-- ===== source module GeneralCK.Certificates.E8TAxisProd0251PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0251PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0251StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨2690879721921964209596752456793030551114694077, 2690879721921964209596752456793030551114825150⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0251StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0251StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0251StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2239508420437104764284119736608677703687167999485, 2239508420437104764284119736608677703687168130558⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0251StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0251StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0251StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨880577469555873053778656908938965968543606987389, 880577469555873053778656908938965968543607118462⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0251StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0251StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0251StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨876906193579724784222253173988686333103955999176, 876906193579724784222253173988686333103956130249⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0251StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0251StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0251StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858806245, 2849167218250950044280193223065006085312326434⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0251StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0251StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0251StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2220989959146203942278856072072081120998919819973, 2258054091262509235013941793937008873212629377120⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0251StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0251StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0251StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨874157230747478651127939648387624030242740161947, 887018735049816900191077495365469056175113601153⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0251StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0251StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0251StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨870712988176454679833831807012927217752922878482, 883118980747789020882084464779538700246874470803⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0251StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0251StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0251StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0251PaddedInputs

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0252PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0252PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0252StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨3007454792385135386557447160398116569795916971, 3007454792385135386557447160398116569796048044⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0252StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0252StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0252StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2203763072011470146489582452753053373482105816761, 2203763072011470146489582452753053373482105947834⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0252StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0252StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0252StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨868617113497772692368686748854564557162355578594, 868617113497772692368686748854564557162355709667⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0252StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0252StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0252StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨864539270161105163740168296694370154034029282629, 864539270161105163740168296694370154034029413702⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0252StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0252StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0252StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2849167218250950044280193223065006085312195361, 3165742448647063503620071141085134670978139345⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0252StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0252StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0252StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2185299997858007781513684444410996213977655759044, 2222255291856429851874220686980443631899353155002⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0252StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0252StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0252StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨862235822613332734442002484759373418279860363415, 875019236366843678144084161940470670675231471398⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0252StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0252StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0252StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨858384943750592238779991986336301839154815927780, 870712988176454679833831807012927217752923009555⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0252StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0252StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0252StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0252PaddedInputs

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0253PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0253PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0253StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨3007454792385135386557447160398116569795916971, 3007454792385135386557447160398116569796048044⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0253StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0253StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0253StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2167496778030749535375849116874054591809577306880, 2167496778030749535375849116874054591809577437953⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0253StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0253StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0253StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨856302210448687089229127087332001370695025874342, 856302210448687089229127087332001370695026005415⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0253StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0253StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0253StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨852249911794452062012049136358764955095133723948, 852249911794452062012049136358764955095133855021⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0253StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0253StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0253StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2849167218250950044280193223065006085312195361, 3165742448647063503620071141085134670978139345⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0253StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0253StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0253StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2149094032349808565141438601629983347811363669864, 2185930721759970506683951043565355111437476362894⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0253StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0253StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0253StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨849960879361055916238778446333942431649780147159, 862664165944678037906770610371578220863353434673⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0253StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0253StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0253StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨846134075813431409586727826645377644661771904234, 858384943750592238779991986336301839154816058853⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0253StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0253StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0253StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0253PaddedInputs

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0254PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0254PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0254StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨2690879721921964209596752456793030551114694077, 2690879721921964209596752456793030551114825150⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0254StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0254StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0254StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2203131368793057409381337232897591382076241278444, 2203131368793057409381337232897591382076241409517⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0254StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0254StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0254StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨868187467173751992471297993761205624547079531907, 868187467173751992471297993761205624547079662980⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0254StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0254StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0254StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨864539270161105163740168296694370154034029282629, 864539270161105163740168296694370154034029413702⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0254StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0254StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0254StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858806245, 2849167218250950044280193223065006085312326434⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0254StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0254StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0254StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2184669309228439526573711343006089816796651220448, 2221622609040950356192009939625428230446663976635⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0254StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0254StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0254StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨861807572949673468660518328224844520744745640750, 874588186260648773346854413637122018667374698659⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0254StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0254StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0254StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨858384943750592238779991986336301839154815927780, 870712988176454679833831807012927217752923009555⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0254StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0254StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0254StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0254PaddedInputs

end


