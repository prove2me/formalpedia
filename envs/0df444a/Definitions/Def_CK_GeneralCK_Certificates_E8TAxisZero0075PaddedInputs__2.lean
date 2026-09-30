-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0075PaddedInputs__2
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0075PaddedInputs__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T22:09:33.81488+00:00
-- url     : https://prove2.me/theorems/ebf5e54a-da2e-4fee-a5b3-afe3d1652bea
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0075PaddedInputs (+1 modules: GeneralCK.Certificates.E8TAxisZero0076PaddedInputs)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0075PaddedInputs (+1 modules: GeneralCK.Certificates.E8TAxisZero0076PaddedInputs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0075PaddedInputs (+1 modules: GeneralCK.Certificates.E8TAxisZero0076PaddedInputs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0075PaddedInputs (+1 modules: GeneralCK.Certificates.E8TAxisZero0076PaddedInputs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0075PaddedInputs (+1 modules: GeneralCK/Certificates/E8TAxisZero0076PaddedInputs).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0075StableWitnesses__2

-- ===== source module GeneralCK.Certificates.E8TAxisZero0075PaddedInputs =====
section

/-! The six positive alpha intervals widened by 16777216 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisZero0075PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisZero0075StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerBAlpha : DyadicInterval precision := ⟨1443004964744911456381893345181437087061279408011, 1443004964744911456381893345181437087061312962444⟩
def centerBInput : Inputs precision :=
  { E8TAxisZero0075StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisZero0075StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisZero0075StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨610749047126901767587564500529189331296601320865, 610749047126901767587564500529189331296634875298⟩
def centerCInput : Inputs precision :=
  { E8TAxisZero0075StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisZero0075StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisZero0075StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨610560585232978838677636124558316081121172228563, 610560585232978838677636124558316081121205782996⟩
def centerDInput : Inputs precision :=
  { E8TAxisZero0075StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisZero0075StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisZero0075StableWitnesses.centerDLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1426986055799192838512876476998623343810942122647, 1459105292769415311780651483550583481703733632670⟩
def wholeBInput : Inputs precision :=
  { E8TAxisZero0075StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisZero0075StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisZero0075StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨605149690269836019889894242842311313124278525621, 616363734361026223237742947818267087747687835381⟩
def wholeCInput : Inputs precision :=
  { E8TAxisZero0075StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisZero0075StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisZero0075StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨605149690269836019889894242842311313124278525621, 615985792935344704096715461380744242879805757766⟩
def wholeDInput : Inputs precision :=
  { E8TAxisZero0075StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisZero0075StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisZero0075StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisZero0075PaddedInputs

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0076PaddedInputs =====
section

/-! The six positive alpha intervals widened by 16777216 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisZero0076PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisZero0076StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerBAlpha : DyadicInterval precision := ⟨1411592916174558478281194275238796835225099118594, 1411592916174558478281194275238796835225132673027⟩
def centerBInput : Inputs precision :=
  { E8TAxisZero0076StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisZero0076StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisZero0076StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨599940457824606446097303393245383275788622732790, 599940457824606446097303393245383275788656287223⟩
def centerCInput : Inputs precision :=
  { E8TAxisZero0076StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisZero0076StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisZero0076StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨599752983055354003753543703993878049904113150977, 599752983055354003753543703993878049904146705410⟩
def centerDInput : Inputs precision :=
  { E8TAxisZero0076StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisZero0076StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisZero0076StableWitnesses.centerDLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1395736578421875585713064654815202821689827344268, 1427532357011884353116380646773615700350633230803⟩
def wholeBInput : Inputs precision :=
  { E8TAxisZero0076StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisZero0076StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisZero0076StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨594370338528145575810628189240163754488521504977, 605525639754255905015627397518030978757099236040⟩
def wholeCInput : Inputs precision :=
  { E8TAxisZero0076StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisZero0076StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisZero0076StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨594370338528145575810628189240163754488521504977, 605149690269836019889894242842311313124312080054⟩
def wholeDInput : Inputs precision :=
  { E8TAxisZero0076StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisZero0076StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisZero0076StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisZero0076PaddedInputs

end


