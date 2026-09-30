-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0132PaddedInputs__5_q03
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0132PaddedInputs__5_q03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T00:32:55.066905+00:00
-- url     : https://prove2.me/theorems/deb3b8d8-82ac-4655-9c7b-ebee8d76f96d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0132PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0133PaddedInputs, GeneralCK.Certificates.E8TAxisProd0134Padd…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0132PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0133PaddedInputs, GeneralCK.Certificates.E8TAxisProd0134PaddedInputs, GeneralCK.Certificates.E8TAxisProd0135PaddedInputs, GeneralCK.Certificates.E8TAxisProd0136PaddedInputs) (piece 4 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0132PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0133PaddedInputs, GeneralCK.Certificates.E8TAxisProd0134PaddedInputs, GeneralCK.Certificates.E8TAxisProd0135PaddedInputs, GeneralCK.Certificates.E8TAxisProd0136PaddedInputs) (piece 4 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0132PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0133PaddedInputs, GeneralCK.Certificates.E8TAxisProd0134PaddedInputs, GeneralCK.Certificates.E8TAxisProd0135PaddedInputs, GeneralCK.Certificates.E8TAxisProd0136PaddedInputs) (piece 4 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0132PaddedInputs (+4 modules: GeneralCK/Certificates/E8TAxisProd0133PaddedInputs, GeneralCK/Certificates/E8TAxisProd0134PaddedInputs, GeneralCK/Certificates/E8TAxisProd0135PaddedInputs, GeneralCK/Certificates/E8TAxisProd0136PaddedInputs) (piece 4 of 5).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0132PaddedInputs__5_q02

-- ===== source module GeneralCK.Certificates.E8TAxisProd0135PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0135PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0135StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨1582869063071984205522252427078437298396856442, 1582869063071984205522252427078437298396987515⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0135StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0135StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0135StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1047097234846893185191241168818805273629517846092, 1047097234846893185191241168818805273629517977165⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0135StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0135StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0135StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨469963891056194552582472665051408868706991711639, 469963891056194552582472665051408868706991842712⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0135StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0135StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0135StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨468197947567212351774406011872494977440423910132, 468197947567212351774406011872494977440424041205⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0135StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0135StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0135StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1266295042977660303900587558721132456011124059, 1899443256066344012630337314537754309230343028⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0135StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0135StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0135StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1023300595444368493082805525999753225833125400426, 1071163533946626840883335333769298938372431760350⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0135StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0135StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0135StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨460795368920412028518162504643854518865778698691, 479168318693266819909468923991435055930292536236⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0135StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0135StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0135StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨459387967798615484561738103898747303530785113893, 477040995173626483635311023942643508471660735576⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0135StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0135StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0135StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0135PaddedInputs

end


