-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0132PaddedInputs__5_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0132PaddedInputs__5_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T00:16:43.66997+00:00
-- url     : https://prove2.me/theorems/43b816dc-6d2e-43d9-bf35-60d5d2acf507
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0132PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0133PaddedInputs, GeneralCK.Certificates.E8TAxisProd0134Padd…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0132PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0133PaddedInputs, GeneralCK.Certificates.E8TAxisProd0134PaddedInputs, GeneralCK.Certificates.E8TAxisProd0135PaddedInputs, GeneralCK.Certificates.E8TAxisProd0136PaddedInputs) (piece 2 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0132PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0133PaddedInputs, GeneralCK.Certificates.E8TAxisProd0134PaddedInputs, GeneralCK.Certificates.E8TAxisProd0135PaddedInputs, GeneralCK.Certificates.E8TAxisProd0136PaddedInputs) (piece 2 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0132PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0133PaddedInputs, GeneralCK.Certificates.E8TAxisProd0134PaddedInputs, GeneralCK.Certificates.E8TAxisProd0135PaddedInputs, GeneralCK.Certificates.E8TAxisProd0136PaddedInputs) (piece 2 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0132PaddedInputs (+4 modules: GeneralCK/Certificates/E8TAxisProd0133PaddedInputs, GeneralCK/Certificates/E8TAxisProd0134PaddedInputs, GeneralCK/Certificates/E8TAxisProd0135PaddedInputs, GeneralCK/Certificates/E8TAxisProd0136PaddedInputs) (piece 2 of 5).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0132PaddedInputs__5_q00

-- ===== source module GeneralCK.Certificates.E8TAxisProd0133PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0133PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0133StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨2216017656540843594568486214625237657012888708, 2216017656540843594568486214625237657013019781⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0133StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0133StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0133StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1048035918945644949049918457930746431148228220926, 1048035918945644949049918457930746431148228351999⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0133StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0133StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0133StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨470670639963713368888541291203335431626484404838, 470670639963713368888541291203335431626484535911⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0133StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0133StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0133StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨468197947567212351774406011872494977440423910132, 468197947567212351774406011872494977440424041205⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0133StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0133StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0133StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1899443256066344012630337314537754309230211955, 2532592299075639559542598685704412299858937318⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0133StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0133StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0133StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1024228741177052029276836569204746508120070930562, 1072112829804862998812524346003829014177160883205⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0133StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0133StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0133StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨461499381581860949131485878842069002795670596082, 479877859596601426615371866855283257178900208323⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0133StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0133StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0133StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨459387967798615484561738103898747303530785113893, 477040995173626483635311023942643508471660735576⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0133StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0133StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0133StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0133PaddedInputs

end


