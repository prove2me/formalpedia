-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0037PaddedInputs__5_q03
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0037PaddedInputs__5_q03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T01:11:44.071734+00:00
-- url     : https://prove2.me/theorems/1ea342a8-ccac-4e7d-b16e-e71490efc0a8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0037PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0038PaddedInputs, GeneralCK.Certificates.E8TAxisProd0039Padd…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0037PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0038PaddedInputs, GeneralCK.Certificates.E8TAxisProd0039PaddedInputs, GeneralCK.Certificates.E8TAxisProd0040PaddedInputs, GeneralCK.Certificates.E8TAxisProd0041PaddedInputs) (piece 4 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0037PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0038PaddedInputs, GeneralCK.Certificates.E8TAxisProd0039PaddedInputs, GeneralCK.Certificates.E8TAxisProd0040PaddedInputs, GeneralCK.Certificates.E8TAxisProd0041PaddedInputs) (piece 4 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0037PaddedInputs (+4 modules: GeneralCK.Certificates.E8TAxisProd0038PaddedInputs, GeneralCK.Certificates.E8TAxisProd0039PaddedInputs, GeneralCK.Certificates.E8TAxisProd0040PaddedInputs, GeneralCK.Certificates.E8TAxisProd0041PaddedInputs) (piece 4 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0037PaddedInputs (+4 modules: GeneralCK/Certificates/E8TAxisProd0038PaddedInputs, GeneralCK/Certificates/E8TAxisProd0039PaddedInputs, GeneralCK/Certificates/E8TAxisProd0040PaddedInputs, GeneralCK/Certificates/E8TAxisProd0041PaddedInputs) (piece 4 of 5).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0037PaddedInputs__5_q02

-- ===== source module GeneralCK.Certificates.E8TAxisProd0040PaddedInputs =====
section

/-! The eight original alpha intervals widened by 65536 precision-160 units
on each side. The retained exp/log witnesses are checked again for the
wider inputs. No original input or public inverse bracket is modified. -/

namespace GeneralCK.Certificates.E8TAxisProd0040PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0040StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978008272, 3165742448647063503620071141085134670978139345⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0040StableWitnesses.centerAInput with alpha := centerAAlpha }

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAInput.alpha)
      centerAInput.expNegTwo E8TAxisProd0040StableWitnesses.centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAInput.expNegTwo)
      centerAInput.logOnePlusExp E8TAxisProd0040StableWitnesses.centerALogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨202507445516537500012131595254672422594966997717, 202507445516537500012131595254672422594967128790⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0040StableWitnesses.centerBInput with alpha := centerBAlpha }

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBInput.alpha)
      centerBInput.expNegTwo E8TAxisProd0040StableWitnesses.centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBInput.expNegTwo)
      centerBInput.logOnePlusExp E8TAxisProd0040StableWitnesses.centerBLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨102288576562075948255867412728424315936308775087, 102288576562075948255867412728424315936308906160⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0040StableWitnesses.centerCInput with alpha := centerCAlpha }

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCInput.alpha)
      centerCInput.expNegTwo E8TAxisProd0040StableWitnesses.centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCInput.expNegTwo)
      centerCInput.logOnePlusExp E8TAxisProd0040StableWitnesses.centerCLogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨99105371957748756558358702025034649328540403453, 99105371957748756558358702025034649328540534526⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0040StableWitnesses.centerDInput with alpha := centerDAlpha }

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0040StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0040StableWitnesses.centerDLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858806245, 3798893981423257492988718450954299577395530717⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0040StableWitnesses.wholeAInput with alpha := wholeAAlpha }

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAInput.alpha)
      wholeAInput.expNegTwo E8TAxisProd0040StableWitnesses.wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAInput.expNegTwo)
      wholeAInput.logOnePlusExp E8TAxisProd0040StableWitnesses.wholeALogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨193778155013554683299889988710244792947683977547, 211253010738814688741513314259447908539070330428⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0040StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisProd0040StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisProd0040StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨97673285984124066128015298065358904033793436231, 106906222136452251800882146200705633326592887993⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0040StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisProd0040StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisProd0040StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨95127887983717436574352739463518235552733741458, 103084551358829778834915002511195342403115297212⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0040StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisProd0040StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisProd0040StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisProd0040PaddedInputs

end


