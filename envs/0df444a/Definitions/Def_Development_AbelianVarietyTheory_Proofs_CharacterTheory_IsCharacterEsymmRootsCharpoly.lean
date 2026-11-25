-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterEsymmRootsCharpoly
-- name    : Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterEsymmRootsCharpoly
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T01:00:01.242353+00:00
-- url     : https://prove2.me/theorems/63da052a-bf84-4d0e-adbc-a300db799cc1
-- title:
--   Is Character Esymm Roots Charpoly
-- statement:
--   Definitions and structural lemmas for Is Character Esymm Roots Charpoly, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterEsymmRootsCharpoly.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Theorems.Thm_GlobalTheory_IsLogBounded_compoundMatrix
import Theorems.Thm_GlobalTheory_compoundMatrix_mul
import Theorems.Thm_GlobalTheory_compoundMatrix_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI
def compoundRep {G : Type} [Group G] {n : ℕ} (j : ℕ) (ρ : G →* GL (Fin n) ℂ) :
    Representation ℂ G (Set.powersetCard (Fin n) j → ℂ) where
  toFun g := Matrix.toLin' (GlobalTheory.compoundMatrix j (ρ g : Matrix (Fin n) (Fin n) ℂ))
  map_one' := by
    rw [map_one, Units.val_one, GlobalTheory.compoundMatrix_one, Matrix.toLin'_one]; rfl
  map_mul' a b := by
    rw [map_mul, Units.val_mul, GlobalTheory.compoundMatrix_mul, Matrix.toLin'_mul]; rfl
end GlobalTheory.BI


