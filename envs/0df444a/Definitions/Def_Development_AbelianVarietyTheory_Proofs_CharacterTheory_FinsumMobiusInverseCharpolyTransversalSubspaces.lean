-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumMobiusInverseCharpolyTransversalSubspaces
-- name    : Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumMobiusInverseCharpolyTransversalSubspaces
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:13:32.179893+00:00
-- url     : https://prove2.me/theorems/968bf3c9-6948-434b-9fb9-d527662f9ff3
-- title:
--   Finsum Mobius Inverse Charpoly Transversal Subspaces
-- statement:
--   Definitions and structural lemmas for Finsum Mobius Inverse Charpoly Transversal Subspaces, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FinsumMobiusInverseCharpolyTransversalSubspaces.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyEqFinsumPsiStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
end GlobalTheory.CuspGL


