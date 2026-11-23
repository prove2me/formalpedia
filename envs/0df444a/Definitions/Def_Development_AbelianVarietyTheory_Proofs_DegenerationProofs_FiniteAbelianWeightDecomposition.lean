-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:05.907046+00:00
-- url     : https://prove2.me/theorems/b5560900-ac9a-4afd-b20b-4641d6d1f5cc
-- title:
--   Finite Abelian Weight Decomposition
-- statement:
--   Definitions and structural lemmas for Finite Abelian Weight Decomposition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteAbelianWeightDecomposition.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CharSumInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open TensorProduct
namespace GlobalTheory
namespace FiniteAbelianWeights
variable {o : Type} [CommRing o] {T : Type} [CommGroup T]
  {M : Type} [AddCommGroup M] [Module o M]
noncomputable def avg [Fintype T] (ρ : Representation o T M) (u : o) (c : T →* oˣ) : M →ₗ[o] M :=
  u • ∑ t : T, (((c t)⁻¹ : oˣ) : o) • ρ t
variable [Fintype T] (ρ : Representation o T M) (u : o)
end FiniteAbelianWeights
end GlobalTheory


