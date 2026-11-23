-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUnitaryConjSplitLatticeOfLocal
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUnitaryConjSplitLatticeOfLocal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:59:59.587458+00:00
-- url     : https://prove2.me/theorems/1ca5eb6d-cbec-4ba5-8f17-b7a8fcfeeee6
-- title:
--   Exists Unitary Conj Split Lattice Of Local
-- statement:
--   Definitions and structural lemmas for Exists Unitary Conj Split Lattice Of Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUnitaryConjSplitLatticeOfLocal.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryTransvectionSubmonoidAdjustIntegralAway
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryEqQuasiReflectionMulTransvections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryTransvectionSubmonoidNormalDetOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
namespace GlobalTheory.UTrans
def awayLoc {V : Type} [AddCommGroup V] (L : AddSubgroup V) (b : ℕ) : AddSubgroup V where
  carrier := {v | ∃ K : ℕ, K.Coprime b ∧ K • v ∈ L}
  zero_mem' := ⟨1, by simp, by simp⟩
  add_mem' := by
    rintro v w ⟨K, hK, hv⟩ ⟨K', hK', hw⟩
    refine ⟨K * K', Nat.Coprime.mul_left hK hK', ?_⟩
    have : (K * K') • (v + w) = K' • K • v + K • K' • w := by module
    rw [this]
    exact add_mem (nsmul_mem hv _) (nsmul_mem hw _)
  neg_mem' := by
    rintro v ⟨K, hK, hv⟩
    exact ⟨K, hK, by simpa using hv⟩
end GlobalTheory.UTrans


