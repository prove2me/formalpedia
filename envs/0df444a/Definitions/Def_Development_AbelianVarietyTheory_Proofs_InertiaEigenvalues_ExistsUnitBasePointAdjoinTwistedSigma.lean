-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitBasePointAdjoinTwistedSigma
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitBasePointAdjoinTwistedSigma
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:40.315084+00:00
-- url     : https://prove2.me/theorems/1ef23517-1b21-4664-a111-a60849c759ad
-- title:
--   Exists Unit Base Point Adjoin Twisted Sigma
-- statement:
--   Definitions and structural lemmas for Exists Unit Base Point Adjoin Twisted Sigma, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitBasePointAdjoinTwistedSigma.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UnitLemma.UnitBase
open GlobalTheory.UnitLemma Polynomial
def cO (K : UQ) : K.O →+* K.O where
  toFun x := Classical.choose (K.c_int x)
  map_one' := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int 1)]; simp
  map_mul' x y := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int (x * y)), map_mul, map_mul, map_mul,
      ← Classical.choose_spec (K.c_int x), ← Classical.choose_spec (K.c_int y)]
  map_zero' := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int 0)]; simp
  map_add' x y := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int (x + y)), map_add, map_add, map_add,
      ← Classical.choose_spec (K.c_int x), ← Classical.choose_spec (K.c_int y)]
end GlobalTheory.UnitLemma.UnitBase


