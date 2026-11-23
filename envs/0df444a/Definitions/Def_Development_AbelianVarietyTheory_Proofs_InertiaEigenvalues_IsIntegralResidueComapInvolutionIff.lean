-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralResidueComapInvolutionIff
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralResidueComapInvolutionIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:01:05.571482+00:00
-- url     : https://prove2.me/theorems/37f98c3e-d217-45a3-b841-b80e5ab1c6ac
-- title:
--   Is Integral Residue Comap Involution Iff
-- statement:
--   Definitions and structural lemmas for Is Integral Residue Comap Involution Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsIntegralResidueComapInvolutionIff.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
namespace GlobalTheory.UnitLemma.SwapInt
noncomputable def conjO (K : UQ) : K.O →+* K.O where
  toFun o := Classical.choose (K.c_int o)
  map_one' := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int 1)]; simp
  map_mul' a b := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int (a * b)), map_mul, map_mul, map_mul,
      ← Classical.choose_spec (K.c_int a), ← Classical.choose_spec (K.c_int b)]
  map_zero' := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int 0)]; simp
  map_add' a b := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int (a + b)), map_add, map_add, map_add,
      ← Classical.choose_spec (K.c_int a), ← Classical.choose_spec (K.c_int b)]
end GlobalTheory.UnitLemma.SwapInt


