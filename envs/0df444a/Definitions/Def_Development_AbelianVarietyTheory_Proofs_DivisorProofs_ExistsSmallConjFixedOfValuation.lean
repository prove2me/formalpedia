-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmallConjFixedOfValuation
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmallConjFixedOfValuation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:01:03.780631+00:00
-- url     : https://prove2.me/theorems/eee02b21-fc7a-4347-a994-83f3cb0f58d5
-- title:
--   Exists Small Conj Fixed Of Valuation
-- statement:
--   Definitions and structural lemmas for Exists Small Conj Fixed Of Valuation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmallConjFixedOfValuation.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
namespace GlobalTheory.UnitLemma
noncomputable def UQ.cInt (K : UQ) : K.O ≃+* K.O :=
  let f := algebraMap K.O K.E
  have hf : Function.Injective f := IsFractionRing.injective K.O K.E
  let d : K.O → K.O := fun x => Classical.choose (K.c_int x)
  have hd : ∀ x, f (d x) = K.c (f x) := fun x => (Classical.choose_spec (K.c_int x)).symm
  have hdd : ∀ x, d (d x) = x := fun x => hf (by rw [hd, hd, K.c_c])
  { toFun := d
    invFun := d
    left_inv := hdd
    right_inv := hdd
    map_mul' := fun a b => hf (by rw [hd, map_mul, map_mul, map_mul, hd, hd])
    map_add' := fun a b => hf (by rw [hd, map_add, map_add, map_add, hd, hd]) }
end GlobalTheory.UnitLemma


