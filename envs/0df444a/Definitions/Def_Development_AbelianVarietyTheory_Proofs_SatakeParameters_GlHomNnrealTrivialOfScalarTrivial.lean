-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_GlHomNnrealTrivialOfScalarTrivial
-- name    : Development_AbelianVarietyTheory_Proofs_SatakeParameters_GlHomNnrealTrivialOfScalarTrivial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:39.329627+00:00
-- url     : https://prove2.me/theorems/f85c4195-4050-4af4-b7ea-0e367b4d7840
-- title:
--   Gl Hom Nnreal Trivial Of Scalar Trivial
-- statement:
--   Definitions and structural lemmas for Gl Hom Nnreal Trivial Of Scalar Trivial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/GlHomNnrealTrivialOfScalarTrivial.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
open Matrix
section HomTriv
variable {k : Type} [Field k] {N : ℕ}
lemma det_diagonal_ne_zero (d : Fin N → k) (hd : ∀ m, d m ≠ 0) :
    (diagonal d).det ≠ 0 := by
  rw [det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun m _ => hd m
end HomTriv
end GlobalTheory
namespace GlobalTheory
open Matrix
section HomTriv2
variable {k : Type} [Field k] {N : ℕ}
end HomTriv2
end GlobalTheory
namespace GlobalTheory
open Matrix
section HomTriv3
variable {k : Type} [Field k] {N : ℕ}
lemma mulSingle_unit_ne_zero (m : Fin N) (a : kˣ) (t : Fin N) :
    (Pi.mulSingle m (a : k) : Fin N → k) t ≠ 0 := by
  by_cases ht : t = m
  · rw [ht, Pi.mulSingle_eq_same]; exact a.ne_zero
  · rw [Pi.mulSingle_eq_of_ne ht]; exact one_ne_zero
noncomputable def elemDiag (m : Fin N) (a : kˣ) : GL (Fin N) k :=
  nonsingInvUnit (diagonal (Pi.mulSingle m (a : k)))
    (isUnit_iff_ne_zero.mpr (det_diagonal_ne_zero _ (mulSingle_unit_ne_zero m a)))
end HomTriv3
end GlobalTheory


