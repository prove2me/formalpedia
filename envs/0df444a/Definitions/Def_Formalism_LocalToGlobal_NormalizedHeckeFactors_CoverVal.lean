-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverVal
-- name    : Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverVal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:16:05.483343+00:00
-- url     : https://prove2.me/theorems/50e54c39-91ec-4bb9-8b6a-998fac756394
-- title:
--   Cover Val
-- statement:
--   Definitions and structural lemmas for Cover Val, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverVal.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.NCov
open Polynomial
section Val
variable {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ))
end Val
section DVR
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
end DVR
section Away
variable {R : Type*} [CommRing R]
def IntAway (q a : R) : Prop := ∃ N : ℕ, IsIntegral ℤ (q ^ N * a)
variable {q : R}
theorem IntAway.of_isIntegral {a : R} (ha : IsIntegral ℤ a) : IntAway q a := ⟨0, by simpa using ha⟩
theorem IntAway.add (hq : IsIntegral ℤ q) {a b : R} (ha : IntAway q a) (hb : IntAway q b) :
    IntAway q (a + b) := by
  obtain ⟨N, hN⟩ := ha
  obtain ⟨M, hM⟩ := hb
  refine ⟨N + M, ?_⟩
  rw [show q ^ (N + M) * (a + b) = q ^ M * (q ^ N * a) + q ^ N * (q ^ M * b) by ring]
  exact ((hq.pow M).mul hN).add ((hq.pow N).mul hM)
theorem IntAway.mul {a b : R} (ha : IntAway q a) (hb : IntAway q b) : IntAway q (a * b) := by
  obtain ⟨N, hN⟩ := ha
  obtain ⟨M, hM⟩ := hb
  refine ⟨N + M, ?_⟩
  rw [show q ^ (N + M) * (a * b) = (q ^ N * a) * (q ^ M * b) by ring]
  exact hN.mul hM
theorem IntAway.neg {a : R} (ha : IntAway q a) : IntAway q (-a) := by
  obtain ⟨N, hN⟩ := ha
  exact ⟨N, by rw [mul_neg]; exact hN.neg⟩
def intAwaySubring (hq : IsIntegral ℤ q) : Subring R where
  carrier := {a | IntAway q a}
  mul_mem' := fun ha hb => IntAway.mul ha hb
  one_mem' := IntAway.of_isIntegral isIntegral_one
  add_mem' := fun ha hb => IntAway.add hq ha hb
  zero_mem' := IntAway.of_isIntegral isIntegral_zero
  neg_mem' := fun ha => IntAway.neg ha
end Away
end Formalism.L2.NCov


