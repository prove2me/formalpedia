-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIntegralRatioRingIffMemAdjoin
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIntegralRatioRingIffMemAdjoin
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T12:58:43.316329+00:00
-- url     : https://prove2.me/theorems/b5340e79-d173-5770-a0b1-84d977239eea
-- title:
--   Is Integral Ratio Ring Iff Mem Adjoin
-- statement:
--   Definitions and structural lemmas for Is Integral Ratio Ring Iff Mem Adjoin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIntegralRatioRingIffMemAdjoin.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TupleCone
open Polynomial
section Saturation
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
def saturation (x : B) (hx : IsIntegral A x) : Subring B where
  carrier := {b | ∃ n : ℕ, IsIntegral A (b * x ^ n)}
  zero_mem' := ⟨0, by simpa using isIntegral_zero⟩
  one_mem' := ⟨0, by simpa using isIntegral_one⟩
  add_mem' := by
    rintro a b ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have := (hn.mul (hx.pow m)).add (hm.mul (hx.pow n))
    convert this using 1
    ring
  mul_mem' := by
    rintro a b ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have := hn.mul hm
    convert this using 1
    ring
  neg_mem' := by
    rintro a ⟨n, hn⟩
    exact ⟨n, by simpa using hn.neg⟩
end Saturation
variable (o : Type*) [CommRing o] {L : Type*} [Field L] [Algebra o L] {σ : Type*} (t : σ → L)
def cone : Subalgebra o L[X] := Algebra.adjoin o (Set.range fun s => C (t s) * X)
def ratioRing (i : σ) : Subalgebra o L := Algebra.adjoin o (Set.range fun k => t k / t i)
def piece (n : ℕ) : Submodule o L where
  carrier := {a | IsIntegral (cone o t) (C a * X ^ n)}
  zero_mem' := by simpa using isIntegral_zero
  add_mem' := by
    intro a b ha hb
    simpa [add_mul] using IsIntegral.add ha hb
  smul_mem' := by
    intro c a ha
    have h := (isIntegral_algebraMap (R := cone o t) (A := L[X]) (x := algebraMap o _ c)).mul ha
    change IsIntegral _ _
    rw [Algebra.smul_def, map_mul, mul_assoc]
    exact h
variable {o t}
def spread (L : Type*) [CommRing L] : L[X] →+* L[X][X] :=
  eval₂RingHom (C.comp C) (C X * X)
section Finite
variable (o t) [IsDedekindDomain o] [CharZero L] [Algebra.EssFiniteType o L] [Finite σ]
end Finite
end GlobalTheory.TupleCone


