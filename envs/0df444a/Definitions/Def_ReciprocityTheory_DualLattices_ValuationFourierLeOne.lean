-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_ValuationFourierLeOne
-- name    : ReciprocityTheory_DualLattices_ValuationFourierLeOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:03.667966+00:00
-- url     : https://prove2.me/theorems/a3216008-0a73-4abd-9087-ec79f6f9479a
-- title:
--   Valuation Fourier Le One
-- statement:
--   Definitions and structural lemmas for Valuation Fourier Le One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationFourierLeOne.lean

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetEqOfSpanEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
namespace ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
def pairInt {X : Type} [Fintype X] (U : X → C) : Submodule R (X → C) where
  carrier := {F | ∃ r : R, algebraMap R C r = ∑ x, U x * F x}
  add_mem' := by
    rintro F G ⟨r, hr⟩ ⟨s, hs⟩
    exact ⟨r + s, by simp [hr, hs, mul_add, Finset.sum_add_distrib]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c F ⟨r, hr⟩
    refine ⟨c * r, ?_⟩
    simp only [map_mul, hr, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
def conv (u w : N → C) : N → C := fun c => ∑ a, u a * w (c - a)
def cpow (u : N → C) : ℕ → N → C
  | 0 => Pi.single 0 1
  | k + 1 => conv (cpow u k) u
end ReciprocityTheory.PGsh.L2


