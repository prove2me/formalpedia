-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemPowIffCoeffMem
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemPowIffCoeffMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:56.345747+00:00
-- url     : https://prove2.me/theorems/06e4821f-e35d-4b82-8752-ca8db3730107
-- title:
--   Mem Pow Iff Coeff Mem
-- statement:
--   Definitions and structural lemmas for Mem Pow Iff Coeff Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MemPowIffCoeffMem.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
namespace GlobalTheory.IdealPowerCoefficients
open MvPowerSeries Finsupp
section SlopeTestRemainingChoices
variable {R : Type u_1} [CommRing R] {κ : Type u_2}
def coeffIdeal (I : Ideal R) (n : ℕ) : Ideal (MvPowerSeries κ R) where
  carrier := {f | ∀ e : κ →₀ ℕ, coeff e f ∈ I ^ (n - e.degree)}
  add_mem' := by
    intro f g hf hg e
    rw [map_add]
    exact Ideal.add_mem _ (hf e) (hg e)
  zero_mem' := by
    intro e
    simp
  smul_mem' := by
    intro c f hf e
    classical
    rw [smul_eq_mul, coeff_mul]
    refine Ideal.sum_mem _ (fun p hp => ?_)
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right ?_ (hf p.2))
    have : e.degree = p.1.degree + p.2.degree := by rw [← hp, map_add]
    omega
noncomputable def pick (d : κ →₀ ℕ) (k : κ) : κ :=
  if h : d.support.Nonempty then h.choose else k
noncomputable def cof [DecidableEq κ] (f : MvPowerSeries κ R) (k : κ) : MvPowerSeries κ R :=
  fun e => if pick (e + single k 1) k = k then coeff (e + single k 1) f else 0
end SlopeTestRemainingChoices
end GlobalTheory.IdealPowerCoefficients


