-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MaximalIdealLeFiltOne
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MaximalIdealLeFiltOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:36.352016+00:00
-- url     : https://prove2.me/theorems/689bc1b4-0818-41b1-921a-0f953c697335
-- title:
--   Maximal Ideal Le Filt One
-- statement:
--   Definitions and structural lemmas for Maximal Ideal Le Filt One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MaximalIdealLeFiltOne.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.MaximalIdealFiltration
open MvPowerSeries
variable {O : Type} [CommRing O] [IsLocalRing O] {a : ℕ}
def filt (N : ℕ) : Ideal (MvPowerSeries (Fin a) O) where
  carrier := {f | ∀ m : Fin a →₀ ℕ, coeff m f ∈ IsLocalRing.maximalIdeal O ^ (N - m.degree)}
  add_mem' := by
    intro f g hf hg m
    simp only [Set.mem_setOf_eq, map_add] at *
    exact Ideal.add_mem _ (hf m) (hg m)
  zero_mem' := by
    intro m
    simp
  smul_mem' := by
    intro c f hf m
    simp only [Set.mem_setOf_eq, smul_eq_mul, coeff_mul] at *
    refine Ideal.sum_mem _ fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    refine Ideal.mul_mem_left _ _ ?_
    refine Ideal.pow_le_pow_right ?_ (hf p.2)
    have : p.2.degree ≤ m.degree := by
      rw [← hp, map_add]; omega
    omega
end GlobalTheory.MaximalIdealFiltration


