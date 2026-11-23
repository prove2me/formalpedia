-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PartialDerivativeExponent
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_PartialDerivativeExponent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:54.990953+00:00
-- url     : https://prove2.me/theorems/9e0d00f0-e876-4bdd-bc56-559905189c85
-- title:
--   Partial Derivative Exponent
-- statement:
--   Definitions and structural lemmas for Partial Derivative Exponent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PartialDerivativeExponent.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
open MvPowerSeries
variable {σ : Type}
def OnV {k : Type} [CommRing k] (V : Set σ) (f : MvPowerSeries σ k) : Prop :=
  ∀ e : σ →₀ ℕ, coeff e f ≠ 0 → ∀ i ∈ e.support, i ∈ V
def subV (k : Type) [CommRing k] (V : Set σ) : Subalgebra k (MvPowerSeries σ k) where
  carrier := {f | OnV V f}
  mul_mem' := by
    classical
    intro f g hf hg
    change OnV V f at hf
    change OnV V g at hg
    change OnV V (f * g)
    intro e he i hi
    rw [coeff_mul] at he
    obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [← hp] at hi
    rcases Finset.mem_union.1 (Finsupp.support_add hi) with h | h
    · exact hf _ (left_ne_zero_of_mul hne) i h
    · exact hg _ (right_ne_zero_of_mul hne) i h
  add_mem' := by
    intro f g hf hg
    change OnV V f at hf
    change OnV V g at hg
    change OnV V (f + g)
    intro e he i hi
    rw [map_add] at he
    by_cases h : coeff e f = 0
    · rw [h, zero_add] at he
      exact hg e he i hi
    · exact hf e h i hi
  algebraMap_mem' := by
    intro r
    change OnV V _
    intro e he i hi
    classical
    have e0 : e = 0 := by
      by_contra hne
      apply he
      simp [MvPowerSeries.algebraMap_apply, coeff_C, hne]
    subst e0
    simp at hi
variable {k : Type} [CommRing k]
variable [Algebra ℚ k]
end Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent


