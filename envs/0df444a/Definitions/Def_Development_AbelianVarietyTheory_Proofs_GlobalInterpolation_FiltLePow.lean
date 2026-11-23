-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiltLePow
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiltLePow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:53:50.858511+00:00
-- url     : https://prove2.me/theorems/1ccfa542-3536-49bf-858a-125ab2d13326
-- title:
--   Filt Le Pow
-- statement:
--   Definitions and structural lemmas for Filt Le Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FiltLePow.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
namespace GlobalTheory.FiltrationMultiplicative
section
variable {O : Type} [CommRing O] [IsLocalRing O]
variable (O) in

def Filt (σ : Type) (N : ℕ) : Set (MvPowerSeries σ O) :=
  {f | ∀ m : σ →₀ ℕ, coeff m f ∈ IsLocalRing.maximalIdeal O ^ (N - Finsupp.degree m)}
theorem filt_mul {σ : Type} {a b : ℕ} {f g : MvPowerSeries σ O}
    (hf : f ∈ Filt O σ a) (hg : g ∈ Filt O σ b) : f * g ∈ Filt O σ (a + b) := by
  classical
  intro m
  rw [coeff_mul]
  refine Ideal.sum_mem _ fun p hp => ?_
  have hpm : p.1 + p.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hd : Finsupp.degree p.1 + Finsupp.degree p.2 = Finsupp.degree m := by
    rw [← map_add, hpm]
  have := Ideal.mul_mem_mul (hf p.1) (hg p.2)
  rw [← pow_add] at this
  exact Ideal.pow_le_pow_right (by omega) this
theorem filt_zero {σ : Type} (f : MvPowerSeries σ O) : f ∈ Filt O σ 0 := by
  intro m
  simp
variable (O) in

def FiltIdeal (σ : Type) (N : ℕ) : Ideal (MvPowerSeries σ O) where
  carrier := Filt O σ N
  add_mem' := by
    intro f g hf hg m
    rw [map_add]
    exact Ideal.add_mem _ (hf m) (hg m)
  zero_mem' := by
    intro m
    simp
  smul_mem' := by
    intro c f hf
    have := filt_mul (filt_zero c) hf
    simpa using this
def IsFirst {a : ℕ} (m : Fin a →₀ ℕ) (i : Fin a) : Prop := m i ≠ 0 ∧ ∀ j, j < i → m j = 0
open Classical in

noncomputable def part {a : ℕ} (f : MvPowerSeries (Fin a) O) (i : Fin a) :
    MvPowerSeries (Fin a) O :=
  fun q => if IsFirst (q + Finsupp.single i 1) i then coeff (q + Finsupp.single i 1) f else 0
end
end GlobalTheory.FiltrationMultiplicative


