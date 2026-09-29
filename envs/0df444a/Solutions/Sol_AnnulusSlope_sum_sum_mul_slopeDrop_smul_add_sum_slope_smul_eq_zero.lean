-- Prove2me | solution 1 for AnnulusSlope.sum_sum_mul_slopeDrop_smul_add_sum_slope_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/4316fa58-956b-56e4-9283-d8c3871e7721

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AnnulusSlope_sum_sum_mul_slopeDrop_smul_add_sum_slope_smul_eq_zero

set_option autoImplicit false

universe u v

set_option autoImplicit false

open Finset BigOperators

namespace AnnulusSlope

def slope (g : ℕ → ℤ) (d : ℕ) : ℤ := g d - g (d - 1)

def drop (g : ℕ → ℤ) (d : ℕ) : ℤ := slope g d - slope g (d + 1)

theorem sum_mul_drop_eq (g : ℕ → ℤ) (e : ℕ) (he : 1 ≤ e) :
    ∑ d ∈ Ico 1 e, (d : ℤ) * drop g d = (g e - g 0) - (e : ℤ) * slope g e := by
  induction e, he using Nat.le_induction with
  | base => simp [slope]
  | succ n hn ih =>
      rw [Finset.sum_Ico_succ_top hn, ih]
      simp only [drop, slope, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      ring

theorem lattice_identity {S : Type*} [Fintype S] {M : Type*} [AddCommGroup M]
    (coord : S → M) (v : M) (e : S → ℕ) (he : ∀ s, 1 ≤ e s)
    (hv : ∀ s, (e s : ℤ) • coord s = v) (hsum : ∑ s, coord s = 0)
    (g : S → ℕ → ℤ) (δ : ℤ) (hδ : ∀ s, g s (e s) - g s 0 = δ) :
    ∑ s, (∑ d ∈ Ico 1 (e s), (d : ℤ) * drop (g s) d) • coord s + (∑ s, slope (g s) (e s)) • v = 0 := by
  have h1 : ∀ s, (∑ d ∈ Ico 1 (e s), (d : ℤ) * drop (g s) d) • coord s =
      δ • coord s - slope (g s) (e s) • v := by
    intro s
    rw [sum_mul_drop_eq (g s) (e s) (he s), hδ, sub_smul, mul_comm, ← smul_smul, hv]
  simp_rw [h1]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, hsum, smul_zero, zero_sub, Finset.sum_smul, neg_add_cancel]

end AnnulusSlope

open Finset BigOperators in
theorem solution
    {S : Type u} [Fintype S] {M : Type v} [AddCommGroup M]
    (coord : S → M) (v : M) (e : S → ℕ) (he : ∀ s, 1 ≤ e s)
    (hv : ∀ s, (e s : ℤ) • coord s = v) (hsum : ∑ s, coord s = 0)
    (g : S → ℕ → ℤ) (δ : ℤ) (hδ : ∀ s, g s (e s) - g s 0 = δ) :
    ∑ s, (∑ d ∈ Finset.Ico 1 (e s),
        (d : ℤ) * ((g s d - g s (d - 1)) - (g s (d + 1) - g s d))) • coord s +
      (∑ s, (g s (e s) - g s (e s - 1))) • v = 0 :=
  AnnulusSlope.lattice_identity coord v e he hv hsum g δ hδ

end S_AnnulusSlope_sum_sum_mul_slopeDrop_smul_add_sum_slope_smul_eq_zero
end P2MW
export P2MW.S_AnnulusSlope_sum_sum_mul_slopeDrop_smul_add_sum_slope_smul_eq_zero (solution)
