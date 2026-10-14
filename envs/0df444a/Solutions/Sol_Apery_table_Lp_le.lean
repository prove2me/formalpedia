-- Prove2me | solution 1 for Apery.table_Lp_le
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T18:40:18.943056+00:00
-- url     : https://prove2.me/submissions/21b55fdb-9d26-4dc2-b4e6-3cb42baf6710

/-
# The inner bound in continuous form (source `Apery/Growth/TablePrime.lean`)

Proves the platform theorem `Apery.table_Lp_le` from `Apery.inner_Lp_le`,
`Apery.class_sum_approx` and `layer_eq`. Port of mo271/Zeta5 @
7fe736760f4b96bfdb4334b68e3b3124ecbe10b0.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourcePrimeSum
import Definitions.Def_Zeta5_SourceArith
import Definitions.Def_Zeta5_SourceNorm
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourceGrowthErrors
import Theorems.Thm_Apery_class_sum_approx
import Theorems.Thm_Apery_inner_Lp_le

set_option autoImplicit false

section Port0
/-!
# The inner bound in continuous form (source `Apery/Growth/TablePrime.lean`)

This file proves the platform theorem `Apery.table_Lp_le`:

`-L_p ≤ p·E_in(K/p, k) + Ctab n p k` for `k` in the admissible window,

from the discrete form `Apery.inner_Lp_le`, the class-sum approximation
`Apery.class_sum_approx`, the closed layer form `layer_eq` and the floor/fractional-part
computations. Faithful port of mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Finset

namespace Apery

lemma layer_eq {p : ℕ} (hp : 0 < p) (h : ℕ) :
    layer p 1000 h = (p : ℝ) * Jc ((h : ℝ) / p) := by
  unfold layer Jc
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [mul_max_of_nonneg _ _ hpR.le, mul_zero, mul_sub, mul_div_cancel₀ _ hpR.ne']
  congr 1; ring

variable {p : ℕ} [hp : Fact p.Prime]

section
variable {n : ℕ} (hn : 33 ≤ n) (hodd : 2 * (p / 2) + 1 = p) (hp7 : 7 ≤ p)
  (hsmall : ¬ p * Mcut ≤ 40 * n) (hin : 3 * p ≤ 40 * n) (hsq : 2 * (40 * n) < p ^ 2)
  (hdeg : 5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 < p ^ 2)

set_option maxHeartbeats 1000000 in
include hn hodd hp7 hsmall hin hsq hdeg in
/-- **The inner bound in continuous form.** -/
theorem table_Lp_le (k : ℤ) (hk1 : kloI n p ≤ k) (hk2 : k ≤ ktopI n p) :
    -(Lp n p : ℝ) ≤ (p : ℝ) * Ein (40 * n / p) k + Ctab n p k := by
  have hp0 : 0 < p := by omega
  have hpR0 : (0 : ℝ) < p := by exact_mod_cast hp0
  have main := inner_Lp_le hn hodd hp7 hsmall hin hsq hdeg k hk1 hk2
  -- the floors and fractional parts
  have hx : (40 * n / p : ℝ) = ((40 * n : ℕ) : ℝ) / (p : ℕ) := by push_cast; ring
  have hfl : ⌊(40 * n / p : ℝ)⌋₊ = 40 * n / p := by rw [hx, Nat.floor_div_eq_div]
  have hfl' : ⌊(3 : ℝ) / 40 * (40 * n / p)⌋₊ = 3 * n / p := by
    rw [show (3 : ℝ) / 40 * (40 * n / p) = ((3 * n : ℕ) : ℝ) / (p : ℕ) by push_cast; ring,
      Nat.floor_div_eq_div]
  have hfK : Int.fract ((40 * n / p : ℝ)) = ((40 * n % p : ℕ) : ℝ) / p := by
    rw [hx]; exact Int.fract_div_natCast_eq_div_natCast_mod
  have hfN : Int.fract ((3 : ℝ) / 40 * (40 * n / p)) = ((3 * n % p : ℕ) : ℝ) / p := by
    rw [show (3 : ℝ) / 40 * (40 * n / p) = ((3 * n : ℕ) : ℝ) / (p : ℕ) by push_cast; ring]
    exact Int.fract_div_natCast_eq_div_natCast_mod
  -- the class sum
  have hcs := class_sum_approx hodd (Nat.mod_lt (40 * n) hp0) (Nat.mod_lt (3 * n) hp0)
    (hIn n p k)
  have hb : ∀ i j, bcoef (fun a => bcoef (fun b => hIn n p k a b) j) i =
      bIn (40 * n / p) (3 * n / p) k i j := fun i j => rfl
  simp only [hb] at hcs
  rw [abs_le] at hcs
  -- the layer term
  have hlay : 2 * layer p 1000 (37 * n : ℕ) = (p : ℝ) * (2 * Jc (37 / 40 * (40 * n / p))) := by
    rw [layer_eq hp0]
    have : ((37 * n : ℕ) : ℝ) / p = 37 / 40 * (40 * n / p) := by push_cast; ring
    rw [this]; ring
  unfold Ein Ctab
  rw [hfl, hfl', hfK, hfN]
  have e1 : ((37 * n : ℕ) : ℝ) = (p : ℝ) * (37 / 40 * (40 * n / p)) := by
    push_cast; field_simp
  rw [hlay] at main
  rw [e1] at main
  have hE : ((k - kloI n p : ℤ) : ℝ) * (L0I n p : ℝ) ≤ ((ktopI n p - kloI n p : ℤ) : ℝ) * (L0I n p : ℝ) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast (show k - kloI n p ≤ ktopI n p - kloI n p by omega)
  nlinarith [hcs.2, hE]

end

end Apery

#check @Apery.table_Lp_le
end Port0


open Finset in
/-- The platform target `Apery.table_Lp_le`, restated at top level as `solution`. -/
theorem solution {p : ℕ} [hp : Fact p.Prime] {n : ℕ} (hn : 33 ≤ n)
    (hodd : 2 * (p / 2) + 1 = p) (hp7 : 7 ≤ p) (hsmall : ¬ p * Apery.Mcut ≤ 40 * n)
    (hin : 3 * p ≤ 40 * n) (hsq : 2 * (40 * n) < p ^ 2)
    (hdeg : 5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 < p ^ 2)
    (k : ℤ) (hk1 : Apery.kloI n p ≤ k) (hk2 : k ≤ Apery.ktopI n p) :
    -(Apery.Lp n p : ℝ) ≤ (p : ℝ) * Apery.Ein (40 * n / p) k + Apery.Ctab n p k :=
  Apery.table_Lp_le hn hodd hp7 hsmall hin hsq hdeg k hk1 hk2
