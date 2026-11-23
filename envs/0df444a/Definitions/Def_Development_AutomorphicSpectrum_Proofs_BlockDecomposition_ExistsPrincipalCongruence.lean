-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsPrincipalCongruence
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsPrincipalCongruence
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:55.911143+00:00
-- url     : https://prove2.me/theorems/859abf28-7166-4a70-979e-e7defb3fa3e0
-- title:
--   Exists Principal Congruence
-- statement:
--   Definitions and structural lemmas for Exists Principal Congruence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsPrincipalCongruence.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
namespace GlobalTheory.CompanionTheory.PrincipalCongruence
variable {k Γ : Type*} [Field k] [LinearOrderedCommGroupWithZero Γ]
variable {n : Type*} [Fintype n] [DecidableEq n]
theorem entry_mul_le (v : Valuation k Γ) {r s : Γ} (hs : s ≤ 1)
    {A B : Matrix n n k} (hA : ∀ i j, v (A i j) ≤ r) (hB : ∀ i j, v (B i j) ≤ s) (i j : n) :
    v ((A * B) i j) ≤ r := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le v fun l _ => ?_
  rw [map_mul]
  calc v (A i l) * v (B l j) ≤ r * s := mul_le_mul' (hA i l) (hB l j)
    _ ≤ r * 1 := mul_le_mul' le_rfl hs
    _ = r := mul_one r
theorem inv_entry_le_one (v : Valuation k Γ) {r : Γ} (hr : r < 1)
    {A B : Matrix n n k} (hBA : B * (1 + A) = 1) (hA : ∀ i j, v (A i j) ≤ r) (i j : n) :
    v (B i j) ≤ 1 := by
  haveI : Nonempty (n × n) := ⟨(i, j)⟩
  obtain ⟨⟨a, b⟩, hmax⟩ := Finite.exists_max (fun p : n × n => v (B p.1 p.2))
  have hM : ∀ i j, v (B i j) ≤ v (B a b) := fun i j => hmax (i, j)
  refine (hM i j).trans ?_
  by_contra hlt
  have hgt : 1 < v (B a b) := not_le.mp hlt
  have hpos : 0 < v (B a b) := zero_lt_one.trans hgt
  have hB : B = 1 - B * A := by
    have : B + B * A = 1 := by rw [← hBA, mul_add, mul_one]
    exact eq_sub_of_add_eq this
  have hprod : v ((B * A) a b) ≤ v (B a b) * r := by
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_le v fun l _ => ?_
    rw [map_mul]
    exact mul_le_mul' (hM a l) (hA l b)
  have hlt' : v (B a b) * r < v (B a b) := by
    calc v (B a b) * r < v (B a b) * 1 := by
          exact mul_lt_mul_of_pos_left hr hpos
      _ = v (B a b) := mul_one _
  have hone : v ((1 : Matrix n n k) a b) ≤ 1 := by
    by_cases h : a = b
    · rw [h, Matrix.one_apply_eq, map_one]
    · rw [Matrix.one_apply_ne h, map_zero]
      exact zero_le_one
  have hentry : B a b = (1 : Matrix n n k) a b - (B * A) a b := by
    conv_lhs => rw [hB]
    rfl
  have hle : v (B a b) ≤ max (v ((1 : Matrix n n k) a b)) (v ((B * A) a b)) := by
    rw [hentry]
    exact Valuation.map_sub v _ _
  rcases le_max_iff.mp hle with h | h
  · exact absurd (h.trans hone) (not_le.mpr hgt)
  · exact absurd (h.trans hprod) (not_le.mpr hlt')
def principalCongruence (v : Valuation k Γ) (r : Γ) (hr : r < 1) :
    Subgroup (GL n k) where
  carrier := {g | ∀ i j, v ((g : Matrix n n k) i j - (1 : Matrix n n k) i j) ≤ r}
  one_mem' := by
    intro i j
    simp
  mul_mem' := by
    intro g h hg hh i j
    have hg' : ∀ i j, v (((g : Matrix n n k) - 1) i j) ≤ r := hg
    have hh' : ∀ i j, v (((h : Matrix n n k) - 1) i j) ≤ r := hh
    have key : ((g * h : GL n k) : Matrix n n k) - 1 =
        ((g : Matrix n n k) - 1) * ((h : Matrix n n k) - 1) +
          (((g : Matrix n n k) - 1) + ((h : Matrix n n k) - 1)) := by
      rw [Units.val_mul]
      noncomm_ring
    have key' : ((g * h : GL n k) : Matrix n n k) i j - (1 : Matrix n n k) i j =
        (((g : Matrix n n k) - 1) * ((h : Matrix n n k) - 1)) i j +
          ((((g : Matrix n n k) - 1) i j) + (((h : Matrix n n k) - 1) i j)) := by
      rw [← Matrix.sub_apply, key]
      rfl
    rw [key']
    exact Valuation.map_add_le v (entry_mul_le v hr.le hg' hh' i j)
      (Valuation.map_add_le v (hg' i j) (hh' i j))
  inv_mem' := by
    intro g hg i j
    have hg' : ∀ i j, v (((g : Matrix n n k) - 1) i j) ≤ r := hg
    have hBA : ((g⁻¹ : GL n k) : Matrix n n k) * (1 + ((g : Matrix n n k) - 1)) = 1 := by
      rw [add_sub_cancel, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hint := inv_entry_le_one v hr hBA hg'
    have key : ((g⁻¹ : GL n k) : Matrix n n k) - 1 =
        -(((g⁻¹ : GL n k) : Matrix n n k) * ((g : Matrix n n k) - 1)) := by
      rw [mul_sub, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
      abel
    have key' : ((g⁻¹ : GL n k) : Matrix n n k) i j - (1 : Matrix n n k) i j =
        -((((g⁻¹ : GL n k) : Matrix n n k) * ((g : Matrix n n k) - 1)) i j) := by
      rw [← Matrix.sub_apply, key]
      rfl
    rw [key', Valuation.map_neg, Matrix.mul_apply]
    refine Valuation.map_sum_le v fun l _ => ?_
    rw [map_mul]
    calc v (((g⁻¹ : GL n k) : Matrix n n k) i l) * v (((g : Matrix n n k) - 1) l j)
        ≤ 1 * r := mul_le_mul' (hint i l) (hg' l j)
      _ = r := one_mul r
end GlobalTheory.CompanionTheory.PrincipalCongruence


