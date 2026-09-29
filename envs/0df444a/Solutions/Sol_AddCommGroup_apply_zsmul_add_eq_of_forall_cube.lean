-- Prove2me | solution 1 for AddCommGroup.apply_zsmul_add_eq_of_forall_cube
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/4ad08cd4-d397-5025-926c-d75e86e01022

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddCommGroup_apply_zsmul_add_eq_of_forall_cube

set_option autoImplicit false

namespace P2mQuad

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

theorem tri_succ (n : ℤ) : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
  have h : (n + 1) * (n + 1 - 1) = n * (n - 1) + n * 2 := by ring
  rw [h, Int.add_mul_ediv_right _ _ two_ne_zero]

theorem tri_zero : (0 : ℤ) * (0 - 1) / 2 = 0 := by norm_num

theorem eq_of_second_difference (g : ℤ → N) (D : N)
    (h : ∀ n : ℤ, g (n + 2) - 2 • g (n + 1) + g n = D) (n : ℤ) :
    g n = g 0 + n • (g 1 - g 0) + (n * (n - 1) / 2) • D := by

  have h1 : ∀ n : ℤ, g (n + 1) - g n = (g 1 - g 0) + n • D := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ k ih =>
      have hk := h k
      have e : (k : ℤ) + 1 + 1 = k + 2 := by ring
      rw [e]

      have : g (k + 2) - g (k + 1) = (g (k + 1) - g k) + D := by
        rw [← hk]; abel
      rw [this, ih, add_smul, one_smul]
      abel
    | pred k ih =>

      have hk := h (-(k : ℤ) - 1)
      have e1 : (-(k : ℤ) - 1 + 2) = -k + 1 := by ring
      have e2 : (-(k : ℤ) - 1 + 1) = -k := by ring
      rw [e1, e2] at hk
      rw [e2]
      have : g (-(k : ℤ)) - g (-k - 1) = (g (-k + 1) - g (-k)) - D := by
        rw [← hk]; abel
      rw [this, ih, sub_smul, one_smul]
      abel
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have := h1 k
    rw [tri_succ, add_smul, eq_add_of_sub_eq' this |>.trans (by rfl), ih, add_smul, one_smul]
    abel
  | pred k ih =>
    have hk := h1 (-(k : ℤ) - 1)
    have e2 : (-(k : ℤ) - 1 + 1) = -k := by ring
    rw [e2] at hk

    have : g (-(k : ℤ) - 1) = g (-k) - ((g 1 - g 0) + (-(k : ℤ) - 1) • D) := by
      rw [← hk]; abel
    rw [this, ih]
    have ht : (-(k : ℤ)) * (-(k : ℤ) - 1) / 2 = (-(k : ℤ) - 1) * (-(k : ℤ) - 1 - 1) / 2 + (-(k : ℤ) - 1) := by
      have := tri_succ (-(k : ℤ) - 1)
      rw [e2] at this
      exact this
    rw [ht, add_smul, sub_smul, sub_smul, one_smul]
    abel

theorem main (Λ : M → N)
    (hΛ : ∀ x y z : M, Λ (x + y + z) - Λ (x + y) - Λ (x + z) - Λ (y + z) + Λ x + Λ y + Λ z = Λ 0)
    (x y : M) (n : ℤ) :
    Λ (n • x + y) = Λ y + n • (Λ (x + y) - Λ y) + (n * (n - 1) / 2) • (Λ (2 • x) - 2 • Λ x + Λ 0) := by
  set g : ℤ → M := fun n => n • x + y with hg
  have h2 : ∀ n : ℤ, Λ (g (n + 2)) - 2 • Λ (g (n + 1)) + Λ (g n) = Λ (2 • x) - 2 • Λ x + Λ 0 := by
    intro n
    have hc := hΛ (n • x + y) x x
    have e1 : n • x + y + x + x = g (n + 2) := by simp only [hg]; module
    have e2 : n • x + y + x = g (n + 1) := by simp only [hg]; module
    have e3 : x + x = 2 • x := (two_nsmul x).symm
    rw [e1, e2, e3] at hc
    have e4 : Λ (g n) = Λ (n • x + y) := rfl

    rw [two_nsmul (Λ (g (n + 1))), two_nsmul (Λ x)]
    have := hc

    calc Λ (g (n + 2)) - (Λ (g (n + 1)) + Λ (g (n + 1))) + Λ (g n)
        = (Λ (g (n + 2)) - Λ (g (n + 1)) - Λ (g (n + 1)) - Λ (2 • x) + Λ (n • x + y) + Λ x + Λ x)
            + (Λ (2 • x) - (Λ x + Λ x)) := by rw [e4]; abel
      _ = Λ 0 + (Λ (2 • x) - (Λ x + Λ x)) := by rw [this]
      _ = Λ (2 • x) - (Λ x + Λ x) + Λ 0 := by abel
  have hmain := eq_of_second_difference (fun n => Λ (g n)) _ h2 n
  have g0 : g 0 = y := by simp [hg]
  have g1 : g 1 = x + y := by simp [hg]
  simp only [g0, g1] at hmain
  exact hmain

end P2mQuad

theorem solution
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] (Λ : M → N)
    (hΛ : ∀ x y z : M,
      Λ (x + y + z) - Λ (x + y) - Λ (x + z) - Λ (y + z) + Λ x + Λ y + Λ z = Λ 0)
    (x y : M) (n : ℤ) :
    Λ (n • x + y) =
      Λ y + n • (Λ (x + y) - Λ y) + (n * (n - 1) / 2) • (Λ (2 • x) - 2 • Λ x + Λ 0) :=
  P2mQuad.main Λ hΛ x y n

end S_AddCommGroup_apply_zsmul_add_eq_of_forall_cube
end P2MW
export P2MW.S_AddCommGroup_apply_zsmul_add_eq_of_forall_cube (solution)
