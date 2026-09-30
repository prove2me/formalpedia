-- Prove2me | Definitions.Def_CK_CKLaneR2_Tail_SoundG1
-- name    : CK_CKLaneR2_Tail_SoundG1
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:29:09.191985+00:00
-- url     : https://prove2.me/theorems/45b0f8f4-b629-42e0-a16b-e49196880162
-- title:
--   Courtade–Kumar proof module `CKLaneR2.Tail.SoundG1` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneR2.Tail.SoundG1` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneR2.Tail.SoundG1` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneR2.Tail.SoundG1 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneR2/Tail/SoundG1.lean)

import Definitions.Def_CK_CKLaneR2_Tail_SoundBase

-- ===== source module CKLaneR2.Tail.SoundG1 =====
section

/-!
# Lane R2 — tail checker soundness, part 2: the `g1` series TM and the front ends
-/

namespace CKLaneR2.Tail

open CKLaneR2.TM3 CKLaneR2.Cell GeneralCK

/-! ## ok-flag helpers -/

theorem mul_ok_left {A B : TM} (h : (mul A B).ok = true) : A.ok = true := by
  simp only [mul, TM.mul, Bool.and_eq_true] at h; exact h.1.1.1

theorem mul_ok_right {A B : TM} (h : (mul A B).ok = true) : B.ok = true := by
  simp only [mul, TM.mul, Bool.and_eq_true] at h; exact h.1.1.2

theorem xlog_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : Real.log y ≤ -1) :
    x * (-Real.log x) ≤ y * (-Real.log y) := by
  have hy0 : 0 < y := lt_of_lt_of_le hx hxy
  have h := Real.log_le_sub_one_of_pos (div_pos hy0 hx)
  rw [Real.log_div hy0.ne' hx.ne'] at h
  have h2 : x * (Real.log y - Real.log x) ≤ x * (y / x - 1) := mul_le_mul_of_nonneg_left h hx.le
  have h3 : x * (y / x - 1) = y - x := by field_simp
  nlinarith

/-! ## `g1Series` -/

theorem g1Horner_contains {U : TM} {uf : ℝ → ℝ → ℝ → ℝ} (hU : Contains one U uf) :
    Contains one (g1Horner U) (fun x y z => g1Poly (uf x y z)) := by
  have h6 : Contains one (TM.const ((one / 7 : ℕ) : Int) 1) (fun _ _ _ => 1 / ((6 : ℕ) + 1 : ℝ)) := by
    apply Contains.const
    have := natdiv_err 6
    simpa using this
  have h5 := g1Step_contains hU h6 5
  have h4 := g1Step_contains hU h5 4
  have h3 := g1Step_contains hU h4 3
  have h2 := g1Step_contains hU h3 2
  have h1 := g1Step_contains hU h2 1
  have h0 := g1Step_contains hU h1 0
  refine Contains.congr h0 (fun x y z _ _ _ => ?_)
  unfold g1Poly; push_cast; ring

theorem g1Series_contains {U omU : TM} {uf : ℝ → ℝ → ℝ → ℝ} (hU : Contains one U uf)
    (homU : Contains one omU (fun x y z => 1 - uf x y z))
    (hnn : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → 0 ≤ uf x y z) :
    Contains one (g1Series U omU) (fun x y z => g1 (uf x y z)) := by
  have hG := C_mul homU (g1Horner_contains hU)
  intro hok x y z hx hy hz
  simp only [g1Series, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hGok, hup0⟩, hup⟩ := hok
  have hG' := hG hGok x y z hx hy hz
  -- U.ok from G.ok
  have hUok : U.ok = true := by
    have h1 := mul_ok_right hGok
    have h2 : (g1Horner U).ok = (mul U (g1Step U (g1Step U (g1Step U (g1Step U (g1Step U
        (TM.const ((one / 7 : ℕ) : Int) 1) ((one / 6 : ℕ) : Int)) ((one / 5 : ℕ) : Int)) ((one / 4 : ℕ) : Int))
        ((one / 3 : ℕ) : Int)) ((one / 2 : ℕ) : Int))).ok := rfl
    rw [h2] at h1
    exact mul_ok_left h1
  have hu0 := hnn x y z hx hy hz
  have hu1 := Contains.le_upper hone hU hUok x y z hx hy hz
  have hone' := CKLaneR2.Cell.hone'
  have hup' : (U.upper : ℝ) / one ≤ 1 / 8 := by
    rw [div_le_iff₀ hone']
    have : (U.upper : ℝ) ≤ (((one / 8 : ℕ) : ℤ) : ℝ) := by exact_mod_cast hup
    have h8 : (((one / 8 : ℕ) : ℤ) : ℝ) * 8 ≤ one := by
      have : (one / 8) * 8 ≤ one := Nat.div_mul_le_self one 8
      rw [Int.cast_natCast]; exact_mod_cast this
    linarith
  have hlt : uf x y z < 1 := by linarith
  have hser := g1_series_err hu0 hlt
  -- tail
  have htail : uf x y z ^ 7 ≤ ((cdiv (U.upper.toNat ^ 7) (one ^ 6) + 1 : ℕ) : ℝ) / one := by
    have hupnn : (0 : ℤ) ≤ U.upper := le_of_lt hup0
    have hcast : ((U.upper.toNat : ℕ) : ℝ) = (U.upper : ℝ) := by
      have : ((U.upper.toNat : ℤ)) = U.upper := Int.toNat_of_nonneg hupnn
      exact_mod_cast this
    have h7 : uf x y z ^ 7 ≤ ((U.upper : ℝ) / one) ^ 7 := pow_le_pow_left₀ hu0 hu1 7
    have hcd := le_cdiv (U.upper.toNat ^ 7) (one ^ 6) (pow_pos hone 6)
    have e : ((U.upper : ℝ) / one) ^ 7 = (((U.upper.toNat ^ 7 : ℕ) : ℝ) / ((one ^ 6 : ℕ) : ℝ)) / one := by
      push_cast; rw [hcast]; field_simp
    calc uf x y z ^ 7 ≤ ((U.upper : ℝ) / one) ^ 7 := h7
      _ = (((U.upper.toNat ^ 7 : ℕ) : ℝ) / ((one ^ 6 : ℕ) : ℝ)) / one := e
      _ ≤ ((cdiv (U.upper.toNat ^ 7) (one ^ 6) : ℕ) : ℝ) / one :=
          div_le_div_of_nonneg_right hcd hone'.le
      _ ≤ ((cdiv (U.upper.toNat ^ 7) (one ^ 6) + 1 : ℕ) : ℝ) / one := by
          apply div_le_div_of_nonneg_right _ hone'.le; push_cast; linarith
  simp only
  calc |g1 (uf x y z) - evalP 0 (mul omU (g1Horner U)).p x y z / one|
      ≤ |g1 (uf x y z) - (1 - uf x y z) * g1Poly (uf x y z)|
        + |(1 - uf x y z) * g1Poly (uf x y z) - evalP 0 (mul omU (g1Horner U)).p x y z / one| := by
        have := abs_add_le (g1 (uf x y z) - (1 - uf x y z) * g1Poly (uf x y z))
          ((1 - uf x y z) * g1Poly (uf x y z) - evalP 0 (mul omU (g1Horner U)).p x y z / one)
        rw [show g1 (uf x y z) - (1 - uf x y z) * g1Poly (uf x y z)
            + ((1 - uf x y z) * g1Poly (uf x y z) - evalP 0 (mul omU (g1Horner U)).p x y z / one)
            = g1 (uf x y z) - evalP 0 (mul omU (g1Horner U)).p x y z / one by ring] at this
        exact this
    _ ≤ ((cdiv (U.upper.toNat ^ 7) (one ^ 6) + 1 : ℕ) : ℝ) / one + ((mul omU (g1Horner U)).r : ℝ) / one :=
        add_le_add (hser.trans htail) hG'
    _ = (((mul omU (g1Horner U)).r + (cdiv (U.upper.toNat ^ 7) (one ^ 6) + 1) : ℕ) : ℝ) / one := by
        push_cast; ring

end CKLaneR2.Tail

end


