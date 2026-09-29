-- Prove2me | solution 1 for AlgebraicCurve.RadialRegion.exists_recip
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/0cc15fcd-d849-5d36-b7e8-9e51d9b6d843

import Mathlib
import Definitions.Def_AlgebraicCurve_CellDissection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RadialRegion_exists_recip

set_option autoImplicit false

open AlgebraicCurve

noncomputable section

namespace RadialRecip

section Recip

private theorem le_inv_flip {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a ≤ b⁻¹) :
    b ≤ a⁻¹ := by
  have h1 : a * b ≤ 1 := by
    calc a * b ≤ b⁻¹ * b := mul_le_mul_of_nonneg_right h hb.le
    _ = 1 := inv_mul_cancel₀ hb.ne'
  calc b = a⁻¹ * (a * b) := by field_simp
  _ ≤ a⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 (inv_pos.mpr ha).le
  _ = a⁻¹ := mul_one _

private theorem lt_inv_flip {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a < b⁻¹) :
    b < a⁻¹ := by
  by_contra hcon
  push Not at hcon
  have h1 : b⁻¹ ≤ a⁻¹⁻¹ :=
    le_inv_flip (inv_pos.mpr ha) (inv_pos.mpr hb) (by rw [inv_inv]; exact hcon)
  rw [inv_inv] at h1
  exact absurd (lt_of_lt_of_le h h1) (lt_irrefl a)

variable (R : RadialRegion)

private theorem r_arg_inv (w : ℂ) : R.r (Complex.arg w⁻¹) = R.r (-Complex.arg w) := by
  rw [Complex.arg_inv]
  split_ifs with h
  · rw [h]
    have h1 := R.hper (-Real.pi)
    have h2 : -Real.pi + 2 * Real.pi = Real.pi := by ring
    rw [h2] at h1
    rw [← h1]
  · rfl

private theorem loop_periodic (φ : ℝ) : R.loop (φ + 2 * Real.pi) = R.loop φ := by
  show R.q + (R.r (φ + 2 * Real.pi) : ℂ) * Complex.exp (((φ + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
    R.q + (R.r φ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)
  rw [R.hper φ]
  have h : (((φ + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
      (φ : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

private theorem loop_two_pi_sub (x : ℝ) : R.loop (2 * Real.pi - x) = R.loop (-x) := by
  have h := loop_periodic R (-x)
  rw [show -x + 2 * Real.pi = 2 * Real.pi - x by ring] at h
  exact h

noncomputable def recip : RadialRegion where
  q := 0
  r := (fun φ => (R.r (-φ))⁻¹)
  hcont := ((R.hcont.comp continuous_neg).inv₀ fun φ => (R.hpos _).ne')
  hper := by
    intro φ
    show (R.r (-(φ + 2 * Real.pi)))⁻¹ = (R.r (-φ))⁻¹
    congr 1
    have h1 : -(φ + 2 * Real.pi) = -φ - 2 * Real.pi := by ring
    rw [h1, R.hper.sub_eq]
  hpos := (fun φ => inv_pos.mpr (R.hpos _))
  N := R.N
  φs := (fun k => 2 * Real.pi - R.φs (Fin.rev k))
  hφ0 := by
    show 2 * Real.pi - R.φs (Fin.rev 0) = 0
    rw [Fin.rev_zero, R.hφN]
    ring
  hφN := by
    show 2 * Real.pi - R.φs (Fin.rev (Fin.last R.N)) = 2 * Real.pi
    rw [Fin.rev_last, R.hφ0]
    ring
  hmono := by
    intro k l hkl
    have h1 : Fin.rev l < Fin.rev k := by
      rw [Fin.lt_def, Fin.val_rev, Fin.val_rev]
      rw [Fin.lt_def] at hkl
      omega
    have h2 := R.hmono h1
    show 2 * Real.pi - R.φs (Fin.rev k) < 2 * Real.pi - R.φs (Fin.rev l)
    linarith
  hC2 := by
    intro k'
    have hicc : Set.Icc (2 * Real.pi - R.φs (Fin.rev k'.castSucc))
        (2 * Real.pi - R.φs (Fin.rev k'.succ))
        = Set.Icc (2 * Real.pi - R.φs ((Fin.rev k').succ))
          (2 * Real.pi - R.φs ((Fin.rev k').castSucc)) := by
      rw [Fin.rev_castSucc, Fin.rev_succ]
    show ContDiffOn ℝ 2 (fun φ => (R.r (-φ))⁻¹)
      (Set.Icc (2 * Real.pi - R.φs (Fin.rev k'.castSucc)) (2 * Real.pi - R.φs (Fin.rev k'.succ)))
    rw [hicc]
    have hmaps : Set.MapsTo (fun φ => 2 * Real.pi - φ)
        (Set.Icc (2 * Real.pi - R.φs ((Fin.rev k').succ))
          (2 * Real.pi - R.φs ((Fin.rev k').castSucc)))
        (Set.Icc (R.φs ((Fin.rev k').castSucc)) (R.φs ((Fin.rev k').succ))) := by
      intro φ hφ
      obtain ⟨h1, h2⟩ := hφ
      exact ⟨by linarith, by linarith⟩
    have h1 : ContDiffOn ℝ 2 (fun φ => R.r (2 * Real.pi - φ))
        (Set.Icc (2 * Real.pi - R.φs ((Fin.rev k').succ))
          (2 * Real.pi - R.φs ((Fin.rev k').castSucc))) :=
      (R.hC2 (Fin.rev k')).comp ((contDiff_const.sub contDiff_id).contDiffOn) hmaps
    have h2 : ContDiffOn ℝ 2 (fun φ => (R.r (2 * Real.pi - φ))⁻¹)
        (Set.Icc (2 * Real.pi - R.φs ((Fin.rev k').succ))
          (2 * Real.pi - R.φs ((Fin.rev k').castSucc))) :=
      h1.inv fun φ _ => (R.hpos _).ne'
    refine h2.congr ?_
    intro φ _
    show (R.r (-φ))⁻¹ = (R.r (2 * Real.pi - φ))⁻¹
    congr 1
    have h3 : -φ = (2 * Real.pi - φ) - 2 * Real.pi := by ring
    rw [h3, R.hper.sub_eq]

theorem recip_q : (recip R).q = 0 := rfl

theorem recip_N : (recip R).N = R.N := rfl

def idx (k : Fin R.N) : Fin (recip R).N := k

def unidx (k : Fin (recip R).N) : Fin R.N := k

theorem loop_recip (hq : R.q = 0) (φ : ℝ) : ((recip R).loop φ)⁻¹ = R.loop (-φ) := by
  show ((0 : ℂ) + (((R.r (-φ))⁻¹ : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))⁻¹ =
    R.q + (R.r (-φ) : ℂ) * Complex.exp (((-φ : ℝ) : ℂ) * Complex.I)
  rw [hq]
  simp only [zero_add, Complex.ofReal_inv, Complex.ofReal_neg, neg_mul, Complex.exp_neg, mul_inv,
    inv_inv]

theorem loop_recip_eq (hq : R.q = 0) (θ : ℝ) :
    (recip R).loop θ = (R.loop (2 * Real.pi - θ))⁻¹ := by
  rw [loop_two_pi_sub R θ, ← loop_recip R hq θ, inv_inv]

theorem zero_mem_Kint : (0 : ℂ) ∈ (recip R).Kint := by
  show ‖(0 : ℂ) - 0‖ < (R.r (-Complex.arg ((0 : ℂ) - 0)))⁻¹
  rw [sub_zero, norm_zero]
  exact inv_pos.mpr (R.hpos _)

theorem mem_K_iff (hq : R.q = 0) {w : ℂ} (hw : w ≠ 0) : w ∈ (recip R).K ↔ w⁻¹ ∉ R.Kint := by
  have hK : w ∈ (recip R).K ↔ ‖w‖ ≤ (R.r (-Complex.arg w))⁻¹ := by
    show ‖w - 0‖ ≤ (R.r (-Complex.arg (w - 0)))⁻¹ ↔ _
    rw [sub_zero]
  have hKint : w⁻¹ ∉ R.Kint ↔ R.r (-Complex.arg w) ≤ ‖w‖⁻¹ := by
    show ¬ (‖w⁻¹ - R.q‖ < R.r (Complex.arg (w⁻¹ - R.q))) ↔ _
    rw [hq, sub_zero, not_lt, r_arg_inv R w, norm_inv]
  rw [hK, hKint]
  constructor
  · intro h
    exact le_inv_flip (norm_pos_iff.mpr hw) (R.hpos _) h
  · intro h
    exact le_inv_flip (R.hpos _) (norm_pos_iff.mpr hw) h

theorem mem_Kint_iff (hq : R.q = 0) {w : ℂ} (hw : w ≠ 0) :
    w ∈ (recip R).Kint ↔ w⁻¹ ∉ R.K := by
  have hKint : w ∈ (recip R).Kint ↔ ‖w‖ < (R.r (-Complex.arg w))⁻¹ := by
    show ‖w - 0‖ < (R.r (-Complex.arg (w - 0)))⁻¹ ↔ _
    rw [sub_zero]
  have hK : w⁻¹ ∉ R.K ↔ R.r (-Complex.arg w) < ‖w‖⁻¹ := by
    show ¬ (‖w⁻¹ - R.q‖ ≤ R.r (Complex.arg (w⁻¹ - R.q))) ↔ _
    rw [hq, sub_zero, not_le, r_arg_inv R w, norm_inv]
  rw [hKint, hK]
  constructor
  · intro h
    exact lt_inv_flip (norm_pos_iff.mpr hw) (R.hpos _) h
  · intro h
    exact lt_inv_flip (R.hpos _) (norm_pos_iff.mpr hw) h

theorem image_inv_arcSet (hq : R.q = 0) (k : Fin R.N) :
    (fun w : ℂ => w⁻¹) '' (recip R).arcSet (idx R (Fin.rev k)) = R.arcSet k := by
  have hI1 : (recip R).φs (Fin.castSucc (idx R (Fin.rev k))) = 2 * Real.pi - R.φs k.succ := by
    show 2 * Real.pi - R.φs (Fin.rev (Fin.castSucc (Fin.rev k))) = _
    rw [Fin.rev_castSucc, Fin.rev_rev]
  have hI2 : (recip R).φs (Fin.succ (idx R (Fin.rev k))) = 2 * Real.pi - R.φs k.castSucc := by
    show 2 * Real.pi - R.φs (Fin.rev (Fin.succ (Fin.rev k))) = _
    rw [Fin.rev_succ, Fin.rev_rev]
  simp only [RadialRegion.arcSet, RadialRegion.arcIcc, hI1, hI2, Set.image_image, loop_recip R hq]
  ext w
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    obtain ⟨hφ1, hφ2⟩ := hφ
    refine ⟨2 * Real.pi - φ, ⟨by linarith, by linarith⟩, ?_⟩
    show R.loop (2 * Real.pi - φ) = R.loop (-φ)
    exact loop_two_pi_sub R φ
  · rintro ⟨ψ, hψ, rfl⟩
    obtain ⟨hψ1, hψ2⟩ := hψ
    refine ⟨2 * Real.pi - ψ, ⟨by linarith, by linarith⟩, ?_⟩
    show R.loop (-(2 * Real.pi - ψ)) = R.loop ψ
    have h := loop_two_pi_sub R (2 * Real.pi - ψ)
    rw [show 2 * Real.pi - (2 * Real.pi - ψ) = ψ by ring] at h
    exact h.symm

theorem arcIcc_recip_idx_rev (k : Fin R.N) :
    (recip R).arcIcc (idx R (Fin.rev k)) = (fun t : ℝ => 2 * Real.pi - t) '' R.arcIcc k := by
  have hI1 : (recip R).φs (Fin.castSucc (idx R (Fin.rev k))) = 2 * Real.pi - R.φs k.succ := by
    show 2 * Real.pi - R.φs (Fin.rev (Fin.castSucc (Fin.rev k))) = _
    rw [Fin.rev_castSucc, Fin.rev_rev]
  have hI2 : (recip R).φs (Fin.succ (idx R (Fin.rev k))) = 2 * Real.pi - R.φs k.castSucc := by
    show 2 * Real.pi - R.φs (Fin.rev (Fin.succ (Fin.rev k))) = _
    rw [Fin.rev_succ, Fin.rev_rev]
  simp only [RadialRegion.arcIcc, hI1, hI2]
  ext t
  constructor
  · intro ht
    obtain ⟨ht1, ht2⟩ := ht
    refine ⟨2 * Real.pi - t, ⟨by linarith, by linarith⟩, ?_⟩
    show 2 * Real.pi - (2 * Real.pi - t) = t
    ring
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hx1, hx2⟩ := hx
    show 2 * Real.pi - x ∈ Set.Icc (2 * Real.pi - R.φs k.succ) (2 * Real.pi - R.φs k.castSucc)
    exact ⟨by linarith, by linarith⟩

def arcEquiv : Fin R.N ≃ Fin (recip R).N where
  toFun k := idx R (Fin.rev k)
  invFun j := Fin.rev (unidx R j)
  left_inv k := by
    show Fin.rev (Fin.rev k) = k
    exact Fin.rev_rev k
  right_inv j := by
    show Fin.rev (Fin.rev (unidx R j)) = unidx R j
    exact Fin.rev_rev _

theorem arcEquiv_apply (k : Fin R.N) : arcEquiv R k = idx R (Fin.rev k) := rfl

theorem arcIcc_recip_arcEquiv (k : Fin R.N) :
    (recip R).arcIcc (arcEquiv R k) = (fun t : ℝ => 2 * Real.pi - t) '' R.arcIcc k := by
  rw [arcEquiv_apply R k]
  exact arcIcc_recip_idx_rev R k

theorem image_inv_arcSet_arcEquiv (hq : R.q = 0) (k : Fin R.N) :
    (fun w : ℂ => w⁻¹) '' (recip R).arcSet (arcEquiv R k) = R.arcSet k := by
  rw [arcEquiv_apply R k]
  exact image_inv_arcSet R hq k

end Recip

section Statement

open scoped Real
open Set

theorem exists_recip (R : RadialRegion) (hq : R.q = 0) :
    ∃ R' : RadialRegion,
      R'.q = 0 ∧ R'.N = R.N ∧ (0 : ℂ) ∈ R'.Kint ∧
      (∀ w : ℂ, w ≠ 0 → (w ∈ R'.K ↔ w⁻¹ ∉ R.Kint)) ∧
      (∀ w : ℂ, w ≠ 0 → (w ∈ R'.Kint ↔ w⁻¹ ∉ R.K)) ∧
      (∀ θ : ℝ, R'.loop θ = (R.loop (2 * π - θ))⁻¹) ∧
      ∃ σ : Fin R.N ≃ Fin R'.N,
        (∀ k : Fin R.N, R'.arcIcc (σ k) = (fun t : ℝ => 2 * π - t) '' R.arcIcc k) ∧
        (∀ k : Fin R.N, (fun w : ℂ => w⁻¹) '' R'.arcSet (σ k) = R.arcSet k) := by
  exact ⟨recip R, recip_q R, recip_N R, zero_mem_Kint R, fun w hw => mem_K_iff R hq hw,
    fun w hw => mem_Kint_iff R hq hw, loop_recip_eq R hq, arcEquiv R, arcIcc_recip_arcEquiv R,
    image_inv_arcSet_arcEquiv R hq⟩

end Statement

end RadialRecip

end

open scoped Real
open AlgebraicCurve Set

theorem solution (R : RadialRegion) (hq : R.q = 0) :
    ∃ R' : RadialRegion,
      R'.q = 0 ∧ R'.N = R.N ∧ (0 : ℂ) ∈ R'.Kint ∧
      (∀ w : ℂ, w ≠ 0 → (w ∈ R'.K ↔ w⁻¹ ∉ R.Kint)) ∧
      (∀ w : ℂ, w ≠ 0 → (w ∈ R'.Kint ↔ w⁻¹ ∉ R.K)) ∧
      (∀ θ : ℝ, R'.loop θ = (R.loop (2 * π - θ))⁻¹) ∧
      ∃ σ : Fin R.N ≃ Fin R'.N,
        (∀ k : Fin R.N, R'.arcIcc (σ k) = (fun t : ℝ => 2 * π - t) '' R.arcIcc k) ∧
        (∀ k : Fin R.N, (fun w : ℂ => w⁻¹) '' R'.arcSet (σ k) = R.arcSet k) := by
  exact RadialRecip.exists_recip (R := R) (hq := hq)

end S_AlgebraicCurve_RadialRegion_exists_recip
end P2MW
export P2MW.S_AlgebraicCurve_RadialRegion_exists_recip (solution)
