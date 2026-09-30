-- Prove2me | Definitions.Def_CK_CKLaneP_SeamCore
-- name    : CK_CKLaneP_SeamCore
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:21:19.982459+00:00
-- url     : https://prove2.me/theorems/6e6c7025-afd6-4bde-864f-37f121ff8035
-- title:
--   Courtade–Kumar proof module `CKLaneP.SeamCore` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.SeamCore` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.SeamCore` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.SeamCore (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/SeamCore.lean)

import Definitions.Def_CK_CKLaneP_RightFiber
import Definitions.Def_CK_CKLaneP_LeftFiber

-- ===== source module CKLaneP.SeamCore =====
section
/-
Lane P — seam field core: the seam curve, the equal-mean line, the right fiber, and their
mean-value consequences.

* Seam curve `seamCurve S e f y = cPG((S−y)/2, (S+y)/2, e, f)`, derivative
  `seamD S e f y = Θ(y/(e+f)) − Θ((1−S+y)/(2e))/2 + Θ((1−S−y)/(2f))/2`.
* Equal-mean line `emLine e f m = cPG(m, m, e, f)`, derivative
  `jdef e f m = Θ((1−2m)/(2e)) + Θ((1−2m)/(2f)) − 2Θ((1−2m)/(e+f))`.
* Right fiber `x ↦ cPG(x, b, e, f)`, derivative
  `rightD b e f x = −Θ((b−x)/(e+f)) − Θ((1−x−b)/(e+f)) + Θ((1−2x)/(2e))`.
-/

set_option autoImplicit false

namespace CKLaneP

open GeneralCK Set

/-! ### Seam curve -/

noncomputable def seamCurve (S e f y : ℝ) : ℝ := canonicalPureGap ((S - y) / 2) ((S + y) / 2) e f

noncomputable def seamD (S e f y : ℝ) : ℝ :=
  e8Theta (y / (e + f)) - e8Theta ((1 - S + y) / (2 * e)) / 2 + e8Theta ((1 - S - y) / (2 * f)) / 2

theorem hasDerivAt_seamCurve {S e f y : ℝ} (hy : 0 < y) (hyS : S + y < 1) (hSy : y < 1 + S)
    (he : 0 < e) (hf : 0 < f) :
    HasDerivAt (seamCurve S e f) (seamD S e f y) y := by
  have hef : 0 < (e + f) / 2 := by linarith
  have hFd := (hasDerivAt_F_radius hy hef).differentiableAt.hasDerivAt
  have hFl := (hasDerivAt_F_radius (show 0 < 1 - S + y by linarith) he).differentiableAt.hasDerivAt
  have hFr := (hasDerivAt_F_radius (show 0 < 1 - S - y by linarith) hf).differentiableAt.hasDerivAt
  have hleft := hFl.comp y ((hasDerivAt_id y).const_add (1 - S))
  have hright := hFr.comp y ((hasDerivAt_id y).const_sub (1 - S))
  have hd1 := deriv_F_radius_eq_e8Theta hy hef
  have hd2 := deriv_F_radius_eq_e8Theta (show 0 < 1 - S + y by linarith) he
  have hd3 := deriv_F_radius_eq_e8Theta (show 0 < 1 - S - y by linarith) hf
  have e1 : y / (2 * ((e + f) / 2)) = y / (e + f) := by ring_nf
  rw [e1] at hd1
  have hleft' : HasDerivAt (fun t => F (1 - S + t) e)
      (deriv (fun r => F r e) (1 - S + y) * 1) y := hleft
  have hright' : HasDerivAt (fun t => F (1 - S - t) f)
      (deriv (fun r => F r f) (1 - S - y) * -1) y := hright
  have hsum :=
    ((hFd.add (hasDerivAt_const y (entropyCorrection e f))).sub
      (hasDerivAt_const y (radialPhi (1 - S) ((e + f) / 2)))).add
      ((((hasDerivAt_const y (eta e)).sub hleft').add
        ((hasDerivAt_const y (eta f)).sub hright')).div_const 2)
  have hev : seamCurve S e f =ᶠ[nhds y]
      (fun t => F t ((e + f) / 2) + entropyCorrection e f - radialPhi (1 - S) ((e + f) / 2) +
        ((eta e - F (1 - S + t) e) + (eta f - F (1 - S - t) f)) / 2) :=
    Filter.Eventually.of_forall (fun t => by
      simp only [seamCurve, canonicalPureGap, radialPhi]
      have h1 : (S + t) / 2 - (S - t) / 2 = t := by ring
      have h2 : 1 - (S - t) / 2 - (S + t) / 2 = 1 - S := by ring
      have h3 : 1 - 2 * ((S - t) / 2) = 1 - S + t := by ring
      have h4 : 1 - 2 * ((S + t) / 2) = 1 - S - t := by ring
      rw [h1, h2, h3, h4])
  refine (hsum.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [hd1, hd2, hd3]
  unfold seamD
  ring

/-- Continuity of the seam curve on `[0, y1]` (the endpoint `y = 0` is the equal-mean point). -/
theorem continuousOn_seamCurve {S e f y1 : ℝ} (hS1 : S + y1 < 1) (hy1 : 0 ≤ y1)
    (he : 0 < e) (hf : 0 < f) : ContinuousOn (seamCurve S e f) (Icc 0 y1) := by
  have hef : 0 < (e + f) / 2 := by linarith
  have hF := continuousOn_F_radius hef
  have hFe := continuousOn_F_radius he
  have hFf := continuousOn_F_radius hf
  have h1 : ContinuousOn (fun t : ℝ => F t ((e + f) / 2)) (Icc 0 y1) :=
    hF.mono (fun t ht => ht.1)
  have h2 : ContinuousOn (fun t : ℝ => F (1 - S + t) e) (Icc 0 y1) :=
    hFe.comp (continuous_const.add continuous_id).continuousOn
      (fun t ht => by simp only [mem_Ici]; linarith [ht.1, ht.2])
  have h3 : ContinuousOn (fun t : ℝ => F (1 - S - t) f) (Icc 0 y1) :=
    hFf.comp (continuous_const.sub continuous_id).continuousOn
      (fun t ht => by simp only [mem_Ici]; linarith [ht.1, ht.2])
  have hcont : ContinuousOn (fun t => F t ((e + f) / 2) + entropyCorrection e f -
      radialPhi (1 - S) ((e + f) / 2) +
        ((eta e - F (1 - S + t) e) + (eta f - F (1 - S - t) f)) / 2) (Icc 0 y1) := by
    apply ContinuousOn.add
    · exact (h1.add continuousOn_const).sub continuousOn_const
    · exact (((continuousOn_const.sub h2).add (continuousOn_const.sub h3)).div_const 2)
  refine hcont.congr (fun t _ => ?_)
  simp only [seamCurve, canonicalPureGap, radialPhi]
  have h1 : (S + t) / 2 - (S - t) / 2 = t := by ring
  have h2 : 1 - (S - t) / 2 - (S + t) / 2 = 1 - S := by ring
  have h3 : 1 - 2 * ((S - t) / 2) = 1 - S + t := by ring
  have h4 : 1 - 2 * ((S + t) / 2) = 1 - S - t := by ring
  rw [h1, h2, h3, h4]

/-- Generic "linear-then-flat" lower bound: if `g' ≥ min(α(t−y0), A) − β` on `[y0, y]` with
`0 < α`, `β ≤ A`, `0 ≤ β`, then `g y ≥ g y0 − β²/(2α)`. -/
theorem mvt_linear_lower {g g' : ℝ → ℝ} {y0 y α A β : ℝ} (hyy : y0 ≤ y)
    (hcont : ContinuousOn g (Icc y0 y))
    (hderiv : ∀ t ∈ Ioo y0 y, HasDerivAt g (g' t) t)
    (hα : 0 < α) (hβA : β ≤ A) (hβ : 0 ≤ β)
    (hbound : ∀ t ∈ Ioo y0 y, min (α * (t - y0)) A - β ≤ g' t) :
    g y0 - β ^ 2 / (2 * α) ≤ g y := by
  -- split at y1 = min y (y0 + A/α)
  set y1 := min y (y0 + A / α) with hy1
  have hAα : 0 ≤ A / α := div_nonneg (hβ.trans hβA) hα.le
  have hy01 : y0 ≤ y1 := le_min hyy (by linarith)
  have hy1y : y1 ≤ y := min_le_left _ _
  -- on [y0, y1]: g(t) - (α(t-y0)^2/2 - β(t-y0)) is monotone
  have hq : ∀ t : ℝ, HasDerivAt (fun t => α * (t - y0) ^ 2 / 2 - β * (t - y0)) (α * (t - y0) - β) t := by
    intro t
    have h := (((((hasDerivAt_id t).sub_const y0).pow 2).const_mul α).div_const 2).sub
      (((hasDerivAt_id t).sub_const y0).const_mul β)
    refine h.congr_deriv ?_
    simp only [id_eq, Nat.cast_ofNat]
    ring
  have hmono1 : MonotoneOn (fun t => g t - (α * (t - y0) ^ 2 / 2 - β * (t - y0))) (Icc y0 y1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc y0 y1)
    · exact (hcont.mono (Icc_subset_Icc le_rfl hy1y)).sub (by fun_prop)
    · intro t ht
      rw [interior_Icc] at ht
      have htt : t ∈ Ioo y0 y := ⟨ht.1, lt_of_lt_of_le ht.2 hy1y⟩
      exact ((hderiv t htt).sub (hq t)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have htt : t ∈ Ioo y0 y := ⟨ht.1, lt_of_lt_of_le ht.2 hy1y⟩
      have hd : HasDerivAt (fun t => g t - (α * (t - y0) ^ 2 / 2 - β * (t - y0)))
          (g' t - (α * (t - y0) - β)) t := (hderiv t htt).sub (hq t)
      have hderv : deriv (fun t => g t - (α * (t - y0) ^ 2 / 2 - β * (t - y0))) t =
          g' t - (α * (t - y0) - β) := hd.deriv
      rw [hderv]
      have hb := hbound t htt
      have hmin : min (α * (t - y0)) A = α * (t - y0) := by
        apply min_eq_left
        have : t - y0 ≤ A / α := by
          have := ht.2
          have h2 : y1 ≤ y0 + A / α := min_le_right _ _
          linarith
        calc α * (t - y0) ≤ α * (A / α) := mul_le_mul_of_nonneg_left this hα.le
          _ = A := by field_simp
      rw [hmin] at hb
      linarith
  have hstep1 := hmono1 ⟨le_rfl, hy01⟩ ⟨hy01, le_rfl⟩ hy01
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_div, sub_zero] at hstep1
  -- quadratic lower bound
  have hquad : -(β ^ 2 / (2 * α)) ≤ α * (y1 - y0) ^ 2 / 2 - β * (y1 - y0) := by
    rw [neg_le_iff_add_nonneg]
    have : α * (y1 - y0) ^ 2 / 2 - β * (y1 - y0) + β ^ 2 / (2 * α) =
        (α * (y1 - y0) - β) ^ 2 / (2 * α) := by field_simp; ring
    rw [this]; positivity
  -- on [y1, y]: g is monotone (derivative ≥ A - β ≥ 0) when y1 < y
  have hstep2 : g y1 ≤ g y := by
    rcases eq_or_lt_of_le hy1y with heq | hlt
    · rw [heq]
    · have hy1eq : y1 = y0 + A / α := by
        rcases min_choice y (y0 + A / α) with h | h
        · have : y1 = y := by rw [hy1]; exact h
          linarith
        · rw [hy1]; exact h
      have hmono2 : MonotoneOn g (Icc y1 y) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc y1 y) (hcont.mono (Icc_subset_Icc hy01 le_rfl))
        · intro t ht
          rw [interior_Icc] at ht
          exact (hderiv t ⟨lt_of_le_of_lt hy01 ht.1, ht.2⟩).differentiableAt.differentiableWithinAt
        · intro t ht
          rw [interior_Icc] at ht
          have htt : t ∈ Ioo y0 y := ⟨lt_of_le_of_lt hy01 ht.1, ht.2⟩
          rw [(hderiv t htt).deriv]
          have hb := hbound t htt
          have hmin : min (α * (t - y0)) A = A := by
            apply min_eq_right
            have : A / α ≤ t - y0 := by linarith [ht.1]
            calc A = α * (A / α) := by field_simp
              _ ≤ α * (t - y0) := mul_le_mul_of_nonneg_left this hα.le
          rw [hmin] at hb
          linarith
      exact hmono2 ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt.le
  linarith

/-! ### Equal-mean line -/

noncomputable def emLine (e f m : ℝ) : ℝ := canonicalPureGap m m e f

noncomputable def jdef (e f m : ℝ) : ℝ :=
  e8Theta ((1 - 2 * m) / (2 * e)) + e8Theta ((1 - 2 * m) / (2 * f)) -
    2 * e8Theta ((1 - 2 * m) / (e + f))

theorem hasDerivAt_emLine {e f m : ℝ} (hm : m < 1 / 2) (he : 0 < e) (hf : 0 < f) :
    HasDerivAt (emLine e f) (jdef e f m) m := by
  have hef : 0 < (e + f) / 2 := by linarith
  have hz : 0 < 1 - 2 * m := by linarith
  have hFc := (hasDerivAt_F_radius hz hef).differentiableAt.hasDerivAt
  have hFe := (hasDerivAt_F_radius hz he).differentiableAt.hasDerivAt
  have hFf := (hasDerivAt_F_radius hz hf).differentiableAt.hasDerivAt
  have hc := hFc.comp m (((hasDerivAt_id m).const_mul 2).const_sub 1)
  have hl := hFe.comp m (((hasDerivAt_id m).const_mul 2).const_sub 1)
  have hr := hFf.comp m (((hasDerivAt_id m).const_mul 2).const_sub 1)
  have hd1 := deriv_F_radius_eq_e8Theta hz hef
  have hd2 := deriv_F_radius_eq_e8Theta hz he
  have hd3 := deriv_F_radius_eq_e8Theta hz hf
  have e1 : (1 - 2 * m) / (2 * ((e + f) / 2)) = (1 - 2 * m) / (e + f) := by ring_nf
  rw [e1] at hd1
  have hc' : HasDerivAt (fun t => F (1 - 2 * t) ((e + f) / 2))
      (deriv (fun r => F r ((e + f) / 2)) (1 - 2 * m) * -(2 * 1)) m := hc
  have hl' : HasDerivAt (fun t => F (1 - 2 * t) e)
      (deriv (fun r => F r e) (1 - 2 * m) * -(2 * 1)) m := hl
  have hr' : HasDerivAt (fun t => F (1 - 2 * t) f)
      (deriv (fun r => F r f) (1 - 2 * m) * -(2 * 1)) m := hr
  have hsum :=
    (((hasDerivAt_const m (F 0 ((e + f) / 2))).add (hasDerivAt_const m (entropyCorrection e f))).sub
      ((hasDerivAt_const m (eta ((e + f) / 2))).sub hc')).add
      ((((hasDerivAt_const m (eta e)).sub hl').add ((hasDerivAt_const m (eta f)).sub hr')).div_const 2)
  have hev : emLine e f =ᶠ[nhds m]
      (fun t => F 0 ((e + f) / 2) + entropyCorrection e f -
        (eta ((e + f) / 2) - F (1 - 2 * t) ((e + f) / 2)) +
        ((eta e - F (1 - 2 * t) e) + (eta f - F (1 - 2 * t) f)) / 2) :=
    Filter.Eventually.of_forall (fun t => by
      simp only [emLine, canonicalPureGap, radialPhi, sub_self]
      have h2 : 1 - t - t = 1 - 2 * t := by ring
      rw [h2])
  refine (hsum.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [hd1, hd2, hd3]
  unfold jdef
  ring

/-- Mean-value lower bound on the equal-mean line. -/
theorem emLine_mvt {e f m1 m2 ℓ : ℝ} (he : 0 < e) (hf : 0 < f) (h12 : m1 ≤ m2) (h2 : m2 < 1 / 2)
    (hd : ∀ t ∈ Icc m1 m2, ℓ ≤ jdef e f t) :
    emLine e f m1 + ℓ * (m2 - m1) ≤ emLine e f m2 := by
  have hdiff : ∀ t ∈ Icc m1 m2, HasDerivAt (fun y => emLine e f y - ℓ * y) (jdef e f t - ℓ) t := by
    intro t ht
    have h := hasDerivAt_emLine (lt_of_le_of_lt ht.2 h2) he hf
    exact (h.sub ((hasDerivAt_id t).const_mul ℓ)).congr_deriv (by rw [mul_one])
  have hcont : ContinuousOn (fun y => emLine e f y - ℓ * y) (Icc m1 m2) :=
    fun t ht => (hdiff t ht).continuousAt.continuousWithinAt
  have hmono : MonotoneOn (fun y => emLine e f y - ℓ * y) (Icc m1 m2) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc m1 m2) hcont
    · intro t ht
      exact (hdiff t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hdiff t (interior_subset ht)).deriv]
      linarith [hd t (interior_subset ht)]
  have := hmono ⟨le_rfl, h12⟩ ⟨h12, le_rfl⟩ h12
  simp only at this
  linarith

/-! ### Right fiber mean-value bound -/

noncomputable def rightD (b e f x : ℝ) : ℝ :=
  -e8Theta ((b - x) / (e + f)) - e8Theta ((1 - x - b) / (e + f)) + e8Theta ((1 - 2 * x) / (2 * e))

theorem rightFiber_mvt {b e f t1 t2 ℓ : ℝ} (he : 0 < e) (hf : 0 < f)
    (h12 : t1 ≤ t2) (h2b : t2 < b) (hb : b < 1 / 2)
    (hd : ∀ t ∈ Icc t1 t2, ℓ ≤ rightD b e f t) :
    canonicalPureGap t1 b e f + ℓ * (t2 - t1) ≤ canonicalPureGap t2 b e f := by
  have hdiff : ∀ t ∈ Icc t1 t2, HasDerivAt (fun y => canonicalPureGap y b e f - ℓ * y)
      (rightD b e f t - ℓ) t := by
    intro t ht
    have htb : t < b := lt_of_le_of_lt ht.2 h2b
    have h := hasDerivAt_rightFiber htb (by linarith) (by linarith) he hf
    exact (h.sub ((hasDerivAt_id t).const_mul ℓ)).congr_deriv (by unfold rightD; ring)
  have hcont : ContinuousOn (fun y => canonicalPureGap y b e f - ℓ * y) (Icc t1 t2) :=
    fun t ht => (hdiff t ht).continuousAt.continuousWithinAt
  have hmono : MonotoneOn (fun y => canonicalPureGap y b e f - ℓ * y) (Icc t1 t2) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc t1 t2) hcont
    · intro t ht
      exact (hdiff t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hdiff t (interior_subset ht)).deriv]
      linarith [hd t (interior_subset ht)]
  have := hmono ⟨le_rfl, h12⟩ ⟨h12, le_rfl⟩ h12
  simp only at this
  linarith

end CKLaneP

end


