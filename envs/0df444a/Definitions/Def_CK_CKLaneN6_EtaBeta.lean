-- Prove2me | Definitions.Def_CK_CKLaneN6_EtaBeta
-- name    : CK_CKLaneN6_EtaBeta
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:00:53.799315+00:00
-- url     : https://prove2.me/theorems/7006bf2d-a15e-4bdd-8950-2e2cf6a3ddcf
-- title:
--   Courtade–Kumar proof module `CKLaneN6.EtaBeta` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN6.EtaBeta` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN6.EtaBeta` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN6.EtaBeta (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN6/EtaBeta.lean)

import Definitions.Def_CK_GeneralCK_PsiParentEntropyGain

-- ===== source module CKLaneN6.EtaBeta =====
section

/-!
# Lane N6: the archive's logarithmic parent rule (13) — entropy-slope lower bound with `β`

SMALL_RATIO PROOF.md §9: for `0 < h < 1`, `v = H⁻¹(h)`, `ℓ = ln((1-v)/v)`,
`h (-η'(h) - 2) ≥ (1-2v)/(L(1-v)) · (1 + 1/ℓ)` (from `-ln(1-v) ≥ v`).  The first factor decreases in
`v`, the second increases, so on `h ∈ [h0, h1]` with rational brackets `vm ≤ H⁻¹(h0)`,
`H⁻¹(h1) ≤ vp ≤ 1/2` and upper bounds `Lq ≥ ln 2`, `λ ≥ ln((1-vm)/vm) > 0`,
`-η'(h) ≥ 2 + β/h` with `β = (1-2vp)/(Lq(1-vp)) (1 + 1/λ)`.  Integrating (antitone
`η(h) + 2h + β ln h` on `[h0,h1]`):
`η(a) - η(a+c) ≥ 2c + β ln(1 + c/a)` for `h0 ≤ a`, `c ≥ 0`, `a + c ≤ h1`.

Only compiled corpus facts are used (`GeneralCK.deriv_eta`, `hasDerivAt_eta`, `entropyInverse_*`,
`H_strictMonoOn`, `Scalar.eta_continuousOn`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneN6

open GeneralCK Set

/-- Pointwise slope bound: `(1-2v)/(L(1-v)) (1 + 1/ℓ) / h ≤ -η'(h) - 2`. -/
theorem neg_deriv_eta_sub_two_ge {h : ℝ} (hh : 0 < h) (hh1 : h < 1) :
    (1 - 2 * entropyInverse h) / (Real.log 2 * (1 - entropyInverse h)) *
        (1 + 1 / Real.log ((1 - entropyInverse h) / entropyInverse h)) / h ≤
      -deriv eta h - 2 := by
  set v := entropyInverse h with hvdef
  have hv : 0 < v := entropyInverse_pos hh hh1.le
  have hvhalf : v < 1 / 2 := entropyInverse_lt_half hh.le hh1
  have hvc : 0 < 1 - v := by linarith
  have hr : 0 < 1 - 2 * v := by linarith
  have hH : H v = h := (entropyInverse_spec hh.le hh1.le).2.2
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq1 : 1 < (1 - v) / v := by rw [lt_div_iff₀ hv]; linarith
  have hℓ : 0 < Real.log ((1 - v) / v) := Real.log_pos hq1
  set ℓ := Real.log ((1 - v) / v) with hℓdef
  have hJ : J v = ℓ / Real.log 2 := by unfold J; rfl
  have hbin : Real.binEntropy v = v * ℓ - Real.log (1 - v) := by
    rw [Real.binEntropy, Real.log_inv, Real.log_inv, hℓdef, Real.log_div hvc.ne' hv.ne']
    ring
  have hHb : H v = Real.binEntropy v / Real.log 2 := by unfold H; rfl
  have hLh : Real.log 2 * h = v * ℓ - Real.log (1 - v) := by
    rw [← hH, hHb, ← hbin]; field_simp
  have hlog1 : v ≤ -Real.log (1 - v) := by linarith [Real.log_le_sub_one_of_pos hvc]
  rw [deriv_eta hh hh1, ← hvdef, hJ]
  have hden : 0 < Real.log 2 * v * (1 - v) * (ℓ / Real.log 2) := by positivity
  have e1 : -(-2 - (1 - 2 * v) / (Real.log 2 * v * (1 - v) * (ℓ / Real.log 2))) - 2 =
      (1 - 2 * v) / (v * (1 - v) * ℓ) := by
    field_simp
    ring
  rw [e1]
  have key : (1 + 1 / ℓ) * (v * (1 - v) * ℓ) ≤ Real.log 2 * (1 - v) * h := by
    have e2 : (1 + 1 / ℓ) * (v * (1 - v) * ℓ) = (1 - v) * (v * ℓ + v) := by
      field_simp
    rw [e2]
    have : v * ℓ + v ≤ Real.log 2 * h := by rw [hLh]; linarith
    nlinarith
  rw [div_le_div_iff₀ hh (by positivity)]
  have hA : 0 < Real.log 2 * (1 - v) := by positivity
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hA]
  calc (1 - 2 * v) * (1 + 1 / ℓ) * (v * (1 - v) * ℓ)
      = (1 - 2 * v) * ((1 + 1 / ℓ) * (v * (1 - v) * ℓ)) := by ring
    _ ≤ (1 - 2 * v) * (Real.log 2 * (1 - v) * h) := mul_le_mul_of_nonneg_left key hr.le
    _ = (1 - 2 * v) * h * (Real.log 2 * (1 - v)) := by ring

/-- Uniform slope bound on `[h0, h1]` with rational-style brackets. -/
theorem neg_deriv_eta_ge_beta {h0 h1 h vm vp Lq lam : ℝ} (hh0 : 0 < h0) (hh1 : h1 < 1)
    (hh : h0 ≤ h) (hh' : h ≤ h1) (hvm0 : 0 < vm) (hvm2 : vm ≤ 1 / 2) (hvm : H vm ≤ h0)
    (hvp0 : 0 ≤ vp) (hvp : h1 ≤ H vp)
    (hvp2 : vp ≤ 1 / 2) (hLq : Real.log 2 ≤ Lq) (hlam : Real.log ((1 - vm) / vm) ≤ lam)
    (hlam0 : 0 < lam) :
    (1 - 2 * vp) / (Lq * (1 - vp)) * (1 + 1 / lam) / h ≤ -deriv eta h - 2 := by
  have hpos : 0 < h := lt_of_lt_of_le hh0 hh
  have hlt1 : h < 1 := lt_of_le_of_lt hh' hh1
  have hpt := neg_deriv_eta_sub_two_ge hpos hlt1
  set v := entropyInverse h with hvdef
  have hv : 0 < v := entropyInverse_pos hpos hlt1.le
  have hvhalf : v < 1 / 2 := entropyInverse_lt_half hpos.le hlt1
  have hH : H v = h := (entropyInverse_spec hpos.le hlt1.le).2.2
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- brackets of v
  have hvmv : vm ≤ v := by
    by_contra hn
    have hlt : v < vm := lt_of_not_ge hn
    have := H_strictMonoOn ⟨hv.le, hvhalf.le⟩ ⟨hvm0.le, hvm2⟩ hlt
    linarith
  have hvvp : v ≤ vp := by
    by_contra hn
    have hlt : vp < v := lt_of_not_ge hn
    have := H_strictMonoOn ⟨hvp0, hvp2⟩ ⟨hv.le, hvhalf.le⟩ hlt
    linarith
  -- factor comparisons
  have hr1 : 0 ≤ 1 - 2 * vp := by linarith
  have f1 : (1 - 2 * vp) / (1 - vp) ≤ (1 - 2 * v) / (1 - v) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hq1 : 1 < (1 - v) / v := by rw [lt_div_iff₀ hv]; linarith
  have hℓ : 0 < Real.log ((1 - v) / v) := Real.log_pos hq1
  have hℓm : Real.log ((1 - v) / v) ≤ Real.log ((1 - vm) / vm) := by
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ hv hvm0]
    nlinarith
  have f2 : 1 + 1 / lam ≤ 1 + 1 / Real.log ((1 - v) / v) := by
    have : 1 / lam ≤ 1 / Real.log ((1 - v) / v) :=
      one_div_le_one_div_of_le hℓ (hℓm.trans hlam)
    linarith
  have f3 : 1 / Lq ≤ 1 / Real.log 2 := one_div_le_one_div_of_le hL hLq
  have hLq0 : 0 < Lq := lt_of_lt_of_le hL hLq
  have hbig : (1 - 2 * vp) / (Lq * (1 - vp)) * (1 + 1 / lam) ≤
      (1 - 2 * v) / (Real.log 2 * (1 - v)) * (1 + 1 / Real.log ((1 - v) / v)) := by
    have e1 : (1 - 2 * vp) / (Lq * (1 - vp)) = (1 / Lq) * ((1 - 2 * vp) / (1 - vp)) := by
      field_simp
    have e2 : (1 - 2 * v) / (Real.log 2 * (1 - v)) = (1 / Real.log 2) * ((1 - 2 * v) / (1 - v)) := by
      field_simp
    rw [e1, e2]
    have g1 : 0 ≤ (1 - 2 * vp) / (1 - vp) := div_nonneg hr1 (by linarith)
    have g2 : 0 ≤ 1 + 1 / lam := by positivity
    have g3 : 0 ≤ 1 / Lq := by positivity
    calc 1 / Lq * ((1 - 2 * vp) / (1 - vp)) * (1 + 1 / lam)
        ≤ 1 / Real.log 2 * ((1 - 2 * vp) / (1 - vp)) * (1 + 1 / lam) := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right f3 g1) g2
      _ ≤ 1 / Real.log 2 * ((1 - 2 * v) / (1 - v)) * (1 + 1 / lam) := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left f1 (by positivity)) g2
      _ ≤ 1 / Real.log 2 * ((1 - 2 * v) / (1 - v)) * (1 + 1 / Real.log ((1 - v) / v)) := by
          apply mul_le_mul_of_nonneg_left f2
          apply mul_nonneg (by positivity) (div_nonneg (by linarith) (by linarith))
  calc (1 - 2 * vp) / (Lq * (1 - vp)) * (1 + 1 / lam) / h
      ≤ (1 - 2 * v) / (Real.log 2 * (1 - v)) * (1 + 1 / Real.log ((1 - v) / v)) / h :=
        div_le_div_of_nonneg_right hbig hpos.le
    _ ≤ -deriv eta h - 2 := hpt

/-- Integrated form of the archive's (13): `η(a) - η(a+c) ≥ 2c + β ln(1 + c/a)`. -/
theorem eta_increment_ge_beta {h0 h1 vm vp Lq lam a c : ℝ} (hh0 : 0 < h0) (hh1 : h1 < 1)
    (hvm0 : 0 < vm) (hvm2 : vm ≤ 1 / 2) (hvm : H vm ≤ h0) (hvp0 : 0 ≤ vp) (hvp : h1 ≤ H vp)
    (hvp2 : vp ≤ 1 / 2)
    (hLq : Real.log 2 ≤ Lq) (hlam : Real.log ((1 - vm) / vm) ≤ lam) (hlam0 : 0 < lam)
    (ha : h0 ≤ a) (hc : 0 ≤ c) (hac : a + c ≤ h1) :
    2 * c + (1 - 2 * vp) / (Lq * (1 - vp)) * (1 + 1 / lam) * Real.log (1 + c / a) ≤
      eta a - eta (a + c) := by
  set β := (1 - 2 * vp) / (Lq * (1 - vp)) * (1 + 1 / lam) with hβ
  have ha0 : 0 < a := lt_of_lt_of_le hh0 ha
  have hmono : AntitoneOn (fun h : ℝ => eta h + 2 * h + β * Real.log h) (Icc h0 h1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc h0 h1)
      (f' := fun h => deriv eta h + 2 + β / h)
    · apply ContinuousOn.add
      · apply ContinuousOn.add
        · exact Scalar.eta_continuousOn.mono (fun x hx => ⟨lt_of_lt_of_le hh0 hx.1,
            (hx.2.trans hh1.le)⟩)
        · exact (continuous_const.mul continuous_id).continuousOn
      · apply ContinuousOn.mul continuousOn_const
        exact Real.continuousOn_log.mono (fun x hx => ne_of_gt (lt_of_lt_of_le hh0 hx.1))
    · intro h hh
      rw [interior_Icc] at hh
      have hp : 0 < h := lt_of_lt_of_le hh0 hh.1.le
      have hl : h < 1 := lt_of_lt_of_le hh.2 hh1.le
      have h1 := hasDerivAt_eta hp hl
      rw [← (hasDerivAt_eta hp hl).deriv] at h1
      have h2 : HasDerivAt (fun y : ℝ => 2 * y) 2 h := by
        simpa using (hasDerivAt_id h).const_mul (2 : ℝ)
      have h3 : HasDerivAt (fun y : ℝ => β * Real.log y) (β / h) h := by
        simpa [div_eq_mul_inv] using (Real.hasDerivAt_log hp.ne').const_mul β
      exact ((h1.add h2).add h3).hasDerivWithinAt
    · intro h hh
      rw [interior_Icc] at hh
      have hb := neg_deriv_eta_ge_beta hh0 hh1 hh.1.le hh.2.le hvm0 hvm2 hvm hvp0 hvp hvp2 hLq
        hlam hlam0
      have : β / h ≤ -deriv eta h - 2 := hb
      linarith
  have hb : 0 < a + c := by linarith
  have hm := hmono ⟨ha, by linarith⟩ ⟨by linarith, hac⟩ (by linarith : a ≤ a + c)
  simp only at hm
  have he : 1 + c / a = (a + c) / a := by field_simp
  rw [he, Real.log_div hb.ne' ha0.ne']
  nlinarith

end CKLaneN6

end


