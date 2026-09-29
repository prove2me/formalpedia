-- Prove2me | Definitions.Def_CK_GeneralCK_RadialContact
-- name    : CK_GeneralCK_RadialContact
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:20:31.861071+00:00
-- url     : https://prove2.me/theorems/68e23eb9-fa8d-4e0b-bf0d-e76799f25e88
-- title:
--   Courtade–Kumar proof module `GeneralCK.RadialContact` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.RadialContact` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.RadialContact` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.RadialContact (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/RadialContact.lean)

import Definitions.Def_CK_GeneralCK_ProfileBasics

namespace GeneralCK

/-- The contact equation has exactly one solution in the open lower half. -/
theorem existsUnique_radialContact {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    ∃! v : ℝ, 0 < v ∧ v < 1 / 2 ∧ z * H v = h * (1 - 2 * v) := by
  let g : ℝ → ℝ := fun v => z * H v - h * (1 - 2 * v)
  have hg : Continuous g :=
    (H_continuous.const_mul z).sub
      ((continuous_const.sub (continuous_const.mul continuous_id)).const_mul h)
  have hzero : g 0 = -h := by simp [g]
  have hhalf : g (1 / 2) = z := by simp only [g, H_half]; ring
  have himage := intermediate_value_Icc (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    hg.continuousOn
  obtain ⟨v, hv, heq⟩ := himage (show (0 : ℝ) ∈ Set.Icc (g 0) (g (1 / 2)) by
    rw [hzero, hhalf]; exact ⟨by linarith, hz.le⟩)
  have hv0 : 0 < v := by
    apply lt_of_le_of_ne hv.1
    intro he
    rw [← he, hzero] at heq
    linarith
  have hv1 : v < 1 / 2 := by
    apply lt_of_le_of_ne hv.2
    intro he
    rw [he, hhalf] at heq
    linarith
  have hveq : z * H v = h * (1 - 2 * v) := sub_eq_zero.mp heq
  refine ⟨v, ⟨hv0, hv1, hveq⟩, ?_⟩
  rintro u ⟨hu0, hu1, hueq⟩
  rcases lt_trichotomy u v with huv | huv | huv
  · have hH := H_strictMonoOn ⟨hu0.le, hu1.le⟩ ⟨hv0.le, hv1.le⟩ huv
    have hm := mul_lt_mul_of_pos_left hH hz
    nlinarith
  · exact huv
  · have hH := H_strictMonoOn ⟨hv0.le, hv1.le⟩ ⟨hu0.le, hu1.le⟩ huv
    have hm := mul_lt_mul_of_pos_left hH hz
    nlinarith

theorem radialContact_spec {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    0 < radialContact z h ∧ radialContact z h < 1 / 2 ∧
      z * H (radialContact z h) = h * (1 - 2 * radialContact z h) := by
  obtain ⟨v, hv, huniq⟩ := existsUnique_radialContact hz hh
  have hset : {u : ℝ | 0 < u ∧ u < 1 / 2 ∧ z * H u = h * (1 - 2 * u)} = {v} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun hu => huniq u hu, fun he => he ▸ hv⟩
  simpa only [radialContact, hset, csInf_singleton] using hv

theorem radialContact_pos {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    0 < radialContact z h := (radialContact_spec hz hh).1

theorem radialContact_lt_half {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    radialContact z h < 1 / 2 := (radialContact_spec hz hh).2.1

theorem radialContact_equation {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    z * H (radialContact z h) = h * (1 - 2 * radialContact z h) :=
  (radialContact_spec hz hh).2.2

theorem radialContact_eq_of_equation {z h v : ℝ} (hz : 0 < z) (hh : 0 < h)
    (hv : 0 < v) (hv' : v < 1 / 2) (heq : z * H v = h * (1 - 2 * v)) :
    radialContact z h = v := by
  obtain ⟨u, _, huniq⟩ := existsUnique_radialContact hz hh
  exact (huniq _ (radialContact_spec hz hh)).trans (huniq v ⟨hv, hv', heq⟩).symm

/-- Simultaneous nonzero scaling leaves the defining root set unchanged. -/
theorem radialContact_scale (z h : ℝ) {c : ℝ} (hc : c ≠ 0) :
    radialContact (c * z) (c * h) = radialContact z h := by
  unfold radialContact
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, mul_assoc, mul_right_inj' hc]

/-- Homogeneity includes the explicitly defined zero-radius branch. -/
theorem F_scale (z h c : ℝ) : F (c * z) (c * h) = c * F z h := by
  by_cases hc : c = 0
  · subst c; simp [F]
  by_cases hz : z = 0
  · subst z; simp [F]
  simp only [F, mul_ne_zero hc hz, hz, ↓reduceIte, radialContact_scale z h hc]
  ring

theorem radialContact_strictMono_entropy {z a b : ℝ}
    (hz : 0 < z) (ha : 0 < a) (hab : a < b) :
    radialContact z a < radialContact z b := by
  obtain ⟨hu, hu', hequ⟩ := radialContact_spec hz ha
  obtain ⟨hv, hv', heqv⟩ := radialContact_spec hz (ha.trans hab)
  by_contra hn
  have hvu : radialContact z b ≤ radialContact z a := le_of_not_gt hn
  have hH := H_strictMonoOn.monotoneOn ⟨hv.le, hv'.le⟩ ⟨hu.le, hu'.le⟩ hvu
  have hm := mul_le_mul_of_nonneg_left hH hz.le
  have hg : a * (1 - 2 * radialContact z a) < b * (1 - 2 * radialContact z b) := by
    calc
      a * (1 - 2 * radialContact z a) ≤ a * (1 - 2 * radialContact z b) :=
        mul_le_mul_of_nonneg_left (by linarith) ha.le
      _ < b * (1 - 2 * radialContact z b) :=
        mul_lt_mul_of_pos_right hab (by linarith)
  linarith

theorem radialContact_mono_entropy {z a b : ℝ}
    (hz : 0 < z) (ha : 0 < a) (hab : a ≤ b) :
    radialContact z a ≤ radialContact z b := by
  rcases hab.eq_or_lt with rfl | hab
  · exact le_rfl
  · exact (radialContact_strictMono_entropy hz ha hab).le

theorem radialContact_strictAnti_radius {a b h : ℝ}
    (ha : 0 < a) (hab : a < b) (hh : 0 < h) :
    radialContact b h < radialContact a h := by
  obtain ⟨hu, hu', hequ⟩ := radialContact_spec ha hh
  obtain ⟨hv, hv', heqv⟩ := radialContact_spec (ha.trans hab) hh
  by_contra hn
  have huv : radialContact a h ≤ radialContact b h := le_of_not_gt hn
  have hH := H_strictMonoOn.monotoneOn ⟨hu.le, hu'.le⟩ ⟨hv.le, hv'.le⟩ huv
  have hm := mul_le_mul_of_nonneg_left (show 1 - 2 * radialContact b h ≤
      1 - 2 * radialContact a h by linarith) hh.le
  have hg : a * H (radialContact a h) < b * H (radialContact b h) := by
    calc
      a * H (radialContact a h) ≤ a * H (radialContact b h) :=
        mul_le_mul_of_nonneg_left hH ha.le
      _ < b * H (radialContact b h) :=
        mul_lt_mul_of_pos_right hab (H_pos hv (by linarith))
  linarith

theorem radialContact_anti_radius {a b h : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hh : 0 < h) :
    radialContact b h ≤ radialContact a h := by
  rcases hab.eq_or_lt with rfl | hab
  · exact le_rfl
  · exact (radialContact_strictAnti_radius ha hab hh).le

theorem radialContact_normalize_radius {z : ℝ} (hz : z ≠ 0) (h : ℝ) :
    radialContact z h = radialContact 1 (h / z) := by
  have hs := radialContact_scale z h (c := z⁻¹) (inv_ne_zero hz)
  simpa only [inv_mul_cancel₀ hz, ← div_eq_inv_mul] using hs.symm

theorem radialContact_normalize_entropy (z : ℝ) {h : ℝ} (hh : h ≠ 0) :
    radialContact z h = radialContact (z / h) 1 := by
  have hs := radialContact_scale z h (c := h⁻¹) (inv_ne_zero hh)
  simpa only [inv_mul_cancel₀ hh, ← div_eq_inv_mul] using hs.symm

theorem F_perspective {h : ℝ} (hh : h ≠ 0) (z : ℝ) :
    F z h = h * F (z / h) 1 := by
  simpa only [mul_div_cancel₀ z hh, mul_one] using (F_scale (z / h) 1 h)

theorem radialContact_le_iff_ratio {z₁ z₂ h₁ h₂ : ℝ}
    (hz₁ : 0 < z₁) (hz₂ : 0 < z₂) (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) :
    radialContact z₁ h₁ ≤ radialContact z₂ h₂ ↔ h₁ / z₁ ≤ h₂ / z₂ := by
  rw [radialContact_normalize_radius hz₁.ne', radialContact_normalize_radius hz₂.ne']
  constructor
  · intro hc
    by_contra hn
    have := radialContact_strictMono_entropy (z := 1) (by norm_num)
      (div_pos hh₂ hz₂) (lt_of_not_ge hn)
    exact (not_lt_of_ge hc) this
  · exact radialContact_mono_entropy (by norm_num) (div_pos hh₁ hz₁)

/-- A nonnegative residual certifies an upper contact bracket. -/
theorem radialContact_le_iff {z h v : ℝ} (hz : 0 < z) (hh : 0 < h)
    (hv : 0 ≤ v) (hv' : v ≤ 1 / 2) :
    radialContact z h ≤ v ↔ h * (1 - 2 * v) ≤ z * H v := by
  obtain ⟨hu, hu', heq⟩ := radialContact_spec hz hh
  constructor
  · intro huv
    have hH := H_strictMonoOn.monotoneOn ⟨hu.le, hu'.le⟩ ⟨hv, hv'⟩ huv
    have hm := mul_le_mul_of_nonneg_left hH hz.le
    have ht := mul_le_mul_of_nonneg_left
      (show 1 - 2 * v ≤ 1 - 2 * radialContact z h by linarith) hh.le
    linarith
  · intro hr
    by_contra hn
    have hvu := lt_of_not_ge hn
    have hH := H_strictMonoOn ⟨hv, hv'⟩ ⟨hu.le, hu'.le⟩ hvu
    have hm := mul_lt_mul_of_pos_left hH hz
    have ht := mul_lt_mul_of_pos_left
      (show 1 - 2 * radialContact z h < 1 - 2 * v by linarith) hh
    linarith

/-- A nonpositive residual certifies a lower contact bracket. -/
theorem le_radialContact_iff {z h v : ℝ} (hz : 0 < z) (hh : 0 < h)
    (hv : 0 ≤ v) (hv' : v ≤ 1 / 2) :
    v ≤ radialContact z h ↔ z * H v ≤ h * (1 - 2 * v) := by
  obtain ⟨hu, hu', heq⟩ := radialContact_spec hz hh
  constructor
  · intro hvu
    have hH := H_strictMonoOn.monotoneOn ⟨hv, hv'⟩ ⟨hu.le, hu'.le⟩ hvu
    have hm := mul_le_mul_of_nonneg_left hH hz.le
    have ht := mul_le_mul_of_nonneg_left
      (show 1 - 2 * radialContact z h ≤ 1 - 2 * v by linarith) hh.le
    linarith
  · intro hr
    by_contra hn
    have huv := lt_of_not_ge hn
    have hH := H_strictMonoOn ⟨hu.le, hu'.le⟩ ⟨hv, hv'⟩ huv
    have hm := mul_lt_mul_of_pos_left hH hz
    have ht := mul_lt_mul_of_pos_left
      (show 1 - 2 * v < 1 - 2 * radialContact z h by linarith) hh
    linarith

end GeneralCK


