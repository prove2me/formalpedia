-- Prove2me | Definitions.Def_CK_CKLaneA3V_Contact
-- name    : CK_CKLaneA3V_Contact
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T15:58:33.194118+00:00
-- url     : https://prove2.me/theorems/1729d7d8-248a-4ea4-829b-3dbf28a03430
-- title:
--   Courtade–Kumar proof module `CKLaneA3V.Contact` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA3V.Contact` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA3V.Contact` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA3V.Contact (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3V/Contact.lean)

import Definitions.Def_CK_CKLaneA3V_SeriesTM2
import Definitions.Def_CK_GeneralCK_CorrectionHessianNatural
import Definitions.Def_CK_GeneralCK_CorrectionHighUScaledContract
import Definitions.Def_CK_GeneralCK_CorrectionHighUNearCornerDetGapFactor
import Definitions.Def_CK_GeneralCK_CorrectionHighUNearCornerRegularContact
import Definitions.Def_CK_GeneralCK_CorrectionComplementCharts

/-!
# CKLaneA3V.Contact — identities linking the TM atoms to the rootV definitions

Coordinates: `u = 1/2 - t`, `w = 1/2 - (1-ρ) t`, `w - u = ρ t`, on `Dom t ρ`.
-/

namespace CKLaneA3V

open GeneralCK GeneralCK.Correction

theorem dom_u_pos {t ρ : ℝ} (hd : Dom t ρ) : 0 < 1 / 2 - t := by
  have := hd.2.1; have : (Tq : ℝ) = 1 / 5 := by norm_num [Tq]
  linarith

theorem dom_u_lt_w {t ρ : ℝ} (hd : Dom t ρ) : 1 / 2 - t < 1 / 2 - (1 - ρ) * t := by
  have h1 := hd.1; have h3 := hd.2.2.1
  nlinarith

theorem dom_w_lt {t ρ : ℝ} (hd : Dom t ρ) : 1 / 2 - (1 - ρ) * t < 1 / 2 := by
  have h1 := hd.1; have h4 := hd.2.2.2
  nlinarith

theorem dom_gap {t ρ : ℝ} : (1 / 2 - (1 - ρ) * t) - (1 / 2 - t) = ρ * t := by ring

theorem atanhR_eq_A (x : ℝ) : atanhR x = SmallMean.A x := rfl

/-- `jn (1/2 - s) = 2 atanh (2 s)` for `0 ≤ s < 1/2`. -/
theorem jn_half_sub {s : ℝ} (hs0 : -1 / 2 < s) (hs1 : s < 1 / 2) :
    Natural.jn (1 / 2 - s) = 2 * atanhR (2 * s) := by
  unfold Natural.jn atanhR
  have h1 : (1 : ℝ) / 2 - s ≠ 0 := by linarith
  have h2 : (1 : ℝ) - 2 * s ≠ 0 := by linarith
  have : (1 - (1 / 2 - s)) / (1 / 2 - s) = (1 + 2 * s) / (1 - 2 * s) := by
    field_simp; ring
  rw [this]; ring

theorem jn_u {t ρ : ℝ} (hd : Dom t ρ) : Natural.jn (1 / 2 - t) = 2 * atanhR (2 * t) := by
  have := dom_u_pos hd; exact jn_half_sub (by linarith [hd.1]) (by linarith)

theorem jn_w {t ρ : ℝ} (hd : Dom t ρ) :
    Natural.jn (1 / 2 - (1 - ρ) * t) = 2 * atanhR (2 * ((1 - ρ) * t)) := by
  have h1 := hd.1; have h2 := hd.2.1; have h3 := hd.2.2.1; have h4 := hd.2.2.2
  have hT : (Tq : ℝ) = 1 / 5 := by norm_num [Tq]
  apply jn_half_sub <;> nlinarith

/-- `biasE x = biasB x - x atanh x` for `|x| < 1`. -/
theorem biasE_eq {x : ℝ} (hx : |x| < 1) :
    Certificates.Reflection.biasE x = Certificates.Reflection.biasB x - x * atanhR x := by
  have hp : 0 < 1 + x := by have := (abs_lt.mp hx).1; linarith
  have hm : 0 < 1 - x := by have := (abs_lt.mp hx).2; linarith
  unfold Certificates.Reflection.biasE Certificates.Reflection.biasB atanhR
  have e1 : (1 : ℝ) - x * x = (1 + x) * (1 - x) := by ring
  rw [e1, Real.log_mul hp.ne' hm.ne', Real.log_div hp.ne' hm.ne']
  ring

theorem biasB_eq (x : ℝ) :
    Certificates.Reflection.biasB x = Real.log 2 - Real.log (1 - x * x) / 2 := rfl

/-- `hn (1/2 - s) = biasE (2 s)` -/
theorem hn_half_sub {s : ℝ} (hs0 : -1 / 2 < s) (hs1 : s < 1 / 2) :
    Certificates.Mixed.hn (1 / 2 - s) = Certificates.Reflection.biasE (2 * s) := by
  have h := Natural.biasE_probability (v := 1 / 2 - s) (by linarith) (by linarith)
  rw [← h]; congr 1; ring

theorem entropySum_eq {t ρ : ℝ} (hd : Dom t ρ) :
    Natural.entropySum (1 / 2 - t) (1 / 2 - (1 - ρ) * t) =
      Certificates.Reflection.biasE (2 * t) + Certificates.Reflection.biasE (2 * ((1 - ρ) * t)) := by
  have h1 := hd.1; have h2 := hd.2.1; have h3 := hd.2.2.1; have h4 := hd.2.2.2
  have hT : (Tq : ℝ) = 1 / 5 := by norm_num [Tq]
  unfold Natural.entropySum
  rw [hn_half_sub (by linarith) (by linarith), hn_half_sub (by nlinarith) (by nlinarith)]

theorem dslope_jn_eq {t ρ : ℝ} (hd : Dom t ρ) :
    dslope Natural.jn (1 / 2 - t) (1 / 2 - (1 - ρ) * t) =
      -4 * ((atanhR (2 * ((1 - ρ) * t)) - atanhR (2 * t)) / (2 * ((1 - ρ) * t) - 2 * t)) := by
  have hne : 1 / 2 - (1 - ρ) * t ≠ 1 / 2 - t := (dom_u_lt_w hd).ne'
  rw [dslope_of_ne _ hne, slope_def_field, jn_u hd, jn_w hd]
  have h1 := hd.1; have h3 := hd.2.2.1
  have hq : ρ * t ≠ 0 := by positivity
  have hρ : ρ ≠ 0 := h3.ne'
  have ht : t ≠ 0 := h1.ne'
  have hq2 : 2 * ((1 - ρ) * t) - 2 * t ≠ 0 := by
    have : 2 * ((1 - ρ) * t) - 2 * t = -(2 * (ρ * t)) := by ring
    rw [this]; exact neg_ne_zero.mpr (by positivity)
  have e : (1 / 2 - (1 - ρ) * t) - (1 / 2 - t) = ρ * t := by ring
  have e2 : 2 * ((1 - ρ) * t) - 2 * t = -2 * (ρ * t) := by ring
  have key : ∀ (a b D : ℝ), D ≠ 0 → (2 * a - 2 * b) / D = -4 * ((a - b) / (-2 * D)) := by
    intro a b D hD; field_simp; ring
  rw [e, e2]
  exact key _ _ _ hq

/-! ## monotonicity of `biasE` and the contact equation -/

theorem hn_eq_binEntropy (v : ℝ) : Certificates.Mixed.hn v = Real.binEntropy v := by
  unfold Certificates.Mixed.hn Real.binEntropy
  rw [Real.log_inv, Real.log_inv]; ring

theorem biasE_eq_binEntropy {x : ℝ} (hx0 : -1 < x) (hx1 : x < 1) :
    Certificates.Reflection.biasE x = Real.binEntropy ((1 - x) / 2) := by
  have h := Natural.biasE_probability (v := (1 - x) / 2) (by linarith) (by linarith)
  have e : 1 - 2 * ((1 - x) / 2) = x := by ring
  rw [e] at h
  rw [h, hn_eq_binEntropy]

theorem biasE_anti {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    Certificates.Reflection.biasE b ≤ Certificates.Reflection.biasE a := by
  rw [biasE_eq_binEntropy (by linarith) (by linarith), biasE_eq_binEntropy (by linarith) (by linarith)]
  apply Real.binEntropy_strictMonoOn.monotoneOn
  · constructor <;> norm_num <;> linarith
  · constructor <;> norm_num <;> linarith
  · linarith

/-- the contact ratio `γ = c/(w-u)` satisfies `γ S = 2 biasE(ρ t γ)`. -/
theorem contact_eqn {t ρ : ℝ} (hd : Dom t ρ) :
    let c := Natural.contact (1 / 2 - t) (1 / 2 - (1 - ρ) * t)
    let S := Natural.entropySum (1 / 2 - t) (1 / 2 - (1 - ρ) * t)
    0 < c ∧ c < 1 ∧ c / (ρ * t) * S = 2 * Certificates.Reflection.biasE (ρ * t * (c / (ρ * t))) := by
  intro c S
  obtain ⟨hc0, hc1, hce⟩ := Natural.contact_spec (dom_u_pos hd) (dom_u_lt_w hd) (dom_w_lt hd)
  have hgap := @dom_gap t ρ
  rw [hgap] at hce
  have h1 := hd.1; have h3 := hd.2.2.1
  have hd0 : 0 < ρ * t := by positivity
  have hS0 : 0 < S := by
    have h := hd.2.1
    have hT : (Tq : ℝ) = 1 / 5 := by norm_num [Tq]
    show 0 < Natural.entropySum (1 / 2 - t) (1 / 2 - (1 - ρ) * t)
    unfold Natural.entropySum
    rw [hn_eq_binEntropy, hn_eq_binEntropy]
    have a1 : 0 < Real.binEntropy (1 / 2 - t) := Real.binEntropy_pos (by linarith) (by linarith)
    have h4 := hd.2.2.2
    have hp : 0 < (1 - ρ) * t := mul_pos (by linarith) h1
    have a2 : 0 < Real.binEntropy (1 / 2 - (1 - ρ) * t) :=
      Real.binEntropy_pos (by nlinarith) (by linarith)
    linarith
  have hE0 : 0 < Certificates.Reflection.biasE c := by
    by_contra hneg
    push Not at hneg
    have : c / Certificates.Reflection.biasE c ≤ 0 := div_nonpos_of_nonneg_of_nonpos hc0.le hneg
    have : 0 < 2 * (ρ * t) / S := by positivity
    change c / Certificates.Reflection.biasE c = 2 * (ρ * t) / Natural.entropySum _ _ at hce
    linarith
  refine ⟨hc0, hc1, ?_⟩
  have hcd : ρ * t * (c / (ρ * t)) = c := by field_simp
  rw [hcd]
  have := hce
  change c / Certificates.Reflection.biasE c = 2 * (ρ * t) / S at this
  field_simp at this ⊢
  linarith

end CKLaneA3V


