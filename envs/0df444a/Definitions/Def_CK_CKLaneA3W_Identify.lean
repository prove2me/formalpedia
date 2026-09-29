-- Prove2me | Definitions.Def_CK_CKLaneA3W_Identify
-- name    : CK_CKLaneA3W_Identify
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T16:04:01.410002+00:00
-- url     : https://prove2.me/theorems/8ea74092-e83a-4c67-8920-9baed57b3062
-- title:
--   Courtade–Kumar proof module `CKLaneA3W.Identify` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA3W.Identify` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA3W.Identify` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA3W.Identify (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3W/Identify.lean)

import Definitions.Def_CK_CKLaneA3W_Contact
import Definitions.Def_CK_CKLaneA3W_ExactPoly

/-!
# CKLaneA3W.Identify — contact TM (implicit equation) and pointwise identities for congr steps
-/

namespace CKLaneA3W

open GeneralCK GeneralCK.Correction

theorem good_gamma {DS Φ : TMd} (G : TPoly)
    (hS : Good (fun t ρ => Natural.entropySum (1 / 2 - t) (1 / 2 - (1 - ρ) * t)) DS)
    (hΦ : Good (fun t ρ => ev G t ρ * Natural.entropySum (1 / 2 - t) (1 / 2 - (1 - ρ) * t) +
        ((-2 : ℚ) : ℝ) * Certificates.Reflection.biasE
          (((1 / 2 - (1 - ρ) * t) - (1 / 2 - t)) * ev G t ρ)) Φ)
    (hΦ0 : allEmpty Φ.P = true)
    (Smin : ℚ) (hSmin : 0 < Smin) (hSlow : Smin ≤ TPoly.lowB DS.P - DS.r * Tq ^ DS.n)
    (hG0 : 0 ≤ TPoly.lowB G) (hG1 : Tq * bsum (entryBounds G) < 1)
    (r' : ℚ) (hr' : Φ.r / Smin ≤ r') :
    Good (fun t ρ => Natural.contact (1 / 2 - t) (1 / 2 - (1 - ρ) * t) /
      ((1 / 2 - (1 - ρ) * t) - (1 / 2 - t))) ⟨G, r', Φ.n⟩ := by
  refine ⟨?_, le_trans (div_nonneg hΦ.2 hSmin.le) hr'⟩
  intro t ρ hd
  show |Natural.contact (1 / 2 - t) (1 / 2 - (1 - ρ) * t) / ((1 / 2 - (1 - ρ) * t) - (1 / 2 - t)) -
    ev G t ρ| ≤ (r' : ℝ) * t ^ Φ.n
  have ht0 := hd.1.le
  have h1 := hd.1; have h3 := hd.2.2.1; have h4 := hd.2.2.2
  set g := ev G t ρ with hg
  set S := Natural.entropySum (1 / 2 - t) (1 / 2 - (1 - ρ) * t) with hSdef
  set c := Natural.contact (1 / 2 - t) (1 / 2 - (1 - ρ) * t) with hc
  have hgap := @dom_gap t ρ
  rw [hgap]
  -- bounds on g
  have hg0 : 0 ≤ g := le_trans (by exact_mod_cast hG0) (TPoly.lowB_spec ht0 hd.2.1 hd.sigma G)
  have hgb : |g| ≤ bsum (entryBounds G) := (entryBounds_spec G).eval_le ht0 hd.2.1 hd.sigma
  have hG1' : (Tq : ℝ) * (bsum (entryBounds G) : ℝ) < 1 := by exact_mod_cast hG1
  have hdg1 : ρ * t * g < 1 := by
    have hb0 : (0 : ℝ) ≤ bsum (entryBounds G) := (abs_nonneg _).trans hgb
    have : ρ * t * g ≤ 1 * (Tq : ℝ) * bsum (entryBounds G) := by
      have hg' : g ≤ bsum (entryBounds G) := (le_abs_self g).trans hgb
      have hρt : ρ * t ≤ 1 * (Tq : ℝ) := by nlinarith [hd.2.1]
      calc ρ * t * g ≤ (1 * (Tq : ℝ)) * bsum (entryBounds G) :=
            mul_le_mul hρt hg' hg0 (by nlinarith [Tq_pos])
        _ = 1 * (Tq : ℝ) * bsum (entryBounds G) := by ring
    linarith
  have hdg0 : 0 ≤ ρ * t * g := by positivity
  -- contact equation
  obtain ⟨hc0, hc1, hce⟩ := contact_eqn hd
  have hd0 : 0 < ρ * t := by positivity
  set γ := c / (ρ * t) with hγ
  have hdγ : ρ * t * γ = c := by rw [hγ]; field_simp
  rw [hdγ] at hce
  -- S lower bound
  have hSl := hS.lower hd
  have hSm : (Smin : ℝ) ≤ S := le_trans (by exact_mod_cast hSlow) hSl
  have hSm0 : (0 : ℝ) < Smin := by exact_mod_cast hSmin
  have hS0 : 0 < S := lt_of_lt_of_le hSm0 hSm
  -- residual bound
  have hΦp := hΦ.1 t ρ hd
  have hΦe : ev Φ.P t ρ = 0 := allEmpty_eval _ _ _ _ hΦ0
  simp only at hΦp
  rw [hΦe, sub_zero, hgap] at hΦp
  push_cast at hΦp
  -- Φ(g) = g S - 2 E(ρ t g); Φ(γ) = 0
  have key : |γ - g| * S ≤ |g * S - 2 * Certificates.Reflection.biasE (ρ * t * g)| := by
    rcases le_total γ g with hle | hle
    · -- g ≥ γ : E(ρ t g) ≤ E(c)
      have hE : Certificates.Reflection.biasE (ρ * t * g) ≤ Certificates.Reflection.biasE c := by
        apply biasE_anti hc0.le _ hdg1
        have h' : ρ * t * γ ≤ ρ * t * g := mul_le_mul_of_nonneg_left hle hd0.le
        rw [hdγ] at h'; exact h'
      have : (g - γ) * S ≤ g * S - 2 * Certificates.Reflection.biasE (ρ * t * g) := by nlinarith
      rw [abs_of_nonpos (by linarith : γ - g ≤ 0)]
      calc -(γ - g) * S = (g - γ) * S := by ring
        _ ≤ _ := this
        _ ≤ _ := le_abs_self _
    · have hE : Certificates.Reflection.biasE c ≤ Certificates.Reflection.biasE (ρ * t * g) := by
        apply biasE_anti hdg0 _ hc1
        have h' : ρ * t * g ≤ ρ * t * γ := mul_le_mul_of_nonneg_left hle hd0.le
        rw [hdγ] at h'; exact h'
      have : g * S - 2 * Certificates.Reflection.biasE (ρ * t * g) ≤ (g - γ) * S := by nlinarith
      rw [abs_of_nonneg (by linarith : 0 ≤ γ - g)]
      calc (γ - g) * S = -((g - γ) * S) := by ring
        _ ≤ -(g * S - 2 * Certificates.Reflection.biasE (ρ * t * g)) := by linarith
        _ ≤ _ := neg_le_abs _
  have hfin : |γ - g| ≤ (Φ.r : ℝ) * t ^ Φ.n / Smin := by
    rw [le_div_iff₀ hSm0]
    calc |γ - g| * Smin ≤ |γ - g| * S := mul_le_mul_of_nonneg_left hSm (abs_nonneg _)
      _ ≤ _ := key
      _ = |g * S + -2 * Certificates.Reflection.biasE (ρ * t * g)| := by ring_nf
      _ ≤ _ := hΦp
  have hr'' : (Φ.r : ℝ) / Smin ≤ r' := by exact_mod_cast hr'
  show |c / (ρ * t) - g| ≤ (r' : ℝ) * t ^ Φ.n
  calc |c / (ρ * t) - g| = |γ - g| := rfl
    _ ≤ (Φ.r : ℝ) * t ^ Φ.n / Smin := hfin
    _ = ((Φ.r : ℝ) / Smin) * t ^ Φ.n := by ring
    _ ≤ (r' : ℝ) * t ^ Φ.n := mul_le_mul_of_nonneg_right hr'' (pow_nonneg ht0 _)

/-- `|x| < 1` for a TM-enclosed function with valuation 1 -/
theorem Good.abs_lt_one {x : ℝ → ℝ → ℝ} {X : TMd} (hx : Good x X) (hz : zeroPrefix X.P 1 = true)
    (h1 : 1 ≤ X.n) (κ : ℚ) (hκ : bsum (ldrop (entryBounds X.P) 1) + X.r * Tq ^ (X.n - 1) ≤ κ)
    (hκT : κ * Tq < 1) {t ρ : ℝ} (hd : Dom t ρ) : |x t ρ| < 1 := by
  have hxb := hx.abs_le' hz h1 hκ hd
  rw [pow_one] at hxb
  have hκ0 : (0 : ℝ) ≤ κ := by
    have := le_trans (abs_nonneg _) hxb
    by_contra hneg; push Not at hneg
    nlinarith [hd.1]
  have hκT' : (κ : ℝ) * (Tq : ℝ) < 1 := by exact_mod_cast hκT
  exact lt_of_le_of_lt (hxb.trans (mul_le_mul_of_nonneg_left hd.2.1 hκ0)) hκT'

theorem biasB_pos {c : ℝ} (hc : |c| < 1) : 0 < Certificates.Reflection.biasB c := by
  unfold Certificates.Reflection.biasB
  have h1 : 0 < 1 - c * c := by
    have : c * c < 1 := by
      have := abs_mul_abs_self c
      nlinarith [abs_nonneg c]
    linarith
  have h2 : 1 - c * c ≤ 1 := by nlinarith [mul_self_nonneg c]
  have h3 : Real.log (1 - c * c) ≤ 0 := Real.log_nonpos h1.le h2
  have h4 : 0 < Real.log 2 := by positivity
  linarith

end CKLaneA3W


