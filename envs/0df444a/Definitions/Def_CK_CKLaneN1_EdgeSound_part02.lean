-- Prove2me | Definitions.Def_CK_CKLaneN1_EdgeSound_part02
-- name    : CK_CKLaneN1_EdgeSound_part02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T17:59:32.579755+00:00
-- url     : https://prove2.me/theorems/55cc4ff3-9b71-4998-83e1-b1beb348c811
-- title:
--   Courtade–Kumar proof module `CKLaneN1.EdgeSound (part 3 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.EdgeSound (part 3 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.EdgeSound (part 3 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.EdgeSound (part 3 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/EdgeSound (part 3 of 5).lean)

import Definitions.Def_CK_CKLaneN1_EdgeSound_part01
set_option autoImplicit false
set_option autoImplicit false
namespace CKLaneN1.Edge
open GeneralCK CKLaneE.FP CKLaneN1.Capital Set
/-- Normalized entropy-Jensen bound. -/
theorem jensen_gap_le {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1 / 2) :
    a + b - 2 * entropyInverse ((H a + H b) / 2) ≤
      ((a + b) / 2 * Cfun ((b - a) / (a + b)) +
        (1 - (a + b) / 2) * Cfun ((b - a) / (2 * (1 - (a + b) / 2)))) /
        (Real.log 2 * J ((a + b) / 2)) := by
  obtain ⟨-, -, hq, -⟩ := q_facts ha hab.le hb
  have hJ : 0 < J ((a + b) / 2) := J_pos (by linarith) (by linarith)
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hJH := JH_eq ha hab (by linarith)
  rw [hJH] at hq
  rw [le_div_iff₀ (mul_pos hL hJ)]
  have := mul_le_mul_of_nonneg_left hq (show (0 : ℝ) ≤ 2 * Real.log 2 by linarith)
  have e : 2 * Real.log 2 * (((a + b) / 2 * Cfun ((b - a) / (a + b)) +
      (1 - (a + b) / 2) * Cfun ((b - a) / (2 * (1 - (a + b) / 2)))) / (2 * Real.log 2)) =
      (a + b) / 2 * Cfun ((b - a) / (a + b)) +
      (1 - (a + b) / 2) * Cfun ((b - a) / (2 * (1 - (a + b) / 2))) := by
    field_simp
  rw [e] at this
  nlinarith

/-! ## Variant term bounds -/

section Terms

variable {a b y z : ℝ}

/-- Interior-cost term. -/
theorem T2_sound {B : B3} {w : EWit} (hV : eVarOK B w = true) (ha : 0 < a) (hab : a < b)
    (hb : b < 1 / 2) (hy : 0 < y) (hd : b - a = z * y) (hz : 0 ≤ z)
    (hM1 : (a + b) / 2 ≤ ((eM1 B : ℚ) : ℝ)) (ha1 : a ≤ ((ea1 B : ℚ) : ℝ))
    (ha1' : ((ea1 B : ℚ) : ℝ) < 1) (hb0 : ((eb0 B : ℚ) : ℝ) ≤ b) (hb0' : 0 < ((eb0 B : ℚ) : ℝ))
    (hb0p : ptOk (eb0 B) = true) (hy1 : y ≤ ((ey1 B : ℚ) : ℝ)) :
    y ^ 2 * (((eT2 B w).1 : ℝ) * z + ((eT2 B w).2 : ℝ) * z ^ 2) ≤ interiorCost a b := by
  have hL := log_two_mem
  have hL0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  cases hk : w.k2
  · simp only [eT2, hk, Bool.false_eq_true, if_false]
    have hj := interiorCost_ge ha hab (by linarith)
    have hden : 0 < (a + b) * Real.log 2 := mul_pos (by linarith) hL0
    have hden2 : (a + b) * Real.log 2 ≤ 2 * ((eM1 B : ℚ) : ℝ) * ((LqHi : ℚ) : ℝ) := by
      have h1 : a + b ≤ 2 * ((eM1 B : ℚ) : ℝ) := by linarith
      exact mul_le_mul h1 hL.2 hL0.le (by linarith)
    have hmono : (b - a) ^ 2 / (2 * ((eM1 B : ℚ) : ℝ) * ((LqHi : ℚ) : ℝ)) ≤
        (b - a) ^ 2 / ((a + b) * Real.log 2) :=
      div_le_div_of_nonneg_left (sq_nonneg _) hden hden2
    have e : y ^ 2 * (((0 : ℚ) : ℝ) * z + ((1 / (2 * eM1 B * LqHi) : ℚ) : ℝ) * z ^ 2) =
        (b - a) ^ 2 / (2 * ((eM1 B : ℚ) : ℝ) * ((LqHi : ℚ) : ℝ)) := by
      rw [hd]
      push_cast
      ring
    rw [e]
    linarith
  · simp only [eT2, hk, if_true]
    simp only [eVarOK, hk, if_true, Bool.and_eq_true, decide_eq_true_eq] at hV
    obtain ⟨⟨⟨⟨⟨hpa1, hlam⟩, hD⟩, hy1pos⟩, -⟩, -⟩ := hV
    have hJa : ((lamLo (ea1 B) : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ) ≤ J a :=
      (J_ge hpa1 hlam).trans (J_anti ha ha1 ha1')
    have hJb : J b ≤ ((lamHi (eb0 B) : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ) :=
      (J_anti hb0' hb0 (by linarith)).trans (J_le hb0p (by linarith))
    have hDR : (0 : ℝ) ≤ ((eDelta B : ℚ) : ℝ) := by exact_mod_cast hD
    have hDle : ((eDelta B : ℚ) : ℝ) ≤ J a - J b := by
      simp only [eDelta]
      push_cast
      linarith
    have hy1p : (0 : ℝ) < ((ey1 B : ℚ) : ℝ) := by exact_mod_cast hy1pos
    unfold interiorCost
    rw [hd]
    have h1 : z * y * ((eDelta B : ℚ) : ℝ) / 2 ≤ z * y * (J a - J b) / 2 := by
      have := mul_le_mul_of_nonneg_left hDle (mul_nonneg hz hy.le)
      linarith
    have h2 : y ^ 2 * (((eDelta B / (2 * ey1 B) : ℚ) : ℝ) * z + ((0 : ℚ) : ℝ) * z ^ 2) ≤
        z * y * ((eDelta B : ℚ) : ℝ) / 2 := by
      push_cast
      rw [show y ^ 2 * (((eDelta B : ℚ) : ℝ) / (2 * ((ey1 B : ℚ) : ℝ)) * z + 0 * z ^ 2) =
        z * y * ((eDelta B : ℚ) : ℝ) / 2 * (y / ((ey1 B : ℚ) : ℝ)) by field_simp; ring]
      have hr : y / ((ey1 B : ℚ) : ℝ) ≤ 1 := by rw [div_le_one hy1p]; exact hy1
      have hnn : 0 ≤ z * y * ((eDelta B : ℚ) : ℝ) / 2 := by positivity
      nlinarith
    linarith

/-- Algebra of the normalized Jensen variant. -/
theorem jensen_alg_norm {g M ρ ρ' Cρ Cρ' D L JM Chi CH M0 M1 Lq J1 : ℝ}
    (hg : g ≤ (M * Cρ + (1 - M) * Cρ') / (L * JM))
    (hCρ : Cρ ≤ ρ ^ 2 * Chi) (hCρ' : Cρ' ≤ ρ' ^ 2 * CH)
    (eρ : M * ρ ^ 2 = D / (4 * M)) (eρ' : (1 - M) * ρ' ^ 2 = D / (4 * (1 - M)))
    (hD : 0 ≤ D) (hM0 : 0 < M0) (hM0M : M0 ≤ M) (hMM1 : M ≤ M1) (hM1 : M1 < 1)
    (hLq : 0 < Lq) (hLqL : Lq ≤ L) (hJ1 : 0 < J1) (hJ1J : J1 ≤ JM)
    (hChi : 0 ≤ Chi) (hCH : 0 ≤ CH) :
    g ≤ D * (Chi / M0 + CH / (1 - M1)) / (4 * (Lq * J1)) := by
  have hMpos : 0 < M := lt_of_lt_of_le hM0 hM0M
  have h1M : 0 < 1 - M := by linarith
  have h1M1 : 0 < 1 - M1 := by linarith
  have hN : M * Cρ + (1 - M) * Cρ' ≤ D * (Chi / M0 + CH / (1 - M1)) / 4 := by
    have a1 : M * Cρ ≤ M * (ρ ^ 2 * Chi) := mul_le_mul_of_nonneg_left hCρ hMpos.le
    have a2 : (1 - M) * Cρ' ≤ (1 - M) * (ρ' ^ 2 * CH) := mul_le_mul_of_nonneg_left hCρ' h1M.le
    have a3 : M * (ρ ^ 2 * Chi) = D / (4 * M) * Chi := by rw [← eρ]; ring
    have a4 : (1 - M) * (ρ' ^ 2 * CH) = D / (4 * (1 - M)) * CH := by rw [← eρ']; ring
    have a5 : D / (4 * M) * Chi ≤ D / (4 * M0) * Chi :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hD (by positivity) (by linarith)) hChi
    have a6 : D / (4 * (1 - M)) * CH ≤ D / (4 * (1 - M1)) * CH :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hD (by linarith) (by linarith)) hCH
    have a7 : D / (4 * M0) * Chi + D / (4 * (1 - M1)) * CH = D * (Chi / M0 + CH / (1 - M1)) / 4 := by
      field_simp
    linarith
  have hN' : 0 ≤ D * (Chi / M0 + CH / (1 - M1)) / 4 :=
    div_nonneg (mul_nonneg hD (add_nonneg (div_nonneg hChi hM0.le) (div_nonneg hCH h1M1.le)))
      (by norm_num)
  have hLJ : 0 < L * JM := mul_pos (by linarith) (by linarith)
  have hLJ' : Lq * J1 ≤ L * JM := mul_le_mul hLqL hJ1J hJ1.le (by linarith)
  calc g ≤ (M * Cρ + (1 - M) * Cρ') / (L * JM) := hg
    _ ≤ D * (Chi / M0 + CH / (1 - M1)) / 4 / (L * JM) := div_le_div_of_nonneg_right hN hLJ.le
    _ ≤ D * (Chi / M0 + CH / (1 - M1)) / 4 / (Lq * J1) :=
        div_le_div_of_nonneg_left hN' (mul_pos hLq hJ1) hLJ'
    _ = D * (Chi / M0 + CH / (1 - M1)) / (4 * (Lq * J1)) := by rw [div_div]

/-- Algebra of the direct Jensen variant. -/
theorem jensen_alg_direct {g M Cρ Cρ' L JM CH M0 M1 Lq Lh J1 R : ℝ}
    (hg : g ≤ (M * Cρ + (1 - M) * Cρ') / (L * JM))
    (hCρ : Cρ ≤ 2 * L) (hCρ' : Cρ' ≤ R ^ 2 * CH)
    (hM0M : M0 ≤ M) (hMM1 : M ≤ M1) (hMpos : 0 < M) (hM1 : M < 1)
    (hLq : 0 < Lq) (hLqL : Lq ≤ L) (hLLh : L ≤ Lh) (hJ1 : 0 < J1) (hJ1J : J1 ≤ JM)
    (hCH : 0 ≤ CH) :
    g ≤ (M1 * (2 * Lh) + (1 - M0) * R ^ 2 * CH) / (Lq * J1) := by
  have h1M : 0 < 1 - M := by linarith
  have hN : M * Cρ + (1 - M) * Cρ' ≤ M1 * (2 * Lh) + (1 - M0) * R ^ 2 * CH := by
    have a1 : M * Cρ ≤ M1 * (2 * Lh) := by
      calc M * Cρ ≤ M * (2 * L) := mul_le_mul_of_nonneg_left hCρ hMpos.le
        _ ≤ M1 * (2 * Lh) := mul_le_mul hMM1 (by linarith) (by linarith) (by linarith)
    have a2 : (1 - M) * Cρ' ≤ (1 - M0) * R ^ 2 * CH := by
      calc (1 - M) * Cρ' ≤ (1 - M) * (R ^ 2 * CH) := mul_le_mul_of_nonneg_left hCρ' h1M.le
        _ ≤ (1 - M0) * (R ^ 2 * CH) :=
            mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (sq_nonneg R) hCH)
        _ = (1 - M0) * R ^ 2 * CH := by ring
    linarith
  have hN' : 0 ≤ M1 * (2 * Lh) + (1 - M0) * R ^ 2 * CH := by
    have : 0 ≤ M1 := by linarith
    have : 0 ≤ Lh := by linarith
    have : 0 ≤ 1 - M0 := by linarith
    positivity
  have hLJ : 0 < L * JM := mul_pos (by linarith) (by linarith)
  have hLJ' : Lq * J1 ≤ L * JM := mul_le_mul hLqL hJ1J hJ1.le (by linarith)
  calc g ≤ (M * Cρ + (1 - M) * Cρ') / (L * JM) := hg
    _ ≤ (M1 * (2 * Lh) + (1 - M0) * R ^ 2 * CH) / (L * JM) := div_le_div_of_nonneg_right hN hLJ.le
    _ ≤ (M1 * (2 * Lh) + (1 - M0) * R ^ 2 * CH) / (Lq * J1) :=
        div_le_div_of_nonneg_left hN' (mul_pos hLq hJ1) hLJ'

set_option maxHeartbeats 1000000 in
/-- Entropy-Jensen term. Here `g = a + b - 2q` and `Θq = Θ(X_q)`. -/
theorem T3_sound {B : B3} {w : EWit} (hV : eVarOK B w = true) (ha : 0 < a) (hab : a < b)
    (hb : b < 1 / 2) (hy : 0 < y) (hd : b - a = z * y)
    {Θq : ℝ} (hΘ0 : 0 ≤ Θq) (hΘ1 : Θq ≤ ((slopeHi w.v2 : ℚ) : ℝ))
    (hM0 : ((eM0 B : ℚ) : ℝ) ≤ (a + b) / 2) (hM0p : 0 < ((eM0 B : ℚ) : ℝ))
    (hM1 : (a + b) / 2 ≤ ((eM1 B : ℚ) : ℝ)) (hM1l : ((eM1 B : ℚ) : ℝ) < 1 / 2)
    (hJM : ((eJM1 B : ℚ) : ℝ) ≤ J ((a + b) / 2)) (hJMp : 0 < ((eJM1 B : ℚ) : ℝ))
    (hrho : (b - a) / (a + b) ≤ ((erho1 B : ℚ) : ℝ))
    (hrhop : (b - a) / (2 * (1 - (a + b) / 2)) ≤ ((erhop1 B : ℚ) : ℝ))
    (hrhop2 : ((erhop1 B : ℚ) : ℝ) ≤ 1 / 2) (hy0 : ((ey0 B : ℚ) : ℝ) ≤ y) :
    (a + b - 2 * entropyInverse ((H a + H b) / 2)) * Θq ≤
      y ^ 2 * (((eT3 B w).1 : ℝ) + ((eT3 B w).2 : ℝ) * z ^ 2) := by
  have hL := log_two_mem
  have hL0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLq : (0 : ℝ) < ((LqLo : ℚ) : ℝ) := LqLo_pos
  have hs : 0 < a + b := by linarith
  have hMpos : 0 < (a + b) / 2 := by linarith
  have hM1' : 0 < 1 - (a + b) / 2 := by linarith
  have hρpos : 0 < (b - a) / (a + b) := div_pos (by linarith) hs
  have hρ1 : (b - a) / (a + b) ≤ 1 := by rw [div_le_one hs]; linarith
  have hρ'pos : 0 < (b - a) / (2 * (1 - (a + b) / 2)) := div_pos (by linarith) (by linarith)
  have hq := q_facts ha hab.le hb
  have hg0 : 0 ≤ a + b - 2 * entropyInverse ((H a + H b) / 2) := by linarith [hq.2.1]
  have hJ := jensen_gap_le ha hab hb
  have hCρ' := Cfun_le_CH hρ'pos (hrhop.trans hrhop2)
  have hCH0 : (0 : ℝ) ≤ ((CHq : ℚ) : ℝ) := by norm_num [CHq]
  have hΘ1' : 0 ≤ ((slopeHi w.v2 : ℚ) : ℝ) := hΘ0.trans hΘ1
  have hgΘ : (a + b - 2 * entropyInverse ((H a + H b) / 2)) * Θq ≤
      (a + b - 2 * entropyInverse ((H a + H b) / 2)) * ((slopeHi w.v2 : ℚ) : ℝ) :=
    mul_le_mul_of_nonneg_left hΘ1 hg0
  have eMρ : (a + b) / 2 * ((b - a) / (a + b)) ^ 2 = (b - a) ^ 2 / (4 * ((a + b) / 2)) := by
    field_simp; ring
  have eMρ' : (1 - (a + b) / 2) * ((b - a) / (2 * (1 - (a + b) / 2))) ^ 2 =
      (b - a) ^ 2 / (4 * (1 - (a + b) / 2)) := by
    field_simp; ring
  cases hk : w.k3
  · simp only [eT3, hk, Bool.false_eq_true, if_false]
    simp only [eVarOK, hk, Bool.false_eq_true, if_false, Bool.and_eq_true, decide_eq_true_eq]
      at hV
    obtain ⟨⟨-, ⟨⟨⟨⟨hr0, hr1⟩, hpr⟩, hpr2⟩, hchi⟩⟩, -⟩ := hV
    have hr0R : (0 : ℝ) < ((erho1 B : ℚ) : ℝ) := by exact_mod_cast hr0
    have hr1R : ((erho1 B : ℚ) : ℝ) < 1 := by exact_mod_cast hr1
    have hchiR : (0 : ℝ) ≤ ((eChi1 B : ℚ) : ℝ) := by exact_mod_cast hchi
    have hCmono := Chat_mono hρpos hrho hr1R
    have hCle := Cfun_le_Chi hr0 hr1 hpr hpr2
    have hChiE : ((eChi1 B : ℚ) : ℝ) * ((erho1 B : ℚ) : ℝ) ^ 2 =
        (1 + ((erho1 B : ℚ) : ℝ)) * (-((l1Lo (erho1 B / (1 + erho1 B)) : ℚ) : ℝ)) +
          (1 - ((erho1 B : ℚ) : ℝ)) * ((l1Hi (erho1 B) : ℚ) : ℝ) := by
      simp only [eChi1]
      push_cast
      field_simp
    have hCρ : Cfun ((b - a) / (a + b)) ≤ ((b - a) / (a + b)) ^ 2 * ((eChi1 B : ℚ) : ℝ) := by
      have hr2 : 0 < ((erho1 B : ℚ) : ℝ) ^ 2 := by positivity
      have h1 : Cfun ((b - a) / (a + b)) * ((erho1 B : ℚ) : ℝ) ^ 2 ≤
          ((b - a) / (a + b)) ^ 2 * ((eChi1 B : ℚ) : ℝ) * ((erho1 B : ℚ) : ℝ) ^ 2 := by
        have h2 : Cfun (((erho1 B : ℚ) : ℝ)) * ((b - a) / (a + b)) ^ 2 ≤
            ((eChi1 B : ℚ) : ℝ) * ((erho1 B : ℚ) : ℝ) ^ 2 * ((b - a) / (a + b)) ^ 2 := by
          rw [hChiE]
          exact mul_le_mul_of_nonneg_right hCle (sq_nonneg _)
        nlinarith
      exact le_of_mul_le_mul_right h1 hr2
    have hg := jensen_alg_norm hJ hCρ hCρ' eMρ eMρ' (sq_nonneg _) hM0p hM0 hM1 (by linarith)
      hLq hL.1 hJMp hJM hchiR hCH0
    have e : y ^ 2 * (((0 : ℚ) : ℝ) + ((slopeHi w.v2 * exi B : ℚ) : ℝ) * z ^ 2) =
        (b - a) ^ 2 * (((eChi1 B : ℚ) : ℝ) / ((eM0 B : ℚ) : ℝ) +
          ((CHq : ℚ) : ℝ) / (1 - ((eM1 B : ℚ) : ℝ))) /
          (4 * (((LqLo : ℚ) : ℝ) * ((eJM1 B : ℚ) : ℝ))) * ((slopeHi w.v2 : ℚ) : ℝ) := by
      rw [hd]
      simp only [exi]
      push_cast
      ring
    rw [e]
    exact hgΘ.trans (mul_le_mul_of_nonneg_right hg hΘ1')
  · simp only [eT3, hk, if_true]
    simp only [eVarOK, hk, if_true, Bool.and_eq_true, decide_eq_true_eq] at hV
    obtain ⟨⟨-, hy0p⟩, -⟩ := hV
    have hy0R : (0 : ℝ) < ((ey0 B : ℚ) : ℝ) := by exact_mod_cast hy0p
    have hCρ := Cfun_le_two_log_two hρpos.le hρ1
    have hCρ'' : Cfun ((b - a) / (2 * (1 - (a + b) / 2))) ≤
        ((erhop1 B : ℚ) : ℝ) ^ 2 * ((CHq : ℚ) : ℝ) :=
      hCρ'.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hρ'pos.le hrhop 2) hCH0)
    have hg := jensen_alg_direct hJ hCρ hCρ'' hM0 hM1 hMpos (by linarith) hLq hL.1 hL.2 hJMp hJM
      hCH0
    set G := ((eM1 B : ℚ) : ℝ) * (2 * ((LqHi : ℚ) : ℝ)) +
      (1 - ((eM0 B : ℚ) : ℝ)) * ((erhop1 B : ℚ) : ℝ) ^ 2 * ((CHq : ℚ) : ℝ) with hG
    have hGd : 0 ≤ G / (((LqLo : ℚ) : ℝ) * ((eJM1 B : ℚ) : ℝ)) := hg0.trans hg
    have hyy : 1 ≤ y ^ 2 / ((ey0 B : ℚ) : ℝ) ^ 2 := by
      rw [le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_left₀ hy0R.le hy0 2
    have e : y ^ 2 * (((slopeHi w.v2 * (eM1 B * (2 * LqHi) + (1 - eM0 B) * erhop1 B ^ 2 * CHq) /
        (LqLo * eJM1 B * ey0 B ^ 2) : ℚ) : ℝ) + ((0 : ℚ) : ℝ) * z ^ 2) =
        y ^ 2 / ((ey0 B : ℚ) : ℝ) ^ 2 * (G / (((LqLo : ℚ) : ℝ) * ((eJM1 B : ℚ) : ℝ))) *
          ((slopeHi w.v2 : ℚ) : ℝ) := by
      have hLqne : ((LqLo : ℚ) : ℝ) ≠ 0 := hLq.ne'
      have hJne : ((eJM1 B : ℚ) : ℝ) ≠ 0 := hJMp.ne'
      have hy0ne : ((ey0 B : ℚ) : ℝ) ≠ 0 := hy0R.ne'
      rw [hG]
      push_cast
      field_simp
      ring
    refine le_of_le_of_eq ?_ e.symm
    have h1 := mul_le_mul_of_nonneg_right hg hΘ1'
    have h2 : G / (((LqLo : ℚ) : ℝ) * ((eJM1 B : ℚ) : ℝ)) * ((slopeHi w.v2 : ℚ) : ℝ) ≤
        y ^ 2 / ((ey0 B : ℚ) : ℝ) ^ 2 * (G / (((LqLo : ℚ) : ℝ) * ((eJM1 B : ℚ) : ℝ))) *
          ((slopeHi w.v2 : ℚ) : ℝ) := by
      have := mul_le_mul_of_nonneg_right hyy (mul_nonneg hGd hΘ1')
      linarith
    linarith

/-- Algebra of the outer tangent term. -/
theorem T4_alg_norm {cb y z Θd c4 g : ℝ} (hcb : cb = y * (1 - z)) (hcb0 : 0 ≤ cb)
    (hΘ : Θd ≤ 81 / 50 * (y * c4 + z * y * g)) :
    cb * Θd ≤ y ^ 2 * (81 / 50 * c4 + 81 / 50 * (g - c4) * z + -(81 / 50 * g) * z ^ 2) := by
  have h := mul_le_mul_of_nonneg_left hΘ hcb0
  have e : cb * (81 / 50 * (y * c4 + z * y * g)) =
      y ^ 2 * (81 / 50 * c4 + 81 / 50 * (g - c4) * z + -(81 / 50 * g) * z ^ 2) := by
    rw [hcb]; ring
  linarith
end Terms
end CKLaneN1.Edge


