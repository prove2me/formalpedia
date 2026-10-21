-- Prove2me | solution 1 for AgencyPassThrough.Pricing.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T04:49:39.051866+00:00
-- url     : https://prove2.me/submissions/665cb751-18d3-45fc-bfb1-b45c28349752

import Mathlib
import Definitions.Def_AgencyPassThrough_Pricing_Model

set_option autoImplicit false

namespace AgencyPassThrough.Pricing

variable {q : ℝ → ℝ} {D : Set ℝ}

lemma p2_lam_pos (hq : DemandStanding q D) {p : ℝ} (hp : p ∈ D) : 0 < lam q p := by
  unfold lam
  exact div_pos_of_neg_of_neg (neg_neg_of_pos (hq.q_pos p hp)) (hq.A1 p hp)

lemma p2_lam_mul_dq (hq : DemandStanding q D) {p : ℝ} (hp : p ∈ D) :
    lam q p * deriv q p = -q p := by
  unfold lam
  have := (hq.A1 p hp).ne
  field_simp

lemma p2_lam_cd (hq : DemandStanding q D) : ContDiffOn ℝ 2 (lam q) D := by
  have h1 : ContDiffOn ℝ 2 (deriv q) D :=
    hq.smooth.deriv_of_isOpen hq.isOpen (by norm_num)
  have h0 : ContDiffOn ℝ 2 q D := hq.smooth.of_le (by norm_num)
  have e : lam q = fun p => -(q p) / deriv q p := rfl
  rw [e]
  exact h0.neg.div h1 (fun x hx => (hq.A1 x hx).ne)

lemma p2_dlam_cd (hq : DemandStanding q D) : ContDiffOn ℝ 1 (deriv (lam q)) D :=
  (p2_lam_cd hq).deriv_of_isOpen hq.isOpen (by norm_num)

lemma p2_q_hasDeriv (hq : DemandStanding q D) {p : ℝ} (hp : p ∈ D) :
    HasDerivAt q (deriv q p) p :=
  ((hq.smooth.differentiableOn (by norm_num)).differentiableAt
    (hq.isOpen.mem_nhds hp)).hasDerivAt

lemma p2_lam_hasDeriv (hq : DemandStanding q D) {p : ℝ} (hp : p ∈ D) :
    HasDerivAt (lam q) (deriv (lam q) p) p :=
  (((p2_lam_cd hq).differentiableOn (by norm_num)).differentiableAt
    (hq.isOpen.mem_nhds hp)).hasDerivAt

lemma p2_F_hasDeriv (hq : DemandStanding q D) {p : ℝ} (hp : p ∈ D) :
    HasDerivAt (fun x => lam q x * (2 - deriv (lam q) x))
      (deriv (fun x => lam q x * (2 - deriv (lam q) x)) p) p := by
  have hc : ContDiffOn ℝ 1 (fun x => lam q x * (2 - deriv (lam q) x)) D :=
    ((p2_lam_cd hq).of_le (by norm_num)).mul (contDiffOn_const.sub (p2_dlam_cd hq))
  exact ((hc.differentiableOn (by norm_num)).differentiableAt
    (hq.isOpen.mem_nhds hp)).hasDerivAt

/-- The comparison curve `H_θ(p) = p - c_s - λ(p) - θ λ(p) (1 - λ'(p))`. -/
noncomputable def p2_H (q : ℝ → ℝ) (cs θ : ℝ) (p : ℝ) : ℝ :=
  p - cs - (1 - θ) * lam q p - θ * (lam q p * (2 - deriv (lam q) p))

lemma p2_H_eq (q : ℝ → ℝ) (cs θ p : ℝ) :
    p2_H q cs θ p = p - cs - lam q p - θ * lam q p * (1 - deriv (lam q) p) := by
  unfold p2_H; ring

lemma p2_H_strictMono (hq : DemandStanding q D) (cs θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    StrictMonoOn (p2_H q cs θ) D := by
  have hder : ∀ p ∈ D, HasDerivAt (p2_H q cs θ)
      (1 - (1 - θ) * deriv (lam q) p
        - θ * deriv (fun x => lam q x * (2 - deriv (lam q) x)) p) p := by
    intro p hp
    have := (((hasDerivAt_id p).sub_const cs).sub
      ((p2_lam_hasDeriv hq hp).const_mul (1 - θ))).sub ((p2_F_hasDeriv hq hp).const_mul θ)
    exact this
  apply strictMonoOn_of_deriv_pos hq.ordConnected.convex
  · intro p hp; exact (hder p hp).continuousAt.continuousWithinAt
  · intro p hp
    rw [hq.isOpen.interior_eq] at hp
    rw [(hder p hp).deriv]
    have a := hq.A3_lam p hp
    have b := hq.A3_lam2 p hp
    rcases h1.lt_or_eq with h | h
    · nlinarith [mul_nonneg h0 (sub_pos.2 b).le, mul_pos (sub_pos.2 h) (sub_pos.2 a)]
    · subst h; linarith

lemma p2_mono_aux {S : Set ℝ} {f f' : ℝ → ℝ} {a b : ℝ} (hsub : Set.Icc a b ⊆ S)
    (hd : ∀ p ∈ S, HasDerivAt f (f' p) p) (hpos : ∀ p ∈ Set.Ioo a b, 0 ≤ f' p)
    (hab : a ≤ b) : f a ≤ f b := by
  have hm : MonotoneOn f (Set.Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · exact fun p hp => (hd p (hsub hp)).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      exact fun p hp =>
        (hd p (hsub (Set.Ioo_subset_Icc_self hp))).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro p hp
      rw [(hd p (hsub (Set.Ioo_subset_Icc_self hp))).deriv]
      exact hpos p hp
  exact hm ⟨le_refl a, hab⟩ ⟨hab, le_refl b⟩ hab

/-- Algebraic form of the agency equation: it is `H_{θ_B K_B}(p_B) = 0`. -/
lemma p2_algA (x cs t l e θ : ℝ) (hd : x - t * l ≠ 0) (hm : 1 - e ≠ 0)
    (h : x - cs = l + cs * t * l * (((1 - t) * l + x * (1 - e)) / (x - t * l) ^ 2)) :
    x - cs - l - θ * l * (1 - e) =
      (t * (cs / (x - t * l) / (1 - e) * (1 + (l - x * e) / (x - t * l))) - θ)
        * l * (1 - e) := by
  have e1 : x - cs - l = cs * t * l * (((1 - t) * l + x * (1 - e)) / (x - t * l) ^ 2) := by
    linarith
  rw [show x - cs - l - θ * l * (1 - e) = (x - cs - l) - θ * l * (1 - e) by ring, e1]
  field_simp
  ring

lemma p2_algP (x cs t l e : ℝ) (hcs : 0 ≤ cs) (ht0 : 0 ≤ t) (hl : 0 ≤ l) (hA4 : x * e ≤ l)
    (hd : 0 < x - t * l)
    (h : x - cs = l + cs * t * l * (((1 - t) * l + x * (1 - e)) / (x - t * l) ^ 2)) :
    l ≤ (1 - cs / (x - t * l)) * x := by
  have e1 : x - cs - l = cs * t * l * (((1 - t) * l + x * (1 - e)) / (x - t * l) ^ 2) := by
    linarith
  have key : (1 - cs / (x - t * l)) * x - l = cs * t * l * (l - x * e) / (x - t * l) ^ 2 := by
    have : (1 - cs / (x - t * l)) * x - l = (x - cs - l) + cs - cs / (x - t * l) * x := by ring
    rw [this, e1]
    field_simp
    ring
  have : 0 ≤ cs * t * l * (l - x * e) / (x - t * l) ^ 2 := by
    apply div_nonneg _ (sq_nonneg _)
    exact mul_nonneg (mul_nonneg (mul_nonneg hcs ht0) hl) (by linarith)
  linarith

lemma p2_algKB (x cs t l e : ℝ) (hx : 0 < x) (hl : 0 < l) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (he : e < 1) (hA4 : x * e ≤ l) (hd : 0 < x - t * l)
    (h : x - cs = l + cs * t * l * (((1 - t) * l + x * (1 - e)) / (x - t * l) ^ 2)) :
    cs / (x - t * l) / (1 - e) * (1 + (l - x * e) / (x - t * l)) ≤ 1 := by
  set d := x - t * l with hdd
  set N := (1 - t) * l + x * (1 - e) with hN
  have hm : 0 < 1 - e := by linarith
  have hNpos : 0 < N := by
    rw [hN]; have : 0 ≤ (1 - t) * l := mul_nonneg (by linarith) hl.le
    nlinarith [mul_pos hx hm]
  have hK : cs / d / (1 - e) * (1 + (l - x * e) / d) = cs * N / (d ^ 2 * (1 - e)) := by
    have hd0 : d ≠ 0 := hd.ne'
    have hm0 : 1 - e ≠ 0 := hm.ne'
    rw [hN]; field_simp; rw [hdd]; ring
  rw [hK, div_le_one (by positivity)]
  have hE : cs * (d ^ 2 + t * l * N) = (x - l) * d ^ 2 := by
    have e1 : x - l - cs = cs * t * l * (N / d ^ 2) := by linarith
    field_simp at e1
    linarith
  have hP : 0 < d ^ 2 + t * l * N := by positivity
  have h3 : (x - l) * N - (1 - e) * (d ^ 2 + t * l * N) = -((l - x * e) * l * (1 - t * e)) := by
    rw [hN, hdd]; ring
  have h4 : 0 ≤ (l - x * e) * l * (1 - t * e) := by
    apply mul_nonneg (mul_nonneg (by linarith) hl.le)
    rcases le_or_gt e 0 with h5 | h5
    · nlinarith
    · nlinarith
  by_contra hc
  push Not at hc
  have h1 : d ^ 2 * (1 - e) * (d ^ 2 + t * l * N) < cs * N * (d ^ 2 + t * l * N) :=
    mul_lt_mul_of_pos_right hc hP
  have h2 : cs * N * (d ^ 2 + t * l * N) = (x - l) * d ^ 2 * N := by
    rw [← hE]; ring
  have h6 : 0 ≤ d ^ 2 * ((l - x * e) * l * (1 - t * e)) := mul_nonneg (sq_nonneg d) h4
  have h7 : d ^ 2 * ((x - l) * N - (1 - e) * (d ^ 2 + t * l * N)) =
      -(d ^ 2 * ((l - x * e) * l * (1 - t * e))) := by rw [h3]; ring
  nlinarith

end AgencyPassThrough.Pricing

open AgencyPassThrough.Pricing in
theorem solution (q : ℝ → ℝ) (D : Set ℝ) (hq : DemandStanding q D)
    (n : ℕ) (hn : 2 ≤ n) (cs eps a b pW pB : ℝ)
    (hcs : 0 ≤ cs) (heps0 : 0 ≤ eps) (heps1 : eps < 1)
    (hab : 0 < a - eps * b)
    (hdpdw : a + ((n : ℝ) - 1) * b = 1 / (1 - deriv (lam q) pW))
    (hθW0 : 0 ≤ thetaW n eps a b) (hθW1 : thetaW n eps a b ≤ 1)
    (hW : IsWholesaleEq q D cs (thetaW n eps a b) pW)
    (hB : IsAgencyEq q D cs (thetaB eps) pB) :
    (0 ≤ b → pB ≤ pW ∧
      piWr n q pW ≤ piBr n q cs (thetaB eps) pB ∧
      piBi q cs (thetaB eps) pB ≤ piWi q cs pW) ∧
    (b < 0 → (pW < pB ↔
      thetaW n eps a b < thetaB eps * min (KB q cs (thetaB eps) pB) 1)) := by
  obtain ⟨hpW, hWe⟩ := hW
  obtain ⟨hpB, hd, hBe⟩ := hB
  have ht : thetaB eps = 1 - eps := rfl
  have ht0 : 0 < thetaB eps := by rw [ht]; linarith
  have ht1 : thetaB eps ≤ 1 := by rw [ht]; linarith
  have hlB := p2_lam_pos hq hpB
  have hlW := p2_lam_pos hq hpW
  have hmB : 0 < 1 - deriv (lam q) pB := by linarith [hq.A3_lam pB hpB]
  have hmW : 0 < 1 - deriv (lam q) pW := by linarith [hq.A3_lam pW hpW]
  have hxB : 0 < pB := hq.pos hpB
  have hA4B := hq.A4 pB hpB
  have hKB1 : KB q cs (thetaB eps) pB ≤ 1 := by
    unfold KB alphaB
    exact p2_algKB pB cs (thetaB eps) (lam q pB) (deriv (lam q) pB) hxB hlB ht0 ht1
      (by linarith) hA4B hd hBe
  have hmin : min (KB q cs (thetaB eps) pB) 1 = KB q cs (thetaB eps) pB := min_eq_left hKB1
  set θW := thetaW n eps a b with hθW
  have hHW : p2_H q cs θW pW = 0 := by rw [p2_H_eq]; linarith
  have hHB : p2_H q cs θW pB = (thetaB eps * KB q cs (thetaB eps) pB - θW)
      * lam q pB * (1 - deriv (lam q) pB) := by
    rw [p2_H_eq]
    unfold KB alphaB
    exact p2_algA pB cs (thetaB eps) (lam q pB) (deriv (lam q) pB) θW hd.ne' hmB.ne' hBe
  have hmono := p2_H_strictMono hq cs θW hθW0 hθW1
  have hlm : 0 < lam q pB * (1 - deriv (lam q) pB) := mul_pos hlB hmB
  have hB2 : 0 ≤ 1 - eps := by linarith
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · -- part (i)
    have hθ : thetaB eps ≤ θW := by
      rw [hθW, ht]; unfold thetaW
      rw [le_div_iff₀ hab]
      nlinarith [mul_nonneg hB2 (mul_nonneg (by linarith : (0:ℝ) ≤ (n:ℝ) - 1 + eps) hb)]
    have hθ' : thetaB eps * KB q cs (thetaB eps) pB ≤ θW := by
      nlinarith [mul_le_mul_of_nonneg_left hKB1 ht0.le]
    have hle : pB ≤ pW := by
      rw [← hmono.le_iff_le hpB hpW, hHW, hHB]
      have := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hθ') hlm.le
      linarith [this, show (thetaB eps * KB q cs (thetaB eps) pB - θW) * lam q pB
        * (1 - deriv (lam q) pB) = (thetaB eps * KB q cs (thetaB eps) pB - θW)
        * (lam q pB * (1 - deriv (lam q) pB)) by ring]
    have hsub : Set.Icc pB pW ⊆ D := hq.ordConnected.out hpB hpW
    have hP := p2_algP pB cs (thetaB eps) (lam q pB) (deriv (lam q) pB) hcs ht0.le hlB.le hA4B
      hd hBe
    have hqB := hq.q_pos pB hpB
    refine ⟨hle, ?_, ?_⟩
    · -- retailer profit
      -- piTilde is antitone
      have hT : lam q pW * q pW ≤ lam q pB * q pB := by
        have := p2_mono_aux (f := fun p => -(lam q p * q p))
          (f' := fun p => -(deriv (lam q) p * q p + lam q p * deriv q p)) hsub
          (fun p hp => ((p2_lam_hasDeriv hq hp).mul (p2_q_hasDeriv hq hp)).neg)
          (fun p hp => by
            have hp' := hsub (Set.Ioo_subset_Icc_self hp)
            have h1 := p2_lam_mul_dq hq hp'
            have h2 := hq.q_pos p hp'
            have h3 := hq.A3_lam p hp'
            rw [h1]
            nlinarith [mul_pos (sub_pos.2 h3) h2]) hle
        linarith
      unfold piWr piBr wW
      have hn0 : (0 : ℝ) ≤ n := by linarith
      have h2 : lam q pB * q pB ≤ (1 - alphaB q cs (thetaB eps) pB) * pB * q pB := by
        unfold alphaB
        exact mul_le_mul_of_nonneg_right hP hqB.le
      have : (pW - (pW - lam q pW)) * q pW ≤ (1 - alphaB q cs (thetaB eps) pB) * pB * q pB := by
        rw [show pW - (pW - lam q pW) = lam q pW by ring]; linarith
      calc (n : ℝ) * (pW - (pW - lam q pW)) * q pW
          = (n : ℝ) * ((pW - (pW - lam q pW)) * q pW) := by ring
        _ ≤ (n : ℝ) * ((1 - alphaB q cs (thetaB eps) pB) * pB * q pB) :=
          mul_le_mul_of_nonneg_left this hn0
        _ = (n : ℝ) * ((1 - alphaB q cs (thetaB eps) pB) * pB) * q pB := by ring
    · -- supplier profit
      have hH1W : p2_H q cs 1 pW ≤ 0 := by
        rw [p2_H_eq]
        have : pW - cs - lam q pW = θW * lam q pW * (1 - deriv (lam q) pW) := by linarith
        nlinarith [mul_pos hlW hmW]
      have hDot : (pB - cs - lam q pB) * q pB ≤ (pW - cs - lam q pW) * q pW := by
        have := p2_mono_aux (f := fun p => (p - cs - lam q p) * q p)
          (f' := fun p => (1 - deriv (lam q) p) * q p + (p - cs - lam q p) * deriv q p) hsub
          (fun p hp => (((hasDerivAt_id p).sub_const cs).sub (p2_lam_hasDeriv hq hp)).mul
            (p2_q_hasDeriv hq hp))
          (fun p hp => by
            have hp' := hsub (Set.Ioo_subset_Icc_self hp)
            have h1 := p2_lam_mul_dq hq hp'
            have hdq := hq.A1 p hp'
            have hH : p2_H q cs 1 p ≤ 0 := by
              have := hmono
              have hlt : p2_H q cs 1 p < p2_H q cs 1 pW :=
                (p2_H_strictMono hq cs 1 zero_le_one le_rfl) hp' hpW hp.2
              linarith
            rw [p2_H_eq] at hH
            have e : (1 - deriv (lam q) p) * q p + (p - cs - lam q p) * deriv q p
                = deriv q p * (p - cs - lam q p - 1 * lam q p * (1 - deriv (lam q) p)) := by
              have hq' : q p = -(lam q p * deriv q p) := by linarith
              rw [hq']; ring
            rw [e]
            exact mul_nonneg_of_nonpos_of_nonpos hdq.le hH) hle
        simpa using this
      unfold piBi piWi wW
      have h2 : (alphaB q cs (thetaB eps) pB * pB - cs) * q pB ≤ (pB - cs - lam q pB) * q pB := by
        apply mul_le_mul_of_nonneg_right _ hqB.le
        unfold alphaB
        have : cs / (pB - thetaB eps * lam q pB) * pB = pB - (1 - cs / (pB - thetaB eps * lam q pB)) * pB := by ring
        linarith
      have e3 : (pW - lam q pW - cs) * q pW = (pW - cs - lam q pW) * q pW := by ring
      linarith
  · -- part (ii)
    rw [hmin]
    rw [← hmono.lt_iff_lt hpW hpB, hHW, hHB, mul_assoc, mul_pos_iff_of_pos_right hlm, sub_pos]
