-- Prove2me | Definitions.Def_CK_CKLaneE_CertEP3
-- name    : CK_CKLaneE_CertEP3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T19:20:17.82367+00:00
-- url     : https://prove2.me/theorems/a38ff963-75f4-4af9-8b94-a52b67014d40
-- title:
--   Courtade–Kumar proof module `CKLaneE.CertEP3` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneE.CertEP3` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneE.CertEP3` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneE.CertEP3 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneE/CertEP3.lean)

import Definitions.Def_CK_CKLaneE_CertEP3_part00

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace CKLaneE.EP3
open GeneralCK GeneralCK.Scalar CKLaneE.FP CKLaneE.Chart CKLaneE.LS CKLaneE.DT
open CKLaneE.EP (Jlo Jlo_le pbar_nonneg)
open CKLaneE.NLS (H_le_H box_geometry)
set_option maxHeartbeats 1000000 in
theorem check_sound (B : Box3) (vS vI vc : ℚ) (mode : ℕ) (hw : check B vS vI vc mode = true) :
    Good B := by
  intro k μ hμ hin
  obtain ⟨hr1, hr2, hb1, hb2, hE1, hE2⟩ := hin
  have hab := hμ.hab
  simp only [check, Bool.and_eq_true] at hw
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hbox, _⟩, haLo⟩, haHi⟩, hb1ok⟩, hb2ok⟩, hmHi⟩, hvS⟩, hvI⟩, qIHi⟩, hvc⟩,
    qvc⟩, qK⟩, hmode⟩ := hw
  simp only [decide_eq_true_eq] at qIHi qvc qK
  have ha0 : 0 < μ.a := μ.a_interior.1
  have hb0 : 0 < μ.b := μ.b_interior.1
  have ha1 : μ.a < 1 := μ.a_interior.2
  have hb1' : μ.b < 1 := μ.b_interior.2
  have hE0 : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy; linarith [μ.e_pos, μ.f_pos]
  obtain ⟨hHaL, hHaH, hHbL, hHbH, hHmH⟩ :=
    law_H_bounds B ha0 hb0 hbox haLo haHi hb1ok hb2ok hmHi hr1 hr2 hb1 hb2
  obtain ⟨R1, _, R2, B1, _, _, _⟩ := boxOk_real hbox
  obtain ⟨_, _, _, _, gdL, gdH, _⟩ := box_geometry R1 R2 B1 hb0 hr1 hr2 hb1 hb2
  have hK0 : (0 : ℝ) ≤ ((K B : ℚ) : ℝ) := by exact_mod_cast qK
  have hKb0 := K_bound B ha0 hab hb1' hbox qK hr1 hr2 hb1 hb2 hHaL hHbL hHmH
  have hΔD0 : H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2 ≤ ((DHi B : ℚ) : ℝ) := by
    rw [c_DHi, c_CLo]; linarith
  obtain ⟨hΔDx, hKxb, hKx0⟩ := drop_bounds B hbox ha0 hab hb1' hr1 hr2 hb1 hb2 hΔD0 hK0 hKb0
  set Δ := μ.entropyDrop with hΔ
  set s := μ.meanDeficit with hs
  have hΔdef : Δ = H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2 := rfl
  rw [← hΔdef] at hΔDx hKxb
  have hsdef : s = (H μ.a + H μ.b) / 2 - μ.meanEntropy := by
    rw [hs]; unfold InteriorLaw.meanDeficit InteriorLaw.meanEntropy; ring
  have hΔ0 : 0 ≤ Δ := μ.entropyDrop_nonneg
  have hs0 : 0 ≤ s := μ.meanDeficit_mem.1
  have hs_hi : s ≤ ((sHi B : ℚ) : ℝ) := by rw [c_sHi, c_CHi, hsdef]; linarith
  have hI_hi : Δ + s ≤ ((IHi B : ℚ) : ℝ) := by rw [c_IHi, hΔdef, hsdef]; linarith
  have hIHi1 : ((IHi B : ℚ) : ℝ) < 1 := by exact_mod_cast qIHi
  have hI1 : Δ + s < 1 := lt_of_le_of_lt hI_hi hIHi1
  have htrap := P_trapezoid hs0 (le_add_of_nonneg_left hΔ0) hI1
  have hPS := anchorOk_sound hvS hs0 hs_hi
  have hPI := anchorOk_sound hvI (by linarith) hI_hi
  have hsplit : μ.splitBound ≤ Δ * ((pbar vS vI : ℚ) : ℝ) := by
    have e : μ.splitBound = P (Δ + s) - P s := rfl
    rw [e, c_pbar]
    have h1 : (Δ + s - s) = Δ := by ring
    rw [h1] at htrap
    have := mul_le_mul_of_nonneg_left (add_le_add hPS hPI) hΔ0
    linarith
  have hpbar0 := pbar_nonneg hs0 (le_add_of_nonneg_left hΔ0) hI1 hPS hPI
  have hcostF := PsiEndpointPlane.law_radial_lower μ hab
  set d := μ.b - μ.a with hd
  set E := μ.meanEntropy with hEdef
  have hd0 : 0 < d := by rw [hd]; linarith
  have hvc0 : (0 : ℝ) < vc := by exact_mod_cast (ptOk_pos hvc).1
  have hvc12 : (vc : ℝ) < 1 / 2 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr qvc
    push_cast at h; linarith
  have hFdef : F d E = d * J (radialContact d E) := by
    unfold F; rw [if_neg hd0.ne']
  have hrc0 := radialContact_pos hd0 hE0
  have hrc12 := radialContact_lt_half hd0 hE0
  obtain ⟨hHvcL, hHvcH⟩ := H_bounds hvc
  have hE2R : μ.meanEntropy ≤ (B.E2 : ℝ) := hE2
  have hE1R : (B.E1 : ℝ) ≤ μ.meanEntropy := hE1
  have hmain : Δ * ((pbar vS vI : ℚ) : ℝ) ≤ F d E := by
    by_cases hm : mode = 0
    · rw [if_pos hm] at hmode
      simp only [modeA, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hmode
      obtain ⟨⟨qdLo, qcont, qlam⟩, hacc⟩ := hmode
      have hdLoR : (0 : ℝ) < ((dLo B : ℚ) : ℝ) := by exact_mod_cast qdLo
      have hdLo_le : ((dLo B : ℚ) : ℝ) ≤ d := by rw [c_dLo]; exact gdL
      have hE2pos : (0 : ℝ) < B.E2 := lt_of_lt_of_le hE0 hE2
      -- radialContact d E ≤ vc
      have hcont : (B.E2 : ℝ) * (1 - 2 * vc) ≤ ((dLo B : ℚ) : ℝ) * H (vc : ℝ) := by
        have h := (Rat.cast_le (K := ℝ)).mpr qcont
        push_cast at h
        have := mul_le_mul_of_nonneg_left hHvcL hdLoR.le
        linarith
      have h1 : radialContact ((dLo B : ℚ) : ℝ) (B.E2 : ℝ) ≤ (vc : ℝ) :=
        (radialContact_le_iff hdLoR hE2pos hvc0.le hvc12.le).mpr hcont
      have h2 : radialContact d E ≤ radialContact ((dLo B : ℚ) : ℝ) E :=
        radialContact_anti_radius hdLoR hdLo_le hE0
      have h3 : radialContact ((dLo B : ℚ) : ℝ) E ≤ radialContact ((dLo B : ℚ) : ℝ) (B.E2 : ℝ) :=
        radialContact_mono_entropy hdLoR hE0 hE2R
      have hJ : J (vc : ℝ) ≤ J (radialContact d E) :=
        J_antitone hrc0 hvc12.le (h2.trans (h3.trans h1))
      have hJlo := Jlo_le hvc qlam
      have hJlo0 : (0 : ℝ) ≤ ((Jlo vc : ℚ) : ℝ) := by
        have : (0 : ℝ) ≤ ((lamLo vc : ℚ) : ℝ) := by exact_mod_cast qlam
        have hq : (0 : ℝ) < ((LqHi : ℚ) : ℝ) := lt_of_lt_of_le LqLo_pos
          ((log_two_mem).1.trans (log_two_mem).2)
        simp only [Jlo]; push_cast; positivity
      have hF : d * ((Jlo vc : ℚ) : ℝ) ≤ F d E := by
        rw [hFdef]
        exact mul_le_mul_of_nonneg_left (hJlo.trans hJ) hd0.le
      rcases hacc with ha | ha
      · have hA1 : ((Dx B : ℚ) : ℝ) * ((pbar vS vI : ℚ) : ℝ) ≤
            ((dLo B : ℚ) : ℝ) * ((Jlo vc : ℚ) : ℝ) := by exact_mod_cast ha
        have t1 := mul_le_mul_of_nonneg_right hΔDx hpbar0
        have t2 := mul_le_mul_of_nonneg_right hdLo_le hJlo0
        linarith
      · have qA2 := ha
        have hA2 : ((Kx B : ℚ) : ℝ) * ((dHi B : ℚ) : ℝ) * ((pbar vS vI : ℚ) : ℝ) ≤
            ((Jlo vc : ℚ) : ℝ) := by exact_mod_cast qA2
        have hdHi : d ≤ ((dHi B : ℚ) : ℝ) := by rw [c_dHi]; exact gdH
        have t1 : Δ * ((pbar vS vI : ℚ) : ℝ) ≤ ((Kx B : ℚ) : ℝ) * d ^ 2 * ((pbar vS vI : ℚ) : ℝ) :=
          mul_le_mul_of_nonneg_right hKxb hpbar0
        have t2 : ((Kx B : ℚ) : ℝ) * d ^ 2 * ((pbar vS vI : ℚ) : ℝ) ≤
            d * (((Kx B : ℚ) : ℝ) * ((dHi B : ℚ) : ℝ) * ((pbar vS vI : ℚ) : ℝ)) := by
          have : ((Kx B : ℚ) : ℝ) * d ^ 2 * ((pbar vS vI : ℚ) : ℝ) =
              d * (((Kx B : ℚ) : ℝ) * d * ((pbar vS vI : ℚ) : ℝ)) := by ring
          rw [this]
          apply mul_le_mul_of_nonneg_left _ hd0.le
          apply mul_le_mul_of_nonneg_right _ hpbar0
          exact mul_le_mul_of_nonneg_left hdHi hKx0
        have t3 := mul_le_mul_of_nonneg_left hA2 hd0.le
        linarith
    · rw [if_neg hm] at hmode
      simp only [modeB, decide_eq_true_eq] at hmode
      obtain ⟨qdHi, qcont, qB⟩ := hmode
      have hdHiR : (0 : ℝ) < ((dHi B : ℚ) : ℝ) := by exact_mod_cast qdHi
      have hdHi : d ≤ ((dHi B : ℚ) : ℝ) := by rw [c_dHi]; exact gdH
      have hE1pos : (0 : ℝ) < B.E1 := by exact_mod_cast (by
        have := hbox; simp only [boxOk, decide_eq_true_eq] at this; exact this.2.2.2.2.2.2)
      have hcont : ((dHi B : ℚ) : ℝ) * H (vc : ℝ) ≤ (B.E1 : ℝ) * (1 - 2 * vc) := by
        have h := (Rat.cast_le (K := ℝ)).mpr qcont
        push_cast at h
        have := mul_le_mul_of_nonneg_left hHvcH hdHiR.le
        linarith
      have h1 : (vc : ℝ) ≤ radialContact ((dHi B : ℚ) : ℝ) (B.E1 : ℝ) :=
        (le_radialContact_iff hdHiR hE1pos hvc0.le hvc12.le).mpr hcont
      have h2 : radialContact ((dHi B : ℚ) : ℝ) E ≤ radialContact d E :=
        radialContact_anti_radius hd0 hdHi hE0
      have h3 : radialContact ((dHi B : ℚ) : ℝ) (B.E1 : ℝ) ≤ radialContact ((dHi B : ℚ) : ℝ) E :=
        radialContact_mono_entropy hdHiR hE1pos hE1R
      set v := radialContact d E with hv
      have hvge : (vc : ℝ) ≤ v := h1.trans (h3.trans h2)
      have hHv : H (vc : ℝ) ≤ H v := H_le_H hvc0.le hvge hrc12.le
      have hlogit := logit_ge_twice_imbalance hrc0 hrc12.le
      have heq := radialContact_equation hd0 hE0
      rw [← hv] at heq
      -- F ≥ 2 d^2 H(v) / (E log 2)
      have hL := log_two_pos
      obtain ⟨_, hL2⟩ := log_two_mem
      have hFlow : 2 * d ^ 2 * H v / (E * Real.log 2) ≤ F d E := by
        rw [hFdef]
        rw [div_le_iff₀ (by positivity)]
        have : d * (2 * (1 - 2 * v)) ≤ d * (Real.log 2 * J v) :=
          mul_le_mul_of_nonneg_left hlogit hd0.le
        nlinarith [this, heq]
      have hBR : ((Kx B : ℚ) : ℝ) * ((pbar vS vI : ℚ) : ℝ) * (B.E2 : ℝ) * ((LqHi : ℚ) : ℝ) ≤
          2 * ((Hlo vc : ℚ) : ℝ) := by exact_mod_cast qB
      have hE2pos : (0 : ℝ) < B.E2 := lt_of_lt_of_le hE0 hE2
      have hLqHi : (0 : ℝ) < ((LqHi : ℚ) : ℝ) := lt_of_lt_of_le hL hL2
      -- K pbar ≤ 2 Hlo(vc)/(E2 LqHi) ≤ 2 H(v)/(E log 2)
      have hq1 : ((Kx B : ℚ) : ℝ) * ((pbar vS vI : ℚ) : ℝ) ≤
          2 * ((Hlo vc : ℚ) : ℝ) / ((B.E2 : ℝ) * ((LqHi : ℚ) : ℝ)) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      have hHlo0 : (0 : ℝ) ≤ ((Hlo vc : ℚ) : ℝ) := by
        have h0 : 0 ≤ ((Kx B : ℚ) : ℝ) * ((pbar vS vI : ℚ) : ℝ) := mul_nonneg hKx0 hpbar0
        by_contra hneg
        have hneg' : ((Hlo vc : ℚ) : ℝ) < 0 := lt_of_not_ge hneg
        have : 2 * ((Hlo vc : ℚ) : ℝ) / ((B.E2 : ℝ) * ((LqHi : ℚ) : ℝ)) < 0 :=
          div_neg_of_neg_of_pos (by linarith) (by positivity)
        linarith
      have hq2 : 2 * ((Hlo vc : ℚ) : ℝ) / ((B.E2 : ℝ) * ((LqHi : ℚ) : ℝ)) ≤
          2 * H v / (E * Real.log 2) := by
        have hHv0 : 0 ≤ H v := H_nonneg hrc0.le (by linarith [hrc12])
        apply div_le_div₀ (by linarith) (by linarith [hHvcL.trans hHv]) (by positivity)
        exact mul_le_mul hE2R hL2 hL.le hE2pos.le
      have t1 : Δ * ((pbar vS vI : ℚ) : ℝ) ≤ ((Kx B : ℚ) : ℝ) * d ^ 2 * ((pbar vS vI : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_right hKxb hpbar0
      have t2 : ((Kx B : ℚ) : ℝ) * d ^ 2 * ((pbar vS vI : ℚ) : ℝ) ≤ d ^ 2 * (2 * H v / (E * Real.log 2)) := by
        have : ((Kx B : ℚ) : ℝ) * d ^ 2 * ((pbar vS vI : ℚ) : ℝ) =
            d ^ 2 * (((Kx B : ℚ) : ℝ) * ((pbar vS vI : ℚ) : ℝ)) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left (hq1.trans hq2) (sq_nonneg d)
      have t3 : d ^ 2 * (2 * H v / (E * Real.log 2)) = 2 * d ^ 2 * H v / (E * Real.log 2) := by ring
      linarith
  exact μ.gap_le_of_splitBound hμ.hactive.le (hsplit.trans (hmain.trans hcostF))

end CKLaneE.EP3

#check @CKLaneE.EP3.check_sound
#print axioms CKLaneE.EP3.check_sound


