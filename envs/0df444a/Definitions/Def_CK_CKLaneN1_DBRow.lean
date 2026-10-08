-- Prove2me | Definitions.Def_CK_CKLaneN1_DBRow
-- name    : CK_CKLaneN1_DBRow
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-05T18:25:14.95942+00:00
-- url     : https://prove2.me/theorems/3d3d8fe8-9543-4479-9f5d-c0da6d4d6581
-- title:
--   Courtade–Kumar proof module `CKLaneN1.DBRow` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.DBRow` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.DBRow` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.DBRow (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/DBRow.lean)

import Definitions.Def_CK_CKLaneN1_DBSound

-- ===== source module CKLaneN1.DBRow =====
section

/-!
# Lane N1: NO_SEP §6 leaf soundness and the row `NoSepA_ModerateRest` (conditional on the tree check)
-/

namespace CKLaneN1

open GeneralCK GeneralCK.Scalar CKLaneE.FP Set

/-- §6 leaves other than prior-cap (153 normalized-endpoint + 140 normalized-log-sum); the 32
prior-cap leaves have `I_+ ≤ 3/40`, hence `s ≤ 3/40`.
(Verbatim copy of `CKLaneN23.NoSepA_ModerateRest`.) -/
def NoSepA_ModerateRest : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 9 / 10 → μ.b - μ.a ≤ 1 / 50 →
    11 / 200 ≤ μ.meanEntropy → 3 / 40 < (H μ.a + H μ.b) / 2 - μ.meanEntropy →
    PsiActive μ → μ.gap ≤ μ.cost

/-- `gap ≤ Δ · P'(I)` for a non-strictly psi-active law (convexity of `P`). -/
theorem gap_le_drop_slope {k : ℕ} (μ : InteriorLaw (Fin k))
    (hact : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ (H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2) *
      P1 (H ((μ.a + μ.b) / 2) - μ.meanEntropy) := by
  have h1 : μ.gap ≤ candidateGap psi μ.a μ.b μ.e μ.f := hybrid_gap_le_psi hact
  have h2 := CKLaneD.law_gap_le_P μ
  obtain ⟨hs0, hs1⟩ := CKLaneD.law_deficit_mem μ
  have hΔ0 : 0 ≤ H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2 := by
    have := μ.entropyDrop_nonneg
    unfold InteriorLaw.entropyDrop InteriorLaw.midpoint at this
    linarith
  have hEpos := CKLaneD.law_meanEntropy_pos μ
  have hHm1 : H ((μ.a + μ.b) / 2) ≤ 1 := H_le_one _
  set s := (H μ.a + H μ.b) / 2 - μ.meanEntropy with hs_def
  set I := H ((μ.a + μ.b) / 2) - μ.meanEntropy with hI_def
  have hsI : s ≤ I := by rw [hs_def, hI_def]; linarith
  have hI1 : I < 1 := by rw [hI_def]; linarith
  have htrap := CKLaneE.P_trapezoid hs0 hsI hI1
  have hmono : P1 s ≤ P1 I := CKLaneE.P1_monotoneOn ⟨hs0, lt_of_le_of_lt hsI hI1⟩
    ⟨hs0.trans hsI, hI1⟩ hsI
  have hIs : I - s = H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2 := by rw [hs_def, hI_def]; ring
  have h3 : P I - P s ≤ (I - s) * P1 I := by
    have := mul_le_mul_of_nonneg_left hmono (show 0 ≤ I - s by linarith)
    linarith
  rw [← hIs]
  linarith

set_option maxHeartbeats 2000000 in
/-- Soundness of one §6 leaf check, in the row form. -/
theorem dbLeaf_sound {p : List ℕ} {w : DBLeaf} (h : dbLeafOK p w = true)
    {k : ℕ} (μ : InteriorLaw (Fin k)) (hab : μ.a ≤ μ.b) (hsum : μ.a + μ.b ≤ 1)
    (ha : 1 / 10 ≤ μ.a) (hd : μ.b - μ.a ≤ 1 / 50)
    (hs : 3 / 40 < (H μ.a + H μ.b) / 2 - μ.meanEntropy)
    (hin : InDB (dbRoot.ofPath p) μ) (hact : PsiActive μ) : μ.gap ≤ μ.cost := by
  rcases hab.eq_or_lt with heq | hlt
  · exact μ.equal_mean_hybrid heq
  have hΔ0 : 0 ≤ H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2 := by
    have := μ.entropyDrop_nonneg
    unfold InteriorLaw.entropyDrop InteriorLaw.midpoint at this
    linarith
  have hgap := gap_le_drop_slope μ hact.le
  have hEpos := CKLaneD.law_meanEntropy_pos μ
  have hdpos : 0 < μ.b - μ.a := by linarith
  have hL := log_two_pos
  cases w with
  | cap =>
      simp only [dbLeafOK, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hb, hcap⟩ := h
      have fx := dbFacts_of hb μ hlt hsum ha hd hin
      have hcapR : ((dbIup (dbRoot.ofPath p) : ℚ) : ℝ) ≤ 3 / 40 := by
        have := (Rat.cast_le (K := ℝ)).mpr hcap
        push_cast at this
        linarith
      have := fx.hI_le
      linarith
  | endpoint vp vc =>
      simp only [dbLeafOK, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hb, hanc⟩, hI0⟩, hptvc⟩, hvc12, hres, hlam, hp0, hfin⟩ := h
      have fx := dbFacts_of hb μ hlt hsum ha hd hin
      set B := dbRoot.ofPath p with hB
      have hIge : 0 ≤ H ((μ.a + μ.b) / 2) - μ.meanEntropy := by
        have : (H μ.a + H μ.b) / 2 ≤ H ((μ.a + μ.b) / 2) := by linarith
        linarith
      have hP1 : P1 (H ((μ.a + μ.b) / 2) - μ.meanEntropy) ≤ ((P1up vp : ℚ) : ℝ) :=
        anchorOk_sound hanc hIge fx.hI_le
      have hp0R : (0 : ℝ) ≤ ((P1up vp : ℚ) : ℝ) := by exact_mod_cast hp0
      have hfinR : ((dbK B : ℚ) : ℝ) * ((P1up vp : ℚ) : ℝ) ≤ ((JloOf vc : ℚ) : ℝ) / (DD : ℝ) := by
        exact_mod_cast hfin
      have hvc12R : ((vc : ℚ) : ℝ) ≤ 1 / 2 := by
        have h := (Rat.cast_le (K := ℝ)).mpr hvc12
        push_cast at h
        linarith
      have hresR : ((dbEup B : ℚ) : ℝ) * (1 - 2 * ((vc : ℚ) : ℝ)) ≤ (DD : ℝ) * ((Hlo vc : ℚ) : ℝ) := by
        exact_mod_cast hres
      have hlamR : (0 : ℝ) ≤ ((lamLo vc : ℚ) : ℝ) := by exact_mod_cast hlam
      have hDD : (DD : ℝ) = 1 / 50 := by simp [DD]
      have hDDpos : (0 : ℝ) < (DD : ℝ) := by rw [hDD]; norm_num
      -- gap ≤ d² · Jlo / D
      have hg1 : μ.gap ≤ (μ.b - μ.a) ^ 2 * (((JloOf vc : ℚ) : ℝ) / (DD : ℝ)) := by
        have e1 : (H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2) *
            P1 (H ((μ.a + μ.b) / 2) - μ.meanEntropy) ≤
            (H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2) * ((P1up vp : ℚ) : ℝ) :=
          mul_le_mul_of_nonneg_left hP1 hΔ0
        have e2 : (H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2) * ((P1up vp : ℚ) : ℝ) ≤
            ((dbK B : ℚ) : ℝ) * (μ.b - μ.a) ^ 2 * ((P1up vp : ℚ) : ℝ) :=
          mul_le_mul_of_nonneg_right fx.hdrop hp0R
        have e3 : ((dbK B : ℚ) : ℝ) * (μ.b - μ.a) ^ 2 * ((P1up vp : ℚ) : ℝ) ≤
            (μ.b - μ.a) ^ 2 * (((JloOf vc : ℚ) : ℝ) / (DD : ℝ)) := by
          have := mul_le_mul_of_nonneg_left hfinR (sq_nonneg (μ.b - μ.a))
          linarith
        linarith
      -- cost ≥ d² · Jlo / D
      have hvcpos : (0 : ℝ) < ((vc : ℚ) : ℝ) := by exact_mod_cast (ptOk_pos hptvc).1
      have hrc : radialContact (DD : ℝ) μ.meanEntropy ≤ ((vc : ℚ) : ℝ) := by
        rw [radialContact_le_iff hDDpos hEpos hvcpos.le hvc12R]
        have h1 : μ.meanEntropy * (1 - 2 * ((vc : ℚ) : ℝ)) ≤
            ((dbEup B : ℚ) : ℝ) * (1 - 2 * ((vc : ℚ) : ℝ)) :=
          mul_le_mul_of_nonneg_right fx.hE_le (by linarith)
        have h2 := mul_le_mul_of_nonneg_left (H_ge_Hlo hptvc) hDDpos.le
        linarith
      have hrcpos := radialContact_pos hDDpos hEpos
      have hJa := J_antitone hrcpos hvc12R hrc
      obtain ⟨hvclog, -⟩ := lam_bounds hptvc
      have hJlo : ((JloOf vc : ℚ) : ℝ) ≤ J ((vc : ℚ) : ℝ) := by
        simp only [JloOf]
        push_cast
        unfold J
        calc ((lamLo vc : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ) ≤ ((lamLo vc : ℚ) : ℝ) / Real.log 2 :=
              div_le_div_of_nonneg_left hlamR hL LqHi_ge
          _ ≤ Real.log ((1 - ((vc : ℚ) : ℝ)) / ((vc : ℚ) : ℝ)) / Real.log 2 :=
              div_le_div_of_nonneg_right hvclog hL.le
      have hFD : (DD : ℝ) * ((JloOf vc : ℚ) : ℝ) ≤ F (DD : ℝ) μ.meanEntropy := by
        have : F (DD : ℝ) μ.meanEntropy = (DD : ℝ) * J (radialContact (DD : ℝ) μ.meanEntropy) := by
          simp [F, hDDpos.ne']
        rw [this]
        exact mul_le_mul_of_nonneg_left (hJlo.trans hJa) hDDpos.le
      have hanti := antitoneOn_F_div_sq (h := μ.meanEntropy) hEpos hdpos hDDpos (by rw [hDD]; exact hd)
      simp only at hanti
      have hcost : (μ.b - μ.a) ^ 2 * (((JloOf vc : ℚ) : ℝ) / (DD : ℝ)) ≤ μ.cost := by
        have hF := PsiEndpointPlane.law_radial_lower μ hlt
        have h1 : ((JloOf vc : ℚ) : ℝ) / (DD : ℝ) ≤ F (DD : ℝ) μ.meanEntropy / (DD : ℝ) ^ 2 := by
          rw [div_le_div_iff₀ hDDpos (by positivity)]
          have := mul_le_mul_of_nonneg_left hFD hDDpos.le
          have e : (DD : ℝ) * ((DD : ℝ) * ((JloOf vc : ℚ) : ℝ)) = ((JloOf vc : ℚ) : ℝ) * (DD : ℝ) ^ 2 := by
            ring
          linarith
        have h2 : (μ.b - μ.a) ^ 2 * (F (DD : ℝ) μ.meanEntropy / (DD : ℝ) ^ 2) ≤
            F (μ.b - μ.a) μ.meanEntropy := by
          have hdne : μ.b - μ.a ≠ 0 := hdpos.ne'
          have := mul_le_mul_of_nonneg_left hanti (sq_nonneg (μ.b - μ.a))
          rw [show (μ.b - μ.a) ^ 2 * (F (μ.b - μ.a) μ.meanEntropy / (μ.b - μ.a) ^ 2) =
            F (μ.b - μ.a) μ.meanEntropy by field_simp] at this
          exact this
        have := mul_le_mul_of_nonneg_left h1 (sq_nonneg (μ.b - μ.a))
        linarith
      linarith
  | logsum vp kap =>
      simp only [dbLeafOK, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hb, hanc⟩, hI0⟩, hptus⟩, hk0, hk2, hkus, hp4, hfin⟩ := h
      have fx := dbFacts_of hb μ hlt hsum ha hd hin
      set B := dbRoot.ofPath p with hB
      set us : ℚ := (1 - dbRmax B) / 2 with hus
      have hIge : 0 ≤ H ((μ.a + μ.b) / 2) - μ.meanEntropy := by
        have : (H μ.a + H μ.b) / 2 ≤ H ((μ.a + μ.b) / 2) := by linarith
        linarith
      have hP1 : P1 (H ((μ.a + μ.b) / 2) - μ.meanEntropy) ≤ ((P1up vp : ℚ) : ℝ) :=
        anchorOk_sound hanc hIge fx.hI_le
      have hk0R : (0 : ℝ) ≤ (kap : ℝ) := by exact_mod_cast hk0
      have hk2R : (kap : ℝ) ≤ 2 := by exact_mod_cast hk2
      have hp4R : (4 : ℝ) ≤ ((P1up vp : ℚ) : ℝ) := by exact_mod_cast hp4
      have hfinR : (kap : ℝ) / (2 * ((((1 + DD) ^ 2 - B.a0 ^ 2) / 4 : ℚ) : ℝ)) *
          max 0 (((dbIlo B : ℚ) : ℝ) - ((dbK B : ℚ) : ℝ) * (DD : ℝ) ^ 2) -
          ((dbK B : ℚ) : ℝ) * (((P1up vp : ℚ) : ℝ) - 4) ≥ 0 := by
        have := (Rat.cast_le (K := ℝ)).mpr hfin
        push_cast at this ⊢
        linarith
      -- kappa hypotheses of the M07 floor
      have husR0 : (0 : ℝ) < (us : ℝ) := by
        have hr : ((dbRmax B : ℚ) : ℝ) ≤ 4 / 5 := by
          simp only [dbRmax]; push_cast; exact min_le_right _ _
        rw [hus]; push_cast; linarith
      have hbase : (kap : ℝ) * (-Real.log (1 - (us : ℝ))) ≤ (us : ℝ) / (1 - (us : ℝ)) := by
        obtain ⟨-, -, hl1, -⟩ := ptOk_sound hptus
        have hkusR : (kap : ℝ) * (-((l1Lo us : ℚ) : ℝ)) ≤ (us : ℝ) / (1 - (us : ℝ)) := by
          have := (Rat.cast_le (K := ℝ)).mpr hkus
          push_cast at this ⊢
          linarith
        have := mul_le_mul_of_nonneg_left (show -Real.log (1 - (us : ℝ)) ≤ -((l1Lo us : ℚ) : ℝ) by
          linarith) hk0R
        linarith
      have haI := μ.a_interior
      have hbI := μ.b_interior
      have hua : (us : ℝ) ≤ μ.a := fx.hus_a
      have hk_a0 := kappa_transfer husR0 hua haI.2 hbase
      have hk_a1 : (kap : ℝ) * (-Real.log μ.a) ≤ (1 - μ.a) / μ.a := by
        have := kappa_transfer husR0 (show (us : ℝ) ≤ 1 - μ.a by linarith) (by linarith) hbase
        rwa [show (1 : ℝ) - (1 - μ.a) = μ.a by ring] at this
      have hk_b0 := kappa_transfer husR0 (show (us : ℝ) ≤ μ.b by linarith) hbI.2 hbase
      have hk_b1 : (kap : ℝ) * (-Real.log μ.b) ≤ (1 - μ.b) / μ.b := by
        have := kappa_transfer husR0 (show (us : ℝ) ≤ 1 - μ.b by linarith) (by linarith) hbase
        rwa [show (1 : ℝ) - (1 - μ.b) = μ.b by ring] at this
      have hM07 := CKLaneM07.kappa_cost_lower_bound μ hk0R hk2R hk_a0 hk_a1 hk_b0 hk_b1
      have hj := four_entropyDrop_le_interiorCost haI.1 haI.2 hbI.1 hbI.2
      -- quantities
      set Δ := H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2 with hΔ
      set s := (H μ.a + H μ.b) / 2 - μ.meanEntropy with hs_def
      set d := μ.b - μ.a with hd_def
      set K := ((dbK B : ℚ) : ℝ) with hK
      set V := LogSum.V μ.a μ.b with hV
      set Vs := ((((1 + DD) ^ 2 - B.a0 ^ 2) / 4 : ℚ) : ℝ) with hVs
      have hVpos : 0 < V := LogSum.V_pos haI hbI
      have hVle : V ≤ Vs := fx.hV
      have hDD : (DD : ℝ) = 1 / 50 := by simp [DD]
      have hKd : K * d ^ 2 ≤ K * (DD : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ fx.hK0
        apply pow_le_pow_left₀ hdpos.le
        rw [hDD]; exact hd
      have hsstar : max 0 (((dbIlo B : ℚ) : ℝ) - K * (DD : ℝ) ^ 2) ≤ s := by
        apply max_le (by linarith)
        have h1 := fx.hI_ge
        have h2 := fx.hdrop
        rw [← hd_def] at h2
        have : H ((μ.a + μ.b) / 2) - μ.meanEntropy = s + Δ := by rw [hs_def, hΔ]; ring
        linarith
      set sst := max 0 (((dbIlo B : ℚ) : ℝ) - K * (DD : ℝ) ^ 2) with hsst
      have hsst0 : 0 ≤ sst := le_max_left _ _
      -- κ d² s / (2V) ≥ κ d² sst / (2 Vs)
      have hVs0 : 0 < Vs := lt_of_lt_of_le hVpos hVle
      have hlog1 : (kap : ℝ) / (2 * Vs) * sst ≤ (kap : ℝ) * s / (2 * V) := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have e1 : (kap : ℝ) * sst * (2 * V) ≤ (kap : ℝ) * s * (2 * Vs) := by
          have h1 : sst * V ≤ s * Vs := mul_le_mul hsstar hVle hVpos.le (hsst0.trans hsstar)
          have := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 2 * (kap : ℝ) by positivity)
          linarith
        linarith
      -- gap ≤ Δ P1up
      have hg1 : μ.gap ≤ Δ * ((P1up vp : ℚ) : ℝ) := by
        have := mul_le_mul_of_nonneg_left hP1 hΔ0
        linarith
      -- cost ≥ 4Δ + κ d² s/(2V)
      have hcost : 4 * Δ + (kap : ℝ) * s / (2 * V) * d ^ 2 ≤ μ.cost := by
        have e : (kap : ℝ) * ((μ.a - μ.b) ^ 2 / (4 * LogSum.V μ.a μ.b)) *
            ((H μ.a - μ.e) + (H μ.b - μ.f)) = (kap : ℝ) * s / (2 * V) * d ^ 2 := by
          rw [hs_def, hd_def, hV]
          unfold InteriorLaw.meanEntropy
          field_simp
          ring
        rw [e] at hM07
        linarith
      -- final
      have hΔK : Δ * (((P1up vp : ℚ) : ℝ) - 4) ≤ K * d ^ 2 * (((P1up vp : ℚ) : ℝ) - 4) :=
        mul_le_mul_of_nonneg_right (by rw [hΔ, hd_def]; exact fx.hdrop) (by linarith)
      have hfin2 : 0 ≤ d ^ 2 * ((kap : ℝ) / (2 * Vs) * sst - K * (((P1up vp : ℚ) : ℝ) - 4)) :=
        mul_nonneg (sq_nonneg d) (by linarith)
      have hfin3 : d ^ 2 * ((kap : ℝ) / (2 * Vs) * sst) ≤ (kap : ℝ) * s / (2 * V) * d ^ 2 := by
        have := mul_le_mul_of_nonneg_left hlog1 (sq_nonneg d)
        linarith
      have hstep1 : Δ * ((P1up vp : ℚ) : ℝ) = 4 * Δ + Δ * (((P1up vp : ℚ) : ℝ) - 4) := by ring
      have hstep2 : K * d ^ 2 * (((P1up vp : ℚ) : ℝ) - 4) ≤ d ^ 2 * ((kap : ℝ) / (2 * Vs) * sst) := by
        have e : d ^ 2 * ((kap : ℝ) / (2 * Vs) * sst - K * (((P1up vp : ℚ) : ℝ) - 4)) =
            d ^ 2 * ((kap : ℝ) / (2 * Vs) * sst) - K * d ^ 2 * (((P1up vp : ℚ) : ℝ) - 4) := by ring
        linarith
      linarith [hg1, hcost, hΔK, hstep1, hstep2, hfin3]

/-- The row `NoSepA_ModerateRest` from a §6 tree whose leaves all pass the kernel check. -/
theorem noSepA_moderateRest_of_tree {T : PT DBLeaf} (hall : T.allLeaves dbLeafOK = true) :
    NoSepA_ModerateRest := by
  intro k μ hab hsum ha _hb hd hE hs hact
  have hEpos := CKLaneD.law_meanEntropy_pos μ
  set Hm := H ((μ.a + μ.b) / 2) with hHm
  have hEM : (EM : ℝ) = 11 / 200 := by simp [EM]
  have hEle : μ.meanEntropy ≤ Hm := by
    have h1 : μ.meanEntropy ≤ (H μ.a + H μ.b) / 2 := by
      unfold InteriorLaw.meanEntropy; linarith [μ.e_le_cap, μ.f_le_cap]
    have h2 := μ.entropyDrop_nonneg
    unfold InteriorLaw.entropyDrop InteriorLaw.midpoint at h2
    rw [hHm]; linarith
  have hHmE : (EM : ℝ) ≤ Hm := by rw [hEM]; linarith
  set t : ℝ := if (EM : ℝ) < Hm then (μ.meanEntropy - EM) / (Hm - EM) else 0 with ht
  have htE : μ.meanEntropy = (EM : ℝ) + t * (Hm - EM) := by
    rw [ht]
    split_ifs with hc
    · have hne : Hm - (EM : ℝ) ≠ 0 := (sub_pos.mpr hc).ne'
      field_simp
      ring
    · have : Hm = (EM : ℝ) := le_antisymm (le_of_not_gt hc) hHmE
      rw [this]; linarith
  have ht01 : 0 ≤ t ∧ t ≤ 1 := by
    rw [ht]
    split_ifs with hc
    · constructor
      · exact div_nonneg (by linarith) (by linarith)
      · rw [div_le_one (by linarith)]; linarith
    · norm_num
  have hq0 : 0 ≤ 1 - μ.a - μ.b := by linarith
  have hq1 : 1 - μ.a - μ.b ≤ 4 / 5 := by linarith [μ.a_interior.1]
  have hroot : dbRoot.Mem (1 - μ.a - μ.b) t 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [dbRoot]; push_cast; exact hq0
    · simp only [dbRoot]; push_cast; exact hq1
    · simp only [dbRoot]; push_cast; exact ht01.1
    · simp only [dbRoot]; push_cast; exact ht01.2
    · simp [dbRoot]
    · simp [dbRoot]
  obtain ⟨q, hq, hmem⟩ := PT.cover dbRoot T hroot
  obtain ⟨h1, h2, h3, h4, -, -⟩ := hmem
  have hin : InDB (dbRoot.ofPath q.1) μ := by
    refine ⟨h1, h2, ?_, ?_⟩
    · rw [htE]
      have := mul_le_mul_of_nonneg_right h3 (show 0 ≤ Hm - (EM : ℝ) by linarith)
      linarith
    · rw [htE]
      have := mul_le_mul_of_nonneg_right h4 (show 0 ≤ Hm - (EM : ℝ) by linarith)
      linarith
  exact dbLeaf_sound (PT.allLeaves_sound hall q hq) μ hab hsum ha hd hs hin hact

end CKLaneN1

end


