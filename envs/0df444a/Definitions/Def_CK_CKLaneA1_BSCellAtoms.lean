-- Prove2me | Definitions.Def_CK_CKLaneA1_BSCellAtoms
-- name    : CK_CKLaneA1_BSCellAtoms
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:28:55.49092+00:00
-- url     : https://prove2.me/theorems/fb58e49b-31f8-4fe6-a948-2c390c2a2704
-- title:
--   Courtade–Kumar proof module `CKLaneA1.BSCellAtoms` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.BSCellAtoms` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.BSCellAtoms` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.BSCellAtoms (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/BSCellAtoms.lean)

import Definitions.Def_CK_CKLaneA1_BSCellSound

/-!
# CKLaneA1.BSCellAtoms — soundness of the both-small cell atoms, and of the cell check
-/

set_option autoImplicit false

namespace CKLaneA1

open GeneralCK GeneralCK.Correction GeneralCK.Correction.Natural GeneralCK.Correction.HighU
open GeneralCK.Certificates
open GeneralCK.Certificates.Reflection (biasE biasB)

local notation "sc" => (DyadicInterval.scale 64 : ℝ)

theorem hi_of_le {I : DI} {a x : ℝ} (hI : I.Contains a) (hxa : x ≤ a) : sc * x ≤ (I.hi:ℝ) :=
  (mul_le_mul_of_nonneg_left hxa SC_pos.le).trans hI.2

theorem lo_of_le {I : DI} {a x : ℝ} (hI : I.Contains a) (hax : a ≤ x) : (I.lo:ℝ) ≤ sc * x :=
  hI.1.trans (mul_le_mul_of_nonneg_left hax SC_pos.le)

/-- Lower-endpoint transfer with the endpoint named explicitly (avoids premature unification of
the interval with the goal's interval). -/
theorem lo_le {I : DI} {a x : ℝ} {l : ℤ} (hI : I.Contains a) (hl : I.lo = l) (hax : a ≤ x) :
    (l:ℝ) ≤ sc * x := by
  subst hl; exact hI.1.trans (mul_le_mul_of_nonneg_left hax SC_pos.le)

theorem hi_ge {I : DI} {a x : ℝ} {h : ℤ} (hI : I.Contains a) (hh : I.hi = h) (hxa : x ≤ a) :
    sc * x ≤ (h:ℝ) := by
  subst hh; exact (mul_le_mul_of_nonneg_left hxa SC_pos.le).trans hI.2

set_option maxHeartbeats 1000000 in
theorem bs_cell_sound {n : ℕ} {L2 : DI} (hL : L2.Contains (Real.log 2)) {s : BSStrip}
    {A B : RNode} {two : Bool} {cd : CData}
    (hs : bsStripOK n L2 s = true) (h : bsCellCheck n L2 s A B two cd = true)
    {u w : ℝ} (hu : 0 < u) (huw : u < w) (hw1 : s.lo ≤ w) (hw2 : w ≤ s.hi)
    (hr1 : (A.ra:ℝ)/sc ≤ u/w) (hr2 : u/w ≤ (B.ra:ℝ)/sc) :
    0 < actualDetGapCoefficient u w ∧ 0 < m11 u w := by
  have hsc := SC_pos
  have hw0 : 0 < w := hu.trans huw
  obtain ⟨hPw, hOm, hW, hLw, hw14, hJw, hlo0⟩ := bs_w_atoms hL hs hw0 hw1 hw2
  have hw12 : w < 1/2 := by linarith
  have hJu : 0 < jn u := jn_pos hu (by linarith)
  have hw0' : w ≠ 0 := hw0.ne'
  have hu0' : u ≠ 0 := hu.ne'
  have h1w : (1:ℝ) - w ≠ 0 := (by linarith : (0:ℝ) < 1 - w).ne'
  have h1u : (1:ℝ) - u ≠ 0 := (by linarith : (0:ℝ) < 1 - u).ne'
  have hwu' : w - u ≠ 0 := (sub_pos.mpr huw).ne'
  -- unpack the cell check
  unfold bsCellCheck at h
  simp only [] at h
  have h0 := Bool.and_eq_true_iff.mp h
  have h1 := Bool.and_eq_true_iff.mp h0.1
  have h2 := Bool.and_eq_true_iff.mp h1.1
  have h3 := Bool.and_eq_true_iff.mp h2.1
  have hB : rnodeOK B = true := h3.1
  have hA : (decide (A.ra = 0) || rnodeOK A) = true := h3.2
  have hgd := h2.2
  have hbr := h1.2
  have hfin := h0.2
  set a := bsAt n L2 s A B with ha_def
  unfold bsGuards at hgd
  have hg1 := Bool.and_eq_true_iff.mp hgd
  obtain ⟨gA0, gP0, gAB, gAt, gY0, gd0, gw1, gw2, gy1, gU1, gSp, gsl, gsl1, gtt, gia, gdg, gtw, gon⟩ :=
    of_decide_eq_true hg1.1
  have gsHi := hg1.2
  obtain ⟨hBr0, hBr1, hBlog⟩ := rnode_facts (n := n) hL hB
  have hBr0' : (0:ℝ) < (B.ra:ℝ)/sc := hBr0
  have hBr1' : (B.ra:ℝ)/sc ≤ 1 := hBr1
  have hP : a.P.Contains (1 / jn w) := hPw
  have hPlo : (a.P.lo:ℝ)/sc ≤ 1 / jn w := lo_div_le hP
  have hPhi : 1 / jn w ≤ (a.P.hi:ℝ)/sc := le_hi_div hP
  have hp0 : 0 < 1 / jn w := one_div_pos.mpr hJw
  have hJw' : jn w ≠ 0 := hJw.ne'
  -- basic real facts
  set r := u / w with hr_def
  have hr0 : 0 < r := div_pos hu hw0
  have hr1' : r < 1 := (div_lt_one hw0).mpr huw
  have hA' : (0:ℝ) ≤ (A.ra:ℝ)/sc := div_nonneg (by exact_mod_cast gA0) hsc.le
  have hBr : (B.ra:ℝ)/sc = B.r := rfl
  have hr2' : r ≤ B.r := hr2
  have huw_eq : u = r * w := by rw [hr_def]; field_simp
  have hsh_eq : (w - u)/w = 1 - r := by rw [hr_def]; field_simp
  have hu14 : u ≤ 1/4 := by linarith
  have hw1' : (s.w1.xa:ℝ)/sc ≤ w := hw1
  have hlo0' : (0:ℝ) ≤ (s.w1.xa:ℝ)/sc := hlo0
  -- R, U, Sh
  have hR : a.R.Contains r := mk_of_div hr1 hr2
  have hU : a.U.Contains u := by
    have hm1 := DyadicInterval.mul_sound (Iv.pt_contains A.ra) (Iv.pt_contains s.w1.xa)
    have hm2 := DyadicInterval.mul_sound (Iv.pt_contains B.ra) (Iv.pt_contains s.w2.xa)
    refine ⟨lo_le hm1 rfl ?_, hi_ge hm2 rfl ?_⟩
    · rw [huw_eq]; exact mul_le_mul hr1 hw1 hlo0 hr0.le
    · rw [huw_eq]; exact mul_le_mul hr2 hw2 hw0.le (hA'.trans (hr1.trans hr2))
  have hUhi : u ≤ (a.U.hi:ℝ)/sc := le_hi_div hU
  have hSh : a.Sh.Contains ((w - u)/w) := by
    rw [hsh_eq]
    apply mk_of_div
    · have e : ((SCz - B.ra : ℤ):ℝ)/sc = 1 - (B.ra:ℝ)/sc := by
        rw [show (SCz - B.ra : ℤ) = DyadicInterval.scale 64 - B.ra from rfl]; push_cast; field_simp
      rw [e]; linarith
    · have e : ((SCz - A.ra : ℤ):ℝ)/sc = 1 - (A.ra:ℝ)/sc := by
        rw [show (SCz - A.ra : ℤ) = DyadicInterval.scale 64 - A.ra from rfl]; push_cast; field_simp
      rw [e]; linarith
  have hsh0 : 0 < (w - u)/w := by rw [hsh_eq]; linarith
  -- y = (w-u)/(1-w)
  set y := (w - u)/(1 - w) with hy_def
  have hy0 : 0 ≤ y := div_nonneg (by linarith) (by linarith)
  have hhi1 : s.hi < 1 := by linarith [hw14, hw2, (show s.hi ≤ 1/4 from by
    have hn2 := node_facts (n := n) hL (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hs).1).1
    have hg := of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hs).1).2
    have : s.hi = s.w2.x := rfl
    rw [this]; unfold Node.x; rw [div_le_iff₀ hsc]
    have : (4:ℝ) * s.w2.xa ≤ (SCz:ℝ) := by exact_mod_cast hg.2.2.1
    rw [SCz_real] at this; linarith)]
  have hY : a.Y.Contains y := by
    have e : y = w * (1 - r) * (1 - w)⁻¹ := by rw [hy_def, hr_def]; field_simp
    have hr1w : ((Iv.one.sub (Iv.pt s.w1.xa)).recip).Contains (1 - s.lo)⁻¹ :=
      DyadicInterval.recip_sound gw1 (DyadicInterval.sub_sound Iv.one_contains (Iv.pt_contains s.w1.xa))
    have hr2w : ((Iv.one.sub (Iv.pt s.w2.xa)).recip).Contains (1 - s.hi)⁻¹ :=
      DyadicInterval.recip_sound gw2 (DyadicInterval.sub_sound Iv.one_contains (Iv.pt_contains s.w2.xa))
    have hm1 := DyadicInterval.mul_sound (DyadicInterval.mul_sound (Iv.pt_contains s.w1.xa)
      (pt_sub_contains B.ra)) hr1w
    have hm2 := DyadicInterval.mul_sound (DyadicInterval.mul_sound (Iv.pt_contains s.w2.xa)
      (pt_sub_contains A.ra)) hr2w
    have hlw : s.lo < 1 := by linarith
    rw [e]
    refine ⟨lo_le hm1 rfl ?_, hi_ge hm2 rfl ?_⟩
    · exact mul_le_mul (mul_le_mul hw1 (by linarith) (by linarith) hw0.le)
        (inv_anti₀ (by linarith) (by linarith)) (inv_nonneg.mpr (by linarith))
        (mul_nonneg hw0.le (by linarith))
    · have hw2' : 0 ≤ s.hi := hlo0.trans (hw1.trans hw2)
      exact mul_le_mul (mul_le_mul hw2 (by linarith) (by linarith) hw2')
        (inv_anti₀ (by linarith) (by linarith)) (inv_nonneg.mpr (by linarith))
        (mul_nonneg hw2' (by linarith))
  -- log(1+y)
  have hlb := log1p_bounds hy0
  have hL1y : (bsL1y a.Y).Contains (Real.log (1 + y)) := by
    have hylo : (a.Y.lo:ℝ)/sc ≤ y := lo_div_le hY
    have hylo0 : (0:ℝ) ≤ (a.Y.lo:ℝ)/sc := div_nonneg (by exact_mod_cast gY0) hsc.le
    have hq := DyadicInterval.mul_sound (Iv.pt_contains a.Y.lo)
      (DyadicInterval.recip_sound gy1 (DyadicInterval.add_sound Iv.one_contains (Iv.pt_contains a.Y.lo)))
    refine ⟨lo_le hq rfl ?_, ?_⟩
    · refine le_trans ?_ hlb.1
      rw [← div_eq_mul_inv, div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    · exact (mul_le_mul_of_nonneg_left hlb.2 hsc.le).trans hY.2
  -- δ = jn u − jn w
  have hdeq := delta_eq hu huw (by linarith : w < 1)
  rw [← hr_def, ← hy_def] at hdeq
  set δ := jn u - jn w with hδ_def
  have hδ0 : 0 ≤ δ := by rw [hδ_def]; linarith [jn_anti hu huw.le (by linarith : w < 1)]
  have hlogr : -Real.log B.r ≤ -Real.log r := by
    have := Real.log_le_log hr0 hr2'; linarith
  have hdlo : (a.dlo:ℝ)/sc ≤ δ := by
    have hi := DyadicInterval.add_sound (DyadicInterval.neg_sound hBlog) hL1y
    have := lo_div_le hi
    change (((rlog n L2 B).neg.add (bsL1y a.Y)).lo:ℝ)/sc ≤ δ
    rw [hdeq]; linarith
  have hdlo0 : (0:ℝ) ≤ (a.dlo:ℝ)/sc := div_nonneg (by exact_mod_cast gd0) hsc.le
  have hAok : A.ra ≠ 0 → rnodeOK A = true := fun hA0 => by simpa [hA0] using hA
  have hdhi : A.ra ≠ 0 → δ ≤ (a.dhi:ℝ)/sc := by
    intro hA0
    obtain ⟨hAr0, -, hAlog⟩ := rnode_facts (n := n) hL (hAok hA0)
    have hi := DyadicInterval.add_sound (DyadicInterval.neg_sound hAlog) hL1y
    have := le_hi_div hi
    have hlogA : -Real.log r ≤ -Real.log A.r := by
      have := Real.log_le_log hAr0 hr1; linarith
    change δ ≤ (((rlog n L2 A).neg.add (bsL1y a.Y)).hi:ℝ)/sc
    rw [hdeq]; linarith
  have hD : A.ra ≠ 0 → a.D.Contains δ := fun hA0 => mk_of_div hdlo (hdhi hA0)
  -- rδ
  have hRd : a.Rd.Contains (r * δ) := by
    change (bsRd n L2 A B a.Y).Contains (r * δ)
    unfold bsRd
    by_cases hA0 : A.ra = 0
    · rw [if_pos hA0]
      have hB4 : B.r ≤ 1/4 := by
        have := gAt hA0
        rw [← hBr, div_le_iff₀ hsc]
        have : (4:ℝ) * B.ra ≤ (SCz:ℝ) := by exact_mod_cast this
        rw [SCz_real] at this; linarith
      have hm := DyadicInterval.mul_sound (Iv.pt_contains B.ra)
        (DyadicInterval.add_sound (DyadicInterval.neg_sound hBlog) (Iv.pt_contains a.Y.hi))
      refine ⟨?_, hi_ge hm rfl ?_⟩
      · change ((0:ℤ):ℝ) ≤ _; rw [Int.cast_zero]; exact mul_nonneg hsc.le (mul_nonneg hr0.le hδ0)
      · have hnl := mul_neglog_le hr0 hr2' (neglog_ge_one hBr0 hB4)
        have hyh : Real.log (1 + y) ≤ (a.Y.hi:ℝ)/sc := hlb.2.trans (le_hi_div hY)
        have hlog0 : 0 ≤ Real.log (1 + y) := Real.log_nonneg (by linarith)
        have h2 : r * Real.log (1 + y) ≤ B.r * ((a.Y.hi:ℝ)/sc) :=
          mul_le_mul hr2' hyh hlog0 hBr0.le
        rw [hdeq]
        change r * (-Real.log r + Real.log (1 + y)) ≤ B.r * (-Real.log B.r + (a.Y.hi:ℝ)/sc)
        nlinarith
    · rw [if_neg hA0]
      exact DyadicInterval.mul_sound hR (hD hA0)
  -- τ
  have htau_eq := tau_eq hJw hJu
  rw [← hδ_def] at htau_eq
  have hTau : a.Tau.Contains (jn w / jn u) := by
    rw [htau_eq]
    change (bsTau a.P a.D A a.dlo).Contains _
    unfold bsTau
    by_cases hA0 : A.ra = 0
    · rw [if_pos hA0]
      have hq := DyadicInterval.recip_sound (gtt hA0)
        (DyadicInterval.add_sound Iv.one_contains (DyadicInterval.mul_sound hP (Iv.pt_contains a.dlo)))
      refine ⟨?_, hi_ge hq rfl ?_⟩
      · change ((0:ℤ):ℝ) ≤ _; rw [Int.cast_zero]
        have hden : 0 < 1 + 1 / jn w * δ := by have := mul_nonneg hp0.le hδ0; linarith
        exact mul_nonneg hsc.le (one_div_pos.mpr hden).le
      · rw [one_div (1 + 1 / jn w * δ)]
        have h1 := mul_nonneg hp0.le hdlo0
        have h2 := mul_le_mul_of_nonneg_left hdlo hp0.le
        exact inv_anti₀ (by linarith) (by linarith)
    · rw [if_neg hA0]
      rw [one_div (1 + 1 / jn w * δ)]
      exact DyadicInterval.recip_sound (gia hA0).1
        (DyadicInterval.add_sound Iv.one_contains (DyadicInterval.mul_sound hP (hD hA0)))
  have htau0 : 0 < jn w / jn u := div_pos hJw hJu
  -- r/τ, q̂u, q̂w, k̂, A_u, Ŝp
  have hRt : a.Rt.Contains ((u / w) * (jn u / jn w)) := by
    rw [rtau_eq hJw.ne']
    exact DyadicInterval.add_sound hR (DyadicInterval.mul_sound hP hRd)
  have hQu : a.Qu.Contains (qp u / w) := by
    have e : qp u / w = r * (1 - u) := by rw [hr_def]; unfold qp; field_simp
    rw [e]; exact DyadicInterval.mul_sound hR (DyadicInterval.sub_sound Iv.one_contains hU)
  have hQw : a.Qw.Contains (qp w / w) := by
    have e : qp w / w = 1 - w := by unfold qp; field_simp
    rw [e]; exact DyadicInterval.sub_sound Iv.one_contains hW
  have hKh : a.Kh.Contains ((1 / jn w) * (qp u * jn u) / w) := by
    rw [kh_eq hw0 hJw.ne']
    exact DyadicInterval.mul_sound (DyadicInterval.sub_sound Iv.one_contains hU) hRt
  have hAu : a.Au.Contains ((-Real.log (1 - u)) / w) := by
    have hb := neglog1m_bounds hu.le (by linarith : u < 1)
    have hq := DyadicInterval.mul_sound hR
      (DyadicInterval.recip_sound gU1 (DyadicInterval.sub_sound Iv.one_contains hU))
    refine ⟨?_, hi_ge hq rfl ?_⟩
    · change (A.ra:ℝ) ≤ _
      have hle : (A.ra:ℝ)/sc ≤ (-Real.log (1 - u)) / w := by
        refine hr1.trans ?_
        rw [hr_def]; exact div_le_div_of_nonneg_right hb.1 hw0.le
      have e : (A.ra:ℝ) = sc * ((A.ra:ℝ)/sc) := by field_simp
      rw [e]; exact mul_le_mul_of_nonneg_left hle hsc.le
    · rw [hr_def]
      calc (-Real.log (1 - u)) / w ≤ (u / (1 - u)) / w := div_le_div_of_nonneg_right hb.2 hw0.le
        _ = u / w * (1 - u)⁻¹ := by field_simp
  have hSp : a.Sp.Contains ((1 / jn w) * entropySum u w / w) := by
    rw [Sp_eq hu huw hw12]
    exact DyadicInterval.add_sound (DyadicInterval.add_sound hRt Iv.one_contains)
      (DyadicInterval.mul_sound hP (DyadicInterval.add_sound hAu hLw))
  -- divided difference atoms
  have hmvt := jn_slope_mvt hu huw hw12.le
  have hqu0 : 0 < qp u := by unfold qp; nlinarith
  have hqw0 : 0 < qp w := by unfold qp; nlinarith
  have hQjh : a.Qjh.Contains ((qp u / w) * (w * ((jn w - jn u)/(w - u)))) := by
    have e1 : (qp u / w) * (w * ((jn w - jn u)/(w - u))) = qp u * ((jn w - jn u)/(w - u)) := by
      field_simp
    have hA_ : (bsQjhA a.R a.U s.w1.xa).Contains ((qp u / w) * (w * ((jn w - jn u)/(w - u)))) := by
      rw [e1]
      have hq := DyadicInterval.neg_sound (DyadicInterval.mul_sound (DyadicInterval.mul_sound hR
        (DyadicInterval.sub_sound Iv.one_contains hU))
        (DyadicInterval.recip_sound gw1 (DyadicInterval.sub_sound Iv.one_contains (Iv.pt_contains s.w1.xa))))
      refine ⟨?_, hi_ge hq rfl ?_⟩
      · change ((-SCz : ℤ):ℝ) ≤ _
        rw [Int.cast_neg, SCz_real]
        have h1 : -1 ≤ qp u * ((jn w - jn u)/(w - u)) := by
          have := mul_le_mul_of_nonneg_left hmvt.1 hqu0.le
          have hqu0' : qp u ≠ 0 := hqu0.ne'
          have e : qp u * (-1 / qp u) = -1 := by field_simp
          linarith
        nlinarith [mul_le_mul_of_nonneg_left h1 hsc.le]
      · have h1 : qp u * ((jn w - jn u)/(w - u)) ≤ qp u * (-1 / qp w) :=
          mul_le_mul_of_nonneg_left hmvt.2 hqu0.le
        have e : qp u * (-1 / qp w) = -(r * (1 - u) * (1 - w)⁻¹) := by
          rw [hr_def]; unfold qp; field_simp <;> ring
        have h2 : r * (1 - u) * (1 - (s.w1.xa:ℝ)/sc)⁻¹ ≤ r * (1 - u) * (1 - w)⁻¹ := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hr0.le (by linarith))
          exact inv_anti₀ (by linarith) (by linarith)
        linarith
    change (bsQjh a.R a.U a.Sh a.Rd s.w1.xa B).Contains _
    unfold bsQjh
    by_cases hBd : B.ra < SCz
    · rw [if_pos hBd]
      refine Iv.meet_contains hA_ ?_
      rw [qjh_eq hw0.ne' (sub_ne_zero.mpr (ne_of_gt huw)), ← hr_def, ← hδ_def, div_eq_mul_inv]
      exact DyadicInterval.neg_sound (DyadicInterval.mul_sound (DyadicInterval.mul_sound
        (DyadicInterval.sub_sound Iv.one_contains hU) hRd) (DyadicInterval.recip_sound (gdg hBd).1 hSh))
    · rw [if_neg hBd]; exact hA_
  -- σ and ν
  set σ := -(jn w / jn u) * (w * ((jn w - jn u)/(w - u))) with hσ_def
  have hσ_eq : σ = (jn w / jn u) * δ / ((w - u)/w) :=
    sigma_eq hw0.ne' (sub_ne_zero.mpr (ne_of_gt huw)) hJu.ne'
  have hθ_eq : (jn w / jn u) * δ = δ / (1 + (1 / jn w) * δ) := theta_eq hJw hJu
  have hσ0 : 0 ≤ σ := by rw [hσ_eq]; exact div_nonneg (mul_nonneg htau0.le hδ0) hsh0.le
  have hden0 : 0 < 1 + 1 / jn w * δ := by have := mul_nonneg hp0.le hδ0; linarith
  have hθ0 : 0 ≤ δ / (1 + 1 / jn w * δ) := div_nonneg hδ0 hden0.le
  -- -ĵ bounds
  have hnj1 : 1 / (1 - w) ≤ -(w * ((jn w - jn u)/(w - u))) := by
    have := mul_le_mul_of_nonneg_left hmvt.2 hw0.le
    have e : w * (-1 / qp w) = -(1 / (1 - w)) := by unfold qp; field_simp <;> ring
    linarith
  have hnj2 : -(w * ((jn w - jn u)/(w - u))) ≤ 1 / (r * (1 - u)) := by
    have := mul_le_mul_of_nonneg_left hmvt.1 hw0.le
    have e : w * (-1 / qp u) = -(1 / (r * (1 - u))) := by
      rw [hr_def]; unfold qp; field_simp <;> ring
    linarith
  have hσA : σ = (jn w / jn u) * (-(w * ((jn w - jn u)/(w - u)))) := by rw [hσ_def]; ring
  have hsLoA : (bsSigLoA a.Tau s.w1.xa : ℝ)/sc ≤ σ := by
    have hq := DyadicInterval.mul_sound hTau
      (DyadicInterval.recip_sound gw1 (DyadicInterval.sub_sound Iv.one_contains (Iv.pt_contains s.w1.xa)))
    refine (lo_div_le hq).trans ?_
    rw [hσA]
    apply mul_le_mul_of_nonneg_left _ htau0.le
    refine le_trans ?_ hnj1
    rw [one_div]; exact inv_anti₀ (by linarith) (by linarith)
  have hsLoB : B.ra < SCz → (bsSigLoB a.Sh a.P a.dlo : ℝ)/sc ≤ σ := by
    intro hBd
    obtain ⟨gSh0, gShh, gShl, gpd, -⟩ := gdg hBd
    have hq := DyadicInterval.mul_sound (DyadicInterval.mul_sound (Iv.pt_contains a.dlo)
      (DyadicInterval.recip_sound gpd (DyadicInterval.add_sound Iv.one_contains
        (DyadicInterval.mul_sound (Iv.pt_contains a.P.hi) (Iv.pt_contains a.dlo)))))
      (DyadicInterval.recip_sound gShh (Iv.pt_contains a.Sh.hi))
    refine (lo_div_le hq).trans ?_
    rw [hσ_eq, hθ_eq]
    have hth := theta_lower hp0.le hPhi hdlo0 hdlo
    have hshh : (w - u)/w ≤ (a.Sh.hi:ℝ)/sc := le_hi_div hSh
    rw [← div_eq_mul_inv, ← div_eq_mul_inv]
    calc (a.dlo:ℝ)/sc / (1 + (a.P.hi:ℝ)/sc * ((a.dlo:ℝ)/sc)) / ((a.Sh.hi:ℝ)/sc)
        ≤ δ / (1 + 1 / jn w * δ) / ((a.Sh.hi:ℝ)/sc) :=
          div_le_div_of_nonneg_right hth (hsh0.le.trans hshh)
      _ ≤ δ / (1 + 1 / jn w * δ) / ((w - u)/w) := div_le_div_of_nonneg_left hθ0 hsh0 hshh
  have hsLo : (a.sLo : ℝ)/sc ≤ σ := by
    change (bsSigLo a.Tau a.Sh a.P s.w1.xa a.dlo B : ℝ)/sc ≤ σ
    unfold bsSigLo
    by_cases hBd : B.ra < SCz
    · rw [if_pos hBd, Int.cast_max]
      rw [div_le_iff₀ hsc]
      exact max_le ((div_le_iff₀ hsc).mp hsLoA) ((div_le_iff₀ hsc).mp (hsLoB hBd))
    · rw [if_neg hBd]; exact hsLoA
  have hsHiA : A.ra ≠ 0 → σ ≤ (bsSigHiA a.Tau a.U A : ℝ)/sc := by
    intro hA0
    obtain ⟨hAr0, -, -⟩ := rnode_facts (n := n) hL (hAok hA0)
    have hq := DyadicInterval.mul_sound hTau (DyadicInterval.recip_sound (gia hA0).2
      (DyadicInterval.mul_sound (Iv.pt_contains A.ra) (DyadicInterval.sub_sound Iv.one_contains
        (Iv.pt_contains a.U.hi))))
    refine le_trans ?_ (le_hi_div hq)
    rw [hσA]
    apply mul_le_mul_of_nonneg_left _ htau0.le
    refine hnj2.trans ?_
    rw [one_div]
    have hpos : 0 < (A.ra:ℝ)/sc * (1 - (a.U.hi:ℝ)/sc) := by
      have := Iv.contains_pos (DyadicInterval.mul_sound (Iv.pt_contains A.ra)
        (DyadicInterval.sub_sound Iv.one_contains (Iv.pt_contains a.U.hi))) (gia hA0).2
      exact this
    have hU1 : 0 < 1 - (a.U.hi:ℝ)/sc := pos_of_mul_pos_right hpos hA'
    exact inv_anti₀ hpos (mul_le_mul hr1 (by linarith) hU1.le hr0.le)
  have hsHiB1 : A.ra ≠ 0 → B.ra < SCz → σ ≤ (bsSigHiB1 a.Sh a.P a.dhi : ℝ)/sc := by
    intro hA0 hBd
    obtain ⟨gSh0, gShh, gShl, gpd, gpdh⟩ := gdg hBd
    have hPlo0 : (0:ℝ) ≤ (a.P.lo:ℝ)/sc := div_nonneg (by exact_mod_cast gP0) hsc.le
    have hq := DyadicInterval.mul_sound (DyadicInterval.mul_sound (Iv.pt_contains a.dhi)
      (DyadicInterval.recip_sound (gpdh hA0) (DyadicInterval.add_sound Iv.one_contains
        (DyadicInterval.mul_sound (Iv.pt_contains a.P.lo) (Iv.pt_contains a.dhi)))))
      (DyadicInterval.recip_sound gShl (Iv.pt_contains a.Sh.lo))
    refine le_trans ?_ (le_hi_div hq)
    rw [hσ_eq, hθ_eq]
    have hth := theta_upper hPlo0 hPlo hδ0 (hdhi hA0)
    have hshl : (a.Sh.lo:ℝ)/sc ≤ (w - u)/w := lo_div_le hSh
    have hshl0 : (0:ℝ) < (a.Sh.lo:ℝ)/sc := Iv.contains_pos (Iv.pt_contains a.Sh.lo) gShl
    rw [← div_eq_mul_inv, ← div_eq_mul_inv]
    calc δ / (1 + 1 / jn w * δ) / ((w - u)/w) ≤ δ / (1 + 1 / jn w * δ) / ((a.Sh.lo:ℝ)/sc) :=
          div_le_div_of_nonneg_left hθ0 hshl0 hshl
      _ ≤ _ := div_le_div_of_nonneg_right hth hshl0.le
  have hsHiB0 : B.ra < SCz → 0 < a.P.lo → σ ≤ (bsSigHiB0 a.Sh a.P : ℝ)/sc := by
    intro hBd hP0
    obtain ⟨gSh0, gShh, gShl, gpd, -⟩ := gdg hBd
    have hPl : (0:ℝ) < (a.P.lo:ℝ)/sc := div_pos (by exact_mod_cast hP0) hsc
    have hP0' : 0 < (Iv.pt a.P.lo).lo := hP0
    have hq := DyadicInterval.mul_sound (DyadicInterval.recip_sound hP0' (Iv.pt_contains a.P.lo))
      (DyadicInterval.recip_sound gShl (Iv.pt_contains a.Sh.lo))
    refine le_trans ?_ (le_hi_div hq)
    rw [hσ_eq, hθ_eq]
    have hth := theta_le_inv hPl hPlo hδ0
    have hshl : (a.Sh.lo:ℝ)/sc ≤ (w - u)/w := lo_div_le hSh
    have hshl0 : (0:ℝ) < (a.Sh.lo:ℝ)/sc := Iv.contains_pos (Iv.pt_contains a.Sh.lo) gShl
    rw [← div_eq_mul_inv, ← one_div]
    calc δ / (1 + 1 / jn w * δ) / ((w - u)/w) ≤ δ / (1 + 1 / jn w * δ) / ((a.Sh.lo:ℝ)/sc) :=
          div_le_div_of_nonneg_left hθ0 hshl0 hshl
      _ ≤ 1 / ((a.P.lo:ℝ)/sc) / ((a.Sh.lo:ℝ)/sc) := div_le_div_of_nonneg_right hth hshl0.le
  have hsHi : ∀ hv, a.sHi = some hv → σ ≤ (hv:ℝ)/sc := by
    intro hv hsv
    change bsSigHi a.Tau a.Sh a.P a.U A B a.dhi = some hv at hsv
    unfold bsSigHi at hsv
    by_cases hA0 : A.ra = 0
    · rw [if_pos hA0] at hsv
      by_cases hc : B.ra < SCz ∧ 0 < a.P.lo
      · rw [if_pos hc] at hsv
        cases hsv; exact hsHiB0 hc.1 hc.2
      · rw [if_neg hc] at hsv; cases hsv
    · rw [if_neg hA0] at hsv
      by_cases hBd : B.ra < SCz
      · rw [if_pos hBd] at hsv
        cases hsv; rw [Int.cast_min]
        rw [le_div_iff₀ hsc]
        exact le_min ((le_div_iff₀ hsc).mp (hsHiA hA0)) ((le_div_iff₀ hsc).mp (hsHiB1 hA0 hBd))
      · rw [if_neg hBd] at hsv
        cases hsv; exact hsHiA hA0
  have hNu : a.Nu.Contains (1 / (1 + σ)) := by
    change (bsNu a.sLo a.sHi).Contains _
    unfold bsNu
    have hsLo0 : (0:ℝ) ≤ (a.sLo:ℝ)/sc := div_nonneg (by exact_mod_cast gsl) hsc.le
    have hq := DyadicInterval.recip_sound gsl1 (DyadicInterval.add_sound Iv.one_contains
      (Iv.pt_contains a.sLo))
    refine ⟨?_, hi_ge hq rfl ?_⟩
    · rcases hsv : a.sHi with _ | hv
      · change ((0:ℤ):ℝ) ≤ _; rw [Int.cast_zero]
        exact mul_nonneg hsc.le (one_div_pos.mpr (by linarith)).le
      · have hpos : 0 < (Iv.one.add (Iv.pt hv)).lo := by
          have := gsHi
          rw [hsv] at this
          simpa [sHiOK] using this
        have hq2 := DyadicInterval.recip_sound hpos
          (DyadicInterval.add_sound Iv.one_contains (Iv.pt_contains hv))
        change ((Iv.one.add (Iv.pt hv)).recip.lo : ℝ) ≤ _
        refine lo_le hq2 rfl ?_
        have hle := hsHi hv hsv
        rw [one_div]; exact inv_anti₀ (by linarith) (by linarith)
    · rw [one_div]; exact inv_anti₀ (by linarith) (by linarith)
  have hNus : a.Nus.Contains (1 / (1 + σ) * σ) := by
    have hσ1 : 1 + σ ≠ 0 := (by linarith : (0:ℝ) < 1 + σ).ne'
    have e : 1 / (1 + σ) * σ = 1 - 1 / (1 + σ) := by field_simp <;> ring
    rw [e]; exact DyadicInterval.sub_sound Iv.one_contains hNu
  -- the contact argument S/(2(w-u))
  have hS := entropySum_pos' hu huw hw12
  have hYeq : ((1 / jn w) * entropySum u w / w) * (2 * ((1 / jn w) * ((w - u)/w)))⁻¹ =
      entropySum u w / (2 * (w - u)) := by
    field_simp
  have hY2 : two = true → a.IY.Contains (entropySum u w / (2 * (w - u))) := by
    intro ht
    rw [← hYeq]
    exact DyadicInterval.mul_sound hSp (DyadicInterval.recip_sound (gtw ht)
      (DyadicInterval.mul_sound Iv.two_contains (DyadicInterval.mul_sound hP hSh)))
  have hY1 : two = false → (a.Ylo:ℝ)/sc ≤ entropySum u w / (2 * (w - u)) := by
    intro hf
    have hq := DyadicInterval.mul_sound (Iv.pt_contains a.Sp.lo)
      (DyadicInterval.recip_sound (gon hf) (DyadicInterval.mul_sound Iv.two_contains
        (DyadicInterval.mul_sound (Iv.pt_contains a.P.hi) (Iv.pt_contains a.Sh.hi))))
    refine (lo_div_le hq).trans ?_
    rw [← hYeq]
    have hSplo : (a.Sp.lo:ℝ)/sc ≤ (1 / jn w) * entropySum u w / w := lo_div_le hSp
    have hSplo0 : (0:ℝ) < (a.Sp.lo:ℝ)/sc := div_pos (by exact_mod_cast gSp) hsc
    have hshh : (w - u)/w ≤ (a.Sh.hi:ℝ)/sc := le_hi_div hSh
    have hden : 0 < 2 * ((1 / jn w) * ((w - u)/w)) := by have := mul_pos hp0 hsh0; linarith
    rw [← div_eq_mul_inv, ← div_eq_mul_inv]
    calc (a.Sp.lo:ℝ)/sc / (2 * ((a.P.hi:ℝ)/sc * ((a.Sh.hi:ℝ)/sc)))
        ≤ (a.Sp.lo:ℝ)/sc / (2 * ((1 / jn w) * ((w - u)/w))) := by
          apply div_le_div_of_nonneg_left hSplo0.le hden
          have := mul_le_mul hPhi hshh hsh0.le (hp0.le.trans hPhi)
          linarith
      _ ≤ _ := div_le_div_of_nonneg_right hSplo hden.le
  exact bsFinal_sound hL hbr hfin hu huw hw12 gSp hP hOm hW hU hSh hTau hQu hQw hKh hSp hQjh
    hNu hNus hσ0 hY2 hY1

#print axioms bs_cell_sound

end CKLaneA1


