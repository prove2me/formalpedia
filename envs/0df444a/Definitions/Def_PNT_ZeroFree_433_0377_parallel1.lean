-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0377_parallel1
-- name    : PNT_ZeroFree_433_0377_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:13:56.744498+00:00
-- url     : https://prove2.me/theorems/3f5bf223-5558-4aa9-a2ae-6564e0a71761
-- title:
--   Zero-free region foundations: Hecke.DetectorSlotSelection, Moments.SlotRemoval, CompactProfileFamily [0377_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Hecke.DetectorSlotSelection
--   - OAI.NumberTheory.DirichletL.Moments.SlotRemoval
--   - OAI.NumberTheory.DirichletL.CompactProfileFamily
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/DetectorSlotSelection.lean#L9-L152
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Moments/SlotRemoval.lean#L9-L69
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CompactProfileFamily.lean#L10-L128

import Definitions.Def_PNT_ZeroFree_433_0145
import Definitions.Def_PNT_ZeroFree_433_0152
import Definitions.Def_PNT_ZeroFree_433_0250_parallel1

/- Supporting zero-free-region lemmas, grouped by intact source scopes.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/DetectorSlotSelection.lean#L9-L152
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Moments/SlotRemoval.lean#L9-L69
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CompactProfileFamily.lean#L10-L128
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Hecke.DetectorSlotSelection
section
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorSlotSelection

theorem whole_slots {α : Type*} (s : Finset α) (w g : α→ℝ) (G mesh : ℝ)
    (hG : 0≤G) (hmesh : 0≤mesh)
    (hw : ∀ i∈s, 0≤w i) (hwm : ∀ i∈s, w i≤mesh)
    (hg : ∀ i∈s, 0≤g i) (hgG : ∀ i∈s, g i≤G)
    (q z : ℝ) (hq : 0≤q) (hqG : q≤G) (hz : 0≤z)
    (hzs : z≤∑ i∈s, w i) (hmean : q*(∑ i∈s, w i)≤∑ i∈s, w i*g i) :
    ∃ T : Finset α, T⊆s ∧ (∑ i∈T, w i)≤z ∧ q*z-G*mesh≤∑ i∈T, w i*g i := by
  classical
  induction s using Finset.strongInductionOn generalizing q z with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨a,ha,hmax⟩ := s.exists_max_image g hs
      by_cases hza : z≤w a
      · refine ⟨∅,Finset.empty_subset _,by simpa using hz,?_⟩
        have hzmesh : z≤mesh := hza.trans (hwm a ha)
        have hprod := mul_le_mul hqG hzmesh hz hG
        simpa only [Finset.sum_empty] using (sub_nonpos.mpr hprod)
      have haz : w a<z := lt_of_not_ge hza
      let s' := s.erase a
      have hss : s'⊂s := Finset.erase_ssubset ha
      have hsub : s'⊆s := Finset.erase_subset a s
      have hsum : ∑ i∈s, w i=w a+∑ i∈s', w i := by
        simpa [s',add_comm] using (Finset.sum_erase_add s w ha).symm
      have hgain : ∑ i∈s, w i*g i=w a*g a+∑ i∈s', w i*g i := by
        simpa [s',add_comm] using (Finset.sum_erase_add s (fun i => w i*g i) ha).symm
      let W := ∑ i∈s', w i
      let A := ∑ i∈s', w i*g i
      have hW : 0<W := by rw [hsum] at hzs; dsimp [W]; linarith
      have hA : 0≤A := Finset.sum_nonneg (fun i hi => mul_nonneg (hw i (hsub hi)) (hg i (hsub hi)))
      have hAg : A≤W*g a := by
        calc
          _ ≤ ∑ i∈s', w i*g a := Finset.sum_le_sum (fun i hi =>
            mul_le_mul_of_nonneg_left (hmax i (hsub hi)) (hw i (hsub hi)))
          _ = _ := by dsimp [W]; rw [Finset.sum_mul]
      let q' := A/W
      have hq' : 0≤q' := div_nonneg hA hW.le
      have hq'a : q'≤g a := (div_le_iff₀ hW).mpr (by simpa [mul_comm] using hAg)
      have hq'G : q'≤G := hq'a.trans (hgG a ha)
      have he : q'*W=A := div_mul_cancel₀ A hW.ne'
      have hz' : 0≤z-w a := sub_nonneg.mpr haz.le
      have hzs' : z-w a≤∑ i∈s', w i := by rw [hsum] at hzs; linarith
      obtain ⟨T,hTs,hTz,hTgain⟩ := ih s' hss
        (fun i hi => hw i (hsub hi)) (fun i hi => hwm i (hsub hi))
        (fun i hi => hg i (hsub hi)) (fun i hi => hgG i (hsub hi))
        q' (z-w a) hq' hq'G hz' hzs' he.le
      have haT : a∉T := fun h => (Finset.mem_erase.mp (hTs h)).1 rfl
      refine ⟨insert a T,Finset.insert_subset_iff.mpr ⟨ha,hTs.trans hsub⟩,?_,?_⟩
      · rw [Finset.sum_insert haT]
        linarith
      · rw [Finset.sum_insert haT]
        have hprefix : q*z≤w a*g a+q'*(z-w a) := by
          rw [hsum,hgain] at hmean
          change q*(w a+W)≤w a*g a+A at hmean
          rw [←he] at hmean
          by_cases hqq : q≤q'
          · have h1 := mul_le_mul_of_nonneg_right hqq hz
            have h2 := mul_le_mul_of_nonneg_left hq'a (hw a ha)
            nlinarith
          · have hqq' : 0≤q-q' := by linarith
            have h1 := mul_le_mul_of_nonneg_left hzs hqq'
            rw [hsum] at h1
            change (q-q')*z≤(q-q')*(w a+W) at h1
            nlinarith
        linarith
    · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      have hz0 : z=0 := by simpa using le_antisymm hzs hz
      refine ⟨∅,Finset.empty_subset _,by simpa using hz,?_⟩
      simp only [Finset.sum_empty,hz0,mul_zero,zero_sub]
      exact neg_nonpos.mpr (mul_nonneg hG hmesh)

theorem whole_positive_slots {α : Type*} (s : Finset α) (w g : α→ℝ) (G mesh : ℝ)
    (hG : 0≤G) (hmesh : 0≤mesh)
    (hw : ∀ i∈s, 0≤w i) (hwm : ∀ i∈s, w i≤mesh)
    (hgG : ∀ i∈s, g i≤G)
    (q z : ℝ) (hq : 0≤q) (hqG : q≤G) (hz : 0≤z)
    (hzs : z≤∑ i∈s, w i) (hmean : q*(∑ i∈s, w i)≤∑ i∈s, w i*max (g i) 0) :
    ∃ T : Finset α, T⊆s ∧ (∀ i∈T, 0<g i) ∧
      (∑ i∈T, w i)≤z ∧ q*z-G*mesh≤∑ i∈T, w i*g i := by
  classical
  obtain ⟨T,hTs,hTz,hTgain⟩ := whole_slots s w (fun i => max (g i) 0) G mesh hG hmesh
    hw hwm (fun i hi => le_max_right _ _) (fun i hi => max_le (hgG i hi) hG)
    q z hq hqG hz hzs hmean
  let P := T.filter (fun i => 0<g i)
  have hPT : P⊆T := Finset.filter_subset _ _
  refine ⟨P,hPT.trans hTs,fun i hi => (Finset.mem_filter.mp hi).2,?_,?_⟩
  · exact (Finset.sum_le_sum_of_subset_of_nonneg hPT (fun i hi _ => hw i (hTs hi))).trans hTz
  · have he : (∑ i∈T, w i*max (g i) 0)=∑ i∈P, w i*g i := by
      calc
        _ = ∑ i∈P, w i*max (g i) 0 := by
          symm
          apply Finset.sum_subset hPT
          intro i hi hn
          have hg : g i≤0 := le_of_not_gt (fun h => hn (Finset.mem_filter.mpr ⟨hi,h⟩))
          rw [max_eq_right hg,mul_zero]
        _ = _ := Finset.sum_congr rfl (fun i hi => by
          rw [max_eq_left (Finset.mem_filter.mp hi).2.le])
    rwa [he] at hTgain

theorem selected_product_spike {α : Type*} (s : Finset α) (w g : α→ℝ)
    (U δ mesh q z : ℝ) (hU : 1≤U) (hδ : 0≤δ) (hmesh : 0≤mesh)
    (hw : ∀ i∈s, 0≤w i) (hwm : ∀ i∈s, w i≤mesh)
    (hg : ∀ i∈s, g i≤δ/2) (hq : 0≤q) (hqδ : q≤δ/2) (hz : 0≤z)
    (hzs : z≤∑ i∈s, w i) (hmean : q*(∑ i∈s, w i)≤∑ i∈s, w i*max (g i) 0)
    : ∃ T : Finset α, T⊆s ∧ (∀ i∈T, 0<g i) ∧ (∑ i∈T, w i)≤z ∧
      ∀ Q : α→ℂ, (∀ i∈s, 0<g i → U^(2*w i*g i)≤‖Q i‖^2) →
        U^(2*q*z-δ*mesh)≤‖∏ i∈T, Q i‖^2 := by
  obtain ⟨T,hTs,hTpos,hTz,hgain⟩ := whole_positive_slots s w g (δ/2) mesh
    (by positivity) hmesh hw hwm hg q z hq hqδ hz hzs hmean
  refine ⟨T,hTs,hTpos,hTz,?_⟩
  intro Q hQ
  have hUp : 0<U := by linarith
  calc
    _ ≤ U^(∑ i∈T, 2*w i*g i) := Real.rpow_le_rpow_of_exponent_le hU (by
      have he : (∑ i∈T, 2*w i*g i)=2*(∑ i∈T, w i*g i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [he]
      linarith)
    _ = ∏ i∈T, U^(2*w i*g i) := Real.rpow_sum_of_pos hUp _ _
    _ ≤ ∏ i∈T, ‖Q i‖^2 := Finset.prod_le_prod (fun i hi => Real.rpow_nonneg hUp.le _)
      (fun i hi => hQ i (hTs hi) (hTpos i hi))
    _ = _ := by rw [norm_prod,Finset.prod_pow]

theorem selected_product_with_decrement {α : Type*} (s : Finset α) (w g : α→ℝ)
    (U δ mesh q z ν : ℝ) (hU : 1≤U) (hδ : 0≤δ) (hmesh : 0≤mesh)
    (hw : ∀ i∈s, 0≤w i) (hwm : ∀ i∈s, w i≤mesh)
    (hg : ∀ i∈s, g i≤δ/2) (hq : 0≤q) (hqδ : q≤δ/2) (hz : 0≤z) (hν : 0≤ν)
    (hzs : z≤∑ i∈s, w i) (hmean : q*(∑ i∈s, w i)≤∑ i∈s, w i*max (g i) 0) :
    ∃ T : Finset α, T⊆s ∧ (∀ i∈T, 0<g i) ∧
      (∑ i∈T, w i)≤max 0 (z-ν) ∧
      ∀ Q : α→ℂ, (∀ i∈s, 0<g i → U^(2*w i*g i)≤‖Q i‖^2) →
        U^(2*q*z-2*q*ν-δ*mesh)≤‖∏ i∈T, Q i‖^2 := by
  have hcap : max 0 (z-ν)≤z := max_le hz (by linarith)
  obtain ⟨T,hTs,hTp,hTw,hTb⟩ := selected_product_spike s w g U δ mesh q (max 0 (z-ν))
    hU hδ hmesh hw hwm hg hq hqδ (le_max_left _ _) (hcap.trans hzs) hmean
  refine ⟨T,hTs,hTp,hTw,?_⟩
  intro Q hQ
  apply le_trans _ (hTb Q hQ)
  apply Real.rpow_le_rpow_of_exponent_le hU
  have hh := mul_le_mul_of_nonneg_left (le_max_right 0 (z-ν)) (show 0≤2*q by positivity)
  nlinarith

end SevenEighths.HeckeDetectorSlotSelection

end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Moments.SlotRemoval
section
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentSlotRemoval

theorem whole_slot_removal {α : Type*} (s : Finset α) (length : α → ℝ)
    (η κ F : ℝ) (hη : 0 ≤ η) (hκ : 0 < κ) (hF : 0 ≤ F)
    (hL : ∀ i ∈ s, 0 ≤ length i) (hmesh : ∀ i ∈ s, length i ≤ η) :
    ∃ R : Finset α, R ⊆ s ∧
      (∑ i ∈ R, length i) ≤ min (∑ i ∈ s, length i) (F/(6*κ)+η) ∧
      (R=s ∨ F ≤ 6*κ*(∑ i ∈ R, length i)) := by
  have hthreshold : 0 ≤ F/(6*κ) := div_nonneg hF (by positivity)
  by_cases htotal : (∑ i ∈ s, length i) ≤ F/(6*κ)
  · refine ⟨s,Finset.Subset.refl _,le_min le_rfl ?_,Or.inl rfl⟩
    linarith
  · have htarget : 0 ≤ (∑ i ∈ s, length i)-F/(6*κ) := by linarith
    obtain ⟨T,hTs,hTupper,hTlower⟩ := HeckeDetectorSlotSelection.whole_slots
      s length (fun _ => 1) 1 η (by norm_num) hη hL hmesh
      (by intros; norm_num) (by intros; norm_num) 1
      ((∑ i ∈ s, length i)-F/(6*κ)) (by norm_num) (by norm_num)
      htarget (by linarith) (by simp)
    simp only [one_mul,mul_one] at hTlower
    have hsum : (∑ i ∈ s, length i)=(∑ i ∈ s\T, length i)+(∑ i ∈ T, length i) :=
      (Finset.sum_sdiff hTs).symm
    have hTnonneg : 0 ≤ ∑ i ∈ T, length i := Finset.sum_nonneg (fun i hi => hL i (hTs hi))
    refine ⟨s\T,Finset.sdiff_subset,le_min (by linarith) (by linarith),Or.inr ?_⟩
    have hremove : F/(6*κ) ≤ ∑ i ∈ s\T, length i := by linarith
    exact (div_le_iff₀ (by positivity : 0 < 6*κ)).mp hremove |>.trans_eq (mul_comm _ _)

theorem removal_cost {α : Type*} (s : Finset α) (length : α → ℝ)
    (η κ F : ℝ) (hη : 0 ≤ η) (hκ : 0 < κ) (hF : 0 ≤ F)
    (hL : ∀ i ∈ s, 0 ≤ length i) (hmesh : ∀ i ∈ s, length i ≤ η) :
    ∃ R : Finset α, R ⊆ s ∧
      κ*(∑ i ∈ R, length i) ≤ F/6+κ*η ∧
      (R=s ∨ F-6*κ*(∑ i ∈ R, length i) ≤ 0) := by
  obtain ⟨R,hRs,hR,hpay⟩ := whole_slot_removal s length η κ F hη hκ hF hL hmesh
  refine ⟨R,hRs,?_,hpay.imp_right sub_nonpos.mpr⟩
  have hh := mul_le_mul_of_nonneg_left (hR.trans (min_le_right _ _)) hκ.le
  have he : κ*(F/(6*κ)+η)=F/6+κ*η := by field_simp
  rwa [he] at hh

theorem actual_product_removal {α : Type*} (s : Finset α) (length : α → ℝ)
    (η κ F : ℝ) (hη : 0 ≤ η) (hκ : 0 < κ) (hF : 0 ≤ F)
    (hL : ∀ i ∈ s, 0 ≤ length i) (hmesh : ∀ i ∈ s, length i ≤ η) :
    ∃ R : Finset α, R ⊆ s ∧ (R=s ∨ F-6*κ*(∑ i ∈ R, length i) ≤ 0) ∧
      ∀ (Z : ℝ), 1 ≤ Z → ∀ (C : α → ℝ), (∀ i ∈ s, 0 ≤ C i) →
      ∀ (Q : α → ℂ), (∀ i ∈ s, ‖Q i‖^2 ≤ C i*Z^(κ*length i)) →
      ‖∏ i ∈ s, Q i‖^2 ≤
        (∏ i ∈ R, C i)*Z^(F/6+κ*η)*‖∏ i ∈ s\R, Q i‖^2 := by
  obtain ⟨R,hRs,hcost,hpay⟩ := removal_cost s length η κ F hη hκ hF hL hmesh
  refine ⟨R,hRs,hpay,?_⟩
  intro Z hZ C hC Q hQ
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hremoved : ‖∏ i ∈ R, Q i‖^2 ≤ (∏ i ∈ R, C i)*Z^(F/6+κ*η) := by
    rw [norm_prod,← Finset.prod_pow]
    calc
      _ ≤ ∏ i ∈ R, C i*Z^(κ*length i) :=
        Finset.prod_le_prod (fun i hi => sq_nonneg _) (fun i hi => hQ i (hRs hi))
      _ = (∏ i ∈ R, C i)*Z^(κ*(∑ i ∈ R, length i)) := by
        rw [Finset.prod_mul_distrib,Finset.mul_sum,Real.rpow_sum_of_pos hZpos]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ hcost) (Finset.prod_nonneg (fun i hi => hC i (hRs hi)))
  have he : (∏ i ∈ s, Q i)=(∏ i ∈ s\R, Q i)*(∏ i ∈ R, Q i) :=
    (Finset.prod_sdiff hRs).symm
  rw [he,norm_mul,mul_pow,mul_comm (‖∏ i ∈ s\R, Q i‖^2)]
  exact mul_le_mul_of_nonneg_right hremoved (sq_nonneg _)

end SevenEighths.CenteredMomentSlotRemoval

end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.CompactProfileFamily
section
namespace OAI

noncomputable section
open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace SevenEighths.CompactProfileFamily
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem section_deriv_smooth (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun p : E × ℝ => deriv (F p.1) p.2) := by
  have hFp : ContDiff ℝ ∞
      (Function.uncurry (fun p : E × ℝ => F p.1)) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd := hFp.fderiv contDiff_snd (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  simpa only [deriv] using hd.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem section_iteratedDeriv_smooth (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : E × ℝ => iteratedDeriv j (F p.1) p.2) := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero, Function.uncurry_def] using hF
  | succ j ih =>
    simpa only [iteratedDeriv_succ] using
      section_deriv_smooth (fun σ => iteratedDeriv j (F σ)) ih

theorem tsupport_iteratedDeriv_subset (f : ℝ → ℂ) (j : ℕ) :
    tsupport (iteratedDeriv j f) ⊆ tsupport f := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

theorem compact_family_deriv_integrable (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (σ : E) (j : ℕ) :
    Integrable (iteratedDeriv j (F σ)) := by
  have hs : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (iteratedDeriv j (F σ)) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    exact (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  exact (hs.continuous_iteratedDeriv j (by first | simp | exact_mod_cast le_top)).integrable_of_hasCompactSupport hc

theorem compact_family_deriv_L1_bound (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set E) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, (∫ u : ℝ, ‖iteratedDeriv j (F σ) u‖) ≤ C := by
  have hc := (section_iteratedDeriv_smooth F hF j).continuous.norm
  obtain ⟨M, hM⟩ := (hJ.prod hK).bddAbove_image hc.continuousOn
  let C : ℝ := (|M| + 1) * (volume.real K + 1)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro σ hσ
  have hbound : ∀ u ∈ K, ‖iteratedDeriv j (F σ) u‖ ≤ |M| + 1 := by
    intro u hu
    exact (hM (Set.mem_image_of_mem _ (show (σ, u) ∈ J ×ˢ K from ⟨hσ, hu⟩))).trans (by linarith [le_abs_self M])
  have hs : Function.support (iteratedDeriv j (F σ)) ⊆ K :=
    (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  have hzero : ∀ u, u ∉ K → ‖iteratedDeriv j (F σ) u‖ = 0 := by
    intro u hu
    have hz : iteratedDeriv j (F σ) u = 0 := by
      by_contra hn
      exact hu (hs hn)
    simp [hz]
  have hi := norm_setIntegral_le_of_norm_le_const («μ» := volume) (f := fun u => ‖iteratedDeriv j (F σ) u‖)
    hK.measure_lt_top (C := |M| + 1) (fun u hu => by simpa using hbound u hu)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero] at hi
  rw [Real.norm_of_nonneg (integral_nonneg (fun u => norm_nonneg _))] at hi
  exact hi.trans (by dsimp [C]; nlinarith [abs_nonneg M])

theorem compact_family_fourier_power_bound (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set E) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      |w| ^ j * ‖𝓕 (F σ) w‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compact_family_deriv_L1_bound F hF K hK hsupp J hJ j
  refine ⟨C / (2 * Real.pi) ^ j, by positivity, ?_⟩
  intro σ hσ w
  have hs : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hfour := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) hs
    (fun k _ => compact_family_deriv_integrable F hF K hK hsupp σ k)
    (by simp : (j : ℕ∞) ≤ ⊤)
  have hid : (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) =
      ‖𝓕 (iteratedDeriv j (F σ)) w‖ := by
    rw [hfour]
    simp only [norm_smul, norm_pow, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    ring
  have hn : ‖𝓕 (iteratedDeriv j (F σ)) w‖ ≤ C := by
    apply (VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) (iteratedDeriv j (F σ)) w).trans
    exact hb σ hσ
  apply (le_div_iff₀ (by positivity : 0 < (2 * Real.pi) ^ j)).mpr
  rw [← hid] at hn
  calc
    _ = (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) := mul_comm _ _
    _ ≤ C := hn

theorem compact_family_fourier_weighted_bound (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set E) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      (1 + |w|) ^ j * ‖𝓕 (F σ) w‖ ≤ C := by
  obtain ⟨C₀, hC₀, h0⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ 0
  obtain ⟨Cj, hCj, hj⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ j
  refine ⟨2 ^ j * (C₀ + Cj), by positivity, ?_⟩
  intro σ hσ w
  have hbase : ‖𝓕 (F σ) w‖ ≤ C₀ := by simpa using h0 σ hσ w
  by_cases hw : |w| ≤ 1
  · calc
      _ ≤ 2 ^ j * ‖𝓕 (F σ) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ ≤ 2 ^ j * C₀ := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have hw' : 1 ≤ |w| := le_of_lt (lt_of_not_ge hw)
    calc
      _ ≤ (2 * |w|) ^ j * ‖𝓕 (F σ) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ = 2 ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) := by rw [mul_pow, mul_assoc]
      _ ≤ 2 ^ j * Cj := mul_le_mul_of_nonneg_left (hj σ hσ w) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end SevenEighths.CompactProfileFamily

end

end OAI

end


