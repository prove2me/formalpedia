-- Prove2me | solution 1 for AssortSearch.MNLQC.Supplement.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:16:19.764267+00:00
-- url     : https://prove2.me/submissions/b194b92e-b7cb-4186-9d64-ea0c7942b427

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_AssortSearch_Cannibal_Model
import Definitions.Def_AssortSearch_FullAssort_Model
import Definitions.Def_AssortSearch_HeurEq_Model
import Definitions.Def_AssortSearch_MNLQC_Supplement_Model

open MeasureTheory RetailVariety.Structure

open AssortSearch
open AssortSearch.MNLQC
open AssortSearch.MNLQC.Supplement

/-- **Theorem 7** (p. 22), in both search models. Take any assortment `1 ≤ x ≤ n` and the
preferences `v̂(x)` estimated from it. With any narrower assortment `x' < x` the no-search model
under-estimates the no-purchase demand, `d_0(x') ≥ q_0^m(x' | v̂(x))`; with any deeper assortment
`x < x'' ≤ n` it over-estimates it, `d_0(x'') ≤ q_0^m(x'' | v̂(x))`. The first conjunct is the
independent assortment model (threshold parameter `λ > 0`), the second the overlapping assortment
model (scale `μ > 0`, search cost `b > 0`, threshold `Ū(x)` depending on the depth). -/
theorem solution {n : ℕ} (lam μ b : ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (hv : ∀ i, 0 < v i) (hanti : Antitone v) (hv0 : 0 < v0) (hlam : 0 < lam)
    (hμ : 0 < μ) (hb : 0 < b)
    (x : ℕ) (hx1 : 1 ≤ x) (hxn : x ≤ n) :
    ((∀ x' : ℕ, x' < x →
        AssortSearch.HeurEq.shareNoPurchase (AssortSearch.HeurEq.estPref lam v v0 x)
            (AssortSearch.HeurEq.estPrefNoPurchase lam v v0 x) x' ≤
          AssortSearch.HeurEq.demandNoPurchase lam v v0 x') ∧
      (∀ x'' : ℕ, x < x'' → x'' ≤ n →
        AssortSearch.HeurEq.demandNoPurchase lam v v0 x'' ≤
          AssortSearch.HeurEq.shareNoPurchase (AssortSearch.HeurEq.estPref lam v v0 x)
            (AssortSearch.HeurEq.estPrefNoPurchase lam v v0 x) x'')) ∧
    ((∀ x' : ℕ, x' < x →
        AssortSearch.HeurEq.shareNoPurchase (estPrefOv μ b v v0 x)
            (estPrefNoPurchaseOv μ b v v0 x) x' ≤
          demandNoPurchaseOv μ b v v0 x') ∧
      (∀ x'' : ℕ, x < x'' → x'' ≤ n →
        demandNoPurchaseOv μ b v v0 x'' ≤
          AssortSearch.HeurEq.shareNoPurchase (estPrefOv μ b v v0 x)
            (estPrefNoPurchaseOv μ b v v0 x) x'')) := by
              classical
              have hn : 0 < n := by omega
              set S : ℕ → ℝ := fun y => ∑ j ∈ popularSet n y, v j with hSdef
              have hS0 : ∀ y, 0 ≤ S y := fun y => Finset.sum_nonneg (fun j _ => (hv j).le)
              have hsub : ∀ y z, y ≤ z → popularSet n y ⊆ popularSet n z := by
                intro y z hyz j hj
                simp only [popularSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
                omega
              have hSmono : ∀ y z, y ≤ z → S y ≤ S z := by
                intro y z hyz
                exact Finset.sum_le_sum_of_subset_of_nonneg (hsub y z hyz) (fun j _ _ => (hv j).le)
              -- the generic comparison
              have generic : ∀ (dem : ℕ → Fin n → ℝ) (g : ℕ → ℝ),
                  (∀ y, y ≤ n → ∀ i, dem y i = v i / (S y + g y + v0)) →
                  (∀ y, y ≤ n → 0 ≤ g y) →
                  (∀ y z, y ≤ z → z ≤ n → g z ≤ g y) →
                  ((∀ x' : ℕ, x' < x →
                    AssortSearch.HeurEq.shareNoPurchase
                      (fun i => if i.val < x then dem x i / (if h : 0 < n then dem x ⟨0, h⟩ else 0)
                        else dem n i / (if h : 0 < n then dem n ⟨0, h⟩ else 0))
                      ((1 - ∑ i ∈ popularSet n x, dem x i) / (if h : 0 < n then dem x ⟨0, h⟩ else 0)) x' ≤
                    1 - ∑ i ∈ popularSet n x', dem x' i) ∧
                  (∀ x'' : ℕ, x < x'' → x'' ≤ n →
                    1 - ∑ i ∈ popularSet n x'', dem x'' i ≤
                    AssortSearch.HeurEq.shareNoPurchase
                      (fun i => if i.val < x then dem x i / (if h : 0 < n then dem x ⟨0, h⟩ else 0)
                        else dem n i / (if h : 0 < n then dem n ⟨0, h⟩ else 0))
                      ((1 - ∑ i ∈ popularSet n x, dem x i) / (if h : 0 < n then dem x ⟨0, h⟩ else 0)) x'')) := by
                intro dem g hdem hg0 hgmono
                have hpos : ∀ y, y ≤ n → 0 < S y + g y + v0 := fun y hy => by linarith [hS0 y, hg0 y hy]
                have hD : ∀ y, y ≤ n → 1 - ∑ i ∈ popularSet n y, dem y i = (g y + v0) / (S y + g y + v0) := by
                  intro y hy
                  rw [Finset.sum_congr rfl (fun i _ => hdem y hy i), ← Finset.sum_div]
                  have := hpos y hy
                  field_simp
                  ring
                have hv1 := hv ⟨0, hn⟩
                have hest : (fun i : Fin n => if i.val < x then dem x i / (if h : 0 < n then dem x ⟨0, h⟩ else 0)
                        else dem n i / (if h : 0 < n then dem n ⟨0, h⟩ else 0)) = fun i => v i / v ⟨0, hn⟩ := by
                  funext i
                  have h1 := hpos x hxn
                  have h2 := hpos n le_rfl
                  rw [dif_pos hn, dif_pos hn]
                  split_ifs
                  · rw [hdem x hxn, hdem x hxn]; field_simp
                  · rw [hdem n le_rfl, hdem n le_rfl]; field_simp
                have hq : ∀ y, AssortSearch.HeurEq.shareNoPurchase
                      (fun i => if i.val < x then dem x i / (if h : 0 < n then dem x ⟨0, h⟩ else 0)
                        else dem n i / (if h : 0 < n then dem n ⟨0, h⟩ else 0))
                      ((1 - ∑ i ∈ popularSet n x, dem x i) / (if h : 0 < n then dem x ⟨0, h⟩ else 0)) y
                      = (g x + v0) / (S y + g x + v0) := by
                  intro y
                  rw [hest, hD x hxn, dif_pos hn, hdem x hxn]
                  unfold AssortSearch.HeurEq.shareNoPurchase
                  rw [← Finset.sum_div]
                  have h1 := hpos x hxn
                  have h3 : 0 < S y + g x + v0 := by linarith [hS0 y, hg0 x hxn]
                  have h4 : (∑ j ∈ popularSet n y, v j) = S y := rfl
                  rw [h4]
                  field_simp
                  rw [show S y + (g x + v0) = S y + g x + v0 by ring]
                  field_simp
                refine ⟨?_, ?_⟩
                · intro y hy
                  rw [hq, hD y (by omega)]
                  have h3 : 0 < S y + g x + v0 := by linarith [hS0 y, hg0 x hxn]
                  have h4 := hpos y (by omega)
                  rw [div_le_div_iff₀ h3 h4]
                  have := mul_le_mul_of_nonneg_left (hgmono y x hy.le hxn) (hS0 y)
                  nlinarith
                · intro y hy hyn
                  rw [hq, hD y hyn]
                  have h3 : 0 < S y + g x + v0 := by linarith [hS0 y, hg0 x hxn]
                  have h4 := hpos y hyn
                  rw [div_le_div_iff₀ h4 h3]
                  have := mul_le_mul_of_nonneg_left (hgmono x y hy.le hyn) (hS0 y)
                  nlinarith
              have key : ∀ (L s vi : ℝ), 0 < L → 0 ≤ s →
                  vi / (s + v0) * (1 - Real.exp (-(L * (v0 + s)))) =
                    vi / (s + (v0 + s) / (Real.exp (L * (v0 + s)) - 1) + v0) := by
                intro L s vi hL hs
                have hP : 0 < v0 + s := by linarith
                have he : 1 < Real.exp (L * (v0 + s)) := Real.one_lt_exp_iff.mpr (by positivity)
                have he1 : 0 < Real.exp (L * (v0 + s)) - 1 := by linarith
                rw [Real.exp_neg]
                have hden : s + (v0 + s) / (Real.exp (L * (v0 + s)) - 1) + v0
                    = (v0 + s) * Real.exp (L * (v0 + s)) / (Real.exp (L * (v0 + s)) - 1) := by
                  rw [eq_div_iff he1.ne', add_mul, add_mul, div_mul_cancel₀ _ he1.ne']; ring
                rw [hden]
                have : 0 < Real.exp (L * (v0 + s)) := Real.exp_pos _
                field_simp
                ring
              have hmono : ∀ L1 L2 P1 P2 : ℝ, 0 < L1 → L1 ≤ L2 → 0 < P1 → P1 ≤ P2 →
                  P2 / (Real.exp (L2 * P2) - 1) ≤ P1 / (Real.exp (L1 * P1) - 1) := by
                intro L1 L2 P1 P2 hL1 hL hP1 hP
                have ha : 0 < L1 * P1 := mul_pos hL1 hP1
                have hab : L1 * P1 ≤ L2 * P2 := mul_le_mul hL hP hP1.le (by linarith)
                have hb' : 0 < L2 * P2 := by linarith
                have hsec := convexOn_exp.secant_mono (a := 0) (x := L1 * P1) (y := L2 * P2)
                  (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _) ha.ne' hb'.ne' hab
                simp only [Real.exp_zero, sub_zero] at hsec
                have hea : 0 < Real.exp (L1 * P1) - 1 := by
                  have := Real.one_lt_exp_iff.mpr ha; linarith
                have heb : 0 < Real.exp (L2 * P2) - 1 := by
                  have := Real.one_lt_exp_iff.mpr hb'; linarith
                rw [div_le_div_iff₀ ha hb'] at hsec
                rw [div_le_div_iff₀ heb hea]
                -- hsec : (e^a - 1) * (L2 P2) ≤ (e^b - 1) * (L1 P1)
                have h1 : (Real.exp (L1 * P1) - 1) * P2 * L2 ≤ (Real.exp (L2 * P2) - 1) * P1 * L2 := by
                  have : (Real.exp (L2 * P2) - 1) * (L1 * P1) ≤ (Real.exp (L2 * P2) - 1) * (L2 * P1) :=
                    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL hP1.le) heb.le
                  nlinarith
                have hL2 : 0 < L2 := by linarith
                have := le_of_mul_le_mul_right h1 hL2
                linarith
              have hP : ∀ y, 0 < v0 + S y := fun y => by linarith [hS0 y]
              refine ⟨?_, ?_⟩
              · exact generic (fun y i => AssortSearch.HeurEq.demand lam v v0 y i)
                  (fun y => (v0 + S y) / (Real.exp (lam * (v0 + S y)) - 1))
                  (fun y _ i => key lam (S y) (v i) hlam (hS0 y))
                  (fun y _ => by
                    have := Real.one_lt_exp_iff.mpr (mul_pos hlam (hP y))
                    exact div_nonneg (hP y).le (by linarith))
                  (fun y z hyz _ => hmono lam lam _ _ hlam le_rfl (hP y) (by linarith [hSmono y z hyz]))
              · set w1 : ℝ → ℝ := fun z => 1 / μ * AssortSearch.Cannibal.lam μ z *
                    Real.exp (-(AssortSearch.Cannibal.lam μ z)) with hw1def
                set Φ1 : ℝ → ℝ := fun t => ∫ z in Set.Ioi t, (z - t) * w1 z with hΦ1def
                have hw : ∀ T : Finset (Fin n), 0 < AssortSearch.FullAssort.outsidePref v T → ∀ y,
                    AssortSearch.FullAssort.w μ v T y =
                      w1 (y - μ * Real.log (AssortSearch.FullAssort.outsidePref v T)) := by
                  intro T hV y
                  have e : AssortSearch.Cannibal.lam μ (y - μ * Real.log (AssortSearch.FullAssort.outsidePref v T))
                      = AssortSearch.Cannibal.lam μ y * AssortSearch.FullAssort.outsidePref v T := by
                    unfold AssortSearch.Cannibal.lam
                    rw [show -((y - μ * Real.log (AssortSearch.FullAssort.outsidePref v T)) / μ +
                          Real.eulerMascheroniConstant) = -(y / μ + Real.eulerMascheroniConstant) +
                          Real.log (AssortSearch.FullAssort.outsidePref v T) by field_simp; ring,
                      Real.exp_add, Real.exp_log hV]
                  simp only [hw1def]
                  rw [e]
                  unfold AssortSearch.FullAssort.w AssortSearch.FullAssort.outsideCdf
                  ring
                have hΦ : ∀ T : Finset (Fin n), 0 < AssortSearch.FullAssort.outsidePref v T → ∀ u,
                    AssortSearch.FullAssort.searchGain μ v T u =
                      Φ1 (u - μ * Real.log (AssortSearch.FullAssort.outsidePref v T)) := by
                  intro T hV u
                  set c := μ * Real.log (AssortSearch.FullAssort.outsidePref v T)
                  unfold AssortSearch.FullAssort.searchGain
                  simp only [hΦ1def]
                  simp_rw [hw T hV]
                  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
                  conv_rhs => rw [← integral_sub_right_eq_self _ c]
                  congr 1
                  funext y
                  by_cases h : u < y
                  · have h' : u - c < y - c := by linarith
                    simp [Set.indicator, h, h'] <;> exact Or.inl rfl
                  · have h' : ¬ (u - c < y - c) := by intro hh; exact h (by linarith)
                    simp [Set.indicator, h, h']
                have hsInf : ∀ c1 c2 : ℝ, c1 ≤ c2 →
                    sInf {u | Φ1 (u - c1) ≤ b} ≤ sInf {u | Φ1 (u - c2) ≤ b} := by
                  intro c1 c2 hc
                  by_cases hgood : ({t | Φ1 t ≤ b}).Nonempty ∧ BddBelow {t | Φ1 t ≤ b}
                  · obtain ⟨⟨t, ht⟩, ⟨m, hm⟩⟩ := hgood
                    have hbdd : BddBelow {u | Φ1 (u - c1) ≤ b} := by
                      refine ⟨m + c1, fun u hu => ?_⟩
                      have := hm (show u - c1 ∈ {t | Φ1 t ≤ b} from hu)
                      linarith
                    apply le_csInf
                    · exact ⟨t + c2, by simpa using ht⟩
                    · intro u hu
                      have hmem : u - c2 + c1 ∈ {u | Φ1 (u - c1) ≤ b} := by
                        simpa using hu
                      have := csInf_le hbdd hmem
                      linarith
                  · have hzero : ∀ c : ℝ, sInf {u | Φ1 (u - c) ≤ b} = 0 := by
                      intro c
                      by_cases hne : ({t | Φ1 t ≤ b}).Nonempty
                      · have hnb : ¬ BddBelow {t | Φ1 t ≤ b} := fun h => hgood ⟨hne, h⟩
                        apply Real.sInf_of_not_bddBelow
                        rintro ⟨m, hm⟩
                        apply hnb
                        refine ⟨m - c, fun t ht => ?_⟩
                        have := hm (show t + c ∈ {u | Φ1 (u - c) ≤ b} by simpa using ht)
                        linarith
                      · have : {u | Φ1 (u - c) ≤ b} = ∅ := by
                          ext u
                          simp only [Set.mem_empty_iff_false, iff_false]
                          intro hu
                          exact hne ⟨u - c, hu⟩
                        rw [this, Real.sInf_empty]
                    rw [hzero, hzero]
                have hVpos : ∀ z, z < n → 0 < AssortSearch.FullAssort.outsidePref v (popularSet n z) := by
                  intro z hz
                  unfold AssortSearch.FullAssort.outsidePref
                  apply Finset.sum_pos' (fun i _ => (hv i).le)
                  refine ⟨⟨z, hz⟩, ?_, hv _⟩
                  simp [popularSet]
                have hVmono : ∀ y z, y ≤ z → AssortSearch.FullAssort.outsidePref v (popularSet n z) ≤
                    AssortSearch.FullAssort.outsidePref v (popularSet n y) := by
                  intro y z hyz
                  unfold AssortSearch.FullAssort.outsidePref
                  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.compl_subset_compl.mpr (hsub y z hyz))
                    (fun j _ _ => (hv j).le)
                have hU : ∀ y z, y ≤ z → z < n →
                    AssortSearch.FullAssort.Ubar μ v (popularSet n z) b ≤
                      AssortSearch.FullAssort.Ubar μ v (popularSet n y) b := by
                  intro y z hyz hz
                  have hVz := hVpos z hz
                  have hVy := hVpos y (by omega)
                  unfold AssortSearch.FullAssort.Ubar
                  simp_rw [hΦ _ hVz, hΦ _ hVy]
                  apply hsInf
                  exact mul_le_mul_of_nonneg_left (Real.log_le_log hVz (hVmono y z hyz)) hμ.le
                set Λ : ℕ → ℝ := fun y => AssortSearch.Cannibal.lam μ
                  (AssortSearch.FullAssort.Ubar μ v (popularSet n y) b) with hΛdef
                have hΛpos : ∀ y, 0 < Λ y := fun y => Real.exp_pos _
                have hΛmono : ∀ y z, y ≤ z → z < n → Λ y ≤ Λ z := by
                  intro y z hyz hz
                  simp only [hΛdef, AssortSearch.Cannibal.lam]
                  apply Real.exp_le_exp.mpr
                  have := div_le_div_of_nonneg_right (hU y z hyz hz) hμ.le
                  linarith
                have hpopuniv : ∀ y, y ≤ n → (popularSet n y = Finset.univ ↔ y = n) := by
                  intro y hy
                  constructor
                  · intro h
                    by_contra hne
                    have hlt : y < n := lt_of_le_of_ne hy hne
                    have : (⟨y, hlt⟩ : Fin n) ∈ popularSet n y := by rw [h]; exact Finset.mem_univ _
                    simp [popularSet] at this
                  · rintro rfl
                    ext j
                    simp [popularSet]
                exact generic (fun y i => demandOv μ b v v0 y i)
                  (fun y => if y < n then (v0 + S y) / (Real.exp (Λ y * (v0 + S y)) - 1) else 0)
                  (fun y hy i => by
                    show AssortSearch.FullAssort.demandSO μ v v0 b (popularSet n y) i = _
                    unfold AssortSearch.FullAssort.demandSO
                    by_cases hyn : y < n
                    · have hne : popularSet n y ≠ Finset.univ := fun h => by
                        have := (hpopuniv y hy).mp h; omega
                      rw [if_neg hne, if_pos hyn]
                      exact key (Λ y) (S y) (v i) (hΛpos y) (hS0 y)
                    · have hyn' : y = n := by omega
                      rw [if_pos ((hpopuniv y hy).mpr hyn'), if_neg hyn]
                      unfold share
                      simp [S])
                  (fun y _ => by
                    split_ifs
                    · have := Real.one_lt_exp_iff.mpr (mul_pos (hΛpos y) (hP y))
                      exact div_nonneg (hP y).le (by linarith)
                    · exact le_rfl)
                  (fun y z hyz hzn => by
                    by_cases hz : z < n
                    · rw [if_pos hz, if_pos (by omega)]
                      exact hmono _ _ _ _ (hΛpos y) (hΛmono y z hyz hz) (hP y) (by linarith [hSmono y z hyz])
                    · rw [if_neg hz]
                      split_ifs
                      · have := Real.one_lt_exp_iff.mpr (mul_pos (hΛpos y) (hP y))
                        exact div_nonneg (hP y).le (by linarith)
                      · exact le_rfl)
