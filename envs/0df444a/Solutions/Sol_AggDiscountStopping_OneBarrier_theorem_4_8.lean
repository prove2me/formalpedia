-- Prove2me | solution 1 for AggDiscountStopping.OneBarrier.theorem_4_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T19:00:15.27407+00:00
-- url     : https://prove2.me/submissions/880a423e-1bf2-4e06-b043-fe46e6b61b75

import Mathlib
import Definitions.Def_AggDiscountStopping_OneBarrier_Setting
import Theorems.Thm_AggDiscountStopping_OneBarrier_lemma_2_2
import Theorems.Thm_AggDiscountStopping_OneBarrier_eq_4_7
import Theorems.Thm_AggDiscountStopping_OneBarrier_eq_4_8_4_9
import Theorems.Thm_AggDiscountStopping_OneBarrier_eq_4_10

open MeasureTheory Set Filter Topology
open scoped NNReal
open AggDiscountStopping.OneBarrier

/-- A continuous path started strictly above `c ≥ 0` enters `[0, c]` exactly at `c`. -/
lemma ads_entry_point {Ω : Type*} [MeasurableSpace Ω] (D : Diffusion Ω) (hD : D.Valid)
    (c x : ℝ) (hc : 0 ≤ c) (hcx : c < x) (ω : Ω) (hen : D.enters x (Icc 0 c) ω) :
    D.X x (D.entryTime x (Icc 0 c) ω) ω = c := by
  set f : ℝ≥0 → ℝ := fun t => D.X x t ω with hf
  have hfc : Continuous f := hD.cont x ω
  have hf0 : f 0 = x := hD.start x ω
  set S : Set ℝ≥0 := {t : ℝ≥0 | 0 < t ∧ D.X x t ω ∈ Icc 0 c} with hS
  have hne : S.Nonempty := hen
  have hτ : D.entryTime x (Icc 0 c) ω = sInf S := rfl
  rw [hτ]
  have hcl : IsClosed {t : ℝ≥0 | f t ∈ Icc 0 c} := isClosed_Icc.preimage hfc
  have hmem : sInf S ∈ {t : ℝ≥0 | f t ∈ Icc 0 c} := by
    have h1 := csInf_mem_closure hne (OrderBot.bddBelow S)
    have h2 : closure S ⊆ {t : ℝ≥0 | f t ∈ Icc 0 c} :=
      closure_minimal (fun t ht => ht.2) hcl
    exact h2 h1
  have hle : f (sInf S) ≤ c := hmem.2
  refine le_antisymm hle ?_
  by_contra hlt
  push Not at hlt
  -- IVT on [0, τ]
  have hivt := intermediate_value_Icc' (zero_le : (0:ℝ≥0) ≤ sInf S) hfc.continuousOn
  have hcmem : c ∈ Icc (f (sInf S)) (f 0) := ⟨hlt.le, by rw [hf0]; exact hcx.le⟩
  obtain ⟨s, hs, hfs⟩ := hivt hcmem
  have hs0 : 0 < s := by
    rcases eq_or_lt_of_le hs.1 with h | h
    · subst h; rw [hf0] at hfs; linarith
    · exact h
  have hsS : s ∈ S := ⟨hs0, by show f s ∈ Icc 0 c; rw [hfs]; exact ⟨hc, le_rfl⟩⟩
  have := csInf_le (OrderBot.bddBelow S) hsS
  have hseq : s = sInf S := le_antisymm hs.2 this
  rw [← hseq] at hlt
  exact absurd hfs (ne_of_lt hlt)

/-- For a barrier `c ≥ K` and a start `x > c`, the aggregated payoff is `ϕ(0)`. -/
lemma ads_J_zero {Ω : Type*} [MeasurableSpace Ω] (M : Model) (hM : M.Valid) (D : Diffusion Ω)
    (hD : D.Valid) (c x : ℝ) (hc : M.K ≤ c) (hcx : c < x) :
    J M D x (Icc 0 c) = M.att 0 := by
  have hc0 : 0 ≤ c := le_trans hM.K_pos.le hc
  have hzero : ∀ r ω, discPayoff M D r x (Icc 0 c) ω = 0 := by
    intro r ω
    unfold discPayoff
    split_ifs with hen
    · rw [ads_entry_point D hD c x hc0 hcx ω hen]
      have : M.g c = 0 := by unfold Model.g; exact max_eq_right (by linarith)
      rw [this, mul_zero]
    · rfl
  have hF := hM.F_prob
  unfold J
  simp only [hzero, integral_zero]
  simp

theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : Model) (hM : M.Valid)
    (hCi : M.CondI) (hCii1 : M.CondII1) (ε : ℝ) (hε : 0 < ε) (hCii2 : M.CondII2 ε)
    (hCiii : M.CondIII) (D : Diffusion Ω) (hD : D.Valid) (φ : ℝ → ℝ → ℝ)
    (hφ : IsLaplaceRep M D φ)
    (hG : ∀ a, 0 < a → Integrable (fun r => deriv (φ r) a / φ r a) M.F) :
    ∃ aStar : ℝ, 0 ≤ aStar ∧ aStar < M.K ∧
      (∀ a, 0 < a → (IsEquilibrium M D (Icc 0 a) ↔ aStar ≤ a)) ∧
      (∀ a b, 0 < a → aStar ≤ a → a ≤ b → ∀ x, 0 ≤ x →
        Vval M D x (Icc 0 b) ≤ Vval M D x (Icc 0 a)) ∧
      (0 < aStar → IsOptimalOneBarrier M D aStar) := by
  obtain ⟨hmono, -, -, aStar, ha0, haK, hroot, hiff⟩ :=
    eq_4_8_4_9 M hM hCi hCii1 φ hφ.sol hG
  have h410 := eq_4_10 M hM hCi hCii1 ε hε hCii2 hCiii D hD φ hφ hG aStar ha0 haK hiff
  have hK := hM.K_pos
  -- points of the region are indifferent
  have hin : ∀ a x, 0 < a → 0 ≤ x → x ≤ a → J M D x (Icc 0 a) = M.att (M.g x) := fun a x ha hx hxa =>
    (lemma_2_2 M hM D hD φ hφ a ha x hx hxa).2
  have hgK : ∀ x, M.K ≤ x → M.g x = 0 := fun x hx => by
    unfold Model.g; exact max_eq_right (by linarith)
  -- characterization of one-barrier equilibria
  have heqchar : ∀ a, 0 < a →
      (IsEquilibrium M D (Icc 0 a) ↔ ∀ x, a < x → M.att (M.g x) ≤ J M D x (Icc 0 a)) := by
    intro a ha
    constructor
    · rintro ⟨-, hΘ⟩ x hax
      by_contra hlt
      push Not at hlt
      have hx : x ∈ Theta M D (Icc 0 a) := Or.inl ⟨by linarith, hlt⟩
      rw [hΘ] at hx
      exact absurd hx.2 (not_le.mpr hax)
    · intro hge
      refine ⟨measurableSet_Icc, ?_⟩
      ext x
      constructor
      · rintro (⟨hx0, hlt⟩ | ⟨-, hxR⟩)
        · by_contra hxR
          have hax : a < x := by
            by_contra h
            exact hxR ⟨hx0, not_lt.mp h⟩
          exact absurd (hge x hax) (not_le.mpr hlt)
        · exact hxR
      · intro hx
        exact Or.inr ⟨⟨hx.1, (hin a x ha hx.1 hx.2).symm⟩, hx⟩
  -- above an admissible barrier continuing is at least as good as stopping
  have hgood : ∀ a, 0 < a → aStar ≤ a → ∀ x, a < x → M.att (M.g x) ≤ J M D x (Icc 0 a) := by
    intro a ha haS x hax
    rcases le_or_gt M.K a with haK' | haK'
    · rw [ads_J_zero M hM D hD a x haK' hax, hgK x (by linarith)]
    · rcases le_or_gt x M.K with hxK | hxK
      · have := h410 a x x ha haS hax le_rfl hxK
        rw [hin x x (by linarith) (by linarith) le_rfl] at this
        exact this.le
      · have := h410 a M.K x ha haS haK' hxK.le le_rfl
        rw [ads_J_zero M hM D hD M.K x le_rfl hxK] at this
        rw [hgK x hxK.le]
        exact this.le
  -- the attitude function has positive derivative on (0, ∞)
  obtain ⟨hattc, hattd, hattsm, hattm⟩ := hCiii
  have hattdiff : ∀ y, 0 < y → DifferentiableAt ℝ M.att y := fun y hy =>
    ((hattd.differentiableOn one_ne_zero) y hy).differentiableAt (isOpen_Ioi.mem_nhds hy)
  have hderivpos : ∀ c, 0 < c → 0 < deriv M.att c := by
    intro c hc
    by_contra hle
    push Not at hle
    have hnp : ∀ y ∈ Ioo (c / 2) c, deriv M.att y ≤ 0 := by
      intro y hy
      have hy0 : 0 < y := by linarith [hy.1]
      have h1 : deriv M.att y * y ≤ deriv M.att c * c :=
        hattm (show y ∈ Ioi (0:ℝ) from hy0) (show c ∈ Ioi (0:ℝ) from hc) hy.2.le
      have h2 : deriv M.att c * c ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle hc.le
      by_contra hpos
      push Not at hpos
      have : 0 < deriv M.att y * y := mul_pos hpos hy0
      linarith
    have hanti : AntitoneOn M.att (Icc (c / 2) c) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      · exact hattc.mono (fun y hy => show (0:ℝ) ≤ y by linarith [hy.1])
      · intro y hy
        rw [interior_Icc] at hy
        exact (hattdiff y (by linarith [hy.1])).differentiableWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        exact hnp y hy
    have hlt := hattsm (show c / 2 ∈ Ici (0:ℝ) from by simp only [mem_Ici]; linarith)
      (show c ∈ Ici (0:ℝ) from hc.le) (by linarith : c / 2 < c)
    have hge := hanti (show c / 2 ∈ Icc (c / 2) c from ⟨le_rfl, by linarith⟩)
      (show c ∈ Icc (c / 2) c from ⟨by linarith, le_rfl⟩) (by linarith : c / 2 ≤ c)
    linarith
  -- below the threshold, points just above the barrier strictly prefer to stop
  have hbad : ∀ a, 0 < a → a < aStar → ∃ x, a < x ∧ J M D x (Icc 0 a) < M.att (M.g x) := by
    intro a ha haS
    have haK' : a < M.K := lt_trans haS haK
    have hS0 : 0 < aStar := lt_trans ha haS
    have hneg : G M φ a + 1 / (M.K - a) < 0 := by
      have h1 := hmono ⟨ha, haK'⟩ ⟨hS0, haK⟩ haS
      simp only at h1
      rw [hroot hS0] at h1
      exact h1
    have hJd := eq_4_7 M hM hCi hCii1 ε hε hCii2 ⟨hattc, hattd, hattsm, hattm⟩ D hD φ hφ hG a ha haK'
    have hKa : 0 < M.K - a := by linarith
    have hgd : HasDerivAt (fun x => M.g x) (-1) a := by
      have h1 : HasDerivAt (fun x => M.K - x) (-1) a := by
        simpa using (hasDerivAt_id a).const_sub M.K
      apply h1.congr_of_eventuallyEq
      have : ∀ᶠ x in 𝓝 a, x < M.K := eventually_lt_nhds haK'
      filter_upwards [this] with x hx
      unfold Model.g
      exact max_eq_left (by linarith)
    have hga : M.g a = M.K - a := by unfold Model.g; exact max_eq_left hKa.le
    have hattg : HasDerivAt (fun x => M.att (M.g x)) (deriv M.att (M.K - a) * (-1)) a := by
      have h2 : HasDerivAt M.att (deriv M.att (M.g a)) (M.g a) :=
        (hattdiff _ (by rw [hga]; exact hKa)).hasDerivAt
      have h3 := h2.comp a hgd
      rw [hga] at h3
      exact h3
    have hdiff := hJd.sub hattg.hasDerivWithinAt
    set d := deriv M.att (M.K - a) * (M.K - a) * G M φ a - deriv M.att (M.K - a) * (-1) with hd
    have hdneg : d < 0 := by
      have hdp := hderivpos (M.K - a) hKa
      have : d = deriv M.att (M.K - a) * (M.K - a) * (G M φ a + 1 / (M.K - a)) := by
        rw [hd]; field_simp; ring
      rw [this]
      exact mul_neg_of_pos_of_neg (mul_pos hdp hKa) hneg
    rw [hasDerivWithinAt_iff_tendsto_slope] at hdiff
    have hset : Ici a \ {a} = Ioi a := by
      ext y
      simp only [mem_diff, mem_Ici, mem_singleton_iff, mem_Ioi]
      constructor
      · rintro ⟨h1, h2⟩; exact lt_of_le_of_ne h1 (Ne.symm h2)
      · intro h; exact ⟨h.le, h.ne'⟩
    rw [hset] at hdiff
    have hev : ∀ᶠ x in 𝓝[>] a, slope (fun x => J M D x (Icc 0 a) - M.att (M.g x)) a x < 0 :=
      hdiff (gt_mem_nhds hdneg)
    have hev2 : ∀ᶠ x in 𝓝[>] a, a < x := self_mem_nhdsWithin
    obtain ⟨x, hx1, hx2⟩ := (hev.and hev2).exists
    refine ⟨x, hx2, ?_⟩
    rw [slope_def_field] at hx1
    have hza : J M D a (Icc 0 a) - M.att (M.g a) = 0 := by
      rw [hin a a ha ha.le le_rfl]; ring
    rw [hza, sub_zero] at hx1
    have hxa : 0 < x - a := by linarith
    have := (div_neg_iff.mp hx1)
    rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
    · linarith
    · linarith
  have hpart1 : ∀ a, 0 < a → (IsEquilibrium M D (Icc 0 a) ↔ aStar ≤ a) := by
    intro a ha
    rw [heqchar a ha]
    constructor
    · intro hge
      by_contra hlt
      push Not at hlt
      obtain ⟨x, hax, hx⟩ := hbad a ha hlt
      exact absurd (hge x hax) (not_le.mpr hx)
    · intro haS
      exact hgood a ha haS
  have hpart2 : ∀ a b, 0 < a → aStar ≤ a → a ≤ b → ∀ x, 0 ≤ x →
      Vval M D x (Icc 0 b) ≤ Vval M D x (Icc 0 a) := by
    intro a b ha haS hab x hx
    unfold Vval
    rcases eq_or_lt_of_le hab with h | hab'
    · rw [h]
    have hb : 0 < b := lt_of_lt_of_le ha hab
    rcases le_or_gt x b with hxb | hxb
    · rw [hin b x hb hx hxb, max_self]
      exact le_max_left _ _
    · rcases le_or_gt b M.K with hbK | hbK
      · have := h410 a b x ha haS hab' hxb.le hbK
        exact max_le_max le_rfl this.le
      · rw [ads_J_zero M hM D hD b x hbK.le hxb, hgK x (by linarith), max_self]
        exact le_max_left _ _
  refine ⟨aStar, ha0, haK, hpart1, hpart2, ?_⟩
  intro hS0
  refine ⟨(hpart1 aStar hS0).mpr le_rfl, ?_⟩
  intro b hb hbeq x hx
  exact hpart2 aStar b hS0 le_rfl ((hpart1 b hb).mp hbeq) x hx
