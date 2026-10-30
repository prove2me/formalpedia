-- Prove2me | solution 1 for AggDiscountStopping.OneBarrier.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T19:09:09.917064+00:00
-- url     : https://prove2.me/submissions/fb9125a3-040a-4241-a9b2-1594444fbf21

import Mathlib
import Definitions.Def_AggDiscountStopping_OneBarrier_Setting

open MeasureTheory Set Filter Topology
open scoped NNReal
open AggDiscountStopping.OneBarrier

/-- The Riccati equation (4.3) for `m̃ = −ψ′/ψ`. -/
lemma ads_riccati (M : Model) (hM : M.Valid) (r : ℝ) (ψ : ℝ → ℝ)
    (hψ : IsDecreasingSolution M r ψ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (mtilde ψ)
      (mtilde ψ x ^ 2 - 2 * (M.μ x / M.σ x ^ 2) * mtilde ψ x - 2 * r / M.σ x ^ 2) x := by
  have hs := hM.σ_sq_pos x hx
  have hpos := hψ.pos x hx
  have hnhds : Ioi (0:ℝ) ∈ 𝓝 x := isOpen_Ioi.mem_nhds hx
  have h1 : HasDerivAt ψ (deriv ψ x) x :=
    (((hψ.smooth.differentiableOn (by norm_num)) x hx).differentiableAt hnhds).hasDerivAt
  have h2 : HasDerivAt (deriv ψ) (deriv (deriv ψ) x) x :=
    ((((hψ.smooth.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)).differentiableOn
      (by norm_num)) x hx).differentiableAt hnhds).hasDerivAt
  have h3 := h2.neg.div h1 hpos.ne'
  have hode := hψ.ode x hx
  have h4 : HasDerivAt (mtilde ψ)
      ((-deriv (deriv ψ) x * ψ x - -deriv ψ x * deriv ψ x) / ψ x ^ 2) x := h3
  convert h4 using 1
  have hσ : M.σ x ≠ 0 := by
    intro h; rw [h] at hs; simp at hs
  have hpp : deriv (deriv ψ) x = 2 * (r * ψ x - M.μ x * deriv ψ x) / M.σ x ^ 2 := by
    rw [eq_div_iff hs.ne']
    linarith
  rw [hpp]
  unfold mtilde
  field_simp
  ring

theorem solution (M : Model) (hM : M.Valid) (hCi : M.CondI) (hCii1 : M.CondII1)
    (r : ℝ) (hr : 0 ≤ r) (ψ : ℝ → ℝ) (hψ : IsDecreasingSolution M r ψ) :
    ∀ x, 0 < x → mtilde ψ x < M.phi1 r x := by
  obtain ⟨hd1, C, x₀, hC⟩ := hCii1
  set m := mtilde ψ with hm_def
  set p := M.phi1 r with hp_def
  set S : ℝ → ℝ := fun x => Real.sqrt (M.μ x ^ 2 + 2 * r * M.σ x ^ 2) with hS_def
  set m' : ℝ → ℝ := fun x =>
    m x ^ 2 - 2 * (M.μ x / M.σ x ^ 2) * m x - 2 * r / M.σ x ^ 2 with hm'_def
  have hmd : ∀ x, 0 < x → HasDerivAt m (m' x) x := fun x hx => ads_riccati M hM r ψ hψ x hx
  have hmc : ContinuousOn m (Ioi 0) := fun x hx => (hmd x hx).continuousAt.continuousWithinAt
  have hpdiff : ∀ x, 0 < x → DifferentiableAt ℝ p x := fun x hx =>
    differentiableAt_of_deriv_ne_zero (hd1 r hr x hx).ne
  have hpd : ∀ x, 0 < x → HasDerivAt p (deriv p x) x := fun x hx => (hpdiff x hx).hasDerivAt
  have hpc : ContinuousOn p (Ioi 0) := fun x hx => (hpdiff x hx).continuousAt.continuousWithinAt
  have hpanti : StrictAntiOn p (Ioi 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioi 0) hpc
    intro x hx
    rw [interior_Ioi] at hx
    exact hd1 r hr x hx
  have hSsq : ∀ x, S x ^ 2 = M.μ x ^ 2 + 2 * r * M.σ x ^ 2 := by
    intro x
    simp only [hS_def]
    rw [Real.sq_sqrt (by positivity)]
  have hSnn : ∀ x, 0 ≤ S x := fun x => Real.sqrt_nonneg _
  have hp_eq : ∀ x, p x = (M.μ x + S x) / M.σ x ^ 2 := fun x => rfl
  have hp_nn : ∀ x, 0 < x → 0 ≤ p x := by
    intro x hx
    rw [hp_eq]
    exact div_nonneg (add_nonneg (hCi x hx.le) (hSnn x)) (hM.σ_sq_pos x hx).le
  -- factorization m̃′ = (m̃ − ϕ₁)(m̃ − ϕ₂)
  have hfac : ∀ x, 0 < x → m' x = (m x - p x) * (m x - p x + 2 * S x / M.σ x ^ 2) := by
    intro x hx
    have hs := (hM.σ_sq_pos x hx).ne'
    have hσ : M.σ x ≠ 0 := by
      intro h; rw [h] at hs; simp at hs
    have e : m' x = m x ^ 2 - 2 * (M.μ x / M.σ x ^ 2) * m x - 2 * r / M.σ x ^ 2 := rfl
    rw [e, hp_eq]
    rw [show (m x - (M.μ x + S x) / M.σ x ^ 2) *
        (m x - (M.μ x + S x) / M.σ x ^ 2 + 2 * S x / M.σ x ^ 2) =
        m x ^ 2 - 2 * (M.μ x / M.σ x ^ 2) * m x + (M.μ x ^ 2 - S x ^ 2) / (M.σ x ^ 2) ^ 2 by
      field_simp; ring]
    rw [hSsq x]
    field_simp
    ring
  have hpos_of : ∀ x, 0 < x → 0 < m x - p x → 0 < m' x := by
    intro x hx hq
    rw [hfac x hx]
    apply mul_pos hq
    have : 0 ≤ 2 * S x / M.σ x ^ 2 := div_nonneg (by linarith [hSnn x]) (hM.σ_sq_pos x hx).le
    linarith
  -- m̃′ ≥ (m̃ − ϕ₁) m̃
  have hlow : ∀ x, 0 < x → 0 ≤ m x - p x → (m x - p x) * m x ≤ m' x := by
    intro x hx hq
    rw [hfac x hx]
    apply mul_le_mul_of_nonneg_left _ hq
    have hμS : M.μ x ≤ S x := by
      have := Real.abs_le_sqrt (show M.μ x ^ 2 ≤ M.μ x ^ 2 + 2 * r * M.σ x ^ 2 by
        have := hM.σ_sq_pos x hx; nlinarith)
      exact le_trans (le_abs_self _) this
    have : m x - p x + 2 * S x / M.σ x ^ 2 = m x + (S x - M.μ x) / M.σ x ^ 2 := by
      rw [hp_eq]; field_simp; ring
    rw [this]
    have : 0 ≤ (S x - M.μ x) / M.σ x ^ 2 :=
      div_nonneg (by linarith) (hM.σ_sq_pos x hx).le
    linarith
  intro x hx
  by_contra hcon
  push Not at hcon
  -- Step A: a point where m̃ > ϕ₁ strictly
  obtain ⟨x1, hx1, hq1⟩ : ∃ x1, 0 < x1 ∧ 0 < m x1 - p x1 := by
    rcases lt_or_eq_of_le hcon with hlt | heq
    · exact ⟨x, hx, by linarith⟩
    · have hq0 : m x - p x = 0 := by rw [heq]; ring
      have hm'0 : m' x = 0 := by rw [hfac x hx, hq0, zero_mul]
      have hqd : HasDerivAt (fun y => m y - p y) (m' x - deriv p x) x :=
        (hmd x hx).sub (hpd x hx)
      have hpos' : 0 < m' x - deriv p x := by rw [hm'0]; linarith [hd1 r hr x hx]
      have hqdw := hqd.hasDerivWithinAt (s := Ici x)
      rw [hasDerivWithinAt_iff_tendsto_slope] at hqdw
      have hset : Ici x \ {x} = Ioi x := by
        ext y
        simp only [Set.mem_sdiff, mem_Ici, mem_singleton_iff, mem_Ioi]
        constructor
        · rintro ⟨h1, h2⟩; exact lt_of_le_of_ne h1 (Ne.symm h2)
        · intro h; exact ⟨h.le, h.ne'⟩
      rw [hset] at hqdw
      have hev : ∀ᶠ y in 𝓝[>] x, 0 < slope (fun y => m y - p y) x y :=
        hqdw (lt_mem_nhds hpos')
      have hev2 : ∀ᶠ y in 𝓝[>] x, x < y := self_mem_nhdsWithin
      obtain ⟨y, hy1, hy2⟩ := (hev.and hev2).exists
      refine ⟨y, by linarith, ?_⟩
      rw [slope_def_field, hq0, sub_zero] at hy1
      have hyx : 0 < y - x := by linarith
      exact (div_pos_iff_of_pos_right hyx).mp hy1
  -- Step B: m̃ > ϕ₁ on [x1, ∞)
  have hqpos : ∀ y, x1 ≤ y → 0 < m y - p y := by
    by_contra hneg
    push Not at hneg
    set T := Ici x1 ∩ (fun y => m y - p y) ⁻¹' (Iic 0) with hT
    have hTne : T.Nonempty := by
      obtain ⟨y, hy, hy'⟩ := hneg
      exact ⟨y, hy, hy'⟩
    have hqc : ContinuousOn (fun y => m y - p y) (Ici x1) :=
      (hmc.sub hpc).mono (fun y hy => lt_of_lt_of_le hx1 hy)
    have hTcl : IsClosed T := hqc.preimage_isClosed_of_isClosed isClosed_Ici isClosed_Iic
    have hTbdd : BddBelow T := ⟨x1, fun y hy => hy.1⟩
    set x2 := sInf T
    have hx2T : x2 ∈ T := hTcl.csInf_mem hTne hTbdd
    have hx2ge : x1 ≤ x2 := hx2T.1
    have hqx2 : m x2 - p x2 ≤ 0 := hx2T.2
    have hx12 : x1 < x2 := by
      rcases eq_or_lt_of_le hx2ge with h | h
      · rw [← h] at hqx2; linarith
      · exact h
    have hbelow : ∀ y, x1 ≤ y → y < x2 → 0 < m y - p y := by
      intro y hy1 hy2
      by_contra hle
      push Not at hle
      have : x2 ≤ y := csInf_le hTbdd ⟨hy1, hle⟩
      linarith
    have hmono : MonotoneOn m (Icc x1 x2) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      · exact hmc.mono (fun y hy => lt_of_lt_of_le hx1 hy.1)
      · intro y hy
        rw [interior_Icc] at hy
        exact (hmd y (by linarith [hy.1])).differentiableAt.differentiableWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        rw [(hmd y (by linarith [hy.1])).deriv]
        exact (hpos_of y (by linarith [hy.1]) (hbelow y hy.1.le hy.2)).le
    have h1 : m x1 ≤ m x2 := hmono ⟨le_rfl, hx2ge⟩ ⟨hx2ge, le_rfl⟩ hx2ge
    have h2 : p x2 < p x1 := hpanti hx1 (lt_trans hx1 hx12) hx12
    linarith
  -- Step C: linear growth of m̃
  have hmonoI : MonotoneOn m (Ici x1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · exact hmc.mono (fun y hy => lt_of_lt_of_le hx1 hy)
    · intro y hy
      rw [interior_Ici] at hy
      exact (hmd y (by linarith [mem_Ioi.mp hy])).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have hy' : x1 < y := hy
      rw [(hmd y (by linarith)).deriv]
      exact (hpos_of y (by linarith) (hqpos y hy'.le)).le
  set c := m x1 - p x1 with hc
  have hm1pos : 0 < m x1 := by linarith [hp_nn x1 hx1]
  set d := c * m x1 with hd
  have hdpos : 0 < d := mul_pos hq1 hm1pos
  have hm'd : ∀ y, x1 < y → d ≤ m' y := by
    intro y hy
    have hy0 : 0 < y := by linarith
    have hmy : m x1 ≤ m y := hmonoI (mem_Ici.mpr le_rfl) (mem_Ici.mpr hy.le) hy.le
    have hpy : p y ≤ p x1 := (hpanti hx1 hy0 hy).le
    have hqy : c ≤ m y - p y := by rw [hc]; linarith
    have := hlow y hy0 (hqpos y hy.le).le
    calc d = c * m x1 := rfl
      _ ≤ (m y - p y) * m y := mul_le_mul hqy hmy hm1pos.le (by linarith)
      _ ≤ m' y := this
  have hlin : ∀ y, x1 ≤ y → m x1 + d * (y - x1) ≤ m y := by
    have hmono2 : MonotoneOn (fun y => m y - d * y) (Ici x1) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici _)
      · exact (hmc.mono (fun y hy => lt_of_lt_of_le hx1 hy)).sub
          (continuousOn_const.mul continuousOn_id)
      · intro y hy
        rw [interior_Ici] at hy
        have hy' : x1 < y := hy
        exact ((hmd y (by linarith)).differentiableAt.sub
          ((differentiableAt_id).const_mul d)).differentiableWithinAt
      · intro y hy
        rw [interior_Ici] at hy
        have hy' : x1 < y := hy
        have hder : HasDerivAt (fun y => m y - d * y) (m' y - d * 1) y :=
          (hmd y (by linarith)).sub ((hasDerivAt_id y).const_mul d)
        rw [hder.deriv]
        linarith [hm'd y hy']
    intro y hy
    have := hmono2 (mem_Ici.mpr le_rfl) (mem_Ici.mpr hy) hy
    simp only at this
    linarith
  -- Step D: blow-up contradiction via w = 1/m̃
  set xb := max x₀ 1 with hxb
  have hCnn : 0 ≤ C := by
    have h := hC xb (le_max_left _ _)
    have hpos : 0 < xb := lt_of_lt_of_le one_pos (le_max_right _ _)
    have : 0 < (M.μ xb + 1) / M.σ xb ^ 2 :=
      div_pos (by linarith [hCi xb hpos.le]) (hM.σ_sq_pos xb hpos)
    linarith
  set M0 := 1 + 8 * C + 8 * r * C with hM0
  set x3 := max xb x1 + M0 / d with hx3
  have hM0pos : 0 < M0 := by positivity
  have hx3ge1 : x1 < x3 := by
    have : 0 < M0 / d := div_pos hM0pos hdpos
    have := le_max_right xb x1
    linarith
  have hx3gexb : xb ≤ x3 := by
    have : 0 < M0 / d := div_pos hM0pos hdpos
    have := le_max_left xb x1
    linarith
  have hxb1 : 1 ≤ xb := le_max_right _ _
  have hlarge : ∀ y, x3 ≤ y → M0 ≤ m y := by
    intro y hy
    have h1 := hlin y (by linarith)
    have : M0 ≤ d * (y - x1) := by
      have h2 : M0 / d ≤ y - x1 := by
        have := le_max_right xb x1
        linarith
      calc M0 = d * (M0 / d) := by field_simp
        _ ≤ d * (y - x1) := mul_le_mul_of_nonneg_left h2 hdpos.le
    linarith
  have hmpos : ∀ y, x3 ≤ y → 0 < m y := fun y hy => by linarith [hlarge y hy]
  set w : ℝ → ℝ := fun y => (m y)⁻¹ with hw
  have hwd : ∀ y, x3 ≤ y → HasDerivAt w (-(m' y) / (m y) ^ 2) y := by
    intro y hy
    have hy0 : 0 < y := by linarith
    exact (hmd y hy0).inv (hmpos y hy).ne'
  have hwbound : ∀ y, x3 ≤ y → -(m' y) / (m y) ^ 2 ≤ -1 / 2 := by
    intro y hy
    have hy0 : 0 < y := by linarith
    have hyx0 : x₀ ≤ y := le_trans (le_max_left _ _) (le_trans hx3gexb hy)
    have hsq := hM.σ_sq_pos y hy0
    have hCy := hC y hyx0
    have hμ := hCi y hy0.le
    set A := M.μ y / M.σ y ^ 2
    set B := 1 / M.σ y ^ 2
    have hA0 : 0 ≤ A := div_nonneg hμ hsq.le
    have hB0 : 0 ≤ B := div_nonneg zero_le_one hsq.le
    have hsum : (M.μ y + 1) / M.σ y ^ 2 = A + B := by
      simp only [A, B]; field_simp
    have hAB : A + B ≤ C := hsum ▸ hCy
    have hmy := hlarge y hy
    have hm'eq : m' y = m y ^ 2 - 2 * A * m y - 2 * r * B := by
      simp only [hm'_def, A, B]; ring
    have hmp := hmpos y hy
    rw [div_le_iff₀ (by positivity), hm'eq]
    have hAC : A ≤ C := by linarith
    have hBC : B ≤ C := by linarith
    have h1 : 8 * A ≤ m y := by nlinarith
    have h2 : 8 * r * B ≤ m y := by nlinarith
    have hrC : 0 ≤ r * C := mul_nonneg hr hCnn
    have hm1 : 1 ≤ m y := by linarith
    have h3 : 8 * A * m y ≤ m y * m y := mul_le_mul_of_nonneg_right h1 hmp.le
    have h4 : m y ≤ m y * m y := by nlinarith
    nlinarith
  have hanti : AntitoneOn (fun y => w y + y / 2) (Ici x3) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · intro y hy
      exact ((hwd y hy).continuousAt.add
        ((continuous_id.div_const 2).continuousAt)).continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      exact ((hwd y (le_of_lt hy)).differentiableAt.add
        ((differentiableAt_id).div_const 2)).differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have hder : HasDerivAt (fun y => w y + y / 2) (-(m' y) / (m y) ^ 2 + 1 / 2) y :=
        (hwd y (le_of_lt hy)).add ((hasDerivAt_id y).div_const 2)
      rw [hder.deriv]
      linarith [hwbound y (le_of_lt hy)]
  have hw3 : 0 < w x3 := inv_pos.mpr (hmpos x3 le_rfl)
  set X := x3 + 2 * w x3 + 2
  have hX : x3 ≤ X := by linarith
  have := hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr hX) hX
  simp only at this
  have hwX : 0 < w X := inv_pos.mpr (hmpos X hX)
  have : w X ≤ -1 := by
    simp only [X] at this ⊢
    linarith
  linarith
