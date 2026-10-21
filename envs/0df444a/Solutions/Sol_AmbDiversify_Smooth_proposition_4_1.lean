-- Prove2me | solution 1 for AmbDiversify.Smooth.proposition_4_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:04:23.491026+00:00
-- url     : https://prove2.me/submissions/347954b4-d09c-4487-a7fc-96a555a6961a

import Mathlib
import Definitions.Def_AmbDiversify_Smooth_Model

set_option autoImplicit false
open AmbDiversify.Smooth

theorem ce_spec (φ : ℝ → ℝ) (hc : Continuous φ) (μ a b : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    φ (smoothCE φ μ a b) = μ * φ a + (1 - μ) * φ b := by
  have hex : ∃ c, φ c = μ * φ a + (1 - μ) * φ b := by
    have hmem : μ * φ a + (1 - μ) * φ b ∈ Set.uIcc (φ a) (φ b) := by
      rw [Set.mem_uIcc]
      rcases le_total (φ a) (φ b) with h | h
      · left; constructor <;> nlinarith
      · right; constructor <;> nlinarith
    obtain ⟨c, _, hc'⟩ := intermediate_value_uIcc (a := a) (b := b) hc.continuousOn hmem
    exact ⟨c, hc'⟩
  exact Function.invFun_eq hex

theorem aux_ge (D D' : ℝ → ℝ) (c : ℝ) (hD : ∀ x, HasDerivAt D (D' x) x)
    (h1 : ∀ x, x < c → D' x ≤ 0) (h2 : ∀ x, c < x → 0 ≤ D' x) (hc : D c = 0) :
    ∀ x, 0 ≤ D x := by
  intro x
  rcases lt_trichotomy x c with h | h | h
  · have hA : AntitoneOn D (Set.Iic c) :=
      antitoneOn_of_deriv_nonpos (convex_Iic c)
        (fun y _ => (hD y).continuousAt.continuousWithinAt)
        (fun y _ => (hD y).differentiableAt.differentiableWithinAt)
        (fun y hy => by
          rw [interior_Iic] at hy
          rw [(hD y).deriv]; exact h1 y hy)
    have := hA (Set.mem_Iic.2 h.le) (Set.mem_Iic.2 le_rfl) h.le
    linarith
  · rw [h, hc]
  · have hM : MonotoneOn D (Set.Ici c) :=
      monotoneOn_of_deriv_nonneg (convex_Ici c)
        (fun y _ => (hD y).continuousAt.continuousWithinAt)
        (fun y _ => (hD y).differentiableAt.differentiableWithinAt)
        (fun y hy => by
          rw [interior_Ici] at hy
          rw [(hD y).deriv]; exact h2 y hy)
    have := hM (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h.le) h.le
    linarith

theorem aux_gt (D D' : ℝ → ℝ) (c : ℝ) (hD : ∀ x, HasDerivAt D (D' x) x)
    (h1 : ∀ x, x < c → D' x < 0) (h2 : ∀ x, c < x → 0 < D' x) (hc : D c = 0) :
    ∀ x, x ≠ c → 0 < D x := by
  intro x hx
  rcases lt_or_gt_of_ne hx with h | h
  · have hA : StrictAntiOn D (Set.Iic c) :=
      strictAntiOn_of_deriv_neg (convex_Iic c)
        (fun y _ => (hD y).continuousAt.continuousWithinAt)
        (fun y hy => by
          rw [interior_Iic] at hy
          rw [(hD y).deriv]; exact h1 y hy)
    have := hA (Set.mem_Iic.2 h.le) (Set.mem_Iic.2 le_rfl) h
    linarith
  · have hM : StrictMonoOn D (Set.Ici c) :=
      strictMonoOn_of_deriv_pos (convex_Ici c)
        (fun y _ => (hD y).continuousAt.continuousWithinAt)
        (fun y hy => by
          rw [interior_Ici] at hy
          rw [(hD y).deriv]; exact h2 y hy)
    have := hM (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h.le) h
    linarith

theorem hasDerivL (φ : ℝ → ℝ) (hdd : Differentiable ℝ (deriv φ)) (pos : ∀ x, 0 < deriv φ x)
    (z x : ℝ) :
    HasDerivAt (fun x => Real.log (deriv φ (x + z)) - Real.log (deriv φ x))
      (absAmbAversion φ x - absAmbAversion φ (x + z)) x := by
  have h1 : HasDerivAt (fun x => Real.log (deriv φ (x + z)))
      (deriv (deriv φ) (x + z) / deriv φ (x + z)) x :=
    ((hdd (x + z)).hasDerivAt.comp_add_const x z).log (pos (x + z)).ne'
  have h2 : HasDerivAt (fun x => Real.log (deriv φ x))
      (deriv (deriv φ) x / deriv φ x) x :=
    (hdd x).hasDerivAt.log (pos x).ne'
  refine (h1.sub h2).congr_deriv ?_
  unfold absAmbAversion
  ring

theorem g_eq (φ : ℝ → ℝ) (pos : ∀ x, 0 < deriv φ x) (z x : ℝ) :
    deriv φ (x + z) / deriv φ x
      = Real.exp (Real.log (deriv φ (x + z)) - Real.log (deriv φ x)) := by
  rw [Real.exp_sub, Real.exp_log (pos _), Real.exp_log (pos _)]

theorem g_anti (φ : ℝ → ℝ) (hdd : Differentiable ℝ (deriv φ)) (pos : ∀ x, 0 < deriv φ x) (z : ℝ)
    (h : ∀ x, absAmbAversion φ x - absAmbAversion φ (x + z) ≤ 0) :
    Antitone (fun x => deriv φ (x + z) / deriv φ x) := by
  have hL : Antitone (fun x => Real.log (deriv φ (x + z)) - Real.log (deriv φ x)) :=
    antitone_of_deriv_nonpos (fun x => (hasDerivL φ hdd pos z x).differentiableAt)
      (fun x => by rw [(hasDerivL φ hdd pos z x).deriv]; exact h x)
  intro a b hab
  show deriv φ (b + z) / deriv φ b ≤ deriv φ (a + z) / deriv φ a
  rw [g_eq φ pos z b, g_eq φ pos z a]
  exact Real.exp_le_exp.2 (hL hab)

theorem g_mono (φ : ℝ → ℝ) (hdd : Differentiable ℝ (deriv φ)) (pos : ∀ x, 0 < deriv φ x) (z : ℝ)
    (h : ∀ x, 0 ≤ absAmbAversion φ x - absAmbAversion φ (x + z)) :
    Monotone (fun x => deriv φ (x + z) / deriv φ x) := by
  have hL : Monotone (fun x => Real.log (deriv φ (x + z)) - Real.log (deriv φ x)) :=
    monotone_of_deriv_nonneg (fun x => (hasDerivL φ hdd pos z x).differentiableAt)
      (fun x => by rw [(hasDerivL φ hdd pos z x).deriv]; exact h x)
  intro a b hab
  show deriv φ (a + z) / deriv φ a ≤ deriv φ (b + z) / deriv φ b
  rw [g_eq φ pos z b, g_eq φ pos z a]
  exact Real.exp_le_exp.2 (hL hab)

theorem g_smono (φ : ℝ → ℝ) (hdd : Differentiable ℝ (deriv φ)) (pos : ∀ x, 0 < deriv φ x) (z : ℝ)
    (h : ∀ x, 0 < absAmbAversion φ x - absAmbAversion φ (x + z)) :
    StrictMono (fun x => deriv φ (x + z) / deriv φ x) := by
  have hL : StrictMono (fun x => Real.log (deriv φ (x + z)) - Real.log (deriv φ x)) :=
    strictMono_of_deriv_pos (fun x => by rw [(hasDerivL φ hdd pos z x).deriv]; exact h x)
  intro a b hab
  show deriv φ (a + z) / deriv φ a < deriv φ (b + z) / deriv φ b
  rw [g_eq φ pos z b, g_eq φ pos z a]
  exact Real.exp_lt_exp.2 (hL hab)

theorem g_santi (φ : ℝ → ℝ) (hdd : Differentiable ℝ (deriv φ)) (pos : ∀ x, 0 < deriv φ x) (z : ℝ)
    (h : ∀ x, absAmbAversion φ x - absAmbAversion φ (x + z) < 0) :
    StrictAnti (fun x => deriv φ (x + z) / deriv φ x) := by
  have hL : StrictAnti (fun x => Real.log (deriv φ (x + z)) - Real.log (deriv φ x)) :=
    strictAnti_of_deriv_neg (fun x => by rw [(hasDerivL φ hdd pos z x).deriv]; exact h x)
  intro a b hab
  show deriv φ (b + z) / deriv φ b < deriv φ (a + z) / deriv φ a
  rw [g_eq φ pos z b, g_eq φ pos z a]
  exact Real.exp_lt_exp.2 (hL hab)

theorem hasDerivD (φ : ℝ → ℝ) (hd : Differentiable ℝ φ) (pos : ∀ x, 0 < deriv φ x) (z c x : ℝ) :
    HasDerivAt (fun x => φ (x + z) - φ (c + z) - (deriv φ (c + z) / deriv φ c) * (φ x - φ c))
      (deriv φ x * (deriv φ (x + z) / deriv φ x - deriv φ (c + z) / deriv φ c)) x := by
  have h1 : HasDerivAt (fun x => φ (x + z)) (deriv φ (x + z)) x :=
    (hd (x + z)).hasDerivAt.comp_add_const x z
  have h2 : HasDerivAt (fun x => (deriv φ (c + z) / deriv φ c) * (φ x - φ c))
      ((deriv φ (c + z) / deriv φ c) * deriv φ x) x :=
    ((hd x).hasDerivAt.sub_const (φ c)).const_mul _
  refine ((h1.sub_const (φ (c + z))).sub h2).congr_deriv ?_
  have := (pos x).ne'
  field_simp

/-- tangent inequalities; `g c = φ'(c+z)/φ'(c)` -/
theorem tang_ge (φ : ℝ → ℝ) (hd : Differentiable ℝ φ) (pos : ∀ x, 0 < deriv φ x) (z c : ℝ)
    (hg : Monotone (fun x => deriv φ (x + z) / deriv φ x)) (x : ℝ) :
    (deriv φ (c + z) / deriv φ c) * (φ x - φ c) ≤ φ (x + z) - φ (c + z) := by
  have := aux_ge (fun x => φ (x + z) - φ (c + z) - (deriv φ (c + z) / deriv φ c) * (φ x - φ c))
    (fun x => deriv φ x * (deriv φ (x + z) / deriv φ x - deriv φ (c + z) / deriv φ c)) c
    (hasDerivD φ hd pos z c)
    (fun y hy => mul_nonpos_of_nonneg_of_nonpos (pos y).le (sub_nonpos.2 (hg hy.le)))
    (fun y hy => mul_nonneg (pos y).le (sub_nonneg.2 (hg hy.le)))
    (by simp) x
  linarith

theorem tang_le (φ : ℝ → ℝ) (hd : Differentiable ℝ φ) (pos : ∀ x, 0 < deriv φ x) (z c : ℝ)
    (hg : Antitone (fun x => deriv φ (x + z) / deriv φ x)) (x : ℝ) :
    φ (x + z) - φ (c + z) ≤ (deriv φ (c + z) / deriv φ c) * (φ x - φ c) := by
  have := aux_ge (fun x => -(φ (x + z) - φ (c + z) - (deriv φ (c + z) / deriv φ c) * (φ x - φ c)))
    (fun x => -(deriv φ x * (deriv φ (x + z) / deriv φ x - deriv φ (c + z) / deriv φ c))) c
    (fun y => (hasDerivD φ hd pos z c y).neg)
    (fun y hy => by
      have := mul_nonneg (pos y).le (sub_nonneg.2 (hg hy.le))
      linarith)
    (fun y hy => by
      have := mul_nonpos_of_nonneg_of_nonpos (pos y).le (sub_nonpos.2 (hg hy.le))
      linarith)
    (by simp) x
  linarith

theorem tang_gt (φ : ℝ → ℝ) (hd : Differentiable ℝ φ) (pos : ∀ x, 0 < deriv φ x) (z c : ℝ)
    (hg : StrictMono (fun x => deriv φ (x + z) / deriv φ x)) (x : ℝ) (hx : x ≠ c) :
    (deriv φ (c + z) / deriv φ c) * (φ x - φ c) < φ (x + z) - φ (c + z) := by
  have := aux_gt (fun x => φ (x + z) - φ (c + z) - (deriv φ (c + z) / deriv φ c) * (φ x - φ c))
    (fun x => deriv φ x * (deriv φ (x + z) / deriv φ x - deriv φ (c + z) / deriv φ c)) c
    (hasDerivD φ hd pos z c)
    (fun y hy => mul_neg_of_pos_of_neg (pos y) (sub_neg.2 (hg hy)))
    (fun y hy => mul_pos (pos y) (sub_pos.2 (hg hy)))
    (by simp) x hx
  linarith

theorem tang_lt (φ : ℝ → ℝ) (hd : Differentiable ℝ φ) (pos : ∀ x, 0 < deriv φ x) (z c : ℝ)
    (hg : StrictAnti (fun x => deriv φ (x + z) / deriv φ x)) (x : ℝ) (hx : x ≠ c) :
    φ (x + z) - φ (c + z) < (deriv φ (c + z) / deriv φ c) * (φ x - φ c) := by
  have := aux_gt (fun x => -(φ (x + z) - φ (c + z) - (deriv φ (c + z) / deriv φ c) * (φ x - φ c)))
    (fun x => -(deriv φ x * (deriv φ (x + z) / deriv φ x - deriv φ (c + z) / deriv φ c))) c
    (fun y => (hasDerivD φ hd pos z c y).neg)
    (fun y hy => by
      have := mul_pos (pos y) (sub_pos.2 (hg hy))
      linarith)
    (fun y hy => by
      have := mul_neg_of_pos_of_neg (pos y) (sub_neg.2 (hg hy))
      linarith)
    (by simp) x hx
  linarith

theorem raise_le (φ : ℝ → ℝ) (hφ : IsAmbiguityFunction φ)
    (μ x1 x2 d : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hx : x1 ≤ x2) (hd : 0 ≤ d) :
    smoothCE φ μ x1 (x2 + d) ≤ smoothCE φ μ x1 x2 + (1 - μ) * d := by
  obtain ⟨h2, h1, hconc⟩ := hφ
  have hs : StrictMono φ := strictMono_of_deriv_pos h1
  have hcont : Continuous φ := h2.continuous
  have hc : φ (smoothCE φ μ x1 x2) = μ * φ x1 + (1 - μ) * φ x2 := ce_spec φ hcont μ _ _ hμ0 hμ1
  have hc' : φ (smoothCE φ μ x1 (x2 + d)) = μ * φ x1 + (1 - μ) * φ (x2 + d) :=
    ce_spec φ hcont μ _ _ hμ0 hμ1
  generalize smoothCE φ μ x1 x2 = c at hc ⊢
  generalize smoothCE φ μ x1 (x2 + d) = c' at hc' ⊢
  have hμ' : 0 ≤ 1 - μ := by linarith
  have hcx2 : c ≤ x2 := by
    apply hs.le_iff_le.1
    rw [hc]
    have := hs.monotone hx
    nlinarith
  -- increments of a concave function decrease
  have hinc : φ (x2 + d) + φ c ≤ φ (c + d) + φ x2 := by
    rcases eq_or_lt_of_le (show 0 ≤ x2 - c + d by linarith) with h0 | hpos
    · have hd0 : d = 0 := by linarith
      have hx0 : x2 = c := by linarith
      subst hd0; subst hx0; linarith
    · have hs0 : 0 ≤ d / (x2 - c + d) := div_nonneg hd hpos.le
      have hs1 : 0 ≤ 1 - d / (x2 - c + d) := by
        rw [sub_nonneg, div_le_one hpos]; linarith
      have e1 := @hconc.2 c (Set.mem_univ _) (x2 + d) (Set.mem_univ _)
        (1 - d / (x2 - c + d)) (d / (x2 - c + d)) hs1 hs0 (by ring)
      have e2 := @hconc.2 c (Set.mem_univ _) (x2 + d) (Set.mem_univ _)
        (d / (x2 - c + d)) (1 - d / (x2 - c + d)) hs0 hs1 (by ring)
      have q1 : (1 - d / (x2 - c + d)) • c + (d / (x2 - c + d)) • (x2 + d) = c + d := by
        simp only [smul_eq_mul]; field_simp; ring
      have q2 : (d / (x2 - c + d)) • c + (1 - d / (x2 - c + d)) • (x2 + d) = x2 := by
        simp only [smul_eq_mul]; field_simp; ring
      rw [q1] at e1
      rw [q2] at e2
      simp only [smul_eq_mul] at e1 e2
      linarith
  have hconc2 : (1 - μ) * φ (c + d) + μ * φ c ≤ φ (c + (1 - μ) * d) := by
    have := @hconc.2 c (Set.mem_univ _) (c + d) (Set.mem_univ _) μ (1 - μ) hμ0 hμ' (by ring)
    simp only [smul_eq_mul] at this
    have e : μ * c + (1 - μ) * (c + d) = c + (1 - μ) * d := by ring
    rw [e] at this
    linarith
  have hm := mul_le_mul_of_nonneg_left hinc hμ'
  have : φ c' ≤ φ (c + (1 - μ) * d) := by
    rw [hc']
    nlinarith
  have := hs.le_iff_le.1 this
  linarith

theorem ce_shift_le (φ : ℝ → ℝ) (hφ : IsAmbiguityFunction φ) (hcai : CAAA φ ∨ IAAA φ)
    (μ x1 x2 z : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hz : 0 ≤ z) :
    smoothCE φ μ (x1 + z) (x2 + z) ≤ smoothCE φ μ x1 x2 + z := by
  obtain ⟨h2, h1, _⟩ := hφ
  have hd : Differentiable ℝ φ := h2.differentiable (by norm_num)
  have hdd : Differentiable ℝ (deriv φ) := h2.differentiable_deriv_two
  have hs : StrictMono φ := strictMono_of_deriv_pos h1
  have hcont : Continuous φ := h2.continuous
  have hμ2 : 0 ≤ 1 - μ := by linarith
  have hc : φ (smoothCE φ μ x1 x2) = μ * φ x1 + (1 - μ) * φ x2 :=
    ce_spec φ hcont μ _ _ hμ0 hμ1
  have hc' : φ (smoothCE φ μ (x1 + z) (x2 + z)) = μ * φ (x1 + z) + (1 - μ) * φ (x2 + z) :=
    ce_spec φ hcont μ _ _ hμ0 hμ1
  generalize smoothCE φ μ x1 x2 = c at hc ⊢
  generalize smoothCE φ μ (x1 + z) (x2 + z) = c' at hc' ⊢
  have hg : Antitone (fun x => deriv φ (x + z) / deriv φ x) :=
    g_anti φ hdd h1 z (fun x => by
      rcases hcai with hC | hI
      · exact sub_nonpos.2 (hC x (x + z)).le
      · exact sub_nonpos.2 (hI.monotone (by linarith : x ≤ x + z)))
  have e1 := tang_le φ hd h1 z c hg x1
  have e2 := tang_le φ hd h1 z c hg x2
  have hcomb : μ * (φ (x1 + z) - φ (c + z) - (deriv φ (c + z) / deriv φ c) * (φ x1 - φ c)) +
      (1 - μ) * (φ (x2 + z) - φ (c + z) - (deriv φ (c + z) / deriv φ c) * (φ x2 - φ c))
      = φ c' - φ (c + z) := by
    linear_combination hc'.symm - (deriv φ (c + z) / deriv φ c) * hc.symm
  generalize deriv φ (c + z) / deriv φ c = k at e1 e2 hcomb
  have p1 : μ * (φ (x1 + z) - φ (c + z) - k * (φ x1 - φ c)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hμ0 (by linarith)
  have p2 : (1 - μ) * (φ (x2 + z) - φ (c + z) - k * (φ x2 - φ c)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hμ2 (by linarith)
  have : φ c' ≤ φ (c + z) := by linarith
  have := hs.le_iff_le.1 this
  linarith

theorem ce_swap (φ : ℝ → ℝ) (μ a b : ℝ) : smoothCE φ μ a b = smoothCE φ (1 - μ) b a := by
  unfold smoothCE
  congr 1
  ring

theorem key (φ : ℝ → ℝ) (hφ : IsAmbiguityFunction φ) (hcai : CAAA φ ∨ IAAA φ)
    (μ A1 A2 D1 D2 : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hA : A1 ≤ A2) (h0 : 0 ≤ D1) (hD : D1 ≤ D2) :
    smoothCE φ μ (A1 + D1) (A2 + D2) ≤ smoothCE φ μ A1 A2 + (μ * D1 + (1 - μ) * D2) := by
  have s1 := ce_shift_le φ hφ hcai μ A1 A2 D1 hμ0 hμ1 h0
  have s2 := raise_le φ hφ μ (A1 + D1) (A2 + D1) (D2 - D1) hμ0 hμ1 (by linarith) (by linarith)
  have e : A2 + D1 + (D2 - D1) = A2 + D2 := by ring
  rw [e] at s2
  linarith

theorem solution (u φ : ℝ → ℝ) (W0 L μ p1 p2 : ℝ)
    (hL : 0 < L) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hp1_0 : 0 ≤ p1) (hp1_1 : p1 ≤ 1) (hp2_0 : 0 ≤ p2) (hp2_1 : p2 ≤ 1)
    (hu_mono : Monotone u) (hu_conc : ConcaveOn ℝ Set.univ u)
    (hφ : IsAmbiguityFunction φ)
    (hcase : (IAAA φ ∧ p1 = 1 - p2) ∨ ((CAAA φ ∨ IAAA φ) ∧ 1 / 2 ≤ p1 ∧ 1 / 2 ≤ p2)) :
    VD_smt φ u W0 L μ p1 p2 ≤ VD_AN u W0 L μ p1 p2 := by
  have hG : 0 ≤ 2 * u (W0 - L / 2) - u (W0 - L) - u W0 := by
    have hmid : (W0 - L / 2) = (1 / 2 : ℝ) • (W0 - L) + (1 / 2 : ℝ) • W0 := by
      simp only [smul_eq_mul]; ring
    have := @hu_conc.2 (W0 - L) (Set.mem_univ _) W0 (Set.mem_univ _) (1 / 2) (1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
    rw [← hmid] at this
    simp only [smul_eq_mul] at this
    linarith
  have hvd : ∀ p, VD_risk u W0 L p = p * (1 - p) * (2 * u (W0 - L / 2) - u (W0 - L) - u W0) := by
    intro p; unfold VD_risk EU_D EU_ND; ring
  have hD : ∀ p, EU_D u W0 L p = EU_ND u W0 L p + VD_risk u W0 L p := by
    intro p; unfold VD_risk; ring
  have hAN : VD_AN u W0 L μ p1 p2 = μ * VD_risk u W0 L p1 + (1 - μ) * VD_risk u W0 L p2 := by
    unfold VD_AN EU_D_AN EU_ND_AN VD_risk; ring
  have hsm : VD_smt φ u W0 L μ p1 p2 =
      smoothCE φ μ (EU_ND u W0 L p1 + VD_risk u W0 L p1) (EU_ND u W0 L p2 + VD_risk u W0 L p2)
        - smoothCE φ μ (EU_ND u W0 L p1) (EU_ND u W0 L p2) := by
    unfold VD_smt EU_D_smt EU_ND_smt
    rw [hD p1, hD p2]
  rw [hAN, hsm]
  have hnd : ∀ p, EU_ND u W0 L p = u W0 - p * (u W0 - u (W0 - L)) := by
    intro p; unfold EU_ND; ring
  have hsub : 0 ≤ u W0 - u (W0 - L) := sub_nonneg.2 (hu_mono (by linarith))
  have hΔ0 : ∀ p, 0 ≤ p → p ≤ 1 → 0 ≤ VD_risk u W0 L p := fun p h0 h1 => by
    rw [hvd]; exact mul_nonneg (mul_nonneg h0 (by linarith)) hG
  rcases hcase with ⟨hI, h12⟩ | ⟨hcai, hh1, hh2⟩
  · have hΔeq : VD_risk u W0 L p2 = VD_risk u W0 L p1 := by
      rw [hvd, hvd, h12]; ring
    rw [hΔeq]
    have := ce_shift_le φ hφ (Or.inr hI) μ (EU_ND u W0 L p1) (EU_ND u W0 L p2)
      (VD_risk u W0 L p1) hμ0 hμ1 (hΔ0 p1 hp1_0 hp1_1)
    linarith
  · rcases le_total p2 p1 with h | h
    · have hA : EU_ND u W0 L p1 ≤ EU_ND u W0 L p2 := by
        rw [hnd, hnd]; nlinarith [mul_nonneg (sub_nonneg.2 h) hsub]
      have hΔ : VD_risk u W0 L p1 ≤ VD_risk u W0 L p2 := by
        rw [hvd, hvd]
        have h3 : 0 ≤ p1 + p2 - 1 := by linarith
        nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 h) h3) hG]
      have := key φ hφ hcai μ _ _ _ _ hμ0 hμ1 hA (hΔ0 p1 hp1_0 hp1_1) hΔ
      linarith
    · have hA : EU_ND u W0 L p2 ≤ EU_ND u W0 L p1 := by
        rw [hnd, hnd]; nlinarith [mul_nonneg (sub_nonneg.2 h) hsub]
      have hΔ : VD_risk u W0 L p2 ≤ VD_risk u W0 L p1 := by
        rw [hvd, hvd]
        have h3 : 0 ≤ p1 + p2 - 1 := by linarith
        nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 h) h3) hG]
      have := key φ hφ hcai (1 - μ) _ _ _ _ (by linarith) (by linarith) hA (hΔ0 p2 hp2_0 hp2_1) hΔ
      rw [ce_swap φ μ (EU_ND u W0 L p1 + VD_risk u W0 L p1) (EU_ND u W0 L p2 + VD_risk u W0 L p2),
        ce_swap φ μ (EU_ND u W0 L p1) (EU_ND u W0 L p2)]
      linarith
