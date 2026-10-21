-- Prove2me | solution 1 for AmbDiversify.Smooth.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:03:17.92243+00:00
-- url     : https://prove2.me/submissions/8dfb65e8-930b-4f90-a459-2d84ddac6e7d

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

theorem comb (φ : ℝ → ℝ) (μ x1 x2 z c c' k : ℝ)
    (hc : φ c = μ * φ x1 + (1 - μ) * φ x2)
    (hc' : φ c' = μ * φ (x1 + z) + (1 - μ) * φ (x2 + z)) :
    μ * (φ (x1 + z) - φ (c + z) - k * (φ x1 - φ c)) +
      (1 - μ) * (φ (x2 + z) - φ (c + z) - k * (φ x2 - φ c)) = φ c' - φ (c + z) := by
  linear_combination hc'.symm - k * hc.symm

theorem solution (φ : ℝ → ℝ) (hφ2 : ContDiff ℝ 2 φ) (hφ1 : ∀ x, 0 < deriv φ x)
    (μ x1 x2 z : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hx : x1 ≠ x2) (hz : 0 < z) :
    (DAAA φ → smoothCE φ μ x1 x2 + z < smoothCE φ μ (x1 + z) (x2 + z)) ∧
    (CAAA φ → smoothCE φ μ (x1 + z) (x2 + z) = smoothCE φ μ x1 x2 + z) ∧
    (IAAA φ → smoothCE φ μ (x1 + z) (x2 + z) < smoothCE φ μ x1 x2 + z) := by
  have hd : Differentiable ℝ φ := hφ2.differentiable (by norm_num)
  have hdd : Differentiable ℝ (deriv φ) := hφ2.differentiable_deriv_two
  have hs : StrictMono φ := strictMono_of_deriv_pos hφ1
  have hcont : Continuous φ := hφ2.continuous
  have hμ0' : 0 ≤ μ := hμ0.le
  have hμ1' : μ ≤ 1 := hμ1.le
  have hμ2 : 0 < 1 - μ := by linarith
  have hc : φ (smoothCE φ μ x1 x2) = μ * φ x1 + (1 - μ) * φ x2 :=
    ce_spec φ hcont μ _ _ hμ0' hμ1'
  have hc' : φ (smoothCE φ μ (x1 + z) (x2 + z)) = μ * φ (x1 + z) + (1 - μ) * φ (x2 + z) :=
    ce_spec φ hcont μ _ _ hμ0' hμ1'
  generalize smoothCE φ μ x1 x2 = c at hc ⊢
  generalize smoothCE φ μ (x1 + z) (x2 + z) = c' at hc' ⊢
  have hx' : ¬ (x1 = c ∧ x2 = c) := fun ⟨h1, h2⟩ => hx (h1.trans h2.symm)
  have hcomb := comb φ μ x1 x2 z c c' (deriv φ (c + z) / deriv φ c) hc hc'
  refine ⟨fun hD => ?_, fun hC => ?_, fun hI => ?_⟩
  · have hg : StrictMono (fun x => deriv φ (x + z) / deriv φ x) :=
      g_smono φ hdd hφ1 z (fun x => sub_pos.2 (hD (by linarith : x < x + z)))
    have e1 := tang_ge φ hd hφ1 z c hg.monotone x1
    have e2 := tang_ge φ hd hφ1 z c hg.monotone x2
    have key : φ (c + z) < φ c' := by
      by_cases h1 : x1 = c
      · have h2 : x2 ≠ c := fun h2 => hx' ⟨h1, h2⟩
        have f2 := tang_gt φ hd hφ1 z c hg x2 h2
        generalize deriv φ (c + z) / deriv φ c = k at e1 e2 f2 hcomb
        have p1 : 0 ≤ μ * (φ (x1 + z) - φ (c + z) - k * (φ x1 - φ c)) :=
          mul_nonneg hμ0' (by linarith)
        have p2 : 0 < (1 - μ) * (φ (x2 + z) - φ (c + z) - k * (φ x2 - φ c)) :=
          mul_pos hμ2 (by linarith)
        linarith
      · have f1 := tang_gt φ hd hφ1 z c hg x1 h1
        generalize deriv φ (c + z) / deriv φ c = k at e1 e2 f1 hcomb
        have p1 : 0 < μ * (φ (x1 + z) - φ (c + z) - k * (φ x1 - φ c)) :=
          mul_pos hμ0 (by linarith)
        have p2 : 0 ≤ (1 - μ) * (φ (x2 + z) - φ (c + z) - k * (φ x2 - φ c)) :=
          mul_nonneg hμ2.le (by linarith)
        linarith
    exact hs.lt_iff_lt.1 key
  · have hg1 : Monotone (fun x => deriv φ (x + z) / deriv φ x) :=
      g_mono φ hdd hφ1 z (fun x => sub_nonneg.2 (hC x (x + z)).ge)
    have hg2 : Antitone (fun x => deriv φ (x + z) / deriv φ x) :=
      g_anti φ hdd hφ1 z (fun x => sub_nonpos.2 (hC x (x + z)).le)
    have e1 := tang_ge φ hd hφ1 z c hg1 x1
    have e2 := tang_ge φ hd hφ1 z c hg1 x2
    have f1 := tang_le φ hd hφ1 z c hg2 x1
    have f2 := tang_le φ hd hφ1 z c hg2 x2
    generalize deriv φ (c + z) / deriv φ c = k at e1 e2 f1 f2 hcomb
    have a1 : φ (x1 + z) - φ (c + z) - k * (φ x1 - φ c) = 0 := by linarith
    have a2 : φ (x2 + z) - φ (c + z) - k * (φ x2 - φ c) = 0 := by linarith
    rw [a1, a2] at hcomb
    have : φ c' = φ (c + z) := by linarith
    exact hs.injective this
  · have hg : StrictAnti (fun x => deriv φ (x + z) / deriv φ x) :=
      g_santi φ hdd hφ1 z (fun x => sub_neg.2 (hI (by linarith : x < x + z)))
    have e1 := tang_le φ hd hφ1 z c hg.antitone x1
    have e2 := tang_le φ hd hφ1 z c hg.antitone x2
    have key : φ c' < φ (c + z) := by
      by_cases h1 : x1 = c
      · have h2 : x2 ≠ c := fun h2 => hx' ⟨h1, h2⟩
        have f2 := tang_lt φ hd hφ1 z c hg x2 h2
        generalize deriv φ (c + z) / deriv φ c = k at e1 e2 f2 hcomb
        have p1 : μ * (φ (x1 + z) - φ (c + z) - k * (φ x1 - φ c)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hμ0' (by linarith)
        have p2 : (1 - μ) * (φ (x2 + z) - φ (c + z) - k * (φ x2 - φ c)) < 0 :=
          mul_neg_of_pos_of_neg hμ2 (by linarith)
        linarith
      · have f1 := tang_lt φ hd hφ1 z c hg x1 h1
        generalize deriv φ (c + z) / deriv φ c = k at e1 e2 f1 hcomb
        have p1 : μ * (φ (x1 + z) - φ (c + z) - k * (φ x1 - φ c)) < 0 :=
          mul_neg_of_pos_of_neg hμ0 (by linarith)
        have p2 : (1 - μ) * (φ (x2 + z) - φ (c + z) - k * (φ x2 - φ c)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hμ2.le (by linarith)
        linarith
    exact hs.lt_iff_lt.1 key
