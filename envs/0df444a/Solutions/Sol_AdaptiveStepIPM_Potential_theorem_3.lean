-- Prove2me | solution 1 for AdaptiveStepIPM.Potential.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T14:40:22.437011+00:00
-- url     : https://prove2.me/submissions/945a115a-a85a-442f-b93f-a499170d116e

import Mathlib
import Definitions.Def_LinearOptimization_InteriorPointPotential
import Definitions.Def_AdaptiveStepIPM_Potential_Algorithm3

set_option autoImplicit false

open Matrix

namespace P46cc

open AdaptiveStepIPM.Potential

lemma seg_pos {a d b e θ : ℝ} (ha : 0 < a) (hb : 0 < b) (hθ : 0 ≤ θ)
    (h : ∀ τ : ℝ, 0 ≤ τ → τ ≤ θ → 0 < (a + τ * d) * (b + τ * e)) :
    0 < a + θ * d ∧ 0 < b + θ * e := by
  constructor
  · by_contra hc
    push Not at hc
    have hd : d < 0 := by
      by_contra hd; push Not at hd; nlinarith
    have h0 : a + (-a / d) * d = 0 := by rw [div_mul_cancel₀ _ hd.ne]; ring
    have := h (-a / d) (div_nonneg_of_nonpos (by linarith) hd.le)
      ((div_le_iff_of_neg hd).2 (by linarith))
    rw [h0, zero_mul] at this
    exact lt_irrefl _ this
  · by_contra hc
    push Not at hc
    have he : e < 0 := by
      by_contra he; push Not at he; nlinarith
    have h0 : b + (-b / e) * e = 0 := by rw [div_mul_cancel₀ _ he.ne]; ring
    have := h (-b / e) (div_nonneg_of_nonpos (by linarith) he.le)
      ((div_le_iff_of_neg he).2 (by linarith))
    rw [h0, mul_zero] at this
    exact lt_irrefl _ this

lemma dot_dir_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (dx : Fin n → ℝ)
    (dy : Fin m → ℝ) (ds : Fin n → ℝ)
    (h1 : A *ᵥ dx = 0) (h2 : Aᵀ *ᵥ dy + ds = 0) : ∑ j, dx j * ds j = 0 := by
  have hds : ds = -(Aᵀ *ᵥ dy) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact h2
  have : dx ⬝ᵥ ds = 0 := by
    rw [hds, dotProduct_neg, dotProduct_mulVec, vecMul_transpose, h1, zero_dotProduct,
      neg_zero]
  simpa [dotProduct] using this

lemma line_dot {m n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (γ : ℝ)
    (x s dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ)
    (hd : IsNewtonDirection A γ x s dx dy ds) (θ : ℝ) :
    lineStep x dx θ ⬝ᵥ lineStep s ds θ = (x ⬝ᵥ s) * (1 - θ * (1 - γ)) := by
  obtain ⟨h1, h2, h3⟩ := hd
  have h0 := dot_dir_zero A dx dy ds h2 h3
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hS : ∑ j, x j * s j = x ⬝ᵥ s := rfl
  have hsum : ∑ j, (s j * dx j + x j * ds j) = γ * (x ⬝ᵥ s) - x ⬝ᵥ s := by
    simp_rw [h1]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hS]
    unfold AdaptiveStepIPM.PredCorr.mu
    field_simp
  have expand : lineStep x dx θ ⬝ᵥ lineStep s ds θ =
      x ⬝ᵥ s + θ * ∑ j, (s j * dx j + x j * ds j) + θ ^ 2 * ∑ j, dx j * ds j := by
    simp only [lineStep, dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [expand, hsum, h0]; ring

lemma mu_line {m n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (γ : ℝ)
    (x s dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ)
    (hd : IsNewtonDirection A γ x s dx dy ds) (θ : ℝ) :
    AdaptiveStepIPM.PredCorr.mu (lineStep x dx θ) (lineStep s ds θ) =
      AdaptiveStepIPM.PredCorr.mu x s * (1 - θ * (1 - γ)) := by
  unfold AdaptiveStepIPM.PredCorr.mu
  rw [line_dot hn A γ x s dx dy ds hd θ]; ring

lemma w_lower {n : ℕ} {β : ℝ} {x s : Fin n → ℝ}
    (h : negInfNorm (centralityResidual x s) ≤ β * AdaptiveStepIPM.PredCorr.mu x s)
    (j : Fin n) : (1 - β) * AdaptiveStepIPM.PredCorr.mu x s ≤ x j * s j := by
  have h1 : |min (centralityResidual x s j) 0| ≤ negInfNorm (centralityResidual x s) := by
    unfold negInfNorm
    have := norm_le_pi_norm (fun j => min (centralityResidual x s j) 0) j
    simpa [Real.norm_eq_abs] using this
  have h2 := neg_abs_le (min (centralityResidual x s j) 0)
  have h3 := min_le_left (centralityResidual x s j) 0
  have h4 : centralityResidual x s j = x j * s j - AdaptiveStepIPM.PredCorr.mu x s := rfl
  linarith

lemma negInf_le {n : ℕ} (z : Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c) (h : ∀ j, -c ≤ z j) :
    negInfNorm z ≤ c := by
  unfold negInfNorm
  refine (pi_norm_le_iff_of_nonneg hc).2 fun j => ?_
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · exact le_min (h j) (by linarith)
  · exact (min_le_right _ _).trans hc

lemma pq_bound {n : ℕ} (x s dx ds : Fin n → ℝ) (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j)
    (h0 : ∑ j, dx j * ds j = 0)
    (hh : ∀ j, (s j * dx j + x j * ds j) ^ 2 ≤ (x j * s j) ^ 2) (j : Fin n) :
    -(dx j * ds j) * 4 ≤ ∑ i, x i * s i := by
  have hw : ∀ i, 0 < x i * s i := fun i => mul_pos (hx i) (hs i)
  have key : ∑ i, (s i * dx i - x i * ds i) ^ 2 / (x i * s i) =
      ∑ i, (s i * dx i + x i * ds i) ^ 2 / (x i * s i) := by
    have : ∀ i, (s i * dx i - x i * ds i) ^ 2 / (x i * s i) =
        (s i * dx i + x i * ds i) ^ 2 / (x i * s i) - 4 * (dx i * ds i) := by
      intro i
      have e : (s i * dx i - x i * ds i) ^ 2 =
          (s i * dx i + x i * ds i) ^ 2 - 4 * (dx i * ds i) * (x i * s i) := by ring
      rw [e, sub_div, mul_div_cancel_right₀ _ (hw i).ne']
    rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_sub_distrib, ← Finset.mul_sum, h0]
    ring
  have hle : ∑ i, (s i * dx i + x i * ds i) ^ 2 / (x i * s i) ≤ ∑ i, x i * s i := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [div_le_iff₀ (hw i)]; nlinarith [hh i]
  have hsingle : (s j * dx j - x j * ds j) ^ 2 / (x j * s j) ≤
      ∑ i, (s i * dx i - x i * ds i) ^ 2 / (x i * s i) :=
    Finset.single_le_sum (f := fun i => (s i * dx i - x i * ds i) ^ 2 / (x i * s i))
      (fun i _ => div_nonneg (sq_nonneg _) (hw i).le) (Finset.mem_univ j)
  have hid : -(dx j * ds j) * 4 ≤ (s j * dx j - x j * ds j) ^ 2 / (x j * s j) := by
    rw [le_div_iff₀ (hw j)]
    have e : (s j * dx j - x j * ds j) ^ 2 =
        (s j * dx j + x j * ds j) ^ 2 - 4 * (x j * s j) * (dx j * ds j) := by ring
    nlinarith [sq_nonneg (s j * dx j + x j * ds j)]
  linarith

lemma line_feas {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x s dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) (γ θ : ℝ)
    (hd : IsNewtonDirection A γ x s dx dy ds) (hAx : A *ᵥ x = b)
    (hy : ∃ y : Fin m → ℝ, Aᵀ *ᵥ y + s = c) :
    A *ᵥ lineStep x dx θ = b ∧ ∃ y : Fin m → ℝ, Aᵀ *ᵥ y + lineStep s ds θ = c := by
  obtain ⟨_, h2, h3⟩ := hd
  have ex : lineStep x dx θ = x + θ • dx := by funext j; simp [lineStep]
  have es : lineStep s ds θ = s + θ • ds := by funext j; simp [lineStep]
  obtain ⟨y, hy⟩ := hy
  refine ⟨by rw [ex, mulVec_add, mulVec_smul, h2, smul_zero, add_zero, hAx], y + θ • dy, ?_⟩
  rw [es, mulVec_add, mulVec_smul]
  calc Aᵀ *ᵥ y + θ • (Aᵀ *ᵥ dy) + (s + θ • ds) = (Aᵀ *ᵥ y + s) + θ • (Aᵀ *ᵥ dy + ds) := by
        rw [smul_add]; abel
    _ = c := by rw [hy, h3, smul_zero, add_zero]

/-- The ψ lower bound `(ρ − n) log(xᵀs) + n log n ≤ ψ`. -/
lemma psi_lower {n : ℕ} (hn : 1 ≤ n) (ρ : ℝ) (x s : Fin n → ℝ) (hx : ∀ j, 0 < x j)
    (hs : ∀ j, 0 < s j) :
    (ρ - n) * Real.log (x ⬝ᵥ s) + n * Real.log n ≤
      LinearOptimization.interiorPointPotential ρ x s := by
  have hw : ∀ j, 0 < x j * s j := fun j => mul_pos (hx j) (hs j)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hS : 0 < x ⬝ᵥ s := Finset.sum_pos (fun j _ => hw j) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  set S := x ⬝ᵥ s with hSdef
  set μ := S / n with hμdef
  have hμ : 0 < μ := div_pos hS hn0
  have h1 : ∀ j, Real.log (x j * s j) ≤ Real.log μ + (x j * s j / μ - 1) := by
    intro j
    have := Real.log_le_sub_one_of_pos (div_pos (hw j) hμ)
    rw [Real.log_div (hw j).ne' hμ.ne'] at this
    linarith
  have hsum : ∑ j, Real.log (x j * s j) ≤ n * (Real.log S - Real.log n) := by
    calc ∑ j, Real.log (x j * s j) ≤ ∑ j, (Real.log μ + (x j * s j / μ - 1)) :=
          Finset.sum_le_sum fun j _ => h1 j
      _ = n * Real.log μ + ((∑ j, x j * s j) / μ - n) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_div]; simp
      _ = n * (Real.log S - Real.log n) := by
          have : ∑ j, x j * s j = S := rfl
          rw [this, hμdef, Real.log_div hS.ne' hn0.ne']; field_simp; ring
  have hsplit : ∑ j, Real.log (x j) + ∑ j, Real.log (s j) = ∑ j, Real.log (x j * s j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => (Real.log_mul (hx j).ne' (hs j).ne').symm
  unfold LinearOptimization.interiorPointPotential
  rw [dotProduct_comm]
  linarith

/-- The ψ upper bound `ψ ≤ (ρ − n) log(xᵀs) + n log n + n log(1/(1 − β))` on `N_∞⁻(β)`. -/
lemma psi_upper {n : ℕ} (hn : 1 ≤ n) (ρ β : ℝ) (hβ1 : β < 1) (x s : Fin n → ℝ)
    (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j)
    (hlow : ∀ j, (1 - β) * AdaptiveStepIPM.PredCorr.mu x s ≤ x j * s j) :
    LinearOptimization.interiorPointPotential ρ x s ≤
      (ρ - n) * Real.log (x ⬝ᵥ s) + n * Real.log n + n * Real.log (1 / (1 - β)) := by
  have hw : ∀ j, 0 < x j * s j := fun j => mul_pos (hx j) (hs j)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hS : 0 < x ⬝ᵥ s := Finset.sum_pos (fun j _ => hw j) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hb : 0 < 1 - β := by linarith
  have hsum : n * (Real.log (1 - β) + Real.log (x ⬝ᵥ s) - Real.log n) ≤
      ∑ j, Real.log (x j * s j) := by
    calc n * (Real.log (1 - β) + Real.log (x ⬝ᵥ s) - Real.log n)
        = ∑ _j : Fin n, Real.log ((1 - β) * AdaptiveStepIPM.PredCorr.mu x s) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          unfold AdaptiveStepIPM.PredCorr.mu
          rw [Real.log_mul hb.ne' (div_pos hS hn0).ne', Real.log_div hS.ne' hn0.ne']; ring
      _ ≤ ∑ j, Real.log (x j * s j) := Finset.sum_le_sum fun j _ =>
          Real.log_le_log (mul_pos hb (by unfold AdaptiveStepIPM.PredCorr.mu
                                          exact div_pos hS hn0)) (hlow j)
  have hsplit : ∑ j, Real.log (x j) + ∑ j, Real.log (s j) = ∑ j, Real.log (x j * s j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => (Real.log_mul (hx j).ne' (hs j).ne').symm
  have hL : Real.log (1 / (1 - β)) = -Real.log (1 - β) := by
    rw [one_div, Real.log_inv]
  unfold LinearOptimization.interiorPointPotential
  rw [dotProduct_comm, hL]
  linarith

lemma beta_gamma_le {β γ : ℝ} (hβ0 : 0 < β) (hγβ : γ ≤ 2 * (1 - β)) : β * γ ≤ 1 / 2 := by
  nlinarith [sq_nonneg (2 * β - 1)]

/-- A point on the line, inside `N_∞⁻(β)`, at which `(ρ − n) log(xᵀs)` has dropped by
`12 n log(1/(1 − β))`. -/
lemma step_exists {m n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (β γ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hγβ : γ ≤ 2 * (1 - β)) (x s : Fin n → ℝ) (hN : InNinfMinus A b c β x s)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ)
    (hd : IsNewtonDirection A γ x s dx dy ds) :
    ∃ θ : ℝ, InNinfMinus A b c β (lineStep x dx θ) (lineStep s ds θ) ∧
      (rho n β γ - n) * Real.log (lineStep x dx θ ⬝ᵥ lineStep s ds θ) ≤
        (rho n β γ - n) * Real.log (x ⬝ᵥ s) - 12 * n * Real.log (1 / (1 - β)) := by
  obtain ⟨⟨hx, hs, hAx, hy⟩, hres⟩ := hN
  have hw : ∀ j, 0 < x j * s j := fun j => mul_pos (hx j) (hs j)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hS : 0 < x ⬝ᵥ s := Finset.sum_pos (fun j _ => hw j) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  set μ := AdaptiveStepIPM.PredCorr.mu x s with hμdef
  have hμ : 0 < μ := div_pos hS hn0
  have hSμ : x ⬝ᵥ s = n * μ := by rw [hμdef]; unfold AdaptiveStepIPM.PredCorr.mu; field_simp
  have hL : 0 < Real.log (1 / (1 - β)) :=
    Real.log_pos (one_lt_one_div (by linarith) (by linarith))
  set L := Real.log (1 / (1 - β)) with hLdef
  have hg : 0 < β * γ * (1 - γ) := by
    have : 0 < 1 - γ := by linarith
    positivity
  have hρn : rho n β γ - n = 3 / (β * γ * (1 - γ)) * L * (n : ℝ) ^ 2 := by
    unfold rho; ring
  have hfeas := fun θ => line_feas A b c x s dx dy ds γ θ hd hAx hy
  have hmu := mu_line hn A γ x s dx dy ds hd
  have hdot := line_dot hn A γ x s dx dy ds hd
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · -- n = 1
    have hn1 : n = 1 := by omega
    subst hn1
    have hρ1 : 0 < rho 1 β γ - 1 := by
      have := hρn; simp only [Nat.cast_one] at this; rw [this]; positivity
    set K := 12 * L / (rho 1 β γ - 1) with hK
    have hγ1' : 0 < 1 - γ := by linarith
    set θ := (1 - Real.exp (-K)) / (1 - γ) with hθ
    have hθu : 1 - θ * (1 - γ) = Real.exp (-K) := by
      rw [hθ]; field_simp; ring
    have hK0 : 0 < K := div_pos (by linarith) hρ1
    have hθ0 : 0 ≤ θ := by
      rw [hθ]; apply div_nonneg _ hγ1'.le
      have : Real.exp (-K) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
      linarith
    have hdot1 : ∀ (u v : Fin 1 → ℝ), u ⬝ᵥ v = u 0 * v 0 := by
      intro u v; simp [dotProduct]
    have hpos : ∀ τ, 0 ≤ τ → τ ≤ θ → 0 < 1 - τ * (1 - γ) := by
      intro τ _ hτ
      have : τ * (1 - γ) ≤ θ * (1 - γ) := mul_le_mul_of_nonneg_right hτ hγ1'.le
      have := Real.exp_pos (-K)
      linarith
    have hprod : ∀ τ, 0 ≤ τ → τ ≤ θ →
        0 < (x 0 + τ * dx 0) * (s 0 + τ * ds 0) := by
      intro τ h0 hτ
      have := hdot τ
      rw [hdot1, hdot1] at this
      simp only [lineStep] at this
      rw [this]
      exact mul_pos (by rw [← hdot1]; exact hS) (hpos τ h0 hτ)
    obtain ⟨hpx, hps⟩ := seg_pos (hx 0) (hs 0) hθ0 hprod
    refine ⟨θ, ⟨⟨?_, ?_, (hfeas θ).1, (hfeas θ).2⟩, ?_⟩, ?_⟩
    · intro j; rw [Fin.fin_one_eq_zero j]; exact hpx
    · intro j; rw [Fin.fin_one_eq_zero j]; exact hps
    · apply negInf_le
      · rw [hmu θ, hθu]; positivity
      · intro j
        rw [Fin.fin_one_eq_zero j]
        unfold centralityResidual AdaptiveStepIPM.PredCorr.mu
        rw [hdot1]
        have : 0 ≤ β * ((lineStep x dx θ 0 * lineStep s ds θ 0) / ((1 : ℕ) : ℝ)) := by
          have := mul_pos hpx hps
          simp only [lineStep]
          positivity
        simp only [Nat.cast_one, div_one] at this ⊢
        linarith
    · rw [hdot θ, hθu, Real.log_mul hS.ne' (Real.exp_pos _).ne', Real.log_exp, hK]
      field_simp
      simp only [Nat.cast_one]
      linarith
  · -- n ≥ 2
    have hbg := beta_gamma_le hβ0 hγβ
    set θ := 4 * β * γ / n with hθ
    have hθ0 : 0 ≤ θ := by positivity
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h2
    have hθ1 : θ ≤ 1 := by
      rw [hθ, div_le_one hn0]; linarith
    have hθn : θ * n = 4 * β * γ := by rw [hθ]; field_simp
    have hlow : ∀ j, (1 - β) * μ ≤ x j * s j := fun j => w_lower hres j
    obtain ⟨h1d, h2d, h3d⟩ := hd
    have h0 := dot_dir_zero A dx dy ds h2d h3d
    have hh : ∀ j, (s j * dx j + x j * ds j) ^ 2 ≤ (x j * s j) ^ 2 := by
      intro j
      rw [h1d j]
      have hlj := hlow j
      have a1 : 0 ≤ γ * μ := by positivity
      have a2 : γ * μ ≤ 2 * (x j * s j) := by nlinarith
      nlinarith [mul_nonneg a1 (by linarith : (0 : ℝ) ≤ 2 * (x j * s j) - γ * μ)]
    have hpq : ∀ j, -(dx j * ds j) * 4 ≤ n * μ := by
      intro j
      have := pq_bound x s dx ds hx hs h0 hh j
      have e : ∑ i, x i * s i = x ⬝ᵥ s := rfl
      rw [e, hSμ] at this; exact this
    -- residual bound at every τ ∈ [0, θ]
    have hres' : ∀ τ, 0 ≤ τ → τ ≤ θ → ∀ j,
        -(β * (μ * (1 - τ * (1 - γ)))) ≤
          (x j + τ * dx j) * (s j + τ * ds j) - μ * (1 - τ * (1 - γ)) := by
      intro τ hτ0 hτ j
      have hτ1 : τ ≤ 1 := hτ.trans hθ1
      have hτn : τ * n ≤ 4 * β * γ := by
        rw [← hθn]; exact mul_le_mul_of_nonneg_right hτ hn0.le
      have e : (x j + τ * dx j) * (s j + τ * ds j) =
          x j * s j + τ * (s j * dx j + x j * ds j) + τ ^ 2 * (dx j * ds j) := by ring
      rw [e, h1d j]
      have f1 : 0 ≤ (1 - τ) * (x j * s j - μ + β * μ) :=
        mul_nonneg (by linarith) (by linarith [hlow j])
      have f2 : 0 ≤ τ ^ 2 * (n * μ + 4 * (dx j * ds j)) :=
        mul_nonneg (sq_nonneg _) (by linarith [hpq j])
      have f3 : 0 ≤ τ * μ * (4 * β * γ - τ * n) :=
        mul_nonneg (mul_nonneg hτ0 hμ.le) (by linarith)
      nlinarith [f1, f2, f3]
    have hprod : ∀ j, ∀ τ, 0 ≤ τ → τ ≤ θ → 0 < (x j + τ * dx j) * (s j + τ * ds j) := by
      intro j τ hτ0 hτ
      have hτ1 : τ ≤ 1 := hτ.trans hθ1
      have hm : 0 < μ * (1 - τ * (1 - γ)) := by
        apply mul_pos hμ; nlinarith
      have := hres' τ hτ0 hτ j
      nlinarith
    refine ⟨θ, ⟨⟨fun j => (seg_pos (hx j) (hs j) hθ0 (hprod j)).1,
      fun j => (seg_pos (hx j) (hs j) hθ0 (hprod j)).2, (hfeas θ).1, (hfeas θ).2⟩, ?_⟩, ?_⟩
    · apply negInf_le
      · rw [hmu θ]; apply mul_nonneg hβ0.le; apply mul_nonneg hμ.le; nlinarith
      · intro j
        unfold centralityResidual
        rw [hmu θ]
        exact hres' θ hθ0 le_rfl j
    · have hu : 0 < 1 - θ * (1 - γ) := by nlinarith
      rw [hdot θ, Real.log_mul hS.ne' hu.ne']
      have hlog : Real.log (1 - θ * (1 - γ)) ≤ -(θ * (1 - γ)) := by
        have := Real.log_le_sub_one_of_pos hu; linarith
      have hρpos : 0 ≤ rho n β γ - n := by rw [hρn]; positivity
      have key : (rho n β γ - n) * (θ * (1 - γ)) = 12 * n * L := by
        have e1 : (1 - γ) ≠ 0 := (by linarith : (0:ℝ) < 1 - γ).ne'
        have e2 : β ≠ 0 := hβ0.ne'
        have e3 : γ ≠ 0 := hγ0.ne'
        have e4 : (n : ℝ) ≠ 0 := hn0.ne'
        rw [hρn, hθ]; field_simp; ring
      nlinarith [mul_le_mul_of_nonneg_left hlog hρpos]

lemma alg3_step_decrease {m n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (β γ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hγβ : γ ≤ 2 * (1 - β)) (x s x' s' : Fin n → ℝ)
    (hN : InNinfMinus A b c β x s) (hstep : Alg3Step A b c β γ (rho n β γ) x s x' s') :
    InNinfMinus A b c β x' s' ∧
      LinearOptimization.interiorPointPotential (rho n β γ) x' s' ≤
        LinearOptimization.interiorPointPotential (rho n β γ) x s -
          11 * n * Real.log (1 / (1 - β)) := by
  obtain ⟨dx, dy, ds, θbar, hd, hNbar, hmin, rfl, rfl⟩ := hstep
  obtain ⟨θ, hNθ, hlog⟩ := step_exists hn A b c β γ hβ0 hβ1 hγ0 hγ1 hγβ x s hN dx dy ds hd
  refine ⟨hNbar, ?_⟩
  have h1 := hmin θ hNθ
  have h2 := psi_upper hn (rho n β γ) β hβ1 _ _ hNθ.1.1 hNθ.1.2.1
    (fun j => w_lower hNθ.2 j)
  have h3 := psi_lower hn (rho n β γ) x s hN.1.1 hN.1.2.1
  linarith

end P46cc

open AdaptiveStepIPM.Potential in
theorem solution {m n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (β γ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hγβ : γ ≤ 2 * (1 - β)) (t : ℝ) (ht : 0 < t) (x s : ℕ → Fin n → ℝ)
    (hrun : IsAlg3Run A b c β γ (rho n β γ) t x s) :
    ∃ k : ℕ, k ≤ ⌈6 * (n : ℝ) * t / (11 * β * γ * (1 - γ))⌉₊ ∧
      x k ⬝ᵥ s k ≤ (2 : ℝ) ^ (-t) := by
  obtain ⟨hN0, _, hψ0, hstep⟩ := hrun
  set L := Real.log (1 / (1 - β)) with hLdef
  set K := ⌈6 * (n : ℝ) * t / (11 * β * γ * (1 - γ))⌉₊ with hKdef
  by_contra hcon
  push Not at hcon
  have inv : ∀ k, k ≤ K → InNinfMinus A b c β (x k) (s k) ∧
      LinearOptimization.interiorPointPotential (rho n β γ) (x k) (s k) ≤
        LinearOptimization.interiorPointPotential (rho n β γ) (x 0) (s 0) -
          k * (11 * n * L) := by
    intro k
    induction k with
    | zero => intro _; simp [hN0]
    | succ k ih =>
      intro hk
      obtain ⟨hNk, hψk⟩ := ih (by omega)
      obtain ⟨hN', hψ'⟩ := P46cc.alg3_step_decrease hn A b c β γ hβ0 hβ1 hγ0 hγ1 hγβ
        (x k) (s k) (x (k + 1)) (s (k + 1)) hNk (hstep k (hcon k (by omega)))
      refine ⟨hN', ?_⟩
      push_cast
      linarith
  obtain ⟨hNK, hψK⟩ := inv K le_rfl
  have hlow := P46cc.psi_lower hn (rho n β γ) (x K) (s K) hNK.1.1 hNK.1.2.1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < L := Real.log_pos (one_lt_one_div (by linarith) (by linarith))
  have hg : 0 < β * γ * (1 - γ) := by
    have : 0 < 1 - γ := by linarith
    positivity
  have hρn : rho n β γ - n = 3 / (β * γ * (1 - γ)) * L * (n : ℝ) ^ 2 := by
    unfold rho; ring
  have hρpos : 0 < rho n β γ - n := by rw [hρn]; positivity
  have hKge : 6 * (n : ℝ) * t / (11 * β * γ * (1 - γ)) ≤ K := Nat.le_ceil _
  have hq : 6 * (n : ℝ) * t / (11 * β * γ * (1 - γ)) * (11 * n * L) =
      2 * (rho n β γ - n) * t := by
    have e1 : (1 - γ) ≠ 0 := (by linarith : (0:ℝ) < 1 - γ).ne'
    have e2 : β ≠ 0 := hβ0.ne'
    have e3 : γ ≠ 0 := hγ0.ne'
    rw [hρn]; field_simp; ring
  have hKD : 2 * (rho n β γ - n) * t ≤ K * (11 * n * L) := by
    rw [← hq]; exact mul_le_mul_of_nonneg_right hKge (by positivity)
  have hlogS : Real.log (x K ⬝ᵥ s K) ≤ -t := by
    have : (rho n β γ - n) * Real.log (x K ⬝ᵥ s K) ≤ (rho n β γ - n) * (-t) := by
      linarith
    exact le_of_mul_le_mul_left this hρpos
  have hSpos : 0 < x K ⬝ᵥ s K :=
    Finset.sum_pos (fun j _ => mul_pos (hNK.1.1 j) (hNK.1.2.1 j)) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hle : x K ⬝ᵥ s K ≤ (2 : ℝ) ^ (-t) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc x K ⬝ᵥ s K = Real.exp (Real.log (x K ⬝ᵥ s K)) := (Real.exp_log hSpos).symm
      _ ≤ Real.exp (Real.log 2 * -t) := by
          apply Real.exp_le_exp.2
          have := Real.log_two_lt_d9
          nlinarith
  linarith [hcon K le_rfl]
