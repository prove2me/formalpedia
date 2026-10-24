-- Prove2me | solution 1 for AccelVI.AVC.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T13:01:02.729248+00:00
-- url     : https://prove2.me/submissions/f8a2687d-1287-4c74-9ffa-6a400112eb08

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_AVC_Setting
import Theorems.Thm_AccelVI_AVC_eq_5_3
import Theorems.Thm_AccelVI_AVC_spectrum_LPol_Icc

open AccelVI.AVC Matrix

theorem solution {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] (M : MDP S A)
    (hM : M.Valid) (pol : S → A → ℝ) (hpol : FoundationsML.ReinforcementLearning.IsPolicy pol)
    (hrev : IsReversible (LPol M pol)) :
    spectralRadius ℂ ((Bpol M pol).map (algebraMap ℝ ℂ)) = ENNReal.ofReal (theta M.lam) := by
  obtain ⟨hP, hl0, hl1⟩ := hM
  -- θ ∈ [0,1)
  have hk : 1 / kappa M.lam = (1 - M.lam) / (1 + M.lam) := by
    unfold kappa; field_simp
  have hk0 : 0 < 1 / kappa M.lam := by rw [hk]; apply div_pos <;> linarith
  have hk1 : 1 / kappa M.lam < 1 := by
    rw [hk, div_lt_one (by linarith)]; linarith
  have hsq1 : Real.sqrt (1 / kappa M.lam) < 1 := by
    rw [Real.sqrt_lt' one_pos]; simpa using hk1
  have hθ0 : 0 ≤ theta M.lam := by unfold theta; linarith
  -- row sums of L
  have hrow : ∀ i, ∑ j, LPol M pol i j = 1 := by
    intro i
    simp only [LPol, Matrix.of_apply, FoundationsML.ReinforcementLearning.InducedTransition]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simp [fun a => (hP i a).2, (hpol i).2]
  apply le_antisymm
  · -- upper bound
    apply iSup₂_le
    intro ω hω
    obtain ⟨μ, hμ, heq⟩ := eq_5_3 M ⟨hP, hl0, hl1⟩ pol hpol ω hω
    obtain ⟨t, ⟨ht1, ht2⟩, rfl⟩ := spectrum_LPol_Icc M ⟨hP, hl0, hl1⟩ pol hpol hrev μ hμ
    set θ := theta M.lam
    have hre := congrArg Complex.re heq
    have him := congrArg Complex.im heq
    simp [pow_two] at hre him
    have hn : ‖ω‖ ^ 2 = ω.re ^ 2 + ω.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hc : ω.re ^ 2 + ω.im ^ 2 = 1 / 2 * (t + 1) * θ ^ 2 := by
      have hdisc : ((t + 1) * θ) ^ 2 - 4 * (1 / 2 * (t + 1) * θ ^ 2) ≤ 0 := by
        have : ((t + 1) * θ) ^ 2 - 4 * (1 / 2 * (t + 1) * θ ^ 2) = θ ^ 2 * ((t + 1) * (t - 1)) := by
          ring
        rw [this]
        apply mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
        nlinarith
      have him' : ω.im * (2 * ω.re - (t + 1) * θ) = 0 := by linarith
      rcases mul_eq_zero.mp him' with h | h
      · rw [h] at hre
        have h2 : (2 * ω.re - (t + 1) * θ) ^ 2 ≤ 0 := by nlinarith
        have h3 : 2 * ω.re - (t + 1) * θ = 0 := by nlinarith [sq_nonneg (2 * ω.re - (t + 1) * θ)]
        rw [h]; nlinarith
      · have : ω.re = (t + 1) * θ / 2 := by linarith
        rw [this] at hre ⊢
        nlinarith
    have hle : ‖ω‖ ≤ θ := by
      have : ‖ω‖ ^ 2 ≤ θ ^ 2 := by
        rw [hn, hc]; nlinarith [sq_nonneg θ]
      nlinarith [norm_nonneg ω]
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
    exact ENNReal.ofReal_le_ofReal hle
  · -- lower bound: θ is an eigenvalue with eigenvector (θ·1, 1)
    set θ := theta M.lam
    obtain ⟨ν, ⟨⟨_, hν1⟩, _⟩, _⟩ := hrev.2
    have hne : Nonempty S := by
      by_contra h
      rw [not_nonempty_iff] at h
      simp at hν1
    obtain ⟨i0⟩ := hne
    let v : S ⊕ S → ℝ := Sum.elim (fun _ => θ) (fun _ => 1)
    have hL1 : ∀ c : ℝ, (LPol M pol) *ᵥ (fun _ => c) = fun _ => c := by
      intro c; funext i
      simp [Matrix.mulVec, dotProduct, ← Finset.sum_mul, hrow i]
    have hBv : (Bpol M pol) *ᵥ v = θ • v := by
      unfold Bpol
      rw [Matrix.fromBlocks_mulVec]
      funext i
      rcases i with i | i
      · simp only [Sum.elim_inl, v]
        have e1 : (fun _ : S => θ) = ((Sum.elim (fun _ : S => θ) (fun _ : S => (1:ℝ))) ∘ Sum.inl) := rfl
        simp only [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Function.comp_def,
          Sum.elim_inl, Sum.elim_inr, hL1, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      · simp [v, Function.comp_def]
    have hmem : (θ : ℂ) ∈ spectrum ℂ ((Bpol M pol).map (algebraMap ℝ ℂ)) := by
      rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨fun i => ((v i : ℝ) : ℂ), ?_, ?_⟩
      · intro h
        have := congrFun h (Sum.inr i0)
        simp [v] at this
      · funext i
        rw [Matrix.sub_mulVec, Pi.sub_apply, Matrix.algebraMap_eq_diagonal]
        simp only [Pi.algebraMap_apply, Matrix.mulVec_diagonal]
        have hm : ((Bpol M pol).map (algebraMap ℝ ℂ) *ᵥ fun i => ((v i : ℝ) : ℂ)) i =
            (((Bpol M pol) *ᵥ v) i : ℂ) := by
          simp [Matrix.mulVec, dotProduct]
        rw [hm, hBv]
        simp
    have := le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ ((Bpol M pol).map (algebraMap ℝ ℂ))) =>
      (‖k‖₊ : ENNReal)) (θ : ℂ) hmem
    unfold spectralRadius
    refine le_trans ?_ this
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
    simp [abs_of_nonneg hθ0]
