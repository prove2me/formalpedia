-- Prove2me | solution 1 for ALADIN.DualDecomp.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:57:16.599795+00:00
-- url     : https://prove2.me/submissions/54346909-7a1c-441d-8a90-32155e578bca

import Mathlib
import Definitions.Def_ALADIN_DualDecomp_Problem
import Definitions.Def_ALADIN_DualDecomp_Step

open Matrix ALADIN.DualDecomp

private theorem reduced_props {n nh : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin nh) (Fin n) ℝ) (hH : H.PosDef) (hC : C.rank = nh) :
    let Q := C * H⁻¹ * Cᵀ
    let P := H⁻¹ - H⁻¹ * Cᵀ * Q⁻¹ * C * H⁻¹
    Q.PosDef ∧ P.IsHermitian ∧ C * P = 0 ∧ P * Cᵀ = 0 ∧
      H * P = 1 - Cᵀ * Q⁻¹ * C * H⁻¹ ∧
      P * H = 1 - H⁻¹ * Cᵀ * Q⁻¹ * C ∧ P.PosSemidef := by
  dsimp only
  let Q := C * H⁻¹ * Cᵀ
  let P := H⁻¹ - H⁻¹ * Cᵀ * Q⁻¹ * C * H⁻¹
  have hinj : Function.Injective C.vecMul := by
    rw [Matrix.vecMul_injective_iff, linearIndependent_iff_card_eq_finrank_span]
    simpa [← C.rank_eq_finrank_span_row, Set.finrank] using hC.symm
  have hQ : Q.PosDef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hH.inv.mul_mul_conjTranspose_same hinj
  have hHunit : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  have hQunit : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ.isUnit
  have hHsym : H⁻¹ᵀ = H⁻¹ := by simpa using hH.inv.isHermitian.eq
  have hQsym : Q⁻¹ᵀ = Q⁻¹ := by simpa using hQ.inv.isHermitian.eq
  have hPsym : Pᵀ = P := by
    dsimp [P]
    simp only [transpose_sub, transpose_mul, transpose_transpose, hHsym, hQsym]
    simp only [Matrix.mul_assoc]
  have hCP : C * P = 0 := by
    dsimp [P]
    rw [Matrix.mul_sub]
    have he : C * (H⁻¹ * Cᵀ * Q⁻¹ * C * H⁻¹) = Q * Q⁻¹ * (C * H⁻¹) := by
      dsimp [Q]
      simp only [Matrix.mul_assoc]
    rw [he, Q.mul_nonsing_inv hQunit, Matrix.one_mul, sub_self]
  have hPC : P * Cᵀ = 0 := by
    have := congrArg Matrix.transpose hCP
    simpa only [transpose_mul, hPsym, transpose_zero] using this
  have hHP : H * P = 1 - Cᵀ * Q⁻¹ * C * H⁻¹ := by
    dsimp [P]
    rw [Matrix.mul_sub, H.mul_nonsing_inv hHunit]
    have he : H * (H⁻¹ * Cᵀ * Q⁻¹ * C * H⁻¹) =
        (H * H⁻¹) * (Cᵀ * Q⁻¹ * C * H⁻¹) := by simp only [Matrix.mul_assoc]
    rw [he, H.mul_nonsing_inv hHunit, Matrix.one_mul]
  have hPH : P * H = 1 - H⁻¹ * Cᵀ * Q⁻¹ * C := by
    have := congrArg Matrix.transpose hHP
    simpa only [transpose_mul, transpose_sub, transpose_one, transpose_transpose,
      hPsym, hHsym, hQsym, show Hᵀ = H by simpa using hH.isHermitian.eq,
      Matrix.mul_assoc] using this
  have hPHP : P * H * P = P := by
    rw [hPH, Matrix.sub_mul, Matrix.one_mul]
    have he : H⁻¹ * Cᵀ * Q⁻¹ * C * P = H⁻¹ * Cᵀ * Q⁻¹ * (C * P) := by
      simp only [Matrix.mul_assoc]
    rw [he, hCP, Matrix.mul_zero, sub_zero]
  have hP : P.PosSemidef := by
    have hp := hH.posSemidef.conjTranspose_mul_mul_same P
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hPsym, hPHP] using hp
  exact ⟨hQ, by simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hPsym,
    hCP, hPC, hHP, hPH, hP⟩

private theorem negative_shift {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ)
    (hM : (-M).PosSemidef) (μ : ℝ) (hμ : 0 < μ) :
    (-(M - μ⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ))).PosDef := by
  have hp : (μ⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)).PosDef :=
    Matrix.PosDef.one.smul (inv_pos.mpr hμ)
  have he : -(M - μ⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)) = μ⁻¹ • 1 + -M := by abel
  rw [he]
  exact hp.add_posSemidef hM

private theorem stationarity_aux {N n m nh : ℕ} (P : Problem N n m nh) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (lam : Fin m → ℝ) (i : Fin N) (yi : Fin n → ℝ) (κi : Fin nh → ℝ)
    (Ci : Matrix (Fin nh) (Fin n) ℝ)
    (hf : ContDiff ℝ 2 (P.f i)) (hh : ContDiff ℝ 2 (P.h i))
    (hstep1 : Step1Solution P 0 Sig x lam i yi κi) :
    grad (P.f i) yi + (P.A i)ᵀ *ᵥ lam + (Cstar P i yi)ᵀ *ᵥ κi = 0 ∧
    modGrad P i yi κi Ci + (P.A i)ᵀ *ᵥ lam + Ciᵀ *ᵥ κi = 0 := by
  let L : (Fin n → ℝ) →L[ℝ] ℝ :=
    ((dotProductBilin ℝ ℝ lam).comp (Matrix.mulVecLin (P.A i))).toContinuousLinearMap
  have hg : grad (decoupledObjective P 0 Sig x lam i) yi =
      grad (P.f i) yi + (P.A i)ᵀ *ᵥ lam := by
    have he : decoupledObjective P 0 Sig x lam i =
        P.f i + L := by
      ext z
      simp [decoupledObjective, L, dotProductBilin]
    ext k
    change (fderiv ℝ (decoupledObjective P 0 Sig x lam i) yi) (Pi.single k 1) = _
    rw [he, fderiv_add (hf.differentiable (by norm_num) yi) L.differentiableAt, L.fderiv]
    change (fderiv ℝ (P.f i) yi) (Pi.single k 1) + lam ⬝ᵥ (P.A i *ᵥ Pi.single k 1) = _
    rw [Matrix.mulVec_single_one]
    simp [grad, mulVec, dotProduct, Matrix.transpose_apply, mul_comm]
  have hc : (Cstar P i yi)ᵀ *ᵥ κi =
      ∑ j, κi j • grad (fun z => P.h i z j) yi := by
    ext k
    simp only [mulVec, dotProduct, transpose_apply, Cstar, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hj
    · ring
    · have hk := (mul_eq_zero.mp (hstep1.2.2.2.1 j)).resolve_right hj
      simp [hk]
  have hs : grad (P.f i) yi + (P.A i)ᵀ *ᵥ lam + (Cstar P i yi)ᵀ *ᵥ κi = 0 := by
    rw [hc, ← hg]
    exact hstep1.2.2.2.2
  refine ⟨hs, ?_⟩
  simp only [modGrad, transpose_sub, sub_mulVec]
  linear_combination hs

theorem solution {N n m nh : ℕ} (P : Problem N n m nh)
    (hf : ∀ i, ContDiff ℝ 2 (P.f i)) (hh : ∀ i, ContDiff ℝ 2 (P.h i))
    (hfconv : ∀ i, StrictConvexOn ℝ Set.univ (P.f i))
    (hhconv : ∀ i j, ConvexOn ℝ Set.univ (fun z => P.h i z j))
    (x : Fin N → Fin n → ℝ) (lam : Fin m → ℝ)
    (ρ : ℝ) (hρ : ρ = 0) (Sig : Fin N → Matrix (Fin n) (Fin n) ℝ) (hSig : ∀ i, (Sig i).PosSemidef)
    (y : Fin N → Fin n → ℝ) (κ : Fin N → Fin nh → ℝ)
    (hstep1 : ∀ i, Step1Solution P ρ (Sig i) (x i) lam i (y i) (κ i))
    (C : Fin N → Matrix (Fin nh) (Fin n) ℝ) (hC : ∀ i, (C i).rank = nh)
    (H : Fin N → Matrix (Fin n) (Fin n) ℝ) (hH : ∀ i, (H i).PosDef)
    (μ : ℝ) (hμ : 0 < μ)
    (Δy : Fin N → Fin n → ℝ) (s : Fin m → ℝ) (lamQP : Fin m → ℝ) (ν : Fin N → Fin nh → ℝ)
    (hQP : QPKKT P lam y κ C H μ Δy s lamQP ν)
    (α α₃ : ℝ) (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hα₃ : α₃ = α) :
    IsUnit (Mmat P C H - μ⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)).det ∧
    lamPlus lam α₃ lamQP = lamDD lam α μ (Mmat P C H) (gradV P y) := by
  subst ρ
  subst α₃
  let R : Fin N → Matrix (Fin n) (Fin n) ℝ := fun i => reducedInv (H i) (C i)
  have hR (i : Fin N) : (R i).PosSemidef := (reduced_props (H i) (C i) (hH i) (hC i)).2.2.2.2.2.2
  have hM : (-Mmat P C H).PosSemidef := by
    have hp (i : Fin N) : (P.A i * R i * (P.A i)ᵀ).PosSemidef := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        (hR i).mul_mul_conjTranspose_same (P.A i)
    simpa [Mmat, R] using Matrix.posSemidef_sum Finset.univ (fun i _ => hp i)
  let K := Mmat P C H - μ⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)
  have hKneg : (-K).PosDef := negative_shift (Mmat P C H) hM μ hμ
  have hKunit : IsUnit K := by simpa using hKneg.isUnit
  have hKdet : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).mp hKunit
  let d := lamQP - lam
  have hdy (i : Fin N) : Δy i = -(R i *ᵥ ((P.A i)ᵀ *ᵥ d)) := by
    obtain ⟨hq, hps, hcp, hpc, hhp, hph, hp⟩ := reduced_props (H i) (C i) (hH i) (hC i)
    change R i * (C i)ᵀ = 0 at hpc
    change R i * H i = 1 - (H i)⁻¹ * (C i)ᵀ * (C i * (H i)⁻¹ * (C i)ᵀ)⁻¹ * C i at hph
    have hid : R i *ᵥ (H i *ᵥ Δy i) = Δy i := by
      rw [Matrix.mulVec_mulVec, hph, Matrix.sub_mulVec, Matrix.one_mulVec]
      simp only [← Matrix.mulVec_mulVec, hQP.2.2.2 i, Matrix.mulVec_zero, sub_zero]
    have hz (u : Fin nh → ℝ) : R i *ᵥ ((C i)ᵀ *ᵥ u) = 0 := by
      rw [Matrix.mulVec_mulVec, hpc, Matrix.zero_mulVec]
    have hs := (stationarity_aux P (Sig i) (x i) lam i (y i) (κ i) (C i)
      (hf i) (hh i) (hstep1 i)).2
    have he : H i *ᵥ Δy i + (P.A i)ᵀ *ᵥ d + (C i)ᵀ *ᵥ (ν i - κ i) = 0 := by
      dsimp [d]
      simp only [Matrix.mulVec_sub]
      linear_combination hQP.1 i - hs
    have he' := congrArg (fun z => R i *ᵥ z) he
    simp only [Matrix.mulVec_add, hid, hz, add_zero, Matrix.mulVec_zero] at he'
    exact eq_neg_of_add_eq_zero_left he'
  have hMd : Mmat P C H *ᵥ d = ∑ i, P.A i *ᵥ Δy i := by
    simp only [Mmat, Matrix.neg_mulVec]
    rw [Matrix.sum_mulVec]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hdy, Matrix.mulVec_neg]
    simp only [R, ← Matrix.mulVec_mulVec]
  have hcouple : gradV P y + Mmat P C H *ᵥ d = s := by
    rw [hMd]
    have hc := hQP.2.2.1
    simp only [Matrix.mulVec_add, Finset.sum_add_distrib] at hc
    dsimp [gradV]
    linear_combination hc
  have hs : μ • s = d := by
    dsimp [d]
    linear_combination hQP.2.1
  have his : μ⁻¹ • d = s := by rw [← hs, inv_smul_smul₀ (ne_of_gt hμ)]
  have hKd : K *ᵥ d = -(gradV P y) := by
    dsimp [K]
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, his]
    linear_combination hcouple
  have hd : d = -(K⁻¹ *ᵥ gradV P y) := by
    have he := congrArg (fun z => K⁻¹ *ᵥ z) hKd
    rw [Matrix.mulVec_mulVec, K.nonsing_inv_mul hKdet, Matrix.one_mulVec,
      Matrix.mulVec_neg] at he
    exact he
  refine ⟨hKdet, ?_⟩
  change lam + α • d = lam - α • (K⁻¹ *ᵥ gradV P y)
  rw [hd, smul_neg, sub_eq_add_neg]
