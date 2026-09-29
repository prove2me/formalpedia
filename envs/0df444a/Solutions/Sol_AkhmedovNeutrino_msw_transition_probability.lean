-- Prove2me | solution 1 for AkhmedovNeutrino.msw_transition_probability
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T23:47:09.817302+00:00
-- url     : https://prove2.me/submissions/08621fa2-ee9b-48e2-ac06-f4c817908d8d

import Mathlib
import Definitions.Def_AkhmedovNeutrino_MSW

set_option autoImplicit false

open Complex

theorem msw_Sderiv_a1e4 (ω b t : ℝ) (hb : ω = 0 → b = 0) :
    HasDerivAt (fun t : ℝ => b * (Real.sin (ω * t) / ω)) (b * Real.cos (ω * t)) t := by
  by_cases hω : ω = 0
  · have : b = 0 := hb hω
    subst this
    simpa using hasDerivAt_const t (0 : ℝ)
  · have h1 : HasDerivAt (fun t : ℝ => ω * t) (ω * 1) t := (hasDerivAt_id' t).const_mul ω
    have h2 := ((h1.sin).div_const ω).const_mul b
    refine h2.congr_deriv ?_
    field_simp

theorem msw_alg0_a1e4 (e J V b k ω cs sn : ℂ) (hJ : J ^ 2 = -1)
    (hkey : (b ^ 2 + k ^ 2) * (sn / ω) = ω * sn) :
    e * ((-(V / 2) * 1) * J) * (cs + J * (b * (sn / ω))) + e * ((-sn * (ω * 1)) + J * (b * cs))
      = -(J * ((-b + V / 2) * (e * (cs + J * (b * (sn / ω))))
          + k * (e * (-J * (k * (sn / ω)))))) := by
  linear_combination e * hkey - e * (b ^ 2 + k ^ 2) * (sn / ω) * hJ

theorem msw_alg1_a1e4 (e J V b k ω cs sn : ℂ) :
    e * ((-(V / 2) * 1) * J) * (-J * (k * (sn / ω))) + e * (-J * (k * cs))
      = -(J * (k * (e * (cs + J * (b * (sn / ω))))
          + (b + V / 2) * (e * (-J * (k * (sn / ω)))))) := by
  ring

theorem msw_core_a1e4 (V b k ω : ℝ) (hω : ω ^ 2 = b ^ 2 + k ^ 2) (ν : ℝ → Fin 2 → ℂ)
    (hν : ∀ t : ℝ, HasDerivAt ν
      (-(Complex.I • ((!![-b + V / 2, k; k, b + V / 2] : Matrix (Fin 2) (Fin 2) ℝ).map
        ((↑) : ℝ → ℂ)).mulVec (ν t))) t)
    (h0 : ν 0 = ![1, 0]) (L : ℝ) :
    ν L 1 = cexp (↑(-(V / 2) * L) * I) * (-I * ↑(k * (Real.sin (ω * L) / ω))) := by
  set A : Matrix (Fin 2) (Fin 2) ℂ :=
    (!![-b + V / 2, k; k, b + V / 2] : Matrix (Fin 2) (Fin 2) ℝ).map ((↑) : ℝ → ℂ) with hA
  have hb0 : ω = 0 → b = 0 := by
    intro h; rw [h] at hω; nlinarith [sq_nonneg b, sq_nonneg k]
  have hk0 : ω = 0 → k = 0 := by
    intro h; rw [h] at hω; nlinarith [sq_nonneg b, sq_nonneg k]
  let ψ : ℝ → Fin 2 → ℂ := fun t =>
    ![cexp (↑(-(V / 2) * t) * I) * (↑(Real.cos (ω * t)) + I * ↑(b * (Real.sin (ω * t) / ω))),
      cexp (↑(-(V / 2) * t) * I) * (-I * ↑(k * (Real.sin (ω * t) / ω)))]
  have hψ : ∀ t : ℝ, HasDerivAt ψ (-(Complex.I • A.mulVec (ψ t))) t := by
    intro t
    have he : HasDerivAt (fun t : ℝ => cexp (↑(-(V / 2) * t) * I))
        (cexp (↑(-(V / 2) * t) * I) * (↑(-(V / 2) * 1) * I)) t :=
      ((((hasDerivAt_id' t).const_mul (-(V / 2))).ofReal_comp).mul_const I).cexp
    have hC : HasDerivAt (fun t : ℝ => ((Real.cos (ω * t) : ℝ) : ℂ))
        ((-Real.sin (ω * t) * (ω * 1) : ℝ) : ℂ) t :=
      (((hasDerivAt_id' t).const_mul ω).cos).ofReal_comp
    have hSb : HasDerivAt (fun t : ℝ => ((b * (Real.sin (ω * t) / ω) : ℝ) : ℂ))
        ((b * Real.cos (ω * t) : ℝ) : ℂ) t := (msw_Sderiv_a1e4 ω b t hb0).ofReal_comp
    have hSk : HasDerivAt (fun t : ℝ => ((k * (Real.sin (ω * t) / ω) : ℝ) : ℂ))
        ((k * Real.cos (ω * t) : ℝ) : ℂ) t := (msw_Sderiv_a1e4 ω k t hk0).ofReal_comp
    have hkey : (b ^ 2 + k ^ 2) * (Real.sin (ω * t) / ω) = ω * Real.sin (ω * t) := by
      by_cases h : ω = 0
      · rw [hb0 h, hk0 h, h]; simp
      · rw [← hω]; field_simp
    have hkeyC : ((b : ℂ) ^ 2 + (k : ℂ) ^ 2) * ((Real.sin (ω * t) : ℂ) / (ω : ℂ))
        = (ω : ℂ) * (Real.sin (ω * t) : ℂ) := by exact_mod_cast hkey
    have hmv0 : ∀ x : Fin 2 → ℂ, (-(Complex.I • A.mulVec x)) 0
        = -(I * (((-b + V / 2 : ℝ) : ℂ) * x 0 + (k : ℂ) * x 1)) := by
      intro x; simp [hA]
    have hmv1 : ∀ x : Fin 2 → ℂ, (-(Complex.I • A.mulVec x)) 1
        = -(I * ((k : ℂ) * x 0 + ((b + V / 2 : ℝ) : ℂ) * x 1)) := by
      intro x; simp [hA]
    have d0 : HasDerivAt (fun x : ℝ => cexp (↑(-(V / 2) * x) * I) *
        (↑(Real.cos (ω * x)) + I * ↑(b * (Real.sin (ω * x) / ω))))
        (cexp (↑(-(V / 2) * t) * I) * (↑(-(V / 2) * 1) * I) *
          (↑(Real.cos (ω * t)) + I * ↑(b * (Real.sin (ω * t) / ω))) +
         cexp (↑(-(V / 2) * t) * I) *
          (↑(-Real.sin (ω * t) * (ω * 1)) + I * ↑(b * Real.cos (ω * t)))) t :=
      he.mul (hC.add (hSb.const_mul I))
    have d1 : HasDerivAt (fun x : ℝ => cexp (↑(-(V / 2) * x) * I) *
        (-I * ↑(k * (Real.sin (ω * x) / ω))))
        (cexp (↑(-(V / 2) * t) * I) * (↑(-(V / 2) * 1) * I) *
          (-I * ↑(k * (Real.sin (ω * t) / ω))) +
         cexp (↑(-(V / 2) * t) * I) * (-I * ↑(k * Real.cos (ω * t)))) t :=
      he.mul (hSk.const_mul (-I))
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · refine HasDerivAt.congr_deriv d0 ?_
      show _ = (-(Complex.I • A.mulVec (ψ t))) 0
      rw [hmv0]
      show _ = -(I * (((-b + V / 2 : ℝ) : ℂ) *
          (cexp (↑(-(V / 2) * t) * I) *
            (↑(Real.cos (ω * t)) + I * ↑(b * (Real.sin (ω * t) / ω)))) +
          (k : ℂ) * (cexp (↑(-(V / 2) * t) * I) * (-I * ↑(k * (Real.sin (ω * t) / ω))))))
      have := msw_alg0_a1e4 (cexp (↑(-(V / 2) * t) * I)) I (V : ℂ) (b : ℂ) (k : ℂ) (ω : ℂ)
        (Real.cos (ω * t) : ℂ) (Real.sin (ω * t) : ℂ) Complex.I_sq hkeyC
      push_cast at this ⊢
      linear_combination this
    · refine HasDerivAt.congr_deriv d1 ?_
      show _ = (-(Complex.I • A.mulVec (ψ t))) 1
      rw [hmv1]
      show _ = -(I * ((k : ℂ) *
          (cexp (↑(-(V / 2) * t) * I) *
            (↑(Real.cos (ω * t)) + I * ↑(b * (Real.sin (ω * t) / ω)))) +
          ((b + V / 2 : ℝ) : ℂ) *
            (cexp (↑(-(V / 2) * t) * I) * (-I * ↑(k * (Real.sin (ω * t) / ω))))))
      have := msw_alg1_a1e4 (cexp (↑(-(V / 2) * t) * I)) I (V : ℂ) (b : ℂ) (k : ℂ) (ω : ℂ)
        (Real.cos (ω * t) : ℂ) (Real.sin (ω * t) : ℂ)
      push_cast at this ⊢
      linear_combination this
  -- Lipschitz bound for the linear vector field
  let Lc : (Fin 2 → ℂ) →L[ℝ] (Fin 2 → ℂ) :=
    ((-(I • LinearMap.toContinuousLinearMap (Matrix.mulVecLin A))) :
      (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)).restrictScalars ℝ
  have hLc : (fun x : Fin 2 → ℂ => -(Complex.I • A.mulVec x)) = ⇑Lc := by
    funext x
    simp [Lc]
  have hv : ∀ _t : ℝ, LipschitzOnWith ‖Lc‖₊
      (fun x : Fin 2 → ℂ => -(Complex.I • A.mulVec x)) Set.univ := by
    intro _t
    rw [hLc]
    exact Lc.lipschitz.lipschitzOnWith
  have hψ0 : ψ 0 = ![1, 0] := by
    funext i
    fin_cases i <;> simp [ψ]
  have heq : ν = ψ :=
    ODE_solution_unique_univ (v := fun _ x => -(Complex.I • A.mulVec x))
      (s := fun _ => Set.univ) (t₀ := 0) hv
      (fun t => ⟨hν t, Set.mem_univ _⟩) (fun t => ⟨hψ t, Set.mem_univ _⟩)
      (by rw [h0, hψ0])
  rw [heq]
  simp [ψ]

open AkhmedovNeutrino in
theorem solution (Δm2 E θ0 GF Ne : ℝ) (hE : 0 < E)
    (ν : ℝ → Fin 2 → ℂ)
    (hν : ∀ t : ℝ, HasDerivAt ν
      (-(Complex.I • ((mswHamiltonian Δm2 E θ0 GF Ne).map ((↑) : ℝ → ℂ)).mulVec (ν t))) t)
    (h0 : ν 0 = ![1, 0]) (L : ℝ) :
    Complex.normSq (ν L 1) =
      matterOscAmplitude Δm2 E θ0 GF Ne *
        Real.sin (Real.pi * L / matterOscLength Δm2 E θ0 GF Ne) ^ 2 := by
  have hD : 0 ≤ (Δm2 / (2 * E) * Real.cos (2 * θ0) - ccPotential GF Ne) ^ 2
      + (Δm2 / (2 * E)) ^ 2 * Real.sin (2 * θ0) ^ 2 := by positivity
  have hg2 : matterEnergyGap Δm2 E θ0 GF Ne ^ 2 =
      (Δm2 / (2 * E) * Real.cos (2 * θ0) - ccPotential GF Ne) ^ 2
        + (Δm2 / (2 * E)) ^ 2 * Real.sin (2 * θ0) ^ 2 := by
    rw [matterEnergyGap, Real.sq_sqrt hD]
  have hgnn : 0 ≤ matterEnergyGap Δm2 E θ0 GF Ne := Real.sqrt_nonneg _
  set g := matterEnergyGap Δm2 E θ0 GF Ne with hg
  set V := ccPotential GF Ne with hV
  set b := (Δm2 / (2 * E) * Real.cos (2 * θ0) - V) / 2 with hb
  set k := Δm2 / (2 * E) * Real.sin (2 * θ0) / 2 with hk
  have hHam : mswHamiltonian Δm2 E θ0 GF Ne =
      (!![-b + V / 2, k; k, b + V / 2] : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mswHamiltonian, hb, hk, hV] <;> ring
  rw [hHam] at hν
  have hω : (g / 2) ^ 2 = b ^ 2 + k ^ 2 := by
    rw [div_pow, hg2, hb, hk]; ring
  have hcore := msw_core_a1e4 V b k (g / 2) hω ν hν h0 L
  rw [hcore]
  have hn1 : Complex.normSq (cexp (↑(-(V / 2) * L) * I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]; norm_num
  rw [Complex.normSq_mul, hn1, Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_I,
    Complex.normSq_ofReal, one_mul, one_mul]
  unfold matterOscAmplitude matterOscLength
  rw [← hg2]
  by_cases hg0 : g = 0
  · have hk0 : k = 0 := by
      have : k ^ 2 ≤ 0 := by nlinarith [sq_nonneg b]
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm this (sq_nonneg k))
    rw [hk0, hg0]; simp
  · have hgp : 0 < g := lt_of_le_of_ne hgnn (fun h => hg0 h.symm)
    have harg : Real.pi * L / (2 * Real.pi / g) = g / 2 * L := by
      field_simp
    rw [harg, hk]
    field_simp
