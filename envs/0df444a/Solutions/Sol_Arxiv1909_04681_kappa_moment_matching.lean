-- Prove2me | solution 1 for Arxiv1909_04681.kappa_moment_matching
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T06:53:23.063229+00:00
-- url     : https://prove2.me/submissions/33622d62-4f77-49fd-9105-5b595b14e5b1

import Mathlib
import Definitions.Def_Arxiv1909_04681_Basic

open Filter Topology Asymptotics Set

namespace S81MM
open Arxiv1909_04681

lemma taylor3 (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (hev : ∀ x, f (-x) = f x) :
    (fun x => f x - (f 0 + iteratedDeriv 2 f 0 / 2 * x ^ 2)) =O[𝓝 0] fun x => x ^ 3 := by
  have h := (taylor_isLittleO_univ (x₀ := 0) hf).isBigO
  have hdf : DifferentiableAt ℝ f 0 := hf.differentiable (by norm_num) 0
  have h1 := hdf.hasDerivAt
  have h2 := HasDerivAt.comp (0:ℝ) (by simpa using h1 : HasDerivAt f (deriv f 0) (-0)) (hasDerivAt_neg 0)
  rw [show f ∘ (fun x => -x) = f from funext hev] at h2
  have hd : deriv f 0 = 0 := by have := h1.unique h2; linarith
  have hT : ∀ x, taylorWithinEval f 3 univ 0 x = f 0 + deriv f 0 * x + iteratedDeriv 2 f 0 / 2 * x ^ 2 +
      iteratedDeriv 3 f 0 / 6 * x ^ 3 := by
    intro x
    simp [taylorWithinEval_succ, taylor_within_zero_eval, iteratedDerivWithin_univ, Nat.factorial]
    ring
  have h3 : (fun x : ℝ => iteratedDeriv 3 f 0 / 6 * x ^ 3) =O[𝓝 0] fun x => x ^ 3 :=
    (isBigO_refl _ _).const_mul_left _
  simp only [sub_zero] at h
  have := h.add h3
  refine this.congr_left (fun x => ?_)
  rw [hT, hd]; ring

lemma I0_pos (κ : ℝ) : 1 ≤ besselI 0 κ := by
  unfold besselI
  have hs : Summable (fun k : ℕ => (κ ^ 2 / 4) ^ k / ((k.factorial : ℝ) * ((0 + k).factorial : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      (Real.summable_pow_div_factorial (κ ^ 2 / 4))
    have h1 : (1 : ℝ) ≤ ((0 + k).factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
    have h2 : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    apply div_le_div_of_nonneg_left (by positivity) h2
    nlinarith
  have := hs.le_tsum 0 (fun k _ => by positivity)
  simpa using this

lemma vm_eq (κ : ℝ) : vonMises 0 κ = fun x => Real.exp (κ * Real.cos x) / (2 * Real.pi * besselI 0 κ) := by
  funext x; simp [vonMises]

lemma vm_d2 (κ : ℝ) : iteratedDeriv 2 (vonMises 0 κ) 0 = -κ * Real.exp κ / (2 * Real.pi * besselI 0 κ) := by
  rw [vm_eq, iteratedDeriv_succ, iteratedDeriv_one]
  set c := 2 * Real.pi * besselI 0 κ
  have hd : ∀ x, HasDerivAt (fun x => Real.exp (κ * Real.cos x) / c)
      (Real.exp (κ * Real.cos x) * (κ * -Real.sin x) / c) x := by
    intro x
    exact (((Real.hasDerivAt_cos x).const_mul κ).exp).div_const c
  rw [show deriv (fun x => Real.exp (κ * Real.cos x) / c) =
    fun x => Real.exp (κ * Real.cos x) * (κ * -Real.sin x) / c from funext fun x => (hd x).deriv]
  have h2 : HasDerivAt (fun x => Real.exp (κ * Real.cos x) * (κ * -Real.sin x) / c)
      ((Real.exp (κ * Real.cos 0) * (κ * -Real.sin 0) * (κ * -Real.sin 0) +
        Real.exp (κ * Real.cos 0) * (κ * -Real.cos 0)) / c) 0 := by
    exact ((((Real.hasDerivAt_cos 0).const_mul κ).exp).mul (((Real.hasDerivAt_sin 0).neg).const_mul κ)).div_const c
  rw [h2.deriv]; simp; ring

lemma vm_ratio (κ : ℝ) : curvatureRatio (vonMises 0 κ) = -κ / 2 := by
  unfold curvatureRatio
  rw [vm_d2]
  have hI := I0_pos κ
  have hc : 0 < 2 * Real.pi * besselI 0 κ := by positivity
  rw [vm_eq]; simp only [Real.cos_zero, mul_one]
  have := Real.exp_pos κ
  field_simp

lemma vm_taylor (κ : ℝ) : (fun x => vonMises 0 κ x -
    (vonMises 0 κ 0 + iteratedDeriv 2 (vonMises 0 κ) 0 / 2 * x ^ 2)) =O[𝓝 0] fun x => x ^ 3 := by
  apply taylor3
  · rw [vm_eq]; fun_prop
  · intro x; rw [vm_eq]; simp [Real.cos_neg]

lemma erf_hd (x : ℝ) : HasDerivAt erf (2 / Real.sqrt Real.pi * Real.exp (-x ^ 2)) x := by
  unfold erf
  exact ((by fun_prop : Continuous fun t : ℝ => Real.exp (-t ^ 2)).integral_hasStrictDerivAt 0 x).hasDerivAt.const_mul _

@[fun_prop] lemma erf_diff : Differentiable ℝ erf := fun x => (erf_hd x).differentiableAt

@[fun_prop] lemma erf_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) erf := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨erf_diff, ?_⟩
  rw [show deriv erf = fun x => 2 / Real.sqrt Real.pi * Real.exp (-x ^ 2) from funext fun x => (erf_hd x).deriv]
  fun_prop

lemma erf_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ erf x := by
  unfold erf
  exact mul_nonneg (by positivity) (intervalIntegral.integral_nonneg hx (fun t _ => (Real.exp_pos _).le))

noncomputable def g (S c : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi) * S * c * Real.exp (S ^ 2 * c ^ 2 / 2) * (erf (S * c / Real.sqrt 2) + 1) + 2

lemma tp_eq (V σ : ℝ) : truePhaseDensity V σ =
    fun φ => Real.exp (-(V / σ) ^ 2 / 2) / (4 * Real.pi * σ) * g (V / σ) (Real.cos φ) := rfl

lemma g_cd (S : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g S) := by unfold g; fun_prop

lemma g_d1 (S : ℝ) : HasDerivAt (g S) (Real.sqrt (2 * Real.pi) * S * Real.exp (S ^ 2 / 2) * (1 + S ^ 2) *
    (erf (S / Real.sqrt 2) + 1) + 2 * S ^ 2) 1 := by
  have he : HasDerivAt (fun c : ℝ => Real.exp (S ^ 2 * c ^ 2 / 2))
      (Real.exp (S ^ 2 * 1 ^ 2 / 2) * (S ^ 2 * (↑2 * 1 ^ (2 - 1)) / 2)) 1 :=
    (((hasDerivAt_pow 2 (1:ℝ)).const_mul (S ^ 2)).div_const 2).exp
  have hr : HasDerivAt (fun c : ℝ => S * c / Real.sqrt 2) (S * 1 / Real.sqrt 2) 1 :=
    ((hasDerivAt_id (1:ℝ)).const_mul S).div_const _
  have hf : HasDerivAt (fun c => erf (S * c / Real.sqrt 2) + 1)
      (2 / Real.sqrt Real.pi * Real.exp (-(S * 1 / Real.sqrt 2) ^ 2) * (S * 1 / Real.sqrt 2)) 1 :=
    ((erf_hd _).comp 1 hr).add_const 1
  have h := ((((hasDerivAt_id (1:ℝ)).const_mul (Real.sqrt (2 * Real.pi) * S)).mul he).mul hf).add_const 2
  unfold g
  refine h.congr_deriv ?_
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq : (S / Real.sqrt 2) ^ 2 = S ^ 2 / 2 := by rw [div_pow, hs2]
  have hpi : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi := Real.sqrt_mul (by norm_num) _
  have hp0 : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have h20 : 0 < Real.sqrt 2 := by positivity
  simp only [Pi.mul_apply, mul_one, one_pow, id]
  rw [hsq, Real.exp_neg, hpi]
  have hE := Real.exp_pos (S ^ 2 / 2)
  field_simp

lemma tp_d2 (V σ : ℝ) : iteratedDeriv 2 (truePhaseDensity V σ) 0 =
    -(Real.exp (-(V / σ) ^ 2 / 2) / (4 * Real.pi * σ)) * deriv (g (V / σ)) 1 := by
  set S := V / σ
  set A := Real.exp (-(V / σ) ^ 2 / 2) / (4 * Real.pi * σ)
  have hgd : Differentiable ℝ (g S) := (g_cd S).differentiable (by simp)
  have hg' : Differentiable ℝ (deriv (g S)) :=
    ((contDiff_infty_iff_deriv.1 (g_cd S)).2).differentiable (by simp)
  rw [tp_eq, iteratedDeriv_succ, iteratedDeriv_one]
  rw [show deriv (fun φ => A * g S (Real.cos φ)) = fun φ => A * (deriv (g S) (Real.cos φ) * -Real.sin φ) from
    funext fun φ => (((hgd _).hasDerivAt.comp φ (Real.hasDerivAt_cos φ)).const_mul A).deriv]
  have h2 := (((hg' (Real.cos 0)).hasDerivAt.comp 0 (Real.hasDerivAt_cos 0)).mul (Real.hasDerivAt_sin 0).neg).const_mul A
  have h3 : HasDerivAt (fun φ => A * (deriv (g S) (Real.cos φ) * -Real.sin φ)) _ 0 := h2
  rw [h3.deriv]; simp

lemma tp_ratio (V σ : ℝ) (hV : 0 < V) (hσ : 0 < σ) :
    curvatureRatio (truePhaseDensity V σ) =
      (V / σ) / (2 * (Real.sqrt (2 * Real.pi) * (V / σ) * Real.exp ((V / σ) ^ 2 / 2) *
          (erf ((V / σ) / Real.sqrt 2) + 1) + 2)) *
        (Real.sqrt (2 * Real.pi) * Real.exp ((V / σ) ^ 2 / 2) * (1 + (V / σ) ^ 2) *
          (erfc ((V / σ) / Real.sqrt 2) - 2) - 2 * (V / σ)) := by
  unfold curvatureRatio
  rw [tp_d2, (g_d1 _).deriv, tp_eq]
  simp only [Real.cos_zero]
  unfold g erfc
  set S := V / σ
  have hS : 0 < S := div_pos hV hσ
  simp only [mul_one, one_pow]
  have he := erf_nonneg (S / Real.sqrt 2) (by positivity)
  have hA : 0 < Real.exp (-S ^ 2 / 2) / (4 * Real.pi * σ) := by positivity
  have hg1 : 0 < Real.sqrt (2 * Real.pi) * S * Real.exp (S ^ 2 / 2) * (erf (S / Real.sqrt 2) + 1) + 2 := by
    positivity
  field_simp
  ring

lemma tp_kappa (V σ : ℝ) (hV : 0 < V) (hσ : 0 < σ) :
    curvatureRatio (truePhaseDensity V σ) = -kappaOfSNR (V / σ) / 2 := by
  rw [tp_ratio V σ hV hσ]
  unfold kappaOfSNR erfc
  set S := V / σ
  have hS : 0 < S := div_pos hV hσ
  have he := erf_nonneg (S / Real.sqrt 2) (by positivity)
  have hg1 : 0 < Real.sqrt (2 * Real.pi) * S * Real.exp (S ^ 2 / 2) * (erf (S / Real.sqrt 2) + 1) + 2 := by
    positivity
  field_simp
  ring

lemma tp_taylor (V σ : ℝ) : (fun x => truePhaseDensity V σ x -
    (truePhaseDensity V σ 0 + iteratedDeriv 2 (truePhaseDensity V σ) 0 / 2 * x ^ 2)) =O[𝓝 0] fun x => x ^ 3 := by
  apply taylor3
  · rw [tp_eq]
    have := g_cd (V / σ)
    exact (contDiff_const.mul (this.comp Real.contDiff_cos)).of_le (WithTop.coe_le_coe.2 le_top)
  · intro x; rw [tp_eq]; simp [Real.cos_neg]

end S81MM

open Arxiv1909_04681 S81MM in
theorem solution (V σ : ℝ) (hV : 0 < V) (hσ : 0 < σ) :
    ((fun x => truePhaseDensity V σ x -
        (truePhaseDensity V σ 0 + iteratedDeriv 2 (truePhaseDensity V σ) 0 / 2 * x ^ 2))
        =O[𝓝 0] fun x => x ^ 3) ∧
    curvatureRatio (truePhaseDensity V σ) =
      (V / σ) / (2 * (Real.sqrt (2 * Real.pi) * (V / σ) * Real.exp ((V / σ) ^ 2 / 2) *
          (erf ((V / σ) / Real.sqrt 2) + 1) + 2)) *
        (Real.sqrt (2 * Real.pi) * Real.exp ((V / σ) ^ 2 / 2) * (1 + (V / σ) ^ 2) *
          (erfc ((V / σ) / Real.sqrt 2) - 2) - 2 * (V / σ)) ∧
    (∀ κ : ℝ, 0 ≤ κ →
      (fun x => vonMises 0 κ x -
          (vonMises 0 κ 0 + iteratedDeriv 2 (vonMises 0 κ) 0 / 2 * x ^ 2))
          =O[𝓝 0] fun x => x ^ 3) ∧
    (∀ κ : ℝ, 0 ≤ κ → curvatureRatio (vonMises 0 κ) = -κ / 2) ∧
    (∀ κ : ℝ, 0 ≤ κ →
      (curvatureRatio (truePhaseDensity V σ) = curvatureRatio (vonMises 0 κ) ↔
        κ = kappaOfSNR (V / σ))) := by
  refine ⟨tp_taylor V σ, tp_ratio V σ hV hσ, fun κ _ => vm_taylor κ, fun κ _ => vm_ratio κ, fun κ _ => ?_⟩
  rw [tp_kappa V σ hV hσ, vm_ratio]
  constructor <;> intro h <;> linarith
