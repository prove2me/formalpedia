-- Prove2me | Definitions.Def_sf241_second_profile
-- name    : sf241_second_profile
-- status  : Definition
-- author  : @shivm
-- created : 2026-10-05T06:23:58.80534+00:00
-- url     : https://prove2.me/theorems/2f49ead8-433f-4b5e-9fc9-c44349429863
-- title:
--   A second $H_{0,2}$ critical profile at $\kappa=4$
-- statement:
--   A second $H_{0,2}$ critical profile at $\kappa=4$.
--
--   1. `SphericalFerromagnet.SF241.two_theta_isH02CriticalProfile'`: $h(\theta)=2\theta$ is an $H_{0,2}$ critical profile for $\kappa=4$.
--   2. `SphericalFerromagnet.SF241.exists_second_profile_kappa_four'`: there is an $H_{0,2}$ critical profile $h$ for $\kappa=4$ with $h(\theta)\ne 2\theta$ for some $\theta\in[0,\pi]$.
--
--   **Construction.** The endpoint map $a\mapsto h_a(\pi/2)$ is continuous on $[3,5]$, $>\pi$ at $a=3$ and $<\pi$ at $a=5$; by the intermediate value theorem some $a\in[3,5]$ has $h_a(\pi/2)=\pi$. Reflect across the equator:
--   $$h(\theta)=2\pi-h_a(\pi-\theta)\quad(\theta>\pi/2).$$
--   Because $h_a(\pi/2)=\pi$, the reflected function is smooth and solves (2.6) on $(0,\pi)$; pole regularity gives a smooth map on $S^2$. Its slope at $0$ is $a\ge3\ne2$, so $h\ne2\theta$.
-- source:
--   S. Gustafson, D. Meinert, C. Melcher, Saddle Point Configurations for Spherical Ferromagnets, arXiv:2509.05159v2, https://arxiv.org/abs/2509.05159, eq. (2.6), Definition 3.1, Remark 3.18; AIM open problems list, problem 241 (https://github.com/MColbrook/AIM). Supporting proof infrastructure for the disproof of SphericalFerromagnet.hemispheric_profile_unique.

import Mathlib
import Definitions.Def_spherical_ferromagnet_shooting_defs
import Definitions.Def_sf241_shoot_family
import Definitions.Def_sf241_shoot_bounds

/-!
# A second `H_{0,2}` critical profile at `κ = 4`

1. `2θ` is an `H_{0,2}` critical profile for `κ = 4` (`two_theta_isH02CriticalProfile'`).
2. Shooting from the north pole: the endpoint map `a ↦ h_a(π/2)` is continuous on `[3, 5]`,
   `> π` at `a = 3` and `< π` at `a = 5`; by the intermediate value theorem some slope
   `a ∈ [3, 5]` gives `h_a(π/2) = π`.
3. Reflecting this shot across the equator, `h(θ) = 2π - h(π - θ)` for `θ > π/2`, gives a
   smooth `H_{0,2}` critical profile. Its slope at `0` is `a ≥ 3 ≠ 2`, so it differs from `2θ`
   (`exists_second_profile_kappa_four'`).
-/

open scoped ContDiff
open Real Set

namespace SphericalFerromagnet.SF241

/-- The ODE identity: `2 cot θ - sin 4θ / (2 sin² θ) - 2 sin 2θ = 0`. -/
theorem two_theta_solves_profile_eq : SolvesProfileEq 4 (fun θ => 2 * θ) := by
  intro θ hθ
  have hs : Real.sin θ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).ne'
  have hd : deriv (fun θ : ℝ => 2 * θ) = fun _ => 2 := by
    funext t
    exact ((hasDerivAt_id t).const_mul (2 : ℝ)).deriv.trans (by simp)
  unfold profileOperator
  rw [hd]
  simp only [deriv_const', zero_add]
  have h4 : (2 : ℝ) * (2 * θ) = 2 * (2 * θ) := rfl
  have e1 : Real.sin (2 * (2 * θ)) = 2 * (2 * Real.sin θ * Real.cos θ) *
      (1 - 2 * Real.sin θ ^ 2) := by
    rw [Real.sin_two_mul, Real.sin_two_mul, Real.cos_two_mul, Real.cos_sq']
    ring
  have e2 : (2 : ℝ) * (2 * θ) - 2 * θ = 2 * θ := by ring
  rw [e1, e2, Real.sin_two_mul]
  field_simp
  ring

/-- Explicit polynomial-over-`|x|²` form of the field induced by `h = 2θ`. -/
noncomputable def twoThetaField (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![2 * x 0 * x 2 / (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2),
    2 * x 1 * x 2 / (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2),
    2 * x 2 ^ 2 / (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) - 1]

lemma normSq_ne_zero {x : Fin 3 → ℝ} (hx : x ≠ 0) : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 ≠ 0 := by
  intro hS
  apply hx
  have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  have h1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  have h2 : x 2 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  funext i
  fin_cases i <;> simp [h0, h1, h2]

lemma twoThetaField_contDiffOn :
    ContDiffOn ℝ ∞ twoThetaField {x : Fin 3 → ℝ | x ≠ 0} := by
  have hS : ContDiff ℝ ∞ (fun x : Fin 3 → ℝ => x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) := by fun_prop
  have hne : ∀ x ∈ {x : Fin 3 → ℝ | x ≠ 0}, x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 ≠ 0 :=
    fun x hx => normSq_ne_zero hx
  rw [contDiffOn_pi]
  intro i
  fin_cases i
  · simp only [twoThetaField]
    exact (ContDiff.contDiffOn (by fun_prop)).div hS.contDiffOn hne
  · simp only [twoThetaField]
    exact (ContDiff.contDiffOn (by fun_prop)).div hS.contDiffOn hne
  · simp only [twoThetaField]
    exact ((ContDiff.contDiffOn (by fun_prop)).div hS.contDiffOn hne).sub contDiffOn_const

lemma inducedField_two_theta {x : Fin 3 → ℝ} (hx : x ≠ 0) :
    inducedField (fun θ => 2 * θ) x = twoThetaField x := by
  set S := x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 with hSdef
  have hS : S ≠ 0 := normSq_ne_zero hx
  have hSpos : 0 < S := lt_of_le_of_ne (by positivity) (Ne.symm hS)
  set ρ := Real.sqrt S with hρ
  have hρpos : 0 < ρ := Real.sqrt_pos.mpr hSpos
  have hρsq : ρ ^ 2 = S := Real.sq_sqrt hSpos.le
  set t := x 2 / ρ with ht
  have ht2 : t ^ 2 = x 2 ^ 2 / S := by rw [ht, div_pow, hρsq]
  have htle : t ^ 2 ≤ 1 := by
    rw [ht2, div_le_one hSpos]; nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  have htm : -1 ≤ t := by nlinarith [sq_nonneg (t + 1)]
  have htM : t ≤ 1 := by nlinarith [sq_nonneg (t - 1)]
  have hcos : Real.cos (2 * Real.arccos t) = 2 * x 2 ^ 2 / S - 1 := by
    rw [Real.cos_two_mul, Real.cos_arccos htm htM, ht2]; ring
  set r := Real.sqrt (x 0 ^ 2 + x 1 ^ 2) with hr
  unfold inducedField
  simp only []
  rw [← hSdef, ← hρ, ← ht, ← hr]
  by_cases hr0 : r = 0
  · rw [if_pos hr0]
    have hq : x 0 ^ 2 + x 1 ^ 2 = 0 := by
      have := Real.sqrt_eq_zero'.mp hr0
      linarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    have h1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    have hS' : S = x 2 ^ 2 := by rw [hSdef, h0, h1]; ring
    funext i
    fin_cases i <;> simp [twoThetaField, h0, h1, hcos, hS']
  · rw [if_neg hr0]
    have hrpos : 0 < r := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr0)
    have hsin : Real.sin (Real.arccos t) = r / ρ := by
      rw [Real.sin_arccos]
      have : 1 - t ^ 2 = (x 0 ^ 2 + x 1 ^ 2) / S := by
        rw [ht2]; field_simp; rw [hSdef]; ring
      rw [this, Real.sqrt_div' _ hSpos.le]
    have hsin2 : Real.sin (2 * Real.arccos t) = 2 * (r / ρ) * t := by
      rw [Real.sin_two_mul, hsin, Real.cos_arccos htm htM]
    funext i
    fin_cases i
    · simp only [twoThetaField, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [hsin2, ← hSdef, ← hρsq, ht]; field_simp
    · simp only [twoThetaField, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_zero]
      rw [hsin2, ← hSdef, ← hρsq, ht]; field_simp
    · simp [twoThetaField, hcos, ← hSdef]

theorem two_theta_inducesSmoothMap : InducesSmoothMap (fun θ => 2 * θ) := by
  unfold InducesSmoothMap
  exact twoThetaField_contDiffOn.congr (fun x hx => inducedField_two_theta hx)

theorem two_theta_isH02CriticalProfile' : IsH02CriticalProfile 4 (fun θ => 2 * θ) := by
  refine ⟨?_, two_theta_inducesSmoothMap, two_theta_solves_profile_eq, by simp, by ring, ?_⟩
  · exact (contDiff_const.mul contDiff_id).contDiffOn
  · intro θ _; ring

end SphericalFerromagnet.SF241

namespace SphericalFerromagnet.SF241


section
open scoped ContDiff
open Real Set

theorem inducesSmoothMap_of_repr (h A B : ℝ → ℝ)
    (hA : ContDiffOn ℝ ∞ A (Icc (-1) 1)) (hB : ContDiffOn ℝ ∞ B (Icc (-1) 1))
    (hrep : ∀ θ ∈ Icc (0 : ℝ) π,
      Real.cos (h θ) = A (Real.cos θ) ∧ Real.sin (h θ) = B (Real.cos θ) * Real.sin θ) :
    InducesSmoothMap h := by
  set U := {x : Fin 3 → ℝ | x ≠ 0} with hU
  let ρ : (Fin 3 → ℝ) → ℝ := fun x => Real.sqrt (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2)
  let T : (Fin 3 → ℝ) → ℝ := fun x => x 2 / ρ x
  have hρne : ∀ x ∈ U, ρ x ≠ 0 := by
    intro x hx
    have hS := normSq_ne_zero hx
    have hSpos : 0 < x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hS)
    exact (Real.sqrt_pos.mpr hSpos).ne'
  have hρ : ContDiffOn ℝ ∞ ρ U :=
    (ContDiff.contDiffOn (by fun_prop)).sqrt (fun x hx => normSq_ne_zero hx)
  have hT : ContDiffOn ℝ ∞ T U := (ContDiff.contDiffOn (by fun_prop)).div hρ hρne
  have hTmem : ∀ x ∈ U, T x ∈ Icc (-1 : ℝ) 1 := by
    intro x hx
    have hS := normSq_ne_zero hx
    have hSpos : 0 < x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hS)
    have hρpos : 0 < ρ x := Real.sqrt_pos.mpr hSpos
    have hρsq : ρ x ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := Real.sq_sqrt hSpos.le
    have h2 : (T x) ^ 2 ≤ 1 := by
      simp only [T]
      rw [div_pow, hρsq, div_le_one hSpos]; nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    exact ⟨by nlinarith [sq_nonneg (T x + 1)], by nlinarith [sq_nonneg (T x - 1)]⟩
  have hmaps : MapsTo T U (Icc (-1) 1) := fun x hx => hTmem x hx
  have hAT : ContDiffOn ℝ ∞ (fun x => A (T x)) U := hA.comp hT hmaps
  have hBT : ContDiffOn ℝ ∞ (fun x => B (T x)) U := hB.comp hT hmaps
  set F : (Fin 3 → ℝ) → Fin 3 → ℝ :=
    fun x => ![B (T x) * (x 0 / ρ x), B (T x) * (x 1 / ρ x), A (T x)] with hFdef
  have hF : ContDiffOn ℝ ∞ F U := by
    rw [contDiffOn_pi]
    intro i
    fin_cases i
    · exact hBT.mul ((ContDiff.contDiffOn (by fun_prop)).div hρ hρne)
    · exact hBT.mul ((ContDiff.contDiffOn (by fun_prop)).div hρ hρne)
    · exact hAT
  refine hF.congr ?_
  intro x hx
  have hS := normSq_ne_zero hx
  have hSpos : 0 < x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hS)
  have hρpos : 0 < ρ x := Real.sqrt_pos.mpr hSpos
  have hρsq : ρ x ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := Real.sq_sqrt hSpos.le
  obtain ⟨htm, htM⟩ := hTmem x hx
  set t := T x with ht
  have hθ : Real.arccos t ∈ Icc (0 : ℝ) π := ⟨Real.arccos_nonneg t, Real.arccos_le_pi t⟩
  obtain ⟨hcos, hsin⟩ := hrep _ hθ
  rw [Real.cos_arccos htm htM] at hcos hsin
  set r := Real.sqrt (x 0 ^ 2 + x 1 ^ 2) with hr
  have hsinθ : Real.sin (Real.arccos t) = r / ρ x := by
    rw [Real.sin_arccos]
    have : 1 - t ^ 2 = (x 0 ^ 2 + x 1 ^ 2) / (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) := by
      simp only [ht, T]; rw [div_pow, hρsq]; field_simp; ring
    rw [this, Real.sqrt_div' _ hSpos.le]
  unfold inducedField
  simp only []
  by_cases hr0 : Real.sqrt (x 0 ^ 2 + x 1 ^ 2) = 0
  · rw [if_pos hr0]
    have hq : x 0 ^ 2 + x 1 ^ 2 = 0 := by
      have := Real.sqrt_eq_zero'.mp hr0
      linarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    have h1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    funext i
    fin_cases i
    · simp [hFdef, h0]
    · simp [hFdef, h1]
    · simp only [hFdef, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
      exact hcos
  · rw [if_neg hr0]
    have hrpos : 0 < r := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr0)
    funext i
    fin_cases i
    · simp only [hFdef, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      change Real.sin (h (Real.arccos t)) * (x 0 / r) = _
      rw [hsin, hsinθ, ← ht]; field_simp
    · simp only [hFdef, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      change Real.sin (h (Real.arccos t)) * (x 1 / r) = _
      rw [hsin, hsinθ, ← ht]; field_simp
    · simp only [hFdef, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
      exact hcos

end

section
open scoped ContDiff
open Real Set

theorem inducesSmoothMap_of_north_pole_repr (G : ℝ → ℝ) (hG : ContDiffOn ℝ ∞ G (Ioo 0 π))
    (hsym : ∀ θ ∈ Icc (0 : ℝ) π, G (π - θ) = 2 * π - G θ)
    (δ : ℝ) (hδ : 0 < δ) (hδπ : δ < π) (A₁ B₁ : ℝ → ℝ)
    (hA₁ : ContDiffOn ℝ ∞ A₁ (Icc (Real.cos δ) 1)) (hB₁ : ContDiffOn ℝ ∞ B₁ (Icc (Real.cos δ) 1))
    (hrep : ∀ θ ∈ Icc (0 : ℝ) δ,
      Real.cos (G θ) = A₁ (Real.cos θ) ∧ Real.sin (G θ) = B₁ (Real.cos θ) * Real.sin θ) :
    InducesSmoothMap G := by
  have hpi := Real.pi_pos
  have hc1 : Real.cos δ < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hδπ.le hδ; rwa [Real.cos_zero] at this
  have hcm1 : -1 < Real.cos δ := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi hδ.le le_rfl hδπ; rwa [Real.cos_pi] at this
  -- arccos facts
  have hacI : ∀ t ∈ Icc (Real.cos δ) 1, Real.arccos t ∈ Icc (0 : ℝ) δ := by
    intro t ht
    refine ⟨Real.arccos_nonneg t, ?_⟩
    calc Real.arccos t ≤ Real.arccos (Real.cos δ) := Real.arccos_le_arccos ht.1
      _ = δ := Real.arccos_cos hδ.le hδπ.le
  have hacS : ∀ t, Real.arccos t = π - Real.arccos (-t) := by
    intro t; rw [Real.arccos_neg]; ring
  -- the symmetry on cos / sin
  have hsymc : ∀ φ ∈ Icc (0 : ℝ) π, Real.cos (G (π - φ)) = Real.cos (G φ) := by
    intro φ hφ; rw [hsym φ hφ, Real.cos_two_pi_sub]
  have hsyms : ∀ φ ∈ Icc (0 : ℝ) π, Real.sin (G (π - φ)) = -Real.sin (G φ) := by
    intro φ hφ; rw [hsym φ hφ, Real.sin_two_pi_sub]
  have hδI : ∀ φ ∈ Icc (0 : ℝ) δ, φ ∈ Icc (0 : ℝ) π := fun φ hφ => ⟨hφ.1, hφ.2.trans hδπ.le⟩
  -- interior smoothness of G ∘ arccos
  have hacC : ContDiffOn ℝ ∞ Real.arccos (Ioo (-1) 1) := fun t ht =>
    (Real.contDiffAt_arccos (ne_of_gt ht.1) (ne_of_lt ht.2)).contDiffWithinAt
  have hacM : MapsTo Real.arccos (Ioo (-1) 1) (Ioo 0 π) := fun t ht =>
    ⟨Real.arccos_pos.mpr ht.2, Real.arccos_lt_pi.mpr ht.1⟩
  have hGac : ContDiffOn ℝ ∞ (fun t => G (Real.arccos t)) (Ioo (-1) 1) := hG.comp hacC hacM
  have hsq : ∀ t ∈ Ioo (-1 : ℝ) 1, Real.sqrt (1 - t ^ 2) ≠ 0 := by
    intro t ht
    have : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    exact (Real.sqrt_pos.mpr this).ne'
  -- the global functions
  set A : ℝ → ℝ := fun t => Real.cos (G (Real.arccos t)) with hAdef
  set B : ℝ → ℝ := fun t => if t = 1 then B₁ 1 else if t = -1 then -B₁ 1 else
    Real.sin (G (Real.arccos t)) / Real.sqrt (1 - t ^ 2) with hBdef
  -- local identities
  have hAN : ∀ t ∈ Icc (Real.cos δ) 1, A t = A₁ t := by
    intro t ht
    simp only [hAdef]
    rw [(hrep _ (hacI t ht)).1, Real.cos_arccos (by linarith [ht.1]) ht.2]
  have hAS : ∀ t ∈ Icc (-1 : ℝ) (-Real.cos δ), A t = A₁ (-t) := by
    intro t ht
    have ht' : -t ∈ Icc (Real.cos δ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simp only [hAdef]
    rw [hacS t, hsymc _ (hδI _ (hacI _ ht')), (hrep _ (hacI _ ht')).1,
      Real.cos_arccos (by linarith [ht'.1]) ht'.2]
  have hBN : ∀ t ∈ Icc (Real.cos δ) 1, B t = B₁ t := by
    intro t ht
    simp only [hBdef]
    by_cases h1 : t = 1
    · rw [if_pos h1, h1]
    · have hm1 : t ≠ -1 := by intro h; rw [h] at ht; linarith [ht.1]
      rw [if_neg h1, if_neg hm1, (hrep _ (hacI t ht)).2,
        Real.cos_arccos (by linarith [ht.1]) ht.2, Real.sin_arccos]
      have hne := hsq t ⟨by linarith [ht.1], lt_of_le_of_ne ht.2 h1⟩
      field_simp
  have hBS : ∀ t ∈ Icc (-1 : ℝ) (-Real.cos δ), B t = -B₁ (-t) := by
    intro t ht
    have ht' : -t ∈ Icc (Real.cos δ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simp only [hBdef]
    have h1 : t ≠ 1 := by intro h; rw [h] at ht; linarith [ht.2]
    rw [if_neg h1]
    by_cases hm1 : t = -1
    · rw [if_pos hm1, hm1, neg_neg]
    · rw [if_neg hm1, hacS t, hsyms _ (hδI _ (hacI _ ht')), (hrep _ (hacI _ ht')).2,
        Real.cos_arccos (by linarith [ht'.1]) ht'.2, Real.sin_arccos]
      have hne := hsq t ⟨lt_of_le_of_ne ht.1 (Ne.symm hm1), by linarith [ht.2]⟩
      rw [show (-t) ^ 2 = t ^ 2 by ring]
      field_simp
  have hBI : ∀ t ∈ Ioo (-1 : ℝ) 1, B t = Real.sin (G (Real.arccos t)) / Real.sqrt (1 - t ^ 2) := by
    intro t ht
    simp only [hBdef]
    rw [if_neg (ne_of_lt ht.2), if_neg (ne_of_gt ht.1)]
  have hnegM : MapsTo (fun t : ℝ => -t) (Icc (-1) 1 ∩ Iio (-Real.cos δ)) (Icc (Real.cos δ) 1) := by
    intro t ht
    simp only [mem_inter_iff, mem_Icc, mem_Iio] at ht
    exact ⟨by linarith, by linarith⟩
  have hsubN : Icc (-1) 1 ∩ Ioi (Real.cos δ) ⊆ Icc (Real.cos δ) 1 :=
    fun t ht => ⟨le_of_lt ht.2, ht.1.2⟩
  have hsubS : Icc (-1) 1 ∩ Iio (-Real.cos δ) ⊆ Icc (-1) (-Real.cos δ) :=
    fun t ht => ⟨ht.1.1, le_of_lt ht.2⟩
  have hsubI : Icc (-1 : ℝ) 1 ∩ Ioo (-1) 1 ⊆ Ioo (-1) 1 := inter_subset_right
  -- smoothness of A and B
  have hA : ContDiffOn ℝ ∞ A (Icc (-1) 1) := by
    apply contDiffOn_of_locally_contDiffOn
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · refine ⟨Ioi (Real.cos δ), isOpen_Ioi, by rw [h1]; exact hc1, ?_⟩
      exact (hA₁.mono hsubN).congr (fun s hs => hAN s (hsubN hs))
    rcases eq_or_lt_of_le ht.1 with h2 | h2
    · refine ⟨Iio (-Real.cos δ), isOpen_Iio, by rw [← h2]; simp only [mem_Iio]; linarith, ?_⟩
      exact (hA₁.comp contDiffOn_id.neg hnegM).congr (fun s hs => hAS s (hsubS hs))
    · refine ⟨Ioo (-1) 1, isOpen_Ioo, ⟨h2, h1⟩, ?_⟩
      exact (contDiff_cos.comp_contDiffOn hGac).mono hsubI
  have hB : ContDiffOn ℝ ∞ B (Icc (-1) 1) := by
    apply contDiffOn_of_locally_contDiffOn
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · refine ⟨Ioi (Real.cos δ), isOpen_Ioi, by rw [h1]; exact hc1, ?_⟩
      exact (hB₁.mono hsubN).congr (fun s hs => hBN s (hsubN hs))
    rcases eq_or_lt_of_le ht.1 with h2 | h2
    · refine ⟨Iio (-Real.cos δ), isOpen_Iio, by rw [← h2]; simp only [mem_Iio]; linarith, ?_⟩
      exact (hB₁.comp contDiffOn_id.neg hnegM).neg.congr (fun s hs => hBS s (hsubS hs))
    · refine ⟨Ioo (-1) 1, isOpen_Ioo, ⟨h2, h1⟩, ?_⟩
      have hden : ContDiffOn ℝ ∞ (fun t : ℝ => Real.sqrt (1 - t ^ 2)) (Ioo (-1) 1) :=
        (ContDiff.contDiffOn (by fun_prop)).sqrt (fun t ht => by nlinarith [ht.1, ht.2])
      have hnum : ContDiffOn ℝ ∞ (fun t => Real.sin (G (Real.arccos t))) (Ioo (-1) 1) :=
        contDiff_sin.comp_contDiffOn hGac
      exact ((hnum.div hden hsq).mono hsubI).congr (fun s hs => hBI s (hsubI hs))
  -- the representation on [0, π]
  refine inducesSmoothMap_of_repr G A B hA hB ?_
  intro θ hθ
  constructor
  · simp only [hAdef]; rw [Real.arccos_cos hθ.1 hθ.2]
  · rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      have := (hrep 0 ⟨le_rfl, hδ.le⟩).2
      rw [Real.sin_zero, mul_zero] at this
      rw [this, Real.sin_zero, mul_zero]
    rcases eq_or_lt_of_le hθ.2 with hπ | hπ
    · subst hπ
      have h0' := (hrep 0 ⟨le_rfl, hδ.le⟩).2
      rw [Real.sin_zero, mul_zero] at h0'
      have := hsyms 0 ⟨le_rfl, hpi.le⟩
      rw [sub_zero, h0', neg_zero] at this
      rw [this, Real.sin_pi, mul_zero]
    · have hc1' : Real.cos θ < 1 := by
        have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθ.2 h0; rwa [Real.cos_zero] at this
      have hcm1' : -1 < Real.cos θ := by
        have := Real.cos_lt_cos_of_nonneg_of_le_pi hθ.1 le_rfl hπ; rwa [Real.cos_pi] at this
      have hsθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 hπ
      rw [hBI _ ⟨hcm1', hc1'⟩, Real.arccos_cos hθ.1 hθ.2]
      have : Real.sqrt (1 - Real.cos θ ^ 2) = Real.sin θ := by
        rw [← Real.sin_sq, Real.sqrt_sq hsθ.le]
      rw [this]; field_simp

end

section
open scoped ContDiff Topology
open Real Set Filter

/-- Gluing a function on `[0, π/2]` with an affine reflection of itself. -/
lemma glue_hasDerivAt {c σ : ℝ} {f f' : ℝ → ℝ}
    (hf : ∀ θ ∈ Icc 0 (π / 2), HasDerivWithinAt f (f' θ) (Icc 0 (π / 2)) θ)
    (hval : f (π / 2) = c + σ * f (π / 2)) (hder : f' (π / 2) = -σ * f' (π / 2)) :
    ∀ θ ∈ Ioo 0 π, HasDerivAt (fun θ => if θ ≤ π / 2 then f θ else c + σ * f (π - θ))
      (if θ ≤ π / 2 then f' θ else -σ * f' (π - θ)) θ := by
  have hp : 0 < π / 2 := by positivity
  have hpp : π - π / 2 = π / 2 := by ring
  intro θ hθ
  rcases lt_trichotomy θ (π / 2) with hlt | heq | hgt
  · have hI : Icc 0 (π / 2) ∈ 𝓝 θ := Icc_mem_nhds hθ.1 hlt
    have h1 : HasDerivAt f (f' θ) θ := (hf θ ⟨hθ.1.le, hlt.le⟩).hasDerivAt hI
    rw [if_pos hlt.le]
    apply h1.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hlt] with t ht
    rw [if_pos (le_of_lt ht)]
  · subst heq
    rw [if_pos le_rfl]
    have hL : HasDerivWithinAt f (f' (π / 2)) (Iic (π / 2)) (π / 2) :=
      (hf _ ⟨hp.le, le_rfl⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE hp)
    have hm : HasDerivWithinAt (fun t : ℝ => π - t) (-1) (Ici (π / 2)) (π / 2) :=
      ((hasDerivAt_id' (π / 2)).const_sub π).hasDerivWithinAt
    have hL' : HasDerivWithinAt f (f' (π / 2)) (Iic (π / 2)) (π - π / 2) := by
      rw [hpp]; exact hL
    have hR0 : HasDerivWithinAt (fun t => f (π - t)) (f' (π / 2) * (-1)) (Ici (π / 2))
        (π / 2) :=
      hL'.comp (π / 2) hm (fun t ht => by simp only [mem_Iic, mem_Ici] at ht ⊢; linarith)
    have hR : HasDerivWithinAt (fun t => c + σ * f (π - t)) (f' (π / 2)) (Ici (π / 2))
        (π / 2) := by
      exact ((hR0.const_mul σ).const_add c).congr_deriv (by linear_combination -hder)
    have hU := (hL.congr (f₁ := fun θ => if θ ≤ π / 2 then f θ else c + σ * f (π - θ))
      (fun t ht => if_pos ht) (if_pos le_rfl)).union
      (hR.congr (f₁ := fun θ => if θ ≤ π / 2 then f θ else c + σ * f (π - θ))
        (fun t ht => by
          by_cases h : t ≤ π / 2
          · have : t = π / 2 := le_antisymm h ht
            subst this
            rw [if_pos h, hpp]; exact hval
          · rw [if_neg h])
        (by rw [if_pos le_rfl, hpp]; exact hval))
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at hU
  · have hφ : π - θ ∈ Ioo 0 (π / 2) := ⟨by linarith [hθ.2], by linarith⟩
    have hI : Icc 0 (π / 2) ∈ 𝓝 (π - θ) := Icc_mem_nhds hφ.1 hφ.2
    have h1 : HasDerivAt f (f' (π - θ)) (π - θ) := (hf _ ⟨hφ.1.le, hφ.2.le⟩).hasDerivAt hI
    have h2 : HasDerivAt (fun t => f (π - t)) (f' (π - θ) * (-1)) θ :=
      h1.comp θ ((hasDerivAt_id' θ).const_sub π)
    have h3 := (h2.const_mul σ).const_add c
    rw [if_neg (not_le.mpr hgt)]
    have h4 : HasDerivAt (fun t => c + σ * f (π - t)) (-σ * f' (π - θ)) θ := by
      exact h3.congr_deriv (by ring)
    apply h4.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hgt] with t ht
    rw [if_neg (not_le.mpr ht)]

/-- The right-hand side of the profile equation solved for `h''`. -/
noncomputable def profileRHS (κ θ u p : ℝ) : ℝ :=
  -(Real.cos θ / Real.sin θ) * p + Real.sin (2 * u) / (2 * Real.sin θ ^ 2)
    + κ / 2 * Real.sin (2 * u - 2 * θ)

/-- Bootstrap: a `C²` solution of `G'' = F(θ, G, G')` on `(0, π)` is `C^∞` there. -/
lemma bootstrap_smooth (κ : ℝ) {G G1 : ℝ → ℝ}
    (hG : ∀ θ ∈ Ioo 0 π, HasDerivAt G (G1 θ) θ)
    (hG1 : ∀ θ ∈ Ioo 0 π, HasDerivAt G1 (profileRHS κ θ (G θ) (G1 θ)) θ) :
    ContDiffOn ℝ ∞ G (Ioo 0 π) := by
  have hU : IsOpen (Ioo (0 : ℝ) π) := isOpen_Ioo
  have hsin : ∀ θ ∈ Ioo (0 : ℝ) π, Real.sin θ ≠ 0 :=
    fun θ hθ => (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).ne'
  have hdG : ∀ θ ∈ Ioo (0 : ℝ) π, deriv G θ = G1 θ := fun θ hθ => (hG θ hθ).deriv
  have hdG1 : ∀ θ ∈ Ioo (0 : ℝ) π, deriv G1 θ = profileRHS κ θ (G θ) (G1 θ) :=
    fun θ hθ => (hG1 θ hθ).deriv
  have key : ∀ n : ℕ, ContDiffOn ℝ n G (Ioo 0 π) ∧ ContDiffOn ℝ n G1 (Ioo 0 π) := by
    intro n
    induction n with
    | zero =>
      simp only [Nat.cast_zero, contDiffOn_zero]
      exact ⟨fun θ hθ => (hG θ hθ).continuousAt.continuousWithinAt,
        fun θ hθ => (hG1 θ hθ).continuousAt.continuousWithinAt⟩
    | succ n ih =>
      obtain ⟨ihG, ihG1⟩ := ih
      have hR : ContDiffOn ℝ n (fun θ => profileRHS κ θ (G θ) (G1 θ)) (Ioo 0 π) := by
        unfold profileRHS
        have hs2 : ∀ θ ∈ Ioo (0 : ℝ) π, 2 * Real.sin θ ^ 2 ≠ 0 :=
          fun θ hθ => by have := hsin θ hθ; positivity
        refine ContDiffOn.add (ContDiffOn.add ?_ ?_) ?_
        · exact ((contDiff_cos.contDiffOn.div contDiff_sin.contDiffOn hsin).neg).mul ihG1
        · exact ((contDiff_sin.comp_contDiffOn (contDiffOn_const.mul ihG)).div
            (contDiffOn_const.mul (contDiff_sin.contDiffOn.pow 2)) hs2)
        · exact contDiffOn_const.mul (contDiff_sin.comp_contDiffOn
            ((contDiffOn_const.mul ihG).sub (contDiffOn_const.mul contDiffOn_id)))
      have hdiffG : DifferentiableOn ℝ G (Ioo 0 π) :=
        fun θ hθ => (hG θ hθ).differentiableAt.differentiableWithinAt
      have hdiffG1 : DifferentiableOn ℝ G1 (Ioo 0 π) :=
        fun θ hθ => (hG1 θ hθ).differentiableAt.differentiableWithinAt
      have e : ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 := by push_cast; rfl
      rw [e, contDiffOn_succ_iff_deriv_of_isOpen hU, contDiffOn_succ_iff_deriv_of_isOpen hU]
      refine ⟨⟨hdiffG, fun h => by exact absurd h (by simp), ihG1.congr hdG⟩,
        ⟨hdiffG1, fun h => by exact absurd h (by simp), hR.congr hdG1⟩⟩
  exact contDiffOn_infty.mpr (fun n => (key n).1)

lemma sin_two_mul_two_pi_sub (x : ℝ) : Real.sin (2 * (2 * π - x)) = -Real.sin (2 * x) := by
  rw [show 2 * (2 * π - x) = -(2 * x) + ((2 : ℕ) : ℝ) * (2 * π) by push_cast; ring,
    Real.sin_add_nat_mul_two_pi, Real.sin_neg]

lemma sin_refl_aux (x φ : ℝ) :
    Real.sin (2 * (2 * π - x) - 2 * (π - φ)) = -Real.sin (2 * x - 2 * φ) := by
  rw [show 2 * (2 * π - x) - 2 * (π - φ) = -(2 * x - 2 * φ) + ((1 : ℕ) : ℝ) * (2 * π) by
    push_cast; ring, Real.sin_add_nat_mul_two_pi, Real.sin_neg]

/-- (L2b) Reflection about the equator: a solution on `[0, π/2]` through `(π/2, π)` extends,
by `h(π - θ) = 2π - h(θ)`, to a smooth solution on `[0, π]`.
(Same statement as the draft lemma of the proposal.) -/
theorem hemispheric_extension (κ : ℝ) (h : ℝ → ℝ)
    (hs : ContDiffOn ℝ ∞ h (Set.Icc 0 (Real.pi / 2)))
    (hmid : h (Real.pi / 2) = Real.pi)
    (hode : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), profileOperator κ h θ = 0) :
    ContDiffOn ℝ ∞ (fun θ => if θ ≤ Real.pi / 2 then h θ else 2 * Real.pi - h (Real.pi - θ))
        (Set.Icc 0 Real.pi) ∧
      SolvesProfileEq κ
        (fun θ => if θ ≤ Real.pi / 2 then h θ else 2 * Real.pi - h (Real.pi - θ)) := by
  set I := Icc (0 : ℝ) (π / 2) with hIdef
  have hp : 0 < π / 2 := by positivity
  have hpπ : π / 2 < π := by linarith [Real.pi_pos]
  have hUI : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hp
  set d1 := derivWithin h I with hd1def
  set d2 := derivWithin d1 I with hd2def
  have hs1 : ContDiffOn ℝ ∞ d1 I := hs.derivWithin hUI (by simp)
  have hs2 : ContDiffOn ℝ ∞ d2 I := hs1.derivWithin hUI (by simp)
  have hd1 : ∀ θ ∈ I, HasDerivWithinAt h (d1 θ) I θ :=
    fun θ hθ => ((hs.differentiableOn (by simp)) θ hθ).hasDerivWithinAt
  have hd2 : ∀ θ ∈ I, HasDerivWithinAt d1 (d2 θ) I θ :=
    fun θ hθ => ((hs1.differentiableOn (by simp)) θ hθ).hasDerivWithinAt
  -- the ODE in terms of d1, d2 on (0, π/2]
  set E : ℝ → ℝ := fun θ => d2 θ + Real.cos θ / Real.sin θ * d1 θ
    - Real.sin (2 * h θ) / (2 * Real.sin θ ^ 2) - κ / 2 * Real.sin (2 * h θ - 2 * θ) with hEdef
  have hEoo : EqOn E (fun _ => 0) (Ioo 0 (π / 2)) := by
    intro θ hθ
    have hI : I ∈ 𝓝 θ := Icc_mem_nhds hθ.1 hθ.2
    have e1 : deriv h θ = d1 θ := ((hd1 θ (Ioo_subset_Icc_self hθ)).hasDerivAt hI).deriv
    have e2 : deriv (deriv h) θ = d2 θ := by
      have hev : deriv h =ᶠ[𝓝 θ] d1 := by
        filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with t ht
        exact ((hd1 t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).deriv
      rw [hev.deriv_eq]
      exact ((hd2 θ (Ioo_subset_Icc_self hθ)).hasDerivAt hI).deriv
    have := hode θ hθ
    unfold profileOperator at this
    rw [e1, e2] at this
    simpa [hEdef] using this
  have hsinI : ∀ θ ∈ Ioc (0 : ℝ) (π / 2), Real.sin θ ≠ 0 :=
    fun θ hθ => (Real.sin_pos_of_pos_of_lt_pi hθ.1 (lt_of_le_of_lt hθ.2 hpπ)).ne'
  have hEcont : ContinuousOn E (Ioc 0 (π / 2)) := by
    have hsub : Ioc (0 : ℝ) (π / 2) ⊆ I := Ioc_subset_Icc_self
    have ch := hs.continuousOn.mono hsub
    have c1 := hs1.continuousOn.mono hsub
    have c2 := hs2.continuousOn.mono hsub
    have hs2' : ∀ θ ∈ Ioc (0 : ℝ) (π / 2), 2 * Real.sin θ ^ 2 ≠ 0 :=
      fun θ hθ => by have := hsinI θ hθ; positivity
    refine ((c2.add ((continuousOn_cos.div continuousOn_sin hsinI).mul c1)).sub ?_).sub ?_
    · exact (continuousOn_sin.comp (continuousOn_const.mul ch) (mapsTo_univ _ _)).div
        (continuousOn_const.mul (continuousOn_sin.pow 2)) hs2'
    · exact continuousOn_const.mul (continuousOn_sin.comp
        ((continuousOn_const.mul ch).sub (continuousOn_const.mul continuousOn_id))
        (mapsTo_univ _ _))
  have hE : EqOn E (fun _ => 0) (Ioc 0 (π / 2)) := by
    refine hEoo.of_subset_closure hEcont continuousOn_const Ioo_subset_Ioc_self ?_
    rw [closure_Ioo hp.ne]; exact Ioc_subset_Icc_self
  have hd2p : d2 (π / 2) = 0 := by
    have := hE ⟨hp, le_rfl⟩
    simp only [hEdef, Real.cos_pi_div_two, Real.sin_pi_div_two, hmid] at this
    have e3 : Real.sin (2 * π) = 0 := Real.sin_two_pi
    have e4 : Real.sin (2 * π - 2 * (π / 2)) = 0 := by
      rw [show 2 * π - 2 * (π / 2) = π by ring]; exact Real.sin_pi
    rw [e3, e4] at this
    linarith
  -- glued function and its derivatives
  set G : ℝ → ℝ := fun θ => if θ ≤ π / 2 then h θ else 2 * π - h (π - θ) with hGdef
  set G1 : ℝ → ℝ := fun θ => if θ ≤ π / 2 then d1 θ else d1 (π - θ) with hG1def
  set G2 : ℝ → ℝ := fun θ => if θ ≤ π / 2 then d2 θ else -d2 (π - θ) with hG2def
  have hGd : ∀ θ ∈ Ioo 0 π, HasDerivAt G (G1 θ) θ := by
    intro θ hθ
    have := glue_hasDerivAt (c := 2 * π) (σ := -1) hd1 (by rw [hmid]; ring) (by ring) θ hθ
    have eF : (fun t => if t ≤ π / 2 then h t else 2 * π + -1 * h (π - t)) = G := by
      funext t; simp only [hGdef]; split_ifs <;> ring
    have eD : (if θ ≤ π / 2 then d1 θ else - -1 * d1 (π - θ)) = G1 θ := by
      simp only [hG1def]; split_ifs <;> ring
    rw [eF, eD] at this; exact this
  have hG1d : ∀ θ ∈ Ioo 0 π, HasDerivAt G1 (G2 θ) θ := by
    intro θ hθ
    have := glue_hasDerivAt (c := 0) (σ := 1) hd2 (by ring) (by rw [hd2p]; ring) θ hθ
    have eF : (fun t => if t ≤ π / 2 then d1 t else 0 + 1 * d1 (π - t)) = G1 := by
      funext t; simp only [hG1def]; split_ifs <;> ring
    have eD : (if θ ≤ π / 2 then d2 θ else -1 * d2 (π - θ)) = G2 θ := by
      simp only [hG2def]; split_ifs <;> ring
    rw [eF, eD] at this; exact this
  -- the ODE for G in normal form on (0, π)
  have hG2eq : ∀ θ ∈ Ioo 0 π, G2 θ = profileRHS κ θ (G θ) (G1 θ) := by
    intro θ hθ
    unfold profileRHS
    by_cases hle : θ ≤ π / 2
    · simp only [hGdef, hG1def, hG2def, if_pos hle]
      have := hE ⟨hθ.1, hle⟩
      simp only [hEdef] at this
      linarith
    · have hgt : π / 2 < θ := not_le.mp hle
      simp only [hGdef, hG1def, hG2def, if_neg hle]
      set φ := π - θ with hφ
      have hφI : φ ∈ Ioc (0 : ℝ) (π / 2) := ⟨by linarith [hθ.2], by linarith⟩
      have := hE hφI
      simp only [hEdef] at this
      have hθφ : θ = π - φ := by ring
      have hc : Real.cos θ = -Real.cos φ := by rw [hθφ, Real.cos_pi_sub]
      have hsn : Real.sin θ = Real.sin φ := by rw [hθφ, Real.sin_pi_sub]
      have r1 := sin_two_mul_two_pi_sub (h φ)
      have r2 := sin_refl_aux (h φ) φ
      rw [← hθφ] at r2
      rw [hc, hsn, r1, r2]
      have hsφ := hsinI φ hφI
      field_simp
      field_simp at this
      linarith
  have hG1d' : ∀ θ ∈ Ioo 0 π, HasDerivAt G1 (profileRHS κ θ (G θ) (G1 θ)) θ :=
    fun θ hθ => hG2eq θ hθ ▸ hG1d θ hθ
  have hGsmooth : ContDiffOn ℝ ∞ G (Ioo 0 π) := bootstrap_smooth κ hGd hG1d'
  refine ⟨?_, ?_⟩
  · -- smoothness on [0, π] by locality
    apply contDiffOn_of_locally_contDiffOn
    intro x hx
    rcases lt_trichotomy x (π / 2) with hlt | heq | hgt
    · refine ⟨Iio (π / 2), isOpen_Iio, hlt, ?_⟩
      have hsub : Icc 0 π ∩ Iio (π / 2) ⊆ I := fun t ht => ⟨ht.1.1, le_of_lt ht.2⟩
      exact (hs.mono hsub).congr (fun t ht => if_pos (le_of_lt ht.2))
    · refine ⟨Ioo 0 π, isOpen_Ioo, ⟨by rw [heq]; exact hp, by rw [heq]; exact hpπ⟩, ?_⟩
      exact hGsmooth.mono inter_subset_right
    · refine ⟨Ioi (π / 2), isOpen_Ioi, hgt, ?_⟩
      have hmaps : MapsTo (fun t : ℝ => π - t) (Icc 0 π ∩ Ioi (π / 2)) I := by
        intro t ht
        simp only [mem_inter_iff, mem_Icc, mem_Ioi] at ht
        exact ⟨by linarith, by linarith⟩
      have hc : ContDiffOn ℝ ∞ (fun t => 2 * π - h (π - t)) (Icc 0 π ∩ Ioi (π / 2)) :=
        contDiffOn_const.sub (hs.comp (contDiffOn_const.sub contDiffOn_id) hmaps)
      exact hc.congr (fun t ht => if_neg (not_le.mpr ht.2))
  · -- the equation on (0, π)
    intro θ hθ
    have e1 : deriv G θ = G1 θ := (hGd θ hθ).deriv
    have e2 : deriv (deriv G) θ = G2 θ := by
      have hev : deriv G =ᶠ[𝓝 θ] G1 := by
        filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with t ht
        exact (hGd t ht).deriv
      rw [hev.deriv_eq]
      exact (hG1d θ hθ).deriv
    unfold profileOperator
    rw [e1, e2, hG2eq θ hθ]
    unfold profileRHS
    ring

end

section
open scoped ContDiff
open Real Set

theorem shooting_solution_kappa_four :
    ∃ h : ℝ → ℝ, ContDiffOn ℝ ∞ h (Icc 0 (π / 2)) ∧ h 0 = 0 ∧ h (π / 2) = π ∧
      (∀ θ ∈ Ioo (0 : ℝ) (π / 2), profileOperator 4 h θ = 0) ∧
      3 ≤ derivWithin h (Icc 0 (π / 2)) 0 ∧ PoleRep h := by
  obtain ⟨Φ, hΦc, hΦ⟩ := P241S.endpoint_continuous
  have h3 : (3 : ℝ) ∈ Icc (3 : ℝ) 5 := ⟨le_rfl, by norm_num⟩
  have h5 : (5 : ℝ) ∈ Icc (3 : ℝ) 5 := ⟨by norm_num, le_rfl⟩
  obtain ⟨h₃, hh₃, -⟩ := P241S.exists_shot 3 h3
  obtain ⟨h₅, hh₅, -⟩ := P241S.exists_shot 5 h5
  have hΦ3 : π < Φ 3 := (hΦ 3 h3 h₃ hh₃) ▸ P241N.three_overshoots h₃ hh₃
  have hΦ5 : Φ 5 < π := (hΦ 5 h5 h₅ hh₅) ▸ P241N.five_undershoots h₅ hh₅
  obtain ⟨a, ha, hΦa⟩ := intermediate_value_Icc' (by norm_num : (3 : ℝ) ≤ 5) hΦc
    ⟨hΦ5.le, hΦ3.le⟩
  obtain ⟨h, ⟨hs, h0, hd, hode⟩, hpole⟩ := P241S.exists_shot a ha
  exact ⟨h, hs, h0, (hΦ a ha h ⟨hs, h0, hd, hode⟩).trans hΦa, hode, hd ▸ ha.1, hpole⟩

end

section
open scoped ContDiff
open Real Set

theorem exists_second_profile_kappa_four' :
    ∃ h : ℝ → ℝ, IsH02CriticalProfile 4 h ∧ ∃ θ ∈ Set.Icc (0 : ℝ) Real.pi, h θ ≠ 2 * θ := by
  obtain ⟨h, hs, h0, hmid, hode, hder, hpole⟩ := shooting_solution_kappa_four
  set G : ℝ → ℝ := fun θ => if θ ≤ π / 2 then h θ else 2 * π - h (π - θ) with hG
  obtain ⟨hGs, hGode⟩ := hemispheric_extension 4 h hs hmid hode
  have hpi := Real.pi_pos
  have hG0 : G 0 = 0 := by
    have h' : (0 : ℝ) ≤ π / 2 := by positivity
    simp only [hG, if_pos h', h0]
  have hGπ : G π = 2 * π := by
    have : ¬ π ≤ π / 2 := by linarith
    simp [hG, this, h0]
  have hGsymm : ∀ θ ∈ Icc (0 : ℝ) π, G (π - θ) = 2 * π - G θ := by
    intro θ hθ
    simp only [hG]
    rcases lt_trichotomy θ (π / 2) with hlt | heq | hgt
    · have h1 : ¬ π - θ ≤ π / 2 := by linarith
      rw [if_neg h1, if_pos hlt.le]; simp
    · subst heq
      have h1 : π - π / 2 = π / 2 := by ring
      simp only [h1, le_refl, if_true, hmid]; ring
    · have h1 : π - θ ≤ π / 2 := by linarith
      have h2 : ¬ θ ≤ π / 2 := by linarith
      rw [if_pos h1, if_neg h2]; ring
  have hGsm : InducesSmoothMap G := by
    obtain ⟨δ, hδ, A₁, B₁, hA₁, hB₁, hrep⟩ := hpole
    refine inducesSmoothMap_of_north_pole_repr G (hGs.mono Ioo_subset_Icc_self) hGsymm δ hδ.1
      (by linarith [hδ.2]) A₁ B₁ hA₁ hB₁ ?_
    intro θ hθ
    have hle : θ ≤ π / 2 := hθ.2.trans hδ.2.le
    simp only [hG, if_pos hle]
    exact hrep θ hθ
  refine ⟨G, ⟨hGs, hGsm, hGode, hG0, hGπ, hGsymm⟩, ?_⟩
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have heq : EqOn h (fun θ => 2 * θ) (Icc 0 (π / 2)) := by
    intro θ hθ
    have := hcon θ ⟨hθ.1, by linarith [hθ.2]⟩
    simp only [hG, if_pos hθ.2] at this
    exact this
  have hmem : (0 : ℝ) ∈ Icc 0 (π / 2) := ⟨le_rfl, by positivity⟩
  have hd2 : derivWithin (fun θ : ℝ => 2 * θ) (Icc 0 (π / 2)) 0 = 2 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)).hasDerivWithinAt
      (s := Icc 0 (π / 2))
    have h' := this.derivWithin (uniqueDiffOn_Icc (by positivity) 0 hmem)
    simpa using h'
  rw [derivWithin_congr heq (heq hmem), hd2] at hder
  norm_num at hder

end

end SphericalFerromagnet.SF241


