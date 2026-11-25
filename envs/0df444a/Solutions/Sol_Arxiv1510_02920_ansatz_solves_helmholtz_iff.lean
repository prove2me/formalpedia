-- Prove2me | solution 1 for Arxiv1510_02920.ansatz_solves_helmholtz_iff
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T15:42:41.295437+00:00
-- url     : https://prove2.me/submissions/ea5075db-64ef-4499-b197-d1d7c7ace0e8

import Mathlib
import Definitions.Def_Arxiv1510_02920_Basic

open Filter Topology Asymptotics
namespace Arxiv1510_02920

theorem ansatz_solves_helmholtz_iff (c : ℝ) (hc : 0 < c) (ω : ℝ) (hω : ω ≠ 0)
    (P : ℝ → ℂ → ℂ) (hP : Differentiable ℝ (fun x : ℝ => P x (ω : ℂ)))
    (gp gm : ℂ) (hPp : Tendsto (fun x : ℝ => P x (ω : ℂ)) atTop (𝓝 gp))
    (hPm : Tendsto (fun x : ℝ => P x (ω : ℂ)) atBot (𝓝 gm))
    (E0 : ℂ) (hE0 : E0 ≠ 0) (eps : ℝ → ℂ) :
    (∀ x, HelmholtzAt c ω eps (waveField c E0 P ω) x) ↔ ∀ x, eps x = perm c P x (ω : ℂ) := by
  set p : ℝ → ℂ := fun x => P x (ω : ℂ) with hpdef
  set k : ℂ := ((ω / c : ℝ) : ℂ) with hk
  set E := waveField c E0 P ω with hEdef
  have hint : ∀ x, HasDerivAt (fun u => ∫ t in (0:ℝ)..u, p t) (p x) x := fun x =>
    (hP.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hE : ∀ x, HasDerivAt E (Complex.I * k * p x * E x) x := by
    intro x
    have h1 := (((hint x).const_mul (Complex.I * k)).cexp).const_mul E0
    have hfE : E = fun y => E0 * Complex.exp (Complex.I * k * ∫ t in (0:ℝ)..y, p t) := rfl
    rw [hfE]
    exact h1.congr_deriv (by beta_reduce; ring)
  have hdE : deriv E = fun x => Complex.I * k * p x * E x := funext fun x => (hE x).deriv
  have hE2 : ∀ x, HasDerivAt (deriv E)
      (Complex.I * k * (deriv p x * E x + p x * (Complex.I * k * p x * E x))) x := by
    intro x
    rw [hdE]
    have := (((hP x).hasDerivAt.mul (hE x)).const_mul (Complex.I * k))
    have hf : (fun x => Complex.I * k * p x * E x) = fun y => Complex.I * k * (p * E) y := by
      funext y; simp only [Pi.mul_apply]; ring
    rw [hf]; exact this
  have hEne : ∀ x, E x ≠ 0 := by
    intro x; simp only [hEdef, waveField]
    exact mul_ne_zero hE0 (Complex.exp_ne_zero _)
  have hkne : k ≠ 0 := by
    simp only [hk]; exact_mod_cast div_ne_zero hω hc.ne'
  have key : ∀ x, deriv (deriv E) x + ((ω / c : ℝ) : ℂ) ^ 2 * eps x * E x =
      k ^ 2 * E x * (eps x - perm c P x (ω : ℂ)) := by
    intro x
    rw [(hE2 x).deriv]
    unfold perm
    rw [← hk]
    have hωc : (ω : ℂ) ≠ 0 := by exact_mod_cast hω
    have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hkk : k = (ω : ℂ) / (c : ℂ) := by simp [hk]
    rw [hkk]
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  constructor
  · intro h x
    have := (h x).2.2
    rw [key x] at this
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 (mul_ne_zero (pow_ne_zero _ hkne) (hEne x))
    · exact sub_eq_zero.1 h0
  · intro h x
    refine ⟨Filter.Eventually.of_forall fun y => (hE y).differentiableAt, (hE2 x).differentiableAt, ?_⟩
    rw [key x, h x, sub_self, mul_zero]

end Arxiv1510_02920
open Arxiv1510_02920 in
theorem solution (c : ℝ) (hc : 0 < c) (ω : ℝ) (hω : ω ≠ 0)
    (P : ℝ → ℂ → ℂ) (hP : Differentiable ℝ (fun x : ℝ => P x (ω : ℂ)))
    (gp gm : ℂ) (hPp : Tendsto (fun x : ℝ => P x (ω : ℂ)) atTop (𝓝 gp))
    (hPm : Tendsto (fun x : ℝ => P x (ω : ℂ)) atBot (𝓝 gm))
    (E0 : ℂ) (hE0 : E0 ≠ 0) (eps : ℝ → ℂ) :
    (∀ x, HelmholtzAt c ω eps (waveField c E0 P ω) x) ↔ ∀ x, eps x = perm c P x (ω : ℂ) :=
  ansatz_solves_helmholtz_iff c hc ω hω P hP gp gm hPp hPm E0 hE0 eps
