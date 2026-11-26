-- Prove2me | solution 1 for Arxiv2608_05214.single_interface_reflection
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T00:42:33.595631+00:00
-- url     : https://prove2.me/submissions/08ebd097-d7b6-4351-8dc3-f4b548920bdf

import Mathlib
import Definitions.Def_Arxiv2608_05214_Basic

set_option autoImplicit false

namespace S74SI
open Arxiv2608_05214

lemma dA (f : ℝ → ℝ) (hf : Differentiable ℝ f) (r τ₀ t η : ℝ) :
    deriv (fun τ => interfaceAbove f r τ₀ τ t / η) τ₀ = ((r - 1) * deriv f (t - τ₀)) / η := by
  have h1 : HasDerivAt (fun τ => f (t - τ)) (-deriv f (t - τ₀)) τ₀ :=
    (hf (t - τ₀)).hasDerivAt.comp_const_sub t τ₀
  have h2 : HasDerivAt (fun τ => f (t + τ - 2 * τ₀)) (deriv f (τ₀ + (t - 2 * τ₀))) τ₀ := by
    have e : (fun τ => f (t + τ - 2 * τ₀)) = fun τ => f (τ + (t - 2 * τ₀)) := by
      funext τ; ring_nf
    rw [e]
    exact (hf (τ₀ + (t - 2 * τ₀))).hasDerivAt.comp_add_const τ₀ (t - 2 * τ₀)
  have h := (h1.fun_add (h2.const_mul r)).div_const η
  unfold interfaceAbove
  rw [h.deriv, show τ₀ + (t - 2 * τ₀) = t - τ₀ by ring]
  ring

lemma dB (f : ℝ → ℝ) (hf : Differentiable ℝ f) (T τ₀ t η : ℝ) :
    deriv (fun τ => interfaceBelow f T τ t / η) τ₀ = (-(T * deriv f (t - τ₀))) / η := by
  have h1 : HasDerivAt (fun τ => f (t - τ)) (-deriv f (t - τ₀)) τ₀ :=
    (hf (t - τ₀)).hasDerivAt.comp_const_sub t τ₀
  have h := (h1.const_mul T).div_const η
  unfold interfaceBelow
  rw [h.deriv]
  ring

lemma uniq (τ₀ : ℝ) (f : ℝ → ℝ) (hf : Differentiable ℝ f) (hf' : ∃ s, deriv f s ≠ 0)
    (η₁ η₂ : ℝ) (h1 : 0 < η₁) (h2 : 0 < η₂) (r T : ℝ)
    (h : SatisfiesInterfaceConditions η₁ η₂ τ₀ f r T) :
    r = (η₁ ^ 2 - η₂ ^ 2) / (η₁ ^ 2 + η₂ ^ 2) := by
  obtain ⟨hc, hd⟩ := h
  obtain ⟨s, hs⟩ := hf'
  have hfnz : ∃ u, f u ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have : f = fun _ => 0 := funext hcon
    apply hs; rw [this]; simp
  obtain ⟨u, hu⟩ := hfnz
  have e2 := hd (s + τ₀)
  rw [dA f hf, dB f hf, show s + τ₀ - τ₀ = s by ring] at e2
  have e1 := hc (u + τ₀)
  unfold interfaceAbove interfaceBelow at e1
  rw [show u + τ₀ - τ₀ = u by ring, show u + τ₀ + τ₀ - 2 * τ₀ = u by ring] at e1
  have h1' := h1.ne'; have h2' := h2.ne'
  field_simp at e1 e2
  -- e2 : η₁ (r-1) f' = - η₂ T f' ; e1: η₂ (1+r) f = η₁ T f
  have hden : η₁ ^ 2 + η₂ ^ 2 ≠ 0 := by positivity
  field_simp
  linear_combination η₁ * e2 + η₂ * e1

end S74SI

open Arxiv2608_05214 S74SI in
theorem solution (τ₀ : ℝ) (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hf' : ∃ s, deriv f s ≠ 0) :
    (∀ η₁ η₂ : ℝ, 0 < η₁ → 0 < η₂ →
      (∃ T, SatisfiesInterfaceConditions η₁ η₂ τ₀ f ((η₁ ^ 2 - η₂ ^ 2) / (η₁ ^ 2 + η₂ ^ 2)) T) ∧
      ∀ r T, SatisfiesInterfaceConditions η₁ η₂ τ₀ f r T →
        r = (η₁ ^ 2 - η₂ ^ 2) / (η₁ ^ 2 + η₂ ^ 2) ∧ η₂ ^ 2 / η₁ ^ 2 = (1 - r) / (1 + r)) ∧
    (∀ Z₁ Z₂ : ℝ, 0 < Z₁ → 0 < Z₂ → ∀ r T,
      SatisfiesInterfaceConditions (1 / Real.sqrt Z₁) (1 / Real.sqrt Z₂) τ₀ f r T →
        r = (Z₂ - Z₁) / (Z₂ + Z₁)) := by
  refine ⟨fun η₁ η₂ h1 h2 => ⟨?_, fun r T h => ?_⟩, fun Z₁ Z₂ hZ1 hZ2 r T h => ?_⟩
  · have hden : η₁ ^ 2 + η₂ ^ 2 ≠ 0 := by positivity
    have h1' := h1.ne'; have h2' := h2.ne'
    refine ⟨η₁ * (1 - (η₁ ^ 2 - η₂ ^ 2) / (η₁ ^ 2 + η₂ ^ 2)) / η₂, ?_, ?_⟩
    · intro t
      unfold interfaceAbove interfaceBelow
      rw [show t + τ₀ - 2 * τ₀ = t - τ₀ by ring]
      field_simp
      ring
    · intro t
      rw [dA f hf, dB f hf]
      field_simp
      ring
  · have hr := uniq τ₀ f hf hf' η₁ η₂ h1 h2 r T h
    refine ⟨hr, ?_⟩
    have hden : η₁ ^ 2 + η₂ ^ 2 ≠ 0 := by positivity
    have h1' := h1.ne'; have h2' := h2.ne'
    have hp : 1 + r ≠ 0 := by
      have : 1 + r = 2 * η₁ ^ 2 / (η₁ ^ 2 + η₂ ^ 2) := by rw [hr]; field_simp; ring
      rw [this]; positivity
    rw [hr] at hp ⊢
    field_simp
    ring
  · have s1 := Real.sqrt_pos.2 hZ1
    have s2 := Real.sqrt_pos.2 hZ2
    have hr := uniq τ₀ f hf hf' _ _ (by positivity) (by positivity) r T h
    rw [hr]
    have q1 := Real.sq_sqrt hZ1.le
    have q2 := Real.sq_sqrt hZ2.le
    rw [div_pow, div_pow, one_pow, q1, q2]
    field_simp
