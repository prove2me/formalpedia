-- Prove2me | solution 1 for Arxiv2608_05214.liouville_schrodinger
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T00:01:09.857477+00:00
-- url     : https://prove2.me/submissions/405b3d09-ffda-4116-a296-128465a00742

import Mathlib
import Definitions.Def_Arxiv2608_05214_Basic

set_option autoImplicit false

open MeasureTheory

open Arxiv2608_05214 in
theorem solution (η : ℝ → ℝ) (ψ : ℝ → ℝ → ℝ)
    (hηpos : ∀ τ, 0 < η τ) (hη : ContDiff ℝ 2 η) (hψ : ∀ t, ContDiff ℝ 2 (fun τ => ψ τ t)) :
    (∀ τ t : ℝ, hornEqLHS (fun τ => η τ ^ 2) (fun τ t => ψ τ t / η τ) τ t =
        η τ * schrodingerLHS (scatteringPotential η) ψ τ t) ∧
    (∀ τ : ℝ, (∀ᶠ σ in nhds τ, η σ = η τ) → scatteringPotential η τ = 0) := by
  have hηd : Differentiable ℝ η := hη.differentiable (by norm_num)
  have hηd' : Differentiable ℝ (deriv η) := by
    have := hη.iterate_deriv' 1 1
    simpa using this.differentiable (by norm_num)
  refine ⟨fun τ t => ?_, fun τ h => ?_⟩
  · set f : ℝ → ℝ := fun τ => ψ τ t
    have hfd : Differentiable ℝ f := (hψ t).differentiable (by norm_num)
    have hfd' : Differentiable ℝ (deriv f) := by
      have := (hψ t).iterate_deriv' 1 1
      simpa using this.differentiable (by norm_num)
    have e1 : (fun s => η s ^ 2 * deriv (fun τ => ψ τ t / η τ) s) =
        fun s => η s * deriv f s - f s * deriv η s := by
      funext s
      have hd := (hfd s).hasDerivAt.div (hηd s).hasDerivAt (hηpos s).ne'
      rw [show (fun τ => ψ τ t / η τ) = f / η from rfl, hd.deriv]
      have := (hηpos s).ne'
      field_simp
    have e2 : deriv (fun s => η s * deriv f s - f s * deriv η s) τ =
        η τ * deriv (deriv f) τ - f τ * deriv (deriv η) τ := by
      have := (((hηd τ).hasDerivAt.mul (hfd' τ).hasDerivAt).sub
        ((hfd τ).hasDerivAt.mul (hηd' τ).hasDerivAt)).deriv
      rw [show (fun s => η s * deriv f s - f s * deriv η s) = η * deriv f - f * deriv η from rfl, this]; ring
    unfold hornEqLHS schrodingerLHS scatteringPotential
    rw [e1, e2]
    have ht : ∀ s, deriv (fun t => ψ τ t / η τ) s = deriv (fun t => ψ τ t) s / η τ :=
      fun s => deriv_div_const _
    simp only [ht]
    have ht2 : deriv (fun s => deriv (fun t => ψ τ t) s / η τ) t =
        deriv (fun s => deriv (fun t => ψ τ t) s) t / η τ := deriv_div_const _
    rw [ht2]
    have := (hηpos τ).ne'
    field_simp
    ring
  · unfold scatteringPotential
    have h1 : deriv η =ᶠ[nhds τ] fun _ => (0 : ℝ) := by
      have h' : η =ᶠ[nhds τ] fun _ => η τ := h
      have := h'.deriv
      simpa using this
    rw [h1.deriv_eq]
    simp
