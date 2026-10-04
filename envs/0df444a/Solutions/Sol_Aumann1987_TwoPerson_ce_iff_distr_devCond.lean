-- Prove2me | solution 1 for Aumann1987.TwoPerson.ce_iff_distr_devCond
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T06:43:28.319163+00:00
-- url     : https://prove2.me/submissions/f4922bde-7bc4-4763-9504-98f60494da5f

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Real.Basic
import Definitions.Def_Aumann1987_TwoPerson_Model

open Finset

open Aumann1987.TwoPerson in
/-- The fiber-sum identity: summing `μ γ * F (f₁ γ) (f₂ γ)` over `γ` equals summing
`distr μ f₁ f₂ j k * F j k` over pairs `(j, k)`. -/
lemma fiber_sum {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂] [DecidableEq S₁] [DecidableEq S₂]
    {Γ : Type*} [Fintype Γ] (μ : Γ → ℝ) (f₁ : Γ → S₁) (f₂ : Γ → S₂) (F : S₁ → S₂ → ℝ) :
    ∑ γ, μ γ * F (f₁ γ) (f₂ γ) = ∑ j, ∑ k, distr μ f₁ f₂ j k * F j k := by
  classical
  -- first fiber decomposition: by the value of `f₁`
  have h1 : ∑ γ, μ γ * F (f₁ γ) (f₂ γ)
      = ∑ j, ∑ γ ∈ Finset.univ.filter (fun γ => f₁ γ = j), μ γ * F (f₁ γ) (f₂ γ) := by
    rw [Finset.sum_fiberwise_eq_sum_filter Finset.univ Finset.univ f₁
      (fun γ => μ γ * F (f₁ γ) (f₂ γ))]
    simp
  rw [h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  -- on the fiber, `F (f₁ γ) = F j`
  have h2 : ∑ γ ∈ Finset.univ.filter (fun γ => f₁ γ = j), μ γ * F (f₁ γ) (f₂ γ)
      = ∑ γ ∈ Finset.univ.filter (fun γ => f₁ γ = j), μ γ * F j (f₂ γ) :=
    Finset.sum_congr rfl fun γ hγ => by rw [(Finset.mem_filter.mp hγ).2]
  rw [h2]
  -- second fiber decomposition: by the value of `f₂`, inside the first fiber
  have h3 : ∑ γ ∈ Finset.univ.filter (fun γ => f₁ γ = j), μ γ * F j (f₂ γ)
      = ∑ k, ∑ γ ∈ (Finset.univ.filter (fun γ => f₁ γ = j)).filter
          (fun γ => f₂ γ = k), μ γ * F j k := by
    have hL : ∑ k, ∑ γ ∈ (Finset.univ.filter (fun γ => f₁ γ = j)).filter
          (fun γ => f₂ γ = k), μ γ * F j (f₂ γ)
        = ∑ γ ∈ Finset.univ.filter (fun γ => f₁ γ = j), μ γ * F j (f₂ γ) := by
      simpa using Finset.sum_fiberwise_eq_sum_filter
        (Finset.univ.filter (fun γ => f₁ γ = j)) Finset.univ f₂
        (fun γ => μ γ * F j (f₂ γ))
    rw [← hL]
    exact Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun γ hγ => by rw [(Finset.mem_filter.mp hγ).2]
  rw [h3]
  refine Finset.sum_congr rfl fun k _ => ?_
  -- merge the two filters and pull the constant `F j k` out of the sum
  have hfilter : (Finset.univ.filter (fun γ => f₁ γ = j)).filter (fun γ => f₂ γ = k)
      = Finset.univ.filter (fun γ => f₁ γ = j ∧ f₂ γ = k) := by
    ext γ
    simp
  rw [hfilter]
  rw [← Finset.sum_mul]
  rfl

open Aumann1987.TwoPerson in
theorem solution {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    [DecidableEq S₁] [DecidableEq S₂] (h₁ h₂ : S₁ → S₂ → ℝ)
    {Γ : Type*} [Fintype Γ] (μ : Γ → ℝ) (hμ : IsProbVec μ) (f₁ : Γ → S₁) (f₂ : Γ → S₂) :
    IsCE h₁ h₂ μ f₁ f₂ ↔
      DevCond₁ h₁ (distr μ f₁ f₂) ∧ DevCond₂ h₂ (distr μ f₁ f₂) := by
  classical
  constructor
  · rintro ⟨his, hers⟩
    constructor
    · intro φ
      have hφ := his φ
      rw [fiber_sum μ f₁ f₂ (fun j k => h₁ (φ j) k),
        fiber_sum μ f₁ f₂ (fun j k => h₁ j k)] at hφ
      exact hφ
    · intro ψ
      have hψ := hers ψ
      rw [fiber_sum μ f₁ f₂ (fun j k => h₂ j (ψ k)),
        fiber_sum μ f₁ f₂ (fun j k => h₂ j k)] at hψ
      exact hψ
  · rintro ⟨d1, d2⟩
    refine ⟨?_, ?_⟩
    · intro φ
      have hφ := d1 φ
      rw [← fiber_sum μ f₁ f₂ (fun j k => h₁ (φ j) k),
        ← fiber_sum μ f₁ f₂ (fun j k => h₁ j k)] at hφ
      exact hφ
    · intro ψ
      have hψ := d2 ψ
      rw [← fiber_sum μ f₁ f₂ (fun j k => h₂ j (ψ k)),
        ← fiber_sum μ f₁ f₂ (fun j k => h₂ j k)] at hψ
      exact hψ
