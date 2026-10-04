-- Prove2me | solution 1 for Aumann1987.TwoPerson.ced_iff_linear_inequalities
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T06:43:45.946796+00:00
-- url     : https://prove2.me/submissions/49de9882-cfcf-43e6-a4ba-87d1a6ef1806

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Real.Basic
import Definitions.Def_Aumann1987_TwoPerson_Model

open Finset

/-! Auxiliary lemma: split a finite sum at a single point. -/
lemma sum_split {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι) (A : ℝ) (B : ι → ℝ) :
    ∑ x ∈ Finset.univ, (if x = j then A else B x) = A + ∑ x ∈ Finset.univ.erase j, B x := by
  classical
  rw [← Finset.add_sum_erase (s := Finset.univ) (f := fun x => if x = j then A else B x)
      (Finset.mem_univ j), if_pos rfl]
  congr 1
  exact Finset.sum_congr rfl fun x hx => by simp [Finset.ne_of_mem_erase hx]

open Aumann1987.TwoPerson in
/-- The fiber-sum identity: summing `μ γ * F (f₁ γ) (f₂ γ)` over `γ` equals summing
`distr μ f₁ f₂ j k * F j k` over pairs `(j, k)`. -/
lemma fiber_sum {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂] [DecidableEq S₁] [DecidableEq S₂]
    {Γ : Type*} [Fintype Γ] (μ : Γ → ℝ) (f₁ : Γ → S₁) (f₂ : Γ → S₂) (F : S₁ → S₂ → ℝ) :
    ∑ γ, μ γ * F (f₁ γ) (f₂ γ) = ∑ j, ∑ k, distr μ f₁ f₂ j k * F j k := by
  classical
  have h1 : ∑ γ, μ γ * F (f₁ γ) (f₂ γ)
      = ∑ j, ∑ γ ∈ Finset.univ.filter (fun γ => f₁ γ = j), μ γ * F (f₁ γ) (f₂ γ) := by
    rw [Finset.sum_fiberwise_eq_sum_filter Finset.univ Finset.univ f₁
      (fun γ => μ γ * F (f₁ γ) (f₂ γ))]
    simp
  rw [h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h2 : ∑ γ ∈ Finset.univ.filter (fun γ => f₁ γ = j), μ γ * F (f₁ γ) (f₂ γ)
      = ∑ γ ∈ Finset.univ.filter (fun γ => f₁ γ = j), μ γ * F j (f₂ γ) :=
    Finset.sum_congr rfl fun γ hγ => by rw [(Finset.mem_filter.mp hγ).2]
  rw [h2]
  have h3 : ∑ γ ∈ Finset.univ.filter (fun γ => f₁ γ = j), μ γ * F j (f₂ γ)
      = ∑ k, ∑ γ ∈ (Finset.univ.filter (fun γ => f₁ γ = j)).filter
          (fun γ => f₂ γ = k), μ γ * F j (f₂ γ) := by
    have hL : ∑ k, ∑ γ ∈ (Finset.univ.filter (fun γ => f₁ γ = j)).filter
          (fun γ => f₂ γ = k), μ γ * F j (f₂ γ)
        = ∑ γ ∈ Finset.univ.filter (fun γ => f₁ γ = j), μ γ * F j (f₂ γ) := by
      simpa using Finset.sum_fiberwise_eq_sum_filter
        (Finset.univ.filter (fun γ => f₁ γ = j)) Finset.univ f₂
        (fun γ => μ γ * F j (f₂ γ))
    rw [← hL]
  rw [h3]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hfilter : (Finset.univ.filter (fun γ => f₁ γ = j)).filter (fun γ => f₂ γ = k)
      = Finset.univ.filter (fun γ => f₁ γ = j ∧ f₂ γ = k) := by
    ext γ
    simp
  rw [hfilter]
  have hpt : ∀ γ ∈ Finset.univ.filter (fun γ => f₁ γ = j ∧ f₂ γ = k),
      μ γ * F j (f₂ γ) = μ γ * F j k := by
    intro γ hγ
    rw [(Finset.mem_filter.mp hγ).2.2]
  rw [Finset.sum_congr rfl hpt, ← Finset.sum_mul]
  rfl

open Aumann1987.TwoPerson in
theorem solution {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    [DecidableEq S₁] [DecidableEq S₂] (h₁ h₂ : S₁ → S₂ → ℝ)
    (p : S₁ → S₂ → ℝ) (hp : IsDistribution p) :
    IsCED h₁ h₂ p ↔
      (∀ j q : S₁, 0 ≤ ∑ k, (h₁ j k - h₁ q k) * p j k) ∧
      (∀ k r : S₂, 0 ≤ ∑ j, (h₂ j k - h₂ j r) * p j k) := by
  classical
  constructor
  · -- a correlated equilibrium distribution satisfies (2.4) and (2.5)
    rintro ⟨Γ, inst, μ, f₁, f₂, hprob, hce, hdistr⟩
    have hdev : DevCond₁ h₁ (distr μ f₁ f₂) ∧ DevCond₂ h₂ (distr μ f₁ f₂) := by
      constructor
      · intro φ
        have hφ := hce.1 φ
        rw [fiber_sum μ f₁ f₂ (fun j k => h₁ (φ j) k),
          fiber_sum μ f₁ f₂ (fun j k => h₁ j k)] at hφ
        exact hφ
      · intro ψ
        have hψ := hce.2 ψ
        rw [fiber_sum μ f₁ f₂ (fun j k => h₂ j (ψ k)),
          fiber_sum μ f₁ f₂ (fun j k => h₂ j k)] at hψ
        exact hψ
    rw [hdistr] at hdev
    obtain ⟨d1, d2⟩ := hdev
    refine ⟨?_, ?_⟩
    · -- player 1: (2.4)
      intro j q
      have key0 := d1 (fun x => if x = j then q else x)
      have hG : ∀ x ∈ Finset.univ,
          ∑ k, p x k * h₁ (if x = j then q else x) k
            = if x = j then ∑ k, p j k * h₁ q k else ∑ k, p x k * h₁ x k := by
        intro x _
        by_cases hx : x = j <;> simp [hx]
      have lhs : ∑ x, ∑ k, p x k * h₁ (if x = j then q else x) k
          = ∑ k, p j k * h₁ q k + (∑ x ∈ Finset.univ.erase j, ∑ k, p x k * h₁ x k) := by
        rw [Finset.sum_congr rfl hG, sum_split]
      have rhs : ∑ x, ∑ k, p x k * h₁ x k
          = ∑ k, p j k * h₁ j k + (∑ x ∈ Finset.univ.erase j, ∑ k, p x k * h₁ x k) := by
        rw [← Finset.add_sum_erase Finset.univ (fun x => ∑ k, p x k * h₁ x k)
          (Finset.mem_univ j)]
      have rearr : ∑ k, (h₁ j k - h₁ q k) * p j k
          = (∑ k, p j k * h₁ j k) - (∑ k, p j k * h₁ q k) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      linarith [key0, lhs, rhs, rearr]
    · -- player 2: (2.5)
      intro k r
      have key0 := d2 (fun y => if y = k then r else y)
      have h1' : (∑ j, ∑ y, p j y * h₂ j (if y = k then r else y))
          = ∑ y, ∑ j, p j y * h₂ j (if y = k then r else y) := Finset.sum_comm
      have h2' : (∑ j, ∑ y, p j y * h₂ j y)
          = ∑ y, ∑ j, p j y * h₂ j y := Finset.sum_comm
      rw [h1', h2'] at key0
      have hG : ∀ y ∈ Finset.univ,
          ∑ j, p j y * h₂ j (if y = k then r else y)
            = if y = k then ∑ j, p j k * h₂ j r else ∑ j, p j y * h₂ j y := by
        intro y _
        by_cases hy : y = k <;> simp [hy]
      have lhs : ∑ y, ∑ j, p j y * h₂ j (if y = k then r else y)
          = ∑ j, p j k * h₂ j r + (∑ y ∈ Finset.univ.erase k, ∑ j, p j y * h₂ j y) := by
        rw [Finset.sum_congr rfl hG, sum_split]
      have rhs : ∑ y, ∑ j, p j y * h₂ j y
          = ∑ j, p j k * h₂ j k + (∑ y ∈ Finset.univ.erase k, ∑ j, p j y * h₂ j y) := by
        rw [← Finset.add_sum_erase Finset.univ (fun y => ∑ j, p j y * h₂ j y)
          (Finset.mem_univ k)]
      have rearr : ∑ j, (h₂ j k - h₂ j r) * p j k
          = (∑ j, p j k * h₂ j k) - (∑ j, p j k * h₂ j r) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      linarith [key0, lhs, rhs, rearr]
  · -- (2.4) and (2.5) exhibit `p` as the distribution of a correlated equilibrium
    rintro ⟨ineq4, ineq5⟩
    have d1 : DevCond₁ h₁ p := by
      intro φ
      refine Finset.sum_le_sum fun x _ => ?_
      have h2 : ∑ k, (h₁ x k - h₁ (φ x) k) * p x k
          = (∑ k, p x k * h₁ x k) - (∑ k, p x k * h₁ (φ x) k) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      have h3 := ineq4 x (φ x)
      linarith
    have d2 : DevCond₂ h₂ p := by
      intro ψ
      have hpt : ∀ y ∈ Finset.univ,
          ∑ j, p j y * h₂ j (ψ y) ≤ ∑ j, p j y * h₂ j y := by
        intro y _
        have h2 : ∑ j, (h₂ j y - h₂ j (ψ y)) * p j y
            = (∑ j, p j y * h₂ j y) - (∑ j, p j y * h₂ j (ψ y)) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun j _ => by ring
        have h3 := ineq5 y (ψ y)
        linarith
      calc ∑ j, ∑ k, p j k * h₂ j (ψ k)
          = ∑ k, ∑ j, p j k * h₂ j (ψ k) := Finset.sum_comm
        _ ≤ ∑ k, ∑ j, p j k * h₂ j k := Finset.sum_le_sum hpt
        _ = ∑ j, ∑ k, p j k * h₂ j k := Finset.sum_comm
    -- the canonical carrier: enumerate `S₁ × S₂` by `Fin n` to land in universe 0
    classical
    set e : S₁ × S₂ ≃ Fin (Fintype.card (S₁ × S₂)) := Fintype.equivFin (S₁ × S₂) with he
    set μ : Fin (Fintype.card (S₁ × S₂)) → ℝ :=
      fun i => p (e.symm i).1 (e.symm i).2 with hμ
    set g₁ : Fin (Fintype.card (S₁ × S₂)) → S₁ := fun i => (e.symm i).1 with hg₁
    set g₂ : Fin (Fintype.card (S₁ × S₂)) → S₂ := fun i => (e.symm i).2 with hg₂
    -- the distribution of the projections is `p`
    have hdistrP : distr μ g₁ g₂ = p := by
      funext j k
      dsimp [distr, hμ, hg₁, hg₂]
      have hfib : ∀ i : Fin (Fintype.card (S₁ × S₂)),
          i ∈ Finset.univ.filter (fun i => (e.symm i).1 = j ∧ (e.symm i).2 = k)
            ↔ i = e (j, k) := by
        intro i
        rw [Finset.mem_filter]
        simp only [Finset.mem_univ, true_and]
        constructor
        · intro h
          have hpair : e.symm i = (j, k) := Prod.ext h.1 h.2
          calc i = e (e.symm i) := (Equiv.apply_symm_apply e i).symm
            _ = e (j, k) := by rw [hpair]
        · intro h
          subst h
          simp
      rw [Finset.sum_eq_single (e (j, k))]
      · simp [hμ]
      · intro b hb hne
        rw [hfib b] at hb
        exact absurd hb hne
      · rw [hfib]
        simp
    -- the probability vector
    have hprob : IsProbVec μ := by
      refine ⟨fun i => hp.1 _ _, ?_⟩
      calc ∑ i, μ i = ∑ y : S₁ × S₂, p y.1 y.2 :=
            Fintype.sum_equiv e.symm μ (fun y => p y.1 y.2) (by intro i; rfl)
        _ = ∑ j, ∑ k, p j k := Fintype.sum_prod_type' (fun j k => p j k)
        _ = 1 := hp.2
    -- the pair of projections is a correlated equilibrium
    have hce : IsCE h₁ h₂ μ g₁ g₂ := by
      constructor
      · intro φ
        have e1 := fiber_sum μ g₁ g₂ (fun j k => h₁ (φ j) k)
        have e2 := fiber_sum μ g₁ g₂ (fun j k => h₁ j k)
        rw [hdistrP] at e1 e2
        exact e1 ▸ e2 ▸ d1 φ
      · intro ψ
        have e1 := fiber_sum μ g₁ g₂ (fun j k => h₂ j (ψ k))
        have e2 := fiber_sum μ g₁ g₂ (fun j k => h₂ j k)
        rw [hdistrP] at e1 e2
        exact e1 ▸ e2 ▸ d2 ψ
    exact ⟨_, inferInstance, _, _, _, hprob, hce, hdistrP⟩
