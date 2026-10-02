-- Prove2me | Definitions.Def_TeschlQM_Atomic_mulOp
-- name    : TeschlQM_Atomic_mulOp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T08:37:23.164631+00:00
-- url     : https://prove2.me/theorems/9451ec40-9988-45a2-9f53-7016abc8d126
-- title:
--   Maximally defined multiplication operator in L² (2.21)
-- statement:
--   Let $(X, \mu)$ be a measure space and $g : X \to \mathbb C$ a measurable function. The **multiplication operator** by $g$ in $L^2(X, d\mu)$ is
--   $$(g f)(x) = g(x) f(x), \qquad \mathfrak D(g) = \{ f \in L^2(X, d\mu) \mid g f \in L^2(X, d\mu) \}.$$
--
--   Potentials $V(x)$ in Schrödinger operators act as such multiplication operators in $L^2(\mathbb R^n)$, and the free Hamiltonian is unitarily equivalent to the multiplication operator by $|p|^2$.
--
--   **Formalization Note.** `mulOp μ g` is a `LinearPMap` on `Lp ℂ 2 μ` with domain `mulOpDomain μ g = {f | MemLp (g · f) 2 μ}` (the maximal domain) and value the $L^2$ class of $x \mapsto g(x) f(x)$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 59, Section 2.2, Eq. (2.21)

import Mathlib

namespace TeschlQM.Atomic

open MeasureTheory

/-- The maximal domain of the multiplication operator by `g` in `L²(X, μ)`:
`𝔇(g) = {f ∈ L² | g f ∈ L²}`. -/
def mulOpDomain {X : Type*} [MeasurableSpace X] (μ : Measure X) (g : X → ℂ) :
    Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {f | MemLp (fun x => g x * (f : X → ℂ) x) 2 μ}
  add_mem' := by
    intro f₁ f₂ h₁ h₂
    refine (h₁.add h₂).ae_eq ?_
    filter_upwards [Lp.coeFn_add f₁ f₂] with x hx
    rw [hx, Pi.add_apply, Pi.add_apply, mul_add]
  zero_mem' := by
    refine (MemLp.zero : MemLp (fun _ : X => (0 : ℂ)) 2 μ).ae_eq ?_
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
    rw [hx, Pi.zero_apply, mul_zero]
  smul_mem' := by
    intro c f h
    refine (h.const_smul c).ae_eq ?_
    filter_upwards [Lp.coeFn_smul c f] with x hx
    rw [hx, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]

/-- Teschl (2.21), p. 59: the (maximally defined) **multiplication operator** by
the measurable function `g` in `L²(X, μ)`, `(g f)(x) = g(x) f(x)` with domain
`𝔇(g) = {f ∈ L² | g f ∈ L²}`. A potential `V(x)` acting in `L²(ℝⁿ)` is this operator. -/
noncomputable def mulOp {X : Type*} [MeasurableSpace X] (μ : Measure X) (g : X → ℂ) :
    Lp ℂ 2 μ →ₗ.[ℂ] Lp ℂ 2 μ where
  domain := mulOpDomain μ g
  toFun :=
    { toFun := fun f => MemLp.toLp _ f.2
      map_add' := by
        intro f₁ f₂
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (f₁ + f₂).2, MemLp.coeFn_toLp f₁.2,
          MemLp.coeFn_toLp f₂.2, Lp.coeFn_add (f₁ : Lp ℂ 2 μ) f₂,
          Lp.coeFn_add (MemLp.toLp _ f₁.2) (MemLp.toLp _ f₂.2)] with x h h₁ h₂ h₃ h₄
        rw [h, h₄, Pi.add_apply, h₁, h₂, Submodule.coe_add, h₃, Pi.add_apply, mul_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (c • f).2, MemLp.coeFn_toLp f.2,
          Lp.coeFn_smul c (f : Lp ℂ 2 μ), Lp.coeFn_smul c (MemLp.toLp _ f.2)] with x h h₁ h₂ h₃
        rw [h, RingHom.id_apply, h₃, Pi.smul_apply, h₁, Submodule.coe_smul, h₂, Pi.smul_apply,
          smul_eq_mul, smul_eq_mul, mul_left_comm] }

end TeschlQM.Atomic


