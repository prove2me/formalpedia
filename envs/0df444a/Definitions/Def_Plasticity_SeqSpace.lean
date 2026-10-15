-- Prove2me | Definitions.Def_Plasticity_SeqSpace
-- name    : Plasticity_SeqSpace
-- status  : Definition
-- author  : @scanstone
-- created : 2026-10-14T08:53:52.934793+00:00
-- url     : https://prove2.me/theorems/4aac2c47-2c0c-4490-aff0-628e02fc7f5d
-- title:
--   The spaces $\ell_\infty(\Gamma)$, $c_0(\Gamma)$, $c_{00}(\Gamma)$ and their unit balls
-- statement:
--   For an arbitrary index set $\Gamma$, $\ell_\infty(\Gamma)$ is the space of bounded real functions on $\Gamma$ with the supremum norm $\|x\|=\sup_{i\in\Gamma}|x_i|$.
--   Inside it, $c_0(\Gamma)$ is the subspace of functions that vanish at infinity (for every $\varepsilon>0$ only finitely many $i$ have $|x_i|\ge\varepsilon$), and $c_{00}(\Gamma)$ the subspace of finitely supported functions.
--   A **space between $c_{00}(\Gamma)$ and $c_0(\Gamma)$** is a linear subspace $X$ with $c_{00}(\Gamma)\subseteq X\subseteq c_0(\Gamma)$; its closed unit ball is $B_X=X\cap\{x:\|x\|\le1\}$.
--   A subspace $Y$ of $\ell_\infty(\Delta)$ **realizes all sign patterns** if for every countable $C\subseteq\Delta$ and every choice of signs $\varepsilon_d\in\{1,-1\}$, $d\in C$, some $v\in Y$ has $\varepsilon_d v_d>0$ for all $d\in C$.
-- source:
--   This repository: expositions/c0_between_spaces.md, §1 (Setting) and §4 (before Corollary 4)

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Order.Filter.Cofinite

/-!
# Plasticity: sequence spaces over an arbitrary index set

`Linf Γ` is ℓ∞(Γ), the real bounded functions on `Γ` with the supremum norm (Mathlib's
`lp (fun _ => ℝ) ∞`). Inside it, `c0 Γ` is the subspace of functions vanishing at
infinity (tending to `0` along the cofinite filter) and `c00 Γ` the subspace of finitely
supported functions. A space "between c₀₀(Γ) and c₀(Γ)" is a submodule `X` with
`c00 Γ ≤ X ≤ c0 Γ`; its closed unit ball inside `Linf Γ` is `ballIn X`.
-/

namespace Plasticity

open Filter Topology

/-- ℓ∞(Γ): bounded real functions on `Γ` with the supremum norm. -/
abbrev Linf (Γ : Type*) : Type _ := lp (fun _ : Γ => ℝ) ⊤

/-- c₀(Γ): the functions in ℓ∞(Γ) that tend to `0` along the cofinite filter. -/
def c0 (Γ : Type*) : Submodule ℝ (Linf Γ) where
  carrier := {x | Tendsto (⇑x) cofinite (𝓝 0)}
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, lp.coeFn_zero]
    exact tendsto_const_nhds
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq, lp.coeFn_add] at *
    have h := hx.add hy
    rw [add_zero] at h
    exact h
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq, lp.coeFn_smul] at *
    have h := hx.const_smul c
    rw [smul_zero] at h
    exact h

/-- c₀₀(Γ): the finitely supported functions in ℓ∞(Γ). -/
def c00 (Γ : Type*) : Submodule ℝ (Linf Γ) where
  carrier := {x | (Function.support (⇑x)).Finite}
  zero_mem' := by
    show (Function.support (⇑(0 : Linf Γ))).Finite
    rw [lp.coeFn_zero, Function.support_zero]
    exact Set.finite_empty
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq, lp.coeFn_add] at *
    exact (hx.union hy).subset (Function.support_add _ _)
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq, lp.coeFn_smul] at *
    exact hx.subset (Function.support_const_smul_subset c _)

/-- The closed unit ball of a subspace `X` of ℓ∞(Γ), as a subset of ℓ∞(Γ). -/
def ballIn {Γ : Type*} (X : Submodule ℝ (Linf Γ)) : Set (Linf Γ) :=
  (X : Set (Linf Γ)) ∩ Metric.closedBall 0 1

/-- `Y` realizes all sign patterns: for every countable `C ⊆ Δ` and every choice of signs
`ε d = ±1` on `C` there is `v ∈ Y` with `v d` of sign `ε d` for every `d ∈ C`. -/
def RealizesSignPatterns {Δ : Type*} (Y : Submodule ℝ (Linf Δ)) : Prop :=
  ∀ C : Set Δ, C.Countable → ∀ ε : Δ → ℝ, (∀ d ∈ C, ε d = 1 ∨ ε d = -1) →
    ∃ v : Linf Δ, v ∈ Y ∧ ∀ d ∈ C, 0 < ε d * v d

end Plasticity


