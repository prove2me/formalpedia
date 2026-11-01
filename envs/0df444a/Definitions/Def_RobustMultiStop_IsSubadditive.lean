-- Prove2me | Definitions.Def_RobustMultiStop_IsSubadditive
-- name    : RobustMultiStop_IsSubadditive
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:29:23.774966+00:00
-- url     : https://prove2.me/theorems/f056adfe-58a2-4c90-b648-38b14673ef6e
-- title:
--   Subadditivity (P1) of a DMU
-- statement:
--   A DMU $\rho$ on $\mathfrak X$ with horizon $N$ is **subadditive** (P1) if
--
--   $$\rho_t(X+Y)\le\rho_t(X)+\rho_t(Y)\qquad\text{for all }X,Y\in\mathfrak X,\ t\le N.$$
--
--   Subadditivity is the only property beyond (C1)–(C4) needed for the dual representation (3.1)–(3.2) of Theorem 3.1.
-- source:
--   Laeven, Schoenmakers, Schweizer & Stadje, Robust Multiple Stopping — A Pathwise Duality Approach, arXiv:2006.01802v2, §2.1, p.4, property (P1)

import Mathlib

open MeasureTheory

namespace RobustMultiStop

/-- Subadditivity (P1), Laeven, Schoenmakers, Schweizer & Stadje, *Robust Multiple Stopping — A
Pathwise Duality Approach*, arXiv:2006.01802v2, §2.1, p.4: `ρ_t(X + Y) ≤ ρ_t(X) + ρ_t(Y)` for all
`X, Y ∈ 𝔛` and `t ∈ {0, …, T}`.

**Formalization Note** Inequalities are `P`-a.s. (order of `Ω →ₘ[P] ℝ`); `N` is the horizon. -/
def IsSubadditive {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
    (N : ℕ) (𝔛 : Submodule ℝ (Ω →ₘ[P] ℝ)) (ρ : ℕ → (Ω →ₘ[P] ℝ) → (Ω →ₘ[P] ℝ)) : Prop :=
  ∀ t ≤ N, ∀ X ∈ 𝔛, ∀ Y ∈ 𝔛, ρ t (X + Y) ≤ ρ t X + ρ t Y

end RobustMultiStop


