-- Prove2me | Definitions.Def_TeschlODE_PeriodicOrbits_IsStableOrbit
-- name    : TeschlODE_PeriodicOrbits_IsStableOrbit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T04:37:54.274495+00:00
-- url     : https://prove2.me/theorems/3c38a05d-4b03-48c2-ae2a-a0e733260bd3
-- title:
--   Stable orbit — §12.1
-- statement:
--   Let $\Phi$ be the flow on $M$ with maximal intervals $I_x$. An orbit $\gamma$ is **stable** if for every neighborhood $U$ of $\gamma$ there is a neighborhood $V \subseteq U$ of $\gamma$ such that every solution starting in $V$ remains in $U$ for all $t \ge 0$:
--   $$\forall x \in V,\ \forall t \ge 0:\quad t \in I_x \ \text{ and } \ \Phi(t, x) \in U .$$
--
--   The definition ignores time parametrization: a nearby solution has to stay near the orbit as a set, not near a particular point moving on it. An orbit which is not stable is **unstable**.
--
--   **Formalization Note.** Neighborhoods of the set $\gamma$ are elements of `nhdsSet γ`. $V$ is also required to lie in the phase space $M$ (solutions start in $M$); since $\gamma \subseteq M$ and $M$ is open, this loses nothing. "Remains in $U$ for all $t \ge 0$" includes that the solution exists for all $t \ge 0$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 315, §12.1

import Mathlib

namespace TeschlODE.PeriodicOrbits

/-- Teschl, §12.1, p. 315: the orbit `γ` is stable for the flow `Φ` (maximal time intervals `I`)
on `M`: for every neighborhood `U` of `γ` there is a neighborhood `V ⊆ U` of `γ`, contained in
`M`, such that the solution starting at any `x ∈ V` exists for all `t ≥ 0` and remains in `U`
for all `t ≥ 0`. (Neighborhoods of a set are `nhdsSet γ`.) -/
def IsStableOrbit {n : ℕ} (M : Set (Fin n → ℝ)) (I : (Fin n → ℝ) → Set ℝ)
    (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)) (γ : Set (Fin n → ℝ)) : Prop :=
  ∀ U ∈ nhdsSet γ, ∃ V ∈ nhdsSet γ, V ⊆ U ∧ V ⊆ M ∧
    ∀ x ∈ V, ∀ t : ℝ, 0 ≤ t → t ∈ I x ∧ Φ t x ∈ U

end TeschlODE.PeriodicOrbits


