-- Prove2me | Definitions.Def_TeschlODE_Stability_IsAsymptoticallyStable
-- name    : TeschlODE_Stability_IsAsymptoticallyStable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T13:05:05.02999+00:00
-- url     : https://prove2.me/theorems/d411232a-696e-41da-92ba-0e9fea1902d2
-- title:
--   Asymptotically stable fixed point (6.26)
-- statement:
--   With $M$, $\Phi$, $I_x$ as for stability, a point $x_0$ is **asymptotically stable** if it is stable and there is a neighborhood $U \subseteq M$ of $x_0$ such that for every $x \in U$ the solution $\Phi(\cdot, x)$ exists for all $t \ge 0$ and
--   $$\lim_{t \to \infty} |\Phi(t, x) - x_0| = 0 . \qquad (6.26)$$
--
--   Both conjuncts are kept: (6.26) alone does not imply stability (Problem 6.16).
--
--   **Formalization Note.** The limit is `Tendsto (fun t => Φ t x) atTop (nhds x₀)`, equivalent to $|\Phi(t,x) - x_0| \to 0$; existence on $[0, \infty)$, implicit in the book's limit, is stated explicitly so that the limit is not read off meaningless values of $\Phi$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 198, §6.5, Eq. (6.26)

import Mathlib
import Definitions.Def_TeschlODE_Stability_IsStable

namespace TeschlODE.Stability

/-- Teschl, §6.5, p. 198, (6.26): the fixed point `x₀` is asymptotically stable: it is stable
and there is a neighborhood `U ⊆ M` of `x₀` such that for every `x ∈ U` the solution exists for
all `t ≥ 0` and `Φ(t, x) → x₀` as `t → ∞` (i.e. `|Φ(t, x) - x₀| → 0`). -/
def IsAsymptoticallyStable {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) : Prop :=
  IsStable M I Φ x₀ ∧
  ∃ U ∈ nhds x₀, U ⊆ M ∧ ∀ x ∈ U, (∀ t : ℝ, 0 ≤ t → t ∈ I x) ∧
    Filter.Tendsto (fun t => Φ t x) Filter.atTop (nhds x₀)

end TeschlODE.Stability


