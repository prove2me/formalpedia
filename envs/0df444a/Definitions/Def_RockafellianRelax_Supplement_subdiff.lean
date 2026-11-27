-- Prove2me | Definitions.Def_RockafellianRelax_Supplement_subdiff
-- name    : RockafellianRelax_Supplement_subdiff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:15:45.436871+00:00
-- url     : https://prove2.me/theorems/0fa0e92f-adbe-5847-b684-5a9e3aaf7159
-- title:
--   General (limiting) subdifferential on $\mathbb R^m\times\mathbb R^n$
-- statement:
--   Let $\psi : \mathbb R^m\times\mathbb R^n \to \overline{\mathbb R}$. At a point $z$ where $\psi$ is finite, a **regular subgradient** is a vector $v$ such that for every $\epsilon > 0$ and all $w$ near $z$, $\psi(w) \ge \psi(z) + \langle v, w-z\rangle - \epsilon\|w-z\|_2$. The **subdifferential** is
--
--   $$
--   \partial\psi(z) = \{v \mid \exists\, z^k\to z,\ \psi(z^k)\to\psi(z),\ v^k \to v,\ v^k \text{ a regular subgradient of }\psi\text{ at }z^k\}
--   $$
--
--   where $\psi(z)$ is finite, and $\partial\psi(z) = \emptyset$ at every other $z$.
--
--   This is the subdifferential in the optimality conditions of Theorems 5.1 and 5.2.
--
--   **Formalization Note** The published `NonconvexSplitting.Shared.LimitingSubdiff` is evaluated on Euclidean $\mathbb R^{m+n}$ and pulled back. It excludes only the value $+\infty$, so the condition $\psi(z) \ne -\infty$ is added, as the paper sets $\partial\psi(z) = \emptyset$ there.
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, §5, p.24 (subgradients in the general sense of [51], Rockafellar–Wets Definition 8.3)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_RockafellianRelax_Supplement_jointEuclid

namespace RockafellianRelax.Supplement

/-- **General (limiting) subdifferential `∂ψ`** on `ℝᵐ × ℝⁿ`.
Royset, Chen & Eckstrand, arXiv:2204.04762v4, §5, p.24: "For a function ψ : ℝⁿ → R̄ and a point x at which it is finite, the set of
subgradients of ψ at x is denoted by ∂ψ(x). We set ∂ψ(x) = ∅ for other x. … These concepts are
understood in the general sense of [51]." ([51] is Rockafellar–Wets, Definition 8.3.)

**Formalization Note.** The published `NonconvexSplitting.Shared.LimitingSubdiff` (limits of regular
subgradients along `zᵏ → z` with `ψ(zᵏ) → ψ(z)`) is taken on `EuclideanSpace ℝ (Fin m ⊕ Fin n)`
and pulled back by `jointEuclid`. That definition excludes `ψ z = ⊤` only, so `ψ z ≠ ⊥` is added:
`∂ψ z = ∅` wherever `ψ` is not finite. At a finite point the two agree with Definition 8.3. -/
def subdiff {m n : ℕ} (ψ : (Fin m → ℝ) × (Fin n → ℝ) → EReal)
    (z : (Fin m → ℝ) × (Fin n → ℝ)) : Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
  {v | ψ z ≠ ⊥ ∧ jointEuclid v ∈
    NonconvexSplitting.Shared.LimitingSubdiff (fun e => ψ (jointEuclid.symm e)) (jointEuclid z)}

end RockafellianRelax.Supplement


