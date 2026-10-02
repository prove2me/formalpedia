-- Prove2me | Definitions.Def_TeschlODE_Stability_sublevelComponent
-- name    : TeschlODE_Stability_sublevelComponent
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T12:48:51.625216+00:00
-- url     : https://prove2.me/theorems/a78f8c5a-f9d3-4dc4-8434-fddbd41a45c1
-- title:
--   The set $S_\delta$: connected component of $\{x \in U : L(x) \le \delta\}$ containing $x_0$
-- statement:
--   Let $U \subseteq \mathbb{R}^n$, $L : U \to \mathbb{R}$, $x_0 \in \mathbb{R}^n$ and $\delta \in \mathbb{R}$. The set $S_\delta$ is the connected component of the sublevel set
--   $$\{x \in U : L(x) \le \delta\}$$
--   containing $x_0$.
--
--   **Formalization Note.** This is Mathlib's `connectedComponentIn`, which is the empty set when $x_0$ is not in the sublevel set (for a Liapunov function: when $\delta < 0$). Every theorem uses it with $\delta > 0$ or states closedness explicitly.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 201, §6.6, definition of S_δ

import Mathlib

namespace TeschlODE.Stability

/-- Teschl, §6.6, p. 201: `S_δ`, the connected component of `{x ∈ U | L(x) ≤ δ}` containing
`x₀` (empty when `x₀` is not in that set, e.g. for `δ < L x₀`). -/
def sublevelComponent {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n)))
    (L : EuclideanSpace ℝ (Fin n) → ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (δ : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  connectedComponentIn {x | x ∈ U ∧ L x ≤ δ} x₀

end TeschlODE.Stability


