-- Prove2me | Definitions.Def_TeschlODE_Planar_IsTransversalArc
-- name    : TeschlODE_Planar_IsTransversalArc
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T15:08:22.937973+00:00
-- url     : https://prove2.me/theorems/5f4c228f-9cc9-484c-9324-e787634dad42
-- title:
--   Arc Σ transversal to a planar vector field (§7.3)
-- statement:
--   Let $M \subseteq \mathbb{R}^2$ and $f = (f_1, f_2)$ a vector field on $M$. An **arc** $\Sigma = s(J)$ is a one-dimensional submanifold given by a map $s$ on an open interval $J$ with $\dot s \neq 0$; the parameter orders its points. It is **transversal** to $f$ if
--   $$\dot s_1(t)\, f_2(s(t)) - \dot s_2(t)\, f_1(s(t)) \neq 0 \qquad \text{for all } t \in J .$$
--
--   Transversal arcs through regular points are the local sections along which the planar proofs of §7.3 compare successive returns of an orbit.
--
--   **Formalization Note.** $s$ is taken $C^1$ on $J$ (the book says "smooth"; $C^1$ is a wider class, so statements quantified over all transversal arcs are at least as strong as the book's). "Submanifold" is encoded as: $s$ restricted to $J$ is a topological embedding (in particular injective). The arc is required to lie in $M$, where $f$ is defined. Coordinates `0, 1` are the book's $1, 2$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), pp. 220–221, §7.3

import Mathlib

namespace TeschlODE.Planar

/-- Teschl, §7.3, pp. 220–221: `Σ = s(J)` is an arc transversal to the planar vector field `f`
on `M ⊆ ℝ²`. The arc is given by a map `s` on an open interval `J` that is `C¹` on `J` (the book
says "smooth"; `C¹` is taken), is a topological embedding of `J` (the book's "submanifold of
dimension one"; in particular `s` is injective on `J`, so the parameter orders the points of `Σ`),
has `ṡ ≠ 0`, lies in `M`, and is transversal: `ṡ₁(t) f₂(s(t)) − ṡ₂(t) f₁(s(t)) ≠ 0` for all
`t ∈ J` (coordinates `0, 1` are the book's `1, 2`). -/
def IsTransversalArc (f : (Fin 2 → ℝ) → Fin 2 → ℝ) (M : Set (Fin 2 → ℝ)) (J : Set ℝ)
    (s : ℝ → Fin 2 → ℝ) : Prop :=
  IsOpen J ∧ J.OrdConnected ∧ J.Nonempty ∧ ContDiffOn ℝ 1 s J ∧
    Topology.IsEmbedding (fun t : J => s t) ∧ (∀ t ∈ J, s t ∈ M) ∧
    ∀ t ∈ J, deriv s t ≠ 0 ∧ deriv s t 0 * f (s t) 1 - deriv s t 1 * f (s t) 0 ≠ 0

end TeschlODE.Planar


