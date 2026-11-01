-- Prove2me | Definitions.Def_CoupledLearning_IsUHC
-- name    : CoupledLearning_IsUHC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:37:27.28088+00:00
-- url     : https://prove2.me/theorems/b535364c-e5a4-4a99-83c9-6f15ee9e79bb
-- title:
--   Upper hemicontinuity of a correspondence on a domain
-- statement:
--   Let $X,Y$ be topological spaces, $D\subseteq X$ and $\Gamma:X\rightrightarrows Y$. Then $\Gamma$ is **upper hemicontinuous on $D$** if for every $x\in D$ and every open set $V\supseteq\Gamma(x)$ there is a neighbourhood $W$ of $x$ such that
--
--   $$\Gamma(x')\subseteq V\qquad\text{for all }x'\in W\cap D.$$
--
--   This is the continuity notion of Assumption 1.
--
--   **Formalization Note** This is the open-set definition, with no closed, compact or nonempty values. For non-compact values it differs from having a closed graph and from the $\varepsilon$-enlargement version.
-- source:
--   Wu, Amin, Ozdaglar, Convergence and Stability of Coupled Belief–Strategy Learning Dynamics in Continuous Games, arXiv:2206.05637v2, Assumption 1, p.9

import Mathlib

open Topology

namespace CoupledLearning

/-- Upper hemicontinuity of a correspondence `Γ : D ⇒ Y` on a domain `D ⊆ X` (the notion of
Assumption 1, arXiv:2206.05637v2, p.9): at every `x ∈ D`, for every open `V ⊇ Γ(x)` there is a
neighbourhood `W` of `x` with `Γ(x') ⊆ V` for all `x' ∈ W ∩ D`.

**Formalization Note.** This is the open-set definition. No closed, compact or nonempty values are
assumed: the paper does not assume them, and with non-compact values this notion differs from
closedness of the graph and from the `ε`-enlargement version. "Within `D`" is
`∀ᶠ x' in 𝓝[D] x`. -/
def IsUHC {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (D : Set X) (Γ : X → Set Y) :
    Prop :=
  ∀ x ∈ D, ∀ V : Set Y, IsOpen V → Γ x ⊆ V → ∀ᶠ x' in 𝓝[D] x, Γ x' ⊆ V

end CoupledLearning


