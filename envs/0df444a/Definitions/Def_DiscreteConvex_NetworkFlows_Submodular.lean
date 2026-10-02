-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlows_Submodular
-- name    : DiscreteConvex_NetworkFlows_Submodular
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:13:56.332052+00:00
-- url     : https://prove2.me/theorems/99b3f816-a874-4222-932c-34d9eb481a94
-- title:
--   Submodularity of an $\mathbb R\cup\{+\infty\}$-valued set function
-- statement:
--   A set function $g : 2^V \to \mathbb R \cup \{+\infty\}$ is **submodular** if $g(X) + g(Y) \ge g(X \cup Y) + g(X \cap Y)$ for all $X, Y \subseteq V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.247.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.247

import Mathlib

/-!
Submodularity of a `ℝ ∪ {+∞}`-valued set function, in `DiscreteConvex.NetworkFlows`.
-/

namespace DiscreteConvex.NetworkFlows

/-- A set function `g : 2^V → ℝ ∪ {+∞}` is **submodular** if
`g(X) + g(Y) ≥ g(X ∪ Y) + g(X ∩ Y)` for all `X, Y ⊆ V`. -/
def Submodular {V : Type*} [DecidableEq V] (g : Finset V → WithTop ℝ) : Prop :=
  ∀ X Y : Finset V, g X + g Y ≥ g (X ∪ Y) + g (X ∩ Y)

end DiscreteConvex.NetworkFlows


