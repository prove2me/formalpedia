-- Prove2me | Definitions.Def_Supermodularity_Cooperative_IsTotallyLargeCore
-- name    : Supermodularity_Cooperative_IsTotallyLargeCore
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:01:47.797587+00:00
-- url     : https://prove2.me/theorems/13a9e7d3-a6e5-4f53-9550-1a8023dbde5e
-- title:
--   Section 5.1 - a totally large core
-- statement:
--   A cooperative game $(N,f)$ has a **totally large core** (p. 209) if the core of *every* subgame
--   $(U,f)$, $U \subseteq N$, is large.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 209, Section 5.1

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_IsLargeCore

namespace Supermodularity.Cooperative

/-- `IsTotallyLargeCore f` says the cooperative game with characteristic function
`f` has a totally large core (Topkis p. 209): the core of every subgame `(U, f)`,
for every coalition `U ⊆ Fin n`, is large. -/
def IsTotallyLargeCore {n : ℕ} (f : Finset (Fin n) → ℝ) : Prop :=
  ∀ U : Finset (Fin n), IsLargeCore U f

end Supermodularity.Cooperative


