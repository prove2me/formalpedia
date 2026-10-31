-- Prove2me | Definitions.Def_KingTerrain_NPHard_Complexity
-- name    : KingTerrain_NPHard_Complexity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T23:51:43.251722+00:00
-- url     : https://prove2.me/theorems/4ce73a5f-8af7-4398-8ee1-e7e79560bfdc
-- title:
--   NP-hardness under polynomial-time many-one reductions
-- statement:
--   A language $L$ is NP-hard if every language $K$ in NP over every finite nonempty alphabet admits a polynomial-time many-one reduction to $L$:
--
--   $$\forall K\in\mathrm{NP},\quad K\le_p L.$$
--
--   The shared CookPvsNP definitions give finite-state Turing-machine computation, polynomial running time on all input strings, and a yes/no equivalence on every input. This definition takes only the hardness clause; it does not assert that the target belongs to NP. It is independent of terrain geometry and is reusable for other decision problems.
-- source:
--   King and Krohn, Terrain Guarding is NP-Hard, DOI 10.1137/100791506, supplied PDF dated October 20, 2009, PDF p.2, Theorem 1; finite-machine conventions from the referenced CookPvsNP definition.

import Definitions.Def_CookPvsNP_defs

set_option autoImplicit false

namespace KingTerrain.NPHard

/-- The hardness clause alone: no membership-in-NP requirement on the target. -/
def IsNPHard {Sym : Type} (L : CookPvsNP.Lang Sym) : Prop :=
  ∀ (A : Type) [Fintype A] [Nonempty A] (K : CookPvsNP.Lang A),
    K ∈ CookPvsNP.NP A → CookPvsNP.PolyReducible K L

end KingTerrain.NPHard


