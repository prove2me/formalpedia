-- Prove2me | Definitions.Def_TwoConnSS_costB
-- name    : TwoConnSS_costB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:39.535306+00:00
-- url     : https://prove2.me/theorems/c36aa643-af33-489c-95ca-4a84dc6f7652
-- title:
--   The credit assignment B and $\mathrm{cost}_B$
-- statement:
--   Under **assignment B**, a 4-cycle component receives $4/5$ credit, a 5-cycle component $17/10$, every other 2EC component $2$, and a complex component $C$ receives
--   $$1 + b(C) + \ell(C)/5,$$
--   where $b(C)$ is the number of its 2EC blocks and $\ell(C)$ the number of its lonely vertices. Then $\mathrm{cost}_B(S) = |S| + \mathrm{cr}_B(S)$.
--
--   Assignment B is used by Algorithm B, which handles covers rich in 4-cycles.
--
--   **Formalization Note** Credits are exact rationals; isolated vertices (absent from covers for Algorithm B) get no credit.
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), §8.1.2, p.38

import Mathlib
import Definitions.Def_TwoConnSS_blocks

namespace TwoConnSS

open Classical

variable {V : Type*} [Fintype V]

/-- The credit of one component under assignment B (p.38). -/
noncomputable def compCrB (S : Finset (Sym2 V)) (C : Finset V) : ℚ :=
  if IsCycleComp S C 4 then 4 / 5
  else if IsCycleComp S C 5 then 17 / 10
  else if IsTwoECComp S C then 2
  else if IsComplexComp S C then 1 + ((blocksIn S C).card : ℚ) + ((lonely S C).card : ℚ) / 5
  else 0

/-- **The cost under assignment B**, `cost_B(S) = |S| + cr_B(S)`.
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), §8.1.2, p.38: "Under assignment B,
a 4-cycle receives 4/5 credit, a 5-cycle receives 17/10 credits, and any other 2EC component
receives two credits. A complex component C receives one component credit, one credit for each 2EC
block, and 1/5 credit for each lonely vertex. Its total contribution is 1 + b(C) + ℓ(C)/5. Set
costB(S) = |S| + crB(S)."

**Formalization Note.** Credits are exact rationals; an isolated vertex (which a cover for
Algorithm B never has) receives none. -/
noncomputable def costB (S : Finset (Sym2 V)) : ℚ :=
  (S.card : ℚ) + ∑ C ∈ comps S, compCrB S C

end TwoConnSS


