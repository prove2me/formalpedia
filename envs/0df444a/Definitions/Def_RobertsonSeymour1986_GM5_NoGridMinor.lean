-- Prove2me | Definitions.Def_RobertsonSeymour1986_GM5_NoGridMinor
-- name    : RobertsonSeymour1986_GM5_NoGridMinor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:52:24.529486+00:00
-- url     : https://prove2.me/theorems/7f53880a-4256-447b-aac9-75d651d917d9
-- title:
--   The class $\mathcal F_\theta$ of graphs with no $\theta$-grid minor
-- statement:
--   For an integer $\theta$, let $\mathcal F_\theta$ be the class of all graphs with no minor isomorphic to the $\theta$-grid. This file defines the predicate "$G\in\mathcal F_\theta$".
--
--   Throughout Sections 3–7 of Graph Minors V, $\theta$ is a fixed even integer with $\theta\ge 6$, and the results are about graphs in $\mathcal F_\theta$.
--
--   **Formalization Note** The standing assumption "$\theta$ even, $\theta\ge 6$" is not built into this predicate; every theorem that uses $\mathcal F_\theta$ assumes it explicitly.
-- source:
--   Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), Sect. 2, p. 95 (PDF p. 4), definition of 𝓕_θ after (2.1); DOI 10.1016/0095-8956(86)90030-4

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsMinor
import Definitions.Def_RobertsonSeymour1986_GM5_grid

namespace RobertsonSeymour1986.GM5

/-- Membership in the class `𝓕_θ`: `G` has no minor isomorphic to the `θ`-grid.

Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986),
Sect. 2, p. 95 (PDF p. 4), unnumbered: "Throughout the rest of the paper, θ is a fixed even integer
with θ ≥ 6. Let 𝓕_θ be the class of all graphs with no minor isomorphic to the θ-grid."

`NoGridMinor θ G` is "`G ∈ 𝓕_θ`".

**Formalization Note** The standing assumption "θ even, θ ≥ 6" is not part of this definition; every
theorem that uses `𝓕_θ` carries it as the hypotheses `Even θ` and `6 ≤ θ`. -/
def NoGridMinor {V : Type} (θ : ℕ) (G : SimpleGraph V) : Prop :=
  ¬ IsMinor (grid θ) G

end RobertsonSeymour1986.GM5


