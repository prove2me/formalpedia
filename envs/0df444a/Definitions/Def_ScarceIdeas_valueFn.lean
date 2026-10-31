-- Prove2me | Definitions.Def_ScarceIdeas_valueFn
-- name    : ScarceIdeas_valueFn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:16:58.567993+00:00
-- url     : https://prove2.me/theorems/a5d48b96-c6da-4c4c-8131-f802171c8b73
-- title:
--   Value function $V(\phi)=\sup_u J(\phi,u)$
-- statement:
--   The **value function** is the maximal expected social welfare from state $\phi$:
--
--   $$V(\phi)=\sup\{J(\phi,u): u\text{ admissible}\}.$$
--
--   It is the object of the HJB equation (19), of the relation (22), and of Theorem 3.
--
--   **Formalization Note** A real supremum; the set is nonempty and bounded, so the value is genuine. $V$ is not defined through the HJB equation or (22).
-- source:
--   Basov, Erkal, Minehart, Scotchmer, Scarcity of Ideas and Optimal R&D Policy, SSRN 4628270, §4.2, (16)–(17), pp.20–21

import Mathlib
import Definitions.Def_ScarceIdeas_IsAdmissible
import Definitions.Def_ScarceIdeas_welfare

namespace ScarceIdeas

/-- **Value function `V(ϕ)`.**
Basov, Erkal, Minehart, Scotchmer, *Scarcity of Ideas and Optimal R&D Policy*, SSRN 4628270,
§4.2, (16)–(17), pp.20–21: the maximal expected social welfare from state `ϕ`,

$$V(\phi)=\sup_{u\ \text{admissible}} J(\phi,u).$$

**Formalization Note** A real `sSup` over the image of the admissible policies. The set is
nonempty (constant policies) and bounded (`|J| ≤ max(v/r − c̲, c̄ − v/r)`, because the claim-time
density integrates to at most `1`), so the supremum is genuine. `V` is the supremum, not a
solution of the HJB equation or of (22): those are theorems of the mission. -/
noncomputable def valueFn (r v cL cH : ℝ) (f h0 : ℝ → ℝ) (ϕ : ℝ) : ℝ :=
  sSup ((fun u => welfare r v cL f h0 ϕ u) '' {u | IsAdmissible cL cH u})

end ScarceIdeas


