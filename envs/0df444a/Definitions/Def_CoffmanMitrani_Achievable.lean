-- Prove2me | Definitions.Def_CoffmanMitrani_Achievable
-- name    : CoffmanMitrani_Achievable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:17:15.91506+00:00
-- url     : https://prove2.me/theorems/80df1f2b-199d-4b55-ab94-6fbbb3605195
-- title:
--   Achievable performance vectors $H^*$
-- statement:
--   A vector $W \in \mathbb R^M$ is **achievable** if some scheduling strategy achieves it. The set of achievable vectors is the paper's $H^*$.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, p. 816 (proof of Theorem 2); §1, p. 813

import Mathlib
import Definitions.Def_CoffmanMitrani_IsStrategy
import Definitions.Def_CoffmanMitrani_Achieves

namespace CoffmanMitrani

/-- **Achievable performance vectors (the set `H*`).**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, p. 816, proof of Theorem 2: "If H* denotes the set of all achievable performance vectors";
p. 813: "Hereafter we shall talk simply of "scheduling strategies" meaning strategies confined to
the class defined in this section."

`Achievable D W` holds when some scheduling strategy achieves `W`. -/
def Achievable (D : Data) (W : Fin D.M → ℝ) : Prop :=
  ∃ S : Schedule D.M, IsStrategy D S ∧ Achieves D S W

end CoffmanMitrani


