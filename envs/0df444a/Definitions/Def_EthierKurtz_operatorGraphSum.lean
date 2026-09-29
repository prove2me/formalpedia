-- Prove2me | Definitions.Def_EthierKurtz_operatorGraphSum
-- name    : EthierKurtz_operatorGraphSum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:41:59.463789+00:00
-- url     : https://prove2.me/theorems/232806eb-861c-482a-b780-cc1edd6e1944
-- title:
--   Sum of operator graphs
-- statement:
--   The graph sum at a common input, with the domain intersection implicit in graph membership.
-- source:
--   Ethier and Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 1, pp. 16, 37.

import Mathlib

open Filter
open scoped Topology

namespace EthierKurtz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Operator addition on the intersection of domains, rather than addition
of arbitrary graph pairs. Also defined for graph closures (Section 7, p. 37). -/
def operatorGraphSum (G H : Set (E × E)) : Set (E × E) :=
  {p | ∃ y z : E, (p.1, y) ∈ G ∧ (p.1, z) ∈ H ∧ p.2 = y + z}

end EthierKurtz


