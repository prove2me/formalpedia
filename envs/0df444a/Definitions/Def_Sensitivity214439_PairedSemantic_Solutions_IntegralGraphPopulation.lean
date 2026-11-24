-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_IntegralGraphPopulation
-- name    : Sensitivity214439_PairedSemantic_Solutions_IntegralGraphPopulation
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T19:45:38.734849+00:00
-- url     : https://prove2.me/theorems/39cce052-db92-4506-97eb-b84f63cdbfb5
-- title:
--   Integral minimum-edge function
-- statement:
--   For natural numbers $n,\alpha$, define
--
--   $$E(n,\alpha)=\alpha\binom{\lfloor n/\alpha\rfloor}{2}
--   +(n\bmod\alpha)\lfloor n/\alpha\rfloor.$$
--
--   For $\alpha>0$, this is the exact lower edge count for a graph on $n$ vertices with independence number at most $\alpha$, attained by distributing vertices as evenly as possible among $\alpha$ disjoint cliques. Natural-number division and remainder provide the total definition also at $\alpha=0$.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/IntegralGraphPopulation.lean lines 11–12; SHA256 9d86c4eb9053c08d7ec4547f7f2bf448c9e34dc489207e5d5db311e45b93c7ee; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SensitivityGraphPopulation
end SensitivityGraphPopulation
namespace SimpleGraph
end SimpleGraph



/-! The exact integral Turán lower edge count used by the source population tables. -/
namespace SensitivityGraphPopulation

noncomputable section
open scoped Classical
open SimpleGraph
set_option autoImplicit false

def minimumEdges (n alpha : ℕ) : ℕ :=
  alpha * (n / alpha).choose 2 + (n % alpha) * (n / alpha)












end
end SensitivityGraphPopulation


