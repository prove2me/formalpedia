-- Prove2me | Definitions.Def_EthierKurtz_unboundedOperatorGraph
-- name    : EthierKurtz_unboundedOperatorGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:41:48.371302+00:00
-- url     : https://prove2.me/theorems/ed688009-94e5-40c4-a20d-3b0e735ca093
-- title:
--   Graph of an unbounded operator
-- statement:
--   The graph of a domain-restricted linear operator as a subset of the ambient product space.
-- source:
--   Ethier and Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 1, pp. 16, 37.

import Mathlib

open Filter
open scoped Topology

namespace EthierKurtz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The graph of a possibly unbounded linear operator in the ambient E × E,
so topological closure also allows the domain to grow (Chapter 1, p. 16). -/
def unboundedOperatorGraph (D : Submodule ℝ E) (A : D →ₗ[ℝ] E) : Set (E × E) :=
  ((LinearPMap.mk D A).graph : Set (E × E))

end EthierKurtz


