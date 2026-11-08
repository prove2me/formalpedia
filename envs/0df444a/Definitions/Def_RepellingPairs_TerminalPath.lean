-- Prove2me | Definitions.Def_RepellingPairs_TerminalPath
-- name    : RepellingPairs_TerminalPath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:03:33.955549+00:00
-- url     : https://prove2.me/theorems/39922d07-d97f-4ca7-af61-6e41b2542042
-- title:
--   A path between two terminals
-- statement:
--   A **terminal path** of an OS instance is a pair of terminals with a path of $G$ between them. It is a unit, or a carrier, of the flow $F'$ of §3, which may use any paths. Trivial paths are allowed.
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), §3, p.7

import Mathlib
import Definitions.Def_RepellingPairs_Multigraph
import Definitions.Def_RepellingPairs_OSInstance

set_option autoImplicit false

namespace RepellingPairs

universe u v

/-- A path of the graph between two terminals, one unit (or one carrier) of the flow `F′` of §3, which
"may use any paths" (p.7). `src = tgt` is the trivial path at a terminal.
Chen, Pylyavskyy, Tan, arXiv:2607.02883 (version of October 23, 2026), §3, p.7. -/
structure TerminalPath {V : Type u} {E : Type v} {k : ℕ} (G : OSInstance V E k) where
  /-- First terminal. -/
  src : Fin k
  /-- Last terminal. -/
  tgt : Fin k
  /-- The path. -/
  path : G.graph.Path (G.term src) (G.term tgt)

end RepellingPairs


