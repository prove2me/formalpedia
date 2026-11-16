-- Prove2me | Definitions.Def_ApproxEquilibriumCost_General_Supplement_SeriesParallel
-- name    : ApproxEquilibriumCost_General_Supplement_SeriesParallel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:44:34.11779+00:00
-- url     : https://prove2.me/theorems/d9d37b48-5489-4dc0-91e2-d39b7cf113c2
-- title:
--   §2.3 — series-parallel networks, edge paths and depth
-- statement:
--   A two-terminal directed series-parallel network $N$ is built from a single directed edge by arbitrary finite series and parallel compositions. Every leaf is a distinct edge, including parallel edges. The resource labels are $\mathrm{Fin}(\operatorname{edgeCount}N)$. Its depth is
--
--   $$h_{\mathrm{edge}}=1,\qquad h_{A;B}=h_A+h_B,\qquad h_{A\parallel B}=\max\{h_A,h_B\}.$$
--
--   The paths of an edge form the singleton family containing that edge. A series composition joins every left-child path with every right-child path, on disjoint edge labels; a parallel composition takes the union of the two embedded path families. These are exactly all directed terminal paths: series forces passage through the cut vertex, and parallel permits no switch between disjoint child interiors. In these acyclic graphs each path is determined by its edge set. The family and all its members are nonempty. The general network term is reused from the published ThinFlowSP.Breakpoints.SPTerm, with exactly the same three constructors and no thin-flow assumptions. This module adds only its edge enumeration, path family and depth for the routing interface.
-- source:
--   Yu Cheng, Tianle Jiang, STOC 2027 submission #438 (October 2026), How Much Can Approximate Equilibria Change the Social Cost of Selfish Routing?, §2.3, printed p.9 = PDF p.9 (offset 0). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/438.pdf

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Network

noncomputable section

namespace ApproxEquilibriumCost.General.Supplement

/-- Section 2.3, printed/PDF p.9: reuse the published general
two-terminal series-parallel term, with no dynamic-flow assumptions.
Its `arc`, `series`, `par` constructors are exactly the source's rules;
Kaiser Definition 28, arXiv:2002.11428v2 p.18 uses the same convention. -/
abbrev SPNetwork := ThinFlowSP.Breakpoints.SPTerm

/-- Leaves are distinct resource edges, enumerated from left to right. -/
def edgeCount : SPNetwork → ℕ
  | .arc => 1
  | .series A B => edgeCount A + edgeCount B
  | .par A B => edgeCount A + edgeCount B

/-- Maximum number of edges on a terminal-to-terminal path, not tree height. -/
def depth : SPNetwork → ℕ
  | .arc => 1
  | .series A B => depth A + depth B
  | .par A B => max (depth A) (depth B)

/-- All directed source-to-sink paths as finite sets of distinctly labelled edges.
Series concatenates one path from each child; parallel chooses a child.
This is exactly the path family of the graph built by Section 2.3: the
series cut vertex forces traversal of both children, while in parallel
the child interiors are disjoint and there is no way to switch children.
These directed acyclic graphs have a unique path order for each such edge
set, so forgetting order identifies no distinct paths. Both the family
and each member are nonempty, by the three recursive cases. -/
def paths : (N : SPNetwork) → Finset (Finset (Fin (edgeCount N)))
  | .arc => {{⟨0, by decide⟩}}
  | .series A B =>
      (paths A).biUnion fun P => (paths B).image fun Q =>
        P.image (Fin.castAdd (edgeCount B)) ∪ Q.image (Fin.natAdd (edgeCount A))
  | .par A B =>
      ((paths A).image fun P => P.image (Fin.castAdd (edgeCount B))) ∪
      ((paths B).image fun Q => Q.image (Fin.natAdd (edgeCount A)))

end ApproxEquilibriumCost.General.Supplement


