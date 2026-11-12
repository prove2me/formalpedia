-- Prove2me | Definitions.Def_MinorFreeOracle_LinearSpace_Graph
-- name    : MinorFreeOracle_LinearSpace_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:42:35.613458+00:00
-- url     : https://prove2.me/theorems/02ea65ca-7140-4d97-8ef5-e63eca89515c
-- title:
--   Simple weighted graphs and exclusion of a fixed minor
-- statement:
--   Let G be a finite weighted undirected edge-list graph. It is simple when no edge is a loop and no two different edges have the same unordered endpoint pair. Its underlying simple graph forgets edge weights and enumeration. A finite simple graph H is excluded as a minor when there is no branch-set minor model of H in that underlying graph.
--
--   These predicates put the source's simple graph convention on the published graph carrier. Nonnegative weights and connectedness are separate hypotheses, so zero weights remain permitted. Vertices are numbered by finite initial segments; this numbering changes no graph instance.
-- source:
--   Eunjin Oh, Linear-Space Exact Distance Oracle for Minor-Free Graphs, STOC 2027 submission #160 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/160.pdf, §3, PDF p.15 (printed p.13); graph conventions and branch-set minor definition

import Mathlib
import Definitions.Def_TenChallenges_Minor
import Definitions.Def_TZLevelsADO_Graph

namespace MinorFreeOracle.LinearSpace

/-- Oh, §3, PDF p.15: the source's undirected simple graph, on the published edge-list carrier.
The two orientations of an endpoint pair denote the same undirected edge. -/
def IsSimple (G : TZLevelsADO.Graph) : Prop :=
  (∀ e, G.src e ≠ G.dst e) ∧
  ∀ e f, ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
    (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f

/-- Forget weights and the enumeration of edges. Loops are removed. -/
def toSimpleGraph (G : TZLevelsADO.Graph) : SimpleGraph (Fin G.n) where
  Adj u v := u ≠ v ∧ ∃ e, (G.src e = u ∧ G.dst e = v) ∨
    (G.src e = v ∧ G.dst e = u)
  symm := ⟨by
    rintro u v ⟨hne, e, h | h⟩
    · exact ⟨hne.symm, e, Or.inr h⟩
    · exact ⟨hne.symm, e, Or.inl h⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

/-- Oh, §3, PDF p.15: exclude the given finite simple graph as a branch-set minor. -/
def MinorFree {h : ℕ} (G : TZLevelsADO.Graph) (H : SimpleGraph (Fin h)) : Prop :=
  ¬ Nonempty (SimpleGraph.Minor H (toSimpleGraph G))

end MinorFreeOracle.LinearSpace


