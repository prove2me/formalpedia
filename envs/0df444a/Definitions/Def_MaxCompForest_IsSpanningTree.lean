-- Prove2me | Definitions.Def_MaxCompForest_IsSpanningTree
-- name    : MaxCompForest_IsSpanningTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:34:16.473206+00:00
-- url     : https://prove2.me/theorems/36363316-0dc5-4d92-a1c3-234d790d9cb2
-- title:
--   Label-sensitive spanning tree
-- statement:
--   A set $T$ of edge labels of $G=(V,E)$ is a **spanning tree** when its edges connect all of $V$ and $|T|=|V|-1$.
--
--   Parallel labels are distinct objects: two parallel labels give two different spanning trees, each with its own weight.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), p.1

import Mathlib
import Definitions.Def_MaxCompForest_spanSub
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} [Fintype V]

/-- **`T` is the label set of a spanning tree**: its edges connect `V`, and `|T| + 1 = |V|`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), p.1.

**Formalization Note.** Stated on label sets, so that two parallel labels are two different trees. A
connected spanning edge set with `|V| − 1` labels is exactly a tree. -/
def IsSpanningTree (G : WGraph V E) (T : Finset E) : Prop :=
  (spanSub G T).Connected ∧ T.card + 1 = Fintype.card V

end MaxCompForest


