-- Prove2me | Definitions.Def_VDCyclePack_ShortCyclesMeet
-- name    : VDCyclePack_ShortCyclesMeet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:08:23.534968+00:00
-- url     : https://prove2.me/theorems/f83bd65e-d253-4625-8984-ca758b7c0790
-- title:
--   Condition (3): every cycle of length at most $aL$ meets $A=V(H)$
-- statement:
--   For a marked packing $H$, $A=V(H)$, and integers $a$, $L$, condition (3) says that every cycle of $G$ of length at most $aL$ has a vertex in $A$; equivalently, $\mathrm{girth}(G-A)>aL$, where a forest has girth $+\infty$.
--
--   The greedy construction of Section 6.1 yields a marked packing with this property, and Lemma 6.6 assumes it.
--
--   **Formalization Note** Stated in the paper's "every cycle of $G$ of length at most $aL$ meets $A$" form; Mathlib's `girth`, which is $0$ on forests, is not used.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), (3), p.18

import Mathlib
import Definitions.Def_VDCyclePack_cycles

namespace VDCyclePack

/-- **Condition (3): every cycle of length at most aL meets A = V(H).**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), (3), p.18: "The graph remaining when the procedure stops is exactly G − A, and it
contains no cycle of length at most aL. Equivalently, every cycle of G of length at most aL meets
A, and girth(G − A) > aL."

`ShortCyclesMeet G H a L` says every cycle `C` of `G` with `|C| ≤ a·L` has a vertex in `V(H)`.

**Formalization Note.** This is the paper's "every cycle of G of length at most aL meets A" form
of (3); it holds vacuously when `G − A` is a forest (girth `+∞`). Mathlib's `girth` (which is `0`
on forests) is not used. -/
def ShortCyclesMeet {V : Type*} [Fintype V] (G : SimpleGraph V) (H : G.Subgraph) (a L : ℕ) :
    Prop :=
  ∀ C ∈ cycles G, C.verts.ncard ≤ a * L → (C.verts ∩ H.verts).Nonempty

end VDCyclePack


