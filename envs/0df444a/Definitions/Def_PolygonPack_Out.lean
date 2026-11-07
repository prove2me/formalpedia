-- Prove2me | Definitions.Def_PolygonPack_Out
-- name    : PolygonPack_Out
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:55:05.858435+00:00
-- url     : https://prove2.me/theorems/e7f4e131-36a7-4e0c-8f3c-fd9c01ea7064
-- title:
--   Algorithm output: exact poses of the selected polygons
-- statement:
--   An **output** is a list of entries $(k,a,b,x,y)$, where $k$ is the index of a polygon and $a,b,x,y$ are algebraic number descriptions. The output **selects** the set of indices it names. It is **sound** for an instance if the indices are distinct and in range and there are poses that pack the selected set, with each entry denoting the four numbers of the pose of its polygon.
--
--   A sound output is thus an exact description of a feasible packing, which is what the paper's algorithms return.
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), §2.7, p.13

import Mathlib
import Definitions.Def_PolygonPack_Instance
import Definitions.Def_PolygonPack_Pose
import Definitions.Def_PolygonPack_Packs
import Definitions.Def_PolygonPack_AlgNum

namespace PolygonPack

/-- **Algorithm output.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), §2.7, p.13: "Placements are returned as exact real algebraic numbers of
polynomial description length."

An output is a list of entries `(k, a, b, x, y)`: polygon `k` is packed with the pose whose four numbers
are the algebraic numbers `a, b, x, y`. `out.indexSet I` is the selected set. `out.Sound I`: the indices
are distinct and in range, and there are poses that pack the selected set and that the entries denote.

**Formalization Note.** Repeated indices are excluded by `Nodup`, so the profit of the selected set is
not double counted. A subset without placements would drop the clause of p.13. -/
abbrev Out : Type := List (ℕ × AlgNum × AlgNum × AlgNum × AlgNum)

/-- The polygon indices of an output. -/
def Out.indices (out : Out) : List ℕ := out.map Prod.fst

/-- The set of polygons an output selects. -/
def Out.indexSet (out : Out) (I : Instance) : Finset (Fin I.n) :=
  Finset.univ.filter (fun i => i.val ∈ out.indices)

/-- The output denotes a feasible packing of the polygons it selects. -/
def Out.Sound (out : Out) (I : Instance) : Prop :=
  out.indices.Nodup ∧ (∀ k ∈ out.indices, k < I.n) ∧
    ∃ T : Fin I.n → Pose, Packs I (out.indexSet I) T ∧
      ∀ e ∈ out, ∀ hk : e.1 < I.n,
        e.2.1.Denotes (T ⟨e.1, hk⟩).a ∧ e.2.2.1.Denotes (T ⟨e.1, hk⟩).b ∧
          e.2.2.2.1.Denotes (T ⟨e.1, hk⟩).x ∧ e.2.2.2.2.Denotes (T ⟨e.1, hk⟩).y

end PolygonPack


