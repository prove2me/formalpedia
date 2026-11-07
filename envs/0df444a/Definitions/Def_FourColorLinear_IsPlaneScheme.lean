-- Prove2me | Definitions.Def_FourColorLinear_IsPlaneScheme
-- name    : FourColorLinear_IsPlaneScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:52:47.93223+00:00
-- url     : https://prove2.me/theorems/39513708-8d53-43b4-9b24-a0a00a8948a3
-- title:
--   Plane graphs and plane triangulations as rotation systems
-- statement:
--   A combinatorial embedding of a simple graph $G$ on the sphere is a rotation system with no twisted edge and Euler genus $0$: the published embedding scheme with its signature constantly false. Tracing a facial walk means traversing a dart $d$ and continuing with the rotation-successor of the reversed dart; write $\varphi(d)$ for that next dart. The orbits of $\varphi$ are the faces.
--
--   A **plane triangulation** is such a graph that is connected, has at least $3$ vertices, and has $\varphi^3 = \mathrm{id}$ on darts: "a (simple) graph embedded in the 2-sphere, all of whose faces are triangles".
--
--   The **rotation lists** of a plane graph are adjacency lists in which each vertex lists its neighbours in rotation order, from an arbitrary first neighbour. They are the input of the algorithms on triangulations (Theorems 3, 7, 8).
-- source:
--   Inoue, Kawarabayashi, Miyashita, Mohar, Thomassen, Thorup, Four-Coloring Planar Graphs in Linear Time, arXiv:2610.39753 (held version, sha256 4dce39c5…), §1.1, pp.2–3

import Mathlib
import Definitions.Def_PlanarQueue_Genus_EulerGenus
import Definitions.Def_FourColorLinear_encodeAdj

open PlanarQueue.Genus

namespace FourColorLinear

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A combinatorial embedding on the sphere: a rotation system with no twisted edge and Euler
genus 0.  This is the "plane graph" of arXiv:2610.39753 (held version, sha256 4dce39c5…), pp.2–3. -/
def IsPlaneScheme (S : EmbeddingScheme G) : Prop :=
  (∀ d, S.sig d = false) ∧ S.eulerGenus = 0

/-- One step along a facial walk: traverse `d`, then continue with the rotation-successor of the
reversed dart. The orbits of this permutation of darts are the faces. -/
def faceNext (S : EmbeddingScheme G) (d : G.Dart) : G.Dart := S.rot d.symm

/-- Plane triangulation, arXiv:2610.39753, p.2: "a (simple) graph embedded in the 2-sphere, all of
whose faces are triangles".

**Formalization Note** Connected with at least 3 vertices, and every facial walk has length 3:
`faceNext` iterated three times is the identity on darts. A cycle of length 3 in a simple graph has
no shorter facial period, so every face really is a triangle. -/
def IsPlaneTriangulation (S : EmbeddingScheme G) : Prop :=
  IsPlaneScheme S ∧ G.Connected ∧ 3 ≤ Fintype.card V ∧ ∀ d, (faceNext S)^[3] d = d

/-- The input of Theorems 3, 6, 7, 8 of arXiv:2610.39753: for each vertex, its neighbours in rotation
order, from an arbitrary first neighbour; the words are `encodeAdj rl`. -/
def IsRotLists {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (S : EmbeddingScheme G)
    (rl : Fin n → List (Fin n)) : Prop :=
  AdjacencyLists G rl ∧
    ∀ d : G.Dart, ∃ i, (rl d.fst)[i]? = some d.snd ∧
      (rl d.fst)[(i + 1) % (rl d.fst).length]? = some (S.rot d).snd

end FourColorLinear


