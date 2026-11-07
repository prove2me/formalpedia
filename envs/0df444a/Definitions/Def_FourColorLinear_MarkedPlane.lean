-- Prove2me | Definitions.Def_FourColorLinear_MarkedPlane
-- name    : FourColorLinear_MarkedPlane
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:53:39.126406+00:00
-- url     : https://prove2.me/theorems/435f9398-0266-4ae3-85e3-3cd7d9bc0953
-- title:
--   Plane graphs with marked boundary walks
-- statement:
--   A plane graph $H$ together with **hole information** for regions $R_0,\dots,R_d$: for each dart and each $j$, whether the dart runs along a hole walk $W_k$ of $\partial R_j$, which $k$, and whether it is the start dart of that walk. This is a constant number of bits per edge.
--
--   Two marked plane graphs are the same if a rotation-preserving isomorphism respects all marks. Such an isomorphism carries hole walks to hole walks, with the enumeration of vertices and edges they induce.
-- source:
--   Inoue, Kawarabayashi, Miyashita, Mohar, Thomassen, Thorup, Four-Coloring Planar Graphs in Linear Time, arXiv:2610.39753 (held version, sha256 4dce39c5…), §2.1, pp.12–13

import Mathlib
import Definitions.Def_FourColorLinear_IsPlaneScheme

open PlanarQueue.Genus

namespace FourColorLinear

/-- A plane graph `H` with the boundaries of a region `R₀` and its children `R₁, …, R_d` marked in it,
arXiv:2610.39753 (held version, sha256 4dce39c5…), pp.12–13: "we just need to store for each edge in
∂R which boundary W_k it belongs to, and whether it is the start edge u_kv_k and, if so, with what
orientation. We call this information the hole information".

**Formalization Note** The marks sit on darts, so an edge on two walks and the orientation of a start
edge are both visible: `mark x j = some (k, st)` says the dart `x` runs along the walk `W_k` of
`∂R_j`, and `st` says it is the start dart of that walk. There are at most `h` holes per region. -/
structure MarkedPlane (d h : ℕ) where
  /-- number of vertices -/
  n : ℕ
  /-- the graph `H` -/
  G : SimpleGraph (Fin n)
  [dec : DecidableRel G.Adj]
  /-- its plane embedding -/
  S : EmbeddingScheme G
  plane : IsPlaneScheme S
  /-- the hole information of each dart -/
  mark : G.Dart → Fin (d + 1) → Option (Fin h × Bool)

attribute [instance] MarkedPlane.dec

/-- Two marked plane graphs are the same: a rotation-preserving isomorphism respecting all marks,
hence carrying hole walks to hole walks with their enumeration. -/
def MarkedPlane.Iso {d h : ℕ} (x y : MarkedPlane d h) : Prop :=
  ∃ e : x.G ≃g y.G,
    (∀ a : x.G.Dart, e.toHom.mapDart (x.S.rot a) = y.S.rot (e.toHom.mapDart a)) ∧
      ∀ a : x.G.Dart, y.mark (e.toHom.mapDart a) = x.mark a

end FourColorLinear


