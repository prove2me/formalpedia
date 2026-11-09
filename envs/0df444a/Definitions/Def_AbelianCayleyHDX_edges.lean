-- Prove2me | Definitions.Def_AbelianCayleyHDX_edges
-- name    : AbelianCayleyHDX_edges
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:25:33.645762+00:00
-- url     : https://prove2.me/theorems/cf9ef3a9-c5b4-4dd2-b096-4a303a534e37
-- title:
--   Edges of a two-dimensional complex given by its triangles
-- statement:
--   A pure two-dimensional simplicial complex is determined by its set $T$ of **triangles** (top faces, 3-element subsets of the vertex set); its faces are all subsets of triangles. Its **edges** (1-faces) are the 2-element subsets of the triangles of $T$.
--
--   **Formalization Note** The triangle set is a `Finset` of `Finset`s, so every face occurs once: the complex is simple by construction.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.2, p.8

import Mathlib
import Definitions.Def_ReplParity_Vec
open ReplParity (Vec)

namespace AbelianCayleyHDX

/-- **The edges of a two-dimensional complex given by its triangles** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.2, p.8:
the 1-faces of the downward closure of `X(2)`): the 2-element subsets of the triangles in `T`.

**Formalization Note** A pure two-dimensional complex is represented by its set `T` of top faces
(triangles); its faces are all subsets of members of `T`. A `Finset` of faces holds each face once,
so the complex is simple by construction. -/
def edges {n : ℕ} (T : Finset (Finset (Vec n))) : Finset (Finset (Vec n)) :=
  T.biUnion fun τ => τ.powersetCard 2

end AbelianCayleyHDX


