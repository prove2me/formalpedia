-- Prove2me | Definitions.Def_VertexSampleCSP_supportFn
-- name    : VertexSampleCSP_supportFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:31.363336+00:00
-- url     : https://prove2.me/theorems/7f21e415-9300-4a32-92d6-bb3819b3dddb
-- title:
--   Support function $h_U$ of a set in Euclidean space
-- statement:
--   The **support function** of a nonempty compact set $U\subseteq\mathbb R^D$ is
--
--   $$h_U(u)=\max_{z\in U}\langle u,z\rangle.$$
--
--   It turns Minkowski sums into pointwise sums and so reduces Hausdorff distances between sums of polytopes to suprema of real-valued functions.
--
--   **Formalization Note** Defined on `EuclideanSpace ℝ ι` for a finite index type `ι`, as the real supremum of the image. On a nonempty compact set this is the maximum; on an empty or unbounded set it is the default value $0$, and every statement of the mission applies it to nonempty compact sets only.
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), Appendix A, "Support functions", p.13 (PDF p.15)

import Mathlib

open scoped InnerProductSpace

namespace VertexSampleCSP

/-- **Support function `h_U`.** Chang, *Optimal Vertex Sampling for Constraint Satisfaction
Problems*, STOC 2027 submission (manuscript sha256 1e0edd23…), Appendix A, "Support functions",
p.13 (PDF p.15): "The support function of a nonempty compact set U ⊆ ℝ^D is hU(u) = max_{z∈U}⟨u, z⟩."

`supportFn U u = sup_{z ∈ U} ⟨u, z⟩` on the Euclidean space `ℝ^ι` of a finite index type `ι`.

**Formalization Note.** Written as `sSup` of the image of `z ↦ ⟨u, z⟩` on `U`. For `U` nonempty and
compact the image is nonempty and compact, so this is the printed maximum. On an empty or unbounded
`U` the real `sSup` is the junk value `0`; every statement using `supportFn` applies it to nonempty
compact sets only (the convex hulls of finitely many points, with `q ≥ 1`). -/
noncomputable def supportFn {ι : Type*} [Fintype ι] (U : Set (EuclideanSpace ℝ ι))
    (u : EuclideanSpace ℝ ι) : ℝ :=
  sSup ((fun z => ⟪u, z⟫_ℝ) '' U)

end VertexSampleCSP


