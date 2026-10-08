-- Prove2me | Definitions.Def_SmoothedSimplex_Shadow_ang
-- name    : SmoothedSimplex_Shadow_ang
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:47:03.026792+00:00
-- url     : https://prove2.me/theorems/fdc4d3af-9d41-44f3-a4a2-9d38511fb459
-- title:
--   Definition 4.0.2 — $\mathrm{ang}(q,S)$
-- statement:
--   For a vector $q\in\mathbb R^d$ and a set $S\subseteq\mathbb R^d$,
--
--   $$
--   \mathrm{ang}(q,S)=\min_{x\in S}\ \mathrm{angle}(q,x),\qquad \mathrm{ang}(q,\emptyset)=\infty,
--   $$
--
--   where $\mathrm{angle}(q,x)\in[0,\pi]$ is the angle between $q$ and $x$ at the origin. It measures how close the ray through $q$ comes to the set $S$.
--
--   **Formalization Note** The value lies in $[0,\infty]$, so the empty set receives $\infty$ as in the paper. The minimum is written as an infimum; on the compact sets to which the paper applies it (faces of simplices not containing the origin) it is attained.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Definition 4.0.2, printed p. 38 (PDF p. 38)

import Mathlib

namespace SmoothedSimplex.Shadow

/-- `ang(q, S)` (Spielman & Teng, arXiv:cs/0111050v7, Definition 4.0.2, printed p. 38,
PDF p. 38): for a vector `q` and a set `S`, `ang(q, S) = min_{x∈S} angle(q, x)`, and
`ang(q, ∅) = ∞`.

**Formalization Note.** The value lies in `[0, ∞]` (`ℝ≥0∞`), so the empty set gets `∞` exactly as
in the paper (a real infimum would give the junk value `0`). `angle(q, x)` is Mathlib's
`InnerProductGeometry.angle q x ∈ [0, π]`. The minimum is written as an infimum; on the compact
sets the paper applies it to (faces of simplices not containing `0`) it is attained. -/
noncomputable def ang {d : ℕ} (q : EuclideanSpace ℝ (Fin d))
    (S : Set (EuclideanSpace ℝ (Fin d))) : ENNReal :=
  ⨅ x ∈ S, ENNReal.ofReal (InnerProductGeometry.angle q x)

end SmoothedSimplex.Shadow


