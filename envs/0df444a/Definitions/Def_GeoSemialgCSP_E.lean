-- Prove2me | Definitions.Def_GeoSemialgCSP_E
-- name    : GeoSemialgCSP_E
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:46:51.863235+00:00
-- url     : https://prove2.me/theorems/f97b3ab4-3072-497a-aa5d-38320f59cbf4
-- title:
--   Points of $\mathbb R^d$
-- statement:
--   The ambient space of the CSP is $\mathbb R^d$ with the Euclidean norm $\|\cdot\|_2$. A CSP over a domain $X\subseteq\mathbb R^d$ assigns a point of $\mathbb R^d$ to every variable.
--
--   This is the carrier of all predicates, assignments and distributions in the mission.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`, so `dist` is the Euclidean distance; coordinates are indexed $0,\dots,d-1$.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3 Setup, p.7 (PDF p.8)

import Mathlib

namespace GeoSemialgCSP

/-- **Points of `ℝ^d`.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3 Setup, printed p.7 (PDF p.8): the domain `X ⊆ ℝ^d`.

`E d` is `ℝ^d` with the Euclidean norm `‖·‖₂`, the norm of Definition 1.1 (2).

**Formalization Note.** `EuclideanSpace ℝ (Fin d)`; coordinates are 0-based (`Fin d`). -/
abbrev E (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

end GeoSemialgCSP


