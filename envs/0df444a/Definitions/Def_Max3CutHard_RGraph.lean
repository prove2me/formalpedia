-- Prove2me | Definitions.Def_Max3CutHard_RGraph
-- name    : Max3CutHard_RGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:45.152489+00:00
-- url     : https://prove2.me/theorems/805d5042-a829-4836-b559-8e62eaceb490
-- title:
--   A real-weighted graph
-- statement:
--   A **weighted graph** on a vertex set $V$ is a finite list of edges $\{a,b\}$ with weights $w_{ab}\in\mathbb R$; parallel edges are allowed and their weights add.
--
--   The source's graphs have non-negative weights; that condition is the separate predicate *non-negative*.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, Cuts, p.4

import Mathlib

namespace Max3CutHard

/-- **A real-weighted graph on a vertex type `V`.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, Cuts, p.4: "A (weighted)
graph `G = (V, E, w)`".

**Formalization Note.** A list of edges `((a, b), w_ab)`; parallel edges are allowed (their weights
add). Non-negativity of the weights is the separate predicate `IsNonneg`. -/
abbrev RGraph (V : Type) : Type := List ((V × V) × ℝ)

end Max3CutHard


