-- Prove2me | Definitions.Def_MemQueryFeas_Vec
-- name    : MemQueryFeas_Vec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:39.125193+00:00
-- url     : https://prove2.me/theorems/1e2b2af0-3ef5-4201-84df-69d9ead1e656
-- title:
--   The space $\mathbb R^d$
-- statement:
--   The ambient space of the feasibility problem is $\mathbb R^d$ with its Euclidean inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$. Queries are points of the unit ball $B_d(0,1)$ and separating hyperplanes are given by their normals $g\in\mathbb R^d$.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`; coordinates are indexed from $0$.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Problem setup, p.3 (PDF p.4)

import Mathlib

namespace MemQueryFeas

/-- **The ambient space `ℝ^d`.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Problem setup, p.3 (PDF p.4): queries lie in the unit
ball `B_d(0,1)` of `ℝ^d` and separating hyperplanes have normals `g_t ∈ ℝ^d`.

**Formalization Note.** `ℝ^d` is `EuclideanSpace ℝ (Fin d)`, with the Euclidean inner product and
norm; coordinates are indexed by `Fin d` (0-based). -/
abbrev Vec (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

end MemQueryFeas


