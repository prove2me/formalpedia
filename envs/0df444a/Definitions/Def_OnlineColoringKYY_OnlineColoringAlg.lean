-- Prove2me | Definitions.Def_OnlineColoringKYY_OnlineColoringAlg
-- name    : OnlineColoringKYY_OnlineColoringAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:27:29.028017+00:00
-- url     : https://prove2.me/theorems/8ecca42b-faf8-493a-849c-77adcdf5a4de
-- title:
--   Deterministic online coloring algorithm
-- statement:
--   In the **online coloring problem** the vertices of an undirected graph arrive one by one. Immediately after a vertex arrives, together with all its edges to previously arrived vertices, the algorithm must assign it a color in $\mathbb N$.
--
--   A **deterministic online coloring algorithm** is given by a rule $A$ that, for every $m \ge 0$ and every graph $H$ on the vertex set $\{0, 1, \dots, m\}$ (the first $m+1$ arrivals, in order), returns the color
--   $$
--   A(m, H) \in \mathbb N
--   $$
--   of the newest vertex $m$. The algorithm sees the graph so far and nothing else; no computability or running-time condition is imposed, as the lower bound of the paper holds even with unlimited computation.
--
--   This is the object every result of the mission quantifies over. Properness (adjacent vertices get different colors) is the separate predicate *IsProper*.
--
--   **Formalization Note** The earlier colors of a deterministic algorithm are themselves functions of the earlier prefixes, so the color of the newest vertex as a function of the current prefix graph (`color : (m : ℕ) → SimpleGraph (Fin (m + 1)) → ℕ`) describes exactly the deterministic online algorithms. An algorithm that knows the final number of vertices in advance is a family of such rules, one for each $n$.
-- source:
--   Kawarabayashi–Yoneda–Yoneda, Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms, STOC 2027 submission (manuscript sha256 3d1eeea6…), Definition 3.1, printed p.10 (PDF p.12); Section 4.1, p.11 (PDF p.13)

import Mathlib

set_option autoImplicit false

namespace OnlineColoringKYY

/-- A **deterministic online coloring algorithm** (Kawarabayashi–Yoneda–Yoneda, *Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms*, STOC 2027 submission (manuscript sha256 3d1eeea6…), Definition 3.1, printed p.10 = PDF
p.12; Section 4.1, p.11 = PDF p.13). The vertices arrive one by one; immediately after a vertex
arrives, together with its edges to the earlier vertices, the algorithm assigns it a color in `ℕ`.

`color m H` is the color given to the `(m+1)`-st arriving vertex `Fin.last m` when the graph
induced on the first `m + 1` arrivals is `H : SimpleGraph (Fin (m + 1))`.

**Formalization Note** Vertex `i` of `Fin (m + 1)` is the `(i+1)`-st arrival. A deterministic
algorithm's earlier colors are themselves functions of the earlier prefixes, so taking the color of
the newest vertex as a function of the current prefix graph loses nothing: it is exactly "the
algorithm sees the graph so far (and its own past output) and nothing else". No computability or
cost condition is imposed (the paper's lower bound holds "even with unlimited computation"). An
algorithm that knows the final number of vertices `n` in advance is a family `n ↦ A n` of such
algorithms. Properness is a separate predicate, `IsProper`. -/
structure OnlineColoringAlg where
  /-- The color of the newest vertex `Fin.last m`, given the prefix graph on `Fin (m + 1)`. -/
  color : (m : ℕ) → SimpleGraph (Fin (m + 1)) → ℕ

end OnlineColoringKYY


