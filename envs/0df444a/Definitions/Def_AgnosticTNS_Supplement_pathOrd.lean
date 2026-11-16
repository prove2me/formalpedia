-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_pathOrd
-- name    : AgnosticTNS_Supplement_pathOrd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:31:42.417209+00:00
-- url     : https://prove2.me/theorems/1a606c4d-b774-4758-9f50-993041110c6d
-- title:
--   Labelled path $P^\pi_n$ of a linear ordering
-- statement:
--   For a linear ordering, i.e. a bijection $\pi:V\to[n]$, write $v_i=\pi^{-1}(i)$. The **labelled path** $P^\pi_n$ is the path $v_1 - v_2 - \cdots - v_n$: two vertices are adjacent exactly when their positions are consecutive.
--
--   **Formalization Note** Positions are $0$-based; $P^\pi_n$ is the pullback of the path graph $0-1-\cdots-(n-1)$ along $\pi$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Definition 6.1, p.48; Theorem 6.11, p.52

import Mathlib

namespace AgnosticTNS.Supplement

/-- **The labelled path `P^π_n`**, Definition 6.1, p.48 and Theorem 6.11, p.52 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)):
for a linear ordering (bijection) `π : V → [n]` with `v_i = π⁻¹(i)`, the path `v_1 − v_2 − ⋯ − v_n`.

**Formalization Note** `π : Equiv.Perm (Fin n)` sends a vertex to its position (0-based); two
vertices are adjacent iff their positions are consecutive, i.e. the pullback of
`SimpleGraph.pathGraph n` (the path `0 − 1 − ⋯ − (n−1)`) along `π`. -/
def pathOrd {n : ℕ} (π : Equiv.Perm (Fin n)) : SimpleGraph (Fin n) :=
  (SimpleGraph.pathGraph n).comap π

end AgnosticTNS.Supplement


