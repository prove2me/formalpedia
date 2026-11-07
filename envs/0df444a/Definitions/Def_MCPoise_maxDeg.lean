-- Prove2me | Definitions.Def_MCPoise_maxDeg
-- name    : MCPoise_maxDeg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:25:47.389205+00:00
-- url     : https://prove2.me/theorems/eb41c04d-70f8-46a9-b3a9-5c18d0979fe2
-- title:
--   Maximum degree of a graph
-- statement:
--   For a graph $H$ on a finite vertex set $V$, the **maximum degree** is
--   $$\Delta(H) = \max_{v \in V} \deg_H(v).$$
--   It equals $0$ when $V$ is empty. It is the first summand of the poise.
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Definition 1, p.3

import Mathlib

namespace MCPoise

/-- **Maximum degree** `max_{v∈V} deg_H(v)`.
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Definition 1, p.3.

**Formalization Note.** `Finset.sup` on `ℕ` is `0` over an empty vertex set, which is the value `n = 0`
needs; `Set.ncard` of a neighbour set on a finite type is its cardinality. -/
noncomputable def maxDeg {V : Type*} [Fintype V] (H : SimpleGraph V) : ℕ :=
  Finset.univ.sup fun v => (H.neighborSet v).ncard

end MCPoise


