-- Prove2me | Definitions.Def_QueryDepthMIS_Perm
-- name    : QueryDepthMIS_Perm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:25:17.891171+00:00
-- url     : https://prove2.me/theorems/aaf10803-22f6-4cb5-b4d0-07de0f14ac59
-- title:
--   Sample space of a uniformly random permutation: orderings $V \simeq \{0,\dots,n-1\}$
-- statement:
--   Let $V$ be a finite vertex set with $n = |V|$. The paper draws a permutation $\pi$ of $V$ uniformly at random, $\pi(i)$ being the $i$-th vertex. Here one outcome is an ordering
--   $$
--   \omega : V \xrightarrow{\ \sim\ } \{0, 1, \dots, n-1\},
--   $$
--   a bijection assigning to each vertex its (0-based) position; the paper's $\pi$ is $\omega^{-1}$. A uniformly random permutation is a uniformly random element of this finite set of $n!$ orderings.
--
--   This type is the sample space of every probability in the mission.
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), §2.1, p.7

import Mathlib

set_option autoImplicit false

namespace QueryDepthMIS

/-- The sample space of the uniformly random permutation `π` of `V` (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), §2.1, p.7: "Let π
be a permutation of V chosen uniformly at random"): one point `ω : V ≃ Fin n` (with
`n = |V|`) is one ordering of the vertices, `ω v` being the 0-based position of `v`; the paper's
`π` is `ω⁻¹` (`π(i)` is the vertex at position `i`).

**Formalization Note** "Uniformly at random" is the uniform (counting) law on this finite type,
see the published `PunctSketch.coinProb`; `Fintype (V ≃ Fin n)` is Mathlib's instance. -/
abbrev Perm (V : Type*) [Fintype V] : Type _ := V ≃ Fin (Fintype.card V)

end QueryDepthMIS


