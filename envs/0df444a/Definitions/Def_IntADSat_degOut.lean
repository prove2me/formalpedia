-- Prove2me | Definitions.Def_IntADSat_degOut
-- name    : IntADSat_degOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:46.639474+00:00
-- url     : https://prove2.me/theorems/1f986140-034c-4d9c-9571-c51809752311
-- title:
--   Degree in $G[[n]\setminus C]$
-- statement:
--   For a simple graph $G$ on $[n]$, a set $C\subseteq[n]$ and a vertex $v$, $\deg_{G[[n]\setminus C]}(v)$ is the number of neighbours of $v$ outside $C$ (for $v\notin C$ this is the degree of $v$ in the induced subgraph on $[n]\setminus C$).
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemmas B.8 and B.9, p.18 (PDF 19)

import Mathlib

set_option autoImplicit false

namespace IntADSat

/-- The degree `deg_{G[[n] ∖ C]}(v)` of a vertex in the induced subgraph on the complement of a
row set `C` (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemmas B.8 and B.9, p.18 (PDF 19)): the number of neighbours of `v` outside `C`. -/
noncomputable def degOut {n : ℕ} (G : SimpleGraph (Fin n)) (C : Finset (Fin n)) (v : Fin n) : ℕ :=
  Set.ncard {u | u ∉ C ∧ G.Adj u v}

end IntADSat


