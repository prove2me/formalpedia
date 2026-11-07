-- Prove2me | Definitions.Def_GeoSemialgCSP_MULC_satFrac
-- name    : GeoSemialgCSP_MULC_satFrac
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:49:53.949195+00:00
-- url     : https://prove2.me/theorems/41f47824-1bdf-4e2f-a6c1-c9f8c77e10fb
-- title:
--   Fraction of satisfied Unique Games edges
-- statement:
--   A labelling $\ell$ of the vertices satisfies an edge occurrence $(u,v,\pi_{uv})$ when $\ell(u)=\pi_{uv}(\ell(v))$. The **value** of $\ell$ is the fraction of edge occurrences it satisfies (uniform edge weights).
--
--   **Formalization Note** It is $0$ for an instance without edges.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §6, p.17 (PDF p.18)

import Mathlib
import Definitions.Def_GeoSemialgCSP_MULC

namespace GeoSemialgCSP

/-- **Fraction of satisfied edges.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §6, printed p.17 (PDF p.18): an edge is
satisfied by a labelling `ℓ` when `ℓ(u) = π_{uv}(ℓ(v))`; edges have uniform weight.

**Formalization Note.** `lab.1` labels the left side, `lab.2` the right side. The fraction is `0`
for an empty edge list. -/
noncomputable def MULC.satFrac (L : MULC) (lab : (Fin L.nV → Fin L.M) × (Fin L.nW → Fin L.M)) : ℝ :=
  ((L.edges.countP (fun e => decide (e.2.2 (lab.2 e.2.1) = lab.1 e.1)) : ℕ) : ℝ) /
    (L.edges.length : ℝ)

end GeoSemialgCSP


