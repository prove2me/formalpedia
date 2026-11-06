-- Prove2me | Definitions.Def_GnpColoring_hubs
-- name    : GnpColoring_hubs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:18.038575+00:00
-- url     : https://prove2.me/theorems/ecc013c2-79f4-4034-8579-956e7b71c9b5
-- title:
--   The hubs $H=\{v:\deg_G(v)>\bar\Delta\}$
-- statement:
--   Let $G$ be a graph on the vertex set $V=\{0,\dots,n-1\}$. The set of **hubs** is
--
--   $$H=\{v\in V:\ \deg_G(v)>\bar\Delta\},\qquad \bar\Delta=d+d^{1/2+\eta}.$$
--
--   Degrees are always taken in $G$, also after conditioning or passing to a subgraph.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Section 5.1, pp.43 and 45

import Mathlib
import Definitions.Def_GnpColoring_deltaBar

open scoped Classical
open Finset

namespace GnpColoring

/-- **The hubs** `H = {v ∈ V : deg_G(v) > Δ̄}`, `Δ̄ = d + d^(1/2+η)`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Section 5.1, pp.43 and 45: "Call a vertex a hub if its degree in the original graph G
exceeds Δ̄, and write H for the set of hubs."

**Formalization Note** Vertices are `Fin n` (the paper's `[n]`, 0-based); degrees are in `G`. -/
noncomputable def hubs {n : ℕ} (G : SimpleGraph (Fin n)) (d η : ℝ) : Finset (Fin n) :=
  univ.filter fun v => deltaBar d η < (G.degree v : ℝ)

end GnpColoring


