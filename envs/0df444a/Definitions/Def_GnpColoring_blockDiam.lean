-- Prove2me | Definitions.Def_GnpColoring_blockDiam
-- name    : GnpColoring_blockDiam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:28.162193+00:00
-- url     : https://prove2.me/theorems/e1ff6b1e-0272-4722-80e5-6a54ffed24be
-- title:
--   The diameter $\operatorname{diam}(G[B])$ of a block
-- statement:
--   The diameter of the induced subgraph $G[B]$, with distances measured by paths inside $G[B]$ rather than in $G$.
--
--   **Formalization Note** The graph diameter of the induced subgraph; it is the finite diameter whenever $G[B]$ is connected, the only case used.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Section 2.1, p.13; Section 4, p.35

import Mathlib

open scoped Classical
open Finset

namespace GnpColoring

/-- **The diameter of a block measured inside it**, `diam(G[B])`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Section 2.1, p.13: "The diameter of a connected subgraph is measured using paths within
that subgraph"; Section 4, p.35: "Diameters of these components are measured inside the
components, rather than in the ambient graph."

**Formalization Note** `SimpleGraph.diam` of the induced graph `G[B]`; it is the finite diameter
whenever `G[B]` is connected, which is the only case the mission uses. -/
noncomputable def blockDiam {n : ℕ} (G : SimpleGraph (Fin n)) (B : Finset (Fin n)) : ℕ :=
  (G.induce (B : Set (Fin n))).diam

end GnpColoring


