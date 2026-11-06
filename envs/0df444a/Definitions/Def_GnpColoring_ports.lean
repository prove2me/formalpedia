-- Prove2me | Definitions.Def_GnpColoring_ports
-- name    : GnpColoring_ports
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:58.606368+00:00
-- url     : https://prove2.me/theorems/ee594609-91b8-4949-aa12-55ba1c697257
-- title:
--   The ports $P_B$ of a block
-- statement:
--   The **ports** of a block $B$ are the vertices of $B$ adjacent to at least one vertex of $\partial B$. All interaction between a block and the singletons passes through its ports.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Definition 3.2 (2), p.15

import Mathlib
import Definitions.Def_GnpColoring_extBoundary

open scoped Classical
open Finset

namespace GnpColoring

/-- **The ports** `P_B` of a block: the vertices of `B` adjacent to some vertex of `∂B`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Definition 3.2 (2), p.15: "We call vertices in B that are adjacent to (one or multiple)
vertices in ∂B ports." -/
noncomputable def ports {n : ℕ} (G : SimpleGraph (Fin n)) (B : Finset (Fin n)) : Finset (Fin n) :=
  B.filter fun u => ∃ v ∈ extBoundary G B, G.Adj u v

end GnpColoring


