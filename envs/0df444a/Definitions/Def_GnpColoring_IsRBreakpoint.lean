-- Prove2me | Definitions.Def_GnpColoring_IsRBreakpoint
-- name    : GnpColoring_IsRBreakpoint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:36.317481+00:00
-- url     : https://prove2.me/theorems/72760b4d-e966-4801-becf-9e4068ad040b
-- title:
--   $r$-breakpoint (Definition 3.1)
-- statement:
--   Let $r\ge0$ be an integer. A vertex $v$ is an **$r$-breakpoint** if every self-avoiding path $P=(v_0,\dots,v_\ell)$ in $G$ with $v_0=v$ and $0\le\ell\le r$ has weight
--
--   $$W(P)=\prod_{i=0}^{\ell}W(v_i)\le1.$$
--
--   The single-vertex path $(v)$ is included, so an $r$-breakpoint has $W(v)\le1$.
--
--   **Formalization Note** Paths are walks with no repeated vertex; length is the number of edges.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Definition 3.1, p.15

import Mathlib
import Definitions.Def_GnpColoring_vertexWeight

open scoped Classical
open Finset

namespace GnpColoring

/-- **r-breakpoint** (Definition 3.1): `v` is an `r`-breakpoint if every self-avoiding path
`P = (v₀, …, v_ℓ)` in `G` with `v₀ = v` and `0 ≤ ℓ ≤ r` has weight `W(P) = ∏_{i=0}^ℓ W(vᵢ) ≤ 1`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Definition 3.1, p.15: "The single-vertex path P = (v) is explicitly included."

**Formalization Note** A self-avoiding path is a `G.Walk v u` with `IsPath`; its length is the
number of edges and its vertices are `support` (the single-vertex path is `Walk.nil`). -/
def IsRBreakpoint {n : ℕ} (G : SimpleGraph (Fin n)) (d η A C : ℝ) (r : ℕ) (v : Fin n) : Prop :=
  ∀ (u : Fin n) (P : G.Walk v u), P.IsPath → P.length ≤ r →
    (P.support.map (vertexWeight G d η A C)).prod ≤ 1

end GnpColoring


