-- Prove2me | Definitions.Def_FixpReciprocal_circuitMap
-- name    : FixpReciprocal_circuitMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:49:41.35234+00:00
-- url     : https://prove2.me/theorems/abd2d3e4-d0ed-4624-820d-e1b93576e4f8
-- title:
--   The map $F_{\mathcal C}$ on the cube
-- statement:
--   For a generalized circuit $\mathcal C$ with gates $g_i=(f_i,j_{i,1},\dots,j_{i,k_i})$, the map $F_{\mathcal C}$ is given coordinatewise by
--   $$\bigl(F_{\mathcal C}(x)\bigr)_i=f_i(x_{j_{i,1}},\dots,x_{j_{i,k_i}}).$$
--   The file also defines the unit cube $[0,1]^N$. Solutions of $\mathcal C$ are exactly the fixed points of $F_{\mathcal C}$ in the cube.
-- source:
--   Shimizu, FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions (STOC 2027 submission, sha256 ffcad4a7…), proof of Theorem 4.2, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_FixpReciprocal_RGate

namespace FixpReciprocal

/-- The unit cube `[0, 1]^N`. -/
def cube (N : ℕ) : Set (Fin N → ℝ) := {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

/-- **The map `F_C`:** `(F_C(x))_i = f_i(x_{j_{i,1}}, …, x_{j_{i,k_i}})`.

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), proof of Theorem 4.2, p.12. -/
noncomputable def circuitMap (τ : ℚ) (C : List RGate) (x : Fin C.length → ℝ) : Fin C.length → ℝ :=
  fun i => (C.get i).eval τ (lookup x)

end FixpReciprocal


