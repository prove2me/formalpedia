-- Prove2me | Definitions.Def_LPCommunity_LPFail_XTilde
-- name    : LPCommunity_LPFail_XTilde
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T11:04:15.82351+00:00
-- url     : https://prove2.me/theorems/4d31ea64-d2f2-48bd-9e81-a4c36da179bd
-- title:
--   Proof of Theorem 5, p. 12 — the distance-based feasible point x̃ of (LP-P)
-- statement:
--   Let $G=(V,E)$ be a graph on $V=\{1,\dots,n\}$ with graph distance $\rho_G$, average distance $\rho_{\mathrm{avg}}(G)$ and constant $c(G)$ of display (17). The point $\tilde x\in\mathbb R^{\binom n2}$ of the proof of Theorem 5 is
--   $$\tilde x_{ij}=\frac{\rho_G(i,j)+c(G)}{2\rho_{\mathrm{avg}}(G)+2c(G)\,(1-\frac1n)},\qquad 1\le i<j\le n,$$
--   with $\tilde x_{ji}:=\tilde x_{ij}$.
--
--   It renormalizes the graph metric $\rho_G$, shifted by $c(G)$, so that the coordinates sum to $n^2/4$; it is the witness that (LP-P) does not recover the planted bisection.
--
--   **Formalization Note** $\tilde x$ is an array on $V\times V$, set to $0$ on the diagonal and symmetric, matching the encoding of feasibility in the Setting. The distance enters through its real value; for a connected graph this is the shortest-path length.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 12, §3.2, proof of Theorem 5 (definition of x̃)

import Mathlib
import Definitions.Def_LPCommunity_LPFail_Setting

open Finset
open scoped Classical ENNReal

namespace LPCommunity.LPFail

/-- The point `x̃` of the proof of Theorem 5 (p. 12):
`x̃_ij = (ρ_G(i, j) + c(G)) / (2ρ_avg(G) + 2c(G)(1 − 1/n))` for `i ≠ j`, symmetric, with zero
diagonal (the page indexes `x̃` by pairs `i < j` only). -/
noncomputable def xTilde {n : ℕ} (G : SimpleGraph (Fin n)) : Fin n → Fin n → ℝ :=
  fun i j => if i = j then 0 else
    (((rho G i j : ℕ∞) : ℝ≥0∞).toReal + cG G) /
      (2 * (rhoAvg G).toReal + 2 * cG G * (1 - 1 / (n : ℝ)))

end LPCommunity.LPFail


