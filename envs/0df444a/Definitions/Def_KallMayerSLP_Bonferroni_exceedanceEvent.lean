-- Prove2me | Definitions.Def_KallMayerSLP_Bonferroni_exceedanceEvent
-- name    : KallMayerSLP_Bonferroni_exceedanceEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:04.640993+00:00
-- url     : https://prove2.me/theorems/4a918422-816b-4031-a056-f9e4710f8c44
-- title:
--   The event $B_i(x)=\{\xi_i> x_i\}$
-- statement:
--   For a random vector $\xi:\Omega\to\mathbb R^r$ and $x\in\mathbb R^r$,
--   $$
--   B_i(x)=A_i^c(x)=\{\omega : \xi_i(\omega)> x_i\},\qquad i=1,\dots,r.
--   $$
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 4, §3.4, eq. (3.7), p.285 (PDF 294)

import Mathlib

namespace KallMayerSLP.Bonferroni

/-- The event `B_i(x) := A_i^c(x) = {ω | ξ_i(ω) > x_i}`, for a random vector `ξ : Ω → ℝ^r`.

Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 4, eq. (3.7), p.285 (PDF 294). -/
def exceedanceEvent {Ω : Type*} {r : ℕ} (ξ : Ω → Fin r → ℝ) (x : Fin r → ℝ) (i : Fin r) :
    Set Ω :=
  {ω | x i < ξ ω i}

end KallMayerSLP.Bonferroni


