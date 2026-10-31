-- Prove2me | Definitions.Def_KallMayerSLP_Bonferroni_lowerEvent
-- name    : KallMayerSLP_Bonferroni_lowerEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:07.087678+00:00
-- url     : https://prove2.me/theorems/2be30710-4c31-499e-bf2f-41caf9404ad4
-- title:
--   The event $A_i(x)=\{\xi_i\le x_i\}$
-- statement:
--   For a random vector $\xi:\Omega\to\mathbb R^r$ and $x\in\mathbb R^r$,
--   $$
--   A_i(x)=\{\omega : \xi_i(\omega)\le x_i\},\qquad i=1,\dots,r.
--   $$
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 4, §3.4, eq. (3.7), p.285 (PDF 294)

import Mathlib

namespace KallMayerSLP.Bonferroni

/-- The event `A_i(x) := {ω | ξ_i(ω) ≤ x_i}`, for a random vector `ξ : Ω → ℝ^r`.

Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 4, eq. (3.7), p.285 (PDF 294). -/
def lowerEvent {Ω : Type*} {r : ℕ} (ξ : Ω → Fin r → ℝ) (x : Fin r → ℝ) (i : Fin r) : Set Ω :=
  {ω | ξ ω i ≤ x i}

end KallMayerSLP.Bonferroni


