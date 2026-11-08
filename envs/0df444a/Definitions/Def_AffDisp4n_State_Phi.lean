-- Prove2me | Definitions.Def_AffDisp4n_State_Phi
-- name    : AffDisp4n_State_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:58:46.216138+00:00
-- url     : https://prove2.me/theorems/81931f11-91ae-442e-ab3a-1d7a05d131f8
-- title:
--   The map $\Phi(u) = b + Lu$
-- statement:
--   The map of a state from parameter assignments to inputs of the original circuit:
--   $$
--   \Phi(u) = b + L u, \qquad u \in \mathbb F_2^m .
--   $$
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.2, p.13, display (1)

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_State

namespace AffDisp4n

/-- The map **`Φ(u) = b + L u`** of a state (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), display (1), p.13), from parameter assignments
`u ∈ 𝔽₂ᵐ` to inputs of the original circuit. -/
def State.Phi {n : ℕ} (σ : State n) (u : Fin σ.m → ZMod 2) : Fin n → ZMod 2 :=
  σ.b + σ.L.mulVec u

end AffDisp4n


