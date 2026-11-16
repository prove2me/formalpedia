-- Prove2me | Definitions.Def_RegevJointHybrid
-- name    : RegevJointHybrid
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T09:09:26.247794+00:00
-- url     : https://prove2.me/theorems/11e01e41-4513-4b73-98ee-87e2af5dc94b
-- title:
--   Isometric evolution and joint Born-event mass
-- statement:
--   For a finite-dimensional complex state space, these definitions specify sequential isometric evolution and the Born mass of an arbitrary event on the complete measurement register. They provide the interface for analyzing correlated quantum output events.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, https://cims.nyu.edu/~regev/papers/qcrypto.pdf, Lemmas 3.3 and 3.14, pp. 19 and 26 (PDF pages 19 and 26). This generic finite-dimensional ideal-prefix hybrid estimate is an explicit formalization aid, not a verbatim result or a construction of the algorithms in the source.

import Mathlib
set_option autoImplicit false
namespace RegevJointHybrid
noncomputable section

/-- Sequential isometries acting on a full retained state space. -/
def evolve {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (step : ℕ → E →ₗᵢ[ℂ] E) : ℕ → E → E
  | 0, state => state
  | count+1, state => step count (evolve step count state)

/-- Born mass of an arbitrary classical event on all measured registers. -/
def bornEvent {α : Type*} [Fintype α] (event : α → Prop)
    (state : EuclideanSpace ℂ α) : ℝ :=
  open Classical in ∑ value,if event value then ‖state value‖^2 else 0

end
end RegevJointHybrid


