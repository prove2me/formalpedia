-- Prove2me | Definitions.Def_ScalarMultiRisk_Api
-- name    : ScalarMultiRisk_Api
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:23:42.588342+00:00
-- url     : https://prove2.me/theorems/ecadfe50-cc5b-4ded-abac-8b16641ec277
-- title:
--   The acceptance set $A^\pi_t$
-- statement:
--   $A^\pi_t=\{X\in L^\infty(\mathbb R^d)\mid\pi^S_t(X)\le0\}$.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Proposition 4.5, p.19

import Mathlib
import Definitions.Def_ScalarMultiRisk_piS
import Definitions.Def_ScalarMultiRisk_acceptanceSet

open MeasureTheory

namespace ScalarMultiRisk

/-- **The acceptance set `A^π_t`.** arXiv:1807.10694v5, Proposition 4.5, p.19:
`A^π_t := {X ∈ L∞(ℝ^d) | π^S_t(X) ≤ 0}`. -/
def Api {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} (A : Market Ω T d)
    (ρ : Fin (T + 1) → (Ω → Fin d → ℝ) → Ω → ℝ) (S : Fin (T + 1) → Ω → Fin d → ℝ)
    (t : Fin (T + 1)) : Set (Ω → Fin d → ℝ) :=
  acceptanceSet A.toFilteredSpace (piS A ρ S t)

end ScalarMultiRisk


