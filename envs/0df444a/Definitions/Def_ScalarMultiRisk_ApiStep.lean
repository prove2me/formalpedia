-- Prove2me | Definitions.Def_ScalarMultiRisk_ApiStep
-- name    : ScalarMultiRisk_ApiStep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:25:18.094985+00:00
-- url     : https://prove2.me/theorems/61d7a82d-d414-4588-a5ea-3590af9a3fb3
-- title:
--   The stepped acceptance set $A^\pi_{t,s}$
-- statement:
--   $A^\pi_{t,s}=A^\pi_t\cap L^\infty_s(\mathbb R^d)$: the portfolios known at time $s$ that are acceptable at time $t$.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Corollary 4.11(1), p.23

import Mathlib
import Definitions.Def_ScalarMultiRisk_Api
import Definitions.Def_ScalarMultiRisk_LinftyFull

open MeasureTheory

namespace ScalarMultiRisk

/-- **The stepped acceptance set `A^π_{t,s}`.** arXiv:1807.10694v5, Corollary 4.11(1), p.23:
`A^π_{t,s} := A^π_t ∩ L∞_s(ℝ^d)`. -/
def ApiStep {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} (A : Market Ω T d)
    (ρ : Fin (T + 1) → (Ω → Fin d → ℝ) → Ω → ℝ) (S : Fin (T + 1) → Ω → Fin d → ℝ)
    (t s : Fin (T + 1)) : Set (Ω → Fin d → ℝ) :=
  Api A ρ S t ∩ LinftyFull A.toFilteredSpace s

end ScalarMultiRisk


