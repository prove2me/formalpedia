-- Prove2me | Definitions.Def_ScalarMultiRisk_priceSetAt
-- name    : ScalarMultiRisk_priceSetAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:23:36.769981+00:00
-- url     : https://prove2.me/theorems/4b4964c0-d04b-432c-88a8-21282106aa20
-- title:
--   The set $\mathcal S_t$
-- statement:
--   $\mathcal S_t=\{S\in\mathcal S\mid\pi^S_t(0)\in L^\infty_t(\mathbb R)\}$.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, p.20

import Mathlib
import Definitions.Def_ScalarMultiRisk_priceSet
import Definitions.Def_ScalarMultiRisk_piS
import Definitions.Def_ScalarMultiRisk_InLinftyE

open MeasureTheory

namespace ScalarMultiRisk

/-- **The set `𝒮_t`.** arXiv:1807.10694v5, p.20: `𝒮_t := {S ∈ 𝒮 | π^S_t(0) ∈ L∞_t(ℝ)}`. -/
def priceSetAt {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} [NeZero d] (A : Market Ω T d)
    (ρ : Fin (T + 1) → (Ω → Fin d → ℝ) → Ω → ℝ) (t : Fin (T + 1)) :
    Set (Fin (T + 1) → Ω → Fin d → ℝ) :=
  {S ∈ priceSet A | InLinftyE A.toFilteredSpace t (piS A ρ S t 0)}

end ScalarMultiRisk


