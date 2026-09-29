-- Prove2me | Definitions.Def_EthierKurtz_IsOutwardUnitNormal
-- name    : EthierKurtz_IsOutwardUnitNormal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:13:21.503985+00:00
-- url     : https://prove2.me/theorems/bdb08770-6a55-40ad-ac97-e3c2052dd279
-- title:
--   Outward unit normal
-- statement:
--   A unit vector at a boundary point oriented outward by a local C¹ defining function that is negative exactly inside the region.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 8, Section 1, equation (1.19), printed p. 369 (PDF p. 378).

import Mathlib

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- Outward unit normal, expressed by a local C¹ defining function with
negative values precisely on Ω. The positive multiple fixes orientation. -/
def IsOutwardUnitNormal {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (x v : EuclideanSpace ℝ (Fin d)) : Prop :=
  x ∈ frontier Ω ∧ ‖v‖ = 1 ∧
    ∃ V : Set (EuclideanSpace ℝ (Fin d)), IsOpen V ∧ x ∈ V ∧
    ∃ r : EuclideanSpace ℝ (Fin d) → ℝ,
    ∃ scale : ℝ, 0 < scale ∧ ContDiffOn ℝ 1 r V ∧ r x = 0 ∧
      (∀ y ∈ V, y ∈ Ω ↔ r y < 0) ∧
      ∀ h, fderiv ℝ r x h = scale * (∑ i, v i * h i)

end EthierKurtz


