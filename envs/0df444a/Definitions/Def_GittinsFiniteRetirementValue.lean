-- Prove2me | Definitions.Def_GittinsFiniteRetirementValue
-- name    : GittinsFiniteRetirementValue
-- status  : Definition
-- author  : @Harry_Xu
-- created : 2026-07-31T04:11:59.647154+00:00
-- url     : https://prove2.me/theorems/dbdea5d8-d4ba-411f-8e82-d6ace7157df0
-- title:
--   Finite-horizon Gittins retirement values
-- statement:
--   The finite-horizon Bellman approximants for the discounted retirement game: horizon zero has value zero, while horizon $n+1$ takes the maximum of immediate retirement and one charged reward plus the discounted expected horizon-$n$ continuation value.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Theorem 35.3 on printed pp.442--443 and Lemma 35.7(a) on printed p.449.

import Mathlib.Probability.Kernel.MeasurableIntegral
import Definitions.Def_GittinsRetirementValue

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-- Finite-horizon Bellman approximants for the discounted retirement game.
At horizon zero the value is zero; at horizon `n+1`, the player either retires
for zero or plays once and receives the continuation value at horizon `n`. -/
noncomputable def gittinsFiniteRetirementValue
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) (r : S → ℝ) (α γ : ℝ) : ℕ → S → ℝ
  | 0, _ => 0
  | n + 1, x =>
      max 0 (r x - γ +
        α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P x)

end BanditAlgorithm


