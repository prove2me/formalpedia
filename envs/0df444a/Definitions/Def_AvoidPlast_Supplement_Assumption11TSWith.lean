-- Prove2me | Definitions.Def_AvoidPlast_Supplement_Assumption11TSWith
-- name    : AvoidPlast_Supplement_Assumption11TSWith
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:03:11.329197+00:00
-- url     : https://prove2.me/theorems/a2d7c1c0-e896-4d0b-97f6-8f481b805cd5
-- title:
--   Assumption 1.1 with $p$, for time-and-space evaluable families
-- statement:
--   As Assumption 1.1 with $p$, with the family evaluable in simultaneous time $\mathrm{poly}(n)$ and space $O(n^{\varepsilon^2})$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorems 5.6, 5.9, pp.24–25

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_PolyTime
import Definitions.Def_AvoidPlast_SolvesAvoid
import Definitions.Def_AvoidPlast_ceilPow
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_prob
import Definitions.Def_AvoidPlast_Supplement_EvaluableInTimeSpace

namespace AvoidPlast.Supplement

open AvoidPlast

/-- Assumption 1.1 with a given `p`, for families evaluable in simultaneous time `poly(n)` and
space `O(n^{ε²})` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorems 5.6 and 5.9, pp.24–25). -/
def Assumption11TSWith (p : ℕ → ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∃ C : List Bool → List Bool → List Bool,
      EvaluableInTimeSpace C (ceilPow (ε ^ 2)) (ceilPow ε) (fun n => (n : ℝ) ^ (ε ^ 2)) ∧
        ∀ A : Machine 1, PolyTime A → ∀ᶠ n : ℕ in Filter.atTop,
          prob n (fun x => SolvesAvoid C (ceilPow (ε ^ 2)) (ceilPow ε) x (output A ![x])) ≤ p n

end AvoidPlast.Supplement


