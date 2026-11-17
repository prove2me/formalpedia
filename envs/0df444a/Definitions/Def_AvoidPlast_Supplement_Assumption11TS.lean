-- Prove2me | Definitions.Def_AvoidPlast_Supplement_Assumption11TS
-- name    : AvoidPlast_Supplement_Assumption11TS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:03:42.359304+00:00
-- url     : https://prove2.me/theorems/3357f43e-a949-455c-bcd9-53ccf9dfbd89
-- title:
--   Assumption 1.1 with $p(n)=n^{-\omega(1)}$, for time-and-space evaluable families
-- statement:
--   For every sufficiently small $\varepsilon>0$ there are a family stretching $\lceil|x|^{\varepsilon^2}\rceil$ bits to $\lceil|x|^\varepsilon\rceil$ bits, evaluable in simultaneous time $\mathrm{poly}(n)$ and space $O(|x|^{\varepsilon^2})$, and a negligible $p:\mathbb N\to(0,1)$ such that every polynomial-time $A$ solves $\mathrm{Avoid}(C_x)$ on at most a $p(n)$ fraction of the $n$-bit inputs, for every large $n$. This is the base mission's Assumption 1.1 with the stronger evaluability.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 1.3, p.4

import Mathlib
import Definitions.Def_QuantumPRC_Negligible
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_PolyTime
import Definitions.Def_AvoidPlast_SolvesAvoid
import Definitions.Def_AvoidPlast_ceilPow
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_prob
import Definitions.Def_AvoidPlast_Supplement_EvaluableInTimeSpace

namespace AvoidPlast.Supplement

open AvoidPlast

/-- The hypothesis of Theorem 1.3 on Avoid (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), p.4): Assumption 1.1 with `p(n) = n^{-ω(1)}`
for families evaluable in simultaneous time `poly(n)` and space `O(n^{ε²})`. Same shape as the
base `Assumption11`: the negligible `p : ℕ → (0,1)` is chosen with the family. -/
def Assumption11TS : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∃ C : List Bool → List Bool → List Bool,
      EvaluableInTimeSpace C (ceilPow (ε ^ 2)) (ceilPow ε) (fun n => (n : ℝ) ^ (ε ^ 2)) ∧
      ∃ p : ℕ → ℝ, (∀ n, 0 < p n ∧ p n < 1) ∧ QuantumPRC.Negligible p ∧
        ∀ A : Machine 1, PolyTime A → ∀ᶠ n : ℕ in Filter.atTop,
          prob n (fun x => SolvesAvoid C (ceilPow (ε ^ 2)) (ceilPow ε) x (output A ![x])) ≤ p n

end AvoidPlast.Supplement


