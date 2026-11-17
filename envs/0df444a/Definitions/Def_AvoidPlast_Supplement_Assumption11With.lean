-- Prove2me | Definitions.Def_AvoidPlast_Supplement_Assumption11With
-- name    : AvoidPlast_Supplement_Assumption11With
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:02:33.293208+00:00
-- url     : https://prove2.me/theorems/8809253b-4a31-4806-b04e-83c88af33851
-- title:
--   Assumption 1.1 with a given $p$
-- statement:
--   Assumption 1.1 holds with $p$ if for every sufficiently small $\varepsilon>0$ there is a family $C=\{C_x\}$ stretching $\lceil|x|^{\varepsilon^2}\rceil$ bits to $\lceil|x|^{\varepsilon}\rceil$ bits and evaluable in space $O(|x|^{\varepsilon^2})$ such that for every polynomial-time $A$ and every large enough $n$,
--   $$\Pr_{x\in\{0,1\}^n}[A(x)\text{ solves }\mathrm{Avoid}(C_x)]\le p(n).$$
--
--   **Formalization Note** One $p$ serves every $\varepsilon$, since the conclusions of Theorems 5.6, 5.8, 5.9 are stated in terms of $p$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Assumption 1.1, p.3; Theorem 5.8, p.25

import Mathlib
import Definitions.Def_AvoidPlast_EvaluableInSpace
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_PolyTime
import Definitions.Def_AvoidPlast_SolvesAvoid
import Definitions.Def_AvoidPlast_ceilPow
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_prob

namespace AvoidPlast.Supplement

open AvoidPlast

/-- Assumption 1.1 with a given bound `p` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Assumption 1.1, p.3; Theorem 5.8, p.25): for
every sufficiently small `ε > 0` there is a family stretching `⌈|x|^{ε²}⌉` bits to `⌈|x|^ε⌉`
bits, evaluable in space `O(|x|^{ε²})`, such that every polynomial-time `A` has, for every large
`n`, `Pr_x[A(x) solves Avoid(C_x)] ≤ p(n)`.

**Formalization Note** One `p` serves every `ε`, since the conclusions of Theorems 5.6, 5.8, 5.9
are stated in terms of `p`. -/
def Assumption11With (p : ℕ → ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∃ C : List Bool → List Bool → List Bool,
      EvaluableInSpace C (ceilPow (ε ^ 2)) (ceilPow ε) (fun n => (n : ℝ) ^ (ε ^ 2)) ∧
        ∀ A : Machine 1, PolyTime A → ∀ᶠ n : ℕ in Filter.atTop,
          prob n (fun x => SolvesAvoid C (ceilPow (ε ^ 2)) (ceilPow ε) x (output A ![x])) ≤ p n

end AvoidPlast.Supplement


