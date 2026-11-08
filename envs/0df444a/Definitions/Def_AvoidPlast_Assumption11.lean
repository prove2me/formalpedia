-- Prove2me | Definitions.Def_AvoidPlast_Assumption11
-- name    : AvoidPlast_Assumption11
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:49:20.012469+00:00
-- url     : https://prove2.me/theorems/39b17034-7532-480e-86fc-6e667aa37d19
-- title:
--   Assumption 1.1 with $p(n)=n^{-\omega(1)}$
-- statement:
--   Assumption 1.1 of the paper with $p(n)=n^{-\omega(1)}$: for every sufficiently small constant $\varepsilon>0$ there are a family $C=\{C_x\}$ stretching $\lceil|x|^{\varepsilon^2}\rceil$ bits to $\lceil|x|^{\varepsilon}\rceil$ bits, evaluable in space $O(|x|^{\varepsilon^2})$, and a negligible $p:\mathbb N\to(0,1)$ such that for every polynomial-time algorithm $A$ and every large enough $n$,
--
--   $$\Pr_{x\in\{0,1\}^n}[A(x)\text{ solves Avoid}(C_x)]\le p(n).$$
--
--   This is low-space range avoidance being hard on average for polynomial time.
--
--   **Formalization Note** The printed order is kept: $p$ is chosen before $A$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Assumption 1.1, p.3; Theorem 5.14, item 2, p.29

import Mathlib
import Definitions.Def_QuantumPRC_Negligible
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_prob
import Definitions.Def_AvoidPlast_PolyTime
import Definitions.Def_AvoidPlast_EvaluableInSpace
import Definitions.Def_AvoidPlast_SolvesAvoid
import Definitions.Def_AvoidPlast_ceilPow

namespace AvoidPlast

/-- Assumption 1.1 with `p(n) = n^{-ω(1)}` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Assumption 1.1, p.3; Theorem 5.14, item 2, p.29):
for every sufficiently small `ε > 0` there is a family `C = {C_x}` stretching `⌈|x|^{ε²}⌉` bits to
`⌈|x|^ε⌉` bits and evaluable in space `O(|x|^{ε²})`, and a negligible `p : ℕ → (0,1)`, such that for
every polynomial-time `A` and every large enough `n`, `Pr_x[A(x) solves Avoid(C_x)] ≤ p(n)`.

**Formalization Note** The printed order is kept: `p` comes before `A`. Readings R1, R2, R3. -/
def Assumption11 : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∃ C : List Bool → List Bool → List Bool,
      EvaluableInSpace C (ceilPow (ε ^ 2)) (ceilPow ε) (fun n => (n : ℝ) ^ (ε ^ 2)) ∧
      ∃ p : ℕ → ℝ, (∀ n, 0 < p n ∧ p n < 1) ∧ QuantumPRC.Negligible p ∧
        ∀ A : Machine 1, PolyTime A → ∀ᶠ n : ℕ in Filter.atTop,
          prob n (fun x => SolvesAvoid C (ceilPow (ε ^ 2)) (ceilPow ε) x (output A ![x])) ≤ p n

end AvoidPlast


