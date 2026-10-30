-- Prove2me | Definitions.Def_RoslingAssembly_Feasible
-- name    : RoslingAssembly_Feasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:37:29.88555+00:00
-- url     : https://prove2.me/theorems/03c2def1-bde3-4238-9afd-43d20ccf7701
-- title:
--   Feasibility for problem P, constraint (3)
-- statement:
--   A policy is **feasible** for problem P if in every period $t\ge1$, for every item $i$,
--   $$X_{it}\le Y_{it}\le X^l_{kt}\qquad\text{for all }k\in P(i). \tag{3}$$
--   The left inequality says that orders are nonnegative; the right one, that an item can only be assembled from components on hand.
--
--   **Formalization Note** Constraint (3) is required along every demand path, not only almost surely. Quantities of periods $\le 0$ come from the pre-horizon history.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, §1, p. 567, Problem P, (3)

import Mathlib
import Definitions.Def_RoslingAssembly_Network_P
import Definitions.Def_RoslingAssembly_Xpath
import Definitions.Def_RoslingAssembly_XlPath

namespace RoslingAssembly

/-- **Feasibility for problem P**, constraint (3) (p. 567). Rosling, *Optimal Inventory Policies
for Assembly Systems under Random Demands*, Operations Research 37(4), 1989, p. 567, Problem P:
"such that X_it ≤ Y_it ≤ X^l_kt for all k ∈ P(i) and all i, t (3)".

`Feasible net ℓ Yh ξh pol` says that, along every demand path `ω` and in every period `t ≥ 1`,
for every item `i`: `X_it ≤ Y_it` (orders are nonnegative) and `Y_it ≤ X^l_kt` for every
immediate predecessor `k ∈ P(i)` (an item can only be assembled from components on hand).

**Formalization Note.** Constraint (3) is required on every demand path, not only almost surely
(the stronger requirement on the policies that witness Theorem 4(i)). Periods are integers with
the paper's numbering; `X`, `Y`, `X^l` in periods `≤ 0` come from the pre-horizon history
`Yh`, `ξh`. Items are `Fin N`, 0-based. -/
def Feasible {N : ℕ} (net : Network N) (ℓ : Fin N → ℕ) (Yh : ℤ → Fin N → ℝ) (ξh : ℤ → ℝ)
    (pol : ℕ → (ℕ → ℝ) → Fin N → ℝ) : Prop :=
  ∀ (ω : ℕ → ℝ) (t : ℤ), 1 ≤ t → ∀ i : Fin N,
    Xpath Yh ξh pol ω t i ≤ Ypath Yh pol ω t i ∧
      ∀ k ∈ net.P i, Ypath Yh pol ω t i ≤ XlPath ℓ Yh ξh pol ω t k

end RoslingAssembly


