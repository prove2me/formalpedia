-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_ex31Data
-- name    : KallMayerSLP_Multistage_ex31Data
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:15:05.014362+00:00
-- url     : https://prove2.me/theorems/1ce3df72-cd36-4326-86c5-843896b6f856
-- title:
--   Example 3.1: the problem data
-- statement:
--   The three-stage problem of Example 3.1:
--   $$
--   \min\{2x+\mathbb E[y_1(\xi_2)+2y_2(\xi_2)]+\mathbb E[z_1(\xi_2,\xi_3)+z_2(\xi_2,\xi_3)]\}
--   $$
--   subject to $x+y_1(\xi_2)-y_2(\xi_2)=\xi_2$, $x+y_1(\xi_2)-y_2(\xi_2)+z_1(\xi_2,\xi_3)-z_2(\xi_2,\xi_3)=\xi_3$, and $x,y_1,y_2,z_1,z_2\ge0$.
--
--   **Formalization Note** $n=(1,2,2)$ and $m=(0,1,1)$, since the first stage has no equality constraint. Each $\xi_t$ is a vector of $\mathbb R^1$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, Example 3.1, p.257 (PDF 266)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_MSLP

namespace KallMayerSLP.Multistage

/-- The data of Example 3.1 (Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3,
Example 3.1, p.257, PDF 266), the three-stage problem
`min {2x + 𝔼[y_1(ξ_2) + 2 y_2(ξ_2)] + 𝔼[z_1(ξ_2, ξ_3) + z_2(ξ_2, ξ_3)]}` s.t.
`x + y_1 − y_2 = ξ_2`, `x + y_1 − y_2 + z_1 − z_2 = ξ_3`, `x, y_1, y_2, z_1, z_2 ≥ 0`.

**Formalization Note.** `n = (1, 2, 2)`, and `m = (0, 1, 1)`, since the first stage has no equality
constraint. Each `ξ_t` is a vector of `ℝ^1`. Every matrix `A_{tτ}`, `τ ≤ t`, has the row `(1)` or
`(1, -1)`, written as "`1` in column `0`, `-1` in column `1`". -/
def ex31Data : MSLP where
  T := 3
  one_le_T := by norm_num
  n := fun t => if t = 1 then 1 else 2
  m := fun t => if t = 1 then 0 else 1
  r := fun _ => 1
  c := fun t j => if t = 1 then 2 else if t = 2 then (j.val : ℝ) + 1 else 1
  A := fun _ _ _ j => if j.val = 0 then 1 else -1
  b := fun t =>
    { toFun := fun ζ _ => if h : 2 ≤ t then ζ ⟨t, h, le_rfl⟩ 0 else 0
      linear := { toFun := fun ζ _ => if h : 2 ≤ t then ζ ⟨t, h, le_rfl⟩ 0 else 0
                  map_add' := fun ζ ζ' => by
                    funext i; by_cases h : 2 ≤ t <;> simp [h]
                  map_smul' := fun a ζ => by
                    funext i; by_cases h : 2 ≤ t <;> simp [h] }
      map_vadd' := fun ζ v => by
        funext i; by_cases h : 2 ≤ t <;> simp [h] }

end KallMayerSLP.Multistage


