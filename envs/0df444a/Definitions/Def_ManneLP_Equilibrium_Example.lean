-- Prove2me | Definitions.Def_ManneLP_Equilibrium_Example
-- name    : ManneLP_Equilibrium_Example
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:53:37.918869+00:00
-- url     : https://prove2.me/theorems/dabe39bb-ce0f-4169-9cb5-b168c7d6e56f
-- title:
--   §6 — the numerical example: T = 3, p = (2/3, 0, 1/3), C₁(i) = i, C₂(j) = 3j, C₃ = max[0, 6(n − i − j)], j ∈ {0, 1}; Table 2's solutions
-- statement:
--   This file defines the numerical example of Manne (1960), §6, as an instance of the general model.
--
--   1. $T=3$.
--   2. Demand law: $p_0=2/3$, $p_1=0$, $p_2=1/3$, and $p_n=0$ for $n\ge3$.
--   3. Costs: $C_1(i)=i$, $C_2(j)=3j$, $C_3(m)=\max[0,6m]$ for the shortage level $m=n-i-j$.
--   4. Production capacity is at most one unit per month, $j\in\{0,1\}$, and $i+j\le T$, so the admissible pairs are
--   $$
--   (0,0),\ (0,1),\ (1,0),\ (1,1),\ (2,0),\ (2,1),\ (3,0).
--   $$
--
--   It also defines two points of the linear program:
--
--   - the **optimal activity levels of Table 2**: $x_{01}=1/3$, $x_{11}=2/9$, $x_{20}=4/9$, every other $x_{ij}=0$;
--   - the **do-nothing solution** of footnote 3: $x_{00}=1$, every other $x_{ij}=0$.
--
--   The example's cost coefficients (Table 1), its optimal solution (Table 2, footnote 3) and its implicit prices (footnote 5) are stated on these definitions, through the general linear program, so that the example tests the general model.
--
--   **Formalization Note** Table 2 prints $x_{30}=\varepsilon$, "a 'small' positive quantity", "to eliminate the question of degeneracy"; the solution it describes has $x_{30}=0$, which is the value used here. The file contains the short proof that $\sum_n p_n=1$ for this demand law.
-- source:
--   Manne, Linear Programming and Sequential Decisions, Management Science 6 (1960), pp. 263–264 (PDF pp. 6–7), §6, data display, Table 2, footnote 3

import Mathlib
import Definitions.Def_ManneLP_Equilibrium_Model

namespace ManneLP.Equilibrium

/-- The demand law of the §6 example: `p₀ = 2/3`, `p₁ = 0`, `p₂ = 1/3`, `pₙ = 0` for `n ≥ 3`. -/
noncomputable def exampleDemand : ℕ → ℝ :=
  fun n => if n = 0 then 2 / 3 else if n = 2 then 1 / 3 else 0

theorem exampleDemand_hasSum : HasSum exampleDemand 1 := by
  have h : HasSum exampleDemand (∑ n ∈ Finset.range 3, exampleDemand n) :=
    hasSum_sum_of_ne_finset_zero (fun n hn => by
      simp only [Finset.mem_range, not_lt] at hn
      simp only [exampleDemand]
      rw [if_neg (by omega), if_neg (by omega)])
  convert h using 1
  simp [Finset.sum_range_succ, exampleDemand]
  norm_num

/-- The numerical example of §6 (p. 263): `T = 3`; production capacity one unit per month
(`j ∈ {0, 1}`) together with `i + j ≤ T`, giving the admissible pairs
`(0,0), (0,1), (1,0), (1,1), (2,0), (2,1), (3,0)`; demand law `exampleDemand`;
`C₁(i) = i`, `C₂(j) = 3j`, `C₃(m) = max[0, 6m]`. -/
noncomputable def exampleModel : Model where
  T := 3
  T_pos := by norm_num
  A := ((Finset.range 4) ×ˢ (Finset.range 2)).filter (fun a => a.1 + a.2 ≤ 3)
  A_le := by
    intro a ha
    exact (Finset.mem_filter.mp ha).2
  zero_mem := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  p := exampleDemand
  p_nonneg := by
    intro n
    simp only [exampleDemand]
    split_ifs <;> norm_num
  p_hasSum := exampleDemand_hasSum
  C₁ := fun i => (i : ℝ)
  C₂ := fun j => 3 * (j : ℝ)
  C₃ := fun m => max 0 (6 * (m : ℝ))

/-- The optimal activity levels of Table 2 (p. 263): `x₀₁ = 1/3`, `x₁₁ = 2/9`, `x₂₀ = 4/9`, and every
other `xᵢⱼ = 0` (in particular `x₃₀ = 0`; Table 2's `ε` is a device against degeneracy). -/
noncomputable def exampleOptimal : ℕ × ℕ → ℝ :=
  fun a =>
    if a = (0, 1) then 1 / 3 else if a = (1, 1) then 2 / 9 else if a = (2, 0) then 4 / 9 else 0

/-- The do-nothing basic feasible solution of footnote 3 (p. 264): `x₀₀ = 1`, all other unknowns
zero. -/
noncomputable def exampleDoNothing : ℕ × ℕ → ℝ :=
  fun a => if a = (0, 0) then 1 else 0

end ManneLP.Equilibrium


