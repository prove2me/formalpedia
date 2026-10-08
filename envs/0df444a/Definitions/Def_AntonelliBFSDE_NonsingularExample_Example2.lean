-- Prove2me | Definitions.Def_AntonelliBFSDE_NonsingularExample_Example2
-- name    : AntonelliBFSDE_NonsingularExample_Example2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T20:00:07.265058+00:00
-- url     : https://prove2.me/theorems/297de5f8-4f6e-4f7c-8eaf-e293fa12353d
-- title:
--   The terminal value and weighted tail integral of Example 2
-- statement:
--   For the system of Example 2, define its terminal value from the forward equation and define the weighted future integral by
--
--   $$
--   U_T=J_0+\int_0^T V_s\,ds,\qquad
--   R_t=\int_t^T(r-t)V_r\,dr.
--   $$
--
--   The first expression is independent of the value assigned to a representative of the $L^1$ process $U$ at the single time $T$. The second is the tail term in equation (3.12).
--
--   **Formalization Note** The shared setting also defines the general deterministic-coefficient system (3.1)–(3.2) with $A_s=C_s=s$ and $J_t=J_0$. Both components and the conditional-expectation argument are required to be integrable where the paper uses them.
-- source:
--   Antonelli, Backward-forward stochastic differential equations, Ann. Appl. Probab. 3(3) (1993), pp. 785, 791–792, (3.1)–(3.3), (3.10)–(3.12)

import Mathlib
import Definitions.Def_AntonelliBFSDE_SingularExample_Setting

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.NonsingularExample

open MeasureTheory

/-- The terminal value of (3.10), defined by its forward integral. -/
noncomputable def UT {Ω : Type*} [MeasurableSpace Ω]
    (T : ℝ≥0) (J₀ : Ω → ℝ) (V : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ :=
  J₀ ω + ∫ s in Set.Ioc (0 : ℝ) (T : ℝ), V s.toNNReal ω 

/-- The weighted Volterra integral in the corrected (3.12). -/
noncomputable def weightedTail {Ω : Type*} [MeasurableSpace Ω]
    (T : ℝ≥0) (V : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ r in Set.Ioc (t : ℝ) (T : ℝ),
    (r - (t : ℝ)) * V r.toNNReal ω 

end AntonelliBFSDE.NonsingularExample


