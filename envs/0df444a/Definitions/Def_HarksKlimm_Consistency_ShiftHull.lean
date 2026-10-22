-- Prove2me | Definitions.Def_HarksKlimm_Consistency_ShiftHull
-- name    : HarksKlimm_Consistency_ShiftHull
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:11.95147+00:00
-- url     : https://prove2.me/theorems/dc1cc3b5-0c06-471d-a9bc-9a7233e33f33
-- title:
--   Integer hull of a function and one positive translate
-- statement:
--   For a class $C$, define the translated-function integer hull by
--   $$\mathcal L_{\mathbb Z}^3(C)=\{x\mapsto a_1c(x)+a_2c(x+\delta): a_1,a_2\in\mathbb Z,\ c\in C,\ \delta>0\}.$$
--   The same function occurs in both terms. Monotonicity of this hull is a conclusion of later results, not part of its definition.
--
--   **Formalization Note** The shift is a strictly positive nonnegative real. The hull is empty when $C$ is empty; coefficients may be negative or zero.
-- source:
--   Harks and Klimm (2012), https://doi.org/10.1287/moor.1120.0543, §5, displayed definition, p. 426 (PDF p. 8)

import Mathlib
set_option autoImplicit false
open scoped NNReal

namespace HarksKlimm.Consistency

def ShiftHull (C : Set (ℝ≥0 → ℝ)) : Set (ℝ≥0 → ℝ) :=
  {h | ∃ (a₁ a₂ : ℤ) (c : ℝ≥0 → ℝ) (δ : ℝ≥0),
    c ∈ C ∧ 0 < δ ∧ ∀ x, h x = (a₁ : ℝ) * c x + (a₂ : ℝ) * c (x + δ)}

end HarksKlimm.Consistency


