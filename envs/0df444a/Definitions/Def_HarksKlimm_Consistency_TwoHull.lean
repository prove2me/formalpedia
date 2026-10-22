-- Prove2me | Definitions.Def_HarksKlimm_Consistency_TwoHull
-- name    : HarksKlimm_Consistency_TwoHull
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:10.844859+00:00
-- url     : https://prove2.me/theorems/d69d8c69-dd78-45c1-b1f2-443427e5528a
-- title:
--   Two-function integer hull without offsets
-- statement:
--   For a class $C$, define the two-function integer hull without offsets by
--   $$\mathcal L_{\mathbb Z}^2(C)=\{x\mapsto a_1c_1(x)+a_2c_2(x):a_1,a_2\in\mathbb Z,\ c_1,c_2\in C\}.$$
--   The two functions may coincide and the coefficients may vanish. This is the restricted hull used to express compatibility between different cost functions.
--
--   **Formalization Note** Both witnesses must belong to $C$, so the hull is empty when $C$ is empty. There are no shifts or monotonicity requirements in this definition.
-- source:
--   Harks and Klimm (2012), https://doi.org/10.1287/moor.1120.0543, §4, displayed definition, p. 425 (PDF p. 7)

import Mathlib
set_option autoImplicit false
open scoped NNReal

namespace HarksKlimm.Consistency

def TwoHull (C : Set (ℝ≥0 → ℝ)) : Set (ℝ≥0 → ℝ) :=
  {h | ∃ (a₁ a₂ : ℤ) (c₁ c₂ : ℝ≥0 → ℝ),
    c₁ ∈ C ∧ c₂ ∈ C ∧ ∀ x, h x = (a₁ : ℝ) * c₁ x + (a₂ : ℝ) * c₂ x}

end HarksKlimm.Consistency


