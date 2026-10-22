-- Prove2me | Definitions.Def_HarksKlimm_Consistency_IsAffine
-- name    : HarksKlimm_Consistency_IsAffine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:09.863394+00:00
-- url     : https://prove2.me/theorems/2a0552b7-2fe8-4372-be05-1eb50b6319c2
-- title:
--   Affine functions on the nonnegative half-line
-- statement:
--   A function $c:[0,\infty)\to\mathbb R$ is affine if
--   $$\exists a,b\in\mathbb R\ \forall x\ge0,\quad c(x)=ax+b.$$
--   There are no sign restrictions on the slope or intercept. This is the affine alternative in the classification.
--
--   **Formalization Note** The domain is the nonnegative real half-line, including zero; costs take arbitrary real values.
-- source:
--   Harks and Klimm (2012), https://doi.org/10.1287/moor.1120.0543, Theorem 5.1, p. 427 (PDF p. 9)

import Mathlib
set_option autoImplicit false
open scoped NNReal

namespace HarksKlimm.Consistency

def IsAffine (c : ℝ≥0 → ℝ) : Prop :=
  ∃ a b : ℝ, ∀ x : ℝ≥0, c x = a * (x : ℝ) + b

end HarksKlimm.Consistency


