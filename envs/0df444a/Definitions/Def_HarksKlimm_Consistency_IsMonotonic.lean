-- Prove2me | Definitions.Def_HarksKlimm_Consistency_IsMonotonic
-- name    : HarksKlimm_Consistency_IsMonotonic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:08.510987+00:00
-- url     : https://prove2.me/theorems/cc80fc61-c8fd-42f3-bde0-20e126782877
-- title:
--   Monotonicity in either direction
-- statement:
--   A function $c:[0,\infty)\to\mathbb R$ is monotonic if it is nondecreasing or nonincreasing:
--   $$(\forall x\le y,\ c(x)\le c(y))\quad\text{or}\quad(\forall x\le y,\ c(y)\le c(x)).$$
--   The direction is a property of the whole function, and can differ between functions. Constants satisfy both alternatives.
--
--   **Formalization Note** The domain is the nonnegative real half-line, including zero; costs take arbitrary real values.
-- source:
--   Harks and Klimm (2012), https://doi.org/10.1287/moor.1120.0543, §1.1 monotonicity convention; Lemma 3.1, p. 422 (PDF p. 4)

import Mathlib
set_option autoImplicit false
open scoped NNReal

namespace HarksKlimm.Consistency

def IsMonotonic (c : ℝ≥0 → ℝ) : Prop := Monotone c ∨ Antitone c

end HarksKlimm.Consistency


