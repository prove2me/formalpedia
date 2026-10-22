-- Prove2me | Definitions.Def_HarksKlimm_Consistency_IsExponential
-- name    : HarksKlimm_Consistency_IsExponential
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:07.929106+00:00
-- url     : https://prove2.me/theorems/57b5cb55-86d4-4e0b-90a0-ebefa892fbbd
-- title:
--   Exponential functions with a specified rate
-- statement:
--   For a specified real rate $\varphi$, a function $c:[0,\infty)\to\mathbb R$ has exponential form with that rate if
--   $$\exists a,b\in\mathbb R\ \forall x\ge0,\quad c(x)=ae^{\varphi x}+b.$$
--   The rate parameter is explicit so that one can distinguish a shared rate for a class from rates chosen separately for its members. Zero rates and zero amplitudes are allowed.
--
--   **Formalization Note** The domain is the nonnegative real half-line, including zero; costs take arbitrary real values.
-- source:
--   Harks and Klimm (2012), https://doi.org/10.1287/moor.1120.0543, Theorem 5.1, p. 427 (PDF p. 9)

import Mathlib
set_option autoImplicit false
open scoped NNReal

namespace HarksKlimm.Consistency

def IsExponential (φ : ℝ) (c : ℝ≥0 → ℝ) : Prop :=
  ∃ a b : ℝ, ∀ x : ℝ≥0, c x = a * Real.exp (φ * (x : ℝ)) + b

end HarksKlimm.Consistency


