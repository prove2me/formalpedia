-- Prove2me | Definitions.Def_DerivativeChainContinuation_Sixth9ValidatedInverse
-- name    : DerivativeChainContinuation_Sixth9ValidatedInverse
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T23:14:36.489435+00:00
-- url     : https://prove2.me/theorems/b068eb77-df0a-445c-9899-d5a4ff4439c9
-- title:
--   Coefficient and bound vectors for the validated inverse
-- statement:
--   Use the four exact residual coefficient polynomials $C_0,C_1,C_2,C_3$ as the coefficient-function vector. Define the real bound vector
--
--   $$b=(10^{-12},10^{-5},1,1).$$
--
--   The definitions provide the inputs to the finite polynomial contraction theorem. The coefficient estimates and root-family conclusions are proved separately.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/Sixth9ValidatedInverse.lean#L15-L16; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/Sixth9ValidatedInverse.lean#L18-L18

import Mathlib
import Definitions.Def_DerivativeChainContinuation_Sixth9C0Data
import Definitions.Def_DerivativeChainContinuation_Sixth9C1Data
import Definitions.Def_DerivativeChainContinuation_Sixth9C2Data
import Definitions.Def_DerivativeChainContinuation_Sixth9C3Data
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open scoped BigOperators

noncomputable def sixth9NewtonCoefficients (j : Fin 4) : ℂ → ℂ :=
  ![sixth9C0,sixth9C1,sixth9C2,sixth9C3] j

noncomputable def sixth9NewtonBounds : Fin 4 → ℝ := ![1/1000000000000,1/100000,1,1]






end DerivativeChainContinuation


