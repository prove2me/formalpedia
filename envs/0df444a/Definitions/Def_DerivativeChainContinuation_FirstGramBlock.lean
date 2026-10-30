-- Prove2me | Definitions.Def_DerivativeChainContinuation_FirstGramBlock
-- name    : DerivativeChainContinuation_FirstGramBlock
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:21:21.180981+00:00
-- url     : https://prove2.me/theorems/f3f914c1-30d4-4be0-a520-701d00094dcc
-- title:
--   Index equivalence for the first-coordinate Gram split
-- statement:
--   Define the exact equivalence $\{\ast\}\sqcup\{0,\ldots,n-1\}\simeq\{0,\ldots,n\}$ that separates the first coordinate from the remaining coordinates. It is used in the Gram block determinant induction.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/FirstGramBlock.lean#L8-L9

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Matrix
open scoped BigOperators

def firstSumEquiv (n : ℕ) : Unit ⊕ Fin n ≃ Fin (n+1) :=
  (Equiv.sumComm Unit (Fin n)).trans ((Equiv.optionEquivSumPUnit (Fin n)).symm.trans (finSuccEquiv n).symm)






end DerivativeChainContinuation


