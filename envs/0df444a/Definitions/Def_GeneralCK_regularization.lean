-- Prove2me | Definitions.Def_GeneralCK_regularization
-- name    : GeneralCK_regularization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-24T22:20:45.761998+00:00
-- url     : https://prove2.me/theorems/60572800-8898-489f-ae40-a7d0f4447ff7
-- title:
--   Complementing the Boolean cube
-- statement:
--   For each dimension $n$, complementEquiv is the equivalence of the Boolean cube that negates every coordinate. Its two inverse laws are proved in the definition. This relabeling connects the channel parameters $p$ and $1-p$ in the endpoint and symmetry reduction.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Regularization.lean#L33-L37

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_GeneralCK_statement

open scoped BigOperators
namespace GeneralCK.Regularization
open scoped BigOperators







def complementEquiv (n : ℕ) : Cube n ≃ Cube n where
  toFun y i := !(y i)
  invFun y i := !(y i)
  left_inv y := by funext i; simp
  right_inv y := by funext i; simp















end GeneralCK.Regularization


