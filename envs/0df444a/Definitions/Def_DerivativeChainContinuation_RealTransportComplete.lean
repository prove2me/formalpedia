-- Prove2me | Definitions.Def_DerivativeChainContinuation_RealTransportComplete
-- name    : DerivativeChainContinuation_RealTransportComplete
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T16:43:07.841976+00:00
-- url     : https://prove2.me/theorems/b394d255-5f81-4db4-a359-c6ab60b52fd8
-- title:
--   A finite complex source lies on an affine real line
-- statement:
--   A complex source $a_0,\ldots,a_n$ is collinear when there exist $o,c\in\mathbb C$ with $c
--   e0$ and real numbers $r_0,\ldots,r_n$ such that
--
--   $$a_i=o+cr_i\qquad(0\le i\le n).$$
--
--   This formulation permits repeated roots and arbitrary endpoint order.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RealTransportComplete.lean#L54-L55

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators





def OnComplexLine {n : ℕ} (a : Fin (n+1) → ℂ) : Prop :=
  ∃ o c : ℂ,c≠0 ∧ ∃ r : Fin (n+1) → ℝ,∀ i,a i=o+c*(r i : ℂ)




end DerivativeChainContinuation


