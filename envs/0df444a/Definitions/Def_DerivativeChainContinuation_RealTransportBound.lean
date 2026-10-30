-- Prove2me | Definitions.Def_DerivativeChainContinuation_RealTransportBound
-- name    : DerivativeChainContinuation_RealTransportBound
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T16:40:22.616967+00:00
-- url     : https://prove2.me/theorems/d671833c-b881-4ed8-a4c0-9cbf03294dc3
-- title:
--   Real chains through roots of successive derivatives
-- statement:
--   For $p\in\mathbb R[X]$, an integer $n\ge0$, and a real sequence $z_0,\ldots,z_n$, the derivative-chain predicate is
--
--   $$p^{(n-i)}(z_i)=0\qquad(0\le i\le n).$$
--
--   It identifies histories in a factorized root tower with chains for the source polynomial.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RealTransportBound.lean#L10-L11

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators

def IsRealDerivativeChain (p : Polynomial ℝ) (n : ℕ) (z : Fin (n+1) → ℝ) : Prop :=
  ∀ i,(derivative^[n-i.val] p).eval (z i)=0










end DerivativeChainContinuation


