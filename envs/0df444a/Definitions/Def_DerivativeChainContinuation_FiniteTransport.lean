-- Prove2me | Definitions.Def_DerivativeChainContinuation_FiniteTransport
-- name    : DerivativeChainContinuation_FiniteTransport
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T16:42:14.678547+00:00
-- url     : https://prove2.me/theorems/2b854dad-22ff-499d-bde9-93d7bab7e010
-- title:
--   Ordered dispersion of a finite real row
-- statement:
--   For $a_0,\ldots,a_{m-1}\in\mathbb R$, define the centered rank-weighted sum
--
--   $$D(a)=\sum_{i=0}^{m-1}(2i+1-m)a_i.$$
--
--   For ordered rows this dispersion is the potential whose decrease measures transport between interlacing rows.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/FiniteTransport.lean#L6-L7

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
namespace DerivativeChainContinuation
open scoped BigOperators

noncomputable def orderedDispersion {m : ℕ} (a : Fin m → ℝ) : ℝ :=
  ∑ i, (2*(i.val : ℝ)+1-m)*a i












end DerivativeChainContinuation


