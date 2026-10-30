-- Prove2me | Definitions.Def_DerivativeChainContinuation_RealTransportGeneral
-- name    : DerivativeChainContinuation_RealTransportGeneral
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T16:41:48.473217+00:00
-- url     : https://prove2.me/theorems/4cda6d0c-c46b-440d-80b3-13fbd2bbd368
-- title:
--   Centroid of a finite real source
-- statement:
--   For $a_0,\ldots,a_n\in\mathbb R$, define
--
--   $$\mu(a)=\frac1{n+1}\sum_{i=0}^{n}a_i.$$
--
--   Subtracting this centroid produces the centered source used in the variance-normalized transport estimate.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RealTransportGeneral.lean#L8-L9

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators

noncomputable def realCentroid {n : ℕ} (a : Fin (n+1) → ℝ) : ℝ :=
  (∑ i,a i)/(n+1 : ℝ)












end DerivativeChainContinuation


