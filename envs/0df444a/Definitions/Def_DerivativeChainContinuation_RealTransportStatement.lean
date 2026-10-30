-- Prove2me | Definitions.Def_DerivativeChainContinuation_RealTransportStatement
-- name    : DerivativeChainContinuation_RealTransportStatement
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T16:44:24.95454+00:00
-- url     : https://prove2.me/theorems/e7c7f506-dff0-469b-b2ab-2b5f9825599a
-- title:
--   Endpoint transport cost stated directly through derivatives
-- statement:
--   For $p_a(X)=\prod_{j=0}^{n}(X-a_j)$ and $v\in\mathbb C$, define
--
--   $$C_a(v)=\inf\left\{\sum_{i=0}^{n-1}|z_{i+1}-z_i|:\ p_a^{(n-i)}(z_i)=0\ (0\le i\le n),\ z_n=v\right\}.$$
--
--   This expands the derivative-chain predicate directly so the headline transport inequality can be read without auxiliary chain notation.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RealTransportStatement.lean#L8-L13

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators

noncomputable def explicitEndpointCost {n : ℕ} (a : Fin (n+1) → ℂ) (v : ℂ) : ℝ :=
  sInf {t : ℝ | ∃ z : Fin (n+1) → ℂ,
    (∀ i : Fin (n+1),
      (derivative^[n-i.val] (∏ j : Fin (n+1), (X-C (a j)))).eval (z i)=0) ∧
    z (Fin.last n)=v ∧
    (∑ i : Fin n, ‖z i.succ-z i.castSucc‖)=t}






end DerivativeChainContinuation


