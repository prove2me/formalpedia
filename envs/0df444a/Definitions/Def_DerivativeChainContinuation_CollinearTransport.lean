-- Prove2me | Definitions.Def_DerivativeChainContinuation_CollinearTransport
-- name    : DerivativeChainContinuation_CollinearTransport
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T16:41:23.728608+00:00
-- url     : https://prove2.me/theorems/0f974a9c-9164-4c0a-b016-dc4a0bd9ab7f
-- title:
--   Complex endpoint transport cost, centroid, and normalized ratio
-- statement:
--   For $a_0,\ldots,a_n\in\mathbb C$, let $\mu=(n+1)^{-1}\sum_i a_i$. Let $C_a(v)$ be the infimum of $L(z)=\sum_{i=0}^{n-1}|z_{i+1}-z_i|$ over derivative chains for $\prod_i(X-a_i)$ ending at $v$. Define
--
--   $$R(a)=\frac{\sum_i C_a(a_i)^2}{\sum_i|a_i-\mu|^2}.$$
--
--   The transport theorem controls this ratio when the roots are collinear and the denominator is positive.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/CollinearTransport.lean#L9-L10; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/CollinearTransport.lean#L72-L73; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/CollinearTransport.lean#L75-L76

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators

noncomputable def complexCentroid {n : ℕ} (a : Fin (n+1) → ℂ) : ℂ :=
  (∑ i,a i)/(n+1 : ℂ)









noncomputable def complexEndpointCost {n : ℕ} (a : Fin (n+1) → ℂ) (v : ℂ) : ℝ :=
  sInf {t : ℝ | ∃ z : Fin (n+1) → ℂ,IsChain a z ∧ z (Fin.last n)=v ∧ chainCost z=t}

noncomputable def uniformComplexTransportRatio {n : ℕ} (a : Fin (n+1) → ℂ) : ℝ :=
  (∑ i,(complexEndpointCost a (a i))^2)/(∑ i,‖a i-complexCentroid a‖^2)




end DerivativeChainContinuation


