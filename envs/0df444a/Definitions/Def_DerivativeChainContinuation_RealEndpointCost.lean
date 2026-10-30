-- Prove2me | Definitions.Def_DerivativeChainContinuation_RealEndpointCost
-- name    : DerivativeChainContinuation_RealEndpointCost
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T16:45:52.52795+00:00
-- url     : https://prove2.me/theorems/8ed78d6a-3cea-47af-8ce5-4ebcd9ed32c0
-- title:
--   Recursive history costs and their uniform row mean
-- statement:
--   For a real row family $r_k$ with $k+1$ entries, define the endpoint-history cost recursively by
--
--   $$H_r(0,v)=|v-r_0(0)|,\qquad H_r(k+1,v)=\min_{0\le i\le k}\bigl(H_r(k,r_k(i))+|r_k(i)-v|\bigr).$$
--
--   Its row mean is $\overline H_r(k)=(k+1)^{-1}\sum_i H_r(k,r_k(i))$. These costs implement optimal transport through consecutive root rows.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RealEndpointCost.lean#L13-L14; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RealEndpointCost.lean#L8-L11

import Mathlib
import Definitions.Def_DerivativeChainContinuation_EndpointCost
import Definitions.Def_DerivativeChainContinuation_RealTower
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
namespace DerivativeChainContinuation
open scoped BigOperators

noncomputable def realHistoryCost (r : RealRows) : ℕ → ℝ → ℝ
  | 0,v => |v-r 0 0|
  | k+1,v => finiteEndpointCost (fun i : Fin (k+1) => realHistoryCost r k (r k i))
      (fun i => (r k i : ℂ)) (v : ℂ)

noncomputable def meanHistoryCost (r : RealRows) (k : ℕ) : ℝ :=
  (∑ i,realHistoryCost r k (r k i))/(k+1 : ℝ)












end DerivativeChainContinuation


