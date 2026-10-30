-- Prove2me | Definitions.Def_DerivativeChainContinuation_EndpointCost
-- name    : DerivativeChainContinuation_EndpointCost
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T16:43:31.964256+00:00
-- url     : https://prove2.me/theorems/bb4c79c9-61e5-477c-9e78-999e0ec813f2
-- title:
--   Finite minimum for extending a chain to an endpoint
-- statement:
--   For a finite nonempty index set $I$, real prefix costs $c_i$, complex previous endpoints $x_i$, and a new endpoint $v\in\mathbb C$, define
--
--   $$F(v)=\inf_{i\in I}\bigl(c_i+|x_i-v|\bigr).$$
--
--   This is the least cost of appending $v$ to one of the available prefixes.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/EndpointCost.lean#L5-L7

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
namespace DerivativeChainContinuation

noncomputable def finiteEndpointCost {ι : Type*} [Fintype ι] [Nonempty ι]
    (prefixCost : ι → ℝ) (lastPoint : ι → ℂ) (v : ℂ) : ℝ :=
  ⨅ i, prefixCost i + ‖lastPoint i-v‖










end DerivativeChainContinuation


