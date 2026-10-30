-- Prove2me | Definitions.Def_DerivativeChainContinuation_JoinedPaths
-- name    : DerivativeChainContinuation_JoinedPaths
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:31:21.507733+00:00
-- url     : https://prove2.me/theorems/7d5ef8e9-69ad-4c0d-a7c2-7424c7c3c3f0
-- title:
--   Joining a geodesic prefix to a root tail
-- statement:
--   The function `joinAt` concatenates an initial complex path with a shifted later path at the specified natural-number index. It is the finite path operation used to combine the radial prefix with the energy-controlled tail.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/JoinedPaths.lean#L7-L8

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability

set_option autoImplicit false
namespace DerivativeChainContinuation
open DerivativeChainPrivate
open scoped BigOperators

def joinAt (M : ℕ) (f z : ℕ → ℂ) (i : ℕ) : ℂ :=
  if i < M then f i else z (i-(M-1))











end DerivativeChainContinuation


