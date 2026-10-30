-- Prove2me | Definitions.Def_DerivativeChainContinuation_ReturnPath
-- name    : DerivativeChainContinuation_ReturnPath
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:29:31.298633+00:00
-- url     : https://prove2.me/theorems/ff46d135-48c4-4778-b9bb-83e04b2b2437
-- title:
--   Closing a finite complex path at a chosen center
-- statement:
--   The function `closeAt` keeps the first $r$ entries of a complex path and sets every later entry to a chosen center $u\in\mathbb C$. It adds the single return edge needed by the centroid-return construction.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/ReturnPath.lean#L7-L8

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability

set_option autoImplicit false
namespace DerivativeChainContinuation
open DerivativeChainPrivate
open scoped BigOperators

def closeAt (r : ℕ) (f : ℕ → ℂ) (u : ℂ) (i : ℕ) : ℂ :=
  if i < r then f i else u



end DerivativeChainContinuation


