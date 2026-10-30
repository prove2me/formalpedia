-- Prove2me | Definitions.Def_DerivativeChainContinuation_DeficitInequalities
-- name    : DerivativeChainContinuation_DeficitInequalities
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T18:05:25.140235+00:00
-- url     : https://prove2.me/theorems/190b80a5-9ff8-4297-9b58-d12e4867b4af
-- title:
--   Intrinsic maximum root norm
-- statement:
--   Define the intrinsic root radius $R(p)$ as the maximum norm in the finite multiset of complex roots, with value zero for an empty multiset. This radius bounds every actual root and is used in the determinant-to-deficit estimate.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/DeficitInequalities.lean#L34-L35

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators





noncomputable def rootRadius (p : Polynomial ℂ) : ℝ :=
  ((p.roots.toFinset.sup fun z => ‖z‖₊ : NNReal) : ℝ)







end DerivativeChainContinuation


