-- Prove2me | Definitions.Def_DerivativeChainContinuation_ComplexHistories
-- name    : DerivativeChainContinuation_ComplexHistories
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:22:29.984506+00:00
-- url     : https://prove2.me/theorems/768fd3cb-ca65-4579-8757-eb881669fa13
-- title:
--   Complete row histories and recursive endpoint costs
-- statement:
--   A history chooses one root slot in each row. Its recursive endpoint cost starts with the distance to the unique first-row point and then minimizes previous cost plus the next Euclidean edge. At actual row endpoints this cost is attained by a complete history.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/ComplexHistories.lean#L14-L15; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/ComplexHistories.lean#L10-L12

import Mathlib
import Definitions.Def_DerivativeChainContinuation_EndpointCost
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators

noncomputable def complexRowHistoryCost (r : ComplexRootRows) : ℕ → ℂ → ℝ
  | 0,v => ‖v-r 0 0‖
  | k+1,v => finiteEndpointCost (fun i => complexRowHistoryCost r k (r k i)) (r k) v

def IsComplexRowHistory (r : ComplexRootRows) {n : ℕ} (z : Fin (n+1) → ℂ) : Prop :=
  ∀ i, ∃ j : Fin (i.val+1), z i=r i.val j








end DerivativeChainContinuation


