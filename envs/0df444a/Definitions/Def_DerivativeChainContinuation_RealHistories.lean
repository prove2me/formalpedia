-- Prove2me | Definitions.Def_DerivativeChainContinuation_RealHistories
-- name    : DerivativeChainContinuation_RealHistories
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T16:45:11.846544+00:00
-- url     : https://prove2.me/theorems/6864b7ed-65c5-4de7-b24d-d0358641b7bd
-- title:
--   Real history membership and total chain length
-- statement:
--   For $z_0,\ldots,z_n\in\mathbb R$, define
--
--   $$L(z)=\sum_{i=0}^{n-1}|z_{i+1}-z_i|.$$
--
--   A sequence is a history of the triangular row family $r$ when $z_i$ is an entry of row $r_i$ at every level $i$. No nearest-parent constraint is imposed.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RealHistories.lean#L10-L11; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RealHistories.lean#L7-L8

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RealTower
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open scoped BigOperators

noncomputable def realChainCost {n : ℕ} (z : Fin (n+1) → ℝ) : ℝ :=
  ∑ i : Fin n, |z i.succ-z i.castSucc|

def IsRowHistory (r : RealRows) {n : ℕ} (z : Fin (n+1) → ℝ) : Prop :=
  ∀ i : Fin (n+1), ∃ j : Fin (i.val+1), z i=r i.val j








end DerivativeChainContinuation


