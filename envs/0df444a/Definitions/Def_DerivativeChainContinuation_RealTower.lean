-- Prove2me | Definitions.Def_DerivativeChainContinuation_RealTower
-- name    : DerivativeChainContinuation_RealTower
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T16:44:02.282593+00:00
-- url     : https://prove2.me/theorems/e1c816d6-eb82-42ce-8fbf-abb86ac2cf73
-- title:
--   Real derivative rows and their normalized interlacing step
-- statement:
--   A real row family assigns a row $r_k$ of $k+1$ real entries to every integer $k\ge0$. A step at level $k$ requires $r_{k+1}(i)\le r_k(i)\le r_{k+1}(i+1)$ and the polynomial identity
--
--   $$p_{r_{k+1}}^{\prime}=(k+2)p_{r_k}.$$
--
--   This interface records both root interlacing and the normalized derivative relation.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RealTower.lean#L8-L10; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RealTower.lean#L6-L6

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial

abbrev RealRows := (k : ℕ) → Fin (k+1) → ℝ

def RealRowStep (r : RealRows) (k : ℕ) : Prop :=
  (∀ i : Fin (k+1), r (k+1) i.castSucc ≤ r k i ∧ r k i ≤ r (k+1) i.succ) ∧
    (realRootProduct (r (k+1))).derivative = C (k+2 : ℝ)*realRootProduct (r k)




end DerivativeChainContinuation


