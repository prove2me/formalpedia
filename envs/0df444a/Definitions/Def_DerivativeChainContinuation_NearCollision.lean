-- Prove2me | Definitions.Def_DerivativeChainContinuation_NearCollision
-- name    : DerivativeChainContinuation_NearCollision
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:18:55.269623+00:00
-- url     : https://prove2.me/theorems/58fc81b3-14bb-4c76-a76b-611abde906ef
-- title:
--   Localized positive-part near-collision charge
-- statement:
--   For finite real weights $w_i$, complex points $x_i$ and real charges $c_i$, define $$\mathcal C(w,x,c)=\sum_{i,j}w_iw_j\max(c_i-2|x_i-x_j|,0).$$ The charge is localized by the actual pair distance.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/NearCollision.lean#L6-L8

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
namespace DerivativeChainContinuation
open scoped BigOperators

noncomputable def nearCollisionCharge {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (x : ι → ℂ) (c : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, w i*w j*max (c i-2*‖x i-x j‖) 0





end DerivativeChainContinuation


