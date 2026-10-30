-- Prove2me | Definitions.Def_DerivativeChainContinuation_AppellCoefficients
-- name    : DerivativeChainContinuation_AppellCoefficients
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:32:22.684793+00:00
-- url     : https://prove2.me/theorems/9206ee86-21bf-4921-94eb-a7f548b3f9df
-- title:
--   Appell coefficients of an arbitrary complex polynomial
-- statement:
--   For $p\in\mathbb C[X]$ of degree $n$ and $j\in\mathbb N$, define $c_j=p_{n-j}/\binom nj$, using the total division operation on complex numbers. These normalized coefficients reconstruct $p$ through its degree-$n$ Appell row.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/AppellCoefficients.lean#L7-L8

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability

set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial

noncomputable def appellCoefficients (p : Polynomial ℂ) (j : ℕ) : ℂ :=
  p.coeff (p.natDegree-j)/(p.natDegree.choose j:ℂ)







end DerivativeChainContinuation


