-- Prove2me | Definitions.Def_DerivativeChainContinuation_AppellRows
-- name    : DerivativeChainContinuation_AppellRows
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:29:59.308282+00:00
-- url     : https://prove2.me/theorems/b78b4f5d-89f8-470c-920e-e2dac25f8f84
-- title:
--   Normalized Appell polynomial rows
-- statement:
--   For $m\in\mathbb N$ and $c:\mathbb N\to\mathbb C$, define $A_m(X)=\sum_{j=0}^m\binom mj c_jX^{m-j}$. These rows satisfy the normalized derivative recurrence used by the sparse-family proofs.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/AppellRows.lean#L7-L8

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability

set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators

noncomputable def appellRow (m : ℕ) (c : ℕ → ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (m+1), C ((m.choose k:ℂ)*c (m-k))*X^k















end DerivativeChainContinuation


