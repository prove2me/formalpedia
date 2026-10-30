-- Prove2me | Definitions.Def_DerivativeChainContinuation_BinomialRows
-- name    : DerivativeChainContinuation_BinomialRows
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:29:08.337566+00:00
-- url     : https://prove2.me/theorems/9fe0f645-4d76-4c46-8cb2-5d76311ee13b
-- title:
--   Binomial polynomials with a zero-root multiplicity
-- statement:
--   For $q,r\in\mathbb N$ and $c\in\mathbb C$, define $B_{q,r,c}(X)=X^r(X^q+c)$. This is the one-mode model for the initial radial prefix.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/BinomialRows.lean#L6-L7

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability

set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial

noncomputable def binomialPoly (q r : ℕ) (c : ℂ) : Polynomial ℂ :=
  X^(q+r)+C c*X^r







end DerivativeChainContinuation


