-- Prove2me | Definitions.Def_DerivativeChainContinuation_RealInterlacing
-- name    : DerivativeChainContinuation_RealInterlacing
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T16:42:40.407786+00:00
-- url     : https://prove2.me/theorems/b21b1e7c-6545-4bc5-9d3d-5557842884d7
-- title:
--   Monic root product for a finite real row
-- statement:
--   For a finite real row $a_0,\ldots,a_{m-1}$, define the monic polynomial
--
--   $$p_a(X)=\prod_{i=0}^{m-1}(X-a_i).$$
--
--   Repeated entries are retained with their multiplicities. This polynomial represents each row of a real derivative tower.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RealInterlacing.lean#L7-L8

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators

noncomputable def realRootProduct {n : ℕ} (a : Fin n → ℝ) : Polynomial ℝ :=
  ∏ i, (X-C (a i))










end DerivativeChainContinuation


