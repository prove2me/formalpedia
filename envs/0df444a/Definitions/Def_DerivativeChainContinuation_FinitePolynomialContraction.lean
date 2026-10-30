-- Prove2me | Definitions.Def_DerivativeChainContinuation_FinitePolynomialContraction
-- name    : DerivativeChainContinuation_FinitePolynomialContraction
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T23:10:45.242981+00:00
-- url     : https://prove2.me/theorems/2f4b47a5-c056-465b-9473-089ecfd5bb58
-- title:
--   A parameter-dependent finite polynomial map
-- statement:
--   For a natural number $d$, coefficient functions $c_j:\mathbb C\to\mathbb C$ indexed by $0\le j\le d$, and complex $t,y$, define
--
--   $$F_c(t,y)=\sum_{j=0}^{d}c_j(t)y^j.$$
--
--   Analyticity and coefficient bounds are hypotheses of later contraction theorems, rather than part of this data definition.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/FinitePolynomialContraction.lean#L25-L26

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
namespace DerivativeChainContinuation
open scoped BigOperators



noncomputable def polynomialContractionMap (d : ℕ) (c : Fin (d+1) → ℂ → ℂ) (t y : ℂ) : ℂ :=
  ∑ j,c j t*y^j.val


end DerivativeChainContinuation


