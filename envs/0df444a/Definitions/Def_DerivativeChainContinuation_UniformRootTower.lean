-- Prove2me | Definitions.Def_DerivativeChainContinuation_UniformRootTower
-- name    : DerivativeChainContinuation_UniformRootTower
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:20:26.45697+00:00
-- url     : https://prove2.me/theorems/89aca0ee-eaf3-414b-a454-5c117148f805
-- title:
--   Uniform actual polynomial root rows
-- statement:
--   Define rows $r_k$ with $k+1$ complex root slots and their monic root products. A uniform polynomial step requires the exact normalized derivative relation and a nonnegative barycentric kernel with uniform parent and child marginals. Coincident roots retain separate slots.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/UniformRootTower.lean#L6-L6; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/UniformRootTower.lean#L11-L16; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/UniformRootTower.lean#L8-L9

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators
abbrev ComplexRootRows := (k : ℕ) → Fin (k+1) → ℂ

noncomputable def complexRowProduct (r : ComplexRootRows) (k : ℕ) : Polynomial ℂ :=
  ∏ i, (X-C (r k i))

def UniformPolynomialStep (r : ComplexRootRows) (k : ℕ) : Prop :=
  (complexRowProduct r (k+1)).derivative = C (k+2 : ℂ)*complexRowProduct r k ∧
  ∃ K : Fin (k+1) → Fin (k+2) → ℝ,
    (∀ j i, 0 ≤ K j i) ∧ (∀ j, ∑ i, K j i=1) ∧
    (∀ j, ∑ i, (K j i:ℂ)*r (k+1) i=r k j) ∧
    (∀ i, (∑ j, (k+1:ℝ)⁻¹*K j i)=(k+2:ℝ)⁻¹)


end DerivativeChainContinuation


