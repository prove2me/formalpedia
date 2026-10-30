-- Prove2me | Definitions.Def_DerivativeChainContinuation_MatrixEnergy
-- name    : DerivativeChainContinuation_MatrixEnergy
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T18:04:57.189438+00:00
-- url     : https://prove2.me/theorems/91772ef4-106b-49e2-9a8e-ec88f7d41e81
-- title:
--   Finite matrix square bounds
-- statement:
--   For a complex finite vector $v$, define its squared Euclidean norm by $\sum_i|v_i|^2$. The predicate $\operatorname{SquareBound}(T,r)$ means $\|Tv\|^2\le r\|v\|^2$ for every vector. These definitions state the operator bounds used in the compression estimates.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/MatrixEnergy.lean#L47-L49; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/MatrixEnergy.lean#L8-L8

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Matrix
open scoped BigOperators

noncomputable def vectorSq {n : ℕ} (v : Fin n → ℂ) : ℝ := ∑ i, Complex.normSq (v i)











/-- Squared Euclidean operator bound, without choosing an operator norm instance. -/
def SquareBound {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) : Prop :=
  ∀ v, vectorSq (M*ᵥv) ≤ r*vectorSq v







end DerivativeChainContinuation


