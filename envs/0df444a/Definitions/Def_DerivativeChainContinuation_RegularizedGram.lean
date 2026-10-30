-- Prove2me | Definitions.Def_DerivativeChainContinuation_RegularizedGram
-- name    : DerivativeChainContinuation_RegularizedGram
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:20:53.840631+00:00
-- url     : https://prove2.me/theorems/3c1e29ec-b9cf-49af-bdff-0dd6c2409a6a
-- title:
--   Regularized Gram matrices and off-diagonal column energy
-- statement:
--   For a complex square matrix $T$ and real $t$, set $G_t(T)=tI+T^*T$. Define each column off-diagonal energy as the sum of squared norms of its off-diagonal entries. Positive-scale assumptions are kept in the results that require them.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RegularizedGram.lean#L12-L13; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RegularizedGram.lean#L9-L10

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Matrix
open scoped BigOperators ComplexOrder

noncomputable def regularizedGram {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℂ := diagonal (fun _ => (t:ℂ))+T.conjTranspose*T

noncomputable def columnOffDiagonalEnergy {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (j : Fin n) : ℝ := ∑ i, if i=j then 0 else Complex.normSq (T i j)












end DerivativeChainContinuation


