-- Prove2me | Definitions.Def_DerivativeChainContinuation_CompressionRankTwo
-- name    : DerivativeChainContinuation_CompressionRankTwo
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:20:00.82889+00:00
-- url     : https://prove2.me/theorems/0e68b5b5-4871-4a0a-80b7-011a6ae3815b
-- title:
--   The exact rank-two compression update
-- statement:
--   Define the explicit two-column and two-row factors used to express the root-compression Gram matrix as a diagonal matrix plus a rank-two update. Their entries retain the source centroid sum and the exact factors $1/n$; no centering assumption is inserted.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/CompressionRankTwo.lean#L9-L10; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/CompressionRankTwo.lean#L12-L13

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace DerivativeChainContinuation
open Matrix
open scoped BigOperators

noncomputable def compressionUpdateLeft {n : ℕ} (a : Fin n → ℂ) : Matrix (Fin n) (Fin 2) ℂ :=
  Matrix.of (fun i j => ![star (a i),star (a i)*a i] j)

noncomputable def compressionUpdateRight {n : ℕ} (a : Fin n → ℂ) : Matrix (Fin 2) (Fin n) ℂ :=
  Matrix.of (fun j k => ![((∑ i,a i)/(n:ℂ)-a k)/(n:ℂ),-(n:ℂ)⁻¹] j)




end DerivativeChainContinuation


