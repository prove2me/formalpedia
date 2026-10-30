-- Prove2me | Definitions.Def_DerivativeChainContinuation_CompressionGeometry
-- name    : DerivativeChainContinuation_CompressionGeometry
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T18:04:34.859285+00:00
-- url     : https://prove2.me/theorems/03910412-b3fa-47b1-b7db-070561003565
-- title:
--   Ambient root compression and Frobenius energy
-- statement:
--   For $n$ complex root slots, let $P=I-\mathbf1\mathbf1^*/n$ and define the ambient compression $B=P\operatorname{diag}(a)P$. Its squared Frobenius norm is the sum of squared entry norms. This ambient convention includes one additional zero eigenvalue.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/CompressionGeometry.lean#L8-L10; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/CompressionGeometry.lean#L16-L17; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/CompressionGeometry.lean#L12-L14

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open scoped BigOperators
open Matrix

/-- Orthogonal projection onto the zero-sum coordinate hyperplane. -/
noncomputable def centeringProjection (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  1 - Matrix.of (fun _ _ => (n : ℂ)⁻¹)

/-- Compression extended by zero on the constant vector. -/
noncomputable def rootCompression {n : ℕ} (a : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  centeringProjection n * diagonal a * centeringProjection n

noncomputable def frobeniusSq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j)











end DerivativeChainContinuation


