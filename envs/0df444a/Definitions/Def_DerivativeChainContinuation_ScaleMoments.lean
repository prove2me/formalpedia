-- Prove2me | Definitions.Def_DerivativeChainContinuation_ScaleMoments
-- name    : DerivativeChainContinuation_ScaleMoments
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:21:55.193487+00:00
-- url     : https://prove2.me/theorems/36377b61-8cd0-4824-af0c-c3c8fb722f57
-- title:
--   Positive-scale weighted complex root moments
-- statement:
--   For $n$ root slots and real squared scale $t$, define $w_i=1/[n(t+|a_i|^2)]$, $M_0=\sum_iw_i$, $M_1=\sum_iw_i a_i$, $F=tM_0^2+|M_1|^2$ and $D=\prod_i(t+|a_i|^2)$. Final bounds impose nonzero root count and positive scale explicitly.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/ScaleMoments.lean#L12-L13; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/ScaleMoments.lean#L10-L11; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/ScaleMoments.lean#L8-L9; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/ScaleMoments.lean#L14-L15; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/ScaleMoments.lean#L6-L7

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
namespace DerivativeChainContinuation
open scoped BigOperators

noncomputable def scaleWeight {n : ℕ} (a : Fin n → ℂ) (t : ℝ) (i : Fin n) : ℝ :=
  (n:ℝ)⁻¹/(t+Complex.normSq (a i))
noncomputable def scaleMeanZero {n : ℕ} (a : Fin n → ℂ) (t : ℝ) : ℝ :=
  ∑ i,scaleWeight a t i
noncomputable def scaleMeanOne {n : ℕ} (a : Fin n → ℂ) (t : ℝ) : ℂ :=
  ∑ i,(scaleWeight a t i:ℂ)*a i
noncomputable def scaleGramFactor {n : ℕ} (a : Fin n → ℂ) (t : ℝ) : ℝ :=
  t*(scaleMeanZero a t)^2+Complex.normSq (scaleMeanOne a t)
noncomputable def scaleSourceProduct {n : ℕ} (a : Fin n → ℂ) (t : ℝ) : ℝ :=
  ∏ i,(t+Complex.normSq (a i))






end DerivativeChainContinuation


