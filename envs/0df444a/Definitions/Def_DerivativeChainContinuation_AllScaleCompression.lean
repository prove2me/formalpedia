-- Prove2me | Definitions.Def_DerivativeChainContinuation_AllScaleCompression
-- name    : DerivativeChainContinuation_AllScaleCompression
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:23:37.600368+00:00
-- url     : https://prove2.me/theorems/17ec9275-8614-4059-855e-902e03fb1171
-- title:
--   Actual derivative products and the compression gap
-- statement:
--   For root slots $a_i$ and squared scale $t$, define the source product $D=\prod_i(t+|a_i|^2)$ and the corresponding product $D\prime$ over roots of the actual monic normalized derivative. With $F=tM_0^2+|M_1|^2$, define the compression gap $\Gamma=tF-tD\prime/D$. Division uses Lean's total field convention; the final analytic estimates assume $t>0$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/AllScaleCompression.lean#L16-L17; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/AllScaleCompression.lean#L13-L14

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PolynomialMoments
import Definitions.Def_DerivativeChainContinuation_ScaleMoments
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace DerivativeChainContinuation
open Matrix Polynomial
open scoped BigOperators ComplexOrder

noncomputable def scaleDerivativeProduct {n : ℕ} (a : Fin n → ℂ) (t : ℝ) : ℝ :=
  ((monicDerivative (∏ i,(X-C (a i)))).roots.map (fun b => t+Complex.normSq b)).prod

noncomputable def scaleCompressionGap {n : ℕ} (a : Fin n → ℂ) (t : ℝ) : ℝ :=
  t*scaleGramFactor a t-t*scaleDerivativeProduct a t/scaleSourceProduct a t




end DerivativeChainContinuation


