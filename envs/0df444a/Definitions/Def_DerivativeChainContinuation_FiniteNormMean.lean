-- Prove2me | Definitions.Def_DerivativeChainContinuation_FiniteNormMean
-- name    : DerivativeChainContinuation_FiniteNormMean
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:19:28.984446+00:00
-- url     : https://prove2.me/theorems/67b4429f-3c6a-4627-abc5-96db9fbca794
-- title:
--   Finite Gini dispersion and kernel travel costs
-- statement:
--   For finite real weights $w_i$ and complex points $x_i$, define $G(w,x)=\sum_{i,j}w_iw_j|x_i-x_j|$. For a finite kernel $K_{ia}$ define $c_i=\sum_aK_{ia}|y_a-x_i|$ and the conditional pair-distance $d_{ij}=\sum_{a,b}K_{ia}K_{jb}|y_a-y_b|$. Positivity and normalization are imposed by theorems that need them.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/FiniteNormMean.lean#L22-L23; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/FiniteNormMean.lean#L25-L27; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/FiniteNormMean.lean#L29-L31

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
namespace DerivativeChainContinuation
open scoped BigOperators





noncomputable def finiteGini {ι : Type*} [Fintype ι] (w : ι → ℝ) (z : ι → ℂ) : ℝ :=
  ∑ i, ∑ j, w i*w j*‖z i-z j‖

noncomputable def kernelCost {ι κ : Type*} [Fintype κ]
    (K : ι → κ → ℝ) (x : ι → ℂ) (y : κ → ℂ) (i : ι) : ℝ :=
  ∑ a, K i a*‖y a-x i‖

noncomputable def kernelPairDistance {ι κ : Type*} [Fintype κ]
    (K : ι → κ → ℝ) (y : κ → ℂ) (i j : ι) : ℝ :=
  ∑ a, ∑ b, K i a*K j b*‖y a-y b‖


end DerivativeChainContinuation


