-- Prove2me | Definitions.Def_DerivativeChainContinuation_RowCovariance
-- name    : DerivativeChainContinuation_RowCovariance
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T18:06:02.959544+00:00
-- url     : https://prove2.me/theorems/e15d5240-1cfc-4bf8-ac15-b1836ce98ba8
-- title:
--   Actual polynomial root moments and Schoenberg deficit
-- statement:
--   Define $V(p)$ as the uniform squared norm of the actual roots, $H(p)$ as their uniform complex square, and $\Sigma(p)$ as their real two-dimensional covariance matrix. Define $\delta(p)=(\deg p-2)V(p)-(\deg p-1)V(\operatorname{monicDerivative}p)$. Roots count multiplicity; variance interpretations require centering.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RowCovariance.lean#L14-L17; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RowCovariance.lean#L11-L12; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RowCovariance.lean#L7-L9; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RowCovariance.lean#L19-L21

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PolynomialMoments
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial

/-- Second moment about zero; this is variance when the root centroid is zero. -/
noncomputable def rootVariance (p : Polynomial ℂ) : ℝ :=
  (p.roots.map Complex.normSq).sum / p.natDegree

noncomputable def rootHolomorphicMoment (p : Polynomial ℂ) : ℂ :=
  (p.roots.map fun z => z^2).sum / (p.natDegree : ℂ)

/-- Root second-moment matrix about zero; covariance for centered input. -/
noncomputable def rootCovariance (p : Polynomial ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(rootVariance p + (rootHolomorphicMoment p).re)/2, (rootHolomorphicMoment p).im/2;
     (rootHolomorphicMoment p).im/2, (rootVariance p - (rootHolomorphicMoment p).re)/2]

noncomputable def schoenbergDeficit (p : Polynomial ℂ) : ℝ :=
  (p.natDegree-2 : ℕ) * rootVariance p -
    (p.natDegree-1 : ℕ) * rootVariance (monicDerivative p)






end DerivativeChainContinuation


