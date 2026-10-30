-- Prove2me | Definitions.Def_DerivativeChainContinuation_Covariance
-- name    : DerivativeChainContinuation_Covariance
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T18:02:36.412101+00:00
-- url     : https://prove2.me/theorems/8d719504-b561-43bc-bc22-f02cd850b626
-- title:
--   Finite complex second moments and covariance matrix
-- statement:
--   Define the uniform mean squared norm $V$, the complex mean square $H$, and the real two-by-two second-moment matrix of a finite complex root list. These become centered variance and covariance when the list has mean zero.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/Covariance.lean#L13-L15; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/Covariance.lean#L10-L11; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/Covariance.lean#L7-L8

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations


set_option autoImplicit false
namespace DerivativeChainContinuation
open scoped BigOperators

noncomputable def secondMoment {n : ℕ} (a : Fin n → ℂ) : ℝ :=
  (∑ i, Complex.normSq (a i)) / n

noncomputable def holomorphicMoment {n : ℕ} (a : Fin n → ℂ) : ℂ :=
  Complex.ofReal ((n : ℝ)⁻¹) * ∑ i, (a i)^2

noncomputable def covariance {n : ℕ} (a : Fin n → ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(∑ i, (a i).re^2) / n, (∑ i, (a i).re * (a i).im) / n;
     (∑ i, (a i).re * (a i).im) / n, (∑ i, (a i).im^2) / n]













end DerivativeChainContinuation


