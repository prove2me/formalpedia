-- Prove2me | Definitions.Def_DerivativeChainContinuation_RootCovariance
-- name    : DerivativeChainContinuation_RootCovariance
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T18:06:57.584833+00:00
-- url     : https://prove2.me/theorems/cd888c56-aa63-498e-8a32-421fa7d1b3ab
-- title:
--   Transverse root variance
-- statement:
--   Define transverse variance by $\beta(p)=(V(p)-|H(p)|)/2$. For centered complex roots this is the smaller eigenvalue of the real covariance matrix.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RootCovariance.lean#L33-L34

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RowCovariance
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial









noncomputable def transverseVariance (p : Polynomial ℂ) : ℝ :=
  (rootVariance p - ‖rootHolomorphicMoment p‖)/2







end DerivativeChainContinuation


