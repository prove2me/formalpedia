-- Prove2me | Definitions.Def_Kyprianou_Ch03_EsscherDensity
-- name    : Kyprianou_Ch03_EsscherDensity
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-14T13:36:15.69287+00:00
-- url     : https://prove2.me/theorems/f517d219-91f5-480d-b37d-d30971dc69e8
-- title:
--   Esscher finite-time exponential density
-- statement:
--   For a real process X, an Esscher parameter beta and base Laplace exponent value psiBeta, the finite-time density is exp(beta*X_t-psiBeta*t). Its martingale and change-of-measure properties are separate proof obligations.
-- source:
--   Kyprianou (2006), Chapter 3, equation (3.11), printed p. 78.

import Mathlib
set_option autoImplicit false
namespace Kyprianou.Ch03
/-- The exponential Esscher martingale density at deterministic time t. -/
noncomputable def esscherDensity
    {Omega : Type} (X : NNReal -> Omega -> Real)
    (beta psiBeta : Real) (t : NNReal) (omega : Omega) : Real :=
  Real.exp (beta * X t omega - psiBeta * (t : Real))
end Kyprianou.Ch03


