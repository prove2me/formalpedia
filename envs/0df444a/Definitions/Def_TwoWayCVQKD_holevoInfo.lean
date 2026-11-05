-- Prove2me | Definitions.Def_TwoWayCVQKD_holevoInfo
-- name    : TwoWayCVQKD_holevoInfo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:45:41.629676+00:00
-- url     : https://prove2.me/theorems/f5538629-a8aa-4130-827e-f35c49d95e06
-- title:
--   Holevo information $I(X_K:E)$ between Eve and a classical variable
-- statement:
--   The Holevo information between Eve and the honest user $K=A,B$ is
--   $$
--   I(X_K:E):=H(E)-H(E|X_K),
--   $$
--   where $H(E)=S(\rho_E)$ is the von Neumann entropy of Eve's state and $H(E|X_K)$ is the entropy of her state conditioned on the classical variable $X_K$. Both are computed from covariance matrices through Eq. (2): the matrix of Eve's modes, and its conditional matrix given $X_K$.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, Eq. (8), p.6

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08
import Definitions.Def_TwoWayCVQKD_crossCov
import Definitions.Def_TwoWayCVQKD_condCov
import Definitions.Def_TwoWayCVQKD_gaussEntropy
open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, Eq. (8), p.6:
`I(X_K : E) := H(E) - H(E|X_K)`, with `H(E) = S(ρ_E)` the entropy of Eve's Gaussian state and
`H(E|X_K)` the entropy of her state conditioned on the classical variable `X_K`.

**Formalization Note** `eve` lists Eve's `n` modes as linear combinations of the sources. The
conditional state has covariance matrix `condCov`. -/
noncomputable def holevoInfo {S κ : Type*} [Fintype S] [Fintype κ] [DecidableEq κ] {n : ℕ}
    (Sg : Matrix S S ℝ) (eve : QuadratureIndex n → S → ℝ) (x : κ → S → ℝ) : ℝ :=
  gaussEntropy (crossCov Sg eve eve) - gaussEntropy (condCov Sg eve x)

end TwoWayCVQKD


