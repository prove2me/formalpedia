-- Prove2me | Definitions.Def_SATotalCoeffLB_omegaAND
-- name    : SATotalCoeffLB_omegaAND
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:18:12.151274+00:00
-- url     : https://prove2.me/theorems/c0420236-cf5e-4340-963c-e1376a7b6744
-- title:
--   AND polynomial $\omega(U,W) = (1+U+W-UW)/2$
-- statement:
--   For two variables $U, W$, the **AND polynomial** is
--
--   $$
--   \omega(U, W) = \frac{1 + U + W - UW}{2}.
--   $$
--
--   On the $\pm1$ cube it equals $-1$ exactly when $U = W = -1$, so it computes the AND of the two Boolean values in the $\{\pm1\}$ encoding: with $U = (-1)^{\bar u}$, $W = (-1)^{\bar w}$ it equals $(-1)^{\bar u \bar w}$. The paper writes $\omega_{ij}(X) = \omega(X_i, X_j)$.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), p.9 and p.49 (ω_ij)

import Mathlib
import Definitions.Def_SATotalCoeffLB_var

namespace SATotalCoeffLB

/-- **The AND polynomial** `ω(U, W) := (1 + U + W − UW)/2` of two variables (the `ω_ij(X_i, X_j)`
of p.9 and p.49 of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178)). In the `±1` encoding it is `-1` exactly when both inputs are `-1`,
i.e. it computes AND (it equals `(-1)^{x̄_i x̄_j}`). -/
noncomputable def omegaAND {V : Type*} (u w : V) : CubeFn V :=
  fun x => (1 + var u x + var w x - var u x * var w x) / 2

end SATotalCoeffLB


