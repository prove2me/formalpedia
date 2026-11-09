-- Prove2me | Definitions.Def_SATotalCoeffLB_Ae
-- name    : SATotalCoeffLB_Ae
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:19:19.529015+00:00
-- url     : https://prove2.me/theorems/357d7676-6802-414e-b22c-dbc3d15573ee
-- title:
--   $A_e = Y_e - \omega_e(X)$
-- statement:
--   For a pair $e = \{i,j\}$, $i<j$,
--
--   $$
--   A_e = Y_e - \omega_e(X), \qquad \omega_e(X) = \frac{1 + X_i + X_j - X_iX_j}{2},
--   $$
--
--   an element of $\mathbb R[X, Y]/\langle y^2-1\rangle$. Since $Y_e^2 = 1$, the AND check satisfies $p_e = Y_e A_e/2$, so bounding the functional $L_0$ on monomial multiples of $A_e$ (Lemma 17, Eq. (29)) bounds it on multiples of $p_e$.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), Section 9.2, p.52

import Mathlib
import Definitions.Def_SATotalCoeffLB_omegaAND
import Definitions.Def_SATotalCoeffLB_Pair

namespace SATotalCoeffLB

/-- **The polynomial `A_e := Y_e − ω_e(X)`** for a pair `e = (i, j)` (Section 9.2, p.52, of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178)),
in the Boolean quotient ring on the variables `X, Y` (`Fin n ⊕ Pair n`). It satisfies
`p_e = Y_e A_e / 2`. -/
noncomputable def Ae {n : ℕ} (e : Pair n) : CubeFn (Fin n ⊕ Pair n) :=
  fun x => var (Sum.inr e : Fin n ⊕ Pair n) x - omegaAND (Sum.inl e.1.1 : Fin n ⊕ Pair n) (Sum.inl e.1.2) x

end SATotalCoeffLB


