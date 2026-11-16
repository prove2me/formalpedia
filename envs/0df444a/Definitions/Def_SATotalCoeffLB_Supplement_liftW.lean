-- Prove2me | Definitions.Def_SATotalCoeffLB_Supplement_liftW
-- name    : SATotalCoeffLB_Supplement_liftW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:29:36.74605+00:00
-- url     : https://prove2.me/theorems/7ffbeb01-2c50-4042-bd22-6cac35424291
-- title:
--   A polynomial $p(W)$ read in $\mathbb R[W,Q]$
-- statement:
--   For $p$ in the Boolean quotient ring over $W$, $p(W)$ is the same polynomial regarded as an element of $\mathbb R[W, Q]/\langle y^2 - 1 : y \in W \cup Q\rangle$, i.e. the function on $\{\pm1\}^{W \cup Q}$ that ignores the $Q$-coordinates.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), Theorem 9, item 1, p.74

import Mathlib
import Definitions.Def_SATotalCoeffLB_CubeFn

namespace SATotalCoeffLB.Supplement

open SATotalCoeffLB

/-- **A polynomial `p(W)` of `ℝ[W]` read in `ℝ[W, Q]`** (Theorem 9, item 1, p.74, of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178)):
the function on the cube of `W ⊕ Q` that reads only the `W`-bits. -/
def liftW {W Q : Type*} (p : CubeFn W) : CubeFn (W ⊕ Q) :=
  fun z => p (fun w => z (Sum.inl w))

end SATotalCoeffLB.Supplement


