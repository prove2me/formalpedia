-- Prove2me | Definitions.Def_SATotalCoeffLB_parityCheckH
-- name    : SATotalCoeffLB_parityCheckH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:19:30.994788+00:00
-- url     : https://prove2.me/theorems/0f0df82a-9ac6-48a0-9540-9a4cdfdf968f
-- title:
--   Parity check of a matrix column, Eq. (24)
-- statement:
--   Let $E$ be a set of pairs, $H \in \mathbb F_2^{t \times E}$ a matrix whose columns are indexed by $E$, and $s = (s_e)_{e\in E}$ signs. For $e \in E$, the parity check of Eq. (24) is
--
--   $$
--   q_e = \frac{1 - s_e\, Y_e\, T^{H_{\cdot,e}}}{2}, \qquad T^u = \prod_{\ell : u_\ell = 1} T_\ell \ (u \in \mathbb F_2^t),
--   $$
--
--   that is, the parity check of $e$ whose set $S_e$ is the support of the column $H_{\cdot,e}$. The system $P_{H,s}$ of Section 9 consists of all AND checks and these parity checks.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), Section 9, Eq. (24), p.49

import Mathlib
import Definitions.Def_SATotalCoeffLB_parityCheck

namespace SATotalCoeffLB

/-- **The parity check of Eq. (24)** `q_e := (1 − s_e Y_e T^{H_{·,e}})/2`, `T^u := ∏_{ℓ : u_ℓ = 1} T_ℓ`
(Section 9, p.49, of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178)), for a set of pairs `E`, a matrix `H ∈ F₂^{t×E}` and signs
`s = (s_e)_{e∈E}`: the parity check of `e ∈ E` whose set is the support of the column `H_{·,e}`. -/
noncomputable def parityCheckH {n t : ℕ} {E : Finset (Pair n)} (H : Matrix (Fin t) E (ZMod 2))
    (s : E → ℝ) (e : E) : CubeFn (Var n t) :=
  parityCheck (Finset.univ.filter fun ℓ => H ℓ e = 1) (s e) e.1

end SATotalCoeffLB


