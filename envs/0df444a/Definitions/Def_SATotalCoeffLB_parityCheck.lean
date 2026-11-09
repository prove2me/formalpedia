-- Prove2me | Definitions.Def_SATotalCoeffLB_parityCheck
-- name    : SATotalCoeffLB_parityCheck
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:18:38.340989+00:00
-- url     : https://prove2.me/theorems/dd5200b8-1970-4297-a51b-ec605624d815
-- title:
--   Parity check $q_e = (1 - s_e Y_e \prod_{j\in S_e} T_j)/2$
-- statement:
--   For a pair $e$, a sign $s_e \in \{\pm1\}$ and a set $S_e \subseteq [t]$, the **parity check** is
--
--   $$
--   q_e = \frac{1 - s_e\, Y_e \prod_{j \in S_e} T_j}{2}.
--   $$
--
--   On the cube it equals $0$ if $Y_e \prod_{j \in S_e} T_j = s_e$ (the parity of $Y_e$ and the $T_j$, $j \in S_e$, is the one prescribed by $s_e$) and $1$ otherwise. It is an $(|S_e|+1)$-junta with coefficients of magnitude at most $1/2$.
--
--   **Formalization Note** The sign is a real number $\sigma$; every statement that uses it assumes $\sigma = 1$ or $\sigma = -1$.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), p.9 (Parity Checks)

import Mathlib
import Definitions.Def_SATotalCoeffLB_Var__c31706
import Definitions.Def_SATotalCoeffLB_var

namespace SATotalCoeffLB

/-- **The parity check** `q_e := (1 − s_e Y_e ∏_{ℓ ∈ S_e} T_ℓ)/2` for a pair `e`, a sign `s_e` and
a set `S_e ⊆ [t]` (p.9 of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178); Eq. (24), p.49, with `S_e` the support of the column `H_{·,e}`).
On the cube, for `s_e = ±1`, it is `0` if `Y_e ∏_{ℓ∈S_e} T_ℓ = s_e` and `1` otherwise.

**Formalization Note** The sign is a real number `σ`; the statements that use it assume
`σ = 1 ∨ σ = -1`. -/
noncomputable def parityCheck {n t : ℕ} (S : Finset (Fin t)) (σ : ℝ) (e : Pair n) :
    CubeFn (Var n t) :=
  fun x => (1 - σ * var (Sum.inr (Sum.inl e) : Var n t) x *
    ∏ ℓ ∈ S, var (Sum.inr (Sum.inr ℓ) : Var n t) x) / 2

end SATotalCoeffLB


