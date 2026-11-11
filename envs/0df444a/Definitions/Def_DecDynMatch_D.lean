-- Prove2me | Definitions.Def_DecDynMatch_D
-- name    : DecDynMatch_D
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:59:43.261912+00:00
-- url     : https://prove2.me/theorems/56c1c6b3-2aec-4c0d-9955-27f810999809
-- title:
--   Cumulative POSM mismatch cost $D_F(T;I)$
-- statement:
--   For an instance $I$, a replay rule $F$ and a horizon $T$, the **cumulative POSM mismatch cost** is the number of rounds among the first $T$ in which the realized matching of SC-DA with rule $F$ is not the player-optimal stable matching of that round:
--   $$
--   D_F(T;I)=\sum_{t=1}^{T}\mathbf 1\{M_t\ne m^*_t\}.
--   $$
--   For $F(x)=H+2x$ this is the paper's $D(T;I)$ for SC-DA. It is the quantity bounded by the goal theorem.
--
--   **Formalization Note** "$M_t\ne m^*_t$" is "$M_t$ is not a POSM at round $t$"; the POSM is unique, so the two agree. $D_F(0;I)=0$.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), eq. (1), p.5; App. A.4, p.20

import Mathlib
import Definitions.Def_DecDynMatch_IsPOSM
import Definitions.Def_DecDynMatch_exec

namespace DecDynMatch

variable {K : ℕ} {ι : Type*} [Fintype ι]

open Classical in
/-- **Cumulative POSM mismatch cost.** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable
Matching*, arXiv:2610.41912 (held version, sha256 6a27277e…), eq. (1), p.5:
"D_Π(T; I) = Σ_{t=1}^{T} 1{Mₜ ≠ m*ₜ}"; App. A.4, p.20: "Write D_F(T; I) for the mismatch cost
under replay rule F".

`D F I T` is the number of rounds `1 ≤ t ≤ T` in which the realized matching of SC-DA with replay
rule `F` is not the POSM of round `t`.

**Formalization Note.** "`Mₜ ≠ m*ₜ`" is "`Mₜ` is not a POSM at round `t`" (`IsPOSM`); the POSM is
unique, so the two agree. `D F I 0 = 0`. -/
noncomputable def D (F : ℕ → ℕ) (I : Instance K ι) (T : ℕ) : ℕ :=
  ((Finset.Icc 1 T).filter (fun t => ¬ IsPOSM I t (M F I t))).card

end DecDynMatch


