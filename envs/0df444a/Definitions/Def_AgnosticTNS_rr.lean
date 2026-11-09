-- Prove2me | Definitions.Def_AgnosticTNS_rr
-- name    : AgnosticTNS_rr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:08.787127+00:00
-- url     : https://prove2.me/theorems/1a2d23f2-da1a-4851-b55c-1017069bb1c5
-- title:
--   Rank bound $r_i=\chi^{|\mathrm{cut}_G(S_i)|}$
-- statement:
--   For a learning sequence of $G$ and bond dimension bound $\chi$, the rank bound at step $i$ is
--   $$
--   r_i=\chi^{|\mathrm{cut}_G(S_i)|}.
--   $$
--   By Claim 2.2 every state of $S_d(G,\chi)$ has Schmidt rank at most $r_i$ across $S_i\mid[n]\setminus S_i$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Section 3.2, Eq. (3.22), p.18

import Mathlib
import Definitions.Def_AgnosticTNS_cut
import Definitions.Def_AgnosticTNS_LearningSequence

namespace AgnosticTNS

/-- **The rank bound `r_i = χ^{|cut_G(S_i)|}`**, Eq. (3.22), p.18 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)). -/
noncomputable def rr {n : ℕ} (G : SimpleGraph (Fin n)) (χ : ℕ) (Ls : LearningSequence n)
    (i : Fin Ls.L) : ℕ :=
  χ ^ (cut G (Ls.S i)).card

end AgnosticTNS


