-- Prove2me | Definitions.Def_AgnosticTNS_Mset
-- name    : AgnosticTNS_Mset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:09.654173+00:00
-- url     : https://prove2.me/theorems/c7ccbe80-7975-4b2e-8e02-74336187fda6
-- title:
--   Active subsystem $M_i$
-- statement:
--   Given residual sets $R_j$ of the earlier steps, the active subsystem of step $i$ of Algorithm 1 is
--   $$
--   M_i:=F_i\cup\bigcup_{j\in I_i}R_j .
--   $$
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Algorithm 1 line 4, p.19

import Mathlib
import Definitions.Def_AgnosticTNS_LearningSequence

namespace AgnosticTNS

/-- **The active subsystem `M_i := F_i ∪ ⋃_{j ∈ I_i} R_j`**, Algorithm 1 line 4, p.19 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)),
for given residual sets `R_j`. -/
def Mset {n : ℕ} (Ls : LearningSequence n) (R : Fin Ls.L → Finset (Fin n)) (i : Fin Ls.L) :
    Finset (Fin n) :=
  Ls.F i ∪ (Ls.I i).biUnion R

end AgnosticTNS


