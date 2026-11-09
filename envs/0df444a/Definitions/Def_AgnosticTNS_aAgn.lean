-- Prove2me | Definitions.Def_AgnosticTNS_aAgn
-- name    : AgnosticTNS_aAgn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:37:41.599418+00:00
-- url     : https://prove2.me/theorems/d78b9f61-3b08-4a97-bb3a-0da31d349972
-- title:
--   Active-subsystem bound $a^{\mathrm{agn}}_i$
-- statement:
--   At step $i$ the active subsystem consists of the fresh qudits $F_i$ and the residual qudits of the children of $i$; its size is bounded by
--   $$
--   a^{\mathrm{agn}}_i:=|F_i|+\sum_{j\in I_i}p_j .
--   $$
--   Write $a^{\mathrm{agn}}_{\max}:=\max_i a^{\mathrm{agn}}_i$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Section 3.2, Eq. (3.26), p.19

import Mathlib
import Definitions.Def_AgnosticTNS_pP

namespace AgnosticTNS

/-- **The active-subsystem bound `a^agn_i := |F_i| + Σ_{j ∈ I_i} p_j`**, Eq. (3.26), p.19 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)).
`a^agn_max := max_i a^agn_i` is `Finset.univ.sup (aAgn …)`. -/
noncomputable def aAgn {n : ℕ} (d : ℕ) (G : SimpleGraph (Fin n)) (χ : ℕ) (Ls : LearningSequence n)
    (ε ϑ : ℝ) (i : Fin Ls.L) : ℕ :=
  (Ls.F i).card + ∑ j ∈ Ls.I i, pP d G χ Ls ε ϑ j

end AgnosticTNS


