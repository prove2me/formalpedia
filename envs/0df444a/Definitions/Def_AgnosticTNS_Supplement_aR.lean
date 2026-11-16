-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_aR
-- name    : AgnosticTNS_Supplement_aR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:24:50.266884+00:00
-- url     : https://prove2.me/theorems/25e1ff7d-e4aa-4005-bee7-78466da35d7f
-- title:
--   Realisable active size $a_i=|F_i|+\sum_{j\in I_i}\lceil\log_d r_j\rceil$
-- statement:
--   Given a learning sequence $\mathcal L=(S_i,I_i,F_i)_{i=1}^L$ and rank bounds $r_1,\dots,r_L$, set $q_j:=\lceil\log_d r_j\rceil$ (the number of qudits needed for a residual subsystem supporting a state of rank at most $r_j$) and
--   $$
--   a_i := |F_i| + \sum_{j\in I_i} q_j .
--   $$
--   This bounds the size of the active subsystem at step $i$ of the realisable learner (Algorithm 2). The rank bounds are either the uniform $r_j=\chi^{|\mathrm{cut}_G(S_j)|}$ of (4.41) or the weighted ones of (4.42).
--
--   **Formalization Note** $q_j$ is `Nat.clog d r_j`, the least $q$ with $r_j\le d^q$, which equals $\lceil\log_d r_j\rceil$ for $r_j\ge1$, $d\ge2$. These are not the enlarged agnostic sizes $a^{\mathrm{agn}}_i$ of Section 3.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Section 4.2, Eqs. (4.43)–(4.44), p.32

import Mathlib
import Definitions.Def_AgnosticTNS_LearningSequence

namespace AgnosticTNS.Supplement

/-- **The realisable active size** `a_i = |F_i| + Σ_{j ∈ I_i} q_j` with `q_j = ⌈log_d r_j⌉`,
Eqs. (4.43)–(4.44), p.32 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)), for given rank bounds `r_j`
(the uniform `r_j = χ^{|cut_G(S_j)|}` of (4.41) or the weighted ones of (4.42)).

**Formalization Note** `q_j = ⌈log_d r_j⌉` is `Nat.clog d r_j`, the least `q` with `r_j ≤ d^q`
(equal to `⌈log_d r_j⌉` for `r_j ≥ 1` and `d ≥ 2`; `0` when `r_j = 1`). These are not the
enlarged agnostic sizes `a^agn_i` of Section 3. -/
def aR {n : ℕ} (d : ℕ) (Ls : LearningSequence n) (r : Fin Ls.L → ℕ) (i : Fin Ls.L) : ℕ :=
  (Ls.F i).card + ∑ j ∈ Ls.I i, Nat.clog d (r j)

end AgnosticTNS.Supplement


