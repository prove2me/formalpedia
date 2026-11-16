-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_lcGraph
-- name    : AgnosticTNS_Supplement_lcGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:26:04.993405+00:00
-- url     : https://prove2.me/theorems/36f1c822-67b1-42ff-82a0-a22d35b41e46
-- title:
--   Learning complexity $\mathrm{lc}_{d,\chi}(G)$ of a graph
-- statement:
--   The **learning complexity** of a graph $G$ on $[n]$ is the best learning complexity of a learning sequence for $G$ with the uniform rank bounds:
--   $$
--   \mathrm{lc}_{d,\chi}(G) := \min_{\mathcal L} \mathrm{lc}_{d,\chi}(\mathcal L),
--   $$
--   the minimum over all learning sequences $\mathcal L$ for $G$. The minimum exists for $n\ge1$: the one-step sequence $S_1=F_1=[n]$, $I_1=\emptyset$ is a learning sequence.
--
--   **Formalization Note** Written as `sInf` of the set of attained values in $\mathbb N$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Section 4.2, Eq. (4.47), p.32

import Mathlib
import Definitions.Def_AgnosticTNS_Supplement_lcSeq
import Definitions.Def_AgnosticTNS_rr

namespace AgnosticTNS.Supplement

/-- **The learning complexity of a graph** `lc_{d,χ}(G) := min_L lc_{d,χ}(L)`, Eq. (4.47), p.32
(Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): the minimum over all learning sequences for `G` of the
learning complexity with the uniform rank bounds `r_i = χ^{|cut_G(S_i)|}`.

**Formalization Note** `sInf` of a set of natural numbers; for `n ≥ 1` the set is nonempty (the
one-step sequence `S_1 = F_1 = V`, `I_1 = ∅`, p.32), so `sInf` is the minimum. -/
noncomputable def lcGraph {n : ℕ} (d : ℕ) (G : SimpleGraph (Fin n)) (χ : ℕ) : ℕ :=
  sInf {c | ∃ Ls : LearningSequence n, lcSeq d Ls (rr G χ Ls) = c}

end AgnosticTNS.Supplement


