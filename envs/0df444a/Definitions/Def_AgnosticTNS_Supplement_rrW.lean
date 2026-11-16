-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_rrW
-- name    : AgnosticTNS_Supplement_rrW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:24:26.07021+00:00
-- url     : https://prove2.me/theorems/d63f6396-7d74-4b0d-9e08-9d9f5036e96c
-- title:
--   Weighted rank bound $r_i=\prod_{e\in\mathrm{cut}_G(S_i)}w(e)$
-- statement:
--   Let $G=([n],E)$ be a graph with edge dimensions $w:E\to\mathbb N$ and let $\mathcal L=(S_i,I_i,F_i)_{i=1}^L$ be a learning sequence for $G$. The **weighted rank bound** of step $i$ is
--   $$
--   r_i := \prod_{e\in\mathrm{cut}_G(S_i)} w(e),
--   $$
--   with the empty product equal to $1$. Every state in $S_d(G,w)$ has reduced rank at most $r_i$ across the cut $S_i\mid[n]\setminus S_i$; it replaces the uniform bound $\chi^{|\mathrm{cut}_G(S_i)|}$ when the edge dimensions are known.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Section 4.2, Eq. (4.42), p.32

import Mathlib
import Definitions.Def_AgnosticTNS_cut
import Definitions.Def_AgnosticTNS_LearningSequence

namespace AgnosticTNS.Supplement

/-- **The weighted rank bound** `r_i = ∏_{e ∈ cut_G(S_i)} w(e)`, Eq. (4.42), p.32 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)).
The empty product is `1`.

**Formalization Note** `w : E → ℕ` is any edge-dimension function on the edges of `G`. -/
noncomputable def rrW {n : ℕ} (G : SimpleGraph (Fin n)) (w : G.edgeSet → ℕ) (Ls : LearningSequence n)
    (i : Fin Ls.L) : ℕ :=
  ∏ e ∈ cut G (Ls.S i), w e

end AgnosticTNS.Supplement


