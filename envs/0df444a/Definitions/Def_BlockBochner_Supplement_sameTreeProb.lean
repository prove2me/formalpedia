-- Prove2me | Definitions.Def_BlockBochner_Supplement_sameTreeProb
-- name    : BlockBochner_Supplement_sameTreeProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:32:43.858865+00:00
-- url     : https://prove2.me/theorems/50167feb-70a0-446f-90bf-31ba82a3cee5
-- title:
--   $s_{ij}$: probability that $i,j$ are edges of the same tree of $F$
-- statement:
--   For the fugacity measure $\mu$ on the forests $F$ of a finite multigraph,
--   $$
--   s_{ij}=\Pr_\mu\big[i\text{ and }j\text{ are edges of the same tree component of }F\big],\qquad S=(s_{ij})_{i,j\in E}.
--   $$
--   That is, $i\in F$, $j\in F$, and $i,j$ lie in one connected component of the forest $(W,F)$. In particular $s_{ii}=p_i$ and $s_{ij}\le p_{ij}$.
--
--   **Formalization Note** The sum of $\mu(F)$ over edge sets $F$ containing $i$ and $j$ in which an endpoint of $i$ is connected to an endpoint of $j$ through edges of $F$; $\mu(F)=0$ off the forest family.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228 (sha256 e4bc2683…4a27706), Sec. 5.3, p.33 (PDF p.34)

import Mathlib
import Definitions.Def_BlockBochner_Supplement_fugacityProb
import Definitions.Def_BlockBochner_Supplement_edgeConn

namespace BlockBochner.Supplement

open Classical in
/-- **`s_ij`: probability that `i, j` lie in the same tree.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 5.3,
p.33: `s_ij = Pr_µ[i, j are edges of the same tree component of F]` and `S = (s_ij)_{i,j∈E}`;
in particular `s_ii = p_i`.

**Formalization Note** The sum of `µ(F)` over the edge sets `F` with `i ∈ F`, `j ∈ F`, and an endpoint
of `i` connected to an endpoint of `j` in `(W, F)` (`edgeConn`); then `i` and `j` lie in one connected
component of the forest. `µ` is `fugacityProb I lam`, with `I` the forest family. -/
noncomputable def sameTreeProb {W α : Type*} [Fintype α] (ends : α → Sym2 W)
    (I : Finset α → Prop) (lam : α → ℝ) (i j : α) : ℝ :=
  ∑ F ∈ Finset.univ.filter (fun F : Finset α => i ∈ F ∧ j ∈ F ∧
      ∃ u ∈ ends i, ∃ v ∈ ends j, edgeConn ends F u v), fugacityProb I lam F

end BlockBochner.Supplement


