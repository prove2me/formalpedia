-- Prove2me | Definitions.Def_DetAuctions_Supplement_IsDeterministic
-- name    : DetAuctions_Supplement_IsDeterministic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:41:51.364349+00:00
-- url     : https://prove2.me/theorems/349fc34e-cbb7-4a3f-8a19-ccded6d97b9a
-- title:
--   Deterministic mechanism (allocation in $\{0,1\}^m$)
-- statement:
--   A selling mechanism $M=(a,p)$ for $m$ items has an allocation $a=(a_1,\dots,a_m):V\to[0,1]^m$, where $a_j(b)$ is the probability with which item $j$ is sold on bid profile $b$. The mechanism is **deterministic** if
--   $$a(b)\in\{0,1\}^m\quad\text{for every bid profile } b,$$
--   i.e. every item is either sold for sure or not sold at all. General mechanisms with $a\in[0,1]^m$ are sometimes called lotteries.
--
--   The predicate is used to state that the paper's $2.19$ lower bound for $\max\{\mathsf{SREV},\mathsf{BREV}\}$ is already attained by a deterministic auction (Theorem D.1).
--
--   **Formalization Note** A predicate on the published `MultiItemRev.Decomp.Mechanism`, whose allocation `q` is the paper's $a$; it is required at every profile of $\mathbb R_{\ge0}^m$, the value space of the published model.
-- source:
--   Giannakopoulos, Hahn, On the Power of Determinism in Multi-Item Auctions, arXiv:2609.35711 (version of Nov. 3, 2026) [preprint], footnote 6, p.7 (pdf p.9)

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

open MultiItemRev.Decomp
open scoped NNReal

namespace DetAuctions.Supplement

/-- A mechanism is **deterministic** if its allocation lies in `{0, 1}^m`: at every value profile
`x`, every item `j` is either sold with probability `0` or with probability `1`.

Giannakopoulos, Hahn, *On the Power of Determinism in Multi-Item Auctions*, arXiv:2609.35711
(version of Nov. 3, 2026), footnote 6, p.7: "Mechanisms such that a ∈ {0, 1}^m are called
deterministic, while the term lotteries is sometimes also used for general mechanisms with
a ∈ [0, 1]^m, to emphasize the randomness of the allocation rule."

**Formalization Note** A predicate on the published `MultiItemRev.Decomp.Mechanism`, whose
allocation `q : (ι → ℝ≥0) → ι → ℝ` is the paper's `a`; it is required at every profile of
`ℝ≥0^ι`, the value space of the published model. -/
def IsDeterministic {ι : Type*} (M : Mechanism ι) : Prop :=
  ∀ (x : ι → ℝ≥0) (j : ι), M.q x j = 0 ∨ M.q x j = 1

end DetAuctions.Supplement


