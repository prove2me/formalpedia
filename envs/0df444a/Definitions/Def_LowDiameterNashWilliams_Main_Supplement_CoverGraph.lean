-- Prove2me | Definitions.Def_LowDiameterNashWilliams_Main_Supplement_CoverGraph
-- name    : LowDiameterNashWilliams_Main_Supplement_CoverGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T10:34:40.953204+00:00
-- url     : https://prove2.me/theorems/fa0f09de-c108-475a-aa10-d84dc6aadc9b
-- title:
--   Set Cover reduction graph with two cliques
-- statement:
--   For an indexed Set Cover instance $(U,S_1,\ldots,S_m)$ and integer $k$, put $D=2k$. The clique $Q$ contains the $D$ labelled copies $v_{j,t}$ of each set index and the distinct vertices $x_i,y_i$ for $i\in[k]$. Each element vertex $a\in U$ is adjacent exactly to those $v_{j,t}$ for which $a\in S_j$; element vertices have no other incident edges. A disjoint clique $R$ has $D^2+1$ vertices $a_1,\ldots,a_{D^2+1}$, and the only edges from $R$ to the rest are $a_ix_i$, $i\in[k]$.
--
--   All labels are distinct, and the constructed graph has
--   $$n=|U|+Dm+2k+D^2+1.$$
--   The relation constructor records each unordered edge once. No degree, tree-packing, cover-extraction or ratio conclusion is built into this object. The same graph is shared by Claims 7.1–7.3.
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Section 7.2, Theorem 7 construction before Claim 7.1, p. 29 (PDF p. 30)

import Mathlib
import Definitions.Def_LowDiameterNashWilliams_Main_Supplement_SetCover

set_option autoImplicit false
open scoped ENNReal NNReal
open Classical

namespace LowDiameterNashWilliams.Main.Supplement

/-- U first, then the D copies per set and the k designated pairs in Q, then R. -/
def coverQEnd (I : SCInstance) (k : ℕ) : ℕ :=
  I.n + (2*k) * I.sets.length + 2*k

def coverGraphOrder (I : SCInstance) (k : ℕ) : ℕ := coverQEnd I k + (2*k)^2 + 1

def coverGraphRel (I : SCInstance) (k u v : ℕ) : Prop :=
  (I.n ≤ u ∧ u < coverQEnd I k ∧ I.n ≤ v ∧ v < coverQEnd I k) ∨
  (coverQEnd I k ≤ u ∧ u < coverGraphOrder I k ∧
    coverQEnd I k ≤ v ∧ v < coverGraphOrder I k) ∨
  (∃ a : Fin I.n, ∃ j : Fin I.sets.length, a ∈ I.sets.get j ∧ u = a.val ∧
    I.n + (2*k) * j.val ≤ v ∧ v < I.n + (2*k) * (j.val+1)) ∨
  (∃ i : Fin k, u = coverQEnd I k + i.val ∧
    v = I.n + (2*k) * I.sets.length + 2*i.val)

/-- The precise graph of Section 7.2, D=2k, with no packing or degree facts stored in its data. -/
noncomputable def coverGraph (I : SCInstance) (k : ℕ) : GraphInput :=
  graphFromRel (coverGraphOrder I k) (coverGraphRel I k)

end LowDiameterNashWilliams.Main.Supplement


