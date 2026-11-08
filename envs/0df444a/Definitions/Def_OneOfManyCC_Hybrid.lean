-- Prove2me | Definitions.Def_OneOfManyCC_Hybrid
-- name    : OneOfManyCC_Hybrid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:57.312097+00:00
-- url     : https://prove2.me/theorems/b293dc77-3b1a-47ff-9e25-fcb026470a53
-- title:
--   The hybrid leaf sets $L_j$ and their forcing probabilities $p_j$
-- statement:
--   Let $P$ be a protocol for $\mathrm{OneOut}^{\neq}_k(R)$, with leaf outputs $(i_w,o_w)$ and projections $S_w,T_w$. For tuples $X=(x_1,\dots,x_k)\in A^k$, $Y=(y_1,\dots,y_k)\in B^k$, not necessarily with distinct entries, and $0\le j\le k$, let
--
--   $$L_j=\{w : i_w\le j,\ x_{i_w}\in S_w\}\cup\{w : i_w>j,\ y_{i_w}\notin T_w\}.$$
--
--   Leaves at positions up to $j$ are judged by Alice's tuple and the other leaves by Bob's tuple. For distributions $\mu$ on $A$ and $\nu$ on $B$, let $p_j$ be the probability, for $X\sim\mu^k$ and $Y\sim\nu^k$ independently, that Alice can force $L_j$. The differences $p_j-p_{j-1}$ are the hybrid steps of the proof of Lemma 5.2.
--
--   **Formalization Note** Positions are 0-based: $i_w\le j$ is `i.val < j` and $i_w>j$ is `j ≤ i.val`. The probability is the sum of the product weights over pairs of tuples.
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), §5, proof of Lemma 5.2, pp.10–11

import Mathlib
import Definitions.Def_OneOfManyCC_LeafSets
import Definitions.Def_OneOfManyCC_Forcing
import Definitions.Def_OneOfManyCC_mass

namespace OneOfManyCC

namespace Protocol

variable {A B O : Type} {k : ℕ}

/-- **The hybrid leaf set** `L_j`.
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), §5, proof of Lemma 5.2, pp.10–11:
"L_j = {w : i_w ≤ j, x_{i_w} ∈ S_w} ∪ {w : i_w > j, y_{i_w} ∉ T_w}, in which leaves at positions up
to j are judged by Alice's tuple and the other leaves by Bob's tuple."

**Formalization Note.** The tuples `X`, `Y` are arbitrary, not necessarily injective. Positions are
`0`-based: the paper's `i_w` is `i.val + 1`, so `i_w ≤ j` is `i.val < j` and `i_w > j` is `j ≤ i.val`. -/
def hybridLeaves (P : Protocol (Fin k ↪ A) (Fin k ↪ B) (Fin k × O)) (j : ℕ)
    (X : Fin k → A) (Y : Fin k → B) : Set (List Bool) :=
  {w | ∃ i, P.HasIndex w i ∧ ((i.val < j ∧ X i ∈ P.projS w) ∨ (j ≤ i.val ∧ Y i ∉ P.projT w))}

/-- **The probability** `p_j` (§5, proof of Lemma 5.2, p.10): "draw X = (x1, . . . , xk) ∼ µᵏ and
Y = (y1, . . . , yk) ∼ νᵏ independently … let p_j be the probability that Alice can force the set
L_j". -/
noncomputable def hybridProb [Fintype A] [Fintype B]
    (P : Protocol (Fin k ↪ A) (Fin k ↪ B) (Fin k × O)) (μ : A → ℝ) (ν : B → ℝ) (j : ℕ) : ℝ :=
  mass (fun XY : (Fin k → A) × (Fin k → B) => (∏ l, μ (XY.1 l)) * ∏ l, ν (XY.2 l))
    {XY | P.AliceForces (P.hybridLeaves j XY.1 XY.2)}

end Protocol

end OneOfManyCC


