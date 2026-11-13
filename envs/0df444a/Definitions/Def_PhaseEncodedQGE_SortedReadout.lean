-- Prove2me | Definitions.Def_PhaseEncodedQGE_SortedReadout
-- name    : PhaseEncodedQGE_SortedReadout
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:50:16.658206+00:00
-- url     : https://prove2.me/theorems/e5c7e09d-51f7-4e64-ba11-e8205aa33e4b
-- title:
--   Sorted readout $p^\downarrow_G$, the counts $K_m(n)$ and the $m$-defect block of ranks
-- statement:
--   Sorting the $2^n$ Born probabilities $p_G(x;\beta)$, $x\in\{0,1\}^n$, in descending order gives the **sorted readout** $p^\downarrow_G$, a list of $2^n$ reals that does not depend on the labelling of the vertices. Let
--   $$K_m(n)=\sum_{i\le m}\binom{n}{i}.$$
--   The ranks $K_{m-1}(n)+1,\dots,K_m(n)$ of the sorted readout form the **$m$-defect block**; it has $\binom nm$ entries (for $m=0$ it is rank $1$).
--
--   The block is defined by rank alone: when $t=\tan(\eta/2)>1$ and $\beta$ is small it is occupied by the outcomes with exactly $m$ defects, which is a theorem of the mission, not part of this definition.
--
--   **Formalization Note** The sorted readout is the descending sort of the multiset of the $2^n$ values. Ranks are 1-based in the paper and 0-based list positions here, so the $m$-defect block is the $\binom nm$ entries after the first $\sum_{i<m}\binom ni$.
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), §1, p.1 (PDF p.2); §2, p.5 (PDF p.6), 'Defect layers and blocks'

import Mathlib
import Definitions.Def_PhaseEncodedQGE_Circuit
set_option autoImplicit false

namespace PhaseEncodedQGE

/-- The sorted readout `p↓_G`: the `2ⁿ` Born probabilities `p_G(x; β)`, `x ∈ {0,1}ⁿ`, sorted in
descending order (Miller, Lee, STOC 2027 submission (build 2026-11-03), §1, p.1; §2, p.4).

**Formalization Note** It is the descending sort (`Multiset.sort (· ≥ ·)`) of the multiset of the
`2ⁿ` values, so it is a list of reals that does not depend on how outcomes are enumerated. Ranks are
1-based in the paper and 0-based list indices here: rank `k` is index `k − 1`. -/
noncomputable def sortedReadout {n : ℕ} (prep : Outcome n → ℂ) (P : Axis) (r : ℕ)
    (G : SimpleGraph (Fin n)) (γ β : ℝ) : List ℝ :=
  ((Finset.univ : Finset (Outcome n)).val.map (born prep P r G γ β)).sort (· ≥ ·)

/-- `K_m(n) = ∑_{i ≤ m} (n choose i)`, the number of outcomes with at most `m` defects (§2, p.5). -/
def Kcount (n m : ℕ) : ℕ := ∑ i ∈ Finset.range (m + 1), n.choose i

/-- The entries of the sorted readout at the ranks `K_{m−1}(n) + 1, …, K_m(n)` of the `m`-defect
block (§2, p.5). With 0-based indices these are the `(n choose m)` entries that follow the first
`∑_{i < m} (n choose i) = K_{m−1}(n)` ones; for `m = 0` the block is rank `1`.

**Formalization Note** The block is cut from the sorted readout by rank alone; which outcomes
occupy it is not part of the definition. -/
noncomputable def block {n : ℕ} (prep : Outcome n → ℂ) (P : Axis) (r : ℕ)
    (G : SimpleGraph (Fin n)) (γ β : ℝ) (m : ℕ) : List ℝ :=
  ((sortedReadout prep P r G γ β).drop (∑ i ∈ Finset.range m, n.choose i)).take (n.choose m)

end PhaseEncodedQGE


