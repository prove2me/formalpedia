-- Prove2me | Definitions.Def_NestedLogitAssort_DeltaGrid_Window
-- name    : NestedLogitAssort_DeltaGrid_Window
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:05:30.780094+00:00
-- url     : https://prove2.me/theorems/1452264e-8683-4a20-8cc8-fb0903ec2739
-- title:
--   Weight window $[\delta^{l-1},\delta^l]$ of level $l$
-- statement:
--   Fix $\delta>1$, a nest $i$ and an integer level $l$. An assortment $S\subseteq N$ lies in the window of level $l$ when
--
--   $$
--   \delta^{l-1}\le v_{i0}+\sum_{j\in S}v_{ij}\le\delta^{l}.
--   $$
--
--   This is the constraint of the knapsack problem (15) with lower and upper bounds that defines $\hat G_{il}$.
--
--   **Formalization Note** $\delta^l$ and $\delta^{l-1}$ are integer powers (`zpow`), since $l$ may be negative.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, Section 6.2, eq. (15), p. 28

import Mathlib
import Definitions.Def_NestedLogitAssort_DeltaGrid_V

namespace NestedLogitAssort.DeltaGrid

/-- **The weight window `[δ^{l−1}, δ^l]` of level `l`: the constraint of problem (15).**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, Section 6.2, eq. (15), p. 28:
an assortment `S_i` lies in the window of level `l ∈ ℤ` when
`δ^{l−1} ≤ v_{i0} + ∑_{j ∈ S_i} v_{ij} ≤ δ^l`.

**Formalization Note.** `l` is an integer and `δ ^ l`, `δ ^ (l - 1)` are integer powers
(`zpow`). -/
def Window {M : Type*} {n : ℕ} (I : Instance M n) (δ : ℝ) (i : M) (l : ℤ)
    (S : Finset (Fin n)) : Prop :=
  δ ^ (l - 1) ≤ V I i S ∧ V I i S ≤ δ ^ l

end NestedLogitAssort.DeltaGrid


