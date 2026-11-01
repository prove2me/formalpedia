-- Prove2me | Definitions.Def_SponsoredAssort_threshold
-- name    : SponsoredAssort_threshold
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:52.635683+00:00
-- url     : https://prove2.me/theorems/229d5df6-7cae-4b10-8798-cac4d5cfb7ec
-- title:
--   Display threshold $\hat v_i^P(v_{-i})$
-- statement:
--   In the partition mechanism, let $\hat S_i\in P$ be the unique part containing seller $i$. The display threshold of seller $i$ is
--
--   $$
--   \hat v_i^P(v_{-i})=\inf_{y\ge0}\{\,y:\ S^P(y,v_{-i})=\hat S_i\,\},
--   $$
--
--   the least attractiveness at which seller $i$'s part is displayed.
--
--   **Formalization Note** An infimum in $\mathbb R_{\ge0}$, equal to $0$ on the empty set. It is only used when seller $i$ is displayed, in which case the set contains $v_i$.
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), Definition 5.2, (3), p.27

import Mathlib
import Definitions.Def_SponsoredAssort_Attr

open scoped NNReal

namespace SponsoredAssort

/-- The **display threshold** `v̂ᵢ^P(v₋ᵢ) = inf_{y ≥ 0} {y : S^P(y, v₋ᵢ) = Ŝᵢ}` of seller `i` in the
partition mechanism (Balseiro, Désir, SSRN 3821382 (Feb. 21, 2022), Definition 5.2, (3), p.27),
where `Ŝᵢ ∈ P` is the unique part containing `i` (`P.part i`).

**Formalization Note.** An `sInf` in `ℝ≥0`, which is `0` on the empty set. It enters the payment
only when seller `i` is displayed at `v`; then `S^P(v) = Ŝᵢ`, so `vᵢ` belongs to the set and the
set is nonempty. -/
noncomputable def threshold {n : ℕ} (P : Finpartition (Finset.univ : Finset (Fin n)))
    (S : Attr n → Finset (Fin n)) (i : Fin n) (v : Attr n) : ℝ≥0 :=
  sInf {y : ℝ≥0 | S (Function.update v i y) = P.part i}

end SponsoredAssort


