-- Prove2me | Definitions.Def_SponsoredAssort_partitionMech
-- name    : SponsoredAssort_partitionMech
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:50:51.168788+00:00
-- url     : https://prove2.me/theorems/3a67416c-5578-4885-ac6d-4a22332a5e96
-- title:
--   Partition mechanism $m^P$
-- statement:
--   For a partition $P$ of $[n]$, the **partition mechanism** $m^P$ displays a part of pointwise highest welfare, $S^P(v)\in\arg\max_{\ell}R(S_\ell,v)$. A seller who is not displayed pays nothing; a displayed seller $i$ pays the revenue of the threshold type,
--
--   $$
--   p_i^P(v)=\begin{cases} r_i\,\pi_i\big(\hat S_i,(\hat v_i^P(v_{-i}),v_{-i})\big), & i\in S^P(v),\\ 0, & i\notin S^P(v).\end{cases}
--   $$
--
--   Each seller appears in only one candidate assortment, and a displayed seller's payment does not depend on its own report, as in a second-price auction.
--
--   **Formalization Note** The payment follows the sentence after (3) on p.27 ("A seller who is not displayed pays nothing … Otherwise, the seller pays the revenue of the type with the attractiveness $\hat v_i(v_{-i})$"). The printed case split $\hat v_i^P(v_{-i})\le v_i$ in (3) differs only at a tie where seller $i$ is not displayed although $v_i=\hat v_i^P(v_{-i})$; there (3) would charge a seller who is not displayed and break (IR), e.g. for $r=(2,1)$, the singleton partition and $v=(1/3,1)$.
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), Definition 5.2 and (3), pp.26–27

import Mathlib
import Definitions.Def_SponsoredAssort_Mechanism
import Definitions.Def_SponsoredAssort_choiceProb
import Definitions.Def_SponsoredAssort_threshold

open scoped NNReal

namespace SponsoredAssort

/-- The **partition mechanism** `m^P` (Balseiro, Désir, SSRN 3821382 (Feb. 21, 2022),
Definition 5.2 and (3), pp.26–27): it displays `S^P(v)`, a part of `P` of pointwise highest
welfare (the selector `S`, see `IsBestSelector`), and charges seller `i`
`rᵢ · πᵢ(Ŝᵢ, (v̂ᵢ^P(v₋ᵢ), v₋ᵢ))` if `i ∈ S^P(v)` and `0` otherwise, where `Ŝᵢ` is the part
containing `i` and `v̂ᵢ^P` the display threshold.

**Formalization Note.** The payment follows the sentence after (3) on p.27, "A seller who is not
displayed pays nothing, i.e., `pᵢ^P(v) = 0` if `i ∉ S^P(v)`. Otherwise, the seller pays the revenue
of the type with the attractiveness `v̂ᵢ(v₋ᵢ)`", rather than the case split `v̂ᵢ^P(v₋ᵢ) ≤ vᵢ` of (3):
the two differ only at a tie in which seller `i` is not displayed although `vᵢ = v̂ᵢ^P(v₋ᵢ)`, and
there (3) charges a seller who is not displayed, which violates (IR) (e.g. `r = (2, 1)`, singleton
partition, `v = (1/3, 1)`). The rule is meant to be used with a selector `S` satisfying
`IsBestSelector r P S`. -/
noncomputable def partitionMech {n : ℕ} (r : Fin n → ℝ)
    (P : Finpartition (Finset.univ : Finset (Fin n))) (S : Attr n → Finset (Fin n)) :
    Mechanism n where
  alloc := S
  pay v i :=
    if i ∈ S v then r i * choiceProb (P.part i) (Function.update v i (threshold P S i v)) i
    else 0

end SponsoredAssort


