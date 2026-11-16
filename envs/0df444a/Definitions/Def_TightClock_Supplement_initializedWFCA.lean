-- Prove2me | Definitions.Def_TightClock_Supplement_initializedWFCA
-- name    : TightClock_Supplement_initializedWFCA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:10:29.105741+00:00
-- url     : https://prove2.me/theorems/0ce929a4-bb94-40ba-a13b-91dada76c3ed
-- title:
--   Auction 3 — $\mathrm{InitializedWFCA}$
-- statement:
--   **Auction 3 (InitializedWFCA)**, started from an active set $A$ with current prices $(p_i)_{i\in A}$, on disjoint groups $G_1,\dots,G_k$. While $A$ is infeasible (not contained in one group):
--
--   1. protect a group $j'\in\arg\max_j\sum_{i\in A\cap G_j}p_i$ (ties by the selection rule);
--   2. let $\ell=\min_{i\in A\setminus G_{j'}}p_i$;
--   3. offer every $i\in A\setminus G_{j'}$ with $p_i=\ell$ the price $\delta\lfloor p_i/\delta\rfloor+\delta$; those who reject leave $A$.
--
--   Finally serve all bidders in $A$.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §4.2, Auction 3, p.18 (PDF p.21)

import Mathlib
import Definitions.Def_TightClock_Supplement_retainOnly
import Definitions.Def_TightClock_Supplement_Selector
import Definitions.Def_TightClock_Supplement_groupFamily

set_option autoImplicit false

namespace TightClock.Supplement

/-- Auction 3, `InitializedWFCA`, on disjoint groups `Gs`, started from the public state `st0`
(active set `A` and prices `pᵢ`). While `A` is infeasible (not inside one group), protect
`j′ ∈ arg max_j ∑_{i∈A∩G_j} pᵢ` (chosen by the selection rule `sel`), let `ℓ = min_{i∈A∖G_{j′}} pᵢ`, and offer
each `i ∈ A ∖ G_{j′}` with `pᵢ = ℓ` the price `δ⌊pᵢ/δ⌋ + δ`; those who reject leave `A`. Finally serve
all of `A`. Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §4.2, Auction 3, p.18 (PDF 21).

**Formalization Note** The offers of one iteration go in the order of `Fin n`. The `else 0` branch
of `ℓ` is never used: an infeasible `A` is not inside the protected group. -/
noncomputable def initializedWFCA {n : ℕ} (δ : ℝ) (Gs : Finset (Finset (Fin n))) (sel : Selector n)
    (st0 : CState n) : ClockProg n (Finset (Fin n)) :=
  ClockProg.loop (fun st : CState n => do
    if st.active ∈ groupFamily Gs then return Sum.inr st.active
    else
      let j := sel.pick Gs (fun G => ∑ i ∈ st.active ∩ G, st.price i)
      let out := st.active \ j
      let ℓ : ℝ := if h : out.Nonempty then out.inf' h st.price else 0
      let st' ← ((List.finRange n).filter (fun i => decide (i ∈ out ∧ st.price i = ℓ))).foldlM
        (fun (st : CState n) i => do
          let (_, st') ← offerTo st i (nextGrid δ (st.price i))
          return st') st
      return Sum.inl st') st0

end TightClock.Supplement


