-- Prove2me | Definitions.Def_TightClock_Supplement_learnedPrices
-- name    : TightClock_Supplement_learnedPrices
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:11:31.90581+00:00
-- url     : https://prove2.me/theorems/7bd9278e-14f3-4cab-87bc-4a000714f17b
-- title:
--   Auction 2 — $\mathrm{LearnedPricesAuction}$
-- statement:
--   **Auction 2 (LearnedPricesAuction)** on disjoint groups. Each bidder is sampled independently with probability $\sigma=1/4$ and revealed ($v_i\leftarrow\mathrm{Reveal}(i)$, sample $T$). For each group $G_j$ with $W_j=\sum_{i\in T\cap G_j}q(v_i)$:
--
--   * if $W_j=0$, the unsampled bidders of $G_j$ stay active at price $0$;
--   * otherwise each unsampled bidder $i\in G_j$ is independently offered $2^r$ with probability $p_{j,r}$; she stays active at price $2^r$ if she accepts and exits if she rejects.
--
--   Then Auction 3 runs on the active bidders, starting from their current prices.
--
--   **Formalization Note** The sample is $T=\{i:s_i<1/4\}$ and the level of bidder $i$ is drawn from her own uniform $\ell_i$, all independent. The group of an unsampled bidder enters through the sampled bidders sharing a group with her.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §4.2, Auction 2, p.18 (PDF p.21), with (4.2)–(4.5), p.17 (PDF p.20)

import Mathlib
import Definitions.Def_TightClock_Supplement_initializedWFCA
import Definitions.Def_TightClock_Supplement_revealSet
import Definitions.Def_TightClock_Supplement_levelDraw

set_option autoImplicit false

namespace TightClock.Supplement

/-- Auction 2, `LearnedPricesAuction`, on disjoint groups `Gs`. Each bidder is sampled independently
with probability `σ = 1/4` (iff `sᵢ < 1/4`) and `Reveal`ed. For each group `G_j` let
`W_j = ∑_{i∈T∩G_j} q(vᵢ)` (4.3). If `W_j = 0` the unsampled bidders of `G_j` stay active at price `0`;
otherwise each unsampled `i ∈ G_j` is independently offered `2^r` with probability `p_{j,r}` (4.5)
(drawn from the uniform `ℓᵢ` by `levelDraw`), stays active at price `2^r` if she accepts and exits if
she rejects. Then Auction 3 runs on the active bidders with these prices. Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §4.2, Auction 2,
p.18 (PDF 21), with (4.2)–(4.5), p.17 (PDF 20).

**Formalization Note** The group of an unsampled bidder `i` is entered through the sampled bidders
sharing a group with `i` (`T ∩ G_j` for the group `G_j ∋ i` of a partition). The offers go in the
order of `Fin n`. -/
noncomputable def learnedPrices {n : ℕ} (δ : ℝ) (Gs : Finset (Finset (Fin n))) (sel : Selector n)
    (s ℓ : Fin n → unitInterval) : ClockProg n (Finset (Fin n)) := do
  let T : Finset (Fin n) := Finset.univ.filter (fun i => (s i : ℝ) < 1 / 4)
  let (st, val) ← revealSet δ ⟨fun _ => 0, Finset.univ⟩ T
  let peers : Fin n → Finset (Fin n) := fun i => T.filter (fun i' => ∃ G ∈ Gs, i ∈ G ∧ i' ∈ G)
  let st ← (List.finRange n).foldlM (fun (st : CState n) i => do
    if i ∉ T ∧ 0 < ∑ i' ∈ peers i, dyadicRound (val i') then
      let (_, st') ← offerTo st i ((2 : ℝ) ^ (levelDraw (peers i) val (ℓ i)))
      return st'
    else return st) st
  initializedWFCA δ Gs sel st

end TightClock.Supplement


