-- Prove2me | Definitions.Def_TightClock_Supplement_halfSample
-- name    : TightClock_Supplement_halfSample
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:16:22.48021+00:00
-- url     : https://prove2.me/theorems/9e7b8cbf-e390-4de0-825f-79dd0a1dacdb
-- title:
--   Auction 6 — $\mathrm{HalfSample}$
-- statement:
--   **Auction 6 (HalfSample).** Each bidder is sampled independently with probability $1/2$ and revealed (sample $T$). Select $j\in\arg\max_{j\in[k]}\sum_{i\in G_j\cap T}v_i$ over the maximal sets $G_1,\dots,G_k$ of $\mathcal F$ (by the selection rule) and run $\mathrm{RetainOnly}(G_j\setminus T)$: these bidders are served at price $0$.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §5.1.2, Auction 6, p.23 (PDF p.26)

import Mathlib
import Definitions.Def_TightClock_Supplement_revealSet
import Definitions.Def_TightClock_Supplement_retainOnly
import Definitions.Def_TightClock_Supplement_Selector
import Definitions.Def_BayesClock_maximalSets

set_option autoImplicit false

namespace TightClock.Supplement

/-- Auction 6, `HalfSample`, for a downward-closed `F`. Each bidder is sampled independently with
probability `1/2` (iff `uᵢ < 1/2`) and `Reveal`ed (`T`). Select `j ∈ arg max_j ∑_{i∈G_j∩T} vᵢ` over
the maximal sets `G_j` of `F` (chosen by the selection rule `sel`), and run `RetainOnly(G_j ∖ T)`: those bidders
are served at price `0`. Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §5.1.2, Auction 6, p.23 (PDF 26). -/
noncomputable def halfSample {n : ℕ} (δ : ℝ) (F : Finset (Finset (Fin n))) (sel : Selector n)
    (u : Fin n → unitInterval) : ClockProg n (Finset (Fin n)) := do
  let T : Finset (Fin n) := Finset.univ.filter (fun i => (u i : ℝ) < 1 / 2)
  let (st, val) ← revealSet δ ⟨fun _ => 0, Finset.univ⟩ T
  let G := sel.pick (BayesClock.maximalSets F) (fun G => ∑ i ∈ G ∩ T, val i)
  retainOnly δ st (G \ T)

end TightClock.Supplement


