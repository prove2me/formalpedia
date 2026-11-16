-- Prove2me | Definitions.Def_TightClock_Supplement_singletonProg
-- name    : TightClock_Supplement_singletonProg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:15:28.227025+00:00
-- url     : https://prove2.me/theorems/5b867770-dea6-48fa-88b9-083a63a733ab
-- title:
--   Auction 5 — $\mathrm{Singleton}$
-- statement:
--   **Auction 5 (Singleton).** Start with $A=N$. While $|A|>1$, sweep the bidders in a fixed order: stop the sweep as soon as $|A|=1$; otherwise, if $i\in A$, raise $p_i$ by $\delta$ and remove $i$ if she rejects. Then run $\mathrm{RetainOnly}(A)$. Its welfare is exactly $\max_i v_i$.
--
--   **Formalization Note** The fixed order is the order of the bidder indices; any fixed order becomes this one after relabeling the bidders.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §5.1.1, Auction 5, p.22 (PDF p.25)

import Mathlib
import Definitions.Def_TightClock_Supplement_retainOnly

set_option autoImplicit false

namespace TightClock.Supplement

/-- Auction 5, `Singleton`. `A = N`. While `|A| > 1`: for each bidder `i` in the fixed order, stop
the sweep once `|A| = 1`; otherwise, if `i ∈ A`, raise `pᵢ` by `δ` and remove `i` if she rejects.
Then `RetainOnly(A)`. Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §5.1.1, Auction 5, p.22 (PDF 25).

**Formalization Note** The fixed order is the order of `Fin n` (any fixed order is this one after
relabeling the bidders). "go to line 8" is realized by skipping the rest of the sweep: the `while`
test then fails at once. -/
noncomputable def singletonProg {n : ℕ} (δ : ℝ) : ClockProg n (Finset (Fin n)) := do
  let st ← ClockProg.loop (fun st : CState n => do
    if st.active.card ≤ 1 then return Sum.inr st
    else
      let st' ← (List.finRange n).foldlM (fun (st : CState n) i => do
        if st.active.card = 1 then return st
        else if i ∈ st.active then
          let (_, st') ← offerTo st i (st.price i + δ)
          return st'
        else return st) st
      return Sum.inl st') ⟨fun _ => 0, Finset.univ⟩
  retainOnly δ st st.active

end TightClock.Supplement


