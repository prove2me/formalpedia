-- Prove2me | Definitions.Def_TightClock_Supplement_revealSet
-- name    : TightClock_Supplement_revealSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:06:46.62418+00:00
-- url     : https://prove2.me/theorems/ad6a6a4f-9333-41da-9d67-8d0d3ebe7c64
-- title:
--   $\mathrm{Reveal}(i)$ for every sampled bidder
-- statement:
--   Apply $\mathrm{Reveal}(i)$ to every bidder $i$ of a sample $T$ and record the learned values ($0$ outside $T$). This is the step "for each sampled $i$: $v_i\leftarrow\mathrm{Reveal}(i)$; $T\leftarrow T\cup\{i\}$" of Auctions 2, 6 and 8.
--
--   **Formalization Note** The reveals are made in the order of the bidder indices; no outcome depends on the order.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), Auction 2, p.18 (PDF p.21); Auction 6, p.23 (PDF p.26); Auction 8, p.27 (PDF p.30)

import Mathlib
import Definitions.Def_TightClock_Supplement_reveal

set_option autoImplicit false

namespace TightClock.Supplement

/-- `Reveal(i)` for every bidder `i ∈ T`, in the order of `Fin n`; returns the new state and the
learned values (`0` outside `T`). Used by Auctions 2, 6 and 8 ("for each i ... vi ← Reveal(i);
T ← T ∪ {i}"). Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), pp.18, 22, 27 (PDF 21, 25, 30).

**Formalization Note** The order of the reveals is the order of `Fin n`; it does not affect any
outcome. -/
noncomputable def revealSet {n : ℕ} (δ : ℝ) (st0 : CState n) (T : Finset (Fin n)) :
    ClockProg n (CState n × (Fin n → ℝ)) :=
  (List.finRange n).foldlM (fun (acc : CState n × (Fin n → ℝ)) i => do
    if i ∈ T then
      let (x, st') ← reveal δ acc.1 i
      return (st', Function.update acc.2 i x)
    else return acc) (st0, fun _ => 0)

end TightClock.Supplement


