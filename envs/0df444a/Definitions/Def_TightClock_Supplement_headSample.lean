-- Prove2me | Definitions.Def_TightClock_Supplement_headSample
-- name    : TightClock_Supplement_headSample
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:18:44.111677+00:00
-- url     : https://prove2.me/theorems/463b4a6a-b7f1-4d1f-8ba7-6f75ec6fbc69
-- title:
--   Auction 8 — $\mathrm{HeadSample}$
-- statement:
--   **Auction 8 (HeadSample)** with $m=\lceil\log(8d)\rceil$. Each bidder is sampled independently with probability $1/2$ and revealed (sample $T$). Let
--
--   $$g=\max\{v(S):S\in\mathcal F(m),\ S\subseteq T\}.$$
--
--   If $g=0$, run $\mathrm{RetainOnly}(\emptyset)$; otherwise run $\mathrm{Window}(g/(4m),g;\mathcal F(m),N\setminus T)$.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §5.1.3, Auction 8, p.27 (PDF p.30)

import Mathlib
import Definitions.Def_TightClock_Supplement_windowProg
import Definitions.Def_TightClock_Supplement_revealSet
import Definitions.Def_TightClock_Supplement_sizeRestricted
import Definitions.Def_TightClock_Supplement_headSize

set_option autoImplicit false

namespace TightClock.Supplement

/-- Auction 8, `HeadSample`, for a downward-closed `F`, with `m = ⌈log(8d)⌉`. Each bidder is sampled
independently with probability `1/2` (iff `uᵢ < 1/2`) and `Reveal`ed (`T`). Let
`g = max{v(S) : S ∈ F(m), S ⊆ T}`. If `g = 0`, `RetainOnly(∅)`; otherwise
`Window(g/(4m), g; F(m), N ∖ T)`. Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §5.1.3, Auction 8, p.27 (PDF 30).

**Formalization Note** `∅ ∈ F(m)` for a downward-closed `F`, so the maximum defining `g` is over a
nonempty family; the `else 0` branch is never used. -/
noncomputable def headSample {n : ℕ} (δ : ℝ) (F : Finset (Finset (Fin n))) (sel : Selector n)
    (u c d : Fin n → unitInterval) : ClockProg n (Finset (Fin n)) := do
  let m := headSize F
  let T : Finset (Fin n) := Finset.univ.filter (fun i => (u i : ℝ) < 1 / 2)
  let (st, val) ← revealSet δ ⟨fun _ => 0, Finset.univ⟩ T
  let heads := (sizeRestricted F m).filter (fun S => S ⊆ T)
  let g : ℝ := if h : heads.Nonempty then heads.sup' h (fun S => ∑ i ∈ S, val i) else 0
  if g = 0 then retainOnly δ st ∅
  else windowProg δ (g / (4 * (m : ℝ))) g (sizeRestricted F m) (Finset.univ \ T) sel c d st

end TightClock.Supplement


