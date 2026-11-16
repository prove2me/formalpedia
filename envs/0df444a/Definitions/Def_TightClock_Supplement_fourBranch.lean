-- Prove2me | Definitions.Def_TightClock_Supplement_fourBranch
-- name    : TightClock_Supplement_fourBranch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:23:07.512956+00:00
-- url     : https://prove2.me/theorems/b3dd8743-a4f6-49f9-8e74-106380e0dcae
-- title:
--   Auction 10 — $\mathrm{FourBranch}$
-- statement:
--   **Auction 10 (FourBranch)** for a downward-closed family $\mathcal F$: draw a branch index $\kappa$ uniformly from $\{1,2,3,4\}$ and run Singleton, HeadSample, HalfSample or RoutedDisjoint for $\kappa=1,2,3,4$ respectively.
--
--   **Formalization Note** $\kappa$ is read off one uniform $u$ ($\kappa=1$ iff $u<1/4$, and so on), which is uniform on $\{1,2,3,4\}$, like the page's two fair coins.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §5.2, Auction 10, p.31 (PDF p.34)

import Mathlib
import Definitions.Def_TightClock_Supplement_singletonProg
import Definitions.Def_TightClock_Supplement_headSample
import Definitions.Def_TightClock_Supplement_halfSample
import Definitions.Def_TightClock_Supplement_routedDisjoint
import Definitions.Def_TightClock_Supplement_FourBranchSeed

set_option autoImplicit false

namespace TightClock.Supplement

/-- Auction 10, `FourBranch`, for a downward-closed `F`: draw a branch index `κ` uniformly from
`{1, 2, 3, 4}` and run `Singleton`, `HeadSample`, `HalfSample` or `RoutedDisjoint` for
`κ = 1, 2, 3, 4`. Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §5.2, Auction 10, p.31 (PDF 34).

**Formalization Note** `κ` is read off one uniform `ω.1` (`κ = 1` iff `ω.1 < 1/4`, and so on), which
is uniform on `{1,2,3,4}`, like the page's two fair coins. -/
noncomputable def fourBranch {n : ℕ} (δ : ℝ) (F : Finset (Finset (Fin n))) (sel : Selector n)
    (ω : FourBranchSeed n) : ClockProg n (Finset (Fin n)) :=
  if (ω.1 : ℝ) < 1 / 4 then singletonProg δ
  else if (ω.1 : ℝ) < 1 / 2 then headSample δ F sel ω.2.1 ω.2.2.1 ω.2.2.2.1
  else if (ω.1 : ℝ) < 3 / 4 then halfSample δ F sel ω.2.2.2.2.1
  else routedDisjoint δ F sel ω.2.2.2.2.2.1 ω.2.2.2.2.2.2

end TightClock.Supplement


