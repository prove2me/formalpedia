-- Prove2me | Definitions.Def_TightClock_condExpect
-- name    : TightClock_condExpect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:13:28.425368+00:00
-- url     : https://prove2.me/theorems/317cc3fe-643b-4d58-a94a-2932d703e5e4
-- title:
--   Conditional expectation given a history
-- statement:
--   For a function $g$ of the value profile and a history $h$ of positive probability,
--
--   $$\mathbb E[g(X)\mid H^t=h]=\frac{\mathbb E_{X\sim D}\big[g(X)\mathbb 1[H^t=h]\big]}{\Pr[H^t=h]}.$$
--
--   The tree and the seed are fixed: as in the proof of Proposition 6.11, "Conditional on $H^t$" is over the values only.
--
--   **Formalization Note** Every statement using this expression assumes that $h$ has positive probability, which excludes division by $0$.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.2, p.36 (PDF p.39)

import Mathlib
import Definitions.Def_TightClock_histProb

set_option autoImplicit false

namespace TightClock

open Classical in
/-- The conditional expectation `E[g(X) | Hᵗ = h]` under the i.i.d. prior `D`, for a single-step clock with its tree
and seed fixed. Afshinmehr et al., manuscript (STOC 2027 submission), §6.2, p.36 (PDF 39).

**Formalization Note** Every statement using it assumes `0 < histProb q L D σ h`, which excludes the junk division
by zero. -/
noncomputable def condExpect (q L : ℕ) (D : FinitePrior) (σ : SingleStepStrategy (bidderCount q L))
    (h : SingleStepHistory (bidderCount q L)) (g : (Fin (bidderCount q L) → ℝ) → ℝ) : ℝ :=
  priorExpect D (fun v => if ssHist q L σ v h.length = h then g v else 0) / histProb q L D σ h

end TightClock


