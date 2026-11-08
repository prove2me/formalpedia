-- Prove2me | Definitions.Def_TightClock_CB
-- name    : TightClock_CB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:16:58.677495+00:00
-- url     : https://prove2.me/theorems/77eed572-cf27-4af9-9c6e-7eb185120725
-- title:
--   Optimal clock welfare $\mathrm{CB}(\mathcal F,D)$
-- statement:
--   The **optimal Bayesian welfare achievable by a clock auction** is
--
--   $$\mathrm{CB}(\mathcal F,D)=\sup_\pi\ \mathbb E_{X\sim D,\omega}[\mathrm{SW}_\pi(X;\omega)],$$
--
--   where the supremum ranges over all adaptive randomized clocks. By §6.1, those clocks know $\mathcal F$ and $D$, have unlimited computation, may continue to make offers after their active set has become feasible, and may serve any feasible subset of their active bidders.
--
--   **Formalization Note** For a downward-closed family, the set of values is nonempty (it contains the value of `stop ∅`) and bounded above by $\mathrm{FB}(\mathcal F,D)$, so the real supremum is genuine.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.14 (PDF p.17); §6.1, p.34 (PDF p.37)

import Mathlib
import Definitions.Def_TightClock_clockValue

set_option autoImplicit false

namespace TightClock

/-- The optimal Bayesian welfare `CB(F, D) = sup_π E_{X∼D, ω}[SW_π(X; ω)]`, where "The supremum ranges over
all adaptive randomized clocks satisfying the rules above." Afshinmehr et al., manuscript (STOC 2027
submission), §3, p.14 (PDF 17); §6.1, p.34 (PDF 37).

**Formalization Note** The real supremum would be junk on an empty or unbounded set. For downward-closed `F`
the set contains the value of `stop ∅` and is bounded above by `FB F D`. This is proved in the mission's
verification file. -/
noncomputable def CB {n : ℕ} (F : Finset (Finset (Fin n))) (D : FinitePrior) : ℝ :=
  sSup {x : ℝ | ∃ π : RandomizedClock F, x = clockValue π D}

end TightClock


