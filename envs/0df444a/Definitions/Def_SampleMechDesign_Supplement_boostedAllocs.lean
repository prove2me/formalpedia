-- Prove2me | Definitions.Def_SampleMechDesign_Supplement_boostedAllocs
-- name    : SampleMechDesign_Supplement_boostedAllocs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:47:04.234986+00:00
-- url     : https://prove2.me/theorems/e673037b-9dcb-4719-bb16-daa68b332969
-- title:
--   Appendix D — $\mathcal Q_M$, the boosted allocations of an AMA
-- statement:
--   For an AMA $M$ with boosts $\lambda$, $\mathcal Q_M$ is the set of all allocations $Q$ such that $\lambda(Q)>0$. Theorem D.2 measures the complexity of an AMA by $|\mathcal Q_M|$ and spreads the confidence over the possible sets $\mathcal Q_M$ with a weight function.
-- source:
--   Balcan, Sandholm, Vitercik, Generalization Guarantees for Multi-item Profit Maximization: Pricing, Auctions, and Randomized Mechanisms, arXiv:1705.00243v6, Appendix D, p.46 (PDF p.46)

import Mathlib
import Definitions.Def_SampleMechDesign_Supplement_Alloc

namespace SampleMechDesign.Supplement

open Finset

/-- **`Q_M`, the boosted allocations of an AMA.** Balcan, Sandholm, Vitercik,
arXiv:1705.00243v6, Appendix D, p.46: "For an AMA M, let Q_M be the set of all allocations Q such
that λ(Q) > 0."

`boostedAllocs λ` is the finite set of allocations with a positive boost. -/
noncomputable def boostedAllocs {n m : ℕ} (lam : Alloc n m → ℝ) : Finset (Alloc n m) :=
  univ.filter fun Q => 0 < lam Q

end SampleMechDesign.Supplement


