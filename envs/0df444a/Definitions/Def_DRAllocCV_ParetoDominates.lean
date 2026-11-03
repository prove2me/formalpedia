-- Prove2me | Definitions.Def_DRAllocCV_ParetoDominates
-- name    : DRAllocCV_ParetoDominates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:15:00.550985+00:00
-- url     : https://prove2.me/theorems/2cd7cf87-7cd1-4b68-b437-3644d892e79a
-- title:
--   Pareto robust dominance (Definition 2)
-- statement:
--   A feasible mechanism $(p',q')$ **Pareto robustly dominates** a feasible mechanism $(p,q)$ if inequality (1) holds for every $\mathbb P\in\mathcal P$ and is strict for at least one $\mathbb P\in\mathcal P$: $(p',q')$ is never worse in expectation and sometimes strictly better.
-- source:
--   Bayrak, Koçyiğit, Kuhn, Pınar, Distributionally Robust Optimal Allocation with Costly Verification, arXiv:2211.15122v3, §2, p.7, Definition 2

import Mathlib
import Definitions.Def_DRAllocCV_WeaklyParetoDominates

open MeasureTheory

namespace DRAllocCV

/-- **Pareto robust dominance** (Definition 2, Bayrak, Koçyiğit, Kuhn, Pınar, *Distributionally Robust Optimal Allocation with Costly Verification*, arXiv:2211.15122v3, §2, p.7): `(p′, q′)` Pareto robustly
dominates `(p, q)` if inequality (1) holds for all `ℙ ∈ 𝒫` and is strict for at least one
`ℙ ∈ 𝒫`. The dominating mechanism `(p′, q′)` comes first in the argument list. -/
def ParetoDominates {ι : Type*} [Fintype ι] [DecidableEq ι] (tlo thi : ι → ℝ)
    (Pset : Set (Measure (ι → ℝ))) (c : ι → ℝ) (p' q' p q : ι → (ι → ℝ) → ℝ) : Prop :=
  WeaklyParetoDominates tlo thi Pset c p' q' p q ∧
  ∃ P ∈ Pset, expectedPayoff P c p q < expectedPayoff P c p' q'

end DRAllocCV


