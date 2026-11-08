-- Prove2me | Definitions.Def_TightClock_priorExpect
-- name    : TightClock_priorExpect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:43:00.827439+00:00
-- url     : https://prove2.me/theorems/585ba55c-dd03-4371-898e-d08dba481714
-- title:
--   Expectation over the i.i.d. finite prior
-- statement:
--   Let $X_1,\dots,X_n$ be i.i.d. with finite law $D$. For a function $g$ of the profile,
--
--   $$\mathbb E_{X\sim D}[g(X)]=\sum_{x\in(\operatorname{supp}D)^n}\Big(\prod_{i=1}^n D(x_i)\Big)g(x).$$
--
--   **Formalization Note** The law is finite, so the expectation is this finite sum, and no measurability in the profile arises.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.14 (PDF p.17)

import Mathlib
import Definitions.Def_TightClock_FinitePrior

set_option autoImplicit false

namespace TightClock

/-- The expectation `E_{X∼D}[g(X)]` of a function of the value profile, when the `n` values are i.i.d.
with law `D`. Afshinmehr et al., manuscript (STOC 2027 submission), §3, p.14 (PDF 17).

**Formalization Note** The law is finite, so the expectation is the finite sum over support profiles of
the product of the weights times `g`. No measurability in the profile arises. -/
noncomputable def priorExpect {n : ℕ} (D : FinitePrior) (g : (Fin n → ℝ) → ℝ) : ℝ :=
  ∑ x ∈ Fintype.piFinset (fun _ : Fin n => D.support), (∏ i, D.weight (x i)) * g x

end TightClock


