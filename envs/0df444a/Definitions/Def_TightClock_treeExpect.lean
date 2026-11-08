-- Prove2me | Definitions.Def_TightClock_treeExpect
-- name    : TightClock_treeExpect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:13:02.128714+00:00
-- url     : https://prove2.me/theorems/96f23fbf-3d8a-4d7f-868c-0b6ba5456b36
-- title:
--   Expectation over the random tree
-- statement:
--   The expectation of a function $g$ of the realized tree, $\mathbb E_{\rm tree}[g(T)]=\sum_T\Pr[T]\,g(T)$.
--
--   **Formalization Note** The law is a finite sum, consistently with the prior. A probability is the expectation of an indicator.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), Instance 11, §6.2, p.35 (PDF p.38)

import Mathlib
import Definitions.Def_TightClock_treeWeight

set_option autoImplicit false

namespace TightClock

/-- The expectation over the random tree. Afshinmehr et al., manuscript (STOC 2027 submission), Instance 11,
§6.2, p.35 (PDF 38).

**Formalization Note** The tree law is a finite sum, consistently with `priorExpect`. A probability is the
expectation of an indicator. The law sums to one, as the verification file proves. -/
noncomputable def treeExpect (q L : ℕ) (g : Tree q L → ℝ) : ℝ :=
  ∑ T : Tree q L, treeWeight q L T * g T

end TightClock


