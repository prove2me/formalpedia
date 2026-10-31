-- Prove2me | Definitions.Def_TimeScaleAvg_AssumptionA
-- name    : TimeScaleAvg_AssumptionA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:53.045594+00:00
-- url     : https://prove2.me/theorems/e6404f55-34d6-4a4a-8258-f8116e7e5fcf
-- title:
--   Assumption $(\mathcal A)$: convex, $C^1$, minimizer exists, $\nabla f$ Lipschitz on bounded sets
-- statement:
--   Let $\mathcal H$ be a real Hilbert space. A function $f:\mathcal H\to\mathbb R$ satisfies assumption $(\mathcal A)$ when
--
--   1. $f$ is convex;
--   2. $f$ is of class $C^1$;
--   3. $S=\operatorname{argmin}_{\mathcal H}f\ne\emptyset$;
--   4. $\nabla f$ is Lipschitz continuous on the bounded sets of $\mathcal H$: for every bounded $B\subseteq\mathcal H$ there is $L\ge0$ with $\|\nabla f(u)-\nabla f(v)\|\le L\|u-v\|$ for all $u,v\in B$.
--
--   The paper makes this assumption throughout, and every result of this mission rests on it.
--
--   **Formalization Note** The constant $L$ depends on the bounded set; there is no global Lipschitz constant. $\mathcal H$ may be infinite-dimensional.
-- source:
--   Attouch, Boţ & Nguyen, Fast Convex Optimization via Time Scale and Averaging of the Steepest Descent, arXiv:2208.08260v3, Eq. (2), p.1

import Mathlib
import Definitions.Def_TimeScaleAvg_argminSet

open scoped NNReal

namespace TimeScaleAvg

/-- Assumption (A), made "throughout the paper" (Attouch, Boţ & Nguyen, arXiv:2208.08260v3,
Eq. (2), p.1): `f : H → ℝ` is a convex function of class `C¹`, `S = argmin_H f ≠ ∅`, and `∇f` is
Lipschitz continuous on the bounded sets of `H`.

**Formalization Note.** The Lipschitz constant depends on the bounded set, as on the page: there is
no global constant. `H` is any real Hilbert space, possibly infinite-dimensional. -/
structure AssumptionA {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) : Prop where
  /-- `f` is convex. -/
  convex : ConvexOn ℝ Set.univ f
  /-- `f` is of class `C¹`. -/
  contDiff : ContDiff ℝ 1 f
  /-- `S = argmin_H f ≠ ∅`. -/
  argmin_nonempty : (argminSet f).Nonempty
  /-- `∇f` is Lipschitz continuous on each bounded set, with a constant depending on the set. -/
  lipschitzOn_gradient : ∀ B : Set H, Bornology.IsBounded B →
    ∃ L : ℝ≥0, LipschitzOnWith L (gradient f) B

end TimeScaleAvg


