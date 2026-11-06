-- Prove2me | Definitions.Def_PADMPriv_stopLaw
-- name    : PADMPriv_stopLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:08:31.116392+00:00
-- url     : https://prove2.me/theorems/1cdb710d-2ff6-408e-bfd4-7441cd2d2e47
-- title:
--   Uniform law of the stopping time $K$
-- statement:
--   The stopping time $K$ of Stop-PADM is uniformly distributed on $\{\lfloor n/2\rfloor+1,\dots,n\}$:
--   $$
--   \Pr[K=k] = \frac{1}{\lceil n/2\rceil},\qquad k\in\{\lfloor n/2\rfloor+1,\dots,n\}.
--   $$
--
--   **Formalization Note** A measure on $\mathbb N$: the average of the point masses on the window, a probability measure for $n\ge1$.
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Section 4.2, p.10

import Mathlib
import Definitions.Def_PADMPriv_stopWindow

namespace PADMPriv

open MeasureTheory

/-- The law of the stopping time `K` of Stop-PADM, Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), Section 4.2, p.10:
`K` is uniform on `{⌊n/2⌋ + 1, …, n}`.

**Formalization Note** A measure on `ℕ`: the average of the Dirac masses at the points of the
window. It is a probability measure for `n ≥ 1`. -/
noncomputable def stopLaw (n : ℕ) : Measure ℕ :=
  ((stopWindow n).card : NNReal)⁻¹ • ∑ k ∈ stopWindow n, Measure.dirac k

instance stopLaw_isFiniteMeasure (n : ℕ) : IsFiniteMeasure (stopLaw n) := by
  unfold stopLaw
  infer_instance

end PADMPriv


