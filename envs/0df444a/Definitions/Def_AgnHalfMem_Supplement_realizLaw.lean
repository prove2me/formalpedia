-- Prove2me | Definitions.Def_AgnHalfMem_Supplement_realizLaw
-- name    : AgnHalfMem_Supplement_realizLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:56:45.49792+00:00
-- url     : https://prove2.me/theorems/2d5db2aa-75b7-4a5d-9268-7225005965d6
-- title:
--   The distribution realizable by the halfspace $w^*$ with marginal $\mu$
-- statement:
--   For a probability distribution $\mu$ on $\mathbb R^d$ and a vector $w^*\in\mathbb R^d$, let $D_{\mu,w^*}$ be the law of
--   $$
--   \big(x,\ \mathrm{sign}(\langle w^*,x\rangle)\big),\qquad x\sim\mu ,
--   $$
--   with $\mathrm{sign}(0)=+1$. This is the distribution *realizable by the halfspace $w^*$ with fixed marginal $\mu$* of Theorem 5.2: its $x$-marginal is $\mu$ and its labels are exactly those of the halfspace $h_{w^*}$.
--
--   **Formalization Note** The labelling map is measurable, so $D_{\mu,w^*}$ is a probability distribution with $x$-marginal $\mu$ (checked in the mission's sanity file).
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), Theorem 5.2 and its proof, p.19

import Mathlib
import Definitions.Def_AgnHalfMem_halfspace

open MeasureTheory

namespace AgnHalfMem

namespace Supplement

/-- **Distribution realizable by a halfspace with a fixed marginal.** S. Garg, T. Jadhav,
*Memory-Sample Tradeoffs for Agnostically Learning Halfspaces*, STOC 2027 submission (manuscript,
PDF sha256 386bc9b3…43f84d5), Theorem 5.2, p.19: "a distribution realizable by a halfspace with a
fixed marginal µ"; proof, p.19: "µ is the known marginal distribution", labels `h_{w*}(x)`.

For a probability measure `µ` on `ℝ^d` and a vector `w*`, `realizLaw µ w*` is the law of
`(x, sign(⟨w*, x⟩))` with `x ∼ µ`.

**Formalization Note.** The map `x ↦ (x, halfspace w* x)` is measurable (the halfspace is the
indicator of a closed set), so this is a probability measure with `X`-marginal `µ` whenever `µ`
is one. Labels are `Bool` (`true ↔ +1`), with `sign(0) = +1`. -/
noncomputable def realizLaw {d : ℕ} (μ : Measure (Fin d → ℝ)) (w : Fin d → ℝ) :
    Measure ((Fin d → ℝ) × Bool) :=
  μ.map (fun x => (x, halfspace w x))

end Supplement

end AgnHalfMem


