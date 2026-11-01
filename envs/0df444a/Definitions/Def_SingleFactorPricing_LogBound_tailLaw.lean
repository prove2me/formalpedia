-- Prove2me | Definitions.Def_SingleFactorPricing_LogBound_tailLaw
-- name    : SingleFactorPricing_LogBound_tailLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:14:57.988039+00:00
-- url     : https://prove2.me/theorems/8c836b97-3ed8-4460-9e44-8413dc98082b
-- title:
--   The type law of the tight instance
-- statement:
--   For $\rho>1$, the probability law on the interval $[1,\rho]$ of willingness-to-pay values with density $v^{-2}$ on $(1,\rho)$ and an atom of mass $1/\rho$ at $\rho$. Its tail is
--
--   $$
--   \mu\{v\ge p\}=\min(1,1/p),\qquad 0<p\le\rho .
--   $$
--
--   This is the distribution of types in the paper's tight instance.
--
--   **Formalization Note** The paper's tail $k\min(1,1/p)$ has total mass $k$. Since §2 requires a distribution of total mass one, the factor $k$ is carried by each type's demand (`tightDemand`).
-- source:
--   Gallego, Berbeglia, Bounds and Heuristics for Multi-Product Personalized Pricing, arXiv:2102.03038v2, proof of Theorem 1, p.4

import Mathlib

open MeasureTheory

namespace SingleFactorPricing.LogBound

/-- **The type law of the tight instance.** Gallego, Berbeglia, arXiv:2102.03038v2, proof of
Theorem 1, p.4: "a continuum of types with willingness to pay in the interval `[1, ρ]`".

**Formalization Note.** The probability law on `[1, ρ]` with tail `μ{v ≥ p} = min(1, 1/p)` for
`0 < p ≤ ρ`: density `v⁻²` on `(1, ρ)` plus an atom of mass `1/ρ` at `ρ`. The paper's tail
`k min(1, 1/p)` has total mass `k`, so the factor `k` is carried by each type's demand
(`tightDemand`) and the types form a probability law, as §2 requires. -/
noncomputable def tailLaw (ρ : ℝ) : Measure (Set.Icc (1 : ℝ) ρ) :=
  Measure.comap Subtype.val
    ((volume.restrict (Set.Ioo 1 ρ)).withDensity (fun v => ENNReal.ofReal (v ^ 2)⁻¹) +
      ENNReal.ofReal (1 / ρ) • Measure.dirac ρ)

end SingleFactorPricing.LogBound


