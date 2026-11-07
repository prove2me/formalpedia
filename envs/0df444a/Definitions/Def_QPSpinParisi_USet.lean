-- Prove2me | Definitions.Def_QPSpinParisi_USet
-- name    : QPSpinParisi_USet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:02:04.02525+00:00
-- url     : https://prove2.me/theorems/ef0b6698-4e9f-4b91-9f05-dd34e6a97c21
-- title:
--   The class $\mathcal U$ of order parameters
-- statement:
--   The class $\mathcal U$ consists of all nonnegative, nondecreasing, right continuous functions $\gamma$ on $[0,1)$ with
--   $$\int_0^1\gamma(t)\,dt<\infty.$$
--   The infimum of the Parisi functional in Theorem 1 runs over this class. Its members may be unbounded near $1$.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.4 (PDF p.4)

import Mathlib
import Definitions.Def_QPSpinParisi_gamHat

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The class `U` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.4, PDF p.4): nonnegative, nondecreasing, right continuous functions `γ` on `[0, 1)` with
`∫₀¹ γ(t) dt < ∞`.

**Formalization Note** The domain is `Ico 0 1`, so two members that differ are different functions of the source. `γ` may
blow up at `1`, and the integrability clause is what makes every integral over `[0,1]` honest. -/
def USet : Set (Ico (0 : ℝ) 1 → ℝ) :=
  {γ | (∀ t, 0 ≤ γ t) ∧ Monotone γ ∧ (∀ t, ContinuousWithinAt γ (Ioi t) t) ∧
    IntegrableOn (gamHat γ) (Ico 0 1)}

end QPSpinParisi


