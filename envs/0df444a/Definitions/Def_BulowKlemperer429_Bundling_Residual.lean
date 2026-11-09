-- Prove2me | Definitions.Def_BulowKlemperer429_Bundling_Residual
-- name    : BulowKlemperer429_Bundling_Residual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:45:15.235202+00:00
-- url     : https://prove2.me/theorems/ae317609-b7d6-40e9-906e-28a0f16b86b2
-- title:
--   Utility-subtracted value and unallocated value
-- statement:
--   For a truthful mechanism $M=(x,p)$ on finitely many nonnegative item values, let $u(v)=\sum_jv_jx_j(v)-p(v)$. Define
--   $$w(v)=\sum_jv_j-u(v),\qquad \ell(v)=\sum_jv_j(1-x_j(v)).$$
--   Thus $w=p+\ell$. The residual $w$ and the unallocated value $\ell$ measure different portions of value left after utility is deducted.
--
--   The mechanism is the published direct-mechanism model, reused without altering its admissibility predicate. Real-coordinate expressions are evaluated on the nonnegative orthant through $z\mapsto\max(z,0)$; coordinate slices replace just one coordinate. These extensions provide a real vector space for joint concavity and real functions for right derivatives, and do not restrict mechanisms or their allocation measurability.
-- source:
--   Yichen Huang, STOC 2027 submission #429 (October 2026), p. 7, §3.1, definitions of w and ℓ (PDF p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/429.pdf

import Mathlib
import Definitions.Def_MultiItemRev_BundlingOpt_Model
import Definitions.Def_BulowKlemperer429_Bundling_Variation
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace BulowKlemperer429.Bundling

variable {ι : Type} [Fintype ι]

/-- Section 3.1 p. 7: total value minus the buyer's utility. -/
def residual (M : MultiItemRev.BundlingOpt.Mechanism ι) (v : ι → ℝ≥0) : ℝ :=
  (∑ j, (v j : ℝ)) - MultiItemRev.BundlingOpt.buyerPayoff M v

/-- Unallocated value; no allocation-measurability hypothesis is built in. -/
def unallocated (M : MultiItemRev.BundlingOpt.Mechanism ι) (v : ι → ℝ≥0) : ℝ :=
  ∑ j, (v j : ℝ) * (1 - M.q v j)

/-- Real-coordinate extension, used only on the closed nonnegative orthant. -/
def residualReal (M : MultiItemRev.BundlingOpt.Mechanism ι) (v : ι → ℝ) : ℝ :=
  residual M (fun j => (v j).toNNReal)

/-- The coordinate slice agrees with w(v₋ⱼ,z) for z ≥ 0. -/
noncomputable def residualSlice (M : MultiItemRev.BundlingOpt.Mechanism ι)
    (v : ι → ℝ≥0) (j : ι) (z : ℝ) : ℝ := by
  classical
  exact residual M (Function.update v j z.toNNReal)

end BulowKlemperer429.Bundling


