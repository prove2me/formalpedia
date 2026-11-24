-- Prove2me | Definitions.Def_OpaquePricing_Dominance_Supplement_Harmonic
-- name    : OpaquePricing_Dominance_Supplement_Harmonic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:31:34.232232+00:00
-- url     : https://prove2.me/theorems/aa456647-55e8-4c28-b8b6-84ca98d35e2d
-- title:
--   Harmonic numbers and weighted maxima
-- statement:
--   For an integer $n\ge0$, define the harmonic number and two weighted maxima by
--   $$H_n=\sum_{i=1}^n\frac1i,\qquad M(x)=\max(0,\max_{1\le i\le n}ix_i),\qquad T(x)=\max(0,\max_{1\le i\le n}i\sum_{k=i}^n x_k).$$
--   The added zero specifies the empty-index value and has no effect for the nonnegative vectors used in Lemmas 6–7. Indices in Lean start at zero, so the mathematical weight $i$ is represented by the index plus one. These are arithmetic quantities, with no revenue inequality built into their definitions.
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), Appendix I.5, p. 48; Appendix J, pp. 52–53

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting

open MeasureTheory

namespace OpaquePricing.Dominance.Supplement

noncomputable def harmonic (n : ℕ) : ℝ := ∑ i : Fin n, 1 / ((i.val : ℝ) + 1)

/-- Maximum with outside value zero; equals the ordinary maximum on nonnegative inputs. -/
noncomputable def maxZero {n : ℕ} (f : Fin n → ℝ) : ℝ :=
  (Finset.univ.image f ∪ {0}).max' (by simp)

noncomputable def weightedMax {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  maxZero (fun i => ((i.val : ℝ) + 1) * x i)

noncomputable def weightedTailMax {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  maxZero (fun i => ((i.val : ℝ) + 1) * ∑ k : Fin n, if i ≤ k then x k else 0)

end OpaquePricing.Dominance.Supplement


