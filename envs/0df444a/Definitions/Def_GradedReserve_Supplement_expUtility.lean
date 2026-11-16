-- Prove2me | Definitions.Def_GradedReserve_Supplement_expUtility
-- name    : GradedReserve_Supplement_expUtility
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:38:24.588989+00:00
-- url     : https://prove2.me/theorems/6942543f-b2c1-4de5-95b5-554ec56a0465
-- title:
--   Expected utility of a bidder (per user and round)
-- statement:
--   The ex-ante expected utility of bidder $i$, i.e. of the user it represents, under a strategy profile $\sigma$:
--   $$u_i=\mathbb E\big[V_i\,q_i(V_i)-m_i(V_i)\big].$$
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 4.3 part 4, p.10 (PDF 11)

import Mathlib
import Definitions.Def_GradedReserve_typeMeasure
import Definitions.Def_GradedReserve_Supplement_interimQ
import Definitions.Def_GradedReserve_Supplement_interimM
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- The ex-ante expected utility of bidder `i` (the user it represents) under the strategy profile
`σ`: `E[Vᵢ qᵢ(Vᵢ) − mᵢ(Vᵢ)]` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 4.3 part 4, p.10, PDF 11, "the utility per user and
round"). -/
noncomputable def expUtility {n : ℕ} (M : Mechanism n) (f : ℝ → ℝ) (σ : Fin n → Kernel ℝ ℝ)
    (i : Fin n) : ℝ :=
  ∫ v, (v * interimQ M f σ i v - interimM M f σ i v) ∂(typeMeasure f)

end GradedReserve.Supplement


