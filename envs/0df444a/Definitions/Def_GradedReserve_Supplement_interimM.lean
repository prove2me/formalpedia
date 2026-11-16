-- Prove2me | Definitions.Def_GradedReserve_Supplement_interimM
-- name    : GradedReserve_Supplement_interimM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:37:12.523842+00:00
-- url     : https://prove2.me/theorems/2754d66e-a897-4b74-ae52-6248c2324559
-- title:
--   Interim expected payment $m_i(v)$
-- statement:
--   The interim expected payment of bidder $i$ at type $v$ under a strategy profile $\sigma$:
--   $$m_i(v)=\int P_i(a)\,\sigma_i(v)(da).$$
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section B, p.26 (PDF 27)

import Mathlib
import Definitions.Def_GradedReserve_Supplement_profileLaw
import Definitions.Def_GradedReserve_Supplement_payAgainst
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- The interim expected payment `mᵢ(v)` of bidder `i` at type `v` under the strategy profile `σ`
(Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section B, p.26, PDF 27), averaging over its own mixing and the opponents' values and
actions. -/
noncomputable def interimM {n : ℕ} (M : Mechanism n) (f : ℝ → ℝ) (σ : Fin n → Kernel ℝ ℝ)
    (i : Fin n) (v : ℝ) : ℝ :=
  ∫ a, payAgainst M (profileLaw f σ) i a ∂(σ i v)

end GradedReserve.Supplement


