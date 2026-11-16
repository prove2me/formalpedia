-- Prove2me | Definitions.Def_GradedReserve_Supplement_interimQ
-- name    : GradedReserve_Supplement_interimQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:36:43.783921+00:00
-- url     : https://prove2.me/theorems/27ad60a5-7c20-484d-aa97-249e0614f08b
-- title:
--   Interim allocation $q_i(v)$
-- statement:
--   The interim allocation of bidder $i$ at type $v$ under a strategy profile $\sigma$ is the probability that type $v$ receives the item, averaging over its own mixing and the opponents' values and actions:
--   $$q_i(v)=\int W_i(a)\,\sigma_i(v)(da).$$
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section B, p.26 (PDF 27)

import Mathlib
import Definitions.Def_GradedReserve_Supplement_profileLaw
import Definitions.Def_GradedReserve_Supplement_allocAgainst
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- The interim allocation `qᵢ(v)` of bidder `i` at type `v` under the strategy profile `σ`:
the probability that type `v` of bidder `i` receives the item, averaging over its own mixing
(Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section B, p.26, PDF 27: "`qᵢ(v)` and `mᵢ(v)` denote the equilibrium interim allocation and
expected payment, including any mixing"). -/
noncomputable def interimQ {n : ℕ} (M : Mechanism n) (f : ℝ → ℝ) (σ : Fin n → Kernel ℝ ℝ)
    (i : Fin n) (v : ℝ) : ℝ :=
  ∫ a, allocAgainst M (profileLaw f σ) i a ∂(σ i v)

end GradedReserve.Supplement


