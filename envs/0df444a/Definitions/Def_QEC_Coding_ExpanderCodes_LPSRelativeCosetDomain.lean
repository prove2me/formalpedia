-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain
-- name    : QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:11:25.028187+00:00
-- url     : https://prove2.me/theorems/aebeca14-a5ae-433f-8390-d48f8d2d6d20
-- title:
--   LPSRelative Coset Domain
-- statement:
--   Definitions and structural lemmas for LPSRelative Coset Domain, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRelativeCosetDomain.lean

import Mathlib.MeasureTheory.Group.FundamentalDomain
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open MeasureTheory Set Filter
open scoped Pointwise ENNReal
noncomputable section
variable {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α] [Countable G]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance lpsRelativeDomain_countableQuotient (H : Subgroup G) : Countable (G ⧸ H) :=
  inferInstanceAs (Countable (Quotient (QuotientGroup.leftRel H)))
def lpsRelativeDomain (H : Subgroup G) (s : Set α)
    (r : G ⧸ H → G) : Set α :=
  ⋃ c : G ⧸ H, (r c)⁻¹ • s
section IndexedRelative
variable {G α I : Type*} [Group G] [MulAction G α] [MeasurableSpace α] [Countable G]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]
  [Fintype I] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
end IndexedRelative
end
end QEC.Coding.TannerLiftedProduct


