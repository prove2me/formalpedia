-- Prove2me | Definitions.Def_PricingWithTips_Finset3DM
-- name    : PricingWithTips_Finset3DM
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-21T20:15:09.995235+00:00
-- url     : https://prove2.me/theorems/7bb27fae-1c6c-498d-8424-86dfff662cf1
-- title:
--   Finite-set three-dimensional matching
-- statement:
--   For an equal-cardinality three-dimensional matching instance, this module defines an exact-cover formulation using a finite set of triples. A selected matching covers every vertex in each of the three coordinate classes exactly once. This representation is the conventional finite-set interface used by formalized reductions and bridges to the allocation-based representation used for Theorems 4.1 and 4.2.
-- source:
--   Chen, Hu, Li, and Wang, Online Food Delivery Platforms: Pricing with Tips, arXiv:2507.10872v1, Section 4, reduction from 3-dimensional matching, https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips_ThreeDM

namespace PricingWithTips

/-- A triple in an equal-cardinality three-dimensional matching instance. -/
abbrev ThreeDMTriple (n : ℕ) := Fin n × Fin n × Fin n

/-- Every vertex in the codomain occurs in exactly one selected triple. -/
def IsExactCover3DM {α β : Type*} (M : Finset α) (p : α → β) : Prop :=
  ∀ b : β, ∃! t : α, t ∈ M ∧ p t = b

/-- A finite set of triples contains a perfect three-dimensional matching. -/
def HasPerfectFinset3DM (n : ℕ) (T : Finset (ThreeDMTriple n)) : Prop :=
  ∃ M : Finset (ThreeDMTriple n), M ⊆ T ∧
    IsExactCover3DM M Prod.fst ∧
    IsExactCover3DM M (fun t => t.2.1) ∧
    IsExactCover3DM M (fun t => t.2.2)

end PricingWithTips


