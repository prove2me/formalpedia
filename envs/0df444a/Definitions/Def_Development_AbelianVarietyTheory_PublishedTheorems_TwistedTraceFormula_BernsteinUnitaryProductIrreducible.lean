-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
-- name    : Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:34.650815+00:00
-- url     : https://prove2.me/theorems/9741761c-2e22-4f59-a333-8d0a617682e8
-- title:
--   Bernstein Unitary Product Irreducible
-- statement:
--   Definitions and structural lemmas for Bernstein Unitary Product Irreducible, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/BernsteinUnitaryProductIrreducible.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
namespace GlobalTheory.Published
def BernsteinUnitaryProductIrreducible : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W),
    IsSmooth π₁ → π₁.IsIrreducible → IsUnitarisable π₁ →
    IsSmooth π₂ → π₂.IsIrreducible → IsUnitarisable π₂ →
    (prod₂ π₁ π₂).IsIrreducible
namespace BernsteinUnitaryProductIrreducible
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
end BernsteinUnitaryProductIrreducible
end GlobalTheory.Published


