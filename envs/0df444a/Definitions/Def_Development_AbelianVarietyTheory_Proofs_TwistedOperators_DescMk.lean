-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DescMk
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_DescMk
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:28.003791+00:00
-- url     : https://prove2.me/theorems/73d09954-f99b-42c3-871a-e064d74646d7
-- title:
--   Desc Mk
-- statement:
--   Definitions and structural lemmas for Desc Mk, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DescMk.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.QuotientDescentTwistedOperators
open Topology
noncomputable def desc {G : Type} [AddCommGroup G] [TopologicalSpace G] (Γ : AddSubgroup G)
    (f : G → ℂ) (hf : Continuous f) (hΓ : ∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) : C(G ⧸ Γ, ℂ) where
  toFun := fun q => Quotient.liftOn' q f (by
    intro a b hab
    rw [QuotientAddGroup.leftRel_apply] at hab
    have := hΓ _ hab a
    rw [← this]
    congr 1
    abel)
  continuous_toFun := hf.quotient_liftOn' _
end GlobalTheory.QuotientDescentTwistedOperators


