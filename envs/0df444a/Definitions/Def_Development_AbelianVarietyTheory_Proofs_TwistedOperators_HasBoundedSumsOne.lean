-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:59.539866+00:00
-- url     : https://prove2.me/theorems/1b7d0467-05d5-4a91-a255-eff854c2e2ca
-- title:
--   Has Bounded Sums One
-- statement:
--   Definitions and structural lemmas for Has Bounded Sums One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasBoundedSumsOne.lean

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
open GlobalTheory.SplitWeil GlobalTheory.SmGL
namespace GlobalTheory.SatakeBound
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
def IsBorelSph (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ) : Prop :=
  (∀ g : GL (Fin n) k, ∀ x ∈ KO k (Fin n), φ (g * x) = φ g) ∧
    ∀ b ∈ borel k (Fin n), ∀ t : Fin n → kˣ,
      (∀ i, (b : Matrix (Fin n) (Fin n) k) i i = t i) → φ b = ∏ i, γ i ^ ord k (t i)
def HasBoundedSums (φ : GL (Fin n) k → ℂ) : Prop :=
  ∀ S : Finset (GL (Fin n) k ⧸ KO k (Fin n)), (∀ x ∈ KO k (Fin n), ∀ c ∈ S, x • c ∈ S) →
    ‖∑ c ∈ S, φ c.out‖ ≤ S.card
end GlobalTheory.SatakeBound


