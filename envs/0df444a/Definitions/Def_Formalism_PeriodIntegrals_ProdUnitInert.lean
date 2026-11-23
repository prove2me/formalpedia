-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_ProdUnitInert
-- name    : Formalism_PeriodIntegrals_ProdUnitInert
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:07.112341+00:00
-- url     : https://prove2.me/theorems/d80773df-46cf-4289-bb07-0a32abd6505d
-- title:
--   Prod Unit Inert
-- statement:
--   Definitions and structural lemmas for Prod Unit Inert, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ProdUnitInert.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.ProdUnitInert
open Classical
abbrev Qbar : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ
def lamC {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (x : ℂ) : ℂ_[p] :=
  if h : x ∈ Qbar then lam ⟨x, h⟩ else 0
end PI.ProdUnitInert
namespace PI
open PI.ProdUnitInert
def ProdUnitInert : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (K : IntermediateField ℚ E) (c : E →+* E) (φ₀ : E →+* ℂ) (S : Type) [Fintype S]
    (emb : S → E →+* ℂ), Function.Injective emb → (∀ (s : S) (a : K), emb s (a : E) = φ₀ (a : E)) →
    Fintype.card S = Module.finrank K E → (∀ (φ : E →+* ℂ) (x : E), φ (c x) = (starRingEnd ℂ) (φ x)) →
    Module.finrank ℚ K = 2 → ∀ (d p : ℕ) [Fact p.Prime] (b : K), b ^ 2 = ((-(d : ℤ) : ℤ) : K) →
    jacobiSym (-(d : ℤ)) p = -1 → ∀ (lam : Qbar →+* ℂ_[p]) (z : E), z * c z = 1 →
    ‖lamC lam (∏ s, emb s z)‖ = 1
end PI
end


