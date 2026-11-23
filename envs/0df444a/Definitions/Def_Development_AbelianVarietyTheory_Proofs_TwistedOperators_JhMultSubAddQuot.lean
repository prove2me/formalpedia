-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_JhMultSubAddQuot
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_JhMultSubAddQuot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:31.728058+00:00
-- url     : https://prove2.me/theorems/3cff5c1c-a388-4b87-9d3b-85fb2a0de44b
-- title:
--   Jh Mult Sub Add Quot
-- statement:
--   Definitions and structural lemmas for Jh Mult Sub Add Quot, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/JhMultSubAddQuot.lean

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
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
namespace GlobalTheory.JHMult
variable {F G V W V₁ V₂ : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
def subMap {ρ : Representation F G V} {ρ₁ : Representation F G V₁} (p : ρ.IntertwiningMap ρ₁)
    (S : Subrepresentation ρ) : Subrepresentation ρ₁ :=
  ⟨S.toSubmodule.map p.toLinearMap, by
    rintro g _ ⟨v, hv, rfl⟩
    exact ⟨ρ g v, S.apply_mem_toSubmodule g hv, p.isIntertwining _ _ g v⟩⟩
def subComap {ρ : Representation F G V} {ρ₁ : Representation F G V₁} (p : ρ.IntertwiningMap ρ₁)
    (S : Subrepresentation ρ₁) : Subrepresentation ρ :=
  ⟨S.toSubmodule.comap p.toLinearMap, fun g v hv => by
    show p (ρ g v) ∈ S.toSubmodule
    rw [p.isIntertwining]
    exact S.apply_mem_toSubmodule g hv⟩
def Step (σ : Representation F G W) {ρ : Representation F G V} (S T : Subrepresentation ρ) : Prop :=
  ∃ f : V →ₗ[F] W, (∀ w, ∃ v ∈ S.toSubmodule, f v = w) ∧
    (∀ g, ∀ v ∈ S.toSubmodule, f (ρ g v) = σ g (f v)) ∧
    ∀ v ∈ S.toSubmodule, (f v = 0 ↔ v ∈ T.toSubmodule)
section Exact
variable {σ : Representation F G W} {ρ : Representation F G V} {ρ₁ : Representation F G V₁}
  {ρ₂ : Representation F G V₂} (ι : ρ₁.IntertwiningMap ρ) (p : ρ.IntertwiningMap ρ₂)
end Exact
end GlobalTheory.JHMult


