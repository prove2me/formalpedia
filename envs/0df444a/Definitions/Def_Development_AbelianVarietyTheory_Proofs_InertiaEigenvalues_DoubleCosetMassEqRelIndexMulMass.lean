-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DoubleCosetMassEqRelIndexMulMass
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DoubleCosetMassEqRelIndexMulMass
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-27T05:29:05.815968+00:00
-- url     : https://prove2.me/theorems/9ff8de65-fa28-5900-ac5f-906b6f45f35f
-- title:
--   Double Coset Mass Eq Rel Index Mul Mass
-- statement:
--   Definitions and structural lemmas for Double Coset Mass Eq Rel Index Mul Mass, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DoubleCosetMassEqRelIndexMulMass.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteDcOfCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UnimodMass
variable {G : Type*} [Group G]
def dcMapLe {Γ W K : Subgroup G} (hWK : W ≤ K) : DC Γ W → DC Γ K :=
  Quotient.map' (s₁ := dcSetoid Γ W) (s₂ := dcSetoid Γ K) id (by
    intro a b hab
    obtain ⟨γ, hγ, κ, hκ, e⟩ := hab
    exact ⟨γ, hγ, κ, hWK hκ, e⟩)
def dcOfCoset (Γ W K : Subgroup G) (t : G) : K ⧸ W.subgroupOf K → DC Γ W :=
  Quotient.lift (fun k : K => (Quotient.mk (dcSetoid Γ W) (t * k))) (by
    intro a b hab
    apply Quotient.sound
    have h := (QuotientGroup.leftRel_apply).1 hab
    rw [Subgroup.mem_subgroupOf] at h
    refine ⟨1, Γ.one_mem, (a : G)⁻¹ * b, by simpa using h, ?_⟩
    simp [mul_assoc])
end GlobalTheory.UnimodMass
namespace GlobalTheory.UnimodMass
end GlobalTheory.UnimodMass
namespace GlobalTheory.UnimodMass
open scoped BigOperators
end GlobalTheory.UnimodMass


