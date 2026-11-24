-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_SpanOrbitStab
-- name    : Development_WeilBound_ThetaLifts_CartanFactorisation_SpanOrbitStab
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:42.329733+00:00
-- url     : https://prove2.me/theorems/12e5f1c2-8e7f-41a7-893c-26c0a9eb8f80
-- title:
--   Span Orbit Stab
-- statement:
--   Definitions and structural lemmas for Span Orbit Stab, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/SpanOrbitStab.lean

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
namespace PositivityTheory.ThKF.Abs
open scoped InnerProductSpace
variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
def orb {K : Type} [Group K] (κ : K →* Module.End ℂ U) (x : U) : Submodule ℂ U := Submodule.span ℂ (Set.range fun k => κ k x)
def homs {K : Type} [Group K] (κ : K →* Module.End ℂ U) (W : Submodule ℂ U) : Submodule ℂ (U →ₗ[ℂ] U) where
  carrier := {L | (∀ x, L x ∈ W) ∧ ∀ k x, L (κ k x) = κ k (L x)}
  add_mem' := fun {a b} ha hb => ⟨fun x => add_mem (ha.1 x) (hb.1 x), fun k x => by simp [ha.2, hb.2]⟩
  zero_mem' := ⟨fun x => by simp, fun k x => by simp⟩
  smul_mem' := fun c a ha => ⟨fun x => W.smul_mem c (ha.1 x), fun k x => by simp [ha.2]⟩
def ck (H : Submodule ℂ (U →ₗ[ℂ] U)) : Submodule ℂ U where
  carrier := {z | ∀ L ∈ H, L z = 0}
  add_mem' := fun {a b} ha hb L hL => by rw [map_add, ha L hL, hb L hL, add_zero]
  zero_mem' := fun L _ => map_zero L
  smul_mem' := fun c a ha L hL => by rw [map_smul, ha L hL, smul_zero]
def Proj (St : Submodule ℂ U → Prop) : Prop :=
  ∀ f : U, ∃ Z Z' : Submodule ℂ U, FiniteDimensional ℂ Z ∧ f ∈ Z ∧ Z = Z'ᗮ ∧
    ∀ S : Submodule ℂ U, St S → ∀ u ∈ S, ∃ y ∈ S, ∃ z ∈ S, y ∈ Z ∧ z ∈ Z' ∧ u = y + z
end PositivityTheory.ThKF.Abs
end


