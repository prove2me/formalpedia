-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionOfIsPushout
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionOfIsPushout
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:03:21.425994+00:00
-- url     : https://prove2.me/theorems/52bc333e-677b-43c4-b4fe-7c49e02ba7ee
-- title:
--   Is Extension Of Is Pushout
-- statement:
--   Definitions and structural lemmas for Is Extension Of Is Pushout, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsExtensionOfIsPushout.lean

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
namespace GlobalTheory.FieldBaseChange
variable {K F : Type} [Field K] [Field F] [Algebra K F]
section Basic
variable {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module F W]
def IsCoord (a : V →ₛₗ[algebraMap K F] W) (ℓ : F →ₗ[K] K) (Λ : W →+ V) : Prop :=
  ∀ c v, Λ (c • a v) = ℓ c • v
structure IsExtension (a : V →ₛₗ[algebraMap K F] W) : Prop where
  span : Submodule.span F (Set.range a) = ⊤
  coord : ∀ ℓ : F →ₗ[K] K, ∃ Λ, IsCoord a ℓ Λ
end Basic
section Graph
variable {R : Type} [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K]
  {V₀ V V' W W' : Type} [AddCommGroup V₀] [Module R V₀] [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module F V'] [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module F W']
  {J : Type} {P₀ P P' : J → Type} [∀ j, AddCommGroup (P₀ j)] [∀ j, Module R (P₀ j)]
  [∀ j, AddCommGroup (P j)] [∀ j, Module K (P j)] [∀ j, AddCommGroup (P' j)] [∀ j, Module F (P' j)]
end Graph
end GlobalTheory.FieldBaseChange


