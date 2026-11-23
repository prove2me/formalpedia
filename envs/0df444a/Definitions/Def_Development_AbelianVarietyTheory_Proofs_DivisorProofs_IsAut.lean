-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAut
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAut
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:47.163741+00:00
-- url     : https://prove2.me/theorems/440d5591-a7f7-4456-87cb-b3821be3ffa8
-- title:
--   Is Aut
-- statement:
--   Definitions and structural lemmas for Is Aut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAut.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace GlobalTheory.ThK.Dbl
def IsAut {G : Type} [Group G] [TopologicalSpace G] (Γ : Subgroup G) (f : G → ℂ) : Prop :=
  Continuous f ∧ (∀ γ ∈ Γ, ∀ h, f (γ * h) = f h) ∧ ∃ U : Subgroup G, IsOpen (U : Set G) ∧
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun u : U => fun x => f (x * u)))
def opT {G : Type} [MeasurableSpace G] (μ : Measure G) (𝓕 : Set G) (k : G → G → ℂ) (φ : G → ℂ) : G → ℂ :=
  fun h => ∫ h' in 𝓕, φ h' * k h h' ∂μ
def rconv {G : Type} [Mul G] [MeasurableSpace G] (μ : Measure G) (ψ : G → ℂ) (φ : G → ℂ) : G → ℂ :=
  fun h => ∫ g, ψ g * φ (h * g) ∂μ
def InSpan {G : Type} [Mul G] (f f' u u' : G → ℂ) : Prop :=
  ∃ (n : ℕ) (y : Fin n → G) (c : Fin n → ℂ),
    u = (fun h => ∑ j, c j * f (h * y j)) ∧ u' = (fun h => ∑ j, c j * f' (h * y j))
end GlobalTheory.ThK.Dbl


