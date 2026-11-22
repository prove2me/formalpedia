-- Prove2me | Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrExistsMeasRep
-- name    : Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrExistsMeasRep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:24:51.102181+00:00
-- url     : https://prove2.me/theorems/b1252f6b-0b8c-4cf1-9b3d-3edba8eb0b5f
-- title:
--   Rr Exists Meas Rep
-- statement:
--   Definitions and structural lemmas for Rr Exists Meas Rep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrExistsMeasRep.lean

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
namespace Formalism.MainNotions.LeviCoordinates
open MeasureTheory Set
open scoped ENNReal Pointwise InnerProductSpace
def rr_rep {G : Type*} [Mul G] (S D : Set G) (y : G) : G := by
  classical
  exact if h : ∃ γ ∈ S, γ * y ∈ D then h.choose * y else y
section Abs
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
structure rr_FD (μ : Measure G) (Γ : Subgroup G) (D : Set G) : Prop where
  meas : MeasurableSet D
  cov : ∀ y : G, ∃ γ ∈ (Γ : Set G), γ * y ∈ D
  disj : ∀ γ ∈ (Γ : Set G), γ ≠ 1 → μ ((fun y => γ * y) '' D ∩ D) = 0
def rr_N (Γ : Subgroup G) (D : Set G) : Set G :=
  {y | ∃ γ₁ ∈ Γ, ∃ γ₂ ∈ Γ, γ₁ ≠ γ₂ ∧ γ₁ * y ∈ D ∧ γ₂ * y ∈ D}
variable {μ : Measure G} {Γ : Subgroup G} {D : Set G}
end Abs
section Abs2
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
variable {μ : Measure G} {Γ : Subgroup G} {D : Set G}
def rr_IsReg (μ : Measure G) (Γ : Subgroup G) (D : Set G)
    (R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))) : Prop :=
  ∀ g F, ((R g F : Lp ℂ 2 (μ.restrict D)) : G → ℂ) =ᵐ[μ.restrict D]
    fun x => (F : G → ℂ) (rr_rep (Γ : Set G) D (x * g))
variable {R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))}
end Abs2
end Formalism.MainNotions.LeviCoordinates
end


