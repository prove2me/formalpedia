-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaussianDualMeasure_DualMeasure
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaussianDualMeasure_DualMeasure
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:50.604972+00:00
-- url     : https://prove2.me/theorems/116b8a0c-281f-4dfe-9cea-c607facb3bf8
-- title:
--   Dual Measure
-- statement:
--   Definitions and structural lemmas for Dual Measure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaussianDualMeasure/DualMeasure.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GaussIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory
noncomputable section
namespace PI.GI
def dual {F : Type} [Field F] (ψ : AddChar F ℂ) {d : ℕ} (L : Set (Fin d → F)) : Set (Fin d → F) :=
  {w | ∀ y ∈ L, ψ (dotProduct y w) = 1}
def md {F : Type} [Field F] [ValuativeRel F] [MeasurableSpace F] (μ : Measure F) (a : F) : ENNReal :=
  μ ((fun y => a * y) '' (𝒪[F] : Set F))
open scoped Classical in

def Orth : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] [MeasurableSpace F] [BorelSpace F] (μ : Measure F), μ.IsAddHaarMeasure →
    μ (𝒪[F] : Set F) = 1 →
  ∀ (ψ : AddChar F ℂ), Continuous ψ → (∀ x : F, (∀ y ∈ 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) →
  ∀ (d : ℕ) (K : AddSubgroup (Fin d → F)), IsCompact (K : Set (Fin d → F)) → IsOpen (K : Set (Fin d → F)) →
  ∀ w : Fin d → F,
    ∫ y in (K : Set (Fin d → F)), ψ (dotProduct y w) ∂(Measure.pi fun _ : Fin d => μ) =
      if w ∈ dual ψ (K : Set (Fin d → F)) then (((Measure.pi fun _ : Fin d => μ) (K : Set (Fin d → F))).toReal : ℂ) else 0
def SqFormula : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] [MeasurableSpace F] [BorelSpace F] (μ : Measure F), μ.IsAddHaarMeasure →
    μ (𝒪[F] : Set F) = 1 →
  ∀ (ψ : AddChar F ℂ), Continuous ψ → (∀ x : F, (∀ y ∈ 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) →
  ∀ (d : ℕ) (A : Matrix (Fin d) (Fin d) F), A.IsSymm →
  ∀ (L : AddSubgroup (Fin d → F)), IsCompact (L : Set (Fin d → F)) → IsOpen (L : Set (Fin d → F)) →
    ((‖∫ x in (L : Set (Fin d → F)), ψ (dotProduct x (A.mulVec x) / 2) ∂(Measure.pi fun _ : Fin d => μ)‖ ^ 2 : ℝ) : ℂ) =
      (((Measure.pi fun _ : Fin d => μ) (L : Set (Fin d → F))).toReal : ℂ) *
        ∫ z in {z | z ∈ (L : Set (Fin d → F)) ∧ A.mulVec z ∈ dual ψ (L : Set (Fin d → F))},
          ψ (dotProduct z (A.mulVec z) / 2) ∂(Measure.pi fun _ : Fin d => μ)
def SmallT : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] [MeasurableSpace F] [BorelSpace F] (μ : Measure F), μ.IsAddHaarMeasure →
    μ (𝒪[F] : Set F) = 1 →
  ∀ (ψ : AddChar F ℂ), Continuous ψ → (∀ x : F, (∀ y ∈ 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) →
  ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) F), H.IsSymm → H.det ≠ 0 →
  ∀ (L : AddSubgroup (Fin d → F)), IsCompact (L : Set (Fin d → F)) → IsOpen (L : Set (Fin d → F)) →
  ∃ δ : ℝ, 0 < δ ∧ ∀ t : F, t ≠ 0 → (md μ t).toReal < δ →
    {z | z ∈ (L : Set (Fin d → F)) ∧ (t⁻¹ • H).mulVec z ∈ dual ψ (L : Set (Fin d → F))} =
        (fun w => (t • H⁻¹).mulVec w) '' dual ψ (L : Set (Fin d → F)) ∧
    ∀ z ∈ (L : Set (Fin d → F)), (t⁻¹ • H).mulVec z ∈ dual ψ (L : Set (Fin d → F)) →
      ψ (dotProduct z ((t⁻¹ • H).mulVec z) / 2) = 1
def DetScale : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] [MeasurableSpace F] [BorelSpace F] (μ : Measure F), μ.IsAddHaarMeasure →
    μ (𝒪[F] : Set F) = 1 →
  ∀ (d : ℕ) (M : Matrix (Fin d) (Fin d) F), M.det ≠ 0 → ∀ S : Set (Fin d → F),
    (Measure.pi fun _ : Fin d => μ) ((fun w => M.mulVec w) '' S) = md μ M.det * (Measure.pi fun _ : Fin d => μ) S
def ModMul : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] [MeasurableSpace F] [BorelSpace F] (μ : Measure F), μ.IsAddHaarMeasure →
    μ (𝒪[F] : Set F) = 1 →
  ∀ a b : F, a ≠ 0 → b ≠ 0 → md μ (a * b) = md μ a * md μ b
def DualMeasure : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] [MeasurableSpace F] [BorelSpace F] (μ : Measure F), μ.IsAddHaarMeasure →
    μ (𝒪[F] : Set F) = 1 →
  ∀ (ψ : AddChar F ℂ), Continuous ψ → (∀ x : F, (∀ y ∈ 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) →
  ∀ (d : ℕ) (L : AddSubgroup (Fin d → F)), IsCompact (L : Set (Fin d → F)) → IsOpen (L : Set (Fin d → F)) →
    (Measure.pi fun _ : Fin d => μ) (L : Set (Fin d → F)) * (Measure.pi fun _ : Fin d => μ) (dual ψ (L : Set (Fin d → F))) = 1
end PI.GI


