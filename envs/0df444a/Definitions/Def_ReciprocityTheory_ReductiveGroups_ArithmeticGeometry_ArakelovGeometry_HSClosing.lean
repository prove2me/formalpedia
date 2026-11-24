-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_HSClosing
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_HSClosing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:07.416438+00:00
-- url     : https://prove2.me/theorems/32e1802a-8b69-498f-becd-bac396db5d4a
-- title:
--   HSClosing
-- statement:
--   Definitions and structural lemmas for HSClosing, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/HSClosing.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
structure GDatum (D : ℕ) : Type 1 where

  Ω : Type
  [fieldΩ : Field Ω]
  [charΩ : CharZero Ω]

  κ : Type
  [fintypeκ : Fintype κ]

  x : Ix κ → Ω

  m : ConeMetric ℂ (Ix κ)

  μ : Measure (Ix κ → ℂ)
  good : IsGood D x m μ
attribute [instance] GDatum.fieldΩ GDatum.charΩ GDatum.fintypeκ
def IsInvMat {J : Type} [Fintype J] (A : Matrix J J ℚ) : Prop :=
  ∃ B : Matrix J J ℚ, ∀ v : J → ℚ, A.mulVec (B.mulVec v) = v ∧ B.mulVec (A.mulVec v) = v
def IsTransport {κ : Type} [Fintype κ] (A : Matrix (Ix κ) (Ix κ) ℚ) (m m' : ConeMetric ℂ (Ix κ))
    (μ μ' : Measure (Ix κ → ℂ)) : Prop :=
  (∀ z, m'.ρ (matActC A z) = m.ρ z) ∧ μ' = μ.map (matActC A)
def IsPullFS {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ} (x : Ix κ → Ω)
    (e : Fin (D + 1) → Ix κ) (m : ConeMetric ℂ (Ix κ)) : Prop :=
  ∀ z ∈ pts (coordIdeal ℤ x), m.ρ z = Real.sqrt (∑ k, ‖z (e k)‖ ^ 2)
def hhOf (I : AllFam) (D : ℕ) : ℝ :=
  I Unit (GlobalTheory (Fin (D + 1))) ⊥ (D + 1) fun _ => HermLine.ofCone (fsMetric (Ix (Fin (D + 1))))
abbrev pw (D : ℕ) : ℕ → ℝ := fun n => (n : ℝ) ^ (D + 1)
def StepA (I : AllFam) (D : ℕ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (m₀ m₁ : ConeMetric ℂ (Ix κ)) (μ : Measure (Ix κ → ℂ)) (e : Fin (D + 1) → Ix κ),
    IsProjFrame x e → IsGood D x m₀ μ → IsGood D x m₁ μ →
    (fun n => defect I D x m₁ μ n - defect I D x m₀ μ n) =o[atTop] pw D
def StepT (D : ℕ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (m : ConeMetric ℂ (Ix κ)) (μ : Measure (Ix κ → ℂ)) (A : Matrix (Ix κ) (Ix κ) ℚ)
    (e : Fin (D + 1) → Ix κ),
    IsGood D x m μ → IsInvMat A → IsProjFrame (matAct A x) e →
    ∃ m' μ', IsTransport A m m' μ μ' ∧ IsGood D (matAct A x) m' μ'
def StepB (I : AllFam) (D : ℕ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (m m' : ConeMetric ℂ (Ix κ)) (μ μ' : Measure (Ix κ → ℂ)) (A : Matrix (Ix κ) (Ix κ) ℚ)
    (e : Fin (D + 1) → Ix κ),
    IsGood D x m μ → IsInvMat A → IsProjFrame (matAct A x) e → IsTransport A m m' μ μ' →
    IsGood D (matAct A x) m' μ' →
    (fun n => defect I D (matAct A x) m' μ' n - defect I D x m μ n) =o[atTop] pw D
def StepN (D : ℕ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (m : ConeMetric ℂ (Ix κ)) (μ : Measure (Ix κ → ℂ)), IsGood D x m μ →
    ∃ (A : Matrix (Ix κ) (Ix κ) ℚ) (e : Fin (D + 1) → Ix κ),
      IsInvMat A ∧ IsProjFrame (matAct A x) e
def StepM (D : ℕ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (m : ConeMetric ℂ (Ix κ)) (μ : Measure (Ix κ → ℂ)) (e : Fin (D + 1) → Ix κ),
    IsGood D x m μ → IsProjFrame x e → ∃ m₀, IsPullFS x e m₀ ∧ IsGood D x m₀ μ
def StepC (I : AllFam) (D : ℕ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (m : ConeMetric ℂ (Ix κ)) (μ : Measure (Ix κ → ℂ)) (e : Fin (D + 1) → Ix κ),
    IsGood D x m μ → IsProjFrame x e → IsPullFS x e m →
    (fun n => defect I D x m μ n - (projDeg x e : ℝ) * hsDefect D (chiP D) (hhOf I D) n)
      =o[atTop] pw D
def StepV (I : AllFam) (D : ℕ) : Prop :=
  ∃ d : GDatum D, (∀ n, chi d.x d.m d.μ n = chiP D (2 * n)) ∧
    top I d.x d.m D = 2 ^ (D + 1) * hhOf I D ∧
    ∀ (A : Matrix (Ix d.κ) (Ix d.κ) ℚ) (e : Fin (D + 1) → Ix d.κ), IsInvMat A →
      IsProjFrame (matAct A d.x) e → projDeg (matAct A d.x) e = 2 ^ D
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry


