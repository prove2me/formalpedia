-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:43:00.669369+00:00
-- url     : https://prove2.me/theorems/e7120c29-fc2d-4600-8872-b8fd200098ed
-- title:
--   Statements Current
-- statement:
--   Definitions and structural lemmas for Statements Current, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
variable {n d : ℕ}
def IsSheetAt (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (x : Fin n → ℂ)
    (s : (Fin d → ℂ) → Fin n → ℂ) : Prop :=
  ∃ U : Set (Fin d → ℂ), IsOpen U ∧ A *ᵥ x ∈ U ∧ DifferentiableOn ℂ s U ∧ s (A *ᵥ x) = x ∧
    (∀ y ∈ U, A *ᵥ s y = y ∧ s y ∈ zeroSet J) ∧
    ∃ V ∈ 𝓝 x, ∀ x' ∈ zeroSet J ∩ V, A *ᵥ x' ∈ U → x' = s (A *ᵥ x')
open Classical in

def sheetSum (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (F : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) (y : Fin d → ℂ) : ℝ :=
  ∑ᶠ (x : Fin n → ℂ) (_ : x ∈ fibre J A y),
    if h : ∃ s, IsSheetAt J A x s then F x h.choose else 0
def chartDens (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) : ℝ :=
  sheetSum J A (fun x s => f x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) y
def chartAbsDens (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) : ℝ :=
  sheetSum J A (fun x s => |f x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y|) y
def chartInt (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) : ℝ :=
  ∫ y, chartDens J A f φ y
open Classical in

def varInt (J : Ideal (MvPolynomial (Fin n) ℂ)) (d : ℕ) (f : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) : ℝ :=
  if h : ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J A then chartInt J h.choose f φ else 0
def SmoothNear (S : Set (Fin n → ℂ)) (φ : (Fin n → ℂ) → ℝ) : Prop :=
  ∃ U : Set (Fin n → ℂ), IsOpen U ∧ S ⊆ U ∧ ContDiffOn ℝ ∞ φ U
def linEval (u x : Fin n → ℂ) : ℂ := ∑ j, u j * x j
def euclPot (x : Fin n → ℂ) : ℝ := ∑ j, ‖x j‖ ^ 2
def energyInt (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (B : Set (Fin n → ℂ)) (χ : (Fin n → ℂ) → ℝ) : ℝ :=
  chartInt J A (B.indicator fun _ => 1) (vecCons (fun x => χ x ^ 2 / 2) fun _ => euclPot) -
    chartInt J A (B.indicator χ) (vecCons χ fun _ => euclPot)
structure VarBranch (J : Ideal (MvPolynomial (Fin n) ℂ)) (k : ℕ) (p : Fin n → ℂ) where

  radius : ℝ
  radius_pos : 0 < radius

  toFun : (Fin k → ℂ) → Fin n → ℂ
  differentiableOn : DifferentiableOn ℂ toFun (Metric.ball 0 radius)
  injOn : Set.InjOn toFun (Metric.ball 0 radius)
  map_zero : toFun 0 = p
  mapsTo : Set.MapsTo toFun (Metric.ball 0 radius) (zeroSet J)
def VarBranch.image {J : Ideal (MvPolynomial (Fin n) ℂ)} {k : ℕ} {p : Fin n → ℂ}
    (b : VarBranch J k p) : Set (Fin n → ℂ) :=
  b.toFun '' Metric.ball 0 b.radius
def VarBranch.slice {J : Ideal (MvPolynomial (Fin n) ℂ)} {k : ℕ} {p : Fin n → ℂ}
    (b : VarBranch J (k + 1) p) : Set (Fin n → ℂ) :=
  b.toFun '' (Metric.ball 0 b.radius ∩ {t | t 0 = 0})
def VanishesToOrder {k : ℕ} (F : (Fin (k + 1) → ℂ) → ℂ) (r : ℝ) (m : ℕ) : Prop :=
  ∃ H : (Fin (k + 1) → ℂ) → ℂ, DifferentiableOn ℂ H (Metric.ball 0 r) ∧
    (∀ t ∈ Metric.ball 0 r, H t ≠ 0) ∧ ∀ t ∈ Metric.ball 0 r, F t = t 0 ^ m * H t
def IntegralIndep.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A A' : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    IsFiniteProjection J A' → Measurable f →
    (∀ k, SmoothNear (zeroSet J) (φ k)) → Integrable (chartAbsDens J A f φ) →
      Integrable (chartAbsDens J A' f φ) ∧ chartInt J A f φ = chartInt J A' f φ
def PointIntegral.Statement : Prop :=
  ∀ (n : ℕ) (p : Fin n → ℂ) (f : (Fin n → ℂ) → ℝ) (φ : Fin 0 → (Fin n → ℂ) → ℝ),
    varInt (RingHom.ker (MvPolynomial.eval p)) 0 f φ = f p
def LineSliceMass.Statement : Prop :=
  varInt (Ideal.span {X 0 - 1} : Ideal (MvPolynomial (Fin 2) ℂ)) 1 (fun _ => 1)
    (fun _ x => Real.log ((HermNorm.std 2).dualNorm x)) = 1
def CutOff.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    P ≠ 0 →
      ∃ χ : ℕ → (Fin n → ℂ) → ℝ,
        (∀ k, ContDiff ℝ ∞ (χ k)) ∧ (∀ k x, χ k x ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ k, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ {x | eval (A *ᵥ x) P = 0} ⊆ U ∧
          ∀ x ∈ U ∩ zeroSet J, χ k x = 0) ∧
        (∀ x ∈ zeroSet J, eval (A *ᵥ x) P ≠ 0 → Tendsto (fun k => χ k x) atTop (𝓝 1)) ∧
        (∀ R : ℝ, Tendsto (fun k => energyInt J A (Metric.closedBall 0 R) (χ k)) atTop (𝓝 0)) ∧
        (∀ (R : ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ), (∀ i, SmoothNear (zeroSet J) (φ i)) →
          Tendsto (fun k => ∫ y, chartAbsDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
            (vecCons (χ k) φ) y) atTop (𝓝 0))
def StokesOnVariety.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (f g : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) →
    SmoothNear (zeroSet J) f → SmoothNear (zeroSet J) g →
    (∀ i, SmoothNear (zeroSet J) (φ i)) → (HasCompactSupport f ∨ HasCompactSupport g) →
      varInt J (d + 1) f (vecCons g φ) = varInt J (d + 1) g (vecCons f φ)
def LogIntegrable.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (u : Fin n → ℂ) (φ : Fin d → (Fin n → ℂ) → ℝ) (R : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    linForm u ∉ J → (∀ i, SmoothNear (zeroSet J) (φ i)) →
      Integrable (chartAbsDens J A
        ((Metric.closedBall 0 R).indicator fun x => Real.log ‖linEval u x‖) φ)
def LocalOrder.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u p : Fin n → ℂ) (m : ℕ)
    (γ : Fin m → VarBranch J (d + 1) p) (ord : Fin m → ℕ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes → p ∈ zeroSet W →
    (∃ N ∈ 𝓝 p, zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) →
    (∃ N ∈ 𝓝 p, ∀ b, zeroSet W ∩ N ⊆ (γ b).slice) →
    (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | linEval u x = 0}) →
    (∀ b, VanishesToOrder (fun t => linEval u ((γ b).toFun t)) (γ b).radius (ord b)) →
      localMult (J ⊔ Ideal.span {linForm u}) W = ∑ b, ord b
def PoincareLelong.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (f : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    ContDiff ℝ ∞ f → HasCompactSupport f → (∀ i, SmoothNear (zeroSet J) (φ i)) →
      varInt J (d + 1) (fun x => Real.log ‖linEval u x‖) (vecCons f φ) =
        ∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
          (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d f φ
def ConeToProjective.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (ℓ : Fin n → ℂ) (g : (Fin n → ℂ) → ℝ),
    IsProjPrime J → IsChowForm J (e + 1) F → linForm ℓ ∉ J →
    (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → g (t • x) = g x) → ContinuousOn g {x | x ≠ 0} →
      coneIntegral h J e g =
        varInt (J ⊔ Ideal.span {linForm ℓ - 1}) e g (fun _ x => Real.log (h.dualNorm x))
def GreenFromLelong.Statement : Prop :=
  IntegralIndep.Statement → CutOff.Statement → StokesOnVariety.Statement →
    LogIntegrable.Statement → PoincareLelong.Statement → ConeToProjective.Statement →
      GreenSymmetry.Statement
def MassFromLelong.Statement : Prop :=
  IntegralIndep.Statement → CutOff.Statement → StokesOnVariety.Statement →
    LogIntegrable.Statement → PoincareLelong.Statement → ConeToProjective.Statement →
      ChowFormSection.Statement → ConeIntegralMass.Statement
section Inhabitants
def lineBranch : VarBranch (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1 0 where
  radius := 1
  radius_pos := one_pos
  toFun := id
  differentiableOn := differentiableOn_id
  injOn := Set.injOn_id _
  map_zero := rfl
  mapsTo := fun _ _ q hq => by
    rw [Ideal.mem_bot] at hq
    simp [hq]
end Inhabitants
end
end GroundTheory.Heights₂.Heights


