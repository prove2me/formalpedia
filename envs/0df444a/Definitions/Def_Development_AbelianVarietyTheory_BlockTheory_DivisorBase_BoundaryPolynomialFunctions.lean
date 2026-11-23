-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_BoundaryPolynomialFunctions
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_BoundaryPolynomialFunctions
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:47:17.736828+00:00
-- url     : https://prove2.me/theorems/a9095b21-1867-4d1f-8d55-77f52713a144
-- title:
--   Boundary Polynomial Functions
-- statement:
--   Definitions and structural lemmas for Boundary Polynomial Functions, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/BoundaryPolynomialFunctions.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal LinearAlgebra.Projectivization
noncomputable section
variable {d : ℕ} {X : Type} [TopologicalSpace X]
def IsProjective (A : FinHolAtlas d X) : Prop :=
  ∃ (N : ℕ) (F : X → ℙ ℂ (Fin (N + 1) → ℂ)), Function.Injective F ∧
    ∀ x, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ ∃ G : X → Fin (N + 1) → ℂ,
      (∀ i, A.HoloOn W fun y => G y i) ∧
      (∀ y ∈ W, ∃ h : G y ≠ 0, F y = Projectivization.mk ℂ (G y) h) ∧
      ∀ j, x ∈ (A.chart j).source → ∀ v : Fin d → ℂ,
        fderiv ℂ (G ∘ (A.chart j).symm) (A.chart j x) v ∈ Submodule.span ℂ {G x} → v = 0
def IsIrreducibleAnalytic (A : FinHolAtlas d X) (Z : Set X) : Prop :=
  A.IsAnalyticSubset Z ∧ Z.Nonempty ∧
    ∀ Z₁ Z₂, A.IsAnalyticSubset Z₁ → A.IsAnalyticSubset Z₂ → Z = Z₁ ∪ Z₂ → Z = Z₁ ∨ Z = Z₂
def IsIrreducibleComponent (A : FinHolAtlas d X) (S C : Set X) : Prop :=
  Maximal (fun C' => IsIrreducibleAnalytic A C' ∧ C' ⊆ S) C
def padZero (n d : ℕ) (z : Fin n → ℂ) : Fin d → ℂ :=
  fun k => if h : (k : ℕ) < n then z ⟨k, h⟩ else 0
def IsStraightening (A : FinHolAtlas d X) (Z : Set X) (n : ℕ)
    (ψ : OpenPartialHomeomorph X (Fin d → ℂ)) : Prop :=
  n ≤ d ∧ IsCompatChart A ψ ∧
    Z ∩ ψ.source = {y ∈ ψ.source | ∀ k : Fin d, n ≤ (k : ℕ) → ψ y k = 0}
def regularLocus (A : FinHolAtlas d X) (Z : Set X) (n : ℕ) : Set X :=
  {x ∈ Z | ∃ ψ, IsStraightening A Z n ψ ∧ x ∈ ψ.source}
def param (n : ℕ) (ψ : OpenPartialHomeomorph X (Fin d → ℂ)) (z : Fin n → ℂ) : X :=
  ψ.symm (padZero n d z)
def paramDens (n : ℕ) (Φ : LocPot X) (ψ : OpenPartialHomeomorph X (Fin d → ℂ))
    (z : Fin n → ℂ) : ℝ :=
  maDens (fun _ z' => Φ.φ (param n ψ z) (param n ψ z')) z
def IsPieceFamily (A : FinHolAtlas d X) (Z : Set X) (n : ℕ) (S : Set X) {k : ℕ}
    (ψ : Fin k → OpenPartialHomeomorph X (Fin d → ℂ)) (B : Fin k → Set (Fin n → ℂ)) : Prop :=
  (∀ j, IsStraightening A Z n (ψ j)) ∧ (∀ j, MeasurableSet (B j)) ∧
    (∀ j, ∀ z ∈ B j, padZero n d z ∈ (ψ j).target ∧ param n (ψ j) z ∈ S) ∧
    Pairwise fun i j => Disjoint (param n (ψ i) '' B i) (param n (ψ j) '' B j)
def regIntegral (A : FinHolAtlas d X) (Z : Set X) (n : ℕ) (Φ : LocPot X) (S : Set X)
    (f : X → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (k : ℕ) (ψ : Fin k → OpenPartialHomeomorph X (Fin d → ℂ)) (B : Fin k → Set (Fin n → ℂ))
    (_ : IsPieceFamily A Z n S ψ B),
    ∑ j, ∫⁻ z in B j, f (param n (ψ j) z) * ‖paramDens n Φ (ψ j) z‖ₑ
def normSec (L : LocPot X) (s : X → X → ℂ) (y : X) : ℝ :=
  ‖s y y‖ * Real.exp (-L.φ y y)
open scoped Classical in

def absLogNorm (L : LocPot X) (s : X → X → ℂ) (y : X) : ℝ≥0∞ :=
  if s y y = 0 then ∞ else ENNReal.ofReal |logNormSec L s y|
def boundary {m : ℕ} (σ : Fin m → X → X → ℂ) : Set X :=
  {y | ∃ i, σ i y y = 0}
def rFun (L : LocPot X) (σ : X → X → ℂ) (y : X) : ℝ :=
  Real.exp 1 - 2 * logNormSec L σ y
def pFun {m : ℕ} (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ) (c : ℝ) (y : X) : ℝ :=
  -c * ∑ i, Real.log (rFun (Λ i) (σ i) y)
def poincarePot {m : ℕ} (α : LocPot X) (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ)
    (c : ℝ) : LocPot X :=
  α + LocPot.ofFun fun y => pFun Λ σ c y / 2
def FormBoundedBy (A : FinHolAtlas d X) (α L : LocPot X) (K : ℝ) : Prop :=
  IsPsh A (α.rsmul K + L) ∧ IsPsh A (α.rsmul K + L.rsmul (-1))
def IsAdmissibleConst {m : ℕ} (A : FinHolAtlas d X) (α : LocPot X) (Λ : Fin m → LocPot X)
    (c : ℝ) : Prop :=
  0 < c ∧ ∃ K : Fin m → ℝ, (∀ i, 0 ≤ K i ∧ FormBoundedBy A α (Λ i) (K i)) ∧
    c * ∑ i, K i ≤ Real.exp 1 / 2
def IsBoundarySetting {m : ℕ} (A : FinHolAtlas d X) (α : LocPot X) (Λ : Fin m → LocPot X)
    (σ : Fin m → X → X → ℂ) (c : ℝ) : Prop :=
  IsPotential A α ∧ IsPosPot A α ∧
    (∀ i, IsPotential A (Λ i) ∧ IsSection A (Λ i) (σ i) ∧
      interior {y | σ i y y = 0} = ∅ ∧ ∀ y, normSec (Λ i) (σ i) y ≤ 1) ∧
    IsAdmissibleConst A α Λ c
def LogNormIntegrablePoincare : Prop :=
  ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas d X),
    IsProjective A →
  ∀ (m : ℕ) (α : LocPot X) (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ) (c : ℝ),
    IsBoundarySetting A α Λ σ c →
  ∀ (Z : Set X) (n : ℕ), IsIrreducibleAnalytic A Z → (regularLocus A Z n).Nonempty →
    ¬ Z ⊆ boundary σ →
  ∀ (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s →
    (∀ y, normSec L s y ≤ 1) →
    (∃ y ∈ Z, s y y ≠ 0) →
    (∀ C, IsIrreducibleComponent A (Z ∩ boundary σ) C → ∃ y ∈ C, s y y ≠ 0) →
    regIntegral A Z n (poincarePot α Λ σ c) (regularLocus A Z n \ boundary σ)
      (absLogNorm L s) < ∞
end
end GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions


