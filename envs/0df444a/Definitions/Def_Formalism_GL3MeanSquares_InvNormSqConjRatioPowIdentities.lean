-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_InvNormSqConjRatioPowIdentities
-- name    : Formalism_GL3MeanSquares_InvNormSqConjRatioPowIdentities
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:32.875803+00:00
-- url     : https://prove2.me/theorems/70efb7c1-4883-417b-a5af-1f7e79966c6b
-- title:
--   Inv Norm Sq Conj Ratio Pow Identities
-- statement:
--   Definitions and structural lemmas for Inv Norm Sq Conj Ratio Pow Identities, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/InvNormSqConjRatioPowIdentities.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Formalism_GL3MeanSquares_ModelCocycleExponent
import Definitions.Def_Formalism_GL3MeanSquares_InverseNormLeOfIntegerInner
import Definitions.Def_Formalism_GL3MeanSquares_QuadraticFormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_RationalMatrixPrimeOrderBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology ArithmeticFunction
noncomputable section
namespace Formalism.HermitianLattices.GlobalBoundRefinements
open Formalism.HermitianLattices.GL2PrimeSums in

def ShortIntervalLowerBound : Prop :=
  ∀ C₀ Cr cr cb : ℝ, 0 < C₀ → 0 < Cr → 0 < cr → 0 < cb →
    ∃ C₀' c : ℝ, C₀ ≤ C₀' ∧ 0 < c ∧
      ∀ (B G β : ℝ) (θ : ℤ) (π₁ π₂ : ℝ → ℕ) (η' : ℝ → ℝ),
        4 ≤ B → 1 ≤ G → G ≤ B → θ ∈ ({-1, 0, 1} : Set ℤ) →
        (θ ≠ 0 → 1 / 2 ≤ β ∧ β < 1 ∧ cb / (B ^ 2 * Real.log B) ≤ 1 - β) →
        (∀ Y : ℝ, 1 ≤ Y → (π₂ Y : ℝ) ≤ 2 * Real.sqrt Y) →
        (∀ Y : ℝ, 0 ≤ η' Y ∧ η' Y ≤ 3 * Real.log B) →
        (∀ Y : ℝ, B ^ C₀ ≤ Y →
          |G * ((π₁ Y : ℝ) + π₂ Y + η' Y) - Emain θ β Y| ≤ rhoErr Cr cr B Y * Emain θ β Y) →
        ∀ X : ℝ, B ^ C₀' ≤ X →
          c * B ^ (-5 : ℝ) * X / Real.log X ≤ Emain θ β X ∧
          ∀ h : ℝ, h ≤ 1 → rhoErr Cr cr B X ≤ h / 100 → B ^ (7 : ℝ) ≤ h * X ^ ((1 : ℝ) / 3) →
            c * h * B ^ (-6 : ℝ) * X / Real.log X ≤ (π₁ (X * (1 + h)) : ℝ) - π₁ X
open Formalism.HermitianLattices.GL2PrimeSums in

def PrimeDivisorCountAbsorption : Prop :=
  ∀ C₀ Cr cr cb : ℝ, 0 < C₀ → 0 < Cr → 0 < cr → 0 < cb →
    ∃ C₀' : ℝ, C₀ ≤ C₀' ∧
      ∀ (B G β : ℝ) (θ : ℤ) (P η' : ℝ → ℝ),
        4 ≤ B → 1 ≤ G → G ≤ B → θ ∈ ({-1, 0, 1} : Set ℤ) →
        (θ ≠ 0 → 1 / 2 ≤ β ∧ β < 1 ∧ cb / (B ^ 2 * Real.log B) ≤ 1 - β) →
        (∀ Y : ℝ, 0 ≤ η' Y ∧ η' Y ≤ 3 * Real.log B) →
        (∀ Y : ℝ, B ^ C₀ ≤ Y →
          |G * (P Y + η' Y) - Emain θ β Y| ≤ rhoErr Cr cr B Y * Emain θ β Y) →
        ∀ Y : ℝ, B ^ C₀' ≤ Y →
          |G * P Y - Emain θ β Y| ≤ rhoErr (2 * Cr) cr B Y * Emain θ β Y
open Formalism.HermitianLattices.GL2PrimeSums in

def PrimeCountAsymptoticInProgressions (C₀ Cr cr cb : ℝ) : Prop :=
  ∀ m a : ℕ, 3 ≤ m → Nat.Coprime a m → ∃ (θ : ℤ) (β : ℝ) (η' : ℝ → ℝ), θ ∈ ({-1, 0, 1} : Set ℤ) ∧
    (θ ≠ 0 → 1 / 2 ≤ β ∧ β < 1 ∧ cb / ((4 * (m : ℝ)) ^ 2 * Real.log (4 * m)) ≤ 1 - β) ∧
    (∀ Y : ℝ, 0 ≤ η' Y ∧ η' Y ≤ 3 * Real.log (4 * m)) ∧
    ∀ Y : ℝ, (4 * (m : ℝ)) ^ C₀ ≤ Y →
      |(m.totient : ℝ) * ((((Icc 1 ⌊Y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD m])).card : ℝ) + η' Y) - Emain θ β Y|
        ≤ rhoErr Cr cr (4 * m) Y * Emain θ β Y
open Formalism.HermitianLattices.GL2PrimeSums in

def ShortIntervalImpliesProgressions : Prop :=
  ShortIntervalLowerBound → ∀ C₀ Cr cr cb : ℝ, 0 < C₀ → 0 < Cr → 0 < cr → 0 < cb → PrimeCountAsymptoticInProgressions C₀ Cr cr cb →
    ∃ C₀' c : ℝ, 0 < C₀' ∧ 0 < c ∧ PrimesAPInterval C₀' Cr cr c
open Formalism.HermitianLattices.GL2PrimeSums in

def LipschitzWeightedSums : Prop :=
  (∀ (a : ℕ → ℂ) (S : ℂ), (∀ y : ℝ, 0 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, ‖a n‖ ≤ 2 * y) →
    ∀ A w₀ w₁ w₂ : ℝ, 0 < w₀ → w₀ ≤ w₁ → w₁ ≤ w₂ → w₂ ≤ A →
      ‖(w₂ : ℂ) * Gchi a S (A / w₂) - (w₁ : ℂ) * Gchi a S (A / w₁)‖ ≤ 3 * A / w₀ * (w₂ - w₁)) ∧
  (∀ a : ℕ → ℝ, (∀ n, 0 ≤ a n) → (∀ y : ℝ, 0 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, a n ≤ 2 * y) →
    ∀ A w₀ w₁ w₂ : ℝ, 0 < w₀ → w₀ ≤ w₁ → w₁ ≤ w₂ → w₂ ≤ A →
      |w₂ * Gone a (A / w₂) - w₁ * Gone a (A / w₁)| ≤ 3 * A / w₀ * (w₂ - w₁))
def ParallelogramMax : Prop :=
  ∀ (T : Type) [AddCommGroup T] [Fintype T] (M₀ m : T → ℝ),
    (∀ P Q, Q ≠ 0 → M₀ (P + Q) + M₀ (P - Q) - 2 * M₀ P = 2 * m Q) → M₀ 0 = 0 →
    (∀ Q, Q ≠ 0 → m Q = 0) ∧ ∀ P, M₀ P = 0
open Classical in

def BRValuation : Prop :=
  ∀ (Emb : Type) [Fintype Emb] (φ c : Equiv.Perm Emb) (κ : Emb → ZMod 2) (τ₀ : Emb),
    Disjoint (univ.filter (fun τ => φ.SameCycle τ₀ τ))
      ((univ.filter (fun τ => φ.SameCycle τ₀ τ)).image c) →
    ∀ (i : ℤ) (val s' : Emb → ℤ),
      (∀ τ ∈ univ.filter (fun τ => φ.SameCycle τ₀ τ), val τ = i) →
      (∀ τ ∈ (univ.filter (fun τ => φ.SameCycle τ₀ τ)).image c, val τ = -i) →
      (∀ τ, τ ∉ univ.filter (fun τ => φ.SameCycle τ₀ τ) →
        τ ∉ (univ.filter (fun τ => φ.SameCycle τ₀ τ)).image c → val τ = 0) →
      ∑ τ ∈ univ.filter (fun τ => κ τ = 0), -(s' τ) * val τ =
        -i * (∑ τ ∈ (univ.filter (fun τ => φ.SameCycle τ₀ τ)).filter (fun τ => κ τ = 0), s' τ -
          ∑ τ ∈ ((univ.filter (fun τ => φ.SameCycle τ₀ τ)).image c).filter (fun τ => κ τ = 0), s' τ)
def Ms_min : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], NumberField.IsTotallyComplex K →
    ∀ x : NumberField.RingOfIntegers K, x ≠ 0 →
    (Fintype.card (NumberField.InfinitePlace K) : ℝ) ≤ ∑ w : NumberField.InfinitePlace K, (w (x : K)) ^ 2
open Formalism.LogVandermondeBounds.StandardLattice in

def LogLFunctionEulerBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ M : ℕ, 2 ≤ M →
    Multipliable (fun P : {P : Ideal (NumberField.RingOfIntegers K) // P.IsMaximal} =>
      Formalism.HermitianLatticesTheory.eulerFac K M P.1) ∧
    0 < Formalism.HermitianLatticesTheory.lValEta K M ∧
    |Real.log (Formalism.HermitianLatticesTheory.lValEta K M)| ≤ (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * Real.log (zetaR M)
def RankThresholdInequalityEventually : Prop :=
  ∀ (C L : ℝ) (f m k : ℕ), 0 ≤ C → 1 ≤ L → 1 ≤ f → 2 ≤ m → Even m → m ≤ k →
    let r := k + m - 1
    let p := k + m / 2 - 1
    let q := m / 2
    Real.exp (-(r : ℝ)) ≤ 1 / 3 ∧ p + q = r ∧ min p q = q ∧
    C * (q : ℝ) * ((p * q : ℕ) : ℝ) ^ 3 * r * Real.log r / (1 / 3 : ℝ) ^ 2 ≤ 9 * C * (r : ℝ) ^ 19 * (f : ℝ) ^ 5 * L
def RankMulPowThreeHalvesLeFourthPower : Prop :=
  ∀ (f m k : ℕ) (L : ℝ), 2 ≤ m → 1 ≤ f → 1 ≤ k → 1 ≤ L →
    120 * ((k + m - 1 : ℕ) : ℝ) * ((m / 2 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤
      120 * ((k + m - 1 : ℕ) : ℝ) ^ 19 * (f : ℝ) ^ 5 * L
def DimensionMassJointBound : Prop :=
  ∀ (f : ℕ) (Dstar massr Isig : ℝ) (dsig dimV : ℕ → ℝ),
    0 < massr → 0 < Isig → (∀ ρ, ρ < f → 0 ≤ dimV ρ) →
    (h3 : ∀ ρ, ρ < f → (1 - 1 / 3) * dimV ρ ≤ dsig ρ) →
    (hD : Dstar = massr * Isig * ∏ ρ ∈ range f, dsig ρ) →
    (2 / 3 : ℝ) ^ f * massr * Isig * ∏ ρ ∈ range f, dimV ρ ≤ Dstar
def DiscriminantTermBound : Prop :=
  ∀ (k m : ℕ) (L vE : ℝ), 1 ≤ m → m ≤ k → Real.pi ≤ vE → Real.log vE ≤ L →
    -((L + Real.log 2) / 2) ≤ -(((m : ℝ) - 1) / (2 * k)) * Real.log (2 * vE) ∧
    -(((m : ℝ) - 1) / (2 * k)) * Real.log (2 * vE) ≤ 0
def TableauExponentRange : Prop :=
  ∀ (μ : YoungDiagram) (T : SemistandardYoungTableau μ) (j : ℕ) (last first s nu1 : ℤ),
    first = last + μ.rowLen 0 → nu1 = first + s → 0 ≤ s → 0 ≤ nu1 →
    last ≤ last + ((μ.cells.filter (fun c => T c.1 c.2 = j)).card : ℤ) ∧
    last + ((μ.cells.filter (fun c => T c.1 c.2 = j)).card : ℤ) ≤ first ∧ max first 0 ≤ nu1
def IndicatorKernelSum : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (n n' : ℕ) (fW : Fin n' → ℤ) (x0 : Fin n → ℤ)
    (x : Matrix (Fin n') (Fin n) ℚ),
    (fun j => (x0 j : ZMod q)) ≠ 0 →
    let e1 : Fin n → ℚ := fun j => (x0 j : ℚ) / q
    let intMat : Prop := ∀ i j, x i j ∈ Set.range (Int.cast : ℤ → ℚ)
    let rhs : Prop := intMat ∧ ∃ z : ℤ,
      (∑ i, (fW i : ℚ) * (x.mulVec (fun j => (x0 j : ℚ))) i) = z ∧ (z : ZMod q) = 1
    let UKcond : (Fin n' → ZMod q) → Prop := fun xW =>
      (∑ i, (fW i : ZMod q) * xW i) = 1 ∧ intMat ∧
      (∀ i, (x.mulVec e1) i - ((xW i).val : ℚ) / q ∈ Set.range (Int.cast : ℤ → ℚ))
    let KUcond : (Fin n → ZMod q) → Prop := fun f =>
      (∑ j, f j * (x0 j : ZMod q)) = 1 ∧ intMat ∧
      (∀ j, ∃ z : ℤ, (∑ i, (fW i : ℚ) * x i j) = z ∧ (z : ZMod q) = f j)
    (rhs → Nat.card {xW // UKcond xW} = 1 ∧ Nat.card {f // KUcond f} = 1) ∧
    (¬ rhs → Nat.card {xW // UKcond xW} = 0 ∧ Nat.card {f // KUcond f} = 0)
def CharactersCancelScalar : Prop :=
  ∀ (A H : Type) [CommGroup A] [CommGroup H] (χ m : A →* H) (M M' g : ℤ) (ϖ : A), M' - M = g →
    ((m * χ ^ (-M')) ϖ * (m⁻¹ * χ ^ M) ϖ)⁻¹ = χ ϖ ^ g ∧
    χ ϖ ^ (-g) * ((m * χ ^ (-M')) ϖ * (m⁻¹ * χ ^ M) ϖ)⁻¹ = 1
def TriangularSumExponentBound : Prop :=
  ∀ (m nT : ℕ) (t f N sumW e1 : ℝ), e1 ≤ 2 * sumW + f * N →
    (m : ℝ) * e1 + nT * ((t + 1) / 2) * ((m : ℝ) * (m + 1) / 2) ≤
      ∑ _j ∈ range m, (2 * sumW + f * N + nT * (t + 1) * ((m : ℝ) + 1) / 4)
def ExponentBudgetLogBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (W : ι → ℝ) (nT m t : ℕ) (N b L logT C₀ : ℝ),
    (∀ τ, 0 ≤ W τ ∧ W τ ≤ 2 * b) → nT ≤ Fintype.card ι → 1 ≤ m → 1 ≤ t → 0 ≤ N → N ≤ b → (t : ℝ) * m ≤ b →
    0 ≤ logT → logT ≤ C₀ * m * L →
    0 ≤ (2 * ∑ τ, W τ + Fintype.card ι * N + nT * ((t : ℝ) + 1) * ((m : ℝ) + 1) / 4) * logT ∧
    (2 * ∑ τ, W τ + Fintype.card ι * N + nT * ((t : ℝ) + 1) * ((m : ℝ) + 1) / 4) * logT ≤
      6 * C₀ * Fintype.card ι * b * m * L
def InvNormSqConjRatioPowIdentities : Prop :=
  ∀ (z : ℂ) (g : ℕ), z ≠ 0 →
    ‖(((Complex.normSq z : ℝ) : ℂ) ^ g)⁻¹ * (z / (starRingEnd ℂ) z) ^ g‖ = ((Complex.normSq z) ^ g)⁻¹ ∧
    (((Complex.normSq z : ℝ) : ℂ) ^ g)⁻¹ * (z / (starRingEnd ℂ) z) ^ g = (((starRingEnd ℂ) z) ^ (2 * g))⁻¹ ∧
    (((Complex.normSq z : ℝ) : ℂ) ^ g)⁻¹ * ((starRingEnd ℂ) z / z) ^ g = (z ^ (2 * g))⁻¹
end Formalism.HermitianLattices.GlobalBoundRefinements


