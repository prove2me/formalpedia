-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMDefs
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:51.112435+00:00
-- url     : https://prove2.me/theorems/00b84f8a-26b3-43d4-afb2-e8e40b477bb5
-- title:
--   AMDefs
-- statement:
--   Definitions and structural lemmas for AMDefs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AMDefs.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def torusAct (c : K → ℂ) (z : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun p => c p.1 * z p
def IsTorusInv (g : ((Σ k, ι k) → ℂ) → ℝ) : Prop :=
  ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (torusAct c z) = g z
structure ChartSys (P : Ideal (MRing ι)) (D : ℕ) (μ : Measure ((Σ k, ι k) → ℂ)) where

  N : ℕ

  U : Fin N → Set (Fin D → ℂ)

  C : Fin N → Set (Fin D → ℂ)

  γ : Fin N → (Fin D → ℂ) → (Σ k, ι k) → ℂ

  ν : Fin N → (Fin D → ℂ) → ℝ
  isOpen_U : ∀ a, IsOpen (U a)
  isCompact_C : ∀ a, IsCompact (C a)
  C_subset : ∀ a, C a ⊆ U a
  analytic : ∀ a, AnalyticOnNhd ℂ (γ a) (U a)
  mem : ∀ a, ∀ y ∈ U a, γ a y ∈ mcPts P
  contDiff_ν : ∀ a, ContDiffOn ℝ 1 (ν a) (U a)
  ν_pos : ∀ a, ∀ y ∈ U a, 0 < ν a y
  le : ∀ (a : Fin N) (g : ((Σ k, ι k) → ℂ) → ℝ), Measurable g → IsTorusInv g → (∀ z, 0 ≤ g z) →
    ∫⁻ y in U a, ENNReal.ofReal (g (γ a y) * ν a y) ≤ ∫⁻ z, ENNReal.ofReal (g z) ∂μ
  cover : ∀ᵐ z ∂μ, ∃ a, ∃ y ∈ C a, ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusAct c (γ a y)
  dense : mcPts P ⊆ closure {z | ∃ a, ∃ y ∈ C a, ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusAct c (γ a y)}
def unitDeg [DecidableEq K] (k₀ : K) : K → ℤ := fun k => if k = k₀ then 1 else 0
def blockDeg [DecidableEq K] (k₀ : K) (n : ℕ) : K → ℕ := fun k => if k = k₀ then n else 0
variable {Ω : Type} [Field Ω] [CharZero Ω]
def IsSecBasisM [DecidableEq K] (y : (Σ k, ι k) → Ω) (k₀ : K) (n : ℕ) {r : ℕ}
    (b : Fin r → MvPolynomial (Σ k, ι k) ℚ) : Prop :=
  (∀ j, ∃ f : MRing ι, IsMultiHomog f (blockDeg k₀ n) ∧ b j = map (Int.castRingHom ℚ) f) ∧
    LinearIndependent ℤ (fun j => aeval y (b j)) ∧
    (Submodule.span ℤ (Set.range fun j => aeval y (b j))).toAddSubgroup = secM y (blockDeg k₀ n)
def wgtH (A : HermLine ι) (n : ℕ) (z : (Σ k, ι k) → ℂ) : ℝ :=
  (A.h z ^ (2 * n))⁻¹
open Classical in

def chiM [DecidableEq K] (y : (Σ k, ι k) → Ω) (k₀ : K) (A : HermLine ι)
    (μ : Measure ((Σ k, ι k) → ℂ)) (n : ℕ) : ℝ :=
  if h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Σ k, ι k) ℚ), IsSecBasisM y k₀ n p.2 then
    -(1 / 2) * Real.log (bGram μ (fun j => secFun (h.choose.2 j)) (wgtH A n)).det.re
  else 0
def IsPshAlong {P : Ideal (MRing ι)} {D : ℕ} {μ : Measure ((Σ k, ι k) → ℂ)} (S : ChartSys P D μ)
    (A : HermLine ι) : Prop :=
  ∀ a, ∀ y ∈ S.U a, ∀ w, 0 ≤ leviForm (fun y' => Real.log (A.h (S.γ a y'))) y w
def IsBergDensityM {P : Ideal (MRing ι)} {D : ℕ} {μ : Measure ((Σ k, ι k) → ℂ)}
    (S : ChartSys P D μ) (A : HermLine ι) (β : ((Σ k, ι k) → ℂ) → ℝ) : Prop :=
  IsTorusInv β ∧ ∀ᵐ z ∂μ, ∃ a, ∃ y ∈ S.C a, (∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusAct c (S.γ a y)) ∧
    β z * ((D.factorial : ℝ) * S.ν a y) =
      maDensity (fun _ : Fin D => fun y' => Real.log (A.h (S.γ a y'))) y
def IsBridged {P : Ideal (MRing ι)} {D : ℕ} {μ : Measure ((Σ k, ι k) → ℂ)} (S : ChartSys P D μ) :
    Prop :=
  ∀ (A : HermLine ι) (β g : ((Σ k, ι k) → ℂ) → ℝ) (B : ℝ), IsSmoothHerm A → IsPshAlong S A →
    IsBergDensityM S A β → Measurable β → Measurable g → IsTorusInv g → (∀ z, |g z| ≤ B) →
    ∫ z, g z * β z ∂μ = ptsIntegral (e := D) P (fun _ z => Real.log (A.h z)) g / (D.factorial : ℝ)
structure IsGoodM [DecidableEq K] (D : ℕ) (y : (Σ k, ι k) → Ω) (k₀ : K) (A : HermLine ι)
    (μ : Measure ((Σ k, ι k) → ℂ)) (S : ChartSys (mCoordIdeal y) D μ) : Prop where
  arith : IsArithVar (mCoordIdeal y) (D + 1)
  deg : A.a = unitDeg k₀
  smooth : IsSmoothHerm A
  psh : IsPshAlong S A
  conjA : IsConjInvariantH A
  conjMu : μ.map (fun z p => starRingEnd ℂ (z p)) = μ
  prob : IsProbabilityMeasure μ
  carried : μ (mcPts (mCoordIdeal y))ᶜ = 0

  rank : ∀ ε > 0, ∀ᶠ n : ℕ in Filter.atTop,
    (geomDeg (mCoordIdeal y) A D / (D.factorial : ℝ) - ε) * (n : ℝ) ^ D ≤
      (Module.finrank ℤ (secM y (blockDeg k₀ n)) : ℝ)
def defectM [DecidableEq K] (I : AllFam) (D : ℕ) (y : (Σ k, ι k) → Ω) (k₀ : K) (A : HermLine ι)
    (μ : Measure ((Σ k, ι k) → ℂ)) : ℕ → ℝ :=
  hsDefect D (chiM y k₀ A μ) (I K ι (mCoordIdeal y) (D + 1) fun _ => A)
def StepAM (I : AllFam) (D : ℕ) : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (A₀ A₁ : HermLine ι)
    (μ : Measure ((Σ k, ι k) → ℂ)) (S : ChartSys (mCoordIdeal y) D μ),
    IsBridged S → IsGoodM D y k₀ A₀ μ S → IsGoodM D y k₀ A₁ μ S →
    (fun n => defectM I D y k₀ A₁ μ n - defectM I D y k₀ A₀ μ n) =o[Filter.atTop] pw D
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry


