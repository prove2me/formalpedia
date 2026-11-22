-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
-- name    : Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:05:29.449323+00:00
-- url     : https://prove2.me/theorems/d92fbf58-ad37-4269-8056-e80b37569048
-- title:
--   Landau Zero Free Criterion
-- statement:
--   Definitions and structural lemmas for Landau Zero Free Criterion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauZeroFreeCriterion.lean

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_CharFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace Deduction
def gm (F : CharFamily) (u : ℝ) : ℝ := Gm F (Real.exp u)
def zeroSet (F : CharFamily) : Set ℂ :=
  {ρ | 0 < ρ.re ∧ ∃ i, DirichletCharacter.LFunction (F.χ i) ρ = 0 ∨
    DirichletCharacter.LFunction (F.χ i) ((starRingEnd ℂ) ρ) = 0}
structure PoleData (g : ℝ → ℝ) (Φ : ℂ → ℂ) (Z : Set ℂ) : Prop where
  meas : Measurable g
  growth : ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → |g u| ≤ C * Real.exp (2 * u)
  laplace : ∀ s : ℂ, 2 < s.re → Φ s = ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-s * u)
  pos : ∀ ρ ∈ Z, 0 < ρ.re
  diff : DifferentiableOn ℂ Φ ({s : ℂ | 0 < s.re} \ Z)
  iso : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z
  pole : ∀ ρ ∈ Z, ∃ c : ℂ, c ≠ 0 ∧ (ρ.im = 0 → 0 < c.re ∧ c.im = 0) ∧
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧ ∀ᶠ s in 𝓝[≠] ρ, Φ s = c / (s - ρ) + h s
def WindowHypU (g : ℝ → ℝ) (θ δ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧ ∃ R : ℝ → ℝ,
    IntegrableOn (fun u => R u * Real.exp (-θ * u)) (Icc U ((1 + δ) * U)) ∧
    (∀ u ∈ Icc U ((1 + δ) * U), 0 ≤ R u ∧ g u ≤ R u) ∧
    ∫ u in Icc U ((1 + δ) * U), R u * Real.exp (-θ * u) ≤ Real.exp (η * U)
open Classical in

def famD (q : ℕ) [NeZero q] (S : Finset (DirichletCharacter ℂ q)) (w : ℝ) (hw : 0 < w) : CharFamily where
  ι := Option {ξ : DirichletCharacter ℂ q // ξ ∈ S ∧ ξ ≠ 1}
  N := fun i => match i with
    | none => 1
    | some _ => q
  nz := fun i => by cases i <;> infer_instance
  χ := fun i => match i with
    | none => (1 : DirichletCharacter ℂ 1)
    | some ξ => ξ.1
  a := fun i => match i with
    | none => 1
    | some _ => w
  a_pos := fun i => by cases i <;> simp [hw]
  adm := fun i => by
    cases i with
    | none => exact Or.inl rfl
    | some ξ => exact Or.inr ξ.2.2
open Classical in

def GmLevel (j : ℕ) (y : ℝ) : ℝ :=
  G y + (3 * (2 : ℝ) ^ j + 1)⁻¹ *
    ∑ ξ ∈ Finset.univ.filter (fun ξ : DirichletCharacter ℂ (2 ^ (j + 2)) => ξ.Even ∧ ξ ≠ 1), (Gchi ξ y).re
def ZeroFreeAbove (j : ℕ) (θ : ℝ) : Prop :=
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 ∧
    ∀ ξ : DirichletCharacter ℂ (2 ^ (j + 2)), ξ.Even → ξ ≠ 1 → DirichletCharacter.LFunction ξ s ≠ 0
def LandauZeroFreeCriterion (j : ℕ) : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ y0 : ℝ, (∀ y ≥ y0, GmLevel j y ≤ y ^ θ) → ZeroFreeAbove j θ
end Deduction
end


