-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
-- name    : ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:41:58.102285+00:00
-- url     : https://prove2.me/theorems/1fa638f7-16c3-494b-8996-1c158bf49729
-- title:
--   Is Psh Locally Integrable Statement
-- statement:
--   Definitions and structural lemmas for Is Psh Locally Integrable Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/IsPshLocallyIntegrableStatement.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology
open scoped ContDiff
noncomputable section
variable {D : ℕ}
def IsPsh (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ) : Prop :=
  UpperSemicontinuousOn φ U ∧
    ∀ z w : Fin D → ℂ, (∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • w ∈ U) →
      CircleIntegrable (fun ζ : ℂ => φ (z + ζ • w)) 0 1 ∧
        φ z ≤ Real.circleAverage (fun ζ : ℂ => φ (z + ζ • w)) 0 1
def IsLeviPsh (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ) : Prop :=
  ContDiffOn ℝ 2 φ U ∧ ∀ z ∈ U, ∀ w : Fin D → ℂ, 0 ≤ levi φ z w
def IsPsh_iff_isLeviPshStatement : Prop :=
  ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ), IsOpen U → ContDiffOn ℝ 2 φ U →
    (IsPsh U φ ↔ IsLeviPsh U φ)
def IsPshInhabitStatement : Prop :=
  ∀ D : ℕ, IsPsh (Set.univ : Set (Fin D → ℂ)) (fun z => ∑ j, ‖z j‖ ^ 2) ∧
    IsPsh (Set.univ : Set (Fin D → ℂ)) (fun z => ‖z‖) ∧
    IsLeviPsh (Set.univ : Set (Fin D → ℂ)) (fun z => ∑ j, ‖z j‖ ^ 2) ∧
    ¬ IsPsh (Set.univ : Set (Fin (D + 1) → ℂ)) (fun z => -‖z 0‖ ^ 2)
def IsPsh_locallyIntegrableStatement : Prop :=
  ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ), IsOpen U → IsPsh U φ →
    LocallyIntegrableOn φ U volume
def IsPsh_supStatement : Prop :=
  ∀ (D : ℕ) (ι : Type) [Fintype ι] [Nonempty ι] (U : Set (Fin D → ℂ))
    (u : ι → (Fin D → ℂ) → ℝ), IsOpen U → (∀ j, IsPsh U (u j)) →
    IsPsh U (fun z => Finset.univ.sup' Finset.univ_nonempty (fun j => u j z))
def SubMeanPolydiscStatement : Prop :=
  ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (t : ℝ),
    IsOpen U → IsPsh U φ → 0 < t → closedBall z t ⊆ U →
    IntegrableOn φ (closedBall z t) volume ∧ φ z ≤ ⨍ x in closedBall z t, φ x
def coordDiv (S : Finset (Fin D)) : Set (Fin D → ℂ) :=
  {z | ∃ i ∈ S, z i = 0}
open Classical in

def limsupExt (U A : Set (Fin D → ℂ)) (v : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) : ℝ :=
  if z ∈ A then limsup v (𝓝[U \ A] z) else v z
def PshExtensionStatement : Prop :=
  ∀ (D : ℕ) (S : Finset (Fin D)) (U : Set (Fin D → ℂ)) (u : (Fin D → ℂ) → ℝ) (C : ℝ),
    IsOpen U → U ⊆ ball 0 1 → ContinuousOn u (U \ coordDiv S) → IsPsh (U \ coordDiv S) u →
    (∀ z ∈ U \ coordDiv S, u z ≤ C * Real.log (Real.exp 1 + ∑ i ∈ S, Real.log ‖z i‖⁻¹)) →
    (∀ K : Set (Fin D → ℂ), IsCompact K → K ⊆ U → BddAbove (u '' (K \ coordDiv S))) ∧
      ∀ κ : ℝ, IsPsh U (limsupExt U (coordDiv S) (fun z => max (u z) (-κ)))
def polyMax (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (t : ℝ) : ℝ :=
  sSup (φ '' closedBall z t)
def PolyMaxLogConvexStatement : Prop :=
  ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (R : ℝ),
    IsOpen U → IsPsh U φ → 0 < R → closedBall z R ⊆ U →
    ConvexOn ℝ (Set.Iic (Real.log R)) (fun s => polyMax φ z (Real.exp s)) ∧
      MonotoneOn (polyMax φ z) (Set.Ioc 0 R) ∧
      (∀ t, 0 ≤ t → t ≤ R → ∃ x ∈ closedBall z t, φ x = polyMax φ z t) ∧
      Tendsto (polyMax φ z) (𝓝[>] 0) (𝓝 (φ z))
structure Mollifier (D : ℕ) where

  toFun : (Fin D → ℂ) → ℝ
  contDiff : ContDiff ℝ ∞ toFun
  nonneg : ∀ w, 0 ≤ toFun w
  support_subset : Function.support toFun ⊆ ball 0 1
  integral_eq_one : ∫ w, toFun w = 1
  circle_inv : ∀ (c : ℂ) (w : Fin D → ℂ), ‖c‖ = 1 → toFun (c • w) = toFun w
def MollifierInhabitStatement : Prop := ∀ D : ℕ, Nonempty (Mollifier D)
def Mollifier.scaled (ρ : Mollifier D) (ε : ℝ) (w : Fin D → ℂ) : ℝ :=
  (ε ^ (2 * D))⁻¹ * ρ.toFun (ε⁻¹ • w)
def molli (ρ : Mollifier D) (ε : ℝ) (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) : ℝ :=
  ∫ w, ρ.scaled ε w * φ (z - w)
def shrink (U : Set (Fin D → ℂ)) (ε : ℝ) : Set (Fin D → ℂ) :=
  {z | closedBall z ε ⊆ U}
def MollifyStatement : Prop :=
  ∀ (D : ℕ) (ρ : Mollifier D) (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ),
    IsOpen U → IsPsh U φ →
    (∀ ε, 0 < ε → IsOpen (shrink U ε) ∧ ContDiffOn ℝ ∞ (molli ρ ε φ) (shrink U ε) ∧
        IsPsh (shrink U ε) (molli ρ ε φ) ∧
        ∀ z ∈ shrink U ε, φ z ≤ molli ρ ε φ z ∧ molli ρ ε φ z ≤ polyMax φ z ε) ∧
      (∀ z ∈ U, Tendsto (fun ε => molli ρ ε φ z) (𝓝[>] 0) (𝓝 (φ z)))
def MollifyLipStatement : Prop :=
  ∀ (D : ℕ) (ρ : Mollifier D) (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ) (L : NNReal),
    LipschitzOnWith L φ U → ∀ ε, 0 < ε → ∀ z ∈ shrink U ε, |molli ρ ε φ z - φ z| ≤ L * ε
def MollificationSecondOrder : Prop :=
  ∀ (D : ℕ) (ρ : Mollifier D) (U K : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ),
    IsOpen U → ContDiffOn ℝ 3 φ U → IsCompact K → K ⊆ U →
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ → ∀ z ∈ K, z ∈ shrink U ε ∧
      |molli ρ ε φ z - φ z| ≤ C * ε ∧
      ‖fderiv ℝ (molli ρ ε φ) z - fderiv ℝ φ z‖ ≤ C * ε ∧
      ‖fderiv ℝ (fderiv ℝ (molli ρ ε φ)) z - fderiv ℝ (fderiv ℝ φ) z‖ ≤ C * ε
def kθ : ℝ → ℝ :=
  (⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩ : ContDiffBump (0 : ℝ)).normed volume
def tmax {ι : Type*} [Fintype ι] [Nonempty ι] (t : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty t
def regMax {ι : Type*} [Fintype ι] [Nonempty ι] (η : ℝ) (t : ι → ℝ) : ℝ :=
  ∫ h : ι → ℝ, tmax (fun j => t j + η * h j) * ∏ j, kθ (h j)
def RegMaxStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] [DecidableEq ι],
    (∀ η : ℝ, 0 < η →
      ContDiff ℝ ∞ (regMax (ι := ι) η) ∧ ConvexOn ℝ Set.univ (regMax (ι := ι) η) ∧
      Monotone (regMax (ι := ι) η) ∧
      (∀ t : ι → ℝ, tmax t ≤ regMax η t ∧ regMax η t ≤ tmax t + η / 2) ∧
      (∀ (t : ι → ℝ) i, (∀ j, j ≠ i → t j + η ≤ t i) → regMax η t = t i) ∧
      (∀ (t : ι → ℝ) j k (s : ℝ), k ≠ j → t j + η ≤ t k → s + η ≤ t k →
        regMax η (Function.update t j s) = regMax η t) ∧
      (∀ (t : ι → ℝ) (c : ℝ), regMax η (fun j => t j + c) = regMax η t + c) ∧
      (∀ t : ι → ℝ, ∑ j, fderiv ℝ (regMax (ι := ι) η) t (Pi.single j 1) = 1)) ∧
    ∃ C : ℝ, ∀ η : ℝ, 0 < η → ∀ (t : ι → ℝ) (i j : ι),
      |fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) t (Pi.single i 1) (Pi.single j 1)| ≤ C / η
def RegMaxPshStatement : Prop :=
  ∀ (D : ℕ) (ι : Type) [Fintype ι] [Nonempty ι] (η : ℝ) (U : Set (Fin D → ℂ))
    (u : ι → (Fin D → ℂ) → ℝ), IsOpen U → 0 < η → (∀ j, IsPsh U (u j)) →
    IsPsh U (fun z => regMax η (fun j => u j z))
def RegMaxLeviStatement : Prop :=
  ∀ (D : ℕ) (ι : Type) [Fintype ι] [Nonempty ι] (η : ℝ) (U : Set (Fin D → ℂ))
    (u : ι → (Fin D → ℂ) → ℝ), IsOpen U → 0 < η → (∀ j, ContDiffOn ℝ 2 (u j) U) →
    ∀ z ∈ U, ∀ (w : Fin D → ℂ) (g : ℝ), (∀ j, g ≤ levi (u j) z w) →
      g ≤ levi (fun x => regMax η (fun j => u j x)) z w
end
end ReciprocityTheory.AnForm.A


