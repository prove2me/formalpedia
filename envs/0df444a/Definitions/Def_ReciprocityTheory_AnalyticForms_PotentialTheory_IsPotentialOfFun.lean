-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:34.893723+00:00
-- url     : https://prove2.me/theorems/be1c77de-0965-4acf-a9a7-c246662a65a7
-- title:
--   Is Potential Of Fun
-- statement:
--   Definitions and structural lemmas for Is Potential Of Fun, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IsPotentialOfFun.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.M
open MeasureTheory
open scoped ContDiff
noncomputable section
structure FinHolAtlas (e : ℕ) (X : Type*) [TopologicalSpace X] where

  n : ℕ

  chart : Fin n → OpenPartialHomeomorph X (Fin e → ℂ)

  cover : ∀ x, ∃ j, x ∈ (chart j).source

  holo : ∀ j k, AnalyticOnNhd ℂ (chart k ∘ (chart j).symm)
    ((chart j).target ∩ (chart j).symm ⁻¹' (chart k).source)
namespace FinHolAtlas
variable {e : ℕ} {X : Type*} [TopologicalSpace X]
def SmoothOn (A : FinHolAtlas e X) (U : Set X) (f : X → ℝ) : Prop :=
  ∀ j, ContDiffOn ℝ ∞ (f ∘ (A.chart j).symm) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U)
def Smooth (A : FinHolAtlas e X) (f : X → ℝ) : Prop :=
  A.SmoothOn Set.univ f
def HoloOn (A : FinHolAtlas e X) (U : Set X) (g : X → ℂ) : Prop :=
  ∀ j, AnalyticOnNhd ℂ (g ∘ (A.chart j).symm) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U)
def Compatible {e : ℕ} (A B : FinHolAtlas e X) : Prop :=
  (∀ j k, AnalyticOnNhd ℂ (B.chart k ∘ (A.chart j).symm)
    ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (B.chart k).source)) ∧
  ∀ j k, AnalyticOnNhd ℂ (A.chart k ∘ (B.chart j).symm)
    ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (A.chart k).source)
def IsAnalyticSubset (A : FinHolAtlas e X) (S : Set X) : Prop :=
  ∀ x, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ ∃ (r : ℕ) (f : Fin r → X → ℂ),
    (∀ i, A.HoloOn W (f i)) ∧ S ∩ W = {y ∈ W | ∀ i, f i y = 0}
end FinHolAtlas
open FinHolAtlas
structure LocPot (X : Type*) [TopologicalSpace X] where

  U : X → Set X
  isOpen_U : ∀ x, IsOpen (U x)
  mem_U : ∀ x, x ∈ U x

  φ : X → X → ℝ
namespace LocPot
variable {e : ℕ} {X : Type*} [TopologicalSpace X]
def ofFun (u : X → ℝ) : LocPot X where
  U _ := Set.univ
  isOpen_U _ := isOpen_univ
  mem_U _ := Set.mem_univ _
  φ _ := u
instance : Add (LocPot X) where
  add P Q :=
    { U := fun x => P.U x ∩ Q.U x
      isOpen_U := fun x => (P.isOpen_U x).inter (Q.isOpen_U x)
      mem_U := fun x => ⟨P.mem_U x, Q.mem_U x⟩
      φ := fun x y => P.φ x y + Q.φ x y }
def zsmul (m : ℤ) (P : LocPot X) : LocPot X where
  U := P.U
  isOpen_U := P.isOpen_U
  mem_U := P.mem_U
  φ x y := (m : ℝ) * P.φ x y
def rsmul (c : ℝ) (P : LocPot X) : LocPot X where
  U := P.U
  isOpen_U := P.isOpen_U
  mem_U := P.mem_U
  φ x y := c * P.φ x y
def pullback {Y : Type*} [TopologicalSpace Y] (h : Y → X) (hh : Continuous h) (P : LocPot X) :
    LocPot Y where
  U y := h ⁻¹' P.U (h y)
  isOpen_U y := (P.isOpen_U (h y)).preimage hh
  mem_U y := P.mem_U (h y)
  φ y z := P.φ (h y) (h z)
end LocPot
variable {e : ℕ} {X : Type*} [TopologicalSpace X]
def IsPotential (A : FinHolAtlas e X) (P : LocPot X) : Prop :=
  (∀ x, A.SmoothOn (P.U x) (P.φ x)) ∧
  ∀ x x', ∀ y ∈ P.U x ∩ P.U x', ∃ W : Set X, IsOpen W ∧ y ∈ W ∧ ∃ G : X → ℂ,
    A.HoloOn W G ∧ ∀ z ∈ W ∩ P.U x ∩ P.U x', P.φ x z - P.φ x' z = (G z).re
def IsPsh (A : FinHolAtlas e X) (P : LocPot X) : Prop :=
  ∀ x j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x, ∀ w : Fin e → ℂ,
    0 ≤ levi (P.φ x ∘ (A.chart j).symm) y w
def IsPosPot (A : FinHolAtlas e X) (P : LocPot X) : Prop :=
  ∀ x j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x, ∀ w : Fin e → ℂ, w ≠ 0 →
    0 < levi (P.φ x ∘ (A.chart j).symm) y w
def locDens (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (j : Fin A.n) (y : Fin e → ℂ) : ℝ :=
  maDens (fun i y' => (Φ i).φ ((A.chart j).symm y) ((A.chart j).symm y')) y
structure ChartPartition (A : FinHolAtlas e X) where

  χ : Fin A.n → X → ℝ
  smooth : ∀ j, A.Smooth (χ j)
  nonneg : ∀ j x, 0 ≤ χ j x
  tsupport_subset : ∀ j, tsupport (χ j) ⊆ (A.chart j).source
  sum_eq_one : ∀ x, ∑ j, χ j x = 1
def integralWith (A : FinHolAtlas e X) (P : ChartPartition A) (Φ : Fin e → LocPot X)
    (g : X → ℝ) : ℝ :=
  ∑ j, ∫ y in (A.chart j).target,
    P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y
open scoped Classical in

def mInt (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (g : X → ℝ) : ℝ :=
  if h : Nonempty (ChartPartition A) then integralWith A h.some Φ g else 0
def MIntegrable (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (g : X → ℝ) : Prop :=
  ∀ j, ∀ K ⊆ (A.chart j).target, IsCompact K →
    IntegrableOn (fun y => g ((A.chart j).symm y) * locDens A Φ j y) K
def HoloMap {e' : ℕ} {Y : Type*} [TopologicalSpace Y] (B : FinHolAtlas e' Y)
    (A : FinHolAtlas e X) (h : Y → X) : Prop :=
  Continuous h ∧ ∀ j k, AnalyticOnNhd ℂ (A.chart k ∘ h ∘ (B.chart j).symm)
    ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (h ⁻¹' (A.chart k).source))
def IsSection (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) : Prop :=
  (∀ x, A.HoloOn (L.U x) (s x)) ∧
  ∀ x x', ∀ y ∈ L.U x ∩ L.U x',
    ‖s x y‖ * Real.exp (-L.φ x y) = ‖s x' y‖ * Real.exp (-L.φ x' y)
def logNormSec (L : LocPot X) (s : X → X → ℂ) (y : X) : ℝ :=
  Real.log (‖s y y‖ * Real.exp (-L.φ y y))
def IsCompatChart (A : FinHolAtlas e X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) : Prop :=
  ∀ j, AnalyticOnNhd ℂ (ψ ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source) ∧
    AnalyticOnNhd ℂ (A.chart j ∘ ψ.symm) (ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source)
def IsSNC (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) {r : ℕ} (m : Fin r → ℕ)
    (W : Fin r → Set X) : Prop :=
  ∀ x, ∃ ψ : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ ∧ x ∈ ψ.source ∧
    ψ.source ⊆ L.U x ∧ ∃ σ : Fin r → Option (Fin e),
      (∀ k k' i, σ k = some i → σ k' = some i → k = k') ∧
      (∀ k, W k ∩ ψ.source = {y ∈ ψ.source | ∃ i, σ k = some i ∧ ψ y i = 0}) ∧
      ∃ u : X → ℂ, A.HoloOn ψ.source u ∧ (∀ y ∈ ψ.source, u y ≠ 0) ∧
        ∀ y ∈ ψ.source, s x y = u y * ∏ k, (match σ k with
          | some i => ψ y i ^ m k
          | none => 1)
def chartIdx (A : FinHolAtlas e X) (x : X) : Fin A.n := Classical.choose (A.cover x)
def pushDens (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (q : X → Fin e → ℂ) (x : X) : ℝ :=
  locDens A Φ (chartIdx A x) (A.chart (chartIdx A x) x) /
    ‖LinearMap.det (fderiv ℂ (q ∘ (A.chart (chartIdx A x)).symm) (A.chart (chartIdx A x) x) :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2
open scoped Classical in

def maMeasure [MeasurableSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) : Measure X :=
  if h : Nonempty (ChartPartition A) then
    ∑ j, ((volume.restrict (A.chart j).target).withDensity fun y =>
      ENNReal.ofReal (h.some.χ j ((A.chart j).symm y) * locDens A Φ j y)).map (A.chart j).symm
  else 0
end
end ReciprocityTheory.AnForm.M


