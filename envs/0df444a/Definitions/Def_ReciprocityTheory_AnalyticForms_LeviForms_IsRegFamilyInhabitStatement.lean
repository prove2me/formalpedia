-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
-- name    : ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:13.74829+00:00
-- url     : https://prove2.me/theorems/bd4f29fa-2fb5-40e5-886a-5e3d3a4584cf
-- title:
--   Is Reg Family Inhabit Statement
-- statement:
--   Definitions and structural lemmas for Is Reg Family Inhabit Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/IsRegFamilyInhabitStatement.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.P
open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas
noncomputable section
variable {X : Type*}
def bdry (s : X → X → ℂ) : Set X := {y | s y y = 0}
def rW [TopologicalSpace X] (L : LocPot X) (s : X → X → ℂ) (y : X) : ℝ :=
  Real.exp 1 - 2 * logNormSec L s y
def mixFam [TopologicalSpace X] (e i : ℕ) (Φ : LocPot X) (w : X → ℝ) : Fin e → LocPot X :=
  fun k => if k.val < i then Φ + LocPot.ofFun w else Φ
def TailBoundStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas e X) (Θ : Fin e → LocPot X) (L : LocPot X) (s : X → X → ℂ) {n : ℕ}
    (m : Fin n → ℕ) (W : Fin n → Set X),
    (∀ i, IsPotential A (Θ i)) → (∀ i, IsPosPot A (Θ i)) → IsPotential A L → IsSection A L s → IsSNC A L s m W →
    (∀ y, logNormSec L s y ≤ 0) →
    ∃ C : ℝ, ∀ (C₁ : ℝ) (u : Fin e → X → ℝ), 0 ≤ C₁ → (∀ i, A.Smooth (u i)) →
      (∀ i, IsPsh A (Θ i + LocPot.ofFun (u i))) →
      (∀ i, ∀ y ∉ bdry s, -C₁ * Real.log (rW L s y) ≤ u i y ∧ u i y ≤ 0) →
      ∀ R : ℝ, Real.exp 1 ≤ R →
        maMeasure A (fun i => Θ i + LocPot.ofFun (u i)) (bdry s ∪ {y | R ≤ rW L s y}) ≤
            ENNReal.ofReal (C * (C₁ + 3) * Real.log R / R) ∧
          ∫⁻ y in (bdry s)ᶜ ∩ {y | R ≤ rW L s y}, ENNReal.ofReal (Real.log (rW L s y))
              ∂maMeasure A (fun i => Θ i + LocPot.ofFun (u i)) ≤
            ENNReal.ofReal (C * (C₁ + 3) * Real.log R ^ 2 / R)
def EnergyStepStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (Φ : LocPot X) (w : X → ℝ), IsPotential A Φ → A.Smooth w →
    IsPsh A Φ → IsPsh A (Φ + LocPot.ofFun w) → ∀ i : ℕ, i + 1 ≤ e →
      mInt A (mixFam e (i + 1) Φ w) w ≤ mInt A (mixFam e i Φ w) w
def EnergySumStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (Φ : LocPot X) (w : X → ℝ), IsPotential A Φ → A.Smooth w →
    IsPsh A Φ → IsPsh A (Φ + LocPot.ofFun w) →
      ∑ i ∈ Finset.range (e + 1), mInt A (mixFam e i Φ w) w ≤
        ((e : ℝ) + 1) * mInt A (fun _ => Φ) w
def MeanLogStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (lam : Ω → ℝ)
    (N : ℝ → Ω → ℕ) (r a κ : ℝ), 0 < r → 0 ≤ a → 3 * a ≤ κ → 1 ≤ κ → Measurable lam →
    (∀ ω, 0 < lam ω) → (∀ t, 0 < t → t ≤ r → Measurable (N t)) →
    (∀ t ω, 0 < t → t ≤ r → lam ω < t → 1 ≤ N t ω) →
    (∀ t ω, 0 < t → t ≤ r → t ≤ lam ω → N t ω = 0) →
    (∀ ω, lam ω < r → (N r ω : ℝ) ≤ (3 * r / lam ω) ^ a) →
    Integrable (fun ω => (N r ω : ℝ)) P →
    (∀ θ, 0 < θ → θ ≤ 1 → ∫ ω, (N (θ * r) ω : ℝ) ∂P = θ ^ κ * ∫ ω, (N r ω : ℝ) ∂P) →
      ∫⁻ ω, ENNReal.ofReal (Real.log (r / lam ω)) ∂P ≤ 3
def IsPshOn [TopologicalSpace X] {e : ℕ} (A : FinHolAtlas e X) (U : Set X) (P : LocPot X) : Prop :=
  ∀ x j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (P.U x ∩ U), ∀ w : Fin e → ℂ,
    0 ≤ levi (P.φ x ∘ (A.chart j).symm) y w
def IsPshSubOn [TopologicalSpace X] {e : ℕ} (A : FinHolAtlas e X) (U : Set X) (P : LocPot X) :
    Prop :=
  ∀ x j, ReciprocityTheory.AnForm.A.IsPsh ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (P.U x ∩ U))
    (P.φ x ∘ (A.chart j).symm)
def epsT (C t : ℝ) : ℝ := C * Real.log (Real.log (1 / t)) / Real.log (1 / t)
def rLoc {D : ℕ} (S : Finset (Fin D)) (m : Fin D → ℕ) (z : Fin D → ℂ) : ℝ :=
  Real.exp 1 + ∑ i ∈ S, (m i : ℝ) * Real.log (4 / ‖z i‖ ^ 2)
def IsAdaptedAtlas [TopologicalSpace X] {e : ℕ} (A B : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) : Prop :=
  A.Compatible B ∧ (∀ j, Metric.closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target) ∧
    (∀ x, ∃ j, x ∈ (B.chart j).source ∧ B.chart j x ∈ Metric.ball (0 : Fin e → ℂ) 1) ∧
    ∃ M : ℝ, ∀ j, ∃ (S : Finset (Fin e)) (m : Fin e → ℕ), (∀ i ∈ S, 1 ≤ m i) ∧
      (∀ y ∈ (B.chart j).target, ((B.chart j).symm y ∈ bdry s ↔ ∃ i ∈ S, y i = 0)) ∧
      ∀ y ∈ Metric.closedBall (0 : Fin e → ℂ) 2, (B.chart j).symm y ∉ bdry s →
        |rW L s ((B.chart j).symm y) - rLoc S m y| ≤ M
def IsRegFamily [TopologicalSpace X] {e : ℕ} (A : FinHolAtlas e X) (Θ L : LocPot X)
    (s : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C t₀ : ℝ) : Prop :=
  0 < t₀ ∧ t₀ < 1 ∧ ∀ t, 0 < t → t ≤ t₀ →
    A.Smooth (phT t) ∧
    (∀ y, phT t y ≤ C) ∧ (∀ y ∉ bdry s, ph y ≤ phT t y) ∧
    (∀ y, -C * Real.log (Real.log (1 / t)) ≤ phT t y) ∧
    IsPsh A (th + LocPot.ofFun (phT t) + Θ.rsmul (epsT C t)) ∧
    (∀ y ∉ bdry s, rW L s y ≤ Real.log (1 / t) →
      phT t y ≤ ph y + t ^ ((1 : ℝ) / 3) + epsT C t) ∧
    (∀ y ∉ bdry s, phT t y ≤ ph y + t ^ ((1 : ℝ) / 3) + epsT C t * rW L s y) ∧
    (∀ t', t ≤ t' → t' ≤ t₀ → ∀ y, phT t y ≤ phT t' y + C * epsT C t')
def IsRegFamilyC2 [TopologicalSpace X] {e : ℕ} (A : FinHolAtlas e X) (s : X → X → ℂ)
    (ph : X → ℝ) (phT : ℝ → X → ℝ) : Prop :=
  ∀ j, ∀ K ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (bdry s)ᶜ, IsCompact K →
    TendstoUniformlyOn (fun t => phT t ∘ (A.chart j).symm) (ph ∘ (A.chart j).symm)
        (nhdsWithin 0 (Set.Ioi 0)) K ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (phT t ∘ (A.chart j).symm))
        (fderiv ℝ (ph ∘ (A.chart j).symm)) (nhdsWithin 0 (Set.Ioi 0)) K ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (phT t ∘ (A.chart j).symm)))
        (fderiv ℝ (fderiv ℝ (ph ∘ (A.chart j).symm))) (nhdsWithin 0 (Set.Ioi 0)) K
def IsSingWeight [TopologicalSpace X] {e : ℕ} (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (C₅ : ℝ) : Prop :=
  IsPotential A th ∧ A.SmoothOn (bdry s)ᶜ ph ∧ IsPshOn A (bdry s)ᶜ (th + LocPot.ofFun ph) ∧
    ∀ y ∉ bdry s, -C₅ * Real.log (rW L s y) ≤ ph y ∧ ph y ≤ C₅
def IsGradBound [TopologicalSpace X] {e : ℕ} (B : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) (ph : X → ℝ) (C₅ : ℝ) : Prop :=
  ∀ j, ∀ y ∈ Metric.ball (0 : Fin e → ℂ) (3 / 2), (B.chart j).symm y ∉ bdry s →
      ‖fderiv ℝ (ph ∘ (B.chart j).symm) y‖ ≤
        C₅ * rW L s ((B.chart j).symm y) ^ C₅ * Real.exp (rW L s ((B.chart j).symm y) / 2)
def RegGlobalStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A B : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ)
    (W : Fin n → Set X), IsPotential A Θ → IsPosPot A Θ → IsPotential A L → IsSection A L s →
    IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → IsAdaptedAtlas A B L s →
    ∀ (th : LocPot X) (ph : X → ℝ) (C₅ : ℝ), IsSingWeight A L s th ph C₅ →
      IsGradBound B L s ph C₅ → ∃ (C t₀ : ℝ) (phT : ℝ → X → ℝ),
        IsRegFamily A Θ L s th ph phT C t₀ ∧ IsRegFamilyC2 A s ph phT
def RegGlobalContStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ)
    (W : Fin n → Set X), IsPotential A Θ → IsPosPot A Θ → IsPotential A L → IsSection A L s →
    IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) →
    ∀ (th : LocPot X) (ph : X → ℝ) (C₅ : ℝ), IsPotential A th → ContinuousOn ph (bdry s)ᶜ →
      (∀ y ∉ bdry s, |ph y| ≤ C₅) → IsPshSubOn A (bdry s)ᶜ (th + LocPot.ofFun ph) →
      ∃ (C t₀ : ℝ) (phT : ℝ → X → ℝ), 0 < t₀ ∧ t₀ < 1 ∧
        (∀ t, 0 < t → t ≤ t₀ →
          A.Smooth (phT t) ∧ (∀ y, -C ≤ phT t y ∧ phT t y ≤ C) ∧
          (∀ y ∉ bdry s, ph y ≤ phT t y) ∧
          IsPsh A (th + LocPot.ofFun (phT t) + Θ.rsmul (epsT C t)) ∧
          ∀ x ∈ bdry s, ∀ δ > 0, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
            ∀ y ∈ V, y ∉ bdry s → ph y ≤ phT t x + δ) ∧
        ∀ y ∉ bdry s, Filter.Tendsto (fun t => phT t y) (nhdsWithin 0 (Set.Ioi 0)) (nhds (ph y))
def IsRegFamilyInhabitStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X)
    (s : X → X → ℂ), IsPotential A Θ → IsPosPot A Θ → (∀ y, logNormSec L s y ≤ 0) →
      IsRegFamily A Θ L s Θ (fun _ => 0) (fun _ _ => 0) 1 (Real.exp (-Real.exp 1)) ∧
        IsRegFamilyC2 A s (fun _ => 0) (fun _ _ => 0)
def ConvergenceStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ}
    (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A Θ → IsPosPot A Θ → IsPotential A L →
    IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) →
    ∀ (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ) (C₅ C t₀ : ℝ),
      (∀ i, IsSingWeight A L s (th i) (ph i) C₅) →
      (∀ i, IsRegFamily A Θ L s (th i) (ph i) (phT i) C t₀) →
      (∀ i, IsRegFamilyC2 A s (ph i) (phT i)) →
      ∀ (g : X → ℝ) (gT : ℝ → X → ℝ) (C₆ : ℝ), (∀ t, ContinuousOn (gT t) (bdry s)ᶜ) →
        (∀ t y, y ∉ bdry s → |gT t y| ≤ C₆ * Real.log (rW L s y)) →
        TendstoLocallyUniformlyOn gT g (nhdsWithin 0 (Set.Ioi 0)) (bdry s)ᶜ →
        let μT := fun t => maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ)
        let μ := maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ)
        IsFiniteMeasure μ ∧ (μ Set.univ).toReal = mInt A (fun i => th i + Θ) (fun _ => 1) ∧
          Integrable g μ ∧ (∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), Integrable (gT t) (μT t)) ∧
          Filter.Tendsto (fun t => ∫ y, gT t y ∂μT t) (nhdsWithin 0 (Set.Ioi 0))
            (nhds (∫ y, g y ∂μ))
def UnifIntStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ}
    (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A Θ → IsPosPot A Θ → IsPotential A L →
    IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) →
    ∀ (L' : LocPot X) (v : X → X → ℂ) (Dg : Set X), IsPotential A L' → IsSection A L' v →
      IsSNC A L' v ![1] ![Dg] →
      IsSNC A (L + L') (fun x y => s x y * v x y) (Fin.snoc m 1) (Fin.snoc W Dg) →
      (∀ y, logNormSec L' v y ≤ 0) →
    ∀ (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ) (C₅ C t₀ : ℝ),
      (∀ i, IsSingWeight A L s (th i) (ph i) C₅) →
      (∀ i, IsRegFamily A Θ L s (th i) (ph i) (phT i) C t₀) →
      (∀ i, IsRegFamilyC2 A s (ph i) (phT i)) →
        let G := fun y => -logNormSec L' v y
        let μT := fun t => maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ)
        let μ := maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ)
        Integrable G μ ∧ (∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), Integrable G (μT t)) ∧
          Filter.Tendsto (fun t => ∫ y, G y ∂μT t) (nhdsWithin 0 (Set.Ioi 0))
            (nhds (∫ y, G y ∂μ))
def ConvergenceSignedStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ}
    (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A Θ → IsPosPot A Θ → IsPotential A L →
    IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) →
    ∀ (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ) (C₅ C t₀ : ℝ),
      (∀ i, IsSingWeight A L s (th i) (ph i) C₅) →
      (∀ i, IsRegFamily A Θ L s (th i) (ph i) (phT i) C t₀) →
      (∀ i, IsRegFamilyC2 A s (ph i) (phT i)) →
      ∀ (g : X → ℝ) (gT : ℝ → X → ℝ) (C₆ : ℝ), (∀ t, ContinuousOn (gT t) (bdry s)ᶜ) →
        (∀ t y, y ∉ bdry s → |gT t y| ≤ C₆ * Real.log (rW L s y)) →
        TendstoLocallyUniformlyOn gT g (nhdsWithin 0 (Set.Ioi 0)) (bdry s)ᶜ →
        MIntegrable A (fun i => th i + LocPot.ofFun (ph i)) g ∧
          Filter.Tendsto (fun t => mInt A (fun i => th i + LocPot.ofFun (phT i t)) (gT t))
            (nhdsWithin 0 (Set.Ioi 0)) (nhds (mInt A (fun i => th i + LocPot.ofFun (ph i)) g))
def ConvergenceRateStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ}
    (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A Θ → IsPosPot A Θ → IsPotential A L →
    IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) →
    ∀ (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ)
      (th₀ : LocPot X) (ph₀ : X → ℝ) (phT₀ : ℝ → X → ℝ) (C₅ C t₀ : ℝ),
      (∀ i, IsSingWeight A L s (th i) (ph i) C₅) →
      (∀ i, IsRegFamily A Θ L s (th i) (ph i) (phT i) C t₀) →
      IsSingWeight A L s th₀ ph₀ C₅ → IsRegFamily A Θ L s th₀ ph₀ phT₀ C t₀ →
      ∃ C' t₁ : ℝ, 0 < t₁ ∧ ∀ t t', 0 < t' → t' ≤ t → t ≤ t₁ → ∀ c : Fin e → Bool,
        ∫⁻ y, ENNReal.ofReal |phT₀ t y - phT₀ t' y|
            ∂maMeasure A (fun i => th i + LocPot.ofFun (phT i (if c i then t else t')) + Θ) ≤
          ENNReal.ofReal (C' * Real.log (Real.log (1 / t)) ^ 2 / Real.log (1 / t))
def PullbackStatement : Prop :=
  ∀ {e e' : ℕ} {X X' : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace X'] [CompactSpace X'] [T2Space X'] (A : FinHolAtlas e X)
    (A' : FinHolAtlas e' X') (h : X' → X) (hh : HoloMap A' A h) (Θ L : LocPot X) (Θ' : LocPot X')
    (s : X → X → ℂ) {n n' : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X) (m' : Fin n' → ℕ)
    (W' : Fin n' → Set X'), IsPotential A Θ → IsPosPot A Θ → IsPotential A' Θ' → IsPosPot A' Θ' →
    IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) →
    IsSNC A' (L.pullback h hh.1) (fun x y => s (h x) (h y)) m' W' →
    ∀ (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C₅ C t₀ : ℝ),
      IsSingWeight A L s th ph C₅ → IsRegFamily A Θ L s th ph phT C t₀ →
      IsRegFamilyC2 A s ph phT →
      ∃ C' t₀' : ℝ,
        IsSingWeight A' (L.pullback h hh.1) (fun x y => s (h x) (h y)) (th.pullback h hh.1)
            (ph ∘ h) C₅ ∧
          IsRegFamily A' Θ' (L.pullback h hh.1) (fun x y => s (h x) (h y)) (th.pullback h hh.1)
            (ph ∘ h) (fun t => phT t ∘ h) C' t₀' ∧
          IsRegFamilyC2 A' (fun x y => s (h x) (h y)) (ph ∘ h) (fun t => phT t ∘ h)
abbrev Pairs (N : ℕ) := {p : Fin N × Fin N // p.1 < p.2}
def cellMat (N : ℕ) (z : Pairs N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  let Z : Matrix (Fin N) (Fin N) ℂ := ∑ p : Pairs N, Matrix.single p.1.2 p.1.1 (z p)
  ∑ k ∈ Finset.range N, ((k.factorial : ℂ)⁻¹) • Z ^ k
def logDetFlag (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (z : Pairs N → ℂ) : ℝ :=
  (1 / 2) * Real.log ‖(Matrix.submatrix ((cellMat N z).conjTranspose *
      Matrix.diagonal (fun k => (hd k : ℂ)) * cellMat N z)
      (Fin.castLE hm) (Fin.castLE hm)).det‖
def HomDensityStatement : Prop :=
  ∀ (N : ℕ) (hd : Fin N → ℝ), (∀ k, hd k ≠ 0) → ∀ (m : ℕ) (hm : m ≤ N) (w : Pairs N → ℂ),
    levi (logDetFlag N hd m hm) 0 w =
      ∑ p : Pairs N, if p.1.1.val < m ∧ m ≤ p.1.2.val then
        hd p.1.2 / (2 * hd p.1.1) * ‖w p‖ ^ 2 else 0
end
end ReciprocityTheory.AnForm.P


