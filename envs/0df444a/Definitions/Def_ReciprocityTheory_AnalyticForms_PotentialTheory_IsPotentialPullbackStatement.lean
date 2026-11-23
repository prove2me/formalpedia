-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:14.506806+00:00
-- url     : https://prove2.me/theorems/8da6a667-8007-4cb2-b082-c1d64d5a9f59
-- title:
--   Is Potential Pullback Statement
-- statement:
--   Definitions and structural lemmas for Is Potential Pullback Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IsPotentialPullbackStatement.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
noncomputable section
def IsPotentialAddStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P Q : LocPot X),
    IsPotential A P → IsPotential A Q → IsPotential A (P + Q)
def IsPotentialZsmulStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (m : ℤ) (P : LocPot X),
    IsPotential A P → IsPotential A (P.zsmul m)
def IsPotentialPullbackStatement : Prop :=
  ∀ {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (A : FinHolAtlas e X)
    (B : FinHolAtlas e' Y) (h : Y → X) (hh : HoloMap B A h) (P : LocPot X),
    IsPotential A P → IsPotential B (P.pullback h hh.1)
def IsPotentialRsmulStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (c : ℝ) (P : LocPot X),
    IsPotential A P → IsPotential A (P.rsmul c)
def IsPshRsmulStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (c : ℝ) (P : LocPot X),
    0 ≤ c → IsPotential A P → IsPsh A P → IsPsh A (P.rsmul c)
def PshShiftStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Ω : LocPot X), IsPotential A Ω → IsPosPot A Ω → ∀ w : X → ℝ, A.Smooth w →
      ∃ C : ℝ, IsPsh A (LocPot.ofFun w + Ω.rsmul C)
def RegularAtlasStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X),
    ∃ B : FinHolAtlas e X, A.Compatible B ∧
      (∀ j, Metric.closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target) ∧
      ∀ x, ∃ j, x ∈ (B.chart j).source ∧ B.chart j x ∈ Metric.ball (0 : Fin e → ℂ) 1
def SNCInducedAtlasStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (L : LocPot X) (s : X → X → ℂ) {r : ℕ} (m : Fin r → ℕ)
    (W : Fin r → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W →
      ∀ k, ∃ B : FinHolAtlas e (W k), HoloMap B A Subtype.val
def IsPshAddStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P Q : LocPot X),
    IsPotential A P → IsPotential A Q → IsPsh A P → IsPsh A Q → IsPsh A (P + Q)
def ExistsPartitionStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X),
    Nonempty (ChartPartition A)
def LocDensBaseStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X),
    (∀ i, IsPotential A (Φ i)) → ∀ j, ∀ y ∈ (A.chart j).target, ∀ x : Fin e → X,
      (∀ i, (A.chart j).symm y ∈ (Φ i).U (x i)) →
      locDens A Φ j y = maDens (fun i y' => (Φ i).φ (x i) ((A.chart j).symm y')) y
def LocDensContStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X),
    (∀ i, IsPotential A (Φ i)) → ∀ j, ContinuousOn (locDens A Φ j) (A.chart j).target
def LocDensChartStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X),
    (∀ i, IsPotential A (Φ i)) → ∀ j k, ∀ y ∈ (A.chart j).target,
      (A.chart j).symm y ∈ (A.chart k).source →
      locDens A Φ j y = locDens A Φ k (A.chart k ((A.chart j).symm y)) *
        ‖LinearMap.det (fderiv ℂ (A.chart k ∘ (A.chart j).symm) y :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2
def IntegralWithIndepStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (P Q : ChartPartition A) (Φ : Fin e → LocPot X), (∀ i, IsPotential A (Φ i)) →
    ∀ g : X → ℝ, MIntegrable A Φ g → integralWith A P Φ g = integralWith A Q Φ g
def MIntEqStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (P : ChartPartition A) (Φ : Fin e → LocPot X), (∀ i, IsPotential A (Φ i)) →
    ∀ g : X → ℝ, MIntegrable A Φ g → mInt A Φ g = integralWith A P Φ g
def MIntAtlasIndepStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A B : FinHolAtlas e X), A.Compatible B → ∀ Φ : Fin e → LocPot X,
    (∀ i, IsPotential A (Φ i)) → ∀ g : X → ℝ, MIntegrable A Φ g →
      MIntegrable B Φ g ∧ mInt A Φ g = mInt B Φ g
def MIntegrableContStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X),
    (∀ i, IsPotential A (Φ i)) → ∀ g : X → ℝ, Continuous g → MIntegrable A Φ g
def MIntSymmStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X)
    (σ : Equiv.Perm (Fin e)) (g : X → ℝ), mInt A (Φ ∘ σ) g = mInt A Φ g
def MIntAddStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (P Q : LocPot X) (Φ : Fin e → LocPot X),
    IsPotential A P → IsPotential A Q → (∀ i, IsPotential A (Φ i)) → ∀ g : X → ℝ,
    MIntegrable A (Fin.cons P Φ) g → MIntegrable A (Fin.cons Q Φ) g →
      mInt A (Fin.cons (P + Q) Φ) g = mInt A (Fin.cons P Φ) g + mInt A (Fin.cons Q Φ) g
def MIntZsmulStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas (e + 1) X) (m : ℤ)
    (P : LocPot X) (Φ : Fin e → LocPot X), IsPotential A P → (∀ i, IsPotential A (Φ i)) →
    ∀ g : X → ℝ, mInt A (Fin.cons (P.zsmul m) Φ) g = m * mInt A (Fin.cons P Φ) g
def MIntRsmulStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas (e + 1) X) (c : ℝ)
    (P : LocPot X) (Φ : Fin e → LocPot X), IsPotential A P → (∀ i, IsPotential A (Φ i)) →
    ∀ g : X → ℝ, mInt A (Fin.cons (P.rsmul c) Φ) g = c * mInt A (Fin.cons P Φ) g
def MIntLinearStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X), (∀ i, IsPotential A (Φ i)) → ∀ (c : ℝ) (g g' : X → ℝ),
    MIntegrable A Φ g → MIntegrable A Φ g' →
      mInt A Φ (fun x => c * g x + g' x) = c * mInt A Φ g + mInt A Φ g'
def MIntNonnegStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X),
    (∀ i, IsPotential A (Φ i)) → (∀ i, IsPsh A (Φ i)) → ∀ g : X → ℝ, (∀ x, 0 ≤ g x) →
      0 ≤ mInt A Φ g
def MIntMeasureStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X), (∀ i, IsPotential A (Φ i)) →
    ∃ μ ν : Measure X, IsFiniteMeasure μ ∧ IsFiniteMeasure ν ∧
      ∀ g : X → ℝ, Measurable g → MIntegrable A Φ g →
        Integrable g μ ∧ Integrable g ν ∧ mInt A Φ g = ∫ x, g x ∂μ - ∫ x, g x ∂ν
def MaMeasureStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X), (∀ i, IsPotential A (Φ i)) →
    (∀ i, IsPsh A (Φ i)) → IsFiniteMeasure (maMeasure A Φ) ∧
      ∀ g : X → ℝ, Measurable g → (MIntegrable A Φ g ↔ Integrable g (maMeasure A Φ)) ∧
        (MIntegrable A Φ g → mInt A Φ g = ∫ x, g x ∂maMeasure A Φ)
def MaMeasureMonoStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (A : FinHolAtlas e X) (Φ Θ : Fin e → LocPot X), (∀ i, IsPotential A (Φ i)) →
    (∀ i, IsPsh A (Φ i)) → (∀ i, IsPotential A (Θ i)) → (∀ i, IsPsh A (Θ i)) →
      maMeasure A Φ ≤ maMeasure A (fun i => Φ i + Θ i)
def LocDensPosStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X),
    (∀ i, IsPotential A (Φ i)) → (∀ i, IsPosPot A (Φ i)) →
      ∀ j, ∀ y ∈ (A.chart j).target, 0 < locDens A Φ j y
def AnalyticNullStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (S : Set X),
    A.IsAnalyticSubset S → interior S = ∅ →
      ∀ j, volume ((A.chart j) '' (S ∩ (A.chart j).source)) = 0
def MIntCongrNullStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X)
    (S : Set X), A.IsAnalyticSubset S → interior S = ∅ → ∀ g g' : X → ℝ,
    (∀ x ∉ S, g x = g' x) → mInt A Φ g = mInt A Φ g'
def StokesStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (w : X → ℝ), A.Smooth w → ∀ Φ : Fin e → LocPot X,
    (∀ i, IsPotential A (Φ i)) → mInt A (Fin.cons (LocPot.ofFun w) Φ) (fun _ => 1) = 0
def ByPartsSymmStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (v w : X → ℝ), A.Smooth v → A.Smooth w →
    ∀ Φ : Fin e → LocPot X, (∀ i, IsPotential A (Φ i)) →
      mInt A (Fin.cons (LocPot.ofFun w) Φ) v = mInt A (Fin.cons (LocPot.ofFun v) Φ) w
def ByPartsNonposStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (v : X → ℝ), A.Smooth v → ∀ Φ : Fin e → LocPot X,
    (∀ i, IsPotential A (Φ i)) → (∀ i, IsPsh A (Φ i)) →
      mInt A (Fin.cons (LocPot.ofFun v) Φ) v ≤ 0
def MassIndepStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (u : Fin e → X → ℝ), (∀ i, IsPotential A (Φ i)) →
    (∀ i, A.Smooth (u i)) →
      mInt A (fun i => Φ i + LocPot.ofFun (u i)) (fun _ => 1) = mInt A Φ (fun _ => 1)
def LogNormIntegrableStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (L : LocPot X) (s : X → X → ℂ) {r : ℕ} (m : Fin r → ℕ) (W : Fin r → Set X),
    IsPotential A L → IsSection A L s → IsSNC A L s m W → ∀ Φ : Fin e → LocPot X,
    (∀ i, IsPotential A (Φ i)) → MIntegrable A Φ (logNormSec L s)
def PoincareLelongCurveStatement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas 1 X)
    (L : LocPot X) (s : X → X → ℂ) {r : ℕ} (m : Fin r → ℕ) (p : Fin r → X),
    Function.Injective p → IsPotential A L → IsSection A L s → IsSNC A L s m (fun k => {p k}) →
    ∀ v : X → ℝ, A.Smooth v →
      mInt A ![LocPot.ofFun v] (logNormSec L s) = ∑ k, (m k : ℝ) * v (p k) - mInt A ![L] v
def PoincareLelongStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (L : LocPot X) (s : X → X → ℂ) {r : ℕ} (m : Fin r → ℕ)
    (W : Fin r → Set X) (B : ∀ k, FinHolAtlas e (W k)),
    IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ k, HoloMap (B k) A Subtype.val) →
    ∀ v : X → ℝ, A.Smooth v → ∀ Φ : Fin e → LocPot X, (∀ i, IsPotential A (Φ i)) →
      mInt A (Fin.cons (LocPot.ofFun v) Φ) (logNormSec L s) =
        ∑ k, (m k : ℝ) * mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val)
            (v ∘ Subtype.val) - mInt A (Fin.cons L Φ) v
def PushForwardStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X), (∀ i, IsPotential A (Φ i)) → ∀ (q : X → Fin e → ℂ) (T S : Set X),
    IsClosed T → T ⊆ S → A.IsAnalyticSubset S → interior S = ∅ →
    (∀ i, A.HoloOn Tᶜ (fun x => q x i)) →
    (∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) →
    (∀ y, (q ⁻¹' {y} \ S).Finite) →
    ∀ g : X → ℝ, MIntegrable A Φ g →
      Integrable (fun y => ∑ᶠ x ∈ q ⁻¹' {y} \ S, g x * pushDens A Φ q x) ∧
        mInt A Φ g = ∫ y, ∑ᶠ x ∈ q ⁻¹' {y} \ S, g x * pushDens A Φ q x
def LocDensPullbackStatement : Prop :=
  ∀ {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (A : FinHolAtlas e X)
    (B : FinHolAtlas e Y) (h : Y → X) (hh : HoloMap B A h) (Φ : Fin e → LocPot X),
    (∀ i, IsPotential A (Φ i)) → ∀ j k, ∀ y ∈ (B.chart j).target,
      h ((B.chart j).symm y) ∈ (A.chart k).source →
      locDens B (fun i => (Φ i).pullback h hh.1) j y =
        locDens A Φ k (A.chart k (h ((B.chart j).symm y))) *
          ‖LinearMap.det (fderiv ℂ (A.chart k ∘ h ∘ (B.chart j).symm) y :
            (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2
def RankDropStatement : Prop :=
  ∀ {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (A : FinHolAtlas e' X)
    (B : FinHolAtlas e Y) (h : Y → X) (hh : HoloMap B A h),
    (∀ j k, ∀ y ∈ (B.chart j).target, h ((B.chart j).symm y) ∈ (A.chart k).source →
      Module.finrank ℂ (LinearMap.range (fderiv ℂ (A.chart k ∘ h ∘ (B.chart j).symm) y :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e' → ℂ))) < e) →
    ∀ Φ : Fin e → LocPot X, (∀ i, IsPotential A (Φ i)) → ∀ g : Y → ℝ,
      mInt B (fun i => (Φ i).pullback h hh.1) g = 0
def IsDegreeOff {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (h : Y → X) (d : ℕ) (S : Set X) : Prop :=
  A.IsAnalyticSubset S ∧ interior S = ∅ ∧ B.IsAnalyticSubset (h ⁻¹' S) ∧
    interior (h ⁻¹' S) = ∅ ∧ (∀ x ∉ S, (h ⁻¹' {x}).ncard = d) ∧
    ∀ j k, ∀ y ∈ (B.chart j).target, (B.chart j).symm y ∉ h ⁻¹' S →
      h ((B.chart j).symm y) ∈ (A.chart k).source →
      LinearMap.det (fderiv ℂ (A.chart k ∘ h ∘ (B.chart j).symm) y :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0
def DegreeFormulaStatement : Prop :=
  ∀ {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X]
    [CompactSpace Y] [T2Space Y] (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (h : Y → X)
    (hh : HoloMap B A h) (d : ℕ) (S : Set X), IsDegreeOff A B h d S →
    ∀ Φ : Fin e → LocPot X, (∀ i, IsPotential A (Φ i)) → ∀ g : X → ℝ, Continuous g →
      mInt B (fun i => (Φ i).pullback h hh.1) (g ∘ h) = d * mInt A Φ g
def DegreeFormulaIntStatement : Prop :=
  ∀ {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X]
    [CompactSpace Y] [T2Space Y] (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (h : Y → X)
    (hh : HoloMap B A h) (d : ℕ) (S : Set X), IsDegreeOff A B h d S →
    ∀ Φ : Fin e → LocPot X, (∀ i, IsPotential A (Φ i)) → ∀ g : X → ℝ, MIntegrable A Φ g →
      MIntegrable B (fun i => (Φ i).pullback h hh.1) (g ∘ h) ∧
        mInt B (fun i => (Φ i).pullback h hh.1) (g ∘ h) = d * mInt A Φ g
end
end ReciprocityTheory.AnForm.M


