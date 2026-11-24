-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IsConeAnalyticSubset
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IsConeAnalyticSubset
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:06.05639+00:00
-- url     : https://prove2.me/theorems/2ce057e0-940e-4d05-aa8c-f8374c31e052
-- title:
--   Is Cone Analytic Subset
-- statement:
--   Definitions and structural lemmas for Is Cone Analytic Subset, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IsConeAnalyticSubset.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_MoriwakiSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_HSClosing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_DoubleBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqZeroOfSecTraceMulEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Filter Topology
open scoped Manifold ContDiff ENNReal
noncomputable section
section OneBlock
variable {κ : Type} [Fintype κ]
def IsAnalyticSubset (D : ℕ) {M : Type} [TopologicalSpace M] [ChartedSpace (Fin D → ℂ) M]
    (A : Set M) : Prop :=
  IsClosed A ∧ ∀ q : M, ∃ U ∈ 𝓝 q, ∃ (r : ℕ) (g : Fin r → M → ℂ),
    (∀ j, MDifferentiableOn 𝓘(ℂ, Fin D → ℂ) 𝓘(ℂ, ℂ) (g j) U) ∧
      A ∩ U = {q' | q' ∈ U ∧ ∀ j, g j q' = 0}
def IsConeAnalyticSubset (P : Ideal (MvPolynomial (Ix κ) ℤ)) (B : Set (Ix κ → ℂ)) : Prop :=
  B ⊆ pts P ∧ (∀ z ∈ B, ∀ c : ℂ, c ≠ 0 → c • z ∈ B) ∧
    ∀ z ∈ pts P, ∃ U ∈ 𝓝 z, ∃ (r : ℕ) (g : Fin r → (Ix κ → ℂ) → ℂ),
      (∀ j, DifferentiableOn ℂ (g j) U) ∧ B ∩ U = {w | w ∈ U ∧ w ∈ pts P ∧ ∀ j, g j w = 0}
structure IsAnalyticRes (P : Ideal (MvPolynomial (Ix κ) ℤ)) (D : ℕ) {M : Type} [TopologicalSpace M]
    [ChartedSpace (Fin D → ℂ) M] [MeasurableSpace M] (f : M → Ix κ → ℂ) : Prop where
  mem : ∀ q, f q ∈ pts P
  meas : Measurable f
  holo : ∀ q, ∃ c : M → ℂ, (∀ᶠ q' in 𝓝 q, c q' ≠ 0) ∧
    MDifferentiableAt 𝓘(ℂ, Fin D → ℂ) 𝓘(ℂ, Ix κ → ℂ) (fun q' ↦ c q' • f q') q
  onto : ∀ z ∈ pts P, ∃ q, ∃ c : ℂ, c ≠ 0 ∧ z = c • f q
  exc : ∃ (A : Set M) (B : Set (Ix κ → ℂ)), IsAnalyticSubset D A ∧ Dense Aᶜ ∧
    IsConeAnalyticSubset P B ∧ pts P ⊆ closure (pts P \ B) ∧ (∀ q, q ∉ A → f q ∉ B) ∧
    (∀ q q', q ∉ A → q' ∉ A → ∀ c : ℂ, f q' = c • f q → q' = q) ∧
    ∀ z ∈ pts P, z ∉ B → ∃ q, q ∉ A ∧ ∃ c : ℂ, c ≠ 0 ∧ z = c • f q
def IsSmoothVolume (D : ℕ) {M : Type} [TopologicalSpace M] [ChartedSpace (Fin D → ℂ) M]
    [MeasurableSpace M] (dV : Measure M) : Prop :=
  IsProbabilityMeasure dV ∧ ∀ e ∈ atlas (Fin D → ℂ) M, ∃ ν : (Fin D → ℂ) → ℝ,
    ContDiffOn ℝ ∞ ν e.target ∧ (∀ y ∈ e.target, 0 < ν y) ∧
    ∀ s : Set M, MeasurableSet s → s ⊆ e.source → dV s = ∫⁻ y in e '' s, ENNReal.ofReal (ν y)
def symMeasure {M : Type} [MeasurableSpace M] (f : M → Ix κ → ℂ) (dV : Measure M) :
    Measure (Ix κ → ℂ) :=
  (2 : ℝ≥0∞)⁻¹ • (dV.map f + dV.map (conjPt ∘ f))
def secRank {Ω : Type} [Field Ω] (x : Ix κ → Ω) (n : ℕ) : ℕ :=
  Module.finrank ℤ (sec ℤ x n)
def secNorm {J : Type} [Fintype J] {Ω : Type} [Field Ω] (x : J → Ω) (m : ConeMetric ℂ J)
    (μ : Measure (J → ℂ)) (n : ℕ) (s : Ω) : ℝ := by
  classical
  exact if h : ∃ f : MvPolynomial J ℤ, f.IsHomogeneous n ∧ aeval x f = s then
    l2Norm m (Int.castRingHom ℂ) μ n h.choose else 0
structure IsHSDatum (D : ℕ) {Ω : Type} [Field Ω] [CharZero Ω] (x : Ix κ → Ω)
    (m : ConeMetric ℂ (Ix κ)) (P₀ : Ideal (MvPolynomial (Ix κ) ℤ)) : Prop where
  one_le : 1 ≤ D
  arith : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1)
  indep : LinearIndependent ℤ x
  le : P₀ ≤ coordIdeal ℤ x
  semipos : IsSemipositiveRel (ι := GlobalTheory κ) P₀ (coordIdeal ℤ x) (HermLine.ofCone m)
  conj : IsConjInvariantH (HermLine.ofCone m)
end OneBlock
section Block
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
def hpow (A : HermLine ι) (j : ℕ) : HermLine ι where
  a := (j : ℤ) • A.a
  h z := A.h z ^ j
  pos z hz := pow_pos (A.pos z hz) j
  smul c z hc := by
    rw [A.smul c z hc, mul_pow, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_comm, zpow_mul, zpow_natCast]
def SupLE (P : Ideal (MRing ι)) (y : (Σ k, ι k) → Ω) (a : K → ℤ) (hm : ((Σ k, ι k) → ℂ) → ℝ)
    (c : ℝ) (s : Ω) : Prop :=
  ∀ (dg dh : K → ℕ) (g h : MRing ι) (z : (Σ k, ι k) → ℂ), IsMultiHomog g dg → IsMultiHomog h dh →
    (∀ k, (dg k : ℤ) = dh k + a k) → aeval y g = s * aeval y h → z ∈ mcPts P →
    ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤ c * ‖eval z (map (Int.castRingHom ℂ) h)‖ * hm z
def IsRep (y : (Σ k, ι k) → Ω) (a : K → ℤ) (s : Ω) (g h : MRing ι) : Prop :=
  ∃ dg dh : K → ℕ, IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + a k) ∧
    aeval y h ≠ 0 ∧ aeval y g = s * aeval y h
def NonzeroAtPt (y : (Σ k, ι k) → Ω) (a : K → ℤ) (s : Ω) (z : (Σ k, ι k) → ℂ) : Prop :=
  ∃ g h, IsRep y a s g h ∧ eval z (map (Int.castRingHom ℂ) g) ≠ 0 ∧
    eval z (map (Int.castRingHom ℂ) h) ≠ 0
def NonzeroAtPrime (y : (Σ k, ι k) → Ω) (a : K → ℤ) (s : Ω) (Q : Ideal (MRing ι)) : Prop :=
  ∃ g h, IsRep y a s g h ∧ g ∉ Q ∧ h ∉ Q
def IsGeneratedOnModel (y : (Σ k, ι k) → Ω) (a : K → ℤ) : Prop :=
  ∀ Q : Ideal (MRing ι), Inter.IsClosedPt Q → mCoordIdeal y ≤ Q →
    ∃ s ∈ chartLat y a 1, NonzeroAtPrime y a s Q
def IsGeneratedGeneric (y : (Σ k, ι k) → Ω) (a : K → ℤ) : Prop :=
  ∀ z ∈ mcPts (mCoordIdeal y), ∃ s ∈ chartLat y a 1, NonzeroAtPt y a s z
def IsSemiampleOnFibres (P : Ideal (MRing ι)) (a : K → ℤ) : Prop :=
  ∀ W : Ideal (MRing ι), IsMultiProjPrime W → P ≤ W → charOf W ≠ 0 →
    ∃ j : ℕ, 1 ≤ j ∧ ∀ Q : Ideal (MRing ι), Inter.IsClosedPt Q → W ≤ Q →
      ∃ (g h : MRing ι) (dg dh : K → ℕ), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
        (∀ k, (dg k : ℤ) = dh k + j * a k) ∧ h ∉ W ∧ g ∉ Q ∧ h ∉ Q ∧
        ∀ Q' : Ideal (MRing ι), Inter.IsClosedPt Q' → W ≤ Q' →
          ∃ (g' h' : MRing ι) (dg' dh' : K → ℕ), IsMultiHomog g' dg' ∧ IsMultiHomog h' dh' ∧
            (∀ k, (dg' k : ℤ) = dh' k + j * a k) ∧ h' ∉ Q' ∧ g * h' - g' * h ∈ W
def IsBig (y : (Σ k, ι k) → Ω) (a : K → ℤ) (D : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ j : ℕ, 1 ≤ j ∧ ∀ᶠ n : ℕ in atTop, ∃ (r : ℕ) (s : Fin r → Ω),
    c * (n : ℝ) ^ D ≤ (r : ℝ) ∧ LinearIndependent ℤ s ∧ ∀ i, s i ∈ chartLat y a (j * n)
def IsAmpleGeneric (P : Ideal (MRing ι)) (A : HermLine ι) : Prop :=
  ∀ (W : Ideal (MRing ι)) (d : ℕ), 1 ≤ d → IsArithVar W (d + 1) → P ≤ W → 0 < geomDeg W A d
def IsAmpleOnFibres (P : Ideal (MRing ι)) (a : K → ℤ) : Prop :=
  ∀ (W : Ideal (MRing ι)) (d : ℕ), 1 ≤ d → IsMultiProjPrime W → P ≤ W → charOf W ≠ 0 →
    ringKrullDim (MRing ι ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
    0 < geoNum d W (fun _ ↦ a)
def IsVeryAmpleGeneric (y : (Σ k, ι k) → Ω) (a : K → ℤ) : Prop :=
  IsGeneratedGeneric y a ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ s ∈ chartLat y a n, ∃ N : ℕ, 0 < N ∧
    (N : Ω) * s ∈ (Submodule.span ℤ (chartLat y a 1 : Set Ω)) ^ n
structure IsGoodDatum (y : (Σ k, ι k) → Ω) (D : ℕ) (P₀ : Ideal (MRing ι)) (A : HermLine ι) : Prop where
  gen : IsGeneratedGeneric y A.a
  big : IsBig y A.a D
  le : P₀ ≤ mCoordIdeal y
  semipos : IsSemipositiveRel P₀ (mCoordIdeal y) A
  semiample : IsSemiampleOnFibres (mCoordIdeal y) A.a
structure IsSmallGenerated (y : (Σ k, ι k) → Ω) (D : ℕ) (P₀ : Ideal (MRing ι)) (A : HermLine ι) :
    Prop where
  nonneg : ∀ k, 0 ≤ A.a k
  gens : ∃ (q : ℕ) (w : Fin q → MRing ι), (∀ j, IsMultiHomog (w j) fun k ↦ (A.a k).toNat) ∧
    (∀ Q : Ideal (MRing ι), IsMultiProjPrime Q → mCoordIdeal y ≤ Q → ∃ j, w j ∉ Q) ∧
    ∀ j, ∀ z ∈ mcPts (mCoordIdeal y), ‖eval z (map (Int.castRingHom ℂ) (w j))‖ ≤ A.h z
  le : P₀ ≤ mCoordIdeal y
  semipos : IsSemipositiveRel P₀ (mCoordIdeal y) A
  big : IsBig y A.a D
def hHat0 (y : (Σ k, ι k) → Ω) (A : HermLine ι) (n : ℕ) : ℝ :=
  smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n
def volHat (y : (Σ k, ι k) → Ω) (A : HermLine ι) (D : ℕ) : ℝ :=
  arVolP (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) 1 D
def PtDominated (y : (Σ k, ι k) → Ω) (a b : K → ℤ) (ha hb : ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ)
    (s t : Ω) (z : (Σ k, ι k) → ℂ) : Prop :=
  ∀ g h g' h' : MRing ι, IsRep y a s g h → IsRep y b t g' h' →
    eval z (map (Int.castRingHom ℂ) h) ≠ 0 → eval z (map (Int.castRingHom ℂ) h') ≠ 0 →
    ‖eval z (map (Int.castRingHom ℂ) g')‖ / (‖eval z (map (Int.castRingHom ℂ) h')‖ * hb z) ≤
      c * (‖eval z (map (Int.castRingHom ℂ) g)‖ / (‖eval z (map (Int.castRingHom ℂ) h)‖ * ha z))
end Block
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel


