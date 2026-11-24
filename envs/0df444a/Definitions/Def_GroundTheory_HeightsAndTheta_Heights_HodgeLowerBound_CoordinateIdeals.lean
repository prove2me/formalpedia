-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals
-- name    : GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:02.196273+00:00
-- url     : https://prove2.me/theorems/af28d56f-d3b0-46c8-87cf-66142b0c53e1
-- title:
--   Coordinate Ideals
-- statement:
--   Definitions and structural lemmas for Coordinate Ideals, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix ComplexOrder
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
section Coordinates
variable {Ω : Type} [Field Ω]
def segreCoord (y : (Σ k, ι k) → Ω) : ((k : K) → ι k) → Ω :=
  fun c => ∏ k, y ⟨k, c k⟩
def torusSmul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun p => c p.1 * z p
def conjVec (z : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun p => starRingEnd ℂ (z p)
def IsValueAt (y : (Σ k, ι k) → Ω) (s : Ω) (z : (Σ k, ι k) → ℂ) (v : ℂ) : Prop :=
  ∃ (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧ aeval y h ≠ 0 ∧
    aeval y g = s * aeval y h ∧ eval z (map (Int.castRingHom ℂ) h) ≠ 0 ∧
    v = eval z (map (Int.castRingHom ℂ) g) / eval z (map (Int.castRingHom ℂ) h)
def IsUnitAt (y : (Σ k, ι k) → Ω) (s : Ω) (z : (Σ k, ι k) → ℂ) : Prop :=
  ∃ v, IsValueAt y s z v ∧ v ≠ 0
def InFrameDomain (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (f : Ω) (z : (Σ k, ι k) → ℂ) : Prop :=
  (∀ k, z ⟨k, c k⟩ ≠ 0) ∧ IsUnitAt y f z
end Coordinates
section Frames
variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {N : ℕ}
def IsFrameOver (y : (Σ k, ι k) → Ω) (W : ChartBundle ℤ (segreCoord y) N E)
    (c : (k : K) → ι k) (f : Ω) (b : Fin N → E) : Prop :=
  segreCoord y c ≠ 0 ∧ f ∈ chartRing ℤ (segreCoord y) c ∧ f ≠ 0 ∧ LinearIndependent Ω b ∧
    ∀ e, (∃ n : ℕ, f ^ n • e ∈ W.lat c) ↔
      ∃ a : Fin N → Ω, (∀ q, ∃ n : ℕ, f ^ n * a q ∈ chartRing ℤ (segreCoord y) c) ∧
        e = ∑ q, a q • b q
end Frames
section Charts
structure SncChart (P : Ideal (MRing ι)) (n : ℕ) (Bd : Set ((Σ k, ι k) → ℂ)) where

  γ : (Fin n → ℂ) → (Σ k, ι k) → ℂ

  a : ℕ
  a_le : a ≤ n
  analytic : AnalyticOnNhd ℂ γ (Metric.ball 0 1)
  mem : ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1, γ t ∈ mcPts P
  immersion : ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ v : Fin n → ℂ,
    (∃ c : K → ℂ, fderiv ℂ γ t v = torusSmul c (γ t)) → v = 0
  injective : ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ t' ∈ Metric.ball (0 : Fin n → ℂ) 1,
    ∀ c : K → ℂ, (∀ k, c k ≠ 0) → γ t = torusSmul c (γ t') → t = t'
  boundary : ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1, γ t ∈ Bd ↔ ∃ i : Fin n, (i : ℕ) < a ∧ t i = 0
def SncChart.logR {P : Ideal (MRing ι)} {n : ℕ} {Bd : Set ((Σ k, ι k) → ℂ)} (χ : SncChart P n Bd)
    (t : Fin n → ℂ) : ℝ :=
  Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < χ.a then Real.log (1 / ‖t i‖ ^ 2) else 0
end Charts
section Metric
variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {N : ℕ}
structure HermMetric (y : (Σ k, ι k) → Ω) (W : ChartBundle ℤ (segreCoord y) N E)
    (Xo : Set ((Σ k, ι k) → ℂ)) {P : Ideal (MRing ι)} {n nc : ℕ} {Bd : Set ((Σ k, ι k) → ℂ)}
    (χ : Fin nc → SncChart P n Bd) where

  m : ℕ

  chart : Fin m → (k : K) → ι k

  fr : Fin m → Ω

  b : Fin m → Fin N → E
  isFrame : ∀ l, IsFrameOver y W (chart l) (fr l) (b l)

  gram : Fin m → ((Σ k, ι k) → ℂ) → Matrix (Fin N) (Fin N) ℂ
  cover : ∀ z ∈ Xo, ∃ l, InFrameDomain y (chart l) (fr l) z
  posDef : ∀ l, ∀ z ∈ Xo, InFrameDomain y (chart l) (fr l) z → (gram l z).PosDef
  compat : ∀ l l', ∀ z ∈ Xo, InFrameDomain y (chart l) (fr l) z →
    InFrameDomain y (chart l') (fr l') z →
    ∀ S : Matrix (Fin N) (Fin N) Ω, (∀ q, b l' q = ∑ p, S p q • b l p) →
    ∀ Sz : Matrix (Fin N) (Fin N) ℂ, (∀ p q, IsValueAt y (S p q) z (Sz p q)) →
      gram l' z = Szᴴ * gram l z * Sz
  torus : ∀ l, ∀ z ∈ Xo, InFrameDomain y (chart l) (fr l) z → ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
    gram l (torusSmul c z) = gram l z
  conj : ∀ l, ∀ z ∈ Xo, InFrameDomain y (chart l) (fr l) z →
    gram l (conjVec z) = (gram l z).map (starRingEnd ℂ)
  smooth : ∀ a l, ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1, (χ a).γ t ∈ Xo →
    InFrameDomain y (chart l) (fr l) ((χ a).γ t) → ∀ p q,
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t' => gram l ((χ a).γ t') p q) t
  logBound : ∀ a, ∀ t₀ : Fin n → ℂ, ‖t₀‖ ≤ 1 / 2 →
    ∃ l, InFrameDomain y (chart l) (fr l) ((χ a).γ t₀) ∧
    ∃ ε > (0 : ℝ), ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ t : Fin n → ℂ, ‖t - t₀‖ < ε → ‖t‖ < 1 →
      (χ a).γ t ∈ Xo → InFrameDomain y (chart l) (fr l) ((χ a).γ t) →
      ((gram l ((χ a).γ t))⁻¹ - (c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef ∧
      (((C * (χ a).logR t : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) -
        (gram l ((χ a).γ t))⁻¹).PosSemidef ∧
      ∀ p q, ‖fderiv ℝ (fun t' => gram l ((χ a).γ t') p q) t‖ ≤
        C * Real.exp ((χ a).logR t / 2)
end Metric
section Divisors
structure IsVerticalDivisorAt (P : Ideal (MRing ι)) (p : ℕ) (b : K → ℤ) (f g : MRing ι) :
    Prop where
  degrees : ∃ bf bg : K → ℕ, IsMultiHomog f bf ∧ IsMultiHomog g bg ∧
    (fun k => (bf k : ℤ) - bg k) = b
  num_not_mem : f ∉ P
  den_not_mem : g ∉ P
  unit_off_fibre : ∀ W : Ideal (MRing ι), W.IsPrime → P ≤ W → IsRelevant W →
    (C (p : ℤ) : MRing ι) ∉ W → ∃ u v : MRing ι, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P
end Divisors
section Positive
def IsPositiveRel (P : Ideal (MRing ι)) (A : HermLine ι) : Prop :=
  IsSmoothHerm A ∧ ∀ z ∈ mcPts P, ∀ w, IsConeTangent (Int.castRingHom ℂ) P z w →
    (∀ c : K → ℂ, w ≠ torusSmul c z) → 0 < leviForm (fun z => Real.log (A.h z)) z w
end Positive
structure ComponentData (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type)
    [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] where

  N : ℕ

  j : ℕ
  two_le_N : 2 ≤ N
  one_le_j : 1 ≤ j
  j_le : j ≤ N - 1

  F' : IntermediateField ℚ ℂ
  finiteDimensional : FiniteDimensional ℚ F'

  const : F' →+* Ω

  y : (Σ k, ι k) → Ω
  const_mem : ∀ c : (k : K) → ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ r : F',
    const r ∈ Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)
  arith : IsArithVar (mCoordIdeal y) (Fintype.card Ψ * j * (N - j) + 1)
  birational : Birational y
  smoothGeneric : SmoothGenericFibreM y

  Bd : Set ((Σ k, ι k) → ℂ)
  bd_subset : Bd ⊆ mcPts (mCoordIdeal y)
  bd_closed : IsClosed ((↑) ⁻¹' Bd : Set (mcPts (mCoordIdeal y)))
  bd_torus : ∀ z ∈ Bd, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → torusSmul c z ∈ Bd
  bd_conj : ∀ z ∈ Bd, conjVec z ∈ Bd

  nCharts : ℕ

  chart : Fin nCharts → SncChart (mCoordIdeal y) (Fintype.card Ψ * j * (N - j)) Bd
  chart_cover : ∀ z ∈ mcPts (mCoordIdeal y), ∃ a, ∃ t : Fin (Fintype.card Ψ * j * (N - j)) → ℂ,
    ‖t‖ ≤ 1 / 2 ∧ ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c ((chart a).γ t)

  W : ∀ τ, ChartBundle ℤ (segreCoord y) N (E τ)

  h : ∀ τ, HermMetric y (W τ) (mcPts (mCoordIdeal y) \ Bd) chart

  S : Finset ℕ
  S_prime : ∀ p ∈ S, p.Prime

  vdeg : ℕ → K → ℤ

  vnum : ℕ → MRing ι

  vden : ℕ → MRing ι
  vertical : ∀ p ∈ S, IsVerticalDivisorAt (mCoordIdeal y) p (vdeg p) (vnum p) (vden p)

  a' : K → ℤ
  a'_pos : ∀ k, 0 < a' k

  A' : HermLine ι
  A'_deg : A'.a = a'
  A'_pos : IsPositiveRel (mCoordIdeal y) A'
  A'_conj : IsConjInvariantH A'

  KA : ℝ
  heights : ∀ W : Ideal (MRing ι), IsArithVar W 1 → mCoordIdeal y ≤ W →
    -KA * (degC W : ℝ) ≤ II K ι W 1 ![A']
namespace ComponentData
variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  (D : ComponentData II Ψ K ι Ω E)
def f (_ : ComponentData II Ψ K ι Ω E) : ℕ := Fintype.card Ψ
def j' : ℕ := D.N - D.j
def n : ℕ := Fintype.card Ψ * D.j * (D.N - D.j)
def PX : Ideal (MRing ι) := mCoordIdeal D.y
def Xo : Set ((Σ k, ι k) → ℂ) := mcPts (mCoordIdeal D.y) \ D.Bd
end ComponentData
end GroundTheory.Heights₂.Heights.LowerBoundFree


