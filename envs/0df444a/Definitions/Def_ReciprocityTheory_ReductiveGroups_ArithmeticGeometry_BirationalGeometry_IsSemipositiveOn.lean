-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:14.757807+00:00
-- url     : https://prove2.me/theorems/9fc8af06-0536-4818-adff-6cf275b20b46
-- title:
--   Is Semipositive On
-- statement:
--   Definitions and structural lemmas for Is Semipositive On, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/IsSemipositiveOn.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
section Coord
variable (o : Type*) {Ω : Type*} [CommRing o] [CommRing Ω] [Algebra o Ω] {ι : Type*}
def coneMap (x : ι → Ω) : MvPolynomial (ι) o →ₐ[o] Polynomial Ω :=
  aeval fun i => Polynomial.C (x i) * Polynomial.X
def coneRing (x : ι → Ω) : Subalgebra o (Polynomial Ω) :=
  (coneMap o x).range
def coordIdeal (x : ι → Ω) : Ideal (MvPolynomial (ι) o) :=
  RingHom.ker (coneMap o x)
def sec (x : ι → Ω) (d : ℕ) : Submodule o Ω :=
  (homogeneousSubmodule (ι) o d).map
    (aeval x : MvPolynomial (ι) o →ₐ[o] Ω).toLinearMap
def secNm (x : ι → Ω) (d : ℕ) : Submodule o Ω :=
  ((integralClosure (coneRing o x) (Polynomial Ω)).restrictScalars o).toSubmodule.comap
    ((Polynomial.monomial d).restrictScalars o)
def gradedPiece (I : Ideal (MvPolynomial (ι) o)) (d : ℕ) :
    Submodule o (MvPolynomial (ι) o ⧸ I) :=
  (homogeneousSubmodule (ι) o d).map (Ideal.Quotient.mkₐ o I).toLinearMap
def IsHomogIdeal (I : Ideal (MvPolynomial (ι) o)) : Prop :=
  ∀ f ∈ I, ∀ d, homogeneousComponent d f ∈ I
end Coord
section Points
variable {o : Type*} [CommRing o] {C : Type*} [NormedField C] {ι : Type*}
def conePts (σ : o →+* C) (I : Ideal (MvPolynomial (ι) o)) : Set (ι → C) :=
  {z | z ≠ 0 ∧ ∀ f ∈ I, eval z (map σ f) = 0}
variable (C ι) in

structure ConeMetric where

  ρ : (ι → C) → ℝ
  pos : ∀ z, z ≠ 0 → 0 < ρ z
  smul : ∀ (c : C) (z : ι → C), ρ (c • z) = ‖c‖ * ρ z
variable (C ι) in

def maxMetric [Fintype ι] : ConeMetric C ι where
  ρ z := ‖z‖
  pos _ hz := norm_pos_iff.mpr hz
  smul c z := norm_smul c z
variable (ι) in

def fsMetric [Fintype ι] : ConeMetric ℂ ι where
  ρ z := ‖WithLp.toLp 2 z‖
  pos _ hz := norm_pos_iff.mpr (by simpa using hz)
  smul c z := by rw [WithLp.toLp_smul, norm_smul]
def ptNorm (m : ConeMetric C ι) (σ : o →+* C) (d : ℕ) (f : MvPolynomial (ι) o)
    (z : ι → C) : ℝ :=
  ‖eval z (map σ f)‖ / m.ρ z ^ d
def supNorm (m : ConeMetric C ι) (σ : o →+* C) (I : Ideal (MvPolynomial (ι) o))
    (d : ℕ) (f : MvPolynomial (ι) o) : ℝ :=
  sSup (ptNorm m σ d f '' conePts σ I)
def IsPtsMeasure [Fintype ι] (m : ConeMetric ℂ ι) (σ : o →+* ℂ) (I : Ideal (MvPolynomial (ι) o))
    (μ : MeasureTheory.Measure (ι → ℂ)) : Prop :=
  MeasureTheory.IsProbabilityMeasure μ ∧ μ (conePts σ I ∩ {z | m.ρ z = 1})ᶜ = 0
def l2Norm [Fintype ι] (m : ConeMetric ℂ ι) (σ : o →+* ℂ) (μ : MeasureTheory.Measure (ι → ℂ))
    (d : ℕ) (f : MvPolynomial (ι) o) : ℝ :=
  Real.sqrt (∫ z, ptNorm m σ d f z ^ 2 ∂μ)
def IsConjInvariant (m : ConeMetric ℂ ι) : Prop :=
  ∀ z, m.ρ (fun i => (starRingEnd ℂ) (z i)) = m.ρ z
end Points
section Heights
def coeffGaussNorm {K ι : Type*} [Field K] (v : AbsoluteValue K ℝ) (f : MvPolynomial ι K) : ℝ :=
  ⨆ m : f.support, v (f.coeff m)
def hgt {K ι : Type*} [Field K] [NumberField K] (y : ι → K) : ℝ :=
  Height.logHeight y / Height.totalWeight K
end Heights
section Curvature
variable {ι : Type*} [Fintype ι]
def IsSmoothMetric (m : ConeMetric ℂ ι) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m.ρ {z | z ≠ 0}
def leviForm (φ : (ι → ℂ) → ℝ) (z w : ι → ℂ) : ℝ :=
  (fderiv ℝ (fderiv ℝ φ) z w w + fderiv ℝ (fderiv ℝ φ) z (Complex.I • w) (Complex.I • w)) / 4
def IsSemipositive (m : ConeMetric ℂ ι) : Prop :=
  IsSmoothMetric m ∧ ∀ z, z ≠ 0 → ∀ w, 0 ≤ leviForm (fun z => Real.log (m.ρ z)) z w
end Curvature
section Chow
open NumberField
variable {e n : ℕ}
def IsMultihomog {K : Type*} [CommSemiring K] (P : MvPolynomial (Fin (e + 1) × Fin n) K) (δ : ℕ) :
    Prop :=
  ∀ m ∈ P.support, ∀ k, ∑ j, m (k, j) = δ
def logMean (μ : MeasureTheory.Measure (Fin (e + 1) × Fin n → ℂ))
    (P : MvPolynomial (Fin (e + 1) × Fin n) ℂ) : ℝ :=
  ∫ u, Real.log ‖eval u P‖ ∂μ
def chowHeightOfForm {K : Type*} [Field K] [NumberField K]
    (μ : InfinitePlace K → MeasureTheory.Measure (Fin (e + 1) × Fin n → ℂ))
    (P : MvPolynomial (Fin (e + 1) × Fin n) K) : ℝ :=
  ((∑ᶠ v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K), Real.log (coeffGaussNorm v.1 P)) +
    ∑ w : InfinitePlace K, (w.mult : ℝ) * logMean (μ w) (map w.embedding P)) /
    Height.totalWeight K
def chowHt {K : Type*} [Field K] [NumberField K]
    (μ : InfinitePlace K → MeasureTheory.Measure (Fin (e + 1) × Fin n → ℂ))
    (P : MvPolynomial (Fin (e + 1) × Fin n) K) (δ : ℕ) : ℝ :=
  chowHeightOfForm μ P + (e + 1 : ℝ) * δ * (harmonic (n - 1) : ℝ) / 2
end Chow
section MetrisedHeight
open NumberField
variable {ι : Type*}
def ptHeight {K : Type*} [Field K] [NumberField K] [Fintype ι] (m : InfinitePlace K → ConeMetric ℂ ι)
    (y : ι → K) : ℝ :=
  ((∑ᶠ v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K), Real.log (⨆ i, v.1 (y i))) +
    ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log ((m w).ρ fun i => w.embedding (y i))) /
    Height.totalWeight K
end MetrisedHeight
section SphereMeasure
variable {e n : ℕ}
def groupAct (k : Fin (e + 1)) (U : Matrix (Fin n) (Fin n) ℂ) (u : Fin (e + 1) × Fin n → ℂ) :
    Fin (e + 1) × Fin n → ℂ :=
  fun p => if p.1 = k then U.mulVec (fun j => u (k, j)) p.2 else u p
def IsSphereMeasure (μ : MeasureTheory.Measure (Fin (e + 1) × Fin n → ℂ)) : Prop :=
  MeasureTheory.IsProbabilityMeasure μ ∧ μ {u | ∃ k, ∑ j, ‖u (k, j)‖ ^ 2 ≠ 1} = 0 ∧
    ∀ k, ∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, μ.map (groupAct k U) = μ
end SphereMeasure
section Joins
variable {Ω : Type*} [CommRing Ω] {ι κ : Type*}
def segreJoin (x : ι → Ω) (y : κ → Ω) : ι × κ → Ω := fun p => x p.1 * y p.2
end Joins
section Multi
variable {r : ℕ} {ι : Fin r → Type*} [∀ k, Fintype (ι k)]
def multiPtNorm (m : ∀ k, ConeMetric ℂ (ι k)) (a : Fin r → ℤ)
    (f g : MvPolynomial (Σ k, ι k) ℂ) (z : ∀ k, ι k → ℂ) : ℝ :=
  ‖eval (fun p => z p.1 p.2) f‖ / ‖eval (fun p => z p.1 p.2) g‖ / ∏ k, (m k).ρ (z k) ^ a k
end Multi
section Along
variable {o : Type*} [CommRing o] {ι : Type*} [Fintype ι]
def IsConeTangent (σ : o →+* ℂ) (I : Ideal (MvPolynomial ι o)) (z w : ι → ℂ) : Prop :=
  ∀ f ∈ I, ∑ i, eval z (pderiv i (map σ f)) * w i = 0
def IsSemipositiveOn (m : ConeMetric ℂ ι) (σ : o →+* ℂ) (I : Ideal (MvPolynomial ι o))
    (S : Set (ι → ℂ)) : Prop :=
  IsSmoothMetric m ∧
    ∀ z ∈ S, z ≠ 0 → ∀ w, IsConeTangent σ I z w → 0 ≤ leviForm (fun z => Real.log (m.ρ z)) z w
end Along
section MongeAmpere
variable {D : ℕ}
def cxHessian (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  fun i j =>
    let H := fderiv ℝ (fderiv ℝ φ) z
    let ei : Fin D → ℂ := Pi.single i 1
    let ej : Fin D → ℂ := Pi.single j 1
    ((H ei ej + H (Complex.I • ei) (Complex.I • ej) : ℝ) +
      Complex.I * ((H ei (Complex.I • ej) - H (Complex.I • ei) ej : ℝ))) / 4
def mixedDisc (A : Fin D → Matrix (Fin D) (Fin D) ℂ) : ℂ :=
  (1 / (D.factorial : ℂ)) *
    ∑ S : Finset (Fin D), (-1) ^ (D - S.card) * (∑ k ∈ S, A k).det
def maDensity (φ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) : ℝ :=
  (D.factorial : ℝ) * (2 / Real.pi) ^ D * (mixedDisc fun k => cxHessian (φ k) z).re
def maIntegral (φ : Fin D → (Fin D → ℂ) → ℝ) (g : (Fin D → ℂ) → ℝ) (U : Set (Fin D → ℂ)) : ℝ :=
  ∫ z in U, g z * maDensity φ z
end MongeAmpere
section LatticeDegree
open NumberField ComplexConjugate
variable {ι : Type*} {r : ℕ}
def realGram {K : Type*} [Field K] [NumberField K] (m : InfinitePlace K → ConeMetric ℂ ι)
    (μ : InfinitePlace K → MeasureTheory.Measure (ι → ℂ)) (d : ℕ)
    (b : Fin r → MvPolynomial ι K) : Matrix (Fin r) (Fin r) ℝ :=
  fun k l => ∑ w : InfinitePlace K, (w.mult : ℝ) *
    (∫ z, eval z (map w.embedding (b k)) * conj (eval z (map w.embedding (b l))) /
      (((m w).ρ z ^ (2 * d) : ℝ) : ℂ) ∂μ w).re
def l2Degree {K : Type*} [Field K] [NumberField K] (m : InfinitePlace K → ConeMetric ℂ ι)
    (μ : InfinitePlace K → MeasureTheory.Measure (ι → ℂ)) (d : ℕ)
    (b : Fin r → MvPolynomial ι K) : ℝ :=
  -(Real.log (realGram m μ d b).det / 2) / Height.totalWeight K
end LatticeDegree
end ReciprocityTheory.ChartRestriction.G.Geo


