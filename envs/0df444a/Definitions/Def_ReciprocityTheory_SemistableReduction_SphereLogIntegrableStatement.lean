-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
-- name    : ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:38:25.085881+00:00
-- url     : https://prove2.me/theorems/124bf545-5a84-49ae-9b6d-f71b754c80a2
-- title:
--   Sphere Log Integrable Statement
-- statement:
--   Definitions and structural lemmas for Sphere Log Integrable Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SphereLogIntegrableStatement.lean

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
namespace ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric NumberField
abbrev UnitSphereC (n : ℕ) : Type := sphere (0 : EuclideanSpace ℂ (Fin n)) 1
def sphereProb (n : ℕ) : Measure (UnitSphereC n) :=
  ProbabilityTheory.cond (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ
instance (n : ℕ) : IsZeroOrProbabilityMeasure (sphereProb n) := by
  unfold sphereProb; infer_instance
def spherePoint {n : ℕ} (z : UnitSphereC n) : Fin n → ℂ :=
  WithLp.ofLp (z : EuclideanSpace ℂ (Fin n))
abbrev BlockSphere (B n : ℕ) : Type := Fin B → UnitSphereC n
def blockSphereProb (B n : ℕ) : Measure (BlockSphere B n) :=
  Measure.pi fun _ => sphereProb n
def blockPoint {B n : ℕ} (z : BlockSphere B n) : Fin B × Fin n → ℂ :=
  fun p => spherePoint (z p.1) p.2
def blockSphereMean (B n : ℕ) (f : MvPolynomial (Fin B × Fin n) ℂ) : ℝ :=
  ∫ z, Real.log ‖MvPolynomial.eval (blockPoint z) f‖ ∂(blockSphereProb B n)
def IsMultiHomogeneous {R : Type*} [CommSemiring R] {B n : ℕ} (a : Fin B → ℕ)
    (f : MvPolynomial (Fin B × Fin n) R) : Prop :=
  ∀ s ∈ f.support, ∀ b : Fin B, ∑ j : Fin n, s (b, j) = a b
def gaussAbs {K : Type*} [Field K] [NumberField K] {ι : Type*} (w : FinitePlace K)
    (f : MvPolynomial ι K) : ℝ :=
  ((f.support.sup fun s => (w (f.coeff s)).toNNReal : NNReal) : ℝ)
def h0 {K : Type*} [Field K] [NumberField K] {B n : ℕ} (f : MvPolynomial (Fin B × Fin n) K) : ℝ :=
  ((∑ᶠ w : FinitePlace K, Real.log (gaussAbs w f)) +
      ∑ σ : K →+* ℂ, blockSphereMean B n (MvPolynomial.map σ f)) / (Module.finrank ℚ K : ℝ)
def SphereLinLogStatement : Prop :=
  ∀ (n : ℕ) (c : EuclideanSpace ℂ (Fin n)), c ≠ 0 →
    Integrable (fun z : UnitSphereC n => Real.log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖)
        (sphereProb n) ∧
      ∫ z, Real.log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖ ∂(sphereProb n) =
        Real.log ‖c‖ - (harmonic (n - 1) : ℝ) / 2
def SJStatement : Prop :=
  ∀ (n a : ℕ) (f : MvPolynomial (Fin n) ℂ) (u : EuclideanSpace ℂ (Fin n)),
    f.IsHomogeneous a → ‖u‖ = 1 → MvPolynomial.eval (WithLp.ofLp u) f ≠ 0 →
    Integrable (fun z : UnitSphereC n => Real.log ‖MvPolynomial.eval (spherePoint z) f‖)
        (sphereProb n) ∧
      Real.log ‖MvPolynomial.eval (WithLp.ofLp u) f‖ - (a : ℝ) / 2 * (harmonic (n - 1) : ℝ) ≤
        ∫ z, Real.log ‖MvPolynomial.eval (spherePoint z) f‖ ∂(sphereProb n)
def SphereLogIntegrableStatement : Prop :=
  ∀ (B n : ℕ) (a : Fin B → ℕ) (f : MvPolynomial (Fin B × Fin n) ℂ),
    f ≠ 0 → IsMultiHomogeneous a f →
    Integrable (fun z => Real.log ‖MvPolynomial.eval (blockPoint z) f‖) (blockSphereProb B n)
def RootLogBoundStatement : Prop :=
  ∀ (p : Polynomial ℂ) (A : ℝ), p.Monic → (∀ k, Real.posLog ‖p.coeff k‖ ≤ A) →
    (p.roots.map fun r => Real.posLog ‖r‖).sum ≤ (p.natDegree : ℝ) * (Real.log 2 + A)
def HeightAdditiveStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (B n : ℕ) (a a' : Fin B → ℕ)
    (f g : MvPolynomial (Fin B × Fin n) K),
    0 < n → f ≠ 0 → g ≠ 0 → IsMultiHomogeneous a f → IsMultiHomogeneous a' g →
    h0 (f * g) = h0 f + h0 g ∧ ∀ c : K, c ≠ 0 → h0 (MvPolynomial.C c * f) = h0 f
def HeightLowerBoundStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (B n : ℕ) (a : Fin B → ℕ)
    (f : MvPolynomial (Fin B × Fin n) K),
    0 < n → f ≠ 0 → IsMultiHomogeneous a f →
    -(∑ b, (a b : ℝ) * (Real.log n + 1 / 2)) ≤ h0 f
def heightQuotient {K : Type*} [Field K] [NumberField K] {B n : ℕ}
    (f g : MvPolynomial (Fin B × Fin n) K) : ℝ :=
  h0 f - h0 g
def HeightQuotientStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (B n : ℕ) (a b a' b' : Fin B → ℕ)
    (f g f' g' : MvPolynomial (Fin B × Fin n) K),
    0 < n → f ≠ 0 → g ≠ 0 → f' ≠ 0 → g' ≠ 0 →
    IsMultiHomogeneous a f → IsMultiHomogeneous b g →
    IsMultiHomogeneous a' f' → IsMultiHomogeneous b' g' →
    f * g' = f' * g → heightQuotient f g = heightQuotient f' g'
def torusProb (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ => volume.restrict (Set.Ioc (0 : ℝ) 1)
def torusPoint {ι : Type*} (θ : ι → ℝ) : ι → ℂ :=
  fun i => Complex.exp (2 * Real.pi * Complex.I * (θ i : ℂ))
def torusMean {ι : Type*} [Fintype ι] (f : MvPolynomial ι ℂ) : ℝ :=
  ∫ θ, Real.log ‖MvPolynomial.eval (torusPoint θ) f‖ ∂(torusProb ι)
def coeffIn {R : Type*} [CommSemiring R] {ι : Type*} (i : ι) (k : ℕ) (f : MvPolynomial ι R) :
    MvPolynomial ι R :=
  ∑ s ∈ f.support.filter (fun s => s i = k), MvPolynomial.monomial (s.erase i) (f.coeff s)
def polyL2 {ι : Type*} (f : MvPolynomial ι ℂ) : ℝ :=
  Real.sqrt (∑ s ∈ f.support, ‖f.coeff s‖ ^ 2)
def polyInner {ι : Type*} (P Q : MvPolynomial ι ℂ) : ℂ :=
  ∑ s ∈ P.support, P.coeff s * star (Q.coeff s)
def TorusMeanBasicStatement : Prop :=
  ∀ (ι : Type) [Fintype ι],
    (∀ f : MvPolynomial ι ℂ, f ≠ 0 →
      Integrable (fun θ => Real.log ‖MvPolynomial.eval (torusPoint θ) f‖) (torusProb ι)) ∧
    (∀ f g : MvPolynomial ι ℂ, f ≠ 0 → g ≠ 0 → torusMean (f * g) = torusMean f + torusMean g) ∧
    (∀ (s : ι →₀ ℕ) (c : ℂ), torusMean (MvPolynomial.monomial s c) = Real.log ‖c‖)
def TorusCoeffStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] (f : MvPolynomial ι ℂ) (i : ι) (k : ℕ), coeffIn i k f ≠ 0 →
    ((∀ k', k < k' → coeffIn i k' f = 0) ∨ (∀ k', k' < k → coeffIn i k' f = 0)) →
    torusMean (coeffIn i k f) ≤ torusMean f
def TorusLexStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [LinearOrder ι] (f : MvPolynomial ι ℂ) (s : ι →₀ ℕ), s ∈ f.support →
    (∀ t ∈ f.support, t ≠ s → ∃ i, (∀ j < i, s j = t j) ∧ s i < t i) →
    Real.log ‖f.coeff s‖ ≤ torusMean f
def TorusL2Cauchy : Prop :=
  ∀ (ι : Type) [Fintype ι] (f : MvPolynomial ι ℂ),
    (f ≠ 0 → torusMean f ≤ Real.log (polyL2 f)) ∧
    ∀ s : ι →₀ ℕ, ∃ θ : ι → ℝ, ‖f.coeff s‖ ≤ ‖MvPolynomial.eval (torusPoint θ) f‖
def GramStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : MvPolynomial ι ℂ) (S : Finset (ι →₀ ℕ)), F ≠ 0 →
    Real.exp (2 * S.card * torusMean F) ≤
      (Matrix.det (Matrix.of fun m m' : S =>
        polyInner (F * MvPolynomial.monomial (m : ι →₀ ℕ) 1)
          (F * MvPolynomial.monomial (m' : ι →₀ ℕ) 1))).re
def SphereLeTorusStatement : Prop :=
  ∀ (B n : ℕ) (a : Fin B → ℕ) (f : MvPolynomial (Fin B × Fin n) ℂ),
    0 < n → f ≠ 0 → IsMultiHomogeneous a f → blockSphereMean B n f ≤ torusMean f
end ReciprocityTheory.MultiplicativeHeights


