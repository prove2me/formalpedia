-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SphereBlockLogMean
-- name    : Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SphereBlockLogMean
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:06.148961+00:00
-- url     : https://prove2.me/theorems/568672d8-e24e-4faa-a75c-5df7a9874ec0
-- title:
--   Sphere Block Log Mean
-- statement:
--   Definitions and structural lemmas for Sphere Block Log Mean, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SphereBlockLogMean.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory NumberField MvPolynomial
open scoped ENNReal NNReal Pointwise
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure
abbrev UnitSphere (N : ℕ) : Type :=
  Metric.sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1
def sphereSurface (N : ℕ) : Measure (UnitSphere N) :=
  (volume : Measure (EuclideanSpace ℂ (Fin (N + 1)))).toSphere
def sphereMeasure (N : ℕ) : Measure (UnitSphere N) :=
  (sphereSurface N Set.univ)⁻¹ • sphereSurface N
instance sphereSurface_finite (N : ℕ) : IsFiniteMeasure (sphereSurface N) := by
  unfold sphereSurface; infer_instance
instance sphereSurface_neZero (N : ℕ) : NeZero (sphereSurface N) := by
  refine ⟨fun h => ?_⟩
  have := (Measure.toSphere_eq_zero_iff _).1 h
  exact not_subsingleton _ this
instance sphereMeasure_isProbabilityMeasure (N : ℕ) : IsProbabilityMeasure (sphereMeasure N) := by
  unfold sphereMeasure; infer_instance
def sphereMap {N : ℕ}
    (e : EuclideanSpace ℂ (Fin (N + 1)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (N + 1)))
    (z : UnitSphere N) : UnitSphere N :=
  ⟨e z.1, by simpa using z.2⟩
def blockSphereMeasure (B N : ℕ) : Measure (Fin B → UnitSphere N) :=
  Measure.pi fun _ => sphereMeasure N
instance blockSphereMeasure_isProbabilityMeasure (B N : ℕ) :
    IsProbabilityMeasure (blockSphereMeasure B N) := by
  unfold blockSphereMeasure; infer_instance
def sphereLogAbs {N : ℕ} (f : MvPolynomial (Fin (N + 1)) ℂ) (z : UnitSphere N) : ℝ :=
  Real.log ‖eval (fun j => z.1 j) f‖
def sphereLogMean {N : ℕ} (f : MvPolynomial (Fin (N + 1)) ℂ) : ℝ :=
  ∫ z, sphereLogAbs f z ∂sphereMeasure N
def blockLogAbs {B N : ℕ} (P : MvPolynomial (Fin B × Fin (N + 1)) ℂ)
    (T : Fin B → UnitSphere N) : ℝ :=
  Real.log ‖eval (fun i => (T i.1).1 i.2) P‖
def blockLogMean {B N : ℕ} (P : MvPolynomial (Fin B × Fin (N + 1)) ℂ) : ℝ :=
  ∫ T, blockLogAbs P T ∂blockSphereMeasure B N
def IsBlockHomogeneous {R : Type} [CommSemiring R] {B n : ℕ}
    (ω : MvPolynomial (Fin B × Fin n) R) (a : Fin B → ℕ) : Prop :=
  ∀ d : Fin B × Fin n →₀ ℕ, coeff d ω ≠ 0 → ∀ b : Fin B, ∑ j : Fin n, d (b, j) = a b
section NumberField
variable {K : Type} [Field K] [NumberField K]
def gaussAbsValue {ι : Type} (w : FinitePlace K) (ω : MvPolynomial ι K) : ℝ :=
  ((ω.support.sup fun d => Real.toNNReal (w (coeff d ω)) : ℝ≥0) : ℝ)
theorem exists_gaussAbsValue_eq {ι : Type} (w : FinitePlace K) {ω : MvPolynomial ι K}
    (h : ω ≠ 0) : ∃ d ∈ ω.support, gaussAbsValue w ω = w (coeff d ω) := by
  obtain ⟨d, hd, e⟩ := Finset.exists_mem_eq_sup ω.support (support_nonempty.2 h)
    fun d => Real.toNNReal (w (coeff d ω))
  exact ⟨d, hd, by rw [gaussAbsValue, e, Real.coe_toNNReal _ (apply_nonneg w _)]⟩
def heightZero {B N : ℕ} (ω : MvPolynomial (Fin B × Fin (N + 1)) K) : ℝ :=
  ((∑ᶠ w : FinitePlace K, Real.log (gaussAbsValue w ω)) +
    ∑ σ : K →+* ℂ, blockLogMean (MvPolynomial.map σ ω)) / (Module.finrank ℚ K : ℝ)
end NumberField
def hermitianLinearForm {N : ℕ} (u : EuclideanSpace ℂ (Fin (N + 1))) :
    MvPolynomial (Fin (N + 1)) ℂ :=
  ∑ j, X j * C (starRingEnd ℂ (u j))
def LogAbsIntegrable : Prop :=
  (∀ (N a : ℕ) (f : MvPolynomial (Fin (N + 1)) ℂ), f ≠ 0 → f.IsHomogeneous a →
    (∀ᵐ z ∂sphereMeasure N, eval (fun j => z.1 j) f ≠ 0) ∧
      Integrable (sphereLogAbs f) (sphereMeasure N)) ∧
  ∀ (B N : ℕ) (a : Fin B → ℕ) (P : MvPolynomial (Fin B × Fin (N + 1)) ℂ), P ≠ 0 →
    IsBlockHomogeneous P a →
    (∀ᵐ T ∂blockSphereMeasure B N, eval (fun i => (T i.1).1 i.2) P ≠ 0) ∧
      Integrable (blockLogAbs P) (blockSphereMeasure B N)
def GaussAbsValueMul : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (B N : ℕ) (w : FinitePlace K)
    (ω ω' : MvPolynomial (Fin B × Fin (N + 1)) K),
    gaussAbsValue w (ω * ω') = gaussAbsValue w ω * gaussAbsValue w ω'
def HeightZeroAdditive : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (B N : ℕ) (a a' : Fin B → ℕ)
    (ω ω' : MvPolynomial (Fin B × Fin (N + 1)) K), ω ≠ 0 → ω' ≠ 0 →
    IsBlockHomogeneous ω a → IsBlockHomogeneous ω' a' →
    heightZero (ω * ω') = heightZero ω + heightZero ω'
def HeightZeroScaleInvariant : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (B N : ℕ) (a : Fin B → ℕ) (c : K)
    (ω : MvPolynomial (Fin B × Fin (N + 1)) K), c ≠ 0 → ω ≠ 0 → IsBlockHomogeneous ω a →
    heightZero (C c * ω) = heightZero ω
def HeightZeroOnFractions : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (B N : ℕ) (a b a' b' : Fin B → ℕ)
    (p q p' q' : MvPolynomial (Fin B × Fin (N + 1)) K), p ≠ 0 → q ≠ 0 → p' ≠ 0 → q' ≠ 0 →
    IsBlockHomogeneous p a → IsBlockHomogeneous q b →
    IsBlockHomogeneous p' a' → IsBlockHomogeneous q' b' → p * q' = p' * q →
    heightZero p - heightZero q = heightZero p' - heightZero q'
def SphericalJensen : Prop :=
  ∀ N : ℕ,
    (∀ (a : ℕ) (f : MvPolynomial (Fin (N + 1)) ℂ) (u : EuclideanSpace ℂ (Fin (N + 1))),
      f.IsHomogeneous a → ‖u‖ = 1 → eval (fun j => u j) f ≠ 0 →
      Integrable (sphereLogAbs f) (sphereMeasure N) ∧
        Real.log ‖eval (fun j => u j) f‖ - (a : ℝ) / 2 * (harmonic N : ℝ) ≤ sphereLogMean f) ∧
    (∀ (a : ℕ) (u : EuclideanSpace ℂ (Fin (N + 1))), ‖u‖ = 1 →
      sphereLogMean (hermitianLinearForm u ^ a) =
        Real.log ‖eval (fun j => u j) (hermitianLinearForm u ^ a)‖ -
          (a : ℝ) / 2 * (harmonic N : ℝ)) ∧
    ∀ u : EuclideanSpace ℂ (Fin (N + 1)), u ≠ 0 →
      sphereLogMean (hermitianLinearForm u) = Real.log ‖u‖ - (harmonic N : ℝ) / 2
def HeightZeroLowerBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (B N : ℕ) (a : Fin B → ℕ)
    (ω : MvPolynomial (Fin B × Fin (N + 1)) K), ω ≠ 0 → IsBlockHomogeneous ω a →
    -∑ b, (a b : ℝ) * (Real.log (N + 1 : ℕ) + 1 / 2) ≤ heightZero ω ∧
    -((B : ℝ) * ((Finset.univ.sup a : ℕ) : ℝ) * (Real.log (N + 1 : ℕ) + 1 / 2)) ≤
      -∑ b, (a b : ℝ) * (Real.log (N + 1 : ℕ) + 1 / 2)
def HeightZeroStatements : Prop :=
  LogAbsIntegrable ∧ GaussAbsValueMul ∧ HeightZeroAdditive ∧ HeightZeroScaleInvariant ∧
    HeightZeroOnFractions ∧ SphericalJensen ∧ HeightZeroLowerBound
example (B n : ℕ) (b₀ : Fin B) (j₀ : Fin n) :
    IsBlockHomogeneous (X (b₀, j₀) : MvPolynomial (Fin B × Fin n) ℚ) (Pi.single b₀ 1) := by
  intro d hd b
  rw [coeff_X'] at hd
  have : Finsupp.single (b₀, j₀) 1 = d := by
    by_contra h; exact hd (if_neg h)
  subst this
  by_cases hb : b = b₀
  · subst hb; simp [Finsupp.single_apply, eq_comm]
  · simp [Finsupp.single_apply, hb, Ne.symm hb]
example (K : Type) [Field K] [NumberField K] (B N : ℕ) :
    heightZero (1 : MvPolynomial (Fin B × Fin (N + 1)) K) = 0 := by
  have h : ∀ w : FinitePlace K,
      gaussAbsValue w (1 : MvPolynomial (Fin B × Fin (N + 1)) K) = 1 := by
    intro w
    obtain ⟨d, hd, e⟩ := exists_gaussAbsValue_eq w
      (one_ne_zero : (1 : MvPolynomial (Fin B × Fin (N + 1)) K) ≠ 0)
    rw [mem_support_iff, coeff_one] at hd
    rw [e, coeff_one, if_pos (by by_contra h; exact hd (if_neg h)), map_one]
  simp [heightZero, h, blockLogMean, blockLogAbs]
end GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure


