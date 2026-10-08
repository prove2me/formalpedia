-- Prove2me | Definitions.Def_OAIErdos3B005
-- name    : OAIErdos3B005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T07:53:31.413639+00:00
-- url     : https://prove2.me/theorems/aff6915e-717c-475f-a237-c386ec31a853
-- title:
--   OpenAI Erdős-3 split, definitions bundle 6 of 132
-- statement:
--   Definitions bundle 6 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B004`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 6 available.
--
--   Modules: `Geometry.BoxDifferenceHom`, `Geometry.ProgressionCoordinateResampling`, `Estimates.PaddedBooleanFeatures`, `Geometry.OperatorCoordinateBound`, `Polynomial.PolynomialAnalyticDerivative`, `Polynomial.PolynomialDeterminantDerivativeBound`, `Sampling.BooleanProductSampler`, `Polynomial.BooleanBlockCoefficientPhase`, `Estimates.RectangularCellGeometry`, `Estimates.SublevelThresholdBalance`, `Estimates.FiniteFiberVolumeBound`, `Estimates.SeparatedInterpolationBound`, `Estimates.SeparatedRealSamples`, `Polynomial.UnivariatePolynomialSublevel`, `Estimates.SymmetricScalarSublevel`, `Polynomial.PolynomialCoordinateSlice`, `Probability.SymmetricCubeMeasure`, `Estimates.SymmetricCubeSublevel`, `Estimates.SymmetricCubeVolume`, `Polynomial.PolynomialDeterminantDegree`, `Geometry.CoordinateDeterminant`, `Polynomial.PolynomialDilation`, `Polynomial.PolynomialValueCoefficient`, `Polynomial.EmbeddedMatrixDeterminantPolynomial`, `Estimates.BooleanMinorDimension`, `Estimates.SmoothHalfspaceCutoff`, `Estimates.ScalarCubeDomain`, `Probability.ScalarCubeDomainDensity`, `Estimates.ScalarCubeBoundaryCost`, `Geometry.ScalarCubeCoordinates`, `Estimates.ScalarCubeBoundaryVolume`, `Probability.ScalarCubeBoundaryMass`, `Estimates.ScalarCubeFaceSlab`, `Probability.ScaledCubeProductMeasure`, `Estimates.ProductCutoffLipschitz`, `Estimates.ResidualErrorAllocation`, `Lattices.ScalarCubeLatticeGeometry`, `Probability.ScalarCubeDensityBudget`, `Dynamics.ScalarCubeBoundaryLogBudget`, `Estimates.UnitTestClipping`, `Polynomial.PolynomialParameterContinuity`, `Estimates.BooleanSelectedDerivativeBound`, `Estimates.BoundedInequalityGoodCutoff`, `Estimates.PrincipalCoefficientSource`, `Geometry.BlockCubeCoordinates`, `Estimates.SigmaAxisOperator`, `Lattices.BooleanAffineInput`, `Estimates.CoefficientNormalization`, `Polynomial.MonomialArrayJet`, `Sampling.CanonicalSamplerTuple`, `Estimates.JointBooleanGoodWeight`, `Probability.FiniteArrayMeasure`, `Probability.DensityMixtureAELaw`, `Probability.RestrictedComplexChartDensityComparison`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B004

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxDifferenceHom
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem expect_prod_split {X Y M : Type*} [Fintype X] [Fintype Y]
    [AddCommMonoid M] [Module ℚ≥0 M] (F : X × Y → M) :
    (𝔼 p, F p) = 𝔼 x, 𝔼 y, F (x,y) := by
  simpa using (Finset.expect_product' (Finset.univ : Finset X)
    (Finset.univ : Finset Y) (fun x y => F (x,y)))

theorem expect_empty_tuple {X : Fin 0 → Type*} [∀ i, Fintype (X i)]
    {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M] (F : (∀ i, X i) → M) :
    (𝔼 x, F x) = F (fun i => Fin.elim0 i) := by
  calc
    (𝔼 x, F x) = 𝔼 _x : ∀ i, X i, F (fun i => Fin.elim0 i) := by
      apply Finset.expect_congr rfl
      intro x _
      congr 1
      exact Subsingleton.elim _ _
    _ = _ := Fintype.expect_const _

theorem expect_two_dependent_fin_cons {n : ℕ} {X : Fin (n+1) → Type*}
    [∀ i, Fintype (X i)] {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M]
    (F : (∀ i, X i) → (∀ i, X i) → M) :
    (𝔼 x, 𝔼 y, F x y) =
      𝔼 a : X 0, 𝔼 b : X 0, 𝔼 u : ∀ i : Fin n, X i.succ,
        𝔼 v : ∀ i : Fin n, X i.succ, F (Fin.cons a u) (Fin.cons b v) := by
  rw [expect_dependent_fin_cons]
  apply Finset.expect_congr rfl
  intro a _
  simp_rw [expect_dependent_fin_cons]
  exact Finset.expect_comm _ _ _

theorem expect_pow_two_pow_le {X : Type*} [Fintype X] [Nonempty X]
    (n : ℕ) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (𝔼 x, f x)^(2^n) ≤ 𝔼 x, (f x)^(2^n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ, pow_mul]
    calc
      ((𝔼 x, f x)^(2^n))^2 ≤ (𝔼 x, (f x)^(2^n))^2 :=
        pow_le_pow_left₀ (pow_nonneg (Finset.expect_nonneg (fun x _ => hf x)) _) ih 2
      _ ≤ 𝔼 x, ((f x)^(2^n))^2 := expect_square_le _

theorem expect_double_pow_two_pow_le {X Y : Type*}
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (n : ℕ) (f : X → Y → ℝ) (hf : ∀ x y, 0 ≤ f x y) :
    (𝔼 x, 𝔼 y, f x y)^(2^n) ≤ 𝔼 x, 𝔼 y, (f x y)^(2^n) := by
  apply (expect_pow_two_pow_le n (fun x => 𝔼 y, f x y)
    (fun x => Finset.expect_nonneg (fun y _ => hf x y))).trans
  exact Finset.expect_le_expect (fun x _ => expect_pow_two_pow_le n (f x) (hf x))

theorem norm_mean_first_difference {X Y : Type*}
    [Fintype X] [Fintype Y] [Nonempty Y] (F : X → Y → ℂ) :
    ‖𝔼 x, 𝔼 y, F x y‖^2 ≤ 𝔼 x, 𝔼 x', ‖𝔼 y, F x y * star (F x' y)‖ := by
  have h := finite_family_cauchy_schwarz (fun _ : Y => (1 : ℂ)) F
    (show ∀ _ : Y, ‖(1 : ℂ)‖ ≤ (1 : ℝ) by intro; norm_num)
  simpa only [one_mul, one_pow, Finset.expect_comm (Finset.univ : Finset Y)
    (Finset.univ : Finset X)] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteBoxCorrelation {X Y : Type*} [Fintype X] [Fintype Y]
    (F : X → Y → ℂ) : ℂ :=
  𝔼 x, 𝔼 x', 𝔼 y, 𝔼 y',
    F x y * star (F x' y) * star (F x y') * F x' y'

theorem finiteBoxCorrelation_re_eq_mean_square {X Y : Type*} [Fintype X] [Fintype Y]
    (F : X → Y → ℂ) :
    (finiteBoxCorrelation F).re = 𝔼 x, 𝔼 x', ‖𝔼 y, F x y * star (F x' y)‖ ^ 2 := by
  unfold finiteBoxCorrelation
  simp_rw [square_norm_mean_eq_cross_re, ← expect_re]
  congr 1
  apply Finset.expect_congr rfl
  intro x _
  apply Finset.expect_congr rfl
  intro x' _
  apply Finset.expect_congr rfl
  intro y _
  apply Finset.expect_congr rfl
  intro y' _
  simp only [star_mul, star_star]
  ring

theorem norm_weighted_expect_sq_le {X : Type*} [Fintype X] [Nonempty X]
    (a f : X → ℂ) (ha : ∀ x, ‖a x‖ ≤ 1) :
    ‖𝔼 x, a x * f x‖ ^ 2 ≤ 𝔼 x, ‖f x‖ ^ 2 := by
  have hcs := norm_expect_mul_star_sq_le a (fun x => star (f x))
  simp only [star_star, norm_star] at hcs
  have ha2 : (𝔼 x, ‖a x‖ ^ 2) ≤ 1 := by
    exact (Finset.expect_le_expect (fun x _ =>
      pow_le_pow_left₀ (norm_nonneg _) (ha x) 2)).trans_eq (by simp)
  exact hcs.trans ((mul_le_mul_of_nonneg_right ha2
    (Finset.expect_nonneg (fun _ _ => sq_nonneg _))).trans_eq (one_mul _))

theorem norm_weighted_pair_mean_pow_four_le_box {X Y : Type*}
    [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (F : X → Y → ℂ) (a : X → ℂ) (b : Y → ℂ)
    (ha : ∀ x, ‖a x‖ ≤ 1) (hb : ∀ y, ‖b y‖ ≤ 1) :
    ‖𝔼 x, 𝔼 y, F x y * a x * b y‖ ^ 4 ≤ (finiteBoxCorrelation F).re := by
  let m : ℂ := 𝔼 x, 𝔼 x', a x * star (a x') * (𝔼 y, F x y * star (F x' y))
  have hleft : (𝔼 y, b y * (𝔼 x, F x y * a x)) = 𝔼 x, 𝔼 y, F x y * a x * b y := by
    simp_rw [Finset.mul_expect]
    rw [Finset.expect_comm]
    apply Finset.expect_congr rfl
    intro x _
    apply Finset.expect_congr rfl
    intro y _
    ring
  have hright : (𝔼 x, 𝔼 x', 𝔼 y, (F x y * a x) * star (F x' y * a x')) = m := by
    dsimp [m]
    simp_rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    apply Finset.expect_congr rfl
    intro x' _
    apply Finset.expect_congr rfl
    intro y _
    rw [map_mul]
    ring
  have hfirst : ‖𝔼 x, 𝔼 y, F x y * a x * b y‖ ^ 2 ≤ m.re := by
    simpa only [hleft, hright, one_pow, one_mul] using
      finite_family_cauchy_schwarz_re b (fun x y => F x y * a x) hb
  have hsecond : ‖m‖ ^ 2 ≤ 𝔼 x, 𝔼 x', ‖𝔼 y, F x y * star (F x' y)‖ ^ 2 := by
    have hh := norm_weighted_expect_sq_le
      (fun u : X × X => a u.1 * star (a u.2))
      (fun u : X × X => 𝔼 y, F u.1 y * star (F u.2 y)) (fun u => by
        rw [norm_mul, norm_star]
        exact (mul_le_of_le_one_left (norm_nonneg _) (ha _)).trans (ha _))
    simpa only [← Finset.univ_product_univ, Finset.expect_product, m] using hh
  have hm : 0 ≤ m.re := (sq_nonneg _).trans hfirst
  calc
    _ = (‖𝔼 x, 𝔼 y, F x y * a x * b y‖ ^ 2) ^ 2 := by ring
    _ ≤ m.re ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hfirst 2
    _ ≤ ‖m‖ ^ 2 := pow_le_pow_left₀ hm (Complex.re_le_norm m) 2
    _ ≤ _ := hsecond.trans_eq (finiteBoxCorrelation_re_eq_mean_square F).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def iteratedBoxDifference {Z : Type*} :
    (n : ℕ) → {X : Fin n → Type*} → ((∀ i, X i) → Z → ℂ) →
      (∀ i, X i) → (∀ i, X i) → Z → ℂ
  | 0, _, F, _, _, z => F (fun i => Fin.elim0 i) z
  | n+1, _, F, u, v, z => iteratedBoxDifference n
      (fun x z => F (Fin.cons (u 0) x) z * star (F (Fin.cons (v 0) x) z))
      (Fin.tail u) (Fin.tail v) z

theorem iterated_box_cauchy_schwarz (n : ℕ) {X : Fin n → Type*}
    [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    {Z : Type*} [Fintype Z] [Nonempty Z] (F : (∀ i, X i) → Z → ℂ) :
    ‖𝔼 x, 𝔼 z, F x z‖^(2^n) ≤
      𝔼 u, 𝔼 v, ‖𝔼 z, iteratedBoxDifference n F u v z‖ := by
  induction n with
  | zero => simp only [pow_zero, pow_one, expect_empty_tuple, iteratedBoxDifference, le_refl]
  | succ n ih =>
    let G := fun a b (x : ∀ i : Fin n, X i.succ) z =>
      F (Fin.cons a x) z * star (F (Fin.cons b x) z)
    have hcs : ‖𝔼 x, 𝔼 z, F x z‖^2 ≤
        𝔼 a : X 0, 𝔼 b : X 0, ‖𝔼 x : ∀ i : Fin n, X i.succ, 𝔼 z, G a b x z‖ := by
      rw [expect_dependent_fin_cons]
      have h := norm_mean_first_difference
        (fun (a : X 0) (p : (∀ i : Fin n, X i.succ) × Z) => F (Fin.cons a p.1) p.2)
      simpa only [expect_prod_split] using h
    calc
      _ = (‖𝔼 x, 𝔼 z, F x z‖^2)^(2^n) := by rw [← pow_mul, pow_succ]; congr 1; omega
      _ ≤ (𝔼 a : X 0, 𝔼 b : X 0,
          ‖𝔼 x : ∀ i : Fin n, X i.succ, 𝔼 z, G a b x z‖)^(2^n) :=
        pow_le_pow_left₀ (sq_nonneg _) hcs _
      _ ≤ 𝔼 a : X 0, 𝔼 b : X 0,
          ‖𝔼 x : ∀ i : Fin n, X i.succ, 𝔼 z, G a b x z‖^(2^n) :=
        expect_double_pow_two_pow_le n _ (fun _ _ => norm_nonneg _)
      _ ≤ 𝔼 a : X 0, 𝔼 b : X 0, 𝔼 u : ∀ i : Fin n, X i.succ,
          𝔼 v : ∀ i : Fin n, X i.succ, ‖𝔼 z, iteratedBoxDifference n (G a b) u v z‖ := by
        apply Finset.expect_le_expect
        intro a _
        apply Finset.expect_le_expect
        intro b _
        exact ih (G a b)
      _ = _ := by
        rw [expect_two_dependent_fin_cons]
        rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def boxSlice {X : Type*} (a z : Fin 2 → X) : Fin 4 → X := ![z 0, a 0, z 1, a 1]

def boxSliceEquiv (X : Type*) : ((Fin 2 → X) × (Fin 2 → X)) ≃ (Fin 4 → X) where
  toFun p := boxSlice p.1 p.2
  invFun x := (![x 1, x 3], ![x 0, x 2])
  left_inv p := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl

theorem expect_boxSlice {X M : Type*} [Fintype X] [AddCommMonoid M] [Module ℚ≥0 M]
    (F : (Fin 4 → X) → M) :
    (𝔼 x, F x) = 𝔼 a : Fin 2 → X, 𝔼 z : Fin 2 → X, F (boxSlice a z) := by
  calc
    _ = 𝔼 p : (Fin 2 → X) × (Fin 2 → X), F (boxSlice p.1 p.2) :=
      (Fintype.expect_equiv (boxSliceEquiv X) _ F (fun _ => rfl)).symm
    _ = _ := by
      simpa using (Finset.expect_product' Finset.univ Finset.univ
        (fun a z => F (boxSlice a z)))

noncomputable def boxKernel {X : Type*} (K : X → X → ℂ) (x : Fin 4 → X) : ℂ :=
  K (x 0) (x 2) * star (K (x 1) (x 2)) * star (K (x 0) (x 3)) * K (x 1) (x 3)

noncomputable def boxAnchorFactor {X : Type*} (K : X → X → ℂ)
    (a z : Fin 2 → X) : ℂ :=
  star (K (a 0) (z 1)) * star (K (z 0) (a 1)) * K (a 0) (a 1)

theorem boxKernel_slice {X : Type*} (K : X → X → ℂ) (a z : Fin 2 → X) :
    boxKernel K (boxSlice a z) = K (z 0) (z 1) * boxAnchorFactor K a z := by
  simp [boxKernel, boxSlice, boxAnchorFactor, mul_assoc]

theorem boxKernel_mean {X : Type*} [Fintype X] (K : X → X → ℂ) :
    (𝔼 x : Fin 4 → X, boxKernel K x) = finiteBoxCorrelation K := by
  simp_rw [expect_fin_cons]
  unfold finiteBoxCorrelation
  apply Finset.expect_congr rfl
  intro x _
  apply Finset.expect_congr rfl
  intro a _
  apply Finset.expect_congr rfl
  intro y _
  apply Finset.expect_congr rfl
  intro b _
  change (𝔼 _ : Fin 0 → X, K x y * star (K a y) * star (K x b) * K a b) = _
  rw [Fintype.expect_const]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

def additiveBoxDifference {Z R : Type*} [AddGroup R] :
    (n : ℕ) → {X : Fin n → Type*} → ((∀ i, X i) → Z → R) →
      (∀ i, X i) → (∀ i, X i) → Z → R
  | 0, _, F, _, _, z => F (fun i => Fin.elim0 i) z
  | n+1, _, F, u, v, z => additiveBoxDifference n
      (fun x z => F (Fin.cons (u 0) x) z - F (Fin.cons (v 0) x) z)
      (Fin.tail u) (Fin.tail v) z

theorem additiveBoxDifference_sum {Z R J : Type*} [AddCommGroup R]
    (n : ℕ) {X : Fin n → Type*} (S : Finset J)
    (F : J → (∀ i, X i) → Z → R) (u v : ∀ i, X i) (z : Z) :
    additiveBoxDifference n (fun x z => ∑ j ∈ S, F j x z) u v z =
      ∑ j ∈ S, additiveBoxDifference n (F j) u v z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [additiveBoxDifference, ← Finset.sum_sub_distrib]
    exact ih (fun j x z => F j (Fin.cons (u 0) x) z - F j (Fin.cons (v 0) x) z)
      (Fin.tail u) (Fin.tail v)

theorem additiveBoxDifference_product {Z R : Type*} [CommRing R]
    (n : ℕ) {X : Fin n → Type*} (a : Z → R) (f : ∀ i, X i → R)
    (u v : ∀ i, X i) (z : Z) :
    additiveBoxDifference n (fun x z => a z * ∏ i, f i (x i)) u v z =
      a z * ∏ i, (f i (u i)-f i (v i)) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [additiveBoxDifference]
    have he : (fun x z =>
        a z * ∏ i, f i (Fin.cons (u 0) x i) - a z * ∏ i, f i (Fin.cons (v 0) x i)) =
        (fun (x : ∀ i : Fin n, X i.succ) z =>
          (a z*(f 0 (u 0)-f 0 (v 0))) * ∏ i, f i.succ (x i)) := by
      funext x z
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      ring
    rw [he, ih]
    simp only [Fin.prod_univ_succ, Fin.tail_def]
    ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_box_anchor_correlation {X : Type*} [Fintype X] [Nonempty X]
    (K : X → X → ℂ) :
    ∃ a : Fin 2 → X, (finiteBoxCorrelation K).re ≤
      ‖𝔼 z : Fin 2 → X, K (z 0) (z 1) * boxAnchorFactor K a z‖ := by
  have hmean : (finiteBoxCorrelation K).re =
      𝔼 a : Fin 2 → X, (𝔼 z : Fin 2 → X,
        K (z 0) (z 1) * boxAnchorFactor K a z).re := by
    rw [← boxKernel_mean, expect_boxSlice, expect_re]
    simp_rw [boxKernel_slice]
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean.le
  exact ⟨a, ha.trans (Complex.re_le_norm _)⟩

end Erdos3

end

section

namespace Erdos3

theorem additiveBoxDifference_hom {Z R S : Type*} [AddGroup R] [AddGroup S]
    (L : R →+ S) (n : ℕ) {X : Fin n → Type*}
    (F : (∀ i, X i) → Z → R) (u v : ∀ i, X i) (z : Z) :
    additiveBoxDifference n (fun x t => L (F x t)) u v z =
      L (additiveBoxDifference n F u v z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [additiveBoxDifference, ← map_sub]
    exact ih (fun x t => F (Fin.cons (u 0) x) t - F (Fin.cons (v 0) x) t)
      (Fin.tail u) (Fin.tail v)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProgressionCoordinateResampling
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G R : Type*} [DecidableEq R] {X : G → R → Type*}

def resampleGroupCoordinates (label : G → R) (c : ∀ g r, X g r)
    (t : ∀ g, X g (label g)) : ∀ g r, X g r :=
  fun g => Function.update (c g) (label g) (t g)

@[simp] theorem resampleGroupCoordinates_selected (label : G → R)
    (c : ∀ g r, X g r) (t : ∀ g, X g (label g)) (g : G) :
    resampleGroupCoordinates label c t g (label g) = t g := by
  simp only [resampleGroupCoordinates, Function.update_self]

def groupCoordinateResamplingEquiv (label : G → R) :
    ((∀ g r, X g r) × (∀ g, X g (label g))) ≃
      ((∀ g r, X g r) × (∀ g, X g (label g))) where
  toFun p := (resampleGroupCoordinates label p.1 p.2, fun g => p.1 g (label g))
  invFun p := (resampleGroupCoordinates label p.1 p.2, fun g => p.1 g (label g))
  left_inv p := by
    apply Prod.ext
    · funext g r
      by_cases hr : r = label g
      · subst r
        simp only [resampleGroupCoordinates, Function.update_self]
      · simp only [resampleGroupCoordinates, Function.update_of_ne hr]
    · funext g
      exact resampleGroupCoordinates_selected label p.1 p.2 g
  right_inv p := by
    apply Prod.ext
    · funext g r
      by_cases hr : r = label g
      · subst r
        simp only [resampleGroupCoordinates, Function.update_self]
      · simp only [resampleGroupCoordinates, Function.update_of_ne hr]
    · funext g
      exact resampleGroupCoordinates_selected label p.1 p.2 g

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PaddedBooleanFeatures
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def booleanFeature {α R : Type*} [DecidableEq α] [Zero R] [One R]
    (a : Option α) (t : Finset α) : R :=
  match a with
  | none => 1
  | some i => if i ∈ t then 1 else 0

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.OperatorCoordinateBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem clm_norm_le_card_mul_of_basis {I E : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (A : (I → ℝ) →L[ℝ] E)
    {M : ℝ} (hM : 0 ≤ M) (hA : ∀ i, ‖A (Pi.single i 1)‖ ≤ M) :
    ‖A‖ ≤ Fintype.card I * M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hsum : A x = ∑ i, (x i) • A (Pi.single i 1) := by
    calc
      A x = A (∑ i, Pi.single i (x i)) :=
        congrArg A (LinearMap.sum_single_apply (fun _ : I => ℝ) x).symm
      _ = ∑ i, A (Pi.single i (x i)) := map_sum A _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        have hs : Pi.single i (x i) = (x i) • (Pi.single i (1 : ℝ) : I → ℝ) := by
          rw [← Pi.single_smul]
          simp
        rw [hs, map_smul]
  rw [hsum]
  calc
    _ ≤ ∑ i, ‖(x i) • A (Pi.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : I, ‖x‖ * M := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (norm_le_pi_norm x i) (hA i) (norm_nonneg _) (norm_nonneg x)
    _ = _ := by simp [mul_comm, mul_left_comm, mul_assoc]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialAnalyticDerivative
namespace OAI

section

namespace Erdos3

open scoped ContDiff

theorem mvPolynomial_contDiff_eval {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) : ContDiff ℝ ∞ (fun a : ι → ℝ => MvPolynomial.eval a p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simpa only [MvPolynomial.eval_C] using (contDiff_const (c := r))
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp =>
    have h := hp.mul (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).contDiff
    simp only [ContinuousLinearMap.proj_apply] at h
    simp only [map_mul, MvPolynomial.eval_X]
    exact h

theorem mvPolynomial_hasDerivAt_update {ι : Type*} [DecidableEq ι]
    (p : MvPolynomial ι ℝ) (j : ι) (a : ι → ℝ) :
    HasDerivAt (fun t => MvPolynomial.eval (Function.update a j t) p)
      (MvPolynomial.eval a (MvPolynomial.pderiv j p)) (a j) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    simpa only [MvPolynomial.eval_C, MvPolynomial.pderiv_C, map_zero] using hasDerivAt_const (a j) r
  | add p q hp hq =>
    have h := HasDerivAt.add hp hq
    simp only [map_add]
    exact h
  | mul_X p i hp =>
    by_cases hi : i = j
    · subst i
      have h := hp.mul (hasDerivAt_id (a j))
      simp only [id_eq, Function.update_eq_self, mul_one] at h
      simp only [map_mul, MvPolynomial.eval_X, Function.update_self, MvPolynomial.pderiv_mul,
        MvPolynomial.pderiv_X_self, map_add, mul_one]
      exact h
    · have h := hp.mul (hasDerivAt_const (a j) (a i))
      simp only [Function.update_eq_self, mul_zero, add_zero] at h
      simp only [map_mul, MvPolynomial.eval_X, Function.update_of_ne hi, MvPolynomial.pderiv_mul,
        MvPolynomial.pderiv_X_of_ne hi, mul_zero,
        add_zero]
      exact h

theorem mvPolynomial_fderiv_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial ι ℝ) (a : ι → ℝ) (j : ι) :
    fderiv ℝ (fun x : ι → ℝ => MvPolynomial.eval x p) a (Pi.single j 1) =
      MvPolynomial.eval a (MvPolynomial.pderiv j p) := by
  have hupdate : HasDerivAt (fun t => Function.update a j t) (Pi.single j 1) (a j) := by
    apply hasDerivAt_pi.mpr
    intro i
    by_cases hi : i = j
    · subst i
      simp only [Function.update_self, Pi.single_eq_same]
      exact hasDerivAt_id (a j)
    · simpa [Function.update_of_ne hi, Pi.single_eq_of_ne hi] using hasDerivAt_const (a j) (a i)
  have hp := (mvPolynomial_contDiff_eval p).differentiable (by norm_num)
  have hf : HasFDerivAt (fun x : ι → ℝ => MvPolynomial.eval x p)
      (fderiv ℝ (fun x : ι → ℝ => MvPolynomial.eval x p) a) (Function.update a j (a j)) := by
    rw [Function.update_eq_self]
    exact (hp a).hasFDerivAt
  have h := hf.comp_hasDerivAt (a j) hupdate
  simp only [Function.comp_def] at h
  exact h.unique (mvPolynomial_hasDerivAt_update p j a)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDeterminantDerivativeBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

abbrev BlockParameter (B F α : Type*) := B × F × Option α

noncomputable def booleanAffinePolynomial {B F α : Type*} [Fintype α] [DecidableEq α]
    (b : B) (v : F) (t : Finset α) : MvPolynomial (BlockParameter B F α) ℝ :=
  ∑ r : Option α, MvPolynomial.C (booleanFeature r t : ℝ) * MvPolynomial.X (b, v, r)

def blockSpecialization {B F α : Type*} [DecidableEq α]
    (label : B → F → Option α) (z : BlockParameter B F α) : ℝ :=
  if z.2.2 = label z.1 z.2.1 then 1 else 0

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem mvPolynomial_prod_eval_abs_le {I K : Type*} (s : Finset K)
    (p : K → MvPolynomial I ℝ) (a : I → ℝ) {L : ℝ}
    (hp : ∀ k ∈ s, |MvPolynomial.eval a (p k)| ≤ L) :
    |MvPolynomial.eval a (∏ k ∈ s, p k)| ≤ L ^ s.card := by
  rw [map_prod, Finset.abs_prod]
  calc
    _ ≤ ∏ _k ∈ s, L := Finset.prod_le_prod (fun _ _ => abs_nonneg _) hp
    _ = _ := by simp

theorem mvPolynomial_prod_pderiv_eval_abs_le_of_bound {I K : Type*} (s : Finset K)
    (p : K → MvPolynomial I ℝ) (j : I) (a : I → ℝ) {L D : ℝ}
    (hL : 1 ≤ L) (hD : 0 ≤ D)
    (hp : ∀ k ∈ s, |MvPolynomial.eval a (p k)| ≤ L)
    (hd : ∀ k ∈ s, |MvPolynomial.eval a (MvPolynomial.pderiv j (p k))| ≤ D) :
    |MvPolynomial.eval a (MvPolynomial.pderiv j (∏ k ∈ s, p k))| ≤
      s.card * D * L ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hL0 : 0 ≤ L := zero_le_one.trans hL
    have hps : ∀ k ∈ s, |MvPolynomial.eval a (p k)| ≤ L :=
      fun k hk => hp k (Finset.mem_insert_of_mem hk)
    have hds : ∀ k ∈ s, |MvPolynomial.eval a (MvPolynomial.pderiv j (p k))| ≤ D :=
      fun k hk => hd k (Finset.mem_insert_of_mem hk)
    have hprod := mvPolynomial_prod_eval_abs_le s p a hps
    have hder := ih hps hds
    rw [Finset.prod_insert hi, MvPolynomial.pderiv_mul, map_add, map_mul, map_mul]
    calc
      _ ≤ |MvPolynomial.eval a (MvPolynomial.pderiv j (p i))| *
          |MvPolynomial.eval a (∏ k ∈ s, p k)| +
          |MvPolynomial.eval a (p i)| * |MvPolynomial.eval a (MvPolynomial.pderiv j (∏ k ∈ s, p k))| :=
        (abs_add_le _ _).trans_eq (by simp only [abs_mul])
      _ ≤ D * L ^ s.card + L * (s.card * D * L ^ s.card) :=
        add_le_add (mul_le_mul (hd i (Finset.mem_insert_self i s)) hprod (abs_nonneg _) hD)
          (mul_le_mul (hp i (Finset.mem_insert_self i s)) hder (abs_nonneg _) hL0)
      _ ≤ L * (D * L ^ s.card) + L * (s.card * D * L ^ s.card) := by
        apply add_le_add _ le_rfl
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hL (mul_nonneg hD (pow_nonneg hL0 _))
      _ = _ := by rw [Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one, pow_succ]; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem polynomial_det_pderiv_eval_abs_le {I O : Type*} [Fintype O] [DecidableEq O]
    (M : Matrix O O (MvPolynomial I ℝ)) (a : I → ℝ) (j : I) {L D : ℝ}
    (hL : 1 ≤ L) (hD : 0 ≤ D)
    (hM : ∀ row col, |MvPolynomial.eval a (M row col)| ≤ L)
    (hd : ∀ row col, |MvPolynomial.eval a (MvPolynomial.pderiv j (M row col))| ≤ D) :
    |MvPolynomial.eval a (MvPolynomial.pderiv j M.det)| ≤
      (Fintype.card O).factorial * (Fintype.card O * D * L ^ Fintype.card O) := by
  classical
  rw [Matrix.det_apply', map_sum, map_sum]
  calc
    _ ≤ ∑ σ : Equiv.Perm O, |MvPolynomial.eval a (MvPolynomial.pderiv j
        (((Equiv.Perm.sign σ : ℤ) : MvPolynomial I ℝ) * ∏ i, M (σ i) i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm O, Fintype.card O * D * L ^ Fintype.card O := by
      apply Finset.sum_le_sum
      intro σ _
      have hsign : (((Equiv.Perm.sign σ : ℤ) : MvPolynomial I ℝ)) =
          MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : ℝ) := by simp
      rw [hsign, MvPolynomial.pderiv_C_mul, map_mul, MvPolynomial.eval_C, abs_mul,
        ← Int.cast_abs, Equiv.Perm.sign_abs, Int.cast_one, one_mul]
      simpa only [Finset.card_univ] using mvPolynomial_prod_pderiv_eval_abs_le_of_bound
        Finset.univ (fun i => M (σ i) i) j a hL hD
        (fun i _ => hM (σ i) i) (fun i _ => hd (σ i) i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]

theorem polynomial_det_eval_function {I O : Type*} [Fintype O] [DecidableEq O]
    (M : Matrix O O (MvPolynomial I ℝ)) :
    (fun a => (M.map (MvPolynomial.eval a)).det) = (fun a => MvPolynomial.eval a M.det) := by
  funext a
  have h := (MvPolynomial.eval a).map_det M
  simp only [RingHom.mapMatrix_apply] at h
  exact h.symm

theorem polynomial_det_fderiv_norm_le {I O : Type*}
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (M : Matrix O O (MvPolynomial I ℝ)) (a : I → ℝ) {L D : ℝ}
    (hL : 1 ≤ L) (hD : 0 ≤ D)
    (hM : ∀ row col, |MvPolynomial.eval a (M row col)| ≤ L)
    (hd : ∀ row col j, |MvPolynomial.eval a (MvPolynomial.pderiv j (M row col))| ≤ D) :
    ‖fderiv ℝ (fun x => (M.map (MvPolynomial.eval x)).det) a‖ ≤
      Fintype.card I * ((Fintype.card O).factorial *
        (Fintype.card O * D * L ^ Fintype.card O)) := by
  rw [polynomial_det_eval_function]
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  apply clm_norm_le_card_mul_of_basis _ (by positivity)
  intro j
  rw [mvPolynomial_fderiv_coordinate, Real.norm_eq_abs]
  exact polynomial_det_pderiv_eval_abs_le M a j hL hD hM (fun row col => hd row col j)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.BooleanProductSampler
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
  [DecidableEq B] [DecidableEq F] [DecidableEq α]

noncomputable def booleanBlockPolynomial (b : B) (t : Finset α) :
    MvPolynomial (BlockParameter B F α) ℝ :=
  ∏ v : F, booleanAffinePolynomial b v t

noncomputable def booleanSamplerPolynomial (c : B → ℝ) (s : Finset α) :
    MvPolynomial (BlockParameter B F α) ℝ :=
  booleanCoefficient (fun t => ∑ b : B, MvPolynomial.C (c b) * booleanBlockPolynomial b t) s

noncomputable def booleanSelectedColumn (c : B → ℝ) (b : B) (v : F) (r : Option α) (s : Finset α) :
    MvPolynomial (BlockParameter B F α) ℝ :=
  MvPolynomial.C (c b) * booleanCoefficient
    (fun t => MvPolynomial.C (booleanFeature r t : ℝ) *
      ∏ k ∈ Finset.univ.erase v, booleanAffinePolynomial b k t) s

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BooleanBlockCoefficientPhase
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def booleanBlockValue {G α : Type*} [Fintype G] [Fintype α] [DecidableEq α]
    (a : G → Option α → ℝ) (t : Finset α) : ℝ :=
  ∏ g, ∑ r, (booleanFeature r t : ℝ)*a g r

noncomputable def booleanBlockPhase {G α : Type*} [Fintype G] [Fintype α] [DecidableEq α]
    (ξ : Finset α → ℝ) (a : G → Option α → ℝ) : ℝ :=
  ∑ s, ξ s * booleanCoefficient (booleanBlockValue a) s

def frozenBooleanConstant {G α : Type*} [Fintype α] [DecidableEq α]
    (label : G → Option α) (c : G → Option α → ℝ) (t : Finset α) (g : G) : ℝ :=
  ∑ r ∈ Finset.univ.erase (label g), (booleanFeature r t : ℝ)*c g r

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def frozenBooleanFactor {G α : Type*} [Fintype α] [DecidableEq α]
    (label : G → Option α) (c : G → Option α → ℝ) (t : Finset α) (g : G) : MvPolynomial G ℝ :=
  MvPolynomial.C (booleanFeature (label g) t : ℝ)*MvPolynomial.X g +
    MvPolynomial.C (frozenBooleanConstant label c t g)

noncomputable def frozenBooleanPhasePolynomial {G α : Type*} [Fintype G]
    [Fintype α] [DecidableEq α]
    (label : G → Option α) (c : G → Option α → ℝ) (ξ : Finset α → ℝ) : MvPolynomial G ℝ :=
  ∑ s, MvPolynomial.C (ξ s) * booleanCoefficient (fun t => ∏ g, frozenBooleanFactor label c t g) s

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RectangularCellGeometry
namespace OAI

section

namespace Erdos3

theorem rectangularLatticeCell_disjoint {I : Type*}
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) :
    Pairwise (fun k l => Disjoint (rectangularLatticeCell a S k) (rectangularLatticeCell a S l)) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hkl (((rectangularLatticeCell_iff a S hS x k).mp hx).symm.trans
    ((rectangularLatticeCell_iff a S hS x l).mp hy))

theorem rectangularLatticeCell_point_distance {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (δ : ℝ) (hδ : 0 ≤ δ)
    (hmesh : ∀ i, 1 / S i ≤ δ) (k : I → ℤ) (x : I → ℝ)
    (hx : x ∈ rectangularLatticeCell a S k) :
    ‖x - rectangularLatticePoint a S k‖ ≤ δ := by
  have h := rectangularLatticeSample_error a S hS hδ hmesh x
  have hk := (rectangularLatticeCell_iff a S hS x k).mp hx
  rw [rectangularLatticeSample, hk, norm_sub_rev] at h
  exact h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SublevelThresholdBalance
namespace OAI

section

namespace Erdos3

theorem sublevel_threshold_balance (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    {u c : ℝ} (hu : 0 < u) (hc : 0 < c) :
    ∃ τ : ℝ, 0 < τ ∧
      (τ / c) ^ (((n * d : ℕ) : ℝ)⁻¹) =
        (u / c) ^ ((((n + 1) * d : ℕ) : ℝ)⁻¹) ∧
      (u / τ) ^ ((d : ℝ)⁻¹) =
        (u / c) ^ ((((n + 1) * d : ℕ) : ℝ)⁻¹) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  let x : ℝ := u / c
  let a : ℝ := (n : ℝ) / (n + 1)
  have hx : 0 < x := div_pos hu hc
  let τ : ℝ := c * x ^ a
  have hτ : 0 < τ := mul_pos hc (Real.rpow_pos_of_pos hx _)
  have hratio : τ / c = x ^ a := by dsimp [τ]; field_simp
  have hexp : a * (((n * d : ℕ) : ℝ)⁻¹) = ((((n + 1) * d : ℕ) : ℝ)⁻¹) := by
    dsimp [a]
    push_cast
    field_simp
  have hexp' : (1 - a) * (d : ℝ)⁻¹ = ((((n + 1) * d : ℕ) : ℝ)⁻¹) := by
    dsimp [a]
    push_cast
    field_simp
    ring
  have hquot : u / τ = x ^ (1 - a) := by
    rw [Real.rpow_sub hx, Real.rpow_one]
    dsimp [τ, x]
    field_simp
  refine ⟨τ, hτ, ?_, ?_⟩
  · rw [hratio, ← Real.rpow_mul hx.le, hexp]
  · rw [hquot, ← Real.rpow_mul hx.le, hexp']

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberVolumeBound
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem integral_indicator_fiber (ν : Measure B) (s : Set (A × B)) (hs : MeasurableSet s) (x : A) :
    (∫ y, s.indicator (fun _ => (1 : ℝ)) (x, y) ∂ν) = ν.real {y | (x, y) ∈ s} := by
  have ht : MeasurableSet {y | (x, y) ∈ s} := hs.preimage (measurable_const.prodMk measurable_id)
  have heq : (fun y => s.indicator (fun _ => (1 : ℝ)) (x, y)) =
      {y | (x, y) ∈ s}.indicator (fun _ => (1 : ℝ)) := by
    funext y
    rfl
  rw [heq]
  exact integral_indicator_one ht

theorem product_measureReal_eq_integral_fiber
    (μ : Measure A) (ν : Measure B) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (s : Set (A × B)) (hs : MeasurableSet s) :
    (μ.prod ν).real s = ∫ x, ν.real {y | (x, y) ∈ s} ∂μ := by
  rw [← integral_indicator_one hs]
  change (∫ z, s.indicator (fun _ => (1 : ℝ)) z ∂μ.prod ν) = _
  rw [integral_prod _ ((integrable_const (1 : ℝ)).indicator hs)]
  apply integral_congr_ae
  filter_upwards [] with x
  exact integral_indicator_fiber ν s hs x

theorem product_probability_le_bad_set_add
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : Set (A × B)) (hs : MeasurableSet s) (bad : Set A) (hbad : MeasurableSet bad)
    {b : ℝ} (hb : 0 ≤ b) (hgood : ∀ x, x ∉ bad → ν.real {y | (x, y) ∈ s} ≤ b) :
    (μ.prod ν).real s ≤ μ.real bad + b := by
  have hi : Integrable (s.indicator (fun _ => (1 : ℝ))) (μ.prod ν) :=
    (integrable_const (1 : ℝ)).indicator hs
  rw [← integral_indicator_one hs]
  change (∫ z, s.indicator (fun _ => (1 : ℝ)) z ∂μ.prod ν) ≤ _
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ x, bad.indicator (fun _ => (1 : ℝ)) x + b ∂μ := by
      apply integral_mono hi.integral_prod_left
        (((integrable_const (1 : ℝ)).indicator hbad).add (integrable_const b))
      intro x
      change (∫ y, s.indicator (fun _ => (1 : ℝ)) (x, y) ∂ν) ≤
        bad.indicator (fun _ => (1 : ℝ)) x + b
      rw [integral_indicator_fiber ν s hs x]
      by_cases hx : x ∈ bad
      · rw [Set.indicator_of_mem hx]
        have hle : ν.real {y | (x, y) ∈ s} ≤ 1 := by
          have h := measureReal_mono (μ := ν) (Set.subset_univ {y | (x, y) ∈ s})
          simp only [probReal_univ] at h
          exact h
        linarith
      · rw [Set.indicator_of_notMem hx, zero_add]
        exact hgood x hx
    _ = _ := by
      rw [integral_add ((integrable_const (1 : ℝ)).indicator hbad) (integrable_const b),
        integral_indicator_const (1 : ℝ) hbad, integral_const]
      simp

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem product_measureReal_le_of_fiber_bound {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (s : Set (A × B)) (hs : MeasurableSet s) (hsfin : (μ.prod ν) s ≠ ⊤)
    (T : Set A) (hT : MeasurableSet T) (hTfin : μ T ≠ ⊤)
    (hbase : ∀ z ∈ s, z.1 ∈ T) {b : ℝ}
    (hbound : ∀ x, ν.real {y | (x, y) ∈ s} ≤ b) :
    (μ.prod ν).real s ≤ μ.real T * b := by
  have hi : Integrable (s.indicator (fun _ => (1 : ℝ))) (μ.prod ν) :=
    (integrableOn_const hsfin).integrable_indicator hs
  have hmajor : Integrable (T.indicator (fun _ => b)) μ :=
    (integrableOn_const hTfin).integrable_indicator hT
  rw [← integral_indicator_one hs]
  change (∫ z, s.indicator (fun _ => (1 : ℝ)) z ∂μ.prod ν) ≤ _
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ x, T.indicator (fun _ => b) x ∂μ := by
      apply integral_mono hi.integral_prod_left hmajor
      intro x
      change (∫ y, s.indicator (fun _ => (1 : ℝ)) (x, y) ∂ν) ≤ T.indicator (fun _ => b) x
      rw [integral_indicator_fiber ν s hs]
      by_cases hx : x ∈ T
      · rw [Set.indicator_of_mem hx]
        exact hbound x
      · have hempty : {y | (x, y) ∈ s} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro y hy
          exact hx (hbase (x, y) hy)
        rw [hempty, measureReal_empty, Set.indicator_of_notMem hx]
    _ = _ := by rw [integral_indicator_const _ hT, smul_eq_mul]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SeparatedInterpolationBound
namespace OAI

section

namespace Erdos3

open Polynomial
open scoped BigOperators

theorem coeff_X_sub_C_mul_abs_le (p : ℝ[X]) {M y : ℝ} (hM : 0 ≤ M)
    (hp : ∀ n, |p.coeff n| ≤ M) (hy : |y| ≤ 1) (n : ℕ) :
    |((X - C y) * p).coeff n| ≤ 2 * M := by
  cases n with
  | zero =>
    simp only [mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, neg_mul, abs_neg,
      abs_mul]
    calc
      |y| * |p.coeff 0| ≤ 1 * M := mul_le_mul hy (hp 0) (abs_nonneg _) zero_le_one
      _ ≤ 2 * M := by linarith
  | succ n =>
    rw [coeff_X_sub_C_mul]
    calc
      |p.coeff n - y * p.coeff (n + 1)| ≤ |p.coeff n| + |y * p.coeff (n + 1)| := abs_sub _ _
      _ = |p.coeff n| + |y| * |p.coeff (n + 1)| := by rw [abs_mul]
      _ ≤ M + 1 * M := add_le_add (hp n) (mul_le_mul hy (hp (n + 1)) (abs_nonneg _) zero_le_one)
      _ = 2 * M := by ring

theorem coeff_prod_X_sub_C_abs_le {ι : Type*} (s : Finset ι) (v : ι → ℝ)
    (hv : ∀ i ∈ s, |v i| ≤ 1) (n : ℕ) :
    |(∏ i ∈ s, (X - C (v i))).coeff n| ≤ (2 : ℝ) ^ s.card := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty =>
    simp only [Finset.prod_empty, Finset.card_empty, pow_zero, coeff_one]
    split_ifs <;> norm_num
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, pow_succ]
    have hp (k : ℕ) : |(∏ j ∈ s, (X - C (v j))).coeff k| ≤ (2 : ℝ) ^ s.card := by
      exact ih (fun j hj => hv j (Finset.mem_insert_of_mem hj)) k
    simpa only [mul_comm] using coeff_X_sub_C_mul_abs_le (∏ j ∈ s, (X - C (v j)))
      (by positivity : 0 ≤ (2 : ℝ) ^ s.card) hp (hv i (Finset.mem_insert_self i s)) n

theorem lagrange_basis_coeff_abs_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℝ) (i : ι) {r : ℝ} (hr : 0 < r)
    (hv : ∀ j ∈ s, |v j| ≤ 1)
    (hsep : ∀ j ∈ s.erase i, r ≤ |v i - v j|) (n : ℕ) :
    |(Lagrange.basis s v i).coeff n| ≤ (2 / r) ^ (s.erase i).card := by
  have heq : Lagrange.basis s v i =
      C (∏ j ∈ s.erase i, (v i - v j)⁻¹) * ∏ j ∈ s.erase i, (X - C (v j)) := by
    simp only [Lagrange.basis, Lagrange.basisDivisor, Finset.prod_mul_distrib, map_prod]
  have hprod : (∏ j ∈ s.erase i, |(v i - v j)⁻¹|) ≤ (r⁻¹) ^ (s.erase i).card := by
    apply (Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j hj => ?_)).trans_eq
      (Finset.prod_const _)
    rw [abs_inv]
    simpa only [one_div] using one_div_le_one_div_of_le hr (hsep j hj)
  rw [heq, coeff_C_mul, abs_mul, Finset.abs_prod]
  calc
    _ ≤ (r⁻¹) ^ (s.erase i).card * (2 : ℝ) ^ (s.erase i).card :=
      mul_le_mul hprod (coeff_prod_X_sub_C_abs_le (s.erase i) v
        (fun j hj => hv j (Finset.mem_of_mem_erase hj)) n) (abs_nonneg _) (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open Polynomial
open scoped BigOperators

theorem polynomial_coeff_le_of_separated_samples (p : ℝ[X]) (t : Finset ℝ)
    {r u : ℝ} (hr : 0 < r) (hu : 0 ≤ u) (hdeg : p.degree < t.card)
    (ht : ∀ x ∈ t, |x| ≤ 1) (hval : ∀ x ∈ t, |p.eval x| ≤ u)
    (hsep : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → r ≤ |x - y|) (n : ℕ) :
    |p.coeff n| ≤ (t.card : ℝ) * u * (2 / r) ^ (t.card - 1) := by
  classical
  have heq : p = Lagrange.interpolate t id (fun x => p.eval x) :=
    Lagrange.eq_interpolate (fun _ _ _ _ h => h) hdeg
  have hterm (x : ℝ) (hx : x ∈ t) :
      |(C (p.eval x) * Lagrange.basis t id x).coeff n| ≤ u * (2 / r) ^ (t.card - 1) := by
    rw [coeff_C_mul, abs_mul]
    apply mul_le_mul (hval x hx) _ (abs_nonneg _) hu
    have h := lagrange_basis_coeff_abs_le t id x hr ht
      (fun y hy => hsep x hx y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy).symm) n
    simpa only [Finset.card_erase_of_mem hx] using h
  calc
    |p.coeff n| = |(∑ x ∈ t, C (p.eval x) * Lagrange.basis t id x).coeff n| :=
      congrArg (fun q : ℝ[X] => |q.coeff n|) heq
    _ = |∑ x ∈ t, (C (p.eval x) * Lagrange.basis t id x).coeff n| := by rw [finsetSum_coeff]
    _ ≤ ∑ x ∈ t, |(C (p.eval x) * Lagrange.basis t id x).coeff n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ t, u * (2 / r) ^ (t.card - 1) := Finset.sum_le_sum hterm
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SeparatedRealSamples
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem real_interval_cover_measure_le (t : Finset ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (⋃ y ∈ t, Set.Ioo (y - r) (y + r)) ≤ 2 * (t.card : ℝ) * r := by
  apply (measureReal_biUnion_finset_le t (fun y => Set.Ioo (y - r) (y + r))).trans
  have hlen (y : ℝ) : volume.real (Set.Ioo (y - r) (y + r)) = 2 * r := by
    rw [Real.volume_real_Ioo_of_le (by linarith)]
    ring
  simp only [hlen, Finset.sum_const, nsmul_eq_mul]
  ring_nf
  exact le_rfl

theorem exists_separated_real_samples (s : Set ℝ) {r : ℝ} (hr : 0 < r) (n : ℕ)
    (hlarge : 2 * (n : ℝ) * r < volume.real s) :
    ∃ t : Finset ℝ, t.card = n ∧ (↑t : Set ℝ) ⊆ s ∧
      ∀ x ∈ t, ∀ y ∈ t, x ≠ y → r ≤ |x - y| := by
  classical
  induction n with
  | zero => exact ⟨∅, rfl, by simp, by simp⟩
  | succ n ih =>
    have hsmall : 2 * (n : ℝ) * r < volume.real s := by
      push_cast at hlarge
      nlinarith
    obtain ⟨t, hcard, hts, hsep⟩ := ih hsmall
    let cover := ⋃ y ∈ t, Set.Ioo (y - r) (y + r)
    have hfinite : volume cover ≠ ⊤ := by
      apply measure_biUnion_ne_top t.finite_toSet
      intro y _
      simp only [Real.volume_Ioo, ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true]
    have hnot : ¬s ⊆ cover := by
      intro hsub
      have h := (measureReal_mono hsub hfinite).trans (real_interval_cover_measure_le t hr.le)
      rw [hcard] at h
      linarith
    obtain ⟨x, hxs, hxc⟩ := Set.not_subset.mp hnot
    have hfar (y : ℝ) (hy : y ∈ t) : r ≤ |x - y| := by
      by_contra! h
      have hxy := abs_lt.mp h
      apply hxc
      exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy, ⟨by linarith, by linarith⟩⟩⟩
    have hxt : x ∉ t := by
      intro hx
      have h := hfar x hx
      simp only [sub_self, abs_zero] at h
      linarith
    refine ⟨insert x t, by rw [Finset.card_insert_of_notMem hxt, hcard], ?_, ?_⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hxs
      · exact hts hy
    · intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with hax | hat
      · subst a
        rcases Finset.mem_insert.mp hb with rfl | hbt
        · exact False.elim (hab rfl)
        · exact hfar b hbt
      · rcases Finset.mem_insert.mp hb with hbx | hbt
        · subst b
          simpa only [abs_sub_comm] using hfar a hat
        · exact hsep a hat b hbt hab

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.UnivariatePolynomialSublevel
namespace OAI

section

namespace Erdos3

open MeasureTheory Polynomial
open scoped BigOperators

def unitPolynomialSublevel (p : ℝ[X]) (u : ℝ) : Set ℝ :=
  {x | |x| ≤ 1 ∧ |p.eval x| ≤ u}

theorem unitPolynomialSublevel_power_bound (p : ℝ[X]) {d : ℕ} (hd : 0 < d)
    (hdeg : p.natDegree ≤ d) {u : ℝ} (hu : 0 ≤ u) (k : ℕ) :
    |p.coeff k| * (volume.real (unitPolynomialSublevel p u)) ^ d ≤
      (d + 1 : ℝ) * (8 * (d + 1 : ℝ)) ^ d * u := by
  let mass := volume.real (unitPolynomialSublevel p u)
  change |p.coeff k| * mass ^ d ≤ _
  have hmass0 : 0 ≤ mass := measureReal_nonneg
  by_cases hz : mass = 0
  · rw [hz, zero_pow (Nat.ne_of_gt hd), mul_zero]
    positivity
  have hmass : 0 < mass := lt_of_le_of_ne hmass0 (Ne.symm hz)
  let r := mass / (4 * (d + 1 : ℝ))
  have hr : 0 < r := by dsimp [r]; positivity
  have hscale : 2 * (d + 1 : ℝ) * r = mass / 2 := by
    dsimp [r]
    field_simp
    ring
  have hlarge : 2 * ((d + 1 : ℕ) : ℝ) * r < volume.real (unitPolynomialSublevel p u) := by
    push_cast
    rw [hscale]
    change mass / 2 < mass
    linarith
  obtain ⟨t, htcard, hts, htsep⟩ := exists_separated_real_samples (unitPolynomialSublevel p u) hr (d + 1) hlarge
  have hdegree : p.degree < t.card := by
    rw [htcard]
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hdeg)
  have hcoeff := polynomial_coeff_le_of_separated_samples p t hr hu hdegree
    (fun x hx => (hts hx).1) (fun x hx => (hts hx).2) htsep k
  rw [htcard, Nat.add_sub_cancel] at hcoeff
  push_cast at hcoeff
  have hcancel : (2 / r) * mass = 8 * (d + 1 : ℝ) := by
    dsimp [r]
    field_simp
    ring
  calc
    |p.coeff k| * mass ^ d ≤ ((d + 1 : ℝ) * u * (2 / r) ^ d) * mass ^ d :=
      mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hmass0 d)
    _ = (d + 1 : ℝ) * u * ((2 / r) * mass) ^ d := by rw [mul_pow]; ring
    _ = _ := by rw [hcancel]; ring

noncomputable def univariateSublevelConstant (d : ℕ) : ℝ :=
  ((d + 1 : ℝ) * (8 * (d + 1 : ℝ)) ^ d) ^ ((d : ℝ)⁻¹)

theorem univariateSublevelConstant_pos (d : ℕ) : 0 < univariateSublevelConstant d := by
  unfold univariateSublevelConstant
  positivity

theorem unitPolynomialSublevel_rpow_bound (p : ℝ[X]) {d : ℕ} (hd : 0 < d)
    (hdeg : p.natDegree ≤ d) {u c : ℝ} (hu : 0 ≤ u) (hc : 0 < c)
    (k : ℕ) (hk : c ≤ |p.coeff k|) :
    volume.real (unitPolynomialSublevel p u) ≤
      univariateSublevelConstant d * (u / c) ^ ((d : ℝ)⁻¹) := by
  unfold univariateSublevelConstant
  rw [← Real.mul_rpow (by positivity : 0 ≤ (d + 1 : ℝ) * (8 * (d + 1 : ℝ)) ^ d)
    (div_nonneg hu hc.le)]
  apply (Real.le_rpow_inv_iff_of_pos measureReal_nonneg (by positivity)
    (by exact_mod_cast hd : (0 : ℝ) < d)).mpr
  rw [Real.rpow_natCast, ← mul_div_assoc]
  apply (le_div_iff₀ hc).mpr
  calc
    (volume.real (unitPolynomialSublevel p u)) ^ d * c ≤
        |p.coeff k| * (volume.real (unitPolynomialSublevel p u)) ^ d := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hk (pow_nonneg measureReal_nonneg d)
    _ ≤ _ := unitPolynomialSublevel_power_bound p hd hdeg hu k

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymmetricScalarSublevel
namespace OAI

section

namespace Erdos3

open MeasureTheory Polynomial
open scoped ENNReal

noncomputable def symmetricScalarMeasure : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • volume.restrict (Set.Icc (-1 : ℝ) 1)

instance symmetricScalarMeasure_probability : IsProbabilityMeasure symmetricScalarMeasure := by
  constructor
  norm_num [symmetricScalarMeasure, Measure.smul_apply, ENNReal.smul_def, Real.volume_Icc]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

theorem symmetricScalarMeasure_sublevel (p : ℝ[X]) (u : ℝ) :
    symmetricScalarMeasure.real {x | |p.eval x| ≤ u} =
      (1 / 2 : ℝ) * volume.real (unitPolynomialSublevel p u) := by
  have hs : MeasurableSet {x | |p.eval x| ≤ u} := (isClosed_le p.continuous.abs continuous_const).measurableSet
  have heq : {x | |p.eval x| ≤ u} ∩ Set.Icc (-1 : ℝ) 1 = unitPolynomialSublevel p u := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Icc, unitPolynomialSublevel, abs_le]
    tauto
  rw [symmetricScalarMeasure, measureReal_ennreal_smul_apply, measureReal_restrict_apply hs, heq]
  norm_num

theorem symmetricScalarMeasure_sublevel_bound (p : ℝ[X]) {d : ℕ} (hd : 0 < d)
    (hdeg : p.natDegree ≤ d) {u c : ℝ} (hu : 0 ≤ u) (hc : 0 < c)
    (k : ℕ) (hk : c ≤ |p.coeff k|) :
    symmetricScalarMeasure.real {x | |p.eval x| ≤ u} ≤
      univariateSublevelConstant d * (u / c) ^ ((d : ℝ)⁻¹) := by
  rw [symmetricScalarMeasure_sublevel]
  apply le_trans _ (unitPolynomialSublevel_rpow_bound p hd hdeg hu hc k hk)
  nlinarith [measureReal_nonneg (μ := volume) (s := unitPolynomialSublevel p u)]

theorem polynomial_family_sublevel_step {T : Type*} [MeasurableSpace T]
    (μ : Measure T) [IsProbabilityMeasure μ] (p : T → ℝ[X]) {d : ℕ} (hd : 0 < d)
    (hdeg : ∀ x, (p x).natDegree ≤ d)
    (hval : Measurable (fun z : T × ℝ => (p z.1).eval z.2))
    (k : ℕ) (hcoeff : Measurable (fun x => (p x).coeff k))
    {u τ : ℝ} (hu : 0 ≤ u) (hτ : 0 < τ) :
    (μ.prod symmetricScalarMeasure).real {z | |(p z.1).eval z.2| ≤ u} ≤
      μ.real {x | |(p x).coeff k| ≤ τ} +
        univariateSublevelConstant d * (u / τ) ^ ((d : ℝ)⁻¹) := by
  apply product_probability_le_bad_set_add μ symmetricScalarMeasure _
    (measurableSet_le (continuous_abs.measurable.comp hval) measurable_const) _
    (measurableSet_le (continuous_abs.measurable.comp hcoeff) measurable_const)
    (mul_nonneg (univariateSublevelConstant_pos d).le (Real.rpow_nonneg (div_nonneg hu hτ.le) _))
  intro x hx
  have hk : τ ≤ |(p x).coeff k| := (lt_of_not_ge hx).le
  exact symmetricScalarMeasure_sublevel_bound (p x) hd (hdeg x) hu hτ k hk

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoordinateSlice
namespace OAI

section

namespace Erdos3

noncomputable def polynomialCoordinateSlice {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (x : Fin n → ℝ) : Polynomial ℝ :=
  (MvPolynomial.finSuccEquiv ℝ n p).map (MvPolynomial.eval x)

theorem polynomialCoordinateSlice_eval {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (x : Fin n → ℝ) (y : ℝ) :
    (polynomialCoordinateSlice p x).eval y = MvPolynomial.eval (Fin.cons y x) p :=
  (MvPolynomial.eval_eq_eval_mv_eval' x y p).symm

theorem polynomialCoordinateSlice_coeff {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (x : Fin n → ℝ) (k : ℕ) :
    (polynomialCoordinateSlice p x).coeff k =
      MvPolynomial.eval x ((MvPolynomial.finSuccEquiv ℝ n p).coeff k) := by
  simp only [polynomialCoordinateSlice, Polynomial.coeff_map]

theorem polynomialCoordinateSlice_degree_le {n d : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (hp : p.degreeOf 0 ≤ d) (x : Fin n → ℝ) :
    (polynomialCoordinateSlice p x).natDegree ≤ d := by
  apply (Polynomial.natDegree_map_le).trans
  exact (MvPolynomial.natDegree_finSuccEquiv p).le.trans hp

theorem polynomialCoordinateSlice_coefficient_degrees {n d : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (hp : ∀ j, p.degreeOf j ≤ d) (k : ℕ) (j : Fin n) :
    ((MvPolynomial.finSuccEquiv ℝ n p).coeff k).degreeOf j ≤ d :=
  (MvPolynomial.degreeOf_coeff_finSuccEquiv p j k).trans (hp j.succ)

theorem polynomialCoordinateSlice_selected_coefficient {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (m : Fin (n + 1) →₀ ℕ) :
    ((MvPolynomial.finSuccEquiv ℝ n p).coeff (m 0)).coeff m.tail =
      p.coeff m := by
  rw [MvPolynomial.finSuccEquiv_coeff_coeff, Finsupp.cons_tail]

theorem polynomialCoordinateSlice_measurable_eval {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) :
    Measurable (fun z : (Fin n → ℝ) × ℝ => (polynomialCoordinateSlice p z.1).eval z.2) := by
  have hcons : Continuous (fun z : (Fin n → ℝ) × ℝ => (Fin.cons z.2 z.1 : Fin (n + 1) → ℝ)) := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_snd
    · exact (continuous_apply j).comp continuous_fst
  have h := (p.continuous_eval.comp hcons).measurable
  simp only [Function.comp_def] at h
  simpa only [polynomialCoordinateSlice_eval] using h

theorem polynomialCoordinateSlice_measurable_coeff {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (k : ℕ) :
    Measurable (fun x => (polynomialCoordinateSlice p x).coeff k) := by
  simpa only [polynomialCoordinateSlice_coeff] using
    ((MvPolynomial.finSuccEquiv ℝ n p).coeff k).continuous_eval.measurable

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SymmetricCubeMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def symmetricCubeMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => symmetricScalarMeasure)

instance symmetricCubeMeasure_probability (n : ℕ) : IsProbabilityMeasure (symmetricCubeMeasure n) := by
  unfold symmetricCubeMeasure
  infer_instance

theorem symmetricCubeMeasure_zero : symmetricCubeMeasure 0 = Measure.dirac 0 :=
  Measure.pi_of_empty _ _

theorem symmetricCubeMeasure_cons (n : ℕ) :
    MeasurePreserving (fun z : (Fin n → ℝ) × ℝ => (Fin.cons z.2 z.1 : Fin (n + 1) → ℝ))
      ((symmetricCubeMeasure n).prod symmetricScalarMeasure) (symmetricCubeMeasure (n + 1)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have he : MeasurePreserving e (symmetricCubeMeasure (n + 1))
      (symmetricScalarMeasure.prod (symmetricCubeMeasure n)) :=
    measurePreserving_piFinSuccAbove (fun _ => symmetricScalarMeasure) 0
  have h := (MeasurePreserving.symm e he).comp
    (Measure.measurePreserving_swap (μ := symmetricCubeMeasure n) (ν := symmetricScalarMeasure))
  convert h using 1
  funext z
  simp only [Function.comp_apply, e, MeasurableEquiv.piFinSuccAbove_symm_apply]
  change Fin.cons z.2 z.1 = @Fin.insertNth n (fun _ => ℝ) 0 z.2 z.1
  exact (Fin.insertNth_zero' _ _).symm

theorem symmetricCubeMeasure_sublevel_succ {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (u : ℝ) :
    (symmetricCubeMeasure (n + 1)).real {x | |MvPolynomial.eval x p| ≤ u} =
      ((symmetricCubeMeasure n).prod symmetricScalarMeasure).real
        {z | |(polynomialCoordinateSlice p z.1).eval z.2| ≤ u} := by
  have hs : MeasurableSet {x | |MvPolynomial.eval x p| ≤ u} :=
    (isClosed_le p.continuous_eval.abs continuous_const).measurableSet
  have h := (symmetricCubeMeasure_cons n).measureReal_preimage hs.nullMeasurableSet
  simpa only [Set.preimage_ofPred_eq, polynomialCoordinateSlice_eval] using h.symm

theorem symmetricCubeMeasure_sublevel_step {n d : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (hd : 0 < d) (hp : p.degreeOf 0 ≤ d)
    (k : ℕ) {u τ : ℝ} (hu : 0 ≤ u) (hτ : 0 < τ) :
    (symmetricCubeMeasure (n + 1)).real {x | |MvPolynomial.eval x p| ≤ u} ≤
      (symmetricCubeMeasure n).real
        {x | |MvPolynomial.eval x ((MvPolynomial.finSuccEquiv ℝ n p).coeff k)| ≤ τ} +
      univariateSublevelConstant d * (u / τ) ^ ((d : ℝ)⁻¹) := by
  rw [symmetricCubeMeasure_sublevel_succ]
  have h := polynomial_family_sublevel_step (symmetricCubeMeasure n) (polynomialCoordinateSlice p)
    hd (polynomialCoordinateSlice_degree_le p hp) (polynomialCoordinateSlice_measurable_eval p)
    k (polynomialCoordinateSlice_measurable_coeff p k) hu hτ
  simpa only [polynomialCoordinateSlice_coeff] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymmetricCubeSublevel
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem symmetricCubeMeasure_sublevel_one
    (p : MvPolynomial (Fin 1) ℝ) {d : ℕ} (hd : 0 < d) (hp : p.degreeOf 0 ≤ d)
    {u c : ℝ} (hu : 0 ≤ u) (hc : 0 < c) (m : Fin 1 →₀ ℕ)
    (hm : c ≤ |p.coeff m|) :
    (symmetricCubeMeasure 1).real {x | |MvPolynomial.eval x p| ≤ u} ≤
      univariateSublevelConstant d * (u / c) ^ ((d : ℝ)⁻¹) := by
  have htail : m.tail = 0 := Subsingleton.elim _ _
  have hcoeff : (polynomialCoordinateSlice p (0 : Fin 0 → ℝ)).coeff (m 0) =
      p.coeff m := by
    rw [polynomialCoordinateSlice_coeff, MvPolynomial.eval_zero]
    have h := polynomialCoordinateSlice_selected_coefficient p m
    rw [htail] at h
    exact h
  have hs : MeasurableSet {z : (Fin 0 → ℝ) × ℝ | |(polynomialCoordinateSlice p z.1).eval z.2| ≤ u} :=
    measurableSet_le (continuous_abs.measurable.comp (polynomialCoordinateSlice_measurable_eval p))
      measurable_const
  rw [symmetricCubeMeasure_sublevel_succ, product_measureReal_eq_integral_fiber _ _ _ hs,
    symmetricCubeMeasure_zero, integral_dirac]
  exact symmetricScalarMeasure_sublevel_bound _ hd (polynomialCoordinateSlice_degree_le p hp 0)
    hu hc (m 0) (by simpa only [hcoeff] using hm)

theorem symmetricCube_polynomial_sublevel_bound (d : ℕ) (hd : 0 < d) :
    ∀ (n : ℕ) (p : MvPolynomial (Fin (n + 1)) ℝ),
      (∀ j, p.degreeOf j ≤ d) → ∀ {u c : ℝ}, 0 < u → 0 < c →
      ∀ m : Fin (n + 1) →₀ ℕ, c ≤ |p.coeff m| →
      (symmetricCubeMeasure (n + 1)).real {x | |MvPolynomial.eval x p| ≤ u} ≤
        ((n + 1 : ℝ) * univariateSublevelConstant d) *
          (u / c) ^ ((((n + 1) * d : ℕ) : ℝ)⁻¹) := by
  intro n
  induction n with
  | zero =>
    intro p hp u c hu hc m hm
    simpa only [Nat.zero_add, Nat.one_mul, Nat.cast_zero, zero_add, one_mul] using
      symmetricCubeMeasure_sublevel_one p hd (hp 0) hu.le hc m hm
  | succ n ih =>
    intro p hp u c hu hc m hm
    obtain ⟨τ, hτ, hfirst, hsecond⟩ := sublevel_threshold_balance (n + 1) d (by omega) hd hu hc
    let q := (MvPolynomial.finSuccEquiv ℝ (n + 1) p).coeff (m 0)
    have hq : ∀ j, q.degreeOf j ≤ d := polynomialCoordinateSlice_coefficient_degrees p hp (m 0)
    have hqc : c ≤ |q.coeff m.tail| := by
      simpa only [q, polynomialCoordinateSlice_selected_coefficient] using hm
    have hbase := ih q hq hτ hc m.tail hqc
    have hstep := symmetricCubeMeasure_sublevel_step p hd (hp 0) (m 0) hu.le hτ
    apply hstep.trans
    calc
      _ ≤ ((n + 1 : ℝ) * univariateSublevelConstant d) *
          (τ / c) ^ ((((n + 1) * d : ℕ) : ℝ)⁻¹) +
          univariateSublevelConstant d * (u / τ) ^ ((d : ℝ)⁻¹) :=
        add_le_add hbase le_rfl
      _ = _ := by rw [hfirst, hsecond]; push_cast; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymmetricCubeVolume
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ENNReal BigOperators

def symmetricUnitBox (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc (-1 : ℝ) 1)

theorem symmetricUnitBox_mem (n : ℕ) (x : Fin n → ℝ) :
    x ∈ symmetricUnitBox n ↔ ∀ i, |x i| ≤ 1 := by
  simp only [symmetricUnitBox, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Icc, abs_le]

theorem symmetricCubeMeasure_eq_smul_restrict (n : ℕ) :
    symmetricCubeMeasure n = (1 / 2 : ℝ≥0∞) ^ n • volume.restrict (symmetricUnitBox n) := by
  unfold symmetricCubeMeasure
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hs)]
  change (1 / 2 : ℝ≥0∞) ^ n * volume ((Set.pi Set.univ s) ∩
    (Set.pi Set.univ fun _ : Fin n => Set.Icc (-1 : ℝ) 1)) = _
  rw [← Set.pi_inter_distrib, volume_pi_pi]
  simp only [symmetricScalarMeasure, Measure.smul_apply, Measure.restrict_apply (hs _),
    smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem symmetricUnitBox_volume_inter (n : ℕ) (s : Set (Fin n → ℝ)) (hs : MeasurableSet s) :
    volume.real (symmetricUnitBox n ∩ s) = (2 : ℝ) ^ n * (symmetricCubeMeasure n).real s := by
  rw [symmetricCubeMeasure_eq_smul_restrict, measureReal_ennreal_smul_apply,
    measureReal_restrict_apply hs, ENNReal.toReal_pow]
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  rw [← mul_assoc, ← mul_pow]
  norm_num only [div_self (by norm_num : (2 : ℝ) ≠ 0), one_pow, one_mul]
  rw [Set.inter_comm]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDeterminantDegree
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem polynomial_det_degreeOf_le {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial κ ℝ)) (j : κ) (e : ℕ)
    (hM : ∀ a b, (M a b).degreeOf j ≤ e) :
    M.det.degreeOf j ≤ Fintype.card ι * e := by
  classical
  rw [Matrix.det_apply']
  apply (MvPolynomial.degreeOf_sum_le j Finset.univ _).trans
  apply Finset.sup_le
  intro σ _
  have hsign : (((Equiv.Perm.sign σ : ℤ) : MvPolynomial κ ℝ)) =
      MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : ℝ) := by simp
  rw [hsign]
  apply (MvPolynomial.degreeOf_C_mul_le _ j _).trans
  apply (MvPolynomial.degreeOf_prod_le j Finset.univ _).trans
  calc
    _ ≤ ∑ _a : ι, e := Finset.sum_le_sum (fun a _ => hM (σ a) a)
    _ = _ := by simp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateDeterminant
namespace OAI

section

namespace Erdos3

noncomputable def coordinateMatrixPolynomial {I X : Type*} (index : I → I → X) :
    Matrix I I (MvPolynomial X ℝ) := fun i j => MvPolynomial.X (index i j)

theorem coordinateMatrixPolynomial_eval {I X : Type*} [Fintype I] [DecidableEq I]
    (index : I → I → X) (x : X → ℝ) :
    MvPolynomial.eval x (coordinateMatrixPolynomial index).det =
      Matrix.det (fun i j => x (index i j)) := by
  rw [(MvPolynomial.eval x).map_det]
  congr 1
  ext i j
  change MvPolynomial.eval x (MvPolynomial.X (index i j) : MvPolynomial X ℝ) = x (index i j)
  simp only [MvPolynomial.eval_X]

theorem coordinateMatrixPolynomial_degree {I X : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq X] (index : I → I → X) (j : X) :
    (coordinateMatrixPolynomial index).det.degreeOf j ≤ Fintype.card I := by
  apply (polynomial_det_degreeOf_le _ j 1 ?_).trans_eq (Nat.mul_one _)
  intro a b
  simp only [coordinateMatrixPolynomial, MvPolynomial.degreeOf_X]
  split_ifs <;> omega

noncomputable def coordinateDeterminantVariation (I X : Type*) [Fintype I] [Fintype X] : ℝ :=
  Fintype.card X * ((Fintype.card I).factorial * Fintype.card I)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDilation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def dilateMvPolynomial {ι : Type*} (R : ℝ) (p : MvPolynomial ι ℝ) : MvPolynomial ι ℝ :=
  ∑ m ∈ p.support, MvPolynomial.monomial m
    (p.coeff m * ∏ i ∈ m.support, R ^ m i)

theorem dilateMvPolynomial_coeff {ι : Type*} (R : ℝ) (p : MvPolynomial ι ℝ) (m : ι →₀ ℕ) :
    (dilateMvPolynomial R p).coeff m =
      p.coeff m * ∏ i ∈ m.support, R ^ m i := by
  classical
  rw [dilateMvPolynomial, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp only [MvPolynomial.notMem_support_iff.mp h, zero_mul]

theorem dilateMvPolynomial_support_subset {ι : Type*} (R : ℝ) (p : MvPolynomial ι ℝ) :
    (dilateMvPolynomial R p).support ⊆ p.support := by
  intro m hm
  rw [MvPolynomial.mem_support_iff, dilateMvPolynomial_coeff] at hm
  exact MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hm)

theorem dilateMvPolynomial_degree_le {ι : Type*} (R : ℝ) (p : MvPolynomial ι ℝ)
    (i : ι) {d : ℕ} (hp : p.degreeOf i ≤ d) : (dilateMvPolynomial R p).degreeOf i ≤ d := by
  rw [MvPolynomial.degreeOf_le_iff] at hp ⊢
  exact fun m hm => hp m (dilateMvPolynomial_support_subset R p hm)

theorem dilateMvPolynomial_eval {ι : Type*} (R : ℝ) (p : MvPolynomial ι ℝ) (x : ι → ℝ) :
    MvPolynomial.eval x (dilateMvPolynomial R p) = MvPolynomial.eval (R • x) p := by
  classical
  rw [dilateMvPolynomial, MvPolynomial.eval_sum, MvPolynomial.eval_eq]
  apply Finset.sum_congr rfl
  intro m _
  rw [MvPolynomial.eval_monomial]
  simp only [Finsupp.prod, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib]
  ring

theorem dilateMvPolynomial_coeff_abs_le {ι : Type*} {R : ℝ} (hR : 1 ≤ R)
    (p : MvPolynomial ι ℝ) (m : ι →₀ ℕ) :
    |p.coeff m| ≤ |(dilateMvPolynomial R p).coeff m| := by
  have hw : 1 ≤ ∏ i ∈ m.support, R ^ m i := by
    calc
      1 = ∏ _i ∈ m.support, (1 : ℝ) := by simp
      _ ≤ ∏ i ∈ m.support, R ^ m i := Finset.prod_le_prod (fun _ _ => zero_le_one)
        (fun index _ => one_le_pow₀ hR)
  rw [dilateMvPolynomial_coeff, abs_mul, abs_of_nonneg (zero_le_one.trans hw)]
  exact le_mul_of_one_le_right (abs_nonneg _) hw

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialValueCoefficient
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mvPolynomial_eval_abs_le_sum_coeff {ι : Type*}
    (p : MvPolynomial ι ℝ) (x : ι → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    |MvPolynomial.eval x p| ≤ ∑ m ∈ p.support, |p.coeff m| := by
  classical
  rw [MvPolynomial.eval_eq]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro m _
  rw [abs_mul, Finset.abs_prod]
  have hprod : (∏ i ∈ m.support, |x i ^ m i|) ≤ 1 := by
    apply Finset.prod_le_one
    · exact fun _ _ => abs_nonneg _
    · intro i _
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (hx i)
  exact mul_le_of_le_one_right (abs_nonneg _) hprod

theorem mvPolynomial_support_card_le {N d : ℕ}
    (p : MvPolynomial (Fin N) ℝ) (hp : ∀ i, p.degreeOf i ≤ d) :
    p.support.card ≤ (d + 1) ^ N := by
  classical
  let f : p.support → (Fin N → Fin (d + 1)) := fun m i =>
    ⟨m.val i, Nat.lt_succ_of_le ((MvPolynomial.degreeOf_le_iff.mp (hp i)) m.val m.property)⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    exact congrArg Fin.val (congrFun hab i)
  have h := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using h

theorem exists_coefficient_of_unit_box_value {N d : ℕ}
    (p : MvPolynomial (Fin N) ℝ) (hp : ∀ i, p.degreeOf i ≤ d)
    (x : Fin N → ℝ) (hx : ∀ i, |x i| ≤ 1) {v : ℝ} (hv : 0 < v)
    (hval : v ≤ |MvPolynomial.eval x p|) :
    ∃ m : Fin N →₀ ℕ, v / (d + 1 : ℝ) ^ N ≤ |p.coeff m| := by
  classical
  have hp0 : p ≠ 0 := by
    intro h
    simp only [h, map_zero, abs_zero] at hval
    linarith
  obtain ⟨m, _hm, hmax⟩ := p.support.exists_max_image
    (fun monomial => |p.coeff monomial|) (MvPolynomial.support_nonempty.mpr hp0)
  refine ⟨m, (div_le_iff₀ (by positivity : 0 < (d + 1 : ℝ) ^ N)).mpr ?_⟩
  have hcard : (p.support.card : ℝ) ≤ (d + 1 : ℝ) ^ N := by
    exact_mod_cast mvPolynomial_support_card_le p hp
  calc
    v ≤ |MvPolynomial.eval x p| := hval
    _ ≤ ∑ monomial ∈ p.support, |p.coeff monomial| := mvPolynomial_eval_abs_le_sum_coeff p x hx
    _ ≤ ∑ _monomial ∈ p.support, |p.coeff m| := Finset.sum_le_sum hmax
    _ = (p.support.card : ℝ) * |p.coeff m| := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (d + 1 : ℝ) ^ N * |p.coeff m| :=
      mul_le_mul_of_nonneg_right hcard (abs_nonneg _)
    _ = _ := mul_comm _ _

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.EmbeddedMatrixDeterminantPolynomial
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

def unitMvPolynomialSublevel {N : ℕ} (p : MvPolynomial (Fin N) ℝ) (u : ℝ) : Set (Fin N → ℝ) :=
  symmetricUnitBox N ∩ {x | |MvPolynomial.eval x p| ≤ u}

theorem unitMvPolynomialSublevel_volume_ne_top {N : ℕ} (p : MvPolynomial (Fin N) ℝ) (u : ℝ) :
    volume (unitMvPolynomialSublevel p u) ≠ ⊤ := by
  have hbox : volume (symmetricUnitBox N) ≠ ⊤ := by
    rw [symmetricUnitBox, volume_pi_pi]
    exact ENNReal.prod_ne_top (fun _ _ => by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  exact measure_ne_top_of_subset Set.inter_subset_left hbox

noncomputable def multivariateSublevelConstant (N d : ℕ) : ℝ :=
  (2 : ℝ) ^ N * N * univariateSublevelConstant d

theorem multivariateSublevelConstant_pos {N : ℕ} (hN : 0 < N) (d : ℕ) :
    0 < multivariateSublevelConstant N d := by
  unfold multivariateSublevelConstant
  exact mul_pos (mul_pos (by positivity) (by exact_mod_cast hN)) (univariateSublevelConstant_pos d)

theorem multivariate_polynomial_sublevel_bound {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (p : MvPolynomial (Fin N) ℝ) (hp : ∀ j, p.degreeOf j ≤ d)
    {u c : ℝ} (hu : 0 < u) (hc : 0 < c) (m : Fin N →₀ ℕ)
    (hm : c ≤ |p.coeff m|) :
    volume.real (unitMvPolynomialSublevel p u) ≤
      multivariateSublevelConstant N d * (u / c) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  have h := symmetricCube_polynomial_sublevel_bound d hd n p hp hu hc m hm
  rw [unitMvPolynomialSublevel, symmetricUnitBox_volume_inter _ _
    (isClosed_le p.continuous_eval.abs continuous_const).measurableSet]
  have hmul := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (2 : ℝ) ^ (n + 1))
  simpa only [multivariateSublevelConstant, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, mul_assoc] using hmul

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Pointwise

def boxMvPolynomialSublevel {N : ℕ} (p : MvPolynomial (Fin N) ℝ) (R u : ℝ) : Set (Fin N → ℝ) :=
  {x | (∀ i, |x i| ≤ R) ∧ |MvPolynomial.eval x p| ≤ u}

theorem boxMvPolynomialSublevel_eq_smul {N : ℕ} (p : MvPolynomial (Fin N) ℝ)
    {R : ℝ} (hR : 0 < R) (u : ℝ) :
    boxMvPolynomialSublevel p R u = R • unitMvPolynomialSublevel (dilateMvPolynomial R p) u := by
  ext x
  constructor
  · intro hx
    have hback : R • (R⁻¹ • x) = x := by rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
    refine Set.mem_smul_set.mpr ⟨R⁻¹ • x, ⟨?_, ?_⟩, hback⟩
    · apply (symmetricUnitBox_mem N _).mpr
      intro i
      change |R⁻¹ * x i| ≤ 1
      rw [abs_mul, abs_inv, abs_of_pos hR]
      calc
        R⁻¹ * |x i| ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left (hx.1 i) (inv_nonneg.mpr hR.le)
        _ = 1 := inv_mul_cancel₀ hR.ne'
    · change |MvPolynomial.eval (R⁻¹ • x) (dilateMvPolynomial R p)| ≤ u
      rw [dilateMvPolynomial_eval, hback]
      exact hx.2
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hx
    refine ⟨?_, ?_⟩
    · intro i
      change |R * y i| ≤ R
      rw [abs_mul, abs_of_pos hR]
      have hi := (symmetricUnitBox_mem N y).mp hy.1 i
      exact (mul_le_mul_of_nonneg_left hi hR.le).trans_eq (mul_one R)
    · rw [← dilateMvPolynomial_eval]
      exact hy.2

theorem boxMvPolynomialSublevel_volume {N : ℕ} (p : MvPolynomial (Fin N) ℝ)
    {R : ℝ} (hR : 0 < R) (u : ℝ) :
    volume.real (boxMvPolynomialSublevel p R u) =
      R ^ N * volume.real (unitMvPolynomialSublevel (dilateMvPolynomial R p) u) := by
  rw [boxMvPolynomialSublevel_eq_smul p hR, measureReal_def, Measure.addHaar_smul_of_nonneg volume hR.le,
    ENNReal.toReal_mul]
  simp [Module.finrank_fintype_fun_eq_card, measureReal_def, hR.le]

theorem boxMvPolynomialSublevel_volume_ne_top {N : ℕ} (p : MvPolynomial (Fin N) ℝ)
    {R : ℝ} (hR : 0 < R) (u : ℝ) : volume (boxMvPolynomialSublevel p R u) ≠ ⊤ := by
  rw [boxMvPolynomialSublevel_eq_smul p hR, Measure.addHaar_smul_of_nonneg volume hR.le]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (unitMvPolynomialSublevel_volume_ne_top _ _)

theorem polynomial_sublevel_box_bound {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (p : MvPolynomial (Fin N) ℝ) (hp : ∀ j, p.degreeOf j ≤ d)
    {R u c : ℝ} (hR : 1 ≤ R) (hu : 0 < u) (hc : 0 < c) (m : Fin N →₀ ℕ)
    (hm : c ≤ |p.coeff m|) :
    volume.real (boxMvPolynomialSublevel p R u) ≤
      R ^ N * multivariateSublevelConstant N d * (u / c) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
  rw [boxMvPolynomialSublevel_volume p (zero_lt_one.trans_le hR)]
  have h := multivariate_polynomial_sublevel_bound hN hd (dilateMvPolynomial R p)
    (fun j => dilateMvPolynomial_degree_le R p j (hp j)) hu hc m
    (hm.trans (dilateMvPolynomial_coeff_abs_le hR p m))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (pow_nonneg (zero_le_one.trans hR) N)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

noncomputable def reindexPolynomialMatrix {I J O : Type*} (e : I ≃ J)
    (M : Matrix O O (MvPolynomial I ℝ)) : Matrix O O (MvPolynomial J ℝ) :=
  M.map (MvPolynomial.rename e)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem shiftedPolynomial_grid_sublevel_transfer {Ω : Type*} [Fintype Ω] {N : ℕ}
    (p : FiniteProbabilityWeights Ω) (grid : Ω → Fin N → ℤ) (hinj : Function.Injective grid)
    (a S : Fin N → ℝ) (hS : ∀ i, 0 < S i)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hgrid : ∀ ω i, |rectangularLatticePoint a S (grid ω) i| ≤ 1)
    (P : MvPolynomial (Fin N) ℝ) (M K u : ℝ) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hw : ∀ ω, p.weight ω ≤ M * (∏ i, S i)⁻¹)
    (hLip : ∀ x y : Fin N → ℝ, (∀ i, |x i| ≤ 2) → (∀ i, |y i| ≤ 2) →
      |MvPolynomial.eval x P - MvPolynomial.eval y P| ≤ K * ‖x - y‖) :
    p.eventProbability (fun ω => |MvPolynomial.eval (rectangularLatticePoint a S (grid ω)) P| ≤ u) ≤
      M * volume.real (boxMvPolynomialSublevel P 2 (u + K * δ)) := by
  let cell := fun ω => rectangularLatticeCell a S (grid ω)
  apply finite_cell_event_probability_le p _ volume cell _ M ((∏ i, S i)⁻¹) hM
    (fun v w hvw => rectangularLatticeCell_disjoint a S hS (hinj.ne hvw))
    (fun ω => rectangularLatticeCell_measurable _ _ _)
    (fun ω => rectangularLatticeCell_volume_ne_top _ _ _)
    (fun ω => rectangularLatticeCell_volume a S hS (grid ω)) hw _
    (boxMvPolynomialSublevel_volume_ne_top P (by norm_num) _)
  intro ω hω x hx
  have hd := rectangularLatticeCell_point_distance a S hS δ hδ hmesh (grid ω) x hx
  have hxb (i : Fin N) : |x i| ≤ 2 := by
    have hi0 : |x i - rectangularLatticePoint a S (grid ω) i| ≤
        ‖x - rectangularLatticePoint a S (grid ω)‖ := by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using
        norm_le_pi_norm (x - rectangularLatticePoint a S (grid ω)) i
    have hi := hi0.trans hd
    have ht := abs_add_le (x i - rectangularLatticePoint a S (grid ω) i)
      (rectangularLatticePoint a S (grid ω) i)
    rw [sub_add_cancel] at ht
    exact ht.trans (by linarith [hgrid ω i])
  have hyb (i : Fin N) : |rectangularLatticePoint a S (grid ω) i| ≤ 2 :=
    (hgrid ω i).trans (by norm_num)
  have he := (hLip x _ hxb hyb).trans (mul_le_mul_of_nonneg_left hd hK)
  refine ⟨hxb, ?_⟩
  have ha := abs_sub_abs_le_abs_sub (MvPolynomial.eval x P)
    (MvPolynomial.eval (rectangularLatticePoint a S (grid ω)) P)
  linarith

theorem shiftedPolynomial_grid_sublevel_bound_of_value {Ω : Type*} [Fintype Ω] {N d : ℕ}
    (hN : 0 < N) (hd : 0 < d)
    (p : FiniteProbabilityWeights Ω) (grid : Ω → Fin N → ℤ) (hinj : Function.Injective grid)
    (a S : Fin N → ℝ) (hS : ∀ i, 0 < S i)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hgrid : ∀ ω i, |rectangularLatticePoint a S (grid ω) i| ≤ 1)
    (P : MvPolynomial (Fin N) ℝ) (hdeg : ∀ i, P.degreeOf i ≤ d)
    (M K u : ℝ) (hM : 0 ≤ M) (hK : 0 ≤ K) (hu : 0 < u)
    (hw : ∀ ω, p.weight ω ≤ M * (∏ i, S i)⁻¹)
    (hLip : ∀ x y : Fin N → ℝ, (∀ i, |x i| ≤ 2) → (∀ i, |y i| ≤ 2) →
      |MvPolynomial.eval x P - MvPolynomial.eval y P| ≤ K * ‖x - y‖)
    (x₀ : Fin N → ℝ) (hx₀ : ∀ i, |x₀ i| ≤ 1) (hval : 1 ≤ |MvPolynomial.eval x₀ P|) :
    p.eventProbability (fun ω => |MvPolynomial.eval (rectangularLatticePoint a S (grid ω)) P| ≤ u) ≤
      M * (2 ^ N * multivariateSublevelConstant N d *
        ((u + K * δ) * (d + 1 : ℝ) ^ N) ^ (((N * d : ℕ) : ℝ)⁻¹)) := by
  apply (shiftedPolynomial_grid_sublevel_transfer p grid hinj a S hS hδ hδ1 hmesh hgrid
    P M K u hM hK hw hLip).trans
  apply mul_le_mul_of_nonneg_left _ hM
  obtain ⟨t, ht⟩ := exists_coefficient_of_unit_box_value P hdeg x₀ hx₀ zero_lt_one hval
  have h := polynomial_sublevel_box_bound hN hd P hdeg (by norm_num : (1 : ℝ) ≤ 2)
    (add_pos_of_pos_of_nonneg hu (mul_nonneg hK hδ))
    (by positivity : (0 : ℝ) < 1 / (d + 1 : ℝ) ^ N) t ht
  simpa only [div_div_eq_mul_div, div_one] using h

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

variable {n N : ℕ}

noncomputable def embeddedMatrixDeterminantPolynomial
    (e : Fin n × Fin n ↪ Fin N) : MvPolynomial (Fin N) ℝ :=
  (coordinateMatrixPolynomial (fun i j => e (i,j))).det

noncomputable def embeddedMatrixIdentityPoint
    (e : Fin n × Fin n ↪ Fin N) (k : Fin N) : ℝ :=
  if ∃ i : Fin n, e (i,i) = k then 1 else 0

theorem embeddedMatrixIdentityPoint_entry (e : Fin n × Fin n ↪ Fin N) (a b : Fin n) :
    embeddedMatrixIdentityPoint e (e (a,b)) = if a = b then 1 else 0 := by
  have hdiag : (∃ i : Fin n, e (i,i) = e (a,b)) ↔ a = b := by
    constructor
    · rintro ⟨i,hi⟩
      have hh := e.injective hi
      exact (congrArg Prod.fst hh).symm.trans (congrArg Prod.snd hh)
    · intro hab
      subst b
      exact ⟨a,rfl⟩
  simp only [embeddedMatrixIdentityPoint, hdiag]

theorem embeddedMatrixIdentityPoint_bound (e : Fin n × Fin n ↪ Fin N) (k : Fin N) :
    |embeddedMatrixIdentityPoint e k| ≤ 1 := by
  unfold embeddedMatrixIdentityPoint
  split_ifs <;> norm_num

theorem embeddedMatrixDeterminantPolynomial_eval
    (e : Fin n × Fin n ↪ Fin N) (x : Fin N → ℝ) :
    MvPolynomial.eval x (embeddedMatrixDeterminantPolynomial e) =
      Matrix.det (fun i j : Fin n => x (e (i,j))) :=
  coordinateMatrixPolynomial_eval _ _

theorem embeddedMatrixDeterminantPolynomial_degree
    (e : Fin n × Fin n ↪ Fin N) (k : Fin N) :
    (embeddedMatrixDeterminantPolynomial e).degreeOf k ≤ n := by
  simpa only [Fintype.card_fin, embeddedMatrixDeterminantPolynomial] using
    coordinateMatrixPolynomial_degree (fun i j => e (i,j)) k

theorem embeddedMatrixDeterminantPolynomial_identity
    (e : Fin n × Fin n ↪ Fin N) :
    MvPolynomial.eval (embeddedMatrixIdentityPoint e) (embeddedMatrixDeterminantPolynomial e) = 1 := by
  rw [embeddedMatrixDeterminantPolynomial_eval]
  have he : (fun i j : Fin n => embeddedMatrixIdentityPoint e (e (i,j))) =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simpa only [Matrix.one_apply] using embeddedMatrixIdentityPoint_entry e i j
  rw [he, Matrix.det_one]

noncomputable def embeddedMatrixDeterminantLip (n N : ℕ) : ℝ :=
  (N : ℝ) * ((n.factorial : ℝ) * ((n : ℝ) * 2 ^ n))

theorem embeddedMatrixDeterminantLip_nonneg (n N : ℕ) :
    0 ≤ embeddedMatrixDeterminantLip n N := by
  unfold embeddedMatrixDeterminantLip
  positivity

theorem embeddedMatrixDeterminantPolynomial_derivative
    (e : Fin n × Fin n ↪ Fin N) (x : Fin N → ℝ) (hx : ∀ j, |x j| ≤ 2) :
    ‖fderiv ℝ (fun x => MvPolynomial.eval x (embeddedMatrixDeterminantPolynomial e)) x‖ ≤
      embeddedMatrixDeterminantLip n N := by
  have h := polynomial_det_fderiv_norm_le
    (coordinateMatrixPolynomial (fun i j => e (i,j))) x
    (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 1)
    (fun a b => by
      simpa only [coordinateMatrixPolynomial, MvPolynomial.eval_X] using hx (e (a,b)))
    (fun a b j => by
      simp only [coordinateMatrixPolynomial, MvPolynomial.pderiv_X, Pi.single_apply]
      split_ifs <;> norm_num)
  rw [polynomial_det_eval_function] at h
  simpa only [Fintype.card_fin, mul_one, embeddedMatrixDeterminantLip,
    embeddedMatrixDeterminantPolynomial] using h

theorem embeddedMatrixDeterminantPolynomial_lipschitz
    (e : Fin n × Fin n ↪ Fin N) (x y : Fin N → ℝ)
    (hx : ∀ j, |x j| ≤ 2) (hy : ∀ j, |y j| ≤ 2) :
    |MvPolynomial.eval x (embeddedMatrixDeterminantPolynomial e) -
      MvPolynomial.eval y (embeddedMatrixDeterminantPolynomial e)| ≤
      embeddedMatrixDeterminantLip n N * ‖x - y‖ := by
  let S : Set (Fin N → ℝ) := Set.Icc (fun _ => -2) (fun _ => 2)
  have hmem (z : Fin N → ℝ) : z ∈ S ↔ ∀ j, |z j| ≤ 2 := by
    simp only [S, Set.mem_Icc, Pi.le_def, abs_le, forall_and]
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ S) => (mvPolynomial_contDiff_eval (embeddedMatrixDeterminantPolynomial e)).differentiable
      (by norm_num) z)
    (fun z hz => embeddedMatrixDeterminantPolynomial_derivative e z ((hmem z).mp hz))
    (convex_Icc _ _) ((hmem y).mpr hy) ((hmem x).mpr hx)
  simpa only [Real.norm_eq_abs] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanMinorDimension
namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff

variable {B F α O : Type*} [Fintype B] [Fintype F] [Fintype α]
  [DecidableEq B] [DecidableEq F] [DecidableEq α]

noncomputable def booleanSamplerMap (c : B → ℝ) (sets : O → Finset α)
    (a : BlockParameter B F α → ℝ) (o : O) : ℝ :=
  MvPolynomial.eval a (booleanSamplerPolynomial c (sets o))

noncomputable def booleanSelectedMinor (c : B → ℝ) (sets : O → Finset α)
    (block : O → B) (v : F) (r : O → Option α) : Matrix O O (MvPolynomial (BlockParameter B F α) ℝ) :=
  fun row col => MvPolynomial.pderiv (block col, v, r col) (booleanSamplerPolynomial c (sets row))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def productMinorEntryBound (q h : ℕ) (C R : ℝ) : ℝ :=
  C * ((2 : ℝ) ^ h * (((q : ℝ) + 1) * R) ^ (h - 1))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def restrictBlockParameters {B O F α : Type*} (block : O → B)
    (a : BlockParameter B F α → ℝ) (j : BlockParameter O F α) : ℝ :=
  a (block j.1, j.2.1, j.2.2)

end Erdos3

end

section

namespace Erdos3

theorem blockParameter_card {B α : Type*} [Fintype B] [Fintype α] (h : ℕ) :
    Fintype.card (BlockParameter B (Fin h) α) = Fintype.card B * (h * (Fintype.card α + 1)) := by
  simp only [BlockParameter, Fintype.card_prod, Fintype.card_fin, Fintype.card_option]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def productMinorPartialBound (q h : ℕ) (C R : ℝ) : ℝ :=
  C * ((2 : ℝ) ^ h * (h * (((q : ℝ) + 1) * R) ^ h))

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

noncomputable def booleanMinorDeterminant {B O F α : Type*}
    [Fintype B] [Fintype O] [Fintype F] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) (v : F) (r : O → Option α)
    (a : BlockParameter B F α → ℝ) : ℝ :=
  ((booleanSelectedMinor c sets block v r).map (MvPolynomial.eval a)).det

def productMinorDeterminantDerivativeBound (n j q h : ℕ) (C R : ℝ) : ℝ :=
  n * (j.factorial * (j * productMinorPartialBound q h C R *
    (1 + productMinorEntryBound q h C R) ^ j))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

noncomputable def booleanBlockParameterEquiv (O α : Type*) [Fintype O] [Fintype α] (h : ℕ) :
    BlockParameter O (Fin h) α ≃ Fin (Fintype.card O * (h * (Fintype.card α + 1))) :=
  Fintype.equivFinOfCardEq (blockParameter_card h)

abbrev BoundedBooleanMonomial (α : Type*) (h : ℕ) := {s : Finset α // s.card ≤ h}

instance boundedBooleanMonomialNonempty (α : Type*) (h : ℕ) :
    Nonempty (BoundedBooleanMonomial α h) :=
  ⟨⟨∅, by simp⟩⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothHalfspaceCutoff
namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

theorem exists_smoothTransition_lipschitz :
    ∃ A : ℝ≥0, 1 ≤ A ∧ LipschitzWith A Real.smoothTransition := by
  have hs : ContDiffOn ℝ 1 Real.smoothTransition (Set.Icc (0 : ℝ) 1) :=
    Real.smoothTransition.contDiff.contDiffOn
  obtain ⟨K, hK⟩ := hs.exists_lipschitzOnWith one_ne_zero (convex_Icc _ _) isCompact_Icc
  have hglobal : LipschitzWith K Real.smoothTransition := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hx := (Set.projIcc (0 : ℝ) 1 zero_le_one x).property
    have hy := (Set.projIcc (0 : ℝ) 1 zero_le_one y).property
    have h := hK.dist_le_mul _ hx _ hy
    simp only [Real.smoothTransition.projIcc] at h
    have hp := (LipschitzWith.projIcc (a := (0 : ℝ)) (b := 1) zero_le_one).dist_le_mul x y
    simp only [NNReal.coe_one, one_mul] at hp
    exact h.trans (mul_le_mul_of_nonneg_left hp K.coe_nonneg)
  exact ⟨K + 1, by simp, hglobal.weaken (by simp)⟩

noncomputable def halfspaceCutoff {E : Type*} (r : ℝ) (d : E → ℝ) (x : E) : ℝ :=
  Real.smoothTransition (d x / r - 1)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarCubeDomain
namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff NNReal

def positiveInequalityDomain {I E : Type*} (d : I → E → ℝ) : Set E :=
  {x | ∀ i, 0 < d i x}

theorem positiveInequalityDomain_isOpen {I E : Type*} [Fintype I] [TopologicalSpace E]
    (d : I → E → ℝ) (hd : ∀ i, Continuous (d i)) : IsOpen (positiveInequalityDomain d) := by
  have heq : positiveInequalityDomain d = ⋂ i, {x | 0 < d i x} := by
    ext x
    simp [positiveInequalityDomain]
  rw [heq]
  exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (hd i))

noncomputable def inequalityBoundaryCutoff {I E : Type*} [Fintype I]
    (r : I → ℝ) (d : I → E → ℝ) (x : E) : ℝ :=
  ∏ i, halfspaceCutoff (r i) (d i) x

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators ContDiff

noncomputable def scalarCubeValue {α : Type*} [Fintype α] [DecidableEq α]
    (a : Option α → ℝ) (t : Finset α) : ℝ :=
  ∑ r : Option α, (booleanFeature r t : ℝ) * a r

theorem scalarCubeValue_empty {α : Type*} [Fintype α] [DecidableEq α]
    (a : Option α → ℝ) : scalarCubeValue a ∅ = a none := by
  simp [scalarCubeValue, Fintype.sum_option, booleanFeature]

theorem scalarCubeValue_singleton {α : Type*} [Fintype α] [DecidableEq α]
    (a : Option α → ℝ) (i : α) : scalarCubeValue a {i} = a none + a (some i) := by
  simp [scalarCubeValue, Fintype.sum_option, booleanFeature]

theorem scalarCubeValue_contDiff {α : Type*} [Fintype α] [DecidableEq α] (t : Finset α) :
    ContDiff ℝ ∞ (fun a : Option α → ℝ => scalarCubeValue a t) := by
  unfold scalarCubeValue
  apply ContDiff.sum
  intro r _
  exact contDiff_const.mul (ContinuousLinearMap.proj r : (Option α → ℝ) →L[ℝ] ℝ).contDiff

def scalarCubeDomain (α : Type*) [Fintype α] [DecidableEq α] : Set (Option α → ℝ) :=
  {a | ∀ t : Finset α, scalarCubeValue a t ∈ Set.Ioo (0 : ℝ) 1}

noncomputable def scalarCubeFace {α : Type*} [Fintype α] [DecidableEq α]
    (i : Bool × Finset α) (a : Option α → ℝ) : ℝ :=
  if i.1 then 1 - scalarCubeValue a i.2 else scalarCubeValue a i.2

theorem scalarCubeFace_contDiff {α : Type*} [Fintype α] [DecidableEq α] (i : Bool × Finset α) :
    ContDiff ℝ ∞ (scalarCubeFace i) := by
  rcases i with ⟨b, t⟩
  cases b with
  | false => exact scalarCubeValue_contDiff t
  | true => exact contDiff_const.sub (scalarCubeValue_contDiff t)

theorem positiveInequalityDomain_scalarCubeFace (α : Type*) [Fintype α] [DecidableEq α] :
    positiveInequalityDomain (@scalarCubeFace α _ _) = scalarCubeDomain α := by
  ext a
  constructor
  · intro ha t
    have hlo : 0 < scalarCubeValue a t := ha (false, t)
    have hhi : 0 < 1 - scalarCubeValue a t := ha (true, t)
    exact ⟨hlo, by linarith⟩
  · intro ha i
    rcases i with ⟨b, t⟩
    cases b with
    | false => exact (ha t).1
    | true => exact sub_pos.mpr (ha t).2

theorem scalarCubeDomain_isOpen (α : Type*) [Fintype α] [DecidableEq α] :
    IsOpen (scalarCubeDomain α) := by
  rw [← positiveInequalityDomain_scalarCubeFace α]
  exact positiveInequalityDomain_isOpen _ (fun i => (scalarCubeFace_contDiff i).continuous)

theorem scalarCubeDomain_coordinate_abs_lt_one {α : Type*} [Fintype α] [DecidableEq α]
    {a : Option α → ℝ} (ha : a ∈ scalarCubeDomain α) (r : Option α) : |a r| < 1 := by
  have hzero := ha ∅
  rw [scalarCubeValue_empty] at hzero
  cases r with
  | none => exact abs_lt.mpr ⟨by linarith [hzero.1], hzero.2⟩
  | some i =>
    have hi := ha {i}
    rw [scalarCubeValue_singleton] at hi
    exact abs_lt.mpr ⟨by linarith [hzero.1, hzero.2, hi.1], by linarith [hzero.1, hi.2]⟩

theorem scalarCubeDomain_isBounded (α : Type*) [Fintype α] [DecidableEq α] :
    Bornology.IsBounded (scalarCubeDomain α) := by
  apply (Metric.isBounded_closedBall (x := (0 : Option α → ℝ)) (r := 1)).subset
  intro a ha
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro r
  simpa only [Real.norm_eq_abs] using (scalarCubeDomain_coordinate_abs_lt_one ha r).le

noncomputable def scalarCubeCenter (α : Type*) : Option α → ℝ
  | none => 1 / 2
  | some _ => 0

theorem scalarCubeValue_center {α : Type*} [Fintype α] [DecidableEq α] (t : Finset α) :
    scalarCubeValue (scalarCubeCenter α) t = 1 / 2 := by
  simp [scalarCubeValue, Fintype.sum_option, scalarCubeCenter, booleanFeature]

theorem scalarCubeDomain_nonempty (α : Type*) [Fintype α] [DecidableEq α] :
    (scalarCubeDomain α).Nonempty := by
  refine ⟨scalarCubeCenter α, ?_⟩
  intro t
  rw [scalarCubeValue_center]
  norm_num

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeDomainDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem scalarCubeDomain_volume_pos (α : Type*) [Fintype α] [DecidableEq α] :
    0 < volume (scalarCubeDomain α) :=
  (scalarCubeDomain_isOpen α).measure_pos volume (scalarCubeDomain_nonempty α)

theorem scalarCubeDomain_volume_lt_top (α : Type*) [Fintype α] [DecidableEq α] :
    volume (scalarCubeDomain α) < ⊤ :=
  (measure_mono subset_closure).trans_lt (scalarCubeDomain_isBounded α).isCompact_closure.measure_lt_top

theorem scalarCubeDomain_volumeReal_pos (α : Type*) [Fintype α] [DecidableEq α] :
    0 < volume.real (scalarCubeDomain α) :=
  ENNReal.toReal_pos (scalarCubeDomain_volume_pos α).ne' (scalarCubeDomain_volume_lt_top α).ne

noncomputable def scalarCubeDomainDensity (α : Type*) [Fintype α] [DecidableEq α] : ℝ :=
  (volume.real (scalarCubeDomain α))⁻¹

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarCubeBoundaryCost
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def scalarCubeLinearMap {α : Type*} [Fintype α] [DecidableEq α] (t : Finset α) :
    (Option α → ℝ) →L[ℝ] ℝ :=
  ∑ r : Option α, (booleanFeature r t : ℝ) • ContinuousLinearMap.proj r

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ScalarCubeCoordinates
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def scalarCubeJoin {α : Type*} (z : (α → ℝ) × ℝ) : Option α → ℝ :=
  (MeasurableEquiv.piOptionEquivProd (fun _ : Option α => ℝ)).symm z

theorem scalarCubeJoin_none {α : Type*} (z : (α → ℝ) × ℝ) : scalarCubeJoin z none = z.2 := rfl

theorem scalarCubeJoin_some {α : Type*} (z : (α → ℝ) × ℝ) (i : α) :
    scalarCubeJoin z (some i) = z.1 i := rfl

theorem scalarCubeJoin_measurable (α : Type*) : Measurable (@scalarCubeJoin α) :=
  (MeasurableEquiv.piOptionEquivProd (fun _ : Option α => ℝ)).symm.measurable

theorem scalarCubeJoin_measurePreserving (α : Type*) [Fintype α] :
    MeasurePreserving (@scalarCubeJoin α) volume volume := by
  refine ⟨scalarCubeJoin_measurable α, ?_⟩
  exact Measure.pi_map_piOptionEquivProd (fun _ : Option α => (volume : Measure ℝ))

theorem scalarCubeJoin_value {α : Type*} [Fintype α] [DecidableEq α]
    (z : (α → ℝ) × ℝ) (t : Finset α) :
    scalarCubeValue (scalarCubeJoin z) t = z.2 + ∑ i ∈ t, z.1 i := by
  simp [scalarCubeValue, Fintype.sum_option, booleanFeature, scalarCubeJoin_none,
    scalarCubeJoin_some, ite_mul]

theorem scalarCubeJoin_face {α : Type*} [Fintype α] [DecidableEq α]
    (z : (α → ℝ) × ℝ) (i : Bool × Finset α) :
    scalarCubeFace i (scalarCubeJoin z) =
      if i.1 then 1 - (z.2 + ∑ k ∈ i.2, z.1 k) else z.2 + ∑ k ∈ i.2, z.1 k := by
  simp only [scalarCubeFace, scalarCubeJoin_value]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarCubeBoundaryVolume
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

def scalarCubeFaceStrip {α : Type*} [Fintype α] [DecidableEq α]
    (i : Bool × Finset α) (u : ℝ) : Set (Option α → ℝ) :=
  scalarCubeDomain α ∩ {a | scalarCubeFace i a < u}

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeBoundaryMass
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def scalarCubeMeasure (α : Type*) [Fintype α] [DecidableEq α] :
    Measure (Option α → ℝ) :=
  (volume (scalarCubeDomain α))⁻¹ • volume.restrict (scalarCubeDomain α)

instance scalarCubeMeasure_probability (α : Type*) [Fintype α] [DecidableEq α] :
    IsProbabilityMeasure (scalarCubeMeasure α) := by
  constructor
  simp only [scalarCubeMeasure, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (scalarCubeDomain_volume_pos α).ne' (scalarCubeDomain_volume_lt_top α).ne

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

noncomputable def oneCubeEndpointEquiv : (Option (Fin 1) → ℝ) ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 1) => ℝ)).trans
    (((MeasurableEquiv.funUnique (Fin 1) ℝ).prodCongr (MeasurableEquiv.refl ℝ)).trans
      ((MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ).trans (MeasurableEquiv.shearAddRight ℝ)))

@[simp] theorem oneCubeEndpointEquiv_apply (a : Option (Fin 1) → ℝ) :
    oneCubeEndpointEquiv a = (a none, a none + a (some 0)) := rfl

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def scalarCubeBoundaryConstant (α : Type*) [Fintype α] [DecidableEq α] : ℝ :=
  4 * scalarCubeDomainDensity α * ((2 : ℝ) ^ Fintype.card α) ^ 2

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarCubeFaceSlab
namespace OAI

section

namespace Erdos3

open MeasureTheory

def closedScalarCubeDomain (α : Type*) [Fintype α] [DecidableEq α] : Set (Option α → ℝ) :=
  {a | ∀ t : Finset α, scalarCubeValue a t ∈ Set.Icc (0 : ℝ) 1}

theorem scalarCubeDomain_subset_closed (α : Type*) [Fintype α] [DecidableEq α] :
    scalarCubeDomain α ⊆ closedScalarCubeDomain α :=
  fun _ ha t => ⟨(ha t).1.le, (ha t).2.le⟩

theorem closedScalarCubeDomain_isClosed (α : Type*) [Fintype α] [DecidableEq α] :
    IsClosed (closedScalarCubeDomain α) := by
  have heq : closedScalarCubeDomain α = ⋂ t : Finset α, {a | scalarCubeValue a t ∈ Set.Icc (0 : ℝ) 1} := by
    ext a
    simp [closedScalarCubeDomain]
  rw [heq]
  exact isClosed_iInter (fun t => isClosed_Icc.preimage (scalarCubeValue_contDiff t).continuous)

theorem closedScalarCubeDomain_iff_faces {α : Type*} [Fintype α] [DecidableEq α]
    (a : Option α → ℝ) : a ∈ closedScalarCubeDomain α ↔ ∀ i, 0 ≤ scalarCubeFace i a := by
  constructor
  · intro ha i
    rcases i with ⟨side, t⟩
    cases side with
    | false => exact (ha t).1
    | true => exact sub_nonneg.mpr (ha t).2
  · intro ha t
    have hlo : 0 ≤ scalarCubeValue a t := ha (false, t)
    have hhi : 0 ≤ 1 - scalarCubeValue a t := ha (true, t)
    exact ⟨hlo, by linarith⟩

theorem closedScalarCubeDomain_coordinate_abs_le_one {α : Type*} [Fintype α] [DecidableEq α]
    {a : Option α → ℝ} (ha : a ∈ closedScalarCubeDomain α) (r : Option α) : |a r| ≤ 1 := by
  have hzero := ha ∅
  rw [scalarCubeValue_empty] at hzero
  cases r with
  | none => exact abs_le.mpr ⟨by linarith [hzero.1], hzero.2⟩
  | some i =>
    have hi := ha {i}
    rw [scalarCubeValue_singleton] at hi
    exact abs_le.mpr ⟨by linarith [hzero.2, hi.1], by linarith [hzero.1, hi.2]⟩

theorem closedScalarCubeDomain_compact (α : Type*) [Fintype α] [DecidableEq α] :
    IsCompact (closedScalarCubeDomain α) := by
  apply Metric.isCompact_of_isClosed_isBounded (closedScalarCubeDomain_isClosed α)
  apply (Metric.isBounded_closedBall (x := (0 : Option α → ℝ)) (r := 1)).subset
  intro a ha
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro r
  simpa only [Real.norm_eq_abs] using closedScalarCubeDomain_coordinate_abs_le_one ha r

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem closedScalarCubeFace_zero_volume {α : Type*} [Fintype α] [DecidableEq α]
    (i : Bool × Finset α) :
    volume (closedScalarCubeDomain α ∩ {a | scalarCubeFace i a = 0}) = 0 := by
  let Z := closedScalarCubeDomain α ∩ {a | scalarCubeFace i a = 0}
  have hZm : MeasurableSet Z := (closedScalarCubeDomain_isClosed α).measurableSet.inter
    (measurableSet_eq_fun (scalarCubeFace_contDiff i).continuous.measurable measurable_const)
  have hZfin : volume Z ≠ ⊤ := ne_of_lt ((measure_mono Set.inter_subset_left).trans_lt
    (closedScalarCubeDomain_compact α).measure_lt_top)
  let s : Set ((α → ℝ) × ℝ) := scalarCubeJoin ⁻¹' Z
  have hs : MeasurableSet s := hZm.preimage (scalarCubeJoin_measurable α)
  have hm := (scalarCubeJoin_measurePreserving α).measure_preimage hZm.nullMeasurableSet
  have hmr := (scalarCubeJoin_measurePreserving α).measureReal_preimage hZm.nullMeasurableSet
  have hsfin : (volume : Measure ((α → ℝ) × ℝ)) s ≠ ⊤ := by
    change volume (scalarCubeJoin ⁻¹' Z) ≠ ⊤
    rw [hm]
    exact hZfin
  have hbase : ∀ z ∈ s, z.1 ∈ Metric.closedBall (0 : α → ℝ) 1 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro k
    have h := closedScalarCubeDomain_coordinate_abs_le_one hz.1 (some k)
    simpa only [Real.norm_eq_abs, scalarCubeJoin_some] using h
  have hbound : ∀ b : α → ℝ, volume.real {y | (b, y) ∈ s} ≤ 0 := by
    intro b
    let c : ℝ := if i.1 then 1 - ∑ k ∈ i.2, b k else -(∑ k ∈ i.2, b k)
    have hsub : {y | (b, y) ∈ s} ⊆ {c} := by
      intro y hy
      have heq : scalarCubeFace i (scalarCubeJoin (b, y)) = 0 := hy.2
      rw [scalarCubeJoin_face] at heq
      apply Set.mem_singleton_iff.mpr
      dsimp [c]
      split_ifs at heq ⊢ <;> linarith
    have h := measureReal_mono (μ := volume) hsub (by simp)
    simpa [measureReal_def] using h
  have h := product_measureReal_le_of_fiber_bound
    (volume : Measure (α → ℝ)) (volume : Measure ℝ) s hs hsfin
    (Metric.closedBall (0 : α → ℝ) 1) measurableSet_closedBall
    (isCompact_closedBall _ _).measure_ne_top hbase hbound
  change volume.real s ≤ _ at h
  rw [hmr, mul_zero] at h
  exact (measureReal_eq_zero_iff hZfin).mp (le_antisymm h measureReal_nonneg)

theorem closedScalarCubeDomain_boundary_null (α : Type*) [Fintype α] [DecidableEq α] :
    volume (closedScalarCubeDomain α \ scalarCubeDomain α) = 0 := by
  have hsub : closedScalarCubeDomain α \ scalarCubeDomain α ⊆
      ⋃ i : Bool × Finset α, closedScalarCubeDomain α ∩ {a | scalarCubeFace i a = 0} := by
    intro a ha
    have hn : ¬ ∀ i, 0 < scalarCubeFace i a := by
      intro hp
      apply ha.2
      rw [← positiveInequalityDomain_scalarCubeFace α]
      exact hp
    obtain ⟨i, hi⟩ := not_forall.mp hn
    have hz : scalarCubeFace i a = 0 := le_antisymm (le_of_not_gt hi)
      ((closedScalarCubeDomain_iff_faces a).mp ha.1 i)
    exact Set.mem_iUnion.mpr ⟨i, ha.1, hz⟩
  exact measure_mono_null hsub (measure_iUnion_null closedScalarCubeFace_zero_volume)

theorem scalarCubeDomain_ae_closed (α : Type*) [Fintype α] [DecidableEq α] :
    scalarCubeDomain α =ᵐ[volume] closedScalarCubeDomain α := by
  apply ae_eq_set.mpr
  constructor
  · have he : scalarCubeDomain α \ closedScalarCubeDomain α = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro a ha
      exact ha.2 (scalarCubeDomain_subset_closed α ha.1)
    rw [he, measure_empty]
  · exact closedScalarCubeDomain_boundary_null α

noncomputable def closedScalarCubeMeasure (α : Type*) [Fintype α] [DecidableEq α] :
    Measure (Option α → ℝ) :=
  (volume (closedScalarCubeDomain α))⁻¹ • volume.restrict (closedScalarCubeDomain α)

theorem closedScalarCubeMeasure_eq (α : Type*) [Fintype α] [DecidableEq α] :
    closedScalarCubeMeasure α = scalarCubeMeasure α := by
  have hvol := measure_congr (scalarCubeDomain_ae_closed α)
  have hrestrict := Measure.restrict_congr_set (scalarCubeDomain_ae_closed α)
  simp only [closedScalarCubeMeasure, scalarCubeMeasure, ← hvol, ← hrestrict]

instance closedScalarCubeMeasure_probability (α : Type*) [Fintype α] [DecidableEq α] :
    IsProbabilityMeasure (closedScalarCubeMeasure α) := by
  rw [closedScalarCubeMeasure_eq]
  infer_instance

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Classical

def halfOpenScalarCubeDomain (I : Type*) [Fintype I] [DecidableEq I] : Set (Option I → ℝ) :=
  {x | ∀ t : Finset I, scalarCubeValue x t ∈ Set.Ico (0 : ℝ) 1}

theorem halfOpenScalarCubeDomain_subset_closed (I : Type*) [Fintype I] [DecidableEq I] :
    halfOpenScalarCubeDomain I ⊆ closedScalarCubeDomain I :=
  fun _ hx t => ⟨(hx t).1, (hx t).2.le⟩

theorem halfOpenScalarCubeDomain_norm_le {I : Type*} [Fintype I] [DecidableEq I]
    {x : Option I → ℝ} (hx : x ∈ halfOpenScalarCubeDomain I) : ‖x‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  exact closedScalarCubeDomain_coordinate_abs_le_one (halfOpenScalarCubeDomain_subset_closed I hx) i

noncomputable def scalarCubeIndicator (I : Type*) [Fintype I] [DecidableEq I]
    (x : Option I → ℝ) : ℝ := if x ∈ halfOpenScalarCubeDomain I then 1 else 0

theorem scalarCubeIndicator_zero_outside (I : Type*) [Fintype I] [DecidableEq I]
    (x : Option I → ℝ) (hx : 1 < ‖x‖) : scalarCubeIndicator I x = 0 := by
  apply if_neg
  exact fun h => (not_lt_of_ge (halfOpenScalarCubeDomain_norm_le h)) hx

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

def scalarCubeFaceSlab {I : Type*} [Fintype I] [DecidableEq I]
    (i : Bool × Finset I) (u : ℝ) : Set (Option I → ℝ) :=
  Metric.closedBall 0 2 ∩ {x | |scalarCubeFace i x| ≤ u}

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScaledCubeProductMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

def scalarCubeProductDomain (ι α : Type*) [Fintype ι] [Fintype α] [DecidableEq α] :
    Set (ι → Option α → ℝ) := Set.univ.pi (fun _ => scalarCubeDomain α)

noncomputable def scalarCubeProductMeasure (ι α : Type*) [Fintype ι] [Fintype α]
    [DecidableEq α] : Measure (ι → Option α → ℝ) :=
  Measure.pi (fun _ : ι => scalarCubeMeasure α)

instance scalarCubeProductMeasure_probability (ι α : Type*) [Fintype ι] [Fintype α]
    [DecidableEq α] : IsProbabilityMeasure (scalarCubeProductMeasure ι α) := by
  unfold scalarCubeProductMeasure
  infer_instance

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable (ι : Type*) [Fintype ι]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductCutoffLipschitz
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def finiteRectangleRefinement {I : Type*} (K N : I → ℕ) :
    ((∀ i, Fin (K i)) × (∀ i, Fin (N i))) ≃ (∀ i, Fin (K i * N i)) where
  toFun x i := finProdFinEquiv (x.1 i, x.2 i)
  invFun y := (fun i => (finProdFinEquiv.symm (y i)).1,
    fun i => (finProdFinEquiv.symm (y i)).2)
  left_inv x := by
    apply Prod.ext <;> funext i <;> simp
  right_inv y := by
    funext i
    exact finProdFinEquiv.apply_symm_apply (y i)

end Erdos3

end

section

namespace Erdos3

noncomputable def progressionCellCorner {I : Type*} (N : I → ℕ) (u v : I → ℝ)
    {K : I → ℕ} (k : ∀ i, Fin (K i)) : I → ℝ :=
  fun i => u i + v i * (N i * (k i).val : ℕ)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def scalarCubeCutoffLipschitzConstant (I : Type*) [Fintype I]
    (A : ℝ≥0) (r : ℝ≥0) : ℝ≥0 :=
  (2 * 2 ^ Fintype.card I : ℕ) * (A / r * (Fintype.card I + 1))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

noncomputable def scalarCubeCutoffWeight {α : Type*} [Fintype α] [DecidableEq α]
    (b : (Option α → ℝ) → ℝ) (a : Option α → ℝ) : ℝ := scalarCubeDomainDensity α * b a

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

noncomputable def scalarCubeBoundaryWeight (α : Type*) [Fintype α] [DecidableEq α]
    (r : ℝ) : (Option α → ℝ) → ℝ :=
  scalarCubeCutoffWeight (inequalityBoundaryCutoff (fun _ : Bool × Finset α => r) scalarCubeFace)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

noncomputable def scalarCubeProductWeight {ι : Type*} [Fintype ι]
    (α : Type*) [Fintype α] [DecidableEq α] (r : ι → ℝ) : (ι → Option α → ℝ) → ℝ :=
  tensorCutoffWeight (fun i => scalarCubeBoundaryWeight α (r i))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

noncomputable def scalarCubeProductCutoff {ι : Type*} [Fintype ι]
    (α : Type*) [Fintype α] [DecidableEq α] (r : ι → ℝ) : (ι → Option α → ℝ) → ℝ :=
  tensorCutoffWeight (fun i => inequalityBoundaryCutoff
    (fun _ : Bool × Finset α => r i) scalarCubeFace)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ResidualErrorAllocation
namespace OAI

section

namespace Erdos3

theorem inv_min_le_of_inv_le {a b M : ℝ} (ha : a⁻¹ ≤ M) (hb : b⁻¹ ≤ M) :
    (min a b)⁻¹ ≤ M := by
  rcases le_total a b with h | h
  · simpa only [min_eq_left h] using ha
  · simpa only [min_eq_right h] using hb

theorem one_add_le_exp_succ {x P : ℝ} (hP : 0 ≤ P) (hx : x ≤ Real.exp P) :
    1+x ≤ Real.exp (P+1) := by
  have h1 : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ 2*Real.exp P := by linarith
    _ ≤ Real.exp 1*Real.exp P := mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

end Erdos3

end

section

namespace Erdos3.NativeModelingNumerics

end Erdos3.NativeModelingNumerics

end

section

namespace Erdos3

noncomputable def regularizationRadius (L ε : ℝ) : ℝ := min 1 (ε/(2*(1+L)))

end Erdos3

end

section

namespace Erdos3

noncomputable def twoTermErrorResolution (T A ε : ℝ) : ℝ := 1+T+2*A/ε

noncomputable def twoTermErrorWidth (B ε : ℝ) : ℝ := min 1 (ε/(2*(1+B)))

theorem twoTermErrorChoices_log_bounds {T A B ε P : ℝ}
    (hA0 : 0 ≤ A) (_hB0 : 0 ≤ B) (hε : 0 < ε) (hP : 0 ≤ P)
    (hT : T ≤ Real.exp P) (hA : A ≤ Real.exp P) (hB : B ≤ Real.exp P)
    (hi : ε⁻¹ ≤ Real.exp P) :
    twoTermErrorResolution T A ε ≤ Real.exp (2*P+4) ∧
    (twoTermErrorWidth B ε)⁻¹ ≤ Real.exp (2*P+4) := by
  have h1 : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have hsq : Real.exp P ≤ (Real.exp P)^2 := by nlinarith
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hbound : 4*(Real.exp P)^2 ≤ Real.exp (2*P+4) := by
    calc
      _ ≤ Real.exp 4*(Real.exp P)^2 := mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  constructor
  · apply le_trans _ hbound
    unfold twoTermErrorResolution
    rw [div_eq_mul_inv]
    have hm : 2*A*ε⁻¹ ≤ 2*Real.exp P*Real.exp P := by gcongr
    nlinarith
  · unfold twoTermErrorWidth
    apply inv_min_le_of_inv_le
    · simpa only [inv_one] using Real.one_le_exp_iff.mpr (by positivity : 0 ≤ 2*P+4)
    · apply le_trans _ hbound
      rw [inv_div, div_eq_mul_inv]
      have hm : 2*(1+B)*ε⁻¹ ≤ 2*(1+Real.exp P)*Real.exp P := by gcongr
      nlinarith

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

noncomputable def replacementAccuracy (B epsilon : ℝ) : ℝ := min 1 (epsilon / (1 + B))

end Erdos3

end

section

namespace Erdos3

noncomputable def replacementScaleThreshold (C delta rho J Q R U : ℝ) : ℝ :=
  1 + 2 * C / delta + 4 * J / rho + 4 / rho + U + R * Q

end Erdos3

end

section

namespace Erdos3

noncomputable def residualPointAccuracy (M S F mesh epsilon : ℝ) : ℝ :=
  min (replacementAccuracy (6 * M * S * F) epsilon) (replacementAccuracy (2 * mesh) 1)

noncomputable def residualGridAccuracy (M S K epsilon : ℝ) : ℝ :=
  replacementAccuracy (6 * M * S * K) epsilon

noncomputable def residualMeanAccuracy (M K V epsilon : ℝ) : ℝ :=
  replacementAccuracy (V ^ 2 * (1 + 3 * M * K)) (min 1 epsilon)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScalarCubeLatticeGeometry
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem scalarCubeValue_formula {I : Type*} [Fintype I] [DecidableEq I]
    (x : Option I → ℝ) (t : Finset I) :
    scalarCubeValue x t = x none + ∑ i ∈ t, x (some i) := by
  simp [scalarCubeValue, Fintype.sum_option, booleanFeature, ite_mul]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeDensityBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def scalarCubeInnerBox (I : Type*) [Fintype I] : Set (Option I → ℝ) :=
  Set.Icc (fun i => scalarCubeCenter I i-1/(4*((Fintype.card I : ℝ)+1)))
    (fun i => scalarCubeCenter I i+1/(4*((Fintype.card I : ℝ)+1)))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScalarCubeBoundaryLogBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

noncomputable def scalarCubeProductBoundaryRadius (ι α : Type*) [Fintype ι] [Fintype α]
    [DecidableEq α] (η : ℝ) : ℝ :=
  η / (scalarCubeBoundaryConstant α * ((Fintype.card ι : ℝ) + 1))

noncomputable def scalarCubeProductDerivativeConstant (α : Type*) [Fintype α]
    [DecidableEq α] (A : ℝ≥0) : ℝ :=
  ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) * ((Fintype.card α : ℝ) + 1) ^ 2 * A *
    scalarCubeBoundaryConstant α

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

def scalarCubeBoundaryLog (q : ℕ) : ℝ := ((q : ℝ)+1)^2+2*q+2
def scalarCubeDerivativeLog (q : ℕ) (P : ℝ) : ℝ := P+3*q+1+scalarCubeBoundaryLog q

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitTestClipping
namespace OAI

section

namespace Erdos3

open MeasureTheory

def unitTestClip (x : ℝ) : ℝ := max (-1) (min 1 x)

theorem unitTestClip_mem (x : ℝ) : unitTestClip x ∈ Set.Icc (-1 : ℝ) 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialParameterContinuity
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mvPolynomial_pderiv_degreeOf_le {I : Type*} [DecidableEq I]
    (p : MvPolynomial I ℝ) (j i : I) {d : ℕ} (hd : p.degreeOf i ≤ d) :
    (MvPolynomial.pderiv j p).degreeOf i ≤ d := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro m hm
  have hc : p.coeff (m + Finsupp.single j 1) ≠ 0 := by
    intro hz
    apply MvPolynomial.mem_support_iff.mp hm
    rw [MvPolynomial.coeff_pderiv, hz, zero_mul]
  have hb := MvPolynomial.degreeOf_le_iff.mp hd _ (MvPolynomial.mem_support_iff.mpr hc)
  have hi : m i ≤ (m + Finsupp.single j 1 : I →₀ ℕ) i := by simp only [Finsupp.add_apply]; omega
  exact hi.trans hb

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

variable {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]

noncomputable def polynomialVectorMap (p : O → MvPolynomial I ℝ) (x : I → ℝ) (o : O) : ℝ :=
  MvPolynomial.eval x (p o)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def polynomialBoxLip (n d : ℕ) (C : ℝ≥0) : ℝ≥0 :=
  n * ((d+1 : ℝ≥0)^n * (d*C))

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

abbrev PolynomialParameter (Z I : Type*) := Option (Z ⊕ I)

def polynomialParameterPoint {Z I : Type*} (t : ℝ) (z : Z → ℝ) (x : I → ℝ) :
    PolynomialParameter Z I → ℝ := fun s => match s with
  | none => t
  | some (.inl j) => z j
  | some (.inr i) => x i

noncomputable def polynomialParameterInjection (Z I : Type*) [Fintype I] :
    (I → ℝ) →L[ℝ] (PolynomialParameter Z I → ℝ) :=
  ContinuousLinearMap.pi (fun s => match s with
    | none => 0
    | some (.inl _) => 0
    | some (.inr i) => ContinuousLinearMap.proj i)

noncomputable def parameterPolynomialMap {Z I O : Type*} [Fintype Z] [Fintype I] [Fintype O]
    (p : O → MvPolynomial (PolynomialParameter Z I) ℝ) (t : ℝ) (z : Z → ℝ) (x : I → ℝ) : O → ℝ :=
  polynomialVectorMap p (polynomialParameterPoint t z x)

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators ContDiff

theorem realPolynomialMass_pderiv_degreeOf {I : Type*} (p : MvPolynomial I ℝ)
    (i : I) {d : ℕ} (hd : p.degreeOf i ≤ d) :
    realPolynomialMass (pderiv i p) ≤ (d : ℝ) * realPolynomialMass p := by
  classical
  conv_lhs => rw [← p.support_sum_monomial_coeff, map_sum]
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ m ∈ p.support, (d : ℝ) * |p.coeff m| := by
      apply Finset.sum_le_sum
      intro m hm
      rw [pderiv_monomial, realPolynomialMass_monomial, abs_mul,
        abs_of_nonneg (show (0 : ℝ) ≤ (m i : ℝ) from Nat.cast_nonneg _)]
      have hmi : (m i : ℝ) ≤ d := by exact_mod_cast (monomial_le_degreeOf i hm).trans hd
      nlinarith [abs_nonneg (p.coeff m)]
    _ = _ := by rw [realPolynomialMass, Finset.mul_sum]

noncomputable def polynomialMassC2Budget (N d : ℕ) (C : ℝ) : ℝ :=
  (1 + (N : ℝ) * d) ^ 2 * C

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def polynomialColumns {P I J : Type*} [Fintype I] [Fintype J]
    (p : I → J → MvPolynomial P ℝ) (x : P → ℝ) : (J → ℝ) →L[ℝ] (I → ℝ) :=
  matrixSupCLM (fun i j => MvPolynomial.eval x (p i j))

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanSelectedDerivativeBound
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators ContDiff

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Topology NNReal BigOperators

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

noncomputable def productMinorInverseBound (j q h : ℕ) (C R κ : ℝ) : ℝ :=
  j * (j.factorial * (productMinorEntryBound q h C R) ^ (j - 1) / κ)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {κ ι : Type*} [Fintype κ] [Fintype ι]

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

def productMinorDerivativeBound (n j q h : ℕ) (C R : ℝ) : ℝ :=
  n * (j * productMinorPartialBound q h C R)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedInequalityGoodCutoff
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

noncomputable def goodDomainCutoff {ι E : Type*} [Fintype ι]
    (ψ : ℝ → ℝ) (r : ι → ℝ) (d : ι → E → ℝ) (b : E → ℝ) (x : E) : ℝ :=
  b x * ∏ i, sublevelCutoff ψ (r i) (d i) x

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

noncomputable def sublevelCutoffProduct {J E : Type*} [Fintype J]
    (ψ : ℝ → ℝ) (κ : J → ℝ) (d : J → E → ℝ) (x : E) : ℝ :=
  ∏ i, sublevelCutoff ψ (κ i) (d i) x

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Topology

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BooleanAffineInput
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def booleanAffineInput {I α : Type*} [Fintype α] [DecidableEq α]
    (a : Option α → MvPolynomial I ℝ) (t : Finset α) : MvPolynomial I ℝ :=
  ∑ r, MvPolynomial.C (booleanFeature r t : ℝ) * a r

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientNormalization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def booleanCoefficientTail {T K I α : Type*} [Fintype α] [DecidableEq α]
    (terms : Finset T) (coefficient : T → MvPolynomial I ℝ)
    (exponent : T → K →₀ ℕ) (input : K → Option α → MvPolynomial I ℝ)
    (s : Finset α) : MvPolynomial I ℝ :=
  booleanCoefficient (fun t => ∑ n ∈ terms,
    coefficient n * polynomialMonomial (fun k => booleanAffineInput (input k) t) (exponent n)) s

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def booleanJetColumnPolynomial {K P α : Type*} [Fintype α] [DecidableEq α]
    (e : K →₀ ℕ) (input : K → Option α → MvPolynomial P ℝ) (s : Finset α) : MvPolynomial P ℝ :=
  booleanCoefficient (fun t => polynomialMonomial (fun k => booleanAffineInput (input k) t) e) s

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def normalizedCoefficientTail {T K Z I α : Type*} [Fintype α] [DecidableEq α]
    (terms : Finset T) (weight : T → ℝ) (exponent : T → K →₀ ℕ)
    (coefficientIndex : T → Z) (inputIndex : K → Option α → Z ⊕ I) (s : Finset α) :
    MvPolynomial (PolynomialParameter Z I) ℝ :=
  booleanCoefficientTail terms
    (fun n => MvPolynomial.C (weight n) * MvPolynomial.X (some (.inl (coefficientIndex n))))
    exponent (fun k r => MvPolynomial.X (some (inputIndex k r))) s

noncomputable def normalizedCoefficientTailValue {T K Z I α : Type*} [Fintype α] [DecidableEq α]
    (terms : Finset T) (weight : T → ℝ) (exponent : T → K →₀ ℕ)
    (coefficientIndex : T → Z) (inputIndex : K → Option α → Z ⊕ I)
    (z : Z → ℝ) (x : I → ℝ) (s : Finset α) : ℝ :=
  booleanCoefficient (fun t => ∑ n ∈ terms, (weight n * z (coefficientIndex n)) *
    ∏ k ∈ (exponent n).support,
      (∑ r, (booleanFeature r t : ℝ) * Sum.elim z x (inputIndex k r)) ^ exponent n k) s

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrincipalCoefficientSource
namespace OAI

section

namespace Erdos3

open MeasureTheory ProbabilityTheory

theorem finiteProductMarginal_measurePreserving {I J X : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace X] (μ : I → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (e : J → I) (he : Function.Injective e) :
    MeasurePreserving (fun x : I → X => fun j => x (e j))
      (Measure.pi μ) (Measure.pi (fun j => μ (e j))) := by
  have hind : iIndepFun (fun i (x : I → X) => x i) (Measure.pi μ) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hsel := iIndepFun.precomp he hind
  have hm := hsel.map_fun_eq_pi_map (fun j => (measurable_pi_apply (e j)).aemeasurable)
  refine ⟨by fun_prop, hm.trans ?_⟩
  congr 1
  funext j
  exact (measurePreserving_eval μ (e j)).map_eq

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BlockCubeCoordinates
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def blockCubeFlatten (B F α : Type*) [Fintype B] [Fintype F] [Fintype α] :
    ((B × F) → Option α → ℝ) ≃L[ℝ] (BlockParameter B F α → ℝ) where
  toLinearEquiv :=
    { toFun := fun x z => x (z.1, z.2.1) z.2.2
      invFun := fun a bf r => a (bf.1, bf.2, r)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SigmaAxisOperator
namespace OAI

section

namespace Erdos3

variable {D : Type*} [Fintype D] {I O P : D → Type*}
  [∀ d, Fintype (I d)] [∀ d, Fintype (O d)] [∀ d, Fintype (P d)]

noncomputable def sigmaAxisOperator (A : ∀ d, (I d → ℝ) →L[ℝ] (O d → ℝ)) :
    ((Σ d, I d) → ℝ) →L[ℝ] ((Σ d, O d) → ℝ) :=
  ContinuousLinearMap.pi (fun s => (ContinuousLinearMap.proj s.2).comp
    ((A s.1).comp (sigmaAxisProjection I s.1)))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MonomialArrayJet
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def monomialArrayPolynomial {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (a : J → ℝ) : MvPolynomial K ℝ :=
  ∑ j, MvPolynomial.monomial (e j) (a j)

theorem monomialArrayPolynomial_eval {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (a : J → ℝ) (x : K → ℝ) :
    MvPolynomial.eval x (monomialArrayPolynomial e a) =
      ∑ j, a j*∏ k ∈ (e j).support, x k^e j k := by
  simp only [monomialArrayPolynomial, map_sum, MvPolynomial.eval_monomial, Finsupp.prod]

theorem monomialArrayPolynomial_coeff {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (he : Function.Injective e) (a : J → ℝ) (j : J) :
    (monomialArrayPolynomial e a).coeff (e j) = a j := by
  classical
  simp only [monomialArrayPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    he.eq_iff]
  simp

theorem monomialArrayPolynomial_coeff_zero_of_not_mem {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (a : J → ℝ) (m : K →₀ ℕ) (hm : ∀ j, e j ≠ m) :
    (monomialArrayPolynomial e a).coeff m = 0 := by
  classical
  simp only [monomialArrayPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  exact Finset.sum_eq_zero (fun j _ => if_neg (hm j))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CanonicalSamplerTuple
namespace OAI

section

namespace Erdos3

open scoped ContDiff NNReal

variable {D : Type*} [Fintype D] {I O : D → Type*}
  [∀ d, Fintype (I d)] [∀ d, Fintype (O d)]

noncomputable def sigmaAxisSampler (U : ∀ d, (I d → ℝ) → (O d → ℝ))
    (x : (Σ d, I d) → ℝ) (s : Σ d, O d) : ℝ :=
  U s.1 (sigmaAxisProjection I s.1 x) s.2

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

abbrev JointBlockParameter {D : Type*} (B : D → Type*) (h : D → ℕ) (α : Type*) :=
  Σ d, BlockParameter (B d) (Fin (h d)) α

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

noncomputable def jointBooleanSampler (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) :
    (JointBlockParameter B h α → ℝ) → ((Σ d, O d) → ℝ) :=
  sigmaAxisSampler (fun d => booleanSamplerMap (F := Fin (h d)) (c d) (sets d))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

abbrev PrincipalTupleIndex {D : Type*} (B : D → Type*) (h : D → ℕ) :=
  Σ d, B d × Fin (h d)

abbrev SamplerTupleIndex {D : Type*} (G : Type*) (B : D → Type*) (h : D → ℕ) :=
  G ⊕ PrincipalTupleIndex B h

def canonicalTupleInput {D G Z α : Type*} {B : D → Type*} {h : D → ℕ}
    (extra : G → Option α → Z) : SamplerTupleIndex G B h → Option α → Z ⊕ JointBlockParameter B h α
  | .inl g, r => .inl (extra g r)
  | .inr ⟨d, b, v⟩, r => .inr ⟨d, b, v, r⟩

theorem samplerTupleIndex_card {D G : Type*} [Fintype D] [Fintype G]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ) :
    Fintype.card (SamplerTupleIndex G B h) = Fintype.card G + ∑ d, Fintype.card (B d) * h d := by
  simp only [SamplerTupleIndex, PrincipalTupleIndex, Fintype.card_sum, Fintype.card_sigma,
    Fintype.card_prod, Fintype.card_fin]

noncomputable def normalizedCubeTuple {K Z I α : Type*} [Fintype α] [DecidableEq α]
    (input : K → Option α → Z ⊕ I) (z : Z → ℝ) (x : I → ℝ) (vertex : Finset α) (k : K) : ℝ :=
  ∑ r : Option α, (booleanFeature r vertex : ℝ) * Sum.elim z x (input k r)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JointBooleanGoodWeight
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def blockCubeWeight {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    (w : ((B × F) → Option α → ℝ) → ℝ) (a : BlockParameter B F α → ℝ) : ℝ :=
  w ((blockCubeFlatten B F α).symm a)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

noncomputable def blockCubeMeasure (B F α : Type*) [Fintype B] [Fintype F] [Fintype α]
    [DecidableEq α] : Measure (BlockParameter B F α → ℝ) :=
  Measure.map (blockCubeFlatten B F α) (scalarCubeProductMeasure (B × F) α)

instance blockCubeMeasure_probability (B F α : Type*) [Fintype B] [Fintype F] [Fintype α]
    [DecidableEq α] : IsProbabilityMeasure (blockCubeMeasure B F α) := by
  constructor
  rw [blockCubeMeasure, Measure.map_apply (blockCubeFlatten B F α).continuous.measurable
    MeasurableSet.univ, Set.preimage_univ, measure_univ]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

noncomputable def scalarCubeGoodWeight {I J : Type*} [Fintype I] [Fintype J]
    (α : Type*) [Fintype α] [DecidableEq α] (ψ : ℝ → ℝ) (r : I → ℝ) (κ : J → ℝ)
    (d : J → (I → Option α → ℝ) → ℝ) (x : I → Option α → ℝ) : ℝ :=
  scalarCubeProductWeight α r x * sublevelCutoffProduct ψ κ d x

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DensityMixtureAELaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def scalarDensityConvolution (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t, f (x - t) * g t

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem realDensityMeasure_map_equiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (μ : Measure X) (f : X → ℝ) :
    Measure.map e (realDensityMeasure μ f) =
      realDensityMeasure (Measure.map e μ) (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, realDensityMeasure, realDensityMeasure,
    withDensity_apply _ (e.measurable hs), withDensity_apply _ hs,
    e.restrict_map, e.measurableEmbedding.lintegral_map]
  simp only [e.symm_apply_apply]

theorem realDensityMeasure_pi {D : Type*} [Fintype D] {E : D → Type*}
    [∀ d, MeasurableSpace (E d)] (μ : ∀ d, Measure (E d)) [∀ d, SigmaFinite (μ d)]
    (f : ∀ d, E d → ℝ) (hf : ∀ d, Integrable (f d) (μ d)) (hf0 : ∀ d x, 0 ≤ f d x) :
    Measure.pi (fun d => realDensityMeasure (μ d) (f d)) =
      realDensityMeasure (Measure.pi μ) (tensorCutoffWeight f) := by
  let : ∀ d, IsFiniteMeasure (realDensityMeasure (μ d) (f d)) :=
    fun d => realDensityMeasure_finite (μ d) (f d) (hf d) (hf0 d)
  apply Measure.pi_eq
  intro s hs
  have hfi : Integrable (tensorCutoffWeight f) (Measure.pi μ) := Integrable.fintype_prod_dep hf
  rw [realDensityMeasure_apply _ (tensorCutoffWeight f) hfi
    (tensorCutoffWeight_nonneg f hf0) (MeasurableSet.univ_pi hs)]
  have hi : (∫ x in Set.univ.pi s, tensorCutoffWeight f x ∂Measure.pi μ) =
      ∏ d, ∫ y in s d, f d y ∂μ d := by
    rw [Measure.restrict_pi_pi]
    exact integral_fintype_prod_eq_prod f
  rw [hi, ENNReal.ofReal_prod_of_nonneg (fun d _ => integral_nonneg (hf0 d))]
  apply Finset.prod_congr rfl
  intro d _
  exact (realDensityMeasure_apply (μ d) (f d) (hf d) (hf0 d) (hs d)).symm

theorem finiteMeasure_eq_of_integrals {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ f : X → ℝ, Measurable f → (∫ x, f x ∂μ) = ∫ x, f x ∂ν) : μ = ν := by
  ext s hs
  apply (measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have hi := h (s.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hs)
  simpa only [integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one] using hi

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem densityMixture_mappedTest {T Ω X : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure T) (ν : Measure Ω) (ξ : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [SFinite ξ]
    (U : T × Ω → X) (hU : Measurable U) (D : T → X → ℝ)
    (hD : Measurable (Function.uncurry D))
    (hprob : ∀ t, (∀ x, 0 ≤ D t x) ∧ Integrable (D t) ξ ∧ (∫ x, D t x ∂ξ) = 1)
    (hlaw : ∀ t, ν.map (fun a => U (t, a)) = realDensityMeasure ξ (D t))
    (φ : X → ℝ) (hφ : Measurable φ) {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    mappedTest (μ.prod ν) U φ = ∫ x, densityMixture μ D x*φ x ∂ξ := by
  have hi : Integrable (fun p => φ (U p)) (μ.prod ν) :=
    (integrable_const C).mono' (hφ.comp hU).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hbound (U p)))
  change (∫ p, φ (U p) ∂μ.prod ν) = _
  rw [integral_prod _ hi, densityMixture_test_integral μ ξ D
    (densityMixture_joint_integrable μ ξ D hD (Filter.Eventually.of_forall hprob)) φ hφ hbound]
  apply integral_congr_ae
  filter_upwards [] with t
  exact mappedTest_eq_density ν ξ (fun a => U (t, a))
    (hU.comp (measurable_const.prodMk measurable_id)) (D t)
    (hD.comp (measurable_const.prodMk measurable_id)) (hprob t).1 (hlaw t) φ hφ

theorem densityMixture_image_law {T Ω X : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure T) (ν : Measure Ω) (ξ : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [SFinite ξ]
    (U : T × Ω → X) (hU : Measurable U) (D : T → X → ℝ)
    (hD : Measurable (Function.uncurry D))
    (hprob : ∀ t, (∀ x, 0 ≤ D t x) ∧ Integrable (D t) ξ ∧ (∫ x, D t x ∂ξ) = 1)
    (hlaw : ∀ t, ν.map (fun a => U (t, a)) = realDensityMeasure ξ (D t)) :
    (μ.prod ν).map U = realDensityMeasure ξ (densityMixture μ D) := by
  have hp := densityMixture_probability_density μ ξ D hD (Filter.Eventually.of_forall hprob)
  have hm : Measurable (densityMixture μ D) :=
    hD.stronglyMeasurable.integral_prod_left'.measurable
  let : IsProbabilityMeasure ((μ.prod ν).map U) := Measure.isProbabilityMeasure_map hU.aemeasurable
  let : IsFiniteMeasure (realDensityMeasure ξ (densityMixture μ D)) :=
    realDensityMeasure_finite ξ _ hp.2.1 hp.1
  ext s hs
  apply (measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have hb : ∀ x, ‖s.indicator (fun _ => (1 : ℝ)) x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ s <;> simp [hx]
  have ht := densityMixture_mappedTest μ ν ξ U hU D hD hprob hlaw
    (s.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hs) hb
  have himage : mappedTest (μ.prod ν) U (s.indicator (fun _ => (1 : ℝ))) =
      ∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂(μ.prod ν).map U :=
    (integral_map hU.aemeasurable (measurable_const.indicator hs).aestronglyMeasurable).symm
  rw [himage, ← realDensityMeasure_integral ξ _ hm hp.1] at ht
  simpa only [integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one] using ht

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem pmf_real_integrable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : PMF X) : Integrable (fun x => (p x).toReal) Measure.count := by
  apply integrable_count_iff.mpr
  simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using
    ENNReal.summable_toReal p.tsum_coe_ne_top

theorem pmf_realDensity_count {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : PMF X) : p.toMeasure = realDensityMeasure Measure.count (fun x => (p x).toReal) := by
  ext s hs
  rw [p.toMeasure_apply hs, realDensityMeasure, withDensity_apply _ hs]
  simp_rw [ENNReal.ofReal_toReal (p.apply_ne_top _)]
  rw [← lintegral_indicator (μ := Measure.count) hs p, lintegral_count]

theorem independentIntegerLaw_density {J : Type*} [Fintype J] (p : J → PMF ℤ) :
    Measure.pi (fun j => (p j).toMeasure) =
      realDensityMeasure (Measure.pi (fun _ : J => (Measure.count : Measure ℤ)))
        (fun z => ∏ j, (p j (z j)).toReal) := by
  simp_rw [pmf_realDensity_count]
  exact realDensityMeasure_pi (fun _ => Measure.count) (fun j z => (p j z).toReal)
    (fun j => pmf_real_integrable (p j)) (fun _ _ => ENNReal.toReal_nonneg)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Function Set

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem realDensityMeasure_map_embedding (e : X → Y) (he : MeasurableEmbedding e)
    (μ : Measure X) (f : X → ℝ) :
    Measure.map e (realDensityMeasure μ f) =
      realDensityMeasure (Measure.map e μ) (Function.extend e f (fun _ => 0)) := by
  ext S hS
  rw [Measure.map_apply he.measurable hS, realDensityMeasure, realDensityMeasure,
    withDensity_apply _ (hS.preimage he.measurable), withDensity_apply _ hS,
    he.restrict_map, he.lintegral_map]
  simp only [he.injective.extend_apply]

theorem realDensityMeasure_restrict_support (ν : Measure Y) (f : Y → ℝ)
    {S : Set Y} (hS : MeasurableSet S) (hf : ∀ y ∉ S, f y = 0) :
    realDensityMeasure (ν.restrict S) f = realDensityMeasure ν f := by
  unfold realDensityMeasure
  rw [← withDensity_indicator hS]
  congr 1
  ext y
  by_cases hy : y ∈ S
  · simp only [Set.indicator_of_mem hy]
  · simp only [Set.indicator_of_notMem hy, hf y hy, ENNReal.ofReal_zero]

theorem realDensityMeasure_smul_real (ν : Measure Y) (f : Y → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    realDensityMeasure (ENNReal.ofReal c • ν) f = realDensityMeasure ν (fun y => c * f y) := by
  unfold realDensityMeasure
  rw [withDensity_smul_measure]
  have he : (fun y => ENNReal.ofReal (c * f y)) =
      ENNReal.ofReal c • (fun y => ENNReal.ofReal (f y)) := by
    funext y
    exact ENNReal.ofReal_mul hc
  rw [he, withDensity_smul' _ _ ENNReal.ofReal_ne_top]

noncomputable def embeddingDensity (e : X → Y) (c : ℝ) (f : X → ℝ) (y : Y) : ℝ :=
  c * Function.extend e f (fun _ => 0) y

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem embeddingDensity_apply (e : X → Y) (he : Function.Injective e)
    (c : ℝ) (f : X → ℝ) (x : X) : embeddingDensity e c f (e x) = c * f x := by
  simp only [embeddingDensity, he.extend_apply]

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem embeddingDensity_zero (e : X → Y) (c : ℝ) (f : X → ℝ) (y : Y)
    (hy : y ∉ Set.range e) : embeddingDensity e c f y = 0 := by
  simp only [embeddingDensity, Function.extend_apply' f (fun _ => 0) y hy, mul_zero]

theorem embeddingDensity_measurable (e : X → Y) (he : MeasurableEmbedding e)
    (c : ℝ) (f : X → ℝ) (hf : Measurable f) : Measurable (embeddingDensity e c f) :=
  measurable_const.mul (he.measurable_extend hf measurable_const)

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem embeddingDensity_nonneg (e : X → Y) (he : Function.Injective e)
    {c : ℝ} (hc : 0 ≤ c) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) (y : Y) :
    0 ≤ embeddingDensity e c f y := by
  by_cases hy : y ∈ Set.range e
  · obtain ⟨x, rfl⟩ := hy
    rw [embeddingDensity_apply e he]
    exact mul_nonneg hc (hf x)
  · rw [embeddingDensity_zero e c f y hy]

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem embeddingDensity_bound (e : X → Y) (he : Function.Injective e)
    {c B : ℝ} (hB : 0 ≤ B) (f : X → ℝ) (hf : ∀ x, c * f x ≤ B) (y : Y) :
    embeddingDensity e c f y ≤ B := by
  by_cases hy : y ∈ Set.range e
  · obtain ⟨x, rfl⟩ := hy
    rw [embeddingDensity_apply e he]
    exact hf x
  · rw [embeddingDensity_zero e c f y hy]
    exact hB

theorem embeddingDensity_law (e : X → Y) (he : MeasurableEmbedding e)
    (μ : Measure X) (ν : Measure Y) {c : ℝ} (hc : 0 ≤ c)
    (hmap : Measure.map e μ = ENNReal.ofReal c • ν.restrict (Set.range e)) (f : X → ℝ) :
    Measure.map e (realDensityMeasure μ f) = realDensityMeasure ν (embeddingDensity e c f) := by
  rw [realDensityMeasure_map_embedding e he, hmap, realDensityMeasure_smul_real _ _ hc]
  apply realDensityMeasure_restrict_support ν _ he.measurableSet_range
  exact embeddingDensity_zero e c f

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem measurePreserving_realDensity_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (π : X → Y) (hπ : MeasurePreserving π μ ν)
    (f : Y → ℝ) (hf : Measurable f) (hfi : Integrable f ν) (hf0 : ∀ y, 0 ≤ f y) :
    (realDensityMeasure μ (fun x => f (π x))).map π = realDensityMeasure ν f := by
  have hi := hπ.integrable_comp_of_integrable hfi
  let _ := realDensityMeasure_finite μ (fun x => f (π x)) hi (fun x => hf0 _)
  let _ := realDensityMeasure_finite ν f hfi hf0
  apply finiteMeasure_eq_of_integrals
  intro φ hφ
  rw [integral_map hπ.measurable.aemeasurable hφ.aestronglyMeasurable,
    realDensityMeasure_integral μ (fun x => f (π x)) (hf.comp hπ.measurable)
      (fun x => hf0 _) (fun x => φ (π x)),
    realDensityMeasure_integral ν f hf hf0 φ]
  have he := integral_map (μ := μ) hπ.measurable.aemeasurable (hf.mul hφ).aestronglyMeasurable
  simpa only [hπ.map_eq, Pi.mul_apply] using he.symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem productDensity_pushforward {J : Type*} [Fintype J] {X Y : J → Type*}
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSpace (Y j)]
    (μ : ∀ j, Measure (X j)) (ν : ∀ j, Measure (Y j)) [∀ j, SigmaFinite (ν j)]
    (q : ∀ j, X j → Y j) (hq : ∀ j, Measurable (q j)) (f : ∀ j, Y j → ℝ)
    (hfi : ∀ j, Integrable (f j) (ν j)) (hf0 : ∀ j y, 0 ≤ f j y)
    (hlaw : ∀ j, Measure.map (q j) (μ j) = realDensityMeasure (ν j) (f j)) :
    Measure.map (fun x j => q j (x j)) (Measure.pi μ) =
      realDensityMeasure (Measure.pi ν) (tensorCutoffWeight f) := by
  have houtput : ∀ j, SigmaFinite (Measure.map (q j) (μ j)) := by
    intro j
    rw [hlaw j]
    let : IsFiniteMeasure (realDensityMeasure (ν j) (f j)) :=
      realDensityMeasure_finite (ν j) (f j) (hfi j) (hf0 j)
    exact IsFiniteMeasure.toSigmaFinite _
  rw [Measure.pi_map_pi (μ := μ) (f := q) (hμ := houtput) (fun j => (hq j).aemeasurable)]
  simp_rw [hlaw]
  exact realDensityMeasure_pi ν f hfi hf0

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteArrayMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem finiteArray_uncurry_measurePreserving {I J X : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace X] (μ : I → J → Measure X) [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (MeasurableEquiv.curry I J X).symm
      (Measure.pi (fun i => Measure.pi (μ i))) (Measure.pi (fun ij : I × J => μ ij.1 ij.2)) := by
  refine ⟨(MeasurableEquiv.curry I J X).symm.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (MeasurableEquiv.curry I J X).symm.measurable (MeasurableSet.univ_pi hs)]
  have he : (MeasurableEquiv.curry I J X).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
    ext x
    constructor
    · intro hx i _ j _
      exact hx (i, j) (Set.mem_univ _)
    · intro hx ij _
      exact hx ij.1 (Set.mem_univ _) ij.2 (Set.mem_univ _)
  rw [he, Measure.pi_pi]
  simp only [Measure.pi_pi, Fintype.prod_prod_type]

def finiteArrayTranspose (I J X : Type*) [MeasurableSpace X] : (I → J → X) ≃ᵐ (J → I → X) :=
  ((MeasurableEquiv.curry I J X).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : J × I => X) (Equiv.prodComm I J))).trans
      (MeasurableEquiv.curry J I X)

theorem finiteArrayTranspose_measurePreserving {I J X : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace X] (μ : I → J → Measure X) [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (finiteArrayTranspose I J X)
      (Measure.pi (fun i => Measure.pi (μ i))) (Measure.pi (fun j => Measure.pi (fun i => μ i j))) := by
  have h₁ := finiteArray_uncurry_measurePreserving μ
  have h₂ := measurePreserving_piCongrLeft (fun ji : J × I => μ ji.2 ji.1) (Equiv.prodComm I J)
  have h₃ := (finiteArray_uncurry_measurePreserving (fun j i => μ i j)).symm
    (MeasurableEquiv.curry J I X).symm
  exact h₃.comp (h₂.comp h₁)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RestrictedComplexChartDensityComparison
namespace OAI

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Set

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

noncomputable def restrictedChartDensity (q : X → Y) (S : Set X) (c : ℝ)
    (f : X → ℝ) : Y → ℝ :=
  embeddingDensity (fun x : S => q x.val) c (fun x => f x.val)

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem restrictedChartDensity_apply (q : X → Y) (S : Set X) (c : ℝ) (f : X → ℝ)
    (hinj : Set.InjOn q S) {x : X} (hx : x ∈ S) :
    restrictedChartDensity q S c f (q x) = c * f x :=
  embeddingDensity_apply _ (fun a b h => Subtype.ext (hinj a.property b.property h)) c _ ⟨x,hx⟩

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem restrictedChartDensity_zero (q : X → Y) (S : Set X) (c : ℝ) (f : X → ℝ)
    {y : Y} (hy : y ∉ q '' S) : restrictedChartDensity q S c f y = 0 := by
  apply embeddingDensity_zero
  rintro ⟨x, rfl⟩
  exact hy ⟨x.val, x.property, rfl⟩

theorem subtype_density_map (μ : Measure X) {S : Set X} (hS : MeasurableSet S)
    (f : X → ℝ) (hf : ∀ x ∉ S, f x = 0) :
    Measure.map ((↑) : S → X)
      (realDensityMeasure (Measure.comap ((↑) : S → X) μ) (fun x => f x.val)) =
      realDensityMeasure μ f := by
  have hmap : Measure.map ((↑) : S → X) (Measure.comap ((↑) : S → X) μ) =
      ENNReal.ofReal (1 : ℝ) • μ.restrict (Set.range ((↑) : S → X)) := by
    simpa only [ENNReal.ofReal_one, one_smul, Subtype.range_coe] using map_comap_subtype_coe hS μ
  have h := embeddingDensity_law ((↑) : S → X) (MeasurableEmbedding.subtype_coe hS)
    (Measure.comap ((↑) : S → X) μ) μ zero_le_one hmap (fun x => f x.val)
  have he : embeddingDensity ((↑) : S → X) 1 (fun x => f x.val) = f := by
    funext x
    by_cases hx : x ∈ S
    · have hi := embeddingDensity_apply ((↑) : S → X) Subtype.coe_injective 1 (fun x => f x.val) ⟨x,hx⟩
      simpa only [one_mul] using hi
    · rw [embeddingDensity_zero _ _ _ x (by simpa only [Subtype.range_coe] using hx), hf x hx]
  rwa [he] at h

theorem restrictedChartDensity_law (q : X → Y) (hq : Measurable q)
    {S : Set X} (hS : MeasurableSet S)
    (he : MeasurableEmbedding (fun x : S => q x.val))
    (μ : Measure X) (ν : Measure Y) {c : ℝ} (hc : 0 ≤ c)
    (hmap : Measure.map q (μ.restrict S) = ENNReal.ofReal c • ν.restrict (q '' S))
    (f : X → ℝ) (hf : ∀ x ∉ S, f x = 0) :
    Measure.map q (realDensityMeasure μ f) = realDensityMeasure ν (restrictedChartDensity q S c f) := by
  let μS := Measure.comap ((↑) : S → X) μ
  have hrange : Set.range (fun x : S => q x.val) = q '' S := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x,hx⟩, rfl⟩
  have hm : Measure.map (fun x : S => q x.val) μS =
      ENNReal.ofReal c • ν.restrict (Set.range (fun x : S => q x.val)) := by
    rw [hrange]
    change Measure.map (q ∘ ((↑) : S → X)) μS = _
    rw [← Measure.map_map hq measurable_subtype_coe]
    change Measure.map q (Measure.map ((↑) : S → X) (Measure.comap ((↑) : S → X) μ)) = _
    rw [map_comap_subtype_coe hS μ, hmap]
  rw [← subtype_density_map μ hS f hf, Measure.map_map hq measurable_subtype_coe]
  exact embeddingDensity_law _ he μS ν hc hm _

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Set

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Set

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X Y : Type*}

noncomputable def restrictedComplexChartDensity (q : X → Y) (S : Set X) (c : ℝ)
    (f : X → ℂ) : Y → ℂ :=
  fun y => (c : ℂ) * Function.extend (fun x : S => q x.val) (fun x => f x.val) (fun _ => 0) y

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end


