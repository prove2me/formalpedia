-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Points
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Points
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:40.90118+00:00
-- url     : https://prove2.me/theorems/9a1adb3e-a542-41c0-a769-ba5b799e0481
-- title:
--   Points
-- statement:
--   Definitions and structural lemmas for Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Points.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
abbrev Coord (n : ι → ℕ) : Type := Σ k : ι, Fin (n k + 1)
def coordDeg (n : ι → ℕ) : Coord n → (ι → ℕ) := fun v ↦ Pi.single v.1 1
abbrev Cone (n : ι → ℕ) (F : Type*) : Type _ := (k : ι) → Fin (n k + 1) → F
variable {n : ι → ℕ}
def evalCone {F : Type*} [CommRing F] (z : Cone n F) (f : MvPolynomial (Coord n) ℤ) : F :=
  eval₂ (Int.castRingHom F) (fun v : Coord n ↦ z v.1 v.2) f
def BlockNonzero {F : Type*} [Zero F] (z : Cone n F) : Prop := ∀ k, z k ≠ 0
variable (n) in

structure ArithVariety where

  ideal : Ideal (MvPolynomial (Coord n) ℤ)
  isPrime : ideal.IsPrime

  homogeneous : ∀ f ∈ ideal, ∀ m : ι → ℕ, weightedHomogeneousComponent (coordDeg n) m f ∈ ideal

  relevant : ∀ k, ∃ i, (X ⟨k, i⟩ : MvPolynomial (Coord n) ℤ) ∉ ideal

  horizontal : ∀ a : ℤ, (C a : MvPolynomial (Coord n) ℤ) ∈ ideal → a = 0
namespace ArithVariety
def points (P : ArithVariety n) (F : Type*) [CommRing F] : Set (Cone n F) :=
  {z | BlockNonzero z ∧ ∀ f ∈ P.ideal, evalCone z f = 0}
def ZariskiDense (P : ArithVariety n) (S : Set (Cone n (AlgebraicClosure ℚ))) : Prop :=
  ∀ (m : ι → ℕ) (f : MvPolynomial (Coord n) ℤ), IsWeightedHomogeneous (coordDeg n) f m →
    (∀ z ∈ S, evalCone z f = 0) → f ∈ P.ideal
variable (n) in

def whole : ArithVariety n where
  ideal := ⊥
  isPrime := Ideal.isPrime_bot
  homogeneous f hf m := by
    rw [Submodule.mem_bot] at hf ⊢
    rw [hf, map_zero]
  relevant k := ⟨0, by rw [Submodule.mem_bot]; exact X_ne_zero _⟩
  horizontal a ha := by
    rw [Submodule.mem_bot] at ha
    exact C_eq_zero.mp ha
end ArithVariety
variable (n) in

structure HermLine where

  deg : ι → ℤ

  metric : Cone n ℂ → ℝ
  metric_pos : ∀ z : Cone n ℂ, BlockNonzero z → 0 < metric z
  metric_smul : ∀ (c : ι → ℂ) (z : Cone n ℂ), (∀ k, c k ≠ 0) → BlockNonzero z →
    metric (fun k i ↦ c k * z k i) = (∏ k, ‖c k‖ ^ deg k) * metric z
  metric_smooth : ContDiffOn ℝ ∞ metric {z | BlockNonzero z}
def l2Norm {m : ℕ} (w : Fin m → ℂ) : ℝ := Real.sqrt (∑ i, ‖w i‖ ^ 2)
theorem norm_le_l2Norm {m : ℕ} (w : Fin m → ℂ) (i : Fin m) : ‖w i‖ ≤ l2Norm w :=
  Real.le_sqrt_of_sq_le (Finset.single_le_sum (f := fun j ↦ ‖w j‖ ^ 2)
    (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ i))
theorem vectorL2Norm_pos {m : ℕ} {w : Fin m → ℂ} (hw : w ≠ 0) : 0 < l2Norm w := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  exact lt_of_lt_of_le (norm_pos_iff.mpr hi) (norm_le_l2Norm w i)
theorem vectorL2Norm_const_mul {m : ℕ} (c : ℂ) (w : Fin m → ℂ) :
    l2Norm (fun i ↦ c * w i) = ‖c‖ * l2Norm w := by
  simp only [l2Norm, norm_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
omit [DecidableEq ι] in
theorem contDiffOn_l2Norm_block (k : ι) :
    ContDiffOn ℝ ∞ (fun z : Cone n ℂ ↦ l2Norm (z k)) {z | BlockNonzero z} := by
  have hsum : ContDiff ℝ ∞ (fun z : Cone n ℂ ↦ ∑ i, ‖z k i‖ ^ 2) := by
    refine ContDiff.sum fun i _ ↦ ?_
    exact (contDiff_norm_sq ℝ).comp (contDiff_pi.1 (contDiff_pi.1 contDiff_id k) i)
  refine hsum.contDiffOn.sqrt fun z hz ↦ ?_
  have := vectorL2Norm_pos (hz k)
  exact ne_of_gt (Real.sqrt_pos.mp this)
namespace HermLine
variable (n) in

def standard : HermLine n where
  deg _ := 1
  metric z := ∏ k, l2Norm (z k)
  metric_pos z hz := Finset.prod_pos fun k _ ↦ vectorL2Norm_pos (hz k)
  metric_smul c z _ _ := by
    simp only [vectorL2Norm_const_mul, zpow_one, Finset.prod_mul_distrib]
  metric_smooth := contDiffOn_prod fun k _ ↦ contDiffOn_l2Norm_block k
def scale (A : HermLine n) (t : ℝ) (ht : 0 < t) : HermLine n where
  deg := A.deg
  metric z := t * A.metric z
  metric_pos z hz := mul_pos ht (A.metric_pos z hz)
  metric_smul c z hc hz := by
    rw [A.metric_smul c z hc hz]
    ring
  metric_smooth := contDiffOn_const.mul A.metric_smooth
def project {ι' : Type} {n' : ι' → ℕ} (j : ι → ι') {F : Type*} (z : Cone n' F) :
    Cone (n' ∘ j) F :=
  fun k ↦ z (j k)
omit [DecidableEq ι] in
theorem prod_extend_zpow {ι' : Type} [Fintype ι'] {j : ι → ι'} (hj : Function.Injective j)
    (a : ι → ℤ) (r : ι' → ℝ) :
    ∏ k', r k' ^ Function.extend j a 0 k' = ∏ k, r (j k) ^ a k := by
  classical
  symm
  refine Fintype.prod_of_injective j hj _ _ (fun k' hk' ↦ ?_) (fun k ↦ ?_)
  · rw [Function.extend_apply' _ _ _ (fun ⟨k, hk⟩ ↦ hk' ⟨k, hk⟩), Pi.zero_apply, zpow_zero]
  · rw [hj.extend_apply]
def pullback {ι' : Type} [Fintype ι'] {n' : ι' → ℕ} (j : ι → ι') (hj : Function.Injective j)
    (A : HermLine (n' ∘ j)) : HermLine n' where
  deg := Function.extend j A.deg 0
  metric z := A.metric (project j z)
  metric_pos z hz := A.metric_pos _ fun k ↦ hz (j k)
  metric_smul c z hc hz := by
    have h := A.metric_smul (fun k ↦ c (j k)) (project j z) (fun k ↦ hc (j k)) (fun k ↦ hz (j k))
    rw [prod_extend_zpow hj A.deg (fun k' ↦ ‖c k'‖)]
    exact h
  metric_smooth := by
    have hp : ContDiff ℝ ∞ (fun z : Cone n' ℂ ↦ project j z) :=
      contDiff_pi.2 fun k ↦ contDiff_pi.1 contDiff_id (j k)
    exact A.metric_smooth.comp hp.contDiffOn fun z hz k ↦ hz (j k)
end HermLine
def coordField (z : Cone n (AlgebraicClosure ℚ)) : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.adjoin ℚ (Set.range fun v : Coord n ↦ z v.1 v.2)
theorem isIntegral_algebraicClosure_rat (x : AlgebraicClosure ℚ) : IsIntegral ℚ x := by
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ <;> rfl
  exact (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
instance (z : Cone n (AlgebraicClosure ℚ)) : FiniteDimensional ℚ (coordField z) :=
  IntermediateField.finiteDimensional_adjoin fun x _ ↦ isIntegral_algebraicClosure_rat x
instance (z : Cone n (AlgebraicClosure ℚ)) : NumberField (coordField z) := {}
def coordVec (z : Cone n (AlgebraicClosure ℚ)) : Cone n (coordField z) :=
  fun k i ↦ ⟨z k i, IntermediateField.subset_adjoin ℚ _ ⟨⟨k, i⟩, rfl⟩⟩
def height (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) : ℝ :=
  ((Module.finrank ℚ (coordField x) : ℝ))⁻¹ *
    ((∑ᶠ v : FinitePlace (coordField x),
        ∑ k, (A.deg k : ℝ) * Real.log (⨆ i, v (coordVec x k i))) +
      ∑ σ : coordField x →+* ℂ, Real.log (A.metric fun k i ↦ σ (coordVec x k i)))
def coordIn (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (z : Cone n (AlgebraicClosure ℚ))
    (hz : ∀ k i, z k i ∈ L) : Cone n L :=
  fun k i ↦ ⟨z k i, hz k i⟩
def finiteTerm {L : Type*} [Field L] [NumberField L] (A : HermLine n) (v : FinitePlace L)
    (y : Cone n L) : ℝ :=
  ∑ k, (A.deg k : ℝ) * Real.log (⨆ i, v (y k i))
def chartMonomial (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ) : MvPolynomial (Coord n) ℤ :=
  ∏ k, X ⟨k, c k⟩ ^ d k
def IsChartForm (P : ArithVariety n) (a : ι → ℤ) (num den : MvPolynomial (Coord n) ℤ)
    (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ) (e : MvPolynomial (Coord n) ℤ) : Prop :=
  (∃ δ : ι → ℕ, IsWeightedHomogeneous (coordDeg n) e δ ∧ ∀ k, (δ k : ℤ) = a k + d k) ∧
    den * e - num * chartMonomial c d ∈ P.ideal
structure IntegralSection (P : ArithVariety n) (a : ι → ℤ) where

  num : MvPolynomial (Coord n) ℤ

  den : MvPolynomial (Coord n) ℤ

  numDeg : ι → ℕ

  denDeg : ι → ℕ
  num_isHomogeneous : IsWeightedHomogeneous (coordDeg n) num numDeg
  den_isHomogeneous : IsWeightedHomogeneous (coordDeg n) den denDeg
  deg_eq : ∀ k, (numDeg k : ℤ) - denDeg k = a k
  den_not_mem : den ∉ P.ideal
  regular : ∀ c : (k : ι) → Fin (n k + 1), (∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal) →
    ∃ (d : ι → ℕ) (e : MvPolynomial (Coord n) ℤ), IsChartForm P a num den c d e
theorem isWeightedHomogeneous_chartMonomial (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ) :
    IsWeightedHomogeneous (coordDeg n) (chartMonomial c d) d := by
  have h := IsWeightedHomogeneous.prod Finset.univ
    (fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ^ d k) (fun k ↦ d k • Pi.single k 1)
    (fun k _ ↦ (isWeightedHomogeneous_X (R := ℤ) (coordDeg n) ⟨k, c k⟩).pow (d k))
  have e : (∑ k, d k • Pi.single k 1 : ι → ℕ) = d := by
    ext k'
    rw [Finset.sum_apply]
    simp [Pi.single_apply]
  rw [e] at h
  exact h
namespace IntegralSection
variable {P : ArithVariety n} {a : ι → ℤ}
variable (P) in

def chartSection (c : (k : ι) → Fin (n k + 1)) : IntegralSection P (fun _ ↦ 1) where
  num := chartMonomial c 1
  den := 1
  numDeg := 1
  denDeg := 0
  num_isHomogeneous := isWeightedHomogeneous_chartMonomial c 1
  den_isHomogeneous := isWeightedHomogeneous_one ℤ (coordDeg n)
  deg_eq k := by simp
  den_not_mem := (Ideal.ne_top_iff_one _).mp P.isPrime.ne_top
  regular _ _ := ⟨0, chartMonomial c 1,
    ⟨⟨1, isWeightedHomogeneous_chartMonomial c 1, fun k ↦ by simp⟩, by simp [chartMonomial]⟩⟩
def NonzeroAt (s : IntegralSection P a) (x : Cone n (AlgebraicClosure ℚ)) : Prop :=
  ∃ (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ) (e : MvPolynomial (Coord n) ℤ),
    IsChartForm P a s.num s.den c d e ∧ (∀ k, x k (c k) ≠ 0) ∧ evalCone x e ≠ 0
def SupNormLE (A : HermLine n) (s : IntegralSection P A.deg) (C : ℝ) : Prop :=
  ∀ z ∈ P.points ℂ, ∀ (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ) (e : MvPolynomial (Coord n) ℤ),
    IsChartForm P A.deg s.num s.den c d e → (∀ k, z k (c k) ≠ 0) →
    ‖evalCone z e‖ / (‖evalCone z (chartMonomial c d)‖ * A.metric z) ≤ Real.exp C
end IntegralSection
end
end GroundTheory.Heights₂.Heights


