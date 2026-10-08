-- Prove2me | Definitions.Def_OAIErdos3B000
-- name    : OAIErdos3B000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T07:11:35.503987+00:00
-- url     : https://prove2.me/theorems/c1505bbd-5cdb-44a2-940f-4aa27df38b91
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1 of 132
-- statement:
--   Definitions bundle 1 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It is the first bundle of the chain; it imports `ErdosReciprocal` (the definitions of the target statement).
--
--   Modules: `Estimates.FourBalancedRelations`, `Polynomial.RealPolynomialEvaluationMass`, `Estimates.LinearCoefficientMap`, `Estimates.ScalarExtensionSubstitution`, `Polynomial.VectorPolynomialReconstruction`, `Polynomial.MixedWeightedPolynomialRename`, `Geometry.WeightedSubstitutionSupport`, `Estimates.FormalExpLog`, `Estimates.RationalHeight`, `Estimates.TruncatedSeries`, `Estimates.TensorContraction`, `Estimates.DynkinTrees`, `Linear.DynkinProjection`, `Estimates.FreePrimitiveCriterion`, `Linear.LieWordProjection`, `Estimates.FreeLieTreeCoefficientBounds`, `Nilpotent.NilpotentBilinearExponential`, `Nilpotent.LieBCHContinuity`, `Estimates.UniformProductAccuracy`, `Model`, `Results.Basic`, `Estimates.ComplexFiniteMeans`, `Sampling.FrozenPartitionScore`, `Estimates.ProgressionPartitionComposition`, `Probability.ComplexPartitionMixture`, `Geometry.BoxBlockBudget`, `Fourier.RationalLiftCharacterTwist`, `Estimates.DependentPatchValue`, `Lattices.AffineLowestLayer`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Model
namespace OAI

namespace Erdos3

def APFree (A : Set ℕ) (k : ℕ) : Prop := ¬ HasAP A k

noncomputable def extremalNumber (k N : ℕ) : ℕ := by
  classical
  exact (((Finset.Icc 1 N).powerset).filter fun S : Finset ℕ ↦ APFree (S : Set ℕ) k).sup
    Finset.card

end Erdos3

open scoped BigOperators

namespace Erdos3

end Erdos3

namespace Erdos3

def QuantitativeDensityBound (k : ℕ) : Prop :=
  ∃ C c η : ℝ, 0 < C ∧ 0 < c ∧ 0 < η ∧
    ∀ N : ℕ, 3 ≤ N →
      (extremalNumber k N : ℝ) ≤
        C * N * Real.exp (-c * (Real.log (Real.log N)) ^ (1 + η))

def QuantitativeDensityTheorem : Prop :=
  ∀ k : ℕ, 3 ≤ k → QuantitativeDensityBound k

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Results.Basic
namespace OAI

section

namespace Erdos3

theorem HasAP.mono {A B : Set ℕ} {k : ℕ} (h : HasAP A k) (hAB : A ⊆ B) :
    HasAP B k := by
  obtain ⟨a, d, hd, h⟩ := h
  exact ⟨a, d, hd, fun i hi ↦ hAB (h i hi)⟩

theorem APFree.mono {A B : Set ℕ} {k : ℕ} (h : APFree B k) (hAB : A ⊆ B) :
    APFree A k := fun hA ↦ h (hA.mono hAB)

theorem HasAP.affine_image {A : Set ℕ} {k : ℕ} (h : HasAP A k)
    (u v : ℕ) (hv : 0 < v) : HasAP ((fun n ↦ u + v * n) '' A) k := by
  obtain ⟨a, d, hd, h⟩ := h
  refine ⟨u + v * a, v * d, Nat.mul_pos hv hd, fun i hi ↦ ?_⟩
  exact ⟨a + i * d, h i hi, by ring⟩

theorem APFree.affine_preimage {A : Set ℕ} {k : ℕ} (h : APFree A k)
    (u v : ℕ) (hv : 0 < v) : APFree ((fun n ↦ u + v * n) ⁻¹' A) k := by
  intro hpre
  exact h ((hpre.affine_image u v hv).mono (Set.image_preimage_subset _ _))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexFiniteMeans
namespace OAI

section

open scoped BigOperators

namespace Erdos3

theorem expect_fin_cons {G M : Type*} [Fintype G] [AddCommMonoid M] [Module ℚ≥0 M]
    {n : ℕ} (F : (Fin (n + 1) → G) → M) :
    (𝔼 x, F x) = 𝔼 a : G, 𝔼 y : Fin n → G, F (Fin.cons a y) := by
  calc
    (𝔼 x, F x) = 𝔼 p : G × (Fin n → G), F (Fin.cons p.1 p.2) := by
      apply Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (n + 1) ↦ G)).symm
      intro x
      congr 1
      simp
    _ = _ := by
      simpa using (Finset.expect_product' (Finset.univ : Finset G)
        (Finset.univ : Finset (Fin n → G)) (fun a y ↦ F (Fin.cons a y)))

theorem norm_expect_mul_star_sq_le {Ω : Type*} [Fintype Ω] (f g : Ω → ℂ) :
    ‖𝔼 x, f x * star (g x)‖ ^ 2 ≤
      (𝔼 x, ‖f x‖ ^ 2) * (𝔼 x, ‖g x‖ ^ 2) := by
  have hnorm : ‖𝔼 x, f x * star (g x)‖ ≤ 𝔼 x, ‖f x‖ * ‖g x‖ := by
    simpa only [norm_mul, norm_star] using
      (RCLike.norm_expect_le (K := ℂ) (f := fun x ↦ f x * star (g x)))
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
    (Finset.expect_mul_sq_le_sq_mul_sq Finset.univ (fun x ↦ ‖f x‖) (fun x ↦ ‖g x‖))

theorem expect_square_le {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    (𝔼 x, f x) ^ 2 ≤ 𝔼 x, f x ^ 2 := by
  have h := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ f (fun _ : Ω ↦ (1 : ℝ))
  simpa using h

theorem prod_bool_tuple_succ {M : Type*} [CommMonoid M] {n : ℕ}
    (F : (Fin (n + 1) → Bool) → M) :
    (∏ ω, F ω) =
      (∏ ω : Fin n → Bool, F (Fin.cons false ω)) *
        (∏ ω : Fin n → Bool, F (Fin.cons true ω)) := by
  calc
    (∏ ω, F ω) = ∏ q : Bool × (Fin n → Bool), F (Fin.cons q.1 q.2) := by
      apply Fintype.prod_equiv (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Bool)).symm
      intro ω
      simp
    _ = _ := by rw [Fintype.prod_prod_type]; simp [mul_comm]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def orderedProductTail {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∏ j, if i < j then x j else 1

noncomputable def axisProduct {G : Type*} [Add G] {n : ℕ}
    (f : Fin n → G → ℝ) (t : Fin n → G) (y : G) : ℝ := ∏ i, f i (y + t i)

noncomputable def axisSuffix {G : Type*} [Add G] {n : ℕ}
    (f : Fin n → G → ℝ) (t : Fin n → G) (i : Fin n) (y : G) : ℝ :=
  orderedProductTail (fun j => f j (y + t j)) i

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

noncomputable def realShiftCorrelation (a J : G → ℝ) (h : G) : ℝ :=
  𝔼 n, a n * J (n + h)

noncomputable def realBilinearAverage (a H W : G → ℝ) : ℝ :=
  𝔼 x, 𝔼 y, H x * W y * a (x + y)

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

theorem expect_prod_boolean_pow_le {Ω : Type*} [Fintype Ω]
    (n : ℕ) (F : (Fin n → Bool) → Ω → ℝ) (hF : ∀ ω x, 0 ≤ F ω x) :
    (𝔼 x, ∏ ω, F ω x) ^ (2 ^ n) ≤ ∏ ω, 𝔼 x, F ω x ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    let A (b : Bool) (x : Ω) := ∏ ω : Fin n → Bool, F (Fin.cons b ω) x
    have hprod (x : Ω) : (∏ ω, F ω x) = A false x * A true x :=
      prod_bool_tuple_succ _
    have hcs := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ (A false) (A true)
    have hpart (b : Bool) : (𝔼 x, A b x ^ 2) ^ (2 ^ n) ≤
        ∏ ω : Fin n → Bool, 𝔼 x, F (Fin.cons b ω) x ^ (2 ^ (n + 1)) := by
      have h := ih (fun ω x ↦ F (Fin.cons b ω) x ^ 2) (fun _ _ ↦ sq_nonneg _)
      simpa only [A, ← Finset.prod_pow, ← pow_mul, ← pow_succ'] using h
    calc
      (𝔼 x, ∏ ω, F ω x) ^ (2 ^ (n + 1)) =
          ((𝔼 x, A false x * A true x) ^ 2) ^ (2 ^ n) := by
        simp_rw [hprod]
        rw [← pow_mul, pow_succ']
      _ ≤ ((𝔼 x, A false x ^ 2) * (𝔼 x, A true x ^ 2)) ^ (2 ^ n) :=
        pow_le_pow_left₀ (sq_nonneg _) hcs _
      _ = (𝔼 x, A false x ^ 2) ^ (2 ^ n) * (𝔼 x, A true x ^ 2) ^ (2 ^ n) :=
        mul_pow _ _ _
      _ ≤ (∏ ω : Fin n → Bool, 𝔼 x, F (Fin.cons false ω) x ^ (2 ^ (n + 1))) *
          (∏ ω : Fin n → Bool, 𝔼 x, F (Fin.cons true ω) x ^ (2 ^ (n + 1))) := by
        apply mul_le_mul (hpart false) (hpart true)
        · exact pow_nonneg (Finset.expect_nonneg (fun _ _ ↦ sq_nonneg _)) _
        · exact Finset.prod_nonneg (fun ω _ ↦ Finset.expect_nonneg
            (fun x _ ↦ pow_nonneg (hF _ x) _))
      _ = ∏ ω, 𝔼 x, F ω x ^ (2 ^ (n + 1)) :=
        (prod_bool_tuple_succ (fun ω ↦ 𝔼 x, F ω x ^ (2 ^ (n + 1)))).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*}

noncomputable def cellAverage [Add G] (C : Finset G) (f : G → ℝ) (x : G) : ℝ :=
  𝔼 c ∈ C, f (x + c)

variable [Fintype G] [DecidableEq G]

variable [AddCommGroup G]

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

theorem exists_common_slice_of_equal_marginals {A B H : Type*}
    [Fintype A] [Fintype B] [Fintype H] [Nonempty A] [Nonempty B] [Nonempty H]
    (f : A → H → ℝ) (g : B → H → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hmarginal : ∀ h, (𝔼 a, f a h) = 𝔼 b, g b h)
    (hmean : δ ≤ 𝔼 h, 𝔼 a, f a h) :
    ∃ (a : A) (b : B), δ ^ 2 ≤ 𝔼 h, f a h * g b h := by
  have henergy := (pow_le_pow_left₀ hδ hmean 2).trans
    (expect_square_le (fun h => 𝔼 a, f a h))
  have hproduct : (𝔼 h, (𝔼 a, f a h) ^ 2) = 𝔼 a, 𝔼 b, 𝔼 h, f a h * g b h := by
    calc
      _ = 𝔼 h, (𝔼 a, f a h) * (𝔼 b, g b h) := by
        apply Finset.expect_congr rfl
        intro h _
        rw [← hmarginal h, pow_two]
      _ = 𝔼 h, 𝔼 a, 𝔼 b, f a h * g b h := by simp_rw [Fintype.expect_mul_expect]
      _ = 𝔼 a, 𝔼 h, 𝔼 b, f a h * g b h := Finset.expect_comm _ _ _
      _ = _ := by
        apply Finset.expect_congr rfl
        intro a _
        exact Finset.expect_comm _ _ _
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty (henergy.trans_eq hproduct)
  obtain ⟨b, _, hb⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty ha
  exact ⟨a, b, hb⟩

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RationalLiftCharacterTwist
namespace OAI

section

namespace Erdos3

theorem real_fourierChar_norm_sub_le (a b : ℝ) :
    ‖(Real.fourierChar a : ℂ) - (Real.fourierChar b : ℂ)‖ ≤
      2 * Real.pi * |a - b| := by
  have hmul : (Real.fourierChar a : ℂ) =
      (Real.fourierChar (a - b) : ℂ) * (Real.fourierChar b : ℂ) := by
    rw [← Circle.coe_mul, ← Real.fourierChar.map_add_eq_mul, sub_add_cancel]
  calc
    ‖(Real.fourierChar a : ℂ) - (Real.fourierChar b : ℂ)‖ =
        ‖((Real.fourierChar (a - b) : ℂ) - 1) * (Real.fourierChar b : ℂ)‖ := by
      rw [sub_mul, one_mul, ← hmul]
    _ = ‖(Real.fourierChar (a - b) : ℂ) - 1‖ := by
      rw [norm_mul, Circle.norm_coe, mul_one]
    _ ≤ ‖2 * Real.pi * (a - b)‖ := by
      rw [Real.fourierChar_apply, mul_comm _ Complex.I]
      exact Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi * |a - b| := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {m : ℕ}

noncomputable def rationalLiftCharacterTwist (M : ℕ) (a : Fin m → ℤ) (c : Fin m → ℝ)
    (y : Fin m → ℝ) (r : Fin m → ZMod M) : ℂ :=
  Real.fourierChar ((∑ i, (a i : ℝ) * (y i + (r i).val + c i)) / (M : ℝ))

noncomputable def rationalLiftCharacterTwistLip (M : ℕ) (a : Fin m → ℤ) : ℝ≥0 :=
  ⟨2 * Real.pi * (∑ i, |(a i : ℝ)|) / (M : ℝ), by positivity⟩

theorem rationalLiftCharacterTwist_norm (M : ℕ) (a : Fin m → ℤ) (c y : Fin m → ℝ)
    (r : Fin m → ZMod M) : ‖rationalLiftCharacterTwist M a c y r‖ = 1 :=
  Circle.norm_coe _

theorem rationalLiftCharacterTwist_lipschitz (M : ℕ) (a : Fin m → ℤ) (c : Fin m → ℝ)
    (r : Fin m → ZMod M) :
    LipschitzWith (rationalLiftCharacterTwistLip M a) (fun y => rationalLiftCharacterTwist M a c y r) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  have hdiff : |(∑ i, (a i : ℝ) * (x i + (r i).val + c i)) / (M : ℝ) -
      (∑ i, (a i : ℝ) * (y i + (r i).val + c i)) / (M : ℝ)| ≤
      (∑ i, |(a i : ℝ)|) / (M : ℝ) * dist x y := by
    rw [← sub_div, ← Finset.sum_sub_distrib]
    have heq : (∑ i, ((a i : ℝ) * (x i + (r i).val + c i) -
        (a i : ℝ) * (y i + (r i).val + c i))) =
        ∑ i, (a i : ℝ) * (x i - y i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heq, abs_div, abs_of_nonneg (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
    calc
      _ ≤ (∑ i, |(a i : ℝ) * (x i - y i)|) / (M : ℝ) :=
        div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg M)
      _ ≤ (∑ i, |(a i : ℝ)| * dist x y) / (M : ℝ) := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg M)
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) (abs_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  change ‖(Real.fourierChar _ : ℂ) - (Real.fourierChar _ : ℂ)‖ ≤ _
  apply (real_fourierChar_norm_sub_le _ _).trans
  apply (mul_le_mul_of_nonneg_left hdiff (by positivity : 0 ≤ 2 * Real.pi)).trans_eq
  change 2 * Real.pi * ((∑ i, |(a i : ℝ)|) / (M : ℝ) * dist x y) =
    (2 * Real.pi * (∑ i, |(a i : ℝ)|) / (M : ℝ)) * dist x y
  ring

theorem rationalLiftCharacterTwistLip_le (M : ℕ) (hM : 0 < M) (a : Fin m → ℤ)
    (A : ℝ) (ha : ∀ i, |(a i : ℝ)| ≤ A) :
    (rationalLiftCharacterTwistLip M a : ℝ) ≤ 2 * Real.pi * m * A := by
  have hs : (∑ i, |(a i : ℝ)|) ≤ (m : ℝ) * A := by
    calc
      _ ≤ ∑ _i : Fin m, A := Finset.sum_le_sum (fun i _ => ha i)
      _ = _ := by simp
  change 2 * Real.pi * (∑ i, |(a i : ℝ)|) / (M : ℝ) ≤ _
  apply (div_le_self (by positivity)
    (show (1 : ℝ) ≤ M by exact_mod_cast Nat.succ_le_of_lt hM)).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs
    (by positivity : 0 ≤ 2 * Real.pi)

theorem rationalLiftCharacterTwist_residual (M : ℕ) (hM : 0 < M)
    (a : Fin m → ℤ) (c x : Fin m → ℝ) (β : Fin m → ℤ) :
    rationalLiftCharacterTwist M a c (fun i => x i - (β i : ℝ))
      (fun i => (β i : ZMod M)) =
        (Real.fourierChar ((∑ i, (a i : ℝ) * (x i + c i)) / (M : ℝ)) : ℂ) := by
  let : NeZero M := ⟨hM.ne'⟩
  have hzexists (i : Fin m) : ∃ z : ℤ,
      β i = ((β i : ZMod M).val : ℤ) + (M : ℤ) * z :=
    (ZMod.intCast_eq_iff M (β i) (β i : ZMod M)).mp rfl
  choose z hz using hzexists
  have hβ (i : Fin m) : (β i : ℝ) = ((β i : ZMod M).val : ℝ) + (M : ℝ) * (z i : ℝ) := by
    exact_mod_cast hz i
  have hMr : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hphase : (∑ i, (a i : ℝ) * (x i - (β i : ℝ) + (β i : ZMod M).val + c i)) / (M : ℝ) =
      (∑ i, (a i : ℝ) * (x i + c i)) / (M : ℝ) - ((∑ i, a i * z i : ℤ) : ℝ) := by
    calc
      _ = ∑ i, ((a i : ℝ) * (x i + c i) / (M : ℝ) - ((a i * z i : ℤ) : ℝ)) := by
        rw [div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [hβ i, Int.cast_mul]
        field_simp
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Int.cast_sum]
        simp only [div_eq_mul_inv, Finset.sum_mul]
  have hzchar : Real.fourierChar (((∑ i, a i * z i : ℤ) : ℝ)) = 1 := by
    apply Subtype.ext
    change (Circle.exp (2 * Real.pi * (((∑ i, a i * z i : ℤ) : ℝ))) : ℂ) = 1
    rw [mul_comm (2 * Real.pi), Circle.exp_intCast_mul]
    simp
  unfold rationalLiftCharacterTwist
  rw [hphase, Real.fourierChar.map_sub_eq_div, hzchar, div_one]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DependentPatchValue
namespace OAI

section

namespace Erdos3

open scoped NNReal

structure TriangularSlots (d : ℕ) where
  center : (Fin d → ℝ) → Fin d → ℝ
  lower : ∀ i x y, (∀ j, j < i → x j = y j) → center x i = center y i

namespace TriangularSlots

variable {d : ℕ}

def residual (A : TriangularSlots d) (b : Fin d → ℤ) : Fin d → ℝ :=
  fun i => (b i : ℝ) - A.center (fun j => (b j : ℝ)) i

theorem integer_unique (A : TriangularSlots d) {b c : Fin d → ℤ} {r t : ℝ}
    (hgap : r + t < 1)
    (hb : ∀ i, |A.residual b i| ≤ r) (hc : ∀ i, |A.residual c i| ≤ t) : b = c := by
  have hall : ∀ n : ℕ, ∀ i : Fin d, i.val = n → b i = c i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hi
      have hcenter : A.center (fun j => (b j : ℝ)) i = A.center (fun j => (c j : ℝ)) i := by
        apply A.lower
        intro j hj
        have hjn : j.val < n := by simpa only [Fin.lt_def, ← hi] using hj
        rw [ih j.val hjn j rfl]
      have heq : ((b i - c i : ℤ) : ℝ) = A.residual b i - A.residual c i := by
        simp only [residual, Int.cast_sub, hcenter]
        ring
      have habs : |((b i - c i : ℤ) : ℝ)| < 1 := by
        rw [heq]
        exact (abs_sub _ _).trans_lt ((add_le_add (hb i) (hc i)).trans_lt hgap)
      have hl : (-1 : ℤ) < b i - c i := by exact_mod_cast (abs_lt.mp habs).1
      have hr : b i - c i < (1 : ℤ) := by exact_mod_cast (abs_lt.mp habs).2
      omega
  exact funext (fun i => hall i.val i rfl)

end TriangularSlots

structure PatchKernel (d : ℕ) where
  value : (Fin d → ℝ) → ℝ
  nonneg : ∀ x, 0 ≤ value x
  le_one : ∀ x, value x ≤ 1
  support : ∀ x, value x ≠ 0 → ∀ i, |x i| ≤ 1 / 4
  lip : ℝ≥0
  lipschitz : LipschitzWith lip value

namespace TriangularSlots

variable {d : ℕ} (A : TriangularSlots d) (Φ : PatchKernel d)

theorem contributing_unique {b c : Fin d → ℤ}
    (hb : Φ.value (A.residual b) ≠ 0) (hc : Φ.value (A.residual c) ≠ 0) : b = c :=
  A.integer_unique (by norm_num) (Φ.support _ hb) (Φ.support _ hc)

noncomputable def patchValue : ℝ := ∑' b : Fin d → ℤ, Φ.value (A.residual b)

theorem patchValue_eq_of_nonzero {b : Fin d → ℤ} (hb : Φ.value (A.residual b) ≠ 0) :
    A.patchValue Φ = Φ.value (A.residual b) := by
  apply tsum_eq_single b
  intro c hcb
  by_contra hc
  exact hcb (A.contributing_unique Φ hc hb)

theorem patchValue_eq_zero (h : ∀ b : Fin d → ℤ, Φ.value (A.residual b) = 0) :
    A.patchValue Φ = 0 := by
  simp only [patchValue, h, tsum_zero]

theorem patchValue_eq_at_residual {b : Fin d → ℤ}
    (hb : ∀ i, |A.residual b i| ≤ 1 / 4) :
    A.patchValue Φ = Φ.value (A.residual b) := by
  apply tsum_eq_single b
  intro c hcb
  by_contra hc
  exact hcb (A.integer_unique (by norm_num) (Φ.support _ hc) hb)

theorem patchValue_mem_Icc : A.patchValue Φ ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases h : ∃ b : Fin d → ℤ, Φ.value (A.residual b) ≠ 0
  · obtain ⟨b, hb⟩ := h
    rw [A.patchValue_eq_of_nonzero Φ hb]
    exact ⟨Φ.nonneg _, Φ.le_one _⟩
  · have hz : ∀ b : Fin d → ℤ, Φ.value (A.residual b) = 0 := by simpa using h
    rw [A.patchValue_eq_zero Φ hz]
    exact ⟨le_rfl, zero_le_one⟩

end TriangularSlots

end Erdos3

end

section

namespace Erdos3.TriangularSlots

variable {d : ℕ}

theorem patchValue_dist_of_residuals_close (A B : TriangularSlots d) (Φ : PatchKernel d)
    {ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε < 1 / 4)
    (hclose : ∀ b, Φ.value (A.residual b) ≠ 0 ∨ Φ.value (B.residual b) ≠ 0 →
      dist (A.residual b) (B.residual b) ≤ ε) :
    dist (A.patchValue Φ) (B.patchValue Φ) ≤ Φ.lip * ε := by
  have hbound (b) (hb : Φ.value (A.residual b) ≠ 0 ∨ Φ.value (B.residual b) ≠ 0) :
      ∀ i, |A.residual b i| ≤ 1 / 4 + ε := by
    intro i
    rcases hb with hb | hb
    · exact (Φ.support _ hb i).trans (by linarith)
    · have hd := (dist_le_pi_dist (A.residual b) (B.residual b) i).trans
        (hclose b (Or.inr hb))
      rw [Real.dist_eq] at hd
      have htriangle : |A.residual b i| ≤
          |A.residual b i - B.residual b i| + |B.residual b i| := by
        simpa only [sub_add_cancel] using
          abs_add_le (A.residual b i - B.residual b i) (B.residual b i)
      linarith [Φ.support _ hb i]
  by_cases h : ∃ b, Φ.value (A.residual b) ≠ 0 ∨ Φ.value (B.residual b) ≠ 0
  · obtain ⟨b, hb⟩ := h
    have hunique (c) (hc : Φ.value (A.residual c) ≠ 0 ∨ Φ.value (B.residual c) ≠ 0) : c = b :=
      A.integer_unique (by linarith : (1 / 4 + ε) + (1 / 4 + ε) < 1) (hbound c hc) (hbound b hb)
    have hA : A.patchValue Φ = Φ.value (A.residual b) := by
      apply tsum_eq_single b
      intro c hcb
      by_contra hc
      exact hcb (hunique c (Or.inl hc))
    have hB : B.patchValue Φ = Φ.value (B.residual b) := by
      apply tsum_eq_single b
      intro c hcb
      by_contra hc
      exact hcb (hunique c (Or.inr hc))
    rw [hA, hB]
    exact (Φ.lipschitz.dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left (hclose b hb) Φ.lip.coe_nonneg)
  · have hA (b) : Φ.value (A.residual b) = 0 := by
      by_contra hb
      exact h ⟨b, Or.inl hb⟩
    have hB (b) : Φ.value (B.residual b) = 0 := by
      by_contra hb
      exact h ⟨b, Or.inr hb⟩
    rw [A.patchValue_eq_zero Φ hA, B.patchValue_eq_zero Φ hB, dist_self]
    exact mul_nonneg Φ.lip.coe_nonneg hε

end Erdos3.TriangularSlots

end

section

namespace Erdos3

variable {D E : ℕ}

def slotPrefix {R : Type*} (x : Fin (D + E) → R) : Fin D → R :=
  fun i => x (i.castAdd E)

def slotSuffix {R : Type*} (x : Fin (D + E) → R) : Fin E → R :=
  fun i => x (i.natAdd D)

@[simp] theorem slotPrefix_append {R : Type*} (b : Fin D → R) (c : Fin E → R) :
    slotPrefix (Fin.append b c) = b := by ext i; simp [slotPrefix]

@[simp] theorem slotSuffix_append {R : Type*} (b : Fin D → R) (c : Fin E → R) :
    slotSuffix (Fin.append b c) = c := by ext i; simp [slotSuffix]

namespace TriangularSlots

def append (A : TriangularSlots D) (B : (Fin D → ℝ) → TriangularSlots E) :
    TriangularSlots (D + E) where
  center x := Fin.append (A.center (slotPrefix x)) ((B (slotPrefix x)).center (slotSuffix x))
  lower i := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · intro x y hxy
      simp only [Fin.append_left]
      apply A.lower
      intro k hkj
      exact hxy (k.castAdd E) (by simpa only [Fin.lt_def, Fin.val_castAdd] using hkj)
    · intro x y hxy
      simp only [Fin.append_right]
      have hp : slotPrefix x = slotPrefix y := by
        ext k
        exact hxy (k.castAdd E) (by simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]; omega)
      rw [hp]
      apply (B (slotPrefix y)).lower
      intro k hkj
      exact hxy (k.natAdd D) (by simpa only [Fin.lt_def, Fin.val_natAdd, Nat.add_lt_add_iff_left] using hkj)

end TriangularSlots

theorem dist_append_same_left_le (z : Fin D → ℝ) (x y : Fin E → ℝ) :
    dist (Fin.append z x) (Fin.append z y) ≤ dist x y := by
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp
  · simpa only [Fin.append_right] using dist_le_pi_dist x y j

namespace PatchKernel

def freeze (Φ : PatchKernel (D + E)) (z : Fin D → ℝ) : PatchKernel E where
  value y := Φ.value (Fin.append z y)
  nonneg y := Φ.nonneg _
  le_one y := Φ.le_one _
  support y hy i := by simpa using Φ.support _ hy (i.natAdd D)
  lip := Φ.lip
  lipschitz := LipschitzWith.of_dist_le_mul (fun x y =>
    (Φ.lipschitz.dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left (dist_append_same_left_le z x y) Φ.lip.coe_nonneg))

end PatchKernel

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem rationalLiftCharacterTwistLip_le_exp {m : ℕ}
    (M : ℕ) (hM : 0 < M) (a : Fin m → ℤ) (p q : ℝ)
    (hm : (m : ℝ) ≤ Real.exp p) (ha : ∀ i, |(a i : ℝ)| ≤ Real.exp q) :
    (rationalLiftCharacterTwistLip M a : ℝ) ≤ Real.exp (p + q + 8) := by
  have hpi : 2 * Real.pi ≤ Real.exp (8 : ℝ) := by
    linarith [Real.pi_lt_four, Real.add_one_le_exp (8 : ℝ)]
  calc
    _ ≤ 2 * Real.pi * m * Real.exp q := rationalLiftCharacterTwistLip_le M hM a _ ha
    _ ≤ Real.exp 8 * Real.exp p * Real.exp q := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hpi hm (Nat.cast_nonneg m) (Real.exp_nonneg _)) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem rationalLiftCharacterTwistLip_le_exp_of_dim {m : ℕ}
    (M : ℕ) (hM : 0 < M) (a : Fin m → ℤ) (p q : ℝ)
    (hm : (m : ℝ) ≤ p) (ha : ∀ i, |(a i : ℝ)| ≤ Real.exp q) :
    (rationalLiftCharacterTwistLip M a : ℝ) ≤ Real.exp (p + q + 8) :=
  rationalLiftCharacterTwistLip_le_exp M hM a p q
    (hm.trans (by linarith [Real.add_one_le_exp p])) ha

end Erdos3

end

section

namespace Erdos3

theorem stable_sort_symm_lt {n : ℕ} (w : Fin n → ℕ) {i j : Fin n}
    (hij : i < j) (hw : w i ≤ w j) :
    (Tuple.sort w).symm i < (Tuple.sort w).symm j := by
  by_contra h
  have hji : (Tuple.sort w).symm j < (Tuple.sort w).symm i :=
    lt_of_le_of_ne (le_of_not_gt h) (fun he => hij.ne ((Tuple.sort w).symm.injective he.symm))
  have hwji := Tuple.monotone_sort w hji.le
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at hwji
  have htie := (Tuple.eq_sort_iff.mp (rfl : Tuple.sort w = Tuple.sort w)).2
    _ _ hji (by simpa only [Equiv.apply_symm_apply] using le_antisymm hwji hw)
  simp only [Equiv.apply_symm_apply] at htie
  exact (lt_asymm hij htie)

structure SlotInterleaving (D E : ℕ) where
  perm : Equiv.Perm (Fin (D + E))
  left_strictMono : StrictMono (fun i : Fin D => perm.symm (i.castAdd E))
  right_strictMono : StrictMono (fun i : Fin E => perm.symm (i.natAdd D))

namespace SlotInterleaving

variable {D E : ℕ}

def left (I : SlotInterleaving D E) (i : Fin D) : Fin (D + E) :=
  I.perm.symm (i.castAdd E)

def right (I : SlotInterleaving D E) (i : Fin E) : Fin (D + E) :=
  I.perm.symm (i.natAdd D)

def fill (I : SlotInterleaving D E) {R : Type*} (x : Fin D → R) (y : Fin E → R) :
    Fin (D + E) → R := fun k => Fin.append x y (I.perm k)

@[simp] theorem fill_left (I : SlotInterleaving D E) {R : Type*}
    (x : Fin D → R) (y : Fin E → R) (i : Fin D) : I.fill x y (I.left i) = x i := by
  simp [fill, left]

@[simp] theorem fill_right (I : SlotInterleaving D E) {R : Type*}
    (x : Fin D → R) (y : Fin E → R) (i : Fin E) : I.fill x y (I.right i) = y i := by
  simp [fill, right]

theorem cases (I : SlotInterleaving D E) {p : Fin (D + E) → Prop}
    (hl : ∀ i, p (I.left i)) (hr : ∀ i, p (I.right i)) (k : Fin (D + E)) : p k := by
  rw [← I.perm.symm_apply_apply k]
  exact Fin.addCases hl hr (I.perm k)

def sorted (w : Fin D → ℕ) (v : Fin E → ℕ) (hw : Monotone w) (hv : Monotone v) :
    SlotInterleaving D E where
  perm := Tuple.sort (Fin.append w v)
  left_strictMono i j hij := stable_sort_symm_lt _
    (by simpa only [Fin.lt_def, Fin.val_castAdd] using hij)
    (by simpa using hw hij.le)
  right_strictMono i j hij := stable_sort_symm_lt _ (by simpa using hij)
    (by simpa using hv hij.le)

theorem sorted_weight_mono (w : Fin D → ℕ) (v : Fin E → ℕ)
    (hw : Monotone w) (hv : Monotone v) :
    Monotone ((sorted w v hw hv).fill w v) := Tuple.monotone_sort _

end SlotInterleaving

theorem dist_restrict_coordinates_le {d n : ℕ} (f : Fin d → Fin n)
    (x y : Fin n → ℝ) : dist (fun i => x (f i)) (fun i => y (f i)) ≤ dist x y := by
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  exact dist_le_pi_dist x y (f i)

end Erdos3

end

section

namespace Erdos3

namespace TriangularSlots

variable {D E : ℕ}

end TriangularSlots

end Erdos3

end

section

namespace Erdos3.TriangularSlots

variable {D E d : ℕ}

@[ext] theorem ext {A B : TriangularSlots d}
    (h : ∀ x i, A.center x i = B.center x i) : A = B := by
  have hc : A.center = B.center := funext (fun x => funext (h x))
  cases A
  cases B
  cases hc
  rfl

def takePrefix (A : TriangularSlots (D + E)) : TriangularSlots D where
  center x i := A.center (Fin.append x 0) (i.castAdd E)
  lower i x y hxy := by
    apply A.lower
    intro j
    refine Fin.addCases (fun k hj => ?_) (fun k hj => ?_) j
    · simp only [Fin.append_left]
      apply hxy
      simpa only [Fin.lt_def, Fin.val_castAdd] using hj
    · simp only [Fin.append_right]

def dropPrefix (A : TriangularSlots (D + E)) (b : Fin D → ℝ) : TriangularSlots E where
  center x i := A.center (Fin.append b x) (i.natAdd D)
  lower i x y hxy := by
    apply A.lower
    intro j
    refine Fin.addCases (fun k hj => ?_) (fun k hj => ?_) j
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]
      apply hxy
      simpa only [Fin.lt_def, Fin.val_natAdd, Nat.add_lt_add_iff_left] using hj

end Erdos3.TriangularSlots

end

section

namespace Erdos3

variable {D E : ℕ}

namespace TriangularSlots

def interleave (A : TriangularSlots D) (B : TriangularSlots E)
    (I : SlotInterleaving D E) : TriangularSlots (D + E) where
  center x := I.fill (A.center (fun i => x (I.left i)))
    (B.center (fun i => x (I.right i)))
  lower k x y h := by
    apply I.cases (p := fun k =>
      (∀ j, j < k → x j = y j) →
      I.fill (A.center (fun i => x (I.left i))) (B.center (fun i => x (I.right i))) k =
      I.fill (A.center (fun i => y (I.left i))) (B.center (fun i => y (I.right i))) k) _ _ k h
    · intro i hi
      simp only [SlotInterleaving.fill_left]
      exact A.lower i _ _ (fun j hj => hi _ (I.left_strictMono hj))
    · intro i hi
      simp only [SlotInterleaving.fill_right]
      exact B.lower i _ _ (fun j hj => hi _ (I.right_strictMono hj))

@[simp] theorem interleave_residual_left (A : TriangularSlots D) (B : TriangularSlots E)
    (I : SlotInterleaving D E) (z : Fin (D + E) → ℤ) (i : Fin D) :
    (A.interleave B I).residual z (I.left i) = A.residual (fun j => z (I.left j)) i := by
  simp [residual, interleave]

@[simp] theorem interleave_residual_right (A : TriangularSlots D) (B : TriangularSlots E)
    (I : SlotInterleaving D E) (z : Fin (D + E) → ℤ) (i : Fin E) :
    (A.interleave B I).residual z (I.right i) = B.residual (fun j => z (I.right j)) i := by
  simp [residual, interleave]

end TriangularSlots

namespace PatchKernel

def product (Φ : PatchKernel D) (Ψ : PatchKernel E) (I : SlotInterleaving D E) :
    PatchKernel (D + E) where
  value x := Φ.value (fun i => x (I.left i)) * Ψ.value (fun i => x (I.right i))
  nonneg x := mul_nonneg (Φ.nonneg _) (Ψ.nonneg _)
  le_one x := (mul_le_of_le_one_left (Ψ.nonneg _) (Φ.le_one _)).trans (Ψ.le_one _)
  support x hx := by
    have hl := Φ.support _ (mul_ne_zero_iff.mp hx).1
    have hr := Ψ.support _ (mul_ne_zero_iff.mp hx).2
    exact I.cases hl hr
  lip := Φ.lip + Ψ.lip
  lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    let x₁ := fun i => x (I.left i)
    let x₂ := fun i => x (I.right i)
    let y₁ := fun i => y (I.left i)
    let y₂ := fun i => y (I.right i)
    have hl : dist (Φ.value x₁) (Φ.value y₁) ≤ Φ.lip * dist x y :=
      (Φ.lipschitz.dist_le_mul _ _).trans
        (mul_le_mul_of_nonneg_left (dist_restrict_coordinates_le I.left x y) Φ.lip.coe_nonneg)
    have hr : dist (Ψ.value x₂) (Ψ.value y₂) ≤ Ψ.lip * dist x y :=
      (Ψ.lipschitz.dist_le_mul _ _).trans
        (mul_le_mul_of_nonneg_left (dist_restrict_coordinates_le I.right x y) Ψ.lip.coe_nonneg)
    have h₁ : dist (Φ.value x₁ * Ψ.value x₂) (Φ.value y₁ * Ψ.value x₂) ≤
        dist (Φ.value x₁) (Φ.value y₁) := by
      rw [Real.dist_eq, ← sub_mul, abs_mul, abs_of_nonneg (Ψ.nonneg _)]
      exact mul_le_of_le_one_right (abs_nonneg _) (Ψ.le_one _)
    have h₂ : dist (Φ.value y₁ * Ψ.value x₂) (Φ.value y₁ * Ψ.value y₂) ≤
        dist (Ψ.value x₂) (Ψ.value y₂) := by
      rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (Φ.nonneg _)]
      exact mul_le_of_le_one_left (abs_nonneg _) (Φ.le_one _)
    exact (dist_triangle _ (Φ.value y₁ * Ψ.value x₂) _).trans
      ((add_le_add (h₁.trans hl) (h₂.trans hr)).trans_eq (by simp [add_mul]))

@[simp] theorem product_lip (Φ : PatchKernel D) (Ψ : PatchKernel E)
    (I : SlotInterleaving D E) : (Φ.product Ψ I).lip = Φ.lip + Ψ.lip := rfl

@[simp] theorem product_value_fill (Φ : PatchKernel D) (Ψ : PatchKernel E)
    (I : SlotInterleaving D E) (x : Fin D → ℝ) (y : Fin E → ℝ) :
    (Φ.product Ψ I).value (I.fill x y) = Φ.value x * Ψ.value y := by
  simp [product]

end PatchKernel

namespace TriangularSlots

theorem interleave_kernel_residual (A : TriangularSlots D) (B : TriangularSlots E)
    (Φ : PatchKernel D) (Ψ : PatchKernel E) (I : SlotInterleaving D E)
    (z : Fin (D + E) → ℤ) :
    (Φ.product Ψ I).value ((A.interleave B I).residual z) =
      Φ.value (A.residual (fun j => z (I.left j))) *
      Ψ.value (B.residual (fun j => z (I.right j))) := by
  simp [PatchKernel.product]

theorem interleave_patchValue (A : TriangularSlots D) (B : TriangularSlots E)
    (Φ : PatchKernel D) (Ψ : PatchKernel E) (I : SlotInterleaving D E) :
    (A.interleave B I).patchValue (Φ.product Ψ I) = A.patchValue Φ * B.patchValue Ψ := by
  classical
  by_cases hA : ∃ b, Φ.value (A.residual b) ≠ 0
  · obtain ⟨b, hb⟩ := hA
    by_cases hB : ∃ c, Ψ.value (B.residual c) ≠ 0
    · obtain ⟨c, hc⟩ := hB
      have hz : (Φ.product Ψ I).value ((A.interleave B I).residual (I.fill b c)) ≠ 0 := by
        simpa [interleave_kernel_residual] using mul_ne_zero hb hc
      rw [(A.interleave B I).patchValue_eq_of_nonzero _ hz,
        A.patchValue_eq_of_nonzero _ hb, B.patchValue_eq_of_nonzero _ hc]
      simp [interleave_kernel_residual]
    · have hc : ∀ c, Ψ.value (B.residual c) = 0 := by simpa using hB
      rw [B.patchValue_eq_zero _ hc, mul_zero]
      apply patchValue_eq_zero
      intro z
      rw [interleave_kernel_residual, hc, mul_zero]
  · have hb : ∀ b, Φ.value (A.residual b) = 0 := by simpa using hA
    rw [A.patchValue_eq_zero _ hb, zero_mul]
    apply patchValue_eq_zero
    intro z
    rw [interleave_kernel_residual, hb, zero_mul]

end TriangularSlots

end Erdos3

end

section

namespace Erdos3.TriangularSlots

variable {D E : ℕ}

end Erdos3.TriangularSlots

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DynkinTrees
namespace OAI

section

namespace Erdos3

abbrev WordPolynomial (X : Type*) := MonoidAlgebra ℚ (FreeSemigroup X)

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

def rightBracket (x : L) : Module.End ℚ L where
  toFun z := ⁅z, x⁆
  map_add' z w := add_lie z w x
  map_smul' c z := smul_lie c z x

@[simp] theorem rightBracket_apply (x z : L) : rightBracket x z = ⁅z, x⁆ := rfl

def rightBracketList (f : X → L) : List X → Module.End ℚ L
  | [] => 1
  | x :: xs => rightBracketList f xs * rightBracket (f x)

@[simp] theorem rightBracketList_nil (f : X → L) : rightBracketList f [] = 1 := rfl
@[simp] theorem rightBracketList_cons (f : X → L) (x : X) (xs : List X) :
    rightBracketList f (x :: xs) = rightBracketList f xs * rightBracket (f x) := rfl

theorem rightBracketList_append (f : X → L) (xs ys : List X) :
    rightBracketList f (xs ++ ys) = rightBracketList f ys * rightBracketList f xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.cons_append, rightBracketList_cons, ih, mul_assoc]

def rightBracketWord (f : X → L) (w : FreeSemigroup X) : Module.End ℚ L :=
  rightBracketList f (w.head :: w.tail)

theorem rightBracketWord_mul (f : X → L) (u v : FreeSemigroup X) :
    rightBracketWord f (u * v) = rightBracketWord f v * rightBracketWord f u := by
  change rightBracketList f ((u.head :: u.tail) ++ (v.head :: v.tail)) = _
  exact rightBracketList_append f _ _

def dynkinWord (f : X → L) (w : FreeSemigroup X) : L :=
  rightBracketList f w.tail (f w.head)

theorem dynkinWord_mul (f : X → L) (u v : FreeSemigroup X) :
    dynkinWord f (u * v) = rightBracketWord f v (dynkinWord f u) := by
  simp only [dynkinWord, FreeSemigroup.tail_mul, FreeSemigroup.head_mul,
    rightBracketList_append, Module.End.mul_apply, rightBracketWord]

noncomputable def wordLinearMap {M : Type*} [AddCommGroup M] [Module ℚ M]
    (v : FreeSemigroup X → M) : WordPolynomial X →ₗ[ℚ] M :=
  (Finsupp.linearCombination ℚ v).comp (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

@[simp] theorem wordLinearMap_single {M : Type*} [AddCommGroup M] [Module ℚ M]
    (v : FreeSemigroup X → M) (w : FreeSemigroup X) (r : ℚ) :
    wordLinearMap v (MonoidAlgebra.single w r) = r • v w := by
  simp [wordLinearMap]

noncomputable def dynkinMap (f : X → L) : WordPolynomial X →ₗ[ℚ] L :=
  wordLinearMap (dynkinWord f)

noncomputable def rightAction (f : X → L) : WordPolynomial X →ₗ[ℚ] Module.End ℚ L :=
  wordLinearMap (rightBracketWord f)

@[simp] theorem dynkinMap_single (f : X → L) (w : FreeSemigroup X) (r : ℚ) :
    dynkinMap f (MonoidAlgebra.single w r) = r • dynkinWord f w := wordLinearMap_single _ _ _

@[simp] theorem rightAction_single (f : X → L) (w : FreeSemigroup X) (r : ℚ) :
    rightAction f (MonoidAlgebra.single w r) = r • rightBracketWord f w :=
  wordLinearMap_single _ _ _

theorem rightAction_mul (f : X → L) (p q : WordPolynomial X) :
    rightAction f (p * q) = rightAction f q * rightAction f p := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p₁ p₂ h₁ h₂ => simp [add_mul, h₁, h₂, mul_add]
  | single u r =>
    induction q using MonoidAlgebra.induction_linear with
    | zero => simp
    | add q₁ q₂ h₁ h₂ => simp [mul_add, h₁, h₂, add_mul]
    | single v t =>
      simp only [MonoidAlgebra.single_mul_single, rightAction_single, rightBracketWord_mul]
      rw [smul_mul_smul, mul_comm r t]

theorem dynkinMap_mul (f : X → L) (p q : WordPolynomial X) :
    dynkinMap f (p * q) = rightAction f q (dynkinMap f p) := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p₁ p₂ h₁ h₂ => simp [add_mul, h₁, h₂]
  | single u r =>
    induction q using MonoidAlgebra.induction_linear with
    | zero => simp
    | add q₁ q₂ h₁ h₂ => simp [mul_add, h₁, h₂]
    | single v t =>
      simp only [MonoidAlgebra.single_mul_single, dynkinMap_single, rightAction_single,
        dynkinWord_mul, LinearMap.smul_apply, map_smul, smul_smul]

end Erdos3

end

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

def lieTreeEval (f : X → L) : FreeMagma X → L
  | .of x => f x
  | .mul u v => ⁅lieTreeEval f u, lieTreeEval f v⁆

noncomputable def commutatorTree : FreeMagma X → WordPolynomial X
  | .of x => MonoidAlgebra.single (FreeSemigroup.of x) 1
  | .mul u v => commutatorTree u * commutatorTree v - commutatorTree v * commutatorTree u

theorem rightBracket_lie (u v : L) :
    rightBracket ⁅u, v⁆ = rightBracket v * rightBracket u - rightBracket u * rightBracket v := by
  ext z
  change ⁅z, ⁅u, v⁆⁆ = ⁅⁅z, u⁆, v⁆ - ⁅⁅z, v⁆, u⁆
  rw [leibniz_lie, ← lie_skew u ⁅z, v⁆, sub_eq_add_neg]

theorem rightAction_commutatorTree (f : X → L) (t : FreeMagma X) :
    rightAction f (commutatorTree t) = rightBracket (lieTreeEval f t) := by
  induction t using FreeMagma.rec with
  | of x =>
    simp [commutatorTree, lieTreeEval, rightBracketWord, FreeSemigroup.of]
  | mul u v hu hv =>
    simp only [commutatorTree, map_sub, rightAction_mul, hu, hv, lieTreeEval, rightBracket_lie]

theorem dynkinMap_commutatorTree (f : X → L) (t : FreeMagma X) :
    dynkinMap f (commutatorTree t) = (t.length : ℚ) • lieTreeEval f t := by
  induction t using FreeMagma.rec with
  | of x => simp [commutatorTree, lieTreeEval, dynkinWord, FreeSemigroup.of]
  | mul u v hu hv =>
    simp only [commutatorTree, map_sub, dynkinMap_mul, rightAction_commutatorTree,
      hu, hv, rightBracket_apply, smul_lie, FreeMagma.length, Nat.cast_add,
      lieTreeEval, add_smul]
    rw [← lie_skew (lieTreeEval f v) (lieTreeEval f u), smul_neg, sub_neg_eq_add]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FormalExpLog
namespace OAI

section

namespace Erdos3

open PowerSeries

theorem formalSeries_eq_of_derivative_eq {f g : PowerSeries ℚ}
    (hd : derivative ℚ f = derivative ℚ g) (hc : constantCoeff f = constantCoeff g) :
    f = g := by
  ext n
  cases n with
  | zero => simpa only [coeff_zero_eq_constantCoeff] using hc
  | succ n =>
    have h := congrArg (coeff n) hd
    simp only [coeff_derivative] at h
    exact mul_right_cancel₀ (by positivity : (n : ℚ) + 1 ≠ 0) h

theorem formal_log_derivative_mul : derivative ℚ (log ℚ) * (1 + X) = (1 : PowerSeries ℚ) := by
  rw [deriv_log, mul_add, mul_one]
  ext n
  cases n with
  | zero => simp
  | succ n =>
    simp only [map_add, coeff_succ_mul_X, coeff_mk, coeff_one, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, and_false, ite_false, pow_succ]
    simp

theorem formal_log_derivative_subst {f : PowerSeries ℚ} (hf : HasSubst f) :
    (derivative ℚ (log ℚ)).subst f * (1 + f) = 1 := by
  have h := congrArg (substAlgHom hf) formal_log_derivative_mul
  simpa only [map_mul, map_add, map_one, substAlgHom_X, coe_substAlgHom] using h

theorem formal_log_exp : (log ℚ).subst (exp ℚ - 1) = (X : PowerSeries ℚ) := by
  apply formalSeries_eq_of_derivative_eq
  · rw [derivative_subst HasSubst.exp_sub_one, derivative_X]
    have hd : derivative ℚ (exp ℚ - 1) = exp ℚ := by simp [derivative_exp]
    rw [hd]
    have hadd : (1 : PowerSeries ℚ) + (exp ℚ - 1) = exp ℚ := by abel
    simpa only [hadd] using
      formal_log_derivative_subst (f := exp ℚ - 1) HasSubst.exp_sub_one
  · have h := constantCoeff_logOf (f := exp ℚ) constantCoeff_exp
    simpa only [logOf_eq, constantCoeff_X] using h

theorem formal_exp_sub_one_log : (exp ℚ - 1).subst (log ℚ) = (X : PowerSeries ℚ) := by
  have hP' : IsUnit (coeff 1 (log ℚ)) := by rw [coeff_one_log]; exact isUnit_one
  have hQ : exp ℚ - 1 = (log ℚ).substInvOfIsUnit hP' := calc
    _ = PowerSeries.subst (exp ℚ - 1) X := (subst_X HasSubst.exp_sub_one).symm
    _ = _ := by
      rw [← (log ℚ).subst_substInvOfIsUnit_left constantCoeff_log hP',
        subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' constantCoeff_log)
          HasSubst.exp_sub_one _, formal_log_exp, X_subst _]
  rw [hQ, (log ℚ).subst_substInvOfIsUnit_left constantCoeff_log hP']

theorem formal_exp_log : (exp ℚ).subst (log ℚ) = (1 + X : PowerSeries ℚ) := by
  have h := formal_exp_sub_one_log
  rw [subst_sub HasSubst.log] at h
  have hone : (1 : PowerSeries ℚ).subst (log ℚ) = 1 := by
    rw [← coe_substAlgHom HasSubst.log, map_one]
  rw [hone] at h
  exact sub_eq_iff_eq_add.mp h |>.trans (add_comm _ _)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FourBalancedRelations
namespace OAI

section

namespace Erdos3

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

def fourAlternatingMap : (Fin 4 → V) →ₗ[R] V :=
  (LinearMap.proj 0 : (Fin 4 → V) →ₗ[R] V) + LinearMap.proj 1 - LinearMap.proj 2 - LinearMap.proj 3

theorem fourAlternatingMap_apply (v : Fin 4 → V) :
    fourAlternatingMap (R := R) v = v 0 + v 1 - v 2 - v 3 := rfl

def fourCommonModulo (C D : Submodule R V) : Submodule R (Fin 4 → V) :=
  Submodule.pi Set.univ (fun _ => C) ⊓
    ⨅ k : Fin 4, D.comap ((LinearMap.proj k : (Fin 4 → V) →ₗ[R] V) - LinearMap.proj 0)

theorem mem_fourCommonModulo (C D : Submodule R V) (v : Fin 4 → V) :
    v ∈ fourCommonModulo C D ↔ (∀ k, v k ∈ C) ∧ ∀ k, v k - v 0 ∈ D := by
  simp [fourCommonModulo, Submodule.mem_pi]

def fourBalancedDependent (D : Submodule R V) : Submodule R (Fin 4 → V) :=
  Submodule.pi Set.univ (fun _ => D) ⊓ LinearMap.ker (fourAlternatingMap (R := R))

theorem mem_fourBalancedDependent (D : Submodule R V) (v : Fin 4 → V) :
    v ∈ fourBalancedDependent D ↔ (∀ k, v k ∈ D) ∧ v 0 + v 1 - v 2 - v 3 = 0 := by
  simp [fourBalancedDependent, Submodule.mem_pi, fourAlternatingMap_apply]

theorem fourBalancedDependent_le_common (C D : Submodule R V) (hDC : D ≤ C) :
    fourBalancedDependent D ≤ fourCommonModulo C D := by
  intro v hv
  obtain ⟨hv, _⟩ := (mem_fourBalancedDependent D v).mp hv
  exact (mem_fourCommonModulo C D v).mpr
    ⟨fun k => hDC (hv k), fun k => D.sub_mem (hv k) (hv 0)⟩

def fourRefinedRelation (C D : Submodule R V) (K : Submodule R (Fin 4 → V)) :
    Submodule R (Fin 4 → V) :=
  (K ⊓ fourCommonModulo C D) ⊔ fourBalancedDependent D

theorem fourRefinedRelation_le_common (C D : Submodule R V) (hDC : D ≤ C)
    (K : Submodule R (Fin 4 → V)) : fourRefinedRelation C D K ≤ fourCommonModulo C D :=
  sup_le inf_le_right (fourBalancedDependent_le_common C D hDC)

theorem fourBalancedDependent_le_refined (C D : Submodule R V)
    (K : Submodule R (Fin 4 → V)) : fourBalancedDependent D ≤ fourRefinedRelation C D K :=
  le_sup_right

def fourPetalSpace (D : Submodule R V) (K : Submodule R (Fin 4 → V)) : Submodule R V :=
  D ⊓ K.comap (LinearMap.single R (fun _ : Fin 4 => V) 0)

theorem mem_fourPetalSpace (D : Submodule R V) (K : Submodule R (Fin 4 → V)) (v : V) :
    v ∈ fourPetalSpace D K ↔ v ∈ D ∧ LinearMap.single R (fun _ : Fin 4 => V) 0 v ∈ K := Iff.rfl

theorem fourPetalSpace_le_first (D : Submodule R V) (K : Submodule R (Fin 4 → V)) :
    fourPetalSpace D K ≤ K.map (LinearMap.proj 0) := by
  intro v hv
  exact ⟨LinearMap.single R (fun _ : Fin 4 => V) 0 v, hv.2, by simp [LinearMap.single_apply]⟩

theorem fourAlternatingMap_mem_dependent (C D : Submodule R V) (v : Fin 4 → V)
    (hv : v ∈ fourCommonModulo C D) : fourAlternatingMap (R := R) v ∈ D := by
  have h := (mem_fourCommonModulo C D v).mp hv
  have heq : fourAlternatingMap (R := R) v = (v 1 - v 0) - (v 2 - v 0) - (v 3 - v 0) := by
    rw [fourAlternatingMap_apply]
    abel
  rw [heq]
  exact D.sub_mem (D.sub_mem (h.2 1) (h.2 2)) (h.2 3)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalHeight
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def RationalHeightLE (q : ℚ) (H : ℕ) : Prop :=
  q.num.natAbs ≤ H ∧ q.den ≤ H

theorem RationalHeightLE.mono {q : ℚ} {H K : ℕ}
    (hq : RationalHeightLE q H) (hHK : H ≤ K) : RationalHeightLE q K :=
  ⟨hq.1.trans hHK, hq.2.trans hHK⟩

theorem rational_fraction_entries_le (a b : ℤ) (hb : b ≠ 0) :
    ((a : ℚ) / b).num.natAbs ≤ a.natAbs ∧
      ((a : ℚ) / b).den ≤ b.natAbs := by
  obtain ⟨c, ha, hd⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den a hb
  have hc : c ≠ 0 := by
    intro h
    exact hb (by simpa [h] using hd)
  have hcpos : 0 < c.natAbs := Int.natAbs_pos.mpr hc
  constructor
  · calc
      _ ≤ c.natAbs * ((a : ℚ) / b).num.natAbs := Nat.le_mul_of_pos_left _ hcpos
      _ = a.natAbs := by simpa only [Int.natAbs_mul] using congrArg Int.natAbs ha.symm
  · calc
      _ ≤ c.natAbs * ((a : ℚ) / b).den := Nat.le_mul_of_pos_left _ hcpos
      _ = b.natAbs := by
        simpa only [Int.natAbs_mul, Int.natAbs_natCast] using congrArg Int.natAbs hd.symm

theorem rationalHeightLE_fraction (a b : ℤ) (hb : b ≠ 0)
    {H : ℕ} (haH : a.natAbs ≤ H) (hbH : b.natAbs ≤ H) :
    RationalHeightLE ((a : ℚ) / b) H :=
  ⟨(rational_fraction_entries_le a b hb).1.trans haH,
    (rational_fraction_entries_le a b hb).2.trans hbH⟩

section Array

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def arrayDenominator (q : ι → ℚ) : ℕ := ∏ i, (q i).den

def clearedArray (q : ι → ℚ) (i : ι) : ℤ :=
  (q i).num * (∏ j ∈ Finset.univ.erase i, (q j).den : ℕ)

omit [DecidableEq ι] in
theorem arrayDenominator_pos (q : ι → ℚ) : 0 < arrayDenominator q :=
  Finset.prod_pos fun i _ => (q i).den_pos

omit [DecidableEq ι] in
theorem arrayDenominator_le (q : ι → ℚ) {H : ℕ}
    (hq : ∀ i, (q i).den ≤ H) :
    arrayDenominator q ≤ H ^ Fintype.card ι := by
  exact (Finset.prod_le_prod' fun i _ => hq i).trans_eq (by simp)

theorem arrayDenominator_eq (q : ι → ℚ) (i : ι) :
    arrayDenominator q = (q i).den * ∏ j ∈ Finset.univ.erase i, (q j).den := by
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

theorem clearedArray_cast (q : ι → ℚ) (i : ι) :
    (clearedArray q i : ℚ) = (arrayDenominator q : ℚ) * q i := by
  rw [arrayDenominator_eq q i]
  have hq := Rat.num_div_den (q i)
  have hd : ((q i).den : ℚ) ≠ 0 := by exact_mod_cast (q i).den_ne_zero
  dsimp only [clearedArray]
  push_cast
  conv_rhs => rhs; rw [← hq]
  field_simp

theorem clearedArray_natAbs_le (q : ι → ℚ) {H : ℕ}
    (hq : ∀ i, RationalHeightLE (q i) H) (i : ι) :
    (clearedArray q i).natAbs ≤ H ^ Fintype.card ι := by
  have hprod : (∏ j ∈ Finset.univ.erase i, (q j).den) ≤
      H ^ (Finset.univ.erase i).card := by
    exact (Finset.prod_le_prod' fun j _ => (hq j).2).trans_eq (by simp)
  have hcard : (Finset.univ.erase i).card + 1 = Fintype.card ι := by
    simpa using Finset.card_erase_add_one (Finset.mem_univ i)
  calc
    (clearedArray q i).natAbs =
        (q i).num.natAbs * ∏ j ∈ Finset.univ.erase i, (q j).den := by
      simp only [clearedArray, Int.natAbs_mul, Int.natAbs_natCast]
    _ ≤ H * H ^ (Finset.univ.erase i).card := Nat.mul_le_mul (hq i).1 hprod
    _ = H ^ Fintype.card ι := by rw [← hcard, pow_succ, mul_comm]

theorem exists_bounded_integer_array (q : ι → ℚ) {H : ℕ}
    (hq : ∀ i, RationalHeightLE (q i) H) :
    ∃ D : ℕ, 0 < D ∧ D ≤ H ^ Fintype.card ι ∧
      ∃ a : ι → ℤ, (∀ i, (a i : ℚ) = (D : ℚ) * q i) ∧
        ∀ i, (a i).natAbs ≤ H ^ Fintype.card ι :=
  ⟨arrayDenominator q, arrayDenominator_pos q,
    arrayDenominator_le q (fun i => (hq i).2), clearedArray q,
    clearedArray_cast q, clearedArray_natAbs_le q hq⟩

end Array

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TruncatedSeries
namespace OAI

section

namespace Erdos3
variable {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]

def truncatedSeriesCon (A : Type*) [Ring A] (s : ℕ) : RingCon (PowerSeries A) where
  r f g := ∀ n, n ≤ s → PowerSeries.coeff n f = PowerSeries.coeff n g
  iseqv := ⟨fun _ _ _ => rfl, fun h n hn => (h n hn).symm,
    fun h₁ h₂ n hn => (h₁ n hn).trans (h₂ n hn)⟩
  add' hf hg n hn := by rw [map_add, map_add, hf n hn, hg n hn]
  mul' hf hg n hn := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro ij hij
    have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    rw [hf ij.1 (by omega), hg ij.2 (by omega)]

abbrev TruncatedSeries (A : Type*) [Ring A] (s : ℕ) := (truncatedSeriesCon A s).Quotient

noncomputable def truncatedSeriesMk (s : ℕ) : PowerSeries A →ₐ[ℚ] TruncatedSeries A s :=
  (truncatedSeriesCon A s).mkₐ ℚ

theorem truncatedSeriesMk_surjective (s : ℕ) :
    Function.Surjective (truncatedSeriesMk (A := A) s) :=
  (truncatedSeriesCon A s).mkₐ_surjective

theorem truncatedSeriesMk_eq_iff (s : ℕ) (f g : PowerSeries A) :
    truncatedSeriesMk s f = truncatedSeriesMk s g ↔
      ∀ n, n ≤ s → PowerSeries.coeff n f = PowerSeries.coeff n g :=
  (truncatedSeriesCon A s).eq

noncomputable def truncatedSeriesCoeff (s n : ℕ) (hn : n ≤ s) :
    TruncatedSeries A s →ₗ[ℚ] A where
  toFun := Quotient.lift (PowerSeries.coeff n) (fun _ _ h => h n hn)
  map_add' p q := by
    obtain ⟨f, rfl⟩ := truncatedSeriesMk_surjective s p
    obtain ⟨g, rfl⟩ := truncatedSeriesMk_surjective s q
    exact map_add (PowerSeries.coeff n) f g
  map_smul' r p := by
    obtain ⟨f, rfl⟩ := truncatedSeriesMk_surjective s p
    exact PowerSeries.coeff_smul n f r

@[simp] theorem truncatedSeriesCoeff_mk (s n : ℕ) (hn : n ≤ s) (f : PowerSeries A) :
    truncatedSeriesCoeff s n hn (truncatedSeriesMk s f) = PowerSeries.coeff n f := rfl

theorem truncatedSeries_ext {s : ℕ} {p q : TruncatedSeries A s}
    (h : ∀ n (hn : n ≤ s), truncatedSeriesCoeff s n hn p = truncatedSeriesCoeff s n hn q) :
    p = q := by
  obtain ⟨f, rfl⟩ := truncatedSeriesMk_surjective s p
  obtain ⟨g, rfl⟩ := truncatedSeriesMk_surjective s q
  exact (truncatedSeriesMk_eq_iff s f g).mpr h

noncomputable def seriesConstantCoeff : PowerSeries A →ₐ[ℚ] A :=
  { PowerSeries.constantCoeff with
    commutes' r := by
      change PowerSeries.constantCoeff (PowerSeries.C (algebraMap ℚ A r)) = _
      exact PowerSeries.constantCoeff_C _ }

noncomputable def truncatedSeriesConstantCoeff (s : ℕ) : TruncatedSeries A s →ₐ[ℚ] A :=
  (truncatedSeriesCon A s).liftₐ seriesConstantCoeff (by
    intro f g h
    change PowerSeries.constantCoeff f = PowerSeries.constantCoeff g
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using h 0 (Nat.zero_le s))

@[simp] theorem truncatedSeriesConstantCoeff_mk (s : ℕ) (f : PowerSeries A) :
    truncatedSeriesConstantCoeff s (truncatedSeriesMk s f) = PowerSeries.constantCoeff f := rfl

noncomputable def truncatedSeriesMap (s : ℕ) (φ : A →ₐ[ℚ] B) :
    TruncatedSeries A s →ₐ[ℚ] TruncatedSeries B s :=
  (truncatedSeriesCon A s).liftₐ ((truncatedSeriesMk s).comp (PowerSeries.mapAlgHom φ)) (by
    intro f g h
    apply (truncatedSeriesMk_eq_iff s _ _).mpr
    intro n hn
    change φ (PowerSeries.coeff n f) = φ (PowerSeries.coeff n g)
    rw [h n hn])

@[simp] theorem truncatedSeriesMap_mk (s : ℕ) (φ : A →ₐ[ℚ] B) (f : PowerSeries A) :
    truncatedSeriesMap s φ (truncatedSeriesMk s f) =
      truncatedSeriesMk s (PowerSeries.mapAlgHom φ f) := rfl

@[simp] theorem truncatedSeriesCoeff_map (s n : ℕ) (hn : n ≤ s) (φ : A →ₐ[ℚ] B)
    (p : TruncatedSeries A s) :
    truncatedSeriesCoeff s n hn (truncatedSeriesMap s φ p) =
      φ (truncatedSeriesCoeff s n hn p) := by
  obtain ⟨f, rfl⟩ := truncatedSeriesMk_surjective s p
  simp [PowerSeries.mapAlgHom_apply]

@[simp] theorem truncatedSeriesConstantCoeff_map (s : ℕ) (φ : A →ₐ[ℚ] B)
    (p : TruncatedSeries A s) :
    truncatedSeriesConstantCoeff s (truncatedSeriesMap s φ p) =
      φ (truncatedSeriesConstantCoeff s p) := by
  obtain ⟨f, rfl⟩ := truncatedSeriesMk_surjective s p
  change PowerSeries.constantCoeff (PowerSeries.map φ.toRingHom f) = _
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff]
  rfl

noncomputable def truncatedSeriesPositive (s : ℕ) : NonUnitalSubalgebra ℚ (TruncatedSeries A s) where
  carrier := {p | truncatedSeriesConstantCoeff s p = 0}
  zero_mem' := map_zero _
  add_mem' hp hq := by
    change truncatedSeriesConstantCoeff s _ = 0 at hp hq ⊢
    rw [map_add, hp, hq, zero_add]
  smul_mem' r p hp := by
    change truncatedSeriesConstantCoeff s _ = 0 at hp ⊢
    rw [map_smul, hp, smul_zero]
  mul_mem' hp hq := by
    change truncatedSeriesConstantCoeff s _ = 0 at hp hq ⊢
    rw [map_mul, hp, hq, zero_mul]

@[simp] theorem mem_truncatedSeriesPositive {s : ℕ} {p : TruncatedSeries A s} :
    p ∈ truncatedSeriesPositive s ↔ truncatedSeriesConstantCoeff s p = 0 := Iff.rfl

theorem truncatedSeriesPositive_pow {s : ℕ} {p : TruncatedSeries A s}
    (hp : p ∈ truncatedSeriesPositive s) : p ^ (s + 1) = 0 := by
  obtain ⟨f, rfl⟩ := truncatedSeriesMk_surjective s p
  change PowerSeries.constantCoeff f = 0 at hp
  rw [← map_pow, ← map_zero (truncatedSeriesMk s)]
  apply (truncatedSeriesMk_eq_iff s _ _).mpr
  intro n hn
  rw [map_zero]
  apply PowerSeries.coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast (Nat.lt_succ_of_le hn))
    (PowerSeries.le_order_pow_of_constantCoeff_eq_zero (s + 1) hp)

theorem truncatedSeriesPositive_nilpotent {s : ℕ} {p : TruncatedSeries A s}
    (hp : p ∈ truncatedSeriesPositive s) : IsNilpotent p :=
  ⟨s + 1, truncatedSeriesPositive_pow hp⟩

theorem truncatedSeriesMap_positive (s : ℕ) (φ : A →ₐ[ℚ] B)
    {p : TruncatedSeries A s} (hp : p ∈ truncatedSeriesPositive s) :
    truncatedSeriesMap s φ p ∈ truncatedSeriesPositive s := by
  rw [mem_truncatedSeriesPositive, truncatedSeriesConstantCoeff_map,
    mem_truncatedSeriesPositive.mp hp, map_zero]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TensorContraction
namespace OAI

section

namespace Erdos3
open TensorProduct
variable {A : Type*} [Ring A] [Algebra ℚ A]

noncomputable def tensorContract (S T : A →ₗ[ℚ] A) : A ⊗[ℚ] A →ₗ[ℚ] A :=
  (LinearMap.mul' ℚ A).comp (TensorProduct.map S T)

@[simp] theorem tensorContract_tmul (S T : A →ₗ[ℚ] A) (a b : A) :
    tensorContract S T (a ⊗ₜ[ℚ] b) = S a * T b := by
  simp [tensorContract]

theorem tensorContract_mul_left (S T : A →ₗ[ℚ] A)
    (hS : ∀ a b, S (a * b) = S b * S a) (t : A ⊗[ℚ] A) (a : A) :
    tensorContract S T (t * (a ⊗ₜ[ℚ] 1)) = S a * tensorContract S T t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul p q => simp [Algebra.TensorProduct.tmul_mul_tmul, hS, mul_assoc]
  | add p q hp hq => simp only [add_mul, map_add, hp, hq, mul_add]

theorem tensorContract_id_mul_right (S : A →ₗ[ℚ] A) (t : A ⊗[ℚ] A) (a : A) :
    tensorContract S LinearMap.id (t * (1 ⊗ₜ[ℚ] a)) =
      tensorContract S LinearMap.id t * a := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul p q => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_assoc]
  | add p q hp hq => simp only [add_mul, map_add, hp, hq]

theorem tensorContract_derivation_mul_right (S T : A →ₗ[ℚ] A)
    (hT : ∀ a b, T (a * b) = T a * b + a * T b) (t : A ⊗[ℚ] A) (a : A) :
    tensorContract S T (t * (1 ⊗ₜ[ℚ] a)) =
      tensorContract S T t * a + tensorContract S LinearMap.id t * T a := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul p q => simp [Algebra.TensorProduct.tmul_mul_tmul, hT, mul_add, mul_assoc]
  | add p q hp hq =>
    simp only [add_mul, map_add, hp, hq]
    abel

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DynkinProjection
namespace OAI

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

def WordHomogeneous (n : ℕ) (p : WordPolynomial X) : Prop :=
  ∀ w, p.coeff w ≠ 0 → w.length = n

theorem WordHomogeneous.sub {n : ℕ} {p q : WordPolynomial X}
    (hp : WordHomogeneous n p) (hq : WordHomogeneous n q) : WordHomogeneous n (p - q) := by
  intro w hw
  by_cases h : p.coeff w = 0
  · apply hq w
    intro he
    apply hw
    change p.coeff w - q.coeff w = 0
    rw [h, he, sub_zero]
  · exact hp w h

theorem WordHomogeneous.mul {n m : ℕ} {p q : WordPolynomial X}
    (hp : WordHomogeneous n p) (hq : WordHomogeneous m q) : WordHomogeneous (n + m) (p * q) := by
  classical
  intro w hw
  by_contra hlen
  apply hw
  rw [MonoidAlgebra.coeff_mul]
  apply Finset.sum_eq_zero
  intro u hu
  apply Finset.sum_eq_zero
  intro v hv
  have hu' := hp u (Finsupp.mem_support_iff.mp hu)
  have hv' := hq v (Finsupp.mem_support_iff.mp hv)
  have hne : u * v ≠ w := by
    intro he
    apply hlen
    rw [← he, FreeSemigroup.length_mul, hu', hv']
  simp only [hne, ite_false]

theorem commutatorTree_homogeneous (t : FreeMagma X) :
    WordHomogeneous t.length (commutatorTree t) := by
  induction t using FreeMagma.rec with
  | of x =>
    intro w hw
    have he : FreeSemigroup.of x = w := by
      classical
      by_contra hn
      apply hw
      simp [commutatorTree, hn]
    rw [← he]
    rfl
  | mul u v hu hv =>
    apply (hu.mul hv).sub
    simpa only [Nat.add_comm v.length u.length] using hv.mul hu

noncomputable def dynkinProjection (f : X → L) : WordPolynomial X →ₗ[ℚ] L :=
  wordLinearMap (fun w => (w.length : ℚ)⁻¹ • dynkinWord f w)

theorem dynkinProjection_homogeneous (f : X → L) {n : ℕ} {p : WordPolynomial X}
    (hp : WordHomogeneous n p) : dynkinProjection f p = (n : ℚ)⁻¹ • dynkinMap f p := by
  classical
  change p.coeff.sum (fun w r => r • ((w.length : ℚ)⁻¹ • dynkinWord f w)) =
    (n : ℚ)⁻¹ • p.coeff.sum (fun w r => r • dynkinWord f w)
  rw [Finsupp.sum, Finsupp.sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [hp w (Finsupp.mem_support_iff.mp hw), smul_comm]

theorem dynkinProjection_commutatorTree (f : X → L) (t : FreeMagma X) :
    dynkinProjection f (commutatorTree t) = lieTreeEval f t := by
  rw [dynkinProjection_homogeneous f (commutatorTree_homogeneous t),
    dynkinMap_commutatorTree, inv_smul_smul₀]
  exact_mod_cast (Nat.ne_zero_of_lt t.length_pos)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreePrimitiveCriterion
namespace OAI

section

namespace Erdos3

variable {X : Type*}

noncomputable instance wordPolynomialLieRing : LieRing (WordPolynomial X) where
  bracket p q := p * q - q * p
  add_lie p q r := by change (p + q) * r - r * (p + q) = _; simp [add_mul, mul_add]; abel
  lie_add p q r := by change p * (q + r) - (q + r) * p = _; simp [add_mul, mul_add]; abel
  lie_self p := by change p * p - p * p = 0; exact sub_self _
  leibniz_lie p q r := by
    change p * (q * r - r * q) - (q * r - r * q) * p =
      (p * q - q * p) * r - r * (p * q - q * p) +
        (q * (p * r - r * p) - (p * r - r * p) * q)
    noncomm_ring

noncomputable instance wordPolynomialLieAlgebra : LieAlgebra ℚ (WordPolynomial X) where
  lie_smul c p q := by
    change p * (c • q) - (c • q) * p = c • (p * q - q * p)
    rw [mul_smul_comm, smul_mul_assoc, smul_sub]

@[simp] theorem wordPolynomial_lie (p q : WordPolynomial X) : ⁅p, q⁆ = p * q - q * p := rfl

noncomputable def freeLieWordExpansion : FreeLieAlgebra ℚ X →ₗ⁅ℚ⁆ WordPolynomial X :=
  FreeLieAlgebra.lift ℚ (fun x => MonoidAlgebra.single (FreeSemigroup.of x) 1)

@[simp] theorem freeLieWordExpansion_of (x : X) :
    freeLieWordExpansion (FreeLieAlgebra.of ℚ x) = MonoidAlgebra.single (FreeSemigroup.of x) 1 :=
  FreeLieAlgebra.lift_of_apply _ _

theorem freeLieWordExpansion_tree (t : FreeMagma X) :
    freeLieWordExpansion (lieTreeEval (FreeLieAlgebra.of ℚ) t) = commutatorTree t := by
  induction t using FreeMagma.rec with
  | of x => exact freeLieWordExpansion_of x
  | mul u v hu hv =>
    change freeLieWordExpansion ⁅lieTreeEval (FreeLieAlgebra.of ℚ) u,
      lieTreeEval (FreeLieAlgebra.of ℚ) v⁆ = _
    rw [LieHom.map_lie, hu, hv]
    rfl

theorem freeLie_mk_single_tree (t : FreeMagma X) :
    (FreeLieAlgebra.mk ℚ (MonoidAlgebra.single t 1) : FreeLieAlgebra ℚ X) =
      lieTreeEval (FreeLieAlgebra.of ℚ) t := by
  induction t using FreeMagma.rec with
  | of x => rfl
  | mul u v hu hv =>
    have hs := MonoidAlgebra.single_mul_single u v (1 : ℚ) 1
    simp only [one_mul] at hs
    change FreeLieAlgebra.mk ℚ (MonoidAlgebra.single (u * v) 1) = _
    rw [← hs, map_mul]
    change ⁅(FreeLieAlgebra.mk ℚ (MonoidAlgebra.single u 1) : FreeLieAlgebra ℚ X),
      (FreeLieAlgebra.mk ℚ (MonoidAlgebra.single v 1) : FreeLieAlgebra ℚ X)⁆ = _
    rw [hu, hv]
    rfl

theorem freeLie_linear_induction (P : FreeLieAlgebra ℚ X → Prop)
    (hz : P 0) (ha : ∀ x y, P x → P y → P (x + y))
    (hs : ∀ (r : ℚ) x, P x → P (r • x))
    (ht : ∀ t : FreeMagma X, P (lieTreeEval (FreeLieAlgebra.of ℚ) t))
    (x : FreeLieAlgebra ℚ X) : P x := by
  refine Quot.inductionOn x ?_
  intro q
  change P (FreeLieAlgebra.mk ℚ q)
  induction q using MonoidAlgebra.induction_linear with
  | zero =>
    change P (0 : FreeLieAlgebra ℚ X)
    exact hz
  | add p q hp hq =>
    change P ((FreeLieAlgebra.mk ℚ p : FreeLieAlgebra ℚ X) +
      (FreeLieAlgebra.mk ℚ q : FreeLieAlgebra ℚ X))
    exact ha _ _ hp hq
  | single t r =>
    have he : MonoidAlgebra.single t r = r • MonoidAlgebra.single t (1 : ℚ) := by simp
    rw [he, map_smul, freeLie_mk_single_tree]
    exact hs r _ (ht t)

theorem dynkinProjection_freeLieWordExpansion (x : FreeLieAlgebra ℚ X) :
    dynkinProjection (FreeLieAlgebra.of ℚ) (freeLieWordExpansion x) = x := by
  apply freeLie_linear_induction (fun x =>
    dynkinProjection (FreeLieAlgebra.of ℚ) (freeLieWordExpansion x) = x)
  · simp
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro r x hx
    simp only [map_smul, hx]
  · intro t
    rw [freeLieWordExpansion_tree, dynkinProjection_commutatorTree]

theorem freeLieWordExpansion_injective :
    Function.Injective (freeLieWordExpansion (X := X)) :=
  Function.LeftInverse.injective dynkinProjection_freeLieWordExpansion

end Erdos3

end

section

namespace Erdos3

variable {X : Type*}
attribute [local instance] LieRing.ofAssociativeRing

noncomputable def wordPolynomialEmbedding : WordPolynomial X →ₙₐ[ℚ] FreeAlgebra ℚ X :=
  (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm.toAlgHom.toNonUnitalAlgHom).comp
    (MonoidAlgebra.mapDomainNonUnitalAlgHom ℚ ℚ FreeSemigroup.toFreeMonoid)

theorem wordPolynomialEmbedding_injective : Function.Injective (wordPolynomialEmbedding (X := X)) :=
  FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm.injective.comp
    (MonoidAlgebra.mapDomain_injective FreeSemigroup.toFreeMonoid_injective)

@[simp] theorem wordPolynomialEmbedding_generator (x : X) :
    wordPolynomialEmbedding (MonoidAlgebra.single (FreeSemigroup.of x) 1) = FreeAlgebra.ι ℚ x := by
  let e : FreeAlgebra ℚ X ≃ₐ[ℚ] MonoidAlgebra ℚ (FreeMonoid X) :=
    FreeAlgebra.equivMonoidAlgebraFreeMonoid
  change e.symm (MonoidAlgebra.mapDomain FreeSemigroup.toFreeMonoid
    (MonoidAlgebra.single (FreeSemigroup.of x) 1)) = _
  rw [MonoidAlgebra.mapDomain_single, FreeSemigroup.toFreeMonoid_of]
  apply e.injective
  rw [e.apply_symm_apply]
  change MonoidAlgebra.single (FreeMonoid.of x) 1 =
    FreeAlgebra.lift ℚ (fun x => MonoidAlgebra.of ℚ (FreeMonoid X) (FreeMonoid.of x))
      (FreeAlgebra.ι ℚ x)
  rw [FreeAlgebra.lift_ι_apply]
  rfl

noncomputable def wordPolynomialEmbeddingLie : WordPolynomial X →ₗ⁅ℚ⁆ FreeAlgebra ℚ X where
  toFun := wordPolynomialEmbedding
  map_add' := map_add wordPolynomialEmbedding
  map_smul' := map_smul wordPolynomialEmbedding
  map_lie' {p q} := by
    change wordPolynomialEmbedding (p * q - q * p) =
      wordPolynomialEmbedding p * wordPolynomialEmbedding q -
        wordPolynomialEmbedding q * wordPolynomialEmbedding p
    rw [map_sub, map_mul, map_mul]

noncomputable def freeLieAssociativeExpansion : FreeLieAlgebra ℚ X →ₗ⁅ℚ⁆ FreeAlgebra ℚ X :=
  FreeLieAlgebra.lift ℚ (FreeAlgebra.ι ℚ)

theorem wordPolynomialEmbedding_comp_freeLie :
    wordPolynomialEmbeddingLie.comp freeLieWordExpansion =
      (freeLieAssociativeExpansion : FreeLieAlgebra ℚ X →ₗ⁅ℚ⁆ FreeAlgebra ℚ X) := by
  apply FreeLieAlgebra.hom_ext
  intro x
  change wordPolynomialEmbedding (freeLieWordExpansion (FreeLieAlgebra.of ℚ x)) =
    freeLieAssociativeExpansion (FreeLieAlgebra.of ℚ x)
  rw [freeLieWordExpansion_of, wordPolynomialEmbedding_generator]
  exact (FreeLieAlgebra.lift_of_apply _ _).symm

end Erdos3

end

section

namespace Erdos3
variable {X : Type*}

noncomputable def freeWord : FreeMonoid X →* FreeAlgebra ℚ X :=
  FreeMonoid.lift (FreeAlgebra.ι ℚ)

@[simp] theorem freeWord_of (x : X) : freeWord (FreeMonoid.of x) = FreeAlgebra.ι ℚ x :=
  FreeMonoid.lift_eval_of _ _

theorem freeWord_coeff (w : FreeMonoid X) :
    FreeAlgebra.equivMonoidAlgebraFreeMonoid (freeWord w) = MonoidAlgebra.single w 1 := by
  have h : FreeAlgebra.equivMonoidAlgebraFreeMonoid.toAlgHom.toMonoidHom.comp freeWord =
      MonoidAlgebra.of ℚ (FreeMonoid X) := by
    apply FreeMonoid.hom_eq
    intro x
    simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  exact DFunLike.congr_fun h w

theorem freeWord_single_symm (w : FreeMonoid X) (r : ℚ) :
    FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (MonoidAlgebra.single w r) = r • freeWord w := by
  apply FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective
  simp only [AlgEquiv.apply_symm_apply, map_smul, freeWord_coeff]
  simp

noncomputable def freeWordLinearMap {M : Type*} [AddCommGroup M] [Module ℚ M]
    (v : FreeMonoid X → M) : FreeAlgebra ℚ X →ₗ[ℚ] M :=
  (Finsupp.linearCombination ℚ v).comp
    ((MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap.comp
      FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearMap)

@[simp] theorem freeWordLinearMap_word {M : Type*} [AddCommGroup M] [Module ℚ M]
    (v : FreeMonoid X → M) (w : FreeMonoid X) : freeWordLinearMap v (freeWord w) = v w := by
  simp [freeWordLinearMap, freeWord_coeff]

theorem freeAlgebra_linear_induction (P : FreeAlgebra ℚ X → Prop)
    (hz : P 0) (ha : ∀ p q, P p → P q → P (p + q))
    (hs : ∀ (r : ℚ) p, P p → P (r • p)) (hw : ∀ w, P (freeWord w))
    (p : FreeAlgebra ℚ X) : P p := by
  obtain ⟨q, rfl⟩ := FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm.surjective p
  induction q using MonoidAlgebra.induction_linear with
  | zero => simpa only [map_zero] using hz
  | add p q hp hq => simpa only [map_add] using ha _ _ hp hq
  | single w r => rw [freeWord_single_symm]; exact hs r _ (hw w)

theorem freeMonoid_induction_right (P : FreeMonoid X → Prop) (h1 : P 1)
    (hstep : ∀ w x, P w → P (w * FreeMonoid.of x)) (w : FreeMonoid X) : P w := by
  have h : ∀ xs : List X, P (FreeMonoid.ofList xs) := by
    intro xs
    induction xs using List.reverseRecOn with
    | nil => exact h1
    | append_singleton xs x ih =>
      rw [FreeMonoid.ofList_append, FreeMonoid.ofList_singleton]
      exact hstep _ _ ih
  exact h w.toList

noncomputable def freeDegree : FreeAlgebra ℚ X →ₗ[ℚ] FreeAlgebra ℚ X :=
  freeWordLinearMap (fun w => (w.length : ℚ) • freeWord w)

@[simp] theorem freeDegree_word (w : FreeMonoid X) :
    freeDegree (freeWord w) = (w.length : ℚ) • freeWord w := freeWordLinearMap_word _ _

@[simp] theorem freeDegree_one : freeDegree (1 : FreeAlgebra ℚ X) = 0 := by
  have h := freeDegree_word (1 : FreeMonoid X)
  simpa using h

@[simp] theorem freeDegree_generator (x : X) : freeDegree (FreeAlgebra.ι ℚ x) = FreeAlgebra.ι ℚ x := by
  have h := freeDegree_word (FreeMonoid.of x)
  simpa using h

theorem freeDegree_mul (p q : FreeAlgebra ℚ X) :
    freeDegree (p * q) = freeDegree p * q + p * freeDegree q := by
  apply freeAlgebra_linear_induction (fun p =>
    freeDegree (p * q) = freeDegree p * q + p * freeDegree q)
  · simp
  · intro p₁ p₂ h₁ h₂
    simp only [add_mul, map_add, h₁, h₂]
    abel
  · intro r p hp
    simp only [smul_mul_assoc, map_smul, hp, smul_add]
  · intro u
    apply freeAlgebra_linear_induction (fun q =>
      freeDegree (freeWord u * q) = freeDegree (freeWord u) * q + freeWord u * freeDegree q)
    · simp
    · intro q₁ q₂ h₁ h₂
      simp only [mul_add, map_add, h₁, h₂]
      abel
    · intro r q hq
      simp only [mul_smul_comm, map_smul, hq, smul_add]
    · intro v
      rw [← map_mul, freeDegree_word, FreeMonoid.length_mul, Nat.cast_add, add_smul,
        map_mul, freeDegree_word, freeDegree_word, smul_mul_assoc, mul_smul_comm]

end Erdos3

end

section

namespace Erdos3

variable {X L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem map_lieTreeEval (φ : L →ₗ⁅ℚ⁆ M) (f : X → L) (t : FreeMagma X) :
    φ (lieTreeEval f t) = lieTreeEval (fun x => φ (f x)) t := by
  induction t using FreeMagma.rec with
  | of x => rfl
  | mul u v hu hv => simp only [lieTreeEval, LieHom.map_lie, hu, hv]

theorem lift_lieTreeEval (f : X → L) (t : FreeMagma X) :
    FreeLieAlgebra.lift ℚ f (lieTreeEval (FreeLieAlgebra.of ℚ) t) = lieTreeEval f t := by
  rw [map_lieTreeEval]
  simp only [FreeLieAlgebra.lift_of_apply]

theorem dynkinProjection_lift (f : X → L) (x : FreeLieAlgebra ℚ X) :
    dynkinProjection f (freeLieWordExpansion x) = FreeLieAlgebra.lift ℚ f x := by
  apply freeLie_linear_induction (fun x =>
    dynkinProjection f (freeLieWordExpansion x) = FreeLieAlgebra.lift ℚ f x)
  · simp
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro r x hx
    simp only [map_smul, hx]
  · intro t
    rw [freeLieWordExpansion_tree, dynkinProjection_commutatorTree, lift_lieTreeEval]

theorem rightBracketList_mem_lowerCentralSeries (f : X → L) (xs : List X)
    {n : ℕ} {z : L} (hz : z ∈ LieModule.lowerCentralSeries ℚ L L n) :
    rightBracketList f xs z ∈ LieModule.lowerCentralSeries ℚ L L (n + xs.length) := by
  induction xs generalizing n z with
  | nil => simpa only [rightBracketList_nil, Module.End.one_apply, List.length_nil, Nat.add_zero] using hz
  | cons x xs ih =>
    have hleft : ⁅f x, z⁆ ∈ LieModule.lowerCentralSeries ℚ L L (n + 1) := by
      rw [LieModule.lowerCentralSeries_succ]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) hz
    have hright : ⁅z, f x⁆ ∈ LieModule.lowerCentralSeries ℚ L L (n + 1) := by
      rw [← lie_skew z (f x)]
      exact (LieModule.lowerCentralSeries ℚ L L (n + 1)).neg_mem hleft
    have h := ih hright
    simpa only [rightBracketList_cons, Module.End.mul_apply, rightBracket_apply,
      List.length_cons, Nat.add_assoc, Nat.add_comm 1 xs.length] using h

theorem dynkinWord_mem_lowerCentralSeries (f : X → L) (w : FreeSemigroup X) :
    dynkinWord f w ∈ LieModule.lowerCentralSeries ℚ L L w.tail.length := by
  have h : f w.head ∈ LieModule.lowerCentralSeries ℚ L L 0 := by
    rw [LieModule.lowerCentralSeries_zero]
    exact LieSubmodule.mem_top _
  simpa only [dynkinWord, Nat.zero_add] using rightBracketList_mem_lowerCentralSeries f w.tail h

theorem dynkinWord_eq_zero_of_length_gt (f : X → L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) {w : FreeSemigroup X}
    (hw : s < w.length) : dynkinWord f w = 0 := by
  have hle : s ≤ w.tail.length := by change s < w.tail.length + 1 at hw; omega
  have h := LieModule.antitone_lowerCentralSeries ℚ L L hle
    (dynkinWord_mem_lowerCentralSeries f w)
  simpa only [hnil, LieSubmodule.mem_bot] using h

theorem dynkinProjection_eq_zero_of_low_coeff_zero (f : X → L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) {p : WordPolynomial X}
    (hp : ∀ w, w.length ≤ s → p.coeff w = 0) : dynkinProjection f p = 0 := by
  classical
  change p.coeff.sum (fun w r => r • ((w.length : ℚ)⁻¹ • dynkinWord f w)) = 0
  apply Finset.sum_eq_zero
  intro w hw
  have hgt : s < w.length := by
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hw) (hp w (Nat.le_of_not_gt hn))
  dsimp only
  rw [dynkinWord_eq_zero_of_length_gt f hnil hgt, smul_zero, smul_zero]

theorem dynkinProjection_eq_of_low_coeff_eq (f : X → L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) {p q : WordPolynomial X}
    (hpq : ∀ w, w.length ≤ s → p.coeff w = q.coeff w) :
    dynkinProjection f p = dynkinProjection f q := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply dynkinProjection_eq_zero_of_low_coeff_zero f hnil
  intro w hw
  change p.coeff w - q.coeff w = 0
  rw [hpq w hw, sub_self]

theorem lie_lift_eq_of_low_word_coeff_eq (f : X → L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) {p q : FreeLieAlgebra ℚ X}
    (hpq : ∀ w, w.length ≤ s →
      (freeLieWordExpansion p).coeff w = (freeLieWordExpansion q).coeff w) :
    FreeLieAlgebra.lift ℚ f p = FreeLieAlgebra.lift ℚ f q := by
  rw [← dynkinProjection_lift f p, ← dynkinProjection_lift f q]
  exact dynkinProjection_eq_of_low_coeff_eq f hnil hpq

end Erdos3

end

section

namespace Erdos3
open TensorProduct
variable {X : Type*}

noncomputable def freeCoproduct : FreeAlgebra ℚ X →ₐ[ℚ]
    FreeAlgebra ℚ X ⊗[ℚ] FreeAlgebra ℚ X :=
  FreeAlgebra.lift ℚ (fun x => FreeAlgebra.ι ℚ x ⊗ₜ[ℚ] 1 + 1 ⊗ₜ[ℚ] FreeAlgebra.ι ℚ x)

@[simp] theorem freeCoproduct_generator (x : X) :
    freeCoproduct (FreeAlgebra.ι ℚ x) =
      FreeAlgebra.ι ℚ x ⊗ₜ[ℚ] 1 + 1 ⊗ₜ[ℚ] FreeAlgebra.ι ℚ x :=
  FreeAlgebra.lift_ι_apply _ _

noncomputable def freeAugmentation : FreeAlgebra ℚ X →ₐ[ℚ] ℚ :=
  FreeAlgebra.lift ℚ (fun _ => 0)

@[simp] theorem freeAugmentation_generator (x : X) : freeAugmentation (FreeAlgebra.ι ℚ x) = 0 :=
  FreeAlgebra.lift_ι_apply _ _

noncomputable def freeAntipodeOp : FreeAlgebra ℚ X →ₐ[ℚ] (FreeAlgebra ℚ X)ᵐᵒᵖ :=
  FreeAlgebra.lift ℚ (fun x => MulOpposite.op (-FreeAlgebra.ι ℚ x))

noncomputable def freeAntipode : FreeAlgebra ℚ X →ₗ[ℚ] FreeAlgebra ℚ X :=
  (MulOpposite.opLinearEquiv ℚ).symm.toLinearMap.comp freeAntipodeOp.toLinearMap

@[simp] theorem freeAntipode_generator (x : X) : freeAntipode (FreeAlgebra.ι ℚ x) = -FreeAlgebra.ι ℚ x := by
  change MulOpposite.unop (freeAntipodeOp (FreeAlgebra.ι ℚ x)) = _
  rw [freeAntipodeOp, FreeAlgebra.lift_ι_apply]
  rfl

@[simp] theorem freeAntipode_one : freeAntipode (1 : FreeAlgebra ℚ X) = 1 := by
  change MulOpposite.unop (freeAntipodeOp 1) = 1
  rw [map_one, MulOpposite.unop_one]

theorem freeAntipode_mul (p q : FreeAlgebra ℚ X) :
    freeAntipode (p * q) = freeAntipode q * freeAntipode p := by
  change MulOpposite.unop (freeAntipodeOp (p * q)) = _
  rw [map_mul, MulOpposite.unop_mul]
  rfl

def FreePrimitive (p : FreeAlgebra ℚ X) : Prop :=
  freeCoproduct p = p ⊗ₜ[ℚ] 1 + 1 ⊗ₜ[ℚ] p

theorem freePrimitive_generator (x : X) : FreePrimitive (FreeAlgebra.ι ℚ x) :=
  freeCoproduct_generator x

theorem FreePrimitive.commutator {p q : FreeAlgebra ℚ X}
    (hp : FreePrimitive p) (hq : FreePrimitive q) : FreePrimitive (p * q - q * p) := by
  unfold FreePrimitive at hp hq ⊢
  simp only [map_sub, map_mul, hp, hq, add_mul, mul_add,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, sub_tmul, tmul_sub]
  abel

end Erdos3

end

section

namespace Erdos3
variable {X : Type*}

noncomputable def freeScaleSeries : FreeAlgebra ℚ X →ₐ[ℚ] PowerSeries (FreeAlgebra ℚ X) :=
  FreeAlgebra.lift ℚ (fun x => PowerSeries.monomial 1 (FreeAlgebra.ι ℚ x))

@[simp] theorem freeScaleSeries_generator (x : X) :
    freeScaleSeries (FreeAlgebra.ι ℚ x) = PowerSeries.monomial 1 (FreeAlgebra.ι ℚ x) :=
  FreeAlgebra.lift_ι_apply _ _

theorem freeScaleSeries_word (w : FreeMonoid X) :
    freeScaleSeries (freeWord w) = PowerSeries.monomial w.length (freeWord w) := by
  induction w using freeMonoid_induction_right with
  | h1 => simp
  | hstep w x hw =>
    rw [map_mul, map_mul, freeWord_of, hw, freeScaleSeries_generator,
      PowerSeries.monomial_mul_monomial]
    simp only [FreeMonoid.length_mul, FreeMonoid.length_of]

noncomputable def freeHomogeneousPart (n : ℕ) : FreeAlgebra ℚ X →ₗ[ℚ] FreeAlgebra ℚ X :=
  ((PowerSeries.coeff n).restrictScalars ℚ).comp freeScaleSeries.toLinearMap

theorem freeHomogeneousPart_apply (n : ℕ) (p : FreeAlgebra ℚ X) :
    freeHomogeneousPart n p = PowerSeries.coeff n (freeScaleSeries p) := rfl

@[simp] theorem freeHomogeneousPart_word (n : ℕ) (w : FreeMonoid X) :
    freeHomogeneousPart n (freeWord w) = if n = w.length then freeWord w else 0 := by
  rw [freeHomogeneousPart_apply, freeScaleSeries_word, PowerSeries.coeff_monomial]

noncomputable def freeTruncation (s : ℕ) : FreeAlgebra ℚ X →ₗ[ℚ] FreeAlgebra ℚ X :=
  ∑ n ∈ Finset.range (s + 1), freeHomogeneousPart n

theorem freeTruncation_apply (s : ℕ) (p : FreeAlgebra ℚ X) :
    freeTruncation s p = ∑ n ∈ Finset.range (s + 1), freeHomogeneousPart n p := by
  simp [freeTruncation]

@[simp] theorem freeTruncation_word (s : ℕ) (w : FreeMonoid X) :
    freeTruncation s (freeWord w) = if w.length ≤ s then freeWord w else 0 := by
  rw [freeTruncation_apply]
  simp only [freeHomogeneousPart_word]
  simp [Finset.sum_ite_eq']

theorem freeTruncation_idempotent (s : ℕ) (p : FreeAlgebra ℚ X) :
    freeTruncation s (freeTruncation s p) = freeTruncation s p := by
  apply freeAlgebra_linear_induction (fun p =>
    freeTruncation s (freeTruncation s p) = freeTruncation s p)
  · simp
  · intro p q hp hq
    simp only [map_add, hp, hq]
  · intro r p hp
    simp only [map_smul, hp]
  · intro w
    rw [freeTruncation_word]
    split_ifs with hw <;> simp [hw]

end Erdos3

end

section

namespace Erdos3

variable {X : Type*}

noncomputable def wordTruncation (s : ℕ) : WordPolynomial X →ₗ[ℚ] WordPolynomial X :=
  wordLinearMap (fun w => if w.length ≤ s then MonoidAlgebra.single w 1 else 0)

@[simp] theorem wordTruncation_single (s : ℕ) (w : FreeSemigroup X) (r : ℚ) :
    wordTruncation s (MonoidAlgebra.single w r) =
      if w.length ≤ s then MonoidAlgebra.single w r else 0 := by
  simp only [wordTruncation, wordLinearMap_single]
  split_ifs <;> simp

theorem wordTruncation_coeff (s : ℕ) (p : WordPolynomial X) (w : FreeSemigroup X) :
    (wordTruncation s p).coeff w = if w.length ≤ s then p.coeff w else 0 := by
  classical
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq =>
    simp only [map_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]
    split_ifs <;> simp
  | single u r =>
    rw [wordTruncation_single]
    by_cases he : u = w
    · subst u
      split_ifs <;> simp
    · split_ifs <;> simp [he]

theorem wordTruncation_eq_iff (s : ℕ) (p q : WordPolynomial X) :
    wordTruncation s p = wordTruncation s q ↔
      ∀ w, w.length ≤ s → p.coeff w = q.coeff w := by
  constructor
  · intro h w hw
    have he := congrArg (fun p : WordPolynomial X => p.coeff w) h
    simpa only [wordTruncation_coeff, hw, ite_true] using he
  · intro h
    ext w
    simp only [wordTruncation_coeff]
    split_ifs with hw
    · exact h w hw
    · rfl

section Lie
variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem dynkinProjection_wordTruncation (f : X → L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (p : WordPolynomial X) :
    dynkinProjection f (wordTruncation s p) = dynkinProjection f p := by
  apply dynkinProjection_eq_of_low_coeff_eq f hnil
  intro w hw
  simp only [wordTruncation_coeff, hw, ite_true]

theorem lie_lift_eq_of_wordTruncation_eq (f : X → L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) {p q : FreeLieAlgebra ℚ X}
    (h : wordTruncation s (freeLieWordExpansion p) = wordTruncation s (freeLieWordExpansion q)) :
    FreeLieAlgebra.lift ℚ f p = FreeLieAlgebra.lift ℚ f q :=
  lie_lift_eq_of_low_word_coeff_eq f hnil ((wordTruncation_eq_iff _ _ _).mp h)

end Lie
end Erdos3

end

section

namespace Erdos3
open TensorProduct
variable {X : Type*}
attribute [local instance] LieRing.ofAssociativeRing

noncomputable def freeAssociativeLieSubalgebra : LieSubalgebra ℚ (FreeAlgebra ℚ X) :=
  freeLieAssociativeExpansion.range

theorem freeAssociativeLieSubalgebra_generator (x : X) :
    FreeAlgebra.ι ℚ x ∈ freeAssociativeLieSubalgebra := by
  exact ⟨FreeLieAlgebra.of ℚ x, FreeLieAlgebra.lift_of_apply _ _⟩

noncomputable def freeAntipodeConvolution : FreeAlgebra ℚ X →ₗ[ℚ] FreeAlgebra ℚ X :=
  (tensorContract freeAntipode LinearMap.id).comp freeCoproduct.toLinearMap

noncomputable def freeDynkinConvolution : FreeAlgebra ℚ X →ₗ[ℚ] FreeAlgebra ℚ X :=
  (tensorContract freeAntipode freeDegree).comp freeCoproduct.toLinearMap

@[simp] theorem freeAntipodeConvolution_one :
    freeAntipodeConvolution (1 : FreeAlgebra ℚ X) = 1 := by
  simp [freeAntipodeConvolution, Algebra.TensorProduct.one_def]

@[simp] theorem freeDynkinConvolution_one :
    freeDynkinConvolution (1 : FreeAlgebra ℚ X) = 0 := by
  simp [freeDynkinConvolution, Algebra.TensorProduct.one_def]

theorem freeAntipodeConvolution_mul_generator (p : FreeAlgebra ℚ X) (x : X) :
    freeAntipodeConvolution (p * FreeAlgebra.ι ℚ x) =
      -FreeAlgebra.ι ℚ x * freeAntipodeConvolution p +
        freeAntipodeConvolution p * FreeAlgebra.ι ℚ x := by
  change tensorContract freeAntipode LinearMap.id (freeCoproduct (p * FreeAlgebra.ι ℚ x)) = _
  rw [map_mul, freeCoproduct_generator, mul_add, map_add,
    tensorContract_mul_left _ _ freeAntipode_mul, tensorContract_id_mul_right,
    freeAntipode_generator]
  rfl

theorem freeDynkinConvolution_mul_generator (p : FreeAlgebra ℚ X) (x : X) :
    freeDynkinConvolution (p * FreeAlgebra.ι ℚ x) =
      -FreeAlgebra.ι ℚ x * freeDynkinConvolution p +
        (freeDynkinConvolution p * FreeAlgebra.ι ℚ x +
          freeAntipodeConvolution p * FreeAlgebra.ι ℚ x) := by
  change tensorContract freeAntipode freeDegree (freeCoproduct (p * FreeAlgebra.ι ℚ x)) = _
  rw [map_mul, freeCoproduct_generator, mul_add, map_add,
    tensorContract_mul_left _ _ freeAntipode_mul,
    tensorContract_derivation_mul_right _ _ freeDegree_mul,
    freeAntipode_generator, freeDegree_generator]
  rfl

theorem freeAntipodeConvolution_eq_augmentation (p : FreeAlgebra ℚ X) :
    freeAntipodeConvolution p = freeAugmentation p • 1 := by
  apply freeAlgebra_linear_induction (fun p =>
    freeAntipodeConvolution p = freeAugmentation p • 1)
  · simp
  · intro p q hp hq
    simp only [map_add, hp, hq, add_smul]
  · intro r p hp
    simp only [map_smul, hp, smul_smul, smul_eq_mul]
  · intro w
    induction w using freeMonoid_induction_right with
    | h1 => simp
    | hstep w x hw =>
      rw [map_mul, freeWord_of, freeAntipodeConvolution_mul_generator, hw]
      simp

theorem freeDynkinConvolution_mem (p : FreeAlgebra ℚ X) :
    freeDynkinConvolution p ∈ freeAssociativeLieSubalgebra := by
  apply freeAlgebra_linear_induction (fun p =>
    freeDynkinConvolution p ∈ freeAssociativeLieSubalgebra)
  · simpa only [map_zero] using freeAssociativeLieSubalgebra.zero_mem
  · intro p q hp hq
    simpa only [map_add] using freeAssociativeLieSubalgebra.add_mem hp hq
  · intro r p hp
    simpa only [map_smul] using freeAssociativeLieSubalgebra.smul_mem r hp
  · intro w
    induction w using freeMonoid_induction_right with
    | h1 => simp [freeAssociativeLieSubalgebra.zero_mem]
    | hstep w x hw =>
      rw [map_mul, freeWord_of, freeDynkinConvolution_mul_generator,
        freeAntipodeConvolution_eq_augmentation]
      have hbr := freeAssociativeLieSubalgebra.lie_mem hw
        (freeAssociativeLieSubalgebra_generator x)
      have hsm := freeAssociativeLieSubalgebra.smul_mem (freeAugmentation (freeWord w))
        (freeAssociativeLieSubalgebra_generator x)
      convert freeAssociativeLieSubalgebra.add_mem hbr hsm using 1
      change -FreeAlgebra.ι ℚ x * freeDynkinConvolution (freeWord w) +
          (freeDynkinConvolution (freeWord w) * FreeAlgebra.ι ℚ x +
            (freeAugmentation (freeWord w) • 1) * FreeAlgebra.ι ℚ x) =
        (freeDynkinConvolution (freeWord w) * FreeAlgebra.ι ℚ x -
          FreeAlgebra.ι ℚ x * freeDynkinConvolution (freeWord w)) +
            freeAugmentation (freeWord w) • FreeAlgebra.ι ℚ x
      rw [smul_mul_assoc, one_mul, neg_mul]
      abel

theorem FreePrimitive.dynkin_eq_degree {p : FreeAlgebra ℚ X} (hp : FreePrimitive p) :
    freeDynkinConvolution p = freeDegree p := by
  change tensorContract freeAntipode freeDegree (freeCoproduct p) = _
  rw [hp, map_add]
  simp

end Erdos3

end

section

namespace Erdos3
open TensorProduct
variable {X : Type*}
attribute [local instance] LieRing.ofAssociativeRing

theorem freeAugmentation_antipode (p : FreeAlgebra ℚ X) :
    freeAugmentation (freeAntipode p) = freeAugmentation p := by
  apply freeAlgebra_linear_induction (fun p =>
    freeAugmentation (freeAntipode p) = freeAugmentation p)
  · simp
  · intro p q hp hq
    simp only [map_add, hp, hq]
  · intro r p hp
    simp only [map_smul, hp]
  · intro w
    induction w using freeMonoid_induction_right with
    | h1 => simp
    | hstep w x _ => simp [freeAntipode_mul]

theorem FreePrimitive.augmentation_eq_zero {p : FreeAlgebra ℚ X} (hp : FreePrimitive p) :
    freeAugmentation p = 0 := by
  have hc : freeAntipode p + p = freeAugmentation p • 1 := by
    rw [← freeAntipodeConvolution_eq_augmentation]
    change _ = tensorContract freeAntipode LinearMap.id (freeCoproduct p)
    rw [hp, map_add]
    simp
  have h := congrArg freeAugmentation hc
  simp only [map_add, freeAugmentation_antipode, map_smul, map_one, smul_eq_mul, mul_one] at h
  linarith

noncomputable def freeDegreeInverse : FreeAlgebra ℚ X →ₗ[ℚ] FreeAlgebra ℚ X :=
  freeWordLinearMap (fun w => (w.length : ℚ)⁻¹ • freeWord w)

@[simp] theorem freeDegreeInverse_word (w : FreeMonoid X) :
    freeDegreeInverse (freeWord w) = (w.length : ℚ)⁻¹ • freeWord w :=
  freeWordLinearMap_word _ _

theorem freeAugmentation_word_of_ne_one {w : FreeMonoid X} (hw : w ≠ 1) :
    freeAugmentation (freeWord w) = 0 := by
  induction w using FreeMonoid.inductionOn' with
  | one => exact (hw rfl).elim
  | of_mul x w _ => simp

theorem freeDegreeInverse_degree (p : FreeAlgebra ℚ X) :
    freeDegreeInverse (freeDegree p) = p - freeAugmentation p • 1 := by
  apply freeAlgebra_linear_induction (fun p =>
    freeDegreeInverse (freeDegree p) = p - freeAugmentation p • 1)
  · simp
  · intro p q hp hq
    simp only [map_add, hp, hq, add_smul]
    abel
  · intro r p hp
    simp only [map_smul, hp, smul_sub, smul_smul, smul_eq_mul]
  · intro w
    by_cases hw : w = 1
    · subst w
      simp
    · rw [freeDegree_word, map_smul, freeDegreeInverse_word, smul_smul,
        mul_inv_cancel₀ (show (w.length : ℚ) ≠ 0 by
          exact_mod_cast (FreeMonoid.length_eq_zero.not.mpr hw)), one_smul,
        freeAugmentation_word_of_ne_one hw, zero_smul, sub_zero]

theorem freeDegree_lieTree (t : FreeMagma X) :
    freeDegree (lieTreeEval (FreeAlgebra.ι ℚ) t) =
      (t.length : ℚ) • lieTreeEval (FreeAlgebra.ι ℚ) t := by
  induction t using FreeMagma.rec with
  | of x => simp [lieTreeEval]
  | mul u v hu hv =>
    change freeDegree (lieTreeEval (FreeAlgebra.ι ℚ) u * lieTreeEval (FreeAlgebra.ι ℚ) v -
        lieTreeEval (FreeAlgebra.ι ℚ) v * lieTreeEval (FreeAlgebra.ι ℚ) u) = _
    rw [map_sub, freeDegree_mul, freeDegree_mul, hu, hv]
    change _ = ((u.length + v.length : ℕ) : ℚ) •
      (lieTreeEval (FreeAlgebra.ι ℚ) u * lieTreeEval (FreeAlgebra.ι ℚ) v -
        lieTreeEval (FreeAlgebra.ι ℚ) v * lieTreeEval (FreeAlgebra.ι ℚ) u)
    simp only [Nat.cast_add, add_smul, smul_sub, smul_mul_assoc, mul_smul_comm]
    abel

theorem freePrimitive_lieTree (t : FreeMagma X) :
    FreePrimitive (lieTreeEval (FreeAlgebra.ι ℚ) t) := by
  induction t using FreeMagma.rec with
  | of x => exact freePrimitive_generator x
  | mul u v hu hv => exact hu.commutator hv

theorem freeDegreeInverse_lieTree (t : FreeMagma X) :
    freeDegreeInverse (lieTreeEval (FreeAlgebra.ι ℚ) t) =
      (t.length : ℚ)⁻¹ • lieTreeEval (FreeAlgebra.ι ℚ) t := by
  have h := freeDegreeInverse_degree (lieTreeEval (FreeAlgebra.ι ℚ) t)
  rw [freeDegree_lieTree, map_smul, (freePrimitive_lieTree t).augmentation_eq_zero,
    zero_smul, sub_zero] at h
  have hlen : (t.length : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt t.length_pos)
  have hs := congrArg (fun z : FreeAlgebra ℚ X => (t.length : ℚ)⁻¹ • z) h
  simpa only [smul_smul, inv_mul_cancel₀ hlen, one_smul] using hs

theorem freeDegreeInverse_mem {p : FreeAlgebra ℚ X} (hp : p ∈ freeAssociativeLieSubalgebra) :
    freeDegreeInverse p ∈ freeAssociativeLieSubalgebra := by
  obtain ⟨l, rfl⟩ := hp
  apply freeLie_linear_induction (fun l =>
    freeDegreeInverse (freeLieAssociativeExpansion l) ∈ freeAssociativeLieSubalgebra)
  · simpa only [map_zero] using freeAssociativeLieSubalgebra.zero_mem
  · intro l m hl hm
    simpa only [map_add] using freeAssociativeLieSubalgebra.add_mem hl hm
  · intro r l hl
    simpa only [map_smul] using freeAssociativeLieSubalgebra.smul_mem r hl
  · intro t
    change freeDegreeInverse (FreeLieAlgebra.lift ℚ (FreeAlgebra.ι ℚ)
      (lieTreeEval (FreeLieAlgebra.of ℚ) t)) ∈ _
    rw [lift_lieTreeEval, freeDegreeInverse_lieTree]
    apply freeAssociativeLieSubalgebra.smul_mem
    exact ⟨lieTreeEval (FreeLieAlgebra.of ℚ) t, lift_lieTreeEval _ _⟩

theorem FreePrimitive.mem {p : FreeAlgebra ℚ X} (hp : FreePrimitive p) :
    p ∈ freeAssociativeLieSubalgebra := by
  have hm := freeDegreeInverse_mem (freeDynkinConvolution_mem p)
  rw [hp.dynkin_eq_degree, freeDegreeInverse_degree, hp.augmentation_eq_zero,
    zero_smul, sub_zero] at hm
  exact hm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.LieWordProjection
namespace OAI

section

namespace Erdos3

variable {X : Type*}

noncomputable def lieWordSubalgebra : LieSubalgebra ℚ (WordPolynomial X) :=
  LieSubalgebra.lieSpan ℚ (WordPolynomial X)
    (Set.range (fun x : X => MonoidAlgebra.single (FreeSemigroup.of x) (1 : ℚ)))

theorem commutatorTree_mem_lieWordSubalgebra (t : FreeMagma X) :
    commutatorTree t ∈ lieWordSubalgebra := by
  induction t using FreeMagma.rec with
  | of x => exact LieSubalgebra.subset_lieSpan ⟨x, rfl⟩
  | mul u v hu hv => exact lieWordSubalgebra.lie_mem hu hv

theorem freeLieWordExpansion_range :
    (freeLieWordExpansion (X := X)).range = lieWordSubalgebra := by
  apply le_antisymm
  · intro p hp
    obtain ⟨x, rfl⟩ := (LieHom.mem_range _ _).mp hp
    apply freeLie_linear_induction (fun x => freeLieWordExpansion x ∈ lieWordSubalgebra)
    · simpa only [map_zero] using lieWordSubalgebra.zero_mem
    · intro x y hx hy
      rw [map_add]
      exact lieWordSubalgebra.add_mem hx hy
    · intro r x hx
      rw [map_smul]
      exact lieWordSubalgebra.smul_mem r hx
    · intro t
      rw [freeLieWordExpansion_tree]
      exact commutatorTree_mem_lieWordSubalgebra t
  · apply LieSubalgebra.lieSpan_le.mpr
    rintro p ⟨x, rfl⟩
    exact (LieHom.mem_range _ _).mpr ⟨FreeLieAlgebra.of ℚ x, freeLieWordExpansion_of x⟩

noncomputable def lieWordProjection : WordPolynomial X →ₗ[ℚ] WordPolynomial X :=
  freeLieWordExpansion.toLinearMap.comp (dynkinProjection (FreeLieAlgebra.of ℚ))

@[simp] theorem lieWordProjection_apply (p : WordPolynomial X) :
    lieWordProjection p = freeLieWordExpansion (dynkinProjection (FreeLieAlgebra.of ℚ) p) := rfl

theorem lieWordProjection_eq_self_iff (p : WordPolynomial X) :
    lieWordProjection p = p ↔ p ∈ lieWordSubalgebra := by
  rw [← freeLieWordExpansion_range]
  constructor
  · intro h
    exact (LieHom.mem_range _ _).mpr ⟨dynkinProjection (FreeLieAlgebra.of ℚ) p, h⟩
  · intro h
    obtain ⟨x, rfl⟩ := (LieHom.mem_range _ _).mp h
    simp only [lieWordProjection_apply, dynkinProjection_freeLieWordExpansion]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreeLieTreeCoefficientBounds
namespace OAI

section

namespace Erdos3
variable {X : Type*}
attribute [local instance] LieRing.ofAssociativeRing

theorem wordPolynomialEmbedding_single (w : FreeSemigroup X) (r : ℚ) :
    wordPolynomialEmbedding (MonoidAlgebra.single w r) = r • freeWord w.toFreeMonoid := by
  change FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
    (MonoidAlgebra.mapDomain FreeSemigroup.toFreeMonoid (MonoidAlgebra.single w r)) = _
  rw [MonoidAlgebra.mapDomain_single, freeWord_single_symm]

theorem freeSemigroup_toFreeMonoid_length (w : FreeSemigroup X) :
    w.toFreeMonoid.length = w.length := by
  cases w
  rw [FreeSemigroup.toFreeMonoid_mk_eq_cons]
  rfl

theorem wordPolynomialEmbedding_truncation (s : ℕ) (p : WordPolynomial X) :
    wordPolynomialEmbedding (wordTruncation s p) = freeTruncation s (wordPolynomialEmbedding p) := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single w r =>
    rw [wordTruncation_single, wordPolynomialEmbedding_single, map_smul, freeTruncation_word,
      freeSemigroup_toFreeMonoid_length]
    split_ifs <;> simp [wordPolynomialEmbedding_single]

theorem wordPolynomialEmbedding_freeLieExpansion (p : FreeLieAlgebra ℚ X) :
    wordPolynomialEmbedding (freeLieWordExpansion p) = freeLieAssociativeExpansion p :=
  DFunLike.congr_fun wordPolynomialEmbedding_comp_freeLie p

theorem lie_lift_eq_of_freeTruncation_eq {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (f : X → L) {s : ℕ} (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    {p q : FreeLieAlgebra ℚ X}
    (h : freeTruncation s (freeLieAssociativeExpansion p) =
      freeTruncation s (freeLieAssociativeExpansion q)) :
    FreeLieAlgebra.lift ℚ f p = FreeLieAlgebra.lift ℚ f q := by
  apply lie_lift_eq_of_wordTruncation_eq f hnil
  apply wordPolynomialEmbedding_injective
  rw [wordPolynomialEmbedding_truncation, wordPolynomialEmbedding_truncation,
    wordPolynomialEmbedding_freeLieExpansion, wordPolynomialEmbedding_freeLieExpansion]
  exact h

theorem freeTruncation_eq_of_scaled_series_eq {s : ℕ} {p q : FreeAlgebra ℚ X}
    (h : truncatedSeriesMk s (freeScaleSeries p) = truncatedSeriesMk s (freeScaleSeries q)) :
    freeTruncation s p = freeTruncation s q := by
  rw [freeTruncation_apply, freeTruncation_apply]
  apply Finset.sum_congr rfl
  intro n hn
  exact (truncatedSeriesMk_eq_iff s _ _).mp h n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))

theorem lie_lift_eq_of_scaled_series_eq {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (f : X → L) {s : ℕ} (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    {p q : FreeLieAlgebra ℚ X}
    (h : truncatedSeriesMk s (freeScaleSeries (freeLieAssociativeExpansion p)) =
      truncatedSeriesMk s (freeScaleSeries (freeLieAssociativeExpansion q))) :
    FreeLieAlgebra.lift ℚ f p = FreeLieAlgebra.lift ℚ f q :=
  lie_lift_eq_of_freeTruncation_eq f hnil (freeTruncation_eq_of_scaled_series_eq h)

end Erdos3

end

section

namespace Erdos3

variable {X : Type*}

noncomputable def freeWordCoefficients : FreeAlgebra ℚ X →ₗ[ℚ] (FreeMonoid X →₀ ℚ) :=
  (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap.comp
    FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearMap

theorem freeWordCoefficients_word (w : FreeMonoid X) :
    freeWordCoefficients (freeWord w) = Finsupp.single w 1 := by
  change (FreeAlgebra.equivMonoidAlgebraFreeMonoid (freeWord w)).coeff = _
  rw [freeWord_coeff]
  rfl

theorem freeWordCoefficients_truncation (s : ℕ) (p : FreeAlgebra ℚ X) (w : FreeMonoid X) :
    freeWordCoefficients (freeTruncation s p) w =
      if w.length ≤ s then freeWordCoefficients p w else 0 := by
  classical
  apply freeAlgebra_linear_induction (fun p =>
    freeWordCoefficients (freeTruncation s p) w =
      if w.length ≤ s then freeWordCoefficients p w else 0)
  · simp
  · intro p q hp hq
    simp only [map_add, Finsupp.add_apply, hp, hq]
    split_ifs <;> simp
  · intro r p hp
    simp only [map_smul, Finsupp.smul_apply, hp]
    split_ifs <;> simp
  · intro v
    rw [freeTruncation_word]
    by_cases hv : v = w
    · subst v
      split_ifs <;> simp
    · split_ifs <;> simp [freeWordCoefficients_word, hv]

theorem freeWordCoefficients_embedding (p : WordPolynomial X) (w : FreeSemigroup X) :
    freeWordCoefficients (wordPolynomialEmbedding p) w.toFreeMonoid = p.coeff w := by
  change (FreeAlgebra.equivMonoidAlgebraFreeMonoid
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
      (MonoidAlgebra.mapDomain FreeSemigroup.toFreeMonoid p))).coeff w.toFreeMonoid = _
  rw [AlgEquiv.apply_symm_apply]
  exact Finsupp.mapDomain_apply FreeSemigroup.toFreeMonoid_injective p.coeff w

end Erdos3

end

section

namespace Erdos3

variable {X : Type*}

theorem wordTruncation_homogeneous (s : ℕ) {n : ℕ} {p : WordPolynomial X}
    (hp : WordHomogeneous n p) :
    wordTruncation s p = if n ≤ s then p else 0 := by
  classical
  ext w
  rw [wordTruncation_coeff]
  by_cases hw : p.coeff w = 0
  · simp only [hw]
    split_ifs <;> simp [hw]
  · rw [hp w hw]
    split_ifs <;> rfl

theorem wordTruncation_freeLie_mem (s : ℕ) (p : FreeLieAlgebra ℚ X) :
    wordTruncation s (freeLieWordExpansion p) ∈ lieWordSubalgebra := by
  apply freeLie_linear_induction (fun p =>
    wordTruncation s (freeLieWordExpansion p) ∈ lieWordSubalgebra)
  · simpa only [map_zero] using lieWordSubalgebra.zero_mem
  · intro p q hp hq
    rw [map_add, map_add]
    exact lieWordSubalgebra.add_mem hp hq
  · intro r p hp
    rw [map_smul, map_smul]
    exact lieWordSubalgebra.smul_mem r hp
  · intro t
    rw [freeLieWordExpansion_tree, wordTruncation_homogeneous s (commutatorTree_homogeneous t)]
    split_ifs
    · exact commutatorTree_mem_lieWordSubalgebra t
    · exact lieWordSubalgebra.zero_mem

noncomputable def freeLieTruncation (s : ℕ) : FreeLieAlgebra ℚ X →ₗ[ℚ] FreeLieAlgebra ℚ X :=
  (dynkinProjection (FreeLieAlgebra.of ℚ)).comp
    ((wordTruncation s).comp freeLieWordExpansion.toLinearMap)

theorem freeLieTruncation_expansion (s : ℕ) (p : FreeLieAlgebra ℚ X) :
    freeLieWordExpansion (freeLieTruncation s p) = wordTruncation s (freeLieWordExpansion p) :=
  (lieWordProjection_eq_self_iff _).mpr (wordTruncation_freeLie_mem s p)

theorem freeLieTruncation_associativeExpansion (s : ℕ) (p : FreeLieAlgebra ℚ X) :
    freeLieAssociativeExpansion (freeLieTruncation s p) =
      freeTruncation s (freeLieAssociativeExpansion p) := by
  rw [← wordPolynomialEmbedding_freeLieExpansion, freeLieTruncation_expansion,
    wordPolynomialEmbedding_truncation, wordPolynomialEmbedding_freeLieExpansion]

theorem freeLieTruncation_support_length (s : ℕ) (p : FreeLieAlgebra ℚ X)
    {w : FreeSemigroup X} (hw : w ∈ (freeLieWordExpansion (freeLieTruncation s p)).coeff.support) :
    w.length ≤ s := by
  have h := Finsupp.mem_support_iff.mp hw
  rw [freeLieTruncation_expansion, wordTruncation_coeff] at h
  by_contra hlen
  exact h (if_neg hlen)

theorem lift_freeLieTruncation {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (f : X → L) {s : ℕ} (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (p : FreeLieAlgebra ℚ X) :
    FreeLieAlgebra.lift ℚ f (freeLieTruncation s p) = FreeLieAlgebra.lift ℚ f p := by
  rw [← dynkinProjection_lift, freeLieTruncation_expansion,
    dynkinProjection_wordTruncation f hnil, dynkinProjection_lift]

end Erdos3

end

section

namespace Erdos3

variable {X : Type*}

noncomputable def freeWordSplits (w : FreeMonoid X) : Finset (FreeMonoid X × FreeMonoid X) := by
  classical
  exact (Finset.range (w.length + 1)).image (fun n =>
    (FreeMonoid.ofList (w.toList.take n), FreeMonoid.ofList (w.toList.drop n)))

theorem mem_freeWordSplits (w u v : FreeMonoid X) :
    (u, v) ∈ freeWordSplits w ↔ u * v = w := by
  classical
  unfold freeWordSplits
  constructor
  · intro h
    obtain ⟨n, _, hnv⟩ := Finset.mem_image.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hnv
    change FreeMonoid.ofList (w.toList.take n ++ w.toList.drop n) = w
    rw [List.take_append_drop]
    rfl
  · intro h
    subst w
    apply Finset.mem_image.mpr
    refine ⟨u.length, Finset.mem_range.mpr ?_, ?_⟩
    · rw [FreeMonoid.length_mul]
      omega
    · change (FreeMonoid.ofList ((u.toList ++ v.toList).take u.toList.length),
        FreeMonoid.ofList ((u.toList ++ v.toList).drop u.toList.length)) = (u, v)
      simp only [List.take_left, List.drop_left]
      rfl

theorem freeWordSplits_card_le (w : FreeMonoid X) : (freeWordSplits w).card ≤ w.length + 1 := by
  classical
  unfold freeWordSplits
  exact (Finset.card_image_le).trans_eq (Finset.card_range _)

theorem freeWordCoefficients_mul (p q : FreeAlgebra ℚ X) (w : FreeMonoid X) :
    freeWordCoefficients (p * q) w =
      ∑ uv ∈ freeWordSplits w, freeWordCoefficients p uv.1 * freeWordCoefficients q uv.2 := by
  change (FreeAlgebra.equivMonoidAlgebraFreeMonoid (p * q)).coeff w = _
  rw [map_mul]
  exact MonoidAlgebra.coeff_mul_antidiag _ _ _ _ (fun {uv} => mem_freeWordSplits w uv.1 uv.2)

end Erdos3

end

section

namespace Erdos3

variable {X : Type*}

def FreeCoefficientBound (s D M : ℕ) (p : FreeAlgebra ℚ X) : Prop :=
  ∀ w, w.length ≤ s → ∃ a : ℤ,
    (a : ℚ) = (D : ℚ) * freeWordCoefficients p w ∧ a.natAbs ≤ M

namespace FreeCoefficientBound

variable {s D E M N : ℕ} {p q : FreeAlgebra ℚ X}

theorem mono (hp : FreeCoefficientBound s D M p) (hMN : M ≤ N) :
    FreeCoefficientBound s D N p := by
  intro w hw
  obtain ⟨a, ha, hb⟩ := hp w hw
  exact ⟨a, ha, hb.trans hMN⟩

theorem zero (s D M : ℕ) : FreeCoefficientBound (X := X) s D M 0 := by
  intro w _
  refine ⟨0, ?_, Nat.zero_le _⟩
  simp

theorem word (s : ℕ) (w : FreeMonoid X) : FreeCoefficientBound s 1 1 (freeWord w) := by
  classical
  intro v _
  by_cases hv : w = v
  · refine ⟨1, ?_, by simp⟩
    simp [freeWordCoefficients_word, hv]
  · refine ⟨0, ?_, by simp⟩
    simp [freeWordCoefficients_word, hv]

theorem one (s : ℕ) : FreeCoefficientBound (X := X) s 1 1 1 := by
  simpa only [map_one] using word s (1 : FreeMonoid X)

theorem neg (hp : FreeCoefficientBound s D M p) : FreeCoefficientBound s D M (-p) := by
  intro w hw
  obtain ⟨a, ha, hb⟩ := hp w hw
  refine ⟨-a, ?_, by simpa using hb⟩
  simp only [Int.cast_neg, map_neg, Finsupp.neg_apply, mul_neg, ha]

theorem add_same (hp : FreeCoefficientBound s D M p) (hq : FreeCoefficientBound s D N q) :
    FreeCoefficientBound s D (M + N) (p + q) := by
  intro w hw
  obtain ⟨a, ha, hb⟩ := hp w hw
  obtain ⟨b, he, hf⟩ := hq w hw
  refine ⟨a + b, ?_, (Int.natAbs_add_le _ _).trans (Nat.add_le_add hb hf)⟩
  simp only [Int.cast_add, map_add, Finsupp.add_apply, mul_add, ha, he]

theorem enlarge_denominator (hp : FreeCoefficientBound s D M p) (E : ℕ) :
    FreeCoefficientBound s (E * D) (E * M) p := by
  intro w hw
  obtain ⟨a, ha, hb⟩ := hp w hw
  refine ⟨(E : ℤ) * a, ?_, ?_⟩
  · push_cast
    rw [ha, mul_assoc]
  · simpa only [Int.natAbs_mul, Int.natAbs_natCast] using Nat.mul_le_mul_left E hb

theorem smul {r : ℚ} {a : ℤ} (hp : FreeCoefficientBound s D M p)
    (ha : (a : ℚ) = (E : ℚ) * r) (hbound : a.natAbs ≤ N) :
    FreeCoefficientBound s (E * D) (N * M) (r • p) := by
  intro w hw
  obtain ⟨b, hb, hbM⟩ := hp w hw
  refine ⟨a * b, ?_, ?_⟩
  · simp only [Int.cast_mul, Nat.cast_mul, map_smul, Finsupp.smul_apply, smul_eq_mul, ha, hb]
    ring
  · simpa only [Int.natAbs_mul] using Nat.mul_le_mul hbound hbM

theorem mul (hp : FreeCoefficientBound s D M p) (hq : FreeCoefficientBound s E N q) :
    FreeCoefficientBound s (D * E) ((s + 1) * M * N) (p * q) := by
  classical
  intro w hw
  have hlen : ∀ uv ∈ freeWordSplits w, uv.1.length ≤ s ∧ uv.2.length ≤ s := by
    intro uv huv
    have hmul := (mem_freeWordSplits w uv.1 uv.2).mp huv
    have h := congrArg FreeMonoid.length hmul
    rw [FreeMonoid.length_mul] at h
    omega
  choose a ha haM using fun uv : freeWordSplits w => hp uv.val.1 (hlen uv uv.property).1
  choose b hb hbN using fun uv : freeWordSplits w => hq uv.val.2 (hlen uv uv.property).2
  refine ⟨∑ uv, a uv * b uv, ?_, ?_⟩
  · push_cast
    simp_rw [ha, hb]
    rw [freeWordCoefficients_mul, Finset.mul_sum]
    conv_rhs => rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro uv _
    ring
  · calc
      _ ≤ ∑ uv, (a uv * b uv).natAbs := Int.natAbs_sum_le _ _
      _ ≤ ∑ _uv : freeWordSplits w, M * N := by
        apply Finset.sum_le_sum
        intro uv _
        simpa only [Int.natAbs_mul] using Nat.mul_le_mul (haM uv) (hbN uv)
      _ = (freeWordSplits w).card * (M * N) := by simp
      _ ≤ (s + 1) * (M * N) := Nat.mul_le_mul_right _
        ((freeWordSplits_card_le w).trans (Nat.add_le_add_right hw 1))
      _ = _ := by ring

theorem pow (hp : FreeCoefficientBound s D M p) (n : ℕ) :
    FreeCoefficientBound s (D ^ n) (((s + 1) * M) ^ n) (p ^ n) := by
  induction n with
  | zero => simpa using one s
  | succ n ih =>
    simpa only [pow_succ, mul_assoc, Nat.mul_left_comm] using ih.mul hp

theorem sum_finset {ι : Type*} (t : Finset ι) (f : ι → FreeAlgebra ℚ X)
    (hf : ∀ i ∈ t, FreeCoefficientBound s D M (f i)) :
    FreeCoefficientBound s D (t.card * M) (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using zero s D 0
  | @insert i t hi ih =>
    have h := (hf i (Finset.mem_insert_self _ _)).add_same
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi, Finset.card_insert_of_notMem hi,
      Nat.add_mul, one_mul, Nat.add_comm] using h

theorem list_prod (f : List (FreeAlgebra ℚ X)) (hf : ∀ p ∈ f, FreeCoefficientBound s D M p) :
    FreeCoefficientBound s (D ^ f.length) (((s + 1) * M) ^ f.length) f.prod := by
  induction f with
  | nil => simpa using one s
  | cons p ps ih =>
    have h := (hf p List.mem_cons_self).mul (ih (fun q hq => hf q (List.mem_cons_of_mem p hq)))
    simpa only [List.prod_cons, List.length_cons, pow_succ', mul_assoc] using h

theorem rationalHeight (hp : FreeCoefficientBound s D M p) (hD : 0 < D)
    (w : FreeMonoid X) (hw : w.length ≤ s) :
    RationalHeightLE (freeWordCoefficients p w) (max D M) := by
  obtain ⟨a, ha, hb⟩ := hp w hw
  have heq : freeWordCoefficients p w = (a : ℚ) / (D : ℤ) := by
    apply (eq_div_iff (by exact_mod_cast hD.ne')).mpr
    simpa only [Int.cast_natCast, mul_comm] using ha.symm
  rw [heq]
  apply rationalHeightLE_fraction a (D : ℤ) (by exact_mod_cast hD.ne')
  · exact hb.trans (le_max_right _ _)
  · simpa only [Int.natAbs_natCast] using le_max_left D M

end FreeCoefficientBound

end Erdos3

end

section

namespace Erdos3

variable {X : Type*}

theorem commutatorTree_coefficient_bound (s : ℕ) (a : FreeMagma X) :
    FreeCoefficientBound s 1 ((2 * (s + 1)) ^ (a.length - 1))
      (wordPolynomialEmbedding (commutatorTree a)) := by
  induction a using FreeMagma.rec with
  | of x =>
    simpa only [commutatorTree, wordPolynomialEmbedding_generator, freeWord_of,
      FreeMagma.length, Nat.sub_self, pow_zero] using
      FreeCoefficientBound.word s (FreeMonoid.of x)
  | mul a b ha hb =>
    have h := (ha.mul hb).add_same (hb.mul ha).neg
    have he : (s + 1) * (2 * (s + 1)) ^ (a.length - 1) * (2 * (s + 1)) ^ (b.length - 1) +
        (s + 1) * (2 * (s + 1)) ^ (b.length - 1) * (2 * (s + 1)) ^ (a.length - 1) =
        (2 * (s + 1)) ^ ((a * b).length - 1) := by
      have ha0 := a.length_pos
      have hb0 := b.length_pos
      rw [show (a * b).length - 1 = (a.length - 1) + (b.length - 1) + 1 by
        change a.length + b.length - 1 = _; omega, pow_succ, pow_add]
      ring
    simpa only [commutatorTree, FreeMagma.length, map_sub, map_add, map_neg, map_mul,
      one_mul, sub_eq_add_neg, he] using h

theorem commutatorTree_coefficient_height (s : ℕ) (a : FreeMagma X)
    (w : FreeSemigroup X) (hw : w.length ≤ s) :
    RationalHeightLE ((commutatorTree a).coeff w) ((2 * (s + 1)) ^ (a.length - 1)) := by
  have h := (commutatorTree_coefficient_bound s a).rationalHeight (by omega)
    w.toFreeMonoid (by simpa only [freeSemigroup_toFreeMonoid_length] using hw)
  have hpow : 1 ≤ (2 * (s + 1)) ^ (a.length - 1) := one_le_pow₀ (by omega)
  simpa only [freeWordCoefficients_embedding, max_eq_right hpow] using h

theorem commutatorTree_coefficient_integral (s : ℕ) (a : FreeMagma X)
    (w : FreeSemigroup X) (hw : w.length ≤ s) :
    ∃ z : ℤ, (z : ℚ) = (commutatorTree a).coeff w ∧ z.natAbs ≤ (2 * (s + 1)) ^ (a.length - 1) := by
  obtain ⟨z, hz, hbound⟩ := commutatorTree_coefficient_bound s a w.toFreeMonoid
    (by simpa only [freeSemigroup_toFreeMonoid_length] using hw)
  exact ⟨z, by simpa only [Nat.cast_one, one_mul, freeWordCoefficients_embedding] using hz, hbound⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolynomialEvaluationMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def realPolynomialMass {I : Type*} (p : MvPolynomial I ℝ) : ℝ :=
  ∑ m ∈ p.support, |p.coeff m|

theorem realPolynomialMass_nonneg {I : Type*} (p : MvPolynomial I ℝ) : 0 ≤ realPolynomialMass p :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem realPolynomialMass_zero {I : Type*} : realPolynomialMass (0 : MvPolynomial I ℝ) = 0 := by
  simp [realPolynomialMass]

theorem realPolynomialMass_monomial {I : Type*} (m : I →₀ ℕ) (c : ℝ) :
    realPolynomialMass (MvPolynomial.monomial m c) = |c| := by
  classical
  by_cases hc : c = 0 <;> simp [realPolynomialMass, MvPolynomial.support_monomial, hc]

theorem realPolynomialMass_C {I : Type*} (c : ℝ) :
    realPolynomialMass (MvPolynomial.C c : MvPolynomial I ℝ) = |c| :=
  realPolynomialMass_monomial 0 c

theorem realPolynomialMass_X {I : Type*} (i : I) :
    realPolynomialMass (MvPolynomial.X i : MvPolynomial I ℝ) = 1 := by
  simpa only [MvPolynomial.X, abs_one] using realPolynomialMass_monomial (Finsupp.single i 1) 1

theorem realPolynomialMass_one {I : Type*} : realPolynomialMass (1 : MvPolynomial I ℝ) = 1 := by
  simpa only [map_one, abs_one] using (realPolynomialMass_C (I := I) 1)

theorem realPolynomialMass_eq_sum_of_support_subset {I : Type*}
    (p : MvPolynomial I ℝ) (s : Finset (I →₀ ℕ)) (hs : p.support ⊆ s) :
    realPolynomialMass p = ∑ m ∈ s, |p.coeff m| := by
  classical
  apply Finset.sum_subset hs
  intro m _ hm
  rw [MvPolynomial.notMem_support_iff.mp hm, abs_zero]

theorem realPolynomialMass_coeff_le {I : Type*} (p : MvPolynomial I ℝ) (m : I →₀ ℕ) :
    |p.coeff m| ≤ realPolynomialMass p := by
  classical
  by_cases hm : m ∈ p.support
  · exact Finset.single_le_sum (fun n _ => abs_nonneg (p.coeff n)) hm
  · rw [MvPolynomial.notMem_support_iff.mp hm, abs_zero]
    exact realPolynomialMass_nonneg p

theorem realPolynomialMass_add_le {I : Type*} (p q : MvPolynomial I ℝ) :
    realPolynomialMass (p + q) ≤ realPolynomialMass p + realPolynomialMass q := by
  classical
  rw [realPolynomialMass_eq_sum_of_support_subset (p + q) (p.support ∪ q.support)
    (MvPolynomial.support_add),
    realPolynomialMass_eq_sum_of_support_subset p (p.support ∪ q.support) Finset.subset_union_left,
    realPolynomialMass_eq_sum_of_support_subset q (p.support ∪ q.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun monomial _ => by
    simpa only [MvPolynomial.coeff_add] using
      abs_add_le (p.coeff monomial) (q.coeff monomial))

theorem realPolynomialMass_sum_le {I J : Type*} (s : Finset J) (p : J → MvPolynomial I ℝ) :
    realPolynomialMass (∑ j ∈ s, p j) ≤ ∑ j ∈ s, realPolynomialMass (p j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, realPolynomialMass_zero, le_refl]
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (realPolynomialMass_add_le _ _).trans (add_le_add le_rfl ih)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem realPolynomialMass_mul_le {I : Type*} (p q : MvPolynomial I ℝ) :
    realPolynomialMass (p * q) ≤ realPolynomialMass p * realPolynomialMass q := by
  classical
  have he : p * q = ∑ m ∈ p.support, ∑ n ∈ q.support,
      MvPolynomial.monomial (m + n) (p.coeff m * q.coeff n) := by
    conv_lhs => rw [p.as_sum, q.as_sum]
    simp only [Finset.sum_mul, Finset.mul_sum, MvPolynomial.monomial_mul]
    exact Finset.sum_comm
  rw [he]
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ m ∈ p.support, ∑ n ∈ q.support,
        realPolynomialMass (MvPolynomial.monomial (m + n) (p.coeff m * q.coeff n)) :=
      Finset.sum_le_sum (fun _ _ => realPolynomialMass_sum_le _ _)
    _ = realPolynomialMass p * realPolynomialMass q := by
      simp_rw [realPolynomialMass_monomial]
      simp only [abs_mul, realPolynomialMass,
        Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm

theorem realPolynomialMass_prod_le {I J : Type*} (s : Finset J) (p : J → MvPolynomial I ℝ) :
    realPolynomialMass (∏ j ∈ s, p j) ≤ ∏ j ∈ s, realPolynomialMass (p j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, realPolynomialMass_one, le_refl]
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    exact (realPolynomialMass_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left ih (realPolynomialMass_nonneg _))

theorem realPolynomialMass_pow_le {I : Type*} (p : MvPolynomial I ℝ) (n : ℕ) :
    realPolynomialMass (p ^ n) ≤ realPolynomialMass p ^ n := by
  induction n with
  | zero => simp only [pow_zero, realPolynomialMass_one, le_refl]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (realPolynomialMass_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right ih (realPolynomialMass_nonneg _))

theorem realPolynomialMass_C_mul_le {I : Type*} (c : ℝ) (p : MvPolynomial I ℝ) :
    realPolynomialMass (MvPolynomial.C c * p) ≤ |c| * realPolynomialMass p := by
  simpa only [realPolynomialMass_C] using realPolynomialMass_mul_le (MvPolynomial.C c) p

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

theorem polynomialFunctional_expansion {σ R : Type*} [CommRing R]
    (L : MvPolynomial σ R →ₗ[R] R) (P : MvPolynomial σ R) :
    L P = ∑ d ∈ P.support, P.coeff d * L (monomial d 1) := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d _
  have he : monomial d (P.coeff d) = P.coeff d • monomial d (1 : R) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [he, map_smul, smul_eq_mul]

theorem polynomialFunctional_map_expansion {σ R S : Type*} [CommRing R] [CommRing S]
    (ρ : R →+* S) (L : MvPolynomial σ S →ₗ[S] S) (P : MvPolynomial σ R) :
    L (map ρ P) = ∑ d ∈ P.support, ρ (P.coeff d) * L (monomial d 1) := by
  conv_lhs => rw [P.as_sum]
  simp only [map_sum, map_monomial]
  apply Finset.sum_congr rfl
  intro d _
  have he : monomial d (ρ (P.coeff d)) = ρ (P.coeff d) • monomial d (1 : S) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [he, map_smul, smul_eq_mul]

theorem polynomialFunctional_le_mass {σ : Type*}
    (L : MvPolynomial σ ℝ →ₗ[ℝ] ℝ) (P : MvPolynomial σ ℝ) {C : ℝ}
    (hL : ∀ d ∈ P.support, |L (monomial d 1)| ≤ C) :
    |L P| ≤ C * realPolynomialMass P := by
  rw [polynomialFunctional_expansion]
  calc
    _ ≤ ∑ d ∈ P.support, |P.coeff d * L (monomial d 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ P.support, C * |P.coeff d| := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul, mul_comm C]
      exact mul_le_mul_of_nonneg_left (hL d hd) (abs_nonneg _)
    _ = C * realPolynomialMass P := by rw [realPolynomialMass, Finset.mul_sum]

theorem polynomialFunctional_homogeneous_le_mass {σ : Type*}
    (L : MvPolynomial σ ℝ →ₗ[ℝ] ℝ) {P : MvPolynomial σ ℝ} {h : ℕ}
    (hP : P.IsHomogeneous h) {C : ℝ}
    (hL : ∀ d : σ →₀ ℕ, d.degree = h → |L (monomial d 1)| ≤ C) :
    |L P| ≤ C * realPolynomialMass P :=
  polynomialFunctional_le_mass L P (fun d hd => hL d
    (by simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hP (mem_support_iff.mp hd)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem realPolynomialMass_substitution_le {I J : Type*}
    (p : MvPolynomial I ℝ) (f : I → MvPolynomial J ℝ) {M : ℝ} (hM : 1 ≤ M)
    (hf : ∀ i, realPolynomialMass (f i) ≤ M) {d : ℕ} (hd : p.totalDegree ≤ d) :
    realPolynomialMass (MvPolynomial.eval₂Hom MvPolynomial.C f p) ≤
      realPolynomialMass p * M ^ d := by
  classical
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
  calc
    _ ≤ ∑ m ∈ p.support, realPolynomialMass
        (MvPolynomial.C (p.coeff m) * ∏ i ∈ m.support, f i ^ m i) :=
      realPolynomialMass_sum_le _ _
    _ ≤ ∑ m ∈ p.support, |p.coeff m| * M ^ d := by
      apply Finset.sum_le_sum
      intro m hm
      apply (realPolynomialMass_C_mul_le _ _).trans
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        _ ≤ ∏ i ∈ m.support, realPolynomialMass (f i ^ m i) := realPolynomialMass_prod_le _ _
        _ ≤ ∏ i ∈ m.support, M ^ m i := by
          apply Finset.prod_le_prod (fun _ _ => realPolynomialMass_nonneg _)
          intro i _
          exact (realPolynomialMass_pow_le _ _).trans
            (pow_le_pow_left₀ (realPolynomialMass_nonneg _) (hf i) _)
        _ = M ^ (m.sum fun _ n => n) := by rw [Finset.prod_pow_eq_pow_sum]; rfl
        _ ≤ M ^ d := pow_le_pow_right₀ hM ((MvPolynomial.le_totalDegree hm).trans hd)
    _ = realPolynomialMass p * M ^ d := by rw [← Finset.sum_mul]; rfl

theorem polynomial_substitution_totalDegree_le {I J : Type*}
    (p : MvPolynomial I ℝ) (f : I → MvPolynomial J ℝ) {e d : ℕ}
    (hf : ∀ i, (f i).totalDegree ≤ e) (hd : p.totalDegree ≤ d) :
    (MvPolynomial.eval₂Hom MvPolynomial.C f p).totalDegree ≤ d * e := by
  classical
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  calc
    _ ≤ ∑ i ∈ m.support, (f i ^ m i).totalDegree := MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ m.support, m i * e := Finset.sum_le_sum (fun i _ =>
      (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hf i)))
    _ = (m.sum fun _ n => n) * e := by rw [← Finset.sum_mul]; rfl
    _ ≤ d * e := Nat.mul_le_mul_right _ ((MvPolynomial.le_totalDegree hm).trans hd)

theorem realPolynomialMass_rename_le {I J : Type*} (p : MvPolynomial I ℝ) (f : I → J) :
    realPolynomialMass (MvPolynomial.rename f p) ≤ realPolynomialMass p := by
  have he : (MvPolynomial.rename f : MvPolynomial I ℝ →ₐ[ℝ] MvPolynomial J ℝ).toRingHom =
      MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X (f i)) := by ext <;> simp
  change realPolynomialMass ((MvPolynomial.rename f).toRingHom p) ≤ _
  rw [he]
  have h := realPolynomialMass_substitution_le p (fun i => MvPolynomial.X (f i))
    (M := 1) le_rfl (fun i => (realPolynomialMass_X (f i)).le) le_rfl
  simpa only [one_pow, mul_one] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def polynomialMonomial {K I : Type*}
    (a : K → MvPolynomial I ℝ) (m : K →₀ ℕ) : MvPolynomial I ℝ :=
  ∏ k ∈ m.support, a k ^ m k

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ : Type*}

theorem realPolynomialMass_smul (c : ℝ) (P : MvPolynomial σ ℝ) :
    realPolynomialMass (c • P) = |c| * realPolynomialMass P := by
  classical
  by_cases hc : c = 0
  · simp [hc, realPolynomialMass_zero]
  · simp only [realPolynomialMass, support_smul_eq hc, coeff_smul,
      smul_eq_mul, abs_mul, Finset.mul_sum]

theorem realPolynomialMass_pderiv (i : σ) (P : MvPolynomial σ ℝ)
    {s : ℕ} (hP : P.totalDegree ≤ s) :
    realPolynomialMass (pderiv i P) ≤ s * realPolynomialMass P := by
  classical
  conv_lhs => rw [← P.support_sum_monomial_coeff, map_sum]
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ a ∈ P.support, s * |P.coeff a| := by
      apply Finset.sum_le_sum
      intro a ha
      rw [pderiv_monomial, realPolynomialMass_monomial, abs_mul,
        abs_of_nonneg (show (0 : ℝ) ≤ (a i : ℝ) from Nat.cast_nonneg _)]
      have h : (a i : ℝ) ≤ s := by
        exact_mod_cast (monomial_le_degreeOf i ha).trans ((degreeOf_le_totalDegree P i).trans hP)
      nlinarith [abs_nonneg (P.coeff a)]
    _ = _ := by rw [realPolynomialMass, Finset.mul_sum]

theorem polynomialDerivation_eq_sum [Fintype σ]
    (D : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ)) :
    D = ∑ i, D (X i) • pderiv i := by
  classical
  apply MvPolynomial.derivation_ext
  intro j
  change D (X j) = (Derivation.coeFnAddMonoidHom (∑ i, D (X i) • pderiv i)) (X j)
  rw [map_sum]
  simp [pderiv_X, smul_eq_mul, Pi.single_apply]

theorem realPolynomialMass_derivation [Fintype σ]
    (D : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ))
    {M : ℝ} (hM : 0 ≤ M) (hD : ∀ i, realPolynomialMass (D (X i)) ≤ M)
    {P : MvPolynomial σ ℝ} {s : ℕ} (hP : P.totalDegree ≤ s) :
    realPolynomialMass (D P) ≤ (Fintype.card σ * M * s) * realPolynomialMass P := by
  classical
  have he : D P = ∑ i, D (X i) * pderiv i P := by
    conv_lhs => rw [polynomialDerivation_eq_sum D]
    change (Derivation.coeFnAddMonoidHom (∑ i, D (X i) • pderiv i)) P = _
    rw [map_sum]
    simp [smul_eq_mul]
  rw [he]
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : σ, M * (s * realPolynomialMass P) := by
      apply Finset.sum_le_sum
      intro i _
      exact (realPolynomialMass_mul_le _ _).trans
        (mul_le_mul (hD i) (realPolynomialMass_pderiv i P hP)
          (realPolynomialMass_nonneg _) hM)
    _ = _ := by simp; ring

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

theorem abs_aeval_le_mass_box {σ : Type*} (P : MvPolynomial σ ℝ) (x : σ → ℝ)
    {B : ℝ} {n : ℕ} (hB : 1 ≤ B) (hx : ∀ i, |x i| ≤ B) (hP : P.totalDegree ≤ n) :
    |aeval x P| ≤ realPolynomialMass P * B ^ n := by
  classical
  change |P.eval₂ (RingHom.id ℝ) x| ≤ _
  rw [eval₂_eq]
  calc
    _ ≤ ∑ a ∈ P.support, |P.coeff a * ∏ i ∈ a.support, x i ^ a i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ P.support, |P.coeff a| * B ^ n := by
      apply Finset.sum_le_sum
      intro a ha
      rw [abs_mul, Finset.abs_prod]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        _ = ∏ i ∈ a.support, |x i| ^ a i := by simp only [abs_pow]
        _ ≤ ∏ i ∈ a.support, B ^ a i :=
          Finset.prod_le_prod (fun _ _ => by positivity)
            (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hx i) _)
        _ = B ^ (a.sum fun _ m => m) := by rw [Finset.prod_pow_eq_pow_sum]; rfl
        _ ≤ B ^ n := pow_le_pow_right₀ hB ((le_totalDegree ha).trans hP)
    _ = _ := by rw [← Finset.sum_mul]; rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LinearCoefficientMap
namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

noncomputable def mapPolynomialCoefficients {I R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (L : S →ₗ[R] R) (P : MvPolynomial I S) : MvPolynomial I R :=
  ∑ d ∈ P.support, monomial d (L (P.coeff d))

theorem mapPolynomialCoefficients_degree {I R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (L : S →ₗ[R] R) (P : MvPolynomial I S) :
    (mapPolynomialCoefficients L P).totalDegree ≤ P.totalDegree := by
  unfold mapPolynomialCoefficients
  apply totalDegree_finsetSum_le
  intro d hd
  exact (totalDegree_monomial_le d _).trans (le_totalDegree hd)

theorem mapPolynomialCoefficients_eval {I R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (L : S →ₗ[R] R) (P : MvPolynomial I S) (x : I → R) :
    eval x (mapPolynomialCoefficients L P) = L (eval (fun i => algebraMap R S (x i)) P) := by
  unfold mapPolynomialCoefficients
  rw [map_sum]
  conv_rhs => rw [P.as_sum]
  simp only [map_sum, eval_monomial]
  apply Finset.sum_congr rfl
  intro d _
  have he : P.coeff d * d.prod (fun i n => (algebraMap R S) (x i) ^ n) =
      (d.prod (fun i n => x i ^ n)) • P.coeff d := by
    simp only [Finsupp.prod, Algebra.smul_def, map_prod, map_pow]
    exact mul_comm _ _
  rw [he, map_smul, smul_eq_mul, mul_comm]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FrozenPartitionScore
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

noncomputable def partitionCell (cell : Ω → ι) (i : ι) : Finset Ω := by
  classical
  exact Finset.univ.filter (fun x => cell x = i)

omit [Fintype ι] in
theorem mem_partitionCell (cell : Ω → ι) (i : ι) (x : Ω) :
    x ∈ partitionCell cell i ↔ cell x = i := by
  classical
  simp [partitionCell]

theorem sum_partitionCell (cell : Ω → ι) (f : Ω → ℝ) :
    (∑ i, ∑ x ∈ partitionCell cell i, f x) = ∑ x, f x := by
  classical
  simp only [partitionCell, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem card_partitionCell_sum (cell : Ω → ι) :
    (∑ i, ((partitionCell cell i).card : ℝ)) = (Fintype.card Ω : ℝ) := by
  simpa using sum_partitionCell cell (fun _ => 1)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_good_partition_score {Ω I : Type*} [Fintype Ω] [Nonempty Ω] [Fintype I]
    (cell : Ω → I) (good : I → Prop) [DecidablePred good] (g : Ω → ℝ) {B τ ρ S : ℝ}
    (hB : 0 ≤ B) (hτ : 0 ≤ τ) (hg : ∀ x, g x ≤ B)
    (hbad : (𝔼 x, if good (cell x) then (0 : ℝ) else 1) ≤ ρ)
    (hscore : S ≤ 𝔼 x, g x) (hbudget : τ + B * ρ < S) :
    ∃ i, good i ∧ τ < 𝔼 x ∈ partitionCell cell i, g x := by
  classical
  by_contra! hnone
  let b : Ω → ℝ := fun x => if good (cell x) then 0 else 1
  have hcell (i : I) : (∑ x ∈ partitionCell cell i, g x) ≤
      τ * (partitionCell cell i).card + B * ∑ x ∈ partitionCell cell i, b x := by
    by_cases hi : good i
    · have hb : (∑ x ∈ partitionCell cell i, b x) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        simp only [b, (mem_partitionCell _ _ _).mp hx, hi, ite_true]
      rw [hb, mul_zero, add_zero]
      have h := mul_le_mul_of_nonneg_left (hnone i hi)
        (Nat.cast_nonneg (partitionCell cell i).card : (0 : ℝ) ≤ _)
      rw [Finset.card_mul_expect] at h
      simpa only [mul_comm] using h
    · have hb : (∑ x ∈ partitionCell cell i, b x) = (partitionCell cell i).card := by
        calc
          _ = ∑ _x ∈ partitionCell cell i, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro x hx
            simp only [b, (mem_partitionCell _ _ _).mp hx, hi, ite_false]
          _ = _ := by simp
      rw [hb]
      have hs : (∑ x ∈ partitionCell cell i, g x) ≤ B * (partitionCell cell i).card := by
        calc
          _ ≤ ∑ _x ∈ partitionCell cell i, B := Finset.sum_le_sum (fun x _ => hg x)
          _ = _ := by simp [mul_comm]
      exact hs.trans (le_add_of_nonneg_left (mul_nonneg hτ (Nat.cast_nonneg _)))
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) => hcell i)
  rw [sum_partitionCell, Finset.sum_add_distrib, ← Finset.mul_sum, card_partitionCell_sum,
    ← Finset.mul_sum, sum_partitionCell] at hsum
  have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hupper : (𝔼 x, g x) ≤ τ + B * (𝔼 x, b x) := by
    rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
    apply (div_le_iff₀ hN).mpr
    convert hsum using 1
    field_simp
  have hb : (𝔼 x, b x) ≤ ρ := hbad
  have hfinal := hupper.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hb hB))
  linarith

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

theorem unit_weight_score_error {a W V ε : ℝ} (ha : |a| ≤ 1) (hclose : dist W V ≤ ε) :
    a * W ≤ a * V + ε := by
  have h : a * (W - V) ≤ ε := by
    calc
      _ ≤ |a * (W - V)| := le_abs_self _
      _ = |a| * |W - V| := abs_mul _ _
      _ ≤ 1 * ε := mul_le_mul ha (by simpa only [Real.dist_eq] using hclose) (abs_nonneg _) (by norm_num)
      _ = ε := one_mul _
  nlinarith

theorem exists_good_frozen_partition_score {Ω I : Type*} [Fintype Ω] [Nonempty Ω] [Fintype I]
    (cell : Ω → I) (good : I → Prop) [DecidablePred good]
    (a W : Ω → ℝ) (V : I → Ω → ℝ) {B τ ρ ε S : ℝ}
    (hB : 0 ≤ B) (hτ : 0 ≤ τ) (hε : 0 ≤ ε)
    (ha : ∀ x, |a x| ≤ 1) (hW : ∀ x, a x * W x ≤ B)
    (hbad : (𝔼 x, if good (cell x) then (0 : ℝ) else 1) ≤ ρ)
    (hclose : ∀ x, dist (W x) (V (cell x) x) ≤ ε)
    (hscore : S ≤ 𝔼 x, a x * W x) (hbudget : τ + ε + B * ρ < S) :
    ∃ i, good i ∧ τ < 𝔼 x ∈ partitionCell cell i, a x * V i x := by
  obtain ⟨i, hi, hs⟩ := exists_good_partition_score cell good (fun x => a x * W x)
    hB (add_nonneg hτ hε) hW hbad hscore hbudget
  have hne : (partitionCell cell i).Nonempty := by
    by_contra hn
    have hz := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [hz, Finset.expect_empty] at hs
    linarith
  have herr : (𝔼 x ∈ partitionCell cell i, a x * W x) ≤
      (𝔼 x ∈ partitionCell cell i, a x * V i x) + ε := by
    calc
      _ ≤ 𝔼 x ∈ partitionCell cell i, (a x * V i x + ε) := by
        apply Finset.expect_le_expect
        intro x hx
        apply unit_weight_score_error (ha x)
        simpa only [(mem_partitionCell _ _ _).mp hx] using hclose x
      _ = _ := by rw [Finset.expect_add_distrib, Finset.expect_const hne]
  exact ⟨i, hi, by linarith⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProgressionPartitionComposition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def truncatedProgressionLength (N a q H : ℕ) : ℕ :=
  if a < N then min H ((N - 1 - a) / q + 1) else 0

theorem lt_truncatedProgressionLength_iff {N a q H j : ℕ} (hq : 0 < q) :
    j < truncatedProgressionLength N a q H ↔ j < H ∧ a + q * j < N := by
  by_cases ha : a < N
  · simp only [truncatedProgressionLength, if_pos ha, lt_min_iff]
    rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hq, Nat.mul_comm j q]
    omega
  · simp only [truncatedProgressionLength, if_neg ha, Nat.not_lt_zero, false_iff,
      not_and]
    omega

def progressionBlockLabel {N : ℕ} (q H : ℕ) (hq : 0 < q) (n : Fin N) :
    Fin q × Fin (N / q / H + 1) :=
  (⟨n.val % q, Nat.mod_lt _ hq⟩,
    ⟨n.val / q / H, Nat.lt_succ_of_le
      (Nat.div_le_div_right (Nat.div_le_div_right (Nat.le_of_lt n.isLt)))⟩)

def progressionBlockStart {N q H : ℕ} (i : Fin q × Fin (N / q / H + 1)) : ℕ :=
  i.1.val + q * (H * i.2.val)

theorem progressionBlock_reconstruct {N q H : ℕ} (hq : 0 < q) (n : Fin N) :
    progressionBlockStart (progressionBlockLabel q H hq n) + q * (n.val / q % H) =
      n.val := by
  dsimp [progressionBlockStart, progressionBlockLabel]
  calc
    _ = n.val % q + q * (n.val / q % H + H * (n.val / q / H)) := by ring
    _ = n.val := by rw [Nat.mod_add_div, Nat.mod_add_div]

theorem progressionBlockLabel_of_point {N q H : ℕ} (hq : 0 < q) (hH : 0 < H)
    (i : Fin q × Fin (N / q / H + 1)) {j : ℕ} (hj : j < H)
    (hpoint : progressionBlockStart i + q * j < N) :
    progressionBlockLabel q H hq ⟨progressionBlockStart i + q * j, hpoint⟩ = i := by
  apply Prod.ext <;> apply Fin.ext
  · simp [progressionBlockLabel, progressionBlockStart, Nat.add_mod,
      Nat.mod_eq_of_lt i.1.isLt]
  · change (i.1.val + q * (H * i.2.val) + q * j) / q / H = i.2.val
    rw [show i.1.val + q * (H * i.2.val) + q * j =
      i.1.val + q * (H * i.2.val + j) by ring]
    rw [Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt i.1.isLt, zero_add]
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hH, Nat.div_eq_of_lt hj, zero_add]

theorem progressionBlockLabel_eq_iff {N q H : ℕ} (hq : 0 < q) (hH : 0 < H)
    (i : Fin q × Fin (N / q / H + 1)) (n : Fin N) :
    progressionBlockLabel q H hq n = i ↔
      ∃ j < truncatedProgressionLength N (progressionBlockStart i) q H,
        n.val = progressionBlockStart i + q * j := by
  constructor
  · intro hi
    have heq := progressionBlock_reconstruct (H := H) hq n
    rw [hi] at heq
    exact ⟨n.val / q % H,
      (lt_truncatedProgressionLength_iff hq).mpr
        ⟨Nat.mod_lt _ hH, lt_of_eq_of_lt heq n.isLt⟩,
      heq.symm⟩
  · rintro ⟨j, hj, hn⟩
    have hj' := (lt_truncatedProgressionLength_iff hq).mp hj
    have heq := progressionBlockLabel_of_point hq hH i hj'.1 hj'.2
    have hfin : n = ⟨progressionBlockStart i + q * j, hj'.2⟩ := Fin.ext hn
    rwa [← hfin] at heq

noncomputable def progressionBlockEquiv {N q H : ℕ} (hq : 0 < q) (hH : 0 < H)
    (i : Fin q × Fin (N / q / H + 1)) :
    Fin (truncatedProgressionLength N (progressionBlockStart i) q H) ≃
      ↥(partitionCell (progressionBlockLabel q H hq) i) := by
  let point (j : Fin (truncatedProgressionLength N (progressionBlockStart i) q H)) :
      ↥(partitionCell (progressionBlockLabel q H hq) i) :=
    ⟨⟨progressionBlockStart i + q * j.val,
        ((lt_truncatedProgressionLength_iff hq).mp j.isLt).2⟩,
      (mem_partitionCell _ _ _).mpr
        (progressionBlockLabel_of_point hq hH i
          ((lt_truncatedProgressionLength_iff hq).mp j.isLt).1 _)⟩
  apply Equiv.ofBijective point
  constructor
  · intro j k hjk
    apply Fin.ext
    have heq : progressionBlockStart i + q * j.val =
        progressionBlockStart i + q * k.val := congrArg (fun n => n.val.val) hjk
    exact mul_left_cancel₀ hq.ne' (Nat.add_left_cancel heq)
  · intro n
    obtain ⟨j, hj, hn⟩ := (progressionBlockLabel_eq_iff hq hH i n.val).mp
      ((mem_partitionCell _ _ _).mp n.property)
    exact ⟨⟨j, hj⟩, Subtype.ext (Fin.ext hn.symm)⟩

theorem progressionBlock_label_count (N q H : ℕ) :
    Fintype.card (Fin q × Fin (N / q / H + 1)) ≤ N / H + q := by
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.mul_add, Nat.mul_one]
  apply Nat.add_le_add_right
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm q H, ← Nat.div_div_eq_div_mul]
  exact Nat.mul_div_le _ _

theorem progressionBlock_label_count_mul (N q H : ℕ) :
    Fintype.card (Fin q × Fin (N / q / H + 1)) * H ≤ N + q * H := by
  calc
    _ ≤ (N / H + q) * H := Nat.mul_le_mul_right H (progressionBlock_label_count N q H)
    _ = N / H * H + q * H := Nat.add_mul _ _ _
    _ ≤ N + q * H := Nat.add_le_add_right (Nat.div_mul_le_self _ _) _

theorem progressionBlock_label_count_mul_le_twice {N q H : ℕ} (hfit : q * H ≤ N) :
    Fintype.card (Fin q × Fin (N / q / H + 1)) * H ≤ 2 * N := by
  have h := progressionBlock_label_count_mul N q H
  omega

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

structure FiniteProgressionPartition (N : ℕ) where
  Label : Type
  labelFintype : Fintype Label
  start : Label → ℕ
  step : Label → ℕ
  length : Label → ℕ
  step_pos : ∀ i, 0 < step i
  equiv : (Σ i : Label, Fin (length i)) ≃ Fin N
  equiv_val : ∀ i (j : Fin (length i)), (equiv ⟨i, j⟩).val = start i + step i * j.val

attribute [instance] FiniteProgressionPartition.labelFintype

namespace FiniteProgressionPartition

variable {N : ℕ} (P : FiniteProgressionPartition N)

def point (i : P.Label) (j : Fin (P.length i)) : Fin N := P.equiv ⟨i, j⟩

@[simp] theorem point_val (i : P.Label) (j : Fin (P.length i)) :
    (P.point i j).val = P.start i + P.step i * j.val := P.equiv_val i j

theorem point_lt (i : P.Label) {j : ℕ} (hj : j < P.length i) :
    P.start i + P.step i * j < N := by
  simpa only [P.point_val] using (P.point i ⟨j, hj⟩).isLt

def cell (n : Fin N) : P.Label := (P.equiv.symm n).1

def offset (n : Fin N) : Fin (P.length (P.cell n)) := (P.equiv.symm n).2

@[simp] theorem cell_point (i : P.Label) (j : Fin (P.length i)) :
    P.cell (P.point i j) = i := by simp [cell, point]

@[simp] theorem point_cell_offset (n : Fin N) : P.point (P.cell n) (P.offset n) = n := by
  exact P.equiv.apply_symm_apply n

noncomputable def pointEquiv (i : P.Label) :
    Fin (P.length i) ≃ ↥(partitionCell P.cell i) := by
  let f (j : Fin (P.length i)) : ↥(partitionCell P.cell i) :=
    ⟨P.point i j, (mem_partitionCell P.cell i _).mpr (P.cell_point i j)⟩
  apply Equiv.ofBijective f
  constructor
  · intro j k h
    have he : P.equiv ⟨i, j⟩ = P.equiv ⟨i, k⟩ := congrArg Subtype.val h
    exact sigma_mk_injective (β := fun i : P.Label => Fin (P.length i)) (P.equiv.injective he)
  · intro n
    have hi : P.cell n.val = i := (mem_partitionCell P.cell i n.val).mp n.property
    rcases hx : P.equiv.symm n.val with ⟨k, j⟩
    have hki : k = i := by simpa only [cell, hx] using hi
    subst k
    refine ⟨j, Subtype.ext ?_⟩
    have he := congrArg P.equiv hx
    simpa only [f, point, Equiv.apply_symm_apply] using he.symm

theorem card_cell (i : P.Label) : (partitionCell P.cell i).card = P.length i := by
  simpa only [Fintype.card_coe, Fintype.card_fin] using (Fintype.card_congr (P.pointEquiv i)).symm

def whole (N : ℕ) : FiniteProgressionPartition N where
  Label := Unit
  labelFintype := inferInstance
  start := fun _ => 0
  step := fun _ => 1
  length := fun _ => N
  step_pos := fun _ => by decide
  equiv := {
    toFun := fun x => x.2
    invFun := fun n => ⟨(), n⟩
    left_inv := fun ⟨i, j⟩ => by cases i; rfl
    right_inv := fun _ => rfl }
  equiv_val := fun _ _ => by simp

noncomputable def blocks (N q H : ℕ) (hq : 0 < q) (hH : 0 < H) :
    FiniteProgressionPartition N where
  Label := Fin q × Fin (N / q / H + 1)
  labelFintype := inferInstance
  start := progressionBlockStart
  step := fun _ => q
  length := fun i => truncatedProgressionLength N (progressionBlockStart i) q H
  step_pos := fun _ => hq
  equiv := (Equiv.sigmaCongrRight (fun i => (progressionBlockEquiv hq hH i).trans
    (Equiv.subtypeEquivRight (fun n => mem_partitionCell (progressionBlockLabel q H hq) i n)))).trans
    (Equiv.sigmaFiberEquiv (progressionBlockLabel q H hq))
  equiv_val := fun _ _ => rfl

end FiniteProgressionPartition
end Erdos3

end

section

namespace Erdos3

def mergedIntervalLength (N H k : ℕ) : ℕ :=
  if k + 1 = N / H then N - H * k else H

theorem mergedInterval_start_le {N H k : ℕ} (hk : k < N / H) : H * k ≤ N := by
  have hq : H * (N / H) ≤ N := by simpa only [mul_comm] using Nat.div_mul_le_self N H
  exact (Nat.mul_le_mul_left H hk.le).trans hq

theorem mergedInterval_length_bounds {N H k : ℕ} (hH : 0 < H) (hk : k < N / H) :
    H ≤ mergedIntervalLength N H k ∧ mergedIntervalLength N H k < 2 * H := by
  by_cases hlast : k + 1 = N / H
  · have hstart := mergedInterval_start_le hk
    have hcancel := Nat.sub_add_cancel hstart
    have hq : H * (N / H) ≤ N := by simpa only [mul_comm] using Nat.div_mul_le_self N H
    have hdiv := Nat.mod_add_div N H
    have hrem := Nat.mod_lt N hH
    rw [← hlast] at hq hdiv
    simp only [mergedIntervalLength, hlast, ite_true]
    constructor <;> nlinarith
  · simp only [mergedIntervalLength, hlast, ite_false]
    exact ⟨le_rfl, by omega⟩

theorem mergedInterval_point_lt {N H k j : ℕ} (hk : k < N / H)
    (hj : j < mergedIntervalLength N H k) : H * k + j < N := by
  by_cases hlast : k + 1 = N / H
  · have hstart := mergedInterval_start_le hk
    simp only [mergedIntervalLength, hlast, ite_true] at hj
    omega
  · have hjH : j < H := by simpa only [mergedIntervalLength, hlast, ite_false] using hj
    have hstep := Nat.mul_le_mul_left H (Nat.succ_le_of_lt hk)
    have hq : H * (N / H) ≤ N := by simpa only [mul_comm] using Nat.div_mul_le_self N H
    nlinarith

theorem mergedInterval_index_unique {N H k l j t : ℕ}
    (hk : k < N / H) (hl : l < N / H)
    (hj : j < mergedIntervalLength N H k) (ht : t < mergedIntervalLength N H l)
    (heq : H * k + j = H * l + t) : k = l := by
  rcases lt_trichotomy k l with hkl | hkl | hlk
  · have hlast : k + 1 ≠ N / H := by omega
    have hjH : j < H := by simpa only [mergedIntervalLength, hlast, ite_false] using hj
    have hstep := Nat.mul_le_mul_left H (Nat.succ_le_of_lt hkl)
    nlinarith
  · exact hkl
  · have hlast : l + 1 ≠ N / H := by omega
    have htH : t < H := by simpa only [mergedIntervalLength, hlast, ite_false] using ht
    have hstep := Nat.mul_le_mul_left H (Nat.succ_le_of_lt hlk)
    nlinarith

theorem exists_mergedInterval_coordinate {N H y : ℕ} (hH : 0 < H) (hHN : H ≤ N) (hy : y < N) :
    ∃ k < N / H, ∃ j < mergedIntervalLength N H k, H * k + j = y := by
  have hq : 0 < N / H := Nat.div_pos hHN hH
  let k := min (y / H) (N / H - 1)
  have hkleft : k ≤ y / H := Nat.min_le_left _ _
  have hkright : k ≤ N / H - 1 := Nat.min_le_right _ _
  have hk : k < N / H := by omega
  have hdivy : H * (y / H) ≤ y := by simpa only [mul_comm] using Nat.div_mul_le_self y H
  have hstart : H * k ≤ y := (Nat.mul_le_mul_left H hkleft).trans hdivy
  have hj : y - H * k < mergedIntervalLength N H k := by
    by_cases hlast : k + 1 = N / H
    · simp only [mergedIntervalLength, hlast, ite_true]
      omega
    · have hkeq : k = y / H := by
        by_cases hle : y / H ≤ N / H - 1
        · exact min_eq_left hle
        · have heq : k = N / H - 1 := min_eq_right (le_of_not_ge hle)
          omega
      have hdiv := Nat.mod_add_div y H
      have hrem := Nat.mod_lt y hH
      rw [← hkeq] at hdiv
      simp only [mergedIntervalLength, hlast, ite_false]
      omega
  exact ⟨k, hk, y - H * k, hj, by omega⟩

end Erdos3

end

section

namespace Erdos3

theorem truncatedProgressionLength_le (N a q H : ℕ) :
    truncatedProgressionLength N a q H ≤ H := by
  unfold truncatedProgressionLength
  split_ifs
  · exact min_le_left _ _
  · exact Nat.zero_le _

namespace FiniteProgressionPartition

variable {N : ℕ} (P : FiniteProgressionPartition N)

noncomputable def restrict (M : ℕ) (hMN : M ≤ N) : FiniteProgressionPartition M := by
  let len (i : P.Label) := truncatedProgressionLength M (P.start i) (P.step i) (P.length i)
  have hlen (i : P.Label) : len i ≤ P.length i := truncatedProgressionLength_le _ _ _ _
  let emb : (Σ i : P.Label, Fin (len i)) → Σ i : P.Label, Fin (P.length i) :=
    Sigma.map id (fun i j => ⟨j.val, j.isLt.trans_le (hlen i)⟩)
  have hemb : Function.Injective emb := by
    apply Function.injective_id.sigma_map
    intro i x y h
    apply Fin.ext
    exact congrArg (fun z : Fin (P.length i) => z.val) h
  let f (x : Σ i : P.Label, Fin (len i)) : Fin M :=
    ⟨P.start x.1 + P.step x.1 * x.2.val,
      ((lt_truncatedProgressionLength_iff (P.step_pos x.1)).mp x.2.isLt).2⟩
  have hrel (x : Σ i : P.Label, Fin (len i)) : (P.equiv (emb x)).val = (f x).val :=
    P.equiv_val x.1 _
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply hemb
      apply P.equiv.injective
      apply Fin.ext
      rw [hrel, hrel, h]
    · intro n
      let y := P.equiv.symm ⟨n.val, n.isLt.trans_le hMN⟩
      have hy : P.start y.1 + P.step y.1 * y.2.val = n.val := by
        rw [← P.equiv_val]
        exact congrArg Fin.val (P.equiv.apply_symm_apply _)
      have hj : y.2.val < len y.1 :=
        (lt_truncatedProgressionLength_iff (P.step_pos y.1)).mpr ⟨y.2.isLt, by rw [hy]; exact n.isLt⟩
      exact ⟨⟨y.1, ⟨y.2.val, hj⟩⟩, Fin.ext hy⟩
  exact {
    Label := P.Label
    labelFintype := P.labelFintype
    start := P.start
    step := P.step
    length := len
    step_pos := P.step_pos
    equiv := Equiv.ofBijective f hf
    equiv_val := fun _ _ => rfl }

@[simp] theorem restrict_start (M : ℕ) (hMN : M ≤ N) (i : P.Label) :
    (P.restrict M hMN).start i = P.start i := rfl

@[simp] theorem restrict_step (M : ℕ) (hMN : M ≤ N) (i : P.Label) :
    (P.restrict M hMN).step i = P.step i := rfl

@[simp] theorem restrict_card (M : ℕ) (hMN : M ≤ N) :
    Fintype.card (P.restrict M hMN).Label = Fintype.card P.Label := rfl

end FiniteProgressionPartition
end Erdos3

end

section

namespace Erdos3.FiniteProgressionPartition

noncomputable def mergedIntervals (N H : ℕ) (hH : 0 < H) (hHN : H ≤ N) :
    FiniteProgressionPartition N := by
  let len : Fin (N / H) → ℕ := fun k => mergedIntervalLength N H k.val
  let f : (Σ k : Fin (N / H), Fin (len k)) → Fin N := fun x =>
    ⟨H * x.1.val + x.2.val, mergedInterval_point_lt x.1.isLt x.2.isLt⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨k, j⟩ ⟨l, t⟩ heq
      have he : H * k.val + j.val = H * l.val + t.val := congrArg Fin.val heq
      have hkl : k = l := Fin.ext (mergedInterval_index_unique k.isLt l.isLt j.isLt t.isLt he)
      cases hkl
      have hjt : j = t := Fin.ext (Nat.add_left_cancel he)
      cases hjt
      rfl
    · intro y
      obtain ⟨k, hk, j, hj, heq⟩ := exists_mergedInterval_coordinate hH hHN y.isLt
      exact ⟨⟨⟨k, hk⟩, ⟨j, hj⟩⟩, Fin.ext heq⟩
  exact {
    Label := Fin (N / H)
    labelFintype := inferInstance
    start := fun k => H * k.val
    step := fun _ => 1
    length := len
    step_pos := fun _ => Nat.zero_lt_one
    equiv := Equiv.ofBijective f hf
    equiv_val := fun _ _ => by simp only [Equiv.ofBijective_apply, f, one_mul] }

theorem mergedIntervals_length_bounds (N H : ℕ) (hH : 0 < H) (hHN : H ≤ N)
    (k : (mergedIntervals N H hH hHN).Label) :
    H ≤ (mergedIntervals N H hH hHN).length k ∧
      (mergedIntervals N H hH hHN).length k < 2 * H :=
  mergedInterval_length_bounds hH k.isLt

@[simp] theorem mergedIntervals_start (N H : ℕ) (hH : 0 < H) (hHN : H ≤ N)
    (k : (mergedIntervals N H hH hHN).Label) :
    (mergedIntervals N H hH hHN).start k = H * k.val := rfl

@[simp] theorem mergedIntervals_step (N H : ℕ) (hH : 0 < H) (hHN : H ≤ N)
    (k : (mergedIntervals N H hH hHN).Label) :
    (mergedIntervals N H hH hHN).step k = 1 := rfl

@[simp] theorem mergedIntervals_card (N H : ℕ) (hH : 0 < H) (hHN : H ≤ N) :
    Fintype.card (mergedIntervals N H hH hHN).Label = N / H := Fintype.card_fin _

theorem cell_eq_iff_of_step_one {N : ℕ} (P : FiniteProgressionPartition N)
    (hstep : ∀ k, P.step k = 1) (n : Fin N) (k : P.Label) :
    P.cell n = k ↔ P.start k ≤ n.val ∧ n.val < P.start k + P.length k := by
  constructor
  · intro hn
    subst k
    have heq := congrArg Fin.val (P.point_cell_offset n)
    rw [P.point_val, hstep, one_mul] at heq
    have hj := (P.offset n).isLt
    omega
  · rintro ⟨hlo, hhi⟩
    let j : Fin (P.length k) := ⟨n.val - P.start k, by omega⟩
    have heq : P.point k j = n := by
      apply Fin.ext
      rw [P.point_val, hstep, one_mul]
      dsimp only [j]
      omega
    rw [← heq, P.cell_point]

theorem end_le_of_step_one {N : ℕ} (P : FiniteProgressionPartition N)
    (hstep : ∀ k, P.step k = 1) (k : P.Label) (hpos : 0 < P.length k) :
    P.start k + P.length k ≤ N := by
  have h := P.point_lt k (j := P.length k - 1) (by omega)
  rw [hstep, one_mul] at h
  omega

end Erdos3.FiniteProgressionPartition

end

section

namespace Erdos3.FiniteProgressionPartition

variable {N : ℕ} (P : FiniteProgressionPartition N)

noncomputable def bind (Q : ∀ i : P.Label, FiniteProgressionPartition (P.length i)) :
    FiniteProgressionPartition N where
  Label := Σ i : P.Label, (Q i).Label
  labelFintype := inferInstance
  start := fun x => P.start x.1 + P.step x.1 * (Q x.1).start x.2
  step := fun x => P.step x.1 * (Q x.1).step x.2
  length := fun x => (Q x.1).length x.2
  step_pos := fun x => Nat.mul_pos (P.step_pos x.1) ((Q x.1).step_pos x.2)
  equiv := (Equiv.sigmaAssoc (fun i j => Fin ((Q i).length j))).trans
    ((Equiv.sigmaCongrRight (fun i => (Q i).equiv)).trans P.equiv)
  equiv_val := by
    intro x j
    change (P.equiv ⟨x.1, (Q x.1).equiv ⟨x.2, j⟩⟩).val = _
    rw [P.equiv_val, (Q x.1).equiv_val]
    ring

@[simp] theorem bind_start (Q : ∀ i : P.Label, FiniteProgressionPartition (P.length i))
    (i : P.Label) (j : (Q i).Label) :
    (P.bind Q).start ⟨i, j⟩ = P.start i + P.step i * (Q i).start j := rfl

@[simp] theorem bind_step (Q : ∀ i : P.Label, FiniteProgressionPartition (P.length i))
    (i : P.Label) (j : (Q i).Label) :
    (P.bind Q).step ⟨i, j⟩ = P.step i * (Q i).step j := rfl

@[simp] theorem bind_length (Q : ∀ i : P.Label, FiniteProgressionPartition (P.length i))
    (i : P.Label) (j : (Q i).Label) : (P.bind Q).length ⟨i, j⟩ = (Q i).length j := rfl

end Erdos3.FiniteProgressionPartition

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarExtensionSubstitution
namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

theorem aeval_polynomial_totalDegree_le {I J R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (P : MvPolynomial I R) (f : I → MvPolynomial J S) {d e : ℕ}
    (hP : P.totalDegree ≤ d) (hf : ∀ i, (f i).totalDegree ≤ e) :
    (aeval f P).totalDegree ≤ d * e := by
  rw [aeval_def, eval₂_eq]
  apply totalDegree_finsetSum_le
  intro a ha
  apply (totalDegree_mul _ _).trans
  simp only [MvPolynomial.algebraMap_apply, totalDegree_C, zero_add]
  calc
    _ ≤ ∑ i ∈ a.support, (f i ^ a i).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ a.support, a i * e := Finset.sum_le_sum (fun i _ =>
      (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hf i)))
    _ = (a.sum fun _ n => n) * e := by rw [← Finset.sum_mul]; rfl
    _ ≤ d * e := Nat.mul_le_mul_right _ ((le_totalDegree ha).trans hP)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformProductAccuracy
namespace OAI

section

namespace Erdos3

theorem abs_finset_prod_sub_prod_le {ι : Type*} (S : Finset ι) (f g : ι → ℝ)
    {B δ : ℝ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hf : ∀ i ∈ S, |f i| ≤ B) (hg : ∀ i ∈ S, |g i| ≤ B)
    (hdiff : ∀ i ∈ S, |f i - g i| ≤ δ) :
    |(∏ i ∈ S, f i) - ∏ i ∈ S, g i| ≤ S.card * δ * B ^ S.card := by
  classical
  revert hf hg hdiff
  induction S using Finset.induction_on with
  | empty => intro _ _ _; simp
  | @insert a S ha ih =>
    intro hf hg hdiff
    have hfS := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgS := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hdS := fun i hi => hdiff i (Finset.mem_insert_of_mem hi)
    have hrec := ih hfS hgS hdS
    have hprod : |∏ i ∈ S, g i| ≤ B ^ S.card := by
      rw [Finset.abs_prod]
      calc
        _ ≤ ∏ _i ∈ S, B := Finset.prod_le_prod (fun _ _ => abs_nonneg _) hgS
        _ = _ := by simp
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    calc
      _ = |f a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i) + (f a - g a) * ∏ i ∈ S, g i| := by
        congr 1
        ring
      _ ≤ |f a| * |(∏ i ∈ S, f i) - ∏ i ∈ S, g i| + |f a - g a| * |∏ i ∈ S, g i| := by
        simpa only [abs_mul] using abs_add_le
          (f a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i)) ((f a - g a) * ∏ i ∈ S, g i)
      _ ≤ B * (S.card * δ * B ^ S.card) + δ * B ^ S.card :=
        add_le_add (mul_le_mul (hf a (Finset.mem_insert_self _ _)) hrec
          (abs_nonneg _) (by linarith))
          (mul_le_mul (hdiff a (Finset.mem_insert_self _ _)) hprod (abs_nonneg _) hδ)
      _ = (S.card : ℝ) * δ * B ^ (S.card + 1) + δ * B ^ S.card := by rw [pow_succ]; ring
      _ ≤ (S.card : ℝ) * δ * B ^ (S.card + 1) + δ * B ^ (S.card + 1) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB (Nat.le_succ _)) hδ)
      _ = _ := by push_cast; ring

theorem abs_pow_sub_pow_box_bound {x y B δ : ℝ} {n s : ℕ}
    (hB : 1 ≤ B) (hδ : 0 ≤ δ) (hx : |x| ≤ B) (hy : |y| ≤ B)
    (hxy : |x - y| ≤ δ) (hn : n ≤ s) :
    |x ^ n - y ^ n| ≤ δ * s * B ^ s := by
  apply (abs_pow_sub_pow_le x y n).trans
  apply mul_le_mul (mul_le_mul hxy (Nat.cast_le.mpr hn) (Nat.cast_nonneg _) hδ)
  · exact (pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) (max_le hx hy) _).trans
      (pow_le_pow_right₀ hB (by omega))
  · positivity
  · positivity

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

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def uniformProductAccuracy (N : ℕ) (C δ : ℝ) : ℝ :=
  min 1 (δ / (((N : ℝ) + 1) * (C + 2) ^ N))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ComplexPartitionMixture
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem sum_partitionCell_complex {X K : Type*} [Fintype X] [Fintype K]
    (cell : X → K) (f : X → ℂ) :
    (∑ k, ∑ x ∈ partitionCell cell k, f x) = ∑ x, f x := by
  classical
  simp only [partitionCell, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem complex_expect_partition_mixture {X K : Type*} [Fintype X] [Fintype K]
    (cell : X → K) (f : X → ℂ) :
    (𝔼 x, f x) = ∑ k, ((partitionCell cell k).card : ℂ) / Fintype.card X *
      (𝔼 x ∈ partitionCell cell k, f x) := by
  classical
  have hcell (k : K) : ((partitionCell cell k).card : ℂ) / Fintype.card X *
      (𝔼 x ∈ partitionCell cell k, f x) =
      (∑ x ∈ partitionCell cell k, f x) / Fintype.card X := by
    rw [Finset.expect_eq_sum_div_card]
    by_cases hc : (partitionCell cell k).card = 0
    · have hempty := Finset.card_eq_zero.mp hc
      simp only [hempty, Finset.card_empty, Nat.cast_zero, Finset.sum_empty, zero_div, mul_zero]
    · have hc' : ((partitionCell cell k).card : ℂ) ≠ 0 := by exact_mod_cast hc
      calc
        _ = (((partitionCell cell k).card : ℂ) / (partitionCell cell k).card) *
            ((∑ x ∈ partitionCell cell k, f x) / Fintype.card X) := by ring
        _ = _ := by rw [div_self hc', one_mul]
  simp_rw [hcell]
  rw [← Finset.sum_div, sum_partitionCell_complex, Fintype.expect_eq_sum_div_card]

theorem complex_expect_partition_count_weights {X K : Type*} [Fintype X] [Fintype K]
    (cell : X → K) (f : X → ℂ) :
    (𝔼 x, f x) = ∑ k,
      (((partitionCell cell k).card : ℝ) / (∑ j, ((partitionCell cell j).card : ℝ)) : ℂ) *
      (𝔼 x ∈ partitionCell cell k, f x) := by
  rw [card_partitionCell_sum]
  simpa only [Complex.ofReal_div, Complex.ofReal_natCast] using complex_expect_partition_mixture cell f

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxBlockBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem expect_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
    [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)] (i : ι) (f : X i → ℝ) :
    (𝔼 x : (∀ j, X j), f (x i)) = 𝔼 a, f a := by
  have h := Fintype.expect_equiv (Equiv.piSplitAt i X)
    (fun x => f (x i)) (fun x => f x.1) (fun _ => rfl)
  rw [h]
  simpa using Finset.expect_product' (Finset.univ : Finset (X i))
    (Finset.univ : Finset (∀ j : {j // j ≠ i}, X j)) (fun a _ => f a)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def coordinateExceptional {ι X : Type*} [Fintype ι] [Fintype X]
    (B : Finset X) : Finset (ι → X) := by
  classical
  exact Finset.univ.filter (fun x => ∃ i, x i ∈ B)

theorem not_mem_coordinateExceptional {ι X : Type*} [Fintype ι] [Fintype X]
    (B : Finset X) (x : ι → X) : x ∉ coordinateExceptional B ↔ ∀ i, x i ∉ B := by
  classical
  simp [coordinateExceptional]

theorem coordinateExceptional_density_le {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype X] [Nonempty X] (B : Finset X) :
    ((coordinateExceptional (ι := ι) B).card : ℝ) / Fintype.card (ι → X) ≤
      (Fintype.card ι : ℝ) * (B.card : ℝ) / Fintype.card X := by
  classical
  have hpoint (x : ι → X) : (if ∃ i, x i ∈ B then (1 : ℝ) else 0) ≤
      ∑ i, if x i ∈ B then (1 : ℝ) else 0 := by
    by_cases h : ∃ i, x i ∈ B
    · obtain ⟨i, hi⟩ := h
      rw [if_pos ⟨i, hi⟩]
      calc
        (1 : ℝ) = if x i ∈ B then 1 else 0 := by rw [if_pos hi]
        _ ≤ _ := Finset.single_le_sum
          (f := fun j : ι => if x j ∈ B then (1 : ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
    · rw [if_neg h]
      exact Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)
  calc
    _ = 𝔼 x : ι → X, if ∃ i, x i ∈ B then (1 : ℝ) else 0 := by
      simp [coordinateExceptional, Fintype.expect_eq_sum_div_card]
      congr 1
      ext x
      simp
    _ ≤ 𝔼 x : ι → X, ∑ i, if x i ∈ B then (1 : ℝ) else 0 :=
      Finset.expect_le_expect (fun x _ => hpoint x)
    _ = ∑ i, 𝔼 x : ι → X, if x i ∈ B then (1 : ℝ) else 0 := Finset.expect_sum_comm _ _ _
    _ = ∑ _i : ι, (B.card : ℝ) / Fintype.card X := by
      congr 1
      funext i
      rw [expect_coordinate (X := fun _ : ι => X) i (fun x : X => if x ∈ B then (1 : ℝ) else 0)]
      simp [Fintype.expect_eq_sum_div_card, Finset.sum_ite_mem]
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Erdos3

end

section

namespace Erdos3.BoxProgressionPartition

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i))

def cell (x : ∀ i, Fin (N i)) : ∀ i, (P i).Label := fun i => (P i).cell (x i)

def point (a : ∀ i, (P i).Label) (j : ∀ i, Fin ((P i).length (a i))) : ∀ i, Fin (N i) :=
  fun i => (P i).point (a i) (j i)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem point_val (a : ∀ i, (P i).Label) (j : ∀ i, Fin ((P i).length (a i))) (i : ι) :
    (point P a j i).val = (P i).start (a i) + (P i).step (a i) * (j i).val :=
  (P i).point_val _ _

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem cell_point (a : ∀ i, (P i).Label) (j : ∀ i, Fin ((P i).length (a i))) :
    cell P (point P a j) = a := by
  funext i
  exact (P i).cell_point _ _

noncomputable def pointEquiv (a : ∀ i, (P i).Label) :
    (∀ i, Fin ((P i).length (a i))) ≃ ↥(partitionCell (cell P) a) :=
  (Equiv.piCongrRight (fun i => (P i).pointEquiv (a i))).trans
    (Equiv.subtypePiEquivPi.symm.trans (Equiv.subtypeEquivRight (fun x => by
      simp only [mem_partitionCell, cell, funext_iff])))

@[simp] theorem pointEquiv_val (a : ∀ i, (P i).Label) (j : ∀ i, Fin ((P i).length (a i))) :
    (pointEquiv P a j).val = point P a j := rfl

theorem expect_cell (a : ∀ i, (P i).Label) (f : (∀ i, Fin (N i)) → ℝ) :
    (𝔼 x ∈ partitionCell (cell P) a, f x) =
      𝔼 j : (∀ i, Fin ((P i).length (a i))), f (point P a j) := by
  have h := Fintype.expect_equiv (pointEquiv P a)
    (fun j => f (point P a j)) (fun x => f x.val) (fun _ => rfl)
  have hcoe : (𝔼 x : ↥(partitionCell (cell P) a), f x.val) =
      𝔼 x ∈ partitionCell (cell P) a, f x := by
    rw [Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, Fintype.card_coe,
      Finset.sum_coe_sort]
  exact hcoe.symm.trans h.symm

end Erdos3.BoxProgressionPartition

end

section

namespace Erdos3.BoxProgressionPartition

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i))

noncomputable def normalizedPoint (x : ∀ i, Fin (N i)) : ι → ℝ :=
  fun i => (x i).val / (N i : ℝ)

noncomputable def normalizedStart (a : ∀ i, (P i).Label) : ι → ℝ :=
  fun i => ((P i).start (a i) : ℝ) / N i

end Erdos3.BoxProgressionPartition

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_partition_cell_norm_mean_le {X K : Type*} [Fintype X] [Nonempty X]
    [Fintype K] (cell : X → K) (f : X → ℂ) :
    ∃ k, (partitionCell cell k).Nonempty ∧
      ‖𝔼 x, f x‖ ≤ ‖𝔼 x ∈ partitionCell cell k, f x‖ := by
  classical
  obtain ⟨x, _, hx⟩ := Finset.univ.exists_max_image
    (fun x : X => ‖𝔼 y ∈ partitionCell cell (cell x), f y‖) Finset.univ_nonempty
  have hmax (k : K) : ‖𝔼 y ∈ partitionCell cell k, f y‖ ≤
      ‖𝔼 y ∈ partitionCell cell (cell x), f y‖ := by
    by_cases hk : (partitionCell cell k).Nonempty
    · obtain ⟨y, hy⟩ := hk
      have h := hx y (Finset.mem_univ _)
      simpa only [(mem_partitionCell cell k y).mp hy] using h
    · rw [Finset.not_nonempty_iff_eq_empty.mp hk]
      simp only [Finset.expect_empty, norm_zero]
      exact norm_nonneg (𝔼 y ∈ partitionCell cell (cell x), f y)
  refine ⟨cell x, ⟨x, (mem_partitionCell cell _ _).mpr rfl⟩, ?_⟩
  have hcard : (Fintype.card X : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := X))
  rw [complex_expect_partition_count_weights cell f, card_partitionCell_sum]
  calc
    _ ≤ ∑ k, ‖(((partitionCell cell k).card : ℝ) / Fintype.card X : ℂ) *
        (𝔼 y ∈ partitionCell cell k, f y)‖ := norm_sum_le _ _
    _ ≤ ∑ k, ((partitionCell cell k).card : ℝ) / Fintype.card X *
        ‖𝔼 y ∈ partitionCell cell (cell x), f y‖ := by
      apply Finset.sum_le_sum
      intro k _
      simp only [norm_mul, norm_div, Complex.norm_real, norm_natCast]
      exact mul_le_mul_of_nonneg_left (hmax k) (by positivity)
    _ = ‖𝔼 y ∈ partitionCell cell (cell x), f y‖ := by
      rw [← Finset.sum_mul, ← Finset.sum_div, card_partitionCell_sum, div_self hcard,
        one_mul]

namespace BoxProgressionPartition

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i))

theorem expect_cell_complex (a : ∀ i, (P i).Label) (f : (∀ i, Fin (N i)) → ℂ) :
    (𝔼 x ∈ partitionCell (cell P) a, f x) =
      𝔼 j : (∀ i, Fin ((P i).length (a i))), f (point P a j) := by
  have h := Fintype.expect_equiv (pointEquiv P a)
    (fun j => f (point P a j)) (fun x => f x.val) (fun _ => rfl)
  have hcoe : (𝔼 x : ↥(partitionCell (cell P) a), f x.val) =
      𝔼 x ∈ partitionCell (cell P) a, f x := by
    rw [Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, Fintype.card_coe,
      Finset.sum_coe_sort]
  exact hcoe.symm.trans h.symm

theorem exists_positive_box_norm_mean_le (hN : ∀ i, 0 < N i) (f : (ι → ℕ) → ℂ) :
    ∃ a : ∀ i, (P i).Label, (∀ i, 0 < (P i).length (a i)) ∧
      ‖𝔼 x : (∀ i, Fin (N i)), f (fun i => (x i).val)‖ ≤
        ‖𝔼 j : (∀ i, Fin ((P i).length (a i))),
          f (fun i => (P i).start (a i) + (P i).step (a i) * (j i).val)‖ := by
  classical
  let : Nonempty (∀ i, Fin (N i)) := ⟨fun i => ⟨0, hN i⟩⟩
  obtain ⟨a, ha, hmean⟩ := exists_partition_cell_norm_mean_le (cell P)
    (fun x => f (fun i => (x i).val))
  refine ⟨a, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := ha
    let j := (pointEquiv P a).symm ⟨x, hx⟩
    exact fun i => Nat.zero_lt_of_lt (j i).isLt
  · rw [expect_cell_complex] at hmean
    simpa only [point_val] using hmean

end BoxProgressionPartition
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem short_progression_cell_mass_le {N : ℕ} (P : FiniteProgressionPartition N)
    {L : ℝ} (hL : 0 ≤ L) :
    (𝔼 n : Fin N, if ((P.length (P.cell n) : ℕ) : ℝ) < L then 1 else 0) ≤
      (Fintype.card P.Label : ℝ) * L / N := by
  classical
  let b : Fin N → ℝ := fun n => if (P.length (P.cell n) : ℝ) < L then 1 else 0
  have hcell (a : P.Label) : (∑ n ∈ partitionCell P.cell a, b n) ≤ L := by
    have heq : (∑ n ∈ partitionCell P.cell a, b n) =
        if (P.length a : ℝ) < L then (P.length a : ℝ) else 0 := by
      calc
        _ = ∑ _n ∈ partitionCell P.cell a, if (P.length a : ℝ) < L then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro n hn
          simp only [b, (mem_partitionCell _ _ _).mp hn]
        _ = _ := by split_ifs <;> simp [P.card_cell]
    rw [heq]
    split_ifs with h
    · exact h.le
    · exact hL
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset P.Label)) => hcell a)
  rw [sum_partitionCell] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin]
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg N)

theorem short_box_side_mass_le {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i)) (hN : ∀ i, 0 < N i)
    (L : ι → ℝ) (hL : ∀ i, 0 ≤ L i) :
    (𝔼 x : (∀ i, Fin (N i)), if (∀ i, L i ≤ ((P i).length ((P i).cell (x i)) : ℝ)) then 0 else 1) ≤
      ∑ i, (Fintype.card (P i).Label : ℝ) * L i / N i := by
  classical
  let : ∀ i, Nonempty (Fin (N i)) := fun i => ⟨⟨0, hN i⟩⟩
  have hpoint (x : ∀ i, Fin (N i)) :
      (if (∀ i, L i ≤ ((P i).length ((P i).cell (x i)) : ℝ)) then (0 : ℝ) else 1) ≤
        ∑ i, if ((P i).length ((P i).cell (x i)) : ℝ) < L i then 1 else 0 := by
    split_ifs with h
    · exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
    · push Not at h
      obtain ⟨i, hi⟩ := h
      have hs := Finset.single_le_sum (s := Finset.univ)
        (f := fun j => if ((P j).length ((P j).cell (x j)) : ℝ) < L j then (1 : ℝ) else 0)
        (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
      simpa only [hi, ite_true] using hs
  apply (Finset.expect_le_expect (fun x _ => hpoint x)).trans
  rw [Finset.expect_sum_comm]
  apply Finset.sum_le_sum
  intro i _
  rw [expect_coordinate (X := fun j => Fin (N j)) i
    (fun n : Fin (N i) => if ((P i).length ((P i).cell n) : ℝ) < L i then (1 : ℝ) else 0)]
  exact short_progression_cell_mass_le (P i) (hL i)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem progressionBlock_short_side_bound {N q H : ℕ} (hN : 0 < N) (hH : 0 < H)
    (hfit : q * H ≤ N) {L : ℝ} (hL : 0 ≤ L) :
    (Fintype.card (Fin q × Fin (N / q / H + 1)) : ℝ) * L / N ≤ 2 * L / H := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  apply (div_le_div_iff₀ hNr hHr).mpr
  have hc : (Fintype.card (Fin q × Fin (N / q / H + 1)) : ℝ) * H ≤ 2 * N := by
    exact_mod_cast progressionBlock_label_count_mul_le_twice hfit
  nlinarith [mul_le_mul_of_nonneg_right hc hL]

theorem boxBlock_short_side_budget {ι : Type*} [Fintype ι] (N H : ι → ℕ) (q : ℕ)
    (hN : ∀ i, 0 < N i) (hH : ∀ i, 0 < H i) (hfit : ∀ i, q * H i ≤ N i)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    (∑ i, (Fintype.card (Fin q × Fin (N i / q / H i + 1)) : ℝ) *
      (θ * H i / (2 * (Fintype.card ι + 1))) / N i) ≤ θ := by
  have hn : (0 : ℝ) < Fintype.card ι + 1 := by positivity
  calc
    _ ≤ ∑ i, 2 * (θ * H i / (2 * (Fintype.card ι + 1))) / H i := by
      apply Finset.sum_le_sum
      intro i _
      exact progressionBlock_short_side_bound (hN i) (hH i) (hfit i) (by positivity)
    _ = ∑ _i : ι, θ / (Fintype.card ι + 1) := by
      apply Finset.sum_congr rfl
      intro i _
      have hHi : (H i : ℝ) ≠ 0 := by exact_mod_cast (hH i).ne'
      field_simp
    _ ≤ θ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hn).mpr
      nlinarith

theorem exists_box_block_mesh {ι : Type*} (N : ι → ℕ) (q : ℕ) (hq : 0 < q)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hlarge : ∀ i, 2 * (q : ℝ) ≤ ρ * N i) :
    ∃ H : ι → ℕ, (∀ i, 0 < H i) ∧ (∀ i, q * H i ≤ N i) ∧
      (∀ i, (q : ℝ) * H i ≤ ρ * N i) ∧
      (∀ i, ρ * N i / (2 * q) ≤ (H i : ℝ)) := by
  let H : ι → ℕ := fun i => ⌊ρ * N i / q⌋₊
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hx (i) : 2 ≤ ρ * N i / q := (le_div_iff₀ hqr).mpr (hlarge i)
  have hlo (i) : ρ * N i / q - 1 < (H i : ℝ) := Nat.sub_one_lt_floor _
  have hhi (i) : (H i : ℝ) ≤ ρ * N i / q := Nat.floor_le (by positivity)
  have hH (i) : 0 < H i := by
    have h : (0 : ℝ) < H i := by linarith [hlo i, hx i]
    exact_mod_cast h
  have hwidth (i) : (q : ℝ) * H i ≤ ρ * N i := by
    have h := (le_div_iff₀ hqr).mp (hhi i)
    simpa only [mul_comm] using h
  refine ⟨H, hH, ?_, hwidth, ?_⟩
  · intro i
    have h := (hwidth i).trans (mul_le_of_le_one_left (Nat.cast_nonneg (N i)) hρ1)
    exact_mod_cast h
  · intro i
    have heq : ρ * N i / (2 * q) = (ρ * N i / q) / 2 := by ring
    rw [heq]
    linarith [hlo i, hx i]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.VectorPolynomialReconstruction
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

abbrev VectorPolynomial (σ R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] :=
  MvPolynomial σ R ⊗[R] V

namespace VectorPolynomial

variable {σ R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

noncomputable def coefficients : VectorPolynomial σ R V ≃ₗ[R] (σ →₀ ℕ) →₀ V := by
  classical
  exact TensorProduct.equivFinsuppOfBasisLeft (MvPolynomial.basisMonomials σ R)

noncomputable def monomial (α : σ →₀ ℕ) (v : V) : VectorPolynomial σ R V :=
  MvPolynomial.monomial α (1 : R) ⊗ₜ[R] v

@[simp] theorem coefficients_tmul (p : MvPolynomial σ R) (v : V) (α : σ →₀ ℕ) :
    coefficients (p ⊗ₜ[R] v) α = p.coeff α • v := by
  classical
  exact TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply _ _ _ _

@[simp] theorem coefficients_monomial (α : σ →₀ ℕ) (v : V) :
    coefficients (monomial (R := R) α v) = Finsupp.single α v := by
  classical
  ext β
  by_cases h : α = β
  · subst β
    simp [monomial]
  · simp [monomial, h, Ne.symm h]

@[simp] theorem coefficients_symm_single (α : σ →₀ ℕ) (v : V) :
    (coefficients (R := R)).symm (Finsupp.single α v) = monomial α v := by
  apply coefficients.injective
  simp

theorem sum_monomial_coefficients (p : VectorPolynomial σ R V) :
    (coefficients p).sum (fun α v => monomial (R := R) α v) = p := by
  classical
  exact (TensorProduct.equivFinsuppOfBasisLeft_symm_apply
    (MvPolynomial.basisMonomials σ R) (coefficients p)).symm.trans
      (coefficients.symm_apply_apply p)

noncomputable def map (f : V →ₗ[R] W) : VectorPolynomial σ R V →ₗ[R] VectorPolynomial σ R W :=
  f.lTensor (MvPolynomial σ R)

@[simp] theorem map_monomial (f : V →ₗ[R] W) (α : σ →₀ ℕ) (v : V) :
    map f (monomial α v) = monomial α (f v) := rfl

@[simp] theorem coefficients_map (f : V →ₗ[R] W) (p : VectorPolynomial σ R V)
    (α : σ →₀ ℕ) : coefficients (map f p) α = f (coefficients p α) := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q v => simp [map]
  | add p q hp hq => simp [hp, hq]

def DegreeLE (w : σ → ℕ) (d : ℕ) (p : VectorPolynomial σ R V) : Prop :=
  ∀ α, d < Finsupp.weight w α → coefficients p α = 0

theorem degreeLE_iff (w : σ → ℕ) (d : ℕ) (p : VectorPolynomial σ R V) :
    DegreeLE w d p ↔ ∀ α ∈ (coefficients p).support, Finsupp.weight w α ≤ d := by
  classical
  simp only [DegreeLE, Finsupp.mem_support_iff]
  exact ⟨fun h α hα => le_of_not_gt (fun hd => hα (h α hd)),
    fun h α hd => Classical.byContradiction (fun hα => (not_le_of_gt hd) (h α hα))⟩

theorem DegreeLE.map {w : σ → ℕ} {d : ℕ} {p : VectorPolynomial σ R V}
    (hp : DegreeLE w d p) (f : V →ₗ[R] W) : DegreeLE w d (map f p) := by
  intro α hα
  rw [coefficients_map, hp α hα, f.map_zero]

theorem degreeLE_map_iff (w : σ → ℕ) (d : ℕ) (f : V →ₗ[R] W)
    (hf : Function.Injective f) (p : VectorPolynomial σ R V) :
    DegreeLE w d (map f p) ↔ DegreeLE w d p := by
  refine ⟨fun h α hα => hf ?_, fun h => h.map f⟩
  simpa only [coefficients_map, f.map_zero] using h α hα

noncomputable def eval (x : σ → R) : VectorPolynomial σ R V →ₗ[R] V :=
  (TensorProduct.lid R V).toLinearMap.comp
    ((MvPolynomial.aeval x).toLinearMap.rTensor V)

@[simp] theorem eval_tmul (x : σ → R) (q : MvPolynomial σ R) (v : V) :
    eval x (q ⊗ₜ[R] v) = MvPolynomial.aeval x q • v := rfl

@[simp] theorem eval_monomial (x : σ → R) (α : σ →₀ ℕ) (v : V) :
    eval x (monomial α v) = (α.prod fun i n => x i ^ n) • v := by
  simp [monomial, MvPolynomial.eval_monomial]

@[simp] theorem eval_map (x : σ → R) (f : V →ₗ[R] W) (p : VectorPolynomial σ R V) :
    eval x (map f p) = f (eval x p) := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q v => simp [map]
  | add p q hp hq => simp [hp, hq]

end VectorPolynomial
end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

noncomputable def monomialScale {σ : Type*} (T : σ → ℝ) (α : σ →₀ ℕ) : ℝ :=
  α.prod (fun i n => T i ^ n)

@[simp] theorem monomialScale_zero {σ : Type*} (T : σ → ℝ) : monomialScale T 0 = 1 := by
  simp [monomialScale]

theorem monomialScale_pos {σ : Type*} (T : σ → ℝ) (hT : ∀ i, 0 < T i) (α : σ →₀ ℕ) :
    0 < monomialScale T α := by
  classical
  exact Finset.prod_pos (fun i _ => pow_pos (hT i) _)

theorem one_le_monomialScale {σ : Type*} (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i) (α : σ →₀ ℕ) :
    1 ≤ monomialScale T α := by
  classical
  exact Finset.one_le_prod (fun index _ => one_le_pow₀ (hT index))

theorem le_monomialScale_of_ne_zero {σ : Type*} (T : σ → ℝ) {R : ℝ}
    (hR : 1 ≤ R) (hT : ∀ i, R ≤ T i) {α : σ →₀ ℕ} (hα : α ≠ 0) :
    R ≤ monomialScale T α := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hα
    ext i
    exact hn i
  have hTi : 1 ≤ T i := hR.trans (hT i)
  have hp : T i ≤ T i ^ α i := by
    simpa only [pow_one] using pow_le_pow_right₀ hTi (Nat.one_le_iff_ne_zero.mpr hi)
  have hs : ({i} : Finset σ) ⊆ α.support :=
    Finset.singleton_subset_iff.mpr (Finsupp.mem_support_iff.mpr hi)
  have hprod := Finset.prod_le_prod_of_subset_of_one_le hs
    (fun index _ => pow_nonneg (zero_le_one.trans (hR.trans (hT index))) (α index))
    (fun index _ _ => one_le_pow₀ (hR.trans (hT index)))
  exact (hT i).trans (hp.trans (by
    simpa only [Finset.prod_singleton, monomialScale, Finsupp.prod] using hprod))

theorem monomialScale_add {σ : Type*} (T : σ → ℝ) (α β : σ →₀ ℕ) :
    monomialScale T (α + β) = monomialScale T α * monomialScale T β := by
  classical
  exact Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

variable {σ V : Type*} [AddCommGroup V] [Module ℚ V]

noncomputable def multiplyVariable (i : σ) :
    VectorPolynomial σ ℚ V →ₗ[ℚ] VectorPolynomial σ ℚ V :=
  (LinearMap.mulLeft ℚ (MvPolynomial.X i : MvPolynomial σ ℚ)).rTensor V

@[simp] theorem multiplyVariable_tmul (i : σ) (P : MvPolynomial σ ℚ) (v : V) :
    multiplyVariable i (P ⊗ₜ[ℚ] v) = (MvPolynomial.X i * P) ⊗ₜ[ℚ] v := rfl

theorem coefficients_multiplyVariable [DecidableEq σ] (i : σ)
    (P : VectorPolynomial σ ℚ V) (β : σ →₀ ℕ) :
    coefficients (multiplyVariable i P) β =
      if i ∈ β.support then coefficients P (β - Finsupp.single i 1) else 0 := by
  induction P using TensorProduct.induction_on with
  | zero => simp
  | tmul p v =>
    rw [multiplyVariable_tmul, coefficients_tmul, MvPolynomial.coeff_X_mul', coefficients_tmul]
    split_ifs <;> simp
  | add P Q hP hQ =>
    simp only [map_add, Finsupp.add_apply, hP, hQ]
    split_ifs <;> simp

noncomputable def eulerSum [Fintype σ] :
    VectorPolynomial σ ℚ V →ₗ[ℚ] VectorPolynomial σ ℚ V :=
  ∑ i, (multiplyVariable i).comp ((MvPolynomial.pderiv i).toLinearMap.rTensor V)

theorem eulerSum_monomial [Fintype σ] (β : σ →₀ ℕ) (v : V) :
    eulerSum (monomial (R := ℚ) β v) =
      (Finsupp.weight (fun _ : σ => (1 : ℕ)) β : ℚ) • monomial β v := by
  have hdegree : β.degree = Finsupp.weight (fun _ : σ => (1 : ℕ)) β :=
    DFunLike.congr_fun Finsupp.degree_eq_weight_one β
  have h := (MvPolynomial.isHomogeneous_monomial (1 : ℚ) hdegree).sum_X_mul_pderiv
  simp only [eulerSum, LinearMap.sum_apply, LinearMap.comp_apply, monomial,
    LinearMap.rTensor_tmul, multiplyVariable_tmul]
  change (∑ i, (MvPolynomial.X i * MvPolynomial.pderiv i (MvPolynomial.monomial β (1 : ℚ))) ⊗ₜ[ℚ] v) = _
  rw [← TensorProduct.sum_tmul, h]
  simp only [Nat.cast_smul_eq_nsmul, TensorProduct.smul_tmul']

theorem eulerSum_eq_degree_smul [Fintype σ] (d : ℕ) (P : VectorPolynomial σ ℚ V)
    (hP : ∀ β, Finsupp.weight (fun _ : σ => (1 : ℕ)) β ≠ d → coefficients P β = 0) :
    eulerSum P = (d : ℚ) • P := by
  classical
  conv_lhs => rw [← sum_monomial_coefficients P]
  conv_rhs => rw [← sum_monomial_coefficients P]
  simp only [Finsupp.sum, map_sum, eulerSum_monomial, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro β hβ
  have he : Finsupp.weight (fun _ : σ => (1 : ℕ)) β = d := by
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hβ) (hP β hn)
  rw [he]

noncomputable def reconstructDerivatives [Fintype σ] (d : ℕ) :
    (σ → VectorPolynomial σ ℚ V) →ₗ[ℚ] VectorPolynomial σ ℚ V :=
  (d : ℚ)⁻¹ • ∑ i, (multiplyVariable i).comp (LinearMap.proj i)

theorem reconstructDerivatives_apply [Fintype σ] (d : ℕ)
    (P : σ → VectorPolynomial σ ℚ V) :
    reconstructDerivatives d P = (d : ℚ)⁻¹ • ∑ i, multiplyVariable i (P i) := by
  simp only [reconstructDerivatives, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]

theorem reconstructDerivatives_partial [Fintype σ] {d : ℕ} (hd : 0 < d)
    (P : VectorPolynomial σ ℚ V)
    (hP : ∀ β, Finsupp.weight (fun _ : σ => (1 : ℕ)) β ≠ d → coefficients P β = 0) :
    reconstructDerivatives d (fun i => (MvPolynomial.pderiv i).toLinearMap.rTensor V P) = P := by
  rw [reconstructDerivatives_apply]
  have he := eulerSum_eq_degree_smul d P hP
  simp only [eulerSum, LinearMap.sum_apply, LinearMap.comp_apply] at he
  rw [he, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hd.ne'), one_smul]

theorem coefficients_reconstructDerivatives [Fintype σ] [DecidableEq σ] (d : ℕ)
    (P : σ → VectorPolynomial σ ℚ V) (β : σ →₀ ℕ) :
    coefficients (reconstructDerivatives d P) β =
      (d : ℚ)⁻¹ • ∑ i, if i ∈ β.support then coefficients (P i) (β - Finsupp.single i 1) else 0 := by
  rw [reconstructDerivatives_apply]
  simp only [map_smul, Finsupp.smul_apply, map_sum, Finsupp.finsetSum_apply,
    coefficients_multiplyVariable]

theorem reconstructDerivatives_mem [Fintype σ] (W : Submodule ℚ V) (d : ℕ)
    (P : σ → VectorPolynomial σ ℚ V)
    (hP : ∀ i β, coefficients (P i) β ∈ W) :
    ∀ β, coefficients (reconstructDerivatives d P) β ∈ W := by
  classical
  intro β
  rw [coefficients_reconstructDerivatives]
  apply W.smul_mem
  apply W.sum_mem
  intro i _
  split_ifs
  · exact hP i _
  · exact W.zero_mem

theorem reconstructDerivatives_homogeneous [Fintype σ] {d : ℕ} (hd : 0 < d)
    (P : σ → VectorPolynomial σ ℚ V)
    (hP : ∀ i β, Finsupp.weight (fun _ : σ => (1 : ℕ)) β ≠ d - 1 → coefficients (P i) β = 0) :
    ∀ β, Finsupp.weight (fun _ : σ => (1 : ℕ)) β ≠ d →
      coefficients (reconstructDerivatives d P) β = 0 := by
  classical
  intro β hβ
  rw [coefficients_reconstructDerivatives]
  suffices (∑ i, if i ∈ β.support then coefficients (P i) (β - Finsupp.single i 1) else 0) = 0 by
    rw [this, smul_zero]
  apply Finset.sum_eq_zero
  intro i _
  split_ifs with hi
  · apply hP
    have hw := Finsupp.weight_sub_single_add (w := fun _ : σ => (1 : ℕ))
      (Finsupp.mem_support_iff.mp hi)
    omega
  · rfl

theorem homogeneous_derivative_split_mod [Fintype σ] (W : Submodule ℚ V)
    {d : ℕ} (hd : 0 < d) (P : VectorPolynomial σ ℚ V)
    (hP : ∀ β, Finsupp.weight (fun _ : σ => (1 : ℕ)) β ≠ d → coefficients P β = 0)
    (S R : σ → VectorPolynomial σ ℚ V)
    (hsplit : ∀ i β, coefficients
      ((MvPolynomial.pderiv i).toLinearMap.rTensor V P - S i - R i) β ∈ W) :
    ∀ β, coefficients (P - reconstructDerivatives d S - reconstructDerivatives d R) β ∈ W := by
  let D : σ → VectorPolynomial σ ℚ V := fun i => (MvPolynomial.pderiv i).toLinearMap.rTensor V P
  have he : reconstructDerivatives d (D - S - R) =
      P - reconstructDerivatives d S - reconstructDerivatives d R := by
    rw [map_sub, map_sub, reconstructDerivatives_partial hd P hP]
  rw [← he]
  exact reconstructDerivatives_mem W d (D - S - R) hsplit

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped TensorProduct

variable {σ ι R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

noncomputable def coefficientTensorBasis (b : Basis ι R V) :
    Basis ((σ →₀ ℕ) × ι) R (VectorPolynomial σ R V) :=
  (MvPolynomial.basisMonomials σ R).tensorProduct b

@[simp] theorem coefficientTensorBasis_apply (b : Basis ι R V) (α : σ →₀ ℕ) (i : ι) :
    coefficientTensorBasis b (α, i) = monomial α (b i) := by
  simp [coefficientTensorBasis, monomial]

theorem coefficientTensorBasis_repr (b : Basis ι R V) (p : VectorPolynomial σ R V)
    (α : σ →₀ ℕ) (i : ι) :
    (coefficientTensorBasis b).repr p (α, i) = b.repr (coefficients p α) i := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q v =>
      simp only [coefficientTensorBasis, Basis.tensorProduct_repr_tmul_apply, coefficients_tmul,
        map_smul, Finsupp.smul_apply, smul_eq_mul]
      change b.repr v i * q.coeff α = q.coeff α * b.repr v i
      exact mul_comm _ _
  | add p q hp hq =>
      simp only [map_add, Finsupp.add_apply, hp, hq]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {σ ι R S V : Type*} [CommRing R] [CommRing S] [AddCommGroup V] [Module R V]

noncomputable def coordinate (f : V →+ S) (p : VectorPolynomial σ R V) : MvPolynomial σ S :=
  (MvPolynomial.basisMonomials σ S).repr.symm ((coefficients p).mapRange f f.map_zero)

@[simp] theorem coeff_coordinate (f : V →+ S) (p : VectorPolynomial σ R V) (α : σ →₀ ℕ) :
    (coordinate f p).coeff α = f (coefficients p α) := by
  change ((MvPolynomial.basisMonomials σ S).repr
    ((MvPolynomial.basisMonomials σ S).repr.symm _)) α = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

@[simp] theorem coordinate_monomial (f : V →+ S) (α : σ →₀ ℕ) (v : V) :
    coordinate f (monomial (R := R) α v) = MvPolynomial.monomial α (f v) := by
  classical
  ext β
  by_cases h : α = β
  · subst β
    simp
  · simp [h, Ne.symm h]

@[simp] theorem coordinate_sum {κ : Type*} (f : V →+ S) (u : Finset κ)
    (p : κ → VectorPolynomial σ R V) :
    coordinate f (∑ i ∈ u, p i) = ∑ i ∈ u, coordinate f (p i) := by
  ext α
  simp only [coeff_coordinate, map_sum, Finsupp.finsetSum_apply, MvPolynomial.coeff_sum]

theorem scalar_weightedDegree_le_iff (w : σ → ℕ) (d : ℕ) (p : MvPolynomial σ S) :
    p.weightedTotalDegree w ≤ d ↔
      ∀ α, d < Finsupp.weight w α → p.coeff α = 0 := by
  classical
  simp only [MvPolynomial.weightedTotalDegree, Finset.sup_le_iff,
    MvPolynomial.mem_support_iff]
  exact ⟨fun h α hd => Classical.byContradiction (fun hα => (not_le_of_gt hd) (h α hα)),
    fun h α hα => le_of_not_gt (fun hd => hα (h α hd))⟩

theorem degreeLE_iff_coordinates (w : σ → ℕ) (d : ℕ)
    (f : ι → V →+ S) (hsep : ∀ v, (∀ i, f i v = 0) → v = 0)
    (p : VectorPolynomial σ R V) :
    DegreeLE w d p ↔ ∀ i, (coordinate (f i) p).weightedTotalDegree w ≤ d := by
  simp only [scalar_weightedDegree_le_iff, coeff_coordinate]
  constructor
  · intro hp i α hα
    rw [hp α hα, map_zero]
  · intro hp α hα
    exact hsep _ (fun i => hp i α hα)

theorem degreeLE_iff_basis_coordinates [Module S V]
    (e : Module.Basis ι S V) (w : σ → ℕ) (d : ℕ) (p : VectorPolynomial σ R V) :
    DegreeLE w d p ↔
      ∀ i, (coordinate (e.coord i).toAddMonoidHom p).weightedTotalDegree w ≤ d := by
  apply degreeLE_iff_coordinates
  intro v hv
  apply e.repr.injective
  ext i
  have hi : (e.coord i) v = 0 := hv i
  simpa only [map_zero, Finsupp.zero_apply, Module.Basis.coord_apply] using hi

theorem degreeLE_one_iff_basis_totalDegree [Module S V]
    (e : Module.Basis ι S V) (d : ℕ) (p : VectorPolynomial σ R V) :
    DegreeLE (1 : σ → ℕ) d p ↔
      ∀ i, (coordinate (e.coord i).toAddMonoidHom p).totalDegree ≤ d := by
  simpa only [MvPolynomial.weightedTotalDegree_one] using
    degreeLE_iff_basis_coordinates e (1 : σ → ℕ) d p

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

noncomputable def pair (p : VectorPolynomial σ R V) (q : VectorPolynomial σ R W) :
    VectorPolynomial σ R (V × W) :=
  map (LinearMap.inl R V W) p + map (LinearMap.inr R V W) q

@[simp] theorem coefficients_pair (p : VectorPolynomial σ R V) (q : VectorPolynomial σ R W)
    (α : σ →₀ ℕ) : coefficients (pair p q) α = (coefficients p α, coefficients q α) := by
  simp [pair]

@[simp] theorem eval_pair (p : VectorPolynomial σ R V) (q : VectorPolynomial σ R W) (x : σ → R) :
    eval x (pair p q) = (eval x p, eval x q) := by
  simp [pair]

noncomputable def restrictCoefficients (P : Submodule R V) (p : VectorPolynomial σ R V)
    (hp : ∀ α, coefficients p α ∈ P) : VectorPolynomial σ R P :=
  coefficients.symm
    { support := (coefficients p).support
      toFun α := ⟨coefficients p α, hp α⟩
      mem_support_toFun := by intro α; simp }

@[simp] theorem coefficients_restrictCoefficients (P : Submodule R V) (p : VectorPolynomial σ R V)
    (hp : ∀ α, coefficients p α ∈ P) (α : σ →₀ ℕ) :
    (coefficients (restrictCoefficients P p hp) α : V) = coefficients p α := by
  simp only [restrictCoefficients, LinearEquiv.apply_symm_apply]
  rfl

@[simp] theorem map_restrictCoefficients (P : Submodule R V) (p : VectorPolynomial σ R V)
    (hp : ∀ α, coefficients p α ∈ P) : map P.subtype (restrictCoefficients P p hp) = p := by
  apply coefficients.injective
  ext α
  rw [coefficients_map]
  exact coefficients_restrictCoefficients P p hp α

theorem eval_restrictCoefficients (P : Submodule R V) (p : VectorPolynomial σ R V)
    (hp : ∀ α, coefficients p α ∈ P) (x : σ → R) :
    (eval (V := P) x (restrictCoefficients P p hp) : V) = eval x p := by
  change P.subtype (eval x (restrictCoefficients P p hp)) = _
  rw [← eval_map, map_restrictCoefficients]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {σ R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

def coefficientSupport (S : Set (σ →₀ ℕ)) : Submodule R (VectorPolynomial σ R V) where
  carrier := {p | ∀ a, a ∉ S → coefficients p a = 0}
  zero_mem' := by simp
  add_mem' hp hq := by
    intro a ha
    simp only [map_add, Finsupp.add_apply, hp a ha, hq a ha, add_zero]
  smul_mem' c p hp := by
    intro a ha
    simp only [map_smul, Finsupp.smul_apply, hp a ha, smul_zero]

@[simp] theorem mem_coefficientSupport (S : Set (σ →₀ ℕ)) (p : VectorPolynomial σ R V) :
    p ∈ coefficientSupport S ↔ ∀ a, a ∉ S → coefficients p a = 0 := Iff.rfl

theorem monomial_mem_coefficientSupport {S : Set (σ →₀ ℕ)} {a : σ →₀ ℕ}
    (ha : a ∈ S) (v : V) : monomial (R := R) a v ∈ coefficientSupport S := by
  classical
  intro b hb
  have hab : a ≠ b := by rintro rfl; exact hb ha
  simp [hab]

@[simp] theorem coefficientSupport_empty :
    coefficientSupport (R := R) (V := V) (∅ : Set (σ →₀ ℕ)) = ⊥ := by
  apply bot_unique
  intro p hp
  apply coefficients.injective
  ext a
  exact hp a (Set.notMem_empty a)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {σ ι R S V : Type*} [CommRing R] [CommRing S]
  [AddCommGroup V] [Module R V]

noncomputable def ofScalar (f : S →+ V) (p : MvPolynomial σ S) : VectorPolynomial σ R V :=
  coefficients.symm (((MvPolynomial.basisMonomials σ S).repr p).mapRange f f.map_zero)

@[simp] theorem coefficients_ofScalar (f : S →+ V) (p : MvPolynomial σ S) (α : σ →₀ ℕ) :
    coefficients (ofScalar (R := R) f p) α = f (p.coeff α) := by
  simp only [ofScalar, LinearEquiv.apply_symm_apply, Finsupp.mapRange_apply]
  rfl

variable [Fintype ι] [Module S V]

noncomputable def ofCoordinates (e : Module.Basis ι S V) (p : ι → MvPolynomial σ S) :
    VectorPolynomial σ R V :=
  ∑ i, ofScalar ((LinearMap.id : S →ₗ[S] S).smulRight (e i)).toAddHom (p i)

theorem coefficients_ofCoordinates (e : Module.Basis ι S V)
    (p : ι → MvPolynomial σ S) (α : σ →₀ ℕ) :
    coefficients (ofCoordinates (R := R) e p) α = ∑ index, (p index).coeff α • e index := by
  simp [ofCoordinates]

@[simp] theorem coordinate_ofCoordinates (e : Module.Basis ι S V)
    (p : ι → MvPolynomial σ S) (i : ι) :
    coordinate (e.coord i).toAddMonoidHom (ofCoordinates (R := R) e p) = p i := by
  classical
  ext α
  rw [coeff_coordinate, coefficients_ofCoordinates]
  change e.coord i (∑ index, (p index).coeff α • e index) = _
  simp [Module.Basis.coord_apply, Finsupp.single_apply, mul_ite]

@[simp] theorem ofCoordinates_coordinate (e : Module.Basis ι S V)
    (p : VectorPolynomial σ R V) :
    ofCoordinates e (fun i => coordinate (e.coord i).toAddMonoidHom p) = p := by
  apply coefficients.injective
  ext α
  rw [coefficients_ofCoordinates]
  simp only [coeff_coordinate]
  change (∑ i, e.repr (coefficients p α) i • e i) = coefficients p α
  exact e.sum_repr _

noncomputable def coordinatesEquiv (e : Module.Basis ι S V) :
    VectorPolynomial σ R V ≃ (ι → MvPolynomial σ S) where
  toFun p i := coordinate (e.coord i).toAddMonoidHom p
  invFun := ofCoordinates e
  left_inv := ofCoordinates_coordinate e
  right_inv p := funext (coordinate_ofCoordinates e p)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MixedWeightedPolynomialRename
namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped Pointwise

variable {σ R : Type*} [CommRing R]

noncomputable def polynomialTranslate (h : σ → R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  MvPolynomial.aeval (fun i => X i + C (h i))

@[simp] theorem polynomialTranslate_X (h : σ → R) (i : σ) :
    polynomialTranslate h (X i) = X i + C (h i) := by simp [polynomialTranslate]

@[simp] theorem polynomialTranslate_C (h : σ → R) (r : R) :
    polynomialTranslate h (C r) = C r := by simp [polynomialTranslate]

noncomputable def weightedSupportLE (w : σ → ℕ) (d : ℕ) : Submodule R (MvPolynomial σ R) :=
  MvPolynomial.restrictSupport R {α | Finsupp.weight w α ≤ d}

noncomputable def weightedSupportLT (w : σ → ℕ) (d : ℕ) : Submodule R (MvPolynomial σ R) :=
  MvPolynomial.restrictSupport R {α | Finsupp.weight w α < d}

theorem weightedSupportLE_monomial (w : σ → ℕ) (α : σ →₀ ℕ) (r : R) :
    monomial α r ∈ weightedSupportLE w (Finsupp.weight w α) := by
  apply (monomial_mem_restrictSupport R).mpr
  left
  change Finsupp.weight w α ≤ Finsupp.weight w α
  exact le_rfl

theorem weightedSupportLE_mul {w : σ → ℕ} {d e : ℕ} {p q : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLE w d) (hq : q ∈ weightedSupportLE w e) :
    p * q ∈ weightedSupportLE w (d + e) := by
  classical
  intro α hα
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hα)
  exact (map_add (Finsupp.weight w) β γ).trans_le (Nat.add_le_add (hp hβ) (hq hγ))

theorem weightedSupportLT_mul_LE {w : σ → ℕ} {d e : ℕ} {p q : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLT w d) (hq : q ∈ weightedSupportLE w e) :
    p * q ∈ weightedSupportLT w (d + e) := by
  classical
  intro α hα
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hα)
  exact (map_add (Finsupp.weight w) β γ).trans_lt (Nat.add_lt_add_of_lt_of_le (hp hβ) (hq hγ))

theorem weightedSupportLE_mul_LT {w : σ → ℕ} {d e : ℕ} {p q : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLE w d) (hq : q ∈ weightedSupportLT w e) :
    p * q ∈ weightedSupportLT w (d + e) := by
  rw [mul_comm, Nat.add_comm]
  exact weightedSupportLT_mul_LE hq hp

theorem translation_bounds_mul (h : σ → R) (w : σ → ℕ)
    (p q : MvPolynomial σ R) (d e : ℕ)
    (hp : p ∈ weightedSupportLE w d)
    (htp : polynomialTranslate h p ∈ weightedSupportLE w d)
    (htq : polynomialTranslate h q ∈ weightedSupportLE w e)
    (hdp : polynomialTranslate h p - p ∈ weightedSupportLT w d)
    (hdq : polynomialTranslate h q - q ∈ weightedSupportLT w e) :
    polynomialTranslate h (p * q) ∈ weightedSupportLE w (d + e) ∧
      polynomialTranslate h (p * q) - p * q ∈ weightedSupportLT w (d + e) := by
  refine ⟨by rw [map_mul]; exact weightedSupportLE_mul htp htq, ?_⟩
  rw [map_mul, show polynomialTranslate h p * polynomialTranslate h q - p * q =
    (polynomialTranslate h p - p) * polynomialTranslate h q + p * (polynomialTranslate h q - q) by ring]
  exact (weightedSupportLT w (d + e)).add_mem (weightedSupportLT_mul_LE hdp htq)
    (weightedSupportLE_mul_LT hp hdq)

theorem polynomialTranslate_monomial_bounds (h : σ → R) (w : σ → ℕ)
    (hw : ∀ i, 0 < w i) (α : σ →₀ ℕ) :
    polynomialTranslate h (monomial α 1) ∈ weightedSupportLE w (Finsupp.weight w α) ∧
      polynomialTranslate h (monomial α 1) - monomial α 1 ∈
        weightedSupportLT w (Finsupp.weight w α) := by
  classical
  have hX (i : σ) : polynomialTranslate h (X i) ∈ weightedSupportLE w (w i) ∧
      polynomialTranslate h (X i) - X i ∈ weightedSupportLT w (w i) := by
    have hi : (X i : MvPolynomial σ R) ∈ weightedSupportLE w (w i) := by
      simpa only [X, Finsupp.weight_single, one_smul] using weightedSupportLE_monomial w (Finsupp.single i 1) (1 : R)
    have hc : (C (h i) : MvPolynomial σ R) ∈ weightedSupportLE w (w i) := by
      exact (monomial_mem_restrictSupport R).mpr (Or.inl (by simp))
    refine ⟨by rw [polynomialTranslate_X]; exact (weightedSupportLE w _).add_mem hi hc, ?_⟩
    rw [polynomialTranslate_X, add_sub_cancel_left]
    exact (monomial_mem_restrictSupport R).mpr (Or.inl (by simpa using hw i))
  have hsingle (i : σ) (n : ℕ) :
      polynomialTranslate h (monomial (Finsupp.single i n) 1) ∈ weightedSupportLE w (n * w i) ∧
      polynomialTranslate h (monomial (Finsupp.single i n) 1) - monomial (Finsupp.single i n) 1 ∈
        weightedSupportLT w (n * w i) := by
    induction n with
    | zero =>
      rw [Finsupp.single_zero, zero_mul]
      change polynomialTranslate h 1 ∈ weightedSupportLE w 0 ∧
        polynomialTranslate h 1 - 1 ∈ weightedSupportLT w 0
      rw [map_one, sub_self]
      exact ⟨by simpa using weightedSupportLE_monomial w (0 : σ →₀ ℕ) (1 : R), Submodule.zero_mem _⟩
    | succ n ih =>
      have hp := weightedSupportLE_monomial w (Finsupp.single i n) (1 : R)
      simp only [Finsupp.weight_single, smul_eq_mul] at hp
      have hh := translation_bounds_mul h w (monomial (Finsupp.single i n) 1) (X i)
        (n * w i) (w i) hp ih.1 (hX i).1 ih.2 (hX i).2
      simpa only [X, MvPolynomial.monomial_mul, one_mul, ← Finsupp.single_add, Nat.succ_mul] using hh
  induction α using Finsupp.induction with
  | zero =>
    change polynomialTranslate h 1 ∈ weightedSupportLE w 0 ∧
      polynomialTranslate h 1 - 1 ∈ weightedSupportLT w 0
    rw [map_one, sub_self]
    exact ⟨by simpa using weightedSupportLE_monomial w (0 : σ →₀ ℕ) (1 : R), Submodule.zero_mem _⟩
  | @single_add i n α hi hn ih =>
    have hp := weightedSupportLE_monomial w (Finsupp.single i n) (1 : R)
    have hh := translation_bounds_mul h w (monomial (Finsupp.single i n) 1) (monomial α 1)
      (Finsupp.weight w (Finsupp.single i n)) (Finsupp.weight w α) hp
      (by simpa only [Finsupp.weight_single, smul_eq_mul] using (hsingle i n).1) ih.1
      (by simpa only [Finsupp.weight_single, smul_eq_mul] using (hsingle i n).2) ih.2
    simpa only [MvPolynomial.monomial_mul, one_mul, map_add] using hh

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Pointwise

variable {σ : Type*}

noncomputable def polynomialDegreeGap (k d : ℕ) : Submodule ℚ (MvPolynomial σ ℚ) :=
  MvPolynomial.restrictSupport ℚ {α | Finsupp.weight (fun _ => 1) α + k ≤ d}

theorem polynomialDegreeGap_monomial (α : σ →₀ ℕ) (c : ℚ) :
    monomial α c ∈ polynomialDegreeGap 0 (Finsupp.weight (fun _ => 1) α) :=
  (monomial_mem_restrictSupport ℚ).mpr (Or.inl (by simp))

theorem polynomialDegreeGap_mul {i j d e : ℕ} {p q : MvPolynomial σ ℚ}
    (hp : p ∈ polynomialDegreeGap i d) (hq : q ∈ polynomialDegreeGap j e) :
    p * q ∈ polynomialDegreeGap (i + j) (d + e) := by
  classical
  intro α hα
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hα)
  have hb := hp hβ
  have hc := hq hγ
  change Finsupp.weight (fun _ : σ => 1) β + i ≤ d at hb
  change Finsupp.weight (fun _ : σ => 1) γ + j ≤ e at hc
  change Finsupp.weight (fun _ : σ => 1) (β + γ) + (i + j) ≤ d + e
  rw [map_add]
  omega

theorem polynomialDegreeGap_pderiv {k d : ℕ} {p : MvPolynomial σ ℚ}
    (hp : p ∈ polynomialDegreeGap k d) (i : σ) :
    MvPolynomial.pderiv i p ∈ polynomialDegreeGap (k + 1) d := by
  classical
  intro α hα
  change α ∈ (MvPolynomial.pderiv i p).support at hα
  have hn : p.coeff (α + Finsupp.single i 1) ≠ 0 := by
    intro hz
    have hc : (MvPolynomial.pderiv i p).coeff α ≠ 0 := MvPolynomial.mem_support_iff.mp hα
    rw [MvPolynomial.coeff_pderiv, hz, zero_mul] at hc
    exact hc rfl
  have hh := hp (MvPolynomial.mem_support_iff.mpr hn)
  change Finsupp.weight (fun _ : σ => 1) (α + Finsupp.single i 1) + k ≤ d at hh
  simp only [map_add, Finsupp.weight_single, one_smul] at hh
  change Finsupp.weight (fun _ : σ => 1) α + (k + 1) ≤ d
  omega

noncomputable def scalarDirectionalDerivative [Fintype σ] (h : σ → ℚ) :
    Derivation ℚ (MvPolynomial σ ℚ) (MvPolynomial σ ℚ) :=
  ∑ i, h i • MvPolynomial.pderiv i

theorem scalarDirectionalDerivative_apply [Fintype σ] (h : σ → ℚ) (p : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative h p = ∑ i, h i • MvPolynomial.pderiv i p := by
  change (Derivation.coeFnAddMonoidHom (∑ i, h i • MvPolynomial.pderiv i)) p = _
  rw [map_sum]
  simp only [Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply]

@[simp] theorem scalarDirectionalDerivative_C [Fintype σ] (h : σ → ℚ) (c : ℚ) :
    scalarDirectionalDerivative h (C c) = 0 := MvPolynomial.derivation_C _ _

@[simp] theorem scalarDirectionalDerivative_X [Fintype σ] (h : σ → ℚ) (j : σ) :
    scalarDirectionalDerivative h (X j) = C (h j) := by
  classical
  simp [scalarDirectionalDerivative_apply, MvPolynomial.pderiv_X, Pi.single_apply, MvPolynomial.C_eq_smul_one]

theorem scalarDirectionalDerivative_mul [Fintype σ] (h : σ → ℚ) (p q : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative h (p * q) = scalarDirectionalDerivative h p * q +
      p * scalarDirectionalDerivative h q := by
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

theorem polynomialDegreeGap_directionalDerivative [Fintype σ] (h : σ → ℚ)
    {k d : ℕ} {p : MvPolynomial σ ℚ} (hp : p ∈ polynomialDegreeGap k d) :
    scalarDirectionalDerivative h p ∈ polynomialDegreeGap (k + 1) d := by
  rw [scalarDirectionalDerivative_apply]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (polynomialDegreeGap_pderiv hp i))

theorem polynomialDegreeGap_translate_monomial (h : σ → ℚ) (α : σ →₀ ℕ) :
    polynomialTranslate h (monomial α 1) ∈ polynomialDegreeGap 0 (Finsupp.weight (fun _ => 1) α) := by
  intro β hβ
  simpa only [Nat.add_zero] using
    (polynomialTranslate_monomial_bounds h (fun _ => 1) (by simp) α).1 hβ

theorem polynomialDegreeGap_translate_sub_monomial (h : σ → ℚ) (α : σ →₀ ℕ) :
    polynomialTranslate h (monomial α 1) - monomial α 1 ∈
      polynomialDegreeGap 1 (Finsupp.weight (fun _ => 1) α) := by
  intro β hβ
  exact Nat.succ_le_of_lt ((polynomialTranslate_monomial_bounds h (fun _ => 1) (by simp) α).2 hβ)

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ R S : Type*} [CommRing R] [CommRing S]

theorem eval₂_eq_of_weightedSupport (φ : R →+* S)
    {w : σ → ℕ} {d : ℕ} {P : MvPolynomial σ R}
    (hP : P ∈ weightedSupportLE w d) (x y : σ → S)
    (hxy : ∀ i, w i ≤ d → x i = y i) :
    eval₂ φ x P = eval₂ φ y P := by
  apply MvPolynomial.eval₂_congr φ x y
  intro i α hi hα
  exact hxy i ((Finsupp.le_weight_of_ne_zero' w
    (Finsupp.mem_support_iff.mp hi)).trans (hP (MvPolynomial.mem_support_iff.mpr hα)))

theorem aeval_eq_of_weightedSupportLE [Algebra R S]
    {w : σ → ℕ} {d : ℕ} {P : MvPolynomial σ R}
    (hP : P ∈ weightedSupportLE w d) (x y : σ → S)
    (hxy : ∀ i, w i ≤ d → x i = y i) : aeval x P = aeval y P :=
  eval₂_eq_of_weightedSupport (algebraMap R S) hP x y hxy

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {σ τ R : Type*} [CommRing R]

theorem weightedSupportLE_mono {w : σ → ℕ} {d e : ℕ} {p : MvPolynomial σ R}
    (hde : d ≤ e) (hp : p ∈ weightedSupportLE w d) : p ∈ weightedSupportLE w e :=
  fun _ h => (hp h).trans hde

theorem weightedSupportLE_C (w : σ → ℕ) (d : ℕ) (r : R) :
    C r ∈ weightedSupportLE w d := by
  exact (monomial_mem_restrictSupport R).mpr (Or.inl (by simp))

theorem weightedSupportLE_X (w : σ → ℕ) (i : σ) :
    (X i : MvPolynomial σ R) ∈ weightedSupportLE w (w i) := by
  simpa only [X, Finsupp.weight_single, one_smul] using
    weightedSupportLE_monomial w (Finsupp.single i 1) (1 : R)

theorem weightedSupportLE_pow {w : σ → ℕ} {d : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLE w d) (n : ℕ) :
    p ^ n ∈ weightedSupportLE w (n * d) := by
  induction n with
  | zero => simpa using weightedSupportLE_C w 0 (1 : R)
  | succ n ih =>
    simpa only [pow_succ, Nat.succ_mul] using weightedSupportLE_mul ih hp

theorem weightedSupportLE_prod {ι : Type*} (s : Finset ι) (w : σ → ℕ)
    (f : ι → MvPolynomial σ R) (d : ι → ℕ)
    (hf : ∀ i ∈ s, f i ∈ weightedSupportLE w (d i)) :
    (∏ i ∈ s, f i) ∈ weightedSupportLE w (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using weightedSupportLE_C w 0 (1 : R)
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact weightedSupportLE_mul (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem weightedSupportLE_aeval_monomial (w : σ → ℕ) (v : τ → ℕ)
    (f : σ → MvPolynomial τ R) (hf : ∀ i, f i ∈ weightedSupportLE v (w i))
    (α : σ →₀ ℕ) (r : R) :
    aeval (R := R) f (monomial α r) ∈ weightedSupportLE v (Finsupp.weight w α) := by
  classical
  rw [aeval_monomial]
  have hprod := weightedSupportLE_prod α.support v (fun i => f i ^ α i)
    (fun i => α i * w i) (fun i _ => weightedSupportLE_pow (hf i) (α i))
  have hweight : (∑ i ∈ α.support, α i * w i) = Finsupp.weight w α := by
    simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Nat.cast_id]
  rw [hweight] at hprod
  simpa only [zero_add, MvPolynomial.algebraMap_eq, Finsupp.prod] using
    weightedSupportLE_mul (weightedSupportLE_C v 0 r) hprod

theorem weightedSupportLE_aeval (w : σ → ℕ) (v : τ → ℕ)
    (f : σ → MvPolynomial τ R) (hf : ∀ i, f i ∈ weightedSupportLE v (w i))
    {p : MvPolynomial σ R} {d : ℕ} (hp : p ∈ weightedSupportLE w d) :
    aeval (R := R) f p ∈ weightedSupportLE v d := by
  classical
  rw [← p.support_sum_monomial_coeff, map_sum]
  apply (weightedSupportLE v d).sum_mem
  intro α hα
  exact weightedSupportLE_mono (hp hα) (weightedSupportLE_aeval_monomial w v f hf α _)

theorem mem_weightedSupportLE_iff (w : σ → ℕ) (d : ℕ) (p : MvPolynomial σ R) :
    p ∈ weightedSupportLE w d ↔ p.weightedTotalDegree w ≤ d := by
  classical
  change (∀ α ∈ p.support, Finsupp.weight w α ≤ d) ↔ _
  simp only [weightedTotalDegree, Finset.sup_le_iff]

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ : Type*} [Fintype σ]

noncomputable def scalarTaylorRemainder (h : σ → ℚ) :
    MvPolynomial σ ℚ →ₗ[ℚ] MvPolynomial σ ℚ :=
  (polynomialTranslate h).toLinearMap - LinearMap.id - (scalarDirectionalDerivative h).toLinearMap

theorem scalarTaylorRemainder_apply (h : σ → ℚ) (p : MvPolynomial σ ℚ) :
    scalarTaylorRemainder h p = polynomialTranslate h p - p - scalarDirectionalDerivative h p := rfl

@[simp] theorem scalarTaylorRemainder_C (h : σ → ℚ) (c : ℚ) :
    scalarTaylorRemainder h (C c) = 0 := by
  rw [scalarTaylorRemainder_apply, polynomialTranslate_C, scalarDirectionalDerivative_C, sub_self, sub_zero]

@[simp] theorem scalarTaylorRemainder_X (h : σ → ℚ) (i : σ) :
    scalarTaylorRemainder h (X i) = 0 := by
  rw [scalarTaylorRemainder_apply, polynomialTranslate_X, scalarDirectionalDerivative_X]
  ring

theorem scalarTaylorRemainder_mul (h : σ → ℚ) (p q : MvPolynomial σ ℚ) :
    scalarTaylorRemainder h (p * q) =
      scalarTaylorRemainder h p * polynomialTranslate h q +
        scalarDirectionalDerivative h p * (polynomialTranslate h q - q) +
        p * scalarTaylorRemainder h q := by
  simp only [scalarTaylorRemainder_apply, map_mul, scalarDirectionalDerivative_mul]
  ring

theorem remainder_monomial_add (h : σ → ℚ) (α β : σ →₀ ℕ)
    (hα : scalarTaylorRemainder h (monomial α 1) ∈
      polynomialDegreeGap 2 (Finsupp.weight (fun _ => 1) α))
    (hβ : scalarTaylorRemainder h (monomial β 1) ∈
      polynomialDegreeGap 2 (Finsupp.weight (fun _ => 1) β)) :
    scalarTaylorRemainder h (monomial (α + β) 1) ∈
      polynomialDegreeGap 2 (Finsupp.weight (fun _ => 1) (α + β)) := by
  rw [map_add]
  have he : (monomial (α + β) 1 : MvPolynomial σ ℚ) = monomial α 1 * monomial β 1 := by simp
  rw [he, scalarTaylorRemainder_mul]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · exact polynomialDegreeGap_mul (i := 2) (j := 0) hα (polynomialDegreeGap_translate_monomial h β)
    · exact polynomialDegreeGap_mul (i := 1) (j := 1)
        (polynomialDegreeGap_directionalDerivative h (k := 0) (polynomialDegreeGap_monomial α 1))
        (polynomialDegreeGap_translate_sub_monomial h β)
  · exact polynomialDegreeGap_mul (i := 0) (j := 2) (polynomialDegreeGap_monomial α 1) hβ

theorem scalarTaylorRemainder_monomial (h : σ → ℚ) (α : σ →₀ ℕ) :
    scalarTaylorRemainder h (monomial α 1) ∈
      polynomialDegreeGap 2 (Finsupp.weight (fun _ => 1) α) := by
  classical
  have hz : scalarTaylorRemainder h (monomial (0 : σ →₀ ℕ) 1) = 0 :=
    scalarTaylorRemainder_C h 1
  have hsingle (i : σ) (n : ℕ) : scalarTaylorRemainder h (monomial (Finsupp.single i n) 1) ∈
      polynomialDegreeGap 2 (Finsupp.weight (fun _ => 1) (Finsupp.single i n)) := by
    induction n with
    | zero => rw [Finsupp.single_zero, hz]; exact Submodule.zero_mem _
    | succ n ih =>
      rw [show Finsupp.single i (n + 1) = Finsupp.single i n + Finsupp.single i 1 from Finsupp.single_add _ _ _]
      apply remainder_monomial_add h _ _ ih
      change scalarTaylorRemainder h (X i) ∈ _
      rw [scalarTaylorRemainder_X]
      exact Submodule.zero_mem _
  induction α using Finsupp.induction with
  | zero => rw [hz]; exact Submodule.zero_mem _
  | @single_add i n α _ _ ih => exact remainder_monomial_add h _ _ (hsingle i n) ih

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ : Type*}

noncomputable def polynomialTranslationPath (x : σ → ℚ) :
    MvPolynomial σ ℚ →ₐ[ℚ] Polynomial (MvPolynomial σ ℚ) :=
  MvPolynomial.aeval fun i =>
    Polynomial.C (X i) - Polynomial.C (C (x i)) * Polynomial.X

@[simp] theorem polynomialTranslationPath_C (x : σ → ℚ) (c : ℚ) :
    polynomialTranslationPath x (C c) = Polynomial.C (C c) := by
  simp [polynomialTranslationPath]

@[simp] theorem polynomialTranslationPath_X (x : σ → ℚ) (i : σ) :
    polynomialTranslationPath x (X i) =
      Polynomial.C (X i) - Polynomial.C (C (x i)) * Polynomial.X := by
  simp [polynomialTranslationPath]

theorem polynomialTranslationPath_eval (x : σ → ℚ) (t : ℚ)
    (V : MvPolynomial σ ℚ) :
    (polynomialTranslationPath x V).eval (C t) =
      polynomialTranslate (fun i => -(t * x i)) V := by
  induction V using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.eval_mul, hp, polynomialTranslationPath_X,
      Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X, polynomialTranslate_X]
    congr 1
    simp only [map_neg, map_mul]
    ring

@[simp] theorem polynomialTranslate_zero (V : MvPolynomial σ ℚ) :
    polynomialTranslate (0 : σ → ℚ) V = V := by
  induction V using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp [hp]

@[simp] theorem polynomialTranslationPath_eval_zero (x : σ → ℚ)
    (V : MvPolynomial σ ℚ) :
    (polynomialTranslationPath x V).eval 0 = V := by
  have h := polynomialTranslationPath_eval x 0 V
  simp only [map_zero, zero_mul, neg_zero] at h
  exact h.trans (polynomialTranslate_zero V)

theorem polynomialTranslationPath_derivative [Fintype σ] (x : σ → ℚ)
    (V : MvPolynomial σ ℚ) :
    (polynomialTranslationPath x V).derivative =
      -polynomialTranslationPath x (scalarDirectionalDerivative x V) := by
  induction V using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    simp only [map_add, hp, hq, neg_add_rev]
    abel
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.derivative_mul, hp,
      polynomialTranslationPath_X, Polynomial.derivative_sub, Polynomial.derivative_C,
      Polynomial.derivative_X, zero_sub, scalarDirectionalDerivative_mul,
      scalarDirectionalDerivative_X, map_add, polynomialTranslationPath_C]
    ring

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {σ τ R : Type*} [CommRing R]

def lowestSlotWeight (h : ℕ) : σ ⊕ τ → ℕ := Sum.elim (fun _ => 1) (fun _ => h)

theorem exponent_eq_single_of_lowest_slot {h : ℕ} (hh : 0 < h)
    {α : (σ ⊕ τ) →₀ ℕ}
    (hα : Finsupp.weight (lowestSlotWeight h) α ≤ h)
    {j : τ} (hj : α (Sum.inr j) ≠ 0) : α = Finsupp.single (Sum.inr j) 1 := by
  classical
  have hw := Finsupp.weight_sub_single_add (w := lowestSlotWeight (σ := σ) (τ := τ) h) hj
  have hz : Finsupp.weight (lowestSlotWeight h) (α - Finsupp.single (Sum.inr j) 1) = 0 := by
    change _ + h = _ at hw
    omega
  have hzero : α - Finsupp.single (Sum.inr j) 1 = 0 := by
    ext v
    have hv : lowestSlotWeight (σ := σ) (τ := τ) h v ≠ 0 := by
      cases v <;> simp [lowestSlotWeight, hh.ne']
    have hle := Finsupp.le_weight (lowestSlotWeight h) hv (α - Finsupp.single (Sum.inr j) 1)
    rw [hz] at hle
    exact Nat.eq_zero_of_le_zero hle
  have heq := Finsupp.sub_add_single_one_cancel hj
  rw [hzero, zero_add] at heq
  exact heq.symm

def SlotAffine [Fintype τ] (h : ℕ) (p : MvPolynomial (σ ⊕ τ) R) : Prop :=
  ∃ (C₀ : MvPolynomial σ R) (m : τ → R),
    C₀ ∈ weightedSupportLE (fun _ : σ => 1) h ∧
    ∀ (t : σ → R) (x : τ → R),
      aeval (Sum.elim t x) p = aeval t C₀ + ∑ j, m j * x j

namespace SlotAffine

variable [Fintype τ] {h : ℕ}

theorem zero : SlotAffine (σ := σ) (τ := τ) (R := R) h 0 := by
  refine ⟨0, 0, (weightedSupportLE _ _).zero_mem, ?_⟩
  intro t x
  simp

theorem add {p q : MvPolynomial (σ ⊕ τ) R}
    (hp : SlotAffine h p) (hq : SlotAffine h q) : SlotAffine h (p + q) := by
  obtain ⟨Cp, mp, hCp, heqp⟩ := hp
  obtain ⟨Cq, mq, hCq, heqq⟩ := hq
  refine ⟨Cp + Cq, mp + mq, (weightedSupportLE _ _).add_mem hCp hCq, ?_⟩
  intro t x
  simp only [map_add, heqp, heqq, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  abel

theorem of_monomial {α : (σ ⊕ τ) →₀ ℕ} (c : R) (hh : 0 < h)
    (hα : Finsupp.weight (lowestSlotWeight h) α ≤ h) :
    SlotAffine h (monomial α c) := by
  classical
  by_cases hslots : ∀ j : τ, α (Sum.inr j) = 0
  · let C₀ : MvPolynomial σ R :=
      aeval (Sum.elim X (fun _ : τ => 0)) (monomial α c)
    have hC : C₀ ∈ weightedSupportLE (fun _ : σ => 1) h := by
      apply weightedSupportLE_aeval (lowestSlotWeight h) (fun _ : σ => 1)
      · intro v
        cases v with
        | inl a => exact weightedSupportLE_X _ a
        | inr j => exact (weightedSupportLE _ _).zero_mem
      · exact weightedSupportLE_mono hα (weightedSupportLE_monomial _ _ _)
    refine ⟨C₀, 0, hC, ?_⟩
    intro t x
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, C₀,
      MvPolynomial.comp_aeval_apply]
    simp only [aeval_monomial]
    congr 1
    apply Finset.prod_congr rfl
    intro v hv
    cases v with
    | inl a => simp
    | inr j => simp [hslots j]
  · push Not at hslots
    obtain ⟨j, hj⟩ := hslots
    rw [exponent_eq_single_of_lowest_slot hh hα hj]
    refine ⟨0, Pi.single j c, (weightedSupportLE _ _).zero_mem, ?_⟩
    intro t x
    simp [aeval_monomial, Pi.single_apply]

end SlotAffine

theorem slotAffine_of_weightedSupport [Fintype τ] {h : ℕ} (hh : 0 < h)
    {p : MvPolynomial (σ ⊕ τ) R}
    (hp : p ∈ weightedSupportLE (lowestSlotWeight h) h) : SlotAffine h p := by
  classical
  have hsum (s : Finset ((σ ⊕ τ) →₀ ℕ))
      (hs : ∀ α ∈ s, Finsupp.weight (lowestSlotWeight h) α ≤ h) :
      SlotAffine h (∑ α ∈ s, monomial α (p.coeff α)) := by
    induction s using Finset.induction_on with
    | empty => simpa using (SlotAffine.zero (σ := σ) (τ := τ) (R := R) (h := h))
    | @insert α s hnot ih =>
      rw [Finset.sum_insert hnot]
      exact (SlotAffine.of_monomial _ hh (hs α (Finset.mem_insert_self _ _))).add
        (ih (fun β hβ => hs β (Finset.mem_insert_of_mem hβ)))
  simpa only [p.support_sum_monomial_coeff] using hsum p.support hp

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {U B R : Type*} [CommRing R]

theorem weightedSupportLE_rename_inl_ring (v : U → ℕ) (w : B → ℕ)
    {d : ℕ} {P : MvPolynomial U R} (hP : P ∈ weightedSupportLE v d) :
    rename (Sum.inl : U → U ⊕ B) P ∈ weightedSupportLE (Sum.elim v w) d := by
  rw [rename_eq_aeval]
  apply weightedSupportLE_aeval _ _ _ _ hP
  intro i
  exact weightedSupportLE_X (Sum.elim v w) (Sum.inl i)

theorem weightedSupportLE_rename_inr_ring (v : U → ℕ) (w : B → ℕ)
    {d : ℕ} {P : MvPolynomial B R} (hP : P ∈ weightedSupportLE w d) :
    rename (Sum.inr : B → U ⊕ B) P ∈ weightedSupportLE (Sum.elim v w) d := by
  rw [rename_eq_aeval]
  apply weightedSupportLE_aeval _ _ _ _ hP
  intro i
  exact weightedSupportLE_X (Sum.elim v w) (Sum.inr i)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.WeightedSubstitutionSupport
namespace OAI

section

namespace Erdos3

theorem aeval_monomial_weightedSupport {σ τ R : Type*} [CommRing R]
    (f : σ → MvPolynomial τ R) (w : σ → ℕ) (v : τ → ℕ)
    (hf : ∀ i, f i ∈ weightedSupportLE v (w i)) (α : σ →₀ ℕ)
    {β : τ →₀ ℕ}
    (hβ : β ∈ (MvPolynomial.aeval (R := R) f (MvPolynomial.monomial α 1)).support) :
    Finsupp.weight v β ≤ Finsupp.weight w α :=
  weightedSupportLE_aeval_monomial w v f hf α 1 hβ

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineLowestLayer
namespace OAI

section

namespace Erdos3

namespace TriangularSlots

variable {D : ℕ}

noncomputable def affineBlock (M : Matrix (Fin D) (Fin D) ℝ)
    (hM : ∀ i j, i ≤ j → M i j = 0) (P : Fin D → ℝ) : TriangularSlots D where
  center x := P + M.mulVec (x - P)
  lower i x y hxy := by
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hji : j < i
    · simp only [Pi.sub_apply, hxy j hji]
    · simp [hM i j (le_of_not_gt hji)]

end TriangularSlots

def shiftedIntegerBlock {T : Type*} {D : ℕ} (I : T → Fin D → ℤ)
    (t₀ : T) (b₀ : Fin D → ℤ) (t : T) : Fin D → ℤ := b₀ + I t - I t₀

@[simp] theorem shiftedIntegerBlock_at_base {T : Type*} {D : ℕ}
    (I : T → Fin D → ℤ) (t₀ : T) (b₀ : Fin D → ℤ) :
    shiftedIntegerBlock I t₀ b₀ t₀ = b₀ := by simp [shiftedIntegerBlock]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NilpotentBilinearExponential
namespace OAI

section

namespace Erdos3

open IsNilpotent TensorProduct Module.End

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [Module ℚ M]
  [AddCommGroup N] [Module R N] [Module ℚ N]
  [AddCommGroup P] [Module R P] [Module ℚ P]

theorem nilpotentExp_bilinear
    (b : M →ₗ[R] N →ₗ[R] P)
    (DM : Module.End R M) (DN : Module.End R N) (DP : Module.End R P)
    (hM : IsNilpotent DM) (hN : IsNilpotent DN) (hP : IsNilpotent DP)
    (hb : ∀ x y, DP (b x y) = b (DM x) y + b x (DN y)) (x : M) (y : N) :
    exp DP (b x y) = b (exp DM x) (exp DN y) := by
  let DL : Module.End R (M ⊗[R] N) := DM.rTensor N
  let DR : Module.End R (M ⊗[R] N) := DN.lTensor M
  have hL : IsNilpotent DL := hM.map (rTensorAlgHom R M N)
  have hR : IsNilpotent DR := hN.map (lTensorAlgHom R N M)
  have hc : Commute DL DR := by ext; simp [DL, DR]
  let m : M ⊗[R] N →ₗ[R] P := TensorProduct.lift b
  have he : exp DP ∘ₗ m = m ∘ₗ exp (DL + DR) := by
    apply Module.End.commute_exp_left_of_commute (hc.isNilpotent_add hL hR) hP
    ext x y
    simp [m, DL, DR, hb]
  have heL : exp DL = (exp DM).rTensor N := (hM.map_exp (rTensorAlgHom R M N)).symm
  have heR : exp DR = (exp DN).lTensor M := (hN.map_exp (lTensorAlgHom R N M)).symm
  have h := LinearMap.congr_fun he (x ⊗ₜ[R] y)
  simpa [m, exp_add_of_commute hc hL hR, heL, heR] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.LieBCHContinuity
namespace OAI

section

namespace Erdos3

open PowerSeries Finset

section Ring
variable {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]

noncomputable def nilpotentSeries (f : PowerSeries ℚ) (a : A) : A :=
  ∑ i ∈ range (nilpotencyClass a), coeff i f • a ^ i

theorem nilpotentSeries_eq_sum (f : PowerSeries ℚ) {a : A} {k : ℕ} (h : a ^ k = 0) :
    nilpotentSeries f a = ∑ i ∈ range k, coeff i f • a ^ i := by
  unfold nilpotentSeries
  have hle : nilpotencyClass a ≤ k := csInf_le' h
  apply sum_subset (range_mono hle)
  intro i hi hnot
  rw [pow_eq_zero_of_le (Nat.le_of_not_gt (by simpa using hnot))
    (pow_nilpotencyClass ⟨k, h⟩), smul_zero]

theorem nilpotentSeries_eq_finsum (f : PowerSeries ℚ) {a : A} (ha : IsNilpotent a) :
    nilpotentSeries f a = ∑ᶠ i : ℕ, coeff i f • a ^ i := by
  symm
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra hn
  have he : a ^ i = 0 := pow_eq_zero_of_le
    (Nat.le_of_not_gt (by simpa using hn)) (pow_nilpotencyClass ha)
  exact hi (by simp [he])

theorem map_nilpotentSeries (f : PowerSeries ℚ) {a : A} (ha : IsNilpotent a)
    (φ : A →ₐ[ℚ] B) : φ (nilpotentSeries f a) = nilpotentSeries f (φ a) := by
  obtain ⟨k, hk⟩ := ha
  have hk' : (φ a) ^ k = 0 := by rw [← map_pow, hk, map_zero]
  simp [nilpotentSeries_eq_sum f hk, nilpotentSeries_eq_sum f hk']

theorem nilpotentSeries_exp (a : A) :
    nilpotentSeries (PowerSeries.exp ℚ) a = IsNilpotent.exp a := by
  simp [nilpotentSeries, IsNilpotent.exp, coeff_exp, one_div]

end Ring

section CommRing
variable {A : Type*} [CommRing A] [Algebra ℚ A]

omit [Algebra ℚ A] in
theorem hasSubst_C_nilpotent {a : A} (ha : IsNilpotent a) :
    HasSubst (C a : PowerSeries A) := by
  change IsNilpotent (constantCoeff (C a))
  simpa only [constantCoeff_C] using ha

theorem subst_C_nilpotent_eq (f : PowerSeries ℚ) {a : A} (ha : IsNilpotent a) :
    f.subst (C a : PowerSeries A) = C (nilpotentSeries f a) := by
  ext n
  rw [coeff_subst' (hasSubst_C_nilpotent ha)]
  simp only [← map_pow, coeff_C]
  cases n with
  | zero => simp only [ite_true, nilpotentSeries_eq_finsum f ha]
  | succ n => simp

noncomputable def nilpotentSeriesHom {a : A} (ha : IsNilpotent a) :
    PowerSeries ℚ →ₐ[ℚ] A :=
  constantCoeff.toRatAlgHom.comp (substAlgHom (hasSubst_C_nilpotent ha))

theorem nilpotentSeriesHom_apply {a : A} (ha : IsNilpotent a) (f : PowerSeries ℚ) :
    nilpotentSeriesHom ha f = nilpotentSeries f a := by
  simp only [nilpotentSeriesHom, AlgHom.comp_apply, RingHom.toRatAlgHom_apply,
    coe_substAlgHom, subst_C_nilpotent_eq f ha, constantCoeff_C]

theorem nilpotentSeries_X {a : A} (ha : IsNilpotent a) :
    nilpotentSeries X a = a := by
  have h := subst_X (R := ℚ) (hasSubst_C_nilpotent ha)
  rw [subst_C_nilpotent_eq _ ha] at h
  exact C_injective h

theorem isNilpotent_nilpotentSeries {a : A} (ha : IsNilpotent a)
    {g : PowerSeries ℚ} (hg : constantCoeff g = 0) :
    IsNilpotent (nilpotentSeries g a) := by
  have h := (HasSubst.of_constantCoeff_zero' hg).comp (hasSubst_C_nilpotent ha)
  change IsNilpotent (nilpotentSeriesHom ha g) at h
  rwa [nilpotentSeriesHom_apply] at h

theorem nilpotentSeries_subst {a : A} (ha : IsNilpotent a)
    (f : PowerSeries ℚ) {g : PowerSeries ℚ} (hg : constantCoeff g = 0) :
    nilpotentSeries (f.subst g) a = nilpotentSeries f (nilpotentSeries g a) := by
  have h := subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hg)
    (hasSubst_C_nilpotent ha) f
  rw [subst_C_nilpotent_eq _ ha, subst_C_nilpotent_eq _ ha,
    subst_C_nilpotent_eq _ (isNilpotent_nilpotentSeries ha hg)] at h
  exact C_injective h

end CommRing
end Erdos3

end

section

namespace Erdos3

open PowerSeries

section Ring
variable {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]

noncomputable def nilpotentLog (a : A) : A := nilpotentSeries (log ℚ) a

theorem nilpotentLog_eq_sum {a : A} {k : ℕ} (h : a ^ k = 0) :
    nilpotentLog a = ∑ i ∈ Finset.range k, ((-1 : ℚ) ^ (i + 1) / i) • a ^ i := by
  rw [nilpotentLog, nilpotentSeries_eq_sum _ h]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hzero : i = 0
  · simp [hzero]
  · simp [coeff_log, hzero]

theorem nilpotentLog_zero : nilpotentLog (0 : A) = 0 := by
  simp [nilpotentLog_eq_sum (pow_one (0 : A))]

theorem map_nilpotentLog {a : A} (ha : IsNilpotent a) (φ : A →ₐ[ℚ] B) :
    φ (nilpotentLog a) = nilpotentLog (φ a) := map_nilpotentSeries _ ha φ

end Ring

section CommRing
variable {A : Type*} [CommRing A] [Algebra ℚ A]

theorem isNilpotent_nilpotentLog_comm {a : A} (ha : IsNilpotent a) :
    IsNilpotent (nilpotentLog a) := isNilpotent_nilpotentSeries ha constantCoeff_log

theorem exp_nilpotentLog_comm {a : A} (ha : IsNilpotent a) :
    IsNilpotent.exp (nilpotentLog a) = 1 + a := by
  have h := nilpotentSeries_subst ha (exp ℚ) (g := log ℚ) constantCoeff_log
  rw [formal_exp_log, ← nilpotentSeriesHom_apply ha, map_add, map_one,
    nilpotentSeriesHom_apply, nilpotentSeries_X ha, nilpotentSeries_exp] at h
  exact h.symm

theorem nilpotentLog_exp_sub_one_comm {a : A} (ha : IsNilpotent a) :
    nilpotentLog (IsNilpotent.exp a - 1) = a := by
  have h := nilpotentSeries_subst ha (log ℚ) (g := exp ℚ - 1)
    (by simp [constantCoeff_exp])
  rw [formal_log_exp, nilpotentSeries_X ha, ← nilpotentSeriesHom_apply ha,
    map_sub, map_one, nilpotentSeriesHom_apply, nilpotentSeries_exp] at h
  exact h.symm

end CommRing

section Ring
variable {A : Type*} [Ring A] [Algebra ℚ A]

theorem isNilpotent_nilpotentLog {a : A} (ha : IsNilpotent a) :
    IsNilpotent (nilpotentLog a) := by
  let S := Algebra.adjoin ℚ ({a} : Set A)
  let x : S := ⟨a, Algebra.self_mem_adjoin_singleton ℚ a⟩
  have hx : IsNilpotent x :=
    (IsNilpotent.map_iff (f := S.val) Subtype.val_injective).mp ha
  have h := (isNilpotent_nilpotentLog_comm hx).map S.val
  rwa [map_nilpotentLog hx S.val] at h

theorem exp_nilpotentLog {a : A} (ha : IsNilpotent a) :
    IsNilpotent.exp (nilpotentLog a) = 1 + a := by
  let S := Algebra.adjoin ℚ ({a} : Set A)
  let x : S := ⟨a, Algebra.self_mem_adjoin_singleton ℚ a⟩
  have hx : IsNilpotent x :=
    (IsNilpotent.map_iff (f := S.val) Subtype.val_injective).mp ha
  have h := congrArg S.val (exp_nilpotentLog_comm hx)
  rw [IsNilpotent.map_exp (isNilpotent_nilpotentLog_comm hx),
    map_nilpotentLog hx, map_add, map_one] at h
  exact h

theorem nilpotentLog_exp_sub_one {a : A} (ha : IsNilpotent a) :
    nilpotentLog (IsNilpotent.exp a - 1) = a := by
  let S := Algebra.adjoin ℚ ({a} : Set A)
  let x : S := ⟨a, Algebra.self_mem_adjoin_singleton ℚ a⟩
  have hx : IsNilpotent x :=
    (IsNilpotent.map_iff (f := S.val) Subtype.val_injective).mp ha
  have h := congrArg S.val (nilpotentLog_exp_sub_one_comm hx)
  rw [map_nilpotentLog (IsNilpotent.isNilpotent_exp_sub_one hx), map_sub, map_one,
    IsNilpotent.map_exp hx] at h
  exact h

theorem exp_injective_on_nilpotents {a b : A} (ha : IsNilpotent a)
    (hb : IsNilpotent b) (h : IsNilpotent.exp a = IsNilpotent.exp b) : a = b := by
  rw [← nilpotentLog_exp_sub_one ha, ← nilpotentLog_exp_sub_one hb, h]

end Ring
end Erdos3

end

section

namespace Erdos3

open PowerSeries Finset

variable {A : Type*} [Ring A] [Algebra ℚ A]

theorem nonUnitalSubalgebra_pow_mem (I : NonUnitalSubalgebra ℚ A) {a : A}
    (ha : a ∈ I) {n : ℕ} (hn : 0 < n) : a ^ n ∈ I := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  clear hn
  induction n with
  | zero => simpa using ha
  | succ n ih =>
    rw [pow_succ]
    exact mul_mem ih ha

theorem nilpotentSeries_sub (f g : PowerSeries ℚ) (a : A) :
    nilpotentSeries (f - g) a = nilpotentSeries f a - nilpotentSeries g a := by
  simp [nilpotentSeries, sub_smul, sum_sub_distrib]

theorem nilpotentSeries_one {a : A} (ha : IsNilpotent a) :
    nilpotentSeries 1 a = 1 := by
  obtain ⟨k, hk⟩ := ha
  rw [nilpotentSeries_eq_sum _ (pow_eq_zero_of_le (Nat.le_succ k) hk)]
  simp [coeff_one]

theorem nilpotentSeries_mem (I : NonUnitalSubalgebra ℚ A) {a : A} (ha : a ∈ I)
    {f : PowerSeries ℚ} (hf : constantCoeff f = 0) : nilpotentSeries f a ∈ I := by
  apply I.sum_mem
  intro i hi
  by_cases hzero : i = 0
  · simp [hzero, coeff_zero_eq_constantCoeff, hf]
  · exact I.smul_mem _ (nonUnitalSubalgebra_pow_mem I ha (Nat.pos_of_ne_zero hzero))

theorem nilpotentLog_mem (I : NonUnitalSubalgebra ℚ A) {a : A} (ha : a ∈ I) :
    nilpotentLog a ∈ I := nilpotentSeries_mem I ha constantCoeff_log

theorem exp_sub_one_mem (I : NonUnitalSubalgebra ℚ A) {a : A}
    (ha : a ∈ I) (hna : IsNilpotent a) : IsNilpotent.exp a - 1 ∈ I := by
  rw [← nilpotentSeries_exp a, ← nilpotentSeries_one hna, ← nilpotentSeries_sub]
  exact nilpotentSeries_mem I ha (by simp [constantCoeff_exp])

theorem exp_mul_exp_sub_one_mem (I : NonUnitalSubalgebra ℚ A) {a b : A}
    (ha : a ∈ I) (hb : b ∈ I) (hna : IsNilpotent a) (hnb : IsNilpotent b) :
    IsNilpotent.exp a * IsNilpotent.exp b - 1 ∈ I := by
  have hpa := exp_sub_one_mem I ha hna
  have hpb := exp_sub_one_mem I hb hnb
  have hid : IsNilpotent.exp a * IsNilpotent.exp b - 1 =
      (IsNilpotent.exp a - 1) * (IsNilpotent.exp b - 1) +
        (IsNilpotent.exp a - 1) + (IsNilpotent.exp b - 1) := by noncomm_ring
  rw [hid]
  exact I.add_mem (I.add_mem (I.mul_mem hpa hpb) hpa) hpb

noncomputable def nilpotentBCH (a b : A) : A :=
  nilpotentLog (IsNilpotent.exp a * IsNilpotent.exp b - 1)

theorem nilpotentBCH_mem (I : NonUnitalSubalgebra ℚ A) {a b : A}
    (ha : a ∈ I) (hb : b ∈ I) (hna : IsNilpotent a) (hnb : IsNilpotent b) :
    nilpotentBCH a b ∈ I :=
  nilpotentLog_mem I (exp_mul_exp_sub_one_mem I ha hb hna hnb)

section NilAlgebra
variable (I : NonUnitalSubalgebra ℚ A) (hI : ∀ a ∈ I, IsNilpotent a)
include hI

theorem exp_nilpotentBCH {a b : A} (ha : a ∈ I) (hb : b ∈ I) :
    IsNilpotent.exp (nilpotentBCH a b) = IsNilpotent.exp a * IsNilpotent.exp b := by
  have hn := hI _ (exp_mul_exp_sub_one_mem I ha hb (hI _ ha) (hI _ hb))
  rw [nilpotentBCH, exp_nilpotentLog hn]
  abel

theorem nilpotentBCH_assoc {a b c : A} (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I) :
    nilpotentBCH (nilpotentBCH a b) c = nilpotentBCH a (nilpotentBCH b c) := by
  have hab := nilpotentBCH_mem I ha hb (hI _ ha) (hI _ hb)
  have hbc := nilpotentBCH_mem I hb hc (hI _ hb) (hI _ hc)
  apply exp_injective_on_nilpotents
    (hI _ (nilpotentBCH_mem I hab hc (hI _ hab) (hI _ hc)))
    (hI _ (nilpotentBCH_mem I ha hbc (hI _ ha) (hI _ hbc)))
  rw [exp_nilpotentBCH I hI hab hc, exp_nilpotentBCH I hI ha hbc,
    exp_nilpotentBCH I hI ha hb, exp_nilpotentBCH I hI hb hc, mul_assoc]

end NilAlgebra

theorem nilpotentBCH_zero_left {a : A} (ha : IsNilpotent a) : nilpotentBCH 0 a = a := by
  simp only [nilpotentBCH, IsNilpotent.exp_zero, one_mul, nilpotentLog_exp_sub_one ha]

theorem nilpotentBCH_neg_left {a : A} (ha : IsNilpotent a) : nilpotentBCH (-a) a = 0 := by
  rw [nilpotentBCH, IsNilpotent.exp_neg_mul_exp_self ha, sub_self, nilpotentLog_zero]

theorem nilpotentBCH_eq_add_of_commute {a b : A} (ha : IsNilpotent a)
    (hb : IsNilpotent b) (hab : Commute a b) : nilpotentBCH a b = a + b := by
  rw [nilpotentBCH, ← IsNilpotent.exp_add_of_commute hab ha hb,
    nilpotentLog_exp_sub_one (hab.isNilpotent_add ha hb)]

end Erdos3

end

section

namespace Erdos3

open IsNilpotent TensorProduct Module.End

variable {R M N P : Type*} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [Module ℚ M] [IsScalarTower ℚ R M]
  [AddCommGroup N] [Module R N] [Module ℚ N] [IsScalarTower ℚ R N]
  [AddCommGroup P] [Module R P] [Module ℚ P] [IsScalarTower ℚ R P]

theorem nilpotentLog_intertwine
    {DM : Module.End R M} {DN : Module.End R N} {g : M →ₗ[R] N}
    (hM : IsNilpotent DM) (hN : IsNilpotent DN) (h : DN ∘ₗ g = g ∘ₗ DM) :
    nilpotentLog DN ∘ₗ g = g ∘ₗ nilpotentLog DM := by
  ext x
  obtain ⟨k, hk⟩ := hM
  obtain ⟨l, hl⟩ := hN
  have hmk : DM ^ max k l = 0 := pow_eq_zero_of_le (le_max_left k l) hk
  have hnl : DN ^ max k l = 0 := pow_eq_zero_of_le (le_max_right k l) hl
  have hp (i : ℕ) : (DN ^ i) (g x) = g ((DM ^ i) x) := by
    simpa using LinearMap.congr_fun (Module.End.commute_pow_left_of_commute h i) x
  simp [nilpotentLog_eq_sum hmk, nilpotentLog_eq_sum hnl, hp, map_rat_smul]

theorem nilpotentExp_intertwine_injective
    {DM : Module.End R M} {DN : Module.End R N} {g : M →ₗ[R] N}
    (hM : IsNilpotent DM) (hN : IsNilpotent DN)
    (h : exp DN ∘ₗ g = g ∘ₗ exp DM) : DN ∘ₗ g = g ∘ₗ DM := by
  have hd : (exp DN - 1) ∘ₗ g = g ∘ₗ (exp DM - 1) := by
    ext x
    have hx := LinearMap.congr_fun h x
    simpa only [LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub]
      using congrArg (fun y => y - g x) hx
  have hl := nilpotentLog_intertwine (isNilpotent_exp_sub_one hM)
    (isNilpotent_exp_sub_one hN) hd
  simpa only [nilpotentLog_exp_sub_one hM, nilpotentLog_exp_sub_one hN] using hl

omit [IsScalarTower ℚ R M] [IsScalarTower ℚ R N] in
theorem nilpotentExp_bilinear_injective
    (b : M →ₗ[R] N →ₗ[R] P)
    (DM : Module.End R M) (DN : Module.End R N) (DP : Module.End R P)
    (hM : IsNilpotent DM) (hN : IsNilpotent DN) (hP : IsNilpotent DP)
    (hb : ∀ x y, exp DP (b x y) = b (exp DM x) (exp DN y)) (x : M) (y : N) :
    DP (b x y) = b (DM x) y + b x (DN y) := by
  let DL : Module.End R (M ⊗[R] N) := DM.rTensor N
  let DR : Module.End R (M ⊗[R] N) := DN.lTensor M
  have hL : IsNilpotent DL := hM.map (rTensorAlgHom R M N)
  have hR : IsNilpotent DR := hN.map (lTensorAlgHom R N M)
  have hc : Commute DL DR := by ext; simp [DL, DR]
  let m : M ⊗[R] N →ₗ[R] P := TensorProduct.lift b
  have heL : exp DL = (exp DM).rTensor N := (hM.map_exp (rTensorAlgHom R M N)).symm
  have heR : exp DR = (exp DN).lTensor M := (hN.map_exp (lTensorAlgHom R N M)).symm
  have he : exp DP ∘ₗ m = m ∘ₗ exp (DL + DR) := by
    ext x y
    simp [m, exp_add_of_commute hc hL hR, heL, heR, hb]
  have hd := nilpotentExp_intertwine_injective (hc.isNilpotent_add hL hR) hP he
  simpa [m, DL, DR] using LinearMap.congr_fun hd (x ⊗ₜ[R] y)

theorem nilpotentLog_bilinear
    (b : M →ₗ[R] N →ₗ[R] P)
    (FM : Module.End R M) (FN : Module.End R N) (FP : Module.End R P)
    (hM : IsNilpotent (FM - 1)) (hN : IsNilpotent (FN - 1))
    (hP : IsNilpotent (FP - 1))
    (hb : ∀ x y, FP (b x y) = b (FM x) (FN y)) (x : M) (y : N) :
    nilpotentLog (FP - 1) (b x y) =
      b (nilpotentLog (FM - 1) x) y + b x (nilpotentLog (FN - 1) y) := by
  apply nilpotentExp_bilinear_injective b _ _ _
    (isNilpotent_nilpotentLog hM) (isNilpotent_nilpotentLog hN)
    (isNilpotent_nilpotentLog hP) _ x y
  simpa only [exp_nilpotentLog hM, exp_nilpotentLog hN, exp_nilpotentLog hP,
    show 1 + (FM - 1) = FM by abel,
    show 1 + (FN - 1) = FN by abel,
    show 1 + (FP - 1) = FP by abel] using hb

end Erdos3

end

section

namespace Erdos3

variable {A : Type*} [Ring A] [Algebra ℚ A]

structure NilpotentBCHGroup (I : NonUnitalSubalgebra ℚ A)
    (_hI : ∀ a ∈ I, IsNilpotent a) where
  coord : A
  mem_coord : coord ∈ I

namespace NilpotentBCHGroup
variable {I : NonUnitalSubalgebra ℚ A} {hI : ∀ a ∈ I, IsNilpotent a}

@[ext]
theorem ext {a b : NilpotentBCHGroup I hI} (h : a.coord = b.coord) : a = b := by
  cases a
  cases b
  cases h
  rfl

noncomputable instance : Mul (NilpotentBCHGroup I hI) where
  mul a b := ⟨nilpotentBCH a.coord b.coord,
    nilpotentBCH_mem I a.mem_coord b.mem_coord (hI _ a.mem_coord) (hI _ b.mem_coord)⟩

instance : One (NilpotentBCHGroup I hI) where
  one := ⟨0, I.zero_mem⟩

instance : Inv (NilpotentBCHGroup I hI) where
  inv a := ⟨-a.coord, I.neg_mem a.mem_coord⟩

@[simp] theorem coord_mul (a b : NilpotentBCHGroup I hI) :
    (a * b).coord = nilpotentBCH a.coord b.coord := rfl
@[simp] theorem coord_one : (1 : NilpotentBCHGroup I hI).coord = 0 := rfl
@[simp] theorem coord_inv (a : NilpotentBCHGroup I hI) : (a⁻¹).coord = -a.coord := rfl

noncomputable instance : Group (NilpotentBCHGroup I hI) :=
  Group.ofLeftAxioms
    (fun a b c => ext (nilpotentBCH_assoc I hI a.mem_coord b.mem_coord c.mem_coord))
    (fun a => ext (nilpotentBCH_zero_left (hI _ a.mem_coord)))
    (fun a => ext (nilpotentBCH_neg_left (hI _ a.mem_coord)))

noncomputable def expHom : NilpotentBCHGroup I hI →* Aˣ where
  toFun a :=
    { val := IsNilpotent.exp a.coord
      inv := IsNilpotent.exp (-a.coord)
      val_inv := IsNilpotent.exp_mul_exp_neg_self (hI _ a.mem_coord)
      inv_val := IsNilpotent.exp_neg_mul_exp_self (hI _ a.mem_coord) }
  map_one' := by apply Units.ext; exact IsNilpotent.exp_zero
  map_mul' a b := by
    apply Units.ext
    exact exp_nilpotentBCH I hI a.mem_coord b.mem_coord

@[simp] theorem expHom_val (a : NilpotentBCHGroup I hI) :
    ↑(expHom a) = IsNilpotent.exp a.coord := rfl

end NilpotentBCHGroup
end Erdos3

end

section

namespace Erdos3

open Finset

variable {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]

noncomputable def finiteExp (k : ℕ) (a : A) : A :=
  ∑ i ∈ range k, (i.factorial : ℚ)⁻¹ • a ^ i

noncomputable def finiteLog (k : ℕ) (a : A) : A :=
  ∑ i ∈ range k, ((-1 : ℚ) ^ (i + 1) / i) • a ^ i

theorem map_finiteExp (φ : A →ₐ[ℚ] B) (k : ℕ) (a : A) :
    φ (finiteExp k a) = finiteExp k (φ a) := by simp [finiteExp]

theorem map_finiteLog (φ : A →ₐ[ℚ] B) (k : ℕ) (a : A) :
    φ (finiteLog k a) = finiteLog k (φ a) := by simp [finiteLog]

theorem finiteExp_eq_exp {a : A} {k : ℕ} (h : a ^ k = 0) :
    finiteExp k a = IsNilpotent.exp a := (IsNilpotent.exp_eq_sum h).symm

theorem finiteLog_eq_log {a : A} {k : ℕ} (h : a ^ k = 0) :
    finiteLog k a = nilpotentLog a := (nilpotentLog_eq_sum h).symm

noncomputable def bchPolynomial (k : ℕ) : FreeAlgebra ℚ (Fin 2) :=
  finiteLog k (finiteExp k (FreeAlgebra.ι ℚ 0) * finiteExp k (FreeAlgebra.ι ℚ 1) - 1)

noncomputable def bchPolynomialEval (a b : A) : FreeAlgebra ℚ (Fin 2) →ₐ[ℚ] A :=
  FreeAlgebra.lift ℚ ![a, b]

theorem bchPolynomialEval_formula (k : ℕ) (a b : A) :
    bchPolynomialEval a b (bchPolynomial k) =
      finiteLog k (finiteExp k a * finiteExp k b - 1) := by
  simp [bchPolynomial, bchPolynomialEval, map_finiteLog, map_finiteExp]

theorem bchPolynomialEval_eq (I : NonUnitalSubalgebra ℚ A) {k : ℕ}
    (hI : ∀ a ∈ I, a ^ k = 0) {a b : A} (ha : a ∈ I) (hb : b ∈ I) :
    bchPolynomialEval a b (bchPolynomial k) = nilpotentBCH a b := by
  have hna : IsNilpotent a := ⟨k, hI a ha⟩
  have hnb : IsNilpotent b := ⟨k, hI b hb⟩
  rw [bchPolynomialEval_formula, finiteExp_eq_exp (hI a ha), finiteExp_eq_exp (hI b hb),
    finiteLog_eq_log (hI _ (exp_mul_exp_sub_one_mem I ha hb hna hnb))]
  rfl

theorem map_nilpotentBCH (I : NonUnitalSubalgebra ℚ A)
    (hI : ∀ a ∈ I, IsNilpotent a) (φ : A →ₐ[ℚ] B) {a b : A}
    (ha : a ∈ I) (hb : b ∈ I) : φ (nilpotentBCH a b) = nilpotentBCH (φ a) (φ b) := by
  rw [nilpotentBCH, map_nilpotentLog (hI _
    (exp_mul_exp_sub_one_mem I ha hb (hI _ ha) (hI _ hb))), map_sub, map_mul, map_one,
    IsNilpotent.map_exp (hI _ ha), IsNilpotent.map_exp (hI _ hb), nilpotentBCH]

end Erdos3

end

section

namespace Erdos3
variable {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]

theorem nilpotentBCH_commuting_maps
    (I : NonUnitalSubalgebra ℚ A) (hI : ∀ a ∈ I, IsNilpotent a)
    (J : NonUnitalSubalgebra ℚ B) (hJ : ∀ b ∈ J, IsNilpotent b)
    (L R : A →ₐ[ℚ] B) (hL : ∀ a ∈ I, L a ∈ J) (hR : ∀ a ∈ I, R a ∈ J)
    (hcomm : ∀ a b, Commute (L a) (R b)) {a b : A} (ha : a ∈ I) (hb : b ∈ I) :
    nilpotentBCH (L a + R a) (L b + R b) = L (nilpotentBCH a b) + R (nilpotentBCH a b) := by
  have hc := nilpotentBCH_mem I ha hb (hI _ ha) (hI _ hb)
  have hca := J.add_mem (hL _ ha) (hR _ ha)
  have hcb := J.add_mem (hL _ hb) (hR _ hb)
  apply exp_injective_on_nilpotents
    (hJ _ (nilpotentBCH_mem J hca hcb (hJ _ hca) (hJ _ hcb)))
    (hJ _ (J.add_mem (hL _ hc) (hR _ hc)))
  rw [exp_nilpotentBCH J hJ hca hcb,
    IsNilpotent.exp_add_of_commute (hcomm a a) (hJ _ (hL _ ha)) (hJ _ (hR _ ha)),
    IsNilpotent.exp_add_of_commute (hcomm b b) (hJ _ (hL _ hb)) (hJ _ (hR _ hb)),
    IsNilpotent.exp_add_of_commute (hcomm _ _) (hJ _ (hL _ hc)) (hJ _ (hR _ hc)),
    ← IsNilpotent.map_exp (hI _ ha) L, ← IsNilpotent.map_exp (hI _ ha) R,
    ← IsNilpotent.map_exp (hI _ hb) L, ← IsNilpotent.map_exp (hI _ hb) R,
    ← IsNilpotent.map_exp (hI _ hc) L, ← IsNilpotent.map_exp (hI _ hc) R,
    exp_nilpotentBCH I hI ha hb, map_mul, map_mul]
  exact (hcomm (IsNilpotent.exp b) (IsNilpotent.exp a)).symm.mul_mul_mul_comm _ _

end Erdos3

end

section

namespace Erdos3

variable (A : Type*) [Ring A] [Algebra ℚ A]

structure NilpotentAlgebraFiltration (s : ℕ) where
  layer : ℕ → Submodule ℚ A
  antitone : Antitone layer
  zero_eq_top : layer 0 = ⊤
  mul_mem : ∀ {i j : ℕ} {a b : A}, a ∈ layer i → b ∈ layer j → a * b ∈ layer (i + j)
  terminal : layer (s + 1) = ⊥

namespace NilpotentAlgebraFiltration
variable {A} {s : ℕ} (F : NilpotentAlgebraFiltration A s)

def layerAlgebra (i : ℕ) : NonUnitalSubalgebra ℚ A where
  carrier := F.layer i
  zero_mem' := (F.layer i).zero_mem
  add_mem' := (F.layer i).add_mem
  smul_mem' c _ hx := (F.layer i).smul_mem c hx
  mul_mem' ha hb := F.antitone (Nat.le_add_right i i) (F.mul_mem ha hb)

@[simp] theorem mem_layerAlgebra (i : ℕ) (a : A) : a ∈ F.layerAlgebra i ↔ a ∈ F.layer i :=
  Iff.rfl

theorem pow_mem {i : ℕ} {a : A} (ha : a ∈ F.layer i) (n : ℕ) :
    a ^ n ∈ F.layer (n * i) := by
  induction n with
  | zero => simp [F.zero_eq_top]
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact F.mul_mem ih ha

theorem pow_eq_zero {i : ℕ} (hi : 1 ≤ i) {a : A} (ha : a ∈ F.layer i) :
    a ^ (s + 1) = 0 := by
  have h := F.antitone (Nat.le_mul_of_pos_right (s + 1) hi) (F.pow_mem ha (s + 1))
  simpa only [F.terminal, Submodule.mem_bot] using h

theorem isNilpotent_of_mem {i : ℕ} (hi : 1 ≤ i) {a : A} (ha : a ∈ F.layer i) :
    IsNilpotent a := ⟨s + 1, F.pow_eq_zero hi ha⟩

theorem positive_nilpotent : ∀ a ∈ F.layerAlgebra 1, IsNilpotent a :=
  fun _ ha => F.isNilpotent_of_mem le_rfl ha

theorem bchPolynomial_formula {a b : A} (ha : a ∈ F.layer 1) (hb : b ∈ F.layer 1) :
    bchPolynomialEval a b (bchPolynomial (s + 1)) = nilpotentBCH a b :=
  bchPolynomialEval_eq (F.layerAlgebra 1) (fun _ hx => F.pow_eq_zero le_rfl hx) ha hb

theorem bch_mem {i : ℕ} (hi : 1 ≤ i) {a b : A}
    (ha : a ∈ F.layer i) (hb : b ∈ F.layer i) : nilpotentBCH a b ∈ F.layer i :=
  nilpotentBCH_mem (F.layerAlgebra i) ha hb
    (F.isNilpotent_of_mem hi ha) (F.isNilpotent_of_mem hi hb)

theorem exp_sub_one_mem_layer {i : ℕ} {a : A} (ha : a ∈ F.layer i)
    (hna : IsNilpotent a) : IsNilpotent.exp a - 1 ∈ F.layer i :=
  exp_sub_one_mem (F.layerAlgebra i) ha hna

end NilpotentAlgebraFiltration
end Erdos3

end

section

namespace Erdos3
open TensorProduct
variable {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]

theorem seriesMap_commute (L R : A →ₐ[ℚ] B) (hcomm : ∀ a b, Commute (L a) (R b))
    (f g : PowerSeries A) : Commute (PowerSeries.mapAlgHom L f) (PowerSeries.mapAlgHom R g) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  conv_rhs => rw [← Finset.HasAntidiagonal.map_swap_antidiagonal]
  simp only [Finset.sum_map, Function.Embedding.coeFn_mk,
    PowerSeries.mapAlgHom_apply, PowerSeries.coeff_map]
  apply Finset.sum_congr rfl
  intro ij _
  exact (hcomm _ _).eq

theorem truncatedSeriesMap_commute (s : ℕ) (L R : A →ₐ[ℚ] B)
    (hcomm : ∀ a b, Commute (L a) (R b)) (p q : TruncatedSeries A s) :
    Commute (truncatedSeriesMap s L p) (truncatedSeriesMap s R q) := by
  obtain ⟨f, rfl⟩ := truncatedSeriesMk_surjective s p
  obtain ⟨g, rfl⟩ := truncatedSeriesMk_surjective s q
  exact (seriesMap_commute L R hcomm f g).map (truncatedSeriesMk s)

variable {X : Type*}

def TruncatedPrimitive {s : ℕ} (p : TruncatedSeries (FreeAlgebra ℚ X) s) : Prop :=
  truncatedSeriesMap s freeCoproduct p =
    truncatedSeriesMap s Algebra.TensorProduct.includeLeft p +
      truncatedSeriesMap s Algebra.TensorProduct.includeRight p

theorem TruncatedPrimitive.coeff {s : ℕ} {p : TruncatedSeries (FreeAlgebra ℚ X) s}
    (hp : TruncatedPrimitive p) (n : ℕ) (hn : n ≤ s) :
    FreePrimitive (truncatedSeriesCoeff s n hn p) := by
  have h := congrArg (truncatedSeriesCoeff s n hn) hp
  simpa only [FreePrimitive, truncatedSeriesCoeff_map, map_add, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply] using h

theorem truncatedPrimitive_iff_coeff {s : ℕ} (p : TruncatedSeries (FreeAlgebra ℚ X) s) :
    TruncatedPrimitive p ↔ ∀ n (hn : n ≤ s), FreePrimitive (truncatedSeriesCoeff s n hn p) := by
  refine ⟨fun hp n hn => hp.coeff n hn, fun h => ?_⟩
  apply truncatedSeries_ext
  intro n hn
  simpa only [FreePrimitive, truncatedSeriesCoeff_map, map_add, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply] using h n hn

theorem TruncatedPrimitive.bch {s : ℕ} {p q : TruncatedSeries (FreeAlgebra ℚ X) s}
    (hp : TruncatedPrimitive p) (hq : TruncatedPrimitive q)
    (hp0 : p ∈ truncatedSeriesPositive s) (hq0 : q ∈ truncatedSeriesPositive s) :
    TruncatedPrimitive (nilpotentBCH p q) := by
  let I := truncatedSeriesPositive (A := FreeAlgebra ℚ X) s
  let J := truncatedSeriesPositive (A := FreeAlgebra ℚ X ⊗[ℚ] FreeAlgebra ℚ X) s
  let D : TruncatedSeries (FreeAlgebra ℚ X) s →ₐ[ℚ]
      TruncatedSeries (FreeAlgebra ℚ X ⊗[ℚ] FreeAlgebra ℚ X) s :=
    truncatedSeriesMap s freeCoproduct
  let L : TruncatedSeries (FreeAlgebra ℚ X) s →ₐ[ℚ]
      TruncatedSeries (FreeAlgebra ℚ X ⊗[ℚ] FreeAlgebra ℚ X) s :=
    truncatedSeriesMap s Algebra.TensorProduct.includeLeft
  let R : TruncatedSeries (FreeAlgebra ℚ X) s →ₐ[ℚ]
      TruncatedSeries (FreeAlgebra ℚ X ⊗[ℚ] FreeAlgebra ℚ X) s :=
    truncatedSeriesMap s Algebra.TensorProduct.includeRight
  have hI : ∀ a ∈ I, IsNilpotent a := fun _ ha => truncatedSeriesPositive_nilpotent ha
  have hJ : ∀ a ∈ J, IsNilpotent a := fun _ ha => truncatedSeriesPositive_nilpotent ha
  change D (nilpotentBCH p q) = L (nilpotentBCH p q) + R (nilpotentBCH p q)
  calc
    D (nilpotentBCH p q) = nilpotentBCH (D p) (D q) :=
      map_nilpotentBCH (A := TruncatedSeries (FreeAlgebra ℚ X) s)
        (B := TruncatedSeries (FreeAlgebra ℚ X ⊗[ℚ] FreeAlgebra ℚ X) s)
        I hI D (a := p) (b := q) hp0 hq0
    _ = nilpotentBCH (L p + R p) (L q + R q) := congrArg₂ nilpotentBCH hp hq
    _ = L (nilpotentBCH p q) + R (nilpotentBCH p q) := ?_
  apply nilpotentBCH_commuting_maps (A := TruncatedSeries (FreeAlgebra ℚ X) s)
    (B := TruncatedSeries (FreeAlgebra ℚ X ⊗[ℚ] FreeAlgebra ℚ X) s) I hI J hJ L R
    (fun _ ha => truncatedSeriesMap_positive s _ ha)
    (fun _ ha => truncatedSeriesMap_positive s _ ha) _ hp0 hq0
  intro a b
  apply truncatedSeriesMap_commute
  intro u v
  change (u ⊗ₜ[ℚ] 1) * (1 ⊗ₜ[ℚ] v) = (1 ⊗ₜ[ℚ] v) * (u ⊗ₜ[ℚ] 1)
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end Erdos3

end

section

namespace Erdos3
variable {X : Type*}
attribute [local instance] LieRing.ofAssociativeRing

noncomputable def scaledFreeGenerator (s : ℕ) (x : X) : TruncatedSeries (FreeAlgebra ℚ X) s :=
  truncatedSeriesMk s (PowerSeries.monomial 1 (FreeAlgebra.ι ℚ x))

theorem scaledFreeGenerator_positive (s : ℕ) (x : X) :
    scaledFreeGenerator s x ∈ truncatedSeriesPositive s := by
  rw [mem_truncatedSeriesPositive]
  change PowerSeries.constantCoeff (PowerSeries.monomial 1 (FreeAlgebra.ι ℚ x)) = 0
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_monomial]
  rfl

theorem scaledFreeGenerator_primitive (s : ℕ) (x : X) :
    TruncatedPrimitive (scaledFreeGenerator s x) := by
  apply (truncatedPrimitive_iff_coeff _).mpr
  intro n hn
  change FreePrimitive (PowerSeries.coeff n (PowerSeries.monomial 1 (FreeAlgebra.ι ℚ x)))
  rw [PowerSeries.coeff_monomial]
  split_ifs
  · exact freePrimitive_generator x
  · simp [FreePrimitive]

theorem scaled_bchPolynomial (s : ℕ) :
    truncatedSeriesMk s (freeScaleSeries (bchPolynomial (s + 1))) =
      nilpotentBCH (scaledFreeGenerator s (0 : Fin 2)) (scaledFreeGenerator s (1 : Fin 2)) := by
  have h := bchPolynomialEval_eq (A := TruncatedSeries (FreeAlgebra ℚ (Fin 2)) s)
    (truncatedSeriesPositive s) (k := s + 1)
    (fun _ ha => truncatedSeriesPositive_pow ha)
    (a := scaledFreeGenerator s (0 : Fin 2)) (b := scaledFreeGenerator s (1 : Fin 2))
    (scaledFreeGenerator_positive s (0 : Fin 2)) (scaledFreeGenerator_positive s (1 : Fin 2))
  rw [bchPolynomialEval_formula] at h
  simpa only [bchPolynomial, map_finiteLog, map_sub, map_mul, map_one, map_finiteExp,
    freeScaleSeries_generator, scaledFreeGenerator] using h

theorem bchHomogeneousPart_primitive (s n : ℕ) (hn : n ≤ s) :
    FreePrimitive (freeHomogeneousPart n (bchPolynomial (s + 1))) := by
  have h := (scaledFreeGenerator_primitive s (0 : Fin 2)).bch
    (scaledFreeGenerator_primitive s (1 : Fin 2))
    (scaledFreeGenerator_positive s (0 : Fin 2)) (scaledFreeGenerator_positive s (1 : Fin 2))
  rw [← scaled_bchPolynomial] at h
  exact h.coeff n hn

theorem bchHomogeneousPart_mem (s n : ℕ) (hn : n ≤ s) :
    freeHomogeneousPart n (bchPolynomial (s + 1)) ∈ freeAssociativeLieSubalgebra :=
  (bchHomogeneousPart_primitive s n hn).mem

theorem bchTruncation_mem (s : ℕ) :
    freeTruncation s (bchPolynomial (s + 1)) ∈ freeAssociativeLieSubalgebra := by
  rw [freeTruncation_apply]
  apply freeAssociativeLieSubalgebra.sum_mem
  intro n hn
  exact bchHomogeneousPart_mem s n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))

noncomputable def bchLiePolynomial (s : ℕ) : FreeLieAlgebra ℚ (Fin 2) :=
  Classical.choose (bchTruncation_mem s)

theorem bchLiePolynomial_expansion (s : ℕ) :
    freeLieAssociativeExpansion (bchLiePolynomial s) = freeTruncation s (bchPolynomial (s + 1)) :=
  Classical.choose_spec (bchTruncation_mem s)

noncomputable def lieBCH {L : Type*} [LieRing L] [LieAlgebra ℚ L] (s : ℕ) (a b : L) : L :=
  FreeLieAlgebra.lift ℚ ![a, b] (bchLiePolynomial s)

end Erdos3

end

section

namespace Erdos3

noncomputable def bchWordCoefficients (s : ℕ) : FreeSemigroup (Fin 2) →₀ ℚ :=
  (freeLieWordExpansion (bchLiePolynomial s)).coeff

noncomputable def bchBracketSupport (s : ℕ) : Finset (FreeSemigroup (Fin 2)) :=
  (bchWordCoefficients s).support

noncomputable def bchBracketCoefficient (s : ℕ) (w : FreeSemigroup (Fin 2)) : ℚ :=
  bchWordCoefficients s w / w.length

theorem bchWordExpansion_truncation (s : ℕ) :
    wordTruncation s (freeLieWordExpansion (bchLiePolynomial s)) =
      freeLieWordExpansion (bchLiePolynomial s) := by
  apply wordPolynomialEmbedding_injective
  rw [wordPolynomialEmbedding_truncation, wordPolynomialEmbedding_freeLieExpansion,
    bchLiePolynomial_expansion, freeTruncation_idempotent]

theorem bchBracketSupport_length (s : ℕ) {w : FreeSemigroup (Fin 2)}
    (hw : w ∈ bchBracketSupport s) : w.length ≤ s := by
  have h := congrArg (fun p : WordPolynomial (Fin 2) => p.coeff w) (bchWordExpansion_truncation s)
  rw [wordTruncation_coeff] at h
  by_contra hgt
  rw [if_neg hgt] at h
  exact (Finsupp.mem_support_iff.mp hw) h.symm

theorem lieBCH_bracket_formula {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (s : ℕ) (a b : L) :
    lieBCH s a b = ∑ w ∈ bchBracketSupport s, bchBracketCoefficient s w • dynkinWord ![a, b] w := by
  rw [lieBCH, ← dynkinProjection_lift]
  change (bchWordCoefficients s).sum (fun w r => r • ((w.length : ℚ)⁻¹ • dynkinWord ![a, b] w)) = _
  simp only [Finsupp.sum, bchBracketSupport, bchBracketCoefficient, smul_smul, div_eq_mul_inv]

noncomputable def bchCoefficientHeight (s : ℕ) : ℕ :=
  1 + (bchBracketSupport s).sup (fun w =>
    max (bchBracketCoefficient s w).num.natAbs (bchBracketCoefficient s w).den)

theorem bchBracketCoefficient_height (s : ℕ) {w : FreeSemigroup (Fin 2)}
    (hw : w ∈ bchBracketSupport s) : RationalHeightLE (bchBracketCoefficient s w) (bchCoefficientHeight s) := by
  have h := Finset.le_sup (f := fun w =>
    max (bchBracketCoefficient s w).num.natAbs (bchBracketCoefficient s w).den) hw
  constructor
  · exact (le_max_left _ _).trans (h.trans (Nat.le_add_left _ 1))
  · exact (le_max_right _ _).trans (h.trans (Nat.le_add_left _ 1))

theorem exists_bch_integer_coefficients (s : ℕ) :
    ∃ D : ℕ, 0 < D ∧ D ≤ bchCoefficientHeight s ^ (bchBracketSupport s).card ∧
      ∃ c : (w : FreeSemigroup (Fin 2)) → w ∈ bchBracketSupport s → ℤ,
        (∀ w hw, (c w hw : ℚ) = (D : ℚ) * bchBracketCoefficient s w) ∧
        ∀ w hw, (c w hw).natAbs ≤ bchCoefficientHeight s ^ (bchBracketSupport s).card := by
  classical
  let q : bchBracketSupport s → ℚ := fun w => bchBracketCoefficient s w
  have hq : ∀ w, RationalHeightLE (q w) (bchCoefficientHeight s) :=
    fun w => bchBracketCoefficient_height s w.property
  obtain ⟨D, hD, hDb, c, hc, hcb⟩ := exists_bounded_integer_array q hq
  refine ⟨D, hD, ?_, (fun w hw => c ⟨w, hw⟩), ?_, ?_⟩
  · simpa only [Fintype.card_coe] using hDb
  · intro w hw
    exact hc ⟨w, hw⟩
  · intro w hw
    simpa only [Fintype.card_coe] using hcb ⟨w, hw⟩

end Erdos3

end

section

namespace Erdos3
variable {X A : Type*} [Ring A] [Algebra ℚ A]
attribute [local instance] LieRing.ofAssociativeRing

namespace NilpotentAlgebraFiltration
variable {s : ℕ} (F : NilpotentAlgebraFiltration A s) (f : X → A)

theorem eval_freeWord_mem (hf : ∀ x, f x ∈ F.layer 1) (w : FreeMonoid X) :
    FreeAlgebra.lift ℚ f (freeWord w) ∈ F.layer w.length := by
  induction w using freeMonoid_induction_right with
  | h1 => simp [F.zero_eq_top]
  | hstep w x hw =>
    rw [map_mul, map_mul, freeWord_of, FreeAlgebra.lift_ι_apply,
      FreeMonoid.length_mul, FreeMonoid.length_of]
    exact F.mul_mem hw (hf x)

theorem eval_freeWord_eq_zero (hf : ∀ x, f x ∈ F.layer 1) (w : FreeMonoid X)
    (hw : s < w.length) : FreeAlgebra.lift ℚ f (freeWord w) = 0 := by
  have h := F.antitone (Nat.succ_le_of_lt hw) (F.eval_freeWord_mem f hf w)
  simpa only [F.terminal, Submodule.mem_bot] using h

theorem eval_freeTruncation (hf : ∀ x, f x ∈ F.layer 1) (p : FreeAlgebra ℚ X) :
    FreeAlgebra.lift ℚ f (freeTruncation s p) = FreeAlgebra.lift ℚ f p := by
  apply freeAlgebra_linear_induction (fun p =>
    FreeAlgebra.lift ℚ f (freeTruncation s p) = FreeAlgebra.lift ℚ f p)
  · simp
  · intro p q hp hq
    simp only [map_add, hp, hq]
  · intro r p hp
    simp only [map_smul, hp]
  · intro w
    rw [freeTruncation_word]
    split_ifs with hw
    · rfl
    · rw [map_zero, F.eval_freeWord_eq_zero f hf w (Nat.lt_of_not_ge hw)]

end NilpotentAlgebraFiltration

theorem freeLieAssociativeExpansion_eval (f : X → A) (p : FreeLieAlgebra ℚ X) :
    FreeAlgebra.lift ℚ f (freeLieAssociativeExpansion p) = FreeLieAlgebra.lift ℚ f p := by
  have h : (FreeAlgebra.lift ℚ f).toLieHom.comp freeLieAssociativeExpansion = FreeLieAlgebra.lift ℚ f := by
    apply FreeLieAlgebra.hom_ext
    intro x
    simp [freeLieAssociativeExpansion]
  exact DFunLike.congr_fun h p

theorem NilpotentAlgebraFiltration.lieBCH_eq {s : ℕ} (F : NilpotentAlgebraFiltration A s)
    {a b : A} (ha : a ∈ F.layer 1) (hb : b ∈ F.layer 1) : lieBCH s a b = nilpotentBCH a b := by
  rw [lieBCH, ← freeLieAssociativeExpansion_eval, bchLiePolynomial_expansion,
    F.eval_freeTruncation ![a, b] (by intro x; fin_cases x <;> assumption)]
  exact F.bchPolynomial_formula ha hb

end Erdos3

end

section

namespace Erdos3

open Module

section General

variable {X Y L : Type*} [TopologicalSpace Y] [LieRing L] [LieAlgebra ℚ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousConstSMul ℚ L]

omit [IsTopologicalAddGroup L] [ContinuousConstSMul ℚ L] in
theorem continuous_rightBracketList
    (hlie : Continuous (fun z : L × L => ⁅z.1, z.2⁆))
    (f : X → Y → L) (hf : ∀ x, Continuous (f x)) (xs : List X)
    (a : Y → L) (ha : Continuous a) :
    Continuous (fun y => rightBracketList (fun x => f x y) xs (a y)) := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    exact ih (fun y => ⁅a y, f x y⁆) (hlie.comp (ha.prodMk (hf x)))

omit [IsTopologicalAddGroup L] [ContinuousConstSMul ℚ L] in
theorem continuous_dynkinWord
    (hlie : Continuous (fun z : L × L => ⁅z.1, z.2⁆))
    (f : X → Y → L) (hf : ∀ x, Continuous (f x)) (w : FreeSemigroup X) :
    Continuous (fun y => dynkinWord (fun x => f x y) w) :=
  continuous_rightBracketList hlie f hf w.tail (f w.head) (hf w.head)

theorem continuous_lieBCH
    (hlie : Continuous (fun z : L × L => ⁅z.1, z.2⁆)) (s : ℕ) :
    Continuous (fun z : L × L => lieBCH s z.1 z.2) := by
  simp only [lieBCH_bracket_formula]
  apply continuous_finsetSum
  intro w _
  apply Continuous.const_smul
  exact continuous_dynkinWord hlie (fun i (z : L × L) => ![z.1, z.2] i)
    (by intro i; fin_cases i; exact continuous_fst; exact continuous_snd) w

end General

section Real

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]

theorem continuous_lie_of_real_basis (e : Basis ι ℝ L) :
    Continuous (fun z : L × L => ⁅z.1, z.2⁆) := by
  classical
  have hcoord (i : ι) : Continuous (fun x : L => e.repr x i) :=
    (continuous_apply i).comp e.equivFunL.continuous
  have hformula (a b : L) : ⁅a, b⁆ =
      ∑ i, ∑ j, e.repr a i • e.repr b j • ⁅e i, e j⁆ := by
    conv_lhs => rw [← e.sum_repr a, ← e.sum_repr b]
    simp only [sum_lie, lie_sum, smul_lie, lie_smul, Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact smul_comm _ _ _
  have heq : (fun z : L × L => ⁅z.1, z.2⁆) =
      (fun z => ∑ i, ∑ j, e.repr z.1 i • e.repr z.2 j • ⁅e i, e j⁆) :=
    funext (fun z => hformula z.1 z.2)
  rw [heq]
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact ((hcoord i).comp continuous_fst).smul
    (((hcoord j).comp continuous_snd).smul continuous_const)

theorem continuous_lie_finiteDimensional [FiniteDimensional ℝ L] :
    Continuous (fun z : L × L => ⁅z.1, z.2⁆) :=
  continuous_lie_of_real_basis (Module.finBasis ℝ L)

end Real

end Erdos3

end

end OAI

end


