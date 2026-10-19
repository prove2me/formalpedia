-- Prove2me | Definitions.Def_OAIE3v2B007
-- name    : OAIE3v2B007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:57:19.565559+00:00
-- url     : https://prove2.me/theorems/301ed100-a73d-43fc-85f0-ec225ae29cd9
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 8 of 311
-- statement:
--   Definitions bundle 8 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Dynamics/DenseProductPowerBudget.lean`, `Dynamics/MultiaffineBiasBudget.lean`, `Estimates/CommonDenominatorMultiples.lean`, `Estimates/ComplexFiniteMeans.lean`, `Estimates/CorrelationDerivative.lean`, `Estimates/DenseCorrelationPairs.lean`, `Estimates/DenseProductApproximation.lean`, `Estimates/FiniteBiasedSlice.lean`, `Estimates/HomogeneousScaledSubstitution.lean`, `Estimates/MultiaffineBias.lean`, `Estimates/MultiaffineExpansion.lean`, `Estimates/MultiaffineOptionExpansion.lean`, `Estimates/ShiftTestingGowers.lean`, `FixedDensity/Energy.lean`, `Geometry/BoxCornerMean.lean`, `Geometry/BoxDifferenceHom.lean`, `Geometry/IntervalBoxDifference.lean`, `Geometry/MultilinearBoxInverse.lean`, `Lattices/IntegerFiberCount.lean`, `Lattices/NearIntegerMultiples.lean`, `Linear/MatrixCoordinateSlice.lean`, `Polynomial/AffineShiftPolynomial.lean`, `Polynomial/DiagonalTensorPolynomial.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerFiberCount
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem card_integer_set_le_diameter_add_one (A : Finset ℤ) {L : ℝ} (hL : 0 ≤ L)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, |(x : ℝ) - y| ≤ L) :
    (A.card : ℝ) ≤ L + 1 := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp only [Finset.card_empty, Nat.cast_zero]
    linarith
  have hsub : A ⊆ Finset.Icc (A.min' hA) (A.max' hA) := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨A.min'_le x hx, A.le_max' x hx⟩
  have hcard : (A.card : ℝ) ≤ (A.max' hA : ℝ) + 1 - A.min' hA := by
    have hc := Finset.card_le_card hsub
    have hi := Int.card_Icc_of_le (A.min' hA) (A.max' hA)
      (le_trans (A.min'_le_max' hA) (by omega))
    have hc' : (A.card : ℤ) ≤ A.max' hA + 1 - A.min' hA := by
      exact_mod_cast hi ▸ (show (A.card : ℤ) ≤ (Finset.Icc (A.min' hA) (A.max' hA)).card by
        exact_mod_cast hc)
    exact_mod_cast hc'
  have hd := (abs_le.mp (hdiam _ (A.max'_mem hA) _ (A.min'_mem hA))).2
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonDenominatorMultiples
namespace OAI

section

namespace Erdos3

theorem short_difference_card_of_density {H Q : ℕ} {ρ : ℝ}
    (hQ : 0 < Q) (hρQ : 4 ≤ ρ * Q) (hρH : 4 ≤ ρ * H)
    (D : Finset ℤ) (hsize : ρ * H ≤ (D.card : ℝ)) :
    2 * H / Q + 1 < D.card := by
  have hQ' : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have hdiv : ((2 * H / Q : ℕ) : ℝ) ≤ (2 * H : ℝ) / Q := by
    apply (le_div_iff₀ hQ').mpr
    exact_mod_cast Nat.div_mul_le_self (2 * H) Q
  have hquot : (2 * H : ℝ) / Q ≤ ρ * H / 2 := by
    apply (div_le_iff₀ hQ').mpr
    have h := mul_le_mul_of_nonneg_right hρQ (Nat.cast_nonneg (α := ℝ) H)
    nlinarith only [h]
  have hreal : ((2 * H / Q + 1 : ℕ) : ℝ) < D.card := by
    push_cast
    linarith
  exact_mod_cast hreal

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

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CorrelationDerivative
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

omit [AddCommGroup H] in
theorem expect_star (f : H → ℂ) : (𝔼 x, star (f x)) = star (𝔼 x, f x) := by
  simp [Fintype.expect_eq_sum_div_card]

omit [AddCommGroup H] in
theorem expect_re (f : H → ℂ) : (𝔼 x, f x).re = 𝔼 x, (f x).re := by
  simp [Fintype.expect_eq_sum_div_card]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem mul_star_re_eq_norm_sq (z : ℂ) : (z * star z).re = ‖z‖ ^ 2 := by
  change (z * (starRingEnd ℂ) z).re = ‖z‖ ^ 2
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftTestingGowers
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {H Ω : Type*} [Fintype H] [Fintype Ω]

theorem square_norm_mean_eq_cross_re (v : H → ℂ) :
    ‖𝔼 h, v h‖ ^ 2 = (𝔼 h, 𝔼 k, v h * star (v k)).re := by
  rw [← Fintype.expect_mul_expect, expect_star, mul_star_re_eq_norm_sq]

theorem mean_square_family_le_cross_norm (v : H → Ω → ℂ) :
    (𝔼 x, ‖𝔼 h, v h x‖ ^ 2) ≤ 𝔼 h, 𝔼 k, ‖𝔼 x, v h x * star (v k x)‖ := by
  simp_rw [square_norm_mean_eq_cross_re]
  rw [← expect_re, Finset.expect_comm]
  have hid (h : H) :
      (𝔼 x, 𝔼 k, v h x * star (v k x)) = 𝔼 k, 𝔼 x, v h x * star (v k x) :=
    Finset.expect_comm _ _ _
  simp_rw [hid, expect_re]
  apply Finset.expect_le_expect
  intro h _
  apply Finset.expect_le_expect
  intro k _
  rw [← expect_re]
  exact Complex.re_le_norm _

theorem finite_family_cauchy_schwarz [Nonempty Ω]
    (B : Ω → ℂ) (v : H → Ω → ℂ) {M : ℝ} (hB : ∀ x, ‖B x‖ ≤ M) :
    ‖𝔼 x, B x * (𝔼 h, v h x)‖ ^ 2 ≤
      M ^ 2 * (𝔼 h, 𝔼 k, ‖𝔼 x, v h x * star (v k x)‖) := by
  have hcs := norm_expect_mul_star_sq_le B (fun x => star (𝔼 h, v h x))
  simp only [star_star, norm_star] at hcs
  have hBM : (𝔼 x, ‖B x‖ ^ 2) ≤ M ^ 2 :=
    (Finset.expect_le_expect (fun x _ =>
      pow_le_pow_left₀ (norm_nonneg _) (hB x) 2)).trans_eq (Fintype.expect_const _)
  exact hcs.trans ((mul_le_mul_of_nonneg_right hBM
    (Finset.expect_nonneg (fun x _ => sq_nonneg _))).trans
      (mul_le_mul_of_nonneg_left (mean_square_family_le_cross_norm v) (sq_nonneg M)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseCorrelationPairs
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_dense_level_set {H : Type*} [Fintype H] [Nonempty H]
    (f : H → ℝ) {a : ℝ} (ha : 0 ≤ a) (hf : ∀ h, f h ≤ 1) (hmean : a ≤ 𝔼 h, f h) :
    ∃ S : Finset H, a / 2 * Fintype.card H ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, a / 2 ≤ f h := by
  classical
  let S := Finset.univ.filter (fun h => a / 2 ≤ f h)
  have hpoint (h : H) : f h ≤ a / 2 + (if h ∈ S then (1 : ℝ) else 0) := by
    by_cases hs : h ∈ S
    · simp only [hs, ite_true]
      linarith [hf h]
    · simp only [hs, ite_false]
      have hsmall : f h < a / 2 := by simpa only [S, Finset.mem_filter,
        Finset.mem_univ, true_and, not_le] using hs
      linarith
  have hindicator : (𝔼 h, if h ∈ S then (1 : ℝ) else 0) =
      (S.card : ℝ) / Fintype.card H := by
    rw [Fintype.expect_eq_sum_div_card]
    simp
  have h := hmean.trans (Finset.expect_le_expect (fun h _ => hpoint h))
  rw [Finset.expect_add_distrib, Fintype.expect_const, hindicator] at h
  have hcard : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
  refine ⟨S, ?_, fun h hh => (Finset.mem_filter.mp hh).2⟩
  apply (le_div_iff₀ hcard).mp
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NearIntegerMultiples
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def NearInteger (ε x : ℝ) : Prop := ∃ m : ℤ, |x-m| ≤ ε

noncomputable def nearIntegerDensity {X : Type*} [Fintype X] (a : X → ℝ) (ε : ℝ) : ℝ :=
  𝔼 x, if NearInteger ε (a x) then (1 : ℝ) else 0

theorem nearIntegerDensity_eq_card {X : Type*} [Fintype X] (a : X → ℝ) (ε : ℝ) :
    nearIntegerDensity a ε =
      ((Finset.univ.filter (fun x => NearInteger ε (a x))).card : ℝ)/Fintype.card X := by
  simp [nearIntegerDensity, Fintype.expect_eq_sum_div_card]

theorem nearIntegerDensity_le_one {X : Type*} [Fintype X] [Nonempty X]
    (a : X → ℝ) (ε : ℝ) : nearIntegerDensity a ε ≤ 1 := by
  rw [nearIntegerDensity_eq_card]
  apply (div_le_one (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card X)).mpr
  exact_mod_cast (Finset.card_filter_le Finset.univ (fun x => NearInteger ε (a x)))

theorem card_div_le_nearIntegerDensity {X : Type*} [Fintype X]
    (a : X → ℝ) (ε : ℝ) (S : Finset X) (hS : ∀ x ∈ S, NearInteger ε (a x)) :
    (S.card : ℝ)/Fintype.card X ≤ nearIntegerDensity a ε := by
  rw [nearIntegerDensity_eq_card]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (Finset.card_le_card (show S ⊆ Finset.univ.filter (fun x => NearInteger ε (a x)) from
    fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ x, hS x hx⟩))

theorem exists_constant_denominator_fiber {X : Type*} (S : Finset X) (q : X → ℕ)
    {K : ℕ} (hK : 0 < K) (hq : ∀ x ∈ S, 0 < q x ∧ q x ≤ K)
    {μ : ℝ} (hsize : (K : ℝ)*μ ≤ S.card) :
    ∃ q₀ : ℕ, 0 < q₀ ∧ q₀ ≤ K ∧ ∃ E : Finset X,
      E ⊆ S ∧ μ ≤ E.card ∧ ∀ x ∈ E, q x = q₀ := by
  have hmap : ∀ x ∈ S, q x ∈ Finset.Icc 1 K := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨(hq x hx).1, (hq x hx).2⟩
  obtain ⟨q₀, hq₀, hlarge⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    hmap (show (Finset.Icc 1 K).Nonempty from ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hK⟩⟩)
    (by simpa only [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] using hsize)
  refine ⟨q₀, (Finset.mem_Icc.mp hq₀).1, (Finset.mem_Icc.mp hq₀).2,
    S.filter (fun x => q x = q₀), Finset.filter_subset _ _, hlarge, ?_⟩
  intro x hx
  exact (Finset.mem_filter.mp hx).2

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem nearIntegerDensity_product {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → ℝ) (ε : ℝ) :
    nearIntegerDensity (fun p : X × Y => f p.1 p.2) ε =
      𝔼 x, nearIntegerDensity (f x) ε := by
  unfold nearIntegerDensity
  exact Finset.expect_product' _ _ (fun x y => if NearInteger ε (f x y) then (1 : ℝ) else 0)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.DenseProductPowerBudget
namespace OAI

section

namespace Erdos3

def denseProductBudget : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n+1, B => 512*B^2*(denseProductBudget n (16*B^2)+1)

theorem denseProductBudget_pos (n B : ℕ) (hB : 1 ≤ B) : 0 < denseProductBudget n B := by
  have hBp : 0 < B := by omega
  cases n <;> simp only [denseProductBudget] <;> positivity

theorem denseProductBudget_step_bounds (n B : ℕ) (hB : 1 ≤ B) :
    8*B ≤ denseProductBudget (n+1) B ∧
    denseProductBudget n (16*B^2) ≤ denseProductBudget (n+1) B ∧
    256*B^2 ≤ denseProductBudget (n+1) B ∧
    384*B^2*denseProductBudget n (16*B^2) ≤ denseProductBudget (n+1) B ∧
    8*B*denseProductBudget n (16*B^2) ≤ denseProductBudget (n+1) B := by
  let C := denseProductBudget n (16*B^2)
  have hC : 1 ≤ C := denseProductBudget_pos n (16*B^2) (by nlinarith)
  have hsq : B ≤ B^2 := by nlinarith
  have hs1 : 1 ≤ B^2 := by nlinarith
  have hBC : B*C ≤ B^2*C := Nat.mul_le_mul_right C hsq
  have hBC' : B ≤ B^2*C := hsq.trans (le_mul_of_one_le_right (Nat.zero_le _) hC)
  have hCC : C ≤ B^2*C := le_mul_of_one_le_left (Nat.zero_le C) hs1
  have hsqC : B^2 ≤ B^2*C := le_mul_of_one_le_right (Nat.zero_le _) hC
  have hlarge : 384*B^2*C ≤ 512*B^2*(C+1) := by nlinarith [Nat.zero_le (B^2*C)]
  change 8*B ≤ 512*B^2*(C+1) ∧ C ≤ 512*B^2*(C+1) ∧
    256*B^2 ≤ 512*B^2*(C+1) ∧ 384*B^2*C ≤ 512*B^2*(C+1) ∧
    8*B*C ≤ 512*B^2*(C+1)
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  exact ⟨hlarge, by nlinarith⟩

def denseProductExponent : ℕ → ℕ
  | 0 => 0
  | n+1 => 2*denseProductExponent n+2

def denseProductConstant : ℕ → ℕ
  | 0 => 1
  | n+1 => 512*(denseProductConstant n*16^denseProductExponent n+1)

theorem denseProductConstant_pos (n : ℕ) : 0 < denseProductConstant n := by
  cases n <;> simp only [denseProductConstant] <;> positivity

theorem denseProductBudget_le_power (n B : ℕ) (hB : 1 ≤ B) :
    denseProductBudget n B ≤ denseProductConstant n*B^denseProductExponent n := by
  induction n generalizing B with
  | zero => simp [denseProductBudget, denseProductConstant, denseProductExponent]
  | succ n ih =>
    have hB' : 1 ≤ 16*B^2 := by nlinarith
    have hp : 1 ≤ B^(2*denseProductExponent n) := by
      have := pow_pos (show 0 < B by omega) (2*denseProductExponent n)
      omega
    calc
      _ ≤ 512*B^2*(denseProductConstant n*(16*B^2)^denseProductExponent n+1) := by
        exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (ih (16*B^2) hB') 1)
      _ = 512*B^2*(denseProductConstant n*16^denseProductExponent n*B^(2*denseProductExponent n)+1) := by
        rw [mul_pow, ← pow_mul]
        ring
      _ ≤ 512*B^2*(denseProductConstant n*16^denseProductExponent n*B^(2*denseProductExponent n)+
          B^(2*denseProductExponent n)) := by gcongr
      _ = denseProductConstant (n+1)*B^denseProductExponent (n+1) := by
        simp only [denseProductConstant, denseProductExponent, pow_add, pow_two]
        ring

end Erdos3

end

section

namespace Erdos3

def denseProductDensityConstant (e : ℕ) : ℕ :=
  denseProductConstant e * 2^denseProductExponent e

noncomputable def denseProductDensityBudget (e : ℕ) (η : ℝ) : ℝ :=
  (denseProductDensityConstant e : ℝ)/η^denseProductExponent e

theorem denseProductDensityBudget_pos (e : ℕ) {η : ℝ} (hη : 0 < η) :
    0 < denseProductDensityBudget e η := by
  have hc : 0 < denseProductConstant e := denseProductConstant_pos e
  unfold denseProductDensityBudget denseProductDensityConstant
  positivity

theorem reciprocal_density_ceil {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    1 ≤ ⌈1/η⌉₊ ∧ 1/(⌈1/η⌉₊ : ℝ) ≤ η ∧ (⌈1/η⌉₊ : ℝ) ≤ 2/η := by
  have hpos : 1 ≤ ⌈1/η⌉₊ := Nat.one_le_ceil_iff.mpr (by positivity)
  have hceilpos : (0 : ℝ) < ⌈1/η⌉₊ := by exact_mod_cast hpos
  have hle := Nat.le_ceil (1/η)
  have hnear := (Nat.ceil_lt_add_one (show 0 ≤ 1/η by positivity)).le
  refine ⟨hpos, ?_, ?_⟩
  · apply (div_le_iff₀ hceilpos).mpr
    nlinarith [(div_le_iff₀ hη).mp hle]
  · have hone : 1 ≤ 1/η := (le_div_iff₀ hη).mpr (by simpa using hη1)
    calc
      _ ≤ 1/η+1 := hnear
      _ ≤ 1/η+1/η := add_le_add le_rfl hone
      _ = 2/η := by ring

theorem denseProductBudget_ceil_le (e : ℕ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    (denseProductBudget e ⌈1/η⌉₊ : ℝ) ≤ denseProductDensityBudget e η := by
  obtain ⟨hB, _, hceil⟩ := reciprocal_density_ceil hη hη1
  calc
    (denseProductBudget e ⌈1/η⌉₊ : ℝ) ≤
        (denseProductConstant e : ℝ)*(⌈1/η⌉₊ : ℝ)^denseProductExponent e := by
      exact_mod_cast denseProductBudget_le_power e ⌈1/η⌉₊ hB
    _ ≤ (denseProductConstant e : ℝ)*(2/η)^denseProductExponent e := by gcongr
    _ = denseProductDensityBudget e η := by
      simp only [denseProductDensityBudget, denseProductDensityConstant, Nat.cast_mul,
        Nat.cast_pow, Nat.cast_ofNat, div_pow]
      ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProductApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem nearInteger_mono {ε δ x : ℝ} (h : NearInteger ε x) (hle : ε ≤ δ) :
    NearInteger δ x := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, hm.trans hle⟩

theorem nearInteger_of_pos_density_const {X : Type*} [Fintype X] {ε x : ℝ}
    (h : 0 < nearIntegerDensity (fun _ : X => x) ε) : NearInteger ε x := by
  by_contra hn
  simp [nearIntegerDensity, hn] at h

end Erdos3

end

section

namespace Erdos3

theorem dense_product_step_tolerance {B C H K ε : ℝ}
    (hC : 0 < C) (hH : 1 ≤ H) (hK : 0 < K)
    (hcoef : 384*B^2*C ≤ K) (hε : 0 ≤ ε) (hsmall : ε ≤ 1/K) :
    384*B^2*ε/H ≤ 1/C := by
  have hεK : K*ε ≤ 1 := by nlinarith [(le_div_iff₀ hK).mp hsmall]
  calc
    384*B^2*ε/H ≤ 384*B^2*ε := div_le_self (by positivity) hH
    _ ≤ (K/C)*ε := mul_le_mul_of_nonneg_right ((le_div_iff₀ hC).mpr hcoef) hε
    _ = K*ε/C := by ring
    _ ≤ 1/C := div_le_div_of_nonneg_right hεK hC.le

theorem dense_product_error_composition {B C H K P ε : ℝ}
    (hH : 0 < H) (hP : 0 < P) (hcoef : 384*B^2*C ≤ K) (hε : 0 ≤ ε) :
    C*(384*B^2*ε/H)/P ≤ K*ε/(H*P) := by
  calc
    C*(384*B^2*ε/H)/P = (384*B^2*C)*ε/(H*P) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hε)
      (mul_pos hH hP).le

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_common_rational_approximations_varying {I : Type*} [Fintype I] [DecidableEq I]
    (θ Q E : I → ℝ)
    (h : ∀ i, ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Q i ∧ ∃ m : ℤ, |θ i - (m : ℝ) / q| ≤ E i) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ ∏ i, Q i ∧
      ∃ a : I → ℤ, ∀ i, |θ i - (a i : ℝ) / D| ≤ E i := by
  choose q hq hqQ m hm using h
  let D := ∏ i, q i
  let rest := fun i => ∏ j ∈ Finset.univ.erase i, q j
  have hrest (i : I) : 0 < rest i := Finset.prod_pos (fun j _ => hq j)
  have hD (i : I) : q i * rest i = D :=
    Finset.mul_prod_erase Finset.univ q (Finset.mem_univ i)
  have hDp : 0 < D := Finset.prod_pos (fun i _ => hq i)
  refine ⟨D, hDp, ?_, (fun i => (rest i : ℤ) * m i), ?_⟩
  · calc
      (D : ℝ) = ∏ i, (q i : ℝ) := by simp [D]
      _ ≤ ∏ i, Q i := Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => hqQ i)
  · intro i
    have hqr : (0 : ℝ) < q i := by exact_mod_cast hq i
    have hrr : (0 : ℝ) < rest i := by exact_mod_cast hrest i
    have hd : (D : ℝ) = (q i : ℝ) * rest i := by exact_mod_cast (hD i).symm
    have he : (((rest i : ℤ) * m i : ℤ) : ℝ) / (D : ℝ) = (m i : ℝ) / q i := by
      push_cast
      rw [hd]
      field_simp
    rw [he]
    exact hm i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.IntervalBoxDifference
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

abbrev SymmetricIntegerInterval (N : ℕ) :=
  ↥(Finset.Icc (-(N : ℤ)) (N : ℤ))

instance symmetricIntegerInterval_inhabited (N : ℕ) : Inhabited (SymmetricIntegerInterval N) :=
  ⟨⟨0, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩⟩

theorem symmetricIntegerInterval_abs_le (N : ℕ) (x : SymmetricIntegerInterval N) :
    |(x : ℤ)| ≤ (N : ℤ) :=
  abs_le.mpr (Finset.mem_Icc.mp x.property)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

def intervalDifference (N : ℕ) (y x : Fin N) : SymmetricIntegerInterval N :=
  ⟨(x.val : ℤ)-y.val, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩

def intervalBoxDifference {ι : Type*} (N : ι → ℕ)
    (y x : ∀ i, Fin (N i)) : ∀ i, SymmetricIntegerInterval (N i) :=
  fun i => intervalDifference (N i) (y i) (x i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.MultiaffineBiasBudget
namespace OAI

section

namespace Erdos3

noncomputable def multiaffineBiasBudget (n : ℕ) (ζ : ℝ) : ℝ :=
  denseProductDensityBudget n (ζ^(2^n)/(2*3^n))/ζ^(2^n)

theorem multiaffineBiasBudget_pos (n : ℕ) {ζ : ℝ} (hζ : 0 < ζ) :
    0 < multiaffineBiasBudget n ζ := by
  have h := denseProductDensityBudget_pos n
    (show 0 < ζ^(2^n)/(2*3^n) by positivity)
  exact div_pos h (pow_pos hζ _)

theorem multiaffineBiasBudget_bounds (n : ℕ) {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    denseProductDensityBudget n (ζ^(2^n)/(2*3^n)) ≤ multiaffineBiasBudget n ζ ∧
    multiaffineBiasBudget n ζ * ζ^(2^n) = denseProductDensityBudget n (ζ^(2^n)/(2*3^n)) := by
  have hp : 0 < ζ^(2^n) := pow_pos hζ _
  have hp1 : ζ^(2^n) ≤ 1 := pow_le_one₀ hζ.le hζ1
  have hL := denseProductDensityBudget_pos n
    (show 0 < ζ^(2^n)/(2*3^n) by positivity)
  constructor
  · apply (le_div_iff₀ hp).mpr
    exact mul_le_of_le_one_right hL.le hp1
  · exact div_mul_cancel₀ _ hp.ne'

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteBiasedSlice
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_biased_finite_slice {A B : Type*} [Fintype A] [Fintype B] [Nonempty A]
    (F : A → B → ℂ) {δ : ℝ} (hδ : δ ≤ ‖𝔼 a, 𝔼 b, F a b‖) :
    ∃ a, δ ≤ ‖𝔼 b, F a b‖ := by
  have hmean : δ ≤ 𝔼 a, ‖𝔼 b, F a b‖ := hδ.trans (RCLike.norm_expect_le (K := ℂ))
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean
  exact ⟨a, ha⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HomogeneousScaledSubstitution
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem homogeneous_aeval_scaled {I J R : Type*} [CommRing R]
    (P : MvPolynomial I R) {h : ℕ} (hP : P.IsHomogeneous h)
    (w : I → R) (Q : MvPolynomial J R) :
    aeval (fun i => C (w i) * Q) P = C (eval w P) * Q ^ h := by
  have hm (a : I →₀ ℕ) (ha : a ∈ P.support) :
      aeval (fun i => C (w i) * Q) (monomial a (P.coeff a)) =
        C (eval w (monomial a (P.coeff a))) * Q ^ h := by
    have hd : (∑ i ∈ a.support, a i) = h := by
      simpa only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] using
        hP (mem_support_iff.mp ha)
    rw [aeval_monomial, eval_monomial]
    simp only [algebraMap_eq, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
      ← map_pow, ← map_prod, Finset.prod_pow_eq_pow_sum, hd, map_mul, mul_assoc]
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  simp only [map_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl hm

end Erdos3

end

end OAI
end

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MultiaffineExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def multiaffineExpansion {R : Type*} [CommRing R] {n : ℕ}
    (c : Finset (Fin n) → R) (x : Fin n → R) : R :=
  ∑ S : Finset (Fin n), c S * ∏ i, if i ∈ S then x i else 1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MultiaffineBias
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem nearInteger_rational_approximation {θ ε : ℝ} {q : ℕ} (hq : 0 < q)
    (hnear : NearInteger ε ((q : ℝ)*θ)) :
    ∃ m : ℤ, |θ-(m : ℝ)/q| ≤ ε := by
  obtain ⟨m,hm⟩ := hnear
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have he : θ-(m : ℝ)/q = ((q : ℝ)*θ-m)/q := by field_simp
  refine ⟨m, ?_⟩
  rw [he, abs_div, abs_of_pos hqp]
  exact (div_le_div_of_nonneg_right hm hqp.le).trans
    (div_le_self ((abs_nonneg _).trans hm) hq1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MultiaffineOptionExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem multiaffineExpansion_affine {n : ℕ} (a b : Finset (Fin n) → ℝ)
    (x : Fin n → ℝ) (t : ℝ) :
    multiaffineExpansion (fun S => a S*t+b S) x =
      multiaffineExpansion a x*t + multiaffineExpansion b x := by
  unfold multiaffineExpansion
  simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.Energy
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable def mean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  𝔼 x, f x

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxCornerMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def MissesBoxCoordinate {n : ℕ} {X : Type*} (U : (Fin n → X) → ℂ) (i : Fin n) : Prop :=
  ∀ x a, U (Function.update x i a) = U x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MatrixCoordinateSlice
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def matrixCoordinateSplit {H I : Type*} [DecidableEq I]
    (j : H → I) (X : I → Type*) :
    (H → ∀ k, X k) ≃ (∀ i, X (j i)) × (∀ i, ∀ k : {k // k ≠ j i}, X k) where
  toFun v := (fun i => v i (j i), fun i k => v i k)
  invFun p i := (Equiv.piSplitAt (j i) X).symm (p.1 i, p.2 i)
  left_inv v := by
    funext i
    exact (Equiv.piSplitAt (j i) X).symm_apply_apply (v i)
  right_inv p := by
    apply Prod.ext
    · funext i
      exact congrArg Prod.fst ((Equiv.piSplitAt (j i) X).apply_symm_apply (p.1 i, p.2 i))
    · funext i
      exact congrArg Prod.snd ((Equiv.piSplitAt (j i) X).apply_symm_apply (p.1 i, p.2 i))

theorem matrixCoordinateSplit_symm_update {H I : Type*} [DecidableEq I]
    (j : H → I) (X : I → Type*) (x x₀ : ∀ i, X (j i))
    (r : ∀ i, ∀ k : {k // k ≠ j i}, X k) :
    (matrixCoordinateSplit j X).symm (x, r) =
      fun i => Function.update ((matrixCoordinateSplit j X).symm (x₀, r) i) (j i) (x i) := by
  funext i k
  by_cases hk : k = j i
  · subst k
    simp [matrixCoordinateSplit, Equiv.piSplitAt]
  · simp [matrixCoordinateSplit, Equiv.piSplitAt, hk]

theorem exists_biased_matrix_coordinate_slice {H I : Type*} [Fintype H] [Fintype I]
    [DecidableEq H] [DecidableEq I]
    (X : I → Type*) [∀ k, Fintype (X k)] [∀ k, Nonempty (X k)]
    (j : H → I) (F : (H → ∀ k, X k) → ℂ) {δ : ℝ}
    (hδ : δ ≤ ‖𝔼 v, F v‖) :
    ∃ b : H → ∀ k, X k, δ ≤ ‖𝔼 x : ∀ i, X (j i),
      F (fun i => Function.update (b i) (j i) (x i))‖ := by
  let e := matrixCoordinateSplit j X
  have he := Fintype.expect_equiv e F (fun p => F (e.symm p)) (fun v => by simp)
  rw [he, ← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm] at hδ
  obtain ⟨r, hr⟩ := exists_biased_finite_slice (fun r x => F (e.symm (x, r))) hδ
  let x₀ : ∀ i, X (j i) := fun i => Classical.choice inferInstance
  refine ⟨e.symm (x₀, r), ?_⟩
  have hmean : (𝔼 x : ∀ i, X (j i), F (e.symm (x, r))) =
      𝔼 x : ∀ i, X (j i), F (fun i => Function.update (e.symm (x₀, r) i) (j i) (x i)) := by
    apply Finset.expect_congr rfl
    intro x _
    exact congrArg F (matrixCoordinateSplit_symm_update j X x x₀ r)
  exact hr.trans_eq (congrArg norm hmean)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MultilinearBoxInverse
namespace OAI

section

namespace Erdos3

open scoped Classical

def stridedMatrixPoint {H I : Type*} {N : I → ℕ}
    (b : H → I → ℝ) (s : I → ℕ) (x : H → ∀ k, Fin (N k)) : H → I → ℝ :=
  fun i k => b i k + (s k : ℝ) * ((x i k).val : ℝ)

noncomputable def stridedMatrixSliceBase {H I : Type*} [DecidableEq I] {N : I → ℕ}
    (b : H → I → ℝ) (s : I → ℕ) (x : H → ∀ k, Fin (N k)) (j : H → I) : H → I → ℝ :=
  fun i => Function.update (stridedMatrixPoint b s x i) (j i) (b i (j i))

theorem stridedMatrixPoint_update {H I : Type*} [DecidableEq I] {N : I → ℕ}
    (b : H → I → ℝ) (s : I → ℕ) (y : H → ∀ k, Fin (N k)) (j : H → I)
    (x : ∀ i, Fin (N (j i))) :
    stridedMatrixPoint b s (fun i => Function.update (y i) (j i) (x i)) =
      fun i => stridedMatrixSliceBase b s y j i +
        ((s (j i) : ℝ) * ((x i).val : ℝ)) • Pi.single (j i) (1 : ℝ) := by
  funext i k
  by_cases hk : k = j i
  · subst k
    simp [stridedMatrixPoint, stridedMatrixSliceBase]
  · simp [stridedMatrixPoint, stridedMatrixSliceBase, hk]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AffineShiftPolynomial
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

noncomputable def affineShiftCoordinate {I : Type*} {n : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ) (i : I) : MvPolynomial (Fin n) ℝ :=
  C (base i) + ∑ j, C (direction j i) * X j

noncomputable def affineShiftPullback {I : Type*} {n : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ) :
    MvPolynomial I ℝ →ₐ[ℝ] MvPolynomial (Fin n) ℝ :=
  aeval (affineShiftCoordinate base direction)

theorem affineShiftPullback_eval {I : Type*} {n : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ)
    (P : MvPolynomial I ℝ) (t : Fin n → ℝ) :
    eval t (affineShiftPullback base direction P) =
      eval (fun i => base i + ∑ j, direction j i * t j) P := by
  change (aeval t) ((aeval (affineShiftCoordinate base direction)) P) =
    (aeval (fun i => base i + ∑ j, direction j i * t j)) P
  rw [comp_aeval_apply]
  simp only [affineShiftCoordinate, map_add, map_sum, map_mul, aeval_C, aeval_X,
    Algebra.algebraMap_self_apply]

theorem affineShiftCoordinate_degree {I : Type*} {n : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ) (i : I) :
    (affineShiftCoordinate base direction i).totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · simp only [totalDegree_C, zero_le]
  · apply totalDegree_finsetSum_le
    intro j _
    exact (totalDegree_mul _ _).trans (by simp)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DiagonalTensorPolynomial
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def tensorDiagonalPolynomial {I R : Type*} [Fintype I] [CommSemiring R]
    {h : ℕ} (θ : (Fin h → I) → R) : MvPolynomial I R :=
  ∑ j : Fin h → I, MvPolynomial.C (θ j) * ∏ i, MvPolynomial.X (j i)

end Erdos3

end

end OAI
end


