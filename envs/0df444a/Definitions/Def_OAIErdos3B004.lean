-- Prove2me | Definitions.Def_OAIErdos3B004
-- name    : OAIErdos3B004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T07:30:36.123855+00:00
-- url     : https://prove2.me/theorems/978d3a8a-61ee-4eeb-8c52-e7a4176b05aa
-- title:
--   OpenAI Erdős-3 split, definitions bundle 5 of 132
-- statement:
--   Definitions bundle 5 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B003`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 5 available.
--
--   Modules: `Lattices.IntegerFiberUniformBound`, `Probability.SmoothProbabilityProfile`, `Estimates.SplitSmoothProductProfile`, `Lattices.ShortIntegerDifference`, `Estimates.CommonDenominatorMultiples`, `Fourier.RectangularGridCharacter`, `Estimates.CyclicShortShiftSet`, `Geometry.BoxDetectionExponents`, `Estimates.FixedPartnerPower`, `Linear.BalancedDualBounds`, `Estimates.ShiftTestingGowers`, `Estimates.DenseCorrelationPairs`, `Estimates.BooleanCubeProduct`, `Estimates.GowersWeightedDerivative`, `Geometry.SupportedCubeEquivTransport`, `Estimates.CubeTranslation`, `Fourier.FiniteSpectrumCutoff`, `Fourier.FiniteFourierSmoothing`, `Estimates.FiniteConvolution`, `Estimates.CyclicCutNeighborhood`, `Lattices.ResidueSliceCountingCost`, `Estimates.PhysicalSliceCost`, `Estimates.WeightedOverlapCorrelation`, `Estimates.EmbeddedFiniteConditioning`, `Lattices.BoxResiduePartition`, `Lattices.PhysicalSubboxResidueSlice`, `Polynomial.AffinePhaseBias`, `Lattices.NearIntegerMultiples`, `Dynamics.DenseProductPowerBudget`, `Estimates.DenseProductApproximation`, `Polynomial.PhasePreservingCauchySchwarz`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B003

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ShortIntegerDifference
namespace OAI

section

namespace Erdos3

theorem exists_short_integer_difference (D : Finset ℤ) {H Q : ℕ} (hQ : 0 < Q)
    (hD : ∀ h ∈ D, |h| ≤ (H : ℤ)) (hcard : 2 * H / Q + 1 < D.card) :
    ∃ x ∈ D, ∃ y ∈ D, x < y ∧ y - x < (Q : ℤ) := by
  let f : ℤ → ℤ := fun h => (h + (H : ℤ)) / (Q : ℤ)
  let B := Finset.Icc (0 : ℤ) ((2 * H / Q : ℕ) : ℤ)
  have hQ' : (0 : ℤ) < Q := by exact_mod_cast hQ
  have hmap : ∀ h ∈ D, f h ∈ B := by
    intro h hh
    have hd := abs_le.mp (hD h hh)
    simp only [B, f, Finset.mem_Icc]
    constructor
    · exact Int.ediv_nonneg (by omega) hQ'.le
    · have hl : h + (H : ℤ) ≤ ((2 * H : ℕ) : ℤ) := by omega
      exact_mod_cast Int.ediv_le_ediv hQ' hl
  have hB : B.card = 2 * H / Q + 1 := by
    simp only [B, Int.card_Icc, sub_zero]
    norm_cast
  obtain ⟨x, hx, y, hy, hxy, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (by rwa [hB] : B.card < D.card) hmap
  have hdif : |x - y| < (Q : ℤ) := by
    have hxrem := Int.emod_nonneg (x + (H : ℤ)) (by omega : (Q : ℤ) ≠ 0)
    have hyrem := Int.emod_nonneg (y + (H : ℤ)) (by omega : (Q : ℤ) ≠ 0)
    have hxlt := Int.emod_lt_of_pos (x + (H : ℤ)) hQ'
    have hylt := Int.emod_lt_of_pos (y + (H : ℤ)) hQ'
    have hxdiv := Int.emod_add_ediv_mul (x + (H : ℤ)) (Q : ℤ)
    have hydiv := Int.emod_add_ediv_mul (y + (H : ℤ)) (Q : ℤ)
    change (x + (H : ℤ)) / Q = (y + (H : ℤ)) / Q at heq
    rw [heq] at hxdiv
    rw [abs_lt]
    constructor <;> omega
  rcases lt_or_gt_of_ne hxy with hxy | hxy
  · exact ⟨x, hx, y, hy, hxy, by have := abs_lt.mp hdif; omega⟩
  · exact ⟨y, hy, x, hx, hxy, by have := abs_lt.mp hdif; omega⟩

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

theorem many_multiples_rational_approximation (D : Finset ℤ) (n : ℤ → ℤ)
    {H Q : ℕ} {α ε ρ : ℝ} (hH : 0 < H) (hQ : 0 < Q)
    (hρ : 0 < ρ) (hε : 0 ≤ ε)
    (hρQ : 4 ≤ ρ * Q) (hρH : 4 ≤ ρ * H)
    (hsmall : 16 * ((Q : ℝ) * ε) ≤ ρ) (hcap : (Q : ℝ) * ε ≤ 1)
    (hsize : ρ * H ≤ (D.card : ℝ))
    (hD : ∀ h ∈ D, |h| ≤ (H : ℤ))
    (hclose : ∀ h ∈ D, |(h : ℝ) * α - n h| ≤ ε) :
    ∃ q : ℕ, 0 < q ∧ q ≤ Q ∧ ∃ p : ℤ,
      |(q : ℝ) * α - p| ≤ 24 * Q * ε / (ρ * H) := by
  obtain ⟨x, hx, y, hy, hxy, hdiff⟩ := exists_short_integer_difference D hQ hD
    (short_difference_card_of_density hQ hρQ hρH D hsize)
  let q := (y - x).toNat
  let p := n y - n x
  have hqcast : (q : ℤ) = y - x := Int.toNat_of_nonneg (by omega)
  have hq : 0 < q := by omega
  have hqQ : q ≤ Q := by omega
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqQ' : (q : ℝ) ≤ Q := Nat.cast_le.mpr hqQ
  have hqε : (q : ℝ) * ε ≤ Q * ε := mul_le_mul_of_nonneg_right hqQ' hε
  have hfirst : |(q : ℝ) * α - p| ≤ 2 * ε := by
    have hxc := abs_le.mp (hclose x hx)
    have hyc := abs_le.mp (hclose y hy)
    have hqr : (q : ℝ) = (y : ℝ) - x := by exact_mod_cast hqcast
    rw [hqr]
    simp only [p, Int.cast_sub]
    rw [abs_le]
    constructor <;> nlinarith only [hxc.1, hxc.2, hyc.1, hyc.2]
  let m : ℤ → ℤ := fun h => (q : ℤ) * n h - h * p
  have hphase : ∀ h ∈ D,
      |(h : ℝ) * ((q : ℝ) * α - p) - m h| ≤ (q : ℝ) * ε := by
    intro h hh
    have hid : (h : ℝ) * ((q : ℝ) * α - p) - m h =
        (q : ℝ) * ((h : ℝ) * α - n h) := by
      simp only [m, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
      ring
    rw [hid, abs_mul, abs_of_nonneg (Nat.cast_nonneg q)]
    exact mul_le_mul_of_nonneg_left (hclose h hh) (Nat.cast_nonneg q)
  have happrox := small_linear_phase_of_many_near_integers D m
    (Nat.cast_pos.mpr hH) hρ (mul_nonneg (Nat.cast_nonneg q) hε)
    (hqε.trans hcap) (by nlinarith only [hsmall, hqε])
    (hfirst.trans (by nlinarith only [mul_le_mul_of_nonneg_right hq' hε]))
    hsize (fun h hh => by exact_mod_cast hD h hh) hphase
  refine ⟨q, hq, hqQ, p, happrox.trans ?_⟩
  apply div_le_div_of_nonneg_right _ (mul_nonneg hρ.le (Nat.cast_nonneg H))
  nlinarith only [hqε]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RectangularGridCharacter
namespace OAI

section

open scoped BigOperators ComplexConjugate ENNReal Real

open Finset Function MeasureTheory Set

namespace Erdos3.CircleFourier

noncomputable section

abbrev Circle := UnitAddCircle

abbrev circleHaar : Measure Circle := AddCircle.haarAddCircle

def integerDistance (x : Circle) : ℝ := ‖x‖

theorem integerDistance_nonneg (x : Circle) : 0 ≤ integerDistance x := norm_nonneg x

theorem integerDistance_le_half (x : Circle) : integerDistance x ≤ 1 / 2 := by
  simpa [integerDistance] using AddCircle.norm_le_half_period (1 : ℝ) one_ne_zero (x := x)

@[simp]
theorem integerDistance_zero : integerDistance (0 : Circle) = 0 := by
  simp [integerDistance]

@[simp]
theorem integerDistance_neg (x : Circle) : integerDistance (-x) = integerDistance x := by
  simp [integerDistance]

@[simp]
theorem integerDistance_coe (x : ℝ) :
    integerDistance (x : Circle) = |x - round x| := by
  simp [integerDistance, UnitAddCircle.norm_eq]

def character (x : Circle) : ℂ := AddCircle.toCircle x

@[simp]
theorem character_zero : character 0 = 1 := by
  simp [character]

@[simp]
theorem character_add (x y : Circle) : character (x + y) = character x * character y := by
  unfold character
  rw [AddCircle.toCircle_add]
  rfl

@[simp]
theorem character_neg (x : Circle) : character (-x) = star (character x) := by
  unfold character
  rw [AddCircle.toCircle_neg, _root_.Circle.coe_inv, Complex.inv_def,
    _root_.Circle.normSq_coe]
  simp

@[simp]
theorem character_nsmul (n : ℕ) (x : Circle) : character (n • x) = character x ^ n := by
  unfold character
  rw [AddCircle.toCircle_nsmul]
  rfl

@[simp]
theorem character_zsmul (n : ℤ) (x : Circle) : character (n • x) = character x ^ n := by
  unfold character
  rw [AddCircle.toCircle_zsmul]
  rfl

@[simp]
theorem character_finset_sum {I : Type*} (s : Finset I) (f : I → Circle) :
    character (∑ i ∈ s, f i) = ∏ i ∈ s, character (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, character_add]

@[simp]
theorem character_fintype_sum {I : Type*} [Fintype I] (f : I → Circle) :
    character (∑ i, f i) = ∏ i, character (f i) := by
  simp

@[simp]
theorem norm_character (x : Circle) : ‖character x‖ = 1 := by
  exact Circle.norm_coe _

theorem character_eq_one_iff (x : Circle) : character x = 1 ↔ x = 0 := by
  constructor
  · intro h
    apply AddCircle.injective_toCircle one_ne_zero
    apply Subtype.ext
    simpa [character] using h
  · rintro rfl
    exact character_zero

def geometricCharacterSum (N : ℕ) (x : Circle) : ℂ :=
  ∑ n ∈ range N, character (n • x)

theorem geometricCharacterSum_mul (N : ℕ) (x : Circle) :
    geometricCharacterSum N x * (character x - 1) = character (N • x) - 1 := by
  simp only [geometricCharacterSum, character_nsmul]
  exact geom_sum_mul (character x) N

theorem norm_character_sub_one_le_two (x : Circle) : ‖character x - 1‖ ≤ 2 := by
  calc
    ‖character x - 1‖ ≤ ‖character x‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num

theorem four_mul_integerDistance_le_norm_character_sub_one (x : Circle) :
    4 * integerDistance x ≤ ‖character x - 1‖ := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective x
  let y : ℝ := r - round r
  have hyabs : |y| ≤ 1 / 2 := by
    simpa [y] using abs_sub_round r
  have hypi_abs : |π * y| ≤ π / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hsin : 2 * |y| ≤ |Real.sin (π * y)| := by
    have h := Real.mul_abs_le_abs_sin hypi_abs
    calc
      2 * |y| = (2 / π) * |π * y| := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
        field_simp [Real.pi_ne_zero]
      _ ≤ |Real.sin (π * y)| := h
  have hry : (r : Circle) = (y : Circle) := by
    simp [y, sub_eq_add_neg]
  have hcharacter :
      character (y : Circle) = Complex.exp (Complex.I * (2 * π * y : ℝ)) := by
    unfold character
    rw [AddCircle.toCircle, Function.Periodic.lift_coe, Circle.coe_exp]
    congr 1
    push_cast
    ring
  rw [integerDistance_coe]
  change 4 * |y| ≤ _
  rw [hry, hcharacter, Complex.norm_exp_I_mul_ofReal_sub_one]
  change 4 * |y| ≤ |2 * Real.sin ((2 * π * y) / 2)|
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    4 * |y| = 2 * (2 * |y|) := by ring
    _ ≤ 2 * |Real.sin (π * y)| :=
      mul_le_mul_of_nonneg_left hsin (by norm_num)
    _ = 2 * |Real.sin ((2 * π * y) / 2)| := by ring_nf

theorem two_mul_integerDistance_mul_norm_geometricCharacterSum_le_one
    (N : ℕ) (x : Circle) :
    2 * integerDistance x * ‖geometricCharacterSum N x‖ ≤ 1 := by
  have hprod :
      ‖geometricCharacterSum N x‖ * ‖character x - 1‖ ≤ 2 := by
    rw [← norm_mul, geometricCharacterSum_mul]
    exact norm_character_sub_one_le_two _
  have hden := four_mul_integerDistance_le_norm_character_sub_one x
  have hnorm : 0 ≤ ‖geometricCharacterSum N x‖ := norm_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hden hnorm]

theorem geometricCharacterSum_eq_sum_fin (N : ℕ) (x : Circle) :
    geometricCharacterSum N x = ∑ n : Fin N, character ((n : ℕ) • x) := by
  rw [Finset.sum_fin_eq_sum_range]
  rw [geometricCharacterSum]
  apply Finset.sum_congr rfl
  intro n hn
  simp [Finset.mem_range.mp hn]

end
end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped Real NNReal

noncomputable def characterLipConstant : ℝ≥0 := ⟨2 * Real.pi, by positivity⟩

theorem coe_characterLipConstant : (characterLipConstant : ℝ) = 2 * Real.pi := rfl

theorem character_coe_exp (r : ℝ) :
    character (r : Circle) = Complex.exp (Complex.I * (2 * Real.pi * r : ℝ)) := by
  unfold character
  rw [AddCircle.toCircle, Function.Periodic.lift_coe, _root_.Circle.coe_exp]
  congr 1
  push_cast
  ring

theorem norm_character_sub_one_le (x : Circle) :
    ‖character x - 1‖ ≤ 2 * Real.pi * ‖x‖ := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective x
  let y : ℝ := r - round r
  have hry : (r : Circle) = (y : Circle) := by simp [y, sub_eq_add_neg]
  change ‖character (r : Circle) - 1‖ ≤ 2 * Real.pi * integerDistance (r : Circle)
  rw [integerDistance_coe]
  change ‖character (r : Circle) - 1‖ ≤ 2 * Real.pi * |y|
  rw [hry, character_coe_exp, Complex.norm_exp_I_mul_ofReal_sub_one]
  have heq : (2 * Real.pi * y) / 2 = Real.pi * y := by ring
  rw [heq, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ 2 * |Real.pi * y| := mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = _ := by rw [abs_mul, abs_of_pos Real.pi_pos]; ring

theorem character_lipschitz : LipschitzWith characterLipConstant character := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hxy : character (x - y) * character y = character x := by
    rw [← character_add, sub_add_cancel]
  have heq : (character (x - y) - 1) * character y = character x - character y := by
    rw [sub_mul, one_mul, hxy]
  have hnorm : ‖character x - character y‖ = ‖character (x - y) - 1‖ := by
    rw [← heq, norm_mul, norm_character, mul_one]
  rw [dist_eq_norm, hnorm, dist_eq_norm]
  exact norm_character_sub_one_le (x - y)

end Erdos3.CircleFourier

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

noncomputable def cyclicIntegerCharacter (M : ℕ) [NeZero M] (z : ℤ) : AddChar (ZMod M) ℂ where
  toFun r := character (ZMod.toAddCircle (r * (z : ZMod M)))
  map_zero_eq_one' := by simp only [zero_mul, map_zero, character_zero]
  map_add_eq_mul' r s := by
    simp only [add_mul, map_add, character_add]

noncomputable def gridResidueEquiv (M : ℕ) [NeZero M] : Fin M ≃ ZMod M where
  toFun k := (k.val : ZMod M)
  invFun r := ⟨r.val, ZMod.val_lt r⟩
  left_inv k := by
    apply Fin.ext
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt k.isLt]
  right_inv r := ZMod.natCast_zmod_val r

noncomputable def integerGridCharacter (M : ℕ) [NeZero M] (k : Fin M) (z : ℤ) : ℂ :=
  cyclicIntegerCharacter M z (gridResidueEquiv M k)

end Erdos3

end

section

namespace Erdos3

open CircleFourier

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

noncomputable def linearCircleHom (L : E →ₗ[ℝ] ℝ) : E →+ CircleFourier.Circle :=
  (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp L.toAddMonoidHom

theorem integral_subgroup_le_linearCircleHom_ker (Γ : AddSubgroup E) (L : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Γ, ∃ n : ℤ, L x = n) : Γ ≤ (linearCircleHom L).ker := by
  intro x hx
  change (L x : CircleFourier.Circle) = 0
  obtain ⟨n, hn⟩ := hint x hx
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  exact ⟨n, by simp [hn]⟩

noncomputable def quotientLinearPhase (Γ : AddSubgroup E) (L : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Γ, ∃ n : ℤ, L x = n) : (E ⧸ Γ) →+ CircleFourier.Circle :=
  QuotientAddGroup.lift Γ (linearCircleHom L) (integral_subgroup_le_linearCircleHom_ker Γ L hint)

noncomputable def quotientLinearCharacter (Γ : AddSubgroup E) (L : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Γ, ∃ n : ℤ, L x = n) (x : E ⧸ Γ) : ℂ :=
  character (quotientLinearPhase Γ L hint x)

theorem quotientLinearCharacter_mk (Γ : AddSubgroup E) (L : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Γ, ∃ n : ℤ, L x = n) (x : E) :
    quotientLinearCharacter Γ L hint (QuotientAddGroup.mk' Γ x) =
      character (L x : CircleFourier.Circle) := rfl

theorem quotientLinearCharacter_add (Γ : AddSubgroup E) (L : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Γ, ∃ n : ℤ, L x = n) (x y : E ⧸ Γ) :
    quotientLinearCharacter Γ L hint (x + y) =
      quotientLinearCharacter Γ L hint x * quotientLinearCharacter Γ L hint y := by
  simp only [quotientLinearCharacter, map_add, character_add]

theorem quotientLinearCharacter_norm (Γ : AddSubgroup E) (L : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Γ, ∃ n : ℤ, L x = n) (x : E ⧸ Γ) :
    ‖quotientLinearCharacter Γ L hint x‖ = 1 := norm_character _

theorem quotientLinearCharacter_zero (Γ : AddSubgroup E)
    (hint : ∀ x ∈ Γ, ∃ n : ℤ, (0 : E →ₗ[ℝ] ℝ) x = n) (x : E ⧸ Γ) :
    quotientLinearCharacter Γ 0 hint x = 1 := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective Γ x
  simp only [quotientLinearCharacter_mk, LinearMap.zero_apply, AddCircle.coe_zero, character_zero]

theorem quotientLinearCharacter_continuous [TopologicalSpace E]
    (Γ : AddSubgroup E) (L : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Γ, ∃ n : ℤ, L x = n) (hL : Continuous L) :
    Continuous (quotientLinearCharacter Γ L hint) := by
  apply (QuotientAddGroup.isQuotientMap_mk Γ).continuous_iff.mpr
  change Continuous (fun x : E => character (L x : CircleFourier.Circle))
  exact (continuous_subtype_val.comp AddCircle.continuous_toCircle).comp
    ((AddCircle.continuous_mk' (1 : ℝ)).comp hL)

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped BigOperators

theorem linear_site_sum {S W : Type*} [Fintype S] [DecidableEq S]
    [AddCommGroup W] [Module ℝ W] (M : (S → W) →ₗ[ℝ] ℝ) (v : S → W) :
    M v = ∑ s, M (Pi.single s (v s)) := by
  have hv : v = ∑ s, Pi.single s (v s) := by
    funext s
    simp [Pi.single_apply]
  exact (congrArg M hv).trans (map_sum M _ _)

theorem character_real_sum {S : Type*} (s : Finset S) (f : S → ℝ) :
    character ((∑ t ∈ s, f t : ℝ) : CircleFourier.Circle) =
      ∏ t ∈ s, character (f t : CircleFourier.Circle) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert t s ht ih =>
    simp only [Finset.sum_insert ht, AddCircle.coe_add, character_add, Finset.prod_insert ht, ih]

noncomputable def siteFunctionalCharacter {S W : Type*} [DecidableEq S]
    [AddCommGroup W] [Module ℝ W] (M : (S → W) →ₗ[ℝ] ℝ) (s : S) (w : W) : ℂ :=
  character (M (Pi.single s w) : CircleFourier.Circle)

theorem siteFunctionalCharacter_norm {S W : Type*} [DecidableEq S]
    [AddCommGroup W] [Module ℝ W] (M : (S → W) →ₗ[ℝ] ℝ) (s : S) (w : W) :
    ‖siteFunctionalCharacter M s w‖ = 1 := norm_character _

theorem character_linear_site_sum {S W : Type*} [Fintype S] [DecidableEq S]
    [AddCommGroup W] [Module ℝ W] (M : (S → W) →ₗ[ℝ] ℝ) (v : S → W) :
    character (M v : CircleFourier.Circle) = ∏ s, siteFunctionalCharacter M s (v s) := by
  rw [linear_site_sum M v]
  exact character_real_sum _ _

end Erdos3

end

section

namespace Erdos3

open Module
open scoped BigOperators NNReal

theorem abs_linearMap_le_basis_bound {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℝ V] (e : Basis ι ℝ V) (η : V →ₗ[ℝ] ℝ)
    (A : ℝ≥0) (hη : ∀ i, |η (e i)| ≤ A) (x : V) :
    |η x| ≤ (Fintype.card ι : ℝ) * A * ‖e.equivFun x‖ := by
  have hx : η x = ∑ i, e.repr x i * η (e i) := by
    conv_lhs => rw [← e.sum_repr x]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [hx]
  calc
    _ ≤ ∑ i, |e.repr x i * η (e i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, ‖e.equivFun x‖ * A := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      have he : |e.repr x i| ≤ ‖e.equivFun x‖ := by
        simpa only [Real.norm_eq_abs, Basis.equivFun_apply] using (norm_le_pi_norm (e.equivFun x) i)
      exact mul_le_mul he (hη i) (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem norm_character_real_sub_one_le (r : ℝ) :
    ‖CircleFourier.character (r : CircleFourier.Circle) - 1‖ ≤
      (CircleFourier.characterLipConstant : ℝ) * |r| := by
  apply (CircleFourier.norm_character_sub_one_le _).trans
  exact mul_le_mul_of_nonneg_left
    (by simpa only [Real.norm_eq_abs] using
      (show ‖(r : CircleFourier.Circle)‖ ≤ ‖r‖ from QuotientAddGroup.norm_mk_le_norm))
    (by positivity : 0 ≤ 2 * Real.pi)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

noncomputable def rectangularGridCharacter {J : Type*} [Fintype J]
    (M : ℕ) [NeZero M] (k : J → Fin M) (y : J → ℤ) : ℂ :=
  ∏ j, integerGridCharacter M (k j) (y j)

def integerGridResidue {J : Type*} (M : ℕ) (y : J → ℤ) : J → ZMod M := fun j => (y j : ZMod M)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicShortShiftSet
namespace OAI

section

namespace Erdos3

theorem exists_exponential_constant_fiber {α β : Type*}
    (S : Finset α) (hS : S.Nonempty) (f : α → β) (A : Set β) (hA : A.Finite)
    (hf : ∀ x ∈ S, f x ∈ A) {C : ℝ} (hcount : (A.ncard : ℝ) ≤ Real.exp C) :
    ∃ y ∈ A, ∃ T : Finset α, T ⊆ S ∧ T.Nonempty ∧ (∀ x ∈ T, f x = y) ∧
      Real.exp (-C) * S.card ≤ (T.card : ℝ) := by
  classical
  have hf' : ∀ x ∈ S, f x ∈ hA.toFinset := fun x hx => hA.mem_toFinset.mpr (hf x hx)
  have hAne : hA.toFinset.Nonempty := by
    obtain ⟨x, hx⟩ := hS
    exact ⟨f x, hf' x hx⟩
  have hn : hA.toFinset.card • (Real.exp (-C) * S.card) ≤ (S.card : ℝ) := by
    rw [nsmul_eq_mul, ← Set.ncard_eq_toFinset_card A hA]
    calc
      (A.ncard : ℝ) * (Real.exp (-C) * S.card) ≤
          Real.exp C * (Real.exp (-C) * S.card) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
      _ = (S.card : ℝ) := by rw [← mul_assoc, ← Real.exp_add]; simp
  obtain ⟨y, hy, hlarge⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := S) (t := hA.toFinset) (f := f) hf' hAne hn
  have hpos : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have htpos : 0 < (S.filter (fun x => f x = y)).card := by
    exact_mod_cast (mul_pos (Real.exp_pos (-C)) hpos).trans_le hlarge
  exact ⟨y, hA.mem_toFinset.mp hy, S.filter (fun x => f x = y), Finset.filter_subset _ _,
    Finset.card_pos.mp htpos, fun x hx => (Finset.mem_filter.mp hx).2, hlarge⟩

end Erdos3

end

section

namespace Erdos3

def CyclicShortShiftSet {N : ℕ} (H : Finset (ZMod N)) : Prop :=
  ∀ x ∈ H, ∀ y ∈ H, 2 * |(x.val : ℤ) - y.val| < (N : ℤ)

theorem exists_cyclicShortShiftSet {N : ℕ} [NeZero N]
    (H : Finset (ZMod N)) (hH : H.Nonempty) :
    ∃ S : Finset (ZMod N), S ⊆ H ∧ S.Nonempty ∧
      (H.card : ℝ) / 2 ≤ (S.card : ℝ) ∧ CyclicShortShiftSet S := by
  classical
  let label (x : ZMod N) : Bool := decide (2 * x.val < N)
  have hcount : (Finset.univ : Finset Bool).card • ((H.card : ℝ) / 2) ≤ (H.card : ℝ) := by
    norm_num
    linarith
  obtain ⟨b, _, hb⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := H) (t := (Finset.univ : Finset Bool)) (f := label)
    (fun _ _ => Finset.mem_univ _) Finset.univ_nonempty hcount
  let S := H.filter (fun x => label x = b)
  have hpos : (0 : ℝ) < H.card := by exact_mod_cast hH.card_pos
  have hS : S.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (half_pos hpos).trans_le hb
  refine ⟨S, Finset.filter_subset _ _, hS, hb, ?_⟩
  intro x hx y hy
  have hx' := (Finset.mem_filter.mp hx).2
  have hy' := (Finset.mem_filter.mp hy).2
  have hxN := x.val_lt
  have hyN := y.val_lt
  cases b <;> simp only [label, decide_eq_false_iff_not, decide_eq_true_eq] at hx' hy'
  · by_cases hxy : (y.val : ℤ) ≤ x.val
    · rw [abs_of_nonneg (by omega)]
      omega
    · rw [abs_of_nonpos (by omega)]
      omega
  · by_cases hxy : (y.val : ℤ) ≤ x.val
    · rw [abs_of_nonneg (by omega)]
      omega
    · rw [abs_of_nonpos (by omega)]
      omega

theorem CyclicShortShiftSet.integer_relation {N : ℕ} [NeZero N]
    {H : Finset (ZMod N)} (hH : CyclicShortShiftSet H)
    {x₁ x₂ x₃ x₄ : ZMod N} (h₁ : x₁ ∈ H) (h₂ : x₂ ∈ H)
    (h₃ : x₃ ∈ H) (h₄ : x₄ ∈ H) (hrel : x₁ - x₂ = x₃ - x₄) :
    (x₁.val : ℤ) - x₂.val = (x₃.val : ℤ) - x₄.val := by
  let d₁ : ℤ := (x₁.val : ℤ) - x₂.val
  let d₂ : ℤ := (x₃.val : ℤ) - x₄.val
  have hd₁ : 2 * |d₁| < (N : ℤ) := hH x₁ h₁ x₂ h₂
  have hd₂ : 2 * |d₂| < (N : ℤ) := hH x₃ h₃ x₄ h₄
  have hcast : (d₁ : ZMod N) = (d₂ : ZMod N) := by
    simpa only [d₁, d₂, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val] using hrel
  have hdvd : (N : ℤ) ∣ d₂ - d₁ :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub d₁ d₂ N).mp hcast
  have habs : |d₂ - d₁| < (N : ℤ) :=
    (abs_sub d₂ d₁).trans_lt (by omega)
  have hsmall : (d₂ - d₁).natAbs < (N : ℤ).natAbs := by
    apply Int.ofNat_lt.mp
    simpa only [Int.natCast_natAbs, abs_of_nonneg (Int.natCast_nonneg N)] using habs
  have hzero := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd hsmall
  change d₁ = d₂
  omega

theorem CyclicShortShiftSet.quadruple_relation {N : ℕ} [NeZero N]
    {H : Finset (ZMod N)} (hH : CyclicShortShiftSet H) (a h k : ZMod N)
    (h₁ : h ∈ H) (h₂ : h - a ∈ H) (h₃ : k ∈ H) (h₄ : k - a ∈ H) :
    -(h.val : ℤ) + (h - a).val + k.val - (k - a).val = 0 := by
  have heq := hH.integer_relation h₁ h₂ h₃ h₄ (by abel : h - (h - a) = k - (k - a))
  omega

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxDetectionExponents
namespace OAI

section

namespace Erdos3

def boxModeBudget (a : ℕ) (p : ℝ) : ℝ := p + (p + 1 + a) ^ a + 2

def boxInductionInputBudget (a b : ℕ) (p : ℝ) : ℝ :=
  (p + 1 + b) ^ b + 2 * boxModeBudget a p + 2 * p + 3

def boxRetainedBudget (a : ℕ) (p : ℝ) : ℝ := 2 * boxModeBudget a p + 2 * p + 6

def boxDetectionStepBudget (s a b c : ℕ) (p : ℝ) : ℝ :=
  ((s + 2) ^ (s + 2) : ℕ) * p + (s + 1 : ℕ) * (boxRetainedBudget a p + p) +
    (2 ^ (s + 1) : ℕ) * (boxInductionInputBudget a b p + c) ^ c + boxRetainedBudget a p

theorem boxModeBudget_nonneg (a : ℕ) {p : ℝ} (hp : 0 ≤ p) : 0 ≤ boxModeBudget a p := by
  unfold boxModeBudget
  positivity

theorem boxInductionInputBudget_bounds (a b : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (p + 1 + b) ^ b ≤ boxInductionInputBudget a b p ∧
    2 * boxModeBudget a p + 1 ≤ boxInductionInputBudget a b p ∧
    p ≤ boxInductionInputBudget a b p := by
  have hmode := boxModeBudget_nonneg a hp
  have hpow : 0 ≤ (p + 1 + b) ^ b := by positivity
  unfold boxInductionInputBudget
  constructor
  · linarith
  constructor <;> linarith

theorem boxDetectionStepBudget_nonneg (s a b c : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ boxDetectionStepBudget s a b c p := by
  unfold boxDetectionStepBudget boxRetainedBudget boxInductionInputBudget boxModeBudget
  positivity

theorem exists_boxDetectionStepBudget_bound (s a b c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → boxDetectionStepBudget s a b c p ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + 1 + Polynomial.C a) ^ a + 2
  let K := (X + 1 + Polynomial.C b) ^ b + 2 * R + 2 * X + 3
  let V := 2 * R + 2 * X + 6
  let P := Polynomial.C ((s + 2) ^ (s + 2)) * X + Polynomial.C (s + 1) * (V + X) +
    Polynomial.C (2 ^ (s + 1)) * (K + Polynomial.C c) ^ c + V
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, V, K, R, X, Polynomial.eval₂_pow, boxDetectionStepBudget,
    boxRetainedBudget, boxInductionInputBudget, boxModeBudget] using hbound p hp

end Erdos3

end

section

namespace Erdos3

theorem exp_sub_one_le_half_exp (x : ℝ) : Real.exp (x - 1) ≤ Real.exp x / 2 := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  calc
    _ ≤ Real.exp (x - 1) * Real.exp 1 := mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem two_pow_le_exp_of_le (d : ℕ) {p : ℝ} (hd : (d : ℝ) ≤ p) :
    (2 : ℝ) ^ d ≤ Real.exp p := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ (Real.exp 1) ^ d := pow_le_pow_left₀ (by norm_num) htwo d
    _ = Real.exp d := by rw [← Real.exp_nat_mul, mul_one]
    _ ≤ _ := Real.exp_le_exp.mpr hd

theorem exp_neg_nat_mul_le_inverse_pow (N d : ℕ) (hN : 0 < N) {p : ℝ} (hd : (d : ℝ) ≤ p) :
    Real.exp (-(N : ℝ) * p) ≤ ((1 : ℝ) / N) ^ d := by
  have hbase : (N : ℝ) ≤ Real.exp N := by linarith [Real.add_one_le_exp (N : ℝ)]
  have hpow : (N : ℝ) ^ d ≤ Real.exp ((N : ℝ) * p) := by
    calc
      _ ≤ (Real.exp N) ^ d := pow_le_pow_left₀ (Nat.cast_nonneg N) hbase d
      _ = Real.exp ((d : ℝ) * N) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [show (0 : ℝ) ≤ N from Nat.cast_nonneg N])
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hi := one_div_le_one_div_of_le (pow_pos hn d) hpow
  simpa only [div_pow, one_pow, neg_mul, Real.exp_neg, one_div, inv_pow] using hi

theorem retained_exponential_weight (d : ℕ) {p r : ℝ} (hd : (d : ℝ) ≤ p) :
    let L := 2 * r + 2 * p + 6
    Real.exp (-L) ≤ Real.exp (-r) ^ 2 / (2 * Real.exp (p + 1) ^ 2) -
      (2 : ℝ) ^ d * Real.exp (-(L + p)) := by
  let L := 2 * r + 2 * p + 6
  have hloss : (2 : ℝ) ^ d * Real.exp (-(L + p)) ≤ Real.exp (-L) := by
    calc
      _ ≤ Real.exp p * Real.exp (-(L + p)) :=
        mul_le_mul_of_nonneg_right (two_pow_le_exp_of_le d hd) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have he : Real.exp (-r) ^ 2 / (2 * Real.exp (p + 1) ^ 2) =
      Real.exp 4 / 2 * Real.exp (-L) := by
    calc
      _ = (Real.exp (-r) ^ 2 / Real.exp (p + 1) ^ 2) / 2 := by ring
      _ = Real.exp (2 * (-r) - 2 * (p + 1)) / 2 := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_sub]
        norm_num
      _ = (Real.exp 4 * Real.exp (-L)) / 2 := by
        rw [← Real.exp_add]
        congr 2
        dsimp [L]
        ring
      _ = _ := by ring
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  change Real.exp (-L) ≤ _
  rw [he]
  nlinarith [Real.exp_pos (-L)]

theorem exp_neg_le_of_pow {x P : ℝ} {n : ℕ} (hx : 0 ≤ x) (hP : 0 ≤ P) (hn : n ≠ 0)
    (h : Real.exp (-P) ≤ x ^ n) : Real.exp (-P) ≤ x := by
  have ht : Real.exp (-P) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hp : ∀ k : ℕ, Real.exp (-P) ^ (k + 1) ≤ Real.exp (-P) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      exact (mul_le_mul ih ht (Real.exp_nonneg _) (Real.exp_nonneg _)).trans_eq (mul_one _)
  cases n with
  | zero => exact False.elim (hn rfl)
  | succ k => exact le_of_pow_le_pow_left₀ (Nat.succ_ne_zero k) hx ((hp k).trans h)

theorem box_detection_exponential_product (s a b c d : ℕ) {p : ℝ} (hd : (d : ℝ) ≤ p) :
    Real.exp (-boxDetectionStepBudget s a b c p) ≤
      ((1 : ℝ) / ((s : ℝ) + 2) ^ (s + 2)) ^ d *
        Real.exp (-(boxRetainedBudget a p + p)) ^ (s + 1) *
        Real.exp (-((boxInductionInputBudget a b p + c) ^ c)) ^ (2 ^ (s + 1)) *
        Real.exp (-boxRetainedBudget a p) := by
  have hc : Real.exp (-(((s + 2) ^ (s + 2) : ℕ) : ℝ) * p) ≤
      ((1 : ℝ) / ((s : ℝ) + 2) ^ (s + 2)) ^ d := by
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat] using
      exp_neg_nat_mul_le_inverse_pow ((s + 2) ^ (s + 2)) d (by positivity) hd
  calc
    _ = Real.exp (-(((s + 2) ^ (s + 2) : ℕ) : ℝ) * p) *
        Real.exp (-(boxRetainedBudget a p + p)) ^ (s + 1) *
        Real.exp (-((boxInductionInputBudget a b p + c) ^ c)) ^ (2 ^ (s + 1)) *
        Real.exp (-boxRetainedBudget a p) := by
      simp only [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      unfold boxDetectionStepBudget
      ring
    _ ≤ _ := by gcongr

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FixedPartnerPower
namespace OAI

section

namespace Erdos3

theorem exists_large_fixed_choices {G K P : Type*} [Fintype K] [Fintype P]
    (H : Finset G) (hH : H.Nonempty) (rel : G → K → P → Prop)
    (hchoice : ∀ h ∈ H, ∀ k, ∃ p, rel h k p) {R : ℝ}
    (hcount : (Fintype.card P : ℝ) ≤ Real.exp R) :
    ∃ (q : K → P) (S : Finset G), S ⊆ H ∧ S.Nonempty ∧
      Real.exp (-R * Fintype.card K) * H.card ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ k, rel h k (q k) := by
  classical
  choose choices hchoices using hchoice
  obtain ⟨h0, hh0⟩ := hH
  have hH : H.Nonempty := ⟨h0, hh0⟩
  let code : G → (K → P) := fun h => if hh : h ∈ H then choices h hh else choices h0 hh0
  have hcode (h : G) (hh : h ∈ H) (k : K) : rel h k (code h k) := by
    simpa [code, hh] using hchoices h hh k
  have hcodeCount : (((Set.univ : Set (K → P)).ncard : ℕ) : ℝ) ≤
      Real.exp (R * Fintype.card K) := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Nat.cast_pow]
    calc
      _ ≤ (Real.exp R) ^ Fintype.card K := pow_le_pow_left₀ (Nat.cast_nonneg _) hcount _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  obtain ⟨q, _, S, hsub, hSn, hconst, hsize⟩ := exists_exponential_constant_fiber
    H hH code Set.univ Set.finite_univ (fun _ _ => Set.mem_univ _) hcodeCount
  refine ⟨q, S, hsub, hSn, ?_, ?_⟩
  · simpa only [neg_mul] using hsize
  · intro h hh k
    rw [← hconst h hh]
    exact hcode h (hsub hh) k

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

noncomputable def functionCorrelationLinearMap (w : Ω → ℂ) : (Ω → ℂ) →ₗ[ℂ] ℂ where
  toFun v := 𝔼 x, v x * w x
  map_add' v u := by simp [Pi.add_apply, add_mul, Finset.expect_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply,
      Finset.mul_expect]

noncomputable def functionCorrelationSeminorm (w : Ω → ℂ) : Seminorm ℂ (Ω → ℂ) :=
  (normSeminorm ℂ ℂ).comp (functionCorrelationLinearMap w)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def weightedModelError {G I : Type*} [Fintype I]
    (c : I → ℂ) (ea : G → ℝ) (eb : I → G → ℝ) (h : G) : ℝ :=
  ea h + ∑ i, ‖c i‖ * eb i h

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

variable {G ι : Type*} [AddCommGroup G] [Fintype G]

noncomputable def shiftTestSeminormAt (B : G → ℂ) (T : ι → G → ℂ) (h : G) :
    Seminorm ℂ (G → ℂ) :=
  ⨆ i, functionCorrelationSeminorm (fun x => B (x + h) * T i x)

noncomputable def shiftTestingSeminorm (B : G → ℂ) (T : ι → G → ℂ) :
    Seminorm ℂ (G → ℂ) :=
  Seminorm.of (fun v => 𝔼 h, shiftTestSeminormAt B T h v)
    (fun u v => by
      rw [← Finset.expect_add_distrib]
      exact Finset.expect_le_expect (fun h _ => map_add_le_add _ _ _))
    (fun a v => by simp only [map_smul_eq_mul, Finset.mul_expect])

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

variable {G ι : Type*} [AddCommGroup G]

def translatedTestFamily (T : ι → G → ℂ) (p : G × ι) (x : G) : ℂ := T p.2 (x + p.1)

variable [Fintype G]

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

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BalancedDualBounds
namespace OAI

section

namespace Erdos3

theorem exists_complex_unit_phase (z : ℂ) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ a * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · subst z
    exact ⟨1, by simp, by simp⟩
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  refine ⟨star z / (‖z‖ : ℂ), ?_, ?_⟩
  · simp [hn]
  · calc
      _ = (star z * z) / (‖z‖ : ℂ) := by ring
      _ = ((‖z‖ ^ 2 : ℝ) : ℂ) / (‖z‖ : ℂ) := by
        rw [mul_comm (star z) z]
        change z * (starRingEnd ℂ) z / (‖z‖ : ℂ) = _
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      _ = _ := by
        rw [Complex.ofReal_pow]
        field_simp

theorem norm_lt_of_re_lt_on_balanced {E : Type*} [AddCommGroup E] [Module ℂ E]
    (f : E →ₗ[ℂ] ℂ) {S : Set E} (hS : Balanced ℂ S) {c : ℝ}
    (hf : ∀ x ∈ S, (f x).re < c) : ∀ x ∈ S, ‖f x‖ < c := by
  intro x hx
  obtain ⟨a, ha, hphase⟩ := exists_complex_unit_phase (f x)
  have h := hf (a • x) (hS.smul_mem ha.le hx)
  simpa only [map_smul, smul_eq_mul, hphase, Complex.ofReal_re] using h

theorem seminorm_dual_bound_of_ball {E : Type*} [AddCommGroup E] [Module ℂ E]
    (X : Seminorm ℂ E) (f : E →ₗ[ℂ] ℂ) {tau : ℝ} (htau : 0 < tau)
    (hball : ∀ v, X v ≤ tau → ‖f v‖ < 1) : ∀ v, tau * ‖f v‖ ≤ X v := by
  intro v
  by_contra h
  have hv : X v < tau * ‖f v‖ := lt_of_not_ge h
  have hnorm : 0 < ‖f v‖ := by nlinarith [apply_nonneg X v, norm_nonneg (f v)]
  let a : ℂ := (‖f v‖⁻¹ : ℝ)
  have ha : ‖a‖ = ‖f v‖⁻¹ := by
    simp [a]
  have hX : X (a • v) ≤ tau := by
    rw [map_smul_eq_mul, ha, inv_mul_eq_div]
    exact ((div_lt_iff₀ hnorm).mpr (by simpa only [mul_comm] using hv)).le
  have hbad := hball (a • v) hX
  have hbad' : (1 : ℝ) < 1 := by
    simpa only [map_smul, norm_smul, ha, inv_mul_cancel₀ hnorm.ne'] using hbad
  exact (lt_irrefl 1) hbad'

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

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem shift_phase_average (v B : G → ℂ) (L : G → G → ℂ) (a : G → ℂ)
    (ha : ∀ h, a h * (𝔼 x, v x * (B (x + h) * L h x)) =
      (‖𝔼 x, v x * (B (x + h) * L h x)‖ : ℂ)) :
    (𝔼 y, B y * (𝔼 h, a h * v (y - h) * L h (y - h))) =
      ((𝔼 h, ‖𝔼 x, v x * (B (x + h) * L h x)‖) : ℝ) := by
  have hmove (h : G) :
      a h * (𝔼 x, v x * (B (x + h) * L h x)) =
        𝔼 y, B y * (a h * v (y - h) * L h (y - h)) := by
    rw [Finset.mul_expect]
    apply Fintype.expect_equiv (Equiv.addRight h)
    intro x
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    ring
  calc
    _ = 𝔼 h, 𝔼 y, B y * (a h * v (y - h) * L h (y - h)) := by
      simp_rw [Finset.mul_expect]
      rw [Finset.expect_comm]
    _ = 𝔼 h, a h * (𝔼 x, v x * (B (x + h) * L h x)) := by simp_rw [← hmove]
    _ = _ := by simp_rw [ha]; simp [Fintype.expect_eq_sum_div_card]

theorem shift_phase_cross_norm (v : G → ℂ) (L : G → G → ℂ) (a : G → ℂ)
    (ha : ∀ h, ‖a h‖ = 1) (h k : G) :
    ‖𝔼 y, (a h * v (y - h) * L h (y - h)) *
      star (a k * v (y - k) * L k (y - k))‖ =
    ‖𝔼 x, v x * star (v (x + h - k)) * L h x * star (L k (x + h - k))‖ := by
  have hid : (a h * star (a k)) *
      (𝔼 x, v x * star (v (x + h - k)) * L h x * star (L k (x + h - k))) =
      𝔼 y, (a h * v (y - h) * L h (y - h)) *
        star (a k * v (y - k) * L k (y - k)) := by
    rw [Finset.mul_expect]
    apply Fintype.expect_equiv (Equiv.addRight h)
    intro x
    simp only [Equiv.coe_addRight, add_sub_cancel_right, star_mul]
    ring
  rw [← hid, norm_mul, norm_mul, norm_star, ha, ha, one_mul, one_mul]

theorem shifted_test_cauchy_schwarz (v B : G → ℂ) (L : G → G → ℂ)
    {M : ℝ} (hB : ∀ x, ‖B x‖ ≤ M) :
    (𝔼 h, ‖𝔼 x, v x * (B (x + h) * L h x)‖) ^ 2 ≤
      M ^ 2 * (𝔼 h, 𝔼 k,
        ‖𝔼 x, v x * star (v (x + h - k)) * L h x * star (L k (x + h - k))‖) := by
  have hex (h : G) := exists_complex_unit_phase (𝔼 x, v x * (B (x + h) * L h x))
  choose a ha hphase using hex
  have hcs := finite_family_cauchy_schwarz B
    (fun h y => a h * v (y - h) * L h (y - h)) hB
  rw [shift_phase_average v B L a hphase, Complex.norm_real,
    Real.norm_of_nonneg (Finset.expect_nonneg (fun h _ => norm_nonneg _))] at hcs
  simpa only [shift_phase_cross_norm v L a ha] using hcs

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finite_absolute_cauchy_schwarz {H Ω : Type*} [Fintype H] [Fintype Ω]
    [Nonempty Ω] (B : Ω → ℂ) (v : H → Ω → ℂ) {M : ℝ} (hB : ∀ x, ‖B x‖ ≤ M) :
    (𝔼 h, ‖𝔼 x, B x * v h x‖) ^ 2 ≤
      M ^ 2 * (𝔼 h, 𝔼 k, ‖𝔼 x, v h x * star (v k x)‖) := by
  choose a ha hphase using fun h => exists_complex_unit_phase (𝔼 x, B x * v h x)
  have havg : (𝔼 x, B x * (𝔼 h, a h * v h x)) =
      ((𝔼 h, ‖𝔼 x, B x * v h x‖) : ℝ) := by
    calc
      _ = 𝔼 h, a h * (𝔼 x, B x * v h x) := by
        simp_rw [Finset.mul_expect]
        rw [Finset.expect_comm]
        apply Finset.expect_congr rfl
        intro h _
        apply Finset.expect_congr rfl
        intro x _
        ring
      _ = _ := by simp_rw [hphase]; simp [Fintype.expect_eq_sum_div_card]
  have hcross (h k : H) :
      ‖𝔼 x, (a h * v h x) * star (a k * v k x)‖ =
        ‖𝔼 x, v h x * star (v k x)‖ := by
    have hid : (𝔼 x, (a h * v h x) * star (a k * v k x)) =
        (a h * star (a k)) * (𝔼 x, v h x * star (v k x)) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      simp only [star_mul]
      ring
    rw [hid, norm_mul, norm_mul, norm_star, ha, ha, one_mul, one_mul]
  have hcs := finite_family_cauchy_schwarz B (fun h x => a h * v h x) hB
  rw [havg, Complex.norm_real,
    Real.norm_of_nonneg (Finset.expect_nonneg (fun h _ => norm_nonneg _))] at hcs
  simpa only [hcross] using hcs

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G ι : Type*} [AddCommGroup G] [Fintype G] [Nonempty ι]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G ι : Type*} [AddCommGroup G] [Fintype G]

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

section

namespace Erdos3

open scoped BigOperators

theorem exists_large_anchor_branch {I G : Type*} [Fintype I] [Fintype G] [Nonempty G]
    (anchor : I → G) (branch : I → Bool) {α : ℝ} (hα : 0 < α)
    (hsize : α * (Fintype.card G : ℝ) ^ 3 ≤ Fintype.card I) :
    ∃ (k : G) (b : Bool) (T : Finset I), T.Nonempty ∧
      α / 2 * (Fintype.card G : ℝ) ^ 2 ≤ (T.card : ℝ) ∧
      ∀ t ∈ T, anchor t = k ∧ branch t = b := by
  classical
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hb : Fintype.card (G × Bool) • (α / 2 * (Fintype.card G : ℝ) ^ 2) ≤
      (Fintype.card I : ℝ) := by
    calc
      _ = α * (Fintype.card G : ℝ) ^ 3 := by
        simp only [nsmul_eq_mul, Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
        ring
      _ ≤ _ := hsize
  obtain ⟨⟨k, b⟩, hkb⟩ := Fintype.exists_le_card_fiber_of_nsmul_le_card
    (fun i => (anchor i, branch i)) hb
  let T := Finset.univ.filter (fun i => (anchor i, branch i) = (k, b))
  have hTsize : α / 2 * (Fintype.card G : ℝ) ^ 2 ≤ (T.card : ℝ) := hkb
  have hTpos : (0 : ℝ) < T.card := lt_of_lt_of_le (by positivity) hTsize
  refine ⟨k, b, T, Finset.card_pos.mp (by exact_mod_cast hTpos), hTsize, ?_⟩
  intro t ht
  exact Prod.mk.inj (Finset.mem_filter.mp ht).2

theorem exists_dense_first_fibers {I G : Type*} [Fintype G] [Nonempty G] [DecidableEq G]
    (T : Finset I) (a h : I → G) (hinj : Set.InjOn (fun i => (a i, h i)) (T : Set I))
    {ρ : ℝ} (hρ : 0 < ρ) (hsize : ρ * (Fintype.card G : ℝ) ^ 2 ≤ T.card) :
    ∃ A : Finset G, A.Nonempty ∧ ρ / 2 * (Fintype.card G : ℝ) ≤ (A.card : ℝ) ∧
      ∀ x ∈ A, ρ / 2 * (Fintype.card G : ℝ) ≤ ((T.filter (fun i => a i = x)).card : ℝ) := by
  classical
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  let F (x : G) := T.filter (fun i => a i = x)
  have hcard (x : G) : (F x).card ≤ Fintype.card G := by
    have hmap : Function.Injective (fun t : F x => h t.val) := by
      intro u v huv
      apply Subtype.ext
      apply hinj (Finset.mem_filter.mp u.property).1 (Finset.mem_filter.mp v.property).1
      exact Prod.ext ((Finset.mem_filter.mp u.property).2.trans (Finset.mem_filter.mp v.property).2.symm) huv
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective _ hmap
  have hsum : ∑ x : G, (F x).card = T.card := by
    symm
    exact Finset.card_eq_sum_card_fiberwise (f := a) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  let density (x : G) := ((F x).card : ℝ) / Fintype.card G
  have hmean : ρ ≤ 𝔼 x, density x := by
    rw [Fintype.expect_eq_sum_div_card]
    simp only [density, ← Finset.sum_div, ← Nat.cast_sum, hsum]
    apply (le_div_iff₀ hN).mpr
    apply (le_div_iff₀ hN).mpr
    nlinarith only [hsize]
  have hunit (x : G) : density x ≤ 1 := by
    apply (div_le_iff₀ hN).mpr
    simpa only [one_mul] using (Nat.cast_le.mpr (hcard x) : ((F x).card : ℝ) ≤ Fintype.card G)
  obtain ⟨A, hAsize, hA⟩ := exists_dense_level_set density hρ.le hunit hmean
  have hApos : (0 : ℝ) < A.card := lt_of_lt_of_le (by positivity) hAsize
  refine ⟨A, Finset.card_pos.mp (by exact_mod_cast hApos), hAsize, ?_⟩
  intro x hx
  exact (le_div_iff₀ hN).mp (hA x hx)

theorem exists_dense_anchored_fibers {I G : Type*} [Fintype I] [Fintype G]
    [Nonempty G] [DecidableEq G] (a h k : I → G) (branch : I → Bool)
    (hinj : Function.Injective (fun i => (a i, h i, k i)))
    {α : ℝ} (hα : 0 < α) (hsize : α * (Fintype.card G : ℝ) ^ 3 ≤ Fintype.card I) :
    ∃ (anchor : G) (b : Bool) (T : Finset I) (A : Finset G), A.Nonempty ∧
      α / 4 * (Fintype.card G : ℝ) ≤ (A.card : ℝ) ∧
      (∀ t ∈ T, k t = anchor ∧ branch t = b) ∧
      Set.InjOn (fun i => (a i, h i)) (T : Set I) ∧
      ∀ x ∈ A, α / 4 * (Fintype.card G : ℝ) ≤ ((T.filter (fun i => a i = x)).card : ℝ) := by
  classical
  obtain ⟨anchor, b, T, _, hTsize, hT⟩ := exists_large_anchor_branch k branch hα hsize
  have hpair : Set.InjOn (fun i => (a i, h i)) (T : Set I) := by
    intro u hu v hv huv
    have hau : a u = a v := congrArg (fun z : G × G => z.1) huv
    have hhu : h u = h v := congrArg (fun z : G × G => z.2) huv
    apply hinj
    exact Prod.ext hau (Prod.ext hhu ((hT u hu).1.trans (hT v hv).1.symm))
  obtain ⟨A, hA, hAsize, hAfiber⟩ := exists_dense_first_fibers T a h hpair (by positivity) hTsize
  refine ⟨anchor, b, T, A, hA, ?_, hT, hpair, ?_⟩
  · convert hAsize using 1; ring
  · intro x hx
    convert hAfiber x hx using 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {H Ω : Type*} [Fintype H] [Fintype Ω]

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

def partnerAnchorWeight {G : Type*} (U V Q : G → ℂ) (x : G) : ℂ :=
  U x * star (V x) * (Q x * star (Q x))

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

theorem exists_dense_correlation_pairs {I X : Type*} [Fintype I] [Nonempty I]
    [Fintype X] [Nonempty X] (B : X → ℂ) (v : I → X → ℂ) {δ : ℝ}
    (hδ : 0 < δ) (hB : ∀ x, ‖B x‖ ≤ 1) (hv : ∀ i x, ‖v i x‖ ≤ 1)
    (hcorr : ∀ i, δ ≤ ‖𝔼 x, B x * v i x‖) :
    ∃ P : Finset (I × I), P.Nonempty ∧
      δ ^ 2 / 2 * (Fintype.card I : ℝ) ^ 2 ≤ (P.card : ℝ) ∧
      ∀ t ∈ P, δ ^ 2 / 2 ≤ ‖𝔼 x, v t.1 x * star (v t.2 x)‖ := by
  have hmean : δ ≤ 𝔼 i, ‖𝔼 x, B x * v i x‖ := by
    simpa only [Fintype.expect_const] using
      Finset.expect_le_expect (s := Finset.univ) (fun i _ => hcorr i)
  have hcs := finite_absolute_cauchy_schwarz B v hB
  have hcross : δ ^ 2 ≤ 𝔼 t : I × I, ‖𝔼 x, v t.1 x * star (v t.2 x)‖ := by
    have h := (pow_le_pow_left₀ hδ.le hmean 2).trans hcs
    simpa only [one_pow, one_mul, ← Finset.univ_product_univ, Finset.expect_product] using h
  have hunit (t : I × I) : ‖𝔼 x, v t.1 x * star (v t.2 x)‖ ≤ 1 := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply (Finset.expect_le_expect _).trans_eq (Fintype.expect_const _)
    intro x _
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hv t.1 x)).trans (hv t.2 x)
  obtain ⟨P, hsize, hP⟩ := exists_dense_level_set
    (fun t : I × I => ‖𝔼 x, v t.1 x * star (v t.2 x)‖) (sq_nonneg δ) hunit hcross
  have hsize' : δ ^ 2 / 2 * (Fintype.card I : ℝ) ^ 2 ≤ (P.card : ℝ) := by
    simpa only [Fintype.card_prod, Nat.cast_mul, pow_two] using hsize
  have hcard : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hpos : 0 < (P.card : ℝ) := lt_of_lt_of_le (by positivity) hsize'
  exact ⟨P, Finset.card_pos.mp (by exact_mod_cast hpos), hsize', hP⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeProduct
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

noncomputable def mixedGowersMoment : (j : ℕ) → ((Fin j → Bool) → H → ℂ) → ℂ
  | 0, F => 𝔼 x, F default x
  | j + 1, F => 𝔼 h, mixedGowersMoment j
      (fun ω ↦ crossDerivative (F (Fin.cons false ω)) (F (Fin.cons true ω)) h)

theorem mixedGowersMoment_const (j : ℕ) (f : H → ℂ) :
    mixedGowersMoment j (fun _ ↦ f) = gowersMoment j f := by
  induction j generalizing f with
  | zero => rfl
  | succ j ih => simp only [mixedGowersMoment, crossDerivative_self, ih, gowersMoment]

theorem mixedGowersMoment_one (F : (Fin 1 → Bool) → H → ℂ) :
    mixedGowersMoment 1 F =
      (𝔼 x, F (Fin.cons false default) x) * star (𝔼 x, F (Fin.cons true default) x) :=
  expect_crossDerivative _ _

theorem norm_mixedGowersMoment_le (j : ℕ) (F : (Fin (j + 1) → Bool) → H → ℂ) :
    ‖mixedGowersMoment (j + 1) F‖ ≤ ∏ ω, gowersNorm (j + 1) (F ω) := by
  induction j with
  | zero =>
    rw [mixedGowersMoment_one, norm_mul, norm_star, prod_bool_tuple_succ]
    rw [Fintype.prod_subsingleton _ (default : Fin 0 → Bool),
      Fintype.prod_subsingleton _ (default : Fin 0 → Bool),
      gowersNorm_one, gowersNorm_one]
  | succ j ih =>
    let D (ω : Fin (j + 1) → Bool) (h : H) :=
      crossDerivative (F (Fin.cons false ω)) (F (Fin.cons true ω)) h
    have hnorm : ‖mixedGowersMoment (j + 2) F‖ ≤
        𝔼 h, ∏ ω, gowersNorm (j + 1) (D ω h) := by
      change ‖𝔼 h, mixedGowersMoment (j + 1) (fun ω ↦ D ω h)‖ ≤ _
      exact (RCLike.norm_expect_le (K := ℂ)).trans
        (Finset.expect_le_expect (fun h _ ↦ ih (fun ω ↦ D ω h)))
    have hholder := expect_prod_boolean_pow_le (j + 1)
      (fun ω h ↦ gowersNorm (j + 1) (D ω h)) (fun ω h ↦ gowersNorm_nonneg j _)
    have hcross : (∏ ω, 𝔼 h, gowersNorm (j + 1) (D ω h) ^ (2 ^ (j + 1))) ≤
        ∏ ω : Fin (j + 1) → Bool,
          (gowersNorm (j + 2) (F (Fin.cons false ω)) *
            gowersNorm (j + 2) (F (Fin.cons true ω))) ^ (2 ^ (j + 1)) := by
      apply Finset.prod_le_prod
      · intro ω hω
        exact Finset.expect_nonneg (fun h _ ↦ pow_nonneg (gowersNorm_nonneg j _) _)
      · intro ω hω
        exact expect_cross_gowersNorm_pow_le j _ _
    have hfactor : (∏ ω : Fin (j + 1) → Bool,
          (gowersNorm (j + 2) (F (Fin.cons false ω)) *
            gowersNorm (j + 2) (F (Fin.cons true ω))) ^ (2 ^ (j + 1))) =
        (∏ ω, gowersNorm (j + 2) (F ω)) ^ (2 ^ (j + 1)) := by
      rw [Finset.prod_pow, Finset.prod_mul_distrib,
        ← prod_bool_tuple_succ (fun ω ↦ gowersNorm (j + 2) (F ω))]
    apply le_of_pow_le_pow_left₀ (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
      (Finset.prod_nonneg (fun ω _ ↦ gowersNorm_nonneg (j + 1) _))
    exact (pow_le_pow_left₀ (norm_nonneg _) hnorm _).trans
      (hholder.trans (hcross.trans_eq hfactor))

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

def booleanWeight {j : ℕ} (ω : Fin j → Bool) : ℕ :=
  ∑ i, if ω i then 1 else 0

@[simp] theorem booleanWeight_cons_false {j : ℕ} (ω : Fin j → Bool) :
    booleanWeight (Fin.cons false ω) = booleanWeight ω := by
  unfold booleanWeight
  rw [Fin.sum_univ_succ]
  simp

@[simp] theorem booleanWeight_cons_true {j : ℕ} (ω : Fin j → Bool) :
    booleanWeight (Fin.cons true ω) = booleanWeight ω + 1 := by
  unfold booleanWeight
  rw [Fin.sum_univ_succ]
  simp [Nat.add_comm]

variable {H : Type*} [AddCommGroup H]

def cubeShift {j : ℕ} (hs : Fin j → H) (ω : Fin j → Bool) : H :=
  ∑ i, if ω i then hs i else 0

@[simp] theorem cubeShift_cons_false {j : ℕ} (h : H) (hs : Fin j → H)
    (ω : Fin j → Bool) : cubeShift (Fin.cons h hs) (Fin.cons false ω) = cubeShift hs ω := by
  simp [cubeShift, Fin.sum_univ_succ]

@[simp] theorem cubeShift_cons_true {j : ℕ} (h : H) (hs : Fin j → H)
    (ω : Fin j → Bool) : cubeShift (Fin.cons h hs) (Fin.cons true ω) = h + cubeShift hs ω := by
  simp [cubeShift, Fin.sum_univ_succ]

def mixedCubeProduct {j : ℕ} (F : (Fin j → Bool) → H → ℂ) (hs : Fin j → H) (x : H) : ℂ :=
  ∏ ω, conjugationPower (booleanWeight ω) (F ω (x + cubeShift hs ω))

@[simp] theorem mixedCubeProduct_zero (F : (Fin 0 → Bool) → H → ℂ)
    (hs : Fin 0 → H) (x : H) : mixedCubeProduct F hs x = F default x := by
  unfold mixedCubeProduct
  rw [Fintype.prod_subsingleton _ (default : Fin 0 → Bool)]
  simp [booleanWeight, cubeShift, conjugationPower]

theorem mixedCubeProduct_cons {j : ℕ} (F : (Fin (j + 1) → Bool) → H → ℂ)
    (h : H) (hs : Fin j → H) (x : H) :
    mixedCubeProduct F (Fin.cons h hs) x =
      mixedCubeProduct (fun ω ↦ F (Fin.cons false ω)) hs x *
        star (mixedCubeProduct (fun ω ↦ F (Fin.cons true ω)) hs (x + h)) := by
  simp only [mixedCubeProduct]
  rw [prod_bool_tuple_succ]
  simp only [booleanWeight_cons_false, booleanWeight_cons_true,
    cubeShift_cons_false, cubeShift_cons_true, conjugationPower, RingHom.comp_apply,
    starRingEnd_apply, ← add_assoc]
  change _ = _ * (starRingEnd ℂ) _
  rw [map_prod]
  simp only [starRingEnd_apply]

theorem mixedCubeProduct_crossDerivative {j : ℕ} (F G : (Fin j → Bool) → H → ℂ)
    (h : H) (hs : Fin j → H) (x : H) :
    mixedCubeProduct (fun ω ↦ crossDerivative (F ω) (G ω) h) hs x =
      mixedCubeProduct F hs x * star (mixedCubeProduct G hs (x + h)) := by
  simp only [mixedCubeProduct, crossDerivative, map_mul, conjugationPower_star,
    Finset.prod_mul_distrib]
  change _ = _ * (starRingEnd ℂ) _
  rw [map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro ω hω
  congr 3
  abel

variable [Fintype H]

theorem mixedGowersMoment_eq_expect_cube {j : ℕ} (F : (Fin j → Bool) → H → ℂ) :
    mixedGowersMoment j F = 𝔼 hs : Fin j → H, 𝔼 x, mixedCubeProduct F hs x := by
  induction j with
  | zero => simp [mixedGowersMoment]
  | succ j ih =>
    rw [mixedGowersMoment, expect_fin_cons]
    simp_rw [ih, mixedCubeProduct_crossDerivative, mixedCubeProduct_cons]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem norm_gowersMoment (j : ℕ) (f : H → ℂ) :
    ‖gowersMoment (j + 1) f‖ = (gowersMoment (j + 1) f).re := by
  have he : gowersMoment (j + 1) f = ((gowersMoment (j + 1) f).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simp only [gowersMoment_im_zero, Complex.ofReal_im]
  conv_lhs => rw [he]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gowersMoment_re_nonneg j f)]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

omit [Fintype H] in
theorem multiplicativeDerivative_const_mul (c : ℂ) (f : H → ℂ) (h : H) :
    multiplicativeDerivative (fun x ↦ c * f x) h =
      (fun x ↦ (c * star c) * multiplicativeDerivative f h x) := by
  funext x
  simp only [multiplicativeDerivative, star_mul]
  ring

theorem gowersNorm_const_mul (j : ℕ) (c : ℂ) (f : H → ℂ) :
    gowersNorm (j + 1) (fun x ↦ c * f x) = ‖c‖ * gowersNorm (j + 1) f := by
  induction j generalizing c f with
  | zero =>
    simp only [Nat.zero_add, gowersNorm_one, ← Finset.mul_expect, norm_mul]
  | succ j ih =>
    apply (pow_left_inj₀ (gowersNorm_nonneg (j + 1) _)
      (mul_nonneg (norm_nonneg _) (gowersNorm_nonneg (j + 1) _))
      (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))).mp
    rw [gowersNorm_derivative, mul_pow, gowersNorm_derivative]
    simp only [multiplicativeDerivative_const_mul, ih, norm_mul, norm_star, mul_pow]
    rw [← Finset.mul_expect]
    congr 1
    rw [← pow_add]
    congr 1
    simp [pow_succ, Nat.mul_two]

theorem gowersNorm_le_succ (j : ℕ) (f : H → ℂ) :
    gowersNorm (j + 1) f ≤ gowersNorm (j + 2) f := by
  let F (ω : Fin (j + 2) → Bool) : H → ℂ := if ω 0 then (fun _ ↦ 1) else f
  have hm : mixedGowersMoment (j + 2) F = gowersMoment (j + 1) f := by
    change (𝔼 h, mixedGowersMoment (j + 1)
      (fun ω ↦ crossDerivative (F (Fin.cons false ω)) (F (Fin.cons true ω)) h)) = _
    have hd (h : H) :
        (fun ω ↦ crossDerivative (F (Fin.cons false ω)) (F (Fin.cons true ω)) h) =
        (fun _ : Fin (j + 1) → Bool ↦ f) := by
      funext ω x
      simp [F, crossDerivative]
    simp only [hd, mixedGowersMoment_const, Fintype.expect_const]
  have hp : (∏ ω, gowersNorm (j + 2) (F ω)) = gowersNorm (j + 2) f ^ (2 ^ (j + 1)) := by
    rw [prod_bool_tuple_succ]
    simp [F, gowersNorm_const_one]
  apply le_of_pow_le_pow_left₀ (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
    (gowersNorm_nonneg (j + 1) f)
  rw [gowersNorm_pow, ← norm_gowersMoment, ← hm]
  exact (norm_mixedGowersMoment_le (j + 1) F).trans_eq hp

theorem norm_expect_le_gowersNorm (j : ℕ) (f : H → ℂ) :
    ‖𝔼 x, f x‖ ≤ gowersNorm (j + 1) f := by
  induction j with
  | zero => exact (gowersNorm_one f).ge
  | succ j ih => exact ih.trans (gowersNorm_le_succ j f)

theorem gowersNorm_const (j : ℕ) (c : ℂ) :
    gowersNorm (j + 1) (fun _ : H ↦ c) = ‖c‖ := by
  simpa only [mul_one, gowersNorm_const_one] using
    (gowersNorm_const_mul j c (fun _ : H ↦ 1))

@[simp] theorem gowersNorm_zero (j : ℕ) :
    gowersNorm (j + 1) (fun _ : H ↦ 0) = 0 := by
  rw [gowersNorm_const, norm_zero]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem norm_gowersMoment_le_mean_norm (j : ℕ) (f : H → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) : ‖gowersMoment j f‖ ≤ 𝔼 x, ‖f x‖ := by
  induction j generalizing f with
  | zero => exact RCLike.norm_expect_le (K := ℂ)
  | succ j ih =>
    have hunit (h x : H) : ‖multiplicativeDerivative f h x‖ ≤ 1 := by
      simpa only [multiplicativeDerivative, norm_mul, norm_star, one_mul] using
        mul_le_mul (hf x) (hf (x + h)) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have hnorm (h x : H) : ‖multiplicativeDerivative f h x‖ ≤ ‖f x‖ := by
      simpa only [multiplicativeDerivative, norm_mul, norm_star, mul_one] using
        mul_le_mul_of_nonneg_left (hf (x + h)) (norm_nonneg (f x))
    calc
      _ ≤ 𝔼 h, ‖gowersMoment j (multiplicativeDerivative f h)‖ := RCLike.norm_expect_le (K := ℂ)
      _ ≤ 𝔼 _h : H, 𝔼 x, ‖f x‖ := by
        apply Finset.expect_le_expect
        intro h _
        exact (ih _ (hunit h)).trans (Finset.expect_le_expect (fun x _ => hnorm h x))
      _ = _ := Fintype.expect_const _

theorem gowersNorm_pow_le_mean_norm (j : ℕ) (f : H → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    gowersNorm (j + 1) f ^ (2 ^ (j + 1)) ≤ 𝔼 x, ‖f x‖ := by
  rw [gowersNorm_pow, ← norm_gowersMoment]
  exact norm_gowersMoment_le_mean_norm (j + 1) f hf

theorem gowersNorm_le_of_mean_norm_le_pow (j : ℕ) (f : H → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hmean : (𝔼 x, ‖f x‖) ≤ ε ^ (2 ^ (j + 1))) : gowersNorm (j + 1) f ≤ ε := by
  exact le_of_pow_le_pow_left₀ (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) hε
    ((gowersNorm_pow_le_mean_norm j f hf).trans hmean)

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

def restrictTo (Q : Finset H) (f : H → ℂ) : H → ℂ :=
  fun x ↦ if x ∈ Q then f x else 0

omit [AddCommGroup H] [Fintype H] in
@[simp] theorem restrictTo_empty (f : H → ℂ) :
    restrictTo ∅ f = (fun _ ↦ 0) := by
  funext x
  simp [restrictTo]

omit [AddCommGroup H] in
theorem expect_restrictTo (Q : Finset H) (f : H → ℂ) :
    (𝔼 x, restrictTo Q f x) = (∑ x ∈ Q, f x) / Fintype.card H := by
  simp [restrictTo, Fintype.expect_eq_sum_div_card]

omit [AddCommGroup H] in
theorem norm_expect_restrict_one (Q : Finset H) :
    ‖𝔼 x, restrictTo Q (fun _ ↦ 1) x‖ = (Q.card : ℝ) / Fintype.card H := by
  rw [expect_restrictTo]
  simp

noncomputable def restrictedGowersNorm (j : ℕ) (Q : Finset H) (f : H → ℂ) : ℝ :=
  gowersNorm j (restrictTo Q f) / gowersNorm j (restrictTo Q (fun _ ↦ 1))

theorem restrictedGowersNorm_nonneg (j : ℕ) (Q : Finset H) (f : H → ℂ) :
    0 ≤ restrictedGowersNorm (j + 1) Q f :=
  div_nonneg (gowersNorm_nonneg j _) (gowersNorm_nonneg j _)

theorem restrictedGowersNorm_degree_one {Q : Finset H} (hQ : Q.Nonempty) (f : H → ℂ) :
    restrictedGowersNorm 1 Q f = ‖𝔼 x ∈ Q, f x‖ := by
  rw [restrictedGowersNorm, gowersNorm_one, gowersNorm_one,
    norm_expect_restrict_one, expect_restrictTo, Finset.expect_eq_sum_div_card]
  simp only [norm_div, Complex.norm_natCast]
  have hcard : (Q.card : ℝ) ≠ 0 := by exact_mod_cast hQ.card_pos.ne'
  have hH : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem norm_mixedGowersMoment_restrict_le (j : ℕ) (Q : Finset H)
    (F : (Fin (j + 1) → Bool) → H → ℂ) :
    ‖mixedGowersMoment (j + 1) (fun ω ↦ restrictTo Q (F ω))‖ /
        (gowersMoment (j + 1) (restrictTo Q (fun _ ↦ 1))).re ≤
      ∏ ω, restrictedGowersNorm (j + 1) Q (F ω) := by
  simp only [restrictedGowersNorm, Finset.prod_div_distrib]
  rw [Finset.prod_const]
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [gowersNorm_pow]
  exact div_le_div_of_nonneg_right (norm_mixedGowersMoment_le j _)
    (gowersMoment_re_nonneg j _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

theorem multiplicativeDerivative_norm_le_one (f : G → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (h x : G) : ‖multiplicativeDerivative f h x‖ ≤ 1 := by
  simpa only [multiplicativeDerivative, norm_mul, norm_star, one_mul] using
    mul_le_mul (hf x) (hf (x + h)) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

variable [Fintype G]

theorem gowersNorm_le_one (s : ℕ) (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    gowersNorm (s + 1) f ≤ 1 := by
  apply gowersNorm_le_of_mean_norm_le_pow s f hf (by norm_num)
  simpa only [one_pow, Fintype.expect_const] using
    Finset.expect_le_expect (s := Finset.univ) (fun x _ => hf x)

def derivativeInverseBudget (s : ℕ) (p : ℝ) : ℝ := (2 ^ (s + 2) : ℕ) * p + 2

theorem derivativeInverseBudget_ge_two (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    2 ≤ derivativeInverseBudget s p := by
  unfold derivativeInverseBudget
  exact le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) hp)

theorem exists_many_large_gowers_derivatives (s : ℕ) (f : G → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) {p : ℝ} (hp : 0 ≤ p)
    (hG : Real.exp (-p) ≤ gowersNorm (s + 2) f) :
    ∃ H : Finset G, H.Nonempty ∧
      Real.exp (-derivativeInverseBudget s p) * Fintype.card G ≤ (H.card : ℝ) ∧
      ∀ h ∈ H, Real.exp (-derivativeInverseBudget s p) ≤
        gowersNorm (s + 1) (multiplicativeDerivative f h) := by
  let a := Real.exp (-((2 ^ (s + 2) : ℕ) : ℝ) * p)
  have hmean : a ≤ 𝔼 h, gowersNorm (s + 1) (multiplicativeDerivative f h) ^
      (2 ^ (s + 1)) := by
    rw [← gowersNorm_derivative]
    calc
      a = Real.exp (-p) ^ (2 ^ (s + 2)) := by
        dsimp [a]
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_nonneg _) hG _
  have hunit (h : G) : gowersNorm (s + 1) (multiplicativeDerivative f h) ≤ 1 :=
    gowersNorm_le_one s _ (multiplicativeDerivative_norm_le_one f hf h)
  obtain ⟨H, hcard, hlarge⟩ := exists_dense_level_set
    (fun h => gowersNorm (s + 1) (multiplicativeDerivative f h) ^ (2 ^ (s + 1)))
    (Real.exp_nonneg _) (fun h => pow_le_one₀ (gowersNorm_nonneg s _) (hunit h)) hmean
  have hsmall : Real.exp (-derivativeInverseBudget s p) ≤ a / 2 := by
    calc
      _ ≤ Real.exp (-((2 ^ (s + 2) : ℕ) : ℝ) * p - 1) := by
        apply Real.exp_le_exp.mpr
        unfold derivativeInverseBudget
        linarith
      _ ≤ _ := exp_sub_one_le_half_exp _
  have hdense : Real.exp (-derivativeInverseBudget s p) * Fintype.card G ≤
      (H.card : ℝ) :=
    (mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg _)).trans hcard
  have hnonempty : H.Nonempty := by
    apply Finset.card_pos.mp
    have hpos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
    exact_mod_cast (mul_pos (Real.exp_pos _) hpos).trans_le hdense
  refine ⟨H, hnonempty, hdense, fun h hh => ?_⟩
  exact exp_neg_le_of_pow (gowersNorm_nonneg s _)
    (by linarith [derivativeInverseBudget_ge_two s hp])
    (pow_ne_zero _ (by norm_num)) (hsmall.trans (hlarge h hh))

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

def groupCubeSet (j : ℕ) (Q : Finset H) : Finset ((Fin j → H) × H) :=
  Finset.univ.filter (fun p ↦ ∀ ω : Fin j → Bool, p.2 + cubeShift p.1 ω ∈ Q)

def groupCubeCount (j : ℕ) (Q : Finset H) : ℕ := (groupCubeSet j Q).card

omit [Fintype H] in
theorem mixedCubeProduct_indicator (j : ℕ) (Q : Finset H) (hs : Fin j → H) (x : H) :
    mixedCubeProduct (fun _ ↦ restrictTo Q (fun _ ↦ 1)) hs x =
      if ∀ ω : Fin j → Bool, x + cubeShift hs ω ∈ Q then 1 else 0 := by
  have hv (ω : Fin j → Bool) :
      conjugationPower (booleanWeight ω) (restrictTo Q (fun _ ↦ 1) (x + cubeShift hs ω)) =
        if x + cubeShift hs ω ∈ Q then 1 else 0 := by
    by_cases hω : x + cubeShift hs ω ∈ Q <;> simp [restrictTo, hω]
  simp only [mixedCubeProduct, hv]
  by_cases hall : ∀ ω : Fin j → Bool, x + cubeShift hs ω ∈ Q
  · simp [hall]
  · rw [if_neg hall]
    obtain ⟨ω, hω⟩ := not_forall.mp hall
    exact Finset.prod_eq_zero (Finset.mem_univ ω) (if_neg hω)

theorem gowersMoment_indicator_eq_cubeCount (j : ℕ) (Q : Finset H) :
    gowersMoment j (restrictTo Q (fun _ ↦ 1)) =
      (groupCubeCount j Q : ℂ) / (Fintype.card H : ℂ) ^ (j + 1) := by
  rw [← mixedGowersMoment_const, mixedGowersMoment_eq_expect_cube]
  simp_rw [mixedCubeProduct_indicator]
  rw [← Finset.expect_product', Finset.univ_product_univ]
  rw [Fintype.expect_eq_sum_div_card]
  have hsum : (∑ p : (Fin j → H) × H,
      if ∀ ω : Fin j → Bool, p.2 + cubeShift p.1 ω ∈ Q then (1 : ℂ) else 0) =
        (groupCubeCount j Q : ℂ) := by
    simp [groupCubeCount, groupCubeSet]
  rw [hsum]
  simp [Fintype.card_prod, pow_succ]

theorem gowersMoment_indicator_re (j : ℕ) (Q : Finset H) :
    (gowersMoment j (restrictTo Q (fun _ ↦ 1))).re =
      (groupCubeCount j Q : ℝ) / (Fintype.card H : ℝ) ^ (j + 1) := by
  rw [gowersMoment_indicator_eq_cubeCount]
  simpa only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast] using
    (Complex.ofReal_re ((groupCubeCount j Q : ℝ) / (Fintype.card H : ℝ) ^ (j + 1)))

end Erdos3

end

section

namespace Erdos3

variable {G : Type*} [AddCommGroup G]

theorem cubeProduct_norm_le_one (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hs : List G) (x : G) : ‖cubeProduct f hs x‖ ≤ 1 := by
  induction hs generalizing x with
  | nil => simpa only [cubeProduct_nil] using hf x
  | cons h hs ih =>
    rw [cubeProduct_cons, norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ih x)).trans (ih (x + h))

theorem cubeProduct_mul (f g : G → ℂ) (hs : List G) (x : G) :
    cubeProduct (fun y => f y * g y) hs x = cubeProduct f hs x * cubeProduct g hs x := by
  induction hs generalizing x with
  | nil => simp only [cubeProduct_nil]
  | cons h hs ih =>
    simp only [cubeProduct_cons, ih, star_mul]
    ring

theorem cubeProduct_star (f : G → ℂ) (hs : List G) (x : G) :
    cubeProduct (fun y => star (f y)) hs x = star (cubeProduct f hs x) := by
  induction hs generalizing x with
  | nil => simp only [cubeProduct_nil]
  | cons h hs ih =>
    simp only [cubeProduct_cons, ih, star_mul, star_star]
    exact mul_comm _ _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def additiveQuadrupleCorrelation (g : G → G → ℂ) (a h k : G) : ℝ :=
  ‖𝔼 x, star (g h x) * g (h - a) (x + a) * g k x * star (g (k - a) (x + a))‖

theorem derivative_correlations_force_additive_quadruples
    (f : G → ℂ) (g : G → G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    (𝔼 h, ‖𝔼 x, multiplicativeDerivative f h x * star (g h x)‖) ^ 4 ≤
      𝔼 a, 𝔼 h, 𝔼 k, additiveQuadrupleCorrelation g a h k := by
  let C (a : G) := 𝔼 h, ‖𝔼 x, multiplicativeDerivative f a x *
    (star (g h x) * g (h - a) (x + a))‖
  have hfirst : (𝔼 h, ‖𝔼 x, multiplicativeDerivative f h x * star (g h x)‖) ^ 2 ≤
      𝔼 a, C a := by
    have hcs := shifted_test_cauchy_schwarz f (fun x => star (f x))
      (fun h x => star (g h x)) (M := 1) (by simpa only [norm_star] using hf)
    have hreindex : (𝔼 h, 𝔼 k, ‖𝔼 x, f x * star (f (x + h - k)) *
        star (g h x) * g k (x + h - k)‖) = 𝔼 a, C a := by
      calc
        _ = 𝔼 h, 𝔼 a, ‖𝔼 x, multiplicativeDerivative f a x *
            (star (g h x) * g (h - a) (x + a))‖ := by
          apply Finset.expect_congr rfl
          intro h _
          apply Fintype.expect_equiv (Equiv.subLeft h)
          intro k
          simp only [Equiv.subLeft_apply, sub_sub_cancel, multiplicativeDerivative,
            ← add_sub_assoc, mul_assoc]
        _ = _ := Finset.expect_comm _ _ _
    rw [← hreindex]
    simpa only [one_pow, one_mul, star_star, multiplicativeDerivative, mul_assoc] using hcs
  have hsecond (a : G) : C a ^ 2 ≤
      𝔼 h, 𝔼 k, additiveQuadrupleCorrelation g a h k := by
    have hcs := finite_absolute_cauchy_schwarz (multiplicativeDerivative f a)
      (fun h x => star (g h x) * g (h - a) (x + a))
      (multiplicativeDerivative_norm_le_one f hf a)
    simpa only [one_pow, one_mul, C, additiveQuadrupleCorrelation, star_mul,
      star_star, mul_assoc, mul_comm, mul_left_comm] using hcs
  calc
    _ = ((𝔼 h, ‖𝔼 x, multiplicativeDerivative f h x * star (g h x)‖) ^ 2) ^ 2 := by ring
    _ ≤ (𝔼 a, C a) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hfirst 2
    _ ≤ 𝔼 a, C a ^ 2 := expect_square_le C
    _ ≤ _ := Finset.expect_le_expect (fun a _ => hsecond a)

theorem additiveQuadrupleCorrelation_le_one (g : G → G → ℂ)
    (hg : ∀ h x, ‖g h x‖ ≤ 1) (a h k : G) : additiveQuadrupleCorrelation g a h k ≤ 1 := by
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply Finset.expect_le Finset.univ_nonempty
  intro x _
  simp only [norm_mul, norm_star]
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hg _ _)
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hg _ _)
  exact (mul_le_of_le_one_left (norm_nonneg _) (hg _ _)).trans (hg _ _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem conjugationPower_norm (n : ℕ) (z : ℂ) : ‖conjugationPower n z‖ = ‖z‖ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ‖star (conjugationPower n z)‖ = ‖z‖
    rw [norm_star, ih]

theorem cubeProduct_eq_mixedCubeProduct {H : Type*} [AddCommGroup H]
    (f : H → ℂ) {d : ℕ} (k : Fin d → H) (x : H) :
    cubeProduct f (List.ofFn k) x = mixedCubeProduct (fun _ => f) k x := by
  induction d generalizing x with
  | zero => simp only [List.ofFn_zero, cubeProduct_nil, mixedCubeProduct_zero]
  | succ d ih =>
    rw [← Fin.cons_self_tail k, List.ofFn_cons, cubeProduct_cons, mixedCubeProduct_cons]
    rw [ih, ih]

theorem cubeProduct_eq_boolean_product {H : Type*} [AddCommGroup H]
    (f : H → ℂ) {d : ℕ} (k : Fin d → H) (x : H) :
    cubeProduct f (List.ofFn k) x =
      ∏ ω : Fin d → Bool, conjugationPower (booleanWeight ω) (f (x + cubeShift k ω)) :=
  cubeProduct_eq_mixedCubeProduct f k x

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GowersWeightedDerivative
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

def derivativeSupport (Q : Finset H) (h : H) : Finset H :=
  Q.filter (fun x ↦ x + h ∈ Q)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedCubeEquivTransport
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

@[simp] theorem cubeShift_false {j : ℕ} (hs : Fin j → A) :
    cubeShift hs (fun _ ↦ false) = 0 := by simp [cubeShift]

def cubeAxis {j : ℕ} (i : Fin j) : Fin j → Bool := fun k ↦ decide (k = i)

@[simp] theorem cubeShift_axis {j : ℕ} (hs : Fin j → A) (i : Fin j) :
    cubeShift hs (cubeAxis i) = hs i := by simp [cubeShift, cubeAxis]

theorem map_cubeShift (φ : A →+ B) {j : ℕ} (hs : Fin j → A) (ω : Fin j → Bool) :
    φ (cubeShift hs ω) = cubeShift (fun i ↦ φ (hs i)) ω := by
  simp only [cubeShift, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp

def ReflectsPairSums (φ : A →+ B) (Q : Set A) : Prop :=
  ∀ a ∈ Q, ∀ b ∈ Q, ∀ c ∈ Q, ∀ d ∈ Q,
    φ a + φ b = φ c + φ d → a + b = c + d

theorem ReflectsPairSums.injOn {φ : A →+ B} {Q : Set A}
    (hφ : ReflectsPairSums φ Q) : Set.InjOn φ Q := by
  intro a ha b hb he
  exact add_right_cancel (hφ a ha a ha b hb a ha (by rw [he]))

abbrev SupportedCube (j : ℕ) (Q : Set A) :=
  {p : (Fin j → A) × A // ∀ ω : Fin j → Bool, p.2 + cubeShift p.1 ω ∈ Q}

theorem SupportedCube.base_mem {j : ℕ} {Q : Set A} (p : SupportedCube j Q) : p.val.2 ∈ Q := by
  simpa using p.property (fun _ ↦ false)

theorem SupportedCube.axis_mem {j : ℕ} {Q : Set A} (p : SupportedCube j Q) (i : Fin j) :
    p.val.2 + p.val.1 i ∈ Q := by
  simpa using p.property (cubeAxis i)

def SupportedCube.map (φ : A →+ B) {j : ℕ} {Q : Set A} (p : SupportedCube j Q) :
    SupportedCube j (φ '' Q) :=
  ⟨(fun i ↦ φ (p.val.1 i), φ p.val.2), fun ω ↦
    ⟨p.val.2 + cubeShift p.val.1 ω, p.property ω, by rw [map_add, map_cubeShift]⟩⟩

theorem SupportedCube.map_injective {φ : A →+ B} {Q : Set A}
    (hφ : Set.InjOn φ Q) (j : ℕ) :
    Function.Injective (SupportedCube.map φ : SupportedCube j Q → _) := by
  intro p q he
  have hb : φ p.val.2 = φ q.val.2 := congrArg (fun r ↦ r.val.2) he
  have hx : p.val.2 = q.val.2 := hφ p.base_mem q.base_mem hb
  have hh (i : Fin j) : φ (p.val.1 i) = φ (q.val.1 i) :=
    congrArg (fun r ↦ r.val.1 i) he
  have hi (i : Fin j) : p.val.1 i = q.val.1 i := by
    have hv := hφ (p.axis_mem i) (q.axis_mem i) (by simp only [map_add, hb, hh])
    rw [hx] at hv
    exact add_left_cancel hv
  apply Subtype.ext
  exact Prod.ext (funext hi) hx

theorem exists_lift_cube {φ : A →+ B} {Q : Set A} (hφ : ReflectsPairSums φ Q)
    (j : ℕ) (x : B) (hs : Fin j → B)
    (hQ : ∀ ω : Fin j → Bool, x + cubeShift hs ω ∈ φ '' Q) :
    ∃ a : A, ∃ ds : Fin j → A,
      (∀ ω : Fin j → Bool, a + cubeShift ds ω ∈ Q) ∧ φ a = x ∧ ∀ i, φ (ds i) = hs i := by
  induction j generalizing x with
  | zero =>
    obtain ⟨a, ha, he⟩ := hQ (fun _ ↦ false)
    refine ⟨a, (fun i ↦ Fin.elim0 i), ?_, ?_, fun i ↦ Fin.elim0 i⟩
    · intro ω
      simpa [cubeShift] using ha
    · simpa using he
  | succ j ih =>
    have hface : ∀ ω : Fin j → Bool, x + cubeShift (Fin.tail hs) ω ∈ φ '' Q := by
      intro ω
      have hv := hQ (Fin.cons false ω)
      rw [← Fin.cons_self_tail hs, cubeShift_cons_false] at hv
      exact hv
    obtain ⟨a, ds, hds, ha, hmap⟩ := ih x (Fin.tail hs) hface
    obtain ⟨b, hb, hbmap⟩ := hQ (Fin.cons true (fun _ ↦ false))
    rw [← Fin.cons_self_tail hs, cubeShift_cons_true, cubeShift_false, add_zero] at hbmap
    have hamem : a ∈ Q := by simpa using hds (fun _ ↦ false)
    have hdmap : φ (b - a) = hs 0 := by rw [map_sub, hbmap, ha]; abel
    refine ⟨a, Fin.cons (b - a) ds, ?_, ha, ?_⟩
    · intro ω
      rw [← Fin.cons_self_tail ω]
      cases hω : ω 0 with
      | false => simpa only [cubeShift_cons_false] using hds (Fin.tail ω)
      | true =>
        rw [cubeShift_cons_true]
        obtain ⟨c, hc, hcmap⟩ := hQ (Fin.cons true (Fin.tail ω))
        rw [← Fin.cons_self_tail hs, cubeShift_cons_true] at hcmap
        have hpair : (a + cubeShift ds (Fin.tail ω)) + b = c + a := by
          apply hφ _ (hds (Fin.tail ω)) b hb c hc a hamem
          simp only [map_add, map_cubeShift, hmap, hbmap, hcmap, ha]
          abel
        have he : a + (b - a + cubeShift ds (Fin.tail ω)) = c := by
          apply add_right_cancel (b := a)
          calc
            (a + (b - a + cubeShift ds (Fin.tail ω))) + a =
                (a + cubeShift ds (Fin.tail ω)) + b := by abel
            _ = c + a := hpair
        rwa [he]
    · intro i
      refine Fin.cases ?_ (fun k ↦ ?_) i
      · exact hdmap
      · exact hmap k

theorem SupportedCube.map_surjective {φ : A →+ B} {Q : Set A}
    (hφ : ReflectsPairSums φ Q) (j : ℕ) :
    Function.Surjective (SupportedCube.map φ : SupportedCube j Q → _) := by
  intro p
  obtain ⟨a, ds, hds, ha, hmap⟩ := exists_lift_cube hφ j p.val.2 p.val.1 p.property
  refine ⟨⟨(ds, a), hds⟩, ?_⟩
  apply Subtype.ext
  exact Prod.ext (funext hmap) ha

noncomputable def supportedCubeEquiv {φ : A →+ B} {Q : Set A}
    (hφ : ReflectsPairSums φ Q) (j : ℕ) : SupportedCube j Q ≃ SupportedCube j (φ '' Q) :=
  Equiv.ofBijective (SupportedCube.map φ) ⟨SupportedCube.map_injective hφ.injOn j,
    SupportedCube.map_surjective hφ j⟩

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A : Type*} [AddCommGroup A]

def SupportedCube.points {j : ℕ} {Q : Set A} (p : SupportedCube j Q) : Q × (Fin j → Q) :=
  (⟨p.val.2, p.base_mem⟩, fun i ↦ ⟨p.val.2 + p.val.1 i, p.axis_mem i⟩)

theorem SupportedCube.points_injective (j : ℕ) (Q : Set A) :
    Function.Injective (SupportedCube.points : SupportedCube j Q → _) := by
  intro p q he
  have hx : p.val.2 = q.val.2 := congrArg (fun r ↦ r.1.val) he
  have hd (i : Fin j) : p.val.1 i = q.val.1 i := by
    have hi : p.val.2 + p.val.1 i = q.val.2 + q.val.1 i :=
      congrArg (fun r ↦ (r.2 i).val) he
    rw [hx] at hi
    exact add_left_cancel hi
  apply Subtype.ext
  exact Prod.ext (funext hd) hx

instance supportedCubeFinite (j : ℕ) (Q : Set A) [Finite Q] : Finite (SupportedCube j Q) :=
  Finite.of_injective SupportedCube.points (SupportedCube.points_injective j Q)

noncomputable instance supportedCubeFintype (j : ℕ) (Q : Set A) [Finite Q] :
    Fintype (SupportedCube j Q) := Fintype.ofFinite _

noncomputable def supportedCubeSum (j : ℕ) (Q : Set A) [Finite Q]
    (F : (Fin j → Bool) → A → ℂ) : ℂ :=
  ∑ p : SupportedCube j Q, mixedCubeProduct F p.val.1 p.val.2

section FiniteAmbient

variable [Fintype A] [DecidableEq A]

noncomputable def supportedCubeFinsetEquiv (j : ℕ) (Q : Finset A) :
    SupportedCube j (Q : Set A) ≃ (groupCubeSet j Q) :=
  Equiv.subtypeEquivRight (fun p ↦ by simp [groupCubeSet])

theorem card_supportedCube (j : ℕ) (Q : Finset A) :
    Nat.card (SupportedCube j (Q : Set A)) = groupCubeCount j Q := by
  rw [Nat.card_congr (supportedCubeFinsetEquiv j Q), Nat.card_eq_fintype_card]
  exact Fintype.card_coe _

theorem supportedCubeSum_eq_sum (j : ℕ) (Q : Finset A) (F : (Fin j → Bool) → A → ℂ) :
    supportedCubeSum j (Q : Set A) F =
      ∑ p ∈ groupCubeSet j Q, mixedCubeProduct F p.1 p.2 := by
  exact (Finset.sum_subtype (groupCubeSet j Q) (fun p ↦ by simp [groupCubeSet])
    (fun p ↦ mixedCubeProduct F p.1 p.2)).symm

omit [Fintype A] in
theorem mixedCubeProduct_restrictTo {j : ℕ} (Q : Finset A)
    (F : (Fin j → Bool) → A → ℂ) (hs : Fin j → A) (x : A) :
    mixedCubeProduct (fun ω ↦ restrictTo Q (F ω)) hs x =
      if ∀ ω : Fin j → Bool, x + cubeShift hs ω ∈ Q then mixedCubeProduct F hs x else 0 := by
  classical
  by_cases hall : ∀ ω : Fin j → Bool, x + cubeShift hs ω ∈ Q
  · rw [if_pos hall]
    unfold mixedCubeProduct
    apply Finset.prod_congr rfl
    intro ω hω
    simp only [restrictTo, if_pos (hall ω)]
  · rw [if_neg hall]
    obtain ⟨ω, hω⟩ := not_forall.mp hall
    unfold mixedCubeProduct
    apply Finset.prod_eq_zero (Finset.mem_univ ω)
    simp only [restrictTo, if_neg hω, map_zero]

theorem mixedGowersMoment_restrict_eq_supportedCubeSum (j : ℕ) (Q : Finset A)
    (F : (Fin j → Bool) → A → ℂ) :
    mixedGowersMoment j (fun ω ↦ restrictTo Q (F ω)) =
      supportedCubeSum j (Q : Set A) F / (Fintype.card A : ℂ) ^ (j + 1) := by
  classical
  rw [mixedGowersMoment_eq_expect_cube]
  simp_rw [mixedCubeProduct_restrictTo]
  rw [← Finset.expect_product', Finset.univ_product_univ,
    Fintype.expect_eq_sum_div_card, supportedCubeSum_eq_sum]
  have hc : (Fintype.card ((Fin j → A) × A) : ℂ) = (Fintype.card A : ℂ) ^ (j + 1) := by
    simp [pow_succ]
  rw [hc]
  congr 1
  simp [groupCubeSet, Finset.sum_filter]

end FiniteAmbient

variable [DecidableEq A]

omit [DecidableEq A] in
theorem card_supportedCube_le (j : ℕ) (Q : Finset A) :
    Nat.card (SupportedCube j (Q : Set A)) ≤ Q.card ^ (j + 1) := by
  have h := Nat.card_le_card_of_injective SupportedCube.points
    (SupportedCube.points_injective j (Q : Set A))
  simpa [Nat.card_eq_fintype_card, pow_succ, mul_comm] using h

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

noncomputable def imageExtension (φ : A →+ B) (Q : Finset A) (f : A → ℂ) : B → ℂ := by
  classical
  exact fun y ↦ ∑ a ∈ Q, if φ a = y then f a else 0

theorem imageExtension_apply {φ : A →+ B} {Q : Finset A} (hi : Set.InjOn φ (Q : Set A))
    (f : A → ℂ) {a : A} (ha : a ∈ Q) : imageExtension φ Q f (φ a) = f a := by
  classical
  unfold imageExtension
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    exact if_neg (fun he ↦ hba (hi hb ha he))
  · intro hna
    exact (hna ha).elim

theorem imageExtension_eq_zero {φ : A →+ B} {Q : Finset A} (f : A → ℂ) {y : B}
    (hy : y ∉ φ '' (Q : Set A)) : imageExtension φ Q f y = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro a ha
  exact if_neg (fun he ↦ hy ⟨a, ha, he⟩)

theorem mixedCubeProduct_imageExtension {φ : A →+ B} {Q : Finset A}
    (hi : Set.InjOn φ (Q : Set A)) {j : ℕ} (F : (Fin j → Bool) → A → ℂ)
    (p : SupportedCube j (Q : Set A)) :
    mixedCubeProduct (fun ω ↦ imageExtension φ Q (F ω))
      (fun i ↦ φ (p.val.1 i)) (φ p.val.2) = mixedCubeProduct F p.val.1 p.val.2 := by
  unfold mixedCubeProduct
  apply Finset.prod_congr rfl
  intro ω hω
  rw [← map_cubeShift, ← map_add]
  exact congrArg (conjugationPower (booleanWeight ω))
    (imageExtension_apply hi (F ω) (p.property ω))

variable [Fintype B] [DecidableEq B]

omit [Fintype B] in
theorem restrictTo_imageExtension (φ : A →+ B) (Q : Finset A) (f : A → ℂ) :
    restrictTo (Q.image φ) (imageExtension φ Q f) = imageExtension φ Q f := by
  classical
  funext y
  by_cases hy : y ∈ Q.image φ
  · simp only [restrictTo, if_pos hy]
  · rw [restrictTo, if_neg hy]
    exact (imageExtension_eq_zero f (by
      rintro ⟨a, ha, he⟩
      exact hy (Finset.mem_image.mpr ⟨a, ha, he⟩))).symm

omit [Fintype B] [DecidableEq B] in
theorem supportedCubeSum_imageExtension {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) (F : (Fin j → Bool) → A → ℂ) :
    supportedCubeSum j (φ '' (Q : Set A)) (fun ω ↦ imageExtension φ Q (F ω)) =
      supportedCubeSum j (Q : Set A) F := by
  classical
  symm
  apply Fintype.sum_equiv (supportedCubeEquiv hφ j)
  intro p
  exact (mixedCubeProduct_imageExtension hφ.injOn F p).symm

theorem mixedGowersMoment_imageExtension {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) (F : (Fin j → Bool) → A → ℂ) :
    mixedGowersMoment j (fun ω ↦ imageExtension φ Q (F ω)) =
      supportedCubeSum j (Q : Set A) F / (Fintype.card B : ℂ) ^ (j + 1) := by
  classical
  have hr : (fun ω ↦ imageExtension φ Q (F ω)) =
      (fun ω ↦ restrictTo (Q.image φ) (imageExtension φ Q (F ω))) := by
    funext ω
    exact (restrictTo_imageExtension φ Q (F ω)).symm
  rw [hr, mixedGowersMoment_restrict_eq_supportedCubeSum]
  simp only [Finset.coe_image, supportedCubeSum_imageExtension hφ]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A : Type*} [AddCommGroup A] [DecidableEq A]

def cubeDifferenceSupport (Q : Finset A) : Finset A :=
  (Q ×ˢ Q).image (fun p ↦ p.2 - p.1)

theorem mem_cubeDifferenceSupport (Q : Finset A) (h : A) :
    h ∈ cubeDifferenceSupport Q ↔ (derivativeSupport Q h).Nonempty := by
  constructor
  · intro hh
    obtain ⟨⟨x, y⟩, hp, rfl⟩ := Finset.mem_image.mp hh
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
    refine ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩⟩
    simpa using hy
  · rintro ⟨x, hx⟩
    obtain ⟨hx, hxh⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_image.mpr ⟨(x, x + h), Finset.mem_product.mpr ⟨hx, hxh⟩, by simp⟩

theorem SupportedCube.first_mem_difference {j : ℕ} {Q : Finset A}
    (p : SupportedCube (j + 1) (Q : Set A)) : p.val.1 0 ∈ cubeDifferenceSupport Q :=
  Finset.mem_image.mpr ⟨(p.val.2, p.val.2 + p.val.1 0),
    Finset.mem_product.mpr ⟨p.base_mem, p.axis_mem 0⟩, by simp⟩

def SupportedCube.tail {j : ℕ} {Q : Finset A} (p : SupportedCube (j + 1) (Q : Set A)) :
    SupportedCube j (derivativeSupport Q (p.val.1 0) : Set A) := by
  refine ⟨(Fin.tail p.val.1, p.val.2), ?_⟩
  intro ω
  apply Finset.mem_filter.mpr
  have hfalse := p.property (Fin.cons false ω)
  have htrue := p.property (Fin.cons true ω)
  rw [← Fin.cons_self_tail p.val.1, cubeShift_cons_false] at hfalse
  rw [← Fin.cons_self_tail p.val.1, cubeShift_cons_true] at htrue
  exact ⟨hfalse, by simpa only [Finset.mem_coe, add_assoc, add_left_comm, add_comm] using htrue⟩

def SupportedCube.cons {j : ℕ} {Q : Finset A} (h : A)
    (p : SupportedCube j (derivativeSupport Q h : Set A)) : SupportedCube (j + 1) (Q : Set A) := by
  refine ⟨(Fin.cons h p.val.1, p.val.2), ?_⟩
  intro ω
  obtain ⟨hfalse, htrue⟩ := Finset.mem_filter.mp (p.property (Fin.tail ω))
  rw [← Fin.cons_self_tail ω]
  cases ω 0 with
  | false => simpa only [Finset.mem_coe, cubeShift_cons_false] using hfalse
  | true => simpa only [Finset.mem_coe, cubeShift_cons_true, add_assoc, add_left_comm, add_comm] using htrue

def supportedCubeDerivativeEquiv (j : ℕ) (Q : Finset A) :
    SupportedCube (j + 1) (Q : Set A) ≃
      Σ h : cubeDifferenceSupport Q, SupportedCube j (derivativeSupport Q h.val : Set A) where
  toFun p := ⟨⟨p.val.1 0, p.first_mem_difference⟩, p.tail⟩
  invFun p := p.2.cons p.1.val
  left_inv p := by
    apply Subtype.ext
    change (Fin.cons (p.val.1 0) (Fin.tail p.val.1), p.val.2) = p.val
    rw [Fin.cons_self_tail]
  right_inv p := by
    rcases p with ⟨h, p⟩
    rfl

theorem supportedCubeSum_derivative (j : ℕ) (Q : Finset A)
    (F : (Fin (j + 1) → Bool) → A → ℂ) :
    supportedCubeSum (j + 1) (Q : Set A) F =
      ∑ h ∈ cubeDifferenceSupport Q, supportedCubeSum j (derivativeSupport Q h : Set A)
        (fun ω ↦ crossDerivative (F (Fin.cons false ω)) (F (Fin.cons true ω)) h) := by
  let he := (supportedCubeDerivativeEquiv j Q).symm
  calc
    _ = ∑ p : Σ h : cubeDifferenceSupport Q,
        SupportedCube j (derivativeSupport Q h.val : Set A),
        mixedCubeProduct F (Fin.cons p.1.val p.2.val.1) p.2.val.2 := by
      symm
      apply Fintype.sum_equiv he
      intro p
      rfl
    _ = _ := by
      simp only [Fintype.sum_sigma, mixedCubeProduct_cons,
        ← mixedCubeProduct_crossDerivative, supportedCubeSum]
      exact Finset.sum_coe_sort (cubeDifferenceSupport Q)
        (fun h ↦ supportedCubeSum j (derivativeSupport Q h : Set A)
          (fun ω ↦ crossDerivative (F (Fin.cons false ω)) (F (Fin.cons true ω)) h))

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

noncomputable def finiteSupportGowersNorm (j : ℕ) (Q : Finset A) (f : A → ℂ) : ℝ :=
  ((supportedCubeSum j (Q : Set A) (fun _ ↦ f)).re /
    Nat.card (SupportedCube j (Q : Set A))) ^ (((2 ^ j : ℕ) : ℝ)⁻¹)

variable [Fintype B] [DecidableEq B]

theorem card_supportedCube_image {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) :
    Nat.card (SupportedCube j (Q : Set A)) = groupCubeCount j (Q.image φ) := by
  classical
  rw [Nat.card_congr (supportedCubeEquiv hφ j)]
  simpa only [Finset.coe_image] using card_supportedCube j (Q.image φ)

theorem gowersMoment_imageExtension_re {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) (f : A → ℂ) :
    (gowersMoment j (imageExtension φ Q f)).re =
      (supportedCubeSum j (Q : Set A) (fun _ ↦ f)).re /
        (Fintype.card B : ℝ) ^ (j + 1) := by
  have hm := congrArg Complex.re (mixedGowersMoment_imageExtension hφ j (fun _ ↦ f))
  simpa only [mixedGowersMoment_const, ← Nat.cast_pow, Complex.div_natCast_re] using hm

theorem restrictedGowersNorm_imageExtension_pow {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) (f : A → ℂ) :
    restrictedGowersNorm (j + 1) (Q.image φ) (imageExtension φ Q f) ^ (2 ^ (j + 1)) =
      (supportedCubeSum (j + 1) (Q : Set A) (fun _ ↦ f)).re /
        Nat.card (SupportedCube (j + 1) (Q : Set A)) := by
  simp only [restrictedGowersNorm, div_pow, gowersNorm_pow,
    restrictTo_imageExtension, gowersMoment_imageExtension_re hφ, gowersMoment_indicator_re]
  rw [← card_supportedCube_image hφ]
  exact div_div_div_cancel_right₀
    (pow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero : (Fintype.card B : ℝ) ≠ 0)) _ _

theorem finiteSupportGowersNorm_eq_restricted {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) (f : A → ℂ) :
    finiteSupportGowersNorm (j + 1) Q f =
      restrictedGowersNorm (j + 1) (Q.image φ) (imageExtension φ Q f) := by
  unfold finiteSupportGowersNorm
  rw [← restrictedGowersNorm_imageExtension_pow hφ]
  exact Real.pow_rpow_inv_natCast (restrictedGowersNorm_nonneg j _ _)
    (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))

theorem norm_supportedCubeSum_le_of_embedding {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) (F : (Fin (j + 1) → Bool) → A → ℂ) :
    ‖supportedCubeSum (j + 1) (Q : Set A) F‖ /
        Nat.card (SupportedCube (j + 1) (Q : Set A)) ≤
      ∏ ω, finiteSupportGowersNorm (j + 1) Q (F ω) := by
  have h := norm_mixedGowersMoment_restrict_le j (Q.image φ)
    (fun ω ↦ imageExtension φ Q (F ω))
  simp only [restrictTo_imageExtension, mixedGowersMoment_imageExtension hφ,
    norm_div, norm_pow, Complex.norm_natCast, gowersMoment_indicator_re,
    ← card_supportedCube_image hφ, ← finiteSupportGowersNorm_eq_restricted hφ] at h
  rwa [div_div_div_cancel_right₀
    (pow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero : (Fintype.card B : ℝ) ≠ 0))] at h

theorem finiteSupportGowersNorm_degree_one_of_embedding {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (hQ : Q.Nonempty) (f : A → ℂ) :
    finiteSupportGowersNorm 1 Q f = ‖𝔼 x ∈ Q, f x‖ := by
  classical
  rw [finiteSupportGowersNorm_eq_restricted hφ 0,
    restrictedGowersNorm_degree_one (hQ.image φ)]
  simp only [Finset.expect_eq_sum_div_card]
  rw [Finset.card_image_of_injOn hφ.injOn, Finset.sum_image]
  · congr 2
    apply Finset.sum_congr rfl
    intro x hx
    exact imageExtension_apply hφ.injOn f hx
  · exact hφ.injOn

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

theorem ReflectsPairSums.mono {φ : A →+ B} {Q R : Set A}
    (hφ : ReflectsPairSums φ Q) (hRQ : R ⊆ Q) : ReflectsPairSums φ R := by
  intro a ha b hb c hc d hd he
  exact hφ a (hRQ ha) b (hRQ hb) c (hRQ hc) d (hRQ hd) he

theorem card_supportedCube_pos (j : ℕ) {Q : Finset A} (hQ : Q.Nonempty) :
    0 < Nat.card (SupportedCube j (Q : Set A)) := by
  obtain ⟨a, ha⟩ := hQ
  let : Nonempty (SupportedCube j (Q : Set A)) :=
    ⟨⟨((fun _ ↦ 0), a), fun ω ↦ by simpa [cubeShift] using ha⟩⟩
  exact Nat.card_pos

variable [DecidableEq A]

variable [Fintype B] [DecidableEq B]

omit [DecidableEq A] in
theorem finiteSupportGowersNorm_pow_mul_count {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (hQ : Q.Nonempty) (j : ℕ) (f : A → ℂ) :
    (Nat.card (SupportedCube (j + 1) (Q : Set A)) : ℝ) *
        finiteSupportGowersNorm (j + 1) Q f ^ (2 ^ (j + 1)) =
      (supportedCubeSum (j + 1) (Q : Set A) (fun _ ↦ f)).re := by
  rw [finiteSupportGowersNorm_eq_restricted hφ, restrictedGowersNorm_imageExtension_pow hφ]
  have hC : (Nat.card (SupportedCube (j + 1) (Q : Set A)) : ℝ) ≠ 0 := by
    exact_mod_cast (card_supportedCube_pos (j + 1) hQ).ne'
  field_simp

theorem finiteSupportGowersNorm_derivative_mul_count {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (hQ : Q.Nonempty) (j : ℕ) (f : A → ℂ) :
    (Nat.card (SupportedCube (j + 2) (Q : Set A)) : ℝ) *
        finiteSupportGowersNorm (j + 2) Q f ^ (2 ^ (j + 2)) =
      ∑ h ∈ cubeDifferenceSupport Q,
        (Nat.card (SupportedCube (j + 1) (derivativeSupport Q h : Set A)) : ℝ) *
          finiteSupportGowersNorm (j + 1) (derivativeSupport Q h)
            (multiplicativeDerivative f h) ^ (2 ^ (j + 1)) := by
  rw [finiteSupportGowersNorm_pow_mul_count hφ hQ]
  have he := congrArg Complex.re (supportedCubeSum_derivative (j + 1) Q (fun _ ↦ f))
  simp only [crossDerivative_self, Complex.re_sum] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro h hh
  have hφh : ReflectsPairSums φ (derivativeSupport Q h : Set A) :=
    hφ.mono (fun _ hx ↦ (Finset.mem_filter.mp hx).1)
  exact (finiteSupportGowersNorm_pow_mul_count hφh
    ((mem_cubeDifferenceSupport Q h).mp hh) j (multiplicativeDerivative f h)).symm

theorem finiteSupportGowersNorm_derivative {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (hQ : Q.Nonempty) (j : ℕ) (f : A → ℂ) :
    finiteSupportGowersNorm (j + 2) Q f ^ (2 ^ (j + 2)) =
      ∑ h ∈ cubeDifferenceSupport Q,
        ((Nat.card (SupportedCube (j + 1) (derivativeSupport Q h : Set A)) : ℝ) /
          Nat.card (SupportedCube (j + 2) (Q : Set A))) *
          finiteSupportGowersNorm (j + 1) (derivativeSupport Q h)
            (multiplicativeDerivative f h) ^ (2 ^ (j + 1)) := by
  have hC : (Nat.card (SupportedCube (j + 2) (Q : Set A)) : ℝ) ≠ 0 := by
    exact_mod_cast (card_supportedCube_pos (j + 2) hQ).ne'
  calc
    _ = ((Nat.card (SupportedCube (j + 2) (Q : Set A)) : ℝ) *
        finiteSupportGowersNorm (j + 2) Q f ^ (2 ^ (j + 2))) /
          Nat.card (SupportedCube (j + 2) (Q : Set A)) := by field_simp
    _ = _ := by
      rw [finiteSupportGowersNorm_derivative_mul_count hφ hQ, Finset.sum_div]
      simp only [div_mul_eq_mul_div]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CubeTranslation
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] [DecidableEq A]

def translateSupport (a : A) (Q : Finset A) : Finset A := Q.image (fun x ↦ a + x)

theorem mem_translateSupport (a : A) (Q : Finset A) (x : A) :
    x ∈ translateSupport a Q ↔ x - a ∈ Q := by
  rw [translateSupport, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨x - a, hx, by abel⟩

theorem card_translateSupport (a : A) (Q : Finset A) : (translateSupport a Q).card = Q.card :=
  Finset.card_image_of_injective Q (fun _ _ h ↦ add_left_cancel h)

def supportedCubeTranslateEquiv (j : ℕ) (Q : Finset A) (a : A) :
    SupportedCube j (Q : Set A) ≃ SupportedCube j (translateSupport a Q : Set A) where
  toFun p := ⟨(p.val.1, a + p.val.2), fun ω ↦ by
    apply (mem_translateSupport a Q _).mpr
    simpa only [Finset.mem_coe, add_sub_cancel_left, add_assoc, add_sub_cancel_right] using p.property ω⟩
  invFun p := ⟨(p.val.1, p.val.2 - a), fun ω ↦ by
    have h := (mem_translateSupport a Q _).mp (p.property ω)
    simpa only [Finset.mem_coe, sub_add_eq_add_sub] using h⟩
  left_inv p := by
    apply Subtype.ext
    change (p.val.1, (a + p.val.2) - a) = p.val
    apply Prod.ext
    · rfl
    · simp
  right_inv p := by
    apply Subtype.ext
    change (p.val.1, a + (p.val.2 - a)) = p.val
    apply Prod.ext
    · rfl
    · simp

theorem card_supportedCube_translate (j : ℕ) (Q : Finset A) (a : A) :
    Nat.card (SupportedCube j (translateSupport a Q : Set A)) =
      Nat.card (SupportedCube j (Q : Set A)) :=
  (Nat.card_congr (supportedCubeTranslateEquiv j Q a)).symm

theorem ReflectsPairSums.translate {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (a : A) :
    ReflectsPairSums φ (translateSupport a Q : Set A) := by
  intro b hb c hc d hd e he hrel
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp he
  simp only [map_add] at hrel
  have hr : φ x + φ y = φ z + φ w := by
    apply add_left_cancel (a := φ a + φ a)
    calc
      _ = (φ a + φ x) + (φ a + φ y) := by abel
      _ = (φ a + φ z) + (φ a + φ w) := hrel
      _ = _ := by abel
  have hsum := hφ x hx y hy z hz w hw hr
  calc
    (a + x) + (a + y) = (a + a) + (x + y) := by abel
    _ = (a + a) + (z + w) := by rw [hsum]
    _ = _ := by abel

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FiniteSpectrumCutoff
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def spectrumTail {K : Type*} [Fintype K] [DecidableEq K]
    (S : Finset K) (f : K → ℝ) : ℝ := ∑ k, if k ∈ S then 0 else f k

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

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FiniteFourierSmoothing
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

noncomputable def finiteFourierCoeff (f : H → ℂ) (χ : AddChar H ℂ) : ℂ :=
  𝔼 x, f x * star (χ x)

theorem addChar_sub_star (χ : AddChar H ℂ) (x y : H) :
    χ (x - y) = χ x * star (χ y) := by
  rw [AddChar.map_sub_eq_div, div_eq_mul_inv, AddChar.inv_apply_eq_conj]
  rfl

theorem star_finiteFourierCoeff (f : H → ℂ) (χ : AddChar H ℂ) :
    star (finiteFourierCoeff f χ) = 𝔼 x, star (f x) * χ x := by
  rw [finiteFourierCoeff, ← expect_star]
  apply Finset.expect_congr rfl
  intro x _
  simp only [star_mul, star_star]
  ring

theorem finiteFourier_inversion (f : H → ℂ) (x : H) :
    (∑ χ : AddChar H ℂ, finiteFourierCoeff f χ * χ x) = f x := by
  classical
  calc
    _ = 𝔼 y, f y * (∑ χ : AddChar H ℂ, χ (x - y)) := by
      simp only [finiteFourierCoeff, Finset.expect_mul]
      rw [← Finset.expect_sum_comm]
      apply Finset.expect_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      rw [addChar_sub_star]
      ring
    _ = 𝔼 y, if x = y then (Fintype.card H : ℂ) * f x else 0 := by
      apply Finset.expect_congr rfl
      intro y _
      rw [AddChar.sum_apply_eq_ite]
      by_cases hxy : x = y
      · subst y
        simp [mul_comm]
      · simp [sub_eq_zero, hxy]
    _ = _ := by
      have hc : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      rw [Fintype.expect_eq_sum_div_card, Finset.sum_eq_single x]
      · simp [hc]
      · intro y _ hy
        simp only [if_neg (Ne.symm hy)]
      · simp

theorem finiteFourier_inner (f g : H → ℂ) :
    (∑ χ : AddChar H ℂ, finiteFourierCoeff f χ * star (finiteFourierCoeff g χ)) =
      𝔼 x, f x * star (g x) := by
  simp_rw [star_finiteFourierCoeff, Finset.mul_expect]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro x _
  calc
    _ = (∑ χ : AddChar H ℂ, finiteFourierCoeff f χ * χ x) * star (g x) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ _
      ring
    _ = _ := by rw [finiteFourier_inversion]

theorem finiteFourier_parseval (f : H → ℂ) :
    (∑ χ : AddChar H ℂ, ‖finiteFourierCoeff f χ‖ ^ 2) = 𝔼 x, ‖f x‖ ^ 2 := by
  have h := congrArg Complex.re (finiteFourier_inner f f)
  simpa only [Complex.re_sum, expect_re, mul_star_re_eq_norm_sq] using h

end Erdos3

end

section

open Finset
open scoped BigOperators

namespace Erdos3

variable {G : Type*} [Fintype G] [AddCommGroup G]

noncomputable def fourierL1 (f : G → ℂ) : ℝ :=
  ∑ ψ : AddChar G ℂ, ‖finiteFourierCoeff f ψ‖

theorem norm_sub_translate_le_fourier_sum (f : G → ℂ) (t x : G) :
    ‖f (x - t) - f x‖ ≤
      ∑ ψ : AddChar G ℂ,
        ‖finiteFourierCoeff f ψ‖ * ‖ψ (-t) - 1‖ := by
  classical
  rw [← finiteFourier_inversion f (x - t),
    ← finiteFourier_inversion f x, ← Finset.sum_sub_distrib]
  calc
    ‖∑ ψ : AddChar G ℂ,
        (finiteFourierCoeff f ψ * ψ (x - t) -
          finiteFourierCoeff f ψ * ψ x)‖
        ≤ ∑ ψ : AddChar G ℂ,
            ‖finiteFourierCoeff f ψ * ψ (x - t) -
              finiteFourierCoeff f ψ * ψ x‖ :=
          norm_sum_le _ _
    _ = ∑ ψ : AddChar G ℂ,
          ‖finiteFourierCoeff f ψ‖ * ‖ψ (-t) - 1‖ := by
      apply sum_congr rfl
      intro ψ _
      have hfactor :
          finiteFourierCoeff f ψ * ψ (x - t) -
              finiteFourierCoeff f ψ * ψ x =
            (finiteFourierCoeff f ψ * ψ x) * (ψ (-t) - 1) := by
        have hmap : ψ (x - t) = ψ x * ψ (-t) := by
          rw [sub_eq_add_neg, ψ.map_add_eq_mul]
        rw [hmap]
        ring
      rw [hfactor, norm_mul, norm_mul, AddChar.norm_apply, mul_one]

omit [Fintype G] in

lemma norm_character_neg_sub_one [Finite G] (psi : AddChar G ℂ) (t : G) :
    ‖psi (-t) - 1‖ = ‖1 - psi t‖ := by
  rw [psi.map_neg_eq_inv]
  have hne : psi t ≠ 0 := by
    intro h
    have := AddChar.norm_apply psi t
    simp [h] at this
  calc
    ‖(psi t)⁻¹ - 1‖ = ‖(psi t)⁻¹ * (1 - psi t)‖ := by
      congr 1
      field_simp
    _ = ‖1 - psi t‖ := by
      rw [norm_mul, norm_inv, AddChar.norm_apply, inv_one, one_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteImageMass {X H : Type*} [Fintype X] [DecidableEq H]
    (p : FiniteProbabilityWeights X) (Y : X → H) (z : H) : ℝ :=
  p.mean (fun x => if Y x = z then 1 else 0)

noncomputable def finiteImageCharacteristic {X H : Type*} [Fintype X] [AddCommGroup H]
    (p : FiniteProbabilityWeights X) (Y : X → H) (χ : AddChar H ℂ) : ℂ :=
  p.complexMean (fun x => χ (Y x))

end Erdos3

end

section

open Finset Function Real
open scoped BigOperators ComplexConjugate NNReal

namespace Erdos3.Chang

variable {G : Type*} [Fintype G] [AddCommGroup G]

noncomputable def spectrumSum (A : Finset G) (psi : AddChar G ℂ) : ℂ :=
  ∑ x ∈ A, psi x

noncomputable def largeSpectrum (A : Finset G) (eta : ℝ) : Finset (AddChar G ℂ) :=
  Finset.univ.filter fun psi ↦ eta * A.card ≤ ‖spectrumSum A psi‖

@[simp]
theorem mem_largeSpectrum {A : Finset G} {eta : ℝ} {psi : AddChar G ℂ} :
    psi ∈ largeSpectrum A eta ↔ eta * A.card ≤ ‖spectrumSum A psi‖ := by
  simp [largeSpectrum]

end Erdos3.Chang

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

noncomputable def additiveCharacterKernel (χ : AddChar G ℂ) : AddSubgroup G where
  carrier := {x | χ x = 1}
  zero_mem' := χ.map_zero_eq_one
  add_mem' := by
    intro x y hx hy
    change χ (x + y) = 1
    rw [AddChar.map_add_eq_mul, hx, hy, one_mul]
  neg_mem' := by
    intro x hx
    change χ (-x) = 1
    rw [AddChar.map_neg_eq_inv, hx, inv_one]

variable [Fintype G]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def finiteSetAverage (A : Finset G) (f : G → ℂ) (x : G) : ℂ :=
  𝔼 a ∈ A, f (x - a)

noncomputable def setFourierMultiplier (A : Finset G) (psi : AddChar G ℂ) : ℂ :=
  𝔼 a ∈ A, star (psi a)

theorem finiteFourierCoeff_translate (f : G → ℂ) (a : G) (psi : AddChar G ℂ) :
    finiteFourierCoeff (fun x => f (x - a)) psi = star (psi a) * finiteFourierCoeff f psi := by
  unfold finiteFourierCoeff
  calc
    (𝔼 x, f (x - a) * star (psi x)) = 𝔼 x, f x * star (psi (x + a)) := by
      apply Fintype.expect_equiv (Equiv.subRight a)
      intro x
      simp
    _ = star (psi a) * 𝔼 x, f x * star (psi x) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      rw [AddChar.map_add_eq_mul, star_mul]
      ring

theorem finiteFourierCoeff_finiteSetAverage
    (A : Finset G) (f : G → ℂ) (psi : AddChar G ℂ) :
    finiteFourierCoeff (finiteSetAverage A f) psi =
      setFourierMultiplier A psi * finiteFourierCoeff f psi := by
  unfold finiteFourierCoeff finiteSetAverage
  simp_rw [Finset.expect_mul]
  rw [Finset.expect_comm]
  change (𝔼 a ∈ A, finiteFourierCoeff (fun x => f (x - a)) psi) = _
  simp_rw [finiteFourierCoeff_translate]
  rw [← Finset.expect_mul]
  rfl

omit [Fintype G] in
theorem setFourierMultiplier_eq (A : Finset G) (psi : AddChar G ℂ) :
    setFourierMultiplier A psi = star (Chang.spectrumSum A psi) / (A.card : ℂ) := by
  simp only [setFourierMultiplier, Finset.expect_eq_sum_div_card, Chang.spectrumSum, star_sum]

omit [Fintype G] in
theorem norm_setFourierMultiplier (A : Finset G) (psi : AddChar G ℂ) :
    ‖setFourierMultiplier A psi‖ = ‖Chang.spectrumSum A psi‖ / A.card := by
  rw [setFourierMultiplier_eq, norm_div, norm_star, Complex.norm_natCast]

theorem norm_setFourierMultiplier_le_one {A : Finset G} (hA : A.Nonempty)
    (psi : AddChar G ℂ) : ‖setFourierMultiplier A psi‖ ≤ 1 := by
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  simp only [norm_star, AddChar.norm_apply, Finset.expect_const hA]
  exact le_rfl

theorem mem_largeSpectrum_iff_le_multiplier {A : Finset G} (hA : A.Nonempty)
    (eta : ℝ) (psi : AddChar G ℂ) :
    psi ∈ Chang.largeSpectrum A eta ↔ eta ≤ ‖setFourierMultiplier A psi‖ := by
  have hcard : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  rw [Chang.mem_largeSpectrum, norm_setFourierMultiplier, le_div_iff₀ hcard]

noncomputable def iteratedFiniteSetAverage (A : Finset G) (f : G → ℂ) : ℕ → G → ℂ
  | 0 => f
  | n + 1 => finiteSetAverage A (iteratedFiniteSetAverage A f n)

theorem finiteFourierCoeff_iteratedFiniteSetAverage
    (A : Finset G) (f : G → ℂ) (psi : AddChar G ℂ) (n : ℕ) :
    finiteFourierCoeff (iteratedFiniteSetAverage A f n) psi =
      setFourierMultiplier A psi ^ n * finiteFourierCoeff f psi := by
  induction n with
  | zero => simp [iteratedFiniteSetAverage]
  | succ n ih =>
      rw [iteratedFiniteSetAverage, finiteFourierCoeff_finiteSetAverage, ih, pow_succ]
      ring

end Erdos3

end

section

noncomputable section

open Finset Function Real
open scoped BigOperators ComplexConjugate NNReal

namespace Erdos3.RelativeChangSanders

variable {G : Type*} [Fintype G] [AddCommGroup G]

def IsWeightedDissociated (mu : G → ℝ) (K : ℝ)
    (Delta : Finset (AddChar G ℂ)) : Prop :=
  ∀ u : AddChar G ℂ → ℂ,
    (∀ psi ∈ Delta, ‖u psi‖ ≤ 1) →
      ∑ x : G, mu x *
        ∏ psi ∈ Delta, (1 + (u psi * psi x).re) ≤ exp K

def relativeLargeSpectrum (mu f : G → ℝ) (eta : ℝ) :
    Finset (AddChar G ℂ) :=
    Finset.univ.filter fun psi ↦
    eta * (∑ x : G, f x * mu x) ≤
      ‖∑ x : G, (f x * mu x : ℝ) * psi x‖

@[simp] theorem mem_relativeLargeSpectrum {mu f : G → ℝ} {eta : ℝ}
    {psi : AddChar G ℂ} :
    psi ∈ relativeLargeSpectrum mu f eta ↔
      eta * (∑ x : G, f x * mu x) ≤
        ‖∑ x : G, (f x * mu x : ℝ) * psi x‖ := by
  simp [relativeLargeSpectrum]

end Erdos3.RelativeChangSanders

end

end

section

namespace Erdos3.Chang

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

omit [Fintype G] in
theorem spectrumSum_map_subRight (T : Finset G) (z : G) (psi : AddChar G ℂ) :
    spectrumSum (T.map (Equiv.subRight z).toEmbedding) psi =
      spectrumSum T psi * psi (-z) := by
  unfold spectrumSum
  rw [Finset.sum_map]
  simp only [Equiv.toEmbedding_apply, Equiv.subRight_apply,
    sub_eq_add_neg, AddChar.map_add_eq_mul]
  rw [Finset.sum_mul]

theorem norm_spectrumSum_map_subRight (T : Finset G) (z : G) (psi : AddChar G ℂ) :
    ‖spectrumSum (T.map (Equiv.subRight z).toEmbedding) psi‖ = ‖spectrumSum T psi‖ := by
  rw [spectrumSum_map_subRight, norm_mul, AddChar.norm_apply, mul_one]

theorem mem_largeSpectrum_map_subRight_iff
    (T : Finset G) (z : G) (eta : ℝ) (psi : AddChar G ℂ) :
    psi ∈ largeSpectrum (T.map (Equiv.subRight z).toEmbedding) eta ↔
      psi ∈ largeSpectrum T eta := by
  rw [mem_largeSpectrum, mem_largeSpectrum, Finset.card_map, norm_spectrumSum_map_subRight]

end Erdos3.Chang

end

section

open scoped BigOperators

namespace Erdos3

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem iteratedFiniteSetAverage_translate_le
    {X : Finset G} (hX : X.Nonempty) (m : ℕ) (f : G → ℂ)
    {eta theta : ℝ} (heta : 0 ≤ eta) (htheta : 0 ≤ theta) (t x : G)
    (hphase : ∀ psi ∈ Chang.largeSpectrum X eta, ‖1 - psi t‖ ≤ theta) :
    ‖iteratedFiniteSetAverage X f m (x - t) - iteratedFiniteSetAverage X f m x‖ ≤
      (theta + 2 * eta ^ m) * fourierL1 f := by
  apply (norm_sub_translate_le_fourier_sum (iteratedFiniteSetAverage X f m) t x).trans
  calc
    (∑ psi : AddChar G ℂ,
        ‖finiteFourierCoeff (iteratedFiniteSetAverage X f m) psi‖ * ‖psi (-t) - 1‖) ≤
        ∑ psi : AddChar G ℂ, (theta + 2 * eta ^ m) * ‖finiteFourierCoeff f psi‖ := by
      apply Finset.sum_le_sum
      intro psi _
      rw [finiteFourierCoeff_iteratedFiniteSetAverage, norm_mul, norm_pow,
        norm_character_neg_sub_one]
      have hmu := norm_setFourierMultiplier_le_one hX psi
      by_cases hlarge : eta ≤ ‖setFourierMultiplier X psi‖
      · have hpow : ‖setFourierMultiplier X psi‖ ^ m ≤ 1 :=
          pow_le_one₀ (norm_nonneg _) hmu
        have hp := hphase psi ((mem_largeSpectrum_iff_le_multiplier hX eta psi).2 hlarge)
        calc
          ‖setFourierMultiplier X psi‖ ^ m * ‖finiteFourierCoeff f psi‖ * ‖1 - psi t‖ ≤
              1 * ‖finiteFourierCoeff f psi‖ * theta := by gcongr
          _ ≤ (theta + 2 * eta ^ m) * ‖finiteFourierCoeff f psi‖ := by
            have hepow : 0 ≤ eta ^ m := pow_nonneg heta m
            have hf : 0 ≤ ‖finiteFourierCoeff f psi‖ := norm_nonneg _
            nlinarith
      · have htail : ‖setFourierMultiplier X psi‖ ^ m ≤ eta ^ m :=
          pow_le_pow_left₀ (norm_nonneg _) (le_of_not_ge hlarge) m
        have hchord : ‖1 - psi t‖ ≤ 2 := by
          calc
            ‖1 - psi t‖ ≤ ‖(1 : ℂ)‖ + ‖psi t‖ := norm_sub_le _ _
            _ = 2 := by norm_num
        calc
          ‖setFourierMultiplier X psi‖ ^ m * ‖finiteFourierCoeff f psi‖ * ‖1 - psi t‖ ≤
              eta ^ m * ‖finiteFourierCoeff f psi‖ * 2 := by gcongr
          _ ≤ (theta + 2 * eta ^ m) * ‖finiteFourierCoeff f psi‖ := by
            have hf : 0 ≤ ‖finiteFourierCoeff f psi‖ := norm_nonneg _
            nlinarith
    _ = (theta + 2 * eta ^ m) * fourierL1 f := by rw [fourierL1, Finset.mul_sum]

theorem translate_le_of_iteratedFiniteSetAverage_approx
    {X : Finset G} (hX : X.Nonempty) (m : ℕ) (f : G → ℂ)
    {delta eta theta : ℝ} (heta : 0 ≤ eta) (htheta : 0 ≤ theta) (t x : G)
    (happrox : ∀ y, ‖iteratedFiniteSetAverage X f m y - f y‖ ≤ delta)
    (hphase : ∀ psi ∈ Chang.largeSpectrum X eta, ‖1 - psi t‖ ≤ theta) :
    ‖f (x - t) - f x‖ ≤ 2 * delta + (theta + 2 * eta ^ m) * fourierL1 f := by
  let p := iteratedFiniteSetAverage X f m
  have hdecomp : f (x - t) - f x =
      (f (x - t) - p (x - t)) + (p (x - t) - p x) + (p x - f x) := by ring
  rw [hdecomp]
  calc
    ‖(f (x - t) - p (x - t)) + (p (x - t) - p x) + (p x - f x)‖ ≤
        ‖f (x - t) - p (x - t)‖ + ‖p (x - t) - p x‖ + ‖p x - f x‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ delta + ((theta + 2 * eta ^ m) * fourierL1 f) + delta := by
      apply add_le_add
      · apply add_le_add
        · simpa only [norm_sub_rev] using happrox (x - t)
        · exact iteratedFiniteSetAverage_translate_le hX m f heta htheta t x hphase
      · exact happrox x
    _ = 2 * delta + (theta + 2 * eta ^ m) * fourierL1 f := by ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteConvolution
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

noncomputable def finiteConvolution (f g : H → ℂ) (x : H) : ℂ :=
  𝔼 y, f y * g (x - y)

theorem finiteConvolution_fourier_mass_sq (f g : H → ℂ) :
    (∑ χ : AddChar H ℂ, ‖finiteFourierCoeff f χ * finiteFourierCoeff g χ‖) ^ 2 ≤
      (𝔼 x, ‖f x‖ ^ 2) * (𝔼 x, ‖g x‖ ^ 2) := by
  simp only [norm_mul]
  rw [← finiteFourier_parseval, ← finiteFourier_parseval]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicCutNeighborhood
namespace OAI

section

namespace Erdos3

theorem exists_smoothing_scale {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ K : ℕ, 0 < K ∧ K ≤ N ∧ ((K - 1 : ℕ) : ℝ) ≤ δ * N ∧
      (N : ℝ) / K ≤ 2 / δ := by
  let K := max 1 ⌊δ * N⌋₊
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hfloor : (⌊δ * N⌋₊ : ℝ) ≤ δ * N := Nat.floor_le (by positivity)
  have hfloorN : ⌊δ * N⌋₊ ≤ N := by
    exact_mod_cast hfloor.trans (by nlinarith : δ * N ≤ (N : ℝ))
  have hk : 1 ≤ K := le_max_left _ _
  have hkfloor : ⌊δ * N⌋₊ ≤ K := le_max_right _ _
  have hk1 : (1 : ℝ) ≤ K := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < K := by linarith
  have hfK : (⌊δ * N⌋₊ : ℝ) ≤ K := by exact_mod_cast hkfloor
  have hlt : δ * N < (⌊δ * N⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨K, by omega, max_le (by omega) hfloorN, ?_, ?_⟩
  · have hh : K - 1 ≤ ⌊δ * N⌋₊ := by dsimp [K]; omega
    exact (Nat.cast_le.mpr hh).trans hfloor
  · apply (div_le_div_iff₀ hkpos hδ).mpr
    nlinarith

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

def finiteIndicator (I : Finset H) (x : H) : ℂ := if x ∈ I then 1 else 0

noncomputable def averagingKernel (B : Finset H) (x : H) : ℂ :=
  (Fintype.card H : ℂ) / B.card * finiteIndicator B x

noncomputable def smoothedIndicator (I B : Finset H) (x : H) : ℂ :=
  𝔼 h ∈ B, finiteIndicator I (x - h)

omit [AddCommGroup H] [Fintype H] in
theorem finiteIndicator_norm_le_one (I : Finset H) (x : H) : ‖finiteIndicator I x‖ ≤ 1 := by
  simp only [finiteIndicator]
  split_ifs <;> norm_num

omit [Fintype H] in
theorem smoothedIndicator_norm_le_one (I : Finset H) {B : Finset H} (hB : B.Nonempty) (x : H) :
    ‖smoothedIndicator I B x‖ ≤ 1 := by
  exact (RCLike.norm_expect_le (K := ℂ)).trans
    ((Finset.expect_le_expect (fun h _ => finiteIndicator_norm_le_one I (x - h))).trans_eq
      (Finset.expect_const hB 1))

theorem smoothedIndicator_eq_convolution (I B : Finset H) (x : H) :
    smoothedIndicator I B x = finiteConvolution (averagingKernel B) (finiteIndicator I) x := by
  have hn : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : (fun h => averagingKernel B h * finiteIndicator I (x - h)) =
      (fun h => ((Fintype.card H : ℂ) / B.card) * restrictTo B (fun h => finiteIndicator I (x - h)) h) := by
    funext h
    by_cases hh : h ∈ B <;> simp [averagingKernel, finiteIndicator, restrictTo, hh]
  rw [finiteConvolution, he, ← Finset.mul_expect, expect_restrictTo,
    smoothedIndicator, Finset.expect_eq_sum_div_card]
  by_cases hb : (B.card : ℂ) = 0
  · simp [hb]
  · field_simp

omit [AddCommGroup H] in
theorem mean_indicator_norm_sq (I : Finset H) :
    (𝔼 x, ‖finiteIndicator I x‖ ^ 2) = (I.card : ℝ) / Fintype.card H := by
  have he (x : H) : ‖finiteIndicator I x‖ ^ 2 = if x ∈ I then (1 : ℝ) else 0 := by
    by_cases hx : x ∈ I <;> simp [finiteIndicator, hx]
  simp only [he, Fintype.expect_eq_sum_div_card]
  simp

theorem mean_averagingKernel_norm_sq {B : Finset H} (hB : B.Nonempty) :
    (𝔼 x, ‖averagingKernel B x‖ ^ 2) = (Fintype.card H : ℝ) / B.card := by
  have hn : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hb : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
  simp only [averagingKernel, norm_mul, norm_div, Complex.norm_natCast, mul_pow]
  rw [← Finset.mul_expect, mean_indicator_norm_sq]
  field_simp

theorem smoothedIndicator_fourier_mass {B : Finset H} (hB : B.Nonempty) (I : Finset H) :
    (∑ χ : AddChar H ℂ, ‖finiteFourierCoeff (averagingKernel B) χ * finiteFourierCoeff (finiteIndicator I) χ‖) ≤
      (Fintype.card H : ℝ) / B.card := by
  let M := ∑ χ : AddChar H ℂ,
    ‖finiteFourierCoeff (averagingKernel B) χ * finiteFourierCoeff (finiteIndicator I) χ‖
  have hn : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hb : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hm : M ^ 2 ≤ (I.card : ℝ) / B.card := by
    have hh := finiteConvolution_fourier_mass_sq (averagingKernel B) (finiteIndicator I)
    rw [mean_averagingKernel_norm_sq hB, mean_indicator_norm_sq] at hh
    calc
      _ ≤ ((Fintype.card H : ℝ) / B.card) * ((I.card : ℝ) / Fintype.card H) := hh
      _ = _ := by field_simp
  have hi : (I.card : ℝ) ≤ Fintype.card H := by exact_mod_cast Finset.card_le_univ I
  have hbr : (B.card : ℝ) ≤ Fintype.card H := by exact_mod_cast Finset.card_le_univ B
  have hR : (1 : ℝ) ≤ (Fintype.card H : ℝ) / B.card := (le_div_iff₀ hb).mpr (by simpa using hbr)
  have hm' := hm.trans (div_le_div_of_nonneg_right hi hb.le)
  change M ≤ _
  nlinarith [sq_nonneg ((Fintype.card H : ℝ) / B.card - 1)]

end Erdos3

end

section

open scoped BigOperators symmDiff

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

omit [AddCommGroup H] in
theorem mean_finiteIndicator_difference (I J : Finset H) :
    (𝔼 x, ‖finiteIndicator I x - finiteIndicator J x‖) =
      ((I ∆ J).card : ℝ) / Fintype.card H := by
  have he (x : H) : ‖finiteIndicator I x - finiteIndicator J x‖ =
      if x ∈ I ∆ J then (1 : ℝ) else 0 := by
    by_cases hi : x ∈ I <;> by_cases hj : x ∈ J <;>
      simp [finiteIndicator, Finset.mem_symmDiff, hi, hj]
  simp only [he, Fintype.expect_eq_sum_div_card]
  simp

theorem mean_indicator_smoothing_error (I : Finset H) {B : Finset H} (hB : B.Nonempty)
    {ε : ℝ} (hshift : ∀ h ∈ B, (𝔼 x, ‖finiteIndicator I x - finiteIndicator I (x - h)‖) ≤ ε) :
    (𝔼 x, ‖finiteIndicator I x - smoothedIndicator I B x‖) ≤ ε := by
  have hpoint (x : H) : ‖finiteIndicator I x - smoothedIndicator I B x‖ ≤
      𝔼 h ∈ B, ‖finiteIndicator I x - finiteIndicator I (x - h)‖ := by
    have he : finiteIndicator I x - smoothedIndicator I B x =
        𝔼 h ∈ B, (finiteIndicator I x - finiteIndicator I (x - h)) := by
      rw [Finset.expect_sub_distrib, Finset.expect_const hB]
      rfl
    rw [he]
    exact RCLike.norm_expect_le (K := ℂ)
  calc
    _ ≤ 𝔼 x, 𝔼 h ∈ B, ‖finiteIndicator I x - finiteIndicator I (x - h)‖ :=
      Finset.expect_le_expect (fun x _ => hpoint x)
    _ = 𝔼 h ∈ B, 𝔼 x, ‖finiteIndicator I x - finiteIndicator I (x - h)‖ := Finset.expect_comm _ _ _
    _ ≤ 𝔼 _h ∈ B, ε := Finset.expect_le_expect hshift
    _ = ε := Finset.expect_const hB ε

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {H K : Type*} [AddCommGroup H] [Fintype H]
    [AddCommGroup K] [Fintype K] [DecidableEq K]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem finiteCorrelation_mul_indicator (I : Finset H) (f u : H → ℂ) :
    finiteCorrelation Finset.univ f (fun x => u x * finiteIndicator I x) =
      ((I.card : ℂ) / Fintype.card H) * finiteCorrelation I f u := by
  have he : (fun x => f x * star (u x * finiteIndicator I x)) =
      restrictTo I (fun x => f x * star (u x)) := by
    funext x
    by_cases hx : x ∈ I <;> simp [finiteIndicator, restrictTo, hx]
  unfold finiteCorrelation
  rw [he, expect_restrictTo, Finset.expect_eq_sum_div_card]
  by_cases hI : I.card = 0
  · simp [Finset.card_eq_zero.mp hI]
  · have hi : (I.card : ℂ) ≠ 0 := by exact_mod_cast hI
    have hn : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp

theorem norm_finiteCorrelation_mul_indicator (I : Finset H) (f u : H → ℂ) :
    ‖finiteCorrelation Finset.univ f (fun x => u x * finiteIndicator I x)‖ =
      ((I.card : ℝ) / Fintype.card H) * ‖finiteCorrelation I f u‖ := by
  rw [finiteCorrelation_mul_indicator, norm_mul, norm_div]
  simp only [Complex.norm_natCast]

theorem retained_restricted_correlation (I : Finset H) (f u : H → ℂ)
    {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 < B)
    (hf : ∀ x ∈ I, ‖f x‖ ≤ 1) (hu : ∀ x ∈ I, ‖u x‖ ≤ B)
    (hc : ρ ≤ ‖finiteCorrelation Finset.univ f (fun x => u x * finiteIndicator I x)‖) :
    I.Nonempty ∧ ρ ≤ ‖finiteCorrelation I f u‖ ∧
      ρ / B ≤ (I.card : ℝ) / Fintype.card H := by
  rw [norm_finiteCorrelation_mul_indicator] at hc
  have hI : I.Nonempty := by
    by_contra he
    rw [Finset.not_nonempty_iff_eq_empty.mp he] at hc
    simp only [Finset.card_empty, Nat.cast_zero, zero_div, zero_mul] at hc
    linarith
  have hv0 : 0 ≤ (I.card : ℝ) / Fintype.card H := by positivity
  have hv1 : (I.card : ℝ) / Fintype.card H ≤ 1 := by
    apply (div_le_one (by exact_mod_cast Fintype.card_pos)).mpr
    exact_mod_cast Finset.card_le_univ I
  have hb := norm_finiteCorrelation_le hI f u hf hu
  refine ⟨hI, hc.trans ?_, (div_le_iff₀ hB).mpr ?_⟩
  · exact (mul_le_mul_of_nonneg_right hv1 (norm_nonneg _)).trans_eq (one_mul _)
  · exact hc.trans (mul_le_mul_of_nonneg_left hb hv0)

end Erdos3

end

section

open scoped BigOperators symmDiff

namespace Erdos3

variable {N : ℕ}

def cyclicInterval (a : ZMod N) (L : ℕ) : Finset (ZMod N) :=
  (Finset.range L).image (fun k : ℕ => a + (k : ZMod N))

theorem mem_cyclicInterval_shift (a t x : ZMod N) (L : ℕ) :
    x - t ∈ cyclicInterval a L ↔ x ∈ cyclicInterval (a + t) L := by
  simp only [cyclicInterval, Finset.mem_image]
  constructor
  · rintro ⟨k, hk, he⟩
    refine ⟨k, hk, ?_⟩
    calc
      a + t + k = (a + k) + t := by ring
      _ = x := by rw [he]; ring
  · rintro ⟨k, hk, he⟩
    refine ⟨k, hk, ?_⟩
    rw [← he]
    ring

theorem cyclicInterval_sdiff_next (a : ZMod N) (L : ℕ) :
    cyclicInterval a L \ cyclicInterval (a + 1) L ⊆ {a} := by
  intro x hx
  obtain ⟨hx, hn⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
  have hk' := Finset.mem_range.mp hk
  cases k with
  | zero => simp
  | succ k =>
    exfalso
    apply hn
    refine Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), ?_⟩
    push_cast
    ring

theorem cyclicInterval_next_sdiff (a : ZMod N) (L : ℕ) :
    cyclicInterval (a + 1) L \ cyclicInterval a L ⊆ {a + L} := by
  intro x hx
  obtain ⟨hx, hn⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
  have hk' := Finset.mem_range.mp hk
  by_cases hnext : k + 1 < L
  · exfalso
    apply hn
    refine Finset.mem_image.mpr ⟨k + 1, Finset.mem_range.mpr hnext, ?_⟩
    push_cast
    ring
  · have he : L = k + 1 := by omega
    apply Finset.mem_singleton.mpr
    rw [he]
    push_cast
    ring

theorem card_cyclicInterval_symmDiff_next (a : ZMod N) (L : ℕ) :
    (cyclicInterval a L ∆ cyclicInterval (a + 1) L).card ≤ 2 := by
  rw [Finset.symmDiff_def]
  calc
    _ ≤ (cyclicInterval a L \ cyclicInterval (a + 1) L).card +
        (cyclicInterval (a + 1) L \ cyclicInterval a L).card := Finset.card_union_le _ _
    _ ≤ ({a} : Finset (ZMod N)).card + ({a + L} : Finset (ZMod N)).card :=
      Nat.add_le_add (Finset.card_le_card (cyclicInterval_sdiff_next a L))
        (Finset.card_le_card (cyclicInterval_next_sdiff a L))
    _ = 2 := by simp

theorem cyclicInterval_unit_shift_error [NeZero N] (a : ZMod N) (L : ℕ) :
    (𝔼 x, ‖finiteIndicator (cyclicInterval a L) x - finiteIndicator (cyclicInterval a L) (x - 1)‖) ≤
      2 / (N : ℝ) := by
  have he (x : ZMod N) : finiteIndicator (cyclicInterval a L) (x - 1) =
      finiteIndicator (cyclicInterval (a + 1) L) x := by
    simp only [finiteIndicator, mem_cyclicInterval_shift]
  simp only [he]
  rw [mean_finiteIndicator_difference, ZMod.card]
  exact div_le_div_of_nonneg_right (by exact_mod_cast card_cyclicInterval_symmDiff_next a L) (Nat.cast_nonneg N)

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
theorem cyclicInterval_card (a : ZMod N) {L : ℕ} (hL : L ≤ N) :
    (cyclicInterval a L).card = L := by
  unfold cyclicInterval
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj he
  have hiN : i < N := (Finset.mem_range.mp hi).trans_le hL
  have hjN : j < N := (Finset.mem_range.mp hj).trans_le hL
  have hc : (i : ZMod N) = (j : ZMod N) := add_left_cancel he
  have hv := congrArg ZMod.val hc
  simpa only [ZMod.val_natCast_of_lt hiN, ZMod.val_natCast_of_lt hjN] using hv

omit [NeZero N] in
theorem cyclicInterval_nonempty (a : ZMod N) {L : ℕ} (hL : 0 < L) :
    (cyclicInterval a L).Nonempty := by
  refine ⟨a, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hL, ?_⟩⟩
  simp

theorem cyclicInterval_nat_shift_error (a : ZMod N) (L h : ℕ) :
    (𝔼 x, ‖finiteIndicator (cyclicInterval a L) x - finiteIndicator (cyclicInterval a L) (x - h)‖) ≤
      2 * (h : ℝ) / N := by
  let u := finiteIndicator (cyclicInterval a L)
  induction h with
  | zero => simp
  | succ h ih =>
    have he (x : ZMod N) : x - ((h + 1 : ℕ) : ZMod N) = (x - h) - 1 := by
      push_cast
      ring
    have ht : (𝔼 x, ‖u (x - h) - u ((x - h) - 1)‖) = 𝔼 x, ‖u x - u (x - 1)‖ := by
      simpa only [sub_eq_add_neg] using
        (Fintype.expect_equiv (Equiv.addRight (-(h : ZMod N)))
          (fun x => ‖u (x + -(h : ZMod N)) - u ((x + -(h : ZMod N)) - 1)‖)
          (fun x => ‖u x - u (x - 1)‖) (fun _ => rfl))
    change (𝔼 x, ‖u x - u (x - ((h + 1 : ℕ) : ZMod N))‖) ≤ _
    calc
      _ ≤ (𝔼 x, ‖u x - u (x - h)‖) + (𝔼 x, ‖u (x - h) - u ((x - h) - 1)‖) := by
        rw [← Finset.expect_add_distrib]
        apply Finset.expect_le_expect
        intro x _
        rw [he]
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * (h : ℝ) / N + 2 / N := by
        rw [ht]
        exact add_le_add ih (cyclicInterval_unit_shift_error a L)
      _ = _ := by push_cast; ring

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {N : ℕ} [NeZero N]

end Erdos3

end

section

namespace Erdos3

variable {N : ℕ} [NeZero N]

theorem mem_cyclicInterval_representatives (a b : ℕ) (hab : a ≤ b) (hbN : b ≤ N) (x : ZMod N) :
    x ∈ cyclicInterval (a : ZMod N) (b - a) ↔ a ≤ x.val ∧ x.val < b := by
  constructor
  · intro hx
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hx
    have hk' := Finset.mem_range.mp hk
    have hak : a + k < b := by omega
    have he' : ((a + k : ℕ) : ZMod N) = x := by simpa only [Nat.cast_add] using he
    rw [← he', ZMod.val_natCast_of_lt (hak.trans_le hbN)]
    omega
  · intro hx
    refine Finset.mem_image.mpr ⟨x.val - a, Finset.mem_range.mpr (by omega), ?_⟩
    have he : a + (x.val - a) = x.val := Nat.add_sub_of_le hx.1
    calc
      (a : ZMod N) + (x.val - a : ℕ) = ((a + (x.val - a) : ℕ) : ZMod N) := by push_cast; rfl
      _ = x := by rw [he, ZMod.natCast_zmod_val]

end Erdos3

end

section

namespace Erdos3

variable {N : ℕ} [NeZero N]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

variable (N : I → ℕ) [∀ i, NeZero (N i)]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

def quarterLower (N : ℕ) (i : Fin 4) : ℕ := i.val * N / 4

def quarterUpper (N : ℕ) (i : Fin 4) : ℕ := (i.val + 1) * N / 4

def cyclicQuarter (N : ℕ) (i : Fin 4) : Finset (ZMod N) :=
  cyclicInterval (quarterLower N i : ZMod N) (quarterUpper N i - quarterLower N i)

theorem quarter_bounds (N : ℕ) (i : Fin 4) :
    quarterLower N i ≤ quarterUpper N i ∧ quarterUpper N i ≤ N := by
  fin_cases i <;> simp only [quarterLower, quarterUpper] <;> omega

theorem quarter_short (N : ℕ) (hN : 0 < N) (i : Fin 4) :
    2 * ((quarterUpper N i : ℤ) - quarterLower N i - 1) < N := by
  fin_cases i <;> simp only [quarterLower, quarterUpper] <;> omega

theorem quarter_diameter_lt_third (N : ℕ) (hN : 0 < N) (i : Fin 4) :
    3 * ((quarterUpper N i : ℤ) - quarterLower N i - 1) < N := by
  fin_cases i <;> simp only [quarterLower, quarterUpper] <;> omega

theorem mem_cyclicQuarter {N : ℕ} [NeZero N] (i : Fin 4) (x : ZMod N) :
    x ∈ cyclicQuarter N i ↔ quarterLower N i ≤ x.val ∧ x.val < quarterUpper N i :=
  mem_cyclicInterval_representatives _ _ (quarter_bounds N i).1 (quarter_bounds N i).2 x

theorem sum_cyclicQuarter_indicator {N : ℕ} [NeZero N] (x : ZMod N) :
    (∑ i : Fin 4, finiteIndicator (cyclicQuarter N i) x) = 1 := by
  have hx := x.val_lt
  simp only [finiteIndicator, mem_cyclicQuarter, Fin.sum_univ_succ, Fin.sum_univ_zero,
    quarterLower, quarterUpper, Fin.val_zero, Fin.val_succ, add_zero]
  split_ifs <;> norm_num at * <;> omega

end Erdos3

end

section

namespace Erdos3

def cyclicTranslationOffset {N : ℕ} (h : ZMod N) (a : ℕ) : ℤ :=
  (h.val : ℤ) - if N - h.val ≤ a then (N : ℤ) else 0

theorem cyclic_representative_add {N : ℕ} [NeZero N] (h x : ZMod N) :
    ((h + x).val : ℤ) = (x.val : ℤ) + h.val -
      if N - h.val ≤ x.val then (N : ℤ) else 0 := by
  have hh := h.val_lt
  by_cases hw : N - h.val ≤ x.val
  · have he := ZMod.val_add_val_of_le (a := h) (b := x) (by omega)
    rw [if_pos hw]
    omega
  · have he := ZMod.val_add_of_lt (a := h) (b := x) (by omega)
    rw [if_neg hw]
    omega

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (N : I → ℕ) [∀ i, NeZero (N i)]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

noncomputable def cyclicCutNeighborhood (N : ℕ) [NeZero N] (a : ℤ) (δ : ℝ) : Finset (ZMod N) := by
  classical
  exact Finset.univ.filter (fun x => |(x.val : ℝ) - a| ≤ δ)

theorem mem_cyclicCutNeighborhood (N : ℕ) [NeZero N] (a : ℤ) (δ : ℝ) (x : ZMod N) :
    x ∈ cyclicCutNeighborhood N a δ ↔ |(x.val : ℝ) - a| ≤ δ := by
  classical
  simp only [cyclicCutNeighborhood, Finset.mem_filter, Finset.mem_univ, true_and]

theorem cyclicCutNeighborhood_card_le (N : ℕ) [NeZero N] (a : ℤ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ((cyclicCutNeighborhood N a δ).card : ℝ) ≤ 2 * δ + 1 := by
  have hcard : (cyclicCutNeighborhood N a δ).card ≤ (integerAbsInterval δ).card := by
    apply Finset.card_le_card_of_injOn (fun x : ZMod N => (x.val : ℤ) - a)
    · intro x hx
      change (x.val : ℤ) - a ∈ integerAbsInterval δ
      rw [mem_integerAbsInterval]
      simpa only [Int.cast_sub, Int.cast_natCast] using (mem_cyclicCutNeighborhood N a δ x).mp hx
    · intro x _ y _ hxy
      apply ZMod.val_injective N
      have hv : (x.val : ℤ) = (y.val : ℤ) := by dsimp only at hxy; omega
      exact_mod_cast hv
  exact (Nat.cast_le.mpr hcard).trans (integerAbsInterval_card_le δ hδ)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceCountingCost
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem residue_constraints_iff_lcm {M d : ℕ} {u v c : ℤ}
    (hM : c ≡ u [ZMOD (M : ℤ)]) (hd : c ≡ v [ZMOD (d : ℤ)]) (x : ℤ) :
    (x ≡ u [ZMOD (M : ℤ)] ∧ x ≡ v [ZMOD (d : ℤ)]) ↔
      x ≡ c [ZMOD (Nat.lcm M d : ℤ)] := by
  have hlcm : (M : ℤ).lcm (d : ℤ) = Nat.lcm M d := by simp [Int.lcm_def]
  rw [← hlcm, ← Int.modEq_and_modEq_iff_modEq_lcm]
  exact ⟨fun h => ⟨h.1.trans hM.symm, h.2.trans hd.symm⟩,
    fun h => ⟨h.1.trans hM, h.2.trans hd⟩⟩

theorem exists_integer_coprime_residues {M d : ℕ} (hcop : M.Coprime d) (u v : ℤ) :
    ∃ c : ℤ, c ≡ u [ZMOD (M : ℤ)] ∧ c ≡ v [ZMOD (d : ℤ)] := by
  have hbez : (M : ℤ) * Nat.gcdA M d + (d : ℤ) * Nat.gcdB M d = 1 := by
    simpa only [hcop.gcd_eq_one, Nat.cast_one] using (Nat.gcd_eq_gcd_ab M d).symm
  let c := u * ((d : ℤ) * Nat.gcdB M d) + v * ((M : ℤ) * Nat.gcdA M d)
  refine ⟨c, Int.modEq_iff_dvd.mpr ?_, Int.modEq_iff_dvd.mpr ?_⟩
  · refine ⟨(u - v) * Nat.gcdA M d, ?_⟩
    calc
      u - c = u * ((M : ℤ) * Nat.gcdA M d + (d : ℤ) * Nat.gcdB M d) - c := by rw [hbez, mul_one]
      _ = (M : ℤ) * ((u - v) * Nat.gcdA M d) := by dsimp [c]; ring
  · refine ⟨(v - u) * Nat.gcdB M d, ?_⟩
    calc
      v - c = v * ((M : ℤ) * Nat.gcdA M d + (d : ℤ) * Nat.gcdB M d) - c := by rw [hbez, mul_one]
      _ = (d : ℤ) * ((v - u) * Nat.gcdB M d) := by dsimp [c]; ring

theorem coprime_refinement_preserves_compatibility {M d J : ℕ}
    (hcop : (M * d).Coprime J) (u v w : ℤ) :
    (∃ c : ℤ, c ≡ u [ZMOD (M : ℤ)] ∧ c ≡ v [ZMOD (d : ℤ)]) ↔
      ∃ c : ℤ, c ≡ u [ZMOD (M : ℤ)] ∧ c ≡ v [ZMOD (d : ℤ)] ∧ c ≡ w [ZMOD (J : ℤ)] := by
  constructor
  · rintro ⟨c, hM, hd⟩
    have hL : (Nat.lcm M d).Coprime J := hcop.of_dvd_left (Nat.lcm_dvd_mul M d)
    obtain ⟨t, ht, htJ⟩ := exists_integer_coprime_residues hL c w
    obtain ⟨htM, htd⟩ := (residue_constraints_iff_lcm hM hd t).mpr ht
    exact ⟨t, htM, htd, htJ⟩
  · rintro ⟨c, hM, hd, _⟩
    exact ⟨c, hM, hd⟩

end Erdos3

end

section

namespace Erdos3

noncomputable def residueIndexLower (a r v : ℤ) : ℤ :=
  ⌈((a : ℚ) - (v : ℚ)) / (r : ℚ)⌉

noncomputable def residueIndexLength (a b r v : ℤ) : ℕ :=
  (residueIndexLower b r v - residueIndexLower a r v).toNat

def residueAffineEmbedding (r v : ℤ) (hr : r ≠ 0) : ℤ ↪ ℤ where
  toFun k := v + r * k
  inj' _ _ h := mul_left_cancel₀ hr (add_left_cancel h)

theorem residueIndexInterval_eq (a b r v : ℤ) :
    Finset.Ico (residueIndexLower a r v) (residueIndexLower b r v) =
      Finset.Ico (residueIndexLower a r v) (residueIndexLower a r v + residueIndexLength a b r v) := by
  ext x
  simp only [Finset.mem_Ico, residueIndexLength]
  omega

theorem residueInterval_eq_map (a b r v : ℤ) (hr : 0 < r) :
    Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b) =
      (Finset.Ico (residueIndexLower a r v) (residueIndexLower a r v + residueIndexLength a b r v)).map
        (residueAffineEmbedding r v hr.ne') := by
  rw [Int.Ico_filter_modEq_eq, Int.Ico_filter_dvd_eq (a - v) (b - v) hr, Finset.map_map]
  simp only [Int.cast_sub]
  change (Finset.Ico (residueIndexLower a r v) (residueIndexLower b r v)).map _ = _
  rw [residueIndexInterval_eq]
  congr 1
  ext k
  change k * r + v = v + r * k
  ring

noncomputable def residueIntervalEquiv (a b r v : ℤ) (hr : 0 < r) :
    ↥(Finset.Ico (residueIndexLower a r v) (residueIndexLower a r v + residueIndexLength a b r v)) ≃
      ↥(Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)) := by
  let f : ↥(Finset.Ico (residueIndexLower a r v)
      (residueIndexLower a r v + residueIndexLength a b r v)) →
      ↥(Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)) := fun x =>
    ⟨v + r * x.val, by
      rw [residueInterval_eq_map a b r v hr]
      exact Finset.mem_map.mpr ⟨x.val, x.property, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    apply Subtype.ext
    exact (residueAffineEmbedding r v hr.ne').injective (congrArg Subtype.val h)
  · intro y
    let yy : ℤ := y.val
    have hy : yy ∈ Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b) := y.property
    rw [residueInterval_eq_map a b r v hr] at hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

@[simp] theorem residueIntervalEquiv_val (a b r v : ℤ) (hr : 0 < r)
    (x : ↥(Finset.Ico (residueIndexLower a r v)
      (residueIndexLower a r v + residueIndexLength a b r v))) :
    (residueIntervalEquiv a b r v hr x).val = v + r * x.val := rfl

end Erdos3

end

section

namespace Erdos3

def integerResidueLabel (d : ℕ) (hd : 0 < d) (x : ℤ) : Fin d :=
  ⟨(x % (d : ℤ)).toNat, by
    have hlo := Int.emod_nonneg x (show (d : ℤ) ≠ 0 by exact_mod_cast hd.ne')
    have hhi := Int.emod_lt_of_pos x (show (0 : ℤ) < d by exact_mod_cast hd)
    omega⟩

theorem integerResidueLabel_val (d : ℕ) (hd : 0 < d) (x : ℤ) :
    ((integerResidueLabel d hd x).val : ℤ) = x % (d : ℤ) := by
  have hlo := Int.emod_nonneg x (show (d : ℤ) ≠ 0 by exact_mod_cast hd.ne')
  exact Int.toNat_of_nonneg hlo

theorem integerResidueLabel_eq_iff (d : ℕ) (hd : 0 < d) (x : ℤ) (v : Fin d) :
    integerResidueLabel d hd x = v ↔ x ≡ (v.val : ℤ) [ZMOD (d : ℤ)] := by
  have hv : (v.val : ℤ) % (d : ℤ) = v.val := Int.emod_eq_of_lt
    (Int.natCast_nonneg _) (by exact_mod_cast v.isLt)
  have hx := integerResidueLabel_val d hd x
  rw [Int.ModEq, hv, Fin.ext_iff]
  omega

abbrev CompatibleAuxResidue (M d : ℕ) (u : ℤ) :=
  {v : Fin d // ∃ c : ℤ, c ≡ u [ZMOD (M : ℤ)] ∧ c ≡ (v.val : ℤ) [ZMOD (d : ℤ)]}

noncomputable instance compatibleAuxResidueFintype (M d : ℕ) (u : ℤ) :
    Fintype (CompatibleAuxResidue M d u) := Fintype.ofFinite _

def compatibleAuxResidueOfPoint (M d : ℕ) (hd : 0 < d) (u x : ℤ)
    (hx : x ≡ u [ZMOD (M : ℤ)]) : CompatibleAuxResidue M d u :=
  ⟨integerResidueLabel d hd x, x, hx, (integerResidueLabel_eq_iff d hd x _).mp rfl⟩

theorem compatibleAuxResidueOfPoint_eq_iff (M d : ℕ) (hd : 0 < d) (u x : ℤ)
    (hx : x ≡ u [ZMOD (M : ℤ)]) (v : CompatibleAuxResidue M d u) :
    compatibleAuxResidueOfPoint M d hd u x hx = v ↔
      x ≡ (v.val.val : ℤ) [ZMOD (d : ℤ)] := by
  rw [Subtype.ext_iff]
  exact integerResidueLabel_eq_iff d hd x v.val

noncomputable def CompatibleAuxResidue.baseValue {M d : ℕ} {u : ℤ}
    (v : CompatibleAuxResidue M d u) : ℤ := Classical.choose v.property

noncomputable def CompatibleAuxResidue.refinedValue {M d J : ℕ} {u : ℤ}
    (v : CompatibleAuxResidue M d u) (hcop : (M * d).Coprime J) (w : ℤ) : ℤ :=
  Classical.choose ((coprime_refinement_preserves_compatibility hcop u v.val.val w).mp v.property)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalSliceCost
namespace OAI

section

namespace Erdos3

def PhysicalSubbox {σ : Type*} (parent : σ → ℤ) (H : σ → ℕ)
    (lo : σ → ℤ) (N : σ → ℕ) : Prop :=
  ∀ j, parent j ≤ lo j ∧ lo j + N j ≤ parent j + H j

def ResidueSliceLogCostLE {σ : Type*} (H : σ → ℕ) (lo : σ → ℤ) (N : σ → ℕ)
    (M : ℕ) (a : σ → ℤ) (P : ℝ) : Prop :=
  ∀ j, Real.exp (-P) * (H j : ℝ) ≤ (residueIndexLength (lo j) (lo j + N j) M (a j) : ℝ)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedOverlapCorrelation
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {A : Type*} [AddCommGroup A] [DecidableEq A]

theorem sum_overlaps {M : Type*} [AddCommMonoid M]
    (Q : Finset A) (F : A → A → M) :
    (∑ h ∈ cubeDifferenceSupport Q, ∑ x ∈ derivativeSupport Q h, F x (x + h)) =
      ∑ x ∈ Q, ∑ y ∈ Q, F x y := by
  calc
    _ = ∑ p ∈ (cubeDifferenceSupport Q ×ˢ Q).filter (fun p => p.2 + p.1 ∈ Q),
        F p.2 (p.2 + p.1) := by
      rw [Finset.sum_filter, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro h _
      simp only [derivativeSupport, Finset.sum_filter]
    _ = ∑ p ∈ Q ×ˢ Q, F p.1 p.2 := by
      apply Finset.sum_bij (fun p _ => (p.2, p.2 + p.1))
      · intro p hp
        obtain ⟨hp, hsum⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp hp).2, hsum⟩
      · intro p hp q hq he
        have hx := congrArg Prod.fst he
        have hh := congrArg Prod.snd he
        simp only at hx hh
        apply Prod.ext
        · apply add_left_cancel (a := p.2)
          exact hh.trans (congrArg (fun x => x + q.1) hx).symm
        · exact hx
      · intro p hp
        obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
        refine ⟨(p.2 - p.1, p.1), ?_, ?_⟩
        · apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_product.mpr ⟨?_, hx⟩, ?_⟩
          · exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
          · simpa only [add_sub_cancel] using hy
        · simp only [add_sub_cancel, Prod.eta]
      · intro p hp
        rfl
    _ = _ := Finset.sum_product Q Q (fun p => F p.1 p.2)

theorem sum_overlap_card (Q : Finset A) :
    (∑ h ∈ cubeDifferenceSupport Q, (derivativeSupport Q h).card) = Q.card ^ 2 := by
  simpa only [Finset.sum_const, smul_eq_mul, mul_one, pow_two] using
    sum_overlaps Q (fun _ _ => (1 : ℕ))

theorem sum_overlap_weights {Q : Finset A} (hQ : Q.Nonempty) :
    (∑ h ∈ cubeDifferenceSupport Q, ((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) = 1 := by
  rw [← Finset.sum_div, ← Nat.cast_sum, sum_overlap_card, Nat.cast_pow]
  exact div_self (pow_ne_zero _ (by exact_mod_cast hQ.card_pos.ne'))

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A : Type*} [AddCommGroup A] [DecidableEq A]

theorem correlation_sq_mul_card (Q : Finset A) (f u : A → ℂ) :
    (Q.card : ℝ) ^ 2 * ‖finiteCorrelation Q f u‖ ^ 2 =
      ∑ h ∈ cubeDifferenceSupport Q, ((derivativeSupport Q h).card : ℝ) *
        (finiteCorrelation (derivativeSupport Q h)
          (multiplicativeDerivative f h) (multiplicativeDerivative u h)).re := by
  let g := fun x => f x * star (u x)
  have hp : (∑ h ∈ cubeDifferenceSupport Q, ∑ x ∈ derivativeSupport Q h, g x * star (g (x + h))) =
      (∑ x ∈ Q, g x) * star (∑ x ∈ Q, g x) := by
    rw [sum_overlaps Q (fun x y => g x * star (g y))]
    simp only [Finset.sum_mul, Finset.mul_sum, star_sum]
    rw [Finset.sum_comm]
  have hinner (h : A) : (∑ x ∈ derivativeSupport Q h, g x * star (g (x + h))) =
      ((derivativeSupport Q h).card : ℂ) * finiteCorrelation (derivativeSupport Q h)
        (multiplicativeDerivative f h) (multiplicativeDerivative u h) := by
    rw [finiteCorrelation, Finset.card_mul_expect]
    apply Finset.sum_congr rfl
    intro x _
    simp only [g, multiplicativeDerivative, star_mul, star_star]
    ring
  have hnorm : ‖∑ x ∈ Q, g x‖ ^ 2 = (Q.card : ℝ) ^ 2 * ‖finiteCorrelation Q f u‖ ^ 2 := by
    rw [← Finset.card_mul_expect Q g, norm_mul, Complex.norm_natCast, mul_pow]
    rfl
  have hreal := congrArg Complex.re hp
  simp_rw [hinner] at hreal
  rw [mul_star_re_eq_norm_sq, hnorm] at hreal
  simpa only [Complex.re_sum, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero] using hreal.symm

theorem correlation_sq_eq_sum_overlap {Q : Finset A} (hQ : Q.Nonempty) (f u : A → ℂ) :
    ‖finiteCorrelation Q f u‖ ^ 2 =
      ∑ h ∈ cubeDifferenceSupport Q, (((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) *
        (finiteCorrelation (derivativeSupport Q h)
          (multiplicativeDerivative f h) (multiplicativeDerivative u h)).re := by
  have hcard : (Q.card : ℝ) ≠ 0 := by exact_mod_cast hQ.card_pos.ne'
  calc
    _ = ((Q.card : ℝ) ^ 2 * ‖finiteCorrelation Q f u‖ ^ 2) / (Q.card : ℝ) ^ 2 := by
      field_simp
    _ = _ := by
      rw [correlation_sq_mul_card, Finset.sum_div]
      simp only [div_mul_eq_mul_div]

theorem correlation_sq_le_sum_overlap_norm {Q : Finset A} (hQ : Q.Nonempty) (f u : A → ℂ) :
    ‖finiteCorrelation Q f u‖ ^ 2 ≤
      ∑ h ∈ cubeDifferenceSupport Q, (((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) *
        ‖finiteCorrelation (derivativeSupport Q h)
          (multiplicativeDerivative f h) (multiplicativeDerivative u h)‖ := by
  rw [correlation_sq_eq_sum_overlap hQ]
  apply Finset.sum_le_sum
  intro h _
  exact mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (by positivity)

theorem norm_overlapCorrelation_le {Q : Finset A} (f u : A → ℂ) {B : ℝ}
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) (hu : ∀ x ∈ Q, ‖u x‖ ≤ B)
    {h : A} (hh : h ∈ cubeDifferenceSupport Q) :
    ‖finiteCorrelation (derivativeSupport Q h)
      (multiplicativeDerivative f h) (multiplicativeDerivative u h)‖ ≤ B ^ 2 := by
  apply norm_finiteCorrelation_le ((mem_cubeDifferenceSupport Q h).mp hh)
  · intro x hx
    obtain ⟨hx, hxh⟩ := Finset.mem_filter.mp hx
    simpa only [multiplicativeDerivative, norm_mul, norm_star, one_mul] using
      mul_le_mul (hf x hx) (hf (x + h) hxh) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  · intro x hx
    obtain ⟨hx, hxh⟩ := Finset.mem_filter.mp hx
    have hB : 0 ≤ B := (norm_nonneg (u x)).trans (hu x hx)
    simpa only [multiplicativeDerivative, norm_mul, norm_star, pow_two] using
      mul_le_mul (hu x hx) (hu (x + h) hxh) (norm_nonneg _) hB

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

theorem weight_large_values_of_sum {ι : Type*} (I : Finset ι) (w a : ι → ℝ)
    {r B : ℝ} (hr : 0 ≤ r) (hB : 0 < B)
    (hw : ∀ i ∈ I, 0 ≤ w i) (hsum : ∑ i ∈ I, w i = 1)
    (ha : ∀ i ∈ I, a i ≤ B) (hmean : r ≤ ∑ i ∈ I, w i * a i) :
    r / (2 * B) ≤ ∑ i ∈ I, w i * (if r / 2 ≤ a i then (1 : ℝ) else 0) := by
  classical
  have hp (i : ι) (hi : i ∈ I) : a i ≤ r / 2 + B * (if r / 2 ≤ a i then (1 : ℝ) else 0) := by
    split_ifs with h
    · simp only [mul_one]
      linarith [ha i hi]
    · simp only [mul_zero, add_zero]
      exact (lt_of_not_ge h).le
  have hbound := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hp i hi) (hw i hi))
  have he : (∑ i ∈ I, w i * (r / 2 + B * (if r / 2 ≤ a i then (1 : ℝ) else 0))) =
      r / 2 * (∑ i ∈ I, w i) + B * (∑ i ∈ I, w i * (if r / 2 ≤ a i then (1 : ℝ) else 0)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, hsum, mul_one] at hbound
  apply (div_le_iff₀ (by positivity : 0 < 2 * B)).mpr
  nlinarith

variable {A : Type*} [AddCommGroup A] [DecidableEq A]

theorem weight_correlating_overlaps {Q : Finset A} (hQ : Q.Nonempty)
    (f u : A → ℂ) {ρ B : ℝ} (hρ : 0 ≤ ρ) (hB : 0 < B)
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) (hu : ∀ x ∈ Q, ‖u x‖ ≤ B)
    (hcorr : ρ ≤ ‖finiteCorrelation Q f u‖) :
    ρ ^ 2 / (2 * B ^ 2) ≤ ∑ h ∈ cubeDifferenceSupport Q,
      (((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) *
        (if ρ ^ 2 / 2 ≤ ‖finiteCorrelation (derivativeSupport Q h)
          (multiplicativeDerivative f h) (multiplicativeDerivative u h)‖ then (1 : ℝ) else 0) := by
  apply weight_large_values_of_sum _ _ _ (sq_nonneg ρ) (sq_pos_of_pos hB)
    (fun _ _ => by positivity) (sum_overlap_weights hQ)
    (fun _ hh => norm_overlapCorrelation_le f u hf hu hh)
  exact (pow_le_pow_left₀ hρ hcorr 2).trans (correlation_sq_le_sum_overlap_norm hQ f u)

theorem weight_small_overlaps {Q : Finset A} (hQ : Q.Nonempty) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∑ h ∈ (cubeDifferenceSupport Q).filter
      (fun h => ((derivativeSupport Q h).card : ℝ) ≤ δ * Q.card),
      ((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) ≤
        δ * (cubeDifferenceSupport Q).card / Q.card := by
  classical
  have hq : (0 : ℝ) < Q.card := by exact_mod_cast hQ.card_pos
  let I := (cubeDifferenceSupport Q).filter
    (fun h => ((derivativeSupport Q h).card : ℝ) ≤ δ * Q.card)
  have hp (h : A) (hh : h ∈ I) :
      ((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2 ≤ δ / Q.card := by
    have hsmall := (Finset.mem_filter.mp hh).2
    apply (div_le_div_iff₀ (sq_pos_of_pos hq) hq).mpr
    nlinarith
  calc
    _ ≤ ∑ _h ∈ I, δ / (Q.card : ℝ) := Finset.sum_le_sum hp
    _ = (I.card : ℝ) * (δ / Q.card) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((cubeDifferenceSupport Q).card : ℝ) * (δ / Q.card) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_filter_le _ _) (div_nonneg hδ hq.le)
    _ = _ := by ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.EmbeddedFiniteConditioning
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

noncomputable def ofPositiveWeights {X : Type*} [Fintype X] (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmass : 0 < ∑ x, w x) : FiniteProbabilityWeights X where
  weight x := w x / ∑ y, w y
  nonneg x := div_nonneg (hw x) hmass.le
  total := by rw [← Finset.sum_div, div_self hmass.ne']

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem eq_of_weight_eq {X : Type*} [Fintype X] {p q : FiniteProbabilityWeights X}
    (h : ∀ x, p.weight x = q.weight x) : p = q := by
  cases p with
  | mk wp hp tp =>
    cases q with
    | mk wq hq tq =>
      have he : wp = wq := funext h
      subst wq
      rfl

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoxResiduePartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def integerResidueCount (a b r v : ℤ) : ℕ :=
  (Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card

noncomputable def rectangularResidueCount {I : Type*} [Fintype I] (a b r v : I → ℤ) : ℕ :=
  ∏ i, integerResidueCount (a i) (b i) (r i) (v i)

noncomputable def integerRectangleVolume {I : Type*} [Fintype I] (a b : I → ℤ) : ℝ :=
  ∏ i, ((b i - a i : ℤ) : ℝ)

end Erdos3

end

section

namespace Erdos3

noncomputable def integerIntervalEquivFin (a : ℤ) (N : ℕ) :
    ↥(Finset.Ico a (a + N)) ≃ Fin N where
  toFun x := ⟨(x.val - a).toNat, by have hx := Finset.mem_Ico.mp x.property; omega⟩
  invFun n := ⟨a + n.val, by simp only [Finset.mem_Ico]; omega⟩
  left_inv x := by
    apply Subtype.ext
    have hx := Finset.mem_Ico.mp x.property
    dsimp only
    omega
  right_inv n := by
    apply Fin.ext
    dsimp only
    omega

theorem integerIntervalEquivFin_val (a : ℤ) (N : ℕ) (x : ↥(Finset.Ico a (a + N))) :
    ((integerIntervalEquivFin a N x).val : ℤ) = x.val - a := by
  have hx := Finset.mem_Ico.mp x.property
  change (((x.val - a).toNat : ℕ) : ℤ) = x.val - a
  omega

@[simp] theorem integerIntervalEquivFin_symm_val (a : ℤ) (N : ℕ) (n : Fin N) :
    ((integerIntervalEquivFin a N).symm n).val = a + n.val := rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

noncomputable def intervalCellLower (a : ℤ) {N : ℕ} (P : FiniteProgressionPartition N) (k : P.Label) : ℤ :=
  a + P.start k

noncomputable def intervalCellUpper (a : ℤ) {N : ℕ} (P : FiniteProgressionPartition N) (k : P.Label) : ℤ :=
  a + P.start k + P.length k

noncomputable def intervalResidueCell (a : ℤ) {N : ℕ} (P : FiniteProgressionPartition N) (r v : ℤ) :
    ↥(Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a (a + N))) → P.Label :=
  fun x => P.cell (integerIntervalEquivFin a N ⟨x.val, (Finset.mem_filter.mp x.property).1⟩)

theorem intervalResidueCell_eq_iff (a : ℤ) {N : ℕ} (P : FiniteProgressionPartition N)
    (hstep : ∀ k, P.step k = 1) (r v : ℤ)
    (x : ↥(Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a (a + N)))) (k : P.Label) :
    intervalResidueCell a P r v x = k ↔
      intervalCellLower a P k ≤ x.val ∧ x.val < intervalCellUpper a P k := by
  let y := integerIntervalEquivFin a N ⟨x.val, (Finset.mem_filter.mp x.property).1⟩
  have hy : (y.val : ℤ) = x.val - a := integerIntervalEquivFin_val a N _
  change P.cell y = k ↔ _
  rw [P.cell_eq_iff_of_step_one hstep]
  unfold intervalCellLower intervalCellUpper
  constructor
  · rintro ⟨hlo, hhi⟩
    have hlo' : (P.start k : ℤ) ≤ y.val := by exact_mod_cast hlo
    have hhi' : (y.val : ℤ) < (P.start k : ℤ) + P.length k := by exact_mod_cast hhi
    omega
  · rintro ⟨hlo, hhi⟩
    constructor
    · have h : (P.start k : ℤ) ≤ y.val := by omega
      exact_mod_cast h
    · have h : (y.val : ℤ) < (P.start k : ℤ) + P.length k := by omega
      exact_mod_cast h

noncomputable def intervalResidueCellEquiv (a : ℤ) {N : ℕ} (P : FiniteProgressionPartition N)
    (hstep : ∀ k, P.step k = 1) (hpos : ∀ k, 0 < P.length k) (r v : ℤ) (k : P.Label) :
    {x : ↥(Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a (a + N))) //
      intervalResidueCell a P r v x = k} ≃
      ↥(Finset.filter (fun x => x ≡ v [ZMOD r])
        (Finset.Ico (intervalCellLower a P k) (intervalCellUpper a P k))) where
  toFun x := ⟨x.val.val, Finset.mem_filter.mpr
    ⟨Finset.mem_Ico.mpr ((intervalResidueCell_eq_iff a P hstep r v x.val k).mp x.property),
      (Finset.mem_filter.mp x.val.property).2⟩⟩
  invFun x := by
    have hx := Finset.mem_filter.mp x.property
    have hinterval := Finset.mem_Ico.mp hx.1
    have hend := P.end_le_of_step_one hstep k (hpos k)
    have hend' : (P.start k : ℤ) + P.length k ≤ N := by exact_mod_cast hend
    have hstart : (0 : ℤ) ≤ P.start k := Int.natCast_nonneg _
    have houter : x.val ∈ Finset.Ico a (a + N) := by
      simp only [intervalCellLower, intervalCellUpper] at hinterval
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    let y : ↥(Finset.filter (fun z => z ≡ v [ZMOD r]) (Finset.Ico a (a + N))) :=
      ⟨x.val, Finset.mem_filter.mpr ⟨houter, hx.2⟩⟩
    exact ⟨y, (intervalResidueCell_eq_iff a P hstep r v y k).mpr hinterval⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

abbrev IntegerResidueBox {I : Type*} (a b r v : I → ℤ) :=
  ∀ i, ↥(Finset.filter (fun x => x ≡ v i [ZMOD r i]) (Finset.Ico (a i) (b i)))

noncomputable def boxIntervalResidueCell {I : Type*} (a : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (r v : I → ℤ)
    (x : IntegerResidueBox a (fun i => a i + N i) r v) : ∀ i, (P i).Label :=
  fun i => intervalResidueCell (a i) (P i) (r i) (v i) (x i)

noncomputable def boxIntervalResidueCellEquiv {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (P i).step k = 1) (hpos : ∀ i k, 0 < (P i).length k)
    (r v : I → ℤ) (k : ∀ i, (P i).Label) :
    ↥(partitionCell (boxIntervalResidueCell a N P r v) k) ≃
      IntegerResidueBox (fun i => intervalCellLower (a i) (P i) (k i))
        (fun i => intervalCellUpper (a i) (P i) (k i)) r v := by
  let e₁ : ↥(partitionCell (boxIntervalResidueCell a N P r v) k) ≃
      {x : IntegerResidueBox a (fun i => a i + N i) r v //
        ∀ i, intervalResidueCell (a i) (P i) (r i) (v i) (x i) = k i} :=
    Equiv.subtypeEquivRight (fun x => by
      simp only [mem_partitionCell, boxIntervalResidueCell, funext_iff])
  exact e₁.trans (Equiv.subtypePiEquivPi.trans (Equiv.piCongrRight (fun i =>
    intervalResidueCellEquiv (a i) (P i) (hstep i) (hpos i) (r i) (v i) (k i))))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def integerBox (T : ι → ℕ) : Finset (ι → ℤ) :=
  Fintype.piFinset (fun i ↦ Finset.Ico (0 : ℤ) (T i))

@[simp] theorem mem_integerBox (T : ι → ℕ) (x : ι → ℤ) :
    x ∈ integerBox T ↔ ∀ i, 0 ≤ x i ∧ x i < T i := by
  simp [integerBox, Fintype.mem_piFinset]

abbrev BoxAmbient (T : ι → ℕ) := ∀ i, ZMod (4 * T i)

def boxReduction (T : ι → ℕ) : (ι → ℤ) →+ BoxAmbient T where
  toFun x i := x i
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem boxReduction_apply (T : ι → ℕ) (x : ι → ℤ) (i : ι) :
    boxReduction T x i = (x i : ZMod (4 * T i)) := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem int_eq_of_zmod_eq_of_bounds {m : ℕ} {a b : ℤ}
    (ha : 0 ≤ a ∧ a < m) (hb : 0 ≤ b ∧ b < m) (he : (a : ZMod m) = (b : ZMod m)) :
    a = b := by
  have hm := (ZMod.intCast_eq_intCast_iff' a b m).mp he
  simpa only [Int.emod_eq_of_lt ha.1 ha.2, Int.emod_eq_of_lt hb.1 hb.2] using hm

theorem boxReduction_reflectsPairSums (T : ι → ℕ) :
    ReflectsPairSums (boxReduction T) (integerBox T : Set (ι → ℤ)) := by
  intro a ha b hb c hc d hd he
  have ha' := (mem_integerBox T a).mp ha
  have hb' := (mem_integerBox T b).mp hb
  have hc' := (mem_integerBox T c).mp hc
  have hd' := (mem_integerBox T d).mp hd
  funext i
  change a i + b i = c i + d i
  apply int_eq_of_zmod_eq_of_bounds (m := 4 * T i)
  · have h1 := ha' i
    have h2 := hb' i
    constructor <;> push_cast <;> omega
  · have h1 := hc' i
    have h2 := hd' i
    constructor <;> push_cast <;> omega
  · have hi := congrFun he i
    simpa only [Pi.add_apply, boxReduction_apply, Int.cast_add] using hi

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem integerBox_expect_eq_zmod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) [NeZero N] (f : (ι → ℤ) → ℂ) :
    (𝔼 x ∈ integerBox (fun _ : ι => N), f x) =
      𝔼 t : ι → ZMod N, f (fun i => ((t i).val : ℤ)) := by
  symm
  apply Finset.expect_bij (fun t _ i => ((t i).val : ℤ))
  · intro t _
    rw [mem_integerBox]
    exact fun i => ⟨Int.natCast_nonneg _, by exact_mod_cast (t i).val_lt⟩
  · intro t _
    rfl
  · intro t _ u _ h
    funext i
    apply ZMod.val_injective N
    exact_mod_cast congrFun h i
  · intro x hx
    have hx' := (mem_integerBox (fun _ : ι => N) x).mp hx
    refine ⟨(fun i => (x i : ZMod N)), Finset.mem_univ _, ?_⟩
    funext i
    rw [ZMod.val_intCast, Int.emod_eq_of_lt (hx' i).1 (hx' i).2]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

def integerCyclicMap (N : ℕ) : ℤ →+ ZMod N := Int.castAddHom (ZMod N)

theorem integerInterval_reflectsPairSums (N : ℕ) (a b : ℤ)
    (hdiam : 2 * (b - a - 1) < (N : ℤ)) :
    ReflectsPairSums (integerCyclicMap N) (Finset.Ico a b : Set ℤ) := by
  intro x hx y hy z hz t ht he
  have hx' := Finset.mem_Ico.mp hx
  have hy' := Finset.mem_Ico.mp hy
  have hz' := Finset.mem_Ico.mp hz
  have ht' := Finset.mem_Ico.mp ht
  have hxy : 0 ≤ x + y - 2 * a ∧ x + y - 2 * a < N := by omega
  have hzt : 0 ≤ z + t - 2 * a ∧ z + t - 2 * a < N := by omega
  have he' : ((x + y - 2 * a : ℤ) : ZMod N) = ((z + t - 2 * a : ℤ) : ZMod N) := by
    change (x : ZMod N) + y = (z : ZMod N) + t at he
    push_cast
    exact congrArg (fun v : ZMod N => v - 2 * (a : ZMod N)) he
  have hh := int_eq_of_zmod_eq_of_bounds hxy hzt he'
  omega

theorem integerInterval_image_cyclicInterval (N : ℕ) (a : ℤ) (L : ℕ) :
    (Finset.Ico a (a + L)).image (integerCyclicMap N) = cyclicInterval (a : ZMod N) L := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hy' := Finset.mem_Ico.mp hy
    refine Finset.mem_image.mpr ⟨(y - a).toNat, Finset.mem_range.mpr ?_, ?_⟩
    · omega
    · change (a : ZMod N) + ((y - a).toNat : ZMod N) = (y : ZMod N)
      have he : (((y - a).toNat : ℕ) : ℤ) = y - a := Int.toNat_of_nonneg (by omega)
      rw [← Int.cast_natCast, he]
      push_cast
      ring
  · intro hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨a + k, Finset.mem_Ico.mpr ?_, ?_⟩
    · have hk' := Finset.mem_range.mp hk
      omega
    · change ((a + k : ℤ) : ZMod N) = (a : ZMod N) + k
      push_cast
      rfl

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def integerBoxCubeCount (T : ι → ℕ) (j : ℕ) : ℕ :=
  Nat.card (SupportedCube j (integerBox T : Set (ι → ℤ)))

noncomputable def integerBoxGowersNorm (T : ι → ℕ) (j : ℕ) (f : (ι → ℤ) → ℂ) : ℝ :=
  finiteSupportGowersNorm j (integerBox T) f

variable (T : ι → ℕ) [∀ i, NeZero (T i)]

theorem integerBox_nonempty : (integerBox T).Nonempty := by
  refine ⟨0, (mem_integerBox T 0).mpr ?_⟩
  intro i
  change 0 ≤ (0 : ℤ) ∧ (0 : ℤ) < T i
  exact ⟨le_rfl, by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (T i))⟩

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem card_integerBox (T : ι → ℕ) : (integerBox T).card = ∏ i, T i := by
  simp [integerBox]

def smallCubeSide (T : ι → ℕ) (j : ℕ) (i : ι) : ℕ := (T i - 1) / (j + 1) + 1

variable (T : ι → ℕ) [∀ i, NeZero (T i)]

theorem small_increments_supported (j : ℕ) (x : ι → ℤ)
    (hx : x ∈ integerBox (smallCubeSide T j)) (ds : Fin j → (ι → ℤ))
    (hds : ∀ k, ds k ∈ integerBox (smallCubeSide T j)) (ω : Fin j → Bool) :
    x + cubeShift ds ω ∈ integerBox T := by
  apply (mem_integerBox T _).mpr
  intro i
  let m := (T i - 1) / (j + 1)
  have hxi : 0 ≤ x i ∧ x i ≤ (m : ℤ) := by
    have h := (mem_integerBox _ _).mp hx i
    change 0 ≤ x i ∧ x i < ((m + 1 : ℕ) : ℤ) at h
    push_cast at h
    omega
  have hdi (k : Fin j) : 0 ≤ ds k i ∧ ds k i ≤ (m : ℤ) := by
    have h := (mem_integerBox _ _).mp (hds k) i
    change 0 ≤ ds k i ∧ ds k i < ((m + 1 : ℕ) : ℤ) at h
    push_cast at h
    omega
  have hlo : 0 ≤ ∑ k, if ω k then ds k i else (0 : ℤ) := by
    apply Finset.sum_nonneg
    intro k hk
    split_ifs
    · exact (hdi k).1
    · exact le_rfl
  have hhi : (∑ k, if ω k then ds k i else (0 : ℤ)) ≤ (j : ℤ) * m := by
    calc
      _ ≤ ∑ _k : Fin j, (m : ℤ) := by
        apply Finset.sum_le_sum
        intro k hk
        split_ifs
        · exact (hdi k).2
        · exact Int.natCast_nonneg _
      _ = _ := by simp
  have hm : ((j : ℤ) + 1) * (m : ℤ) < T i := by
    have hmul := Nat.mul_div_le (T i - 1) (j + 1)
    have hT := Nat.pos_of_ne_zero (NeZero.ne (T i))
    have hlt : (j + 1) * m < T i := hmul.trans_lt (Nat.sub_lt hT (by omega))
    exact_mod_cast hlt
  simp only [Pi.add_apply, cubeShift, Finset.sum_apply, ite_apply, Pi.zero_apply]
  constructor <;> nlinarith [hxi.1, hxi.2]

noncomputable def smallBoxCubeMap (j : ℕ) :
    ((Fin j → integerBox (smallCubeSide T j)) × integerBox (smallCubeSide T j)) →
      SupportedCube j (integerBox T : Set (ι → ℤ)) :=
  fun p ↦ ⟨(fun k ↦ (p.1 k).val, p.2.val),
    small_increments_supported T j p.2.val p.2.property
      (fun k ↦ (p.1 k).val) (fun k ↦ (p.1 k).property)⟩

theorem smallBoxCubeMap_injective (j : ℕ) : Function.Injective (smallBoxCubeMap T j) := by
  intro p q he
  apply Prod.ext
  · funext k
    apply Subtype.ext
    exact congrArg (fun r ↦ r.val.1 k) he
  · apply Subtype.ext
    exact congrArg (fun r ↦ r.val.2) he

theorem small_box_card_pow_le_cubeCount (j : ℕ) :
    (integerBox (smallCubeSide T j)).card ^ (j + 1) ≤ integerBoxCubeCount T j := by
  have h := Nat.card_le_card_of_injective (smallBoxCubeMap T j) (smallBoxCubeMap_injective T j)
  change Nat.card ((Fin j → integerBox (smallCubeSide T j)) × integerBox (smallCubeSide T j)) ≤
    integerBoxCubeCount T j at h
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_coe, Fintype.card_fin, pow_succ] using h

theorem card_integerBox_le_small_box (j : ℕ) :
    (integerBox T).card ≤ (j + 1) ^ Fintype.card ι * (integerBox (smallCubeSide T j)).card := by
  have hi (i : ι) : T i ≤ (j + 1) * smallCubeSide T j i := by
    have h := Nat.lt_mul_div_succ (T i - 1) (Nat.succ_pos j)
    change T i - 1 < (j + 1) * ((T i - 1) / (j + 1) + 1) at h
    have hT := Nat.pos_of_ne_zero (NeZero.ne (T i))
    change T i ≤ (j + 1) * ((T i - 1) / (j + 1) + 1)
    omega
  calc
    _ = ∏ i, T i := card_integerBox T
    _ ≤ ∏ i, (j + 1) * smallCubeSide T j i :=
      Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) (fun i _ ↦ hi i)
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]; simp [card_integerBox]

theorem integerBoxCubeCount_lower (j : ℕ) :
    (integerBox T).card ^ (j + 1) ≤
      (j + 1) ^ (Fintype.card ι * (j + 1)) * integerBoxCubeCount T j := by
  have h := Nat.pow_le_pow_left (card_integerBox_le_small_box T j) (j + 1)
  rw [mul_pow, ← pow_mul] at h
  exact h.trans (Nat.mul_le_mul_left _ (small_box_card_pow_le_cubeCount T j))

omit [∀ i, NeZero (T i)] in
theorem integerBoxCubeCount_upper (j : ℕ) :
    integerBoxCubeCount T j ≤ (integerBox T).card ^ (j + 1) :=
  card_supportedCube_le j (integerBox T)

theorem integerBoxCubeCount_bounds (j : ℕ) :
    ((1 : ℝ) / ((j : ℝ) + 1) ^ (j + 1)) ^ Fintype.card ι *
        ((integerBox T).card : ℝ) ^ (j + 1) ≤ integerBoxCubeCount T j ∧
      (integerBoxCubeCount T j : ℝ) ≤ ((integerBox T).card : ℝ) ^ (j + 1) := by
  constructor
  · have h : ((integerBox T).card : ℝ) ^ (j + 1) ≤
        (((j + 1 : ℕ) : ℝ) ^ (Fintype.card ι * (j + 1))) * integerBoxCubeCount T j := by
      exact_mod_cast integerBoxCubeCount_lower T j
    have he : ((1 : ℝ) / ((j : ℝ) + 1) ^ (j + 1)) ^ Fintype.card ι *
        ((integerBox T).card : ℝ) ^ (j + 1) =
        ((integerBox T).card : ℝ) ^ (j + 1) /
          ((j : ℝ) + 1) ^ (Fintype.card ι * (j + 1)) := by
      rw [div_pow, one_pow, ← pow_mul, Nat.mul_comm (j + 1) (Fintype.card ι)]
      ring
    rw [he]
    apply (div_le_iff₀ (pow_pos (by positivity : 0 < (j : ℝ) + 1) _)).mpr
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using h
  · exact_mod_cast integerBoxCubeCount_upper T j

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def translatedIntegerBox (a : ι → ℤ) (T : ι → ℕ) : Finset (ι → ℤ) :=
  translateSupport a (integerBox T)

theorem mem_translatedIntegerBox (a : ι → ℤ) (T : ι → ℕ) (x : ι → ℤ) :
    x ∈ translatedIntegerBox a T ↔ ∀ i, a i ≤ x i ∧ x i < a i + T i := by
  rw [translatedIntegerBox, mem_translateSupport, mem_integerBox]
  apply forall_congr'
  intro i
  change (0 ≤ x i - a i ∧ x i - a i < T i) ↔ _
  omega

variable (T : ι → ℕ) [∀ i, NeZero (T i)]

theorem translatedIntegerBox_nonempty (a : ι → ℤ) : (translatedIntegerBox a T).Nonempty :=
  (integerBox_nonempty T).image (fun x ↦ a + x)

omit [∀ i, NeZero (T i)] in
theorem translatedIntegerBox_reflectsPairSums (a : ι → ℤ) :
    ReflectsPairSums (boxReduction T) (translatedIntegerBox a T : Set (ι → ℤ)) :=
  (boxReduction_reflectsPairSums T).translate a

theorem translatedIntegerBox_norm_degree_one (a : ι → ℤ) (f : (ι → ℤ) → ℂ) :
    finiteSupportGowersNorm 1 (translatedIntegerBox a T) f =
      ‖𝔼 x ∈ translatedIntegerBox a T, f x‖ :=
  finiteSupportGowersNorm_degree_one_of_embedding (translatedIntegerBox_reflectsPairSums T a)
    (translatedIntegerBox_nonempty T a) f

theorem translatedIntegerBox_cubeCount_bounds (a : ι → ℤ) (j : ℕ) :
    ((1 : ℝ) / ((j : ℝ) + 1) ^ (j + 1)) ^ Fintype.card ι *
        ((translatedIntegerBox a T).card : ℝ) ^ (j + 1) ≤
          Nat.card (SupportedCube j (translatedIntegerBox a T : Set (ι → ℤ))) ∧
      (Nat.card (SupportedCube j (translatedIntegerBox a T : Set (ι → ℤ))) : ℝ) ≤
        ((translatedIntegerBox a T).card : ℝ) ^ (j + 1) := by
  simpa only [translatedIntegerBox, card_translateSupport, card_supportedCube_translate,
    integerBoxCubeCount] using integerBoxCubeCount_bounds T j

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def trimmedIntegerBox (N R : I → ℕ) : Finset (I → ℤ) :=
  (integerBox (fun i => N i - 2 * R i)).image (fun x => (fun i => (R i : ℤ)) + x)

theorem card_trimmedIntegerBox (N R : I → ℕ) :
    (trimmedIntegerBox N R).card = ∏ i, (N i - 2 * R i) := by
  rw [trimmedIntegerBox, Finset.card_image_of_injective _ (fun _ _ h => add_left_cancel h),
    card_integerBox]

theorem trimmedIntegerBox_nonempty (N R : I → ℕ) (hR : ∀ i, 2 * R i < N i) :
    (trimmedIntegerBox N R).Nonempty := by
  apply Finset.Nonempty.image
  refine ⟨0, (mem_integerBox _ _).mpr ?_⟩
  intro i
  have h : 0 < N i - 2 * R i := Nat.sub_pos_of_lt (hR i)
  simpa using h

theorem trimmedIntegerBox_add_mem (N R : I → ℕ) (hR : ∀ i, 2 * R i ≤ N i)
    {x : I → ℤ} (hx : x ∈ trimmedIntegerBox N R) (y : I → ℤ)
    (hy : ∀ i, |y i| ≤ (R i : ℤ)) : x + y ∈ integerBox N := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  apply (mem_integerBox N _).mpr
  intro i
  have hi := (mem_integerBox _ _).mp ha i
  have hyi := abs_le.mp (hy i)
  have hRi := hR i
  simp only [Pi.add_apply]
  omega

theorem trimmedIntegerBox_card_deficit (N R : I → ℕ)
    (hN : ∀ i, 0 < N i) (hR : ∀ i, 2 * R i ≤ N i) :
    1 - ((trimmedIntegerBox N R).card : ℝ) / (integerBox N).card ≤
      ∑ i, 2 * (R i : ℝ) / N i := by
  have hNR (i : I) : 0 < (N i : ℝ) := by exact_mod_cast hN i
  have he (i : I) : 2 * (R i : ℝ) / N i ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one (hNR i)).mpr
      exact_mod_cast hR i
  have hi (i : I) : 1 - 2 * (R i : ℝ) / N i = ((N i - 2 * R i : ℕ) : ℝ) / N i := by
    rw [Nat.cast_sub (hR i)]
    push_cast
    field_simp [ne_of_gt (hNR i)]
  have hp := one_sub_sum_le_positive_prod Finset.univ
    (fun i => ((N i - 2 * R i : ℕ) : ℝ) / N i) (fun i => 2 * (R i : ℝ) / N i)
    (fun i _ => by positivity) (fun i _ => he i) (fun i _ => (hi i).le)
  rw [card_trimmedIntegerBox, card_integerBox, Nat.cast_prod, Nat.cast_prod,
    ← Finset.prod_div_distrib]
  linarith

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem derivativeSupport_translatedIntegerBox (a : ι → ℤ) (T : ι → ℕ) (h : ι → ℤ) :
    derivativeSupport (translatedIntegerBox a T) h =
      translatedIntegerBox (fun i => a i + max 0 (-h i)) (fun i => ((T i : ℤ) - |h i|).toNat) := by
  ext x
  simp only [derivativeSupport, Finset.mem_filter, mem_translatedIntegerBox, Pi.add_apply,
    ← forall_and]
  apply forall_congr'
  intro i
  by_cases hi : 0 ≤ h i
  · rw [abs_of_nonneg hi, max_eq_left (by omega : -h i ≤ 0)]
    omega
  · rw [abs_of_neg (by omega : h i < 0), max_eq_right (by omega : 0 ≤ -h i)]
    omega

theorem box_overlap_length_pos (a : ι → ℤ) (T : ι → ℕ) {h : ι → ℤ}
    (hh : h ∈ cubeDifferenceSupport (translatedIntegerBox a T)) (i : ι) :
    0 < ((T i : ℤ) - |h i|).toNat := by
  obtain ⟨x, hx⟩ := (mem_cubeDifferenceSupport _ h).mp hh
  obtain ⟨hx, hxh⟩ := Finset.mem_filter.mp hx
  have hx' := (mem_translatedIntegerBox a T x).mp hx i
  have hxh' := (mem_translatedIntegerBox a T (x + h)).mp hxh i
  simp only [Pi.add_apply] at hxh'
  by_cases hi : 0 ≤ h i
  · rw [abs_of_nonneg hi]
    omega
  · rw [abs_of_neg (by omega : h i < 0)]
    omega

theorem box_differenceSupport_subset (a : ι → ℤ) (T : ι → ℕ) :
    cubeDifferenceSupport (translatedIntegerBox a T) ⊆
      translatedIntegerBox (fun i => -(T i : ℤ)) (fun i => 2 * T i) := by
  intro h hh
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hh
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
  apply (mem_translatedIntegerBox _ _ _).mpr
  intro i
  have hx' := (mem_translatedIntegerBox a T p.1).mp hx i
  have hy' := (mem_translatedIntegerBox a T p.2).mp hy i
  simp only [Pi.sub_apply, Nat.cast_mul, Nat.cast_ofNat]
  omega

theorem card_box_differenceSupport_le (a : ι → ℤ) (T : ι → ℕ) :
    (cubeDifferenceSupport (translatedIntegerBox a T)).card ≤
      2 ^ Fintype.card ι * (translatedIntegerBox a T).card := by
  apply (Finset.card_le_card (box_differenceSupport_subset a T)).trans_eq
  simp only [translatedIntegerBox, card_translateSupport, card_integerBox,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def translatedIntegerBoxEquivPi {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) :
    ↥(translatedIntegerBox a N) ≃ ∀ i, ↥(Finset.Ico (a i) (a i + N i)) := by
  let e : ↥(translatedIntegerBox a N) ≃
      {x : I → ℤ // ∀ i, x i ∈ Finset.Ico (a i) (a i + N i)} :=
    Equiv.subtypeEquivRight (fun x => by simp only [mem_translatedIntegerBox, Finset.mem_Ico])
  exact e.trans Equiv.subtypePiEquivPi

@[simp] theorem translatedIntegerBoxEquivPi_val {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (x : ↥(translatedIntegerBox a N)) (i : I) :
    ((translatedIntegerBoxEquivPi a N x) i).val = x.val i := rfl

noncomputable def integerResidueBoxEquiv {I : Type*} [Fintype I] [DecidableEq I]
    (a b r v : I → ℤ) (hr : ∀ i, 0 < r i) :
    ↥(translatedIntegerBox (fun i => residueIndexLower (a i) (r i) (v i))
      (fun i => residueIndexLength (a i) (b i) (r i) (v i))) ≃ IntegerResidueBox a b r v :=
  (translatedIntegerBoxEquivPi _ _).trans
    (Equiv.piCongrRight fun i => residueIntervalEquiv (a i) (b i) (r i) (v i) (hr i))

@[simp] theorem integerResidueBoxEquiv_val {I : Type*} [Fintype I] [DecidableEq I]
    (a b r v : I → ℤ) (hr : ∀ i, 0 < r i)
    (x : ↥(translatedIntegerBox (fun i => residueIndexLower (a i) (r i) (v i))
      (fun i => residueIndexLength (a i) (b i) (r i) (v i)))) (i : I) :
    ((integerResidueBoxEquiv a b r v hr x) i).val = v i + r i * x.val i := rfl

end Erdos3

end

section

namespace Erdos3

noncomputable def physicalResidueCoordinateEquiv
    (lo hi a : ℤ) (M : ℕ) (hM : 0 < M) :
    Fin (residueIndexLength lo hi M a) ≃
      ↥(Finset.filter (fun x => x ≡ a [ZMOD (M : ℤ)]) (Finset.Ico lo hi)) :=
  (integerIntervalEquivFin (residueIndexLower lo M a)
    (residueIndexLength lo hi M a)).symm.trans
      (residueIntervalEquiv lo hi M a (Nat.cast_pos.mpr hM))

theorem physicalResidueCoordinateEquiv_val
    (lo hi a : ℤ) (M : ℕ) (hM : 0 < M)
    (j : Fin (residueIndexLength lo hi M a)) :
    (physicalResidueCoordinateEquiv lo hi a M hM j).val =
      a + M * (residueIndexLower lo M a + j.val) := rfl

namespace ResidueBoxSlice

variable {X : Type*} (N H : X → ℕ) (lo a : X → ℤ) (M : ℕ)
    (hM : 0 < M) (hbox : PhysicalSubbox (fun _ => 0) N lo H)
    (hne : ∀ i, 0 < residueIndexLength (lo i) (lo i + H i) M (a i))

include hM hbox hne in
theorem physicalResidue_start_nonneg (i : X) :
    0 ≤ a i + M * residueIndexLower (lo i) M (a i) := by
  have hx := (physicalResidueCoordinateEquiv (lo i) (lo i + H i) (a i) M hM
    ⟨0, hne i⟩).property
  have hlow := (Finset.mem_Ico.mp (Finset.mem_filter.mp hx).1).1
  rw [physicalResidueCoordinateEquiv_val] at hlow
  have hboxlow := (hbox i).1
  simpa only [Nat.cast_zero, add_zero] using hboxlow.trans hlow

noncomputable def ofPhysicalResidue : ResidueBoxSlice N M where
  start i := (a i + M * residueIndexLower (lo i) M (a i)).toNat
  length i := residueIndexLength (lo i) (lo i + H i) M (a i)
  inside i j hj := by
    have hx := (physicalResidueCoordinateEquiv (lo i) (lo i + H i) (a i) M hM
      ⟨j, hj⟩).property
    have hhigh := (Finset.mem_Ico.mp (Finset.mem_filter.mp hx).1).2
    rw [physicalResidueCoordinateEquiv_val] at hhigh
    have hboxhigh := (hbox i).2
    have hstart := physicalResidue_start_nonneg N H lo a M hM hbox hne i
    have hlt : ((a i + M * residueIndexLower (lo i) M (a i)).toNat : ℤ) +
        (M : ℤ) * j < N i := by
      rw [Int.toNat_of_nonneg hstart]
      nlinarith
    exact_mod_cast hlt

@[simp] theorem ofPhysicalResidue_length (i : X) :
    (ofPhysicalResidue N H lo a M hM hbox hne).length i =
      residueIndexLength (lo i) (lo i + H i) M (a i) := rfl

@[simp] theorem ofPhysicalResidue_start (i : X) :
    (ofPhysicalResidue N H lo a M hM hbox hne).start i =
      (a i + M * residueIndexLower (lo i) M (a i)).toNat := rfl

theorem ofPhysicalResidue_point_int
    (j : ∀ i, Fin ((ofPhysicalResidue N H lo a M hM hbox hne).length i)) (i : X) :
    (((ofPhysicalResidue N H lo a M hM hbox hne).point j i).val : ℤ) =
      a i + M * (residueIndexLower (lo i) M (a i) + (j i).val) := by
  change (((a i + M * residueIndexLower (lo i) M (a i)).toNat + M * (j i).val : ℕ) : ℤ) = _
  rw [Nat.cast_add, Nat.cast_mul,
    Int.toNat_of_nonneg (physicalResidue_start_nonneg N H lo a M hM hbox hne i)]
  ring

noncomputable def ofPhysicalResidueEquiv :
    (∀ i, Fin ((ofPhysicalResidue N H lo a M hM hbox hne).length i)) ≃
      IntegerResidueBox lo (fun i => lo i + H i) (fun _ => (M : ℤ)) a :=
  Equiv.piCongrRight fun i =>
    physicalResidueCoordinateEquiv (lo i) (lo i + H i) (a i) M hM

@[simp] theorem ofPhysicalResidueEquiv_val
    (j : ∀ i, Fin ((ofPhysicalResidue N H lo a M hM hbox hne).length i)) (i : X) :
    ((ofPhysicalResidueEquiv N H lo a M hM hbox hne j) i).val =
      (((ofPhysicalResidue N H lo a M hM hbox hne).point j i).val : ℤ) := by
  rw [ofPhysicalResidue_point_int]
  rfl

end ResidueBoxSlice
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AffinePhaseBias
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem expect_pi_product {ι : Type*} {κ : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)]
    (f : ∀ i, κ i → ℂ) :
    (𝔼 x : ∀ i, κ i, ∏ i, f i (x i)) = ∏ i, 𝔼 y : κ i, f i y := by
  classical
  simp_rw [Fintype.expect_eq_sum_div_card]
  rw [Finset.prod_div_distrib, Fintype.prod_sum, Fintype.card_pi, Nat.cast_prod]

namespace CircleFourier

noncomputable def geometricCharacterMean (N : ℕ) (x : Circle) : ℂ :=
  𝔼 n : Fin N, character ((n : ℕ) • x)

theorem geometricCharacterMean_eq (N : ℕ) (x : Circle) :
    geometricCharacterMean N x = geometricCharacterSum N x / N := by
  rw [geometricCharacterMean, Fintype.expect_eq_sum_div_card, Fintype.card_fin,
    geometricCharacterSum_eq_sum_fin]

theorem norm_geometricCharacterMean_le_one (N : ℕ) (hN : 0 < N) (x : Circle) :
    ‖geometricCharacterMean N x‖ ≤ 1 := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  calc
    ‖geometricCharacterMean N x‖ ≤ 𝔼 n : Fin N, ‖character ((n : ℕ) • x)‖ := RCLike.norm_expect_le (K := ℂ)
    _ = 1 := by simp

theorem integerDistance_le_of_geometric_mean {N : ℕ} (hN : 0 < N) (x : Circle)
    {δ : ℝ} (hδ : 0 < δ) (hbias : δ ≤ ‖geometricCharacterMean N x‖) :
    integerDistance x ≤ 1 / (2 * N * δ) := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hnorm : ‖geometricCharacterMean N x‖ = ‖geometricCharacterSum N x‖ / N := by
    rw [geometricCharacterMean_eq, norm_div]
    simp
  have hprod := two_mul_integerDistance_mul_norm_geometricCharacterSum_le_one N x
  have hsmall : (N : ℝ) * δ ≤ ‖geometricCharacterSum N x‖ := by
    rw [hnorm, le_div_iff₀ hN'] at hbias
    simpa only [mul_comm] using hbias
  have h := (mul_le_mul_of_nonneg_left hsmall
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (integerDistance_nonneg x))).trans hprod
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * N * δ)).mpr
  nlinarith only [h]

noncomputable def linearPhaseMean {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ι → ℕ) (a : ι → Circle) : ℂ :=
  𝔼 t : ∀ i, Fin (T i), character (∑ i, ((t i : ℕ) • a i))

theorem linearPhaseMean_eq_product {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ι → ℕ) (a : ι → Circle) :
    linearPhaseMean T a = ∏ i, geometricCharacterMean (T i) (a i) := by
  simp only [linearPhaseMean, character_fintype_sum, geometricCharacterMean]
  exact expect_pi_product (fun i (n : Fin (T i)) => character ((n : ℕ) • a i))

theorem geometric_mean_norm_ge_of_linear_bias {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → ℕ) (hT : ∀ i, 0 < T i) (a : ι → Circle) {δ : ℝ}
    (hbias : δ ≤ ‖linearPhaseMean T a‖) (i : ι) :
    δ ≤ ‖geometricCharacterMean (T i) (a i)‖ := by
  classical
  rw [linearPhaseMean_eq_product, norm_prod] at hbias
  apply hbias.trans
  have h := Finset.prod_le_prod_of_subset_of_le_one (Finset.singleton_subset_iff.mpr (Finset.mem_univ i))
    (fun j _ => norm_nonneg (geometricCharacterMean (T j) (a j)))
    (fun j _ _ => norm_geometricCharacterMean_le_one (T j) (hT j) (a j))
  simpa only [Finset.prod_singleton] using h

theorem linear_phase_near_integers {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → ℕ) (hT : ∀ i, 0 < T i) (a : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hbias : δ ≤ ‖linearPhaseMean T (fun i => (a i : Circle))‖) :
    ∀ i, |a i - round (a i)| ≤ 1 / (2 * T i * δ) := by
  intro i
  rw [← integerDistance_coe]
  exact integerDistance_le_of_geometric_mean (hT i) _ hδ
    (geometric_mean_norm_ge_of_linear_bias T hT _ hbias i)

end CircleFourier
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem integerBox_expect_eq_fin {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → ℕ) (f : (ι → ℤ) → ℂ) :
    (𝔼 x ∈ integerBox T, f x) = 𝔼 t : ∀ i, Fin (T i), f (fun i => ((t i : ℕ) : ℤ)) := by
  symm
  apply Finset.expect_bij (fun t _ i => ((t i : ℕ) : ℤ))
  · intro t _
    rw [mem_integerBox]
    exact fun i => ⟨Int.natCast_nonneg _, by exact_mod_cast (t i).isLt⟩
  · intro t _
    rfl
  · intro t _ u _ h
    funext i
    apply Fin.ext
    exact_mod_cast congrFun h i
  · intro x hx
    have hx' := (mem_integerBox T x).mp hx
    let t : ∀ i, Fin (T i) := fun i => ⟨(x i).toNat, by have := hx' i; omega⟩
    refine ⟨t, Finset.mem_univ _, ?_⟩
    funext i
    change ((x i).toNat : ℤ) = x i
    exact Int.toNat_of_nonneg (hx' i).1

namespace CircleFourier

theorem affinePhaseMean_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → ℕ) (c : ℂ) (a₀ : Circle) (a : ι → Circle) :
    (𝔼 t : ∀ i, Fin (T i), c * character (a₀ + ∑ i, (t i : ℕ) • a i)) =
      c * character a₀ * linearPhaseMean T a := by
  simp only [character_add, ← mul_assoc]
  rw [← Finset.mul_expect]
  rfl

theorem linearPhaseMean_norm_ge_of_affine_bias {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → ℕ) (c : ℂ) (a₀ : Circle) (a : ι → Circle)
    {M δ : ℝ} (hM : 0 < M) (hc : ‖c‖ ≤ M)
    (hbias : δ ≤ ‖𝔼 t : ∀ i, Fin (T i), c * character (a₀ + ∑ i, (t i : ℕ) • a i)‖) :
    δ / M ≤ ‖linearPhaseMean T a‖ := by
  rw [affinePhaseMean_eq, norm_mul, norm_mul, norm_character, mul_one] at hbias
  apply (div_le_iff₀ hM).mpr
  exact hbias.trans ((mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans_eq (mul_comm _ _))

end CircleFourier
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
open CircleFourier

theorem nearIntegerDensity_product {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → ℝ) (ε : ℝ) :
    nearIntegerDensity (fun p : X × Y => f p.1 p.2) ε =
      𝔼 x, nearIntegerDensity (f x) ε := by
  unfold nearIntegerDensity
  exact Finset.expect_product' _ _ (fun x y => if NearInteger ε (f x y) then (1 : ℝ) else 0)

theorem nearIntegerDensity_of_geometric_mean {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) {M : ℕ} (hM : 0 < M) {a : ℝ} (ha : 0 < a)
    (hbias : a ≤ 𝔼 x, ‖geometricCharacterMean M (f x : CircleFourier.Circle)‖) :
    a/2 ≤ nearIntegerDensity f (1/((M : ℝ)*a)) := by
  obtain ⟨S, hS, hgood⟩ := exists_dense_level_set
    (fun x => ‖geometricCharacterMean M (f x : CircleFourier.Circle)‖) ha.le
    (fun x => norm_geometricCharacterMean_le_one M hM _) hbias
  have hX : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  apply ((le_div_iff₀ hX).mpr hS).trans
  apply card_div_le_nearIntegerDensity _ _ S
  intro x hx
  have hnear := integerDistance_le_of_geometric_mean hM (f x : CircleFourier.Circle)
    (by linarith : 0 < a/2) (hgood x hx)
  refine ⟨round (f x), ?_⟩
  rw [← integerDistance_coe]
  apply hnear.trans_eq
  congr 1
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem nearIntegerDensity_comp_injective {X Y : Type*}
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (a : Y → ℝ) (ε : ℝ) (f : X → Y) (hf : Function.Injective f) :
    (Fintype.card X : ℝ)*nearIntegerDensity (fun x => a (f x)) ε ≤
      (Fintype.card Y : ℝ)*nearIntegerDensity a ε := by
  let S := Finset.univ.filter (fun x => NearInteger ε (a (f x)))
  let T := Finset.univ.filter (fun y => NearInteger ε (a y))
  have hST : S.image f ⊆ T := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
  have hcard : (S.card : ℝ) ≤ T.card := by
    exact_mod_cast (Finset.card_image_of_injective S hf ▸ Finset.card_le_card hST)
  have hX : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hY : (Fintype.card Y : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simpa only [nearIntegerDensity_eq_card, S, T, mul_div_cancel₀ _ hX,
    mul_div_cancel₀ _ hY] using hcard

theorem nearIntegerDensity_fiber_injections {X Y Z : Type*}
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    [Fintype Z] [Nonempty Z]
    (a : Y → ℝ) (ε : ℝ) (f : Z → X → Y) (hf : ∀ z, Function.Injective (f z))
    {η : ℝ} (hdensity : η ≤ 𝔼 z, nearIntegerDensity (fun x => a (f z x)) ε) :
    η * Fintype.card X / Fintype.card Y ≤ nearIntegerDensity a ε := by
  have hY : (0 : ℝ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hY).mpr
  have hp := Finset.expect_le_expect (fun z (_ : z ∈ (Finset.univ : Finset Z)) =>
    nearIntegerDensity_comp_injective a ε (f z) (hf z))
  rw [← Finset.mul_expect, Fintype.expect_const] at hp
  have hm := mul_le_mul_of_nonneg_left hdensity (Nat.cast_nonneg (Fintype.card X))
  nlinarith only [hm, hp]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem nearInteger_multiples {X : Type*} [Fintype X] [Nonempty X]
    (v : X → ℤ) (hv : Function.Injective v) (A H : ℕ) (hA : 1 ≤ A)
    (hH : 4*A ≤ H) (hcard : H ≤ Fintype.card X) (hbound : ∀ x, |v x| ≤ (H : ℤ))
    {θ ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ 1/(64*(A : ℝ)^2))
    (hdensity : 1/(A : ℝ) ≤ nearIntegerDensity (fun x => (v x : ℝ)*θ) ε) :
    ∃ q : ℕ, 0 < q ∧ q ≤ 4*A ∧ NearInteger (96*(A : ℝ)^2*ε/H) ((q : ℝ)*θ) := by
  have hAp : (0 : ℝ) < A := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hA)
  have hHp : 0 < H := by omega
  have hHr : (0 : ℝ) < H := Nat.cast_pos.mpr hHp
  let S := Finset.univ.filter (fun x => NearInteger ε ((v x : ℝ)*θ))
  let D := S.image v
  have hDcard : D.card = S.card := Finset.card_image_of_injective S hv
  have hs : (1/(A : ℝ))*H ≤ (D.card : ℝ) := by
    have hX : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
    have hden : 1/(A : ℝ) ≤ (S.card : ℝ)/Fintype.card X := by
      simpa only [nearIntegerDensity_eq_card] using hdensity
    rw [hDcard]
    exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (by positivity)).trans
      ((le_div_iff₀ hX).mp hden)
  have hnear : ∀ n ∈ D, NearInteger ε ((n : ℝ)*θ) := by
    intro n hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
    exact (Finset.mem_filter.mp hx).2
  let p : ℤ → ℤ := fun n => if hn : NearInteger ε ((n : ℝ)*θ) then hn.choose else 0
  have hp : ∀ n ∈ D, |(n : ℝ)*θ-p n| ≤ ε := by
    intro n hn
    dsimp only [p]
    rw [dif_pos (hnear n hn)]
    exact (hnear n hn).choose_spec
  have hρQ : (4 : ℝ) ≤ (1/(A : ℝ))*(4*A : ℕ) := by
    push_cast
    field_simp
    norm_num
  have hρH : (4 : ℝ) ≤ (1/(A : ℝ))*H := by
    calc
      _ ≤ (1/(A : ℝ))*(4*A : ℕ) := hρQ
      _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hH) (by positivity)
  have hsmall' : 16*((4*A : ℕ) : ℝ)*ε ≤ 1/(A : ℝ) := by
    calc
      _ ≤ 16*((4*A : ℕ) : ℝ)*(1/(64*(A : ℝ)^2)) := by gcongr
      _ = _ := by push_cast; field_simp; ring
  have hsmall'' : 16*(((4*A : ℕ) : ℝ)*ε) ≤ 1/(A : ℝ) := by linarith [hsmall']
  have hρone : 1/(A : ℝ) ≤ 1 := (div_le_one hAp).mpr (by exact_mod_cast hA)
  have hcap : ((4*A : ℕ) : ℝ)*ε ≤ 1 := by
    have hz : 0 ≤ ((4*A : ℕ) : ℝ)*ε := by positivity
    linarith
  obtain ⟨q, hq, hqA, m, hm⟩ := many_multiples_rational_approximation D p hHp (by omega)
    (by positivity : 0 < 1/(A : ℝ)) hε hρQ hρH hsmall'' hcap hs
    (fun n hn => by obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hn; exact hbound x) hp
  refine ⟨q, hq, hqA, m, hm.trans_eq ?_⟩
  push_cast
  field_simp
  ring

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

theorem expect_dependent_fin_cons {n : ℕ} {X : Fin (n+1) → Type*}
    [∀ i, Fintype (X i)] {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M]
    (F : (∀ i, X i) → M) :
    (𝔼 x, F x) = 𝔼 a : X 0, 𝔼 y : ∀ i : Fin n, X i.succ, F (Fin.cons a y) := by
  calc
    (𝔼 x, F x) = 𝔼 p : X 0 × (∀ i : Fin n, X i.succ), F (Fin.cons p.1 p.2) := by
      apply Fintype.expect_equiv (Fin.consEquiv X).symm
      intro x
      congr 1
      simp
    _ = _ := by
      simpa using (Finset.expect_product' (Finset.univ : Finset (X 0))
        (Finset.univ : Finset (∀ i : Fin n, X i.succ)) (fun a y => F (Fin.cons a y)))

theorem nearIntegerDensity_product_cons {n : ℕ} {X : Fin (n+1) → Type*}
    [∀ i, Fintype (X i)] (v : ∀ i, X i → ℤ) (θ ε : ℝ) :
    nearIntegerDensity (fun x : ∀ i, X i => θ * ∏ i, (v i (x i) : ℝ)) ε =
      𝔼 y : ∀ i : Fin n, X i.succ,
        nearIntegerDensity (fun a : X 0 =>
          (v 0 a : ℝ) * (θ * ∏ i : Fin n, (v i.succ (y i) : ℝ))) ε := by
  unfold nearIntegerDensity
  rw [expect_dependent_fin_cons, Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro y _
  apply Finset.expect_congr rfl
  intro a _
  congr 2
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

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

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

theorem complexMean_const {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X) (z : ℂ) :
    p.complexMean (fun _ => z) = z := by
  unfold complexMean
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, p.total, Complex.ofReal_one, one_mul]

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem dense_product_fiber {X Y : Type*} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (v : X → ℤ) (hv : Function.Injective v) (a : Y → ℝ) (B H : ℕ) (hB : 1 ≤ B)
    (hH : 8*B ≤ H) (hcard : H ≤ Fintype.card X) (hbound : ∀ x, |v x| ≤ (H : ℤ))
    {ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ 1/(256*(B : ℝ)^2))
    (hdensity : 1/(B : ℝ) ≤ 𝔼 y, nearIntegerDensity (fun x => (v x : ℝ)*a y) ε) :
    ∃ q : ℕ, 0 < q ∧ q ≤ 8*B ∧
      1/(16*(B : ℝ)^2) ≤ nearIntegerDensity (fun y => (q : ℝ)*a y) (384*(B : ℝ)^2*ε/H) := by
  have hBp : (0 : ℝ) < B := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hB)
  obtain ⟨S, hS, hfibers⟩ := exists_dense_level_set
    (fun y => nearIntegerDensity (fun x => (v x : ℝ)*a y) ε)
    (show 0 ≤ 1/(B : ℝ) by positivity) (fun y => nearIntegerDensity_le_one _ _) hdensity
  have hchoice : ∀ y : Y, ∃ q : ℕ, 0 < q ∧ q ≤ 8*B ∧
      (y ∈ S → NearInteger (384*(B : ℝ)^2*ε/H) ((q : ℝ)*a y)) := by
    intro y
    by_cases hy : y ∈ S
    · have hsmall' : ε ≤ 1/(64*((2*B : ℕ) : ℝ)^2) := by
        convert hsmall using 1
        push_cast
        ring
      have hd : 1/((2*B : ℕ) : ℝ) ≤ nearIntegerDensity (fun x => (v x : ℝ)*a y) ε := by
        have he : 1/((2*B : ℕ) : ℝ) = (1/(B : ℝ))/2 := by push_cast; field_simp
        rw [he]
        exact hfibers y hy
      obtain ⟨q, hq, hqB, hnear⟩ := nearInteger_multiples v hv (2*B) H (by omega)
        (by omega) hcard hbound hε hsmall' hd
      refine ⟨q, hq, by omega, fun _ => ?_⟩
      have he : 96*((2*B : ℕ) : ℝ)^2*ε/H = 384*(B : ℝ)^2*ε/H := by push_cast; ring
      rwa [he] at hnear
    · exact ⟨1, by omega, by omega, fun hy' => (hy hy').elim⟩
  choose q hq hqB hnear using hchoice
  have hpigeon : ((8*B : ℕ) : ℝ)*((1/(16*(B : ℝ)^2))*Fintype.card Y) ≤ S.card := by
    have he : ((8*B : ℕ) : ℝ)*((1/(16*(B : ℝ)^2))*Fintype.card Y) =
        (1/(B : ℝ))/2*Fintype.card Y := by push_cast; field_simp; ring
    rw [he]
    exact hS
  obtain ⟨q₀, hq₀, hq₀B, E, hES, hE, hconst⟩ :=
    exists_constant_denominator_fiber S q (by omega : 0 < 8*B)
      (fun y _ => ⟨hq y, hqB y⟩) hpigeon
  refine ⟨q₀, hq₀, hq₀B, ?_⟩
  have hY : (0 : ℝ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos
  apply ((le_div_iff₀ hY).mpr hE).trans
  apply card_div_le_nearIntegerDensity _ _ E
  intro y hy
  rw [← hconst y hy]
  exact hnear y (hES hy)

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

section

namespace Erdos3

open scoped BigOperators Classical

theorem dense_product_approximation (e B : ℕ) (hB : 1 ≤ B)
    {X : Fin e → Type*} [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    (v : ∀ i, X i → ℤ) (hv : ∀ i, Function.Injective (v i)) (N : Fin e → ℕ)
    (hN : ∀ i, denseProductBudget e B ≤ N i)
    (hcard : ∀ i, N i ≤ Fintype.card (X i))
    (hbound : ∀ i x, |v i x| ≤ (N i : ℤ))
    {θ ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ 1/(denseProductBudget e B : ℝ))
    (hdensity : 1/(B : ℝ) ≤
      nearIntegerDensity (fun x : ∀ i, X i => θ * ∏ i, (v i (x i) : ℝ)) ε) :
    ∃ q : ℕ, 0 < q ∧ q ≤ denseProductBudget e B ∧
      NearInteger ((denseProductBudget e B : ℝ)*ε / ∏ i, (N i : ℝ)) ((q : ℝ)*θ) := by
  induction e generalizing B θ ε with
  | zero =>
    have hBp : (0 : ℝ) < B := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hB)
    have hd : 0 < nearIntegerDensity (fun _ : ∀ i, X i => θ) ε := by
      simpa only [Fin.prod_univ_zero, mul_one] using
        (lt_of_lt_of_le (one_div_pos.mpr hBp) hdensity)
    refine ⟨1, by omega, le_rfl, ?_⟩
    simpa only [denseProductBudget, Nat.cast_one, one_mul, Fin.prod_univ_zero, div_one]
      using nearInteger_of_pos_density_const hd
  | succ e ih =>
    let C := denseProductBudget e (16*B^2)
    let K := denseProductBudget (e+1) B
    obtain ⟨h8, hCK, h256, h384, h8C⟩ := denseProductBudget_step_bounds e B hB
    have hB' : 1 ≤ 16*B^2 := by nlinarith
    have hCp : (0 : ℝ) < C := by exact_mod_cast denseProductBudget_pos e (16*B^2) hB'
    have hKp : (0 : ℝ) < K := by exact_mod_cast denseProductBudget_pos (e+1) B hB
    have hNp : ∀ i, (0 : ℝ) < N i := by
      intro i
      exact_mod_cast (lt_of_lt_of_le (denseProductBudget_pos (e+1) B hB) (hN i))
    have hN1 : (1 : ℝ) ≤ N 0 := by
      exact_mod_cast (lt_of_lt_of_le (denseProductBudget_pos (e+1) B hB) (hN 0))
    have hcoef : 384*(B : ℝ)^2*C ≤ K := by exact_mod_cast h384
    have hsmall' : ε ≤ 1/(256*(B : ℝ)^2) := by
      apply hsmall.trans
      apply one_div_le_one_div_of_le
      · have hBp : (0 : ℝ) < B := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hB)
        positivity
      · exact_mod_cast h256
    obtain ⟨q₀, hq₀, hq₀B, hd⟩ := dense_product_fiber (v 0) (hv 0)
      (fun y : ∀ i : Fin e, X i.succ => θ * ∏ i, (v i.succ (y i) : ℝ)) B (N 0) hB
      (h8.trans (hN 0)) (hcard 0) (hbound 0) hε hsmall'
      (by rwa [nearIntegerDensity_product_cons] at hdensity)
    let δ := 384*(B : ℝ)^2*ε/N 0
    have hδ : 0 ≤ δ := by dsimp [δ]; positivity
    have hδsmall : δ ≤ 1/(denseProductBudget e (16*B^2) : ℝ) :=
      dense_product_step_tolerance hCp hN1 hKp hcoef hε hsmall
    have hd' : 1/((16*B^2 : ℕ) : ℝ) ≤ nearIntegerDensity
        (fun y : ∀ i : Fin e, X i.succ => ((q₀ : ℝ)*θ) * ∏ i, (v i.succ (y i) : ℝ)) δ := by
      simpa only [δ, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using hd
    obtain ⟨q₁, hq₁, hq₁C, hnear⟩ := ih (16*B^2) hB'
      (fun i => v i.succ) (fun i => hv i.succ) (fun i => N i.succ)
      (fun i => hCK.trans (hN i.succ)) (fun i => hcard i.succ)
      (fun i => hbound i.succ) hδ hδsmall hd'
    refine ⟨q₁*q₀, Nat.mul_pos hq₁ hq₀, ?_, ?_⟩
    · calc
        q₁*q₀ ≤ C*(8*B) := Nat.mul_le_mul hq₁C hq₀B
        _ = 8*B*C := by ring
        _ ≤ K := h8C
    · have hP : 0 < ∏ i : Fin e, (N i.succ : ℝ) :=
        Finset.prod_pos (fun i _ => hNp i.succ)
      have herror := dense_product_error_composition (hNp 0) hP hcoef hε
      have hresult := nearInteger_mono hnear herror
      simpa only [Nat.cast_mul, Fin.prod_univ_succ, mul_assoc] using hresult

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerFiberUniformBound
namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

noncomputable def normalizedIntegerColumns (B : Matrix I J ℤ) (T : J → ℝ) (P : I → ℝ) :
    Matrix I J ℝ :=
  Matrix.diagonal (fun i => (P i)⁻¹) * B.map (Int.castRingHom ℝ) * Matrix.diagonal T

noncomputable def normalizedPivotEquiv (A : Matrix I I ℤ) (hA : A.det ≠ 0)
    (S P : I → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) :
    (I → ℝ) ≃L[ℝ] (I → ℝ) :=
  (matrixSupCLM_inverse_spec (normalizedIntegerPivot A S P)
    (normalizedIntegerPivot_det_ne_zero A hA S P hS hP)).1.choose

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

noncomputable def scaledIntegerWeight (f : (J → ℝ) × (I → ℝ) → ℝ)
    (S : I → ℝ) (T : J → ℝ) (p : (I → ℤ) × (J → ℤ)) : ℝ :=
  f ((fun j => (p.2 j : ℝ) / T j), (fun i => (p.1 i : ℝ) / S i))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Matrix BigOperators NNReal

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

noncomputable def scaledIntegerFiberOutputMass (A : Matrix I I ℤ) (B : Matrix I J ℤ)
    (S P : I → ℝ) (T : J → ℝ) (f : (J → ℝ) × (I → ℝ) → ℝ) (v : I → ℤ) : ℝ :=
  ((∏ i, P i) / ((∏ i, S i) * (∏ j, T j))) *
    ∑' p : {p : (I → ℤ) × (J → ℤ) // A *ᵥ p.1 + B *ᵥ p.2 = v}, scaledIntegerWeight f S T p.val

noncomputable def normalizedFiberDensity (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i)
    (f : (J → ℝ) × (I → ℝ) → ℝ) : (I → ℝ) → ℝ :=
  pivotOutputDensity (normalizedPivotEquiv A hA S P hS hP)
    (matrixSupCLM (normalizedIntegerColumns B T P)) f

end Erdos3

end

section

namespace Erdos3

open scoped Matrix NNReal

noncomputable def integerFiberErrorConstant (j d : ℕ) (G U V R : ℝ) (K : ℝ≥0) : ℝ :=
  G * (j.factorial * U ^ j) * (2 * R + 2) ^ d * K * max 1 (U * V)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SmoothProbabilityProfile
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff

noncomputable def probabilityProfileBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 2, 3 / 4, by norm_num, by norm_num⟩

noncomputable def smoothProbabilityProfile : ℝ → ℝ :=
  probabilityProfileBump.normed volume

theorem smoothProbabilityProfile_contDiff : ContDiff ℝ ∞ smoothProbabilityProfile :=
  probabilityProfileBump.contDiff_normed

theorem smoothProbabilityProfile_compact : HasCompactSupport smoothProbabilityProfile :=
  probabilityProfileBump.hasCompactSupport_normed

theorem smoothProbabilityProfile_range (x : ℝ) :
    0 ≤ smoothProbabilityProfile x ∧ smoothProbabilityProfile x ≤ 1 := by
  refine ⟨probabilityProfileBump.nonneg_normed x, ?_⟩
  have h := probabilityProfileBump.normed_le_div_measure_closedBall_rIn volume x
  norm_num [probabilityProfileBump] at h
  exact h

theorem smoothProbabilityProfile_zero (x : ℝ) (hx : 3 / 4 ≤ |x|) :
    smoothProbabilityProfile x = 0 := by
  have h : probabilityProfileBump x = 0 := probabilityProfileBump.zero_of_le_dist
    (by simpa only [probabilityProfileBump, Real.dist_eq, sub_zero] using hx)
  simp only [smoothProbabilityProfile, ContDiffBump.normed_def, h, zero_div]

theorem smoothProbabilityProfile_zero_outside (x : ℝ) (hx : 1 < |x|) :
    smoothProbabilityProfile x = 0 :=
  smoothProbabilityProfile_zero x (by linarith)

theorem smoothProbabilityProfile_integral : (∫ x, smoothProbabilityProfile x) = 1 :=
  probabilityProfileBump.integral_normed

theorem smoothProbabilityProfile_pos_zero : 0 < smoothProbabilityProfile 0 := by
  have h : probabilityProfileBump 0 = 1 := probabilityProfileBump.one_of_mem_closedBall
    (by simp [probabilityProfileBump])
  change 0 < probabilityProfileBump 0 / ∫ x, probabilityProfileBump x
  rw [h]
  exact one_div_pos.mpr probabilityProfileBump.integral_pos

theorem exists_smoothProbabilityProfile_lipschitz :
    ∃ A : ℝ≥0, 1 ≤ A ∧ LipschitzWith A smoothProbabilityProfile := by
  obtain ⟨A, hA⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    smoothProbabilityProfile_compact (smoothProbabilityProfile_contDiff.of_le (by simp) :
      ContDiff ℝ 1 smoothProbabilityProfile) one_ne_zero
  exact ⟨A + 1, by simp, hA.weaken (by simp)⟩

noncomputable def probabilityProfileLipschitz : ℝ≥0 :=
  exists_smoothProbabilityProfile_lipschitz.choose

theorem probabilityProfileLipschitz_one_le : 1 ≤ probabilityProfileLipschitz :=
  exists_smoothProbabilityProfile_lipschitz.choose_spec.1

theorem smoothProbabilityProfile_lipschitz :
    LipschitzWith probabilityProfileLipschitz smoothProbabilityProfile :=
  exists_smoothProbabilityProfile_lipschitz.choose_spec.2

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SplitSmoothProductProfile
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def splitInputProfile (f : (J → ℝ) × (I → ℝ) → ℝ) (x : J ⊕ I → ℝ) : ℝ :=
  f ((fun j => x (.inl j)), (fun i => x (.inr i)))

theorem splitCoordinates_norm (x : J ⊕ I → ℝ) :
    ‖((fun j => x (.inl j)), (fun i => x (.inr i)))‖ = ‖x‖ := by
  apply le_antisymm
  · change max ‖fun j => x (.inl j)‖ ‖fun i => x (.inr i)‖ ≤ ‖x‖
    apply max_le
    · exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun j => norm_le_pi_norm x (.inl j)
    · exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun i => norm_le_pi_norm x (.inr i)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro k
    cases k with
    | inl j =>
      exact (norm_le_pi_norm (fun j => x (.inl j)) j).trans
        (norm_fst_le ((fun j => x (.inl j)), (fun i => x (.inr i))))
    | inr i =>
      exact (norm_le_pi_norm (fun i => x (.inr i)) i).trans
        (norm_snd_le ((fun j => x (.inl j)), (fun i => x (.inr i))))

theorem splitInputProfile_zero_outside {f : (J → ℝ) × (I → ℝ) → ℝ} {R : ℝ}
    (hf : ∀ p, R < ‖p‖ → f p = 0) (x : J ⊕ I → ℝ) (hx : R < ‖x‖) :
    splitInputProfile f x = 0 :=
  hf _ (by rwa [splitCoordinates_norm])

omit [Fintype I] [Fintype J] in
theorem splitInputProfile_sample_sum (f : (J → ℝ) × (I → ℝ) → ℝ) (S : I → ℝ) (T : J → ℝ) :
    (∑' z : J ⊕ I → ℤ, splitInputProfile f (fun k => (z k : ℝ) / Sum.elim T S k)) =
      ∑' p : (I → ℤ) × (J → ℤ), scaledIntegerWeight f S T p := by
  let e : (J ⊕ I → ℤ) ≃ (I → ℤ) × (J → ℤ) :=
    (Equiv.sumPiEquivProdPi (fun _ : J ⊕ I => ℤ)).trans (Equiv.prodComm _ _)
  exact e.tsum_eq (scaledIntegerWeight f S T)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

def tensorCutoffWeight {ι : Type*} {E : ι → Type*} [Fintype ι] (w : ∀ i, E i → ℝ) (x : ∀ i, E i) : ℝ :=
  ∏ i, w i (x i)

theorem tensorCutoffWeight_nonneg {ι : Type*} {E : ι → Type*} [Fintype ι]
    (w : ∀ i, E i → ℝ) (hw : ∀ i x, 0 ≤ w i x) (x : ∀ i, E i) :
    0 ≤ tensorCutoffWeight w x := Finset.prod_nonneg (fun i _ => hw i (x i))

theorem tensorCutoffWeight_integral {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, MeasureSpace (E i)]
    [∀ i, SigmaFinite (volume : Measure (E i))] (w : ∀ i, E i → ℝ) :
    (∫ x, tensorCutoffWeight w x) = ∏ i, ∫ y, w i y :=
  integral_fintype_prod_volume_eq_prod w

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def scaledInputWeightSum (f : (J → ℝ) × (I → ℝ) → ℝ)
    (S : I → ℝ) (T : J → ℝ) : ℝ := ∑' p : (I → ℤ) × (J → ℤ), scaledIntegerWeight f S T p

noncomputable def scaledInputMass (f : (J → ℝ) × (I → ℝ) → ℝ)
    (S : I → ℝ) (T : J → ℝ) : ℝ := scaledInputWeightSum f S T / ((∏ i, S i) * (∏ j, T j))

theorem scaledIntegerWeight_summable (f : (J → ℝ) × (I → ℝ) → ℝ) (S : I → ℝ) (T : J → ℝ)
    (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) {R : ℝ}
    (hsupport : ∀ p, R < ‖p‖ → f p = 0) : Summable (scaledIntegerWeight f S T) := by
  let e : (J ⊕ I → ℤ) ≃ (I → ℤ) × (J → ℤ) :=
    (Equiv.sumPiEquivProdPi (fun _ : J ⊕ I => ℤ)).trans (Equiv.prodComm _ _)
  have hscale : ∀ k, 0 < Sum.elim T S k := by intro k; cases k <;> simp [hS, hT]
  have h := scaledRectangularWeight_summable (splitInputProfile f) (fun _ => 0)
    (Sum.elim T S) (m := 1) zero_lt_one hscale (splitInputProfile_zero_outside hsupport)
  have heq (z : J ⊕ I → ℤ) : scaledIntegerWeight f S T (e z) =
      splitInputProfile f (fun k => (z k : ℝ) / Sum.elim T S k) := rfl
  have hs : Summable (fun z => scaledIntegerWeight f S T (e z)) := by
    simpa only [heq, zero_add, one_mul] using h
  exact e.summable_iff.mp hs

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {D : Type*} [Fintype D] {I : D → Type*} [∀ d, Fintype (I d)]

noncomputable def sigmaAxisWeight (w : ∀ d, (I d → ℝ) → ℝ) (x : (Σ d, I d) → ℝ) : ℝ :=
  tensorCutoffWeight w (sigmaAxisCoordinates I x)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

noncomputable def smoothProductProfile (I : Type*) [Fintype I] (x : I → ℝ) : ℝ :=
  ∏ i, smoothProbabilityProfile (x i)

theorem smoothProductProfile_eq_cutoff (I : Type*) [Fintype I] :
    smoothProductProfile I = coordinateBoxCutoff smoothProbabilityProfile 1 := by
  funext x
  simp [smoothProductProfile, coordinateBoxCutoff]

theorem smoothProductProfile_contDiff (I : Type*) [Fintype I] :
    ContDiff ℝ ∞ (smoothProductProfile I) := by
  rw [smoothProductProfile_eq_cutoff]
  exact contDiff_coordinateBoxCutoff _ smoothProbabilityProfile_contDiff 1

theorem smoothProductProfile_compact (I : Type*) [Fintype I] :
    HasCompactSupport (smoothProductProfile I) := by
  rw [smoothProductProfile_eq_cutoff]
  exact hasCompactSupport_coordinateBoxCutoff _ smoothProbabilityProfile_zero zero_lt_one

theorem smoothProductProfile_range (I : Type*) [Fintype I] (x : I → ℝ) :
    0 ≤ smoothProductProfile I x ∧ smoothProductProfile I x ≤ 1 :=
  ⟨Finset.prod_nonneg (fun i _ => (smoothProbabilityProfile_range (x i)).1),
    Finset.prod_le_one (fun i _ => (smoothProbabilityProfile_range (x i)).1)
      (fun i _ => (smoothProbabilityProfile_range (x i)).2)⟩

theorem smoothProductProfile_zero_outside (I : Type*) [Fintype I]
    (x : I → ℝ) (hx : 1 < ‖x‖) : smoothProductProfile I x = 0 := by
  classical
  by_contra hn
  apply (not_le_of_gt hx)
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  by_contra! hi
  exact hn (Finset.prod_eq_zero (Finset.mem_univ i)
    (smoothProbabilityProfile_zero_outside (x i) hi))

theorem smoothProductProfile_integral (I : Type*) [Fintype I] :
    (∫ x, smoothProductProfile I x) = 1 := by
  change (∫ x, tensorCutoffWeight (fun _ : I => smoothProbabilityProfile) x) = 1
  rw [tensorCutoffWeight_integral]
  simp only [smoothProbabilityProfile_integral, Finset.prod_const_one]

theorem smoothProductProfile_lipschitz (I : Type*) [Fintype I] :
    LipschitzWith (Fintype.card I * probabilityProfileLipschitz) (smoothProductProfile I) := by
  rw [smoothProductProfile_eq_cutoff]
  simpa only [div_one, NNReal.coe_one] using
    lipschitz_coordinateBoxCutoff smoothProbabilityProfile probabilityProfileLipschitz 1
      zero_lt_one smoothProbabilityProfile_range smoothProbabilityProfile_lipschitz

theorem smoothProductProfile_sum (I J : Type*) [Fintype I] [Fintype J]
    (x : I → ℝ) (y : J → ℝ) :
    smoothProductProfile (I ⊕ J) (Sum.elim x y) =
      smoothProductProfile I x * smoothProductProfile J y := by
  simp [smoothProductProfile, Fintype.prod_sum_type]

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
open scoped BigOperators NNReal

noncomputable def splitSmoothProductProfile (J I : Type*) [Fintype J] [Fintype I]
    (p : (J → ℝ) × (I → ℝ)) : ℝ :=
  smoothProductProfile J p.1 * smoothProductProfile I p.2

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PhasePreservingCauchySchwarz
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mean_square_family_eq_cross_re {H Ω : Type*} [Fintype H] [Fintype Ω]
    (v : H → Ω → ℂ) :
    (𝔼 x, ‖𝔼 h, v h x‖ ^ 2) = (𝔼 h, 𝔼 k, 𝔼 x, v h x * star (v k x)).re := by
  simp_rw [square_norm_mean_eq_cross_re]
  rw [← expect_re, Finset.expect_comm]
  congr 1
  apply Finset.expect_congr rfl
  intro h _
  exact Finset.expect_comm _ _ _

theorem finite_family_cauchy_schwarz_re {H Ω : Type*} [Fintype H] [Fintype Ω]
    [Nonempty Ω] (B : Ω → ℂ) (v : H → Ω → ℂ) {M : ℝ} (hB : ∀ x, ‖B x‖ ≤ M) :
    ‖𝔼 x, B x * (𝔼 h, v h x)‖ ^ 2 ≤
      M ^ 2 * (𝔼 h, 𝔼 k, 𝔼 x, v h x * star (v k x)).re := by
  have hcs := norm_expect_mul_star_sq_le B (fun x => star (𝔼 h, v h x))
  simp only [star_star, norm_star] at hcs
  have hBM : (𝔼 x, ‖B x‖ ^ 2) ≤ M ^ 2 :=
    (Finset.expect_le_expect (fun x _ =>
      pow_le_pow_left₀ (norm_nonneg _) (hB x) 2)).trans_eq (Fintype.expect_const _)
  rw [← mean_square_family_eq_cross_re]
  exact hcs.trans (mul_le_mul_of_nonneg_right hBM
    (Finset.expect_nonneg (fun x _ => sq_nonneg _)))

end Erdos3

end

end OAI

end


