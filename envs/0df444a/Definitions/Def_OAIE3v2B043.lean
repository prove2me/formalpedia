-- Prove2me | Definitions.Def_OAIE3v2B043
-- name    : OAIE3v2B043
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:13:31.077247+00:00
-- url     : https://prove2.me/theorems/c3be8084-f7c7-468e-8182-0e6850eda55f
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 44 of 311
-- statement:
--   Definitions bundle 44 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B000`, `OAIE3v2B001`, `OAIE3v2B002`, `OAIE3v2B003`, `OAIE3v2B006`, `OAIE3v2B007`, `OAIE3v2B008`, `OAIE3v2B009`, `OAIE3v2B011`, `OAIE3v2B013` of this split.
--
--   Modules: `Estimates/CommonDenominatorMultiples.lean`, `Estimates/DenseProductApproximation.lean`, `Estimates/PartialComplexScaledQuadrature.lean`, `Estimates/PrincipalBlockExponent.lean`, `Estimates/RowShiftTopSymbol.lean`, `FixedDensity/GeneratorCells.lean`, `Fourier/BoxDifferenceCharacter.lean`, `Fourier/RectangularGridCharacter.lean`, `Geometry/BoxCornerMean.lean`, `Geometry/IntervalBoxDifference.lean`, `Lattices/IntegerFiberCount.lean`, `Lattices/NearIntegerMultiples.lean`, `Lattices/SelectedResidueApproximation.lean`, `Polynomial/CRTPolynomialChargeBound.lean`, `Polynomial/DiagonalTensorPolynomial.lean`, `Polynomial/MultiaffinePolynomialBias.lean`, `Polynomial/PhasePreservingCauchySchwarz.lean`, `Polynomial/PrincipalMonomialScale.lean`, `Sampling/RationalSpanGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B000
import Definitions.Def_OAIE3v2B001
import Definitions.Def_OAIE3v2B002
import Definitions.Def_OAIE3v2B003
import Definitions.Def_OAIE3v2B006
import Definitions.Def_OAIE3v2B007
import Definitions.Def_OAIE3v2B008
import Definitions.Def_OAIE3v2B009
import Definitions.Def_OAIE3v2B011
import Definitions.Def_OAIE3v2B013

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerFiberCount
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem count_integer_phase_fibers (D : Finset ℤ) (m : ℤ → ℤ)
    {H θ η : ℝ} (hH : 0 ≤ H) (hθ : 0 < θ) (hη : 0 ≤ η)
    (hD : ∀ h ∈ D, |(h : ℝ)| ≤ H)
    (hclose : ∀ h ∈ D, |(h : ℝ) * θ - m h| ≤ η) :
    (D.card : ℝ) ≤ (2 * H * θ + 2 * η + 1) * (2 * η / θ + 1) := by
  have hm (h : ℤ) (hh : h ∈ D) : |(m h : ℝ)| ≤ H * θ + η := by
    have ha := abs_le.mp (hD h hh)
    have he := abs_le.mp (hclose h hh)
    have hlo := mul_le_mul_of_nonneg_right ha.1 hθ.le
    have hhi := mul_le_mul_of_nonneg_right ha.2 hθ.le
    rw [abs_le]
    constructor <;> nlinarith only [hlo, hhi, he.1, he.2]
  have himage : ((D.image m).card : ℝ) ≤ 2 * H * θ + 2 * η + 1 := by
    apply card_integer_set_le_diameter_add_one _ (by positivity)
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    have hx' := abs_le.mp (hm x hx)
    have hy' := abs_le.mp (hm y hy)
    rw [abs_le]
    constructor <;> linarith
  have hfiber (a : ℤ) : ((D.filter (fun h => m h = a)).card : ℝ) ≤ 2 * η / θ + 1 := by
    apply card_integer_set_le_diameter_add_one _ (by positivity)
    intro x hx y hy
    obtain ⟨hx, hmx⟩ := Finset.mem_filter.mp hx
    obtain ⟨hy, hmy⟩ := Finset.mem_filter.mp hy
    have he₁ := abs_le.mp (hclose x hx)
    have he₂ := abs_le.mp (hclose y hy)
    rw [hmx] at he₁
    rw [hmy] at he₂
    apply (le_div_iff₀ hθ).mpr
    rw [← abs_of_pos hθ, ← abs_mul, abs_le]
    constructor <;> nlinarith only [he₁.1, he₁.2, he₂.1, he₂.2]
  calc
    (D.card : ℝ) = ∑ a ∈ D.image m, ((D.filter (fun h => m h = a)).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    _ ≤ ∑ _a ∈ D.image m, (2 * η / θ + 1) := Finset.sum_le_sum (fun a _ => hfiber a)
    _ = ((D.image m).card : ℝ) * (2 * η / θ + 1) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * H * θ + 2 * η + 1) * (2 * η / θ + 1) :=
      mul_le_mul_of_nonneg_right himage (by positivity)

theorem count_integer_phase_fibers_abs (D : Finset ℤ) (m : ℤ → ℤ)
    {H θ η : ℝ} (hH : 0 ≤ H) (hθ : θ ≠ 0) (hη : 0 ≤ η)
    (hD : ∀ h ∈ D, |(h : ℝ)| ≤ H)
    (hclose : ∀ h ∈ D, |(h : ℝ) * θ - m h| ≤ η) :
    (D.card : ℝ) ≤ (2 * H * |θ| + 2 * η + 1) * (2 * η / |θ| + 1) := by
  rcases lt_or_gt_of_ne hθ with ht | ht
  · have he : ∀ h ∈ D, |(h : ℝ) * (-θ) - ((-m h : ℤ) : ℝ)| ≤ η := by
      intro h hh
      simpa only [Int.cast_neg, mul_neg, neg_sub_neg, abs_sub_comm] using hclose h hh
    simpa only [abs_of_neg ht] using count_integer_phase_fibers D (fun h => -m h)
      hH (neg_pos.mpr ht) hη hD he
  · simpa only [abs_of_pos ht] using count_integer_phase_fibers D m hH ht hη hD hclose

theorem small_linear_phase_of_many_near_integers (D : Finset ℤ) (m : ℤ → ℤ)
    {H θ η ρ : ℝ} (hH : 0 < H) (hρ : 0 < ρ) (hη : 0 ≤ η) (hηone : η ≤ 1)
    (hsmall : 16 * η ≤ ρ) (hθsmall : |θ| ≤ 2 * η)
    (hsize : ρ * H ≤ (D.card : ℝ))
    (hD : ∀ h ∈ D, |(h : ℝ)| ≤ H)
    (hclose : ∀ h ∈ D, |(h : ℝ) * θ - m h| ≤ η) :
    |θ| ≤ 24 * η / (ρ * H) := by
  by_cases ht : θ = 0
  · rw [ht, abs_zero]
    positivity
  have hθ : 0 < |θ| := abs_pos.mpr ht
  have hc := count_integer_phase_fibers_abs D m hH.le ht hη hD hclose
  have hc' : ρ * H ≤ (2 * H * |θ| + 3) * (2 * η / |θ| + 1) := by
    apply hsize.trans (hc.trans _)
    apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hp := mul_le_mul_of_nonneg_right hc' hθ.le
  have hid : ((2 * H * |θ| + 3) * (2 * η / |θ| + 1)) * |θ| =
      4 * H * |θ| * η + 2 * H * |θ| ^ 2 + 6 * η + 3 * |θ| := by
    field_simp
    ring
  rw [hid] at hp
  have hsquare := mul_le_mul_of_nonneg_left hθsmall
    (show 0 ≤ 2 * H * |θ| by positivity)
  have hcost := mul_le_mul_of_nonneg_right hsmall
    (show 0 ≤ H * |θ| by positivity)
  apply (le_div_iff₀ (mul_pos hρ hH)).mpr
  nlinarith only [hp, hsquare, hcost, hθsmall]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonDenominatorMultiples
namespace OAI

section

namespace Erdos3

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RectangularGridCharacter
namespace OAI

section

open scoped BigOperators ComplexConjugate ENNReal Real

open _root_.Finset Function MeasureTheory _root_.Set

namespace Erdos3.CircleFourier

noncomputable section

theorem integerDistance_nonneg (x : Circle) : 0 ≤ integerDistance x := norm_nonneg x

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NearIntegerMultiples
namespace OAI

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProductApproximation
namespace OAI

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PartialComplexScaledQuadrature
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem sampledWeightIndices_mem_bound {a S R : ℝ} {k : ℤ}
    (hk : k ∈ sampledWeightIndices a S R) : |(k : ℝ) - a| ≤ S * R := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hk
  have hl := Int.ceil_le.mp hlo
  have hh := Int.le_floor.mp hhi
  rw [abs_le]
  constructor <;> linarith

theorem sampledWeightIndices_card_le (a S R : ℝ) (hS : 0 ≤ S) (hR : 0 ≤ R) :
    ((sampledWeightIndices a S R).card : ℝ) ≤ 2 * S * R + 1 := by
  apply card_integer_set_le_diameter_add_one _ (by positivity)
  intro x hx y hy
  have h := (abs_sub_le (x : ℝ) a y).trans
    (add_le_add (sampledWeightIndices_mem_bound hx)
      (by simpa only [abs_sub_comm] using sampledWeightIndices_mem_bound hy))
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem rectangularLatticePoint_sub_displacement {I : Type*} [Fintype I]
    (a S : I → ℝ) (k v : I → ℤ) :
    rectangularLatticePoint a S (k - v) - rectangularLatticePoint a S k =
      -rectangularLatticePoint 0 S v := by
  funext i
  simp only [rectangularLatticePoint, Pi.sub_apply, Pi.neg_apply, Pi.zero_apply, Int.cast_sub]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalSpanGrid
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι κ : Type*}

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def matrixDenominator (A : Matrix ι κ ℚ) : ℕ :=
  arrayDenominator (fun ij : ι × κ => A ij.1 ij.2)

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

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrincipalBlockExponent
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem productBlockExponent_monomial {K : Type*} {h : ℕ}
    (principal : Fin h → K) (c : ℝ) :
    MvPolynomial.monomial (productBlockExponent principal) c =
      MvPolynomial.C c * ∏ v, MvPolynomial.X (principal v) := by
  rw [productBlockExponent, MvPolynomial.monomial_sum_index]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BoxDifferenceCharacter
namespace OAI

section

namespace Erdos3

open CircleFourier

theorem character_real_sub (a b : ℝ) :
    character ((a-b : ℝ) : CircleFourier.Circle) =
      character (a : CircleFourier.Circle) * star (character (b : CircleFourier.Circle)) := by
  rw [sub_eq_add_neg, AddCircle.coe_add, AddCircle.coe_neg, character_add, character_neg]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxCornerMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem boxTestCorrelation_zero {X : Type*} [Fintype X]
    (F : (Fin 0 → X) → ℂ) (U : Fin 0 → (Fin 0 → X) → ℂ) :
    boxTestCorrelation F U = F (fun i => Fin.elim0 i) := by
  simp only [boxTestCorrelation, Fin.prod_univ_zero, mul_one, expect_empty_tuple]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem assignedBoxTest_misses {n : ℕ} {S X : Type*} [Fintype S]
    (assignment : S → Fin n) (U : S → (Fin n → X) → ℂ)
    (hU : ∀ s, MissesBoxCoordinate (U s) (assignment s)) (i : Fin n) :
    MissesBoxCoordinate (assignedBoxTest assignment U i) i := by
  intro x a
  apply Finset.prod_congr rfl
  intro s _
  by_cases hs : assignment s = i
  · simp only [hs, ite_true]
    simpa only [hs] using hU s x a
  · simp only [hs, ite_false]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PrincipalMonomialScale
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem monomialScale_productBlockExponent {K : Type*} {h : ℕ}
    (principal : Fin h → K) (T : K → ℝ) :
    monomialScale T (productBlockExponent principal) = ∏ v, T (principal v) := by
  have he := congrArg (MvPolynomial.eval T) (productBlockExponent_monomial principal (1 : ℝ))
  simpa only [MvPolynomial.eval_monomial, one_mul, map_mul, map_prod, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Finsupp.prod, monomialScale] using he

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

theorem intervalDifference_injective (N : ℕ) (y : Fin N) :
    Function.Injective (intervalDifference N y) := by
  intro x x' h
  have he := congrArg Subtype.val h
  dsimp [intervalDifference] at he
  apply Fin.ext
  omega

theorem intervalBoxDifference_injective {ι : Type*} (N : ι → ℕ)
    (y : ∀ i, Fin (N i)) : Function.Injective (intervalBoxDifference N y) := by
  intro x x' h
  funext i
  exact intervalDifference_injective (N i) (y i) (congrFun h i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MultiaffinePolynomialBias
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem norm_real_phase_double_mean_le_one {X Y : Type*}
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y] (F : X → Y → ℝ) :
    ‖𝔼 x, 𝔼 y, character (F x y : CircleFourier.Circle)‖ ≤ 1 := by
  calc
    _ ≤ 𝔼 x, ‖𝔼 y, character (F x y : CircleFourier.Circle)‖ :=
      RCLike.norm_expect_le (K := ℂ)
    _ ≤ 𝔼 x, 𝔼 y, ‖character (F x y : CircleFourier.Circle)‖ :=
      Finset.expect_le_expect (fun x _ => RCLike.norm_expect_le (K := ℂ))
    _ = 1 := by simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RowShiftTopSymbol
namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped BigOperators Classical

theorem rowShiftedSite_eq {h : ℕ} {K X V : Type*} [Fintype K] [AddCommGroup V]
    (site : K → ℤ) (base : K → V) (rows : Fin h → K → ℤ) (shift : X → V)
    (x : Fin h → X) :
    integerSiteValue site (rowShiftedTuple base rows shift x) =
      shiftedBoxSite (integerSiteValue site base) (fun i => ∑ k, rows i k * site k) shift x := by
  unfold integerSiteValue rowShiftedTuple shiftedBoxSite
  simp only [smul_add, Finset.smul_sum, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro k _
  simp only [smul_smul, mul_comm]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.GeneratorCells
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

namespace BooleanCutTest

def eval (A : BooleanCutTest Ω) : Ω → ℝ :=
  finsetIndicator A

end BooleanCutTest

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem integerRowShift_bound {K I : Type*} {h : ℕ} {N : I → ℕ}
    (rows : Fin h → K → ℤ) (s : I → ℕ) (x : Fin h → ∀ j, Fin (N j))
    {C : ℝ} (hC : 0 ≤ C) (hrows : ∀ i k, |(rows i k : ℝ)| ≤ C) (z : K × I) :
    |(integerRowShift rows s x z : ℝ)| ≤ (h : ℝ) * C * ((s z.2 : ℝ) * (N z.2 : ℝ)) := by
  simp only [integerRowShift, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  calc
    |∑ i, (rows i z.1 : ℝ) * ((s z.2 : ℝ) * ((x i z.2).val : ℝ))| ≤
        ∑ i, |(rows i z.1 : ℝ) * ((s z.2 : ℝ) * ((x i z.2).val : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin h, C * ((s z.2 : ℝ) * (N z.2 : ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg (s z.2))
        (Nat.cast_nonneg (x i z.2).val) : (0 : ℝ) ≤ (s z.2 : ℝ) * ((x i z.2).val : ℝ))]
      have hx : ((x i z.2).val : ℝ) ≤ (N z.2 : ℝ) := by exact_mod_cast (x i z.2).isLt.le
      exact mul_le_mul (hrows i z.1)
        (mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg _)) (by positivity) hC
    _ = _ := by simp; ring

theorem integerRowShift_normalized_bound {K I : Type*} [Fintype K] [Fintype I]
    {h : ℕ} {N : I → ℕ} (rows : Fin h → K → ℤ) (s : I → ℕ)
    (x : Fin h → ∀ j, Fin (N j)) (S : K × I → ℝ) (hS : ∀ z, 0 < S z)
    {C ε : ℝ} (hC : 0 ≤ C) (hrows : ∀ i k, |(rows i k : ℝ)| ≤ C) (hε : 0 ≤ ε)
    (hscale : ∀ z, (h : ℝ) * C * ((s z.2 : ℝ) * (N z.2 : ℝ)) ≤ ε * S z) :
    ‖rectangularLatticePoint 0 S (integerRowShift rows s x)‖ ≤ ε := by
  rw [rectangularLatticePoint_zero_origin]
  apply (pi_norm_le_iff_of_nonneg hε).mpr
  intro z
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (hS z)]
  apply (div_le_iff₀ (hS z)).mpr
  exact (integerRowShift_bound rows s x hC hrows z).trans (hscale z)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem residueLatticeArray_rowShift {K I : Type*} {h : ℕ} {N : I → ℕ}
    (residue : K × I → ℤ) (modulus : I → ℕ) (rows : Fin h → K → ℤ)
    (u : Fin h → ∀ j, Fin (N j)) (x : K × I → ℤ) (k : K) (j : I) :
    ((residueLatticeArray residue modulus (x + integerRowShift rows (fun _ => 1) u) (k, j) : ℤ) : ℝ) =
      rowShiftedTuple (fun k j => (residueLatticeArray residue modulus x (k, j) : ℝ)) rows
        (fun (y : ∀ j, Fin (N j)) j => (modulus j : ℝ) * ((y j).val : ℝ)) u k j := by
  simp only [residueLatticeArray, integerRowShift, rowShiftedTuple, Pi.add_apply,
    Int.cast_add, Int.cast_mul, Int.cast_sum, Int.cast_natCast, Nat.cast_one, one_mul,
    Finset.sum_apply, zsmul_eq_mul]
  rw [mul_add, Finset.mul_sum, ← add_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.mul_apply, Pi.intCast_apply]
  ring

theorem residueRowShift_normalized_bound {K I : Type*} [Fintype K] [Fintype I]
    {h : ℕ} {N : I → ℕ} (rows : Fin h → K → ℤ) (modulus : I → ℕ)
    (hmodulus : ∀ j, 0 < modulus j) (u : Fin h → ∀ j, Fin (N j))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    {C r : ℝ} (hC : 0 ≤ C) (hrows : ∀ i k, |(rows i k : ℝ)| ≤ C) (hr : 0 ≤ r)
    (hmove : ∀ z, (h : ℝ) * C * ((modulus z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * V z) :
    ‖rectangularLatticePoint 0 (residueProfileWidth modulus V)
      (integerRowShift rows (fun _ => 1) u)‖ ≤ r := by
  apply integerRowShift_normalized_bound rows (fun _ => 1) u _
    (residueProfileWidth_pos modulus V hmodulus hV) hC hrows hr
  intro z
  have hm : (0 : ℝ) < modulus z.2 := by exact_mod_cast hmodulus z.2
  simp only [Nat.cast_one, one_mul, residueProfileWidth]
  rw [← mul_div_assoc, le_div_iff₀ hm]
  calc
    (h : ℝ) * C * (N z.2 : ℝ) * (modulus z.2 : ℝ) =
      (h : ℝ) * C * ((modulus z.2 : ℝ) * (N z.2 : ℝ)) := by ring
    _ ≤ r * V z := hmove z

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialChargeBound
namespace OAI


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem degree_le_one_eq_constant_add_row {I R : Type*} [Fintype I] [CommRing R]
    (P : MvPolynomial I R) (hP : P.totalDegree ≤ 1) :
    P = C (P.coeff 0) + rowPolynomial (polynomialLinearRow P) := by
  have he : P = C (P.coeff 0) + homogeneousComponent 1 P := by
    have hd : P.totalDegree = 0 ∨ P.totalDegree = 1 := by omega
    rcases hd with hd | hd
    · rw [homogeneousComponent_eq_zero 1 P (by omega), add_zero]
      exact totalDegree_eq_zero_iff_eq_C.mp hd
    · simpa [hd, Finset.sum_range_succ] using (sum_homogeneousComponent P).symm
  have hr : polynomialLinearRow (homogeneousComponent 1 P) = polynomialLinearRow P := by
    funext i
    simp only [polynomialLinearRow, coeff_homogeneousComponent, Finsupp.degree_single, ite_true]
  exact he.trans (congrArg (fun Q => C (P.coeff 0) + Q)
    ((homogeneous_eq_rowPolynomial _ (homogeneousComponent_isHomogeneous 1 P)).trans
      (congrArg rowPolynomial hr)))

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DiagonalTensorPolynomial
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem tensorDiagonalPolynomial_eval {I R : Type*} [Fintype I] [CommSemiring R]
    {h : ℕ} (θ : (Fin h → I) → R) (w : I → R) :
    MvPolynomial.eval w (tensorDiagonalPolynomial θ) = ∑ j, θ j * ∏ i, w (j i) := by
  simp [tensorDiagonalPolynomial]

theorem tensorDiagonalPolynomial_add {I R : Type*} [Fintype I] [CommSemiring R]
    {h : ℕ} (θ ψ : (Fin h → I) → R) :
    tensorDiagonalPolynomial (fun j => θ j + ψ j) =
      tensorDiagonalPolynomial θ + tensorDiagonalPolynomial ψ := by
  simp [tensorDiagonalPolynomial, add_mul, Finset.sum_add_distrib]

theorem tensorDiagonalPolynomial_mul {I R : Type*} [Fintype I] [CommSemiring R]
    {h : ℕ} (c : R) (θ : (Fin h → I) → R) :
    tensorDiagonalPolynomial (fun j => c * θ j) = MvPolynomial.C c * tensorDiagonalPolynomial θ := by
  simp [tensorDiagonalPolynomial, Finset.mul_sum, mul_assoc]

theorem tensorDiagonalPolynomial_map {I R S : Type*} [Fintype I]
    [CommSemiring R] [CommSemiring S] {h : ℕ} (f : R →+* S) (θ : (Fin h → I) → R) :
    MvPolynomial.map f (tensorDiagonalPolynomial θ) = tensorDiagonalPolynomial (fun j => f (θ j)) := by
  simp [tensorDiagonalPolynomial]

theorem tensorDiagonalPolynomial_eq_sum_monomial {I : Type*} [Fintype I]
    {h : ℕ} (θ : (Fin h → I) → ℝ) :
    tensorDiagonalPolynomial θ = ∑ j, MvPolynomial.monomial (productBlockExponent j) (θ j) := by
  simp only [tensorDiagonalPolynomial, productBlockExponent_monomial]

theorem tensorDiagonalPolynomial_multilinear_eval {I R : Type*} [Fintype I]
    [DecidableEq I] [CommRing R] {h : ℕ}
    (F : MultilinearMap R (fun _ : Fin h => I → R) R) (w : I → R) :
    MvPolynomial.eval w
      (tensorDiagonalPolynomial (fun j => F (fun i => Pi.single (j i) (1 : R)))) = F (fun _ => w) := by
  rw [tensorDiagonalPolynomial_eval]
  exact (multilinear_diagonal_expansion F w).symm

end Erdos3

end

end OAI
end


