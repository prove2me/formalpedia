-- Prove2me | Definitions.Def_OAIErdos3B120
-- name    : OAIErdos3B120
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T04:15:00.483966+00:00
-- url     : https://prove2.me/theorems/0d7f48c7-7185-416f-bc82-cb9f7bda13d3
-- title:
--   OpenAI Erdős-3 split, definitions bundle 121 of 132
-- statement:
--   Definitions bundle 121 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B119`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 121 available.
--
--   Modules: `OAI.Erdos3.NativeCrossWitnesses.exists_quadruples`, `OAI.Erdos3.NativeCrossWitnesses.exists_quadruples_budget`, `OAI.Erdos3.NativeCrossWitnesses.exists_short_quadruples`, `OAI.Erdos3.NativeCrossWitnesses.restrict`, `OAI.Erdos3.NativeCrossWitnesses.restrict_extension_of_mem`, `OAI.Erdos3.NativeCrossWitnesses.restrict_quadruple`, `OAI.Erdos3.NativeVectorCorrelation.exists_absorb_positive`, `OAI.Erdos3.NilpotentLieFiltration.HasCommonRefilteredOrbitFactors`, `OAI.Erdos3.NilpotentLieFiltration.HasCommonRefilteredOrbitFactors.symbolFactors`, `OAI.Erdos3.NilpotentLieFiltration.PolynomialRationalGrid.to_symbol`, `OAI.Erdos3.NilpotentLieFiltration.PolynomialSlowBound.to_symbol`, `OAI.Erdos3.NilpotentLieFiltration.exists_common_refiltered_mapped_orbit_factors`, `OAI.Erdos3.NilpotentLieFiltration.exists_weighted_common_refiltered_orbit_factors`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialGroupMap_coefficient`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialGroupMap_middle_mem`, `OAI.Erdos3.RationalFilteredNilmanifold.HasFixedProductOrbitFactors`, `OAI.Erdos3.RationalFilteredNilmanifold.HasFixedProductOrbitFactors.mono`, `OAI.Erdos3.additiveQuadrupleCorrelation_real_scale`, `OAI.Erdos3.additiveQuadrupleCorrelation_support`, `OAI.Erdos3.cross_correlations_force_additive_quadruples`, `OAI.Erdos3.derivative_quadruple_exp_threshold`, `OAI.Erdos3.exists_many_correlated_additive_quadruples`, `OAI.Erdos3.exists_many_cross_correlated_quadruples`, `OAI.Erdos3.exists_weighted_common_fast_subalgebra`, `OAI.Erdos3.exists_weighted_common_fast_subalgebra_and_denominator`, `OAI.Erdos3.exists_weighted_common_positive_nat`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B039

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSelectedCorrelators
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem additiveQuadrupleCorrelation_support (g : G → G → ℂ) (H : Finset G)
    (hg : ∀ h, h ∉ H → ∀ x, g h x = 0) {a h k : G}
    (hpos : 0 < additiveQuadrupleCorrelation g a h k) :
    h ∈ H ∧ h - a ∈ H ∧ k ∈ H ∧ k - a ∈ H := by
  have hmem : h ∈ H := by
    by_contra hn
    simp [additiveQuadrupleCorrelation, hg h hn] at hpos
  have hsub : h - a ∈ H := by
    by_contra hn
    simp [additiveQuadrupleCorrelation, hg (h - a) hn] at hpos
  have hkmem : k ∈ H := by
    by_contra hn
    simp [additiveQuadrupleCorrelation, hg k hn] at hpos
  have hksub : k - a ∈ H := by
    by_contra hn
    simp [additiveQuadrupleCorrelation, hg (k - a) hn] at hpos
  exact ⟨hmem, hsub, hkmem, hksub⟩

theorem exists_many_correlated_additive_quadruples
    (f : G → ℂ) (g : G → G → ℂ) (H : Finset G)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ h x, ‖g h x‖ ≤ 1)
    (hzero : ∀ h, h ∉ H → ∀ x, g h x = 0)
    {alpha delta : ℝ} (halpha : 0 < alpha) (hdelta : 0 < delta)
    (hdense : alpha * Fintype.card G ≤ (H.card : ℝ))
    (hcorr : ∀ h ∈ H, delta ≤ ‖𝔼 x, multiplicativeDerivative f h x * star (g h x)‖) :
    ∃ Q : Finset (G × G × G), Q.Nonempty ∧
      (alpha * delta) ^ 4 / 2 * (Fintype.card G : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧
        t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H ∧
        (alpha * delta) ^ 4 / 2 ≤ additiveQuadrupleCorrelation g t.1 t.2.1 t.2.2 := by
  classical
  have hcardG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hindicator : (𝔼 h : G, if h ∈ H then delta else 0) =
      (H.card : ℝ) * delta / Fintype.card G := by
    rw [Fintype.expect_eq_sum_div_card]
    simp
  have hmean : alpha * delta ≤
      𝔼 h, ‖𝔼 x, multiplicativeDerivative f h x * star (g h x)‖ := by
    calc
      _ ≤ (H.card : ℝ) * delta / Fintype.card G := by
        apply (le_div_iff₀ hcardG).mpr
        nlinarith [mul_le_mul_of_nonneg_right hdense hdelta.le]
      _ = _ := hindicator.symm
      _ ≤ _ := by
        apply Finset.expect_le_expect
        intro h _
        split_ifs with hh
        · exact hcorr h hh
        · exact norm_nonneg _
  have hsplit : (𝔼 t : G × G × G, additiveQuadrupleCorrelation g t.1 t.2.1 t.2.2) =
      𝔼 a, 𝔼 h, 𝔼 k, additiveQuadrupleCorrelation g a h k := by
    simp only [← Finset.univ_product_univ, Finset.expect_product]
  have hquad : (alpha * delta) ^ 4 ≤
      𝔼 t : G × G × G, additiveQuadrupleCorrelation g t.1 t.2.1 t.2.2 := by
    rw [hsplit]
    exact (pow_le_pow_left₀ (mul_pos halpha hdelta).le hmean 4).trans
      (derivative_correlations_force_additive_quadruples f g hf)
  obtain ⟨Q, hQcard, hQ⟩ := exists_dense_level_set
    (fun t : G × G × G => additiveQuadrupleCorrelation g t.1 t.2.1 t.2.2)
    (by positivity : 0 ≤ (alpha * delta) ^ 4)
    (fun t => additiveQuadrupleCorrelation_le_one g hg t.1 t.2.1 t.2.2) hquad
  have hcards : (Fintype.card (G × G × G) : ℝ) = (Fintype.card G : ℝ) ^ 3 := by
    simp only [Fintype.card_prod, Nat.cast_mul]
    ring
  rw [hcards] at hQcard
  have hQnonempty : Q.Nonempty := by
    apply Finset.card_pos.mp
    have : (0 : ℝ) < (Q.card : ℝ) := lt_of_lt_of_le (by positivity) hQcard
    exact_mod_cast this
  refine ⟨Q, hQnonempty, hQcard, fun t ht => ?_⟩
  obtain ⟨h₁, h₂, h₃, h₄⟩ := additiveQuadrupleCorrelation_support g H hzero
    (lt_of_lt_of_le (by positivity) (hQ t ht))
  exact ⟨h₁, h₂, h₃, h₄, hQ t ht⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem additiveQuadrupleCorrelation_real_scale {G : Type*} [AddCommGroup G] [Fintype G]
    (g : G → G → ℂ) (c : ℝ) (hc : 0 ≤ c) (a h k : G) :
    additiveQuadrupleCorrelation (fun h x => (c : ℂ) * g h x) a h k =
      c ^ 4 * additiveQuadrupleCorrelation g a h k := by
  unfold additiveQuadrupleCorrelation
  have hmean : (𝔼 x, star ((c : ℂ) * g h x) * ((c : ℂ) * g (h - a) (x + a)) *
      ((c : ℂ) * g k x) * star ((c : ℂ) * g (k - a) (x + a))) =
      (c : ℂ) ^ 4 * (𝔼 x, star (g h x) * g (h - a) (x + a) * g k x * star (g (k - a) (x + a))) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  rw [hmean, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]

theorem derivative_quadruple_exp_threshold (p : ℝ) :
    (Real.exp (-p) * Real.exp (-(2 * p))) ^ 4 / 2 = Real.exp (-(12 * p)) / 2 := by
  rw [← Real.exp_add, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem cross_correlations_force_additive_quadruples
    (f₀ f₁ : G → ℂ) (g : G → G → ℂ)
    (hf₀ : ∀ x, ‖f₀ x‖ ≤ 1) (hf₁ : ∀ x, ‖f₁ x‖ ≤ 1) :
    (𝔼 h, ‖𝔼 x, (f₀ x * star (f₁ (x + h))) * star (g h x)‖) ^ 4 ≤
      𝔼 a, 𝔼 h, 𝔼 k, additiveQuadrupleCorrelation g a h k := by
  let C (a : G) := 𝔼 h, ‖𝔼 x, multiplicativeDerivative f₀ a x *
    (star (g h x) * g (h - a) (x + a))‖
  have hfirst : (𝔼 h, ‖𝔼 x, (f₀ x * star (f₁ (x + h))) * star (g h x)‖) ^ 2 ≤
      𝔼 a, C a := by
    have hcs := shifted_test_cauchy_schwarz f₀ (fun x => star (f₁ x))
      (fun h x => star (g h x)) (M := 1) (by simpa only [norm_star] using hf₁)
    have hreindex : (𝔼 h, 𝔼 k, ‖𝔼 x, f₀ x * star (f₀ (x + h - k)) *
        star (g h x) * g k (x + h - k)‖) = 𝔼 a, C a := by
      calc
        _ = 𝔼 h, 𝔼 a, ‖𝔼 x, multiplicativeDerivative f₀ a x *
            (star (g h x) * g (h - a) (x + a))‖ := by
          apply Finset.expect_congr rfl
          intro h _
          apply Fintype.expect_equiv (Equiv.subLeft h)
          intro k
          simp only [Equiv.subLeft_apply, sub_sub_cancel, multiplicativeDerivative,
            ← add_sub_assoc, mul_assoc]
        _ = _ := Finset.expect_comm _ _ _
    rw [← hreindex]
    simpa only [one_pow, one_mul, star_star, mul_assoc] using hcs
  have hsecond (a : G) : C a ^ 2 ≤
      𝔼 h, 𝔼 k, additiveQuadrupleCorrelation g a h k := by
    have hcs := finite_absolute_cauchy_schwarz (multiplicativeDerivative f₀ a)
      (fun h x => star (g h x) * g (h - a) (x + a))
      (multiplicativeDerivative_norm_le_one f₀ hf₀ a)
    simpa only [one_pow, one_mul, C, additiveQuadrupleCorrelation, star_mul,
      star_star, mul_assoc, mul_comm, mul_left_comm] using hcs
  calc
    _ = ((𝔼 h, ‖𝔼 x, (f₀ x * star (f₁ (x + h))) * star (g h x)‖) ^ 2) ^ 2 := by ring
    _ ≤ (𝔼 a, C a) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hfirst 2
    _ ≤ 𝔼 a, C a ^ 2 := expect_square_le C
    _ ≤ _ := Finset.expect_le_expect (fun a _ => hsecond a)

theorem exists_many_cross_correlated_quadruples
    (f₀ f₁ : G → ℂ) (g : G → G → ℂ) (H : Finset G)
    (hf₀ : ∀ x, ‖f₀ x‖ ≤ 1) (hf₁ : ∀ x, ‖f₁ x‖ ≤ 1) (hg : ∀ h x, ‖g h x‖ ≤ 1)
    (hzero : ∀ h, h ∉ H → ∀ x, g h x = 0)
    {alpha delta : ℝ} (halpha : 0 < alpha) (hdelta : 0 < delta)
    (hdense : alpha * Fintype.card G ≤ (H.card : ℝ))
    (hcorr : ∀ h ∈ H, delta ≤ ‖𝔼 x, (f₀ x * star (f₁ (x + h))) * star (g h x)‖) :
    ∃ Q : Finset (G × G × G), Q.Nonempty ∧
      (alpha * delta) ^ 4 / 2 * (Fintype.card G : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧
        t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H ∧
        (alpha * delta) ^ 4 / 2 ≤ additiveQuadrupleCorrelation g t.1 t.2.1 t.2.2 := by
  classical
  have hcardG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hindicator : (𝔼 h : G, if h ∈ H then delta else 0) =
      (H.card : ℝ) * delta / Fintype.card G := by
    rw [Fintype.expect_eq_sum_div_card]
    simp
  have hmean : alpha * delta ≤
      𝔼 h, ‖𝔼 x, (f₀ x * star (f₁ (x + h))) * star (g h x)‖ := by
    calc
      _ ≤ (H.card : ℝ) * delta / Fintype.card G := by
        apply (le_div_iff₀ hcardG).mpr
        nlinarith [mul_le_mul_of_nonneg_right hdense hdelta.le]
      _ = _ := hindicator.symm
      _ ≤ _ := by
        apply Finset.expect_le_expect
        intro h _
        split_ifs with hh
        · exact hcorr h hh
        · exact norm_nonneg _
  have hsplit : (𝔼 t : G × G × G, additiveQuadrupleCorrelation g t.1 t.2.1 t.2.2) =
      𝔼 a, 𝔼 h, 𝔼 k, additiveQuadrupleCorrelation g a h k := by
    simp only [← Finset.univ_product_univ, Finset.expect_product]
  have hquad : (alpha * delta) ^ 4 ≤
      𝔼 t : G × G × G, additiveQuadrupleCorrelation g t.1 t.2.1 t.2.2 := by
    rw [hsplit]
    exact (pow_le_pow_left₀ (mul_pos halpha hdelta).le hmean 4).trans
      (cross_correlations_force_additive_quadruples f₀ f₁ g hf₀ hf₁)
  obtain ⟨Q, hQcard, hQ⟩ := exists_dense_level_set
    (fun t : G × G × G => additiveQuadrupleCorrelation g t.1 t.2.1 t.2.2)
    (by positivity : 0 ≤ (alpha * delta) ^ 4)
    (fun t => additiveQuadrupleCorrelation_le_one g hg t.1 t.2.1 t.2.2) hquad
  have hcards : (Fintype.card (G × G × G) : ℝ) = (Fintype.card G : ℝ) ^ 3 := by
    simp only [Fintype.card_prod, Nat.cast_mul]
    ring
  rw [hcards] at hQcard
  have hQnonempty : Q.Nonempty := by
    apply Finset.card_pos.mp
    have : (0 : ℝ) < (Q.card : ℝ) := lt_of_lt_of_le (by positivity) hQcard
    exact_mod_cast this
  refine ⟨Q, hQnonempty, hQcard, fun t ht => ?_⟩
  obtain ⟨h₁, h₂, h₃, h₄⟩ := additiveQuadrupleCorrelation_support g H hzero
    (lt_of_lt_of_le (by positivity) (hQ t ht))
  exact ⟨h₁, h₂, h₃, h₄, hQ t ht⟩

end Erdos3

end

section

namespace Erdos3.NativeCrossWitnesses

open scoped BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s N : ℕ} [NeZero N] {p : ℝ} {f₀ f₁ : ZMod N → ℂ}
  {m : ZMod N → ZMod N → ℂ} {H : Finset (ZMod N)}
  (U : NativeCrossWitnesses s N p f₀ f₁ m H)

theorem exists_quadruples (hf₀ : ∀ x, ‖f₀ x‖ ≤ 1) (hf₁ : ∀ x, ‖f₁ x‖ ≤ 1)
    (hm : ∀ h x, ‖m h x‖ ≤ 1)
    (hdense : Real.exp (-p) * Fintype.card (ZMod N) ≤ (H.card : ℝ)) :
    ∃ Q : Finset (ZMod N × ZMod N × ZMod N), Q.Nonempty ∧
      Real.exp (-(12 * p)) / 2 * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧ t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H ∧
        Real.exp (-(8 * p)) / 2 ≤ additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2 := by
  let g (h x : ZMod N) := (Real.exp (-p) : ℂ) * U.extension h x
  have hg (h x : ZMod N) : ‖g h x‖ ≤ 1 := by
    dsimp only [g]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-p) * Real.exp p :=
        mul_le_mul_of_nonneg_left (U.extension_norm hm h x) (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hzero (h : ZMod N) (hh : h ∉ H) (x : ZMod N) : g h x = 0 := by
    simp only [g, U.extension_of_not_mem h hh, mul_zero]
  have hmean (h : ZMod N) :
      (𝔼 x, (f₀ x * star (f₁ (x + h))) * star (g h x)) =
        (Real.exp (-p) : ℂ) * (𝔼 x, (f₀ x * star (f₁ (x + h))) * star (U.extension h x)) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    simp only [g, star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  have hcorr (h : ZMod N) (hh : h ∈ H) :
      Real.exp (-(2 * p)) ≤ ‖𝔼 x, (f₀ x * star (f₁ (x + h))) * star (g h x)‖ := by
    rw [hmean, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hu : Real.exp (-p) ≤
        ‖𝔼 x, (f₀ x * star (f₁ (x + h))) * star (U.extension h x)‖ := by
      simpa only [U.extension_of_mem h hh] using U.product_correlation ⟨h, hh⟩
    calc
      _ = Real.exp (-p) * Real.exp (-p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hu (Real.exp_nonneg _)
  obtain ⟨Q, hQ, hsize, hquad⟩ := exists_many_cross_correlated_quadruples f₀ f₁ g H
    hf₀ hf₁ hg hzero (Real.exp_pos (-p)) (Real.exp_pos (-(2 * p))) hdense hcorr
  have hscale (a h k : ZMod N) : additiveQuadrupleCorrelation g a h k =
      Real.exp (-(4 * p)) * additiveQuadrupleCorrelation U.extension a h k := by
    rw [show g = (fun h x => (Real.exp (-p) : ℂ) * U.extension h x) from rfl,
      additiveQuadrupleCorrelation_real_scale U.extension (Real.exp (-p)) (Real.exp_nonneg _) a h k]
    congr 1
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  refine ⟨Q, hQ, ?_, ?_⟩
  · simpa only [derivative_quadruple_exp_threshold] using hsize
  · intro t ht
    obtain ⟨h₁, h₂, h₃, h₄, hc⟩ := hquad t ht
    refine ⟨h₁, h₂, h₃, h₄, ?_⟩
    rw [derivative_quadruple_exp_threshold, hscale] at hc
    have heq : Real.exp (-(4 * p)) * (Real.exp (-(8 * p)) / 2) = Real.exp (-(12 * p)) / 2 := by
      rw [← mul_div_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [← heq] at hc
    exact le_of_mul_le_mul_left hc (Real.exp_pos _)

theorem exists_quadruples_budget (hH : H.Nonempty)
    (hf₀ : ∀ x, ‖f₀ x‖ ≤ 1) (hf₁ : ∀ x, ‖f₁ x‖ ≤ 1) (hm : ∀ h x, ‖m h x‖ ≤ 1)
    (hdense : Real.exp (-p) * Fintype.card (ZMod N) ≤ (H.card : ℝ)) :
    ∃ Q : Finset (ZMod N × ZMod N × ZMod N), Q.Nonempty ∧
      Real.exp (-(13 * p + 2)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧ t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H ∧
        Real.exp (-(13 * p + 2)) ≤ additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2 := by
  obtain ⟨h, hh⟩ := hH
  have hp : 0 ≤ p := (Nat.cast_nonneg (U ⟨h, hh⟩).dim).trans (U ⟨h, hh⟩).complexity.1.1
  have h12 : Real.exp (-(13 * p + 2)) ≤ Real.exp (-(12 * p)) / 2 :=
    (Real.exp_le_exp.mpr (by linarith only [hp])).trans (exp_sub_one_le_half_exp (-(12 * p)))
  have h8 : Real.exp (-(13 * p + 2)) ≤ Real.exp (-(8 * p)) / 2 :=
    (Real.exp_le_exp.mpr (by linarith only [hp])).trans (exp_sub_one_le_half_exp (-(8 * p)))
  obtain ⟨Q, hQ, hsize, hcorr⟩ := U.exists_quadruples hf₀ hf₁ hm hdense
  refine ⟨Q, hQ, (mul_le_mul_of_nonneg_right h12 (by positivity)).trans hsize, ?_⟩
  intro t ht
  obtain ⟨h₁, h₂, h₃, h₄, hc⟩ := hcorr t ht
  exact ⟨h₁, h₂, h₃, h₄, h8.trans hc⟩

end Erdos3.NativeCrossWitnesses

end

section

namespace Erdos3.NativeCrossWitnesses

variable {s N : ℕ} [NeZero N] {p : ℝ} {f₀ f₁ : ZMod N → ℂ}
  {m : ZMod N → ZMod N → ℂ} {H S : Finset (ZMod N)}
  (U : NativeCrossWitnesses s N p f₀ f₁ m H)

noncomputable def restrict (hSH : S ⊆ H) : NativeCrossWitnesses s N p f₀ f₁ m S :=
  fun h => U ⟨h.val, hSH h.property⟩

theorem restrict_extension_of_mem (hSH : S ⊆ H) (h : ZMod N) (hh : h ∈ S) (x : ZMod N) :
    (U.restrict hSH).extension h x = U.extension h x := by
  rw [extension_of_mem _ h hh, U.extension_of_mem h (hSH hh)]
  rfl

theorem restrict_quadruple (hSH : S ⊆ H) (a h k : ZMod N)
    (h₁ : h ∈ S) (h₂ : h - a ∈ S) (h₃ : k ∈ S) (h₄ : k - a ∈ S) :
    additiveQuadrupleCorrelation (U.restrict hSH).extension a h k =
      additiveQuadrupleCorrelation U.extension a h k := by
  simp only [additiveQuadrupleCorrelation, U.restrict_extension_of_mem hSH h h₁,
    U.restrict_extension_of_mem hSH (h - a) h₂,
    U.restrict_extension_of_mem hSH k h₃, U.restrict_extension_of_mem hSH (k - a) h₄]

theorem exists_short_quadruples (hH : H.Nonempty)
    (hf₀ : ∀ x, ‖f₀ x‖ ≤ 1) (hf₁ : ∀ x, ‖f₁ x‖ ≤ 1) (hm : ∀ h x, ‖m h x‖ ≤ 1)
    (hdense : Real.exp (-p) * Fintype.card (ZMod N) ≤ (H.card : ℝ)) :
    ∃ S : Finset (ZMod N), S ⊆ H ∧ S.Nonempty ∧ CyclicShortShiftSet S ∧
      Real.exp (-(p + 1)) * Fintype.card (ZMod N) ≤ (S.card : ℝ) ∧
      ∃ Q : Finset (ZMod N × ZMod N × ZMod N), Q.Nonempty ∧
        Real.exp (-(13 * (p + 1) + 2)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
        ∀ t ∈ Q, t.2.1 ∈ S ∧ t.2.1 - t.1 ∈ S ∧ t.2.2 ∈ S ∧ t.2.2 - t.1 ∈ S ∧
          -(t.2.1.val : ℤ) + (t.2.1 - t.1).val + t.2.2.val - (t.2.2 - t.1).val = 0 ∧
          Real.exp (-(13 * (p + 1) + 2)) ≤
            additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2 := by
  obtain ⟨S, hSH, hS, hsize, hshort⟩ := exists_cyclicShortShiftSet H hH
  have hhalf : Real.exp (-(p + 1)) ≤ Real.exp (-p) / 2 := by
    rw [show -(p + 1) = -p - 1 by ring]
    exact exp_sub_one_le_half_exp (-p)
  have hdenseS : Real.exp (-(p + 1)) * Fintype.card (ZMod N) ≤ (S.card : ℝ) := by
    calc
      _ ≤ (Real.exp (-p) / 2) * Fintype.card (ZMod N) :=
        mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg _)
      _ = (Real.exp (-p) * Fintype.card (ZMod N)) / 2 := by ring
      _ ≤ (H.card : ℝ) / 2 := div_le_div_of_nonneg_right hdense (by norm_num)
      _ ≤ _ := hsize
  let V := (U.restrict hSH).mono (show p ≤ p + 1 by linarith)
  obtain ⟨Q, hQ, hQsize, hQcorr⟩ := V.exists_quadruples_budget hS hf₀ hf₁ hm hdenseS
  refine ⟨S, hSH, hS, hshort, hdenseS, Q, hQ, hQsize, ?_⟩
  intro t ht
  obtain ⟨h₁, h₂, h₃, h₄, hc⟩ := hQcorr t ht
  refine ⟨h₁, h₂, h₃, h₄, hshort.quadruple_relation t.1 t.2.1 t.2.2 h₁ h₂ h₃ h₄, ?_⟩
  change Real.exp (-(13 * (p + 1) + 2)) ≤
    additiveQuadrupleCorrelation (U.restrict hSH).extension t.1 t.2.1 t.2.2 at hc
  rwa [U.restrict_quadruple hSH t.1 t.2.1 t.2.2 h₁ h₂ h₃ h₄] at hc

end Erdos3.NativeCrossWitnesses

end

section

namespace Erdos3.NativeCorrelationStructure

open scoped BigOperators

variable {s r N : ℕ}
  [NeZero N]
  {p : ℝ}
  {f : ZMod N → ℂ}

end Erdos3.NativeCorrelationStructure

end

section

namespace Erdos3.NativeCorrelationStructure

open scoped BigOperators

variable {s r N : ℕ}
  [NeZero N]
  {p : ℝ}
  {f : ZMod N → ℂ}

end Erdos3.NativeCorrelationStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativePositiveCorrelation
namespace OAI

section

namespace Erdos3.NativeVectorCorrelation

open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_absorb_positive {I : Type*} {degree N : ℕ} [NeZero N] {p : ℝ}
    (f : I → ZMod N → ℂ) (A : ZMod N → ℝ) (hp : 2 ≤ p)
    (hA : PositiveCyclicNiltest.{0} degree N p A)
    (W : NativeVectorCorrelation degree N p (fun i x => (A x : ℂ) * f i x)) :
    Nonempty (NativeVectorCorrelation degree N (productNiltestBudget (raisedNiltestBudget p)) f) := by
  rcases hA with @⟨L, lie, alg, s, dim, top, add, smul, t2, D, hs, T, hT, hTc, heval⟩
  let U := T.raiseStep hs
  have hpq : p ≤ raisedNiltestBudget p := le_raisedNiltestBudget p
  have hU : U.ComplexityLE (raisedNiltestBudget p) :=
    T.raiseStep_complexity hs (by linarith) hTc
  have hval (x : ZMod N) : (A x : ℂ) = star (U.evalCyclic N (fun _ => x)) := by
    rw [RationalFilteredNilmanifold.Niltest.raiseStep_evalCyclic]
    apply Complex.ext
    · simp only [Complex.ofReal_re, Complex.star_def, Complex.conj_re, heval]
    · simp only [Complex.ofReal_im, Complex.star_def, Complex.conj_im,
        (T.unit_interval_evalCyclic hT N (fun _ => x)).1, neg_zero]
  let W' : NativeVectorCorrelation degree N (raisedNiltestBudget p)
      (fun iu : I × Unit => fun x => f iu.1 x * star (U.evalCyclic N (fun _ => x))) := {
    L := W.L
    dim := W.dim
    model := W.model
    test := W.test
    complexity := W.complexity.mono hpq
    coordinate := (W.coordinate, ())
    correlation := by
      have h := (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans W.correlation
      simpa only [hval, mul_comm] using h }
  exact exists_absorb (D.raiseStep hs) (fun _ : Unit => U) f (hp.trans hpq) (fun _ => hU) W'

end Erdos3.NativeVectorCorrelation

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonRefilteredMappedOrbitFactors
namespace OAI

section

namespace Erdos3

open Module

theorem exists_weighted_common_positive_nat {Ω : Type*} [Fintype Ω]
    (outer : FiniteProbabilityWeights Ω) (S : Finset Ω) (hS : 0 < outer.mass S)
    (n : Ω → ℕ) {p : ℝ} (hn : ∀ a ∈ S, 0 < n a ∧ (n a : ℝ) ≤ Real.exp p) :
    ∃ a₀ ∈ S, ∃ T : Finset Ω, T ⊆ S ∧ a₀ ∈ T ∧ (∀ a ∈ T, n a = n a₀) ∧
      Real.exp (-p) * outer.mass S ≤ outer.mass T := by
  let A := Finset.Icc 1 ⌊Real.exp p⌋₊
  have hA : ((A : Set ℕ).ncard : ℝ) ≤ Real.exp p := by
    simpa only [A, Set.ncard_coe_finset, Nat.card_Icc, Nat.add_sub_cancel] using
      (Nat.floor_le (Real.exp_nonneg p))
  obtain ⟨k, _, T, hTS, hT, hk, hlarge⟩ := exists_weighted_exponential_constant_fiber
    outer S hS n (A : Set ℕ) A.finite_toSet
    (fun a ha => Finset.mem_Icc.mpr ⟨(hn a ha).1, Nat.le_floor (hn a ha).2⟩) hA
  obtain ⟨a₀, ha₀⟩ := hT
  exact ⟨a₀, hTS ha₀, T, hTS, ha₀,
    fun a ha => (hk a ha).trans (hk a₀ ha₀).symm, hlarge⟩

theorem exists_weighted_common_fast_subalgebra
    {Ω ι L : Type*} [Fintype Ω] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (e : Basis ι ℚ L) (outer : FiniteProbabilityWeights Ω)
    (S : Finset Ω) (hS : 0 < outer.mass S)
    (K : Ω → LieSubalgebra ℚ L) (m : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hK : ∀ a ∈ S, ∃ v : Fin m → L,
      Submodule.span ℚ (Set.range v) = (K a).toSubmodule ∧
        ∀ i j, rationalLogHeight (e.repr (v i) j) ≤ p) :
    ∃ a₀ ∈ S, ∃ T : Finset Ω, T ⊆ S ∧ a₀ ∈ T ∧ (∀ a ∈ T, K a = K a₀) ∧
      Real.exp (-((p + 2) ^ 5)) * outer.mass S ≤ outer.mass T := by
  have hmem : ∀ a ∈ S, K a ∈ heightBoundedLieSubalgebras e m ⌈Real.exp p⌉₊ := by
    intro a ha
    obtain ⟨v, hv, hh⟩ := hK a ha
    exact (mem_heightBoundedSubspaces e m ⌈Real.exp p⌉₊ (K a).toSubmodule).mpr
      ⟨v, hv, fun i j => rationalHeightLE_ceil_exp (hh i j)⟩
  have hcount : ((heightBoundedLieSubalgebras e m ⌈Real.exp p⌉₊).ncard : ℝ) ≤
      Real.exp ((p + 2) ^ 5) :=
    (heightBoundedLieSubalgebras_ncard_exp_bound e m hp).trans
      (Real.exp_le_exp.mpr (common_subalgebra_cost_le_budget m (Fintype.card ι)
        hp hm hd hp le_rfl))
  obtain ⟨U, _, T, hTS, hT, hU, hlarge⟩ := exists_weighted_exponential_constant_fiber
    outer S hS K (heightBoundedLieSubalgebras e m ⌈Real.exp p⌉₊)
    (finite_card_heightBoundedLieSubalgebras e m ⌈Real.exp p⌉₊).1 hmem hcount
  obtain ⟨a₀, ha₀⟩ := hT
  exact ⟨a₀, hTS ha₀, T, hTS, ha₀,
    fun a ha => (hU a ha).trans (hU a₀ ha₀).symm, hlarge⟩

theorem exists_weighted_common_fast_subalgebra_and_denominator
    {Ω ι L : Type*} [Fintype Ω] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (e : Basis ι ℚ L) (outer : FiniteProbabilityWeights Ω)
    (S : Finset Ω) (hS : 0 < outer.mass S)
    (K : Ω → LieSubalgebra ℚ L) (n : Ω → ℕ) (m : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hK : ∀ a ∈ S, ∃ v : Fin m → L,
      Submodule.span ℚ (Set.range v) = (K a).toSubmodule ∧
        ∀ i j, rationalLogHeight (e.repr (v i) j) ≤ p)
    (hn : ∀ a ∈ S, 0 < n a ∧ (n a : ℝ) ≤ Real.exp p) :
    ∃ a₀ ∈ S, ∃ T : Finset Ω, T ⊆ S ∧ a₀ ∈ T ∧
      (∀ a ∈ T, K a = K a₀ ∧ n a = n a₀) ∧
      Real.exp (-((p + 2) ^ 5 + p)) * outer.mass S ≤ outer.mass T := by
  obtain ⟨b, _, U, hUS, hbU, hKsame, hUlarge⟩ :=
    exists_weighted_common_fast_subalgebra e outer S hS K m hp hm hd hK
  have hUpos : 0 < outer.mass U := (mul_pos (Real.exp_pos _) hS).trans_le hUlarge
  obtain ⟨a₀, haU, T, hTU, haT, hnsame, hTlarge⟩ :=
    exists_weighted_common_positive_nat outer U hUpos n (fun a ha => hn a (hUS ha))
  refine ⟨a₀, hUS haU, T, hTU.trans hUS, haT, ?_, ?_⟩
  · intro a ha
    exact ⟨(hKsame a (hTU ha)).trans (hKsame a₀ haU).symm, hnsame a ha⟩
  · calc
      Real.exp (-((p + 2) ^ 5 + p)) * outer.mass S =
          Real.exp (-p) * (Real.exp (-((p + 2) ^ 5)) * outer.mass S) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-p) * outer.mass U :=
        mul_le_mul_of_nonneg_left hUlarge (Real.exp_pos _).le
      _ ≤ outer.mass T := hTlarge

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

variable {ι J σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (a : ι)

def HasFixedProductOrbitFactors
    (g : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (eta : J → L a →ₗ[ℚ] ℚ) (side : σ → ℝ) (p : ℝ) (m : ℕ)
    (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) : Prop :=
  ∃ freq : J → ∀ i, L i →ₗ[ℚ] ℚ,
    (∀ j, freq j a = eta j) ∧
    (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W s →
      realifyFunctional (piFrequency (freq j)) x = 0) ∧
    ∃ (κ : (pi D).RealGroup)
      (slow middle rat : ((pi D).filtration.realification.adaptedPolynomialFiltration
        (fun _ : σ => 1)).Group),
      κ ∈ (pi D).realLattice ∧
      slow * middle * rat * (pi D).filtration.realification.adaptedConstantGroupHom
        (fun _ : σ => 1) κ =
          ⟨⟨(piRealOrbit (fun i => (D i).filtration) g).log,
            (piRealOrbit (fun i => (D i).filtration) g).property⟩⟩ ∧
      (pi D).filtration.PolynomialSlowBound (pi D).basis (fun _ : σ => 1)
        side (Real.exp p) slow ∧
      (pi D).filtration.PolynomialRationalGrid (pi D).basis (fun _ : σ => 1) m rat ∧
      coefficients (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0 ∧
      coefficients (rat.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0 ∧
      (∀ α, coefficients (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) α ∈
        (pi D).filtration.realGradedRefiltrationLayer W (Finsupp.weight (fun _ => 1) α)) ∧
      (∀ t : σ → ℝ, eval₂ t (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) ∈
        realificationLieSubalgebra ((pi D).filtration.gradedRefiltrationSubalgebra W))

theorem HasFixedProductOrbitFactors.mono
    {g : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : σ => 1)}
    {eta : J → L a →ₗ[ℚ] ℚ} {side : σ → ℝ} {p q : ℝ} {m : ℕ}
    {W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded}
    (h : HasFixedProductOrbitFactors D a g eta side p m W)
    (hpq : p ≤ q) (hside : ∀ i, 0 < side i) :
    HasFixedProductOrbitFactors D a g eta side q m W := by
  obtain ⟨freq, hf, hv, κ, slow, middle, rat, hκ, heq, hs, hr, hm0, hr0, hc, ht⟩ := h
  exact ⟨freq, hf, hv, κ, slow, middle, rat, hκ, heq,
    (pi D).filtration.polynomialSlowBound_mono (pi D).basis (fun _ => 1) side hside
      (Real.exp_le_exp.mpr hpq) slow hs, hr, hm0, hr0, hc, ht⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

variable {G ι J σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (a : ι)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

variable {G ι J σ : Type*} [Fintype G] [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (a : ι)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι J Ω L : Type*} [Fintype σ] [Fintype ι] [Fintype J] [Fintype Ω]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

def HasCommonRefilteredOrbitFactors
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
    (side : σ → ℝ) (q : ℝ) (m : ℕ)
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) : Prop :=
  ∃ e middle r : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
    e * middle * r = g ∧
    (∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b w hF (fun _ => 1)
      (F.realPolynomialSymbolHom b w hF (fun _ => 1) middle).coord) ∈
        realificationLieSubalgebra W) ∧
    F.PolynomialSlowBound b (fun _ => 1) side (Real.exp q) e ∧
    F.PolynomialRationalGrid b (fun _ => 1) m r ∧
    coefficients (e.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
    coefficients (r.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
    coefficients (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 =
      coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0

theorem exists_weighted_common_refiltered_orbit_factors (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι J Ω L : Type*} [Fintype σ] [Fintype ι] [Fintype J] [Fintype Ω]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
      (eta : J → L →ₗ[ℚ] ℚ) {p : ℝ}, 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (∀ i j k, rationalLogHeight (b.repr ⁅b i, b j⁆ k) ≤ p) →
      ∀ side : σ → ℝ, (∀ i, Real.exp ((p + 2) ^ C) ≤ side i) →
      ∀ (outer : FiniteProbabilityWeights Ω) (H : Finset Ω), 0 < outer.mass H →
      ∀ g : Ω → (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      (∀ a ∈ H, ∀ j, F.ControlledSymbolFactorization b w hF (eta j) side
        (F.realPolynomialSymbolHom b w hF (fun _ => 1) (g a)) p) →
      let q := (p + 2) ^ C + (((p + 2) ^ 2 + 2) ^ 63 + 1) + p + 1
      ∃ (W : LieSubalgebra ℚ F.AssociatedGraded)
        (v : Fin (Fintype.card ι) → F.AssociatedGraded) (m : ℕ) (H' : Finset Ω),
        H' ⊆ H ∧ 0 < outer.mass H' ∧
        Real.exp (-((q + 2) ^ 5 + q)) * outer.mass H ≤ outer.mass H' ∧
        Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
        BasisGradedSubmodule (F.associatedGradedBasis b w hF) w W.toSubmodule ∧
        (∀ i k, rationalLogHeight ((F.associatedGradedBasis b w hF).repr (v i) k) ≤ q) ∧
        (∀ j x, x ∈ F.realGradedRefiltrationLayer W s → realifyFunctional (eta j) x = 0) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp q ∧
        ∀ a ∈ H', F.HasCommonRefilteredOrbitFactors b w hF side q m W (g a) := by
  obtain ⟨C, hC, hcommon⟩ := exists_common_refiltered_factorization s
  refine ⟨C, hC, ?_⟩
  intro σ ι J Ω L _ _ _ _ _ _ F b w hF eta p hp hι hσ hJ hstructure
    side hside outer H hH g hfactor
  classical
  let q := (p + 2) ^ C + (((p + 2) ^ 2 + 2) ^ 63 + 1) + p + 1
  have hpC : 0 ≤ (p + 2) ^ C := by positivity
  have hpheight : 0 ≤ ((p + 2) ^ 2 + 2) ^ 63 := by positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hcq : (p + 2) ^ C ≤ q := by dsimp [q]; linarith
  have hvq : ((p + 2) ^ 2 + 2) ^ 63 + 1 ≤ q := by dsimp [q]; linarith
  have hsidepos (i) : 0 < side i := (Real.exp_pos _).trans_le (hside i)
  have hHne : H.Nonempty := by
    by_contra hn
    have he : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty, lt_self_iff_false] at hH
  obtain ⟨a₀, ha₀⟩ := hHne
  let pick (a : Ω) := if a ∈ H then a else a₀
  have hpick (a) : pick a ∈ H := by
    dsimp only [pick]
    split_ifs with ha
    · exact ha
    · exact ha₀
  choose W v m e middle r hv hW hheight hfreq hm hmp hprod hmid he hr he0 hr0 hmiddle0 hanchor
    using fun a => hcommon F b w hF eta p hp hι hσ hJ hstructure side hside
      (g (pick a)) (hfactor (pick a) (hpick a))
  obtain ⟨a₁, _, H', hsub, _, hsame, hmass⟩ :=
    exists_weighted_common_fast_subalgebra_and_denominator
      (F.associatedGradedBasis b w hF) outer H hH W m (Fintype.card ι) hq
      (hι.trans hpq) (hι.trans hpq)
      (fun a _ => ⟨v a, hv a, fun i k => (hheight a i k).trans hvq⟩)
      (fun a _ => ⟨hm a, (hmp a).trans (Real.exp_le_exp.mpr hcq)⟩)
  refine ⟨W a₁, v a₁, m a₁, H', hsub,
    (mul_pos (Real.exp_pos _) hH).trans_le hmass, hmass, hv a₁, hW a₁,
    fun i k => (hheight a₁ i k).trans hvq, hfreq a₁, hm a₁,
    (hmp a₁).trans (Real.exp_le_exp.mpr hcq), ?_⟩
  intro a ha
  have hpa : pick a = a := if_pos (hsub ha)
  have hout : F.HasCommonRefilteredOrbitFactors b w hF side q (m a) (W a) (g (pick a)) := by
    refine ⟨e a, middle a, r a, hprod a, hmid a, ?_, hr a, he0 a, hr0 a, hmiddle0 a⟩
    exact F.polynomialSlowBound_mono b (fun _ => 1) side hsidepos
      (Real.exp_le_exp.mpr hcq) (e a) (he a)
  simpa only [hpa, (hsame a ha).1, (hsame a ha).2] using hout

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem PolynomialSlowBound.to_symbol (w : σ → ℕ) (T : σ → ℝ) (M : ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialSlowBound b w T M g) :
    F.SymbolSlowBound b ω hF w T M (F.realPolynomialSymbolHom b ω hF w g) := by
  intro z
  change |((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr
    (F.realSymbolOfPolynomial b ω hF w g.coord) z| ≤ _
  rw [F.realSymbolOfPolynomial_coordinate]
  exact hg z.val.1 z.val.2

theorem PolynomialRationalGrid.to_symbol (w : σ → ℕ) (l : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialRationalGrid b w l g) :
    F.SymbolRationalGrid b ω hF w l (F.realPolynomialSymbolHom b ω hF w g) := by
  obtain ⟨a, ha⟩ := hg
  refine ⟨fun z => a z.val, ?_⟩
  funext z
  change (a z.val : ℝ) = (l : ℝ) *
    ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr
      (F.realSymbolOfPolynomial b ω hF w g.coord) z
  rw [F.realSymbolOfPolynomial_coordinate]
  exact congrFun ha z.val

theorem HasCommonRefilteredOrbitFactors.symbolFactors [Fintype σ] [Fintype ι]
    (T : σ → ℝ) (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (h : F.HasCommonRefilteredOrbitFactors b ω hF T q l W g) :
    ∃ El Pl Rl : F.RealPolynomialSymbolGroup (fun _ : σ => 1),
      El * Pl * Rl = F.realPolynomialSymbolHom b ω hF (fun _ => 1) g ∧
      Pl.coord ∈ realificationLieSubalgebra
        (F.symbolPointwiseSubalgebra b ω hF (fun _ => 1) W) ∧
      F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp q) El ∧
      F.SymbolRationalGrid b ω hF (fun _ => 1) l Rl := by
  obtain ⟨e, p, r, hprod, hmid, he, hr, _, _, _⟩ := h
  refine ⟨F.realPolynomialSymbolHom b ω hF (fun _ => 1) e,
    F.realPolynomialSymbolHom b ω hF (fun _ => 1) p,
    F.realPolynomialSymbolHom b ω hF (fun _ => 1) r, ?_, ?_, ?_, ?_⟩
  · simpa only [map_mul] using congrArg (F.realPolynomialSymbolHom b ω hF (fun _ => 1)) hprod
  · exact (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF (fun _ => 1) W _).mpr hmid
  · exact he.to_symbol F b ω hF (fun _ => 1) T (Real.exp q) e
  · exact hr.to_symbol F b ω hF (fun _ => 1) l r

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem realPolynomialGroupMap_coefficient (w : σ → ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) (α : σ →₀ ℕ) :
    coefficients ((F.realPolynomialGroupMap G φ hφ w g).coord :
      VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) α =
      realificationLieHom φ (coefficients
        (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) := by
  rw [F.realPolynomialGroupMap_log, coefficients_map]
  rfl

omit [Fintype ι] [Fintype κ] in

theorem realPolynomialGroupMap_middle_mem (w : σ → ℕ)
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : ∀ z : σ → ℝ, eval₂ z (F.realGradedSymbolPolynomial b ω hF w
      (F.realPolynomialSymbolHom b ω hF w g).coord) ∈ realificationLieSubalgebra W) :
    ∀ z : σ → ℝ, eval₂ z (G.realGradedSymbolPolynomial c ν hG w
      (G.realPolynomialSymbolHom c ν hG w
        (F.realPolynomialGroupMap G φ hφ w g)).coord) ∈
      realificationLieSubalgebra (W.map (F.associatedGradedMap G φ hφ)) := by
  have hmem := (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF w W _).mpr hg
  have hmap := F.real_symbolPointwiseSubalgebra_map_mem G b ω hF c ν hG φ hφ w W
    (F.realPolynomialSymbolHom b ω hF w g).coord hmem
  have hsymbol : realificationLieHom (F.filteredPolynomialSymbolMap G φ hφ w)
      (F.realPolynomialSymbolHom b ω hF w g).coord =
      (G.realPolynomialSymbolHom c ν hG w
        (F.realPolynomialGroupMap G φ hφ w g)).coord :=
    F.realFilteredPolynomialSymbolMap_polynomial G φ hφ b ω hF c ν hG w g.coord
  rw [hsymbol] at hmap
  exact (G.mem_real_symbolPointwiseSubalgebra_iff_values c ν hG w _ _).mp hmap

theorem exists_common_refiltered_mapped_orbit_factors
    {H : ℕ} (hentries : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hsource : (Fintype.card ι : ℝ) ≤ p)
    (htarget : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (l : ℕ) (hl : 0 < l) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 4) ∧ l ∣ m ∧
      ∀ (side : σ → ℝ), (∀ i, 0 < side i) →
      ∀ (q : ℝ) (W : LieSubalgebra ℚ F.AssociatedGraded)
        (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
      F.HasCommonRefilteredOrbitFactors b ω hF side q l W g →
      G.HasCommonRefilteredOrbitFactors c ν hG side ((p + 2) ^ 3 + q) m
        (W.map (F.associatedGradedMap G φ hφ))
        (F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) g) := by
  obtain ⟨m, hm, hmp, hlm, hgrid⟩ :=
    F.exists_realPolynomialGroupMap_grid G b c φ hφ (fun _ : σ => 1)
      hentries hp hsource htarget hHp l hl hlp
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro side hside q W g hfactor
  obtain ⟨e, middle, r, hprod, hmid, he, hr, he0, hr0, hmiddle0⟩ := hfactor
  let π := F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1)
  refine ⟨π e, π middle, π r, ?_, ?_, ?_, hgrid r hr, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, hprod]
  · exact F.realPolynomialGroupMap_middle_mem G b ω hF c ν hG φ hφ
      (fun _ : σ => 1) W middle hmid
  · have hslow := F.realPolynomialGroupMap_slow_exp G b c φ hφ
      (fun _ : σ => 1) hentries hp hsource hHp side hside (Real.exp_nonneg q) e he
    simpa only [Real.exp_add] using hslow
  · change coefficients ((F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) e).coord :
      VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0 = 0
    rw [F.realPolynomialGroupMap_coefficient, he0, map_zero]
  · change coefficients ((F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) r).coord :
      VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0 = 0
    rw [F.realPolynomialGroupMap_coefficient, hr0, map_zero]
  · change coefficients ((F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) middle).coord :
        VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0 =
      coefficients ((F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) g).coord :
        VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0
    rw [F.realPolynomialGroupMap_coefficient, F.realPolynomialGroupMap_coefficient, hmiddle0]

end Erdos3.NilpotentLieFiltration

end

end OAI

end


