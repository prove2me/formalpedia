-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_norm_le_and_tsum_indicator_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T11:17:03.754123+00:00
-- url     : https://prove2.me/submissions/254e4869-add9-4416-a334-b17b3467ba54

import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Theorems.Thm_NumberField_exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero
import Theorems.Thm_NumberField_TateGlobal_exists_forall_norm_sub_one_mul_partialDedekindZeta_continuation_le_rpow_of_re_mem_Icc
import Theorems.Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
import Mathlib

universe u

section
section
/-!
# T12B: elementary Euler-product glue for `HeckeChar.LSeries`

* `T12B.norm_le_one`: `‖χ I‖ ≤ 1` (values on coprime ideals are roots of unity: class group and
  `(𝓞/𝔪)ˣ` are finite).
* `T12B.lseries_eq_tsum`: `L(s, χ) = ∑'_I χ(I) N(I)^{-s}` for `Re s > 1`.
* `T12B.sieve`: `(∑' g) · ∏_{P ∈ T} (1 − g P) = ∑'_{I coprime to T} g I` for completely
  multiplicative `g` (finite Euler sieve; no infinite product needed).
* `T12B.sieve_bound`: the sieved sum is close to `1` once `T` kills a large finite set.
-/

namespace ArtinPrimitiveRoots

open NumberField Filter Topology
open scoped nonZeroDivisors

namespace T12B

variable {F : Type*} [Field F] [NumberField F]

/-! ### Summability of `∑_I N(I)^{-σ}` -/

theorem lseriesSummable_card {y : ℝ} (hy : 1 < y) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)) y := by
  have hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℝ)) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue F)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ F).comp tendsto_natCast_atTop_atTop).congr
      fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq
        (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (f := fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ))
    (Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using hlim))
    (fun _ ↦ Nat.cast_nonneg _) zero_le_one (s := (y : ℂ)) (by simpa using hy)
  simpa using h

instance fiber_finite (n : ℕ) : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

/-- `∑_I N(I)^{-σ}` converges for `σ > 1`. -/
theorem summable_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ)) := by
  let e := Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)
  rw [← e.summable_iff]
  refine (summable_sigma_of_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)).2
    ⟨fun n => Summable.of_finite, ?_⟩
  refine (lseriesSummable_card (F := F) hσ).norm.congr fun n => ?_
  have hfib : ∀ y : {I : Ideal (𝓞 F) // Ideal.absNorm I = n},
      ((Ideal.absNorm (e ⟨n, y⟩) : ℕ) : ℝ) ^ (-σ) = (n : ℝ) ^ (-σ) := fun y => by
    simp [e, Equiv.sigmaFiberEquiv, y.2]
  simp only [Function.comp_apply, hfib, tsum_const, nsmul_eq_mul, LSeries.norm_term_eq,
    Complex.ofReal_re, Complex.norm_natCast]
  split_ifs with hn
  · subst hn
    rw [Nat.cast_zero, Real.zero_rpow (by linarith), mul_zero]
  · rw [Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]

/-! ### Basic facts on Hecke characters -/

/-! ### The Dirichlet series as a sum over ideals -/

/-! ### The finite sieve -/

/-- The ideals not contained in any member of `T`. -/
def Cop (T : Finset (Ideal (𝓞 F))) : Set (Ideal (𝓞 F)) := {I | ∀ P ∈ T, ¬ I ≤ P}

theorem sieve (g : Ideal (𝓞 F) → ℂ) (hmul : ∀ I J, g (I * J) = g I * g J) (hg : Summable g)
    (T : Finset (Ideal (𝓞 F))) (hT : ∀ P ∈ T, P.IsPrime ∧ P ≠ ⊥) :
    (∑' I, g I) * ∏ P ∈ T, (1 - g P) = ∑' I, (Cop T).indicator g I := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [Cop]
  | insert P T hPT ih =>
    have hP := hT P (Finset.mem_insert_self P T)
    have ih' := ih (fun Q hQ => hT Q (Finset.mem_insert_of_mem hQ))
    rw [Finset.prod_insert hPT, mul_left_comm, mul_comm, ih']
    set h := (Cop T).indicator g with hh
    have hhs : Summable h := hg.indicator _
    have hPI : ∀ I, h (P * I) = g P * h I := by
      intro I
      by_cases hI : I ∈ Cop T
      · have hPI' : P * I ∈ Cop T := by
          intro Q hQ hle
          rcases (hT Q (Finset.mem_insert_of_mem hQ)).1.mul_le.1 hle with h1 | h1
          · have := (hP.1.isMaximal hP.2).eq_of_le (hT Q (Finset.mem_insert_of_mem hQ)).1.ne_top h1
            exact hPT (this ▸ hQ)
          · exact hI Q hQ h1
        rw [hh, Set.indicator_of_mem hPI', Set.indicator_of_mem hI, hmul]
      · have hPI' : P * I ∉ Cop T := by
          intro hc
          simp only [Cop, Set.mem_setOf_eq, not_forall, not_not] at hI
          obtain ⟨Q, hQ, hle⟩ := hI
          exact hc Q hQ (Ideal.mul_le_right.trans hle)
        rw [hh, Set.indicator_of_notMem hPI', Set.indicator_of_notMem hI, mul_zero]
    have hshift : g P * ∑' I, h I = ∑' J, {J | J ≤ P}.indicator h J := by
      rw [← hhs.tsum_mul_left]
      have hinj : Function.Injective (fun I : Ideal (𝓞 F) => P * I) := by
        intro a b hab
        have hP0 : P ≠ 0 := by rw [Ideal.zero_eq_bot]; exact hP.2
        exact mul_left_cancel₀ hP0 hab
      rw [← hinj.tsum_eq (f := {J | J ≤ P}.indicator h)]
      · congr 1
        funext I
        rw [Set.indicator_of_mem (show P * I ∈ {J | J ≤ P} from Ideal.mul_le_left), hPI]
      · intro J hJ
        have hle : J ≤ P := by
          by_contra hc
          exact hJ (Set.indicator_of_notMem hc _)
        obtain ⟨c, rfl⟩ := Ideal.dvd_iff_le.2 hle
        exact ⟨c, rfl⟩
    rw [mul_sub, mul_one, mul_comm, hshift, ← hhs.tsum_sub (hhs.indicator _)]
    congr 1
    funext J
    simp only [hh, Set.indicator, Cop, Set.mem_setOf_eq, Finset.mem_insert, forall_eq_or_imp]
    by_cases h1 : J ≤ P <;> by_cases h2 : ∀ Q ∈ T, ¬J ≤ Q <;> simp [h1, h2]

end T12B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3P_Zeta: the incomplete Dedekind zeta function `ζ^S`

`ζ^S(s) = ∏_{P ⊇ 𝔪}(1 − N P^{-s}) ζ_F(s) = R(s)/(s − 1)` with `R` entire, `R(1) = R_S`
(`sZetaResidue`), and `‖R(s)‖ ≤ C (2 + |Im s|)^k` on `9/10 ≤ Re s ≤ 12`. From 8087d96f
(`(s − 1) ζ_K` entire), 4f76b464 (convexity bound for `(s − 1) ζ_{K,T}`, here with `T = ∅`), the
Euler product 4d2ff9db, and Mathlib's class number formula; a field in an arbitrary universe is
replaced by a `Type` model. -/

set_option maxHeartbeats 1000000

open NumberField Complex Filter Topology

namespace ArtinPrimitiveRoots

namespace C3P


theorem exists_small_model (F : Type u) [Field F] [NumberField F] :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : NumberField F₀), Nonempty (F₀ ≃+* F) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ F
  have hint : IsIntegral ℚ α := Algebra.IsIntegral.isIntegral α
  haveI : Fact (Irreducible (minpoly ℚ α)) := ⟨minpoly.irreducible hint⟩
  let e : AdjoinRoot (minpoly ℚ α) ≃ₐ[ℚ] F :=
    (IntermediateField.adjoinRootEquivAdjoin ℚ hint).trans
      ((IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv)
  haveI : FiniteDimensional ℚ (AdjoinRoot (minpoly ℚ α)) :=
    LinearEquiv.finiteDimensional e.toLinearEquiv.symm
  haveI : NumberField (AdjoinRoot (minpoly ℚ α)) := { }
  exact ⟨_, inferInstance, inferInstance, ⟨e.toRingEquiv⟩⟩

theorem card_absNorm_eq_congr {K₁ K₂ : Type*} [Field K₁] [NumberField K₁] [Field K₂]
    [NumberField K₂] (e : K₁ ≃+* K₂) (n : ℕ) :
    Nat.card {I : Ideal (𝓞 K₁) // Ideal.absNorm I = n} =
      Nat.card {I : Ideal (𝓞 K₂) // Ideal.absNorm I = n} := by
  set f : 𝓞 K₁ ≃+* 𝓞 K₂ := RingOfIntegers.mapRingEquiv e
  have hnorm : ∀ I : Ideal (𝓞 K₁), Ideal.absNorm (I.map f) = Ideal.absNorm I := by
    intro I
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Submodule.cardQuot_apply]
    exact (Nat.card_congr (Ideal.quotientEquiv I (I.map f) f rfl).toEquiv).symm
  have h1 : ∀ I : Ideal (𝓞 K₁), (I.map f).map f.symm = I := fun I => Ideal.map_of_equiv f
  have h2 : ∀ J : Ideal (𝓞 K₂), (J.map f.symm).map f = J := fun J => by
    have := Ideal.map_of_equiv (I := J) f.symm; rwa [RingEquiv.symm_symm] at this
  refine Nat.card_congr
    { toFun := fun I => ⟨I.1.map f, by rw [hnorm]; exact I.2⟩
      invFun := fun J => ⟨J.1.map f.symm, by rw [← hnorm, h2]; exact J.2⟩
      left_inv := fun I => Subtype.ext (h1 I.1)
      right_inv := fun J => Subtype.ext (h2 J.1) }

theorem dedekindZeta_congr {K₁ K₂ : Type*} [Field K₁] [NumberField K₁] [Field K₂]
    [NumberField K₂] (e : K₁ ≃+* K₂) : dedekindZeta K₁ = dedekindZeta K₂ := by
  funext s
  unfold dedekindZeta
  congr 1
  funext n
  rw [card_absNorm_eq_congr e n]

/-- `(s − 1) ζ_F` continued: entire, with value the residue at 1 and polynomial growth on
`−1/2 ≤ Re s ≤ 5/2`. -/
theorem exists_R0 (F : Type u) [Field F] [NumberField F] :
    ∃ R0 : ℂ → ℂ, Differentiable ℂ R0 ∧ (∀ s : ℂ, 1 < s.re → R0 s = (s - 1) * dedekindZeta F s) ∧
      R0 1 = (dedekindZeta_residue F : ℂ) ∧
      ∃ C A : ℝ, 0 < A ∧ ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 5 / 2 → ‖R0 s‖ ≤ C * (2 + |s.im|) ^ A := by
  obtain ⟨F₀, _, _, ⟨e⟩⟩ := exists_small_model F
  have hζ : dedekindZeta F₀ = dedekindZeta F := dedekindZeta_congr e
  obtain ⟨R0, hR0, -, hR0eq, -⟩ :=
    NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero
      F₀
  refine ⟨R0, hR0, fun s hs => by rw [hR0eq s hs, hζ], ?_, ?_⟩
  · -- the residue, by uniqueness of limits along real `s → 1⁺`
    have h1 : Tendsto (fun s : ℝ => R0 s) (𝓝[>] 1) (𝓝 (R0 1)) := by
      have := ((hR0 1).continuousAt.tendsto).comp
        ((Complex.continuous_ofReal.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1)))
      convert this using 2
      simp
    have h2 := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT F
    refine tendsto_nhds_unique h1 (h2.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hR0eq s (by simpa using hs), hζ]
  · obtain ⟨C, A, -, hA, hb⟩ :=
      NumberField.TateGlobal.exists_forall_norm_sub_one_mul_partialDedekindZeta_continuation_le_rpow_of_re_mem_Icc
        F₀ ∅
    refine ⟨C, A, hA, hb R0 hR0 fun s hs => ?_⟩
    rw [hR0eq s hs]
    congr 1
    have hp := NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta F₀ s hs
    rw [← hp.tprod_eq]
    exact ((Equiv.subtypeUnivEquiv (fun v => Finset.notMem_empty v)).tprod_eq
      (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F₀) =>
        (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)).symm

/-- `‖ζ_F(s)‖` is bounded on `Re s ≥ 5/2`. -/
theorem exists_dedekindZeta_bound (F : Type*) [Field F] [NumberField F] :
    ∃ B : ℝ, ∀ s : ℂ, 5 / 2 ≤ s.re → ‖dedekindZeta F s‖ ≤ B := by
  set f : ℕ → ℂ := fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)
  have hs0 : LSeriesSummable f ((5 / 2 : ℝ) : ℂ) := T12B.lseriesSummable_card (by norm_num)
  refine ⟨∑' n, ‖LSeries.term f ((5 / 2 : ℝ) : ℂ) n‖, fun s hs => ?_⟩
  have hre : ((5 / 2 : ℝ) : ℂ).re ≤ s.re := by simpa using hs
  have hss : LSeriesSummable f s := hs0.of_re_le_re hre
  unfold dedekindZeta
  refine (norm_tsum_le_tsum_norm hss.norm).trans ?_
  exact hss.norm.tsum_le_tsum (fun n => LSeries.norm_term_le_of_re_le_re f hre n) hs0.norm

end C3P

end ArtinPrimitiveRoots

end
end

section
section
/-! # T12A_Sum: Dirichlet series over ideals as sums over ideals

For `f : Ideal (𝓞 K) → ℂ` bounded by `1` and `Re s > 1`, the `LSeries` whose `n`-th coefficient is
`∑ᶠ I ∈ {absNorm I = n}, f I` is the (absolutely convergent) sum `∑' I, f I * N(I)^{-s}`. -/

set_option maxHeartbeats 4000000
set_option autoImplicit false

open NumberField Complex Filter Topology Ideal

namespace ArtinPrimitiveRoots.T12A

variable {K : Type*} [Field K] [NumberField K]

theorem lseriesSummable_card {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℂ)) s := by
  have hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 K) // absNorm I = k} : ℝ)) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue K)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr
      fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (f := fun n ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℝ))
    (Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using hlim))
    (fun _ ↦ Nat.cast_nonneg _) zero_le_one (s := s) hs
  simpa using h

instance finite_fiber (n : ℕ) : Finite {I : Ideal (𝓞 K) // absNorm I = n} := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton {I : Ideal (𝓞 K) // absNorm I = 0} :=
      ⟨fun a b => Subtype.ext (by
        rw [Ideal.absNorm_eq_zero_iff.mp a.2, Ideal.absNorm_eq_zero_iff.mp b.2])⟩
    exact Finite.of_subsingleton
  · exact (finite_setOfPred_absNorm_eq n).to_subtype

/-- The norms `‖N(I)^{-s}‖` are summable over all ideals when `Re s > 1`. -/
theorem summable_norm_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : Ideal (𝓞 K) ↦ ‖(absNorm I : ℂ) ^ (-s)‖) := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h, zero_re] at hs; linarith
  let e := Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) ↦ absNorm I)
  rw [← e.summable_iff]
  refine (summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)).mpr ⟨fun n ↦ Summable.of_finite, ?_⟩
  have key : ∀ n : ℕ, ∑' I : {I : Ideal (𝓞 K) // absNorm I = n},
      ‖(absNorm (e ⟨n, I⟩) : ℂ) ^ (-s)‖ =
      ‖LSeries.term (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℂ)) s n‖ := by
    intro n
    have : ∀ I : {I : Ideal (𝓞 K) // absNorm I = n},
        ‖(absNorm (e ⟨n, I⟩) : ℂ) ^ (-s)‖ = ‖(n : ℂ) ^ (-s)‖ := by
      intro I
      show ‖(absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s)‖ = _
      rw [I.2]
    rw [tsum_congr this, tsum_const, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term_zero, zero_cpow (neg_ne_zero.mpr hs0)]
    · rw [LSeries.term_of_ne_zero hn.ne', norm_div, cpow_neg, norm_inv, div_eq_mul_inv,
        norm_natCast]
  simp_rw [key]
  exact (lseriesSummable_card hs).norm

/-- **Sum over ideals.** -/
theorem hasSum_ideal (f : Ideal (𝓞 K) → ℂ) (hf : ∀ I, ‖f I‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I ↦ f I * (absNorm I : ℂ) ^ (-s))
      (LSeries (fun n ↦ ∑ᶠ I ∈ {I : Ideal (𝓞 K) | absNorm I = n}, f I) s) := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h, zero_re] at hs; linarith
  have hsum : Summable (fun I : Ideal (𝓞 K) ↦ f I * (absNorm I : ℂ) ^ (-s)) := by
    refine Summable.of_norm_bounded (summable_norm_cpow hs) fun I ↦ ?_
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hf I)
  let e := Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) ↦ absNorm I)
  have h1 := (e.hasSum_iff.mpr hsum.hasSum).sigma (fun n ↦ (Summable.of_finite).hasSum)
  suffices hval : LSeries (fun n ↦ ∑ᶠ I ∈ {I : Ideal (𝓞 K) | absNorm I = n}, f I) s =
      ∑' I, f I * (absNorm I : ℂ) ^ (-s) by
    rw [hval]; exact hsum.hasSum
  rw [← h1.tsum_eq, LSeries]
  congr 1
  funext n
  have hfin : ∑ᶠ I ∈ {I : Ideal (𝓞 K) | absNorm I = n}, f I =
      ∑' I : {I : Ideal (𝓞 K) // absNorm I = n}, f I := by
    rw [← finsum_set_coe_eq_finsum_mem, tsum_eq_finsum (Set.toFinite _)]
    rfl
  have hterm : ∀ I : {I : Ideal (𝓞 K) // absNorm I = n},
      f (e ⟨n, I⟩) * (absNorm (e ⟨n, I⟩) : ℂ) ^ (-s) = f I * (n : ℂ) ^ (-s) := by
    intro I
    show f I * (absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s) = _
    rw [I.2]
  show _ = ∑' I : {I : Ideal (𝓞 K) // absNorm I = n}, f (e ⟨n, I⟩) * (absNorm (e ⟨n, I⟩) : ℂ) ^ (-s)
  rw [tsum_congr hterm, tsum_mul_right, ← hfin]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero, zero_cpow (neg_ne_zero.mpr hs0)]
  · rw [LSeries.term_of_ne_zero hn.ne', cpow_neg, div_eq_mul_inv]

end ArtinPrimitiveRoots.T12A

end
end

section
section
/-! # T12A_Prin: removing Euler factors from `ζ_K`

For a finite set `T` of primes and `Re s > 1`,
`∑_{I coprime to T} N(I)^{-s} = ∏_{v ∈ T} (1 - N(v)^{-s}) · ζ_K(s)`. -/

set_option maxHeartbeats 4000000
set_option autoImplicit false

open NumberField Complex Ideal IsDedekindDomain

namespace ArtinPrimitiveRoots.T12A

variable {K : Type*} [Field K] [NumberField K]

open Classical in
/-- `1` on ideals divisible by no prime of `T`, `0` otherwise. -/
noncomputable def coprimeInd (T : Finset (HeightOneSpectrum (𝓞 K))) (I : Ideal (𝓞 K)) : ℂ :=
  if ∀ v ∈ T, ¬ v.asIdeal ∣ I then 1 else 0

/-- The partial zeta function of ideals coprime to `T`. -/
noncomputable def zetaCop (T : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  ∑' I : Ideal (𝓞 K), coprimeInd T I * (absNorm I : ℂ) ^ (-s)

theorem zetaCop_empty {s : ℂ} (hs : 1 < s.re) : zetaCop (K := K) ∅ s = dedekindZeta K s := by
  have h := hasSum_ideal (K := K) (fun _ ↦ (1 : ℂ)) (fun _ ↦ by simp) hs
  have hind : ∀ I : Ideal (𝓞 K), coprimeInd ∅ I = 1 := fun I ↦ by simp [coprimeInd]
  rw [zetaCop]
  simp_rw [hind]
  rw [h.tsum_eq, dedekindZeta]
  refine LSeries_congr (fun {n} _ ↦ ?_) s
  rw [finsum_mem_eq_finite_toFinset_sum _ (Ideal.finite_setOfPred_absNorm_eq n),
    Finset.sum_const, nsmul_eq_mul, mul_one]
  have hc : Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} =
      (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n).toFinset.card :=
    Nat.card_eq_card_finite_toFinset (Ideal.finite_setOfPred_absNorm_eq n)
  rw [hc]

end ArtinPrimitiveRoots.T12A

end
end

section
section
/-! # L3Q_ZS_Dev: the ζ_F package (seam of 85b89dd7), statement verbatim

From `C3P.exists_R0` (8087d96f, 4f76b464), `C3P.exists_dedekindZeta_bound`, `T12A` (Dirichlet
series of ζ_F) and `T12B.sieve`. Does not import its own stub. -/

namespace ArtinPrimitiveRoots

open NumberField Complex

namespace L3QZS

variable (F : Type*) [Field F] [NumberField F]

noncomputable def R0 : ℂ → ℂ := (C3P.exists_R0 F).choose

theorem R0_eq {s : ℂ} (hs : 1 < s.re) : R0 F s = (s - 1) * dedekindZeta F s :=
  (C3P.exists_R0 F).choose_spec.2.1 s hs

theorem R0_bound (X : ℝ) : ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
    ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ X → ‖R0 F s‖ ≤ C * (1 + |s.im|) ^ A := by
  obtain ⟨C, A, hA, hC⟩ := (C3P.exists_R0 F).choose_spec.2.2.2
  obtain ⟨B, hB⟩ := C3P.exists_dedekindZeta_bound F
  refine ⟨max (max C 0 * 2 ^ A) (max B 0 * (|X| + 2)), max A 1, by positivity, by positivity,
    fun s h1 h2 => ?_⟩
  have h1t : 1 ≤ 1 + |s.im| := by linarith [abs_nonneg s.im]
  rcases le_or_gt s.re (5 / 2) with h3 | h3
  · have h := hC s h1 h3
    have h2t : 2 + |s.im| ≤ 2 * (1 + |s.im|) := by linarith [abs_nonneg s.im]
    calc ‖(C3P.exists_R0 F).choose s‖ ≤ C * (2 + |s.im|) ^ A := h
      _ ≤ max C 0 * (2 * (1 + |s.im|)) ^ A := by
          gcongr
          · exact le_max_left _ _
      _ = max C 0 * 2 ^ A * (1 + |s.im|) ^ A := by
          rw [Real.mul_rpow (by norm_num) (by positivity)]; ring
      _ ≤ max (max C 0 * 2 ^ A) (max B 0 * (|X| + 2)) * (1 + |s.im|) ^ max A 1 := by
          gcongr
          · exact le_max_left _ _
          · exact le_max_left _ _
  · have hs1 : 1 < s.re := by linarith
    have hz := hB s h3.le
    show ‖R0 F s‖ ≤ _
    rw [R0_eq F hs1, norm_mul]
    have hsn : ‖s - 1‖ ≤ (|X| + 2) * (1 + |s.im|) := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp only [sub_re, one_re, sub_im, one_im, sub_zero]
      rw [abs_of_nonneg (by linarith)]
      nlinarith [abs_nonneg s.im, le_abs_self X]
    have hp : (1 + |s.im|) ≤ (1 + |s.im|) ^ max A 1 := by
      conv_lhs => rw [← Real.rpow_one (1 + |s.im|)]
      exact Real.rpow_le_rpow_of_exponent_le h1t (le_max_right _ _)
    calc ‖s - 1‖ * ‖dedekindZeta F s‖ ≤ ((|X| + 2) * (1 + |s.im|)) * max B 0 :=
          mul_le_mul hsn (hz.trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
      _ = max B 0 * (|X| + 2) * (1 + |s.im|) := by ring
      _ ≤ max (max C 0 * 2 ^ A) (max B 0 * (|X| + 2)) * (1 + |s.im|) ^ max A 1 := by
          gcongr
          · exact le_max_right _ _

end L3QZS

theorem exists_differentiable_eq_sub_one_mul_dedekindZeta_and_norm_le_and_tsum_indicator_eq
    (F : Type*) [Field F] [NumberField F] :
    ∃ R : ℂ → ℂ, Differentiable ℂ R ∧
      (∀ s : ℂ, 1 < s.re → R s = (s - 1) * dedekindZeta F s) ∧
      R 1 = (dedekindZeta_residue F : ℂ) ∧
      (∀ X : ℝ, ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ X →
        ‖R s‖ ≤ C * (1 + |s.im|) ^ A) ∧
      (∀ s : ℂ, 1 < s.re → dedekindZeta F s = ∑' I : Ideal (𝓞 F), (Ideal.absNorm I : ℂ) ^ (-s)) ∧
      (∀ σ : ℝ, 1 < σ → Summable fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ)) ∧
      (∀ g : Ideal (𝓞 F) → ℂ, (∀ I J, g (I * J) = g I * g J) → Summable g →
        ∀ T : Finset (Ideal (𝓞 F)), (∀ P ∈ T, P.IsPrime ∧ P ≠ ⊥) →
          (∑' I, g I) * ∏ P ∈ T, (1 - g P) =
            ∑' I, ({I | ∀ P ∈ T, ¬ I ≤ P} : Set (Ideal (𝓞 F))).indicator g I) := by
  refine ⟨L3QZS.R0 F, (C3P.exists_R0 F).choose_spec.1, fun s hs => L3QZS.R0_eq F hs,
    (C3P.exists_R0 F).choose_spec.2.2.1, L3QZS.R0_bound F, fun s hs => ?_,
    fun σ hσ => T12B.summable_absNorm_rpow hσ, fun g hmul hg T hT => T12B.sieve g hmul hg T hT⟩
  rw [← T12A.zetaCop_empty hs, T12A.zetaCop]
  congr 1; funext I
  simp [T12A.coprimeInd]

end ArtinPrimitiveRoots

end
end

section
open ArtinPrimitiveRoots

open NumberField

theorem solution
    (F : Type*) [Field F] [NumberField F] :
    ∃ R : ℂ → ℂ, Differentiable ℂ R ∧
      (∀ s : ℂ, 1 < s.re → R s = (s - 1) * dedekindZeta F s) ∧
      R 1 = (dedekindZeta_residue F : ℂ) ∧
      (∀ X : ℝ, ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ X →
        ‖R s‖ ≤ C * (1 + |s.im|) ^ A) ∧
      (∀ s : ℂ, 1 < s.re → dedekindZeta F s = ∑' I : Ideal (𝓞 F), (Ideal.absNorm I : ℂ) ^ (-s)) ∧
      (∀ σ : ℝ, 1 < σ → Summable fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ)) ∧
      (∀ g : Ideal (𝓞 F) → ℂ, (∀ I J, g (I * J) = g I * g J) → Summable g →
        ∀ T : Finset (Ideal (𝓞 F)), (∀ P ∈ T, P.IsPrime ∧ P ≠ ⊥) →
          (∑' I, g I) * ∏ P ∈ T, (1 - g P) =
            ∑' I, ({I | ∀ P ∈ T, ¬ I ≤ P} : Set (Ideal (𝓞 F))).indicator g I) := by
  exact ArtinPrimitiveRoots.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_norm_le_and_tsum_indicator_eq F

end
