-- Prove2me | solution 1 for ArtinPrimitiveRoots.heckeLSeries_euler_package_of_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T11:06:23.456722+00:00
-- url     : https://prove2.me/submissions/6c855ba0-28cb-49ce-945f-626c63005cad

import Mathlib
import Definitions.Def_ArtinHecke

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

theorem toFun_top {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) : χ.toFun ⊤ = 1 := by
  have := χ.map_principal' 1 one_ne_zero (by simp)
  rwa [Ideal.span_singleton_one] at this

theorem toFun_bot {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) : χ.toFun ⊥ = 0 :=
  (χ.eq_zero_iff' ⊥).2 (Or.inl rfl)

theorem toFun_pow {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (I : Ideal (𝓞 F)) (n : ℕ) :
    χ.toFun (I ^ n) = χ.toFun I ^ n := by
  induction n with
  | zero => simp [Ideal.one_eq_top, toFun_top]
  | succ n ih => rw [pow_succ, χ.map_mul', ih, pow_succ]

/-- **(a)** A Hecke character of nonzero modulus takes values of norm `≤ 1`. -/
theorem norm_le_one {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) (χ : HeckeChar F 𝔪) (I : Ideal (𝓞 F)) :
    ‖χ.toFun I‖ ≤ 1 := by
  by_cases h0 : χ.toFun I = 0
  · simp [h0]
  have hI : I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤ := by
    have := (χ.eq_zero_iff' I).not.1 h0
    push Not at this
    exact this
  set h := Fintype.card (ClassGroup (𝓞 F)) with hh
  have hpos : 0 < h := Fintype.card_pos
  have hI0 : I ∈ (Ideal (𝓞 F))⁰ := mem_nonZeroDivisors_of_ne_zero hI.1
  have hIh0 : I ^ h ∈ (Ideal (𝓞 F))⁰ := pow_mem hI0 h
  have hprin : (I ^ h).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff hIh0]
    have : (⟨I ^ h, hIh0⟩ : (Ideal (𝓞 F))⁰) = ⟨I, hI0⟩ ^ h := rfl
    rw [this, map_pow, hh, pow_card_eq_one]
  set β := Submodule.IsPrincipal.generator (I ^ h)
  have hβ : Ideal.span {β} = I ^ h := Ideal.span_singleton_generator (I ^ h)
  have hβ0 : β ≠ 0 := by
    intro hb
    rw [hb, Ideal.span_singleton_eq_bot.2 rfl] at hβ
    exact hI.1 (pow_eq_zero_iff hpos.ne' |>.1 hβ.symm)
  have hcop : Ideal.span {β} ⊔ 𝔪 = ⊤ := by
    rw [hβ, sup_comm]
    exact Ideal.sup_pow_eq_top' (by rw [sup_comm]; exact hI.2)
  have hunit : IsUnit (Ideal.Quotient.mk 𝔪 β) := by
    have h1 : (1 : 𝓞 F) ∈ Ideal.span {β} ⊔ 𝔪 := by rw [hcop]; trivial
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk 𝔪 a) ?_
    rw [← map_mul, mul_comm, ← sub_eq_iff_eq_add.2 hyz.symm, map_sub, map_one,
      Ideal.Quotient.eq_zero_iff_mem.2 hz, sub_zero]
  have : Finite (𝓞 F ⧸ 𝔪) := Ideal.finiteQuotientOfFreeOfNeBot 𝔪 h𝔪
  have : Finite (𝓞 F ⧸ 𝔪)ˣ := Finite.of_injective _ Units.val_injective
  set k := Nat.card (𝓞 F ⧸ 𝔪)ˣ
  have hk : 0 < k := Nat.card_pos
  have hβk : Ideal.Quotient.mk 𝔪 (β ^ k) = Ideal.Quotient.mk 𝔪 1 := by
    rw [map_pow, map_one, ← hunit.unit_spec, ← Units.val_pow_eq_pow_val, pow_card_eq_one',
      Units.val_one]
  have hval := χ.map_principal' (β ^ k) (pow_ne_zero _ hβ0) (Ideal.Quotient.eq.1 hβk)
  rw [← Ideal.span_singleton_pow, hβ, ← pow_mul, toFun_pow] at hval
  exact (Complex.norm_eq_one_of_pow_eq_one hval (Nat.mul_ne_zero hpos.ne' hk.ne')).le

/-! ### The Dirichlet series as a sum over ideals -/

/-- `g_s(I) = χ(I) N(I)^{-s}`. -/
noncomputable def gs {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (s : ℂ) (I : Ideal (𝓞 F)) : ℂ :=
  χ.toFun I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)

theorem gs_mul {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (s : ℂ) (I J : Ideal (𝓞 F)) :
    gs χ s (I * J) = gs χ s I * gs χ s J := by
  simp only [gs, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, χ.map_mul']
  ring

theorem gs_bot {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (s : ℂ) : gs χ s ⊥ = 0 := by
  simp [gs, toFun_bot]

theorem gs_top {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (s : ℂ) : gs χ s ⊤ = 1 := by
  simp [gs, toFun_top]

theorem norm_gs_le {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (hχ : ∀ I, ‖χ.toFun I‖ ≤ 1)
    {s : ℂ} {σ : ℝ} (hσ : σ ≤ s.re) (I : Ideal (𝓞 F)) :
    ‖gs χ s I‖ ≤ ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ) := by
  by_cases hI : Ideal.absNorm I = 0
  · rw [Ideal.absNorm_eq_zero_iff.1 hI, gs_bot, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h1 : (1 : ℝ) ≤ (Ideal.absNorm I : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hI
  rw [gs, norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hI), Complex.neg_re]
  calc ‖χ.toFun I‖ * (Ideal.absNorm I : ℝ) ^ (-s.re)
      ≤ 1 * (Ideal.absNorm I : ℝ) ^ (-σ) :=
        mul_le_mul (hχ I) (Real.rpow_le_rpow_of_exponent_le h1 (by linarith))
          (Real.rpow_nonneg (by positivity) _) zero_le_one
    _ = _ := one_mul _

theorem summable_gs {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (hχ : ∀ I, ‖χ.toFun I‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) : Summable (gs χ s) :=
  Summable.of_norm_bounded (summable_absNorm_rpow hs) (norm_gs_le χ hχ le_rfl)

/-- `L(s, χ) = ∑'_I χ(I) N(I)^{-s}` on `Re s > 1`. -/
theorem lseries_eq_tsum {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (hχ : ∀ I, ‖χ.toFun I‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) : χ.LSeries s = ∑' I, gs χ s I := by
  let e := Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)
  have hsum := summable_gs χ hχ hs
  have hs2 : Summable (fun p => gs χ s (e p)) := (e.summable_iff).2 hsum
  rw [← e.tsum_eq, hs2.tsum_sigma, HeckeChar.LSeries, LSeries]
  congr 1
  funext n
  have hfib : ∀ y : {I : Ideal (𝓞 F) // Ideal.absNorm I = n},
      gs χ s (e ⟨n, y⟩) = χ.toFun y.1 * (n : ℂ) ^ (-s) := fun y => by
    simp [e, Equiv.sigmaFiberEquiv, gs, y.2]
  simp only [hfib]
  rw [tsum_mul_right]
  have hcoeff : (∑' y : {I : Ideal (𝓞 F) // Ideal.absNorm I = n}, χ.toFun y.1) = χ.coeff n := by
    rw [HeckeChar.coeff, finsum_mem_def,
      ← tsum_eq_finsum (L := SummationFilter.unconditional (Ideal (𝓞 F)))
        ((Ideal.finite_setOfPred_absNorm_eq n).subset
        Set.support_indicator_subset),
      ← tsum_subtype]
    rfl
  rw [hcoeff]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, Nat.cast_zero, Complex.zero_cpow, mul_zero]
    intro h
    have : s = 0 := neg_eq_zero.1 h
    rw [this, Complex.zero_re] at hs
    linarith
  · rw [LSeries.term_of_ne_zero hn, Complex.cpow_neg, div_eq_mul_inv]

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

/-- For each `I ∈ S` with `I ≠ ⊥, ⊤`, a chosen maximal ideal containing it. -/
noncomputable def primesOf (S : Finset (Ideal (𝓞 F))) : Finset (Ideal (𝓞 F)) := by
  classical
  exact (S.filter (fun I => I ≠ ⊤ ∧ I ≠ ⊥)).image
    (fun I => if h : I ≠ ⊤ then (Ideal.exists_le_maximal I h).choose else ⊤)

theorem primesOf_spec (S : Finset (Ideal (𝓞 F))) :
    (∀ P ∈ primesOf S, P.IsPrime ∧ P ≠ ⊥) ∧
      ∀ I ∈ S, I ≠ ⊤ → I ≠ ⊥ → ∃ P ∈ primesOf S, I ≤ P := by
  classical
  constructor
  · intro P hP
    simp only [primesOf, Finset.mem_image, Finset.mem_filter] at hP
    obtain ⟨I, ⟨-, hI, hI0⟩, rfl⟩ := hP
    rw [dif_pos hI]
    obtain ⟨hM, hle⟩ := (Ideal.exists_le_maximal I hI).choose_spec
    refine ⟨hM.isPrime, fun hb => hI0 ?_⟩
    rw [hb] at hle
    exact le_bot_iff.1 hle
  · intro I hI hIt hIb
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hI, hIt, hIb⟩), ?_⟩
    simp only [dif_pos hIt]
    exact (Ideal.exists_le_maximal I hIt).choose_spec.2

theorem sieve_bound (g : Ideal (𝓞 F) → ℂ) (hmul : ∀ I J, g (I * J) = g I * g J)
    (h0 : g ⊥ = 0) (h1 : g ⊤ = 1) (f : Ideal (𝓞 F) → ℝ) (hf : Summable f)
    (hgf : ∀ I, ‖g I‖ ≤ f I) (S : Finset (Ideal (𝓞 F))) :
    ‖(∑' I, g I) * ∏ P ∈ primesOf S, (1 - g P) - 1‖ ≤ ∑' I : {I // I ∉ S}, f I := by
  classical
  have hg : Summable g := Summable.of_norm_bounded hf hgf
  obtain ⟨hT, hcov⟩ := primesOf_spec S
  rw [sieve g hmul hg _ hT]
  have hite : Summable (fun I : Ideal (𝓞 F) => if I = ⊤ then (1 : ℂ) else 0) :=
    (hasSum_ite_eq ⊤ (1 : ℂ)).summable
  have hf0 : ∀ I, 0 ≤ f I := fun I => (norm_nonneg _).trans (hgf I)
  have hpt : ∀ I, ‖(Cop (primesOf S)).indicator g I - (if I = ⊤ then (1 : ℂ) else 0)‖ ≤
      ({I | I ∉ S} : Set (Ideal (𝓞 F))).indicator f I := by
    intro I
    by_cases hIt : I = ⊤
    · subst hIt
      have : (⊤ : Ideal (𝓞 F)) ∈ Cop (primesOf S) := fun P hP hle =>
        (hT P hP).1.ne_top (top_le_iff.1 hle)
      rw [Set.indicator_of_mem this, h1, if_pos rfl, sub_self, norm_zero]
      exact Set.indicator_nonneg (fun I _ => hf0 I) _
    rw [if_neg hIt, sub_zero]
    by_cases hS : I ∈ S
    · rw [Set.indicator_of_notMem (show I ∉ {I | I ∉ S} from fun h => h hS)]
      by_cases hIb : I = ⊥
      · subst hIb
        rw [norm_le_zero_iff]
        simp [Set.indicator, h0]
      · obtain ⟨P, hP, hle⟩ := hcov I hS hIt hIb
        have hn : I ∉ Cop (primesOf S) := by
          intro h
          simp only [Cop, Set.mem_setOf_eq] at h
          exact h P hP hle
        rw [Set.indicator_of_notMem hn, norm_zero]
    · rw [Set.indicator_of_mem (show I ∈ {I | I ∉ S} from hS)]
      exact (norm_indicator_le_norm_self _ _).trans (hgf I)
  rw [← tsum_ite_eq (⊤ : Ideal (𝓞 F)) (fun _ => (1 : ℂ)), ← (hg.indicator _).tsum_sub hite]
  have hsn : Summable (fun I => ‖(Cop (primesOf S)).indicator g I -
      (if I = ⊤ then (1 : ℂ) else 0)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (hf.indicator _)
  refine (norm_tsum_le_tsum_norm hsn).trans ?_
  refine (hsn.tsum_le_tsum hpt (hf.indicator _)).trans_eq ?_
  exact (tsum_subtype {I | I ∉ S} f).symm

/-- A finite set outside of which the tail of `f` is small. -/
theorem exists_tail_lt (f : Ideal (𝓞 F) → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset (Ideal (𝓞 F)), ∑' I : {I // I ∉ S}, f I < ε :=
  ((tendsto_tsum_compl_atTop_zero f).eventually (gt_mem_nhds hε)).exists

end T12B

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField

namespace T12B

variable {F : Type*} [Field F] [NumberField F]

/-- The restriction of `χ` to a smaller modulus `𝔪' ≤ 𝔪`: `χ` on ideals coprime to `𝔪'`,
`0` elsewhere. -/
noncomputable def restrictChar {𝔪 𝔪' : Ideal (𝓞 F)} (hle : 𝔪' ≤ 𝔪) (χ : HeckeChar F 𝔪) :
    HeckeChar F 𝔪' where
  toFun I := if I ⊔ 𝔪' = ⊤ then χ.toFun I else 0
  map_mul' I J := by
    have hc : I * J ⊔ 𝔪' = ⊤ ↔ I ⊔ 𝔪' = ⊤ ∧ J ⊔ 𝔪' = ⊤ := by
      simp only [← Ideal.isCoprime_iff_sup_eq, IsCoprime.mul_left_iff]
    by_cases hI : I ⊔ 𝔪' = ⊤ <;> by_cases hJ : J ⊔ 𝔪' = ⊤ <;>
      simp [hc, hI, hJ, χ.map_mul']
  eq_zero_iff' I := by
    by_cases hI : I ⊔ 𝔪' = ⊤
    · have hI' : I ⊔ 𝔪 = ⊤ := top_unique (hI ▸ sup_le_sup_left hle I)
      simp [hI, χ.eq_zero_iff', hI']
    · simp [hI]
  map_principal' α hα h1 := by
    have hcop : Ideal.span {α} ⊔ 𝔪' = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      have : (1 : 𝓞 F) = α - (α - 1) := by ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self α))
        (Ideal.mem_sup_right h1)
    simp only [hcop, if_true]
    exact χ.map_principal' α hα (hle h1)

/-- (b) and (c) for any character of nonzero modulus. -/
theorem ne_zero_and_bound {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) (χ : HeckeChar F 𝔪) :
    (∀ s : ℂ, 1 < s.re → χ.LSeries s ≠ 0) ∧
    (∃ B : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖(χ.LSeries s)⁻¹‖ ≤ B) := by
  have hχ := norm_le_one h𝔪 χ
  constructor
  · intro s hs
    obtain ⟨S, hS⟩ := exists_tail_lt (fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-s.re))
      (by norm_num : (0 : ℝ) < 1 / 2)
    have hb := sieve_bound (gs χ s) (gs_mul χ s) (gs_bot χ s) (gs_top χ s) _
      (summable_absNorm_rpow hs) (norm_gs_le χ hχ le_rfl) S
    rw [← lseries_eq_tsum χ hχ hs] at hb
    intro h0
    rw [h0, zero_mul, zero_sub, norm_neg, norm_one] at hb
    linarith
  · obtain ⟨S, hS⟩ := exists_tail_lt (fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-2 : ℝ))
      (by norm_num : (0 : ℝ) < 1 / 2)
    set f : Ideal (𝓞 F) → ℝ := fun I => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-2 : ℝ)
    have hf0 : ∀ I, 0 ≤ f I := fun I => Real.rpow_nonneg (Nat.cast_nonneg _) _
    set C := ∏ P ∈ primesOf S, (1 + f P) with hC
    have hCpos : 0 < C := Finset.prod_pos fun P _ => by linarith [hf0 P]
    refine ⟨2 * C, fun s hs => ?_⟩
    have hs1 : 1 < s.re := by linarith
    have hb := sieve_bound (gs χ s) (gs_mul χ s) (gs_bot χ s) (gs_top χ s) f
      (summable_absNorm_rpow (by norm_num : (1 : ℝ) < 2)) (norm_gs_le χ hχ hs) S
    rw [← lseries_eq_tsum χ hχ hs1] at hb
    have hprod : ‖∏ P ∈ primesOf S, (1 - gs χ s P)‖ ≤ C := by
      refine (Finset.norm_prod_le _ _).trans (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        fun P _ => ?_)
      exact (norm_sub_le _ _).trans (by rw [norm_one]; linarith [norm_gs_le χ hχ hs P])
    have hlow : 1 / 2 ≤ ‖χ.LSeries s‖ * C := by
      have h1 : (1 : ℝ) ≤ ‖χ.LSeries s * ∏ P ∈ primesOf S, (1 - gs χ s P)‖ + 1 / 2 := by
        have := norm_sub_norm_le (1 : ℂ) (χ.LSeries s * ∏ P ∈ primesOf S, (1 - gs χ s P))
        rw [norm_one, norm_sub_rev] at this
        linarith
      rw [norm_mul] at h1
      nlinarith [norm_nonneg (χ.LSeries s)]
    have hL : 0 < ‖χ.LSeries s‖ := by
      by_contra h
      have : ‖χ.LSeries s‖ = 0 := le_antisymm (not_lt.1 h) (norm_nonneg _)
      rw [this, zero_mul] at hlow
      linarith
    rw [norm_inv, inv_le_comm₀ hL (by positivity)]
    rw [inv_eq_one_div, div_le_iff₀ (by positivity)]
    nlinarith

end T12B

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open NumberField
open T12B in
theorem solution (F : Type*) [Field F] [NumberField F]
    (𝔪 𝔪' : Ideal (𝓞 F))
    (h𝔪' : 𝔪' ≠ ⊥) (hle : 𝔪' ≤ 𝔪) (χ : HeckeChar F 𝔪) :
    (∀ I : Ideal (𝓞 F), ‖χ.toFun I‖ ≤ 1) ∧
    (∀ s : ℂ, 1 < s.re → χ.LSeries s ≠ 0) ∧
    (∃ B : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖(χ.LSeries s)⁻¹‖ ≤ B) ∧
    ∃ χ' : HeckeChar F 𝔪', (∀ I : Ideal (𝓞 F), I ⊔ 𝔪' = ⊤ → χ'.toFun I = χ.toFun I) ∧
      ∀ s : ℂ, 1 < s.re → χ.LSeries s = χ'.LSeries s *
        ∏ᶠ (P : Ideal (𝓞 F)) (_ : P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪' ≤ P ∧ P ⊔ 𝔪 = ⊤),
          (1 - χ.toFun P * (Ideal.absNorm P : ℂ) ^ (-s))⁻¹ := by
  classical
  have h𝔪 : 𝔪 ≠ ⊥ := fun h => h𝔪' (le_bot_iff.1 (h ▸ hle))
  have hχ := norm_le_one h𝔪 χ
  obtain ⟨hne, hB⟩ := ne_zero_and_bound h𝔪 χ
  refine ⟨hχ, hne, hB, restrictChar hle χ, fun I hI => by simp [restrictChar, hI], ?_⟩
  intro s hs
  set χ' := restrictChar hle χ
  have hχ' := norm_le_one h𝔪' χ'
  -- the finite set of primes
  have hfin : {P : Ideal (𝓞 F) | P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪' ≤ P ∧ P ⊔ 𝔪 = ⊤}.Finite := by
    refine (Ideal.finite_setOfPred_absNorm_le (Ideal.absNorm 𝔪')).subset ?_
    intro P ⟨_, _, hle', _⟩
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]))
      (Ideal.absNorm_dvd_absNorm_of_le hle')
  set T := hfin.toFinset with hT
  have hTmem : ∀ P, P ∈ T ↔ P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪' ≤ P ∧ P ⊔ 𝔪 = ⊤ := fun P => by
    simp [hT]
  have hTp : ∀ P ∈ T, P.IsPrime ∧ P ≠ ⊥ := fun P hP =>
    ⟨((hTmem P).1 hP).1, ((hTmem P).1 hP).2.1⟩
  -- the sieve identity
  have hsv := sieve (gs χ s) (gs_mul χ s) (summable_gs χ hχ hs) T hTp
  have hind : (Cop T).indicator (gs χ s) = gs χ' s := by
    funext I
    by_cases hI : I ⊔ 𝔪' = ⊤
    · have hc : I ∈ Cop T := by
        intro P hP hIP
        obtain ⟨hPp, -, hmP, -⟩ := (hTmem P).1 hP
        exact hPp.ne_top (top_unique (hI ▸ sup_le hIP hmP))
      rw [Set.indicator_of_mem hc]
      simp [gs, χ', restrictChar, hI]
    · have h' : gs χ' s I = 0 := by simp [gs, χ', restrictChar, hI]
      rw [h']
      by_cases h0 : χ.toFun I = 0
      · simp [Set.indicator, gs, h0]
      have hI2 : I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤ := by
        have := (χ.eq_zero_iff' I).not.1 h0
        push Not at this
        exact this
      obtain ⟨P, hPmax, hPle⟩ := Ideal.exists_le_maximal _ hI
      have hP : P ∈ T := by
        refine (hTmem P).2 ⟨hPmax.isPrime, ?_, le_sup_right.trans hPle, ?_⟩
        · intro hb
          exact hI2.1 (le_bot_iff.1 (hb ▸ le_sup_left.trans hPle))
        · exact top_unique (hI2.2 ▸ sup_le_sup_right (le_sup_left.trans hPle) 𝔪)
      have hn : I ∉ Cop T := fun hc => hc P hP (le_sup_left.trans hPle)
      exact Set.indicator_of_notMem hn _
  rw [hind, ← lseries_eq_tsum χ hχ hs, ← lseries_eq_tsum χ' hχ' hs] at hsv
  -- the finite product
  have hfp : (∏ᶠ (P : Ideal (𝓞 F)) (_ : P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪' ≤ P ∧ P ⊔ 𝔪 = ⊤),
      (1 - χ.toFun P * (Ideal.absNorm P : ℂ) ^ (-s))⁻¹) = (∏ P ∈ T, (1 - gs χ s P))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact finprod_mem_eq_finite_toFinset_prod _ hfin
  rw [hfp]
  have hPi : ∏ P ∈ T, (1 - gs χ s P) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hsv
    exact (ne_zero_and_bound h𝔪' χ').1 s hs hsv.symm
  rw [← hsv, mul_assoc, mul_inv_cancel₀ hPi, mul_one]
end
