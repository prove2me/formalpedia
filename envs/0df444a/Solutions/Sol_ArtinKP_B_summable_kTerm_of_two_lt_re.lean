-- Prove2me | solution 1 for ArtinKP.B.summable_kTerm_of_two_lt_re
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:29:01.534473+00:00
-- url     : https://prove2.me/submissions/8ecfd116-88cf-4867-adb5-f08c3e2a6f92

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeSModel
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_ArtinKPB002

section
-- module Solutions.Artin.T12.L2B_Quot
/-!
# L2B_Quot: exterior ideals of `𝓞 F` and of `R` (copied from L2A_FSQuot, prover A, to decouple)

* `exists_pow_mul_mem`: every `r ∈ R` has `𝔪^N r ⊆ 𝓞`.
* `mem_of_map_mem`: `I R ∩ 𝓞 = I` for `I + 𝔪 = 1`.
* `exists_sub_mem_map`: `𝓞 → R / I R` is onto for `I + 𝔪 = 1`; `finite_quot_map`,

-/

open NumberField IsDedekindDomain WithZero

namespace ArtinPrimitiveRoots.L2B

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- `I R ∩ 𝓞 = I` for an ideal `I` coprime to `𝔪`. -/
lemma mem_of_map_mem (I : Ideal (𝓞 F)) (hI : I ⊔ 𝔪 = ⊤) (a : 𝓞 F)
    (ha : algebraMap (𝓞 F) (SInt 𝔪) a ∈ I.map (algebraMap (𝓞 F) (SInt 𝔪))) : a ∈ I := by
  set φ := algebraMap (𝓞 F) (SInt 𝔪)
  have hinj : Function.Injective φ := by
    intro x y hxy
    have := congrArg (fun z : SInt 𝔪 => (z : F)) hxy
    simp only [φ, C3I.coe_alg] at this
    exact IsFractionRing.injective (𝓞 F) F this
  -- the predicate
  have hQ : ∀ x ∈ I.map φ, ∃ N : ℕ, ∀ w ∈ 𝔪 ^ N, ∃ i ∈ I, φ w * x = φ i := by
    intro x hx
    rw [Ideal.map] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i0, hi0, rfl⟩ := hx
      exact ⟨0, fun w _ => ⟨w * i0, I.mul_mem_left _ hi0, by rw [map_mul]⟩⟩
    | zero => exact ⟨0, fun w _ => ⟨0, I.zero_mem, by simp⟩⟩
    | add x y _ _ hx hy =>
      obtain ⟨N1, h1⟩ := hx
      obtain ⟨N2, h2⟩ := hy
      refine ⟨max N1 N2, fun w hw => ?_⟩
      obtain ⟨i1, hi1, e1⟩ := h1 w (Ideal.pow_le_pow_right (le_max_left _ _) hw)
      obtain ⟨i2, hi2, e2⟩ := h2 w (Ideal.pow_le_pow_right (le_max_right _ _) hw)
      exact ⟨i1 + i2, I.add_mem hi1 hi2, by rw [mul_add, e1, e2, map_add]⟩
    | smul r x _ hx =>
      obtain ⟨Nx, hNx⟩ := hx
      obtain ⟨Nr, hNr⟩ := exists_pow_mul_mem (𝔪 := 𝔪) r
      refine ⟨Nr + Nx, fun w hw => ?_⟩
      rw [pow_add] at hw
      refine Submodule.mul_induction_on hw ?_ ?_
      · intro w1 hw1 w2 hw2
        obtain ⟨c, hc⟩ := hNr w1 hw1
        obtain ⟨i, hi, ei⟩ := hNx w2 hw2
        refine ⟨c * i, I.mul_mem_left _ hi, ?_⟩
        rw [smul_eq_mul, map_mul, map_mul, ← hc, ← ei]; ring
      · rintro w1 w2 ⟨i1, hi1, e1⟩ ⟨i2, hi2, e2⟩
        exact ⟨i1 + i2, I.add_mem hi1 hi2, by rw [map_add, add_mul, e1, e2, map_add]⟩
  obtain ⟨N, hN⟩ := hQ _ ha
  have hcop : IsCoprime I (𝔪 ^ N) := (Ideal.isCoprime_iff_sup_eq.mpr hI).pow_right
  obtain ⟨u, hu, w, hw, huw⟩ := hcop.exists
  obtain ⟨i, hi, ei⟩ := hN w hw
  have : w * a = i := hinj (by rw [map_mul, ei])
  have ha' : a = u * a + w * a := by rw [← add_mul, huw, one_mul]
  rw [ha', this]
  exact I.add_mem (I.mul_mem_right _ hu) hi

lemma quotHom_surjective (I : Ideal (𝓞 F)) (hI : I ⊔ 𝔪 = ⊤) :
    Function.Surjective (C3I.quotHom 𝔪 I) := by
  intro y
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨c, hc⟩ := exists_sub_mem_map I hI r
  exact ⟨Ideal.Quotient.mk _ c, by rw [C3I.quotHom_mk]; exact (Ideal.Quotient.eq.mpr hc).symm⟩

lemma finite_quot_map (I : Ideal (𝓞 F)) (hI0 : I ≠ ⊥) (hI : I ⊔ 𝔪 = ⊤) :
    Finite (SInt 𝔪 ⧸ I.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  have : Finite (𝓞 F ⧸ I) := Ring.HasFiniteQuotients.finiteQuotient hI0
  exact Finite.of_surjective _ (quotHom_surjective I hI)

end ArtinPrimitiveRoots.L2B
end

section
-- module Solutions.Artin.KP.B7_Link
/-! # B7_Link: the Gauss sums over `R = SInt 𝔪` and the normalization of the frozen statement

* `sAdd 𝔪 h𝔪 : AddData (SInt 𝔪) F` is `sAddChar 𝔪` (additive on all of `F`: `sAddChar_add_all`;
  trivial on `R`), so `gauss S (sAdd 𝔪 h𝔪) ν c = ∑_{d mod c} (d/c)⁻¹ sAddChar 𝔪 (ν d / c)`
  (`gauss_sAdd`).
* `finite_quot_span`: `R ⧸ (c)` is finite for `c ≠ 0`.
* At a good exterior prime `P` (`C3I.Good 𝔪 v`, automatic for `SmallPrimesDvd N₀ 𝔪`,
  `N₀ ≥ C3I.cutN F`) with `π = g.gen P` and a symbol with `(d/π) = χ_P(d)²`:
  `gaussP_one_eq_tau : g₁(π) = tau P 2 = conj (√q γ₂(P))`,
  `gaussP_two_eq_tau : g₂(π) = tau P 4 = √q γ₂(P)`, `γ₂(P) = gaussPhase g 2 P`,
  `gaussP_one_mul_two : g₁ g₂ = N P`, and the complete table `gauss_gen_table` in the form of
  `B7_System.tab` with `G = (ν₀/π) tau P 2`, `G' = (ν₀/π)² tau P 4`, `G G' = N P`, `conj G = G'`.
* `theta_ratio`: the solution of the formal system at `x₀ = q^{-4/3}` gives
  `q^{-1/3} C₁ = (ν₀/π)² · Wv P 1 · C₀` with `Wv P 1 = q^{-1/2} gaussPhase g 2 P` exactly as in the
  frozen statement (and `Wv P 0 = 1`, `Wv P 2 = 0 ↔ Ψ₂ = 0`).
-/

open NumberField IsDedekindDomain

namespace ArtinKP.B7

open ArtinPrimitiveRoots

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### The additive character -/

lemma sAdd_ψ (h𝔪 : 𝔪 ≠ ⊥) (a c : SInt 𝔪) :
    (sAdd 𝔪 h𝔪).ψ a c = sAddChar 𝔪 ((a : F) / (c : F)) := rfl

/-- `R ⧸ (c)` is finite for `c ≠ 0`. -/
theorem finite_quot_span (h𝔪 : 𝔪 ≠ ⊥) {c : SInt 𝔪} (hc : c ≠ 0) :
    Finite (SInt 𝔪 ⧸ Ideal.span {c}) := by
  have hcF : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (c : F)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbF : algebraMap (𝓞 F) F b ≠ 0 := by
    intro h; exact hb0 (by simpa using h)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hab
    exact hcF hab.symm
  have hI : Ideal.span ({a} : Set (𝓞 F)) ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨𝔄, hE, hmap⟩ := exists_exterior_map_eq 𝔪 h𝔪 _ hI
  have hle : 𝔄.map (algebraMap (𝓞 F) (SInt 𝔪)) ≤ Ideal.span {c} := by
    rw [← hmap, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_span_singleton]
    refine ⟨algebraMap (𝓞 F) (SInt 𝔪) b, Subtype.ext ?_⟩
    rw [Subalgebra.coe_mul, ← hab]
    show algebraMap (𝓞 F) F a = algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b * algebraMap (𝓞 F) F b
    field_simp
  have := L2B.finite_quot_map (𝔪 := 𝔪) 𝔄 hE.1 hE.2
  exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)

/-! ### Transport of residue sums to the quotient by an equal ideal -/

/-! ### A good exterior prime -/

end ArtinKP.B7
end

section
-- module Solutions.Artin.KP.S_Jacquet
/-!
# WP-S, part 7: finite Jacquet functionals

`F_{S_f}/𝔩` is the discrete countable group `F/𝔩_M`, `𝔩_M = {x : Small M x}` (strong
approximation is not needed to *define* the functional).  For `f : F → ℂ` invariant under `𝔩_M`:

`jac ψ M f ν = vol(𝔩_M) · Σ_{u ∈ F/𝔩_M} f(u) · conj ψ(ν u)`   (`= ∫_{F_{S_f}} f(u) conj ψ(νu) du`),

`J_Φ(c; ν, s) = jac ψ M (u ↦ Φ_s(c, cu)) ν`, `λ_η(Φ_s; ν) = |η|^s J_Φ(η; ν, s)` (`lam`).

* `lam_bigCell`: `λ_η(Φ^{big}_{η,L}; ν) = vol(𝔩) conj ψ(ν t₀)` for `ν ∈ 𝔩^⊥`.
* `jac_eq_zero`: the functional vanishes when `ψ(ν ·)` is non-trivial on a lattice of periods.
* `norm_lam_le`: the uniform bound `|c|^σ |J_Φ(c; ν, s)| ≤ B·K_σ` (MATH2 §0.2), `K_σ = vol·Σ_u
  ∏_v max(1,|u|_v)^{-σ}`.
* `kir`, `xi_bound`: the bound for the Kirillov function (MATH2 §6.3 (K2), (K3)).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

theorem vol_nonneg (M : ℤ) : 0 ≤ vol 𝔪 M :=
  Finset.prod_nonneg fun _ _ => zpow_nonneg (Nat.cast_nonneg _) _

section jac

variable (ψ : SfChar 𝔪) {M : ℤ} {f : F → ℂ} {ν : F}

/-- **Uniform bound** for the functional of a function dominated by
`C ∏_v max(1, |u|_v)^{-σ}`. -/
theorem norm_jac_le {C σ : ℝ} (hC : 0 ≤ C) (hf : ∀ u : F, ‖f u‖ ≤ C * normS 𝔪 1 u ^ (-σ))
    (hsum : Summable fun u : F ⧸ lat 𝔪 M => normS 𝔪 1 u.out ^ (-σ)) :
    ‖jac ψ M f ν‖ ≤ C * (vol 𝔪 M * ∑' u : F ⧸ lat 𝔪 M, normS 𝔪 1 u.out ^ (-σ)) := by
  have hterm : ∀ u : F ⧸ lat 𝔪 M, ‖f u.out * (starRingEnd ℂ) (ψ (ν * u.out))‖
      ≤ C * normS 𝔪 1 u.out ^ (-σ) := by
    intro u
    rw [norm_mul, RCLike.norm_conj, ψ.norm_one, mul_one]
    exact hf _
  have hsum' : Summable fun u : F ⧸ lat 𝔪 M => C * normS 𝔪 1 u.out ^ (-σ) := hsum.mul_left C
  have hsn : Summable fun u : F ⧸ lat 𝔪 M =>
      ‖f u.out * (starRingEnd ℂ) (ψ (ν * u.out))‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsum'
  rw [jac, norm_mul, Complex.norm_real, Real.norm_of_nonneg (vol_nonneg M)]
  calc vol 𝔪 M * ‖∑' u : F ⧸ lat 𝔪 M, f u.out * (starRingEnd ℂ) (ψ (ν * u.out))‖
      ≤ vol 𝔪 M * ∑' u : F ⧸ lat 𝔪 M, ‖f u.out * (starRingEnd ℂ) (ψ (ν * u.out))‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hsn) (vol_nonneg M)
    _ ≤ vol 𝔪 M * ∑' u : F ⧸ lat 𝔪 M, C * normS 𝔪 1 u.out ^ (-σ) :=
        mul_le_mul_of_nonneg_left (hsn.tsum_le_tsum hterm hsum') (vol_nonneg M)
    _ = _ := by rw [tsum_mul_left]; ring

end jac

variable {ι : F →+* ℂ} {P : CubicPkg F}

/-- **Uniform bound** `|η|^σ |J_Φ(η; ν, s)| ≤ B K_σ`, uniform in `η`, `ν` and in `|s| ≤ M₀`. -/
theorem norm_lam_le (ψ : SfChar 𝔪) (Φ : GSection ι P 𝔪) (M₀ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, ‖s‖ ≤ M₀ → ∀ (M : ℤ) (η ν : F), η ≠ 0 →
      Summable (fun u : F ⧸ lat 𝔪 M => normS 𝔪 1 u.out ^ (-s.re)) →
      ‖lam ψ M Φ η ν s‖ ≤ B * (vol 𝔪 M * ∑' u : F ⧸ lat 𝔪 M, normS 𝔪 1 u.out ^ (-s.re)) := by
  obtain ⟨B₀, hB₀⟩ := Φ.bound M₀
  refine ⟨|B₀|, abs_nonneg _, fun s hs M η ν hη hsum => ?_⟩
  have hpa := absS_pos (𝔪 := 𝔪) hη
  have hr : 0 < absS 𝔪 η ^ (-s.re) := Real.rpow_pos_of_pos hpa _
  have hf : ∀ u : F, ‖Φ s η (η * u)‖ ≤ (|B₀| * absS 𝔪 η ^ (-s.re)) * normS 𝔪 1 u ^ (-s.re) := by
    intro u
    have e : normS 𝔪 η (η * u) = absS 𝔪 η * normS 𝔪 1 u := by
      rw [← normS_mul_left, mul_one]
    have h1 := hB₀ s hs η (η * u)
    rw [e, Real.mul_rpow hpa.le (normS_nonneg _ _)] at h1
    refine h1.trans (le_of_eq_of_le (mul_assoc _ _ _).symm ?_)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hr.le)
      (Real.rpow_nonneg (normS_nonneg _ _) _)
  have h2 := norm_jac_le ψ (ν := ν) (mul_nonneg (abs_nonneg B₀) hr.le) hf hsum
  rw [lam, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpa]
  have hcancel : absS 𝔪 η ^ s.re * absS 𝔪 η ^ (-s.re) = 1 := by
    rw [← Real.rpow_add hpa, add_neg_cancel, Real.rpow_zero]
  have hK : 0 ≤ vol 𝔪 M * ∑' u : F ⧸ lat 𝔪 M, normS 𝔪 1 u.out ^ (-s.re) :=
    mul_nonneg (vol_nonneg M) (tsum_nonneg fun _ => Real.rpow_nonneg (normS_nonneg _ _) _)
  calc absS 𝔪 η ^ s.re * ‖jac ψ M (fun u => Φ s η (η * u)) ν‖
      ≤ absS 𝔪 η ^ s.re * (|B₀| * absS 𝔪 η ^ (-s.re)
          * (vol 𝔪 M * ∑' u : F ⧸ lat 𝔪 M, normS 𝔪 1 u.out ^ (-s.re))) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hpa.le _)
    _ = (absS 𝔪 η ^ s.re * absS 𝔪 η ^ (-s.re)) * (|B₀|
          * (vol 𝔪 M * ∑' u : F ⧸ lat 𝔪 M, normS 𝔪 1 u.out ^ (-s.re))) := by ring
    _ = _ := by rw [hcancel, one_mul]

/-! ### The Kirillov function -/

end ArtinKP.S
end
end

section
-- module Solutions.Artin.T12.T12B_Euler
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

theorem fiber_finite (n : ℕ) : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

/-- `∑_I N(I)^{-σ}` converges for `σ > 1`. -/
theorem summable_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ)) := by
  haveI _iFF := ArtinPrimitiveRoots.T12B.fiber_finite (F := F)
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

end T12B

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.L2B_Orth
/-!
# L2B_Orth: `#(R/𝔰R) = q_𝔰`, primitivity and orthogonality of `j ↦ e(j k / s)`

* `natCard_quot_eq`: `#(R/𝔰R) = N 𝔰` for exterior `𝔰`;
* `exists_primePow_not_mem`: `k ∉ 𝔰R` ⇒ `k ∉ P^a R` for a prime power `P^a ∣ 𝔰`;
* `exists_sAddChar_ne_one_gen`: primitivity of `j ↦ e(j k / s)` for `k ∉ 𝔰R`;
* `finsum_sAddChar`: `∑_{j mod 𝔰} e(j k / s) = q_𝔰 [k ∈ 𝔰R]`.
-/

namespace ArtinPrimitiveRoots.L2B

open NumberField IsDedekindDomain UniqueFactorizationMonoid

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {ι : F →+* ℂ}

theorem natCard_quot_eq {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞) :
    Nat.card (SInt 𝔪 ⧸ 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) = Ideal.absNorm 𝔞 := by
  have hbij : Function.Bijective (C3I.quotHom 𝔪 𝔞) := by
    refine ⟨?_, quotHom_surjective 𝔞 h𝔞.2⟩
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [C3I.quotHom_mk, Ideal.Quotient.eq_zero_iff_mem] at hy
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact mem_of_map_mem 𝔞 h𝔞.2 a hy
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Ideal.absNorm_apply, Submodule.cardQuot_apply]

end ArtinPrimitiveRoots.L2B
end

section
-- module Solutions.Artin.KP.B_Norm
/-!
# WP-B, part 3: the norm of an `S`-integer

* `extOf h𝔪 hc`: the exterior ideal `𝔠 ⊂ 𝓞` with `𝔠R = cR`, for `c ∈ R ∖ 0`.
* `natCard_quot_span`: `#(R/cR) = N𝔠`.
* **Product formula** `Ninf_mul_absS_eq`: `N_∞(c) · |c|_{S_f} = #(R/cR)` for `c ∈ R ∖ 0`
  (class-number trick: `𝔠^h` is principal in `𝓞`).
* `summable_nrm_rpow`: `∑_{c ∈ (R∖0)/Rˣ} #(R/cR)^{-t} < ∞` for `t > 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

theorem extOf_isExterior (h𝔪 : 𝔪 ≠ ⊥) {c : SInt 𝔪} (hc : c ≠ 0) :
    IsExterior 𝔪 (extOf h𝔪 hc) := (exists_ext h𝔪 hc).choose_spec.1

theorem map_extOf (h𝔪 : 𝔪 ≠ ⊥) {c : SInt 𝔪} (hc : c ≠ 0) :
    (extOf h𝔪 hc).map (algebraMap (𝓞 F) (SInt 𝔪)) = Ideal.span {c} :=
  (exists_ext h𝔪 hc).choose_spec.2

/-- `#(R/cR) = N𝔠`. -/
theorem natCard_quot_span (h𝔪 : 𝔪 ≠ ⊥) {c : SInt 𝔪} (hc : c ≠ 0) :
    Nat.card (SInt 𝔪 ⧸ Ideal.span {c}) = Ideal.absNorm (extOf h𝔪 hc) := by
  rw [← map_extOf h𝔪 hc]
  exact L2B.natCard_quot_eq (extOf_isExterior h𝔪 hc)

theorem natCard_quot_span_pos (h𝔪 : 𝔪 ≠ ⊥) {c : SInt 𝔪} (hc : c ≠ 0) :
    0 < Nat.card (SInt 𝔪 ⧸ Ideal.span {c}) := by
  rw [natCard_quot_span h𝔪 hc]
  exact Nat.pos_of_ne_zero fun h =>
    (extOf_isExterior h𝔪 hc).1 (Ideal.absNorm_eq_zero_iff.mp h)

/-- `∑_{c ∈ (R∖0)/Rˣ} #(R/cR)^{-t} < ∞` for `t > 1`. -/
theorem summable_nrm_rpow (h𝔪 : 𝔪 ≠ ⊥) {t : ℝ} (ht : 1 < t) :
    Summable fun a : Cls (SInt 𝔪) =>
      (Nat.card (SInt 𝔪 ⧸ Ideal.span {rp a.1}) : ℝ) ^ (-t) := by
  let g : Cls (SInt 𝔪) → Ideal (𝓞 F) := fun a => extOf h𝔪 (rp_ne_zero a.2)
  have hinj : Function.Injective g := by
    intro a b hab
    have h1 : Ideal.span {rp a.1} = Ideal.span {rp b.1} := by
      rw [← map_extOf h𝔪 (rp_ne_zero a.2), ← map_extOf h𝔪 (rp_ne_zero b.2)]
      exact congrArg _ hab
    have h2 := Ideal.span_singleton_eq_span_singleton.mp h1
    apply Subtype.ext
    rw [← mk_rp a.1, ← mk_rp b.1]
    exact Associates.mk_eq_mk_iff_associated.mpr h2
  have h := (T12B.summable_absNorm_rpow (F := F) ht).comp_injective hinj
  refine h.congr fun a => ?_
  simp only [Function.comp, g]
  rw [natCard_quot_span h𝔪 (rp_ne_zero a.2)]

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.RF_SNorm
/-!
# WP-RF, part 1: summability of the `S_f`-norm series (stub S-1 of WP-S)

`summable_normS_one`: for `σ > 1`, `Σ_{u ∈ F/𝔩_M} ∏_{v ∣ 𝔪} max(1, |u|_v)^{-σ} < ∞`.

Route (WP-S): a finite set of elements of `F` whose pairwise differences have `v(x-y) ≤ exp(k_v)`
for `v ∈ S` and which are pairwise incongruent modulo `{v(x) ≤ exp(k_v - n_v)}` has at most
`∏_v q_v^{n_v}` elements (`card_le_of_separated`; induction on `Σ n_v`, each step maps into the
residue field `𝓞/v`).  Grouping the cosets by the depth vector of their representative gives the
bound `∏_v q_v^{|M|} (1 - q_v^{1-σ})⁻¹` for every finite partial sum.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.RF

open ArtinKP.A ArtinKP.S

variable {F : Type*} [Field F] [NumberField F]

/-- A "residue" map at `v`: integral elements with the same residue are congruent. -/
theorem exists_residue (v : HeightOneSpectrum (𝓞 F)) :
    ∃ r : F → 𝓞 F ⧸ v.asIdeal, ∀ x y : F, v.valuation F x ≤ 1 → v.valuation F y ≤ 1 →
      r x = r y → v.valuation F (x - y) < 1 := by
  classical
  have := v.isMaximal
  let _ := Ideal.Quotient.field v.asIdeal
  have key : ∀ x : F, v.valuation F x ≤ 1 →
      ∃ p : 𝓞 F × 𝓞 F, p.2 ∉ v.asIdeal ∧ x * algebraMap (𝓞 F) F p.2 = algebraMap (𝓞 F) F p.1 := by
    intro x hx
    obtain ⟨n, d, h⟩ := v.exists_primeCompl_mul_eq_of_integer x hx
    exact ⟨(n, d.1), d.2, h⟩
  refine ⟨fun x => if h : v.valuation F x ≤ 1 then
      Ideal.Quotient.mk v.asIdeal (Classical.choose (key x h)).1
        / Ideal.Quotient.mk v.asIdeal (Classical.choose (key x h)).2 else 0, ?_⟩
  intro x y hx hy hxy
  simp only [dif_pos hx, dif_pos hy] at hxy
  obtain ⟨hdx, ex⟩ := Classical.choose_spec (key x hx)
  obtain ⟨hdy, ey⟩ := Classical.choose_spec (key y hy)
  set nx := (Classical.choose (key x hx)).1
  set dx := (Classical.choose (key x hx)).2
  set ny := (Classical.choose (key y hy)).1
  set dy := (Classical.choose (key y hy)).2
  have hdx0 : Ideal.Quotient.mk v.asIdeal dx ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hdy0 : Ideal.Quotient.mk v.asIdeal dy ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  rw [div_eq_div_iff hdx0 hdy0, ← map_mul, ← map_mul, ← sub_eq_zero, ← map_sub,
    Ideal.Quotient.eq_zero_iff_mem] at hxy
  have h1 : v.valuation F (algebraMap (𝓞 F) F (nx * dy - ny * dx)) < 1 :=
    (v.valuation_lt_one_iff_mem _).mpr hxy
  have vdx : v.valuation F (algebraMap (𝓞 F) F dx) = 1 :=
    (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) (v := v)).mpr hdx
  have vdy : v.valuation F (algebraMap (𝓞 F) F dy) = 1 :=
    (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) (v := v)).mpr hdy
  have e : (x - y) * (algebraMap (𝓞 F) F dx * algebraMap (𝓞 F) F dy)
      = algebraMap (𝓞 F) F (nx * dy - ny * dx) := by
    rw [map_sub, map_mul, map_mul, ← ex, ← ey]; ring
  have := congrArg (v.valuation F) e
  rw [map_mul, map_mul, vdx, vdy, mul_one, mul_one] at this
  rw [this]; exact h1

theorem natCard_quot (v : HeightOneSpectrum (𝓞 F)) :
    Nat.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

/-- **Counting.**  A finite set whose differences are `exp k`-bounded on `S` and which is
separated modulo depth `k - n` has at most `∏_{v ∈ S} q_v^{n_v}` elements. -/
theorem card_le_of_separated (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∀ (N : ℕ) (n : HeightOneSpectrum (𝓞 F) → ℕ) (k : HeightOneSpectrum (𝓞 F) → ℤ) (T : Finset F),
      ∑ v ∈ S, n v = N →
      (∀ x ∈ T, ∀ y ∈ T, ∀ v ∈ S, v.valuation F (x - y) ≤ WithZero.exp (k v)) →
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y →
        ¬ ∀ v ∈ S, v.valuation F (x - y) ≤ WithZero.exp (k v - n v)) →
      T.card ≤ ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ n v := by
  classical
  intro N
  induction N with
  | zero =>
    intro n k T hN h1 h2
    have hn : ∀ v ∈ S, n v = 0 := fun v hv => (Finset.sum_eq_zero_iff.mp hN) v hv
    rw [Finset.prod_eq_one fun v hv => by rw [hn v hv, pow_zero]]
    refine Finset.card_le_one.mpr fun x hx y hy => ?_
    by_contra hxy
    refine h2 x hx y hy hxy fun v hv => ?_
    rw [hn v hv]; simpa using h1 x hx y hy v hv
  | succ N ih =>
    intro n k T hN h1 h2
    obtain ⟨v₀, hv₀, hpos⟩ : ∃ v ∈ S, 0 < n v := by
      by_contra hcon
      push Not at hcon
      have : ∑ v ∈ S, n v = 0 := Finset.sum_eq_zero fun v hv => by have := hcon v hv; omega
      omega
    rcases T.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
    · simp
    set n' := Function.update n v₀ (n v₀ - 1) with hn'
    set k' := Function.update k v₀ (k v₀ - 1) with hk'
    have hsum : ∑ v ∈ S, n' v = N := by
      have e1 := Finset.add_sum_erase S n hv₀
      have e2 := Finset.add_sum_erase S n' hv₀
      have e3 : ∑ v ∈ S.erase v₀, n' v = ∑ v ∈ S.erase v₀, n v :=
        Finset.sum_congr rfl fun v hv => by
          rw [hn', Function.update_of_ne (Finset.ne_of_mem_erase hv)]
      have e4 : n' v₀ = n v₀ - 1 := by rw [hn', Function.update_self]
      omega
    obtain ⟨r, hr⟩ := exists_residue v₀
    obtain ⟨π, hπ⟩ := v₀.valuation_surjective F (WithZero.exp (-(k v₀)))
    have : Finite (𝓞 F ⧸ v₀.asIdeal) :=
      Nat.finite_of_card_ne_zero (by rw [natCard_quot]; exact (NumberField.HeightOneSpectrum.one_lt_absNorm v₀).ne_bot)
    let _ := Fintype.ofFinite (𝓞 F ⧸ v₀.asIdeal)
    set c : F → 𝓞 F ⧸ v₀.asIdeal := fun x => r (π * (x - x₀)) with hc
    have hint : ∀ x ∈ T, v₀.valuation F (π * (x - x₀)) ≤ 1 := by
      intro x hx
      rw [map_mul, hπ]
      calc WithZero.exp (-(k v₀)) * v₀.valuation F (x - x₀)
          ≤ WithZero.exp (-(k v₀)) * WithZero.exp (k v₀) :=
            mul_le_mul' le_rfl (h1 x hx x₀ hx₀ v₀ hv₀)
        _ = 1 := by rw [← WithZero.exp_add]; simp
    have hfib : ∀ a ∈ T.image c, (T.filter fun x => c x = a).card
        ≤ ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ n' v := by
      intro a _
      refine ih n' k' _ hsum ?_ ?_
      · intro x hx y hy v hv
        rw [Finset.mem_filter] at hx hy
        by_cases hvv : v = v₀
        · subst hvv
          rw [hk', Function.update_self]
          by_cases hxy : x = y
          · simp [hxy]
          have hlt := hr _ _ (hint x hx.1) (hint y hy.1) (hx.2.trans hy.2.symm)
          have e : π * (x - x₀) - π * (y - x₀) = π * (x - y) := by ring
          rw [e, map_mul, hπ, val_eq_exp_ordv v (sub_ne_zero.mpr hxy), ← WithZero.exp_add,
            ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
          rw [val_eq_exp_ordv v (sub_ne_zero.mpr hxy), WithZero.exp_le_exp]
          omega
        · rw [hk', Function.update_of_ne hvv]
          exact h1 x hx.1 y hy.1 v hv
      · intro x hx y hy hxy hall
        rw [Finset.mem_filter] at hx hy
        refine h2 x hx.1 y hy.1 hxy fun v hv => ?_
        have := hall v hv
        by_cases hvv : v = v₀
        · subst hvv
          rw [hk', hn', Function.update_self, Function.update_self] at this
          have e : k v - 1 - ((n v - 1 : ℕ) : ℤ) = k v - (n v : ℤ) := by omega
          rwa [e] at this
        · rwa [hk', hn', Function.update_of_ne hvv, Function.update_of_ne hvv] at this
    have hcard := Finset.card_le_mul_card_image (f := c) T _ hfib
    have himg : (T.image c).card ≤ Ideal.absNorm v₀.asIdeal := by
      rw [← natCard_quot, Nat.card_eq_fintype_card]
      exact Finset.card_le_univ _
    calc T.card ≤ (∏ v ∈ S, Ideal.absNorm v.asIdeal ^ n' v) * (T.image c).card := hcard
      _ ≤ (∏ v ∈ S, Ideal.absNorm v.asIdeal ^ n' v) * Ideal.absNorm v₀.asIdeal :=
          Nat.mul_le_mul_left _ himg
      _ = ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ n v := by
          rw [← Finset.mul_prod_erase S _ hv₀, ← Finset.mul_prod_erase S
            (fun v => Ideal.absNorm v.asIdeal ^ n v) hv₀]
          have e3 : ∏ v ∈ S.erase v₀, Ideal.absNorm v.asIdeal ^ n' v
              = ∏ v ∈ S.erase v₀, Ideal.absNorm v.asIdeal ^ n v :=
            Finset.prod_congr rfl fun v hv => by
              rw [hn', Function.update_of_ne (Finset.ne_of_mem_erase hv)]
          have e4 : n' v₀ = n v₀ - 1 := by rw [hn', Function.update_self]
          rw [e3, e4]
          have e5 : n v₀ = (n v₀ - 1) + 1 := by omega
          conv_rhs => rw [e5, pow_succ]
          ring

/-! ### Depth -/

theorem val_le_dep (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    v.valuation F x ≤ WithZero.exp ((dep v x : ℕ) : ℤ) := by
  by_cases hx : x = 0
  · simp [hx]
  rw [dep, if_neg hx, val_eq_exp_ordv v hx, WithZero.exp_le_exp]
  omega

open NumberField.HeightOneSpectrum in
theorem adicAbv_eq_zpow (v : HeightOneSpectrum (𝓞 F)) {x : F} (hx : x ≠ 0) :
    adicAbv F v x = (Ideal.absNorm v.asIdeal : ℝ) ^ (-ordv v x) := by
  have hq : (0 : ℝ) < Ideal.absNorm v.asIdeal := by exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).pos
  have h1 : adicAbv F v x ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-ordv v x) :=
    abv_le_of_val_le v (val_eq_exp_ordv v hx).le
  have h2 : adicAbv F v x⁻¹ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-(-ordv v x)) := by
    refine abv_le_of_val_le v ?_
    rw [map_inv₀, val_eq_exp_ordv v hx, ← WithZero.exp_neg]
  rw [map_inv₀, zpow_neg] at h2
  have hpos : 0 < adicAbv F v x := (adicAbv F v).pos hx
  refine le_antisymm h1 ?_
  have h3 := (inv_le_inv₀ hpos (zpow_pos hq _)).mp h2
  exact h3

open NumberField.HeightOneSpectrum in
theorem max_one_adicAbv (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    max 1 (adicAbv F v x) = (Ideal.absNorm v.asIdeal : ℝ) ^ dep v x := by
  have hq : (1 : ℝ) < Ideal.absNorm v.asIdeal := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  by_cases hx : x = 0
  · simp [hx, dep]
  rw [dep, if_neg hx, adicAbv_eq_zpow v hx]
  rcases le_or_gt 0 (ordv v x) with h | h
  · have e : (-ordv v x).toNat = 0 := by omega
    rw [e, pow_zero]
    exact max_eq_left (zpow_le_one_of_nonpos₀ hq.le (by omega))
  · have e : -ordv v x = ((-ordv v x).toNat : ℤ) := by omega
    rw [e, zpow_natCast]
    simp only [Int.toNat_natCast]
    exact max_eq_right (one_le_pow₀ hq.le)

theorem normS_one_eq (𝔪 : Ideal (𝓞 F)) (x : F) :
    normS 𝔪 1 x = ∏ v ∈ CubicPkg.sFin 𝔪, (Ideal.absNorm v.asIdeal : ℝ) ^ dep v x := by
  rw [normS]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_one, max_one_adicAbv]

theorem rpow_factor {a : ℝ} (ha : 0 < a) (κ m : ℕ) (σ : ℝ) :
    a ^ (κ + m) * (a ^ κ) ^ (-σ) = a ^ m * (a ^ (1 - σ)) ^ κ := by
  rw [← Real.rpow_natCast a (κ + m), ← Real.rpow_natCast a κ, ← Real.rpow_natCast a m,
    ← Real.rpow_natCast (a ^ (1 - σ)) κ, ← Real.rpow_mul ha.le, ← Real.rpow_mul ha.le,
    ← Real.rpow_add ha, ← Real.rpow_add ha]
  congr 1
  push_cast
  ring

/-- **Stub S-1 of WP-S, proved** (identical statement to `S.summable_normS_one`). -/
theorem summable_normS_one {𝔪 : Ideal (𝓞 F)} (hG : Good 𝔪) (M : ℤ) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun u : F ⧸ lat 𝔪 M => normS 𝔪 1 u.out ^ (-σ) := by
  classical
  set S := CubicPkg.sFin 𝔪 with hS
  set m : ℕ := M.natAbs with hm
  set q : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (Ideal.absNorm v.asIdeal : ℝ) with hq
  have hq1 : ∀ v, 1 < q v := fun v => by
    show (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ)
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq0 : ∀ v, 0 < q v := fun v => zero_lt_one.trans (hq1 v)
  set ρ : HeightOneSpectrum (𝓞 F) → ℝ := fun v => q v ^ (1 - σ) with hρ
  have hρ0 : ∀ v, 0 ≤ ρ v := fun v => Real.rpow_nonneg (hq0 v).le _
  have hρ1 : ∀ v, ρ v < 1 := fun v => Real.rpow_lt_one_of_one_lt_of_neg (hq1 v) (by linarith)
  refine summable_of_sum_le (c := (∏ v ∈ S.attach, q v.1 ^ m) * ∏ v ∈ S.attach, (1 - ρ v.1)⁻¹)
    (fun u => Real.rpow_nonneg (normS_nonneg _ _) _) fun T => ?_
  -- depth vector
  set d : (F ⧸ lat 𝔪 M) → ({v // v ∈ S} → ℕ) := fun u v => dep v.1 u.out with hd
  set Kmax : ℕ := T.sup fun u => S.sup fun v => dep v u.out with hK
  set P : Finset ({v // v ∈ S} → ℕ) := Fintype.piFinset fun _ => Finset.range (Kmax + 1) with hP
  have hmaps : ∀ u ∈ T, d u ∈ P := by
    intro u hu
    rw [hP, Fintype.mem_piFinset]
    intro v
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact (Finset.le_sup (f := fun v => dep v u.out) v.2).trans
      (Finset.le_sup (f := fun u : F ⧸ lat 𝔪 M => S.sup fun v => dep v u.out) hu)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfiber : ∀ κ ∈ P, ∑ u ∈ T with d u = κ, normS 𝔪 1 u.out ^ (-σ)
      ≤ (∏ v ∈ S.attach, q v.1 ^ m) * ∏ v ∈ S.attach, ρ v.1 ^ κ v := by
    intro κ _
    have hval : ∀ u ∈ T.filter (fun u => d u = κ), normS 𝔪 1 u.out ^ (-σ)
        = ∏ v ∈ S.attach, (q v.1 ^ κ v) ^ (-σ) := by
      intro u hu
      rw [Finset.mem_filter] at hu
      rw [normS_one_eq, ← hS, ← Finset.prod_attach S,
        ← Real.finsetProd_rpow _ _ (fun v _ => pow_nonneg (hq0 v.1).le _)]
      refine Finset.prod_congr rfl fun v _ => ?_
      have : dep v.1 u.out = κ v := congrFun hu.2 v
      rw [this]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
    -- count the fibre
    set k : HeightOneSpectrum (𝓞 F) → ℤ := fun v => if h : v ∈ S then (κ ⟨v, h⟩ : ℤ) else 0
      with hk
    set n : HeightOneSpectrum (𝓞 F) → ℕ := fun v => (if h : v ∈ S then κ ⟨v, h⟩ else 0) + m
      with hn
    have hcount : (T.filter fun u => d u = κ).card
        ≤ ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ n v := by
      rw [← Finset.card_image_of_injective _ (Quotient.out_injective)]
      refine card_le_of_separated S _ n k _ rfl ?_ ?_
      · intro x hx y hy v hv
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hy
        rw [Finset.mem_filter] at hu hu'
        have e1 : dep v u.out = κ ⟨v, hv⟩ := congrFun hu.2 ⟨v, hv⟩
        have e2 : dep v u'.out = κ ⟨v, hv⟩ := congrFun hu'.2 ⟨v, hv⟩
        have b1 := val_le_dep v u.out
        have b2 := val_le_dep v u'.out
        rw [e1] at b1; rw [e2] at b2
        rw [hk]; simp only [dif_pos hv]
        exact (Valuation.map_sub _ _ _).trans (max_le b1 b2)
      · intro x hx y hy hxy hall
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hy
        apply hxy
        have hmem : u.out - u'.out ∈ lat 𝔪 M := by
          intro v hv
          have hvS : v ∈ S := (CubicPkg.mem_sFin hG.ne_bot v).mpr hv
          refine (hall v hvS).trans ?_
          rw [WithZero.exp_le_exp, hk, hn]
          simp only [dif_pos hvS]
          push_cast
          omega
        have : (QuotientAddGroup.mk u.out : F ⧸ lat 𝔪 M) = QuotientAddGroup.mk u'.out := by
          rw [QuotientAddGroup.eq]
          have := (lat 𝔪 M).neg_mem hmem
          rwa [neg_sub, sub_eq_neg_add] at this
        rw [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at this
        rw [this]
    have hcountR : ((T.filter fun u => d u = κ).card : ℝ) ≤ ∏ v ∈ S.attach, q v.1 ^ (κ v + m) := by
      have : ((T.filter fun u => d u = κ).card : ℝ)
          ≤ ((∏ v ∈ S, Ideal.absNorm v.asIdeal ^ n v : ℕ) : ℝ) := by exact_mod_cast hcount
      refine this.trans (le_of_eq ?_)
      push_cast
      rw [← Finset.prod_attach S]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [hn, hq]; simp only [dif_pos v.2, Subtype.coe_eta]
    calc ((T.filter fun u => d u = κ).card : ℝ) * ∏ v ∈ S.attach, (q v.1 ^ κ v) ^ (-σ)
        ≤ (∏ v ∈ S.attach, q v.1 ^ (κ v + m)) * ∏ v ∈ S.attach, (q v.1 ^ κ v) ^ (-σ) :=
          mul_le_mul_of_nonneg_right hcountR
            (Finset.prod_nonneg fun v _ => Real.rpow_nonneg (pow_nonneg (hq0 v.1).le _) _)
      _ = (∏ v ∈ S.attach, q v.1 ^ m) * ∏ v ∈ S.attach, ρ v.1 ^ κ v := by
          rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl fun v _ => rpow_factor (hq0 v.1) _ _ _
  refine (Finset.sum_le_sum hfiber).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun v _ => pow_nonneg (hq0 v.1).le _)
  have hprod : ∑ κ ∈ P, ∏ v ∈ S.attach, ρ v.1 ^ κ v
      = ∏ v ∈ S.attach, ∑ j ∈ Finset.range (Kmax + 1), ρ v.1 ^ j := by
    rw [hP, ← Finset.univ_eq_attach]
    exact (Finset.prod_univ_sum (fun _ : {v // v ∈ S} => Finset.range (Kmax + 1))
      (fun v j => ρ v.1 ^ j)).symm
  rw [hprod]
  refine Finset.prod_le_prod (fun v _ => Finset.sum_nonneg fun j _ => pow_nonneg (hρ0 v.1) _)
    fun v _ => ?_
  rw [← tsum_geometric_of_lt_one (hρ0 v.1) (hρ1 v.1)]
  exact (summable_geometric_of_lt_one (hρ0 v.1) (hρ1 v.1)).sum_le_tsum _
    fun j _ => pow_nonneg (hρ0 v.1) _

end ArtinKP.RF
end
end

section
-- module Solutions.Artin.KP.B_FourCoeff
/-!
# WP-B, part 7: the Fourier coefficients of the Eisenstein series at the cusp `∞`

`fourier_coeff`: for a genuine section `Φ`, `Re s > 2`, `ν ∈ R`, a depth `M` valid for `(Φ, ν)`
and a fundamental cell `D` of `Λ_M = emb (R ∩ 𝔩_M)`:

`∫_D E(x, v) · conj e_∞(νx) dx = Φ_s(0,1) ht(v)^s ∫_D conj e_∞(νx) dx
    + vol(𝔩_M)⁻¹ · W_s(ν; v) · ∑_{c ∈ (R∖0)/Rˣ} g(ν, c) · λ(c; ν, s) · N(c)^{-s}`,

`λ(c; ν, s) = lam ψ_{S_f} M Φ c ν s = |c|_{S_f}^s J_Φ(c; ν, s)`, `N(c) = #(R/cR)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E ArtinKP.K

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (Φ : GSection ι P 𝔪)
  (s : ℂ) (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) (M : ℤ)

include hG in
theorem nrmR_pos {c : SInt 𝔪} (hc : c ≠ 0) : 0 < nrmR c :=
  Nat.cast_pos.mpr (natCard_quot_span_pos hG.ne_bot hc)

/-! ### The integral of one member of the family -/

/-! ### Summation -/

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.S2_Kubota
/-!
# WP-S2, part 8: the normalized finite Jacquet functional `Lam` and the laws of `E.Kubota`

`Lam ψ hG Φ c ν s := |c|_{S_f}^s · J_Φ(c; ν, s)`, the functional of WP-S (`S.lam`) taken at a
valid depth; by `jacD_eq_of_le` it does not depend on the valid depth (`Lam_eq_lamD`).

* `Lam_unit` (J1), `Lam_cube` (S1³), `Lam_act` (MATH2 Lemma 6.1 (iii), any frequency),
  `torusT_torusT_inv` and `Lam_act_surj`: the laws required by the interface `E.Kubota`.
* `kubota`: the instance `E.Kubota (cubicSymbol …) (B7.sAdd 𝔪 h𝔪) (GSection ι P 𝔪)` with
  `act β = Ã(β)`, **given** its field `summable` as a hypothesis.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S2

open ArtinKP.A ArtinKP.S

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

theorem Valid.mono {ψ : SfChar 𝔪} {Φ : GSection ι P 𝔪} {ν : F}
    {k k' : HeightOneSpectrum (𝓞 F) → ℤ} (h : Valid ψ Φ ν k)
    (hk : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal → k v ≤ k' v) : Valid ψ Φ ν k' :=
  ⟨fun b hb => h.1 b (SmallD.mono hk hb), fun x hx => h.2 x (SmallD.mono hk hx)⟩

theorem Lam_eq_lam (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) {ν : F} {M : ℤ}
    (h : Valid ψ Φ ν (fun _ => M)) (c : F) (s : ℂ) :
    Lam ψ hG Φ c ν s = lam ψ M Φ c ν s :=
  Lam_eq_lamD ψ hG Φ h c s

/-! ### The interface `E.Kubota` -/

end ArtinKP.S2
end
end

section
-- module Solutions.Artin.KP.S2_Bound
/-!
# WP-S2, part 9: the uniform bound for `Lam` (towards the field `summable` of `E.Kubota`)

Given stub S-1 of WP-S as a hypothesis (`hS1`, the exact statement of
`S_Stubs.summable_normS_one` without `hG`):

* `K_eq`: `K_σ(M) = vol(𝔩_M) Σ_{F/𝔩_M} ∏_v max(1,|u|_v)^{-σ}` does not depend on `M ≥ 0`
  (it is `∫_{F_{S_f}} ∏ max(1,|u|_v)^{-σ} du`);
* `norm_Lam_le`: `|Lam Φ c ν s| ≤ B · K_{Re s}(0)` for all `c ≠ 0` and **all** `ν`, with `B`
  uniform on `|s| ≤ M₀` — MATH2 §0.2's uniform bound `|c|^σ |J_Φ(c;ν,s)| ≤ B K_σ`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S2

open ArtinKP.A ArtinKP.S

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

open NumberField.HeightOneSpectrum in
/-- `u ↦ ∏_v max(1, |u|_v)` is `𝔩_0`-periodic. -/
theorem normS_one_add (h𝔪 : 𝔪 ≠ ⊥) (x : F) {h : F} (hh : Small 𝔪 0 h) :
    normS 𝔪 1 (x + h) = normS 𝔪 1 x := by
  refine Finset.prod_congr rfl fun v hv => ?_
  have hv' := (CubicPkg.mem_sFin h𝔪 v).mp hv
  have h1 : adicAbv F v h ≤ 1 := by
    have := abv_le_of_val_le v (x := h) (n := 0) (by simpa using hh v hv')
    simpa using this
  have hone : adicAbv F v (1 : F) = 1 := map_one _
  rw [hone]
  refine le_antisymm (max_le (le_max_left _ _) ?_) (max_le (le_max_left _ _) ?_)
  · exact (adicAbv_add_le_max F v x h).trans
      (max_le (le_max_right _ _) (h1.trans (le_max_left _ _)))
  · have e : x = (x + h) + -h := by ring
    have h2 : adicAbv F v (-h) ≤ 1 := by rwa [AbsoluteValue.map_neg]
    calc adicAbv F v x = adicAbv F v ((x + h) + -h) := by rw [← e]
      _ ≤ max (adicAbv F v (x + h)) (adicAbv F v (-h)) := adicAbv_add_le_max F v _ _
      _ ≤ _ := max_le (le_max_right _ _) (h2.trans (le_max_left _ _))

/-- `K_σ` does not depend on the depth `M ≥ 0`. -/
theorem K_eq (ψ : SfChar 𝔪) (h𝔪 : 𝔪 ≠ ⊥) {M : ℤ} (hM : 0 ≤ M) (σ : ℝ) :
    vol 𝔪 M * ∑' u : F ⧸ lat 𝔪 M, normS 𝔪 1 u.out ^ (-σ)
      = vol 𝔪 0 * ∑' u : F ⧸ lat 𝔪 0, normS 𝔪 1 u.out ^ (-σ) := by
  have h := jacD_eq_of_le ψ h𝔪 (k := fun _ => 0) (k' := fun _ => M) (fun _ _ => hM)
    (f := fun u => ((normS 𝔪 1 u ^ (-σ) : ℝ) : ℂ)) (ν := 0)
    (fun x h hh => by rw [normS_one_add h𝔪 x hh])
    (fun h _ => by rw [zero_mul]; exact ψ.map_zero)
  rw [jacD_const, jacD_const, jac, jac] at h
  simp only [zero_mul, ψ.map_zero, map_one, mul_one] at h
  rw [← Complex.ofReal_tsum, ← Complex.ofReal_tsum, ← Complex.ofReal_mul,
    ← Complex.ofReal_mul] at h
  exact Complex.ofReal_injective h

/-- **Uniform bound** for the normalized Jacquet functional, in `c` and in the frequency `ν`. -/
theorem norm_Lam_le (ψ : SfChar 𝔪) (hG : Good 𝔪)
    (hS1 : ∀ (M : ℤ) {σ : ℝ}, 1 < σ → Summable fun u : F ⧸ lat 𝔪 M => normS 𝔪 1 u.out ^ (-σ))
    (Φ : GSection ι P 𝔪) (M₀ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, ‖s‖ ≤ M₀ → 1 < s.re → ∀ c ν : F, c ≠ 0 →
      ‖Lam ψ hG Φ c ν s‖ ≤ B * (vol 𝔪 0 * ∑' u : F ⧸ lat 𝔪 0, normS 𝔪 1 u.out ^ (-s.re)) := by
  obtain ⟨B, hB0, hB⟩ := norm_lam_le ψ Φ M₀
  refine ⟨B, hB0, fun s hs hre c ν hc => ?_⟩
  have hv : Valid ψ Φ ν (fun _ => max (depth ψ hG Φ ν) 0) :=
    (valid_depth ψ hG Φ ν).mono fun _ _ => le_max_left _ _
  rw [Lam_eq_lam ψ hG Φ hv, ← K_eq ψ hG.ne_bot (le_max_right (depth ψ hG Φ ν) 0)]
  exact hB s hs _ c ν hc (hS1 _ hre)

end ArtinKP.S2
end
end

section
-- module Solutions.Artin.KP.B_Kub
/-!
# WP-B, part 9: the Kubota series — convergence, holomorphy, the `E.Kubota` instance

* `kTerm`, `aCoeff`: `𝔞_Φ(ν, s) = ∑_{c ∈ (R∖0)/Rˣ} g(ν, c) · Lam Φ c ν s · N(c)^{-s}`, for every
  `ν ∈ R` (`ν = 0` gives the Dirichlet series of the constant term), with
  `Lam = S2.LamR ψ_{S_f}` (WP-S2's normalized finite Jacquet functional at a valid depth).
* `exists_majorant_kTerm`: locally uniform absolute convergence on `Re s > 2`
  (`|g(ν,c)| ≤ N(c)`, `S2.norm_Lam_le`, S-1, `∑ N(c)^{1-σ} < ∞`).
* `differentiableOn_aCoeff`: holomorphy on `Re s > 2`.
* `kubota hG hz6 : E.Kubota (S2.cubicSymbol …) (B7.sAdd 𝔪 _) (GSection ι P 𝔪)` — no hypothesis left.
* `fourier_coeff_aSer`, `const_term_aCoeff`: the Fourier coefficients in this normalization.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E ArtinKP.K ArtinKP.B7

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

theorem norm_sym_inv_le (S : CubicSymbol (SInt 𝔪)) (d c : SInt 𝔪) (hc : c ≠ 0) :
    ‖(S.sym d c)⁻¹‖ ≤ 1 := by
  by_cases h : IsCoprime d c
  · have h3 := S.sym_pow_three d c hc h
    have hn : ‖S.sym d c‖ = 1 := by
      have := congrArg norm h3
      rw [norm_pow, norm_one] at this
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp this
    rw [norm_inv, hn, inv_one]
  · rw [(S.sym_eq_zero_iff d c hc).mpr h]
    simp

/-- `|g(ν, c)| ≤ N(c)`. -/
theorem norm_gauss_le (S : CubicSymbol (SInt 𝔪)) (h𝔪 : 𝔪 ≠ ⊥) (ν c : SInt 𝔪) (hc : c ≠ 0) :
    ‖gauss S (sAdd 𝔪 h𝔪) ν c‖ ≤ (Nat.card (SInt 𝔪 ⧸ Ideal.span {c}) : ℝ) := by
  have := finite_quot_span h𝔪 hc
  let _ := Fintype.ofFinite (SInt 𝔪 ⧸ Ideal.span {c})
  rw [gauss, rsum, finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ x ∈ (Finset.univ : Finset (SInt 𝔪 ⧸ Ideal.span {c})),
      ‖(S.sym (rep c x) c)⁻¹ * (sAdd 𝔪 h𝔪).ψ (ν * rep c x) c‖ ≤ 1 := by
    intro x _
    rw [norm_mul, sAdd_ψ, norm_sAddChar h𝔪, mul_one]
    exact norm_sym_inv_le S _ c hc
  have h2 := Finset.sum_le_card_nsmul _ _ 1 h1
  simpa using h2

theorem one_le_normS_one (x : F) : 1 ≤ normS 𝔪 1 x := by
  unfold normS
  refine Finset.prod_induction _ (fun y => 1 ≤ y)
    (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl fun v _ => ?_
  refine le_max_of_le_left ?_
  rw [map_one]

variable [IsTotallyComplex F] (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  (Φ : GSection ι P 𝔪) (ν : SInt 𝔪)

/-- Locally uniform absolute convergence on `Re s > 2`. -/
theorem exists_majorant_kTerm (M₀ : ℝ) {σ₁ : ℝ} (hσ₁ : 2 < σ₁) :
    ∃ u : Cls (SInt 𝔪) → ℝ, Summable u ∧ ∀ s : ℂ, ‖s‖ ≤ M₀ → σ₁ ≤ s.re →
      ∀ a : Cls (SInt 𝔪), ‖kTerm hG hz6 Φ ν a s‖ ≤ u a := by
  have hS1 : ∀ (M : ℤ) {σ : ℝ}, 1 < σ →
      Summable fun u : F ⧸ lat 𝔪 M => normS 𝔪 1 u.out ^ (-σ) :=
    fun M _ hσ => RF.summable_normS_one hG M hσ
  obtain ⟨B, hB0, hB⟩ := S2.norm_Lam_le (psiS hG.ne_bot) hG hS1 Φ M₀
  set K₁ : ℝ := vol 𝔪 0 * ∑' u : F ⧸ lat 𝔪 0, normS 𝔪 1 u.out ^ (-σ₁) with hK₁
  have hK₁0 : 0 ≤ K₁ := mul_nonneg (vol_nonneg 0)
    (tsum_nonneg fun _ => Real.rpow_nonneg (normS_nonneg _ _) _)
  refine ⟨fun a => B * K₁ * nrmR (rp a.1) ^ (-(σ₁ - 1)),
    (summable_nrm_rpow hG.ne_bot (t := σ₁ - 1) (by linarith)).mul_left (B * K₁),
    fun s hs hσ a => ?_⟩
  have hc := rp_ne_zero a.2
  have hcF : ((rp a.1 : SInt 𝔪) : F) ≠ 0 := fun h => hc (Subtype.ext h)
  have hp := nrmR_pos hG hc
  have hp1 : 1 ≤ nrmR (rp a.1) :=
    Nat.one_le_cast.mpr (natCard_quot_span_pos hG.ne_bot hc)
  have h1 : ‖gauss (S2.cubicSymbol ι P hG hz6) (sAdd 𝔪 hG.ne_bot) ν (rp a.1)‖
      ≤ nrmR (rp a.1) := norm_gauss_le _ hG.ne_bot ν _ hc
  have hK : vol 𝔪 0 * ∑' u : F ⧸ lat 𝔪 0, normS 𝔪 1 u.out ^ (-s.re) ≤ K₁ := by
    refine mul_le_mul_of_nonneg_left ?_ (vol_nonneg 0)
    exact (hS1 0 (by linarith : (1 : ℝ) < s.re)).tsum_le_tsum
      (fun u => Real.rpow_le_rpow_of_exponent_le (one_le_normS_one _) (neg_le_neg hσ))
      (hS1 0 (by linarith : (1 : ℝ) < σ₁))
  have h2 : ‖S2.LamR (psiS hG.ne_bot) hG Φ (rp a.1) ν s‖ ≤ B * K₁ :=
    (hB s hs (by linarith) _ _ hcF).trans (mul_le_mul_of_nonneg_left hK hB0)
  have h3 : ‖nrm (rp a.1) ^ (-s)‖ ≤ nrmR (rp a.1) ^ (-σ₁) := by
    have hn : nrm (rp a.1) = ((nrmR (rp a.1) : ℝ) : ℂ) := by
      rw [nrm, nrmR, Complex.ofReal_natCast]
    rw [hn, Complex.norm_cpow_eq_rpow_re_of_pos hp, Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hp1 (neg_le_neg hσ)
  have e : nrmR (rp a.1) ^ (-(σ₁ - 1)) = nrmR (rp a.1) * nrmR (rp a.1) ^ (-σ₁) := by
    rw [neg_sub, sub_eq_add_neg, Real.rpow_add hp, Real.rpow_one]
  change ‖kTerm hG hz6 Φ ν a s‖ ≤ B * K₁ * nrmR (rp a.1) ^ (-(σ₁ - 1))
  rw [kTerm, norm_mul, norm_mul, e]
  calc ‖gauss (S2.cubicSymbol ι P hG hz6) (sAdd 𝔪 hG.ne_bot) ν (rp a.1)‖
        * ‖S2.LamR (psiS hG.ne_bot) hG Φ (rp a.1) ν s‖ * ‖nrm (rp a.1) ^ (-s)‖
      ≤ nrmR (rp a.1) * (B * K₁) * nrmR (rp a.1) ^ (-σ₁) := by
        gcongr
    _ = B * K₁ * (nrmR (rp a.1) * nrmR (rp a.1) ^ (-σ₁)) := by ring

theorem summable_kTerm_of_two_lt_re_oai {s : ℂ} (hs : 2 < s.re) :
    Summable fun a : Cls (SInt 𝔪) => kTerm hG hz6 Φ ν a s := by
  obtain ⟨u, hu, hle⟩ := exists_majorant_kTerm hG hz6 Φ ν ‖s‖ hs
  exact Summable.of_norm_bounded hu fun a => hle s le_rfl le_rfl a

end ArtinKP.B
end
end

theorem solution.{u_1} : type_of% @ArtinKP.B.summable_kTerm_of_two_lt_re_oai.{u_1} := @ArtinKP.B.summable_kTerm_of_two_lt_re_oai.{u_1}
