-- Prove2me | solution 1 for ArtinKP.G2a.norm_tau_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:07:02.891997+00:00
-- url     : https://prove2.me/submissions/4a45ff97-b49a-4501-9e81-f256bfad3bd2

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
import Definitions.Def_ArtinKPB017
import Theorems.Thm_ArtinKP_G1_exists_Kir_classDecomp

section
-- module Solutions.Artin.KP.A_Interface
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-A interface (symbols on global elements, Kubota symbol on `SL₂(R)`)

Later packages should import this file only.  Everything is in namespace `ArtinKP.A`, for
`F : Type*` a number field, `𝔪 : Ideal (𝓞 F)`, `R = SInt 𝔪`.

## Standing data (obtained once from `exists_cutoff_setup`)
* `P : CubicPkg F` — cubic Hilbert symbols `P.hv v : Fˣ →* Fˣ →* rootsOfUnity 3 F` on global
  elements; orientation pinned by `CubicPkg.tame`.
* `hG : Good 𝔪` — `𝔪 ≠ ⊥`, primes over `6` divide `𝔪`, extended ideals of `R` are principal.
* `hz6 : IsPrimitiveRoot z6 6`, `z6 : 𝓞 F`.

## Exported statements
* local: `IsTameSymbol`, `kubota_local`, `CubicPkg.isTame`;
* (A1) `CubicPkg.tame`, `CubicPkg.tame_zpow`, `CubicPkg.tame_formula`, `iota3_hv_eq`;
* (A2) `CubicPkg.HS`, `CubicPkg.HS_apply`, `CubicPkg.HS_mul_prod`, `CubicPkg.HS_mul_prod'`,
  `CubicPkg.HS_mul_finprod`;
* (A3) `cubicExt`, `cubicExt_eq_residueSymbol`, `cubicExt_eq_prod`, `cubicExt_reciprocity`,
  `cubicExt_unit_left`, `cubicExt_of_unit_right`, `cubicExt_mul_left`, `cubicExt_mul_right`,
  `cubicExt_pow_three`, `cubicExt_congr`;
* (A4) `CubicPkg.HS_self`, `CubicPkg.HS_skew`, `CubicPkg.HS_skew'`, `CubicPkg.HS_neg_left/right`,
  `CubicPkg.HS_pow_three_left/right`, `CubicPkg.HS_unit`, `CubicPkg.HS_add_eq_one`,
  `CubicPkg.HS_add_eq`, `CubicPkg.IsDeepLevel`, `CubicPkg.exists_isDeepLevel`,
  `CubicPkg.HS_deep_left/right`, `HS_of_mem_SLevel_right/left`;
* (A5) `toF`, `kappa`, `sigmaS`, `kappa_mul`, `kappa_eq_prod`, `IsRad`, `sigmaS_eq_one`;
* (A6) `Gamma`, `mem_Gamma_iff`, `kappa_mul_of_mem_Gamma`, `exists_level_kappa_mul`, `kappaHom`;
* existence: `exists_cutoff_good`, `nonempty_cubicPkg_cyclotomic`, `exists_cutoff_setup`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.A

variable {F : Type*} [Field F] [NumberField F]

/-- Membership in the goal's level group `SLevel 𝔪 k` in terms of valuations:
`v(b - 1) ≤ exp (-(k+1))` at every `v ∣ 𝔪`. -/
theorem val_le_of_mem_SLevel {𝔪 : Ideal (𝓞 F)} {k : ℕ} {b : Fˣ} (hb : b ∈ SLevel 𝔪 k)
    (v : HeightOneSpectrum (𝓞 F)) (hv : 𝔪 ≤ v.asIdeal) :
    v.valuation F ((b : F) - 1) ≤ WithZero.exp (-((k + 1 : ℕ) : ℤ)) := by
  have h := hb v hv
  have hq := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  rw [NumberField.HeightOneSpectrum.adicAbv_def] at h
  have e : (Ideal.absNorm v.asIdeal : ℝ) ^ (-((k : ℤ) + 1))
      = ((WithZeroMulInt.toNNReal hq.ne_zero (WithZero.exp (-((k + 1 : ℕ) : ℤ)) :
          WithZero (Multiplicative ℤ)) : NNReal) : ℝ) := by
    rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, WithZero.toAdd_unzero_eq_log,
      WithZero.log_exp]
    push_cast
    rfl
  rw [e, NNReal.coe_le_coe] at h
  exact (WithZeroMulInt.toNNReal_strictMono hq).le_iff_le.mp h

end ArtinKP.A
end
end

section
-- module Solutions.Artin.T12.C3M_Base
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # C3M_Base: hypotheses from section A, finite quotients `R/𝔞R`, residue-symbol algebra

* `HypAdd 𝔪`: `e` is additive on `F` (needs the existence of `sAddChar` witnesses).
* `HypChi ι 𝔪`: at every exterior prime `P`, `χ_P` is multiplicative on `R` and `χ_P(x)⁶ = 1`
  for `x ∉ PR`.
-/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F]

variable {𝔪 : Ideal (𝓞 F)}

/-! ### Ideals -/

lemma exterior_of_mem_factors {𝔞 Q : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    (hQ : Q ∈ normalizedFactors 𝔞) : Q.IsPrime ∧ IsExterior 𝔪 Q := by
  have hpr : Prime Q := prime_of_normalized_factor Q hQ
  refine ⟨Ideal.isPrime_of_prime hpr, hpr.ne_zero, ?_⟩
  have hle : 𝔞 ≤ Q := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hQ)
  exact eq_top_iff.mpr (h𝔞.2 ▸ sup_le_sup_right hle 𝔪)

/-- `𝓞 → R/𝔞R` is onto for exterior `𝔞`. -/
lemma exists_sub_mem_map {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞) (r : SInt 𝔪) :
    ∃ a : 𝓞 F, r - algebraMap (𝓞 F) (SInt 𝔪) a ∈ 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  let O' : Submodule (𝓞 F) (SInt 𝔪) := LinearMap.range (Algebra.linearMap (𝓞 F) (SInt 𝔪))
  let J : Ideal (𝓞 F) := O'.colon {r}
  have hJ : J ⊔ 𝔞 = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal _ hne
    have h𝔞M : 𝔞 ≤ M := le_trans le_sup_right hJM
    have hM0 : M ≠ ⊥ := fun h => h𝔞.1 (eq_bot_iff.mpr (h ▸ h𝔞M))
    let v : HeightOneSpectrum (𝓞 F) := ⟨M, hM.isPrime, hM0⟩
    have hvS : v ∉ placesOf 𝔪 := by
      intro hv
      have : (⊤ : Ideal (𝓞 F)) ≤ M := h𝔞.2 ▸ sup_le h𝔞M hv
      exact hM.ne_top (eq_top_iff.mpr this)
    obtain ⟨n, ⟨d, hd⟩, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer (K := F) (r : F) (r.2 v hvS)
    have hdJ : d ∈ J := by
      rw [Submodule.mem_colon_singleton]
      refine ⟨n, ?_⟩
      apply Subtype.ext
      show ((algebraMap (𝓞 F) (SInt 𝔪) n : SInt 𝔪) : F) = ((d • r : SInt 𝔪) : F)
      rw [C3B.coe_algebraMap_SInt, Algebra.smul_def, Subalgebra.coe_mul, C3B.coe_algebraMap_SInt]
      have h2 : ((n : 𝓞 F) : F) = (d : F) * (r : F) := by rw [mul_comm]; exact hnd.symm
      exact h2
    exact hd (le_trans le_sup_left hJM hdJ)
  obtain ⟨j, hj, a, ha, hja⟩ := Submodule.mem_sup.mp (hJ ▸ Submodule.mem_top : (1 : 𝓞 F) ∈ J ⊔ 𝔞)
  rw [Submodule.mem_colon_singleton] at hj
  obtain ⟨b, hb⟩ := hj
  refine ⟨b, ?_⟩
  have hb' : algebraMap (𝓞 F) (SInt 𝔪) b = algebraMap (𝓞 F) (SInt 𝔪) j * r := by
    rw [← Algebra.smul_def]; exact hb
  have : r - algebraMap (𝓞 F) (SInt 𝔪) b = algebraMap (𝓞 F) (SInt 𝔪) a * r := by
    rw [hb']
    have h1 : (1 : SInt 𝔪) = algebraMap (𝓞 F) (SInt 𝔪) j + algebraMap (𝓞 F) (SInt 𝔪) a := by
      rw [← map_add, hja, map_one]
    linear_combination r * h1
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)

lemma finite_quot {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞) :
    Finite (SInt 𝔪 ⧸ 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  have : Finite (𝓞 F ⧸ 𝔞) := Ring.HasFiniteQuotients.finiteQuotient h𝔞.1
  let f := Ideal.quotientMap (𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) (algebraMap (𝓞 F) (SInt 𝔪))
    Ideal.le_comap_map
  refine Finite.of_surjective f ?_
  intro y
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, ha⟩ := exists_sub_mem_map h𝔞 r
  refine ⟨Ideal.Quotient.mk 𝔞 a, ?_⟩
  rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
  rw [← neg_mem_iff, neg_sub]; exact ha

/-! ### Residue symbols -/

/-! ### Generators -/

end C3M

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.KP.S_Jacquet
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

theorem out_spec {M : ℤ} (x : F) :
    ∃ h : F, Small 𝔪 M h ∧ (QuotientAddGroup.mk x : F ⧸ lat 𝔪 M).out = x + h := by
  obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add (lat 𝔪 M) x
  exact ⟨h.1, h.2, hh⟩

section jac

variable (ψ : SfChar 𝔪) {M : ℤ} {f : F → ℂ} {ν : F}

/-- The summand of `jac` on the class of `x`, for periodic data. -/
theorem jac_term (hf : ∀ x h : F, Small 𝔪 M h → f (x + h) = f x)
    (hψ : ∀ h : F, Small 𝔪 M h → ψ (ν * h) = 1) (x : F) :
    f (QuotientAddGroup.mk x : F ⧸ lat 𝔪 M).out
        * (starRingEnd ℂ) (ψ (ν * (QuotientAddGroup.mk x : F ⧸ lat 𝔪 M).out))
      = f x * (starRingEnd ℂ) (ψ (ν * x)) := by
  obtain ⟨h, hh, he⟩ := out_spec (𝔪 := 𝔪) (M := M) x
  rw [he, hf x h hh, mul_add, ψ.map_add, hψ h hh, mul_one]

/-- **Support**: the functional vanishes if `ψ(ν·)` is non-trivial on a period of `f`. -/
theorem jac_eq_zero (hf : ∀ x h : F, Small 𝔪 M h → f (x + h) = f x)
    (hψ : ∀ h : F, Small 𝔪 M h → ψ (ν * h) = 1) {b : F} (hfb : ∀ x : F, f (x + b) = f x)
    (hb : ψ (ν * b) ≠ 1) : jac ψ M f ν = 0 := by
  set g : F ⧸ lat 𝔪 M → ℂ := fun u => f u.out * (starRingEnd ℂ) (ψ (ν * u.out)) with hg
  have hshift : ∀ u : F ⧸ lat 𝔪 M,
      g (u + QuotientAddGroup.mk b) = (starRingEnd ℂ) (ψ (ν * b)) * g u := by
    intro u
    induction u using QuotientAddGroup.induction_on with
    | H x =>
      rw [← QuotientAddGroup.mk_add, hg]
      simp only
      rw [jac_term ψ hf hψ, jac_term ψ hf hψ, hfb, mul_add, ψ.map_add, map_mul]
      ring
  have h1 : ∑' u, g (u + QuotientAddGroup.mk b) = ∑' u, g u :=
    (Equiv.addRight (QuotientAddGroup.mk b : F ⧸ lat 𝔪 M)).tsum_eq g
  simp only [hshift] at h1
  rw [tsum_mul_left] at h1
  have hne : (starRingEnd ℂ) (ψ (ν * b)) ≠ 1 := by
    intro h
    apply hb
    have := congrArg (starRingEnd ℂ) h
    simpa using this
  have h0 : ∑' u, g u = 0 := by
    have h2 : ((starRingEnd ℂ) (ψ (ν * b)) - 1) * ∑' u, g u = 0 := by
      rw [sub_mul, h1, one_mul, sub_self]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)
  rw [jac, h0, mul_zero]

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

/-- (K2) **boundedness**, uniformly in `β` (and `η`). -/
theorem norm_kir_le (ψ : SfChar 𝔪) (Φ : GSection ι P 𝔪) (M₀ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, ‖s‖ ≤ M₀ → ∀ (M : ℤ) (η β : F), η ≠ 0 → β ≠ 0 →
      Summable (fun u : F ⧸ lat 𝔪 M => normS 𝔪 1 u.out ^ (-s.re)) →
      ‖kir ψ M Φ η β s‖ ≤ B * (vol 𝔪 M * ∑' u : F ⧸ lat 𝔪 M, normS 𝔪 1 u.out ^ (-s.re)) := by
  obtain ⟨B, hB0, hB⟩ := norm_lam_le ψ Φ M₀
  refine ⟨B, hB0, fun s hs M η β hη hβ hsum => ?_⟩
  rw [kir, norm_mul, norm_pow, norm_brk, one_pow, one_mul]
  exact hB s hs M _ β (mul_ne_zero (pow_ne_zero 2 hβ) hη) hsum

/-- (K3) **support**: `𝒦_Φ(β) = 0` unless `ψ(β ·)` is trivial on the lattice of periods of `Φ`. -/
theorem kir_eq_zero (ψ : SfChar 𝔪) (Φ : GSection ι P 𝔪) :
    ∃ N : ℕ, ∀ (M : ℤ), (N : ℤ) ≤ M → ∀ (η β : F) (s : ℂ),
      (∀ h : F, Small 𝔪 M h → ψ (β * h) = 1) → ∀ b : F, Small 𝔪 N b → ψ (β * b) ≠ 1 →
      kir ψ M Φ η β s = 0 := by
  obtain ⟨N, hN⟩ := Φ.exists_unip
  refine ⟨N, fun M hM η β s hψ b hb hne => ?_⟩
  have hper : ∀ x h : F, Small 𝔪 N h →
      Φ s (β ^ 2 * η) (β ^ 2 * η * (x + h)) = Φ s (β ^ 2 * η) (β ^ 2 * η * x) := by
    intro x h hh
    rw [mul_add]
    exact hN h hh s _ _
  rw [kir, lam, jac_eq_zero ψ (fun x h hh => hper x h (hh.mono hM)) hψ (fun x => hper x b hb) hne,
    mul_zero, mul_zero]

/-- An elementary inequality: bounded `x_v ≥ 0` satisfy
`∏ x_v^{1/3} ≤ C ∏ min(1, x_v^{1/3})`. -/
theorem prod_rpow_le_min {α : Type*} (T : Finset α) (x C : α → ℝ) (hx : ∀ i ∈ T, 0 ≤ x i)
    (hxC : ∀ i ∈ T, x i ≤ C i) :
    ∏ i ∈ T, x i ^ (1 / 3 : ℝ)
      ≤ (∏ i ∈ T, max 1 (C i) ^ (1 / 3 : ℝ)) * ∏ i ∈ T, min 1 (x i ^ (1 / 3 : ℝ)) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun i hi => Real.rpow_nonneg (hx i hi) _) fun i hi => ?_
  have h1 : (1 : ℝ) ≤ max 1 (C i) ^ (1 / 3 : ℝ) :=
    Real.one_le_rpow (le_max_left _ _) (by norm_num)
  by_cases h : x i ≤ 1
  · rw [min_eq_right (Real.rpow_le_one (hx i hi) h (by norm_num))]
    exact le_mul_of_one_le_left (Real.rpow_nonneg (hx i hi) _) h1
  · rw [min_eq_left (Real.one_le_rpow (le_of_not_ge h) (by norm_num)), mul_one]
    exact Real.rpow_le_rpow (hx i hi) ((hxC i hi).trans (le_max_right _ _)) (by norm_num)

open NumberField.HeightOneSpectrum in
/-- **The bound for the Kirillov function** `ξ = |β|^{1/3} 𝒦` (MATH2 §6.3), `η`-term by
`η`-term: for `β` in a fixed fractional ideal (`Small D β`),
`|β|^{1/3} |𝒦^η_Φ(β)| ≤ C ∏_{v ∈ S_f} min(1, |β|_v^{1/3})`.  Together with `kir_eq_zero`
(support in the dual lattice) this is the estimate needed for `bf`. -/
theorem xi_bound (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) (M₀ : ℝ) (D : ℤ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, ‖s‖ ≤ M₀ → ∀ (M : ℤ) (η β : F), η ≠ 0 → β ≠ 0 → Small 𝔪 D β →
      Summable (fun u : F ⧸ lat 𝔪 M => normS 𝔪 1 u.out ^ (-s.re)) →
      absS 𝔪 β ^ (1 / 3 : ℝ) * ‖kir ψ M Φ η β s‖
        ≤ B * (vol 𝔪 M * ∑' u : F ⧸ lat 𝔪 M, normS 𝔪 1 u.out ^ (-s.re))
          * ∏ v ∈ CubicPkg.sFin 𝔪, min 1 (adicAbv F v β ^ (1 / 3 : ℝ)) := by
  obtain ⟨B, hB0, hB⟩ := norm_kir_le ψ Φ M₀
  set C : ℝ := ∏ v ∈ CubicPkg.sFin 𝔪,
    max 1 ((Ideal.absNorm v.asIdeal : ℝ) ^ (-D)) ^ (1 / 3 : ℝ) with hC
  have hC0 : 0 ≤ C := Finset.prod_nonneg fun v _ =>
    Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
  refine ⟨C * B, mul_nonneg hC0 hB0, fun s hs M η β hη hβ hD hsum => ?_⟩
  have h1 := hB s hs M η β hη hβ hsum
  have h2 : absS 𝔪 β ^ (1 / 3 : ℝ)
      ≤ C * ∏ v ∈ CubicPkg.sFin 𝔪, min 1 (adicAbv F v β ^ (1 / 3 : ℝ)) := by
    rw [absS, ← Real.finsetProd_rpow _ _ (fun v _ => (adicAbv F v).nonneg β)]
    exact prod_rpow_le_min _ _ _ (fun v _ => (adicAbv F v).nonneg β) fun v hv =>
      abv_le_of_val_le v (hD v ((CubicPkg.mem_sFin hG.ne_bot v).mp hv))
  have hmin : 0 ≤ ∏ v ∈ CubicPkg.sFin 𝔪, min 1 (adicAbv F v β ^ (1 / 3 : ℝ)) :=
    Finset.prod_nonneg fun v _ => le_min zero_le_one (Real.rpow_nonneg ((adicAbv F v).nonneg β) _)
  calc absS 𝔪 β ^ (1 / 3 : ℝ) * ‖kir ψ M Φ η β s‖
      ≤ (C * ∏ v ∈ CubicPkg.sFin 𝔪, min 1 (adicAbv F v β ^ (1 / 3 : ℝ)))
          * (B * (vol 𝔪 M * ∑' u : F ⧸ lat 𝔪 M, normS 𝔪 1 u.out ^ (-s.re))) :=
        mul_le_mul h2 h1 (norm_nonneg _) (mul_nonneg hC0 hmin)
    _ = _ := by ring

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.B_FourArch
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.B.coe_latREquiv _root_.ArtinKP.B.embR_apply
/-!
# WP-B, part 2: the characters and the archimedean integral

* `eInf x = ∏_w archChar (-x_w)` on `ℂ^r`; `eInf (emb a) = exp(-2πi Tr a)` for `a ∈ F`.
* `psiS h𝔪 : SfChar 𝔪`, `ψ_{S_f}(x) = sAddChar 𝔪 x · conj (eInf (emb x))`; it is trivial on
  `𝔩_0`, and `eInf (emb x) = sAddChar 𝔪 x · conj ψ_{S_f}(x)` (`eInf_emb_eq`).
* `kerA v x = ∏_w v_w / (|x_w|² + v_w²)`; `I_{(c,d)}(x, v) = N_∞(c)⁻¹ · kerA v (x + d/c)`.
* `Winf s ν v = ∏_w jacquet s (-σ_w ν) v_w`; the integral of a shifted kernel against
  `conj eInf(ν x)` (`integral_shift_kernel`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.K

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### The archimedean character -/

/-! ### The `S_f`-character -/

theorem psiS_apply [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) (x : F) :
    psiS h𝔪 x = sAddChar 𝔪 x * conj (eInf (emb x)) := rfl

/-- `ψ_{S_f}` is trivial on `𝔩_0`. -/
theorem psiS_small [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) {x : F} (hx : Small 𝔪 0 x) :
    psiS h𝔪 x = 1 := by
  have h2 : ∀ v ∈ placesOf 𝔪, v.valuation F x ≤ 1 := fun v hv => by
    have := hx v hv
    simpa using this
  rw [psiS_apply, C3I.sAddChar_eq_of_wit (y := x) (by simp) h2, ← eInf_emb, eInf_mul_conj]

/-! ### The archimedean kernel -/

/-! ### Shifted kernels -/

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.G1_Bf
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-G1, part 9: two elementary summability lemmas for the majorant `bf` (MATH3 §4.5)

The two analytic ingredients of stub G1-1 (`G1_Stubs.exists_bf`); Mathlib only.

* `summable_pi_prod`: a finite product of non-negative summable families is summable over the
  product index set.
* `summable_local_weight`: for `q > 1`, `σ > -1/3`, the local weight
  `n ↦ 1[D ≤ n] · min(1, (q^{-n})^{1/3}) · (q^{-n})^σ` is summable over `n ∈ ℤ`.
-/

set_option autoImplicit false

namespace ArtinKP.G1

theorem summable_pi_prod {ι : Type*} [Fintype ι] {α : Type*} (f : ι → α → ℝ)
    (hf0 : ∀ i a, 0 ≤ f i a) (hf : ∀ i, Summable (f i)) :
    Summable fun n : ι → α => ∏ i, f i (n i) := by
  classical
  refine summable_of_sum_le (c := ∏ i, ∑' a, f i a)
    (fun n => Finset.prod_nonneg fun i _ => hf0 i _) fun u => ?_
  calc ∑ n ∈ u, ∏ i, f i (n i)
      ≤ ∑ n ∈ Fintype.piFinset (fun i => u.image (fun n => n i)), ∏ i, f i (n i) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun n hn => Fintype.mem_piFinset.mpr fun i => Finset.mem_image_of_mem _ hn)
          (fun n _ _ => Finset.prod_nonneg fun i _ => hf0 i _)
    _ = ∏ i, ∑ a ∈ u.image (fun n => n i), f i a := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ i, ∑' a, f i a :=
        Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun a _ => hf0 i a)
          (fun i _ => (hf i).sum_le_tsum _ (fun a _ => hf0 i a))

theorem localWeight_nonneg {q : ℝ} (hq : 0 < q) (D : ℤ) (σ : ℝ) (n : ℤ) :
    0 ≤ localWeight q D σ n := by
  unfold localWeight
  split_ifs
  · exact mul_nonneg (le_min zero_le_one (Real.rpow_nonneg (zpow_pos hq _).le _))
      (Real.rpow_nonneg (zpow_pos hq _).le _)
  · exact le_rfl

theorem summable_local_weight {q : ℝ} (hq : 1 < q) (D : ℤ) {σ : ℝ} (hσ : -(1 / 3 : ℝ) < σ) :
    Summable (localWeight q D σ) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  set r : ℝ := q ^ (-(1 / 3 + σ)) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hq0 _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  -- comparison with the geometric series `r^n`, `n ≥ D`
  have hbound : ∀ n : ℤ, localWeight q D σ n ≤ if D ≤ n then r ^ n else 0 := by
    intro n
    unfold localWeight
    split_ifs with h
    · have ha : 0 < q ^ (-n) := zpow_pos hq0 _
      have e : r ^ n = (q ^ (-n)) ^ (1 / 3 : ℝ) * (q ^ (-n)) ^ σ := by
        rw [← Real.rpow_add ha, hr, ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul hq0.le,
          ← Real.rpow_mul hq0.le]
        congr 1
        push_cast
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg ha.le _)
    · exact le_rfl
  refine Summable.of_nonneg_of_le (localWeight_nonneg hq0 D σ) hbound ?_
  have hinj : Function.Injective fun m : ℕ => D + (m : ℤ) := fun a b h => by
    simpa using h
  refine (hinj.summable_iff ?_).mp ?_
  · intro n hn
    rw [if_neg]
    intro hDn
    exact hn ⟨(n - D).toNat, by simp [Int.toNat_of_nonneg (sub_nonneg.mpr hDn)]⟩
  · have : (fun m : ℕ => (fun n : ℤ => if D ≤ n then r ^ n else 0) (D + (m : ℤ)))
        = fun m : ℕ => r ^ D * r ^ m := by
      funext m
      simp only [le_add_iff_nonneg_right, Int.natCast_nonneg, if_true]
      rw [zpow_add₀ hr0.ne', zpow_natCast]
    show Summable ((fun n : ℤ => if D ≤ n then r ^ n else 0) ∘ fun m : ℕ => D + (m : ℤ))
    rw [Function.comp_def, this]
    exact (summable_geometric_of_lt_one hr0.le hr1).mul_left _

end ArtinKP.G1
end

section
-- module Solutions.Artin.KP.S2_Kubota
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-- **`𝒦`-term as a Jacquet functional at frequency `1`** (MATH2 §6.3), at any valid depth:
`kir ψ M Φ η β s = Lam (Ã(β)Φ) η 1 s` for `M` valid for `Φ` and the frequency `β`. -/
theorem kir_eq_Lam (ψ : SfChar 𝔪) (hG : Good 𝔪) (M : ℤ) (Φ : GSection ι P 𝔪) {η β : F}
    (hη : η ≠ 0) (hβ : β ≠ 0) (s : ℂ) (hv : Valid ψ Φ β (fun _ => M)) :
    kir ψ M Φ η β s = Lam ψ hG (Φ.torusT hG β hβ) η 1 s := by
  rw [Lam_act ψ hG Φ hβ hη 1 s, mul_one, Lam_eq_lam ψ hG Φ hv]
  rfl

/-! ### The interface `E.Kubota` -/

end ArtinKP.S2
end
end

section
-- module Solutions.Artin.KP.RF_SNorm
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
-- module Solutions.Artin.KP.S2_Bound
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

end ArtinKP.S2
end
end

section
-- module Solutions.Artin.KP.GL_SNorm
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-GL, part 2: stub S-1 plugged into the bounds of WP-S and WP-S2

`RF.summable_normS_one` (S-1, proved by WP-RF) discharges the summability hypothesis of
`S.norm_lam_le`, `S.norm_kir_le`, `S.xi_bound`, `S.lam_differentiableOn` and `S2.norm_Lam_le`;
the versions here are unconditional for `Re s > 1`.
-/

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.GL

open ArtinKP.A ArtinKP.S

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

/-- S-1 in the shape of the hypothesis `hS1` of WP-S2. -/
theorem hS1 (hG : Good 𝔪) : ∀ (M : ℤ) {σ : ℝ}, 1 < σ →
    Summable fun u : F ⧸ lat 𝔪 M => normS 𝔪 1 u.out ^ (-σ) :=
  fun M _ hσ => RF.summable_normS_one hG M hσ

open NumberField.HeightOneSpectrum in
/-- `S.xi_bound` with S-1 plugged in. -/
theorem xi_bound (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) (M₀ : ℝ) (D : ℤ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, ‖s‖ ≤ M₀ → 1 < s.re → ∀ (M : ℤ) (η β : F), η ≠ 0 → β ≠ 0 →
      Small 𝔪 D β →
      absS 𝔪 β ^ (1 / 3 : ℝ) * ‖kir ψ M Φ η β s‖
        ≤ B * (vol 𝔪 M * ∑' u : F ⧸ lat 𝔪 M, normS 𝔪 1 u.out ^ (-s.re))
          * ∏ v ∈ CubicPkg.sFin 𝔪, min 1 (adicAbv F v β ^ (1 / 3 : ℝ)) := by
  obtain ⟨B, hB0, hB⟩ := S.xi_bound ψ hG Φ M₀ D
  exact ⟨B, hB0, fun s hs hre M η β hη hβ hD => hB s hs M η β hη hβ hD (hS1 hG M hre)⟩

end ArtinKP.GL
end
end

section
-- module Solutions.Artin.KP.G1_Lam
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-G1, part 2: linearity of `Lam`, and the cusp change for `Lam` and for the Kirillov term

* `Lam_smulFun`, `Lam_smul`, `Lam_scal`, `Lam_nT` (all `s`); `Lam_add`, `Lam_sum`, `Lam_addProj`
  (`Re s > 1`, where the defining series converges: `summable_jacTerm`).
* `torusT_torusT`, `torusT_smulFun`, `torusT_smul`.
* `Kt ψ hG Φ β η s := Lam (Ã(β)Φ) η 1 s`, the `η`-term of the Kirillov function (`= S.kir` at a
  valid depth, `Kt_eq_kir`), with the rules (K4):
  `Kt_torusT`, `Kt_nT`, `Kt_smulFun`, `Kt_add`, `Kt_addProj`.
* `Lam_cusp`: `Lam Ψ c' μ s = κ(γ)|c|^{s-2} ψ(μa/c) ⟨c',c⟩⁻¹ Lam (wΦ) (c'/c) (μ/c²) s`,
  `Ψ = translate γ (n(-d/c)Φ)`;
  `cusp_torusT`: `Ã(μ)Ψ = κ(γ)⟨μ,c⟩ |c|^{s-2} n(μa/c) Ã(μ/c²)(wΦ)`;
  `Kt_cusp`, and `xiT_cusp` (MATH3 (2.2)): with `ξ^η_Φ(β) := |β|^{1/3} Kt Φ β η (4/3)`,
  `ξ^η_Ψ(μ) = κ(γ) ψ(μa/c) ⟨μ,c⟩ ξ^η_{wΦ}(μ/c²)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.G1

open ArtinKP.A ArtinKP.S ArtinKP.S2

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

/-! ### Convergence of the defining series, linearity -/

/-! ### `Ã(β)` against the other operations -/

/-! ### The Kirillov term -/

theorem Kt_of_ne (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) {β : F} (hβ : β ≠ 0)
    (η : F) (s : ℂ) : Kt ψ hG Φ β η s = Lam ψ hG (Φ.torusT hG β hβ) η 1 s := by
  rw [Kt, dif_neg hβ]

/-- `Kt` is `S.kir` at any valid depth. -/
theorem Kt_eq_kir (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) {M : ℤ} {η β : F}
    (hη : η ≠ 0) (hβ : β ≠ 0) (s : ℂ) (hv : Valid ψ Φ β (fun _ => M)) :
    Kt ψ hG Φ β η s = kir ψ M Φ η β s := by
  rw [Kt_of_ne ψ hG Φ hβ, kir_eq_Lam ψ hG M Φ hη hβ s hv]

/-! ### The cusp change for `Lam` and for the Kirillov term -/

/-! ### The normalized term `ξ^η = |β|^{1/3} Kt(·, 4/3)` -/

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.G1_DS
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-G1, part 3: Lemma DS (diagonal smoothness) and the class decomposition of `Lam`

* `exists_split`: for `ρ ∈ F^×` an `e ∈ F`, `S_f`-integral, with `e/ρ` and `ρ(1-e)` `S_f`-integral
  (Chinese remainder theorem at the places of `S_f`).
* `GSection.exists_diag` — **Lemma DS** (MATH3 §4.3): for every genuine section `Φ` there is `N`
  with `Φ_s(ac, bd) = Φ_s(c, d)` whenever `a, b ∈ 1 + 𝔩_N`.
  Consequences: `exists_torusT_deep` ((K1) for all sections: `Ã(u)Φ = Φ` for deep `u`).
* `LamDeep ψ hG Ψ N`: `Lam Ψ (uη) = Lam Ψ η` for `u ∈ 1 + 𝔩_N`; `exists_lamDeep` (every section,
  all large `N`), `exists_lamDeep_torusT` (one level for all `Ã(β)Φ`, `β ∈ F^×`).
* `Lam_class`: `Lam Ψ c ν s = ⟨η, c⟩ Lam Ψ η ν s` for `c` in the class of `η`
  (`InClass 𝔪 N η c`, `N` deep, `Ψ` `LamDeep` at `N`).
* `Lam_bigCell`: `Lam` of a big-cell section at any `c`.
* `Lam_classDecomp` — **(CD)** at the level of `Lam`: for a complete system `T` of pairwise
  disjoint classes (`RO.exists_classReps`),
  `Lam Φ c ν s = Σ_{η ∈ T} Lam Φ η ν s · vol(𝔩_M)⁻¹ · Lam (bigCell_{η,M,0}) c ν s`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.G1

open ArtinKP.A ArtinKP.S ArtinKP.S2

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

/-! ### An `S_f`-adic partition of unity -/

theorem val_le_of_mem_pow (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) {y : 𝓞 F}
    (hy : y ∈ v.asIdeal ^ n) : v.valuation F (algebraMap (𝓞 F) F y) ≤ WithZero.exp (-(n : ℤ)) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (v.intValuation_le_pow_iff_mem y n).mpr hy

/-! ### Lemma DS -/

/-! ### `Lam` on a class -/

/-! ### Big cells -/

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.G1_Dual
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.B.coe_latREquiv _root_.ArtinKP.B.embR_apply
/-!
# WP-G1, part 4: Lemma DUAL — the dual lattice of `ψ_{S_f} = B.psiS` is bounded

* `exists_trace_clear`: the trace dual `𝓞^∨` is a fractional ideal (Mathlib's
  `FractionalIdeal.dual ℤ ℚ 1`): one `a ≠ 0` with `a z ∈ 𝓞` whenever `Tr(z 𝓞) ⊂ ℤ`.
* `exists_pole`: for a prime `v₀` and `d`, an element of `F` with a pole of order exactly `d` at
  `v₀` and integral at all other finite places.
* `exists_idem`: an integer `≡ 1` at `v₀` and `≡ 0` at the other places of `S_f`, modulo `n`-th
  powers.
* `psiS_dual` — **Lemma DUAL** (MATH3 §4.4): there is `d₀` such that for all `M`, `β`:
  `ψ(β 𝔩_M) = 1 → β ∈ 𝔩_{-M-d₀}`.
  `Adual ψ M β` is the predicate "`ψ(β·)` is trivial on `𝔩_M`" (the dual lattice `A_M`);
  `HasDual ψ d₀` is the conclusion of DUAL for an arbitrary `SfChar`, the form in which the other
  files use it.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped ComplexConjugate nonZeroDivisors
open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.G1

open ArtinKP.A ArtinKP.S ArtinKP.S2

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### The trace dual is a fractional ideal -/

theorem exists_trace_clear (F : Type*) [Field F] [NumberField F] :
    ∃ a : 𝓞 F, a ≠ 0 ∧ ∀ z : F,
      (∀ w : 𝓞 F, ∃ n : ℤ, Algebra.trace ℚ F (z * algebraMap (𝓞 F) F w) = (n : ℚ)) →
      ∃ b : 𝓞 F, algebraMap (𝓞 F) F a * z = algebraMap (𝓞 F) F b := by
  obtain ⟨a, ha, h⟩ := (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)).isFractional
  refine ⟨a, nonZeroDivisors.ne_zero ha, fun z hz => ?_⟩
  have hmem : z ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [FractionalIdeal.mem_dual (one_ne_zero' (FractionalIdeal (𝓞 F)⁰ F))]
    intro x hx
    obtain ⟨w, rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 F)⁰).mp hx
    obtain ⟨n, hn⟩ := hz w
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply, hn]
    simp
  obtain ⟨b, hb⟩ := h z hmem
  exact ⟨b, by rw [hb, Algebra.smul_def]⟩

/-! ### Elements with prescribed local behaviour -/

/-- An element with a pole of order exactly `d` at `v₀`, integral at every other finite place. -/
theorem exists_pole (v₀ : HeightOneSpectrum (𝓞 F)) (d : ℕ) :
    ∃ z : F, v₀.valuation F z = WithZero.exp (d : ℤ) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v ≠ v₀ → v.valuation F z ≤ 1 := by
  classical
  obtain ⟨π, hπ⟩ := v₀.intValuation_exists_uniformizer
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  set a : 𝓞 F := π ^ d with ha
  have ha0 : a ≠ 0 := pow_ne_zero d hπ0
  have haF : algebraMap (𝓞 F) F a ≠ 0 := by
    rwa [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
  have hva : v₀.valuation F (algebraMap (𝓞 F) F a) = WithZero.exp (-(d : ℤ)) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, ha, map_pow, hπ, ← WithZero.exp_nsmul]
    simp
  have hfin : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ Ideal.span {a}}.Finite :=
    Ideal.finite_factors (by simpa using ha0)
  set T : Finset (HeightOneSpectrum (𝓞 F)) := insert v₀ hfin.toFinset with hT
  set e : ℕ := 1 + T.sup (fun w => (ordv w (algebraMap (𝓞 F) F a)).natAbs) with he
  obtain ⟨c, hc⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (s := T) (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) (fun _ => e)
    (fun v _ => v.prime) (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h))
    (fun v => if v.1 = v₀ then (1 : 𝓞 F) else 0)
  have hv₀T : v₀ ∈ T := Finset.mem_insert_self _ _
  have he1 : (1 : ℤ) ≤ e := by rw [he]; push_cast; omega
  have hc0 : v₀.valuation F (algebraMap (𝓞 F) F c) = 1 := by
    have h1 := hc v₀ hv₀T
    simp only [if_true] at h1
    have h2 := val_le_of_mem_pow v₀ e h1
    rw [map_sub, map_one] at h2
    have h3 : v₀.valuation F (algebraMap (𝓞 F) F c - 1) < 1 := by
      refine h2.trans_lt ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    have := Valuation.map_one_add_of_lt (v := v₀.valuation F) h3
    rwa [add_sub_cancel] at this
  refine ⟨algebraMap (𝓞 F) F c / algebraMap (𝓞 F) F a, ?_, fun v hv => ?_⟩
  · rw [map_div₀, hc0, hva, one_div, ← WithZero.exp_neg, neg_neg]
  · rw [map_div₀]
    by_cases hmem : v ∈ hfin.toFinset
    · have hvT : v ∈ T := Finset.mem_insert_of_mem hmem
      have h1 := hc v hvT
      simp only [hv, if_false, sub_zero] at h1
      have h2 := val_le_of_mem_pow v e h1
      have hle : (ordv v (algebraMap (𝓞 F) F a)).natAbs ≤ T.sup
          (fun w => (ordv w (algebraMap (𝓞 F) F a)).natAbs) :=
        Finset.le_sup (f := fun w => (ordv w (algebraMap (𝓞 F) F a)).natAbs) hvT
      rw [val_eq_exp_ordv v haF, div_eq_mul_inv, ← WithZero.exp_neg]
      refine (mul_le_mul' h2 le_rfl).trans ?_
      rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp, he]
      push_cast
      omega
    · have hnd : ¬ v.asIdeal ∣ Ideal.span {a} := fun h => hmem (hfin.mem_toFinset.mpr h)
      have h1 : v.valuation F (algebraMap (𝓞 F) F a) = 1 := by
        rw [HeightOneSpectrum.valuation_of_algebraMap]
        refine le_antisymm (v.intValuation_le_one a) (not_lt.mp fun hlt => hnd ?_)
        exact (v.intValuation_lt_one_iff_dvd a).mp hlt
      rw [h1, div_one]
      exact HeightOneSpectrum.valuation_le_one (K := F) v c

/-- An integer `≡ 1` at `v₀` and `≡ 0` at the other places of `S_f`, to the precision `n`. -/
theorem exists_idem (h𝔪 : 𝔪 ≠ ⊥) (v₀ : HeightOneSpectrum (𝓞 F)) (hv₀ : 𝔪 ≤ v₀.asIdeal) (n : ℕ) :
    ∃ e : 𝓞 F, v₀.valuation F (algebraMap (𝓞 F) F e - 1) ≤ WithZero.exp (-(n : ℤ)) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal → v ≠ v₀ →
        v.valuation F (algebraMap (𝓞 F) F e) ≤ WithZero.exp (-(n : ℤ)) := by
  classical
  obtain ⟨e, he⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (s := CubicPkg.sFin 𝔪) (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) (fun _ => n)
    (fun v _ => v.prime) (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h))
    (fun v => if v.1 = v₀ then (1 : 𝓞 F) else 0)
  refine ⟨e, ?_, fun v hv hne => ?_⟩
  · have h1 := he v₀ ((CubicPkg.mem_sFin h𝔪 v₀).mpr hv₀)
    simp only [if_true] at h1
    have h2 := val_le_of_mem_pow v₀ n h1
    rwa [map_sub, map_one] at h2
  · have h1 := he v ((CubicPkg.mem_sFin h𝔪 v).mpr hv)
    simp only [hne, if_false, sub_zero] at h1
    exact val_le_of_mem_pow v n h1

/-! ### Lemma DUAL -/

/-- `ψ_{S_f}` on an `S`-integer `x`: `ψ(x) = 1` forces `Tr x ∈ ℤ`. -/
theorem trace_int_of_psiS_eq_one [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) {x : F}
    (hx : x ∈ (placesOf 𝔪).integer F) (h : B.psiS h𝔪 x = 1) :
    ∃ n : ℤ, Algebra.trace ℚ F x = (n : ℚ) := by
  rw [B.psiS_apply, C3B.sAddChar_of_mem x hx, one_mul, B.eInf_emb] at h
  have h' := congrArg conj h
  rw [Complex.conj_conj, map_one, Complex.exp_eq_one_iff] at h'
  obtain ⟨n, hn⟩ := h'
  refine ⟨-n, ?_⟩
  have h2 : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ((-n : ℤ) : ℂ) := by
    have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    apply mul_left_cancel₀ hpi
    push_cast
    linear_combination -hn
  exact_mod_cast h2

/-- **Lemma DUAL** (MATH3 §4.4): the dual lattices of `ψ_{S_f}` are bounded, uniformly:
`ψ(β 𝔩_M) = 1 → β ∈ 𝔩_{-M-d₀}`. -/
theorem psiS_dual [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) : ∃ d₀ : ℤ, HasDual (B.psiS h𝔪) d₀ := by
  classical
  obtain ⟨a, ha0, ha⟩ := exists_trace_clear F
  have haF : algebraMap (𝓞 F) F a ≠ 0 := by
    rwa [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
  set d₀ : ℕ := 1 + (CubicPkg.sFin 𝔪).sup (fun v => (ordv v (algebraMap (𝓞 F) F a)).natAbs)
    with hd₀
  refine ⟨d₀, fun M β hβ v₀ hv₀ => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [map_zero] at hlt
    exact not_lt_zero hlt
  rw [val_eq_exp_ordv v₀ hβ0, WithZero.exp_lt_exp] at hlt
  have hv₀s := (CubicPkg.mem_sFin h𝔪 v₀).mpr hv₀
  have hle₀ : (ordv v₀ (algebraMap (𝓞 F) F a)).natAbs
      ≤ (CubicPkg.sFin 𝔪).sup (fun v => (ordv v (algebraMap (𝓞 F) F a)).natAbs) :=
    Finset.le_sup (f := fun v => (ordv v (algebraMap (𝓞 F) F a)).natAbs) hv₀s
  obtain ⟨z, hz₀, hz⟩ := exists_pole v₀ d₀
  -- some integer multiple of `z` has non-integral trace
  have hw : ∃ w : 𝓞 F, ∀ n : ℤ, Algebra.trace ℚ F (z * algebraMap (𝓞 F) F w) ≠ (n : ℚ) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨b, hb⟩ := ha z hcon
    have h1 : v₀.valuation F (algebraMap (𝓞 F) F a * z) ≤ 1 := by
      rw [hb]
      exact HeightOneSpectrum.valuation_le_one (K := F) v₀ b
    rw [map_mul, hz₀, val_eq_exp_ordv v₀ haF, ← WithZero.exp_add, ← WithZero.exp_zero,
      WithZero.exp_le_exp, hd₀] at h1
    push_cast at h1
    omega
  obtain ⟨w, hw⟩ := hw
  set n : ℕ := max d₀ ((CubicPkg.sFin 𝔪).sup fun v => (M + ordv v β).toNat) with hn
  obtain ⟨e, he₀, he⟩ := exists_idem h𝔪 v₀ hv₀ n
  set zw : F := z * algebraMap (𝓞 F) F w with hzw
  have hwv : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (algebraMap (𝓞 F) F w) ≤ 1 :=
    fun v => HeightOneSpectrum.valuation_le_one (K := F) v w
  have hev : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (algebraMap (𝓞 F) F e) ≤ 1 :=
    fun v => HeightOneSpectrum.valuation_le_one (K := F) v e
  have hzw₀ : v₀.valuation F zw ≤ WithZero.exp (d₀ : ℤ) := by
    rw [hzw, map_mul, hz₀]
    exact mul_le_of_le_one_right' (hwv v₀)
  have hzwv : ∀ v : HeightOneSpectrum (𝓞 F), v ≠ v₀ → v.valuation F zw ≤ 1 := fun v hv => by
    rw [hzw, map_mul]
    exact mul_le_one' (hz v hv) (hwv v)
  -- `h := zw · e / β ∈ 𝔩_M`
  have hsmall : Small 𝔪 M (zw * algebraMap (𝓞 F) F e / β) := by
    intro v hv
    rw [map_div₀, map_mul, val_eq_exp_ordv v hβ0, div_eq_mul_inv, ← WithZero.exp_neg, neg_neg]
    by_cases hvv : v = v₀
    · subst hvv
      refine (mul_le_mul' (mul_le_mul' hzw₀ (hev v)) le_rfl).trans ?_
      rw [mul_one, ← WithZero.exp_add, WithZero.exp_le_exp]
      omega
    · have hvs := (CubicPkg.mem_sFin h𝔪 v).mpr hv
      have hle : (M + ordv v β).toNat ≤ (CubicPkg.sFin 𝔪).sup fun v => (M + ordv v β).toNat :=
        Finset.le_sup (f := fun v => (M + ordv v β).toNat) hvs
      have hnle : (M + ordv v β) ≤ n := by
        have h1 : (M + ordv v β) ≤ ((M + ordv v β).toNat : ℤ) := Int.self_le_toNat _
        have h2 : ((CubicPkg.sFin 𝔪).sup fun v => (M + ordv v β).toNat) ≤ n := le_max_right _ _
        omega
      refine (mul_le_mul' (mul_le_mul' (hzwv v hvv) (he v hv hvv)) le_rfl).trans ?_
      rw [one_mul, ← WithZero.exp_add, WithZero.exp_le_exp]
      omega
  have h1 := hβ _ hsmall
  rw [mul_div_cancel₀ _ hβ0] at h1
  -- `zw·e - zw ∈ 𝔩_0`
  have hdiff : Small 𝔪 0 (zw * (algebraMap (𝓞 F) F e - 1)) := by
    intro v hv
    rw [map_mul, neg_zero, WithZero.exp_zero]
    by_cases hvv : v = v₀
    · subst hvv
      refine (mul_le_mul' hzw₀ he₀).trans ?_
      rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
      have : (d₀ : ℤ) ≤ n := by exact_mod_cast le_max_left d₀ _
      omega
    · refine mul_le_one' (hzwv v hvv) ?_
      refine (Valuation.map_sub _ _ _).trans (max_le (hev v) ?_)
      rw [map_one]
  have h2 : B.psiS h𝔪 zw = 1 := by
    have e1 : zw * algebraMap (𝓞 F) F e = zw + zw * (algebraMap (𝓞 F) F e - 1) := by ring
    rw [e1, (B.psiS h𝔪).map_add, B.psiS_small h𝔪 hdiff, mul_one] at h1
    exact h1
  have hint : zw ∈ (placesOf 𝔪).integer F := fun v hv =>
    hzwv v (fun hvv => hv (by rw [hvv]; exact hv₀))
  obtain ⟨m, hm⟩ := trace_int_of_psiS_eq_one h𝔪 hint h2
  exact hw m hm

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.G1_FI
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-G1, part 5: Lemma FI — finite Fourier inversion on the dual lattices

For an `S_f`-character `ψ` with bounded dual lattices (`HasDual ψ d₀`; for `ψ_{S_f}` this is
`psiS_dual`), `A_M = {β : ψ(β 𝔩_M) = 1}`:

* `sum_char`: orthogonality.  For `β ∈ A_M` and `J ≤ M`,
  `Σ_{t ∈ 𝔩_J/𝔩_M} ψ(βt) = [𝔩_J : 𝔩_M]·1[β ∈ A_J]`.
* `exists_fourier` — **Lemma FI** (MATH3 §4.4): every function on `A_M` invariant under
  translation by `A_J` (`J ≤ M`) is a finite trigonometric polynomial
  `β ↦ Σ_{t ∈ T} ϕ(t) ψ(βt)` with frequencies `T ⊂ 𝔩_J`.
* `exists_fourier_indicator`: the indicator of a coset `β₁ + 𝔩_k` (any depth function `k`),
  restricted to `A_M` — the form used for (G2).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.G1

open ArtinKP.A ArtinKP.S ArtinKP.S2

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

theorem finite_Qt (h𝔪 : 𝔪 ≠ ⊥) {J M : ℤ} (hJM : J ≤ M) : Finite (Qt 𝔪 J M) := by
  have hcard := card_latD_quot h𝔪 (k := fun _ => J) (k' := fun _ => M) (fun _ _ => hJM)
  refine Nat.finite_of_card_ne_zero ?_
  rw [hcard]
  refine (Finset.prod_pos fun v _ => pow_pos ?_ _).ne'
  have := NumberField.HeightOneSpectrum.one_lt_absNorm v
  omega

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.T12.L3X_Meas
/-! # L3X_Meas: sheet measures on the model `SModel 𝔪 k` of `F_S^× / U`

* `lnorm y = Σ_w log|y_w|_w + log |y_f|_{S_f}` (the log of the `S`-norm).
* For a place `w₀`, the base space `SFin × (ℝ^{W∖w₀} × (ℝ/2πℤ)^W)` carries counting ⊗ Lebesgue ⊗
  Haar, and `slice w₀ a` sends it onto the sheet `{lnorm = a}`, solving for the `w₀` log-coordinate.
* `shMeasure w₀ a` is the push-forward: the sheet measure on `X_{e^a}`.
* Translation by `d` maps `shMeasure a` to `shMeasure (a + lnorm d)`; negation maps `shMeasure a` to
  `shMeasure (-a)`; moving the `w₀` coordinate by `t` moves the slice from `a` to `a + t`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-! ### The finite norm -/

theorem SFin.norm_mk (x : Fˣ) :
    (SFin.mk 𝔪 k x).norm = ∏ᶠ v ∈ placesOf 𝔪, NumberField.HeightOneSpectrum.adicAbv F v (x : F) :=
  rfl

theorem SFin.mk_surjective : Function.Surjective (SFin.mk 𝔪 k) := by
  intro y
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul y)
  exact ⟨x, by simp only [SFin.mk, hx]; rfl⟩


theorem SFin.norm_mk_eq_prod (h𝔪 : 𝔪 ≠ ⊥) (x : Fˣ) :
    (SFin.mk 𝔪 k x).norm =
      ∏ v ∈ (finite_placesOf h𝔪).toFinset, NumberField.HeightOneSpectrum.adicAbv F v (x : F) := by
  rw [SFin.norm_mk, finprod_mem_eq_finite_toFinset_prod _ (finite_placesOf h𝔪)]

theorem SFin.norm_mk_pos (h𝔪 : 𝔪 ≠ ⊥) (x : Fˣ) : 0 < (SFin.mk 𝔪 k x).norm := by
  rw [SFin.norm_mk_eq_prod h𝔪]
  exact Finset.prod_pos fun v _ => (AbsoluteValue.pos_iff _).2 x.ne_zero

/-! ### `lnorm` -/

/-! ### Slices -/


/-! ### Measure preservation -/

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.T12.L2B_Bound
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# L2B_Bound: crude norm bounds for the arithmetic factors

`|e| ≤ 1`, `|χ_𝔞| ≤ 1`, `|g_𝔞(k)| ≤ q_𝔞`, `|γ_j(𝔠)| ≤ q_𝔠^{1/2}`, `|F(𝔰,𝔄,h)| ≤ q_𝔰 q_𝔄`,
`|Λ(𝔞)|, |G(𝔞)| ≤ q_𝔞^{1/2}`, `|ϑ(𝔞)| ≤ q_𝔞`.
-/

namespace ArtinPrimitiveRoots.L2B

open NumberField IsDedekindDomain UniqueFactorizationMonoid

variable {F : Type*} [Field F] [NumberField F]

/-! ### Generic lemmas -/

theorem norm_prod_map_le {α : Type*} (s : Multiset α) (f : α → ℂ) (b : α → ℝ)
    (hb : ∀ a ∈ s, 0 ≤ b a) (h : ∀ a ∈ s, ‖f a‖ ≤ b a) :
    ‖(s.map f).prod‖ ≤ (s.map b).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    have hs : ∀ a ∈ s, 0 ≤ b a := fun x hx => hb x (Multiset.mem_cons_of_mem hx)
    exact mul_le_mul (h a (Multiset.mem_cons_self _ _))
      (ih hs fun x hx => h x (Multiset.mem_cons_of_mem hx)) (norm_nonneg _)
      (hb a (Multiset.mem_cons_self _ _))

theorem norm_finsum_le {α : Type*} [Finite α] (f : α → ℂ) (B : ℝ) (h : ∀ a, ‖f a‖ ≤ B) :
    ‖∑ᶠ a, f a‖ ≤ Nat.card α * B := by
  have := Fintype.ofFinite α
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ a, ‖f a‖ ≤ ∑ _a : α, B := Finset.sum_le_sum fun a _ => h a
    _ = Fintype.card α * B := by simp

/-! ### Characters -/

theorem norm_sAddChar_le (𝔪 : Ideal (𝓞 F)) (x : F) : ‖sAddChar 𝔪 x‖ ≤ 1 := by
  unfold sAddChar
  split_ifs
  · rw [Complex.norm_exp]
    simp
  · simp

theorem norm_sexticResidueSymbol_le (ι : F →+* ℂ) (𝔪 P : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ‖sexticResidueSymbol ι 𝔪 P x‖ ≤ 1 := by
  unfold sexticResidueSymbol
  split_ifs with h0 h
  · simp
  · have h6 : (ι ((h.choose : 𝓞 F) : F)) ^ 6 = 1 := by
      have h' : ((h.choose : 𝓞 F) : F) ^ 6 = 1 := by
        have := congrArg (algebraMap (𝓞 F) F) h.choose_spec.1
        simpa using this
      rw [← map_pow, h', map_one]
    exact (Complex.norm_eq_one_of_pow_eq_one h6 (by norm_num)).le
  · simp

theorem norm_residueSymbol_le (ι : F →+* ℂ) (𝔪 𝔞 : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ‖residueSymbol ι 𝔪 𝔞 x‖ ≤ 1 := by
  unfold residueSymbol
  refine (norm_prod_map_le _ _ (fun _ => 1) (fun _ _ => zero_le_one)
    fun P _ => norm_sexticResidueSymbol_le ι 𝔪 P x).trans ?_
  simp

/-! ### Quotients -/

variable {𝔪 : Ideal (𝓞 F)}

theorem card_quot_le {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞) :
    Nat.card (SInt 𝔪 ⧸ 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) ≤ Ideal.absNorm 𝔞 := by
  have : Finite (𝓞 F ⧸ 𝔞) := Ring.HasFiniteQuotients.finiteQuotient h𝔞.1
  let f := Ideal.quotientMap (𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) (algebraMap (𝓞 F) (SInt 𝔪))
    Ideal.le_comap_map
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := C3M.exists_sub_mem_map h𝔞 r
    refine ⟨Ideal.Quotient.mk 𝔞 a, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
    rw [← neg_mem_iff, neg_sub]; exact ha
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.card_le_card_of_surjective f hf

variable {ι : F →+* ℂ}

theorem norm_gaussPhase_le (g : AllowedGen ι 𝔪) (j : ℕ) {𝔠 : Ideal (𝓞 F)}
    (h𝔠 : IsExterior 𝔪 𝔠) : ‖gaussPhase g j 𝔠‖ ≤ Real.sqrt (Ideal.absNorm 𝔠) := by
  have := C3M.finite_quot h𝔠
  unfold gaussPhase
  have hN : (0 : ℝ) < Ideal.absNorm 𝔠 := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h => h𝔠.1 (Ideal.absNorm_eq_zero_iff.1 h))
  have hs : 0 < Real.sqrt (Ideal.absNorm 𝔠) := Real.sqrt_pos.2 hN
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs.le]
  have hsum : ‖∑ᶠ x : SInt 𝔪 ⧸ 𝔠.map (algebraMap (𝓞 F) (SInt 𝔪)),
      residueSymbol ι 𝔪 𝔠 (quotLift x) ^ j * sAddChar 𝔪 ((quotLift x : F) / (g.gen 𝔠 : F))‖ ≤
      Ideal.absNorm 𝔠 := by
    refine (norm_finsum_le _ 1 fun v => ?_).trans ?_
    · rw [norm_mul, norm_pow]
      exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (norm_residueSymbol_le ι 𝔪 𝔠 _))
        (norm_nonneg _) (norm_sAddChar_le _ _)
    · rw [mul_one]; exact_mod_cast card_quot_le h𝔠
  rw [inv_mul_le_iff₀ hs]
  calc _ ≤ (Ideal.absNorm 𝔠 : ℝ) := hsum
    _ = Real.sqrt (Ideal.absNorm 𝔠) * Real.sqrt (Ideal.absNorm 𝔠) :=
      (Real.mul_self_sqrt hN.le).symm

end ArtinPrimitiveRoots.L2B
end

section
-- module Solutions.Artin.T12.L3P_Val
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# L3P_Val: valuations as counts of principal fractional ideals

For `x ≠ 0` in a number field, `v.valuation x = exp (−count_v (x))`, where
`count_v (x) = FractionalIdeal.count F v (spanSingleton x)`. Membership in a nonzero fractional
ideal is a comparison of counts.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal
open scoped nonZeroDivisors Classical

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [NumberField F]

/-! ### The places of `S` -/

variable {𝔪 : Ideal (𝓞 F)}

variable [Fintype (SP 𝔪)]

omit [Fintype (SP 𝔪)] in
theorem one_lt_qS (v : SP 𝔪) : 1 < qS v := by
  rw [qS]
  have h0 : Ideal.absNorm v.1.asIdeal ≠ 0 := by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff]; exact v.1.ne_bot
  have h1 : Ideal.absNorm v.1.asIdeal ≠ 1 := by
    rw [ne_eq, Ideal.absNorm_eq_one_iff]; exact v.1.isPrime.ne_top
  have : 2 ≤ Ideal.absNorm v.1.asIdeal := by omega
  exact_mod_cast this

theorem NN_eq_prod {S : Type*} [Fintype S] (q : S → ℝ) (hq : ∀ v, 0 < q v) (k : S → ℤ) :
    NN q k = ∏ v, q v ^ k v := by
  rw [NN, Real.exp_sum]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [lq, mul_comm, ← Real.rpow_intCast, Real.rpow_def_of_pos (hq v)]

theorem absNorm_Pk (k : SP 𝔪 → ℤ) :
    ((FractionalIdeal.absNorm ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
      FractionalIdeal (𝓞 F)⁰ F) : ℚ) : ℝ) = NN (qS (𝔪 := 𝔪)) k := by
  rw [coe_Pk, map_prod, NN_eq_prod qS (fun v => (one_lt_qS v).trans' one_pos)]
  push_cast
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_zpow₀, coeIdeal_absNorm]
  push_cast; rfl

/-- `|N m| = N 𝔟 · N(P^{val_S m})`. -/
theorem abs_norm_eq {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) {m : SInt 𝔪}
    (hm : Ideal.span {m} = 𝔟.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    ((|Algebra.norm ℚ (m : F)| : ℚ) : ℝ) = (Ideal.absNorm 𝔟 : ℝ) * NN (qS (𝔪 := 𝔪)) (valS (m : F)) := by
  rw [← absNorm_span_singleton (R := 𝓞 F), spanSingleton_eq_mul_Pk h𝔟 hm, map_mul,
    coeIdeal_absNorm, Rat.cast_mul, absNorm_Pk]
  push_cast; rfl

/-! ### Units, the different, and the trace dual -/

end ArtinPrimitiveRoots.L3P
end

section
-- module Solutions.Artin.T12.L3X_Emb
/-! # L3X_Emb: the embedding `F^× → SModel 𝔪 k`

* `sEmb` is a homomorphism on `F^×`.
* The `v`-adic absolute value is `q_v^{-ord_v}`; the finite norm of `[x]` is `∏_{v∈S_f} q_v^{-ord_v x}`.
* The product formula: `lnorm (sEmb m) = log N 𝔟` for an `S`-integer `m` generating the exterior
  ideal `𝔟 R`; in particular `lnorm (sEmb ε) = 0` for `S`-units.
* Valuations at `S_f` descend to `SFin`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory IsDedekindDomain

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

theorem sEmb_of_ne {x : F} (hx : x ≠ 0) :
    sEmb 𝔪 k x = (fun w => (w.mult : ℝ) * Real.log (w x),
      fun w => ((Complex.arg (w.embedding x) : ℝ) : AddCircle (2 * Real.pi)),
      SFin.mk 𝔪 k (Units.mk0 x hx)) := by
  rw [sEmb, dif_neg hx]

theorem sEmb_fin {x : F} (hx : x ≠ 0) : (sEmb 𝔪 k x).2.2 = SFin.mk 𝔪 k (Units.mk0 x hx) := by
  rw [sEmb_of_ne hx]

theorem sEmb_fst {x : F} (hx : x ≠ 0) (w : InfinitePlace F) :
    (sEmb 𝔪 k x).1 w = (w.mult : ℝ) * Real.log (w x) := by
  rw [sEmb_of_ne hx]

/-! ### Absolute values and valuations -/

theorem adicAbv_eq (v : HeightOneSpectrum (𝓞 F)) {x : F} (hx : x ≠ 0) :
    NumberField.HeightOneSpectrum.adicAbv F v x =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-L3P.ordv v x) := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def, L3P.valuation_eq_exp_neg_ordv v hx,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, WithZero.toAdd_unzero_eq_log,
    WithZero.log_exp]
  simp [zpow_neg]

theorem log_SFin_norm_mk (h𝔪 : 𝔪 ≠ ⊥) {x : F} (hx : x ≠ 0) :
    letI : Fintype (L3P.SP 𝔪) := (finite_placesOf h𝔪).fintype
    Real.log (SFin.mk 𝔪 k (Units.mk0 x hx)).norm =
      -∑ v : L3P.SP 𝔪, (L3P.ordv v.1 x : ℝ) * Real.log (Ideal.absNorm v.1.asIdeal : ℝ) := by
  letI : Fintype (L3P.SP 𝔪) := (finite_placesOf h𝔪).fintype
  rw [SFin.norm_mk_eq_prod h𝔪]
  have hq : ∀ v : HeightOneSpectrum (𝓞 F), 0 < (Ideal.absNorm v.asIdeal : ℝ) := fun v => by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast (by omega : 0 < Ideal.absNorm v.asIdeal)
  rw [Real.log_prod (fun v _ => by
    rw [Units.val_mk0, adicAbv_eq v hx]; exact (zpow_pos (hq v) _).ne')]
  rw [← Finset.sum_neg_distrib]
  rw [Finset.sum_subtype (finite_placesOf h𝔪).toFinset (p := fun v => v ∈ placesOf 𝔪)
    (by simp)]
  convert Finset.sum_congr rfl fun (v : L3P.SP 𝔪) _ => (show
    Real.log ((NumberField.HeightOneSpectrum.adicAbv F v.1) ((Units.mk0 x hx : Fˣ) : F)) =
      -((L3P.ordv v.1 x : ℝ) * Real.log (Ideal.absNorm v.1.asIdeal : ℝ)) by
    rw [Units.val_mk0, adicAbv_eq v.1 hx, Real.log_zpow]; push_cast; ring)

/-- The product formula on the model. -/
theorem lnorm_sEmb_gen (h𝔪 : 𝔪 ≠ ⊥) {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) {m : SInt 𝔪}
    (hm : Ideal.span {m} = 𝔟.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    lnorm (sEmb 𝔪 k (m : F)) = Real.log (Ideal.absNorm 𝔟 : ℝ) := by
  letI : Fintype (L3P.SP 𝔪) := (finite_placesOf h𝔪).fintype
  have hm0 : (m : F) ≠ 0 := L3P.ne_zero_of_span_eq h𝔟 hm
  have hN := L3P.abs_norm_eq (𝔪 := 𝔪) h𝔟 hm
  have hinf : ∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log (w (m : F)) =
      Real.log (((|Algebra.norm ℚ (m : F)| : ℚ) : ℝ)) := by
    rw [← InfinitePlace.prod_eq_abs_norm, Real.log_prod (fun w _ =>
      pow_ne_zero _ ((map_ne_zero w).2 hm0))]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Real.log_pow]
  have h𝔟0 : (0 : ℝ) < Ideal.absNorm 𝔟 := by
    have : Ideal.absNorm 𝔟 ≠ 0 := by
      rw [ne_eq, Ideal.absNorm_eq_zero_iff]; exact h𝔟.1
    exact_mod_cast Nat.pos_of_ne_zero this
  rw [lnorm, sEmb_of_ne hm0]
  simp only
  rw [hinf, log_SFin_norm_mk h𝔪 hm0, hN, L3P.NN, Real.log_mul h𝔟0.ne' (Real.exp_pos _).ne',
    Real.log_exp]
  simp only [L3P.lq, L3P.qS, L3P.valS]
  ring

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.KP.H0_Row
/-! # WP-H0, file 3: the coordinate dictionary, part 1 — rows and frequencies

`(z, γ) ↦ γ · rowElt g z` is a bijection `RowClass 𝔪 × U_S⁶ ≃ R ∖ {0}` (`rowEquiv`), so each of the
two `∑'` of the frozen goal is a sum over `ν ∈ R ∖ 0` (`tsum_forward`, `tsum_reflected`, with the
exact summands of the goal). `rowOf ν` is the row class of `ν`: its ideal is the unique exterior
ideal `𝔷` with `𝔷R = νR` (`span_eq_map_rowOf`, `rowOf_ideal_unique`), its multiplicities are the
valuations of `ν` (`count_rowOf`), and it only depends on `ν` modulo `U_S⁶` (`rowOf_gam_mul`). -/

namespace ArtinKP.H0

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

section

variable (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪)
include h𝔪

/-- The ideal of `rowOf ν` generates `νR`. -/
theorem span_eq_map_rowOf (ν : {ν : SInt 𝔪 // ν ≠ 0}) :
    Ideal.span {(ν : SInt 𝔪)} = (rowOf h𝔪 g ν).1.1.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  have : Fintype (L3P.SP 𝔪) := (L3X.finite_placesOf h𝔪).fintype
  have h : (ν : SInt 𝔪) = rowSInt g ((rowEquiv h𝔪 g).symm ν) :=
    (congrArg Subtype.val ((rowEquiv h𝔪 g).apply_symm_apply ν)).symm
  rw [h, rowSInt_eq_par]
  exact L3P.span_unit_mul_gen g _ _

/-! ### Reindexing the two sums of the frozen goal -/

end

end

end ArtinKP.H0
end

section
-- module Solutions.Artin.KP.H0_Coord
/-! # WP-H0, file 4: the coordinate dictionary, part 2 — `SFin`, `sEmb`, `fp`, `Fm`

* `SFin`: `SFin.mk x = 0 ↔ x ∈ SLevel` (`= F^× ∩ U_k`), equality of classes, and weak approximation
  in the form needed: every class of `SFin 𝔪 k` is the class of a nonzero `S`-integer
  (`exists_sInt_rep`); `mem_SLevel_of_sub_one_mem`: `d ≡ 1 mod 𝔪^{k+1}` lies in `SLevel 𝔪 k`.
* `fpF_sEmb_add`: `fp (sEmb ν + y)` is the indicator of `[ν] + y_f = 0` (i.e. `ν·y_f ∈ U_k`)
  times `∏_w ω_{m_w}(ν_w) ω_{m_w}(y_w) κ(|ν|_w · e^{x_w})`.
* `FmOf_sEmb_sub`: the product-form `Fm` at `sEmb ν − y`.
* rotation covariance: `fpF_add_rot`, `FmOf_sub_rot`. -/

namespace ArtinKP.H0

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots FractionalIdeal

set_option linter.unusedSectionVars false

open scoped Classical nonZeroDivisors

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-! ### `SFin` -/

theorem SFin_mk_eq_mk_iff (x y : Fˣ) :
    SFin.mk 𝔪 k x = SFin.mk 𝔪 k y ↔ x⁻¹ * y ∈ SLevel 𝔪 k :=
  Additive.ofMul.injective.eq_iff.trans QuotientGroup.eq

theorem mem_SLevel_iff (x : Fˣ) :
    x ∈ SLevel 𝔪 k ↔ ∀ v ∈ placesOf 𝔪, NumberField.HeightOneSpectrum.adicAbv F v ((x : F) - 1) ≤
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-((k : ℤ) + 1)) := Iff.rfl

/-! ### `SFinCls` -/

/-! ### Angular characters and rotations -/

/-! ### The two functions at `sEmb ν ± y` -/

end

end ArtinKP.H0
end

section
-- module Solutions.Artin.KP.G1_BfS
/-!
# WP-G1, part 10: the majorant `bf` on `SFin 𝔪 k` and its summability (MATH3 §4.5)

`bf([x]) = C · ∏_{v ∈ S_f} min(1, |x|_v^{1/3}) · 1[x ∈ 𝔩_D]` is well defined on
`SFin 𝔪 k = F^×/U_k`, and `Σ_{y ∈ SFin} bf(y) |y|^σ < ∞` for every `σ > -1/3`
(`exists_bf`; the cut `H0.KPCut` wants `σ ≥ -α`, any `α < 1/3`).

Proof: `[x] ↦ (ord_v x)_{v ∈ S_f}` has fibres that inject into the finite group `𝔩_0/𝔩_{k+1}`
(`x ↦ x / t_{ord x}`, `t_n` an element with valuations `n`), and the sum over valuation vectors is a
finite product of geometric series (`summable_pi_prod`, `summable_local_weight`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.G1

open ArtinKP.A ArtinKP.S ArtinKP.S2
open NumberField.HeightOneSpectrum

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

theorem tOf_ne_zero (n : ↥(CubicPkg.sFin 𝔪) → ℤ) : tOf 𝔪 n ≠ 0 := by
  classical
  exact (exists_val_eq 𝔪 (fun v => if h : v ∈ CubicPkg.sFin 𝔪 then n ⟨v, h⟩ else 0)).choose_spec.1

/-- A unit of `SLevel 𝔪 k` is a unit at the places of `S_f`. -/
theorem val_of_mem_SLevel {u : Fˣ} (hu : u ∈ SLevel 𝔪 k) (v : HeightOneSpectrum (𝓞 F))
    (hv : 𝔪 ≤ v.asIdeal) : v.valuation F (u : F) = 1 := by
  have h : Small 𝔪 ((k + 1 : ℕ) : ℤ) ((u : F) - 1) := fun v hv => val_le_of_mem_SLevel hu v hv
  exact h.val_eq_one (by push_cast; omega) v hv

/-- Two representatives of one class of `SFin` have the same valuations at `S_f`. -/
theorem val_eq_of_mk_eq {x x' : Fˣ} (h : SFin.mk 𝔪 k x = SFin.mk 𝔪 k x')
    (v : HeightOneSpectrum (𝓞 F)) (hv : 𝔪 ≤ v.asIdeal) :
    v.valuation F (x' : F) = v.valuation F (x : F) := by
  have hu := (H0.SFin_mk_eq_mk_iff x x').mp h
  have h1 := val_of_mem_SLevel hu v hv
  have e : (x' : F) = (x : F) * ((x⁻¹ * x' : Fˣ) : F) := by
    push_cast
    field_simp
  rw [e, map_mul, h1, mul_one]

theorem mk_repS (y : SFin 𝔪 k) : SFin.mk 𝔪 k (repS y) = y := by
  show Additive.ofMul (QuotientGroup.mk (Quotient.out (Additive.toMul y))) = y
  rw [QuotientGroup.out_eq']
  rfl

theorem sFin_eq_toFinset (h𝔪 : 𝔪 ≠ ⊥) :
    (L3X.finite_placesOf h𝔪).toFinset = CubicPkg.sFin 𝔪 := by
  ext v
  rw [Set.Finite.mem_toFinset, CubicPkg.mem_sFin h𝔪]
  rfl

theorem abv_eq_of_val_eq (v : HeightOneSpectrum (𝓞 F)) {x x' : F} (hx : x ≠ 0) (hx' : x' ≠ 0)
    (h : v.valuation F x' = v.valuation F x) : adicAbv F v x' = adicAbv F v x := by
  have h1 : ordv v x' = ordv v x := by
    rw [val_eq_exp_ordv v hx, val_eq_exp_ordv v hx', WithZero.exp_inj] at h
    omega
  rw [adicAbv_eq_zpow v hx, adicAbv_eq_zpow v hx', h1]

theorem bfF_congr (h𝔪 : 𝔪 ≠ ⊥) (C : ℝ) (D : ℤ) {x x' : Fˣ}
    (h : SFin.mk 𝔪 k x = SFin.mk 𝔪 k x') : bfF 𝔪 C D x' = bfF 𝔪 C D x := by
  classical
  have hval := val_eq_of_mk_eq h
  have hsm : Small 𝔪 D (x' : F) ↔ Small 𝔪 D (x : F) :=
    forall_congr' fun v => forall_congr' fun hv => by rw [hval v hv]
  unfold bfF
  rw [Finset.prod_congr rfl fun v hv => by
    rw [abv_eq_of_val_eq v x.ne_zero x'.ne_zero (hval v ((CubicPkg.mem_sFin h𝔪 v).mp hv))]]
  simp only [hsm]

/-- The pointwise identity behind the summation: `bf · |·|^σ` at `x` is `C` times the product of
the local weights at the valuation vector of `x`. -/
theorem bfF_mul_norm (h𝔪 : 𝔪 ≠ ⊥) (C : ℝ) (D : ℤ) (σ : ℝ) (x : Fˣ) :
    bfF 𝔪 C D x * (SFin.mk 𝔪 k x).norm ^ σ
      = C * ∏ v : ↥(CubicPkg.sFin 𝔪),
          localWeight (Ideal.absNorm v.1.asIdeal : ℝ) D σ (ordVec 𝔪 x v) := by
  classical
  have hx := x.ne_zero
  have habv : ∀ v : HeightOneSpectrum (𝓞 F),
      adicAbv F v (x : F) = (Ideal.absNorm v.asIdeal : ℝ) ^ (-ordv v (x : F)) :=
    fun v => adicAbv_eq_zpow v hx
  have hsmall : Small 𝔪 D (x : F) ↔ ∀ v : ↥(CubicPkg.sFin 𝔪), D ≤ ordVec 𝔪 x v := by
    constructor
    · intro h v
      have := h v.1 ((CubicPkg.mem_sFin h𝔪 v.1).mp v.2)
      rw [val_eq_exp_ordv v.1 hx, WithZero.exp_le_exp] at this
      unfold ordVec
      omega
    · intro h v hv
      have := h ⟨v, (CubicPkg.mem_sFin h𝔪 v).mpr hv⟩
      unfold ordVec at this
      rw [val_eq_exp_ordv v hx, WithZero.exp_le_exp]
      simp only at this
      omega
  rw [L3X.SFin.norm_mk_eq_prod h𝔪, sFin_eq_toFinset h𝔪,
    ← Real.finsetProd_rpow _ _ (fun v _ => (adicAbv F v).nonneg _), bfF]
  by_cases hD : Small 𝔪 D (x : F)
  · rw [if_pos hD, mul_one, mul_assoc, ← Finset.prod_mul_distrib,
      ← Finset.prod_coe_sort (CubicPkg.sFin 𝔪)]
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [localWeight, if_pos (hsmall.mp hD v), habv v.1]
    rfl
  · rw [if_neg hD, mul_zero, zero_mul]
    rw [hsmall] at hD
    push Not at hD
    obtain ⟨v, hv⟩ := hD
    rw [Finset.prod_eq_zero (Finset.mem_univ v) (by rw [localWeight, if_neg (not_le.mpr hv)]),
      mul_zero]

/-- **Injectivity**: a class of `SFin` is determined by its valuation vector and the class of
`x / t_{ord x}` modulo `𝔩_{k+1}`. -/
theorem mk_eq_of_ordVec_clsOf (h𝔪 : 𝔪 ≠ ⊥) {x x' : Fˣ} (hn : ordVec 𝔪 x = ordVec 𝔪 x')
    (hc : clsOf h𝔪 k x = clsOf h𝔪 k x') : SFin.mk 𝔪 k x = SFin.mk 𝔪 k x' := by
  rw [H0.SFin_mk_eq_mk_iff, H0.mem_SLevel_iff]
  intro v hv
  unfold clsOf at hc
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at hc
  have hc' : Small 𝔪 ((k : ℤ) + 1)
      (-((x : F) / tOf 𝔪 (ordVec 𝔪 x)) + (x' : F) / tOf 𝔪 (ordVec 𝔪 x')) := hc
  rw [← hn] at hc'
  have ht := tOf_ne_zero (𝔪 := 𝔪) (ordVec 𝔪 x)
  have hx := x.ne_zero
  have e : ((x⁻¹ * x' : Fˣ) : F) - 1
      = (-((x : F) / tOf 𝔪 (ordVec 𝔪 x)) + (x' : F) / tOf 𝔪 (ordVec 𝔪 x))
        * ((x : F) / tOf 𝔪 (ordVec 𝔪 x))⁻¹ := by
    push_cast
    field_simp
    ring
  refine abv_le_of_val_le v ?_
  rw [e, map_mul, map_inv₀, val_div_tOf h𝔪 x v hv, inv_one, mul_one]
  exact hc' v hv

/-- **The majorant `bf` on `SFin 𝔪 k` and its summability** (MATH3 §4.5; closes stub G1-1 for all
`σ > -1/3`). -/
theorem exists_bf (h𝔪 : 𝔪 ≠ ⊥) (k : ℕ) (C : ℝ) (hC : 0 ≤ C) (D : ℤ) :
    ∃ bf : SFin 𝔪 k → ℝ,
      (∀ x : Fˣ, bf (SFin.mk 𝔪 k x)
        = C * (∏ v ∈ CubicPkg.sFin 𝔪, min 1 (adicAbv F v (x : F) ^ (1 / 3 : ℝ)))
          * (open Classical in if Small 𝔪 D (x : F) then 1 else 0)) ∧
      ∀ σ : ℝ, -(1 / 3 : ℝ) < σ → Summable (fun y : SFin 𝔪 k => bf y * SFin.norm y ^ σ) := by
  classical
  refine ⟨fun y => bfF 𝔪 C D (repS y), fun x => ?_, fun σ hσ => ?_⟩
  · exact bfF_congr h𝔪 C D (mk_repS (SFin.mk 𝔪 k x)).symm
  have hfin := finite_Qt (𝔪 := 𝔪) h𝔪 (show (0 : ℤ) ≤ (k : ℤ) + 1 by omega)
  cases nonempty_fintype (Qt 𝔪 0 ((k : ℤ) + 1))
  -- summability over valuation vectors × the finite group
  have hq : ∀ v : ↥(CubicPkg.sFin 𝔪), (1 : ℝ) < (Ideal.absNorm v.1.asIdeal : ℝ) := fun v => by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v.1
  have hG₀ : Summable fun n : ↥(CubicPkg.sFin 𝔪) → ℤ =>
      ∏ v, localWeight (Ideal.absNorm v.1.asIdeal : ℝ) D σ (n v) :=
    summable_pi_prod _ (fun v n => localWeight_nonneg (zero_lt_one.trans (hq v)) D σ n)
      (fun v => summable_local_weight (hq v) D hσ)
  set G : (↥(CubicPkg.sFin 𝔪) → ℤ) × Qt 𝔪 0 ((k : ℤ) + 1) → ℝ := fun p =>
    C * ∏ v, localWeight (Ideal.absNorm v.1.asIdeal : ℝ) D σ (p.1 v) with hGdef
  have hG0 : 0 ≤ G := fun p => mul_nonneg hC (Finset.prod_nonneg fun v _ =>
    localWeight_nonneg (zero_lt_one.trans (hq v)) D σ _)
  have hGs : Summable G := by
    rw [summable_prod_of_nonneg hG0]
    refine ⟨fun n => Summable.of_finite, ?_⟩
    simp only [hGdef, tsum_fintype, Finset.sum_const, nsmul_eq_mul]
    exact (hG₀.mul_left C).mul_left _
  set Θ : SFin 𝔪 k → (↥(CubicPkg.sFin 𝔪) → ℤ) × Qt 𝔪 0 ((k : ℤ) + 1) := fun y =>
    (ordVec 𝔪 (repS y), clsOf h𝔪 k (repS y)) with hΘ
  have hΘinj : Function.Injective Θ := by
    intro y y' h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    rw [← mk_repS y, ← mk_repS y']
    exact mk_eq_of_ordVec_clsOf h𝔪 h1 h2
  have heq : (fun y : SFin 𝔪 k => bfF 𝔪 C D (repS y) * SFin.norm y ^ σ) = G ∘ Θ := by
    funext y
    have := bfF_mul_norm (k := k) h𝔪 C D σ (repS y)
    rw [mk_repS] at this
    exact this
  rw [heq]
  exact hGs.comp_injective hΘinj

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.G1_Res
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-G1, part 6: interface repairs for WP-E's abstract residue layer (MATH3 findings 6, 7)

New lemmas beside `E.ResFun`, `E.HasResOn`, `E.Theta` (no file of WP-E is edited).

* `ResFun.SmulOn T U`: the scalar law of a residue functional for multipliers that are holomorphic
  on the open set `U` only (`E.ResFun.smul` asks for an entire multiplier).
* `hasResOn_smul`: for the model `HasResOn Ω s₀ γ`, a multiplier analytic on `Ω` with a limit `L`
  along the path `γ` multiplies the residue by `L`.
* `ofContinuation_smulOn`: `ResFun.ofContinuation Ω s₀ γ …` has `SmulOn U` for every open
  `U ⊇ Ω ∪ {s₀}`; `resFunSlit_smulOn`: the slit model has `SmulOn {Re s > 1}`.
  (What is true and sufficient: the multiplier must be analytic on the region `Ω` and continuous at
  `s₀` along the ray; holomorphy on a neighbourhood of `Ω ∪ {s₀}` gives both.)
* `Theta.tau_congr_at`: `τ` sees a section through `Lam` at the one frequency `ν` only, with a
  scalar that may depend on `ν` (`E.Theta.tau_congr` has one scalar for all `ν`).
* `Theta.tau_smul_at`: the same with an entire multiplier `h(s)`.
* `Theta.tau_sum_at`: `Lam Φ c ν s = Σ_i h_i(s) Lam Ψ_i c ν s` on `Re s > 2` gives
  `τ_Φ(ν) = Σ_i h_i(s₀) τ_{Ψ_i}(ν)`, for multipliers holomorphic on `U` (given `SmulOn U`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Filter Topology

namespace ArtinKP.G1

open ArtinKP.B7 ArtinKP.E

/-- **Scalar law of the model**: a multiplier analytic on the region with a limit along the path
multiplies the residue by that limit. -/
theorem hasResOn_smul {Ω : Set ℂ} {s₀ : ℂ} {γ : ℝ → ℂ} {f : ℂ → ℂ} {r : ℂ} (h : ℂ → ℂ) (L : ℂ)
    (hh : AnalyticOnNhd ℂ h Ω) (hl : Tendsto (fun t : ℝ => h (γ t)) (𝓝[>] 0) (𝓝 L))
    (hf : HasResOn Ω s₀ γ f r) : HasResOn Ω s₀ γ (fun s => h s * f s) (L * r) := by
  obtain ⟨Fc, hF, hFf, hlim⟩ := hf
  refine ⟨fun s => h s * Fc s, hh.mul hF, fun s hs => by
    show h s * Fc s = h s * f s
    rw [hFf s hs], ?_⟩
  refine (hl.mul hlim).congr fun t => ?_
  ring

/-- The continuation-and-limit functional has the scalar law for multipliers holomorphic on any
open set containing the region and the point `s₀`. -/
theorem ofContinuation_smulOn (Ω : Set ℂ) (s₀ : ℂ) (γ : ℝ → ℂ) (hΩ : IsPreconnected Ω)
    (h2 : {s : ℂ | 2 < s.re} ⊆ Ω) (hγ : Tendsto γ (𝓝[>] 0) (𝓝 s₀))
    (hγΩ : ∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ∈ Ω) {U : Set ℂ} (hU : IsOpen U) (hΩU : Ω ⊆ U)
    (hs₀ : s₀ ∈ U) : (ResFun.ofContinuation Ω s₀ γ hΩ h2 hγ hγΩ).SmulOn U := by
  intro f r h hh hf
  have hcont : ContinuousAt h s₀ := (hh.differentiableAt (hU.mem_nhds hs₀)).continuousAt
  exact hasResOn_smul h (h s₀) ((hh.analyticOnNhd hU).mono hΩU) (hcont.tendsto.comp hγ) hf

/-- **The slit model has the scalar law for multipliers holomorphic on `Re s > 1`.** -/
theorem resFunSlit_smulOn : resFunSlit.SmulOn {s : ℂ | 1 < s.re} := by
  unfold resFunSlit
  refine ofContinuation_smulOn _ _ _ _ _ _ _ (isOpen_lt continuous_const Complex.continuous_re)
    (fun s hs => hs.1) ?_
  show (1 : ℝ) < (4 / 3 : ℂ).re
  norm_num

end ArtinKP.G1
end

section
-- module Solutions.Artin.KP.G1_Kir
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-G1, part 7: the Kirillov function — (K1)–(K4), the class decomposition, the bound

Section level (any `S_f`-character `ψ` with bounded dual lattices, `HasDual ψ d₀`):

* `exists_Kt_support` (K3): `Kt Φ β η s = 0` unless `β ∈ 𝔩_D` (support in a fractional ideal,
  i.e. `|β|_v ≤ q_v^{-D}` at every `v ∈ S_f` separately); from `S.kir_eq_zero` and DUAL.
* `exists_Kt_bound` (K2): `|β|^{1/3} |Kt Φ β η (4/3)| ≤ C ∏_{v ∈ S_f} min(1, |β|_v^{1/3})` for all
  `β ∈ F^×`, all classes `η`; from `GL.xi_bound`, the support, and `S2.K_eq`.
* `exists_Kt_deep` (K1): `Kt Φ (βu) η s = Kt Φ β η s` for `u` deep.

`τ` level, for `D = B.kubota hG hz6` (`ψ = B.psiS`), any `T : E.Theta D (4/3)`:

* `tau_smul`, `tau_nT`, `tau_addProj`, `tau_sum`, `tau_smulFun`.
* `Kir T Φ β := τ_{Ã(β)Φ}(1)` (MATH3 §0), `xi T Φ β := |β|^{1/3} Kir T Φ β`; **(K4)**:
  `Kir_torusT` (`𝒦_{Ã(β₀)Φ}(β) = ⟨β,β₀⟩𝒦_Φ(ββ₀)`), `Kir_nT` (`𝒦_{n(t)Φ}(β) = ψ(βt)𝒦_Φ(β)`),
  `Kir_smulFun`, `Kir_addProj` (G2), `Kir_sum`, `xi_torusT`, `xi_nT`; `exists_Kir_deep` (K1);
  `Kir_cusp`/`xi_cusp` (MATH3 (2.2)).
* `tau_classDecomp` — **(CD)**: `τ_Ψ(ν) = Σ_η Lam Ψ η ν (4/3) · vol(𝔩_M)⁻¹ τ_{bigCell_η}(ν)`,
  given the scalar law `T.SmulOn {Re s > 1}` (true for `resFunSlit`: `resFunSlit_smulOn`).
* `exists_Kir_classDecomp`: one finite set of classes and weights `w_η` with
  `𝒦_Φ(β) = Σ_η Kt Φ β η (4/3) · w_η` for all `β ∈ F^×`.
* `exists_xi_le` — **the majorant for `ξ`** (MATH3 §4.3):
  `|ξ_Φ(β)| ≤ C ∏_v min(1, |β|_v^{1/3})` and `ξ_Φ(β) = 0` unless `β ∈ 𝔩_D`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.G1

open ArtinKP.A ArtinKP.S ArtinKP.S2 ArtinKP.E ArtinKP.B7

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

/-! ### Section level: support, bound, deep invariance -/

/-- **(K3) support**: the Kirillov term vanishes outside a fractional ideal. -/
theorem exists_Kt_support (ψ : SfChar 𝔪) (hG : Good 𝔪) {d₀ : ℤ} (hd : HasDual ψ d₀)
    (Φ : GSection ι P 𝔪) :
    ∃ D : ℤ, ∀ (β η : F) (s : ℂ), η ≠ 0 → ¬ Small 𝔪 D β → Kt ψ hG Φ β η s = 0 := by
  obtain ⟨N, hN⟩ := kir_eq_zero ψ Φ
  refine ⟨-N - d₀, fun β η s hη hβD => ?_⟩
  by_cases hβ : β = 0
  · simp [Kt, hβ]
  by_contra hne
  refine hβD (hd N β ?_)
  by_contra hA
  unfold Adual at hA
  push Not at hA
  obtain ⟨b, hb, hb1⟩ := hA
  have hv : Valid ψ Φ β (fun _ => max (depth ψ hG Φ β) N) :=
    (valid_depth ψ hG Φ β).mono fun _ _ => le_max_left _ _
  rw [Kt_eq_kir ψ hG Φ hη hβ s hv] at hne
  exact hne (hN _ (le_max_right _ _) η β s hv.2 b hb hb1)

open NumberField.HeightOneSpectrum in
/-- **(K2) the bound for the Kirillov term** at `s₀ = 4/3`, for all `β ∈ F^×`, uniformly in the
class `η`. -/
theorem exists_Kt_bound (ψ : SfChar 𝔪) (hG : Good 𝔪) {d₀ : ℤ} (hd : HasDual ψ d₀)
    (Φ : GSection ι P 𝔪) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β η : F, β ≠ 0 → η ≠ 0 →
      absS 𝔪 β ^ (1 / 3 : ℝ) * ‖Kt ψ hG Φ β η (4 / 3)‖
        ≤ C * ∏ v ∈ CubicPkg.sFin 𝔪, min 1 (adicAbv F v β ^ (1 / 3 : ℝ)) := by
  obtain ⟨D, hD⟩ := exists_Kt_support ψ hG hd Φ
  obtain ⟨B, hB0, hB⟩ := GL.xi_bound ψ hG Φ 2 D
  set K₀ : ℝ := vol 𝔪 0 * ∑' u : F ⧸ lat 𝔪 0, normS 𝔪 1 u.out ^ (-(4 / 3 : ℂ).re) with hK₀
  have hK₀0 : 0 ≤ K₀ :=
    mul_nonneg (vol_nonneg 0) (tsum_nonneg fun _ => Real.rpow_nonneg (normS_nonneg _ _) _)
  refine ⟨B * K₀, mul_nonneg hB0 hK₀0, fun β η hβ hη => ?_⟩
  have hmin : 0 ≤ ∏ v ∈ CubicPkg.sFin 𝔪, min 1 (adicAbv F v β ^ (1 / 3 : ℝ)) :=
    Finset.prod_nonneg fun v _ => le_min zero_le_one (Real.rpow_nonneg ((adicAbv F v).nonneg β) _)
  by_cases hβD : Small 𝔪 D β
  · have hv : Valid ψ Φ β (fun _ => max (depth ψ hG Φ β) 0) :=
      (valid_depth ψ hG Φ β).mono fun _ _ => le_max_left _ _
    rw [Kt_eq_kir ψ hG Φ hη hβ _ hv, hK₀,
      ← K_eq ψ hG.ne_bot (le_max_right (depth ψ hG Φ β) 0)]
    have hnorm : ‖(4 / 3 : ℂ)‖ ≤ 2 := by
      rw [show (4 / 3 : ℂ) = ((4 / 3 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real]
      norm_num
    have hre : (1 : ℝ) < (4 / 3 : ℂ).re := by
      rw [show (4 / 3 : ℂ) = ((4 / 3 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
      norm_num
    exact hB _ hnorm hre _ η β hη hβ hβD
  · rw [hD β η _ hη hβD, norm_zero, mul_zero]
    exact mul_nonneg (mul_nonneg hB0 hK₀0) hmin

/-! ### `τ` level -/

section tau

variable [IsTotallyComplex F] (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  (T : Theta (B.kubota (ι := ι) (P := P) hG hz6) (4 / 3 : ℂ))

/-! ### The Kirillov function -/

theorem Kir_of_ne (Φ : GSection ι P 𝔪) {β : F} (hβ : β ≠ 0) :
    Kir hG hz6 T Φ β = T.tau (Φ.torusT hG β hβ) 1 := by
  rw [Kir, dif_neg hβ]

/-! ### The class decomposition and the majorant -/

open NumberField.HeightOneSpectrum in
/-- **The majorant for the Kirillov function** (MATH3 §4.3, MATH2 §6.3 (K2), (K3)), for every
section: `|ξ_Φ(β)| ≤ C ∏_{v ∈ S_f} min(1, |β|_v^{1/3})` and `ξ_Φ(β) = 0` unless `β ∈ 𝔩_D`
(i.e. `|β|_v ≤ q_v^{-D}` at every `v ∈ S_f`). -/
theorem exists_xi_le (hsm : T.toResFun.SmulOn {s : ℂ | 1 < s.re}) (Φ : GSection ι P 𝔪) :
    ∃ (C : ℝ) (D : ℤ), 0 ≤ C ∧ ∀ β : F, β ≠ 0 →
      (¬ Small 𝔪 D β → xi hG hz6 T Φ β = 0) ∧
      ‖xi hG hz6 T Φ β‖ ≤ C * ∏ v ∈ CubicPkg.sFin 𝔪, min 1 (adicAbv F v β ^ (1 / 3 : ℝ)) := by
  obtain ⟨d₀, hd⟩ := psiS_dual (F := F) hG.ne_bot
  obtain ⟨Tc, w, hKir⟩ := exists_Kir_classDecomp hG hz6 T hsm Φ
  obtain ⟨D, hD⟩ := exists_Kt_support (B.psiS hG.ne_bot) hG hd Φ
  obtain ⟨C, hC0, hC⟩ := exists_Kt_bound (B.psiS hG.ne_bot) hG hd Φ
  refine ⟨C * ∑ η ∈ Tc, ‖w η‖, D,
    mul_nonneg hC0 (Finset.sum_nonneg fun _ _ => norm_nonneg _), fun β hβ => ⟨fun hβD => ?_, ?_⟩⟩
  · rw [xi, hKir β hβ, Finset.sum_eq_zero fun η _ => by rw [hD β η.1 _ η.2 hβD, zero_mul],
      mul_zero]
  · have habs : 0 ≤ absS 𝔪 β ^ (1 / 3 : ℝ) := Real.rpow_nonneg (absS_nonneg _) _
    rw [xi, norm_mul, Complex.norm_real, Real.norm_of_nonneg habs, hKir β hβ]
    calc absS 𝔪 β ^ (1 / 3 : ℝ)
          * ‖∑ η ∈ Tc, Kt (B.psiS hG.ne_bot) hG Φ β η.1 (4 / 3) * w η‖
        ≤ absS 𝔪 β ^ (1 / 3 : ℝ)
          * ∑ η ∈ Tc, ‖Kt (B.psiS hG.ne_bot) hG Φ β η.1 (4 / 3)‖ * ‖w η‖ :=
          mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
            (Finset.sum_le_sum fun η _ => (norm_mul _ _).le)) habs
      _ = ∑ η ∈ Tc, (absS 𝔪 β ^ (1 / 3 : ℝ)
            * ‖Kt (B.psiS hG.ne_bot) hG Φ β η.1 (4 / 3)‖) * ‖w η‖ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun η _ => by ring
      _ ≤ ∑ η ∈ Tc, (C * ∏ v ∈ CubicPkg.sFin 𝔪, min 1 (adicAbv F v β ^ (1 / 3 : ℝ))) * ‖w η‖ :=
          Finset.sum_le_sum fun η _ =>
            mul_le_mul_of_nonneg_right (hC β η.1 hβ η.2) (norm_nonneg _)
      _ = _ := by
          rw [← Finset.mul_sum]
          ring

end tau

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.G1_Main
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex
/-!
# WP-G1: the majorant in the cut's vocabulary, and the axiom check

`norm_xi_le_bf`: for every genuine section `Φ` there is `bf : SFin 𝔪 k → ℝ` with
`|ξ_Φ(x)| ≤ bf([x])` for all `x ∈ F^×` and `Σ_y bf(y) |y|^σ < ∞` for all `σ > -1/3`
(MATH3 §4 (2e); `H0.KPCut` asks for `σ ≥ -α`, so any `α < 1/3` is available, e.g. `α = 1/4`).
`bf` is `C · ∏_v min(1, |x|_v^{1/3}) · 1[x ∈ 𝔩_D]` (`exists_bf`), `C`, `D` from `exists_xi_le`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.G1

open ArtinKP.A ArtinKP.S ArtinKP.S2 ArtinKP.E ArtinKP.B7

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

/-- **The majorant for `ξ` in the cut's vocabulary** (MATH3 §4 (2e)). -/
theorem norm_xi_le_bf [IsTotallyComplex F] (hG : Good 𝔪) {z6 : 𝓞 F}
    (hz6 : IsPrimitiveRoot z6 6)
    (T : Theta (B.kubota (ι := ι) (P := P) hG hz6) (4 / 3 : ℂ))
    (hsm : T.toResFun.SmulOn {s : ℂ | 1 < s.re}) (Φ : GSection ι P 𝔪) (k : ℕ) :
    ∃ bf : SFin 𝔪 k → ℝ,
      (∀ x : Fˣ, ‖xi hG hz6 T Φ (x : F)‖ ≤ bf (SFin.mk 𝔪 k x)) ∧
      ∀ σ : ℝ, -(1 / 3 : ℝ) < σ → Summable (fun y : SFin 𝔪 k => bf y * SFin.norm y ^ σ) := by
  classical
  obtain ⟨C, D, hC0, hC⟩ := exists_xi_le hG hz6 T hsm Φ
  obtain ⟨bf, hbf, hsum⟩ := exists_bf (F := F) hG.ne_bot k C hC0 D
  refine ⟨bf, fun x => ?_, hsum⟩
  rw [hbf x]
  obtain ⟨h0, hle⟩ := hC (x : F) x.ne_zero
  by_cases hD : Small 𝔪 D (x : F)
  · rw [if_pos hD, mul_one]
    exact hle
  · rw [if_neg hD, mul_zero, h0 hD, norm_zero]

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.T12.L3X_Coef
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # L3X_Coef: the forward Fourier coefficient and Cor 5.2

* `coefF g 𝔟 z`: the forward coefficient of `L3X_CutKP` at the frequency class `z` (row ideal `𝔟`):
  `χ_𝔟(x) ∏_{P ∣ 𝔷} W_P(a(x))`, `x = rowElt g z`, with `W_P` the spherical values (5.4).
* `gaussPhase_eq_prod_uSym` (from (3.10)): `γ₂(𝔠) = ∏_{P ∣ 𝔠} γ₂(P) χ_P(c/p)²` for squarefree `𝔠`.
* `prodW_cube` (Cor 5.2): `∏_{P ∣ 𝔠𝔫³} χ_P(A/p^e)^{2e} W_P(p^e) = γ₂(𝔠) / (q_𝔠^{1/2} q_𝔫)`,
  `A = gen(𝔠𝔫³)`, and the product vanishes when some exponent is `≡ 2 (mod 3)`.
* `tsum_coefF_eq_fwd`: the forward unfolded sum is Cut63V's left side `L3V.fwd`.
* `norm_coefF_le`: `‖coefF‖ ≤ 1`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots.L3X

open L3V

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-! ### Norm bounds -/

lemma norm_sext_le (P : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ‖sexticResidueSymbol ι 𝔪 P x‖ ≤ 1 := by
  unfold sexticResidueSymbol
  split_ifs with h1 h2
  · simp
  · have hζ := h2.choose_spec.1
    have h6 : (ι (h2.choose : F)) ^ 6 = 1 := by
      rw [← map_pow]
      have : ((h2.choose : 𝓞 F) : F) ^ 6 = 1 := by
        exact_mod_cast congrArg (fun z : 𝓞 F => (z : F)) hζ
      rw [this, map_one]
    have hn : ‖ι (h2.choose : F)‖ ^ 6 = 1 := by rw [← norm_pow, h6, norm_one]
    have := (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num : (6 : ℕ) ≠ 0)).1 hn
    rw [this]
  · simp

lemma norm_residueSymbol_le' (𝔞 : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ‖residueSymbol ι 𝔪 𝔞 x‖ ≤ 1 := by
  unfold residueSymbol
  induction (normalizedFactors 𝔞) using Multiset.induction_on with
  | empty => simp
  | cons P s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    exact (mul_le_mul (norm_sext_le P x) ih (norm_nonneg _) zero_le_one).trans (by norm_num)

lemma norm_localSymbol_le (P : Ideal (𝓞 F)) (t : F) : ‖localSymbol ι 𝔪 P t‖ ≤ 1 := by
  unfold localSymbol
  split_ifs with h
  · rw [norm_mul, Complex.norm_conj]
    exact (mul_le_mul (norm_sext_le P _) (norm_sext_le P _) (norm_nonneg _) zero_le_one).trans
      (by norm_num)
  · simp

lemma one_le_absNorm_of_prime {P : Ideal (𝓞 F)} (_hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    (1 : ℝ) ≤ Ideal.absNorm P := by
  have : Ideal.absNorm P ≠ 0 := fun h => hP0 (Ideal.absNorm_eq_zero_iff.1 h)
  exact_mod_cast Nat.one_le_iff_ne_zero.2 this


/-! ### Unit-part symbols of generators -/


/-! ### (3.10) in unit-part form, and Cor 5.2 -/


/-! ### The forward sum -/


/-! ### Bounds on the exterior local factors (no `HypChi`) -/

section bounds

variable (g : AllowedGen ι 𝔪) {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hPe : IsExterior 𝔪 P)
include hP hPe

theorem norm_Wv_le (e : ℕ) : ‖L3V.Wv g P e‖ ≤ 1 := by
  have hP1 := one_le_absNorm_of_prime hP hPe.1
  have hq0 : (0 : ℝ) < Ideal.absNorm P := lt_of_lt_of_le zero_lt_one hP1
  have hgp := L2B.norm_gaussPhase_le g 2 hPe
  unfold Wv
  split_ifs with h0 h1
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hq0.le _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hP1 (by simp)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hq0.le _)]
    calc (Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ) - 1 / 2) * ‖gaussPhase g 2 P‖
        ≤ (Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ) - 1 / 2) * Real.sqrt (Ideal.absNorm P) :=
          mul_le_mul_of_nonneg_left hgp (Real.rpow_nonneg hq0.le _)
      _ = (Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ)) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_add hq0]; ring_nf
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hP1 (by simp)
  · simp

theorem norm_Wsph_le (e₀ : ℤ) (t : F) : ‖L3V.Wsph g P e₀ t‖ ≤ 1 := by
  unfold Wsph
  split_ifs
  · simp
  · rw [norm_mul, norm_pow]
    exact (mul_le_mul (pow_le_one₀ (norm_nonneg _) (norm_localSymbol_le P t))
      (norm_Wv_le g hP hPe _) (norm_nonneg _) zero_le_one).trans (by norm_num)

end bounds

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.KP.H_SumMain
/-! # WP-HA, file 3: pointwise summability of the two sums of `H0.KPCutNu`

For every `y : SModel 𝔪 k`:

* `summable_forward_coef`: `∑_{ν ∈ R∖0} coef(ν) · fp(sEmb ν + y)` converges absolutely for any
  bounded coefficient function (the support condition `[ν] + y_f = 0` confines `ν` to one class of
  `SFin`, a separated set in the Minkowski space; `κ(t) ≤ C min(t^α, t^{-4})`).
* `summable_reflected_coef`: `∑_{ν ∈ R∖0} coef(ν) · Fm(cl ν, sEmb ν − y)` converges absolutely for
  any bounded coefficient function and any class function `cl`, under the cut's hypotheses on
  `J`, `bf` (used at `σ = 0` and `σ = 4·#places`).
* `summable_forward`, `summable_reflected`: the two families of `KPCutNu` verbatim;
  `summable_forward_kappaB`, `summable_reflected_kappaB`: with `κ = K.kappaB c` and the cut's
  hypotheses exactly. -/

namespace ArtinKP.H

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-- `‖coefF'‖ ≤ 1`, with no hypothesis on `𝔪`. -/
theorem norm_coefF'_le (g : AllowedGen ι 𝔪) (𝔟 : Ideal (𝓞 F)) (z : RowClass 𝔪) :
    ‖L3X.coefF' g 𝔟 z‖ ≤ 1 := by
  unfold L3X.coefF'
  rw [norm_mul, norm_prod]
  refine (mul_le_mul (L3X.norm_residueSymbol_le' _ _) (Finset.prod_le_one (fun _ _ => norm_nonneg _)
    fun P hP => ?_) (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one).trans (by norm_num)
  obtain ⟨hPp, hPe⟩ := C3M.exterior_of_mem_factors z.1.2 (Multiset.mem_toFinset.1 hP)
  exact L3X.norm_Wsph_le g hPp hPe _ _

end

end ArtinKP.H
end

section
-- module Solutions.Artin.KP.T_Theta
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-T, file 6: genuine sections — `aCont`, `tau`, the instance `E.Theta`, coefficients of `θ`

For `ν ∈ R ∖ 0` and a genuine section `Φ` (`Ψ = Φ.twist hG hz6`, `a₀ = (B.kubota hG hz6).aSer Φ ν`):

* `aCont hG hz6 Φ ν = contSlit a₀` — holomorphic on `E.slit` (`differentiableOn_aCont`), equal to
  the series on `Re s > 2` (`aCont_eq`), unique (`aCont_unique`);
* `tau hG hz6 Φ ν = resSlit a₀ = lim_{t↓0} (s_t − 4/3)·aCont(s_t)` (`tendsto_tau`);
* **`theta hG hz6 : E.Theta (B.kubota hG hz6) (4/3)`** with `toResFun = E.resFunSlit`;
* **`coeff_theta`** (item 3): the Fourier coefficients of `C5.theta Γ (Φ.twist)` for the cells of
  any `Γ`; `coeff_cont`: the same for the continuation on `E.slit`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (Φ : GSection ι P 𝔪)
  (ν : SInt 𝔪)

variable {ν}

theorem theta_toResFun : (theta (ι := ι) (P := P) hG hz6).toResFun = E.resFunSlit := rfl

/-! ### The archimedean factor as an integral over `v` -/


/-! ### Fourier coefficients of `θ` for the cells of `Γ` -/

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.G2a_Major
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex
/-! # WP-G2a, file 2: the summable majorant of `τ_Φ(ν)·W_{4/3}(ν; v)`

* `ThmE hG hz6 g`: **named hypothesis**, Theorem E for the instance `T.theta hG hz6` in the form
  of `H.tau_eq_coefF'` (`thmE_of_PER` derives it from cube periodicity at every exterior prime
  plus the standing data of `H_Tau`).
* `absNorm_rowOf`: the product formula, exact: `N(νR) = ∏_w |ν|_w^{mult} · |ν|_{S_f}`.
* `norm_tau_le`: `|τ_Φ(ν)| ≤ ∏_w |ν|_w^{2/3} · bf([ν])` with `bf` summable against `|y|^σ`,
  `σ > −1/3` (G1's majorant of the Kirillov function).
* `exists_major`: for every box `vBox F n₀` and every `p` a summable `u` with
  `∏_w (1+|ν|_w)^p · |τ_Φ(ν) W_{4/3}(ν; v)| ≤ u ν` for all `v` in the box.
-/

open scoped ComplexConjugate Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

/-- The product formula on `R ∖ 0`, exact. -/
theorem absNorm_rowOf (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) (k : ℕ) (d : {ν : SInt 𝔪 // ν ≠ 0}) :
    (Ideal.absNorm (H0.rowOf h𝔪 g d).1.1 : ℝ) =
      (∏ w : InfinitePlace F, w ((d : SInt 𝔪) : F) ^ w.mult) *
        (SFin.mk 𝔪 k (Units.mk0 ((d : SInt 𝔪) : F) (H0.coe_ne_zero d))).norm := by
  have hd := H0.coe_ne_zero d
  have h1 := L3X.lnorm_sEmb_gen (k := k) h𝔪 (H0.rowOf h𝔪 g d).1.2 (H0.span_eq_map_rowOf h𝔪 g d)
  have hN : (0 : ℝ) < Ideal.absNorm (H0.rowOf h𝔪 g d).1.1 := by
    have : Ideal.absNorm (H0.rowOf h𝔪 g d).1.1 ≠ 0 := by
      rw [ne_eq, Ideal.absNorm_eq_zero_iff]; exact (H0.rowOf h𝔪 g d).1.2.1
    exact_mod_cast Nat.pos_of_ne_zero this
  have hP : 0 < ∏ w : InfinitePlace F, w ((d : SInt 𝔪) : F) ^ w.mult :=
    Finset.prod_pos fun w _ => pow_pos (w.pos_iff.2 hd) _
  have hn := L3X.SFin.norm_mk_pos (k := k) h𝔪 (Units.mk0 _ hd)
  have h2 : L3X.lnorm (sEmb 𝔪 k ((d : SInt 𝔪) : F)) =
      ∑ w : InfinitePlace F, Real.log (w ((d : SInt 𝔪) : F) ^ w.mult) +
        Real.log (SFin.mk 𝔪 k (Units.mk0 ((d : SInt 𝔪) : F) hd)).norm := by
    rw [L3X.lnorm, L3X.sEmb_fin hd]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [L3X.sEmb_fst hd, Real.log_pow]
  refine Real.log_injOn_pos (Set.mem_Ioi.mpr hN) (Set.mem_Ioi.mpr (mul_pos hP hn)) ?_
  rw [Real.log_mul hP.ne' hn.ne', Real.log_prod (fun w _ => (pow_pos (w.pos_iff.2 hd) _).ne'),
    ← h2, h1]

theorem norm_mk_eq_absS (h𝔪 : 𝔪 ≠ ⊥) (k : ℕ) (x : Fˣ) :
    (SFin.mk 𝔪 k x).norm = absS 𝔪 (x : F) := by
  rw [L3X.SFin.norm_mk_eq_prod h𝔪, G1.sFin_eq_toFinset h𝔪]
  rfl

variable [IsTotallyComplex F]

/-- `N(νR)^{1/3} = ∏_w |ν|_w^{2/3} · |ν|_{S_f}^{1/3}`. -/
theorem absNorm_rowOf_rpow (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) (d : {ν : SInt 𝔪 // ν ≠ 0}) :
    (Ideal.absNorm (H0.rowOf h𝔪 g d).1.1 : ℝ) ^ (1 / 3 : ℝ) =
      (∏ w : InfinitePlace F, w ((d : SInt 𝔪) : F) ^ (2 / 3 : ℝ)) *
        absS 𝔪 ((d : SInt 𝔪) : F) ^ (1 / 3 : ℝ) := by
  rw [absNorm_rowOf h𝔪 g 0 d, norm_mk_eq_absS h𝔪, Units.val_mk0,
    Real.mul_rpow (Finset.prod_nonneg fun w _ => by positivity) (absS_nonneg _),
    ← Real.finsetProd_rpow _ _ (fun w _ => by positivity)]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  have hm : w.mult = 2 := by
    rw [InfinitePlace.mult, if_neg]
    exact InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w)
  rw [hm, ← Real.rpow_natCast, ← Real.rpow_mul (apply_nonneg _ _)]
  norm_num

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (g : AllowedGen ι 𝔪)

variable {hG hz6 g}

/-- `τ_Φ(ν) = N(νR)^{1/3}·coef·𝒦_Φ(ν)` with G1's Kirillov function. -/
theorem tau_eq_Kir (hE : ThmE hG hz6 g P) (Φ : GSection ι P 𝔪) (ν : {ν : SInt 𝔪 // ν ≠ 0}) :
    T.tau hG hz6 Φ (ν : SInt 𝔪) =
      (((Ideal.absNorm (H0.rowOf hG.ne_bot g ν).1.1 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
        L3X.coefF' g ⊤ (H0.rowOf hG.ne_bot g ν) *
        G1.Kir hG hz6 (T.theta hG hz6) Φ ((ν : SInt 𝔪) : F) := by
  rw [hE Φ ν, G1.Kir_of_ne hG hz6 _ Φ (H0.coe_ne_zero ν)]
  congr 2
  show S2.actR hG (ν : SInt 𝔪) Φ = _
  rw [S2.actR, dif_neg (H0.coe_ne_zero ν)]

/-- `τ_Φ(ν) = ∏_w |ν|_w^{2/3} · coef^S(ν) · ξ_Φ(ν)`. -/
theorem tau_eq_xi (hE : ThmE hG hz6 g P) (Φ : GSection ι P 𝔪) (ν : {ν : SInt 𝔪 // ν ≠ 0}) :
    T.tau hG hz6 Φ (ν : SInt 𝔪) =
      ((∏ w : InfinitePlace F, w ((ν : SInt 𝔪) : F) ^ (2 / 3 : ℝ) : ℝ) : ℂ) *
        L3X.coefF' g ⊤ (H0.rowOf hG.ne_bot g ν) *
        G1.xi hG hz6 (T.theta hG hz6) Φ ((ν : SInt 𝔪) : F) := by
  rw [tau_eq_Kir hE, absNorm_rowOf_rpow, G1.xi]
  push_cast
  ring

/-- **The coefficient bound.** -/
theorem norm_tau_le_oai (hE : ThmE hG hz6 g P) (Φ : GSection ι P 𝔪) :
    ∃ bf : SFin 𝔪 0 → ℝ, (∀ y, 0 ≤ bf y) ∧
      (∀ σ : ℝ, -(1 / 3 : ℝ) < σ → Summable (fun y : SFin 𝔪 0 => bf y * SFin.norm y ^ σ)) ∧
      ∀ ν : {ν : SInt 𝔪 // ν ≠ 0}, ‖T.tau hG hz6 Φ (ν : SInt 𝔪)‖ ≤
        (∏ w : InfinitePlace F, w ((ν : SInt 𝔪) : F) ^ (2 / 3 : ℝ)) *
          bf (sEmb 𝔪 0 ((ν : SInt 𝔪) : F)).2.2 := by
  have hsm : (T.theta (ι := ι) (P := P) hG hz6).toResFun.SmulOn {s : ℂ | 1 < s.re} := by
    rw [T.theta_toResFun]; exact G1.resFunSlit_smulOn
  obtain ⟨bf, hbf, hsum⟩ := G1.norm_xi_le_bf hG hz6 (T.theta hG hz6) hsm Φ 0
  refine ⟨bf, fun y => ?_, hsum, fun ν => ?_⟩
  · obtain ⟨x, rfl⟩ := L3X.SFin.mk_surjective (𝔪 := 𝔪) (k := 0) y
    exact (norm_nonneg _).trans (hbf x)
  · have hP : 0 ≤ ∏ w : InfinitePlace F, w ((ν : SInt 𝔪) : F) ^ (2 / 3 : ℝ) :=
      Finset.prod_nonneg fun w _ => by positivity
    rw [tau_eq_xi hE, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hP,
      L3X.sEmb_fin (H0.coe_ne_zero ν), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hP
    calc ‖L3X.coefF' g ⊤ (H0.rowOf hG.ne_bot g ν)‖ * ‖G1.xi hG hz6 (T.theta hG hz6) Φ _‖
        ≤ 1 * bf (SFin.mk 𝔪 0 (Units.mk0 _ (H0.coe_ne_zero ν))) :=
          mul_le_mul (H.norm_coefF'_le g ⊤ _) (hbf (Units.mk0 _ (H0.coe_ne_zero ν)))
            (norm_nonneg _) zero_le_one
      _ = _ := one_mul _

end

end ArtinKP.G2a
end

theorem solution.{u_1} : type_of% @ArtinKP.G2a.norm_tau_le_oai.{u_1} := @ArtinKP.G2a.norm_tau_le_oai.{u_1}
