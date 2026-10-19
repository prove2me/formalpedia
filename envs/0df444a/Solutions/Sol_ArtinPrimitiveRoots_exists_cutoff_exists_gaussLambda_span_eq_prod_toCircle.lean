-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_exists_gaussLambda_span_eq_prod_toCircle
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T09:56:25.647154+00:00
-- url     : https://prove2.me/submissions/c8129565-57c8-4339-9a80-86e691c289f4

import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Mathlib

section
section
/-! # L3D_Char: the cubic residue character `ρ_P` with values in `𝓞 K`, `K = ℚ(ω) ⊆ F`

For a maximal ideal `P` of `𝓞 F` with `3 ∣ N P − 1`, `ρ P : MulChar (𝓞 F ⧸ P) (𝓞 K)` is the
character with `ρ(x) ≡ x^{(N P − 1)/3} (mod P)`. It is cubic and nontrivial, and the bundle's
`cubicResidueChar ι P` is `ι ∘ ρ`. -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField

namespace ArtinPrimitiveRoots

namespace L3D

variable {F : Type*} [Field F] [NumberField F] {K : Type*} [Field K] [NumberField K] [Algebra K F]

/-- reduction `𝓞 K → 𝓞 F ⧸ P` -/
noncomputable abbrev red (K : Type*) [Field K] [NumberField K] [Algebra K F] (P : Ideal (𝓞 F)) :
    𝓞 K →+* 𝓞 F ⧸ P :=
  (Ideal.Quotient.mk P).comp (algebraMap (𝓞 K) (𝓞 F))

/-- the standing hypotheses at `P` -/
structure Hyp (P : Ideal (𝓞 F)) [Fintype (𝓞 F ⧸ P)] : Prop where
  max : P.IsMaximal
  ne_bot : P ≠ ⊥
  three : 3 ∣ Fintype.card (𝓞 F ⧸ P) - 1

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 3) {P : Ideal (𝓞 F)} [Fintype (𝓞 F ⧸ P)]

lemma Hyp.card_pos (h : Hyp P) : 1 < Fintype.card (𝓞 F ⧸ P) := by
  haveI := h.max
  letI := Ideal.Quotient.field P
  exact Fintype.one_lt_card

lemma Hyp.card_eq (h : Hyp P) : Fintype.card (𝓞 F ⧸ P) = Ideal.absNorm P := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

/-- `m = (N P − 1)/3`. -/
noncomputable abbrev expo (P : Ideal (𝓞 F)) [Fintype (𝓞 F ⧸ P)] : ℕ :=
  (Fintype.card (𝓞 F ⧸ P) - 1) / 3

lemma Hyp.three_mul (h : Hyp P) : 3 * expo P = Fintype.card (𝓞 F ⧸ P) - 1 :=
  Nat.mul_div_cancel' h.three

lemma Hyp.expo_pos (h : Hyp P) : 0 < expo P := by
  have := h.three_mul; have := h.card_pos
  obtain ⟨k, hk⟩ := h.three
  omega

lemma Hyp.coprime (h : Hyp P) : (Ideal.absNorm P).Coprime 3 := by
  rw [← h.card_eq]
  have := h.three_mul; have := h.card_pos
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  omega

include hζ in
lemma eta_prim : IsPrimitiveRoot hζ.toInteger 3 := hζ.toInteger_isPrimitiveRoot

include hζ in
lemma etaF_prim : IsPrimitiveRoot (algebraMap (𝓞 K) (𝓞 F) hζ.toInteger) 3 :=
  (eta_prim hζ).map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 F))

include hζ in
lemma red_prim (h : Hyp P) : IsPrimitiveRoot (red K P hζ.toInteger) 3 := by
  have h1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact h.max.ne_top
  exact (etaF_prim hζ).idealQuotient_mk h1 h.coprime

include hζ in
/-- cube roots of unity in `𝓞 F` are determined by their residues mod `P` -/
lemma cube_root_inj (h : Hyp P) {a b : 𝓞 F} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : Ideal.Quotient.mk P a = Ideal.Quotient.mk P b) : a = b := by
  obtain ⟨i, hi, rfl⟩ := (etaF_prim hζ).eq_pow_of_pow_eq_one ha
  obtain ⟨k, hk, rfl⟩ := (etaF_prim hζ).eq_pow_of_pow_eq_one hb
  have hp := red_prim hζ h
  simp only [map_pow] at hab
  rw [hp.pow_inj hi hk hab]

/-- the reduction on cube roots of unity -/
noncomputable abbrev redRoots (P : Ideal (𝓞 F)) : rootsOfUnity 3 (𝓞 K) →* rootsOfUnity 3 (𝓞 F ⧸ P) :=
  restrictRootsOfUnity (red K P) 3

include hζ in
lemma redRoots_bijective (h : Hyp P) : Function.Bijective (redRoots (K := K) P) := by
  have hp := red_prim hζ h
  have he := eta_prim hζ
  have hinj : Function.Injective (redRoots (K := K) P) := by
    intro a b hab
    have ha : (a : (𝓞 K)ˣ).val ^ 3 = 1 := by
      have := (mem_rootsOfUnity 3 (a : (𝓞 K)ˣ)).mp a.2
      rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
    have hb : (b : (𝓞 K)ˣ).val ^ 3 = 1 := by
      have := (mem_rootsOfUnity 3 (b : (𝓞 K)ˣ)).mp b.2
      rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
    obtain ⟨i, hi, hi'⟩ := he.eq_pow_of_pow_eq_one ha
    obtain ⟨k, hk, hk'⟩ := he.eq_pow_of_pow_eq_one hb
    have hab' := congrArg (fun z : rootsOfUnity 3 (𝓞 F ⧸ P) => ((z : (𝓞 F ⧸ P)ˣ) : 𝓞 F ⧸ P)) hab
    simp only [restrictRootsOfUnity_coe_apply] at hab'
    rw [← hi', ← hk', map_pow, map_pow] at hab'
    have hik := hp.pow_inj hi hk hab'
    apply Subtype.ext; apply Units.ext
    rw [← hi', ← hk', hik]
  haveI : NeZero 3 := ⟨by norm_num⟩
  refine hinj.bijective_of_nat_card_le ?_
  haveI := h.max
  letI := Ideal.Quotient.field P
  rw [he.card_rootsOfUnity]
  exact card_rootsOfUnity _ 3

/-- `x ↦ x^m` into the cube roots of unity -/
noncomputable def powRoots (h : Hyp P) : (𝓞 F ⧸ P)ˣ →* rootsOfUnity 3 (𝓞 F ⧸ P) :=
  (powMonoidHom (expo P)).codRestrict (rootsOfUnity 3 (𝓞 F ⧸ P)) fun x => by
    classical
    rw [mem_rootsOfUnity, powMonoidHom_apply, ← pow_mul, mul_comm, h.three_mul]
    have : Fintype.card (𝓞 F ⧸ P)ˣ = Fintype.card (𝓞 F ⧸ P) - 1 := by
      haveI := h.max
      letI := Ideal.Quotient.field P
      convert Fintype.card_units (α := 𝓞 F ⧸ P)
    rw [← this]
    exact pow_card_eq_one

/-- the cubic residue character with values in `𝓞 K` -/
noncomputable def rho (h : Hyp P) : MulChar (𝓞 F ⧸ P) (𝓞 K) :=
  MulChar.ofUnitHom <| (Subgroup.subtype _).comp <|
    ((MulEquiv.ofBijective _ (redRoots_bijective hζ h)).symm.toMonoidHom).comp (powRoots h)

lemma rho_unit (h : Hyp P) (u : (𝓞 F ⧸ P)ˣ) :
    red K P (rho hζ h u) = (u : 𝓞 F ⧸ P) ^ expo P := by
  rw [rho, MulChar.ofUnitHom_coe]
  set r := (MulEquiv.ofBijective _ (redRoots_bijective hζ h)).symm (powRoots h u)
  have hr : redRoots (K := K) P r = powRoots h u :=
    (MulEquiv.ofBijective _ (redRoots_bijective hζ h)).apply_symm_apply _
  have := congrArg (fun z : rootsOfUnity 3 (𝓞 F ⧸ P) => ((z : (𝓞 F ⧸ P)ˣ) : 𝓞 F ⧸ P)) hr
  simp only [restrictRootsOfUnity_coe_apply] at this
  simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
    MulEquiv.coe_toMonoidHom]
  rw [this]
  simp [powRoots]

lemma rho_spec (h : Hyp P) (x : 𝓞 F ⧸ P) : red K P (rho hζ h x) = x ^ expo P := by
  haveI := h.max
  letI := Ideal.Quotient.field P
  by_cases hx : x = 0
  · subst hx
    rw [MulChar.map_zero, map_zero, zero_pow h.expo_pos.ne']
  · exact rho_unit hζ h (Units.mk0 x hx)

lemma rho_cube_unit (h : Hyp P) (u : (𝓞 F ⧸ P)ˣ) : (rho hζ h u) ^ 3 = 1 := by
  rw [rho, MulChar.ofUnitHom_coe]
  set r := (MulEquiv.ofBijective _ (redRoots_bijective hζ h)).symm (powRoots h u)
  have := (mem_rootsOfUnity 3 (r : (𝓞 K)ˣ)).mp r.2
  simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
    MulEquiv.coe_toMonoidHom]
  rw [← Units.val_pow_eq_pow_val, this, Units.val_one]

lemma rho_pow_three (h : Hyp P) : rho hζ h ^ 3 = 1 := by
  ext u
  rw [MulChar.pow_apply_coe, rho_cube_unit, MulChar.one_apply_coe]

lemma rho_ne_one (h : Hyp P) : rho hζ h ≠ 1 := by
  classical
  haveI := h.max
  letI := Ideal.Quotient.field P
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (𝓞 F ⧸ P)ˣ)
  have hord : orderOf g = Fintype.card (𝓞 F ⧸ P) - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
    convert Fintype.card_units (α := 𝓞 F ⧸ P)
  intro h1
  have := rho_unit hζ h g
  rw [h1, MulChar.one_apply_coe, map_one] at this
  have hg1 : g ^ expo P = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, ← this, Units.val_one])
  have hdvd := orderOf_dvd_of_pow_eq_one hg1
  rw [hord] at hdvd
  have := Nat.le_of_dvd h.expo_pos hdvd
  have := h.three_mul
  have := h.expo_pos
  omega

lemma rho_sq_ne_one (h : Hyp P) : rho hζ h ^ 2 ≠ 1 := by
  intro h2
  apply rho_ne_one hζ h
  have h3 := rho_pow_three hζ h
  rw [pow_succ, h2, one_mul] at h3
  exact h3

/-- the bundle's `cubicResidueChar ι P` through `ρ` -/
lemma cubicResidueChar_eq (h : Hyp P) (ι : F →+* ℂ) (x : 𝓞 F ⧸ P) :
    cubicResidueChar ι P x = ι ((algebraMap (𝓞 K) (𝓞 F) (rho hζ h x) : 𝓞 F) : F) := by
  classical
  haveI := h.max
  letI := Ideal.Quotient.field P
  by_cases hx : x = 0
  · subst hx
    simp [cubicResidueChar, MulChar.map_zero]
  have hm : (Ideal.absNorm P - 1) / 3 = expo P := by rw [← h.card_eq]
  have hcube : (algebraMap (𝓞 K) (𝓞 F) (rho hζ h x)) ^ 3 = 1 := by
    rw [← map_pow]
    have := rho_cube_unit hζ h (Units.mk0 x hx)
    rw [Units.val_mk0] at this
    rw [this, map_one]
  have hex : ∃ ω : 𝓞 F, ω ^ 3 = 1 ∧
      Ideal.Quotient.mk P ω = x ^ ((Ideal.absNorm P - 1) / 3) :=
    ⟨_, hcube, by rw [hm, ← rho_spec hζ h x]; rfl⟩
  simp only [cubicResidueChar, if_neg hx, dif_pos hex]
  congr 2
  obtain ⟨k1, k2⟩ := hex.choose_spec
  refine cube_root_inj hζ h k1 hcube ?_
  rw [k2, hm, ← rho_spec hζ h x]; rfl

end L3D

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3D_Jac: the cubic Jacobi sum `j_P = J(ρ, ρ) ∈ 𝓞 K`

* `jac_cong`: `−j_P = 1 + 3 z` (Mathlib's `exists_jacobiSum_eq_neg_one_add`);
* `jac_mul_jacBar`: `j_P · J(ρ², ρ²) = N P` (`jacobiSum_mul_jacobiSum_inv`);
* `cubicJacobiSum_eq`: the bundle's `cubicJacobiSum ι P` is `ι j_P`;
* `iota_jacBar`: `ι J(ρ², ρ²) = conj (ι j_P)`. -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField

namespace ArtinPrimitiveRoots

namespace L3D

variable {F : Type*} [Field F] [NumberField F] {K : Type*} [Field K] [NumberField K] [Algebra K F]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 3) {P : Ideal (𝓞 F)} [Fintype (𝓞 F ⧸ P)]

/-- `j_P = J(ρ, ρ)` -/
noncomputable def jac (h : Hyp P) : 𝓞 K := jacobiSum (rho hζ h) (rho hζ h)

/-- `J(ρ², ρ²)` -/
noncomputable def jacBar (h : Hyp P) : 𝓞 K := jacobiSum (rho hζ h ^ 2) (rho hζ h ^ 2)

include hζ in
lemma eta_sq_add (η : 𝓞 K) (hη : IsPrimitiveRoot η 3) : η ^ 2 + η + 1 = 0 := by
  have h1 : η ^ 3 = 1 := hη.pow_eq_one
  have h2 : η - 1 ≠ 0 := sub_ne_zero.mpr (hη.ne_one (by norm_num))
  have : (η - 1) * (η ^ 2 + η + 1) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h h2
  · exact h

lemma jac_cong (h : Hyp P) : ∃ z : 𝓞 K, -jac hζ h = 1 + 3 * z := by
  classical
  haveI := h.max
  letI := Ideal.Quotient.field P
  have hη := eta_prim hζ
  obtain ⟨z, -, hz⟩ := exists_jacobiSum_eq_neg_one_add (n := 3) (by norm_num)
    (rho_pow_three hζ h) (rho_pow_three hζ h) h.three hη
  refine ⟨z * hζ.toInteger, ?_⟩
  have := eta_sq_add hζ _ hη
  rw [jac, hz]
  linear_combination (-z) * this

lemma rho_inv (h : Hyp P) : (rho hζ h)⁻¹ = rho hζ h ^ 2 := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ', rho_pow_three]

lemma jac_mul_jacBar (h : Hyp P) :
    jac hζ h * jacBar hζ h = (Fintype.card (𝓞 F ⧸ P) : 𝓞 K) := by
  classical
  haveI := h.max
  letI := Ideal.Quotient.field P
  set f := algebraMap (𝓞 K) K
  have hf : Function.Injective f := RingOfIntegers.coe_injective
  set χ := (rho hζ h).ringHomComp f
  have hχ : χ ≠ 1 := (MulChar.ringHomComp_ne_one_iff hf).mpr (rho_ne_one hζ h)
  have hχχ : χ * χ ≠ 1 := by
    rw [← MulChar.ringHomComp_mul, ← sq]
    exact (MulChar.ringHomComp_ne_one_iff hf).mpr (rho_sq_ne_one hζ h)
  have hc : ringChar K ≠ ringChar (𝓞 F ⧸ P) := by
    rw [ringChar.eq_zero]
    exact (CharP.char_is_prime (𝓞 F ⧸ P) (ringChar (𝓞 F ⧸ P))).ne_zero.symm
  have key := jacobiSum_mul_jacobiSum_inv hc hχ hχ hχχ
  apply hf
  rw [map_mul, map_natCast, ← key, jac, jacBar, ← jacobiSum_ringHomComp,
    ← jacobiSum_ringHomComp, ← rho_inv, MulChar.ringHomComp_inv]

lemma cubicJacobiSum_eq (h : Hyp P) (ι : F →+* ℂ) :
    cubicJacobiSum ι P = ι ((algebraMap (𝓞 K) (𝓞 F) (jac hζ h) : 𝓞 F) : F) := by
  rw [cubicJacobiSum, finsum_eq_sum_of_fintype, jac, jacobiSum]
  simp only [map_sum, map_mul]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [cubicResidueChar_eq hζ h, cubicResidueChar_eq hζ h]

lemma conj_of_cube {w : ℂ} (hw : w ^ 3 = 1) : starRingEnd ℂ w = w ^ 2 := by
  have hn : ‖w‖ = 1 := by
    have : ‖w‖ ^ 3 = 1 := by rw [← norm_pow, hw, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp this
  have hm : w * starRingEnd ℂ w = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; norm_num
  linear_combination (-(starRingEnd ℂ w)) * hw + w ^ 2 * hm

lemma iota_rho_cube (h : Hyp P) (ι : F →+* ℂ) (x : 𝓞 F ⧸ P) :
    starRingEnd ℂ (ι ((algebraMap (𝓞 K) (𝓞 F) (rho hζ h x) : 𝓞 F) : F)) =
      ι ((algebraMap (𝓞 K) (𝓞 F) ((rho hζ h ^ 2) x) : 𝓞 F) : F) := by
  haveI := h.max
  letI := Ideal.Quotient.field P
  by_cases hx : x = 0
  · subst hx
    simp [MulChar.map_zero]
  have hc := rho_cube_unit hζ h (Units.mk0 x hx)
  rw [Units.val_mk0] at hc
  rw [MulChar.pow_apply' _ (by norm_num), conj_of_cube]
  · simp [map_pow]
  · rw [← map_pow, ← map_pow, ← map_pow, hc]; simp

lemma iota_jacBar (h : Hyp P) (ι : F →+* ℂ) :
    ι ((algebraMap (𝓞 K) (𝓞 F) (jacBar hζ h) : 𝓞 F) : F) =
      starRingEnd ℂ (ι ((algebraMap (𝓞 K) (𝓞 F) (jac hζ h) : 𝓞 F) : F)) := by
  rw [jac, jacBar, jacobiSum, jacobiSum]
  simp only [map_sum, map_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [iota_rho_cube hζ h, iota_rho_cube hζ h]

/-- `|ι j_P|² = N P` -/
lemma normSq_iota_jac (h : Hyp P) (ι : F →+* ℂ) :
    ι ((algebraMap (𝓞 K) (𝓞 F) (jac hζ h) : 𝓞 F) : F) *
      starRingEnd ℂ (ι ((algebraMap (𝓞 K) (𝓞 F) (jac hζ h) : 𝓞 F) : F)) =
      (Ideal.absNorm P : ℂ) := by
  rw [← iota_jacBar hζ h, ← map_mul, ← map_mul, ← map_mul, jac_mul_jacBar hζ h, h.card_eq]
  simp

end L3D

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3D_Norm: `N_{K/ℚ}(j_P) = N P`, and `J(ρ², ρ²) ∉ P` when `N p = ℓ`

* `absNorm_span_jac`: `N (j_P) = N P` (K has a single, complex, infinite place);
* `red_jacBar`: `J(ρ², ρ²) ≡ −(−1)^m C(2m, m) (mod P)`;
* `not_dvd_choose`: `ℓ ∤ C(2m, m)` for `3m = ℓ^s − 1`, `ℓ ≡ 1 (mod 3)` (Kummer). -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField

namespace ArtinPrimitiveRoots

namespace L3D

variable {F : Type*} [Field F] [NumberField F] {K : Type*} [Field K] [NumberField K] [Algebra K F]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 3) {P : Ideal (𝓞 F)} [Fintype (𝓞 F ⧸ P)]

lemma coe_algebraMap_OK (x : 𝓞 K) :
    ((algebraMap (𝓞 K) (𝓞 F) x : 𝓞 F) : F) = algebraMap K F (x : K) := rfl

section cyc

variable [IsCyclotomicExtension {3} ℚ K]

/-- `|N_{K/ℚ} x| = |τ x|²` for any embedding `τ` of `K = ℚ(ω)`. -/
lemma abs_norm_eq (τ : K →+* ℂ) (x : K) :
    |((Algebra.norm ℚ x : ℚ) : ℝ)| = ‖τ x‖ ^ 2 := by
  classical
  have hr : NumberField.InfinitePlace.nrRealPlaces K = 0 :=
    IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero (n := 3) K (by norm_num)
  set w := NumberField.InfinitePlace.mk τ
  have hw : ¬ w.IsReal := by
    intro hreal
    have : 0 < NumberField.InfinitePlace.nrRealPlaces K :=
      Fintype.card_pos_iff.mpr ⟨⟨w, hreal⟩⟩
    omega
  have hsub : ∀ w' : NumberField.InfinitePlace K, w' = w := by
    intro w'
    have hc : NumberField.InfinitePlace.nrComplexPlaces K = 1 := by
      rw [IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two (n := 3) K]
      decide
    have hw' : ¬ w'.IsReal := by
      intro hreal
      have : 0 < NumberField.InfinitePlace.nrRealPlaces K :=
        Fintype.card_pos_iff.mpr ⟨⟨w', hreal⟩⟩
      omega
    have h1 := Fintype.card_le_one_iff.mp (le_of_eq hc)
      ⟨w', NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw'⟩
      ⟨w, NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw⟩
    exact congrArg Subtype.val h1
  have := NumberField.InfinitePlace.prod_eq_abs_norm x
  rw [Fintype.prod_eq_single w (fun w' hw' => absurd (hsub w') hw'),
    NumberField.InfinitePlace.mult, if_neg hw, NumberField.InfinitePlace.apply] at this
  rw [this, Rat.cast_abs]

lemma absNorm_span_jac (h : Hyp P) (ι : F →+* ℂ) :
    Ideal.absNorm (Ideal.span {jac hζ h}) = Ideal.absNorm P := by
  rw [Ideal.absNorm_span_singleton]
  have h1 := abs_norm_eq (ι.comp (algebraMap K F)) (jac hζ h : K)
  have h2 := normSq_iota_jac hζ h ι
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h2
  rw [RingHom.comp_apply, ← coe_algebraMap_OK] at h1
  have h3 : ((Algebra.norm ℤ (jac hζ h)).natAbs : ℝ) = (Ideal.absNorm P : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, ← Algebra.coe_norm_int] at *
    have : (((Algebra.norm ℤ (jac hζ h) : ℤ) : ℚ) : ℝ) = ((Algebra.norm ℤ (jac hζ h) : ℤ) : ℝ) := by
      push_cast; rfl
    rw [← this, h1]
    exact_mod_cast h2
  exact_mod_cast h3

end cyc

/-- `J(ρ², ρ²)` modulo `P`. -/
lemma red_jacBar (h : Hyp P) :
    red K P (jacBar hζ h) = -((-1) ^ expo P * ((2 * expo P).choose (expo P) : 𝓞 F ⧸ P)) := by
  classical
  haveI := h.max
  letI := Ideal.Quotient.field P
  set m := expo P with hm
  have hm0 := h.expo_pos
  have h3m := h.three_mul
  rw [jacBar, jacobiSum, map_sum]
  have step1 : ∀ x : 𝓞 F ⧸ P, red K P ((rho hζ h ^ 2) x * (rho hζ h ^ 2) (1 - x)) =
      ∑ k ∈ Finset.range (2 * m + 1), ((-1) ^ k * ((2 * m).choose k : 𝓞 F ⧸ P)) * x ^ (2 * m + k) := by
    intro x
    rw [map_mul, MulChar.pow_apply' _ (by norm_num), MulChar.pow_apply' _ (by norm_num), map_pow,
      map_pow, rho_spec, rho_spec, ← pow_mul', ← pow_mul', ← hm, sub_eq_neg_add, add_pow,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [one_pow, mul_one, neg_pow]
    ring
  rw [Finset.sum_congr rfl fun x _ => step1 x, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hsum : ∀ k ∈ Finset.range (2 * m + 1), ∑ x : 𝓞 F ⧸ P, x ^ (2 * m + k) =
      if k = m then -1 else 0 := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hpos : 2 * m + k ≠ 0 := by omega
    have hfull : ∑ x : 𝓞 F ⧸ P, x ^ (2 * m + k) = ∑ x : (𝓞 F ⧸ P)ˣ, ((x : 𝓞 F ⧸ P) ^ (2 * m + k)) := by
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨_, Units.val_injective⟩))]
      · rw [Finset.sum_map]; rfl
      · intro x _ hx
        have : x = 0 := by
          by_contra hx0
          exact hx (Finset.mem_map.mpr ⟨Units.mk0 x hx0, Finset.mem_univ _, rfl⟩)
        rw [this, zero_pow hpos]
    rw [hfull, FiniteField.sum_pow_units]
    congr 1
    apply propext
    constructor
    · rintro ⟨c, hc⟩
      rw [← h3m] at hc
      rcases c with _ | _ | c
      · omega
      · omega
      · nlinarith
    · rintro rfl; exact ⟨1, by omega⟩
  rw [Finset.sum_congr rfl fun k hk => by rw [hsum k hk]]
  simp only [mul_ite, mul_neg, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' (Finset.range (2 * m + 1)) m, if_pos (by rw [Finset.mem_range]; omega)]

/-- No carries: `ℓ ∤ C(2m, m)` when `3m + 1 = ℓ^s`, `ℓ ≡ 1 (mod 3)`. -/
lemma not_dvd_choose {ℓ s m : ℕ} (hℓ : ℓ.Prime) (h3 : ℓ % 3 = 1) (hm : 3 * m + 1 = ℓ ^ s) :
    ¬ ℓ ∣ (2 * m).choose m := by
  haveI := Fact.mk hℓ
  have hne : (2 * m).choose m ≠ 0 := (Nat.choose_pos (by omega)).ne'
  rw [dvd_iff_padicValNat_ne_zero hne]
  intro hdvd
  have hv : padicValNat ℓ ((2 * m).choose m) = 0 := by
    rw [padicValNat_choose (b := Nat.log ℓ (2 * m) + 1) (by omega) (Nat.lt_succ_self _)]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [show 2 * m - m = m by omega, not_le]
    set A := ℓ ^ i with hA
    have hA1 : A % 3 = 1 := by rw [hA, Nat.pow_mod, h3]; simp
    have hApos : 0 < A := pow_pos hℓ.pos _
    have hr := Nat.mod_lt m hApos
    by_cases his : s ≤ i
    · have : ℓ ^ s ≤ A := Nat.pow_le_pow_right hℓ.pos his
      have := Nat.mod_le m A
      omega
    · push Not at his
      obtain ⟨c, hc⟩ : A ∣ ℓ ^ s := pow_dvd_pow ℓ his.le
      have hdm := Nat.div_add_mod m A
      set r := m % A
      set q := m / A
      -- 3 r + 1 = A (c − 3 q)
      have hk : 3 * r + 1 + 3 * (A * q) = A * c := by rw [← hc, ← hm]; omega
      have hcq : 3 * q ≤ c := by
        by_contra hcon
        push Not at hcon
        have : A * c < A * (3 * q) := Nat.mul_lt_mul_of_pos_left hcon hApos
        nlinarith
      obtain ⟨k, hk'⟩ : ∃ k, c = 3 * q + k := ⟨c - 3 * q, by omega⟩
      subst hk'
      have hk2 : 3 * r + 1 = A * k := by nlinarith
      have hk3 : k < 3 := by
        by_contra hcon; push Not at hcon
        have : A * 3 ≤ A * k := Nat.mul_le_mul_left A hcon
        omega
      interval_cases k
      · omega
      · omega
      · have : (A * 2) % 3 = 2 := by rw [Nat.mul_mod, hA1]
        omega
  exact hdvd hv

end L3D

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3D_Stick: `(j_P) = N_{F/K}(P)` as ideals of `𝓞 K`

With `p = P ∩ 𝓞 K`, `relNorm P = p^s` and `N p ∈ {ℓ, ℓ²}`:
* `N p = ℓ²`: `p = (ℓ)` and `(j)(j̄) = p^{2s}`, so `(j) = p^a` and `a = s` by norms;
* `N p = ℓ`: `j̄ ∉ P` (`red_jacBar`, `not_dvd_choose`), so `p^s ∣ (j)` and equality by norms. -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField

namespace ArtinPrimitiveRoots

namespace L3D

variable {F : Type*} [Field F] [NumberField F] {K : Type*} [Field K] [NumberField K] [Algebra K F]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 3) {P : Ideal (𝓞 F)} [Fintype (𝓞 F ⧸ P)]

lemma eq_of_le_of_absNorm_eq {R : Type*} [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R]
    [Module.Finite ℤ R] {I J : Ideal R} (hIJ : J ∣ I) (hn : Ideal.absNorm I = Ideal.absNorm J)
    (h0 : Ideal.absNorm J ≠ 0) : I = J := by
  obtain ⟨C, rfl⟩ := hIJ
  rw [map_mul] at hn
  have : Ideal.absNorm C = 1 := by
    have := (Nat.mul_eq_left h0).mp hn
    exact this
  rw [Ideal.absNorm_eq_one_iff.mp this, Ideal.mul_top]

variable [IsCyclotomicExtension {3} ℚ K]

lemma finrank_OK : Module.finrank ℤ (𝓞 K) = 2 := by
  rw [RingOfIntegers.rank, IsCyclotomicExtension.finrank (n := 3) K
    (Polynomial.cyclotomic.irreducible_rat (n := 3) (by norm_num))]
  decide

theorem span_jac_eq_relNorm (h : Hyp P) (ι : F →+* ℂ) :
    Ideal.span {jac hζ h} = Ideal.relNorm (𝓞 K) P := by
  classical
  haveI := h.max
  letI := Ideal.Quotient.field P
  set p := P.under (𝓞 K) with hp
  haveI : p.IsMaximal := inferInstance
  obtain ⟨s, hs⟩ := Ideal.exists_relNorm_eq_pow_of_isPrime P p
  have hQ : Ideal.absNorm P = Ideal.absNorm p ^ s := by
    rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 F) P, hs, map_pow]
  -- the characteristic
  set ℓ := ringChar (𝓞 F ⧸ P) with hℓdef
  have hℓ : ℓ.Prime := CharP.char_is_prime (𝓞 F ⧸ P) ℓ
  have hℓP : ((ℓ : ℕ) : 𝓞 F) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact ringChar.Nat.cast_ringChar
  have hℓp : ((ℓ : ℕ) : 𝓞 K) ∈ p := by
    rw [hp, Ideal.under, Ideal.mem_comap, map_natCast]; exact hℓP
  have hpdvd : Ideal.absNorm p ∣ ℓ ^ 2 := by
    have := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem p).mpr hℓp)
    rw [Ideal.absNorm_span_singleton, show ((ℓ : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) ℓ by simp,
      Algebra.norm_algebraMap, finrank_OK, Int.natAbs_pow, Int.natAbs_natCast] at this
    exact this
  have hp1 : Ideal.absNorm p ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact Ideal.IsPrime.ne_top inferInstance
  obtain ⟨i, hi2, hpi⟩ := (Nat.dvd_prime_pow hℓ).mp hpdvd
  have hp0 : p ≠ ⊥ := by
    intro h0; rw [h0, Ideal.absNorm_bot] at hpi
    exact (pow_pos hℓ.pos i).ne' hpi.symm
  have hpprime : Prime p := Ideal.prime_of_isPrime hp0 inferInstance
  -- the two Jacobi sums
  set J := Ideal.span {jac hζ h}
  set J' := Ideal.span {jacBar hζ h}
  have hJJ : J * J' = Ideal.span {((Ideal.absNorm P : ℕ) : 𝓞 K)} := by
    rw [Ideal.span_singleton_mul_span_singleton, jac_mul_jacBar, h.card_eq]
  have hJn : Ideal.absNorm J = Ideal.absNorm P := absNorm_span_jac hζ h ι
  have hP0 : Ideal.absNorm P ≠ 0 := by rw [← h.card_eq]; exact Fintype.card_ne_zero
  have hspanℓ : ∀ t : ℕ, Ideal.span {((ℓ ^ t : ℕ) : 𝓞 K)} = Ideal.span {((ℓ : ℕ) : 𝓞 K)} ^ t := by
    intro t; rw [Ideal.span_singleton_pow]; push_cast; rfl
  rw [hs]
  interval_cases i
  · exact absurd (by simpa using hpi) hp1
  · -- `N p = ℓ`: `ℓ ≡ 1 (mod 3)` and `j̄ ∉ P`
    rw [pow_one] at hpi
    have hcop : (Ideal.absNorm p).Coprime 3 := by
      have hc := h.coprime
      rw [hQ] at hc
      rcases Nat.eq_zero_or_pos s with hs0 | hs0
      · rw [hs0, pow_zero] at hQ
        exact absurd hQ (by rw [← h.card_eq]; exact (h.card_pos).ne')
      · exact Nat.Coprime.coprime_dvd_left (dvd_pow_self _ hs0.ne') hc
    have h3ℓ : ℓ % 3 = 1 := by
      have hμ := (eta_prim hζ).idealQuotient_mk hp1 hcop
      haveI : Finite (𝓞 K ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp0
      letI := Ideal.Quotient.field p
      letI : Fintype (𝓞 K ⧸ p) := Fintype.ofFinite _
      have hcard : Fintype.card (𝓞 K ⧸ p) = ℓ := by
        rw [← hpi, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
      have := FiniteField.pow_card_sub_one_eq_one _ (hμ.ne_zero (by norm_num))
      rw [hcard] at this
      have h3 := hμ.dvd_of_pow_eq_one _ this
      have := hℓ.two_le
      omega
    have hQs : Ideal.absNorm P = ℓ ^ s := by rw [hQ, hpi]
    have hnot : ¬ p ∣ J' := by
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      intro hmem
      rw [hp, Ideal.under, Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem] at hmem
      have hr := red_jacBar hζ h
      change red K P (jacBar hζ h) = 0 at hmem
      rw [hmem, eq_comm, neg_eq_zero, mul_eq_zero] at hr
      rcases hr with hr | hr
      · exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero) hr
      · rw [CharP.cast_eq_zero_iff (𝓞 F ⧸ P) ℓ] at hr
        refine not_dvd_choose (s := s) hℓ h3ℓ ?_ hr
        rw [← hQs, ← h.card_eq, h.three_mul]
        have := h.card_pos; omega
    have hdvd : p ^ s ∣ J * J' := by
      rw [hJJ, hQs, hspanℓ]
      exact pow_dvd_pow_of_dvd ((Ideal.dvd_iff_le).mpr
        ((Ideal.span_singleton_le_iff_mem p).mpr hℓp)) s
    have hJ := hpprime.pow_dvd_of_dvd_mul_right s hnot hdvd
    refine eq_of_le_of_absNorm_eq hJ ?_ ?_
    · rw [hJn, map_pow, hQ]
    · rw [map_pow, ← hQ]; exact hP0
  · -- `N p = ℓ²`: `p = (ℓ)`
    have hpℓ : Ideal.span {((ℓ : ℕ) : 𝓞 K)} = p := by
      refine eq_of_le_of_absNorm_eq ((Ideal.dvd_iff_le).mpr
        ((Ideal.span_singleton_le_iff_mem p).mpr hℓp)) ?_ ?_
      · rw [Ideal.absNorm_span_singleton, show ((ℓ : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) ℓ by simp,
          Algebra.norm_algebraMap, finrank_OK, Int.natAbs_pow, Int.natAbs_natCast, hpi]
      · rw [hpi]; exact (pow_pos hℓ.pos 2).ne'
    have hQs : Ideal.absNorm P = ℓ ^ (2 * s) := by rw [hQ, hpi, pow_mul]
    have hdvd : J ∣ p ^ (2 * s) := by
      rw [← hpℓ, ← hspanℓ, ← hQs, ← hJJ]; exact dvd_mul_right _ _
    obtain ⟨a, -, ha⟩ := (dvd_prime_pow hpprime _).mp hdvd
    rw [associated_iff_eq] at ha
    rw [ha] at hJn ⊢
    rw [map_pow, hpi, hQs, ← pow_mul] at hJn
    have hℓ1 : 1 < ℓ := hℓ.one_lt
    have := Nat.pow_right_injective hℓ.two_le hJn
    congr 1
    omega

end L3D

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3D_Cong: congruences modulo `3` in `𝓞 K`, `K = ℚ(ω)`

* `intNorm_cong`: `α ≡ 1 (mod 3 𝓞_F) ⇒ N_{F/K} α ≡ 1 (mod 3 𝓞_K)`;
* `unit_eq_one`: a unit of `𝓞 K` that is `≡ 1 (mod 3)` is `1`. -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField

namespace ArtinPrimitiveRoots

namespace L3D

variable {F : Type*} [Field F] [NumberField F] {K : Type*} [Field K] [NumberField K] [Algebra K F]
variable [IsCyclotomicExtension {3} ℚ K]

lemma intNorm_cong (α : 𝓞 F) (hα : α - 1 ∈ Ideal.span {(3 : 𝓞 F)}) :
    Algebra.intNorm (𝓞 K) (𝓞 F) α - 1 ∈ Ideal.span {(3 : 𝓞 K)} := by
  classical
  haveI : IsPrincipalIdealRing (𝓞 K) := IsCyclotomicExtension.Rat.three_pid K
  haveI : Module.Free (𝓞 K) (𝓞 F) := Module.free_of_finite_type_torsion_free'
  rw [Algebra.intNorm_eq_norm]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hα
  set b := Module.Free.chooseBasis (𝓞 K) (𝓞 F)
  rw [Algebra.norm_eq_matrix_det b, ← Ideal.Quotient.eq, RingHom.map_det]
  have hαc : α = 1 + algebraMap (𝓞 K) (𝓞 F) 3 * c := by
    rw [map_ofNat]; linear_combination -hc
  have hM : (Ideal.Quotient.mk (Ideal.span {(3 : 𝓞 K)})).mapMatrix (Algebra.leftMulMatrix b α) = 1 := by
    rw [hαc, map_add, map_one, map_mul, AlgHom.commutes, map_add, map_one, map_mul]
    have h3 : (Ideal.Quotient.mk (Ideal.span {(3 : 𝓞 K)})).mapMatrix
        (algebraMap (𝓞 K) (Matrix (Module.Free.ChooseBasisIndex (𝓞 K) (𝓞 F))
          (Module.Free.ChooseBasisIndex (𝓞 K) (𝓞 F)) (𝓞 K)) 3) = 0 := by
      rw [Matrix.algebraMap_eq_diagonal, RingHom.mapMatrix_apply, Matrix.diagonal_map (by simp)]
      have : (Ideal.Quotient.mk (Ideal.span {(3 : 𝓞 K)})) 3 = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
      ext i j
      simp [Pi.algebraMap_apply, this, Matrix.diagonal_apply]
    rw [h3, zero_mul, add_zero]
  rw [hM, Matrix.det_one, map_one]

lemma not_isUnit_three : ¬ IsUnit (3 : 𝓞 K) := by
  intro hu
  have := hu.map (Algebra.norm ℤ (S := 𝓞 K))
  rw [show (3 : 𝓞 K) = algebraMap ℤ (𝓞 K) 3 by simp, Algebra.norm_algebraMap, finrank_OK,
    Int.isUnit_iff] at this
  norm_num at this

lemma not_three_dvd_unit {x : 𝓞 K} (hx : IsUnit x) : ¬ (3 : 𝓞 K) ∣ x :=
  fun h => not_isUnit_three (isUnit_of_dvd_unit h hx)

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 3)

include hζ in
lemma not_three_dvd_eta_sub_one : ¬ (3 : 𝓞 K) ∣ hζ.toInteger - 1 := by
  rintro ⟨x, hx⟩
  have hη := eta_prim hζ
  have hsq := eta_sq_add hζ _ hη
  have hu : IsUnit hζ.toInteger := hη.isUnit (by norm_num)
  apply not_three_dvd_unit hu
  -- `(η − 1)² = −3η`, so `−3 η = 9 x²` and `η = −3 x²`
  refine ⟨-x ^ 2, ?_⟩
  have h1 : (hζ.toInteger - 1) ^ 2 = -3 * hζ.toInteger := by linear_combination hsq
  rw [hx] at h1
  have h3 : (3 : 𝓞 K) * (3 * x ^ 2 + hζ.toInteger) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h3 with h | h
  · norm_num at h
  · linear_combination h

include hζ in
lemma unit_eq_one (u : (𝓞 K)ˣ) (hu : (u : 𝓞 K) - 1 ∈ Ideal.span {(3 : 𝓞 K)}) : u = 1 := by
  have hmem := IsCyclotomicExtension.Rat.Three.Units.mem hζ u
  rw [Ideal.mem_span_singleton] at hu
  have hη := eta_prim hζ
  have hsq := eta_sq_add hζ _ hη
  have hηu : IsUnit hζ.toInteger := hη.isUnit (by norm_num)
  have hne := not_three_dvd_eta_sub_one hζ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h
  · exact h
  · exfalso
    rw [h, Units.val_neg, Units.val_one] at hu
    apply not_isUnit_three (K := K)
    obtain ⟨y, hy⟩ := hu
    refine isUnit_of_dvd_one ⟨1 + y, ?_⟩
    linear_combination hy
  · exfalso
    rw [h] at hu
    exact hne hu
  · exfalso
    rw [h, Units.val_neg] at hu
    apply not_three_dvd_unit (hηu.pow 2)
    convert hu using 1
    change hζ.toInteger ^ 2 = -hζ.toInteger - 1
    linear_combination hsq
  · exfalso
    rw [h, Units.val_pow_eq_pow_val] at hu
    apply hne
    have : (hζ.toInteger ^ 2 - 1) = (hζ.toInteger - 1) * (-hζ.toInteger ^ 2) := by
      linear_combination (hζ.toInteger - 1) * hsq
    change (3 : 𝓞 K) ∣ hζ.toInteger ^ 2 - 1 at hu
    rw [this] at hu
    exact (IsUnit.dvd_mul_right (hηu.pow 2).neg).mp hu
  · exfalso
    rw [h, Units.val_neg, Units.val_pow_eq_pow_val] at hu
    apply not_three_dvd_unit hηu
    convert hu using 1
    change hζ.toInteger = -hζ.toInteger ^ 2 - 1
    linear_combination hsq

end L3D

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3D_Glob: `Λ((α)) = ι(N_{F/K} α) / |ι(N_{F/K} α)|` for `α ≡ 1 (mod 3)`

`∏_{P ∣ (α)} (−j_P) = N_{F/K}(α)` exactly in `𝓞 K`: the two sides generate the same ideal
(`span_jac_eq_relNorm`) and are both `≡ 1 (mod 3)`, so their unit ratio is `1`. -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace L3D

variable {F : Type*} [Field F] [NumberField F] {K : Type*} [Field K] [NumberField K] [Algebra K F]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 3)

/-- the primes where `ρ_P` is defined -/
def GoodP (P : Ideal (𝓞 F)) : Prop := P ≠ ⊥ ∧ P.IsMaximal ∧ 3 ∣ Ideal.absNorm P - 1

lemma GoodP.finite {P : Ideal (𝓞 F)} (h : GoodP P) : Finite (𝓞 F ⧸ P) :=
  Ring.HasFiniteQuotients.finiteQuotient h.1

lemma GoodP.hyp {P : Ideal (𝓞 F)} (h : GoodP P) [Fintype (𝓞 F ⧸ P)] : Hyp P := by
  refine ⟨h.2.1, h.1, ?_⟩
  have := h.2.2
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card] at this
  exact this

/-- `−j_P` at good primes, `1` elsewhere -/
noncomputable def jacG (P : Ideal (𝓞 F)) : 𝓞 K := by
  classical
  by_cases h : GoodP P
  · letI : Fintype (𝓞 F ⧸ P) := @Fintype.ofFinite _ h.finite
    exact -jac hζ h.hyp
  · exact 1

lemma jacG_eq {P : Ideal (𝓞 F)} (h : GoodP P) :
    letI : Fintype (𝓞 F ⧸ P) := @Fintype.ofFinite _ h.finite
    jacG hζ P = -jac hζ h.hyp := by
  classical
  simp only [jacG, dif_pos h]

lemma jacG_cong {P : Ideal (𝓞 F)} (h : GoodP P) : ∃ z : 𝓞 K, jacG hζ P = 1 + 3 * z := by
  letI : Fintype (𝓞 F ⧸ P) := @Fintype.ofFinite _ h.finite
  rw [jacG_eq hζ h]
  exact jac_cong hζ h.hyp

lemma iota_jacG {P : Ideal (𝓞 F)} (h : GoodP P) (ι : F →+* ℂ) :
    ι ((algebraMap (𝓞 K) (𝓞 F) (jacG hζ P) : 𝓞 F) : F) = -cubicJacobiSum ι P := by
  letI : Fintype (𝓞 F ⧸ P) := @Fintype.ofFinite _ h.finite
  rw [jacG_eq hζ h, cubicJacobiSum_eq hζ h.hyp ι, map_neg]
  push_cast
  rw [map_neg]

include hζ in
lemma norm_cubicJacobiSum {P : Ideal (𝓞 F)} (h : GoodP P) (ι : F →+* ℂ) :
    ‖cubicJacobiSum ι P‖ = Real.sqrt (Ideal.absNorm P) := by
  letI : Fintype (𝓞 F ⧸ P) := @Fintype.ofFinite _ h.finite
  have h2 := normSq_iota_jac hζ h.hyp ι
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← cubicJacobiSum_eq hζ h.hyp ι] at h2
  have h3 : ‖cubicJacobiSum ι P‖ ^ 2 = (Ideal.absNorm P : ℝ) := by exact_mod_cast h2
  rw [← h3, Real.sqrt_sq (norm_nonneg _)]

variable [IsCyclotomicExtension {3} ℚ K]

lemma span_jacG {P : Ideal (𝓞 F)} (h : GoodP P) (ι : F →+* ℂ) :
    Ideal.span {jacG hζ P} = Ideal.relNorm (𝓞 K) P := by
  letI : Fintype (𝓞 F ⧸ P) := @Fintype.ofFinite _ h.finite
  rw [jacG_eq hζ h, Ideal.span_singleton_neg, span_jac_eq_relNorm hζ h.hyp ι]

lemma span_multiset_prod {R : Type*} [CommRing R] (s : Multiset R) :
    Ideal.span {s.prod} = (s.map fun x => Ideal.span {x}).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [Ideal.span_singleton_one]
  | cons a s ih =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons,
      ← Ideal.span_singleton_mul_span_singleton, ih]

lemma multiset_prod_cong {R : Type*} [CommRing R] (s : Multiset R)
    (hs : ∀ x ∈ s, ∃ z : R, x = 1 + 3 * z) : ∃ z : R, s.prod = 1 + 3 * z := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | cons a s ih =>
    obtain ⟨z, hz⟩ := ih fun x hx => hs x (Multiset.mem_cons_of_mem hx)
    obtain ⟨w, hw⟩ := hs a (Multiset.mem_cons_self _ _)
    exact ⟨w + z + 3 * w * z, by rw [Multiset.prod_cons, hz, hw]; ring⟩

/-- `∏_{P ∣ (α)} (−j_P) = N_{F/K}(α)`. -/
theorem prod_jacG_eq_intNorm (ι : F →+* ℂ) (α : 𝓞 F) (hα0 : α ≠ 0)
    (hα3 : α - 1 ∈ Ideal.span {(3 : 𝓞 F)})
    (hgood : ∀ P ∈ normalizedFactors (Ideal.span {α}), GoodP P) :
    ((normalizedFactors (Ideal.span {α})).map (jacG hζ)).prod = Algebra.intNorm (𝓞 K) (𝓞 F) α := by
  set s := normalizedFactors (Ideal.span {α})
  have hspan0 : Ideal.span {α} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hα0
  have hid : Ideal.span {(s.map (jacG hζ)).prod} =
      Ideal.span {Algebra.intNorm (𝓞 K) (𝓞 F) α} := by
    rw [span_multiset_prod, Multiset.map_map, ← Ideal.relNorm_singleton,
      ← Ideal.prod_normalizedFactors_eq_self hspan0, map_multiset_prod]
    congr 1
    refine Multiset.map_congr rfl fun P hP => ?_
    exact span_jacG hζ (hgood P hP) ι
  obtain ⟨u, hu⟩ := (Ideal.span_singleton_eq_span_singleton.mp hid)
  obtain ⟨z, hz⟩ := multiset_prod_cong (s.map (jacG hζ)) fun x hx => by
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hx
    exact jacG_cong hζ (hgood P hP)
  have hN := intNorm_cong (K := K) α hα3
  rw [← hu, hz, Ideal.mem_span_singleton] at hN
  have hu1 : (u : 𝓞 K) - 1 ∈ Ideal.span {(3 : 𝓞 K)} := by
    rw [Ideal.mem_span_singleton]
    obtain ⟨y, hy⟩ := hN
    exact ⟨y - z * u, by linear_combination hy⟩
  rw [← hu, unit_eq_one hζ u hu1, Units.val_one, mul_one]

lemma prod_aux {ι' : Type*} (s : Multiset ι') (a : ι' → ℂ) (r : ι' → ℝ) :
    (s.map fun P => -(((r P : ℝ) : ℂ)⁻¹ * a P)).prod =
      (s.map fun P => -a P).prod / (((s.map r).prod : ℝ) : ℂ) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons b s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, ih]
    push_cast
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
    ring

include hζ in
/-- `Λ((α)) = ι(N α)/|ι(N α)|`. -/
theorem gaussLambda_eq_norm (ι : F →+* ℂ) (α : 𝓞 F) (hα0 : α ≠ 0)
    (hα3 : α - 1 ∈ Ideal.span {(3 : 𝓞 F)})
    (hgood : ∀ P ∈ normalizedFactors (Ideal.span {α}), GoodP P) :
    gaussLambda ι (Ideal.span {α}) =
      ι ((algebraMap (𝓞 K) (𝓞 F) (Algebra.intNorm (𝓞 K) (𝓞 F) α) : 𝓞 F) : F) /
        ((‖ι ((algebraMap (𝓞 K) (𝓞 F) (Algebra.intNorm (𝓞 K) (𝓞 F) α) : 𝓞 F) : F)‖ : ℝ) : ℂ) := by
  set s := normalizedFactors (Ideal.span {α})
  rw [← prod_jacG_eq_intNorm hζ ι α hα0 hα3 hgood]
  set φ : 𝓞 K →* ℂ := (ι.comp ((algebraMap (𝓞 F) F).comp (algebraMap (𝓞 K) (𝓞 F)))).toMonoidHom
  have hφ : ∀ x, φ x = ι ((algebraMap (𝓞 K) (𝓞 F) x : 𝓞 F) : F) := fun _ => rfl
  rw [← hφ, map_multiset_prod]
  rw [show ‖(Multiset.map φ (Multiset.map (jacG hζ) s)).prod‖ =
      ((Multiset.map φ (Multiset.map (jacG hζ) s)).map norm).prod from
    map_multiset_prod (normHom : ℂ →*₀ ℝ) _]
  rw [Multiset.map_map, Multiset.map_map]
  have h1 : ∀ P ∈ s, (φ ∘ jacG hζ) P = -cubicJacobiSum ι P := fun P hP => by
    rw [Function.comp_apply, hφ, iota_jacG hζ (hgood P hP)]
  have h2 : ∀ P ∈ s, ((norm ∘ φ ∘ jacG hζ) P) = Real.sqrt (Ideal.absNorm P) := fun P hP => by
    rw [Function.comp_apply, h1 P hP, norm_neg, norm_cubicJacobiSum hζ (hgood P hP)]
  rw [Multiset.map_congr rfl h1, Multiset.map_congr rfl h2, gaussLambda]
  exact prod_aux s _ _

end L3D

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3D_Emb: `∏_w toCircle(m_w · arg(w α)) = τ₀(N_{F/K} α) / |τ₀(N_{F/K} α)|`

`K = ℚ(ω) ⊆ F`, `τ₀ = ι|_K`, `m_w = +1` iff `w.embedding ω = ι ω`. The `K`-embeddings `σ : F → ℂ`
(over `τ₀`) are in bijection with the infinite places (`σ ↦ mk σ`), and the `w`-factor is `σ α/|σ α|`. -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField

namespace ArtinPrimitiveRoots

namespace L3D

variable {F : Type*} [Field F] [NumberField F] {K : Type*} [Field K] [NumberField K] [Algebra K F]

/-- the sign `m_w` -/
noncomputable def sgn (ι : F →+* ℂ) (z : F) (w : InfinitePlace F) : ℤ :=
  by classical exact if w.embedding z = ι z then 1 else -1

lemma conj_ne_of_prim {c : ℂ} (hc : IsPrimitiveRoot c 3) : starRingEnd ℂ c ≠ c := by
  intro h
  have hre := Complex.conj_eq_iff_re.mp h
  have h3 : (c.re : ℂ) ^ 3 = 1 := by rw [hre]; exact hc.pow_eq_one
  have h3' : c.re ^ 3 = 1 := by exact_mod_cast h3
  have h1 : c.re = 1 := by
    nlinarith [sq_nonneg (c.re - 1), sq_nonneg (c.re + 1/2)]
  apply hc.ne_one (by norm_num)
  rw [← hre, h1]; simp

lemma toCircle_arg (z : ℂ) (hz : z ≠ 0) :
    ((AddCircle.toCircle (((Complex.arg z : ℝ)) : AddCircle (2 * Real.pi)) : Circle) : ℂ) =
      z / ((‖z‖ : ℝ) : ℂ) := by
  rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
  rw [eq_div_iff hn]
  have := Complex.norm_mul_exp_arg_mul_I z
  rw [show 2 * Real.pi / (2 * Real.pi) * Complex.arg z = Complex.arg z by
    field_simp]
  rw [mul_comm]; exact this

lemma toCircle_neg_arg_conj (z : ℂ) (hz : z ≠ 0) :
    ((AddCircle.toCircle ((-1 : ℤ) • ((Complex.arg (starRingEnd ℂ z) : ℝ) :
      AddCircle (2 * Real.pi))) : Circle) : ℂ) = z / ((‖z‖ : ℝ) : ℂ) := by
  rw [neg_one_zsmul, ← AddCircle.coe_neg, AddCircle.toCircle_apply_mk, Circle.coe_exp]
  have hz' : starRingEnd ℂ z ≠ 0 := by rwa [map_ne_zero]
  have h1 := toCircle_arg (starRingEnd ℂ z) hz'
  rw [AddCircle.toCircle_apply_mk, Circle.coe_exp] at h1
  have h2 := congrArg (starRingEnd ℂ) h1
  rw [← Complex.exp_conj, map_div₀, Complex.conj_conj, Complex.conj_ofReal, Complex.norm_conj] at h2
  rw [← h2]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 3) (ι : F →+* ℂ)

include hζ in
lemma no_real (w : InfinitePlace F) : ¬ w.IsReal := by
  intro hw
  have hr := InfinitePlace.isReal_iff.mp hw
  have hp : IsPrimitiveRoot (w.embedding (algebraMap K F ζ)) 3 :=
    (hζ.map_of_injective (algebraMap K F).injective).map_of_injective w.embedding.injective
  apply conj_ne_of_prim hp
  exact RingHom.congr_fun hr _

variable [IsCyclotomicExtension {3} ℚ K]

include hζ in
theorem prod_toCircle_eq (α : F) (hα : α ≠ 0) :
    ∏ w : InfinitePlace F, ((AddCircle.toCircle (sgn ι (algebraMap K F ζ) w •
        ((Complex.arg (w.embedding α) : ℝ) : AddCircle (2 * Real.pi))) : Circle) : ℂ) =
      ι (algebraMap K F (Algebra.norm K α)) /
        ((‖ι (algebraMap K F (Algebra.norm K α))‖ : ℝ) : ℂ) := by
  classical
  set τ₀ : K →+* ℂ := ι.comp (algebraMap K F)
  letI : Algebra K ℂ := τ₀.toAlgebra
  set ζF := algebraMap K F ζ
  have hτ : ∀ σ : F →ₐ[K] ℂ, σ ζF = ι ζF := fun σ => σ.commutes ζ
  have hpι : IsPrimitiveRoot (ι ζF) 3 :=
    (hζ.map_of_injective (algebraMap K F).injective).map_of_injective ι.injective
  set f : (F →ₐ[K] ℂ) → InfinitePlace F := fun σ => InfinitePlace.mk (σ : F →+* ℂ)
  have hinj : Function.Injective f := by
    intro σ₁ σ₂ h12
    rcases InfinitePlace.mk_eq_iff.mp h12 with h | h
    · exact AlgHom.coe_ringHom_injective h
    · exfalso
      have := RingHom.congr_fun h ζF
      simp only [NumberField.ComplexEmbedding.conjugate_coe_eq, AlgHom.coe_toRingHom] at this
      rw [hτ, hτ] at this
      exact conj_ne_of_prim hpι this
  have hcard : Fintype.card (F →ₐ[K] ℂ) = Fintype.card (InfinitePlace F) := by
    rw [AlgHom.card]
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank (K := F)
    have h0 : InfinitePlace.nrRealPlaces F = 0 :=
      Fintype.card_eq_zero_iff.mpr ⟨fun w => no_real hζ w.1 w.2⟩
    have h2 : Module.finrank ℚ F = 2 * Module.finrank K F := by
      rw [← Module.finrank_mul_finrank ℚ K F, IsCyclotomicExtension.finrank (n := 3) K
        (Polynomial.cyclotomic.irreducible_rat (n := 3) (by norm_num))]
      rw [show Nat.totient 3 = 2 by decide]
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    omega
  have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩
  have hfac : ∀ σ : F →ₐ[K] ℂ,
      ((AddCircle.toCircle (sgn ι ζF (f σ) •
        ((Complex.arg ((f σ).embedding α) : ℝ) : AddCircle (2 * Real.pi))) : Circle) : ℂ) =
        σ α / ((‖σ α‖ : ℝ) : ℂ) := by
    intro σ
    have hσα : σ α ≠ 0 := by rwa [map_ne_zero]
    rcases InfinitePlace.embedding_mk_eq (σ : F →+* ℂ) with h | h
    · have hs : sgn ι ζF (f σ) = 1 := by
        simp only [sgn, f, h, AlgHom.coe_toRingHom, hτ, if_true]
      rw [hs, one_zsmul, show (f σ).embedding α = σ α by simp [f, h]]
      exact toCircle_arg _ hσα
    · have hs : sgn ι ζF (f σ) = -1 := by
        have : ¬ (f σ).embedding ζF = ι ζF := by
          simp only [f, h, NumberField.ComplexEmbedding.conjugate_coe_eq, AlgHom.coe_toRingHom, hτ]
          exact conj_ne_of_prim hpι
        simp only [sgn, this, if_false]
      rw [hs, show (f σ).embedding α = starRingEnd ℂ (σ α) by
        simp [f, h, NumberField.ComplexEmbedding.conjugate_coe_eq]]
      exact toCircle_neg_arg_conj _ hσα
  rw [← Fintype.prod_bijective f hbij _ _ (fun σ => rfl)]
  simp_rw [hfac]
  rw [Finset.prod_div_distrib, ← Complex.ofReal_prod, ← norm_prod,
    ← Algebra.norm_eq_prod_embeddings]
  rfl

end L3D

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3B_Norm: the additive character on `R`, the unit ideal, and `a(1,1,1,1) = 1` -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3B_Unit: `U_S⁶`-invariance of `poissonFactor`, and `u = 1` for the principal class

* `exists_sub_mem_map`: `𝓞/P → R/PR` is onto for `P ∉ S`; hence Fermat in `R/PR`.
* `sexticResidueSymbol_unit_pow_six`: `χ_P(μ⁶ x) = χ_P(x)` when `6 ∣ N P − 1`.
* `poissonFactor_unit_pow_six`: `F(𝔰, 𝔄, μ⁶ h) = F(𝔰, 𝔄, h)` for exterior `𝔰, 𝔄` whose prime
  factors all have `6 ∣ N P − 1`.
* `freqElt_principalFreq`: the principal frequency element is `μ⁶` for an `S`-unit `μ`.
-/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

section residue

variable {𝔪 : Ideal (𝓞 F)}

lemma card_quot (P : Ideal (𝓞 F)) (hP0 : P ≠ ⊥) [Fintype (𝓞 F ⧸ P)] :
    Fintype.card (𝓞 F ⧸ P) = Ideal.absNorm P := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

end residue

section gen

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

end gen

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3B_Good: exterior primes satisfy `6 ∣ N P − 1` once `S` contains the primes above `2, 3` -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

/-- A prime of norm divisible by the rational prime `p` has norm at most `p^[F:ℚ]`. -/
theorem absNorm_le_of_prime_dvd (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 F)) (hP0 : P ≠ ⊥)
    [P.IsMaximal] (hpd : p ∣ Ideal.absNorm P) :
    Ideal.absNorm P ≤ p ^ Module.finrank ℤ (𝓞 F) := by
  let _ := Ideal.Quotient.field P
  have : Finite (𝓞 F ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  let _ : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  have hcard := card_quot P hP0
  obtain ⟨f, hq, hpf⟩ := FiniteField.card (𝓞 F ⧸ P) (ringChar (𝓞 F ⧸ P))
  rw [hcard] at hpf
  rw [hpf] at hpd
  have hpq : p = ringChar (𝓞 F ⧸ P) :=
    (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hpd)
  have hp0 : ((p : ℕ) : 𝓞 F ⧸ P) = 0 := by rw [hpq]; exact ringChar.Nat.cast_ringChar
  have hmem : (p : 𝓞 F) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact hp0
  have hle : Ideal.span {(p : 𝓞 F)} ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hmem
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
  rw [Ideal.absNorm_span_singleton] at hdvd
  have hn : Algebra.norm ℤ (p : 𝓞 F) = (p : ℤ) ^ Module.finrank ℤ (𝓞 F) := by
    rw [show (p : 𝓞 F) = algebraMap ℤ (𝓞 F) p by simp, Algebra.norm_algebraMap]
  rw [hn, Int.natAbs_pow, Int.natAbs_natCast] at hdvd
  exact Nat.le_of_dvd (pow_pos hp.pos _) hdvd

/-- In `ℚ(μ_n)` with `6 ∣ n`, a prime of norm `> 3^[F:ℚ]` has `6 ∣ N P − 1`. -/
theorem six_dvd_absNorm_sub_one (n : ℕ) (hn0 : 0 < n) (hn : 6 ∣ n) [IsCyclotomicExtension {n} ℚ F]
    (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hQ : 3 ^ Module.finrank ℤ (𝓞 F) < Ideal.absNorm P) : 6 ∣ Ideal.absNorm P - 1 := by
  have : P.IsMaximal := hP.isMaximal hP0
  let _ := Ideal.Quotient.field P
  have : Finite (𝓞 F ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  let _ : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  set Q := Ideal.absNorm P
  have hd : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
  have h23 : 2 ^ Module.finrank ℤ (𝓞 F) ≤ 3 ^ Module.finrank ℤ (𝓞 F) :=
    Nat.pow_le_pow_left (by norm_num) _
  have h3le : 3 ≤ 3 ^ Module.finrank ℤ (𝓞 F) := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hd
  have h2 : ¬ 2 ∣ Q := fun h => by
    have := absNorm_le_of_prime_dvd 2 Nat.prime_two P hP0 h; omega
  have h3 : ¬ 3 ∣ Q := fun h => by
    have := absNorm_le_of_prime_dvd 3 Nat.prime_three P hP0 h; omega
  have hcop : Q.Coprime 6 := by
    have c2 : Q.Coprime 2 := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2))
    have c3 : Q.Coprime 3 :=
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3))
    have : (6 : ℕ) = 2 * 3 := by norm_num
    rw [this]; exact Nat.Coprime.mul_right c2 c3
  have : NeZero n := ⟨hn0.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  have hζ6 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ (n / 6)) 6 :=
    hζ.pow hn0 (Nat.div_mul_cancel hn).symm
  have hω : IsPrimitiveRoot hζ6.toInteger 6 := hζ6.toInteger_isPrimitiveRoot
  have hωb : IsPrimitiveRoot (Ideal.Quotient.mk P hζ6.toInteger) 6 :=
    hω.idealQuotient_mk (by omega) hcop
  have h1 : Ideal.Quotient.mk P hζ6.toInteger ^ (Q - 1) = 1 := by
    rw [show Q = Fintype.card (𝓞 F ⧸ P) from (card_quot P hP0).symm]
    exact FiniteField.pow_card_sub_one_eq_one _ (hωb.ne_zero (by norm_num))
  exact (hωb.pow_eq_one_iff_dvd _).mp h1

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3D_Main: CutLam, `Λ((α)) = ∏_w toCircle(m_w arg(w α))` for `α ≡ 1 (mod 𝔪^j)`

`N₀ = 3^[F:ℚ]`; `j` with `𝔪^j ≤ (3)` (every prime over `3` contains `𝔪`); `K = ℚ⟮ω⟯`. -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace L3D

theorem target (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∃ (j : ℕ) (m : InfinitePlace F → ℤ), (∀ w, m w = 1 ∨ m w = -1) ∧
      ∀ α : 𝓞 F, α ≠ 0 → α - 1 ∈ 𝔪 ^ j →
        gaussLambda ι (Ideal.span {α}) =
          ∏ w, ((AddCircle.toCircle (m w • ((Complex.arg (w.embedding (α : F)) : ℝ) :
            AddCircle (2 * Real.pi))) : Circle) : ℂ) := by
  classical
  -- the cube root of unity and `K = ℚ⟮ω⟯`
  have : NeZero n := ⟨hn0.ne'⟩
  have hzeta := IsCyclotomicExtension.zeta_spec n ℚ F
  have h3n : 3 ∣ n := Nat.dvd_trans (by norm_num) hn
  set ζF := IsCyclotomicExtension.zeta n ℚ F ^ (n / 3)
  have hζF : IsPrimitiveRoot ζF 3 := hzeta.pow hn0 (Nat.div_mul_cancel h3n).symm
  set K := IntermediateField.adjoin ℚ {ζF}
  haveI : IsCyclotomicExtension {3} ℚ K := hζF.intermediateField_adjoin_isCyclotomicExtension ℚ
  set ζ : K := ⟨ζF, IntermediateField.mem_adjoin_simple_self ℚ ζF⟩
  have hζζ : algebraMap K F ζ = ζF := rfl
  have hζ : IsPrimitiveRoot ζ 3 :=
    (IsPrimitiveRoot.map_iff_of_injective (algebraMap K F).injective).mp (by rw [hζζ]; exact hζF)
  set d := Module.finrank ℤ (𝓞 F)
  refine ⟨3 ^ d, fun 𝔪 h𝔪0 hsm => ?_⟩
  -- `𝔪^k ≤ (3)`
  have hrad : 𝔪 ≤ (Ideal.span {(3 : 𝓞 F)}).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun Q ⟨hQ3, hQ⟩ => ?_
    have h30 : Ideal.span {(3 : 𝓞 F)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; norm_num
    have hQ0 : Q ≠ ⊥ := fun h => h30 (le_bot_iff.mp (h ▸ hQ3))
    refine hsm Q hQ hQ0 ?_
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le hQ3
    rw [Ideal.absNorm_span_singleton, show (3 : 𝓞 F) = algebraMap ℤ (𝓞 F) 3 by simp,
      Algebra.norm_algebraMap] at hdvd
    have : (3 : ℤ) ^ d = ((3 ^ d : ℕ) : ℤ) := by push_cast; rfl
    rw [this, Int.natAbs_natCast] at hdvd
    exact Nat.le_of_dvd (pow_pos (by norm_num) _) hdvd
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian 𝔪)
  refine ⟨k + 1, sgn ι ζF, fun w => ?_, fun α hα0 hα => ?_⟩
  · unfold sgn; split_ifs <;> simp
  have hα1 : α - 1 ∈ 𝔪 := by
    have : 𝔪 ^ (k + 1) ≤ 𝔪 := Ideal.pow_le_self (by omega)
    exact this hα
  have hα3 : α - 1 ∈ Ideal.span {(3 : 𝓞 F)} :=
    hk (Ideal.pow_le_pow_right (by omega) hα)
  have hgood : ∀ P ∈ normalizedFactors (Ideal.span {α}), GoodP P := by
    intro P hP
    have hPp : P.IsPrime := Ideal.isPrime_of_prime (prime_of_normalized_factor P hP)
    have hP0 : P ≠ ⊥ := ne_zero_of_mem_normalizedFactors hP
    have hαP : α ∈ P := by
      have := dvd_of_mem_normalizedFactors hP
      rw [Ideal.dvd_iff_le] at this
      exact this (Ideal.mem_span_singleton_self α)
    have hbig : 3 ^ d < Ideal.absNorm P := by
      by_contra hcon
      push Not at hcon
      have h𝔪P := hsm P hPp hP0 hcon
      apply hPp.ne_top
      rw [Ideal.eq_top_iff_one]
      have := P.sub_mem hαP (h𝔪P hα1)
      simpa using this
    exact ⟨hP0, hPp.isMaximal hP0,
      Nat.dvd_trans (by norm_num) (C3B.six_dvd_absNorm_sub_one n hn0 (Nat.dvd_trans (by norm_num) hn)
        P hPp hP0 hbig)⟩
  have hαF : (α : F) ≠ 0 := by exact_mod_cast hα0
  have hN : ((Algebra.intNorm (𝓞 K) (𝓞 F) α : 𝓞 K) : K) = Algebra.norm K (α : F) :=
    Algebra.algebraMap_intNorm α
  rw [gaussLambda_eq_norm hζ ι α hα0 hα3 hgood, coe_algebraMap_OK, hN,
    ← hζζ, prod_toCircle_eq hζ ι (α : F) hαF]

end L3D

end ArtinPrimitiveRoots

end
end

section
section
/-! L3D: CutLam (`exists_cutoff_exists_gaussLambda_span_eq_prod_toCircle`), Lemma 3.4's `Λ` on
`α ≡ 1 (mod 𝔪^j)`, sorry-free. Does not import the target stub. -/

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

theorem exists_cutoff_exists_gaussLambda_span_eq_prod_toCircle (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∃ (j : ℕ) (m : InfinitePlace F → ℤ), (∀ w, m w = 1 ∨ m w = -1) ∧
      ∀ α : 𝓞 F, α ≠ 0 → α - 1 ∈ 𝔪 ^ j →
        gaussLambda ι (Ideal.span {α}) =
          ∏ w, ((AddCircle.toCircle (m w • ((Complex.arg (w.embedding (α : F)) : ℝ) :
            AddCircle (2 * Real.pi))) : Circle) : ℂ)
  :=
  L3D.target n hn0 hn F ι

end ArtinPrimitiveRoots

end
end

section
open ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

theorem solution (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∃ (j : ℕ) (m : InfinitePlace F → ℤ), (∀ w, m w = 1 ∨ m w = -1) ∧
      ∀ α : 𝓞 F, α ≠ 0 → α - 1 ∈ 𝔪 ^ j →
        gaussLambda ι (Ideal.span {α}) =
          ∏ w, ((AddCircle.toCircle (m w • ((Complex.arg (w.embedding (α : F)) : ℝ) :
            AddCircle (2 * Real.pi))) : Circle) : ℂ)
  := by
  exact ArtinPrimitiveRoots.exists_cutoff_exists_gaussLambda_span_eq_prod_toCircle n hn0 hn F ι

end
