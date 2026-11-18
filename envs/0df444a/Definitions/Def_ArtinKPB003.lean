-- Prove2me | Definitions.Def_ArtinKPB003
-- name    : ArtinKPB003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T09:28:16.739742+00:00
-- url     : https://prove2.me/theorems/47d827f0-dd49-4fa7-bbe6-f7ab1b486889
-- title:
--   Definitions bundle ArtinKPB003 of the split of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   A definitions bundle of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The declarations and their proofs are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **Contents.** It holds 48 declarations of that development: 3 definitions, 2 inductive types or structures and 43 theorems. The definitions and types are `ArtinKP.FA.PrimeElt`, `ArtinPrimitiveRoots.C3I.Good`, `ArtinPrimitiveRoots.C3I.chi`, `ArtinPrimitiveRoots.C3I.omegaL`, `ArtinPrimitiveRoots.C3I.sexFun`.
--
--   **Sources.** They come from these modules of the development, in whole or in part: `KP.A_Bridge`, `KP.B7_Gauss`, `KP.B7_Link`, `KP.F_Alg_Link`, `KP.F_Alg_Symbol`, `KP.S2_Symbol`, `T12.C3B_Unit`, `T12.C3I_Char`, `T12.C3I_Gauss`, `T12.C3I_HD`, `T12.C3I_Res`.
--
--   **Imports.** It imports the published bundles `Def_ArtinHecke`, `Def_ArtinHeckeLocalCoeff`, `Def_ArtinHeckePoissonLocal`, `Def_ArtinHeckeProbe`, `Def_ArtinHeckeSModel`, `Def_ArtinHeckeTheta`, `Def_DedekindDomain_Completion_BaseChange`, `Def_ExtCitation_LocalLevelResidues`, `Def_IsDedekindDomain_FiniteUnitIdeles`, `Def_IsDedekindDomain_FiniteUnitIdelesOutside`, `Def_LanglandsTunnell_ArtinCoreCTM`, `Def_M4aHerbrand_GenuineDescent`, `Def_M4aHerbrand_IdeleClassVocab`, `Def_M4aHerbrand_SIdeleClassGroup`, `Def_NormIndex_AdmissibleExpOfDegree`, `Def_NumberField_ArchimedeanIdeleModule` and `Def_NumberField_PlaceDecompositionAction`; the bundle `ArtinKPB002` of this split.
--
--   **Imported by** (directly, in this split): the bundle `ArtinKPB017`; the statement `ArtinKP.FB.primeElt_gen_of_good`; the proof of `ArtinKP.FB.primeElt_gen_of_good`.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142; definitions carved from that development

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
import Definitions.Def_ArtinKPB002

section
-- module Solutions.Artin.KP.A_Bridge
attribute [-simp] _root_.ArtinKP.S2.cubicSymbol_sym
/-!
# WP-A: the exterior cubic symbol in terms of the goal's `residueSymbol`

`cubicExt_eq_residueSymbol`: if `𝔞` is an exterior ideal of `𝓞 F` with `𝔞 R = c R`, then
`cubicExt ι 𝔪 d c = residueSymbol ι 𝔪 𝔞 d ^ 2`.

The link is `val_eq_exp_count`: `v(c) = exp (-count v (normalizedFactors 𝔞))` at exterior `v`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots UniqueFactorizationMonoid

noncomputable section

namespace ArtinKP.A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- Elements of `v^n · R` have valuation at most `exp (-n)`. -/
theorem val_le_of_mem_map_pow (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) (n : ℕ)
    {z : SInt 𝔪} (hz : z ∈ (v.asIdeal ^ n).map (algebraMap (𝓞 F) (SInt 𝔪))) :
    v.valuation F (z : F) ≤ WithZero.exp (-(n : ℤ)) := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [coe_algebraMap_sInt, v.valuation_of_algebraMap]
    exact (v.intValuation_le_pow_iff_mem a n).mpr ha
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Subalgebra.coe_add]
    exact le_trans (Valuation.map_add _ _ _) (max_le hx hy)
  | smul a x _ hx =>
    simp only [smul_eq_mul, Subalgebra.coe_mul, map_mul]
    calc v.valuation F (a : F) * v.valuation F (x : F) ≤ 1 * v.valuation F (x : F) :=
          mul_le_mul_left (sInt_val_le_one a v hv) _
      _ ≤ _ := by rw [one_mul]; exact hx

theorem pow_dvd_iff_le_count (v : HeightOneSpectrum (𝓞 F)) {𝔞 : Ideal (𝓞 F)} (h𝔞 : 𝔞 ≠ ⊥)
    (k : ℕ) : v.asIdeal ^ k ∣ 𝔞 ↔ k ≤ (normalizedFactors 𝔞).count v.asIdeal := by
  rw [pow_dvd_iff_le_emultiplicity,
    emultiplicity_eq_count_normalizedFactors v.irreducible h𝔞, normalize_eq, Nat.cast_le]

/-- `v(c) = exp (-v_P(𝔞))` if `c R = 𝔞 R`, at an exterior place `v = P`. -/
theorem val_eq_exp_count (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal)
    {𝔞 : Ideal (𝓞 F)} (h𝔞 : 𝔞 ≠ ⊥) (c : SInt 𝔪)
    (hspan : Ideal.span {c} = 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    v.valuation F (c : F) =
      WithZero.exp (-(((normalizedFactors 𝔞).count v.asIdeal : ℕ) : ℤ)) := by
  set n := (normalizedFactors 𝔞).count v.asIdeal with hn
  have hle : v.valuation F (c : F) ≤ WithZero.exp (-(n : ℤ)) := by
    apply val_le_of_mem_map_pow v hv n
    have hdvd : v.asIdeal ^ n ∣ 𝔞 := (pow_dvd_iff_le_count v h𝔞 n).mpr le_rfl
    have : c ∈ 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
      rw [← hspan]; exact Ideal.subset_span rfl
    exact Ideal.map_mono (Ideal.le_of_dvd hdvd) this
  have hnd : ¬ v.asIdeal ^ (n + 1) ∣ 𝔞 := by
    rw [pow_dvd_iff_le_count v h𝔞]; omega
  obtain ⟨a, ha, hav⟩ : ∃ a ∈ 𝔞, a ∉ v.asIdeal ^ (n + 1) := by
    by_contra hcon
    push Not at hcon
    exact hnd (Ideal.dvd_iff_le.mpr hcon)
  have hmem : algebraMap (𝓞 F) (SInt 𝔪) a ∈ Ideal.span {c} := by
    rw [hspan]; exact Ideal.mem_map_of_mem _ ha
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hmem
  have hval : v.valuation F (algebraMap (𝓞 F) F a) ≤ v.valuation F (c : F) := by
    rw [← coe_algebraMap_sInt (𝔪 := 𝔪), ← hs, Subalgebra.coe_mul, map_mul]
    calc v.valuation F (s : F) * v.valuation F (c : F) ≤ 1 * v.valuation F (c : F) :=
          mul_le_mul_left (sInt_val_le_one s v hv) _
      _ = _ := one_mul _
  have hgt : ¬ v.valuation F (c : F) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := by
    intro hcon
    apply hav
    rw [← v.intValuation_le_pow_iff_mem, ← v.valuation_of_algebraMap (K := F)]
    exact hval.trans hcon
  have hc0 : (c : F) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hgt
    exact hgt zero_le
  rw [val_eq_exp_ordv v hc0, WithZero.exp_le_exp] at hle hgt
  rw [val_eq_exp_ordv v hc0]
  congr 1
  push_cast at hgt
  omega

theorem ne_zero_of_span_eq {𝔞 : Ideal (𝓞 F)} (h𝔞 : 𝔞 ≠ ⊥) (c : SInt 𝔪)
    (hspan : Ideal.span {c} = 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) : (c : F) ≠ 0 := by
  intro h0
  have hc : c = 0 := Subtype.ext h0
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔞
  have : algebraMap (𝓞 F) (SInt 𝔪) a ∈ Ideal.span {c} := by
    rw [hspan]; exact Ideal.mem_map_of_mem _ ha
  rw [hc, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at this
  have h' := congrArg (fun z : SInt 𝔪 => (z : F)) this
  simp only [coe_algebraMap_sInt, ZeroMemClass.coe_zero] at h'
  exact ha0 (FaithfulSMul.algebraMap_injective (𝓞 F) F (by simpa using h'))

/-- The exterior cubic symbol is the square of the goal's `residueSymbol`:
`(d/c) = χ_𝔞(d)^2` whenever `𝔞` is exterior with `𝔞 R = c R`. -/
theorem cubicExt_eq_residueSymbol (ι : F →+* ℂ) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    (c d : SInt 𝔪) (hspan : Ideal.span {c} = 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    cubicExt ι 𝔪 d c = residueSymbol ι 𝔪 𝔞 d ^ 2 := by
  classical
  have hc0 : (c : F) ≠ 0 := ne_zero_of_span_eq h𝔞.1 c hspan
  -- prime factors of `𝔞` are exterior
  have hext : ∀ Q ∈ normalizedFactors 𝔞, ¬ 𝔪 ≤ Q := by
    intro Q hQ hle
    have hQp : Prime Q := prime_of_normalized_factor Q hQ
    have h1 : 𝔞 ≤ Q := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hQ)
    have : (⊤ : Ideal (𝓞 F)) ≤ Q := by rw [← h𝔞.2]; exact sup_le h1 hle
    exact (Ideal.isPrime_of_prime hQp).ne_top (top_le_iff.mp this)
  have himg : (CubicPkg.extSupp 𝔪 (c : F)).image (fun v => v.asIdeal)
      = (normalizedFactors 𝔞).toFinset := by
    ext Q
    simp only [Finset.mem_image, Multiset.mem_toFinset]
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨hve, hne⟩ := (CubicPkg.mem_extSupp hc0 v).mp hv
      rw [← Multiset.count_ne_zero]
      intro h0
      apply hne
      rw [val_eq_exp_count v hve h𝔞.1 c hspan, h0]
      simp
    · intro hQ
      have hQp : Prime Q := prime_of_normalized_factor Q hQ
      let v : HeightOneSpectrum (𝓞 F) := ⟨Q, Ideal.isPrime_of_prime hQp, hQp.ne_zero⟩
      refine ⟨v, (CubicPkg.mem_extSupp hc0 v).mpr ⟨hext Q hQ, ?_⟩, rfl⟩
      rw [val_eq_exp_count v (hext Q hQ) h𝔞.1 c hspan]
      have : 0 < (normalizedFactors 𝔞).count v.asIdeal := Multiset.count_pos.mpr hQ
      rw [Ne, WithZero.exp_eq_one]
      omega
  rw [residueSymbol, Finset.prod_multiset_map_count, ← himg,
    Finset.prod_image (fun v _ w _ h => HeightOneSpectrum.ext h), ← Finset.prod_pow, cubicExt]
  refine Finset.prod_congr rfl fun v hv => ?_
  obtain ⟨hve, hne⟩ := (CubicPkg.mem_extSupp hc0 v).mp hv
  have hval := val_eq_exp_count v hve h𝔞.1 c hspan
  have hord : ordv v (c : F) = ((normalizedFactors 𝔞).count v.asIdeal : ℕ) := by
    rw [val_eq_exp_ordv v hc0, WithZero.exp_inj] at hval
    omega
  rw [hord, Int.toNat_natCast, ← pow_mul, mul_comm]

end ArtinKP.A
end
end

section
-- module Solutions.Artin.KP.B7_Gauss
/-! # B7_Gauss: the cubic Gauss sum `g(ν, c)` over a ring of `S`-integers, abstractly

`R` is a domain with fraction-type field `K` (in the application `R = SInt 𝔪`, `K = F`).

* `CubicSymbol R` is the interface to WP-A: the cubic exterior symbol `(d/c)`, with exactly the
  properties used here.
* `AddData R K` is an additive character of `K` trivial on `R` (in the application `sAddChar 𝔪`,
  see `B7_Link`).
* `gauss S A ν c = ∑_{d mod c} (d/c)⁻¹ e(ν d / c)` (terms with `(d, c) ≠ 1` vanish since
  `(d/c) = 0` there and `0⁻¹ = 0`).

Main results (MATH.md (B7)): `gauss_mul` (twisted multiplicativity), `gauss_mul_left`
(`g(μν, c) = (μ/c) g(ν, c)`), the prime-power table `gauss_prime_pow_le`,
`gauss_prime_pow_succ`, `gauss_prime_pow_eq_zero`, and the constant-term sums `csum_eq_phi`,
`csum_eq_zero`, `csum_of_cube`, `csum_eq_zero_of_val`, `csum_prime_pow`, `phi_prime_pow`.
-/

set_option linter.unusedSectionVars false

namespace ArtinKP.B7

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]

/-! ### The additive character on fractions -/

/-! ### Elementary facts about the symbol -/

/-! ### The Gauss sum -/

variable (S : CubicSymbol R) (A : AddData R K)

/-! ### Constant-term sums -/

/-! ### Prime powers -/

section prime

variable {π : R} (hπ : π ≠ 0) (hmax : (Ideal.span {π}).IsMaximal)
  (hfin : ∀ k : ℕ, Finite (R ⧸ Ideal.span {π ^ k}))

include hmax in
lemma isCoprime_iff_not_dvd (d : R) : IsCoprime d π ↔ ¬ π ∣ d := by
  constructor
  · rintro ⟨a, b, hab⟩ ⟨r, rfl⟩
    apply hmax.ne_top
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_singleton]
    exact ⟨a * r + b, by linear_combination -hab⟩
  · intro hd
    have hd' : d ∉ Ideal.span {π} := by rwa [Ideal.mem_span_singleton]
    obtain ⟨y, i, hi, hyi⟩ := hmax.exists_inv hd'
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.1 hi
    exact ⟨y, r, by linear_combination hyi⟩

end prime

end ArtinKP.B7
end

section
-- module Solutions.Artin.T12.C3B_Unit
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

lemma coe_algebraMap_SInt (x : 𝓞 F) :
    ((algebraMap (𝓞 F) (SInt 𝔪) x : SInt 𝔪) : F) = (x : F) := rfl

end residue

section gen

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

lemma gen_ne_zero (g : AllowedGen ι 𝔪) (I : Ideal (𝓞 F)) (hI : IsExterior 𝔪 I) :
    ((g.gen I : SInt 𝔪) : F) ≠ 0 := by
  intro h0
  have h0' : g.gen I = 0 := Subtype.ext h0
  have hs := g.span_gen I hI
  rw [h0', Ideal.span_singleton_eq_bot.mpr rfl] at hs
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI.1
  have : algebraMap (𝓞 F) (SInt 𝔪) a ∈ I.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
    Ideal.mem_map_of_mem _ ha
  rw [← hs, Ideal.mem_bot] at this
  apply ha0
  have := congrArg (fun z : SInt 𝔪 => (z : F)) this
  simp only [coe_algebraMap_SInt, ZeroMemClass.coe_zero] at this
  exact_mod_cast this

end gen

end C3B

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.C3I_Res
/-! # C3I_Res: the residue rings `R / P^j R` at a prime `P ∉ S`

For a height-one prime `v` of `𝓞 F` outside `S = placesOf 𝔪`:
* `mem_map_pow_iff`: `r ∈ v^j R ↔ v(r) ≤ exp(-j)` for `r ∈ R`;
* `quotEquiv`: `𝓞/v^j ≃+* R/v^j R`; `natCard_quot`: `#(R/v^j R) = N(v)^j`;
* `isMaximal_map`: `v R` is maximal;
* `finsum_quot_fibre`: summing a function that only depends on the class mod `v^i R`
  over `R/v^j R` (`i ≤ j`) gives `N(v)^(j-i)` times the sum over `R/v^i R`.
-/

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

section quot

variable {v : HeightOneSpectrum (𝓞 F)}

lemma finite_quot (hv : v ∉ placesOf 𝔪) (j : ℕ) :
    Finite (SInt 𝔪 ⧸ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  have : Finite (𝓞 F ⧸ v.asIdeal ^ j) :=
    Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero _ v.ne_bot)
  exact Finite.of_equiv _ (quotEquiv hv j).toEquiv

lemma natCard_quot (hv : v ∉ placesOf 𝔪) (j : ℕ) :
    Nat.card (SInt 𝔪 ⧸ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪))) =
      Ideal.absNorm v.asIdeal ^ j := by
  rw [← Nat.card_congr (quotEquiv hv j).toEquiv, ← map_pow, Ideal.absNorm_apply,
    Submodule.cardQuot_apply]

end quot

end C3I

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.C3I_Char
/-! # C3I_Char: `χ_P` as a multiplicative character and `x ↦ e(x/π)` as a primitive additive
character of the residue field `L = R / P R`

Standing hypotheses `Good 𝔪 v`: `v` coprime to `𝔪`, `12 ∣ N v − 1`, `v ∤ 𝔇`; and a primitive
sixth root of unity `ω ∈ 𝓞`.

* `chi`: `MulChar L ℂ` with `chi (mk x) = sexticResidueSymbol ι 𝔪 v x`; `chi_neg_one`,
  `chi_pow_six`, `chi_pow_ne_one` (`6 ∤ j`), `chi_cube_eq` (`χ³` is the quadratic character).
* `psi`: `AddChar L ℂ` with `psi (mk x) = e(x / gen P)`; `psi_isPrimitive`.
* `cubicResidueChar_eq`: `ρ_P(x) = χ(x)²` through `𝓞/P ≃ L`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- The standing hypotheses at the prime `v`. -/
structure Good (𝔪 : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) : Prop where
  cop : v.asIdeal ⊔ 𝔪 = ⊤
  twelve : 12 ∣ Ideal.absNorm v.asIdeal - 1
  diff : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal

variable {v : HeightOneSpectrum (𝓞 F)}

lemma Good.notS (h : Good 𝔪 v) : v ∉ placesOf 𝔪 := fun hv =>
  v.isPrime.ne_top (eq_top_iff.2 (h.cop ▸ sup_le le_rfl hv))

lemma Good.ext (h : Good 𝔪 v) : IsExterior 𝔪 v.asIdeal := ⟨v.ne_bot, h.cop⟩

lemma absNorm_ne_one (v : HeightOneSpectrum (𝓞 F)) : Ideal.absNorm v.asIdeal ≠ 1 := by
  rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top

lemma absNorm_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < Ideal.absNorm v.asIdeal := by
  rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot

lemma Good.coprime_six (h : Good 𝔪 v) : (Ideal.absNorm v.asIdeal).Coprime 6 := by
  have h1 := absNorm_pos v
  obtain ⟨k, hk⟩ := h.twelve
  have : Ideal.absNorm v.asIdeal = 12 * k + 1 := by omega
  rw [this, Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, show (12 * k + 1) % 6 = 1 by omega,
    Nat.gcd_one_left]

lemma isMaximal_v (h : Good 𝔪 v) : (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))).IsMaximal :=
  isMaximal_map h.notS

lemma finite_L (h : Good 𝔪 v) : Finite (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  have := finite_quot (𝔪 := 𝔪) h.notS 1
  rwa [pow_one] at this

lemma natCard_L (h : Good 𝔪 v) :
    Nat.card (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) = Ideal.absNorm v.asIdeal := by
  have := natCard_quot (𝔪 := 𝔪) h.notS 1
  rwa [pow_one, pow_one] at this

lemma quotHom_bijective_one (h : v ∉ placesOf 𝔪) :
    Function.Bijective (quotHom 𝔪 v.asIdeal) := by
  have := quotHom_bijective (𝔪 := 𝔪) h 1
  rwa [pow_one] at this

/-! ### The sixth roots of unity -/

section roots

variable (ι : F →+* ℂ)

/-- Choice-free value of a root of unity: if `f ζ = f ω ^ i` then `ι ζ = ι ω ^ i`. -/
lemma iota_eq_pow_of_map {K : Type*} [CommRing K] [IsDomain K] (f : 𝓞 F →+* K) {m : ℕ}
    (hm : 0 < m) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω m) (hωf : IsPrimitiveRoot (f ω) m)
    {ζ : 𝓞 F} (hζ : ζ ^ m = 1) {i : ℕ} (h : f ζ = f ω ^ i) : ι (ζ : F) = ι (ω : F) ^ i := by
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨j, hj, rfl⟩ := hω.eq_pow_of_pow_eq_one hζ
  have hpow : ∀ (z : K) (hz : z ^ m = 1) (n : ℕ), z ^ n = z ^ (n % m) := by
    intro z hz n
    conv_lhs => rw [← Nat.div_add_mod n m, pow_add, pow_mul, hz, one_pow, one_mul]
  have hpowC : ∀ (z : ℂ) (hz : z ^ m = 1) (n : ℕ), z ^ n = z ^ (n % m) := by
    intro z hz n
    conv_lhs => rw [← Nat.div_add_mod n m, pow_add, pow_mul, hz, one_pow, one_mul]
  have h1 : f ω ^ j = f ω ^ (i % m) := by
    rw [← map_pow, h, hpow _ hωf.pow_eq_one]
  have hji : j = i % m := hωf.pow_inj hj (Nat.mod_lt _ hm) h1
  have hιω : ι (ω : F) ^ m = 1 := by
    rw [← map_pow, ← map_pow (algebraMap (𝓞 F) F), hω.pow_eq_one, map_one, map_one]
  rw [show ((ω ^ j : 𝓞 F) : F) = (ω : F) ^ j from map_pow (algebraMap (𝓞 F) F) ω j, map_pow, hji,
    ← hpowC _ hιω]

end roots

section chi

/-- The function underlying `sexticResidueSymbol` on `L = R / P R`. -/
noncomputable def sexFun (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) (y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) : ℂ := by
  classical
  exact if y = 0 then 0 else
    if h : ∃ ζ : 𝓞 F, ζ ^ 6 = 1 ∧
        Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
          (algebraMap (𝓞 F) (SInt 𝔪) ζ) = y ^ ((Ideal.absNorm v.asIdeal - 1) / 6)
    then ι (h.choose : F) else 0

lemma sexticResidueSymbol_eq (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F))
    (x : SInt 𝔪) :
    sexticResidueSymbol ι 𝔪 v.asIdeal x =
      sexFun ι 𝔪 v (Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) x) := by
  unfold sexticResidueSymbol sexFun
  congr 1

variable {ι : F →+* ℂ}

/-- The image of `ω` in `L`. -/
noncomputable abbrev omegaL (ω : 𝓞 F) : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
  Ideal.Quotient.mk _ (algebraMap (𝓞 F) (SInt 𝔪) ω)

lemma omegaL_prim (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) :
    IsPrimitiveRoot (omegaL (𝔪 := 𝔪) (v := v) ω) 6 := by
  have h1 : IsPrimitiveRoot (Ideal.Quotient.mk v.asIdeal ω) 6 :=
    hω.idealQuotient_mk (absNorm_ne_one v) h.coprime_six
  have h2 := h1.map_of_injective (quotHom_bijective_one (𝔪 := 𝔪) h.notS).1
  exact h2

lemma pow_card_sub_one_L (h : Good 𝔪 v)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) :
    y ^ (Ideal.absNorm v.asIdeal - 1) = 1 := by
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  haveI := finite_L h
  letI := Fintype.ofFinite (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  rw [← natCard_L h, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card_sub_one_eq_one y hy

lemma six_mul_e (h : Good 𝔪 v) :
    6 * ((Ideal.absNorm v.asIdeal - 1) / 6) = Ideal.absNorm v.asIdeal - 1 :=
  Nat.mul_div_cancel' ((Nat.dvd_trans (by norm_num) h.twelve))

/-- Every nonzero `y ∈ L` has `y^e` a power of `ω`. -/
lemma exists_pow_e (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) :
    ∃ i : ℕ, i < 6 ∧ y ^ ((Ideal.absNorm v.asIdeal - 1) / 6) = omegaL ω ^ i := by
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have h6 : (y ^ ((Ideal.absNorm v.asIdeal - 1) / 6)) ^ 6 = 1 := by
    rw [← pow_mul, mul_comm, six_mul_e h, pow_card_sub_one_L h hy]
  obtain ⟨i, hi, hi'⟩ := (omegaL_prim h hω).eq_pow_of_pow_eq_one h6
  exact ⟨i, hi, hi'.symm⟩

lemma sexFun_eq_pow (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) {i : ℕ}
    (hi : y ^ ((Ideal.absNorm v.asIdeal - 1) / 6) = omegaL ω ^ i) :
    sexFun ι 𝔪 v y = ι (ω : F) ^ i := by
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have hex : ∃ ζ : 𝓞 F, ζ ^ 6 = 1 ∧
      Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
        (algebraMap (𝓞 F) (SInt 𝔪) ζ) = y ^ ((Ideal.absNorm v.asIdeal - 1) / 6) :=
    ⟨ω ^ i, by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow], by
      rw [map_pow, map_pow, hi]⟩
  classical
  unfold sexFun
  rw [if_neg hy, dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  set f : 𝓞 F →+* SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
    (Ideal.Quotient.mk _).comp (algebraMap (𝓞 F) (SInt 𝔪))
  exact iota_eq_pow_of_map ι f (by norm_num) hω (omegaL_prim h hω) h1 (by
    change Ideal.Quotient.mk _ (algebraMap (𝓞 F) (SInt 𝔪) hex.choose) = omegaL ω ^ i
    rw [h2, hi])

lemma sexFun_zero : sexFun ι 𝔪 v (0 : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) = 0 := by
  classical
  unfold sexFun; rw [if_pos rfl]

lemma iota_omega_prim {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) : IsPrimitiveRoot (ι (ω : F)) 6 :=
  (hω.map_of_injective RingOfIntegers.coe_injective).map_of_injective ι.injective

/-- `χ_P` as a multiplicative character of `L`. -/
noncomputable def chi (ι : F →+* ℂ) (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) :
    MulChar (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ℂ where
  toFun := sexFun ι 𝔪 v
  map_one' := by
    haveI := isMaximal_v h
    letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    rw [sexFun_eq_pow h hω one_ne_zero (i := 0) (by rw [one_pow, pow_zero])]
    simp
  map_mul' := by
    haveI := isMaximal_v h
    letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    intro x y
    by_cases hx : x = 0
    · simp [hx, sexFun_zero]
    by_cases hy : y = 0
    · simp [hy, sexFun_zero]
    obtain ⟨i, -, hi⟩ := exists_pow_e h hω hx
    obtain ⟨j, -, hj⟩ := exists_pow_e h hω hy
    rw [sexFun_eq_pow h hω hx hi, sexFun_eq_pow h hω hy hj,
      sexFun_eq_pow h hω (mul_ne_zero hx hy) (i := i + j) (by rw [mul_pow, hi, hj, pow_add]),
      pow_add]
  map_nonunit' := by
    haveI := isMaximal_v h
    letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    intro a ha
    have : a = 0 := by
      by_contra h'
      exact ha (Ne.isUnit h')
    rw [this]; exact sexFun_zero

lemma chi_mk (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (x : SInt 𝔪) :
    chi ι h hω (Ideal.Quotient.mk _ x) = sexticResidueSymbol ι 𝔪 v.asIdeal x :=
  (sexticResidueSymbol_eq ι 𝔪 v x).symm

lemma chi_eq_pow (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) {i : ℕ}
    (hi : y ^ ((Ideal.absNorm v.asIdeal - 1) / 6) = omegaL ω ^ i) :
    chi ι h hω y = ι (ω : F) ^ i :=
  sexFun_eq_pow h hω hy hi

/-- `χ` has exact order `6`: `χ^j ≠ 1` unless `6 ∣ j`. -/
lemma chi_pow_ne_one (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) {j : ℕ}
    (hj : ¬ 6 ∣ j) : chi ι h hω ^ j ≠ 1 := by
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  haveI := finite_L h
  letI := Fintype.ofFinite (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  set Q := Ideal.absNorm v.asIdeal
  set e := (Q - 1) / 6
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := (SInt 𝔪 ⧸ v.asIdeal.map
    (algebraMap (𝓞 F) (SInt 𝔪)))ˣ)
  have hog : orderOf γ = Q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, Nat.card_units, natCard_L h]
  obtain ⟨i, hi6, hi⟩ := exists_pow_e h hω
    (y := (γ : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))) γ.ne_zero
  -- `ω^i` is a primitive sixth root
  have hcop : Nat.Coprime i 6 := by
    have hord : orderOf ((γ : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ^ e) = 6 := by
      have hγ' : orderOf (γ : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) = Q - 1 := by
        rw [orderOf_units, hog]
      rw [orderOf_pow' _ (by
        have := six_mul_e h; have hQ := absNorm_ne_one v; have hQ0 := absNorm_pos v
        omega), hγ']
      have := six_mul_e h
      have hQ := absNorm_ne_one v; have hQ0 := absNorm_pos v
      rw [show Q - 1 = 6 * e from (six_mul_e h).symm, Nat.gcd_mul_left_left]
      have he : 0 < e := by omega
      rw [Nat.mul_div_cancel _ he]
    have hprim : IsPrimitiveRoot ((γ : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ^ e) 6 := by
      rw [← hord]; exact IsPrimitiveRoot.orderOf _
    rw [hi] at hprim
    exact ((omegaL_prim h hω).pow_iff_coprime (by norm_num) i).1 hprim
  intro hone
  have h1 : chi ι h hω (γ : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ^ j = 1 := by
    rw [← MulChar.pow_apply' _ (by rintro rfl; exact hj (dvd_zero 6)), hone,
      MulChar.one_apply_coe]
  rw [chi_eq_pow h hω (y := (γ : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))))
    γ.ne_zero hi, ← pow_mul, (iota_omega_prim hω).pow_eq_one_iff_dvd] at h1
  exact hj (hcop.symm.dvd_of_dvd_mul_left h1)

end chi

end C3I

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.C3I_Gauss
/-! # C3I_Gauss: the additive character, Gauss sums and Davenport–Hasse on `L = R / P R`

* `psi g h : AddChar L ℂ`, `psi_mk : psi (mk x) = e(x / gen P)`, `psi_isPrimitive`.
* `card_sqrt`: `#{u | u² = w} = 1 + χ³(w)`; `jacobi_dh`: `χ(4) J(χ, χ) = J(χ³, χ)`.
* Gauss sums `g_j = gaussSum (χ^j) ψ`: `gs_mul_gs_inv`, `gs_three_sq`, `star_gs`, `dh`:
  `χ(4) g₁ g₃ = g₂²`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false


open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

lemma mk_quotLift {I : Ideal (SInt 𝔪)} (y : SInt 𝔪 ⧸ I) :
    Ideal.Quotient.mk I (quotLift y) = y :=
  Function.surjInv_eq Ideal.Quotient.mk_surjective _

/-! ### Characters on the finite field `L` -/

end C3I

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.C3I_HD
/-! # C3I_HD: the bundle's `γ_j`, `Λ`, `G` through Gauss and Jacobi sums; `Ḡ⁶ = 1` and
`γ₁ γ₂ Λ̄ Ḡ = −1` at a good prime

* `gaussPhase_eq`: `γ_j(P) = (N P)^{-1/2} g(χ^j, ψ)` (`j ≥ 1`);
* `gaussG_eq`: `G(P) = conj(χ(4)) γ₃(P)`;
* `cubicResidueChar_eq`: `ρ_P(x) = χ²(x)` through `𝓞/P ≃ L`; `gaussLambda_eq`:
  `Λ(P) = −(N P)^{-1/2} J(χ², χ²)`;
* `conj_gaussG_pow_six` and `hd_good`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

lemma normalizedFactors_v (v : HeightOneSpectrum (𝓞 F)) :
    normalizedFactors v.asIdeal = {v.asIdeal} := by
  have hirr : Irreducible v.asIdeal := (Ideal.prime_of_isPrime v.ne_bot v.isPrime).irreducible
  rw [normalizedFactors_irreducible hirr, normalize_eq]

lemma residueSymbol_v (x : SInt 𝔪) :
    residueSymbol ι 𝔪 v.asIdeal x = sexticResidueSymbol ι 𝔪 v.asIdeal x := by
  simp [residueSymbol, normalizedFactors_v]

section field

variable (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
  [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]
include h hω

lemma chi_mk_quotLift (y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    sexticResidueSymbol ι 𝔪 v.asIdeal (quotLift y) = chi ι h hω y := by
  rw [← chi_mk h hω, mk_quotLift]

end field

end C3I

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.KP.B7_Link
attribute [-simp] _root_.ArtinKP.S2.cubicSymbol_sym
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

/-! ### Transport of residue sums to the quotient by an equal ideal -/

/-! ### A good exterior prime -/

section prime

variable {v : HeightOneSpectrum (𝓞 F)} {ι : F →+* ℂ}
variable (h : C3I.Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (g : AllowedGen ι 𝔪)
  (h𝔪 : 𝔪 ≠ ⊥) (S : CubicSymbol (SInt 𝔪))
  (hS : ∀ d : SInt 𝔪, S.sym d (g.gen v.asIdeal) = sexticResidueSymbol ι 𝔪 v.asIdeal d ^ 2)

include h in
lemma gen_ne_zero : g.gen v.asIdeal ≠ 0 := fun h0 =>
  C3B.gen_ne_zero g _ h.ext (by rw [h0]; rfl)

include h in
lemma span_gen : Ideal.span {g.gen v.asIdeal} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
  g.span_gen _ h.ext

include h in
lemma isMaximal_span_gen : (Ideal.span {g.gen v.asIdeal}).IsMaximal := by
  rw [span_gen h g]; exact C3I.isMaximal_v h

include h hω hS in
/-- Nontriviality of `(·/π)`. -/
lemma exists_sym_gen_ne_one :
    ∃ d₀ : SInt 𝔪, IsCoprime d₀ (g.gen v.asIdeal) ∧ S.sym d₀ (g.gen v.asIdeal) ≠ 1 := by
  have := C3I.finite_L h
  let _ : Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) := Fintype.ofFinite _
  have hne := C3I.chi_pow_ne_one (ι := ι) h hω (j := 2) (by norm_num)
  obtain ⟨y, hy⟩ := MulChar.ne_one_iff.1 hne
  refine ⟨quotLift (y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))), ?_, ?_⟩
  · by_contra hnc
    have h0 := (S.sym_eq_zero_iff _ _ (gen_ne_zero h g)).2 hnc
    rw [hS, C3I.chi_mk_quotLift h hω] at h0
    have h1 : C3I.chi ι h hω (y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) *
        C3I.chi ι h hω ((y⁻¹ : (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))ˣ) :
          SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    exact pow_ne_zero 2 (left_ne_zero_of_mul_eq_one h1) h0
  · rw [hS, C3I.chi_mk_quotLift h hω, ← MulChar.pow_apply' _ (by norm_num)]
    exact hy

end prime

end ArtinKP.B7
end

section
-- module Solutions.Artin.KP.F_Alg_Symbol
/-!
# WP-FA, part 2: the strata of Proposition 5.4 and their symbols (MATH2 §5.3)

`π` generates an exterior prime (`PrimeElt`).  For `m ≤ 3` and `t ∈ R` the relation
`Rel π m t p p₁` says `p · [[1, t], [0, π³]] = π^m · p₁` with `m = min(v_P(c), 3)`:

  `p = (π^m c₁, d)`,  `p₁ = (c₁, c₁ t + π^(3-m) d)`,  and `π ∤ c₁` if `m < 3`.

* bijection part: `rel_smul`, `rel_fun`, `rel_inj`, `rel_dom_iff`, `rel_cod_iff`;
* symbol part: `kappa_rel` (`π ∤ c₁`), `kappa_rel_three` (`m = 3`, all cells, incl. the lower
  cells `π ∣ c₁`), `Phi_rel` (the `S_f`-part for a `t` that is deep for `Φ`);
* the phase `Theta` on the strata `m = 1, 2` and its vanishing sum `rsum_Theta`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.FA

open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- The hypotheses on a generator `π` of the exterior prime `v`: it generates a maximal ideal of
`R`, lies in `v`, and the cubic symbol `(·/π)` is not trivial. -/
structure PrimeElt (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F))
    (π : SInt 𝔪) : Prop where
  ne_zero : π ≠ 0
  isMax : (Ideal.span {π}).IsMaximal
  val_lt : v.valuation F (π : F) < 1
  nontriv : ∃ u : SInt 𝔪, ¬ π ∣ u ∧ cubicExt ι 𝔪 u π ≠ 1

/-! ### The relation -/

/-! ### Powers in the cubic symbol -/

/-! ### The phase on the strata `m = 1, 2` -/

end ArtinKP.FA
end
end

section
-- module Solutions.Artin.KP.F_Alg_Link
attribute [-simp] _root_.ArtinKP.S2.cubicSymbol_sym
/-!
# WP-FA, part 5: the hypotheses of `F_Alg_*` at an allowed generator

* `PrimeElt.of_span`: `PrimeElt` from `span {π} = P·R`, maximality and a nontrivial symbol;
* `primeElt_gen`: `PrimeElt ι 𝔪 v (g.gen v.asIdeal)` at a good exterior prime, for any
  `S : CubicSymbol (SInt 𝔪)` that agrees with `cubicExt` (the same hypotheses as `E.pairingHS`
  and `B7_Link`);
* `sum_reps_sAddChar`: the character sum of MATH2 §5.1 for `sAddChar` at `g.gen P`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.FA

open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
  {v : HeightOneSpectrum (𝓞 F)} {ι : F →+* ℂ}

theorem PrimeElt.of_span (hv : ¬ 𝔪 ≤ v.asIdeal) {π : SInt 𝔪} (hπ : π ≠ 0)
    (hspan : Ideal.span {π} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hmax : (Ideal.span {π}).IsMaximal)
    (hχ : ∃ u : SInt 𝔪, ¬ π ∣ u ∧ cubicExt ι 𝔪 u π ≠ 1) : PrimeElt ι 𝔪 v π where
  ne_zero := hπ
  isMax := hmax
  val_lt := by
    rw [(val_generator v hv π hspan).1, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  nontriv := hχ

section gen

variable (h : C3I.Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (g : AllowedGen ι 𝔪)
  (h𝔪 : 𝔪 ≠ ⊥) (S : CubicSymbol (SInt 𝔪))
  (hS : ∀ d : SInt 𝔪, S.sym d (g.gen v.asIdeal) = sexticResidueSymbol ι 𝔪 v.asIdeal d ^ 2)
  (hsym : ∀ d c : SInt 𝔪, c ≠ 0 → S.sym d c = cubicExt ι 𝔪 d c)

include h in
theorem not_le_of_good : ¬ 𝔪 ≤ v.asIdeal := fun hle =>
  v.isPrime.ne_top (eq_top_iff.2 (h.cop ▸ sup_le le_rfl hle))

include h hω hS hsym in
/-- The generator `g.gen P` of a good exterior prime satisfies `PrimeElt`. -/
theorem primeElt_gen : PrimeElt ι 𝔪 v (g.gen v.asIdeal) := by
  refine PrimeElt.of_span (not_le_of_good h) (gen_ne_zero h g) (span_gen h g)
    (isMaximal_span_gen h g) ?_
  obtain ⟨d₀, hcop, hne⟩ := exists_sym_gen_ne_one h hω g S hS
  refine ⟨d₀, (isCoprime_iff_not_dvd (isMaximal_span_gen h g) d₀).1 hcop, ?_⟩
  rwa [← hsym d₀ _ (gen_ne_zero h g)]

end gen

end ArtinKP.FA
end
end

section
-- module Solutions.Artin.KP.S2_Symbol
attribute [-instance] _root_.ArtinKP.S.GSection.instAdd _root_.ArtinKP.S.GSection.instCoeFunForallComplexForallForall _root_.ArtinKP.S.GSection.instSMulComplex _root_.ArtinKP.S.GSection.instZero
/-!
# WP-S2, part 4: the cubic symbol of `R = SInt 𝔪` as a `B7.CubicSymbol`, and its `E.Pairing`

* `isCoprime_of_val`: elements of `R` without a common exterior prime are coprime
  (`E.val_of_isCoprime` is the converse).
* `cubicExt_eq_zero_iff`: `(d/c) = 0 ↔ ¬ IsCoprime d c` for `c ≠ 0`.
* `cubicSymbol ι P hG hz6 : B7.CubicSymbol (SInt 𝔪)` with `sym d c = A.cubicExt ι 𝔪 d c`
  (WP-E open issue 1), `cubicSymbol_gen` (the hypothesis `hS` of `E_Link`), and
  `pairing : E.Pairing (cubicSymbol …)` (`E.pairingHS`).
* `span_rowElt` (WP-E open issue 5).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S2

open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

section symbol

variable (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-- The hypothesis `hS` of `E_Link` / `exists_cutoff_theoremE`. -/
theorem cubicSymbol_gen (g : AllowedGen ι 𝔪) (Q : Ideal (𝓞 F)) (hQ : Q.IsPrime)
    (hext : IsExterior 𝔪 Q) (d : SInt 𝔪) :
    (cubicSymbol ι P hG hz6).sym d (g.gen Q) = sexticResidueSymbol ι 𝔪 Q d ^ 2 := by
  rw [cubicSymbol_sym, cubicExt_eq_residueSymbol ι hext (g.gen Q) d (g.span_gen Q hext)]
  have := C3I.residueSymbol_v (ι := ι) (𝔪 := 𝔪) (v := ⟨Q, hQ, hext.1⟩) d
  rw [this]

end symbol

end ArtinKP.S2
end
end


