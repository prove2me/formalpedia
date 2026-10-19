-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_exists_cls_exists_differentiable_eq_tsum_residueSymbol_pow_three_and_functionalEquation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T10:23:14.945861+00:00
-- url     : https://prove2.me/submissions/004dc621-9b3f-48db-93b9-07d61c10a8e9

import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinL_Abelian
import Theorems.Thm_ArtinL_Abelian_exists_narrowRayClassChar_conductor_eq_localValue_u0
import Theorems.Thm_ArtinL_Abelian_dvd_conductor_iff_not_isUnramifiedAt
import Theorems.Thm_ArtinL_Abelian_exists_completedLSeries_functionalEquation_u0
import Theorems.Thm_LT_HeckeChar_exists_heckeCharOfRayClassChar
import Theorems.Thm_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles
import Theorems.Thm_NumberField_TateGlobal_exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc
import Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
import Theorems.Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
import Theorems.Thm_NumberField_exists_completedDedekindZeta_package
import Theorems.Thm_NumberField_dedekindZeta_ne_zero_of_one_lt_re
import Definitions.Def_LanglandsTunnell_ArtinFrobenius
import Definitions.Def_ArtinHeckeRowL
import Theorems.Thm_ArtinPrimitiveRoots_heckeLSeries_euler_package_of_le
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Mathlib

universe u

section
section
/-! # L3K_Gamma: the Gamma-factor ratio on the left edge of the convexity strip

* `norm_Gamma_mono`: `σ ↦ ‖Γ(σ + it)‖ / Γ(σ)` is nondecreasing on `σ > 0` (Gauss's product).
* `norm_Gamma_one_add_sq`: `‖Γ(1 + it)‖² = π |t| / |sinh(π t)|`.
* `exists_norm_Gammaℂ_ratio_le`: for `0 < δ < 1`,
  `‖Γ_ℂ(1 + δ − it) / Γ_ℂ(−δ + it)‖ ≤ C (1 + |t|)^3`. -/

open Complex Filter Topology

set_option autoImplicit false

namespace ArtinPrimitiveRoots

namespace L3K

end L3K

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

instance finite_fiber (n : ℕ) : Finite {I : Ideal (𝓞 K) // absNorm I = n} := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton {I : Ideal (𝓞 K) // absNorm I = 0} :=
      ⟨fun a b => Subtype.ext (by
        rw [Ideal.absNorm_eq_zero_iff.mp a.2, Ideal.absNorm_eq_zero_iff.mp b.2])⟩
    exact Finite.of_subsingleton
  · exact (finite_setOfPred_absNorm_eq n).to_subtype

end ArtinPrimitiveRoots.T12A

end
end

section
section
/-! # T12A_Ray: a `HeckeChar` as a narrow ray class character

A `HeckeChar K 𝔪` (𝔪 ≠ ⊥) is `I ↦ ψ([I])` on ideals coprime to `𝔪` for a character `ψ` of the narrow
ray class group mod `𝔪` with parity set `∅`, and `χ.LSeries = rayClassLSeries ψ` on `Re s > 1`. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply nonZeroDivisors Complex

namespace ArtinPrimitiveRoots.T12A

section Coprime

variable {F : Type*} [Field F] [NumberField F]

theorem sup_eq_top_iff_forall {I 𝔣 : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    I ⊔ 𝔣 = ⊤ ↔ ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ 𝔣 → ¬ v.asIdeal ∣ I := by
  constructor
  · intro h v hf hI'
    apply v.isPrime.ne_top
    rw [eq_top_iff, ← h]
    exact sup_le (Ideal.le_of_dvd hI') (Ideal.le_of_dvd hf)
  · intro h
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hmb : m ≠ ⊥ := by
      intro hb
      apply hI
      rw [eq_bot_iff, ← hb]
      exact le_trans le_sup_left hle
    let v : HeightOneSpectrum (𝓞 F) := ⟨m, hm.isPrime, hmb⟩
    exact h v (Ideal.dvd_iff_le.mpr (le_trans le_sup_right hle))
      (Ideal.dvd_iff_le.mpr (le_trans le_sup_left hle))

theorem mk0_mem_coprimeToModulus_iff {I 𝔣 : Ideal (𝓞 F)} (hI : I ∈ (Ideal (𝓞 F))⁰) :
    FractionalIdeal.mk0 F ⟨I, hI⟩ ∈ coprimeToModulus F 𝔣 ↔ I ⊔ 𝔣 = ⊤ := by
  have hI0 : I ≠ 0 := nonZeroDivisors.ne_zero hI
  rw [mem_coprimeToModulus_iff, sup_eq_top_iff_forall hI0]
  refine forall_congr' fun v => imp_congr_right fun _ => ?_
  rw [FractionalIdeal.coe_mk0, FractionalIdeal.count_coe F v hI0, Nat.cast_eq_zero]
  constructor
  · intro h hd
    exact (Associates.count_ne_zero_iff_dvd hI0 v.irreducible).mpr hd h
  · intro h
    by_contra hc
    exact h ((Associates.count_ne_zero_iff_dvd hI0 v.irreducible).mp hc)

theorem span_ne_bot {α : 𝓞 F} (hα : α ≠ 0) : Ideal.span {α} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact hα

theorem span_sup_eq_top {𝔣 : Ideal (𝓞 F)} {α : 𝓞 F} (h1 : α - 1 ∈ 𝔣) :
    Ideal.span {α} ⊔ 𝔣 = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h : (1 : 𝓞 F) = α - (α - 1) := by ring
  rw [h]
  exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self α))
    (Ideal.mem_sup_right h1)

end Coprime

section Factor

variable {F : Type*} [Field F] [NumberField F] {𝔣 : Ideal (𝓞 F)}

theorem hasFiniteMulSupport_pow_count (f : HeightOneSpectrum (𝓞 F) → ℂ) {I : Ideal (𝓞 F)}
    (hI : I ≠ ⊥) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      f v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  by_contra hd
  apply hv
  have : (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0 := by
    by_contra hc
    exact hd ((Associates.count_ne_zero_iff_dvd hI v.irreducible).mp hc)
  simp only [this, pow_zero]

open Classical in
theorem count_prime_eq (v w : HeightOneSpectrum (𝓞 F)) :
    (Associates.mk v.asIdeal).count (Associates.mk w.asIdeal).factors = if v = w then 1 else 0 := by
  split_ifs with h
  · subst h
    exact Associates.count_self v.associates_irreducible
  · by_contra hc
    have hd := (Associates.count_ne_zero_iff_dvd w.ne_bot v.irreducible).mp hc
    apply h
    exact HeightOneSpectrum.ext
      ((w.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.le_of_dvd hd)).symm)

/-- A `HeckeChar` is determined on nonzero ideals by its values at primes. -/
theorem heckeChar_eq_finprod (η : ArtinPrimitiveRoots.HeckeChar F 𝔣)
    (f : HeightOneSpectrum (𝓞 F) → ℂ) (hf : ∀ v : HeightOneSpectrum (𝓞 F), η.toFun v.asIdeal = f v)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    η.toFun I = ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      f v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
  revert hI
  refine UniqueFactorizationMonoid.induction_on_prime I ?_ ?_ ?_
  · intro h
    exact absurd rfl h
  · intro x hx _
    rw [Ideal.isUnit_iff] at hx
    subst hx
    have h1 : η.toFun ⊤ = 1 := by
      have := η.map_principal' 1 one_ne_zero (by rw [sub_self]; exact Ideal.zero_mem _)
      rwa [Ideal.span_singleton_one] at this
    rw [h1, ← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one]
    exact (finprod_eq_one_of_forall_eq_one fun v => by
      rw [Associates.count_zero v.associates_irreducible, pow_zero]).symm
  · intro a p ha hp ih hpa
    have ha' : a ≠ ⊥ := ha
    let v₀ : HeightOneSpectrum (𝓞 F) := HeightOneSpectrum.ofPrime hp
    have hp0 : p ≠ 0 := hp.ne_zero
    rw [η.map_mul', ih ha']
    have hcount : ∀ v : HeightOneSpectrum (𝓞 F),
        (Associates.mk v.asIdeal).count (Associates.mk (p * a)).factors =
          (Associates.mk v.asIdeal).count (Associates.mk p).factors +
            (Associates.mk v.asIdeal).count (Associates.mk a).factors := by
      intro v
      rw [← Associates.mk_mul_mk]
      exact Associates.count_mul (Associates.mk_ne_zero.mpr hp0) (Associates.mk_ne_zero.mpr ha)
        v.associates_irreducible
    simp_rw [hcount, pow_add]
    rw [finprod_mul_distrib (hasFiniteMulSupport_pow_count f (I := p) hp0)
      (hasFiniteMulSupport_pow_count f ha')]
    congr 1
    have hp' : p = v₀.asIdeal := rfl
    rw [hp', hf v₀, finprod_eq_single _ v₀]
    · rw [count_prime_eq, if_pos rfl, pow_one]
    · intro v hv
      rw [count_prime_eq, if_neg hv, pow_zero]

end Factor

section Ray

variable {K : Type} [Field K] [NumberField K] {𝔪 : Ideal (𝓞 K)}

theorem heckeChar_ne_zero (χ : HeckeChar K 𝔪) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (hc : I ⊔ 𝔪 = ⊤) : χ.toFun I ≠ 0 := by
  rw [Ne, χ.eq_zero_iff']
  tauto

theorem heckeChar_eq_zero (χ : HeckeChar K 𝔪) {I : Ideal (𝓞 K)}
    (h : ¬ (I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤)) : χ.toFun I = 0 := by
  rw [χ.eq_zero_iff']
  tauto

open Classical in
/-- The values of `χ` at primes, as units (`1` at primes dividing `𝔪`). -/
noncomputable def primeVal (χ : HeckeChar K 𝔪) (v : HeightOneSpectrum (𝓞 K)) : ℂˣ :=
  if h : v.asIdeal ⊔ 𝔪 = ⊤ then Units.mk0 (χ.toFun v.asIdeal) (heckeChar_ne_zero χ v.ne_bot h)
  else 1

theorem raySymbol_coe (χ : HeckeChar K 𝔪) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hc : I ⊔ 𝔪 = ⊤) :
    ((raySymbol K (primeVal χ) (I : FractionalIdeal (𝓞 K)⁰ K) : ℂˣ) : ℂ) = χ.toFun I := by
  rw [heckeChar_eq_finprod χ (fun v => χ.toFun v.asIdeal) (fun v => rfl) I hI, raySymbol,
    ← Units.coeHom_apply, MonoidHom.map_finprod _ (hasFiniteMulSupport_raySymbol_factors K _ _)]
  refine finprod_congr fun v => ?_
  rw [FractionalIdeal.count_coe K v hI, zpow_natCast, Units.coeHom_apply, Units.val_pow_eq_pow_val]
  by_cases hd : v.asIdeal ∣ I
  · have hv : v.asIdeal ⊔ 𝔪 = ⊤ :=
      eq_top_iff.mpr (hc ▸ sup_le_sup_right (Ideal.le_of_dvd hd) _)
    rw [primeVal, dif_pos hv, Units.val_mk0]
  · have : (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0 := by
      by_contra h0
      exact hd ((Associates.count_ne_zero_iff_dvd hI v.irreducible).mp h0)
    rw [this, pow_zero, pow_zero]

theorem hkill (χ : HeckeChar K 𝔪) : ∀ α : 𝓞 K, α ≠ 0 → α - 1 ∈ 𝔪 →
    (∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) →
    raySymbol K (primeVal χ) ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) = 1 := by
  intro α hα h1 _
  apply Units.ext
  rw [raySymbol_coe χ (span_ne_bot hα) (span_sup_eq_top h1), Units.val_one]
  exact χ.map_principal' α hα h1

/-- The narrow ray class character attached to `χ`. -/
noncomputable def rayChar (χ : HeckeChar K 𝔪) : NarrowRayClassGroup K 𝔪 →* ℂ :=
  (Units.coeHom ℂ).comp (raySymbolDescend K (primeVal χ) (hkill χ))

theorem rayChar_mk (χ : HeckeChar K 𝔪) (y : ↥(coprimeToModulus K 𝔪)) :
    rayChar χ (NarrowRayClassGroup.mk K 𝔪 y) =
      ((raySymbol K (primeVal χ)
        ((y : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) : ℂˣ) : ℂ) := by
  rw [rayChar, MonoidHom.comp_apply, raySymbolDescend_mk, raySymbolHom_apply, Units.coeHom_apply]

theorem rayChar_mk_ideal (χ : HeckeChar K 𝔪) {I : Ideal (𝓞 K)} (hI : I ∈ (Ideal (𝓞 K))⁰)
    (hc : FractionalIdeal.mk0 K ⟨I, hI⟩ ∈ coprimeToModulus K 𝔪) :
    rayChar χ (NarrowRayClassGroup.mk K 𝔪 ⟨FractionalIdeal.mk0 K ⟨I, hI⟩, hc⟩) = χ.toFun I := by
  rw [rayChar_mk]
  show ((raySymbol K (primeVal χ) ((FractionalIdeal.mk0 K ⟨I, hI⟩ :
    (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) : ℂˣ) : ℂ) = _
  rw [FractionalIdeal.coe_mk0]
  exact raySymbol_coe χ (nonZeroDivisors.ne_zero hI) ((mk0_mem_coprimeToModulus_iff hI).1 hc)

theorem norm_rayChar (h𝔪 : 𝔪 ≠ ⊥) (χ : HeckeChar K 𝔪) (C : NarrowRayClassGroup K 𝔪) :
    ‖rayChar χ C‖ = 1 := by
  haveI := Deep.NTSupply.finite K h𝔪
  have h : rayChar χ C ^ Nat.card (NarrowRayClassGroup K 𝔪) = 1 := by
    rw [← map_pow, pow_card_eq_one', map_one]
  exact norm_eq_one_of_pow_eq_one h Nat.card_pos.ne'

open Classical in
/-- The class of an ideal (`1` when it is zero or not coprime to `𝔪`). -/
noncomputable def cls (𝔪 : Ideal (𝓞 K)) (I : Ideal (𝓞 K)) : NarrowRayClassGroup K 𝔪 :=
  if h : I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤ then
    NarrowRayClassGroup.mk K 𝔪 ⟨FractionalIdeal.mk0 K ⟨I, mem_nonZeroDivisors_of_ne_zero h.1⟩,
      (mk0_mem_coprimeToModulus_iff _).2 h.2⟩
  else 1

open Classical in
theorem heckeChar_eq_ite (χ : HeckeChar K 𝔪) (I : Ideal (𝓞 K)) :
    χ.toFun I = if I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤ then rayChar χ (cls 𝔪 I) else 0 := by
  split_ifs with h
  · rw [cls, dif_pos h, rayChar_mk_ideal]
  · exact heckeChar_eq_zero χ h

theorem norm_heckeChar_le (h𝔪 : 𝔪 ≠ ⊥) (χ : HeckeChar K 𝔪) (I : Ideal (𝓞 K)) :
    ‖χ.toFun I‖ ≤ 1 := by
  rw [heckeChar_eq_ite]
  split_ifs
  · rw [norm_rayChar h𝔪]
  · simp

end Ray

end ArtinPrimitiveRoots.T12A

end
end

section
section
/-! # C3A_Sieve: Euler products of multiplicative functions of four ideals

A function `f` on 4-tuples of ideals of `𝓞 F`, supported on exterior tuples, with
`f (P^e · y) = A P e · f y` for exterior primes `P` and exterior `y` prime to `P`, and absolutely
summable, has the Euler product `∑' f = ∏'_P ∑'_e A P e` over the exterior primes (`euler4`).
Proof: the finite sieve `∑' f = (∏_{P ∈ T} L_P) · ∑'_{x prime to T} f x` (induction on `T`) and a
tail estimate. Also a bound `‖f‖ ≤ B` for multiplicative majorants (`norm_le_of_mul`). -/

open NumberField Filter Topology

namespace ArtinPrimitiveRoots

namespace C3A

variable {F : Type*} [Field F] [NumberField F]

/-- 4-tuples of ideals. -/
abbrev Tup (F : Type*) [Field F] [NumberField F] : Type _ :=
  Ideal (𝓞 F) × Ideal (𝓞 F) × Ideal (𝓞 F) × Ideal (𝓞 F)

/-- Exponent vectors. -/
abbrev Exps : Type := ℕ × ℕ × ℕ × ℕ

/-- `P^e · x`, coordinatewise. -/
def pw (P : Ideal (𝓞 F)) (e : Exps) (x : Tup F) : Tup F :=
  (P ^ e.1 * x.1, P ^ e.2.1 * x.2.1, P ^ e.2.2.1 * x.2.2.1, P ^ e.2.2.2 * x.2.2.2)

/-- The unit tuple. -/
def one4 : Tup F := (⊤, ⊤, ⊤, ⊤)

/-- Exterior tuples. -/
def Om (𝔪 : Ideal (𝓞 F)) : Set (Tup F) :=
  {x | IsExterior 𝔪 x.1 ∧ IsExterior 𝔪 x.2.1 ∧ IsExterior 𝔪 x.2.2.1 ∧ IsExterior 𝔪 x.2.2.2}

/-- Tuples prime to `P`. -/
def CopP (P : Ideal (𝓞 F)) : Set (Tup F) :=
  {x | ¬ x.1 ≤ P ∧ ¬ x.2.1 ≤ P ∧ ¬ x.2.2.1 ≤ P ∧ ¬ x.2.2.2 ≤ P}

/-- Tuples prime to every member of `T`. -/
def Cop (T : Finset (Ideal (𝓞 F))) : Set (Tup F) := {x | ∀ P ∈ T, x ∈ CopP P}

/-- Exterior primes. -/
def IsEP (𝔪 P : Ideal (𝓞 F)) : Prop := P.IsPrime ∧ P ≠ ⊥ ∧ P ⊔ 𝔪 = ⊤

/-- The type of exterior primes. -/
abbrev EP (𝔪 : Ideal (𝓞 F)) : Type _ := {P : Ideal (𝓞 F) // P.IsPrime ∧ P ≠ ⊥ ∧ P ⊔ 𝔪 = ⊤}

lemma two_le_absNorm {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    2 ≤ Ideal.absNorm P := by
  have h0 : Ideal.absNorm P ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have h1 : Ideal.absNorm P ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact hP.ne_top
  omega

lemma decomp1 {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    ∀ I : Ideal (𝓞 F), I ≠ ⊥ → ∃ k J, I = P ^ k * J ∧ ¬ J ≤ P := by
  intro I
  induction hN : Ideal.absNorm I using Nat.strong_induction_on generalizing I with
  | _ N ih =>
  intro hI
  by_cases hle : I ≤ P
  · obtain ⟨J, rfl⟩ := Ideal.dvd_iff_le.2 hle
    have hJ : J ≠ ⊥ := by rintro rfl; exact hI (by simp)
    have hlt : Ideal.absNorm J < N := by
      rw [← hN, map_mul]
      have := two_le_absNorm hP hP0
      have hJ0 : Ideal.absNorm J ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
      have := Nat.pos_of_ne_zero hJ0
      nlinarith
    obtain ⟨k, K, hK, hKP⟩ := ih _ hlt J rfl hJ
    exact ⟨k + 1, K, by rw [hK, pow_succ', mul_assoc], hKP⟩
  · exact ⟨0, I, by simp, hle⟩

lemma cancel1 {P : Ideal (𝓞 F)} (hP0 : P ≠ ⊥) {a b : ℕ} {J J' : Ideal (𝓞 F)}
    (hJ : ¬ J ≤ P) (hJ' : ¬ J' ≤ P) (h : P ^ a * J = P ^ b * J') : a = b ∧ J = J' := by
  have hP : (P : Ideal (𝓞 F)) ≠ 0 := hP0
  have key : ∀ {a b : ℕ} {J J' : Ideal (𝓞 F)}, ¬ J ≤ P → a ≤ b → P ^ a * J = P ^ b * J' →
      a = b ∧ J = J' := by
    intro a b J J' hJ hab h
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [pow_add, mul_assoc] at h
    have h2 := mul_left_cancel₀ (pow_ne_zero a hP) h
    rcases c with _ | c
    · simp only [pow_zero, one_mul] at h2
      exact ⟨rfl, h2⟩
    · exfalso; apply hJ; rw [h2, pow_succ', mul_assoc]; exact Ideal.mul_le_left
  rcases le_total a b with hab | hab
  · exact key hJ hab h
  · obtain ⟨h1, h2⟩ := key hJ' hab h.symm
    exact ⟨h1.symm, h2.symm⟩

lemma pw_injective {P : Ideal (𝓞 F)} (hP0 : P ≠ ⊥) {e e' : Exps} {y y' : Tup F}
    (hy : y ∈ CopP P) (hy' : y' ∈ CopP P) (h : pw P e y = pw P e' y') : e = e' ∧ y = y' := by
  obtain ⟨e1, e2, e3, e4⟩ := e
  obtain ⟨e1', e2', e3', e4'⟩ := e'
  obtain ⟨y1, y2, y3, y4⟩ := y
  obtain ⟨y1', y2', y3', y4'⟩ := y'
  simp only [pw, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨a1, a2, a3, a4⟩ := hy
  obtain ⟨b1, b2, b3, b4⟩ := hy'
  obtain ⟨c1, d1⟩ := cancel1 hP0 a1 b1 h1
  obtain ⟨c2, d2⟩ := cancel1 hP0 a2 b2 h2
  obtain ⟨c3, d3⟩ := cancel1 hP0 a3 b3 h3
  obtain ⟨c4, d4⟩ := cancel1 hP0 a4 b4 h4
  subst c1 c2 c3 c4 d1 d2 d3 d4
  exact ⟨rfl, rfl⟩

lemma exterior_of_dvd {𝔪 I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 (J * I)) : IsExterior 𝔪 I := by
  refine ⟨fun h => hI.1 (by rw [h, Ideal.mul_bot]), ?_⟩
  rw [eq_top_iff, ← hI.2]
  exact sup_le_sup_right Ideal.mul_le_right _

lemma mem_Om_of_pw {𝔪 P : Ideal (𝓞 F)} {e : Exps} {y : Tup F} (h : pw P e y ∈ Om 𝔪) :
    y ∈ Om 𝔪 :=
  ⟨exterior_of_dvd h.1, exterior_of_dvd h.2.1, exterior_of_dvd h.2.2.1, exterior_of_dvd h.2.2.2⟩

lemma not_le_pw {P Q I : Ideal (𝓞 F)} (hP : P.IsMaximal) (hQ : Q.IsPrime) (hPQ : P ≠ Q)
    (hI : ¬ I ≤ Q) (k : ℕ) : ¬ P ^ k * I ≤ Q := by
  intro h
  rcases hQ.mul_le.1 h with h1 | h1
  · exact hPQ (hP.eq_of_le hQ.ne_top (hQ.le_of_pow_le h1))
  · exact hI h1

lemma pw_mem_Cop {T : Finset (Ideal (𝓞 F))} (hT : ∀ Q ∈ T, Q.IsPrime) {P : Ideal (𝓞 F)}
    (hP : P.IsMaximal) (hPT : P ∉ T) (e : Exps) {y : Tup F} (hy : y ∈ Cop T) :
    pw P e y ∈ Cop T := by
  intro Q hQ
  have hPQ : P ≠ Q := fun h => hPT (h ▸ hQ)
  obtain ⟨a1, a2, a3, a4⟩ := hy Q hQ
  exact ⟨not_le_pw hP (hT Q hQ) hPQ a1 _, not_le_pw hP (hT Q hQ) hPQ a2 _,
    not_le_pw hP (hT Q hQ) hPQ a3 _, not_le_pw hP (hT Q hQ) hPQ a4 _⟩

lemma isEP_of_le {𝔪 P I : Ideal (𝓞 F)} (hP : P.IsMaximal) (hI : IsExterior 𝔪 I) (hle : I ≤ P) :
    IsEP 𝔪 P := by
  refine ⟨hP.isPrime, fun h => hI.1 (le_bot_iff.1 (h ▸ hle)), ?_⟩
  rw [eq_top_iff, ← hI.2]
  exact sup_le_sup_right hle _

/-- Decomposition of an exterior tuple at a prime. -/
lemma decomp4 {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) {𝔪 : Ideal (𝓞 F)} {x : Tup F}
    (hx : x ∈ Om 𝔪) : ∃ e y, x = pw P e y ∧ y ∈ CopP P := by
  obtain ⟨k1, J1, h1, n1⟩ := decomp1 hP hP0 x.1 hx.1.1
  obtain ⟨k2, J2, h2, n2⟩ := decomp1 hP hP0 x.2.1 hx.2.1.1
  obtain ⟨k3, J3, h3, n3⟩ := decomp1 hP hP0 x.2.2.1 hx.2.2.1.1
  obtain ⟨k4, J4, h4, n4⟩ := decomp1 hP hP0 x.2.2.2 hx.2.2.2.1
  refine ⟨(k1, k2, k3, k4), (J1, J2, J3, J4), ?_, n1, n2, n3, n4⟩
  obtain ⟨x1, x2, x3, x4⟩ := x
  simp only [pw] at *
  rw [← h1, ← h2, ← h3, ← h4]

lemma le_of_pw (P : Ideal (𝓞 F)) (e : Exps) (y : Tup F) :
    (pw P e y).1 ≤ y.1 ∧ (pw P e y).2.1 ≤ y.2.1 ∧ (pw P e y).2.2.1 ≤ y.2.2.1 ∧
      (pw P e y).2.2.2 ≤ y.2.2.2 :=
  ⟨Ideal.mul_le_right, Ideal.mul_le_right, Ideal.mul_le_right, Ideal.mul_le_right⟩

lemma one4_mem_Cop (T : Finset (Ideal (𝓞 F))) (hT : ∀ Q ∈ T, Q.IsPrime) :
    (one4 : Tup F) ∈ Cop T := by
  intro Q hQ
  have : ¬ (⊤ : Ideal (𝓞 F)) ≤ Q := fun h => (hT Q hQ).ne_top (top_le_iff.1 h)
  exact ⟨this, this, this, this⟩

section sieve

variable (𝔪 : Ideal (𝓞 F)) (f : Tup F → ℂ) (A : Ideal (𝓞 F) → Exps → ℂ)

/-- The hypotheses of the Euler product. -/
structure EulerHyp : Prop where
  zero : ∀ x, x ∉ Om 𝔪 → f x = 0
  one : f one4 = 1
  mul : ∀ P, IsEP 𝔪 P → ∀ e y, y ∈ Om 𝔪 → y ∈ CopP P → f (pw P e y) = A P e * f y
  summ : Summable (fun x => ‖f x‖)
  summA : ∀ P, IsEP 𝔪 P → Summable (fun e => ‖A P e‖)

variable {𝔪 f A}

lemma summable_norm_indicator (h : EulerHyp 𝔪 f A) (s : Set (Tup F)) :
    Summable (fun x => ‖s.indicator f x‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => norm_indicator_le_norm_self _ _)
    h.summ

/-- One sieve step. -/
theorem sieve_step (h : EulerHyp 𝔪 f A) (T : Finset (Ideal (𝓞 F))) (hT : ∀ Q ∈ T, Q.IsPrime)
    {P : Ideal (𝓞 F)} (hP : IsEP 𝔪 P) (hPT : P ∉ T) :
    ∑' x, (Cop T).indicator f x =
      (∑' e, A P e) * ∑' x, (Cop (insert P T)).indicator f x := by
  classical
  have hPmax : P.IsMaximal := hP.1.isMaximal hP.2.1
  set h1 := (Cop T).indicator f with hh1
  set h2 := (Cop (insert P T)).indicator f with hh2
  rw [tsum_mul_tsum_of_summable_norm (h.summA P hP) (summable_norm_indicator h _)]
  set G : Exps × Tup F → ℂ := fun z => A P z.1 * h2 z.2 with hG
  -- the key pointwise fact
  have hkey : ∀ z : Exps × Tup F, G z ≠ 0 →
      z.2 ∈ Cop (insert P T) ∧ z.2 ∈ Om 𝔪 ∧ h1 (pw P z.1 z.2) = G z := by
    intro z hz
    have hz2 : h2 z.2 ≠ 0 := fun h0 => hz (by simp [hG, h0])
    have hc : z.2 ∈ Cop (insert P T) := by
      by_contra hc; exact hz2 (Set.indicator_of_notMem hc _)
    have hO : z.2 ∈ Om 𝔪 := by
      by_contra hO; exact hz2 (by rw [hh2, Set.indicator_of_mem hc]; exact h.zero _ hO)
    refine ⟨hc, hO, ?_⟩
    have hcT : z.2 ∈ Cop T := fun Q hQ => hc Q (Finset.mem_insert_of_mem hQ)
    have hcP : z.2 ∈ CopP P := hc P (Finset.mem_insert_self _ _)
    rw [hh1, Set.indicator_of_mem (pw_mem_Cop hT hPmax hPT z.1 hcT), h.mul P hP z.1 z.2 hO hcP,
      hG]
    simp only
    rw [hh2, Set.indicator_of_mem hc]
  refine tsum_eq_tsum_of_ne_zero_bij (fun z => pw P z.1.1 z.1.2) ?_ ?_ ?_
  · rintro ⟨z, hz⟩ ⟨z', hz'⟩ hzz
    have a := (hkey z hz).1 P (Finset.mem_insert_self _ _)
    have b := (hkey z' hz').1 P (Finset.mem_insert_self _ _)
    obtain ⟨he, hy⟩ := pw_injective hP.2.1 a b hzz
    exact Subtype.ext (Prod.ext he hy)
  · intro x hx
    have hx' : h1 x ≠ 0 := hx
    have hxc : x ∈ Cop T := by
      by_contra hc; exact hx' (Set.indicator_of_notMem hc _)
    have hxO : x ∈ Om 𝔪 := by
      by_contra hO; exact hx' (by rw [hh1, Set.indicator_of_mem hxc]; exact h.zero _ hO)
    obtain ⟨e, y, rfl, hyP⟩ := decomp4 hP.1 hP.2.1 hxO
    have hyO : y ∈ Om 𝔪 := mem_Om_of_pw hxO
    have hyc : y ∈ Cop (insert P T) := by
      intro Q hQ
      rcases Finset.mem_insert.1 hQ with rfl | hQ
      · exact hyP
      · obtain ⟨a1, a2, a3, a4⟩ := hxc Q hQ
        obtain ⟨l1, l2, l3, l4⟩ := le_of_pw P e y
        exact ⟨fun h' => a1 (l1.trans h'), fun h' => a2 (l2.trans h'),
          fun h' => a3 (l3.trans h'), fun h' => a4 (l4.trans h')⟩
    have hGe : G (e, y) = h1 (pw P e y) := by
      rw [hh1, Set.indicator_of_mem hxc, h.mul P hP e y hyO hyP, hG]
      simp only
      rw [hh2, Set.indicator_of_mem hyc]
    refine ⟨⟨(e, y), ?_⟩, rfl⟩
    show G (e, y) ≠ 0
    rw [hGe]; exact hx'
  · rintro ⟨z, hz⟩
    exact (hkey z hz).2.2

/-- The finite sieve. -/
theorem sieve_eq (h : EulerHyp 𝔪 f A) (T : Finset (Ideal (𝓞 F))) (hT : ∀ Q ∈ T, IsEP 𝔪 Q) :
    ∑' x, f x = (∏ Q ∈ T, ∑' e, A Q e) * ∑' x, (Cop T).indicator f x := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    have : (Cop (∅ : Finset (Ideal (𝓞 F)))) = Set.univ := by
      ext x; simp [Cop]
    rw [this, Set.indicator_univ, Finset.prod_empty, one_mul]
  | insert P T hPT ih =>
    have ih' := ih (fun Q hQ => hT Q (Finset.mem_insert_of_mem hQ))
    rw [ih', sieve_step h T (fun Q hQ => (hT Q (Finset.mem_insert_of_mem hQ)).1)
      (hT P (Finset.mem_insert_self _ _)) hPT, Finset.prod_insert hPT]
    ring

/-- The tail estimate. -/
theorem sieve_tail (h : EulerHyp 𝔪 f A) {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : Finset (EP 𝔪), ∀ T : Finset (EP 𝔪), T₀ ⊆ T →
      ‖∑' x, (Cop (T.map (Function.Embedding.subtype _))).indicator f x - 1‖ < ε := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Finset (Tup F), ∑' x : {x // x ∉ S}, ‖f x‖ < ε :=
    ((tendsto_tsum_compl_atTop_zero (fun x => ‖f x‖)).eventually (gt_mem_nhds hε)).exists
  -- the coordinates of `S`
  set Sid : Finset (Ideal (𝓞 F)) := S.image (·.1) ∪ S.image (·.2.1) ∪ S.image (·.2.2.1) ∪
    S.image (·.2.2.2) with hSid
  have hfin : {P : EP 𝔪 | ∃ I ∈ Sid, I ≠ ⊥ ∧ I ≤ P.1}.Finite := by
    have h1 : {P : Ideal (𝓞 F) | ∃ I ∈ Sid, I ≠ ⊥ ∧ I ≤ P}.Finite := by
      have : {P : Ideal (𝓞 F) | ∃ I ∈ Sid, I ≠ ⊥ ∧ I ≤ P} ⊆
          ⋃ I ∈ Sid, {P : Ideal (𝓞 F) | Ideal.absNorm P ≤ Ideal.absNorm I} := by
        rintro P ⟨I, hI, hI0, hle⟩
        refine Set.mem_biUnion hI ?_
        exact Nat.le_of_dvd (Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]))
          (Ideal.absNorm_dvd_absNorm_of_le hle)
      exact (Set.Finite.biUnion Sid.finite_toSet fun I _ =>
        Ideal.finite_setOfPred_absNorm_le _).subset this
    exact h1.preimage (f := fun P : EP 𝔪 => P.1) Subtype.val_injective.injOn
  refine ⟨hfin.toFinset, fun T hT => ?_⟩
  set T' := T.map (Function.Embedding.subtype _) with hT'
  have hT'p : ∀ Q ∈ T', Q.IsPrime := by
    intro Q hQ
    obtain ⟨P, -, rfl⟩ := Finset.mem_map.1 hQ
    exact P.2.1
  -- inside `S`, only `one4` survives
  have hsurv : ∀ x ∈ S, x ∈ Cop T' → x ∈ Om 𝔪 → x = one4 := by
    intro x hxS hxc hxO
    have hcoord : ∀ I ∈ Sid, IsExterior 𝔪 I → (∀ Q ∈ T', ¬ I ≤ Q) → I = ⊤ := by
      intro I hI hIe hIc
      by_contra hIt
      obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal I hIt
      have hEP := isEP_of_le hM hIe hle
      have hmem : (⟨M, hEP⟩ : EP 𝔪) ∈ T := hT (by
        rw [Set.Finite.mem_toFinset]; exact ⟨I, hI, hIe.1, hle⟩)
      exact hIc M (Finset.mem_map.2 ⟨_, hmem, rfl⟩) hle
    have m1 : x.1 ∈ Sid := by
      simp only [hSid, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Finset.mem_image_of_mem _ hxS)))
    have m2 : x.2.1 ∈ Sid := by
      simp only [hSid, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inr (Finset.mem_image_of_mem _ hxS)))
    have m3 : x.2.2.1 ∈ Sid := by
      simp only [hSid, Finset.mem_union]
      exact Or.inl (Or.inr (Finset.mem_image_of_mem _ hxS))
    have m4 : x.2.2.2 ∈ Sid := by
      simp only [hSid, Finset.mem_union]
      exact Or.inr (Finset.mem_image_of_mem _ hxS)
    have e1 := hcoord _ m1 hxO.1 fun Q hQ => (hxc Q hQ).1
    have e2 := hcoord _ m2 hxO.2.1 fun Q hQ => (hxc Q hQ).2.1
    have e3 := hcoord _ m3 hxO.2.2.1 fun Q hQ => (hxc Q hQ).2.2.1
    have e4 := hcoord _ m4 hxO.2.2.2 fun Q hQ => (hxc Q hQ).2.2.2
    obtain ⟨x1, x2, x3, x4⟩ := x
    simp only at e1 e2 e3 e4
    rw [e1, e2, e3, e4]; rfl
  have hite : Summable (fun x : Tup F => if x = one4 then (1 : ℂ) else 0) :=
    (hasSum_ite_eq one4 (1 : ℂ)).summable
  have hpt : ∀ x, ‖(Cop T').indicator f x - (if x = one4 then (1 : ℂ) else 0)‖ ≤
      ({x | x ∉ S} : Set (Tup F)).indicator (fun x => ‖f x‖) x := by
    intro x
    by_cases hx1 : x = one4
    · subst hx1
      rw [Set.indicator_of_mem (one4_mem_Cop T' hT'p), h.one, if_pos rfl, sub_self, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => norm_nonneg _) _
    rw [if_neg hx1, sub_zero]
    by_cases hxS : x ∈ S
    · rw [Set.indicator_of_notMem (show x ∉ {x | x ∉ S} from fun h' => h' hxS)]
      by_cases hxc : x ∈ Cop T'
      · rw [Set.indicator_of_mem hxc]
        by_cases hxO : x ∈ Om 𝔪
        · exact absurd (hsurv x hxS hxc hxO) hx1
        · rw [h.zero x hxO, norm_zero]
      · rw [Set.indicator_of_notMem hxc, norm_zero]
    · rw [Set.indicator_of_mem (show x ∈ {x | x ∉ S} from hxS)]
      exact norm_indicator_le_norm_self _ _
  rw [← tsum_ite_eq (one4 : Tup F) (fun _ => (1 : ℂ)),
    ← ((summable_norm_indicator h _).of_norm).tsum_sub hite]
  have hsn : Summable (fun x => ‖(Cop T').indicator f x - (if x = one4 then (1 : ℂ) else 0)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (h.summ.indicator _)
  refine lt_of_le_of_lt (norm_tsum_le_tsum_norm hsn) ?_
  refine lt_of_le_of_lt (hsn.tsum_le_tsum hpt (h.summ.indicator _)) ?_
  rw [← tsum_subtype {x | x ∉ S} (fun x => ‖f x‖)]
  exact hS

/-- **The Euler product.** -/
theorem euler4 (h : EulerHyp 𝔪 f A) :
    HasProd (fun P : EP 𝔪 => ∑' e, A P.1 e) (∑' x, f x) ∧
      ((∀ P : EP 𝔪, ∑' e, A P.1 e ≠ 0) → ∑' x, f x ≠ 0) := by
  classical
  set X := ∑' x, f x
  set S : Finset (EP 𝔪) → ℂ :=
    fun T => ∑' x, (Cop (T.map (Function.Embedding.subtype _))).indicator f x with hSdef
  have hEq : ∀ T : Finset (EP 𝔪), X = (∏ P ∈ T, ∑' e, A P.1 e) * S T := by
    intro T
    have := sieve_eq h (T.map (Function.Embedding.subtype _)) (by
      intro Q hQ
      obtain ⟨P, -, rfl⟩ := Finset.mem_map.1 hQ
      exact P.2)
    rw [Finset.prod_map] at this
    exact this
  have hS1 : Tendsto S atTop (𝓝 1) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨T₀, hT₀⟩ := sieve_tail h hε
    exact ⟨T₀, fun T hT => by rw [dist_eq_norm]; exact hT₀ T hT⟩
  constructor
  · have hev : ∀ᶠ T in atTop, ∏ P ∈ T, ∑' e, A P.1 e = X / S T := by
      filter_upwards [hS1.eventually_ne one_ne_zero] with T hT
      rw [hEq T, mul_div_assoc, div_self hT, mul_one]
    show Tendsto _ (SummationFilter.unconditional _).filter _
    simp only [SummationFilter.unconditional_filter]
    have : Tendsto (fun T => X / S T) atTop (𝓝 (X / 1)) := tendsto_const_nhds.div hS1 one_ne_zero
    rw [div_one] at this
    exact this.congr' (hev.mono fun T hT => hT.symm)
  · intro hne hX
    obtain ⟨T, hT⟩ := (hS1.eventually_ne one_ne_zero).exists
    have := hEq T
    rw [hX] at this
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun P _ => hne P) hT this.symm

end sieve

end C3A

end ArtinPrimitiveRoots

end
end

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

end T12B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3A_Euler1: Euler products of `L(s, χ)` and `ζ^S(s)` over the exterior primes

From `euler4` (one active coordinate) and T12B's sieve:
* `hasProd_inv_LSeries`: `∏_{P ∉ S} (1 − χ(P) N P^{-s}) = L(s, χ)⁻¹` for `Re s > 1`;
* `hasProd_zetaS`: `∏_{P ∉ S} (1 − N P^{-s})⁻¹ = ∏_{P ⊇ 𝔪} (1 − N P^{-s}) · ζ_F(s)`. -/

open NumberField Filter Topology

namespace ArtinPrimitiveRoots

namespace C3A

variable {F : Type*} [Field F] [NumberField F]

lemma sup_mul_eq_top_iff {𝔪 I J : Ideal (𝓞 F)} :
    I * J ⊔ 𝔪 = ⊤ ↔ I ⊔ 𝔪 = ⊤ ∧ J ⊔ 𝔪 = ⊤ := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [eq_top_iff, ← h]; exact sup_le_sup_right Ideal.mul_le_left _
    · rw [eq_top_iff, ← h]; exact sup_le_sup_right Ideal.mul_le_right _
  · rintro ⟨h1, h2⟩
    rw [Ideal.mul_sup_eq_of_coprime_left h1, h2]

/-! ### The one-variable Euler product from `euler4` -/

section one

variable {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (s : ℂ)

/-- The function `χ(I) N I^{-s}` placed on the first coordinate. -/
noncomputable def f1 (x : Tup F) : ℂ := by
  classical exact if x.2 = (⊤, ⊤, ⊤) then T12B.gs χ s x.1 else 0

/-- Its local factors. -/
noncomputable def A1 (P : Ideal (𝓞 F)) (e : Exps) : ℂ := by
  classical exact if e.2 = (0, 0, 0) then T12B.gs χ s P ^ e.1 else 0

lemma pow_mul_eq_top {P I : Ideal (𝓞 F)} (hP : P.IsPrime) {k : ℕ} :
    P ^ k * I = ⊤ ↔ k = 0 ∧ I = ⊤ := by
  constructor
  · intro h
    rcases k with _ | k
    · simp only [pow_zero, one_mul] at h; exact ⟨rfl, h⟩
    · exfalso; apply hP.ne_top
      rw [eq_top_iff, ← h, pow_succ', mul_assoc]; exact Ideal.mul_le_left
  · rintro ⟨rfl, rfl⟩; simp

theorem euler1 (hχ : ∀ I, ‖χ.toFun I‖ ≤ 1) (hs : 1 < s.re) :
    HasProd (fun P : EP 𝔪 => (1 - χ.toFun P.1 * ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹)
      (χ.LSeries s) ∧ χ.LSeries s ≠ 0 := by
  classical
  have hg : ∀ P : Ideal (𝓞 F), IsEP 𝔪 P → ‖T12B.gs χ s P‖ < 1 := by
    intro P hP
    have h2 := two_le_absNorm hP.1 hP.2.1
    refine lt_of_le_of_lt (T12B.norm_gs_le χ hχ (le_refl s.re) P) ?_
    have hq : (1 : ℝ) < ((Ideal.absNorm P : ℕ) : ℝ) := by exact_mod_cast h2
    exact Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  have hinj : Function.Injective (fun c : Ideal (𝓞 F) => ((c, ⊤, ⊤, ⊤) : Tup F)) := by
    intro a b h; simpa using h
  have hsupp : Function.support (f1 χ s) ⊆ Set.range (fun c : Ideal (𝓞 F) => ((c, ⊤, ⊤, ⊤) : Tup F)) := by
    intro x hx
    simp only [Function.mem_support, f1] at hx
    split_ifs at hx with h
    swap
    · exact absurd rfl hx
    obtain ⟨x1, x2⟩ := x
    simp only at h
    exact ⟨x1, by rw [h]⟩
  have hcomp : (f1 χ s) ∘ (fun c : Ideal (𝓞 F) => ((c, ⊤, ⊤, ⊤) : Tup F)) = T12B.gs χ s := by
    funext c; simp [f1]
  have hsumm : Summable (T12B.gs χ s) := T12B.summable_gs χ hχ hs
  have hH : EulerHyp 𝔪 (f1 χ s) (A1 χ s) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      simp only [f1]
      split_ifs with h
      · obtain ⟨x1, x2⟩ := x
        simp only at h
        subst h
        have : ¬ IsExterior 𝔪 x1 := fun h' => hx ⟨h', ⟨top_ne_bot, top_sup_eq _⟩,
          ⟨top_ne_bot, top_sup_eq _⟩, ⟨top_ne_bot, top_sup_eq _⟩⟩
        simp only [T12B.gs]
        rw [(χ.eq_zero_iff' x1).2 (by
          by_contra hc; push Not at hc; exact this hc), zero_mul]
      · rfl
    · simp [f1, one4, T12B.gs_top]
    · intro P hP e y hyO hyP
      obtain ⟨e1, e2, e3, e4⟩ := e
      obtain ⟨y1, y2, y3, y4⟩ := y
      simp only [f1, A1, pw, Prod.mk.injEq]
      by_cases he : e2 = 0 ∧ e3 = 0 ∧ e4 = 0
      · obtain ⟨rfl, rfl, rfl⟩ := he
        simp only [pow_zero, one_mul, and_self, if_true]
        split_ifs
        · have hpow : T12B.gs χ s (P ^ e1) = T12B.gs χ s P ^ e1 := by
            induction e1 with
            | zero => simp [T12B.gs_top]
            | succ k ih => rw [pow_succ, T12B.gs_mul, ih, pow_succ]
          rw [T12B.gs_mul, hpow]
        · rw [mul_zero]
      · rw [if_neg, if_neg he, zero_mul]
        rintro ⟨h2, h3, h4⟩
        rw [pow_mul_eq_top hP.1] at h2 h3 h4
        exact he ⟨h2.1, h3.1, h4.1⟩
    · rw [← hinj.summable_iff (fun x hx => by
        by_contra h; exact hx (hsupp (norm_ne_zero_iff.1 h)))]
      rw [show (fun x => ‖f1 χ s x‖) ∘ (fun c : Ideal (𝓞 F) => ((c, ⊤, ⊤, ⊤) : Tup F)) =
        fun c => ‖T12B.gs χ s c‖ by rw [← hcomp]; rfl]
      exact Summable.of_norm_bounded (T12B.summable_absNorm_rpow hs)
        (fun c => by rw [norm_norm]; exact T12B.norm_gs_le χ hχ le_rfl c)
    · intro P hP
      have hgeo := summable_geometric_of_lt_one (norm_nonneg _) (hg P hP)
      have hinj' : Function.Injective (fun k : ℕ => ((k, 0, 0, 0) : Exps)) := by
        intro a b h; simpa using h
      rw [← hinj'.summable_iff (fun e he => by
        obtain ⟨e1, e2⟩ := e
        simp only [A1]
        rw [if_neg, norm_zero]
        intro h; exact he ⟨e1, by rw [h]⟩)]
      refine hgeo.congr fun k => ?_
      simp [A1]
  obtain ⟨hprod, hne⟩ := euler4 hH
  have htsum : ∑' x, f1 χ s x = χ.LSeries s := by
    rw [← hinj.tsum_eq hsupp]
    show ∑' c, ((f1 χ s) ∘ (fun c : Ideal (𝓞 F) => ((c, ⊤, ⊤, ⊤) : Tup F))) c = _
    rw [hcomp, T12B.lseries_eq_tsum χ hχ hs]
  have hloc : ∀ P : EP 𝔪, ∑' e, A1 χ s P.1 e =
      (1 - χ.toFun P.1 * ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹ := by
    intro P
    have hinj' : Function.Injective (fun k : ℕ => ((k, 0, 0, 0) : Exps)) := by
      intro a b h; simpa using h
    rw [← hinj'.tsum_eq (fun e he => by
      obtain ⟨e1, e2⟩ := e
      simp only [Function.mem_support, A1] at he
      split_ifs at he with h'
      · exact ⟨e1, by rw [h']⟩
      · exact absurd rfl he)]
    simp only [A1, if_true]
    exact tsum_geometric_of_norm_lt_one (hg P.1 P.2)
  rw [htsum] at hprod hne
  refine ⟨?_, ?_⟩
  · exact hprod.congr_fun fun P => (hloc P).symm
  · refine hne fun P => ?_
    rw [hloc P]
    refine inv_ne_zero fun h => ?_
    have := hg P.1 P.2
    rw [sub_eq_zero] at h
    have h' : T12B.gs χ s P.1 = 1 := h.symm
    rw [h', norm_one] at this
    exact lt_irrefl _ this

end one

/-! ### `ζ^S` -/

end C3A

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3K_Hecke: an abelian Artin character as a `HeckeChar` of modulus its conductor

For `K` totally complex, `M/K` Galois and `ψ : Gal(M/K) →* ℂˣ`, library 41aa80ff gives a narrow ray
class character `χ_R` mod `𝔣 = conductor ψ` with `χ_R(v) = localValue ψ v`. Then
`psiH I = χ_R([I])` (on `I` coprime to `𝔣`) is a `HeckeChar K 𝔣` with `psiH = idealValue ψ` on nonzero
ideals, so `ArtinL.Abelian.LSeries ψ = psiH.LSeries`. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.InfinitePlace IsDedekindDomain Deep.NTSupply nonZeroDivisors

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ)

/-- The ray class character of 41aa80ff. -/
def chiR : NarrowRayClassGroup K (ArtinL.Abelian.conductor ψ) →* ℂ :=
  (ArtinL.Abelian.exists_narrowRayClassChar_conductor_eq_localValue_u0 K M ψ).choose

open scoped Classical in
lemma chiR_spec :
    (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ ArtinL.Abelian.conductor ψ),
        chiR ψ (primeClass K (ArtinL.Abelian.conductor ψ) v hv) = ArtinL.Abelian.localValue ψ v) ∧
      (chiR ψ = 1 ↔ ψ = 1) ∧
      (∀ (α : 𝓞 K) (hα : α ≠ 0)
        (hc : principalUnit K α hα ∈ coprimeToModulus K (ArtinL.Abelian.conductor ψ)),
        α - 1 ∈ ArtinL.Abelian.conductor ψ →
          chiR ψ (NarrowRayClassGroup.mk K (ArtinL.Abelian.conductor ψ) ⟨principalUnit K α hα, hc⟩) =
            ∏ w ∈ (Finset.univ.filter fun w : {w : InfinitePlace K // w.IsReal} =>
                ¬ ArtinL.Abelian.IsPlusAt ψ w.1),
              ((SignType.sign (embedding_of_isReal w.2 (α : K)) : ℤ) : ℂ)) := by
  have h := (ArtinL.Abelian.exists_narrowRayClassChar_conductor_eq_localValue_u0 K M ψ).choose_spec
  exact ⟨h.1, h.2.1, h.2.2.1⟩

lemma chiR_ne_zero (C : NarrowRayClassGroup K (ArtinL.Abelian.conductor ψ)) : chiR ψ C ≠ 0 := by
  intro h
  have : chiR ψ C * chiR ψ C⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [h, zero_mul] at this; exact zero_ne_one this

lemma sup_eq_top_iff_not_dvd (v : HeightOneSpectrum (𝓞 K)) (𝔣 : Ideal (𝓞 K)) :
    v.asIdeal ⊔ 𝔣 = ⊤ ↔ ¬ v.asIdeal ∣ 𝔣 := by
  rw [Ideal.dvd_iff_le]
  constructor
  · intro h hle
    apply v.isPrime.ne_top; rw [← h]; exact le_antisymm le_sup_left (sup_le le_rfl hle)
  · intro h
    by_contra hne
    have e := v.isMaximal.eq_of_le hne le_sup_left
    exact h (e ▸ le_sup_right)

open Classical in
lemma cls_mul {𝔣 : Ideal (𝓞 K)} {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥ ∧ I ⊔ 𝔣 = ⊤)
    (hJ : J ≠ ⊥ ∧ J ⊔ 𝔣 = ⊤) (hIJ : I * J ≠ ⊥ ∧ I * J ⊔ 𝔣 = ⊤) :
    T12A.cls 𝔣 (I * J) = T12A.cls 𝔣 I * T12A.cls 𝔣 J := by
  rw [T12A.cls, T12A.cls, T12A.cls, dif_pos hI, dif_pos hJ, dif_pos hIJ, ← map_mul]
  congr 1
  apply Subtype.ext
  show FractionalIdeal.mk0 K ⟨I * J, _⟩ = FractionalIdeal.mk0 K ⟨I, _⟩ * FractionalIdeal.mk0 K ⟨J, _⟩
  rw [← map_mul]; rfl

open Classical in
/-- The Hecke character `psiH` of modulus `conductor ψ`. -/
def psiH (hK : ∀ w : InfinitePlace K, w.IsComplex) :
    HeckeChar K (ArtinL.Abelian.conductor ψ) where
  toFun I := if I ≠ ⊥ ∧ I ⊔ ArtinL.Abelian.conductor ψ = ⊤ then
    chiR ψ (T12A.cls (ArtinL.Abelian.conductor ψ) I) else 0
  map_mul' I J := by
    have hb : I * J ≠ ⊥ ↔ I ≠ ⊥ ∧ J ≠ ⊥ := by
      simp only [ne_eq, ← Ideal.zero_eq_bot, mul_eq_zero, not_or]
    by_cases hI : I ≠ ⊥ ∧ I ⊔ ArtinL.Abelian.conductor ψ = ⊤ <;>
      by_cases hJ : J ≠ ⊥ ∧ J ⊔ ArtinL.Abelian.conductor ψ = ⊤
    · have hIJ : I * J ≠ ⊥ ∧ I * J ⊔ ArtinL.Abelian.conductor ψ = ⊤ :=
        ⟨hb.2 ⟨hI.1, hJ.1⟩, C3A.sup_mul_eq_top_iff.2 ⟨hI.2, hJ.2⟩⟩
      rw [if_pos hIJ, if_pos hI, if_pos hJ, cls_mul hI hJ hIJ, map_mul]
    · rw [if_neg hJ, mul_zero, if_neg]
      rintro ⟨h1, h2⟩; exact hJ ⟨(hb.1 h1).2, (C3A.sup_mul_eq_top_iff.1 h2).2⟩
    · rw [if_neg hI, zero_mul, if_neg]
      rintro ⟨h1, h2⟩; exact hI ⟨(hb.1 h1).1, (C3A.sup_mul_eq_top_iff.1 h2).1⟩
    · rw [if_neg hI, zero_mul, if_neg]
      rintro ⟨h1, h2⟩; exact hI ⟨(hb.1 h1).1, (C3A.sup_mul_eq_top_iff.1 h2).1⟩
  eq_zero_iff' I := by
    split_ifs with h
    · simp only [chiR_ne_zero, false_iff, not_or, not_not]; exact h
    · simp only [true_iff]; by_contra h'; push Not at h'; exact h h'
  map_principal' α hα h1 := by
    have hc : Ideal.span {α} ≠ ⊥ ∧ Ideal.span {α} ⊔ ArtinL.Abelian.conductor ψ = ⊤ :=
      ⟨T12A.span_ne_bot hα, T12A.span_sup_eq_top h1⟩
    rw [if_pos hc, T12A.cls, dif_pos hc]
    have hpc : principalUnit K α hα ∈ coprimeToModulus K (ArtinL.Abelian.conductor ψ) :=
      (T12A.mk0_mem_coprimeToModulus_iff _).2 hc.2
    have := (chiR_spec ψ).2.2 α hα hpc h1
    refine (congrArg (chiR ψ) (congrArg (NarrowRayClassGroup.mk K (ArtinL.Abelian.conductor ψ))
      (Subtype.ext rfl))).trans (this.trans ?_)
    apply Finset.prod_eq_one
    intro w _
    exact absurd w.2 (not_isReal_iff_isComplex.2 (hK w.1))

variable (hK : ∀ w : InfinitePlace K, w.IsComplex)

lemma psiH_prime (v : HeightOneSpectrum (𝓞 K)) :
    (psiH ψ hK).toFun v.asIdeal = ArtinL.Abelian.localValue ψ v := by
  classical
  by_cases hv : v.asIdeal ∣ ArtinL.Abelian.conductor ψ
  · have h1 : ¬ (v.asIdeal ≠ ⊥ ∧ v.asIdeal ⊔ ArtinL.Abelian.conductor ψ = ⊤) := fun h =>
      (sup_eq_top_iff_not_dvd v _).1 h.2 hv
    have h2 := (ArtinL.Abelian.dvd_conductor_iff_not_isUnramifiedAt K M ψ v).1 hv
    show (if _ then _ else _) = _
    rw [if_neg h1, ArtinL.Abelian.localValue, if_neg h2]
  · have h1 : v.asIdeal ≠ ⊥ ∧ v.asIdeal ⊔ ArtinL.Abelian.conductor ψ = ⊤ :=
      ⟨v.ne_bot, (sup_eq_top_iff_not_dvd v _).2 hv⟩
    show (if _ then _ else _) = _
    rw [if_pos h1, T12A.cls, dif_pos h1, ← (chiR_spec ψ).1 v hv]
    rfl

lemma psiH_eq_idealValue {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    (psiH ψ hK).toFun I = ArtinL.Abelian.idealValue ψ I := by
  rw [T12A.heckeChar_eq_finprod (psiH ψ hK) (ArtinL.Abelian.localValue ψ) (psiH_prime ψ hK) I hI,
    ArtinL.Abelian.idealValue]

theorem LSeries_eq_psiH (s : ℂ) : ArtinL.Abelian.LSeries ψ s = (psiH ψ hK).LSeries s := by
  classical
  rw [ArtinL.Abelian.LSeries, HeckeChar.LSeries]
  refine LSeries_congr (fun {n} hn => ?_) s
  rw [ArtinL.Abelian.coeff, if_neg hn, HeckeChar.coeff,
    finsum_mem_eq_finite_toFinset_sum _ (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n)]
  refine Finset.sum_congr rfl fun I hI => ?_
  have hI0 : I ≠ ⊥ := by
    intro h; rw [Set.Finite.mem_toFinset] at hI
    rw [h] at hI; simp at hI; exact hn hI.symm
  exact (psiH_eq_idealValue ψ hK hI0).symm

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3K_Conv: the convexity bound for an abelian Artin `L`-function with explicit conductor

For `K` totally complex, `ψ ≠ 1`: the entire continuation `L` of `L(s, ψ)` satisfies
`‖L(s)‖ ≤ C (N 𝔣_ψ)^{1/2+δ} (1 + |t|)^{3 r₂}` on `−δ ≤ Re s ≤ 4`, with `C` depending only on `K`
and `δ`, provided `L` has some polynomial growth on the strip (`GrowthHyp`, from L3K_Growth).

Inputs: the FE 3508ac81 (`Λ(1−s) = W Λ'(s)`), `|W| = 1` from `Λ' = conj ∘ Λ ∘ conj`, the Gamma
ratio of L3K_Gamma, and Phragmén–Lindelöf 40726dc6. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.InfinitePlace IsDedekindDomain Complex

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

/-- Identity theorem for entire functions agreeing on `Re s > 1`. -/
lemma entire_ext {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h : ∀ s : ℂ, 1 < s.re → f s = g s) : f = g := by
  have hfa : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have hga : AnalyticOnNhd ℂ g Set.univ := hg.differentiableOn.analyticOnNhd isOpen_univ
  refine AnalyticOnNhd.eq_of_eventuallyEq hfa hga (z₀ := 2) ?_
  have ho : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [ho.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with s hs using h s hs

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ)

lemma nrRealPlaces_eq_zero (hK : ∀ w : InfinitePlace K, w.IsComplex) : nrRealPlaces K = 0 := by
  haveI : IsTotallyComplex K := ⟨hK⟩
  exact IsTotallyComplex.nrRealPlaces_eq_zero K

/-- `D = |d_K| N 𝔣_ψ`. -/
def Dψ : ℝ := |(discr K : ℝ)| * (Ideal.absNorm (ArtinL.Abelian.conductor ψ) : ℝ)

lemma one_le_Dψ : 1 ≤ Dψ ψ := by
  have h1 : (1 : ℝ) ≤ |(discr K : ℝ)| := by
    have h0 := NumberField.discr_ne_zero K
    have : (1 : ℤ) ≤ |discr K| := Int.one_le_abs h0
    exact_mod_cast this
  have h2 : (1 : ℝ) ≤ (Ideal.absNorm (ArtinL.Abelian.conductor ψ) : ℝ) := by
    exact_mod_cast ArtinL.Abelian.absNorm_conductor_pos ψ
  rw [Dψ]; nlinarith

lemma completedLSeries_eq (hK : ∀ w : InfinitePlace K, w.IsComplex) (s : ℂ) :
    ArtinL.Abelian.completedLSeries ψ s =
      ((Dψ ψ : ℝ) : ℂ) ^ (s / 2) * Gammaℂ s ^ nrComplexPlaces K * ArtinL.Abelian.LSeries ψ s := by
  have hp : ArtinL.Abelian.nPlus ψ = 0 := by
    have := ArtinL.Abelian.nPlus_le ψ; rw [nrRealPlaces_eq_zero hK] at this; omega
  have hm : ArtinL.Abelian.nMinus ψ = 0 := by
    rw [ArtinL.Abelian.nMinus, nrRealPlaces_eq_zero hK]; simp
  rw [ArtinL.Abelian.completedLSeries, hp, hm, pow_zero, pow_zero, mul_one, mul_one, Dψ]

lemma LSeries_two_ne_zero (hK : ∀ w : InfinitePlace K, w.IsComplex) :
    ArtinL.Abelian.LSeries ψ 2 ≠ 0 := by
  rw [LSeries_eq_psiH ψ hK]
  exact (C3A.euler1 (psiH ψ hK) 2
    (T12A.norm_heckeChar_le (ArtinL.Abelian.conductor_ne_bot ψ) _) (by norm_num)).2

/-- The growth hypothesis needed for Phragmén–Lindelöf (supplied by c46e3955 in L3K_Growth). -/
def GrowthHyp (δ : ℝ) : Prop :=
  ∀ L : ℂ → ℂ, Differentiable ℂ L → (∀ s : ℂ, 1 < s.re → L s = ArtinL.Abelian.LSeries ψ s) →
    ∃ (A : ℝ) (N : ℕ), ∀ w : ℂ, -δ ≤ w.re → w.re ≤ 1 + δ → ‖L w‖ ≤ A * (1 + |w.im|) ^ N

/-- The continuation `L = Λ · D^{-s/2} · Γ_ℂ(s)^{-r₂}`. -/
def Lfun (Λ : ℂ → ℂ) (s : ℂ) : ℂ :=
  Λ s * ((Dψ ψ : ℝ) : ℂ) ^ (-s / 2) * ((Gammaℂ s)⁻¹) ^ nrComplexPlaces K

lemma Lfun_differentiable {Λ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ) :
    Differentiable ℂ (Lfun ψ Λ) := by
  have hD : ((Dψ ψ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans_le (one_le_Dψ ψ)).ne'
  refine (hΛ.mul ?_).mul (differentiable_Gammaℂ_inv.pow _)
  intro s
  exact ((differentiableAt_id.neg).div_const 2).const_cpow (Or.inl hD)

lemma Lfun_eq (hK : ∀ w : InfinitePlace K, w.IsComplex) {Λ : ℂ → ℂ}
    (hΛre : ∀ s : ℂ, 1 < s.re → Λ s = ArtinL.Abelian.completedLSeries ψ s) {s : ℂ}
    (hs : 1 < s.re) : Lfun ψ Λ s = ArtinL.Abelian.LSeries ψ s := by
  have hD : ((Dψ ψ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans_le (one_le_Dψ ψ)).ne'
  have hG : Gammaℂ s ≠ 0 := by
    rw [Gammaℂ_def]
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero_of_re_pos (by linarith))
    rw [Ne, Complex.cpow_eq_zero_iff]; push Not; intro h
    exact absurd h (by simp [Real.pi_ne_zero])
  rw [Lfun, hΛre s hs, completedLSeries_eq ψ hK]
  have hc : ((Dψ ψ : ℝ) : ℂ) ^ (s / 2) * ((Dψ ψ : ℝ) : ℂ) ^ (-s / 2) = 1 := by
    rw [← Complex.cpow_add _ _ hD, show s / 2 + -s / 2 = 0 by ring, Complex.cpow_zero]
  have hg : Gammaℂ s ^ nrComplexPlaces K * (Gammaℂ s)⁻¹ ^ nrComplexPlaces K = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hG, one_pow]
  calc _ = (((Dψ ψ : ℝ) : ℂ) ^ (s / 2) * ((Dψ ψ : ℝ) : ℂ) ^ (-s / 2)) *
        (Gammaℂ s ^ nrComplexPlaces K * (Gammaℂ s)⁻¹ ^ nrComplexPlaces K) *
        ArtinL.Abelian.LSeries ψ s := by ring
    _ = _ := by rw [hc, hg, one_mul, one_mul]

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3K_Growth: the a-priori growth hypothesis for Phragmén–Lindelöf

For `ψ ≠ 1`, the entire continuation of `L(s, ψ)` has polynomial growth on every vertical strip:
library c46e3955 applied to the idelic character `η` of f982cbad attached to `χ_R` (41aa80ff), with
`T` the primes dividing the conductor, and the Euler product of `psiH` (C3A `euler1`).
`η` is nontrivial on the norm-one ideles: otherwise `η = |·|^{it}` (a55d6ac4), finite order forces
`t = 0` (86a18a2c), and then `χ_R = 1` because the prime classes generate the ray class group. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.InfinitePlace IsDedekindDomain Deep.NTSupply nonZeroDivisors
  AutomorphicForm NumberField.TateGlobal NumberField.AdelicLevel

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

section Gen

variable {K : Type} [Field K] [NumberField K]

/-- The prime classes generate the narrow ray class group. -/
theorem eq_one_of_primeClass {𝔣 : Ideal (𝓞 K)} (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
    (h : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣), χ (primeClass K 𝔣 v hv) = 1) :
    χ = 1 := by
  classical
  set χu : NarrowRayClassGroup K 𝔣 →* ℂˣ := χ.toHomUnits
  set Kr : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
    ((χu.comp (NarrowRayClassGroup.mk K 𝔣)).ker).map (coprimeToModulus K 𝔣).subtype
  have hP : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 → primeUnit K v ∈ Kr := by
    intro v hv
    refine ⟨⟨primeUnit K v, primeUnit_mem_coprimeToModulus K hv⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply]
    apply Units.ext
    rw [MonoidHom.coe_toHomUnits, Units.val_one]
    exact h v hv
  have hall : ∀ y : ↥(coprimeToModulus K 𝔣), (y : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ Kr := by
    intro y
    set I : FractionalIdeal (𝓞 K)⁰ K := ((y : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
    have hI : I ≠ 0 := Units.ne_zero _
    have hfin := FractionalIdeal.finite_factors (K := K) I
    rw [Filter.eventually_cofinite] at hfin
    set S := hfin.toFinset
    have hy : (y : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ∏ v ∈ S, primeUnit K v ^ FractionalIdeal.count K v I := by
      apply Units.ext
      rw [Units.coe_prod]
      conv_lhs => rw [show ((y : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = I from rfl,
        ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI]
      rw [finprod_eq_prod_of_mulSupport_subset]
      · refine Finset.prod_congr rfl fun v _ => ?_
        rw [Units.val_zpow_eq_zpow_val, primeUnit_val]
      · intro v hv
        rw [Set.Finite.coe_toFinset]
        intro h0
        apply hv
        simp only at h0 ⊢
        rw [h0, zpow_zero]
    rw [hy]
    refine Subgroup.prod_mem _ fun v hv => ?_
    by_cases hd : v.asIdeal ∣ 𝔣
    · have : FractionalIdeal.count K v I = 0 := ((mem_coprimeToModulus_iff K).1 y.2) v hd
      rw [this, zpow_zero]; exact Subgroup.one_mem _
    · exact Subgroup.zpow_mem _ (hP v hd) _
  refine MonoidHom.ext fun C => ?_
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective C
  obtain ⟨z, hz, hzy⟩ := hall y
  have hzy' : z = y := Subtype.ext hzy
  rw [hzy'] at hz
  rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply] at hz
  have := congrArg (fun x : ℂˣ => (x : ℂ)) hz
  simp only [MonoidHom.coe_toHomUnits, Units.val_one] at this
  rw [MonoidHom.one_apply]
  exact this

/-- An idelic character admitting `𝔣` as a modulus is unramified at `v ∤ 𝔣`. -/
theorem isUnramifiedCharAt_of_admitsModulus {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    {η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hη : HeckeCharacter.AdmitsModulus K η 𝔣)
    {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣) : IsUnramifiedCharAt η v := by
  classical
  intro t ht hti
  unfold localChar
  apply hη
  · rfl
  · intro w
    by_cases hw : w = v
    · subst hw
      have hval : Valued.v ((t : w.adicCompletion K)) = 1 := by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ht hti
        apply le_antisymm ht
        have h1 : Valued.v ((t : w.adicCompletion K)) * Valued.v (((t⁻¹ : (w.adicCompletion K)ˣ) :
            w.adicCompletion K)) = 1 := by
          rw [← map_mul, Units.mul_inv, map_one]
        by_contra hlt
        push Not at hlt
        have : Valued.v ((t : w.adicCompletion K)) * Valued.v (((t⁻¹ : (w.adicCompletion K)ˣ) :
            w.adicCompletion K)) < 1 :=
          mul_lt_one_of_lt_of_le hlt hti
        rw [h1] at this; exact lt_irrefl _ this
      have hm : HeckeCharacter.idealMultiplicity K w 𝔣 = 0 := by
        unfold HeckeCharacter.idealMultiplicity
        by_contra h0
        exact hv ((Associates.count_ne_zero_iff_dvd h𝔣 w.irreducible).1 h0)
      show Valued.v (((localUnit (𝓞 K) K w t : (FiniteAdeleRing (𝓞 K) K)ˣ) :
          FiniteAdeleRing (𝓞 K) K) w) = 1 ∧ Valued.v (((localUnit (𝓞 K) K w t :
          (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w - 1) ≤ _
      rw [localUnit_apply_self, hm, Nat.cast_zero, neg_zero, WithZero.exp_zero]
      refine ⟨hval, ?_⟩
      refine (Valuation.map_sub _ _ _).trans (max_le hval.le (by rw [map_one]))
    · show Valued.v (((localUnit (𝓞 K) K v t : (FiniteAdeleRing (𝓞 K) K)ˣ) :
          FiniteAdeleRing (𝓞 K) K) w) = 1 ∧ Valued.v (((localUnit (𝓞 K) K v t :
          (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w - 1) ≤ _
      rw [localUnit_apply_of_ne _ _ _ _ hw, map_one, sub_self, map_zero]
      exact ⟨rfl, zero_le⟩

end Gen

section Main

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ)

/-- The primes dividing the conductor. -/
def condPrimes : Finset (HeightOneSpectrum (𝓞 K)) :=
  (Ideal.finite_factors (R := 𝓞 K) (ArtinL.Abelian.conductor_ne_bot ψ)).toFinset

lemma mem_condPrimes (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ condPrimes ψ ↔ v.asIdeal ∣ ArtinL.Abelian.conductor ψ := by
  rw [condPrimes, Set.Finite.mem_toFinset]; rfl

/-- `EP 𝔣 ≃ {v // v ∉ T}`. -/
def epEquiv : C3A.EP (ArtinL.Abelian.conductor ψ) ≃ {v : HeightOneSpectrum (𝓞 K) // v ∉ condPrimes ψ} where
  toFun P := ⟨⟨P.1, P.2.1, P.2.2.1⟩, by
    rw [mem_condPrimes, ← sup_eq_top_iff_not_dvd]; exact P.2.2.2⟩
  invFun v := ⟨v.1.asIdeal, v.1.isPrime, v.1.ne_bot, by
    rw [sup_eq_top_iff_not_dvd, ← mem_condPrimes]; exact v.2⟩
  left_inv P := rfl
  right_inv v := rfl

/-- **The growth hypothesis holds.** -/
theorem growthHyp (hK : ∀ w : InfinitePlace K, w.IsComplex) (hψ : ψ ≠ 1) (δ : ℝ) : GrowthHyp ψ δ := by
  classical
  intro L hL hLre
  set 𝔣 := ArtinL.Abelian.conductor ψ
  have h𝔣 : 𝔣 ≠ ⊥ := ArtinL.Abelian.conductor_ne_bot ψ
  set χu := (chiR ψ).toHomUnits
  obtain ⟨η, hfin, hadm, hunit, hval⟩ := LT.HeckeChar.exists_heckeCharOfRayClassChar K 𝔣 χu
  have hvalC : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣),
      ((η (uniformizerIdele K v) : ℂˣ) : ℂ) = ArtinL.Abelian.localValue ψ v := by
    intro v hv
    rw [hval v hv, MonoidHom.coe_toHomUnits]; exact (chiR_spec ψ).1 v hv
  -- nontrivial on norm-one ideles
  have hnt : ∃ x ∈ normOneIdeles K, η x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t, ht⟩ := exists_eq_normPowChar_of_forall_mem_normOneIdeles K η hfin.continuous hunit hcon
    obtain ⟨n, hn, hpow⟩ := hfin.isOfFinOrder.exists_pow_eq_one
    have hval_t : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((η z : ℂˣ) : ℂ) = ((ideleNorm K z : ℝ) : ℂ) ^ (Complex.I * t) := by
      intro z; rw [ht]; rfl
    have ht0 : t = 0 := by
      by_contra ht0
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      obtain ⟨z, -, hz⟩ := exists_ideleNorm_eq_and_snd_eq_one K
        (Real.exp (Real.pi / (t * n))) (Real.exp_pos _)
      have h1 : ((η z : ℂˣ) : ℂ) ^ n = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hpow, MonoidHom.one_apply,
          Units.val_one]
      set c := Real.pi / (t * n)
      have hc : ((Real.exp c : ℝ) : ℂ) ^ (Complex.I * t) = Complex.exp (c * (Complex.I * t)) := by
        rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos c).ne'),
          ← Complex.ofReal_log (Real.exp_pos c).le, Real.log_exp]
      rw [hval_t, hz, hc, ← Complex.exp_nat_mul] at h1
      have e : (n : ℂ) * (c * (Complex.I * t)) = Real.pi * Complex.I := by
        have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
        have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
        simp only [c]; push_cast; field_simp
      rw [e, Complex.exp_pi_mul_I] at h1
      norm_num at h1
    have hη1 : ∀ z, η z = 1 := by
      intro z; apply Units.ext; rw [hval_t, ht0]; simp
    apply hψ
    rw [← (chiR_spec ψ).2.1]
    refine eq_one_of_primeClass (chiR ψ) fun v hv => ?_
    rw [(chiR_spec ψ).1 v hv, ← hvalC v hv, hη1, Units.val_one]
  -- the Euler product
  have hLE : ∀ s : ℂ, 1 < s.re →
      L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ condPrimes ψ},
        (1 - (if IsUnramifiedCharAt η v.1 then ((η (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
    intro s hs
    have hχ := T12A.norm_heckeChar_le h𝔣 (psiH ψ hK)
    rw [hLre s hs, LSeries_eq_psiH ψ hK, ← (C3A.euler1 (psiH ψ hK) s hχ hs).1.tprod_eq,
      ← (epEquiv ψ).tprod_eq]
    refine tprod_congr fun P => ?_
    have hv : ¬ ((epEquiv ψ P).1).asIdeal ∣ 𝔣 := by
      rw [← mem_condPrimes]; exact (epEquiv ψ P).2
    rw [if_pos (isUnramifiedCharAt_of_admitsModulus h𝔣 hadm hv), hvalC _ hv,
      ← psiH_prime ψ hK]
    rfl
  exact exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc K η
    hfin.isIdeleClassChar hfin.continuous hunit hnt (condPrimes ψ) (-δ) (1 + δ) L hL hLE

end Main

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3F_Zeta: `ζ_M = ζ_K · L(ψ)` for a quadratic extension

For `M/K` Galois with an injective character `ψ` of order `2` (so `[M : K] = 2`), the Euler factors
of `ζ_M` over a prime `v` of `K` multiply to `(1 − Nv^{-s})^{-1} (1 − ψ(v) Nv^{-s})^{-1}`
(`g |I| f = 2`; ramified: `g = f = 1`; `ψ(Frob) = 1`: `Frob = 1`, `f = 1`, `g = 2`;
`ψ(Frob) = −1`: `f = 2`, `g = 1`). Grouping the Euler product of `ζ_M` by `v` gives the identity. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin Polynomial

open scoped Pointwise

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3F

/-- A finite field in which `x^q = x` for all `x` has at most `q` elements. -/
lemma card_le_of_forall_pow_eq {k : Type*} [Field k] [Fintype k] {q : ℕ} (hq : 1 < q)
    (h : ∀ x : k, x ^ q = x) : Fintype.card k ≤ q := by
  classical
  have hP : (X ^ q - X : k[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k hq
  calc Fintype.card k = (Finset.univ : Finset k).card := rfl
    _ ≤ (X ^ q - X : k[X]).roots.toFinset.card := by
        refine Finset.card_le_card fun x _ => ?_
        rw [Multiset.mem_toFinset, mem_roots hP]
        simp [h x]
    _ ≤ Multiset.card (X ^ q - X : k[X]).roots := Multiset.toFinset_card_le _
    _ ≤ (X ^ q - X : k[X]).natDegree := card_roots' _
    _ = q := FiniteField.X_pow_card_sub_X_natDegree_eq k hq

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M]

/-- The primes of `M` above `v`. -/
abbrev Fib (v : HeightOneSpectrum (𝓞 K)) : Type :=
  {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v}

/-- `Fib v ≃ primesOver v`. -/
def fibEquiv (v : HeightOneSpectrum (𝓞 K)) : Fib (M := M) v ≃ v.asIdeal.primesOver (𝓞 M) where
  toFun w := ⟨w.1.asIdeal, w.1.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩⟩
  invFun Q := ⟨⟨Q.1, Q.2.1, by
      haveI := Q.2.2
      exact Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q.1⟩, by
      ext1
      exact Q.2.2.over.symm⟩
  left_inv w := rfl
  right_inv Q := rfl

instance (v : HeightOneSpectrum (𝓞 K)) : Fintype (Fib (M := M) v) :=
  Fintype.ofEquiv _ (fibEquiv v).symm

lemma card_fib (v : HeightOneSpectrum (𝓞 K)) :
    Fintype.card (Fib (M := M) v) = (v.asIdeal.primesOver (𝓞 M)).ncard := by
  rw [← Nat.card_eq_fintype_card, Nat.card_congr (fibEquiv v), Nat.card_coe_set_eq]

/-- All primes over `v` have norm `Nv^f`, `f = inertiaDegIn`. -/
lemma absNorm_fib (v : HeightOneSpectrum (𝓞 K)) (w : Fib (M := M) v) :
    Ideal.absNorm w.1.asIdeal = Ideal.absNorm v.asIdeal ^ v.asIdeal.inertiaDegIn (𝓞 M) := by
  haveI : w.1.asIdeal.LiesOver v.asIdeal := ((fibEquiv v) w).2.2
  haveI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  haveI : w.1.asIdeal.IsMaximal := w.1.isPrime.isMaximal w.1.ne_bot
  rw [Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.1.asIdeal v.asIdeal v.isPrime v.ne_bot,
    Ideal.inertiaDeg'_eq_inertiaDeg,
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.1.asIdeal (M ≃ₐ[K] M)]

variable (ψ : (M ≃ₐ[K] M) →* ℂˣ)

/-- `g |I| f = |G|`. -/
lemma gIf (v : HeightOneSpectrum (𝓞 K)) :
    (v.asIdeal.primesOver (𝓞 M)).ncard * Nat.card (ArtinL.Abelian.inertiaGroup K M v) *
      v.asIdeal.inertiaDegIn (𝓞 M) = Nat.card (M ≃ₐ[K] M) := by
  rw [Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal (primeAbove K M v) (M ≃ₐ[K] M)]
  exact Ideal.ncard_primesOver_mul_card_inertia_mul_finrank v.asIdeal (primeAbove K M v)

lemma card_stab (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card (MulAction.stabilizer (M ≃ₐ[K] M) (primeAbove K M v)) =
      Nat.card (ArtinL.Abelian.inertiaGroup K M v) * v.asIdeal.inertiaDegIn (𝓞 M) := by
  rw [Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal (primeAbove K M v) (M ≃ₐ[K] M)]
  exact Ideal.card_stabilizer_eq_card_inertia_mul_finrank v.asIdeal (primeAbove K M v)

lemma two_le_absNorm (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

/-- If the Frobenius is trivial then `f = 1`. -/
lemma inertiaDegIn_eq_one_of_frob (v : HeightOneSpectrum (𝓞 K)) (hf : artinFrob K M v = 1) :
    v.asIdeal.inertiaDegIn (𝓞 M) = 1 := by
  classical
  set Q := primeAbove K M v
  have hQv : Q.under (𝓞 K) = v.asIdeal := under_primeAbove K M v
  have hφ : IsArithFrobAt (𝓞 K) (artinFrob K M v) Q := isArithFrobAt_artinFrob K M v
  set q := Nat.card (𝓞 K ⧸ v.asIdeal)
  have hq : q = Ideal.absNorm v.asIdeal := by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hq2 : 1 < q := by rw [hq]; have := two_le_absNorm v; omega
  letI : Field (𝓞 M ⧸ Q) := Ideal.Quotient.field Q
  haveI : Finite (𝓞 M ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q (primeAbove_ne_bot K M v)
  letI : Fintype (𝓞 M ⧸ Q) := Fintype.ofFinite _
  have hall : ∀ x : 𝓞 M ⧸ Q, x ^ q = x := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have := hφ y
    rw [hQv, hf] at this
    rw [← map_pow, eq_comm, Ideal.Quotient.eq]
    simpa using this
  have hcard := card_le_of_forall_pow_eq hq2 hall
  have hN : Ideal.absNorm Q = Fintype.card (𝓞 M ⧸ Q) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hfib := absNorm_fib (M := M) v ⟨⟨Q, (primeAbove_isMaximal K M v).isPrime,
    primeAbove_ne_bot K M v⟩, by ext1; exact hQv⟩
  change Ideal.absNorm Q = _ at hfib
  rw [hN, ← hq] at hfib
  rw [hfib] at hcard
  have hf0 : v.asIdeal.inertiaDegIn (𝓞 M) ≠ 0 :=
    Ideal.inertiaDegIn_ne_zero (G := M ≃ₐ[K] M)
  by_contra hne
  have h2 : 2 ≤ v.asIdeal.inertiaDegIn (𝓞 M) := by omega
  have : q ^ 2 ≤ q ^ v.asIdeal.inertiaDegIn (𝓞 M) := Nat.pow_le_pow_right (by omega) h2
  nlinarith

section Quad

variable {ψ}

variable (hinj : Function.Injective ψ) (hsq : ∀ σ, ψ σ ^ 2 = 1) (hne : ψ ≠ 1)

include hsq in
lemma val_eq_neg_one (τ : M ≃ₐ[K] M) (h : ψ τ ≠ 1) : ((ψ τ : ℂˣ) : ℂ) = -1 := by
  have h2 : ((ψ τ : ℂˣ) : ℂ) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, hsq, Units.val_one]
  have h3 : ((ψ τ : ℂˣ) : ℂ) * ((ψ τ : ℂˣ) : ℂ) = 1 := by rw [← sq]; exact h2
  rcases mul_self_eq_one_iff.1 h3 with h1 | h1
  · exact absurd (Units.ext h1) h
  · exact h1

include hinj hsq hne in
lemma card_gal : Nat.card (M ≃ₐ[K] M) = 2 := by
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀, ψ σ₀ ≠ 1 := by
    by_contra h; push Not at h; exact hne (MonoidHom.ext h)
  have hσ₀1 : σ₀ ≠ 1 := by rintro rfl; exact hσ₀ (map_one ψ)
  rw [Nat.card_eq_two_iff' (1 : M ≃ₐ[K] M)]
  refine ⟨σ₀, hσ₀1, fun τ hτ => ?_⟩
  have hτ' : ψ τ ≠ 1 := fun h => hτ (hinj (h.trans (map_one ψ).symm))
  apply hinj
  apply Units.ext
  rw [val_eq_neg_one hsq τ hτ', val_eq_neg_one hsq σ₀ hσ₀]

include hinj hsq hne in
/-- **The local factor.** -/
theorem local_factor (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    ∏ w : Fib (M := M) v, (1 - ((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ =
      (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ *
        (1 - ArtinL.Abelian.localValue ψ v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ := by
  classical
  have hprod : ∏ w : Fib (M := M) v, (1 - ((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ =
      ((1 - (((Ideal.absNorm v.asIdeal ^ v.asIdeal.inertiaDegIn (𝓞 M) : ℕ) : ℂ)) ^ (-s))⁻¹) ^
        (v.asIdeal.primesOver (𝓞 M)).ncard := by
    rw [← card_fib, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_congr rfl fun w _ => by rw [absNorm_fib]
  rw [hprod]
  have H := gIf (M := M) v
  rw [card_gal hinj hsq hne] at H
  set g := (v.asIdeal.primesOver (𝓞 M)).ncard with hg
  set f := v.asIdeal.inertiaDegIn (𝓞 M) with hf
  set N := Ideal.absNorm v.asIdeal
  have hI1 : 1 ≤ Nat.card (ArtinL.Abelian.inertiaGroup K M v) := Nat.card_pos
  have hg1 : 1 ≤ g := by
    rcases Nat.eq_zero_or_pos g with h | h
    · rw [h] at H; simp at H
    · exact h
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · rw [h] at H; simp at H
    · exact h
  by_cases hun : ArtinL.Abelian.IsUnramifiedAt ψ v
  · have hIbot : ArtinL.Abelian.inertiaGroup K M v = ⊥ := by
      rw [eq_bot_iff]; intro σ hσ
      rw [Subgroup.mem_bot]; exact hinj ((hun σ hσ).trans (map_one ψ).symm)
    have hI : Nat.card (ArtinL.Abelian.inertiaGroup K M v) = 1 := by
      rw [hIbot]; exact Subgroup.card_bot
    rw [hI, mul_one] at H
    rw [ArtinL.Abelian.localValue, if_pos hun]
    by_cases hF : ψ (artinFrob K M v) = 1
    · have hF1 : artinFrob K M v = 1 := hinj (hF.trans (map_one ψ).symm)
      have hf' : f = 1 := inertiaDegIn_eq_one_of_frob v hF1
      rw [hf', mul_one] at H
      rw [hf', H, hF, Units.val_one, one_mul, pow_one, sq]
    · have hstab : 1 < Nat.card (MulAction.stabilizer (M ≃ₐ[K] M) (primeAbove K M v)) := by
        rw [Subgroup.one_lt_card_iff_ne_bot]
        intro hb
        have hmem := (isArithFrobAt_artinFrob K M v).mem_stabilizer
        rw [hb, Subgroup.mem_bot] at hmem
        exact hF (by rw [hmem, map_one])
      rw [card_stab, hI, one_mul] at hstab
      have hf2 : f = 2 := by nlinarith
      have hg' : g = 1 := by rw [hf2] at H; omega
      rw [hg', pow_one, hf2, val_eq_neg_one hsq _ hF]
      have hN : (((N ^ 2 : ℕ) : ℂ)) ^ (-s) = ((N : ℂ) ^ (-s)) * ((N : ℂ) ^ (-s)) := by
        rw [sq, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
      rw [hN, ← mul_inv]
      congr 1; ring
  · have hIne : ArtinL.Abelian.inertiaGroup K M v ≠ ⊥ := by
      intro hb; apply hun; intro σ hσ
      rw [hb, Subgroup.mem_bot] at hσ; rw [hσ, map_one]
    have hI2 : 1 < Nat.card (ArtinL.Abelian.inertiaGroup K M v) :=
      (Subgroup.one_lt_card_iff_ne_bot _).2 hIne
    have hA : g * 2 * 1 ≤ g * Nat.card (ArtinL.Abelian.inertiaGroup K M v) * f :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hI2) hf1
    have hB : 1 * 2 * f ≤ g * Nat.card (ArtinL.Abelian.inertiaGroup K M v) * f :=
      Nat.mul_le_mul (Nat.mul_le_mul hg1 hI2) le_rfl
    have hg' : g = 1 := by omega
    have hf' : f = 1 := by omega
    rw [hg', hf', pow_one, pow_one, ArtinL.Abelian.localValue, if_neg hun, zero_mul, sub_zero,
      inv_one, mul_one]

variable (hK : ∀ w : InfinitePlace K, w.IsComplex)

include hK in
/-- The Euler product of `L(ψ)` over all primes. -/
theorem hasProd_LSeries {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) =>
      (1 - ArtinL.Abelian.localValue ψ v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
      (ArtinL.Abelian.LSeries ψ s) := by
  classical
  have hχ := T12A.norm_heckeChar_le (ArtinL.Abelian.conductor_ne_bot ψ) (L3K.psiH ψ hK)
  have e1 := (C3A.euler1 (L3K.psiH ψ hK) s hχ hs).1
  rw [L3K.LSeries_eq_psiH ψ hK]
  have e2 := ((L3K.epEquiv ψ).symm.hasProd_iff).2 e1
  set Fv : HeightOneSpectrum (𝓞 K) → ℂ := fun v =>
    (1 - ArtinL.Abelian.localValue ψ v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹
  have hsupp : Function.mulSupport Fv ⊆ {v | v ∉ L3K.condPrimes ψ} := by
    intro v hv
    simp only [Set.mem_ofPred_eq]
    intro hc
    apply hv
    have hram := (ArtinL.Abelian.dvd_conductor_iff_not_isUnramifiedAt K M ψ v).1
      ((L3K.mem_condPrimes ψ v).1 hc)
    simp only [Fv, ArtinL.Abelian.localValue, if_neg hram, zero_mul, sub_zero, inv_one]
  have e3 : HasProd (fun v' : {v : HeightOneSpectrum (𝓞 K) // v ∉ L3K.condPrimes ψ} => Fv v'.1)
      ((L3K.psiH ψ hK).LSeries s) := by
    convert e2 using 1
    funext v'
    simp only [Function.comp_apply, Fv]
    rw [← L3K.psiH_prime ψ hK v'.1]
    rfl
  exact (hasProd_subtype_iff_of_mulSupport_subset hsupp).1 e3

include hinj hsq hne hK in
/-- **`ζ_M = ζ_K · L(ψ)`** on `Re s > 1`. -/
theorem dedekindZeta_eq_mul {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta M s = dedekindZeta K s * ArtinL.Abelian.LSeries ψ s := by
  classical
  set f : HeightOneSpectrum (𝓞 M) → ℂ := fun w =>
    (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹
  have h1 : HasProd f (dedekindZeta M s) :=
    NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta M s hs
  set e := Equiv.sigmaFiberEquiv (fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K))
  have h2 : HasProd (f ∘ e) (dedekindZeta M s) := (e.hasProd_iff).2 h1
  have h3 : HasProd (fun v : HeightOneSpectrum (𝓞 K) => ∏ w : Fib (M := M) v, f w.1)
      (dedekindZeta M s) :=
    h2.sigma fun v => hasProd_fintype _
  have h4 : HasProd (fun v : HeightOneSpectrum (𝓞 K) =>
      (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ *
        (1 - ArtinL.Abelian.localValue ψ v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
      (dedekindZeta M s) := by
    convert h3 using 1
    funext v
    exact (local_factor hinj hsq hne v s).symm
  have h5 := NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta K s hs
  have h6 := hasProd_LSeries (ψ := ψ) hK hs
  exact h4.unique (h5.mul h6)

end Quad

end L3F

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3F_Root: the root number of a quadratic character is `1`

For `M/K` totally complex with `ψ` injective of order `2`: by 3508ac81, `Λ(1 − s) = W Λ(s)`
(`ψ⁻¹ = ψ`), so `W² = 1`. With the completed Dedekind zeta functions (7f1aa5b8) and
`ζ_M = ζ_K L(ψ)` (`L3F_Zeta`): `|d_K|^{s/2} D^{s/2} Λ_M(s) = |d_M|^{s/2} Λ_K(s) Λ(s)` on `Re s > 1`,
hence on `ℂ ∖ {0, 1}` (identity theorem). Comparing `s = 2` and `s = −1` gives `W > 0`, so `W = 1`. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open NumberField NumberField.InfinitePlace IsDedekindDomain Complex

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3F

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M] {ψ : (M ≃ₐ[K] M) →* ℂˣ}
  (hinj : Function.Injective ψ) (hsq : ∀ σ, ψ σ ^ 2 = 1) (hne : ψ ≠ 1)
  (hK : ∀ w : InfinitePlace K, w.IsComplex)

include hsq in
lemma inv_eq_self : ψ⁻¹ = ψ := by
  ext σ
  rw [MonoidHom.inv_apply]
  congr 1
  exact inv_eq_of_mul_eq_one_right (by rw [← sq, hsq])

include hK in
lemma isComplex_M (w : InfinitePlace M) : w.IsComplex :=
  IsComplex.of_comap (algebraMap K M) (hK _)

include hinj hsq hne hK in
lemma nrComplexPlaces_M : nrComplexPlaces M = 2 * nrComplexPlaces K := by
  have h1 := card_add_two_mul_card_eq_rank K
  have h2 := card_add_two_mul_card_eq_rank M
  rw [L3K.nrRealPlaces_eq_zero hK, zero_add] at h1
  have hRM : nrRealPlaces M = 0 := by
    haveI : IsTotallyComplex M := ⟨isComplex_M hK⟩
    exact IsTotallyComplex.nrRealPlaces_eq_zero M
  rw [hRM, zero_add] at h2
  have h3 := Module.finrank_mul_finrank ℚ K M
  have h4 : Module.finrank K M = 2 := by
    rw [← IsGalois.card_aut_eq_finrank]; exact card_gal hinj hsq hne
  rw [h4, ← h2, ← h1] at h3
  omega

lemma ofReal_cpow_pos {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ((x : ℂ)) ^ (y : ℂ) = ((x ^ y : ℝ) : ℂ) :=
  (Complex.ofReal_cpow hx.le y).symm

include hinj hsq hne hK in
/-- **Root number one.** -/
theorem fe_root_one :
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      (∀ s : ℂ, 1 < s.re → Λ s = ArtinL.Abelian.completedLSeries ψ s) ∧
      ∀ s : ℂ, Λ (1 - s) = Λ s := by
  obtain ⟨W, Λ, Λ', -, hΛ, hΛ', hre, hfe⟩ :=
    ArtinL.Abelian.exists_completedLSeries_functionalEquation_u0 K M ψ
  have hre' : ∀ s : ℂ, 1 < s.re → Λ s = ArtinL.Abelian.completedLSeries ψ s ∧
      Λ' s = ArtinL.Abelian.completedLSeries ψ⁻¹ s := fun s hs => by
    have := hre s hs; rwa [if_neg hne, one_mul, one_mul] at this
  have hΛ'eq : Λ' = Λ := by
    refine L3K.entire_ext hΛ' hΛ fun s hs => ?_
    rw [(hre' s hs).2, (hre' s hs).1, inv_eq_self hsq]
  rw [hΛ'eq] at hfe
  have gc2 : Gammaℂ 2 ≠ 0 := by
    rw [Gammaℂ_def]
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero_of_re_pos (by norm_num))
    rw [Ne, Complex.cpow_eq_zero_iff]; push Not; intro h
    exact absurd h (by simp [Real.pi_ne_zero])
  -- `Λ(2) ≠ 0`
  have h2 : Λ 2 ≠ 0 := by
    rw [(hre' 2 (by norm_num)).1, L3K.completedLSeries_eq ψ hK]
    refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ ?_)) (L3K.LSeries_two_ne_zero ψ hK)
    · rw [Ne, Complex.cpow_eq_zero_iff]; push Not; intro h
      exact absurd (Complex.ofReal_eq_zero.1 h) (by linarith [L3K.one_le_Dψ ψ])
    · exact gc2
  -- `W² = 1`
  have hW2 : W * W = 1 := by
    have e1 := hfe (-1)
    have e2 := hfe 2
    norm_num at e1 e2
    have : Λ 2 = W * W * Λ 2 := by
      calc Λ 2 = W * Λ (-1) := e1
        _ = W * (W * Λ 2) := by rw [e2]
        _ = W * W * Λ 2 := by ring
    have := mul_right_cancel₀ h2 (this.symm.trans (one_mul (Λ 2)).symm)
    exact this
  -- the zeta packages
  obtain ⟨ΛM, hΛMd, hΛMfe, hΛMre, -⟩ := NumberField.exists_completedDedekindZeta_package M
  obtain ⟨ΛK, hΛKd, hΛKfe, hΛKre, -⟩ := NumberField.exists_completedDedekindZeta_package K
  have hrM := nrComplexPlaces_M hinj hsq hne hK
  have hRK := L3K.nrRealPlaces_eq_zero hK
  have hRM : nrRealPlaces M = 0 := by
    haveI : IsTotallyComplex M := ⟨isComplex_M hK⟩
    exact IsTotallyComplex.nrRealPlaces_eq_zero M
  set A : ℝ := ((|discr K| : ℤ) : ℝ)
  set B : ℝ := L3K.Dψ ψ
  set C : ℝ := ((|discr M| : ℤ) : ℝ)
  have hA : 0 < A := by
    have : (1 : ℤ) ≤ |discr K| := Int.one_le_abs (discr_ne_zero K)
    simp only [A]; exact_mod_cast (by omega : (0 : ℤ) < |discr K|)
  have hB : 0 < B := lt_of_lt_of_le one_pos (L3K.one_le_Dψ ψ)
  have hC : 0 < C := by
    have : (1 : ℤ) ≤ |discr M| := Int.one_le_abs (discr_ne_zero M)
    simp only [C]; exact_mod_cast (by omega : (0 : ℤ) < |discr M|)
  have hAc : (((|discr K| : ℤ) : ℂ)) = ((A : ℝ) : ℂ) := by
    simp only [A, Complex.ofReal_intCast]
  have hCc : (((|discr M| : ℤ) : ℂ)) = ((C : ℝ) : ℂ) := by
    simp only [C, Complex.ofReal_intCast]
  set G : ℂ → ℂ := fun s => ((A : ℂ)) ^ (s / 2) * ((B : ℂ)) ^ (s / 2) * ΛM s -
    ((C : ℂ)) ^ (s / 2) * ΛK s * Λ s
  have hG : ∀ s : ℂ, 1 < s.re → G s = 0 := by
    intro s hs
    simp only [G]
    rw [hΛMre s hs, hΛKre s hs, (hre' s hs).1, L3K.completedLSeries_eq ψ hK,
      dedekindZeta_eq_mul hinj hsq hne hK hs, hrM, hRK, hRM, hAc, hCc]
    simp only [pow_zero, mul_one, pow_mul]
    ring
  -- identity theorem
  set U : Set ℂ := ({0, 1} : Set ℂ)ᶜ
  have hUo : IsOpen U := (Set.toFinite _).isClosed.isOpen_compl
  have hUc : IsPreconnected U :=
    ((Set.toFinite ({0, 1} : Set ℂ)).countable.isConnected_compl_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; exact Nat.one_lt_ofNat)).isPreconnected
  have hcp : ∀ x : ℝ, 0 < x → Differentiable ℂ (fun s : ℂ => ((x : ℂ)) ^ (s / 2)) := by
    intro x hx s
    exact (differentiableAt_id.div_const 2).const_cpow (Or.inl (by exact_mod_cast hx.ne'))
  have hGd : DifferentiableOn ℂ G U := by
    have h1 : DifferentiableOn ℂ ΛM U := hΛMd
    have h2' : DifferentiableOn ℂ ΛK U := hΛKd
    exact ((((hcp A hA).differentiableOn).mul (hcp B hB).differentiableOn).mul h1).sub
      ((((hcp C hC).differentiableOn).mul h2').mul hΛ.differentiableOn)
  have h2U : (2 : ℂ) ∈ U := by norm_num [U]
  have hev : G =ᶠ[nhds (2 : ℂ)] 0 := by
    have ho : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with s hs using hG s hs
  have hzero := (hGd.analyticOnNhd hUo).eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc h2U hev
  have hm1U : (-1 : ℂ) ∈ U := by norm_num [U]
  have hGm1 : G (-1) = 0 := hzero hm1U
  have hG2 : G 2 = 0 := hG 2 (by norm_num)
  simp only [G] at hGm1 hG2
  -- evaluate
  have e1 : (-1 : ℂ) = 1 - 2 := by norm_num
  rw [e1, hΛMfe 2 two_ne_zero (by norm_num), hΛKfe 2 two_ne_zero (by norm_num), hfe 2] at hGm1
  have hhalf : ((1 : ℂ) - 2) / 2 = ((-1 / 2 : ℝ) : ℂ) := by push_cast; ring
  have hone : (2 : ℂ) / 2 = 1 := by norm_num
  rw [hhalf, ofReal_cpow_pos hA, ofReal_cpow_pos hB, ofReal_cpow_pos hC] at hGm1
  rw [hone, cpow_one, cpow_one, cpow_one] at hG2
  have hk : ΛK 2 ≠ 0 := by
    rw [hΛKre 2 (by norm_num)]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ ?_)) (pow_ne_zero _ ?_))
      (NumberField.dedekindZeta_ne_zero_of_one_lt_re K (by norm_num))
    · rw [hAc, Ne, Complex.cpow_eq_zero_iff]; push Not; intro h
      exact absurd (Complex.ofReal_eq_zero.1 h) hA.ne'
    · exact Gammaℝ_ne_zero_of_re_pos (by norm_num)
    · exact gc2
  -- `W` is a positive real
  set a := A ^ (-1 / 2 : ℝ)
  set b := B ^ (-1 / 2 : ℝ)
  set c := C ^ (-1 / 2 : ℝ)
  have ha : 0 < a := Real.rpow_pos_of_pos hA _
  have hb : 0 < b := Real.rpow_pos_of_pos hB _
  have hc : 0 < c := Real.rpow_pos_of_pos hC _
  have hm : ΛM 2 = (C : ℂ) * ΛK 2 * Λ 2 / ((A : ℂ) * (B : ℂ)) := by
    rw [eq_div_iff (by exact_mod_cast (mul_pos hA hB).ne')]
    linear_combination hG2
  have hWr : W = ((a * b * C / (c * A * B) : ℝ) : ℂ) := by
    rw [hm] at hGm1
    have hcl : (c : ℂ) * ΛK 2 * Λ 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by exact_mod_cast hc.ne') hk) h2
    have hAB : ((A : ℂ)) * (B : ℂ) ≠ 0 := by exact_mod_cast (mul_pos hA hB).ne'
    have hAc0 : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
    have hBc0 : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
    have hcc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    push_cast
    field_simp
    have h' : (a : ℂ) * b * ((C : ℂ) * ΛK 2 * Λ 2) = (c : ℂ) * ΛK 2 * (W * Λ 2) * (A * B) := by
      field_simp at hGm1
      linear_combination hGm1
    have hkl : ΛK 2 * Λ 2 ≠ 0 := mul_ne_zero hk h2
    apply mul_right_cancel₀ hkl
    linear_combination -h'
  set r : ℝ := a * b * C / (c * A * B)
  have hr : 0 < r := by positivity
  have hr1 : r = 1 := by
    rw [hWr] at hW2
    have : r * r = 1 := by exact_mod_cast hW2
    nlinarith
  have hW1 : W = 1 := by rw [hWr]; simp [r] at hr1 ⊢; exact_mod_cast hr1
  refine ⟨Λ, hΛ, fun s hs => (hre' s hs).1, fun s => ?_⟩
  rw [hfe, hW1, one_mul]

end L3F

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3K_KB: the Kummer-field basics of C0Z (C0ZK, C0ZF, parts of C0ZS/ZN/ZU/ZV), copied without
the idelic Artin map, so that the KummerConvexity solution does not pull in the C0-H development. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin Polynomial

noncomputable section

namespace ArtinPrimitiveRoots.L3K.KB

section Kch


variable {F : Type} [Field F] {ℓ : ℕ} [NeZero ℓ]

/-- Every `ℓ`-th root of unity of an `F`-field comes from `F`. -/
theorem exists_of_pow_eq_one {ζ : F} (hζ : IsPrimitiveRoot ζ ℓ) (M : Type*) [Field M] [Algebra F M]
    (x : M) (hx : x ^ ℓ = 1) : ∃ y : F, y ^ ℓ = 1 ∧ algebraMap F M y = x := by
  have hζM := hζ.map_of_injective (FaithfulSMul.algebraMap_injective F M)
  obtain ⟨i, -, hi⟩ := hζM.eq_pow_of_pow_eq_one hx
  exact ⟨ζ ^ i, by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow], by rw [map_pow, hi]⟩

variable {ζ : F} (hζ : IsPrimitiveRoot ζ ℓ) (M : Type*) [Field M] [Algebra F M]
include hζ

/-- A Kummer generator: a nonzero `β` with `β^ℓ ∈ F`. -/
structure KGen (M : Type*) [Field M] [Algebra F M] (ℓ : ℕ) where
  β : M
  ne_zero : β ≠ 0
  pow_mem : ∃ a : F, β ^ ℓ = algebraMap F M a

variable {M}

theorem ratio_pow (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) : (σ g.β / g.β) ^ ℓ = 1 := by
  obtain ⟨a, ha⟩ := g.pow_mem
  rw [div_pow, ← map_pow, ha, AlgEquiv.commutes, ← ha, div_self (pow_ne_zero _ g.ne_zero)]

theorem ratio_mem (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) :
    ∃ y : F, y ^ ℓ = 1 ∧ algebraMap F M y = σ g.β / g.β :=
  exists_of_pow_eq_one hζ M _ (ratio_pow hζ g σ)

/-- The value of the Kummer character in `F`. -/
def kval (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) : F := (ratio_mem hζ g σ).choose

theorem kval_pow (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) : kval hζ g σ ^ ℓ = 1 :=
  (ratio_mem hζ g σ).choose_spec.1

theorem algebraMap_kval (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) :
    algebraMap F M (kval hζ g σ) = σ g.β / g.β :=
  (ratio_mem hζ g σ).choose_spec.2

theorem fix_ratio (g : KGen (F := F) M ℓ) (σ τ : M ≃ₐ[F] M) :
    σ (τ g.β / g.β) = τ g.β / g.β := by
  rw [← algebraMap_kval hζ g τ, AlgEquiv.commutes]

/-- The Kummer character `σ ↦ σβ/β`, valued in `μ_ℓ(F)`. -/
def kch (g : KGen (F := F) M ℓ) : (M ≃ₐ[F] M) →* rootsOfUnity ℓ F where
  toFun σ := rootsOfUnity.mkOfPowEq (kval hζ g σ) (kval_pow hζ g σ)
  map_one' := by
    apply Subtype.ext; apply Units.ext
    simp only [rootsOfUnity.coe_mkOfPowEq, OneMemClass.coe_one, Units.val_one]
    apply FaithfulSMul.algebraMap_injective F M
    rw [algebraMap_kval hζ, map_one, AlgEquiv.one_apply, div_self g.ne_zero]
  map_mul' σ τ := by
    apply Subtype.ext; apply Units.ext
    simp only [rootsOfUnity.coe_mkOfPowEq, Subgroup.coe_mul, Units.val_mul]
    apply FaithfulSMul.algebraMap_injective F M
    rw [map_mul, algebraMap_kval hζ, algebraMap_kval hζ, algebraMap_kval hζ, AlgEquiv.mul_apply]
    have h1 : τ g.β = (τ g.β / g.β) * g.β := by field_simp [g.ne_zero]
    conv_lhs => rw [h1, map_mul, fix_ratio hζ g σ τ]
    field_simp [g.ne_zero]

theorem algebraMap_kch (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) :
    algebraMap F M ((kch hζ g σ : Fˣ) : F) = σ g.β / g.β := by
  simp only [kch, MonoidHom.coe_mk, OneHom.coe_mk, rootsOfUnity.coe_mkOfPowEq]
  exact algebraMap_kval hζ g σ


end Kch

section KFsec


variable (F : Type) [Field F] (ℓ : ℕ)

/-- `F(a^{1/ℓ})`. -/
def KF (a : Fˣ) : Type := (X ^ ℓ - C (a : F)).SplittingField

/-- `F(a^{1/ℓ}, a'^{1/ℓ})`. -/
def KF2 (a a' : Fˣ) : Type := ((X ^ ℓ - C (a : F)) * (X ^ ℓ - C (a' : F))).SplittingField

variable (a a' : Fˣ)

instance : Field (KF F ℓ a) := inferInstanceAs (Field (SplittingField _))
instance : Algebra F (KF F ℓ a) := inferInstanceAs (Algebra F (SplittingField _))
instance : Field (KF2 F ℓ a a') := inferInstanceAs (Field (SplittingField _))
instance : Algebra F (KF2 F ℓ a a') := inferInstanceAs (Algebra F (SplittingField _))
instance : IsSplittingField F (KF F ℓ a) (X ^ ℓ - C (a : F)) :=
  inferInstanceAs (IsSplittingField F (SplittingField _) _)
instance : IsSplittingField F (KF2 F ℓ a a') ((X ^ ℓ - C (a : F)) * (X ^ ℓ - C (a' : F))) :=
  inferInstanceAs (IsSplittingField F (SplittingField _) _)
instance : FiniteDimensional F (KF F ℓ a) := IsSplittingField.finiteDimensional _ (X ^ ℓ - C (a : F))
instance : FiniteDimensional F (KF2 F ℓ a a') :=
  IsSplittingField.finiteDimensional _ ((X ^ ℓ - C (a : F)) * (X ^ ℓ - C (a' : F)))
instance : Normal F (KF F ℓ a) := Normal.of_isSplittingField (X ^ ℓ - C (a : F))
instance : Normal F (KF2 F ℓ a a') :=
  Normal.of_isSplittingField ((X ^ ℓ - C (a : F)) * (X ^ ℓ - C (a' : F)))

section CharZero

variable [CharZero F]

instance : IsGalois F (KF F ℓ a) := { }
instance : IsGalois F (KF2 F ℓ a a') := { }

end CharZero

instance [NumberField F] : NumberField (KF F ℓ a) := NumberField.of_module_finite F _
instance [NumberField F] : NumberField (KF2 F ℓ a a') := NumberField.of_module_finite F _

variable {F ℓ}

theorem exists_root_of_splits {M : Type*} [Field M] [Algebra F M] (hℓ : ℓ ≠ 0)
    (hs : Splits ((X ^ ℓ - C (a : F)).map (algebraMap F M))) : ∃ β : M, β ^ ℓ = algebraMap F M a := by
  have hdeg : ((X ^ ℓ - C (a : F)).map (algebraMap F M)).degree ≠ 0 := by
    rw [degree_map]
    exact degree_ne_of_natDegree_ne (by rw [natDegree_X_pow_sub_C]; exact hℓ)
  obtain ⟨β, hβ⟩ := hs.exists_eval_eq_zero hdeg
  refine ⟨β, ?_⟩
  simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, eval_sub, eval_pow, eval_X,
    eval_C] at hβ
  exact sub_eq_zero.mp hβ

/-- A Kummer generator from a root of `X^ℓ - a`. -/
def kgenOf {M : Type*} [Field M] [Algebra F M] {β : M} (hβ : β ^ ℓ = algebraMap F M a)
    (hℓ : ℓ ≠ 0) : KGen (F := F) M ℓ where
  β := β
  ne_zero := by
    rintro rfl
    rw [zero_pow hℓ, eq_comm, map_eq_zero] at hβ
    exact a.ne_zero hβ
  pow_mem := ⟨a, hβ⟩

theorem splits_KF (hℓ : ℓ ≠ 0) :
    Splits ((X ^ ℓ - C (a : F)).map (algebraMap F (KF F ℓ a))) :=
  IsSplittingField.splits (KF F ℓ a) (X ^ ℓ - C (a : F))

theorem root_pow_of_mem_rootSet {M : Type*} [Field M] [Algebra F M] {b : F} {r : M}
    (hr : aeval r (X ^ ℓ - C b) = 0) : r ^ ℓ = algebraMap F M b := by
  simpa [sub_eq_zero] using hr

section Comm

variable [NeZero ℓ] {ζ : F} (hζ : IsPrimitiveRoot ζ ℓ)
include hζ

/-- A root of `X^ℓ - a` is a multiple of a fixed generator by an element of `F`. -/
theorem eq_smul_of_pow_eq {M : Type*} [Field M] [Algebra F M] (g : KGen (F := F) M ℓ) {r : M}
    (hr : r ^ ℓ = g.β ^ ℓ) : ∃ c : F, r = algebraMap F M c * g.β := by
  have h1 : (r / g.β) ^ ℓ = 1 := by rw [div_pow, hr, div_self (pow_ne_zero _ g.ne_zero)]
  obtain ⟨c, -, hc⟩ := exists_of_pow_eq_one hζ M _ h1
  exact ⟨c, by rw [hc]; field_simp [g.ne_zero]⟩

theorem fixes_of_kch_eq_one {M : Type*} [Field M] [Algebra F M] (g : KGen (F := F) M ℓ)
    (σ : M ≃ₐ[F] M) (h : kch hζ g σ = 1) : σ g.β = g.β := by
  have := algebraMap_kch hζ g σ
  rw [h, OneMemClass.coe_one, Units.val_one, map_one, eq_comm, div_eq_one_iff_eq g.ne_zero] at this
  exact this

theorem fixes_root {M : Type*} [Field M] [Algebra F M] (g : KGen (F := F) M ℓ)
    (σ : M ≃ₐ[F] M) (h : σ g.β = g.β) {r : M} (hr : r ^ ℓ = g.β ^ ℓ) : σ r = r := by
  obtain ⟨c, rfl⟩ := eq_smul_of_pow_eq hζ g hr
  rw [map_mul, AlgEquiv.commutes, h]

theorem eq_one_of_kch_KF (g : KGen (F := F) (KF F ℓ a) ℓ)
    (hg : g.β ^ ℓ = algebraMap F (KF F ℓ a) a) (σ : KF F ℓ a ≃ₐ[F] KF F ℓ a)
    (h : kch hζ g σ = 1) : σ = 1 := by
  have f1 := fixes_of_kch_eq_one hζ g σ h
  apply AlgEquiv.coe_toAlgHom_injective
  refine AlgHom.ext_of_adjoin_eq_top
    (IsSplittingField.adjoin_rootSet (KF F ℓ a) (X ^ ℓ - C (a : F))) fun r hr => ?_
  rw [mem_rootSet] at hr
  show σ r = r
  exact fixes_root hζ g σ f1 (by rw [root_pow_of_mem_rootSet hr.2]; exact hg.symm)

theorem kch_KF_injective (g : KGen (F := F) (KF F ℓ a) ℓ)
    (hg : g.β ^ ℓ = algebraMap F (KF F ℓ a) a) : Function.Injective (kch hζ g) :=
  (injective_iff_map_eq_one _).mpr fun σ h => eq_one_of_kch_KF a hζ g hg σ h

end Comm


end KFsec

section RootKF
variable (F : Type) [Field F] [NumberField F] {ℓ : ℕ} [NeZero ℓ]

/-- The chosen root of `X^ℓ - a` in `F(a^{1/ℓ})`. -/
def rootKF (a : Fˣ) : KGen (F := F) (KF F ℓ a) ℓ :=
  kgenOf a (exists_root_of_splits a (NeZero.ne ℓ) (splits_KF a (NeZero.ne ℓ))).choose_spec
    (NeZero.ne ℓ)

theorem rootKF_pow (a : Fˣ) : (rootKF F a).β ^ ℓ = algebraMap F (KF F ℓ a) a :=
  (exists_root_of_splits a (NeZero.ne ℓ) (splits_KF a (NeZero.ne ℓ))).choose_spec
end RootKF

section UV
/-- `n`-th roots of unity congruent modulo `Q` with `n ∉ Q` are equal. -/
theorem eq_of_pow_eq_one_of_sub_mem {R : Type*} [CommRing R] [IsDomain R] (Q : Ideal R) {n : ℕ}
    (hn : (n : R) ∉ Q) {a b : R} (ha : a ^ n = 1) (hb : b ^ n = 1) (hab : a - b ∈ Q) : a = b := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  set η := b * a ^ (n - 1) with hη
  have han : a ^ (n - 1) * a = 1 := by rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0), ha]
  have h1 : 1 - η ∈ Q := by
    have : 1 - η = a ^ (n - 1) * (a - b) := by
      rw [hη, mul_sub, han]; ring
    rw [this]; exact Q.mul_mem_left _ hab
  by_cases hη1 : η = 1
  · calc a = a * 1 := (mul_one a).symm
      _ = a * η := by rw [hη1]
      _ = b * (a ^ (n - 1) * a) := by rw [hη]; ring
      _ = b := by rw [han, mul_one]
  · exfalso
    have hηn : η ^ n = 1 := by
      rw [hη, mul_pow, ← pow_mul, hb, one_mul, mul_comm, pow_mul, ha, one_pow]
    have hsum : ∑ i ∈ Finset.range n, η ^ i = 0 := by
      have h := geom_sum_mul η n
      rw [hηn, sub_self] at h
      exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hη1)
    apply hn
    have : (n : R) = ∑ i ∈ Finset.range n, (1 - η ^ i) := by
      rw [Finset.sum_sub_distrib, hsum, sub_zero, Finset.sum_const, Finset.card_range, nsmul_one]
    rw [this]
    refine Q.sum_mem fun i _ => ?_
    rw [← geom_sum_mul_neg]
    exact Q.mul_mem_left _ h1

variable (F : Type) [Field F] [NumberField F] {ℓ : ℕ} [NeZero ℓ] {ζ : F}
  (hζ : IsPrimitiveRoot ζ ℓ)

/-- An integral Kummer generator `β = d α` at a place where `a` is a unit. -/
theorem exists_intGen (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) (ha : v.valuation F (a : F) = 1) :
    ∃ (d n : 𝓞 F) (β : 𝓞 (KF F ℓ a)), d ∉ v.asIdeal ∧ n ∉ v.asIdeal ∧
      (a : F) * algebraMap (𝓞 F) F d = algebraMap (𝓞 F) F n ∧
      (β : KF F ℓ a) = algebraMap F (KF F ℓ a) (algebraMap (𝓞 F) F d) * (rootKF F a).β ∧
      β ^ ℓ = algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) (d ^ (ℓ - 1) * n) := by
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v (a : F) ha.le
  have hd : (d : 𝓞 F) ∉ v.asIdeal := d.2
  have hn : n ∉ v.asIdeal := by
    rw [← v.valuation_eq_one_iff_notMem (K := F), ← hnd, map_mul, ha,
      (v.valuation_eq_one_iff_notMem (K := F)).mpr hd, one_mul]
  set K := KF F ℓ a
  set β : K := algebraMap F K (algebraMap (𝓞 F) F d) * (rootKF F a).β
  have hβpow : β ^ ℓ = algebraMap F K (algebraMap (𝓞 F) F ((d : 𝓞 F) ^ (ℓ - 1) * n)) := by
    have hℓ1 : ℓ = (ℓ - 1) + 1 := (Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne ℓ))).symm
    rw [mul_pow, rootKF_pow, ← map_pow, ← map_mul]
    congr 1
    rw [map_mul, map_pow, ← hnd]
    conv_lhs => rw [hℓ1, pow_succ]
    ring
  have hint : IsIntegral ℤ β := by
    apply IsIntegral.of_pow (Nat.pos_of_ne_zero (NeZero.ne ℓ))
    rw [hβpow, ← IsScalarTower.algebraMap_apply]
    exact ((((d : 𝓞 F) ^ (ℓ - 1) * n).isIntegral_coe).map (IsScalarTower.toAlgHom ℤ F K))
  refine ⟨d, n, ⟨β, hint⟩, hd, hn, hnd, rfl, ?_⟩
  apply RingOfIntegers.ext
  simp only [map_pow]
  show β ^ ℓ = _
  rw [hβpow, ← IsScalarTower.algebraMap_apply]
  rfl

/-- A root of unity of `F` as an algebraic integer. -/
def rootO (μ : rootsOfUnity ℓ F) : 𝓞 F :=
  ⟨((μ : Fˣ) : F), IsIntegral.of_pow (Nat.pos_of_ne_zero (NeZero.ne ℓ)) (by
    have := μ.2; rw [mem_rootsOfUnity] at this
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]; exact isIntegral_one)⟩

omit [NumberField F] in
theorem rootO_pow (μ : rootsOfUnity ℓ F) : rootO F μ ^ ℓ = 1 := by
  apply RingOfIntegers.ext
  show ((μ : Fˣ) : F) ^ ℓ = 1
  have := μ.2; rw [mem_rootsOfUnity] at this
  rw [← Units.val_pow_eq_pow_val, this, Units.val_one]

include hζ in
/-- `σ β = μ_σ β` in `𝓞 K`. -/
theorem smul_intGen (a : Fˣ) (d : 𝓞 F) (β : 𝓞 (KF F ℓ a))
    (hβ : (β : KF F ℓ a) = algebraMap F (KF F ℓ a) (algebraMap (𝓞 F) F d) * (rootKF F a).β)
    (σ : KF F ℓ a ≃ₐ[F] KF F ℓ a) :
    σ • β = algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) (rootO F (kch hζ (rootKF F a) σ)) * β := by
  apply RingOfIntegers.ext
  have e : ∀ x : 𝓞 F, ((algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) x : 𝓞 (KF F ℓ a)) : KF F ℓ a) =
      algebraMap F (KF F ℓ a) (x : F) := fun x => rfl
  show σ (β : KF F ℓ a) = ((algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) _ : 𝓞 (KF F ℓ a)) : KF F ℓ a) *
    (β : KF F ℓ a)
  rw [e, hβ]
  show σ _ = algebraMap F (KF F ℓ a) ((kch hζ (rootKF F a) σ : Fˣ) : F) * _
  rw [algebraMap_kch, map_mul, AlgEquiv.commutes]
  field_simp [(rootKF (ℓ := ℓ) F a).ne_zero]

include hζ in
/-- **Kummer extensions are unramified** at `v ∤ ℓ` where `a` is a unit. -/
theorem inertia_eq_bot (v : HeightOneSpectrum (𝓞 F)) (hv : (ℓ : 𝓞 F) ∉ v.asIdeal) (a : Fˣ)
    (ha : v.valuation F (a : F) = 1) (w : HeightOneSpectrum (𝓞 (KF F ℓ a)))
    (hw : w.under (𝓞 F) = v) :
    w.asIdeal.inertia (KF F ℓ a ≃ₐ[F] KF F ℓ a) = ⊥ := by
  obtain ⟨d, n, β, hd, hn, -, hβ, hβpow⟩ := exists_intGen (ℓ := ℓ) F v a ha
  have hmem : ∀ x : 𝓞 F, algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) x ∈ w.asIdeal → x ∈ v.asIdeal := by
    intro x hx; rw [← hw]; exact hx
  have hβw : β ∉ w.asIdeal := by
    intro h
    have : β ^ ℓ ∈ w.asIdeal := w.asIdeal.pow_mem_of_mem h ℓ (Nat.pos_of_ne_zero (NeZero.ne ℓ))
    rw [hβpow] at this
    have h2 := hmem _ this
    rcases v.isPrime.mem_or_mem h2 with h3 | h3
    · exact hd (v.isPrime.mem_of_pow_mem _ h3)
    · exact hn h3
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  have h1 := hσ β
  rw [smul_intGen F hζ a d β hβ σ] at h1
  have h2 : (algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) (rootO F (kch hζ (rootKF F a) σ) - 1)) * β ∈
      w.asIdeal := by rw [map_sub, map_one, sub_mul, one_mul]; exact h1
  rcases w.isPrime.mem_or_mem h2 with h3 | h3
  · have h4 := hmem _ h3
    have h5 := eq_of_pow_eq_one_of_sub_mem v.asIdeal hv (rootO_pow F _) (one_pow ℓ) h4
    apply kch_KF_injective a hζ (rootKF F a) (rootKF_pow F a)
    rw [map_one]
    apply Subtype.ext; apply Units.ext
    have := congrArg (fun z : 𝓞 F => (z : F)) h5
    exact this
  · exact absurd h3 hβw

include hζ in

/-- An algebraic integer from an element of `F` that is a root of unity. -/
def toO (x : F) (hx : x ^ ℓ = 1) : 𝓞 F :=
  ⟨x, IsIntegral.of_pow (Nat.pos_of_ne_zero (NeZero.ne ℓ)) (by rw [hx]; exact isIntegral_one)⟩

omit [NumberField F] in
theorem toO_pow (x : F) (hx : x ^ ℓ = 1) : toO F x hx ^ ℓ = 1 := by
  apply RingOfIntegers.ext; show x ^ ℓ = 1; exact hx

include hζ in
/-- `ℓ ∣ N v - 1` when `v ∤ ℓ`. -/
theorem dvd_card_sub_one (v : HeightOneSpectrum (𝓞 F)) (hv : (ℓ : 𝓞 F) ∉ v.asIdeal) :
    ℓ ∣ Nat.card (𝓞 F ⧸ v.asIdeal) - 1 := by
  classical
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  set z := toO F ζ hζ.pow_eq_one
  have hz : z ^ ℓ = 1 := toO_pow F ζ _
  have hη : IsPrimitiveRoot (Ideal.Quotient.mk v.asIdeal z) ℓ := by
    refine ⟨by rw [← map_pow, hz, map_one], fun l hl => ?_⟩
    have h1 : z ^ l - 1 ∈ v.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hl, map_one, sub_self]
    have h2 := eq_of_pow_eq_one_of_sub_mem v.asIdeal hv
      (by rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]) (one_pow ℓ) h1
    apply hζ.dvd_of_pow_eq_one
    have := congrArg (fun x : 𝓞 F => (x : F)) h2
    simpa [z, toO] using this
  have := FiniteField.pow_card_sub_one_eq_one (Ideal.Quotient.mk v.asIdeal z)
    (hη.ne_zero (NeZero.ne ℓ))
  rw [Fintype.card_eq_nat_card] at this
  exact hη.dvd_of_pow_eq_one _ this


end UV

end ArtinPrimitiveRoots.L3K.KB

end
end
end

section
section
/-! # L3K_Kum: the sextic Kummer character `ψ_a` of `F(a^{1/6})/F`

For `a ∈ Fˣ`, `M = KF F 6 a` and `ψ_a = ι ∘ kch : Gal(M/F) →* ℂˣ` (C0Z):
* `psi_injective`; `psi_ne_one` when `a` is not a sixth power in `F`;
* `isUnramifiedAt_psi`: unramified at `v ∤ 6` with `v(a) = 0` (C0ZU);
* `psi_artinFrob`: there `ψ_a(Frob_v) = ι ω` for the sixth root of unity `ω ≡ a^{(Nv−1)/6}`;
* `not_isUnramifiedAt_psi`: ramified at `v` with `6 ∤ v(a)`. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin Polynomial ArtinPrimitiveRoots.L3K.KB

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

variable (F : Type) [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ 6) (ι : F →+* ℂ)
  (a : Fˣ)

/-- The Kummer field `F(a^{1/6})`. -/
abbrev KM := KF F 6 a

/-- `ψ_a(σ) = ι(σβ/β)`. -/
def psi : (KM F a ≃ₐ[F] KM F a) →* ℂˣ :=
  (Units.map ι.toMonoidHom).comp ((rootsOfUnity 6 F).subtype.comp (kch hζ (rootKF (ℓ := 6) F a)))

variable {F}

theorem psi_apply (σ : KM F a ≃ₐ[F] KM F a) :
    ((psi F hζ ι a σ : ℂˣ) : ℂ) = ι ((kch hζ (rootKF (ℓ := 6) F a) σ : Fˣ) : F) := rfl

theorem psi_injective : Function.Injective (psi F hζ ι a) := by
  intro σ τ h
  apply kch_KF_injective a hζ (rootKF F a) (rootKF_pow F a)
  apply Subtype.ext; apply Units.ext
  apply ι.injective
  have := congrArg (fun x : ℂˣ => (x : ℂ)) h
  simpa [psi_apply] using this

theorem psi_eq_one_iff_forall (σ : KM F a ≃ₐ[F] KM F a) : psi F hζ ι a σ = 1 ↔ σ = 1 :=
  ⟨fun h => psi_injective hζ ι a (h.trans (map_one _).symm), fun h => by rw [h, map_one]⟩

/-- If `a` is not a sixth power in `F` then `ψ_a ≠ 1`. -/
theorem psi_ne_one (ha : ∀ b : F, b ^ 6 ≠ (a : F)) : psi F hζ ι a ≠ 1 := by
  intro h
  have hall : ∀ σ : KM F a ≃ₐ[F] KM F a, σ = 1 := fun σ =>
    (psi_eq_one_iff_forall hζ ι a σ).1 (by rw [h, MonoidHom.one_apply])
  have hmem : (rootKF (ℓ := 6) F a).β ∈ (⊥ : IntermediateField F (KM F a)) := by
    rw [IsGalois.mem_bot_iff_fixed]
    intro σ; rw [hall σ]; rfl
  obtain ⟨b, hb⟩ := IntermediateField.mem_bot.1 hmem
  apply ha b
  apply (algebraMap F (KM F a)).injective
  rw [map_pow, hb, rootKF_pow]

/-- The prime of `𝓞 M` over `v`, as a height-one prime. -/
def wAbove (v : HeightOneSpectrum (𝓞 F)) : HeightOneSpectrum (𝓞 (KM F a)) :=
  ⟨primeAbove F (KM F a) v, (primeAbove_isMaximal F (KM F a) v).isPrime,
    primeAbove_ne_bot F (KM F a) v⟩

theorem wAbove_under (v : HeightOneSpectrum (𝓞 F)) : (wAbove a v).under (𝓞 F) = v := by
  ext1; exact under_primeAbove F (KM F a) v

include hζ in
theorem inertiaGroup_eq_bot (v : HeightOneSpectrum (𝓞 F)) (hv : ((6 : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (ha : v.valuation F (a : F) = 1) : ArtinL.Abelian.inertiaGroup F (KM F a) v = ⊥ :=
  inertia_eq_bot F hζ v hv a ha (wAbove a v) (wAbove_under a v)

theorem isUnramifiedAt_psi (v : HeightOneSpectrum (𝓞 F)) (hv : ((6 : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (ha : v.valuation F (a : F) = 1) : ArtinL.Abelian.IsUnramifiedAt (psi F hζ ι a) v := by
  intro σ hσ
  rw [inertiaGroup_eq_bot hζ a v hv ha, Subgroup.mem_bot] at hσ
  rw [hσ, map_one]

include hζ in
/-- **Frobenius.** `kch(Frob_v) = ω` with `ω ≡ a^{(Nv−1)/6} (mod v)` (the argument of C0ZV). -/
theorem kch_artinFrob (v : HeightOneSpectrum (𝓞 F)) (hv : ((6 : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (ha : v.valuation F (a : F) = 1) (ω : F) (hω : ω ^ 6 = 1)
    (hcong : v.valuation F ((a : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6) - ω) < 1) :
    ((kch hζ (rootKF (ℓ := 6) F a) (artinFrob F (KM F a) v) : Fˣ) : F) = ω := by
  classical
  set K := KM F a
  set Q := primeAbove F K v
  let w : HeightOneSpectrum (𝓞 K) := wAbove a v
  have hw : w.under (𝓞 F) = v := wAbove_under a v
  have hQv : Q.under (𝓞 F) = v.asIdeal := under_primeAbove F K v
  set φ := artinFrob F K v
  have hφ : IsArithFrobAt (𝓞 F) φ w.asIdeal := isArithFrobAt_artinFrob F K v
  have hv' : ((6 : ℕ) : 𝓞 F) ∉ v.asIdeal := hv
  -- the Kummer value of the Frobenius
  set μ := kch hζ (rootKF F a) φ
  obtain ⟨d, n, β, hd, hn, hnd, hβ, hβpow⟩ := exists_intGen (ℓ := 6) F v a ha
  have hmem : ∀ x : 𝓞 F, algebraMap (𝓞 F) (𝓞 K) x ∈ w.asIdeal → x ∈ v.asIdeal := by
    intro x hx; rw [← hw]; exact hx
  have hβw : β ∉ w.asIdeal := by
    intro h
    have : β ^ 6 ∈ w.asIdeal := w.asIdeal.pow_mem_of_mem h 6 (Nat.pos_of_ne_zero (NeZero.ne 6))
    rw [hβpow] at this
    rcases v.isPrime.mem_or_mem (hmem _ this) with h3 | h3
    · exact hd (v.isPrime.mem_of_pow_mem _ h3)
    · exact hn h3
  set q := Nat.card (𝓞 F ⧸ v.asIdeal)
  have hq : q = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hFrob : ∀ x : 𝓞 K, φ • x - x ^ q ∈ w.asIdeal := by
    intro x
    have := hφ x
    rw [show w.asIdeal.under (𝓞 F) = v.asIdeal from hQv] at this
    exact this
  -- `6 ∣ q - 1`
  have h6q : 6 ∣ q - 1 := dvd_card_sub_one F hζ v hv
  obtain ⟨K', hK'⟩ := h6q
  have hq1 : q = 6 * K' + 1 := by
    have : 0 < q := by
      rw [hq]; exact Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
    omega
  have hK'eq : (Ideal.absNorm v.asIdeal - 1) / 6 = K' := by
    rw [← hq, hK', Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne 6))]
  rw [hK'eq] at hcong
  set μO := rootO F μ
  have hsm := smul_intGen F hζ a d β hβ φ
  have hfb := hFrob β
  rw [hsm, hq1, pow_succ, pow_mul, hβpow] at hfb
  have hfb' : algebraMap (𝓞 F) (𝓞 K) (μO - ((d ^ (6 - 1) * n) ^ K')) * β ∈ w.asIdeal := by
    rw [map_sub, map_pow, sub_mul]; convert hfb using 1
  have hμA : μO - (d ^ (6 - 1) * n) ^ K' ∈ v.asIdeal := by
    rcases w.isPrime.mem_or_mem hfb' with h | h
    · exact hmem _ h
    · exact absurd h hβw
  -- valuations in `F`
  set D : F := algebraMap (𝓞 F) F d
  set A : F := algebraMap (𝓞 F) F ((d ^ (6 - 1) * n) ^ K')
  have hDv : v.valuation F D = 1 := (v.valuation_eq_one_iff_notMem (K := F)).mpr hd
  have hA : A = D ^ (q - 1) * (a : F) ^ K' := by
    have h61 : 6 = (6 - 1) + 1 := (Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne 6))).symm
    simp only [A, map_pow, map_mul]
    rw [← hnd, hK']
    have e : D ^ (6 - 1) * ((a : F) * D) = (a : F) * D ^ 6 := by
      conv_rhs => rw [h61, pow_succ]
      ring
    rw [e, mul_pow, ← pow_mul, mul_comm]
  -- Fermat: `D^{q-1} ≡ 1`
  have hferm : v.valuation F (D ^ (q - 1) - 1) < 1 := by
    letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
    haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
    letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
    have hmd : Ideal.Quotient.mk v.asIdeal d ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    have := FiniteField.pow_card_sub_one_eq_one _ hmd
    rw [Fintype.card_eq_nat_card, ← map_pow, ← map_one (Ideal.Quotient.mk v.asIdeal),
      Ideal.Quotient.eq] at this
    have e : D ^ (q - 1) - 1 = algebraMap (𝓞 F) F (d ^ (q - 1) - 1) := by
      simp [D]
    rw [e]
    exact (v.valuation_lt_one_iff_mem (K := F) _).mpr this
  set ωO := toO F ω hω
  have hωF : algebraMap (𝓞 F) F ωO = ω := rfl
  have hωv : v.valuation F ω ≤ 1 := by rw [← hωF]; exact v.valuation_le_one (K := F) ωO
  have hAω : v.valuation F (A - ω) < 1 := by
    rw [hA]
    have e : D ^ (q - 1) * (a : F) ^ K' - ω =
        D ^ (q - 1) * ((a : F) ^ K' - ω) + (D ^ (q - 1) - 1) * ω := by ring
    rw [e]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [map_mul, map_pow, hDv, one_pow, one_mul]; exact hcong
    · rw [map_mul]
      calc _ ≤ v.valuation F (D ^ (q - 1) - 1) * 1 := mul_le_mul_right hωv _
        _ < 1 := by rw [mul_one]; exact hferm
  have hμv : v.valuation F (algebraMap (𝓞 F) F μO - A) < 1 := by
    have := (v.valuation_lt_one_iff_mem (K := F) _).mpr hμA
    change v.valuation F (algebraMap (𝓞 F) F (μO - _)) < 1 at this
    rwa [map_sub] at this
  have hμω : μO - ωO ∈ v.asIdeal := by
    rw [← v.valuation_lt_one_iff_mem (K := F)]
    change v.valuation F (algebraMap (𝓞 F) F (μO - ωO)) < 1
    rw [map_sub, hωF]
    have e : algebraMap (𝓞 F) F μO - ω = (algebraMap (𝓞 F) F μO - A) + (A - ω) := by ring
    rw [e]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hμv hAω)
  have heq := eq_of_pow_eq_one_of_sub_mem v.asIdeal hv (rootO_pow F μ) (toO_pow F ω hω) hμω
  have := congrArg (fun x : 𝓞 F => (x : F)) heq
  simpa [μO, rootO, ωO, toO] using this

theorem psi_artinFrob (v : HeightOneSpectrum (𝓞 F)) (hv : ((6 : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (ha : v.valuation F (a : F) = 1) (ω : F) (hω : ω ^ 6 = 1)
    (hcong : v.valuation F ((a : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6) - ω) < 1) :
    ((psi F hζ ι a (artinFrob F (KM F a) v) : ℂˣ) : ℂ) = ι ω := by
  rw [psi_apply, kch_artinFrob hζ a v hv ha ω hω hcong]

/-- **Ramified** at `v` when `6 ∤ v(a)`. -/
theorem not_isUnramifiedAt_psi (v : HeightOneSpectrum (𝓞 F))
    (ha : ∀ k : ℤ, v.valuation F (a : F) ≠ WithZero.exp (6 * k)) :
    ¬ ArtinL.Abelian.IsUnramifiedAt (psi F hζ ι a) v := by
  intro hun
  set K := KM F a
  have hbot : ArtinL.Abelian.inertiaGroup F K v = ⊥ := by
    rw [eq_bot_iff]; intro σ hσ
    rw [Subgroup.mem_bot]; exact (psi_eq_one_iff_forall hζ ι a σ).1 (hun σ hσ)
  have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := K ≃ₐ[F] K) v.asIdeal
    (primeAbove F K v)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal (primeAbove F K v) (K ≃ₐ[F] K)] at h1
  have hc : Nat.card ((primeAbove F K v).inertia (K ≃ₐ[F] K)) = 1 := by
    have : (primeAbove F K v).inertia (K ≃ₐ[F] K) = ⊥ := hbot
    rw [this]; simp
  rw [hc] at h1
  haveI : (wAbove a v).asIdeal.LiesOver v.asIdeal := primeAbove_liesOver F K v
  have he : v.asIdeal.ramificationIdx' (wAbove a v).asIdeal = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot]
    exact h1.symm
  have hval := HeightOneSpectrum.valuation_liesOver K v (wAbove a v) (a : F)
  rw [he, pow_one] at hval
  have hβ : (rootKF (ℓ := 6) F a).β ≠ 0 := (rootKF (ℓ := 6) F a).ne_zero
  have hw0 : (wAbove a v).valuation K (rootKF (ℓ := 6) F a).β ≠ 0 := by
    simpa using hβ
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (wAbove a v).valuation K (rootKF (ℓ := 6) F a).β = WithZero.exp k :=
    ⟨_, (WithZero.exp_log hw0).symm⟩
  apply ha k
  rw [hval, ← rootKF_pow, map_pow, hk, ← WithZero.exp_nsmul]
  congr 1

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3K_Wild: the conductor exponents of `ψ_a`

* `intValuation_smul_sub_le`: for `σ` in the `i`-th ramification group (`i ≥ 1`), i.e.
  `σ x ≡ x (mod 𝔓^{i+1})` for all `x`, one has `w(σx − x) ≤ w(x) e^{−i}` (uniformizer induction).
* `le_of_mem_ramificationGroup`: if moreover `ψ_a σ ≠ 1` then `i ≤ 6 n_v`, where `v(6) = e^{−n_v}`.
* `conductorExponent_psi_le`: `e_v(ψ_a) ≤ 1 + 6 n_v`; it is `0` where `ψ_a` is unramified and `≤ 1`
  at `v ∤ 6`. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin ArtinPrimitiveRoots.L3K.KB WithZero

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

section Generic

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {G : Type*} [Group G]
  [MulSemiringAction G R] (w : HeightOneSpectrum R)

/-- A factorization `t x = ϖ x'` with `t ∉ 𝔓`, for `x ∈ 𝔓` and `w(ϖ) = e^{−1}`. -/
lemma exists_mul_eq_mul (ϖ x : R) (hϖ : w.intValuation ϖ = exp (-1 : ℤ)) (hx : x ∈ w.asIdeal) :
    ∃ t x' : R, t ∉ w.asIdeal ∧ t * x = ϖ * x' := by
  have hϖmem : ϖ ∈ w.asIdeal := by
    rw [← w.intValuation_lt_one_iff_mem, hϖ]; rw [← exp_zero]; exact exp_lt_exp.2 (by norm_num)
  obtain ⟨B, hB⟩ : w.asIdeal ∣ Ideal.span {ϖ} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hϖmem
  have hBnot : ¬ B ≤ w.asIdeal := by
    intro hle
    have : Ideal.span {ϖ} ≤ w.asIdeal ^ 2 := by
      rw [hB, sq]; exact Ideal.mul_mono_right hle
    rw [Ideal.span_singleton_le_iff_mem, ← w.intValuation_le_pow_iff_mem, hϖ] at this
    have := exp_le_exp.1 this
    norm_num at this
  obtain ⟨t, htB, htw⟩ := SetLike.not_le_iff_exists.1 hBnot
  have hmem : t * x ∈ Ideal.span {ϖ} := by
    rw [hB, mul_comm w.asIdeal B]; exact Ideal.mul_mem_mul htB hx
  obtain ⟨x', hx'⟩ := Ideal.mem_span_singleton'.1 hmem
  exact ⟨t, x', htw, by rw [← hx', mul_comm]⟩

/-- **Relative congruence.** -/
theorem intValuation_smul_sub_le (σ : G) (i : ℕ) (hi : 1 ≤ i)
    (hσ : ∀ x : R, σ • x - x ∈ w.asIdeal ^ (i + 1)) :
    ∀ m : ℕ, ∀ x : R, w.intValuation x = exp (-(m : ℤ)) →
      w.intValuation (σ • x - x) ≤ exp (-((m + i : ℕ) : ℤ)) := by
  have hbase : ∀ x : R, w.intValuation (σ • x - x) ≤ exp (-((i + 1 : ℕ) : ℤ)) := fun x =>
    (w.intValuation_le_pow_iff_mem _ _).2 (hσ x)
  obtain ⟨ϖ, hϖ⟩ := w.intValuation_exists_uniformizer
  intro m
  induction m with
  | zero =>
    intro x _
    refine (hbase x).trans (exp_le_exp.2 ?_)
    push_cast; linarith
  | succ m ih =>
    intro x hx
    have hxmem : x ∈ w.asIdeal := by
      rw [← w.intValuation_lt_one_iff_mem, hx]; rw [← exp_zero]; exact exp_lt_exp.2 (by push_cast; linarith)
    obtain ⟨t, x', ht, htx⟩ := exists_mul_eq_mul w ϖ x hϖ hxmem
    have hvt : w.intValuation t = 1 := HeightOneSpectrum.intValuation_eq_one_iff.2 ht
    have hvx' : w.intValuation x' = exp (-(m : ℤ)) := by
      have h1 := congrArg w.intValuation htx
      rw [map_mul, map_mul, hvt, one_mul, hx, hϖ] at h1
      have h2 : exp (-((m + 1 : ℕ) : ℤ)) = exp (-1 : ℤ) * exp (-(m : ℤ)) := by
        rw [← exp_add]; congr 1; push_cast; ring
      rw [h2] at h1
      exact (mul_left_cancel₀ (by simp) h1).symm
    have ih' := ih x' hvx'
    -- `w(σ x') ≤ e^{−m}`
    have hσx' : w.intValuation (σ • x') ≤ exp (-(m : ℤ)) := by
      have : σ • x' = x' + (σ • x' - x') := by ring
      rw [this]
      refine (Valuation.map_add _ _ _).trans (max_le hvx'.le (ih'.trans (exp_le_exp.2 ?_)))
      push_cast; linarith
    -- `w(σ(t x) − t x) ≤ e^{−(m+1+i)}`
    have hϖσ := hbase ϖ
    have h1 : σ • (t * x) - t * x = (σ • ϖ - ϖ) * σ • x' + ϖ * (σ • x' - x') := by
      rw [htx, smul_mul']; ring
    have hA : w.intValuation (σ • (t * x) - t * x) ≤ exp (-((m + 1 + i : ℕ) : ℤ)) := by
      rw [h1]
      refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
      · rw [map_mul]
        calc w.intValuation (σ • ϖ - ϖ) * w.intValuation (σ • x')
            ≤ exp (-((i + 1 : ℕ) : ℤ)) * exp (-(m : ℤ)) := mul_le_mul' hϖσ hσx'
          _ = exp (-((m + 1 + i : ℕ) : ℤ)) := by rw [← exp_add]; congr 1; push_cast; ring
      · rw [map_mul, hϖ]
        calc exp (-1 : ℤ) * w.intValuation (σ • x' - x')
            ≤ exp (-1 : ℤ) * exp (-((m + i : ℕ) : ℤ)) := mul_le_mul_right ih' _
          _ = exp (-((m + 1 + i : ℕ) : ℤ)) := by rw [← exp_add]; congr 1; push_cast; ring
    -- `w(σ t) = 1`
    have hσt : w.intValuation (σ • t) = 1 := by
      have hlt : w.intValuation (σ • t - t) < 1 :=
        (hbase t).trans_lt (by rw [← exp_zero]; exact exp_lt_exp.2 (by push_cast; linarith))
      have : σ • t = t + (σ • t - t) := by ring
      rw [this, Valuation.map_add_eq_of_lt_left _ (by rw [hvt]; exact hlt), hvt]
    have h2 : σ • (t * x) - t * x = σ • t * (σ • x - x) + x * (σ • t - t) := by
      rw [smul_mul']; ring
    have hB : w.intValuation (x * (σ • t - t)) ≤ exp (-((m + 1 + i : ℕ) : ℤ)) := by
      rw [map_mul, hx]
      calc exp (-((m + 1 : ℕ) : ℤ)) * w.intValuation (σ • t - t)
          ≤ exp (-((m + 1 : ℕ) : ℤ)) * exp (-((i + 1 : ℕ) : ℤ)) := mul_le_mul_right (hbase t) _
        _ ≤ exp (-((m + 1 + i : ℕ) : ℤ)) := by
          rw [← exp_add]; exact exp_le_exp.2 (by push_cast; linarith)
    have hC : w.intValuation (σ • t * (σ • x - x)) ≤ exp (-((m + 1 + i : ℕ) : ℤ)) := by
      have : σ • t * (σ • x - x) = (σ • (t * x) - t * x) - x * (σ • t - t) := by rw [h2]; ring
      rw [this]
      refine (Valuation.map_sub _ _ _).trans (max_le hA hB)
    rw [map_mul, hσt, one_mul] at hC
    convert hC using 3

end Generic

section Kummer

variable {F : Type} [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ 6) (ι : F →+* ℂ)
  (a : Fˣ)

/-- `6 = (1 − μ) c` in `𝓞 F` for a sixth root of unity `μ ≠ 1`. -/
lemma six_eq_mul {R : Type*} [CommRing R] [IsDomain R] {μ : R} (h6 : μ ^ 6 = 1) (h1 : μ ≠ 1) :
    ∃ c : R, (6 : R) = (1 - μ) * c := by
  have hsum : ∑ k ∈ Finset.range 6, μ ^ k = 0 := by
    have h := geom_sum_mul μ 6
    rw [h6, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 h1)
  refine ⟨∑ k ∈ Finset.range 6, ∑ j ∈ Finset.range k, μ ^ j, ?_⟩
  have : ∑ k ∈ Finset.range 6, (∑ j ∈ Finset.range k, μ ^ j) * (μ - 1) =
      ∑ k ∈ Finset.range 6, (μ ^ k - 1) := Finset.sum_congr rfl fun k _ => geom_sum_mul μ k
  rw [← Finset.sum_mul, Finset.sum_sub_distrib, hsum] at this
  simp at this
  linear_combination this

/-- An integral Kummer generator `y = d β`. -/
lemma exists_intGen' : ∃ (d : 𝓞 F) (y : 𝓞 (KM F a)), d ≠ 0 ∧
    (y : KM F a) = algebraMap F (KM F a) (algebraMap (𝓞 F) F d) * (rootKF (ℓ := 6) F a).β := by
  obtain ⟨n, d, hd, hnd⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (a : F)
  have hd0 : (d : 𝓞 F) ≠ 0 := nonZeroDivisors.ne_zero hd
  set K := KM F a
  set β : K := algebraMap F K (algebraMap (𝓞 F) F d) * (rootKF (ℓ := 6) F a).β
  have hdF : algebraMap (𝓞 F) F d ≠ 0 := by simpa using hd0
  have hβpow : β ^ 6 = algebraMap F K (algebraMap (𝓞 F) F (d ^ 5 * n)) := by
    rw [mul_pow, rootKF_pow, ← map_pow, ← map_mul]
    congr 1
    rw [← hnd, map_mul, map_pow]
    field_simp
  have hint : IsIntegral ℤ β := by
    apply IsIntegral.of_pow (by norm_num : 0 < 6)
    rw [hβpow, ← IsScalarTower.algebraMap_apply]
    exact (((d : 𝓞 F) ^ 5 * n).isIntegral_coe).map (IsScalarTower.toAlgHom ℤ F K)
  exact ⟨d, ⟨β, hint⟩, hd0, rfl⟩

/-- `v(6) = e^{−n_v}`. -/
def n6 (v : HeightOneSpectrum (𝓞 F)) : ℕ := (-(log (v.intValuation (6 : 𝓞 F)))).toNat

lemma intValuation_six (v : HeightOneSpectrum (𝓞 F)) :
    v.intValuation (6 : 𝓞 F) = exp (-((n6 v : ℕ) : ℤ)) := by
  have h6 : (6 : 𝓞 F) ≠ 0 := by
    intro h; have := congrArg (fun x : 𝓞 F => (x : F)) h; simp at this
  have hne := v.intValuation_ne_zero _ h6
  have hle := v.intValuation_le_one (6 : 𝓞 F)
  have hlog : log (v.intValuation (6 : 𝓞 F)) ≤ 0 := by
    rw [← exp_log hne, ← exp_zero, exp_le_exp] at hle; exact hle
  rw [n6, Int.toNat_of_nonneg (by linarith), neg_neg, exp_log hne]

lemma n6_eq_zero (v : HeightOneSpectrum (𝓞 F)) (hv : ((6 : ℕ) : 𝓞 F) ∉ v.asIdeal) : n6 v = 0 := by
  have h1 : v.intValuation (6 : 𝓞 F) = 1 := HeightOneSpectrum.intValuation_eq_one_iff.2 (by
    simpa using hv)
  have := intValuation_six v
  rw [h1] at this
  have h2 := congrArg log this
  rw [log_one, log_exp] at h2
  omega

include hζ in
lemma card_gal_le : Nat.card (KM F a ≃ₐ[F] KM F a) ≤ 6 :=
  (Nat.card_le_card_of_injective _ (kch_KF_injective a hζ (rootKF F a) (rootKF_pow F a))).trans
    (card_rootsOfUnity _ _)

include hζ in
/-- **Wild bound.** If `σ` lies in the `i`-th ramification group (`i ≥ 1`) and `ψ_a σ ≠ 1`,
then `i ≤ 6 n_v`. -/
theorem le_of_mem_ramificationGroup (v : HeightOneSpectrum (𝓞 F)) (i : ℕ) (hi : 1 ≤ i)
    (σ : KM F a ≃ₐ[F] KM F a) (hσ : σ ∈ ArtinL.Abelian.ramificationGroup F (KM F a) v i)
    (hψ : psi F hζ ι a σ ≠ 1) : i ≤ 6 * n6 v := by
  set K := KM F a
  set w := wAbove a v
  haveI : w.asIdeal.LiesOver v.asIdeal := primeAbove_liesOver F K v
  obtain ⟨d, y, hd, hy⟩ := exists_intGen' a
  set μ := rootO F (kch hζ (rootKF (ℓ := 6) F a) σ)
  have hsm : σ • y = algebraMap (𝓞 F) (𝓞 K) μ * y := smul_intGen F hζ a d y hy σ
  have hμ1 : μ ≠ 1 := by
    intro h
    apply hψ
    have : kch hζ (rootKF (ℓ := 6) F a) σ = 1 := by
      apply Subtype.ext; apply Units.ext
      have := congrArg (fun x : 𝓞 F => (x : F)) h
      simpa [μ, rootO] using this
    rw [psi, MonoidHom.comp_apply, MonoidHom.comp_apply, this]; simp
  have hy0 : y ≠ 0 := by
    intro h
    have : (y : K) = 0 := by rw [h]; rfl
    rw [hy] at this
    simp at this
    rcases this with h1 | h1
    · exact hd h1
    · exact (rootKF (ℓ := 6) F a).ne_zero h1
  set m : ℕ := (-(log (w.intValuation y))).toNat
  have hwy : w.intValuation y = exp (-(m : ℤ)) := by
    have hne := w.intValuation_ne_zero _ hy0
    have hlog : log (w.intValuation y) ≤ 0 := by
      have hle := w.intValuation_le_one y
      rw [← exp_log hne, ← exp_zero, exp_le_exp] at hle; exact hle
    rw [Int.toNat_of_nonneg (by linarith), neg_neg, exp_log hne]
  have hin : ∀ x : 𝓞 K, σ • x - x ∈ w.asIdeal ^ (i + 1) := fun x => hσ x
  have hrel := intValuation_smul_sub_le w σ i hi hin m y hwy
  rw [hsm, show algebraMap (𝓞 F) (𝓞 K) μ * y - y = algebraMap (𝓞 F) (𝓞 K) (μ - 1) * y by
    rw [map_sub, map_one]; ring, map_mul, hwy] at hrel
  have hμv : w.intValuation (algebraMap (𝓞 F) (𝓞 K) (μ - 1)) ≤ exp (-(i : ℤ)) := by
    have h2 : exp (-((m + i : ℕ) : ℤ)) = exp (-(i : ℤ)) * exp (-(m : ℤ)) := by
      rw [← exp_add]; congr 1; push_cast; ring
    rw [h2] at hrel
    exact le_of_mul_le_mul_right hrel (by simp)
  obtain ⟨c, hc⟩ := six_eq_mul (rootO_pow F _) hμ1
  have h6 : w.intValuation (algebraMap (𝓞 F) (𝓞 K) 6) ≤ exp (-(i : ℤ)) := by
    rw [hc, map_mul, map_mul]
    have hneg : w.intValuation (algebraMap (𝓞 F) (𝓞 K) (1 - μ)) =
        w.intValuation (algebraMap (𝓞 F) (𝓞 K) (μ - 1)) := by
      rw [show (1 : 𝓞 F) - μ = -(μ - 1) by ring, map_neg, Valuation.map_neg]
    rw [hneg]
    calc _ ≤ w.intValuation (algebraMap (𝓞 F) (𝓞 K) (μ - 1)) * 1 :=
          mul_le_mul_right (w.intValuation_le_one _) _
      _ ≤ exp (-(i : ℤ)) := by rw [mul_one]; exact hμv
  rw [← HeightOneSpectrum.intValuation_liesOver v w, intValuation_six, ← exp_nsmul] at h6
  rw [exp_le_exp] at h6
  -- `e ≤ 6`
  have he : v.asIdeal.ramificationIdx' w.asIdeal ≤ 6 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot]
    have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := K ≃ₐ[F] K) v.asIdeal
      (primeAbove F K v)
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal (primeAbove F K v) (K ≃ₐ[F] K)] at h1
    change (primeAbove F K v).ramificationIdx (𝓞 F) ≤ 6
    rw [← h1]
    exact (Subgroup.card_le_card_group _).trans (card_gal_le hζ a)
  have : (i : ℤ) ≤ (v.asIdeal.ramificationIdx' w.asIdeal) * (n6 v) := by
    simp only [nsmul_eq_mul] at h6; push_cast at h6; linarith
  have h3 : ((v.asIdeal.ramificationIdx' w.asIdeal : ℕ) : ℤ) * (n6 v) ≤ 6 * (n6 v) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast he) (by positivity)
  omega

lemma ramificationGroup_le_inertiaGroup (v : HeightOneSpectrum (𝓞 F)) (i : ℕ) :
    ArtinL.Abelian.ramificationGroup F (KM F a) v i ≤ ArtinL.Abelian.inertiaGroup F (KM F a) v := by
  intro σ hσ x
  exact Ideal.pow_le_self (Nat.succ_ne_zero i) (hσ x)

/-- The swan conductor is at most `6 n_v`, and `0` if `ψ_a` is trivial on the higher groups. -/
theorem swanConductor_psi_le (v : HeightOneSpectrum (𝓞 F)) (B : ℕ)
    (hB : ∀ i : ℕ, 1 ≤ i → ∀ σ ∈ ArtinL.Abelian.ramificationGroup F (KM F a) v i,
      psi F hζ ι a σ ≠ 1 → i ≤ B) :
    ArtinL.Abelian.swanConductor (psi F hζ ι a) v ≤ B := by
  classical
  unfold ArtinL.Abelian.swanConductor
  set f : ℕ → ℚ := fun i =>
    (Nat.card (ArtinL.Abelian.ramificationGroup F (KM F a) v (i + 1)) : ℚ) /
      (Nat.card (ArtinL.Abelian.inertiaGroup F (KM F a) v) : ℚ) *
      (if ∀ σ ∈ ArtinL.Abelian.ramificationGroup F (KM F a) v (i + 1), psi F hζ ι a σ = 1
        then 0 else 1)
  have hsupp : Function.support f ⊆ (Finset.range B : Set ℕ) := by
    intro i hi
    rw [Function.mem_support] at hi
    by_contra hiB
    apply hi
    simp only [f]
    rw [if_pos, mul_zero]
    intro σ hσ
    by_contra hne
    have := hB (i + 1) (by omega) σ hσ hne
    simp at hiB; omega
  rw [finsum_eq_sum_of_support_subset f hsupp]
  have hle : ∀ i ∈ Finset.range B, f i ≤ 1 := by
    intro i _
    simp only [f]
    have hpos : (0 : ℚ) < Nat.card (ArtinL.Abelian.inertiaGroup F (KM F a) v) := by
      exact_mod_cast Nat.card_pos
    have hcard : (Nat.card (ArtinL.Abelian.ramificationGroup F (KM F a) v (i + 1)) : ℚ) ≤
        Nat.card (ArtinL.Abelian.inertiaGroup F (KM F a) v) := by
      exact_mod_cast Subgroup.card_le_of_le (ramificationGroup_le_inertiaGroup a v (i + 1))
    have h1 : (Nat.card (ArtinL.Abelian.ramificationGroup F (KM F a) v (i + 1)) : ℚ) /
        (Nat.card (ArtinL.Abelian.inertiaGroup F (KM F a) v) : ℚ) ≤ 1 :=
      (div_le_one hpos).2 hcard
    have h0 : (0 : ℚ) ≤ (Nat.card (ArtinL.Abelian.ramificationGroup F (KM F a) v (i + 1)) : ℚ) /
        (Nat.card (ArtinL.Abelian.inertiaGroup F (KM F a) v) : ℚ) := by positivity
    split_ifs <;> nlinarith
  calc ∑ i ∈ Finset.range B, f i ≤ ∑ _i ∈ Finset.range B, (1 : ℚ) := Finset.sum_le_sum hle
    _ = B := by simp

theorem swanConductor_psi_le_six (v : HeightOneSpectrum (𝓞 F)) :
    ArtinL.Abelian.swanConductor (psi F hζ ι a) v ≤ (6 * n6 v : ℕ) :=
  swanConductor_psi_le hζ ι a v _ fun i hi σ hσ hψ => le_of_mem_ramificationGroup hζ ι a v i hi σ hσ hψ

/-- `e_v(ψ_a) ≤ 1 + 6 n_v`. -/
theorem conductorExponent_psi_le (v : HeightOneSpectrum (𝓞 F)) :
    ArtinL.Abelian.conductorExponent (psi F hζ ι a) v ≤ 1 + 6 * n6 v := by
  unfold ArtinL.Abelian.conductorExponent
  have h1 : ⌈ArtinL.Abelian.swanConductor (psi F hζ ι a) v⌉₊ ≤ 6 * n6 v := by
    rw [Nat.ceil_le]; exact_mod_cast swanConductor_psi_le_six hζ ι a v
  split_ifs <;> omega

/-- `e_v(ψ_a) ≤ 1` at `v ∤ 6`. -/
theorem conductorExponent_psi_le_one (v : HeightOneSpectrum (𝓞 F))
    (hv : ((6 : ℕ) : 𝓞 F) ∉ v.asIdeal) :
    ArtinL.Abelian.conductorExponent (psi F hζ ι a) v ≤ 1 := by
  have := conductorExponent_psi_le hζ ι a v
  rw [n6_eq_zero v hv] at this; simpa using this

/-- `e_v(ψ_a) = 0` where `ψ_a` is unramified. -/
theorem conductorExponent_psi_eq_zero (v : HeightOneSpectrum (𝓞 F))
    (hun : ArtinL.Abelian.IsUnramifiedAt (psi F hζ ι a) v) :
    ArtinL.Abelian.conductorExponent (psi F hζ ι a) v = 0 := by
  have hs : ArtinL.Abelian.swanConductor (psi F hζ ι a) v ≤ (0 : ℕ) :=
    swanConductor_psi_le hζ ι a v 0 fun i _ σ hσ hψ =>
      absurd (hun σ (ramificationGroup_le_inertiaGroup a v i hσ)) hψ
  unfold ArtinL.Abelian.conductorExponent
  rw [if_pos hun, zero_add, Nat.ceil_eq_zero]
  exact_mod_cast hs

end Kummer

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3F_Quad: the Kummer character of `a = x³` is quadratic

For `a = x³`, `β² ∈ F` (`β⁶ = x³`, so `β²/x` is a cube root of unity, and those lie in `F`).
Hence `kch σ ² = 1` and `ψ_a(σ)² = 1` for every `σ`. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin ArtinPrimitiveRoots.L3K.KB
  ArtinPrimitiveRoots.L3K

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3F

variable {F : Type} [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ 6) (ι : F →+* ℂ)
  (a : Fˣ)

include hζ in
/-- `β² ∈ F` when `a` is a cube. -/
theorem sq_root_mem (x : F) (hx : (a : F) = x ^ 3) :
    ∃ c : F, c ≠ 0 ∧ (rootKF (ℓ := 6) F a).β ^ 2 = algebraMap F (KM F a) c := by
  set K := KM F a
  set β := (rootKF (ℓ := 6) F a).β
  have hβ0 : β ≠ 0 := (rootKF (ℓ := 6) F a).ne_zero
  have hβ6 : β ^ 6 = algebraMap F K (a : F) := rootKF_pow F a
  have hx0 : x ≠ 0 := by
    intro h; apply a.ne_zero; rw [hx, h]; ring
  have hxK : algebraMap F K x ≠ 0 := by simpa using hx0
  set t := β ^ 2 / algebraMap F K x
  have ht3 : t ^ 3 = 1 := by
    simp only [t, div_pow, ← pow_mul]
    rw [show 2 * 3 = 6 by norm_num, hβ6, hx, map_pow, div_self (pow_ne_zero _ hxK)]
  set ω := ζ ^ 2
  have hω : IsPrimitiveRoot ω 3 := hζ.pow (by norm_num) (by norm_num)
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hωsum : ω ^ 2 + ω + 1 = 0 := by
    have h := hω.geom_sum_eq_zero (by norm_num)
    simp [Finset.sum_range_succ] at h
    linear_combination h
  set ωK := algebraMap F K ω
  have hωK3 : ωK ^ 3 = 1 := by rw [← map_pow, hω3, map_one]
  have hωKs : ωK ^ 2 + ωK + 1 = 0 := by
    have := congrArg (algebraMap F K) hωsum
    simpa [map_add, map_pow] using this
  have hprod : (t - 1) * (t - ωK) * (t - ωK ^ 2) = 0 := by
    linear_combination ht3 + (-(t ^ 2) + t * ωK) * hωKs - hωK3
  have key : ∃ c : F, c ≠ 0 ∧ t = algebraMap F K c := by
    rcases mul_eq_zero.1 hprod with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact ⟨1, one_ne_zero, by rw [map_one]; exact sub_eq_zero.1 h⟩
      · refine ⟨ω, ?_, sub_eq_zero.1 h⟩
        intro h0; rw [h0] at hω3; norm_num at hω3
    · refine ⟨ω ^ 2, ?_, by rw [map_pow]; exact sub_eq_zero.1 h⟩
      intro h0; rw [pow_eq_zero_iff (by norm_num)] at h0; rw [h0] at hω3; norm_num at hω3
  obtain ⟨c, hc0, hc⟩ := key
  refine ⟨c * x, mul_ne_zero hc0 hx0, ?_⟩
  rw [map_mul, ← hc]
  simp only [t]
  exact (div_mul_cancel₀ _ hxK).symm

include hζ in
/-- `kch σ ² = 1` when `a` is a cube. -/
theorem kch_sq (x : F) (hx : (a : F) = x ^ 3) (σ : KM F a ≃ₐ[F] KM F a) :
    ((kch hζ (rootKF (ℓ := 6) F a) σ : Fˣ) : F) ^ 2 = 1 := by
  obtain ⟨c, hc0, hc⟩ := sq_root_mem hζ a x hx
  set K := KM F a
  set β := (rootKF (ℓ := 6) F a).β
  have hβ0 : β ≠ 0 := (rootKF (ℓ := 6) F a).ne_zero
  apply FaithfulSMul.algebraMap_injective F K
  rw [map_pow, algebraMap_kch, map_one, div_pow, ← map_pow, hc, AlgEquiv.commutes,
    div_self (by simpa using hc0)]

include hζ in
theorem kch_eq_one_or (x : F) (hx : (a : F) = x ^ 3) (σ : KM F a ≃ₐ[F] KM F a) :
    ((kch hζ (rootKF (ℓ := 6) F a) σ : Fˣ) : F) = 1 ∨
      ((kch hζ (rootKF (ℓ := 6) F a) σ : Fˣ) : F) = -1 :=
  mul_self_eq_one_iff.1 (by rw [← sq]; exact kch_sq hζ a x hx σ)

/-- `ψ_a(σ)² = 1` when `a` is a cube. -/
theorem psi_sq (x : F) (hx : (a : F) = x ^ 3) (σ : KM F a ≃ₐ[F] KM F a) :
    psi F hζ ι a σ ^ 2 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, psi_apply, ← map_pow, kch_sq hζ a x hx σ, map_one, Units.val_one]

end L3F

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3F_Split: a local square splits

For `a = x³` with `x = y² d`, `v(d − 1) ≤ e^{−2(6 n_v + 1)}`, the quadratic character `ψ_a` is trivial
on the decomposition group of `primeAbove v`: if `σ β = −β` then `η = β³/y³` has `η² = d³ ≡ 1` and
`σ η = −η`, so `w(η − 1) = w(η + 1)` is small, and so is `w(2)`, against `w(6) ≥ e^{−6 n_v}`.
Hence `ψ_a` is unramified at `v` and `ψ_a(Frob_v) = 1`. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin ArtinPrimitiveRoots.L3K.KB
  ArtinPrimitiveRoots.L3K WithZero

open scoped Pointwise

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3F

section Generic

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {G : Type*} [Group G]
  [MulSemiringAction G R] (w : HeightOneSpectrum R)

lemma smul_mem_pow {σ : G} (hσ : σ • w.asIdeal = w.asIdeal) (n : ℕ) {r : R}
    (hr : r ∈ w.asIdeal ^ n) : σ • r ∈ w.asIdeal ^ n := by
  have h := Ideal.smul_mem_pointwise_smul σ r _ hr
  rwa [smul_pow', hσ] at h

lemma intValuation_smul_le {σ : G} (hσ : σ • w.asIdeal = w.asIdeal) (r : R) :
    w.intValuation (σ • r) ≤ w.intValuation r := by
  by_cases hr : r = 0
  · rw [hr, smul_zero]
  have hne := w.intValuation_ne_zero _ hr
  have hle := w.intValuation_le_one r
  have hlog : log (w.intValuation r) ≤ 0 := by
    rw [← exp_log hne, ← exp_zero, exp_le_exp] at hle; exact hle
  set m : ℕ := (-(log (w.intValuation r))).toNat
  have hm : w.intValuation r = exp (-(m : ℤ)) := by
    rw [Int.toNat_of_nonneg (by linarith), neg_neg, exp_log hne]
  have hmem : r ∈ w.asIdeal ^ m := (w.intValuation_le_pow_iff_mem r m).1 hm.le
  rw [hm]
  exact (w.intValuation_le_pow_iff_mem _ m).2 (smul_mem_pow w hσ m hmem)

lemma intValuation_smul {σ : G} (hσ : σ • w.asIdeal = w.asIdeal) (r : R) :
    w.intValuation (σ • r) = w.intValuation r := by
  refine le_antisymm (intValuation_smul_le w hσ r) ?_
  have hσ' : σ⁻¹ • w.asIdeal = w.asIdeal := by
    conv_lhs => rw [← hσ]
    rw [inv_smul_smul]
  have := intValuation_smul_le w hσ' (σ • r)
  rwa [inv_smul_smul] at this

end Generic

variable {F : Type} [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ 6) (ι : F →+* ℂ)
  (a : Fˣ)

/-- The valuation of `wAbove v` is invariant under the decomposition group. -/
lemma valuation_apply_of_mem_stabilizer (v : HeightOneSpectrum (𝓞 F))
    {σ : KM F a ≃ₐ[F] KM F a}
    (hσ : σ ∈ MulAction.stabilizer (KM F a ≃ₐ[F] KM F a) (primeAbove F (KM F a) v)) (z : KM F a) :
    (wAbove a v).valuation (KM F a) (σ z) = (wAbove a v).valuation (KM F a) z := by
  have hσ' : σ • (wAbove a v).asIdeal = (wAbove a v).asIdeal := hσ
  obtain ⟨r, s, hs, hz⟩ := IsFractionRing.div_surjective (A := 𝓞 (KM F a)) z
  subst hz
  have hr : σ (algebraMap (𝓞 (KM F a)) (KM F a) r) =
      algebraMap (𝓞 (KM F a)) (KM F a) (σ • r) := rfl
  have hs' : σ (algebraMap (𝓞 (KM F a)) (KM F a) s) =
      algebraMap (𝓞 (KM F a)) (KM F a) (σ • (s : 𝓞 (KM F a))) := rfl
  rw [map_div₀, hr, hs', map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_smul _ hσ', intValuation_smul _ hσ']

include hζ in
lemma ramificationIdx_le_six (v : HeightOneSpectrum (𝓞 F)) :
    v.asIdeal.ramificationIdx' (wAbove a v).asIdeal ≤ 6 := by
  set K := KM F a
  have : (wAbove a v).asIdeal.LiesOver v.asIdeal := primeAbove_liesOver F K v
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot]
  have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := K ≃ₐ[F] K) v.asIdeal
    (primeAbove F K v)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal (primeAbove F K v) (K ≃ₐ[F] K)] at h1
  change (primeAbove F K v).ramificationIdx (𝓞 F) ≤ 6
  rw [← h1]
  exact (Subgroup.card_le_card_group _).trans (card_gal_le hζ a)

lemma le_exp_of_mul_self_le {r : ℤᵐ⁰} {k : ℕ} (h : r * r ≤ exp (-((2 * k : ℕ) : ℤ))) :
    r ≤ exp (-(k : ℤ)) := by
  by_cases hr : r = 0
  · rw [hr]; exact zero_le
  rw [← exp_log hr, ← exp_add] at h
  rw [← exp_log hr, exp_le_exp]
  rw [exp_le_exp] at h
  push_cast at h
  linarith

include hζ in
/-- **The decomposition group acts trivially** when `a = (y² d)³`, `d ≡ 1` to high order. -/
theorem kch_eq_one_of_mem_stabilizer (x : F) (hx : (a : F) = x ^ 3) (v : HeightOneSpectrum (𝓞 F))
    (y d : F) (hy : y ≠ 0) (hxd : x = y ^ 2 * d)
    (hd : v.valuation F (d - 1) ≤ exp (-((2 * (6 * n6 v + 1) : ℕ) : ℤ)))
    (σ : KM F a ≃ₐ[F] KM F a)
    (hσ : σ ∈ MulAction.stabilizer (KM F a ≃ₐ[F] KM F a) (primeAbove F (KM F a) v)) :
    kch hζ (rootKF (ℓ := 6) F a) σ = 1 := by
  rcases kch_eq_one_or hζ a x hx σ with h1 | hm1
  · apply Subtype.ext; apply Units.ext; exact h1
  exfalso
  have hLO : (wAbove a v).asIdeal.LiesOver v.asIdeal := primeAbove_liesOver F (KM F a) v
  have he0 : v.asIdeal.ramificationIdx' (wAbove a v).asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver _ v.ne_bot
  have he6 : v.asIdeal.ramificationIdx' (wAbove a v).asIdeal ≤ 6 := ramificationIdx_le_six hζ a v
  obtain ⟨e, he⟩ : ∃ e, e = v.asIdeal.ramificationIdx' (wAbove a v).asIdeal := ⟨_, rfl⟩
  rw [← he] at he0 he6
  have hWF : ∀ z : F, (wAbove a v).valuation (KM F a) (algebraMap F (KM F a) z) =
      v.valuation F z ^ e := fun z => by
    rw [he]; exact (HeightOneSpectrum.valuation_liesOver (KM F a) v (wAbove a v) z).symm
  -- the elements
  obtain ⟨β, hβ⟩ : ∃ β, β = (rootKF (ℓ := 6) F a).β := ⟨_, rfl⟩
  have hβ0 : β ≠ 0 := hβ ▸ (rootKF (ℓ := 6) F a).ne_zero
  have hσβ : σ β = -β := by
    have h := algebraMap_kch hζ (rootKF (ℓ := 6) F a) σ
    rw [hm1, map_neg, map_one, ← hβ] at h
    have h' := (eq_div_iff hβ0).1 h
    linear_combination -h'
  have hyK : algebraMap F (KM F a) y ≠ 0 := by simpa using hy
  have hβ6 : β ^ 6 = algebraMap F (KM F a) y ^ 6 * algebraMap F (KM F a) d ^ 3 := by
    rw [hβ, rootKF_pow, hx, hxd, ← map_pow, ← map_pow, ← map_mul]; congr 1; ring
  obtain ⟨η, hη⟩ : ∃ η, η = β ^ 3 / algebraMap F (KM F a) y ^ 3 := ⟨_, rfl⟩
  have hη2 : η ^ 2 = algebraMap F (KM F a) (d ^ 3) := by
    rw [hη, div_pow, ← pow_mul, ← pow_mul, show 3 * 2 = 6 by norm_num, hβ6, map_pow]
    field_simp
  have hση : σ η = -η := by
    rw [hη, map_div₀, map_pow, map_pow, hσβ, AlgEquiv.commutes]
    ring
  -- `v(d) = 1` and `v(d³ − 1) ≤ e^{−N}`
  have hlt : v.valuation F (d - 1) < 1 :=
    hd.trans_lt (by rw [← exp_zero]; exact exp_lt_exp.2 (by push_cast; omega))
  have hvd : v.valuation F d = 1 := by
    have : d = 1 + (d - 1) := by ring
    rw [this, Valuation.map_add_eq_of_lt_left _ (by rw [Valuation.map_one]; exact hlt),
      Valuation.map_one]
  have hvd3 : v.valuation F (d ^ 3 - 1) ≤ exp (-((2 * (6 * n6 v + 1) : ℕ) : ℤ)) := by
    have : d ^ 3 - 1 = (d - 1) * (d ^ 2 + d + 1) := by ring
    rw [this, map_mul]
    have h2 : v.valuation F (d ^ 2 + d + 1) ≤ 1 := by
      refine (Valuation.map_add _ _ _).trans (max_le ((Valuation.map_add _ _ _).trans
        (max_le ?_ ?_)) ?_)
      · rw [map_pow, hvd, one_pow]
      · rw [hvd]
      · rw [Valuation.map_one]
    calc v.valuation F (d - 1) * v.valuation F (d ^ 2 + d + 1)
        ≤ v.valuation F (d - 1) * 1 := mul_le_mul_right h2 _
      _ ≤ _ := by rw [mul_one]; exact hd
  have hW1 : (wAbove a v).valuation (KM F a) (η ^ 2 - 1) ≤
      exp (-((2 * (6 * n6 v + 1) : ℕ) : ℤ)) := by
    rw [hη2, ← map_one (algebraMap F (KM F a)), ← map_sub, hWF]
    have hle1 : v.valuation F (d ^ 3 - 1) ≤ 1 :=
      hvd3.trans (by rw [← exp_zero]; exact exp_le_exp.2 (by omega))
    exact (pow_le_of_le_one (zero_le) hle1 he0).trans hvd3
  -- `w(η − 1) = w(η + 1)`
  have hsym : (wAbove a v).valuation (KM F a) (η + 1) =
      (wAbove a v).valuation (KM F a) (η - 1) := by
    have := valuation_apply_of_mem_stabilizer a v hσ (η - 1)
    rw [map_sub, map_one, hση] at this
    rw [← this, show -η - 1 = -(η + 1) by ring, Valuation.map_neg]
  have hsmall : (wAbove a v).valuation (KM F a) (η - 1) ≤ exp (-((6 * n6 v + 1 : ℕ) : ℤ)) := by
    apply le_exp_of_mul_self_le
    have : (wAbove a v).valuation (KM F a) (η - 1) * (wAbove a v).valuation (KM F a) (η - 1) =
        (wAbove a v).valuation (KM F a) (η ^ 2 - 1) := by
      calc _ = (wAbove a v).valuation (KM F a) (η - 1) * (wAbove a v).valuation (KM F a) (η + 1) := by
            rw [hsym]
        _ = _ := by rw [← map_mul]; congr 1; ring
    rw [this]; exact hW1
  have h2 : (wAbove a v).valuation (KM F a) 2 ≤ exp (-((6 * n6 v + 1 : ℕ) : ℤ)) := by
    have : (2 : KM F a) = (η + 1) - (η - 1) := by ring
    rw [this]
    exact (Valuation.map_sub _ _ _).trans (max_le (hsym ▸ hsmall) hsmall)
  -- `w(6) ≥ e^{−6 n_v}`
  have h6 : (wAbove a v).valuation (KM F a) 6 = exp (-((n6 v : ℕ) : ℤ)) ^ e := by
    have : (6 : KM F a) = algebraMap F (KM F a) (algebraMap (𝓞 F) F 6) := by rw [map_ofNat, map_ofNat]
    rw [this, hWF, HeightOneSpectrum.valuation_of_algebraMap, intValuation_six]
  have h3 : (wAbove a v).valuation (KM F a) 3 ≤ 1 := by
    have : (3 : KM F a) = algebraMap F (KM F a) (algebraMap (𝓞 F) F 3) := by rw [map_ofNat, map_ofNat]
    rw [this, hWF, HeightOneSpectrum.valuation_of_algebraMap]
    exact pow_le_one₀ (zero_le) (HeightOneSpectrum.intValuation_le_one _ _)
  have h62 : (wAbove a v).valuation (KM F a) 6 ≤ (wAbove a v).valuation (KM F a) 2 := by
    have : (6 : KM F a) = 2 * 3 := by norm_num
    rw [this, map_mul]
    calc (wAbove a v).valuation (KM F a) 2 * (wAbove a v).valuation (KM F a) 3
        ≤ (wAbove a v).valuation (KM F a) 2 * 1 := mul_le_mul_right h3 _
      _ = _ := mul_one _
  have := (h62.trans h2)
  rw [h6, ← exp_nsmul, exp_le_exp] at this
  have h' : (e : ℤ) * (n6 v) ≤ 6 * (n6 v) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast he6) (by positivity)
  simp only [nsmul_eq_mul] at this
  push_cast at this
  linarith

include hζ in
/-- Unramified, and `ψ_a(Frob_v) = 1`. -/
theorem psi_local_split (x : F) (hx : (a : F) = x ^ 3) (v : HeightOneSpectrum (𝓞 F))
    (y d : F) (hy : y ≠ 0) (hxd : x = y ^ 2 * d)
    (hd : v.valuation F (d - 1) ≤ exp (-((2 * (6 * n6 v + 1) : ℕ) : ℤ))) :
    ArtinL.Abelian.IsUnramifiedAt (psi F hζ ι a) v ∧
      ArtinL.Abelian.localValue (psi F hζ ι a) v = 1 := by
  set K := KM F a
  have hψ : ∀ σ ∈ MulAction.stabilizer (K ≃ₐ[F] K) (primeAbove F K v), psi F hζ ι a σ = 1 := by
    intro σ hσ
    have h := kch_eq_one_of_mem_stabilizer hζ a x hx v y d hy hxd hd σ hσ
    apply Units.ext
    rw [psi_apply, h]; simp
  have hun : ArtinL.Abelian.IsUnramifiedAt (psi F hζ ι a) v := fun σ hσ =>
    hψ σ (Ideal.inertia_le_stabilizer _ hσ)
  refine ⟨hun, ?_⟩
  rw [ArtinL.Abelian.localValue, if_pos hun,
    hψ _ (isArithFrobAt_artinFrob F K v).mem_stabilizer, Units.val_one]

end L3F

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3F_Cls: a finite local square-class invariant at the primes over `𝔪`

At a prime `v` with uniformizer `π`, `x ≠ 0` has `v(x) = e^k`; the invariant is the parity of `k` and
the class modulo `v^N` of an integral approximation of the unit part `x π^k`. Equal invariants give
`x₁ x₂ = y² d` with `v(d − 1) ≤ e^{−N}`. The product over the primes `v ⊇ 𝔪` is a finite type. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain WithZero

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3F

variable {F : Type} [Field F] [NumberField F]

/-- A uniformizer of `v` in `F`. -/
def unif (v : HeightOneSpectrum (𝓞 F)) : F := (v.valuation_exists_uniformizer F).choose

lemma val_unif (v : HeightOneSpectrum (𝓞 F)) : v.valuation F (unif v) = exp (-1 : ℤ) :=
  (v.valuation_exists_uniformizer F).choose_spec

lemma unif_ne_zero (v : HeightOneSpectrum (𝓞 F)) : unif v ≠ 0 := by
  intro h; have := val_unif v; rw [h, map_zero] at this; exact (exp_ne_zero this.symm).elim

/-- The exponent `k` with `v(x) = e^k`. -/
def vexp (v : HeightOneSpectrum (𝓞 F)) (x : F) : ℤ := log (v.valuation F x)

lemma val_eq_exp_vexp (v : HeightOneSpectrum (𝓞 F)) {x : F} (hx : x ≠ 0) :
    v.valuation F x = exp (vexp v x) := by
  rw [vexp, exp_log]; simpa using hx

/-- The unit part `x π^k`. -/
def unitPart (v : HeightOneSpectrum (𝓞 F)) (x : F) : F := x * unif v ^ vexp v x

lemma val_unitPart (v : HeightOneSpectrum (𝓞 F)) {x : F} (hx : x ≠ 0) :
    v.valuation F (unitPart v x) = 1 := by
  rw [unitPart, map_mul, map_zpow₀, val_unif, val_eq_exp_vexp v hx, ← exp_zsmul, ← exp_add]
  simp

lemma unitPart_ne_zero (v : HeightOneSpectrum (𝓞 F)) {x : F} (hx : x ≠ 0) : unitPart v x ≠ 0 :=
  mul_ne_zero hx (zpow_ne_zero _ (unif_ne_zero v))

/-- An integral approximation to order `N` of a `v`-integral element. -/
def approx (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) (z : F) : 𝓞 F :=
  if h : v.valuation F z ≤ 1 then
    (v.exists_valuation_sub_lt_of_integer h (Units.mk0 (exp (-(N : ℤ))) (exp_ne_zero))).choose
  else 0

lemma approx_spec (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) {z : F} (h : v.valuation F z ≤ 1) :
    v.valuation F (algebraMap (𝓞 F) F (approx v N z) - z) ≤ exp (-(N : ℤ)) := by
  rw [approx, dif_pos h]
  exact (v.exists_valuation_sub_lt_of_integer h
    (Units.mk0 (exp (-(N : ℤ))) (exp_ne_zero))).choose_spec.le

/-- The local invariant. -/
def invP (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) (x : F) : ZMod 2 × (𝓞 F ⧸ v.asIdeal ^ N) :=
  ((vexp v x : ZMod 2), Ideal.Quotient.mk _ (approx v N (unitPart v x)))

lemma val_sub_le_of_mem_pow (v : HeightOneSpectrum (𝓞 F)) {N : ℕ} {a b : 𝓞 F}
    (h : a - b ∈ v.asIdeal ^ N) :
    v.valuation F (algebraMap (𝓞 F) F a - algebraMap (𝓞 F) F b) ≤ exp (-(N : ℤ)) := by
  rw [← map_sub, HeightOneSpectrum.valuation_of_algebraMap]
  exact (v.intValuation_le_pow_iff_mem _ N).2 h

/-- **Equal invariants give a local square up to `1 + v^N`.** -/
theorem exists_sq_mul_of_invP_eq (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) {x₁ x₂ : F}
    (h₁ : x₁ ≠ 0) (h₂ : x₂ ≠ 0) (h : invP v N x₁ = invP v N x₂) :
    ∃ y d : F, y ≠ 0 ∧ x₁ * x₂ = y ^ 2 * d ∧ v.valuation F (d - 1) ≤ exp (-(N : ℤ)) := by
  have hpar : ((vexp v x₁ : ℤ) : ZMod 2) = ((vexp v x₂ : ℤ) : ZMod 2) := congrArg Prod.fst h
  have hres := congrArg Prod.snd h
  simp only [invP] at hres
  rw [Ideal.Quotient.eq] at hres
  obtain ⟨j, hj⟩ : ∃ j : ℤ, vexp v x₁ + vexp v x₂ = 2 * j := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hpar
    obtain ⟨m, hm⟩ := hpar
    push_cast at hm
    exact ⟨vexp v x₁ + m, by linarith⟩
  set u₁ := unitPart v x₁
  set u₂ := unitPart v x₂
  have hu₁ : u₁ ≠ 0 := unitPart_ne_zero v h₁
  have hv₁ := val_unitPart v h₁
  have hv₂ := val_unitPart v h₂
  have hπ := unif_ne_zero v
  refine ⟨unif v ^ (-j) * u₁, u₂ / u₁, mul_ne_zero (zpow_ne_zero _ hπ) hu₁, ?_, ?_⟩
  · have e1 : x₁ = u₁ * unif v ^ (-vexp v x₁) := by
      simp only [u₁, unitPart, mul_assoc, ← zpow_add₀ hπ, add_neg_cancel, zpow_zero, mul_one]
    have e2 : x₂ = u₂ * unif v ^ (-vexp v x₂) := by
      simp only [u₂, unitPart, mul_assoc, ← zpow_add₀ hπ, add_neg_cancel, zpow_zero, mul_one]
    have e3 : unif v ^ (-vexp v x₁) * unif v ^ (-vexp v x₂) = (unif v ^ (-j)) ^ 2 := by
      rw [← zpow_add₀ hπ, ← zpow_natCast, ← zpow_mul]
      congr 1; push_cast; linarith
    calc x₁ * x₂ = (u₁ * unif v ^ (-vexp v x₁)) * (u₂ * unif v ^ (-vexp v x₂)) := by
          rw [← e1, ← e2]
      _ = u₁ * u₂ * (unif v ^ (-vexp v x₁) * unif v ^ (-vexp v x₂)) := by ring
      _ = u₁ * u₂ * (unif v ^ (-j)) ^ 2 := by rw [e3]
      _ = (unif v ^ (-j) * u₁) ^ 2 * (u₂ / u₁) := by
          rw [mul_pow]; field_simp
  · have hd : u₂ / u₁ - 1 = (u₂ - u₁) / u₁ := by field_simp
    rw [hd, map_div₀, hv₁, div_one]
    have hA := approx_spec v N (le_of_eq hv₁)
    have hB := approx_spec v N (le_of_eq hv₂)
    have hC := val_sub_le_of_mem_pow v hres
    have e : u₂ - u₁ = (algebraMap (𝓞 F) F (approx v N u₁) - u₁) -
        (algebraMap (𝓞 F) F (approx v N u₂) - u₂) -
        (algebraMap (𝓞 F) F (approx v N u₁) - algebraMap (𝓞 F) F (approx v N u₂)) := by ring
    rw [e]
    refine (Valuation.map_sub _ _ _).trans (max_le ((Valuation.map_sub _ _ _).trans
      (max_le hA hB)) hC)

/-- The primes over `𝔪`. -/
abbrev PS (𝔪 : Ideal (𝓞 F)) : Type := {v : HeightOneSpectrum (𝓞 F) // 𝔪 ≤ v.asIdeal}

/-- The precision used at `v`. -/
def Nv (v : HeightOneSpectrum (𝓞 F)) : ℕ := 2 * (6 * L3K.n6 v + 1)

/-- The joint invariant. -/
def Inv (𝔪 : Ideal (𝓞 F)) (x : F) : ∀ v : PS 𝔪, ZMod 2 × (𝓞 F ⧸ v.1.asIdeal ^ Nv v.1) :=
  fun v => invP v.1 (Nv v.1) x

lemma finite_PS {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) : Finite (PS 𝔪) := by
  have := Ideal.finite_factors (R := 𝓞 F) h𝔪
  have h' : {v : HeightOneSpectrum (𝓞 F) | 𝔪 ≤ v.asIdeal} = {v | v.asIdeal ∣ 𝔪} := by
    ext v; simp [Ideal.dvd_iff_le]
  exact (h' ▸ this).to_subtype

lemma finite_inv {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) :
    Finite (∀ v : PS 𝔪, ZMod 2 × (𝓞 F ⧸ v.1.asIdeal ^ Nv v.1)) := by
  haveI := finite_PS h𝔪
  haveI : ∀ v : PS 𝔪, Finite (𝓞 F ⧸ v.1.asIdeal ^ Nv v.1) := fun v =>
    Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ v.1.ne_bot)
  infer_instance

/-- **The class function.** -/
theorem exists_cls (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) :
    ∃ (k : ℕ) (cls₀ : F → Fin k), ∀ x₁ x₂ : F, x₁ ≠ 0 → x₂ ≠ 0 → cls₀ x₁ = cls₀ x₂ →
      ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal →
        ∃ y d : F, y ≠ 0 ∧ x₁ * x₂ = y ^ 2 * d ∧
          v.valuation F (d - 1) ≤ exp (-((2 * (6 * L3K.n6 v + 1) : ℕ) : ℤ)) := by
  haveI := finite_inv h𝔪
  refine ⟨_, fun x => Finite.equivFin _ (Inv 𝔪 x), fun x₁ x₂ h₁ h₂ h v hv => ?_⟩
  have hI : Inv 𝔪 x₁ = Inv 𝔪 x₂ := (Finite.equivFin _).injective h
  have := congrFun hI ⟨v, hv⟩
  exact exists_sq_mul_of_invP_eq v _ h₁ h₂ this

end L3F

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3K_Cond: `N 𝔣(ψ_a) ≤ N(D₆) · N(𝔟)`

`D₆ = ∏_{v ∣ 6} v^{1 + 6 n_v}` depends on `F` only; `𝔟` is any nonzero ideal contained in every
`v ∤ 6` at which `a` is not a unit. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin ArtinPrimitiveRoots.L3K.KB WithZero

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

section Gen

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

lemma finprod_count_eq {I : Ideal R} (hI : I ≠ ⊥) :
    ∏ᶠ v : HeightOneSpectrum R,
      v.asIdeal ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors = I :=
  Ideal.finprod_heightOneSpectrum_factorization hI

lemma one_le_count {I : Ideal R} (hI : I ≠ ⊥) (v : HeightOneSpectrum R) (hv : I ≤ v.asIdeal) :
    1 ≤ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
  rw [Nat.one_le_iff_ne_zero]
  exact (Associates.count_ne_zero_iff_dvd hI v.irreducible).2 (Ideal.dvd_iff_le.2 hv)

end Gen

variable {F : Type} [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ 6) (ι : F →+* ℂ)
  (a : Fˣ)

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3K_Val: valuations of a generator `u` of `𝔲 R` at exterior primes

For `u ∈ R = SInt 𝔪` with `u R = 𝔲 R` and an exterior prime `v`: `v(u) = e^{−e}` where
`𝔲 ≤ v^e`, `𝔲 ≰ v^{e+1}`. Hence `v(u) = 1` if `v ∤ 𝔲`, and `v(u)` is not an even sixth power of
`e^{±1}` when `v ∣ 𝔲` and `𝔲` is sixth-power-free. -/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots WithZero

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

lemma sInt_val_le_one' (s : SInt 𝔪) (w : HeightOneSpectrum (𝓞 F)) (hw : ¬ 𝔪 ≤ w.asIdeal) :
    w.valuation F (s : F) ≤ 1 :=
  s.2 w hw

lemma coe_algebraMap_sInt' (a : 𝓞 F) :
    ((algebraMap (𝓞 F) (SInt 𝔪) a : SInt 𝔪) : F) = algebraMap (𝓞 F) F a := rfl

lemma val_algebraMap_le (v : HeightOneSpectrum (𝓞 F)) {x : 𝓞 F} {e : ℕ} (hx : x ∈ v.asIdeal ^ e) :
    v.valuation F (algebraMap (𝓞 F) F x) ≤ exp (-(e : ℤ)) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (v.intValuation_le_pow_iff_mem x e).2 hx

lemma val_le_of_le (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) {𝔲 : Ideal (𝓞 F)}
    {u : SInt 𝔪} (hu : Ideal.span {u} = 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪))) {e : ℕ}
    (he : 𝔲 ≤ v.asIdeal ^ e) : v.valuation F (u : F) ≤ exp (-(e : ℤ)) := by
  have hmem : u ∈ 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hu]; exact Ideal.mem_span_singleton_self u
  clear hu
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    rw [coe_algebraMap_sInt']
    exact val_algebraMap_le v (he hy)
  | zero => simp
  | add x y _ _ hx hy =>
    have : ((x + y : SInt 𝔪) : F) = (x : F) + (y : F) := rfl
    rw [this]; exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  | smul r x _ hx =>
    have : ((r • x : SInt 𝔪) : F) = (r : F) * (x : F) := rfl
    rw [this, map_mul]
    calc v.valuation F (r : F) * v.valuation F (x : F) ≤ 1 * exp (-(e : ℤ)) :=
          mul_le_mul' (sInt_val_le_one' r v hv) hx
      _ = _ := one_mul _

lemma lt_val_of_not_le (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) {𝔲 : Ideal (𝓞 F)}
    {u : SInt 𝔪} (hu : Ideal.span {u} = 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪))) {n : ℕ}
    (hn : ¬ 𝔲 ≤ v.asIdeal ^ n) : exp (-(n : ℤ)) < v.valuation F (u : F) := by
  obtain ⟨x, hx𝔲, hxn⟩ := SetLike.not_le_iff_exists.1 hn
  have hx : algebraMap (𝓞 F) (SInt 𝔪) x ∈ Ideal.span {u} := by
    rw [hu]; exact Ideal.mem_map_of_mem _ hx𝔲
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hx
  have h1 : exp (-(n : ℤ)) < v.valuation F (algebraMap (𝓞 F) F x) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    by_contra h; push Not at h
    exact hxn ((v.intValuation_le_pow_iff_mem x n).1 h)
  have h2 : algebraMap (𝓞 F) F x = (r : F) * (u : F) := by
    rw [← coe_algebraMap_sInt', ← hr]; rfl
  rw [h2, map_mul] at h1
  calc exp (-(n : ℤ)) < v.valuation F (r : F) * v.valuation F (u : F) := h1
    _ ≤ 1 * v.valuation F (u : F) := mul_le_mul' (sInt_val_le_one' r v hv) le_rfl
    _ = _ := one_mul _

/-- `v(u) = e^{−e}` when `𝔲 ≤ v^e` and `𝔲 ≰ v^{e+1}`. -/
lemma val_eq_exp (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) {𝔲 : Ideal (𝓞 F)}
    {u : SInt 𝔪} (hu : Ideal.span {u} = 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪))) {e : ℕ}
    (he : 𝔲 ≤ v.asIdeal ^ e) (he1 : ¬ 𝔲 ≤ v.asIdeal ^ (e + 1)) :
    v.valuation F (u : F) = exp (-(e : ℤ)) := by
  have hle := val_le_of_le v hv hu he
  have hlt := lt_val_of_not_le v hv hu he1
  have hne : v.valuation F (u : F) ≠ 0 := ne_of_gt ((zero_lt_iff.2 (exp_ne_zero)).trans hlt)
  rw [← exp_log hne] at hle hlt ⊢
  rw [exp_le_exp] at hle
  rw [exp_lt_exp] at hlt
  congr 1
  push_cast at hlt
  omega

lemma val_eq_one (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) {𝔲 : Ideal (𝓞 F)}
    {u : SInt 𝔪} (hu : Ideal.span {u} = 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (h : ¬ 𝔲 ≤ v.asIdeal) : v.valuation F (u : F) = 1 := by
  have := val_eq_exp v hv hu (e := 0) (by simp) (by simpa using h)
  simpa using this

/-- At a prime dividing a sixth-power-free `𝔲`, `v(u)` is not `e^{6k}`. -/
lemma val_ne_exp_six (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) {𝔲 : Ideal (𝓞 F)}
    (h6 : IsSixthPowerFree 𝔲) {u : SInt 𝔪}
    (hu : Ideal.span {u} = 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪))) (h : 𝔲 ≤ v.asIdeal) :
    ∀ k : ℤ, v.valuation F (u : F) ≠ exp (6 * k) := by
  classical
  have hex : ∃ n, ¬ 𝔲 ≤ v.asIdeal ^ n := by
    refine ⟨6, fun hle => ?_⟩
    have := h6 v.asIdeal (Ideal.dvd_iff_le.2 hle)
    exact v.isPrime.ne_top (Ideal.isUnit_iff.1 this)
  set n₀ := Nat.find hex
  have hn₀ : ¬ 𝔲 ≤ v.asIdeal ^ n₀ := Nat.find_spec hex
  have hn₀6 : n₀ ≤ 6 := Nat.find_min' hex (fun hle => by
    have := h6 v.asIdeal (Ideal.dvd_iff_le.2 hle)
    exact v.isPrime.ne_top (Ideal.isUnit_iff.1 this))
  have hn₀2 : 2 ≤ n₀ := by
    by_contra hlt; push Not at hlt
    interval_cases hn : n₀
    · exact hn₀ (by simp)
    · exact hn₀ (by simpa using h)
  have he : 𝔲 ≤ v.asIdeal ^ (n₀ - 1) := by
    by_contra hc
    exact Nat.find_min hex (by omega : n₀ - 1 < n₀) hc
  have hval := val_eq_exp v hv hu he (by rwa [Nat.sub_add_cancel (by omega)])
  intro k hk
  rw [hval, exp_inj] at hk
  omega

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-!
# Transport of `AllowedGen` along a field isomorphism

Used to move from `F : Type u` to the universe-0 copy `CyclotomicField n ℚ`.
-/

namespace ArtinPrimitiveRoots

open NumberField IsDedekindDomain

namespace C0R

/-! ### Generic facts on ideals along a ring equivalence -/

section Ideals

variable {R S : Type*} [CommRing R] [CommRing S]

theorem mem_map_equiv (f : R ≃+* S) (I : Ideal R) (y : S) : y ∈ I.map f ↔ f.symm y ∈ I := by
  rw [Ideal.mem_map_of_equiv]
  exact ⟨fun ⟨x, hx, hxy⟩ => by rw [← hxy, f.symm_apply_apply]; exact hx,
    fun h => ⟨_, h, f.apply_symm_apply y⟩⟩

theorem map_equiv_le_iff (f : R ≃+* S) {I J : Ideal R} : I.map f ≤ J.map f ↔ I ≤ J := by
  constructor
  · intro h x hx
    have : f x ∈ J.map f := h ((mem_map_equiv f I _).2 (by simpa using hx))
    simpa using (mem_map_equiv f J _).1 this
  · intro h y hy
    exact (mem_map_equiv f J y).2 (h ((mem_map_equiv f I y).1 hy))

theorem map_equiv_symm_map (f : R ≃+* S) (I : Ideal R) : (I.map f).map f.symm = I := by
  ext x
  rw [mem_map_equiv, RingEquiv.symm_symm, mem_map_equiv, RingEquiv.symm_apply_apply]

theorem map_equiv_coe (f : R ≃+* S) (I : Ideal R) : I.map (f : R →+* S) = I.map f := rfl

end Ideals

/-! ### The equivalences -/

variable {F F' : Type*} [Field F] [NumberField F] [Field F'] [NumberField F']

omit [NumberField F] [NumberField F'] in
theorem mapRingEquiv_symm (e : F ≃+* F') :
    RingOfIntegers.mapRingEquiv e.symm = (RingOfIntegers.mapRingEquiv e).symm := by
  ext x; rfl

/-- `S`-integrality transports along `e`. -/
theorem mem_integer_map (e : F ≃+* F') (𝔪 : Ideal (𝓞 F)) (x : F)
    (hx : x ∈ (placesOf 𝔪).integer F) :
    e x ∈ (placesOf (𝔪.map (RingOfIntegers.mapRingEquiv e))).integer F' := by
  set eO := RingOfIntegers.mapRingEquiv e
  intro v' hv'
  let v : HeightOneSpectrum (𝓞 F) :=
    { asIdeal := v'.asIdeal.comap (eO : 𝓞 F →+* 𝓞 F')
      isPrime := Ideal.comap_isPrime _ _
      ne_bot := by
        intro h
        apply v'.ne_bot
        rw [← Ideal.map_comap_of_surjective (eO : 𝓞 F →+* 𝓞 F') eO.surjective v'.asIdeal, h,
          Ideal.map_bot] }
  have hv : v ∉ placesOf 𝔪 := by
    intro h
    apply hv'
    change 𝔪.map eO ≤ v'.asIdeal
    rw [← map_equiv_coe]
    exact Ideal.map_le_iff_le_comap.2 h
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v x (hx v hv)
  have hd : eO d ∉ v'.asIdeal := d.2
  have hnd' : e x * algebraMap (𝓞 F') F' (eO d) = algebraMap (𝓞 F') F' (eO n) := by
    have := congrArg e hnd
    rw [map_mul] at this
    exact this
  have h1 : v'.valuation F' (algebraMap (𝓞 F') F' (eO d)) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact hd
  have h2 : v'.valuation F' (algebraMap (𝓞 F') F' (eO n)) ≤ 1 := v'.valuation_le_one _
  rw [← hnd', map_mul, h1, mul_one] at h2
  exact h2

/-- The ring `R = 𝓞_S` transports along `e`. -/
def sIntEquiv (e : F ≃+* F') (𝔪 : Ideal (𝓞 F)) :
    SInt 𝔪 ≃+* SInt (𝔪.map (RingOfIntegers.mapRingEquiv e)) where
  toFun x := ⟨e x, mem_integer_map e 𝔪 x x.2⟩
  invFun y := ⟨e.symm y, by
    have := mem_integer_map e.symm (𝔪.map (RingOfIntegers.mapRingEquiv e)) y y.2
    rwa [mapRingEquiv_symm, map_equiv_symm_map] at this⟩
  left_inv x := Subtype.ext (e.symm_apply_apply _)
  right_inv y := Subtype.ext (e.apply_symm_apply _)
  map_mul' x y := Subtype.ext (map_mul e _ _)
  map_add' x y := Subtype.ext (map_add e _ _)

@[simp] theorem sIntEquiv_coe (e : F ≃+* F') (𝔪 : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ((sIntEquiv e 𝔪 x : SInt (𝔪.map (RingOfIntegers.mapRingEquiv e))) : F') = e x := rfl

@[simp] theorem sIntEquiv_symm_coe (e : F ≃+* F') (𝔪 : Ideal (𝓞 F))
    (y : SInt (𝔪.map (RingOfIntegers.mapRingEquiv e))) :
    (((sIntEquiv e 𝔪).symm y : SInt 𝔪) : F) = e.symm y := rfl

theorem map_map_sIntEquiv (e : F ≃+* F') (𝔪 : Ideal (𝓞 F)) (I : Ideal (𝓞 F)) :
    (I.map (algebraMap (𝓞 F) (SInt 𝔪))).map (sIntEquiv e 𝔪) =
      (I.map (RingOfIntegers.mapRingEquiv e)).map
        (algebraMap (𝓞 F') (SInt (𝔪.map (RingOfIntegers.mapRingEquiv e)))) := by
  show Ideal.map ((sIntEquiv e 𝔪 : SInt 𝔪 →+* SInt (𝔪.map (RingOfIntegers.mapRingEquiv e))))
      (I.map (algebraMap (𝓞 F) (SInt 𝔪))) =
    Ideal.map (algebraMap (𝓞 F') (SInt (𝔪.map (RingOfIntegers.mapRingEquiv e))))
      (I.map ((RingOfIntegers.mapRingEquiv e : 𝓞 F →+* 𝓞 F')))
  rw [Ideal.map_map, Ideal.map_map]
  congr 1

theorem absNorm_map_equiv (e : F ≃+* F') (I : Ideal (𝓞 F)) :
    Ideal.absNorm (I.map (RingOfIntegers.mapRingEquiv e)) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I _ (RingOfIntegers.mapRingEquiv e) rfl).toEquiv).symm

theorem isExterior_map (e : F ≃+* F') {𝔪 I : Ideal (𝓞 F)} (h : IsExterior 𝔪 I) :
    IsExterior (𝔪.map (RingOfIntegers.mapRingEquiv e)) (I.map (RingOfIntegers.mapRingEquiv e)) := by
  refine ⟨fun h0 => h.1 ?_, ?_⟩
  · exact (Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.mapRingEquiv e).injective).1 h0
  · rw [← Ideal.map_sup, h.2, Ideal.map_top]

/-! ### Uniqueness of the sixth root of unity modulo `P` -/

theorem eq_of_pow_six {R : Type*} [CommRing R] [IsDomain R] (Q : Ideal R) (h6 : (6 : R) ∉ Q)
    {a b : R} (ha : a ^ 6 = 1) (hb : b ^ 6 = 1) (hab : a - b ∈ Q) : a = b := by
  set η := b * a ^ 5 with hη
  have h1 : 1 - η ∈ Q := by
    have : 1 - η = a ^ 5 * (a - b) := by rw [hη]; linear_combination (-1 : R) * ha
    rw [this]; exact Q.mul_mem_left _ hab
  by_cases hη1 : η = 1
  · have : b = a := calc
        b = b * a ^ 6 := by rw [ha, mul_one]
        _ = (b * a ^ 5) * a := by ring
        _ = a := by rw [← hη, hη1, one_mul]
    exact this.symm
  · exfalso
    have hη6 : η ^ 6 = 1 := by
      rw [hη]
      calc (b * a ^ 5) ^ 6 = b ^ 6 * (a ^ 6) ^ 5 := by ring
        _ = 1 := by rw [ha, hb]; ring
    have hsum : 1 + η + η ^ 2 + η ^ 3 + η ^ 4 + η ^ 5 = 0 := by
      have : (η - 1) * (1 + η + η ^ 2 + η ^ 3 + η ^ 4 + η ^ 5) = 0 := by
        linear_combination hη6
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (sub_eq_zero.1 h) hη1
      · exact h
    apply h6
    have : (6 : R) = (1 - η) * (5 + 4 * η + 3 * η ^ 2 + 2 * η ^ 3 + η ^ 4) +
        (1 + η + η ^ 2 + η ^ 3 + η ^ 4 + η ^ 5) := by ring
    rw [this, hsum, add_zero]
    exact Q.mul_mem_right _ h1

/-! ### The residue symbol transports -/

theorem sexticResidueSymbol_transport (e : F ≃+* F') (ι : F →+* ℂ) (𝔪 P : Ideal (𝓞 F))
    (h6 : P ⊔ Ideal.span {6} = ⊤) (x : SInt 𝔪) :
    sexticResidueSymbol (ι.comp (e.symm : F' →+* F)) (𝔪.map (RingOfIntegers.mapRingEquiv e))
        (P.map (RingOfIntegers.mapRingEquiv e)) (sIntEquiv e 𝔪 x) =
      sexticResidueSymbol ι 𝔪 P x := by
  classical
  set eO := RingOfIntegers.mapRingEquiv e
  set eS := sIntEquiv e 𝔪
  set f := algebraMap (𝓞 F) (SInt 𝔪)
  set f' := algebraMap (𝓞 F') (SInt (𝔪.map eO))
  set Q := P.map f
  have hQ' : (P.map eO).map f' = Q.map eS := (map_map_sIntEquiv e 𝔪 P).symm
  have hmem : ∀ y : SInt 𝔪, eS y ∈ (P.map eO).map f' ↔ y ∈ Q := fun y => by
    rw [hQ', mem_map_equiv, RingEquiv.symm_apply_apply]
  have hN : Ideal.absNorm (P.map eO) = Ideal.absNorm P := absNorm_map_equiv e P
  unfold sexticResidueSymbol
  simp only [Ideal.Quotient.eq_zero_iff_mem]
  by_cases hx : x ∈ Q
  · rw [if_pos hx, if_pos ((hmem x).2 hx)]
  rw [if_neg hx, if_neg (fun h => hx ((hmem x).1 h)), hN]
  set k := (Ideal.absNorm P - 1) / 6
  -- `6 ∉ Q`
  have h6Q : (6 : SInt 𝔪) ∉ Q := by
    intro h6m
    apply hx
    have : Q = ⊤ := by
      rw [eq_top_iff, ← Ideal.map_top f, ← h6, Ideal.map_sup]
      refine sup_le le_rfl ?_
      rw [Ideal.map_span, Set.image_singleton, map_ofNat, Ideal.span_le,
        Set.singleton_subset_iff]
      exact h6m
    rw [this]; trivial
  have hC : ∀ ζ : 𝓞 F, (ζ ^ 6 = 1 ∧ Ideal.Quotient.mk Q (f ζ) = Ideal.Quotient.mk Q x ^ k) ↔
      ((eO ζ) ^ 6 = 1 ∧ Ideal.Quotient.mk ((P.map eO).map f') (f' (eO ζ)) =
        Ideal.Quotient.mk ((P.map eO).map f') (eS x) ^ k) := by
    intro ζ
    apply and_congr
    · rw [← map_pow, ← map_one eO]
      exact eO.injective.eq_iff.symm
    · rw [← map_pow, ← map_pow, Ideal.Quotient.eq, Ideal.Quotient.eq, ← map_pow eS,
        show f' (eO ζ) = eS (f ζ) from rfl, ← map_sub, hmem]
  have huniq : ∀ ζ₁ ζ₂ : 𝓞 F, (ζ₁ ^ 6 = 1 ∧ Ideal.Quotient.mk Q (f ζ₁) = Ideal.Quotient.mk Q x ^ k) →
      (ζ₂ ^ 6 = 1 ∧ Ideal.Quotient.mk Q (f ζ₂) = Ideal.Quotient.mk Q x ^ k) → ζ₁ = ζ₂ := by
    intro ζ₁ ζ₂ h1 h2
    have hsub : f ζ₁ - f ζ₂ ∈ Q := by
      rw [← Ideal.Quotient.eq, h1.2, h2.2]
    have := eq_of_pow_six Q h6Q (by rw [← map_pow, h1.1, map_one])
      (by rw [← map_pow, h2.1, map_one]) hsub
    have h' : ((f ζ₁ : SInt 𝔪) : F) = ((f ζ₂ : SInt 𝔪) : F) := by rw [this]
    exact RingOfIntegers.ext h'
  by_cases h : ∃ ζ : 𝓞 F, ζ ^ 6 = 1 ∧ Ideal.Quotient.mk Q (f ζ) = Ideal.Quotient.mk Q x ^ k
  · have h' : ∃ ζ' : 𝓞 F', ζ' ^ 6 = 1 ∧ Ideal.Quotient.mk ((P.map eO).map f') (f' ζ') =
        Ideal.Quotient.mk ((P.map eO).map f') (eS x) ^ k :=
      ⟨eO h.choose, (hC _).1 h.choose_spec⟩
    rw [dif_pos h, dif_pos h']
    have hspec : eO (eO.symm h'.choose) = h'.choose := eO.apply_symm_apply _
    have hC' := (hC (eO.symm h'.choose)).2 (by rw [hspec]; exact h'.choose_spec)
    have := huniq _ _ hC' h.choose_spec
    rw [← this]
    simp [eO]
  · have h' : ¬ ∃ ζ' : 𝓞 F', ζ' ^ 6 = 1 ∧ Ideal.Quotient.mk ((P.map eO).map f') (f' ζ') =
        Ideal.Quotient.mk ((P.map eO).map f') (eS x) ^ k := by
      rintro ⟨ζ', hζ'⟩
      apply h
      refine ⟨eO.symm ζ', (hC _).2 ?_⟩
      rw [eO.apply_symm_apply]; exact hζ'
    rw [dif_neg h, dif_neg h']

/-! ### `AllowedGen` transports -/

/-- `SmallPrimesDvd` transports. -/
theorem smallPrimesDvd_map (e : F ≃+* F') {N₀ : ℕ} {𝔪 : Ideal (𝓞 F)} (h : SmallPrimesDvd N₀ 𝔪) :
    SmallPrimesDvd N₀ (𝔪.map (RingOfIntegers.mapRingEquiv e)) := by
  set eO := RingOfIntegers.mapRingEquiv e
  intro P' hP' hP'0 hN
  set P := P'.map eO.symm
  have hPP : P.map eO = P' := by
    have := map_equiv_symm_map eO.symm P'
    rwa [RingEquiv.symm_symm] at this
  have hP : P.IsPrime := Ideal.map_isPrime_of_equiv eO.symm
  have hP0 : P ≠ ⊥ := fun h0 => hP'0 (by rw [← hPP, h0, Ideal.map_bot])
  have hNP : Ideal.absNorm P ≤ N₀ := by rw [← absNorm_map_equiv e P, hPP]; exact hN
  rw [← hPP]
  exact (map_equiv_le_iff eO).2 (h P hP hP0 hNP)

end C0R

end ArtinPrimitiveRoots

end
end

section
section
/-! C0Y: valuations of prime generators in `SInt 𝔪` and the sextic residue symbol. -/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace C0Y

variable {F : Type} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

theorem sInt_val_le_one (s : SInt 𝔪) (w : HeightOneSpectrum (𝓞 F)) (hw : ¬ 𝔪 ≤ w.asIdeal) :
    w.valuation F (s : F) ≤ 1 :=
  s.2 w hw

theorem coe_algebraMap_sInt (a : 𝓞 F) :
    ((algebraMap (𝓞 F) (SInt 𝔪) a : SInt 𝔪) : F) = algebraMap (𝓞 F) F a := rfl

/-- Elements of `P · SInt` have `v_P < 1`. -/
theorem val_lt_one_of_mem_map (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal)
    {z : SInt 𝔪} (hz : z ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    v.valuation F (z : F) < 1 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [coe_algebraMap_sInt]
    exact (v.valuation_lt_one_iff_mem (K := F) a).mpr ha
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Subalgebra.coe_add]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hy)
  | smul a x _ hx =>
    simp only [smul_eq_mul, Subalgebra.coe_mul, map_mul]
    calc v.valuation F (a : F) * v.valuation F (x : F) ≤ 1 * v.valuation F (x : F) :=
          mul_le_mul_left (sInt_val_le_one a v hv) _
      _ < 1 := by rw [one_mul]; exact hx

/-- Valuations of a generator of `P · SInt`. -/
theorem val_generator (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) (p : SInt 𝔪)
    (hp : Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    v.valuation F (p : F) = WithZero.exp (-1 : ℤ) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ w.asIdeal → w ≠ v → w.valuation F (p : F) = 1 := by
  have hpmem : p ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hp]; exact Ideal.subset_span rfl
  have hlt := val_lt_one_of_mem_map v hv hpmem
  -- every `a ∈ P` is a multiple of `p` in `SInt`
  have hdiv : ∀ a ∈ v.asIdeal, ∃ s : SInt 𝔪, algebraMap (𝓞 F) F a = (p : F) * (s : F) := by
    intro a ha
    have : algebraMap (𝓞 F) (SInt 𝔪) a ∈ Ideal.span {p} := by
      rw [hp]; exact Ideal.mem_map_of_mem _ ha
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp this
    refine ⟨s, ?_⟩
    rw [← coe_algebraMap_sInt (𝔪 := 𝔪), ← hs, Subalgebra.coe_mul, mul_comm]
  refine ⟨?_, fun w hw hwv => ?_⟩
  · obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer' F
    have hπmem : π ∈ v.asIdeal := by
      rw [← v.valuation_lt_one_iff_mem (K := F), hπ]; exact by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    obtain ⟨s, hs⟩ := hdiv π hπmem
    have h1 : v.valuation F (p : F) * v.valuation F (s : F) = WithZero.exp (-1 : ℤ) := by
      rw [← map_mul, ← hs, hπ]
    have hs1 := sInt_val_le_one s v hv
    have hp0 : v.valuation F (p : F) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at h1; exact WithZero.exp_ne_zero h1.symm
    have hge : WithZero.exp (-1 : ℤ) ≤ v.valuation F (p : F) := by
      rw [← h1]; exact mul_le_of_le_one_right' hs1
    have hle : v.valuation F (p : F) ≤ WithZero.exp (-1 : ℤ) := by
      obtain ⟨k, hk⟩ := WithZero.ne_zero_iff_exists.mp hp0
      rw [← hk] at hlt ⊢
      rw [show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp 0 from rfl] at hlt
      have : (k : WithZero (Multiplicative ℤ)) = WithZero.exp (Multiplicative.toAdd k) := rfl
      rw [this, WithZero.exp_lt_exp] at hlt
      rw [this, WithZero.exp_le_exp]
      omega
    exact le_antisymm hle hge
  · -- `P ⊄ w`
    have hnle : ¬ v.asIdeal ≤ w.asIdeal := by
      intro hle
      have := v.isMaximal.eq_of_le w.isPrime.ne_top hle
      exact hwv (HeightOneSpectrum.ext this.symm)
    obtain ⟨a, ha, haw⟩ := Set.not_subset.mp hnle
    obtain ⟨s, hs⟩ := hdiv a ha
    have h1 : w.valuation F (p : F) * w.valuation F (s : F) = 1 := by
      rw [← map_mul, ← hs]; exact (w.valuation_eq_one_iff_notMem (K := F)).mpr haw
    have hp1 := sInt_val_le_one p w hw
    have hs1 := sInt_val_le_one s w hw
    by_contra hne
    have hlt : w.valuation F (p : F) < 1 := lt_of_le_of_ne hp1 hne
    have : w.valuation F (p : F) * w.valuation F (s : F) < 1 :=
      lt_of_lt_of_le (mul_lt_one_of_lt_of_le hlt hs1) le_rfl
    rw [h1] at this
    exact lt_irrefl _ this

/-- Elements of `SInt` with `v_P < 1` lie in `P · SInt` (given a generator). -/
theorem mem_map_of_val_lt_one (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) (p : SInt 𝔪)
    (hp : Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) (z : SInt 𝔪)
    (hz : v.valuation F (z : F) < 1) : z ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  obtain ⟨hpv, hpw⟩ := val_generator v hv p hp
  have hp0 : (p : F) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hpv; exact WithZero.exp_ne_zero hpv.symm
  have hq : (z : F) / (p : F) ∈ (placesOf 𝔪).integer F := by
    intro w hw
    by_cases hwv : w = v
    · subst hwv
      rw [map_div₀, hpv]
      by_cases hz0 : w.valuation F (z : F) = 0
      · rw [hz0, zero_div]; exact zero_le
      obtain ⟨k, hk⟩ := WithZero.ne_zero_iff_exists.mp hz0
      rw [← hk] at hz ⊢
      have e : (k : WithZero (Multiplicative ℤ)) = WithZero.exp (Multiplicative.toAdd k) := rfl
      rw [e, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hz
      rw [e, ← WithZero.exp_sub, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    · rw [map_div₀, hpw w hw hwv, div_one]
      exact sInt_val_le_one z w hw
  have : z = p * ⟨(z : F) / (p : F), hq⟩ := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul]
    field_simp
  rw [← hp, this]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

/-- The sextic residue symbol at an exterior prime with generator: `6 ∣ N P − 1`, and
`χ_P(y) = ι ξ` for the sixth root of unity `ξ ≡ y^{(N P − 1)/6} (mod P)`. -/
theorem sextic_spec (ι : F →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal)
    (p : SInt 𝔪) (hp : Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (h6 : (6 : 𝓞 F) ∉ v.asIdeal) (y : SInt 𝔪)
    (hy : v.valuation F (y : F) = 1) :
    6 ∣ Ideal.absNorm v.asIdeal - 1 ∧ ∃ ξ : 𝓞 F, ξ ^ 6 = 1 ∧
      v.valuation F ((y : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6) - algebraMap (𝓞 F) F ξ) < 1 ∧
      sexticResidueSymbol ι 𝔪 v.asIdeal y = ι (algebraMap (𝓞 F) F ξ) := by
  classical
  set P := v.asIdeal with hPdef
  letI : Field (𝓞 F ⧸ P) := Ideal.Quotient.field P
  haveI : Finite (𝓞 F ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P v.ne_bot
  letI : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 F ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hinj : ∀ a b : 𝓞 F, a ^ 6 = 1 → b ^ 6 = 1 →
      Ideal.Quotient.mk P a = Ideal.Quotient.mk P b → a = b := fun a b ha hb h =>
    C0R.eq_of_pow_six P h6 ha hb (Ideal.Quotient.eq.mp h)
  have hη : IsPrimitiveRoot (Ideal.Quotient.mk P z6) 6 := by
    refine ⟨by rw [← map_pow, hz6.pow_eq_one, map_one], fun l hl => ?_⟩
    have : z6 ^ l = 1 := hinj _ _ (by rw [← pow_mul, mul_comm, pow_mul, hz6.pow_eq_one, one_pow])
      (one_pow 6) (by rw [map_pow, hl, map_one])
    exact hz6.dvd_of_pow_eq_one l this
  have h6N : 6 ∣ Ideal.absNorm P - 1 := by
    have := FiniteField.pow_card_sub_one_eq_one (Ideal.Quotient.mk P z6) (hη.ne_zero (by norm_num))
    rw [hcard] at this
    exact hη.dvd_of_pow_eq_one _ this
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v (y : F) hy.le
  have hd : (d : 𝓞 F) ∉ P := d.2
  have hdv : v.valuation F (algebraMap (𝓞 F) F d) = 1 :=
    (v.valuation_eq_one_iff_notMem (K := F)).mpr hd
  have hdF : algebraMap (𝓞 F) F d ≠ 0 := by
    intro h0; rw [h0, map_zero] at hdv; exact zero_ne_one hdv
  have hn : (n : 𝓞 F) ∉ P := by
    rw [← v.valuation_eq_one_iff_notMem (K := F), ← hnd, map_mul, hy, hdv, one_mul]
  set k := (Ideal.absNorm P - 1) / 6 with hk
  set u : 𝓞 F ⧸ P := Ideal.Quotient.mk P n * (Ideal.Quotient.mk P d)⁻¹ with hu
  have hmd : Ideal.Quotient.mk P (d : 𝓞 F) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hmn : Ideal.Quotient.mk P n ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hu0 : u ≠ 0 := mul_ne_zero hmn (inv_ne_zero hmd)
  have hu6 : (u ^ k) ^ 6 = 1 := by
    rw [← pow_mul, hk, Nat.div_mul_cancel h6N, ← hcard]
    exact FiniteField.pow_card_sub_one_eq_one u hu0
  obtain ⟨i, -, hi⟩ := hη.eq_pow_of_pow_eq_one hu6
  set ξ := z6 ^ i with hξ
  have hξ6 : ξ ^ 6 = 1 := by rw [hξ, ← pow_mul, mul_comm, pow_mul, hz6.pow_eq_one, one_pow]
  have hcong : n ^ k - ξ * (d : 𝓞 F) ^ k ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_pow, map_pow, map_pow, hi,
      hu, mul_pow, inv_pow, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hmd), mul_one, sub_self]
  have hval : v.valuation F ((y : F) ^ k - algebraMap (𝓞 F) F ξ) < 1 := by
    have hyd : (y : F) = algebraMap (𝓞 F) F n / algebraMap (𝓞 F) F d := by
      rw [← hnd, mul_div_cancel_right₀ _ hdF]
    have : (y : F) ^ k - algebraMap (𝓞 F) F ξ =
        algebraMap (𝓞 F) F (n ^ k - ξ * (d : 𝓞 F) ^ k) / (algebraMap (𝓞 F) F d) ^ k := by
      rw [hyd, eq_div_iff (pow_ne_zero _ hdF)]
      simp only [map_sub, map_mul, map_pow]
      rw [sub_mul, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hdF)]
    rw [this, map_div₀, map_pow, hdv, one_pow, div_one]
    exact (v.valuation_lt_one_iff_mem (K := F) _).mpr hcong
  refine ⟨h6N, ξ, hξ6, hval, ?_⟩
  set f := algebraMap (𝓞 F) (SInt 𝔪)
  set Q := P.map f
  have hyQ : y ∉ Q := fun h => by
    have := val_lt_one_of_mem_map v hv h; rw [hy] at this; exact lt_irrefl _ this
  have h6Q : (6 : SInt 𝔪) ∉ Q := by
    intro h
    have := val_lt_one_of_mem_map v hv h
    have e : ((6 : SInt 𝔪) : F) = algebraMap (𝓞 F) F 6 := by rw [map_ofNat]; rfl
    rw [e, (v.valuation_eq_one_iff_notMem (K := F)).mpr h6] at this
    exact lt_irrefl _ this
  have hex : f ξ - y ^ k ∈ Q := by
    apply mem_map_of_val_lt_one v hv p hp
    have e : ((f ξ - y ^ k : SInt 𝔪) : F) = -((y : F) ^ k - algebraMap (𝓞 F) F ξ) := by
      simp [f, coe_algebraMap_sInt]
    rw [e, Valuation.map_neg]; exact hval
  unfold sexticResidueSymbol
  rw [if_neg (by rwa [Ideal.Quotient.eq_zero_iff_mem])]
  have hE : ∃ ζ : 𝓞 F, ζ ^ 6 = 1 ∧ Ideal.Quotient.mk Q (f ζ) = Ideal.Quotient.mk Q y ^ k :=
    ⟨ξ, hξ6, by rw [← map_pow, Ideal.Quotient.eq]; exact hex⟩
  rw [dif_pos hE]
  have hch := hE.choose_spec
  have hsub : f hE.choose - f ξ ∈ Q := by
    rw [← Ideal.Quotient.eq, hch.2, ← map_pow, Ideal.Quotient.eq]
    have : y ^ k - f ξ = -(f ξ - y ^ k) := by ring
    rw [this]; exact Q.neg_mem hex
  have heq := C0R.eq_of_pow_six Q h6Q (by rw [← map_pow, hch.1, map_one])
    (by rw [← map_pow, hξ6, map_one]) hsub
  have : hE.choose = ξ := by
    have h' := congrArg (fun z : SInt 𝔪 => (z : F)) heq
    simp only [f, coe_algebraMap_sInt] at h'
    exact FaithfulSMul.algebraMap_injective (𝓞 F) F h'
  rw [this]

end C0Y

end
end
end

section
section
/-! # L3K_Bridge: `kummerL` is `L(s, ψ_u)` up to finitely many Euler factors at `S`

Setting (universe 0): `ζ` a primitive sixth root of unity in `F`, every prime containing `6`
contains `𝔪`, every exterior prime is principal in `R`, `u R = 𝔲 R` with `𝔲` exterior and
sixth-power-free, `u` not a sixth power. With `ψ = ψ_u`:
* exterior `v`: `localValue ψ v = χ_v(u)` (`v ∤ 𝔲`, unramified) and `ψ` is ramified at `v ∣ 𝔲`;
* `kummerL u = L(ψ) · ∏_{P ⊇ 𝔣𝔪, P + 𝔣 = 1} (1 − ψ(P) N P^{-s})` on `Re s > 1`. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin ArtinPrimitiveRoots.L3K.KB UniqueFactorizationMonoid

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

variable {F : Type} [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ 6) (ι : F →+* ℂ)
  {𝔪 : Ideal (𝓞 F)}

/-- The data of the bridge. -/
structure BridgeHyp (𝔪 : Ideal (𝓞 F)) (u : SInt 𝔪) (𝔲 : Ideal (𝓞 F)) : Prop where
  ne_bot : 𝔪 ≠ ⊥
  six : ∀ v : HeightOneSpectrum (𝓞 F), (6 : 𝓞 F) ∈ v.asIdeal → 𝔪 ≤ v.asIdeal
  prin : ∀ v : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ v.asIdeal →
    ∃ p : SInt 𝔪, Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))
  gen : Ideal.span {u} = 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪))
  sfree : IsSixthPowerFree 𝔲
  nonsix : ∀ b : F, b ^ 6 ≠ (u : F)

variable {u : SInt 𝔪} {𝔲 : Ideal (𝓞 F)}

lemma BridgeHyp.ne_zero (h : BridgeHyp 𝔪 u 𝔲) : (u : F) ≠ 0 := fun h0 =>
  h.nonsix 0 (by rw [h0]; ring)

/-- `u` as a unit of `F`. -/
def uUnit (h : BridgeHyp 𝔪 u 𝔲) : Fˣ := Units.mk0 (u : F) h.ne_zero

lemma uUnit_val (h : BridgeHyp 𝔪 u 𝔲) : ((uUnit h : Fˣ) : F) = (u : F) := rfl

/-- `ζ` as an algebraic integer. -/
def z6 : 𝓞 F := ⟨ζ, IsIntegral.of_pow (by norm_num : 0 < 6) (by rw [hζ.pow_eq_one]; exact isIntegral_one)⟩

lemma z6_prim : IsPrimitiveRoot (z6 hζ) 6 :=
  (IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 F) F) (by
    show IsPrimitiveRoot ζ 6; exact hζ) (FaithfulSMul.algebraMap_injective _ _))

lemma six_not_mem (h : BridgeHyp 𝔪 u 𝔲) {v : HeightOneSpectrum (𝓞 F)} (hv : ¬ 𝔪 ≤ v.asIdeal) :
    (6 : 𝓞 F) ∉ v.asIdeal := fun h6 => hv (h.six v h6)

/-- **Exterior primes away from `𝔲`.** -/
theorem localValue_eq_sextic (h : BridgeHyp 𝔪 u 𝔲) {v : HeightOneSpectrum (𝓞 F)}
    (hv : ¬ 𝔪 ≤ v.asIdeal) (hv𝔲 : ¬ 𝔲 ≤ v.asIdeal) :
    ArtinL.Abelian.IsUnramifiedAt (psi F hζ ι (uUnit h)) v ∧
      ArtinL.Abelian.localValue (psi F hζ ι (uUnit h)) v = sexticResidueSymbol ι 𝔪 v.asIdeal u := by
  have hval : v.valuation F ((uUnit h : Fˣ) : F) = 1 := val_eq_one v hv h.gen hv𝔲
  have h6 := six_not_mem h hv
  have h6' : ((6 : ℕ) : 𝓞 F) ∉ v.asIdeal := by exact_mod_cast h6
  have hun := isUnramifiedAt_psi hζ ι (uUnit h) v h6' hval
  obtain ⟨p, hp⟩ := h.prin v hv
  obtain ⟨-, ξ, hξ6, hcong, hsx⟩ := C0Y.sextic_spec ι v hv p hp (z6_prim hζ) h6 u hval
  refine ⟨hun, ?_⟩
  rw [ArtinL.Abelian.localValue, if_pos hun, hsx,
    psi_artinFrob hζ ι (uUnit h) v h6' hval (algebraMap (𝓞 F) F ξ) (by rw [← map_pow, hξ6, map_one])
      hcong]

/-- **Primes dividing `𝔲` are ramified**, and there `χ_v(u) = 0`. -/
theorem ramified_of_le (h : BridgeHyp 𝔪 u 𝔲) {v : HeightOneSpectrum (𝓞 F)}
    (hv : ¬ 𝔪 ≤ v.asIdeal) (hv𝔲 : 𝔲 ≤ v.asIdeal) :
    ¬ ArtinL.Abelian.IsUnramifiedAt (psi F hζ ι (uUnit h)) v ∧
      sexticResidueSymbol ι 𝔪 v.asIdeal u = 0 := by
  refine ⟨not_isUnramifiedAt_psi hζ ι (uUnit h) v (val_ne_exp_six v hv h.sfree h.gen hv𝔲), ?_⟩
  obtain ⟨p, hp⟩ := h.prin v hv
  have hlt : v.valuation F (u : F) < 1 := by
    have := val_le_of_le v hv h.gen (e := 1) (by simpa using hv𝔲)
    refine this.trans_lt ?_
    rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by norm_num)
  have hmem := C0Y.mem_map_of_val_lt_one v hv p hp u hlt
  unfold sexticResidueSymbol
  rw [if_pos (Ideal.Quotient.eq_zero_iff_mem.2 hmem)]

lemma residueSymbol_mul' (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 (I * J) x = residueSymbol ι 𝔪 I x * residueSymbol ι 𝔪 J x := by
  unfold residueSymbol
  rw [normalizedFactors_mul hI hJ, Multiset.map_add, Multiset.prod_add]

lemma residueSymbol_prime' {P : Ideal (𝓞 F)} (hP : Irreducible P) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 P x = sexticResidueSymbol ι 𝔪 P x := by
  unfold residueSymbol
  rw [normalizedFactors_irreducible hP, normalize_eq]; simp

lemma residueSymbol_top' (x : SInt 𝔪) : residueSymbol ι 𝔪 ⊤ x = 1 := by
  unfold residueSymbol
  rw [← Ideal.one_eq_top, normalizedFactors_one]; simp

open Classical in
/-- `g(I) = χ_I(u)` on exterior `I`, `0` elsewhere. -/
def gK (𝔪 : Ideal (𝓞 F)) (u : SInt 𝔪) (I : Ideal (𝓞 F)) : ℂ :=
  if IsExterior 𝔪 I then residueSymbol ι 𝔪 I u else 0

lemma isExterior_mul_iff {I J : Ideal (𝓞 F)} :
    IsExterior 𝔪 (I * J) ↔ IsExterior 𝔪 I ∧ IsExterior 𝔪 J := by
  unfold IsExterior
  have hb : I * J ≠ ⊥ ↔ I ≠ ⊥ ∧ J ≠ ⊥ := by
    simp only [ne_eq, ← Ideal.zero_eq_bot, mul_eq_zero, not_or]
  rw [hb, C3A.sup_mul_eq_top_iff]; tauto

lemma gK_mul (I J : Ideal (𝓞 F)) : gK ι 𝔪 u (I * J) = gK ι 𝔪 u I * gK ι 𝔪 u J := by
  classical
  unfold gK
  by_cases hI : IsExterior 𝔪 I <;> by_cases hJ : IsExterior 𝔪 J
  · rw [if_pos (isExterior_mul_iff.2 ⟨hI, hJ⟩), if_pos hI, if_pos hJ,
      residueSymbol_mul' ι I J hI.1 hJ.1]
  · rw [if_neg (fun h => hJ (isExterior_mul_iff.1 h).2), if_neg hJ, mul_zero]
  · rw [if_neg (fun h => hI (isExterior_mul_iff.1 h).1), if_neg hI, zero_mul]
  · rw [if_neg (fun h => hI (isExterior_mul_iff.1 h).1), if_neg hI, zero_mul]

lemma sup_mul_top {P I J : Ideal (𝓞 F)} : P ⊔ I * J = ⊤ ↔ P ⊔ I = ⊤ ∧ P ⊔ J = ⊤ := by
  rw [sup_comm, C3A.sup_mul_eq_top_iff, sup_comm I, sup_comm J]

variable (hK : ∀ w : InfinitePlace F, w.IsComplex)

/-- The Hecke character `χ'` of modulus `𝔣 𝔪` given by 019ae22c from `psiH`. -/
lemma exists_chi' (h : BridgeHyp 𝔪 u 𝔲) :
    ∃ χ' : HeckeChar F (ArtinL.Abelian.conductor (psi F hζ ι (uUnit h)) * 𝔪),
      (∀ I, χ'.toFun I = gK ι 𝔪 u I) ∧
      ∀ s : ℂ, 1 < s.re → (psiH (psi F hζ ι (uUnit h)) hK).LSeries s = χ'.LSeries s *
        ∏ᶠ (P : Ideal (𝓞 F)) (_ : P.IsPrime ∧ P ≠ ⊥ ∧
            ArtinL.Abelian.conductor (psi F hζ ι (uUnit h)) * 𝔪 ≤ P ∧
            P ⊔ ArtinL.Abelian.conductor (psi F hζ ι (uUnit h)) = ⊤),
          (1 - (psiH (psi F hζ ι (uUnit h)) hK).toFun P * (Ideal.absNorm P : ℂ) ^ (-s))⁻¹ := by
  classical
  set ψ := psi F hζ ι (uUnit h)
  set 𝔣 := ArtinL.Abelian.conductor ψ
  obtain ⟨-, -, -, χ', hagree, hL⟩ := heckeLSeries_euler_package_of_le F 𝔣 (𝔣 * 𝔪)
    (mul_ne_zero (ArtinL.Abelian.conductor_ne_bot ψ) h.ne_bot) Ideal.mul_le_left (psiH ψ hK)
  refine ⟨χ', ?_, hL⟩
  have hext : ∀ v : HeightOneSpectrum (𝓞 F), IsExterior 𝔪 v.asIdeal ↔ ¬ 𝔪 ≤ v.asIdeal := by
    intro v
    rw [IsExterior, sup_eq_top_iff_not_dvd, Ideal.dvd_iff_le]
    exact ⟨fun h => h.2, fun h => ⟨v.ne_bot, h⟩⟩
  have hprime : ∀ v : HeightOneSpectrum (𝓞 F), χ'.toFun v.asIdeal = gK ι 𝔪 u v.asIdeal := by
    intro v
    have hirr : Irreducible v.asIdeal := v.irreducible
    by_cases hA : v.asIdeal ⊔ 𝔣 * 𝔪 = ⊤
    · rw [hagree _ hA, psiH_prime]
      obtain ⟨h𝔣, hm⟩ := sup_mul_top.1 hA
      have hvm : ¬ 𝔪 ≤ v.asIdeal := (hext v).1 ⟨v.ne_bot, hm⟩
      have hun : ArtinL.Abelian.IsUnramifiedAt ψ v := by
        by_contra hc
        exact (sup_eq_top_iff_not_dvd v 𝔣).1 h𝔣
          ((ArtinL.Abelian.dvd_conductor_iff_not_isUnramifiedAt F _ ψ v).2 hc)
      have hv𝔲 : ¬ 𝔲 ≤ v.asIdeal := fun hle => (ramified_of_le hζ ι h hvm hle).1 hun
      rw [(localValue_eq_sextic hζ ι h hvm hv𝔲).2, gK, if_pos ((hext v).2 hvm),
        residueSymbol_prime' ι hirr]
    · rw [(χ'.eq_zero_iff' _).2 (Or.inr hA), gK]
      split_ifs with he
      · have hvm : ¬ 𝔪 ≤ v.asIdeal := (hext v).1 he
        have h𝔣 : ¬ v.asIdeal ⊔ 𝔣 = ⊤ := fun h𝔣 => hA (sup_mul_top.2 ⟨h𝔣, he.2⟩)
        have hram : ¬ ArtinL.Abelian.IsUnramifiedAt ψ v :=
          (ArtinL.Abelian.dvd_conductor_iff_not_isUnramifiedAt F _ ψ v).1
            (by by_contra hc; exact h𝔣 ((sup_eq_top_iff_not_dvd v 𝔣).2 hc))
        have hv𝔲 : 𝔲 ≤ v.asIdeal := by
          by_contra hc; exact hram (localValue_eq_sextic hζ ι h hvm hc).1
        rw [residueSymbol_prime' ι hirr, (ramified_of_le hζ ι h hvm hv𝔲).2]
      · rfl
  intro I
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    rw [Ideal.zero_eq_bot, T12B.toFun_bot, gK, if_neg (fun h => h.1 rfl)]
  | h₂ x hx =>
    rw [Ideal.isUnit_iff.1 hx, T12B.toFun_top, gK, if_pos ⟨top_ne_bot, top_sup_eq _⟩,
      residueSymbol_top']
  | h₃ a p ha hp ih =>
    rw [χ'.map_mul', gK_mul, ih]
    congr 1
    exact hprime (HeightOneSpectrum.ofPrime hp)

lemma kummerL_eq_tsum (s : ℂ) :
    kummerL ι 𝔪 u s = ∑' I : Ideal (𝓞 F), gK ι 𝔪 u I * (Ideal.absNorm I : ℂ) ^ (-s) := by
  classical
  unfold kummerL
  rw [← tsum_subtype_eq_of_support_subset (s := {I | IsExterior 𝔪 I})
    (f := fun I : Ideal (𝓞 F) => gK ι 𝔪 u I * (Ideal.absNorm I : ℂ) ^ (-s))]
  · refine tsum_congr fun I => ?_
    simp only [gK, if_pos I.2]
  · intro I hI
    by_contra hne
    apply hI
    simp only [gK]
    rw [if_neg (show ¬ IsExterior 𝔪 I from hne), zero_mul]

/-- The Euler factors at `P ⊇ 𝔣𝔪` with `P + 𝔣 = 1`. -/
def Efac (h : BridgeHyp 𝔪 u 𝔲) (s : ℂ) : ℂ :=
  ∏ᶠ (P : Ideal (𝓞 F)) (_ : P.IsPrime ∧ P ≠ ⊥ ∧
      ArtinL.Abelian.conductor (psi F hζ ι (uUnit h)) * 𝔪 ≤ P ∧
      P ⊔ ArtinL.Abelian.conductor (psi F hζ ι (uUnit h)) = ⊤),
    (1 - (psiH (psi F hζ ι (uUnit h)) hK).toFun P * (Ideal.absNorm P : ℂ) ^ (-s))

/-- **`kummerL = L(ψ) · E`** on `Re s > 1`. -/
theorem kummerL_eq (h : BridgeHyp 𝔪 u 𝔲) {s : ℂ} (hs : 1 < s.re) :
    kummerL ι 𝔪 u s =
      ArtinL.Abelian.LSeries (psi F hζ ι (uUnit h)) s * Efac hζ ι hK h s := by
  classical
  set ψ := psi F hζ ι (uUnit h)
  obtain ⟨χ', hχ', hL⟩ := exists_chi' hζ ι hK h
  have h𝔣𝔪 : ArtinL.Abelian.conductor ψ * 𝔪 ≠ ⊥ :=
    mul_ne_zero (ArtinL.Abelian.conductor_ne_bot ψ) h.ne_bot
  have hnorm := T12B.norm_le_one h𝔣𝔪 χ'
  have hk : kummerL ι 𝔪 u s = χ'.LSeries s := by
    rw [kummerL_eq_tsum, T12B.lseries_eq_tsum χ' hnorm hs]
    refine tsum_congr fun I => ?_
    rw [T12B.gs, hχ']
  have h1 := hL s hs
  have hne := (C3A.euler1 (psiH ψ hK) s
    (T12A.norm_heckeChar_le (ArtinL.Abelian.conductor_ne_bot ψ) _) hs).2
  simp_rw [finprod_inv_distrib] at h1
  change (psiH ψ hK).LSeries s = χ'.LSeries s * (Efac hζ ι hK h s)⁻¹ at h1
  have hE : Efac hζ ι hK h s ≠ 0 := by
    intro h0; rw [h0, inv_zero, mul_zero] at h1; exact hne h1
  rw [hk, LSeries_eq_psiH ψ hK, h1, mul_assoc, inv_mul_cancel₀ hE, mul_one]

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3F_Core: the cut for a number field in `Type`

Totally complex `F` with a primitive sixth root of unity, `𝔪` divisible by the primes over `6`,
exterior primes principal in `R`. With the class function of `L3F_Cls`: for `u R = c R` with `c`
exterior, squarefree, `c ≠ 1`, and `x₁ x₂ = u t²` with `cls₀ x₁ = cls₀ x₂`, put `ψ = ψ_{u³}` (the
quadratic character of `F(√u)`). Then `ψ` splits at the primes over `𝔪` (`L3F_Split`), its
conductor is `c`, and `Λ = L(ψ)` (entire, `L3K`) satisfies the functional equation with root
number `1` (`L3F_Root`) and has polynomial growth on vertical strips (`L3K.growthHyp`). -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open NumberField NumberField.InfinitePlace IsDedekindDomain LanglandsTunnell.P2.Artin
  ArtinPrimitiveRoots.L3K.KB ArtinPrimitiveRoots.L3K UniqueFactorizationMonoid Complex

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3F

section Count

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

open Classical in
lemma count_le_one_of_squarefree {c : Ideal R} (hc0 : c ≠ ⊥) (hsq : Squarefree c)
    (v : HeightOneSpectrum R) :
    (Associates.mk v.asIdeal).count (Associates.mk c).factors ≤ 1 := by
  by_contra h
  push Not at h
  have h2 : 2 ≤ (Associates.mk v.asIdeal).count (Associates.mk c).factors := h
  have hle := (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hc0)
      (Associates.irreducible_mk.2 v.irreducible)).2 h2
  rw [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, sq] at hle
  exact v.isPrime.ne_top (Ideal.isUnit_iff.1 (hsq v.asIdeal hle))

open Classical in
lemma count_eq_of_squarefree {c : Ideal R} (hc0 : c ≠ ⊥) (hsq : Squarefree c)
    (v : HeightOneSpectrum R) :
    (Associates.mk v.asIdeal).count (Associates.mk c).factors =
      if c ≤ v.asIdeal then 1 else 0 := by
  split_ifs with h
  · exact le_antisymm (count_le_one_of_squarefree hc0 hsq v) (L3K.one_le_count hc0 v h)
  · by_contra hne
    exact h (Ideal.le_of_dvd ((Associates.count_ne_zero_iff_dvd hc0 v.irreducible).1 hne))

open Classical in
lemma isSixthPowerFree_pow_three {c : Ideal R} (hc0 : c ≠ ⊥) (hsq : Squarefree c) :
    ∀ J : Ideal R, J ^ 6 ∣ c ^ 3 → IsUnit J := by
  intro J hJ
  by_contra hJu
  have hJtop : J ≠ ⊤ := fun h => hJu (Ideal.isUnit_iff.2 h)
  have hc3 : c ^ 3 ≠ ⊥ := pow_ne_zero _ hc0
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    have h0 : (⊥ : Ideal R) ∣ c ^ 3 := (dvd_pow_self (⊥ : Ideal R) (by norm_num)).trans hJ
    rw [← Ideal.zero_eq_bot, zero_dvd_iff] at h0
    exact hc3 h0
  obtain ⟨P, hPm, hJP⟩ := Ideal.exists_le_maximal J hJtop
  have hP0 : P ≠ ⊥ := fun h => hJ0 (le_bot_iff.1 (h ▸ hJP))
  let v : HeightOneSpectrum R := ⟨P, hPm.isPrime, hP0⟩
  have h6 : v.asIdeal ^ 6 ∣ c ^ 3 :=
    (pow_dvd_pow_of_dvd (Ideal.dvd_iff_le.2 hJP) 6).trans hJ
  have hle := (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hc3)
    (Associates.irreducible_mk.2 v.irreducible) (k := 6)).1
    (by rw [← Associates.mk_pow]; exact Associates.mk_le_mk_iff_dvd.2 h6)
  rw [Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.2 hc0)
      (Associates.irreducible_mk.2 v.irreducible)] at hle
  have := count_le_one_of_squarefree hc0 hsq v
  omega

end Count

variable {F : Type} [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ 6) (ι : F →+* ℂ)
  (hK : ∀ w : InfinitePlace F, w.IsComplex)

include hζ hK in
/-- **The cut in universe `0`.** -/
theorem core (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥)
    (hsmall : SmallPrimesDvd (Ideal.absNorm (Ideal.span {(6 : 𝓞 F)})) 𝔪)
    (hprin : ∀ v : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ v.asIdeal →
      ∃ p : SInt 𝔪, Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    ∃ (k : ℕ) (cls₀ : F → Fin k), ∀ (u : SInt 𝔪) (c : Ideal (𝓞 F)) (x₁ x₂ t : F),
      IsExterior 𝔪 c → Squarefree c → c ≠ ⊤ →
      Ideal.span {u} = c.map (algebraMap (𝓞 F) (SInt 𝔪)) →
      t ≠ 0 → x₁ * x₂ = (u : F) * t ^ 2 → cls₀ x₁ = cls₀ x₂ →
      ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
        (∀ w : ℂ, 1 < w.re →
          Λ w = (∏ P ∈ (normalizedFactors 𝔪).toFinset, (1 - (Ideal.absNorm P : ℂ) ^ (-w)))⁻¹ *
            kummerL ι 𝔪 (u ^ 3) w) ∧
        (∀ w : ℂ, (∀ m : ℕ, w ≠ -(m : ℂ)) → (∀ m : ℕ, 1 - w ≠ -(m : ℂ)) →
          (((|discr F| : ℤ) : ℂ) * (Ideal.absNorm c : ℂ)) ^ (w / 2) *
              Complex.Gammaℂ w ^ nrComplexPlaces F * Λ w =
            (((|discr F| : ℤ) : ℂ) * (Ideal.absNorm c : ℂ)) ^ ((1 - w) / 2) *
              Complex.Gammaℂ (1 - w) ^ nrComplexPlaces F * Λ (1 - w)) ∧
        (∀ σ₁ σ₂ : ℝ, ∃ C A : ℝ, ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ →
          ‖Λ w‖ ≤ C * (1 + |w.im|) ^ A) := by
  classical
  obtain ⟨k, cls₀, hcls⟩ := exists_cls 𝔪 h𝔪
  refine ⟨k, cls₀, fun u c x₁ x₂ t hcE hcsq hctop hgen ht hx12 hc12 => ?_⟩
  have hc0 : c ≠ ⊥ := hcE.1
  -- the Bridge hypotheses for `u³`, `𝔲 = c³`
  have hsix : ∀ v : HeightOneSpectrum (𝓞 F), (6 : 𝓞 F) ∈ v.asIdeal → 𝔪 ≤ v.asIdeal := by
    have h6ne : Ideal.span {(6 : 𝓞 F)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      intro h; have := congrArg (fun x : 𝓞 F => (x : F)) h; simp at this
    intro v hv
    refine hsmall v.asIdeal v.isPrime v.ne_bot (Nat.le_of_dvd ?_ ?_)
    · exact Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
    · exact Ideal.absNorm_dvd_absNorm_of_le (by rwa [Ideal.span_singleton_le_iff_mem])
  have hgen3 : Ideal.span {u ^ 3} = (c ^ 3).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← Ideal.span_singleton_pow, hgen, Ideal.map_pow]
  have hfree : IsSixthPowerFree (c ^ 3) := isSixthPowerFree_pow_three hc0 hcsq
  have hcm : ∀ v : HeightOneSpectrum (𝓞 F), c ≤ v.asIdeal → ¬ 𝔪 ≤ v.asIdeal := by
    intro v hcv hmv
    apply v.isPrime.ne_top
    rw [eq_top_iff, ← hcE.2]; exact sup_le hcv hmv
  obtain ⟨P₀, hP₀m, hcP₀⟩ := Ideal.exists_le_maximal c hctop
  have hP₀0 : P₀ ≠ ⊥ := fun h => hc0 (le_bot_iff.1 (h ▸ hcP₀))
  let v₀ : HeightOneSpectrum (𝓞 F) := ⟨P₀, hP₀m.isPrime, hP₀0⟩
  have hu0 : (u : F) ≠ 0 := by
    intro h0
    have hu : u = 0 := Subtype.ext h0
    rw [hu, Ideal.span_singleton_eq_bot.2 rfl, eq_comm,
      Ideal.map_eq_bot_iff_of_injective] at hgen
    · exact hc0 hgen
    · intro a b hab
      have := congrArg (fun x : SInt 𝔪 => (x : F)) hab
      exact FaithfulSMul.algebraMap_injective (𝓞 F) F this
  have hu30 : ((u ^ 3 : SInt 𝔪) : F) ≠ 0 := by
    rw [SubmonoidClass.coe_pow]; exact pow_ne_zero _ hu0
  have hnon : ∀ b : F, b ^ 6 ≠ ((u ^ 3 : SInt 𝔪) : F) := by
    intro b hb
    have hne := val_ne_exp_six v₀ (hcm v₀ hcP₀) hfree hgen3
      (le_trans (Ideal.pow_le_self (by norm_num)) hcP₀)
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hu30 (by rw [← hb]; ring)
    have hvb : v₀.valuation F b = WithZero.exp (WithZero.log (v₀.valuation F b)) :=
      (WithZero.exp_log (by simpa using hb0)).symm
    apply hne (WithZero.log (v₀.valuation F b))
    calc v₀.valuation F ((u ^ 3 : SInt 𝔪) : F) = v₀.valuation F b ^ 6 := by rw [← hb, map_pow]
      _ = WithZero.exp (WithZero.log (v₀.valuation F b)) ^ 6 := by rw [← hvb]
      _ = _ := by rw [← WithZero.exp_nsmul, nsmul_eq_mul]; push_cast; ring_nf
  let h : BridgeHyp 𝔪 (u ^ 3) (c ^ 3) := ⟨h𝔪, hsix, hprin, hgen3, hfree, hnon⟩
  set ψ := psi F hζ ι (uUnit h) with hψdef
  have hx3 : ((uUnit h : Fˣ) : F) = (u : F) ^ 3 := by rw [uUnit_val, SubmonoidClass.coe_pow]
  have hψ1 : ψ ≠ 1 := psi_ne_one hζ ι (uUnit h) hnon
  have hinj : Function.Injective ψ := psi_injective hζ ι (uUnit h)
  have hsq : ∀ σ, ψ σ ^ 2 = 1 := psi_sq hζ ι (uUnit h) (u : F) hx3
  -- the local splitting
  have hx0 : x₁ * x₂ ≠ 0 := by rw [hx12]; exact mul_ne_zero hu0 (pow_ne_zero _ ht)
  have hsplit : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal →
      ArtinL.Abelian.IsUnramifiedAt ψ v ∧ ArtinL.Abelian.localValue ψ v = 1 := by
    intro v hv
    obtain ⟨y, d, hy, hxy, hd⟩ := hcls x₁ x₂ (left_ne_zero_of_mul hx0)
      (right_ne_zero_of_mul hx0) hc12 v hv
    refine psi_local_split hζ ι (uUnit h) (u : F) hx3 v (y / t) d (div_ne_zero hy ht) ?_ hd
    have e : (u : F) * t ^ 2 = y ^ 2 * d := hx12.symm.trans hxy
    field_simp
    linear_combination e
  -- the conductor
  have hexp : ∀ v : HeightOneSpectrum (𝓞 F), ArtinL.Abelian.conductorExponent ψ v =
      (Associates.mk v.asIdeal).count (Associates.mk c).factors := by
    intro v
    rw [count_eq_of_squarefree hc0 hcsq v]
    split_ifs with hcv
    · have hvm := hcm v hcv
      have h3 : c ^ 3 ≤ v.asIdeal := le_trans (Ideal.pow_le_self (by norm_num)) hcv
      have hram := (ramified_of_le hζ ι h hvm h3).1
      have h6 : ((6 : ℕ) : 𝓞 F) ∉ v.asIdeal := by exact_mod_cast six_not_mem h hvm
      have hle : ArtinL.Abelian.conductorExponent ψ v ≤ 1 :=
        conductorExponent_psi_le_one hζ ι (uUnit h) v h6
      have hge : 1 ≤ ArtinL.Abelian.conductorExponent ψ v := by
        unfold ArtinL.Abelian.conductorExponent; rw [if_neg hram]; omega
      omega
    · by_cases hvm : 𝔪 ≤ v.asIdeal
      · exact conductorExponent_psi_eq_zero hζ ι (uUnit h) v (hsplit v hvm).1
      · have h3 : ¬ c ^ 3 ≤ v.asIdeal := fun h3 => hcv (v.isPrime.le_of_pow_le h3)
        exact conductorExponent_psi_eq_zero hζ ι (uUnit h) v
          (localValue_eq_sextic hζ ι h hvm h3).1
  have hcond : ArtinL.Abelian.conductor ψ = c := by
    rw [ArtinL.Abelian.conductor]
    simp_rw [hexp]
    exact finprod_count_eq hc0
  -- the Euler factors at `𝔪`
  have hEfac : ∀ s : ℂ, Efac hζ ι hK h s =
      ∏ P ∈ (normalizedFactors 𝔪).toFinset, (1 - (Ideal.absNorm P : ℂ) ^ (-s)) := by
    intro s
    rw [← finprod_mem_coe_finset]
    unfold Efac
    refine finprod_congr fun P => ?_
    have hiff : (P.IsPrime ∧ P ≠ ⊥ ∧ ArtinL.Abelian.conductor ψ * 𝔪 ≤ P ∧
        P ⊔ ArtinL.Abelian.conductor ψ = ⊤) ↔
        P ∈ ((normalizedFactors 𝔪).toFinset : Set (Ideal (𝓞 F))) := by
      rw [Finset.mem_coe, Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff h𝔪, hcond]
      constructor
      · rintro ⟨hP, -, hle, htop⟩
        refine ⟨hP, ?_⟩
        rcases hP.mul_le.1 hle with h1 | h1
        · exact absurd (by rw [eq_top_iff, ← htop]; exact sup_le le_rfl h1) hP.ne_top
        · exact h1
      · rintro ⟨hP, hmP⟩
        have hP0 : P ≠ ⊥ := fun h0 => h𝔪 (le_bot_iff.1 (h0 ▸ hmP))
        refine ⟨hP, hP0, le_trans Ideal.mul_le_right hmP, ?_⟩
        by_contra hne
        have hmax := hP.isMaximal hP0
        have hcP : c ≤ P := by
          have := hmax.eq_of_le hne le_sup_left
          rw [this]; exact le_sup_right
        exact hcm ⟨P, hP, hP0⟩ hcP hmP
    rw [finprod_congr_Prop (propext hiff) (g := fun _ => 1 - (Ideal.absNorm P : ℂ) ^ (-s))]
    intro hP
    have hP' := hiff.2 hP
    have hv := (L3K.psiH_prime ψ hK ⟨P, hP'.1, hP'.2.1⟩)
    simp only at hv
    rw [hv]
    have hmP : 𝔪 ≤ P := by
      rw [Finset.mem_coe, Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff h𝔪] at hP
      exact hP.2
    rw [(hsplit ⟨P, hP'.1, hP'.2.1⟩ hmP).2, one_mul]
  -- the completed `L`-function with root number `1`
  obtain ⟨ΛA, hΛA, hΛAre, hΛAfe⟩ := fe_root_one hinj hsq hψ1 hK
  refine ⟨Lfun ψ ΛA, Lfun_differentiable ψ hΛA, ?_, ?_, ?_⟩
  · intro w hw
    rw [Lfun_eq ψ hK hΛAre hw, kummerL_eq hζ ι hK h hw, hEfac w]
    have hE : ∏ P ∈ (normalizedFactors 𝔪).toFinset, (1 - (Ideal.absNorm P : ℂ) ^ (-w)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro P hP
      rw [Multiset.mem_toFinset] at hP
      have hP0 : P ≠ ⊥ := ne_zero_of_mem_normalizedFactors hP
      have hPp : P.IsPrime := (Ideal.mem_normalizedFactors_iff h𝔪).1 hP |>.1
      have h2 := C3A.two_le_absNorm hPp hP0
      intro h0
      have hx : (Ideal.absNorm P : ℂ) ^ (-w) = 1 := (sub_eq_zero.1 h0).symm
      have h1 : ‖(Ideal.absNorm P : ℂ) ^ (-w)‖ = 1 := by rw [hx, norm_one]
      rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re] at h1
      have : ((Ideal.absNorm P : ℕ) : ℝ) ^ (-w.re) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < Ideal.absNorm P))
          (by linarith)
      linarith
    rw [mul_comm (ArtinL.Abelian.LSeries ψ w), ← mul_assoc, inv_mul_cancel₀ hE, one_mul]
  · intro w hw1 hw2
    have hD : ((Dψ ψ : ℝ) : ℂ) = ((|discr F| : ℤ) : ℂ) * (Ideal.absNorm c : ℂ) := by
      simp only [Dψ, hcond, Complex.ofReal_mul, Complex.ofReal_natCast, ← Int.cast_abs,
        Complex.ofReal_intCast]
    have hD0 : ((Dψ ψ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans_le (one_le_Dψ ψ)).ne'
    have hG : ∀ z : ℂ, (∀ m : ℕ, z ≠ -(m : ℂ)) → Gammaℂ z ≠ 0 := by
      intro z hz
      rw [Gammaℂ_def]
      refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero hz)
      rw [Ne, Complex.cpow_eq_zero_iff]; push Not; intro h
      exact absurd h (by simp [Real.pi_ne_zero])
    have key : ∀ z : ℂ, Gammaℂ z ≠ 0 →
        ((Dψ ψ : ℝ) : ℂ) ^ (z / 2) * Gammaℂ z ^ nrComplexPlaces F * Lfun ψ ΛA z = ΛA z := by
      intro z hz
      have hc : ((Dψ ψ : ℝ) : ℂ) ^ (z / 2) * ((Dψ ψ : ℝ) : ℂ) ^ (-z / 2) = 1 := by
        rw [← Complex.cpow_add _ _ hD0, show z / 2 + -z / 2 = 0 by ring, Complex.cpow_zero]
      have hg : Gammaℂ z ^ nrComplexPlaces F * (Gammaℂ z)⁻¹ ^ nrComplexPlaces F = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hz, one_pow]
      rw [Lfun]
      calc _ = (((Dψ ψ : ℝ) : ℂ) ^ (z / 2) * ((Dψ ψ : ℝ) : ℂ) ^ (-z / 2)) *
            (Gammaℂ z ^ nrComplexPlaces F * (Gammaℂ z)⁻¹ ^ nrComplexPlaces F) * ΛA z := by ring
        _ = _ := by rw [hc, hg, one_mul, one_mul]
    rw [← hD, key w (hG w hw1), key (1 - w) (hG (1 - w) hw2), hΛAfe]
  · intro σ₁ σ₂
    obtain ⟨A, N, hA⟩ := growthHyp ψ hK hψ1 (|σ₁| + |σ₂|) (Lfun ψ ΛA)
      (Lfun_differentiable ψ hΛA) (fun s hs => Lfun_eq ψ hK hΛAre hs)
    refine ⟨A, N, fun w h1 h2 => ?_⟩
    rw [Real.rpow_natCast]
    exact hA w (by linarith [neg_abs_le σ₁, abs_nonneg σ₂])
      (by linarith [le_abs_self σ₂, abs_nonneg σ₁])

end L3F

end ArtinPrimitiveRoots

end
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

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3B_Main: (7.16)–(7.17) at `u = 1` from four arithmetic cuts

With `b(𝔠, 𝔫, 𝔰, 𝔯) = γ₂(𝔠) ϑ(𝔠𝔫³) F(𝔰, 𝔠𝔫³, gen(𝔯)⁶)` (the coefficient at `u = 1`, without the
`S`-unit `u`), the target `exists_cutoff_freqCoeff_principalFreq_eq_one_and_eq_mul` follows from

* `CutMul`: cross-prime multiplicativity `b(P^{e₀}𝔠, P^l𝔫, P^k𝔰, P^m𝔯) = b(P^{e₀},P^l,P^k,P^m) b(𝔠,𝔫,𝔰,𝔯)`
  ((7.14), (7.16): Chinese remainders + reciprocity (3.3));
* `CutF`: the local Poisson factor `F(P^k, P^{e₀}(P^l)³, gen(P^m)⁶)` ((7.15), (7.17));
* `CutHD`: `γ₁(P) γ₂(P) Λ̄(P) Ḡ(P) = −1` (Davenport–Hasse, (3.9)–(3.11));
* `CutG6`: `Ḡ(P)⁶ = 1`.

Proved here: `a(1,1,1,1) = 1` (`C3B_Norm`), the `U_S⁶`-invariance replacing `u` by `1`
(`C3B_Unit`, `C3B_Good`), `ϑ` on prime powers, `Λ⁶ = jacobiPhaseSix`, and the table algebra. -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

/-! ### Elementary lemmas -/

end C3B

end ArtinPrimitiveRoots

end
end

section
section
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

section val

variable {v : HeightOneSpectrum (𝓞 F)}

lemma coe_alg (a : 𝓞 F) : ((algebraMap (𝓞 F) (SInt 𝔪) a : SInt 𝔪) : F) = algebraMap (𝓞 F) F a :=
  rfl

lemma val_le_one (hv : v ∉ placesOf 𝔪) (r : SInt 𝔪) : v.valuation F (r : F) ≤ 1 := r.2 v hv

lemma val_alg (a : 𝓞 F) : v.valuation F (algebraMap (𝓞 F) F a) = v.intValuation a :=
  v.valuation_of_algebraMap a

/-- Elements of `v^j R` have valuation at most `exp(-j)`. -/
lemma val_le_of_mem (hv : v ∉ placesOf 𝔪) (j : ℕ) {r : SInt 𝔪}
    (hr : r ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪))) :
    v.valuation F (r : F) ≤ exp (-(j : ℤ)) := by
  rw [Ideal.map] at hr
  induction hr using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [coe_alg, val_alg]
    exact (v.intValuation_le_pow_iff_mem a j).2 ha
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subalgebra.coe_add]
    exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  | smul a x _ hx =>
    rw [smul_eq_mul, Subalgebra.coe_mul, map_mul]
    calc v.valuation F (a : F) * v.valuation F (x : F) ≤ 1 * exp (-(j : ℤ)) :=
          mul_le_mul' (val_le_one hv a) hx
      _ = _ := one_mul _

/-- An element of `𝓞` not in `v` has an inverse modulo `v^j`. -/
lemma exists_mul_sub_one_mem (j : ℕ) {d : 𝓞 F} (hd : d ∉ v.asIdeal) :
    ∃ c : 𝓞 F, c * d - 1 ∈ v.asIdeal ^ j := by
  have h1 : IsCoprime v.asIdeal (Ideal.span {d}) := by
    obtain ⟨y, i, hi, hyi⟩ := v.isMaximal.exists_inv hd
    exact Ideal.isCoprime_iff_exists.mpr ⟨i, hi, y * d, Ideal.mul_mem_left _ _
      (Ideal.mem_span_singleton_self d), by rw [add_comm]; exact hyi⟩
  obtain ⟨i, hi, x, hx, hix⟩ := (h1.pow_left (m := j)).exists
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  refine ⟨c, ?_⟩
  have : c * d - 1 = -i := by linear_combination hix
  rw [this]
  exact neg_mem hi

/-- Every `x ∈ F` with `v(x) ≤ 1` is congruent modulo `v^j` (in valuation) to an element of `𝓞`. -/
lemma exists_val_sub_le (j : ℕ) (x : F) (hx : v.valuation F x ≤ 1) :
    ∃ a : 𝓞 F, v.valuation F (x - algebraMap (𝓞 F) F a) ≤ exp (-(j : ℤ)) := by
  obtain ⟨n, ⟨d, hd⟩, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer (K := F) x hx
  obtain ⟨c, hc⟩ := exists_mul_sub_one_mem (v := v) j hd
  refine ⟨c * n, ?_⟩
  have hvd : v.valuation F (algebraMap (𝓞 F) F d) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hd
  have heq : x - algebraMap (𝓞 F) F (c * n) =
      -(x * algebraMap (𝓞 F) F (c * d - 1)) := by
    have hnd' : x * algebraMap (𝓞 F) F d = algebraMap (𝓞 F) F n := hnd
    rw [map_mul, ← hnd', map_sub, map_mul, map_one]; ring
  rw [heq, Valuation.map_neg, map_mul, val_alg]
  calc v.valuation F x * v.intValuation (c * d - 1) ≤ 1 * exp (-(j : ℤ)) :=
        mul_le_mul' hx ((v.intValuation_le_pow_iff_mem _ j).2 hc)
    _ = _ := one_mul _

/-- Elements of `R` of valuation at most `exp(-j)` lie in `v^j R`. -/
lemma mem_of_val_le (hv : v ∉ placesOf 𝔪) (j : ℕ) (r : SInt 𝔪)
    (h : v.valuation F (r : F) ≤ exp (-(j : ℤ))) :
    r ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  obtain ⟨n, ⟨d, hd⟩, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer (K := F) (r : F) (r.2 v hv)
  have hnd' : (r : F) * algebraMap (𝓞 F) F d = algebraMap (𝓞 F) F n := hnd
  have hvd : v.valuation F (algebraMap (𝓞 F) F d) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hd
  have hn : n ∈ v.asIdeal ^ j := by
    rw [← v.intValuation_le_pow_iff_mem, ← val_alg (v := v), ← hnd', map_mul, hvd, mul_one]
    exact h
  obtain ⟨c, hc⟩ := exists_mul_sub_one_mem (v := v) j hd
  have heq : r = algebraMap (𝓞 F) (SInt 𝔪) (c * n) -
      r * algebraMap (𝓞 F) (SInt 𝔪) (c * d - 1) := by
    apply Subtype.ext
    rw [Subalgebra.coe_sub, Subalgebra.coe_mul, coe_alg, coe_alg, map_mul, map_sub, map_mul,
      map_one, ← hnd']
    ring
  rw [heq]
  exact sub_mem (Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ _ hn))
    (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hc))

lemma mem_map_pow_iff (hv : v ∉ placesOf 𝔪) (j : ℕ) (r : SInt 𝔪) :
    r ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) ↔
      v.valuation F (r : F) ≤ exp (-(j : ℤ)) :=
  ⟨val_le_of_mem hv j, mem_of_val_le hv j r⟩

lemma alg_mem_map_pow_iff (hv : v ∉ placesOf 𝔪) (j : ℕ) (a : 𝓞 F) :
    algebraMap (𝓞 F) (SInt 𝔪) a ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) ↔
      a ∈ v.asIdeal ^ j := by
  rw [mem_map_pow_iff hv, coe_alg, val_alg, v.intValuation_le_pow_iff_mem]

lemma exists_sub_mem_map_pow (hv : v ∉ placesOf 𝔪) (j : ℕ) (r : SInt 𝔪) :
    ∃ a : 𝓞 F, r - algebraMap (𝓞 F) (SInt 𝔪) a ∈
      (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  obtain ⟨a, ha⟩ := exists_val_sub_le (v := v) j (r : F) (r.2 v hv)
  exact ⟨a, mem_of_val_le hv j _ (by rw [Subalgebra.coe_sub, coe_alg]; exact ha)⟩

end val

section quot

variable {v : HeightOneSpectrum (𝓞 F)}

/-- `𝓞/v^j → R/v^j R`. -/
noncomputable def quotHom (𝔪 : Ideal (𝓞 F)) (I : Ideal (𝓞 F)) :
    𝓞 F ⧸ I →+* SInt 𝔪 ⧸ I.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
  Ideal.quotientMap _ (algebraMap (𝓞 F) (SInt 𝔪)) Ideal.le_comap_map

lemma quotHom_mk (I : Ideal (𝓞 F)) (a : 𝓞 F) :
    quotHom 𝔪 I (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk (I.map (algebraMap (𝓞 F) (SInt 𝔪))) (algebraMap (𝓞 F) (SInt 𝔪) a) :=
  rfl

lemma quotHom_bijective (hv : v ∉ placesOf 𝔪) (j : ℕ) :
    Function.Bijective (quotHom 𝔪 (v.asIdeal ^ j)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [quotHom_mk, Ideal.Quotient.eq_zero_iff_mem, alg_mem_map_pow_iff hv] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  · intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := exists_sub_mem_map_pow hv j r
    exact ⟨Ideal.Quotient.mk _ a, by rw [quotHom_mk]; exact (Ideal.Quotient.eq.mpr ha).symm⟩

/-- `𝓞/v^j ≃+* R/v^j R`. -/
noncomputable def quotEquiv (hv : v ∉ placesOf 𝔪) (j : ℕ) :
    𝓞 F ⧸ v.asIdeal ^ j ≃+* SInt 𝔪 ⧸ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) :=
  RingEquiv.ofBijective _ (quotHom_bijective hv j)

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

/-- `v R` is a maximal ideal of `R`. -/
lemma isMaximal_map (hv : v ∉ placesOf 𝔪) :
    (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))).IsMaximal := by
  have e := quotEquiv (𝔪 := 𝔪) hv 1
  rw [pow_one] at e
  apply Ideal.Quotient.maximal_of_isField
  have : (v.asIdeal).IsMaximal := v.isMaximal
  have hf : IsField (𝓞 F ⧸ v.asIdeal) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp this
  exact MulEquiv.isField hf e.symm.toMulEquiv

end quot

section fibre

variable {v : HeightOneSpectrum (𝓞 F)}

end fibre

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3I_Add: the additive character `e`

* `HasWit 𝔪 x`: `x` has a witness `y` in the definition of `sAddChar` (`x - y ∈ R`, `y` integral
  at `S`). `hasWit_of_mul_mem`: true when `x I ⊆ R` for an ideal `I` coprime to `𝔪`; in particular
  `hasWit_div_gen`: `a / gen 𝔞` for `a ∈ R`, `𝔞` exterior.
* `sAddChar_eq_of_wit`: `e(x) = exp(-2πi Tr y)` for every witness; `sAddChar_add`: `e` is additive
  on elements with witnesses.
* `exists_trace_not_int`: for `P ∤ 𝔇`, some `z ∈ P⁻¹` has `Tr z ∉ ℤ`; `sAddChar_ne_one_of_dual`.
* `exists_sAddChar_ne_one`: primitivity at every level: for `x ∈ R ∖ P^j R` some `r ∈ R` has
  `e(x r / gen(P^j)) ≠ 1`.
-/

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

variable {ι : F →+* ℂ}

/-! ### The inverse different -/

/-! ### Primitivity at every level -/

section prim

variable {v : HeightOneSpectrum (𝓞 F)}

end prim

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Base: hypotheses from section A, finite quotients `R/𝔞R`, residue-symbol algebra

* `HypAdd 𝔪`: `e` is additive on `F` (needs the existence of `sAddChar` witnesses).
* `HypChi ι 𝔪`: at every exterior prime `P`, `χ_P` is multiplicative on `R` and `χ_P(x)⁶ = 1`
  for `x ∉ PR`.
-/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F]

/-- Hypothesis (section A): at an exterior prime, the sextic symbol is multiplicative on `R`, with
sixth power `1` off `PR`. -/
def HypChi (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) : Prop :=
  ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P →
    (∀ x y : SInt 𝔪, sexticResidueSymbol ι 𝔪 P (x * y) =
      sexticResidueSymbol ι 𝔪 P x * sexticResidueSymbol ι 𝔪 P y) ∧
    (∀ x : SInt 𝔪, x ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) → sexticResidueSymbol ι 𝔪 P x ^ 6 = 1)

variable {𝔪 : Ideal (𝓞 F)}

/-! ### Ideals -/

lemma exterior_of_mem_factors {𝔞 Q : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    (hQ : Q ∈ normalizedFactors 𝔞) : Q.IsPrime ∧ IsExterior 𝔪 Q := by
  have hpr : Prime Q := prime_of_normalized_factor Q hQ
  refine ⟨Ideal.isPrime_of_prime hpr, hpr.ne_zero, ?_⟩
  have hle : 𝔞 ≤ Q := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hQ)
  exact eq_top_iff.mpr (h𝔞.2 ▸ sup_le_sup_right hle 𝔪)

/-! ### Residue symbols -/

variable {ι : F →+* ℂ}

lemma residueSymbol_mul (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    (x y : SInt 𝔪) :
    residueSymbol ι 𝔪 𝔞 (x * y) = residueSymbol ι 𝔪 𝔞 x * residueSymbol ι 𝔪 𝔞 y := by
  unfold residueSymbol
  rw [← Multiset.prod_map_mul]
  congr 1
  refine Multiset.map_congr rfl fun Q hQ => ?_
  obtain ⟨hQp, hQe⟩ := exterior_of_mem_factors h𝔞 hQ
  exact (hχ Q hQp hQe).1 x y

/-! ### Generators -/

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Sum: the Poisson sum and the Gauss sum with free generators; CRT and twists

* `PS 𝔰 𝔄 s A Af c h = ∑_{d mod 𝔰} ∑_{v mod 𝔄} [h ≡ Af d (𝔰)] χ_𝔰(d) χ_𝔄(v) e((h − Af d) v c/(sA))`;
  `poissonFactor g 𝔰 𝔄 h = PS 𝔰 𝔄 (gen 𝔰) (gen 𝔄) (gen 𝔄) 1 h`.
* `GS 𝔠 c c' j = ∑_{x mod 𝔠} χ_𝔠(x)^j e(x c'/c)`; `gaussPhase g j 𝔠 = q^{-1/2} GS 𝔠 (gen 𝔠) 1 j`.
* `PS_crt`, `GS_crt`: Chinese remainders with idempotents `β s₂A₂`, `α s₁A₁`.
* `PS_twist`, `GS_twist`: unit substitutions.
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F]

section defs

variable (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F))

end defs

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-! ### Generic lemmas -/

/-! ### Coercions -/

/-! ### The Poisson summand -/

section U

variable {𝔰 𝔄 : Ideal (𝓞 F)} {s A Af c h : SInt 𝔪}

end U

/-! ### Field identities -/

/-! ### CRT and twists for `PS` -/

section crt

variable {𝔰₁ 𝔰₂ 𝔄₁ 𝔄₂ : Ideal (𝓞 F)} {s₁ s₂ A₁ A₂ Af c h α β : SInt 𝔪}

end crt

/-! ### Gauss sums -/

section gs

variable {𝔠 : Ideal (𝓞 F)} {c c' : SInt 𝔪} {j : ℕ}

end gs

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Mul: twisted multiplicativity of `γ_j`, of `F(𝔰, 𝔄, gen(𝔯)⁶)`, of `ϑ`, and reciprocity

* `gaussPhase_mul` (3.10): `γ_j(𝔠₁𝔠₂) = χ_{𝔠₁}(c₂)^j χ_{𝔠₂}(c₁)^j γ_j(𝔠₁) γ_j(𝔠₂)`.
* `poissonFactor_mul`: for `𝔰₁𝔄₁` coprime to `𝔰₂𝔄₂`, `𝔯ᵢ` coprime to the other side,
  `χ_{𝔰₁}(A₂) χ_{𝔰₂}(A₁) F(𝔰₁𝔰₂, 𝔄₁𝔄₂, gen(𝔯₁𝔯₂)⁶)
     = χ_{𝔄₁}(s₂A₂) χ_{𝔄₂}(s₁A₁) F(𝔰₁, 𝔄₁, gen(𝔯₁)⁶) F(𝔰₂, 𝔄₂, gen(𝔯₂)⁶)`.
* `residueSymbol_gen_prime`: `χ_𝔟(gen P) = χ_P(gen 𝔟)` (from (3.3)).
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-! ### Coprimality in `R` -/

/-! ### Change of generators -/

/-! ### Generators and residue symbols -/

/-! ### `ϑ` and norms -/

/-! ### (3.10) -/

/-! ### Cross-prime multiplicativity of the Poisson factor -/

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Main: CutMul from `HypAdd` and `HypChi`

`b(P^{e₀}𝔠, P^l𝔫, P^k𝔰, P^m𝔯) = b(P^{e₀}, P^l, P^k, P^m) b(𝔠, 𝔫, 𝔰, 𝔯)`: `ϑ` is completely
multiplicative; `γ₂` and `F` split by (3.10) and `poissonFactor_mul`; with `a = χ_P(gen 𝔠)`,
`w = χ_P(gen 𝔠𝔫³) = a b³`, `σ = χ_P(gen 𝔰)`, `t = e₀ + 3l` the cross factors are
`a^{4e₀}` and `w^{2t}`, whose product is `1`.
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F]

/-- `HypChi` for all moduli divisible by the small primes. -/
def HypChiAll (F : Type*) [Field F] [NumberField F] (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → HypChi ι 𝔪

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

end C3M

end ArtinPrimitiveRoots

end
end

section
section
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

lemma chi_pow_six_apply (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) :
    chi ι h hω y ^ 6 = 1 := by
  obtain ⟨i, -, hi⟩ := exists_pow_e h hω hy
  rw [chi_eq_pow h hω hy hi, ← pow_mul, mul_comm, pow_mul, (iota_omega_prim hω).pow_eq_one,
    one_pow]

end chi

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Chk: `HypChi` from section A's `χ_P` (`C3I_Char`), and CutMul

Exterior primes are `C3I.Good` once `N₀ ≥ max(3^[F:ℚ], N 𝔇)`: `12 ∣ N P − 1` because `μ₁₂ ⊂ F`
and `P ∤ 6`, and `P ∤ 𝔇` because `N P > N 𝔇`.
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F]

/-- In `ℚ(μ_n)` with `12 ∣ n`, a prime of norm `> 3^[F:ℚ]` has `12 ∣ N P − 1`. -/
theorem twelve_dvd_absNorm_sub_one (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    [IsCyclotomicExtension {n} ℚ F]
    (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hQ : 3 ^ Module.finrank ℤ (𝓞 F) < Ideal.absNorm P) : 12 ∣ Ideal.absNorm P - 1 := by
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
    have := C3B.absNorm_le_of_prime_dvd 2 Nat.prime_two P hP0 h; omega
  have h3 : ¬ 3 ∣ Q := fun h => by
    have := C3B.absNorm_le_of_prime_dvd 3 Nat.prime_three P hP0 h; omega
  have hcop : Q.Coprime 12 := by
    have c2 : Q.Coprime 2 :=
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2))
    have c3 : Q.Coprime 3 :=
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3))
    have : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
    rw [this]; exact Nat.Coprime.mul_right (Nat.Coprime.pow_right 2 c2) c3
  have : NeZero n := ⟨hn0.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  have hζ12 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ (n / 12)) 12 :=
    hζ.pow hn0 (Nat.div_mul_cancel hn).symm
  have hω : IsPrimitiveRoot hζ12.toInteger 12 := hζ12.toInteger_isPrimitiveRoot
  have hωb : IsPrimitiveRoot (Ideal.Quotient.mk P hζ12.toInteger) 12 :=
    hω.idealQuotient_mk (by omega) hcop
  have h1 : Ideal.Quotient.mk P hζ12.toInteger ^ (Q - 1) = 1 := by
    rw [show Q = Fintype.card (𝓞 F ⧸ P) from (C3B.card_quot P hP0).symm]
    exact FiniteField.pow_card_sub_one_eq_one _ (hωb.ne_zero (by norm_num))
  exact (hωb.pow_eq_one_iff_dvd _).mp h1

/-- `HypChi` holds for every modulus divisible by the primes of norm `≤ max(3^[F:ℚ], N 𝔇)`. -/
theorem hypChiAll (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) : HypChiAll F ι := by
  refine ⟨max (3 ^ Module.finrank ℤ (𝓞 F)) (Ideal.absNorm (differentIdeal ℤ (𝓞 F))),
    fun 𝔪 _ hS P hP hPe => ?_⟩
  have h𝔪 : ¬ 𝔪 ≤ P := by
    intro h
    apply hP.ne_top
    rw [eq_top_iff, ← hPe.2]
    exact sup_le le_rfl h
  have hgt : max (3 ^ Module.finrank ℤ (𝓞 F)) (Ideal.absNorm (differentIdeal ℤ (𝓞 F))) <
      Ideal.absNorm P := by
    by_contra hc
    exact h𝔪 (hS P hP hPe.1 (not_lt.mp hc))
  let v : HeightOneSpectrum (𝓞 F) := ⟨P, hP, hPe.1⟩
  have hdiff : ¬ differentIdeal ℤ (𝓞 F) ≤ P := by
    intro hle
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
    have hD0 : Ideal.absNorm (differentIdeal ℤ (𝓞 F)) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact differentIdeal_ne_bot
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hD0) hdvd
    have := le_max_right (3 ^ Module.finrank ℤ (𝓞 F)) (Ideal.absNorm (differentIdeal ℤ (𝓞 F)))
    omega
  have hgood : C3I.Good 𝔪 v :=
    ⟨hPe.2, twelve_dvd_absNorm_sub_one n hn0 hn P hP hPe.1 (lt_of_le_of_lt (le_max_left _ _) hgt),
      hdiff⟩
  have : NeZero n := ⟨hn0.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  have hζ6 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ (n / 6)) 6 :=
    hζ.pow hn0 (Nat.div_mul_cancel (Nat.dvd_trans (by norm_num) hn)).symm
  have hω : IsPrimitiveRoot hζ6.toInteger 6 := hζ6.toInteger_isPrimitiveRoot
  have e : ∀ z : SInt 𝔪, C3I.chi ι hgood hω (Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) z) =
      sexticResidueSymbol ι 𝔪 P z := fun z => C3I.chi_mk hgood hω z
  refine ⟨fun x y => ?_, fun x hx => ?_⟩
  · have h : C3I.chi ι hgood hω (Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x *
        Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) y) =
        C3I.chi ι hgood hω (Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x) *
          C3I.chi ι hgood hω (Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) y) :=
      map_mul _ _ _
    rw [← map_mul, e, e, e] at h
    exact h
  · have hne : Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x ≠ 0 := by
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    have h := C3I.chi_pow_six_apply (ι := ι) hgood hω hne
    rwa [e] at h

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3F_Dev: the cut under GL Prop 5.2, statement verbatim, for `F : Type*`

`cls I` is the local square-class invariant of `gen I` (`L3F_Cls`), read in a universe-`0`
model `F₀ ≃+* F`. For the data `𝔤, c₁, c₂`: `u = gen c₁ · gen c₂`, `c = c₁ c₂`,
`gen(𝔤 cᵢ) = εᵢ⁶ gen 𝔤 gen cᵢ`, so `gen(𝔤c₁) gen(𝔤c₂) = u t²` with `t = (ε₁ε₂)³ gen 𝔤`; the summand
is `χ_𝔞(u³)` (`HypChi`), and `L3F.core` applies in `F₀`. This module does not import the
target's stub. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open NumberField NumberField.InfinitePlace IsDedekindDomain UniqueFactorizationMonoid

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3F


theorem small_model (F : Type u) [Field F] [NumberField F] :
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

/-- A number field with a primitive sixth root of unity is totally complex. -/
lemma isComplex_of_prim6' (K : Type*) [Field K] [NumberField K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 6) (w : InfinitePlace K) : w.IsComplex := by
  rw [← not_isReal_iff_isComplex]
  intro hw
  have h := hζ.map_of_injective (embedding_of_isReal hw).injective
  have h6 : ((embedding_of_isReal hw) ζ) ^ 6 = 1 := h.pow_eq_one
  have h2 : ((embedding_of_isReal hw) ζ) ^ 2 = 1 := by
    have : (((embedding_of_isReal hw) ζ) ^ 2) ^ 3 = 1 := by rw [← pow_mul]; exact h6
    exact (pow_eq_one_iff_of_nonneg (sq_nonneg _) (by norm_num)).1 this
  have := h.dvd_of_pow_eq_one 2 h2
  omega

variable {F F' : Type*} [Field F] [NumberField F] [Field F'] [NumberField F']

lemma rsMul' (ι : F →+* ℂ) {𝔪 : Ideal (𝓞 F)} (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (x : SInt 𝔪) :
    residueSymbol ι 𝔪 (I * J) x = residueSymbol ι 𝔪 I x * residueSymbol ι 𝔪 J x := by
  unfold residueSymbol
  rw [normalizedFactors_mul hI hJ, Multiset.map_add, Multiset.prod_add]

lemma rsPrime' (ι : F →+* ℂ) {𝔪 : Ideal (𝓞 F)} {P : Ideal (𝓞 F)} (hP : Irreducible P)
    (x : SInt 𝔪) : residueSymbol ι 𝔪 P x = sexticResidueSymbol ι 𝔪 P x := by
  unfold residueSymbol
  rw [normalizedFactors_irreducible hP, normalize_eq]; simp

lemma rsTop' (ι : F →+* ℂ) {𝔪 : Ideal (𝓞 F)} (x : SInt 𝔪) : residueSymbol ι 𝔪 ⊤ x = 1 := by
  unfold residueSymbol
  rw [← Ideal.one_eq_top, normalizedFactors_one]; simp

lemma extMul' {𝔪 I J : Ideal (𝓞 F)} :
    IsExterior 𝔪 (I * J) ↔ IsExterior 𝔪 I ∧ IsExterior 𝔪 J := by
  unfold IsExterior
  have hb : I * J ≠ ⊥ ↔ I ≠ ⊥ ∧ J ≠ ⊥ := by
    simp only [ne_eq, ← Ideal.zero_eq_bot, mul_eq_zero, not_or]
  rw [hb, C3A.sup_mul_eq_top_iff]; tauto

lemma residueSymbol_transport' (e : F ≃+* F') (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F))
    (h6 : ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → P ⊔ Ideal.span {6} = ⊤)
    (x : SInt 𝔪) (I : Ideal (𝓞 F)) (hI : IsExterior 𝔪 I) :
    residueSymbol (ι.comp (e.symm : F' →+* F)) (𝔪.map (RingOfIntegers.mapRingEquiv e))
        (I.map (RingOfIntegers.mapRingEquiv e)) (C0R.sIntEquiv e 𝔪 x) =
      residueSymbol ι 𝔪 I x := by
  set eO := RingOfIntegers.mapRingEquiv e
  revert hI
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro hI; exact absurd rfl hI.1
  | h₂ y hy =>
    intro _
    rw [Ideal.isUnit_iff.1 hy, Ideal.map_top, rsTop', rsTop']
  | h₃ a p ha hp ih =>
    intro hI
    obtain ⟨hpE, haE⟩ := extMul'.1 hI
    have hpm : (p.map eO) ≠ ⊥ := fun h0 =>
      hpE.1 ((Ideal.map_eq_bot_iff_of_injective eO.injective).1 h0)
    have ham : (a.map eO) ≠ ⊥ := fun h0 =>
      haE.1 ((Ideal.map_eq_bot_iff_of_injective eO.injective).1 h0)
    have hpP : p.IsPrime := (Ideal.prime_iff_isPrime hpE.1).1 hp
    have hpmP : (p.map eO).IsPrime := Ideal.map_isPrime_of_equiv eO
    rw [Ideal.map_mul, rsMul' _ _ _ hpm ham, rsMul' _ _ _ hpE.1 haE.1,
      ih haE, rsPrime' _ ((Ideal.prime_iff_isPrime hpm).2 hpmP).irreducible,
      rsPrime' _ hp.irreducible,
      C0R.sexticResidueSymbol_transport e ι 𝔪 p (h6 p hpP hpE)]

lemma kummerL_transport' (e : F ≃+* F') (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F))
    (h6 : ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → P ⊔ Ideal.span {6} = ⊤)
    (u : SInt 𝔪) (w : ℂ) :
    kummerL (ι.comp (e.symm : F' →+* F)) (𝔪.map (RingOfIntegers.mapRingEquiv e))
        (C0R.sIntEquiv e 𝔪 u) w = kummerL ι 𝔪 u w := by
  set eO := RingOfIntegers.mapRingEquiv e
  have hback : (𝔪.map eO).map (RingOfIntegers.mapRingEquiv e.symm) = 𝔪 := by
    rw [C0R.mapRingEquiv_symm, C0R.map_equiv_symm_map]
  let σ : {I : Ideal (𝓞 F) // IsExterior 𝔪 I} ≃ {I : Ideal (𝓞 F') // IsExterior (𝔪.map eO) I} :=
    { toFun := fun I => ⟨I.1.map eO, C0R.isExterior_map e I.2⟩
      invFun := fun J => ⟨J.1.map (RingOfIntegers.mapRingEquiv e.symm), by
        have := C0R.isExterior_map e.symm J.2
        rwa [hback] at this⟩
      left_inv := fun I => Subtype.ext (by
        show (I.1.map eO).map (RingOfIntegers.mapRingEquiv e.symm) = I.1
        rw [C0R.mapRingEquiv_symm, C0R.map_equiv_symm_map])
      right_inv := fun J => Subtype.ext (by
        show (J.1.map (RingOfIntegers.mapRingEquiv e.symm)).map eO = J.1
        have := C0R.map_equiv_symm_map (RingOfIntegers.mapRingEquiv e.symm) J.1
        rwa [C0R.mapRingEquiv_symm, RingEquiv.symm_symm] at this) }
  unfold kummerL
  rw [← σ.tsum_eq]
  refine tsum_congr fun I => ?_
  show residueSymbol _ _ (I.1.map eO) _ * (Ideal.absNorm (I.1.map eO) : ℂ) ^ (-w) = _
  rw [residueSymbol_transport' e ι 𝔪 h6 u I.1 I.2, C0R.absNorm_map_equiv]

/-- The Euler factors at `𝔪` transport. -/
lemma prod_factors_transport (e : F ≃+* F') (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (w : ℂ) :
    ∏ P ∈ (normalizedFactors (𝔪.map (RingOfIntegers.mapRingEquiv e))).toFinset,
        (1 - (Ideal.absNorm P : ℂ) ^ (-w)) =
      ∏ P ∈ (normalizedFactors 𝔪).toFinset, (1 - (Ideal.absNorm P : ℂ) ^ (-w)) := by
  classical
  set eO := RingOfIntegers.mapRingEquiv e
  have h𝔪' : 𝔪.map eO ≠ ⊥ := fun h0 =>
    h𝔪 ((Ideal.map_eq_bot_iff_of_injective eO.injective).1 h0)
  have hback : ∀ J : Ideal (𝓞 F'), (J.map eO.symm).map eO = J := fun J => by
    have := C0R.map_equiv_symm_map eO.symm J
    rwa [RingEquiv.symm_symm] at this
  refine Finset.prod_nbij' (fun P => P.map eO.symm) (fun P => P.map eO) ?_ ?_ ?_ ?_ ?_
  · intro P hP
    rw [Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff h𝔪'] at hP
    rw [Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff h𝔪]
    refine ⟨by haveI := hP.1; exact Ideal.map_isPrime_of_equiv eO.symm, ?_⟩
    rw [← C0R.map_equiv_le_iff eO, hback]; exact hP.2
  · intro P hP
    rw [Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff h𝔪] at hP
    rw [Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff h𝔪']
    exact ⟨by haveI := hP.1; exact Ideal.map_isPrime_of_equiv eO,
      (C0R.map_equiv_le_iff eO).2 hP.2⟩
  · intro P _; exact hback P
  · intro P _; exact C0R.map_equiv_symm_map eO P
  · intro P _
    rw [← C0R.absNorm_map_equiv e (P.map eO.symm), hback]

lemma squarefree_map (e : F ≃+* F') {c : Ideal (𝓞 F)} (h : Squarefree c) :
    Squarefree (c.map (RingOfIntegers.mapRingEquiv e)) := by
  set eO := RingOfIntegers.mapRingEquiv e
  intro J hJ
  have hback : (J.map eO.symm).map eO = J := by
    have := C0R.map_equiv_symm_map eO.symm J
    rwa [RingEquiv.symm_symm] at this
  have hle : c ≤ J.map eO.symm * J.map eO.symm := by
    have h1 := Ideal.map_mono (f := eO.symm) (Ideal.le_of_dvd hJ)
    rwa [C0R.map_equiv_symm_map, Ideal.map_mul] at h1
  have hu := h _ (Ideal.dvd_iff_le.2 hle)
  rw [Ideal.isUnit_iff] at hu ⊢
  rw [← hback, hu, Ideal.map_top]

lemma rs_cube {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (hχ : C3M.HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)}
    (h𝔞 : IsExterior 𝔪 𝔞) (x y : SInt 𝔪) :
    residueSymbol ι 𝔪 𝔞 ((x * y) ^ 3) = residueSymbol ι 𝔪 𝔞 x ^ 3 * residueSymbol ι 𝔪 𝔞 y ^ 3 := by
  have h := fun a b => C3M.residueSymbol_mul hχ h𝔞 a b
  rw [pow_succ, sq, h, h, h]; ring

end L3F

open L3F in
theorem exists_cutoff_exists_cls_exists_differentiable_eq_tsum_residueSymbol_pow_three_and_functionalEquation
    (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ g : AllowedGen ι 𝔪, ∃ (k : ℕ) (cls : Ideal (𝓞 F) → Fin k),
        ∀ 𝔤 c₁ c₂ : Ideal (𝓞 F), IsExterior 𝔪 (𝔤 * c₁ * c₂) → Squarefree (𝔤 * c₁ * c₂) →
          c₁ * c₂ ≠ ⊤ → cls (𝔤 * c₁) = cls (𝔤 * c₂) →
          ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
            (∀ w : ℂ, 1 < w.re →
              Λ w = (∏ P ∈ (UniqueFactorizationMonoid.normalizedFactors 𝔪).toFinset,
                  (1 - (Ideal.absNorm P : ℂ) ^ (-w)))⁻¹ *
                ∑' 𝔞 : {𝔞 : Ideal (𝓞 F) // IsExterior 𝔪 𝔞},
                  residueSymbol ι 𝔪 𝔞.1 (g.gen c₁) ^ 3 * residueSymbol ι 𝔪 𝔞.1 (g.gen c₂) ^ 3 *
                    (Ideal.absNorm 𝔞.1 : ℂ) ^ (-w)) ∧
            (∀ w : ℂ, (∀ m : ℕ, w ≠ -(m : ℂ)) → (∀ m : ℕ, 1 - w ≠ -(m : ℂ)) →
              (((|discr F| : ℤ) : ℂ) * (Ideal.absNorm (c₁ * c₂) : ℂ)) ^ (w / 2) *
                  Complex.Gammaℂ w ^ InfinitePlace.nrComplexPlaces F * Λ w =
                (((|discr F| : ℤ) : ℂ) * (Ideal.absNorm (c₁ * c₂) : ℂ)) ^ ((1 - w) / 2) *
                  Complex.Gammaℂ (1 - w) ^ InfinitePlace.nrComplexPlaces F * Λ (1 - w)) ∧
            (∀ σ₁ σ₂ : ℝ, ∃ C A : ℝ, ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ →
              ‖Λ w‖ ≤ C * (1 + |w.im|) ^ A) := by
  classical
  haveI : NeZero n := ⟨hn0.ne'⟩
  have hζn := IsCyclotomicExtension.zeta_spec n ℚ F
  obtain ⟨k, hk⟩ := (show 6 ∣ n from dvd_trans (by norm_num) hn)
  have hζ6 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ k) 6 :=
    hζn.pow hn0 (by rw [hk]; ring)
  obtain ⟨Nχ, hNχ⟩ := C3M.hypChiAll (F := F) n hn0 hn ι
  -- the universe-0 model
  obtain ⟨F₀, _, _, ⟨e₀⟩⟩ := L3F.small_model F
  set e : F ≃+* F₀ := e₀.symm
  set eO := RingOfIntegers.mapRingEquiv e
  have hζ' := hζ6.map_of_injective e.injective
  have hK' := isComplex_of_prim6' F₀ hζ'
  have hK : ∀ w : InfinitePlace F, w.IsComplex := isComplex_of_prim6' F hζ6
  -- invariants of the model
  have hdiscr : discr F₀ = discr F := NumberField.discr_eq_discr_of_algEquiv _ e₀.toRatAlgEquiv
  have hnr : nrComplexPlaces F₀ = nrComplexPlaces F := by
    have h1 := card_add_two_mul_card_eq_rank F₀
    have h2 := card_add_two_mul_card_eq_rank F
    haveI : IsTotallyComplex F₀ := ⟨hK'⟩
    haveI : IsTotallyComplex F := ⟨hK⟩
    rw [IsTotallyComplex.nrRealPlaces_eq_zero, zero_add] at h1 h2
    have h3 : Module.finrank ℚ F₀ = Module.finrank ℚ F :=
      e₀.toRatAlgEquiv.toLinearEquiv.finrank_eq
    omega
  refine ⟨max Nχ (Ideal.absNorm (Ideal.span {(6 : 𝓞 F₀)})), fun 𝔪 h𝔪 hsmall g => ?_⟩
  have hsmallχ : SmallPrimesDvd Nχ 𝔪 := fun P hP hP0 hN =>
    hsmall P hP hP0 (hN.trans (le_max_left _ _))
  have hsmall6 : SmallPrimesDvd (Ideal.absNorm (Ideal.span {(6 : 𝓞 F₀)})) 𝔪 := fun P hP hP0 hN =>
    hsmall P hP hP0 (hN.trans (le_max_right _ _))
  have hχ := hNχ 𝔪 h𝔪 hsmallχ
  set 𝔪' := 𝔪.map eO
  have h𝔪' : 𝔪' ≠ ⊥ := fun h0 => h𝔪 ((Ideal.map_eq_bot_iff_of_injective eO.injective).1 h0)
  have hsmall' : SmallPrimesDvd (Ideal.absNorm (Ideal.span {(6 : 𝓞 F₀)})) 𝔪' :=
    C0R.smallPrimesDvd_map e hsmall6
  -- exterior primes of `F` avoid `6`
  have h6 : ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → P ⊔ Ideal.span {6} = ⊤ := by
    intro P hP hE
    have hPm : (P.map eO).IsPrime := Ideal.map_isPrime_of_equiv eO
    have hEm := C0R.isExterior_map e hE
    have hmax : (P.map eO).IsMaximal := hPm.isMaximal hEm.1
    have h1 : P.map eO ⊔ Ideal.span {(6 : 𝓞 F₀)} = ⊤ := by
      by_contra hne
      have hle : Ideal.span {(6 : 𝓞 F₀)} ≤ P.map eO :=
        le_of_eq (hmax.eq_of_le hne le_sup_left).symm |>.trans' le_sup_right
      have hN : Ideal.absNorm (P.map eO) ≤ Ideal.absNorm (Ideal.span {(6 : 𝓞 F₀)}) := by
        refine Nat.le_of_dvd (Nat.pos_of_ne_zero ?_) (Ideal.absNorm_dvd_absNorm_of_le hle)
        rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
        intro h; have := congrArg (fun x : 𝓞 F₀ => (x : F₀)) h; simp at this
      have := hsmall' _ hPm hEm.1 hN
      apply hPm.ne_top
      rw [eq_top_iff, ← hEm.2]; exact sup_le le_rfl this
    have h2 : (P ⊔ Ideal.span {6}).map eO = ⊤ := by
      rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_ofNat]; exact h1
    rw [← C0R.map_equiv_symm_map eO (P ⊔ Ideal.span {6}), h2, Ideal.map_top]
  -- exterior primes of `F₀` are principal in `R₀`
  have hprin' : ∀ v : HeightOneSpectrum (𝓞 F₀), ¬ 𝔪' ≤ v.asIdeal →
      ∃ p : SInt 𝔪', Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F₀) (SInt 𝔪')) := by
    intro v hv
    set P := v.asIdeal.map eO.symm
    have hPP : P.map eO = v.asIdeal := by
      have := C0R.map_equiv_symm_map eO.symm v.asIdeal
      rwa [RingEquiv.symm_symm] at this
    have hP : P.IsPrime := Ideal.map_isPrime_of_equiv eO.symm
    have hP0 : P ≠ ⊥ := fun h0 => v.ne_bot (by rw [← hPP, h0, Ideal.map_bot])
    have hPm : ¬ 𝔪 ≤ P := fun hle => hv (by rw [← hPP]; exact (C0R.map_equiv_le_iff eO).2 hle)
    have hE : IsExterior 𝔪 P := ⟨hP0, by
      by_contra hne
      exact hPm (le_trans le_sup_right
        (le_of_eq ((hP.isMaximal hP0).eq_of_le hne le_sup_left).symm))⟩
    refine ⟨C0R.sIntEquiv e 𝔪 (g.gen P), ?_⟩
    have := congrArg (Ideal.map (C0R.sIntEquiv e 𝔪)) (g.span_gen P hE)
    rw [Ideal.map_span, Set.image_singleton, C0R.map_map_sIntEquiv, hPP] at this
    exact this
  obtain ⟨kk, cls₀, hcore⟩ := L3F.core hζ' (ι.comp (e.symm : F₀ →+* F)) hK' 𝔪' h𝔪' hsmall'
    hprin'
  refine ⟨kk, fun I => cls₀ (e (g.gen I : F)), fun 𝔤 c₁ c₂ hext hsq hne hcl => ?_⟩
  -- exterior pieces
  obtain ⟨h𝔤c₁, hc₂⟩ := extMul'.1 hext
  obtain ⟨h𝔤, hc₁⟩ := extMul'.1 h𝔤c₁
  have hc12 : IsExterior 𝔪 (c₁ * c₂) := extMul'.2 ⟨hc₁, hc₂⟩
  have hsq12 : Squarefree (c₁ * c₂) := by
    rw [mul_assoc] at hsq; exact Squarefree.of_mul_right hsq
  -- the generators
  set u : SInt 𝔪 := g.gen c₁ * g.gen c₂ with hudef
  have hgen : Ideal.span {u} = (c₁ * c₂).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [hudef, ← Ideal.span_singleton_mul_span_singleton, g.span_gen c₁ hc₁, g.span_gen c₂ hc₂,
      Ideal.map_mul]
  obtain ⟨ε₁, hε₁⟩ := g.gen_mul 𝔤 c₁ h𝔤 hc₁
  obtain ⟨ε₂, hε₂⟩ := g.gen_mul 𝔤 c₂ h𝔤 hc₂
  have hg𝔤 : (g.gen 𝔤 : F) ≠ 0 := by
    intro h0
    have hz : g.gen 𝔤 = 0 := Subtype.ext h0
    have := g.span_gen 𝔤 h𝔤
    rw [hz, Ideal.span_singleton_eq_bot.2 rfl, eq_comm,
      Ideal.map_eq_bot_iff_of_injective] at this
    · exact h𝔤.1 this
    · intro a b hab
      have := congrArg (fun x : SInt 𝔪 => (x : F)) hab
      exact FaithfulSMul.algebraMap_injective (𝓞 F) F this
  set t : F := (((ε₁ : Fˣ) : F) * ((ε₂ : Fˣ) : F)) ^ 3 * (g.gen 𝔤 : F) with htdef
  have ht : t ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))) hg𝔤
  have hx : (g.gen (𝔤 * c₁) : F) * (g.gen (𝔤 * c₂) : F) = (u : F) * t ^ 2 := by
    rw [hε₁, hε₂, hudef, htdef]
    push_cast
    ring
  -- transport to `F₀`
  have hgen' : Ideal.span {C0R.sIntEquiv e 𝔪 u} =
      ((c₁ * c₂).map eO).map (algebraMap (𝓞 F₀) (SInt 𝔪')) := by
    have := congrArg (Ideal.map (C0R.sIntEquiv e 𝔪)) hgen
    rw [Ideal.map_span, Set.image_singleton, C0R.map_map_sIntEquiv] at this
    exact this
  have hne' : (c₁ * c₂).map eO ≠ ⊤ := by
    intro h
    apply hne
    rw [← C0R.map_equiv_symm_map eO (c₁ * c₂), h, Ideal.map_top]
  have hx' : e (g.gen (𝔤 * c₁) : F) * e (g.gen (𝔤 * c₂) : F) =
      ((C0R.sIntEquiv e 𝔪 u : SInt 𝔪') : F₀) * (e t) ^ 2 := by
    rw [C0R.sIntEquiv_coe, ← map_pow, ← map_mul, ← map_mul, hx]
  obtain ⟨Λ, hΛd, hΛre, hΛfe, hΛg⟩ := hcore (C0R.sIntEquiv e 𝔪 u) ((c₁ * c₂).map eO) _ _ (e t)
    (C0R.isExterior_map e hc12) (squarefree_map e hsq12) hne' hgen'
    (by simpa using ht) hx' hcl
  refine ⟨Λ, hΛd, fun w hw => ?_, fun w h1 h2 => ?_, hΛg⟩
  · rw [hΛre w hw, prod_factors_transport e 𝔪 h𝔪 w, ← map_pow,
      kummerL_transport' e ι 𝔪 h6 (u ^ 3) w]
    congr 1
    unfold kummerL
    refine tsum_congr fun 𝔞 => ?_
    rw [hudef, rs_cube hχ 𝔞.2]
  · have := hΛfe w h1 h2
    rwa [C0R.absNorm_map_equiv, hdiscr, hnr] at this

namespace L3F

end L3F

end ArtinPrimitiveRoots

end
end
end

section
open ArtinPrimitiveRoots

open NumberField

theorem solution
    (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ g : AllowedGen ι 𝔪, ∃ (k : ℕ) (cls : Ideal (𝓞 F) → Fin k),
        ∀ 𝔤 c₁ c₂ : Ideal (𝓞 F), IsExterior 𝔪 (𝔤 * c₁ * c₂) → Squarefree (𝔤 * c₁ * c₂) →
          c₁ * c₂ ≠ ⊤ → cls (𝔤 * c₁) = cls (𝔤 * c₂) →
          ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
            (∀ w : ℂ, 1 < w.re →
              Λ w = (∏ P ∈ (UniqueFactorizationMonoid.normalizedFactors 𝔪).toFinset,
                  (1 - (Ideal.absNorm P : ℂ) ^ (-w)))⁻¹ *
                ∑' 𝔞 : {𝔞 : Ideal (𝓞 F) // IsExterior 𝔪 𝔞},
                  residueSymbol ι 𝔪 𝔞.1 (g.gen c₁) ^ 3 * residueSymbol ι 𝔪 𝔞.1 (g.gen c₂) ^ 3 *
                    (Ideal.absNorm 𝔞.1 : ℂ) ^ (-w)) ∧
            (∀ w : ℂ, (∀ m : ℕ, w ≠ -(m : ℂ)) → (∀ m : ℕ, 1 - w ≠ -(m : ℂ)) →
              (((|discr F| : ℤ) : ℂ) * (Ideal.absNorm (c₁ * c₂) : ℂ)) ^ (w / 2) *
                  Complex.Gammaℂ w ^ InfinitePlace.nrComplexPlaces F * Λ w =
                (((|discr F| : ℤ) : ℂ) * (Ideal.absNorm (c₁ * c₂) : ℂ)) ^ ((1 - w) / 2) *
                  Complex.Gammaℂ (1 - w) ^ InfinitePlace.nrComplexPlaces F * Λ (1 - w)) ∧
            (∀ σ₁ σ₂ : ℝ, ∃ C A : ℝ, ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ →
              ‖Λ w‖ ≤ C * (1 + |w.im|) ^ A) := by
  exact ArtinPrimitiveRoots.exists_cutoff_exists_cls_exists_differentiable_eq_tsum_residueSymbol_pow_three_and_functionalEquation n hn0 hn F ι

end
