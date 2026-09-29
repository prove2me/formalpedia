-- Prove2me | Definitions.Def_LanglandsTunnell_ArtinCoreCTM
-- name    : LanglandsTunnell_ArtinCoreCTM
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/12005a2a-8ec8-5904-a981-a1aa67765872
-- title:
--   Ray-class vocabulary: relative norms, admissible moduli, adelic content
-- statement:
--   For number fields $k \subseteq E$ the module first sets up the ideal-theoretic relative norm on the coprime-to-modulus groups. Here `coprimeToModulus K 𝔣` is the subgroup of units of the group of fractional ideals of $K$ whose $v$-adic count vanishes at every $v \mid \mathfrak f$. `placeUnder'` sends a height-one prime $w$ of $\mathcal O_E$ to the prime below it, `modulusExt k E 𝔠` is the extended ideal $\mathfrak c\mathcal O_E$, and `fracRelNormUnit` is the ray symbol attached to $w \mapsto \mathfrak p_w^{\,f(w/\mathfrak p_w)}$, i.e. the multiplicative map sending a fractional ideal of $E$ to the product of $\mathfrak p_w^{f\cdot \mathrm{ord}_w}$; `relNormCTM` is its restriction to a homomorphism $\mathrm{coprimeToModulus}\,E\,(\mathfrak c\mathcal O_E) \to \mathrm{coprimeToModulus}\,k\,\mathfrak c$. Adelically, `placeOrd` is the $v$-order of a finite idelic unit (minus the logarithm of its value), `fadContentHom` the induced content homomorphism to fractional-ideal units, `projFin` the projection of an adelic unit to its finite part, and `placeOf`/`archRealProjTau`/`archSign` record, for a real embedding $\tau$, the sign of the component of an adelic unit at the corresponding real place. The predicate `IsAdjuster 𝔣 u α` asserts that the finite part of $u\alpha^{-1}$ has valuation $1$ at every $v \mid \mathfrak f$ and is congruent to $1$ there with precision $\exp(-n_v)$, $n_v$ the multiplicity of $v$ in $\mathfrak f$, and that $u\alpha^{-1}$ is positive at every real embedding; `unitIdeles K 𝔣` is the subgroup of adelic units satisfying these conditions outright. On the Galois side, `resHom` composes restriction of scalars with restriction to a normal subextension; `admissibleExp K v` $= 4e_v(2)+2e_v(3)+1$ and `IsAdmissibleModulus K L 𝔣` requires $\mathfrak f \neq 0$ together with $v^{\mathrm{admissibleExp}} \mid \mathfrak f$ at every $v$ with nontrivial inertia in $\mathrm{Gal}(L/K)$. `normRaySubgroup` is the join of the narrow ray subgroup with the image of `relNormCTM`, and `FirstInequalityCTM`/`SecondInequalityCTM` are the two divisibilities between $\#\mathrm{Gal}(L/K)$ and the index of that subgroup. `primeCarrier`/`primeCarriers` name the classes of primes coprime to the modulus, `coprimeToModulus_antitone`/`ctmInclusion` the monotonicity in the modulus. Finally `ArtinFieldCore` packages, for a prime carrier $i$, an auxiliary tower $E \subseteq N$, $E \subseteq \Theta = E(\zeta_q)$ with a multiple $\mathfrak m$ of $\mathfrak f$, a prime $v \nmid \mathfrak m$ representing $i$, a prime $w$ of $E$ above $v$ of residue degree $1$, admissibility and unramifiedness conditions away from $\mathfrak m\mathcal O_E$, and injectivity of `resHom`, with derived data `Ip`, `Ni`, `ωpi`, `Pi`; `ArtinPairCore` does the same for two cores and a prescribed $\sigma$, carrying as a field the compatibility of the Artin symbol of $L/K$ with the relative norm. `IdeleFirstIneqData` and `IdeleFirstIneqDataAt` assert the existence of an adelic norm homomorphism compatible with adjusters and with content, surjecting onto `unitIdeles` for admissible moduli, and whose image together with the principal ideles has index divisible by the degree.
--
--   **Relation to Mathlib.** Mathlib supplies the adele and finite adele rings, fractional ideals with their $v$-adic counts, infinite places and the arithmetic Frobenius; the ray-class layer used here (coprime-to-modulus and narrow ray subgroups, ray symbols, admissible moduli, the adelic content and adjuster predicates) is the project's own.
--
--   **Where it is used.** This is the class-field-theoretic vocabulary for the Langlands–Tunnell input to the proof: the two inequality predicates and the Artin-symbol cores are the data from which global reciprocity for abelian extensions of number fields is assembled, and that reciprocity underlies the construction of the Hecke characters used in Langlands–Tunnell, hence the modularity of the mod $3$ representation attached to a Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_ArtinCoreCTM.lean

import Definitions.Def_LanglandsTunnell_ArtinFrobenius
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open Deep.NTSupply NumberField IsDedekindDomain WithZero
open scoped nonZeroDivisors IsMulCommutative Pointwise

namespace HeckeCharacter

section RelNorm

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

def placeUnder' (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 k) :=
  ⟨w.asIdeal.under (𝓞 k), inferInstance,
    fun h => w.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)⟩

omit [NumberField k] [NumberField E] in
theorem placeUnder'_asIdeal (w : HeightOneSpectrum (𝓞 E)) :
    (placeUnder' k E w).asIdeal = w.asIdeal.under (𝓞 k) := rfl

abbrev modulusExt (𝔠 : Ideal (𝓞 k)) : Ideal (𝓞 E) := 𝔠.map (algebraMap (𝓞 k) (𝓞 E))

def fracRelNormUnit : (FractionalIdeal ((𝓞 E)⁰) E)ˣ →* (FractionalIdeal ((𝓞 k)⁰) k)ˣ :=
  raySymbolUnitsHom E (fun w =>
    primeUnit k (placeUnder' k E w) ^ ((placeUnder' k E w).asIdeal.inertiaDeg' w.asIdeal))

theorem placeUnder'_dvd_iff (𝔠 : Ideal (𝓞 k)) (w : HeightOneSpectrum (𝓞 E)) :
    (placeUnder' k E w).asIdeal ∣ 𝔠 ↔ w.asIdeal ∣ modulusExt k E 𝔠 := by
  rw [placeUnder'_asIdeal, modulusExt, Ideal.dvd_iff_le, Ideal.dvd_iff_le,
    Ideal.map_le_iff_le_comap]

def gcopNC2 (𝔠 : Ideal (𝓞 k)) (w : HeightOneSpectrum (𝓞 E)) : ↥(coprimeToModulus k 𝔠) := by
  classical
  exact if h : ¬ (placeUnder' k E w).asIdeal ∣ 𝔠
    then ⟨primeUnit k (placeUnder' k E w) ^ ((placeUnder' k E w).asIdeal.inertiaDeg' w.asIdeal),
      pow_mem (primeUnit_mem_coprimeToModulus k h) _⟩
    else 1

theorem coe_raySymbol_gcop_eq_fracRelNormUnit' {𝔠 : Ideal (𝓞 k)}
    (Y : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) (hY : Y ∈ coprimeToModulus E (modulusExt k E 𝔠)) :
    ((raySymbol E (gcopNC2 k E 𝔠) (Y : FractionalIdeal ((𝓞 E)⁰) E)
      : ↥(coprimeToModulus k 𝔠)) : (FractionalIdeal ((𝓞 k)⁰) k)ˣ)
      = fracRelNormUnit k E Y := by
  unfold raySymbol
  refine (MonoidHom.map_finprod ((coprimeToModulus k 𝔠).subtype)
    (hasFiniteMulSupport_raySymbol_factors E (gcopNC2 k E 𝔠) _)).trans ?_
  rw [show fracRelNormUnit k E Y
      = ∏ᶠ w, (primeUnit k (placeUnder' k E w)
            ^ ((placeUnder' k E w).asIdeal.inertiaDeg' w.asIdeal))
          ^ FractionalIdeal.count E w (Y : FractionalIdeal ((𝓞 E)⁰) E) from rfl]
  refine finprod_congr (fun w => ?_)
  rw [map_zpow, Subgroup.coe_subtype]
  classical
  by_cases hw : (placeUnder' k E w).asIdeal ∣ 𝔠
  · have hct : FractionalIdeal.count E w (Y : FractionalIdeal ((𝓞 E)⁰) E) = 0 :=
      (mem_coprimeToModulus_iff E).mp hY w ((placeUnder'_dvd_iff k E 𝔠 w).mp hw)
    rw [hct]; simp
  · simp only [gcopNC2]; rw [dif_pos hw]

theorem fracRelNormUnit_mem_coprimeToModulus {𝔠 : Ideal (𝓞 k)}
    {Y : (FractionalIdeal ((𝓞 E)⁰) E)ˣ} (hY : Y ∈ coprimeToModulus E (modulusExt k E 𝔠)) :
    fracRelNormUnit k E Y ∈ coprimeToModulus k 𝔠 :=
  coe_raySymbol_gcop_eq_fracRelNormUnit' k E Y hY ▸ (raySymbol E (gcopNC2 k E 𝔠) _).2

def relNormCTM (𝔠 : Ideal (𝓞 k)) :
    ↥(coprimeToModulus E (modulusExt k E 𝔠)) →* ↥(coprimeToModulus k 𝔠) :=
  ((fracRelNormUnit k E).comp (coprimeToModulus E (modulusExt k E 𝔠)).subtype).codRestrict
    (coprimeToModulus k 𝔠) (fun Y => fracRelNormUnit_mem_coprimeToModulus k E Y.2)

end RelNorm

section Content

variable (K : Type*) [Field K] [NumberField K]

theorem fad_one_apply (v : HeightOneSpectrum (𝓞 K)) :
    ((1 : FiniteAdeleRing (𝓞 K) K) v : v.adicCompletion K) = 1 := rfl

theorem fad_mul_apply (a b : FiniteAdeleRing (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) :
    ((a * b : FiniteAdeleRing (𝓞 K) K) v : v.adicCompletion K) = a v * b v := rfl

def placeOrd (u : (FiniteAdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) : ℤ :=
  -WithZero.log (Valued.v ((u : FiniteAdeleRing (𝓞 K) K) v))

theorem placeOrd_one (v : HeightOneSpectrum (𝓞 K)) : placeOrd K 1 v = 0 := by
  unfold placeOrd
  rw [Units.val_one, fad_one_apply, map_one, WithZero.log_one, neg_zero]

theorem valued_ne_zero_of_unit (u : (FiniteAdeleRing (𝓞 K) K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((u : FiniteAdeleRing (𝓞 K) K) v) ≠ 0 := by
  rw [ne_eq, map_eq_zero]
  exact ((FiniteAdeleRing.isUnit_iff.mp u.isUnit).1 v)

theorem placeOrd_mul (u u' : (FiniteAdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    placeOrd K (u * u') v = placeOrd K u v + placeOrd K u' v := by
  unfold placeOrd
  rw [Units.val_mul, fad_mul_apply, map_mul,
    WithZero.log_mul (valued_ne_zero_of_unit K u v) (valued_ne_zero_of_unit K u' v),
    neg_add]

theorem placeOrd_eq_zero_iff (u : (FiniteAdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    placeOrd K u v = 0 ↔ Valued.v ((u : FiniteAdeleRing (𝓞 K) K) v) = 1 := by
  unfold placeOrd
  rw [neg_eq_zero]
  constructor
  · intro hlog
    have h := WithZero.exp_log (x := Valued.v ((u : FiniteAdeleRing (𝓞 K) K) v))
      (valued_ne_zero_of_unit K u v)
    rw [hlog, WithZero.exp_zero] at h
    exact h.symm
  · intro h; rw [h, WithZero.log_one]

theorem finite_support_placeOrd (u : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    (Function.support (placeOrd K u)).Finite := by
  have h := FiniteAdeleRing.unitsEquiv_finite_valued_eq_one (R := 𝓞 K) (K := K) u
  rw [Filter.eventually_cofinite] at h
  refine h.subset fun v hv => ?_
  rw [Function.mem_support] at hv
  rw [Set.mem_setOf_eq]
  intro hval
  exact hv ((placeOrd_eq_zero_iff K u v).mpr (by
    set_option backward.isDefEq.respectTransparency false in
    simpa [RestrictedProduct.unitsEquiv_apply] using hval))

def fadContentHom : (FiniteAdeleRing (𝓞 K) K)ˣ →* (FractionalIdeal ((𝓞 K)⁰) K)ˣ where
  toFun u := ∏ᶠ v : HeightOneSpectrum (𝓞 K), (primeUnit K v) ^ (placeOrd K u v)
  map_one' := by simp [placeOrd_one]
  map_mul' u u' := by
    simp only [placeOrd_mul, zpow_add]
    exact finprod_mul_distrib
      ((finite_support_placeOrd K u).subset fun v hv => by
        simp only [Function.mem_mulSupport, ne_eq] at hv ⊢
        contrapose! hv; rw [Function.mem_support, not_not] at hv; simp [hv])
      ((finite_support_placeOrd K u').subset fun v hv => by
        simp only [Function.mem_mulSupport, ne_eq] at hv ⊢
        contrapose! hv; rw [Function.mem_support, not_not] at hv; simp [hv])

def projFin : (AdeleRing (𝓞 K) K)ˣ →* (FiniteAdeleRing (𝓞 K) K)ˣ :=
  (MonoidHom.snd (InfiniteAdeleRing K)ˣ (FiniteAdeleRing (𝓞 K) K)ˣ).comp
    MulEquiv.prodUnits.toMonoidHom

noncomputable def placeOf (τ : K →+* ℝ) : InfinitePlace K :=
  InfinitePlace.mk (Complex.ofRealHom.comp τ)

omit [NumberField K] in

theorem isReal_compOfRealHom (τ : K →+* ℝ) :
    ComplexEmbedding.IsReal (Complex.ofRealHom.comp τ) :=
  RingHom.ext fun x => Complex.conj_ofReal (τ x)

omit [NumberField K] in
theorem isReal_placeOf (τ : K →+* ℝ) : (placeOf K τ).IsReal :=
  ⟨_, isReal_compOfRealHom K τ, rfl⟩

open InfinitePlace.Completion in

noncomputable def archRealProjTau (τ : K →+* ℝ) (u : (AdeleRing (𝓞 K) K)ˣ) : ℝ :=
  ringEquivRealOfIsReal (isReal_placeOf K τ)
    (((u : AdeleRing (𝓞 K) K).1 : InfiniteAdeleRing K) (placeOf K τ))

open InfinitePlace.Completion in
theorem archRealProjTau_mul (τ : K →+* ℝ) (u u' : (AdeleRing (𝓞 K) K)ˣ) :
    archRealProjTau K τ (u * u') = archRealProjTau K τ u * archRealProjTau K τ u' := by
  unfold archRealProjTau
  rw [← map_mul]; rfl

open InfinitePlace.Completion in
theorem archRealProjTau_ne_zero (τ : K →+* ℝ) (u : (AdeleRing (𝓞 K) K)ˣ) :
    archRealProjTau K τ u ≠ 0 := by
  intro h
  have h1 : archRealProjTau K τ u * archRealProjTau K τ u⁻¹ = 1 := by
    rw [← archRealProjTau_mul, mul_inv_cancel]
    unfold archRealProjTau; rw [Units.val_one]
    exact (congrArg (ringEquivRealOfIsReal (isReal_placeOf K τ)) rfl).trans (map_one _)
  rw [h, zero_mul] at h1; exact zero_ne_one h1

def archSign (τ : K →+* ℝ) (u : (AdeleRing (𝓞 K) K)ˣ) : Prop :=
  0 < archRealProjTau K τ u

open InfinitePlace.Completion in

theorem archSign_of_fst_eq_one (τ : K →+* ℝ) {u : (AdeleRing (𝓞 K) K)ˣ}
    (huarch : (u : AdeleRing (𝓞 K) K).1 = 1) : archSign K τ u := by
  show (0:ℝ) < ringEquivRealOfIsReal (isReal_placeOf K τ) _
  rw [huarch, show ((1 : InfiniteAdeleRing K) (placeOf K τ)) = 1 from rfl, map_one]
  exact one_pos

theorem archSign_mul (τ : K →+* ℝ) (u u' : (AdeleRing (𝓞 K) K)ˣ) :
    archSign K τ (u * u') ↔ (archSign K τ u ↔ archSign K τ u') := by
  unfold archSign; rw [archRealProjTau_mul]
  constructor
  · intro hmul
    rcases mul_pos_iff.mp hmul with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact iff_of_true h1 h2
    · exact iff_of_false h1.not_gt h2.not_gt
  · intro hiff
    rcases (archRealProjTau_ne_zero K τ u).lt_or_gt with h1 | h1
    · have h2 := (not_iff_not.mpr hiff).mp h1.not_gt
      exact mul_pos_of_neg_of_neg h1 ((archRealProjTau_ne_zero K τ u').lt_or_gt.resolve_right h2)
    · exact mul_pos h1 (hiff.mp h1)

theorem archSign_one (τ : K →+* ℝ) : archSign K τ 1 :=
  archSign_of_fst_eq_one K τ rfl

theorem archSign_inv (τ : K →+* ℝ) (u : (AdeleRing (𝓞 K) K)ˣ) :
    archSign K τ u⁻¹ ↔ archSign K τ u := by
  have h := archSign_mul K τ u u⁻¹
  rw [mul_inv_cancel, iff_true_intro (archSign_one K τ), true_iff] at h
  exact h.symm

theorem unit_cong_mul {v : HeightOneSpectrum (𝓞 K)} {ε : ℤᵐ⁰} {a b : v.adicCompletion K}
    (hva : Valued.v a = 1) (hca : Valued.v (a - 1) ≤ ε)
    (hvb : Valued.v b = 1) (hcb : Valued.v (b - 1) ≤ ε) :
    Valued.v (a * b) = 1 ∧ Valued.v (a * b - 1) ≤ ε := by
  refine ⟨by rw [map_mul, hva, hvb, one_mul], ?_⟩
  have heq : a * b - 1 = a * (b - 1) + (a - 1) := by ring
  calc Valued.v (a * b - 1) = Valued.v (a * (b - 1) + (a - 1)) := by rw [heq]
    _ ≤ max (Valued.v (a * (b - 1))) (Valued.v (a - 1)) := Valuation.map_add _ _ _
    _ ≤ ε := by
        rw [map_mul, hva, one_mul]
        exact max_le hcb hca

theorem unit_cong_div {v : HeightOneSpectrum (𝓞 K)} {ε : ℤᵐ⁰} {a b : v.adicCompletion K}
    (hca : Valued.v (a - 1) ≤ ε)
    (hvb : Valued.v b = 1) (hcb : Valued.v (b - 1) ≤ ε) :
    Valued.v (a * b⁻¹ - 1) ≤ ε := by
  have hb0 : b ≠ 0 := fun h => by simp [h] at hvb
  have heq : a * b⁻¹ - 1 = (a - b) * b⁻¹ := by field_simp
  rw [heq, map_mul, map_inv₀, hvb, inv_one, mul_one]
  calc Valued.v (a - b) = Valued.v ((a - 1) - (b - 1)) := by ring_nf
    _ ≤ max (Valued.v (a - 1)) (Valued.v (b - 1)) := Valuation.map_sub _ _ _
    _ ≤ ε := max_le hca hcb

theorem fad_units_inv_apply (X : (FiniteAdeleRing (𝓞 K) K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    (((X⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v)
      = (((X : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← fad_mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, fad_one_apply]

structure IsAdjuster (𝔣 : Ideal (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ) (α : Kˣ) : Prop where
  cong : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
    Valued.v ((((u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ :
        (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = 1 ∧
    Valued.v ((((u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ :
        (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v - 1)
      ≤ WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors : ℤ))
  sign : ∀ τ : K →+* ℝ,
    archSign K τ (u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹)

end Content

end HeckeCharacter

namespace LanglandsTunnell.P2.Artin

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter WithZero

section Carriers

variable (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K))

def primeCarrier (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣) : ↥(coprimeToModulus K 𝔣) :=
  ⟨primeUnit K v, primeUnit_mem_coprimeToModulus K hv⟩

def primeCarriers : Set ↥(coprimeToModulus K 𝔣) :=
  {x | ∃ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣), x = primeCarrier K 𝔣 v hv}

end Carriers

section Inclusion

variable (K : Type*) [Field K] [NumberField K]

theorem coprimeToModulus_antitone {𝔣 𝔪 : Ideal (𝓞 K)} (h : 𝔣 ∣ 𝔪) : coprimeToModulus K 𝔪 ≤ coprimeToModulus K 𝔣 :=
  fun _ hx v hv => hx v (dvd_trans hv h)

noncomputable def ctmInclusion {𝔣 𝔪 : Ideal (𝓞 K)} (h : 𝔣 ∣ 𝔪) : ↥(coprimeToModulus K 𝔪) →* ↥(coprimeToModulus K 𝔣) :=
  Subgroup.inclusion (coprimeToModulus_antitone K h)

end Inclusion

section Tower

variable (K M E N : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Field E]
  [NumberField E] [Field N] [NumberField N]
  [Algebra K M] [Algebra K E] [Algebra K N] [Algebra M N] [Algebra E N] [IsScalarTower K M N]
  [IsScalarTower K E N] [IsGalois K M] [IsGalois E N]

def resHom : (N ≃ₐ[E] N) →* (M ≃ₐ[K] M) :=
  (AlgEquiv.restrictNormalHom M).comp
    { toFun := fun σ => σ.restrictScalars K
      map_one' := AlgEquiv.ext fun _ => rfl
      map_mul' := fun _ _ => AlgEquiv.ext fun _ => rfl }

end Tower

section Admissible

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

def admissibleExp (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  4 * Ideal.ramificationIdx' (Ideal.span {(2 : ℤ)}) v.asIdeal + 2 * Ideal.ramificationIdx' (Ideal.span {(3 : ℤ)}) v.asIdeal + 1

def IsAdmissibleModulus (𝔣 : Ideal (𝓞 K)) : Prop :=
  𝔣 ≠ ⊥ ∧ ∀ v : HeightOneSpectrum (𝓞 K), (primeAbove K L v).inertia (L ≃ₐ[K] L) ≠ ⊥ → v.asIdeal ^ admissibleExp K v ∣ 𝔣

end Admissible

section DefN

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def normRaySubgroup (𝔣 : Ideal (𝓞 K)) : Subgroup ↥(coprimeToModulus K 𝔣) :=
  (narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣)
    ⊔ (HeckeCharacter.relNormCTM K L 𝔣).range

end DefN

section Pincer

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

def SecondInequalityCTM (𝔣 : Ideal (𝓞 K)) : Prop :=
  (normRaySubgroup K L 𝔣).index ∣ Nat.card (L ≃ₐ[K] L)

def FirstInequalityCTM (𝔣 : Ideal (𝓞 K)) : Prop :=
  Nat.card (L ≃ₐ[K] L) ∣ (normRaySubgroup K L 𝔣).index

end Pincer

section UnitIdeles

variable (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K))

def unitIdeles : Subgroup (AdeleRing (𝓞 K) K)ˣ where
  carrier := {u | (∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((projFin K u : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v) = 1) ∧
    (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      Valued.v (((projFin K u : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v - 1) ≤ exp (-((Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors : ℤ))) ∧
    ∀ τ : K →+* ℝ, archSign K τ u}
  one_mem' := ⟨fun v => by rw [map_one, Units.val_one, fad_one_apply, map_one],
    fun v _ => by rw [map_one, Units.val_one, fad_one_apply, sub_self, map_zero]; exact zero_le', fun τ => archSign_one K τ⟩
  mul_mem' {u u'} hu hu' := by
    refine ⟨fun v => ?_, fun v hv => ?_, fun τ => (archSign_mul K τ u u').mpr (iff_of_true (hu.2.2 τ) (hu'.2.2 τ))⟩
    · rw [map_mul, Units.val_mul, fad_mul_apply, map_mul, hu.1 v, hu'.1 v, one_mul]
    · rw [map_mul, Units.val_mul, fad_mul_apply]
      exact (unit_cong_mul K (hu.1 v) (hu.2.1 v hv) (hu'.1 v) (hu'.2.1 v hv)).2
  inv_mem' {u} hu := by
    refine ⟨fun v => ?_, fun v hv => ?_, fun τ => (archSign_inv K τ u).mpr (hu.2.2 τ)⟩
    · rw [map_inv, fad_units_inv_apply, map_inv₀, hu.1 v, inv_one]
    · rw [map_inv, fad_units_inv_apply]
      have h := unit_cong_div K (a := (1 : v.adicCompletion K)) (by rw [sub_self, map_zero]; exact zero_le') (hu.1 v) (hu.2.1 v hv)
      rwa [one_mul] at h

end UnitIdeles

structure ArtinFieldCore (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (𝔣 : Ideal (𝓞 K)) (i : ↥(primeCarriers K 𝔣)) where
  E : Type*
  N : Type*
  Θ : Type*
  [instFE : Field E]
  [instNFE : NumberField E]
  [instFN : Field N]
  [instNFN : NumberField N]
  [instFΘ : Field Θ]
  [instNFΘ : NumberField Θ]
  [instAKE : Algebra K E]
  [instAKN : Algebra K N]
  [instAEN : Algebra E N]
  [instALN : Algebra L N]
  [instAEΘ : Algebra E Θ]
  [instANΘ : Algebra N Θ]
  [instSTKEN : IsScalarTower K E N]
  [instSTKLN : IsScalarTower K L N]
  [instSTENΘ : IsScalarTower E N Θ]
  [instGEN : IsGalois E N]
  [instGEΘ : IsGalois E Θ]
  [instCN : IsMulCommutative (N ≃ₐ[E] N)]
  [instCΘ : IsMulCommutative (Θ ≃ₐ[E] Θ)]
  𝔪 : Ideal (𝓞 K)
  h𝔪 : 𝔣 ∣ 𝔪
  v : HeightOneSpectrum (𝓞 K)
  hv𝔪 : ¬ v.asIdeal ∣ 𝔪
  hvi : primeCarrier K 𝔣 v (fun hv => hv𝔪 (dvd_trans hv h𝔪)) = (i : ↥(coprimeToModulus K 𝔣))
  w : HeightOneSpectrum (𝓞 E)
  hw : ¬ w.asIdeal ∣ modulusExt K E 𝔪
  hwv : w.asIdeal.under (𝓞 K) = v.asIdeal
  hf : v.asIdeal.inertiaDeg' w.asIdeal = 1
  q : ℕ
  [instNZq : NeZero q]
  ζ : Θ
  hζ : IsPrimitiveRoot ζ q
  htop : (IntermediateField.adjoin E {ζ} : IntermediateField E Θ) = ⊤
  hq𝔪 : Ideal.span {(q : 𝓞 E)} ∣ modulusExt K E 𝔪
  hunr : ∀ v' : HeightOneSpectrum (𝓞 E), ¬ v'.asIdeal ∣ modulusExt K E 𝔪 →
    ((primeAbove E Θ v').under (𝓞 N)).inertia (N ≃ₐ[E] N) = ⊥
  hadm : IsAdmissibleModulus E N (modulusExt K E 𝔪)
  hI_E : ∀ w' : HeightOneSpectrum (𝓞 E), ¬ w'.asIdeal ∣ modulusExt K E 𝔪 →
    ((primeAbove E N w').under (𝓞 L)).inertia (L ≃ₐ[K] L) = ⊥
  hresInj : Function.Injective (resHom K L E N)

attribute [instance] ArtinFieldCore.instFE ArtinFieldCore.instNFE ArtinFieldCore.instFN
  ArtinFieldCore.instNFN ArtinFieldCore.instFΘ ArtinFieldCore.instNFΘ ArtinFieldCore.instAKE
  ArtinFieldCore.instAKN ArtinFieldCore.instAEN ArtinFieldCore.instALN ArtinFieldCore.instAEΘ
  ArtinFieldCore.instANΘ ArtinFieldCore.instSTKEN ArtinFieldCore.instSTKLN
  ArtinFieldCore.instSTENΘ ArtinFieldCore.instGEN ArtinFieldCore.instGEΘ ArtinFieldCore.instCN
  ArtinFieldCore.instCΘ ArtinFieldCore.instNZq

section PerICore

set_option maxSynthPendingDepth 3

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] {𝔣 : Ideal (𝓞 K)} {i : ↥(primeCarriers K 𝔣)}
  (c : ArtinFieldCore K L 𝔣 i)

def ArtinFieldCore.Ip : Type _ := ↥(coprimeToModulus c.E (modulusExt K c.E c.𝔪))

instance : CommGroup c.Ip := inferInstanceAs (CommGroup ↥(coprimeToModulus c.E (modulusExt K c.E c.𝔪)))

def ArtinFieldCore.Ni : c.Ip →* ↥(coprimeToModulus K 𝔣) :=
  (ctmInclusion K c.h𝔪).comp (relNormCTM K c.E c.𝔪)

def ArtinFieldCore.ωpi : c.Ip →* (L ≃ₐ[K] L) :=
  (resHom K L c.E c.N).comp (artinSymbol c.E c.N (modulusExt K c.E c.𝔪))

def ArtinFieldCore.Pi : c.Ip := ⟨primeUnit c.E c.w, primeUnit_mem_coprimeToModulus c.E c.hw⟩

end PerICore

structure ArtinPairCore (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (𝔣 : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L) {i j : ↥(primeCarriers K 𝔣)}
    (ci : ArtinFieldCore K L 𝔣 i) (cj : ArtinFieldCore K L 𝔣 j) where
  E'' : Type*
  N'' : Type*
  [instFE : Field E'']
  [instNFE : NumberField E'']
  [instFN : Field N'']
  [instNFN : NumberField N'']
  [instAKE : Algebra K E'']
  [instAKN : Algebra K N'']
  [instAiE : Algebra ci.E E'']
  [instAjE : Algebra cj.E E'']
  [instSTKiE : IsScalarTower K ci.E E'']
  [instSTKjE : IsScalarTower K cj.E E'']
  [instAEN : Algebra E'' N'']
  [instALN : Algebra L N'']
  [instSTKEN : IsScalarTower K E'' N'']
  [instSTKLN : IsScalarTower K L N'']
  [instGEN : IsGalois E'' N'']
  [instCN : IsMulCommutative (N'' ≃ₐ[E''] N'')]
  𝔪'' : Ideal (𝓞 K)
  h'' : 𝔣 ∣ 𝔪''
  hi'' : ci.𝔪 ∣ 𝔪''
  hj'' : cj.𝔪 ∣ 𝔪''
  hadm'' : IsAdmissibleModulus E'' N'' (modulusExt K E'' 𝔪'')
  hcompat'' : ∀ B : ↥(coprimeToModulus E'' (modulusExt K E'' 𝔪'')),
    artinSymbol K L 𝔣 (ctmInclusion K h'' (relNormCTM K E'' 𝔪'' B))
      = resHom K L E'' N'' (artinSymbol E'' N'' (modulusExt K E'' 𝔪'') B)
  hσ'' : σ ∈ (resHom K L E'' N'').range
  hresInj'' : Function.Injective (resHom K L E'' N'')

attribute [instance] ArtinPairCore.instFE ArtinPairCore.instNFE ArtinPairCore.instFN ArtinPairCore.instNFN
  ArtinPairCore.instAKE ArtinPairCore.instAKN ArtinPairCore.instAiE ArtinPairCore.instAjE ArtinPairCore.instSTKiE
  ArtinPairCore.instSTKjE ArtinPairCore.instAEN ArtinPairCore.instALN ArtinPairCore.instSTKEN ArtinPairCore.instSTKLN
  ArtinPairCore.instGEN ArtinPairCore.instCN

section IdeleData

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M] [IsMulCommutative (M ≃ₐ[K] M)]

def IdeleFirstIneqData (F : IntermediateField K M) (𝔣 : Ideal (𝓞 K)) : Prop :=
  ∃ Nrm : (AdeleRing (𝓞 F) F)ˣ →* (AdeleRing (𝓞 K) K)ˣ,
    (∀ {u : (AdeleRing (𝓞 F) F)ˣ} {α : (F)ˣ},
      IsAdjuster F (modulusExt K F 𝔣) u α → IsAdjuster K 𝔣 (Nrm u) (Units.map (Algebra.norm K) α)) ∧
    (∀ u : (AdeleRing (𝓞 F) F)ˣ,
      fadContentHom K (projFin K (Nrm u)) = fracRelNormUnit K F (fadContentHom F (projFin F u))) ∧
    (IsAdmissibleModulus K F 𝔣 → unitIdeles K 𝔣 ≤ Nrm.range) ∧
    Module.finrank K F ∣ (M4aHerbrand.principalIdeles (𝓞 K) K ⊔ Nrm.range).index

end IdeleData

section IdeleDataTop

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

def IdeleFirstIneqDataAt (𝔣 : Ideal (𝓞 K)) : Prop :=
  ∃ Nrm : (AdeleRing (𝓞 M) M)ˣ →* (AdeleRing (𝓞 K) K)ˣ,
    (∀ {u : (AdeleRing (𝓞 M) M)ˣ} {α : Mˣ},
      IsAdjuster M (modulusExt K M 𝔣) u α → IsAdjuster K 𝔣 (Nrm u) (Units.map (Algebra.norm K) α)) ∧
    (∀ u : (AdeleRing (𝓞 M) M)ˣ,
      fadContentHom K (projFin K (Nrm u)) = fracRelNormUnit K M (fadContentHom M (projFin M u))) ∧
    (IsAdmissibleModulus K M 𝔣 → unitIdeles K 𝔣 ≤ Nrm.range) ∧
    Module.finrank K M ∣ (M4aHerbrand.principalIdeles (𝓞 K) K ⊔ Nrm.range).index

end IdeleDataTop

end LanglandsTunnell.P2.Artin


