-- Prove2me | Definitions.Def_ModularCurve_FrobeniusModL
-- name    : ModularCurve_FrobeniusModL
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/10e2d725-6f07-5e42-9499-c74970d35336
-- title:
--   Frobenius endomorphism of modular function fields in characteristic ℓ
-- statement:
--   Throughout, $K$ is a field of characteristic a prime $\ell$, $N$ a natural number, and $\bar F_N =$ `modularFunctionFieldFullC K N` is the intermediate field of $K((q))$ obtained by adjoining to $K$ the substituted $j$-expansions $\bar j(q^{d})$ for the nonzero divisors $d$ of $N$, where $\bar j =$ `jqModC K` is $q^{-1}$ times the power series $jNum$ with coefficients cast into $K$, and $x \mapsto x(q^{d})$ is the ring endomorphism `qExpand K d` of $K((q))$.
--
--   The analytic input is that in characteristic $p$ prime one has $s(q)^{p} = (\varphi s)(q^{p})$ for every Laurent series $s$, $\varphi$ being the coefficientwise Frobenius (`pow_char_eq_coeffMap_frobenius_qExpand`, proved from the compatibility of `qExpand` with `PowerSeries.expand` and the single/power-series factorisation of a Laurent series); since $\bar j$ has integral coefficients this yields $\bar j(q^{d\ell}) = \bar j(q^{d})^{\ell}$, hence $\bar F_N$ is stable under $q \mapsto q^{\ell}$. The resulting injective $K$-algebra endomorphism of $\bar F_N$ is `frobeniusModL`; every element of $\bar F_N$ has its $\ell$-th power in the image, so the endomorphism is integral, each $x$ being a root of $X^{\ell} - y$ with $\mathrm{Frob}(y) = x^{\ell}$.
--
--   Along this integral map the module then forms: the restricted place `frobeniusPlaceModL` (valuation ring the preimage of $\mathcal O_w$), the inertia-weighted pushforward and ramification-weighted pullback of divisors (the latter under `HasPrincipalDivisors`), degree invariance of the pushforward, their restrictions to degree-zero divisors, and the induced endomorphisms of $J_0(N)_K := \mathrm{Pic}^{0}(\bar F_N/K)$. The predicate `FrobeniusInputsModL` packages the hypotheses needed for this: existence of principal divisors for $\bar F_N/K$, module-finiteness of $\bar F_N$ over itself along Frobenius, the fundamental identity $\sum_{w \mapsto v} e(w)\deg(w) = [\,\cdot\,]\deg v$, and the norm formula for the pushforward of principal divisors. Finally `frobeniusPushforwardModL` and `frobeniusPullbackModL` are defined to be the corresponding maps on $J_0(N)_K$ when this predicate holds and the zero map otherwise, with lemmas identifying them in both cases and computing them on divisor classes.
--
--   **Relation to Mathlib.** The substitution $q \mapsto q^{p}$ and its interaction with Frobenius rest on Mathlib's `PowerSeries.expand`, `frobenius` and `MvPowerSeries.map_frobenius_expand`; the framework of places, divisors, $\mathrm{Pic}^{0}$ of a function field and of pushforward/pullback along an algebra map is the project's own, as is the Frobenius endomorphism of a modular function field.
--
--   **Where it is used.** These definitions provide the geometric Frobenius on the level-$N$ modular function field in characteristic $\ell$ and the induced correspondence on $\mathrm{Pic}^{0}$, the ingredients from which the Eichler–Shimura relation and hence the description of the Galois action on torsion of $J_0(N)$ in characteristic $\ell$ are obtained.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_FrobeniusModL.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_pow_char_eq_qExpand_of_coeff_fixed
import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open HahnSeries IntermediateField AlgebraicCurve Polynomial

namespace ModularCurve

section ExpandSeam

variable {R : Type*} [CommRing R] (p : ℕ) [NeZero p]

theorem qExpand_ofPowerSeries_eq_expand (u : PowerSeries R) :
    qExpand R p (HahnSeries.ofPowerSeries ℤ R u)
      = HahnSeries.ofPowerSeries ℤ R (PowerSeries.expand p (NeZero.ne p) u) := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  ext k
  by_cases hpk : (p : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hpk
    rw [qExpand_coeff_mul]
    rcases lt_or_ge m 0 with hm | hm
    · have hpm : (p : ℤ) * m < 0 := mul_neg_of_pos_of_neg hp0 hm
      rw [ofPowerSeries_coeff_of_neg _ hm, ofPowerSeries_coeff_of_neg _ hpm]
    · lift m to ℕ using hm with m
      have hcast : ((p : ℤ) * (m : ℤ)) = ((p * m : ℕ) : ℤ) := by push_cast; ring
      rw [HahnSeries.ofPowerSeries_apply_coeff, hcast, HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_expand_mul]
  · rw [qExpand_coeff_of_not_dvd p _ hpk]
    rcases lt_or_ge k 0 with hk | hk
    · exact (ofPowerSeries_coeff_of_neg _ hk).symm
    · lift k to ℕ using hk with k
      rw [HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_expand_of_not_dvd p (NeZero.ne p) u
          (fun ⟨m, hm⟩ => hpk ⟨m, by exact_mod_cast hm⟩)]

end ExpandSeam

section KeyLemma

variable {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]

theorem pow_char_single_one_eq (n : ℤ) :
    (HahnSeries.single n (1 : R)) ^ p
      = coeffMap (frobenius R p) (qExpand R p (HahnSeries.single n (1 : R))) := by
  rw [HahnSeries.single_pow, one_pow, show (p • n : ℤ) = (p : ℤ) * n from nsmul_eq_mul p n,
    qExpand_single, coeffMap_single, show frobenius R p 1 = 1 from map_one _]

theorem pow_char_ofPowerSeries_eq (u : PowerSeries R) :
    (HahnSeries.ofPowerSeries ℤ R u) ^ p
      = coeffMap (frobenius R p) (qExpand R p (HahnSeries.ofPowerSeries ℤ R u)) := by
  haveI : ExpChar R p := ExpChar.prime (Fact.out : p.Prime)
  rw [qExpand_ofPowerSeries_eq_expand p u, coeffMap_ofPowerSeries, ← map_pow]
  congr 1
  exact (MvPowerSeries.map_frobenius_expand p (NeZero.ne p) (f := u)).symm

theorem pow_char_eq_coeffMap_frobenius_qExpand (s : LaurentSeries R) :
    s ^ p = coeffMap (frobenius R p) (qExpand R p s) := by
  conv_lhs => rw [← LaurentSeries.single_order_mul_powerSeriesPart s]
  conv_rhs => rw [← LaurentSeries.single_order_mul_powerSeriesPart s]
  rw [mul_pow, map_mul, map_mul, pow_char_single_one_eq p s.order]
  congr 1
  exact pow_char_ofPowerSeries_eq p s.powerSeriesPart

end KeyLemma

section FrobeniusIdentity

variable (K : Type*) [Field K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]

theorem intCast_pow_char_eq (n : ℤ) : ((n : K) : K) ^ ℓ = (n : K) := by
  have h : (frobenius K ℓ).comp (Int.castRingHom K) = Int.castRingHom K := RingHom.ext_int _ _
  exact (RingHom.congr_fun h n :)

theorem qExpand_ell_qExpand_jqModC_eq_pow (d : ℕ) [NeZero d] :
    qExpand K ℓ (qExpand K d (jqModC K)) = (qExpand K d (jqModC K)) ^ ℓ := by
  rw [qExpand_qExpand, qExpand_congr (mul_comm ℓ d), ← qExpand_qExpand, qExpand_jqModC_eq_pow_unconditional K (ℓ := ℓ),
    map_pow]

omit [Fact ℓ.Prime] in

theorem charP_laurentSeriesC : CharP (LaurentSeries K) ℓ :=
  charP_of_injective_algebraMap (algebraMap K (LaurentSeries K)).injective ℓ

end FrobeniusIdentity

section FrobeniusEndomorphism

variable (K : Type*) [Field K] (N : ℕ) (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]

theorem frobeniusModL_map_le :
    (modularFunctionFieldFullC K N).map (qExpandAlgHomC K ℓ) ≤ modularFunctionFieldFullC K N := by
  rw [modularFunctionFieldFullC, adjoin_map, adjoin_le_iff]
  rintro x ⟨y, ⟨d, hne, hdvd, rfl⟩, rfl⟩
  haveI := hne
  show qExpandAlgHomC K ℓ (qExpand K d (jqModC K)) ∈ modularFunctionFieldFullC K N
  rw [qExpandAlgHomC_apply, qExpand_ell_qExpand_jqModC_eq_pow K ℓ d]
  exact pow_mem (jqModCd_mem_full K N hdvd) ℓ

variable {K N ℓ} in
theorem qExpand_mem_modularFunctionFieldFullC {x : LaurentSeries K}
    (hx : x ∈ modularFunctionFieldFullC K N) : qExpand K ℓ x ∈ modularFunctionFieldFullC K N :=
  frobeniusModL_map_le K N ℓ ⟨x, hx, rfl⟩

def frobeniusModLRingHom : modularFunctionFieldFullC K N →+* modularFunctionFieldFullC K N where
  toFun x := ⟨qExpand K ℓ (x : LaurentSeries K), qExpand_mem_modularFunctionFieldFullC x.2⟩
  map_one' := Subtype.ext (map_one (qExpand K ℓ))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand K ℓ) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand K ℓ))
  map_add' _ _ := Subtype.ext (map_add (qExpand K ℓ) _ _)

def frobeniusModL : modularFunctionFieldFullC K N →ₐ[K] modularFunctionFieldFullC K N :=
  { frobeniusModLRingHom K N ℓ with
    commutes' := fun a => Subtype.ext <| by
      show qExpand K ℓ (algebraMap K (LaurentSeries K) a) = algebraMap K (LaurentSeries K) a
      rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero] }

@[simp]
theorem coe_frobeniusModL (x : modularFunctionFieldFullC K N) :
    (frobeniusModL K N ℓ x : LaurentSeries K) = qExpand K ℓ (x : LaurentSeries K) := rfl

theorem frobeniusModL_injective : Function.Injective (frobeniusModL K N ℓ) := fun _ _ h =>
  Subtype.ext (qExpand_injective ℓ (congrArg (fun z : modularFunctionFieldFullC K N =>
    (z : LaurentSeries K)) h :))

theorem exists_frobeniusModL_eq_pow (x : modularFunctionFieldFullC K N) :
    ∃ y : modularFunctionFieldFullC K N, frobeniusModL K N ℓ y = x ^ ℓ := by
  haveI : CharP (LaurentSeries K) ℓ := charP_laurentSeriesC K ℓ
  suffices h : ∀ {z : LaurentSeries K}, z ∈ modularFunctionFieldFullC K N →
      ∃ y : LaurentSeries K, y ∈ modularFunctionFieldFullC K N ∧ qExpand K ℓ y = z ^ ℓ by
    obtain ⟨y, hy, hyx⟩ := h x.2
    exact ⟨⟨y, hy⟩, Subtype.ext (by rw [coe_frobeniusModL]; push_cast; exact hyx)⟩
  intro z hz
  induction hz using IntermediateField.adjoin_induction with
  | mem y hy =>
    obtain ⟨d, hne, hdvd, rfl⟩ := hy
    haveI := hne
    exact ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hdvd, qExpand_ell_qExpand_jqModC_eq_pow K ℓ d⟩
  | algebraMap c =>
    refine ⟨algebraMap K (LaurentSeries K) (c ^ ℓ), (modularFunctionFieldFullC K N).algebraMap_mem _, ?_⟩
    rw [map_pow, map_pow, algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]
  | add y z _ _ hy hz =>
    obtain ⟨y', hy', hyy⟩ := hy
    obtain ⟨z', hz', hzz⟩ := hz
    exact ⟨y' + z', add_mem hy' hz', by rw [map_add, hyy, hzz, add_pow_char]⟩
  | inv y _ hy =>
    obtain ⟨y', hy', hyy⟩ := hy
    exact ⟨y'⁻¹, inv_mem hy', by rw [map_inv₀, hyy, inv_pow]⟩
  | mul y z _ _ hy hz =>
    obtain ⟨y', hy', hyy⟩ := hy
    obtain ⟨z', hz', hzz⟩ := hz
    exact ⟨y' * z', mul_mem hy' hz', by rw [map_mul, hyy, hzz, mul_pow]⟩

theorem frobeniusModL_isIntegral : (frobeniusModL K N ℓ).toRingHom.IsIntegral := by
  intro x
  obtain ⟨y, hy⟩ := exists_frobeniusModL_eq_pow K N ℓ x
  refine ⟨Polynomial.X ^ ℓ - Polynomial.C y, Polynomial.monic_X_pow_sub_C _ (Fact.out : ℓ.Prime).ne_zero, ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero]
  exact hy.symm

end FrobeniusEndomorphism

section PlacesDivisors

variable (K : Type*) [Field K] (N : ℕ) (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]

def frobeniusPlaceModL (w : Place K (modularFunctionFieldFullC K N)) :
    Place K (modularFunctionFieldFullC K N) :=
  w.restrictAlong (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ)

theorem mem_frobeniusPlaceModL_iff (w : Place K (modularFunctionFieldFullC K N))
    (x : modularFunctionFieldFullC K N) :
    x ∈ (frobeniusPlaceModL K N ℓ w).toValuationSubring ↔
      frobeniusModL K N ℓ x ∈ w.toValuationSubring :=
  Iff.rfl

def frobeniusDivPushforwardModL :
    Divisor K (modularFunctionFieldFullC K N) →+ Divisor K (modularFunctionFieldFullC K N) :=
  Divisor.pushforwardAlong (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ)

def frobeniusDivPullbackModL [HasPrincipalDivisors K (modularFunctionFieldFullC K N)] :
    Divisor K (modularFunctionFieldFullC K N) →+ Divisor K (modularFunctionFieldFullC K N) :=
  Divisor.pullbackAlong (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ)

theorem frobeniusDivPushforwardModL_single (w : Place K (modularFunctionFieldFullC K N)) (n : ℤ) :
    frobeniusDivPushforwardModL K N ℓ (Finsupp.single w n) =
      Finsupp.single (frobeniusPlaceModL K N ℓ w)
        (n * w.inertiaDegAlong (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ)) :=
  Divisor.pushforwardAlong_single (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ) w n

theorem degree_frobeniusDivPushforwardModL (D : Divisor K (modularFunctionFieldFullC K N)) :
    Divisor.degree (frobeniusDivPushforwardModL K N ℓ D) = Divisor.degree D :=
  Divisor.degree_pushforwardAlong (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ) D

end PlacesDivisors

section Jacobian

variable (K : Type*) [Field K] (N : ℕ) (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]

def FrobeniusInputsModL : Prop :=
  ∃ (_ : HasPrincipalDivisors K (modularFunctionFieldFullC K N))
    (hfin : FiniteAlong K (frobeniusModL K N ℓ)),
    FundamentalIdentityAlong K (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ) ∧
      NormFormulaAlong K (frobeniusModL K N ℓ) hfin

variable {K N ℓ} in

theorem frobeniusInputsModL_intro [hP : HasPrincipalDivisors K (modularFunctionFieldFullC K N)]
    (hfin : FiniteAlong K (frobeniusModL K N ℓ))
    (hFI : FundamentalIdentityAlong K (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ))
    (hN : NormFormulaAlong K (frobeniusModL K N ℓ) hfin) : FrobeniusInputsModL K N ℓ :=
  ⟨hP, hfin, hFI, hN⟩

def frobeniusDegZeroPushforwardModL :
    Divisor.degZero (K := K) (F := modularFunctionFieldFullC K N) →+
      Divisor.degZero (K := K) (F := modularFunctionFieldFullC K N) :=
  ((frobeniusDivPushforwardModL K N ℓ).domRestrict _).codRestrict _
    fun D => Divisor.pushforwardAlong_mem_degZero (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ) D.2

@[simp]
theorem coe_frobeniusDegZeroPushforwardModL
    (D : Divisor.degZero (K := K) (F := modularFunctionFieldFullC K N)) :
    (frobeniusDegZeroPushforwardModL K N ℓ D : Divisor K (modularFunctionFieldFullC K N)) =
      frobeniusDivPushforwardModL K N ℓ D :=
  rfl

def frobeniusDegZeroPullbackModL [HasPrincipalDivisors K (modularFunctionFieldFullC K N)]
    (hFI : FundamentalIdentityAlong K (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ)) :
    Divisor.degZero (K := K) (F := modularFunctionFieldFullC K N) →+
      Divisor.degZero (K := K) (F := modularFunctionFieldFullC K N) :=
  ((frobeniusDivPullbackModL K N ℓ).domRestrict _).codRestrict _
    fun D => Divisor.pullbackAlong_mem_degZero (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ)
      hFI D.2

@[simp]
theorem coe_frobeniusDegZeroPullbackModL [HasPrincipalDivisors K (modularFunctionFieldFullC K N)]
    (hFI : FundamentalIdentityAlong K (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ))
    (D : Divisor.degZero (K := K) (F := modularFunctionFieldFullC K N)) :
    (frobeniusDegZeroPullbackModL K N ℓ hFI D : Divisor K (modularFunctionFieldFullC K N)) =
      frobeniusDivPullbackModL K N ℓ D :=
  rfl

def frobeniusPic0PushforwardModL (hfin : FiniteAlong K (frobeniusModL K N ℓ))
    (hN : NormFormulaAlong K (frobeniusModL K N ℓ) hfin) : JZeroC K N →+ JZeroC K N :=
  QuotientAddGroup.map _ _ (frobeniusDegZeroPushforwardModL K N ℓ) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact Divisor.isPrincipal_pushforwardAlong (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ)
      hfin hN hD)

theorem frobeniusPic0PushforwardModL_mk (hfin : FiniteAlong K (frobeniusModL K N ℓ))
    (hN : NormFormulaAlong K (frobeniusModL K N ℓ) hfin)
    (D : Divisor.degZero (K := K) (F := modularFunctionFieldFullC K N)) :
    frobeniusPic0PushforwardModL K N ℓ hfin hN (Pic0.mk D) =
      Pic0.mk (frobeniusDegZeroPushforwardModL K N ℓ D) :=
  rfl

def frobeniusPic0PullbackModL [HasPrincipalDivisors K (modularFunctionFieldFullC K N)]
    (hFI : FundamentalIdentityAlong K (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ)) :
    JZeroC K N →+ JZeroC K N :=
  QuotientAddGroup.map _ _ (frobeniusDegZeroPullbackModL K N ℓ hFI) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact Divisor.isPrincipal_pullbackAlong (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ) hD)

theorem frobeniusPic0PullbackModL_mk [HasPrincipalDivisors K (modularFunctionFieldFullC K N)]
    (hFI : FundamentalIdentityAlong K (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ))
    (D : Divisor.degZero (K := K) (F := modularFunctionFieldFullC K N)) :
    frobeniusPic0PullbackModL K N ℓ hFI (Pic0.mk D) =
      Pic0.mk (frobeniusDegZeroPullbackModL K N ℓ hFI D) :=
  rfl

open Classical in

def frobeniusPushforwardModL : JZeroC K N →+ JZeroC K N :=
  if h : FrobeniusInputsModL K N ℓ then
    frobeniusPic0PushforwardModL K N ℓ h.snd.fst h.snd.snd.2
  else 0

open Classical in

def frobeniusPullbackModL : JZeroC K N →+ JZeroC K N :=
  if h : FrobeniusInputsModL K N ℓ then
    haveI := h.fst
    frobeniusPic0PullbackModL K N ℓ h.snd.snd.1
  else 0

variable {K N ℓ}

theorem frobeniusPushforwardModL_eq [HasPrincipalDivisors K (modularFunctionFieldFullC K N)]
    (hfin : FiniteAlong K (frobeniusModL K N ℓ))
    (hFI : FundamentalIdentityAlong K (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ))
    (hN : NormFormulaAlong K (frobeniusModL K N ℓ) hfin) :
    frobeniusPushforwardModL K N ℓ = frobeniusPic0PushforwardModL K N ℓ hfin hN := by
  have h : FrobeniusInputsModL K N ℓ := frobeniusInputsModL_intro hfin hFI hN
  rw [frobeniusPushforwardModL, dif_pos h]

theorem frobeniusPushforwardModL_mk [HasPrincipalDivisors K (modularFunctionFieldFullC K N)]
    (hfin : FiniteAlong K (frobeniusModL K N ℓ))
    (hFI : FundamentalIdentityAlong K (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ))
    (hN : NormFormulaAlong K (frobeniusModL K N ℓ) hfin)
    (D : Divisor.degZero (K := K) (F := modularFunctionFieldFullC K N)) :
    frobeniusPushforwardModL K N ℓ (Pic0.mk D) = Pic0.mk (frobeniusDegZeroPushforwardModL K N ℓ D) := by
  rw [frobeniusPushforwardModL_eq hfin hFI hN]
  rfl

theorem frobeniusPushforwardModL_of_not (h : ¬ FrobeniusInputsModL K N ℓ) :
    frobeniusPushforwardModL K N ℓ = 0 := by
  rw [frobeniusPushforwardModL, dif_neg h]

theorem frobeniusPullbackModL_eq [HasPrincipalDivisors K (modularFunctionFieldFullC K N)]
    (hfin : FiniteAlong K (frobeniusModL K N ℓ))
    (hFI : FundamentalIdentityAlong K (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ))
    (hN : NormFormulaAlong K (frobeniusModL K N ℓ) hfin) :
    frobeniusPullbackModL K N ℓ = frobeniusPic0PullbackModL K N ℓ hFI := by
  have h : FrobeniusInputsModL K N ℓ := frobeniusInputsModL_intro hfin hFI hN
  rw [frobeniusPullbackModL, dif_pos h]

theorem frobeniusPullbackModL_mk [HasPrincipalDivisors K (modularFunctionFieldFullC K N)]
    (hfin : FiniteAlong K (frobeniusModL K N ℓ))
    (hFI : FundamentalIdentityAlong K (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ))
    (hN : NormFormulaAlong K (frobeniusModL K N ℓ) hfin)
    (D : Divisor.degZero (K := K) (F := modularFunctionFieldFullC K N)) :
    frobeniusPullbackModL K N ℓ (Pic0.mk D) = Pic0.mk (frobeniusDegZeroPullbackModL K N ℓ hFI D) := by
  rw [frobeniusPullbackModL_eq hfin hFI hN]
  rfl

theorem frobeniusPullbackModL_of_not (h : ¬ FrobeniusInputsModL K N ℓ) :
    frobeniusPullbackModL K N ℓ = 0 := by
  rw [frobeniusPullbackModL, dif_neg h]

end Jacobian

end ModularCurve

end


