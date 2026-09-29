-- Prove2me | Definitions.Def_RatIdele_Normalizer
-- name    : RatIdele_Normalizer
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/ef5e3cc3-1b66-5d8d-912e-0467fce5082b
-- title:
--   Normaliser of a rational idele and its unit coordinates
-- statement:
--   Working with the adele ring $\mathbb{A}_\mathbb{Q}$ of $\mathbb{Q}$, written as the product of the infinite adeles with the finite adele ring of $\mathcal{O}_{\mathbb{Q}}$, this module attaches to each idele $x \in \mathbb{A}_\mathbb{Q}^\times$ three sets of coordinates. First, `archCoord x` is the real number obtained by evaluating the archimedean part of $x$ at the unique infinite place of $\mathbb{Q}$ and transporting it along the ring isomorphism of that completion with $\mathbb{R}$; it is multiplicative, never zero, equal to $q$ on the principal idele of $q \in \mathbb{Q}^\times$ and equal to $1$ on ideles with trivial archimedean part. Its sign is recorded as $\pm 1 \in \mathbb{Q}$ by `archSign`. Second, for a height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, `ordAt v x` is the integer $n$ with $|x_v|_v = \exp(-n)$ in $\mathbb{Z}^{m0}$, i.e. minus the `WithZero` logarithm of the valuation of the $v$-component; it is additive in $x$ and vanishes outside a finite set of $v$. The homomorphism `finPart` is the restriction of an idele to its finite part.
--
--   The predicate `IsNormalizer x r`, for $r \in \mathbb{Q}$, asserts that $v(r) = |x_v|_v$ for every finite place $v$ and that $\mathrm{archCoord}(x)\cdot r > 0$; such an $r$ is nonzero and, by the fact that a positive rational with trivial valuation at all finite places equals $1$, unique. The explicit normaliser is
--   $$\rho(x) = \mathrm{archSign}(x)\prod_v p_v^{\,\mathrm{ord}_v(x)},$$
--   the finite product running over the primes $p_v$ generating the $v$, and it is shown to satisfy the predicate. Accordingly $\rho$ is multiplicative, sends the principal idele of $q$ to $q$, sends the idele concentrated at $v$ with component of valuation $\exp(-1)$ to $p_v$ and with unit component to $1$, and reduces to the sign when the finite part is trivial. Third, `unitAt v x` $= x_v \cdot \rho(x)^{-1}$ in the completion at $v$ has valuation $1$; `unitIntAt` records it as an element of the valuation ring, multiplicative in $x$ and a unit there. Supporting lemmas compute valuations of natural numbers at $v$ in terms of divisibility by $p_v$ and identify the $v$-component of a principal idele.
--
--   **Relation to Mathlib.** The identification of the height-one spectrum of $\mathcal{O}_{\mathbb{Q}}$ with the positive primes (`primesEquiv`, `natGenerator`) is Mathlib's; the lemmas of the first section compute ideals and valuations in those terms. The normaliser `ρ`, the predicate `IsNormalizer`, the archimedean coordinate and the unit coordinates `unitAt`/`unitIntAt` are the project's own notions.
--
--   **Where it is used.** These coordinates make explicit the decomposition $\mathbb{A}_\mathbb{Q}^\times = \mathbb{Q}^\times\cdot(\mathbb{R}_{>0}\times\prod_p \mathbb{Z}_p^\times)$ by a formula, with no appeal to finiteness of the class number. They serve the adelic description of modular forms for $\mathrm{GL}_2$ over $\mathbb{Q}$: the unit coordinates at a finite place are the input to nebentypus characters on idele classes, and the normaliser separates the scalar part of a Hecke generator at a prime from its unit part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_RatIdele_Normalizer.lean

import Definitions.Def_NumberField_AdelicLevel
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open Rat.HeightOneSpectrum NumberField.AdelicLevel

namespace RatIdele

local notation "𝔸ℚ" => AdeleRing (𝓞 ℚ) ℚ
local notation "𝔸ℚf" => FiniteAdeleRing (𝓞 ℚ) ℚ

section Primes

theorem natCast_mem_asIdeal_iff (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    ((n : 𝓞 ℚ)) ∈ v.asIdeal ↔ natGenerator v ∣ n := by
  rw [natGenerator_dvd_iff,
    show ((n : ℕ) : ℤ) = Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) ((n : 𝓞 ℚ)) from (map_natCast _ n).symm]
  exact Ideal.apply_mem_of_equiv_iff.symm

theorem natCast_natGenerator_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) : ((natGenerator v : ℕ) : 𝓞 ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (prime_natGenerator v).ne_zero

theorem prime_natCast_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) : Prime ((natGenerator v : ℕ) : 𝓞 ℚ) := by
  have hcast : ((natGenerator v : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((natGenerator v : ℕ) : ℤ) :=
    (map_natCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm
  rw [hcast]
  exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr
    (Nat.prime_iff_prime_int.mp (prime_natGenerator v))

theorem asIdeal_eq_span_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.asIdeal = Ideal.span {((natGenerator v : ℕ) : 𝓞 ℚ)} := by
  have hmax : (Ideal.span {((natGenerator v : ℕ) : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime (natCast_natGenerator_ne_zero v)).mpr
      (prime_natCast_natGenerator v)).isMaximal
      ((Ideal.span_singleton_eq_bot (α := 𝓞 ℚ)).not.mpr (natCast_natGenerator_ne_zero v))
  exact (hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr
    ((natCast_mem_asIdeal_iff v _).mpr dvd_rfl))).symm

theorem valuation_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.valuation ℚ ((natGenerator v : ℕ) : ℚ) = exp (-1 : ℤ) := by
  rw [show ((natGenerator v : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ ((natGenerator v : ℕ) : 𝓞 ℚ) from
      (map_natCast (algebraMap (𝓞 ℚ) ℚ) _).symm, valuation_of_algebraMap]
  exact intValuation_singleton v (natCast_natGenerator_ne_zero v) (asIdeal_eq_span_natGenerator v)

theorem valuation_natCast_of_not_dvd (v : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (h : ¬ natGenerator v ∣ n) :
    v.valuation ℚ ((n : ℕ) : ℚ) = 1 := by
  rw [show ((n : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ ((n : ℕ) : 𝓞 ℚ) from (map_natCast (algebraMap (𝓞 ℚ) ℚ) _).symm,
    valuation_of_algebraMap]
  exact intValuation_eq_one_iff.mpr fun hmem => h ((natCast_mem_asIdeal_iff v n).mp hmem)

theorem eq_of_natGenerator_eq {v w : HeightOneSpectrum (𝓞 ℚ)} (h : natGenerator v = natGenerator w) : v = w :=
  (primesEquiv (R := 𝓞 ℚ)).injective (Subtype.ext h)

theorem valuation_natGenerator_of_ne {v w : HeightOneSpectrum (𝓞 ℚ)} (h : v ≠ w) :
    w.valuation ℚ ((natGenerator v : ℕ) : ℚ) = 1 :=
  valuation_natCast_of_not_dvd w fun hd =>
    h (eq_of_natGenerator_eq
      ((Nat.prime_dvd_prime_iff_eq (prime_natGenerator w) (prime_natGenerator v)).mp hd)).symm

theorem natGenerator_primesEquiv_symm (p : Nat.Primes) :
    natGenerator ((primesEquiv (R := 𝓞 ℚ)).symm p) = (p : ℕ) :=
  congrArg Subtype.val ((primesEquiv (R := 𝓞 ℚ)).apply_symm_apply p)

theorem valued_algebraMap_rat (v : HeightOneSpectrum (𝓞 ℚ)) (q : ℚ) :
    Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q) = v.valuation ℚ q := by
  rw [algebraMap_adicCompletion]
  exact valuedAdicCompletion_eq_valuation' v q

theorem algebraMap_adeleRing_snd (q : ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (algebraMap ℚ 𝔸ℚ q).2 v = algebraMap ℚ (v.adicCompletion ℚ) q := by
  rw [AdeleRing.algebraMap_snd_apply, algebraMap_adicCompletion]
  rfl

theorem natCast_adicCompletion_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (hn : n ≠ 0) :
    ((n : ℕ) : v.adicCompletion ℚ) ≠ 0 := by
  rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ)) n]
  exact (map_ne_zero (algebraMap ℚ (v.adicCompletion ℚ))).mpr (Nat.cast_ne_zero.mpr hn)

end Primes

section Arch

def archCoord (x : (𝔸ℚ)ˣ) : ℝ :=
  InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace ((x : 𝔸ℚ).1 Rat.infinitePlace)

theorem archCoord_mul (x y : (𝔸ℚ)ˣ) : archCoord (x * y) = archCoord x * archCoord y := by
  unfold archCoord
  rw [← map_mul]
  rfl

theorem archCoord_one : archCoord 1 = 1 := by
  unfold archCoord
  rw [show ((1 : (𝔸ℚ)ˣ) : 𝔸ℚ).1 Rat.infinitePlace = 1 from rfl, map_one]

theorem archCoord_ne_zero (x : (𝔸ℚ)ˣ) : archCoord x ≠ 0 := by
  intro h
  have h1 := archCoord_mul x x⁻¹
  rw [mul_inv_cancel, archCoord_one, h, zero_mul] at h1
  exact one_ne_zero h1

theorem archCoord_principal (q : ℚˣ) :
    archCoord (Units.map (algebraMap ℚ 𝔸ℚ : ℚ →* 𝔸ℚ) q) = ((q : ℚ) : ℝ) :=
  eq_ratCast ((InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace :
      Rat.infinitePlace.Completion ≃+* ℝ).toRingHom.comp
    ((Pi.evalRingHom (fun w : InfinitePlace ℚ => w.Completion) Rat.infinitePlace).comp
      ((RingHom.fst _ _).comp (algebraMap ℚ 𝔸ℚ)))) (q : ℚ)

theorem archCoord_finIncl (y : (𝔸ℚf)ˣ) : archCoord (Units.map (finIncl (𝓞 ℚ) ℚ) y) = 1 := by
  unfold archCoord
  rw [Units.coe_map, finIncl_apply_fst, show (1 : InfiniteAdeleRing ℚ) Rat.infinitePlace = 1 from rfl, map_one]

end Arch

section Order

def finPart : (𝔸ℚ)ˣ →* (𝔸ℚf)ˣ := Units.map (RingHom.snd (InfiniteAdeleRing ℚ) 𝔸ℚf).toMonoidHom

theorem finPart_apply (x : (𝔸ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((finPart x : (𝔸ℚf)ˣ) : 𝔸ℚf) v = (x : 𝔸ℚ).2 v := rfl

theorem valued_snd_mul (x y : (𝔸ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v ((((x * y : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v) = Valued.v ((x : 𝔸ℚ).2 v) * Valued.v ((y : 𝔸ℚ).2 v) := by
  rw [← map_mul]
  rfl

theorem valued_snd_ne_zero (x : (𝔸ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) : Valued.v ((x : 𝔸ℚ).2 v) ≠ 0 := by
  rw [ne_eq, map_eq_zero]
  intro h
  have h1 : (((x * x⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v = 1 := by
    rw [mul_inv_cancel]
    rfl
  rw [show (((x * x⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v = (x : 𝔸ℚ).2 v * (((x⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v from rfl, h,
    zero_mul] at h1
  exact zero_ne_one h1

theorem valued_snd_inv_mul (x : (𝔸ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v ((((x⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v) * Valued.v ((x : 𝔸ℚ).2 v) = 1 := by
  rw [← valued_snd_mul, inv_mul_cancel]
  show Valued.v ((1 : 𝔸ℚf) v) = 1
  rw [show ((1 : 𝔸ℚf)) v = 1 from rfl, map_one]

def ordAt (v : HeightOneSpectrum (𝓞 ℚ)) (x : (𝔸ℚ)ˣ) : ℤ := -log (Valued.v ((x : 𝔸ℚ).2 v))

theorem valued_snd_eq (v : HeightOneSpectrum (𝓞 ℚ)) (x : (𝔸ℚ)ˣ) :
    Valued.v ((x : 𝔸ℚ).2 v) = exp (-ordAt v x) := by
  rw [ordAt, neg_neg, exp_log (valued_snd_ne_zero x v)]

theorem ordAt_mul (v : HeightOneSpectrum (𝓞 ℚ)) (x y : (𝔸ℚ)ˣ) : ordAt v (x * y) = ordAt v x + ordAt v y := by
  unfold ordAt
  rw [valued_snd_mul, log_mul (valued_snd_ne_zero x v) (valued_snd_ne_zero y v), neg_add]

theorem ordAt_one (v : HeightOneSpectrum (𝓞 ℚ)) : ordAt v 1 = 0 := by
  unfold ordAt
  rw [show ((1 : (𝔸ℚ)ˣ) : 𝔸ℚ).2 v = 1 from rfl, map_one, log_one, neg_zero]

theorem ordAt_eq_zero_of_le_one {v : HeightOneSpectrum (𝓞 ℚ)} {x : (𝔸ℚ)ˣ} (hx : Valued.v ((x : 𝔸ℚ).2 v) ≤ 1)
    (hxi : Valued.v ((((x⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v) ≤ 1) : ordAt v x = 0 := by
  have hmul := valued_snd_inv_mul x v
  have h1 : Valued.v ((x : 𝔸ℚ).2 v) = 1 := le_antisymm hx (by
    calc (1 : ℤᵐ⁰) = Valued.v ((((x⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v) * Valued.v ((x : 𝔸ℚ).2 v) := hmul.symm
      _ ≤ 1 * Valued.v ((x : 𝔸ℚ).2 v) := mul_le_mul_left hxi _
      _ = Valued.v ((x : 𝔸ℚ).2 v) := one_mul _)
  unfold ordAt
  rw [h1, log_one, neg_zero]

theorem finite_setOf_ordAt_ne_zero (x : (𝔸ℚ)ˣ) : {v : HeightOneSpectrum (𝓞 ℚ) | ordAt v x ≠ 0}.Finite := by
  have hx : ∀ᶠ v in Filter.cofinite, ((x : 𝔸ℚ).2 : 𝔸ℚf) v ∈ v.adicCompletionIntegers ℚ := ((x : 𝔸ℚ).2).2
  have hxi : ∀ᶠ v in Filter.cofinite, ((((x⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 : 𝔸ℚf) v ∈ v.adicCompletionIntegers ℚ :=
    ((((x⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ).2).2
  have hboth := hx.and hxi
  rw [Filter.eventually_cofinite] at hboth
  refine hboth.subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  intro hcon
  exact hv (ordAt_eq_zero_of_le_one ((mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mp hcon.1)
    ((mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mp hcon.2))

end Order

section Normalizer

def IsNormalizer (x : (𝔸ℚ)ˣ) (r : ℚ) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((x : 𝔸ℚ).2 v) = v.valuation ℚ r) ∧ 0 < archCoord x * (r : ℝ)

theorem IsNormalizer.ne_zero {x : (𝔸ℚ)ˣ} {r : ℚ} (h : IsNormalizer x r) : r ≠ 0 := by
  rintro rfl
  have := h.2
  rw [Rat.cast_zero, mul_zero] at this
  exact lt_irrefl _ this

def archSign (x : (𝔸ℚ)ˣ) : ℚ := if 0 < archCoord x then 1 else -1

theorem archCoord_mul_archSign_pos (x : (𝔸ℚ)ˣ) : 0 < archCoord x * (archSign x : ℝ) := by
  unfold archSign
  split_ifs with h
  · rw [Rat.cast_one, mul_one]
    exact h
  · rw [Rat.cast_neg, Rat.cast_one, mul_neg, mul_one]
    exact neg_pos.mpr (lt_of_le_of_ne (not_lt.mp h) (archCoord_ne_zero x))

theorem valuation_archSign (w : HeightOneSpectrum (𝓞 ℚ)) (x : (𝔸ℚ)ˣ) : w.valuation ℚ (archSign x) = 1 := by
  unfold archSign
  split_ifs
  · exact map_one _
  · rw [Valuation.map_neg, map_one]

def ρ (x : (𝔸ℚ)ˣ) : ℚ :=
  archSign x * ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), ((natGenerator v : ℕ) : ℚ) ^ ordAt v x

theorem mulSupport_subset_toFinset (x : (𝔸ℚ)ˣ) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 ℚ) => ((natGenerator v : ℕ) : ℚ) ^ ordAt v x)
      ⊆ ((finite_setOf_ordAt_ne_zero x).toFinset : Set (HeightOneSpectrum (𝓞 ℚ))) := by
  intro v hv
  rw [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
  intro h0
  rw [Function.mem_mulSupport, h0, zpow_zero] at hv
  exact hv rfl

theorem finprod_pow_ordAt_pos (x : (𝔸ℚ)ˣ) :
    (0 : ℚ) < ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), ((natGenerator v : ℕ) : ℚ) ^ ordAt v x :=
  finprod_induction (fun r : ℚ => 0 < r) one_pos (fun _ _ => mul_pos)
    fun v => zpow_pos (Nat.cast_pos.mpr (prime_natGenerator v).pos) _

theorem valuation_ρ (w : HeightOneSpectrum (𝓞 ℚ)) (x : (𝔸ℚ)ˣ) : w.valuation ℚ (ρ x) = Valued.v ((x : 𝔸ℚ).2 w) := by
  classical
  rw [ρ, map_mul, valuation_archSign, one_mul, finprod_eq_prod_of_mulSupport_subset _ (mulSupport_subset_toFinset x),
    map_prod, valued_snd_eq, Finset.prod_eq_single w]
  · rw [map_zpow₀, valuation_natGenerator, ← exp_zsmul, smul_eq_mul, mul_neg_one]
  · intro v _ hvw
    rw [map_zpow₀, valuation_natGenerator_of_ne hvw, one_zpow]
  · intro hw
    have h0 : ordAt w x = 0 := by
      by_contra h0
      exact hw ((Set.Finite.mem_toFinset _).mpr h0)
    rw [h0, zpow_zero, map_one]

theorem ρ_spec (x : (𝔸ℚ)ˣ) : IsNormalizer x (ρ x) := by
  refine ⟨fun v => (valuation_ρ v x).symm, ?_⟩
  rw [ρ, Rat.cast_mul, ← mul_assoc]
  exact mul_pos (archCoord_mul_archSign_pos x) (by exact_mod_cast finprod_pow_ordAt_pos x)

theorem exists_isNormalizer (x : (𝔸ℚ)ˣ) : ∃ r : ℚ, IsNormalizer x r := ⟨ρ x, ρ_spec x⟩

theorem rat_eq_one_of_valuation_eq_one {q : ℚ} (hq : 0 < q)
    (h : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.valuation ℚ q = 1) : q = 1 := by
  have hq0 : q ≠ 0 := hq.ne'
  obtain ⟨z, hz⟩ := mem_integers_of_valuation_le_one ℚ q fun v => (h v).le
  obtain ⟨z', hz'⟩ := mem_integers_of_valuation_le_one ℚ q⁻¹ fun v => by rw [map_inv₀, h v, inv_one]
  have hzz' : z * z' = 1 :=
    IsFractionRing.injective (𝓞 ℚ) ℚ (by rw [map_mul, hz, hz', map_one, mul_inv_cancel₀ hq0])
  have hu : IsUnit z := isUnit_iff_exists_inv.mpr ⟨z', hzz'⟩
  have hzq : (z : ℚ) = q := by rw [RingOfIntegers.coe_eq_algebraMap]; exact hz
  rcases Rat.RingOfIntegers.isUnit_iff.mp hu with h1 | h1
  · rw [← hzq]; exact h1
  · exfalso
    rw [hzq] at h1
    rw [h1] at hq
    exact absurd hq (by norm_num)

theorem IsNormalizer.unique {x : (𝔸ℚ)ˣ} {r r' : ℚ} (h : IsNormalizer x r) (h' : IsNormalizer x r') : r = r' := by
  have hr' := h'.ne_zero
  have hq : 0 < r / r' := by
    have h3 : (0 : ℝ) < (archCoord x * r) / (archCoord x * r') := div_pos h.2 h'.2
    rw [mul_div_mul_left _ _ (archCoord_ne_zero x)] at h3
    exact_mod_cast h3
  have hval : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.valuation ℚ (r / r') = 1 := fun v => by
    rw [map_div₀, ← h.1 v, ← h'.1 v, div_self (valued_snd_ne_zero x v)]
  have := rat_eq_one_of_valuation_eq_one hq hval
  rwa [div_eq_one_iff_eq hr'] at this

theorem ρ_ne_zero (x : (𝔸ℚ)ˣ) : ρ x ≠ 0 := (ρ_spec x).ne_zero

theorem ρ_eq_of_isNormalizer {x : (𝔸ℚ)ˣ} {r : ℚ} (h : IsNormalizer x r) : ρ x = r := (ρ_spec x).unique h

theorem ρ_mul (x y : (𝔸ℚ)ˣ) : ρ (x * y) = ρ x * ρ y := by
  refine ρ_eq_of_isNormalizer ⟨fun v => ?_, ?_⟩
  · rw [valued_snd_mul, (ρ_spec x).1 v, (ρ_spec y).1 v, map_mul]
  · rw [archCoord_mul, Rat.cast_mul, show archCoord x * archCoord y * (((ρ x : ℚ) : ℝ) * ((ρ y : ℚ) : ℝ))
        = (archCoord x * ((ρ x : ℚ) : ℝ)) * (archCoord y * ((ρ y : ℚ) : ℝ)) by ring]
    exact mul_pos (ρ_spec x).2 (ρ_spec y).2

theorem ρ_principal (q : ℚˣ) : ρ (Units.map (algebraMap ℚ 𝔸ℚ : ℚ →* 𝔸ℚ) q) = (q : ℚ) := by
  refine ρ_eq_of_isNormalizer ⟨fun v => ?_, ?_⟩
  · rw [Units.coe_map, MonoidHom.coe_coe, algebraMap_adeleRing_snd, valued_algebraMap_rat]
  · rw [archCoord_principal]
    exact mul_self_pos.mpr (by exact_mod_cast q.ne_zero)

theorem ρ_one : ρ 1 = 1 := by
  have := ρ_principal 1
  rwa [map_one, Units.val_one] at this

theorem ρ_finIncl_localUnit (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ)
    (ht : Valued.v (t : v.adicCompletion ℚ) = exp (-1 : ℤ)) :
    ρ (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v t)) = ((natGenerator v : ℕ) : ℚ) := by
  refine ρ_eq_of_isNormalizer ⟨fun w => ?_, ?_⟩
  · rw [Units.coe_map, finIncl_apply_snd]
    by_cases hw : w = v
    · subst hw
      rw [localUnit_apply_self, ht, valuation_natGenerator]
    · rw [localUnit_apply_of_ne (𝓞 ℚ) ℚ v t hw, map_one, valuation_natGenerator_of_ne (Ne.symm hw)]
  · rw [archCoord_finIncl, one_mul]
    exact_mod_cast (prime_natGenerator v).pos

theorem ρ_finIncl_localUnit_of_valued_one (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ)
    (ht : Valued.v (t : v.adicCompletion ℚ) = 1) :
    ρ (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v t)) = 1 := by
  refine ρ_eq_of_isNormalizer ⟨fun w => ?_, ?_⟩
  · rw [Units.coe_map, finIncl_apply_snd, map_one]
    by_cases hw : w = v
    · subst hw
      rw [localUnit_apply_self, ht]
    · rw [localUnit_apply_of_ne (𝓞 ℚ) ℚ v t hw, map_one]
  · rw [archCoord_finIncl, one_mul, Rat.cast_one]
    exact one_pos

theorem ρ_eq_archSign_of_snd_eq_one {x : (𝔸ℚ)ˣ} (hx : ∀ w : HeightOneSpectrum (𝓞 ℚ), (x : 𝔸ℚ).2 w = 1) :
    ρ x = archSign x := by
  refine ρ_eq_of_isNormalizer ⟨fun w => ?_, archCoord_mul_archSign_pos x⟩
  rw [hx w, map_one, valuation_archSign]

end Normalizer

section UnitAt

def unitAt (v : HeightOneSpectrum (𝓞 ℚ)) (x : (𝔸ℚ)ˣ) : v.adicCompletion ℚ :=
  (x : 𝔸ℚ).2 v * (algebraMap ℚ (v.adicCompletion ℚ) (ρ x))⁻¹

theorem valued_unitAt (v : HeightOneSpectrum (𝓞 ℚ)) (x : (𝔸ℚ)ˣ) : Valued.v (unitAt v x) = 1 := by
  unfold unitAt
  rw [map_mul, map_inv₀, valued_algebraMap_rat, ← (ρ_spec x).1 v, mul_inv_cancel₀ (valued_snd_ne_zero x v)]

theorem unitAt_mul (v : HeightOneSpectrum (𝓞 ℚ)) (x y : (𝔸ℚ)ˣ) : unitAt v (x * y) = unitAt v x * unitAt v y := by
  unfold unitAt
  rw [ρ_mul, map_mul, mul_inv, show (((x * y : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v = (x : 𝔸ℚ).2 v * (y : 𝔸ℚ).2 v from rfl]
  ring

theorem unitAt_one (v : HeightOneSpectrum (𝓞 ℚ)) : unitAt v 1 = 1 := by
  unfold unitAt
  rw [ρ_one, map_one, inv_one, mul_one]
  rfl

theorem unitAt_principal (v : HeightOneSpectrum (𝓞 ℚ)) (q : ℚˣ) :
    unitAt v (Units.map (algebraMap ℚ 𝔸ℚ : ℚ →* 𝔸ℚ) q) = 1 := by
  unfold unitAt
  rw [ρ_principal, Units.coe_map, MonoidHom.coe_coe, algebraMap_adeleRing_snd,
    mul_inv_cancel₀ ((map_ne_zero _).mpr q.ne_zero)]

theorem unitAt_finIncl_localUnit_self (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ)
    (ht : Valued.v (t : v.adicCompletion ℚ) = 1) :
    unitAt v (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v t)) = t := by
  unfold unitAt
  rw [ρ_finIncl_localUnit_of_valued_one v t ht, map_one, inv_one, mul_one, Units.coe_map, finIncl_apply_snd,
    localUnit_apply_self]

theorem unitAt_finIncl_localUnit_of_ne (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ)
    (ht : Valued.v (t : v.adicCompletion ℚ) = 1) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) :
    unitAt w (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v t)) = 1 := by
  unfold unitAt
  rw [ρ_finIncl_localUnit_of_valued_one v t ht, map_one, inv_one, mul_one, Units.coe_map, finIncl_apply_snd,
    localUnit_apply_of_ne (𝓞 ℚ) ℚ v t hw]

def unitIntAt (v : HeightOneSpectrum (𝓞 ℚ)) (x : (𝔸ℚ)ˣ) : v.adicCompletionIntegers ℚ :=
  ⟨unitAt v x, (mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr (valued_unitAt v x).le⟩

theorem coe_unitIntAt (v : HeightOneSpectrum (𝓞 ℚ)) (x : (𝔸ℚ)ˣ) :
    (unitIntAt v x : v.adicCompletion ℚ) = unitAt v x := rfl

theorem unitIntAt_mul (v : HeightOneSpectrum (𝓞 ℚ)) (x y : (𝔸ℚ)ˣ) :
    unitIntAt v (x * y) = unitIntAt v x * unitIntAt v y :=
  Subtype.ext (unitAt_mul v x y)

theorem unitIntAt_one (v : HeightOneSpectrum (𝓞 ℚ)) : unitIntAt v 1 = 1 := Subtype.ext (unitAt_one v)

theorem isUnit_unitIntAt (v : HeightOneSpectrum (𝓞 ℚ)) (x : (𝔸ℚ)ˣ) : IsUnit (unitIntAt v x) :=
  isUnit_iff_exists_inv.mpr ⟨unitIntAt v x⁻¹, by rw [← unitIntAt_mul, mul_inv_cancel, unitIntAt_one]⟩

theorem natCast_mul_unitIntAt_eq_one {v : HeightOneSpectrum (𝓞 ℚ)} {x : (𝔸ℚ)ˣ} {n : ℕ}
    (h : ((n : ℕ) : v.adicCompletion ℚ) * unitAt v x = 1) :
    ((n : ℕ) : v.adicCompletionIntegers ℚ) * unitIntAt v x = 1 :=
  Subtype.ext (by rw [MulMemClass.coe_mul, SubringClass.coe_natCast, OneMemClass.coe_one]; exact h)

end UnitAt

end RatIdele

end


