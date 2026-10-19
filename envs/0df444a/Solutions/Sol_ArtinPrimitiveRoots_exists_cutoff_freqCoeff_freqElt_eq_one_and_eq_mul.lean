-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_freqCoeff_freqElt_eq_one_and_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T04:39:55.129536+00:00
-- url     : https://prove2.me/submissions/0d3b9f76-4943-4aa1-8740-8c15e307a382

import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinHeckeRowL
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_poissonFactor_prime_pow_eq_poissonLocal
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_gaussPhase_mul_gaussPhase_mul_conj_gaussLambda_mul_conj_gaussG_eq_neg_one
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_conj_gaussG_pow_six_eq_one
import Mathlib


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

section sieve

variable (𝔪 : Ideal (𝓞 F))

variable {𝔪 f A}

end sieve

end C3A

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3A_Local: the local coefficients of the principal frequency series and their sum

`principalLocalCoeff Q η θ e₀ l k m` is the coefficient of the principal row `ℱ₁` at a prime `𝔭`
of norm `Q`, for `v_𝔭(𝔠) = e₀ ∈ {0,1}`, `v_𝔭(𝔫) = l`, `v_𝔭(𝔰) = k`, `v_𝔭(𝔯) = m`
(Prop 7.3, (7.16)–(7.17) at `u = 1`, `t = e₀ + 3l`, `J = 6m`): with `η = η(𝔭)` and
`θ = ϑ(𝔭)⁶`, and `γ₁γ₂ϑ = −η`, `τ₁ = √Q γ₁`, `τ₁τ₅ = Q` substituted,

* `t = 0`: `1` if `k = 0` or `m = 0`;
* `t = 6d`, `d ≥ 1`: `θ^d Q^{6d}(1 − Q⁻¹)` if `k = 0`, `m ≥ d`; `θ^d Q^{6d}` if `k = 1`, `m = d`;
* `t = 6d + 1`: `−η √Q θ^d Q^{6d}` if `k = 0`, `m = d`; `−η √Q θ^d Q^{6d} (Q − 1)` if `k = 1`, `m > d`;
* `0` otherwise.

`hasSum_local`: weighted by `wc^{e₀} wn^l ws^k wr^m`, the coefficients sum to the closed form (7.19). -/

open NumberField Filter Topology

namespace ArtinPrimitiveRoots

namespace C3A

/-- The local coefficient (7.16)–(7.17) of the principal row at `u = 1`. -/
noncomputable def principalLocalCoeff (Q : ℕ) (η θ : ℂ) (e₀ l k m : ℕ) : ℂ :=
  if e₀ = 0 then
    if l = 0 then (if k = 0 ∨ m = 0 then 1 else 0)
    else if Even l then
      (if k = 0 ∧ l / 2 ≤ m then θ ^ (l / 2) * (Q : ℂ) ^ (3 * l) * (1 - (Q : ℂ)⁻¹)
       else if k = 1 ∧ m = l / 2 then θ ^ (l / 2) * (Q : ℂ) ^ (3 * l) else 0)
    else 0
  else if e₀ = 1 ∧ Even l then
    (if k = 0 ∧ m = l / 2 then -(η * (Real.sqrt Q : ℂ)) * θ ^ (l / 2) * (Q : ℂ) ^ (3 * l)
     else if k = 1 ∧ l / 2 < m then
       -(η * (Real.sqrt Q : ℂ)) * θ ^ (l / 2) * (Q : ℂ) ^ (3 * l) * ((Q : ℂ) - 1)
     else 0)
  else 0

section sum

variable (Q : ℕ) (η θ wc wn ws wr : ℂ)

end sum

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

instance fiber_finite (n : ℕ) : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

/-! ### Basic facts on Hecke characters -/

theorem toFun_top {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) : χ.toFun ⊤ = 1 := by
  have := χ.map_principal' 1 one_ne_zero (by simp)
  rwa [Ideal.span_singleton_one] at this

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

/-! ### The one-variable Euler product from `euler4` -/

section one

variable {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (s : ℂ)

end one

/-! ### `ζ^S` -/

end C3A

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3P_Maj: the majorants and the Fubini swaps

`u t = (1 + t²)⁻¹`, `γ x = exp(−x²/2)`, and the three-variable majorant
`u t₁ · u t₂ · γ (t₁ + t₃)`; `e^{−(t₁+t₃)²} u t₃ ≤ 4 u t₁ γ(t₁+t₃)` moves the Gaussian's decay onto
the outer variable. -/

open MeasureTheory Filter Topology

namespace ArtinPrimitiveRoots

namespace C3P

/-! ### Integrability of the majorants -/

/-! ### Fubini -/

end C3P

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3P_Bound: the principal-row integrand and its majorant

`Phi ξ w z = E(ξ,w,z) M(z) Ŵ(w) ζ(6z) ζ(w) G(ξ,w,z)` with `ζ(s) = R(s)/(s − 1)`, where
`E = X^{1/2−z} Z^{ξ+z−1} Y^{w−1} e^{(ξ+z−1)²}`; `Aw` and `Bz` are the numerators at the poles
`w = 1` and `z = 1/6`. -/

open Complex MeasureTheory Filter Topology Set

namespace ArtinPrimitiveRoots

namespace C3P

noncomputable section

/-! ### Elementary bounds -/

end

end C3P

end ArtinPrimitiveRoots

end
end

section
section
namespace ArtinPrimitiveRoots

open NumberField Filter Asymptotics Finset

end ArtinPrimitiveRoots

end
end

section
section
namespace ArtinPrimitiveRoots

open NumberField
open scoped nonZeroDivisors

variable {F : Type*} [Field F] [NumberField F]

end ArtinPrimitiveRoots

end
end

section
section
namespace ArtinPrimitiveRoots

open NumberField

theorem T12C_pow_mod3 {M : Type*} [Monoid M] (z : M) (hz : z ^ 3 = 1) (m : ℕ) :
    z ^ m = z ^ (m % 3) := by
  conv_lhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul, hz, one_pow, one_mul]

/-- A prime of norm divisible by `3` has norm at most `3^[F:ℚ]`. -/
theorem T12C_absNorm_le_of_three_dvd {F : Type*} [Field F] [NumberField F] (P : Ideal (𝓞 F))
    (hP0 : P ≠ ⊥) [P.IsMaximal] (h3 : 3 ∣ Ideal.absNorm P) :
    Ideal.absNorm P ≤ 3 ^ Module.finrank ℤ (𝓞 F) := by
  letI := Ideal.Quotient.field P
  have : Finite (𝓞 F ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  letI : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 F ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  obtain ⟨f, hp, hpf⟩ := FiniteField.card (𝓞 F ⧸ P) (ringChar (𝓞 F ⧸ P))
  rw [hcard] at hpf
  rw [hpf] at h3
  have h3p : 3 = ringChar (𝓞 F ⧸ P) :=
    (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.prime_three.dvd_of_dvd_pow h3)
  have h30 : ((3 : ℕ) : 𝓞 F ⧸ P) = 0 := by rw [h3p]; exact ringChar.Nat.cast_ringChar
  have hmem : (3 : 𝓞 F) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat]
    simpa using h30
  have hle : Ideal.span {(3 : 𝓞 F)} ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hmem
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
  rw [Ideal.absNorm_span_singleton] at hdvd
  have hn : Algebra.norm ℤ (3 : 𝓞 F) = 3 ^ Module.finrank ℤ (𝓞 F) := by
    rw [show (3 : 𝓞 F) = algebraMap ℤ (𝓞 F) 3 by simp, Algebra.norm_algebraMap]
  rw [hn, Int.natAbs_pow] at hdvd
  exact Nat.le_of_dvd (by positivity) hdvd

/-- `|J(ρ_P, ρ_P)|^6 / N P^3 = 1` for a prime `P` of norm `> 3^[F:ℚ]` of the cyclotomic field
`F = ℚ(μ_n)`, `3 ∣ n`. -/
theorem T12C_norm_jacobiPhaseSix (n : ℕ) (hn0 : 0 < n) (hn : 3 ∣ n) (F : Type*) [Field F]
    [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) (P : Ideal (𝓞 F))
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hQ : 3 ^ Module.finrank ℤ (𝓞 F) < Ideal.absNorm P) :
    ‖jacobiPhaseSix ι P‖ = 1 := by
  classical
  haveI : P.IsMaximal := hP.isMaximal hP0
  letI := Ideal.Quotient.field P
  have : Finite (𝓞 F ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  letI : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  set Q := Ideal.absNorm P with hQdef
  have hcard : Fintype.card (𝓞 F ⧸ P) = Q := by
    rw [hQdef, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hQ4 : 4 ≤ Q := by
    have : 3 ≤ 3 ^ Module.finrank ℤ (𝓞 F) := by
      have : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) this
    omega
  have h3Q : ¬ 3 ∣ Q := fun h => by
    have := T12C_absNorm_le_of_three_dvd P hP0 h
    omega
  have hcop : Q.Coprime 3 := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3Q))
  -- the cube root of unity
  haveI : NeZero n := ⟨hn0.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  have hζ3 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ (n / 3)) 3 :=
    hζ.pow hn0 (Nat.div_mul_cancel hn).symm
  set ω₀ : 𝓞 F := hζ3.toInteger with hω₀
  have hω : IsPrimitiveRoot ω₀ 3 := hζ3.toInteger_isPrimitiveRoot
  have hωb : IsPrimitiveRoot (Ideal.Quotient.mk P ω₀) 3 :=
    hω.idealQuotient_mk (by omega) hcop
  set ψ : ℂ := ι (ω₀ : F) with hψdef
  have hψ : IsPrimitiveRoot ψ 3 :=
    (hω.map_of_injective RingOfIntegers.coe_injective).map_of_injective ι.injective
  set e := (Q - 1) / 3 with hedef
  have h3e : 3 * e = Q - 1 := by
    have h1 : Ideal.Quotient.mk P ω₀ ^ (Q - 1) = 1 := by
      rw [← hcard]; exact FiniteField.pow_card_sub_one_eq_one _ (hωb.ne_zero (by norm_num))
    have := (hωb.pow_eq_one_iff_dvd _).mp h1
    omega
  -- key lemma
  have KL : ∀ x : 𝓞 F ⧸ P, x ≠ 0 → ∀ i : ℕ, x ^ e = Ideal.Quotient.mk P ω₀ ^ i →
      cubicResidueChar ι P x = ψ ^ i := by
    intro x hx i hi
    have hex : ∃ ω : 𝓞 F, ω ^ 3 = 1 ∧ Ideal.Quotient.mk P ω = x ^ ((Ideal.absNorm P - 1) / 3) :=
      ⟨ω₀ ^ i, by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow], by
        rw [map_pow, ← hi]⟩
    simp only [cubicResidueChar, if_neg hx, dif_pos hex]
    obtain ⟨h1, h2⟩ := hex.choose_spec
    obtain ⟨j, hj, hjω⟩ := hω.eq_pow_of_pow_eq_one h1
    have hmk : Ideal.Quotient.mk P ω₀ ^ j = Ideal.Quotient.mk P ω₀ ^ (i % 3) := by
      rw [← map_pow, hjω, h2, ← T12C_pow_mod3 _ hωb.pow_eq_one]
      exact hi
    have hji : j = i % 3 := hωb.pow_inj hj (Nat.mod_lt _ (by norm_num)) hmk
    rw [← hjω, show ((ω₀ ^ j : 𝓞 F) : F) = (ω₀ : F) ^ j by norm_cast, map_pow, hji, ← T12C_pow_mod3 _ hψ.pow_eq_one]
  have EX : ∀ x : 𝓞 F ⧸ P, x ≠ 0 → ∃ i : ℕ, x ^ e = Ideal.Quotient.mk P ω₀ ^ i := by
    intro x hx
    have : (x ^ e) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, h3e, ← hcard]
      exact FiniteField.pow_card_sub_one_eq_one x hx
    obtain ⟨i, -, hi⟩ := hωb.eq_pow_of_pow_eq_one this
    exact ⟨i, hi.symm⟩
  have Z : cubicResidueChar ι P 0 = 0 := by simp [cubicResidueChar]
  let ρ : MulChar (𝓞 F ⧸ P) ℂ :=
    { toFun := cubicResidueChar ι P
      map_one' := by
        rw [KL 1 one_ne_zero 0 (by simp)]
        simp
      map_mul' := by
        intro x y
        by_cases hx : x = 0
        · simp [hx, Z]
        by_cases hy : y = 0
        · simp [hy, Z]
        obtain ⟨i, hi⟩ := EX x hx
        obtain ⟨j, hj⟩ := EX y hy
        rw [KL x hx i hi, KL y hy j hj, KL (x * y) (mul_ne_zero hx hy) (i + j)
          (by rw [mul_pow, hi, hj, pow_add]), pow_add]
      map_nonunit' := by
        intro a ha
        have : a = 0 := by
          by_contra h
          exact ha (Ne.isUnit h)
        simp [this, Z] }
  have hρ : ∀ x, ρ x = cubicResidueChar ι P x := fun x => rfl
  -- a non-cube
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (𝓞 F ⧸ P)ˣ)
  have hog : orderOf g = Q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, Nat.card_eq_fintype_card,
      hcard]
  obtain ⟨i, hi⟩ := EX (g : 𝓞 F ⧸ P) g.ne_zero
  have hi3 : ¬ 3 ∣ i := by
    intro h
    have h1 : (g : 𝓞 F ⧸ P) ^ e = 1 := by rw [hi, hωb.pow_eq_one_iff_dvd]; exact h
    have h2 : g ^ e = 1 := Units.ext (by simpa using h1)
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hog] at this
    have hepos : 0 < e := by omega
    have := Nat.le_of_dvd hepos this
    omega
  have hρg : ρ g = ψ ^ i := KL _ g.ne_zero i hi
  have hρ1 : ρ ≠ 1 := by
    intro h
    have : ρ g = 1 := by rw [h]; exact MulChar.one_apply_coe g
    rw [hρg, hψ.pow_eq_one_iff_dvd] at this
    exact hi3 this
  have hρ2 : ρ * ρ ≠ 1 := by
    intro h
    have : (ρ * ρ) g = 1 := by rw [h]; exact MulChar.one_apply_coe g
    rw [MulChar.mul_apply, hρg, ← pow_add, hψ.pow_eq_one_iff_dvd] at this
    have : 3 ∣ 2 * i := by rwa [two_mul]
    exact hi3 ((Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) this))
  have hch : ringChar ℂ ≠ ringChar (𝓞 F ⧸ P) := by
    simpa only [ringChar.eq_zero] using (CharP.ringChar_ne_zero_of_finite (𝓞 F ⧸ P)).symm
  have hJ := jacobiSum_mul_jacobiSum_inv hch hρ1 hρ1 hρ2
  rw [← MulChar.star_eq_inv] at hJ
  have hstar : jacobiSum (star ρ) (star ρ) = starRingEnd ℂ (jacobiSum ρ ρ) :=
    jacobiSum_ringHomComp ρ ρ (starRingEnd ℂ)
  rw [hstar, Complex.mul_conj', hcard] at hJ
  have hJn : ‖jacobiSum ρ ρ‖ ^ 2 = Q := by exact_mod_cast hJ
  have hcj : cubicJacobiSum ι P = jacobiSum ρ ρ := by
    rw [cubicJacobiSum, finsum_eq_sum_of_fintype]
    rfl
  rw [jacobiPhaseSix, hcj, norm_mul, norm_inv, norm_pow, norm_pow, Complex.norm_natCast,
    show ‖jacobiSum ρ ρ‖ ^ 6 = (‖jacobiSum ρ ρ‖ ^ 2) ^ 3 by ring, hJn]
  have : (0 : ℝ) < (Q : ℝ) ^ 3 := by have : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
                                     positivity
  rw [← hQdef]
  field_simp

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3P_Row: the principal-row correction `ℋ₁(ξ, w, z)` of Proposition 7.3

`rowLocalFactor Q e θ ξ w z` is `ℋ_{1,𝔭} = (1 − V)(1 − W)(1 − D₁)⁻¹ ℱ_{1,𝔭}` with `ℱ_{1,𝔭}` the
closed form (7.19) at `u = 1`: `Q = N𝔭`, `V = Q^{-6z}`, `W = Q^{-w}`, `D = e Q^{-ξ}` (`e = η(𝔭)`),
`E = θ Q^{4−6ξ} V` (`θ` in the place of `ϑ(𝔭)⁶`), multiplied out:
`[(1 − W) + W(1 − V) + (E((1 − Q⁻¹)(1 − W) + W(1 − V)(1 − W)) − D((1 − V)(1 − W) +
(Q − 1)WV(1 − W)))/(1 − E)] / (1 − D)`.
`rowCorrection` is the product over the exterior primes; on the box `Om` it is continuous,
separately holomorphic and bounded (`‖ℋ_𝔭 − 1‖ ≤ 50 Q^{-9/5}`), and at `(w, z) = (1, 1/6)` it is
`principalCorrection`. -/

open NumberField Complex Filter Topology

namespace ArtinPrimitiveRoots

namespace C3P

end C3P

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3A_Main: (7.12) at `u = 1` from the local multiplicativity of the frequency coefficients

`FreqCoeffLocal F ι` (the remaining cut) says: the coefficient
`a(𝔠, 𝔫, 𝔰, 𝔯) = γ₂(𝔠) ϑ(𝔠𝔫³) F(𝔰, 𝔠𝔫³, u r⁶)` of `ℱ₁` (with `u` the principal frequency element)
is `1` at `(1,1,1,1)` and satisfies `a(P^{e₀}𝔠, P^l 𝔫, P^k 𝔰, P^m 𝔯) =
principalLocalCoeff(N P, η(P), ϑ(P)⁶; e₀, l, k, m) · a(𝔠, 𝔫, 𝔰, 𝔯)` for exterior primes `P` and
exterior `𝔠, 𝔫, 𝔰, 𝔯` prime to `P` (`𝔠` squarefree, `e₀ ≤ 1`). This is (7.16)–(7.17) of the paper.
From it, `chk_exists_cutoff_freqSeries_principalFreq_eq_of_freqCoeffLocal` proves the published cut
`exists_cutoff_freqSeries_principalFreq_eq` verbatim. -/

open NumberField Filter Topology

namespace ArtinPrimitiveRoots

namespace C3A

variable {F : Type*} [Field F] [NumberField F]

/-- The coefficient `γ₂(𝔠) ϑ(𝔠𝔫³) F(𝔰, 𝔠𝔫³, u r⁶)` of `ℱ_u` (7.11). -/
noncomputable def freqCoeff {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪)
    (χ : HeckeChar F 𝔪) (u : SInt 𝔪) (𝔠 𝔫 𝔰 𝔯 : Ideal (𝓞 F)) : ℂ :=
  gaussPhase g 2 𝔠 * χ.thetaChar g (𝔠 * 𝔫 ^ 3) * poissonFactor g 𝔰 (𝔠 * 𝔫 ^ 3) (u * g.gen 𝔯 ^ 6)

/-! ### Elementary lemmas -/

end C3A

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3A_Fac: the local factor on the initial lines

On `Re ξ > 3`, `Re w > 3`, `Re z > 1`, at a prime of norm `Q ≥ 2`:
`∑_e locTerm = (1 − Q^{-6z})⁻¹ (1 − Q^{-w})⁻¹ (1 − η Q^{-ξ}) ℋ_{1,𝔭}(ξ, w, z)` (`hasSum_locTerm`),
and the majorant `‖locTerm e‖ ≤ (Q^{-2})^{e₀+l+k+m}` (`norm_locTerm_le`). -/

open NumberField Filter Topology

namespace ArtinPrimitiveRoots

namespace C3A

section fac

variable (Q : ℕ) (e θ ξ w z : ℂ)

variable {Q e θ ξ w z}

end fac

end C3A

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3R_Hol: holomorphy of series and products of functions on `ℂ³`

A Weierstrass M-test for jointly holomorphic functions on `ℂ × ℂ × ℂ`: if every `f i` is
holomorphic on an open `V` containing the closed `r`-balls around the points of an open
preconnected `s`, and `‖f i‖ ≤ u i` on `V` with `∑ u i < ∞`, then `∑' i, f i` is holomorphic on
`s` (Cauchy estimates on the three coordinate lines bound the derivatives by `3 u i / r`).
The product version goes through `exp ∘ ∑ log (1 + f i)`. -/

open Complex Filter Topology Metric

namespace ArtinPrimitiveRoots

namespace L3R

end L3R

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3R_Loc: the local factors `ℋ_{u,𝔭}` of Proposition 7.3 on the first region

* `Vreg`: the region `Re ξ > .9978, Re w > .0028, Re z > .3998`, which contains the closed
  `10⁻⁴`-balls around the points of `regionOne`.
* `rlU Q e θ c`: the closed form (7.19) times `(1 − V)(1 − W)/(1 − D)` with `W = c Q^{-w}`,
  `D = e Q^{-ξ}` (for `𝔭 ∤ u`, `c = χ_𝔭(u)` and `e = η(𝔭) conj χ_𝔭(u)`); on `Vreg`,
  `‖rlU − 1‖ ≤ 50 Q^{-(1 + 1/2000)}` for `Q ≥ 100` ((7.20)).
* `ramLocal Q c`: `(1 − V) ∑_e c(e) X^e` for a coefficient table `c` with the support and size
  properties of (7.17)–(7.18) at `𝔭 ∣ u` (`RamHyp`); on `Vreg`, `‖ramLocal − 1‖ ≤ 32 Q^{-1/2000}`
  ((7.22)), and it is holomorphic on `regionOne`. -/

open NumberField Complex Filter Topology Metric

namespace ArtinPrimitiveRoots

namespace L3R

open C3A

/-! ### Regions -/

/-! ### Powers of `Q` -/

/-! ### The unramified factor -/

end L3R

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3R_Cut: the arithmetic input `CoeffU` for a general frequency `u`

`CoeffU F ι` collects (7.14)–(7.18) for `u = freqElt g r` and the coefficients
`a_u(𝔠, 𝔫, 𝔰, 𝔯) = γ₂(𝔠) ϑ(𝔠𝔫³) F(𝔰, 𝔠𝔫³, u r⁶)` (C3A's `freqCoeff`):

* (i) `a_u(1,1,1,1) = 1`;
* (ii) cross-prime multiplicativity at an exterior prime `P`;
* (iii) at `P ∤ 𝔲`: `θ = χ_P(u)` is a sixth root of unity and
  `a_u(P^{e₀}, P^l, P^k, P^m) = θ^k θ̄^{e₀+3l} · principalLocalCoeff(Q, η(P), ϑ(P)⁶; e₀, l, k, m)`
  ((7.14): the multiplier `χ_P(h_P)^{k−t}`);
* (iv) at `P ∣ 𝔲`: `χ_P(u) = 0`, `a_u(1, 1, P^k, P^m) = 1_{k=0}`, `a_u = 0` for `k ≥ 2`, and
  `‖a_u(P^{e₀}, P^l, P^k, P^m)‖ ≤ Q^{e₀+3l} √Q^k` ((7.17)–(7.18)).

Also the local algebra at `P ∤ 𝔲`: the twisted table sums to C3A's closed form with
`W = θ Q^{-w}`, `D = η θ̄ Q^{-ξ}` (`hasSum_locTermU`). -/

open NumberField Filter Topology

namespace ArtinPrimitiveRoots

namespace L3R

open C3A

/-- **The arithmetic input** for a general frequency. -/
def CoeffU (F : Type*) [Field F] [NumberField F] (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (r : FreqClass 𝔪),
      freqCoeff g χ (freqElt g r) ⊤ ⊤ ⊤ ⊤ = 1 ∧
      (∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → ∀ e₀ l k m : ℕ, e₀ ≤ 1 →
        ∀ 𝔠 𝔫 𝔰 𝔯 : Ideal (𝓞 F), IsExterior 𝔪 𝔠 → Squarefree 𝔠 → IsExterior 𝔪 𝔫 →
          IsExterior 𝔪 𝔰 → IsExterior 𝔪 𝔯 → ¬ 𝔠 ≤ P → ¬ 𝔫 ≤ P → ¬ 𝔰 ≤ P → ¬ 𝔯 ≤ P →
          freqCoeff g χ (freqElt g r) (P ^ e₀ * 𝔠) (P ^ l * 𝔫) (P ^ k * 𝔰) (P ^ m * 𝔯) =
            freqCoeff g χ (freqElt g r) (P ^ e₀) (P ^ l) (P ^ k) (P ^ m) *
              freqCoeff g χ (freqElt g r) 𝔠 𝔫 𝔰 𝔯) ∧
      (∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → ¬ r.1.1 ≤ P →
        residueSymbol ι 𝔪 P (freqElt g r) ^ 6 = 1 ∧
        ∀ e₀ l k m : ℕ, e₀ ≤ 1 →
          freqCoeff g χ (freqElt g r) (P ^ e₀) (P ^ l) (P ^ k) (P ^ m) =
            residueSymbol ι 𝔪 P (freqElt g r) ^ k *
              starRingEnd ℂ (residueSymbol ι 𝔪 P (freqElt g r)) ^ (e₀ + 3 * l) *
              C3A.principalLocalCoeff (Ideal.absNorm P) (χ.toFun P)
                (starRingEnd ℂ (jacobiPhaseSix ι P) * χ.toFun P ^ 6) e₀ l k m) ∧
      (∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → r.1.1 ≤ P →
        residueSymbol ι 𝔪 P (freqElt g r) = 0 ∧
        (∀ k m : ℕ, freqCoeff g χ (freqElt g r) (P ^ 0) (P ^ 0) (P ^ k) (P ^ m) =
          if k = 0 then 1 else 0) ∧
        (∀ e₀ l k m : ℕ, 2 ≤ k → freqCoeff g χ (freqElt g r) (P ^ e₀) (P ^ l) (P ^ k) (P ^ m) = 0) ∧
        (∀ e₀ l k m : ℕ, e₀ ≤ 1 →
          ‖freqCoeff g χ (freqElt g r) (P ^ e₀) (P ^ l) (P ^ k) (P ^ m)‖ ≤
            (Ideal.absNorm P : ℝ) ^ (e₀ + 3 * l) * Real.sqrt (Ideal.absNorm P) ^ k))

/-! ### The twisted table -/

end L3R

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

lemma sAddChar_congr {𝔪 : Ideal (𝓞 F)} (x x' : F)
    (H : ∀ y : F, (x - y ∈ (placesOf 𝔪).integer F) ↔ (x' - y ∈ (placesOf 𝔪).integer F)) :
    sAddChar 𝔪 x = sAddChar 𝔪 x' := by
  classical
  let G : (F → Prop) → ℂ := fun p => if h : ∃ y, p y then
    Complex.exp (-(2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F h.choose : ℚ) : ℂ)) else 0
  have e1 : sAddChar 𝔪 x = G (fun y => x - y ∈ (placesOf 𝔪).integer F ∧
      ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1) := by
    unfold sAddChar; rfl
  have e2 : sAddChar 𝔪 x' = G (fun y => x' - y ∈ (placesOf 𝔪).integer F ∧
      ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1) := by
    unfold sAddChar; rfl
  rw [e1, e2]
  congr 1
  funext y
  exact propext (and_congr_left' (H y))

/-- `e` is invariant under translation by `R`. -/
lemma sAddChar_add_mem {𝔪 : Ideal (𝓞 F)} (x r : F) (hr : r ∈ (placesOf 𝔪).integer F) :
    sAddChar 𝔪 (x + r) = sAddChar 𝔪 x := by
  have key : ∀ y : F, (x + r - y ∈ (placesOf 𝔪).integer F) ↔ (x - y ∈ (placesOf 𝔪).integer F) := by
    intro y
    constructor
    · intro h
      have := sub_mem h hr
      rwa [show x + r - y - r = x - y by ring] at this
    · intro h
      have := add_mem h hr
      rwa [show x - y + r = x + r - y by ring] at this
  exact sAddChar_congr _ _ key

/-- `e` is trivial on `R`. -/
lemma sAddChar_of_mem {𝔪 : Ideal (𝓞 F)} (x : F) (hx : x ∈ (placesOf 𝔪).integer F) :
    sAddChar 𝔪 x = 1 := by
  have hex : ∃ y : F, x - y ∈ (placesOf 𝔪).integer F ∧
      ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1 :=
    ⟨0, by simpa using hx, fun v _ => by simp⟩
  rw [sAddChar, dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  set y := hex.choose
  have hy : y ∈ (placesOf 𝔪).integer F := by
    have := sub_mem hx h1
    rwa [sub_sub_cancel] at this
  have hall : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F y ≤ 1 := by
    intro v
    by_cases hv : v ∈ placesOf 𝔪
    · exact h2 v hv
    · exact hy v hv
  obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F y hall
  have htr : Algebra.trace ℚ F y = ((Algebra.trace ℤ (𝓞 F) z : ℤ) : ℚ) := by
    rw [← hz, Algebra.coe_trace_int]
  rw [htr]
  have := Complex.exp_int_mul_two_pi_mul_I (-(Algebra.trace ℤ (𝓞 F) z))
  rw [← this]
  congr 1
  push_cast
  ring

/-- The generator of the unit ideal is a unit of `R`. -/
lemma isUnit_gen_top {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) :
    IsUnit (g.gen ⊤) := by
  have h := g.span_gen ⊤ ⟨top_ne_bot, top_sup_eq _⟩
  rw [Ideal.map_top] at h
  exact Ideal.span_singleton_eq_top.mp h

lemma div_gen_top_mem {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) (x : F)
    (hx : x ∈ (placesOf 𝔪).integer F) : x / (g.gen ⊤ : F) ∈ (placesOf 𝔪).integer F := by
  obtain ⟨u, hu⟩ := isUnit_gen_top g
  have hinv : ((↑(u⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = ((g.gen ⊤ : SInt 𝔪) : F)⁻¹ := by
    rw [← hu]
    have h1 : ((↑u : SInt 𝔪) : F) * ((↑(u⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = 1 := by
      rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
    exact (eq_inv_of_mul_eq_one_right h1)
  rw [div_eq_mul_inv, ← hinv]
  exact mul_mem hx (SetLike.coe_mem _)

lemma subsingleton_quot_top {𝔪 : Ideal (𝓞 F)} :
    Subsingleton (SInt 𝔪 ⧸ (⊤ : Ideal (𝓞 F)).map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  rw [Ideal.map_top]
  infer_instance

lemma finsum_quot_top {𝔪 : Ideal (𝓞 F)}
    (f : SInt 𝔪 ⧸ (⊤ : Ideal (𝓞 F)).map (algebraMap (𝓞 F) (SInt 𝔪)) → ℂ) :
    ∑ᶠ x, f x = f 0 := by
  have := subsingleton_quot_top (𝔪 := 𝔪)
  exact finsum_eq_single f 0 (fun x hx => absurd (Subsingleton.elim x 0) hx)

lemma normalizedFactors_top : normalizedFactors (⊤ : Ideal (𝓞 F)) = 0 := by
  rw [← Ideal.one_eq_top, normalizedFactors_one]

lemma residueSymbol_top (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 ⊤ x = 1 := by
  simp [residueSymbol, normalizedFactors_top]

lemma gaussPhase_top {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) (j : ℕ) :
    gaussPhase g j ⊤ = 1 := by
  rw [gaussPhase, finsum_quot_top, residueSymbol_top, one_pow, one_mul,
    sAddChar_of_mem _ (div_gen_top_mem g _ (SetLike.coe_mem _))]
  simp [Ideal.absNorm_top]

lemma thetaChar_top {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪)
    (χ : HeckeChar F 𝔪) : χ.thetaChar g ⊤ = 1 := by
  have h1 : χ.toFun ⊤ = 1 := by
    have := χ.map_principal' 1 one_ne_zero (by simp)
    rwa [Ideal.span_singleton_one] at this
  simp [HeckeChar.thetaChar, gaussLambda, gaussG, normalizedFactors_top, h1]

lemma gaussSumAt_top {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) (k : F)
    (hk : k ∈ (placesOf 𝔪).integer F) : gaussSumAt g ⊤ k = 1 := by
  rw [gaussSumAt, finsum_quot_top, residueSymbol_top, one_mul,
    sAddChar_of_mem _ (div_gen_top_mem g _ (mul_mem hk (SetLike.coe_mem _)))]

lemma poissonFactor_top {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) (h : SInt 𝔪) :
    poissonFactor g ⊤ ⊤ h = 1 := by
  rw [poissonFactor, finsum_quot_top, if_pos (by rw [Ideal.map_top]; exact Submodule.mem_top),
    residueSymbol_top, one_mul,
    gaussSumAt_top g _ (div_gen_top_mem g _ (SetLike.coe_mem _))]

/-- **(i)** `a(1,1,1,1) = 1`, for every `h` in place of `u`. -/
theorem coeff_top {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) (χ : HeckeChar F 𝔪)
    (h : SInt 𝔪) :
    gaussPhase g 2 ⊤ * χ.thetaChar g (⊤ * ⊤ ^ 3) * poissonFactor g ⊤ (⊤ * ⊤ ^ 3) h = 1 := by
  rw [← Ideal.one_eq_top, one_pow, one_mul, Ideal.one_eq_top, gaussPhase_top, thetaChar_top, poissonFactor_top]
  ring

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

lemma coe_algebraMap_SInt (x : 𝓞 F) :
    ((algebraMap (𝓞 F) (SInt 𝔪) x : SInt 𝔪) : F) = (x : F) := rfl

lemma card_quot (P : Ideal (𝓞 F)) (hP0 : P ≠ ⊥) [Fintype (𝓞 F ⧸ P)] :
    Fintype.card (𝓞 F ⧸ P) = Ideal.absNorm P := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

lemma sexticResidueSymbol_eq_of_mk_eq (ι : F →+* ℂ) (P : Ideal (𝓞 F)) (x y : SInt 𝔪)
    (h : Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x =
      Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) y) :
    sexticResidueSymbol ι 𝔪 P x = sexticResidueSymbol ι 𝔪 P y := by
  unfold sexticResidueSymbol
  rw [h]

lemma residueSymbol_congr (ι : F →+* ℂ) (𝔞 : Ideal (𝓞 F)) (x y : SInt 𝔪)
    (h : x - y ∈ 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    residueSymbol ι 𝔪 𝔞 x = residueSymbol ι 𝔪 𝔞 y := by
  unfold residueSymbol
  congr 1
  refine Multiset.map_congr rfl fun P hP => ?_
  apply sexticResidueSymbol_eq_of_mk_eq
  rw [Ideal.Quotient.eq]
  exact Ideal.map_mono (Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hP)) h

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

lemma mem_map_iff (g : AllowedGen ι 𝔪) (I : Ideal (𝓞 F)) (hI : IsExterior 𝔪 I) (x : SInt 𝔪) :
    x ∈ I.map (algebraMap (𝓞 F) (SInt 𝔪)) ↔ ∃ r : SInt 𝔪, x = g.gen I * r := by
  rw [← g.span_gen I hI, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨r, hr⟩; exact ⟨r, by rw [← hr, mul_comm]⟩
  · rintro ⟨r, hr⟩; exact ⟨r, by rw [hr, mul_comm]⟩

lemma div_gen_mem (g : AllowedGen ι 𝔪) (I : Ideal (𝓞 F)) (hI : IsExterior 𝔪 I) (x : SInt 𝔪)
    (hx : x ∈ I.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    (x : F) / (g.gen I : F) ∈ (placesOf 𝔪).integer F := by
  obtain ⟨r, rfl⟩ := (mem_map_iff g I hI x).mp hx
  have h0 := gen_ne_zero g I hI
  rw [Subalgebra.coe_mul, mul_div_cancel_left₀ _ h0]
  exact r.2

lemma gaussSumAt_add_mem (g : AllowedGen ι 𝔪) (𝔄 : Ideal (𝓞 F)) (h𝔄 : IsExterior 𝔪 𝔄) (k : F)
    (a : SInt 𝔪) (ha : a ∈ 𝔄.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    gaussSumAt g 𝔄 (k + a) = gaussSumAt g 𝔄 k := by
  unfold gaussSumAt
  refine finsum_congr fun v => ?_
  congr 1
  have hmem : (a : F) / (g.gen 𝔄 : F) * (quotLift v : F) ∈ (placesOf 𝔪).integer F :=
    mul_mem (div_gen_mem g 𝔄 h𝔄 a ha) (quotLift v).2
  rw [show (k + a) * (quotLift v : F) / (g.gen 𝔄 : F) =
      k * (quotLift v : F) / (g.gen 𝔄 : F) + (a : F) / (g.gen 𝔄 : F) * (quotLift v : F) by ring]
  exact sAddChar_add_mem _ _ hmem

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

/-- The coefficient at `u = 1`: `γ₂(𝔠) ϑ(𝔠𝔫³) F(𝔰, 𝔠𝔫³, gen(𝔯)⁶)`. -/
noncomputable def coeffOne {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪)
    (χ : HeckeChar F 𝔪) (𝔠 𝔫 𝔰 𝔯 : Ideal (𝓞 F)) : ℂ :=
  gaussPhase g 2 𝔠 * χ.thetaChar g (𝔠 * 𝔫 ^ 3) *
    poissonFactor g 𝔰 (𝔠 * 𝔫 ^ 3) (g.gen 𝔯 ^ 6)

/-! ### Elementary lemmas -/

lemma smallPrimesDvd_mono {N N' : ℕ} (h : N' ≤ N) {𝔪 : Ideal (𝓞 F)}
    (hs : SmallPrimesDvd N 𝔪) : SmallPrimesDvd N' 𝔪 :=
  fun P hP hP0 hle => hs P hP hP0 (hle.trans h)

lemma isExterior_top (𝔪 : Ideal (𝓞 F)) : IsExterior 𝔪 ⊤ := ⟨top_ne_bot, top_sup_eq _⟩

lemma isExterior_mul {𝔪 I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (hJ : IsExterior 𝔪 J) :
    IsExterior 𝔪 (I * J) := by
  refine ⟨mul_ne_zero hI.1 hJ.1, ?_⟩
  have h1 : IsCoprime I 𝔪 := Ideal.isCoprime_iff_sup_eq.mpr hI.2
  have h2 : IsCoprime J 𝔪 := Ideal.isCoprime_iff_sup_eq.mpr hJ.2
  exact Ideal.isCoprime_iff_sup_eq.mp (h1.mul_left h2)

lemma isExterior_pow {𝔪 I : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (n : ℕ) :
    IsExterior 𝔪 (I ^ n) := by
  induction n with
  | zero => rw [pow_zero, Ideal.one_eq_top]; exact isExterior_top 𝔪
  | succ k ih => rw [pow_succ]; exact isExterior_mul ih hI

lemma normalizedFactors_prime_pow {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (t : ℕ) :
    normalizedFactors (P ^ t) = Multiset.replicate t P := by
  have hirr : Irreducible P := (Ideal.prime_of_isPrime hP0 hP).irreducible
  rw [normalizedFactors_pow, normalizedFactors_irreducible hirr, normalize_eq,
    Multiset.nsmul_singleton]

lemma thetaChar_prime_pow {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪)
    (χ : HeckeChar F 𝔪) {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (t : ℕ) :
    χ.thetaChar g (P ^ t) = χ.thetaChar g P ^ t := by
  have hχ : χ.toFun (P ^ t) = χ.toFun P ^ t := by
    induction t with
    | zero =>
      rw [pow_zero, pow_zero, Ideal.one_eq_top]
      have := χ.map_principal' 1 one_ne_zero (by simp)
      rwa [Ideal.span_singleton_one] at this
    | succ k ih => rw [pow_succ, χ.map_mul', ih, pow_succ]
  have h1 := normalizedFactors_prime_pow hP hP0 t
  have h0 := normalizedFactors_prime_pow hP hP0 1
  rw [pow_one, Multiset.replicate_one] at h0
  simp only [HeckeChar.thetaChar, gaussLambda, gaussG, h1, h0, Multiset.map_replicate,
    Multiset.prod_replicate, Multiset.map_singleton, Multiset.prod_singleton, hχ, map_pow]
  ring

lemma gaussLambda_prime_pow_six {ι : F →+* ℂ} {P : Ideal (𝓞 F)} (hP : P.IsPrime)
    (hP0 : P ≠ ⊥) : gaussLambda ι P ^ 6 = jacobiPhaseSix ι P := by
  have h0 := normalizedFactors_prime_pow hP hP0 1
  rw [pow_one, Multiset.replicate_one] at h0
  simp only [gaussLambda, h0, Multiset.map_singleton, Multiset.prod_singleton, jacobiPhaseSix]
  have hs : ((Real.sqrt (Ideal.absNorm P) : ℝ) : ℂ) ^ 2 = (Ideal.absNorm P : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; rfl
  have : (-(((Real.sqrt (Ideal.absNorm P) : ℝ) : ℂ)⁻¹ * cubicJacobiSum ι P)) ^ 6 =
      ((((Real.sqrt (Ideal.absNorm P) : ℝ) : ℂ) ^ 2) ^ 3)⁻¹ * cubicJacobiSum ι P ^ 6 := by
    rw [neg_pow, mul_pow, inv_pow, ← pow_mul]; norm_num
  rw [this, hs]

/-- The table algebra: `γ₂^{e₀} ϑ^{e₀+3l} · poissonLocal = principalLocalCoeff`. -/
lemma principalLocalCoeff_eq (Q : ℕ) (η θ γ₁ γ₂ ϑ : ℂ) (hHD : γ₁ * γ₂ * ϑ = -η)
    (h6 : ϑ ^ 6 = θ) (e₀ l k m : ℕ) (he : e₀ ≤ 1) :
    γ₂ ^ e₀ * ϑ ^ (e₀ + 3 * l) * poissonLocal Q γ₁ e₀ l k m =
      principalLocalCoeff Q η θ e₀ l k m := by
  have hl : ∀ l, Even l → ϑ ^ (3 * l) = θ ^ (l / 2) := by
    intro l hl
    obtain ⟨d, rfl⟩ := hl
    rw [← h6, ← pow_mul, show d + d = 2 * d by ring,
      Nat.mul_div_cancel_left d (by norm_num : 0 < 2)]
    congr 1; ring
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he with rfl | rfl
  · simp only [poissonLocal, principalLocalCoeff, if_true, pow_zero, one_mul, zero_add]
    by_cases hl0 : l = 0
    · subst hl0; simp
    · rw [if_neg hl0, if_neg hl0]
      by_cases hle : Even l
      · rw [if_pos hle, if_pos hle, hl l hle]
        split_ifs <;> ring
      · rw [if_neg hle, if_neg hle, mul_zero]
  · simp only [poissonLocal, principalLocalCoeff, one_ne_zero, if_false, true_and, pow_one]
    by_cases hle : Even l
    · rw [if_pos hle, if_pos hle, pow_add, pow_one, hl l hle]
      split_ifs
      · linear_combination ((θ ^ (l / 2)) * (Real.sqrt Q : ℂ) * (Q : ℂ) ^ (3 * l)) * hHD
      · linear_combination ((θ ^ (l / 2)) * (Real.sqrt Q : ℂ) * (Q : ℂ) ^ (3 * l) *
          ((Q : ℂ) - 1)) * hHD
      · ring
    · rw [if_neg hle, if_neg hle, mul_zero]

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

/-- Discreteness: a valuation strictly above `exp(-(j+1))` is at least `exp(-j)`. -/
lemma exp_le_of_lt {γ : ℤᵐ⁰} {j : ℤ} (h : exp (j - 1) < γ) : exp j ≤ γ := by
  have hγ : γ ≠ 0 := ne_zero_of_lt h
  rw [← exp_log hγ] at h ⊢
  rw [exp_lt_exp] at h
  rw [exp_le_exp]
  omega

lemma exp_le_val_of_not_mem (hv : v ∉ placesOf 𝔪) (j : ℕ) (r : SInt 𝔪)
    (h : r ∉ (v.asIdeal ^ (j + 1)).map (algebraMap (𝓞 F) (SInt 𝔪))) :
    exp (-(j : ℤ)) ≤ v.valuation F (r : F) := by
  rw [mem_map_pow_iff hv, not_le] at h
  apply exp_le_of_lt
  convert h using 2
  push_cast; ring

lemma le_of_mul_le_mul_ne {a b c : ℤᵐ⁰} (h : a * c ≤ b * c) (hc : c ≠ 0) : a ≤ b := by
  have := mul_le_mul_right h c⁻¹
  rwa [mul_comm c⁻¹, mul_comm c⁻¹, mul_inv_cancel_right₀ hc, mul_inv_cancel_right₀ hc] at this

lemma isExterior_mul {I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (hJ : IsExterior 𝔪 J) :
    IsExterior 𝔪 (I * J) := by
  refine ⟨mul_ne_zero hI.1 hJ.1, ?_⟩
  have h1 : IsCoprime I 𝔪 := Ideal.isCoprime_iff_sup_eq.mpr hI.2
  have h2 : IsCoprime J 𝔪 := Ideal.isCoprime_iff_sup_eq.mpr hJ.2
  exact Ideal.isCoprime_iff_sup_eq.mp (h1.mul_left h2)

lemma isExterior_pow {I : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (n : ℕ) :
    IsExterior 𝔪 (I ^ n) := by
  induction n with
  | zero => rw [pow_zero, Ideal.one_eq_top]; exact ⟨top_ne_bot, top_sup_eq _⟩
  | succ k ih => rw [pow_succ]; exact isExterior_mul ih hI

/-- A uniformizer in `𝓞`. -/
lemma exists_uniformizer : ∃ p : 𝓞 F, v.valuation F (algebraMap (𝓞 F) F p) = exp (-1 : ℤ) := by
  obtain ⟨p, hp⟩ := v.intValuation_exists_uniformizer
  exact ⟨p, by rw [val_alg, hp]⟩

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

/-- `x` has a witness in the definition of `sAddChar`. -/
def HasWit (𝔪 : Ideal (𝓞 F)) (x : F) : Prop :=
  ∃ y : F, x - y ∈ (placesOf 𝔪).integer F ∧ ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1

/-- The value of `e` through any witness. -/
lemma sAddChar_eq_of_wit {x y : F} (h1 : x - y ∈ (placesOf 𝔪).integer F)
    (h2 : ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1) :
    sAddChar 𝔪 x =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F y : ℚ) : ℂ)) := by
  have hex : ∃ y : F, x - y ∈ (placesOf 𝔪).integer F ∧
      ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1 := ⟨y, h1, h2⟩
  rw [sAddChar, dif_pos hex]
  obtain ⟨k1, k2⟩ := hex.choose_spec
  set y' := hex.choose
  have hd : y' - y ∈ (placesOf 𝔪).integer F := by
    have := sub_mem h1 k1
    rwa [show x - y - (x - y') = y' - y by ring] at this
  have hall : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (y' - y) ≤ 1 := by
    intro v
    by_cases hv : v ∈ placesOf 𝔪
    · exact (Valuation.map_sub _ _ _).trans (max_le (k2 v hv) (h2 v hv))
    · exact hd v hv
  obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F _ hall
  have htr : Algebra.trace ℚ F y' = Algebra.trace ℚ F y + ((Algebra.trace ℤ (𝓞 F) z : ℤ) : ℚ) := by
    rw [Algebra.coe_trace_int, show ((z : 𝓞 F) : F) = algebraMap (𝓞 F) F z from rfl, hz, map_sub]
    ring
  rw [htr]
  push_cast
  rw [mul_add, Complex.exp_add]
  have := Complex.exp_int_mul_two_pi_mul_I (-(Algebra.trace ℤ (𝓞 F) z))
  rw [show -(2 * (Real.pi : ℂ) * Complex.I) * ((Algebra.trace ℤ (𝓞 F) z : ℤ) : ℂ) =
      ((-(Algebra.trace ℤ (𝓞 F) z) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring, this,
    mul_one]

/-- `e` is additive on elements with witnesses. -/
lemma sAddChar_add {x x' : F} (h : HasWit 𝔪 x) (h' : HasWit 𝔪 x') :
    sAddChar 𝔪 (x + x') = sAddChar 𝔪 x * sAddChar 𝔪 x' := by
  obtain ⟨y, hy1, hy2⟩ := h
  obtain ⟨y', hy1', hy2'⟩ := h'
  have hs1 : x + x' - (y + y') ∈ (placesOf 𝔪).integer F := by
    rw [show x + x' - (y + y') = (x - y) + (x' - y') by ring]; exact add_mem hy1 hy1'
  have hs2 : ∀ v ∈ placesOf 𝔪, v.valuation F (y + y') ≤ 1 :=
    fun v hv => (Valuation.map_add _ _ _).trans (max_le (hy2 v hv) (hy2' v hv))
  rw [sAddChar_eq_of_wit hs1 hs2, sAddChar_eq_of_wit hy1 hy2, sAddChar_eq_of_wit hy1' hy2',
    ← Complex.exp_add, map_add]
  push_cast
  ring_nf

/-- A witness exists when `x I ⊆ R` for an ideal `I` coprime to `𝔪`. -/
lemma hasWit_of_mul_mem (x : F) (I : Ideal (𝓞 F)) (hI : I ⊔ 𝔪 = ⊤)
    (hx : ∀ i ∈ I, x * algebraMap (𝓞 F) F i ∈ (placesOf 𝔪).integer F) : HasWit 𝔪 x := by
  obtain ⟨b, d, hd, hbd⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  set N := Ideal.absNorm (Ideal.span {d}) with hN
  have hcop : IsCoprime I (𝔪 ^ N) := (Ideal.isCoprime_iff_sup_eq.mpr hI).pow_right
  obtain ⟨i, hi, w, hw, hiw⟩ := hcop.exists
  refine ⟨x * algebraMap (𝓞 F) F w, ?_, fun v hv => ?_⟩
  · have hw' : algebraMap (𝓞 F) F w = 1 - algebraMap (𝓞 F) F i := by
      rw [← map_one (algebraMap (𝓞 F) F), ← hiw, map_add]; ring
    have : x - x * algebraMap (𝓞 F) F w = x * algebraMap (𝓞 F) F i := by
      rw [hw']; ring
    rw [this]; exact hx i hi
  · have hvm : 𝔪 ≤ v.asIdeal := hv
    -- `d ∉ v^N`
    have hdN : d ∉ v.asIdeal ^ N := by
      intro hmem
      have hle : Ideal.span {d} ≤ v.asIdeal ^ N := (Ideal.span_singleton_le_iff_mem _).2 hmem
      have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
      rw [map_pow] at hdvd
      have hN0 : N ≠ 0 := by
        rw [hN, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hd0
      have h2 : 2 ≤ Ideal.absNorm v.asIdeal := by
        have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
          rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
        have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
          rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
        omega
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hdvd
      have h3 : 2 ^ N ≤ Ideal.absNorm v.asIdeal ^ N := Nat.pow_le_pow_left h2 N
      have h4 : N < 2 ^ N := Nat.lt_two_pow_self
      omega
    have hvd : exp (-(N : ℤ)) < v.valuation F (algebraMap (𝓞 F) F d) := by
      rw [val_alg, ← not_le, v.intValuation_le_pow_iff_mem]; exact hdN
    have hvw : v.valuation F (algebraMap (𝓞 F) F w) ≤ exp (-(N : ℤ)) := by
      rw [val_alg, v.intValuation_le_pow_iff_mem]
      exact Ideal.pow_right_mono hvm N hw
    have hdpos : v.valuation F (algebraMap (𝓞 F) F d) ≠ 0 := ne_zero_of_lt hvd
    have hxd : x * algebraMap (𝓞 F) F d = algebraMap (𝓞 F) F b := by
      rw [← hbd, div_mul_cancel₀]
      exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hd0
    have key : v.valuation F (x * algebraMap (𝓞 F) F w) * v.valuation F (algebraMap (𝓞 F) F d) ≤
        1 * v.valuation F (algebraMap (𝓞 F) F d) := by
      rw [← map_mul, show x * algebraMap (𝓞 F) F w * algebraMap (𝓞 F) F d =
        algebraMap (𝓞 F) F b * algebraMap (𝓞 F) F w by rw [← hxd]; ring, map_mul]
      calc v.valuation F (algebraMap (𝓞 F) F b) * v.valuation F (algebraMap (𝓞 F) F w)
          ≤ 1 * v.valuation F (algebraMap (𝓞 F) F d) :=
            mul_le_mul' (v.valuation_le_one b) (hvw.trans hvd.le)
        _ = _ := rfl
    exact le_of_mul_le_mul_ne key hdpos

variable {ι : F →+* ℂ}

/-- `a / gen 𝔞` has a witness. -/
lemma hasWit_div_gen (g : AllowedGen ι 𝔪) (𝔞 : Ideal (𝓞 F)) (h𝔞 : IsExterior 𝔪 𝔞)
    (a : SInt 𝔪) : HasWit 𝔪 ((a : F) / (g.gen 𝔞 : F)) := by
  apply hasWit_of_mul_mem _ 𝔞 h𝔞.2
  intro i hi
  have hm : algebraMap (𝓞 F) (SInt 𝔪) i ∈ 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
    Ideal.mem_map_of_mem _ hi
  have := C3B.div_gen_mem g 𝔞 h𝔞 _ hm
  rw [coe_alg] at this
  rw [show (a : F) / (g.gen 𝔞 : F) * algebraMap (𝓞 F) F i =
    (a : F) * (algebraMap (𝓞 F) F i / (g.gen 𝔞 : F)) by ring]
  exact mul_mem a.2 this

/-- `e(a/c + b/c) = e(a/c) e(b/c)` for `c` an allowed generator. -/
lemma sAddChar_div_gen_add (g : AllowedGen ι 𝔪) (𝔞 : Ideal (𝓞 F)) (h𝔞 : IsExterior 𝔪 𝔞)
    (a b : SInt 𝔪) :
    sAddChar 𝔪 ((a : F) / (g.gen 𝔞 : F) + (b : F) / (g.gen 𝔞 : F)) =
      sAddChar 𝔪 ((a : F) / (g.gen 𝔞 : F)) * sAddChar 𝔪 ((b : F) / (g.gen 𝔞 : F)) :=
  sAddChar_add (hasWit_div_gen g 𝔞 h𝔞 a) (hasWit_div_gen g 𝔞 h𝔞 b)

/-! ### The inverse different -/

/-- For `P ∤ 𝔇`, some `z ∈ P⁻¹` has non-integral trace. -/
lemma exists_trace_not_int (P : Ideal (𝓞 F)) (hP0 : P ≠ ⊥)
    (hD : ¬ differentIdeal ℤ (𝓞 F) ≤ P) :
    ∃ z : F, (∀ p ∈ P, ∃ a : 𝓞 F, z * algebraMap (𝓞 F) F p = algebraMap (𝓞 F) F a) ∧
      ∀ n : ℤ, Algebra.trace ℚ F z ≠ n := by
  rw [differentialIdeal_le_iff (K := ℚ) (L := F) hP0, Submodule.map_le_iff_le_comap] at hD
  rw [SetLike.not_le_iff_exists] at hD
  obtain ⟨z, hz, hz'⟩ := hD
  have hP' : (P : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := by
    simpa using hP0
  have hz2 : z ∈ ((P : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)⁻¹) := hz
  rw [FractionalIdeal.mem_inv_iff hP'] at hz2
  refine ⟨z, fun p hp => ?_, fun n hn => hz' ?_⟩
  · have := hz2 (algebraMap (𝓞 F) F p) ((FractionalIdeal.mem_coeIdeal _).2 ⟨p, hp, rfl⟩)
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).1 this
    exact ⟨a, ha.symm⟩
  · simp only [Submodule.mem_comap, LinearMap.coe_restrictScalars, Submodule.mem_one]
    exact ⟨n, by rw [hn]; simp⟩

/-- For `P` exterior and `z ∈ P⁻¹` with non-integral trace, `e(z) ≠ 1`. -/
lemma sAddChar_ne_one_of_dual (P : Ideal (𝓞 F)) (hPS : P ⊔ 𝔪 = ⊤) (z : F)
    (hz : ∀ p ∈ P, ∃ a : 𝓞 F, z * algebraMap (𝓞 F) F p = algebraMap (𝓞 F) F a)
    (htr : ∀ n : ℤ, Algebra.trace ℚ F z ≠ n) : sAddChar 𝔪 z ≠ 1 := by
  have hw : ∀ v ∈ placesOf 𝔪, v.valuation F z ≤ 1 := by
    intro v hv
    have hvm : 𝔪 ≤ v.asIdeal := hv
    have hPv : ¬ P ≤ v.asIdeal := by
      intro h
      apply v.isPrime.ne_top
      rw [eq_top_iff, ← hPS]
      exact sup_le h hvm
    obtain ⟨p, hp, hpv⟩ := SetLike.not_le_iff_exists.mp hPv
    obtain ⟨a, ha⟩ := hz p hp
    have h1 : v.valuation F (algebraMap (𝓞 F) F p) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hpv
    have := v.valuation_le_one (K := F) a
    change v.valuation F (algebraMap (𝓞 F) F a) ≤ 1 at this
    rw [← ha, map_mul, h1, mul_one] at this
    exact this
  rw [sAddChar_eq_of_wit (y := z) (by simp) hw]
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  apply htr (-n)
  have h2 : ((Algebra.trace ℚ F z : ℚ) : ℂ) = ((-n : ℤ) : ℂ) := by
    have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    apply mul_left_cancel₀ hpi
    push_cast
    linear_combination -hn
  exact_mod_cast h2

/-! ### Primitivity at every level -/

section prim

variable {v : HeightOneSpectrum (𝓞 F)}

/-- `z (v R) ⊆ R` for `z ∈ v⁻¹`. -/
lemma mul_mem_of_mem_map (z : F)
    (hz : ∀ p ∈ v.asIdeal, ∃ a : 𝓞 F, z * algebraMap (𝓞 F) F p = algebraMap (𝓞 F) F a)
    {y : SInt 𝔪} (hy : y ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    z * (y : F) ∈ (placesOf 𝔪).integer F := by
  rw [Ideal.map] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨a, ha⟩ := hz p hp
    rw [coe_alg, ha]
    exact (algebraMap (𝓞 F) (SInt 𝔪) a).2
  | zero => simp
  | add x y _ _ hx hy => rw [Subalgebra.coe_add, mul_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [smul_eq_mul, Subalgebra.coe_mul, mul_left_comm]
    exact mul_mem a.2 hx

/-- Primitivity of `x ↦ e(x / gen(P^j))` on `R / P^j R`: for `x ∉ P^j R` there is `r ∈ R` with
`e(x r / gen(P^j)) ≠ 1`, when `P ∤ 𝔇`. -/
lemma exists_sAddChar_ne_one (g : AllowedGen ι 𝔪) (hv : v ∉ placesOf 𝔪)
    (hPS : v.asIdeal ⊔ 𝔪 = ⊤) (hD : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) {j : ℕ} (hj : 1 ≤ j)
    (x : SInt 𝔪) (hx : x ∉ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪))) :
    ∃ r : SInt 𝔪, sAddChar 𝔪 ((x : F) * (r : F) / (g.gen (v.asIdeal ^ j) : F)) ≠ 1 := by
  obtain ⟨z, hz, htr⟩ := exists_trace_not_int v.asIdeal v.ne_bot hD
  have hez := sAddChar_ne_one_of_dual v.asIdeal hPS z hz htr
  have hext : IsExterior 𝔪 (v.asIdeal ^ j) :=
    isExterior_pow ⟨v.ne_bot, hPS⟩ j
  set B := g.gen (v.asIdeal ^ j)
  have hB0 : (B : F) ≠ 0 := C3B.gen_ne_zero g _ hext
  have hBmem : B ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← g.span_gen _ hext]; exact Ideal.mem_span_singleton_self _
  have hB1 : B ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    have : (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) ≤
        v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
      Ideal.map_mono (by simpa using Ideal.pow_le_pow_right (I := v.asIdeal) hj)
    exact this hBmem
  -- `w = z B ∈ R`
  have hwR : z * (B : F) ∈ (placesOf 𝔪).integer F := mul_mem_of_mem_map z hz hB1
  set w : SInt 𝔪 := ⟨z * (B : F), hwR⟩
  -- valuations
  have hvz : v.valuation F z ≤ exp (1 : ℤ) := by
    obtain ⟨p, hp⟩ := exists_uniformizer (v := v)
    have hpm : p ∈ v.asIdeal := by
      rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F), hp]
      exact exp_lt_exp.2 (by norm_num) |>.trans_eq exp_zero
    obtain ⟨a, ha⟩ := hz p hpm
    have h1 := v.valuation_le_one (K := F) a
    change v.valuation F (algebraMap (𝓞 F) F a) ≤ 1 at h1
    rw [← ha, map_mul, hp] at h1
    have : v.valuation F z * exp (-1 : ℤ) * exp 1 ≤ 1 * exp 1 := mul_le_mul_left h1 _
    rwa [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one, one_mul] at this
  have hvB := val_le_of_mem hv j hBmem
  have hvw : v.valuation F (w : F) ≤ exp (1 - (j : ℤ)) := by
    change v.valuation F (z * (B : F)) ≤ _
    rw [map_mul, show (1 - (j : ℤ)) = 1 + (-(j : ℤ)) by ring, exp_add]
    exact mul_le_mul' hvz hvB
  have hvx : exp (1 - (j : ℤ)) ≤ v.valuation F (x : F) := by
    have := exp_le_val_of_not_mem hv (j - 1) x (by rwa [Nat.sub_add_cancel hj])
    convert this using 2
    push_cast [Nat.cast_sub hj]; ring
  have hx0 : (x : F) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hvx
    exact exp_ne_zero (le_antisymm hvx bot_le)
  have hvx0 : v.valuation F (x : F) ≠ 0 := by
    rw [Ne, map_eq_zero]; exact hx0
  -- `f = w / x` is `v`-integral
  have hvf : v.valuation F ((w : F) / (x : F)) ≤ 1 := by
    rw [map_div₀, div_le_one₀ (pos_iff_ne_zero.2 hvx0)]
    exact hvw.trans hvx
  obtain ⟨a, ha⟩ := exists_val_sub_le (v := v) j _ hvf
  -- `w - x a ∈ P^j R`
  set δ : SInt 𝔪 := w - x * algebraMap (𝓞 F) (SInt 𝔪) a
  have hδ : δ ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    apply mem_of_val_le hv j
    have : (δ : F) = (x : F) * ((w : F) / (x : F) - algebraMap (𝓞 F) F a) := by
      simp only [δ, Subalgebra.coe_sub, Subalgebra.coe_mul, coe_alg]
      field_simp
    rw [this, map_mul]
    calc v.valuation F (x : F) * v.valuation F ((w : F) / (x : F) - algebraMap (𝓞 F) F a)
        ≤ 1 * exp (-(j : ℤ)) := mul_le_mul' (val_le_one hv x) ha
      _ = _ := one_mul _
  refine ⟨algebraMap (𝓞 F) (SInt 𝔪) a, fun h1 => hez ?_⟩
  have hzeq : z = (x : F) * ((algebraMap (𝓞 F) (SInt 𝔪) a : SInt 𝔪) : F) / (B : F) +
      (δ : F) / (B : F) := by
    simp only [δ, Subalgebra.coe_sub, Subalgebra.coe_mul]
    change z = _ + (z * (B : F) - _) / (B : F)
    field_simp
    ring
  rw [hzeq, C3B.sAddChar_add_mem _ _ (C3B.div_gen_mem g _ hext δ hδ), h1]

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

/-- `x I ⊆ R` for an ideal `I` coprime to `𝔪`. -/
def ExtWit (𝔪 : Ideal (𝓞 F)) (x : F) : Prop :=
  ∃ I : Ideal (𝓞 F), I ⊔ 𝔪 = ⊤ ∧
    ∀ i ∈ I, x * algebraMap (𝓞 F) F i ∈ (placesOf 𝔪).integer F

/-- `e` is additive on elements with `ExtWit` (proved below from section A's `C3I_Add`). -/
def HypAdd (𝔪 : Ideal (𝓞 F)) : Prop :=
  ∀ x y : F, ExtWit 𝔪 x → ExtWit 𝔪 y → sAddChar 𝔪 (x + y) = sAddChar 𝔪 x * sAddChar 𝔪 y

theorem hypAdd (𝔪 : Ideal (𝓞 F)) : HypAdd 𝔪 := by
  rintro x y ⟨I, hI, hx⟩ ⟨J, hJ, hy⟩
  exact C3I.sAddChar_add (C3I.hasWit_of_mul_mem x I hI hx) (C3I.hasWit_of_mul_mem y J hJ hy)

lemma extWit_div_add {𝔪 I : Ideal (𝓞 F)} (hI : I ⊔ 𝔪 = ⊤) {q : SInt 𝔪}
    (hq : Ideal.span {q} = I.map (algebraMap (𝓞 F) (SInt 𝔪))) (hq0 : (q : F) ≠ 0)
    (z r : SInt 𝔪) : ExtWit 𝔪 ((z : F) / (q : F) + (r : F)) := by
  refine ⟨I, hI, fun i hi => ?_⟩
  have hm : algebraMap (𝓞 F) (SInt 𝔪) i ∈ Ideal.span {q} := hq ▸ Ideal.mem_map_of_mem _ hi
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hm
  have hiF : algebraMap (𝓞 F) F i = (t : F) * (q : F) := by
    have := congrArg (fun x : SInt 𝔪 => (x : F)) ht
    simp only [Subalgebra.coe_mul] at this
    rw [this]; rfl
  rw [hiF, show ((z : F) / (q : F) + (r : F)) * ((t : F) * (q : F)) =
    (z : F) * (t : F) + (r : F) * (t : F) * (q : F) by field_simp]
  exact add_mem (mul_mem z.2 t.2) (mul_mem (mul_mem r.2 t.2) q.2)

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

lemma isExterior_of_mul_left {I J : Ideal (𝓞 F)} (h : IsExterior 𝔪 (I * J)) : IsExterior 𝔪 I := by
  refine ⟨fun h0 => h.1 (by rw [h0, Ideal.bot_mul]), ?_⟩
  exact eq_top_iff.mpr (h.2 ▸ sup_le_sup_right (Ideal.mul_le_inf.trans inf_le_left) 𝔪)

lemma isExterior_of_mul_right {I J : Ideal (𝓞 F)} (h : IsExterior 𝔪 (I * J)) :
    IsExterior 𝔪 J := by
  rw [mul_comm] at h; exact isExterior_of_mul_left h

/-- An exterior prime does not become the unit ideal in `R`. -/
lemma map_ne_top {Q : Ideal (𝓞 F)} (hQ : Q.IsPrime) (hQe : IsExterior 𝔪 Q) :
    Q.map (algebraMap (𝓞 F) (SInt 𝔪)) ≠ ⊤ := by
  intro htop
  let v : HeightOneSpectrum (𝓞 F) := ⟨Q, hQ, hQe.1⟩
  have hvS : v ∉ placesOf 𝔪 := by
    intro hv
    have : (⊤ : Ideal (𝓞 F)) ≤ Q := hQe.2 ▸ sup_le le_rfl hv
    exact hQ.ne_top (eq_top_iff.mpr this)
  let J : Ideal (SInt 𝔪) :=
    { carrier := {x | v.valuation F (x : F) < 1}
      add_mem' := fun {a b} ha hb => by
        show v.valuation F ((a + b : SInt 𝔪) : F) < 1
        rw [Subalgebra.coe_add]
        exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hb)
      zero_mem' := by
        show v.valuation F ((0 : SInt 𝔪) : F) < 1
        simp
      smul_mem' := fun c x hx => by
        show v.valuation F ((c * x : SInt 𝔪) : F) < 1
        rw [Subalgebra.coe_mul, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (c.2 v hvS)) hx }
  have hle : Q.map (algebraMap (𝓞 F) (SInt 𝔪)) ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    show v.valuation F ((algebraMap (𝓞 F) (SInt 𝔪) a : SInt 𝔪) : F) < 1
    rw [C3B.coe_algebraMap_SInt]
    exact (v.valuation_lt_one_iff_mem a).mpr ha
  have h1 : (1 : SInt 𝔪) ∈ J := hle (htop ▸ Submodule.mem_top)
  have : v.valuation F ((1 : SInt 𝔪) : F) < 1 := h1
  simp at this

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

/-- Coprimality to `P` for an ideal not contained in the maximal ideal `P`. -/
lemma isCoprime_pow_of_not_le {P J : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hJ : ¬ J ≤ P)
    (a : ℕ) : IsCoprime (P ^ a) J := by
  have hmax : P.IsMaximal := hP.isMaximal hP0
  have h1 : IsCoprime P J := by
    rw [Ideal.isCoprime_iff_sup_eq]
    have : P < P ⊔ J := lt_of_le_of_ne le_sup_left (fun h => hJ (le_sup_right.trans h.symm.le))
    exact hmax.1.2 _ this
  exact h1.pow_left

lemma isCoprime_map {I J : Ideal (𝓞 F)} (h : IsCoprime I J) :
    IsCoprime (I.map (algebraMap (𝓞 F) (SInt 𝔪))) (J.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  rw [Ideal.isCoprime_iff_sup_eq] at h ⊢
  rw [← Ideal.map_sup, h, Ideal.map_top]

lemma exists_inv_mod {I : Ideal (SInt 𝔪)} {x : SInt 𝔪} (h : IsCoprime (Ideal.span {x}) I) :
    ∃ x' : SInt 𝔪, x * x' - 1 ∈ I := by
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.mp h
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  refine ⟨c, ?_⟩
  have : x * c - 1 = -b := by rw [← hab]; ring
  rw [this]; exact neg_mem hb

/-! ### Residue symbols -/

variable {ι : F →+* ℂ}

lemma residueSymbol_mul_ideal (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 (I * J) x = residueSymbol ι 𝔪 I x * residueSymbol ι 𝔪 J x := by
  unfold residueSymbol
  rw [normalizedFactors_mul hI hJ, Multiset.map_add, Multiset.prod_add]

lemma residueSymbol_prime {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 P x = sexticResidueSymbol ι 𝔪 P x := by
  have h := C3B.normalizedFactors_prime_pow hP hP0 1
  rw [pow_one, Multiset.replicate_one] at h
  simp [residueSymbol, h]

lemma residueSymbol_prime_pow {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (k : ℕ)
    (x : SInt 𝔪) : residueSymbol ι 𝔪 (P ^ k) x = sexticResidueSymbol ι 𝔪 P x ^ k := by
  simp [residueSymbol, C3B.normalizedFactors_prime_pow hP hP0 k]

lemma residueSymbol_mul (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    (x y : SInt 𝔪) :
    residueSymbol ι 𝔪 𝔞 (x * y) = residueSymbol ι 𝔪 𝔞 x * residueSymbol ι 𝔪 𝔞 y := by
  unfold residueSymbol
  rw [← Multiset.prod_map_mul]
  congr 1
  refine Multiset.map_congr rfl fun Q hQ => ?_
  obtain ⟨hQp, hQe⟩ := exterior_of_mem_factors h𝔞 hQ
  exact (hχ Q hQp hQe).1 x y

lemma not_mem_of_isCoprime {I : Ideal (SInt 𝔪)} (hI : I ≠ ⊤) {x : SInt 𝔪}
    (h : IsCoprime (Ideal.span {x}) I) : x ∉ I := by
  intro hx
  apply hI
  rw [Ideal.isCoprime_iff_sup_eq] at h
  rw [eq_top_iff, ← h]
  exact sup_le ((Ideal.span_singleton_le_iff_mem I).mpr hx) le_rfl

lemma residueSymbol_pow_six (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    {x : SInt 𝔪} (hx : IsCoprime (Ideal.span {x}) (𝔞.map (algebraMap (𝓞 F) (SInt 𝔪)))) :
    residueSymbol ι 𝔪 𝔞 x ^ 6 = 1 := by
  unfold residueSymbol
  rw [← Multiset.prod_map_pow]
  apply Multiset.prod_eq_one
  intro z hz
  obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.mp hz
  obtain ⟨hQp, hQe⟩ := exterior_of_mem_factors h𝔞 hQ
  apply (hχ Q hQp hQe).2
  apply not_mem_of_isCoprime (map_ne_top hQp hQe)
  have hle : 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪)) ≤ Q.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
    Ideal.map_mono (Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hQ))
  rw [Ideal.isCoprime_iff_sup_eq] at hx ⊢
  exact eq_top_iff.mpr (hx ▸ sup_le_sup_left hle _)

lemma residueSymbol_ne_zero (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    {x : SInt 𝔪} (hx : IsCoprime (Ideal.span {x}) (𝔞.map (algebraMap (𝓞 F) (SInt 𝔪)))) :
    residueSymbol ι 𝔪 𝔞 x ≠ 0 := by
  intro h0
  have := residueSymbol_pow_six hχ h𝔞 hx
  rw [h0] at this; norm_num at this

lemma isCoprime_one (I : Ideal (SInt 𝔪)) : IsCoprime (Ideal.span {(1 : SInt 𝔪)}) I := by
  rw [Ideal.span_singleton_one]; exact Ideal.isCoprime_iff_sup_eq.mpr (top_sup_eq _)

lemma residueSymbol_one (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞) :
    residueSymbol ι 𝔪 𝔞 1 = 1 := by
  have h := residueSymbol_mul hχ h𝔞 (1 : SInt 𝔪) 1
  rw [one_mul] at h
  have h0 := residueSymbol_ne_zero hχ h𝔞 (isCoprime_one _)
  have : residueSymbol ι 𝔪 𝔞 1 * (residueSymbol ι 𝔪 𝔞 1 - 1) = 0 := by
    rw [mul_sub, ← h]; ring
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd h1 h0
  · exact sub_eq_zero.mp h1

/-- `χ_𝔞(x) χ_𝔞(x') = 1` when `x x' ≡ 1 (mod 𝔞R)`. -/
lemma residueSymbol_mul_inv (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    {x x' : SInt 𝔪} (h : x * x' - 1 ∈ 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    residueSymbol ι 𝔪 𝔞 x * residueSymbol ι 𝔪 𝔞 x' = 1 := by
  rw [← residueSymbol_mul hχ h𝔞, C3B.residueSymbol_congr ι 𝔞 _ 1 h, residueSymbol_one hχ h𝔞]

lemma isCoprime_unit (u : (SInt 𝔪)ˣ) (I : Ideal (SInt 𝔪)) :
    IsCoprime (Ideal.span {(u : SInt 𝔪)}) I := by
  rw [Ideal.span_singleton_eq_top.mpr u.isUnit]; exact Ideal.isCoprime_iff_sup_eq.mpr (top_sup_eq _)

lemma residueSymbol_unit_pow_six (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    (u : (SInt 𝔪)ˣ) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 𝔞 ((u : SInt 𝔪) ^ 6 * x) = residueSymbol ι 𝔪 𝔞 x := by
  have hp : ∀ n : ℕ, residueSymbol ι 𝔪 𝔞 ((u : SInt 𝔪) ^ n) = residueSymbol ι 𝔪 𝔞 u ^ n := by
    intro n
    induction n with
    | zero => simp [residueSymbol_one hχ h𝔞]
    | succ n ih => rw [pow_succ, residueSymbol_mul hχ h𝔞, ih, pow_succ]
  rw [residueSymbol_mul hχ h𝔞, hp, residueSymbol_pow_six hχ h𝔞 (isCoprime_unit u _), one_mul]

lemma residueSymbol_pow (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    (x : SInt 𝔪) (n : ℕ) : residueSymbol ι 𝔪 𝔞 (x ^ n) = residueSymbol ι 𝔪 𝔞 x ^ n := by
  induction n with
  | zero => simp [residueSymbol_one hχ h𝔞]
  | succ n ih => rw [pow_succ, residueSymbol_mul hχ h𝔞, ih, pow_succ]

/-! ### Generators -/

/-- `gen(I J) = ε⁶ gen(I) gen(J)` with `ε` a unit of `R`. -/
lemma gen_mul' (g : AllowedGen ι 𝔪) {I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I)
    (hJ : IsExterior 𝔪 J) :
    ∃ ε : (SInt 𝔪)ˣ, g.gen (I * J) = (ε : SInt 𝔪) ^ 6 * g.gen I * g.gen J := by
  obtain ⟨ε, hε⟩ := g.gen_mul I J hI hJ
  refine ⟨Set.unitEquivUnitsInteger (placesOf 𝔪) F ε, ?_⟩
  apply Subtype.ext
  rw [hε]
  simp

lemma gen_top (g : AllowedGen ι 𝔪) : ∃ ε : (SInt 𝔪)ˣ, g.gen ⊤ = (ε : SInt 𝔪) ^ 6 := by
  obtain ⟨ε, hε⟩ := gen_mul' g ⟨top_ne_bot, top_sup_eq _⟩ ⟨top_ne_bot, top_sup_eq _⟩
  rw [Ideal.top_mul] at hε
  obtain ⟨u, hu⟩ := C3B.isUnit_gen_top g
  refine ⟨ε⁻¹, ?_⟩
  have h1 : (u : SInt 𝔪) * 1 = (u : SInt 𝔪) * ((ε : SInt 𝔪) ^ 6 * (u : SInt 𝔪)) := by
    rw [← hu] at hε
    rw [mul_one]
    calc (u : SInt 𝔪) = (ε : SInt 𝔪) ^ 6 * u * u := hε
      _ = _ := by ring
  have h2 := u.isUnit.mul_left_cancel h1
  rw [← hu]
  have h3 : ((ε : SInt 𝔪) ^ 6) * ((↑(ε⁻¹) : SInt 𝔪) ^ 6) = 1 := by
    rw [← mul_pow, Units.mul_inv, one_pow]
  calc (u : SInt 𝔪) = (u : SInt 𝔪) * ((ε : SInt 𝔪) ^ 6 * (↑(ε⁻¹) : SInt 𝔪) ^ 6) := by
        rw [h3, mul_one]
    _ = ((ε : SInt 𝔪) ^ 6 * (u : SInt 𝔪)) * (↑(ε⁻¹) : SInt 𝔪) ^ 6 := by ring
    _ = (↑(ε⁻¹) : SInt 𝔪) ^ 6 := by rw [← h2, one_mul]

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

open Classical in
/-- The summand of the Poisson factor, with free generators `s, A`, multiplier `Af` and twist
`c`. -/
noncomputable def U (𝔰 𝔄 : Ideal (𝓞 F)) (s A Af c h d v : SInt 𝔪) : ℂ :=
  if h - Af * d ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)) then
    residueSymbol ι 𝔪 𝔰 d * (residueSymbol ι 𝔪 𝔄 v *
      sAddChar 𝔪 (((h - Af * d : SInt 𝔪) : F) * (v : F) * (c : F) / ((s : F) * (A : F))))
  else 0

/-- The Poisson factor with free generators. -/
noncomputable def PS (𝔰 𝔄 : Ideal (𝓞 F)) (s A Af c h : SInt 𝔪) : ℂ :=
  ∑ᶠ d : SInt 𝔪 ⧸ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)),
    ∑ᶠ v : SInt 𝔪 ⧸ 𝔄.map (algebraMap (𝓞 F) (SInt 𝔪)),
      U ι 𝔪 𝔰 𝔄 s A Af c h (quotLift d) (quotLift v)

/-- The Gauss sum summand with free generator `c` and twist `c'`. -/
noncomputable def V (𝔠 : Ideal (𝓞 F)) (c c' : SInt 𝔪) (j : ℕ) (x : SInt 𝔪) : ℂ :=
  residueSymbol ι 𝔪 𝔠 x ^ j * sAddChar 𝔪 ((x : F) * (c' : F) / (c : F))

/-- The Gauss sum with free generator. -/
noncomputable def GS (𝔠 : Ideal (𝓞 F)) (c c' : SInt 𝔪) (j : ℕ) : ℂ :=
  ∑ᶠ x : SInt 𝔪 ⧸ 𝔠.map (algebraMap (𝓞 F) (SInt 𝔪)), V ι 𝔪 𝔠 c c' j (quotLift x)

end defs

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-! ### Generic lemmas -/

lemma quotLift_mul_sub (I : Ideal (SInt 𝔪)) (u : SInt 𝔪) (x : SInt 𝔪 ⧸ I) :
    quotLift (Ideal.Quotient.mk I u * x) - u * quotLift x ∈ I := by
  rw [← Ideal.Quotient.eq, map_mul]
  rw [show Ideal.Quotient.mk I (quotLift (Ideal.Quotient.mk I u * x)) =
    Ideal.Quotient.mk I u * x from Function.surjInv_eq Ideal.Quotient.mk_surjective _]
  rw [show Ideal.Quotient.mk I (quotLift x) = x from Function.surjInv_eq Ideal.Quotient.mk_surjective _]

lemma periodic_eq {I : Ideal (SInt 𝔪)} {f : SInt 𝔪 → ℂ}
    (hf : ∀ x w, w ∈ I → f (x + w) = f x) {x y : SInt 𝔪} (h : x - y ∈ I) : f x = f y := by
  have := hf y (x - y) h
  rwa [add_sub_cancel] at this

lemma mem_iff_of_sub_mem {I : Ideal (SInt 𝔪)} {x y : SInt 𝔪} (h : x - y ∈ I) :
    x ∈ I ↔ y ∈ I := by
  constructor
  · intro hx; have := sub_mem hx h; rwa [sub_sub_cancel] at this
  · intro hy; have := add_mem h hy; rwa [sub_add_cancel] at this

lemma exists_eq_mul_of_mem {s : SInt 𝔪} {x : SInt 𝔪} (hx : x ∈ Ideal.span {s}) :
    ∃ y : SInt 𝔪, x = y * s := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hx
  exact ⟨a, ha.symm⟩

/-- Chinese remainders for a periodic function. -/
lemma finsum_crt {I J K : Ideal (SInt 𝔪)} [Finite (SInt 𝔪 ⧸ I)] [Finite (SInt 𝔪 ⧸ J)]
    {e₁ e₂ : SInt 𝔪} (he₁ : e₁ ∈ J) (he₂ : e₂ ∈ I) (h1 : e₁ + e₂ = 1) (hK : K = I * J)
    (f : SInt 𝔪 → ℂ) (hf : ∀ x w, w ∈ K → f (x + w) = f x) :
    ∑ᶠ x : SInt 𝔪 ⧸ K, f (quotLift x) =
      ∑ᶠ x₁ : SInt 𝔪 ⧸ I, ∑ᶠ x₂ : SInt 𝔪 ⧸ J, f (quotLift x₁ * e₁ + quotLift x₂ * e₂) := by
  subst hK
  have cop : IsCoprime I J :=
    Ideal.isCoprime_iff_exists.mpr ⟨e₂, he₂, e₁, he₁, by rw [add_comm]; exact h1⟩
  let φ := Ideal.quotientMulEquivQuotientProd I J cop
  rw [← finsum_comp_equiv φ.symm.toEquiv]
  rw [finsum_curry _ (Set.toFinite _)]
  refine finsum_congr fun x₁ => finsum_congr fun x₂ => ?_
  apply periodic_eq hf
  rw [← Ideal.Quotient.eq]
  rw [show Ideal.Quotient.mk (I * J) (quotLift (φ.symm.toEquiv (x₁, x₂))) = φ.symm (x₁, x₂) from
    Function.surjInv_eq Ideal.Quotient.mk_surjective _]
  apply φ.injective
  rw [RingEquiv.apply_symm_apply]
  have hl : ∀ (L : Ideal (SInt 𝔪)) (y : SInt 𝔪 ⧸ L), Ideal.Quotient.mk L (quotLift y) = y :=
    fun L y => Function.surjInv_eq Ideal.Quotient.mk_surjective _
  ext
  · rw [Ideal.quotientMulEquivQuotientProd_fst, Ideal.Quotient.factor_mk]
    rw [← hl I x₁, Ideal.Quotient.eq, hl I x₁]
    have : quotLift x₁ - (quotLift x₁ * e₁ + quotLift x₂ * e₂) = (quotLift x₁ - quotLift x₂) * e₂ := by
      linear_combination (-quotLift x₁) * h1
    rw [this]; exact Ideal.mul_mem_left _ _ he₂
  · rw [Ideal.quotientMulEquivQuotientProd_snd, Ideal.Quotient.factor_mk]
    rw [← hl J x₂, Ideal.Quotient.eq, hl J x₂]
    have : quotLift x₂ - (quotLift x₁ * e₁ + quotLift x₂ * e₂) = (quotLift x₂ - quotLift x₁) * e₁ := by
      linear_combination (-quotLift x₂) * h1
    rw [this]; exact Ideal.mul_mem_left _ _ he₁

/-- Substitution by a unit of `R/I`. -/
lemma finsum_unit_subst {I : Ideal (SInt 𝔪)} {u u' : SInt 𝔪} (hu : u * u' - 1 ∈ I)
    (f : SInt 𝔪 → ℂ) (hf : ∀ x w, w ∈ I → f (x + w) = f x) :
    ∑ᶠ x : SInt 𝔪 ⧸ I, f (quotLift x) = ∑ᶠ x : SInt 𝔪 ⧸ I, f (u * quotLift x) := by
  have h1 : Ideal.Quotient.mk I u * Ideal.Quotient.mk I u' = 1 := by
    rw [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]; exact hu
  let w : (SInt 𝔪 ⧸ I)ˣ := Units.mkOfMulEqOne _ _ h1
  rw [← finsum_comp_equiv (Units.mulLeft w)]
  refine finsum_congr fun x => ?_
  exact periodic_eq hf (quotLift_mul_sub I u x)

/-! ### Coercions -/

lemma coe_sub' (x y : SInt 𝔪) : ((x - y : SInt 𝔪) : F) = (x : F) - (y : F) := rfl
lemma coe_mul' (x y : SInt 𝔪) : ((x * y : SInt 𝔪) : F) = (x : F) * (y : F) := rfl
lemma coe_add' (x y : SInt 𝔪) : ((x + y : SInt 𝔪) : F) = (x : F) + (y : F) := rfl
lemma coe_neg' (x : SInt 𝔪) : ((-x : SInt 𝔪) : F) = -(x : F) := rfl
lemma coe_one' : ((1 : SInt 𝔪) : F) = 1 := rfl

/-! ### The Poisson summand -/

section U

variable {𝔰 𝔄 : Ideal (𝓞 F)} {s A Af c h : SInt 𝔪}

lemma U_add_left (hs : Ideal.span {s} = 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hs0 : (s : F) ≠ 0) (hA0 : (A : F) ≠ 0) {B : SInt 𝔪} (hAf : Af = A * B) (d v w : SInt 𝔪)
    (hw : w ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    U ι 𝔪 𝔰 𝔄 s A Af c h (d + w) v = U ι 𝔪 𝔰 𝔄 s A Af c h d v := by
  have hw' := hw
  rw [← hs] at hw'
  obtain ⟨w', rfl⟩ := exists_eq_mul_of_mem hw'
  have hcond : (h - Af * (d + w' * s) ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪))) ↔
      (h - Af * d ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
    apply mem_iff_of_sub_mem
    rw [show h - Af * (d + w' * s) - (h - Af * d) = -(Af * (w' * s)) by ring]
    exact neg_mem (Ideal.mul_mem_left _ _ hw)
  unfold U
  by_cases hc : h - Af * d ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪))
  · rw [if_pos (hcond.mpr hc), if_pos hc]
    rw [C3B.residueSymbol_congr ι 𝔰 (d + w' * s) d (by rw [add_sub_cancel_left]; exact hw)]
    congr 2
    have harg : ((h - Af * (d + w' * s) : SInt 𝔪) : F) * (v : F) * (c : F) / ((s : F) * (A : F)) =
        ((h - Af * d : SInt 𝔪) : F) * (v : F) * (c : F) / ((s : F) * (A : F)) +
          ((-(B * w' * v * c) : SInt 𝔪) : F) := by
      subst hAf
      simp only [coe_sub', coe_mul', coe_add', coe_neg']
      field_simp
      ring
    rw [harg]
    exact C3B.sAddChar_add_mem _ _ (SetLike.coe_mem _)
  · rw [if_neg (fun h1 => hc (hcond.mp h1)), if_neg hc]

lemma U_add_right (hs : Ideal.span {s} = 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hA : Ideal.span {A} = 𝔄.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hs0 : (s : F) ≠ 0) (hA0 : (A : F) ≠ 0) (d v w : SInt 𝔪)
    (hw : w ∈ 𝔄.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    U ι 𝔪 𝔰 𝔄 s A Af c h d (v + w) = U ι 𝔪 𝔰 𝔄 s A Af c h d v := by
  have hw' := hw
  rw [← hA] at hw'
  obtain ⟨w', rfl⟩ := exists_eq_mul_of_mem hw'
  unfold U
  by_cases hc : h - Af * d ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪))
  · rw [if_pos hc, if_pos hc]
    rw [C3B.residueSymbol_congr ι 𝔄 (v + w' * A) v (by rw [add_sub_cancel_left]; exact hw)]
    have hc' := hc
    rw [← hs] at hc'
    obtain ⟨y, hy⟩ := exists_eq_mul_of_mem hc'
    congr 2
    have harg : ((h - Af * d : SInt 𝔪) : F) * ((v + w' * A : SInt 𝔪) : F) * (c : F) /
          ((s : F) * (A : F)) =
        ((h - Af * d : SInt 𝔪) : F) * (v : F) * (c : F) / ((s : F) * (A : F)) +
          ((y * w' * c : SInt 𝔪) : F) := by
      rw [hy]
      simp only [coe_mul', coe_add']
      field_simp
    rw [harg]
    exact C3B.sAddChar_add_mem _ _ (SetLike.coe_mem _)
  · rw [if_neg hc, if_neg hc]

end U

/-- `poissonFactor` as a `PS`. -/
lemma poissonFactor_eq_PS (g : AllowedGen ι 𝔪) (𝔰 𝔄 : Ideal (𝓞 F)) (h : SInt 𝔪) :
    poissonFactor g 𝔰 𝔄 h = PS ι 𝔪 𝔰 𝔄 (g.gen 𝔰) (g.gen 𝔄) (g.gen 𝔄) 1 h := by
  unfold poissonFactor PS
  refine finsum_congr fun d => ?_
  by_cases hc : h - g.gen 𝔄 * quotLift d ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪))
  · rw [if_pos hc]
    unfold gaussSumAt
    rw [mul_finsum]
    refine finsum_congr fun v => ?_
    unfold U
    rw [if_pos hc]
    congr 3
    rw [coe_one']
    ring
  · rw [if_neg hc]
    symm
    apply finsum_eq_zero_of_forall_eq_zero
    intro v
    unfold U
    rw [if_neg hc]

/-! ### Field identities -/

lemma alg_crt (h Af d₁ d₂ v₁ v₂ c α β s₁ s₂ A₁ A₂ : F) (hs₁ : s₁ ≠ 0) (hs₂ : s₂ ≠ 0)
    (hA₁ : A₁ ≠ 0) (hA₂ : A₂ ≠ 0) (hαβ : α * (s₁ * A₁) + β * (s₂ * A₂) = 1) :
    (h - Af * (d₁ * (β * (s₂ * A₂)) + d₂ * (α * (s₁ * A₁)))) *
        (v₁ * (β * (s₂ * A₂)) + v₂ * (α * (s₁ * A₁))) * c / ((s₁ * s₂) * (A₁ * A₂)) =
      ((h - Af * d₁) * v₁ * (c * β) / (s₁ * A₁) +
          c * β * α * ((h - Af * d₁) * (v₂ - v₁) - Af * (d₂ - d₁) *
            (v₁ * (β * (s₂ * A₂)) + v₂ * (α * (s₁ * A₁))))) +
        ((h - Af * d₂) * v₂ * (c * α) / (s₂ * A₂) +
          c * α * β * ((h - Af * d₂) * (v₁ - v₂) - Af * (d₁ - d₂) *
            (v₁ * (β * (s₂ * A₂)) + v₂ * (α * (s₁ * A₁))))) := by
  have hp : s₁ * A₁ ≠ 0 := mul_ne_zero hs₁ hA₁
  have hα : α = (1 - β * (s₂ * A₂)) / (s₁ * A₁) := by
    field_simp; linear_combination hαβ
  subst hα
  field_simp
  ring

lemma alg_twist (h A B B' l l' c C d v s y z w : F) (hs : s ≠ 0) (hA : A ≠ 0)
    (hh : h - A * d = y * s) (hB : B * B' - 1 = z * s) (hc : l * l' * c * C - 1 = w * (s * A)) :
    (l * h - A * B * (l * B' * d)) * (l' * C * v) * c / (s * A) =
      (h - A * d) * v * 1 / (s * A) + (-(d * z * v) + w * s * (y - A * d * z) * v) := by
  have e1 : (l * h - A * B * (l * B' * d)) * (l' * C * v) * c / (s * A) =
      (l * l' * c * C) * (h - A * (B * B') * d) * v / (s * A) := by ring
  have hBB : B * B' = 1 + z * s := by linear_combination hB
  have hll : l * l' * c * C = 1 + w * (s * A) := by linear_combination hc
  have hh' : h = A * d + y * s := by linear_combination hh
  rw [e1, hBB, hll, hh']
  field_simp
  ring

lemma alg_gs_crt (x₁ x₂ c' α β c₁ c₂ : F) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0)
    (hαβ : α * c₁ + β * c₂ = 1) :
    (x₁ * (β * c₂) + x₂ * (α * c₁)) * c' / (c₁ * c₂) =
      (x₁ * (c' * β) / c₁ + c' * β * α * (x₂ - x₁)) +
        (x₂ * (c' * α) / c₂ + c' * α * β * (x₁ - x₂)) := by
  have hα : α = (1 - β * c₂) / c₁ := by
    field_simp; linear_combination hαβ
  subst hα
  field_simp
  ring

lemma alg_gs_twist (x C c'' c w : F) (hc : c ≠ 0) (h : C * c'' - 1 = w * c) :
    (C * x) * c'' / c = x * 1 / c + x * w := by
  have h' : C * c'' = 1 + w * c := by linear_combination h
  have e : (C * x) * c'' / c = x * (C * c'') / c := by ring
  rw [e, h']
  field_simp

/-! ### CRT and twists for `PS` -/

section crt

variable {𝔰₁ 𝔰₂ 𝔄₁ 𝔄₂ : Ideal (𝓞 F)} {s₁ s₂ A₁ A₂ Af c h α β : SInt 𝔪}

lemma castF {x y : SInt 𝔪} (h : x = y) : (x : F) = (y : F) := congrArg _ h

lemma U_crt (hadd : HypAdd 𝔪) (h𝔰₁ : 𝔰₁ ≠ ⊥) (h𝔰₂ : 𝔰₂ ≠ ⊥) (h𝔄₁ : 𝔄₁ ≠ ⊥) (h𝔄₂ : 𝔄₂ ≠ ⊥)
    (hsA₁e : 𝔰₁ * 𝔄₁ ⊔ 𝔪 = ⊤) (hsA₂e : 𝔰₂ * 𝔄₂ ⊔ 𝔪 = ⊤)
    (hs₁ : Ideal.span {s₁} = 𝔰₁.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hs₂ : Ideal.span {s₂} = 𝔰₂.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hA₁ : Ideal.span {A₁} = 𝔄₁.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hA₂ : Ideal.span {A₂} = 𝔄₂.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hs₁0 : (s₁ : F) ≠ 0) (hs₂0 : (s₂ : F) ≠ 0) (hA₁0 : (A₁ : F) ≠ 0) (hA₂0 : (A₂ : F) ≠ 0)
    (hαβ : α * (s₁ * A₁) + β * (s₂ * A₂) = 1) (d₁ d₂ v₁ v₂ : SInt 𝔪) :
    U ι 𝔪 (𝔰₁ * 𝔰₂) (𝔄₁ * 𝔄₂) (s₁ * s₂) (A₁ * A₂) Af c h
        (d₁ * (β * (s₂ * A₂)) + d₂ * (α * (s₁ * A₁)))
        (v₁ * (β * (s₂ * A₂)) + v₂ * (α * (s₁ * A₁))) =
      U ι 𝔪 𝔰₁ 𝔄₁ s₁ A₁ Af (c * β) h d₁ v₁ * U ι 𝔪 𝔰₂ 𝔄₂ s₂ A₂ Af (c * α) h d₂ v₂ := by
  have he₁s : β * (s₂ * A₂) ∈ 𝔰₂.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hs₂]; exact Ideal.mem_span_singleton'.mpr ⟨β * A₂, by ring⟩
  have he₁A : β * (s₂ * A₂) ∈ 𝔄₂.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hA₂]; exact Ideal.mem_span_singleton'.mpr ⟨β * s₂, by ring⟩
  have he₂s : α * (s₁ * A₁) ∈ 𝔰₁.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hs₁]; exact Ideal.mem_span_singleton'.mpr ⟨α * A₁, by ring⟩
  have he₂A : α * (s₁ * A₁) ∈ 𝔄₁.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hA₁]; exact Ideal.mem_span_singleton'.mpr ⟨α * s₁, by ring⟩
  have hsub : ∀ x₁ x₂ : SInt 𝔪,
      (x₁ * (β * (s₂ * A₂)) + x₂ * (α * (s₁ * A₁))) - x₁ = (x₂ - x₁) * (α * (s₁ * A₁)) ∧
      (x₁ * (β * (s₂ * A₂)) + x₂ * (α * (s₁ * A₁))) - x₂ = (x₁ - x₂) * (β * (s₂ * A₂)) := by
    intro x₁ x₂
    constructor
    · linear_combination x₁ * hαβ
    · linear_combination x₂ * hαβ
  have hd1 := (hsub d₁ d₂).1
  have hd2 := (hsub d₁ d₂).2
  have hv1 := (hsub v₁ v₂).1
  have hv2 := (hsub v₁ v₂).2
  have cop : IsCoprime (𝔰₁.map (algebraMap (𝓞 F) (SInt 𝔪))) (𝔰₂.map (algebraMap (𝓞 F) (SInt 𝔪))) :=
    Ideal.isCoprime_iff_exists.mpr ⟨_, he₂s, _, he₁s, by rw [add_comm, ← hαβ]; ring⟩
  have hmap : (𝔰₁ * 𝔰₂).map (algebraMap (𝓞 F) (SInt 𝔪)) =
      𝔰₁.map (algebraMap (𝓞 F) (SInt 𝔪)) ⊓ 𝔰₂.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [Ideal.map_mul, Ideal.mul_eq_inf_of_isCoprime cop]
  set d := d₁ * (β * (s₂ * A₂)) + d₂ * (α * (s₁ * A₁)) with hd
  set v := v₁ * (β * (s₂ * A₂)) + v₂ * (α * (s₁ * A₁)) with hv
  have hc1 : (h - Af * d ∈ 𝔰₁.map (algebraMap (𝓞 F) (SInt 𝔪))) ↔
      (h - Af * d₁ ∈ 𝔰₁.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
    apply mem_iff_of_sub_mem
    rw [show h - Af * d - (h - Af * d₁) = -(Af * (d - d₁)) by ring, hd1]
    exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ he₂s))
  have hc2 : (h - Af * d ∈ 𝔰₂.map (algebraMap (𝓞 F) (SInt 𝔪))) ↔
      (h - Af * d₂ ∈ 𝔰₂.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
    apply mem_iff_of_sub_mem
    rw [show h - Af * d - (h - Af * d₂) = -(Af * (d - d₂)) by ring, hd2]
    exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ he₁s))
  unfold U
  by_cases H1 : h - Af * d₁ ∈ 𝔰₁.map (algebraMap (𝓞 F) (SInt 𝔪))
  · by_cases H2 : h - Af * d₂ ∈ 𝔰₂.map (algebraMap (𝓞 F) (SInt 𝔪))
    · have H : h - Af * d ∈ (𝔰₁ * 𝔰₂).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
        rw [hmap]; exact ⟨hc1.mpr H1, hc2.mpr H2⟩
      rw [if_pos H, if_pos H1, if_pos H2]
      rw [residueSymbol_mul_ideal _ _ h𝔰₁ h𝔰₂, residueSymbol_mul_ideal _ _ h𝔄₁ h𝔄₂,
        C3B.residueSymbol_congr ι 𝔰₁ d d₁ (by rw [hd1]; exact Ideal.mul_mem_left _ _ he₂s),
        C3B.residueSymbol_congr ι 𝔰₂ d d₂ (by rw [hd2]; exact Ideal.mul_mem_left _ _ he₁s),
        C3B.residueSymbol_congr ι 𝔄₁ v v₁ (by rw [hv1]; exact Ideal.mul_mem_left _ _ he₂A),
        C3B.residueSymbol_congr ι 𝔄₂ v v₂ (by rw [hv2]; exact Ideal.mul_mem_left _ _ he₁A)]
      have hαβF := castF (F := F) hαβ
      simp only [coe_add', coe_mul', coe_one'] at hαβF
      have harg : ((h - Af * d : SInt 𝔪) : F) * (v : F) * (c : F) /
            (((s₁ * s₂ : SInt 𝔪) : F) * ((A₁ * A₂ : SInt 𝔪) : F)) =
          (((h - Af * d₁ : SInt 𝔪) : F) * (v₁ : F) * ((c * β : SInt 𝔪) : F) /
              ((s₁ : F) * (A₁ : F)) +
            ((c * β * α * ((h - Af * d₁) * (v₂ - v₁) - Af * (d₂ - d₁) * v) : SInt 𝔪) : F)) +
          (((h - Af * d₂ : SInt 𝔪) : F) * (v₂ : F) * ((c * α : SInt 𝔪) : F) /
              ((s₂ : F) * (A₂ : F)) +
            ((c * α * β * ((h - Af * d₂) * (v₁ - v₂) - Af * (d₁ - d₂) * v) : SInt 𝔪) : F)) := by
        rw [hd, hv]
        simp only [coe_sub', coe_mul', coe_add']
        exact alg_crt _ _ _ _ _ _ _ _ _ _ _ _ _ hs₁0 hs₂0 hA₁0 hA₂0 hαβF
      have hq₁ : Ideal.span {s₁ * A₁} = (𝔰₁ * 𝔄₁).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
        rw [Ideal.map_mul, ← hs₁, ← hA₁, Ideal.span_singleton_mul_span_singleton]
      have hq₂ : Ideal.span {s₂ * A₂} = (𝔰₂ * 𝔄₂).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
        rw [Ideal.map_mul, ← hs₂, ← hA₂, Ideal.span_singleton_mul_span_singleton]
      rw [harg, hadd, C3B.sAddChar_add_mem _ _ (SetLike.coe_mem _),
        C3B.sAddChar_add_mem _ _ (SetLike.coe_mem _)]
      · ring
      · exact extWit_div_add hsA₁e hq₁ (by rw [coe_mul']; exact mul_ne_zero hs₁0 hA₁0)
          ((h - Af * d₁) * v₁ * (c * β)) _
      · exact extWit_div_add hsA₂e hq₂ (by rw [coe_mul']; exact mul_ne_zero hs₂0 hA₂0)
          ((h - Af * d₂) * v₂ * (c * α)) _
    · have H : h - Af * d ∉ (𝔰₁ * 𝔰₂).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
        rw [hmap]; exact fun hh => H2 (hc2.mp hh.2)
      rw [if_neg H, if_neg H2, mul_zero]
  · have H : h - Af * d ∉ (𝔰₁ * 𝔰₂).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
      rw [hmap]; exact fun hh => H1 (hc1.mp hh.1)
    rw [if_neg H, if_neg H1, zero_mul]

lemma PS_crt (hadd : HypAdd 𝔪) (h𝔰₁ : IsExterior 𝔪 𝔰₁) (h𝔰₂ : IsExterior 𝔪 𝔰₂)
    (h𝔄₁ : IsExterior 𝔪 𝔄₁) (h𝔄₂ : IsExterior 𝔪 𝔄₂)
    (hs₁ : Ideal.span {s₁} = 𝔰₁.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hs₂ : Ideal.span {s₂} = 𝔰₂.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hA₁ : Ideal.span {A₁} = 𝔄₁.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hA₂ : Ideal.span {A₂} = 𝔄₂.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hs₁0 : (s₁ : F) ≠ 0) (hs₂0 : (s₂ : F) ≠ 0) (hA₁0 : (A₁ : F) ≠ 0) (hA₂0 : (A₂ : F) ≠ 0)
    (hαβ : α * (s₁ * A₁) + β * (s₂ * A₂) = 1) {B : SInt 𝔪} (hAf : Af = A₁ * A₂ * B) :
    PS ι 𝔪 (𝔰₁ * 𝔰₂) (𝔄₁ * 𝔄₂) (s₁ * s₂) (A₁ * A₂) Af c h =
      PS ι 𝔪 𝔰₁ 𝔄₁ s₁ A₁ Af (c * β) h * PS ι 𝔪 𝔰₂ 𝔄₂ s₂ A₂ Af (c * α) h := by
  have := finite_quot h𝔰₁; have := finite_quot h𝔰₂
  have := finite_quot h𝔄₁; have := finite_quot h𝔄₂
  have hs : Ideal.span {s₁ * s₂} = (𝔰₁ * 𝔰₂).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [Ideal.map_mul, ← hs₁, ← hs₂, Ideal.span_singleton_mul_span_singleton]
  have hA : Ideal.span {A₁ * A₂} = (𝔄₁ * 𝔄₂).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [Ideal.map_mul, ← hA₁, ← hA₂, Ideal.span_singleton_mul_span_singleton]
  have hs0 : ((s₁ * s₂ : SInt 𝔪) : F) ≠ 0 := by rw [coe_mul']; exact mul_ne_zero hs₁0 hs₂0
  have hA0 : ((A₁ * A₂ : SInt 𝔪) : F) ≠ 0 := by rw [coe_mul']; exact mul_ne_zero hA₁0 hA₂0
  have he₁s : β * (s₂ * A₂) ∈ 𝔰₂.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hs₂]; exact Ideal.mem_span_singleton'.mpr ⟨β * A₂, by ring⟩
  have he₁A : β * (s₂ * A₂) ∈ 𝔄₂.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hA₂]; exact Ideal.mem_span_singleton'.mpr ⟨β * s₂, by ring⟩
  have he₂s : α * (s₁ * A₁) ∈ 𝔰₁.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hs₁]; exact Ideal.mem_span_singleton'.mpr ⟨α * A₁, by ring⟩
  have he₂A : α * (s₁ * A₁) ∈ 𝔄₁.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hA₁]; exact Ideal.mem_span_singleton'.mpr ⟨α * s₁, by ring⟩
  have h1 : β * (s₂ * A₂) + α * (s₁ * A₁) = 1 := by rw [add_comm]; exact hαβ
  unfold PS
  refine (finsum_crt he₁s he₂s h1 (Ideal.map_mul _ _ _)
    (fun d => ∑ᶠ v : SInt 𝔪 ⧸ (𝔄₁ * 𝔄₂).map (algebraMap (𝓞 F) (SInt 𝔪)),
      U ι 𝔪 (𝔰₁ * 𝔰₂) (𝔄₁ * 𝔄₂) (s₁ * s₂) (A₁ * A₂) Af c h d (quotLift v))
    (fun x w hw => finsum_congr fun v => U_add_left hs hs0 hA0 hAf x _ w hw)).trans ?_
  have step2 : ∀ d : SInt 𝔪,
      ∑ᶠ v : SInt 𝔪 ⧸ (𝔄₁ * 𝔄₂).map (algebraMap (𝓞 F) (SInt 𝔪)),
        U ι 𝔪 (𝔰₁ * 𝔰₂) (𝔄₁ * 𝔄₂) (s₁ * s₂) (A₁ * A₂) Af c h d (quotLift v) =
      ∑ᶠ v₁ : SInt 𝔪 ⧸ 𝔄₁.map (algebraMap (𝓞 F) (SInt 𝔪)),
        ∑ᶠ v₂ : SInt 𝔪 ⧸ 𝔄₂.map (algebraMap (𝓞 F) (SInt 𝔪)),
          U ι 𝔪 (𝔰₁ * 𝔰₂) (𝔄₁ * 𝔄₂) (s₁ * s₂) (A₁ * A₂) Af c h d
            (quotLift v₁ * (β * (s₂ * A₂)) + quotLift v₂ * (α * (s₁ * A₁))) := fun d =>
    finsum_crt he₁A he₂A h1 (Ideal.map_mul _ _ _)
      (fun v => U ι 𝔪 (𝔰₁ * 𝔰₂) (𝔄₁ * 𝔄₂) (s₁ * s₂) (A₁ * A₂) Af c h d v)
      (fun x w hw => U_add_right hs hA hs0 hA0 d x w hw)
  simp only [step2, U_crt hadd h𝔰₁.1 h𝔰₂.1 h𝔄₁.1 h𝔄₂.1 (C3B.isExterior_mul h𝔰₁ h𝔄₁).2
    (C3B.isExterior_mul h𝔰₂ h𝔄₂).2 hs₁ hs₂ hA₁ hA₂ hs₁0 hs₂0 hA₁0 hA₂0 hαβ]
  rw [finsum_mul]
  refine finsum_congr fun d₁ => ?_
  rw [mul_finsum]
  refine finsum_congr fun d₂ => ?_
  rw [finsum_mul]
  refine finsum_congr fun v₁ => ?_
  rw [mul_finsum]

lemma U_twist_pt (hχ : HypChi ι 𝔪) {𝔰 𝔄 : Ideal (𝓞 F)} {s A c h : SInt 𝔪}
    (h𝔰 : IsExterior 𝔪 𝔰) (h𝔄 : IsExterior 𝔪 𝔄)
    (hs : Ideal.span {s} = 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hs0 : (s : F) ≠ 0) (hA0 : (A : F) ≠ 0) {B B' l l' l'' C : SInt 𝔪}
    (hB : B * B' - 1 ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hl : l * l'' - 1 ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hc : l * l' * c * C - 1 ∈ Ideal.span {s * A}) (d v : SInt 𝔪) :
    U ι 𝔪 𝔰 𝔄 s A (A * B) c (l * h) (l * B' * d) (l' * C * v) =
      residueSymbol ι 𝔪 𝔰 l * residueSymbol ι 𝔪 𝔰 B' * residueSymbol ι 𝔪 𝔄 l' *
        residueSymbol ι 𝔪 𝔄 C * U ι 𝔪 𝔰 𝔄 s A A 1 h d v := by
  have hcond : (l * h - A * B * (l * B' * d) ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪))) ↔
      (h - A * d ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
    have e : l * h - A * B * (l * B' * d) = l * (h - A * d) - l * A * d * (B * B' - 1) := by ring
    rw [e]
    constructor
    · intro H
      have H2 : l * (h - A * d) ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
        have := add_mem H (Ideal.mul_mem_left _ (l * A * d) hB)
        rwa [sub_add_cancel] at this
      have e2 : h - A * d = l'' * (l * (h - A * d)) - (l * l'' - 1) * (h - A * d) := by ring
      rw [e2]
      exact sub_mem (Ideal.mul_mem_left _ _ H2) (Ideal.mul_mem_right _ _ hl)
    · intro H
      exact sub_mem (Ideal.mul_mem_left _ _ H) (Ideal.mul_mem_left _ _ hB)
  unfold U
  by_cases H : h - A * d ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪))
  · rw [if_pos (hcond.mpr H), if_pos H]
    rw [residueSymbol_mul hχ h𝔰, residueSymbol_mul hχ h𝔰, residueSymbol_mul hχ h𝔄,
      residueSymbol_mul hχ h𝔄]
    have H' := H
    rw [← hs] at H'
    obtain ⟨y, hy⟩ := exists_eq_mul_of_mem H'
    have hB' := hB
    rw [← hs] at hB'
    obtain ⟨z, hz⟩ := exists_eq_mul_of_mem hB'
    obtain ⟨w, hw⟩ := exists_eq_mul_of_mem hc
    have hyF := castF (F := F) hy
    have hzF := castF (F := F) hz
    have hwF := castF (F := F) hw
    simp only [coe_sub', coe_mul', coe_one'] at hyF hzF hwF
    have harg : ((l * h - A * B * (l * B' * d) : SInt 𝔪) : F) * ((l' * C * v : SInt 𝔪) : F) *
          (c : F) / ((s : F) * (A : F)) =
        ((h - A * d : SInt 𝔪) : F) * (v : F) * ((1 : SInt 𝔪) : F) / ((s : F) * (A : F)) +
          ((-(d * z * v) + w * s * (y - A * d * z) * v : SInt 𝔪) : F) := by
      simp only [coe_sub', coe_mul', coe_add', coe_neg', coe_one']
      exact alg_twist _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs0 hA0 hyF hzF hwF
    rw [harg, C3B.sAddChar_add_mem _ _ (SetLike.coe_mem _)]
    ring
  · rw [if_neg (fun hh => H (hcond.mp hh)), if_neg H, mul_zero]

lemma PS_twist (hχ : HypChi ι 𝔪) {𝔰 𝔄 : Ideal (𝓞 F)} {s A c h : SInt 𝔪}
    (h𝔰 : IsExterior 𝔪 𝔰) (h𝔄 : IsExterior 𝔪 𝔄)
    (hs : Ideal.span {s} = 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hA : Ideal.span {A} = 𝔄.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hs0 : (s : F) ≠ 0) (hA0 : (A : F) ≠ 0) {B B' l l' l'' C : SInt 𝔪}
    (hB : B * B' - 1 ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hl : l * l'' - 1 ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hc : l * l' * c * C - 1 ∈ Ideal.span {s * A}) :
    PS ι 𝔪 𝔰 𝔄 s A (A * B) c (l * h) =
      residueSymbol ι 𝔪 𝔰 l * residueSymbol ι 𝔪 𝔰 B' * residueSymbol ι 𝔪 𝔄 l' *
        residueSymbol ι 𝔪 𝔄 C * PS ι 𝔪 𝔰 𝔄 s A A 1 h := by
  have hu1 : (l * B') * (l'' * B) - 1 ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    have e : (l * B') * (l'' * B) - 1 = (l * l'' - 1) * (B * B') + (B * B' - 1) := by ring
    rw [e]; exact add_mem (Ideal.mul_mem_right _ _ hl) hB
  have hu2 : (l' * C) * (l * c) - 1 ∈ 𝔄.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    have e : (l' * C) * (l * c) - 1 = l * l' * c * C - 1 := by ring
    rw [e, ← hA]
    exact (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left A s)) hc
  unfold PS
  refine (finsum_unit_subst hu1
    (fun d => ∑ᶠ v : SInt 𝔪 ⧸ 𝔄.map (algebraMap (𝓞 F) (SInt 𝔪)),
      U ι 𝔪 𝔰 𝔄 s A (A * B) c (l * h) d (quotLift v))
    (fun x w hw => finsum_congr fun v => U_add_left hs hs0 hA0 rfl x _ w hw)).trans ?_
  rw [mul_finsum]
  refine finsum_congr fun d => ?_
  refine (finsum_unit_subst hu2
    (fun v => U ι 𝔪 𝔰 𝔄 s A (A * B) c (l * h) (l * B' * quotLift d) v)
    (fun x w hw => U_add_right hs hA hs0 hA0 _ x w hw)).trans ?_
  rw [mul_finsum]
  refine finsum_congr fun v => ?_
  exact U_twist_pt hχ h𝔰 h𝔄 hs hs0 hA0 hB hl hc _ _

end crt

/-! ### Gauss sums -/

section gs

variable {𝔠 : Ideal (𝓞 F)} {c c' : SInt 𝔪} {j : ℕ}

lemma V_add (hc : Ideal.span {c} = 𝔠.map (algebraMap (𝓞 F) (SInt 𝔪))) (hc0 : (c : F) ≠ 0)
    (x w : SInt 𝔪) (hw : w ∈ 𝔠.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    V ι 𝔪 𝔠 c c' j (x + w) = V ι 𝔪 𝔠 c c' j x := by
  have hw' := hw
  rw [← hc] at hw'
  obtain ⟨w', rfl⟩ := exists_eq_mul_of_mem hw'
  unfold V
  rw [C3B.residueSymbol_congr ι 𝔠 (x + w' * c) x (by rw [add_sub_cancel_left]; exact hw)]
  have harg : ((x + w' * c : SInt 𝔪) : F) * (c' : F) / (c : F) =
      (x : F) * (c' : F) / (c : F) + ((w' * c' : SInt 𝔪) : F) := by
    simp only [coe_mul', coe_add']
    field_simp
  rw [harg, C3B.sAddChar_add_mem _ _ (SetLike.coe_mem _)]

lemma GS_crt (hadd : HypAdd 𝔪) {𝔠₁ 𝔠₂ : Ideal (𝓞 F)} {c₁ c₂ α β : SInt 𝔪}
    (h𝔠₁ : IsExterior 𝔪 𝔠₁) (h𝔠₂ : IsExterior 𝔪 𝔠₂)
    (hc₁ : Ideal.span {c₁} = 𝔠₁.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hc₂ : Ideal.span {c₂} = 𝔠₂.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hc₁0 : (c₁ : F) ≠ 0) (hc₂0 : (c₂ : F) ≠ 0) (hαβ : α * c₁ + β * c₂ = 1) :
    GS ι 𝔪 (𝔠₁ * 𝔠₂) (c₁ * c₂) c' j = GS ι 𝔪 𝔠₁ c₁ (c' * β) j * GS ι 𝔪 𝔠₂ c₂ (c' * α) j := by
  have := finite_quot h𝔠₁; have := finite_quot h𝔠₂
  have hc : Ideal.span {c₁ * c₂} = (𝔠₁ * 𝔠₂).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [Ideal.map_mul, ← hc₁, ← hc₂, Ideal.span_singleton_mul_span_singleton]
  have hc0 : ((c₁ * c₂ : SInt 𝔪) : F) ≠ 0 := by rw [coe_mul']; exact mul_ne_zero hc₁0 hc₂0
  have he₁ : β * c₂ ∈ 𝔠₂.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hc₂]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have he₂ : α * c₁ ∈ 𝔠₁.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hc₁]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have h1 : β * c₂ + α * c₁ = 1 := by rw [add_comm]; exact hαβ
  unfold GS
  refine (finsum_crt he₁ he₂ h1 (Ideal.map_mul _ _ _) (V ι 𝔪 (𝔠₁ * 𝔠₂) (c₁ * c₂) c' j)
    (fun x w hw => V_add hc hc0 x w hw)).trans ?_
  have hpt : ∀ x₁ x₂ : SInt 𝔪, V ι 𝔪 (𝔠₁ * 𝔠₂) (c₁ * c₂) c' j (x₁ * (β * c₂) + x₂ * (α * c₁)) =
      V ι 𝔪 𝔠₁ c₁ (c' * β) j x₁ * V ι 𝔪 𝔠₂ c₂ (c' * α) j x₂ := by
    intro x₁ x₂
    have hx1 : x₁ * (β * c₂) + x₂ * (α * c₁) - x₁ = (x₂ - x₁) * (α * c₁) := by
      linear_combination x₁ * hαβ
    have hx2 : x₁ * (β * c₂) + x₂ * (α * c₁) - x₂ = (x₁ - x₂) * (β * c₂) := by
      linear_combination x₂ * hαβ
    unfold V
    rw [residueSymbol_mul_ideal _ _ h𝔠₁.1 h𝔠₂.1,
      C3B.residueSymbol_congr ι 𝔠₁ _ x₁ (by rw [hx1]; exact Ideal.mul_mem_left _ _ he₂),
      C3B.residueSymbol_congr ι 𝔠₂ _ x₂ (by rw [hx2]; exact Ideal.mul_mem_left _ _ he₁)]
    have hαβF := castF (F := F) hαβ
    simp only [coe_add', coe_mul', coe_one'] at hαβF
    have harg : ((x₁ * (β * c₂) + x₂ * (α * c₁) : SInt 𝔪) : F) * (c' : F) /
          ((c₁ * c₂ : SInt 𝔪) : F) =
        ((x₁ : F) * ((c' * β : SInt 𝔪) : F) / (c₁ : F) + ((c' * β * α * (x₂ - x₁) : SInt 𝔪) : F)) +
          ((x₂ : F) * ((c' * α : SInt 𝔪) : F) / (c₂ : F) +
            ((c' * α * β * (x₁ - x₂) : SInt 𝔪) : F)) := by
      simp only [coe_sub', coe_mul', coe_add']
      exact alg_gs_crt _ _ _ _ _ _ _ hc₁0 hc₂0 hαβF
    rw [harg, hadd, C3B.sAddChar_add_mem _ _ (SetLike.coe_mem _),
      C3B.sAddChar_add_mem _ _ (SetLike.coe_mem _)]
    · ring
    · exact extWit_div_add h𝔠₁.2 hc₁ hc₁0 (x₁ * (c' * β)) _
    · exact extWit_div_add h𝔠₂.2 hc₂ hc₂0 (x₂ * (c' * α)) _
  simp only [hpt]
  rw [finsum_mul]
  refine finsum_congr fun x₁ => ?_
  rw [mul_finsum]

lemma GS_twist (hχ : HypChi ι 𝔪) (h𝔠 : IsExterior 𝔪 𝔠)
    (hc : Ideal.span {c} = 𝔠.map (algebraMap (𝓞 F) (SInt 𝔪))) (hc0 : (c : F) ≠ 0)
    {c'' C : SInt 𝔪} (hC : C * c'' - 1 ∈ 𝔠.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    GS ι 𝔪 𝔠 c c'' j = residueSymbol ι 𝔪 𝔠 C ^ j * GS ι 𝔪 𝔠 c 1 j := by
  unfold GS
  refine (finsum_unit_subst hC (V ι 𝔪 𝔠 c c'' j) (fun x w hw => V_add hc hc0 x w hw)).trans ?_
  rw [mul_finsum]
  refine finsum_congr fun x => ?_
  have hC' := hC
  rw [← hc] at hC'
  obtain ⟨w, hw⟩ := exists_eq_mul_of_mem hC'
  have hwF := castF (F := F) hw
  simp only [coe_sub', coe_mul', coe_one'] at hwF
  unfold V
  rw [residueSymbol_mul hχ h𝔠, mul_pow]
  have harg : ((C * quotLift x : SInt 𝔪) : F) * (c'' : F) / (c : F) =
      ((quotLift x : SInt 𝔪) : F) * ((1 : SInt 𝔪) : F) / (c : F) +
        ((quotLift x * w : SInt 𝔪) : F) := by
    simp only [coe_mul', coe_one']
    exact alg_gs_twist _ _ _ _ _ hc0 hwF
  rw [harg, C3B.sAddChar_add_mem _ _ (SetLike.coe_mem _)]
  ring

end gs

lemma gaussPhase_eq_GS (g : AllowedGen ι 𝔪) (j : ℕ) (𝔠 : Ideal (𝓞 F)) :
    gaussPhase g j 𝔠 =
      ((Real.sqrt (Ideal.absNorm 𝔠) : ℝ) : ℂ)⁻¹ * GS ι 𝔪 𝔠 (g.gen 𝔠) 1 j := by
  unfold gaussPhase GS V
  congr 1
  refine finsum_congr fun x => ?_
  rw [coe_one', mul_one]

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

lemma cop_mono {X I J : Ideal (SInt 𝔪)} (h : IsCoprime X I) (hIJ : I ≤ J) : IsCoprime X J := by
  rw [Ideal.isCoprime_iff_sup_eq] at h ⊢
  exact eq_top_iff.mpr (h ▸ sup_le_sup_left hIJ X)

lemma cop_mul {x y : SInt 𝔪} {I : Ideal (SInt 𝔪)} (hx : IsCoprime (Ideal.span {x}) I)
    (hy : IsCoprime (Ideal.span {y}) I) : IsCoprime (Ideal.span {x * y}) I := by
  rw [← Ideal.span_singleton_mul_span_singleton]; exact hx.mul_left hy

lemma cop_pow {x : SInt 𝔪} {I : Ideal (SInt 𝔪)} (hx : IsCoprime (Ideal.span {x}) I) (n : ℕ) :
    IsCoprime (Ideal.span {x ^ n}) I := by
  rw [← Ideal.span_singleton_pow]; exact hx.pow_left

lemma cop_of_inv {x x' : SInt 𝔪} {I : Ideal (SInt 𝔪)} (h : x * x' - 1 ∈ I) :
    IsCoprime (Ideal.span {x'}) I := by
  refine Ideal.isCoprime_iff_exists.mpr ⟨x * x', Ideal.mul_mem_left _ _
    (Ideal.mem_span_singleton_self _), -(x * x' - 1), neg_mem h, by ring⟩

lemma cop_gen (g : AllowedGen ι 𝔪) {𝔟 𝔞 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟)
    (h : IsCoprime 𝔟 𝔞) : IsCoprime (Ideal.span {g.gen 𝔟}) (𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  rw [g.span_gen 𝔟 h𝔟]; exact isCoprime_map h

lemma span_gen_mul (g : AllowedGen ι 𝔪) {I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I)
    (hJ : IsExterior 𝔪 J) :
    Ideal.span {g.gen I * g.gen J} = (I * J).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  rw [← Ideal.span_singleton_mul_span_singleton, g.span_gen I hI, g.span_gen J hJ, Ideal.map_mul]

lemma pow_sub_one_mem {x : SInt 𝔪} {I : Ideal (SInt 𝔪)} (h : x - 1 ∈ I) (n : ℕ) :
    x ^ n - 1 ∈ I := by
  obtain ⟨k, hk⟩ := sub_dvd_pow_sub_pow x 1 n
  rw [one_pow] at hk
  rw [hk]; exact Ideal.mul_mem_right _ _ h

lemma exists_ab {x y : SInt 𝔪} (h : IsCoprime (Ideal.span {x}) (Ideal.span {y})) :
    ∃ α β : SInt 𝔪, α * x + β * y = 1 := by
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.mp h
  obtain ⟨α, rfl⟩ := Ideal.mem_span_singleton'.mp hi
  obtain ⟨β, rfl⟩ := Ideal.mem_span_singleton'.mp hj
  exact ⟨α, β, hij⟩

lemma unit_pow_mul_inv (ε : (SInt 𝔪)ˣ) :
    (ε : SInt 𝔪) ^ 6 * ((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) ^ 6 = 1 := by
  rw [← mul_pow, Units.mul_inv, one_pow]

/-! ### Change of generators -/

lemma unit_coe_ne_zero (u : (SInt 𝔪)ˣ) : ((u : SInt 𝔪) : F) ≠ 0 := by
  intro h0
  have : ((u : SInt 𝔪) : F) * (((u⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = 1 := by
    rw [← coe_mul', Units.mul_inv]; rfl
  rw [h0, zero_mul] at this; exact zero_ne_one this

lemma GS_gen_change {𝔠 : Ideal (𝓞 F)} {c₀ c c' : SInt 𝔪} {j : ℕ} (hc₀ : (c₀ : F) ≠ 0)
    (hc' : (c' : F) ≠ 0)
    (hc : (c : F) = (c' : F) * (c₀ : F)) : GS ι 𝔪 𝔠 c₀ 1 j = GS ι 𝔪 𝔠 c c' j := by
  unfold GS V
  refine finsum_congr fun x => ?_
  congr 2
  rw [hc, coe_one']
  field_simp

lemma PS_gen_change {𝔰 𝔄 : Ideal (𝓞 F)} {s₀ A₀ s A Af c h : SInt 𝔪} (hs₀ : (s₀ : F) ≠ 0)
    (hA₀ : (A₀ : F) ≠ 0) (hc0 : (c : F) ≠ 0)
    (hrel : (s : F) * (A : F) = (c : F) * ((s₀ : F) * (A₀ : F))) :
    PS ι 𝔪 𝔰 𝔄 s₀ A₀ Af 1 h = PS ι 𝔪 𝔰 𝔄 s A Af c h := by
  unfold PS U
  refine finsum_congr fun d => finsum_congr fun v => ?_
  split_ifs
  · congr 3
    rw [hrel, coe_one']
    field_simp
  · rfl

/-! ### Generators and residue symbols -/

lemma residueSymbol_gen_mul (hχ : HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {𝔞 I J : Ideal (𝓞 F)}
    (h𝔞 : IsExterior 𝔪 𝔞) (hI : IsExterior 𝔪 I) (hJ : IsExterior 𝔪 J) :
    residueSymbol ι 𝔪 𝔞 (g.gen (I * J)) =
      residueSymbol ι 𝔪 𝔞 (g.gen I) * residueSymbol ι 𝔪 𝔞 (g.gen J) := by
  obtain ⟨ε, hε⟩ := gen_mul' g hI hJ
  rw [hε, mul_assoc, residueSymbol_unit_pow_six hχ h𝔞, residueSymbol_mul hχ h𝔞]

lemma residueSymbol_gen_top (hχ : HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {𝔞 : Ideal (𝓞 F)}
    (h𝔞 : IsExterior 𝔪 𝔞) : residueSymbol ι 𝔪 𝔞 (g.gen ⊤) = 1 := by
  obtain ⟨ε, hε⟩ := gen_top g
  rw [hε, ← mul_one ((ε : SInt 𝔪) ^ 6), residueSymbol_unit_pow_six hχ h𝔞,
    residueSymbol_one hχ h𝔞]

lemma residueSymbol_gen_pow (hχ : HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {𝔞 I : Ideal (𝓞 F)}
    (h𝔞 : IsExterior 𝔪 𝔞) (hI : IsExterior 𝔪 I) (n : ℕ) :
    residueSymbol ι 𝔪 𝔞 (g.gen (I ^ n)) = residueSymbol ι 𝔪 𝔞 (g.gen I) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Ideal.one_eq_top, residueSymbol_gen_top hχ g h𝔞]
  | succ n ih =>
    rw [pow_succ, residueSymbol_gen_mul hχ g h𝔞 (C3B.isExterior_pow hI n) hI, ih, pow_succ]

/-- Extended reciprocity: `χ_𝔟(gen P) = χ_P(gen 𝔟)` for an exterior `𝔟` prime to `P`. -/
lemma residueSymbol_gen_prime (hχ : HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {P : Ideal (𝓞 F)}
    (hP : P.IsPrime) (hPe : IsExterior 𝔪 P) (𝔟 : Ideal (𝓞 F)) :
    IsExterior 𝔪 𝔟 → ¬ 𝔟 ≤ P →
      residueSymbol ι 𝔪 𝔟 (g.gen P) = residueSymbol ι 𝔪 P (g.gen 𝔟) := by
  induction 𝔟 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h.1
  | h₂ u hu =>
    intro hue _
    have hu' : u = ⊤ := Ideal.isUnit_iff.mp hu
    subst hu'
    rw [C3B.residueSymbol_top, residueSymbol_gen_top hχ g hPe]
  | h₃ 𝔞 Q _ hQ ih =>
    intro hQa hle
    have hQp : Q.IsPrime := Ideal.isPrime_of_prime hQ
    have hQe : IsExterior 𝔪 Q := isExterior_of_mul_left hQa
    have hae : IsExterior 𝔪 𝔞 := isExterior_of_mul_right hQa
    have hQP : ¬ Q ≤ P := fun h => hle (le_trans Ideal.mul_le_left h)
    have haP : ¬ 𝔞 ≤ P := fun h => hle (le_trans Ideal.mul_le_right h)
    have hne : P ≠ Q := fun h => hQP (h ▸ le_rfl)
    rw [residueSymbol_mul_ideal _ _ hQe.1 hae.1, ih hae haP,
      residueSymbol_gen_mul hχ g hPe hQe hae, residueSymbol_prime hQp hQe.1,
      residueSymbol_prime hP hPe.1, residueSymbol_prime hP hPe.1,
      ← g.reciprocity P Q hP hQp hPe hQe hne]

/-! ### `ϑ` and norms -/

lemma thetaChar_mul (g : AllowedGen ι 𝔪) (χ : HeckeChar F 𝔪) {I J : Ideal (𝓞 F)}
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) : χ.thetaChar g (I * J) = χ.thetaChar g I * χ.thetaChar g J := by
  simp only [HeckeChar.thetaChar, gaussLambda, gaussG, normalizedFactors_mul hI hJ,
    Multiset.map_add, Multiset.prod_add, map_mul, χ.map_mul']
  ring

lemma sqrt_norm_mul_inv (I J : Ideal (𝓞 F)) :
    ((Real.sqrt (Ideal.absNorm (I * J)) : ℝ) : ℂ)⁻¹ =
      ((Real.sqrt (Ideal.absNorm I) : ℝ) : ℂ)⁻¹ * ((Real.sqrt (Ideal.absNorm J) : ℝ) : ℂ)⁻¹ := by
  rw [map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul, mul_inv]

/-! ### (3.10) -/

theorem gaussPhase_mul (hadd : HypAdd 𝔪) (hχ : HypChi ι 𝔪) (g : AllowedGen ι 𝔪)
    {𝔠₁ 𝔠₂ : Ideal (𝓞 F)} (h₁ : IsExterior 𝔪 𝔠₁) (h₂ : IsExterior 𝔪 𝔠₂)
    (hcop : IsCoprime 𝔠₁ 𝔠₂) (j : ℕ) :
    gaussPhase g j (𝔠₁ * 𝔠₂) =
      residueSymbol ι 𝔪 𝔠₁ (g.gen 𝔠₂) ^ j * residueSymbol ι 𝔪 𝔠₂ (g.gen 𝔠₁) ^ j *
        (gaussPhase g j 𝔠₁ * gaussPhase g j 𝔠₂) := by
  obtain ⟨ε, hε⟩ := gen_mul' g h₁ h₂
  set c₁ := g.gen 𝔠₁
  set c₂ := g.gen 𝔠₂
  have hc₁ := g.span_gen 𝔠₁ h₁
  have hc₂ := g.span_gen 𝔠₂ h₂
  have hc₁0 := C3B.gen_ne_zero g 𝔠₁ h₁
  have hc₂0 := C3B.gen_ne_zero g 𝔠₂ h₂
  have h12 := C3B.gen_ne_zero g (𝔠₁ * 𝔠₂) (C3B.isExterior_mul h₁ h₂)
  obtain ⟨α, β, hαβ⟩ := exists_ab (x := c₁) (y := c₂) (by rw [hc₁, hc₂]; exact isCoprime_map hcop)
  set c' : SInt 𝔪 := ((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) ^ 6
  have hεc : (ε : SInt 𝔪) ^ 6 * c' = 1 := unit_pow_mul_inv ε
  rw [gaussPhase_eq_GS, gaussPhase_eq_GS, gaussPhase_eq_GS, sqrt_norm_mul_inv]
  rw [GS_gen_change (c := c₁ * c₂) (c' := c') h12
    (by rw [Subalgebra.coe_pow]; exact pow_ne_zero _ (unit_coe_ne_zero _)) (by
    rw [hε]; have := castF (F := F) hεc; simp only [coe_mul', coe_one'] at this ⊢
    simp only [Subalgebra.coe_pow] at this ⊢
    linear_combination (-((c₁ : F) * (c₂ : F))) * this)]
  rw [GS_crt hadd h₁ h₂ hc₁ hc₂ hc₁0 hc₂0 hαβ]
  rw [GS_twist (C := (ε : SInt 𝔪) ^ 6 * c₂) hχ h₁ hc₁ hc₁0 (by
      rw [show (ε : SInt 𝔪) ^ 6 * c₂ * (c' * β) - 1 = -(α * c₁) by
        linear_combination c₂ * β * hεc + hαβ, ← hc₁]
      exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))),
    GS_twist (C := (ε : SInt 𝔪) ^ 6 * c₁) hχ h₂ hc₂ hc₂0 (by
      rw [show (ε : SInt 𝔪) ^ 6 * c₁ * (c' * α) - 1 = -(β * c₂) by
        linear_combination c₁ * α * hεc + hαβ, ← hc₂]
      exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))]
  rw [residueSymbol_unit_pow_six hχ h₁, residueSymbol_unit_pow_six hχ h₂]
  ring

/-! ### Cross-prime multiplicativity of the Poisson factor -/

lemma residueSymbol_units_pow_six (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    (u v : (SInt 𝔪)ˣ) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 𝔞 ((u : SInt 𝔪) ^ 6 * (v : SInt 𝔪) ^ 6 * x) = residueSymbol ι 𝔪 𝔞 x := by
  rw [mul_assoc, residueSymbol_unit_pow_six hχ h𝔞, residueSymbol_unit_pow_six hχ h𝔞]

/-- One side of the Chinese-remainder splitting, after the twists. -/
lemma PS_part (hχ : HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {𝔰 𝔄 𝔰' 𝔄' 𝔯' : Ideal (𝓞 F)}
    (h𝔰 : IsExterior 𝔪 𝔰) (h𝔄 : IsExterior 𝔪 𝔄) (h𝔄' : IsExterior 𝔪 𝔄')
    (h𝔯' : IsExterior 𝔪 𝔯') (hr' : IsCoprime 𝔯' (𝔰 * 𝔄)) (hA' : IsCoprime 𝔄' 𝔰)
    (εs εA εr : (SInt 𝔪)ˣ) {c e f : SInt 𝔪}
    (hEc : ((εs : SInt 𝔪) ^ 6 * (εA : SInt 𝔪) ^ 6) * c = 1)
    (hef : e * (g.gen 𝔰 * g.gen 𝔄) + f * (g.gen 𝔰' * g.gen 𝔄') = 1) (r : SInt 𝔪) :
    ∃ B' : SInt 𝔪, residueSymbol ι 𝔪 𝔰 (g.gen 𝔄') * residueSymbol ι 𝔪 𝔰 B' = 1 ∧
      PS ι 𝔪 𝔰 𝔄 (g.gen 𝔰) (g.gen 𝔄) (g.gen 𝔄 * ((εA : SInt 𝔪) ^ 6 * g.gen 𝔄')) (c * f)
          (((εr : SInt 𝔪) ^ 6 * g.gen 𝔯') ^ 6 * r) =
        residueSymbol ι 𝔪 𝔰 B' * residueSymbol ι 𝔪 𝔄 (g.gen 𝔰' * g.gen 𝔄') *
          PS ι 𝔪 𝔰 𝔄 (g.gen 𝔰) (g.gen 𝔄) (g.gen 𝔄) 1 r := by
  have hs := g.span_gen 𝔰 h𝔰
  have hA := g.span_gen 𝔄 h𝔄
  have hsA := span_gen_mul g h𝔰 h𝔄
  have hs0 := C3B.gen_ne_zero g 𝔰 h𝔰
  have hA0 := C3B.gen_ne_zero g 𝔄 h𝔄
  have hsAle𝔰 : Ideal.span {g.gen 𝔰 * g.gen 𝔄} ≤ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hs]; exact Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right _ _)
  have hsAle𝔄 : Ideal.span {g.gen 𝔰 * g.gen 𝔄} ≤ 𝔄.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hA]; exact Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left _ _)
  have hμcop : IsCoprime (Ideal.span {(εr : SInt 𝔪) ^ 6 * g.gen 𝔯'})
      (Ideal.span {g.gen 𝔰 * g.gen 𝔄}) := by
    rw [hsA]
    exact cop_mul (cop_pow (isCoprime_unit εr _) 6) (cop_gen g h𝔯' hr')
  obtain ⟨μ', hμ'⟩ := exists_inv_mod hμcop
  have hBcop : IsCoprime (Ideal.span {(εA : SInt 𝔪) ^ 6 * g.gen 𝔄'})
      (𝔰.map (algebraMap (𝓞 F) (SInt 𝔪))) :=
    cop_mul (cop_pow (isCoprime_unit εA _) 6) (cop_gen g h𝔄' hA')
  obtain ⟨B', hB'⟩ := exists_inv_mod hBcop
  refine ⟨B', ?_, ?_⟩
  · have := residueSymbol_mul_inv hχ h𝔰 hB'
    rwa [residueSymbol_unit_pow_six hχ h𝔰] at this
  set μ := (εr : SInt 𝔪) ^ 6 * g.gen 𝔯'
  have hl : μ ^ 6 * μ' ^ 6 - 1 ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← mul_pow]; exact hsAle𝔰 (pow_sub_one_mem hμ' 6)
  have hc : μ ^ 6 * μ' ^ 6 * (c * f) *
      ((εs : SInt 𝔪) ^ 6 * (εA : SInt 𝔪) ^ 6 * (g.gen 𝔰' * g.gen 𝔄')) - 1 ∈
        Ideal.span {g.gen 𝔰 * g.gen 𝔄} := by
    have e1 : μ ^ 6 * μ' ^ 6 * (c * f) *
        ((εs : SInt 𝔪) ^ 6 * (εA : SInt 𝔪) ^ 6 * (g.gen 𝔰' * g.gen 𝔄')) - 1 =
        ((μ * μ') ^ 6 - 1) - (μ * μ') ^ 6 * e * (g.gen 𝔰 * g.gen 𝔄) := by
      linear_combination (μ * μ') ^ 6 * f * (g.gen 𝔰' * g.gen 𝔄') * hEc + (μ * μ') ^ 6 * hef
    rw [e1]
    exact sub_mem (pow_sub_one_mem hμ' 6)
      (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
  rw [PS_twist hχ h𝔰 h𝔄 hs hA hs0 hA0 (B' := B') (l'' := μ' ^ 6) (l' := μ' ^ 6) hB' hl hc]
  have t1 : residueSymbol ι 𝔪 𝔰 (μ ^ 6) = 1 := by
    rw [residueSymbol_pow hχ h𝔰]
    exact residueSymbol_pow_six hχ h𝔰 (cop_mono hμcop hsAle𝔰)
  have t3 : residueSymbol ι 𝔪 𝔄 (μ' ^ 6) = 1 := by
    rw [residueSymbol_pow hχ h𝔄]
    exact residueSymbol_pow_six hχ h𝔄 (cop_mono (cop_of_inv hμ') hsAle𝔄)
  rw [t1, t3, residueSymbol_units_pow_six hχ h𝔄]
  ring

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

lemma not_le_mul {P I J : Ideal (𝓞 F)} (hP : P.IsPrime) (hI : ¬ I ≤ P) (hJ : ¬ J ≤ P) :
    ¬ I * J ≤ P := fun h => (hP.mul_le.mp h).elim hI hJ

lemma not_le_pow {P I : Ideal (𝓞 F)} (hP : P.IsPrime) (hI : ¬ I ≤ P) (n : ℕ) :
    ¬ I ^ n ≤ P := fun h => hI (@Ideal.IsPrime.le_of_pow_le _ _ _ _ hP _ h)

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3R_Mul: cross-prime multiplicativity of the coefficients of `ℱ_u` for every `u`

C3M's `poissonFactor_mul` and `coeff_mul` with `h = u r⁶` in place of `r⁶`: the extra factor `u`
is common to both sides of the Chinese-remainder splitting, and the cross sixth powers are removed
by the same twists. -/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

theorem poissonFactor_mul_u (u : SInt 𝔪) (hadd : HypAdd 𝔪) (hχ : HypChi ι 𝔪) (g : AllowedGen ι 𝔪)
    {𝔰₁ 𝔰₂ 𝔄₁ 𝔄₂ 𝔯₁ 𝔯₂ : Ideal (𝓞 F)} (h𝔰₁ : IsExterior 𝔪 𝔰₁) (h𝔰₂ : IsExterior 𝔪 𝔰₂)
    (h𝔄₁ : IsExterior 𝔪 𝔄₁) (h𝔄₂ : IsExterior 𝔪 𝔄₂) (h𝔯₁ : IsExterior 𝔪 𝔯₁)
    (h𝔯₂ : IsExterior 𝔪 𝔯₂) (hcop : IsCoprime (𝔰₁ * 𝔄₁) (𝔰₂ * 𝔄₂))
    (hr₂ : IsCoprime 𝔯₂ (𝔰₁ * 𝔄₁)) (hr₁ : IsCoprime 𝔯₁ (𝔰₂ * 𝔄₂)) :
    residueSymbol ι 𝔪 𝔰₁ (g.gen 𝔄₂) * residueSymbol ι 𝔪 𝔰₂ (g.gen 𝔄₁) *
        poissonFactor g (𝔰₁ * 𝔰₂) (𝔄₁ * 𝔄₂) (u * g.gen (𝔯₁ * 𝔯₂) ^ 6) =
      residueSymbol ι 𝔪 𝔄₁ (g.gen 𝔰₂ * g.gen 𝔄₂) *
        residueSymbol ι 𝔪 𝔄₂ (g.gen 𝔰₁ * g.gen 𝔄₁) *
        (poissonFactor g 𝔰₁ 𝔄₁ (u * g.gen 𝔯₁ ^ 6) * poissonFactor g 𝔰₂ 𝔄₂ (u * g.gen 𝔯₂ ^ 6)) := by
  obtain ⟨εs, hεs⟩ := gen_mul' g h𝔰₁ h𝔰₂
  obtain ⟨εA, hεA⟩ := gen_mul' g h𝔄₁ h𝔄₂
  obtain ⟨εr, hεr⟩ := gen_mul' g h𝔯₁ h𝔯₂
  have hs₁ := g.span_gen 𝔰₁ h𝔰₁
  have hs₂ := g.span_gen 𝔰₂ h𝔰₂
  have hA₁ := g.span_gen 𝔄₁ h𝔄₁
  have hA₂ := g.span_gen 𝔄₂ h𝔄₂
  have hs₁0 := C3B.gen_ne_zero g 𝔰₁ h𝔰₁
  have hs₂0 := C3B.gen_ne_zero g 𝔰₂ h𝔰₂
  have hA₁0 := C3B.gen_ne_zero g 𝔄₁ h𝔄₁
  have hA₂0 := C3B.gen_ne_zero g 𝔄₂ h𝔄₂
  have hsA₁ := span_gen_mul g h𝔰₁ h𝔄₁
  have hsA₂ := span_gen_mul g h𝔰₂ h𝔄₂
  obtain ⟨α, β, hαβ⟩ := exists_ab (x := g.gen 𝔰₁ * g.gen 𝔄₁) (y := g.gen 𝔰₂ * g.gen 𝔄₂)
    (by rw [hsA₁, hsA₂]; exact isCoprime_map hcop)
  have ha := unit_pow_mul_inv εs
  have hb := unit_pow_mul_inv εA
  set c : SInt 𝔪 := ((εs⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) ^ 6 * ((εA⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) ^ 6
    with hcdef
  have hEc : ((εs : SInt 𝔪) ^ 6 * (εA : SInt 𝔪) ^ 6) * c = 1 := by
    rw [hcdef]
    linear_combination ((εA : SInt 𝔪) ^ 6 * ((εA⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) ^ 6) * ha + hb
  have hEcF := castF (F := F) hEc
  simp only [coe_mul', coe_one', Subalgebra.coe_pow] at hEcF
  have hc0 : (c : F) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hEcF; exact zero_ne_one hEcF
  have step1 : poissonFactor g (𝔰₁ * 𝔰₂) (𝔄₁ * 𝔄₂) (u * g.gen (𝔯₁ * 𝔯₂) ^ 6) =
      PS ι 𝔪 𝔰₁ 𝔄₁ (g.gen 𝔰₁) (g.gen 𝔄₁) (g.gen 𝔄₁ * ((εA : SInt 𝔪) ^ 6 * g.gen 𝔄₂)) (c * β)
          (((εr : SInt 𝔪) ^ 6 * g.gen 𝔯₂) ^ 6 * (u * g.gen 𝔯₁ ^ 6)) *
        PS ι 𝔪 𝔰₂ 𝔄₂ (g.gen 𝔰₂) (g.gen 𝔄₂) (g.gen 𝔄₂ * ((εA : SInt 𝔪) ^ 6 * g.gen 𝔄₁))
          (c * α) (((εr : SInt 𝔪) ^ 6 * g.gen 𝔯₁) ^ 6 * (u * g.gen 𝔯₂ ^ 6)) := by
    rw [poissonFactor_eq_PS, hεs, hεA, hεr]
    have h0s : (((εs : SInt 𝔪) ^ 6 * g.gen 𝔰₁ * g.gen 𝔰₂ : SInt 𝔪) : F) ≠ 0 := by
      simp only [coe_mul', Subalgebra.coe_pow]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (unit_coe_ne_zero _)) hs₁0) hs₂0
    have h0A : (((εA : SInt 𝔪) ^ 6 * g.gen 𝔄₁ * g.gen 𝔄₂ : SInt 𝔪) : F) ≠ 0 := by
      simp only [coe_mul', Subalgebra.coe_pow]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (unit_coe_ne_zero _)) hA₁0) hA₂0
    rw [PS_gen_change (s := g.gen 𝔰₁ * g.gen 𝔰₂) (A := g.gen 𝔄₁ * g.gen 𝔄₂) (c := c) h0s h0A hc0
      (by
        simp only [coe_mul', Subalgebra.coe_pow]
        linear_combination (-((g.gen 𝔰₁ : F) * (g.gen 𝔰₂ : F) *
          ((g.gen 𝔄₁ : F) * (g.gen 𝔄₂ : F)))) * hEcF)]
    rw [PS_crt hadd h𝔰₁ h𝔰₂ h𝔄₁ h𝔄₂ hs₁ hs₂ hA₁ hA₂ hs₁0 hs₂0 hA₁0 hA₂0 hαβ
      (B := (εA : SInt 𝔪) ^ 6) (by ring)]
    congr 1
    · congr 1 <;> ring
    · congr 1 <;> ring
  obtain ⟨B₁', hinv1, hP1⟩ := PS_part hχ g h𝔰₁ h𝔄₁ h𝔄₂ h𝔯₂ hr₂
    hcop.symm.of_mul_left_right.of_mul_right_left εs εA εr hEc hαβ (u * g.gen 𝔯₁ ^ 6)
  obtain ⟨B₂', hinv2, hP2⟩ := PS_part hχ g h𝔰₂ h𝔄₂ h𝔄₁ h𝔯₁ hr₁
    hcop.of_mul_left_right.of_mul_right_left εs εA εr hEc (by rw [add_comm]; exact hαβ)
    (u * g.gen 𝔯₂ ^ 6)
  rw [step1, hP1, hP2, ← poissonFactor_eq_PS, ← poissonFactor_eq_PS]
  linear_combination (residueSymbol ι 𝔪 𝔄₁ (g.gen 𝔰₂ * g.gen 𝔄₂) *
      residueSymbol ι 𝔪 𝔄₂ (g.gen 𝔰₁ * g.gen 𝔄₁) * poissonFactor g 𝔰₁ 𝔄₁ (u * g.gen 𝔯₁ ^ 6) *
      poissonFactor g 𝔰₂ 𝔄₂ (u * g.gen 𝔯₂ ^ 6)) *
    (residueSymbol ι 𝔪 𝔰₂ (g.gen 𝔄₁) * residueSymbol ι 𝔪 𝔰₂ B₂' * hinv1 + hinv2)


theorem coeff_mul_u (u : SInt 𝔪) (hadd : HypAdd 𝔪) (hχ : HypChi ι 𝔪) (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪)
    {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hPe : IsExterior 𝔪 P) (e₀ l k m : ℕ)
    {𝔠 𝔫 𝔰 𝔯 : Ideal (𝓞 F)} (h𝔠 : IsExterior 𝔪 𝔠) (h𝔫 : IsExterior 𝔪 𝔫)
    (h𝔰 : IsExterior 𝔪 𝔰) (h𝔯 : IsExterior 𝔪 𝔯) (h𝔠P : ¬ 𝔠 ≤ P) (h𝔫P : ¬ 𝔫 ≤ P)
    (h𝔰P : ¬ 𝔰 ≤ P) (h𝔯P : ¬ 𝔯 ≤ P) :
    gaussPhase g 2 (P ^ e₀ * 𝔠) * χ.thetaChar g (P ^ e₀ * 𝔠 * (P ^ l * 𝔫) ^ 3) *
        poissonFactor g (P ^ k * 𝔰) (P ^ e₀ * 𝔠 * (P ^ l * 𝔫) ^ 3) (u * g.gen (P ^ m * 𝔯) ^ 6) =
      gaussPhase g 2 (P ^ e₀) * χ.thetaChar g (P ^ e₀ * (P ^ l) ^ 3) *
          poissonFactor g (P ^ k) (P ^ e₀ * (P ^ l) ^ 3) (u * g.gen (P ^ m) ^ 6) *
        (gaussPhase g 2 𝔠 * χ.thetaChar g (𝔠 * 𝔫 ^ 3) *
          poissonFactor g 𝔰 (𝔠 * 𝔫 ^ 3) (u * g.gen 𝔯 ^ 6)) := by
  have hP0 := hPe.1
  have hPj : ∀ j : ℕ, IsExterior 𝔪 (P ^ j) := C3B.isExterior_pow hPe
  set T := P ^ e₀ * (P ^ l) ^ 3 with hTdef
  set A' := 𝔠 * 𝔫 ^ 3 with hA'def
  have hT : IsExterior 𝔪 T := C3B.isExterior_mul (hPj e₀) (C3B.isExterior_pow (hPj l) 3)
  have hA' : IsExterior 𝔪 A' := C3B.isExterior_mul h𝔠 (C3B.isExterior_pow h𝔫 3)
  have hTpow : T = P ^ (e₀ + 3 * l) := by rw [hTdef, ← pow_mul, ← pow_add, mul_comm l 3]
  have hA'P : ¬ A' ≤ P := not_le_mul hP h𝔠P (not_le_pow hP h𝔫P 3)
  have cop : ∀ (J : Ideal (𝓞 F)) (j : ℕ), ¬ J ≤ P → IsCoprime (P ^ j) J :=
    fun J j hJ => isCoprime_pow_of_not_le hP hP0 hJ j
  have hcop : IsCoprime (P ^ k * T) (𝔰 * A') := by
    rw [hTpow, ← pow_add]; exact cop _ _ (not_le_mul hP h𝔰P hA'P)
  have hr₂ : IsCoprime 𝔯 (P ^ k * T) := by
    rw [hTpow, ← pow_add]; exact (cop _ _ h𝔯P).symm
  have hr₁ : IsCoprime (P ^ m) (𝔰 * A') := cop _ _ (not_le_mul hP h𝔰P hA'P)
  -- the three factorizations
  have hI : P ^ e₀ * 𝔠 * (P ^ l * 𝔫) ^ 3 = T * A' := by rw [hTdef, hA'def]; ring
  rw [hI, gaussPhase_mul hadd hχ g (hPj e₀) h𝔠 (cop _ _ h𝔠P) 2, thetaChar_mul g χ hT.1 hA'.1]
  have hF := poissonFactor_mul_u u hadd hχ g (hPj k) h𝔰 hT hA' (hPj m) h𝔯 hcop hr₂ hr₁
  -- the residue symbols
  set π := g.gen P
  set a := residueSymbol ι 𝔪 P (g.gen 𝔠)
  set bb := residueSymbol ι 𝔪 P (g.gen 𝔫)
  set σ := residueSymbol ι 𝔪 P (g.gen 𝔰)
  set w := residueSymbol ι 𝔪 P (g.gen A')
  have hrec : ∀ 𝔟 : Ideal (𝓞 F), IsExterior 𝔪 𝔟 → ¬ 𝔟 ≤ P →
      residueSymbol ι 𝔪 𝔟 π = residueSymbol ι 𝔪 P (g.gen 𝔟) :=
    fun 𝔟 h1 h2 => residueSymbol_gen_prime hχ g hP hPe 𝔟 h1 h2
  have hPpow : ∀ (j : ℕ) (x : SInt 𝔪),
      residueSymbol ι 𝔪 (P ^ j) x = residueSymbol ι 𝔪 P x ^ j := by
    intro j x
    rw [residueSymbol_prime_pow hP hP0, residueSymbol_prime hP hP0]
  have hTsym : ∀ x : SInt 𝔪,
      residueSymbol ι 𝔪 T x = residueSymbol ι 𝔪 P x ^ e₀ * residueSymbol ι 𝔪 P x ^ (l * 3) := by
    intro x
    rw [hTdef, residueSymbol_mul_ideal _ _ (hPj e₀).1 (C3B.isExterior_pow (hPj l) 3).1,
      ← pow_mul, hPpow, hPpow]
  have hgenT : ∀ 𝔞 : Ideal (𝓞 F), IsExterior 𝔪 𝔞 →
      residueSymbol ι 𝔪 𝔞 (g.gen T) =
        residueSymbol ι 𝔪 𝔞 π ^ e₀ * (residueSymbol ι 𝔪 𝔞 π ^ l) ^ 3 := by
    intro 𝔞 h𝔞
    rw [hTdef, residueSymbol_gen_mul hχ g h𝔞 (hPj e₀) (C3B.isExterior_pow (hPj l) 3),
      residueSymbol_gen_pow hχ g h𝔞 hPe, residueSymbol_gen_pow hχ g h𝔞 (hPj l),
      residueSymbol_gen_pow hχ g h𝔞 hPe]
  have hw : w = a * bb ^ 3 := by
    simp only [w, a, bb]
    rw [hA'def, residueSymbol_gen_mul hχ g hPe h𝔠 (C3B.isExterior_pow h𝔫 3),
      residueSymbol_gen_pow hχ g hPe h𝔫]
  have six : ∀ 𝔟 : Ideal (𝓞 F), IsExterior 𝔪 𝔟 → ¬ 𝔟 ≤ P →
      residueSymbol ι 𝔪 P (g.gen 𝔟) ^ 6 = 1 := by
    intro 𝔟 h1 h2
    have hc : IsCoprime 𝔟 P := by
      have := (cop 𝔟 1 h2).symm; rwa [pow_one] at this
    exact residueSymbol_pow_six hχ hPe (cop_gen g h1 hc)
  have ha6 : a ^ 6 = 1 := six 𝔠 h𝔠 h𝔠P
  have hb6 : bb ^ 6 = 1 := six 𝔫 h𝔫 h𝔫P
  have hσ6 : σ ^ 6 = 1 := six 𝔰 h𝔰 h𝔰P
  have hw6 : w ^ 6 = 1 := six A' hA' hA'P
  have hσ0 : σ ≠ 0 := fun h => by rw [h] at hσ6; norm_num at hσ6
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw6; norm_num at hw6
  -- evaluate the twists in `hF`
  rw [hPpow, hgenT 𝔰 h𝔰, hrec 𝔰 h𝔰 h𝔰P, hTsym,
    residueSymbol_mul hχ hPe, residueSymbol_mul hχ hA',
    hgenT A' hA', residueSymbol_gen_pow hχ g hA' hPe, hrec A' hA' hA'P] at hF
  -- evaluate the twists of `γ₂`
  rw [hPpow, residueSymbol_gen_pow hχ g h𝔠 hPe, hrec 𝔠 h𝔠 h𝔠P]
  have key : (a ^ e₀) ^ 2 * (a ^ e₀) ^ 2 * (w ^ e₀ * (w ^ l) ^ 3) ^ 2 = 1 := by
    rw [hw]
    have e : (a ^ e₀) ^ 2 * (a ^ e₀) ^ 2 * ((a * bb ^ 3) ^ e₀ * ((a * bb ^ 3) ^ l) ^ 3) ^ 2 =
        (a ^ 6) ^ (e₀ + l) * (bb ^ 6) ^ (e₀ + 3 * l) := by ring
    rw [e, ha6, hb6, one_pow, one_pow, one_mul]
  have hK : w ^ k * (σ ^ e₀ * (σ ^ l) ^ 3) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hw0) (mul_ne_zero (pow_ne_zero _ hσ0)
      (pow_ne_zero _ (pow_ne_zero _ hσ0)))
  apply mul_left_cancel₀ hK
  linear_combination ((a ^ e₀) ^ 2 * (a ^ e₀) ^ 2 * (gaussPhase g 2 (P ^ e₀) * gaussPhase g 2 𝔠) *
      (χ.thetaChar g T * χ.thetaChar g A')) * hF +
    (gaussPhase g 2 (P ^ e₀) * gaussPhase g 2 𝔠 * (χ.thetaChar g T * χ.thetaChar g A') *
      poissonFactor g (P ^ k) T (u * g.gen (P ^ m) ^ 6) * poissonFactor g 𝔰 A' (u * g.gen 𝔯 ^ 6) *
      w ^ k * (σ ^ e₀ * (σ ^ l) ^ 3)) * key

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3B_Final: the cut 8a9ce98d from `CutMul`, `CutF`, `CutHD`, `CutG6` -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

lemma gaussPhase_prime_pow {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪)
    (P : Ideal (𝓞 F)) {e₀ : ℕ} (he : e₀ ≤ 1) :
    gaussPhase g 2 (P ^ e₀) = gaussPhase g 2 P ^ e₀ := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he with rfl | rfl
  · rw [pow_zero, pow_zero, Ideal.one_eq_top, gaussPhase_top]
  · rw [pow_one, pow_one]

/-- The local value `b(P^{e₀}, P^l, P^k, P^m) = principalLocalCoeff …`, from `CutF`, `CutHD`,
`CutG6`. -/
lemma coeffOne_local {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) (χ : HeckeChar F 𝔪)
    (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hP0 : P ≠ ⊥) (e₀ l k m : ℕ) (he : e₀ ≤ 1)
    (hF : poissonFactor g (P ^ k) (P ^ e₀ * (P ^ l) ^ 3) (g.gen (P ^ m) ^ 6) =
      poissonLocal (Ideal.absNorm P) (gaussPhase g 1 P) e₀ l k m)
    (hHD : gaussPhase g 1 P * gaussPhase g 2 P * starRingEnd ℂ (gaussLambda ι P) *
        starRingEnd ℂ (gaussG g P) = -1)
    (hG6 : starRingEnd ℂ (gaussG g P) ^ 6 = 1) :
    coeffOne g χ (P ^ e₀) (P ^ l) (P ^ k) (P ^ m) =
      principalLocalCoeff (Ideal.absNorm P) (χ.toFun P)
        (starRingEnd ℂ (jacobiPhaseSix ι P) * χ.toFun P ^ 6) e₀ l k m := by
  have hpow : P ^ e₀ * (P ^ l) ^ 3 = P ^ (e₀ + 3 * l) := by
    rw [← pow_mul, ← pow_add, mul_comm l 3]
  rw [coeffOne, hF, gaussPhase_prime_pow g P he, hpow, thetaChar_prime_pow g χ hP hP0]
  apply principalLocalCoeff_eq _ _ _ _ _ _ _ _ _ _ _ _ he
  · show gaussPhase g 1 P * gaussPhase g 2 P *
        (starRingEnd ℂ (gaussLambda ι P) * starRingEnd ℂ (gaussG g P) * χ.toFun P) = _
    linear_combination (χ.toFun P) * hHD
  · show (starRingEnd ℂ (gaussLambda ι P) * starRingEnd ℂ (gaussG g P) * χ.toFun P) ^ 6 = _
    rw [mul_pow, mul_pow, hG6, ← map_pow, gaussLambda_prime_pow_six hP hP0, mul_one]

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3R_Tab: the coefficient table at `P ∤ u` ((7.14)) and the easy facts at `P ∣ u`

* `pf_twist`: `F(𝔰, 𝔄, u h) = χ_𝔰(u) χ_𝔄(u') F(𝔰, 𝔄, h)` for `u u' ≡ 1 (mod s A)`.
* `coeff_unram`: at `P ∤ u`, `a_u(P^e) = χ_P(u)^k conj(χ_P(u))^{e₀+3l} a_1(P^e)`.
* `pf_ram_t0`: `F(P^k, 1, H) = 0` for `k ≥ 1` and `H ∈ PR`. -/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace L3R

open C3M

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

lemma pf_twist (hχ : HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {𝔰 𝔄 : Ideal (𝓞 F)}
    (h𝔰 : IsExterior 𝔪 𝔰) (h𝔄 : IsExterior 𝔪 𝔄) {u u' : SInt 𝔪}
    (hu : u * u' - 1 ∈ Ideal.span {g.gen 𝔰 * g.gen 𝔄}) (h : SInt 𝔪) :
    poissonFactor g 𝔰 𝔄 (u * h) =
      residueSymbol ι 𝔪 𝔰 u * residueSymbol ι 𝔪 𝔄 u' * poissonFactor g 𝔰 𝔄 h := by
  rw [poissonFactor_eq_PS, poissonFactor_eq_PS]
  have hs := g.span_gen 𝔰 h𝔰
  have hA := g.span_gen 𝔄 h𝔄
  have hs0 := C3B.gen_ne_zero g 𝔰 h𝔰
  have hA0 := C3B.gen_ne_zero g 𝔄 h𝔄
  have hle : Ideal.span {g.gen 𝔰 * g.gen 𝔄} ≤ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hs]; exact Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right _ _)
  have key := PS_twist (ι := ι) hχ h𝔰 h𝔄 hs hA hs0 hA0 (c := 1) (h := h) (B := 1) (B' := 1)
    (l := u) (l' := u') (l'' := u') (C := 1) (by simp) (hle hu) (by simpa using hu)
  rw [mul_one] at key
  rw [key, residueSymbol_one hχ h𝔰, residueSymbol_one hχ h𝔄]
  ring

lemma conj_eq_of_mul_eq_one {θ θ' : ℂ} (h6 : θ ^ 6 = 1) (h : θ * θ' = 1) :
    θ' = starRingEnd ℂ θ := by
  have hn : ‖θ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h6 (by norm_num)
  have hθ0 : θ ≠ 0 := fun h0 => by rw [h0, norm_zero] at hn; exact zero_ne_one hn
  have h1 : θ' = θ⁻¹ := eq_inv_of_mul_eq_one_right h
  rw [h1, Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
  simp

/-- The unit twist of the coefficients at `P ∤ u`. -/
theorem coeff_unram (hχ : HypChi ι 𝔪) (g : AllowedGen ι 𝔪) (χ : HeckeChar F 𝔪) (u : SInt 𝔪)
    {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hPe : IsExterior 𝔪 P)
    (hu : IsCoprime (Ideal.span {u}) (P.map (algebraMap (𝓞 F) (SInt 𝔪)))) (e₀ l k m : ℕ) :
    C3A.freqCoeff g χ u (P ^ e₀) (P ^ l) (P ^ k) (P ^ m) =
      residueSymbol ι 𝔪 P u ^ k * starRingEnd ℂ (residueSymbol ι 𝔪 P u) ^ (e₀ + 3 * l) *
        C3B.coeffOne g χ (P ^ e₀) (P ^ l) (P ^ k) (P ^ m) := by
  have hP0 := hPe.1
  have hpow : P ^ e₀ * (P ^ l) ^ 3 = P ^ (e₀ + 3 * l) := by
    rw [← pow_mul, ← pow_add, mul_comm l 3]
  set t := e₀ + 3 * l
  have hext : ∀ j : ℕ, IsExterior 𝔪 (P ^ j) := C3B.isExterior_pow hPe
  -- an inverse of `u` modulo `P^(k+t+1)`
  have hcop : IsCoprime (Ideal.span {u}) ((P ^ (k + t + 1)).map (algebraMap (𝓞 F) (SInt 𝔪))) := by
    rw [Ideal.map_pow]; exact hu.pow_right
  obtain ⟨u', hu'⟩ := exists_inv_mod hcop
  have hle1 : (P ^ (k + t + 1)).map (algebraMap (𝓞 F) (SInt 𝔪)) ≤
      Ideal.span {g.gen (P ^ k) * g.gen (P ^ t)} := by
    rw [← Ideal.span_singleton_mul_span_singleton, g.span_gen _ (hext k), g.span_gen _ (hext t),
      ← Ideal.map_mul, ← pow_add]
    exact Ideal.map_mono (Ideal.pow_le_pow_right (by omega))
  have hle2 : (P ^ (k + t + 1)).map (algebraMap (𝓞 F) (SInt 𝔪)) ≤
      P.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
    Ideal.map_mono (by
      calc P ^ (k + t + 1) ≤ P ^ 1 := Ideal.pow_le_pow_right (by omega)
        _ = P := pow_one P)
  have htw := pf_twist hχ g (hext k) (hext t) (hle1 hu') (g.gen (P ^ m) ^ 6)
  have hθθ : residueSymbol ι 𝔪 P u * residueSymbol ι 𝔪 P u' = 1 :=
    residueSymbol_mul_inv hχ hPe (hle2 hu')
  have h6 : residueSymbol ι 𝔪 P u ^ 6 = 1 := residueSymbol_pow_six hχ hPe hu
  have hconj := conj_eq_of_mul_eq_one h6 hθθ
  unfold C3A.freqCoeff C3B.coeffOne
  rw [hpow, htw, residueSymbol_prime_pow hP hP0, residueSymbol_prime_pow hP hP0,
    ← residueSymbol_prime hP hP0, ← residueSymbol_prime hP hP0, hconj]
  ring

/-- `F(P^k, 1, H) = 0` for `k ≥ 1` and `H ∈ PR`. -/
theorem pf_ram_t0 (hχ : HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {P : Ideal (𝓞 F)} (hP : P.IsPrime)
    (hPe : IsExterior 𝔪 P) {k : ℕ} (hk : 1 ≤ k) {H : SInt 𝔪}
    (hH : H ∈ P.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    poissonFactor g (P ^ k) (P ^ 0) H = 0 := by
  classical
  have hP0 := hPe.1
  obtain ⟨α, hα⟩ := gen_top g
  have hα' : g.gen (P ^ 0) = (α : SInt 𝔪) ^ 6 := by rw [pow_zero, Ideal.one_eq_top]; exact hα
  have hk1 : (P ^ k).map (algebraMap (𝓞 F) (SInt 𝔪)) ≤ P.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
    Ideal.map_mono (by
      calc P ^ k ≤ P ^ 1 := Ideal.pow_le_pow_right hk
        _ = P := pow_one P)
  unfold poissonFactor
  refine (finsum_congr fun d => ?_).trans finsum_zero
  split_ifs with hc
  · have hAq : g.gen (P ^ 0) * quotLift d ∈ P.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
      have := sub_mem hH (hk1 hc); rwa [sub_sub_cancel] at this
    have hq : quotLift d ∈ P.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
      rw [hα'] at hAq
      have := Ideal.mul_mem_left _ (((α⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) ^ 6) hAq
      rwa [← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul] at this
    rw [residueSymbol_prime_pow hP hP0]
    have : sexticResidueSymbol ι 𝔪 P (quotLift d) = 0 := by
      unfold sexticResidueSymbol
      rw [if_pos (Ideal.Quotient.eq_zero_iff_mem.mpr hq)]
    rw [this, zero_pow (by omega), zero_mul]
  · rfl

end L3R

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

lemma chi_neg_one (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) :
    chi ι h hω (-1) = 1 := by
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have hne : (-1 : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ≠ 0 :=
    neg_ne_zero.2 one_ne_zero
  have heven : Even ((Ideal.absNorm v.asIdeal - 1) / 6) := by
    obtain ⟨k, hk⟩ := h.twelve
    rw [hk, show 12 * k = 6 * (2 * k) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    exact even_two_mul k
  rw [chi_eq_pow h hω hne (i := 0) (by rw [heven.neg_one_pow, pow_zero]), pow_zero]

lemma chi_pow_six_apply (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) :
    chi ι h hω y ^ 6 = 1 := by
  obtain ⟨i, -, hi⟩ := exists_pow_e h hω hy
  rw [chi_eq_pow h hω hy hi, ← pow_mul, mul_comm, pow_mul, (iota_omega_prim hω).pow_eq_one,
    one_pow]

lemma chi_pow_six (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) :
    chi ι h hω ^ 6 = 1 := by
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  ext u
  rw [MulChar.pow_apply' _ (by norm_num), MulChar.one_apply_coe]
  exact chi_pow_six_apply h hω u.ne_zero

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
end

section
section
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

lemma quotLift_mk_sub {I : Ideal (SInt 𝔪)} (x : SInt 𝔪) :
    quotLift (Ideal.Quotient.mk I x) - x ∈ I := by
  rw [← Ideal.Quotient.eq]; exact Function.surjInv_eq Ideal.Quotient.mk_surjective _

lemma mk_quotLift {I : Ideal (SInt 𝔪)} (y : SInt 𝔪 ⧸ I) :
    Ideal.Quotient.mk I (quotLift y) = y :=
  Function.surjInv_eq Ideal.Quotient.mk_surjective _

/-- `e(x / gen 𝔞)` depends only on `x mod 𝔞 R`. -/
lemma sAddChar_div_congr (g : AllowedGen ι 𝔪) (𝔞 : Ideal (𝓞 F)) (h𝔞 : IsExterior 𝔪 𝔞)
    {x x' : SInt 𝔪} (hx : x - x' ∈ 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    sAddChar 𝔪 ((x : F) / (g.gen 𝔞 : F)) = sAddChar 𝔪 ((x' : F) / (g.gen 𝔞 : F)) := by
  have : (x : F) / (g.gen 𝔞 : F) =
      (x' : F) / (g.gen 𝔞 : F) + ((x - x' : SInt 𝔪) : F) / (g.gen 𝔞 : F) := by
    rw [Subalgebra.coe_sub]; ring
  rw [this, C3B.sAddChar_add_mem _ _ (C3B.div_gen_mem g 𝔞 h𝔞 _ hx)]

/-- The additive character `y ↦ e(y / gen P)` of `L`. -/
noncomputable def psi (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) :
    AddChar (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ℂ where
  toFun y := sAddChar 𝔪 ((quotLift y : F) / (g.gen v.asIdeal : F))
  map_zero_eq_one' := by
    have h0 : quotLift (0 : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ∈
        v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, mk_quotLift]
    exact C3B.sAddChar_of_mem _ (C3B.div_gen_mem g _ h.ext _ h0)
  map_add_eq_mul' := by
    intro a b
    have hab : quotLift (a + b) - (quotLift a + quotLift b) ∈
        v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
      rw [← Ideal.Quotient.eq, map_add, mk_quotLift, mk_quotLift, mk_quotLift]
    rw [sAddChar_div_congr g _ h.ext hab, Subalgebra.coe_add, add_div,
      sAddChar_div_gen_add g _ h.ext]

lemma psi_apply (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) (y) :
    psi g h y = sAddChar 𝔪 ((quotLift y : F) / (g.gen v.asIdeal : F)) := rfl

lemma psi_mk (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) (x : SInt 𝔪) :
    psi g h (Ideal.Quotient.mk _ x) = sAddChar 𝔪 ((x : F) / (g.gen v.asIdeal : F)) :=
  sAddChar_div_congr g _ h.ext (quotLift_mk_sub x)

lemma psi_isPrimitive (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) : (psi g h).IsPrimitive := by
  intro a ha hone
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hx : x ∉ (v.asIdeal ^ 1).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [pow_one]; rwa [Ne, Ideal.Quotient.eq_zero_iff_mem] at ha
  obtain ⟨r, hr⟩ := exists_sAddChar_ne_one g h.notS h.cop h.diff le_rfl x hx
  apply hr
  have := congrArg (fun φ => φ (Ideal.Quotient.mk _ r)) hone
  simp only [AddChar.mulShift_apply, AddChar.one_apply] at this
  rw [← map_mul, psi_mk, Subalgebra.coe_mul] at this
  rw [pow_one]
  exact this

/-! ### Characters on the finite field `L` -/

section field

variable (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
variable [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]

include h hω

lemma card_L : Fintype.card (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) =
    Ideal.absNorm v.asIdeal := by
  rw [← Nat.card_eq_fintype_card, natCard_L h]

lemma chi_pow_mod (n : ℕ) : chi ι h hω ^ n = chi ι h hω ^ (n % 6) := by
  conv_lhs => rw [← Nat.div_add_mod n 6, pow_add, pow_mul, chi_pow_six h hω, one_pow, one_mul]

lemma chi_pow_neg_one (j : ℕ) : (chi ι h hω ^ j) (-1) = 1 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [pow_zero]
    exact MulChar.one_apply (isUnit_one.neg (α := SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))))
  rw [MulChar.pow_apply' _ hj.ne', chi_neg_one h hω, one_pow]

lemma chi_pow_inv (j k : ℕ) (hjk : (j + k) % 6 = 0) : (chi ι h hω ^ j)⁻¹ = chi ι h hω ^ k := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← pow_add, chi_pow_mod h hω, hjk, pow_zero]

variable (g : AllowedGen ι 𝔪)

/-- `g(φ, ψ⁻¹) = g(φ, ψ)` for the powers of `χ` (as `χ(-1) = 1`). -/
lemma gs_inv_psi (j : ℕ) :
    gaussSum (chi ι h hω ^ j) (psi g h)⁻¹ = gaussSum (chi ι h hω ^ j) (psi g h) := by
  have h1 := chi_pow_neg_one (ι := ι) h hω j
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have := mul_gaussSum_inv_eq_gaussSum (chi ι h hω ^ j) (psi g h)
  rw [h1, one_mul] at this
  exact this

/-- `g_j g_k = N P` for `j + k ≡ 0 (mod 6)`, `6 ∤ j`. -/
lemma gs_mul_gs {j k : ℕ} (hj : ¬ 6 ∣ j) (hjk : (j + k) % 6 = 0) :
    gaussSum (chi ι h hω ^ j) (psi g h) * gaussSum (chi ι h hω ^ k) (psi g h) =
      Ideal.absNorm v.asIdeal := by
  have hχ := chi_pow_ne_one (ι := ι) h hω hj
  have hψ := psi_isPrimitive g h
  have hcard := card_L h hω
  have hinv := chi_pow_inv (ι := ι) h hω j k hjk
  have hk := gs_inv_psi h hω g k
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [hinv, hk, hcard] at this
  exact this

/-- `conj g_j = g_k` for `j + k ≡ 0 (mod 6)`. -/
lemma star_gs (j k : ℕ) (hjk : (j + k) % 6 = 0) :
    starRingEnd ℂ (gaussSum (chi ι h hω ^ j) (psi g h)) = gaussSum (chi ι h hω ^ k) (psi g h) := by
  have hinv := chi_pow_inv (ι := ι) h hω j k hjk
  have hk := gs_inv_psi h hω g k
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have := star_gaussSum_eq (chi ι h hω ^ j) (psi g h)
  rw [hinv, hk] at this
  exact this

end field

end C3I

end ArtinPrimitiveRoots

end
end

section
section
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

/-- `γ_j(P) = (N P)^{-1/2} g(χ^j, ψ)`. -/
lemma gaussPhase_eq (g : AllowedGen ι 𝔪) {j : ℕ} (hj : j ≠ 0) :
    gaussPhase g j v.asIdeal =
      ((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ)⁻¹ *
        gaussSum (chi ι h hω ^ j) (psi g h) := by
  unfold gaussPhase
  congr 1
  rw [finsum_eq_sum_of_fintype, gaussSum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [residueSymbol_v, chi_mk_quotLift h hω, MulChar.pow_apply' _ hj, psi_apply]

end field

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3I_Loc: generators of prime powers and their valuations

* `SixEq 𝔪 x y`: `x = μ⁶ y` for a unit `μ` of `R`; `gen_mul_sixEq`, `gen_top_sixEq`,
  `gen_pow_add`, `gen_pow_mul`.
* `val_gen`: `v(gen(P^j)) = exp(-j)`; `val_unit`; `mul_mem_iff`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

/-- `x = μ⁶ y` for a unit `μ` of `R`. -/
def SixEq (𝔪 : Ideal (𝓞 F)) (x y : SInt 𝔪) : Prop := ∃ μ : (SInt 𝔪)ˣ, x = (μ : SInt 𝔪) ^ 6 * y

lemma SixEq.refl (x : SInt 𝔪) : SixEq 𝔪 x x := ⟨1, by simp⟩

lemma SixEq.trans {x y z : SInt 𝔪} (h1 : SixEq 𝔪 x y) (h2 : SixEq 𝔪 y z) : SixEq 𝔪 x z := by
  obtain ⟨μ, rfl⟩ := h1
  obtain ⟨ν, rfl⟩ := h2
  exact ⟨μ * ν, by rw [Units.val_mul, mul_pow]; ring⟩

lemma SixEq.mul {x y x' y' : SInt 𝔪} (h1 : SixEq 𝔪 x y) (h2 : SixEq 𝔪 x' y') :
    SixEq 𝔪 (x * x') (y * y') := by
  obtain ⟨μ, rfl⟩ := h1
  obtain ⟨ν, rfl⟩ := h2
  exact ⟨μ * ν, by rw [Units.val_mul, mul_pow]; ring⟩

/-- `gen(IJ) = μ⁶ gen(I) gen(J)`. -/
lemma gen_mul_sixEq (g : AllowedGen ι 𝔪) {I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I)
    (hJ : IsExterior 𝔪 J) : SixEq 𝔪 (g.gen (I * J)) (g.gen I * g.gen J) := by
  obtain ⟨ε, hε⟩ := g.gen_mul I J hI hJ
  refine ⟨Set.unitEquivUnitsInteger (placesOf 𝔪) F ε, Subtype.ext ?_⟩
  rw [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_mul, hε, mul_assoc]
  rfl

lemma isExterior_top' : IsExterior 𝔪 (⊤ : Ideal (𝓞 F)) := ⟨top_ne_bot, top_sup_eq _⟩

/-- `gen ⊤` is a sixth power of a unit. -/
lemma gen_top_sixEq (g : AllowedGen ι 𝔪) : SixEq 𝔪 (g.gen ⊤) 1 := by
  obtain ⟨μ, hμ⟩ := C3B.isUnit_gen_top g
  have h := gen_mul_sixEq g (isExterior_top' (𝔪 := 𝔪)) isExterior_top'
  rw [Ideal.top_mul] at h
  obtain ⟨ν, hν⟩ := h
  refine ⟨ν⁻¹, ?_⟩
  rw [mul_one, ← hμ]
  rw [← hμ] at hν
  have h2 : (ν : SInt 𝔪) ^ 6 * μ = 1 := by
    apply mul_left_cancel₀ μ.ne_zero
    linear_combination (-1 : SInt 𝔪) * hν
  calc (μ : SInt 𝔪) = ((ν⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) ^ 6 * ((ν : SInt 𝔪) ^ 6 * μ) := by
        rw [← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
    _ = _ := by rw [h2, mul_one]

section prime

variable (g : AllowedGen ι 𝔪) (h : Good 𝔪 v)
include h

lemma ext_pow (j : ℕ) : IsExterior 𝔪 (v.asIdeal ^ j) := isExterior_pow h.ext j

lemma gen_pow_add (a b : ℕ) :
    SixEq 𝔪 (g.gen (v.asIdeal ^ (a + b))) (g.gen (v.asIdeal ^ a) * g.gen (v.asIdeal ^ b)) := by
  rw [pow_add]; exact gen_mul_sixEq g (ext_pow h a) (ext_pow h b)

lemma gen_pow_zero : SixEq 𝔪 (g.gen (v.asIdeal ^ 0)) 1 := by
  rw [pow_zero, Ideal.one_eq_top]; exact gen_top_sixEq g

/-- `gen(P^j) ~ π^j`. -/
lemma gen_pow_sixEq (j : ℕ) : SixEq 𝔪 (g.gen (v.asIdeal ^ j)) (g.gen v.asIdeal ^ j) := by
  induction j with
  | zero => have := gen_pow_zero g h; simp only [pow_zero] at this ⊢; exact this
  | succ k ih =>
    have := gen_pow_add g h k 1
    rw [pow_one] at this
    exact this.trans (by rw [pow_succ (g.gen v.asIdeal)]; exact ih.mul (SixEq.refl (𝔪 := 𝔪) _))

/-! ### Valuations -/

lemma val_unit (μ : (SInt 𝔪)ˣ) : v.valuation F ((μ : SInt 𝔪) : F) = 1 := by
  have h1 := val_le_one h.notS (μ : SInt 𝔪)
  have h2 := val_le_one h.notS ((μ⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪)
  have h3 : v.valuation F ((μ : SInt 𝔪) : F) * v.valuation F (((μ⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = 1 := by
    rw [← map_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
  exact eq_one_of_one_le_mul_left h1 h2 h3.ge

lemma val_sixEq {x y : SInt 𝔪} (hxy : SixEq 𝔪 x y) :
    v.valuation F (x : F) = v.valuation F (y : F) := by
  obtain ⟨μ, rfl⟩ := hxy
  rw [Subalgebra.coe_mul, Subalgebra.coe_pow, map_mul, map_pow, val_unit h, one_pow, one_mul]

lemma gen_mem (j : ℕ) :
    g.gen (v.asIdeal ^ j) ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  rw [← g.span_gen _ (ext_pow h j)]; exact Ideal.mem_span_singleton_self _

lemma val_pi : v.valuation F (g.gen v.asIdeal : F) = exp (-1 : ℤ) := by
  have hmem := gen_mem g h 1
  rw [pow_one] at hmem
  apply le_antisymm
  · have := val_le_of_mem h.notS 1 (by rw [pow_one]; exact hmem)
    simpa using this
  · obtain ⟨p, hp⟩ := exists_uniformizer (v := v)
    have hpm : algebraMap (𝓞 F) (SInt 𝔪) p ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
      apply Ideal.mem_map_of_mem
      rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F), hp]
      exact exp_lt_exp.2 (by norm_num) |>.trans_eq exp_zero
    rw [← g.span_gen _ h.ext, Ideal.mem_span_singleton'] at hpm
    obtain ⟨r, hr⟩ := hpm
    have := congrArg (fun z : SInt 𝔪 => v.valuation F (z : F)) hr
    simp only [Subalgebra.coe_mul, map_mul, coe_alg, hp] at this
    rw [← this]
    calc v.valuation F (r : F) * v.valuation F (g.gen v.asIdeal : F)
        ≤ 1 * v.valuation F (g.gen v.asIdeal : F) := mul_le_mul_left (val_le_one h.notS r) _
      _ = _ := one_mul _

/-- `v(gen(P^j)) = exp(-j)`. -/
lemma val_gen (j : ℕ) : v.valuation F (g.gen (v.asIdeal ^ j) : F) = exp (-(j : ℤ)) := by
  rw [val_sixEq h (gen_pow_sixEq g h j), Subalgebra.coe_pow, map_pow, val_pi g h, ← exp_nsmul]
  congr 1; simp

/-- `x y ∈ P^(a+j)` iff `y ∈ P^j` when `v(x) = exp(-a)`. -/
lemma mul_mem_iff {x : SInt 𝔪} {a : ℕ} (hx : v.valuation F (x : F) = exp (-(a : ℤ))) (j : ℕ)
    (y : SInt 𝔪) :
    x * y ∈ (v.asIdeal ^ (a + j)).map (algebraMap (𝓞 F) (SInt 𝔪)) ↔
      y ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  rw [mem_map_pow_iff h.notS, mem_map_pow_iff h.notS, Subalgebra.coe_mul, map_mul, hx]
  have e : (exp (-((a + j : ℕ) : ℤ)) : ℤᵐ⁰) = exp (-(a : ℤ)) * exp (-(j : ℤ)) := by
    rw [← exp_add]; congr 1; push_cast; ring
  rw [e]
  constructor
  · intro h1
    have h1' : v.valuation F (y : F) * exp (-(a : ℤ)) ≤ exp (-(j : ℤ)) * exp (-(a : ℤ)) := by
      rw [mul_comm, mul_comm (exp (-(j : ℤ)))]; exact h1
    exact le_of_mul_le_mul_ne h1' exp_ne_zero
  · intro h1
    exact mul_le_mul' le_rfl h1

end prime

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3I_GP: Gauss sums modulo prime powers

For `t ≥ 1`, `A = gen(P^t)`, `r ∈ R`, `G_t(r) = gaussSumAt g (P^t) r`:
* `gsat_eq_zero`: `G_t(r) = 0` if `r ∉ P^(t-1) R`;
* `gsat_eq_fibre`: `G_t(r) = Q^(t-1) ∑_{a ∈ L} χ(a)^t e(r a / A)` if `r ∈ P^(t-1) R`;
* `exists_c`: then `r / A = c / π` with `c ∈ R`, `c ∈ P R ↔ r ∈ P^t R`;
* `lsum_eq`: the `L`-sum is `∑_a χ^t(a) ψ(c a)`; `ram_sum` (`6 ∣ t`), `gauss_shift` (`6 ∤ t`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

lemma normalizedFactors_v_pow (v : HeightOneSpectrum (𝓞 F)) (t : ℕ) :
    normalizedFactors (v.asIdeal ^ t) = Multiset.replicate t v.asIdeal := by
  rw [normalizedFactors_pow, normalizedFactors_v, Multiset.nsmul_singleton]

lemma residueSymbol_pow (t : ℕ) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 (v.asIdeal ^ t) x = sexticResidueSymbol ι 𝔪 v.asIdeal x ^ t := by
  rw [residueSymbol, normalizedFactors_v_pow v t, Multiset.map_replicate,
    Multiset.prod_replicate]

lemma map_pow_anti {a b : ℕ} (hab : a ≤ b) :
    (v.asIdeal ^ b).map (algebraMap (𝓞 F) (SInt 𝔪)) ≤
      (v.asIdeal ^ a).map (algebraMap (𝓞 F) (SInt 𝔪)) :=
  Ideal.map_mono (Ideal.pow_le_pow_right hab)

section gauss

variable (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
include h

lemma sext_congr {x y : SInt 𝔪} (hxy : x - y ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    sexticResidueSymbol ι 𝔪 v.asIdeal x = sexticResidueSymbol ι 𝔪 v.asIdeal y :=
  C3B.sexticResidueSymbol_eq_of_mk_eq ι _ x y (Ideal.Quotient.eq.mpr hxy)

end gauss

section lsum

variable (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
  [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]
include h hω

end lsum

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3I_F: the local Poisson factor `F(P^k, P^t, gen(P^m)⁶)`

Case analysis following (7.15)–(7.17), with `H = gen(P^m)⁶`, `A = gen(P^t)`, `s = gen(P^k)`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

section main

variable (g : AllowedGen ι 𝔪) (h : Good 𝔪 v)
include h

lemma sext_zero_of_mem {q : SInt 𝔪} (hq : q ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    sexticResidueSymbol ι 𝔪 v.asIdeal q = 0 := by
  unfold sexticResidueSymbol
  rw [if_pos (Ideal.Quotient.eq_zero_iff_mem.mpr hq)]

open Classical in
/-- `F(P^k, P^t, H)` as a sum over `R/P^k R`. -/
lemma pf_eq_sum (k t : ℕ) (H : SInt 𝔪) :
    poissonFactor g (v.asIdeal ^ k) (v.asIdeal ^ t) H =
      ∑ᶠ d : SInt 𝔪 ⧸ (v.asIdeal ^ k).map (algebraMap (𝓞 F) (SInt 𝔪)),
        if H - g.gen (v.asIdeal ^ t) * quotLift d ∈ (v.asIdeal ^ k).map (algebraMap (𝓞 F) (SInt 𝔪))
        then sexticResidueSymbol ι 𝔪 v.asIdeal (quotLift d) ^ k *
          gaussSumAt g (v.asIdeal ^ t)
            (((H - g.gen (v.asIdeal ^ t) * quotLift d : SInt 𝔪) : F) /
              (g.gen (v.asIdeal ^ k) : F))
        else 0 := by
  unfold poissonFactor
  refine finsum_congr fun d => ?_
  split_ifs <;> simp only [residueSymbol_pow]

/-- The quotient `(H - A q)/s` when `s ∣ H - A q`. -/
lemma exists_arg (k : ℕ) (x : SInt 𝔪)
    (hx : x ∈ (v.asIdeal ^ k).map (algebraMap (𝓞 F) (SInt 𝔪))) :
    ∃ r : SInt 𝔪, (x : F) / (g.gen (v.asIdeal ^ k) : F) = (r : F) ∧
      ∀ j, (r ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) ↔
        x ∈ (v.asIdeal ^ (k + j)).map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  obtain ⟨r, hr⟩ := (C3B.mem_map_iff g _ (ext_pow h k) x).1 hx
  refine ⟨r, ?_, fun j => ?_⟩
  · rw [hr, Subalgebra.coe_mul, mul_div_cancel_left₀ _ (C3B.gen_ne_zero g _ (ext_pow h k))]
  · rw [hr, mul_mem_iff h (val_gen g h k)]

section fin

variable {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
  [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]
include hω

end fin

end main

end C3I

end ArtinPrimitiveRoots

end
end

section
section
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

theorem norm_gaussSumAt_le (g : AllowedGen ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    (k : F) : ‖gaussSumAt g 𝔞 k‖ ≤ Ideal.absNorm 𝔞 := by
  have := C3M.finite_quot h𝔞
  unfold gaussSumAt
  refine (norm_finsum_le _ 1 fun v => ?_).trans ?_
  · rw [norm_mul]
    exact mul_le_one₀ (norm_residueSymbol_le ι 𝔪 𝔞 _) (norm_nonneg _) (norm_sAddChar_le _ _)
  · rw [mul_one]; exact_mod_cast card_quot_le h𝔞

theorem norm_poissonFactor_le (g : AllowedGen ι 𝔪) {𝔰 𝔄 : Ideal (𝓞 F)} (h𝔰 : IsExterior 𝔪 𝔰)
    (h𝔄 : IsExterior 𝔪 𝔄) (h : SInt 𝔪) :
    ‖poissonFactor g 𝔰 𝔄 h‖ ≤ Ideal.absNorm 𝔰 * Ideal.absNorm 𝔄 := by
  have := C3M.finite_quot h𝔰
  unfold poissonFactor
  refine (norm_finsum_le _ (Ideal.absNorm 𝔄) fun d => ?_).trans ?_
  · split_ifs
    · rw [norm_mul]
      calc _ ≤ 1 * (Ideal.absNorm 𝔄 : ℝ) :=
            mul_le_mul (norm_residueSymbol_le ι 𝔪 𝔰 _) (norm_gaussSumAt_le g h𝔄 _)
              (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    · simp
  · gcongr; exact_mod_cast card_quot_le h𝔰

end ArtinPrimitiveRoots.L2B

end
end

section
section
/-! # L3R_RamF: the Poisson factor at `P ∣ u` ((7.17)–(7.18) for every `J`)

For a good exterior prime `P = v` and any `H ∈ R`:
* `pf_k2`: `F(P^k, P^t, H) = 0` for `k ≥ 2`, `t ≥ 1` (shift `d ↦ d + gen(P^{k-1}) λ` and sum
  over `λ mod P`: the phase sum `∑_λ ψ(c λ)` vanishes for `c ∉ P`);
* `norm_pf_k1`: `‖F(P, P^t, H)‖ ≤ Q^t √Q` for `t ≥ 1`, `H ∈ PR` (the `d`-sum is a Gauss sum of
  modulus `√Q` or `0`);
* `norm_gaussPhase_two`: `‖γ₂(P)‖ = 1`. -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

section ram

variable (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
  [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]
include h hω

/-- `∑_λ e(c λ / π) = 0` for `c ∉ P R`. -/
lemma sum_psi_mul (c : SInt 𝔪) (hc : c ∉ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    ∑ᶠ l : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)),
      sAddChar 𝔪 (((c * quotLift l : SInt 𝔪) : F) / (g.gen v.asIdeal : F)) = 0 := by
  classical
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  rw [finsum_eq_sum_of_fintype]
  have e : ∀ l : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)),
      sAddChar 𝔪 (((c * quotLift l : SInt 𝔪) : F) / (g.gen v.asIdeal : F)) =
        psi g h (l * Ideal.Quotient.mk _ c) := by
    intro l
    rw [← psi_mk g h, map_mul, mk_quotLift, mul_comm]
  simp_rw [e]
  rw [AddChar.sum_mulShift _ (psi_isPrimitive g h),
    if_neg (fun h0 => hc (Ideal.Quotient.eq_zero_iff_mem.mp h0))]
  simp

/-- **`k ≥ 2`**: `F(P^k, P^t, H) = 0` for `t ≥ 1` and every `H`. -/
theorem pf_k2 {k t : ℕ} (hk : 2 ≤ k) (ht : 1 ≤ t) (H : SInt 𝔪) :
    poissonFactor g (v.asIdeal ^ k) (v.asIdeal ^ t) H = 0 := by
  classical
  haveI hfk := finite_quot (𝔪 := 𝔪) h.notS k
  letI := Fintype.ofFinite (SInt 𝔪 ⧸ (v.asIdeal ^ k).map (algebraMap (𝓞 F) (SInt 𝔪)))
  set I := (v.asIdeal ^ k).map (algebraMap (𝓞 F) (SInt 𝔪)) with hI
  set L := SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))
  set A := g.gen (v.asIdeal ^ t) with hAdef
  set s := g.gen (v.asIdeal ^ k) with hsdef
  set w := g.gen (v.asIdeal ^ (k - 1)) with hwdef
  set π := g.gen v.asIdeal with hπdef
  have hextk := ext_pow h k
  have hextt := ext_pow h t
  have hext1 := ext_pow h (k - 1)
  have hA0 : (A : F) ≠ 0 := C3B.gen_ne_zero g _ hextt
  have hs0 : (s : F) ≠ 0 := C3B.gen_ne_zero g _ hextk
  -- `s = ε⁶ w π`
  obtain ⟨ε, hε⟩ := C3M.gen_mul' g hext1 h.ext
  have hPk : v.asIdeal ^ (k - 1) * v.asIdeal = v.asIdeal ^ k := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  rw [hPk] at hε
  set ν : SInt 𝔪 := ((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) with hν
  have hεν : (ε : SInt 𝔪) * ν = 1 := Units.mul_inv ε
  have hπ0 : (π : F) ≠ 0 := C3B.gen_ne_zero g _ h.ext
  have hw0 : (w : F) ≠ 0 := C3B.gen_ne_zero g _ hext1
  -- the summand and its periodicity
  set fT : SInt 𝔪 → ℂ := fun x => if H - A * x ∈ I then
    sexticResidueSymbol ι 𝔪 v.asIdeal x ^ k *
      gaussSumAt g (v.asIdeal ^ t) (((H - A * x : SInt 𝔪) : F) / (s : F)) else 0 with hfT
  have hAk : ∀ z, z ∈ (v.asIdeal ^ (k - 1)).map (algebraMap (𝓞 F) (SInt 𝔪)) → A * z ∈ I := by
    intro z hz
    have h1 : A * z ∈ (v.asIdeal ^ (t + (k - 1))).map (algebraMap (𝓞 F) (SInt 𝔪)) :=
      (mul_mem_iff h (val_gen g h t) (k - 1) z).2 hz
    exact map_pow_anti (by omega) h1
  have hk1 : (v.asIdeal ^ (k - 1)).map (algebraMap (𝓞 F) (SInt 𝔪)) ≤
      v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    have := map_pow_anti (𝔪 := 𝔪) (v := v) (a := 1) (b := k - 1) (by omega)
    rwa [pow_one] at this
  have hIk1 : I ≤ (v.asIdeal ^ (k - 1)).map (algebraMap (𝓞 F) (SInt 𝔪)) := map_pow_anti (by omega)
  have hper : ∀ x z : SInt 𝔪, z ∈ I → fT (x + z) = fT x := by
    intro x z hz
    obtain ⟨r, hr⟩ := (C3B.mem_map_iff g _ hextk z).1 hz
    have hcond : (H - A * (x + z) ∈ I) ↔ (H - A * x ∈ I) := by
      have e : H - A * (x + z) = (H - A * x) - A * z := by ring
      rw [e]
      have hAz : A * z ∈ I := Ideal.mul_mem_left _ _ hz
      exact ⟨fun hh => by simpa using add_mem hh hAz, fun hh => sub_mem hh hAz⟩
    simp only [hfT]
    by_cases hc : H - A * x ∈ I
    · rw [if_pos (hcond.2 hc), if_pos hc]
      have hsx : sexticResidueSymbol ι 𝔪 v.asIdeal (x + z) = sexticResidueSymbol ι 𝔪 v.asIdeal x :=
        sext_congr h (by rw [add_sub_cancel_left]; exact hk1 (hIk1 hz))
      rw [hsx]
      congr 1
      have e : ((H - A * (x + z) : SInt 𝔪) : F) / (s : F) =
          ((H - A * x : SInt 𝔪) : F) / (s : F) + ((-(A * r) : SInt 𝔪) : F) := by
        simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_neg, hr]
        field_simp
        ring
      rw [e, C3B.gaussSumAt_add_mem g _ hextt _ _
        (neg_mem (Ideal.mul_mem_right _ _ (gen_mem g h t)))]
    · rw [if_neg (fun hh => hc (hcond.1 hh)), if_neg hc]
  -- translation invariance
  have hshift : ∀ y : SInt 𝔪,
      ∑ d : SInt 𝔪 ⧸ I, fT (quotLift d + y) = ∑ d : SInt 𝔪 ⧸ I, fT (quotLift d) := by
    intro y
    rw [← Equiv.sum_comp (Equiv.addRight (Ideal.Quotient.mk I y)) (fun d => fT (quotLift d))]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [Equiv.coe_addRight]
    have hδ : quotLift (d + Ideal.Quotient.mk I y) - (quotLift d + y) ∈ I := by
      rw [← Ideal.Quotient.eq, map_add, mk_quotLift, mk_quotLift]
    rw [show quotLift (d + Ideal.Quotient.mk I y) = (quotLift d + y) +
      (quotLift (d + Ideal.Quotient.mk I y) - (quotLift d + y)) by ring, hper _ _ hδ]
  -- the inner sum vanishes
  haveI hft := finite_quot (𝔪 := 𝔪) h.notS t
  letI := Fintype.ofFinite (SInt 𝔪 ⧸ (v.asIdeal ^ t).map (algebraMap (𝓞 F) (SInt 𝔪)))
  have hin : ∀ x : SInt 𝔪, ∑ l : L, fT (x + w * quotLift l) = 0 := by
    intro x
    have hwl : ∀ l : L, A * (w * quotLift l) ∈ I := fun l =>
      hAk _ (Ideal.mul_mem_right _ _ (gen_mem g h (k - 1)))
    by_cases hc : H - A * x ∈ I
    · obtain ⟨r, hr, -⟩ := exists_arg g h k _ hc
      have hterm : ∀ l : L, fT (x + w * quotLift l) =
          sexticResidueSymbol ι 𝔪 v.asIdeal x ^ k *
            ∑ y : SInt 𝔪 ⧸ (v.asIdeal ^ t).map (algebraMap (𝓞 F) (SInt 𝔪)),
              residueSymbol ι 𝔪 (v.asIdeal ^ t) (quotLift y) *
                sAddChar 𝔪 (((r * quotLift y : SInt 𝔪) : F) / (A : F)) *
                sAddChar 𝔪 ((((-ν ^ 6 * quotLift y) * quotLift l : SInt 𝔪) : F) / (π : F)) := by
        intro l
        have hc' : H - A * (x + w * quotLift l) ∈ I := by
          have e : H - A * (x + w * quotLift l) = (H - A * x) - A * (w * quotLift l) := by ring
          rw [e]; exact sub_mem hc (hwl l)
        simp only [hfT]
        rw [if_pos hc']
        have hsx : sexticResidueSymbol ι 𝔪 v.asIdeal (x + w * quotLift l) =
            sexticResidueSymbol ι 𝔪 v.asIdeal x :=
          sext_congr h (by
            rw [add_sub_cancel_left]
            exact hk1 (Ideal.mul_mem_right _ _ (gen_mem g h (k - 1))))
        rw [hsx]
        congr 1
        unfold gaussSumAt
        rw [finsum_eq_sum_of_fintype]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [mul_assoc]
        congr 1
        have harg : ((H - A * (x + w * quotLift l) : SInt 𝔪) : F) / (s : F) *
            (quotLift y : F) / (A : F) =
            ((r * quotLift y : SInt 𝔪) : F) / (A : F) +
              ((((-ν ^ 6 * quotLift y) * quotLift l : SInt 𝔪) : F) / (π : F)) := by
          have hrF : ((H - A * x : SInt 𝔪) : F) = (r : F) * (s : F) := by
            rw [← hr]; exact (div_mul_cancel₀ _ hs0).symm
          have hsF : (s : F) = ((ε : SInt 𝔪) : F) ^ 6 * (w : F) * (π : F) := by
            rw [hsdef, hε]; simp only [Subalgebra.coe_mul, Subalgebra.coe_pow]; rfl
          have hενF : ((ε : SInt 𝔪) : F) * (ν : F) = 1 := by
            have := congrArg (fun z : SInt 𝔪 => (z : F)) hεν
            simpa only [Subalgebra.coe_mul, Subalgebra.coe_one] using this
          have hε0 : ((ε : SInt 𝔪) : F) ≠ 0 := by
            intro h0; rw [h0, zero_mul] at hενF; exact zero_ne_one hενF
          simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_add,
            Subalgebra.coe_neg, Subalgebra.coe_pow] at hrF ⊢
          have e1 : (H : F) - (A : F) * ((x : F) + (w : F) * (quotLift l : F)) =
              (r : F) * (s : F) - (A : F) * (w : F) * (quotLift l : F) := by
            linear_combination hrF
          rw [e1, hsF]
          have hν6 : (ν : F) ^ 6 = (((ε : SInt 𝔪) : F) ^ 6)⁻¹ := by
            rw [← inv_pow]; congr 1; exact eq_inv_of_mul_eq_one_right hενF
          rw [hν6]
          field_simp
          ring
        rw [harg, sAddChar_add (hasWit_div_gen g _ hextt _) (hasWit_div_gen g _ h.ext _)]
      rw [Finset.sum_congr rfl fun l _ => hterm l, ← Finset.mul_sum, Finset.sum_comm]
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun y _ => ?_)
      rw [← Finset.mul_sum]
      by_cases hy : quotLift y ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))
      · rw [residueSymbol_pow, sext_zero_of_mem h hy, zero_pow (by omega), zero_mul, zero_mul]
      · have hcy : -ν ^ 6 * quotLift y ∉ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
          intro hm
          apply hy
          have := Ideal.mul_mem_left _ (-((ε : SInt 𝔪) ^ 6)) hm
          rwa [show -((ε : SInt 𝔪) ^ 6) * (-ν ^ 6 * quotLift y) = ((ε : SInt 𝔪) * ν) ^ 6 *
            quotLift y by ring, hεν, one_pow, one_mul] at this
        have := sum_psi_mul g h hω _ hcy
        rw [finsum_eq_sum_of_fintype] at this
        rw [this, mul_zero]
    · refine Finset.sum_eq_zero fun l _ => ?_
      simp only [hfT]
      rw [if_neg]
      intro hh
      apply hc
      have := add_mem hh (hwl l)
      rwa [show H - A * (x + w * quotLift l) + A * (w * quotLift l) = H - A * x by ring] at this
  -- assemble
  rw [pf_eq_sum g h, finsum_eq_sum_of_fintype]
  have hQ : (Fintype.card L : ℂ) ≠ 0 := by
    rw [card_L h hω]; exact_mod_cast (absNorm_pos v).ne'
  have key : (Fintype.card L : ℂ) * ∑ d : SInt 𝔪 ⧸ I, fT (quotLift d) = 0 := by
    rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    calc ∑ _l : L, ∑ d : SInt 𝔪 ⧸ I, fT (quotLift d)
        = ∑ l : L, ∑ d : SInt 𝔪 ⧸ I, fT (quotLift d + w * quotLift l) :=
          Finset.sum_congr rfl fun l _ => (hshift _).symm
      _ = ∑ d : SInt 𝔪 ⧸ I, ∑ l : L, fT (quotLift d + w * quotLift l) := Finset.sum_comm
      _ = 0 := Finset.sum_eq_zero fun d _ => hin _
  exact (mul_eq_zero.1 key).resolve_left hQ


/-- `‖g(χ^j, ψ)‖ = √Q` for `j = 1, 2`. -/
lemma norm_gs {j k : ℕ} (hj : ¬ 6 ∣ j) (hjk : (j + k) % 6 = 0) :
    ‖gaussSum (chi ι h hω ^ j) (psi g h)‖ = Real.sqrt (Ideal.absNorm v.asIdeal) := by
  have h1 := gs_mul_gs h hω g hj hjk
  rw [← star_gs h hω g j k hjk] at h1
  have h2 : ‖gaussSum (chi ι h hω ^ j) (psi g h)‖ ^ 2 = (Ideal.absNorm v.asIdeal : ℝ) := by
    have := congrArg Complex.re h1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at this
    exact_mod_cast this
  rw [← h2, Real.sqrt_sq (norm_nonneg _)]

/-- `‖γ₂(P)‖ = 1`. -/
lemma norm_gaussPhase_two : ‖gaussPhase g 2 v.asIdeal‖ = 1 := by
  rw [gaussPhase_eq h hω g (by norm_num : (2 : ℕ) ≠ 0), norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), norm_gs g h hω (j := 2) (k := 4) (by norm_num)
    (by norm_num)]
  have : 0 < Real.sqrt (Ideal.absNorm v.asIdeal) :=
    Real.sqrt_pos.2 (by exact_mod_cast absNorm_pos v)
  field_simp

/-- The twisted Gauss sum `∑_d χ(d) e(−d y/π)` has modulus `≤ √Q`. -/
lemma norm_twisted_le (y : SInt 𝔪) :
    ‖∑ d : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)),
      sexticResidueSymbol ι 𝔪 v.asIdeal (quotLift d) *
        sAddChar 𝔪 (((-y * quotLift d : SInt 𝔪) : F) / (g.gen v.asIdeal : F))‖ ≤
      Real.sqrt (Ideal.absNorm v.asIdeal) := by
  classical
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  set b := Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) (-y)
  have e : ∀ d : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)),
      sexticResidueSymbol ι 𝔪 v.asIdeal (quotLift d) *
        sAddChar 𝔪 (((-y * quotLift d : SInt 𝔪) : F) / (g.gen v.asIdeal : F)) =
      chi ι h hω d * (psi g h).mulShift b d := by
    intro d
    rw [chi_mk_quotLift h hω, AddChar.mulShift_apply, ← psi_mk g h, map_mul, mk_quotLift]
  simp_rw [e]
  change ‖gaussSum (chi ι h hω) ((psi g h).mulShift b)‖ ≤ _
  by_cases hb : b = 0
  · have hz : gaussSum (chi ι h hω) ((psi g h).mulShift b) = 0 := by
      rw [hb, AddChar.mulShift_zero]
      unfold gaussSum
      simp only [AddChar.one_apply, mul_one]
      have hχ : chi ι h hω ≠ 1 := by
        have := chi_pow_ne_one (ι := ι) h hω (j := 1) (by norm_num); rwa [pow_one] at this
      exact MulChar.sum_eq_zero_of_ne_one hχ
    rw [hz, norm_zero]; exact Real.sqrt_nonneg _
  · have hu := gaussSum_mulShift (chi ι h hω) (psi g h) (Units.mk0 b hb)
    have h6 : (chi ι h hω (Units.mk0 b hb : _)) ^ 6 = 1 := by
      rw [← MulChar.pow_apply' _ (by norm_num), chi_pow_six h hω, MulChar.one_apply
        (Units.isUnit _)]
    have hn : ‖chi ι h hω (Units.mk0 b hb : _)‖ = 1 :=
      Complex.norm_eq_one_of_pow_eq_one h6 (by norm_num)
    have := congrArg norm hu
    rw [norm_mul, hn, one_mul] at this
    simp only [Units.val_mk0] at this
    rw [this]
    have := norm_gs g h hω (j := 1) (k := 5) (by norm_num) (by norm_num)
    rw [pow_one] at this
    rw [this]

/-- **`k = 1`**: `‖F(P, P^t, H)‖ ≤ Q^t √Q` for `t ≥ 1`, `H ∈ PR`. -/
theorem norm_pf_k1 {t : ℕ} (ht : 1 ≤ t) {H : SInt 𝔪}
    (hH : H ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    ‖poissonFactor g (v.asIdeal ^ 1) (v.asIdeal ^ t) H‖ ≤
      (Ideal.absNorm v.asIdeal : ℝ) ^ t * Real.sqrt (Ideal.absNorm v.asIdeal) := by
  classical
  haveI hft := finite_quot (𝔪 := 𝔪) h.notS t
  letI := Fintype.ofFinite (SInt 𝔪 ⧸ (v.asIdeal ^ t).map (algebraMap (𝓞 F) (SInt 𝔪)))
  rw [pow_one]
  set A := g.gen (v.asIdeal ^ t)
  set π := g.gen v.asIdeal
  have hextt := ext_pow h t
  have hA0 : (A : F) ≠ 0 := C3B.gen_ne_zero g _ hextt
  have hπ0 : (π : F) ≠ 0 := C3B.gen_ne_zero g _ h.ext
  obtain ⟨h1, hh1⟩ := (C3B.mem_map_iff g _ h.ext H).1 hH
  have hAm : A ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    have := map_pow_anti (𝔪 := 𝔪) (v := v) ht (gen_mem g h t); rwa [pow_one] at this
  obtain ⟨a1, ha1⟩ := (C3B.mem_map_iff g _ h.ext A).1 hAm
  unfold poissonFactor
  rw [finsum_eq_sum_of_fintype]
  have hterm : ∀ d : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)),
      (if H - A * quotLift d ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) then
        residueSymbol ι 𝔪 v.asIdeal (quotLift d) *
          gaussSumAt g (v.asIdeal ^ t) (((H - A * quotLift d : SInt 𝔪) : F) / (π : F)) else 0) =
      ∑ y : SInt 𝔪 ⧸ (v.asIdeal ^ t).map (algebraMap (𝓞 F) (SInt 𝔪)),
        residueSymbol ι 𝔪 (v.asIdeal ^ t) (quotLift y) *
          sAddChar 𝔪 (((h1 * quotLift y : SInt 𝔪) : F) / (A : F)) *
          (sexticResidueSymbol ι 𝔪 v.asIdeal (quotLift d) *
            sAddChar 𝔪 (((-quotLift y * quotLift d : SInt 𝔪) : F) / (π : F))) := by
    intro d
    rw [if_pos (sub_mem hH (Ideal.mul_mem_right _ _ hAm)), residueSymbol_v, gaussSumAt,
      finsum_eq_sum_of_fintype, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have harg : ((H - A * quotLift d : SInt 𝔪) : F) / (π : F) * (quotLift y : F) / (A : F) =
        ((h1 * quotLift y : SInt 𝔪) : F) / (A : F) +
          ((-quotLift y * quotLift d : SInt 𝔪) : F) / (π : F) := by
      have e1 : (H : F) = (π : F) * (h1 : F) := by
        rw [hh1]; simp only [Subalgebra.coe_mul]; rfl
      have e2 : (A : F) = (π : F) * (a1 : F) := by
        rw [ha1]; simp only [Subalgebra.coe_mul]; rfl
      have ha0 : (a1 : F) ≠ 0 := by
        intro h0; rw [h0, mul_zero] at e2; exact hA0 e2
      simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_neg]
      rw [e1, e2]
      field_simp
      ring
    rw [harg, sAddChar_add (hasWit_div_gen g _ hextt _) (hasWit_div_gen g _ h.ext _)]
    ring
  rw [Finset.sum_congr rfl fun d _ => hterm d, Finset.sum_comm]
  refine (norm_sum_le _ _).trans ?_
  have hcard : (Finset.univ : Finset (SInt 𝔪 ⧸ (v.asIdeal ^ t).map (algebraMap (𝓞 F) (SInt 𝔪)))).card
      = Ideal.absNorm v.asIdeal ^ t := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, natCard_quot h.notS t]
  calc ∑ y : SInt 𝔪 ⧸ (v.asIdeal ^ t).map (algebraMap (𝓞 F) (SInt 𝔪)),
        ‖∑ d : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)),
          residueSymbol ι 𝔪 (v.asIdeal ^ t) (quotLift y) *
            sAddChar 𝔪 (((h1 * quotLift y : SInt 𝔪) : F) / (A : F)) *
            (sexticResidueSymbol ι 𝔪 v.asIdeal (quotLift d) *
              sAddChar 𝔪 (((-quotLift y * quotLift d : SInt 𝔪) : F) / (π : F)))‖
      ≤ ∑ _y : SInt 𝔪 ⧸ (v.asIdeal ^ t).map (algebraMap (𝓞 F) (SInt 𝔪)),
          Real.sqrt (Ideal.absNorm v.asIdeal) := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [← Finset.mul_sum, norm_mul, norm_mul]
        have b1 := L2B.norm_residueSymbol_le ι 𝔪 (v.asIdeal ^ t) (quotLift y)
        have b2 := L2B.norm_sAddChar_le 𝔪 (((h1 * quotLift y : SInt 𝔪) : F) / (A : F))
        have b3 := norm_twisted_le g h hω (quotLift y)
        calc ‖residueSymbol ι 𝔪 (v.asIdeal ^ t) (quotLift y)‖ *
              ‖sAddChar 𝔪 (((h1 * quotLift y : SInt 𝔪) : F) / (A : F))‖ * ‖_‖
            ≤ 1 * 1 * Real.sqrt (Ideal.absNorm v.asIdeal) := by gcongr
          _ = _ := by ring
    _ = (Ideal.absNorm v.asIdeal : ℝ) ^ t * Real.sqrt (Ideal.absNorm v.asIdeal) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]; push_cast; ring

end ram

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
/-! # C3I_Cut: the cutoff — exterior primes of `ℚ(μ_n)`, `12 ∣ n`, are good

`N₀ = max(3^[F:ℚ], N 𝔇)`: an exterior prime has norm `> N₀`, so it lies over neither `2` nor `3`
(`12 ∣ N P − 1`) and does not divide the different. -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F]

/-- In `ℚ(μ_n)` with `12 ∣ n`, a prime of norm `> 3^[F:ℚ]` has `12 ∣ N P − 1`. -/
theorem twelve_dvd_absNorm_sub_one (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    [IsCyclotomicExtension {n} ℚ F] (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hQ : 3 ^ Module.finrank ℤ (𝓞 F) < Ideal.absNorm P) : 12 ∣ Ideal.absNorm P - 1 := by
  have : P.IsMaximal := hP.isMaximal hP0
  let _ := Ideal.Quotient.field P
  have : Finite (𝓞 F ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  let _ : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  set Q := Ideal.absNorm P
  have hd : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
  have h23 : 2 ^ Module.finrank ℤ (𝓞 F) ≤ 3 ^ Module.finrank ℤ (𝓞 F) :=
    Nat.pow_le_pow_left (by norm_num) _
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
  have hQ1 : Q ≠ 1 := by
    have : 3 ≤ 3 ^ Module.finrank ℤ (𝓞 F) := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hd
    omega
  have hωb : IsPrimitiveRoot (Ideal.Quotient.mk P hζ12.toInteger) 12 :=
    hω.idealQuotient_mk hQ1 hcop
  have h1 : Ideal.Quotient.mk P hζ12.toInteger ^ (Q - 1) = 1 := by
    rw [show Q = Fintype.card (𝓞 F ⧸ P) from (C3B.card_quot P hP0).symm]
    exact FiniteField.pow_card_sub_one_eq_one _ (hωb.ne_zero (by norm_num))
  exact (hωb.pow_eq_one_iff_dvd _).mp h1

/-- A primitive sixth root of unity in `𝓞 F`. -/
theorem exists_prim_six (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) [IsCyclotomicExtension {n} ℚ F] :
    ∃ ω : 𝓞 F, IsPrimitiveRoot ω 6 := by
  have : NeZero n := ⟨hn0.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  have h6 : 6 ∣ n := Nat.dvd_trans (by norm_num) hn
  have hζ6 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ (n / 6)) 6 :=
    hζ.pow hn0 (Nat.div_mul_cancel h6).symm
  exact ⟨hζ6.toInteger, hζ6.toInteger_isPrimitiveRoot⟩

/-- The cutoff. -/
noncomputable def cutN (F : Type*) [Field F] [NumberField F] : ℕ :=
  max (3 ^ Module.finrank ℤ (𝓞 F)) (Ideal.absNorm (differentIdeal ℤ (𝓞 F)))

/-- Exterior primes are good once `N₀ ≥ cutN F`. -/
theorem good_of_exterior (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) [IsCyclotomicExtension {n} ℚ F]
    {N₀ : ℕ} (hN₀ : cutN F ≤ N₀) {𝔪 : Ideal (𝓞 F)} (hsm : SmallPrimesDvd N₀ 𝔪)
    {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hext : IsExterior 𝔪 P) :
    Good 𝔪 (⟨P, hP, hext.1⟩ : HeightOneSpectrum (𝓞 F)) := by
  have hbig : N₀ < Ideal.absNorm P := by
    by_contra hcon
    apply hP.ne_top
    rw [eq_top_iff, ← hext.2]
    exact sup_le le_rfl (hsm P hP hext.1 (by omega))
  have h1 : 3 ^ Module.finrank ℤ (𝓞 F) ≤ cutN F := le_max_left _ _
  have h2 : Ideal.absNorm (differentIdeal ℤ (𝓞 F)) ≤ cutN F := le_max_right _ _
  refine ⟨hext.2, twelve_dvd_absNorm_sub_one n hn0 hn P hP hext.1 (by omega), ?_⟩
  intro hD
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hD
  have hD0 : Ideal.absNorm (differentIdeal ℤ (𝓞 F)) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact differentIdeal_ne_bot
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hD0) hdvd
  change Ideal.absNorm P ≤ _ at this
  omega

end C3I

open NumberField

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3R_CoeffP: the arithmetic input `CoeffU` is true, from the published cuts

As `L3R_Coeff`, with CutF, CutHD and CutG6 taken from their published (Proved) statements
instead of the local `chk_` copies.

(i) from C3B's `coeff_top`; (ii) from `coeff_mul_u`; (iii) from `coeff_unram` and C3B's
`coeffOne_local` with the proved cuts CutF, CutHD, CutG6; (iv) from `pf_ram_t0`, `pf_k2`,
`norm_pf_k1`, `‖γ₂(P)‖ = 1` and `‖ϑ(P)‖ ≤ 1`. -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain

namespace ArtinPrimitiveRoots

namespace L3R

open C3M

variable {F : Type*} [Field F] [NumberField F]

theorem coeffU_pub (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) : CoeffU F ι := by
  classical
  obtain ⟨N₁, hN₁⟩ := hypChiAll n hn0 hn ι
  obtain ⟨N₂, hN₂⟩ := exists_cutoff_poissonFactor_prime_pow_eq_poissonLocal n hn0 hn F ι
  obtain ⟨N₃, hN₃⟩ :=
    exists_cutoff_gaussPhase_mul_gaussPhase_mul_conj_gaussLambda_mul_conj_gaussG_eq_neg_one
      n hn0 hn F ι
  obtain ⟨N₄, hN₄⟩ := exists_cutoff_conj_gaussG_pow_six_eq_one n hn0 hn F ι
  obtain ⟨ω, hω⟩ := C3I.exists_prim_six (F := F) n hn0 hn
  have hn3 : 3 ∣ n := (by norm_num : 3 ∣ 12).trans hn
  set N₀ := max (max (max N₁ N₂) (max N₃ N₄)) (C3I.cutN F) with hN₀
  refine ⟨N₀, fun 𝔪 h𝔪 hS χ g r => ?_⟩
  have hSn : ∀ N, N ≤ N₀ → SmallPrimesDvd N 𝔪 := fun N hN => C3B.smallPrimesDvd_mono hN hS
  have hχ : HypChi ι 𝔪 := hN₁ 𝔪 h𝔪 (hSn _ (by omega))
  have hF := hN₂ 𝔪 h𝔪 (hSn _ (by omega)) g
  have hHD := hN₃ 𝔪 h𝔪 (hSn _ (by omega)) g
  have hG6 := hN₄ 𝔪 h𝔪 (hSn _ (by omega)) g
  set u := freqElt g r with hu
  set 𝔲 := r.1.1 with h𝔲
  have h𝔲e : IsExterior 𝔪 𝔲 := r.1.2.1
  have hrep : ∃ ε : (SInt 𝔪)ˣ, r.2.rep = (ε : SInt 𝔪) := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ := hrep
  have hu' : u = (ε : SInt 𝔪) * g.gen 𝔲 := by rw [hu, freqElt, hε]
  -- facts at a prime
  have hgood : ∀ P : Ideal (𝓞 F), ∀ hP : P.IsPrime, ∀ hPe : IsExterior 𝔪 P,
      C3I.Good 𝔪 (⟨P, hP, hPe.1⟩ : HeightOneSpectrum (𝓞 F)) := fun P hP hPe =>
    C3I.good_of_exterior n hn0 hn (by omega) hS hP hPe
  have hbig : ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P →
      3 ^ Module.finrank ℤ (𝓞 F) < Ideal.absNorm P := by
    intro P hP hPe
    by_contra hc
    apply hP.ne_top
    rw [eq_top_iff, ← hPe.2]
    exact sup_le le_rfl (hS P hP hPe.1 (le_trans (not_lt.mp hc)
      (le_trans (le_max_left _ _) (le_max_right _ _))))
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (i)
    exact C3B.coeff_top g χ _
  · -- (ii)
    intro P hP hPe e₀ l k m _ 𝔠 𝔫 𝔰 𝔯 h𝔠 _ h𝔫 h𝔰 h𝔯 h𝔠P h𝔫P h𝔰P h𝔯P
    exact coeff_mul_u u (hypAdd 𝔪) hχ χ g hP hPe e₀ l k m h𝔠 h𝔫 h𝔰 h𝔯 h𝔠P h𝔫P h𝔰P h𝔯P
  · -- (iii)
    intro P hP hPe hPu
    have hcop : IsCoprime 𝔲 P := by
      have := isCoprime_pow_of_not_le hP hPe.1 hPu 1
      rw [pow_one] at this; exact this.symm
    have hucop : IsCoprime (Ideal.span {u}) (P.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
      rw [hu']; exact cop_mul (isCoprime_unit ε _) (cop_gen g h𝔲e hcop)
    refine ⟨residueSymbol_pow_six hχ hPe hucop, fun e₀ l k m he => ?_⟩
    rw [coeff_unram hχ g χ u hP hPe hucop e₀ l k m,
      C3B.coeffOne_local g χ P hP hPe.1 e₀ l k m he (hF P hP hPe e₀ l k m he) (hHD P hP hPe)
        (hG6 P hP hPe)]
    rfl
  · -- (iv)
    intro P hP hPe hPu
    set v : HeightOneSpectrum (𝓞 F) := ⟨P, hP, hPe.1⟩ with hv
    have hg := hgood P hP hPe
    haveI := C3I.finite_L hg
    letI := Fintype.ofFinite (SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)))
    have huP : u ∈ P.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
      have h1 : g.gen 𝔲 ∈ 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
        rw [← g.span_gen 𝔲 h𝔲e]; exact Ideal.mem_span_singleton_self _
      rw [hu']
      exact Ideal.mul_mem_left _ _ (Ideal.map_mono hPu h1)
    have hHP : ∀ m : ℕ, u * g.gen (P ^ m) ^ 6 ∈ P.map (algebraMap (𝓞 F) (SInt 𝔪)) := fun m =>
      Ideal.mul_mem_right _ _ huP
    have hext : ∀ j : ℕ, IsExterior 𝔪 (P ^ j) := C3B.isExterior_pow hPe
    have hpow : ∀ e₀ l : ℕ, P ^ e₀ * (P ^ l) ^ 3 = P ^ (e₀ + 3 * l) := fun e₀ l => by
      rw [← pow_mul, ← pow_add, mul_comm l 3]
    have hzero : ∀ e₀ l k m : ℕ, 1 ≤ k → e₀ + 3 * l = 0 →
        poissonFactor g (P ^ k) (P ^ e₀ * (P ^ l) ^ 3) (u * g.gen (P ^ m) ^ 6) = 0 := by
      intro e₀ l k m hk ht
      rw [hpow, ht]
      exact pf_ram_t0 hχ g hP hPe hk (hHP m)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [residueSymbol_prime hP hPe.1]
      unfold sexticResidueSymbol
      rw [if_pos (Ideal.Quotient.eq_zero_iff_mem.mpr huP)]
    · intro k m
      unfold C3A.freqCoeff
      by_cases hk : k = 0
      · subst hk
        rw [if_pos rfl]
        simp only [pow_zero, Ideal.one_eq_top]
        exact C3B.coeff_top g χ _
      · rw [if_neg hk, hzero 0 0 k m (by omega) (by norm_num), mul_zero]
    · intro e₀ l k m hk
      unfold C3A.freqCoeff
      by_cases ht : e₀ + 3 * l = 0
      · rw [hzero e₀ l k m (by omega) ht, mul_zero]
      · rw [hpow]
        have := C3I.pf_k2 (v := v) g hg hω hk (by omega : 1 ≤ e₀ + 3 * l) (u * g.gen (P ^ m) ^ 6)
        rw [this, mul_zero]
    · intro e₀ l k m he
      unfold C3A.freqCoeff
      have hQ1 : (1 : ℝ) ≤ (Ideal.absNorm P : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hPe.1)
      have hs0 : 0 ≤ Real.sqrt (Ideal.absNorm P : ℝ) := Real.sqrt_nonneg _
      -- `‖γ₂(P^{e₀})‖ ≤ 1`
      have hγ : ‖gaussPhase g 2 (P ^ e₀)‖ ≤ 1 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he with rfl | rfl
        · rw [pow_zero, Ideal.one_eq_top, C3B.gaussPhase_top, norm_one]
        · rw [pow_one]; exact (C3I.norm_gaussPhase_two (v := v) g hg hω).le
      -- `‖ϑ(P)‖ ≤ 1`
      have hΛ : ‖gaussLambda ι P‖ = 1 := by
        have h6 := C3B.gaussLambda_prime_pow_six (ι := ι) hP hPe.1
        have hj := T12C_norm_jacobiPhaseSix n hn0 hn3 F ι P hP hPe.1 (hbig P hP hPe)
        have : ‖gaussLambda ι P‖ ^ 6 = 1 := by rw [← norm_pow, h6, hj]
        exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp this
      have hG : ‖gaussG g P‖ = 1 := by
        have h6 := hG6 P hP hPe
        have : ‖starRingEnd ℂ (gaussG g P)‖ = 1 :=
          Complex.norm_eq_one_of_pow_eq_one h6 (by norm_num)
        rwa [Complex.norm_conj] at this
      have hϑ1 : ‖χ.thetaChar g P‖ ≤ 1 := by
        unfold HeckeChar.thetaChar
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj, hΛ, hG, one_mul, one_mul]
        exact T12B.norm_le_one h𝔪 χ P
      have hϑ : ‖χ.thetaChar g (P ^ e₀ * (P ^ l) ^ 3)‖ ≤ 1 := by
        rw [hpow, C3B.thetaChar_prime_pow g χ hP hPe.1, norm_pow]
        exact pow_le_one₀ (norm_nonneg _) hϑ1
      -- the Poisson factor
      have hpf : ‖poissonFactor g (P ^ k) (P ^ e₀ * (P ^ l) ^ 3) (u * g.gen (P ^ m) ^ 6)‖ ≤
          (Ideal.absNorm P : ℝ) ^ (e₀ + 3 * l) * Real.sqrt (Ideal.absNorm P) ^ k := by
        by_cases hk2 : 2 ≤ k
        · by_cases ht : e₀ + 3 * l = 0
          · rw [hzero e₀ l k m (by omega) ht, norm_zero]; positivity
          · rw [hpow, C3I.pf_k2 (v := v) g hg hω hk2 (by omega) _, norm_zero]; positivity
        · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
          · refine (L2B.norm_poissonFactor_le g (hext 0) (C3B.isExterior_mul (hext e₀)
              (C3B.isExterior_pow (hext l) 3)) _).trans ?_
            rw [hpow, pow_zero, Ideal.one_eq_top, Ideal.absNorm_top, map_pow]
            push_cast
            rw [one_mul, pow_zero, mul_one]
          · by_cases ht : e₀ + 3 * l = 0
            · rw [hzero e₀ l 1 m le_rfl ht, norm_zero]; positivity
            · rw [hpow]
              have := C3I.norm_pf_k1 (v := v) g hg hω (by omega : 1 ≤ e₀ + 3 * l) (hHP m)
              simpa only [pow_one] using this
      rw [norm_mul, norm_mul]
      calc ‖gaussPhase g 2 (P ^ e₀)‖ * ‖χ.thetaChar g (P ^ e₀ * (P ^ l) ^ 3)‖ *
            ‖poissonFactor g (P ^ k) (P ^ e₀ * (P ^ l) ^ 3) (u * g.gen (P ^ m) ^ 6)‖
          ≤ 1 * 1 * ((Ideal.absNorm P : ℝ) ^ (e₀ + 3 * l) * Real.sqrt (Ideal.absNorm P) ^ k) := by
            gcongr
        _ = _ := by ring

end L3R

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3R_DevC: the arithmetic half of RowFactorization, statement verbatim

`exists_cutoff_freqCoeff_freqElt_eq_one_and_eq_mul` is `L3R.CoeffU F ι` with the coefficient
`C3A.freqCoeff` and the table `C3A.principalLocalCoeff` unfolded to the published definitions.
Proved by `L3R.coeffU_pub` (which uses the published CutF, CutHD and CutG6). -/

open NumberField

namespace ArtinPrimitiveRoots

theorem exists_cutoff_freqCoeff_freqElt_eq_one_and_eq_mul (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (r : FreqClass 𝔪),
        let a : Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ := fun 𝔠 𝔫 𝔰 𝔯 =>
          gaussPhase g 2 𝔠 * χ.thetaChar g (𝔠 * 𝔫 ^ 3) *
            poissonFactor g 𝔰 (𝔠 * 𝔫 ^ 3) (freqElt g r * g.gen 𝔯 ^ 6)
        a ⊤ ⊤ ⊤ ⊤ = 1 ∧
        (∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → ∀ e₀ l k m : ℕ, e₀ ≤ 1 →
          ∀ 𝔠 𝔫 𝔰 𝔯 : Ideal (𝓞 F), IsExterior 𝔪 𝔠 → Squarefree 𝔠 → IsExterior 𝔪 𝔫 →
            IsExterior 𝔪 𝔰 → IsExterior 𝔪 𝔯 → ¬ 𝔠 ≤ P → ¬ 𝔫 ≤ P → ¬ 𝔰 ≤ P → ¬ 𝔯 ≤ P →
            a (P ^ e₀ * 𝔠) (P ^ l * 𝔫) (P ^ k * 𝔰) (P ^ m * 𝔯) =
              a (P ^ e₀) (P ^ l) (P ^ k) (P ^ m) * a 𝔠 𝔫 𝔰 𝔯) ∧
        (∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → ¬ r.1.1 ≤ P →
          residueSymbol ι 𝔪 P (freqElt g r) ^ 6 = 1 ∧
          ∀ e₀ l k m : ℕ, e₀ ≤ 1 →
            a (P ^ e₀) (P ^ l) (P ^ k) (P ^ m) =
              residueSymbol ι 𝔪 P (freqElt g r) ^ k *
                starRingEnd ℂ (residueSymbol ι 𝔪 P (freqElt g r)) ^ (e₀ + 3 * l) *
                principalLocalCoeff (Ideal.absNorm P) (χ.toFun P)
                  (starRingEnd ℂ (jacobiPhaseSix ι P) * χ.toFun P ^ 6) e₀ l k m) ∧
        (∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → r.1.1 ≤ P →
          residueSymbol ι 𝔪 P (freqElt g r) = 0 ∧
          (∀ k m : ℕ, a (P ^ 0) (P ^ 0) (P ^ k) (P ^ m) = if k = 0 then 1 else 0) ∧
          (∀ e₀ l k m : ℕ, 2 ≤ k → a (P ^ e₀) (P ^ l) (P ^ k) (P ^ m) = 0) ∧
          (∀ e₀ l k m : ℕ, e₀ ≤ 1 →
            ‖a (P ^ e₀) (P ^ l) (P ^ k) (P ^ m)‖ ≤
              (Ideal.absNorm P : ℝ) ^ (e₀ + 3 * l) * Real.sqrt (Ideal.absNorm P) ^ k)) := by
  obtain ⟨N₀, h⟩ := L3R.coeffU_pub n hn0 hn ι
  exact ⟨N₀, h⟩

end ArtinPrimitiveRoots

end
end

section
open NumberField
open ArtinPrimitiveRoots

theorem solution (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (r : FreqClass 𝔪),
        let a : Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ := fun 𝔠 𝔫 𝔰 𝔯 =>
          gaussPhase g 2 𝔠 * χ.thetaChar g (𝔠 * 𝔫 ^ 3) *
            poissonFactor g 𝔰 (𝔠 * 𝔫 ^ 3) (freqElt g r * g.gen 𝔯 ^ 6)
        a ⊤ ⊤ ⊤ ⊤ = 1 ∧
        (∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → ∀ e₀ l k m : ℕ, e₀ ≤ 1 →
          ∀ 𝔠 𝔫 𝔰 𝔯 : Ideal (𝓞 F), IsExterior 𝔪 𝔠 → Squarefree 𝔠 → IsExterior 𝔪 𝔫 →
            IsExterior 𝔪 𝔰 → IsExterior 𝔪 𝔯 → ¬ 𝔠 ≤ P → ¬ 𝔫 ≤ P → ¬ 𝔰 ≤ P → ¬ 𝔯 ≤ P →
            a (P ^ e₀ * 𝔠) (P ^ l * 𝔫) (P ^ k * 𝔰) (P ^ m * 𝔯) =
              a (P ^ e₀) (P ^ l) (P ^ k) (P ^ m) * a 𝔠 𝔫 𝔰 𝔯) ∧
        (∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → ¬ r.1.1 ≤ P →
          residueSymbol ι 𝔪 P (freqElt g r) ^ 6 = 1 ∧
          ∀ e₀ l k m : ℕ, e₀ ≤ 1 →
            a (P ^ e₀) (P ^ l) (P ^ k) (P ^ m) =
              residueSymbol ι 𝔪 P (freqElt g r) ^ k *
                starRingEnd ℂ (residueSymbol ι 𝔪 P (freqElt g r)) ^ (e₀ + 3 * l) *
                principalLocalCoeff (Ideal.absNorm P) (χ.toFun P)
                  (starRingEnd ℂ (jacobiPhaseSix ι P) * χ.toFun P ^ 6) e₀ l k m) ∧
        (∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → r.1.1 ≤ P →
          residueSymbol ι 𝔪 P (freqElt g r) = 0 ∧
          (∀ k m : ℕ, a (P ^ 0) (P ^ 0) (P ^ k) (P ^ m) = if k = 0 then 1 else 0) ∧
          (∀ e₀ l k m : ℕ, 2 ≤ k → a (P ^ e₀) (P ^ l) (P ^ k) (P ^ m) = 0) ∧
          (∀ e₀ l k m : ℕ, e₀ ≤ 1 →
            ‖a (P ^ e₀) (P ^ l) (P ^ k) (P ^ m)‖ ≤
              (Ideal.absNorm P : ℝ) ^ (e₀ + 3 * l) * Real.sqrt (Ideal.absNorm P) ^ k)) := by
  exact ArtinPrimitiveRoots.exists_cutoff_freqCoeff_freqElt_eq_one_and_eq_mul n hn0 hn F ι

end
