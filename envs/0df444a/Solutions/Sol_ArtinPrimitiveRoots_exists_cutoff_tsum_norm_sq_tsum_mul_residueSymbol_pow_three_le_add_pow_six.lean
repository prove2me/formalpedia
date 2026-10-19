-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le_add_pow_six
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:15:23.481974+00:00
-- url     : https://prove2.me/submissions/2239c653-cd59-4c61-8342-6fdcb4734886

import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Definitions.Def_ArtinHeckeRowL
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_exists_differentiable_eq_kummerL_and_norm_le
import Mathlib

section
section
/-! # C3B_Norm: the additive character on `R`, the unit ideal, and `a(1,1,1,1) = 1` -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

/-- The generator of the unit ideal is a unit of `R`. -/
lemma isUnit_gen_top {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) :
    IsUnit (g.gen ⊤) := by
  have h := g.span_gen ⊤ ⟨top_ne_bot, top_sup_eq _⟩
  rw [Ideal.map_top] at h
  exact Ideal.span_singleton_eq_top.mp h

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

/-- The principal frequency element is the sixth power of an `S`-unit. -/
theorem freqElt_principalFreq {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) :
    ∃ μ : (SInt 𝔪)ˣ, freqElt g (principalFreq 𝔪) = (μ : SInt 𝔪) ^ 6 := by
  -- the representative of the trivial class is a sixth power
  set w := Function.surjInv (QuotientGroup.mk_surjective
    (s := (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range)) (1 : SClass 𝔪)
  have hw : (w : SClass 𝔪) = 1 := Function.surjInv_eq _ _
  rw [QuotientGroup.eq_one_iff] at hw
  obtain ⟨ν, hν⟩ := hw
  -- the generator of the unit ideal is the inverse sixth power of an `S`-unit
  obtain ⟨ε, hε⟩ := g.gen_mul ⊤ ⊤ ⟨top_ne_bot, top_sup_eq _⟩ ⟨top_ne_bot, top_sup_eq _⟩
  rw [Ideal.top_mul] at hε
  have hG0 := gen_ne_zero g ⊤ ⟨top_ne_bot, top_sup_eq _⟩
  have hG : (g.gen ⊤ : F) * ((ε : Fˣ) : F) ^ 6 = 1 := by
    have h2 : (g.gen ⊤ : F) * 1 = (g.gen ⊤ : F) * (((ε : Fˣ) : F) ^ 6 * (g.gen ⊤ : F)) := by
      rw [mul_one]; nth_rewrite 1 [hε]; ring
    have := mul_left_cancel₀ hG0 h2
    linear_combination -this
  set ν' := Set.unitEquivUnitsInteger (placesOf 𝔪) F ν
  set ε' := Set.unitEquivUnitsInteger (placesOf 𝔪) F ε
  refine ⟨ν' * ε'⁻¹, ?_⟩
  apply Subtype.ext
  have hrep : ((SClass.rep (1 : SClass 𝔪) : SInt 𝔪) : F) = ((ν : Fˣ) : F) ^ 6 := by
    change (((Set.unitEquivUnitsInteger (placesOf 𝔪) F w : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = _
    rw [← hν]
    simp [powMonoidHom_apply]
  have hε'inv : (((ε'⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) * ((ε : Fˣ) : F) = 1 := by
    have : (((ε'⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) * ((ε' : SInt 𝔪) : F) = 1 := by
      rw [← Subalgebra.coe_mul, Units.inv_mul]; rfl
    simpa [ε'] using this
  have hfe : freqElt g (principalFreq 𝔪) = SClass.rep (1 : SClass 𝔪) * g.gen ⊤ := rfl
  rw [hfe, Subalgebra.coe_mul, hrep, Subalgebra.coe_pow, Units.val_mul, Subalgebra.coe_mul]
  have hν' : ((ν' : SInt 𝔪) : F) = ((ν : Fˣ) : F) := rfl
  rw [hν', mul_pow]
  congr 1
  have hG' : (g.gen ⊤ : F) = ((((ε'⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F)) ^ 6 := by
    have h3 : ((((ε'⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F)) ^ 6 * ((ε : Fˣ) : F) ^ 6 = 1 := by
      rw [← mul_pow, hε'inv, one_pow]
    have hε0 : ((ε : Fˣ) : F) ^ 6 ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
    exact mul_right_cancel₀ hε0 (hG.trans h3.symm)
  exact hG'

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
/-! # L3E_Arith: the off-diagonal coefficient `χ_𝔡(g𝔠₁)³ conj χ_𝔡(g𝔠₂)³`

For exterior squarefree `𝔠₁ ≠ 𝔠₂`, with `𝔞 = 𝔠₁ ⊔ 𝔠₂`, `𝔠ᵢ = 𝔞 𝔟ᵢ`, `𝔲 = (𝔟₁𝔟₂)³` and
`T` the primes of `𝔞`: the frequency class `r = (𝔲, 1)` is not principal, `N 𝔲 ≤ (N𝔠₁ N𝔠₂)³`,
`2^{|T|} ≤ N𝔠₁`, and for every exterior `𝔡`
`χ_𝔡(g𝔠₁)³ conj χ_𝔡(g𝔠₂)³ = 1[𝔡 ⊄ P ∀ P ∈ T] χ_𝔡(freqElt g r)`. -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinPrimitiveRoots

namespace L3E

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

lemma conj_eq_of {z : ℂ} (h : z = 0 ∨ z ^ 2 = 1) : starRingEnd ℂ z = z := by
  rcases h with h | h
  · rw [h, map_zero]
  · have : (z - 1) * (z + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h1 | h1
    · rw [show z = 1 by linear_combination h1, map_one]
    · rw [show z = -1 by linear_combination h1, map_neg, map_one]

lemma sextic_eq_zero_of_mem {P : Ideal (𝓞 F)} {x : SInt 𝔪}
    (hx : x ∈ P.map (algebraMap (𝓞 F) (SInt 𝔪))) : sexticResidueSymbol ι 𝔪 P x = 0 := by
  unfold sexticResidueSymbol
  rw [if_pos (Ideal.Quotient.eq_zero_iff_mem.2 hx)]

lemma conj_rs_cube (hχ : C3M.HypChi ι 𝔪) {𝔡 : Ideal (𝓞 F)} (h𝔡 : IsExterior 𝔪 𝔡) (x : SInt 𝔪) :
    starRingEnd ℂ (residueSymbol ι 𝔪 𝔡 x ^ 3) = residueSymbol ι 𝔪 𝔡 x ^ 3 := by
  unfold residueSymbol
  rw [← Multiset.prod_map_pow, map_multiset_prod, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun Q hQ => ?_
  obtain ⟨hQp, hQe⟩ := C3M.exterior_of_mem_factors h𝔡 hQ
  refine conj_eq_of ?_
  by_cases hx : x ∈ Q.map (algebraMap (𝓞 F) (SInt 𝔪))
  · left; simp [sextic_eq_zero_of_mem (ι := ι) hx]
  · right
    have := (hχ Q hQp hQe).2 x hx
    rw [← pow_mul]; simpa using this

lemma mem_normalizedFactors_of_le {I P : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hle : I ≤ P) : P ∈ normalizedFactors I := by
  have hpr : Prime P := Ideal.prime_of_isPrime hP0 hP
  obtain ⟨q, hq, hassoc⟩ := exists_mem_normalizedFactors_of_dvd hI hpr.irreducible
    (Ideal.dvd_iff_le.2 hle)
  rwa [associated_iff_eq.1 hassoc]

lemma rs_eq_zero_of_le {𝔡 P : Ideal (𝓞 F)} (h𝔡 : 𝔡 ≠ ⊥) (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hle : 𝔡 ≤ P) {x : SInt 𝔪} (hx : x ∈ P.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    residueSymbol ι 𝔪 𝔡 x = 0 := by
  unfold residueSymbol
  refine Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨P, ?_, sextic_eq_zero_of_mem hx⟩)
  exact mem_normalizedFactors_of_le h𝔡 hP hP0 hle

lemma isExterior_sup_left {I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) : IsExterior 𝔪 (I ⊔ J) :=
  ⟨fun h => hI.1 (eq_bot_iff.2 (h ▸ le_sup_left)),
    eq_top_iff.2 (hI.2 ▸ sup_le_sup_right le_sup_left 𝔪)⟩

lemma sup_mul_eq_top_iff' {I J : Ideal (𝓞 F)} :
    I * J ⊔ 𝔪 = ⊤ ↔ I ⊔ 𝔪 = ⊤ ∧ J ⊔ 𝔪 = ⊤ := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [eq_top_iff, ← h]; exact sup_le_sup_right Ideal.mul_le_left _
    · rw [eq_top_iff, ← h]; exact sup_le_sup_right Ideal.mul_le_right _
  · rintro ⟨h1, h2⟩
    rw [Ideal.mul_sup_eq_of_coprime_left h1, h2]

lemma isExterior_mul {I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (hJ : IsExterior 𝔪 J) :
    IsExterior 𝔪 (I * J) := by
  refine ⟨?_, sup_mul_eq_top_iff'.2 ⟨hI.2, hJ.2⟩⟩
  rw [Ne, ← Ideal.zero_eq_bot, mul_eq_zero, not_or]
  exact ⟨hI.1, hJ.1⟩

lemma two_le_absNorm {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) : 2 ≤ Ideal.absNorm P := by
  have h0 : Ideal.absNorm P ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have h1 : Ideal.absNorm P ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact hP.ne_top
  omega

lemma pow_card_le_absNorm {𝔞 : Ideal (𝓞 F)} (h𝔞 : 𝔞 ≠ ⊥) :
    2 ^ (normalizedFactors 𝔞).toFinset.card ≤ Ideal.absNorm 𝔞 := by
  have hprod : (normalizedFactors 𝔞).prod = 𝔞 :=
    associated_iff_eq.1 (prod_normalizedFactors h𝔞)
  have hN : Ideal.absNorm 𝔞 = ((normalizedFactors 𝔞).map Ideal.absNorm).prod := by
    conv_lhs => rw [← hprod]
    exact map_multiset_prod Ideal.absNorm _
  rw [hN]
  calc 2 ^ (normalizedFactors 𝔞).toFinset.card ≤ 2 ^ (normalizedFactors 𝔞).card :=
        Nat.pow_le_pow_right (by norm_num) (Multiset.toFinset_card_le _)
    _ = 2 ^ ((normalizedFactors 𝔞).map Ideal.absNorm).card := by rw [Multiset.card_map]
    _ ≤ _ := by
        refine Multiset.pow_card_le_prod fun x hx => ?_
        obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hx
        have hpr : Prime P := prime_of_normalized_factor P hP
        exact two_le_absNorm (Ideal.isPrime_of_prime hpr) hpr.ne_zero

open Classical in
/-- The data of the off-diagonal pair. -/
theorem offdiag (hχ : C3M.HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {𝔠₁ 𝔠₂ : Ideal (𝓞 F)}
    (h₁ : IsExterior 𝔪 𝔠₁) (h₂ : IsExterior 𝔪 𝔠₂) (s₁ : Squarefree 𝔠₁) (s₂ : Squarefree 𝔠₂)
    (hne : 𝔠₁ ≠ 𝔠₂) :
    ∃ (r : FreqClass 𝔪) (T : Finset (Ideal (𝓞 F))), r ≠ principalFreq 𝔪 ∧
      Ideal.absNorm r.1.1 ≤ (Ideal.absNorm 𝔠₁ * Ideal.absNorm 𝔠₂) ^ 3 ∧
      2 ^ T.card ≤ Ideal.absNorm 𝔠₁ ∧
      (∀ P ∈ T, P.IsPrime ∧ IsExterior 𝔪 P) ∧
      ∀ 𝔡 : Ideal (𝓞 F), IsExterior 𝔪 𝔡 →
        residueSymbol ι 𝔪 𝔡 (g.gen 𝔠₁) ^ 3 *
            starRingEnd ℂ (residueSymbol ι 𝔪 𝔡 (g.gen 𝔠₂) ^ 3) =
          if ∀ P ∈ T, ¬ 𝔡 ≤ P then residueSymbol ι 𝔪 𝔡 (freqElt g r) else 0 := by
  classical
  set 𝔞 := 𝔠₁ ⊔ 𝔠₂ with h𝔞
  have h𝔞e : IsExterior 𝔪 𝔞 := isExterior_sup_left h₁
  obtain ⟨𝔟₁, hb₁⟩ : 𝔞 ∣ 𝔠₁ := Ideal.dvd_iff_le.2 le_sup_left
  obtain ⟨𝔟₂, hb₂⟩ : 𝔞 ∣ 𝔠₂ := Ideal.dvd_iff_le.2 le_sup_right
  have hb₁e : IsExterior 𝔪 𝔟₁ := C3M.isExterior_of_mul_right (hb₁ ▸ h₁)
  have hb₂e : IsExterior 𝔪 𝔟₂ := C3M.isExterior_of_mul_right (hb₂ ▸ h₂)
  have hcop : 𝔟₁ ⊔ 𝔟₂ = ⊤ := by
    have h : 𝔞 * ⊤ = 𝔞 * (𝔟₁ ⊔ 𝔟₂) := by
      rw [Ideal.mul_top, Ideal.mul_sup, ← hb₁, ← hb₂]
    have h0 : 𝔞 ≠ 0 := h𝔞e.1
    exact (mul_left_cancel₀ h0 h).symm
  have sb₁ : Squarefree 𝔟₁ := Squarefree.of_mul_right (hb₁ ▸ s₁)
  have sb₂ : Squarefree 𝔟₂ := Squarefree.of_mul_right (hb₂ ▸ s₂)
  set 𝔟 := 𝔟₁ * 𝔟₂ with h𝔟
  have hbe : IsExterior 𝔪 𝔟 := isExterior_mul hb₁e hb₂e
  have sb : Squarefree 𝔟 := by
    refine squarefree_mul_iff.2 ⟨fun d hd₁ hd₂ => ?_, sb₁, sb₂⟩
    rw [Ideal.isUnit_iff, eq_top_iff, ← hcop]
    exact sup_le (Ideal.dvd_iff_le.1 hd₁) (Ideal.dvd_iff_le.1 hd₂)
  have hbtop : 𝔟 ≠ ⊤ := by
    intro h
    have e1 : 𝔟₁ = ⊤ := eq_top_iff.2 (h ▸ Ideal.mul_le_left)
    have e2 : 𝔟₂ = ⊤ := eq_top_iff.2 (h ▸ Ideal.mul_le_right)
    apply hne
    rw [hb₁, hb₂, e1, e2]
  set 𝔲 := 𝔟 * 𝔟 * 𝔟 with h𝔲
  have hue : IsExterior 𝔪 𝔲 := isExterior_mul (isExterior_mul hbe hbe) hbe
  have hufree : IsSixthPowerFree 𝔲 := by
    intro J hJ
    have h3 : (J ^ 2) ^ 3 ∣ 𝔟 ^ 3 := by
      rw [← pow_mul]; rw [h𝔲] at hJ; simpa [pow_succ, mul_assoc] using hJ
    have h2 : J * J ∣ 𝔟 := by rw [← sq]; exact (pow_dvd_pow_iff_dvd (by norm_num)).1 h3
    exact sb J h2
  have hutop : 𝔲 ≠ ⊤ := fun h => hbtop (eq_top_iff.2 (h ▸ Ideal.mul_le_right))
  set r : FreqClass 𝔪 := (⟨𝔲, hue, hufree⟩, 1) with hr
  set T := (normalizedFactors 𝔞).toFinset with hT
  refine ⟨r, T, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hutop
    have := congrArg (fun p : FreqClass 𝔪 => p.1.1) h
    exact this
  · show Ideal.absNorm 𝔲 ≤ _
    have hN𝔞 : 1 ≤ Ideal.absNorm 𝔞 :=
      Nat.one_le_iff_ne_zero.2 (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔞e.1)
    have e1 : Ideal.absNorm 𝔟₁ ≤ Ideal.absNorm 𝔠₁ := by
      rw [hb₁, map_mul]; exact Nat.le_mul_of_pos_left _ hN𝔞
    have e2 : Ideal.absNorm 𝔟₂ ≤ Ideal.absNorm 𝔠₂ := by
      rw [hb₂, map_mul]; exact Nat.le_mul_of_pos_left _ hN𝔞
    rw [h𝔲, h𝔟, map_mul, map_mul, map_mul]
    have := Nat.mul_le_mul e1 e2
    calc _ = (Ideal.absNorm 𝔟₁ * Ideal.absNorm 𝔟₂) ^ 3 := by ring
      _ ≤ _ := Nat.pow_le_pow_left this 3
  · refine (pow_card_le_absNorm h𝔞e.1).trans ?_
    rw [hb₁, map_mul]
    exact Nat.le_mul_of_pos_right _
      (Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hb₁e.1))
  · intro P hP
    exact C3M.exterior_of_mem_factors h𝔞e (Multiset.mem_toFinset.1 hP)
  · intro 𝔡 h𝔡
    split_ifs with hc
    · -- coprime to `𝔞`
      have hsup : 𝔞 ⊔ 𝔡 = ⊤ := by
        by_contra hne'
        obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne'
        have hM0 : M ≠ ⊥ := fun h0 => h𝔞e.1 (eq_bot_iff.2 (h0 ▸ le_sup_left.trans hle))
        have hMT : M ∈ T := Multiset.mem_toFinset.2
          (mem_normalizedFactors_of_le h𝔞e.1 hM.isPrime hM0 (le_sup_left.trans hle))
        exact hc M hMT (le_sup_right.trans hle)
      have hcopA : IsCoprime (Ideal.span {g.gen 𝔞}) (𝔡.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
        rw [Ideal.isCoprime_iff_sup_eq, g.span_gen 𝔞 h𝔞e, ← Ideal.map_sup, hsup, Ideal.map_top]
      obtain ⟨e₁, he₁⟩ := C3M.gen_mul' g h𝔞e hb₁e
      obtain ⟨e₂, he₂⟩ := C3M.gen_mul' g h𝔞e hb₂e
      obtain ⟨e₃, he₃⟩ := C3M.gen_mul' g hb₁e hb₂e
      obtain ⟨e₄, he₄⟩ := C3M.gen_mul' g hbe hbe
      obtain ⟨e₅, he₅⟩ := C3M.gen_mul' g (isExterior_mul hbe hbe) hbe
      obtain ⟨μ, hμ⟩ := C3B.freqElt_principalFreq g
      obtain ⟨ε, hε⟩ := C3M.gen_top g
      rw [conj_rs_cube hχ h𝔡, ← C3M.residueSymbol_pow hχ h𝔡, ← C3M.residueSymbol_pow hχ h𝔡,
        ← C3M.residueSymbol_mul hχ h𝔡]
      -- the element identity
      have key : ((e₃ : SInt 𝔪) ^ 3 * e₄ * e₅) ^ 6 * (g.gen 𝔠₁ ^ 3 * g.gen 𝔠₂ ^ 3) =
          ((e₁ : SInt 𝔪) ^ 3 * e₂ ^ 3) ^ 6 * (g.gen 𝔞 ^ 6 * g.gen 𝔲) := by
        rw [hb₁, hb₂, he₁, he₂, h𝔲, he₅, he₄, h𝔟, he₃]
        ring
      have hfe : freqElt g r = SClass.rep (1 : SClass 𝔪) * g.gen 𝔲 := rfl
      have hfe' : (ε : SInt 𝔪) ^ 6 * freqElt g r = (μ : SInt 𝔪) ^ 6 * g.gen 𝔲 := by
        have h1 : freqElt g (principalFreq 𝔪) = SClass.rep (1 : SClass 𝔪) * g.gen ⊤ := rfl
        rw [h1, hε] at hμ
        rw [hfe, ← hμ]; ring
      have hu6 : ((e₃ : SInt 𝔪) ^ 3 * e₄ * e₅) ^ 6 = ((e₃ ^ 3 * e₄ * e₅ : (SInt 𝔪)ˣ) :
          SInt 𝔪) ^ 6 := by push_cast; rfl
      have hu6' : ((e₁ : SInt 𝔪) ^ 3 * e₂ ^ 3) ^ 6 = ((e₁ ^ 3 * e₂ ^ 3 : (SInt 𝔪)ˣ) :
          SInt 𝔪) ^ 6 := by push_cast; rfl
      rw [← C3M.residueSymbol_unit_pow_six hχ h𝔡 (e₃ ^ 3 * e₄ * e₅), ← hu6, key, hu6',
        C3M.residueSymbol_unit_pow_six hχ h𝔡, C3M.residueSymbol_mul hχ h𝔡,
        C3M.residueSymbol_pow hχ h𝔡, C3M.residueSymbol_pow_six hχ h𝔡 hcopA, one_mul,
        ← C3M.residueSymbol_unit_pow_six hχ h𝔡 ε (freqElt g r), hfe',
        C3M.residueSymbol_unit_pow_six hχ h𝔡]
    · -- a prime of `𝔞` contains `𝔡`
      push Not at hc
      obtain ⟨P, hPT, hle⟩ := hc
      obtain ⟨hPp, hPe⟩ := C3M.exterior_of_mem_factors h𝔞e (Multiset.mem_toFinset.1 hPT)
      have h𝔞P : 𝔞 ≤ P := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.1 hPT))
      have hmem : g.gen 𝔠₁ ∈ P.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
        have : g.gen 𝔠₁ ∈ Ideal.span {g.gen 𝔠₁} := Ideal.mem_span_singleton_self _
        rw [g.span_gen 𝔠₁ h₁] at this
        exact Ideal.map_mono (le_sup_left.trans h𝔞P) this
      rw [rs_eq_zero_of_le h𝔡.1 hPp hPe.1 hle hmem]
      ring

end L3E

end ArtinPrimitiveRoots

end
end

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

lemma norm_GammaSeq (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    ‖GammaSeq s n‖ =
      (n : ℝ) ^ s.re * (Nat.factorial n : ℝ) / ∏ j ∈ Finset.range (n + 1), ‖s + j‖ := by
  rw [GammaSeq, norm_div, norm_mul, norm_prod,
    Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
  simp

lemma prod_pos_norm {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    0 < ∏ j ∈ Finset.range (n + 1), ‖s + j‖ := by
  refine Finset.prod_pos fun j _ => norm_pos_iff.2 fun h => ?_
  have := congrArg Complex.re h
  simp at this
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

lemma term_ineq {x y t : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    ‖(y : ℂ) + t * I‖ * ‖(x : ℂ)‖ ≤ ‖(x : ℂ) + t * I‖ * ‖(y : ℂ)‖ := by
  have hy : 0 < y := hx.trans_le hxy
  rw [Complex.norm_add_mul_I, Complex.norm_add_mul_I, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx, abs_of_pos hy]
  have e1 : √(y ^ 2 + t ^ 2) * x = √((y ^ 2 + t ^ 2) * x ^ 2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hx.le]
  have e2 : √(x ^ 2 + t ^ 2) * y = √((x ^ 2 + t ^ 2) * y ^ 2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hy.le]
  rw [e1, e2]
  apply Real.sqrt_le_sqrt
  have h1 : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx.le hxy 2
  nlinarith [sq_nonneg t]

/-- `‖Γ(a + it)‖ Γ(b) ≤ ‖Γ(b + it)‖ Γ(a)` for `0 < a ≤ b`. -/
theorem norm_Gamma_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (t : ℝ) :
    ‖Gamma ((a : ℂ) + t * I)‖ * ‖Gamma (b : ℂ)‖ ≤ ‖Gamma ((b : ℂ) + t * I)‖ * ‖Gamma (a : ℂ)‖ := by
  have hb : 0 < b := ha.trans_le hab
  have key : ∀ n : ℕ, n ≠ 0 →
      ‖GammaSeq ((a : ℂ) + t * I) n‖ * ‖GammaSeq (b : ℂ) n‖ ≤
        ‖GammaSeq ((b : ℂ) + t * I) n‖ * ‖GammaSeq (a : ℂ) n‖ := by
    intro n hn
    have hre : ∀ x : ℝ, ((x : ℂ) + t * I).re = x := fun x => by simp
    rw [norm_GammaSeq _ hn, norm_GammaSeq _ hn, norm_GammaSeq _ hn, norm_GammaSeq _ hn,
      hre, hre, Complex.ofReal_re, Complex.ofReal_re]
    have hPa := prod_pos_norm (s := (a : ℂ) + t * I) (by rw [hre]; exact ha) n
    have hPb := prod_pos_norm (s := (b : ℂ) + t * I) (by rw [hre]; exact hb) n
    have hQa := prod_pos_norm (s := (a : ℂ)) (by simpa using ha) n
    have hQb := prod_pos_norm (s := (b : ℂ)) (by simpa using hb) n
    rw [div_mul_div_comm, div_mul_div_comm]
    have hnum : (n : ℝ) ^ a * (Nat.factorial n : ℝ) * ((n : ℝ) ^ b * (Nat.factorial n : ℝ)) =
        (n : ℝ) ^ b * (Nat.factorial n : ℝ) * ((n : ℝ) ^ a * (Nat.factorial n : ℝ)) := by ring
    rw [hnum]
    apply div_le_div_of_nonneg_left (by positivity) (mul_pos hPb hQa)
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod (fun j _ => by positivity)
    intro j _
    have e1 : ∀ x : ℝ, (x : ℂ) + t * I + j = ((x + j : ℝ) : ℂ) + t * I := fun x => by
      push_cast; ring
    have e2 : ∀ x : ℝ, (x : ℂ) + j = ((x + j : ℝ) : ℂ) := fun x => by push_cast; ring
    rw [e1, e1, e2, e2]
    exact term_ineq (by positivity) (by linarith)
  have hlim : ∀ s : ℂ, Tendsto (fun n => ‖GammaSeq s n‖) atTop (𝓝 ‖Gamma s‖) :=
    fun s => (GammaSeq_tendsto_Gamma s).norm
  exact le_of_tendsto_of_tendsto ((hlim _).mul (hlim _)) ((hlim _).mul (hlim _))
    (by filter_upwards [eventually_ne_atTop 0] with n hn using key n hn)

/-- `‖Γ(1 + it)‖² ‖sin(π(1 + it))‖ = π |t|`. -/
lemma norm_Gamma_one_add_sq_mul (t : ℝ) :
    ‖Gamma (1 + t * I)‖ ^ 2 * ‖Complex.sin ((Real.pi : ℂ) * (1 + t * I))‖ = Real.pi * |t| := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  have hz : (-(t : ℂ) * I) ≠ 0 := by
    simp [ht]
  have hrefl := Gamma_mul_Gamma_one_sub (1 + t * I)
  have hsub : (1 : ℂ) - (1 + t * I) = -(t : ℂ) * I := by ring
  rw [hsub] at hrefl
  have hconj : Gamma (1 - t * I) = (starRingEnd ℂ) (Gamma (1 + t * I)) := by
    rw [← Gamma_conj]; congr 1; simp [Complex.conj_ofReal]; ring
  have hadd : Gamma (1 - t * I) = (-(t : ℂ) * I) * Gamma (-(t : ℂ) * I) := by
    have := Gamma_add_one (-(t : ℂ) * I) hz
    rw [show -(t : ℂ) * I + 1 = 1 - t * I by ring] at this
    exact this
  have hsq : (‖Gamma (1 + t * I)‖ ^ 2 : ℂ) = Gamma (1 + t * I) * Gamma (1 - t * I) := by
    rw [hconj, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hsin : Complex.sin ((Real.pi : ℂ) * (1 + t * I)) ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hrefl
    rcases mul_eq_zero.1 hrefl with h | h
    · exact Gamma_ne_zero_of_re_pos (by simp) h
    · exact Gamma_ne_zero (fun m hm => by
        have := congrArg Complex.re hm; simp at this
        have := congrArg Complex.im hm; simp at this; exact ht this) h
  have key : (‖Gamma (1 + t * I)‖ ^ 2 : ℂ) * Complex.sin ((Real.pi : ℂ) * (1 + t * I)) =
      (-(t : ℂ) * I) * Real.pi := by
    rw [hsq, hadd, show Gamma (1 + t * I) * (-(t : ℂ) * I * Gamma (-(t : ℂ) * I)) =
      (-(t : ℂ) * I) * (Gamma (1 + t * I) * Gamma (-(t : ℂ) * I)) by ring, hrefl]
    field_simp
  have := congrArg (‖·‖) key
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_neg,
    Complex.norm_I, mul_one, abs_norm] at this
  rw [this, abs_of_pos Real.pi_pos]; ring

lemma norm_sin_pi_one_add (t : ℝ) :
    ‖Complex.sin ((Real.pi : ℂ) * (1 + t * I))‖ = |Real.sinh (Real.pi * t)| := by
  rw [show (Real.pi : ℂ) * (1 + t * I) = ((Real.pi * t : ℝ) : ℂ) * I + Real.pi by push_cast; ring,
    Complex.sin_add_pi, norm_neg, Complex.sin_mul_I, norm_mul, Complex.norm_I, mul_one,
    ← Complex.ofReal_sinh, Complex.norm_real, Real.norm_eq_abs]

/-- `‖Γ(1 + it)‖² ≤ 4π e^π (1 + |t|) e^{−π|t|}`. -/
lemma norm_Gamma_one_add_sq_le (t : ℝ) :
    ‖Gamma (1 + t * I)‖ ^ 2 ≤ 4 * Real.pi * Real.exp Real.pi * (1 + |t|) * Real.exp (-(Real.pi * |t|)) := by
  have hk := norm_Gamma_one_add_sq_mul t
  rw [norm_sin_pi_one_add] at hk
  have hsh : |Real.sinh (Real.pi * t)| = Real.sinh (Real.pi * |t|) := by
    rw [Real.abs_sinh, abs_mul, abs_of_pos Real.pi_pos]
  rw [hsh] at hk
  set G := ‖Gamma (1 + t * I)‖ ^ 2 with hG
  set x := Real.pi * |t| with hx
  have hpi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hx0 : 0 ≤ x := by positivity
  have hG0 : 0 ≤ G := by positivity
  have hE : 1 ≤ Real.exp Real.pi := Real.one_le_exp hpi.le
  have hRHS : 4 * Real.pi * (1 + |t|) * Real.exp (-x) ≤
      4 * Real.pi * Real.exp Real.pi * (1 + |t|) * Real.exp (-x) := by
    have : 0 ≤ 4 * Real.pi * (1 + |t|) * Real.exp (-x) := by positivity
    nlinarith
  rcases eq_or_lt_of_le hx0 with h0 | hpos
  · have ht : t = 0 := by
      have : |t| = 0 := by
        rcases mul_eq_zero.1 h0.symm with h | h
        · exact absurd h hpi.ne'
        · exact h
      exact abs_eq_zero.1 this
    subst ht
    have : G = 1 := by rw [hG]; simp
    rw [this, ← h0, abs_zero, add_zero, neg_zero, Real.exp_zero, mul_one, mul_one]
    nlinarith
  have hsx : 0 < Real.sinh x := Real.sinh_pos_iff.2 hpos
  have hGeq : G = x / Real.sinh x := by field_simp; linarith
  rcases le_or_gt Real.pi x with hbig | hsmall
  · -- `sinh x ≥ e^x / 4`
    have hex : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
    have hemx : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hsh4 : Real.exp x / 4 ≤ Real.sinh x := by
      rw [Real.sinh_eq]; linarith
    have hprod : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    have hG4 : G ≤ 4 * x * Real.exp (-x) := by
      rw [hGeq, div_le_iff₀ hsx]
      have h1 : 4 * x * Real.exp (-x) * (Real.exp x / 4) = x := by
        field_simp
        rw [mul_comm]; exact hprod
      have : 0 ≤ 4 * x * Real.exp (-x) := by positivity
      nlinarith
    refine hG4.trans (le_trans ?_ hRHS)
    have : x ≤ Real.pi * (1 + |t|) := by rw [hx]; nlinarith [abs_nonneg t]
    have he := Real.exp_pos (-x)
    nlinarith
  · have hG1 : G ≤ 1 := by
      rw [hGeq, div_le_one hsx]; exact Real.self_le_sinh_iff.2 hx0
    refine hG1.trans ?_
    have hex : Real.exp (-Real.pi) ≤ Real.exp (-x) := Real.exp_le_exp.2 (by linarith)
    have hep : Real.exp Real.pi * Real.exp (-Real.pi) = 1 := by rw [← Real.exp_add]; simp
    have : 1 ≤ 4 * Real.pi * (1 + |t|) * Real.exp (-x) * Real.exp Real.pi := by
      have h1 : 1 ≤ 4 * Real.pi * (1 + |t|) := by nlinarith [abs_nonneg t]
      have h2 : 1 ≤ Real.exp (-x) * Real.exp Real.pi := by nlinarith [Real.exp_pos (-Real.pi)]
      nlinarith [Real.exp_pos (-x)]
    have e : 4 * Real.pi * Real.exp Real.pi * (1 + |t|) * Real.exp (-x) =
        4 * Real.pi * (1 + |t|) * Real.exp (-x) * Real.exp Real.pi := by ring
    linarith

end L3K

end ArtinPrimitiveRoots

end
end

section
section
/-! # L2C_Maj: polynomial majorants `ν_N(t) = (1 + |t|)^{-N}`

* `nu N t = (1 + |t|)^{-N}`: positive, `≤ 1`, antitone in `N`, integrable for `N > 1`, tending to
  `0` at `±∞` for `N > 0`;
* `gauss_split`: `e^{-(a+b)²} ν_{N+M}(b) ≤ e^{N²/4} ν_N(a) ν_M(b)` (`N ≥ 0`);
* `poly_nu`: `(2 + |t|)^A ν_{A+2}(t) ≤ 2^A ν_2(t)`;
* `nu_tail`: `ν_N(t) ≤ (1 + T)^{-(N-2)} ν_2(t)` for `|t| ≥ T ≥ 0`, `N ≥ 2`. -/

open Real MeasureTheory Filter Topology Set

namespace ArtinPrimitiveRoots

namespace L2C

noncomputable section

/-- `ν_N(t) = (1 + |t|)^{-N}`. -/
def nu (N t : ℝ) : ℝ := (1 + |t|) ^ (-N)

lemma one_add_abs_pos (t : ℝ) : 0 < 1 + |t| := by positivity

lemma nu_pos (N t : ℝ) : 0 < nu N t := Real.rpow_pos_of_pos (one_add_abs_pos t) _

lemma nu_nonneg (N t : ℝ) : 0 ≤ nu N t := (nu_pos N t).le

lemma integrable_nu {N : ℝ} (hN : 1 < N) : Integrable (nu N) := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := N) (by simpa using hN)
  exact h.congr (Eventually.of_forall fun t => by simp [nu, Real.norm_eq_abs])

lemma tendsto_nu_atTop {N : ℝ} (hN : 0 < N) : Tendsto (nu N) atTop (𝓝 0) := by
  unfold nu
  have h1 : Tendsto (fun t : ℝ => 1 + |t|) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_abs_atTop_atTop.comp tendsto_id)
  exact (tendsto_rpow_neg_atTop hN).comp h1

lemma tendsto_nu_atBot {N : ℝ} (hN : 0 < N) : Tendsto (nu N) atBot (𝓝 0) := by
  unfold nu
  have h1 : Tendsto (fun t : ℝ => 1 + |t|) atBot atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_abs_atBot_atTop
  exact (tendsto_rpow_neg_atTop hN).comp h1

end

end L2C

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3E_Gam: `Γ` on vertical strips, and the Mellin inversion of `e^{-x}`

* `norm_Gamma_strip`: `‖Γ(s)‖ ≤ max(Γ(σ₀), 1) · 4 e^π (1+|t|)² e^{-π|t|/2}` on `σ₀ ≤ Re s ≤ 2`;
* `gamma_maj`: `‖Γ(s)‖ (2 + |t|)^A ≤ K ν₂(t)` on the same strip;
* `exp_neg_eq`: `e^{-x} = (2π)⁻¹ ∫ x^{-(2+iy)} Γ(2+iy) dy` for `x > 0`. -/

open Complex MeasureTheory Filter Topology Set

set_option autoImplicit false

namespace ArtinPrimitiveRoots

namespace L3E

noncomputable section

lemma norm_Gamma_one_add_le (t : ℝ) :
    ‖Gamma (1 + t * I)‖ ≤
      4 * Real.exp Real.pi * (1 + |t|) * Real.exp (-(Real.pi * |t| / 2)) := by
  have h := L3K.norm_Gamma_one_add_sq_le t
  have hpi := Real.pi_pos
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have hE : 1 ≤ Real.exp Real.pi := Real.one_le_exp hpi.le
  have ht : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hX0 : 0 ≤ 4 * Real.exp Real.pi * (1 + |t|) * Real.exp (-(Real.pi * |t| / 2)) := by
    positivity
  have hsq : (Real.exp (-(Real.pi * |t| / 2))) ^ 2 = Real.exp (-(Real.pi * |t|)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  refine le_of_pow_le_pow_left₀ two_ne_zero hX0 ?_
  refine h.trans ?_
  rw [mul_pow, hsq]
  have h0 : 0 ≤ Real.exp (-(Real.pi * |t|)) := (Real.exp_pos _).le
  have h1 : 4 * Real.pi * Real.exp Real.pi * (1 + |t|) ≤
      (4 * Real.exp Real.pi * (1 + |t|)) ^ 2 := by
    have e1 : 4 * Real.pi * Real.exp Real.pi * (1 + |t|) ≤
        16 * Real.exp Real.pi * (1 + |t|) := by
      have : 0 ≤ Real.exp Real.pi * (1 + |t|) := by positivity
      nlinarith
    have e2 : 16 * Real.exp Real.pi * (1 + |t|) ≤ (4 * Real.exp Real.pi * (1 + |t|)) ^ 2 := by
      have : 1 ≤ Real.exp Real.pi * (1 + |t|) := by nlinarith
      nlinarith
    linarith
  exact mul_le_mul_of_nonneg_right h1 h0

lemma norm_Gamma_two_add_le (t : ℝ) :
    ‖Gamma (2 + t * I)‖ ≤
      4 * Real.exp Real.pi * (1 + |t|) ^ 2 * Real.exp (-(Real.pi * |t| / 2)) := by
  have hne : (1 : ℂ) + t * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have h2 : (2 : ℂ) + t * I = (1 + t * I) + 1 := by ring
  rw [h2, Complex.Gamma_add_one _ hne, norm_mul]
  have hn : ‖(1 : ℂ) + t * I‖ ≤ 1 + |t| := by
    refine (norm_add_le _ _).trans ?_
    simp
  have hg := norm_Gamma_one_add_le t
  have h0 : 0 ≤ ‖Gamma (1 + t * I)‖ := norm_nonneg _
  calc ‖(1 : ℂ) + t * I‖ * ‖Gamma (1 + t * I)‖ ≤ (1 + |t|) * ‖Gamma (1 + t * I)‖ :=
        mul_le_mul_of_nonneg_right hn h0
    _ ≤ (1 + |t|) * (4 * Real.exp Real.pi * (1 + |t|) * Real.exp (-(Real.pi * |t| / 2))) :=
        mul_le_mul_of_nonneg_left hg (by positivity)
    _ = _ := by ring

/-- `Γ` on the strip `σ₀ ≤ Re s ≤ 2`. -/
lemma norm_Gamma_strip {σ0 : ℝ} (h0 : 0 < σ0) (_h2 : σ0 ≤ 2) (s : ℂ) (hs1 : σ0 ≤ s.re)
    (hs2 : s.re ≤ 2) :
    ‖Gamma s‖ ≤ max (Real.Gamma σ0) 1 *
      (4 * Real.exp Real.pi * (1 + |s.im|) ^ 2 * Real.exp (-(Real.pi * |s.im| / 2))) := by
  have hre : 0 < s.re := h0.trans_le hs1
  have hmono := L3K.norm_Gamma_mono hre hs2 s.im
  have hs : (s.re : ℂ) + s.im * I = s := Complex.re_add_im s
  rw [hs] at hmono
  have hG2 : ‖Gamma ((2 : ℝ) : ℂ)‖ = 1 := by
    rw [Complex.Gamma_ofReal, Real.Gamma_two]; simp
  have hGre : ‖Gamma ((s.re : ℝ) : ℂ)‖ = Real.Gamma s.re := by
    rw [Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.Gamma_pos_of_pos hre)]
  rw [hG2, mul_one, hGre] at hmono
  have hmax : Real.Gamma s.re ≤ max (Real.Gamma σ0) 1 := by
    have := Real.convexOn_Gamma.le_max_of_mem_Icc (x := σ0) (y := 2) (z := s.re)
      (mem_Ioi.2 h0) (mem_Ioi.2 (by norm_num)) ⟨hs1, hs2⟩
    rwa [Real.Gamma_two] at this
  have hb := norm_Gamma_two_add_le s.im
  have hpush : ((2 : ℝ) : ℂ) + s.im * I = 2 + s.im * I := by push_cast; ring
  rw [hpush] at hmono
  calc ‖Gamma s‖ ≤ ‖Gamma (2 + s.im * I)‖ * Real.Gamma s.re := hmono
    _ ≤ (4 * Real.exp Real.pi * (1 + |s.im|) ^ 2 * Real.exp (-(Real.pi * |s.im| / 2))) *
          max (Real.Gamma σ0) 1 :=
        mul_le_mul hb hmax (Real.Gamma_pos_of_pos hre).le (by positivity)
    _ = _ := by ring

/-- `(1 + x)^N e^{-πx/2} ≤ N^N` for `N ≥ 1`, `x ≥ 0`. -/
lemma poly_exp_le {N : ℝ} (hN : 1 ≤ N) {x : ℝ} (hx : 0 ≤ x) :
    (1 + x) ^ N * Real.exp (-(Real.pi * x / 2)) ≤ N ^ N := by
  have hN0 : 0 < N := by linarith
  have h1 : 1 + x ≤ N * Real.exp (x / N) := by
    have := Real.add_one_le_exp (x / N)
    have h2 : N * (x / N + 1) = x + N := by field_simp
    nlinarith
  have h2 : (1 + x) ^ N ≤ N ^ N * Real.exp x := by
    calc (1 + x) ^ N ≤ (N * Real.exp (x / N)) ^ N :=
          Real.rpow_le_rpow (by linarith) h1 hN0.le
      _ = N ^ N * Real.exp x := by
          rw [Real.mul_rpow hN0.le (Real.exp_pos _).le, ← Real.exp_mul, div_mul_cancel₀ _ hN0.ne']
  have h3 : Real.exp x * Real.exp (-(Real.pi * x / 2)) ≤ 1 := by
    rw [← Real.exp_add, Real.exp_le_one_iff]
    have := Real.pi_gt_three
    nlinarith
  calc (1 + x) ^ N * Real.exp (-(Real.pi * x / 2)) ≤
        (N ^ N * Real.exp x) * Real.exp (-(Real.pi * x / 2)) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = N ^ N * (Real.exp x * Real.exp (-(Real.pi * x / 2))) := by ring
    _ ≤ N ^ N * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = N ^ N := mul_one _

/-- The `Γ` majorant on the strip. -/
lemma gamma_maj {σ0 A : ℝ} (h0 : 0 < σ0) (h2 : σ0 ≤ 2) (hA : 0 ≤ A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, σ0 ≤ s.re → s.re ≤ 2 →
      ‖Gamma s‖ * (2 + |s.im|) ^ A ≤ K * L2C.nu 2 s.im := by
  set M := max (Real.Gamma σ0) 1
  have hM : 0 ≤ M := le_max_of_le_right zero_le_one
  refine ⟨M * (4 * Real.exp Real.pi) * 2 ^ A * (A + 4) ^ (A + 4), by positivity, ?_⟩
  intro s hs1 hs2
  set t := s.im
  have hG := norm_Gamma_strip h0 h2 s hs1 hs2
  have hu : 0 < 1 + |t| := by positivity
  have hpoly : (2 + |t|) ^ A ≤ 2 ^ A * (1 + |t|) ^ A := by
    rw [← Real.mul_rpow (by norm_num) hu.le]
    exact Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg t]) hA
  have hpe := poly_exp_le (N := A + 4) (by linarith) (abs_nonneg t)
  have hsplit : (1 + |t|) ^ 2 * (1 + |t|) ^ A =
      (1 + |t|) ^ (A + 4) * L2C.nu 2 t := by
    unfold L2C.nu
    rw [← Real.rpow_add hu, show A + 4 + -2 = A + 2 by ring, Real.rpow_add hu,
      show ((1 + |t|) ^ (2 : ℝ)) = (1 + |t|) ^ (2 : ℕ) by norm_cast]
    ring
  have hnu : 0 ≤ L2C.nu 2 t := L2C.nu_nonneg 2 t
  calc ‖Gamma s‖ * (2 + |t|) ^ A ≤
        (M * (4 * Real.exp Real.pi * (1 + |t|) ^ 2 * Real.exp (-(Real.pi * |t| / 2)))) *
          (2 ^ A * (1 + |t|) ^ A) :=
        mul_le_mul hG hpoly (by positivity) (by positivity)
    _ = M * (4 * Real.exp Real.pi) * 2 ^ A *
          (((1 + |t|) ^ 2 * (1 + |t|) ^ A) * Real.exp (-(Real.pi * |t| / 2))) := by ring
    _ = M * (4 * Real.exp Real.pi) * 2 ^ A *
          (((1 + |t|) ^ (A + 4) * Real.exp (-(Real.pi * |t| / 2))) * L2C.nu 2 t) := by
        rw [hsplit]; ring
    _ ≤ M * (4 * Real.exp Real.pi) * 2 ^ A * ((A + 4) ^ (A + 4) * L2C.nu 2 t) := by
        gcongr
    _ = _ := by ring

lemma differentiableAt_Gamma_of_re_pos {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Gamma s := by
  refine Complex.differentiableAt_Gamma _ fun m h => ?_
  have := congrArg Complex.re h
  simp at this
  linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]

lemma continuous_Gamma_line {c : ℝ} (hc : 0 < c) : Continuous fun y : ℝ => Gamma (c + y * I) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  exact (differentiableAt_Gamma_of_re_pos (by simpa using hc)).continuousAt.comp (by fun_prop)

lemma integrable_Gamma_two : Integrable fun y : ℝ => Gamma (2 + y * I) := by
  obtain ⟨K, -, hK⟩ := gamma_maj (σ0 := 2) (A := 0) (by norm_num) le_rfl le_rfl
  refine ((L2C.integrable_nu (N := 2) (by norm_num)).const_mul K).mono' ?_ ?_
  · exact_mod_cast (continuous_Gamma_line (c := 2) (by norm_num)).aestronglyMeasurable
  · refine Eventually.of_forall fun y => ?_
    have := hK (2 + y * I) (by simp) (by simp)
    simpa using this

/-- Mellin inversion of `e^{-x}` on the line `Re s = 2`. -/
theorem exp_neg_eq {x : ℝ} (hx : 0 < x) :
    ((Real.exp (-x) : ℝ) : ℂ) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ y : ℝ, (x : ℂ) ^ (-(2 + y * I)) * Gamma (2 + y * I) := by
  have hconv : MellinConvergent (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) (2 : ℝ) := by
    have h := Complex.GammaIntegral_convergent (s := ((2 : ℝ) : ℂ)) (by simp)
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [smul_eq_mul, Complex.ofReal_exp, Complex.ofReal_neg]
    ring
  have hG : ∀ y : ℝ, mellin (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) ((2 : ℝ) + y * I) =
      Gamma (2 + y * I) := by
    intro y
    rw [← GammaIntegral_eq_mellin, ← Complex.Gamma_eq_integral (by simp)]
    push_cast; ring_nf
  have hvert : VerticalIntegrable (mellin (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ))) (2 : ℝ) := by
    unfold VerticalIntegrable
    simp_rw [hG]
    exact integrable_Gamma_two
  have hcont : ContinuousAt (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) x := by fun_prop
  have h := mellinInv_mellin_eq (2 : ℝ) (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) hx hconv hvert hcont
  rw [← h, mellinInv]
  simp_rw [hG, smul_eq_mul]
  rw [Complex.real_smul]
  push_cast
  ring

end

end L3E

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3P_Shift: one-variable contour shifts of vertical line integrals

* `C3P_shift`: no pole, with a decaying integrable majorant `g (Im s)` on the strip;
* `C3P_shift_pole`: one simple pole `p` inside the strip, `f = A / (s - p)`; the majorant is only
  required on the two lines and for `|Im s| ≥ 1`.

The pole computation follows `OAI.SevenEighths.PrincipalMellinResidues.verticalIntegral_simple_pole`
(copied and adapted). -/

set_option maxHeartbeats 1000000

open Complex MeasureTheory Filter Topology Set

namespace ArtinPrimitiveRoots

namespace C3P

lemma integrable_line_of_le {f : ℂ → ℂ} {g : ℝ → ℝ} {c : ℝ}
    (hc : ContinuousOn f {s | s.re = c}) (hg : Integrable g)
    (hb : ∀ t : ℝ, ‖f (c + t * I)‖ ≤ g t) :
    Integrable fun t : ℝ => f (c + t * I) := by
  refine hg.mono' ?_ (Eventually.of_forall hb)
  refine (hc.comp_continuous (by fun_prop) fun t => ?_).aestronglyMeasurable
  simp

lemma horizontal_tendsto {f : ℂ → ℂ} {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : Tendsto g atTop (𝓝 0)) (hb : ∀ x T : ℝ, a ≤ x → x ≤ b → 1 ≤ T → ‖f (x + T * I)‖ ≤ g T) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, f (x + T * I)) atTop (𝓝 0) := by
  have hexp : Tendsto (fun T : ℝ => g T * |b - a|) atTop (𝓝 0) := by
    simpa using hg.mul_const |b - a|
  refine squeeze_zero_norm' ?_ hexp
  filter_upwards [eventually_ge_atTop 1] with T hT
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
  rw [Set.uIoc_of_le hab] at hx
  exact hb x T hx.1.le hx.2 hT

lemma horizontal_tendsto_neg {f : ℂ → ℂ} {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : Tendsto g atBot (𝓝 0))
    (hb : ∀ x T : ℝ, a ≤ x → x ≤ b → T ≤ -1 → ‖f (x + T * I)‖ ≤ g T) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, f (x + (-T) * I)) atTop (𝓝 0) := by
  have hg' : Tendsto (fun T : ℝ => g (-T)) atTop (𝓝 0) := hg.comp tendsto_neg_atTop_atBot
  have hexp : Tendsto (fun T : ℝ => g (-T) * |b - a|) atTop (𝓝 0) := by
    simpa using hg'.mul_const |b - a|
  refine squeeze_zero_norm' ?_ hexp
  filter_upwards [eventually_ge_atTop 1] with T hT
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
  rw [Set.uIoc_of_le hab] at hx
  have := hb x (-T) hx.1.le hx.2 (by linarith)
  simpa using this

/-- Shifting a vertical line integral across a strip on which `f` is holomorphic, given an
integrable majorant `g (Im s)` tending to `0` at `±∞`. -/
theorem C3P_shift {f : ℂ → ℂ} {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : DifferentiableOn ℂ f {s | a ≤ s.re ∧ s.re ≤ b})
    (hg : Integrable g) (hgt : Tendsto g atTop (𝓝 0)) (hgb : Tendsto g atBot (𝓝 0))
    (hb : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖f s‖ ≤ g s.im) :
    ∫ t : ℝ, f (a + t * I) = ∫ t : ℝ, f (b + t * I) := by
  have hc : ∀ c, a ≤ c → c ≤ b → ContinuousOn f {s | s.re = c} := fun c h1 h2 =>
    hf.continuousOn.mono fun s hs => by simp only [Set.mem_ofPred_eq] at hs ⊢; constructor <;> linarith
  have hia := integrable_line_of_le (hc a le_rfl hab) hg fun t => by
    simpa using hb (a + t * I) (by simp) (by simp [hab])
  have hib := integrable_line_of_le (hc b hab le_rfl) hg fun t => by
    simpa using hb (b + t * I) (by simp [hab]) (by simp)
  have hrect : ∀ T : ℝ, (∫ x : ℝ in a..b, f (x + (-T) * I)) - (∫ x : ℝ in a..b, f (x + T * I)) +
      I • (∫ y : ℝ in -T..T, f (b + y * I)) - I • (∫ y : ℝ in -T..T, f (a + y * I)) = 0 := by
    intro T
    have := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨a, -T⟩ ⟨b, T⟩
      (hf.mono fun z hz => by
        rw [mem_reProdIm, Set.uIcc_of_le hab] at hz
        exact ⟨hz.1.1, hz.1.2⟩)
    simpa using this
  have hup := horizontal_tendsto (f := f) hab hgt fun x T h1 h2 _ => by
    simpa using hb (x + T * I) (by simpa using h1) (by simpa using h2)
  have hlow := horizontal_tendsto_neg (f := f) hab hgb fun x T h1 h2 _ => by
    simpa using hb (x + T * I) (by simpa using h1) (by simpa using h2)
  have hva : Tendsto (fun T : ℝ => ∫ y : ℝ in -T..T, f (a + y * I)) atTop
      (𝓝 (∫ τ : ℝ, f (a + τ * I))) :=
    intervalIntegral_tendsto_integral hia tendsto_neg_atTop_atBot tendsto_id
  have hvb : Tendsto (fun T : ℝ => ∫ y : ℝ in -T..T, f (b + y * I)) atTop
      (𝓝 (∫ τ : ℝ, f (b + τ * I))) :=
    intervalIntegral_tendsto_integral hib tendsto_neg_atTop_atBot tendsto_id
  have h1 := ((hlow.sub hup).add ((hvb.const_smul I).sub (hva.const_smul I)))
  have h2 : Tendsto (fun T : ℝ => (0 : ℂ)) atTop
      (𝓝 ((0 - 0) + ((I • ∫ τ : ℝ, f (b + τ * I)) - I • ∫ τ : ℝ, f (a + τ * I)))) := by
    refine h1.congr fun T => ?_
    rw [← hrect T]
    ring
  have h3 := tendsto_nhds_unique tendsto_const_nhds h2
  simp only [sub_self, zero_add, smul_eq_mul] at h3
  rw [← mul_sub, eq_comm, mul_eq_zero, sub_eq_zero] at h3
  exact (h3.resolve_left I_ne_zero).symm

/-! ### A simple pole -/

end C3P

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

/-! ### The Dirichlet series as a sum over ideals -/

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

end T12B

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3E_Smooth: smoothed sums over ideals from an entire continuation

`smooth_bound`: if `‖a(I)‖ ≤ 1`, `a(⊥) = 0`, and `Σ a(I) N I^{-w}` (on `Re w = 2`) continues to an
entire `Φ` with `‖Φ(w)‖ ≤ B (2 + |Im w|)^A` on `σ₀ ≤ Re w ≤ 2`, then
`‖Σ a(I) e^{-N I / D}‖ ≤ K B D^{σ₀}` with `K` depending only on `σ₀, A`
(Mellin inversion of `e^{-x}`, Fubini, and a contour shift from `Re w = 2` to `Re w = σ₀`).
Also `tsum_exp_le`: `Σ_I e^{-N I/D} ≤ 1 + 2 D^σ Σ_I N I^{-σ}` for `1 < σ ≤ 2`. -/

open Complex MeasureTheory Filter Topology Set NumberField

set_option autoImplicit false

namespace ArtinPrimitiveRoots

namespace L3E

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

instance countable_ideal : Countable (Ideal (𝓞 F)) :=
  (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)).symm.injective.countable

lemma cpow_div (N : ℝ) (hN : 0 ≤ N) {D : ℝ} (hD : 0 < D) (s : ℂ) :
    (((N / D : ℝ)) : ℂ) ^ (-s) = (N : ℂ) ^ (-s) * (D : ℂ) ^ s := by
  rw [div_eq_mul_inv, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hN (inv_nonneg.2 hD.le), Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hD.le]; exact Real.pi_ne_zero.symm),
    Complex.cpow_neg (D : ℂ) s, inv_inv]

lemma integrable_kernel {x : ℝ} (hx : 0 < x) :
    Integrable fun y : ℝ => (x : ℂ) ^ (-(2 + y * I)) * Gamma (2 + y * I) := by
  refine (integrable_Gamma_two.norm.const_mul (x ^ (-2 : ℝ))).mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    refine Continuous.mul ?_ ?_
    · exact Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hx.ne'))
    · exact_mod_cast continuous_Gamma_line (c := 2) (by norm_num)
  · refine Eventually.of_forall fun y => ?_
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp

lemma term_eq (c : ℂ) {N D : ℝ} (hN : 0 < N) (hD : 0 < D) :
    c * ((Real.exp (-(N / D)) : ℝ) : ℂ) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ y : ℝ, c * (((N / D : ℝ)) : ℂ) ^ (-(2 + y * I)) * Gamma (2 + y * I) := by
  rw [exp_neg_eq (div_pos hN hD)]
  simp_rw [mul_assoc c]
  rw [integral_const_mul]; ring

lemma rpow_le_max {D σ0 x : ℝ} (hD : 0 < D) (h1 : σ0 ≤ x) (h2 : x ≤ 2) :
    D ^ x ≤ max (D ^ σ0) (D ^ (2 : ℝ)) := by
  rcases le_or_gt 1 D with h | h
  · exact le_max_of_le_right (Real.rpow_le_rpow_of_exponent_le h h2)
  · exact le_max_of_le_left (Real.rpow_le_rpow_of_exponent_ge hD h.le h1)

/-- **The smoothed-sum bound.** -/
theorem smooth_bound {σ0 A : ℝ} (h0 : 0 < σ0) (h2 : σ0 ≤ 2) (hA : 0 ≤ A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (a : Ideal (𝓞 F) → ℂ), (∀ J, ‖a J‖ ≤ 1) → a ⊥ = 0 →
      ∀ (Φ : ℂ → ℂ) (B : ℝ), Differentiable ℂ Φ →
        (∀ w : ℂ, w.re = 2 → Φ w = ∑' J, a J * (Ideal.absNorm J : ℂ) ^ (-w)) →
        (∀ w : ℂ, σ0 ≤ w.re → w.re ≤ 2 → ‖Φ w‖ ≤ B * (2 + |w.im|) ^ A) →
        ∀ D : ℝ, 0 < D →
          ‖∑' J, a J * ((Real.exp (-((Ideal.absNorm J : ℝ) / D)) : ℝ) : ℂ)‖ ≤
            K * B * D ^ σ0 := by
  obtain ⟨Kg, hKg0, hKg⟩ := gamma_maj h0 h2 hA
  set Inu := ∫ t : ℝ, L2C.nu 2 t
  have hInu : 0 ≤ Inu := integral_nonneg fun t => L2C.nu_nonneg 2 t
  have hpi : 0 < Real.pi := Real.pi_pos
  refine ⟨1 / (2 * Real.pi) * Kg * Inu, by positivity, ?_⟩
  intro a ha ha0 Φ B hΦ hΦeq hΦb D hD
  have hB0 : 0 ≤ B := by
    have h1 := (norm_nonneg _).trans (hΦb σ0 (by simp) (by simpa using h2))
    have hp : 0 < (2 + |((σ0 : ℂ)).im|) ^ A := by positivity
    by_contra hc
    push Not at hc
    nlinarith
  set c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  set G : Ideal (𝓞 F) → ℝ → ℂ := fun J y =>
    a J * (((Ideal.absNorm J : ℝ) / D : ℝ) : ℂ) ^ (-(2 + y * I)) * Gamma (2 + y * I) with hGdef
  have hG0 : ∀ J, Ideal.absNorm J = 0 → G J = 0 := by
    intro J hJ
    have hJb : J = ⊥ := Ideal.absNorm_eq_zero_iff.1 hJ
    funext y
    simp [hGdef, hJb, ha0]
  have hterm : ∀ J, a J * ((Real.exp (-((Ideal.absNorm J : ℝ) / D)) : ℝ) : ℂ) =
      c * ∫ y, G J y := by
    intro J
    by_cases hJ : Ideal.absNorm J = 0
    · rw [hG0 J hJ, Ideal.absNorm_eq_zero_iff.1 hJ, ha0]; simp
    · exact term_eq (a J) (by exact_mod_cast Nat.pos_of_ne_zero hJ) hD
  have hint : ∀ J, Integrable (G J) := by
    intro J
    by_cases hJ : Ideal.absNorm J = 0
    · rw [hG0 J hJ]; exact integrable_zero _ _ _
    · have hx : (0 : ℝ) < (Ideal.absNorm J : ℝ) / D :=
        div_pos (by exact_mod_cast Nat.pos_of_ne_zero hJ) hD
      refine ((integrable_kernel hx).const_mul (a J)).congr (Eventually.of_forall fun y => ?_)
      simp only [hGdef]; ring
  set Ig := ∫ y : ℝ, ‖Gamma (2 + y * I)‖
  have hIg : 0 ≤ Ig := integral_nonneg fun y => norm_nonneg _
  have hbound : ∀ J, ∫ y, ‖G J y‖ ≤ D ^ (2 : ℝ) * Ig *
      ((Ideal.absNorm J : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
    intro J
    by_cases hJ : Ideal.absNorm J = 0
    · rw [hG0 J hJ, hJ]; simp [Real.zero_rpow (by norm_num : (-(2 : ℝ)) ≠ 0)]
    · have hN : (0 : ℝ) < (Ideal.absNorm J : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hJ
      have hx : (0 : ℝ) < (Ideal.absNorm J : ℝ) / D := div_pos hN hD
      have hpt : ∀ y : ℝ, ‖G J y‖ ≤ ((Ideal.absNorm J : ℝ) / D) ^ (-(2 : ℝ)) *
          ‖Gamma (2 + y * I)‖ := by
        intro y
        simp only [hGdef, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
        have : (-(2 + (y : ℂ) * I)).re = -2 := by simp
        rw [this]
        have hp : 0 ≤ ((Ideal.absNorm J : ℝ) / D) ^ (-(2 : ℝ)) * ‖Gamma (2 + y * I)‖ := by
          positivity
        calc ‖a J‖ * ((Ideal.absNorm J : ℝ) / D) ^ (-2 : ℝ) * ‖Gamma (2 + y * I)‖ =
              ‖a J‖ * (((Ideal.absNorm J : ℝ) / D) ^ (-(2 : ℝ)) * ‖Gamma (2 + y * I)‖) := by
                rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num]; ring
          _ ≤ 1 * (((Ideal.absNorm J : ℝ) / D) ^ (-(2 : ℝ)) * ‖Gamma (2 + y * I)‖) :=
              mul_le_mul_of_nonneg_right (ha J) hp
          _ = _ := one_mul _
      have hmono := integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg (G J y))
        (integrable_Gamma_two.norm.const_mul (((Ideal.absNorm J : ℝ) / D) ^ (-(2 : ℝ))))
        (Eventually.of_forall hpt)
      rw [integral_const_mul] at hmono
      refine hmono.trans (le_of_eq ?_)
      rw [Real.div_rpow hN.le hD.le, Real.rpow_neg hD.le, div_inv_eq_mul]
      ring
  have hsum : Summable fun J => ∫ y, ‖G J y‖ :=
    Summable.of_nonneg_of_le (fun J => integral_nonneg fun y => norm_nonneg _) hbound
      ((T12B.summable_absNorm_rpow (F := F) (σ := 2) (by norm_num)).mul_left _)
  have hfub := integral_tsum_of_summable_integral_norm hint hsum
  set f : ℂ → ℂ := fun s => Φ s * ((D : ℂ) ^ s * Gamma s) with hfdef
  have hpt : ∀ y : ℝ, ∑' J, G J y = f ((2 : ℝ) + y * I) := by
    intro y
    have hs : ((2 : ℝ) : ℂ) + y * I = 2 + y * I := by push_cast; ring
    rw [hs]
    have hre : (2 + (y : ℂ) * I).re = 2 := by simp
    simp only [hGdef, hfdef, hΦeq _ hre]
    rw [← tsum_mul_right]
    refine tsum_congr fun J => ?_
    rw [cpow_div _ (Nat.cast_nonneg _) hD, Complex.ofReal_natCast]
    ring
  have hmain : ∑' J, a J * ((Real.exp (-((Ideal.absNorm J : ℝ) / D)) : ℝ) : ℂ) =
      c * ∫ y : ℝ, f ((2 : ℝ) + y * I) := by
    rw [tsum_congr hterm, tsum_mul_left, hfub]
    congr 1
    exact integral_congr_ae (Eventually.of_forall hpt)
  -- the shift
  set Mx := max (D ^ σ0) (D ^ (2 : ℝ))
  have hMx : 0 ≤ Mx := le_max_of_le_left (Real.rpow_nonneg hD.le _)
  set gf : ℝ → ℝ := fun t => B * Kg * Mx * L2C.nu 2 t
  have hfd : DifferentiableOn ℂ f {s | σ0 ≤ s.re ∧ s.re ≤ 2} := by
    intro s hs
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (hΦ s).mul (DifferentiableAt.mul ?_ (differentiableAt_Gamma_of_re_pos ?_))
    · exact differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast hD.ne'))
    · exact h0.trans_le hs.1
  have hgi : Integrable gf := (L2C.integrable_nu (by norm_num)).const_mul _
  have hgt : Tendsto gf atTop (𝓝 0) := by
    simpa [gf] using (L2C.tendsto_nu_atTop (N := 2) (by norm_num)).const_mul (B * Kg * Mx)
  have hgb : Tendsto gf atBot (𝓝 0) := by
    simpa [gf] using (L2C.tendsto_nu_atBot (N := 2) (by norm_num)).const_mul (B * Kg * Mx)
  have hnf : ∀ s : ℂ, ‖f s‖ = ‖Φ s‖ * (D ^ s.re * ‖Gamma s‖) := by
    intro s
    simp only [hfdef, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hD]
  have hb : ∀ s : ℂ, σ0 ≤ s.re → s.re ≤ 2 → ‖f s‖ ≤ gf s.im := by
    intro s hs1 hs2
    rw [hnf]
    have h1 := hΦb s hs1 hs2
    have h3 := hKg s hs1 hs2
    have h4 := rpow_le_max (σ0 := σ0) hD hs1 hs2
    calc ‖Φ s‖ * (D ^ s.re * ‖Gamma s‖) ≤ (B * (2 + |s.im|) ^ A) * (Mx * ‖Gamma s‖) :=
          mul_le_mul h1 (mul_le_mul_of_nonneg_right h4 (norm_nonneg _)) (by positivity)
            (by positivity)
      _ = B * Mx * (‖Gamma s‖ * (2 + |s.im|) ^ A) := by ring
      _ ≤ B * Mx * (Kg * L2C.nu 2 s.im) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = gf s.im := by simp only [gf]; ring
  have hshift := C3P.C3P_shift h2 hfd hgi hgt hgb hb
  rw [hmain, ← hshift, norm_mul]
  have hc : ‖c‖ = 1 / (2 * Real.pi) := by
    simp only [c, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (by positivity)
  rw [hc]
  have hgi' : Integrable fun t : ℝ => D ^ σ0 * B * Kg * L2C.nu 2 t :=
    (L2C.integrable_nu (by norm_num)).const_mul _
  have hle := norm_integral_le_of_norm_le hgi' (Eventually.of_forall fun t => by
    have hre : ((σ0 : ℂ) + t * I).re = σ0 := by simp
    have him : ((σ0 : ℂ) + t * I).im = t := by simp
    rw [hnf, hre]
    have h1 := hΦb ((σ0 : ℂ) + t * I) (by rw [hre]) (by rw [hre]; exact h2)
    have h3 := hKg ((σ0 : ℂ) + t * I) (by rw [hre]) (by rw [hre]; exact h2)
    rw [him] at h1 h3
    calc ‖Φ (σ0 + t * I)‖ * (D ^ σ0 * ‖Gamma (σ0 + t * I)‖) ≤
          (B * (2 + |t|) ^ A) * (D ^ σ0 * ‖Gamma (σ0 + t * I)‖) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = D ^ σ0 * B * (‖Gamma (σ0 + t * I)‖ * (2 + |t|) ^ A) := by ring
      _ ≤ D ^ σ0 * B * (Kg * L2C.nu 2 t) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = D ^ σ0 * B * Kg * L2C.nu 2 t := by ring)
  rw [integral_const_mul] at hle
  calc 1 / (2 * Real.pi) * ‖∫ t : ℝ, f (σ0 + t * I)‖ ≤
        1 / (2 * Real.pi) * (D ^ σ0 * B * Kg * Inu) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 1 / (2 * Real.pi) * Kg * Inu * B * D ^ σ0 := by ring

/-- `e^{-x} ≤ 2 x^{-σ}` for `x > 0`, `0 ≤ σ ≤ 2`. -/
lemma exp_neg_le_rpow {x σ : ℝ} (hx : 0 < x) (hσ0 : 0 ≤ σ) (hσ2 : σ ≤ 2) :
    Real.exp (-x) ≤ 2 * x ^ (-σ) := by
  rw [Real.rpow_neg hx.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hx σ)]
  rcases le_or_gt x 1 with h | h
  · have h1 : x ^ σ ≤ 1 := Real.rpow_le_one hx.le h hσ0
    have h2 : Real.exp (-x) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    nlinarith [Real.exp_pos (-x), Real.rpow_nonneg hx.le σ]
  · have h1 : x ^ σ ≤ x ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h.le hσ2
    have h1' : x ^ (2 : ℝ) = x ^ 2 := by norm_cast
    have h3 : x ^ 2 * Real.exp (-x) ≤ 2 := by
      have he : x ^ 2 / 2 ≤ Real.exp x := by
        have := Real.pow_div_factorial_le_exp x hx.le 2
        simpa using this
      have hpos := Real.exp_pos x
      have hinv : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-x)]
    rw [h1'] at h1
    nlinarith [Real.exp_pos (-x)]

/-- **The diagonal sum.** -/
theorem tsum_exp_le {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) {D : ℝ} (hD : 0 < D) :
    Summable (fun J : Ideal (𝓞 F) => Real.exp (-((Ideal.absNorm J : ℝ) / D))) ∧
    ∑' J : Ideal (𝓞 F), Real.exp (-((Ideal.absNorm J : ℝ) / D)) ≤
      1 + 2 * D ^ σ * ∑' J : Ideal (𝓞 F), ((Ideal.absNorm J : ℕ) : ℝ) ^ (-σ) := by
  classical
  have hs := T12B.summable_absNorm_rpow (F := F) hσ1
  set u : Ideal (𝓞 F) → ℝ := fun J =>
    (if J = ⊥ then 1 else 0) + 2 * D ^ σ * ((Ideal.absNorm J : ℕ) : ℝ) ^ (-σ) with hu
  have hus : Summable u := by
    refine Summable.add ?_ (hs.mul_left _)
    exact (hasSum_ite_eq (⊥ : Ideal (𝓞 F)) (1 : ℝ)).summable
  have hle : ∀ J : Ideal (𝓞 F), Real.exp (-((Ideal.absNorm J : ℝ) / D)) ≤ u J := by
    intro J
    by_cases hJ : J = ⊥
    · subst hJ
      simp [hu, Real.zero_rpow (by linarith : (-σ) ≠ 0)]
    · have hN : (0 : ℝ) < (Ideal.absNorm J : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
      have h := exp_neg_le_rpow (div_pos hN hD) (by linarith) hσ2
      rw [Real.div_rpow hN.le hD.le, Real.rpow_neg hD.le, div_inv_eq_mul] at h
      simp only [hu, if_neg hJ, zero_add]
      calc Real.exp (-((Ideal.absNorm J : ℝ) / D)) ≤
            2 * ((Ideal.absNorm J : ℝ) ^ (-σ) * D ^ σ) := h
        _ = _ := by ring
  have hes : Summable (fun J : Ideal (𝓞 F) => Real.exp (-((Ideal.absNorm J : ℝ) / D))) :=
    Summable.of_nonneg_of_le (fun J => (Real.exp_pos _).le) hle hus
  refine ⟨hes, (hes.tsum_le_tsum hle hus).trans (le_of_eq ?_)⟩
  have h1 : Summable (fun J : Ideal (𝓞 F) => if J = ⊥ then (1 : ℝ) else 0) :=
    (hasSum_ite_eq (⊥ : Ideal (𝓞 F)) (1 : ℝ)).summable
  rw [hu, Summable.tsum_add h1 (hs.mul_left _), tsum_ite_eq, tsum_mul_left]

end

end L3E

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3E_Pair: the off-diagonal smoothed sum

For exterior squarefree `𝔠₁ ≠ 𝔠₂` and the coefficient
`a(𝔡) = 1[𝔡 exterior] χ_𝔡(g𝔠₁)³ conj χ_𝔡(g𝔠₂)³`, given KummerConvexity in the form `hL`:
`‖Σ_𝔡 a(𝔡) e^{-N𝔡/D}‖ ≤ K C_L ((N𝔠₁ N𝔠₂)³)^{1/2+δ} N𝔠₁ D^{3/1000}`.
The Dirichlet series of `a` is `kummerL(u) ∏_{P ∈ T}(1 − χ_P(u) N P^{-w})` (T12B.sieve). -/

open Complex NumberField IsDedekindDomain UniqueFactorizationMonoid

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinPrimitiveRoots

namespace L3E

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

lemma norm_sextic_le (P : Ideal (𝓞 F)) (x : SInt 𝔪) : ‖sexticResidueSymbol ι 𝔪 P x‖ ≤ 1 := by
  unfold sexticResidueSymbol
  split_ifs with h1 h2
  · simp
  · have h6 : (ι (h2.choose : F)) ^ 6 = 1 := by
      rw [← map_pow, ← map_pow]
      have := h2.choose_spec.1
      rw [this]
      simp
    rw [Complex.norm_eq_one_of_pow_eq_one h6 (by norm_num)]
  · simp

lemma norm_rs_le (𝔞 : Ideal (𝓞 F)) (x : SInt 𝔪) : ‖residueSymbol ι 𝔪 𝔞 x‖ ≤ 1 := by
  unfold residueSymbol
  induction (normalizedFactors 𝔞) using Multiset.induction_on with
  | empty => simp
  | cons P s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    exact mul_le_one₀ (norm_sextic_le P x) (norm_nonneg _) ih

open Classical in
/-- `χ_I(u)` on exterior `I`, `0` elsewhere. -/
noncomputable def gK (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (u : SInt 𝔪) (I : Ideal (𝓞 F)) : ℂ :=
  if IsExterior 𝔪 I then residueSymbol ι 𝔪 I u else 0

lemma norm_gK_le (u : SInt 𝔪) (I : Ideal (𝓞 F)) : ‖gK ι 𝔪 u I‖ ≤ 1 := by
  unfold gK; split_ifs
  · exact norm_rs_le I u
  · simp

lemma isExterior_mul_iff' {I J : Ideal (𝓞 F)} :
    IsExterior 𝔪 (I * J) ↔ IsExterior 𝔪 I ∧ IsExterior 𝔪 J := by
  refine ⟨fun h => ⟨C3M.isExterior_of_mul_left h, C3M.isExterior_of_mul_right h⟩,
    fun h => isExterior_mul h.1 h.2⟩

lemma rs_mul_ideal (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 (I * J) x = residueSymbol ι 𝔪 I x * residueSymbol ι 𝔪 J x := by
  unfold residueSymbol
  rw [normalizedFactors_mul hI hJ, Multiset.map_add, Multiset.prod_add]

lemma gK_mul (u : SInt 𝔪) (I J : Ideal (𝓞 F)) : gK ι 𝔪 u (I * J) = gK ι 𝔪 u I * gK ι 𝔪 u J := by
  classical
  unfold gK
  by_cases hI : IsExterior 𝔪 I <;> by_cases hJ : IsExterior 𝔪 J
  · rw [if_pos (isExterior_mul_iff'.2 ⟨hI, hJ⟩), if_pos hI, if_pos hJ,
      rs_mul_ideal I J hI.1 hJ.1]
  · rw [if_neg (fun h => hJ (isExterior_mul_iff'.1 h).2), if_neg hJ, mul_zero]
  · rw [if_neg (fun h => hI (isExterior_mul_iff'.1 h).1), if_neg hI, zero_mul]
  · rw [if_neg (fun h => hI (isExterior_mul_iff'.1 h).1), if_neg hI, zero_mul]

lemma kummerL_eq_tsum' (u : SInt 𝔪) (s : ℂ) :
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

lemma norm_natCast_cpow_le (n : ℕ) {w : ℂ} (hw : 0 < w.re) :
    ‖(n : ℂ) ^ (-w)‖ ≤ (n : ℝ) ^ (-w.re) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    have hw0 : -w ≠ 0 := fun h0 => by
      have := congrArg Complex.re h0; simp at this; linarith
    simp [Complex.zero_cpow hw0, Real.zero_rpow (by linarith : (-w.re) ≠ 0)]
  · rw [Complex.norm_natCast_cpow_of_pos h]; simp

lemma natCast_cpow_mul (m n : ℕ) (s : ℂ) :
    ((m * n : ℕ) : ℂ) ^ s = (m : ℂ) ^ s * (n : ℂ) ^ s := by
  rw [Nat.cast_mul]
  exact (Complex.natCast_mul_natCast_cpow m n s).symm.symm

open Classical in
/-- The off-diagonal coefficient. -/
noncomputable def acoef (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (g : AllowedGen ι 𝔪)
    (𝔠₁ 𝔠₂ : Ideal (𝓞 F)) (𝔡 : Ideal (𝓞 F)) : ℂ :=
  if IsExterior 𝔪 𝔡 then
    residueSymbol ι 𝔪 𝔡 (g.gen 𝔠₁) ^ 3 * starRingEnd ℂ (residueSymbol ι 𝔪 𝔡 (g.gen 𝔠₂) ^ 3)
  else 0

lemma norm_acoef_le (g : AllowedGen ι 𝔪) (𝔠₁ 𝔠₂ 𝔡 : Ideal (𝓞 F)) :
    ‖acoef ι 𝔪 g 𝔠₁ 𝔠₂ 𝔡‖ ≤ 1 := by
  unfold acoef; split_ifs
  · rw [norm_mul, norm_pow, Complex.norm_conj, norm_pow]
    have h1 := norm_rs_le (ι := ι) 𝔡 (g.gen 𝔠₁)
    have h2 := norm_rs_le (ι := ι) 𝔡 (g.gen 𝔠₂)
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) h1) (by positivity)
      (pow_le_one₀ (norm_nonneg _) h2)
  · simp

/-- **The off-diagonal bound.** -/
theorem pair_bound (hχ : C3M.HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {A Cl δ : ℝ} (hA : 0 ≤ A)
    (hδ : 0 < δ)
    (hL : ∀ r : FreqClass 𝔪, r ≠ principalFreq 𝔪 → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
          (∀ w : ℂ, 1 < w.re → Λ w = kummerL ι 𝔪 (freqElt g r) w) ∧
          ∀ w : ℂ, 3 / 1000 ≤ w.re → w.re ≤ 4 →
            ‖Λ w‖ ≤ Cl * (Ideal.absNorm r.1.1 : ℝ) ^ (1 / 2 + δ) * (2 + |w.im|) ^ A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ 𝔠₁ 𝔠₂ : Ideal (𝓞 F), IsExterior 𝔪 𝔠₁ → IsExterior 𝔪 𝔠₂ →
      Squarefree 𝔠₁ → Squarefree 𝔠₂ → 𝔠₁ ≠ 𝔠₂ → ∀ D : ℝ, 0 < D →
        ‖∑' 𝔡, acoef ι 𝔪 g 𝔠₁ 𝔠₂ 𝔡 * ((Real.exp (-((Ideal.absNorm 𝔡 : ℝ) / D)) : ℝ) : ℂ)‖ ≤
          K * (Cl * (((Ideal.absNorm 𝔠₁ : ℝ) * Ideal.absNorm 𝔠₂) ^ 3) ^ (1 / 2 + δ) *
            Ideal.absNorm 𝔠₁) * D ^ (3 / 1000 : ℝ) := by
  classical
  obtain ⟨K, hK0, hK⟩ := smooth_bound (F := F) (σ0 := 3 / 1000) (A := A) (by norm_num)
    (by norm_num) hA
  refine ⟨K, hK0, ?_⟩
  intro 𝔠₁ 𝔠₂ h₁ h₂ s₁ s₂ hne D hD
  obtain ⟨r, T, hr, hNr, hTc, hTp, hcoef⟩ := offdiag hχ g h₁ h₂ s₁ s₂ hne
  obtain ⟨Λ, hΛd, hΛeq, hΛb⟩ := hL r hr
  set u := freqElt g r
  set E : ℂ → ℂ := fun w => ∏ P ∈ T, (1 - gK ι 𝔪 u P * (Ideal.absNorm P : ℂ) ^ (-w)) with hE
  have hNP : ∀ P ∈ T, 0 < Ideal.absNorm P := fun P hP =>
    Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact (hTp P hP).2.1)
  have hEd : Differentiable ℂ E := by
    refine Differentiable.fun_finsetProd (𝕜 := ℂ) fun P hP => ?_
    have hP0 : (Ideal.absNorm P : ℂ) ≠ 0 := by exact_mod_cast (hNP P hP).ne'
    exact (differentiable_const _).sub ((differentiable_const _).mul
      (fun s => (differentiableAt_id.neg).const_cpow (Or.inl hP0)))
  have hEb : ∀ w : ℂ, 0 ≤ w.re → ‖E w‖ ≤ 2 ^ T.card := by
    intro w hw
    simp only [hE]
    rw [norm_prod]
    calc ∏ P ∈ T, ‖1 - gK ι 𝔪 u P * (Ideal.absNorm P : ℂ) ^ (-w)‖ ≤ ∏ _P ∈ T, (2 : ℝ) := by
          refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun P hP => ?_
          have h1 : ‖(Ideal.absNorm P : ℂ) ^ (-w)‖ ≤ 1 := by
            rw [Complex.norm_natCast_cpow_of_pos (hNP P hP), Complex.neg_re]
            exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hNP P hP)
              (by linarith)
          calc _ ≤ ‖(1 : ℂ)‖ + ‖gK ι 𝔪 u P * (Ideal.absNorm P : ℂ) ^ (-w)‖ := norm_sub_le _ _
            _ ≤ 1 + 1 * 1 := by
                rw [norm_one, norm_mul]
                gcongr
                exact norm_gK_le u P
            _ = 2 := by norm_num
      _ = 2 ^ T.card := by simp
  -- the coefficient as an indicator
  have hind : ∀ 𝔡, acoef ι 𝔪 g 𝔠₁ 𝔠₂ 𝔡 = (T12B.Cop T).indicator (gK ι 𝔪 u) 𝔡 := by
    intro 𝔡
    unfold acoef
    by_cases h𝔡 : IsExterior 𝔪 𝔡
    · rw [if_pos h𝔡, hcoef 𝔡 h𝔡]
      split_ifs with hc
      · rw [Set.indicator_of_mem (show 𝔡 ∈ T12B.Cop T from hc)]; simp [gK, h𝔡]
      · rw [Set.indicator_of_notMem (show 𝔡 ∉ T12B.Cop T from hc)]
    · rw [if_neg h𝔡]
      by_cases hc : 𝔡 ∈ T12B.Cop T
      · rw [Set.indicator_of_mem hc]; simp [gK, h𝔡]
      · rw [Set.indicator_of_notMem hc]
  have hser : ∀ w : ℂ, w.re = 2 →
      Λ w * E w = ∑' 𝔡, acoef ι 𝔪 g 𝔠₁ 𝔠₂ 𝔡 * (Ideal.absNorm 𝔡 : ℂ) ^ (-w) := by
    intro w hw
    have hw0 : 0 < w.re := by rw [hw]; norm_num
    set gg : Ideal (𝓞 F) → ℂ := fun I => gK ι 𝔪 u I * (Ideal.absNorm I : ℂ) ^ (-w) with hgg
    have hmul : ∀ I J, gg (I * J) = gg I * gg J := by
      intro I J
      simp only [hgg, gK_mul, map_mul, natCast_cpow_mul]
      ring
    have hgs : Summable gg := by
      refine Summable.of_norm_bounded (T12B.summable_absNorm_rpow (F := F) (σ := 2)
        (by norm_num)) fun I => ?_
      simp only [hgg, norm_mul]
      have := norm_natCast_cpow_le (Ideal.absNorm I) hw0
      rw [hw] at this
      calc ‖gK ι 𝔪 u I‖ * ‖(Ideal.absNorm I : ℂ) ^ (-w)‖ ≤ 1 * ((Ideal.absNorm I : ℝ) ^ (-(2 : ℝ))) :=
            mul_le_mul (norm_gK_le u I) this (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    have hTp' : ∀ P ∈ T, P.IsPrime ∧ P ≠ ⊥ := fun P hP => ⟨(hTp P hP).1, (hTp P hP).2.1⟩
    have hsv := T12B.sieve gg hmul hgs T hTp'
    rw [hΛeq w (by rw [hw]; norm_num), kummerL_eq_tsum']
    change (∑' I, gg I) * ∏ P ∈ T, (1 - gg P) = _
    rw [hsv]
    refine tsum_congr fun 𝔡 => ?_
    rw [hind 𝔡]
    by_cases hc : 𝔡 ∈ T12B.Cop T
    · rw [Set.indicator_of_mem hc, Set.indicator_of_mem hc]
    · rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem hc, zero_mul]
  -- the bound on the strip
  set B := Cl * (Ideal.absNorm r.1.1 : ℝ) ^ (1 / 2 + δ) * 2 ^ T.card
  have hΦb : ∀ w : ℂ, 3 / 1000 ≤ w.re → w.re ≤ 2 → ‖Λ w * E w‖ ≤ B * (2 + |w.im|) ^ A := by
    intro w h1 h2
    rw [norm_mul]
    have hl := hΛb w h1 (by linarith)
    have he := hEb w (by linarith)
    have hlam0 : 0 ≤ Cl * (Ideal.absNorm r.1.1 : ℝ) ^ (1 / 2 + δ) * (2 + |w.im|) ^ A :=
      (norm_nonneg _).trans hl
    calc ‖Λ w‖ * ‖E w‖ ≤ (Cl * (Ideal.absNorm r.1.1 : ℝ) ^ (1 / 2 + δ) * (2 + |w.im|) ^ A) *
          2 ^ T.card := mul_le_mul hl he (norm_nonneg _) hlam0
      _ = B * (2 + |w.im|) ^ A := by simp only [B]; ring
  have hmain := hK (acoef ι 𝔪 g 𝔠₁ 𝔠₂) (norm_acoef_le g 𝔠₁ 𝔠₂)
    (by unfold acoef; rw [if_neg (fun h => h.1 rfl)]) (fun w => Λ w * E w) B
    (hΛd.mul hEd) (fun w hw => hser w hw) hΦb D hD
  refine hmain.trans ?_
  -- `B` against the norms of the columns
  have hCl : 0 ≤ Cl := by
    have h := (norm_nonneg _).trans (hΛb 1 (by norm_num) (by norm_num))
    have hp : 0 < (Ideal.absNorm r.1.1 : ℝ) ^ (1 / 2 + δ) * (2 + |(1 : ℂ).im|) ^ A := by
      have : 0 < (Ideal.absNorm r.1.1 : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact r.1.2.1.1)
      positivity
    by_contra hc
    push Not at hc
    nlinarith [mul_pos_of_neg_of_neg hc (neg_neg_of_pos hp)]
  have hN1 : (2 : ℝ) ^ T.card ≤ Ideal.absNorm 𝔠₁ := by exact_mod_cast hTc
  have hNr' : (Ideal.absNorm r.1.1 : ℝ) ≤ ((Ideal.absNorm 𝔠₁ : ℝ) * Ideal.absNorm 𝔠₂) ^ 3 := by
    exact_mod_cast hNr
  have hr1 : (Ideal.absNorm r.1.1 : ℝ) ^ (1 / 2 + δ) ≤
      (((Ideal.absNorm 𝔠₁ : ℝ) * Ideal.absNorm 𝔠₂) ^ 3) ^ (1 / 2 + δ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hNr' (by linarith)
  have hB : B ≤ Cl * (((Ideal.absNorm 𝔠₁ : ℝ) * Ideal.absNorm 𝔠₂) ^ 3) ^ (1 / 2 + δ) *
      Ideal.absNorm 𝔠₁ := by
    simp only [B]
    gcongr
  have hD0 : 0 ≤ D ^ (3 / 1000 : ℝ) := Real.rpow_nonneg hD.le _
  calc K * B * D ^ (3 / 1000 : ℝ) ≤ K * (Cl * (((Ideal.absNorm 𝔠₁ : ℝ) * Ideal.absNorm 𝔠₂) ^ 3) ^
        (1 / 2 + δ) * Ideal.absNorm 𝔠₁) * D ^ (3 / 1000 : ℝ) := by gcongr

end L3E

end ArtinPrimitiveRoots

end
end

section
section
namespace ArtinPrimitiveRoots

open NumberField Filter Topology

/-! L2D: ideal counting in a number field. -/

variable {F : Type*} [Field F] [NumberField F]

lemma L2D_finite_le (t : ℝ) : {I : Ideal (𝓞 F) | (Ideal.absNorm I : ℝ) ≤ t}.Finite :=
  (Ideal.finite_setOfPred_absNorm_le ⌊t⌋₊).subset fun I hI => Nat.le_floor hI

/-- The finite set of ideals of norm `≤ t` (including `⊥`). -/
noncomputable def L2D_le (F : Type*) [Field F] [NumberField F] (t : ℝ) : Finset (Ideal (𝓞 F)) :=
  (L2D_finite_le (F := F) t).toFinset

@[simp] lemma L2D_mem_le {t : ℝ} {I : Ideal (𝓞 F)} :
    I ∈ L2D_le F t ↔ (Ideal.absNorm I : ℝ) ≤ t := by
  simp [L2D_le]

lemma L2D_le_mono {s t : ℝ} (h : s ≤ t) : L2D_le F s ⊆ L2D_le F t := by
  intro I hI; rw [L2D_mem_le] at *; linarith

/-- `#{I : N I ≤ t} ≤ A t` for `t ≥ 1`. -/
lemma L2D_count : ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, 1 ≤ t → ((L2D_le F t).card : ℝ) ≤ A * t := by
  have hlim := NumberField.Ideal.tendsto_norm_le_div_atTop F
  set L := (2 ^ InfinitePlace.nrRealPlaces F * (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces F *
    Units.regulator F * classNumber F) / (Units.torsionOrder F * Real.sqrt |discr F|)
  have hev : ∀ᶠ s : ℝ in atTop,
      (Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ s} : ℝ) / s < |L| + 1 :=
    hlim.eventually (gt_mem_nhds (by linarith [le_abs_self L]))
  obtain ⟨s₀, hs₀⟩ := eventually_atTop.1 hev
  have hcard : ∀ t : ℝ, (Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ t} : ℝ) =
      ((L2D_le F t).card : ℝ) := by
    intro t
    congr 1
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun I => by simp)
  set s₁ := max s₀ 1
  have hs₁ : ((L2D_le F s₁).card : ℝ) ≤ (|L| + 1) * s₁ := by
    have h := hs₀ s₁ (le_max_left _ _)
    rw [hcard, div_lt_iff₀ (by positivity)] at h
    linarith
  have hL1 : 0 < |L| + 1 := by positivity
  refine ⟨(|L| + 1) * s₁, by positivity, fun t ht => ?_⟩
  by_cases hts : s₁ ≤ t
  · have h := hs₀ t (le_trans (le_max_left _ _) hts)
    rw [hcard, div_lt_iff₀ (by linarith)] at h
    have : (|L| + 1) * t ≤ (|L| + 1) * s₁ * t := by
      have : 1 ≤ s₁ := le_max_right _ _
      nlinarith
    linarith
  · push Not at hts
    have hsub := L2D_le_mono (F := F) hts.le
    have : ((L2D_le F t).card : ℝ) ≤ (L2D_le F s₁).card := by
      exact_mod_cast Finset.card_le_card hsub
    nlinarith

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3E_Core: (E₆) from KummerConvexity, for one modulus

Rows `N𝔡 ≤ D` are enlarged to all exterior `𝔡` with weight `e·e^{-N𝔡/D} ≥ 1`; the square is
expanded; the diagonal is `≤ (1 + 2ζ_F(σ)) D^σ` (`σ = 1 + min(ε,1)`), and each off-diagonal pair is
`≪ C^{9/2} D^{3/1000}` (L3E_Pair, with `δ = 1/12`); Cauchy–Schwarz and `#cols ≤ A C` finish, using
`C^{11/2} D^{3/1000} ≤ D + C⁶`. -/

open Complex NumberField

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinPrimitiveRoots

namespace L3E

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

lemma finite_box (𝔪 : Ideal (𝓞 F)) (X : ℝ) :
    Finite {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧ (Ideal.absNorm 𝔡 : ℝ) ≤ X} := by
  have hs : {𝔡 : Ideal (𝓞 F) | IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧
      (Ideal.absNorm 𝔡 : ℝ) ≤ X}.Finite :=
    (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊X⌋₊).subset
      (fun 𝔡 h => Nat.le_floor h.2.2)
  exact hs.to_subtype

lemma final_ineq {C D : ℝ} (hC : 1 ≤ C) (hD : 1 ≤ D) :
    C ^ (11 / 2 : ℝ) * D ^ (3 / 1000 : ℝ) ≤ D + C ^ 6 := by
  set M := max D (C ^ 6)
  have hC6 : (1 : ℝ) ≤ C ^ 6 := one_le_pow₀ hC
  have hM1 : 1 ≤ M := le_max_of_le_left hD
  have h1 : C ^ (11 / 2 : ℝ) ≤ M ^ (11 / 12 : ℝ) := by
    have : C ^ (11 / 2 : ℝ) = (C ^ (6 : ℝ)) ^ (11 / 12 : ℝ) := by
      rw [← Real.rpow_mul (by linarith)]; norm_num
    rw [this]
    refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
    rw [show (C ^ (6 : ℝ)) = C ^ 6 by norm_cast]
    exact le_max_right _ _
  have h2 : D ^ (3 / 1000 : ℝ) ≤ M ^ (3 / 1000 : ℝ) :=
    Real.rpow_le_rpow (by linarith) (le_max_left _ _) (by norm_num)
  calc C ^ (11 / 2 : ℝ) * D ^ (3 / 1000 : ℝ) ≤ M ^ (11 / 12 : ℝ) * M ^ (3 / 1000 : ℝ) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = M ^ (11 / 12 + 3 / 1000 : ℝ) := by rw [← Real.rpow_add (by linarith)]
    _ ≤ M ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hM1 (by norm_num)
    _ = M := Real.rpow_one M
    _ ≤ D + C ^ 6 := max_le (by linarith) (by linarith)

lemma off_le {Kp Clp Ac C D ε : ℝ} (hC : 1 ≤ C) (hD : 1 ≤ D) (hε : 0 < ε) (hKp : 0 ≤ Kp)
    (hClp : 0 ≤ Clp) (hAc : 0 ≤ Ac) :
    Kp * Clp * C ^ (9 / 2 : ℝ) * D ^ (3 / 1000 : ℝ) * (Ac * C) ≤
      Kp * Clp * Ac * ((D + C ^ 6) * (C * D) ^ ε) := by
  have hCD : 1 ≤ (C * D) ^ ε := Real.one_le_rpow (by nlinarith) hε.le
  have h1 : C ^ (9 / 2 : ℝ) * C = C ^ (11 / 2 : ℝ) := by
    rw [show (11 / 2 : ℝ) = 9 / 2 + 1 by norm_num, Real.rpow_add (by linarith), Real.rpow_one]
  have h2 := final_ineq hC hD
  have h0 : 0 ≤ D + C ^ 6 := by positivity
  have h3 : C ^ (11 / 2 : ℝ) * D ^ (3 / 1000 : ℝ) ≤ (D + C ^ 6) * (C * D) ^ ε :=
    h2.trans (le_mul_of_one_le_right h0 hCD)
  have h4 : Kp * Clp * C ^ (9 / 2 : ℝ) * D ^ (3 / 1000 : ℝ) * (Ac * C) =
      Kp * Clp * Ac * ((C ^ (9 / 2 : ℝ) * C) * D ^ (3 / 1000 : ℝ)) := by ring
  rw [h4, h1]
  exact mul_le_mul_of_nonneg_left h3 (by positivity)

lemma diag_le {C D ε ε₁ : ℝ} (hC : 1 ≤ C) (hD : 1 ≤ D) (hε : 0 < ε) (hε₁ : ε₁ ≤ ε) :
    D ^ (1 + ε₁) ≤ (D + C ^ 6) * (C * D) ^ ε := by
  have hD0 : 0 < D := by linarith
  have h1 : D ^ (1 + ε₁) = D * D ^ ε₁ := by rw [Real.rpow_add hD0, Real.rpow_one]
  have h2 : D ^ ε₁ ≤ (C * D) ^ ε :=
    (Real.rpow_le_rpow_of_exponent_le hD hε₁).trans
      (Real.rpow_le_rpow (by linarith) (by nlinarith) hε.le)
  rw [h1]
  have hC6 : 0 ≤ C ^ 6 := by positivity
  calc D * D ^ ε₁ ≤ D * (C * D) ^ ε := mul_le_mul_of_nonneg_left h2 hD0.le
    _ ≤ (D + C ^ 6) * (C * D) ^ ε := by gcongr; linarith

/-- **(E₆) for one modulus**, from KummerConvexity in the form `hL`. -/
theorem core (hχ : C3M.HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {A Cl : ℝ} (hA : 0 ≤ A)
    (hL : ∀ r : FreqClass 𝔪, r ≠ principalFreq 𝔪 → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
          (∀ w : ℂ, 1 < w.re → Λ w = kummerL ι 𝔪 (freqElt g r) w) ∧
          ∀ w : ℂ, 3 / 1000 ≤ w.re → w.re ≤ 4 →
            ‖Λ w‖ ≤ Cl * (Ideal.absNorm r.1.1 : ℝ) ^ (1 / 2 + 1 / 12 : ℝ) * (2 + |w.im|) ^ A)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
      ∀ z : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧ (Ideal.absNorm 𝔠 : ℝ) ≤ C} → ℂ,
        ∑' 𝔡 : {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧ (Ideal.absNorm 𝔡 : ℝ) ≤ D},
            ‖∑' 𝔠, z 𝔠 * residueSymbol ι 𝔪 𝔡.1 (g.gen 𝔠.1) ^ 3‖ ^ 2 ≤
          K * (D + C ^ 6) * (C * D) ^ ε * ∑' 𝔠, ‖z 𝔠‖ ^ 2 := by
  classical
  obtain ⟨Kp, hKp0, hKp⟩ := pair_bound hχ g hA (by norm_num : (0 : ℝ) < 1 / 12) hL
  obtain ⟨Ac, hAc0, hAc⟩ := L2D_count (F := F)
  set ε₁ := min ε 1 with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hε one_pos
  have hε₁1 : ε₁ ≤ 1 := min_le_right _ _
  have hε₁ε : ε₁ ≤ ε := min_le_left _ _
  set σ := 1 + ε₁ with hσ
  set Zσ := ∑' J : Ideal (𝓞 F), ((Ideal.absNorm J : ℕ) : ℝ) ^ (-σ) with hZσ
  have hZ0 : 0 ≤ Zσ := tsum_nonneg fun J => Real.rpow_nonneg (Nat.cast_nonneg _) _
  set Clp := max Cl 0 with hClp
  have hClp0 : 0 ≤ Clp := le_max_right _ _
  set e := Real.exp 1 with he
  have he0 : 0 < e := Real.exp_pos 1
  refine ⟨e * (1 + 2 * Zσ) + e * (Kp * Clp) * Ac, ?_⟩
  intro C D hC hD
  have hD0 : 0 < D := by linarith
  haveI : Fintype {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧
      (Ideal.absNorm 𝔠 : ℝ) ≤ C} := @Fintype.ofFinite _ (finite_box 𝔪 C)
  set Col := {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧ (Ideal.absNorm 𝔠 : ℝ) ≤ C}
    with hCol
  intro z
  set Sf : Ideal (𝓞 F) → ℂ := fun 𝔡 => ∑ c : Col, z c * residueSymbol ι 𝔪 𝔡 (g.gen c.1) ^ 3
    with hSf
  set Z1 := ∑ c : Col, ‖z c‖ with hZ1
  set Q := ∑ c : Col, ‖z c‖ ^ 2 with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun c _ => by positivity
  have hSb : ∀ 𝔡, ‖Sf 𝔡‖ ≤ Z1 := by
    intro 𝔡
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [norm_mul, norm_pow]
    have := norm_rs_le (ι := ι) 𝔡 (g.gen c.1)
    calc ‖z c‖ * ‖residueSymbol ι 𝔪 𝔡 (g.gen c.1)‖ ^ 3 ≤ ‖z c‖ * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) this) (norm_nonneg _)
      _ = ‖z c‖ := mul_one _
  obtain ⟨hEs, hEle⟩ := tsum_exp_le (F := F) (σ := σ) (by linarith) (by linarith) hD0
  set W : Ideal (𝓞 F) → ℝ := fun 𝔡 =>
    if IsExterior 𝔪 𝔡 then e * Real.exp (-((Ideal.absNorm 𝔡 : ℝ) / D)) else 0 with hW
  have hW0 : ∀ 𝔡, 0 ≤ W 𝔡 := fun 𝔡 => by simp only [hW]; split_ifs <;> positivity
  have hWle : ∀ 𝔡, W 𝔡 ≤ e * Real.exp (-((Ideal.absNorm 𝔡 : ℝ) / D)) := fun 𝔡 => by
    simp only [hW]; split_ifs
    · exact le_rfl
    · positivity
  have hRs : Summable fun 𝔡 => W 𝔡 * ‖Sf 𝔡‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun 𝔡 => mul_nonneg (hW0 𝔡) (by positivity))
      (fun 𝔡 => ?_) ((hEs.mul_left e).mul_right (Z1 ^ 2))
    exact mul_le_mul (hWle 𝔡) (pow_le_pow_left₀ (norm_nonneg _) (hSb 𝔡) 2) (by positivity)
      (by positivity)
  -- Step 1: enlarge the rows
  set Rset := {𝔡 : Ideal (𝓞 F) | IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧ (Ideal.absNorm 𝔡 : ℝ) ≤ D}
  have hstep1 : ∑' 𝔡 : {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧
        (Ideal.absNorm 𝔡 : ℝ) ≤ D},
        ‖∑' 𝔠, z 𝔠 * residueSymbol ι 𝔪 𝔡.1 (g.gen 𝔠.1) ^ 3‖ ^ 2 ≤
      ∑' 𝔡, W 𝔡 * ‖Sf 𝔡‖ ^ 2 := by
    have h1 : ∑' 𝔡 : {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧
        (Ideal.absNorm 𝔡 : ℝ) ≤ D},
        ‖∑' 𝔠, z 𝔠 * residueSymbol ι 𝔪 𝔡.1 (g.gen 𝔠.1) ^ 3‖ ^ 2 =
        ∑' 𝔡 : Rset, ‖Sf 𝔡.1‖ ^ 2 := by
      refine tsum_congr fun 𝔡 => ?_
      rw [tsum_fintype]
    rw [h1, tsum_subtype Rset (fun 𝔡 => ‖Sf 𝔡‖ ^ 2)]
    have hpt : ∀ 𝔡, Rset.indicator (fun 𝔡 => ‖Sf 𝔡‖ ^ 2) 𝔡 ≤ W 𝔡 * ‖Sf 𝔡‖ ^ 2 := by
      intro 𝔡
      by_cases h : 𝔡 ∈ Rset
      · rw [Set.indicator_of_mem h]
        have hW1 : 1 ≤ W 𝔡 := by
          simp only [hW, if_pos h.1, he]
          rw [← Real.exp_add, Real.one_le_exp_iff]
          have : (Ideal.absNorm 𝔡 : ℝ) / D ≤ 1 := (div_le_one hD0).2 h.2.2
          linarith
        nlinarith [sq_nonneg ‖Sf 𝔡‖]
      · rw [Set.indicator_of_notMem h]
        exact mul_nonneg (hW0 𝔡) (by positivity)
    exact Summable.tsum_le_tsum hpt
      (Summable.of_nonneg_of_le (fun 𝔡 => Set.indicator_nonneg (fun _ _ => by positivity) _)
        hpt hRs) hRs
  -- Step 2: expand the square
  set T : Col × Col → ℂ := fun p =>
    ∑' 𝔡, acoef ι 𝔪 g p.1.1 p.2.1 𝔡 * ((Real.exp (-((Ideal.absNorm 𝔡 : ℝ) / D)) : ℝ) : ℂ)
    with hT
  have hexp : ∀ 𝔡, ((W 𝔡 * ‖Sf 𝔡‖ ^ 2 : ℝ) : ℂ) = ∑ p : Col × Col,
      z p.1 * starRingEnd ℂ (z p.2) * ((e : ℂ) *
        (acoef ι 𝔪 g p.1.1 p.2.1 𝔡 * ((Real.exp (-((Ideal.absNorm 𝔡 : ℝ) / D)) : ℝ) : ℂ))) := by
    intro 𝔡
    by_cases h𝔡 : IsExterior 𝔪 𝔡
    · have hSS : ((‖Sf 𝔡‖ ^ 2 : ℝ) : ℂ) = ∑ p : Col × Col, z p.1 * starRingEnd ℂ (z p.2) *
          (residueSymbol ι 𝔪 𝔡 (g.gen p.1.1) ^ 3 *
            starRingEnd ℂ (residueSymbol ι 𝔪 𝔡 (g.gen p.2.1) ^ 3)) := by
        rw [Complex.ofReal_pow, ← Complex.mul_conj', hSf, map_sum, Finset.sum_mul_sum,
          ← Finset.sum_product']
        refine Finset.sum_congr (by simp) fun p _ => ?_
        rw [map_mul]; ring
      rw [Complex.ofReal_mul, hSS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [hW, if_pos h𝔡, acoef]
      push_cast
      ring
    · simp [hW, h𝔡, acoef]
  have hsumm : ∀ p : Col × Col, Summable fun 𝔡 => z p.1 * starRingEnd ℂ (z p.2) * ((e : ℂ) *
      (acoef ι 𝔪 g p.1.1 p.2.1 𝔡 * ((Real.exp (-((Ideal.absNorm 𝔡 : ℝ) / D)) : ℝ) : ℂ))) := by
    intro p
    refine ((Summable.of_norm_bounded hEs fun 𝔡 => ?_).mul_left (e : ℂ)).mul_left _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc ‖acoef ι 𝔪 g p.1.1 p.2.1 𝔡‖ * Real.exp (-((Ideal.absNorm 𝔡 : ℝ) / D)) ≤
          1 * Real.exp (-((Ideal.absNorm 𝔡 : ℝ) / D)) :=
          mul_le_mul_of_nonneg_right (norm_acoef_le g _ _ 𝔡) (Real.exp_pos _).le
      _ = _ := one_mul _
  have hR : ((∑' 𝔡, W 𝔡 * ‖Sf 𝔡‖ ^ 2 : ℝ) : ℂ) =
      ∑ p : Col × Col, z p.1 * starRingEnd ℂ (z p.2) * ((e : ℂ) * T p) := by
    rw [Complex.ofReal_tsum, tsum_congr hexp, Summable.tsum_finsetSum (fun p _ => hsumm p)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [tsum_mul_left, tsum_mul_left]
  -- Step 3: the pair bounds
  set Md := (1 + 2 * Zσ) * D ^ σ with hMd
  set Mo := Kp * Clp * C ^ (9 / 2 : ℝ) * D ^ (3 / 1000 : ℝ) with hMo
  have hDσ : 1 ≤ D ^ σ := Real.one_le_rpow hD (by linarith)
  have hMo0 : 0 ≤ Mo := by positivity
  have hTb : ∀ p : Col × Col, ‖T p‖ ≤ (if p.1 = p.2 then Md else 0) + Mo := by
    intro p
    by_cases hp : p.1 = p.2
    · rw [if_pos hp]
      have hpt' : ∀ 𝔡, ‖acoef ι 𝔪 g p.1.1 p.2.1 𝔡 *
          ((Real.exp (-((Ideal.absNorm 𝔡 : ℝ) / D)) : ℝ) : ℂ)‖ ≤
          Real.exp (-((Ideal.absNorm 𝔡 : ℝ) / D)) := by
        intro 𝔡
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact (mul_le_mul_of_nonneg_right (norm_acoef_le g _ _ 𝔡) (Real.exp_pos _).le).trans
          (le_of_eq (one_mul _))
      have hacs : Summable fun 𝔡 => ‖acoef ι 𝔪 g p.1.1 p.2.1 𝔡 *
          ((Real.exp (-((Ideal.absNorm 𝔡 : ℝ) / D)) : ℝ) : ℂ)‖ :=
        Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt' hEs
      have h1 : ‖T p‖ ≤ ∑' 𝔡 : Ideal (𝓞 F), Real.exp (-((Ideal.absNorm 𝔡 : ℝ) / D)) :=
        (norm_tsum_le_tsum_norm hacs).trans (Summable.tsum_le_tsum hpt' hacs hEs)
      have h2 : 1 + 2 * D ^ σ * Zσ ≤ Md := by
        simp only [hMd]; nlinarith
      linarith
    · rw [if_neg hp, zero_add]
      have hne : p.1.1 ≠ p.2.1 := fun h => hp (Subtype.ext h)
      have h := hKp p.1.1 p.2.1 p.1.2.1 p.2.2.1 p.1.2.2.1 p.2.2.2.1 hne D hD0
      refine h.trans ?_
      have hN1 : (Ideal.absNorm p.1.1 : ℝ) ≤ C := p.1.2.2.2
      have hN2 : (Ideal.absNorm p.2.1 : ℝ) ≤ C := p.2.2.2.2
      have hX : (((Ideal.absNorm p.1.1 : ℝ) * Ideal.absNorm p.2.1) ^ 3) ^ (1 / 2 + 1 / 12 : ℝ) ≤
          C ^ (7 / 2 : ℝ) := by
        have h3 : ((Ideal.absNorm p.1.1 : ℝ) * Ideal.absNorm p.2.1) ^ 3 ≤ C ^ (6 : ℝ) := by
          rw [show C ^ (6 : ℝ) = (C * C) ^ 3 by norm_cast; ring]
          exact pow_le_pow_left₀ (by positivity) (mul_le_mul hN1 hN2 (by positivity)
            (by linarith)) 3
        calc _ ≤ (C ^ (6 : ℝ)) ^ (1 / 2 + 1 / 12 : ℝ) :=
              Real.rpow_le_rpow (by positivity) h3 (by norm_num)
          _ = C ^ (7 / 2 : ℝ) := by rw [← Real.rpow_mul (by linarith)]; norm_num
      have hCl : Cl ≤ Clp := le_max_left _ _
      have hX0 : 0 ≤ (((Ideal.absNorm p.1.1 : ℝ) * Ideal.absNorm p.2.1) ^ 3) ^
          (1 / 2 + 1 / 12 : ℝ) := by positivity
      have hin : Cl * (((Ideal.absNorm p.1.1 : ℝ) * Ideal.absNorm p.2.1) ^ 3) ^
          (1 / 2 + 1 / 12 : ℝ) * Ideal.absNorm p.1.1 ≤ Clp * C ^ (7 / 2 : ℝ) * C := by
        calc _ ≤ Clp * (((Ideal.absNorm p.1.1 : ℝ) * Ideal.absNorm p.2.1) ^ 3) ^
              (1 / 2 + 1 / 12 : ℝ) * Ideal.absNorm p.1.1 := by gcongr
          _ ≤ Clp * C ^ (7 / 2 : ℝ) * C := by gcongr
      have hC9 : C ^ (7 / 2 : ℝ) * C = C ^ (9 / 2 : ℝ) := by
        rw [show (9 / 2 : ℝ) = 7 / 2 + 1 by norm_num, Real.rpow_add (by linarith), Real.rpow_one]
      calc Kp * (Cl * (((Ideal.absNorm p.1.1 : ℝ) * Ideal.absNorm p.2.1) ^ 3) ^
            (1 / 2 + 1 / 12 : ℝ) * Ideal.absNorm p.1.1) * D ^ (3 / 1000 : ℝ) ≤
            Kp * (Clp * C ^ (7 / 2 : ℝ) * C) * D ^ (3 / 1000 : ℝ) := by gcongr
        _ = Mo := by rw [hMo, mul_assoc Clp, hC9]; ring
  -- Step 4: sum over the pairs
  set R := ∑' 𝔡, W 𝔡 * ‖Sf 𝔡‖ ^ 2 with hRdef
  have hR0 : 0 ≤ R := tsum_nonneg fun 𝔡 => mul_nonneg (hW0 𝔡) (by positivity)
  have hRle : R ≤ ∑ p : Col × Col, ‖z p.1‖ * ‖z p.2‖ * (e * ((if p.1 = p.2 then Md else 0) + Mo)) := by
    have h := congrArg (fun x : ℂ => ‖x‖) hR
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR0] at h
    rw [h]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos he0]
    gcongr
    exact hTb p
  have hsplit : ∑ p : Col × Col, ‖z p.1‖ * ‖z p.2‖ * (e * ((if p.1 = p.2 then Md else 0) + Mo)) =
      e * Md * Q + e * Mo * Z1 ^ 2 := by
    have h1 : ∀ p : Col × Col, ‖z p.1‖ * ‖z p.2‖ * (e * ((if p.1 = p.2 then Md else 0) + Mo)) =
        e * Md * (if p.1 = p.2 then ‖z p.1‖ * ‖z p.2‖ else 0) + e * Mo * (‖z p.1‖ * ‖z p.2‖) := by
      intro p; split_ifs <;> ring
    rw [Finset.sum_congr rfl fun p _ => h1 p, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
    congr 1
    · congr 1
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_ite_eq]; simp [sq]
    · congr 1
      rw [hZ1, sq, Finset.sum_mul_sum, ← Finset.sum_product']
      rfl
  have hcard : (Fintype.card Col : ℝ) ≤ Ac * C := by
    have hinj : Fintype.card Col ≤ Fintype.card (L2D_le F C) :=
      Fintype.card_le_of_injective
        (fun c : Col => (⟨c.1, (L2D_mem_le).2 c.2.2.2⟩ : (L2D_le F C)))
        (fun a b hab => by have := congrArg Subtype.val hab; exact Subtype.ext this)
    rw [Fintype.card_coe] at hinj
    exact (Nat.cast_le.2 hinj).trans (hAc C hC)
  have hCS : Z1 ^ 2 ≤ Ac * C * Q := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset Col)) (f := fun c => ‖z c‖)
    rw [Finset.card_univ] at h
    exact h.trans (mul_le_mul_of_nonneg_right hcard hQ0)
  have hdiag : D ^ σ ≤ (D + C ^ 6) * (C * D) ^ ε := diag_le hC hD hε hε₁ε
  have hoff : Mo * (Ac * C) ≤ Kp * Clp * Ac * ((D + C ^ 6) * (C * D) ^ ε) :=
    off_le hC hD hε hKp0 hClp0 hAc0.le
  have hQt : ∑' 𝔠 : Col, ‖z 𝔠‖ ^ 2 = Q := tsum_fintype _
  rw [hQt]
  calc _ ≤ R := hstep1
    _ ≤ e * Md * Q + e * Mo * Z1 ^ 2 := hRle.trans (le_of_eq hsplit)
    _ ≤ e * Md * Q + e * Mo * (Ac * C * Q) := by gcongr
    _ = e * (1 + 2 * Zσ) * D ^ σ * Q + e * (Mo * (Ac * C)) * Q := by rw [hMd]; ring
    _ ≤ e * (1 + 2 * Zσ) * ((D + C ^ 6) * (C * D) ^ ε) * Q +
          e * (Kp * Clp * Ac * ((D + C ^ 6) * (C * D) ^ ε)) * Q := by gcongr
    _ = (e * (1 + 2 * Zσ) + e * (Kp * Clp) * Ac) * (D + C ^ 6) * (C * D) ^ ε * Q := by ring

end L3E

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3E_Main: GL Lemma 4.2 with exponent 6, `(E₆)`, as `chk_…`

`exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le_add_pow_six`: the statement of
a7e19a77 with `D + C ^ 6` in place of `D + C ^ 2`, from C3M's `hypChiAll` and KummerConvexity
(L3K's proof of 8ad1a151, imported as modules) through `L3E.core`. Does not import the stub of
a7e19a77. -/

set_option autoImplicit false

namespace ArtinPrimitiveRoots

open NumberField

theorem chk_exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le_add_pow_six (n : ℕ)
    (hn0 : 0 < n) (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (g : AllowedGen ι 𝔪) (ε : ℝ), 0 < ε → ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
        ∀ z : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧ (Ideal.absNorm 𝔠 : ℝ) ≤ C} → ℂ,
          ∑' 𝔡 : {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧ (Ideal.absNorm 𝔡 : ℝ) ≤ D},
              ‖∑' 𝔠, z 𝔠 * residueSymbol ι 𝔪 𝔡.1 (g.gen 𝔠.1) ^ 3‖ ^ 2 ≤
            K * (D + C ^ 6) * (C * D) ^ ε * ∑' 𝔠, ‖z 𝔠‖ ^ 2 := by
  obtain ⟨N₁, hN₁⟩ := C3M.hypChiAll (F := F) n hn0 hn ι
  obtain ⟨N₂, hN₂⟩ := exists_cutoff_exists_differentiable_eq_kummerL_and_norm_le n hn0 hn F ι
  refine ⟨max N₁ N₂, fun 𝔪 h𝔪 hS g ε hε => ?_⟩
  have hS1 : SmallPrimesDvd N₁ 𝔪 := fun P hP hb hle => hS P hP hb (hle.trans (le_max_left _ _))
  have hS2 : SmallPrimesDvd N₂ 𝔪 := fun P hP hb hle => hS P hP hb (hle.trans (le_max_right _ _))
  have hχ := hN₁ 𝔪 h𝔪 hS1
  obtain ⟨A₀, hA₀⟩ := hN₂ 𝔪 h𝔪 hS2 g
  obtain ⟨Cl, hCl⟩ := hA₀ (1 / 12) (by norm_num)
  refine L3E.core hχ g (A := max A₀ 0) (Cl := Cl) (le_max_right _ _) ?_ ε hε
  intro r hr
  obtain ⟨Λ, hd, heq, hb⟩ := hCl r hr
  refine ⟨Λ, hd, heq, fun w h1 h2 => ?_⟩
  have h := hb w h1 h2
  have ht : (1 : ℝ) ≤ 2 + |w.im| := by linarith [abs_nonneg w.im]
  have hp : 0 < (2 + |w.im|) ^ A₀ := Real.rpow_pos_of_pos (by linarith) _
  have hX : 0 ≤ Cl * (Ideal.absNorm r.1.1 : ℝ) ^ (1 / 2 + 1 / 12 : ℝ) := by
    by_contra hc
    push Not at hc
    have := (norm_nonneg _).trans h
    nlinarith [mul_pos_of_neg_of_neg hc (neg_neg_of_pos hp)]
  calc ‖Λ w‖ ≤ Cl * (Ideal.absNorm r.1.1 : ℝ) ^ (1 / 2 + 1 / 12 : ℝ) * (2 + |w.im|) ^ A₀ := h
    _ ≤ Cl * (Ideal.absNorm r.1.1 : ℝ) ^ (1 / 2 + 1 / 12 : ℝ) * (2 + |w.im|) ^ (max A₀ 0) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht (le_max_left _ _)) hX

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3E_Dev: GL Lemma 4.2 with exponent 6, `(E₆)`, under its own name

The statement of a7e19a77 with `D + C ^ 6` in place of `D + C ^ 2` (proof in `L3E_Main`). Does not
import the stub of a7e19a77 nor of the E₆ draft. -/

set_option autoImplicit false

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le_add_pow_six (n : ℕ)
    (hn0 : 0 < n) (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (g : AllowedGen ι 𝔪) (ε : ℝ), 0 < ε → ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
        ∀ z : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧ (Ideal.absNorm 𝔠 : ℝ) ≤ C} → ℂ,
          ∑' 𝔡 : {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧ (Ideal.absNorm 𝔡 : ℝ) ≤ D},
              ‖∑' 𝔠, z 𝔠 * residueSymbol ι 𝔪 𝔡.1 (g.gen 𝔠.1) ^ 3‖ ^ 2 ≤
            K * (D + C ^ 6) * (C * D) ^ ε * ∑' 𝔠, ‖z 𝔠‖ ^ 2 :=
  chk_exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le_add_pow_six n hn0 hn F ι

end ArtinPrimitiveRoots

end
end

section
open ArtinPrimitiveRoots

open NumberField

theorem solution (n : ℕ)
    (hn0 : 0 < n) (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (g : AllowedGen ι 𝔪) (ε : ℝ), 0 < ε → ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
        ∀ z : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧ (Ideal.absNorm 𝔠 : ℝ) ≤ C} → ℂ,
          ∑' 𝔡 : {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧ (Ideal.absNorm 𝔡 : ℝ) ≤ D},
              ‖∑' 𝔠, z 𝔠 * residueSymbol ι 𝔪 𝔡.1 (g.gen 𝔠.1) ^ 3‖ ^ 2 ≤
            K * (D + C ^ 6) * (C * D) ^ ε * ∑' 𝔠, ‖z 𝔠‖ ^ 2 := by
  exact ArtinPrimitiveRoots.exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le_add_pow_six n hn0 hn F ι

end
