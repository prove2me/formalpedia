-- Prove2me | solution 1 for ArtinKP.S2.cubicExt_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:18:04.334647+00:00
-- url     : https://prove2.me/submissions/1d33606a-53ad-455b-99d4-b0d2426dc106

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
import Definitions.Def_ArtinKPB000

section
-- module Solutions.Artin.C0.C0R_P
/-!
# C0-P: the `S`-integers form a PID once `S` contains the small primes

Every ideal class contains a nonzero ideal of bounded norm; once `𝔪` is divisible by every prime of
norm at most that bound, every ideal of `R = 𝓞_S` is principal.
-/

namespace ArtinPrimitiveRoots

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace C0R

variable {F : Type*} [Field F] [NumberField F]

/-- `𝔪 R = R` for `𝔪 ≠ 0`: a power `𝔪^h = (a)` is principal, and `a⁻¹ ∈ R`. -/
theorem map_self_eq_top (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) :
    𝔪.map (algebraMap (𝓞 F) (SInt 𝔪)) = ⊤ := by
  classical
  have h𝔪' : 𝔪 ∈ (Ideal (𝓞 F))⁰ := mem_nonZeroDivisors_of_ne_zero h𝔪
  set h := Fintype.card (ClassGroup (𝓞 F)) with hh
  have hpos : 0 < h := Fintype.card_pos
  have hpow : 𝔪 ^ h ∈ (Ideal (𝓞 F))⁰ := pow_mem h𝔪' h
  have hprin : (𝔪 ^ h).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff hpow]
    have : (⟨𝔪 ^ h, hpow⟩ : (Ideal (𝓞 F))⁰) = (⟨𝔪, h𝔪'⟩ : (Ideal (𝓞 F))⁰) ^ h := rfl
    rw [this, map_pow, pow_card_eq_one]
  obtain ⟨a, ha⟩ := hprin.principal
  rw [Ideal.submodule_span_eq] at ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.2 rfl] at ha
    exact (pow_ne_zero h h𝔪) ha
  have hamem : a ∈ 𝔪 := by
    have : a ∈ 𝔪 ^ h := by rw [ha]; exact Ideal.mem_span_singleton_self a
    exact Ideal.pow_le_self hpos.ne' this
  -- `a⁻¹` is an `S`-integer
  have hinv : ((a : F))⁻¹ ∈ (placesOf 𝔪).integer F := by
    intro v hv
    have hav : a ∉ v.asIdeal := by
      intro hav
      apply hv
      change 𝔪 ≤ v.asIdeal
      have : 𝔪 ^ h ≤ v.asIdeal := by
        rw [ha, Ideal.span_le, Set.singleton_subset_iff]; exact hav
      exact v.isPrime.le_of_pow_le this
    rw [map_inv₀]
    have : v.valuation F (a : F) = 1 := by
      rw [show (a : F) = algebraMap (𝓞 F) F a from rfl, HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.intValuation_eq_one_iff]
      exact hav
    rw [this, inv_one]
  rw [Ideal.eq_top_iff_one]
  have h1 : (1 : SInt 𝔪) = algebraMap (𝓞 F) (SInt 𝔪) a * ⟨_, hinv⟩ := by
    apply Subtype.ext
    change (1 : F) = (a : F) * (a : F)⁻¹
    rw [mul_inv_cancel₀]
    exact_mod_cast ha0
  rw [h1]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hamem)

end C0R

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.KP.A_Residue
/-!
# WP-A: the exterior cubic residue symbol and reciprocity

* `Good 𝔪`: the standing hypotheses on the modulus (`𝔪 ≠ ⊥`, every prime over `6` divides `𝔪`,
  `R = SInt 𝔪` is a PID in the form "every extended ideal is principal");
  `exists_cutoff_good` gives it from `SmallPrimesDvd N₀ 𝔪`.
* `cubicExt ι 𝔪 d c = ∏_{P ∉ S, P ∣ c} χ_P(d)^{2 v_P(c)}` in terms of the goal's
  `sexticResidueSymbol`.
* `cubicExt_eq_prod`: `(d/c) = ι ∏_v (d, c)_v` over the exterior places dividing `c`.
* `cubicExt_reciprocity` (A3): `(d/c) = (c/d) · (c, d)_S` — with the orientation of `CubicPkg`
  the sign in MATH.md (A3) is `+1`.
* unit laws, multiplicativity, dependence on `d mod c` only.

The first section is a universe-polymorphic copy of `C0Y.val_generator`, `C0Y.sextic_spec`
(`Solutions/Artin/C0/C0YR.lean`, stated there for `F : Type`).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.A

variable {F : Type*} [Field F] [NumberField F]

theorem iota3_pow_three (ι : F →+* ℂ) (z : rootsOfUnity 3 F) : iota3 ι z ^ 3 = 1 := by
  rw [← map_pow, root_pow_three, map_one]

variable (ι : F →+* ℂ) {𝔪 : Ideal (𝓞 F)}

open CubicPkg in
/-- `(d/c)` is a cube root of unity when `d` is prime to the exterior part of `c`. -/
theorem cubicExt_pow_three (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F}
    (hz6 : IsPrimitiveRoot z6 6) (c d : SInt 𝔪) (hc : c ≠ 0) (hd0 : d ≠ 0)
    (hd : ∀ v : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ v.asIdeal → v.valuation F (c : F) ≠ 1 →
      v.valuation F (d : F) = 1) :
    cubicExt ι 𝔪 d c ^ 3 = 1 := by
  have hc0 : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)
  have hdF : (d : F) ≠ 0 := fun h => hd0 (Subtype.ext h)
  rw [cubicExt_eq_prod ι P hG hz6 c d (Units.mk0 _ hc0) (Units.mk0 _ hdF) rfl rfl
    (extSupp 𝔪 (c : F)) (fun v hv => ⟨((mem_extSupp hc0 v).mp hv).1,
      hd v ((mem_extSupp hc0 v).mp hv).1 ((mem_extSupp hc0 v).mp hv).2⟩) subset_rfl]
  exact iota3_pow_three ι _

end ArtinKP.A
end
end

section
-- module Solutions.Artin.KP.E_Pairing
/-! # E_Pairing: the pairing `⟨c, d⟩ = ι (c, d)_S` of WP-A is a `Pairing`

`pairingHS`: for any `S : CubicSymbol (SInt 𝔪)` that agrees with WP-A's `cubicExt` (for nonzero
denominators), `br c d = iota3 ι (P.HS 𝔪 c d)` satisfies the interface `Pairing S` of `E_Series`:
bimultiplicative, alternating, cube-valued, and `⟨c, d⟩ (c/d) = (d/c)` for coprime `c, d`
(`cubicExt_reciprocity`).  This is hypothesis (P) of MATH2 §0.1 on `R ∖ 0`.
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

namespace ArtinKP.E

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- Coprime elements of `R` have no common exterior prime. -/
lemma val_of_isCoprime {c d : SInt 𝔪} (h : IsCoprime c d) (v : HeightOneSpectrum (𝓞 F))
    (hv : ¬ 𝔪 ≤ v.asIdeal) : v.valuation F (c : F) = 1 ∨ v.valuation F (d : F) = 1 := by
  obtain ⟨a, b, hab⟩ := h
  by_contra hcon
  push Not at hcon
  have hc : v.valuation F (c : F) < 1 := lt_of_le_of_ne (c.2 v hv) hcon.1
  have hd : v.valuation F (d : F) < 1 := lt_of_le_of_ne (d.2 v hv) hcon.2
  have ha : v.valuation F (a : F) ≤ 1 := a.2 v hv
  have hb : v.valuation F (b : F) ≤ 1 := b.2 v hv
  have h1 : v.valuation F ((a : F) * c + b * d) < 1 := by
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [map_mul]
      calc v.valuation F (a : F) * v.valuation F (c : F) ≤ 1 * v.valuation F (c : F) :=
            mul_le_mul' ha le_rfl
        _ = v.valuation F (c : F) := one_mul _
        _ < 1 := hc
    · rw [map_mul]
      calc v.valuation F (b : F) * v.valuation F (d : F) ≤ 1 * v.valuation F (d : F) :=
            mul_le_mul' hb le_rfl
        _ = v.valuation F (d : F) := one_mul _
        _ < 1 := hd
  have h2 : ((a : F) * c + b * d) = 1 := by
    have := congrArg (fun x : SInt 𝔪 => (x : F)) hab
    simpa using this
  rw [h2, map_one] at h1
  exact lt_irrefl _ h1

end ArtinKP.E
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

lemma le_of_mul_le_mul_ne {a b c : ℤᵐ⁰} (h : a * c ≤ b * c) (hc : c ≠ 0) : a ≤ b := by
  have := mul_le_mul_right h c⁻¹
  rwa [mul_comm c⁻¹, mul_comm c⁻¹, mul_inv_cancel_right₀ hc, mul_inv_cancel_right₀ hc] at this

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

end C3I

end ArtinPrimitiveRoots
end

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

/-- Every `r ∈ R` has `𝔪^N r ⊆ 𝓞` for some `N`. -/
lemma exists_pow_mul_mem (r : SInt 𝔪) : ∃ N : ℕ, ∀ w ∈ 𝔪 ^ N, ∃ c : 𝓞 F,
    algebraMap (𝓞 F) (SInt 𝔪) w * r = algebraMap (𝓞 F) (SInt 𝔪) c := by
  obtain ⟨b, d, hd, hbd⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (r : F)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  set N := Ideal.absNorm (Ideal.span {d}) with hN
  refine ⟨N, fun w hw => ?_⟩
  have hint : ∀ v : HeightOneSpectrum (𝓞 F),
      v.valuation F (algebraMap (𝓞 F) F w * (r : F)) ≤ 1 := by
    intro v
    by_cases hv : v ∈ placesOf 𝔪
    · have hvm : 𝔪 ≤ v.asIdeal := hv
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
        rw [C3I.val_alg, ← not_le, v.intValuation_le_pow_iff_mem]; exact hdN
      have hvw : v.valuation F (algebraMap (𝓞 F) F w) ≤ exp (-(N : ℤ)) := by
        rw [C3I.val_alg, v.intValuation_le_pow_iff_mem]
        exact Ideal.pow_right_mono hvm N hw
      have hdpos : v.valuation F (algebraMap (𝓞 F) F d) ≠ 0 := ne_zero_of_lt hvd
      have hxd : (r : F) * algebraMap (𝓞 F) F d = algebraMap (𝓞 F) F b := by
        rw [← hbd, div_mul_cancel₀]
        exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hd0
      have key : v.valuation F (algebraMap (𝓞 F) F w * (r : F)) *
          v.valuation F (algebraMap (𝓞 F) F d) ≤ 1 * v.valuation F (algebraMap (𝓞 F) F d) := by
        rw [← map_mul, show algebraMap (𝓞 F) F w * (r : F) * algebraMap (𝓞 F) F d =
          algebraMap (𝓞 F) F b * algebraMap (𝓞 F) F w by rw [mul_assoc, hxd]; ring, map_mul]
        exact mul_le_mul' (v.valuation_le_one b) (hvw.trans hvd.le)
      exact C3I.le_of_mul_le_mul_ne key hdpos
    · rw [map_mul]
      exact mul_le_one' (v.valuation_le_one w) (r.2 v hv)
  obtain ⟨c, hc⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F _ hint
  refine ⟨c, Subtype.ext ?_⟩
  rw [Subalgebra.coe_mul, C3I.coe_alg, C3I.coe_alg, hc]

end ArtinPrimitiveRoots.L2B
end

section
-- module Solutions.Artin.KP.S_Basic
/-!
# WP-S, part 1: `S_f`-adic smallness, norms, the pairing `⟨·,·⟩` on `F`, rows of `SL₂(R)`

* `Small 𝔪 N x`: `v(x) ≤ exp(-N)` at every `v ∣ 𝔪` (`N : ℤ`; `N < 0` means "bounded").
* `absS 𝔪 x = |x|_{S_f}`, `normS 𝔪 c d = ‖(c,d)‖ = ∏_{v ∣ 𝔪} max(|c|_v, |d|_v)`.
* `brk ι P 𝔪 x y = ⟨x, y⟩ = ι (x, y)_S` for `x, y ≠ 0`, and `1` if `x = 0` or `y = 0`.
  With WP-A's orientation `⟨c, d⟩ = (d/c)(c/d)⁻¹` on coprime elements of `R` (`brk_reciprocity`).
* `sig`: Kubota's `σ_S` evaluated on a pair and a matrix, through `ι`.
* `Row 𝔪`: primitive pairs of `R = SInt 𝔪`; right action of `SL₂(R)`; scaling by `Rˣ`;
  `kappaRow` and its transformation laws (`kappaRow_act` is Lemma A5 on rows).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F]

/-! ### Smallness at the places of `S_f` -/

/-! ### Absolute values at `S_f` -/

/-! ### The pairing `⟨x, y⟩ = ι (x, y)_S` on `F` -/

/-! ### Kubota's `σ_S` on a pair and a matrix -/

@[simp] theorem Xs_zero (d : F) : Xs 0 d = d := by simp [Xs]

/-! ### Primitive rows -/

variable {𝔪 : Ideal (𝓞 F)}

/-- Units of `R` are units at every exterior place. -/
theorem unit_val_eq_one (ε : (SInt 𝔪)ˣ) (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) :
    v.valuation F ((ε : SInt 𝔪) : F) = 1 := by
  have h1 := sInt_val_le_one (ε : SInt 𝔪) v hv
  have h2 := sInt_val_le_one ((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) v hv
  have h3 : ((ε : SInt 𝔪) : F) * (((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = 1 := by
    rw [← MulMemClass.coe_mul, ε.mul_inv]
    rfl
  exact (val_eq_one_of_mul _ h1 h2 (by rw [h3, map_one])).1

/-! ### The Kubota symbol on rows -/

/-! ### The matrices `w` and `n(t)` -/

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.S2_Symbol
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

open ArtinKP.A ArtinKP.S ArtinKP.E

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- Elements of `R` with no common exterior prime are coprime. -/
theorem isCoprime_of_val (h𝔪 : 𝔪 ≠ ⊥) {d c : SInt 𝔪} (hc : c ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ v.asIdeal →
      v.valuation F (d : F) = 1 ∨ v.valuation F (c : F) = 1) : IsCoprime d c := by
  rw [← Ideal.isCoprime_span_singleton_iff, Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal _ hne
  have hdM : d ∈ M := hJM (Ideal.mem_sup_left (Ideal.mem_span_singleton_self d))
  have hcM : c ∈ M := hJM (Ideal.mem_sup_right (Ideal.mem_span_singleton_self c))
  set Q : Ideal (𝓞 F) := M.comap (algebraMap (𝓞 F) (SInt 𝔪)) with hQ
  have hQp : Q.IsPrime := Ideal.comap_isPrime _ M
  have hinj : Function.Injective (algebraMap (𝓞 F) (SInt 𝔪)) := by
    intro a b hab
    have := congrArg (fun x : SInt 𝔪 => (x : F)) hab
    exact FaithfulSMul.algebraMap_injective (𝓞 F) F this
  have hQ0 : Q ≠ ⊥ := by
    obtain ⟨N, hN⟩ := L2B.exists_pow_mul_mem (𝔪 := 𝔪) c
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (pow_ne_zero N h𝔪)
    obtain ⟨c₀, hc₀⟩ := hN w hw
    have hmem : c₀ ∈ Q := by
      rw [hQ, Ideal.mem_comap, ← hc₀]
      exact M.mul_mem_left _ hcM
    have hc₀0 : c₀ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hc₀
      rcases mul_eq_zero.mp hc₀ with h0 | h0
      · exact hw0 (hinj (by rw [h0, map_zero]))
      · exact hc h0
    intro hbot
    rw [hbot] at hmem
    exact hc₀0 ((Submodule.mem_bot _).mp hmem)
  set v : HeightOneSpectrum (𝓞 F) := ⟨Q, hQp, hQ0⟩ with hv
  have hmapQ : Q.map (algebraMap (𝓞 F) (SInt 𝔪)) ≤ M := Ideal.map_le_iff_le_comap.2 le_rfl
  have hext : ¬ 𝔪 ≤ v.asIdeal := by
    intro hle
    have : 𝔪.map (algebraMap (𝓞 F) (SInt 𝔪)) ≤ M := (Ideal.map_mono hle).trans hmapQ
    rw [C0R.map_self_eq_top 𝔪 h𝔪, top_le_iff] at this
    exact hM.ne_top this
  have hmax : (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))).IsMaximal := C3I.isMaximal_map hext
  have hMeq : v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) = M := hmax.eq_of_le hM.ne_top hmapQ
  have hd1 := val_lt_one_of_mem_map v hext (hMeq ▸ hdM)
  have hc1 := val_lt_one_of_mem_map v hext (hMeq ▸ hcM)
  rcases h v hext with h1 | h1
  · rw [h1] at hd1; exact lt_irrefl _ hd1
  · rw [h1] at hc1; exact lt_irrefl _ hc1

theorem val_eq_one_of_isUnit {c : SInt 𝔪} (hc : IsUnit c) (v : HeightOneSpectrum (𝓞 F))
    (hv : ¬ 𝔪 ≤ v.asIdeal) : v.valuation F (c : F) = 1 := by
  obtain ⟨u, rfl⟩ := hc
  exact unit_val_eq_one u v hv

section symbol

variable (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

include P hG hz6 in
/-- **`(d/c) = 0` exactly when `d` and `c` are not coprime** (`c ≠ 0`). -/
theorem cubicExt_eq_zero_iff_oai (d c : SInt 𝔪) (hc : c ≠ 0) :
    cubicExt ι 𝔪 d c = 0 ↔ ¬ IsCoprime d c := by
  have hc0 : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)
  constructor
  · intro h0 hcop
    have hval := val_of_isCoprime hcop
    by_cases hd : d = 0
    · have hu : IsUnit c := by rwa [hd, isCoprime_zero_left] at hcop
      rw [cubicExt_of_unit_right ι d c (val_eq_one_of_isUnit hu)] at h0
      exact one_ne_zero h0
    · have h3 := cubicExt_pow_three ι P hG hz6 c d hc hd
        (fun v hv hne => (hval v hv).resolve_right hne)
      rw [h0] at h3
      norm_num at h3
  · intro hncop
    have hex : ∃ v : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ v.asIdeal ∧
        v.valuation F (d : F) ≠ 1 ∧ v.valuation F (c : F) ≠ 1 := by
      by_contra hcon
      apply hncop
      refine isCoprime_of_val hG.ne_bot hc fun v hv => ?_
      by_contra hh
      rw [not_or] at hh
      exact hcon ⟨v, hv, hh.1, hh.2⟩
    obtain ⟨v, hv, hd1, hc1⟩ := hex
    have hvs : v ∈ CubicPkg.extSupp 𝔪 (c : F) := (CubicPkg.mem_extSupp hc0 v).mpr ⟨hv, hc1⟩
    refine Finset.prod_eq_zero hvs ?_
    obtain ⟨p, hp⟩ := (hG.principal v.asIdeal).principal
    have hp' : Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := hp.symm
    have hdm : d ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
      mem_map_of_val_lt_one v hv p hp' d (lt_of_le_of_ne (sInt_val_le_one d v hv) hd1)
    have hs : sexticResidueSymbol ι 𝔪 v.asIdeal d = 0 := by
      unfold sexticResidueSymbol
      rw [if_pos (Ideal.Quotient.eq_zero_iff_mem.mpr hdm)]
    have hpos : 0 < ordv v (c : F) := by
      have hlt : v.valuation F (c : F) < 1 := lt_of_le_of_ne (sInt_val_le_one c v hv) hc1
      rw [val_eq_exp_ordv v hc0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
      omega
    rw [hs, zero_pow]
    have : 0 < (ordv v (c : F)).toNat := by omega
    omega

end symbol

end ArtinKP.S2
end
end

theorem solution.{u_1} : type_of% @ArtinKP.S2.cubicExt_eq_zero_iff_oai.{u_1} := @ArtinKP.S2.cubicExt_eq_zero_iff_oai.{u_1}
