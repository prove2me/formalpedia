-- Prove2me | Definitions.Def_RPLib_S4_CDPack10
-- name    : RPLib_S4_CDPack10
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T07:34:57.531556+00:00
-- url     : https://prove2.me/theorems/9e133f50-4344-42ec-929c-dc2345750be9
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 10 of 71
-- statement:
--   Part 10 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_Cone_ResCard`: S4-PD (4), E4B part 3a: residue field cardinalities at a level
--   * `Def_RP_Cone_ResBdry`: S4-PD (4), E4B part 3c: exact boundary residue degrees at a constant extension of a level
--   * `Def_RP_Cone_ResBdry2`: S4-PD (4), E4B part 3c (end): exact boundary residue degrees at a constant extension of a level
--   * `Def_RP_Cone_TwLoc`: S4-PD (4), arithmetic twist part A: the local twist of tame characters
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack09c
import Definitions.Def_RPLib_S3_SBUpper
import Definitions.Def_RPLib_S4_CDPack09b
import Definitions.Def_RPLib_S4_CDPack09
import Definitions.Def_RPLib_S4_CDPack02b
import Definitions.Def_RPLib_S4_TameInertiaCoef

/-!
# Curve-duality library package, part 10 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_Cone_ResCard`: S4-PD (4), E4B part 3a: residue field cardinalities at a level
* `Def_RP_Cone_ResBdry`: S4-PD (4), E4B part 3c: exact boundary residue degrees at a constant extension of a level
* `Def_RP_Cone_ResBdry2`: S4-PD (4), E4B part 3c (end): exact boundary residue degrees at a constant extension of a level
* `Def_RP_Cone_TwLoc`: S4-PD (4), arithmetic twist part A: the local twist of tame characters
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Cone_ResCard =====
section

/-!
# S4-PD (4), E4B part 3a: residue field cardinalities at a level

* `card_quot_eq_pow`: a finite residue field of a ring receiving a finite field `k1` has `#k1 ^ k` elements.
* `pow_card_pow_sub_mem`: `b ^ (#(B/y) ^ j) ≡ b` modulo a maximal ideal `y` with finite residue field.
* `card_quot_levelField`: if a field `M ⊇ R` contains a primitive `(q^m - 1)`-th root of unity (so `𝔽_{q^m} ⊆ M`),
  every finite residue field of the integral closure of `R` in `M` has `q^(m*k)` elements.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Residue

open CP4a

noncomputable section

/-- A finite quotient field of a ring receiving a finite field `k1` has `#k1 ^ k` elements. -/
theorem card_quot_eq_pow {B k1 : Type} [CommRing B] [Field k1] [Fintype k1] (φ : k1 →+* B) (y : Ideal B)
    [y.IsMaximal] [Finite (B ⧸ y)] : ∃ k : ℕ, Nat.card (B ⧸ y) = Fintype.card k1 ^ k := by
  letI : Field (B ⧸ y) := Ideal.Quotient.field y
  letI : Algebra k1 (B ⧸ y) := ((Ideal.Quotient.mk y).comp φ).toAlgebra
  letI : Fintype (B ⧸ y) := Fintype.ofFinite _
  exact ⟨Module.finrank k1 (B ⧸ y), by rw [Nat.card_eq_fintype_card]; exact Module.card_eq_pow_finrank⟩

/-- `b ^ (#(B/y) ^ j) ≡ b` modulo a maximal ideal `y` with finite residue field. -/
theorem pow_card_pow_sub_mem {B : Type} [CommRing B] (y : Ideal B) [y.IsMaximal] [Finite (B ⧸ y)] (j : ℕ)
    (b : B) : b ^ (Nat.card (B ⧸ y) ^ j) - b ∈ y := by
  letI : Field (B ⧸ y) := Ideal.Quotient.field y
  letI : Fintype (B ⧸ y) := Fintype.ofFinite _
  rw [← Ideal.Quotient.eq, map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card_pow]

variable {Fq : Type} [Field Fq] [Fintype Fq]

/-- Elements of `𝔽_{q^m} ⊆ M` are integral over any `R` with `Fq → R → M`. -/
theorem isIntegral_of_mem_levelField {R M : Type} [CommRing R] [Field M] [Algebra R M] [Algebra Fq R] [Algebra Fq M]
    [IsScalarTower Fq R M] {m : ℕ} (hm : 0 < m) (x : levelField Fq M m) : IsIntegral R (x : M) := by
  have hq1 : 1 < Fintype.card Fq ^ m := Nat.one_lt_pow hm.ne' Fintype.one_lt_card
  have hx : (x : M) ^ (Fintype.card Fq ^ m) = x := mem_levelField.1 x.2
  have h1 : IsIntegral Fq (x : M) := ⟨X ^ (Fintype.card Fq ^ m) - X,
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hq1), by simp [hx]⟩
  exact h1.tower_top

/-- **Finite residue fields at a level containing `𝔽_{q^m}`** have `q^(m*k)` elements. -/
theorem card_quot_levelField {R M : Type} [CommRing R] [Field M] [Algebra R M] [Algebra Fq R] [Algebra Fq M]
    [IsScalarTower Fq R M] {m : ℕ} (hm : 0 < m) {ζ : M} (hζ : IsPrimitiveRoot ζ (Fintype.card Fq ^ m - 1))
    (y : Ideal (integralClosure R M)) [y.IsMaximal] [Finite (integralClosure R M ⧸ y)] :
    ∃ k : ℕ, Nat.card (integralClosure R M ⧸ y) = Fintype.card Fq ^ (m * k) := by
  let φ : levelField Fq M m →+* integralClosure R M :=
    { toFun := fun x => ⟨(x : M), isIntegral_of_mem_levelField (R := R) hm x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hc := card_levelField (k0 := Fq) hm hζ
  haveI : Finite (levelField Fq M m) := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  letI : Fintype (levelField Fq M m) := Fintype.ofFinite _
  obtain ⟨k, hk⟩ := card_quot_eq_pow φ y
  refine ⟨k, ?_⟩
  rw [hk, ← Nat.card_eq_fintype_card, hc, pow_mul]

end

end Residue
end RamanujanPetersson

end

-- ===== S4.Def_RP_Cone_ResBdry =====
section

/-!
# S4-PD (4), E4B part 3c: exact boundary residue degrees at a constant extension of a level

S3 setting: a function field `F / 𝔽_q`, the chart `(Rfin, F, Rinf)` and a finite level `L ≤ K_U`.
* `hasFiniteQuotients_of_finiteQuot`: the S3 finiteness class gives Mathlib's `Ring.HasFiniteQuotients`.
* `finite_card_quot_sup`: `card_quot_sup_le` together with finiteness of the residue field.
* `exists_bdry_pow`: one `m0 > 0` with `y ^ (q ^ (m0 j)) ≡ y` modulo every boundary prime of `L`.
* `exists_prim_sup`: a level containing `K(𝔽_{p^(e m)})` contains a primitive `(q^m - 1)`-th root of unity.
* (`card_bdry_sup`, exact boundary degrees, is in `Def_RP_Cone_ResBdry2`.)
* `card_fin_level`: every finite residue field of a level containing `𝔽_{q^m}` has `q^(m k)` elements.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IsDedekindDomain

namespace RamanujanPetersson
namespace Residue

open CurveCoh GalCover Kummer CP4a

noncomputable section

theorem hasFiniteQuotients_of_finiteQuot {S : Type*} [CommRing S] [IsDedekindDomain S]
    [Places.FiniteQuot S] : Ring.HasFiniteQuotients S where
  finiteQuotient {I} hI := by
    obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    have := Places.FiniteQuot.finite (S := S) a ha0
    exact Finite.of_surjective _
      (Ideal.Quotient.factor_surjective ((Ideal.span_singleton_le_iff_mem _).mpr haI))

section Chart

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {R0 : Type} [CommRing R0] [Algebra R0 K]
variable {p : ℕ} [hp : Fact p.Prime] [CharP K p]

set_option synthInstance.maxHeartbeats 400000 in
/-- `card_quot_sup_le` with finiteness of the residue field. -/
theorem finite_card_quot_sup [Ring.HasFiniteQuotients R0] [Nontrivial R0]
    {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K) [FiniteDimensional K L]
    {k : ℕ} (hk : 0 < k) (hCU : constLevel K p k ≤ maxUnram A K) (P : Ideal (proChart A K R0)) [P.IsPrime]
    (hP : P ≠ ⊥) (hres : ∀ y : integralClosure R0 L, y ^ (p ^ k) - y ∈ P.comap (inclU R0 hLU)) :
    Finite (integralClosure R0 ↥(L ⊔ constLevel K p k) ⧸ P.comap (inclU R0 (sup_le hLU hCU))) ∧
    Nat.card (integralClosure R0 ↥(L ⊔ constLevel K p k) ⧸ P.comap (inclU R0 (sup_le hLU hCU))) ≤ p ^ k := by
  have hP0 : P.under R0 ≠ ⊥ := by
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hxP (Algebra.IsIntegral.isIntegral x)
  obtain ⟨h, hhL, hfr⟩ := exists_frob_level hLU P hP0 k hres
  have hL' := mem_fix_sup hLU hCU hhL (mem_fix_constLevel hk hCU hfr)
  set w := P.comap (inclU R0 (sup_le hLU hCU)) with hw
  have hwu : w.comap (algebraMap R0 (integralClosure R0 ↥(L ⊔ constLevel K p k))) = P.under R0 := by
    ext r
    show inclU R0 (sup_le hLU hCU) (algebraMap R0 _ r) ∈ P ↔ algebraMap R0 (proChart A K R0) r ∈ P
    rw [AlgHom.commutes]
  haveI : w.IsPrime := Ideal.comap_isPrime _ _
  haveI : w.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R0) w
    (by rw [hwu]; exact Ring.HasFiniteQuotients.maximalOfPrime hP0)
  letI : Field (integralClosure R0 ↥(L ⊔ constLevel K p k) ⧸ w) := Ideal.Quotient.field w
  refine card_le_of_pow_eq (one_lt_pow_p hk) fun z => ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [← map_pow]
  exact Ideal.Quotient.eq.2 (pow_sub_mem_of_fix (sup_le hLU hCU) hfr hL' y)

end Chart

section Level

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 400000 in
/-- **A uniform boundary exponent at a level**: one `m0 > 0` with `y ^ (q ^ (m0 j)) ≡ y` modulo every boundary
prime of `L` (all boundary residue degrees divide `m0`). -/
theorem exists_bdry_pow (L : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F L]
    [Algebra.IsSeparable F L] :
    ∃ m0 : ℕ, 0 < m0 ∧ ∀ w : Ideal (integralClosure (Places.Rinf Fq F) L), w.IsPrime → w ≠ ⊥ →
      ∀ (j : ℕ) (y : integralClosure (Places.Rinf Fq F) L), y ^ (Fintype.card Fq ^ (m0 * j)) - y ∈ w := by
  classical
  refine ⟨∏ P ∈ (ZetaSB.finite_infPlaces Fq L).toFinset, Places.deg Fq P,
    Finset.prod_pos fun P _ => Places.deg_pos Fq P, fun w hw hw0 j y => ?_⟩
  haveI := hw
  obtain ⟨x, hxw, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hw0
  have hQ0 : w.comap (infEquivM Fq L) ≠ ⊥ := by
    intro h
    have h1 : (infEquivM Fq L).symm x ∈ w.comap (infEquivM Fq L) := by
      rw [Ideal.mem_comap, RingEquiv.apply_symm_apply]
      exact hxw
    rw [h, Ideal.mem_bot] at h1
    exact hx0 (by simpa using congrArg (infEquivM Fq L) h1)
  obtain ⟨P, hPQ⟩ : ∃ P : HeightOneSpectrum (Places.Rinf Fq L), P.asIdeal = w.comap (infEquivM Fq L) :=
    ⟨⟨_, Ideal.comap_isPrime _ _, hQ0⟩, rfl⟩
  have hPm : P.asIdeal.IsMaximal := P.isMaximal
  have hPf : Finite (Places.Rinf Fq L ⧸ P.asIdeal) := Places.finite_residue P
  obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem (fun P => Places.deg Fq P) (ZetaSB.mem_infPlaces P)
  rw [hd]
  have h1 := pow_card_pow_sub_mem P.asIdeal (d * j) ((infEquivM Fq L).symm y)
  rw [Places.card_residue_eq Fq P, ← pow_mul, ← mul_assoc, hPQ] at h1
  have h2 := Ideal.mem_comap.1 h1
  rwa [map_sub, map_pow, RingEquiv.apply_symm_apply] at h2

variable {Fq}

/-- **Finite residue fields at a level containing `𝔽_{q^m}`** (the hypothesis `hdf` of `dvd_sum_bdry`). -/
theorem card_fin_level (M : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F M]
    [Algebra.IsSeparable F M] [IsDedekindDomain (integralClosure (Places.Rfin Fq F) M)] {m : ℕ} (hm : 0 < m)
    {ζ : M} (hζ : IsPrimitiveRoot ζ (Fintype.card Fq ^ m - 1))
    (y : HeightOneSpectrum (integralClosure (Places.Rfin Fq F) M)) :
    ∃ k : ℕ, Nat.card (integralClosure (Places.Rfin Fq F) M ⧸ y.asIdeal) = Fintype.card Fq ^ (m * k) := by
  have hc := card_equiv' (S' := integralClosure (Places.Rfin Fq F) M) (finEquivM Fq M) ((HeightOneSpectrum.equivOfRingEquiv (finEquivM Fq M)).symm y)
  rw [Equiv.apply_symm_apply] at hc
  haveI : Finite (integralClosure (Places.Rfin Fq F) M ⧸ y.asIdeal) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact Nat.card_pos.ne')
  haveI : y.asIdeal.IsMaximal := y.isMaximal
  exact card_quot_levelField (R := Places.Rfin Fq F) hm hζ y.asIdeal

variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable (hζc : ∀ a, 0 < a → ∃ z : maxUnram (Places.Rfin Fq F) F, IsPrimitiveRoot z ((p ^ e) ^ a - 1))

include hq he hζc in
/-- A level containing `K(𝔽_{p^(e m)})` contains a primitive `(q^m - 1)`-th root of unity. -/
theorem exists_prim_sup {m : ℕ} (hm : 0 < m) {M : IntermediateField F (AlgebraicClosure F)}
    (hM : constLevel F p (e * m) ≤ M) : ∃ ζ : M, IsPrimitiveRoot ζ (Fintype.card Fq ^ m - 1) := by
  obtain ⟨z, hz⟩ := hζc m hm
  have hz' : IsPrimitiveRoot ((maxUnram (Places.Rfin Fq F) F).val z) ((p ^ e) ^ m - 1) :=
    hz.map_of_injective (maxUnram (Places.Rfin Fq F) F).val.injective
  have hpos : 1 ≤ (p ^ e) ^ m :=
    Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))
  have h1 : ((maxUnram (Places.Rfin Fq F) F).val z) ^ (p ^ (e * m)) = (maxUnram (Places.Rfin Fq F) F).val z := by
    rw [pow_mul, ← Nat.sub_add_cancel hpos, pow_succ, hz'.pow_eq_one, one_mul]
  have hmem := hM (mem_constLevel (Nat.mul_pos he hm) h1)
  refine ⟨⟨_, hmem⟩, ?_⟩
  rw [hq]
  exact IsPrimitiveRoot.of_map_of_injective (f := M.val) hz' M.val.injective

end Level

end

end Residue
end RamanujanPetersson

end

-- ===== S4.Def_RP_Cone_ResBdry2 =====
section

/-!
# S4-PD (4), E4B part 3c (end): exact boundary residue degrees at a constant extension of a level

* `card_quot_sup_bdry` (any chart): if `y ^ (p^k) ≡ y` modulo every nonzero prime of `B_L`, every nonzero prime `w` of
  `B_{L ⊔ K(𝔽_{p^k})}` is maximal with a finite residue field of at most `p^k` elements.
* `card_bdry_sup` (S3 chart, `R0 = O_∞`): if `y ^ (q^m) ≡ y` modulo every boundary prime of `L`, every boundary residue
  field of `L ⊔ K(𝔽_{p^(e m)})` has exactly `q^m` elements (the hypothesis `hdi` of `dvd_sum_bdry`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IsDedekindDomain

namespace RamanujanPetersson
namespace Residue

open CurveCoh GalCover Kummer CP4a

noncomputable section

section Chart

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {R0 : Type} [CommRing R0] [Algebra R0 K]
variable {p : ℕ} [hp : Fact p.Prime] [CharP K p]

set_option synthInstance.maxHeartbeats 400000 in
/-- **Boundary residue fields of a constant extension** (any chart): if `y ^ (p^k) ≡ y` modulo every nonzero prime of
`B_L`, every nonzero prime of `B_{L ⊔ K(𝔽_{p^k})}` is maximal with at most `p^k` residues. -/
theorem card_quot_sup_bdry [Ring.HasFiniteQuotients R0] [IsDomain R0] [IsIntegrallyClosed R0]
    [IsFractionRing R0 K] {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)
    [FiniteDimensional K L] {k : ℕ} (hk : 0 < k) (hCU : constLevel K p k ≤ maxUnram A K)
    (hres : ∀ w : Ideal (integralClosure R0 L), w.IsPrime → w ≠ ⊥ →
      ∀ y : integralClosure R0 L, y ^ (p ^ k) - y ∈ w)
    (w : Ideal (integralClosure R0 ↥(L ⊔ constLevel K p k))) [hwP : w.IsPrime] (hw : w ≠ ⊥) :
    Finite (integralClosure R0 ↥(L ⊔ constLevel K p k) ⧸ w) ∧
      Nat.card (integralClosure R0 ↥(L ⊔ constLevel K p k) ⧸ w) ≤ p ^ k ∧ w.IsMaximal := by
  obtain ⟨P, hP, hPw⟩ := exists_prime_comap_eq (R0 := R0) (S := proChart A K R0)
    (inclU R0 (sup_le hLU hCU)) (inclU_injective _) w
  have := hP
  have hinj := algebraMap_proChart_injective (A := A) (K := K) (R0 := R0)
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    apply hw
    rw [← hPw]
    exact Ideal.comap_bot_of_injective _ (inclU_injective _)
  have hPu : P.under R0 ≠ ⊥ := by
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hxP (Algebra.IsIntegral.isIntegral x)
  obtain ⟨r, hrP, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPu
  have hPL : P.comap (inclU R0 hLU) ≠ ⊥ := by
    intro h
    have h1 : algebraMap R0 (integralClosure R0 L) r ∈ P.comap (inclU R0 hLU) := by
      rw [Ideal.mem_comap, AlgHom.commutes]; exact hrP
    rw [h, Ideal.mem_bot] at h1
    have h2 := congrArg (inclU R0 hLU) h1
    rw [AlgHom.commutes, map_zero] at h2
    exact hr0 (hinj (h2.trans (map_zero _).symm))
  have hres' : ∀ y : integralClosure R0 L, y ^ (p ^ k) - y ∈ P.comap (inclU R0 hLU) :=
    hres _ (Ideal.comap_isPrime _ _) hPL
  obtain ⟨hfin, hle⟩ := finite_card_quot_sup hLU hk hCU P hP0 hres'
  have hwu : w.comap (algebraMap R0 (integralClosure R0 ↥(L ⊔ constLevel K p k))) = P.under R0 := by
    rw [← hPw]
    ext r
    show inclU R0 (sup_le hLU hCU) (algebraMap R0 _ r) ∈ P ↔ algebraMap R0 (proChart A K R0) r ∈ P
    rw [AlgHom.commutes]
  rw [hPw] at hfin hle
  exact ⟨hfin, hle, Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R0) w
    (by rw [hwu]; exact Ring.HasFiniteQuotients.maximalOfPrime hPu)⟩

end Chart

section Level

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable (hζc : ∀ a, 0 < a → ∃ z : maxUnram (Places.Rfin Fq F) F, IsPrimitiveRoot z ((p ^ e) ^ a - 1))

include hq he hζc in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- **Exact boundary residue degrees**: if `y ^ (q^m) ≡ y` modulo every boundary prime of `L`, every boundary residue
field of `L ⊔ K(𝔽_{p^(e m)})` has exactly `q^m` elements (the hypothesis `hdi` of `dvd_sum_bdry`). The place is a
`HeightOneSpectrum` point (bare ideal binders lose `HasQuotient` in this setting, probe 11-14). -/
theorem card_bdry_sup {L : IntermediateField F (AlgebraicClosure F)} (hLU : L ≤ maxUnram (Places.Rfin Fq F) F)
    [FiniteDimensional F L] {m : ℕ} (hm : 0 < m)
    (hres : ∀ w : Ideal (integralClosure (Places.Rinf Fq F) L), w.IsPrime → w ≠ ⊥ →
      ∀ y : integralClosure (Places.Rinf Fq F) L, y ^ (Fintype.card Fq ^ m) - y ∈ w)
    (hCU : constLevel F p (e * m) ≤ maxUnram (Places.Rfin Fq F) F)
    [IsDedekindDomain (integralClosure (Places.Rinf Fq F) ↥(L ⊔ constLevel F p (e * m)))]
    (w' : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(L ⊔ constLevel F p (e * m)))) :
    Nat.card (integralClosure (Places.Rinf Fq F) ↥(L ⊔ constLevel F p (e * m)) ⧸ w'.asIdeal) =
      Fintype.card Fq ^ m := by
  have := hasFiniteQuotients_of_finiteQuot (S := Places.Rinf Fq F)
  have : w'.asIdeal.IsPrime := w'.isPrime
  have hk : 0 < e * m := Nat.mul_pos he hm
  have hres' : ∀ w : Ideal (integralClosure (Places.Rinf Fq F) L), w.IsPrime → w ≠ ⊥ →
      ∀ y : integralClosure (Places.Rinf Fq F) L, y ^ (p ^ (e * m)) - y ∈ w := fun w hw hw0 y => by
    rw [pow_mul, ← hq]
    exact hres w hw hw0 y
  obtain ⟨hfin0, hle0, -⟩ := card_quot_sup_bdry hLU hk hCU hres' w'.asIdeal (hwP := w'.isPrime) w'.ne_bot
  -- restate along the `HeightOneSpectrum` instance path (the generic one differs at instance transparency)
  have hfin : Finite (integralClosure (Places.Rinf Fq F) ↥(L ⊔ constLevel F p (e * m)) ⧸ w'.asIdeal) := hfin0
  have hle : Nat.card (integralClosure (Places.Rinf Fq F) ↥(L ⊔ constLevel F p (e * m)) ⧸ w'.asIdeal) ≤
      p ^ (e * m) := hle0
  have : w'.asIdeal.IsMaximal := w'.isMaximal
  obtain ⟨ζ, hζ⟩ := exists_prim_sup hq he hζc hm (le_sup_right : constLevel F p (e * m) ≤ L ⊔ _)
  obtain ⟨k, hk'⟩ := card_quot_levelField (R := Places.Rinf Fq F) hm hζ w'.asIdeal
  letI : Field (integralClosure (Places.Rinf Fq F) ↥(L ⊔ constLevel F p (e * m)) ⧸ w'.asIdeal) :=
    Ideal.Quotient.field w'.asIdeal
  have h1 : 1 < Nat.card (integralClosure (Places.Rinf Fq F) ↥(L ⊔ constLevel F p (e * m)) ⧸ w'.asIdeal) :=
    Finite.one_lt_card
  have hq2 : 1 < Fintype.card Fq := Fintype.one_lt_card
  rw [hk'] at h1 hle ⊢
  rw [pow_mul p e m, ← hq] at hle
  have hk1 : m * k ≤ m * 1 := by
    rw [mul_one]
    by_contra hc
    exact absurd hle (not_le.2 (pow_lt_pow_right₀ hq2 (not_le.1 hc)))
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at h1
  have : k = 1 := by
    have := Nat.le_of_mul_le_mul_left hk1 hm
    omega
  rw [this, mul_one]

end Level

end

end Residue
end RamanujanPetersson

end

-- ===== S4.Def_RP_Cone_TwLoc =====
section

/-!
# S4-PD (4), arithmetic twist part A: the local twist of tame characters

For `J ≤ I(Q)` with `σ ^ (p^k d) ∈ J` on `I(Q)` (as in `tame_inertia_le`), and `φ` stabilising `Q` with
`φ ζ = ζ ^ q` (`ζ` a primitive `N d`-th root of unity fixed by inertia):

* `exists_twist_char`: a generator `θ : J → ℤ/N` of the locally constant characters with
  `θ (φ σ φ⁻¹) = q • θ σ` (the cyclotomic twist, from the twist clause of `exists_tame_char` at level `N d`).
* `twist_hom`: every locally constant homomorphism `χ : J → M` to an abelian group killed by `N` satisfies
  `χ (φ σ φ⁻¹) = q • χ σ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace TameInertia

open CurveCoh IsDedekindDomain Kummer

noncomputable section

section Alg

/-- An additive character takes `σ ^ n` to `n • r σ`. -/
theorem char_pow {G : Type} [Group G] {B : Type} [AddCommGroup B] (r : G → B)
    (hr : ∀ σ τ, r (σ * τ) = r σ + r τ) (σ : G) (n : ℕ) : r (σ ^ n) = n • r σ := by
  have h1 : r 1 = 0 := by
    have h := hr 1 1
    rw [mul_one] at h
    simpa using h
  induction n with
  | zero => rw [pow_zero, h1, zero_nsmul]
  | succ n ih => rw [pow_succ, hr, ih, succ_nsmul]

theorem val_nsmul_nsmul {N : ℕ} [NeZero N] {M : Type*} [AddCommGroup M] (hM : ∀ m : M, N • m = 0) (q : ℕ)
    (z : ZMod N) (m : M) : (q • z).val • m = q • z.val • m := by
  have e : q • z = ((q * z.val : ℕ) : ZMod N) := by
    rw [nsmul_eq_mul, Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [e, ZMod.val_natCast, nsmul_mod_eq hM, mul_nsmul']

end Alg

variable {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- **Local twist.** For `J ≤ I(Q)` as in `tame_inertia_le` and `φ` stabilising `Q` with `φ ζ = ζ ^ q`, there is a
generator `θ` of the locally constant characters `J → ℤ/N` with `θ (φ σ φ⁻¹) = q • θ σ`. -/
theorem exists_twist_char {Q : Ideal (proChart A K R0)} (hQ : IsBdryPrime A K R0 Q)
    [Ring.HasFiniteQuotients R0] {p : ℕ} [Fact p.Prime] [CharP K p] {N d : ℕ} [NeZero N] [NeZero d]
    (hNA : IsUnit ((N * d : ℕ) : A)) (hNR : IsUnit ((N * d : ℕ) : R0)) {ζ : maxUnram A K}
    (hζ : IsPrimitiveRoot ζ (N * d)) (hζI : ∀ σ ∈ Q.inertia (Pi1 A K), σ ζ = ζ)
    (x : HeightOneSpectrum R0) (hx : x.asIdeal = Q.comap (algebraMap R0 (proChart A K R0)))
    {a : A} (ha : 1 < x.valuation K (algebraMap A K a))
    {J : Subgroup (Pi1 A K)} (hJ : J ≤ Q.inertia (Pi1 A K)) (k : ℕ)
    (hd : ∀ σ ∈ Q.inertia (Pi1 A K), σ ^ (p ^ k * d) ∈ J)
    (φ : Pi1 A K) (hφ : ∀ b : proChart A K R0, φ • b ∈ Q ↔ b ∈ Q) (q : ℕ) (hφζ : φ ζ = ζ ^ q) :
    ∃ θ : J → ZMod N, ∃ τ₀ : J, IsLocallyConstant θ ∧ (∀ σ τ, θ (σ * τ) = θ σ + θ τ) ∧ θ τ₀ = 1 ∧
      (∀ χ : J → ZMod N, IsLocallyConstant χ → (∀ σ τ, χ (σ * τ) = χ σ + χ τ) →
        ∃ c : ZMod N, ∀ σ, χ σ = c * θ σ) ∧
      ∀ σ (hσ : σ ∈ J) (hσ' : φ * σ * φ⁻¹ ∈ J), θ ⟨φ * σ * φ⁻¹, hσ'⟩ = q • θ ⟨σ, hσ⟩ := by
  have : NeZero (N * d) := ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne d)⟩
  obtain ⟨θ', hθc, hθm, ⟨σ₀, hθ1⟩, -, htw⟩ := exists_tame_char (p := p) hQ hNA hNR hζ hζI x hx ha
  let ι : J → Q.inertia (Pi1 A K) := fun σ => ⟨σ, hJ σ.2⟩
  have hιc : Continuous ι := continuous_subtype_val.subtype_mk _
  let r : J → ZMod (N * d) := fun σ => θ' (ι σ)
  have hr : ∀ σ τ, r (σ * τ) = r σ + r τ := fun σ τ => hθm (ι σ) (ι τ)
  have hpow : ∀ n : ℕ, θ' (σ₀ ^ n) = (n : ZMod (N * d)) := by
    intro n
    rw [char_pow θ' hθm σ₀ n, hθ1, nsmul_eq_mul, mul_one]
  let g : J := ⟨(σ₀ : Pi1 A K) ^ (p ^ k * d), hd _ σ₀.2⟩
  have hg : r g = ((p ^ k * d : ℕ) : ZMod (N * d)) := by
    rw [← hpow]
    show θ' (ι g) = _
    congr 1
  have hp : Nat.Coprime p (N * d) := coprime_of_isUnit (K := K) hNA
  obtain ⟨f, hf, τ₀, hτ₀⟩ := exists_div_char (Fact.out : p.Prime).pos hp r hr hg
  let θ : J → ZMod N := fun σ => f (r σ)
  have hθm' : ∀ σ τ, θ (σ * τ) = θ σ + θ τ := hf
  have hθc' : IsLocallyConstant θ := (hθc.comp_continuous hιc).comp f
  have hN : IsUnit (N : R0) := by
    rw [Nat.cast_mul] at hNR
    exact isUnit_of_mul_isUnit_left hNR
  have hζN : IsPrimitiveRoot (ζ ^ d) N := IsPrimitiveRoot.pow (NeZero.pos _) hζ (mul_comm N d)
  have hζJ : ∀ σ ∈ J, σ (ζ ^ d) = ζ ^ d := fun σ hσ => by rw [map_pow, hζI σ (hJ hσ)]
  have hw : φ ζ = epow ζ ((q : ℕ) : ZMod (N * d)) := by
    rw [epow, ZMod.val_natCast, pow_mod_N hζ]
    exact hφζ
  refine ⟨θ, τ₀, hθc', hθm', hτ₀, fun χ hχc hχ => exists_eq_mul_of_surj
    (fun χ' hc' h' => exists_ne_eq_of_family_le hQ hN hζN hJ hζJ χ' hc' h') hθc' hθm' hτ₀ hχc hχ,
    fun σ hσ hσ' => ?_⟩
  -- `r (φ σ φ⁻¹) = q r σ = r (σ ^ q)`, then apply `f`
  have hc : φ⁻¹ * (φ * σ * φ⁻¹) * φ ∈ Q.inertia (Pi1 A K) := inertia_conj hφ (hJ hσ')
  have h1 := htw φ hφ ((q : ℕ) : ZMod (N * d)) hw (φ * σ * φ⁻¹) (hJ hσ')
  have e1 : (⟨φ⁻¹ * (φ * σ * φ⁻¹) * φ, hc⟩ : Q.inertia (Pi1 A K)) = ι ⟨σ, hσ⟩ :=
    Subtype.ext (by show φ⁻¹ * (φ * σ * φ⁻¹) * φ = σ; group)
  have h2 : r ⟨φ * σ * φ⁻¹, hσ'⟩ = r (⟨σ, hσ⟩ ^ q) := by
    rw [char_pow r hr, nsmul_eq_mul]
    show θ' ⟨φ * σ * φ⁻¹, hJ hσ'⟩ = _
    rw [h1, e1]
  show f (r ⟨φ * σ * φ⁻¹, hσ'⟩) = q • f (r ⟨σ, hσ⟩)
  rw [h2]
  exact char_pow θ hθm' ⟨σ, hσ⟩ q

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- **Local twist for `N`-torsion coefficients**: every locally constant homomorphism `χ : J → M` (`N M = 0`)
satisfies `χ (φ σ φ⁻¹) = q • χ σ` when `φ` stabilises `Q` and `φ ζ = ζ ^ q`. -/
theorem twist_hom {Q : Ideal (proChart A K R0)} (hQ : IsBdryPrime A K R0 Q)
    [Ring.HasFiniteQuotients R0] {p : ℕ} [Fact p.Prime] [CharP K p] {N d : ℕ} [NeZero N] [NeZero d]
    (hNA : IsUnit ((N * d : ℕ) : A)) (hNR : IsUnit ((N * d : ℕ) : R0)) {ζ : maxUnram A K}
    (hζ : IsPrimitiveRoot ζ (N * d)) (hζI : ∀ σ ∈ Q.inertia (Pi1 A K), σ ζ = ζ)
    (x : HeightOneSpectrum R0) (hx : x.asIdeal = Q.comap (algebraMap R0 (proChart A K R0)))
    {a : A} (ha : 1 < x.valuation K (algebraMap A K a))
    {J : Subgroup (Pi1 A K)} (hJ : J ≤ Q.inertia (Pi1 A K)) (k : ℕ)
    (hd : ∀ σ ∈ Q.inertia (Pi1 A K), σ ^ (p ^ k * d) ∈ J)
    (φ : Pi1 A K) (hφ : ∀ b : proChart A K R0, φ • b ∈ Q ↔ b ∈ Q) (q : ℕ) (hφζ : φ ζ = ζ ^ q)
    {M : Type*} [AddCommGroup M] (hM : ∀ m : M, N • m = 0) (χ : J → M) (hχc : IsLocallyConstant χ)
    (hχ : ∀ σ τ, χ (σ * τ) = χ σ + χ τ) (σ : Pi1 A K) (hσ : σ ∈ J) (hσ' : φ * σ * φ⁻¹ ∈ J) :
    χ ⟨φ * σ * φ⁻¹, hσ'⟩ = q • χ ⟨σ, hσ⟩ := by
  obtain ⟨θ, τ₀, -, -, hθ1, hgen, htw⟩ :=
    exists_twist_char (p := p) hQ hNA hNR hζ hζI x hx ha hJ k hd φ hφ q hφζ
  rw [eq_val_nsmul_of_gen hM hθ1 hgen χ hχc hχ, eq_val_nsmul_of_gen hM hθ1 hgen χ hχc hχ ⟨σ, hσ⟩,
    htw σ hσ hσ', val_nsmul_nsmul hM]

end

end TameInertia
end RamanujanPetersson

end


