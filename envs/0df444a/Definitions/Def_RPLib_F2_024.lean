-- Prove2me | Definitions.Def_RPLib_F2_024
-- name    : RPLib_F2_024
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T11:50:50.675877+00:00
-- url     : https://prove2.me/theorems/0a737b04-71fb-4f1a-bb01-84e1f0b0c4ea
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 024 of 70
-- statement:
--   File 024 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Cone_LevProd`: S4-PD (4), E4B part 1: the product formula at a finite level
--   * `S4.Def_RP_Cone_ResCard`: S4-PD (4), E4B part 3a: residue field cardinalities at a level
--   * `S4.Def_RP_Cone_ResBdry`: S4-PD (4), E4B part 3c: exact boundary residue degrees at a constant extension of a level
--   * `S4.Def_RP_Cone_ResBdry2`: S4-PD (4), E4B part 3c (end): exact boundary residue degrees at a constant extension of a level
--   * `S4.Def_RP_Cone_ResSum`: S4-PD (4), E4B part 4: the residue theorem at a level
--   * `S4.Def_RP_Cone_ResMax`: S4-PD (4), E4B part 5b: one normalised tame generator for all constant levels
--   * `S4.Def_RP_Cone_ResGlob`: S4-PD (4), E4B part 5c: the global residue theorem
--   * `S4.Def_RP_Cone_ExDef`: S4-PD (4), E4X part 1: the divisibility hypothesis for boundary divisors, and Kummer roots from it
--   * `S4.Def_RP_Cone_Exist`: S4-PD (4), E4X part 2: existence of global characters with prescribed residues
--   * `S4.Def_RP_Cone_ResStab`: S4-PD E4S arithmetic ResA, part 1: stabilisers in `π₁^geo` and Kummer characters under conjugation
--   * `S4.Def_RP_Cone_ResTr`: S4-PD E4S arithmetic ResA, part 2: transport of normalised generators under geometric conjugation
--   * `S4.Def_RP_Cone_ResCos`: S4-PD E4S arithmetic ResA, part 3: cover points as cosets (pure group theory)
--   * `S4.Def_RP_Cone_E4SInd`: S4-PD E4S, part 4: sections and induction cocycles
--   * `S4.Def_RP_TameInertia_Coef`: Tame inertia, part Coef: homomorphisms to `N`-torsion modules (S4-PD item (2), T9)
--   * `S4.Def_RP_Cone_E4SLoc`: S4-PD E4S, part 5a: local residue hypotheses from normalised generators
--   * `S4.Def_RP_Cone_E4SDat`: S4-PD E4S, part 5b: the residue hypotheses from local and cover-level data
--   * `S4.Def_RP_Cone_ResAsm`: S4-PD E4S arithmetic ResA, part 4: cover points and inertia in the S3 chart
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_023

/-!
# Ramanujan-Petersson curve library (flat edition), file 024 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Cone_LevProd`: S4-PD (4), E4B part 1: the product formula at a finite level
* `S4.Def_RP_Cone_ResCard`: S4-PD (4), E4B part 3a: residue field cardinalities at a level
* `S4.Def_RP_Cone_ResBdry`: S4-PD (4), E4B part 3c: exact boundary residue degrees at a constant extension of a level
* `S4.Def_RP_Cone_ResBdry2`: S4-PD (4), E4B part 3c (end): exact boundary residue degrees at a constant extension of a level
* `S4.Def_RP_Cone_ResSum`: S4-PD (4), E4B part 4: the residue theorem at a level
* `S4.Def_RP_Cone_ResMax`: S4-PD (4), E4B part 5b: one normalised tame generator for all constant levels
* `S4.Def_RP_Cone_ResGlob`: S4-PD (4), E4B part 5c: the global residue theorem
* `S4.Def_RP_Cone_ExDef`: S4-PD (4), E4X part 1: the divisibility hypothesis for boundary divisors, and Kummer roots from it
* `S4.Def_RP_Cone_Exist`: S4-PD (4), E4X part 2: existence of global characters with prescribed residues
* `S4.Def_RP_Cone_ResStab`: S4-PD E4S arithmetic ResA, part 1: stabilisers in `π₁^geo` and Kummer characters under conjugation
* `S4.Def_RP_Cone_ResTr`: S4-PD E4S arithmetic ResA, part 2: transport of normalised generators under geometric conjugation
* `S4.Def_RP_Cone_ResCos`: S4-PD E4S arithmetic ResA, part 3: cover points as cosets (pure group theory)
* `S4.Def_RP_Cone_E4SInd`: S4-PD E4S, part 4: sections and induction cocycles
* `S4.Def_RP_TameInertia_Coef`: Tame inertia, part Coef: homomorphisms to `N`-torsion modules (S4-PD item (2), T9)
* `S4.Def_RP_Cone_E4SLoc`: S4-PD E4S, part 5a: local residue hypotheses from normalised generators
* `S4.Def_RP_Cone_E4SDat`: S4-PD E4S, part 5b: the residue hypotheses from local and cover-level data
* `S4.Def_RP_Cone_ResAsm`: S4-PD E4S arithmetic ResA, part 4: cover points and inertia in the S3 chart
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Cone_LevProd =====
section

/-!
# S4-PD (4), E4B part 1: the product formula at a finite level

For a function field `F / Fq` (S3 setting) and a finite separable level `M / F` inside `F̄`, the places of `M` are
the primes of `B_M = integralClosure (Rfin Fq F) M` (finite) and `B∞_M = integralClosure (Rinf Fq F) M` (over `∞`).
* `valuation_equiv'`, `card_equiv'`: valuations and residue cardinalities are transported along a ring isomorphism of
  Dedekind domains with the same fraction field.
* `finEquivM`, `infEquivM`: `Rfin Fq M ≃+* B_M` and `Rinf Fq M ≃+* B∞_M` (same carrier in `M`).
* `dvd_sum_bdry` (residue sum at a level): if `N ∣ v_y(f)` at every finite place, every finite residue field has
  cardinality `(q^m)^k` and every boundary residue field has cardinality `q^m`, then `N ∣ Σ_w v_w(f)` over the
  boundary places. From the S3 product formula `degS_fin_add_degS_inf` for `M`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IsDedekindDomain

namespace RamanujanPetersson
namespace Residue

noncomputable section

section Transport

variable {S S' : Type*} [CommRing S] [IsDedekindDomain S] [CommRing S'] [IsDedekindDomain S']

variable {K : Type*} [Field K] [Algebra S K] [IsFractionRing S K] [Algebra S' K] [IsFractionRing S' K]

end Transport

section Level

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (M : IntermediateField F (AlgebraicClosure F))

variable [FiniteDimensional F M] [Algebra.IsSeparable F M]

variable [IsDedekindDomain (integralClosure (Places.Rfin Fq F) M)]
  [IsFractionRing (integralClosure (Places.Rfin Fq F) M) M]
  [IsDedekindDomain (integralClosure (Places.Rinf Fq F) M)]
  [IsFractionRing (integralClosure (Places.Rinf Fq F) M) M]

set_option maxHeartbeats 800000 in
/-- **Residue sum at a level**: `N ∣ Σ_w v_w(f)` over the boundary places of `M` when `N` divides `f`'s orders at all
finite places, every finite residue field has `(q^m)^k` elements and every boundary residue field `q^m`. -/
theorem dvd_sum_bdry {N m : ℕ} (hm : 0 < m) {f : M} (hf : f ≠ 0)
    (hfin : ∀ y : HeightOneSpectrum (integralClosure (Places.Rfin Fq F) M),
      (N : ℤ) ∣ WithZero.log (y.valuation M f))
    (hdf : ∀ y : HeightOneSpectrum (integralClosure (Places.Rfin Fq F) M),
      ∃ k : ℕ, Nat.card (integralClosure (Places.Rfin Fq F) M ⧸ y.asIdeal) = Fintype.card Fq ^ (m * k))
    (hdi : ∀ w : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) M),
      Nat.card (integralClosure (Places.Rinf Fq F) M ⧸ w.asIdeal) = Fintype.card Fq ^ m) :
    (N : ℤ) ∣ ∑ᶠ w : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) M),
      WithZero.log (w.valuation M f) := by
  have hq : 2 ≤ Fintype.card Fq := Fintype.one_lt_card
  have hpf := Places.degS_fin_add_degS_inf Fq M hf
  have hv1 : ∀ P : HeightOneSpectrum (Places.Rfin Fq M),
      (HeightOneSpectrum.equivOfRingEquiv (finEquivM Fq M) P).valuation M f = P.valuation M f :=
    fun P => valuation_equiv' _ (fun _ => rfl) P f
  have hv2 : ∀ P : HeightOneSpectrum (Places.Rinf Fq M),
      (HeightOneSpectrum.equivOfRingEquiv (infEquivM Fq M) P).valuation M f = P.valuation M f :=
    fun P => valuation_equiv' _ (fun _ => rfl) P f
  have hd1 : ∀ P : HeightOneSpectrum (Places.Rfin Fq M), ∃ k : ℕ, Places.deg Fq P = m * k := fun P => by
    obtain ⟨k, hk⟩ := hdf (HeightOneSpectrum.equivOfRingEquiv (finEquivM Fq M) P)
    refine ⟨k, Nat.pow_right_injective hq ?_⟩
    show Fintype.card Fq ^ Places.deg Fq P = Fintype.card Fq ^ (m * k)
    rw [← Places.card_residue_eq Fq P,
      ← card_equiv' (S' := integralClosure (Places.Rfin Fq F) M) (finEquivM Fq M) P]
    exact hk
  have hd2 : ∀ P : HeightOneSpectrum (Places.Rinf Fq M), Places.deg Fq P = m := fun P => by
    refine Nat.pow_right_injective hq ?_
    show Fintype.card Fq ^ Places.deg Fq P = Fintype.card Fq ^ m
    rw [← Places.card_residue_eq Fq P,
      ← card_equiv' (S' := integralClosure (Places.Rinf Fq F) M) (infEquivM Fq M) P]
    exact hdi _
  -- the finite part is divisible by `N * m`
  have h1 : ((N : ℤ) * m) ∣ Places.degS Fq (Places.divS (Places.Rfin Fq M) f) := by
    rw [Places.degS, Finsupp.sum]
    refine Finset.dvd_sum fun P _ => ?_
    obtain ⟨k, hk⟩ := hd1 P
    rw [Places.divS_apply, hk, Places.ord, ← hv1 P, Nat.cast_mul]
    exact mul_dvd_mul (dvd_neg.2 (hfin _)) (dvd_mul_right _ _)
  -- the boundary part is `m * (-Σ_w v_w(f))`
  have hs : (∑ᶠ w : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) M),
      WithZero.log (w.valuation M f)) =
      ∑ᶠ P : HeightOneSpectrum (Places.Rinf Fq M), WithZero.log (P.valuation M f) := by
    rw [← finsum_comp_equiv (HeightOneSpectrum.equivOfRingEquiv (infEquivM Fq M))]
    exact finsum_congr fun P => by rw [hv2 P]
  have hsub : Function.support (fun P : HeightOneSpectrum (Places.Rinf Fq M) => WithZero.log (P.valuation M f)) ⊆
      ↑(Places.divS (Places.Rinf Fq M) f).support := fun P hP => by
    rw [Finset.mem_coe, Finsupp.mem_support_iff, Places.divS_apply, Places.ord]
    exact neg_ne_zero.2 hP
  have h2 : Places.degS Fq (Places.divS (Places.Rinf Fq M) f) =
      (m : ℤ) * -∑ᶠ w : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) M),
        WithZero.log (w.valuation M f) := by
    rw [hs, finsum_eq_sum_of_support_subset _ hsub, Places.degS, Finsupp.sum, ← Finset.sum_neg_distrib,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [Places.divS_apply, hd2 P, Places.ord]
    ring
  rw [h2] at hpf
  have h3 : ((m : ℤ) * N) ∣ (m : ℤ) * ∑ᶠ w : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) M),
      WithZero.log (w.valuation M f) := by
    have he : (m : ℤ) * ∑ᶠ w : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) M),
        WithZero.log (w.valuation M f) = Places.degS Fq (Places.divS (Places.Rfin Fq M) f) := by
      linear_combination -hpf
    rw [he, mul_comm]
    exact h1
  exact (mul_dvd_mul_iff_left (by exact_mod_cast hm.ne')).1 h3

end Level

end

end Residue
end RamanujanPetersson


end

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

-- ===== S4.Def_RP_Cone_ResSum =====
section

/-!
# S4-PD (4), E4B part 4: the residue theorem at a level

* `comap_inclU_ne_bot`, `exists_bdry_comap_eq` (any chart): boundary primes of the pro-chart restrict to nonzero
  primes of `B_L`, and every nonzero prime of `B_L` is such a restriction (lying over).
* `eq_of_comap_eq_reps`, `exists_rep_comap_eq` (any chart): for representatives `Q t` of the
  `π₁^geo ∩ Gal(K_U/L)`-orbits of boundary primes, `t ↦ Q t ∩ B_L` is injective (when `L ⊇ K(𝔽_{p^k})` and
  `y ^ (p^k) ≡ y` at the boundary of `L`) and onto the nonzero primes of `B_L`.
* `dvd_sum_reps` (S3 chart, `R0 = O_∞`): if every boundary residue field of `L` has `q^m` elements and
  `L ⊇ F(𝔽_{q^m})`, then for `α ∈ K_U` with `α ^ N = b ∈ L`, `N ∣ Σ_t v_t(b)` over the representatives.
* `sum_reps_eq_zero`: the same for any `χ` with `χ(τ_t) = v_t(b) mod N` (normalised tame generators).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IsDedekindDomain
open scoped Pointwise

namespace RamanujanPetersson
namespace Residue

open CurveCoh GalCover Kummer CP4a

noncomputable section

section Chart

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {R0 : Type} [CommRing R0] [Algebra R0 K]

/-- A boundary prime of the pro-chart restricts to a nonzero prime of `B_L`. -/
theorem comap_inclU_ne_bot [IsDomain R0] [IsIntegrallyClosed R0] [IsFractionRing R0 K]
    {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)
    {Q : Ideal (proChart A K R0)} (hQ : IsBdryPrime A K R0 Q) : Q.comap (inclU R0 hLU) ≠ ⊥ := by
  have := hQ.1
  have hinj := algebraMap_proChart_injective (A := A) (K := K) (R0 := R0)
  have hPu : Q.under R0 ≠ ⊥ := by
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ.2
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hxP (Algebra.IsIntegral.isIntegral x)
  obtain ⟨r, hrP, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPu
  intro h
  have h1 : algebraMap R0 (integralClosure R0 L) r ∈ Q.comap (inclU R0 hLU) := by
    rw [Ideal.mem_comap, AlgHom.commutes]; exact hrP
  rw [h, Ideal.mem_bot] at h1
  have h2 := congrArg (inclU R0 hLU) h1
  rw [AlgHom.commutes, map_zero] at h2
  exact hr0 (hinj (h2.trans (map_zero _).symm))

/-- Lying over: every nonzero prime of `B_L` is the trace of a boundary prime of the pro-chart. -/
theorem exists_bdry_comap_eq {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)
    (w : Ideal (integralClosure R0 L)) [hwP : w.IsPrime] (hw : w ≠ ⊥) :
    ∃ Q : Ideal (proChart A K R0), IsBdryPrime A K R0 Q ∧ Q.comap (inclU R0 hLU) = w := by
  obtain ⟨P, hP, hPw⟩ := exists_prime_comap_eq (R0 := R0) (S := proChart A K R0)
    (inclU R0 hLU) (inclU_injective _) w
  refine ⟨P, ⟨hP, ?_⟩, hPw⟩
  rintro rfl
  apply hw
  rw [← hPw]
  exact Ideal.comap_bot_of_injective _ (inclU_injective _)

/-- Onto: every nonzero prime of `B_L` is the trace of one of the orbit representatives. -/
theorem exists_rep_comap_eq {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K) {q : ℕ}
    {T : Type} (Qt : T → Ideal (proChart A K R0))
    (hcover : ∀ Q, IsBdryPrime A K R0 Q → ∃ t, ∃ g ∈ pi1geo A K q,
      g ∈ (IntermediateField.restrict hLU).fixingSubgroup ∧ Q = g • Qt t)
    (w : Ideal (integralClosure R0 L)) [hwP : w.IsPrime] (hw : w ≠ ⊥) :
    ∃ t, (Qt t).comap (inclU R0 hLU) = w := by
  obtain ⟨Q, hQ, hQw⟩ := exists_bdry_comap_eq hLU w hw
  obtain ⟨t, g, -, hgL, rfl⟩ := hcover Q hQ
  exact ⟨t, by rw [← hQw, comap_smul_of_fix hLU hgL]⟩

variable {p e : ℕ} [hp : Fact p.Prime] [CharP K p]

set_option synthInstance.maxHeartbeats 400000 in
/-- One-to-one: two orbit representatives with the same trace on `B_L` coincide. -/
theorem eq_of_comap_eq_reps [IsDomain R0] [IsIntegrallyClosed R0] [IsFractionRing R0 K] (he : 0 < e)
    (hζ : ∀ a, 0 < a → ∃ ζ : maxUnram A K, IsPrimitiveRoot ζ ((p ^ e) ^ a - 1))
    (hgood : ∀ Q : Ideal (proChart A K R0), IsBdryPrime A K R0 Q →
      Finite (R0 ⧸ Q.under R0) ∧ ∃ d, Nat.card (R0 ⧸ Q.under R0) = (p ^ e) ^ d)
    {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K) [FiniteDimensional K L]
    {k : ℕ} (hk : 0 < k) (hC : constLevel K p k ≤ L)
    (hres : ∀ w : Ideal (integralClosure R0 L), w.IsPrime → w ≠ ⊥ →
      ∀ y : integralClosure R0 L, y ^ (p ^ k) - y ∈ w)
    {T : Type} (Qt : T → Ideal (proChart A K R0)) (hQt : ∀ t, IsBdryPrime A K R0 (Qt t))
    (hdisj : ∀ t t', ∀ g ∈ pi1geo A K (p ^ e), g ∈ (IntermediateField.restrict hLU).fixingSubgroup →
      Qt t' = g • Qt t → t = t')
    {t t' : T} (h : (Qt t).comap (inclU R0 hLU) = (Qt t').comap (inclU R0 hLU)) : t = t' := by
  have := (hQt t).1
  have := (hQt t').1
  obtain ⟨hfin, hcard⟩ := hgood _ (hQt t)
  obtain ⟨γ, hγ, hγL, hγQ⟩ := exists_geo_fix_smul he hζ hLU hk hC hcard
    (hres _ (Ideal.comap_isPrime _ _) (comap_inclU_ne_bot hLU (hQt t))) h
  exact hdisj t t' γ hγ hγL hγQ

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
/-- **Residue theorem at a level** (S3 chart): if `L ⊇ F(𝔽_{q^m})` is unramified over `U` and every boundary residue
field of `L` has `q^m` elements, then for representatives `Q t` of the `π₁^geo ∩ Gal(K_U/L)`-orbits of boundary
primes (places `v t` of `L` under them) and `α ∈ K_U` with `α ^ N = b ∈ L`, `N ∣ Σ_t v_t(b)`. -/
theorem dvd_sum_reps {L : IntermediateField F (AlgebraicClosure F)} (hLU : L ≤ maxUnram (Places.Rfin Fq F) F)
    (hL : L ∈ unramSet (Places.Rfin Fq F) F) [FiniteDimensional F L] [Algebra.IsSeparable F L]
    [IsDedekindDomain (integralClosure (Places.Rfin Fq F) L)]
    [IsFractionRing (integralClosure (Places.Rfin Fq F) L) L]
    [IsDedekindDomain (integralClosure (Places.Rinf Fq F) L)]
    [IsFractionRing (integralClosure (Places.Rinf Fq F) L) L]
    {m : ℕ} (hm : 0 < m) (hC : constLevel F p (e * m) ≤ L)
    (hdi : ∀ w : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) L),
      Nat.card (integralClosure (Places.Rinf Fq F) L ⧸ w.asIdeal) = Fintype.card Fq ^ m)
    {T : Type} [Fintype T] (Qt : T → Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F)))
    (hQt : ∀ t, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) (Qt t))
    (hcover : ∀ Q, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q → ∃ t,
      ∃ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
        g ∈ (IntermediateField.restrict hLU).fixingSubgroup ∧ Q = g • Qt t)
    (hdisj : ∀ t t', ∀ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
      g ∈ (IntermediateField.restrict hLU).fixingSubgroup → Qt t' = g • Qt t → t = t')
    (v : T → HeightOneSpectrum (integralClosure (Places.Rinf Fq F) L))
    (hv : ∀ t, (v t).asIdeal = (Qt t).comap (inclU (Places.Rinf Fq F) hLU))
    {N : ℕ} {α : AlgebraicClosure F} (hαU : α ∈ maxUnram (Places.Rfin Fq F) F) {b : L} (hb : b ≠ 0)
    (hα : α ^ N = (b : AlgebraicClosure F)) :
    (N : ℤ) ∣ ∑ t, WithZero.log ((v t).valuation L b) := by
  have := hasFiniteQuotients_of_finiteQuot (S := Places.Rinf Fq F)
  have hres : ∀ w : Ideal (integralClosure (Places.Rinf Fq F) L), w.IsPrime → w ≠ ⊥ →
      ∀ y : integralClosure (Places.Rinf Fq F) L, y ^ (p ^ (e * m)) - y ∈ w := by
    intro w hw hw0 y
    obtain ⟨w', rfl⟩ : ∃ w' : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) L), w'.asIdeal = w :=
      ⟨⟨w, hw, hw0⟩, rfl⟩
    have h1 := hdi w'
    have : w'.asIdeal.IsMaximal := w'.isMaximal
    have : Finite (integralClosure (Places.Rinf Fq F) L ⧸ w'.asIdeal) :=
      Nat.finite_of_card_ne_zero (by rw [h1]; exact pow_ne_zero _ Fintype.card_ne_zero)
    have h2 := pow_card_pow_sub_mem w'.asIdeal 1 y
    rw [h1, pow_one, hq, ← pow_mul] at h2
    exact h2
  have hk : 0 < e * m := Nat.mul_pos he hm
  have hdisj' : ∀ t t', ∀ g ∈ pi1geo (Places.Rfin Fq F) F (p ^ e),
      g ∈ (IntermediateField.restrict hLU).fixingSubgroup → Qt t' = g • Qt t → t = t' := by
    rw [← hq]; exact hdisj
  have hinj : Function.Injective v := by
    intro t t' h
    apply eq_of_comap_eq_reps he hζc (fun Q hQ => good_inf hq Q hQ) hLU hk hC hres Qt hQt hdisj'
    exact (hv t).symm.trans ((congrArg HeightOneSpectrum.asIdeal h).trans (hv t'))
  have hsurj : Function.Surjective v := by
    intro w
    obtain ⟨t, ht⟩ := exists_rep_comap_eq hLU Qt hcover w.asIdeal (hwP := w.isPrime) w.ne_bot
    exact ⟨t, HeightOneSpectrum.ext ((hv t).trans ht)⟩
  have hsum : ∑ t, WithZero.log ((v t).valuation L b) =
      ∑ᶠ w : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) L), WithZero.log (w.valuation L b) := by
    rw [← finsum_eq_sum_of_fintype]
    exact finsum_comp_equiv (f := fun w => WithZero.log (w.valuation L b)) (Equiv.ofBijective v ⟨hinj, hsurj⟩)
  rw [hsum]
  obtain ⟨ζ, hζ⟩ := exists_prim_sup hq he hζc hm hC
  have hfin : ∀ y : HeightOneSpectrum (integralClosure (Places.Rfin Fq F) L),
      (N : ℤ) ∣ WithZero.log (y.valuation L b) := by
    intro y
    refine dvd_of_mem_maxUnram (Places.Rfin Fq F) hL (perfect_Rfin Fq F) (fun x => ?_) hαU hα y
    rw [RingHom.mem_range]
    refine ⟨fun h => ⟨⟨x, h⟩, rfl⟩, ?_⟩
    rintro ⟨z, rfl⟩
    exact z.2
  exact dvd_sum_bdry Fq L hm hb hfin
    (fun y => card_fin_level L hm hζ y) hdi

include hq he hζc in
/-- **Residue theorem for normalised tame generators**: under the hypotheses of `dvd_sum_reps`, any `χ` with
`χ(τ_t) = v_t(b) mod N` at every representative satisfies `Σ_t χ(τ_t) = 0`. -/
theorem sum_reps_eq_zero {L : IntermediateField F (AlgebraicClosure F)} (hLU : L ≤ maxUnram (Places.Rfin Fq F) F)
    (hL : L ∈ unramSet (Places.Rfin Fq F) F) [FiniteDimensional F L] [Algebra.IsSeparable F L]
    [IsDedekindDomain (integralClosure (Places.Rfin Fq F) L)]
    [IsFractionRing (integralClosure (Places.Rfin Fq F) L) L]
    [IsDedekindDomain (integralClosure (Places.Rinf Fq F) L)]
    [IsFractionRing (integralClosure (Places.Rinf Fq F) L) L]
    {m : ℕ} (hm : 0 < m) (hC : constLevel F p (e * m) ≤ L)
    (hdi : ∀ w : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) L),
      Nat.card (integralClosure (Places.Rinf Fq F) L ⧸ w.asIdeal) = Fintype.card Fq ^ m)
    {T : Type} [Fintype T] (Qt : T → Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F)))
    (hQt : ∀ t, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) (Qt t))
    (hcover : ∀ Q, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q → ∃ t,
      ∃ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
        g ∈ (IntermediateField.restrict hLU).fixingSubgroup ∧ Q = g • Qt t)
    (hdisj : ∀ t t', ∀ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
      g ∈ (IntermediateField.restrict hLU).fixingSubgroup → Qt t' = g • Qt t → t = t')
    (v : T → HeightOneSpectrum (integralClosure (Places.Rinf Fq F) L))
    (hv : ∀ t, (v t).asIdeal = (Qt t).comap (inclU (Places.Rinf Fq F) hLU))
    {N : ℕ} {α : AlgebraicClosure F} (hαU : α ∈ maxUnram (Places.Rfin Fq F) F) {b : L} (hb : b ≠ 0)
    (hα : α ^ N = (b : AlgebraicClosure F)) (c : T → ZMod N)
    (hc : ∀ t, c t = ((WithZero.log ((v t).valuation L b) : ℤ) : ZMod N)) :
    ∑ t, c t = 0 := by
  have h := dvd_sum_reps hq he hζc hLU hL hm hC hdi Qt hQt hcover hdisj v hv hαU hb hα
  simp_rw [hc]
  rw [← Int.cast_sum]
  exact (CharP.intCast_eq_zero_iff (ZMod N) N _).2 h

end Level

end

end Residue
end RamanujanPetersson


end

-- ===== S4.Def_RP_Cone_ResMax =====
section

/-!
# S4-PD (4), E4B part 5b: one normalised tame generator for all constant levels

* `exists_stable`: finitely many families of subsets of `ℤ/N`, monotone along divisibility, are all constant on the
  multiples of one index `k₀`.
* `radVal` (valuation classes of the radicands of a level at `Q ∩ B_L`), `radVal_mono` (they grow along extensions in
  which inertia fixing the smaller level fixes the larger one).
* `exists_stable_tau`: for boundary primes `Q t` (`t` in a finite type) there are `k₀ > 0` and generators `τ t`
  normalised at every constant level `M ⊔ K(𝔽_{p^(e k)})` with `k₀ ∣ k` (from one normalisation per level).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Residue

open CurveCoh GalCover Kummer CP4a TameInertia IsDedekindDomain Polynomial

noncomputable section

/-- Monotone families of subsets of `ℤ/N` stabilise simultaneously along divisibility. -/
theorem exists_stable {T : Type} [Fintype T] {N : ℕ} [NeZero N] (S : T → ℕ → Set (ZMod N))
    (hmono : ∀ t k k', 0 < k → 0 < k' → k ∣ k' → S t k ⊆ S t k') :
    ∃ k₀, 0 < k₀ ∧ ∀ t k, 0 < k → k₀ ∣ k → S t k ⊆ S t k₀ := by
  classical
  let g : ℕ → ℕ := fun k => ∑ t, (S t k).ncard
  have hbdd : BddAbove (g '' {k | 0 < k}) := by
    refine ⟨Fintype.card T * N, ?_⟩
    rintro _ ⟨k, -, rfl⟩
    calc g k = ∑ t, (S t k).ncard := rfl
      _ ≤ ∑ _t : T, N := Finset.sum_le_sum fun t _ => by
          calc (S t k).ncard ≤ (Set.univ : Set (ZMod N)).ncard := Set.ncard_le_ncard (Set.subset_univ _)
            _ = N := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, ZMod.card]
      _ = Fintype.card T * N := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hne : (g '' {k | 0 < k}).Nonempty := ⟨g 1, 1, Nat.one_pos, rfl⟩
  obtain ⟨k₀, hk₀, hg₀⟩ := Nat.sSup_mem hne hbdd
  refine ⟨k₀, hk₀, fun t k hk hdvd => ?_⟩
  have hsub : ∀ t, S t k₀ ⊆ S t k := fun t => hmono t k₀ k hk₀ hk hdvd
  have hle : ∀ t ∈ (Finset.univ : Finset T), (S t k₀).ncard ≤ (S t k).ncard :=
    fun t _ => Set.ncard_le_ncard (hsub t)
  have hgk : g k ≤ g k₀ := by
    rw [hg₀]
    exact le_csSup hbdd ⟨k, hk, rfl⟩
  have heq := (Finset.sum_eq_sum_iff_of_le hle).1 (le_antisymm (Finset.sum_le_sum hle) hgk)
  exact (Set.eq_of_subset_of_ncard_le (hsub t) (heq t (Finset.mem_univ t)).ge).ge

section Chart

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
  {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]

/-- The place `Q ∩ B_L` of a level under a boundary prime `Q`. -/
def bdryPlace {Q : Ideal (proChart A K R0)} (hQ : IsBdryPrime A K R0 Q)
    {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)
    [IsDedekindDomain (integralClosure R0 L)] : HeightOneSpectrum (integralClosure R0 L) :=
  ⟨Q.comap (inclU R0 hLU), haveI := hQ.1; Ideal.IsPrime.comap _, comap_inclU_ne_bot hLU hQ⟩

/-- Valuation classes mod `N`, at `Q ∩ B_L`, of the radicands `α ^ N = b ∈ L` (`α ∈ K_U`). -/
def radVal (Q : Ideal (proChart A K R0)) {L : IntermediateField K (AlgebraicClosure K)}
    (hLU : L ≤ maxUnram A K) [IsDedekindDomain (integralClosure R0 L)]
    [IsFractionRing (integralClosure R0 L) L] (N : ℕ) : Set (ZMod N) :=
  {c | ∃ (α : (maxUnram A K)ˣ) (b : L), (α : maxUnram A K) ^ N = IntermediateField.inclusion hLU b ∧
    ∀ v : HeightOneSpectrum (integralClosure R0 L), v.asIdeal = Q.comap (inclU R0 hLU) →
      ((WithZero.log (v.valuation L b) : ℤ) : ZMod N) = c}

set_option synthInstance.maxHeartbeats 400000 in
theorem radVal_mono [Ring.HasFiniteQuotients R0] {Q : Ideal (proChart A K R0)} (hQ : IsBdryPrime A K R0 Q)
    {L L' : IntermediateField K (AlgebraicClosure K)} (hLL : L ≤ L') (hLU : L ≤ maxUnram A K)
    (hL'U : L' ≤ maxUnram A K) [FiniteDimensional K L']
    [IsDedekindDomain (integralClosure R0 L)] [IsFractionRing (integralClosure R0 L) L]
    [IsDedekindDomain (integralClosure R0 L')] [IsFractionRing (integralClosure R0 L') L']
    (hfix : ∀ σ ∈ Q.inertia (Pi1 A K), (∀ x : maxUnram A K, (x : AlgebraicClosure K) ∈ L → σ x = x) →
      ∀ x : maxUnram A K, (x : AlgebraicClosure K) ∈ L' → σ x = x) (N : ℕ) :
    radVal Q hLU N ⊆ radVal Q hL'U N := by
  have := hQ.1
  rintro c ⟨α, b, hα, hc⟩
  refine ⟨α, IntermediateField.inclusion hLL b, hα, fun v' hv' => ?_⟩
  rw [log_val_eq_of_inertia_fix hLL hLU hL'U (bdryPlace hQ hLU) rfl v' hv' hfix b]
  exact hc _ rfl

variable {p : ℕ} [hp : Fact p.Prime] [CharP K p]

omit [IsDedekindDomain R0] [IsFractionRing R0 K] in
/-- Inertia fixing `M` fixes `M ⊔ K(𝔽_{p^k})`. -/
theorem inertia_fix_sup {e : ℕ} (he : 0 < e) {Q : Ideal (proChart A K R0)} [Q.IsPrime]
    {M : IntermediateField K (AlgebraicClosure K)} (hMU : M ≤ maxUnram A K) {k : ℕ} (hk : 0 < k)
    (hCU : constLevel K p k ≤ maxUnram A K) {σ : Pi1 A K} (hσ : σ ∈ Q.inertia (Pi1 A K))
    (hσM : ∀ y : maxUnram A K, (y : AlgebraicClosure K) ∈ M → σ y = y) :
    ∀ y : maxUnram A K, (y : AlgebraicClosure K) ∈ M ⊔ constLevel K p k → σ y = y := by
  have hgeo := Kummer.inertia_le_pi1geo he rfl hσ
  have h1 : σ ∈ (IntermediateField.restrict hMU).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    exact hσM y ((IntermediateField.mem_restrict hMU _).1 hy)
  have h2 : σ ∈ (IntermediateField.restrict hCU).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    exact fixed_of_mem_constLevel he hk ((IntermediateField.mem_restrict hCU _).1 hy) σ hgeo
  have h3 := mem_fix_sup hMU hCU h1 h2
  intro y hy
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 h3 y ((IntermediateField.mem_restrict _ _).2 hy)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **One normalised generator per boundary prime for all constant levels** `M ⊔ K(𝔽_{p^(e k)})`, `k₀ ∣ k`. -/
theorem exists_stable_tau [Ring.HasFiniteQuotients R0] {e : ℕ} (he : 0 < e)
    {N : ℕ} [NeZero N] (hN : IsUnit (N : R0)) {ζN : maxUnram A K} (hζN : IsPrimitiveRoot ζN N)
    {M : IntermediateField K (AlgebraicClosure K)} (hM : M ∈ unramSet A K)
    {T : Type} [Fintype T] (Q : T → Ideal (proChart A K R0)) (hQ : ∀ t, IsBdryPrime A K R0 (Q t))
    (J : T → Subgroup (Pi1 A K))
    (hJ : ∀ t, ∀ σ ∈ J t, σ ∈ (Q t).inertia (Pi1 A K) ∧
      ∀ y : maxUnram A K, (y : AlgebraicClosure K) ∈ M → σ y = y)
    (P : ∀ t, J t → Prop)
    (htau : ∀ k, 0 < k → ∀ (hLU : M ⊔ constLevel K p (e * k) ≤ maxUnram A K)
      [IsDedekindDomain (integralClosure R0 ↥(M ⊔ constLevel K p (e * k)))]
      [IsFractionRing (integralClosure R0 ↥(M ⊔ constLevel K p (e * k))) ↥(M ⊔ constLevel K p (e * k))]
      (t : T) (v : HeightOneSpectrum (integralClosure R0 ↥(M ⊔ constLevel K p (e * k)))),
      v.asIdeal = (Q t).comap (inclU R0 hLU) →
      ∃ τ : J t, P t τ ∧ ∀ (α : (maxUnram A K)ˣ) (b : ↥(M ⊔ constLevel K p (e * k))),
        (α : maxUnram A K) ^ N = IntermediateField.inclusion hLU b →
        kchar hζN (Γ := J t) α τ =
          ((WithZero.log (v.valuation ↥(M ⊔ constLevel K p (e * k)) b) : ℤ) : ZMod N)) :
    ∃ k₀, 0 < k₀ ∧ ∃ τ : ∀ t, J t, (∀ t, P t (τ t)) ∧
      ∀ k, 0 < k → k₀ ∣ k → ∀ (hLU : M ⊔ constLevel K p (e * k) ≤ maxUnram A K)
      [IsDedekindDomain (integralClosure R0 ↥(M ⊔ constLevel K p (e * k)))]
      [IsFractionRing (integralClosure R0 ↥(M ⊔ constLevel K p (e * k))) ↥(M ⊔ constLevel K p (e * k))]
      (t : T) (v : HeightOneSpectrum (integralClosure R0 ↥(M ⊔ constLevel K p (e * k)))),
      v.asIdeal = (Q t).comap (inclU R0 hLU) →
      ∀ (α : (maxUnram A K)ˣ) (b : ↥(M ⊔ constLevel K p (e * k))),
        (α : maxUnram A K) ^ N = IntermediateField.inclusion hLU b →
        kchar hζN (Γ := J t) α (τ t) =
          ((WithZero.log (v.valuation ↥(M ⊔ constLevel K p (e * k)) b) : ℤ) : ZMod N) := by
  classical
  have hMU : M ≤ maxUnram A K := by
    rw [maxUnram_eq_sSup]
    exact le_sSup hM
  have hLk : ∀ k, 0 < k → M ⊔ constLevel K p (e * k) ∈ unramSet A K := fun k hk =>
    sup_mem_unramSet A K hM (constLevel_mem_unramSet A (Nat.mul_pos he hk))
  have hLkU : ∀ k, 0 < k → M ⊔ constLevel K p (e * k) ≤ maxUnram A K := fun k hk => by
    rw [maxUnram_eq_sSup]
    exact le_sSup (hLk k hk)
  have hfixk : ∀ k, 0 < k → ∀ t, ∀ σ ∈ (Q t).inertia (Pi1 A K),
      (∀ y : maxUnram A K, (y : AlgebraicClosure K) ∈ M → σ y = y) →
      ∀ y : maxUnram A K, (y : AlgebraicClosure K) ∈ M ⊔ constLevel K p (e * k) → σ y = y := by
    intro k hk t σ hσ hσM
    have := (hQ t).1
    exact inertia_fix_sup he hMU (Nat.mul_pos he hk) (le_sup_right.trans (hLkU k hk)) hσ hσM
  have hFD : ∀ k, 0 < k → FiniteDimensional K ↥(M ⊔ constLevel K p (e * k)) := fun k hk => (hLk k hk).1
  have hDed : ∀ k, 0 < k → IsDedekindDomain (integralClosure R0 ↥(M ⊔ constLevel K p (e * k))) :=
    fun k hk => by
      have := hFD k hk
      have : IsGalois K ↥(M ⊔ constLevel K p (e * k)) := (hLk k hk).2.1
      exact integralClosure.isDedekindDomain (A := R0) (K := K) (L := ↥(M ⊔ constLevel K p (e * k)))
  have hFrac : ∀ k, 0 < k → IsFractionRing (integralClosure R0 ↥(M ⊔ constLevel K p (e * k)))
      ↥(M ⊔ constLevel K p (e * k)) := fun k hk => by
    have := hFD k hk
    exact integralClosure.isFractionRing_of_finite_extension (A := R0) K _
  have hLL : ∀ k k', 0 < k → 0 < k' → k ∣ k' →
      M ⊔ constLevel K p (e * k) ≤ M ⊔ constLevel K p (e * k') := fun k k' hk hk' hdvd =>
    sup_le_sup_left (constLevel_le_of_dvd (Nat.mul_pos he hk') (Nat.mul_dvd_mul_left e hdvd)) M
  let S : T → ℕ → Set (ZMod N) := fun t k => if hk : 0 < k then
    (haveI := hDed k hk; haveI := hFrac k hk; radVal (Q t) (hLkU k hk) N) else ∅
  have hS_eq : ∀ t k (hk : 0 < k), S t k =
      (haveI := hDed k hk; haveI := hFrac k hk; radVal (Q t) (hLkU k hk) N) := fun t k hk => dif_pos hk
  have hmono : ∀ t k k', 0 < k → 0 < k' → k ∣ k' → S t k ⊆ S t k' := by
    intro t k k' hk hk' hdvd
    rw [hS_eq t k hk, hS_eq t k' hk']
    have := hFD k' hk'
    have := hDed k hk
    have := hFrac k hk
    have := hDed k' hk'
    have := hFrac k' hk'
    exact radVal_mono (hQ t) (hLL k k' hk hk' hdvd) (hLkU k hk) (hLkU k' hk')
      (fun σ hσ h => hfixk k' hk' t σ hσ fun y hy => h y (le_sup_left (a := M) hy)) N
  obtain ⟨k₀, hk₀, hstab⟩ := exists_stable S hmono
  have := hFD k₀ hk₀
  have := hDed k₀ hk₀
  have := hFrac k₀ hk₀
  choose τ hP hnorm using fun t => htau k₀ hk₀ (hLkU k₀ hk₀) t (bdryPlace (hQ t) (hLkU k₀ hk₀)) rfl
  refine ⟨k₀, hk₀, τ, hP, ?_⟩
  intro k hk hdvd hLU _ _ t v hv α b hα
  have := hFD k hk
  have := (hQ t).1
  have hJle : J t ≤ (Q t).inertia (Pi1 A K) := fun σ hσ => (hJ t σ hσ).1
  have hfix' : ∀ σ ∈ (Q t).inertia (Pi1 A K),
      (∀ x : maxUnram A K, (x : AlgebraicClosure K) ∈ M ⊔ constLevel K p (e * k₀) → σ x = x) →
      ∀ x : maxUnram A K, (x : AlgebraicClosure K) ∈ M ⊔ constLevel K p (e * k) → σ x = x :=
    fun σ hσ h => hfixk k hk t σ hσ fun y hy => h y (le_sup_left (a := M) hy)
  have hval := log_val_eq_of_inertia_fix (hLL k₀ k hk₀ hk hdvd) (hLkU k₀ hk₀) hLU
    (bdryPlace (hQ t) (hLkU k₀ hk₀)) rfl v hv hfix'
  refine kchar_norm_of_le hN hζN hJle (hLL k₀ k hk₀ hk hdvd) (hLkU k₀ hk₀) hLU
    (bdryPlace (hQ t) (hLkU k₀ hk₀)) v hv
    (fun σ hσ => hfixk k hk t σ (hJ t σ hσ).1 (hJ t σ hσ).2) hval ?_ (hnorm t) α b hα
  intro α' b' hα'
  have hmem : ((WithZero.log (v.valuation ↥(M ⊔ constLevel K p (e * k)) b') : ℤ) : ZMod N) ∈ S t k := by
    rw [hS_eq t k hk]
    exact ⟨α', b', hα', fun v' hv' => by rw [HeightOneSpectrum.ext (hv'.trans hv.symm)]⟩
  have hmem0 := hstab t k hk hdvd hmem
  rw [hS_eq t k₀ hk₀] at hmem0
  obtain ⟨β, c, hβ, hc⟩ := hmem0
  exact ⟨β, c, hβ, hc _ rfl⟩

end Chart

end

end Residue
end RamanujanPetersson


end

-- ===== S4.Def_RP_Cone_ResGlob =====
section

/-!
# S4-PD (4), E4B part 5c: the global residue theorem

S3 setting (`F / 𝔽_q`, chart `(Rfin, F, Rinf)`), a finite level `M ≤ K_U` and representatives `Q t` of the
`Γ_H := π₁^geo ∩ Gal(K_U/M)`-orbits of boundary primes; `J t` is the inertia of `Q t` fixing `M`.

* `exists_tau_sum_eq_zero`: from one normalised generator per constant level (`htau`) there are `k₀ > 0` and
  generators `τ t ∈ J t`, normalised at every level `M ⊔ K(𝔽_{p^(e k)})` with `k₀ ∣ k`, such that
  `Σ_t χ(τ t) = 0` for EVERY locally constant additive `χ : Γ_H → ℤ/N` (global residue theorem).
* `htau_norm` (any chart): the level-wise hypothesis `htau` from `exists_norm_tau`.
* `exists_norm_tau_sum`: the same with the tame generators of `exists_norm_tau` and their characters `θ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Residue

open CurveCoh GalCover Kummer CP4a TameInertia IsDedekindDomain Polynomial
open scoped Pointwise

noncomputable section

section Chart

variable {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]
variable {p : ℕ} [hp : Fact p.Prime] [CharP K p]

/-- A normalised tame generator `τ` of `J ≤ I(Q)` with its character `θ` (the shape of `exists_norm_tau`). -/
abbrev TauProp (Q : Ideal (proChart A K R0)) (J : Subgroup (Pi1 A K)) (N : ℕ) (τ : J) : Prop :=
  ∃ θ : J → ZMod N, IsLocallyConstant θ ∧ (∀ σ σ', θ (σ * σ') = θ σ + θ σ') ∧ θ τ = 1 ∧
    (∀ g ∈ Q.inertia (Pi1 A K), ∀ σ (hσ : σ ∈ J) (hσ' : g⁻¹ * σ * g ∈ J),
      θ ⟨g⁻¹ * σ * g, hσ'⟩ = θ ⟨σ, hσ⟩) ∧
    (∀ χ : J → ZMod N, IsLocallyConstant χ → (∀ σ σ', χ (σ * σ') = χ σ + χ σ') →
      ∀ σ, χ σ = χ τ * θ σ)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- The level-wise normalisation hypothesis `htau` of `exists_stable_tau`, from `exists_norm_tau` at every constant
level `M ⊔ K(𝔽_{p^(e k)})` (inertia fixing `M` fixes these levels). -/
theorem htau_norm [Ring.HasFiniteQuotients R0] {e : ℕ} (he : 0 < e) {N : ℕ} [NeZero N]
    {ζN : maxUnram A K} (hζN : IsPrimitiveRoot ζN N) (hζNg : ∀ σ ∈ pi1geo A K (p ^ e), σ ζN = ζN)
    {M : IntermediateField K (AlgebraicClosure K)} (hM : M ∈ unramSet A K) (hMU : M ≤ maxUnram A K)
    {T : Type} (Q : T → Ideal (proChart A K R0)) (hQ : ∀ t, IsBdryPrime A K R0 (Q t))
    (J : T → Subgroup (Pi1 A K))
    (hJ : ∀ t σ, σ ∈ J t ↔ σ ∈ (Q t).inertia (Pi1 A K) ∧
      ∀ y : maxUnram A K, (y : AlgebraicClosure K) ∈ M → σ y = y)
    (d : T → ℕ) (hd0 : ∀ t, 0 < d t)
    (hNA : ∀ t, IsUnit ((N * d t : ℕ) : A)) (hNR : ∀ t, IsUnit ((N * d t : ℕ) : R0))
    (ζ : T → maxUnram A K) (hζ : ∀ t, IsPrimitiveRoot (ζ t) (N * d t))
    (hζI : ∀ t, ∀ σ ∈ (Q t).inertia (Pi1 A K), σ (ζ t) = ζ t)
    (x : T → HeightOneSpectrum R0) (hx : ∀ t, (x t).asIdeal = (Q t).comap (algebraMap R0 (proChart A K R0)))
    (a : T → A) (ha : ∀ t, 1 < (x t).valuation K (algebraMap A K (a t)))
    (kk : T → ℕ) (hd : ∀ t, ∀ σ ∈ (Q t).inertia (Pi1 A K), σ ^ (p ^ kk t * d t) ∈ J t) :
    ∀ k, 0 < k → ∀ (hLU : M ⊔ constLevel K p (e * k) ≤ maxUnram A K)
      [IsDedekindDomain (integralClosure R0 ↥(M ⊔ constLevel K p (e * k)))]
      [IsFractionRing (integralClosure R0 ↥(M ⊔ constLevel K p (e * k))) ↥(M ⊔ constLevel K p (e * k))]
      (t : T) (v : HeightOneSpectrum (integralClosure R0 ↥(M ⊔ constLevel K p (e * k)))),
      v.asIdeal = (Q t).comap (inclU R0 hLU) →
      ∃ τ : J t, TauProp (Q t) (J t) N τ ∧
      ∀ (α : (maxUnram A K)ˣ) (b : ↥(M ⊔ constLevel K p (e * k))),
        (α : maxUnram A K) ^ N = IntermediateField.inclusion hLU b →
        kchar hζN (Γ := J t) α τ =
          ((WithZero.log (v.valuation ↥(M ⊔ constLevel K p (e * k)) b) : ℤ) : ZMod N) := by
  intro k hk hLU _ _ t v hv
  have : NeZero (d t) := ⟨(hd0 t).ne'⟩
  have hLk : M ⊔ constLevel K p (e * k) ∈ unramSet A K :=
    sup_mem_unramSet A K hM (constLevel_mem_unramSet A (Nat.mul_pos he hk))
  have : FiniteDimensional K ↥(M ⊔ constLevel K p (e * k)) := hLk.1
  have := (hQ t).1
  have hJk : ∀ σ, σ ∈ J t ↔ σ ∈ (Q t).inertia (Pi1 A K) ∧
      ∀ y : maxUnram A K, (y : AlgebraicClosure K) ∈ M ⊔ constLevel K p (e * k) → σ y = y := by
    intro σ
    refine ⟨fun hσ => ⟨((hJ t σ).1 hσ).1, inertia_fix_sup he hMU (Nat.mul_pos he hk)
      (le_sup_right.trans hLU) ((hJ t σ).1 hσ).1 ((hJ t σ).1 hσ).2⟩,
      fun h => (hJ t σ).2 ⟨h.1, fun y hy => h.2 y (le_sup_left (a := M) hy)⟩⟩
  have hζNJ : ∀ σ ∈ J t, σ ζN = ζN := fun σ hσ =>
    hζNg σ (Kummer.inertia_le_pi1geo he rfl ((hJ t σ).1 hσ).1)
  obtain ⟨τ, θ, h1, h2, h3, h4, h5, h6⟩ := exists_norm_tau (hQ t) (hNA t) (hNR t) (hζ t) (hζI t) (x t)
    (hx t) (ha t) hLU v hv hJk (kk t) (hd t) hζN hζNJ
  exact ⟨τ, ⟨θ, h1, h2, h3, h4, h5⟩, h6⟩

end Chart

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable (hζc : ∀ a, 0 < a → ∃ z : maxUnram (Places.Rfin Fq F) F, IsPrimitiveRoot z ((p ^ e) ^ a - 1))

end

end Residue
end RamanujanPetersson


end

-- ===== S4.Def_RP_Cone_ExDef =====
section

/-!
# S4-PD (4), E4X part 1: the divisibility hypothesis for boundary divisors, and Kummer roots from it

* `PicDivX A K R0 p N`: **`Pic⁰(X̄)` is `N`-divisible on boundary divisors** -- for every finite level `M ≤ K_U`
  whose boundary residue fields all have the same size and every boundary divisor `D` of `M` with `Σ D = 0`
  (degree `0`), after a constant extension `M·𝔽_{p^m}` some `a ≠ 0` has `N ∣ v_y(a)` at every finite place `y`
  and `D + div(a) ≡ 0 mod N` at the boundary. Explicit hypothesis of S4-PD item (4) (discharged downstream by
  S4-CoreB, like `CdOne.PicDivU`).
* `exists_root_picDivX`: from `PicDivX`, a unit `α ∈ K_U` with `α ^ N ∈ M ⊔ K(𝔽_{p^(e k)})` for every constant level
  `M ⊔ K(𝔽_{p^(e k)}) ⊇ L·𝔽_{p^m}`, whose boundary valuations are `-D mod N` (Kummer unramified criterion + valuations
  along constant extensions).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Residue

open CurveCoh GalCover Kummer CdOne TameInertia IsDedekindDomain

noncomputable section

/-- **`Pic⁰(X̄)/N = 0` on boundary divisors**: at every finite level `M ≤ K_U` whose boundary residue fields all have
`r` elements, every boundary divisor `D` with `Σ D = 0` becomes, after a constant extension `M·𝔽_{p^m}`, congruent
mod `N` to `-div(a)` for some `a ≠ 0` whose finite valuations are all divisible by `N`. -/
def PicDivX (A K R0 : Type) [CommRing A] [Field K] [Algebra A K] [CommRing R0] [IsDedekindDomain R0]
    [Algebra R0 K] [IsFractionRing R0 K] (p : ℕ) [Fact p.Prime] [CharP K p] (N : ℕ) : Prop :=
  ∀ M : IntermediateField K (AlgebraicClosure K), FiniteDimensional K M → M ≤ maxUnram A K →
    ∀ [IsDedekindDomain (integralClosure R0 M)] [IsFractionRing (integralClosure R0 M) M] (r : ℕ),
    (∀ w : HeightOneSpectrum (integralClosure R0 M), Nat.card (integralClosure R0 M ⧸ w.asIdeal) = r) →
    ∀ D : HeightOneSpectrum (integralClosure R0 M) → ℤ, (Function.support D).Finite → ∑ᶠ w, D w = 0 →
    ∃ m : ℕ, 0 < m ∧ ∃ a : ↥(M ⊔ constLevel K p m), a ≠ 0 ∧
      (∀ [IsDedekindDomain (integralClosure A ↥(M ⊔ constLevel K p m))]
        [IsFractionRing (integralClosure A ↥(M ⊔ constLevel K p m)) ↥(M ⊔ constLevel K p m)]
        (y : HeightOneSpectrum (integralClosure A ↥(M ⊔ constLevel K p m))),
        (N : ℤ) ∣ WithZero.log (y.valuation ↥(M ⊔ constLevel K p m) a)) ∧
      ∀ [IsDedekindDomain (integralClosure R0 ↥(M ⊔ constLevel K p m))]
        [IsFractionRing (integralClosure R0 ↥(M ⊔ constLevel K p m)) ↥(M ⊔ constLevel K p m)]
        (w : HeightOneSpectrum (integralClosure R0 ↥(M ⊔ constLevel K p m))),
        (N : ℤ) ∣ D (underI R0 (le_sup_left : M ≤ M ⊔ constLevel K p m) w) +
          WithZero.log (w.valuation ↥(M ⊔ constLevel K p m) a)

variable {A K : Type} [CommRing A] [IsDomain A] [IsDedekindDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K] {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]
variable {p : ℕ} [hp : Fact p.Prime] [CharP K p]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **Kummer roots from `PicDivX`**: a unit `α ∈ K_U` such that at every constant level `L₂ = M ⊔ K(𝔽_{p^(e k)})`
containing `L·𝔽_{p^m}`, `α ^ N = b ∈ L₂` with `v₂(b) ≡ -D(v) mod N` at the boundary place `v₂` of `L₂` over the place
`v` of `L` (both under one boundary prime `Q`). -/
theorem exists_root_picDivX [Ring.HasFiniteQuotients R0] {N : ℕ} [NeZero N] (hPic : PicDivX A K R0 p N)
    (hNA : IsUnit (N : A)) {e : ℕ} (he : 0 < e) {M L : IntermediateField K (AlgebraicClosure K)}
    (hM : M ∈ unramSet A K) (hMU : M ≤ maxUnram A K) (hL : L ∈ unramSet A K) (hLU : L ≤ maxUnram A K)
    (hML : M ≤ L) [hDL : IsDedekindDomain (integralClosure R0 L)] [hFL : IsFractionRing (integralClosure R0 L) L]
    {r : ℕ} (hr : ∀ w : HeightOneSpectrum (integralClosure R0 L), Nat.card (integralClosure R0 L ⧸ w.asIdeal) = r)
    (D : HeightOneSpectrum (integralClosure R0 L) → ℤ) (hD : (Function.support D).Finite)
    (hD0 : ∑ᶠ w, D w = 0) :
    ∃ m, 0 < m ∧ ∃ α : (maxUnram A K)ˣ, ∀ k, 0 < k → L ⊔ constLevel K p m ≤ M ⊔ constLevel K p (e * k) →
      ∀ (hL2U : M ⊔ constLevel K p (e * k) ≤ maxUnram A K),
      ∃ b : ↥(M ⊔ constLevel K p (e * k)), (α : maxUnram A K) ^ N = IntermediateField.inclusion hL2U b ∧
        ∀ [IsDedekindDomain (integralClosure R0 ↥(M ⊔ constLevel K p (e * k)))]
          [IsFractionRing (integralClosure R0 ↥(M ⊔ constLevel K p (e * k))) ↥(M ⊔ constLevel K p (e * k))]
          (Q : Ideal (proChart A K R0)), IsBdryPrime A K R0 Q →
          ∀ v2 : HeightOneSpectrum (integralClosure R0 ↥(M ⊔ constLevel K p (e * k))),
            v2.asIdeal = Q.comap (inclU R0 hL2U) →
          ∀ v : HeightOneSpectrum (integralClosure R0 L), v.asIdeal = Q.comap (inclU R0 hLU) →
            (N : ℤ) ∣ D v + WithZero.log (v2.valuation ↥(M ⊔ constLevel K p (e * k)) b) := by
  have hFDL : FiniteDimensional K L := hL.1
  obtain ⟨m, hm, a, ha0, hafin, habd⟩ := hPic L hFDL hLU r hr D hD hD0
  refine ⟨m, hm, ?_⟩
  have hL1 : L ⊔ constLevel K p m ∈ unramSet A K := sup_mem_unramSet A K hL (constLevel_mem_unramSet A hm)
  have hL1U : L ⊔ constLevel K p m ≤ maxUnram A K := by
    rw [maxUnram_eq_sSup]
    exact le_sSup hL1
  have : FiniteDimensional K ↥(L ⊔ constLevel K p m) := hL1.1
  have : IsGalois K ↥(L ⊔ constLevel K p m) := hL1.2.1
  have hDA1 : IsDedekindDomain (integralClosure A ↥(L ⊔ constLevel K p m)) :=
    integralClosure.isDedekindDomain (A := A) (K := K) (L := ↥(L ⊔ constLevel K p m))
  have hFA1 : IsFractionRing (integralClosure A ↥(L ⊔ constLevel K p m)) ↥(L ⊔ constLevel K p m) :=
    integralClosure.isFractionRing_of_finite_extension (A := A) K _
  have hDR1 : IsDedekindDomain (integralClosure R0 ↥(L ⊔ constLevel K p m)) :=
    integralClosure.isDedekindDomain (A := R0) (K := K) (L := ↥(L ⊔ constLevel K p m))
  have hFR1 : IsFractionRing (integralClosure R0 ↥(L ⊔ constLevel K p m)) ↥(L ⊔ constLevel K p m) :=
    integralClosure.isFractionRing_of_finite_extension (A := R0) K _
  -- the Kummer root is unramified over `U`
  obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq ((a : ↥(L ⊔ constLevel K p m)) : AlgebraicClosure K)
    (Nat.pos_of_ne_zero (NeZero.ne N))
  have hγU : γ ∈ maxUnram A K := root_mem_maxUnram_of_dvd A hL1 hNA ha0 (fun y => hafin y) hγ
  have hγ0 : (⟨γ, hγU⟩ : maxUnram A K) ≠ 0 := by
    intro h0
    have h1 : γ = 0 := congrArg Subtype.val h0
    apply ha0
    have h2 : ((a : ↥(L ⊔ constLevel K p m)) : AlgebraicClosure K) = 0 := by
      rw [← hγ, h1, zero_pow (NeZero.ne N)]
    exact_mod_cast h2
  refine ⟨Units.mk0 _ hγ0, fun k hk hL12 hL2U => ?_⟩
  refine ⟨IntermediateField.inclusion hL12 a, by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, Units.val_mk0, IntermediateField.coe_inclusion, IntermediateField.coe_inclusion]
    exact hγ, ?_⟩
  intro _ _ Q hQ v2 hv2 v hv
  have := hQ.1
  let v1 : HeightOneSpectrum (integralClosure R0 ↥(L ⊔ constLevel K p m)) :=
    ⟨Q.comap (inclU R0 hL1U), Ideal.IsPrime.comap _, comap_inclU_ne_bot hL1U hQ⟩
  have h1 := habd v1
  have hu : underI R0 (le_sup_left : L ≤ L ⊔ constLevel K p m) v1 = v := by
    apply HeightOneSpectrum.ext
    rw [hv]
    ext x
    show x ∈ Ideal.comap (incl R0 K (le_sup_left : L ≤ L ⊔ constLevel K p m)) (Ideal.comap (inclU R0 hL1U) Q) ↔
      x ∈ Ideal.comap (inclU R0 hLU) Q
    have hxe : inclU R0 hL1U (incl R0 K (le_sup_left : L ≤ L ⊔ constLevel K p m) x) = inclU R0 hLU x := by
      apply Subtype.ext
      apply Subtype.ext
      simp only [inclU, AlgHom.coe_mapIntegralClosure, AlgHom.coe_restrictScalars', IntermediateField.coe_inclusion]
      exact incl_val R0 K _ x
    simp only [Ideal.mem_comap]
    rw [← hxe]
  have hCU : constLevel K p (e * k) ≤ maxUnram A K := le_sup_right.trans hL2U
  have hL2 : M ⊔ constLevel K p (e * k) ∈ unramSet A K :=
    sup_mem_unramSet A K hM (constLevel_mem_unramSet A (Nat.mul_pos he hk))
  have : FiniteDimensional K ↥(M ⊔ constLevel K p (e * k)) := hL2.1
  have h2 := log_val_eq_of_inertia_fix hL12 hL1U hL2U v1 rfl v2 hv2
    (fun σ hσ hσ1 => inertia_fix_sup he hMU (Nat.mul_pos he hk) hCU hσ
      (fun y hy => hσ1 y ((hML.trans le_sup_left) hy))) a
  rw [h2, ← hu]
  exact h1

end

end Residue
end RamanujanPetersson


end

-- ===== S4.Def_RP_Cone_Exist =====
section

/-!
# S4-PD (4), E4X part 2: existence of global characters with prescribed residues

S3 setting (`F / 𝔽_q`, chart `(Rfin, F, Rinf)`), a finite level `M ≤ K_U`, representatives `Q t` of the
`Γ_H := π₁^geo ∩ Gal(K_U/M)`-orbits of boundary primes and generators `τ t` of their inertia groups `J t`,
normalised at the constant levels `M ⊔ K(𝔽_{p^(e k)})`, `k₀ ∣ k` (output of `exists_norm_tau_sum`).

* `bij_reps`: at a level with exact boundary residue degrees, the places under the representatives are all the
  boundary places, each once.
* `exists_kchar_of_sum_zero` (**existence**, converse of the global residue theorem): under `PicDivX`, for every
  `c : T → ℤ/N` with `Σ_t c t = 0` there is a locally constant hom `χ : Γ_H → ℤ/N` with `χ(τ t) = c t`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Residue

open CurveCoh GalCover Kummer CP4a CdOne TameInertia IsDedekindDomain Polynomial
open scoped Pointwise

noncomputable section

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable (hζc : ∀ a, 0 < a → ∃ z : maxUnram (Places.Rfin Fq F) F, IsPrimitiveRoot z ((p ^ e) ^ a - 1))

include hq he hζc in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- At a level `L ⊇ F(𝔽_{q^m})` whose boundary residue fields have `q^m` elements, the places `v t` under the orbit
representatives `Q t` form a bijection onto the boundary places of `L`. -/
theorem bij_reps {L : IntermediateField F (AlgebraicClosure F)} (hLU : L ≤ maxUnram (Places.Rfin Fq F) F)
    [FiniteDimensional F L] [IsDedekindDomain (integralClosure (Places.Rinf Fq F) L)]
    {m : ℕ} (hm : 0 < m) (hC : constLevel F p (e * m) ≤ L)
    (hdi : ∀ w : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) L),
      Nat.card (integralClosure (Places.Rinf Fq F) L ⧸ w.asIdeal) = Fintype.card Fq ^ m)
    {T : Type} (Qt : T → Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F)))
    (hQt : ∀ t, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) (Qt t))
    (hcover : ∀ Q, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q → ∃ t,
      ∃ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
        g ∈ (IntermediateField.restrict hLU).fixingSubgroup ∧ Q = g • Qt t)
    (hdisj : ∀ t t', ∀ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
      g ∈ (IntermediateField.restrict hLU).fixingSubgroup → Qt t' = g • Qt t → t = t')
    (v : T → HeightOneSpectrum (integralClosure (Places.Rinf Fq F) L))
    (hv : ∀ t, (v t).asIdeal = (Qt t).comap (inclU (Places.Rinf Fq F) hLU)) :
    Function.Bijective v := by
  have := hasFiniteQuotients_of_finiteQuot (S := Places.Rinf Fq F)
  have hres : ∀ w : Ideal (integralClosure (Places.Rinf Fq F) L), w.IsPrime → w ≠ ⊥ →
      ∀ y : integralClosure (Places.Rinf Fq F) L, y ^ (p ^ (e * m)) - y ∈ w := by
    intro w hw hw0 y
    obtain ⟨w', rfl⟩ : ∃ w' : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) L), w'.asIdeal = w :=
      ⟨⟨w, hw, hw0⟩, rfl⟩
    have h1 := hdi w'
    have : w'.asIdeal.IsMaximal := w'.isMaximal
    have : Finite (integralClosure (Places.Rinf Fq F) L ⧸ w'.asIdeal) :=
      Nat.finite_of_card_ne_zero (by rw [h1]; exact pow_ne_zero _ Fintype.card_ne_zero)
    have h2 := pow_card_pow_sub_mem w'.asIdeal 1 y
    rw [h1, pow_one, hq, ← pow_mul] at h2
    exact h2
  have hk : 0 < e * m := Nat.mul_pos he hm
  have hdisj' : ∀ t t', ∀ g ∈ pi1geo (Places.Rfin Fq F) F (p ^ e),
      g ∈ (IntermediateField.restrict hLU).fixingSubgroup → Qt t' = g • Qt t → t = t' := by
    rw [← hq]; exact hdisj
  refine ⟨fun t t' h => ?_, fun w => ?_⟩
  · apply eq_of_comap_eq_reps he hζc (fun Q hQ => good_inf hq Q hQ) hLU hk hC hres Qt hQt hdisj'
    exact (hv t).symm.trans ((congrArg HeightOneSpectrum.asIdeal h).trans (hv t'))
  · obtain ⟨t, ht⟩ := exists_rep_comap_eq hLU Qt hcover w.asIdeal (hwP := w.isPrime) w.ne_bot
    exact ⟨t, HeightOneSpectrum.ext ((hv t).trans ht)⟩

end

end Residue
end RamanujanPetersson


end

-- ===== S4.Def_RP_Cone_ResStab =====
section

/-!
# S4-PD E4S arithmetic ResA, part 1: stabilisers in `π₁^geo` and Kummer characters under conjugation

* `stab_mem_inertia`: an element of `π₁^geo` stabilising a boundary prime `Q` of the pro-chart lies in its inertia group
  (every residue class mod `Q` is represented by a constant, and `π₁^geo` fixes the constants).
* `kchar_conj`: `kchar α (γ τ γ⁻¹) = kchar β τ` when `α = γ β` and `γ` fixes `ζ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Residue

noncomputable section

open CurveCoh GalCover Kummer CP4a
open scoped Pointwise

section Stab

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
  {R0 : Type} [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
  {p : ℕ} [Fact p.Prime] [CharP K p]

/-- **Decomposition = inertia in `π₁^geo`**: `σ ∈ π₁^geo` with `σ Q = Q` lies in `I(Q)`. -/
theorem stab_mem_inertia {e : ℕ} (he : 0 < e)
    (hζ : ∀ a, 0 < a → ∃ ζ : maxUnram A K, IsPrimitiveRoot ζ ((p ^ e) ^ a - 1))
    {Q : Ideal (proChart A K R0)} [Q.IsPrime] [Finite (R0 ⧸ Q.under R0)]
    (hcard : ∃ d, Nat.card (R0 ⧸ Q.under R0) = (p ^ e) ^ d) {σ : Pi1 A K} (hσ : σ ∈ pi1geo A K (p ^ e))
    (hQ : σ • Q = Q) : σ ∈ Q.inertia (Pi1 A K) := by
  refine AddSubgroup.mem_inertia.2 fun x => ?_
  obtain ⟨c, hc, hxc⟩ := exists_const_sub_mem he hζ hcard x
  have hσc : σ • c = c := Subtype.ext ((mem_pi1geo A K _ σ).1 hσ _ (mem_constSub.1 hc))
  have h1 : σ • (x - c) ∈ Q := by
    rw [← hQ]
    exact Ideal.smul_mem_pointwise_smul σ _ Q hxc
  have h2 : σ • x - x = σ • (x - c) - (x - c) := by
    rw [smul_sub, hσc]
    abel
  rw [h2]
  exact Q.sub_mem h1 hxc

end Stab

section Conj

variable {K E : Type} [Field K] [Field E] [Algebra K E] {N : ℕ} [NeZero N] {ζ : E}

/-- **Kummer characters under conjugation**: if `α = γ β`, `γ ζ = ζ` and `(τ β / β) ^ N = 1`, then
`kchar α (γ τ γ⁻¹) = kchar β τ`. -/
theorem kchar_conj (hζ : IsPrimitiveRoot ζ N) {J J' : Subgroup (E ≃ₐ[K] E)} {γ : E ≃ₐ[K] E} (hγ : γ ζ = ζ)
    {α β : Eˣ} (hβ : (α : E) = γ (β : E)) (τ : J) (hτ' : γ * (τ : E ≃ₐ[K] E) * γ⁻¹ ∈ J')
    (hpow : ((τ : E ≃ₐ[K] E) (β : E) / β) ^ N = 1) :
    kchar hζ (Γ := J') α ⟨γ * (τ : E ≃ₐ[K] E) * γ⁻¹, hτ'⟩ = kchar hζ (Γ := J) β τ := by
  have h1 : (γ * (τ : E ≃ₐ[K] E) * γ⁻¹) (α : E) / α = γ ((τ : E ≃ₐ[K] E) (β : E) / β) := by
    rw [map_div₀, hβ]
    simp only [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  have h2 : γ ((τ : E ≃ₐ[K] E) (β : E) / β) = (τ : E ≃ₐ[K] E) (β : E) / β := by
    rw [← epow_dlog hζ hpow]
    exact map_epow hγ _
  show dlog hζ _ = dlog hζ _
  rw [h1, h2]

end Conj

end

end Residue
end RamanujanPetersson


end

-- ===== S4.Def_RP_Cone_ResTr =====
section

/-!
# S4-PD E4S arithmetic ResA, part 2: transport of normalised generators under geometric conjugation

* `inclU_restrict`, `exists_valuation_transport` (L3): if `τ` is the restriction of `g` to a normal level `L`, the
  place of `L` under `g • Q` is the transport of the place under `Q`, and `v_{gQ}(τ b) = v_Q(b)`.
* `norm_conj` (L4, one level): a generator normalised at `(L, Q)` conjugates by `x` (fixing `ζ_N`) to a generator
  normalised at `(L, x • Q)`.
* `NormAll`, `normAll_conj` (L4, S3 chart): the same at all constant levels `M ⊔ K(𝔽_{p^(e k)})`, `k₀ ∣ k`.
* `chi_eq_of_norm` (L5): two generators normalised at the same prime have the same value under every locally
  constant hom `Γ_H → ℤ/N`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Residue

noncomputable section

open CurveCoh GalCover Kummer CP4a TameInertia IsDedekindDomain Polynomial
open scoped Pointwise

section Transport

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {R0 : Type} [CommRing R0] [Algebra R0 K]

/-- The restriction `τ` of `g` to `L` commutes with `inclU`. -/
theorem inclU_restrict {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)
    {g : Pi1 A K} {τ : L ≃ₐ[K] L}
    (hτ : ∀ y : L, ((τ y : L) : AlgebraicClosure K) =
      ((g (IntermediateField.inclusion hLU y) : maxUnram A K) : AlgebraicClosure K))
    (y : integralClosure R0 L) :
    inclU R0 hLU ((τ.restrictScalars R0).mapIntegralClosure y) = g • inclU R0 hLU y := by
  apply Subtype.ext
  apply Subtype.ext
  show ((τ (y : L) : L) : AlgebraicClosure K) =
    ((g ((inclU R0 hLU y : proChart A K R0) : maxUnram A K) : maxUnram A K) : AlgebraicClosure K)
  rw [hτ]
  rfl

/-- **(L3) Valuation transport**: the place under `g • Q` is the `τ`-transport of the place under `Q`. -/
theorem exists_valuation_transport {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)
    [IsDedekindDomain (integralClosure R0 L)] [IsFractionRing (integralClosure R0 L) L]
    {g : Pi1 A K} {τ : L ≃ₐ[K] L}
    (hτ : ∀ y : L, ((τ y : L) : AlgebraicClosure K) =
      ((g (IntermediateField.inclusion hLU y) : maxUnram A K) : AlgebraicClosure K))
    {Q : Ideal (proChart A K R0)} (v' : HeightOneSpectrum (integralClosure R0 L))
    (hv' : v'.asIdeal = (g • Q).comap (inclU R0 hLU)) :
    ∃ v : HeightOneSpectrum (integralClosure R0 L), v.asIdeal = Q.comap (inclU R0 hLU) ∧
      ∀ b : L, v'.valuation L (τ b) = v.valuation L b := by
  let e : integralClosure R0 L ≃+* integralClosure R0 L :=
    ((τ.restrictScalars R0).mapIntegralClosure).toRingEquiv
  have he : ∀ y, inclU R0 hLU (e y) = g • inclU R0 hLU y := inclU_restrict hLU hτ
  have hvv : HeightOneSpectrum.equivOfRingEquiv e (HeightOneSpectrum.equivOfRingEquiv e.symm v') = v' := by
    apply HeightOneSpectrum.ext
    ext y
    show e.symm.symm (e.symm y) ∈ v'.asIdeal ↔ y ∈ v'.asIdeal
    rw [RingEquiv.symm_symm, RingEquiv.apply_symm_apply]
  refine ⟨HeightOneSpectrum.equivOfRingEquiv e.symm v', ?_, fun b => ?_⟩
  · ext y
    show e.symm.symm y ∈ v'.asIdeal ↔ inclU R0 hLU y ∈ Q
    rw [RingEquiv.symm_symm, hv', Ideal.mem_comap, he, Ideal.smul_mem_pointwise_smul_iff]
  · have h := ZetaSB.valuation_equiv e (τ : L →+* L) (fun r => rfl)
      (HeightOneSpectrum.equivOfRingEquiv e.symm v') b
    rw [hvv] at h
    exact h

end Transport

section Conj

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {R0 : Type} [CommRing R0] [Algebra R0 K]

/-- **(L4) at one level**: if `τ ∈ J` (fixing `L`) is normalised at `(L, Q)` and `x` fixes `ζ_N`, then
`x τ x⁻¹ ∈ J'` is normalised at `(L, x • Q)`. -/
theorem norm_conj {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K) [Normal K L]
    [hD : IsDedekindDomain (integralClosure R0 L)] [hF : IsFractionRing (integralClosure R0 L) L]
    {N : ℕ} [NeZero N] {ζN : maxUnram A K} (hζN : IsPrimitiveRoot ζN N)
    {J J' : Subgroup (Pi1 A K)} (τ : J) {x : Pi1 A K} (hx : x ζN = ζN)
    (hτ' : x * (τ : Pi1 A K) * x⁻¹ ∈ J')
    (hτL : ∀ y : L, (τ : Pi1 A K) (IntermediateField.inclusion hLU y) = IntermediateField.inclusion hLU y)
    (Q : Ideal (proChart A K R0))
    (hn : ∀ v : HeightOneSpectrum (integralClosure R0 L), v.asIdeal = Q.comap (inclU R0 hLU) →
      ∀ (α : (maxUnram A K)ˣ) (b : L), (α : maxUnram A K) ^ N = IntermediateField.inclusion hLU b →
        kchar hζN (Γ := J) α τ = ((WithZero.log (v.valuation L b) : ℤ) : ZMod N))
    (v' : HeightOneSpectrum (integralClosure R0 L)) (hv' : v'.asIdeal = (x • Q).comap (inclU R0 hLU))
    (α : (maxUnram A K)ˣ) (b : L) (hαb : (α : maxUnram A K) ^ N = IntermediateField.inclusion hLU b) :
    kchar hζN (Γ := J') α ⟨x * (τ : Pi1 A K) * x⁻¹, hτ'⟩ =
      ((WithZero.log (v'.valuation L b) : ℤ) : ZMod N) := by
  obtain ⟨σL, hσL⟩ := exists_restrict hLU x
  obtain ⟨v, hv, hval⟩ := exists_valuation_transport hLU hσL v' hv'
  have hxi : ∀ y : L, x (IntermediateField.inclusion hLU y) = IntermediateField.inclusion hLU (σL y) :=
    fun y => Subtype.ext (hσL y).symm
  let β : (maxUnram A K)ˣ := Units.map (x⁻¹ : Pi1 A K).toRingEquiv.toMonoidHom α
  have hβ' : (β : maxUnram A K) = (x⁻¹ : Pi1 A K) α := rfl
  have hβ : (α : maxUnram A K) = x (β : maxUnram A K) := by
    rw [hβ', ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have hb' : (β : maxUnram A K) ^ N = IntermediateField.inclusion hLU (σL.symm b) := by
    have h := hxi (σL.symm b)
    rw [AlgEquiv.apply_symm_apply] at h
    rw [hβ', ← map_pow, hαb, ← h, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have hpow : ((τ : Pi1 A K) (β : maxUnram A K) / β) ^ N = 1 := by
    rw [div_pow, ← map_pow, hb', hτL, div_self]
    rw [← hb']
    exact pow_ne_zero _ β.ne_zero
  rw [kchar_conj hζN hx hβ τ hτ' hpow, hn v hv β (σL.symm b) hb', ← hval, AlgEquiv.apply_symm_apply]

end Conj

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

variable {p e : ℕ} [Fact p.Prime] [CharP F p]
variable (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

end S3

end

end Residue
end RamanujanPetersson


end

-- ===== S4.Def_RP_Cone_ResCos =====
section

/-!
# S4-PD E4S arithmetic ResA, part 3: cover points as cosets (pure group theory)

`π : G →* Gf`, `Γ ≤ G`, subgroups `I s`. The cover points are `CosT = Σ s, π(Γ) ⧸ π(Γ ∩ I s)` (left cosets), with lifts
`cosX t ∈ Γ` of the coset representatives (`cosX = 1` on the trivial coset).

* `cos_rep`: every `p ∈ π(Γ)` lies in exactly one coset `π(x_t) π(Γ ∩ I s)` over `s` (the `hrep` field of `ResDat`).
* `cos_cover`, `cos_disj`: for an action of `G` with `I s ≤ Stab(P s)`, every `γ • P s` (`γ ∈ Γ`) is `g • (x_t • P s)` with
  `g ∈ Γ ∩ ker π`, and such a `t` is unique when `Γ`-conjugate base points coincide and `Γ`-stabilisers lie in `I s`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Residue

noncomputable section

section Cos

variable {G Gf : Type} [Group G] [Group Gf] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)

/-- Cover points: `Σ s, π(Γ) ⧸ π(Γ ∩ I s)`. -/
abbrev CosT : Type := Σ s : S, (Γ.map π) ⧸ cosD π Γ I s

open Classical in
/-- A lift to `Γ` of the coset representative (`1` on the trivial coset). -/
def cosX (t : CosT π Γ I) : G :=
  if t.2 = ((1 : Γ.map π) : (Γ.map π) ⧸ cosD π Γ I t.1) then 1
  else Classical.choose (Subgroup.mem_map.1 (Quotient.out t.2).2)

variable {π Γ I}

theorem cosX_mem (t : CosT π Γ I) : cosX π Γ I t ∈ Γ := by
  unfold cosX
  split_ifs with h
  · exact Γ.one_mem
  · exact (Classical.choose_spec (Subgroup.mem_map.1 (Quotient.out t.2).2)).1

theorem cosX_base (s : S) :
    cosX π Γ I ⟨s, ((1 : Γ.map π) : (Γ.map π) ⧸ cosD π Γ I s)⟩ = 1 := by
  unfold cosX
  rw [if_pos rfl]

theorem cosX_map_mem (t : CosT π Γ I) : π (cosX π Γ I t) ∈ Γ.map π :=
  Subgroup.mem_map_of_mem π (cosX_mem t)

/-- The lift represents its coset. -/
theorem cosX_mk (t : CosT π Γ I) :
    ((⟨π (cosX π Γ I t), cosX_map_mem t⟩ : Γ.map π) : (Γ.map π) ⧸ cosD π Γ I t.1) = t.2 := by
  by_cases h : t.2 = ((1 : Γ.map π) : (Γ.map π) ⧸ cosD π Γ I t.1)
  · have hx : cosX π Γ I t = 1 := by unfold cosX; rw [if_pos h]
    have he : (⟨π (cosX π Γ I t), cosX_map_mem t⟩ : Γ.map π) = 1 :=
      Subtype.ext (by show π (cosX π Γ I t) = 1; rw [hx, map_one])
    rw [he]
    exact h.symm
  · have hx : cosX π Γ I t = Classical.choose (Subgroup.mem_map.1 (Quotient.out t.2).2) := by
      unfold cosX; rw [if_neg h]
    have hx' : π (cosX π Γ I t) = ((Quotient.out t.2 : Γ.map π) : Gf) := by
      rw [hx]; exact (Classical.choose_spec (Subgroup.mem_map.1 (Quotient.out t.2).2)).2
    have he : (⟨π (cosX π Γ I t), cosX_map_mem t⟩ : Γ.map π) = Quotient.out t.2 := Subtype.ext hx'
    rw [he]
    exact QuotientGroup.out_eq' t.2

theorem mem_cosD_iff {s : S} (a b : Γ.map π) :
    ((a : (Γ.map π) ⧸ cosD π Γ I s) = (b : (Γ.map π) ⧸ cosD π Γ I s)) ↔
      ((a : Gf))⁻¹ * b ∈ (Γ ⊓ I s).map π := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]

/-- **Coset partition** (`hrep`). -/
theorem cos_rep (s : S) (p : Gf) (hp : p ∈ Γ.map π) :
    ∃! t : CosT π Γ I, t.1 = s ∧ (π (cosX π Γ I t))⁻¹ * p ∈ (Γ ⊓ I s).map π := by
  refine ⟨⟨s, ((⟨p, hp⟩ : Γ.map π) : (Γ.map π) ⧸ cosD π Γ I s)⟩, ⟨rfl, ?_⟩, ?_⟩
  · have h := cosX_mk (π := π) (Γ := Γ) (I := I) ⟨s, ((⟨p, hp⟩ : Γ.map π) : (Γ.map π) ⧸ cosD π Γ I s)⟩
    exact (mem_cosD_iff (s := s) _ ⟨p, hp⟩).1 h
  · rintro ⟨s', q'⟩ ⟨h1, h2⟩
    dsimp only at h1
    subst h1
    have h := cosX_mk (π := π) (Γ := Γ) (I := I) ⟨_, q'⟩
    have h3 := (mem_cosD_iff ⟨π (cosX π Γ I ⟨_, q'⟩), cosX_map_mem _⟩ ⟨p, hp⟩).2 h2
    dsimp only at h
    rw [h] at h3
    rw [h3]

variable [Finite S] [Finite Gf]

instance finite_cosT : Finite (CosT π Γ I) := by
  have : ∀ s : S, Finite ((Γ.map π) ⧸ cosD π Γ I s) := fun s => Quotient.finite _
  exact Finite.instSigma

end Cos

section Act

variable {G Gf : Type} [Group G] [Group Gf] {π : G →* Gf} {Γ : Subgroup G} {S : Type} {I : S → Subgroup G}
  {X : Type} [MulAction G X] {P : S → X}

/-- **Cover**: `γ • P s` (`γ ∈ Γ`) is `g • (x_t • P s)` with `g ∈ Γ ∩ ker π`. -/
theorem cos_cover (hI : ∀ s, ∀ δ ∈ I s, δ • P s = P s) (s : S) {γ : G} (hγ : γ ∈ Γ) :
    ∃ t : CosT π Γ I, t.1 = s ∧ ∃ g ∈ Γ, π g = 1 ∧ γ • P s = g • (cosX π Γ I t • P s) := by
  obtain ⟨t, ⟨ht, hmem⟩, -⟩ := cos_rep (π := π) (Γ := Γ) (I := I) s (π γ) (Subgroup.mem_map_of_mem π hγ)
  obtain ⟨δ, hδ, hδπ⟩ := Subgroup.mem_map.1 hmem
  have hδΓ := (Subgroup.mem_inf.1 hδ).1
  have hδI := (Subgroup.mem_inf.1 hδ).2
  refine ⟨t, ht, γ * δ⁻¹ * (cosX π Γ I t)⁻¹,
    Γ.mul_mem (Γ.mul_mem hγ (Γ.inv_mem hδΓ)) (Γ.inv_mem (cosX_mem t)), ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv, map_inv, hδπ]
    group
  · rw [smul_smul, inv_mul_cancel_right, mul_smul, hI s δ⁻¹ ((I s).inv_mem hδI)]

/-- **Disjointness**: the cover point is unique. -/
theorem cos_disj (hdisj : ∀ s s', ∀ u ∈ Γ, P s' = u • P s → s = s')
    (hstab : ∀ s, ∀ u ∈ Γ, u • P s = P s → u ∈ I s) (t t' : CosT π Γ I) {g : G} (hg : g ∈ Γ) (hgπ : π g = 1)
    (h : cosX π Γ I t' • P t'.1 = g • (cosX π Γ I t • P t.1)) : t = t' := by
  obtain ⟨s, q⟩ := t
  obtain ⟨s', q'⟩ := t'
  dsimp only at h
  set u := (cosX π Γ I ⟨s', q'⟩)⁻¹ * g * cosX π Γ I ⟨s, q⟩ with hu
  have huΓ : u ∈ Γ := Γ.mul_mem (Γ.mul_mem (Γ.inv_mem (cosX_mem _)) hg) (cosX_mem _)
  have hP : P s' = u • P s := by
    rw [hu, mul_smul, mul_smul, ← h, inv_smul_smul]
  have hss : s = s' := hdisj s s' u huΓ hP
  subst hss
  have huI : u ∈ I s := hstab s u huΓ hP.symm
  have hrep := cos_rep (π := π) (Γ := Γ) (I := I) s (π (cosX π Γ I ⟨s, q⟩)) (cosX_map_mem _)
  refine hrep.unique ⟨rfl, ?_⟩ ⟨rfl, ?_⟩
  · rw [inv_mul_cancel]
    exact Subgroup.one_mem _
  · refine Subgroup.mem_map.2 ⟨u, Subgroup.mem_inf.2 ⟨huΓ, huI⟩, ?_⟩
    rw [hu, map_mul, map_mul, map_inv, hgπ, mul_one]

end Act

end

end Residue
end RamanujanPetersson


end

-- ===== S4.Def_RP_Cone_E4SInd =====
section

/-!
# S4-PD E4S, part 4: sections and induction cocycles

* `secOf π Δ p`: a section of `π` over `π(Δ)` with values in `Δ`.
* `lc_of_cocycle`: a cocycle vanishing on an open neighbourhood of `1` is locally constant.
* `indCoc`: the induction cocycle `g ↦ Σ_p p · χ((sec p)⁻¹ g sec((π g)⁻¹ p))` of a locally constant homomorphism
  `χ : Δ ∩ ker π → Λ`, a locally constant cocycle of `Δ` with values in `Λ[Gf]`.
* `coeff_nrmS`, `sum_single_ind`: norm elements through indicator coefficients.
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace PerfectCx

noncomputable section

open CurveCoh MonoidAlgebra

section Sec

variable {Gf : Type} [Group Gf] {G : Type} [Group G] (π : G →* Gf) (Δ : Subgroup G)

open Classical in
/-- A section of `π` over `π(Δ)` with values in `Δ`. -/
def secOf (p : Gf) : G := if h : p ∈ Δ.map π then (Subgroup.mem_map.1 h).choose else 1

theorem secOf_mem (p : Gf) : secOf π Δ p ∈ Δ := by
  unfold secOf
  split_ifs with h
  · exact (Subgroup.mem_map.1 h).choose_spec.1
  · exact Δ.one_mem

theorem secOf_map {p : Gf} (hp : p ∈ Δ.map π) : π (secOf π Δ p) = p := by
  unfold secOf
  rw [dif_pos hp]
  exact (Subgroup.mem_map.1 hp).choose_spec.2

/-- `π g` as an element of `π(Δ)`. -/
def gP (g : Δ) : Δ.map π := ⟨π g, Subgroup.mem_map_of_mem π g.2⟩

end Sec

section LC

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] (ρ : Representation k G M) (Δ : Subgroup G)

omit [IsTopologicalGroup G] in
/-- A cocycle vanishing on an open neighbourhood of `1` is locally constant. -/
theorem lc_of_cocycle [IsTopologicalGroup G] {c : Δ → M} (hc : ∀ g h : Δ, c (g * h) = c g + ρ g (c h))
    {W : Set Δ} (hW : IsOpen W) (h1 : (1 : Δ) ∈ W) (hW0 : ∀ w ∈ W, c w = 0) : IsLocallyConstant c := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨(g * ·) '' W, isOpenMap_mul_left g W hW, ⟨1, h1, mul_one g⟩, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  show c (g * w) = c g
  rw [hc, hW0 w hw, map_zero, add_zero]

end LC

section Ind

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Δ : Subgroup G) (K : Subgroup G)
  (hK : ∀ g, g ∈ K ↔ g ∈ Δ ∧ π g = 1)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
include hK in
theorem indK_mem (p : Δ.map π) (g : Δ) :
    (secOf π Δ p)⁻¹ * (g : G) * secOf π Δ ((π (g : G))⁻¹ * p) ∈ K := by
  have hq : (π (g : G))⁻¹ * (p : Gf) ∈ Δ.map π :=
    (Δ.map π).mul_mem ((Δ.map π).inv_mem (Subgroup.mem_map_of_mem π g.2)) p.2
  refine (hK _).2 ⟨Δ.mul_mem (Δ.mul_mem (Δ.inv_mem (secOf_mem π Δ _)) g.2) (secOf_mem π Δ _), ?_⟩
  rw [map_mul, map_mul, map_inv, secOf_map π Δ p.2, secOf_map π Δ hq]
  group

/-- `(sec p)⁻¹ g sec((π g)⁻¹ p) ∈ Δ ∩ ker π`. -/
def indK (p : Δ.map π) (g : Δ) : K := ⟨_, indK_mem π Δ K hK p g⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem indK_mul (p : Δ.map π) (g h : Δ) :
    indK π Δ K hK p (g * h) = indK π Δ K hK p g * indK π Δ K hK ((gP π Δ g)⁻¹ * p) h := by
  have e : (π ((g : G) * h))⁻¹ * (p : Gf) = (π (h : G))⁻¹ * ((π (g : G))⁻¹ * p) := by
    rw [map_mul, mul_inv_rev, mul_assoc]
  apply Subtype.ext
  show (secOf π Δ p)⁻¹ * ((g * h : Δ) : G) * secOf π Δ ((π ((g * h : Δ) : G))⁻¹ * p) =
    (secOf π Δ p)⁻¹ * (g : G) * secOf π Δ ((π (g : G))⁻¹ * p) *
      ((secOf π Δ ((π (g : G))⁻¹ * p))⁻¹ * (h : G) * secOf π Δ ((π (h : G))⁻¹ * ((π (g : G))⁻¹ * p)))
  rw [Subgroup.coe_mul, e]
  group

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem indK_coe_of_ker (p : Δ.map π) (w : Δ) (hw : π (w : G) = 1) :
    (indK π Δ K hK p w : G) = (secOf π Δ p)⁻¹ * w * secOf π Δ p := by
  show (secOf π Δ p)⁻¹ * (w : G) * secOf π Δ ((π (w : G))⁻¹ * p) = _
  rw [hw, inv_one, one_mul]

variable [Fintype (Δ.map π)]

/-- The induction cochain of `χ : Δ ∩ ker π → Λ`. -/
def indFun (χ : K → Λ) (g : Δ) : MonoidAlgebra Λ Gf :=
  ∑ p : Δ.map π, single (p : Gf) (χ (indK π Δ K hK p g))

theorem indFun_mul (χ : K → Λ) (hχ : ∀ a b, χ (a * b) = χ a + χ b) (g h : Δ) :
    indFun π Δ K hK χ (g * h) = indFun π Δ K hK χ g + regRep Λ π (g : G) (indFun π Δ K hK χ h) := by
  have e1 : regRep Λ π (g : G) (indFun π Δ K hK χ h) =
      ∑ p : Δ.map π, single (p : Gf) (χ (indK π Δ K hK ((gP π Δ g)⁻¹ * p) h)) := by
    rw [regRep_apply]
    unfold indFun
    rw [Finset.mul_sum]
    simp only [single_mul_single, one_mul]
    exact Fintype.sum_equiv (Equiv.mulLeft (gP π Δ g)) _ _ (fun p => by
      rw [Equiv.coe_mulLeft, inv_mul_cancel_left]
      rfl)
  rw [e1]
  unfold indFun
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← single_add, ← hχ, ← indK_mul]

theorem indFun_lc (hπ : IsOpen (π.ker : Set G)) (χ : K → Λ) (hχc : IsLocallyConstant χ)
    (hχ : ∀ a b, χ (a * b) = χ a + χ b) : IsLocallyConstant (indFun π Δ K hK χ) := by
  have h10 : χ 1 = 0 := by
    have h := hχ 1 1
    rw [mul_one] at h
    simpa using h
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp (hχc {0})
  have hO0 : ∀ k : K, (k : G) ∈ O → χ k = 0 := fun k hk => by
    have h : k ∈ χ ⁻¹' {0} := by rw [← hOeq]; exact hk
    exact h
  have h1O : (1 : G) ∈ O := by
    have h : (1 : K) ∈ χ ⁻¹' {0} := h10
    rw [← hOeq] at h
    exact h
  refine lc_of_cocycle (regRep Λ π) Δ (indFun_mul π Δ K hK χ hχ)
    (W := ⋂ p : Δ.map π, (fun w : Δ => (secOf π Δ p)⁻¹ * (w : G) * secOf π Δ p) ⁻¹' (O ∩ π.ker)) ?_ ?_ ?_
  · exact isOpen_iInter_of_finite fun p => (hO.inter hπ).preimage (by fun_prop)
  · simp only [Set.mem_iInter, Set.mem_preimage, OneMemClass.coe_one, mul_one, inv_mul_cancel]
    exact fun _ => ⟨h1O, π.ker.one_mem⟩
  · intro w hw
    have hw' := Set.mem_iInter.1 hw
    have hw1 : π (w : G) = 1 := by
      have h := (hw' 1).2
      rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_mul, map_inv,
        secOf_map π Δ (1 : Δ.map π).2] at h
      simpa using h
    unfold indFun
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [hO0 _ ?_, single_zero]
    rw [indK_coe_of_ker π Δ K hK p w hw1]
    exact (hw' p).1

/-- The induction cocycle of a locally constant homomorphism `χ : Δ ∩ ker π → Λ`. -/
def indCoc (hπ : IsOpen (π.ker : Set G)) (χ : K → Λ) (hχc : IsLocallyConstant χ)
    (hχ : ∀ a b, χ (a * b) = χ a + χ b) : Z1 (regRep Λ π) Δ :=
  ⟨indFun π Δ K hK χ, (mem_Z1 _ _ _).2 ⟨indFun_lc π Δ K hK hπ χ hχc hχ, indFun_mul π Δ K hK χ hχ⟩⟩

theorem indCoc_apply (hπ : IsOpen (π.ker : Set G)) (χ : K → Λ) (hχc : IsLocallyConstant χ)
    (hχ : ∀ a b, χ (a * b) = χ a + χ b) (g : Δ) :
    (indCoc π Δ K hK hπ χ hχc hχ : Δ → MonoidAlgebra Λ Gf) g = indFun π Δ K hK χ g := rfl

end Ind

section Norm

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf]

open Classical in
theorem coeff_nrmS (D : Subgroup Gf) [Fintype D] (z : Gf) :
    (nrmS Λ D).coeff z = if z ∈ D then 1 else 0 := by
  unfold nrmS
  rw [coeff_sum, Finsupp.finsetSum_apply]
  simp only [coeff_single, Finsupp.single_apply]
  split_ifs with hz
  · rw [Finset.sum_eq_single ⟨z, hz⟩ (fun d _ hd => if_neg fun h => hd (Subtype.ext h))
      (fun h => absurd (Finset.mem_univ _) h), if_pos rfl]
  · exact Finset.sum_eq_zero fun d _ => if_neg fun h : (d : Gf) = z => hz (h ▸ d.2)

open Classical in
/-- `Σ_{p ∈ P} [p q ∈ D] p = N_D · q⁻¹` for `D ≤ P`, `q ∈ P`. -/
theorem sum_single_ind (P D : Subgroup Gf) [Fintype P] [Fintype D] (hDP : D ≤ P) (q : Gf) (hq : q ∈ P) :
    ∑ p : P, single (p : Gf) (if (p : Gf) * q ∈ D then (1 : Λ) else 0) = nrmS Λ D * single q⁻¹ 1 := by
  ext y
  rw [coeff_mul_single_apply, coeff_nrmS, inv_inv, mul_one, coeff_sum, Finsupp.finsetSum_apply]
  simp only [coeff_single, Finsupp.single_apply]
  by_cases hy : y ∈ P
  · rw [Finset.sum_eq_single ⟨y, hy⟩ (fun p _ hp => if_neg fun h => hp (Subtype.ext h))
      (fun h => absurd (Finset.mem_univ _) h), if_pos rfl]
  · have hyq : ¬ y * q ∈ D := fun h => hy (by simpa using P.mul_mem (hDP h) (P.inv_mem hq))
    rw [Finset.sum_eq_zero fun (p : P) _ => if_neg fun h : (p : Gf) = y => hy (h ▸ p.2), if_neg hyq]

end Norm

end

end PerfectCx
end RamanujanPetersson


end

-- ===== S4.Def_RP_TameInertia_Coef =====
section

/-!
# Tame inertia, part Coef: homomorphisms to `N`-torsion modules (S4-PD item (2), T9)

Abstract step: let `θ : Γ → ℤ/N` with `θ σ₀ = 1` be such that every locally constant homomorphism `Γ → ℤ/N` is a
multiple of `θ`. Then for every abelian group `M` killed by `N`, every locally constant homomorphism `χ : Γ → M` is
`σ ↦ (θ σ).val • χ σ₀` (`eq_val_nsmul_of_gen`), and conversely `σ ↦ (θ σ).val • m` is a locally constant homomorphism
for every `m` with value `m` at `σ₀`. So `Hom(Γ, M) ≅ M` by evaluation at `σ₀`. The proof separates points of `M` by
characters `M → ℚ/ℤ` (`CharacterModule`) and identifies the `N`-torsion of `ℚ/ℤ` with `ℤ/N` (`toQCircle`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace TameInertia

noncomputable section

section Circ

variable (N : ℕ) [NeZero N]

/-- `ℤ/N → ℚ/ℤ`, `j ↦ j / N`. -/
def toQCircle : ZMod N →+ AddCircle (1 : ℚ) :=
  ZMod.lift N ⟨AddMonoidHom.mk' (fun j : ℤ ↦ ((j / N : ℚ) : AddCircle (1 : ℚ))) (by simp [add_div]),
    by simp [div_self (NeZero.ne _)]⟩

theorem toQCircle_intCast (j : ℤ) : toQCircle N (j : ZMod N) = ((j / N : ℚ) : AddCircle (1 : ℚ)) := by
  simp [toQCircle]

theorem toQCircle_natCast (j : ℕ) : toQCircle N (j : ZMod N) = ((j / N : ℚ) : AddCircle (1 : ℚ)) := by
  simpa using toQCircle_intCast N j

theorem toQCircle_apply (j : ZMod N) : toQCircle N j = ((j.val / N : ℚ) : AddCircle (1 : ℚ)) := by
  rw [← toQCircle_natCast, ZMod.natCast_zmod_val]

theorem toQCircle_injective : Function.Injective (toQCircle N) := by
  haveI : Fact ((0 : ℚ) < 1) := ⟨one_pos⟩
  intro x y hxy
  have : (0 : ℚ) < N := Nat.cast_pos.mpr (NeZero.pos _)
  rwa [toQCircle_apply, toQCircle_apply, AddCircle.coe_eq_coe_iff_of_mem_Ico,
    div_left_inj' this.ne', Nat.cast_inj, (ZMod.val_injective N).eq_iff] at hxy <;>
  exact ⟨by positivity, by simpa only [zero_add, div_lt_one this, Nat.cast_lt] using ZMod.val_lt _⟩

/-- The `N`-torsion of `ℚ/ℤ` is the image of `ℤ/N`. -/
theorem exists_toQCircle_eq {y : AddCircle (1 : ℚ)} (hy : N • y = 0) : ∃ k : ZMod N, toQCircle N k = y := by
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1 : ℚ)) y
  have h : (((N : ℚ) * q : ℚ) : AddCircle (1 : ℚ)) = 0 := by
    rw [← nsmul_eq_mul, AddCircle.coe_nsmul]
    exact hy
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (1 : ℚ)).1 h
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hq : (m : ℚ) / N = q := by
    rw [zsmul_eq_mul, mul_one] at hm
    rw [hm, mul_div_cancel_left₀ _ hN]
  refine ⟨(m : ZMod N), ?_⟩
  rw [toQCircle_intCast, hq]

end Circ

section Gen

variable {Γ : Type*} [Mul Γ] [TopologicalSpace Γ] {N : ℕ} [NeZero N] {θ : Γ → ZMod N}
  {M : Type*} [AddCommGroup M] (hM : ∀ m : M, N • m = 0)

include hM in
/-- **T9.** If every locally constant homomorphism `Γ → ℤ/N` is a multiple of `θ` and `θ σ₀ = 1`, then every locally
constant homomorphism `χ : Γ → M` to an abelian group killed by `N` is `σ ↦ (θ σ).val • χ σ₀`. -/
theorem eq_val_nsmul_of_gen {σ₀ : Γ} (hθ : θ σ₀ = 1)
    (hgen : ∀ χ : Γ → ZMod N, IsLocallyConstant χ → (∀ σ τ, χ (σ * τ) = χ σ + χ τ) →
      ∃ k : ZMod N, ∀ σ, χ σ = k * θ σ)
    (χ : Γ → M) (hχc : IsLocallyConstant χ) (hχ : ∀ σ τ, χ (σ * τ) = χ σ + χ τ) (σ : Γ) :
    χ σ = (θ σ).val • χ σ₀ := by
  classical
  rw [← sub_eq_zero]
  refine CharacterModule.eq_zero_of_character_apply fun c => ?_
  have hex : ∀ σ, ∃ k : ZMod N, toQCircle N k = c (χ σ) := fun σ =>
    exists_toQCircle_eq N (by rw [← map_nsmul, hM, map_zero])
  let g : AddCircle (1 : ℚ) → ZMod N := fun y => if h : ∃ k, toQCircle N k = y then h.choose else 0
  have hg : ∀ σ, toQCircle N (g (c (χ σ))) = c (χ σ) := fun σ => by
    simp only [g, dif_pos (hex σ)]
    exact (hex σ).choose_spec
  have hgc : IsLocallyConstant (fun σ => g (c (χ σ))) := hχc.comp (fun m => g (c m))
  have hgm : ∀ σ τ, g (c (χ (σ * τ))) = g (c (χ σ)) + g (c (χ τ)) := fun σ τ =>
    toQCircle_injective N (by rw [map_add, hg, hg, hg, hχ, map_add])
  obtain ⟨k, hk⟩ := hgen _ hgc hgm
  have e : ∀ τ, c (χ τ) = (θ τ).val • toQCircle N k := fun τ => by
    rw [← hg τ, hk τ, ← map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]
  have e0 : c (χ σ₀) = toQCircle N k := by
    rw [← hg σ₀, hk σ₀, hθ, mul_one]
  rw [map_sub, map_nsmul, e σ, e0, sub_self]

end Gen

end

end TameInertia
end RamanujanPetersson


end

-- ===== S4.Def_RP_Cone_E4SLoc =====
section

/-!
# S4-PD E4S, part 5a: local residue hypotheses from normalised generators

* `LocGen J I' N τ`: the body of `Residue.TauProp` with the inertia group as a parameter `I'`.
* `LocGen.eq_zero`, `LocGen.conj`: locally constant homomorphisms `J → M` (`N M = 0`) are determined by the
  value at `τ`, which is invariant under conjugation by `I'`.
* `hom_conj`, `sum_eq_zero_of_zmod` (transfer of a `ℤ/N`-valued vanishing statement to `N`-torsion groups).
* `zlift : ℤ/N →+ Λ` (`N = 0` in `Λ`), `resK` (restriction of a cocycle to `Δ ∩ ker π`).
* `ldet_of_locGen`, `linv_of_locGen`, `lex_of_locGen`: the hypotheses `Ldet`, `Linv`, `Lex` of `ResHyp`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

noncomputable section

open CurveCoh MonoidAlgebra TameInertia

section Gen

/-- A normalised generator `τ` of `J` with its character `θ` (the shape of `Residue.TauProp`, with the
inertia group `I'` as a parameter). -/
abbrev LocGen {G : Type} [Group G] [TopologicalSpace G] (J I' : Subgroup G) (N : ℕ) (τ : J) : Prop :=
  ∃ θ : J → ZMod N, IsLocallyConstant θ ∧ (∀ σ σ', θ (σ * σ') = θ σ + θ σ') ∧ θ τ = 1 ∧
    (∀ g ∈ I', ∀ σ (hσ : σ ∈ J) (hσ' : g⁻¹ * σ * g ∈ J), θ ⟨g⁻¹ * σ * g, hσ'⟩ = θ ⟨σ, hσ⟩) ∧
    (∀ χ : J → ZMod N, IsLocallyConstant χ → (∀ σ σ', χ (σ * σ') = χ σ + χ σ') → ∀ σ, χ σ = χ τ * θ σ)

variable {G : Type} [Group G] [TopologicalSpace G] {J I' : Subgroup G} {N : ℕ} [NeZero N] {τ : J}
  {M : Type*} [AddCommGroup M]

theorem LocGen.eq_zero (h : LocGen J I' N τ) (hM : ∀ m : M, N • m = 0) (ψ : J → M) (hψc : IsLocallyConstant ψ)
    (hψ : ∀ a b, ψ (a * b) = ψ a + ψ b) (h0 : ψ τ = 0) (j : J) : ψ j = 0 := by
  obtain ⟨θ, -, -, hθ1, -, hgen⟩ := h
  rw [eq_val_nsmul_of_gen hM hθ1 (fun χ hχc hχ => ⟨χ τ, hgen χ hχc hχ⟩) ψ hψc hψ j, h0, nsmul_zero]

theorem LocGen.conj (h : LocGen J I' N τ) (hM : ∀ m : M, N • m = 0) (ψ : J → M) (hψc : IsLocallyConstant ψ)
    (hψ : ∀ a b, ψ (a * b) = ψ a + ψ b) (g : G) (hg : g ∈ I') (hj : g * τ * g⁻¹ ∈ J) :
    ψ ⟨g * τ * g⁻¹, hj⟩ = ψ τ := by
  obtain ⟨θ, -, -, hθ1, hθc, hgen⟩ := h
  have hj' : g⁻¹⁻¹ * (τ : G) * g⁻¹ ∈ J := by rwa [inv_inv]
  have e : (⟨g * τ * g⁻¹, hj⟩ : J) = ⟨g⁻¹⁻¹ * τ * g⁻¹, hj'⟩ :=
    Subtype.ext (by show g * (τ : G) * g⁻¹ = g⁻¹⁻¹ * τ * g⁻¹; rw [inv_inv])
  have hθ : θ ⟨g * τ * g⁻¹, hj⟩ = 1 := by
    rw [e]
    exact (hθc g⁻¹ (I'.inv_mem hg) τ τ.2 hj').trans hθ1
  rw [eq_val_nsmul_of_gen hM hθ1 (fun χ hχc hχ => ⟨χ τ, hgen χ hχc hχ⟩) ψ hψc hψ ⟨g * τ * g⁻¹, hj⟩, hθ,
    one_val_nsmul hM]

/-- A homomorphism to an abelian group is conjugation invariant. -/
theorem hom_conj {H : Type*} [Group H] (χ : H → M) (hχ : ∀ a b, χ (a * b) = χ a + χ b) (h z : H) :
    χ (h * z * h⁻¹) = χ z := by
  have h1 : χ 1 = 0 := by
    have e := hχ 1 1
    rw [mul_one] at e
    simpa using e
  have h2 : χ h + χ h⁻¹ = 0 := by rw [← hχ, mul_inv_cancel, h1]
  rw [hχ, hχ, add_right_comm, h2, zero_add]

/-- Transfer of a `ℤ/N`-valued vanishing statement to every abelian group killed by `N`
(characters `M → ℚ/ℤ`, as in `TameInertia.eq_val_nsmul_of_gen`). -/
theorem sum_eq_zero_of_zmod {H : Type*} [Mul H] [TopologicalSpace H] {T : Type*} [Fintype T] (y : T → H)
    (hR : ∀ χ : H → ZMod N, IsLocallyConstant χ → (∀ a b, χ (a * b) = χ a + χ b) → ∑ t, χ (y t) = 0)
    (hM : ∀ m : M, N • m = 0) (χ : H → M) (hχc : IsLocallyConstant χ)
    (hχ : ∀ a b, χ (a * b) = χ a + χ b) : ∑ t, χ (y t) = 0 := by
  classical
  refine CharacterModule.eq_zero_of_character_apply fun c => ?_
  have hex : ∀ σ, ∃ k : ZMod N, toQCircle N k = c (χ σ) := fun σ =>
    exists_toQCircle_eq N (by rw [← map_nsmul, hM, map_zero])
  let g : AddCircle (1 : ℚ) → ZMod N := fun z => if h : ∃ k, toQCircle N k = z then h.choose else 0
  have hg : ∀ σ, toQCircle N (g (c (χ σ))) = c (χ σ) := fun σ => by
    simp only [g, dif_pos (hex σ)]
    exact (hex σ).choose_spec
  have hgc : IsLocallyConstant (fun σ => g (c (χ σ))) := hχc.comp (fun m => g (c m))
  have hgm : ∀ σ τ, g (c (χ (σ * τ))) = g (c (χ σ)) + g (c (χ τ)) := fun σ τ =>
    toQCircle_injective N (by rw [map_add, hg, hg, hg, hχ, map_add])
  have h0 : ∑ t, g (c (χ (y t))) = 0 := hR _ hgc hgm
  rw [map_sum]
  calc ∑ t, c (χ (y t)) = ∑ t, toQCircle N (g (c (χ (y t)))) :=
        Finset.sum_congr rfl fun t _ => (hg (y t)).symm
    _ = toQCircle N (∑ t, g (c (χ (y t)))) := (map_sum _ _ _).symm
    _ = 0 := by rw [h0, map_zero]

end Gen

section Loc

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf)

theorem nsmul_alg {N : ℕ} (hN : (N : Λ) = 0) (a : MonoidAlgebra Λ Gf) : N • a = 0 := by
  rw [← Nat.cast_smul_eq_nsmul Λ, hN, zero_smul]

variable (Λ) in
/-- `ℤ/N → Λ` for `N = 0` in `Λ`. -/
def zlift (N : ℕ) (hN : (N : Λ) = 0) : ZMod N →+ Λ :=
  ZMod.lift N ⟨Int.castAddHom Λ, by simp [hN]⟩

theorem zlift_one {N : ℕ} (hN : (N : Λ) = 0) : zlift Λ N hN 1 = 1 := by
  have h : ((1 : ℤ) : ZMod N) = 1 := Int.cast_one
  rw [← h, zlift, ZMod.lift_coe]
  simp

theorem zlift_ite {N : ℕ} (hN : (N : Λ) = 0) (P : Prop) [Decidable P] :
    zlift Λ N hN (if P then 1 else 0) = if P then 1 else 0 := by
  split_ifs
  · exact zlift_one hN
  · exact map_zero _

/-- Restriction of a cocycle on `Δ` to `K = Δ ∩ ker π`. -/
def resK (Δ K : Subgroup G) (hK : ∀ g, g ∈ K ↔ g ∈ Δ ∧ π g = 1) (e : Z1 (regRep Λ π) Δ) (k : K) :
    MonoidAlgebra Λ Gf :=
  (e : Δ → MonoidAlgebra Λ Gf) ⟨k, ((hK k).1 k.2).1⟩

theorem resK_lc (Δ K : Subgroup G) (hK : ∀ g, g ∈ K ↔ g ∈ Δ ∧ π g = 1) (e : Z1 (regRep Λ π) Δ) :
    IsLocallyConstant (resK π Δ K hK e) :=
  ((mem_Z1 _ _ _).1 e.2).1.comp_continuous (continuous_subtype_val.subtype_mk _)

theorem resK_add (Δ K : Subgroup G) (hK : ∀ g, g ∈ K ↔ g ∈ Δ ∧ π g = 1) (e : Z1 (regRep Λ π) Δ)
    (a b : K) : resK π Δ K hK e (a * b) = resK π Δ K hK e a + resK π Δ K hK e b := by
  have hc := ((mem_Z1 _ _ _).1 e.2).2 ⟨a, ((hK a).1 a.2).1⟩ ⟨b, ((hK b).1 b.2).1⟩
  have ha : ∀ x, regRep Λ π (a : G) x = x := fun x => by
    rw [regRep_apply, ((hK a).1 a.2).2, ← one_def, one_mul]
  exact hc.trans (congrArg (fun z => (e : Δ → MonoidAlgebra Λ Gf) ⟨a, ((hK a).1 a.2).1⟩ + z) (ha _))

variable {N : ℕ} [NeZero N]

/-- (Ldet) from `LocGen`. -/
theorem ldet_of_locGen {Δ K I' : Subgroup G} (hK : ∀ g, g ∈ K ↔ g ∈ Δ ∧ π g = 1) {τ : K}
    (h : LocGen K I' N τ) (hN : (N : Λ) = 0) (e : Z1 (regRep Λ π) Δ)
    (h0 : (e : Δ → MonoidAlgebra Λ Gf) ⟨τ, ((hK τ).1 τ.2).1⟩ = 0) (j : Δ) (hj : π j = 1) :
    (e : Δ → MonoidAlgebra Λ Gf) j = 0 :=
  h.eq_zero (nsmul_alg hN) _ (resK_lc π Δ K hK e) (resK_add π Δ K hK e) h0 ⟨j, (hK j).2 ⟨j.2, hj⟩⟩

/-- (Linv) from `LocGen`. -/
theorem linv_of_locGen {Δ K I' : Subgroup G} (hK : ∀ g, g ∈ K ↔ g ∈ Δ ∧ π g = 1) (hΔ : Δ ≤ I') {τ : K}
    (h : LocGen K I' N τ) (hN : (N : Λ) = 0) (e : Z1 (regRep Λ π) Δ) (g : Δ) :
    (e : Δ → MonoidAlgebra Λ Gf) (g * ⟨τ, ((hK τ).1 τ.2).1⟩ * g⁻¹) =
      (e : Δ → MonoidAlgebra Λ Gf) ⟨τ, ((hK τ).1 τ.2).1⟩ := by
  have hτ := (hK τ).1 τ.2
  have hj : (g : G) * τ * (g : G)⁻¹ ∈ K := (hK _).2 ⟨Δ.mul_mem (Δ.mul_mem g.2 hτ.1) (Δ.inv_mem g.2), by
    rw [map_mul, map_mul, map_inv, hτ.2, mul_one, mul_inv_cancel]⟩
  exact h.conj (nsmul_alg hN) _ (resK_lc π Δ K hK e) (resK_add π Δ K hK e) g (hΔ g.2) hj

/-- (Lex) from `LocGen`: the induction cocycle of `θ` takes the value `N_{π Δ}` at `τ`. -/
theorem lex_of_locGen {Δ K I' : Subgroup G} [Fintype (Δ.map π)] (hK : ∀ g, g ∈ K ↔ g ∈ Δ ∧ π g = 1)
    (hΔ : Δ ≤ I') {τ : K} (h : LocGen K I' N τ) (hN : (N : Λ) = 0) (hπ : IsOpen (π.ker : Set G)) :
    ∃ ε : Z1 (regRep Λ π) Δ, (ε : Δ → MonoidAlgebra Λ Gf) ⟨τ, ((hK τ).1 τ.2).1⟩ = nrmS Λ (Δ.map π) := by
  obtain ⟨θ, hθc, hθ, hθ1, hθconj, -⟩ := h
  refine ⟨indCoc π Δ K hK hπ (fun k => zlift Λ N hN (θ k)) (hθc.comp fun z => zlift Λ N hN z)
    (fun a b => by simp only [hθ, map_add]), ?_⟩
  rw [indCoc_apply]
  unfold indFun nrmS
  refine Finset.sum_congr rfl fun p _ => ?_
  have hw : π ((⟨τ, ((hK τ).1 τ.2).1⟩ : Δ) : G) = 1 := ((hK τ).1 τ.2).2
  have hc := indK_coe_of_ker π Δ K hK p ⟨τ, ((hK τ).1 τ.2).1⟩ hw
  have hj : (secOf π Δ p)⁻¹ * (τ : G) * secOf π Δ p ∈ K :=
    (congrArg (· ∈ K) hc).mp (indK π Δ K hK p ⟨τ, ((hK τ).1 τ.2).1⟩).2
  have e : indK π Δ K hK p ⟨τ, ((hK τ).1 τ.2).1⟩ = ⟨_, hj⟩ := Subtype.ext hc
  have key : θ (indK π Δ K hK p ⟨τ, ((hK τ).1 τ.2).1⟩) = 1 :=
    (congrArg θ e).trans ((hθconj _ (hΔ (secOf_mem π Δ p)) τ τ.2 hj).trans hθ1)
  show single (p : Gf) (zlift Λ N hN (θ (indK π Δ K hK p ⟨τ, ((hK τ).1 τ.2).1⟩))) = single (p : Gf) 1
  rw [key, zlift_one]

end Loc

end

end PerfectCx
end RamanujanPetersson


end

-- ===== S4.Def_RP_Cone_E4SDat =====
section

/-!
# S4-PD E4S, part 5b: the residue hypotheses from local and cover-level data

`ResDat` collects data in the shape the arithmetic side produces: normalised generators `σ s` with `LocGen`,
cover points `t : T` over `sh t : S` with conjugators `x t ∈ Γ` and `y t = x t σ (sh t) (x t)⁻¹ ∈ Γ_H = Γ ∩ ker π`,
the coset condition `hrep`, the residue theorem `hR` and the existence statement `hE` (both `ℤ/N`-valued).
`ResDat.toResHyp` builds the `ResHyp` of part 2 over any `Λ` with `N = 0` in `Λ`
(`GR` via `conj_x`, `GE1`/`GE2` via the global induction cocycle `exists_glob` and `conj_eq`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

noncomputable section

open CurveCoh MonoidAlgebra TameInertia

section Dat

variable {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (π : G →* Gf) (Γ : Subgroup G) {S : Type} [Fintype S] [DecidableEq S] (I : S → Subgroup G)
  (N : ℕ) (T : Type) [Fintype T]

/-- Local and cover-level input for `ResHyp`: generators `σ s` with `LocGen`, cover points `t` over `sh t` with
`y t = x t σ (sh t) (x t)⁻¹ ∈ Γ_H`, the coset condition `hrep`, the residue theorem `hR`, existence `hE`. -/
structure ResDat where
  σ : S → G
  hσ : ∀ s, σ s ∈ Γ ⊓ I s
  hσπ : ∀ s, π (σ s) = 1
  J : S → Subgroup G
  hJ : ∀ s g, g ∈ J s ↔ g ∈ Γ ⊓ I s ∧ π g = 1
  hloc : ∀ s, LocGen (J s) (I s) N ⟨σ s, (hJ s (σ s)).2 ⟨hσ s, hσπ s⟩⟩
  ΓH : Subgroup G
  hΓH : ∀ g, g ∈ ΓH ↔ g ∈ Γ ∧ π g = 1
  sh : T → S
  x : T → G
  hx : ∀ t, x t ∈ Γ
  y : T → ΓH
  hy : ∀ t, (y t : G) = x t * σ (sh t) * (x t)⁻¹
  hrep : ∀ s, ∀ p ∈ Γ.map π, ∃! t, sh t = s ∧ (π (x t))⁻¹ * p ∈ (Γ ⊓ I s).map π
  hR : ∀ χ : ΓH → ZMod N, IsLocallyConstant χ → (∀ a b, χ (a * b) = χ a + χ b) → ∑ t, χ (y t) = 0
  hE : ∀ c : T → ZMod N, ∑ t, c t = 0 → ∃ χ : ΓH → ZMod N, IsLocallyConstant χ ∧
    (∀ a b, χ (a * b) = χ a + χ b) ∧ ∀ t, χ (y t) = c t
  s0 : S

variable {π Γ I N T}

namespace ResDat

variable (D : ResDat π Γ I N T) {Λ : Type} [CommRing Λ] [Fintype (Γ.map π)]
  [∀ s, Fintype ((Γ ⊓ I s).map π)]

theorem hσJ (s : S) : D.σ s ∈ D.J s := (D.hJ s _).2 ⟨D.hσ s, D.hσπ s⟩

/-- `σ s` in `Γ`. -/
def sG (s : S) : Γ := ⟨D.σ s, (Subgroup.mem_inf.1 (D.hσ s)).1⟩

variable (Λ) in
/-- `N_s = Σ_{t over s} π(x_t)`. -/
def Ns (s : S) : MonoidAlgebra Λ Gf :=
  ∑ t ∈ Finset.univ.filter (fun t => D.sh t = s), single (π (D.x t)) (1 : Λ)

theorem hNs (s : S) : D.Ns Λ s * nrmS Λ ((Γ ⊓ I s).map π) = nrmS Λ (Γ.map π) := by
  ext z
  rw [coeff_nrmS (Γ.map π) z, Ns, Finset.sum_mul, coeff_sum, Finsupp.finsetSum_apply]
  simp only [coeff_single_mul_apply, one_mul, coeff_nrmS]
  by_cases hz : z ∈ Γ.map π
  · obtain ⟨t0, ht0, hu⟩ := D.hrep s z hz
    rw [if_pos hz, Finset.sum_eq_single t0
      (fun t ht htne => if_neg fun h => htne (hu t ⟨(Finset.mem_filter.1 ht).2, h⟩))
      (fun h => (h (Finset.mem_filter.2 ⟨Finset.mem_univ _, ht0.1⟩)).elim), if_pos ht0.2]
  · rw [if_neg hz]
    exact Finset.sum_eq_zero fun t _ => if_neg fun h => hz (by
      have := (Γ.map π).mul_mem (Subgroup.mem_map_of_mem π (D.hx t)) (Subgroup.map_mono inf_le_left h)
      rwa [mul_inv_cancel_left] at this)

theorem conj_x (c : Z1 (regRep Λ π) Γ) (t : T) :
    single (π (D.x t)) (1 : Λ) * (c : Γ → MonoidAlgebra Λ Gf) (D.sG (D.sh t)) =
      resK π Γ D.ΓH D.hΓH c (D.y t) :=
  calc single (π (D.x t)) (1 : Λ) * (c : Γ → MonoidAlgebra Λ Gf) (D.sG (D.sh t))
      = (c : Γ → MonoidAlgebra Λ Gf) (⟨D.x t, D.hx t⟩ * D.sG (D.sh t) * ⟨D.x t, D.hx t⟩⁻¹) :=
        (cocycle_conj π c ⟨D.x t, D.hx t⟩ (D.sG (D.sh t)) (D.hσπ _)).symm
    _ = resK π Γ D.ΓH D.hΓH c (D.y t) :=
        congrArg (c : Γ → MonoidAlgebra Λ Gf) (Subtype.ext (D.hy t).symm)

/-- (GR) from the residue theorem `hR`. -/
theorem GR [NeZero N] (hN : (N : Λ) = 0) (c : Z1 (regRep Λ π) Γ) :
    ∑ s, D.Ns Λ s * (c : Γ → MonoidAlgebra Λ Gf) (D.sG s) = 0 := by
  have e1 : ∀ s, D.Ns Λ s * (c : Γ → MonoidAlgebra Λ Gf) (D.sG s) =
      ∑ t ∈ Finset.univ.filter (fun t => D.sh t = s), resK π Γ D.ΓH D.hΓH c (D.y t) := fun s => by
    rw [Ns, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [← (Finset.mem_filter.1 ht).2]
    exact D.conj_x c t
  rw [Finset.sum_congr rfl fun s _ => e1 s, Finset.sum_fiberwise]
  exact sum_eq_zero_of_zmod D.y D.hR (nsmul_alg hN) _ (resK_lc π Γ D.ΓH D.hΓH c) (resK_add π Γ D.ΓH D.hΓH c)

theorem cmem (t : T) (s : S) (j : G) (hj : j ∈ D.J s) : D.x t * j * (D.x t)⁻¹ ∈ D.ΓH := by
  obtain ⟨hjΔ, hjπ⟩ := (D.hJ s j).1 hj
  exact (D.hΓH _).2 ⟨Γ.mul_mem (Γ.mul_mem (D.hx t) (Subgroup.mem_inf.1 hjΔ).1) (Γ.inv_mem (D.hx t)), by
    rw [map_mul, map_mul, map_inv, hjπ, mul_one, mul_inv_cancel]⟩

/-- `j ↦ χ(x_t j x_t⁻¹)` on `J s`. -/
def cfun {M : Type*} (χ : D.ΓH → M) (t : T) (s : S) (j : D.J s) : M :=
  χ ⟨D.x t * j * (D.x t)⁻¹, D.cmem t s j j.2⟩

theorem cfun_lc {M : Type*} (χ : D.ΓH → M) (hχc : IsLocallyConstant χ) (t : T) (s : S) :
    IsLocallyConstant (D.cfun χ t s) :=
  hχc.comp_continuous (((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _)

theorem cfun_add {M : Type*} [AddCommGroup M] (χ : D.ΓH → M) (hχ : ∀ a b, χ (a * b) = χ a + χ b) (t : T)
    (s : S) (a b : D.J s) : D.cfun χ t s (a * b) = D.cfun χ t s a + D.cfun χ t s b := by
  simp only [cfun]
  rw [← hχ]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  group

/-- KEY conjugation lemma: `χ(g⁻¹ σ_s g) = χ(y_t)` when `t` is the cover point over `s` of the coset of `π g⁻¹`. -/
theorem conj_eq [NeZero N] {M : Type*} [AddCommGroup M] (hM : ∀ m : M, N • m = 0) (χ : D.ΓH → M)
    (hχc : IsLocallyConstant χ) (hχ : ∀ a b, χ (a * b) = χ a + χ b) (g : G) (hg : g ∈ Γ) (s : S) (t : T)
    (hts : D.sh t = s) (hgt : (π (D.x t))⁻¹ * (π g)⁻¹ ∈ (Γ ⊓ I s).map π) (hgs : g⁻¹ * D.σ s * g ∈ D.ΓH) :
    χ ⟨g⁻¹ * D.σ s * g, hgs⟩ = χ (D.y t) := by
  subst hts
  obtain ⟨δ, hδ, hδπ⟩ := Subgroup.mem_map.1 hgt
  have hxt := D.hx t
  have hδΓ : δ ∈ Γ := (Subgroup.mem_inf.1 hδ).1
  have hh : g⁻¹ * δ⁻¹ * (D.x t)⁻¹ ∈ D.ΓH := (D.hΓH _).2 ⟨Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hg) (Γ.inv_mem hδΓ))
    (Γ.inv_mem hxt), by simp only [map_mul, map_inv, hδπ]; group⟩
  have hjδ : δ * D.σ (D.sh t) * δ⁻¹ ∈ D.J (D.sh t) := (D.hJ _ _).2 ⟨(Γ ⊓ I (D.sh t)).mul_mem
    ((Γ ⊓ I (D.sh t)).mul_mem hδ (D.hσ _)) ((Γ ⊓ I (D.sh t)).inv_mem hδ), by
    rw [map_mul, map_mul, map_inv, D.hσπ, mul_one, mul_inv_cancel]⟩
  have key := (D.hloc (D.sh t)).conj hM (D.cfun χ t (D.sh t)) (D.cfun_lc χ hχc t _) (D.cfun_add χ hχ t _) δ
    (Subgroup.mem_inf.1 hδ).2 hjδ
  have e1 : g⁻¹ * D.σ (D.sh t) * g = (g⁻¹ * δ⁻¹ * (D.x t)⁻¹) * (D.x t * (δ * D.σ (D.sh t) * δ⁻¹) * (D.x t)⁻¹) *
      (g⁻¹ * δ⁻¹ * (D.x t)⁻¹)⁻¹ := by group
  calc χ ⟨g⁻¹ * D.σ (D.sh t) * g, hgs⟩
      = χ (⟨_, hh⟩ * ⟨_, D.cmem t _ _ hjδ⟩ * (⟨_, hh⟩ : D.ΓH)⁻¹) := congrArg χ (Subtype.ext e1)
    _ = D.cfun χ t (D.sh t) ⟨δ * D.σ (D.sh t) * δ⁻¹, hjδ⟩ := hom_conj χ hχ _ _
    _ = D.cfun χ t (D.sh t) ⟨D.σ (D.sh t), D.hσJ _⟩ := key
    _ = χ (D.y t) := congrArg χ (Subtype.ext (D.hy t).symm)

/-- The cover point over `s` of the coset of `q`. -/
def tOf (s : S) (q : Γ.map π) : T := (D.hrep s q q.2).exists.choose

theorem tOf_spec (s : S) (q : Γ.map π) :
    D.sh (D.tOf s q) = s ∧ (π (D.x (D.tOf s q)))⁻¹ * (q : Gf) ∈ (Γ ⊓ I s).map π :=
  (D.hrep s q q.2).exists.choose_spec

theorem tOf_unique (s : S) (q : Γ.map π) (t : T) (ht : D.sh t = s)
    (htq : (π (D.x t))⁻¹ * (q : Gf) ∈ (Γ ⊓ I s).map π) : D.tOf s q = t :=
  (D.hrep s q q.2).unique (D.tOf_spec s q) ⟨ht, htq⟩

theorem tOf_eq_iff (s' s : S) (p q : Γ.map π) :
    D.tOf s' p = D.tOf s q ↔ s' = s ∧ (q : Gf)⁻¹ * p ∈ (Γ ⊓ I s).map π := by
  constructor
  · intro h
    have h1 := D.tOf_spec s' p
    have h2 := D.tOf_spec s q
    rw [h] at h1
    have hs : s' = s := h1.1.symm.trans h2.1
    refine ⟨hs, ?_⟩
    rw [hs] at h1
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ h2.2) h1.2
    rwa [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] at this
  · rintro ⟨rfl, h⟩
    refine D.tOf_unique s' p _ (D.tOf_spec s' q).1 ?_
    have := Subgroup.mul_mem _ (D.tOf_spec s' q).2 h
    rwa [mul_assoc, mul_inv_cancel_left] at this

theorem tOf_inv_eq_iff (s' s : S) (p q : Γ.map π) :
    D.tOf s' p⁻¹ = D.tOf s q ↔ s' = s ∧ (p : Gf) * q ∈ (Γ ⊓ I s).map π := by
  rw [D.tOf_eq_iff]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · have h' : (q : Gf)⁻¹ * (p : Gf)⁻¹ ∈ (Γ ⊓ I s).map π := h
    have := Subgroup.inv_mem _ h'
    rwa [mul_inv_rev, inv_inv, inv_inv] at this
  · show (q : Gf)⁻¹ * (p : Gf)⁻¹ ∈ (Γ ⊓ I s).map π
    have := Subgroup.inv_mem _ h
    rwa [mul_inv_rev] at this

variable [DecidableEq T]

theorem sum_glob (s' s : S) (q : Γ.map π) :
    ∑ p : Γ.map π, single (p : Gf) (if D.tOf s' p⁻¹ = D.tOf s q then (1 : Λ) else 0) =
      if s' = s then nrmS Λ ((Γ ⊓ I s).map π) * single (q : Gf)⁻¹ 1 else 0 := by
  split_ifs with hs
  · rw [← sum_single_ind (Γ.map π) ((Γ ⊓ I s).map π) (Subgroup.map_mono inf_le_left) q q.2]
    refine Finset.sum_congr rfl fun p _ => ?_
    congr 1
    classical
    exact if_congr ((D.tOf_inv_eq_iff s' s p q).trans (and_iff_right hs)) rfl rfl
  · exact Finset.sum_eq_zero fun (p : Γ.map π) _ => by
      rw [if_neg fun h => hs ((D.tOf_inv_eq_iff s' s p q).1 h).1, single_zero]

/-- The global induction cocycle of a `χ` with prescribed values `c` on the `y t`. -/
theorem exists_glob [NeZero N] (hN : (N : Λ) = 0) (hπ : IsOpen (π.ker : Set G)) (c : T → ZMod N)
    (hc : ∑ t, c t = 0) : ∃ e : Z1 (regRep Λ π) Γ, ∀ s', (e : Γ → MonoidAlgebra Λ Gf) (D.sG s') =
      ∑ p : Γ.map π, single (p : Gf) (zlift Λ N hN (c (D.tOf s' p⁻¹))) := by
  obtain ⟨χ, hχc, hχ, hχy⟩ := D.hE c hc
  have hMz : ∀ m : ZMod N, N • m = 0 := fun m => by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  refine ⟨indCoc π Γ D.ΓH D.hΓH hπ (fun k => zlift Λ N hN (χ k)) (hχc.comp fun z => zlift Λ N hN z)
    (fun a b => by simp only [hχ, map_add]), fun s' => ?_⟩
  rw [indCoc_apply]
  unfold indFun
  refine Finset.sum_congr rfl fun p _ => ?_
  have hw : π ((D.sG s' : Γ) : G) = 1 := D.hσπ s'
  have hc' := indK_coe_of_ker π Γ D.ΓH D.hΓH p (D.sG s') hw
  have hgs : (secOf π Γ p)⁻¹ * D.σ s' * secOf π Γ p ∈ D.ΓH :=
    (congrArg (· ∈ D.ΓH) hc').mp (indK π Γ D.ΓH D.hΓH p (D.sG s')).2
  have hgt : (π (D.x (D.tOf s' p⁻¹)))⁻¹ * (π (secOf π Γ p))⁻¹ ∈ (Γ ⊓ I s').map π := by
    rw [secOf_map π Γ p.2]
    exact (D.tOf_spec s' p⁻¹).2
  have e : indK π Γ D.ΓH D.hΓH p (D.sG s') = ⟨_, hgs⟩ := Subtype.ext hc'
  have key : χ (indK π Γ D.ΓH D.hΓH p (D.sG s')) = c (D.tOf s' p⁻¹) :=
    ((congrArg χ e).trans
      (D.conj_eq hMz χ hχc hχ _ (secOf_mem π Γ p) s' _ (D.tOf_spec s' p⁻¹).1 hgt hgs)).trans (hχy _)
  show single (p : Gf) (zlift Λ N hN (χ (indK π Γ D.ΓH D.hΓH p (D.sG s')))) = _
  rw [key]

/-- (GE1) from `hE`. -/
theorem GE1 [NeZero N] (hN : (N : Λ) = 0) (hπ : IsOpen (π.ker : Set G)) (s : S) :
    ∃ c : Z1 (regRep Λ π) Γ, ∀ s', (c : Γ → MonoidAlgebra Λ Gf) (D.sG s') =
      (if s' = s then nrmS Λ ((Γ ⊓ I s).map π) else 0) -
        (if s' = D.s0 then nrmS Λ ((Γ ⊓ I D.s0).map π) else 0) := by
  obtain ⟨e, he⟩ := D.exists_glob hN hπ
    (fun t => (if t = D.tOf s 1 then 1 else 0) - (if t = D.tOf D.s0 1 then 1 else 0))
    (by simp [Finset.sum_sub_distrib])
  refine ⟨e, fun s' => (he s').trans ?_⟩
  have h1 : single (((1 : Γ.map π) : Gf))⁻¹ (1 : Λ) = 1 := by
    show single (1 : Gf)⁻¹ (1 : Λ) = 1
    rw [inv_one, one_def]
  simp only [map_sub, zlift_ite, single_sub, Finset.sum_sub_distrib, D.sum_glob, h1, mul_one]

/-- (GE2) from `hE`. -/
theorem GE2 [NeZero N] (hN : (N : Λ) = 0) (hπ : IsOpen (π.ker : Set G)) (γ : Γ) :
    ∃ c : Z1 (regRep Λ π) Γ, ∀ s', (c : Γ → MonoidAlgebra Λ Gf) (D.sG s') =
      if s' = D.s0 then nrmS Λ ((Γ ⊓ I D.s0).map π) * (single (π γ) 1 - 1) else 0 := by
  obtain ⟨e, he⟩ := D.exists_glob hN hπ
    (fun t => (if t = D.tOf D.s0 (gP π Γ γ)⁻¹ then 1 else 0) - (if t = D.tOf D.s0 1 then 1 else 0))
    (by simp [Finset.sum_sub_distrib])
  refine ⟨e, fun s' => (he s').trans ?_⟩
  have h1 : single (((1 : Γ.map π) : Gf))⁻¹ (1 : Λ) = 1 := by
    show single (1 : Gf)⁻¹ (1 : Λ) = 1
    rw [inv_one, one_def]
  have h2 : single ((((gP π Γ γ)⁻¹ : Γ.map π) : Gf))⁻¹ (1 : Λ) = single (π (γ : G)) 1 := by
    show single ((π (γ : G))⁻¹)⁻¹ (1 : Λ) = _
    rw [inv_inv]
  simp only [map_sub, zlift_ite, single_sub, Finset.sum_sub_distrib, D.sum_glob, h1, h2, mul_one]
  split_ifs
  · rw [mul_sub, mul_one]
  · rw [sub_zero]

/-- The `ResHyp` of the data. -/
def toResHyp [NeZero N] (hN : (N : Λ) = 0) (hπ : IsOpen (π.ker : Set G)) : ResHyp Λ π Γ I where
  σ := D.σ
  hσ := D.hσ
  hσπ := D.hσπ
  Ns := D.Ns Λ
  hNs := D.hNs
  s0 := D.s0
  Ldet s e h0 j hj := ldet_of_locGen π (D.hJ s) (D.hloc s) hN e h0 j hj
  Linv s e g := linv_of_locGen π (D.hJ s) inf_le_right (D.hloc s) hN e g
  Lex s := lex_of_locGen π (D.hJ s) inf_le_right (D.hloc s) hN hπ
  GR := D.GR hN
  GE1 := D.GE1 hN hπ
  GE2 := D.GE2 hN hπ

theorem toResHyp_σ [NeZero N] (hN : (N : Λ) = 0) (hπ : IsOpen (π.ker : Set G)) :
    (D.toResHyp hN hπ).σ = D.σ := rfl

end ResDat

end Dat

end

end PerfectCx
end RamanujanPetersson


end

-- ===== S4.Def_RP_Cone_ResAsm =====
section

/-!
# S4-PD E4S arithmetic ResA, part 4: cover points and inertia in the S3 chart

S3 setting (`F / 𝔽_q`, chart `(Rfin, F, Rinf)`), boundary primes `P s` (one per `π₁^geo`-orbit), a finite level
`M ≤ K_U` with `π : π₁ → Gf` (`Gf` finite, `ker π = Gal(K_U/M)`), and `N` prime to `p`.

* `conj_mem_inertia_smul`: `x I(Q) x⁻¹ ⊆ I(x • Q)`; `Inert Q := I(Q)`, `Jt π Q := I(Q) ∩ ker π`.
* `cosQA`, `cosB`, `cosQA_base`: the cover points `x_t • P (sh t)` and the base points (trivial cosets), with the
  cover / disjointness / inertia facts proved for a general chart `(A, K, R0)` (elaboration note: statements in the
  concrete S3 chart never mention `Ideal.inertia` or a generic `[MulAction]` term directly; they go through these
  chart-generic abbreviations, which instantiate cheaply).
* `exists_norm_tau_fin` (level data discharged) is in `Def_RP_Cone_ResAsmFin`.
* The assembly `exists_resDat` is in `Def_RP_Cone_ResAsm2`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace RamanujanPetersson
namespace Residue

noncomputable section

open CurveCoh GalCover Kummer CP4a TameInertia IsDedekindDomain Polynomial
open scoped Pointwise

section Conj

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {R0 : Type} [CommRing R0] [Algebra R0 K]

/-- Inertia is conjugation-equivariant: `x I(Q) x⁻¹ ⊆ I(x • Q)`. -/
theorem conj_mem_inertia_smul {Q : Ideal (proChart A K R0)} (x : Pi1 A K) {σ : Pi1 A K}
    (hσ : σ ∈ Q.inertia (Pi1 A K)) : x * σ * x⁻¹ ∈ (x • Q).inertia (Pi1 A K) := by
  refine AddSubgroup.mem_inertia.2 fun b => ?_
  have h := AddSubgroup.mem_inertia.1 hσ (x⁻¹ • b)
  have e : (x * σ * x⁻¹) • b - b = x • (σ • x⁻¹ • b - x⁻¹ • b) := by
    rw [smul_sub, mul_smul, mul_smul, smul_inv_smul]
  rw [e]
  exact Ideal.smul_mem_pointwise_smul x _ Q h

/-- The inertia group of `Q` (chart-generic, so that concrete charts can state it cheaply). -/
abbrev Inert (Q : Ideal (proChart A K R0)) : Subgroup (Pi1 A K) := Q.inertia (Pi1 A K)

/-- The part `I(Q) ∩ ker π` of the inertia of `Q`. -/
abbrev Jt {Gf : Type} [Group Gf] (π : Pi1 A K →* Gf) (Q : Ideal (proChart A K R0)) : Subgroup (Pi1 A K) :=
  Q.inertia (Pi1 A K) ⊓ π.ker

theorem stabI_gen (Q : Ideal (proChart A K R0)) (δ : Pi1 A K) (h : δ ∈ Inert Q) : δ • Q = Q :=
  MulAction.mem_stabilizer_iff.1 (Ideal.inertia_le_stabilizer Q h)

end Conj

section Gen

variable {G Gf : Type} [Group G] [Group Gf] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)

end Gen

section CosA

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {R0 : Type} [CommRing R0] [Algebra R0 K]
  {Gf : Type} [Group Gf] (π : Pi1 A K →* Gf) (Γ : Subgroup (Pi1 A K)) {S : Type} (I : S → Subgroup (Pi1 A K))
  (P : S → Ideal (proChart A K R0))

end CosA

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

end S3

end

end Residue
end RamanujanPetersson


end


