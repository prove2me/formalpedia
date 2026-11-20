-- Prove2me | Definitions.Def_RPLib_F2_016
-- name    : RPLib_F2_016
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T09:36:32.002179+00:00
-- url     : https://prove2.me/theorems/4046fce3-d374-4a4d-8082-7c9128b97cfa
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 016 of 70
-- statement:
--   File 016 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacFrob_BrO`: S4-JacFrob, part BrO (bridge 3): `F-bar / F_{lev j}` is unramified
--   * `S4.Def_RP_JacFrob_BrD`: S4-JacFrob, part BrD (bridge 4): degree-1 places, separation, fibre count
--   * `S4.Def_RP_JacFrob_BrPsi`: S4-JacFrob, part BrPsi (bridge 5): `Pic(X-bar) ≃ Pic(F-bar / k-bar)`
--   * `S4.Def_RP_CoreB_Triv`: Core B, O2: the genus 0 case
--   * `S4.Def_RP_DegPoly`: Degree polynomiality (unit S4-DegPoly, lemma L37 of `S4_COREB_ROUTE.md`)
--   * `S4.Def_RP_DegPoly_Data`: Degree polynomiality, part 2: (D2) in `DegreeData` form (unit S4-DegPoly, L37)
--   * `S4.Def_RP_JacDivisors_H`: S4-JacDivisors H (O11: Weil divisors on integral locally Noetherian schemes)
--   * `S4.Def_RP_JacDivisors_I`: S4-JacDivisors I (O12 bridges: orders of sections at codimension-one points, affine charts)
--   * `S4.Def_RP_JacDivisors_J`: S4-JacDivisors J (O12b: algebraic Hartogs at points with factorial stalks)
--   * `S4.Def_RP_JacDivisors_K`: S4-JacDivisors K (O12a: Weil divisors are locally principal at factorial points)
--   * `S4.Def_RP_IsogDegA_FF`: S4-IsogDegA, file FF: the function-field map of a dominant morphism and the degree (O2, O5)
--   * `S4.Def_RP_JacDivisors_L`: S4-JacDivisors L (O13: pull-back of Weil divisors along dominant morphisms)
--   * `S4.Def_RP_JacDivisors_M`: S4-JacDivisors M (O14, step E1: rational maps into proper targets are defined in codimension one)
--   * `S4.Def_RP_JacDivisors_O`: S4-JacDivisors O (O14, steps E1' and E4-E5: where a rational map is undefined, a codimension-one divisor is)
--   * `S4.Def_RP_ThetaSquare_CPull`: S4-ThetaSquare, file CPull: pulling Weil divisors back along non-dominant morphisms (T4a)
--   * `S4.Def_RP_ThetaCube_Det`: S4-ThetaCube, file Det (D-B2, part 1): determinants of pulled-back rational functions
--   * `S4.Def_RP_ThetaCube_SmDed`: S4-ThetaCube, file SmDed (D-B0, part 1): a Dedekind domain of finite type over an algebraically closed field is smooth
--   * `S4.Def_RP_IntersectA_Top`: S4-IntersectA, file Top: general position by a dimension count (topology only)
--   * `S4.Def_RP_IsogDegA_Trans`: S4-IsogDegA, file Trans: translations by `k`-points of a group scheme over `k`
--   * `S4.Def_RP_IntersectA_Gen`: S4-IntersectA, file Gen: translates in general position (L31 existence)
--   * `S4.Def_RP_IntersectA_Fam`: S4-IntersectA, file Fam: the family of translated intersections over `A^g`
--   * `S4.Def_RP_IntersectA_GI`: S4-IntersectA, file GI: integral varieties over an algebraically closed field are geometrically integral
--   * `S4.Def_RP_IntersectA_Prod`: S4-IntersectA, file Prod: products of integral varieties over an algebraically closed field
--   * `S4.Def_RP_IntersectA_PwInst`: S4-IntersectA, file PwInst: the parameter space `A^n` and the family over it
--   * `S4.Def_RP_IntersectA_Cons`: S4-IntersectA, file Cons: generic flatness of a finite morphism
--   * `S4.Def_RP_IntersectA`: S4-IntersectA: intersection numbers at generic translates (L31-L32)
--   * `S4.Def_RP_IntersectB_Sym`: S4-IntersectB, file Sym: symmetry and translation invariance of `inum` (L33, part 1)
--   * `S4.Def_RP_IntersectB_Aff`: S4-IntersectB, file Aff: affine charts for finite subschemes (L33, part 2)
--   * `S4.Def_RP_IntersectB_Alg`: S4-IntersectB, file Alg: the exact-sequence lemma behind additivity (L33, part 3)
--   * `S4.Def_RP_IntersectB_Gen`: S4-IntersectB, file Gen: the generator `u`, the multiplier `s`, the weak NZD criterion (L33, part 3b)
--   * `S4.Def_RP_IntersectB_Ass`: S4-IntersectB, file Ass: associated points of an ideal sheaf (L33, part 4)
--   * `S4.Def_RP_IntersectB_Add_Ring`: S4-IntersectB, file Add_Ring: the chart step of additivity (L33, B3 core)
--   * `S4.Def_RP_IntersectB_Add`: S4-IntersectB, file Add: additivity of `inum` in the first slot (L33, B3)
--   * `S4.Def_RP_JacDivisors_N`: S4-JacDivisors N (O14, steps E6-E7: a prime divisor through `Δ x` meets any morphism in codimension one)
--   * `S4.Def_RP_JacDivisors_P`: S4-JacDivisors P (O14, steps E2 and E8: the difference map `Φ(v, w) = φ(v) φ(w)⁻¹` is defined on the diagonal)
--   * `S4.Def_RP_JacDivisors_Q`: S4-JacDivisors Q (O14, steps E9-E10: Weil's extension theorem, Milne I.3.1-3.2)
--   * `S4.Def_RP_JacDivisors_R`: S4-JacDivisors R (O10, algebra part): étale over a regular ring is regular
--   * `S4.Def_RP_JacDivisors_A`: S4-JacDivisors A (O1): first facts on regular local rings
--   * `S4.Def_RP_JacDivisors_B`: S4-JacDivisors B (O3b, O5): change of rings and Serre's easy direction
--   * `S4.Def_RP_JacDivisors_C`: S4-JacDivisors C (O2 and helpers for Serre's hard direction)
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_015

/-!
# Ramanujan-Petersson curve library (flat edition), file 016 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacFrob_BrO`: S4-JacFrob, part BrO (bridge 3): `F-bar / F_{lev j}` is unramified
* `S4.Def_RP_JacFrob_BrD`: S4-JacFrob, part BrD (bridge 4): degree-1 places, separation, fibre count
* `S4.Def_RP_JacFrob_BrPsi`: S4-JacFrob, part BrPsi (bridge 5): `Pic(X-bar) ≃ Pic(F-bar / k-bar)`
* `S4.Def_RP_CoreB_Triv`: Core B, O2: the genus 0 case
* `S4.Def_RP_DegPoly`: Degree polynomiality (unit S4-DegPoly, lemma L37 of `S4_COREB_ROUTE.md`)
* `S4.Def_RP_DegPoly_Data`: Degree polynomiality, part 2: (D2) in `DegreeData` form (unit S4-DegPoly, L37)
* `S4.Def_RP_JacDivisors_H`: S4-JacDivisors H (O11: Weil divisors on integral locally Noetherian schemes)
* `S4.Def_RP_JacDivisors_I`: S4-JacDivisors I (O12 bridges: orders of sections at codimension-one points, affine charts)
* `S4.Def_RP_JacDivisors_J`: S4-JacDivisors J (O12b: algebraic Hartogs at points with factorial stalks)
* `S4.Def_RP_JacDivisors_K`: S4-JacDivisors K (O12a: Weil divisors are locally principal at factorial points)
* `S4.Def_RP_IsogDegA_FF`: S4-IsogDegA, file FF: the function-field map of a dominant morphism and the degree (O2, O5)
* `S4.Def_RP_JacDivisors_L`: S4-JacDivisors L (O13: pull-back of Weil divisors along dominant morphisms)
* `S4.Def_RP_JacDivisors_M`: S4-JacDivisors M (O14, step E1: rational maps into proper targets are defined in codimension one)
* `S4.Def_RP_JacDivisors_O`: S4-JacDivisors O (O14, steps E1' and E4-E5: where a rational map is undefined, a codimension-one divisor is)
* `S4.Def_RP_ThetaSquare_CPull`: S4-ThetaSquare, file CPull: pulling Weil divisors back along non-dominant morphisms (T4a)
* `S4.Def_RP_ThetaCube_Det`: S4-ThetaCube, file Det (D-B2, part 1): determinants of pulled-back rational functions
* `S4.Def_RP_ThetaCube_SmDed`: S4-ThetaCube, file SmDed (D-B0, part 1): a Dedekind domain of finite type over an algebraically closed field is smooth
* `S4.Def_RP_IntersectA_Top`: S4-IntersectA, file Top: general position by a dimension count (topology only)
* `S4.Def_RP_IsogDegA_Trans`: S4-IsogDegA, file Trans: translations by `k`-points of a group scheme over `k`
* `S4.Def_RP_IntersectA_Gen`: S4-IntersectA, file Gen: translates in general position (L31 existence)
* `S4.Def_RP_IntersectA_Fam`: S4-IntersectA, file Fam: the family of translated intersections over `A^g`
* `S4.Def_RP_IntersectA_GI`: S4-IntersectA, file GI: integral varieties over an algebraically closed field are geometrically integral
* `S4.Def_RP_IntersectA_Prod`: S4-IntersectA, file Prod: products of integral varieties over an algebraically closed field
* `S4.Def_RP_IntersectA_PwInst`: S4-IntersectA, file PwInst: the parameter space `A^n` and the family over it
* `S4.Def_RP_IntersectA_Cons`: S4-IntersectA, file Cons: generic flatness of a finite morphism
* `S4.Def_RP_IntersectA`: S4-IntersectA: intersection numbers at generic translates (L31-L32)
* `S4.Def_RP_IntersectB_Sym`: S4-IntersectB, file Sym: symmetry and translation invariance of `inum` (L33, part 1)
* `S4.Def_RP_IntersectB_Aff`: S4-IntersectB, file Aff: affine charts for finite subschemes (L33, part 2)
* `S4.Def_RP_IntersectB_Alg`: S4-IntersectB, file Alg: the exact-sequence lemma behind additivity (L33, part 3)
* `S4.Def_RP_IntersectB_Gen`: S4-IntersectB, file Gen: the generator `u`, the multiplier `s`, the weak NZD criterion (L33, part 3b)
* `S4.Def_RP_IntersectB_Ass`: S4-IntersectB, file Ass: associated points of an ideal sheaf (L33, part 4)
* `S4.Def_RP_IntersectB_Add_Ring`: S4-IntersectB, file Add_Ring: the chart step of additivity (L33, B3 core)
* `S4.Def_RP_IntersectB_Add`: S4-IntersectB, file Add: additivity of `inum` in the first slot (L33, B3)
* `S4.Def_RP_JacDivisors_N`: S4-JacDivisors N (O14, steps E6-E7: a prime divisor through `Δ x` meets any morphism in codimension one)
* `S4.Def_RP_JacDivisors_P`: S4-JacDivisors P (O14, steps E2 and E8: the difference map `Φ(v, w) = φ(v) φ(w)⁻¹` is defined on the diagonal)
* `S4.Def_RP_JacDivisors_Q`: S4-JacDivisors Q (O14, steps E9-E10: Weil's extension theorem, Milne I.3.1-3.2)
* `S4.Def_RP_JacDivisors_R`: S4-JacDivisors R (O10, algebra part): étale over a regular ring is regular
* `S4.Def_RP_JacDivisors_A`: S4-JacDivisors A (O1): first facts on regular local rings
* `S4.Def_RP_JacDivisors_B`: S4-JacDivisors B (O3b, O5): change of rings and Serre's easy direction
* `S4.Def_RP_JacDivisors_C`: S4-JacDivisors C (O2 and helpers for Serre's hard direction)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacFrob_BrO =====
section

/-!
# S4-JacFrob, part BrO (bridge 3): `F-bar / F_{lev j}` is unramified

* generic: `ord_liesOver_mul` (`ord_w (x) = e(w | v) · ord_v x` for `w` over `v`, from Mathlib `valuation_liesOver`);
* `ord_contFinB_mul`, `ord_contInfB_mul` (the same for the contraction to a level);
* `placeOrd_inl_bar/inr_bar` (`Place.ord` on `F-bar`, which has no `Fintype` constants);
* **`ord_contFinB`, `ord_contInfB`, `ord_contB`**: `ord_{contB j P} f = ord_P f` for `f ∈ F_{lev j}` (a uniformizer of
  `P` lies in some level `M`, forcing `e = 1` there, and the levels are unramified over each other).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.JacFrob

open Polynomial IsDedekindDomain RamanujanPetersson.PicDescent Places

section GenOrd

variable {A K : Type*} (L : Type*) {B : Type*}
variable [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Module.IsTorsionFree A B]
variable [Field K] [Field L] [Algebra K L]
variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
variable [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]

end GenOrd

section Unram

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

include hk in
/-- **Unramified**: orders at the contraction agree with orders upstairs. -/
theorem ord_contFinB (j : ℕ) (w : HeightOneSpectrum (Rfin (kbar Fq Ω) (Fbar Fq F Ω))) (f : Fc Fq F Ω (lev j)) :
    Places.ord (contFinB Fq F Ω hk j w) f = Places.ord w (incF Fq F Ω j f) := by
  obtain ⟨t, ht⟩ := HeightOneSpectrum.valuation_exists_uniformizer (K := Fbar Fq F Ω) (v := w)
  obtain ⟨M0, hM0⟩ := exists_lev_of_mem_Fbar (t : Fbar Fq F Ω).2
  obtain ⟨M, hjM, hM0M⟩ : ∃ M, j ≤ M ∧ M0 ≤ M := ⟨max j M0, le_max_left _ _, le_max_right _ _⟩
  haveI : Fact (lev j ∣ lev M) := ⟨lev_dvd_lev hjM⟩
  let tM : Fc Fq F Ω (lev M) := ⟨(t : Ω), Fc_le (lev_dvd_lev hM0M) hM0⟩
  have htM : incF Fq F Ω M tM = t := Subtype.ext (coe_incF Fq F Ω M tM)
  have ht1 : Places.ord w t = 1 := by
    simp only [Places.ord, ht, WithZero.log_exp, neg_neg]
  have h1 := ord_contFinB_mul Fq F Ω hk M w tM
  rw [htM, ht1] at h1
  have he := Int.eq_one_of_mul_eq_one_right (Nat.cast_nonneg _) h1.symm
  have hf : incF Fq F Ω j f = incF Fq F Ω M (algebraMap (Fc Fq F Ω (lev j)) (Fc Fq F Ω (lev M)) f) :=
    Subtype.ext (by rw [coe_incF, coe_incF, coe_algebraMap_FF])
  rw [hf, ord_contFinB_mul Fq F Ω hk M w, he, one_mul]
  have h2 := ord_contractNN hk (n := lev j) (N := lev M) (contB Fq F Ω hk M (Sum.inl w)) f
  rw [contractNN_contB, contB_inl, contB_inl, Place.ord_inl, Place.ord_inl] at h2
  exact h2

theorem ord_contInfB_mul (j : ℕ) (w : HeightOneSpectrum (Rinf (kbar Fq Ω) (Fbar Fq F Ω))) (f : Fc Fq F Ω (lev j)) :
    letI := (infR Fq F Ω j).toAlgebra
    Places.ord w (incF Fq F Ω j f) =
      ((contInfB Fq F Ω hk j w).asIdeal.ramificationIdx' w.asIdeal : ℤ) * Places.ord (contInfB Fq F Ω hk j w) f := by
  letI := (infR Fq F Ω j).toAlgebra
  letI : Module (Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rinf (kbar Fq Ω) (Fbar Fq F Ω)) := Algebra.toModule
  haveI := isIntegral_infR Fq F Ω hk j
  haveI : Module.IsTorsionFree (Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rinf (kbar Fq Ω) (Fbar Fq F Ω)) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (by
      rw [RingHom.algebraMap_toAlgebra]; exact infR_injective Fq F Ω j)
  letI : Algebra (Fc Fq F Ω (lev j)) (Fbar Fq F Ω) := (incF Fq F Ω j).toAlgebra
  letI : Algebra (Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Fbar Fq F Ω) :=
    ((incF Fq F Ω j).comp (algebraMap (Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Fc Fq F Ω (lev j)))).toAlgebra
  letI : SMul (Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rinf (kbar Fq Ω) (Fbar Fq F Ω)) := Algebra.toSMul
  letI : SMul (Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Fbar Fq F Ω) := Algebra.toSMul
  letI : SMul (Fc Fq F Ω (lev j)) (Fbar Fq F Ω) := Algebra.toSMul
  letI : SMul (Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Fc Fq F Ω (lev j)) := Algebra.toSMul
  haveI : IsScalarTower (Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Fc Fq F Ω (lev j)) (Fbar Fq F Ω) :=
    IsScalarTower.of_algebraMap_eq' (by rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra])
  haveI : IsScalarTower (Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rinf (kbar Fq Ω) (Fbar Fq F Ω)) (Fbar Fq F Ω) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
      refine RingHom.ext fun a => ?_
      rw [RingHom.comp_apply, RingHom.comp_apply]
      exact (coe_infR Fq F Ω j a).symm)
  haveI : w.asIdeal.LiesOver (contInfB Fq F Ω hk j w).asIdeal :=
    ⟨by rw [asIdeal_contInfB, Ideal.under_def, RingHom.algebraMap_toAlgebra]⟩
  have h := ord_liesOver_mul (Fbar Fq F Ω) (contInfB Fq F Ω hk j w) w f
  rw [RingHom.algebraMap_toAlgebra] at h
  exact h

include hk in
/-- **Unramified**: orders at the contraction agree with orders upstairs. -/
theorem ord_contInfB (j : ℕ) (w : HeightOneSpectrum (Rinf (kbar Fq Ω) (Fbar Fq F Ω))) (f : Fc Fq F Ω (lev j)) :
    Places.ord (contInfB Fq F Ω hk j w) f = Places.ord w (incF Fq F Ω j f) := by
  obtain ⟨t, ht⟩ := HeightOneSpectrum.valuation_exists_uniformizer (K := Fbar Fq F Ω) (v := w)
  obtain ⟨M0, hM0⟩ := exists_lev_of_mem_Fbar (t : Fbar Fq F Ω).2
  obtain ⟨M, hjM, hM0M⟩ : ∃ M, j ≤ M ∧ M0 ≤ M := ⟨max j M0, le_max_left _ _, le_max_right _ _⟩
  haveI : Fact (lev j ∣ lev M) := ⟨lev_dvd_lev hjM⟩
  let tM : Fc Fq F Ω (lev M) := ⟨(t : Ω), Fc_le (lev_dvd_lev hM0M) hM0⟩
  have htM : incF Fq F Ω M tM = t := Subtype.ext (coe_incF Fq F Ω M tM)
  have ht1 : Places.ord w t = 1 := by
    simp only [Places.ord, ht, WithZero.log_exp, neg_neg]
  have h1 := ord_contInfB_mul Fq F Ω hk M w tM
  rw [htM, ht1] at h1
  have he := Int.eq_one_of_mul_eq_one_right (Nat.cast_nonneg _) h1.symm
  have hf : incF Fq F Ω j f = incF Fq F Ω M (algebraMap (Fc Fq F Ω (lev j)) (Fc Fq F Ω (lev M)) f) :=
    Subtype.ext (by rw [coe_incF, coe_incF, coe_algebraMap_FF])
  rw [hf, ord_contInfB_mul Fq F Ω hk M w, he, one_mul]
  have h2 := ord_contractNN hk (n := lev j) (N := lev M) (contB Fq F Ω hk M (Sum.inr w)) f
  rw [contractNN_contB, contB_inr, contB_inr, Place.ord_inr, Place.ord_inr] at h2
  exact h2

end Unram

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_BrD =====
section

/-!
# S4-JacFrob, part BrD (bridge 4): degree-1 places, separation, fibre count

* generic: `deg_eq_one_of_const` (a place all of whose residues are constants has degree `1`),
  `exists_const_of_isAlgClosed` (over an algebraically closed field every residue is a constant);
* generic (constant field extensions): `exists_sum_fin/inf` (`A' = Σ L · A`), `const_of_base_fin/inf`;
* `degOne`: every place of `F-bar` contracts to a degree-1 place at all large levels;
* `sepB`, `contB_ne_mono`: places of `F-bar` are separated by their contractions;
* `uniqB`, `fibreB`, `exists_fibreB_singleton`: over a degree-1 level place there is exactly one place of `F-bar`;
* **`card_fibreB`**: `#{P | contB j P = Q} = deg Q`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.JacFrob

open Polynomial IsDedekindDomain RamanujanPetersson.PicDescent Places

section GenDeg

variable {L : Type*} [Field L] {A : Type*} [CommRing A] [IsDedekindDomain A] [Algebra L A]

/-- A place all of whose residues are constants has degree `1`. -/
theorem deg_eq_one_of_const (P : HeightOneSpectrum A)
    (h : ∀ y : A, ∃ l : L, y - algebraMap L A l ∈ P.asIdeal) : Places.deg L P = 1 := by
  haveI := P.isPrime
  have hs : Function.Surjective (algebraMap L (A ⧸ P.asIdeal)) := by
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨l, hl⟩ := h y
    refine ⟨l, ?_⟩
    rw [IsScalarTower.algebraMap_apply L A (A ⧸ P.asIdeal), Ideal.Quotient.algebraMap_eq, eq_comm, ← sub_eq_zero, ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hl
  have hb : Function.Bijective (Algebra.linearMap L (A ⧸ P.asIdeal)) :=
    ⟨(algebraMap L (A ⧸ P.asIdeal)).injective, hs⟩
  rw [Places.deg, ← (LinearEquiv.ofBijective _ hb).finrank_eq, Module.finrank_self]

/-- Over an algebraically closed field every residue is a constant. -/
theorem exists_const_of_isAlgClosed [IsAlgClosed L] [PlacesK.FDQ L A] (P : HeightOneSpectrum A) (y : A) :
    ∃ l : L, y - algebraMap L A l ∈ P.asIdeal := by
  haveI := PlacesK.moduleFinite_residue (K := L) P
  haveI := P.isPrime
  obtain ⟨l, hl⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := L) (K := A ⧸ P.asIdeal)).2
    (Ideal.Quotient.mk P.asIdeal y)
  refine ⟨l, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hl, IsScalarTower.algebraMap_apply L A (A ⧸ P.asIdeal),
    Ideal.Quotient.algebraMap_eq, sub_self]

end GenDeg

section Gen

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {L : Type*} [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable {F' : Type*} [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']
variable [Algebra F F'] [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
variable {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}
variable (h : RR.IsConstExt Fq F L F' c)

/-- `Rfin L F' = Σ_j L c_j · Rfin Fq F`. -/
theorem exists_sum_fin (y : Rfin L F') :
    letI := algFin h
    ∃ a : ι → Rfin Fq F, y = ∑ j, algebraMap L (Rfin L F') (c j) * algebraMap (Rfin Fq F) (Rfin L F') (a j) := by
  letI := algFin h
  have hy : (y : F') ∈ Submodule.span F (Set.range fun j => algebraMap L F' (c j)) := h.span Submodule.mem_top
  obtain ⟨f, hf⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hy
  have hmem : ∀ j, f j ∈ (algebraMap (Rfin Fq F) F).range := (h.fin f).1 (hf ▸ ⟨y, rfl⟩)
  choose a ha using hmem
  refine ⟨a, Subtype.ext ?_⟩
  rw [← hf, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MulMemClass.coe_mul, coe_algFin h (a j), Algebra.smul_def, ← ha j, mul_comm]
  try rfl

/-- `Rinf L F' = Σ_j L c_j · Rinf Fq F`. -/
theorem exists_sum_inf (y : Rinf L F') :
    letI := algInf h
    ∃ a : ι → Rinf Fq F, y = ∑ j, algebraMap L (Rinf L F') (c j) * algebraMap (Rinf Fq F) (Rinf L F') (a j) := by
  letI := algInf h
  have hy : (y : F') ∈ Submodule.span F (Set.range fun j => algebraMap L F' (c j)) := h.span Submodule.mem_top
  obtain ⟨f, hf⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hy
  have hmem : ∀ j, f j ∈ (algebraMap (Rinf Fq F) F).range := (h.inf f).1 (hf ▸ ⟨y, rfl⟩)
  choose a ha using hmem
  refine ⟨a, Subtype.ext ?_⟩
  rw [← hf, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MulMemClass.coe_mul, coe_algInf h (a j), Algebra.smul_def, ← ha j, mul_comm]
  try rfl

/-- If the base ring has constant residues mod `I`, so has `Rfin L F'`. -/
theorem const_of_base_fin (I : Ideal (Rfin L F')) :
    letI := algFin h
    (∀ a : Rfin Fq F, ∃ l : L, algebraMap (Rfin Fq F) (Rfin L F') a - algebraMap L (Rfin L F') l ∈ I) →
      ∀ y : Rfin L F', ∃ l : L, y - algebraMap L (Rfin L F') l ∈ I := by
  letI := algFin h
  intro hb y
  obtain ⟨a, hy⟩ := exists_sum_fin h y
  choose l hl using fun j => hb (a j)
  refine ⟨∑ j, c j * l j, ?_⟩
  rw [hy, map_sum, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [map_mul, ← mul_sub]
  exact I.mul_mem_left _ (hl j)

/-- If the base ring has constant residues mod `I`, so has `Rinf L F'`. -/
theorem const_of_base_inf (I : Ideal (Rinf L F')) :
    letI := algInf h
    (∀ a : Rinf Fq F, ∃ l : L, algebraMap (Rinf Fq F) (Rinf L F') a - algebraMap L (Rinf L F') l ∈ I) →
      ∀ y : Rinf L F', ∃ l : L, y - algebraMap L (Rinf L F') l ∈ I := by
  letI := algInf h
  intro hb y
  obtain ⟨a, hy⟩ := exists_sum_inf h y
  choose l hl using fun j => hb (a j)
  refine ⟨∑ j, c j * l j, ?_⟩
  rw [hy, map_sum, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [map_mul, ← mul_sub]
  exact I.mul_mem_left _ (hl j)

end Gen

section DegOne

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

theorem finR_algebraMap_L (j : ℕ) (l : Lc Fq Ω (lev j)) (c : kbar Fq Ω) (hlc : (l : Ω) = (c : Ω)) :
    finR Fq F Ω j (algebraMap (Lc Fq Ω (lev j)) (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) l) =
      algebraMap (kbar Fq Ω) (Rfin (kbar Fq Ω) (Fbar Fq F Ω)) c := by
  apply Subtype.ext
  rw [coe_finR]
  apply Subtype.ext
  rw [coe_incF]
  exact hlc

theorem infR_algebraMap_L (j : ℕ) (l : Lc Fq Ω (lev j)) (c : kbar Fq Ω) (hlc : (l : Ω) = (c : Ω)) :
    infR Fq F Ω j (algebraMap (Lc Fq Ω (lev j)) (Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) l) =
      algebraMap (kbar Fq Ω) (Rinf (kbar Fq Ω) (Fbar Fq F Ω)) c := by
  apply Subtype.ext
  rw [coe_infR]
  apply Subtype.ext
  rw [coe_incF]
  exact hlc

include hk in
/-- **Degree 1 at large levels** (finite places). -/
theorem degOne_fin (w : HeightOneSpectrum (Rfin (kbar Fq Ω) (Fbar Fq F Ω))) :
    ∃ M0, ∀ M, M0 ≤ M → Places.deg (Lc Fq Ω (lev M)) (contFinB Fq F Ω hk M w) = 1 := by
  classical
  haveI : Fintype (Rfin (Lc Fq Ω (lev 0)) (Fc Fq F Ω (lev 0)) ⧸ (contFinB Fq F Ω hk 0 w).asIdeal) :=
    Fintype.ofFinite _
  choose r hr using fun x : Rfin (Lc Fq Ω (lev 0)) (Fc Fq F Ω (lev 0)) ⧸ (contFinB Fq F Ω hk 0 w).asIdeal =>
    Ideal.Quotient.mk_surjective x
  choose cst hcst using fun x => exists_const_of_isAlgClosed (L := kbar Fq Ω) w (finR Fq F Ω 0 (r x))
  choose J hJ using fun x => exists_lev_of_mem_kbar (cst x).2
  refine ⟨Finset.univ.sup J, fun M hM => ?_⟩
  haveI : Fact (lev 0 ∣ lev M) := ⟨lev_dvd_lev (Nat.zero_le M)⟩
  letI := algFin (isConstExt_pair Fq F Ω hk (n := lev 0) (N := lev M))
  have hbase : ∀ a : Rfin (Lc Fq Ω (lev 0)) (Fc Fq F Ω (lev 0)), ∃ l : Lc Fq Ω (lev M),
      algebraMap _ (Rfin (Lc Fq Ω (lev M)) (Fc Fq F Ω (lev M))) a -
        algebraMap (Lc Fq Ω (lev M)) (Rfin (Lc Fq Ω (lev M)) (Fc Fq F Ω (lev M))) l ∈
          (contFinB Fq F Ω hk M w).asIdeal := by
    intro a
    let x := Ideal.Quotient.mk (contFinB Fq F Ω hk 0 w).asIdeal a
    have hxM : J x ≤ M := le_trans (Finset.le_sup (Finset.mem_univ x)) hM
    refine ⟨⟨(cst x : Ω), Lc_le (lev_dvd_lev hxM) (hJ x)⟩, ?_⟩
    rw [mem_contFinB Fq F Ω hk, RingHom.map_sub, finR_pair Fq F Ω hk, finR_algebraMap_L Fq F Ω M _ (cst x) rfl]
    have h1 : a - r x ∈ (contFinB Fq F Ω hk 0 w).asIdeal := by
      rw [← Ideal.Quotient.eq]; exact (hr x).symm
    rw [mem_contFinB Fq F Ω hk, RingHom.map_sub] at h1
    have h2 := w.asIdeal.add_mem h1 (hcst x)
    rwa [sub_add_sub_cancel] at h2
  exact deg_eq_one_of_const _ (const_of_base_fin (isConstExt_pair Fq F Ω hk (n := lev 0) (N := lev M)) _ hbase)

include hk in
/-- **Degree 1 at large levels** (places over `∞`). -/
theorem degOne_inf (w : HeightOneSpectrum (Rinf (kbar Fq Ω) (Fbar Fq F Ω))) :
    ∃ M0, ∀ M, M0 ≤ M → Places.deg (Lc Fq Ω (lev M)) (contInfB Fq F Ω hk M w) = 1 := by
  classical
  haveI : Fintype (Rinf (Lc Fq Ω (lev 0)) (Fc Fq F Ω (lev 0)) ⧸ (contInfB Fq F Ω hk 0 w).asIdeal) :=
    Fintype.ofFinite _
  choose r hr using fun x : Rinf (Lc Fq Ω (lev 0)) (Fc Fq F Ω (lev 0)) ⧸ (contInfB Fq F Ω hk 0 w).asIdeal =>
    Ideal.Quotient.mk_surjective x
  choose cst hcst using fun x => exists_const_of_isAlgClosed (L := kbar Fq Ω) w (infR Fq F Ω 0 (r x))
  choose J hJ using fun x => exists_lev_of_mem_kbar (cst x).2
  refine ⟨Finset.univ.sup J, fun M hM => ?_⟩
  haveI : Fact (lev 0 ∣ lev M) := ⟨lev_dvd_lev (Nat.zero_le M)⟩
  letI := algInf (isConstExt_pair Fq F Ω hk (n := lev 0) (N := lev M))
  have hbase : ∀ a : Rinf (Lc Fq Ω (lev 0)) (Fc Fq F Ω (lev 0)), ∃ l : Lc Fq Ω (lev M),
      algebraMap _ (Rinf (Lc Fq Ω (lev M)) (Fc Fq F Ω (lev M))) a -
        algebraMap (Lc Fq Ω (lev M)) (Rinf (Lc Fq Ω (lev M)) (Fc Fq F Ω (lev M))) l ∈
          (contInfB Fq F Ω hk M w).asIdeal := by
    intro a
    let x := Ideal.Quotient.mk (contInfB Fq F Ω hk 0 w).asIdeal a
    have hxM : J x ≤ M := le_trans (Finset.le_sup (Finset.mem_univ x)) hM
    refine ⟨⟨(cst x : Ω), Lc_le (lev_dvd_lev hxM) (hJ x)⟩, ?_⟩
    rw [mem_contInfB Fq F Ω hk, RingHom.map_sub, infR_pair Fq F Ω hk, infR_algebraMap_L Fq F Ω M _ (cst x) rfl]
    have h1 : a - r x ∈ (contInfB Fq F Ω hk 0 w).asIdeal := by
      rw [← Ideal.Quotient.eq]; exact (hr x).symm
    rw [mem_contInfB Fq F Ω hk, RingHom.map_sub] at h1
    have h2 := w.asIdeal.add_mem h1 (hcst x)
    rwa [sub_add_sub_cancel] at h2
  exact deg_eq_one_of_const _ (const_of_base_inf (isConstExt_pair Fq F Ω hk (n := lev 0) (N := lev M)) _ hbase)

include hk in
/-- **Degree 1 at large levels**: every place of `F-bar` contracts to degree-1 places. -/
theorem degOne (P : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)) :
    ∃ M0, ∀ M, M0 ≤ M → (contB Fq F Ω hk M P).deg = 1 := by
  rcases P with w | w
  · obtain ⟨M0, h⟩ := degOne_fin Fq F Ω hk w
    exact ⟨M0, fun M hM => by rw [contB_inl, Place.deg_inl]; exact h M hM⟩
  · obtain ⟨M0, h⟩ := degOne_inf Fq F Ω hk w
    exact ⟨M0, fun M hM => by rw [contB_inr, Place.deg_inr]; exact h M hM⟩

/-- **Separation**: distinct places of `F-bar` have distinct contractions at some level. -/
theorem sepB {P1 P2 : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)} (h12 : P1 ≠ P2) :
    ∃ j, contB Fq F Ω hk j P1 ≠ contB Fq F Ω hk j P2 := by
  have hside : P1.isLeft ≠ P2.isLeft → ∃ j, contB Fq F Ω hk j P1 ≠ contB Fq F Ω hk j P2 := fun hs =>
    ⟨0, fun he => hs (by rw [← isLeft_contB Fq F Ω hk 0 P1, he, isLeft_contB])⟩
  rcases P1 with w1 | w1 <;> rcases P2 with w2 | w2
  · have hw : w1 ≠ w2 := fun he => h12 (congrArg Sum.inl he)
    obtain ⟨z, hz1, hz2⟩ := exists_not_mem_of_ne hw
    obtain ⟨j, y, rfl⟩ := exists_finR Fq F Ω z
    refine ⟨j, fun he => hz2 ?_⟩
    rw [contB_inl, contB_inl] at he
    rw [← mem_contFinB Fq F Ω hk, ← Sum.inl.inj he, mem_contFinB]
    exact hz1
  · exact hside (by simp)
  · exact hside (by simp)
  · have hw : w1 ≠ w2 := fun he => h12 (congrArg Sum.inr he)
    obtain ⟨z, hz1, hz2⟩ := exists_not_mem_of_ne hw
    obtain ⟨j, y, rfl⟩ := exists_infR Fq F Ω z
    refine ⟨j, fun he => hz2 ?_⟩
    rw [contB_inr, contB_inr] at he
    rw [← mem_contInfB Fq F Ω hk, ← Sum.inr.inj he, mem_contInfB]
    exact hz1

theorem contB_ne_mono {P1 P2 : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)} {j M : ℕ} (hjM : j ≤ M)
    (h : contB Fq F Ω hk j P1 ≠ contB Fq F Ω hk j P2) : contB Fq F Ω hk M P1 ≠ contB Fq F Ω hk M P2 := by
  haveI : Fact (lev j ∣ lev M) := ⟨lev_dvd_lev hjM⟩
  intro he
  apply h
  rw [← contractNN_contB Fq F Ω hk (i := j) (j := M) P1, he, contractNN_contB]

/-- **Uniqueness** over a degree-1 contraction. -/
theorem uniqB {M : ℕ} {P P' : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)} (hdeg : (contB Fq F Ω hk M P).deg = 1)
    (he : contB Fq F Ω hk M P' = contB Fq F Ω hk M P) : P' = P := by
  classical
  by_contra hne
  obtain ⟨j1, hj1⟩ := sepB Fq F Ω hk hne
  have hne' := contB_ne_mono Fq F Ω hk (le_max_right M j1) hj1
  haveI : Fact (lev M ∣ lev (max M j1)) := ⟨lev_dvd_lev (le_max_left M j1)⟩
  have hs := sum_deg_fibre (isConstExt_pair Fq F Ω hk (n := lev M) (N := lev (max M j1))) (contB Fq F Ω hk M P)
  have h1 : contB Fq F Ω hk (max M j1) P' ∈
      fibre (isConstExt_pair Fq F Ω hk (n := lev M) (N := lev (max M j1))) (contB Fq F Ω hk M P) := by
    rw [mem_fibre]
    exact (contractNN_contB Fq F Ω hk (i := M) (j := max M j1) P').trans he
  have h2 : contB Fq F Ω hk (max M j1) P ∈
      fibre (isConstExt_pair Fq F Ω hk (n := lev M) (N := lev (max M j1))) (contB Fq F Ω hk M P) := by
    rw [mem_fibre]
    exact contractNN_contB Fq F Ω hk (i := M) (j := max M j1) P
  have hsub : ({contB Fq F Ω hk (max M j1) P', contB Fq F Ω hk (max M j1) P} : Finset _) ⊆
      fibre (isConstExt_pair Fq F Ω hk (n := lev M) (N := lev (max M j1))) (contB Fq F Ω hk M P) := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    exacts [h1, h2]
  have hle := Finset.sum_le_sum_of_subset (f := fun Q => Places.Place.deg Q) hsub
  rw [Finset.sum_pair hne', hs, hdeg] at hle
  have d1 := Place.deg_pos (contB Fq F Ω hk (max M j1) P')
  have d2 := Place.deg_pos (contB Fq F Ω hk (max M j1) P)
  omega

/-- The (finite) fibre of the contraction to level `lev j`. -/
noncomputable def fibreB (j : ℕ) (Q : Places.Place (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) :
    Finset (Places.Place (kbar Fq Ω) (Fbar Fq F Ω)) :=
  (finite_contB Fq F Ω hk j Q).toFinset

theorem mem_fibreB (j : ℕ) (Q : Places.Place (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)))
    (P : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)) : P ∈ fibreB Fq F Ω hk j Q ↔ contB Fq F Ω hk j P = Q := by
  rw [fibreB, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

end DegOne

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_BrPsi =====
section

/-!
# S4-JacFrob, part BrPsi (bridge 5): `Pic(X-bar) ≃ Pic(F-bar / k-bar)`

* `psiD j`: pull a level divisor back to `F-bar` (`psiD j D P = D (contB j P)`); injective, compatible with conorm,
  `psiD j (div f) = div f`, degree preserving (`card_fibreB`);
* `psiPic j`: the induced map on classes; `Psi0 : PicBar →+ PicK` (direct-limit lift);
* **`Psi : PicBar ≃+ PicK (kbar) (Fbar)`**, `degPicK_Psi`, **`Psi0Equiv : PicBar0 ≃+ Pic0K`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.JacFrob

open Polynomial IsDedekindDomain RamanujanPetersson.PicDescent Places ZetaSB RamanujanPetersson.JacComplete

section Psi

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

/-- Pull a level divisor back to `F-bar`: `psiD j D P = D (contB j P)`. -/
noncomputable def psiD (j : ℕ) :
    Places.Divisor (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)) →+ Places.Divisor (kbar Fq Ω) (Fbar Fq F Ω) where
  toFun D := by
    classical
    exact Finsupp.onFinset (D.support.biUnion (fibreB Fq F Ω hk j)) (fun P => D (contB Fq F Ω hk j P))
      (fun P hP => Finset.mem_biUnion.2 ⟨contB Fq F Ω hk j P, Finsupp.mem_support_iff.2 hP,
        (mem_fibreB Fq F Ω hk _ _ _).2 rfl⟩)
  map_zero' := by ext; simp
  map_add' D E := by ext; simp

theorem psiD_apply (j : ℕ) (D : Places.Divisor (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)))
    (P : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)) : psiD Fq F Ω hk j D P = D (contB Fq F Ω hk j P) := by
  simp [psiD]

include hk in
theorem psiD_injective (j : ℕ) : Function.Injective (psiD Fq F Ω hk j) := by
  refine (injective_iff_map_eq_zero _).2 fun D hD => ?_
  ext Q
  obtain ⟨P, rfl⟩ := exists_contB_eq Fq F Ω hk j Q
  rw [← psiD_apply Fq F Ω hk j D P, hD]
  rfl

theorem psiD_conormNN {i j : ℕ} [Fact (lev i ∣ lev j)] (D : Places.Divisor (Lc Fq Ω (lev i)) (Fc Fq F Ω (lev i))) :
    psiD Fq F Ω hk j (conormNN Ω hk (lev i) (lev j) D) = psiD Fq F Ω hk i D := by
  ext P
  rw [psiD_apply, psiD_apply, conormNN_apply, contractNN_contB Fq F Ω hk (i := i) (j := j) P]

theorem psiD_single (j : ℕ) (Q : Places.Place (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (n : ℤ) :
    psiD Fq F Ω hk j (Finsupp.single Q n) = ∑ P ∈ fibreB Fq F Ω hk j Q, Finsupp.single P n := by
  classical
  ext P
  rw [psiD_apply, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  by_cases h : contB Fq F Ω hk j P = Q
  · rw [if_pos h.symm, if_pos ((mem_fibreB Fq F Ω hk j Q P).2 h)]
  · rw [if_neg (Ne.symm h), if_neg (fun h' => h ((mem_fibreB Fq F Ω hk j Q P).1 h'))]

end Psi

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_CoreB_Triv =====
section

/-!
# Core B, O2: the genus 0 case

* `degreeDataOfSubsingleton`: on a trivial group the constant degree `1` is degree data of genus `0`.
* `subsingleton_Pic0K_of_genus_zero`: for `g = 0` the group `Pic⁰(F / K)` is trivial.
* `subsingleton_PicBar0_of_genus_zero`: if `genusFK (kbar) (Fbar) = 0` then `PicBar0 Ω hk` is trivial.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CoreB

open RamanujanPetersson.JacAlg

/-- On a trivial group the constant degree `1` is degree data of genus `0`. -/
def degreeDataOfSubsingleton {A : Type*} [AddCommGroup A] [Subsingleton A] (π : Module.End ℤ A)
    (p : ℕ) : DegreeData π 0 p where
  deg _ := 1
  deg_one := rfl
  deg_mul _ _ := rfl
  deg_natCast n := by simp
  deg_poly _ _ := ⟨1, by simp, fun _ => by simp⟩
  deg_eq_zero_iff F := by
    constructor
    · intro h; exact absurd h one_ne_zero
    · intro h; exact (h (Set.toFinite _)).elim
  deg_eq_card_ker F _ := by
    have : Subsingleton (LinearMap.ker (aeval π F)) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    exact (Nat.card_eq_one_iff_unique.2 ⟨this, ⟨0⟩⟩).symm

theorem degreeDataOfSubsingleton_deg {A : Type*} [AddCommGroup A] [Subsingleton A]
    (π : Module.End ℤ A) (p : ℕ) (F : ℤ[X]) : (degreeDataOfSubsingleton π p).deg F = 1 := rfl

section Pic0K

open RamanujanPetersson.JacComplete RamanujanPetersson.RR

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

theorem subsingleton_Pic0K_of_genus_zero (hg : genusFK K F = 0) : Subsingleton (Pic0K K F) := by
  refine ⟨fun a b => ?_⟩
  have h0 : ∀ z : Pic0K K F, z = 0 := fun z => by
    obtain ⟨x, hx⟩ := z
    obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective x
    have hD : D.deg = 0 := (mem_Pic0K K F).1 hx
    exact Subtype.ext (clsK_eq_zero_of_genus_zero hg hD)
  rw [h0 a, h0 b]

end Pic0K

section PicBar0

open RamanujanPetersson.JacComplete RamanujanPetersson.JacFrob RamanujanPetersson.RR
open RamanujanPetersson.PicDescent RamanujanPetersson.Places

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

end PicBar0

end RamanujanPetersson.CoreB


end

-- ===== S4.Def_RP_DegPoly =====
section

/-!
# Degree polynomiality (unit S4-DegPoly, lemma L37 of `S4_COREB_ROUTE.md`)

Milne, *Abelian Varieties*, Lemma 10.12 and Prop. 10.13, in hypothesis form and over pure algebra.

`I` is a `g`-linear integer form on an abelian group `M` (the intersection form on divisors of an abelian variety of
dimension `g`), `c : R → M` sends an endomorphism `a` to the class `a^* D` of a divisor `D = c 1`, and
`deg : R → ℕ` is the degree. Two classes are *numerically equivalent* when their difference lies in `numKer I`.
Assume
* `(D^g) ≠ 0`;
* the projection formula `((a^* D)^g) = deg a · (D^g)`;
* the quadratic relation `(n a + b)^* D ≡ n² a^* D + n e(a, b) + b^* D` for all `a, b` (this is where `D` symmetric
  enters), and `0^* D ≡ 0`.
Then `n ↦ deg (n a + b)` is a polynomial of degree `≤ 2g` with rational coefficients, and `deg n = n ^ (2g)`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.DegPoly

open Polynomial

variable {M : Type*} [AddCommGroup M] {g : ℕ}

theorem mem_numKer {I : MultilinearMap ℤ (fun _ : Fin g => M) ℤ} {u : M} :
    u ∈ numKer I ↔ ∀ (w : Fin g → M) (i : Fin g), I (Function.update w i u) = 0 :=
  Iff.rfl

/-- A `g`-linear form over `ℤ` from a function that is additive in each slot (for example `IntersectB.iform`). -/
def formOfAdd (f : (Fin g → M) → ℤ)
    (hf : ∀ (w : Fin g → M) (i : Fin g) (x y : M),
      f (Function.update w i (x + y)) = f (Function.update w i x) + f (Function.update w i y)) :
    MultilinearMap ℤ (fun _ : Fin g => M) ℤ :=
  MultilinearMap.mk' f hf (fun w i k x =>
    map_zsmul (AddMonoidHom.mk' (fun y => f (Function.update w i y)) (hf w i)) k x)

theorem formOfAdd_apply (f : (Fin g → M) → ℤ)
    (hf : ∀ (w : Fin g → M) (i : Fin g) (x y : M),
      f (Function.update w i (x + y)) = f (Function.update w i x) + f (Function.update w i y))
    (w : Fin g → M) : formOfAdd f hf w = f w :=
  rfl

variable (I : MultilinearMap ℤ (fun _ : Fin g => M) ℤ)

/-- Adding a numerically trivial class does not change the self-intersection. -/
theorem map_add_of_mem {u : M} (hu : u ∈ numKer I) (y : M) :
    I (fun _ => u + y) = I (fun _ => y) := by
  have h := I.map_add_univ (fun _ => u) (fun _ => y)
  rw [show ((fun _ : Fin g => u) + fun _ => y) = fun _ => u + y from rfl] at h
  rw [h, Finset.sum_eq_single (∅ : Finset (Fin g))]
  · simp
  · intro s _ hs
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    have he : Function.update (s.piecewise (fun _ => u) (fun _ => y)) i u =
        s.piecewise (fun _ => u) (fun _ => y) :=
      Function.update_eq_self_iff.mpr (by simp [Finset.piecewise_eq_of_mem _ _ _ hi])
    rw [← he]
    exact hu _ i
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Numerically equivalent classes have the same self-intersection. -/
theorem self_eq_of_sub_mem {x y : M} (h : x - y ∈ numKer I) : I (fun _ => x) = I (fun _ => y) := by
  have := map_add_of_mem I h y
  rwa [sub_add_cancel] at this

/-- Milne 10.12, the algebraic core: `n ↦ ((n² x + n y + z)^g)` is a polynomial of degree `≤ 2g`. -/
theorem exists_poly (x y z : M) : ∃ P : ℤ[X], P.natDegree ≤ 2 * g ∧
    ∀ n : ℤ, I (fun _ => n ^ 2 • x + n • y + z) = P.eval n := by
  let v : Fin 3 → M := ![z, y, x]
  refine ⟨∑ r : Fin g → Fin 3, C (I (fun i => v (r i))) * X ^ (∑ i, (r i : ℕ)), ?_, ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun r _ => (natDegree_C_mul_X_pow_le _ _).trans ?_
    calc ∑ i, (r i : ℕ) ≤ ∑ _i : Fin g, 2 :=
          Finset.sum_le_sum fun i _ => Nat.lt_succ_iff.mp (r i).isLt
      _ = 2 * g := by simp [mul_comm]
  · intro n
    have hv : (fun _ : Fin g => n ^ 2 • x + n • y + z) =
        fun _ => ∑ j : Fin 3, n ^ (j : ℕ) • v j := by
      funext _
      simp [v, Fin.sum_univ_succ]
      abel
    rw [hv, I.map_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [I.map_smul_univ (fun i => n ^ (r i : ℕ)) (fun i => v (r i))]
    simp [Finset.prod_pow_eq_pow_sum, mul_comm]

variable {R : Type*} [Ring R]

/-- `deg 1 = 1` from the projection formula. -/
theorem deg_one_of_proj (c : R → M) (deg : R → ℕ) (hD : I (fun _ => c 1) ≠ 0)
    (hproj : ∀ a, I (fun _ => c a) = deg a * I (fun _ => c 1)) : deg 1 = 1 := by
  have h := hproj 1
  have h1 : ((deg 1 : ℕ) : ℤ) = 1 := by
    have := mul_right_cancel₀ hD (h.symm.trans (one_mul _).symm)
    exact this
  exact_mod_cast h1

/-- **Milne Lemma 10.12 / Prop. 10.13 (L37), (D2) first half.** `n ↦ deg (n a + b)` is a polynomial in `n ∈ ℤ`
of degree `≤ 2g` with rational coefficients. -/
theorem deg_poly_of_quad (c : R → M) (deg : R → ℕ) (hD : I (fun _ => c 1) ≠ 0)
    (hproj : ∀ a, I (fun _ => c a) = deg a * I (fun _ => c 1))
    (hquad : ∀ a b : R, ∃ e : M, ∀ n : ℤ, c (n * a + b) - (n ^ 2 • c a + n • e + c b) ∈ numKer I)
    (a b : R) : ∃ P : ℚ[X], P.natDegree ≤ 2 * g ∧
      ∀ n : ℤ, (deg (n * a + b) : ℚ) = P.eval (n : ℚ) := by
  obtain ⟨e, he⟩ := hquad a b
  obtain ⟨P, hPdeg, hP⟩ := exists_poly I (c a) e (c b)
  refine ⟨C ((I (fun _ => c 1) : ℚ)⁻¹) * P.map (Int.castRingHom ℚ), ?_, fun n => ?_⟩
  · exact (natDegree_C_mul_le _ _).trans (natDegree_map_le.trans hPdeg)
  · have h1 := hproj (n * a + b)
    rw [self_eq_of_sub_mem I (he n), hP n] at h1
    have hd : ((I (fun _ => c 1) : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hD
    rw [eval_mul, eval_C, eval_intCast_map, Int.cast_id, h1, map_mul, map_natCast, eq_intCast]
    field_simp

/-- **(D2) second half.** For symmetric `D` (quadratic relation with the `n²` coefficient, and `0^* D ≡ 0`):
`deg n = n ^ (2g)`. -/
theorem deg_natCast_of_quad (c : R → M) (deg : R → ℕ) (hD : I (fun _ => c 1) ≠ 0)
    (hproj : ∀ a, I (fun _ => c a) = deg a * I (fun _ => c 1))
    (hquad : ∀ a b : R, ∃ e : M, ∀ n : ℤ, c (n * a + b) - (n ^ 2 • c a + n • e + c b) ∈ numKer I)
    (hzero : c 0 ∈ numKer I) (n : ℕ) : deg (n : R) = n ^ (2 * g) := by
  obtain ⟨e, he⟩ := hquad 1 0
  have h1 := he 1
  simp only [Int.cast_one, one_mul, add_zero, one_pow, one_smul] at h1
  have he0 : e ∈ numKer I := by
    have : e = -(c 1 - (c 1 + e + c 0)) - c 0 := by abel
    rw [this]
    exact sub_mem (neg_mem h1) hzero
  have hn := he n
  simp only [Int.cast_natCast, mul_one, add_zero] at hn
  have hk : c (n : R) - ((n : ℤ) ^ 2 • c 1) ∈ numKer I := by
    have : c (n : R) - (n : ℤ) ^ 2 • c 1 =
        (c (n : R) - ((n : ℤ) ^ 2 • c 1 + (n : ℤ) • e + c 0)) + ((n : ℤ) • e + c 0) := by abel
    rw [this]
    exact add_mem hn (add_mem (zsmul_mem he0 _) hzero)
  have h2 := hproj (n : R)
  rw [self_eq_of_sub_mem I hk, I.map_smul_univ (fun _ => ((n : ℤ) ^ 2)) (fun _ => c 1)] at h2
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
  have h3 := mul_right_cancel₀ hD h2
  have h4 : ((deg (n : R) : ℕ) : ℤ) = ((n ^ (2 * g) : ℕ) : ℤ) := by
    rw [← h3]
    push_cast
    rw [← pow_mul]
  exact_mod_cast h4

end RamanujanPetersson.DegPoly


end

-- ===== S4.Def_RP_DegPoly_Data =====
section

/-!
# Degree polynomiality, part 2: (D2) in `DegreeData` form (unit S4-DegPoly, L37)

For `R = ℤ[X]` (where `c F` is the class of `F(π_J)^* D` and `deg F` the degree of `F(π_J)`), the quadratic-relation
data of `Def_RP_DegPoly` gives the fields `deg_one`, `deg_natCast` and `deg_poly` of `JacAlg.DegreeData`.
`degreeDataOfQuad` assembles a `DegreeData` from that data together with (D1) multiplicativity and (D3).
-/

set_option autoImplicit false

namespace RamanujanPetersson.DegPoly

open Polynomial RamanujanPetersson.JacAlg

variable {A : Type*} [AddCommGroup A] {M : Type*} [AddCommGroup M] {g : ℕ}

/-- (D2), first half, in the exact shape of the field `DegreeData.deg_poly`. -/
theorem deg_poly_zsmul (I : MultilinearMap ℤ (fun _ : Fin g => M) ℤ) (c : ℤ[X] → M) (deg : ℤ[X] → ℕ)
    (hD : I (fun _ => c 1) ≠ 0)
    (hproj : ∀ F, I (fun _ => c F) = deg F * I (fun _ => c 1))
    (hquad : ∀ F G : ℤ[X], ∃ e : M, ∀ n : ℤ,
      c (n * F + G) - (n ^ 2 • c F + n • e + c G) ∈ numKer I)
    (F G : ℤ[X]) : ∃ P : ℚ[X], P.natDegree ≤ 2 * g ∧
      ∀ n : ℤ, (deg (n • F + G) : ℚ) = P.eval (n : ℚ) := by
  obtain ⟨P, h1, h2⟩ := deg_poly_of_quad I c deg hD hproj hquad F G
  exact ⟨P, h1, fun n => by rw [zsmul_eq_mul]; exact h2 n⟩

/-- **L37 output.** A `DegreeData` from the quadratic-relation data ((D2) and `deg 1 = 1`), multiplicativity and
(D3). -/
def degreeDataOfQuad (π : Module.End ℤ A) (g p : ℕ) (I : MultilinearMap ℤ (fun _ : Fin g => M) ℤ)
    (c : ℤ[X] → M) (deg : ℤ[X] → ℕ) (hD : I (fun _ => c 1) ≠ 0)
    (hproj : ∀ F, I (fun _ => c F) = deg F * I (fun _ => c 1))
    (hquad : ∀ F G : ℤ[X], ∃ e : M, ∀ n : ℤ,
      c (n * F + G) - (n ^ 2 • c F + n • e + c G) ∈ numKer I)
    (hzero : c 0 ∈ numKer I)
    (deg_mul : ∀ F G : ℤ[X], deg (F * G) = deg F * deg G)
    (deg_eq_zero_iff : ∀ F : ℤ[X], deg F = 0 ↔ (LinearMap.ker (aeval π F) : Set A).Infinite)
    (deg_eq_card_ker : ∀ F : ℤ[X], ¬ (p : ℤ) ∣ F.coeff 0 →
      deg F = Nat.card (LinearMap.ker (aeval π F))) :
    DegreeData π g p where
  deg := deg
  deg_one := deg_one_of_proj I c deg hD hproj
  deg_mul := deg_mul
  deg_natCast := deg_natCast_of_quad I c deg hD hproj hquad hzero
  deg_poly := deg_poly_zsmul I c deg hD hproj hquad
  deg_eq_zero_iff := deg_eq_zero_iff
  deg_eq_card_ker := deg_eq_card_ker

theorem degreeDataOfQuad_deg (π : Module.End ℤ A) (g p : ℕ) (I : MultilinearMap ℤ (fun _ : Fin g => M) ℤ)
    (c : ℤ[X] → M) (deg : ℤ[X] → ℕ) (hD : I (fun _ => c 1) ≠ 0)
    (hproj : ∀ F, I (fun _ => c F) = deg F * I (fun _ => c 1))
    (hquad : ∀ F G : ℤ[X], ∃ e : M, ∀ n : ℤ,
      c (n * F + G) - (n ^ 2 • c F + n • e + c G) ∈ numKer I)
    (hzero : c 0 ∈ numKer I)
    (deg_mul : ∀ F G : ℤ[X], deg (F * G) = deg F * deg G)
    (deg_eq_zero_iff : ∀ F : ℤ[X], deg F = 0 ↔ (LinearMap.ker (aeval π F) : Set A).Infinite)
    (deg_eq_card_ker : ∀ F : ℤ[X], ¬ (p : ℤ) ∣ F.coeff 0 →
      deg F = Nat.card (LinearMap.ker (aeval π F))) :
    (degreeDataOfQuad π g p I c deg hD hproj hquad hzero deg_mul deg_eq_zero_iff deg_eq_card_ker).deg = deg :=
  rfl

end RamanujanPetersson.DegPoly


end

-- ===== S4.Def_RP_JacDivisors_H =====
section

/-!
# S4-JacDivisors H (O11: Weil divisors on integral locally Noetherian schemes)
* `finite_coheight_one_not_mem_basicOpen`: on an affine open `U`, a nonzero section `a` vanishes at only
  finitely many codimension-one points.
* `div f : AlgebraicCycle X ℤ`: the principal divisor `z ↦ ord_z f` (locally finite support).
* `div_mul`, `div_one`, `div_inv`, `div_isWeil`, `div_germ_nonneg`.
* `weilDivisors X`, `principalDivisors X`, `LinEquiv` (linear equivalence, an equivalence relation).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open AlgebraicGeometry CategoryTheory Order Topology

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- A nonzero section on an affine open vanishes at finitely many codimension-one points. -/
lemma finite_coheight_one_not_mem_basicOpen {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U]
    (a : Γ(X, U)) (ha : a ≠ 0) :
    {z : X | z ∈ U ∧ coheight z = 1 ∧ z ∉ X.basicOpen a}.Finite := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hS : {y : Spec Γ(X, U) | y.asIdeal ∈ (Ideal.span {a}).minimalPrimes}.Finite :=
    (Ideal.span {a}).finite_minimalPrimes_of_isNoetherianRing.preimage
      (fun y _ y' _ h => PrimeSpectrum.ext h)
  refine (hS.image hU.fromSpec).subset ?_
  rintro z ⟨hzU, hz1, hza⟩
  have hzU' : z ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hzU
  obtain ⟨y, rfl⟩ := hzU'
  refine ⟨y, ?_, rfl⟩
  have hy1 : y.asIdeal.height = 1 := by
    rw [idealHeight_eq_coheight, ← coheight_eq_of_isOpenImmersion hU.fromSpec]
    exact hz1
  have hay : a ∈ y.asIdeal := by
    have h : y ∉ hU.fromSpec ⁻¹ᵁ X.basicOpen a := hza
    rw [hU.fromSpec_preimage_basicOpen] at h
    by_contra hn
    exact h hn
  have : y.asIdeal.IsPrime := y.isPrime
  have : y.asIdeal.FiniteHeight :=
    Ideal.finiteHeight_iff_lt.mpr (Or.inr (lt_of_eq_of_lt hy1 ENat.one_lt_top))
  refine Ideal.mem_minimalPrimes_of_height_le ((Ideal.span_singleton_le_iff_mem _).mpr hay) ?_
  rw [hy1]
  exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero ha)

/-- A section has order zero wherever it is a unit. -/
lemma ord_germ_eq_zero {U : X.Opens} [Nonempty U] (a : Γ(X, U)) {z : X}
    (hz : z ∈ X.basicOpen a) : Scheme.ord (X.germToFunctionField U a) z = 0 := by
  have : Nonempty (X.basicOpen a) := ⟨⟨z, hz⟩⟩
  have : Nonempty (X.toRingedSpace.basicOpen a) := ⟨⟨z, hz⟩⟩
  have h := Scheme.ord_of_isUnit (X.toRingedSpace.isUnit_res_basicOpen a) hz
  convert h using 2
  exact (X.presheaf.germ_res_apply (homOfLE (X.basicOpen_le a)) _ _ a).symm

lemma ord_one (z : X) : Scheme.ord (1 : X.functionField) z = 0 := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  have h := Scheme.ord_of_isUnit (U := ⊤) (f := 1) isUnit_one (x := z) trivial
  rwa [map_one] at h

/-- Sections are regular: `ord_z a ≥ 0` at every point of `U`. -/
lemma ord_germ_nonneg {U : X.Opens} [Nonempty U] (a : Γ(X, U)) {z : X} (hz : z ∈ U) :
    0 ≤ Scheme.ord (X.germToFunctionField U a) z := by
  by_cases ha : a = 0
  · simp [ha]
  have h := Scheme.ord_le_smul hz ha (1 : X.functionField)
  rw [ord_one, Algebra.smul_def, mul_one] at h
  exact h

lemma finite_support_ord_inter {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U]
    (f : X.functionField) :
    ((U : Set X) ∩ Function.support (fun z => Scheme.ord f z)).Finite := by
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  by_cases hf : f = 0
  · simp [hf]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Γ(X, U)) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha : a ≠ 0 := by rintro rfl; simp at hf
  refine ((finite_coheight_one_not_mem_basicOpen hU a ha).union
    (finite_coheight_one_not_mem_basicOpen hU b hb0)).subset ?_
  rintro z ⟨hzU, hz⟩
  have h1 : coheight z = 1 := by
    by_contra h; exact hz (Scheme.ord_eq_zero_of_coheight_neq_one h _)
  by_contra hmem
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_and, not_not] at hmem
  apply hz
  have hA : algebraMap Γ(X, U) X.functionField a ≠ 0 := by
    rintro h; apply hf; rw [h, zero_div]
  have hB : algebraMap Γ(X, U) X.functionField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective Γ(X, U) X.functionField)).mpr hb0
  have hq : algebraMap Γ(X, U) X.functionField a / algebraMap Γ(X, U) X.functionField b ≠ 0 :=
    div_ne_zero hA hB
  have key := Scheme.ord_mul (x := z) hq hB
  rw [div_mul_cancel₀ _ hB] at key
  have e1 : Scheme.ord (algebraMap Γ(X, U) X.functionField a) z = 0 :=
    ord_germ_eq_zero a (hmem.1 hzU h1)
  have e2 : Scheme.ord (algebraMap Γ(X, U) X.functionField b) z = 0 :=
    ord_germ_eq_zero b (hmem.2 hzU h1)
  change Scheme.ord _ z = 0
  omega

lemma locallyFinite_ord (f : X.functionField) (z : X) :
    ∃ t ∈ 𝓝 z, (t ∩ Function.support (fun z => Scheme.ord f z)).Finite := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  exact ⟨U, U.isOpen.mem_nhds hzU, finite_support_ord_inter hU f⟩

variable (X) in
/-- The principal divisor of a rational function, `z ↦ ord_z f` (junk value `0` for `f = 0`). -/
noncomputable def div (f : X.functionField) : AlgebraicCycle X ℤ where
  toFun z := Scheme.ord f z
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' z _ := locallyFinite_ord f z

lemma div_apply (f : X.functionField) (z : X) : div X f z = Scheme.ord f z := rfl

lemma div_mul {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    div X (f * g) = div X f + div X g := by
  ext z; simp [div_apply, Scheme.ord_mul hf hg]

lemma div_one : div X (1 : X.functionField) = 0 := by
  ext z; simp [div_apply, ord_one]

lemma div_zero : div X (0 : X.functionField) = 0 := by
  ext z; simp [div_apply]

lemma div_inv {f : X.functionField} (hf : f ≠ 0) : div X f⁻¹ = -div X f := by
  have h := div_mul hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf, div_one] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

variable (X) in
/-- Weil divisors: cycles supported on codimension-one points. -/
def weilDivisors : AddSubgroup (AlgebraicCycle X ℤ) where
  carrier := {D | ∀ z, D z ≠ 0 → coheight z = 1}
  zero_mem' z h := (h rfl).elim
  add_mem' {D E} hD hE z h := by
    by_contra hz
    exact h (by simp [Function.locallyFinsuppWithin.coe_add, not_not.mp (mt (hD z) hz),
      not_not.mp (mt (hE z) hz)])
  neg_mem' {D} hD z h := hD z (by simp at h; exact h)

lemma div_mem_weilDivisors (f : X.functionField) : div X f ∈ weilDivisors X := by
  intro z h
  by_contra hz
  exact h (Scheme.ord_eq_zero_of_coheight_neq_one hz f)

end RamanujanPetersson.JacDivisors


end

-- ===== S4.Def_RP_JacDivisors_I =====
section

/-!
# S4-JacDivisors I (O12 bridges: orders of sections at codimension-one points, affine charts)
* `ord_algebraMap_stalk`: `ord_z b = length (O_z ⧸ b)` for `b` in the stalk at a codimension-one point.
* `ord_germ_pos`: a nonzero section vanishing at `z` has positive order there.
* `ord_germ_eq_one`: a section whose germ generates the maximal ideal has order one.
* affine chart dictionary: `fromSpec_mem_basicOpen_iff`, `coheight_fromSpec`, `fromSpec_specializes_iff`,
  `fromSpec_mem`, `exists_fromSpec_eq`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open AlgebraicGeometry CategoryTheory Order Topology IsLocalRing

universe u

variable {X : Scheme.{u}}

section
variable [IsIntegral X] [IsLocallyNoetherian X]

lemma ord_algebraMap_stalk {z : X} (hz : coheight z = 1) {b : X.presheaf.stalk z} (hb : b ≠ 0)
    {n : ℕ} (hn : Ring.ord (X.presheaf.stalk z) b = n) :
    Scheme.ord (algebraMap (X.presheaf.stalk z) X.functionField b) z = n := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  have hK : algebraMap (X.presheaf.stalk z) X.functionField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb
  rw [Scheme.ord_eq_iff hz hK]
  change Ring.ordFrac (X.presheaf.stalk z) (algebraMap _ X.functionField b) = _
  rw [Ring.ordFrac_eq_ord _ hb]
  exact Ring.ordMonoidWithZeroHom_eq_coe _ (mem_nonZeroDivisors_of_ne_zero hb) hn

lemma ord_algebraMap_stalk_pos {z : X} (hz : coheight z = 1) {b : X.presheaf.stalk z} (hb : b ≠ 0)
    (hbm : b ∈ maximalIdeal (X.presheaf.stalk z)) :
    0 < Scheme.ord (algebraMap (X.presheaf.stalk z) X.functionField b) z := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
    (Ring.ord_ne_top (R := X.presheaf.stalk z) (mem_nonZeroDivisors_of_ne_zero hb))
  rw [ord_algebraMap_stalk hz hb hn.symm]
  have hnt : Nontrivial (X.presheaf.stalk z ⧸ Ideal.span {b}) :=
    Ideal.Quotient.nontrivial_iff.mpr (fun h =>
      (maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (h ▸ (Ideal.span_singleton_le_iff_mem _).mpr hbm)))
  have hpos : 0 < Ring.ord (X.presheaf.stalk z) b := Module.length_pos
  rw [← hn] at hpos
  exact_mod_cast hpos

lemma ord_algebraMap_stalk_eq_one {z : X} (hz : coheight z = 1) {b : X.presheaf.stalk z}
    (hb : b ≠ 0) (hbm : Ideal.span {b} = maximalIdeal (X.presheaf.stalk z)) :
    Scheme.ord (algebraMap (X.presheaf.stalk z) X.functionField b) z = 1 := by
  have h1 : Ring.ord (X.presheaf.stalk z) b = ((1 : ℕ) : ℕ∞) := by
    have : IsSimpleModule (X.presheaf.stalk z) (X.presheaf.stalk z ⧸ Ideal.span {b}) := by
      rw [hbm]
      exact isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (maximalIdeal.isMaximal _))
    show Module.length _ _ = _
    rw [Module.length_eq_one]
    rfl
  exact_mod_cast ord_algebraMap_stalk hz hb h1

lemma germ_ne_zero {U : X.Opens} {z : X} (hz : z ∈ U) {r : Γ(X, U)} (hr : r ≠ 0) :
    X.presheaf.germ U z hz r ≠ 0 := by
  intro h
  exact hr (germ_injective_of_isIntegral X z hz (h.trans (map_zero _).symm))

/-- A nonzero section vanishing at a codimension-one point has positive order there. -/
lemma ord_germ_pos {U : X.Opens} [Nonempty U] {z : X} (hz : z ∈ U) (hz1 : coheight z = 1)
    {r : Γ(X, U)} (hr : r ≠ 0) (hzr : z ∉ X.basicOpen r) :
    0 < Scheme.ord (X.germToFunctionField U r) z := by
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hz r]
  refine ord_algebraMap_stalk_pos hz1 (germ_ne_zero hz hr) ?_
  rw [Scheme.mem_basicOpen X r z hz] at hzr
  exact (mem_maximalIdeal _).mpr hzr

/-- A section whose germ generates the maximal ideal at a codimension-one point has order one. -/
lemma ord_germ_eq_one {U : X.Opens} [Nonempty U] {z : X} (hz : z ∈ U) (hz1 : coheight z = 1)
    {r : Γ(X, U)} (hr : r ≠ 0)
    (hspan : Ideal.span {X.presheaf.germ U z hz r} = maximalIdeal (X.presheaf.stalk z)) :
    Scheme.ord (X.germToFunctionField U r) z = 1 := by
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hz r]
  exact ord_algebraMap_stalk_eq_one hz1 (germ_ne_zero hz hr) hspan

end

lemma fromSpec_mem_basicOpen_iff {U : X.Opens} (hU : IsAffineOpen U) (r : Γ(X, U))
    (y : Spec Γ(X, U)) : hU.fromSpec y ∈ X.basicOpen r ↔ r ∉ y.asIdeal := by
  change y ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen r ↔ _
  rw [hU.fromSpec_preimage_basicOpen]
  rfl

lemma coheight_fromSpec {U : X.Opens} (hU : IsAffineOpen U) (y : Spec Γ(X, U)) :
    coheight (hU.fromSpec y) = y.asIdeal.height := by
  rw [idealHeight_eq_coheight, ← coheight_eq_of_isOpenImmersion hU.fromSpec]

lemma fromSpec_specializes_iff {U : X.Opens} (hU : IsAffineOpen U) (y y' : Spec Γ(X, U)) :
    hU.fromSpec y ⤳ hU.fromSpec y' ↔ y.asIdeal ≤ y'.asIdeal := by
  rw [hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff]
  exact (PrimeSpectrum.le_iff_specializes y y').symm

lemma fromSpec_mem {U : X.Opens} (hU : IsAffineOpen U) (y : Spec Γ(X, U)) :
    hU.fromSpec y ∈ U := by
  show hU.fromSpec y ∈ (U : Set X)
  rw [← hU.range_fromSpec]; exact ⟨y, rfl⟩

lemma exists_fromSpec_eq {U : X.Opens} (hU : IsAffineOpen U) {z : X} (hz : z ∈ U) :
    ∃ y : Spec Γ(X, U), hU.fromSpec y = z := by
  rw [← SetLike.mem_coe, ← hU.range_fromSpec] at hz; exact hz

end RamanujanPetersson.JacDivisors


end

-- ===== S4.Def_RP_JacDivisors_J =====
section

/-!
# S4-JacDivisors J (O12b: algebraic Hartogs at points with factorial stalks)
* `maximalIdeal_stalk_fromSpec`: `m_{fromSpec y} = y.map germ`.
* `height_comap_germ`, `comap_germ_le`: contraction of primes of the stalk at `fromSpec y` to `Γ(X, U)`.
* `ord_stalk_chart`: for a prime `Q` of `O_x` (`x = fromSpec y`) contracting to `q` with `w = fromSpec q` of
  codimension one, `ord_w a > 0` for `0 ≠ a ∈ Q` and `ord_w a = 0` for `a ∉ Q`.
* `mem_range_algebraMap_stalk_of_ord_nonneg` (Hartogs): if `O_x` is a UFD and `ord_z f ≥ 0` at every
  codimension-one generalization `z` of `x`, then `f` lies in `O_x`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open AlgebraicGeometry CategoryTheory Order Topology IsLocalRing

universe u

variable {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency.types false in
/-- The maximal ideal of the stalk at `fromSpec y` is generated by the germs of the elements of `y`. -/
lemma maximalIdeal_stalk_fromSpec {U : X.Opens} (hU : IsAffineOpen U) (y : PrimeSpectrum Γ(X, U)) :
    maximalIdeal (X.presheaf.stalk (hU.fromSpec y)) =
      y.asIdeal.map (X.presheaf.germ U (hU.fromSpec y) (fromSpec_mem hU y)).hom := by
  let _ : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, fromSpec_mem hU y⟩
  have : y.asIdeal.IsPrime := y.isPrime
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) y.asIdeal :=
    hU.isLocalization_stalk' y (fromSpec_mem hU y)
  exact (IsLocalization.AtPrime.map_eq_maximalIdeal y.asIdeal
    (X.presheaf.stalk (hU.fromSpec y))).symm

set_option backward.isDefEq.respectTransparency.types false in
lemma height_comap_germ {U : X.Opens} (hU : IsAffineOpen U) (y : PrimeSpectrum Γ(X, U))
    (Q : Ideal (X.presheaf.stalk (hU.fromSpec y))) :
    (Q.comap (X.presheaf.germ U (hU.fromSpec y) (fromSpec_mem hU y)).hom).height = Q.height := by
  let _ : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, fromSpec_mem hU y⟩
  have : y.asIdeal.IsPrime := y.isPrime
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) y.asIdeal :=
    hU.isLocalization_stalk' y (fromSpec_mem hU y)
  exact IsLocalization.height_under y.asIdeal.primeCompl Q

set_option backward.isDefEq.respectTransparency.types false in
lemma comap_germ_le {U : X.Opens} (hU : IsAffineOpen U) (y : PrimeSpectrum Γ(X, U))
    (Q : Ideal (X.presheaf.stalk (hU.fromSpec y))) (hQ : Q ≠ ⊤) :
    Q.comap (X.presheaf.germ U (hU.fromSpec y) (fromSpec_mem hU y)).hom ≤ y.asIdeal := by
  let _ : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, fromSpec_mem hU y⟩
  have : y.asIdeal.IsPrime := y.isPrime
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) y.asIdeal :=
    hU.isLocalization_stalk' y (fromSpec_mem hU y)
  intro r hr
  by_contra h
  exact hQ (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_comap.mp hr)
    (IsLocalization.map_units (X.presheaf.stalk (hU.fromSpec y))
      (⟨r, h⟩ : y.asIdeal.primeCompl)))

section
variable [IsIntegral X] [IsLocallyNoetherian X]

set_option backward.isDefEq.respectTransparency.types false in
/-- Orders at a codimension-one point `w = fromSpec q` of elements of the stalk at `fromSpec y`, where
`q` is the contraction of a prime `Q` of that stalk. -/
lemma ord_stalk_chart {U : X.Opens} (hU : IsAffineOpen U) (y q : PrimeSpectrum Γ(X, U))
    (Q : Ideal (X.presheaf.stalk (hU.fromSpec y))) [hQ : Q.IsPrime]
    (hq : ∀ r : Γ(X, U), r ∈ q.asIdeal ↔ X.presheaf.germ U _ (fromSpec_mem hU y) r ∈ Q)
    (hw : coheight (hU.fromSpec q) = 1)
    {a : X.presheaf.stalk (hU.fromSpec y)} (ha : a ≠ 0) :
    (a ∈ Q → 0 < Scheme.ord (algebraMap _ X.functionField a) (hU.fromSpec q)) ∧
    (a ∉ Q → Scheme.ord (algebraMap _ X.functionField a) (hU.fromSpec q) = 0) := by
  let _ : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, fromSpec_mem hU y⟩
  have : y.asIdeal.IsPrime := y.isPrime
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) y.asIdeal :=
    hU.isLocalization_stalk' y (fromSpec_mem hU y)
  have : Nonempty U := ⟨⟨_, fromSpec_mem hU y⟩⟩
  have hg : ∀ t : Γ(X, U), algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) t =
      X.presheaf.germ U _ (fromSpec_mem hU y) t := fun _ => rfl
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq y.asIdeal.primeCompl a
  have hsu := IsLocalization.map_units (X.presheaf.stalk (hU.fromSpec y)) s
  have hsQ : algebraMap Γ(X, U) _ (s : Γ(X, U)) ∉ Q :=
    fun h => hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ h hsu)
  have hsq : (s : Γ(X, U)) ∉ q.asIdeal := fun h => hsQ ((hq _).mp h)
  have hr0 : r ≠ 0 := by rintro rfl; exact ha (IsLocalization.mk'_zero _)
  have hspec := IsLocalization.mk'_spec (X.presheaf.stalk (hU.fromSpec y)) r s
  have hK := congrArg (algebraMap (X.presheaf.stalk (hU.fromSpec y)) X.functionField) hspec
  rw [map_mul, hg, hg, Scheme.algebraMap_germ_eq_germToFunctionField X (fromSpec_mem hU y),
    Scheme.algebraMap_germ_eq_germToFunctionField X (fromSpec_mem hU y)] at hK
  have hA : algebraMap (X.presheaf.stalk (hU.fromSpec y)) X.functionField
      (IsLocalization.mk' _ r s) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ha
  have hS : X.germToFunctionField U (s : Γ(X, U)) ≠ 0 := by
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField X (fromSpec_mem hU y)]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
      (germ_ne_zero _ (fun h => hsq (h ▸ q.asIdeal.zero_mem)))
  have hmul := Scheme.ord_mul (x := hU.fromSpec q) hA hS
  rw [hK, ord_germ_eq_zero _ ((fromSpec_mem_basicOpen_iff hU _ q).mpr hsq), add_zero] at hmul
  have hiff : IsLocalization.mk' (X.presheaf.stalk (hU.fromSpec y)) r s ∈ Q ↔ r ∈ q.asIdeal := by
    rw [hq, ← hg, ← hspec]
    exact ⟨fun h => Q.mul_mem_right _ h, fun h => (hQ.mem_or_mem h).resolve_right hsQ⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← hmul]
    refine ord_germ_pos (fromSpec_mem hU q) hw hr0 ?_
    rw [fromSpec_mem_basicOpen_iff]
    exact not_not.mpr (hiff.mp h)
  · rw [← hmul]
    exact ord_germ_eq_zero _ ((fromSpec_mem_basicOpen_iff hU _ q).mpr (fun h' => h (hiff.mpr h')))

/-- Algebraic Hartogs: at a point with factorial stalk, a rational function with nonnegative order at
every codimension-one generalization is regular. -/
theorem mem_range_algebraMap_stalk_of_ord_nonneg (x : X)
    [UniqueFactorizationMonoid (X.presheaf.stalk x)] (f : X.functionField)
    (hf : ∀ z : X, z ⤳ x → coheight z = 1 → 0 ≤ Scheme.ord f z) :
    f ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  replace hU : IsAffineOpen U := hU
  obtain ⟨y, rfl⟩ := exists_fromSpec_eq hU hxU
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk (hU.fromSpec y)) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap (X.presheaf.stalk (hU.fromSpec y)) X.functionField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb0
  have key : f * algebraMap (X.presheaf.stalk (hU.fromSpec y)) X.functionField b =
      algebraMap (X.presheaf.stalk (hU.fromSpec y)) X.functionField a := by
    rw [← hab, div_mul_cancel₀ _ hbK]
  suffices H : ∀ b : X.presheaf.stalk (hU.fromSpec y), b ≠ 0 → ∀ a,
      f * algebraMap (X.presheaf.stalk (hU.fromSpec y)) X.functionField b =
        algebraMap (X.presheaf.stalk (hU.fromSpec y)) X.functionField a →
      f ∈ Set.range (algebraMap (X.presheaf.stalk (hU.fromSpec y)) X.functionField) from
    H b hb0 a key
  clear hab hb hbK key hb0 a b
  intro b
  induction b using WfDvdMonoid.induction_on_irreducible with
  | zero => intro h; exact absurd rfl h
  | unit u hu =>
    intro _ a key
    refine ⟨a * ↑hu.unit⁻¹, ?_⟩
    rw [map_mul, ← key, mul_assoc, ← map_mul, hu.mul_val_inv, map_one, mul_one]
  | mul b i hb hi ih =>
    intro _ a key
    by_cases hia : i ∣ a
    · obtain ⟨a', rfl⟩ := hia
      have hi0 : algebraMap (X.presheaf.stalk (hU.fromSpec y)) X.functionField i ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hi.ne_zero
      refine ih hb a' (mul_left_cancel₀ hi0 ?_)
      rw [map_mul, map_mul] at key
      rw [← key]; ring
    · exfalso
      have hip : Prime i := UniqueFactorizationMonoid.irreducible_iff_prime.mp hi
      have ha0 : a ≠ 0 := by rintro rfl; exact hia (dvd_zero i)
      have hQ : (Ideal.span {i}).IsPrime := Ideal.isPrime_span_singleton_of_prime hip
      let q : PrimeSpectrum Γ(X, U) :=
        ⟨(Ideal.span {i}).comap (X.presheaf.germ U _ (fromSpec_mem hU y)).hom, Ideal.IsPrime.comap _⟩
      have hq1 : coheight (hU.fromSpec q) = 1 := by
        refine (coheight_fromSpec hU q).trans ((height_comap_germ hU y _).trans ?_)
        exact
          (Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
            (mem_nonZeroDivisors_of_ne_zero hip.ne_zero) hip.not_isUnit)
      have hqy : hU.fromSpec q ⤳ hU.fromSpec y :=
        (fromSpec_specializes_iff hU q y).mpr (comap_germ_le hU y _ hQ.ne_top)
      have hfa : f ≠ 0 := by
        rintro rfl
        rw [zero_mul] at key
        exact ha0 (IsFractionRing.injective _ X.functionField (key.symm.trans (map_zero _).symm))
      have hib : i * b ≠ 0 := mul_ne_zero hi.ne_zero hb
      have h1 := ord_stalk_chart hU y q (Ideal.span {i}) (fun _ => Iff.rfl) hq1 ha0
      have h2 := ord_stalk_chart hU y q (Ideal.span {i}) (fun _ => Iff.rfl) hq1 hib
      have hmul := Scheme.ord_mul (x := hU.fromSpec q) hfa
        ((map_ne_zero_iff _ (IsFractionRing.injective _ X.functionField)).mpr hib)
      rw [key, h1.2 (fun h' => hia (Ideal.mem_span_singleton.mp h'))] at hmul
      have hpos := h2.1 (Ideal.mem_span_singleton.mpr (dvd_mul_right i b))
      have := hf _ hqy hq1
      omega

end

end RamanujanPetersson.JacDivisors


end

-- ===== S4.Def_RP_JacDivisors_K =====
section

/-!
# S4-JacDivisors K (O12a: Weil divisors are locally principal at factorial points)
* `ord_inv'`, `ord_zpow`, `ord_prod_zpow`: `ord` turns finite products of powers into sums.
* `exists_isOpen_eq_zero_of_specializes`: a cycle vanishing at every generalization of `x` vanishes near `x`.
* `exists_uniformizer`: for a codimension-one generalization `z` of `x = fromSpec y` with `O_x` a UFD there is
  a section `r` with `ord_w r = δ_{wz}` at every codimension-one generalization `w` of `x`.
* `exists_locally_principal`: a Weil divisor equals `div f` on a neighbourhood of a point with factorial stalk.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open AlgebraicGeometry CategoryTheory Order Topology IsLocalRing

universe u

variable {X : Scheme.{u}}

/-- A cycle vanishing at every generalization of `x` vanishes on an open neighbourhood of `x`. -/
lemma exists_isOpen_eq_zero_of_specializes (E : AlgebraicCycle X ℤ) (x : X)
    (hE : ∀ w, w ⤳ x → E w = 0) : ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∀ w ∈ V, E w = 0 := by
  obtain ⟨t, ht, hfin⟩ := E.supportLocallyFiniteWithinDomain' x (Set.mem_univ x)
  refine ⟨interior t \ ⋃ w ∈ t ∩ Function.support E, closure {w},
    isOpen_interior.sdiff (hfin.isClosed_biUnion fun _ _ => isClosed_closure),
    ⟨mem_interior_iff_mem_nhds.mpr ht, ?_⟩, ?_⟩
  · simp only [Set.mem_iUnion, not_exists]
    intro w hw hxw
    exact (Function.mem_support.mp hw.2) (hE w (specializes_iff_mem_closure.mpr hxw))
  · rintro w ⟨hwt, hw⟩
    by_contra h
    exact hw (Set.mem_biUnion (⟨interior_subset hwt, Function.mem_support.mpr h⟩ :
      w ∈ t ∩ Function.support E) (subset_closure rfl))

section
variable [IsIntegral X] [IsLocallyNoetherian X]

lemma ord_inv' {f : X.functionField} (hf : f ≠ 0) (z : X) :
    Scheme.ord f⁻¹ z = -Scheme.ord f z := by
  have h := Scheme.ord_mul (x := z) hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf, ord_one] at h
  omega

lemma ord_zpow {f : X.functionField} (hf : f ≠ 0) (z : X) (n : ℤ) :
    Scheme.ord (f ^ n) z = n * Scheme.ord f z := by
  refine Int.induction_on n ?_ ?_ ?_
  · rw [zpow_zero, ord_one, zero_mul]
  · intro k ih
    rw [zpow_add_one₀ hf, Scheme.ord_mul (zpow_ne_zero _ hf) hf, ih]; ring
  · intro k ih
    rw [zpow_sub_one₀ hf, Scheme.ord_mul (zpow_ne_zero _ hf) (inv_ne_zero hf), ih, ord_inv' hf]
    ring

lemma ord_prod_zpow {ι : Type*} (s : Finset ι) (g : ι → X.functionField) (n : ι → ℤ)
    (hg : ∀ i ∈ s, g i ≠ 0) (z : X) :
    Scheme.ord (∏ i ∈ s, g i ^ n i) z = ∑ i ∈ s, n i * Scheme.ord (g i) z := by
  classical
  revert hg
  refine Finset.induction_on s ?_ ?_
  · intro _; simp [ord_one]
  · intro a s ha ih hg
    have hga := hg a (Finset.mem_insert_self a s)
    have hs : ∀ i ∈ s, g i ≠ 0 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Scheme.ord_mul (zpow_ne_zero _ hga)
      (Finset.prod_ne_zero_iff.mpr fun i hi => zpow_ne_zero _ (hs i hi)), ord_zpow hga, ih hs]

lemma germToFunctionField_ne_zero {U : X.Opens} [Nonempty U] {r : Γ(X, U)} (hr : r ≠ 0) :
    X.germToFunctionField U r ≠ 0 := by
  obtain ⟨⟨z, hz⟩⟩ := ‹Nonempty U›
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hz]
  exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (germ_ne_zero hz hr)

set_option backward.isDefEq.respectTransparency.types false in
open Classical in
/-- A local equation of a prime divisor through a factorial point. -/
lemma exists_uniformizer {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U]
    (y : PrimeSpectrum Γ(X, U)) [UniqueFactorizationMonoid (X.presheaf.stalk (hU.fromSpec y))]
    (z : X) (hz : z ⤳ hU.fromSpec y) (hz1 : coheight z = 1) :
    ∃ r : Γ(X, U), r ≠ 0 ∧ ∀ w : X, w ⤳ hU.fromSpec y → coheight w = 1 →
      Scheme.ord (X.germToFunctionField U r) w = if w = z then 1 else 0 := by
  obtain ⟨q, rfl⟩ := exists_fromSpec_eq hU (hz.mem_open U.isOpen (fromSpec_mem hU y))
  have hqy : q.asIdeal ≤ y.asIdeal := (fromSpec_specializes_iff hU q y).mp hz
  let _ : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, fromSpec_mem hU y⟩
  have : y.asIdeal.IsPrime := y.isPrime
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) y.asIdeal :=
    hU.isLocalization_stalk' y (fromSpec_mem hU y)
  have hg : ∀ t : Γ(X, U), algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) t =
      X.presheaf.germ U _ (fromSpec_mem hU y) t := fun _ => rfl
  have hdisj : ∀ q' : PrimeSpectrum Γ(X, U), q'.asIdeal ≤ y.asIdeal →
      Disjoint (y.asIdeal.primeCompl : Set Γ(X, U)) q'.asIdeal :=
    fun q' h => Set.disjoint_left.mpr fun a ha ha' => ha (h ha')
  -- the prime `Q = q O_x` and its properties, for any codimension-one generalization `q'`
  have hloc : ∀ q' : PrimeSpectrum Γ(X, U), q'.asIdeal ≤ y.asIdeal →
      coheight (hU.fromSpec q') = 1 →
      (q'.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)))).IsPrime ∧
      (q'.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)))).comap
        (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y))) = q'.asIdeal ∧
      (q'.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)))).height = 1 := by
    intro q' hq' h1
    have hc := IsLocalization.under_map_of_isPrime_disjoint y.asIdeal.primeCompl
      (X.presheaf.stalk (hU.fromSpec y)) q'.isPrime (hdisj q' hq')
    refine ⟨IsLocalization.isPrime_of_isPrime_disjoint y.asIdeal.primeCompl _ _ q'.isPrime
      (hdisj q' hq'), hc, ?_⟩
    have h := height_comap_germ hU y
      (q'.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y))))
    have hc' : (q'.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)))).comap
        (X.presheaf.germ U _ (fromSpec_mem hU y)).hom = q'.asIdeal := hc
    rw [hc', ← coheight_fromSpec hU q', h1] at h
    exact h.symm
  obtain ⟨hQp, hQc, hQh⟩ := hloc q hqy hz1
  obtain ⟨π, hπ⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hQh).principal
  change _ = Ideal.span {π} at hπ
  obtain ⟨r, s, hrs⟩ := IsLocalization.exists_mk'_eq y.asIdeal.primeCompl π
  have hsu := IsLocalization.map_units (X.presheaf.stalk (hU.fromSpec y)) s
  have hspec := IsLocalization.mk'_spec (X.presheaf.stalk (hU.fromSpec y)) r s
  rw [hrs] at hspec
  have hπQ : π ∈ q.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y))) :=
    hπ ▸ Ideal.mem_span_singleton_self π
  have hrq : r ∈ q.asIdeal := by
    rw [← hQc, Ideal.mem_comap, ← hspec]; exact Ideal.mul_mem_right _ _ hπQ
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact Ideal.ne_bot_of_height_eq_one hQh (hπ.trans (Ideal.span_singleton_eq_bot.mpr rfl))
  have hr0 : r ≠ 0 := by rintro rfl; exact hπ0 (hrs.symm.trans (IsLocalization.mk'_zero _))
  refine ⟨r, hr0, fun w hw hw1 => ?_⟩
  split_ifs with hwz
  · subst hwz
    refine ord_germ_eq_one (fromSpec_mem hU q) hz1 hr0 (le_antisymm ?_ ?_)
    · rw [Ideal.span_singleton_le_iff_mem, maximalIdeal_stalk_fromSpec hU q]
      exact Ideal.mem_map_of_mem _ hrq
    · rw [maximalIdeal_stalk_fromSpec hU q, Ideal.map_le_iff_le_comap]
      intro c hc
      rw [Ideal.mem_comap, Ideal.mem_span_singleton']
      have hcQ := Ideal.mem_map_of_mem (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y))) hc
      rw [hπ, Ideal.mem_span_singleton'] at hcQ
      obtain ⟨d, hd⟩ := hcQ
      obtain ⟨r', s', rfl⟩ := IsLocalization.exists_mk'_eq y.asIdeal.primeCompl d
      rw [← hrs, ← IsLocalization.mk'_mul, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul, hg, hg] at hd
      have hR := germ_injective_of_isIntegral X _ (fromSpec_mem hU y) hd
      have hss : ((s' * s : y.asIdeal.primeCompl) : Γ(X, U)) ∉ q.asIdeal :=
        fun h => (s' * s).2 (hqy h)
      have hu := (Scheme.mem_basicOpen X _ _ (fromSpec_mem hU q)).mp
        ((fromSpec_mem_basicOpen_iff hU _ q).mpr hss)
      have e := congrArg (X.presheaf.germ U (hU.fromSpec q) (fromSpec_mem hU q)) hR
      rw [map_mul, map_mul] at e
      refine ⟨X.presheaf.germ U (hU.fromSpec q) (fromSpec_mem hU q) r' * ↑hu.unit⁻¹, ?_⟩
      calc X.presheaf.germ U (hU.fromSpec q) (fromSpec_mem hU q) r' * ↑hu.unit⁻¹ *
            X.presheaf.germ U (hU.fromSpec q) (fromSpec_mem hU q) r
          = X.presheaf.germ U (hU.fromSpec q) (fromSpec_mem hU q) c *
            (X.presheaf.germ U (hU.fromSpec q) (fromSpec_mem hU q) ↑(s' * s) * ↑hu.unit⁻¹) := by
            rw [← mul_assoc, ← e]; ring
        _ = X.presheaf.germ U (hU.fromSpec q) (fromSpec_mem hU q) c := by
            rw [hu.mul_val_inv, mul_one]
  · obtain ⟨q', rfl⟩ := exists_fromSpec_eq hU (hw.mem_open U.isOpen (fromSpec_mem hU y))
    have hq'y : q'.asIdeal ≤ y.asIdeal := (fromSpec_specializes_iff hU q' y).mp hw
    refine ord_germ_eq_zero r ((fromSpec_mem_basicOpen_iff hU r q').mpr fun hrq' => hwz ?_)
    obtain ⟨hQp', hQc', hQh'⟩ := hloc q' hq'y hw1
    have hsQ' : algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) (s : Γ(X, U)) ∉
        q'.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y))) :=
      fun h => hQp'.ne_top (Ideal.eq_top_of_isUnit_mem _ h hsu)
    have hπQ' : π ∈ q'.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y))) := by
      have h := Ideal.mem_map_of_mem (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y))) hrq'
      rw [← hspec] at h
      exact (hQp'.mem_or_mem h).resolve_right hsQ'
    have : (q.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)))).FiniteHeight :=
      Ideal.finiteHeight_iff_lt.mpr (Or.inr (lt_of_eq_of_lt hQh ENat.one_lt_top))
    have hle : q.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y))) ≤
        q'.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y))) := by
      rw [hπ, Ideal.span_singleton_le_iff_mem]; exact hπQ'
    have heq := Ideal.eq_of_le_of_height_le _ hle (le_of_eq (hQh'.trans hQh.symm))
    have : q' = q := PrimeSpectrum.ext (by rw [← hQc', ← heq, hQc])
    rw [this]

/-- Weil divisors are locally principal at points with factorial stalks. -/
theorem exists_locally_principal {D : AlgebraicCycle X ℤ} (hD : D ∈ weilDivisors X) (x : X)
    [UniqueFactorizationMonoid (X.presheaf.stalk x)] :
    ∃ f : X.functionField, f ≠ 0 ∧ ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∀ w ∈ V, D w = div X f w := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  replace hU : IsAffineOpen U := hU
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  obtain ⟨y, rfl⟩ := exists_fromSpec_eq hU hxU
  obtain ⟨t, ht, hfin⟩ := D.supportLocallyFiniteWithinDomain' (hU.fromSpec y) (Set.mem_univ _)
  have hZ : {z : X | z ⤳ hU.fromSpec y ∧ D z ≠ 0}.Finite :=
    hfin.subset fun z hz => ⟨mem_of_mem_nhds ((specializes_iff_nhds.mp hz.1) ht), hz.2⟩
  have hr : ∀ z ∈ hZ.toFinset, ∃ r : Γ(X, U), r ≠ 0 ∧ ∀ w : X, w ⤳ hU.fromSpec y →
      coheight w = 1 → Scheme.ord (X.germToFunctionField U r) w = if w = z then 1 else 0 := by
    intro z hz
    rw [Set.Finite.mem_toFinset] at hz
    exact exists_uniformizer hU y z hz.1 (hD z hz.2)
  choose! r hr0 hrord using hr
  have hne : ∀ z ∈ hZ.toFinset, X.germToFunctionField U (r z) ≠ 0 :=
    fun z hz => germToFunctionField_ne_zero (hr0 z hz)
  refine ⟨∏ z ∈ hZ.toFinset, X.germToFunctionField U (r z) ^ D z,
    Finset.prod_ne_zero_iff.mpr fun z hz => zpow_ne_zero _ (hne z hz), ?_⟩
  have hE : ∀ w, w ⤳ hU.fromSpec y →
      (D - div X (∏ z ∈ hZ.toFinset, X.germToFunctionField U (r z) ^ D z)) w = 0 := by
    intro w hw
    simp only [Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply, div_apply]
    rw [sub_eq_zero]
    by_cases hw1 : coheight w = 1
    · rw [ord_prod_zpow _ _ _ hne, Finset.sum_congr rfl fun z hz => by rw [hrord z hz w hw hw1]]
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq]
      split_ifs with hwZ
      · rfl
      · by_contra h
        exact hwZ ((Set.Finite.mem_toFinset hZ).mpr ⟨hw, h⟩)
    · rw [Scheme.ord_eq_zero_of_coheight_neq_one hw1]
      by_contra h
      exact hw1 (hD w h)
  obtain ⟨V, hV, hxV, hVE⟩ := exists_isOpen_eq_zero_of_specializes _ _ hE
  refine ⟨V, hV, hxV, fun w hw => ?_⟩
  have h := hVE w hw
  exact sub_eq_zero.mp h

end

end RamanujanPetersson.JacDivisors


end

-- ===== S4.Def_RP_IsogDegA_FF =====
section

/-!
# S4-IsogDegA, file FF: the function-field map of a dominant morphism and the degree (O2, O5)

For a dominant morphism `f : X ⟶ Y` of irreducible schemes, `f` sends the generic point to the
generic point, so the stalk map at the generic point gives `ffMap f : K(Y) ⟶ K(X)` (the pull-back
`f^*`). `degree f = [K(X) : f^* K(Y)]` for dominant `f` and `0` otherwise. It is multiplicative
on dominant pairs, `degree (𝟙 X) = 1`, and `degree = sepdeg * insepdeg` with `insepdeg = q ^ e`.
The algebra structure `ffAlgebra f` is never a global instance (endomorphisms have `X = Y`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory AlgebraicGeometry Topology

namespace RamanujanPetersson.IsogDegA

/-- A dominant morphism of irreducible schemes sends the generic point to the generic point. -/
theorem map_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X]
    [IrreducibleSpace Y] [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  have h := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at h
  exact h.eq (genericPoint_spec Y)

/-- The pull-back of rational functions `K(Y) ⟶ K(X)` along a dominant morphism. -/
noncomputable def ffMap {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X]
    [IrreducibleSpace Y] [IsDominant f] : Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes (specializes_of_eq (map_genericPoint f)) ≫
    f.stalkMap (genericPoint X)

theorem ffMap_id (X : Scheme.{u}) [IrreducibleSpace X] : ffMap (𝟙 X) = 𝟙 _ := by
  simp [ffMap]

theorem ffMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IrreducibleSpace X]
    [IrreducibleSpace Y] [IrreducibleSpace Z] [IsDominant f] [IsDominant g] :
    ffMap (f ≫ g) = ffMap g ≫ ffMap f := by
  simp only [ffMap, Category.assoc]
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_assoc, TopCat.Presheaf.stalkSpecializes_comp_assoc,
    Scheme.Hom.stalkMap_comp]
  rfl

/-- `K(X)` as a `K(Y)`-algebra through `f^*` (a `def`, never an instance). -/
noncomputable abbrev ffAlgebra {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X]
    [IrreducibleSpace Y] [IsDominant f] : Algebra Y.functionField X.functionField :=
  (ffMap f).hom.toAlgebra

/-- `[K(X) : f^* K(Y)]` for a dominant morphism. -/
noncomputable def degDom {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X]
    [IrreducibleSpace Y] [IsDominant f] : ℕ :=
  @Module.finrank Y.functionField X.functionField _ _ (ffAlgebra f).toModule

open Classical in
/-- The degree: `[K(X) : f^* K(Y)]` for dominant `f`, and `0` otherwise. -/
noncomputable def degree {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X]
    [IrreducibleSpace Y] : ℕ :=
  if _h : IsDominant f then degDom f else 0

theorem degree_of_isDominant {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X]
    [IrreducibleSpace Y] [IsDominant f] : degree f = degDom f := by
  rw [degree]
  exact dif_pos ‹IsDominant f›

theorem degree_of_not_isDominant {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X]
    [IrreducibleSpace Y] (hf : ¬ IsDominant f) : degree f = 0 := by
  rw [degree, dif_neg hf]

theorem degree_id (X : Scheme.{u}) [IsIntegral X] : degree (𝟙 X) = 1 := by
  rw [degree_of_isDominant, degDom]
  have h : (ffAlgebra (𝟙 X)) = Algebra.id _ := by
    apply Algebra.algebra_ext
    intro r
    simp [ffMap_id, RingHom.algebraMap_toAlgebra]
  rw [h]
  exact Module.finrank_self _

theorem isScalarTower_ffAlgebra {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IrreducibleSpace X] [IrreducibleSpace Y] [IrreducibleSpace Z] [IsDominant f]
    [IsDominant g] :
    letI := ffAlgebra f; letI := ffAlgebra g; letI := ffAlgebra (f ≫ g)
    IsScalarTower Z.functionField Y.functionField X.functionField := by
  letI := ffAlgebra f; letI := ffAlgebra g; letI := ffAlgebra (f ≫ g)
  apply IsScalarTower.of_algebraMap_eq'
  simp only [RingHom.algebraMap_toAlgebra, ffMap_comp, CommRingCat.hom_comp]

/-- Multiplicativity of the degree on dominant pairs. -/
theorem degree_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegral X]
    [IsIntegral Y] [IsIntegral Z] [IsDominant f] [IsDominant g] :
    degree (f ≫ g) = degree f * degree g := by
  rw [degree_of_isDominant, degree_of_isDominant, degree_of_isDominant, degDom, degDom, degDom,
    mul_comm]
  letI := ffAlgebra f; letI := ffAlgebra g; letI := ffAlgebra (f ≫ g)
  haveI := isScalarTower_ffAlgebra f g
  exact (Module.finrank_mul_finrank Z.functionField Y.functionField X.functionField).symm

end RamanujanPetersson.IsogDegA


end

-- ===== S4.Def_RP_JacDivisors_L =====
section

/-!
# S4-JacDivisors L (O13: pull-back of Weil divisors along dominant morphisms)
For a dominant morphism `φ : X ⟶ Y` of integral locally Noetherian schemes with `Y` locally factorial,
a Weil divisor `D` on `Y` is locally `div f` (file K); `φ^* D` is locally `div (φ^* f)`.
* `ffMap_algebraMap`: `φ^*` on `K(Y)` restricts to the stalk maps.
* `exists_isUnit_of_ord_eq_zero`: `div g = 0` near a factorial point makes `g` a unit of the stalk.
* `pullback φ D`, `pullback_eq_div_of`, `pullback_div`, `pullback_add`, `pullback_neg`, `pullback_sub`,
  `pullback_mem_weilDivisors`, `pullback_linEquiv`, `pullback_id`, `pullback_comp` (translates are the case of
  automorphisms).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open AlgebraicGeometry CategoryTheory Order Topology IsLocalRing RamanujanPetersson.IsogDegA

universe u

section
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (φ : X ⟶ Y) [IsDominant φ]

/-- The pull-back of rational functions restricts to the stalk maps. -/
lemma ffMap_algebraMap (x : X) (a : Y.presheaf.stalk (φ x)) :
    (ffMap φ).hom (algebraMap _ Y.functionField a) =
      algebraMap _ X.functionField (φ.stalkMap x a) := by
  have h : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have key : Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial :
      genericPoint Y ⤳ φ x) ≫ ffMap φ = φ.stalkMap x ≫ X.presheaf.stalkSpecializes h := by
    rw [← Scheme.Hom.stalkSpecializes_stalkMap, ffMap, TopCat.Presheaf.stalkSpecializes_comp_assoc]
  exact congrArg (fun g => g.hom a) key

lemma ffMap_ne_zero {f : Y.functionField} (hf : f ≠ 0) : (ffMap φ).hom f ≠ 0 :=
  (map_ne_zero_iff _ (ffMap φ).hom.injective).mpr hf

end

section
variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

lemma ord_algebraMap_isUnit (x : X) {u : X.presheaf.stalk x} (hu : IsUnit u) :
    Scheme.ord (algebraMap _ X.functionField u) x = 0 := by
  by_cases hx : coheight x = 1
  · have := ord_algebraMap_stalk hx (b := u) hu.ne_zero (n := 0) (by rw [Ring.ord_of_isUnit hu]; rfl)
    simpa using this
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hx _

/-- A rational function without zeros or poles near a factorial point is a unit of the stalk. -/
lemma exists_isUnit_of_ord_eq_zero (x : X) [UniqueFactorizationMonoid (X.presheaf.stalk x)]
    {g : X.functionField} (hg : g ≠ 0) (h : ∀ z : X, z ⤳ x → coheight z = 1 → Scheme.ord g z = 0) :
    ∃ u : X.presheaf.stalk x, IsUnit u ∧ algebraMap _ X.functionField u = g := by
  obtain ⟨a, ha⟩ := mem_range_algebraMap_stalk_of_ord_nonneg x g fun z hz h1 => (h z hz h1).ge
  obtain ⟨b, hb⟩ := mem_range_algebraMap_stalk_of_ord_nonneg x g⁻¹ fun z hz h1 => by
    rw [ord_inv' hg, h z hz h1]; rfl
  refine ⟨a, IsUnit.of_mul_eq_one b ?_, ha⟩
  apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  rw [map_mul, ha, hb, map_one, mul_inv_cancel₀ hg]

lemma ord_eq_of_div_eq {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0) {z : X}
    (h : div X f z = div X g z) : Scheme.ord (f / g) z = 0 := by
  have e := Scheme.ord_mul (x := z) hg (div_ne_zero hf hg)
  rw [show g * (f / g) = f by field_simp] at e
  rw [div_apply, div_apply] at h
  omega

end

section
variable {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y]
  [IsLocallyNoetherian Y] (φ : X ⟶ Y) [IsDominant φ]

/-- Two local equations of the same divisor at `φ x` have pull-backs of the same order at `x`. -/
lemma ord_ffMap_eq (x : X) [UniqueFactorizationMonoid (Y.presheaf.stalk (φ x))]
    {f g : Y.functionField} (hf : f ≠ 0) (hg : g ≠ 0) {V : Set Y} (hV : IsOpen V) (hx : φ x ∈ V)
    (hfg : ∀ w ∈ V, div Y f w = div Y g w) :
    Scheme.ord ((ffMap φ).hom f) x = Scheme.ord ((ffMap φ).hom g) x := by
  obtain ⟨u, hu, hug⟩ := exists_isUnit_of_ord_eq_zero (φ x) (div_ne_zero hf hg)
    fun z hz _ => ord_eq_of_div_eq hf hg (hfg z (hz.mem_open hV hx))
  have e : (ffMap φ).hom f = (ffMap φ).hom g * algebraMap _ X.functionField (φ.stalkMap x u) := by
    rw [← ffMap_algebraMap, hug, ← map_mul, show g * (f / g) = f by field_simp]
  rw [e, Scheme.ord_mul (ffMap_ne_zero φ hg), ord_algebraMap_isUnit x (hu.map _), add_zero]
  rw [← ffMap_algebraMap, hug]
  exact ffMap_ne_zero φ (div_ne_zero hf hg)

end

section
variable {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]

/-- `f` is a local equation of `D` at `y`. -/
def IsLocEq (D : AlgebraicCycle Y ℤ) (y : Y) (f : Y.functionField) : Prop :=
  f ≠ 0 ∧ ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ ∀ w ∈ V, D w = div Y f w

open Classical in
/-- A chosen local equation (junk `1` when there is none). -/
noncomputable def locEq (D : AlgebraicCycle Y ℤ) (y : Y) : Y.functionField :=
  if h : ∃ f, IsLocEq D y f then h.choose else 1

lemma isLocEq_locEq {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (y : Y)
    [UniqueFactorizationMonoid (Y.presheaf.stalk y)] : IsLocEq D y (locEq D y) := by
  have h : ∃ f, IsLocEq D y f := by
    obtain ⟨f, hf, V, hV⟩ := exists_locally_principal hD y
    exact ⟨f, hf, V, hV⟩
  rw [locEq, dif_pos h]
  exact h.choose_spec

end

section
variable {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y]
  [IsLocallyNoetherian Y] (φ : X ⟶ Y) [IsDominant φ]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)]

lemma ord_ffMap_locEq {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) {f : Y.functionField}
    (hf : f ≠ 0) {V : Set Y} (hV : IsOpen V) (hDV : ∀ w ∈ V, D w = div Y f w) {x : X} (hx : φ x ∈ V) :
    Scheme.ord ((ffMap φ).hom (locEq D (φ x))) x = Scheme.ord ((ffMap φ).hom f) x := by
  obtain ⟨hg, V', hV', hxV', hDV'⟩ := isLocEq_locEq hD (φ x)
  exact ord_ffMap_eq φ x hg hf (hV'.inter hV) ⟨hxV', hx⟩
    fun w hw => (hDV' w hw.1).symm.trans (hDV w hw.2)

lemma locallyFinite_pullback {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (x₀ : X) :
    ∃ t ∈ 𝓝 x₀, (t ∩ Function.support
      (fun x => Scheme.ord ((ffMap φ).hom (locEq D (φ x))) x)).Finite := by
  obtain ⟨hf, V, hV, hx₀, hDV⟩ := isLocEq_locEq hD (φ x₀)
  obtain ⟨t, ht, hfin⟩ := locallyFinite_ord ((ffMap φ).hom (locEq D (φ x₀))) x₀
  refine ⟨t ∩ φ ⁻¹' V, Filter.inter_mem ht ((hV.preimage φ.continuous).mem_nhds hx₀),
    hfin.subset ?_⟩
  rintro x ⟨⟨hxt, hxV⟩, hx⟩
  refine ⟨hxt, ?_⟩
  rw [Function.mem_support, ord_ffMap_locEq φ hD hf hV hDV hxV] at hx
  exact hx

open Classical in
/-- The pull-back `φ^* D` of a Weil divisor (junk `0` for cycles that are not Weil divisors). -/
noncomputable def pullback (D : AlgebraicCycle Y ℤ) : AlgebraicCycle X ℤ :=
  if hD : D ∈ weilDivisors Y then
    { toFun := fun x => Scheme.ord ((ffMap φ).hom (locEq D (φ x))) x
      supportWithinDomain' := Set.subset_univ _
      supportLocallyFiniteWithinDomain' := fun x _ => locallyFinite_pullback φ hD x }
  else 0

lemma pullback_apply {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (x : X) :
    pullback φ D x = Scheme.ord ((ffMap φ).hom (locEq D (φ x))) x := by
  rw [pullback, dif_pos hD]
  rfl

/-- Pull-back through any local equation. -/
lemma pullback_eq_div_of {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) {f : Y.functionField}
    (hf : f ≠ 0) {V : Set Y} (hV : IsOpen V) (hDV : ∀ w ∈ V, D w = div Y f w) {x : X} (hx : φ x ∈ V) :
    pullback φ D x = div X ((ffMap φ).hom f) x := by
  rw [pullback_apply φ hD, div_apply, ord_ffMap_locEq φ hD hf hV hDV hx]

lemma pullback_div {f : Y.functionField} (hf : f ≠ 0) :
    pullback φ (div Y f) = div X ((ffMap φ).hom f) := by
  ext x
  exact pullback_eq_div_of φ (div_mem_weilDivisors f) hf isOpen_univ (fun _ _ => rfl) trivial

lemma pullback_mem_weilDivisors (D : AlgebraicCycle Y ℤ) : pullback φ D ∈ weilDivisors X := by
  by_cases hD : D ∈ weilDivisors Y
  · intro x hx
    rw [pullback_apply φ hD] at hx
    by_contra h
    exact hx (Scheme.ord_eq_zero_of_coheight_neq_one h _)
  · rw [pullback, dif_neg hD]
    exact (weilDivisors X).zero_mem

lemma pullback_add {D E : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hE : E ∈ weilDivisors Y) :
    pullback φ (D + E) = pullback φ D + pullback φ E := by
  ext x
  obtain ⟨hf, V, hV, hxV, hDV⟩ := isLocEq_locEq hD (φ x)
  obtain ⟨hg, V', hV', hxV', hEV'⟩ := isLocEq_locEq hE (φ x)
  have hDE : ∀ w ∈ V ∩ V', (D + E) w = div Y (locEq D (φ x) * locEq E (φ x)) w := by
    intro w hw
    rw [div_mul hf hg, Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
      Function.locallyFinsuppWithin.coe_add, Pi.add_apply, hDV w hw.1, hEV' w hw.2]
  rw [Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
    pullback_eq_div_of φ ((weilDivisors Y).add_mem hD hE) (mul_ne_zero hf hg) (hV.inter hV') hDE
      ⟨hxV, hxV'⟩, pullback_eq_div_of φ hD hf hV hDV hxV, pullback_eq_div_of φ hE hg hV' hEV' hxV',
    map_mul, div_mul (ffMap_ne_zero φ hf) (ffMap_ne_zero φ hg),
    Function.locallyFinsuppWithin.coe_add, Pi.add_apply]

lemma pullback_zero : pullback φ (0 : AlgebraicCycle Y ℤ) = 0 := by
  have h := pullback_add φ (weilDivisors Y).zero_mem (weilDivisors Y).zero_mem
  rw [add_zero] at h
  exact (add_eq_left.mp h.symm)

lemma pullback_neg {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) :
    pullback φ (-D) = -pullback φ D := by
  have h := pullback_add φ hD ((weilDivisors Y).neg_mem hD)
  rw [add_neg_cancel, pullback_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

lemma pullback_sub {D E : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hE : E ∈ weilDivisors Y) :
    pullback φ (D - E) = pullback φ D - pullback φ E := by
  rw [sub_eq_add_neg, pullback_add φ hD ((weilDivisors Y).neg_mem hE), pullback_neg φ hE,
    sub_eq_add_neg]

end

section
variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y]
  [IsLocallyNoetherian Y] [IsIntegral Z] [IsLocallyNoetherian Z]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)]
  [∀ z : Z, UniqueFactorizationMonoid (Z.presheaf.stalk z)]

end

end RamanujanPetersson.JacDivisors


end

-- ===== S4.Def_RP_JacDivisors_M =====
section

/-!
# S4-JacDivisors M (O14, step E1: rational maps into proper targets are defined in codimension one)
* `fromSpecStalkOfMem_specializes`: the stalk maps of a partial map are compatible with specialization.
* `mem_domain_of_valuationRing`: if `Y ⟶ S` satisfies the existence part of the valuative criterion (e.g. it is
  proper) and is locally of finite type, an `S`-partial map from an integral `X` is defined at every point whose
  stalk is a valuation ring.
* `valuationRing_stalk`: a codimension-one point with factorial stalk has a discrete valuation ring as stalk.
* `mem_domain_of_coheight_eq_one`: hence rational maps from a locally factorial `X` to a proper `S`-scheme are
  defined at all codimension-one points.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open AlgebraicGeometry CategoryTheory Order Topology IsLocalRing

universe u

section
variable {X Y : Scheme.{u}}

lemma fromSpecStalkOfMem_specializes (f : X.PartialMap Y) {x y : X} (h : x ⤳ y) (hx : x ∈ f.domain)
    (hy : y ∈ f.domain) :
    Spec.map (X.presheaf.stalkSpecializes h) ≫ f.fromSpecStalkOfMem hy = f.fromSpecStalkOfMem hx := by
  have e : Spec.map (X.presheaf.stalkSpecializes h) ≫ f.domain.fromSpecStalkOfMem y hy =
      f.domain.fromSpecStalkOfMem x hx := by
    rw [← cancel_mono f.domain.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  rw [Scheme.PartialMap.fromSpecStalkOfMem, Scheme.PartialMap.fromSpecStalkOfMem, ← Category.assoc, e]

variable {S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)

/-- E1: a partial map into a target satisfying the valuative existence criterion is defined (as a rational map)
at every point with a valuation-ring stalk. -/
theorem mem_domain_of_valuationRing [IsIntegral X] [LocallyOfFiniteType sY]
    (hY : ValuativeCriterion.Existence sY) (f : X.PartialMap Y) (hf : f.hom ≫ sY = f.domain.ι ≫ sX)
    (x : X) [ValuationRing (X.presheaf.stalk x)] : x ∈ f.toRationalMap.domain := by
  have hgx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have hη : genericPoint X ∈ f.domain :=
    (genericPoint_spec X).specializes trivial |>.mem_open f.domain.2
      f.dense_domain.nonempty.choose_spec
  have hsq : f.fromSpecStalkOfMem hη ≫ sY =
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
        (X.fromSpecStalk x ≫ sX) := by
    rw [Scheme.PartialMap.fromSpecStalkOfMem, Category.assoc, hf, ← Category.assoc,
      Scheme.Opens.fromSpecStalkOfMem_ι, ← Category.assoc]
    change _ = (Spec.map (X.presheaf.stalkSpecializes hgx) ≫ X.fromSpecStalk x) ≫ sX
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hdom : IsDomain (X.presheaf.stalk x) := inferInstance
  let sq : ValuativeCommSq sY :=
    { R := X.presheaf.stalk x, commRing := inferInstance, domain := hdom,
      valuationRing := ‹_›, K := X.functionField, field := inferInstance,
      algebra := inferInstance, isFractionRing := inferInstance,
      i₁ := f.fromSpecStalkOfMem hη, i₂ := X.fromSpecStalk x ≫ sX, commSq := ⟨hsq⟩ }
  let L := (hY sq).exists_lift.some
  let l : Spec (X.presheaf.stalk x) ⟶ Y := L.l
  have hl : l ≫ sY = X.fromSpecStalk x ≫ sX := L.fac_right
  have hl' : Spec.map (X.presheaf.stalkSpecializes hgx) ≫ l = f.fromSpecStalkOfMem hη := L.fac_left
  let g := Scheme.PartialMap.ofFromSpecStalk sX sY l hl
  have hxg : x ∈ g.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk sX sY l hl
  have hηg : genericPoint X ∈ g.domain := hgx.mem_open g.domain.2 hxg
  have hgf : g.equiv f := by
    refine Scheme.PartialMap.equiv_of_fromSpecStalkOfMem_eq g f hηg hη ?_
    rw [← fromSpecStalkOfMem_specializes g hgx hηg hxg,
      Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk]
    exact hl'
  have hgf' : g.toRationalMap = f.toRationalMap := Scheme.PartialMap.toRationalMap_eq_iff.mpr hgf
  rw [← hgf']
  exact g.le_domain_toRationalMap hxg

end

section
variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- A codimension-one point with factorial stalk has a discrete valuation ring as stalk. -/
theorem isDiscreteValuationRing_stalk {z : X} (hz : coheight z = 1)
    [UniqueFactorizationMonoid (X.presheaf.stalk z)] :
    IsDiscreteValuationRing (X.presheaf.stalk z) := by
  have hdim : ringKrullDim (X.presheaf.stalk z) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, hz]; rfl
  have hnf : ¬ IsField (X.presheaf.stalk z) := fun h => by
    have := ringKrullDim_eq_zero_of_isField h
    rw [hdim] at this
    exact absurd this (by decide)
  have hm : (maximalIdeal (X.presheaf.stalk z)).height = 1 := by
    have h := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := X.presheaf.stalk z)
    rw [hdim] at h
    exact_mod_cast h
  exact ((IsDiscreteValuationRing.TFAE (X.presheaf.stalk z) hnf).out 0 4).mpr
    (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hm)

end

section
variable {X Y S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)

/-- E1 at codimension-one points of a locally factorial `X`. -/
theorem mem_domain_of_coheight_eq_one [IsIntegral X] [IsLocallyNoetherian X] [LocallyOfFiniteType sY]
    (hY : ValuativeCriterion.Existence sY) (f : X.PartialMap Y) (hf : f.hom ≫ sY = f.domain.ι ≫ sX)
    {z : X} (hz : coheight z = 1) [UniqueFactorizationMonoid (X.presheaf.stalk z)] :
    z ∈ f.toRationalMap.domain := by
  have := isDiscreteValuationRing_stalk hz
  exact mem_domain_of_valuationRing sX sY hY f hf z

/-- The generic point is in the domain. -/
lemma genericPoint_mem_domain [IrreducibleSpace X] (f : X.PartialMap Y) :
    genericPoint X ∈ f.toRationalMap.domain :=
  f.le_domain_toRationalMap ((genericPoint_spec X).specializes trivial |>.mem_open f.domain.2
    f.dense_domain.nonempty.choose_spec)

end

end RamanujanPetersson.JacDivisors


end

-- ===== S4.Def_RP_JacDivisors_O =====
section

/-!
# S4-JacDivisors O (O14, steps E1' and E4-E5: where a rational map is undefined, a codimension-one divisor is)
* `exists_specMap_of_range`: a morphism `Spec R ⟶ Y` with image in an affine open `W` factors through `Spec Γ(Y, W)`.
* `specMap_cancel`: `Spec K ⟶ Spec R` is an epimorphism onto affine targets when `R ⟶ K` is injective.
* `mem_domain_of_lift`: a lift `Spec 𝒪_x ⟶ Y` of the generic germ of a partial map puts `x` in the domain.
* `mem_domain_of_range` (E4): over an affine base, if the generic ring map `Γ(Y, W) ⟶ K(X)` of a partial map lands in
  `𝒪_x`, the rational map is defined at `x`.
* `exists_not_mem_of_not_mem_domain` (E5, Hartogs): at a factorial point `p` outside the domain there is a
  codimension-one generalization `ζ` of `p` that the map does not send into `W`.
* `mem_domain_of_coheight_le_one` (E1'): into a proper target, points of codimension at most one are in the domain.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open AlgebraicGeometry CategoryTheory Order Topology IsLocalRing

universe u

/-- O-a: a morphism from an affine scheme whose image lies in an affine open factors through it. -/
lemma exists_specMap_of_range {Y : Scheme.{u}} {W : Y.Opens} (hW : IsAffineOpen W) {R : CommRingCat.{u}}
    (t : Spec R ⟶ Y) (ht : Set.range t ⊆ (W : Set Y)) :
    ∃ θ : Γ(Y, W) ⟶ R, t = Spec.map θ ≫ hW.fromSpec := by
  refine ⟨Spec.preimage (IsOpenImmersion.lift hW.fromSpec t (by rw [hW.range_fromSpec]; exact ht)), ?_⟩
  rw [Spec.map_preimage, IsOpenImmersion.lift_fac]

lemma specMap_comp_fromSpec_inj {Y : Scheme.{u}} {W : Y.Opens} (hW : IsAffineOpen W) {R : CommRingCat.{u}}
    {θ₁ θ₂ : Γ(Y, W) ⟶ R} (h : Spec.map θ₁ ≫ hW.fromSpec = Spec.map θ₂ ≫ hW.fromSpec) : θ₁ = θ₂ :=
  Spec.map_injective ((cancel_mono hW.fromSpec).mp h)

/-- O-b: cancellation of `Spec K ⟶ Spec R` (for `R ⟶ K` injective) against maps into an affine scheme. -/
lemma specMap_cancel {A R K : CommRingCat.{u}} (ι : R ⟶ K) (hι : Function.Injective ι)
    {g₁ g₂ : Spec R ⟶ Spec A} (h : Spec.map ι ≫ g₁ = Spec.map ι ≫ g₂) : g₁ = g₂ := by
  obtain ⟨a₁, rfl⟩ : ∃ a, Spec.map a = g₁ := ⟨_, Spec.map_preimage g₁⟩
  obtain ⟨a₂, rfl⟩ : ∃ a, Spec.map a = g₂ := ⟨_, Spec.map_preimage g₂⟩
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at h
  congr 1
  ext a
  apply hι
  have := ConcreteCategory.congr_hom h a
  simpa only [CommRingCat.comp_apply] using this

section
variable {X Y : Scheme.{u}}

/-- The stalk map of a partial map at a point sent into an affine open `W` factors through `Spec Γ(Y, W)`. -/
lemma exists_specMap_fromSpecStalkOfMem (f : X.PartialMap Y) {W : Y.Opens} (hW : IsAffineOpen W) {z : X}
    (hz : z ∈ f.domain) (hzW : f.hom ⟨z, hz⟩ ∈ W) :
    ∃ θ : Γ(Y, W) ⟶ X.presheaf.stalk z, f.fromSpecStalkOfMem hz = Spec.map θ ≫ hW.fromSpec := by
  refine exists_specMap_of_range hW _ ?_
  have hcl' : f.domain.fromSpecStalkOfMem z hz (closedPoint (X.presheaf.stalk z)) = ⟨z, hz⟩ := by
    apply Subtype.ext
    change (f.domain.fromSpecStalkOfMem z hz ≫ f.domain.ι) (closedPoint (X.presheaf.stalk z)) = z
    rw [Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.fromSpecStalk_closedPoint]
  have hcl : f.fromSpecStalkOfMem hz (closedPoint (X.presheaf.stalk z)) = f.hom ⟨z, hz⟩ := by
    rw [← hcl']
    rfl
  rintro _ ⟨q, rfl⟩
  exact ((specializes_closedPoint q).map (f.fromSpecStalkOfMem hz).continuous).mem_open W.isOpen
    (hcl ▸ hzW)

/-- O-d: for `z` sent into `W`, the generic ring map `Γ(Y, W) ⟶ K(X)` lands in `𝒪_z`. -/
lemma mem_range_of_mem [IsIntegral X] (f : X.PartialMap Y) (hη : genericPoint X ∈ f.domain)
    {W : Y.Opens} (hW : IsAffineOpen W) (θ : Γ(Y, W) ⟶ X.presheaf.stalk (genericPoint X))
    (hθ : f.fromSpecStalkOfMem hη = Spec.map θ ≫ hW.fromSpec) {z : X} (hz : z ∈ f.domain)
    (hzW : f.hom ⟨z, hz⟩ ∈ W) (a : Γ(Y, W)) :
    θ a ∈ Set.range (algebraMap (X.presheaf.stalk z) X.functionField) := by
  have hgz : genericPoint X ⤳ z := (genericPoint_spec X).specializes trivial
  obtain ⟨θz, hθz⟩ := exists_specMap_fromSpecStalkOfMem f hW hz hzW
  have h1 := fromSpecStalkOfMem_specializes f hgz hη hz
  rw [hθz, hθ, ← Category.assoc, ← Spec.map_comp] at h1
  have h2 : θz ≫ X.presheaf.stalkSpecializes hgz = θ := specMap_comp_fromSpec_inj hW h1
  exact ⟨θz a, by rw [← h2]; rfl⟩

/-- O-e: elements of the stalk at a codimension-one point have nonnegative order there. -/
lemma ord_algebraMap_nonneg [IsIntegral X] [IsLocallyNoetherian X] {z : X} (hz : coheight z = 1)
    (b : X.presheaf.stalk z) :
    0 ≤ Scheme.ord (algebraMap (X.presheaf.stalk z) X.functionField b) z := by
  by_cases hb : b = 0
  · simp [hb]
  have : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
    (Ring.ord_ne_top (R := X.presheaf.stalk z) (mem_nonZeroDivisors_of_ne_zero hb))
  rw [ord_algebraMap_stalk hz hb hn.symm]
  exact_mod_cast Nat.zero_le n

variable {S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)

/-- A lift `Spec 𝒪_x ⟶ Y` of the generic germ of `f` puts `x` in the domain of `f`. -/
lemma mem_domain_of_lift [IsIntegral X] [LocallyOfFiniteType sY] (f : X.PartialMap Y)
    (hη : genericPoint X ∈ f.domain) (x : X) (l : Spec (X.presheaf.stalk x) ⟶ Y)
    (hl : l ≫ sY = X.fromSpecStalk x ≫ sX)
    (hl' : Spec.map (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)) ≫ l =
      f.fromSpecStalkOfMem hη) : x ∈ f.toRationalMap.domain := by
  have hgx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  let g := Scheme.PartialMap.ofFromSpecStalk sX sY l hl
  have hxg : x ∈ g.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk sX sY l hl
  have hηg : genericPoint X ∈ g.domain := hgx.mem_open g.domain.2 hxg
  have hgf : g.equiv f := by
    refine Scheme.PartialMap.equiv_of_fromSpecStalkOfMem_eq g f hηg hη ?_
    rw [← fromSpecStalkOfMem_specializes g hgx hηg hxg,
      Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk]
    exact hl'
  have hgf' : g.toRationalMap = f.toRationalMap := Scheme.PartialMap.toRationalMap_eq_iff.mpr hgf
  rw [← hgf']
  exact g.le_domain_toRationalMap hxg

/-- E1': into a target satisfying the valuative existence criterion, a partial map from a locally factorial
integral `X` is defined at every point of codimension at most one. -/
theorem mem_domain_of_coheight_le_one [IsIntegral X] [IsLocallyNoetherian X] [LocallyOfFiniteType sY]
    (hY : ValuativeCriterion.Existence sY) (f : X.PartialMap Y) (hf : f.hom ≫ sY = f.domain.ι ≫ sX)
    {z : X} (hz : coheight z ≤ 1) [UniqueFactorizationMonoid (X.presheaf.stalk z)] :
    z ∈ f.toRationalMap.domain := by
  rcases lt_or_eq_of_le hz with h0 | h1
  · have hmax : IsMax z := Order.coheight_eq_zero.mp (Order.lt_one_iff.mp h0)
    have hgz : genericPoint X ⤳ z := (genericPoint_spec X).specializes trivial
    have hzg : z ⤳ genericPoint X := hmax (show z ≤ genericPoint X from hgz)
    rw [(inseparable_iff_specializes_and.mpr ⟨hzg, hgz⟩).eq]
    exact genericPoint_mem_domain f
  · exact mem_domain_of_coheight_eq_one sX sY hY f hf h1

end

section
variable {X Y : Scheme.{u}} {A : CommRingCat.{u}} (sX : X ⟶ Spec A) (sY : Y ⟶ Spec A)

/-- E4: over an affine base, if the generic ring map `θ : Γ(Y, W) ⟶ K(X)` of `f` lands in `𝒪_x`, the rational
map of `f` is defined at `x`. -/
theorem mem_domain_of_range [IsIntegral X] [LocallyOfFiniteType sY] (f : X.PartialMap Y)
    (hf : f.hom ≫ sY = f.domain.ι ≫ sX) (hη : genericPoint X ∈ f.domain) {W : Y.Opens}
    (hW : IsAffineOpen W) (θ : Γ(Y, W) ⟶ X.presheaf.stalk (genericPoint X))
    (hθ : f.fromSpecStalkOfMem hη = Spec.map θ ≫ hW.fromSpec) (x : X)
    (hx : ∀ a, θ a ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField)) :
    x ∈ f.toRationalMap.domain := by
  have hgx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have hinj : Function.Injective (algebraMap (X.presheaf.stalk x) X.functionField) :=
    IsFractionRing.injective _ _
  choose σ hσ using hx
  let σ' : Γ(Y, W) →+* X.presheaf.stalk x :=
    { toFun := σ
      map_one' := hinj (by rw [hσ, map_one, map_one])
      map_mul' := fun a b => hinj (by rw [hσ, map_mul, map_mul, hσ, hσ])
      map_zero' := hinj (by rw [hσ, map_zero, map_zero])
      map_add' := fun a b => hinj (by rw [hσ, map_add, map_add, hσ, hσ]) }
  have hcomp : CommRingCat.ofHom σ' ≫
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) = θ := by
    ext a
    exact hσ a
  let l : Spec (X.presheaf.stalk x) ⟶ Y := Spec.map (CommRingCat.ofHom σ') ≫ hW.fromSpec
  have hl' : Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫ l =
      f.fromSpecStalkOfMem hη := by
    rw [hθ, ← hcomp, Spec.map_comp, Category.assoc]
    rfl
  have hsq : f.fromSpecStalkOfMem hη ≫ sY =
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
        (X.fromSpecStalk x ≫ sX) := by
    rw [Scheme.PartialMap.fromSpecStalkOfMem, Category.assoc, hf, ← Category.assoc,
      Scheme.Opens.fromSpecStalkOfMem_ι, ← Category.assoc]
    change _ = (Spec.map (X.presheaf.stalkSpecializes hgx) ≫ X.fromSpecStalk x) ≫ sX
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hl : l ≫ sY = X.fromSpecStalk x ≫ sX := by
    refine specMap_cancel (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) hinj ?_
    rw [← Category.assoc, hl', hsq]
  exact mem_domain_of_lift sX sY f hη x l hl hl'

/-- E5 (Hartogs): if `f` sends some point into the affine open `W` but is undefined at a factorial point `p`,
then some codimension-one generalization `ζ` of `p` is not sent into `W`. -/
theorem exists_not_mem_of_not_mem_domain [IsIntegral X] [IsLocallyNoetherian X] [LocallyOfFiniteType sY]
    (f : X.PartialMap Y) (hf : f.hom ≫ sY = f.domain.ι ≫ sX) {W : Y.Opens} (hW : IsAffineOpen W)
    {z₀ : X} (hz₀ : z₀ ∈ f.domain) (hz₀W : f.hom ⟨z₀, hz₀⟩ ∈ W)
    {p : X} [UniqueFactorizationMonoid (X.presheaf.stalk p)] (hp : p ∉ f.toRationalMap.domain) :
    ∃ ζ : X, ζ ⤳ p ∧ coheight ζ = 1 ∧ ∀ hζ : ζ ∈ f.domain, f.hom ⟨ζ, hζ⟩ ∉ W := by
  have hgz₀ : genericPoint X ⤳ z₀ := (genericPoint_spec X).specializes trivial
  have hη : genericPoint X ∈ f.domain := hgz₀.mem_open f.domain.2 hz₀
  obtain ⟨θ₀, hθ₀⟩ := exists_specMap_fromSpecStalkOfMem f hW hz₀ hz₀W
  let θ : Γ(Y, W) ⟶ X.presheaf.stalk (genericPoint X) := θ₀ ≫ X.presheaf.stalkSpecializes hgz₀
  have hθ : f.fromSpecStalkOfMem hη = Spec.map θ ≫ hW.fromSpec := by
    rw [← fromSpecStalkOfMem_specializes f hgz₀ hη hz₀, hθ₀, Spec.map_comp, Category.assoc]
  have hnot : ¬ ∀ a, θ a ∈ Set.range (algebraMap (X.presheaf.stalk p) X.functionField) :=
    fun h => hp (mem_domain_of_range sX sY f hf hη hW θ hθ p h)
  push Not at hnot
  obtain ⟨a, ha⟩ := hnot
  have hneg : ¬ ∀ z : X, z ⤳ p → coheight z = 1 → 0 ≤ Scheme.ord (θ a) z :=
    fun h => ha (mem_range_algebraMap_stalk_of_ord_nonneg p (θ a) h)
  push Not at hneg
  obtain ⟨ζ, hζp, hζ1, hlt⟩ := hneg
  refine ⟨ζ, hζp, hζ1, fun hζ hζW => ?_⟩
  obtain ⟨b, hb⟩ := mem_range_of_mem f hη hW θ hθ hζ hζW a
  rw [← hb] at hlt
  exact absurd (ord_algebraMap_nonneg hζ1 b) (not_le.mpr hlt)

end

end RamanujanPetersson.JacDivisors


end

-- ===== S4.Def_RP_ThetaSquare_CPull =====
section

/-!
# S4-ThetaSquare, file CPull: pulling Weil divisors back along non-dominant morphisms (T4a)

For `f : C ⟶ Y` between integral locally Noetherian schemes, `Y` locally factorial, and a Weil divisor `D` on `Y`
whose support avoids `ξ = f (η_C)` (`Avoid f D`), the local equations of `D` are units at `ξ`, so they pull back to
`K(C)` through the stalk map at `η_C`; `cpull f D` is the cycle `x ↦ ord_x (f^* (locEq D (f x)))`.
* `fpull f`: rational functions regular at `ξ` pulled back to `K(C)`; `fpull_algebraMap_at`: on `O_{Y, f x}` it is
  the stalk map at `x`.
* `cpull`, `cpull_apply`, `cpull_eq_of` (any local equation), `cpull_add`, `cpull_div`, `cpull_eq_zero_of` (off the
  support), `cpull_nonneg` and `cpull_pos` (effective divisors), `cpull_comp` (`f ≫ φ` with `φ` dominant).
-/

set_option autoImplicit false

namespace RamanujanPetersson.ThetaSquare

open AlgebraicGeometry CategoryTheory Order Topology IsLocalRing RamanujanPetersson.JacDivisors
  RamanujanPetersson.IsogDegA

universe u

section
variable {X : Scheme.{u}} [IsIntegral X]

/-- The algebra map of a stalk factors through any generization. -/
lemma algebraMap_stalkSpecializes {z y : X} (h : z ⤳ y) (a : X.presheaf.stalk y) :
    algebraMap _ X.functionField ((X.presheaf.stalkSpecializes h).hom a) =
      algebraMap _ X.functionField a :=
  congrArg (fun g => g.hom a) (TopCat.Presheaf.stalkSpecializes_comp X.presheaf
    ((genericPoint_spec X).specializes trivial : genericPoint X ⤳ z) h)

end

section
variable {C Y : Scheme.{u}} [IsIntegral C] [IsIntegral Y] (f : C ⟶ Y)

/-- `ξ = f (η_C)` specializes to every `f x`. -/
lemma xi_specializes (x : C) : f (genericPoint C) ⤳ f x :=
  f.base.hom.map_specializes ((genericPoint_spec C).specializes trivial)

open Classical in
/-- Pull-back to `K(C)` of the rational functions that are regular at `ξ = f (η_C)` (junk `0` otherwise). -/
noncomputable def fpull (g : Y.functionField) : C.functionField :=
  if h : ∃ u : Y.presheaf.stalk (f (genericPoint C)), algebraMap _ Y.functionField u = g
  then (f.stalkMap (genericPoint C)).hom h.choose else 0

lemma fpull_algebraMap (u : Y.presheaf.stalk (f (genericPoint C))) :
    fpull f (algebraMap _ Y.functionField u) = (f.stalkMap (genericPoint C)).hom u := by
  have h : ∃ u' : Y.presheaf.stalk (f (genericPoint C)),
      algebraMap _ Y.functionField u' = algebraMap _ Y.functionField u := ⟨u, rfl⟩
  rw [fpull, dif_pos h]
  congr 1
  exact IsFractionRing.injective _ Y.functionField h.choose_spec

lemma fpull_one : fpull f 1 = 1 := by
  rw [← map_one (algebraMap (Y.presheaf.stalk (f (genericPoint C))) Y.functionField), fpull_algebraMap,
    map_one]

/-- On the stalk at `f x`, `fpull` is the stalk map at `x`. -/
lemma fpull_algebraMap_at (x : C) (a : Y.presheaf.stalk (f x)) :
    fpull f (algebraMap _ Y.functionField a) =
      algebraMap _ C.functionField ((f.stalkMap x).hom a) := by
  rw [← algebraMap_stalkSpecializes (xi_specializes f x) a, fpull_algebraMap]
  exact f.stalkSpecializes_stalkMap_apply (genericPoint C) x
    ((genericPoint_spec C).specializes trivial) a

lemma fpull_mul (u v : Y.presheaf.stalk (f (genericPoint C))) :
    fpull f (algebraMap _ Y.functionField u * algebraMap _ Y.functionField v) =
      fpull f (algebraMap _ Y.functionField u) * fpull f (algebraMap _ Y.functionField v) := by
  rw [← map_mul, fpull_algebraMap, fpull_algebraMap, fpull_algebraMap, map_mul]

lemma fpull_mul_at (x : C) (u : Y.presheaf.stalk (f (genericPoint C))) (w : Y.presheaf.stalk (f x)) :
    fpull f (algebraMap _ Y.functionField u * algebraMap _ Y.functionField w) =
      fpull f (algebraMap _ Y.functionField u) * algebraMap _ C.functionField ((f.stalkMap x).hom w) := by
  rw [← algebraMap_stalkSpecializes (xi_specializes f x) w, fpull_mul, ← fpull_algebraMap_at f x w,
    algebraMap_stalkSpecializes]

lemma fpull_ne_zero {u : Y.presheaf.stalk (f (genericPoint C))} (hu : IsUnit u) :
    fpull f (algebraMap _ Y.functionField u) ≠ 0 := by
  rw [fpull_algebraMap]
  exact (hu.map _).ne_zero

end

section
variable {C Y : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsIntegral Y] [IsLocallyNoetherian Y]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)] (f : C ⟶ Y)

/-- The support of `D` avoids `ξ = f (η_C)`. -/
def Avoid (D : AlgebraicCycle Y ℤ) : Prop :=
  ∃ V : Set Y, IsOpen V ∧ f (genericPoint C) ∈ V ∧ ∀ w ∈ V, D w = 0

lemma avoid_add {D E : AlgebraicCycle Y ℤ} (hD : Avoid f D) (hE : Avoid f E) : Avoid f (D + E) := by
  obtain ⟨V, hV, h1, h2⟩ := hD
  obtain ⟨V', hV', h1', h2'⟩ := hE
  refine ⟨V ∩ V', hV.inter hV', ⟨h1, h1'⟩, fun w hw => ?_⟩
  rw [Function.locallyFinsuppWithin.coe_add, Pi.add_apply, h2 w hw.1, h2' w hw.2, add_zero]

/-- A local equation of `D` at `f x` is a unit at `ξ`. -/
lemma exists_unit_of_isLocEq {D : AlgebraicCycle Y ℤ} (hA : Avoid f D) {x : C} {g : Y.functionField}
    (hg : IsLocEq D (f x) g) :
    ∃ u : Y.presheaf.stalk (f (genericPoint C)), IsUnit u ∧ algebraMap _ Y.functionField u = g := by
  obtain ⟨hg0, V, hV, hxV, hDV⟩ := hg
  obtain ⟨V', hV', hξ, hD0⟩ := hA
  have hξV : f (genericPoint C) ∈ V := (xi_specializes f x).mem_open hV hxV
  refine exists_isUnit_of_ord_eq_zero _ hg0 fun z hz _ => ?_
  show div Y g z = 0
  rw [← hDV z (hz.mem_open hV hξV)]
  exact hD0 z (hz.mem_open hV' hξ)

/-- Two local equations at `f x` give the same order at `x`. -/
lemma ord_fpull_eq_of {D : AlgebraicCycle Y ℤ} (hA : Avoid f D) {x : C} {g h : Y.functionField}
    (hg : IsLocEq D (f x) g) (hh : IsLocEq D (f x) h) :
    Scheme.ord (fpull f g) x = Scheme.ord (fpull f h) x := by
  obtain ⟨uh, huh, rfl⟩ := exists_unit_of_isLocEq f hA hh
  obtain ⟨hg0, V1, hV1, hx1, hD1⟩ := hg
  obtain ⟨hh0, V2, hV2, hx2, hD2⟩ := hh
  obtain ⟨w, hw, hwr⟩ := exists_isUnit_of_ord_eq_zero (f x) (div_ne_zero hg0 hh0)
    fun z hz _ => ord_eq_of_div_eq hg0 hh0
      ((hD1 z (hz.mem_open hV1 hx1)).symm.trans (hD2 z (hz.mem_open hV2 hx2)))
  have e : g = algebraMap _ Y.functionField uh * algebraMap _ Y.functionField w := by
    rw [hwr]
    field_simp
  rw [e, fpull_mul_at, Scheme.ord_mul (fpull_ne_zero f huh), ord_algebraMap_isUnit x (hw.map _), add_zero]
  exact (map_ne_zero_iff _ (IsFractionRing.injective _ C.functionField)).mpr (hw.map _).ne_zero

lemma ord_fpull_locEq {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hA : Avoid f D) {x : C}
    {g : Y.functionField} (hg : IsLocEq D (f x) g) :
    Scheme.ord (fpull f (locEq D (f x))) x = Scheme.ord (fpull f g) x :=
  ord_fpull_eq_of f hA (isLocEq_locEq hD (f x)) hg

lemma locallyFinite_cpull {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hA : Avoid f D) (x₀ : C) :
    ∃ t ∈ 𝓝 x₀, (t ∩ Function.support
      (fun x => Scheme.ord (fpull f (locEq D (f x))) x)).Finite := by
  obtain ⟨hf, V, hV, hx₀, hDV⟩ := isLocEq_locEq hD (f x₀)
  obtain ⟨t, ht, hfin⟩ := locallyFinite_ord (fpull f (locEq D (f x₀))) x₀
  refine ⟨t ∩ f ⁻¹' V, Filter.inter_mem ht ((hV.preimage f.continuous).mem_nhds hx₀),
    hfin.subset ?_⟩
  rintro x ⟨⟨hxt, hxV⟩, hx⟩
  refine ⟨hxt, ?_⟩
  rw [Function.mem_support, ord_fpull_locEq f hD hA ⟨hf, V, hV, hxV, hDV⟩] at hx
  exact hx

open Classical in
/-- The pull-back `f^* D` of a Weil divisor whose support avoids `f (η_C)` (junk `0` otherwise). -/
noncomputable def cpull (D : AlgebraicCycle Y ℤ) : AlgebraicCycle C ℤ :=
  if hD : D ∈ weilDivisors Y ∧ Avoid f D then
    { toFun := fun x => Scheme.ord (fpull f (locEq D (f x))) x
      supportWithinDomain' := Set.subset_univ _
      supportLocallyFiniteWithinDomain' := fun x _ => locallyFinite_cpull f hD.1 hD.2 x }
  else 0

lemma cpull_apply {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hA : Avoid f D) (x : C) :
    cpull f D x = Scheme.ord (fpull f (locEq D (f x))) x := by
  rw [cpull, dif_pos ⟨hD, hA⟩]
  rfl

/-- `cpull` through any local equation. -/
lemma cpull_eq_of {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hA : Avoid f D) {x : C}
    {g : Y.functionField} (hg : IsLocEq D (f x) g) : cpull f D x = Scheme.ord (fpull f g) x := by
  rw [cpull_apply f hD hA, ord_fpull_locEq f hD hA hg]

lemma cpull_eq_zero_of {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hA : Avoid f D) {x : C}
    {V : Set Y} (hV : IsOpen V) (hxV : f x ∈ V) (h0 : ∀ w ∈ V, D w = 0) : cpull f D x = 0 := by
  rw [cpull_eq_of f hD hA (g := 1) ⟨one_ne_zero, V, hV, hxV, fun w hw => by
    rw [h0 w hw, JacDivisors.div_one]; rfl⟩, fpull_one]
  change div C 1 x = 0
  rw [JacDivisors.div_one]
  rfl

lemma cpull_add {D E : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hE : E ∈ weilDivisors Y)
    (hAD : Avoid f D) (hAE : Avoid f E) : cpull f (D + E) = cpull f D + cpull f E := by
  ext x
  obtain ⟨hg, V, hV, hxV, hDV⟩ := isLocEq_locEq hD (f x)
  obtain ⟨hh, V', hV', hxV', hEV'⟩ := isLocEq_locEq hE (f x)
  obtain ⟨ug, hug, hg'⟩ := exists_unit_of_isLocEq f hAD (isLocEq_locEq hD (f x))
  obtain ⟨uh, huh, hh'⟩ := exists_unit_of_isLocEq f hAE (isLocEq_locEq hE (f x))
  have hDE : IsLocEq (D + E) (f x) (locEq D (f x) * locEq E (f x)) := by
    refine ⟨mul_ne_zero hg hh, V ∩ V', hV.inter hV', ⟨hxV, hxV'⟩, fun w hw => ?_⟩
    rw [div_mul hg hh, Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
      Function.locallyFinsuppWithin.coe_add, Pi.add_apply, hDV w hw.1, hEV' w hw.2]
  rw [Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
    cpull_eq_of f ((weilDivisors Y).add_mem hD hE) (avoid_add f hAD hAE) hDE,
    cpull_apply f hD hAD, cpull_apply f hE hAE, ← hg', ← hh', fpull_mul,
    Scheme.ord_mul (fpull_ne_zero f hug) (fpull_ne_zero f huh)]

/-- The pull-back of a principal divisor. -/
lemma cpull_div {g : Y.functionField} (hg : g ≠ 0) (hA : Avoid f (div Y g)) :
    cpull f (div Y g) = div C (fpull f g) := by
  ext x
  rw [cpull_eq_of f (div_mem_weilDivisors g) hA ⟨hg, Set.univ, isOpen_univ, trivial, fun _ _ => rfl⟩,
    div_apply]

/-- A local equation of a divisor that is effective near `y` is regular at `y`. -/
lemma exists_stalk_of_nonneg {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (y : Y)
    (h : ∀ z : Y, z ⤳ y → coheight z = 1 → 0 ≤ D z) :
    ∃ a : Y.presheaf.stalk y, algebraMap _ Y.functionField a = locEq D y := by
  obtain ⟨-, V, hV, hyV, hDV⟩ := isLocEq_locEq hD y
  obtain ⟨a, ha⟩ := mem_range_algebraMap_stalk_of_ord_nonneg y (locEq D y) fun z hz h1 => by
    have := h z hz h1
    rw [hDV z (hz.mem_open hV hyV)] at this
    exact this
  exact ⟨a, ha⟩

lemma cpull_nonneg {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hA : Avoid f D) (x : C)
    (h : ∀ z : Y, z ⤳ f x → coheight z = 1 → 0 ≤ D z) : 0 ≤ cpull f D x := by
  obtain ⟨a, ha⟩ := exists_stalk_of_nonneg hD (f x) h
  rw [cpull_apply f hD hA, ← ha, fpull_algebraMap_at]
  by_cases hx : coheight x = 1
  · exact ord_algebraMap_nonneg hx _
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hx]

lemma cpull_pos {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hA : Avoid f D) {x : C}
    (hx : coheight x = 1) (h : ∀ z : Y, z ⤳ f x → coheight z = 1 → 0 ≤ D z) {z₀ : Y}
    (hz₀ : z₀ ⤳ f x) (hpos : 0 < D z₀) : 0 < cpull f D x := by
  obtain ⟨a, ha⟩ := exists_stalk_of_nonneg hD (f x) h
  obtain ⟨hg0, V, hV, hxV, hDV⟩ := isLocEq_locEq hD (f x)
  obtain ⟨ug, hug, hg'⟩ := exists_unit_of_isLocEq f hA (isLocEq_locEq hD (f x))
  have hna : ¬ IsUnit a := by
    intro hu
    have h1 : D z₀ = 0 := by
      rw [hDV z₀ (hz₀.mem_open hV hxV), div_apply, ← ha,
        ← algebraMap_stalkSpecializes hz₀ a]
      exact ord_algebraMap_isUnit z₀ (hu.map _)
    omega
  have hne : (f.stalkMap x).hom a ≠ 0 := by
    intro h0
    have := fpull_ne_zero f hug
    rw [hg', ← ha, fpull_algebraMap_at, h0, map_zero] at this
    exact this rfl
  have hmem : (f.stalkMap x).hom a ∈ maximalIdeal (C.presheaf.stalk x) :=
    (mem_maximalIdeal _).mpr fun hu => hna (isUnit_of_map_unit (f.stalkMap x).hom a hu)
  rw [cpull_apply f hD hA, ← ha, fpull_algebraMap_at]
  exact ord_algebraMap_stalk_pos hx hne hmem

end

section
variable {C Y Z : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsIntegral Z] [IsLocallyNoetherian Z]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)]
  [∀ z : Z, UniqueFactorizationMonoid (Z.presheaf.stalk z)] (f : C ⟶ Y) (φ : Y ⟶ Z) [IsDominant φ]

lemma fpull_ffMap (u : Z.presheaf.stalk (φ (f (genericPoint C)))) :
    fpull f ((ffMap φ).hom (algebraMap _ Z.functionField u)) =
      fpull (f ≫ φ) (algebraMap _ Z.functionField u) := by
  rw [ffMap_algebraMap, fpull_algebraMap]
  refine Eq.trans ?_ (fpull_algebraMap (f ≫ φ) u).symm
  rw [Scheme.Hom.stalkMap_comp]
  rfl

lemma avoid_pullback {D : AlgebraicCycle Z ℤ} (hD : D ∈ weilDivisors Z) (hA : Avoid (f ≫ φ) D) :
    Avoid f (pullback φ D) := by
  obtain ⟨V, hV, hξ, h0⟩ := hA
  refine ⟨φ ⁻¹' V, hV.preimage φ.continuous, hξ, fun w hw => ?_⟩
  rw [pullback_eq_div_of φ hD one_ne_zero hV (fun w' hw' => by rw [h0 w' hw', JacDivisors.div_one]; rfl) hw,
    map_one, JacDivisors.div_one]
  rfl

/-- Pull-back along `f ≫ φ` is pull-back along `φ` (dominant) and then along `f`. -/
lemma cpull_comp {D : AlgebraicCycle Z ℤ} (hD : D ∈ weilDivisors Z) (hA : Avoid (f ≫ φ) D) :
    cpull (f ≫ φ) D = cpull f (pullback φ D) := by
  ext x
  obtain ⟨hg, V, hV, hxV, hDV⟩ := isLocEq_locEq hD (φ (f x))
  have hloc : IsLocEq D ((f ≫ φ) x) (locEq D (φ (f x))) := ⟨hg, V, hV, hxV, hDV⟩
  obtain ⟨ug, -, hg'⟩ := exists_unit_of_isLocEq (f ≫ φ) hA hloc
  have hloc' : IsLocEq (pullback φ D) (f x) ((ffMap φ).hom (locEq D (φ (f x)))) :=
    ⟨ffMap_ne_zero φ hg, φ ⁻¹' V, hV.preimage φ.continuous, hxV,
      fun w hw => pullback_eq_div_of φ hD hg hV hDV hw⟩
  rw [cpull_eq_of (f ≫ φ) hD hA hloc,
    cpull_eq_of f (pullback_mem_weilDivisors φ D) (avoid_pullback f φ hD hA) hloc', ← hg']
  exact congrArg (fun t => Scheme.ord t x) (fpull_ffMap f φ ug).symm

end

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaCube_Det =====
section

/-!
# S4-ThetaCube, file Det (D-B2, part 1): determinants of pulled-back rational functions
General facts on `fpull` (pull-back of rational functions regular at `f (η_C)`):
* `algebraMap_generic`, `fpull_id`;
* `fpull_fpull`: pulling back twice through stalks;
* **`fpull_det`**: the determinant of a matrix of pulled-back functions is regular at `ℓ (η_C)` and its
  pull-back along `ℓ` is the determinant of the composite pull-backs; `fpull_det_eq`;
* `isUnit_of_stalkMap_ne_zero`, **`avoid_div_of_isUnit`** (for `cpull_div`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory Order Topology RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare

universe u

section Gen

variable {C P X : Scheme.{u}} [IsIntegral C] [IsIntegral P] [IsIntegral X]

/-- On the generic stalk, `algebraMap` to the function field is the identity. -/
lemma algebraMap_generic (v : X.presheaf.stalk (genericPoint X)) :
    @algebraMap (X.presheaf.stalk (genericPoint X)) X.functionField _ _
      (stalkFunctionFieldAlgebra X (genericPoint X)) v = v := by
  have h : (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial :
      genericPoint X ⤳ genericPoint X)) = 𝟙 _ := TopCat.Presheaf.stalkSpecializes_refl _ _
  exact (congrArg (fun t => t.hom v) h).trans rfl

lemma fpull_id (g : X.functionField) : fpull (𝟙 X) g = g := by
  have h := fpull_algebraMap (𝟙 X) (g : X.presheaf.stalk ((𝟙 X : X ⟶ X) (genericPoint X)))
  have e1 : algebraMap (X.presheaf.stalk ((𝟙 X : X ⟶ X) (genericPoint X))) X.functionField g = g :=
    algebraMap_generic g
  have e2 : ((𝟙 X : X ⟶ X).stalkMap (genericPoint X)).hom g = g := by
    rw [Scheme.Hom.stalkMap_id]
    rfl
  rw [e1] at h
  exact h.trans e2

variable (ℓ : C ⟶ P)

/-- Pulling back twice through the stalk at `ℓ (η_C)`. -/
lemma fpull_fpull (z : P ⟶ X) (g : X.functionField)
    (hg : ∃ w : X.presheaf.stalk ((ℓ ≫ z) (genericPoint C)), algebraMap _ X.functionField w = g) :
    ∃ v : P.presheaf.stalk (ℓ (genericPoint C)), algebraMap _ P.functionField v = fpull z g ∧
      (ℓ.stalkMap (genericPoint C)).hom v = fpull (ℓ ≫ z) g := by
  obtain ⟨w, rfl⟩ := hg
  refine ⟨(z.stalkMap (ℓ (genericPoint C))).hom w, (fpull_algebraMap_at z (ℓ (genericPoint C)) w).symm, ?_⟩
  rw [fpull_algebraMap, Scheme.Hom.stalkMap_comp]
  rfl

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **Determinants of pulled-back functions** are regular at `ℓ (η_C)`, with the expected pull-back. -/
theorem fpull_det (z : κ → (P ⟶ X)) (g : κ → κ → X.functionField)
    (hg : ∀ a l, ∃ w : X.presheaf.stalk ((ℓ ≫ z a) (genericPoint C)), algebraMap _ X.functionField w = g a l) :
    ∃ v : P.presheaf.stalk (ℓ (genericPoint C)),
      algebraMap _ P.functionField v = (Matrix.of fun a l => fpull (z a) (g a l)).det ∧
      (ℓ.stalkMap (genericPoint C)).hom v = (Matrix.of fun a l => fpull (ℓ ≫ z a) (g a l)).det := by
  choose v hv1 hv2 using fun a l => fpull_fpull ℓ (z a) (g a l) (hg a l)
  refine ⟨(Matrix.of v).det, ?_, ?_⟩
  · rw [RingHom.map_det]
    congr 1
    ext a l
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    exact hv1 a l
  · rw [RingHom.map_det]
    congr 1
    ext a l
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    exact hv2 a l

theorem fpull_det_eq (z : κ → (P ⟶ X)) (g : κ → κ → X.functionField)
    (hg : ∀ a l, ∃ w : X.presheaf.stalk ((ℓ ≫ z a) (genericPoint C)), algebraMap _ X.functionField w = g a l) :
    fpull ℓ (Matrix.of fun a l => fpull (z a) (g a l)).det =
      (Matrix.of fun a l => fpull (ℓ ≫ z a) (g a l)).det := by
  obtain ⟨v, h1, h2⟩ := fpull_det ℓ z g hg
  rw [← h1, fpull_algebraMap, h2]

/-- A germ at `ℓ (η_C)` with nonzero pull-back is a unit. -/
lemma isUnit_of_stalkMap_ne_zero {v : P.presheaf.stalk (ℓ (genericPoint C))}
    (hv : (ℓ.stalkMap (genericPoint C)).hom v ≠ 0) : IsUnit v := by
  have h : IsUnit ((ℓ.stalkMap (genericPoint C)).hom v : C.functionField) := isUnit_iff_ne_zero.mpr hv
  exact isUnit_of_map_unit (ℓ.stalkMap (genericPoint C)).hom v h

end Gen

section Av

variable {C Y : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsIntegral Y] [IsLocallyNoetherian Y]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)] (f : C ⟶ Y)

/-- **The divisor of a unit at `f (η_C)` avoids `f (η_C)`.** -/
theorem avoid_div_of_isUnit {v : Y.presheaf.stalk (f (genericPoint C))} (hv : IsUnit v) :
    Avoid f (div Y (algebraMap _ Y.functionField v)) := by
  obtain ⟨U, m, s, hs⟩ := TopCat.Presheaf.exists_germ_eq Y.presheaf v
  refine ⟨Y.basicOpen s, (Y.basicOpen s).isOpen, ?_, fun w hw => ?_⟩
  · exact (Y.mem_basicOpen s _ m).mpr (by rw [hs]; exact hv)
  · have hwU : w ∈ U := Y.basicOpen_le s hw
    have hunit : IsUnit (Y.presheaf.germ U w hwU s) := (Y.mem_basicOpen s w hwU).mp hw
    have : Nonempty U := ⟨⟨w, hwU⟩⟩
    have e : algebraMap _ Y.functionField (Y.presheaf.germ U w hwU s) =
        algebraMap _ Y.functionField v := by
      rw [← hs, Scheme.algebraMap_germ_eq_germToFunctionField, Scheme.algebraMap_germ_eq_germToFunctionField]
    rw [div_apply, ← e]
    exact ord_algebraMap_isUnit w hunit

end Av

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_SmDed =====
section

/-!
# S4-ThetaCube, file SmDed (D-B0, part 1): a Dedekind domain of finite type over an algebraically closed field is smooth

Let `B` be a Dedekind domain (not a field) of finite type over an algebraically closed field `K`.
* `exists_unif`: at a nonzero prime `q`, some `x : B` generates the maximal ideal of `B_q`.
* `aeval_injective`: such an `x` is transcendental over `K`.
* `isSmoothAt_of_isMaximal`: `K[X] → B`, `X ↦ x`, is flat (torsion free over a PID), finitely presented and
  unramified at `q` (Mathlib `isUnramifiedAt_iff_map_eq`), hence etale at `q`
  (Mathlib `IsEtaleAt.of_isUnramifiedAt_of_flat`); so `B` is smooth over `K` at `q`.
* `smooth_of_dedekind`: `Algebra.Smooth K B` (the smooth locus is open and contains every closed point).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace RamanujanPetersson.ThetaCube

open Polynomial IsLocalRing

section SmoothDedekind

variable {K : Type*} [Field K] [IsAlgClosed K] {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra K B]
  [Algebra.FiniteType K B]

/-- A uniformizer at a nonzero prime of a Dedekind domain can be chosen in `B`. -/
theorem exists_unif (q : Ideal B) [q.IsPrime] (hq : q ≠ ⊥) :
    ∃ x : B, maximalIdeal (Localization.AtPrime q) = Ideal.span {algebraMap B _ x} := by
  have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hq (Localization.AtPrime q)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime q)
  obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.mk'_surjective q.primeCompl ϖ
  refine ⟨x, ?_⟩
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hϖ, ← hxs,
    ← IsLocalization.mk'_spec (Localization.AtPrime q) x s,
    Ideal.span_singleton_mul_right_unit (IsLocalization.map_units _ s)]

theorem mem_of_unif (q : Ideal B) [q.IsPrime] {x : B}
    (hx : maximalIdeal (Localization.AtPrime q) = Ideal.span {algebraMap B _ x}) : x ∈ q := by
  have h : algebraMap B (Localization.AtPrime q) x ∈ maximalIdeal (Localization.AtPrime q) := by
    rw [hx]
    exact Ideal.subset_span rfl
  rw [← Localization.AtPrime.under_maximalIdeal (I := q)]
  exact h

theorem ne_zero_of_unif (q : Ideal B) [q.IsPrime] (hq : q ≠ ⊥) {x : B}
    (hx : maximalIdeal (Localization.AtPrime q) = Ideal.span {algebraMap B _ x}) : x ≠ 0 := by
  rintro rfl
  have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hq (Localization.AtPrime q)
  exact IsDiscreteValuationRing.not_a_field _ (by rw [hx, map_zero, Ideal.span_singleton_eq_bot.mpr rfl])

omit [IsDedekindDomain B] [Algebra.FiniteType K B] in
/-- A nonzero element of a proper prime is transcendental over the algebraically closed field `K`. -/
theorem aeval_injective [IsDomain B] (q : Ideal B) [q.IsPrime] {x : B} (hxq : x ∈ q) (hx0 : x ≠ 0) :
    Function.Injective (aeval x : K[X] →ₐ[K] B) := by
  by_contra h
  have halg : IsAlgebraic K x := by
    by_contra h'
    exact h (transcendental_iff_injective.mp h')
  obtain ⟨c, hc⟩ := RingHom.mem_range.mp (minpoly.mem_range_of_degree_eq_one K x
    (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible halg.isIntegral)))
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [← hc, map_zero])
  apply Ideal.IsPrime.ne_top ‹q.IsPrime›
  apply Ideal.eq_top_of_isUnit_mem q hxq
  rw [← hc]
  exact (IsUnit.mk0 c hc0).map (algebraMap K B)

omit [IsDedekindDomain B] in
/-- Nullstellensatz: every element is congruent to a constant modulo a maximal ideal. -/
theorem exists_sub_mem (q : Ideal B) [q.IsMaximal] (b : B) : ∃ c : K, b - algebraMap K B c ∈ q := by
  letI := Ideal.Quotient.field q
  have : Module.Finite K (B ⧸ q) := finite_of_finite_type_of_isJacobsonRing K (B ⧸ q)
  obtain ⟨c, hc⟩ :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := B ⧸ q)).2 (Ideal.Quotient.mk q b)
  refine ⟨c, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hc, Ideal.Quotient.mk_algebraMap, sub_self]

/-- A field extension whose algebra map is surjective is separable. -/
theorem isSeparable_of_surjective {F E : Type*} [Field F] [Field E] [Algebra F E]
    (h : Function.Surjective (algebraMap F E)) : Algebra.IsSeparable F E :=
  ⟨fun y => by
    obtain ⟨a, rfl⟩ := h y
    exact isSeparable_algebraMap a⟩

/-- **Smoothness at closed points.** -/
theorem isSmoothAt_of_isMaximal (hB : ¬ IsField B) (q : Ideal B) [hqm : q.IsMaximal] :
    Algebra.IsSmoothAt K q := by
  have hq : q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hqm hB
  obtain ⟨x, hx⟩ := exists_unif q hq
  have hxq : x ∈ q := mem_of_unif q hx
  have hx0 : x ≠ 0 := ne_zero_of_unif q hq hx
  letI : Algebra K[X] B := (aeval x).toRingHom.toAlgebra
  haveI : IsScalarTower K K[X] B := IsScalarTower.of_algebraMap_eq fun c => (aeval_C x c).symm
  haveI : Algebra.FiniteType K[X] B := Algebra.FiniteType.of_restrictScalars_finiteType K K[X] B
  haveI : Algebra.FinitePresentation K[X] B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : Module.Flat K[X] B := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, ← Submodule.isTorsionFree_iff_torsion_eq_bot,
      Module.isTorsionFree_iff_faithfulSMul, faithfulSMul_iff_algebraMap_injective]
    exact aeval_injective q hxq hx0
  have hxX : algebraMap K[X] B X = x := aeval_X x
  letI : Algebra (Localization.AtPrime (q.under K[X])) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver (q.under K[X]) q
  haveI : Algebra.IsUnramifiedAt K[X] q := by
    rw [Algebra.isUnramifiedAt_iff_map_eq K[X] (q.under K[X]) q]
    refine ⟨?_, le_antisymm ?_ ?_⟩
    · apply isSeparable_of_surjective
      intro y
      obtain ⟨b, rfl⟩ := Ideal.algebraMap_residueField_surjective q y
      obtain ⟨c, hc⟩ := exists_sub_mem (K := K) q b
      refine ⟨algebraMap K[X] (q.under K[X]).ResidueField (C c), ?_⟩
      rw [← IsScalarTower.algebraMap_apply K[X] (q.under K[X]).ResidueField q.ResidueField,
        IsScalarTower.algebraMap_apply K[X] B q.ResidueField,
        show algebraMap K[X] B (C c) = algebraMap K B c from aeval_C x c,
        ← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, Ideal.ker_algebraMap_residueField, ← neg_sub]
      exact q.neg_mem hc
    · calc Ideal.map (algebraMap K[X] (Localization.AtPrime q)) (q.under K[X])
          = Ideal.map (algebraMap B (Localization.AtPrime q))
              (Ideal.map (algebraMap K[X] B) (q.under K[X])) := by
            rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
        _ ≤ Ideal.map (algebraMap B (Localization.AtPrime q)) q :=
            Ideal.map_mono (Ideal.map_comap_le (f := algebraMap K[X] B) (K := q))
        _ = maximalIdeal (Localization.AtPrime q) := Localization.AtPrime.map_eq_maximalIdeal
    · rw [hx, Ideal.span_le, Set.singleton_subset_iff]
      have hX : (X : K[X]) ∈ Ideal.comap (algebraMap K[X] B) q := by
        rw [Ideal.mem_comap, hxX]
        exact hxq
      have h1 : algebraMap B (Localization.AtPrime q) x = algebraMap K[X] (Localization.AtPrime q) X := by
        rw [IsScalarTower.algebraMap_apply K[X] B (Localization.AtPrime q), hxX]
      rw [SetLike.mem_coe, h1]
      exact Ideal.mem_map_of_mem _ hX
  haveI : Algebra.IsEtaleAt K[X] q := Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat q
  haveI : IsScalarTower K K[X] (Localization.AtPrime q) := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply K B (Localization.AtPrime q),
      IsScalarTower.algebraMap_apply K[X] B (Localization.AtPrime q), ← IsScalarTower.algebraMap_apply K K[X] B]
  exact Algebra.FormallySmooth.comp K K[X] (Localization.AtPrime q)

/-- `B` is formally smooth over `K`: the smooth locus is open and contains every closed point. -/
theorem formallySmooth_of_dedekind (hB : ¬ IsField B) : Algebra.FormallySmooth K B := by
  haveI : Algebra.FinitePresentation K B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  rw [← Algebra.smoothLocus_eq_univ_iff]
  refine Set.eq_univ_of_forall fun P => ?_
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal P.asIdeal P.isPrime.ne_top
  have hMs : (⟨M, hM.isPrime⟩ : PrimeSpectrum B) ∈ Algebra.smoothLocus K B := isSmoothAt_of_isMaximal hB M
  exact ((PrimeSpectrum.le_iff_specializes P ⟨M, hM.isPrime⟩).mp hle).mem_open Algebra.isOpen_smoothLocus hMs

/-- **D-B0 (ring part).** A Dedekind domain of finite type over an algebraically closed field is smooth. -/
theorem smooth_of_dedekind (hB : ¬ IsField B) : Algebra.Smooth K B :=
  haveI : Algebra.FinitePresentation K B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  ⟨formallySmooth_of_dedekind hB, inferInstance⟩

end SmoothDedekind

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_IntersectA_Top =====
section

/-!
# S4-IntersectA, file Top: general position by a dimension count (topology only)

`X` a Noetherian scheme (points ordered by specialization, `x ≤ y ↔ y ⤳ x`, so `Order.height x` is the
dimension of `closure {x}`). If `height x ≤ g` everywhere and, for each `i < g`, the closed sets `H i a`
(`a : α`) can be chosen to avoid any finite set of points, then some choice makes `⋂ i < g, H i (a i)`
a finite set of closed points. This is the dimension half of L31 (S4_COREB_ROUTE.md section 3).
-/

set_option autoImplicit false

universe u

open Topology TopologicalSpace AlgebraicGeometry

namespace RamanujanPetersson.IntersectA

variable {X : Scheme.{u}} [NoetherianSpace X]

/-- A closed set is a finite union of closures of its own points (its generic points of components). -/
theorem exists_finset_closure (F : Set X) (hF : IsClosed F) :
    ∃ S : Finset X, (∀ η ∈ S, η ∈ F) ∧ F = ⋃ η ∈ S, closure {η} := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨∅, by simp, by rw [Set.eq_empty_of_isEmpty F]; simp⟩
  obtain ⟨T, hTf, hTc, hTi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hF
  choose! gp hgp using fun t (ht : t ∈ T) => QuasiSober.sober (hTi t ht) (hTc t ht)
  refine ⟨(hTf.image gp).toFinset, ?_, ?_⟩
  · intro η hη
    rw [Set.Finite.mem_toFinset] at hη
    obtain ⟨t, ht, rfl⟩ := hη
    exact ⟨t, ht, (hgp t ht).mem⟩
  · ext x
    simp only [Set.mem_sUnion, Set.mem_iUnion, Set.Finite.mem_toFinset, exists_prop]
    constructor
    · rintro ⟨t, ht, hx⟩
      exact ⟨gp t, ⟨t, ht, rfl⟩, by rw [(hgp t ht).def]; exact hx⟩
    · rintro ⟨_, ⟨t, ht, rfl⟩, hx⟩
      exact ⟨t, ht, by rwa [(hgp t ht).def] at hx⟩

/-- Cutting by a closed set `H` that misses the finitely many generic points strictly lowers them. -/
theorem step (S : Finset X) (H : Set X) (hH : IsClosed H) (hS : ∀ η ∈ S, η ∉ H) :
    ∃ S' : Finset X, (⋃ η ∈ S, closure {η}) ∩ H ⊆ ⋃ ξ ∈ S', closure {ξ} ∧
      ∀ ξ ∈ S', ∃ η ∈ S, ξ < η := by
  have hF : IsClosed ((⋃ η ∈ S, closure {η}) ∩ H) :=
    (isClosed_biUnion_finset fun η _ => isClosed_closure).inter hH
  obtain ⟨S', hS'F, hS'eq⟩ := exists_finset_closure _ hF
  refine ⟨S', hS'eq.le, fun ξ hξ => ?_⟩
  obtain ⟨hξ1, hξH⟩ := hS'F ξ hξ
  simp only [Set.mem_iUnion, exists_prop] at hξ1
  obtain ⟨η, hη, hξη⟩ := hξ1
  refine ⟨η, hη, lt_iff_le_not_ge.2 ⟨specializes_iff_mem_closure.mpr hξη, fun h => ?_⟩⟩
  exact hS η hη (Specializes.mem_closed h hH hξH)

/-- The height bookkeeping of one cut: `height + j ≤ g` becomes `height + (j + 1) ≤ g`. -/
theorem height_step (S : Finset X) (H : Set X) (hH : IsClosed H) (hS : ∀ η ∈ S, η ∉ H) (j g : ℕ)
    (hht : ∀ η ∈ S, Order.height η + j ≤ g) :
    ∃ S' : Finset X, (⋃ η ∈ S, closure {η}) ∩ H ⊆ ⋃ ξ ∈ S', closure {ξ} ∧
      ∀ ξ ∈ S', Order.height ξ + ((j + 1 : ℕ) : ℕ∞) ≤ g := by
  obtain ⟨S', h1, h2⟩ := step S H hH hS
  refine ⟨S', h1, fun ξ hξ => ?_⟩
  obtain ⟨η, hη, hlt⟩ := h2 ξ hξ
  have hηfin : Order.height η < ⊤ :=
    lt_of_le_of_lt le_self_add (lt_of_le_of_lt (hht η hη) (ENat.natCast_lt_top g))
  have hξfin : Order.height ξ < ⊤ := lt_of_le_of_lt (Order.height_mono hlt.le) hηfin
  have h3 : Order.height ξ + 1 ≤ Order.height η :=
    Order.add_one_le_of_lt (Order.height_strictMono hlt hξfin)
  calc Order.height ξ + ((j + 1 : ℕ) : ℕ∞) = Order.height ξ + 1 + j := by push_cast; ring
    _ ≤ Order.height η + j := by gcongr
    _ ≤ g := hht η hη

omit [NoetherianSpace X] in
/-- A point of height `0` is closed. -/
theorem isClosed_singleton_of_height_eq_zero (x : X) (hx : Order.height x = 0) :
    IsClosed ({x} : Set X) := by
  rw [Order.height_eq_zero] at hx
  refine isClosed_of_closure_subset fun y hy => ?_
  have h1 : x ⤳ y := specializes_iff_mem_closure.mpr hy
  have h2 : y ⤳ x := hx (show y ≤ x from h1)
  exact Set.mem_singleton_iff.mpr (h1.antisymm h2).eq.symm

/-- The inductive construction: after `j` cuts the intersection lies in `⋃ closure {η}` with
`height η + j ≤ g`. -/
theorem gp_aux {α : Type*} (g : ℕ) (H : ℕ → α → Set X) (hHc : ∀ i a, IsClosed (H i a))
    (hH : ∀ i (S : Finset X), ∃ a, ∀ η ∈ S, η ∉ H i a)
    (S0 : Finset X) (hS0 : ∀ η ∈ S0, Order.height η ≤ g) :
    ∀ j ≤ g, ∃ a : ℕ → α, ∃ S : Finset X,
      (⋃ η ∈ S0, closure {η}) ∩ (⋂ i < j, H i (a i)) ⊆ ⋃ η ∈ S, closure {η} ∧
        ∀ η ∈ S, Order.height η + (j : ℕ∞) ≤ g := by
  intro j
  induction j with
  | zero =>
    intro _
    obtain ⟨a0, -⟩ := hH 0 ∅
    exact ⟨fun _ => a0, S0, Set.inter_subset_left, fun η hη => by simpa using hS0 η hη⟩
  | succ j ih =>
    intro hj
    obtain ⟨a, S, hsub, hht⟩ := ih (Nat.le_of_succ_le hj)
    obtain ⟨b, hb⟩ := hH j S
    obtain ⟨S', hsub', hht'⟩ := height_step S (H j b) (hHc j b) hb j g hht
    refine ⟨Function.update a j b, S', ?_, hht'⟩
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_iInter] at hx
    obtain ⟨hx0, hxi⟩ := hx
    refine hsub' ⟨hsub ⟨hx0, ?_⟩, ?_⟩
    · simp only [Set.mem_iInter]
      intro i hi
      have := hxi i (Nat.lt_succ_of_lt hi)
      rwa [Function.update_of_ne (Nat.ne_of_lt hi)] at this
    · have := hxi j (Nat.lt_succ_self j)
      rwa [Function.update_self] at this

/-- **General position (topological form).** If `dim X ≤ g` and each `H i ·` can avoid any finite set,
some choice of parameters makes `⋂ i < g, H i (a i)` a finite set of closed points. -/
theorem exists_finite_inter {α : Type*} (g : ℕ) (hdim : ∀ x : X, Order.height x ≤ g)
    (H : ℕ → α → Set X) (hHc : ∀ i a, IsClosed (H i a))
    (hH : ∀ i (S : Finset X), ∃ a, ∀ η ∈ S, η ∉ H i a) :
    ∃ a : ℕ → α, (⋂ i < g, H i (a i)).Finite ∧
      ∀ x ∈ ⋂ i < g, H i (a i), IsClosed ({x} : Set X) := by
  obtain ⟨S0, -, hS0⟩ := exists_finset_closure (Set.univ : Set X) isClosed_univ
  obtain ⟨a, S, hsub, hht⟩ := gp_aux g H hHc hH S0 (fun η _ => hdim η) g le_rfl
  have hcl : ∀ η ∈ S, closure {η} = ({η} : Set X) := fun η hη => by
    have h0 : Order.height η = 0 := by
      have h1 := hht η hη
      by_contra h
      have h3 : (1 : ℕ∞) + g ≤ Order.height η + g := by
        gcongr
        exact Order.one_le_iff_ne_zero.mpr h
      have h2 := h3.trans h1
      norm_cast at h2
      omega
    exact (isClosed_singleton_of_height_eq_zero η h0).closure_eq
  have key : (⋂ i < g, H i (a i)) ⊆ (S : Set X) := by
    intro x hx
    have hx' := hsub ⟨by rw [← hS0]; trivial, hx⟩
    simp only [Set.mem_iUnion, exists_prop] at hx'
    obtain ⟨η, hη, hxη⟩ := hx'
    rw [hcl η hη, Set.mem_singleton_iff] at hxη
    rw [hxη]
    exact hη
  refine ⟨a, S.finite_toSet.subset key, fun x hx => ?_⟩
  exact closure_eq_iff_isClosed.mp (hcl x (key hx))

end RamanujanPetersson.IntersectA


end

-- ===== S4.Def_RP_IsogDegA_Trans =====
section

/-!
# S4-IsogDegA, file Trans: translations by `k`-points of a group scheme over `k`

`A : Over (Spec k)` with `[GrpObj A]`. For a `k`-point `a : 𝟙_ ⟶ A`, `transl A a = 𝟙 A * (toUnit A ≫ a)`
is right translation by `a`, an automorphism of `A` over `k`. A homomorphism `φ` intertwines
`transl a` and `transl (a ≫ φ)`. With `k` algebraically closed and `A` locally of finite type,
`pt c = c.left (closed point)` identifies `k`-points with closed points, and translations act
transitively on closed points.
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory

namespace RamanujanPetersson.IsogDegA

section Group

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- Right translation by the `k`-point `a`. -/
noncomputable def transl (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) : A ⟶ A :=
  𝟙 A * (toUnit A ≫ a)

theorem comp_transl {X : Over (Spec (.of k))} (f : X ⟶ A) (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    f ≫ transl A a = f * (toUnit X ≫ a) := by
  rw [transl, comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]

theorem transl_one : transl A 1 = 𝟙 A := by
  rw [transl, comp_one, _root_.mul_one]

theorem transl_comp_transl (a b : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    transl A a ≫ transl A b = transl A (a * b) := by
  rw [comp_transl, transl, transl, comp_mul, _root_.mul_assoc]

theorem point_comp_transl (c a : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    c ≫ transl A a = c * a := by
  rw [comp_transl, toUnit_unit, Category.id_comp]

/-- A homomorphism intertwines translations. -/
theorem transl_comp_hom (φ : A ⟶ A) [IsMonHom φ] (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    transl A a ≫ φ = φ ≫ transl A (a ≫ φ) := by
  rw [comp_transl, transl, mul_comp, Category.id_comp, Category.assoc]

end Group

section Points

variable {k : Type u} [Field k] (A : Over (Spec (.of k)))

variable (k) in
/-- The unique point of `Spec k`. -/
noncomputable def pt0 : Spec (.of k) := IsLocalRing.closedPoint k

/-- The point of `A` hit by the `k`-point `c`. -/
noncomputable def pt (c : 𝟙_ (Over (Spec (.of k))) ⟶ A) : A.left :=
  c.left (pt0 k)

theorem pt_comp {B : Over (Spec (.of k))} (c : 𝟙_ (Over (Spec (.of k))) ⟶ A) (f : A ⟶ B) :
    pt B (c ≫ f) = f.left (pt A c) := by
  simp only [pt, Over.comp_left, Scheme.Hom.comp_apply]

theorem transl_pt [GrpObj A] (c a : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    (transl A a).left (pt A c) = pt A (c * a) := by
  rw [← pt_comp, point_comp_transl, pt]

variable [IsAlgClosed k] [LocallyOfFiniteType A.hom]

/-- `k`-points are the closed points. -/
noncomputable def ptEquiv : (𝟙_ (Over (Spec (.of k))) ⟶ A) ≃ closedPoints A.left :=
  (Equiv.mk (fun c ↦ ⟨c.left, Over.w c⟩) (fun p ↦ Over.homMk p.1 p.2) (fun _ ↦ rfl)
    (fun _ ↦ rfl)).trans (pointEquivClosedPoint A.hom)

theorem ptEquiv_apply (c : 𝟙_ (Over (Spec (.of k))) ⟶ A) : (ptEquiv A c).1 = pt A c := rfl

theorem pt_injective : Function.Injective (pt A) := fun _ _ h ↦
  (ptEquiv A).injective (Subtype.ext h)

theorem isClosed_pt (c : 𝟙_ (Over (Spec (.of k))) ⟶ A) : IsClosed {pt A c} :=
  (ptEquiv A c).2

theorem exists_pt_eq (z : A.left) (hz : IsClosed {z}) : ∃ c, pt A c = z :=
  ⟨(ptEquiv A).symm ⟨z, hz⟩, by rw [← ptEquiv_apply, Equiv.apply_symm_apply]⟩

/-- Translations act transitively on closed points. -/
theorem exists_transl_eq [GrpObj A] (z₁ z₂ : A.left) (h₁ : IsClosed {z₁}) (h₂ : IsClosed {z₂}) :
    ∃ a, (transl A a).left z₁ = z₂ := by
  obtain ⟨c₁, rfl⟩ := exists_pt_eq A z₁ h₁
  obtain ⟨c₂, rfl⟩ := exists_pt_eq A z₂ h₂
  exact ⟨c₁⁻¹ * c₂, by rw [transl_pt, mul_inv_cancel_left]⟩

end Points

end RamanujanPetersson.IsogDegA


end

-- ===== S4.Def_RP_IntersectA_Gen =====
section

/-!
# S4-IntersectA, file Gen: translates in general position (L31 existence)

`A : Over (Spec k)` a group scheme, `k` algebraically closed, `A` locally of finite type.
Left translations `ltransl A w` move `k`-points by `w * _`. For a point `y` and a proper closed `D`,
the right translation parameters `a` with `(transl A a).left y ∈ D` have their points in a proper
closed set (`exists_open_good`); with `A` irreducible, finitely many points can be moved off `D` by one
`a` (`exists_good`). Combined with the dimension count of file Top: for `g` closed subschemes `D i`
with proper supports on `A` of dimension `≤ g`, some translates meet in a finite set of closed points
(`exists_finite_support`).
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory TopologicalSpace

namespace RamanujanPetersson.IntersectA

open RamanujanPetersson.IsogDegA

/-- Finitely many nonempty opens of an irreducible space meet. -/
theorem nonempty_biInter_finset {X : Type*} [TopologicalSpace X] [IrreducibleSpace X] {I : Type*}
    (S : Finset I) (U : I → Set X) (ho : ∀ i ∈ S, IsOpen (U i)) (hn : ∀ i ∈ S, (U i).Nonempty) :
    (⋂ i ∈ S, U i).Nonempty := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s _ ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at ho hn
    rw [Finset.set_biInter_insert]
    exact nonempty_preirreducible_inter ho.1 (isOpen_biInter_finset ho.2) hn.1 (ih ho.2 hn.2)

section Left

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- Left translation by the `k`-point `w`. -/
noncomputable def ltransl (w : 𝟙_ (Over (Spec (.of k))) ⟶ A) : A ⟶ A :=
  (toUnit A ≫ w) * 𝟙 A

theorem comp_ltransl {X : Over (Spec (.of k))} (f : X ⟶ A) (w : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    f ≫ ltransl A w = (toUnit X ≫ w) * f := by
  rw [ltransl, comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]

theorem ltransl_one : ltransl A 1 = 𝟙 A := by
  rw [ltransl, comp_one, _root_.one_mul]

theorem ltransl_comp_ltransl (w v : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    ltransl A w ≫ ltransl A v = ltransl A (v * w) := by
  rw [comp_ltransl, ltransl, ltransl, comp_mul, _root_.mul_assoc]

theorem isIso_ltransl_left (w : 𝟙_ (Over (Spec (.of k))) ⟶ A) : IsIso (ltransl A w).left :=
  ⟨⟨(ltransl A w⁻¹).left, by
    rw [← Over.comp_left, ltransl_comp_ltransl, _root_.inv_mul_cancel, ltransl_one, Over.id_left], by
    rw [← Over.comp_left, ltransl_comp_ltransl, _root_.mul_inv_cancel, ltransl_one, Over.id_left]⟩⟩

theorem point_comp_ltransl (c w : 𝟙_ (Over (Spec (.of k))) ⟶ A) : c ≫ ltransl A w = w * c := by
  rw [comp_ltransl, toUnit_unit, Category.id_comp]

theorem ltransl_pt (c w : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    (ltransl A w).left (pt A c) = pt A (w * c) := by
  rw [← pt_comp, point_comp_ltransl]

/-- The intersection of the translates `D i` by `a i` (all `g` divisors translated). -/
noncomputable def Zid {g : ℕ} (D : Fin g → A.left.IdealSheafData)
    (a : Fin g → (𝟙_ (Over (Spec (.of k))) ⟶ A)) : A.left.IdealSheafData :=
  ⨆ i, (D i).comap (transl A (a i)).left

theorem coe_support_Zid {g : ℕ} (D : Fin g → A.left.IdealSheafData)
    (a : Fin g → (𝟙_ (Over (Spec (.of k))) ⟶ A)) :
    ((Zid A D a).support : Set A.left) = ⋂ i, (transl A (a i)).left ⁻¹' (D i).support := by
  ext x
  simp [Zid]

end Left

section Generic

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [LocallyOfFiniteType A.hom]

omit [GrpObj A] in
/-- A nonempty locally closed set contains a `k`-point (Jacobson). -/
theorem exists_pt_mem (F : Set A.left) (hF : IsLocallyClosed F) (hne : F.Nonempty) :
    ∃ w, pt A w ∈ F := by
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  obtain ⟨z, hzF, hz⟩ := nonempty_inter_closedPoints hne hF
  obtain ⟨w, rfl⟩ := exists_pt_eq A z hz
  exact ⟨w, hzF⟩

/-- The translation parameters moving `y` into a proper closed `D` lie in a proper closed set. -/
theorem exists_open_good (y : A.left) (D : Set A.left) (hD : IsClosed D) (hne : D ≠ Set.univ) :
    ∃ U : Set A.left, IsOpen U ∧ U.Nonempty ∧ ∀ a, pt A a ∈ U → (transl A a).left y ∉ D := by
  let B : Set A.left := ⋂ (w) (_ : pt A w ∈ closure {y}), (ltransl A w).left ⁻¹' D
  have hB : IsClosed B :=
    isClosed_iInter fun w => isClosed_iInter fun _ => hD.preimage (ltransl A w).left.continuous
  refine ⟨Bᶜ, hB.isOpen_compl, ?_, ?_⟩
  · obtain ⟨w₀, hw₀⟩ := exists_pt_mem A (closure {y}) isClosed_closure.isLocallyClosed
      ⟨y, subset_closure rfl⟩
    obtain ⟨y, hy⟩ : ∃ y, y ∉ D := by
      by_contra h
      push_neg at h
      exact hne (Set.eq_univ_of_forall h)
    have := isIso_ltransl_left A w₀
    obtain ⟨x, rfl⟩ := (ltransl A w₀).left.surjective y
    exact ⟨x, fun hx => hy (Set.mem_iInter₂.1 hx w₀ hw₀)⟩
  · intro a ha hbad
    apply ha
    refine Set.mem_iInter₂.2 fun w hw => ?_
    show (ltransl A w).left (pt A a) ∈ D
    rw [ltransl_pt, ← transl_pt]
    have h1 := map_mem_closure (t := D) (transl A a).left.continuous hw
      (fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact hbad)
    rwa [hD.closure_eq] at h1

/-- One translation moves finitely many points off a proper closed set. -/
theorem exists_good [IrreducibleSpace A.left] (S : Finset A.left) (D : Set A.left) (hD : IsClosed D)
    (hne : D ≠ Set.univ) : ∃ a, ∀ y ∈ S, (transl A a).left y ∉ D := by
  choose U hUo hUn hU using fun y => exists_open_good A y D hD hne
  obtain ⟨a, ha⟩ := exists_pt_mem A (⋂ y ∈ S, U y)
    (isOpen_biInter_finset fun y _ => hUo y).isLocallyClosed
    (nonempty_biInter_finset S U (fun y _ => hUo y) fun y _ => hUn y)
  exact ⟨a, fun y hy => hU y a (Set.mem_iInter₂.1 ha y hy)⟩

/-- L31 (existence): some translates of `g` proper closed subschemes meet in finitely many closed
points, on a Noetherian irreducible `A` of dimension `≤ g`. -/
theorem exists_finite_support [NoetherianSpace A.left] [IrreducibleSpace A.left] (g : ℕ)
    (hdim : ∀ x : A.left, Order.height x ≤ g) (D : Fin g → A.left.IdealSheafData)
    (hD : ∀ i, (D i).support ≠ ⊤) :
    ∃ a : Fin g → (𝟙_ (Over (Spec (.of k))) ⟶ A),
      ((Zid A D a).support : Set A.left).Finite ∧
        ∀ x ∈ ((Zid A D a).support : Set A.left), IsClosed ({x} : Set A.left) := by
  classical
  let H : ℕ → (𝟙_ (Over (Spec (.of k))) ⟶ A) → Set A.left := fun i a =>
    if h : i < g then (transl A a).left ⁻¹' (D ⟨i, h⟩).support else ∅
  have hHc : ∀ i a, IsClosed (H i a) := by
    intro i a
    by_cases h : i < g
    · simp only [H, dif_pos h]
      exact (D ⟨i, h⟩).support.isClosed.preimage (transl A a).left.continuous
    · simp only [H, dif_neg h]
      exact isClosed_empty
  have hH : ∀ i (S : Finset A.left), ∃ a, ∀ y ∈ S, y ∉ H i a := by
    intro i S
    by_cases h : i < g
    · have hne : ((D ⟨i, h⟩).support : Set A.left) ≠ Set.univ := fun he =>
        hD ⟨i, h⟩ (TopologicalSpace.Closeds.ext (by rw [he]; rfl))
      obtain ⟨a, ha⟩ := exists_good A S _ (D ⟨i, h⟩).support.isClosed hne
      exact ⟨a, fun y hy => by simp only [H, dif_pos h]; exact ha y hy⟩
    · exact ⟨1, fun y _ => by simp only [H, dif_neg h]; exact Set.notMem_empty y⟩
  obtain ⟨a, hfin, hcl⟩ := exists_finite_inter g hdim H hHc hH
  have hsub : ((Zid A D (fun i => a i)).support : Set A.left) ⊆ ⋂ i < g, H i (a i) := by
    intro x hx
    rw [coe_support_Zid, Set.mem_iInter] at hx
    refine Set.mem_iInter₂.2 fun i hi => ?_
    simp only [H, dif_pos hi]
    exact hx ⟨i, hi⟩
  exact ⟨fun i => a i, hfin.subset hsub, fun x hx => hcl x (hsub hx)⟩

end Generic

end RamanujanPetersson.IntersectA


end

-- ===== S4.Def_RP_IntersectA_Fam =====
section

/-!
# S4-IntersectA, file Fam: the family of translated intersections over `A^g`

`Pw A n = A ⊗ ⋯ ⊗ A` (`n` factors) in `Over (Spec k)`, with projections `proj A n i` and the point
`ptOf A n a` with coordinates `a`. Over `P = Pw A g` the family `famI A D` on `A ⊗ P` is cut out by
the pullbacks of the `D i` along `μᵢ(x, c) = x * cᵢ`. Its fibre over a `k`-point `c` of `P` is the
intersection `Zid A D (c ≫ proj A g ·)` of the translates (`comap_famI`, `isPullback_fibre`).
`len A J` is the length of a closed subscheme `J` of `A`: the rank of `J → Spec k`.
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory Limits

namespace RamanujanPetersson.IntersectA

open RamanujanPetersson.IsogDegA

section Pow

variable {k : Type u} [Field k] (A : Over (Spec (.of k)))

/-- `Pw A n = A^n` as an iterated tensor power. -/
noncomputable def Pw : ℕ → Over (Spec (.of k))
  | 0 => 𝟙_ _
  | n + 1 => Pw n ⊗ A

/-- The coordinate projections of `A^n`. -/
noncomputable def proj : (n : ℕ) → Fin n → (Pw A n ⟶ A)
  | 0, i => i.elim0
  | n + 1, i => if h : (i : ℕ) < n then fst (Pw A n) A ≫ proj n ⟨i, h⟩ else snd (Pw A n) A

/-- The `k`-point of `A^n` with coordinates `a`. -/
noncomputable def ptOf : (n : ℕ) → (Fin n → (𝟙_ (Over (Spec (.of k))) ⟶ A)) →
    (𝟙_ (Over (Spec (.of k))) ⟶ Pw A n)
  | 0, _ => 𝟙 _
  | n + 1, a => lift (ptOf n (Fin.init a)) (a (Fin.last n))

theorem proj_last (n : ℕ) : proj A (n + 1) (Fin.last n) = snd (Pw A n) A := by
  simp [proj]; rfl

theorem proj_castSucc (n : ℕ) (j : Fin n) :
    proj A (n + 1) j.castSucc = fst (Pw A n) A ≫ proj A n j := by
  simp [proj]; rfl

theorem ptOf_succ_fst (n : ℕ) (a : Fin (n + 1) → (𝟙_ (Over (Spec (.of k))) ⟶ A)) :
    ptOf A (n + 1) a ≫ fst (Pw A n) A = ptOf A n (Fin.init a) :=
  lift_fst _ _

theorem ptOf_succ_snd (n : ℕ) (a : Fin (n + 1) → (𝟙_ (Over (Spec (.of k))) ⟶ A)) :
    ptOf A (n + 1) a ≫ snd (Pw A n) A = a (Fin.last n) :=
  lift_snd _ _

theorem ptOf_proj (n : ℕ) (a : Fin n → (𝟙_ (Over (Spec (.of k))) ⟶ A)) (i : Fin n) :
    ptOf A n a ≫ proj A n i = a i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    induction i using Fin.lastCases with
    | last => rw [proj_last]; exact ptOf_succ_snd A n a
    | cast j =>
      rw [proj_castSucc]
      exact ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ proj A n j) (ptOf_succ_fst A n a))).trans (ih _ j)

theorem ptOf_comp_proj (n : ℕ) (c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A n) :
    ptOf A n (fun i => c ≫ proj A n i) = c := by
  induction n with
  | zero => exact toUnit_unique _ _
  | succ n ih =>
    refine CartesianMonoidalCategory.hom_ext (X := Pw A n) (Y := A) _ _ ?_ ?_
    · have h : Fin.init (fun i => c ≫ proj A (n + 1) i) =
          fun j => (c ≫ fst (Pw A n) A) ≫ proj A n j := by
        funext j
        simp only [Fin.init, proj_castSucc]
        exact (Category.assoc _ _ _).symm
      exact (ptOf_succ_fst A n _).trans (by rw [h, ih]; rfl)
    · exact (ptOf_succ_snd A n _).trans (congrArg (c ≫ ·) (proj_last A n))

end Pow

section Family

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- `mu A g i : A ⊗ A^g ⟶ A`, `(x, c) ↦ x * cᵢ`. -/
noncomputable def mu (g : ℕ) (i : Fin g) : A ⊗ Pw A g ⟶ A :=
  fst A (Pw A g) * (snd A (Pw A g) ≫ proj A g i)

/-- The family of translated intersections on `A × A^g`. -/
noncomputable def famI {g : ℕ} (D : Fin g → A.left.IdealSheafData) :
    (A ⊗ Pw A g).left.IdealSheafData :=
  ⨆ i, (D i).comap (mu A g i).left

/-- The section `x ↦ (x, c)` over a `k`-point `c` of `A^g`. -/
noncomputable def sec {g : ℕ} (c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A g) : A ⟶ A ⊗ Pw A g :=
  lift (𝟙 A) (toUnit A ≫ c)

theorem sec_mu {g : ℕ} (c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A g) (i : Fin g) :
    sec A c ≫ mu A g i = transl A (c ≫ proj A g i) := by
  simp only [mu, sec, transl, comp_mul, lift_fst, lift_snd_assoc, Category.assoc]

theorem comap_famI {g : ℕ} (D : Fin g → A.left.IdealSheafData)
    (c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A g) :
    (famI A D).comap (sec A c).left = Zid A D (fun i => c ≫ proj A g i) := by
  rw [famI, Zid, (Scheme.IdealSheafData.map_gc (sec A c).left).l_iSup]
  refine iSup_congr fun i => ?_
  try dsimp only
  rw [← Scheme.IdealSheafData.comap_comp, ← Over.comp_left, sec_mu]

omit [GrpObj A] in
/-- The section over `c` is the base change of the point `c` along `A ⊗ A^g → A^g`. -/
theorem isPullback_sec {g : ℕ} (c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A g) :
    IsPullback (sec A c).left A.hom (snd A (Pw A g)).left c.left := by
  have h1 : (sec A c).left ≫ (fst A (Pw A g)).left = 𝟙 _ := by
    rw [← Over.comp_left, sec, lift_fst, Over.id_left]
  have h2 : c.left ≫ (Pw A g).hom = 𝟙 (Spec (.of k)) := Over.w c
  have t : IsPullback (fst A (Pw A g)).left (snd A (Pw A g)).left A.hom (Pw A g).hom :=
    IsPullback.of_hasPullback A.hom (Pw A g).hom
  refine IsPullback.of_right (h₁₁ := (sec A c).left) ?_ ?_ t
  · rw [h1, h2]
    exact IsPullback.id_horiz A.hom
  · rw [← Over.comp_left, sec, lift_snd, Over.comp_left]; rfl

/-- The family over `A^g`: the subscheme `famI` mapped to the parameter space. -/
noncomputable def famP {g : ℕ} (D : Fin g → A.left.IdealSheafData) :
    (famI A D).subscheme ⟶ (Pw A g).left :=
  (famI A D).subschemeι ≫ (snd A (Pw A g)).left

/-- The fibre of the family over `c` is the subscheme `(famI A D).comap (sec A c)` over `Spec k`. -/
theorem isPullback_fibre {g : ℕ} (D : Fin g → A.left.IdealSheafData)
    (c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A g) :
    IsPullback (((famI A D).comapIso (sec A c).left).hom ≫ pullback.snd _ _)
      (((famI A D).comap (sec A c).left).subschemeι ≫ A.hom) (famP A D) c.left := by
  have s : IsPullback ((famI A D).comap (sec A c).left).subschemeι
      (((famI A D).comapIso (sec A c).left).hom ≫ pullback.snd _ _) (sec A c).left
      (famI A D).subschemeι :=
    IsPullback.of_iso_pullback ⟨by
      rw [Category.assoc, ← pullback.condition, Scheme.IdealSheafData.comapIso_hom_fst_assoc]⟩ _
      (Scheme.IdealSheafData.comapIso_hom_fst _ _) rfl
  exact s.flip.paste_vert (isPullback_sec A c)

end Family

/-- The length of a closed subscheme `J` of `A`: the rank of `J → Spec k` at the point. -/
noncomputable def len {k : Type u} [Field k] (A : Over (Spec (.of k))) (J : A.left.IdealSheafData) : ℕ :=
  Scheme.Hom.finrank (J.subschemeι ≫ A.hom) (pt0 k)

end RamanujanPetersson.IntersectA


end

-- ===== S4.Def_RP_IntersectA_GI =====
section

/-!
# S4-IntersectA, file GI: integral varieties over an algebraically closed field are geometrically integral

`geometricallyIntegral_of_isAlgClosed`: `X` integral and locally of finite type over `Spec k`, `k`
algebraically closed. Over a field `K ⊇ k`, the base change is covered by the opens
`Spec (B ⊗[k] K)` (charts `Spec B` of `X`), domains by `isDomain_tensor`; these opens are irreducible
and pairwise meet (the projection is surjective and `X` is irreducible), so the base change is integral.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace RamanujanPetersson.IntersectA

theorem irreducibleSpace_of_cover {Y : Type*} [TopologicalSpace Y] [Nonempty Y] {ι : Type*}
    (V : ι → Set Y) (hVo : ∀ i, IsOpen (V i)) (hV : ∀ i, IsPreirreducible (V i))
    (hcov : ∀ y, ∃ i, y ∈ V i) (hmeet : ∀ i j, (V i ∩ V j).Nonempty) : IrreducibleSpace Y := by
  refine { isPreirreducible_univ := ?_, toNonempty := ‹_› }
  rintro u v hu hv ⟨x, -, hx⟩ ⟨y, -, hy⟩
  obtain ⟨i, hxi⟩ := hcov x
  obtain ⟨j, hyj⟩ := hcov y
  obtain ⟨z, hzi, hzu, hzj⟩ := hV i u (V j) hu (hVo j) ⟨x, hxi, hx⟩ (hmeet i j)
  obtain ⟨w, -, ⟨hwu, -⟩, hwv⟩ :=
    hV j (u ∩ V i) v (hu.inter (hVo i)) hv ⟨z, hzj, hzu, hzi⟩ ⟨y, hyj, hy⟩
  exact ⟨w, trivial, hwu, hwv⟩

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsIntegral X] [LocallyOfFiniteType f]

end RamanujanPetersson.IntersectA


end

-- ===== S4.Def_RP_IntersectA_Prod =====
section

/-!
# S4-IntersectA, file Prod: products of integral varieties over an algebraically closed field

Mathlib's `IsIntegral (pullback f g)` instance asks for `UniversallyOpen g`, which this Mathlib cannot
supply. We redo the chart argument of file GI with the field `K` replaced by a `k`-domain `C`
(`isIntegral_of_isPullback_domain`), then cover `S` by affine charts `Spec C`:
`isIntegral_pullback f g` for `X` integral, locally of finite type over `Spec k` and `S` integral.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace RamanujanPetersson.IntersectA

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsIntegral X] [LocallyOfFiniteType f]

include f in
/-- A nonempty affine chart of `X`, base changed to a `k`-domain `C`, is integral. -/
theorem isIntegral_chart_domain {C : Type u} [CommRing C] [IsDomain C] [Algebra k C] {Y : Scheme.{u}}
    {fst : Y ⟶ X} {snd : Y ⟶ Spec (.of C)}
    (h : IsPullback fst snd f (Spec.map (CommRingCat.ofHom (algebraMap k C))))
    {B : CommRingCat.{u}} (v : Spec B ⟶ X) (hv : IsOpenImmersion v) (hB : Nonempty (Spec B)) :
    IsIntegral (pullback fst v) := by
  have := hv
  have := hB
  have : IsIntegral (Spec B) := isIntegral_of_isOpenImmersion v
  have : IsDomain B := (affine_isIntegral_iff B).mp inferInstance
  set φ : CommRingCat.of k ⟶ B := Spec.preimage (v ≫ f)
  have hφ : Spec.map φ = v ≫ f := Spec.map_preimage _
  letI : Algebra k B := φ.hom.toAlgebra
  have : Algebra.FiniteType k B := by
    have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this
  have : IsDomain (B ⊗[k] C) := JacSym.isDomain_tensor
  have hT := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct k B C)
  have hP := (IsPullback.of_hasPullback fst v).flip.paste_vert h
  rw [← hφ] at hP
  let e := hP.isoIsPullback _ _ hT
  obtain ⟨t⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of (B ⊗[k] C))))
  have : Nonempty (pullback fst v : Scheme.{u}) := ⟨e.inv t⟩
  exact isIntegral_of_isOpenImmersion e.hom

/-- The base change of `X` to a `k`-domain `C` is integral. -/
theorem isIntegral_of_isPullback_domain {C : Type u} [CommRing C] [IsDomain C] [Algebra k C]
    {Y : Scheme.{u}} {fst : Y ⟶ X} {snd : Y ⟶ Spec (.of C)}
    (h : IsPullback fst snd f (Spec.map (CommRingCat.ofHom (algebraMap k C)))) : IsIntegral Y := by
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k C))) :=
    ⟨fun x => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  have hfst : Surjective fst :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective) h.flip inferInstance
  have key : ∀ i, Nonempty (X.affineCover.X i) → IsIntegral (pullback fst (X.affineCover.f i)) :=
    fun i hi => isIntegral_chart_domain f h (X.affineCover.f i) (X.affineCover.map_prop i) hi
  have hc : ∀ x, Nonempty (X.affineCover.X (X.affineCover.idx x)) := fun x =>
    ⟨(X.affineCover.covers x).choose⟩
  obtain ⟨x0⟩ := (inferInstance : Nonempty X)
  obtain ⟨y0, hy0⟩ := fst.surjective x0
  have : Nonempty Y := ⟨y0⟩
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  refine ⟨irreducibleSpace_of_cover
    (fun x => Set.range (pullback.fst fst (X.affineCover.f (X.affineCover.idx x))))
    (fun x => (pullback.fst fst _).isOpenEmbedding.isOpen_range)
    (fun x => ?_) (fun y => ?_) (fun x x' => ?_), ?_⟩
  · have := key _ (hc x)
    simpa [Set.image_univ] using ((IrreducibleSpace.isIrreducible_univ _).image _
      (pullback.fst fst (X.affineCover.f (X.affineCover.idx x))).continuous.continuousOn).isPreirreducible
  · obtain ⟨z, hz⟩ := X.affineCover.covers (fst y)
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback y z hz.symm
    exact ⟨fst y, w, hw⟩
  · obtain ⟨x1, ⟨z, hz⟩, ⟨z', hz'⟩⟩ := nonempty_preirreducible_inter
      (X.affineCover.f (X.affineCover.idx x)).isOpenEmbedding.isOpen_range
      (X.affineCover.f (X.affineCover.idx x')).isOpenEmbedding.isOpen_range
      ⟨_, (X.affineCover.covers x)⟩ ⟨_, (X.affineCover.covers x')⟩
    obtain ⟨y, rfl⟩ := fst.surjective x1
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback y z hz.symm
    obtain ⟨w', hw', -⟩ := Scheme.Pullback.exists_preimage_pullback y z' hz'.symm
    exact ⟨y, ⟨w, hw⟩, ⟨w', hw'⟩⟩
  · have : ∀ i, IsReduced ((X.affineCover.pullback₁ fst).X i) := fun i => by
      change IsReduced (pullback fst (X.affineCover.f i))
      by_cases hi : Nonempty (X.affineCover.X i)
      · have := key i hi
        infer_instance
      · have : IsEmpty (pullback fst (X.affineCover.f i) : Scheme.{u}) :=
          ⟨fun w => hi ⟨pullback.snd fst (X.affineCover.f i) w⟩⟩
        have : ∀ w : (pullback fst (X.affineCover.f i) : Scheme.{u}),
            _root_.IsReduced ((pullback fst (X.affineCover.f i)).presheaf.stalk w) :=
          fun w => isEmptyElim w
        exact isReduced_of_isReduced_stalk _
    exact IsReduced.of_openCover (𝒰 := X.affineCover.pullback₁ fst)

/-- A nonempty affine chart `Spec B` of an integral `S` gives an integral open `X ×ₖ Spec B`. -/
theorem isIntegral_chart_prod {S : Scheme.{u}} (g : S ⟶ Spec (.of k)) [IsIntegral S]
    {B : CommRingCat.{u}} (v : Spec B ⟶ S) (hv : IsOpenImmersion v) (hB : Nonempty (Spec B)) :
    IsIntegral (pullback (pullback.snd f g) v) := by
  have := hv
  have := hB
  have : IsIntegral (Spec B) := isIntegral_of_isOpenImmersion v
  have : IsDomain B := (affine_isIntegral_iff B).mp inferInstance
  set φ : CommRingCat.of k ⟶ B := Spec.preimage (v ≫ g)
  have hφ : Spec.map φ = v ≫ g := Spec.map_preimage _
  letI : Algebra k B := φ.hom.toAlgebra
  have hP := ((IsPullback.of_hasPullback (pullback.snd f g) v).flip.paste_vert
    (IsPullback.of_hasPullback f g).flip).flip
  rw [← hφ] at hP
  exact isIntegral_of_isPullback_domain f (C := B) hP

/-- `X ×ₖ S` is integral for `X` integral and locally of finite type over `k`, and `S` integral. -/
theorem isIntegral_pullback {S : Scheme.{u}} (g : S ⟶ Spec (.of k)) [IsIntegral S] :
    IsIntegral (pullback f g) := by
  have key : ∀ j, Nonempty (S.affineCover.X j) →
      IsIntegral (pullback (pullback.snd f g) (S.affineCover.f j)) :=
    fun j hj => isIntegral_chart_prod f g (S.affineCover.f j) (S.affineCover.map_prop j) hj
  have hc : ∀ y, Nonempty (S.affineCover.X (S.affineCover.idx y)) := fun y =>
    ⟨(S.affineCover.covers y).choose⟩
  obtain ⟨x0⟩ := (inferInstance : Nonempty X)
  obtain ⟨y0⟩ := (inferInstance : Nonempty S)
  obtain ⟨w0, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x0 y0
    (Subsingleton.elim _ _)
  have : Nonempty (pullback f g : Scheme.{u}) := ⟨w0⟩
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  refine ⟨irreducibleSpace_of_cover
    (fun y => Set.range (pullback.fst (pullback.snd f g) (S.affineCover.f (S.affineCover.idx y))))
    (fun y => (pullback.fst (pullback.snd f g) _).isOpenEmbedding.isOpen_range)
    (fun y => ?_) (fun w => ?_) (fun y y' => ?_), ?_⟩
  · have := key _ (hc y)
    simpa [Set.image_univ] using ((IrreducibleSpace.isIrreducible_univ _).image _
      (pullback.fst (pullback.snd f g)
        (S.affineCover.f (S.affineCover.idx y))).continuous.continuousOn).isPreirreducible
  · obtain ⟨z, hz⟩ := S.affineCover.covers (pullback.snd f g w)
    obtain ⟨w', hw', -⟩ := Scheme.Pullback.exists_preimage_pullback w z hz.symm
    exact ⟨pullback.snd f g w, w', hw'⟩
  · obtain ⟨y1, ⟨z, hz⟩, ⟨z', hz'⟩⟩ := nonempty_preirreducible_inter
      (S.affineCover.f (S.affineCover.idx y)).isOpenEmbedding.isOpen_range
      (S.affineCover.f (S.affineCover.idx y')).isOpenEmbedding.isOpen_range
      ⟨_, (S.affineCover.covers y)⟩ ⟨_, (S.affineCover.covers y')⟩
    obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x0 y1
      (Subsingleton.elim _ _)
    obtain ⟨u1, hu1, -⟩ := Scheme.Pullback.exists_preimage_pullback w z (hw.trans hz.symm)
    obtain ⟨u2, hu2, -⟩ := Scheme.Pullback.exists_preimage_pullback w z' (hw.trans hz'.symm)
    exact ⟨w, ⟨u1, hu1⟩, ⟨u2, hu2⟩⟩
  · have : ∀ j, IsReduced ((S.affineCover.pullback₁ (pullback.snd f g)).X j) := fun j => by
      change IsReduced (pullback (pullback.snd f g) (S.affineCover.f j))
      by_cases hj : Nonempty (S.affineCover.X j)
      · have := key j hj
        infer_instance
      · have : IsEmpty (pullback (pullback.snd f g) (S.affineCover.f j) : Scheme.{u}) :=
          ⟨fun w => hj ⟨pullback.snd (pullback.snd f g) (S.affineCover.f j) w⟩⟩
        have : ∀ w : (pullback (pullback.snd f g) (S.affineCover.f j) : Scheme.{u}),
            _root_.IsReduced ((pullback (pullback.snd f g) (S.affineCover.f j)).presheaf.stalk w) :=
          fun w => isEmptyElim w
        exact isReduced_of_isReduced_stalk _
    exact IsReduced.of_openCover (𝒰 := S.affineCover.pullback₁ (pullback.snd f g))

end RamanujanPetersson.IntersectA


end

-- ===== S4.Def_RP_IntersectA_PwInst =====
section

/-!
# S4-IntersectA, file PwInst: the parameter space `A^n` and the family over it

`A^n` is proper over `k`, integral (`isIntegral_pullback`) and locally Noetherian; `A` is a
Noetherian space. The family `famP A D` is proper, and its fibre over the point with coordinates
`a0` is finite once the intersection `Zid A D a0` has finite support (`finite_fibre`).
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory Limits
  TopologicalSpace

namespace RamanujanPetersson.IntersectA

open RamanujanPetersson.IsogDegA

variable {k : Type u} [Field k] (A : Over (Spec (.of k)))

theorem isProper_Pw [IsProper A.hom] (n : ℕ) : IsProper (Pw A n).hom := by
  induction n with
  | zero => exact (inferInstance : IsProper (𝟙 (Spec (.of k))))
  | succ n ih =>
    have := ih
    exact (inferInstance : IsProper (pullback.fst (Pw A n).hom A.hom ≫ (Pw A n).hom))

theorem isIntegral_Pw [IsAlgClosed k] [IsProper A.hom] [IsIntegral A.left] (n : ℕ) :
    IsIntegral (Pw A n).left := by
  induction n with
  | zero => exact (inferInstance : IsIntegral (Spec (.of k)))
  | succ n ih =>
    have := ih
    have := isProper_Pw A n
    exact isIntegral_pullback (Pw A n).hom A.hom

theorem isLocallyNoetherian_Pw [IsProper A.hom] (n : ℕ) : IsLocallyNoetherian (Pw A n).left := by
  have := isProper_Pw A n
  exact LocallyOfFiniteType.isLocallyNoetherian (Pw A n).hom

theorem noetherianSpace_left [IsProper A.hom] : NoetherianSpace A.left := by
  have := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : IsNoetherian A.left := by constructor
  infer_instance

variable [GrpObj A]

theorem isProper_famP [IsProper A.hom] {g : ℕ} (D : Fin g → A.left.IdealSheafData) :
    IsProper (famP A D) := by
  change IsProper ((famI A D).subschemeι ≫ pullback.snd A.hom (Pw A g).hom)
  infer_instance

/-- The fibre of the family over the point with coordinates `a0` is finite when `Zid A D a0` is. -/
theorem finite_fibre {g : ℕ} (D : Fin g → A.left.IdealSheafData)
    (a0 : Fin g → (𝟙_ (Over (Spec (.of k))) ⟶ A)) (ha0 : ((Zid A D a0).support : Set A.left).Finite) :
    (famP A D ⁻¹' {pt (Pw A g) (ptOf A g a0)}).Finite := by
  have hJ : (famI A D).comap (sec A (ptOf A g a0)).left = Zid A D a0 := by
    rw [comap_famI]
    congr 1
    funext i
    exact ptOf_proj A g a0 i
  have h := isPullback_fibre A D (ptOf A g a0)
  have : Finite ((famI A D).comap (sec A (ptOf A g a0)).left).subscheme := by
    refine Set.finite_univ_iff.mp (Set.Finite.of_finite_image ?_
      ((famI A D).comap (sec A (ptOf A g a0)).left).subschemeι.isClosedEmbedding.injective.injOn)
    rw [Set.image_univ, Scheme.IdealSheafData.range_subschemeι, hJ]
    exact ha0
  refine (Set.finite_range
    (((famI A D).comapIso (sec A (ptOf A g a0)).left).hom ≫ pullback.snd _ _)).subset ?_
  intro z hz
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := famP A D)
    (g := (ptOf A g a0).left) z (pt0 k) hz
  refine ⟨h.isoPullback.inv w, ?_⟩
  rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hw]

end RamanujanPetersson.IntersectA


end

-- ===== S4.Def_RP_IntersectA_Cons =====
section

/-!
# S4-IntersectA, file Cons: generic flatness of a finite morphism

`GoodNbhd p`: an open `j : T ⟶ Y` (nonempty) over which `p : Z ⟶ Y` becomes finite flat of constant rank.
`exists_free_away`: a finite algebra `S` over a Noetherian domain `R` becomes free after inverting one
`r ≠ 0`. Hence `goodNbhd_SpecMap` (finite `Spec S → Spec R`), `goodNbhd_of_isFinite` (finite `q` over an
integral locally Noetherian base) and `goodNbhd_of_isProper` (proper `p` with one finite fibre, by
Zariski's main theorem `exists_isFinite_morphismRestrict_of_finite_preimage_singleton`).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace RamanujanPetersson.IntersectA

theorem exists_free_away {R S : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] [Module.Finite R S] :
    ∃ r : R, r ≠ 0 ∧ Module.Free (Localization.Away r) (Localization.Away r ⊗[R] S) := by
  haveI : Module.FinitePresentation R S := Module.finitePresentation_of_finite R S
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (nonZeroDivisors R) (LocalizedModule.mkLinearMap (nonZeroDivisors R) S) (FractionRing R)
  refine ⟨r, nonZeroDivisors.ne_zero hr, ?_⟩
  exact Module.Free.of_equiv (IsLocalizedModule.isBaseChange (Submonoid.powers r)
    (Localization.Away r) (LocalizedModule.mkLinearMap (Submonoid.powers r) S)).equiv.symm

/-- A nonempty open `j : T ⟶ Y` over which `p` is finite flat of constant rank `n`. -/
def GoodNbhd {Z Y : Scheme.{u}} (p : Z ⟶ Y) : Prop :=
  ∃ (T W : Scheme.{u}) (j : T ⟶ Y) (i : W ⟶ Z) (q : W ⟶ T), IsOpenImmersion j ∧ Nonempty T ∧
    IsPullback i q p j ∧ Flat q ∧ IsFinite q ∧ ∃ n : ℕ, ∀ t, q.finrank t = n

theorem GoodNbhd.of_isPullback {Z Y Z' Y' : Scheme.{u}} {p : Z ⟶ Y} {p' : Z' ⟶ Y'} {i' : Z' ⟶ Z}
    {j' : Y' ⟶ Y} [IsOpenImmersion j'] (h : IsPullback i' p' p j') (hp : GoodNbhd p') :
    GoodNbhd p := by
  obtain ⟨T, W, j, i, q, hj, hT, hsq, hfl, hfin, n, hn⟩ := hp
  haveI := hj
  exact ⟨T, W, j ≫ j', i ≫ i', q, inferInstance, hT, hsq.paste_horiz h, hfl, hfin, n, hn⟩

theorem goodNbhd_SpecMap {R S : CommRingCat.{u}} [IsDomain R] [IsNoetherianRing R] (φ : R ⟶ S)
    (hφ : φ.hom.Finite) : GoodNbhd (Spec.map φ) := by
  letI : Algebra R S := φ.hom.toAlgebra
  haveI : Module.Finite R S := hφ
  obtain ⟨r, hr, hfree⟩ := exists_free_away (R := R) (S := S)
  haveI : IsDomain (Localization.Away r) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hr)
  have hsq := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R (Localization.Away r) S)).flip
  have e : (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom :
      CommRingCat.of (Localization.Away r) ⟶ CommRingCat.of (Localization.Away r ⊗[R] S)) =
      CommRingCat.ofHom (algebraMap (Localization.Away r) (Localization.Away r ⊗[R] S)) := rfl
  rw [e] at hsq
  refine ⟨_, _, _, _, _, inferInstance, inferInstance, hsq, ?_, ?_,
    Module.finrank (Localization.Away r) (Localization.Away r ⊗[R] S), fun t => ?_⟩
  · exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  · exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  · refine (Scheme.Hom.finrank_SpecMap_algebraMap (Localization.Away r)
      (Localization.Away r ⊗[R] S) t).trans ?_
    rw [Module.rankAtStalk_eq_finrank_of_free]
    exact Pi.natCast_apply _ t

/-- Finite over an affine integral locally Noetherian base. -/
theorem goodNbhd_of_isAffine {W T : Scheme.{u}} (q : W ⟶ T) [IsFinite q] [IsAffine T]
    [IsIntegral T] [IsLocallyNoetherian T] : GoodNbhd q := by
  haveI : IsAffine W := isAffine_of_isAffineHom q
  haveI : IsNoetherianRing Γ(T, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top T⟩
  have hsq : IsPullback W.isoSpec.inv (Spec.map q.appTop) q T.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨by rw [Iso.inv_comp_eq, ← Category.assoc,
      Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩
  exact GoodNbhd.of_isPullback hsq (goodNbhd_SpecMap q.appTop q.finite_appTop)

/-- Finite over an integral locally Noetherian base. -/
theorem goodNbhd_of_isFinite {W T : Scheme.{u}} (q : W ⟶ T) [IsFinite q] [IsIntegral T]
    [IsLocallyNoetherian T] : GoodNbhd q := by
  obtain ⟨t⟩ := (inferInstance : Nonempty T)
  obtain ⟨R, u, hu, y, -⟩ := T.exists_Spec_apply_eq t
  haveI := hu
  haveI : Nonempty (Spec R) := ⟨y⟩
  haveI : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion u
  haveI : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_of_isOpenImmersion u
  exact GoodNbhd.of_isPullback (IsPullback.of_hasPullback q u)
    (goodNbhd_of_isAffine (pullback.snd q u))

/-- Proper with one finite fibre, over an integral locally Noetherian base (generic flatness). -/
theorem goodNbhd_of_isProper {Z Y : Scheme.{u}} (p : Z ⟶ Y) [IsProper p] [IsIntegral Y]
    [IsLocallyNoetherian Y] (y : Y) (hy : (p ⁻¹' {y}).Finite) : GoodNbhd p := by
  obtain ⟨V, hyV, hV⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton p y hy
  haveI := hV
  haveI : Nonempty V := ⟨⟨y, hyV⟩⟩
  haveI : IsIntegral V := isIntegral_of_isOpenImmersion V.ι
  exact GoodNbhd.of_isPullback (isPullback_morphismRestrict p V).flip
    (goodNbhd_of_isFinite (p ∣_ V))

end RamanujanPetersson.IntersectA


end

-- ===== S4.Def_RP_IntersectA =====
section

/-!
# S4-IntersectA: intersection numbers at generic translates (L31-L32)

`A` is an integral group scheme, proper over an algebraically closed field `k`, all of whose points
have height `≤ g`; `D : Fin g → A.left.IdealSheafData` are proper closed subschemes. For a `k`-point
`c` of `A^g`, `Zid A D (c ≫ proj A g ·)` is the intersection of the translates `D i · cᵢ`.

* `exists_inum` (L31-L32): there are `n` and a nonempty open `U ⊆ A^g` such that for every `k`-point
  `c ∈ U` the intersection is finite and has length `n` (generic flatness of the family `famP`).
* `inum A g hdim D hD` is this `n`, the intersection number `(D_1 ⋯ D_g)`; `inum_spec` and
  `inum_unique` (any nonempty open with a constant length gives `inum`).
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory Limits
  TopologicalSpace

namespace RamanujanPetersson.IntersectA

open RamanujanPetersson.IsogDegA

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- Over the open image of a good neighbourhood, every fibre is finite of length `n`. -/
theorem fibre_of_goodNbhd {g : ℕ} (D : Fin g → A.left.IdealSheafData) {T W : Scheme.{u}}
    (j : T ⟶ (Pw A g).left) [IsOpenImmersion j] (i0 : W ⟶ (famI A D).subscheme) (q : W ⟶ T)
    (hsq : IsPullback i0 q (famP A D) j) [Flat q] [IsFinite q] (n : ℕ)
    (hn : ∀ t, q.finrank t = n) (c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A g)
    (hc : pt (Pw A g) c ∈ Set.range j) :
    ((Zid A D (fun i => c ≫ proj A g i)).support : Set A.left).Finite ∧
      len A (Zid A D (fun i => c ≫ proj A g i)) = n := by
  have H : Set.range c.left ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim (α := Spec (.of k)) x (pt0 k)]
    exact hc
  have s : IsPullback (((famI A D).comapIso (sec A c).left).hom ≫ pullback.snd _ _)
      (((famI A D).comap (sec A c).left).subschemeι ≫ A.hom) (famP A D)
      (IsOpenImmersion.lift j c.left H ≫ j) := by
    rw [IsOpenImmersion.lift_fac]
    exact isPullback_fibre A D c
  have S := IsPullback.of_right' s hsq
  have : IsFinite (((famI A D).comap (sec A c).left).subschemeι ≫ A.hom) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsFinite) S inferInstance
  rw [← comap_famI]
  refine ⟨?_, ?_⟩
  · have hf := (((famI A D).comap (sec A c).left).subschemeι ≫ A.hom).finite_preimage_singleton
      (pt0 k)
    have hu : (((famI A D).comap (sec A c).left).subschemeι ≫ A.hom) ⁻¹' {pt0 k} = Set.univ :=
      Set.eq_univ_of_forall fun x => by
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact Subsingleton.elim _ _
    rw [hu] at hf
    have := Set.finite_univ_iff.mp hf
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact Set.finite_range _
  · show Scheme.Hom.finrank _ (pt0 k) = n
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ S (pt0 k)]
    exact hn _

variable [IsAlgClosed k] [IsProper A.hom] [IsIntegral A.left]

/-- L31-L32: on a nonempty open of `A^g`, the translated intersections are finite of constant
length. -/
theorem exists_inum (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g)
    (D : Fin g → A.left.IdealSheafData) (hD : ∀ i, (D i).support ≠ ⊤) :
    ∃ n : ℕ, ∃ U : Set (Pw A g).left, IsOpen U ∧ U.Nonempty ∧
      ∀ c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A g, pt (Pw A g) c ∈ U →
        ((Zid A D (fun i => c ≫ proj A g i)).support : Set A.left).Finite ∧
          len A (Zid A D (fun i => c ≫ proj A g i)) = n := by
  have := noetherianSpace_left A
  have := isIntegral_Pw A g
  have := isLocallyNoetherian_Pw A g
  have := isProper_famP A D
  obtain ⟨a0, ha0, -⟩ := exists_finite_support A g hdim D hD
  obtain ⟨T, W, j, i0, q, hj, hT, hsq, hflat, hfin, n, hn⟩ :=
    goodNbhd_of_isProper (famP A D) _ (finite_fibre A D a0 ha0)
  have := hj
  have := hT
  have := hflat
  have := hfin
  exact ⟨n, Set.range j, j.isOpenEmbedding.isOpen_range, Set.range_nonempty j,
    fun c hc => fibre_of_goodNbhd A D j i0 q hsq n hn c hc⟩

/-- The intersection number `(D_1 ⋯ D_g)`: the length of the intersection of generic translates. -/
noncomputable def inum (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g)
    (D : Fin g → A.left.IdealSheafData) (hD : ∀ i, (D i).support ≠ ⊤) : ℕ :=
  Classical.choose (exists_inum A g hdim D hD)

theorem inum_spec (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g)
    (D : Fin g → A.left.IdealSheafData) (hD : ∀ i, (D i).support ≠ ⊤) :
    ∃ U : Set (Pw A g).left, IsOpen U ∧ U.Nonempty ∧
      ∀ c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A g, pt (Pw A g) c ∈ U →
        ((Zid A D (fun i => c ≫ proj A g i)).support : Set A.left).Finite ∧
          len A (Zid A D (fun i => c ≫ proj A g i)) = inum A g hdim D hD :=
  Classical.choose_spec (exists_inum A g hdim D hD)

/-- Any nonempty open of `A^g` on which the length is constant computes `inum`. -/
theorem inum_unique (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g)
    (D : Fin g → A.left.IdealSheafData) (hD : ∀ i, (D i).support ≠ ⊤) (n : ℕ)
    (U : Set (Pw A g).left) (hU : IsOpen U) (hne : U.Nonempty)
    (h : ∀ c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A g, pt (Pw A g) c ∈ U →
      len A (Zid A D (fun i => c ≫ proj A g i)) = n) :
    n = inum A g hdim D hD := by
  obtain ⟨U', hU', hne', h'⟩ := inum_spec A g hdim D hD
  have := isIntegral_Pw A g
  have := isProper_Pw A g
  obtain ⟨c, hc⟩ := exists_pt_mem (Pw A g) (U ∩ U') (hU.inter hU').isLocallyClosed
    (nonempty_preirreducible_inter hU hU' hne hne')
  rw [← h c hc.1, (h' c hc.2).2]

end RamanujanPetersson.IntersectA


end

-- ===== S4.Def_RP_IntersectB_Sym =====
section

/-!
# S4-IntersectB, file Sym: symmetry and translation invariance of `inum` (L33, part 1)

`liftPw` builds maps into `A^n` from their coordinates (`liftPw_proj`, `Pw_hom_ext`).
`inum_eq_of_reparam`: an automorphism `ψ` of the parameter space `A^g` that carries the translated
intersections of `D'` to those of `D` gives `inum D' = inum D`. Applied to coordinate permutations
(`inum_perm`) and coordinatewise translations (`inum_shift`).
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory Limits

namespace RamanujanPetersson.IntersectB

open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA

section Lift

variable {k : Type u} [Field k] (A : Over (Spec (.of k)))

/-- A map into `A^n` with the given coordinates. -/
noncomputable def liftPw : (n : ℕ) → {X : Over (Spec (.of k))} → (Fin n → (X ⟶ A)) → (X ⟶ Pw A n)
  | 0, X, _ => toUnit X
  | n + 1, _, f => lift (liftPw n (Fin.init f)) (f (Fin.last n))

theorem liftPw_proj (n : ℕ) {X : Over (Spec (.of k))} (f : Fin n → (X ⟶ A)) (i : Fin n) :
    liftPw A n f ≫ proj A n i = f i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    induction i using Fin.lastCases with
    | last => rw [proj_last]; exact lift_snd _ _
    | cast j =>
      rw [proj_castSucc]
      exact ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ proj A n j) (lift_fst _ _))).trans (ih _ j)

theorem Pw_hom_ext (n : ℕ) {X : Over (Spec (.of k))} (f f' : X ⟶ Pw A n)
    (h : ∀ i, f ≫ proj A n i = f' ≫ proj A n i) : f = f' := by
  induction n with
  | zero => exact toUnit_unique _ _
  | succ n ih =>
    refine CartesianMonoidalCategory.hom_ext (X := Pw A n) (Y := A) _ _ ?_ ?_
    · refine ih _ _ fun j => ?_
      have hj := h j.castSucc
      rw [proj_castSucc] at hj
      exact (Category.assoc _ _ _).trans (hj.trans (Category.assoc _ _ _).symm)
    · have hl := h (Fin.last n)
      rw [proj_last] at hl
      exact hl

theorem surjective_left_of_comp_eq_id {X Y : Over (Spec (.of k))} (ψ : X ⟶ Y) (ψ' : Y ⟶ X)
    (h : ψ' ≫ ψ = 𝟙 Y) : Function.Surjective ψ.left := by
  intro y
  refine ⟨ψ'.left y, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h]
  rfl

/-- Permutation of the coordinates of `A^g`. -/
noncomputable def permPw (g : ℕ) (σ : Equiv.Perm (Fin g)) : Pw A g ⟶ Pw A g :=
  liftPw A g (fun j => proj A g (σ.symm j))

theorem permPw_proj (g : ℕ) (σ : Equiv.Perm (Fin g)) (j : Fin g) :
    permPw A g σ ≫ proj A g j = proj A g (σ.symm j) :=
  liftPw_proj A g _ j

theorem permPw_inv (g : ℕ) (σ : Equiv.Perm (Fin g)) :
    permPw A g σ.symm ≫ permPw A g σ = 𝟙 _ :=
  Pw_hom_ext A g _ _ fun j => by
    rw [Category.assoc, permPw_proj, permPw_proj, Equiv.symm_symm, Equiv.apply_symm_apply,
      Category.id_comp]

/-- Coordinatewise right translation of `A^g`. -/
noncomputable def shiftPw (g : ℕ) (b : Fin g → (𝟙_ (Over (Spec (.of k))) ⟶ A)) [GrpObj A] :
    Pw A g ⟶ Pw A g :=
  liftPw A g (fun j => proj A g j ≫ transl A (b j))

theorem shiftPw_proj (g : ℕ) (b : Fin g → (𝟙_ (Over (Spec (.of k))) ⟶ A)) [GrpObj A] (j : Fin g) :
    shiftPw A g b ≫ proj A g j = proj A g j ≫ transl A (b j) :=
  liftPw_proj A g _ j

theorem shiftPw_inv (g : ℕ) (b : Fin g → (𝟙_ (Over (Spec (.of k))) ⟶ A)) [GrpObj A] :
    shiftPw A g (fun j => (b j)⁻¹) ≫ shiftPw A g b = 𝟙 _ :=
  Pw_hom_ext A g _ _ fun j => by
    rw [Category.assoc, shiftPw_proj, ← Category.assoc, shiftPw_proj, Category.assoc,
      transl_comp_transl, _root_.inv_mul_cancel, transl_one, Category.comp_id, Category.id_comp]

end Lift

section Reparam

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left]

/-- Reparametrising the translations by a surjective endomorphism of `A^g` does not change `inum`. -/
theorem inum_eq_of_reparam (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g)
    (D D' : Fin g → A.left.IdealSheafData) (hD : ∀ i, (D i).support ≠ ⊤)
    (hD' : ∀ i, (D' i).support ≠ ⊤) (ψ : Pw A g ⟶ Pw A g) (hψ : Function.Surjective ψ.left)
    (h : ∀ c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A g,
      Zid A D' (fun i => c ≫ proj A g i) = Zid A D (fun i => (c ≫ ψ) ≫ proj A g i)) :
    inum A g hdim D' hD' = inum A g hdim D hD := by
  obtain ⟨U, hU, hne, hc⟩ := inum_spec A g hdim D hD
  refine (inum_unique A g hdim D' hD' _ (ψ.left ⁻¹' U) (hU.preimage ψ.left.continuous) ?_ ?_).symm
  · obtain ⟨y, hy⟩ := hne
    obtain ⟨x, rfl⟩ := hψ y
    exact ⟨x, hy⟩
  · intro c hcU
    rw [h c]
    exact (hc (c ≫ ψ) (by rw [pt_comp]; exact hcU)).2

/-- B1 (symmetry): `inum` is invariant under permuting the divisors. -/
theorem inum_perm (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g)
    (D : Fin g → A.left.IdealSheafData) (hD : ∀ i, (D i).support ≠ ⊤) (σ : Equiv.Perm (Fin g)) :
    inum A g hdim (fun i => D (σ i)) (fun i => hD (σ i)) = inum A g hdim D hD := by
  refine inum_eq_of_reparam A g hdim D _ hD _ (permPw A g σ)
    (surjective_left_of_comp_eq_id _ _ (permPw_inv A g σ)) fun c => ?_
  simp only [Zid]
  refine (iSup_congr fun i => ?_).trans (Equiv.iSup_comp (g := fun j =>
    (D j).comap (transl A ((c ≫ permPw A g σ) ≫ proj A g j)).left) σ)
  rw [Category.assoc, permPw_proj, Equiv.symm_apply_apply]

theorem support_comap_transl_ne_top (I : A.left.IdealSheafData) (hI : I.support ≠ ⊤)
    (b : 𝟙_ (Over (Spec (.of k))) ⟶ A) : (I.comap (transl A b).left).support ≠ ⊤ := by
  intro h
  apply hI
  refine eq_top_iff.mpr fun x _ => ?_
  have hx : (transl A b).left ((transl A b⁻¹).left x) = x := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, transl_comp_transl, _root_.inv_mul_cancel,
      transl_one]
    rfl
  have hy : (transl A b⁻¹).left x ∈ (I.comap (transl A b).left).support := by
    rw [h]; exact Set.mem_univ _
  rw [Scheme.IdealSheafData.support_comap] at hy
  rw [← hx]
  exact hy

/-- B2 (translation invariance): translating the divisors does not change `inum`. -/
theorem inum_shift (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g)
    (D : Fin g → A.left.IdealSheafData) (hD : ∀ i, (D i).support ≠ ⊤)
    (b : Fin g → (𝟙_ (Over (Spec (.of k))) ⟶ A)) :
    inum A g hdim (fun i => (D i).comap (transl A (b i)).left)
      (fun i => support_comap_transl_ne_top A (D i) (hD i) (b i)) = inum A g hdim D hD := by
  refine inum_eq_of_reparam A g hdim D _ hD _ (shiftPw A g b)
    (surjective_left_of_comp_eq_id _ _ (shiftPw_inv A g b)) fun c => ?_
  simp only [Zid]
  refine iSup_congr fun i => ?_
  rw [← Scheme.IdealSheafData.comap_comp, ← Over.comp_left, transl_comp_transl, Category.assoc,
    shiftPw_proj, ← Category.assoc, point_comp_transl]

end Reparam

end RamanujanPetersson.IntersectB


end

-- ===== S4.Def_RP_IntersectB_Aff =====
section

/-!
# S4-IntersectB, file Aff: affine charts for finite subschemes (L33, part 2)

* `exists_affine_mem`: on a group scheme, any finite set of points lies in one affine open.
* `algV`, `algV_spec`: the `k`-algebra structure on sections over an affine open.
* `len_eq_finrank`: a closed subscheme with finite support inside an affine open `V` has
  `len = finrank_k (Γ(V) ⧸ J(V))`, and this quotient is finite over `k`.
* `comap_mul_of_isIso`: pulling back ideal sheaves along an isomorphism preserves products.
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory Limits
  TopologicalSpace

namespace RamanujanPetersson.IntersectB

open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA

section Aff

variable {k : Type u} [Field k] (A : Over (Spec (.of k)))

/-- Translations are isomorphisms (as in `IsogDegA_QF`, which this file does not import). -/
theorem isIso_translL [GrpObj A] (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) : IsIso (transl A a).left :=
  ⟨⟨(transl A a⁻¹).left, by
    rw [← Over.comp_left, transl_comp_transl, _root_.mul_inv_cancel, transl_one, Over.id_left], by
    rw [← Over.comp_left, transl_comp_transl, _root_.inv_mul_cancel, transl_one, Over.id_left]⟩⟩

/-- (a) Finitely many points of a group scheme lie in one affine open. -/
theorem exists_affine_mem [GrpObj A] [IsAlgClosed k] [LocallyOfFiniteType A.hom]
    [IrreducibleSpace A.left] (S : Finset A.left) :
    ∃ V : A.left.affineOpens, ∀ x ∈ S, x ∈ (V : A.left.Opens) := by
  obtain ⟨x0⟩ : Nonempty A.left := inferInstance
  obtain ⟨_, ⟨V0, hV0, rfl⟩, hx0, -⟩ :=
    A.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x0) isOpen_univ
  have hD : IsClosed (V0 : Set A.left)ᶜ := V0.isOpen.isClosed_compl
  have hne : (V0 : Set A.left)ᶜ ≠ Set.univ := by
    intro h
    have h1 : x0 ∈ (V0 : Set A.left)ᶜ := h ▸ Set.mem_univ x0
    exact h1 hx0
  obtain ⟨a, ha⟩ := exists_good A S _ hD hne
  have := isIso_translL A a
  refine ⟨⟨(transl A a).left ⁻¹ᵁ V0, hV0.preimage_of_isIso _⟩, fun x hx => ?_⟩
  have := ha x hx
  simpa using this

/-- The `k`-algebra structure on the sections of `A` over an affine open. -/
noncomputable def algV (V : A.left.affineOpens) : CommRingCat.of k ⟶ Γ(A.left, V) :=
  Spec.preimage (V.2.fromSpec ≫ A.hom)

theorem algV_spec (V : A.left.affineOpens) : Spec.map (algV A V) = V.2.fromSpec ≫ A.hom :=
  Spec.map_preimage _

/-- (b) The length of a closed subscheme with finite support inside an affine open `V`. -/
theorem len_eq_finrank [LocallyOfFiniteType A.hom] (J : A.left.IdealSheafData)
    (V : A.left.affineOpens) (hV : (J.support : Set A.left) ⊆ V)
    (hfin : (J.support : Set A.left).Finite) :
    letI := (algV A V).hom.toAlgebra
    Module.Finite k (Γ(A.left, V) ⧸ J.ideal V) ∧
      len A J = Module.finrank k (Γ(A.left, V) ⧸ J.ideal V) := by
  letI := (algV A V).hom.toAlgebra
  let f : Spec (.of (Γ(A.left, V) ⧸ J.ideal V)) ⟶ J.subscheme := J.subschemeCover.f V
  have hfo : IsOpenImmersion f := J.subschemeCover.map_prop V
  have hf : IsIso f := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨hfo, ⟨fun z => ?_⟩⟩
    have h2 := J.opensRange_subschemeCover_map V
    have hz : z ∈ J.subschemeι ⁻¹ᵁ (V : A.left.Opens) :=
      hV (by rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩)
    rw [← h2] at hz
    exact hz
  have hcomp : f ≫ J.subschemeι ≫ A.hom =
      Spec.map (CommRingCat.ofHom (algebraMap k (Γ(A.left, V) ⧸ J.ideal V))) := by
    have h1 : f ≫ J.subschemeι = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal V))) ≫
        V.2.fromSpec :=
      (J.subschemeCover_map_subschemeι V).trans (J.glueDataObjι_ι V)
    rw [← Category.assoc, h1, Category.assoc, ← algV_spec, ← Spec.map_comp]
    rfl
  -- finiteness over `k`
  have hft : Algebra.FiniteType k Γ(A.left, V) := by
    have : LocallyOfFiniteType (Spec.map (algV A V)) := by
      rw [algV_spec]
      have : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
      infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this
  have hJac : IsJacobsonRing (Γ(A.left, V) ⧸ J.ideal V) := isJacobsonRing_of_finiteType (A := k)
  have hfinsub : Finite J.subscheme := by
    have hi : Function.Injective J.subschemeι := J.subschemeι.isEmbedding.injective
    refine Set.finite_univ_iff.mp (Set.Finite.of_finite_image (hfin.subset ?_) hi.injOn)
    rintro _ ⟨z, -, rfl⟩
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z, rfl⟩
  have hfinR : Finite (PrimeSpectrum (Γ(A.left, V) ⧸ J.ideal V)) :=
    Finite.of_injective (β := J.subscheme) (fun x => f x) f.isOpenEmbedding.injective
  have hdisc : DiscreteTopology (PrimeSpectrum (Γ(A.left, V) ⧸ J.ideal V)) :=
    JacobsonSpace.discreteTopology (Set.toFinite _)
  have hdim := (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp hdisc).2
  have hmf : Module.Finite k (Γ(A.left, V) ⧸ J.ideal V) :=
    (Module.finite_iff_krullDimLE_zero k _).mpr hdim
  refine ⟨hmf, ?_⟩
  have hg : J.subschemeι ≫ A.hom = inv f ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (Γ(A.left, V) ⧸ J.ideal V))) := by
    rw [← hcomp, IsIso.inv_hom_id_assoc]
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap k (Γ(A.left, V) ⧸ J.ideal V)))) := by
    rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]; infer_instance
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k (Γ(A.left, V) ⧸ J.ideal V)))) := by
    rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finite_algebraMap]; exact hmf
  show Scheme.Hom.finrank _ (pt0 k) = _
  rw [hg, Scheme.Hom.finrank_comp_left_of_isIso]
  refine (Scheme.Hom.finrank_SpecMap_algebraMap k (Γ(A.left, V) ⧸ J.ideal V) (pt0 k)).trans ?_
  rw [Module.rankAtStalk_eq_finrank_of_free]
  rfl

/-- (c) Pulling back along an isomorphism preserves products of ideal sheaves. -/
theorem comap_mul_of_isIso {X Y : Scheme.{u}} (I I' : Y.IdealSheafData) (f : X ⟶ Y) [IsIso f] :
    (I * I').comap f = I.comap f * I'.comap f := by
  ext U : 2
  simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
  let e := (f.appIso U).commRingCatIsoToRingEquiv
  have h (K : Ideal Γ(Y, f ''ᵁ U)) : K.comap (f.appIso U).inv.hom = K.map e := by
    rw [← Ideal.comap_symm]; rfl
  rw [h, h, h, Ideal.map_mul]

end Aff

end RamanujanPetersson.IntersectB


end

-- ===== S4.Def_RP_IntersectB_Alg =====
section

/-!
# S4-IntersectB, file Alg: the exact-sequence lemma behind additivity (L33, part 3)

`finrank_quot_mul`: for ideals `I, I', J` of a `k`-algebra `R`, an element `u ∈ I'` and `s ∈ R`
with `s • I' ⊆ (u)`, `s` a unit modulo `X := I * I' ⊔ J`, and `u` a non-zero-divisor modulo `J`
after inverting `s`, the quotient dimensions add:
`dim R/X = dim R/(I ⊔ J) + dim R/(I' ⊔ J)` (short exact sequence `0 → R/(I⊔J) --u--> R/X → R/(I'⊔J) → 0`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.IntersectB

section Alg

variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

theorem mem_of_isUnit_mul_mem {X : Ideal R} {s x : R} (hs : IsUnit (Ideal.Quotient.mk X s))
    (h : s * x ∈ X) : x ∈ X := by
  obtain ⟨t, ht⟩ := hs.exists_left_inv
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [← Ideal.Quotient.eq_zero_iff_mem] at h ⊢
  calc Ideal.Quotient.mk X x
      = (Ideal.Quotient.mk X t * Ideal.Quotient.mk X s) * Ideal.Quotient.mk X x := by
        rw [ht, one_mul]
    _ = Ideal.Quotient.mk X t * Ideal.Quotient.mk X (s * x) := by rw [map_mul, mul_assoc]
    _ = 0 := by rw [h, mul_zero]

theorem isUnit_mk_of_le {X Y : Ideal R} (hXY : X ≤ Y) {s : R}
    (hs : IsUnit (Ideal.Quotient.mk X s)) : IsUnit (Ideal.Quotient.mk Y s) := by
  have := hs.map (Ideal.Quotient.factor hXY)
  simpa using this

theorem exists_mul_of_mem_mul {I I' : Ideal R} {u s : R}
    (hsu : ∀ y ∈ I', s * y ∈ Ideal.span {u}) {y : R} (hy : y ∈ I * I') :
    ∃ i ∈ I, s * y = u * i := by
  refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) ?_
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hsu b hb)
    exact ⟨a * c, I.mul_mem_right c ha, by linear_combination (-a) * hc⟩
  · rintro y₁ y₂ ⟨i₁, hi₁, e₁⟩ ⟨i₂, hi₂, e₂⟩
    exact ⟨i₁ + i₂, I.add_mem hi₁ hi₂, by rw [mul_add, e₁, e₂, mul_add]⟩

/-- B3 core: additivity of quotient dimensions along `0 → R/(I⊔J) --u--> R/X → R/(I'⊔J) → 0`. -/
theorem finrank_quot_mul (I I' J : Ideal R) (u s : R) (hu : u ∈ I')
    (hsu : ∀ y ∈ I', s * y ∈ Ideal.span {u})
    (hs : IsUnit (Ideal.Quotient.mk (I * I' ⊔ J) s))
    (hnzd : ∀ x, u * x ∈ J → ∃ n : ℕ, s ^ n * x ∈ J)
    [Module.Finite k (R ⧸ (I * I' ⊔ J))] :
    Module.finrank k (R ⧸ (I * I' ⊔ J)) =
      Module.finrank k (R ⧸ (I ⊔ J)) + Module.finrank k (R ⧸ (I' ⊔ J)) := by
  have hXY : I * I' ⊔ J ≤ I ⊔ J := sup_le_sup_right Ideal.mul_le_left J
  have hXZ : I * I' ⊔ J ≤ I' ⊔ J := sup_le_sup_right Ideal.mul_le_right J
  let ψ : R →ₗ[k] R ⧸ (I * I' ⊔ J) :=
    (Ideal.Quotient.mkₐ k (I * I' ⊔ J)).toLinearMap ∘ₗ LinearMap.mulLeft k u
  have hψ (r : R) : ψ r = Ideal.Quotient.mk (I * I' ⊔ J) (u * r) := rfl
  have hker : LinearMap.ker ψ = (I ⊔ J).restrictScalars k := by
    ext r
    rw [LinearMap.mem_ker, hψ, Ideal.Quotient.eq_zero_iff_mem, Submodule.restrictScalars_mem]
    constructor
    · intro h
      obtain ⟨y, hy, j, hj, hyj⟩ := Submodule.mem_sup.mp h
      obtain ⟨i, hi, hi'⟩ := exists_mul_of_mem_mul hsu hy
      have h1 : u * (s * r - i) ∈ J := by
        have e : u * (s * r - i) = s * j := by linear_combination hi' - s * hyj
        rw [e]; exact J.mul_mem_left s hj
      obtain ⟨n, hn⟩ := hnzd _ h1
      have h2 : s ^ (n + 1) * r ∈ I ⊔ J := by
        have e : s ^ (n + 1) * r = s ^ n * (s * r - i) + s ^ n * i := by ring
        rw [e]
        exact add_mem (Submodule.mem_sup_right hn) (Submodule.mem_sup_left (I.mul_mem_left _ hi))
      refine mem_of_isUnit_mul_mem ?_ h2
      have := (isUnit_mk_of_le hXY hs).pow (n + 1)
      rwa [← map_pow] at this
    · intro h
      obtain ⟨i, hi, j, hj, rfl⟩ := Submodule.mem_sup.mp h
      rw [mul_add]
      exact add_mem (Submodule.mem_sup_left (show u * i ∈ I * I' by
        rw [mul_comm u i]; exact Ideal.mul_mem_mul hi hu))
        (Submodule.mem_sup_right (J.mul_mem_left u hj))
  let π : (R ⧸ (I * I' ⊔ J)) →ₗ[k] R ⧸ (I' ⊔ J) := (Ideal.Quotient.factorₐ k hXZ).toLinearMap
  have hπmk (r : R) : π (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk (I' ⊔ J) r := rfl
  have hπ : Function.Surjective π := Ideal.Quotient.factor_surjective hXZ
  have hkr : LinearMap.ker π = LinearMap.range ψ := by
    ext q
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [LinearMap.mem_ker, hπmk, Ideal.Quotient.eq_zero_iff_mem, LinearMap.mem_range]
    simp only [hψ]
    constructor
    · intro h
      have h1 : r ∈ Ideal.span {u} ⊔ (I * I' ⊔ J) := by
        apply mem_of_isUnit_mul_mem (isUnit_mk_of_le le_sup_right hs)
        obtain ⟨y, hy, j, hj, rfl⟩ := Submodule.mem_sup.mp h
        rw [mul_add]
        exact add_mem (Submodule.mem_sup_left (hsu y hy))
          (Submodule.mem_sup_right (Submodule.mem_sup_right (J.mul_mem_left s hj)))
      obtain ⟨a, ha, x, hx, rfl⟩ := Submodule.mem_sup.mp h1
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      refine ⟨c, ?_⟩
      rw [Ideal.Quotient.eq]
      have e : u * c - (c * u + x) = -x := by ring
      rw [e]
      exact Submodule.neg_mem _ hx
    · rintro ⟨y, hy⟩
      rw [Ideal.Quotient.eq] at hy
      have e : r = u * y - (u * y - r) := by ring
      rw [e]
      exact sub_mem (Submodule.mem_sup_left (I'.mul_mem_right y hu)) (hXZ hy)
  have e1 := LinearMap.finrank_range_add_finrank_ker π
  rw [LinearMap.range_eq_top.mpr hπ, finrank_top, hkr] at e1
  have e2 : Module.finrank k (LinearMap.range ψ) = Module.finrank k (R ⧸ (I ⊔ J)) := by
    rw [← (LinearMap.quotKerEquivRange ψ).finrank_eq, hker]
    exact (Submodule.Quotient.restrictScalarsEquiv k (I ⊔ J)).finrank_eq
  omega

end Alg

end RamanujanPetersson.IntersectB


end

-- ===== S4.Def_RP_IntersectB_Gen =====
section

/-!
# S4-IntersectB, file Gen: the generator `u`, the multiplier `s`, the weak NZD criterion (L33, part 3b)

* `LocPrinAt I' m`: `I'` is principal near the maximal ideal `m`, phrased without localisation.
* `exists_gen_quot`: if `R/X` is finite over an infinite field `k` and `I'` is principal near every maximal ideal
  containing `X`, there are `u ∈ I'` and `s` with `s • I' ⊆ (u)` and `s` a unit modulo `X`.
* `weak_nzd`: if every associated prime of `R/J` containing `u` contains `s`, then `u x ∈ J → s^n x ∈ J`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.IntersectB

open Ideal

section Gen

variable {R : Type*} [CommRing R]

/-- `I'` is principal near `m`: some `v ∈ I'` and `t ∉ m` with `t • I' ⊆ (v)`. -/
def LocPrinAt (I' m : Ideal R) : Prop :=
  ∃ v ∈ I', ∃ t ∉ m, ∀ y ∈ I', t * y ∈ span ({v} : Set R)

theorem mem_mul_of_mul_mem {m I' : Ideal R} (hm : m.IsMaximal) {t u : R} (ht : t ∉ m)
    (hu : u ∈ I') (h : t * u ∈ m * I') : u ∈ m * I' := by
  obtain ⟨y, i, hi, e⟩ := hm.exists_inv ht
  have : u = y * (t * u) + i * u := by
    calc u = (y * t + i) * u := by rw [e, one_mul]
      _ = y * (t * u) + i * u := by ring
  rw [this]
  exact add_mem (mul_mem_left _ _ h) (mul_mem_mul hi hu)

theorem colon_of_notMem [IsDomain R] {I' m : Ideal R} (hm : m.IsMaximal) (h : LocPrinAt I' m)
    {u : R} (hu : u ∈ I') (hum : u ∉ m * I') :
    ∃ a ∉ m, ∀ y ∈ I', a * y ∈ span ({u} : Set R) := by
  obtain ⟨v, hv, t, ht, htv⟩ := h
  obtain ⟨a, ha⟩ := mem_span_singleton'.1 (htv u hu)
  refine ⟨a, fun ham => hum (mem_mul_of_mul_mem hm ht hu ?_), fun y hy => ?_⟩
  · rw [← ha]; exact mul_mem_mul ham hv
  · obtain ⟨b, hb⟩ := mem_span_singleton'.1 (htv y hy)
    have ht0 : t ≠ 0 := fun h0 => ht (h0 ▸ m.zero_mem)
    have key : t * (a * y) = t * (b * u) := by
      calc t * (a * y) = a * (t * y) := by ring
        _ = a * (b * v) := by rw [hb]
        _ = b * (a * v) := by ring
        _ = b * (t * u) := by rw [ha]
        _ = t * (b * u) := by ring
    rw [mul_left_cancel₀ ht0 key]
    exact mul_mem_left _ _ (mem_span_singleton_self u)

theorem mul_ne_self [IsDomain R] {I' m : Ideal R} (hm : m.IsMaximal) (h : LocPrinAt I' m)
    (hI : I' ≠ ⊥) : m * I' ≠ I' := by
  intro hEq
  obtain ⟨v, hv, t, ht, htv⟩ := h
  have key : ∀ x ∈ m * I', t * x ∈ m * span ({v} : Set R) := by
    intro x hx
    refine Submodule.mul_induction_on hx (fun a ha y hy => ?_) (fun x y hx hy => ?_)
    · rw [show t * (a * y) = a * (t * y) by ring]; exact mul_mem_mul ha (htv y hy)
    · rw [mul_add]; exact add_mem hx hy
  have h1 := key v (hEq.symm ▸ hv)
  rw [mul_comm m, mem_span_singleton_mul] at h1
  obtain ⟨z, hz, hzv⟩ := h1
  have ht0 : t - z ∉ m := fun h' => ht (by simpa using add_mem h' hz)
  have hv0 : v = 0 := by
    have : v * (t - z) = 0 := by rw [mul_sub, hzv]; ring
    exact (mul_eq_zero.1 this).resolve_right (fun h0 => ht0 (h0 ▸ m.zero_mem))
  apply hI
  rw [eq_bot_iff]
  intro y hy
  have := htv y hy
  rw [hv0, span_singleton_eq_bot.2 rfl, mem_bot] at this
  exact mem_bot.2 ((mul_eq_zero.1 this).resolve_left (fun h0 => ht (h0 ▸ m.zero_mem)))

theorem exists_gen (k : Type*) [Field k] [Infinite k] [Algebra k R] [IsDomain R] (I' : Ideal R)
    (S : Set (Ideal R)) (hS : S.Finite) (hmax : ∀ m ∈ S, m.IsMaximal)
    (hloc : ∀ m ∈ S, LocPrinAt I' m) :
    ∃ u ∈ I', ∃ s, (∀ m ∈ S, s ∉ m) ∧ ∀ y ∈ I', s * y ∈ span ({u} : Set R) := by
  by_cases hI : I' = ⊥
  · refine ⟨0, zero_mem _, 1, fun m hm h1 => (hmax m hm).ne_top ((eq_top_iff_one m).2 h1),
      fun y hy => ?_⟩
    rw [hI, mem_bot] at hy; simp [hy]
  have : Finite S := hS.to_subtype
  let M := I'.restrictScalars k
  let p : S → Submodule k M := fun m => ((m.1 * I').restrictScalars k).comap M.subtype
  have hp : ∀ m, p m ≠ ⊤ := by
    intro m htop
    apply mul_ne_self (hmax m.1 m.2) (hloc m.1 m.2) hI
    refine le_antisymm mul_le_right (fun y hy => ?_)
    have : (⟨y, hy⟩ : M) ∈ p m := htop ▸ Submodule.mem_top
    exact this
  obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  let Q : Ideal R := (span ({(x : R)} : Set R)).colon (I' : Set R)
  have hcol : ∀ m ∈ S, ∃ a ∉ m, a ∈ Q := by
    intro m hm
    obtain ⟨a, ham, ha⟩ := colon_of_notMem (hmax m hm) (hloc m hm) x.2 (hx ⟨m, hm⟩)
    exact ⟨a, ham, Submodule.mem_colon.2 (fun y hy => ha y hy)⟩
  have hnot : ¬ ((Q : Set R) ⊆ ⋃ i ∈ S, (((fun m : Ideal R => m) i : Ideal R) : Set R)) := by
    intro hsub
    obtain ⟨m, hm, hle⟩ := (subset_union_prime_finite hS (f := fun m : Ideal R => m) ⊤ ⊤
      (fun m hm _ _ => (hmax m hm).isPrime)).1 hsub
    obtain ⟨a, ham, ha⟩ := hcol m hm
    exact ham (hle ha)
  obtain ⟨s, hs, hsS⟩ := Set.not_subset.1 hnot
  exact ⟨x, x.2, s, fun m hm hsm => hsS (Set.mem_biUnion hm hsm),
    fun y hy => Submodule.mem_colon.1 hs y hy⟩

theorem isUnit_mk_of_forall {X : Ideal R} {s : R}
    (h : ∀ m : Ideal R, m.IsMaximal → X ≤ m → s ∉ m) : IsUnit (Ideal.Quotient.mk X s) := by
  by_contra hs
  obtain ⟨M, hM, hsM⟩ :=
    exists_max_ideal_of_mem_nonunits (show Ideal.Quotient.mk X s ∈ nonunits _ from hs)
  refine h (M.comap (Ideal.Quotient.mk X))
    (comap_isMaximal_of_surjective _ Quotient.mk_surjective) (fun x hx => ?_) hsM
  rw [mem_comap, Quotient.eq_zero_iff_mem.2 hx]; exact M.zero_mem

theorem finite_maximal_of_finite (k : Type*) [Field k] [Algebra k R] (X : Ideal R)
    [Module.Finite k (R ⧸ X)] : {m : Ideal R | m.IsMaximal ∧ X ≤ m}.Finite := by
  have : IsArtinianRing (R ⧸ X) := IsArtinianRing.of_finite k (R ⧸ X)
  refine ((IsArtinianRing.setOfPred_isMaximal_finite (R := R ⧸ X)).image
    (Ideal.comap (Ideal.Quotient.mk X))).subset ?_
  rintro m ⟨hm, hXm⟩
  have := hm
  exact ⟨m.map (Ideal.Quotient.mk X), IsMaximal.map_of_surjective_of_ker_le Quotient.mk_surjective
    (by rw [mk_ker]; exact hXm), comap_map_mk hXm⟩

/-- O3b: the generator and the multiplier for `finrank_quot_mul`. -/
theorem exists_gen_quot (k : Type*) [Field k] [Infinite k] [Algebra k R] [IsDomain R]
    (I' X : Ideal R) [Module.Finite k (R ⧸ X)]
    (hloc : ∀ m : Ideal R, m.IsMaximal → X ≤ m → LocPrinAt I' m) :
    ∃ u ∈ I', ∃ s, IsUnit (Ideal.Quotient.mk X s) ∧ ∀ y ∈ I', s * y ∈ span ({u} : Set R) := by
  obtain ⟨u, hu, s, hs, hsu⟩ := exists_gen k I' _ (finite_maximal_of_finite k X)
    (fun m hm => hm.1) (fun m hm => hloc m hm.1 hm.2)
  exact ⟨u, hu, s, isUnit_mk_of_forall (fun m hm hXm => hs m ⟨hm, hXm⟩), hsu⟩

/-- O4 (algebra): the weak non-zero-divisor condition from associated primes. -/
theorem weak_nzd [IsNoetherianRing R] (J : Ideal R) (u s : R)
    (H : ∀ p ∈ associatedPrimes R (R ⧸ J), u ∈ p → s ∈ p) :
    ∀ x, u * x ∈ J → ∃ n : ℕ, s ^ n * x ∈ J := by
  intro x hux
  have hsm : ∀ r y : R, r • Ideal.Quotient.mk J y = Ideal.Quotient.mk J (r * y) := fun _ _ => rfl
  let N : Submodule R (R ⧸ J) := Submodule.span R {Ideal.Quotient.mk J x}
  have : Module.Finite R N := Module.Finite.iff_fg.2 (Submodule.fg_span_singleton _)
  have hu : u ∈ Module.annihilator R N := by
    rw [Module.mem_annihilator]
    rintro ⟨n, hn⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hn
    apply Subtype.ext
    change u • a • Ideal.Quotient.mk J x = 0
    rw [smul_comm, hsm u x, Quotient.eq_zero_iff_mem.2 hux, smul_zero]
  have hsrad : s ∈ (Module.annihilator R N).radical := by
    rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
    intro p hp
    have hass := Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R N hp
    exact H p (associatedPrimes.subset_of_injective (f := N.subtype) N.injective_subtype hass)
      (hp.1.2 hu)
  obtain ⟨n, hn⟩ := hsrad
  have := congrArg Subtype.val
    (Module.mem_annihilator.1 hn ⟨_, Submodule.mem_span_singleton_self (Ideal.Quotient.mk J x)⟩)
  change s ^ n • Ideal.Quotient.mk J x = 0 at this
  exact ⟨n, Quotient.eq_zero_iff_mem.1 (by rw [← hsm]; exact this)⟩

end Gen

end RamanujanPetersson.IntersectB


end

-- ===== S4.Def_RP_IntersectB_Ass =====
section

/-!
# S4-IntersectB, file Ass: associated points of an ideal sheaf (L33, part 4)

* `IsAssPt C V x hx`: the prime of `x` in the affine chart `V` is associated to `Γ(V) ⧸ C(V)`.
* `assSet C`: the points that are associated in some affine chart.
* `isAssPt_basicOpen`: being associated does not change when passing to a basic open.
* `assSet_finite`: on a quasi-compact locally Noetherian scheme `assSet C` is finite.
* `not_le_of_ass`: if no associated point lies in `supp I`, then `I(V)` lies in no associated prime of `Γ(V)/C(V)`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.IntersectB

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

section AssAlg

/-- Associated primes of `R ⧸ J` and of `R' ⧸ J R'` for a localisation `R'` of `R`. -/
theorem ass_localization {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R R']
    [IsNoetherianRing R] (S : Submonoid R) [IsLocalization S R'] (J : Ideal R) (P : Ideal R') :
    P.comap (algebraMap R R') ∈ associatedPrimes R (R ⧸ J) ↔
      P ∈ associatedPrimes R' (R' ⧸ J.map (algebraMap R R')) := by
  have h := Module.associatedPrimes.preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
    (S := S) (R' := R') (f := J.toLocalizedQuotient' R' S (Algebra.linearMap R R'))
  have hJ : J.localized' R' S (Algebra.linearMap R R') = J.map (algebraMap R R') := by
    rw [Submodule.localized'_eq_span]; rfl
  rw [hJ] at h
  exact Set.ext_iff.1 h P

end AssAlg

section Ass

variable {X : Scheme} (C : X.IdealSheafData)

/-- `x ∈ V` is an associated point of `C` in the affine chart `V`. -/
def IsAssPt (V : X.affineOpens) (x : X) (hx : x ∈ (V : X.Opens)) : Prop :=
  (V.2.primeIdealOf ⟨x, hx⟩).asIdeal ∈ associatedPrimes Γ(X, V) (Γ(X, V) ⧸ C.ideal V)

/-- The associated points of `C` (in some affine chart). -/
def assSet : Set X := {x | ∃ (V : X.affineOpens) (hx : x ∈ (V : X.Opens)), IsAssPt C V x hx}

theorem isAssPt_congr {U U' : X.affineOpens} (h : U = U') (x : X) (hx : x ∈ (U : X.Opens))
    (hx' : x ∈ (U' : X.Opens)) : IsAssPt C U x hx ↔ IsAssPt C U' x hx' := by
  subst h; rfl

theorem primeIdealOf_fromSpec {U : X.Opens} (hU : IsAffineOpen U) (P : PrimeSpectrum Γ(X, U))
    (h : hU.fromSpec P ∈ U) : hU.primeIdealOf ⟨hU.fromSpec P, h⟩ = P := by
  have e : (⟨hU.fromSpec P, h⟩ : U) = hU.isoSpec.inv P := by
    apply Subtype.ext
    rfl
  rw [e]
  dsimp only [IsAffineOpen.primeIdealOf]
  change (hU.isoSpec.inv ≫ hU.isoSpec.hom) P = P
  rw [Iso.inv_hom_id]
  rfl

theorem fromSpec_mem {U : X.Opens} (hU : IsAffineOpen U) (P : PrimeSpectrum Γ(X, U)) :
    hU.fromSpec P ∈ U := by
  rw [← SetLike.mem_coe, ← hU.range_fromSpec]; exact ⟨P, rfl⟩

variable [IsLocallyNoetherian X]

theorem isAssPt_basicOpen (V : X.affineOpens) (f : Γ(X, V)) (x : X) (hx : x ∈ X.basicOpen f) :
    IsAssPt C V x (X.basicOpen_le f hx) ↔ IsAssPt C (X.affineBasicOpen f) x hx := by
  have hle : (X.affineBasicOpen f : X.Opens) ≤ V := X.basicOpen_le f
  let ρ := X.presheaf.map (homOfLE hle).op
  let _ := ρ.hom.toAlgebra
  have hloc : IsLocalization.Away f Γ(X, (X.affineBasicOpen f : X.Opens)) :=
    V.2.isLocalization_of_eq_basicOpen f (homOfLE hle) rfl
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian V
  have h0 := IsAffineOpen.comap_primeIdealOf_appLE (f := 𝟙 X) (x := x) V.1 V.2
    (X.affineBasicOpen f : X.Opens) (X.affineBasicOpen f).2 (fun y hy => hle hy) hx
  have hP : ((X.affineBasicOpen f).2.primeIdealOf ⟨x, hx⟩).asIdeal.comap (algebraMap _ _) =
      (V.2.primeIdealOf ⟨x, X.basicOpen_le f hx⟩).asIdeal := by
    have h1 := congrArg PrimeSpectrum.asIdeal h0
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app] at h1
    exact h1
  unfold IsAssPt
  rw [← hP, ass_localization (Submonoid.powers f) (C.ideal V)]
  have hm := C.map_ideal' (U := X.affineBasicOpen f) (V := V) (homOfLE hle).op
  exact Iff.of_eq (by rw [← hm]; rfl)

theorem finite_isAssPt_chart (W : X.affineOpens) :
    {x | ∃ hx : x ∈ (W : X.Opens), IsAssPt C W x hx}.Finite := by
  have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian W
  have hA := associatedPrimes.finite Γ(X, W) (Γ(X, W) ⧸ C.ideal W)
  have hB : {P : PrimeSpectrum Γ(X, W) |
      P.asIdeal ∈ associatedPrimes Γ(X, W) (Γ(X, W) ⧸ C.ideal W)}.Finite :=
    hA.preimage (fun P _ Q _ h => PrimeSpectrum.ext h)
  refine (hB.image (fun P => W.2.fromSpec P)).subset ?_
  rintro x ⟨hx, hass⟩
  exact ⟨_, hass, W.2.fromSpec_primeIdealOf ⟨x, hx⟩⟩

theorem assSet_finite [CompactSpace X] : (assSet C).Finite := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun V : X.affineOpens => ((V : X.Opens) : Set X)) (fun V => V.1.isOpen) (fun x _ => by
      have hx : x ∈ (⨆ i : X.affineOpens, (i : X.Opens)) := by
        rw [iSup_affineOpens_eq_top X]; trivial
      obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      exact Set.mem_iUnion.2 ⟨V, hV⟩)
  refine (t.finite_toSet.biUnion (fun W _ => finite_isAssPt_chart C W)).subset ?_
  rintro x ⟨V, hxV, hass⟩
  obtain ⟨W, hWt, hxW⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter V.2 W.2 x ⟨hxV, hxW⟩
  have hxg : x ∈ X.basicOpen g := hfg ▸ hxf
  exact Set.mem_biUnion hWt ⟨hxW, (isAssPt_basicOpen C W g x hxg).2
    ((isAssPt_congr C (Subtype.ext hfg) x hxf hxg).1 ((isAssPt_basicOpen C V f x hxf).1 hass))⟩

omit [IsLocallyNoetherian X] in
/-- If no associated point of `C` lies in `supp I`, then `I(V)` lies in no associated prime of
`Γ(V) ⧸ C(V)`. -/
theorem not_le_of_ass (I : X.IdealSheafData) (h : ∀ x ∈ assSet C, x ∉ I.support)
    (V : X.affineOpens) (p : Ideal Γ(X, V))
    (hp : p ∈ associatedPrimes Γ(X, V) (Γ(X, V) ⧸ C.ideal V)) : ¬ I.ideal V ≤ p := by
  intro hle
  have hpr : p.IsPrime := IsAssociatedPrime.isPrime hp
  let P : PrimeSpectrum Γ(X, V) := ⟨p, hpr⟩
  have hmem := fromSpec_mem V.2 P
  apply h (V.2.fromSpec P) ⟨V, hmem, by
    unfold IsAssPt; rw [primeIdealOf_fromSpec V.2 P hmem]; exact hp⟩
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hmem]
  exact (Set.ext_iff.1 (V.2.fromSpec_preimage_zeroLocus (I.ideal V : Set Γ(X, V))) P).2
    ((PrimeSpectrum.mem_zeroLocus _ _).2 hle)

end Ass

end RamanujanPetersson.IntersectB


end

-- ===== S4.Def_RP_IntersectB_Add_Ring =====
section

/-!
# S4-IntersectB, file Add_Ring: the chart step of additivity (L33, B3 core)

* `IsLocPrin I`: `I` is principal near every maximal ideal of every affine chart; stable under
  pullback along isomorphisms (`isLocPrin_comap`).
* `finrank_chart`: for ideals `I, I', J` of a Noetherian domain over an infinite field, with `I'`
  locally principal and contained in no associated prime of `R ⧸ J`,
  `dim R/(II'+J) = dim R/(I+J) + dim R/(I'+J)`.
* `len_mul`: the same for lengths of closed subschemes of `A` with finite support, when the
  support of `L'` avoids the associated points of `C`.
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory Limits

namespace RamanujanPetersson.IntersectB

open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA

section Ring

/-- Local principality transported along a ring isomorphism. -/
theorem locPrinAt_comap {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') (ψ : R' →+* R)
    (h1 : ∀ x, φ (ψ x) = x) (h2 : ∀ x, ψ (φ x) = x) {K : Ideal R'} {m : Ideal R}
    (h : LocPrinAt K (m.comap ψ)) : LocPrinAt (K.comap φ) m := by
  obtain ⟨v, hv, t, ht, htv⟩ := h
  refine ⟨ψ v, ?_, ψ t, ht, fun y hy => ?_⟩
  · show φ (ψ v) ∈ K
    rw [h1]; exact hv
  · obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (htv (φ y) hy)
    refine Ideal.mem_span_singleton'.2 ⟨ψ a, ?_⟩
    rw [← map_mul, ha, map_mul, h2]

/-- Ring step of B3. -/
theorem finrank_chart (k : Type*) [Field k] [Infinite k] {R : Type*} [CommRing R] [Algebra k R]
    [IsDomain R] [IsNoetherianRing R] (I I' J : Ideal R) [Module.Finite k (R ⧸ (I * I' ⊔ J))]
    (hloc : ∀ m : Ideal R, m.IsMaximal → LocPrinAt I' m)
    (hass : ∀ p ∈ associatedPrimes R (R ⧸ J), ¬ I' ≤ p) :
    Module.finrank k (R ⧸ (I * I' ⊔ J)) =
      Module.finrank k (R ⧸ (I ⊔ J)) + Module.finrank k (R ⧸ (I' ⊔ J)) := by
  obtain ⟨u, hu, s, hs, hsu⟩ := exists_gen_quot k I' (I * I' ⊔ J) (fun m hm _ => hloc m hm)
  refine finrank_quot_mul I I' J u s hu hsu hs (weak_nzd J u s fun p hp hup => ?_)
  by_contra hsp
  refine hass p hp fun y hy => ?_
  have hp' : p.IsPrime := IsAssociatedPrime.isPrime hp
  have h1 : s * y ∈ p := (Ideal.span_singleton_le_iff_mem p).2 hup (hsu y hy)
  exact (hp'.mem_or_mem h1).resolve_left hsp

end Ring

section Sch

/-- `I` is principal near every maximal ideal of every affine chart. -/
def IsLocPrin {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  ∀ (V : X.affineOpens) (m : Ideal Γ(X, V)), m.IsMaximal → LocPrinAt (I.ideal V) m

theorem isLocPrin_comap {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) [IsIso f]
    (h : IsLocPrin I) : IsLocPrin (I.comap f) := by
  intro V m hm
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  refine locPrinAt_comap _ (f.appIso V).hom.hom (fun x => ?_) (fun x => ?_) (h _ _ ?_)
  · rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  · rw [← CommRingCat.comp_apply, Iso.inv_hom_id]; rfl
  · exact Ideal.comap_isMaximal_of_surjective _ fun y => ⟨(f.appIso V).inv.hom y, by
      rw [← CommRingCat.comp_apply, Iso.inv_hom_id]; rfl⟩

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [LocallyOfFiniteType A.hom] [IsIntegral A.left]

/-- B3 at the level of lengths: `len (L L' + C) = len (L + C) + len (L' + C)`. -/
theorem len_mul (L L' C : A.left.IdealSheafData)
    (hfin : ((L * L' ⊔ C).support : Set A.left).Finite)
    (hloc : IsLocPrin L') (hass : ∀ x ∈ assSet C, x ∉ L'.support) :
    len A (L * L' ⊔ C) = len A (L ⊔ C) + len A (L' ⊔ C) := by
  classical
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  obtain ⟨x0⟩ : Nonempty A.left := inferInstance
  obtain ⟨V, hV⟩ := exists_affine_mem A (insert x0 hfin.toFinset)
  have hS : ((L * L' ⊔ C).support : Set A.left) ⊆ (V : A.left.Opens) := fun x hx =>
    hV x (Finset.mem_insert_of_mem (hfin.mem_toFinset.2 hx))
  have h2 : ((L ⊔ C).support : Set A.left) ⊆ (L * L' ⊔ C).support :=
    Scheme.IdealSheafData.support_antitone (sup_le_sup_right
      (Scheme.IdealSheafData.le_def.2 fun U => Ideal.mul_le_left) C)
  have h3 : ((L' ⊔ C).support : Set A.left) ⊆ (L * L' ⊔ C).support :=
    Scheme.IdealSheafData.support_antitone (sup_le_sup_right
      (Scheme.IdealSheafData.le_def.2 fun U => Ideal.mul_le_right) C)
  have : Nonempty (V : A.left.Opens) := ⟨⟨x0, hV x0 (Finset.mem_insert_self _ _)⟩⟩
  have : IsDomain Γ(A.left, V) := inferInstance
  have : IsNoetherianRing Γ(A.left, V) := IsLocallyNoetherian.component_noetherian V
  letI := (algV A V).hom.toAlgebra
  obtain ⟨hf1, e1⟩ := len_eq_finrank A (L * L' ⊔ C) V hS hfin
  obtain ⟨-, e2⟩ := len_eq_finrank A (L ⊔ C) V (h2.trans hS) (hfin.subset h2)
  obtain ⟨-, e3⟩ := len_eq_finrank A (L' ⊔ C) V (h3.trans hS) (hfin.subset h3)
  rw [e1, e2, e3]
  have : Module.Finite k (Γ(A.left, V) ⧸ (L.ideal V * L'.ideal V ⊔ C.ideal V)) := hf1
  exact finrank_chart k (L.ideal V) (L'.ideal V) (C.ideal V) (fun m hm => hloc V m hm)
    (fun p hp => not_le_of_ass C L' hass V p hp)

end Sch

end RamanujanPetersson.IntersectB


end

-- ===== S4.Def_RP_IntersectB_Add =====
section

/-!
# S4-IntersectB, file Add: additivity of `inum` in the first slot (L33, B3)

For a locally principal `I'` (`IsLocPrin`), `(I I' · E) = (I · E) + (I' · E)`.
Proof (slice trick): pick a `k`-point `c*` of `A^(n+1)` where all three intersections are generic,
freeze its last `n` coordinates (intersection `C`), and move the first coordinate inside the slice
so that the translate of `supp I'` avoids the finitely many associated points of `C`; then
`len_mul` applies.
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory Limits

namespace RamanujanPetersson.IntersectB

open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA

section Slice

variable {k : Type u} [Field k] (A : Over (Spec (.of k)))

theorem Zid_cons [GrpObj A] {n : ℕ} (X : A.left.IdealSheafData) (E : Fin n → A.left.IdealSheafData)
    (a : Fin (n + 1) → (𝟙_ (Over (Spec (.of k))) ⟶ A)) :
    Zid A (Fin.cons X E : Fin (n + 1) → A.left.IdealSheafData) a =
      X.comap (transl A (a 0)).left ⊔ ⨆ j, (E j).comap (transl A (a j.succ)).left := by
  unfold Zid
  apply le_antisymm
  · refine iSup_le fun i => ?_
    induction i using Fin.cases with
    | zero => rw [Fin.cons_zero]; exact le_sup_left
    | succ j =>
      rw [Fin.cons_succ]
      exact le_sup_of_le_right (le_iSup (fun j => (E j).comap (transl A (a j.succ)).left) j)
  · refine sup_le ?_ (iSup_le fun j => ?_)
    · refine le_trans ?_ (le_iSup _ (0 : Fin (n + 1)))
      rw [Fin.cons_zero]
    · refine le_trans ?_ (le_iSup _ j.succ)
      rw [Fin.cons_succ]

/-- The slice of `A^(n+1)` through `c` along the first coordinate. -/
noncomputable def slice {n : ℕ} (c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A (n + 1)) : A ⟶ Pw A (n + 1) :=
  liftPw A (n + 1) (X := A) (Fin.cons (𝟙 A) fun j => toUnit A ≫ c ≫ proj A (n + 1) j.succ)

theorem slice_proj_zero {n : ℕ} (c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A (n + 1)) :
    slice A c ≫ proj A (n + 1) 0 = 𝟙 A := by
  rw [slice, liftPw_proj, Fin.cons_zero]

theorem slice_proj_succ {n : ℕ} (c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A (n + 1)) (j : Fin n) :
    slice A c ≫ proj A (n + 1) j.succ = toUnit A ≫ c ≫ proj A (n + 1) j.succ := by
  rw [slice, liftPw_proj, Fin.cons_succ]

theorem pt_slice_zero {n : ℕ} (c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A (n + 1))
    (w : 𝟙_ (Over (Spec (.of k))) ⟶ A) : (w ≫ slice A c) ≫ proj A (n + 1) 0 = w := by
  rw [Category.assoc, slice_proj_zero, Category.comp_id]

theorem pt_slice_succ {n : ℕ} (c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A (n + 1))
    (w : 𝟙_ (Over (Spec (.of k))) ⟶ A) (j : Fin n) :
    (w ≫ slice A c) ≫ proj A (n + 1) j.succ = c ≫ proj A (n + 1) j.succ := by
  rw [Category.assoc, slice_proj_succ, ← Category.assoc, comp_toUnit, toUnit_unit,
    Category.id_comp]

theorem slice_self {n : ℕ} (c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A (n + 1)) :
    (c ≫ proj A (n + 1) 0) ≫ slice A c = c :=
  Pw_hom_ext A (n + 1) _ _ fun i => by
    induction i using Fin.cases with
    | zero => exact pt_slice_zero A c _
    | succ j => exact pt_slice_succ A c _ j

end Slice

section B3

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left]

/-- B3: additivity of the intersection number in a locally principal factor. -/
theorem inum_mul (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ (n + 1 : ℕ))
    (I I' : A.left.IdealSheafData) (E : Fin n → A.left.IdealSheafData)
    (h1 : ∀ i, ((Fin.cons (I * I') E : Fin (n + 1) → A.left.IdealSheafData) i).support ≠ ⊤)
    (h2 : ∀ i, ((Fin.cons I E : Fin (n + 1) → A.left.IdealSheafData) i).support ≠ ⊤)
    (h3 : ∀ i, ((Fin.cons I' E : Fin (n + 1) → A.left.IdealSheafData) i).support ≠ ⊤)
    (hloc : IsLocPrin I') :
    inum A (n + 1) hdim (Fin.cons (I * I') E) h1 =
      inum A (n + 1) hdim (Fin.cons I E) h2 + inum A (n + 1) hdim (Fin.cons I' E) h3 := by
  have := isIntegral_Pw A (n + 1)
  have := isProper_Pw A (n + 1)
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨U1, hU1o, hU1n, hU1⟩ := inum_spec A (n + 1) hdim _ h1
  obtain ⟨U2, hU2o, hU2n, hU2⟩ := inum_spec A (n + 1) hdim _ h2
  obtain ⟨U3, hU3o, hU3n, hU3⟩ := inum_spec A (n + 1) hdim _ h3
  have hUo : IsOpen (U1 ∩ U2 ∩ U3) := (hU1o.inter hU2o).inter hU3o
  obtain ⟨cs, hcs⟩ := exists_pt_mem (Pw A (n + 1)) (U1 ∩ U2 ∩ U3) hUo.isLocallyClosed
    (nonempty_preirreducible_inter (hU1o.inter hU2o) hU3o
      (nonempty_preirreducible_inter hU1o hU2o hU1n hU2n) hU3n)
  obtain ⟨C, hC⟩ : ∃ C : A.left.IdealSheafData,
      C = ⨆ j, (E j).comap (transl A (cs ≫ proj A (n + 1) j.succ)).left := ⟨_, rfl⟩
  have hEf := assSet_finite C
  have hI' : (I'.support : Set A.left) ≠ Set.univ := fun h => h3 0 (by
    rw [Fin.cons_zero]; exact SetLike.coe_injective (h.trans TopologicalSpace.Closeds.coe_top.symm))
  choose G hGo hGn hG using fun ξ => exists_open_good A ξ _ I'.support.isClosed hI'
  have hO : IsOpen ((slice A cs).left ⁻¹' (U1 ∩ U2 ∩ U3)) := hUo.preimage (slice A cs).left.continuous
  have hOn : pt A (cs ≫ proj A (n + 1) 0) ∈ (slice A cs).left ⁻¹' (U1 ∩ U2 ∩ U3) := by
    show (slice A cs).left (pt A _) ∈ U1 ∩ U2 ∩ U3
    rw [← pt_comp, slice_self]; exact hcs
  obtain ⟨c0, hc0O, hc0G⟩ := exists_pt_mem A _ (hO.inter (isOpen_biInter_finset fun ξ _ => hGo ξ)).isLocallyClosed
    (nonempty_preirreducible_inter hO (isOpen_biInter_finset fun ξ _ => hGo ξ) ⟨_, hOn⟩
      (nonempty_biInter_finset hEf.toFinset G (fun ξ _ => hGo ξ) fun ξ _ => hGn ξ))
  have hc : pt (Pw A (n + 1)) (c0 ≫ slice A cs) ∈ U1 ∩ U2 ∩ U3 := by rw [pt_comp]; exact hc0O
  have hZ (X : A.left.IdealSheafData) :
      Zid A (Fin.cons X E : Fin (n + 1) → A.left.IdealSheafData)
        (fun i => (c0 ≫ slice A cs) ≫ proj A (n + 1) i) = X.comap (transl A c0).left ⊔ C := by
    rw [Zid_cons, hC, pt_slice_zero]
    simp only [pt_slice_succ]
  have := isIso_translL A c0
  obtain ⟨hfin1, hl1⟩ := hU1 _ hc.1.1
  obtain ⟨-, hl2⟩ := hU2 _ hc.1.2
  obtain ⟨-, hl3⟩ := hU3 _ hc.2
  rw [hZ, comap_mul_of_isIso] at hfin1 hl1
  rw [hZ] at hl2 hl3
  rw [← hl1, ← hl2, ← hl3]
  refine len_mul A _ _ C hfin1 (isLocPrin_comap I' _ hloc) fun x hx => ?_
  rw [Scheme.IdealSheafData.support_comap]
  exact hG x c0 (Set.mem_iInter₂.1 hc0G x (hEf.mem_toFinset.2 hx))

end B3

end RamanujanPetersson.IntersectB


end

-- ===== S4.Def_RP_JacDivisors_N =====
section

/-!
# S4-JacDivisors N (O14, steps E6-E7: a prime divisor through `Δ x` meets any morphism in codimension one)
* `exists_uniformizer_specializes`: near a point `x` with factorial stalk, a uniformizer `r` of a codimension-one
  generalization `ζ` of `x` cuts out exactly the specializations of `ζ` among the generalizations of `x`.
* `exists_coheight_le_one_not_mem_basicOpen`: Krull's principal ideal theorem on a chart: if `x ∉ D(r)` there is a
  generalization `v` of `x` of codimension at most one with `v ∉ D(r)`.
* `exists_specializes_of_coheight_eq_one`: for any morphism `Δ : V ⟶ P` and a codimension-one generalization `ζ` of
  `Δ x` (factorial stalk at `Δ x`), some generalization `v` of `x` of codimension at most one has `ζ ⤳ Δ v`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open AlgebraicGeometry CategoryTheory Order Topology IsLocalRing

universe u

section
variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- A uniformizer of a codimension-one generalization `ζ` of `x` cuts out the specializations of `ζ` near `x`. -/
lemma exists_uniformizer_specializes {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    [UniqueFactorizationMonoid (X.presheaf.stalk x)] (ζ : X) (hζ : ζ ⤳ x) (hζ1 : coheight ζ = 1) :
    ∃ r : Γ(X, U), r ≠ 0 ∧ ζ ∉ X.basicOpen r ∧
      ∀ w : X, w ⤳ x → w ∉ X.basicOpen r → ζ ⤳ w := by
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  obtain ⟨y, rfl⟩ := exists_fromSpec_eq hU hx
  obtain ⟨r, hr0, hr⟩ := exists_uniformizer hU y ζ hζ hζ1
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hζU : ζ ∈ U := hζ.mem_open U.isOpen hx
  have hζr : ζ ∉ X.basicOpen r := by
    intro h
    have h1 := ord_germ_eq_zero r h
    rw [hr ζ hζ hζ1, if_pos rfl] at h1
    exact one_ne_zero h1
  refine ⟨r, hr0, hζr, fun w hw hwr => ?_⟩
  have hwU : w ∈ U := hw.mem_open U.isOpen hx
  obtain ⟨q, rfl⟩ := exists_fromSpec_eq hU hwU
  have hrq : r ∈ q.asIdeal := by
    by_contra h
    exact hwr ((fromSpec_mem_basicOpen_iff hU r q).mpr h)
  have : q.asIdeal.IsPrime := q.isPrime
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {r}) (J := q.asIdeal)
    ((Ideal.span_singleton_le_iff_mem _).mpr hrq)
  have hpp : p.IsPrime := hp.1.1
  have hrp : r ∈ p := hp.1.2 (Ideal.mem_span_singleton_self r)
  have hp1 : p.height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hp) ?_
    have hne : p ≠ ⊥ := fun h => hr0 (by rw [h] at hrp; exact hrp)
    rw [Order.one_le_iff_pos, pos_iff_ne_zero]
    exact fun h => hne (Ideal.height_eq_zero_iff_eq_bot.mp h)
  let pp : Spec Γ(X, U) := ⟨p, hpp⟩
  have hpp1 : coheight (hU.fromSpec pp) = 1 := by rw [coheight_fromSpec]; exact hp1
  have hppq : hU.fromSpec pp ⤳ hU.fromSpec q := (fromSpec_specializes_iff hU pp q).mpr hpq
  have hppy : hU.fromSpec pp ⤳ hU.fromSpec y := hppq.trans hw
  have hpos := ord_germ_pos (fromSpec_mem hU pp) hpp1 hr0
    (by rw [fromSpec_mem_basicOpen_iff]; exact not_not.mpr hrp)
  rw [hr _ hppy hpp1] at hpos
  split_ifs at hpos with heq
  · rw [← heq]; exact hppq
  · exact absurd hpos (lt_irrefl 0)

end

/-- Krull's principal ideal theorem on an affine chart. -/
lemma exists_coheight_le_one_not_mem_basicOpen {X : Scheme.{u}} [IsLocallyNoetherian X] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) (r : Γ(X, U)) (hxr : x ∉ X.basicOpen r) :
    ∃ v : X, v ⤳ x ∧ coheight v ≤ 1 ∧ v ∈ U ∧ v ∉ X.basicOpen r := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨y, rfl⟩ := exists_fromSpec_eq hU hx
  have hry : r ∈ y.asIdeal := by
    by_contra h
    exact hxr ((fromSpec_mem_basicOpen_iff hU r y).mpr h)
  have : y.asIdeal.IsPrime := y.isPrime
  obtain ⟨p, hp, hpy⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {r}) (J := y.asIdeal)
    ((Ideal.span_singleton_le_iff_mem _).mpr hry)
  have hpp : p.IsPrime := hp.1.1
  let pp : Spec Γ(X, U) := ⟨p, hpp⟩
  refine ⟨hU.fromSpec pp, (fromSpec_specializes_iff hU pp y).mpr hpy, ?_, fromSpec_mem hU pp, ?_⟩
  · rw [coheight_fromSpec]
    exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hp
  · rw [fromSpec_mem_basicOpen_iff]
    exact not_not.mpr (hp.1.2 (Ideal.mem_span_singleton_self r))

/-- E6-E7: a prime divisor `ζ` through `Δ x` (factorial stalk at `Δ x`) contains `Δ v` for some generalization `v`
of `x` of codimension at most one. -/
theorem exists_specializes_of_coheight_eq_one {V P : Scheme.{u}} [IsIntegral P] [IsLocallyNoetherian P]
    [IsLocallyNoetherian V] (Δ : V ⟶ P) (x : V) [UniqueFactorizationMonoid (P.presheaf.stalk (Δ x))]
    {ζ : P} (hζ : ζ ⤳ Δ x) (hζ1 : coheight ζ = 1) :
    ∃ v : V, v ⤳ x ∧ coheight v ≤ 1 ∧ ζ ⤳ Δ v := by
  obtain ⟨_, ⟨UP, hUP, rfl⟩, hxUP, -⟩ :=
    P.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (Δ x)) isOpen_univ
  replace hUP : IsAffineOpen UP := hUP
  obtain ⟨r, -, hζr, hr⟩ := exists_uniformizer_specializes hUP hxUP ζ hζ hζ1
  have hxr : Δ x ∉ P.basicOpen r := fun h => hζr (hζ.mem_open (P.basicOpen r).isOpen h)
  obtain ⟨_, ⟨UV, hUV, rfl⟩, hxUV, hUVle⟩ :=
    V.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (Δ ⁻¹ᵁ UP : Set V) from hxUP)
      (Δ ⁻¹ᵁ UP).isOpen
  replace hUV : IsAffineOpen UV := hUV
  let r' : Γ(V, UV) := Δ.appLE UP UV hUVle r
  have hbo : ∀ v ∈ UV, v ∈ V.basicOpen r' ↔ Δ v ∈ P.basicOpen r := by
    intro v hv
    rw [← SetLike.mem_coe, Scheme.basicOpen_appLE Δ UV UP hUVle r]
    exact ⟨fun h => h.2, fun h => ⟨hv, h⟩⟩
  obtain ⟨v, hvx, hv1, hvU, hvr⟩ :=
    exists_coheight_le_one_not_mem_basicOpen hUV hxUV r' (by rw [hbo x hxUV]; exact hxr)
  refine ⟨v, hvx, hv1, hr _ (hvx.map Δ.base.hom.continuous) ?_⟩
  rw [← hbo v hvU]
  exact hvr

end RamanujanPetersson.JacDivisors


end

-- ===== S4.Def_RP_JacDivisors_P =====
section

/-!
# S4-JacDivisors P (O14, steps E2 and E8: the difference map `Φ(v, w) = φ(v) φ(w)⁻¹` is defined on the diagonal)
For `V G : Over (Spec k)` with `G` a group object and a partial map `f : V ⇀ G` over `k` with domain `D`:
* `sqOpen D = pr₁⁻¹ D ∩ pr₂⁻¹ D ⊆ V ×_k V` and `quotHom f = (f ∘ pr₁) · (f ∘ pr₂)⁻¹ : sqOpen D ⟶ G` over `k`;
  `quotPM f` is the corresponding partial map `V ×_k V ⇀ G`.
* `quotHom_diag`: `Φ(Δ v) = e` (the unit point of `G`) for `v ∈ D`.
* `diag_mem_domain` (E8): if `D` contains every point of codimension at most one, `V ×_k V` is integral and locally
  Noetherian, and the stalk of `V ×_k V` at `Δ x` is factorial, then `Φ` is defined at `Δ x`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open AlgebraicGeometry CategoryTheory Order Topology MonoidalCategory MonObj CartesianMonoidalCategory

universe u

section
variable {k : Type u} [Field k] {V G : Over (Spec (.of k))}

/-- The diagonal `V ⟶ V ×_k V`. -/
noncomputable abbrev diag (V : Over (Spec (.of k))) : V ⟶ V ⊗ V := lift (𝟙 V) (𝟙 V)

/-- `pr₁⁻¹ D ∩ pr₂⁻¹ D`. -/
noncomputable def sqOpen (D : V.left.Opens) : (V ⊗ V).left.Opens :=
  (fst V V).left ⁻¹ᵁ D ⊓ (snd V V).left ⁻¹ᵁ D

/-- `sqOpen D` as an object over `k`. -/
noncomputable abbrev sqOver (D : V.left.Opens) : Over (Spec (.of k)) :=
  Over.mk ((sqOpen D).ι ≫ (V ⊗ V).hom)

lemma fst_diag_apply (v : V.left) : (fst V V).left ((diag V).left v) = v := by
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_fst]
  rfl

lemma snd_diag_apply (v : V.left) : (snd V V).left ((diag V).left v) = v := by
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd]
  rfl

lemma diag_mem {D : V.left.Opens} {v : V.left} (hv : v ∈ D) : (diag V).left v ∈ sqOpen D :=
  ⟨show (fst V V).left ((diag V).left v) ∈ D by rw [fst_diag_apply]; exact hv,
   show (snd V V).left ((diag V).left v) ∈ D by rw [snd_diag_apply]; exact hv⟩

lemma sqOpen_le_fst (D : V.left.Opens) : sqOpen D ≤ (fst V V).left ⁻¹ᵁ D := inf_le_left

lemma sqOpen_le_snd (D : V.left.Opens) : sqOpen D ≤ (snd V V).left ⁻¹ᵁ D := inf_le_right

lemma diag_le (D : V.left.Opens) : D ≤ (diag V).left ⁻¹ᵁ sqOpen D := fun _ hw => diag_mem hw

lemma diag_resLE_pr (D : V.left.Opens) (p : V ⊗ V ⟶ V) (hp : diag V ≫ p = 𝟙 V)
    (h₁ : D ≤ (diag V).left ⁻¹ᵁ sqOpen D) (h₂ : sqOpen D ≤ p.left ⁻¹ᵁ D) :
    (diag V).left.resLE (sqOpen D) D h₁ ≫ p.left.resLE D (sqOpen D) h₂ = 𝟙 _ := by
  rw [← cancel_mono D.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
    Scheme.Hom.resLE_comp_ι, Category.assoc, ← Over.comp_left, hp, Over.id_left,
    Category.comp_id, Category.id_comp]

/-- `f ∘ pr` on `sqOpen D`, as a map over `k`. -/
noncomputable def prRes (f : V.left.PartialMap G.left) (hf : f.hom ≫ G.hom = f.domain.ι ≫ V.hom)
    (p : V ⊗ V ⟶ V) (hp : sqOpen f.domain ≤ p.left ⁻¹ᵁ f.domain) : sqOver f.domain ⟶ G :=
  Over.homMk (p.left.resLE f.domain (sqOpen f.domain) hp ≫ f.hom) (by
    change (p.left.resLE _ _ hp ≫ f.hom) ≫ G.hom = (sqOpen f.domain).ι ≫ (V ⊗ V).hom
    rw [Category.assoc, hf, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Over.w p])

variable [GrpObj G]

/-- E2: `Φ = (f ∘ pr₁) · (f ∘ pr₂)⁻¹ : sqOpen D ⟶ G` over `k`. -/
noncomputable def quotHom (f : V.left.PartialMap G.left) (hf : f.hom ≫ G.hom = f.domain.ι ≫ V.hom) :
    sqOver f.domain ⟶ G :=
  prRes f hf (fst V V) (sqOpen_le_fst _) * (prRes f hf (snd V V) (sqOpen_le_snd _))⁻¹

/-- `Φ(Δ v)` is the unit point of `G` for `v ∈ D`. -/
lemma quotHom_diag (f : V.left.PartialMap G.left) (hf : f.hom ≫ G.hom = f.domain.ι ≫ V.hom)
    {v : V.left} (hv : v ∈ f.domain) :
    (quotHom f hf).left ⟨(diag V).left v, diag_mem hv⟩ = η[G].left (default : Spec (.of k)) := by
  let D' : Over (Spec (.of k)) := Over.mk (f.domain.ι ≫ V.hom)
  let fD : D' ⟶ G := Over.homMk f.hom hf
  let δ : D' ⟶ sqOver f.domain :=
    Over.homMk ((diag V).left.resLE (sqOpen f.domain) f.domain (diag_le _)) (by
      change _ ≫ (sqOpen f.domain).ι ≫ (V ⊗ V).hom = f.domain.ι ≫ V.hom
      rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Over.w (diag V)])
  have h1 : δ ≫ prRes f hf (fst V V) (sqOpen_le_fst _) = fD := by
    apply Over.OverMorphism.ext
    change (diag V).left.resLE _ _ _ ≫ (fst V V).left.resLE _ _ _ ≫ f.hom = f.hom
    rw [← Category.assoc, diag_resLE_pr _ _ (lift_fst _ _), Category.id_comp]
  have h2 : δ ≫ prRes f hf (snd V V) (sqOpen_le_snd _) = fD := by
    apply Over.OverMorphism.ext
    change (diag V).left.resLE _ _ _ ≫ (snd V V).left.resLE _ _ _ ≫ f.hom = f.hom
    rw [← Category.assoc, diag_resLE_pr _ _ (lift_snd _ _), Category.id_comp]
  have h : δ ≫ quotHom f hf = 1 := by
    rw [quotHom, comp_mul, GrpObj.comp_inv, h1, h2, mul_inv_cancel]
  have hδ : δ.left ⟨v, hv⟩ = ⟨(diag V).left v, diag_mem hv⟩ := by
    apply Subtype.ext
    change ((diag V).left.resLE (sqOpen f.domain) f.domain (diag_le _) ≫ (sqOpen f.domain).ι) ⟨v, hv⟩ = _
    rw [Scheme.Hom.resLE_comp_ι]
    rfl
  rw [← hδ]
  change (δ ≫ quotHom f hf).left ⟨v, hv⟩ = _
  rw [h, Hom.one_def]
  change η[G].left ((toUnit D').left ⟨v, hv⟩) = _
  congr 1
  exact @Subsingleton.elim (Spec (.of k)) _ _ _

/-- `Φ` as a partial map `V ×_k V ⇀ G`. -/
noncomputable def quotPM [IrreducibleSpace (V ⊗ V).left] [IrreducibleSpace V.left]
    (f : V.left.PartialMap G.left) (hf : f.hom ≫ G.hom = f.domain.ι ≫ V.hom) :
    (V ⊗ V).left.PartialMap G.left where
  domain := sqOpen f.domain
  dense_domain := (sqOpen f.domain).isOpen.dense ⟨_, diag_mem f.dense_domain.nonempty.choose_spec⟩
  hom := (quotHom f hf).left

lemma quotPM_comp [IrreducibleSpace (V ⊗ V).left] [IrreducibleSpace V.left]
    (f : V.left.PartialMap G.left) (hf : f.hom ≫ G.hom = f.domain.ι ≫ V.hom) :
    (quotPM f hf).hom ≫ G.hom = (quotPM f hf).domain.ι ≫ (V ⊗ V).hom :=
  Over.w (quotHom f hf)

/-- E8: the difference map is defined at `Δ x` for every `x`, provided the domain of `f` contains all points of
codimension at most one and the stalk of `V ×_k V` at `Δ x` is factorial. -/
theorem diag_mem_domain [IsIntegral (V ⊗ V).left] [IsLocallyNoetherian (V ⊗ V).left]
    [IrreducibleSpace V.left] [IsLocallyNoetherian V.left] [LocallyOfFiniteType G.hom]
    (f : V.left.PartialMap G.left) (hf : f.hom ≫ G.hom = f.domain.ι ≫ V.hom)
    (hcod : ∀ v : V.left, coheight v ≤ 1 → v ∈ f.domain) (x : V.left)
    [UniqueFactorizationMonoid ((V ⊗ V).left.presheaf.stalk ((diag V).left x))] :
    (diag V).left x ∈ (quotPM f hf).toRationalMap.domain := by
  by_contra hx
  obtain ⟨v₀, hv₀⟩ := f.dense_domain.nonempty
  obtain ⟨_, ⟨W, hW, rfl⟩, heW, -⟩ := G.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (η[G].left (default : Spec (.of k)))) isOpen_univ
  replace hW : IsAffineOpen W := hW
  have hΔW : ∀ (v : V.left) (hv : v ∈ f.domain),
      (quotPM f hf).hom ⟨(diag V).left v, diag_mem hv⟩ ∈ W := fun v hv => by
    change (quotHom f hf).left ⟨(diag V).left v, diag_mem hv⟩ ∈ W
    rw [quotHom_diag f hf hv]
    exact heW
  obtain ⟨ζ, hζx, hζ1, hζW⟩ := exists_not_mem_of_not_mem_domain (V ⊗ V).hom G.hom (quotPM f hf)
    (quotPM_comp f hf) hW (z₀ := (diag V).left v₀) (diag_mem hv₀) (hΔW v₀ hv₀) hx
  obtain ⟨v, -, hv1, hζv⟩ := exists_specializes_of_coheight_eq_one (diag V).left x hζx hζ1
  have hvD := hcod v hv1
  have hζN : ζ ∈ sqOpen f.domain := hζv.mem_open (sqOpen f.domain).isOpen (diag_mem hvD)
  apply hζW hζN
  have hsp : (⟨ζ, hζN⟩ : (quotPM f hf).domain) ⤳ ⟨(diag V).left v, diag_mem hvD⟩ :=
    (subtype_specializes_iff _ _).mpr hζv
  exact (hsp.map (quotPM f hf).hom.continuous).mem_open W.isOpen (hΔW v hvD)

end

end RamanujanPetersson.JacDivisors


end

-- ===== S4.Def_RP_JacDivisors_Q =====
section

/-!
# S4-JacDivisors Q (O14, steps E9-E10: Weil's extension theorem, Milne I.3.1-3.2)
For `V G : Over (Spec k)` (`k` algebraically closed), `G` a group object and `f : V ⇀ G` a partial map over `k`:
* `mem_domain_of_slice`: if `a ∈ dom f` is a `k`-point and the difference map `Φ(v, w) = f(v) f(w)⁻¹` is defined at
  `(x, a)`, then `f` extends to `x` (`v ↦ Φ(v, a) · f(a)` near `x`).
* `mem_domain_of_isClosed`: if `Φ` is defined at `Δ x` and `x` is closed, then `f` extends to `x`.
* `domain_eq_top` (E10): if `V` and `V ×_k V` are integral, locally Noetherian with factorial stalks, `V` is of finite type
  and `G` is separated, locally of finite type and satisfies the existence part of the valuative criterion (e.g. proper),
  then every rational map `V ⤏ G` over `k` is defined everywhere.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open AlgebraicGeometry CategoryTheory Limits Order Topology MonoidalCategory MonObj CartesianMonoidalCategory

universe u

/-- The maximal representative of a rational map between `S`-schemes is again an `S`-map. -/
lemma toPartialMap_comp {X Y S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) [IsReduced X] [Y.IsSeparated]
    [S.IsSeparated] (f : X.PartialMap Y) (hf : f.hom ≫ sY = f.domain.ι ≫ sX) :
    f.toRationalMap.toPartialMap.hom ≫ sY = f.toRationalMap.toPartialMap.domain.ι ≫ sX := by
  letI : X.Over S := ⟨sX⟩
  letI : Y.Over S := ⟨sY⟩
  haveI : f.IsOver S := Scheme.PartialMap.isOver_iff.mpr hf
  exact Scheme.PartialMap.isOver_iff.mp inferInstance

section
variable {k : Type u} [Field k] {V G : Over (Spec (.of k))}

lemma slice_fst_apply (a : 𝟙_ (Over (Spec (.of k))) ⟶ V) (v : V.left) :
    (fst V V).left ((slice a).left v) = v := by
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_fst]
  rfl

lemma slice_snd_apply (a : 𝟙_ (Over (Spec (.of k))) ⟶ V) (v : V.left) :
    (snd V V).left ((slice a).left v) = IsogDegA.pt V a := by
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd, Over.comp_left, Scheme.Hom.comp_apply]
  change a.left _ = a.left (IsogDegA.pt0 k)
  congr 1
  exact @Subsingleton.elim (Spec (.of k)) _ _ _

lemma slice_le (a : 𝟙_ (Over (Spec (.of k))) ⟶ V) (D : V.left.Opens) (ha : IsogDegA.pt V a ∈ D) :
    D ≤ (slice a).left ⁻¹ᵁ sqOpen D := fun v hv =>
  ⟨show (fst V V).left ((slice a).left v) ∈ D by rw [slice_fst_apply]; exact hv,
   show (snd V V).left ((slice a).left v) ∈ D by rw [slice_snd_apply]; exact ha⟩

lemma resLE_comp_resLE (D : V.left.Opens) (s : V ⟶ V ⊗ V) (p : V ⊗ V ⟶ V) (hp : s ≫ p = 𝟙 V)
    (h₁ : D ≤ s.left ⁻¹ᵁ sqOpen D) (h₂ : sqOpen D ≤ p.left ⁻¹ᵁ D) :
    s.left.resLE (sqOpen D) D h₁ ≫ p.left.resLE D (sqOpen D) h₂ = 𝟙 _ := by
  rw [← cancel_mono D.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
    Scheme.Hom.resLE_comp_ι, Category.assoc, ← Over.comp_left, hp, Over.id_left,
    Category.comp_id, Category.id_comp]

variable [GrpObj G]

/-- E9 (slice step): if `a` is a `k`-point in the domain of `f` and the difference map `Φ` is defined at `(x, a)`,
then `f` extends to `x`. -/
theorem mem_domain_of_slice [IrreducibleSpace V.left] [IsReduced (V ⊗ V).left]
    [IrreducibleSpace (V ⊗ V).left] [G.left.IsSeparated]
    (f : V.left.PartialMap G.left) (hf : f.hom ≫ G.hom = f.domain.ι ≫ V.hom)
    (a : 𝟙_ (Over (Spec (.of k))) ⟶ V) (ha : IsogDegA.pt V a ∈ f.domain) {x : V.left}
    (hx : (slice a).left x ∈ (quotPM f hf).toRationalMap.domain) : x ∈ f.toRationalMap.domain := by
  let Φ' := (quotPM f hf).toRationalMap.toPartialMap
  have hΦ' : Φ'.hom ≫ G.hom = Φ'.domain.ι ≫ (V ⊗ V).hom :=
    toPartialMap_comp (V ⊗ V).hom G.hom (quotPM f hf) (quotPM_comp f hf)
  have hsq : sqOpen f.domain ≤ Φ'.domain := (quotPM f hf).le_domain_toRationalMap
  have hsD : f.domain ≤ (slice a).left ⁻¹ᵁ sqOpen f.domain := slice_le a f.domain ha
  let N : V.left.Opens := (slice a).left ⁻¹ᵁ Φ'.domain
  have hDN : f.domain ≤ N := fun v hv => hsq (hsD hv)
  let D' : Over (Spec (.of k)) := Over.mk (f.domain.ι ≫ V.hom)
  let N' : Over (Spec (.of k)) := Over.mk (N.ι ≫ V.hom)
  let P' : Over (Spec (.of k)) := Over.mk (Φ'.domain.ι ≫ (V ⊗ V).hom)
  let fD : D' ⟶ G := Over.homMk f.hom hf
  let ΦO : P' ⟶ G := Over.homMk Φ'.hom hΦ'
  let sN : N' ⟶ P' := Over.homMk ((slice a).left.resLE Φ'.domain N le_rfl) (by
    change _ ≫ Φ'.domain.ι ≫ (V ⊗ V).hom = N.ι ≫ V.hom
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Over.w (slice a)])
  have hrange : Set.range a.left ⊆ Set.range f.domain.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    have hp : p = IsogDegA.pt0 k := @Subsingleton.elim (Spec (.of k)) _ _ _
    subst hp
    exact ha
  let aD : 𝟙_ (Over (Spec (.of k))) ⟶ D' := Over.homMk (IsOpenImmersion.lift f.domain.ι a.left hrange) (by
    change _ ≫ f.domain.ι ≫ V.hom = _
    rw [← Category.assoc, IsOpenImmersion.lift_fac, Over.w a])
  let c : 𝟙_ (Over (Spec (.of k))) ⟶ G := aD ≫ fD
  let Ψ : N' ⟶ G := sN ≫ ΦO * (toUnit N' ≫ c)
  let iD : D' ⟶ N' := Over.homMk (V.left.homOfLE hDN) (by
    change _ ≫ N.ι ≫ V.hom = f.domain.ι ≫ V.hom
    rw [← Category.assoc, Scheme.homOfLE_ι])
  let δ : D' ⟶ sqOver f.domain := Over.homMk ((slice a).left.resLE (sqOpen f.domain) f.domain hsD) (by
    change _ ≫ (sqOpen f.domain).ι ≫ (V ⊗ V).hom = f.domain.ι ≫ V.hom
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Over.w (slice a)])
  have h1 : δ ≫ prRes f hf (fst V V) (sqOpen_le_fst _) = fD := by
    apply Over.OverMorphism.ext
    change (slice a).left.resLE _ _ _ ≫ (fst V V).left.resLE _ _ _ ≫ f.hom = f.hom
    rw [← Category.assoc, resLE_comp_resLE _ _ _ (lift_fst _ _), Category.id_comp]
  have h2 : δ ≫ prRes f hf (snd V V) (sqOpen_le_snd _) = toUnit D' ≫ c := by
    apply Over.OverMorphism.ext
    change (slice a).left.resLE _ _ _ ≫ (snd V V).left.resLE _ _ _ ≫ f.hom =
      (toUnit D').left ≫ IsOpenImmersion.lift f.domain.ι a.left hrange ≫ f.hom
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    rw [← cancel_mono f.domain.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
      Scheme.Hom.resLE_comp_ι, Category.assoc, Category.assoc, IsOpenImmersion.lift_fac,
      ← Over.comp_left, lift_snd, Over.comp_left, ← Category.assoc]
    congr 1
  have hres : (V ⊗ V).left.homOfLE hsq ≫ Φ'.hom = (quotPM f hf).hom :=
    (quotPM f hf).toPartialMap_toRationalMap_restrict
  have hfΦ : iD ≫ sN ≫ ΦO = δ ≫ quotHom f hf := by
    apply Over.OverMorphism.ext
    change V.left.homOfLE hDN ≫ (slice a).left.resLE Φ'.domain N le_rfl ≫ Φ'.hom =
      (slice a).left.resLE (sqOpen f.domain) f.domain hsD ≫ (quotPM f hf).hom
    rw [← hres, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← cancel_mono Φ'.domain.ι]
    simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc]
  have hΨ : iD ≫ Ψ = fD := by
    change iD ≫ (sN ≫ ΦO * (toUnit N' ≫ c)) = fD
    rw [comp_mul, hfΦ, ← Category.assoc, comp_toUnit, quotHom, comp_mul, GrpObj.comp_inv, h1, h2,
      inv_mul_cancel_right]
  let g : V.left.PartialMap G.left :=
    ⟨N, N.isOpen.dense ⟨_, hDN f.dense_domain.nonempty.choose_spec⟩, Ψ.left⟩
  have heq : g.equiv f := by
    refine ⟨f.domain, f.dense_domain, hDN, le_rfl, ?_⟩
    simp only [Scheme.PartialMap.restrict_hom, Scheme.homOfLE_rfl, Category.id_comp]
    exact congrArg (fun φ => φ.left) hΨ
  exact Scheme.RationalMap.mem_domain.mpr ⟨g, hx, Scheme.PartialMap.toRationalMap_eq_iff.mpr heq⟩

/-- E9: if the difference map is defined at `Δ x` for a closed point `x`, then `f` extends to `x`. -/
theorem mem_domain_of_isClosed [IsAlgClosed k] [LocallyOfFiniteType V.hom] [IrreducibleSpace V.left]
    [IsReduced (V ⊗ V).left] [IrreducibleSpace (V ⊗ V).left] [G.left.IsSeparated]
    (f : V.left.PartialMap G.left) (hf : f.hom ≫ G.hom = f.domain.ι ≫ V.hom) {x : V.left}
    (hx : IsClosed ({x} : Set V.left)) (hΔ : (diag V).left x ∈ (quotPM f hf).toRationalMap.domain) :
    x ∈ f.toRationalMap.domain := by
  haveI : JacobsonSpace V.left := LocallyOfFiniteType.jacobsonSpace V.hom
  obtain ⟨b, rfl⟩ := IsogDegA.exists_pt_eq V x hx
  let t : V ⟶ V ⊗ V := lift (toUnit V ≫ b) (𝟙 V)
  have e1 : b ≫ toUnit V = 𝟙 _ := toUnit_unique _ _
  have hbt : b ≫ t = b ≫ diag V := by
    simp only [t, comp_lift, Category.comp_id, reassoc_of% e1]
  have htx : t.left (IsogDegA.pt V b) = (diag V).left (IsogDegA.pt V b) := by
    rw [← IsogDegA.pt_comp, ← IsogDegA.pt_comp, hbt]
  let O : V.left.Opens := t.left ⁻¹ᵁ (quotPM f hf).toRationalMap.domain
  have hO : ((O : Set V.left) ∩ (f.domain : Set V.left)).Nonempty :=
    nonempty_preirreducible_inter O.isOpen f.domain.isOpen
      ⟨IsogDegA.pt V b, show t.left _ ∈ _ by rw [htx]; exact hΔ⟩ f.dense_domain.nonempty
  obtain ⟨a, haO, hacl⟩ := nonempty_inter_closedPoints hO (O.isOpen.inter f.domain.isOpen).isLocallyClosed
  obtain ⟨c, rfl⟩ := IsogDegA.exists_pt_eq V a hacl
  have e2 : c ≫ toUnit V = 𝟙 _ := toUnit_unique _ _
  refine mem_domain_of_slice f hf c haO.2 ?_
  have hbc : b ≫ slice c = c ≫ t := by
    simp only [slice, t, comp_lift, Category.comp_id, reassoc_of% e1, reassoc_of% e2]
  rw [← IsogDegA.pt_comp, hbc, IsogDegA.pt_comp]
  exact haO.1

/-- E10, **Weil's extension theorem** (factorial-stalk form): a rational map over `k` from `V` (with `V` and `V ×_k V`
integral, locally Noetherian, with factorial local rings) to a separated group `G` satisfying the existence part of the
valuative criterion is defined everywhere. -/
theorem domain_eq_top [IsAlgClosed k] [LocallyOfFiniteType V.hom] [LocallyOfFiniteType G.hom] [IsSeparated G.hom]
    [IsIntegral V.left] [IsLocallyNoetherian V.left] [IsIntegral (V ⊗ V).left] [IsLocallyNoetherian (V ⊗ V).left]
    [∀ v : V.left, UniqueFactorizationMonoid (V.left.presheaf.stalk v)]
    [∀ p : (V ⊗ V).left, UniqueFactorizationMonoid ((V ⊗ V).left.presheaf.stalk p)]
    (hY : ValuativeCriterion.Existence G.hom)
    (f : V.left.PartialMap G.left) (hf : f.hom ≫ G.hom = f.domain.ι ≫ V.hom) :
    f.toRationalMap.domain = ⊤ := by
  haveI : G.left.IsSeparated := ⟨by rw [← terminal.comp_from G.hom]; infer_instance⟩
  haveI : JacobsonSpace V.left := LocallyOfFiniteType.jacobsonSpace V.hom
  let f' := f.toRationalMap.toPartialMap
  have hf' : f'.hom ≫ G.hom = f'.domain.ι ≫ V.hom := toPartialMap_comp V.hom G.hom f hf
  have hcod : ∀ v : V.left, coheight v ≤ 1 → v ∈ f'.domain := fun v hv =>
    mem_domain_of_coheight_le_one V.hom G.hom hY f hf hv
  have hcl : ∀ x : V.left, IsClosed ({x} : Set V.left) → x ∈ f.toRationalMap.domain := by
    intro x hx
    have h := mem_domain_of_isClosed f' hf' hx (diag_mem_domain f' hf' hcod x)
    rwa [Scheme.RationalMap.toRationalMap_toPartialMap] at h
  refine top_unique fun x _ => ?_
  by_contra hx
  obtain ⟨y, hy, hycl⟩ := nonempty_inter_closedPoints (Z := ((f.toRationalMap.domain : Set V.left))ᶜ)
    ⟨x, hx⟩ f.toRationalMap.domain.isOpen.isClosed_compl.isLocallyClosed
  exact hy (hcl y hycl)

end

end RamanujanPetersson.JacDivisors


end

-- ===== S4.Def_RP_JacDivisors_R =====
section

/-!
# S4-JacDivisors R (O10, algebra part): étale over a regular ring is regular
* `isRegularLocalRing_of_etale_of_liesOver`, `isRegularLocalRing_of_etale`: if `A` is a regular
  ring and `B` is an étale `A`-algebra, then `B_Q` is a regular local ring for every prime `Q`.
* `isRegularRing_of_etale`: `B` is a regular ring.
Proof: `m_{B_Q} = p B_Q` (unramified), so `m_{B_Q}` needs at most `dim A_p = ht p` generators,
and `ht p ≤ ht Q` by going-down (flat).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open IsLocalRing

universe u v

theorem isRegularLocalRing_of_etale_of_liesOver {A : Type u} {B : Type v} [CommRing A]
    [CommRing B] [Algebra A B] [IsRegularRing A] [Algebra.Etale A B] (p : Ideal A) [p.IsPrime]
    (Q : Ideal B) [Q.IsPrime] [Q.LiesOver p] :
    IsRegularLocalRing (Localization.AtPrime Q) := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  let := Localization.AtPrime.algebraOfLiesOver p Q
  have hun : Algebra.IsUnramifiedAt A Q := by
    show Algebra.FormallyUnramified A (Localization.AtPrime Q)
    have : Algebra.FormallyUnramified B (Localization.AtPrime Q) :=
      Algebra.FormallyUnramified.of_isLocalization Q.primeCompl
    exact Algebra.FormallyUnramified.comp A B _
  have hmap : p.map (algebraMap A (Localization.AtPrime Q)) = maximalIdeal _ :=
    ((Algebra.isUnramifiedAt_iff_map_eq A p Q).mp hun).2
  have e : p.map (algebraMap A (Localization.AtPrime Q)) =
      (maximalIdeal (Localization.AtPrime p)).map
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime Q)) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
  have h1 : (maximalIdeal (Localization.AtPrime Q)).spanFinrank ≤
      (maximalIdeal (Localization.AtPrime p)).spanFinrank := by
    rw [← hmap, e]
    exact Ideal.spanFinrank_map_le_of_fg _ (IsNoetherian.noetherian _)
  have h2 : ((maximalIdeal (Localization.AtPrime p)).spanFinrank : WithBot ℕ∞) = p.height := by
    rw [IsRegularLocalRing.spanFinrank_maximalIdeal,
      IsLocalization.AtPrime.ringKrullDim_eq_height p]
  have h3 : p.height ≤ Q.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p Q]
    exact le_self_add
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q]
  calc ((maximalIdeal (Localization.AtPrime Q)).spanFinrank : WithBot ℕ∞)
      ≤ ((maximalIdeal (Localization.AtPrime p)).spanFinrank : WithBot ℕ∞) := by
        exact_mod_cast h1
    _ = p.height := h2
    _ ≤ Q.height := by exact_mod_cast h3

theorem isRegularLocalRing_of_etale {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] [IsRegularRing A] [Algebra.Etale A B] (Q : Ideal B) [Q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime Q) :=
  isRegularLocalRing_of_etale_of_liesOver (Q.under A) Q

theorem isRegularRing_of_etale {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] [IsRegularRing A] [Algebra.Etale A B] : IsRegularRing B := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  rw [isRegularRing_iff]
  intro Q _
  exact isRegularLocalRing_of_etale (A := A) Q

end RamanujanPetersson.JacDivisors


end

-- ===== S4.Def_RP_JacDivisors_A =====
section

/-!
# S4-JacDivisors A (O1): first facts on regular local rings
For `x ∈ m \ m²` in a regular local ring `R`, `R ⧸ (x)` is regular local with one generator fewer;
regular local rings are domains; such `x` generate prime ideals.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open IsLocalRing Ideal

universe u

section Cotangent

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A nonzero vector extends to a spanning set with `finrank` elements. -/
theorem exists_finite_span_insert {v : V} (hv : v ≠ 0) :
    ∃ t : Set V, t.Finite ∧ t.ncard + 1 ≤ Module.finrank K V ∧
      Submodule.span K (insert v t) = ⊤ := by
  have hs : LinearIndepOn K id ({v} : Set V) := (linearIndepOn_singleton_iff K (v := id)).mpr hv
  let b := Module.Basis.extend hs
  set T := hs.extend (Set.subset_univ _) with hTdef
  have : Finite T := Module.Finite.finite_basis b
  have hT : T.Finite := Set.toFinite T
  have hvT : v ∈ T := hs.subset_extend _ (Set.mem_singleton v)
  refine ⟨T \ {v}, hT.sdiff, ?_, ?_⟩
  · rw [Set.ncard_sdiff_singleton_add_one hvT hT, Module.finrank_eq_nat_card_basis b,
      Nat.card_coe_set_eq]
  · rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hvT]
    have h := (Module.Basis.extend hs).span_eq
    rw [Module.Basis.range_extend] at h
    exact h

end Cotangent

variable {R : Type u} [CommRing R]

theorem isLocalRing_quotient_span [IsLocalRing R] {x : R} (hx : x ∈ maximalIdeal R) :
    IsLocalRing (R ⧸ span {x}) := by
  have : Nontrivial (R ⧸ span {x}) := Ideal.Quotient.nontrivial_iff.mpr (by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact (IsLocalRing.mem_maximalIdeal x).mp hx)
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- `x ∈ m \ m²` is part of a minimal generating set of `m`. -/
theorem exists_span_insert_eq_maximalIdeal [IsLocalRing R] [IsNoetherianRing R]
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    ∃ t : Set R, t.Finite ∧ t.ncard + 1 ≤ (maximalIdeal R).spanFinrank ∧
      Ideal.span (insert x t) = maximalIdeal R := by
  have hv : (maximalIdeal R).toCotangent ⟨x, hx⟩ ≠ 0 := by
    rwa [Ne, Ideal.toCotangent_eq_zero]
  obtain ⟨t, htf, htc, hts⟩ := exists_finite_span_insert (K := ResidueField R) hv
  choose ℓ hℓ using fun w : CotangentSpace R => (maximalIdeal R).toCotangent_surjective w
  refine ⟨(fun w => (ℓ w : R)) '' t, htf.image _, ?_, ?_⟩
  · calc _ ≤ t.ncard + 1 := by gcongr; exact Set.ncard_image_le htf
      _ ≤ _ := by rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]; exact htc
  · have key : Submodule.span R (insert (⟨x, hx⟩ : maximalIdeal R) (ℓ '' t)) = ⊤ := by
      rw [← CotangentSpace.span_image_eq_top_iff, Set.image_insert_eq, Set.image_image]
      simpa [hℓ] using hts
    have := congrArg (Submodule.map (maximalIdeal R).subtype) key
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, Set.image_insert_eq,
      Set.image_image] at this
    exact this

theorem spanFinrank_maximalIdeal_quotient_add_one_le [IsLocalRing R] [IsNoetherianRing R]
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    [IsLocalRing (R ⧸ span {x})] :
    (maximalIdeal (R ⧸ span {x})).spanFinrank + 1 ≤ (maximalIdeal R).spanFinrank := by
  obtain ⟨t, htf, htc, hts⟩ := exists_span_insert_eq_maximalIdeal hx hx2
  have hmap : maximalIdeal (R ⧸ span {x}) = Ideal.span (Ideal.Quotient.mk (span {x}) '' t) := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective, ← hts,
      Ideal.map_span, Set.image_insert_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr (mem_span_singleton_self x), Ideal.span_insert_zero]
  calc _ ≤ ((Ideal.Quotient.mk (span {x})) '' t).ncard + 1 := by
        rw [hmap]; gcongr; exact Submodule.spanFinrank_span_le_ncard_of_finite (htf.image _)
    _ ≤ t.ncard + 1 := by gcongr; exact Set.ncard_image_le htf
    _ ≤ _ := htc

/-- The Krull dimension of a Noetherian local ring is a natural number. -/
theorem exists_nat_ringKrullDim_eq [IsLocalRing R] [IsNoetherianRing R] :
    ∃ k : ℕ, ringKrullDim R = k := by
  have h := ringKrullDim_le_spanFinrank_maximalIdeal R
  have h0 : ringKrullDim R ≠ ⊥ := by
    intro h'
    have h0' := ringKrullDim_nonneg_of_nontrivial (R := R)
    rw [h'] at h0'
    exact absurd h0' (by simp)
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp h0
  rw [← ha] at h ⊢
  have ha' : a ≤ (maximalIdeal R).spanFinrank := WithBot.coe_le_coe.mp h
  obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top _) ha')
  exact ⟨k, rfl⟩

/-- `R ⧸ (x)` is regular local for `x ∈ m \ m²`, and its maximal ideal needs one generator fewer. -/
theorem isRegularLocalRing_quotient [IsRegularLocalRing R] {x : R} (hx : x ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ span {x})] :
    IsRegularLocalRing (R ⧸ span {x}) ∧
      (maximalIdeal (R ⧸ span {x})).spanFinrank + 1 = (maximalIdeal R).spanFinrank := by
  have h1 := spanFinrank_maximalIdeal_quotient_add_one_le hx hx2
  have h2 : ringKrullDim R ≤ ringKrullDim (R ⧸ span {x}) + 1 := by
    have := ringKrullDim_le_ringKrullDim_quotient_add_encard (R := R) ({x} : Set R)
      (by simpa [IsLocalRing.ringJacobson_eq_maximalIdeal] using hx)
    simpa using this
  have h3 := ringKrullDim_le_spanFinrank_maximalIdeal (R ⧸ span {x})
  have h4 : ringKrullDim R = (maximalIdeal R).spanFinrank :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  obtain ⟨k, hk⟩ := exists_nat_ringKrullDim_eq (R := R ⧸ span {x})
  rw [hk] at h2 h3
  rw [h4] at h2
  have h2' : (maximalIdeal R).spanFinrank ≤ k + 1 := by exact_mod_cast h2
  have h3' : k ≤ (maximalIdeal (R ⧸ span {x})).spanFinrank := by exact_mod_cast h3
  refine ⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_, by omega⟩
  rw [hk]
  exact_mod_cast (by omega : (maximalIdeal (R ⧸ span {x})).spanFinrank ≤ k)

/-- Prime avoidance: an element of `m` outside `m²` and outside every minimal prime. -/
theorem exists_mem_maximalIdeal_avoid [IsLocalRing R] [IsNoetherianRing R]
    (hm : ¬ maximalIdeal R ≤ maximalIdeal R ^ 2) (hmin : maximalIdeal R ∉ minimalPrimes R) :
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ ∀ P ∈ minimalPrimes R, x ∉ P := by
  classical
  by_contra hcon
  push Not at hcon
  let s : Finset (Ideal R) := insert (maximalIdeal R ^ 2)
    (minimalPrimes.finite_of_isNoetherianRing R).toFinset
  have hp : ∀ i ∈ s, i ≠ maximalIdeal R ^ 2 → i ≠ maximalIdeal R ^ 2 → IsPrime (id i) := by
    intro i hi h1 _
    rcases Finset.mem_insert.mp hi with h | h
    · exact absurd h h1
    · exact ((Set.Finite.mem_toFinset _).mp h).1.1
  have hsub : ((maximalIdeal R : Set R)) ⊆ ⋃ i ∈ (↑s : Set (Ideal R)), id i := by
    intro y hy
    simp only [id, Set.mem_iUnion, SetLike.mem_coe, exists_prop]
    by_cases hy2 : y ∈ maximalIdeal R ^ 2
    · exact ⟨_, by simp [s], hy2⟩
    · obtain ⟨P, hP, hyP⟩ := hcon y hy hy2
      exact ⟨P, by simp [s, hP], hyP⟩
  obtain ⟨i, hi, hle⟩ := (Ideal.subset_union_prime _ _ hp).mp hsub
  rcases Finset.mem_insert.mp hi with h | h
  · exact hm (h ▸ hle)
  · have hP := (Set.Finite.mem_toFinset _).mp h
    have heq : i = maximalIdeal R := le_antisymm (le_maximalIdeal hP.1.1.ne_top) hle
    exact hmin (heq ▸ hP)

/-- Regular local rings are domains (induction on the number of generators of `m`). -/
theorem isDomain_of_spanFinrank_eq : ∀ (n : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R],
    (maximalIdeal R).spanFinrank = n → IsDomain R := by
  intro n
  induction n with
  | zero =>
    intro R _ _ h
    have hb : maximalIdeal R = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot (maximalIdeal R).fg_of_isNoetherianRing).mp h
    let := ((isField_iff_maximalIdeal_eq).mpr hb).toField
    infer_instance
  | succ n ih =>
    intro R _ _ h
    have hm : ¬ maximalIdeal R ≤ maximalIdeal R ^ 2 := by
      intro hle
      have hb : maximalIdeal R = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _
        (maximalIdeal R).fg_of_isNoetherianRing (by rwa [pow_two] at hle)
        (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top])
      rw [hb, Submodule.spanFinrank_bot] at h
      omega
    have hmin : maximalIdeal R ∉ minimalPrimes R := by
      intro hmin
      have h0 := (Ideal.height_eq_zero_iff (I := maximalIdeal R)).mpr hmin
      have h5 : ringKrullDim R = (maximalIdeal R).spanFinrank :=
        (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
      rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h0, h] at h5
      norm_cast at h5
    obtain ⟨x, hx, hx2, hxmin⟩ := exists_mem_maximalIdeal_avoid hm hmin
    haveI : IsLocalRing (R ⧸ span {x}) := isLocalRing_quotient_span hx
    obtain ⟨hreg, hcard⟩ := isRegularLocalRing_quotient hx hx2
    haveI := hreg
    have hdom : IsDomain (R ⧸ span {x}) := ih _ (by omega)
    haveI hprime : (span {x}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp hdom
    obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal R) ≤ span {x})
    have hxP : x ∉ P := hxmin P hP
    have hPsm : P ≤ maximalIdeal R • P := by
      intro p hp
      obtain ⟨r, rfl⟩ := mem_span_singleton'.mp (hPle hp)
      have hr : r ∈ P := (hP.1.1.mem_or_mem hp).resolve_right hxP
      rw [mul_comm]
      exact Submodule.smul_mem_smul hx hr
    have hP0 : P = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _
      P.fg_of_isNoetherianRing hPsm (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top])
    haveI : (⊥ : Ideal R).IsPrime := hP0 ▸ hP.1.1
    exact IsDomain.of_bot_isPrime R

instance isDomain_of_isRegularLocalRing [IsRegularLocalRing R] : IsDomain R :=
  isDomain_of_spanFinrank_eq _ R rfl

/-- For `x ∈ m \ m²` in a regular local ring, `(x)` is prime. -/
theorem isPrime_span_of_not_mem_sq [IsRegularLocalRing R] {x : R} (hx : x ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) : (span {x}).IsPrime := by
  haveI : IsLocalRing (R ⧸ span {x}) := isLocalRing_quotient_span hx
  haveI := (isRegularLocalRing_quotient hx hx2).1
  exact (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance

end RamanujanPetersson.JacDivisors


end

-- ===== S4.Def_RP_JacDivisors_B =====
section

/-!
# S4-JacDivisors B (O3b, O5): change of rings and Serre's easy direction
* `hasPDLT_restrict`: if `x` is `R`-regular and `E` is an `R ⧸ (x)`-module with `pd < n + 1`, then
  `pd_R E < n + 2`.
* `exists_hasPDLT_of_isRegularLocalRing`: over a regular local ring every finite module has finite
  projective dimension.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open CategoryTheory IsLocalRing Ideal
open scoped Pointwise

universe u

variable {R : Type u} [CommRing R]

/-- Restriction of `ModuleCat.of (R ⧸ I) M` along `R → R ⧸ I`, for compatible actions. -/
noncomputable def restrictOfIso (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M]
    [Module (R ⧸ I) M] (h : ∀ (r : R) (m : M), Ideal.Quotient.mk I r • m = r • m) :
    (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj (ModuleCat.of (R ⧸ I) M) ≅
      ModuleCat.of R M :=
  let e : ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj (ModuleCat.of (R ⧸ I) M)) ≃ₗ[R] M :=
    { toFun := fun m => m
      invFun := fun m => m
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => h r m
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  e.toModuleIso

theorem isSMulRegular_finsupp {x : R} (hx : IsSMulRegular R x) (ι : Type u) :
    IsSMulRegular (ι →₀ R) x := fun f g h => Finsupp.ext fun i => hx (by
  simpa using DFunLike.congr_fun h i)

theorem ker_mapRange_mkQ (x : R) (ι : Type u) :
    LinearMap.ker (Finsupp.mapRange.linearMap (Submodule.mkQ (span {x})) :
      (ι →₀ R) →ₗ[R] (ι →₀ R ⧸ span {x})) = x • (⊤ : Submodule R (ι →₀ R)) := by
  rw [Finsupp.ker_mapRange, Submodule.ker_mkQ, ← (span {x}).mul_top, ← smul_eq_mul,
    Finsupp.submodule_smul]
  simp [Submodule.ideal_span_singleton_smul]

/-- `(R/x)^(ι)` has projective dimension `< 2` over `R` when `x` is `R`-regular. -/
theorem hasPDLT_restrict_finsupp {x : R} (hx : IsSMulRegular R x) (ι : Type u) :
    HasProjectiveDimensionLT ((ModuleCat.restrictScalars (Ideal.Quotient.mk (span {x}))).obj
      (ModuleCat.of (R ⧸ span {x}) (ι →₀ R ⧸ span {x}))) 2 := by
  have hS : (ModuleCat.smulShortComplex (ModuleCat.of R (ι →₀ R)) x).ShortExact :=
    IsSMulRegular.smulShortComplex_shortExact (isSMulRegular_finsupp hx ι)
  have : Projective (ModuleCat.of R (ι →₀ R)) :=
    ModuleCat.projective_of_free Finsupp.basisSingleOne
  have h3 : HasProjectiveDimensionLT (ModuleCat.of R (QuotSMulTop x (ι →₀ R))) 2 :=
    hS.hasProjectiveDimensionLT_X₃ 1
      (inferInstance : HasProjectiveDimensionLT (ModuleCat.of R (ι →₀ R)) 1)
      (hasProjectiveDimensionLT_of_ge (ModuleCat.of R (ι →₀ R)) 1 2 (by norm_num))
  let e : QuotSMulTop x (ι →₀ R) ≃ₗ[R] (ι →₀ R ⧸ span {x}) :=
    (Submodule.quotEquivOfEq _ _ (ker_mapRange_mkQ x ι).symm).trans
      (LinearMap.quotKerEquivOfSurjective (Finsupp.mapRange.linearMap (Submodule.mkQ (span {x})))
        (by exact Finsupp.mapRange_surjective _ (map_zero _) (Submodule.mkQ_surjective (span {x}))))
  have := hasProjectiveDimensionLT_of_iso e.toModuleIso 2
  exact hasProjectiveDimensionLT_of_iso (restrictOfIso (span {x}) (ι →₀ R ⧸ span {x})
    (fun r f => by rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul])).symm 2

/-- O3b: `pd_R E ≤ pd_{R/x} E + 1` for an `R ⧸ (x)`-module `E`, when `x` is `R`-regular. -/
theorem hasPDLT_restrict {x : R} (hx : IsSMulRegular R x) : ∀ (n : ℕ)
    (E : ModuleCat.{u} (R ⧸ span {x})), HasProjectiveDimensionLT E (n + 1) →
      HasProjectiveDimensionLT
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk (span {x}))).obj E) (n + 2) := by
  intro n
  induction n with
  | zero =>
    intro E hE
    have : Projective E := projective_iff_hasProjectiveDimensionLT_one.mpr hE
    let p : ModuleCat.of (R ⧸ span {x}) (E →₀ R ⧸ span {x}) ⟶ E :=
      ModuleCat.ofHom (Finsupp.linearCombination _ id)
    have : Epi p := (ModuleCat.epi_iff_surjective _).mpr
      (fun e => ⟨Finsupp.single e 1, by simp [p]⟩)
    let rt : Retract E (ModuleCat.of (R ⧸ span {x}) (E →₀ R ⧸ span {x})) :=
      ⟨Projective.factorThru (𝟙 E) p, p, Projective.factorThru_comp _ _⟩
    have := hasPDLT_restrict_finsupp hx E
    exact (rt.map (ModuleCat.restrictScalars (Ideal.Quotient.mk (span {x})))).hasProjectiveDimensionLT 2
  | succ n ih =>
    intro E hE
    let f : (E →₀ R ⧸ span {x}) →ₗ[R ⧸ span {x}] E := Finsupp.linearCombination _ id
    have surj : Function.Surjective f := fun e => ⟨Finsupp.single e 1, by simp [f]⟩
    have hS := LinearMap.shortExact_shortComplexKer surj
    have : Projective (ModuleCat.of (R ⧸ span {x}) (E →₀ R ⧸ span {x})) :=
      ModuleCat.projective_of_free Finsupp.basisSingleOne
    have hK := (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp hE
    have hS' := hS.map_of_exact (ModuleCat.restrictScalars (Ideal.Quotient.mk (span {x})))
    have := hasPDLT_restrict_finsupp hx E
    exact hS'.hasProjectiveDimensionLT_X₃ (n + 2) (ih _ hK)
      (hasProjectiveDimensionLT_of_ge ((ModuleCat.restrictScalars (Ideal.Quotient.mk (span {x}))).obj
        (ModuleCat.of (R ⧸ span {x}) (E →₀ R ⧸ span {x}))) 2 (n + 3) (by omega))

/-- `x ∈ m \ m²` exists when `m` needs at least one generator. -/
theorem exists_mem_maximalIdeal_not_mem_sq [IsLocalRing R] [IsNoetherianRing R]
    (h : (maximalIdeal R).spanFinrank ≠ 0) : ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 := by
  refine SetLike.not_le_iff_exists.mp fun hle => h ?_
  have hb : maximalIdeal R = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _
    (maximalIdeal R).fg_of_isNoetherianRing (by rwa [pow_two] at hle)
    (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top])
  rw [hb, Submodule.spanFinrank_bot]

/-- O5 (Serre, easy direction): over a regular local ring every finite module has finite
projective dimension (induction on the number of generators of `m`). -/
theorem exists_hasPDLT_of_spanFinrank : ∀ (d : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R],
    (maximalIdeal R).spanFinrank = d → ∀ (M : ModuleCat.{u} R), Module.Finite R M →
      ∃ n : ℕ, HasProjectiveDimensionLT M n := by
  intro d
  induction d with
  | zero =>
    intro R _ _ h M _
    have hb : maximalIdeal R = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot (maximalIdeal R).fg_of_isNoetherianRing).mp h
    let := ((isField_iff_maximalIdeal_eq).mpr hb).toField
    have : Module.Free R M := Module.Free.of_divisionRing R M
    have : Projective M := ModuleCat.projective_of_free (Module.Free.chooseBasis R M)
    exact ⟨1, inferInstance⟩
  | succ d ih =>
    intro R _ _ h M _
    obtain ⟨x, hx, hx2⟩ := exists_mem_maximalIdeal_not_mem_sq (R := R) (by omega)
    have : IsLocalRing (R ⧸ span {x}) := isLocalRing_quotient_span hx
    obtain ⟨hreg, hcard⟩ := isRegularLocalRing_quotient hx hx2
    have := hreg
    have hx0 : x ≠ 0 := fun h0 => hx2 (h0 ▸ zero_mem _)
    have hxR : IsSMulRegular R x := IsSMulRegular.of_ne_zero hx0
    obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R M
    have hS := LinearMap.shortExact_shortComplexKer hf
    have hxK : IsSMulRegular (LinearMap.ker f) x := IsSMulRegular.of_ne_zero hx0
    have : Module.Finite (R ⧸ span {x}) (QuotSMulTop x (LinearMap.ker f)) :=
      Module.Finite.of_restrictScalars_finite R _ _
    obtain ⟨m, hm⟩ := ih (R ⧸ span {x}) (by omega)
      (ModuleCat.of (R ⧸ span {x}) (QuotSMulTop x (LinearMap.ker f))) inferInstance
    have h1 : HasProjectiveDimensionLT
        (ModuleCat.of (R ⧸ span {x}) (QuotSMulTop x (LinearMap.ker f))) (m + 1) :=
      hasProjectiveDimensionLT_of_ge _ m (m + 1) (by omega)
    have := hasPDLT_restrict hxR m _ h1
    have h3 : HasProjectiveDimensionLT (ModuleCat.of R (QuotSMulTop x (LinearMap.ker f))) (m + 2) :=
      hasProjectiveDimensionLT_of_iso (restrictOfIso (span {x}) (QuotSMulTop x (LinearMap.ker f))
        (fun r q => Module.IsTorsionBy.mk_smul (Module.isTorsionBy_quotient_element_smul _ x) r q)) _
    have h3' := (projectiveDimension_le_iff _ (m + 1)).mpr h3
    have h4 := ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular
      (ModuleCat.of R (LinearMap.ker f)) x hxK hx
    have h5 := h4.symm.trans_le h3'
    have h6 : HasProjectiveDimensionLT (ModuleCat.of R (LinearMap.ker f)) (m + 1) :=
      projectiveDimension_lt_iff.mp (ENat.WithBot.add_one_le_natCast_iff.mp h5)
    have : Projective (ModuleCat.of R P) := ModuleCat.projective_of_free (Module.Free.chooseBasis R P)
    exact ⟨m + 2, hS.hasProjectiveDimensionLT_X₃ (m + 1) h6
      (hasProjectiveDimensionLT_of_ge (ModuleCat.of R P) 1 (m + 2) (by omega))⟩

/-- O5: every finite module over a regular local ring has finite projective dimension. -/
theorem exists_hasPDLT_of_isRegularLocalRing [IsRegularLocalRing R] (M : ModuleCat.{u} R)
    [Module.Finite R M] : ∃ n : ℕ, HasProjectiveDimensionLT M n :=
  exists_hasPDLT_of_spanFinrank _ R rfl M inferInstance

end RamanujanPetersson.JacDivisors


end

-- ===== S4.Def_RP_JacDivisors_C =====
section

/-!
# S4-JacDivisors C (O2 and helpers for Serre's hard direction)
* `coeff_mem_maximalIdeal_of_minimal`: relations among a minimal generating set have all
  coefficients in `m`.
* `free_of_depth_zero` (O2): if `s ≠ 0` kills `m`, every finite module of finite projective dimension
  is free; `maximalIdeal_eq_bot_of_depth_zero`: then `pd k < ∞` forces `m = 0`.
* `exists_nonZeroDivisor_not_mem_sq`: prime avoidance over the associated primes and `m²`.
* `spanFinrank_maximalIdeal_le_quotient_add_one`: lifting generators from `R ⧸ (x)`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open CategoryTheory IsLocalRing Ideal

universe u

variable {R : Type u} [CommRing R]

theorem coeff_mem_maximalIdeal_of_minimal [IsLocalRing R] {M : Type u} [AddCommGroup M]
    [Module R M] (t : Finset M) (ht : Submodule.span R (t : Set M) = ⊤)
    (hmin : ∀ t' : Finset M, Submodule.span R (t' : Set M) = ⊤ → t.card ≤ t'.card)
    (c : t →₀ R) (hc : Finsupp.linearCombination R (Subtype.val : t → M) c = 0) (i : t) :
    c i ∈ maximalIdeal R := by
  classical
  by_contra hi
  have hu : IsUnit (c i) := by simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hi
  set N := Submodule.span R ((t.erase i : Finset M) : Set M)
  have h1 : Finsupp.linearCombination R (Subtype.val : t → M) (c.erase i) ∈ N := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    have hji : j ≠ i := by
      rintro rfl
      simp at hj
    exact Finset.mem_erase.mpr ⟨fun h => hji (Subtype.ext h), j.2⟩
  have h2 : c i • (i : M) ∈ N := by
    have hsplit : c = c.erase i + Finsupp.single i (c i) := (Finsupp.erase_add_single i c).symm
    rw [hsplit, map_add, Finsupp.linearCombination_single] at hc
    rw [eq_neg_of_add_eq_zero_right hc]
    exact N.neg_mem h1
  have h3 : (i : M) ∈ N := (Submodule.smul_mem_iff_of_isUnit N hu).mp h2
  have h4 : N = ⊤ := by
    rw [eq_top_iff, ← ht, Submodule.span_le]
    intro y hy
    by_cases hyi : y = i
    · rw [hyi]; exact h3
    · exact Submodule.subset_span (Finset.mem_erase.mpr ⟨hyi, hy⟩)
  have h5 := hmin _ h4
  rw [Finset.card_erase_of_mem i.2] at h5
  have : 0 < t.card := Finset.card_pos.mpr ⟨i, i.2⟩
  omega

/-- Prime avoidance: a nonzerodivisor in `m \ m²`, unless `m` consists of zero divisors. -/
theorem exists_nonZeroDivisor_not_mem_sq [IsLocalRing R] [IsNoetherianRing R]
    (hm : ¬ maximalIdeal R ≤ maximalIdeal R ^ 2)
    (hd : ¬ Disjoint (maximalIdeal R : Set R) (nonZeroDivisors R)) :
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ x ∈ nonZeroDivisors R := by
  by_contra hcon
  push Not at hcon
  have hsub : (maximalIdeal R : Set R) ⊆
      ⋃ i ∈ insert (maximalIdeal R ^ 2) (associatedPrimes R R), id i := by
    intro y hy
    by_cases hy2 : y ∈ maximalIdeal R ^ 2
    · exact Set.mem_biUnion (Set.mem_insert _ _) hy2
    · have : y ∈ ⋃ p ∈ associatedPrimes R R, (p : Set R) := by
        rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors]; exact hcon y hy hy2
      obtain ⟨P, hP, hyP⟩ := Set.mem_iUnion₂.mp this
      exact Set.mem_biUnion (Set.mem_insert_of_mem _ hP) hyP
  obtain ⟨P, hP, hle⟩ := (Ideal.subset_union_prime_finite ((associatedPrimes.finite R R).insert _)
    (f := id) (maximalIdeal R ^ 2) (maximalIdeal R ^ 2)
    (fun P hP h1 _ => ((Set.mem_insert_iff.mp hP).resolve_left h1).1)).mp hsub
  rcases Set.mem_insert_iff.mp hP with rfl | hP
  · exact hm hle
  · apply hd
    rw [Set.disjoint_left]
    intro a ha hnz
    have : a ∈ ⋃ p ∈ associatedPrimes R R, (p : Set R) := Set.mem_biUnion hP (hle ha)
    rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors] at this
    exact this hnz

end RamanujanPetersson.JacDivisors


end


