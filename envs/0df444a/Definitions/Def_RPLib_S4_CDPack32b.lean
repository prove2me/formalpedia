-- Prove2me | Definitions.Def_RPLib_S4_CDPack32b
-- name    : RPLib_S4_CDPack32b
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T09:30:14.077179+00:00
-- url     : https://prove2.me/theorems/af8855f0-ce33-42fb-96fb-09e5fb97629f
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 32b of 71
-- statement:
--   Part 32b of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacFrob_BrO`: S4-JacFrob, part BrO (bridge 3): `F-bar / F_{lev j}` is unramified
--   * `Def_RP_JacFrob_BrD`: S4-JacFrob, part BrD (bridge 4): degree-1 places, separation, fibre count
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack32

/-!
# Curve-duality library package, part 32b of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacFrob_BrO`: S4-JacFrob, part BrO (bridge 3): `F-bar / F_{lev j}` is unramified
* `Def_RP_JacFrob_BrD`: S4-JacFrob, part BrD (bridge 4): degree-1 places, separation, fibre count
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

theorem ord_liesOver_mul (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]
    (x : K) : Places.ord w (algebraMap K L x) = (v.asIdeal.ramificationIdx' w.asIdeal : ℤ) * Places.ord v x := by
  simp only [Places.ord]
  rw [← HeightOneSpectrum.valuation_liesOver L v w x, WithZero.log_pow, nsmul_eq_mul, mul_neg]

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

theorem ord_contFinB_mul (j : ℕ) (w : HeightOneSpectrum (Rfin (kbar Fq Ω) (Fbar Fq F Ω))) (f : Fc Fq F Ω (lev j)) :
    letI := (finR Fq F Ω j).toAlgebra
    Places.ord w (incF Fq F Ω j f) =
      ((contFinB Fq F Ω hk j w).asIdeal.ramificationIdx' w.asIdeal : ℤ) * Places.ord (contFinB Fq F Ω hk j w) f := by
  letI := (finR Fq F Ω j).toAlgebra
  letI : Module (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rfin (kbar Fq Ω) (Fbar Fq F Ω)) := Algebra.toModule
  haveI := isIntegral_finR Fq F Ω hk j
  haveI : Module.IsTorsionFree (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rfin (kbar Fq Ω) (Fbar Fq F Ω)) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (by
      rw [RingHom.algebraMap_toAlgebra]; exact finR_injective Fq F Ω j)
  letI : Algebra (Fc Fq F Ω (lev j)) (Fbar Fq F Ω) := (incF Fq F Ω j).toAlgebra
  letI : Algebra (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Fbar Fq F Ω) :=
    ((incF Fq F Ω j).comp (algebraMap (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Fc Fq F Ω (lev j)))).toAlgebra
  letI : SMul (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rfin (kbar Fq Ω) (Fbar Fq F Ω)) := Algebra.toSMul
  letI : SMul (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Fbar Fq F Ω) := Algebra.toSMul
  letI : SMul (Fc Fq F Ω (lev j)) (Fbar Fq F Ω) := Algebra.toSMul
  letI : SMul (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Fc Fq F Ω (lev j)) := Algebra.toSMul
  haveI : IsScalarTower (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Fc Fq F Ω (lev j)) (Fbar Fq F Ω) :=
    IsScalarTower.of_algebraMap_eq' (by rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra])
  haveI : IsScalarTower (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rfin (kbar Fq Ω) (Fbar Fq F Ω)) (Fbar Fq F Ω) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
      refine RingHom.ext fun a => ?_
      rw [RingHom.comp_apply, RingHom.comp_apply]
      exact (coe_finR Fq F Ω j a).symm)
  haveI : w.asIdeal.LiesOver (contFinB Fq F Ω hk j w).asIdeal :=
    ⟨by rw [asIdeal_contFinB, Ideal.under_def, RingHom.algebraMap_toAlgebra]⟩
  have h := ord_liesOver_mul (Fbar Fq F Ω) (contFinB Fq F Ω hk j w) w f
  rw [RingHom.algebraMap_toAlgebra] at h
  exact h

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

theorem placeOrd_inl_bar (w : HeightOneSpectrum (Rfin (kbar Fq Ω) (Fbar Fq F Ω))) (f : Fbar Fq F Ω) :
    Places.Place.ord (Sum.inl w : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)) f = Places.ord w f := rfl

theorem placeOrd_inr_bar (w : HeightOneSpectrum (Rinf (kbar Fq Ω) (Fbar Fq F Ω))) (f : Fbar Fq F Ω) :
    Places.Place.ord (Sum.inr w : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)) f = Places.ord w f := rfl

/-- **Unramified** (places): `ord_{contB j P} f = ord_P f` for `f ∈ F_{lev j}`. -/
theorem ord_contB (j : ℕ) (P : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)) (f : Fc Fq F Ω (lev j)) :
    (contB Fq F Ω hk j P).ord f = P.ord (incF Fq F Ω j f) := by
  rcases P with w | w
  · rw [contB_inl, Place.ord_inl, placeOrd_inl_bar, ord_contFinB]
  · rw [contB_inr, Place.ord_inr, placeOrd_inr_bar, ord_contInfB]

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

theorem exists_not_mem_of_ne {w1 w2 : HeightOneSpectrum A} (h : w1 ≠ w2) :
    ∃ z ∈ w1.asIdeal, z ∉ w2.asIdeal := by
  by_contra hc
  push_neg at hc
  exact h (HeightOneSpectrum.ext (w1.isMaximal.eq_of_le w2.isPrime.ne_top hc))

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

include hk in
/-- At all large levels, `P` is the only place of `F-bar` over its contraction. -/
theorem exists_fibreB_singleton (P : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)) :
    ∃ M0, ∀ M, M0 ≤ M → fibreB Fq F Ω hk M (contB Fq F Ω hk M P) = {P} := by
  obtain ⟨M0, h⟩ := degOne Fq F Ω hk P
  exact ⟨M0, fun M hM => Finset.eq_singleton_iff_unique_mem.2
    ⟨(mem_fibreB Fq F Ω hk _ _ _).2 rfl, fun P' hP' => uniqB Fq F Ω hk (h M hM) ((mem_fibreB Fq F Ω hk _ _ _).1 hP')⟩⟩

include hk in
/-- **Fibre count**: there are exactly `deg Q` places of `F-bar` over a level place `Q`. -/
theorem card_fibreB (j : ℕ) (Q : Places.Place (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) :
    (fibreB Fq F Ω hk j Q).card = Q.deg := by
  classical
  choose! M0 hM0 using fun P (_ : P ∈ fibreB Fq F Ω hk j Q) => degOne Fq F Ω hk P
  let M := max j ((fibreB Fq F Ω hk j Q).sup M0)
  haveI : Fact (lev j ∣ lev M) := ⟨lev_dvd_lev (le_max_left _ _)⟩
  have hdeg : ∀ P ∈ fibreB Fq F Ω hk j Q, (contB Fq F Ω hk M P).deg = 1 := fun P hP =>
    hM0 P hP M (le_trans (Finset.le_sup hP) (le_max_right _ _))
  have hdown : ∀ P, contB Fq F Ω hk M P ∈ fibre (isConstExt_pair Fq F Ω hk (n := lev j) (N := lev M)) Q ↔
      P ∈ fibreB Fq F Ω hk j Q := fun P => by
    rw [mem_fibre, mem_fibreB]
    exact Iff.of_eq (congrArg (· = Q) (contractNN_contB Fq F Ω hk (i := j) (j := M) P))
  have hbij : (fibreB Fq F Ω hk j Q).card =
      (fibre (isConstExt_pair Fq F Ω hk (n := lev j) (N := lev M)) Q).card := by
    refine Finset.card_bij (fun P _ => contB Fq F Ω hk M P) (fun P hP => (hdown P).2 hP)
      (fun P1 _ P2 hP2 he => uniqB Fq F Ω hk (hdeg P2 hP2) he) (fun Q' hQ' => ?_)
    obtain ⟨P, hP⟩ := exists_contB_eq Fq F Ω hk M Q'
    exact ⟨P, (hdown P).1 (by rw [hP]; exact hQ'), hP⟩
  have hall : ∀ Q' ∈ fibre (isConstExt_pair Fq F Ω hk (n := lev j) (N := lev M)) Q, Q'.deg = 1 := by
    intro Q' hQ'
    obtain ⟨P, rfl⟩ := exists_contB_eq Fq F Ω hk M Q'
    exact hdeg P ((hdown P).1 hQ')
  have hsum := sum_deg_fibre (isConstExt_pair Fq F Ω hk (n := lev j) (N := lev M)) Q
  rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_eq_mul, mul_one] at hsum
  rw [hbij, hsum]

end DegOne

end RamanujanPetersson.JacFrob

end


