-- Prove2me | Definitions.Def_RPLib_S3_SBUpper
-- name    : RPLib_S3_SBUpper
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:37:59.686204+00:00
-- url     : https://prove2.me/theorems/1e277097-868d-4adb-ad8f-e576c5ce96f9
-- title:
--   Weight-two Ramanujan-Petersson library: S3-ZetaSB, D1: the Galois-twist upper bound
-- statement:
--   S3-ZetaSB, D1: the Galois-twist upper bound.
--
--   For `F ⊆ E` with `E / K` Galois (`K = RatFunc Fq`) and `F` with full constant field `Fq`:
--   * `exists_lift_tower` (U1): Frobenius-fixed points of `R` lift to `S` for a tower `R0 → R → S` with `S` free of
--     finite rank over `R0`;
--   * `piInfR_mem`, `Cinf` (U2): every place over `x = ∞` contains `1/x`, so these places are finite in number;
--     `Cinf` is the sum of their degrees;
--   * `numPoints_le_fixed_add` (U3): `N_m(F) ≤ #{w : Rfin F → L, Frob^m-fixed} + Cinf`;
--   * `card_Hs_eq` (U4): `|Gal(E/F)| = ℓ0 · |Gal(E/F) ⊓ ker constRes|`;
--   * `sum_twisted_H_eq` (U5): `Σ_{h ∈ Gal(E/F)} N(h) = |Gal(E/F)| · #{w fixed}`;
--   * `upper_bound_core` (U6): `N_m(F) ≤ q ^ m + (2 g_E + 1) q ^ (m/2) + Cinf`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer 2009, Chapters 1 and 5; E. Bombieri, Counting points on curves over finite fields (d'après S. A. Stepanov), Séminaire Bourbaki 430 (1973); A. Weil, Sur les courbes algébriques et les variétés qui s'en déduisent, Hermann 1948

import Mathlib
import Definitions.Def_RPLib_S3_SBGalC

/-!
# S3-ZetaSB, D1: the Galois-twist upper bound

For `F ⊆ E` with `E / K` Galois (`K = RatFunc Fq`) and `F` with full constant field `Fq`:
* `exists_lift_tower` (U1): Frobenius-fixed points of `R` lift to `S` for a tower `R0 → R → S` with `S` free of
  finite rank over `R0`;
* `piInfR_mem`, `Cinf` (U2): every place over `x = ∞` contains `1/x`, so these places are finite in number;
  `Cinf` is the sum of their degrees;
* `numPoints_le_fixed_add` (U3): `N_m(F) ≤ #{w : Rfin F → L, Frob^m-fixed} + Cinf`;
* `card_Hs_eq` (U4): `|Gal(E/F)| = ℓ0 · |Gal(E/F) ⊓ ker constRes|`;
* `sum_twisted_H_eq` (U5): `Σ_{h ∈ Gal(E/F)} N(h) = |Gal(E/F)| · #{w fixed}`;
* `upper_bound_core` (U6): `N_m(F) ≤ q ^ m + (2 g_E + 1) q ^ (m/2) + Cinf`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial Module IsDedekindDomain

namespace RamanujanPetersson.ZetaSB

open RR

section Generic

variable {Fq : Type*} [Field Fq] [Fintype Fq]

/-- (U1) `exists_lift` over a tower `R0 → R → S` with `S` free of finite rank over `R0`. -/
theorem exists_lift_tower {R0 R S L : Type*} [CommRing R0] [Nontrivial R0] [CommRing R] [Nontrivial R] [CommRing S]
    [Algebra R0 R] [Algebra R0 S] [Algebra R S] [IsScalarTower R0 R S]
    [Algebra Fq R] [Algebra Fq S] [IsScalarTower Fq R S] [Algebra.IsIntegral R S]
    [Module.Free R0 S] [Module.Finite R0 S]
    (hinj : Function.Injective (algebraMap R S)) [Field L] [Algebra Fq L] [Finite L] (m : ℕ)
    (z : R →ₐ[Fq] L) (hz : ∀ r, z r ^ (Fintype.card Fq ^ m) = z r)
    (hL : m * (finrank R0 S).factorial ∣ finrank Fq L) :
    ∃ y : S →ₐ[Fq] L, y.comp (IsScalarTower.toAlgHom Fq R S) = z := by
  classical
  set p := RingHom.ker z with hp
  haveI : p.IsPrime := RingHom.ker_isPrime z
  let zb : R ⧸ p →ₐ[Fq] L := Ideal.kerLiftAlg z
  have zb_inj : Function.Injective zb := Ideal.kerLiftAlg_injective z
  haveI : Finite (R ⧸ p) := Finite.of_injective zb zb_inj
  haveI hpmax : p.IsMaximal := Ideal.Quotient.maximal_of_isField p (Finite.isField_of_domain _)
  have hle : RingHom.ker (algebraMap R S) ≤ p := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le
  obtain ⟨P, hPmax, hPp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral p hle
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI : Field (S ⧸ P) := Ideal.Quotient.field P
  have hle' : p ≤ P.comap (IsScalarTower.toAlgHom Fq R S) := hPp.ge
  let ι : R ⧸ p →ₐ[Fq] S ⧸ P := Ideal.quotientMapₐ P (IsScalarTower.toAlgHom Fq R S) hle'
  have hdeg1 : finrank Fq (R ⧸ p) ∣ m := by
    refine finrank_dvd_of_fixed zb m fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact hz a
  letI : Algebra (R ⧸ p) (S ⧸ P) := ι.toRingHom.toAlgebra
  haveI : IsScalarTower Fq (R ⧸ p) (S ⧸ P) := IsScalarTower.of_algebraMap_eq fun c => (ι.commutes c).symm
  have hspan := span_basis_quot_eq_top (R := R0) ((Ideal.Quotient.mk p).comp (algebraMap R0 R))
    (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective ι.toRingHom
    (fun r => by rw [IsScalarTower.algebraMap_apply R0 R S]; rfl)
  haveI : Module.Finite (R ⧸ p) (S ⧸ P) := by
    refine ⟨⟨Finset.univ.image fun i => Ideal.Quotient.mk P (Module.Free.chooseBasis R0 S i), ?_⟩⟩
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact hspan
  haveI : Module.Finite Fq (R ⧸ p) := Module.Finite.of_finite
  haveI : Module.Finite Fq (S ⧸ P) := Module.Finite.trans (R ⧸ p) (S ⧸ P)
  have hrel : finrank (R ⧸ p) (S ⧸ P) ≤ finrank R0 S := by
    rw [Module.finrank_eq_card_chooseBasisIndex R0 S]
    exact finrank_le_of_span_eq_top hspan
  have hdvd2 : finrank (R ⧸ p) (S ⧸ P) ∣ (finrank R0 S).factorial :=
    Nat.dvd_factorial Module.finrank_pos hrel
  have htow : finrank Fq (S ⧸ P) = finrank Fq (R ⧸ p) * finrank (R ⧸ p) (S ⧸ P) :=
    (Module.finrank_mul_finrank Fq (R ⧸ p) (S ⧸ P)).symm
  have hdvd : finrank Fq (S ⧸ P) ∣ finrank Fq L := by
    rw [htow]; exact (Nat.mul_dvd_mul hdeg1 hdvd2).trans hL
  obtain ⟨ψ, hψ⟩ := exists_algHom_comp_eq ι zb hdvd
  refine ⟨ψ.comp (Ideal.Quotient.mkₐ Fq P), AlgHom.ext fun r => ?_⟩
  have := congrArg (fun f : R ⧸ p →ₐ[Fq] L => f (Ideal.Quotient.mk p r)) hψ
  exact this

end Generic

section FF

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {E : Type*} [Field E] [Algebra Fq E] [Algebra Fq[X] E] [Algebra (RatFunc Fq) E]
  [IsScalarTower Fq[X] (RatFunc Fq) E] [IsScalarTower Fq Fq[X] E] [FunctionField Fq E]
  [Algebra.IsSeparable (RatFunc Fq) E]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

variable (Fq F) in
/-- The image of `1/x` in `Rinf F`. -/
noncomputable abbrev piInfR : Places.Rinf Fq F :=
  algebraMap (Places.Oinf Fq) (Places.Rinf Fq F) (Places.piInf Fq)

theorem piInfR_ne_zero : piInfR Fq F ≠ 0 := by
  rw [Ne, ← map_zero (algebraMap (Places.Oinf Fq) (Places.Rinf Fq F)),
    (Places.algebraMap_Oinf_Rinf_injective Fq F).eq_iff]
  exact Places.piInf_ne_zero Fq

/-- (U2) Every place over `x = ∞` contains `1/x`. -/
theorem piInfR_mem (P : HeightOneSpectrum (Places.Rinf Fq F)) : piInfR Fq F ∈ P.asIdeal := by
  haveI := P.isMaximal
  have h1 : (P.asIdeal.comap (algebraMap (Places.Oinf Fq) (Places.Rinf Fq F))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P.asIdeal
  have h2 := IsLocalRing.eq_maximalIdeal h1
  have h3 := IsLocalRing.eq_maximalIdeal (Places.span_piInf_isMaximal Fq)
  have h4 : Places.piInf Fq ∈ P.asIdeal.comap (algebraMap (Places.Oinf Fq) (Places.Rinf Fq F)) := by
    rw [h2, ← h3]; exact Ideal.mem_span_singleton_self _
  exact h4

variable (Fq F) in
theorem finite_infPlaces :
    {P : HeightOneSpectrum (Places.Rinf Fq F) | P.asIdeal ∣ Ideal.span {piInfR Fq F}}.Finite :=
  Ideal.finite_factors (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact piInfR_ne_zero)

variable (Fq F) in
/-- `C_∞`: the total degree of the places over `x = ∞`. -/
noncomputable def Cinf : ℕ := ∑ P ∈ (finite_infPlaces Fq F).toFinset, Places.deg Fq P

theorem mem_infPlaces (P : HeightOneSpectrum (Places.Rinf Fq F)) : P ∈ (finite_infPlaces Fq F).toFinset :=
  (Set.Finite.mem_toFinset _).mpr (Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr (piInfR_mem P)))

/-- (U3) `N_m(F) ≤ #{w : Rfin F → L, Frob^m-fixed} + C_∞` when `m ∣ [L : Fq]`. -/
theorem numPoints_le_fixed_add (p : ℕ) [Fact p.Prime] [CharP Fq p] (L : Type*) [Field L] [Algebra Fq L]
    [Finite L] [Fintype (Places.Rfin Fq F →ₐ[Fq] L)] [DecidableEq (Places.Rfin Fq F →ₐ[Fq] L)]
    {m : ℕ} (hm : m ≠ 0) (hL : m ∣ finrank Fq L) (φ : L →ₐ[Fq] L)
    (hφ : ∀ x, φ x = x ^ (Fintype.card Fq ^ m)) :
    Places.numPoints Fq F m ≤
      (Finset.univ.filter fun w : Places.Rfin Fq F →ₐ[Fq] L => φ.comp w = w).card + Cinf Fq F := by
  classical
  haveI : NeZero m := ⟨hm⟩
  let Lm := FiniteField.Extension Fq p m
  letI : Fintype Lm := Fintype.ofFinite Lm
  obtain ⟨χ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := Fq) (K := Lm) (L := L)
    (by rw [FiniteField.finrank_extension]; exact hL)
  have hcard : Fintype.card Lm = Fintype.card Fq ^ m := by
    rw [← Nat.card_eq_fintype_card, FiniteField.natCard_extension, Nat.card_eq_fintype_card]
  have h1 := Places.numPoints_eq_card_algHom Fq F Lm
  rw [FiniteField.finrank_extension] at h1
  rw [h1]
  refine Nat.add_le_add ?_ ?_
  · calc Nat.card (Places.Rfin Fq F →ₐ[Fq] Lm)
        ≤ Nat.card {w : Places.Rfin Fq F →ₐ[Fq] L // φ.comp w = w} := by
          refine Nat.card_le_card_of_injective (fun w => ⟨χ.comp w, AlgHom.ext fun a => ?_⟩) fun w w' h => ?_
          · rw [AlgHom.comp_apply, AlgHom.comp_apply, hφ, ← map_pow, ← hcard, FiniteField.pow_card]
          · exact AlgHom.ext fun a => (χ : Lm →+* L).injective
              (congrArg (fun u : {w : Places.Rfin Fq F →ₐ[Fq] L // φ.comp w = w} => u.1 a) h)
      _ = _ := by rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  · rw [Places.card_algHom_eq_sum Fq Lm (T := (finite_infPlaces Fq F).toFinset) (fun P _ => mem_infPlaces P)]
    unfold Cinf
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- (U4) If `F` has full constant field, `Gal(E/F)` maps onto `Aut(k'/Fq)`, so
`|Gal(E/F)| = ℓ0 · |Gal(E/F) ⊓ ker constRes|`. -/
theorem card_Hs_eq [IsGalois (RatFunc Fq) E] (hk : Places.constField Fq F = ⊥) (ι : F →ₐ[RatFunc Fq] E) :
    Nat.card ι.fieldRange.fixingSubgroup = finrank Fq (Places.constField Fq E) *
      Nat.card (ι.fieldRange.fixingSubgroup ⊓ (constRes Fq E).ker : Subgroup (E ≃ₐ[RatFunc Fq] E)) := by
  set Hs := ι.fieldRange.fixingSubgroup with hHs
  let ρ' := (constRes Fq E).comp Hs.subtype
  have h1 : Nat.card ρ'.ker * Nat.card ρ'.range = Nat.card Hs := by
    rw [← Subgroup.index_ker]; exact Subgroup.card_mul_index _
  have h3 : Nat.card ρ'.ker = Nat.card (Hs ⊓ (constRes Fq E).ker : Subgroup (E ≃ₐ[RatFunc Fq] E)) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, Subgroup.mem_inf.mpr ⟨x.1.2, MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp x.2)⟩⟩
        invFun := fun x => ⟨⟨x.1, (Subgroup.mem_inf.mp x.2).1⟩,
          MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp x.2).2)⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  have hfix : IntermediateField.fixedField ρ'.range = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [IntermediateField.mem_fixedField_iff] at hc
    have hfixc : ∀ h ∈ Hs, h (c : E) = c := fun h hh => by
      have := hc (ρ' ⟨h, hh⟩) ⟨⟨h, hh⟩, rfl⟩
      rw [← constRes_apply]
      exact congrArg Subtype.val this
    have hmem : (c : E) ∈ ι.fieldRange := by
      rw [← IsGalois.fixedField_fixingSubgroup ι.fieldRange]
      exact (IntermediateField.mem_fixedField_iff _ _).mpr hfixc
    obtain ⟨a, ha⟩ := ι.mem_fieldRange.mp hmem
    have hint : IsIntegral Fq a := by
      have h2 : IsIntegral Fq (c : E) := Places.isIntegral_of_mem_constField Fq E c
      rw [← ha] at h2
      exact (isIntegral_algHom_iff (ι.restrictScalars Fq) (ι : F →+* E).injective).mp h2
    have ha' : a ∈ Places.constField Fq F := hint
    rw [hk] at ha'
    obtain ⟨x, hx⟩ := IntermediateField.mem_bot.mp ha'
    rw [IntermediateField.mem_bot]
    refine ⟨x, Subtype.ext ?_⟩
    rw [← ha, ← hx]
    exact ((ι.restrictScalars Fq).commutes x).symm
  have hrange : Nat.card ρ'.range = finrank Fq (Places.constField Fq E) := by
    have h1 : finrank Fq (IntermediateField.fixedField ρ'.range) = 1 :=
      IntermediateField.finrank_eq_one_iff.mpr hfix
    rw [← IntermediateField.finrank_fixedField_eq_card, ← Module.finrank_mul_finrank Fq
      (IntermediateField.fixedField ρ'.range) (Places.constField Fq E), h1, one_mul]
  rw [← h1, h3, hrange, mul_comm]

variable (L : Type*) [Field L] [Algebra Fq L] [Finite L]

/-- (U5) `F`-side count, equality form: every Frobenius-fixed point of `Rfin F` lifts to `Rfin E`. -/
theorem sum_twisted_H_eq [IsGalois (RatFunc Fq) E] (ι : F →ₐ[RatFunc Fq] E)
    [Fintype (Places.Rfin Fq E →ₐ[Fq] L)] [DecidableEq (Places.Rfin Fq E →ₐ[Fq] L)]
    [Fintype (Places.Rfin Fq F →ₐ[Fq] L)] [DecidableEq (Places.Rfin Fq F →ₐ[Fq] L)]
    [Fintype (E ≃ₐ[RatFunc Fq] E)] [DecidablePred (· ∈ ι.fieldRange.fixingSubgroup)] (m : ℕ)
    (hL : m * (finrank Fq[X] (Places.Rfin Fq E)).factorial ∣ finrank Fq L)
    (φ : L →ₐ[Fq] L) (hφ : ∀ x, φ x = x ^ (Fintype.card Fq ^ m)) :
    ∑ g ∈ Finset.univ.filter (· ∈ ι.fieldRange.fixingSubgroup),
      (Finset.univ.filter fun y : Places.Rfin Fq E →ₐ[Fq] L => twist y g = φ.comp y).card =
    (Finset.univ.filter (· ∈ ι.fieldRange.fixingSubgroup)).card *
      (Finset.univ.filter fun w : Places.Rfin Fq F →ₐ[Fq] L => φ.comp w = w).card := by
  classical
  letI : Algebra (Places.Rfin Fq F) (Places.Rfin Fq E) := (finMap Fq ι).toRingHom.toAlgebra
  haveI : IsScalarTower Fq (Places.Rfin Fq F) (Places.Rfin Fq E) :=
    IsScalarTower.of_algebraMap_eq fun c => Subtype.ext (by
      change algebraMap Fq E c = ι (algebraMap Fq F c)
      exact ((ι.restrictScalars Fq).commutes c).symm)
  haveI : IsScalarTower Fq[X] (Places.Rfin Fq F) (Places.Rfin Fq E) :=
    IsScalarTower.of_algebraMap_eq fun r => ((finMap Fq ι).commutes r).symm
  haveI : Algebra.IsIntegral (Places.Rfin Fq F) (Places.Rfin Fq E) :=
    ⟨fun b => (Algebra.IsIntegral.isIntegral (R := Fq[X]) b).tower_top⟩
  have hinj : Function.Injective (algebraMap (Places.Rfin Fq F) (Places.Rfin Fq E)) :=
    fun a b h => Subtype.ext ((ι : F →+* E).injective (congrArg Subtype.val h))
  haveI : SMulCommClass ι.fieldRange.fixingSubgroup (Places.Rfin Fq F) (Places.Rfin Fq E) :=
    ⟨fun h a b => Subtype.ext (by
      change (h : E ≃ₐ[RatFunc Fq] E) (ι a * b) = ι a * (h : E ≃ₐ[RatFunc Fq] E) b
      rw [map_mul, (IntermediateField.mem_fixingSubgroup_iff _ _).mp h.2 _ (ι.mem_fieldRange.mpr ⟨a, rfl⟩)])⟩
  haveI : Algebra.IsInvariant (Places.Rfin Fq F) (Places.Rfin Fq E) ι.fieldRange.fixingSubgroup := ⟨fun b hb => by
    have hfix : ∀ h ∈ ι.fieldRange.fixingSubgroup, h (b : E) = b := fun h hh => congrArg Subtype.val (hb ⟨h, hh⟩)
    have hmem : (b : E) ∈ ι.fieldRange := by
      rw [← IsGalois.fixedField_fixingSubgroup ι.fieldRange]
      exact (IntermediateField.mem_fixedField_iff _ _).mpr hfix
    obtain ⟨a, ha⟩ := ι.mem_fieldRange.mp hmem
    have hint : IsIntegral Fq[X] a := by
      have hb2 : IsIntegral Fq[X] (b : E) := b.2
      rw [← ha] at hb2
      exact (isIntegral_algHom_iff (ι.restrictScalars Fq[X])
        (RingHom.injective (ι.restrictScalars Fq[X]).toRingHom)).mp hb2
    exact ⟨⟨a, hint⟩, Subtype.ext ha⟩⟩
  have hsum := sum_card_twisted_eq (G := ι.fieldRange.fixingSubgroup) (A := Places.Rfin Fq F)
    (B := Places.Rfin Fq E) φ
  have hconv : ∑ g ∈ Finset.univ.filter (· ∈ ι.fieldRange.fixingSubgroup),
      (Finset.univ.filter fun y : Places.Rfin Fq E →ₐ[Fq] L => twist y g = φ.comp y).card =
      ∑ h : ι.fieldRange.fixingSubgroup,
        (Finset.univ.filter fun y : Places.Rfin Fq E →ₐ[Fq] L => twist y h = φ.comp y).card :=
    Finset.sum_subtype _ (fun g => by simp) _
  rw [hconv, hsum]
  calc _ = ∑ z ∈ Finset.univ.filter (fun z : Places.Rfin Fq F →ₐ[Fq] L => φ.comp z = z),
        Fintype.card ι.fieldRange.fixingSubgroup := Finset.sum_congr rfl fun z hz => by
          rw [if_pos]
          rw [Finset.mem_filter] at hz
          have hz' : ∀ r, z r ^ (Fintype.card Fq ^ m) = z r := fun r => by
            rw [← hφ]
            exact congrArg (fun u : Places.Rfin Fq F →ₐ[Fq] L => u r) hz.2
          obtain ⟨y, hy⟩ := exists_lift_tower (R0 := Fq[X]) (R := Places.Rfin Fq F) (S := Places.Rfin Fq E)
            hinj m z hz' hL
          exact ⟨y, hy⟩
    _ = _ := by rw [Finset.sum_const, smul_eq_mul, mul_comm, Fintype.card_subtype]

/-- **Galois-twist upper bound (core).** For `F ⊆ E` with `E / K` Galois, `F` with full constant field,
`ℓ0 ∣ m`, `q ^ m = Q0 ^ 2` large and a place of `E` of degree `ℓ0`:
`N_m(F) ≤ q ^ m + (2 g_E + 1) q ^ (m/2) + C_∞`. -/
theorem upper_bound_core [IsGalois (RatFunc Fq) E] (hk : Places.constField Fq F = ⊥)
    (ι : F →ₐ[RatFunc Fq] E)
    (p : ℕ) [Fact p.Prime] [CharP E p] (k Q0 m : ℕ) (hm : m ≠ 0) (hQ0def : Q0 = p ^ k)
    (hq : Fintype.card Fq ^ m = Q0 ^ 2) (hℓ : finrank Fq (Places.constField Fq E) ∣ m)
    (hL : m * (finrank Fq[X] (Places.Rfin Fq E)).factorial ∣ finrank Fq L)
    (P0 : Places.Place Fq E) (hP0 : P0.deg = ellF Fq E 0)
    (hQ0 : (genusF Fq E + ellF Fq E 0) ^ 2 < ellF Fq E 0 ^ 2 * Q0) :
    Places.numPoints Fq F m ≤ Q0 ^ 2 + (2 * genusF Fq E + 1) * Q0 + Cinf Fq F := by
  classical
  haveI : CharP Fq p := (Algebra.charP_iff Fq E p).mpr inferInstance
  letI : Fintype (E ≃ₐ[RatFunc Fq] E) := Fintype.ofFinite _
  haveI : Finite (Places.Rfin Fq E →ₐ[Fq] L) :=
    finite_algHom_of_pow (fun N hN => Places.X_pow_ne_self Fq E hN) L
  letI : Fintype (Places.Rfin Fq E →ₐ[Fq] L) := Fintype.ofFinite _
  haveI : Finite (Places.Rfin Fq F →ₐ[Fq] L) :=
    finite_algHom_of_pow (fun N hN => Places.X_pow_ne_self Fq F hN) L
  letI : Fintype (Places.Rfin Fq F →ₐ[Fq] L) := Fintype.ofFinite _
  set φ : L →ₐ[Fq] L := FiniteField.frobeniusAlgHom Fq L ^ m with hφdef
  have hφ : ∀ x, φ x = x ^ (Fintype.card Fq ^ m) := frob_pow_apply L m
  have hφ' : ∀ x, φ x = x ^ (Q0 ^ 2) := fun x => by rw [hφ, hq]
  set Hs := ι.fieldRange.fixingSubgroup with hHs
  set U := ellF Fq E 0 * (Q0 ^ 2 + (2 * genusF Fq E + 1) * Q0) with hUdef
  set N : (E ≃ₐ[RatFunc Fq] E) → ℕ := fun g =>
    (Finset.univ.filter fun y : Places.Rfin Fq E →ₐ[Fq] L => twist y g = φ.comp y).card with hN
  have hU : ∀ g, N g ≤ U := fun g => card_twisted_le L g p k Q0 hQ0def φ hφ' P0 hP0 hQ0
  have h0 : ∀ g, ¬ (g ∈ (constRes Fq E).ker) → N g = 0 := by
    intro g hg
    by_contra hne
    obtain ⟨y, hy⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
    rw [Finset.mem_filter] at hy
    exact hg ((mem_ker_constRes g).mpr fun c => fix_const_of_twist L hℓ g φ hφ y hy.2 c)
  set b := (Finset.univ.filter fun g => g ∈ Hs ∧ g ∈ (constRes Fq E).ker).card with hb
  set W := (Finset.univ.filter fun w : Places.Rfin Fq F →ₐ[Fq] L => φ.comp w = w).card with hW
  have hsum : ∑ g ∈ Finset.univ.filter (· ∈ Hs), N g = (Finset.univ.filter (· ∈ Hs)).card * W :=
    sum_twisted_H_eq L ι m hL φ hφ
  have hle : ∑ g ∈ Finset.univ.filter (· ∈ Hs), N g ≤ b * U := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter (· ∈ Hs)) (· ∈ (constRes Fq E).ker),
      Finset.sum_eq_zero (fun g hg => h0 g (Finset.mem_filter.mp hg).2), add_zero, Finset.filter_filter]
    calc _ ≤ ∑ g ∈ Finset.univ.filter (fun g => g ∈ Hs ∧ g ∈ (constRes Fq E).ker), U :=
          Finset.sum_le_sum fun g _ => hU g
      _ = b * U := by rw [Finset.sum_const, smul_eq_mul]
  have hcardHs : (Finset.univ.filter (· ∈ Hs)).card = ellF Fq E 0 * b := by
    have h1 := card_Hs_eq hk ι
    rw [← RR.ellF_zero, Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_eq_fintype_card,
      Fintype.card_subtype] at h1
    rw [h1, hb]
    congr 2
    exact Finset.filter_congr fun g _ => Subgroup.mem_inf
  have hpos : 0 < (Finset.univ.filter (· ∈ Hs)).card := Finset.card_pos.mpr ⟨1, by simp [Hs.one_mem]⟩
  have hWU : W ≤ Q0 ^ 2 + (2 * genusF Fq E + 1) * Q0 := by
    have key : (ellF Fq E 0 * b) * W ≤ (ellF Fq E 0 * b) * (Q0 ^ 2 + (2 * genusF Fq E + 1) * Q0) := by
      calc (ellF Fq E 0 * b) * W = ∑ g ∈ Finset.univ.filter (· ∈ Hs), N g := by rw [hsum, hcardHs]
        _ ≤ b * U := hle
        _ = _ := by rw [hUdef]; ring
    rw [hcardHs] at hpos
    exact Nat.le_of_mul_le_mul_left key hpos
  have hdvd : m ∣ finrank Fq L := (Dvd.intro _ rfl).trans hL
  calc Places.numPoints Fq F m ≤ W + Cinf Fq F := numPoints_le_fixed_add p L hm hdvd φ hφ
    _ ≤ _ := Nat.add_le_add_right hWU _

end FF

end RamanujanPetersson.ZetaSB


