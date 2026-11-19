-- Prove2me | Definitions.Def_RPLib_F2_002
-- name    : RPLib_F2_002
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T02:57:36.397594+00:00
-- url     : https://prove2.me/theorems/d994def8-9908-40a2-88b2-66af8e1cb2e2
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 002 of 70
-- statement:
--   File 002 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S3.SB_GalC`: S3-ZetaSB, E2b part C: the Galois-twist lower bound for a Galois function field
--   * `S3.SB_Upper`: S3-ZetaSB, D1: the Galois-twist upper bound
--   * `S3.Zeta_A`: S3-ZetaSB, O5 part A: effective divisors and the Newton identity
--   * `S3.SB_ClosA`: S3-ZetaSB, E1 part A: a Galois closure of `F / K` with an arbitrary constant extension
--   * `S3.SB_ClosB`: S3-ZetaSB, E1 part B: a place of `GalE Fq F n` of degree `ℓ(0)`
--   * `S3.HasseWeil_A`: S3-ZetaSB, O6b part A: the two-sided bound along a progression
--   * `S3.Zeta_B`: S3-ZetaSB, O5 part B: the index `δ`, divisor classes and the counting formula for `A_n`
--   * `S3.Zeta_C`: S3-ZetaSB, O5 part C: the power-series argument
--   * `S3.HasseWeil_B`: S3-ZetaSB, O6b part B: `δ = 1`, `|α_i| ≤ √q` and the Hasse-Weil bound
--   * `S4.Def_RP_PicDescent_A`: S4-PicDescent, part A: the divisor class group, `Pic⁰`, and the class number `h = L(1)`
--   * `S4.Def_RP_PicDescent_B1`: S4-PicDescent, part B1: coordinates for the constant field extension `L(x) / Fq(x)`
--   * `S4.Def_RP_PicDescent_B2`: S4-PicDescent, part B2: a generic constant field extension in coordinates
--   * `S4.Def_RP_PicDescent_B3`: S4-PicDescent, part B3: the generic constant field extension is an `RR.IsConstExt`
--   * `S4.Def_RP_PicDescent_B4`: S4-PicDescent, part B4a: the finite fields `L_n` inside an ambient field
--   * `S4.Def_RP_PicDescent_C1`: S4-PicDescent, part C1: the rings of a constant field extension are tensor products
--   * `S4.Def_RP_PicDescent_D1`: S4-PicDescent, part D1: the Galois action of `Gal(L/Fq)` on a constant field extension
--   * `S4.Def_RP_CurveCoh_Pair`: S4-CurveCoh, part 1: cohomology of a pair `(Γ, {I_s})` in the `π₁` model (generic algebra)
--   * `S4.Def_RP_GalCover`: S4-GalCover draft v1: Galois etale covers and Frobenius (S4_DESIGN section 1)
--   * `S4.Def_RP_CurveCoh_Curve`: S4-CurveCoh, part 7: the curve instance
--   * `S4.Def_RP_Kummer_Gal`: S4-Kummer, part 1: Kummer characters for a subgroup of a Galois group (generic field theory)
--   * `S4.Def_RP_Kummer_H1`: S4-Kummer, part 2: `H¹(Γ, ZMod N)` is the Kummer group, with the Frobenius action
--   * `S4.Def_RP_Kummer_Const`: S4-Kummer, part 3: constants are unramified; `μ_N ⊆ K_U`; the curve form of Kummer theory
--   * `S4.Def_RP_Kummer_UnrCore`: S4-Kummer, part K4a (core): an inertia element fixes an `N`-th root of an `N`-th-power ideal class
--   * `S4.Def_RP_Kummer_Unr`: S4-Kummer, part K4a (assembly): Kummer roots of `N`-th-power ideal classes are unramified
--   * `S4.Def_RP_Tsen_Zero`: S4-PD (1), T1: common zeros over an algebraically closed field; the strong `C₁` property
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_001

/-!
# Ramanujan-Petersson curve library (flat edition), file 002 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S3.SB_GalC`: S3-ZetaSB, E2b part C: the Galois-twist lower bound for a Galois function field
* `S3.SB_Upper`: S3-ZetaSB, D1: the Galois-twist upper bound
* `S3.Zeta_A`: S3-ZetaSB, O5 part A: effective divisors and the Newton identity
* `S3.SB_ClosA`: S3-ZetaSB, E1 part A: a Galois closure of `F / K` with an arbitrary constant extension
* `S3.SB_ClosB`: S3-ZetaSB, E1 part B: a place of `GalE Fq F n` of degree `ℓ(0)`
* `S3.HasseWeil_A`: S3-ZetaSB, O6b part A: the two-sided bound along a progression
* `S3.Zeta_B`: S3-ZetaSB, O5 part B: the index `δ`, divisor classes and the counting formula for `A_n`
* `S3.Zeta_C`: S3-ZetaSB, O5 part C: the power-series argument
* `S3.HasseWeil_B`: S3-ZetaSB, O6b part B: `δ = 1`, `|α_i| ≤ √q` and the Hasse-Weil bound
* `S4.Def_RP_PicDescent_A`: S4-PicDescent, part A: the divisor class group, `Pic⁰`, and the class number `h = L(1)`
* `S4.Def_RP_PicDescent_B1`: S4-PicDescent, part B1: coordinates for the constant field extension `L(x) / Fq(x)`
* `S4.Def_RP_PicDescent_B2`: S4-PicDescent, part B2: a generic constant field extension in coordinates
* `S4.Def_RP_PicDescent_B3`: S4-PicDescent, part B3: the generic constant field extension is an `RR.IsConstExt`
* `S4.Def_RP_PicDescent_B4`: S4-PicDescent, part B4a: the finite fields `L_n` inside an ambient field
* `S4.Def_RP_PicDescent_C1`: S4-PicDescent, part C1: the rings of a constant field extension are tensor products
* `S4.Def_RP_PicDescent_D1`: S4-PicDescent, part D1: the Galois action of `Gal(L/Fq)` on a constant field extension
* `S4.Def_RP_CurveCoh_Pair`: S4-CurveCoh, part 1: cohomology of a pair `(Γ, {I_s})` in the `π₁` model (generic algebra)
* `S4.Def_RP_GalCover`: S4-GalCover draft v1: Galois etale covers and Frobenius (S4_DESIGN section 1)
* `S4.Def_RP_CurveCoh_Curve`: S4-CurveCoh, part 7: the curve instance
* `S4.Def_RP_Kummer_Gal`: S4-Kummer, part 1: Kummer characters for a subgroup of a Galois group (generic field theory)
* `S4.Def_RP_Kummer_H1`: S4-Kummer, part 2: `H¹(Γ, ZMod N)` is the Kummer group, with the Frobenius action
* `S4.Def_RP_Kummer_Const`: S4-Kummer, part 3: constants are unramified; `μ_N ⊆ K_U`; the curve form of Kummer theory
* `S4.Def_RP_Kummer_UnrCore`: S4-Kummer, part K4a (core): an inertia element fixes an `N`-th root of an `N`-th-power ideal class
* `S4.Def_RP_Kummer_Unr`: S4-Kummer, part K4a (assembly): Kummer roots of `N`-th-power ideal classes are unramified
* `S4.Def_RP_Tsen_Zero`: S4-PD (1), T1: common zeros over an algebraically closed field; the strong `C₁` property
-/

set_option autoImplicit false

-- ===== S3.SB_GalC =====
section

/-!
# S3-ZetaSB, E2b part C: the Galois-twist lower bound for a Galois function field

For `F ⊆ E` with `E / K` Galois (`K = RatFunc Fq`, group `G`, `Hs = Gal(E/F)` as the fixing subgroup of `ι F`):
* `constRes : G →* Aut(k'/Fq)` (restriction to the constant field `k'` of `E`) has range of size `ℓ0 = [k' : Fq]`
  (`card_gal_eq : |G| = ℓ0 |ker|`), and `|Hs| ≤ ℓ0 |Hs ⊓ ker|`;
* the `F`-side count `Σ_{h ∈ Hs} N(h) ≤ |Hs| · N_m(F)` and the `K`-side count `|G| q ^ m ≤ Σ_{g ∈ G} N(g)`;
* `lower_bound_core`: `q ^ m ≤ N_m(F) + |G| (2 g_E + 1) q ^ (m/2)` when `q ^ m = Q0 ^ 2` is large and `E` has a
  place of degree `ℓ0`.
-/

set_option autoImplicit false

open Polynomial Module IsDedekindDomain

namespace RamanujanPetersson.ZetaSB

open RR

/-- The counting inequality behind the lower bound (pure bookkeeping). -/
theorem count_assembly {G : Type*} [Fintype G] (N : G → ℕ) (pH p0 : G → Prop) [DecidablePred pH]
    [DecidablePred p0] (ℓ0 Q c NF : ℕ) (hU : ∀ g, N g ≤ ℓ0 * (Q + c)) (h0 : ∀ g, ¬ p0 g → N g = 0)
    (hG : Fintype.card G * Q ≤ ∑ g, N g)
    (hH : ∑ g ∈ Finset.univ.filter pH, N g ≤ (Finset.univ.filter pH).card * NF)
    (hG0 : Fintype.card G = ℓ0 * (Finset.univ.filter p0).card)
    (hH0 : (Finset.univ.filter pH).card ≤ ℓ0 * (Finset.univ.filter fun g => pH g ∧ p0 g).card) :
    (Finset.univ.filter pH).card * Q ≤ (Finset.univ.filter pH).card * NF + Fintype.card G * c := by
  classical
  have hab : (Finset.univ.filter p0).card = (Finset.univ.filter fun g => pH g ∧ p0 g).card +
      (Finset.univ.filter fun g => p0 g ∧ ¬ pH g).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter p0) pH, Finset.filter_filter,
      Finset.filter_filter]
    have e : (Finset.univ.filter fun g => p0 g ∧ pH g) = Finset.univ.filter fun g => pH g ∧ p0 g :=
      Finset.filter_congr fun g _ => and_comm
    rw [e]
  have key : ∀ g, N g ≤ (if pH g then N g else 0) + (if p0 g ∧ ¬ pH g then ℓ0 * (Q + c) else 0) := by
    intro g
    by_cases h1 : pH g
    · simp [h1]
    · by_cases h2 : p0 g
      · simp [h1, h2, hU g]
      · simp [h1, h2, h0 g h2]
  have hsum : ∑ g, N g ≤ ∑ g ∈ Finset.univ.filter pH, N g +
      (Finset.univ.filter fun g => p0 g ∧ ¬ pH g).card * (ℓ0 * (Q + c)) := by
    calc ∑ g, N g ≤ ∑ g, ((if pH g then N g else 0) + (if p0 g ∧ ¬ pH g then ℓ0 * (Q + c) else 0)) :=
          Finset.sum_le_sum fun g _ => key g
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  rw [hG0, hab] at hG ⊢
  generalize (Finset.univ.filter pH).card = H at *
  generalize (Finset.univ.filter fun g => pH g ∧ p0 g).card = b at *
  generalize (Finset.univ.filter fun g => p0 g ∧ ¬ pH g).card = a at *
  generalize (∑ g ∈ Finset.univ.filter pH, N g) = SH at *
  generalize (∑ g, N g) = S at *
  nlinarith [Nat.mul_le_mul_right Q hH0, Nat.zero_le (ℓ0 * b * c)]

section FF

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {E : Type*} [Field E] [Algebra Fq E] [Algebra Fq[X] E] [Algebra (RatFunc Fq) E]
  [IsScalarTower Fq[X] (RatFunc Fq) E] [IsScalarTower Fq Fq[X] E] [FunctionField Fq E]
  [Algebra.IsSeparable (RatFunc Fq) E]

theorem fixedField_range_constRes [IsGalois (RatFunc Fq) E] :
    IntermediateField.fixedField (constRes Fq E).range = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [IntermediateField.mem_fixedField_iff] at hc
  have hfix : ∀ g : E ≃ₐ[RatFunc Fq] E, g (c : E) = c := fun g => by
    have := hc (constRes Fq E g) ⟨g, rfl⟩
    rw [← constRes_apply, this]
  have hmem : (c : E) ∈ (⊥ : IntermediateField (RatFunc Fq) E) := by
    rw [← IsGalois.fixedField_fixingSubgroup (⊥ : IntermediateField (RatFunc Fq) E)]
    exact fun g => hfix g
  obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp hmem
  have hint : IsIntegral Fq r := by
    have h2 : IsIntegral Fq (c : E) := Places.isIntegral_of_mem_constField Fq E c
    rw [← hr] at h2
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom Fq (RatFunc Fq) E)
      (algebraMap (RatFunc Fq) E).injective).mp h2
  obtain ⟨a, ha⟩ := ratFunc_eq_of_isIntegral hint
  rw [IntermediateField.mem_bot]
  refine ⟨a, Subtype.ext ?_⟩
  rw [← hr, ← ha, ← IsScalarTower.algebraMap_apply Fq (RatFunc Fq) E]
  rfl

theorem card_range_constRes [IsGalois (RatFunc Fq) E] :
    Nat.card (constRes Fq E).range = finrank Fq (Places.constField Fq E) := by
  have h1 : finrank Fq (IntermediateField.fixedField (constRes Fq E).range) = 1 :=
    IntermediateField.finrank_eq_one_iff.mpr fixedField_range_constRes
  rw [← IntermediateField.finrank_fixedField_eq_card, ← Module.finrank_mul_finrank Fq
    (IntermediateField.fixedField (constRes Fq E).range) (Places.constField Fq E), h1, one_mul]

/-- `|G| = ℓ0 · |ker constRes|`. -/
theorem card_gal_eq [IsGalois (RatFunc Fq) E] :
    Nat.card (E ≃ₐ[RatFunc Fq] E) = finrank Fq (Places.constField Fq E) * Nat.card (constRes Fq E).ker := by
  rw [← Subgroup.card_mul_index (constRes Fq E).ker, Subgroup.index_ker, card_range_constRes, mul_comm]

variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

variable (L : Type*) [Field L] [Algebra Fq L] [Finite L]

/-- `F`-side count: `Σ_{h ∈ Gal(E/F)} N(h) ≤ |Gal(E/F)| · #{w : Rfin F → L, Frob-fixed}`. -/
theorem sum_twisted_H_le [IsGalois (RatFunc Fq) E] (ι : F →ₐ[RatFunc Fq] E)
    [Fintype (Places.Rfin Fq E →ₐ[Fq] L)] [DecidableEq (Places.Rfin Fq E →ₐ[Fq] L)]
    [Fintype (Places.Rfin Fq F →ₐ[Fq] L)] [DecidableEq (Places.Rfin Fq F →ₐ[Fq] L)]
    [Fintype (E ≃ₐ[RatFunc Fq] E)] [DecidablePred (· ∈ ι.fieldRange.fixingSubgroup)] (φ : L →ₐ[Fq] L) :
    ∑ g ∈ Finset.univ.filter (· ∈ ι.fieldRange.fixingSubgroup),
      (Finset.univ.filter fun y : Places.Rfin Fq E →ₐ[Fq] L => twist y g = φ.comp y).card ≤
    (Finset.univ.filter (· ∈ ι.fieldRange.fixingSubgroup)).card *
      (Finset.univ.filter fun w : Places.Rfin Fq F →ₐ[Fq] L => φ.comp w = w).card := by
  classical
  letI : Algebra (Places.Rfin Fq F) (Places.Rfin Fq E) := (finMap Fq ι).toRingHom.toAlgebra
  haveI : IsScalarTower Fq (Places.Rfin Fq F) (Places.Rfin Fq E) :=
    IsScalarTower.of_algebraMap_eq fun c => Subtype.ext (by
      change algebraMap Fq E c = ι (algebraMap Fq F c)
      exact ((ι.restrictScalars Fq).commutes c).symm)
  haveI : SMulCommClass ι.fieldRange.fixingSubgroup (Places.Rfin Fq F) (Places.Rfin Fq E) := ⟨fun h a b => Subtype.ext (by
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
  have hsum := sum_card_twisted_eq (G := ι.fieldRange.fixingSubgroup) (A := Places.Rfin Fq F) (B := Places.Rfin Fq E) φ
  have hconv : ∑ g ∈ Finset.univ.filter (· ∈ ι.fieldRange.fixingSubgroup),
      (Finset.univ.filter fun y : Places.Rfin Fq E →ₐ[Fq] L => twist y g = φ.comp y).card =
      ∑ h : ι.fieldRange.fixingSubgroup, (Finset.univ.filter fun y : Places.Rfin Fq E →ₐ[Fq] L => twist y h = φ.comp y).card :=
    Finset.sum_subtype _ (fun g => by simp) _
  rw [hconv, hsum]
  calc _ ≤ ∑ z ∈ Finset.univ.filter (fun z : Places.Rfin Fq F →ₐ[Fq] L => φ.comp z = z), Fintype.card ι.fieldRange.fixingSubgroup :=
        Finset.sum_le_sum fun z _ => by split_ifs <;> simp
    _ = _ := by rw [Finset.sum_const, smul_eq_mul, mul_comm, Fintype.card_subtype]

/-- Frobenius-fixed points of `Rfin F` number at most `N_m(F)`. -/
theorem card_fixed_le_numPoints [Fintype (Places.Rfin Fq F →ₐ[Fq] L)] [DecidableEq (Places.Rfin Fq F →ₐ[Fq] L)]
    {m : ℕ} (hm : m ≠ 0) (φ : L →ₐ[Fq] L) (hφ : ∀ x, φ x = x ^ (Fintype.card Fq ^ m)) :
    (Finset.univ.filter fun w : Places.Rfin Fq F →ₐ[Fq] L => φ.comp w = w).card ≤ Places.numPoints Fq F m := by
  classical
  set s := Finset.univ.filter fun w : Places.Rfin Fq F →ₐ[Fq] L => φ.comp w = w with hs
  have hdeg : ∀ w ∈ s, Places.deg Fq (Places.kerPlace Fq L w) ∣ m := fun w hw => by
    rw [hs, Finset.mem_filter] at hw
    refine deg_kerPlace_dvd L m w fun a => ?_
    rw [← hφ]
    exact congrArg (fun u : Places.Rfin Fq F →ₐ[Fq] L => u a) hw.2
  rw [Finset.card_eq_sum_card_image (Places.kerPlace Fq L)]
  calc ∑ P ∈ s.image (Places.kerPlace Fq L), (s.filter fun w => Places.kerPlace Fq L w = P).card
      ≤ ∑ P ∈ s.image (Places.kerPlace Fq L), Places.deg Fq P := Finset.sum_le_sum fun P _ => by
        calc _ ≤ (Finset.univ.filter fun y : Places.Rfin Fq F →ₐ[Fq] L => Places.kerPlace Fq L y = P).card :=
              Finset.card_le_card fun y hy => by
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢; exact hy.2
          _ = Nat.card {y : Places.Rfin Fq F →ₐ[Fq] L // Places.kerPlace Fq L y = P} := by
              rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
          _ ≤ Places.deg Fq P := by rw [Places.card_fiber]; split_ifs <;> simp
    _ = ∑ P ∈ ((s.image (Places.kerPlace Fq L)).map Function.Embedding.inl : Finset (Places.Place Fq F)),
          Places.Place.deg P := by
        rw [Finset.sum_map]; rfl
    _ ≤ ∑ P ∈ (Places.finite_place_deg_dvd Fq F hm).toFinset, Places.Place.deg P := by
        refine Finset.sum_le_sum_of_subset fun P hP => ?_
        rw [Finset.mem_map] at hP
        obtain ⟨P', hP', rfl⟩ := hP
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hP'
        rw [Set.Finite.mem_toFinset]
        exact hdeg w hw
    _ = Places.numPoints Fq F m := by rw [Places.numPoints, dif_neg hm]

/-- `K`-side count: every Frobenius-fixed point of `Fq[X]` lifts to `Rfin E`, so `|G| q ^ m ≤ Σ_g N(g)`. -/
theorem card_gal_mul_le_sum [IsGalois (RatFunc Fq) E]
    [Fintype (Places.Rfin Fq E →ₐ[Fq] L)] [DecidableEq (Places.Rfin Fq E →ₐ[Fq] L)]
    [Fintype (E ≃ₐ[RatFunc Fq] E)] (p : ℕ) [Fact p.Prime] [CharP Fq p] (m : ℕ) (hm : m ≠ 0)
    (hL : m * (finrank Fq[X] (Places.Rfin Fq E)).factorial ∣ finrank Fq L)
    (φ : L →ₐ[Fq] L) (hφ : ∀ x, φ x = x ^ (Fintype.card Fq ^ m)) :
    Fintype.card (E ≃ₐ[RatFunc Fq] E) * Fintype.card Fq ^ m ≤
      ∑ g : E ≃ₐ[RatFunc Fq] E,
        (Finset.univ.filter fun y : Places.Rfin Fq E →ₐ[Fq] L => twist y g = φ.comp y).card := by
  classical
  haveI := isInvariant_poly (Fq := Fq) (E := E)
  haveI : Finite (Fq[X] →ₐ[Fq] L) :=
    Finite.of_injective (fun z : Fq[X] →ₐ[Fq] L => z X) fun z z' h => Polynomial.algHom_ext h
  letI : Fintype (Fq[X] →ₐ[Fq] L) := Fintype.ofFinite _
  rw [sum_card_twisted_eq (A := Fq[X]) φ]
  have hdvd : m ∣ finrank Fq L := (Dvd.intro _ rfl).trans hL
  calc Fintype.card (E ≃ₐ[RatFunc Fq] E) * Fintype.card Fq ^ m
      ≤ Fintype.card (E ≃ₐ[RatFunc Fq] E) * (Finset.univ.filter fun z : Fq[X] →ₐ[Fq] L => φ.comp z = z).card :=
        Nat.mul_le_mul_left _ (card_fixed_poly_ge p m hm hdvd φ hφ)
    _ = ∑ z ∈ Finset.univ.filter (fun z : Fq[X] →ₐ[Fq] L => φ.comp z = z), Fintype.card (E ≃ₐ[RatFunc Fq] E) := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ = _ := Finset.sum_congr rfl fun z hz => by
        rw [if_pos]
        rw [Finset.mem_filter] at hz
        have hz' : ∀ r, z r ^ (Fintype.card Fq ^ m) = z r := fun r => by
          rw [← hφ]
          exact congrArg (fun u : Fq[X] →ₐ[Fq] L => u r) hz.2
        obtain ⟨y, hy⟩ := exists_lift (R := Fq[X]) (S := Places.Rfin Fq E)
          (FunctionField.ringOfIntegers.algebraMap_injective Fq E) m z hz' hL
        exact ⟨y, hy⟩

/-- **Galois-twist lower bound (core).** For `F ⊆ E` with `E / K` Galois, `ℓ0 ∣ m`, `q ^ m = Q0 ^ 2` large and
a place of `E` of degree `ℓ0`: `q ^ m ≤ N_m(F) + |G| (2 g_E + 1) q ^ (m/2)`. -/
theorem lower_bound_core [IsGalois (RatFunc Fq) E] (ι : F →ₐ[RatFunc Fq] E)
    (p : ℕ) [Fact p.Prime] [CharP E p] (k Q0 m : ℕ) (hm : m ≠ 0) (hQ0def : Q0 = p ^ k)
    (hq : Fintype.card Fq ^ m = Q0 ^ 2) (hℓ : finrank Fq (Places.constField Fq E) ∣ m)
    (hL : m * (finrank Fq[X] (Places.Rfin Fq E)).factorial ∣ finrank Fq L)
    (P0 : Places.Place Fq E) (hP0 : P0.deg = ellF Fq E 0)
    (hQ0 : (genusF Fq E + ellF Fq E 0) ^ 2 < ellF Fq E 0 ^ 2 * Q0) :
    Q0 ^ 2 ≤ Places.numPoints Fq F m + Nat.card (E ≃ₐ[RatFunc Fq] E) * ((2 * genusF Fq E + 1) * Q0) := by
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
  set N : (E ≃ₐ[RatFunc Fq] E) → ℕ := fun g =>
    (Finset.univ.filter fun y : Places.Rfin Fq E →ₐ[Fq] L => twist y g = φ.comp y).card with hN
  have hU : ∀ g, N g ≤ ellF Fq E 0 * (Q0 ^ 2 + (2 * genusF Fq E + 1) * Q0) := fun g =>
    card_twisted_le L g p k Q0 hQ0def φ hφ' P0 hP0 hQ0
  have h0 : ∀ g, ¬ (g ∈ (constRes Fq E).ker) → N g = 0 := by
    intro g hg
    by_contra hne
    obtain ⟨y, hy⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
    rw [Finset.mem_filter] at hy
    exact hg ((mem_ker_constRes g).mpr fun c => fix_const_of_twist L hℓ g φ hφ y hy.2 c)
  have hG : Fintype.card (E ≃ₐ[RatFunc Fq] E) * Q0 ^ 2 ≤ ∑ g, N g := by
    rw [← hq]; exact card_gal_mul_le_sum L p m hm hL φ hφ
  have hH : ∑ g ∈ Finset.univ.filter (· ∈ Hs), N g ≤
      (Finset.univ.filter (· ∈ Hs)).card * Places.numPoints Fq F m :=
    (sum_twisted_H_le L ι φ).trans (Nat.mul_le_mul_left _ (card_fixed_le_numPoints L hm φ hφ))
  have hG0 : Fintype.card (E ≃ₐ[RatFunc Fq] E) =
      ellF Fq E 0 * (Finset.univ.filter (· ∈ (constRes Fq E).ker)).card := by
    rw [← Nat.card_eq_fintype_card, card_gal_eq, RR.ellF_zero, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hH0 : (Finset.univ.filter (· ∈ Hs)).card ≤
      ellF Fq E 0 * (Finset.univ.filter fun g => g ∈ Hs ∧ g ∈ (constRes Fq E).ker).card := by
    have h1 := card_le_mul_card_inf_ker (constRes Fq E) Hs
    rw [IsGalois.card_aut_eq_finrank, ← RR.ellF_zero, Nat.card_eq_fintype_card, Fintype.card_subtype,
      Nat.card_eq_fintype_card, Fintype.card_subtype] at h1
    refine h1.trans (Nat.mul_le_mul_left _ (Finset.card_le_card fun g hg => ?_))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Subgroup.mem_inf] at hg ⊢
    exact hg
  have hmain := count_assembly N (· ∈ Hs) (· ∈ (constRes Fq E).ker) (ellF Fq E 0) (Q0 ^ 2)
    ((2 * genusF Fq E + 1) * Q0) (Places.numPoints Fq F m) hU h0 hG hH hG0 hH0
  have hH1 : 1 ≤ (Finset.univ.filter (· ∈ Hs)).card :=
    Finset.card_pos.mpr ⟨1, by simp [Hs.one_mem]⟩
  rw [← Nat.card_eq_fintype_card] at hmain
  generalize (Finset.univ.filter (· ∈ Hs)).card = H at hmain hH1
  by_contra hcon
  push_neg at hcon
  have h1 := Nat.mul_le_mul_left H (Nat.succ_le_of_lt hcon)
  have h2 : Nat.card (E ≃ₐ[RatFunc Fq] E) * ((2 * genusF Fq E + 1) * Q0) ≤
      H * (Nat.card (E ≃ₐ[RatFunc Fq] E) * ((2 * genusF Fq E + 1) * Q0)) := Nat.le_mul_of_pos_left _ hH1
  nlinarith

end FF

end RamanujanPetersson.ZetaSB


end

-- ===== S3.SB_Upper =====
section

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


end

-- ===== S3.Zeta_A =====
section

/-!
# S3-ZetaSB, O5 part A: effective divisors and the Newton identity

`A_n` = number of effective divisors of degree `n` (finite: they are supported on the places of degree `≤ n`).
Newton identity (the coefficientwise form of `t Z'(t) = Z(t) · Σ_m N_m t^m`):
`n A_n = Σ_{m=1}^n N_m A_{n-m}`, proved by the bijection `D ↦ D - k P` (no infinite products).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.ZetaSB

open Places

section Eff

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- The places of degree `≤ n`. -/
noncomputable def lowPlaces (n : ℕ) : Finset (Place Fq F) := (finite_place_deg_le Fq F n).toFinset

/-- The effective divisors of degree `n`. -/
noncomputable def effDivs (n : ℕ) : Finset (Divisor Fq F) :=
  ((lowPlaces Fq F n).finsupp fun _ => Finset.Icc (0 : ℤ) n).filter fun D => Divisor.deg D = n

/-- `A_n`: the number of effective divisors of degree `n`. -/
noncomputable def numEff (n : ℕ) : ℕ := (effDivs Fq F n).card

variable {Fq F}

theorem mem_lowPlaces {n : ℕ} {P : Place Fq F} : P ∈ lowPlaces Fq F n ↔ P.deg ≤ n := by
  rw [lowPlaces, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

theorem deg_eq_sum_of_subset (D : Divisor Fq F) {s : Finset (Place Fq F)} (hs : D.support ⊆ s) :
    Divisor.deg D = ∑ P ∈ s, D P * (P.deg : ℤ) :=
  Finsupp.sum_of_support_subset D hs (fun P n => n * (P.deg : ℤ)) (fun _ _ => zero_mul _)

theorem nonneg_apply {D : Divisor Fq F} (hD : 0 ≤ D) (P : Place Fq F) : 0 ≤ D P := by
  simpa using Finsupp.le_def.mp hD P

theorem term_le_deg {D : Divisor Fq F} (hD : 0 ≤ D) (P : Place Fq F) :
    D P * (P.deg : ℤ) ≤ Divisor.deg D := by
  classical
  rw [deg_eq_sum_of_subset D (Finset.subset_insert P D.support)]
  exact Finset.single_le_sum (f := fun Q => D Q * (Q.deg : ℤ))
    (fun Q _ => mul_nonneg (nonneg_apply hD Q) (Nat.cast_nonneg _)) (Finset.mem_insert_self P _)

theorem apply_le_deg {D : Divisor Fq F} (hD : 0 ≤ D) (P : Place Fq F) : D P ≤ Divisor.deg D := by
  have h1 := term_le_deg hD P
  have h2 : (1 : ℤ) ≤ P.deg := by exact_mod_cast P.deg_pos
  nlinarith [nonneg_apply hD P]

theorem deg_le_of_apply_ne {D : Divisor Fq F} (hD : 0 ≤ D) {P : Place Fq F} (hP : D P ≠ 0) :
    (P.deg : ℤ) ≤ Divisor.deg D := by
  have h1 := term_le_deg hD P
  have h2 : 1 ≤ D P := by have := nonneg_apply hD P; omega
  nlinarith [Nat.cast_nonneg (α := ℤ) P.deg]

theorem mem_effDivs {n : ℕ} {D : Divisor Fq F} : D ∈ effDivs Fq F n ↔ 0 ≤ D ∧ Divisor.deg D = n := by
  classical
  rw [effDivs, Finset.mem_filter, Finset.mem_finsupp_iff]
  constructor
  · rintro ⟨⟨hsupp, hval⟩, hdeg⟩
    refine ⟨Finsupp.le_def.mpr fun P => ?_, hdeg⟩
    by_cases hP : P ∈ lowPlaces Fq F n
    · simpa using (Finset.mem_Icc.mp (hval P hP)).1
    · have : P ∉ D.support := fun h => hP (hsupp h)
      simp [Finsupp.notMem_support_iff.mp this]
  · rintro ⟨hD, hdeg⟩
    refine ⟨⟨fun P hP => ?_, fun P _ => ?_⟩, hdeg⟩
    · rw [mem_lowPlaces]
      have := deg_le_of_apply_ne hD (Finsupp.mem_support_iff.mp hP)
      rw [hdeg] at this
      exact_mod_cast this
    · rw [Finset.mem_Icc, ← hdeg]
      exact ⟨nonneg_apply hD P, apply_le_deg hD P⟩

theorem support_subset_lowPlaces {n : ℕ} {D : Divisor Fq F} (hD : D ∈ effDivs Fq F n) :
    D.support ⊆ lowPlaces Fq F n := by
  classical
  rw [effDivs, Finset.mem_filter, Finset.mem_finsupp_iff] at hD
  exact hD.1.1

/-- `#{D ∈ Eff_n : k ≤ D(P)} = A_{n - k deg P}` (and `0` if `k deg P > n`). -/
theorem card_filter_le_eff (n k : ℕ) (P : Place Fq F) :
    ((effDivs Fq F n).filter fun D => (k : ℤ) ≤ D P).card =
      if k * P.deg ≤ n then numEff Fq F (n - k * P.deg) else 0 := by
  classical
  split_ifs with hk
  · rw [numEff]
    refine Finset.card_nbij' (fun D => D - Finsupp.single P (k : ℤ)) (fun D => D + Finsupp.single P (k : ℤ))
      ?_ ?_ ?_ ?_
    · intro D hD
      rw [Finset.mem_coe, Finset.mem_filter, mem_effDivs] at hD
      rw [Finset.mem_coe, mem_effDivs]
      refine ⟨Finsupp.le_def.mpr fun Q => ?_, ?_⟩
      · rw [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply]
        have := nonneg_apply hD.1.1 Q
        split_ifs with hQ
        · subst hQ; simp only [Finsupp.coe_zero, Pi.zero_apply]; linarith [hD.2]
        · simpa using this
      · rw [Divisor.deg_sub, Divisor.deg_single, hD.1.2]
        push_cast [Nat.cast_sub hk]; ring
    · intro D hD
      rw [Finset.mem_coe, mem_effDivs] at hD
      rw [Finset.mem_coe, Finset.mem_filter, mem_effDivs]
      refine ⟨⟨add_nonneg hD.1 (Finsupp.single_nonneg.mpr (Nat.cast_nonneg k)), ?_⟩, ?_⟩
      · rw [Divisor.deg_add, Divisor.deg_single, hD.2]
        push_cast [Nat.cast_sub hk]; ring
      · rw [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
        linarith [nonneg_apply hD.1 P]
    · intro D _; simp
    · intro D _; simp
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro D hD hkD
    rw [mem_effDivs] at hD
    have h1 := term_le_deg hD.1 P
    rw [hD.2] at h1
    have : (k : ℤ) * P.deg ≤ n := le_trans (mul_le_mul_of_nonneg_right hkD (Nat.cast_nonneg _)) h1
    exact hk (by exact_mod_cast this)

/-- For `D ∈ Eff_n`: `n = Σ_{P, deg P ≤ n} Σ_{k=1}^n [k ≤ D(P)] deg P`. -/
theorem eq_sum_of_mem_effDivs {n : ℕ} {D : Divisor Fq F} (hD : D ∈ effDivs Fq F n) :
    n = ∑ P ∈ lowPlaces Fq F n, ∑ k ∈ Finset.Icc 1 n, if (k : ℤ) ≤ D P then P.deg else 0 := by
  classical
  have hsupp := support_subset_lowPlaces hD
  rw [mem_effDivs] at hD
  have hin : ∀ P, ∑ k ∈ Finset.Icc 1 n, (if (k : ℤ) ≤ D P then P.deg else 0) = (D P).toNat * P.deg := by
    intro P
    have h0 := nonneg_apply hD.1 P
    have hle : D P ≤ n := hD.2 ▸ apply_le_deg hD.1 P
    set a := (D P).toNat with ha
    have ha' : (a : ℤ) = D P := Int.toNat_of_nonneg h0
    have han : a ≤ n := by exact_mod_cast (ha' ▸ hle)
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    congr 1
    have : (Finset.Icc 1 n).filter (fun k : ℕ => (k : ℤ) ≤ D P) = Finset.Icc 1 a := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc, ← ha']
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, by exact_mod_cast h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans han⟩, by exact_mod_cast h2⟩
    rw [this, Nat.card_Icc]; omega
  rw [Finset.sum_congr rfl fun P _ => hin P]
  have key : ((∑ P ∈ lowPlaces Fq F n, (D P).toNat * P.deg : ℕ) : ℤ) = Divisor.deg D := by
    rw [deg_eq_sum_of_subset D hsupp]
    push_cast
    exact Finset.sum_congr rfl fun P _ => by rw [Int.toNat_of_nonneg (nonneg_apply hD.1 P)]
  have := hD.2
  rw [← key] at this
  exact_mod_cast this.symm

theorem sum_reindex_mul (n d : ℕ) (hd : 0 < d) (f : ℕ → ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (if k * d ≤ n then f (k * d) else 0) =
      ∑ m ∈ Finset.Icc 1 n, (if d ∣ m then f m else 0) := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  have himg : (Finset.Icc 1 n).filter (fun m => d ∣ m) =
      ((Finset.Icc 1 n).filter fun k => k * d ≤ n).image (· * d) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, c, rfl⟩
      have hc : 1 ≤ c := by
        rcases Nat.eq_zero_or_pos c with h | h
        · subst h; omega
        · exact h
      exact ⟨c, ⟨⟨hc, le_trans (Nat.le_mul_of_pos_left c hd) h2⟩, by rw [mul_comm]; exact h2⟩,
        mul_comm c d⟩
    · rintro ⟨k, ⟨⟨h1, _⟩, h3⟩, rfl⟩
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), h3⟩, Dvd.intro_left k rfl⟩
  rw [himg, Finset.sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_right hd h]

theorem numPoints_eq_sum_low {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    numPoints Fq F m = ∑ P ∈ (lowPlaces Fq F n).filter (fun P => P.deg ∣ m), P.deg := by
  classical
  have hm : m ≠ 0 := by omega
  rw [numPoints, dif_neg hm]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext P
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_filter, mem_lowPlaces]
  exact ⟨fun h => ⟨(Nat.le_of_dvd (by omega) h).trans hmn, h⟩, fun h => h.2⟩

/-- **Newton identity** `n A_n = Σ_{m=1}^n N_m A_{n-m}`. -/
theorem newton (n : ℕ) :
    n * numEff Fq F n = ∑ m ∈ Finset.Icc 1 n, numPoints Fq F m * numEff Fq F (n - m) := by
  classical
  calc n * numEff Fq F n = ∑ D ∈ effDivs Fq F n, n := by rw [numEff, Finset.sum_const, smul_eq_mul, mul_comm]
    _ = ∑ D ∈ effDivs Fq F n, ∑ P ∈ lowPlaces Fq F n, ∑ k ∈ Finset.Icc 1 n,
          (if (k : ℤ) ≤ D P then P.deg else 0) :=
        Finset.sum_congr rfl fun D hD => eq_sum_of_mem_effDivs hD
    _ = ∑ P ∈ lowPlaces Fq F n, ∑ k ∈ Finset.Icc 1 n,
          P.deg * ((effDivs Fq F n).filter fun D => (k : ℤ) ≤ D P).card := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun P _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
    _ = ∑ P ∈ lowPlaces Fq F n, ∑ k ∈ Finset.Icc 1 n,
          (if k * P.deg ≤ n then P.deg * numEff Fq F (n - k * P.deg) else 0) := by
        refine Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun k _ => ?_
        rw [card_filter_le_eff]
        split_ifs <;> simp
    _ = ∑ P ∈ lowPlaces Fq F n, ∑ m ∈ Finset.Icc 1 n,
          (if P.deg ∣ m then P.deg * numEff Fq F (n - m) else 0) :=
        Finset.sum_congr rfl fun P _ =>
          sum_reindex_mul n P.deg P.deg_pos (fun m => P.deg * numEff Fq F (n - m))
    _ = ∑ m ∈ Finset.Icc 1 n, ∑ P ∈ lowPlaces Fq F n,
          (if P.deg ∣ m then P.deg * numEff Fq F (n - m) else 0) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun m hm => by
        rw [Finset.mem_Icc] at hm
        rw [← Finset.sum_filter, ← Finset.sum_mul, numPoints_eq_sum_low hm.1 hm.2]

theorem numEff_zero : numEff Fq F 0 = 1 := by
  classical
  rw [numEff, Finset.card_eq_one]
  refine ⟨0, Finset.eq_singleton_iff_unique_mem.mpr ⟨mem_effDivs.mpr ⟨le_rfl, by simp [Divisor.deg]⟩,
    fun D hD => ?_⟩⟩
  rw [mem_effDivs] at hD
  ext P
  have h1 := apply_le_deg hD.1 P
  have h2 := nonneg_apply hD.1 P
  rw [hD.2] at h1
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  push_cast at h1
  omega

end Eff

end RamanujanPetersson.ZetaSB


end

-- ===== S3.SB_ClosA =====
section

/-!
# S3-ZetaSB, E1 part A: a Galois closure of `F / K` with an arbitrary constant extension

`K = RatFunc Fq`. `GalE0 Fq F` is the splitting field of the minimal polynomial of a primitive element of `F / K`;
`GalE Fq F n` is the splitting field over `GalE0` of `X ^ (q ^ (n+1)) - X`. Both carry the function-field instance
list; `GalE Fq F n` is Galois over `K` and `closureEmb Fq F n : F →ₐ[K] GalE Fq F n`.
-/

set_option autoImplicit false

open Polynomial Module IsDedekindDomain

namespace RamanujanPetersson.ZetaSB

/-- Towers compose: `A → B → C` and `A, B → C → D` give `A → B → D`. -/
theorem isScalarTower_of_towers (A B C D : Type*) [CommSemiring A] [CommSemiring B] [CommSemiring C]
    [Semiring D] [Algebra A B] [Algebra A C] [Algebra B C] [Algebra A D] [Algebra B D] [Algebra C D]
    [IsScalarTower A C D] [IsScalarTower B C D] [IsScalarTower A B C] : IsScalarTower A B D :=
  IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq A C D, IsScalarTower.algebraMap_eq B C D,
      IsScalarTower.algebraMap_eq A B C, RingHom.comp_assoc])

section Closure

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- A primitive-element power basis of `F / K`. -/
noncomputable abbrev primPB : PowerBasis (RatFunc Fq) F :=
  Field.powerBasisOfFiniteOfSeparable (RatFunc Fq) F

/-- The Galois closure `E0` of `F / K` (splitting field of the minimal polynomial of a primitive element). -/
abbrev GalE0 : Type _ := SplittingField (minpoly (RatFunc Fq) (primPB Fq F).gen)

instance : IsScalarTower Fq Fq[X] (GalE0 Fq F) :=
  isScalarTower_of_towers Fq Fq[X] (RatFunc Fq) (GalE0 Fq F)

instance : IsGalois (RatFunc Fq) (GalE0 Fq F) :=
  IsGalois.of_separable_splitting_field (Algebra.IsSeparable.isSeparable (RatFunc Fq) (primPB Fq F).gen)

instance : FunctionField Fq (GalE0 Fq F) := inferInstanceAs (FiniteDimensional (RatFunc Fq) (GalE0 Fq F))

/-- `X ^ (q ^ (n+1)) - X` over `K`. -/
noncomputable abbrev frobPoly (n : ℕ) : (RatFunc Fq)[X] := X ^ (Fintype.card Fq ^ (n + 1)) - X

/-- The Galois closure with constants `F_{q^(n+1)}` adjoined. -/
abbrev GalE (n : ℕ) : Type _ :=
  SplittingField ((frobPoly Fq n).map (algebraMap (RatFunc Fq) (GalE0 Fq F)))

variable (n : ℕ)

instance : IsScalarTower Fq[X] (RatFunc Fq) (GalE Fq F n) :=
  isScalarTower_of_towers Fq[X] (RatFunc Fq) (GalE0 Fq F) (GalE Fq F n)

instance : IsScalarTower Fq Fq[X] (GalE Fq F n) :=
  isScalarTower_of_towers Fq Fq[X] (GalE0 Fq F) (GalE Fq F n)

instance : IsScalarTower (RatFunc Fq) (GalE0 Fq F) (GalE Fq F n) := inferInstance

instance : FunctionField Fq (GalE Fq F n) :=
  Module.Finite.trans (GalE0 Fq F) (GalE Fq F n)

theorem charP_ringChar (R : Type*) [Field R] [Algebra Fq R] : CharP R (ringChar Fq) :=
  charP_of_injective_algebraMap (algebraMap Fq R).injective (ringChar Fq)

theorem ringChar_dvd_card_pow : ringChar Fq ∣ Fintype.card Fq ^ (n + 1) :=
  Dvd.dvd.mul_left ((CharP.cast_eq_zero_iff Fq (ringChar Fq) _).mp (FiniteField.cast_card_eq_zero Fq)) _

theorem one_lt_card_pow : 1 < Fintype.card Fq ^ (n + 1) :=
  Nat.one_lt_pow (Nat.succ_ne_zero n) Fintype.one_lt_card

theorem frobPoly_separable (R : Type*) [Field R] [Algebra Fq R] [Algebra (RatFunc Fq) R] :
    ((frobPoly Fq n).map (algebraMap (RatFunc Fq) R)).Separable := by
  haveI := charP_ringChar Fq R
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X]
  exact galois_poly_separable (ringChar Fq) _ (ringChar_dvd_card_pow Fq n)

instance : IsGalois (GalE0 Fq F) (GalE Fq F n) :=
  IsGalois.of_separable_splitting_field (frobPoly_separable Fq n (GalE0 Fq F))

instance : Algebra.IsSeparable (RatFunc Fq) (GalE Fq F n) :=
  Algebra.IsSeparable.trans (RatFunc Fq) (GalE0 Fq F) (GalE Fq F n)

instance : IsGalois (RatFunc Fq) (GalE Fq F n) := by
  refine isGalois_iff.mpr ⟨inferInstance, ?_⟩
  have h1 : minpoly (RatFunc Fq) (primPB Fq F).gen ≠ 0 :=
    minpoly.ne_zero (Algebra.IsIntegral.isIntegral _)
  have h2 : frobPoly Fq n ≠ 0 := by
    have := frobPoly_separable Fq n (RatFunc Fq)
    rw [Algebra.algebraMap_self, Polynomial.map_id] at this
    exact this.ne_zero
  have := Polynomial.IsSplittingField.mul (K := GalE0 Fq F) (L := GalE Fq F n) _ _ h1 h2
  exact Normal.of_isSplittingField (minpoly (RatFunc Fq) (primPB Fq F).gen * frobPoly Fq n)

/-- A root of the minimal polynomial of the primitive element in `E0`. -/
noncomputable def rootE0 : GalE0 Fq F :=
  rootOfSplits (SplittingField.splits (minpoly (RatFunc Fq) (primPB Fq F).gen))
    (by
      rw [degree_map]
      exact (minpoly.degree_pos (Algebra.IsIntegral.isIntegral (primPB Fq F).gen)).ne')

theorem aeval_rootE0 : aeval (rootE0 Fq F) (minpoly (RatFunc Fq) (primPB Fq F).gen) = 0 := by
  rw [aeval_def, eval₂_eq_eval_map]
  exact eval_rootOfSplits _ _

/-- `F ↪ E0` over `K`. -/
noncomputable def embE0 : F →ₐ[RatFunc Fq] GalE0 Fq F :=
  (primPB Fq F).lift (rootE0 Fq F) (aeval_rootE0 Fq F)

/-- `F ↪ GalE n` over `K`. -/
noncomputable def closureEmb : F →ₐ[RatFunc Fq] GalE Fq F n :=
  (IsScalarTower.toAlgHom (RatFunc Fq) (GalE0 Fq F) (GalE Fq F n)).comp (embE0 Fq F)

end Closure

end RamanujanPetersson.ZetaSB


end

-- ===== S3.SB_ClosB =====
section

/-!
# S3-ZetaSB, E1 part B: a place of `GalE Fq F n` of degree `ℓ(0)`

Pick a finite place `P` of `E0 = GalE0 Fq F`, of degree `n + 1`, and a place `Q` of `E = GalE Fq F n` over it. A
Frobenius element `σ ∈ Gal(E/E0)` at `Q` (Mathlib `IsArithFrobAt.exists_of_isInvariant`) fixes the roots of
`X ^ (q ^ (n+1)) - X` (two roots differ by a constant, a unit), hence all of `E`, so `x ^ (q ^ (n+1)) = x` on the residue
field: `deg Q ∣ n + 1`. The `q ^ (n+1)` roots are constants, so `n + 1 ≤ ℓ0`, and `ℓ0 ∣ deg Q`: `deg Q = ℓ0 = ℓ(0)`.
-/

set_option autoImplicit false

open Polynomial Module IsDedekindDomain

namespace RamanujanPetersson.ZetaSB

open RR

section ClosB

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]

/-- Every function field has a finite place. -/
theorem exists_finPlace (E : Type*) [Field E] [Algebra Fq E] [Algebra Fq[X] E] [Algebra (RatFunc Fq) E]
    [IsScalarTower Fq[X] (RatFunc Fq) E] [IsScalarTower Fq Fq[X] E] [FunctionField Fq E]
    [Algebra.IsSeparable (RatFunc Fq) E] :
    Nonempty (HeightOneSpectrum (Places.Rfin Fq E)) := by
  classical
  have hX : (Ideal.span {(X : Fq[X])}).IsPrime := (Ideal.span_singleton_prime X_ne_zero).mpr prime_X
  have hinj := FunctionField.ringOfIntegers.algebraMap_injective Fq E
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := Places.Rfin Fq E)
    (Ideal.span {(X : Fq[X])}) ⊥ (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
  refine ⟨⟨Q, hQ, fun h => ?_⟩⟩
  rw [h, Ideal.comap_bot_of_injective _ hinj] at hQc
  exact X_ne_zero (Ideal.span_singleton_eq_bot.mp hQc.symm)

variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- **E1**: some `GalE Fq F n` has a place of degree `ℓ(0)`. -/
theorem exists_galE_place : ∃ n : ℕ, ∃ P0 : Places.Place Fq (GalE Fq F n),
    P0.deg = ellF Fq (GalE Fq F n) 0 := by
  classical
  obtain ⟨P⟩ := exists_finPlace Fq (GalE0 Fq F)
  obtain ⟨n, hn⟩ : ∃ n, Places.deg Fq P = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Places.deg_pos Fq P).ne'
  refine ⟨n, ?_⟩
  set N := Fintype.card Fq ^ (n + 1) with hN
  set ι0 := IsScalarTower.toAlgHom (RatFunc Fq) (GalE0 Fq F) (GalE Fq F n) with hι0
  letI : Algebra (Places.Rfin Fq (GalE0 Fq F)) (Places.Rfin Fq (GalE Fq F n)) :=
    (finMap Fq ι0).toRingHom.toAlgebra
  haveI : IsScalarTower Fq[X] (Places.Rfin Fq (GalE0 Fq F)) (Places.Rfin Fq (GalE Fq F n)) :=
    IsScalarTower.of_algebraMap_eq fun a => Subtype.ext (by
      change algebraMap Fq[X] (GalE Fq F n) a = ι0 (algebraMap Fq[X] (GalE0 Fq F) a)
      exact ((ι0.restrictScalars Fq[X]).commutes a).symm)
  haveI : Algebra.IsIntegral (Places.Rfin Fq (GalE0 Fq F)) (Places.Rfin Fq (GalE Fq F n)) :=
    ⟨fun b => (Algebra.IsIntegral.isIntegral (R := Fq[X]) b).tower_top⟩
  have hinj : Function.Injective
      (algebraMap (Places.Rfin Fq (GalE0 Fq F)) (Places.Rfin Fq (GalE Fq F n))) :=
    fun a b h => Subtype.ext (ι0.injective (congrArg Subtype.val h))
  haveI := P.isPrime
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (S := Places.Rfin Fq (GalE Fq F n)) P.asIdeal ⊥
    (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
  have hQne : Q ≠ ⊥ := fun h => P.ne_bot (by rw [← hQc, h, Ideal.comap_bot_of_injective _ hinj])
  set Qh : HeightOneSpectrum (Places.Rfin Fq (GalE Fq F n)) := ⟨Q, hQ, hQne⟩ with hQh
  -- the decomposition setting: `G = Gal(E/E0)` inside `Gal(E/K)`
  haveI : SMulCommClass ι0.fieldRange.fixingSubgroup (Places.Rfin Fq (GalE0 Fq F))
      (Places.Rfin Fq (GalE Fq F n)) := ⟨fun h a b => Subtype.ext (by
    change (h : GalE Fq F n ≃ₐ[RatFunc Fq] GalE Fq F n) (ι0 a * b) =
      ι0 a * (h : GalE Fq F n ≃ₐ[RatFunc Fq] GalE Fq F n) b
    rw [map_mul, (IntermediateField.mem_fixingSubgroup_iff _ _).mp h.2 _ (ι0.mem_fieldRange.mpr ⟨a, rfl⟩)])⟩
  haveI : Algebra.IsInvariant (Places.Rfin Fq (GalE0 Fq F)) (Places.Rfin Fq (GalE Fq F n))
      ι0.fieldRange.fixingSubgroup := ⟨fun b hb => by
    have hfix : ∀ h ∈ ι0.fieldRange.fixingSubgroup, h (b : GalE Fq F n) = b :=
      fun h hh => congrArg Subtype.val (hb ⟨h, hh⟩)
    have hmem : (b : GalE Fq F n) ∈ ι0.fieldRange := by
      rw [← IsGalois.fixedField_fixingSubgroup ι0.fieldRange]
      exact (IntermediateField.mem_fixedField_iff _ _).mpr hfix
    obtain ⟨a, ha⟩ := ι0.mem_fieldRange.mp hmem
    have hint : IsIntegral Fq[X] a := by
      have hb2 : IsIntegral Fq[X] (b : GalE Fq F n) := b.2
      rw [← ha] at hb2
      exact (isIntegral_algHom_iff (ι0.restrictScalars Fq[X])
        (RingHom.injective (ι0.restrictScalars Fq[X]).toRingHom)).mp hb2
    exact ⟨⟨a, hint⟩, Subtype.ext ha⟩⟩
  haveI := Qh.isPrime
  haveI : Finite (Places.Rfin Fq (GalE Fq F n) ⧸ Qh.asIdeal) := Places.finite_residue Qh
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (Places.Rfin Fq (GalE0 Fq F))
    ι0.fieldRange.fixingSubgroup Qh.asIdeal
  have hcardP : Nat.card (Places.Rfin Fq (GalE0 Fq F) ⧸ Qh.asIdeal.under (Places.Rfin Fq (GalE0 Fq F))) = N := by
    rw [show Qh.asIdeal.under (Places.Rfin Fq (GalE0 Fq F)) = P.asIdeal from hQc, Places.card_residue_eq Fq P, hn]
  have hfr : ∀ b : Places.Rfin Fq (GalE Fq F n), σ • b - b ^ N ∈ Q := fun b => by
    have := hσ b
    rw [hcardP] at this
    exact this
  -- constants: roots of `X ^ N - X` are integral over `Fq`
  have hint : ∀ r : GalE Fq F n, r ^ N = r → IsIntegral Fq r := fun r hr =>
    ⟨X ^ N - X, monic_X_pow_sub (by rw [degree_X]; exact_mod_cast one_lt_card_pow Fq n), by
      simp [eval₂_sub, eval₂_X_pow, eval₂_X, hr]⟩
  have hfixr : ∀ r : GalE Fq F n, r ^ N = r →
      (σ : GalE Fq F n ≃ₐ[RatFunc Fq] GalE Fq F n) r = r := by
    intro r hr
    set s := (σ : GalE Fq F n ≃ₐ[RatFunc Fq] GalE Fq F n) r with hs
    have hsN : s ^ N = s := by rw [hs, ← map_pow, hr]
    by_contra hne
    have hc0 : s - r ≠ 0 := sub_ne_zero.mpr hne
    have hcm : s - r ∈ Places.constField Fq (GalE Fq F n) :=
      sub_mem ((mem_algebraicClosure_iff' (F := Fq)).mpr (hint s hsN))
        ((mem_algebraicClosure_iff' (F := Fq)).mpr (hint r hr))
    have hci : IsIntegral Fq (s - r)⁻¹ := (mem_algebraicClosure_iff' (F := Fq)).mp (inv_mem hcm)
    set rb : Places.Rfin Fq (GalE Fq F n) := ⟨r, (hint r hr).tower_top⟩ with hrb
    set ci : Places.Rfin Fq (GalE Fq F n) := ⟨(s - r)⁻¹, hci.tower_top⟩ with hci'
    have h1 := Q.mul_mem_left ci (hfr rb)
    have h2 : ci * (σ • rb - rb ^ N) = 1 := Subtype.ext (by
      change (s - r)⁻¹ * (s - r ^ N) = 1
      rw [hr, inv_mul_cancel₀ hc0])
    rw [h2] at h1
    exact hQ.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have hfixE0 : ∀ a : GalE0 Fq F, (σ : GalE Fq F n ≃ₐ[RatFunc Fq] GalE Fq F n)
      (algebraMap (GalE0 Fq F) (GalE Fq F n) a) = algebraMap (GalE0 Fq F) (GalE Fq F n) a :=
    fun a => (IntermediateField.mem_fixingSubgroup_iff _ _).mp σ.2 _ (ι0.mem_fieldRange.mpr ⟨a, rfl⟩)
  set σ' : GalE Fq F n →ₐ[GalE0 Fq F] GalE Fq F n :=
    { (σ : GalE Fq F n ≃ₐ[RatFunc Fq] GalE Fq F n).toAlgHom.toRingHom with commutes' := hfixE0 } with hσ'
  have hσid : σ' = AlgHom.id (GalE0 Fq F) (GalE Fq F n) := by
    refine AlgHom.ext_of_adjoin_eq_top (SplittingField.adjoin_rootSet _) fun r hr => ?_
    rw [mem_rootSet'] at hr
    have h2 := hr.2
    rw [aeval_map_algebraMap] at h2
    simp only [frobPoly, map_sub, map_pow, aeval_X] at h2
    exact hfixr r (sub_eq_zero.mp h2)
  have hall : ∀ x, (σ : GalE Fq F n ≃ₐ[RatFunc Fq] GalE Fq F n) x = x := fun x =>
    congrArg (fun φ : GalE Fq F n →ₐ[GalE0 Fq F] GalE Fq F n => φ x) hσid
  -- residue field of `Q` is fixed by `x ↦ x ^ N`
  have hdeg : Places.deg Fq Qh ∣ n + 1 := by
    haveI := Qh.isMaximal
    letI : Field (Places.Rfin Fq (GalE Fq F n) ⧸ Qh.asIdeal) := Ideal.Quotient.field _
    refine finrank_dvd_of_fixed (AlgHom.id Fq _) (n + 1) fun x => ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 := hfr b
    have h2 : σ • b = b := Subtype.ext (hall b)
    rw [h2] at h1
    rw [AlgHom.id_apply, ← hN, ← map_pow, Ideal.Quotient.eq, ← neg_sub]
    exact Q.neg_mem h1
  -- the `N` roots are constants
  have hNle : N ≤ Fintype.card Fq ^ ellF Fq (GalE Fq F n) 0 := by
    rw [ellF_zero, ← Nat.card_eq_fintype_card (α := Fq), ← Module.natCard_eq_pow_finrank]
    have hc := card_rootSet_eq_natDegree (K := GalE Fq F n) (frobPoly_separable Fq n (GalE0 Fq F))
      (SplittingField.splits _)
    rw [natDegree_map, FiniteField.X_pow_card_sub_X_natDegree_eq (K' := RatFunc Fq) (one_lt_card_pow Fq n)]
      at hc
    rw [hN, ← hc, ← Nat.card_eq_fintype_card]
    refine Nat.card_le_card_of_injective (fun r => ⟨(r : GalE Fq F n), ?_⟩) fun a b h => ?_
    · have h2 := ((mem_rootSet'.mp r.2).2)
      rw [aeval_map_algebraMap] at h2
      simp only [frobPoly, map_sub, map_pow, aeval_X] at h2
      exact (mem_algebraicClosure_iff' (F := Fq)).mpr (hint _ (sub_eq_zero.mp h2))
    · have h' := congrArg Subtype.val h
      exact Subtype.ext h'
  have hle : n + 1 ≤ ellF Fq (GalE Fq F n) 0 := by
    by_contra h
    rw [not_le] at h
    exact absurd hNle (not_le.mpr (Nat.pow_lt_pow_right Fintype.one_lt_card h))
  refine ⟨Sum.inl Qh, ?_⟩
  have hdvd := Places.finrank_constField_dvd Fq (GalE Fq F n) (Sum.inl Qh)
  rw [Places.Place.deg_inl] at hdvd ⊢
  rw [← ellF_zero] at hdvd
  have h1 := Nat.le_of_dvd (Places.deg_pos Fq Qh) hdvd
  have h2 := Nat.le_of_dvd (Nat.succ_pos n) hdeg
  omega

end ClosB

end RamanujanPetersson.ZetaSB


end

-- ===== S3.HasseWeil_A =====
section

/-!
# S3-ZetaSB, O6b part A: the two-sided bound along a progression

For a function field `F / Fq` with full constant field, `N_m(F) = q ^ m + O(q ^ (m/2))` along `m ∈ D·ℕ`, `D > 0`:
take the Galois closure `E = GalE Fq F n` with a place of degree `ℓ = ℓ_E(0)` (`exists_galE_place`), `D = 2ℓ`,
`Q0 = q ^ (ℓ j)` (so `q ^ m = Q0 ^ 2`), a finite field `L` of large degree, and combine `lower_bound_core` (SB_GalC)
with `upper_bound_core` (SB_Upper).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial Module IsDedekindDomain

namespace RamanujanPetersson.ZetaSB

open RR

section HWA

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- **O6b (A)**: `|N_{Dj}(F) - q ^ (Dj)| ≤ C √q ^ (Dj)` for all `j ≥ j0`, some `D > 0`. -/
theorem two_sided (hk : Places.constField Fq F = ⊥) :
    ∃ D : ℕ, 0 < D ∧ ∃ C : ℝ, ∃ j0 : ℕ, ∀ j : ℕ, j0 ≤ j →
      |(Places.numPoints Fq F (D * j) : ℝ) - (Fintype.card Fq : ℝ) ^ (D * j)| ≤
        C * Real.sqrt (Fintype.card Fq) ^ (D * j) := by
  classical
  obtain ⟨n, P0, hP0⟩ := exists_galE_place Fq F
  obtain ⟨p, hchar, r, hp, hcard⟩ := FiniteField.card' Fq
  haveI := hchar
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP (GalE Fq F n) p := (Algebra.charP_iff Fq (GalE Fq F n) p).mp hchar
  set ℓ := ellF Fq (GalE Fq F n) 0 with hℓdef
  set gE := genusF Fq (GalE Fq F n) with hgE
  set G := Nat.card (GalE Fq F n ≃ₐ[RatFunc Fq] GalE Fq F n) with hG
  set Ci := Cinf Fq F with hCi
  have hℓ1 : 1 ≤ ℓ := by rw [← hP0]; exact P0.deg_pos
  have hr1 : 1 ≤ (r : ℕ) := r.pos
  refine ⟨2 * ℓ, by omega, (G * (2 * gE + 1) + (2 * gE + 1) + Ci : ℕ), (gE + ℓ) ^ 2 + 1, fun j hj => ?_⟩
  set m := 2 * ℓ * j with hm
  set Q0 := p ^ ((r : ℕ) * (ℓ * j)) with hQ0
  have hj1 : 1 ≤ j := by omega
  have hm0 : m ≠ 0 := by positivity
  have hq : Fintype.card Fq ^ m = Q0 ^ 2 := by
    rw [hcard, ← pow_mul, ← pow_mul]; congr 1; rw [hm]; ring
  have h2j : 2 ^ j ≤ Q0 := by
    calc 2 ^ j ≤ 2 ^ ((r : ℕ) * (ℓ * j)) :=
          Nat.pow_le_pow_right two_pos (by nlinarith)
      _ ≤ Q0 := Nat.pow_le_pow_left hp.two_le _
  have hQ1 : 1 ≤ Q0 := le_trans Nat.one_le_two_pow h2j
  have hQ0lt : (gE + ℓ) ^ 2 < ℓ ^ 2 * Q0 := by
    have h1 : (gE + ℓ) ^ 2 < 2 ^ j := lt_of_lt_of_le (by omega) (j.lt_two_pow_self).le
    have h2 : Q0 ≤ ℓ ^ 2 * Q0 := Nat.le_mul_of_pos_left _ (by positivity)
    omega
  have hℓm : finrank Fq (Places.constField Fq (GalE Fq F n)) ∣ m := by
    rw [← RR.ellF_zero]; exact Dvd.intro (2 * j) (by rw [hm]; ring)
  set M := m * (finrank Fq[X] (Places.Rfin Fq (GalE Fq F n))).factorial with hM
  haveI : NeZero M := ⟨mul_ne_zero hm0 (Nat.factorial_ne_zero _)⟩
  have hL : M ∣ finrank Fq (FiniteField.Extension Fq p M) := by rw [FiniteField.finrank_extension]
  have hlo := lower_bound_core (FiniteField.Extension Fq p M) (closureEmb Fq F n) p ((r : ℕ) * (ℓ * j)) Q0 m
    hm0 rfl hq hℓm hL P0 hP0 hQ0lt
  have hup := upper_bound_core (FiniteField.Extension Fq p M) hk (closureEmb Fq F n) p ((r : ℕ) * (ℓ * j)) Q0 m
    hm0 rfl hq hℓm hL P0 hP0 hQ0lt
  have hsq : Real.sqrt (Fintype.card Fq) ^ m = (Q0 : ℝ) := by
    rw [show m = 2 * (ℓ * j) by rw [hm]; ring, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _), hcard, hQ0]
    push_cast
    rw [← pow_mul]
  have hqm : (Fintype.card Fq : ℝ) ^ m = (Q0 : ℝ) ^ 2 := by exact_mod_cast hq
  rw [hsq, hqm]
  have hlo' : (Q0 : ℝ) ^ 2 ≤ Places.numPoints Fq F m + G * ((2 * gE + 1) * Q0) := by exact_mod_cast hlo
  have hup' : (Places.numPoints Fq F m : ℝ) ≤ Q0 ^ 2 + (2 * gE + 1) * Q0 + Ci := by exact_mod_cast hup
  have hQ1' : (1 : ℝ) ≤ Q0 := by exact_mod_cast hQ1
  have hG0 : (0 : ℝ) ≤ G := Nat.cast_nonneg _
  have hg0 : (0 : ℝ) ≤ gE := Nat.cast_nonneg _
  have hC0 : (0 : ℝ) ≤ Ci := Nat.cast_nonneg _
  push_cast
  rw [abs_sub_le_iff]
  constructor
  · nlinarith [mul_nonneg hC0 (sub_nonneg.mpr hQ1'), mul_nonneg (mul_nonneg hG0 (by positivity : (0 : ℝ) ≤ 2 * gE + 1))
      (by positivity : (0 : ℝ) ≤ Q0)]
  · nlinarith [mul_nonneg hC0 (by positivity : (0 : ℝ) ≤ Q0), mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * gE + 1)
      (by positivity : (0 : ℝ) ≤ Q0)]

end HWA

end RamanujanPetersson.ZetaSB


end

-- ===== S3.Zeta_B =====
section

/-!
# S3-ZetaSB, O5 part B: the index `δ`, divisor classes and the counting formula for `A_n`

* `delta Fq F`: the least positive degree of a divisor; every divisor degree is a multiple of it, so
  `A_n = 0` unless `δ ∣ n` (`numEff_eq_zero_of_not_dvd`).
* `newton_delta`: the Newton identity compressed to multiples of `δ`.
* Divisor classes `Divisor ⧸ princ`. With full constant field (`constField Fq F = ⊥`), every class of degree
  `n ≥ 2g - 1` has `(q ^ (n + 1 - g) - 1) / (q - 1)` effective members and the number of such classes does not
  depend on `n ∈ δℕ`, whence `numEff_formula` : `(q - 1) A_n = h (q ^ (n + 1 - g) - 1)` and the linear recurrence
  `numEff_rec` : `A_{n+2δ} + q^δ A_n = (1 + q^δ) A_{n+δ}` for `δ ∣ n`, `n ≥ 2g - 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.ZetaSB

open Places RR

section Delta

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- The degree as an additive homomorphism. -/
noncomputable def degHom : Divisor Fq F →+ ℤ := AddMonoidHom.mk' Divisor.deg Divisor.deg_add

theorem deg_zsmul (k : ℤ) (D : Divisor Fq F) : Divisor.deg (k • D) = k * Divisor.deg D := by
  have h := map_zsmul (degHom Fq F) k D
  simpa only [degHom, AddMonoidHom.mk'_apply, smul_eq_mul] using h

theorem exists_pos_deg : ∃ n : ℕ, 0 < n ∧ ∃ D : Divisor Fq F, Divisor.deg D = n := by
  obtain ⟨P⟩ := nonempty_infPlace Fq F
  refine ⟨Place.deg (Fq := Fq) (F := F) (Sum.inr P), Place.deg_pos _, Finsupp.single (Sum.inr P) 1, ?_⟩
  rw [Divisor.deg_single, one_mul]

/-- `δ`: the least positive degree of a divisor. -/
noncomputable def delta : ℕ := sInf {n : ℕ | 0 < n ∧ ∃ D : Divisor Fq F, Divisor.deg D = n}

theorem delta_mem : 0 < delta Fq F ∧ ∃ D : Divisor Fq F, Divisor.deg D = delta Fq F :=
  Nat.sInf_mem (exists_pos_deg Fq F)

theorem delta_pos : 0 < delta Fq F := (delta_mem Fq F).1

theorem delta_le {n : ℕ} (hn : 0 < n) {D : Divisor Fq F} (hD : Divisor.deg D = n) : delta Fq F ≤ n :=
  Nat.sInf_le ⟨hn, D, hD⟩

theorem delta_dvd_deg (D : Divisor Fq F) : (delta Fq F : ℤ) ∣ Divisor.deg D := by
  obtain ⟨hδ, D0, hD0⟩ := delta_mem Fq F
  have hδ' : (0 : ℤ) < delta Fq F := by exact_mod_cast hδ
  apply Int.dvd_of_emod_eq_zero
  have h0 := Int.emod_nonneg (Divisor.deg D) hδ'.ne'
  have h1 := Int.emod_lt_of_pos (Divisor.deg D) hδ'
  have h2 := Int.emod_add_ediv_mul (Divisor.deg D) (delta Fq F)
  have hE : Divisor.deg (D - (Divisor.deg D / delta Fq F) • D0) = Divisor.deg D % delta Fq F := by
    rw [Divisor.deg_sub, deg_zsmul, hD0]
    linarith
  generalize Divisor.deg D % (delta Fq F : ℤ) = r at h0 h1 hE ⊢
  by_contra hne
  have := delta_le Fq F (n := r.toNat) (by omega) (D := D - (Divisor.deg D / delta Fq F) • D0)
    (by rw [hE]; omega)
  omega

theorem numEff_eq_zero_of_not_dvd {n : ℕ} (hn : ¬ delta Fq F ∣ n) : numEff Fq F n = 0 := by
  rw [numEff, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro D hD
  rw [mem_effDivs] at hD
  have := delta_dvd_deg Fq F D
  rw [hD.2] at this
  exact hn (Int.natCast_dvd_natCast.mp this)

/-- The Newton identity compressed to multiples of `δ`:
`δ k A_{δk} = Σ_{j=1}^k N_{δj} A_{δ(k-j)}`. -/
theorem newton_delta (k : ℕ) :
    delta Fq F * k * numEff Fq F (delta Fq F * k) =
      ∑ j ∈ Finset.Icc 1 k, numPoints Fq F (delta Fq F * j) * numEff Fq F (delta Fq F * (k - j)) := by
  have hδ := delta_pos Fq F
  rw [newton]
  symm
  have himg : ∑ j ∈ Finset.Icc 1 k, numPoints Fq F (delta Fq F * j) * numEff Fq F (delta Fq F * (k - j)) =
      ∑ m ∈ (Finset.Icc 1 k).image (delta Fq F * ·), numPoints Fq F m * numEff Fq F (delta Fq F * k - m) := by
    rw [Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hδ h)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Nat.mul_sub]
  rw [himg]
  apply Finset.sum_subset
  · intro m hm
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
    rw [Finset.mem_Icc] at hj ⊢
    exact ⟨le_trans hj.1 (Nat.le_mul_of_pos_left j hδ), Nat.mul_le_mul_left _ hj.2⟩
  · intro m hm hnot
    rw [Finset.mem_Icc] at hm
    have hnd : ¬ delta Fq F ∣ (delta Fq F * k - m) := by
      rintro ⟨c, hc⟩
      by_cases hmd : delta Fq F ∣ m
      · obtain ⟨j, rfl⟩ := hmd
        apply hnot
        refine Finset.mem_image.mpr ⟨j, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
        · rcases Nat.eq_zero_or_pos j with h | h
          · subst h; omega
          · exact h
        · exact Nat.le_of_mul_le_mul_left hm.2 hδ
      · apply hmd
        refine ⟨k - c, ?_⟩
        rw [Nat.mul_sub]
        omega
    simp only [numEff_eq_zero_of_not_dvd Fq F hnd, mul_zero]

end Delta

section Classes

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

theorem div_one' : (Places.div (1 : F) : Divisor Fq F) = 0 :=
  (Places.div_eq_zero_iff Fq F one_ne_zero).mpr (one_mem _)

variable {F} in
theorem div_inv' {f : F} (hf : f ≠ 0) : (Places.div f⁻¹ : Divisor Fq F) = -Places.div f := by
  rw [← one_div, Places.div_div one_ne_zero hf, div_one', zero_sub]

variable {F} in
theorem div_algebraMap {c : Fq} (hc : c ≠ 0) : (Places.div (algebraMap Fq F c) : Divisor Fq F) = 0 :=
  (Places.div_eq_zero_iff Fq F ((_root_.map_ne_zero _).mpr hc)).mpr (IntermediateField.algebraMap_mem _ c)

/-- The principal divisors. -/
noncomputable def princ : AddSubgroup (Divisor Fq F) where
  carrier := {D | ∃ f : F, f ≠ 0 ∧ (Places.div f : Divisor Fq F) = D}
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, mul_ne_zero hf hg, Places.div_mul hf hg⟩
  zero_mem' := ⟨1, one_ne_zero, div_one' Fq F⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨f⁻¹, inv_ne_zero hf, div_inv' Fq hf⟩

theorem mem_princ {D : Divisor Fq F} :
    D ∈ princ Fq F ↔ ∃ f : F, f ≠ 0 ∧ (Places.div f : Divisor Fq F) = D := Iff.rfl

/-- The divisor class of `D`. -/
noncomputable abbrev cls (D : Divisor Fq F) : Divisor Fq F ⧸ princ Fq F := QuotientAddGroup.mk D

variable {Fq F}

theorem cls_div_add {f : F} (hf : f ≠ 0) (D : Divisor Fq F) :
    cls Fq F (Places.div f + D) = cls Fq F D := by
  apply QuotientAddGroup.eq.mpr
  refine (mem_princ Fq F).mpr ⟨f⁻¹, inv_ne_zero hf, ?_⟩
  rw [div_inv' Fq hf]
  abel

theorem finite_LF (D : Divisor Fq F) : (LF Fq F D : Set F).Finite := by
  have := Data.finite_LD (ffData_axioms0 (Fq := Fq) (F := F)) D
  exact Set.finite_coe_iff.mp this

/-- With full constant field, every divisor of degree `n ≥ 2g - 1` is equivalent to an effective one. -/
theorem exists_eff_of_deg (hk : constField Fq F = ⊥) {n : ℕ} (hn : 2 * (genusF Fq F : ℤ) - 1 ≤ n)
    (D : Divisor Fq F) (hD : Divisor.deg D = n) :
    ∃ E ∈ effDivs Fq F n, cls Fq F E = cls Fq F D := by
  have h1 := riemann_inequalityF' hk D
  rw [hD] at h1
  have hpos : 0 < ellF Fq F D := by
    have : (0 : ℤ) < ellF Fq F D := by omega
    exact_mod_cast this
  obtain ⟨f, hfL, hf0⟩ := Data.exists_ne_zero_of_ell_pos hpos
  refine ⟨Places.div f + D, mem_effDivs.mpr ⟨(mem_LF hf0).mp hfL, ?_⟩, cls_div_add hf0 D⟩
  rw [Divisor.deg_add, Places.deg_div hf0, hD, zero_add]

theorem ellF_of_mem (hk : constField Fq F = ⊥) {n : ℕ} (hn : 2 * (genusF Fq F : ℤ) - 1 ≤ n)
    {E : Divisor Fq F} (hE : E ∈ effDivs Fq F n) : ellF Fq F E = n + 1 - genusF Fq F := by
  have hd := (mem_effDivs.mp hE).2
  have := ellF_eq_of_deg hk (D := E) (by rw [hd]; exact hn)
  rw [hd] at this
  omega

variable [DecidableEq (Divisor Fq F ⧸ princ Fq F)]

variable (Fq F) in
/-- The number of divisor classes containing an effective divisor of degree `n`. -/
noncomputable def hcl (n : ℕ) : ℕ := ((effDivs Fq F n).image (cls Fq F)).card

/-- A class with an effective member `E0` has `(q ^ ℓ(E0) - 1) / (q - 1)` effective members. -/
theorem card_fiber_mul (hk : constField Fq F = ⊥) {n : ℕ} {E0 : Divisor Fq F} (hE0 : E0 ∈ effDivs Fq F n) :
    ((effDivs Fq F n).filter fun E => cls Fq F E = cls Fq F E0).card * (Fintype.card Fq - 1) =
      Fintype.card Fq ^ ellF Fq F E0 - 1 := by
  classical
  set Fib := (effDivs Fq F n).filter fun E => cls Fq F E = cls Fq F E0 with hFib
  set T := (finite_LF E0).toFinset.filter (· ≠ (0 : F)) with hT
  have hTmem : ∀ f, f ∈ T ↔ f ∈ LF Fq F E0 ∧ f ≠ 0 := by
    intro f
    rw [hT, Finset.mem_filter, Set.Finite.mem_toFinset]
    rfl
  have hcardT : T.card = Fintype.card Fq ^ ellF Fq F E0 - 1 := by
    have h1 : Nat.card (LF Fq F E0) = (finite_LF E0).toFinset.card := Nat.card_eq_card_finite_toFinset _
    have h0 : (0 : F) ∈ (finite_LF E0).toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact (LF Fq F E0).zero_mem
    rw [hT, Finset.filter_ne', Finset.card_erase_of_mem h0, ← h1, card_LF]
  have hmaps : ∀ f ∈ T, (Places.div f + E0 : Divisor Fq F) ∈ Fib := by
    intro f hf
    obtain ⟨hfL, hf0⟩ := (hTmem f).mp hf
    rw [hFib, Finset.mem_filter, mem_effDivs]
    refine ⟨⟨(mem_LF hf0).mp hfL, ?_⟩, cls_div_add hf0 E0⟩
    rw [Divisor.deg_add, Places.deg_div hf0, zero_add]
    exact (mem_effDivs.mp hE0).2
  rw [← hcardT, Finset.card_eq_sum_card_fiberwise hmaps, Finset.card_eq_sum_ones Fib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun E hE => ?_
  rw [one_mul]
  rw [hFib, Finset.mem_filter, mem_effDivs] at hE
  obtain ⟨⟨hEnn, -⟩, hEc⟩ := hE
  obtain ⟨f0, hf0, hdiv⟩ := (mem_princ Fq F).mp (QuotientAddGroup.eq.mp hEc.symm)
  have hE' : E = Places.div f0 + E0 := by rw [hdiv]; abel
  have hf0L : f0 ∈ LF Fq F E0 := (mem_LF hf0).mpr (hE' ▸ hEnn)
  have hfib : T.filter (fun f => Places.div f + E0 = E) =
      (Finset.univ.erase (0 : Fq)).image (fun c => algebraMap Fq F c * f0) := by
    ext f
    rw [Finset.mem_filter, hTmem, Finset.mem_image]
    constructor
    · rintro ⟨⟨_, hf⟩, hφ⟩
      rw [hE'] at hφ
      have hdd : (Places.div (f / f0) : Divisor Fq F) = 0 := by
        rw [Places.div_div hf hf0]
        exact sub_eq_zero.mpr (add_right_cancel hφ)
      have hmem := (Places.div_eq_zero_iff Fq F (div_ne_zero hf hf0)).mp hdd
      rw [hk, IntermediateField.mem_bot] at hmem
      obtain ⟨c, hc⟩ := hmem
      have hfc : f = algebraMap Fq F c * f0 := by rw [hc, div_mul_cancel₀ f hf0]
      refine ⟨c, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, hfc.symm⟩
      rintro rfl
      apply hf
      rw [hfc, map_zero, zero_mul]
    · rintro ⟨c, hc, rfl⟩
      have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
      have hne : algebraMap Fq F c ≠ 0 := (_root_.map_ne_zero _).mpr hc0
      refine ⟨⟨?_, mul_ne_zero hne hf0⟩, ?_⟩
      · rw [← Algebra.smul_def]
        exact (LF Fq F E0).smul_mem c hf0L
      · rw [Places.div_mul hne hf0, div_algebraMap Fq hc0, zero_add, hE']
  rw [hfib, Finset.card_image_of_injective _
      (fun a b h => (algebraMap Fq F).injective (mul_right_cancel₀ hf0 h)),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

/-- `A_n (q - 1) = h_n (q ^ (n + 1 - g) - 1)` for `n ≥ 2g - 1`. -/
theorem numEff_mul (hk : constField Fq F = ⊥) {n : ℕ} (hn : 2 * (genusF Fq F : ℤ) - 1 ≤ n) :
    numEff Fq F n * (Fintype.card Fq - 1) =
      hcl Fq F n * (Fintype.card Fq ^ (n + 1 - genusF Fq F) - 1) := by
  rw [numEff, hcl, Finset.card_eq_sum_card_fiberwise (f := cls Fq F)
      (t := (effDivs Fq F n).image (cls Fq F)) (fun E hE => Finset.mem_image_of_mem _ hE),
    Finset.sum_mul, Finset.card_eq_sum_ones ((effDivs Fq F n).image (cls Fq F)), Finset.sum_mul]
  refine Finset.sum_congr rfl fun c hc => ?_
  obtain ⟨E0, hE0, rfl⟩ := Finset.mem_image.mp hc
  rw [one_mul, card_fiber_mul hk hE0, ellF_of_mem hk hn hE0]

/-- Translation by a divisor of degree `n' - n` maps the classes of degree `n'` into those of degree `n`. -/
theorem hcl_le (hk : constField Fq F = ⊥) {n n' : ℕ} (hn : 2 * (genusF Fq F : ℤ) - 1 ≤ n)
    (B : Divisor Fq F) (hB : Divisor.deg B = (n' : ℤ) - n) : hcl Fq F n' ≤ hcl Fq F n := by
  unfold hcl
  refine (Finset.card_le_card (t := ((effDivs Fq F n).image (cls Fq F)).image (· + cls Fq F B))
    fun c hc => ?_).trans Finset.card_image_le
  obtain ⟨E', hE', rfl⟩ := Finset.mem_image.mp hc
  have hdeg : Divisor.deg (E' - B) = n := by
    rw [Divisor.deg_sub, hB, (mem_effDivs.mp hE').2]
    ring
  obtain ⟨E, hE, hEc⟩ := exists_eff_of_deg hk hn (E' - B) hdeg
  refine Finset.mem_image.mpr ⟨cls Fq F E, Finset.mem_image_of_mem _ hE, ?_⟩
  rw [hEc]
  simp only [cls, QuotientAddGroup.mk_sub, sub_add_cancel]

end Classes

section Formula

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- **Counting formula**: there is `h` with `(q - 1) A_n = h (q ^ (n + 1 - g) - 1)` for all `n ≥ 2g - 1`
with `δ ∣ n`. -/
theorem numEff_formula (hk : constField Fq F = ⊥) :
    ∃ h : ℕ, ∀ n : ℕ, delta Fq F ∣ n → 2 * (genusF Fq F : ℤ) - 1 ≤ n →
      ((Fintype.card Fq : ℤ) - 1) * numEff Fq F n =
        h * ((Fintype.card Fq : ℤ) ^ (n + 1 - genusF Fq F) - 1) := by
  classical
  obtain ⟨-, D0, hD0⟩ := delta_mem Fq F
  set N0 := delta Fq F * (2 * genusF Fq F) with hN0
  have hK : 2 * (genusF Fq F : ℤ) - 1 ≤ N0 := by
    have : 2 * genusF Fq F ≤ N0 := Nat.le_mul_of_pos_left _ (delta_pos Fq F)
    omega
  refine ⟨hcl Fq F N0, fun n hdvd hn => ?_⟩
  obtain ⟨c, rfl⟩ := hdvd
  have hdeg : ∀ a b : ℕ, Divisor.deg (((a : ℤ) - b) • D0) =
      ((delta Fq F * a : ℕ) : ℤ) - ((delta Fq F * b : ℕ) : ℤ) := by
    intro a b
    rw [deg_zsmul, hD0]
    push_cast
    ring
  have heq : hcl Fq F (delta Fq F * c) = hcl Fq F N0 :=
    le_antisymm (hcl_le hk hK _ (hdeg c (2 * genusF Fq F))) (hcl_le hk hn _ (hdeg (2 * genusF Fq F) c))
  have h := numEff_mul hk hn
  rw [heq] at h
  have hq : 1 ≤ Fintype.card Fq := Fintype.card_pos
  have hq2 : 1 ≤ Fintype.card Fq ^ (delta Fq F * c + 1 - genusF Fq F) := Nat.one_le_pow _ _ Fintype.card_pos
  zify [hq, hq2] at h
  linear_combination h

/-- The linear recurrence `A_{n+2δ} + q^δ A_n = (1 + q^δ) A_{n+δ}` for `δ ∣ n`, `n ≥ 2g - 1`. -/
theorem numEff_rec (hk : constField Fq F = ⊥) {n : ℕ} (hdvd : delta Fq F ∣ n)
    (hn : 2 * (genusF Fq F : ℤ) - 1 ≤ n) :
    (numEff Fq F (n + 2 * delta Fq F) : ℤ) + (Fintype.card Fq : ℤ) ^ delta Fq F * numEff Fq F n =
      (1 + (Fintype.card Fq : ℤ) ^ delta Fq F) * numEff Fq F (n + delta Fq F) := by
  obtain ⟨h, hh⟩ := numEff_formula hk
  have h0 := hh n hdvd hn
  have h1 := hh (n + delta Fq F) (dvd_add hdvd dvd_rfl) (by push_cast; omega)
  have h2 := hh (n + 2 * delta Fq F) (dvd_add hdvd (dvd_mul_left _ _)) (by push_cast; omega)
  rw [show n + delta Fq F + 1 - genusF Fq F = (n + 1 - genusF Fq F) + delta Fq F by omega, pow_add] at h1
  rw [show n + 2 * delta Fq F + 1 - genusF Fq F = (n + 1 - genusF Fq F) + delta Fq F + delta Fq F by omega,
    pow_add, pow_add] at h2
  have hq : (Fintype.card Fq : ℤ) - 1 ≠ 0 := by
    have := Fintype.one_lt_card (α := Fq)
    omega
  apply mul_left_cancel₀ hq
  linear_combination h2 + (Fintype.card Fq : ℤ) ^ delta Fq F * h0 -
    (1 + (Fintype.card Fq : ℤ) ^ delta Fq F) * h1

end Formula

end RamanujanPetersson.ZetaSB


end

-- ===== S3.Zeta_C =====
section

/-!
# S3-ZetaSB, O5 part C: the power-series argument

* `powerSum_of_newton` (abstract): a sequence `a` with `a 0 = 1`, the Newton identity
  `(k + 1) a_{k+1} = Σ_{j=0}^{k} b_{j+1} a_{k-j}` and the recurrence `a_{k+2} + Q a_k = (1 + Q) a_{k+1}` for
  `k + 2 ≥ K` has `b_k = 1 + Q^k - Σ_i c_i^k` (`k ≥ 1`) for a multiset `c ⊆ ℂ` with at most `K - 1` elements.
  Proof: `P := (1 - X)(1 - Q X) Σ a_k X^k` is a polynomial of degree `< K` with `P(0) = 1`, so
  `P = Π (1 - c_i X)` over `ℂ`; compare the logarithmic derivatives `P' = P · G` (no logarithms, no inverses).
* `numPoints_powerSum`: for a function field with full constant field, with `δ = delta Fq F`,
  `N_{δk} = δ (1 + q^{δk} - Σ_i c_i^k)` for all `k ≥ 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.ZetaSB

section PS

open PowerSeries

/-- The power series `Σ_{i ≥ 0} (Σ_j c_j^{i+1}) X^i`. -/
noncomputable def psumSeries (c : Multiset ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun i => (c.map (· ^ (i + 1))).sum

theorem coeff_succ_one_sub_mul (r : ℂ) (f : PowerSeries ℂ) (n : ℕ) :
    coeff (n + 1) ((1 - C r * X) * f) = coeff (n + 1) f - r * coeff n f := by
  rw [show (1 - C r * X) * f = f - C r * (X * f) by ring, map_sub, coeff_C_mul, coeff_succ_X_mul]

theorem coeff_zero_one_sub_mul (r : ℂ) (f : PowerSeries ℂ) :
    coeff 0 ((1 - C r * X) * f) = coeff 0 f := by
  rw [show (1 - C r * X) * f = f - C r * (X * f) by ring, map_sub, coeff_C_mul, coeff_zero_X_mul, mul_zero,
    sub_zero]

theorem one_sub_mul_geom (r : ℂ) : (1 - C r * X) * PowerSeries.mk (fun i => r ^ (i + 1)) = C r := by
  ext n
  cases n with
  | zero => rw [coeff_zero_one_sub_mul, coeff_mk, coeff_zero_C, zero_add, pow_one]
  | succ n =>
    rw [coeff_succ_one_sub_mul, coeff_mk, coeff_mk, coeff_C, if_neg (Nat.succ_ne_zero n)]
    ring

theorem deriv_one_sub (r : ℂ) : derivative ℂ (1 - C r * X) = -C r := by
  rw [map_sub, Derivation.leibniz, derivative_X, derivative_C, Derivation.map_one_eq_zero, smul_zero, add_zero,
    smul_eq_mul, mul_one, zero_sub]

theorem psumSeries_zero : psumSeries 0 = 0 := by
  ext n
  simp [psumSeries]

theorem psumSeries_cons (r : ℂ) (c : Multiset ℂ) :
    psumSeries (r ::ₘ c) = PowerSeries.mk (fun i => r ^ (i + 1)) + psumSeries c := by
  ext n
  simp [psumSeries, coeff_mk]

/-- Logarithmic derivative of `Π (1 - c_i X)`. -/
theorem deriv_prod (c : Multiset ℂ) :
    derivative ℂ (c.map fun r => 1 - C r * X).prod =
      -((c.map fun r => 1 - C r * X).prod * psumSeries c) := by
  induction c using Multiset.induction_on with
  | empty => simp [psumSeries_zero, Derivation.map_one_eq_zero]
  | cons r c ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Derivation.leibniz, ih, deriv_one_sub, smul_eq_mul, smul_eq_mul,
      psumSeries_cons]
    have hg := one_sub_mul_geom r
    linear_combination (c.map fun r => 1 - C r * X).prod * hg

theorem coe_prod_one_sub (c : Multiset ℂ) :
    (((c.map fun r => 1 - Polynomial.C r * Polynomial.X).prod : Polynomial ℂ) : PowerSeries ℂ) =
      (c.map fun r => 1 - C r * X).prod := by
  induction c using Multiset.induction_on with
  | empty => simp
  | cons r c ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.coe_mul, ih, Multiset.map_cons, Multiset.prod_cons]
    congr 1
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sub, map_one, map_mul,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C,
      Polynomial.coe_X]

/-- Over `ℂ`, a polynomial with constant coefficient `1` is `Π (1 - c_i X)`. -/
theorem exists_factor (p : Polynomial ℂ) (hp : p.coeff 0 = 1) :
    ∃ c : Multiset ℂ, Multiset.card c = p.natDegree ∧
      p = (c.map fun r => 1 - Polynomial.C r * Polynomial.X).prod := by
  have hroots : Multiset.card p.roots = p.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hne : p ≠ 0 := by
    rintro rfl
    simp at hp
  have h0 : ∀ r ∈ p.roots, r ≠ 0 := by
    intro r hr h
    subst h
    rw [Polynomial.mem_roots hne, Polynomial.IsRoot, ← Polynomial.coeff_zero_eq_eval_zero, hp] at hr
    exact one_ne_zero hr
  refine ⟨p.roots.map (·⁻¹), by rw [Multiset.card_map, hroots], ?_⟩
  have hfac := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hroots
  have hX : ∀ r ∈ p.roots, (Polynomial.X - Polynomial.C r) =
      Polynomial.C (-r) * (1 - Polynomial.C r⁻¹ * Polynomial.X) := by
    intro r hr
    rw [mul_sub, mul_one, ← mul_assoc, ← Polynomial.C_mul, neg_mul, mul_inv_cancel₀ (h0 r hr)]
    simp only [Polynomial.C_neg, Polynomial.C_1]
    ring
  rw [Multiset.map_congr rfl hX, Multiset.prod_map_mul] at hfac
  have hC : (p.roots.map fun r => Polynomial.C (-r)).prod = Polynomial.C (p.roots.map fun r => -r).prod := by
    rw [map_multiset_prod, Multiset.map_map]
    rfl
  rw [hC] at hfac
  set R := (p.roots.map fun r => 1 - Polynomial.C r⁻¹ * Polynomial.X).prod with hRdef
  have hR0 : R.coeff 0 = 1 := by
    rw [hRdef, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_multiset_prod, Multiset.map_map]
    simp
  have hlc : p.leadingCoeff * (p.roots.map fun r => -r).prod = 1 := by
    have h := congrArg (fun q : Polynomial ℂ => q.coeff 0) hfac
    simp only [← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul, hR0, hp, mul_one] at h
    exact h
  rw [Multiset.map_map]
  calc p = Polynomial.C p.leadingCoeff * (Polynomial.C (p.roots.map fun r => -r).prod * R) := hfac.symm
    _ = R := by rw [← mul_assoc, ← Polynomial.C_mul, hlc, Polynomial.C_1, one_mul]
    _ = _ := by rw [hRdef]; rfl

/-- **Abstract zeta lemma.** -/
theorem powerSum_of_newton (a b : ℕ → ℂ) (Q : ℂ) (K : ℕ) (hK : 1 ≤ K) (ha0 : a 0 = 1)
    (hnewt : ∀ k : ℕ, ((k : ℂ) + 1) * a (k + 1) = ∑ j ∈ Finset.range (k + 1), b (j + 1) * a (k - j))
    (hrec : ∀ k : ℕ, K ≤ k + 2 → a (k + 2) + Q * a k = (1 + Q) * a (k + 1))
    (h1 : K ≤ 1 → a 1 = (1 + Q) * a 0) :
    ∃ c : Multiset ℂ, Multiset.card c ≤ K - 1 ∧
      ∀ k : ℕ, b (k + 1) = 1 + Q ^ (k + 1) - (c.map (· ^ (k + 1))).sum := by
  obtain ⟨Z, hZ⟩ : ∃ Z : PowerSeries ℂ, Z = PowerSeries.mk a := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : PowerSeries ℂ, G = PowerSeries.mk fun i => b (i + 1) := ⟨_, rfl⟩
  have hdZ : derivative ℂ Z = G * Z := by
    ext n
    rw [coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, hZ, coeff_mk]
    simp only [hG, coeff_mk]
    linear_combination hnewt n
  obtain ⟨W, hW⟩ : ∃ W : PowerSeries ℂ, W = (1 - C Q * X) * Z := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P : PowerSeries ℂ, P = (1 - C 1 * X) * W := ⟨_, rfl⟩
  have hWc : ∀ n, coeff (n + 1) W = a (n + 1) - Q * a n := by
    intro n
    rw [hW, coeff_succ_one_sub_mul, hZ, coeff_mk, coeff_mk]
  have hW0 : coeff 0 W = a 0 := by rw [hW, coeff_zero_one_sub_mul, hZ, coeff_mk]
  have hP0 : coeff 0 P = 1 := by rw [hPdef, coeff_zero_one_sub_mul, hW0, ha0]
  have hPv : ∀ n, K ≤ n → coeff n P = 0 := by
    intro n hn
    rcases n with _ | _ | k
    · omega
    · rw [hPdef, coeff_succ_one_sub_mul, hWc, hW0, h1 hn]
      ring
    · have h : a (k + 1 + 1) + Q * a k = (1 + Q) * a (k + 1) := hrec k hn
      rw [hPdef, coeff_succ_one_sub_mul, hWc, hWc]
      linear_combination h
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  set p := trunc (K' + 1) P with hpdef
  have hp : (p : PowerSeries ℂ) = P := by
    ext n
    rw [Polynomial.coeff_coe, hpdef, coeff_trunc]
    split_ifs with h
    · rfl
    · exact (hPv n (by omega)).symm
  have hpc0 : p.coeff 0 = 1 := by rw [hpdef, coeff_trunc, if_pos (Nat.succ_pos K'), hP0]
  obtain ⟨c, hcard, hpc⟩ := exists_factor p hpc0
  refine ⟨c, ?_, ?_⟩
  · rw [hcard, Nat.add_sub_cancel]
    exact Nat.lt_succ_iff.mp (natDegree_trunc_lt P K')
  have hPc : P = (c.map fun r => 1 - C r * X).prod := by
    rw [← hp, hpc, coe_prod_one_sub]
  have h2 : P = ((1 ::ₘ {Q} : Multiset ℂ).map fun r => 1 - C r * X).prod * Z := by
    rw [hPdef, hW, Multiset.map_cons, Multiset.prod_cons, Multiset.map_singleton, Multiset.prod_singleton, mul_assoc]
  have hne : P ≠ 0 := by
    intro h
    rw [h, map_zero] at hP0
    exact zero_ne_one hP0
  have hd1 : derivative ℂ P = -(P * psumSeries c) := by rw [hPc, deriv_prod]
  have hd2 : derivative ℂ P = P * (G - psumSeries (1 ::ₘ {Q})) := by
    rw [h2, Derivation.leibniz, hdZ, deriv_prod, smul_eq_mul, smul_eq_mul]
    ring
  have hGeq : G - psumSeries (1 ::ₘ {Q}) = -psumSeries c := by
    apply mul_left_cancel₀ hne
    rw [← hd2, hd1]
    ring
  intro k
  have hk := congrArg (coeff k) hGeq
  rw [map_sub, map_neg, hG, coeff_mk] at hk
  simp only [psumSeries, coeff_mk, Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons,
    Multiset.sum_singleton, one_pow] at hk
  linear_combination hk

end PS

section Concrete

open Polynomial Places RR

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

variable (Fq F) in
/-- `newton_delta` re-indexed over `range`. -/
theorem newton_delta' (k : ℕ) :
    delta Fq F * (k + 1) * numEff Fq F (delta Fq F * (k + 1)) =
      ∑ i ∈ Finset.range (k + 1), numPoints Fq F (delta Fq F * (i + 1)) * numEff Fq F (delta Fq F * (k - i)) := by
  rw [newton_delta]
  refine Finset.sum_nbij' (· - 1) (· + 1) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢
    omega
  · intro j hj
    simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    omega
  · intro j _
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    rw [show j - 1 + 1 = j by omega, show k + 1 - j = k - (j - 1) by omega]

/-- **Point counts as power sums.** With `δ = delta Fq F` and full constant field, there is a multiset
`c ⊆ ℂ` with at most `K - 1` elements such that `N_{δk} = δ (1 + q^{δk} - Σ_i c_i^k)` for all `k ≥ 1`. -/
theorem numPoints_powerSum (hk : constField Fq F = ⊥) (K : ℕ) (hK : 1 ≤ K)
    (hKg : ∀ k : ℕ, K ≤ k + 2 → 2 * (genusF Fq F : ℤ) - 1 ≤ ((delta Fq F * k : ℕ) : ℤ))
    (h1 : K ≤ 1 → numEff Fq F (delta Fq F) = 1 + Fintype.card Fq ^ delta Fq F) :
    ∃ c : Multiset ℂ, Multiset.card c ≤ K - 1 ∧ ∀ k : ℕ, 1 ≤ k →
      (numPoints Fq F (delta Fq F * k) : ℂ) =
        delta Fq F * (1 + (Fintype.card Fq : ℂ) ^ (delta Fq F * k) - (c.map (· ^ k)).sum) := by
  have hδ : (delta Fq F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (delta_pos Fq F).ne'
  obtain ⟨c, hc, hb⟩ := powerSum_of_newton (fun k => (numEff Fq F (delta Fq F * k) : ℂ))
    (fun j => (numPoints Fq F (delta Fq F * j) : ℂ) / delta Fq F) ((Fintype.card Fq : ℂ) ^ delta Fq F) K hK
    (by simp [numEff_zero])
    (by
      intro k
      have h := congrArg (Nat.cast : ℕ → ℂ) (newton_delta' Fq F k)
      push_cast at h
      rw [Finset.sum_congr rfl (fun j _ => div_mul_eq_mul_div _ _ _), ← Finset.sum_div, eq_div_iff hδ]
      linear_combination h)
    (by
      intro k hk2
      have h := congrArg (Int.cast : ℤ → ℂ) (numEff_rec hk (dvd_mul_right (delta Fq F) k) (hKg k hk2))
      push_cast at h
      rw [show delta Fq F * (k + 2) = delta Fq F * k + 2 * delta Fq F by ring,
        show delta Fq F * (k + 1) = delta Fq F * k + delta Fq F by ring]
      linear_combination h)
    (by
      intro hK1
      simp only [mul_one, mul_zero, numEff_zero, h1 hK1]
      push_cast
      ring)
  refine ⟨c, hc, fun k hk1 => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h := hb k
  rw [div_eq_iff hδ] at h
  rw [h, pow_mul]
  ring

end Concrete

end RamanujanPetersson.ZetaSB


end

-- ===== S3.HasseWeil_B =====
section

/-!
# S3-ZetaSB, O6b part B: `δ = 1`, `|α_i| ≤ √q` and the Hasse-Weil bound

For a function field `F / Fq` with full constant field (`q = #Fq`, `g = genusF Fq F`):
* `delta_eq_one`: the least positive divisor degree is `1` (F.K. Schmidt). By `numPoints_powerSum` (any `δ`),
  `δ + Q ^ k - N_{δk} = Σ_z e(z) z ^ k` with `Q = q ^ δ`, `e = δ · count_c - (δ - 1)·[z = Q]`; the two-sided bound
  `two_sided` makes this `O(√Q ^ k)` along `k ∈ D·ℕ`, so (ExpSum) the grouped coefficient at `Q` (`|Q| > √Q`)
  vanishes: `δ · a = δ - 1` with `a ∈ ℕ`, hence `δ = 1`.
* `zeta_shape`: `N_m = 1 + q ^ m - Σ_i α_i ^ m` for all `m ≥ 1`, at most `2g` numbers `α_i`, each `|α_i| ≤ √q`.
* `hasse_weil`: `|N_m - q ^ m - 1| ≤ 2 g √q ^ m` for all `m ≥ 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial Filter Asymptotics

namespace RamanujanPetersson.ZetaSB

open Places RR

section HWB

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- `A_1 = q + 1` in genus `0` (from `numEff_formula` at `n = 0, 1`). -/
theorem numEff_one_of_genus_zero (hk : constField Fq F = ⊥) (hg : genusF Fq F = 0)
    (hδ1 : delta Fq F = 1) : numEff Fq F 1 = 1 + Fintype.card Fq := by
  obtain ⟨h, hh⟩ := numEff_formula hk
  have hq1 : 1 < Fintype.card Fq := Fintype.one_lt_card
  have hq0 : ((Fintype.card Fq : ℤ) - 1) ≠ 0 := by omega
  have h0 := hh 0 (by rw [hδ1]; exact one_dvd 0) (by rw [hg]; norm_num)
  have h1 := hh 1 (by rw [hδ1]) (by rw [hg]; norm_num)
  rw [numEff_zero, hg] at h0
  rw [hg] at h1
  simp only [Nat.cast_one, mul_one, Nat.sub_zero, zero_add, pow_one] at h0
  have hfac : ((h : ℤ) - 1) * ((Fintype.card Fq : ℤ) - 1) = 0 := by linear_combination -h0
  have hh1 : (h : ℤ) = 1 := by
    rcases mul_eq_zero.mp hfac with h' | h'
    · linarith
    · exact absurd h' hq0
  have hfac2 : ((numEff Fq F 1 : ℤ) - (1 + Fintype.card Fq)) * ((Fintype.card Fq : ℤ) - 1) = 0 := by
    simp only [Nat.sub_zero] at h1
    linear_combination h1 + ((Fintype.card Fq : ℤ) ^ 2 - 1) * hh1
  rcases mul_eq_zero.mp hfac2 with h' | h'
  · have : (numEff Fq F 1 : ℤ) = 1 + Fintype.card Fq := by linarith
    exact_mod_cast this
  · exact absurd h' hq0

end HWB

end RamanujanPetersson.ZetaSB


end

-- ===== S4.Def_RP_PicDescent_A =====
section

/-!
# S4-PicDescent, part A: the divisor class group, `Pic⁰`, and the class number `h = L(1)`

* `Pic Fq F := Divisor Fq F ⧸ princ Fq F`, `degPic`, `Pic0 Fq F := ker degPic`.
* `exists_deg_one` (**F. K. Schmidt**, from S3-ZetaSB's `delta_eq_one`): with full constant field there is a
  divisor of degree `1`.
* `finite_Pic0`, `card_Pic0_eq_hcl`: `Pic⁰` is finite and its order is the number of classes of any degree
  `N ≥ 2g - 1`; `card_Pic0_mul`: `A_N (q - 1) = h (q ^ (N + 1 - g) - 1)` with `h = #Pic⁰`.
* `prod_eq_of_newton` (abstract power-series lemma) and **`classNumber_eq_prod`**: for EVERY multiset `c ⊆ ℂ` with
  `N_m = 1 + q^m - Σ_i c_i^m` for all `m ≥ 1`, `#Pic⁰(F) = Π_i (1 - c_i)`, i.e. `h = L(1)`.
* `classNumber_zeta`: the same together with S3-ZetaSB's `zeta_shape` (`#c ≤ 2g`, `‖c_i‖ ≤ √q`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.PicDescent

open Places RR ZetaSB

section PS

open PowerSeries

/-- Uniqueness for the linear differential equation `W' = W · H` over `ℂ`. -/
theorem eq_of_derivative_eq_mul (W1 W2 H : PowerSeries ℂ) (h1 : derivative ℂ W1 = W1 * H)
    (h2 : derivative ℂ W2 = W2 * H) (h0 : coeff 0 W1 = coeff 0 W2) : W1 = W2 := by
  obtain ⟨D, hD⟩ : ∃ D : PowerSeries ℂ, D = W1 - W2 := ⟨_, rfl⟩
  have hDd : derivative ℂ D = D * H := by
    rw [hD, map_sub, h1, h2]
    ring
  have hc : ∀ n, coeff n D = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | n
      · rw [hD, map_sub, h0, sub_self]
      · have h := congrArg (coeff n) hDd
        rw [coeff_derivative, coeff_mul, Finset.sum_eq_zero (fun p hp => by
          rw [ih p.1 (by have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp; omega), zero_mul])] at h
        have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
        exact (mul_eq_zero.mp h).resolve_right hn
  have : D = 0 := PowerSeries.ext fun n => by rw [hc n, map_zero]
  rw [hD] at this
  exact sub_eq_zero.mp this

theorem natDegree_prod_one_sub_le (c : Multiset ℂ) :
    (c.map fun r => 1 - Polynomial.C r * Polynomial.X).prod.natDegree ≤ Multiset.card c := by
  induction c using Multiset.induction_on with
  | empty => simp
  | cons r c ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    refine (Polynomial.natDegree_mul_le).trans ?_
    have : (1 - Polynomial.C r * Polynomial.X).natDegree ≤ 1 := by compute_degree
    omega

theorem coeff_zero_prod_one_sub (c : Multiset ℂ) :
    coeff 0 ((c.map fun r => 1 - C r * X).prod : PowerSeries ℂ) = 1 := by
  rw [← coe_prod_one_sub, Polynomial.coeff_coe, Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.eval_multiset_prod, Multiset.map_map]
  simp

/-- **Abstract class-number lemma.** Let `a 0 = 1`, `(k+1) a_{k+1} = Σ_{j ≤ k} b_{j+1} a_{k-j}` (Newton),
`b_k = 1 + Q^k - Σ_i c_i^k` for `k ≥ 1`, and `a_{n+1} - Q a_n = h` for `n ≥ M`. Then `Π_i (1 - c_i) = h`. -/
theorem prod_eq_of_newton (a b : ℕ → ℂ) (Q h : ℂ) (c : Multiset ℂ) (M : ℕ) (ha0 : a 0 = 1)
    (hnewt : ∀ k : ℕ, ((k : ℂ) + 1) * a (k + 1) = ∑ j ∈ Finset.range (k + 1), b (j + 1) * a (k - j))
    (hb : ∀ k : ℕ, b (k + 1) = 1 + Q ^ (k + 1) - (c.map (· ^ (k + 1))).sum)
    (hh : ∀ n : ℕ, M ≤ n → a (n + 1) - Q * a n = h) :
    (c.map fun z => 1 - z).prod = h := by
  obtain ⟨Z, hZ⟩ : ∃ Z : PowerSeries ℂ, Z = PowerSeries.mk a := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : PowerSeries ℂ, G = PowerSeries.mk fun i => b (i + 1) := ⟨_, rfl⟩
  have hdZ : derivative ℂ Z = G * Z := by
    ext n
    rw [coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, hZ, coeff_mk]
    simp only [hG, coeff_mk]
    linear_combination hnewt n
  have hG' : G = PowerSeries.mk (fun i => (1 : ℂ) ^ (i + 1)) + PowerSeries.mk (fun i => Q ^ (i + 1)) -
      psumSeries c := by
    ext n
    simp only [hG, psumSeries, map_add, map_sub, coeff_mk, hb, one_pow]
  obtain ⟨V, hV⟩ : ∃ V : PowerSeries ℂ, V = (1 - C Q * X) * Z := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : PowerSeries ℂ, W = (1 - C 1 * X) * V := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : PowerSeries ℂ, P = (c.map fun r => 1 - C r * X).prod := ⟨_, rfl⟩
  have hWd : derivative ℂ W = W * -psumSeries c := by
    have g1 := one_sub_mul_geom 1
    have gQ := one_sub_mul_geom Q
    rw [hW, hV, Derivation.leibniz, Derivation.leibniz, hdZ, deriv_one_sub, deriv_one_sub, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, smul_eq_mul]
    rw [hG']
    linear_combination ((1 - C Q * X) * Z) * g1 + ((1 - C 1 * X) * Z) * gQ
  have hPd : derivative ℂ P = P * -psumSeries c := by
    rw [hP, deriv_prod]
    ring
  have hV0 : coeff 0 V = a 0 := by rw [hV, coeff_zero_one_sub_mul, hZ, coeff_mk]
  have hW0 : coeff 0 W = 1 := by rw [hW, coeff_zero_one_sub_mul, hV0, ha0]
  have hWP : W = P := eq_of_derivative_eq_mul W P _ hWd hPd (by rw [hW0, hP, coeff_zero_prod_one_sub])
  have hVs : ∀ n, coeff (n + 1) V = a (n + 1) - Q * a n := by
    intro n
    rw [hV, coeff_succ_one_sub_mul, hZ, coeff_mk, coeff_mk]
  have hsum : ∀ n, ∑ i ∈ Finset.range (n + 1), coeff i W = coeff n V := by
    intro n
    induction n with
    | zero => rw [Finset.sum_range_one, hW, coeff_zero_one_sub_mul]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, hW, coeff_succ_one_sub_mul]
      ring
  set p : Polynomial ℂ := (c.map fun r => 1 - Polynomial.C r * Polynomial.X).prod with hpdef
  have hpP : (p : PowerSeries ℂ) = P := by rw [hpdef, coe_prod_one_sub, hP]
  have hev : (c.map fun z => 1 - z).prod = p.eval 1 := by
    rw [hpdef, Polynomial.eval_multiset_prod, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun r _ => ?_
    simp
  set N := M + Multiset.card c with hN
  have hlt : p.natDegree < N + 1 + 1 := by
    have := natDegree_prod_one_sub_le c
    rw [← hpdef] at this
    omega
  rw [hev, Polynomial.eval_eq_sum_range' hlt]
  have hcoef : ∀ i, p.coeff i * (1 : ℂ) ^ i = coeff i W := by
    intro i
    rw [one_pow, mul_one, hWP, ← hpP, Polynomial.coeff_coe]
  rw [Finset.sum_congr rfl fun i _ => hcoef i, hsum, hVs]
  exact hh N (by omega)

end PS

section Pic

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- The divisor class group `Pic(F) = Div(F) / Princ(F)`. -/
abbrev Pic : Type _ := Divisor Fq F ⧸ princ Fq F

/-- The degree of a divisor class. -/
noncomputable def degPic : Pic Fq F →+ ℤ :=
  QuotientAddGroup.lift (princ Fq F) (degHom Fq F) (by
    rintro _ ⟨f, hf, rfl⟩
    rw [AddMonoidHom.mem_ker]
    exact deg_div hf)

theorem degPic_mk (D : Divisor Fq F) : degPic Fq F (QuotientAddGroup.mk D) = Divisor.deg D := rfl

/-- `Pic⁰(F)`: the divisor classes of degree `0`. -/
noncomputable def Pic0 : AddSubgroup (Pic Fq F) := (degPic Fq F).ker

theorem mem_Pic0 {x : Pic Fq F} : x ∈ Pic0 Fq F ↔ degPic Fq F x = 0 := AddMonoidHom.mem_ker

variable {Fq F}

end Pic

end RamanujanPetersson.PicDescent


end

-- ===== S4.Def_RP_PicDescent_B1 =====
section

/-!
# S4-PicDescent, part B1: coordinates for the constant field extension `L(x) / Fq(x)`

`L / Fq` a finite field extension with an `Fq`-basis `c`.
* `polyCoord c P j ∈ Fq[X]`: the coordinate polynomials of `P ∈ L[X]`, `Σ_j P_j c_j = P`, `deg P_j ≤ deg P`.
* `exists_map_dvd`: every nonzero `q ∈ L[X]` divides a nonzero `d ∈ Fq[X]` (`L[X]` is integral over `Fq[X]`).
* `ratMap : Fq(x) →+* L(x)`, `ratMap_mem_Oinf` (it maps `O_∞(Fq)` into `O_∞(L)`).
* `exists_Oinf_coord`: every `a ∈ O_∞(L)` is `Σ_j g_j c_j` with `g_j ∈ O_∞(Fq)`, i.e. `O_∞(L) = L ⊗ O_∞(Fq)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.PicDescent

open Places Polynomial

section Coord

theorem alg_ne_zero {K : Type*} [Field K] {p : K[X]} (hp : p ≠ 0) :
    algebraMap K[X] (RatFunc K) p ≠ 0 := by
  rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))]

theorem intDegree_div_poly {K : Type*} [Field K] {p d : K[X]} (hp : p ≠ 0) (hd : d ≠ 0) :
    (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) d).intDegree =
      (p.natDegree : ℤ) - d.natDegree := by
  rw [RatFunc.intDegree_div (alg_ne_zero hp) (alg_ne_zero hd), RatFunc.intDegree_polynomial,
    RatFunc.intDegree_polynomial]

theorem mem_Oinf_div {K : Type*} [Field K] [DecidableEq (RatFunc K)] {p d : K[X]} (hd : d ≠ 0)
    (h : p.natDegree ≤ d.natDegree) :
    algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) d ∈ Oinf K := by
  by_cases hp : p = 0
  · rw [hp, map_zero, zero_div]; exact zero_mem _
  rw [mem_Oinf_iff' K (div_ne_zero (alg_ne_zero hp) (alg_ne_zero hd)), intDegree_div_poly hp hd]
  omega

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {L : Type*} [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable {ι : Type*} [Fintype ι]

/-- The `j`-th coordinate polynomial of `P ∈ L[X]` for an `Fq`-basis `c` of `L`. -/
noncomputable def polyCoord (c : Module.Basis ι Fq L) (P : L[X]) (j : ι) : Fq[X] :=
  P.sum fun i a => monomial i (c.repr a j)

theorem coeff_polyCoord (c : Module.Basis ι Fq L) (P : L[X]) (j : ι) (i : ℕ) :
    (polyCoord c P j).coeff i = c.repr (P.coeff i) j := by
  simp only [polyCoord, Polynomial.sum_def, finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq',
    mem_support_iff]
  split_ifs with h
  · rfl
  · have h0 : P.coeff i = 0 := by simpa using h
    rw [h0, map_zero, Finsupp.zero_apply]

theorem natDegree_polyCoord_le (c : Module.Basis ι Fq L) (P : L[X]) (j : ι) :
    (polyCoord c P j).natDegree ≤ P.natDegree :=
  natDegree_le_iff_coeff_eq_zero.mpr fun i hi => by
    rw [coeff_polyCoord, coeff_eq_zero_of_natDegree_lt hi, map_zero, Finsupp.zero_apply]

theorem sum_polyCoord (c : Module.Basis ι Fq L) (P : L[X]) :
    ∑ j, (polyCoord c P j).map (algebraMap Fq L) * C (c j) = P := by
  ext i
  simp only [finsetSum_coeff, coeff_mul_C, coeff_map, coeff_polyCoord]
  simp_rw [← Algebra.smul_def]
  exact c.sum_repr (P.coeff i)

/-- Every nonzero `q ∈ L[X]` divides some nonzero `d ∈ Fq[X]`. -/
theorem exists_map_dvd {q : L[X]} (hq : q ≠ 0) :
    ∃ d : Fq[X], d ≠ 0 ∧ q ∣ d.map (algebraMap Fq L) := by
  let _ : Algebra Fq[X] L[X] := Polynomial.algebra Fq L
  have : Module.Finite Fq L := Module.Finite.of_finite
  have hint : IsIntegral Fq[X] q :=
    Polynomial.isIntegral_iff_isIntegral_coeff.mpr fun n => Algebra.IsIntegral.isIntegral _
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Ideal.comap_ne_bot_of_integral_mem hq (Ideal.mem_span_singleton_self q) hint)
  exact ⟨d, hd0, Ideal.mem_span_singleton.mp (Ideal.mem_comap.mp hd)⟩

variable (Fq L) in
/-- The ring map `Fq(x) → L(x)`. -/
noncomputable def ratMap : RatFunc Fq →+* RatFunc L :=
  RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap Fq L))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective _ (algebraMap Fq L).injective))

theorem ratMap_div (p d : Fq[X]) :
    ratMap Fq L (algebraMap Fq[X] (RatFunc Fq) p / algebraMap Fq[X] (RatFunc Fq) d) =
      algebraMap L[X] (RatFunc L) (p.map (algebraMap Fq L)) /
        algebraMap L[X] (RatFunc L) (d.map (algebraMap Fq L)) :=
  RatFunc.map_apply_div _ (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (Polynomial.map_injective _ (algebraMap Fq L).injective)) p d

theorem ratMap_algebraMap (p : Fq[X]) :
    ratMap Fq L (algebraMap Fq[X] (RatFunc Fq) p) = algebraMap L[X] (RatFunc L) (p.map (algebraMap Fq L)) := by
  have h := ratMap_div (L := L) p 1
  rwa [map_one, div_one, Polynomial.map_one, map_one, div_one] at h

theorem ratMap_mem_Oinf {g : RatFunc Fq} (hg : g ∈ Oinf Fq) : ratMap Fq L g ∈ Oinf L := by
  by_cases h0 : g = 0
  · rw [h0, map_zero]; exact zero_mem _
  have hdeg : g.intDegree ≤ 0 := (mem_Oinf_iff' Fq h0).mp hg
  have e := RatFunc.num_div_denom g
  rw [← e, ratMap_div]
  apply mem_Oinf_div ((Polynomial.map_ne_zero_iff (algebraMap Fq L).injective).mpr (RatFunc.denom_ne_zero g))
  rw [natDegree_map, natDegree_map]
  unfold RatFunc.intDegree at hdeg
  omega

/-- `O_∞(L) = L ⊗ O_∞(Fq)` in coordinates. -/
theorem exists_Oinf_coord (c : Module.Basis ι Fq L) {a : RatFunc L} (ha : a ∈ Oinf L) :
    ∃ g : ι → RatFunc Fq, (∀ j, g j ∈ Oinf Fq) ∧
      a = ∑ j, ratMap Fq L (g j) * algebraMap L (RatFunc L) (c j) := by
  by_cases ha0 : a = 0
  · exact ⟨0, fun j => zero_mem _, by simp [ha0]⟩
  obtain ⟨d, hd0, r, hr⟩ := exists_map_dvd (Fq := Fq) (RatFunc.denom_ne_zero a)
  have hdm : d.map (algebraMap Fq L) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap Fq L).injective).mpr hd0
  have hr0 : r ≠ 0 := by rintro rfl; rw [mul_zero] at hr; exact hdm hr
  have hP0 : a.num * r ≠ 0 := mul_ne_zero (RatFunc.num_ne_zero ha0) hr0
  have haP : a = algebraMap L[X] (RatFunc L) (a.num * r) /
      algebraMap L[X] (RatFunc L) (d.map (algebraMap Fq L)) := by
    rw [hr, map_mul, map_mul, mul_div_mul_right _ _ (alg_ne_zero hr0), RatFunc.num_div_denom]
  have hdeg : (a.num * r).natDegree ≤ d.natDegree := by
    have := (mem_Oinf_iff' L ha0).mp ha
    rw [haP, intDegree_div_poly hP0 hdm, natDegree_map] at this
    omega
  refine ⟨fun j => algebraMap Fq[X] (RatFunc Fq) (polyCoord c (a.num * r) j) /
      algebraMap Fq[X] (RatFunc Fq) d,
    fun j => mem_Oinf_div hd0 ((natDegree_polyCoord_le c _ j).trans hdeg), ?_⟩
  conv_lhs => rw [haP, ← sum_polyCoord c (a.num * r)]
  rw [map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ratMap_div, map_mul, div_mul_eq_mul_div, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]

end Coord

end RamanujanPetersson.PicDescent


end

-- ===== S4.Def_RP_PicDescent_B2 =====
section

/-!
# S4-PicDescent, part B2: a generic constant field extension in coordinates

Setting of `RR.IsConstExt`: `F / Fq` a function field with full constant field (`constField Fq F = ⊥`),
`L / Fq` a finite extension with a power basis `pb`, and `F' / L` a function field with compatible maps
`F → F'`, `L → F'`, the same separating element (`hx`) and `[F' : F] = [L : Fq]` (`hdim`).
* `compat_poly`, `compat_rat`: the maps `Fq[x] → L[x] → F'` and `Fq(x) → L(x) → F'` factor through `F`.
* `natDegree_minpoly`: the image `α'` of `pb.gen` keeps its degree over `F` (coefficients of a factor of
  `μ` are algebraic over `Fq`, hence constants).
* `basisF`: the images of `pb.basis` form an `F`-basis of `F'`; `trace_algebraMap_L`:
  `Tr_{F'/F} (a) = Tr_{L/Fq} (a)` for `a ∈ L`.
* `coord_eq_trace`: coordinates are traces against the trace-dual basis `dualB pb`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.PicDescent

open Places Polynomial RR

section Compat

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F]
variable {L : Type*} [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable {F' : Type*} [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F']
variable [Algebra F F'] [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']

theorem compat_poly_hom (hx : algebraMap F F' (xF Fq F) = xF L F') :
    (algebraMap L[X] F').comp (mapRingHom (algebraMap Fq L)) =
      (algebraMap F F').comp (algebraMap Fq[X] F) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · have e1 : algebraMap L[X] F' (C (algebraMap Fq L a)) = algebraMap Fq F' a := by
      rw [IsScalarTower.algebraMap_apply Fq L F']
      exact (IsScalarTower.algebraMap_apply L L[X] F' _).symm
    have e2 : algebraMap Fq[X] F (C a) = algebraMap Fq F a :=
      (IsScalarTower.algebraMap_apply Fq Fq[X] F a).symm
    simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_C]
    rw [e1, e2, ← IsScalarTower.algebraMap_apply Fq F F']
  · simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_X]
    exact hx.symm

theorem compat_poly (hx : algebraMap F F' (xF Fq F) = xF L F') (p : Fq[X]) :
    algebraMap L[X] F' (p.map (algebraMap Fq L)) = algebraMap F F' (algebraMap Fq[X] F p) :=
  RingHom.congr_fun (compat_poly_hom hx) p

theorem compat_rat_hom (hx : algebraMap F F' (xF Fq F) = xF L F') :
    (algebraMap (RatFunc L) F').comp (ratMap Fq L) = (algebraMap F F').comp (algebraMap (RatFunc Fq) F) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors Fq[X]) (RingHom.ext fun p => ?_)
  simp only [RingHom.comp_apply]
  rw [ratMap_algebraMap, ← IsScalarTower.algebraMap_apply L[X] (RatFunc L) F',
    ← IsScalarTower.algebraMap_apply Fq[X] (RatFunc Fq) F, compat_poly hx]

theorem compat_rat (hx : algebraMap F F' (xF Fq F) = xF L F') (g : RatFunc Fq) :
    algebraMap (RatFunc L) F' (ratMap Fq L g) = algebraMap F F' (algebraMap (RatFunc Fq) F g) :=
  RingHom.congr_fun (compat_rat_hom hx) g

end Compat

section Generic

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {L : Type*} [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable {F' : Type*} [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']
variable [Algebra F F'] [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']

variable (pb : PowerBasis Fq L)

/-- The generator keeps its degree over `F` when `F` has full constant field. -/
theorem natDegree_minpoly (hk : constField Fq F = ⊥) :
    (minpoly F (algebraMap L F' pb.gen)).natDegree = pb.dim := by
  have hint : IsIntegral Fq pb.gen := pb.isIntegral_gen
  have hμ : (minpoly Fq pb.gen).Monic := minpoly.monic hint
  have hα : IsIntegral F (algebraMap L F' pb.gen) := (hint.algebraMap (B := F')).tower_top
  have hdvd : minpoly F (algebraMap L F' pb.gen) ∣ (minpoly Fq pb.gen).map (algebraMap Fq F) := by
    refine minpoly.dvd F _ ?_
    rw [aeval_map_algebraMap, aeval_algebraMap_apply, minpoly.aeval, map_zero]
  have hcoeff : ∀ n, (minpoly F (algebraMap L F' pb.gen)).coeff n ∈ Set.range (algebraMap Fq F) := by
    intro n
    have hi := Polynomial.isIntegral_coeff_of_dvd _ _ hμ (minpoly.monic hα) hdvd n
    have hmem : (minpoly F (algebraMap L F' pb.gen)).coeff n ∈ constField Fq F :=
      mem_algebraicClosure_iff'.2 hi
    rw [hk] at hmem
    exact IntermediateField.mem_bot.1 hmem
  obtain ⟨q0, hq0, hdeg, hmon⟩ :=
    lifts_and_degree_eq_and_monic ((lifts_iff_coeff_lifts _).2 hcoeff) (minpoly.monic hα)
  have h0 : aeval pb.gen q0 = 0 := by
    apply (algebraMap L F').injective
    rw [map_zero, ← aeval_algebraMap_apply, ← aeval_map_algebraMap F, hq0, minpoly.aeval]
  have hle1 : (minpoly Fq pb.gen).natDegree ≤ q0.natDegree :=
    natDegree_le_of_dvd (minpoly.dvd Fq _ h0) hmon.ne_zero
  have hle2 : (minpoly F (algebraMap L F' pb.gen)).natDegree ≤ (minpoly Fq pb.gen).natDegree := by
    have := natDegree_le_of_dvd hdvd ((hμ.map (algebraMap Fq F)).ne_zero)
    rwa [natDegree_map] at this
  have hq : q0.natDegree = (minpoly F (algebraMap L F' pb.gen)).natDegree := natDegree_eq_of_degree_eq hdeg
  rw [← pb.natDegree_minpoly]
  omega

theorem linearIndependent_basis (hk : constField Fq F = ⊥) :
    LinearIndependent F fun j => algebraMap L F' (pb.basis j) := by
  have h := linearIndependent_pow (K := F) (algebraMap L F' pb.gen)
  have e := natDegree_minpoly (F := F) (F' := F') pb hk
  have h2 := h.comp (Fin.cast e.symm) (Fin.cast_injective _)
  convert h2 using 1
  funext j
  simp [PowerBasis.coe_basis, map_pow]

theorem span_basis (hk : constField Fq F = ⊥)
    (hdim : Module.finrank F F' = Module.finrank Fq L) :
    ⊤ ≤ Submodule.span F (Set.range fun j => algebraMap L F' (pb.basis j)) := by
  have : Nonempty (Fin pb.dim) := ⟨⟨0, pb.dim_pos⟩⟩
  have hc : Fintype.card (Fin pb.dim) = Module.finrank F F' := by
    rw [Fintype.card_fin, hdim, pb.finrank]
  exact (LinearIndependent.span_eq_top_of_card_eq_finrank
    (linearIndependent_basis (F := F) (F' := F') pb hk) hc).ge

/-- The `F`-basis of `F'` given by the images of `pb.basis`. -/
noncomputable def basisF (hk : constField Fq F = ⊥)
    (hdim : Module.finrank F F' = Module.finrank Fq L) : Module.Basis (Fin pb.dim) F F' :=
  Module.Basis.mk (linearIndependent_basis pb hk) (span_basis pb hk hdim)

theorem basisF_apply (hk : constField Fq F = ⊥) (hdim : Module.finrank F F' = Module.finrank Fq L)
    (j : Fin pb.dim) : basisF pb hk hdim j = algebraMap L F' (pb.basis j) :=
  Module.Basis.mk_apply _ _ _

include pb in
theorem finiteDimensional (hk : constField Fq F = ⊥)
    (hdim : Module.finrank F F' = Module.finrank Fq L) : FiniteDimensional F F' :=
  Module.Finite.of_basis (basisF pb hk hdim)

theorem repr_algebraMap (hk : constField Fq F = ⊥) (hdim : Module.finrank F F' = Module.finrank Fq L)
    (x : L) (k : Fin pb.dim) :
    (basisF pb hk hdim).repr (algebraMap L F' x) k = algebraMap Fq F (pb.basis.repr x k) := by
  have h : algebraMap L F' (∑ i, pb.basis.repr x i • pb.basis i) =
      ∑ i, algebraMap Fq F (pb.basis.repr x i) • basisF pb hk hdim i := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, basisF_apply,
      ← IsScalarTower.algebraMap_apply Fq L F', ← IsScalarTower.algebraMap_apply Fq F F']
  conv_lhs => rw [← pb.basis.sum_repr x]
  rw [h, Module.Basis.repr_sum_self]

include pb in
/-- `Tr_{F'/F} (a) = Tr_{L/Fq} (a)` for `a ∈ L`. -/
theorem trace_algebraMap_L (hk : constField Fq F = ⊥)
    (hdim : Module.finrank F F' = Module.finrank Fq L) (a : L) :
    Algebra.trace F F' (algebraMap L F' a) = algebraMap Fq F (Algebra.trace Fq L a) := by
  classical
  rw [Algebra.trace_eq_matrix_trace (basisF pb hk hdim), Algebra.trace_eq_matrix_trace pb.basis,
    Matrix.trace, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, basisF_apply, ← map_mul, repr_algebraMap]

/-- The trace-dual basis of `pb.basis`. -/
noncomputable def dualB : Module.Basis (Fin pb.dim) Fq L :=
  haveI := pb.finite
  (Algebra.traceForm Fq L).dualBasis (traceForm_nondegenerate Fq L) pb.basis

theorem trace_dualB (i j : Fin pb.dim) :
    Algebra.trace Fq L (dualB pb i * pb.basis j) = if j = i then 1 else 0 := by
  have := pb.finite
  have h := (Algebra.traceForm Fq L).apply_dualBasis_left (traceForm_nondegenerate Fq L) pb.basis i j
  rwa [Algebra.traceForm_apply] at h

/-- Coordinates are traces against the dual basis. -/
theorem coord_eq_trace (hk : constField Fq F = ⊥)
    (hdim : Module.finrank F F' = Module.finrank Fq L) (f : Fin pb.dim → F) (k : Fin pb.dim) :
    f k = Algebra.trace F F'
      ((∑ j, f j • algebraMap L F' (pb.basis j)) * algebraMap L F' (dualB pb k)) := by
  have h : ∀ j, Algebra.trace F F' (f j • algebraMap L F' (pb.basis j) * algebraMap L F' (dualB pb k)) =
      if j = k then f k else 0 := by
    intro j
    rw [smul_mul_assoc, map_smul, ← map_mul, trace_algebraMap_L pb hk hdim, mul_comm, trace_dualB,
      smul_eq_mul]
    split_ifs with hjk
    · rw [hjk, map_one, mul_one]
    · rw [map_zero, mul_zero]
  rw [Finset.sum_mul, map_sum]
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Generic

end RamanujanPetersson.PicDescent


end

-- ===== S4.Def_RP_PicDescent_B3 =====
section

/-!
# S4-PicDescent, part B3: the generic constant field extension is an `RR.IsConstExt`

In the setting of part B2 (`hk : constField Fq F = ⊥`, `hdim : [F' : F] = [L : Fq]`, same `x`):
* `isIntegral_Rfin_poly`, `isIntegral_Rinf_Oinf`: `L[x]` and `O_∞(L)` are integral over the rings `Rfin`,
  `Rinf` of `F` inside `F'`;
* `fin_iff`, `inf_iff`: an element `Σ f_j c_j` is integral over `L[x]` (resp. `O_∞(L)`) iff every `f_j` is
  integral over `Fq[x]` (resp. `O_∞(Fq)`) (trace-dual coordinates, `Algebra.isIntegral_trace`);
* `isConstExt`: hence `RR.IsConstExt Fq F L F' pb.basis`; `genusF_eq`, `constField_eq_bot`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.PicDescent

open Places Polynomial RR

/-- Integrality over `R` through an intermediate ring `A` whose image is integral over `R`. -/
theorem isIntegral_of_forall_algebraMap {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R B] [Algebra A B] (h : ∀ a : A, IsIntegral R (algebraMap A B a)) {z : B}
    (hz : IsIntegral A z) : IsIntegral R z := by
  let φ : A →+* integralClosure R B := (algebraMap A B).codRestrict (integralClosure R B) h
  have h1 : IsIntegral (integralClosure R B) (RingHom.id B z) :=
    hz.map_of_comp_eq φ (RingHom.id B) (RingHom.ext fun _ => rfl)
  exact isIntegral_trans z h1

section Generic

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {L : Type*} [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable {F' : Type*} [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']
variable [Algebra F F'] [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']

/-- Elements of `L` are integral over any subring `R` of `F` containing `Fq`. -/
theorem isIntegral_L {R : Type*} [CommRing R] [Algebra R F] [Algebra R F'] [IsScalarTower R F F']
    (φ : Fq →+* R) (hφ : ∀ r, algebraMap R F (φ r) = algebraMap Fq F r) (a : L) :
    IsIntegral R (algebraMap L F' a) := by
  refine (Algebra.IsIntegral.isIntegral (R := Fq) a).map_of_comp_eq φ (algebraMap L F')
    (RingHom.ext fun r => ?_)
  simp only [RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply R F F', hφ, ← IsScalarTower.algebraMap_apply Fq F F',
    ← IsScalarTower.algebraMap_apply Fq L F']

theorem isIntegral_Rfin_L (a : L) : IsIntegral (Rfin Fq F) (algebraMap L F' a) :=
  isIntegral_L ((algebraMap Fq[X] (Rfin Fq F)).comp (algebraMap Fq Fq[X]))
    (fun r => (IsScalarTower.algebraMap_apply Fq[X] (Rfin Fq F) F _).symm.trans
      (IsScalarTower.algebraMap_apply Fq Fq[X] F r).symm) a

theorem isIntegral_Rinf_L (a : L) : IsIntegral (Rinf Fq F) (algebraMap L F' a) :=
  isIntegral_L ((algebraMap (Oinf Fq) (Rinf Fq F)).comp (algebraMap Fq (Oinf Fq)))
    (fun r => (IsScalarTower.algebraMap_apply (Oinf Fq) (Rinf Fq F) F _).symm.trans
      (IsScalarTower.algebraMap_apply Fq (Oinf Fq) F r).symm) a

theorem isIntegral_Rfin_poly (hx : algebraMap F F' (xF Fq F) = xF L F') (p : L[X]) :
    IsIntegral (Rfin Fq F) (algebraMap L[X] F' p) := by
  have hX : IsIntegral (Rfin Fq F) (algebraMap L[X] F' X) := by
    change IsIntegral _ (xF L F')
    rw [← hx]
    have hm : xF Fq F ∈ integralClosure Fq[X] F := isIntegral_algebraMap
    exact isIntegral_algebraMap (R := Rfin Fq F) (A := F') (x := ⟨xF Fq F, hm⟩)
  rw [p.as_sum_range_C_mul_X_pow, map_sum]
  refine IsIntegral.sum _ fun i _ => ?_
  have e : algebraMap L[X] F' (C (p.coeff i)) = algebraMap L F' (p.coeff i) :=
    (IsScalarTower.algebraMap_apply L L[X] F' _).symm
  rw [map_mul, map_pow, e]
  exact (isIntegral_Rfin_L _).mul (hX.pow _)

theorem isIntegral_Rinf_Oinf (pb : PowerBasis Fq L) (hx : algebraMap F F' (xF Fq F) = xF L F')
    (a : Oinf L) : IsIntegral (Rinf Fq F) (algebraMap (Oinf L) F' a) := by
  obtain ⟨g, hg, ha⟩ := exists_Oinf_coord pb.basis a.2
  rw [IsScalarTower.algebraMap_apply (Oinf L) (RatFunc L) F']
  change IsIntegral _ (algebraMap (RatFunc L) F' (a : RatFunc L))
  rw [ha, map_sum]
  refine IsIntegral.sum _ fun j _ => ?_
  rw [map_mul, compat_rat hx, ← IsScalarTower.algebraMap_apply L (RatFunc L) F']
  refine IsIntegral.mul ?_ (isIntegral_Rinf_L _)
  have hm : algebraMap (RatFunc Fq) F (g j) ∈ integralClosure (Oinf Fq) F := by
    have e : algebraMap (RatFunc Fq) F (g j) = algebraMap (Oinf Fq) F ⟨g j, hg j⟩ :=
      IsScalarTower.algebraMap_apply (Oinf Fq) (RatFunc Fq) F ⟨g j, hg j⟩
    rw [e]; exact isIntegral_algebraMap
  exact isIntegral_algebraMap (R := Rinf Fq F) (A := F') (x := ⟨_, hm⟩)

variable (pb : PowerBasis Fq L)

theorem fin_iff (hk : constField Fq F = ⊥) (hdim : Module.finrank F F' = Module.finrank Fq L)
    (hx : algebraMap F F' (xF Fq F) = xF L F') (f : Fin pb.dim → F) :
    (∑ j, f j • algebraMap L F' (pb.basis j)) ∈ (algebraMap (Rfin L F') F').range ↔
      ∀ j, f j ∈ (algebraMap (Rfin Fq F) F).range := by
  have := finiteDimensional pb hk hdim
  constructor
  · rintro ⟨z, hz⟩ k
    have hzi : IsIntegral L[X] (∑ j, f j • algebraMap L F' (pb.basis j)) := by rw [← hz]; exact z.2
    have h1 : IsIntegral (Rfin Fq F)
        ((∑ j, f j • algebraMap L F' (pb.basis j)) * algebraMap L F' (dualB pb k)) :=
      (isIntegral_of_forall_algebraMap (isIntegral_Rfin_poly hx) hzi).mul (isIntegral_Rfin_L _)
    have h2 := Algebra.isIntegral_trace (L := F) h1
    rw [← coord_eq_trace pb hk hdim f k] at h2
    exact ⟨⟨f k, isIntegral_trans (f k) h2⟩, rfl⟩
  · intro h
    have hi : IsIntegral L[X] (∑ j, f j • algebraMap L F' (pb.basis j)) := by
      refine IsIntegral.sum _ fun j _ => ?_
      obtain ⟨r, hr⟩ := h j
      rw [Algebra.smul_def, ← hr]
      refine IsIntegral.mul ?_ ?_
      · exact (r.2 : IsIntegral Fq[X] (r : F)).map_of_comp_eq (mapRingHom (algebraMap Fq L))
          (algebraMap F F') (compat_poly_hom hx)
      · rw [IsScalarTower.algebraMap_apply L L[X] F']; exact isIntegral_algebraMap
    exact ⟨⟨_, hi⟩, rfl⟩

theorem inf_iff (hk : constField Fq F = ⊥) (hdim : Module.finrank F F' = Module.finrank Fq L)
    (hx : algebraMap F F' (xF Fq F) = xF L F') (f : Fin pb.dim → F) :
    (∑ j, f j • algebraMap L F' (pb.basis j)) ∈ (algebraMap (Rinf L F') F').range ↔
      ∀ j, f j ∈ (algebraMap (Rinf Fq F) F).range := by
  have := finiteDimensional pb hk hdim
  constructor
  · rintro ⟨z, hz⟩ k
    have hzi : IsIntegral (Oinf L) (∑ j, f j • algebraMap L F' (pb.basis j)) := by rw [← hz]; exact z.2
    have h1 : IsIntegral (Rinf Fq F)
        ((∑ j, f j • algebraMap L F' (pb.basis j)) * algebraMap L F' (dualB pb k)) :=
      (isIntegral_of_forall_algebraMap (isIntegral_Rinf_Oinf pb hx) hzi).mul (isIntegral_Rinf_L _)
    have h2 := Algebra.isIntegral_trace (L := F) h1
    rw [← coord_eq_trace pb hk hdim f k] at h2
    exact ⟨⟨f k, isIntegral_trans (f k) h2⟩, rfl⟩
  · intro h
    let φ : Oinf Fq →+* Oinf L :=
      (ratMap Fq L).restrict (Oinf Fq) (Oinf L) fun _ hg => ratMap_mem_Oinf hg
    have hφ : (algebraMap (Oinf L) F').comp φ = (algebraMap F F').comp (algebraMap (Oinf Fq) F) := by
      refine RingHom.ext fun g => ?_
      simp only [RingHom.comp_apply]
      rw [IsScalarTower.algebraMap_apply (Oinf L) (RatFunc L) F',
        IsScalarTower.algebraMap_apply (Oinf Fq) (RatFunc Fq) F]
      exact compat_rat hx g
    have hi : IsIntegral (Oinf L) (∑ j, f j • algebraMap L F' (pb.basis j)) := by
      refine IsIntegral.sum _ fun j _ => ?_
      obtain ⟨r, hr⟩ := h j
      rw [Algebra.smul_def, ← hr]
      refine IsIntegral.mul ?_ ?_
      · exact (r.2 : IsIntegral (Oinf Fq) (r : F)).map_of_comp_eq φ (algebraMap F F') hφ
      · have e : algebraMap L F' (pb.basis j) =
            algebraMap (Oinf L) F' ⟨_, algebraMap_mem_Oinf L (pb.basis j)⟩ := by
          rw [IsScalarTower.algebraMap_apply (Oinf L) (RatFunc L) F']
          exact IsScalarTower.algebraMap_apply L (RatFunc L) F' _
        rw [e]; exact isIntegral_algebraMap
    exact ⟨⟨_, hi⟩, rfl⟩

/-- **The constant field extension in coordinates.** -/
theorem isConstExt (hk : constField Fq F = ⊥) (hdim : Module.finrank F F' = Module.finrank Fq L)
    (hx : algebraMap F F' (xF Fq F) = xF L F') : IsConstExt Fq F L F' pb.basis where
  linearIndependent := linearIndependent_basis pb hk
  span := span_basis pb hk hdim
  xF_eq := hx
  fin := fin_iff pb hk hdim hx
  inf := inf_iff pb hk hdim hx

include pb in
theorem constField_eq_bot (hk : constField Fq F = ⊥) (hdim : Module.finrank F F' = Module.finrank Fq L)
    (hx : algebraMap F F' (xF Fq F) = xF L F') : constField L F' = ⊥ :=
  (isConstExt pb hk hdim hx).constField_eq_bot hk

end Generic

end RamanujanPetersson.PicDescent


end

-- ===== S4.Def_RP_PicDescent_B4 =====
section

/-!
# S4-PicDescent, part B4a: the finite fields `L_n` inside an ambient field

`Ω` any field over the finite field `Fq` (`q = #Fq`).
* `frobPow Fq Ω n`: the `n`-th power of the arithmetic (`q`-power) Frobenius, `x ↦ x ^ q ^ n`.
* `Lc Fq Ω n`: its fixed field `{x | x ^ q ^ n = x}`; finite for `n ≠ 0`; when `Ω` is algebraically closed it has
  `q ^ n` elements and `[L_n : Fq] = n`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.PicDescent

open Polynomial

section Frob

variable (Fq : Type*) [Field Fq] [Fintype Fq] (Ω : Type*) [Field Ω] [Algebra Fq Ω]

/-- The `n`-th power of the arithmetic (`q`-power) Frobenius of `Ω` over `Fq`. -/
noncomputable def frobPow (n : ℕ) : Ω →ₐ[Fq] Ω := FiniteField.frobeniusAlgHom Fq Ω ^ n

theorem frobPow_apply (n : ℕ) (x : Ω) : frobPow Fq Ω n x = x ^ Fintype.card Fq ^ n := by
  induction n generalizing x with
  | zero => simp [frobPow]
  | succ n ih =>
    rw [frobPow, pow_succ, AlgHom.mul_apply, ← frobPow, ih, FiniteField.frobeniusAlgHom_apply,
      ← pow_mul, pow_succ']

/-- `L_n`: the fixed field of the `q ^ n`-Frobenius. -/
noncomputable def Lc (n : ℕ) : IntermediateField Fq Ω :=
  Subalgebra.toIntermediateField (AlgHom.equalizer (frobPow Fq Ω n) (AlgHom.id Fq Ω)) fun x hx => by
    rw [AlgHom.mem_equalizer, frobPow_apply, AlgHom.id_apply] at hx ⊢
    rw [inv_pow, hx]

variable {Fq Ω} in
theorem mem_Lc {n : ℕ} {x : Ω} : x ∈ Lc Fq Ω n ↔ x ^ Fintype.card Fq ^ n = x := by
  show x ∈ AlgHom.equalizer (frobPow Fq Ω n) (AlgHom.id Fq Ω) ↔ _
  rw [AlgHom.mem_equalizer, frobPow_apply, AlgHom.id_apply]

/-- `X ^ q ^ n - X`. -/
noncomputable def galPoly (n : ℕ) : Fq[X] := X ^ Fintype.card Fq ^ n - X

theorem natDegree_galPoly {n : ℕ} (hn : n ≠ 0) :
    (galPoly Fq n).natDegree = Fintype.card Fq ^ n :=
  FiniteField.X_pow_card_pow_sub_X_natDegree_eq Fq hn Fintype.one_lt_card

theorem galPoly_ne_zero {n : ℕ} (hn : n ≠ 0) : galPoly Fq n ≠ 0 := by
  intro h
  have := natDegree_galPoly Fq hn
  rw [h, natDegree_zero] at this
  exact (pow_pos Fintype.card_pos n).ne this

theorem galPoly_separable {n : ℕ} (hn : n ≠ 0) : (galPoly Fq n).Separable := by
  have h : ((Fintype.card Fq ^ n : ℕ) : Fq) = 0 := by
    rw [Nat.cast_pow, FiniteField.cast_card_eq_zero, zero_pow hn]
  exact galois_poly_separable (ringChar Fq) _ (ringChar.dvd h)

theorem mem_Lc_iff_rootSet {n : ℕ} (hn : n ≠ 0) {x : Ω} :
    x ∈ Lc Fq Ω n ↔ x ∈ (galPoly Fq n).rootSet Ω := by
  rw [mem_Lc, mem_rootSet]
  have e : aeval x (galPoly Fq n) = x ^ Fintype.card Fq ^ n - x := by
    rw [galPoly, map_sub, map_pow, aeval_X]
  rw [e, sub_eq_zero]
  exact ⟨fun h => ⟨galPoly_ne_zero Fq hn, h⟩, fun h => h.2⟩

instance finite_Lc (n : ℕ) [NeZero n] : Finite (Lc Fq Ω n) := by
  have : (Lc Fq Ω n : Set Ω) ⊆ (galPoly Fq n).rootSet Ω := fun x hx =>
    (mem_Lc_iff_rootSet Fq Ω (NeZero.ne n)).1 hx
  exact (((galPoly Fq n).rootSet_finite Ω).subset this).to_subtype

noncomputable instance fintype_Lc (n : ℕ) [NeZero n] : Fintype (Lc Fq Ω n) := Fintype.ofFinite _

theorem card_Lc [IsAlgClosed Ω] {n : ℕ} (hn : n ≠ 0) :
    Nat.card (Lc Fq Ω n) = Fintype.card Fq ^ n := by
  classical
  have e : (Lc Fq Ω n : Set Ω) = (galPoly Fq n).rootSet Ω :=
    Set.ext fun x => mem_Lc_iff_rootSet Fq Ω hn
  have hc := card_rootSet_eq_natDegree (K := Ω) (galPoly_separable Fq hn) (IsAlgClosed.splits _)
  rw [natDegree_galPoly Fq hn] at hc
  rw [← hc, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.setCongr e)

theorem finrank_Lc [IsAlgClosed Ω] {n : ℕ} (hn : n ≠ 0) : Module.finrank Fq (Lc Fq Ω n) = n := by
  have : NeZero n := ⟨hn⟩
  have h1 := Module.card_eq_pow_finrank (K := Fq) (V := Lc Fq Ω n)
  rw [Fintype.card_eq_nat_card, card_Lc Fq Ω hn] at h1
  exact (Nat.pow_right_injective Fintype.one_lt_card h1).symm

variable {Fq Ω} in
theorem isSeparable_of_mem_Lc {n : ℕ} [NeZero n] {x : Ω} (hx : x ∈ Lc Fq Ω n) : IsSeparable Fq x := by
  have hr := (mem_Lc_iff_rootSet Fq Ω (NeZero.ne n)).1 hx
  rw [mem_rootSet] at hr
  exact (galPoly_separable Fq (NeZero.ne n)).of_dvd (minpoly.dvd Fq x hr.2)

/-- A power basis of `L_n` over `Fq`. -/
noncomputable def pbL (n : ℕ) [NeZero n] : PowerBasis Fq (Lc Fq Ω n) :=
  Field.powerBasisOfFiniteOfSeparable Fq (Lc Fq Ω n)

end Frob

section Ext

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]

/-- `F_n = F · L_n` inside `Ω`: the constant field extension of degree `n`. -/
noncomputable def Fc (n : ℕ) : IntermediateField F Ω := IntermediateField.adjoin F (Lc Fq Ω n : Set Ω)

variable {Fq F Ω} in
theorem mem_Fc_of_mem_Lc {n : ℕ} {x : Ω} (hx : x ∈ Lc Fq Ω n) : x ∈ Fc Fq F Ω n :=
  IntermediateField.subset_adjoin F _ hx

/-- The inclusion `L_n → F_n`. -/
noncomputable def LtoF (n : ℕ) : Lc Fq Ω n →+* Fc Fq F Ω n where
  toFun x := ⟨x, mem_Fc_of_mem_Lc x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable instance algebra_LF (n : ℕ) : Algebra (Lc Fq Ω n) (Fc Fq F Ω n) :=
  (LtoF Fq F Ω n).toAlgebra

theorem coe_algebraMap_LF {n : ℕ} (x : Lc Fq Ω n) :
    ((algebraMap (Lc Fq Ω n) (Fc Fq F Ω n) x : Fc Fq F Ω n) : Ω) = x := rfl

instance isScalarTower_LF (n : ℕ) : IsScalarTower Fq (Lc Fq Ω n) (Fc Fq F Ω n) :=
  IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl

instance finiteDimensional_Fc (n : ℕ) [NeZero n] : FiniteDimensional F (Fc Fq F Ω n) := by
  have : Finite (Lc Fq Ω n : Set Ω) := finite_Lc Fq Ω n
  exact IntermediateField.finiteDimensional_adjoin fun x hx =>
    ((isSeparable_of_mem_Lc hx).tower_top F).isIntegral

instance isSeparable_Fc (n : ℕ) [NeZero n] : Algebra.IsSeparable F (Fc Fq F Ω n) :=
  (IntermediateField.isSeparable_adjoin_iff_isSeparable F Ω).2 fun _ hx =>
    (isSeparable_of_mem_Lc hx).tower_top F

theorem Fc_eq_adjoin (n : ℕ) [NeZero n] :
    Fc Fq F Ω n = IntermediateField.adjoin F {((pbL Fq Ω n).gen : Ω)} := by
  apply le_antisymm
  · rw [Fc, IntermediateField.adjoin_le_iff]
    intro y hy
    obtain ⟨f, -, hf⟩ := (pbL Fq Ω n).exists_eq_aeval ⟨y, hy⟩
    have hy' : y = aeval ((pbL Fq Ω n).gen : Ω) f := by
      have := congrArg (Lc Fq Ω n).val hf
      rw [← Polynomial.aeval_algHom_apply] at this
      exact this
    have h2 : aeval ((pbL Fq Ω n).gen : Ω) (f.map (algebraMap Fq F)) ∈
        IntermediateField.adjoin F {((pbL Fq Ω n).gen : Ω)} :=
      IntermediateField.algebra_adjoin_le_adjoin F _ (Polynomial.aeval_mem_adjoin_singleton F _)
    rw [Polynomial.aeval_map_algebraMap] at h2
    rw [hy']
    exact h2
  · exact IntermediateField.adjoin_simple_le_iff.2 (mem_Fc_of_mem_Lc (pbL Fq Ω n).gen.2)

section FF

variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- The separating element `x` of `F`, inside `F_n`. -/
noncomputable def xc (n : ℕ) : Fc Fq F Ω n := algebraMap F (Fc Fq F Ω n) (RR.xF Fq F)

noncomputable instance algebra_polyF (n : ℕ) : Algebra (Lc Fq Ω n)[X] (Fc Fq F Ω n) :=
  (aeval (xc Fq F Ω n)).toRingHom.toAlgebra

theorem algebraMap_polyF {n : ℕ} (p : (Lc Fq Ω n)[X]) :
    algebraMap (Lc Fq Ω n)[X] (Fc Fq F Ω n) p = aeval (xc Fq F Ω n) p := rfl

instance isScalarTower_polyF (n : ℕ) :
    IsScalarTower (Lc Fq Ω n) (Lc Fq Ω n)[X] (Fc Fq F Ω n) :=
  IsScalarTower.of_algebraMap_eq fun a => (aeval_C (xc Fq F Ω n) a).symm

theorem transcendental_xF : Transcendental Fq (RR.xF Fq F) := by
  rw [transcendental_iff_injective]
  intro p p' h
  rw [RR.aeval_xF, RR.aeval_xF] at h
  exact FaithfulSMul.algebraMap_injective Fq[X] F h

theorem transcendental_xc (n : ℕ) [NeZero n] : Transcendental (Lc Fq Ω n) (xc Fq F Ω n) := by
  have h1 : Transcendental Fq (xc Fq F Ω n) := by
    rw [xc, transcendental_algebraMap_iff (algebraMap F (Fc Fq F Ω n)).injective]
    exact transcendental_xF Fq F
  exact h1.extendScalars (Lc Fq Ω n)

theorem aeval_xc_injective (n : ℕ) [NeZero n] :
    Function.Injective (aeval (R := Lc Fq Ω n) (xc Fq F Ω n)) :=
  transcendental_iff_injective.1 (transcendental_xc Fq F Ω n)

noncomputable instance algebra_ratF (n : ℕ) [NeZero n] :
    Algebra (RatFunc (Lc Fq Ω n)) (Fc Fq F Ω n) :=
  (RatFunc.liftAlgHom (aeval (xc Fq F Ω n))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (aeval_xc_injective Fq F Ω n))).toRingHom.toAlgebra

theorem algebraMap_ratF (n : ℕ) [NeZero n] (g : RatFunc (Lc Fq Ω n)) :
    algebraMap (RatFunc (Lc Fq Ω n)) (Fc Fq F Ω n) g = RatFunc.liftAlgHom (aeval (xc Fq F Ω n))
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (aeval_xc_injective Fq F Ω n)) g :=
  rfl

instance isScalarTower_ratF (n : ℕ) [NeZero n] :
    IsScalarTower (Lc Fq Ω n)[X] (RatFunc (Lc Fq Ω n)) (Fc Fq F Ω n) :=
  IsScalarTower.of_algebraMap_eq fun p => by
    rw [algebraMap_ratF, ← div_one (algebraMap (Lc Fq Ω n)[X] (RatFunc (Lc Fq Ω n)) p),
      ← map_one (algebraMap (Lc Fq Ω n)[X] (RatFunc (Lc Fq Ω n))), RatFunc.liftAlgHom_apply_div,
      map_one, div_one, algebraMap_polyF]

noncomputable instance decEq_ratL (n : ℕ) : DecidableEq (RatFunc (Lc Fq Ω n)) := Classical.decEq _

theorem hx_Fc (n : ℕ) [NeZero n] :
    algebraMap F (Fc Fq F Ω n) (RR.xF Fq F) = RR.xF (Lc Fq Ω n) (Fc Fq F Ω n) := by
  show xc Fq F Ω n = algebraMap (Lc Fq Ω n)[X] (Fc Fq F Ω n) X
  rw [algebraMap_polyF, aeval_X]

instance functionField_Fc (n : ℕ) [NeZero n] : FunctionField (Lc Fq Ω n) (Fc Fq F Ω n) := by
  letI : Algebra (RatFunc Fq) (Fc Fq F Ω n) :=
    ((algebraMap F (Fc Fq F Ω n)).comp (algebraMap (RatFunc Fq) F)).toAlgebra
  haveI : IsScalarTower (RatFunc Fq) F (Fc Fq F Ω n) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite (RatFunc Fq) (Fc Fq F Ω n) := Module.Finite.trans F (Fc Fq F Ω n)
  letI : Algebra (RatFunc Fq) (RatFunc (Lc Fq Ω n)) := (ratMap Fq (Lc Fq Ω n)).toAlgebra
  haveI : IsScalarTower (RatFunc Fq) (RatFunc (Lc Fq Ω n)) (Fc Fq F Ω n) :=
    IsScalarTower.of_algebraMap_eq fun g =>
      (RingHom.congr_fun (compat_rat_hom (hx_Fc Fq F Ω n)) g).symm
  exact Module.Finite.of_restrictScalars_finite (RatFunc Fq) (RatFunc (Lc Fq Ω n)) (Fc Fq F Ω n)

instance isSeparable_ratF (n : ℕ) [NeZero n] :
    Algebra.IsSeparable (RatFunc (Lc Fq Ω n)) (Fc Fq F Ω n) := by
  letI : Algebra (RatFunc Fq) (Fc Fq F Ω n) :=
    ((algebraMap F (Fc Fq F Ω n)).comp (algebraMap (RatFunc Fq) F)).toAlgebra
  haveI : IsScalarTower (RatFunc Fq) F (Fc Fq F Ω n) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra (RatFunc Fq) (RatFunc (Lc Fq Ω n)) := (ratMap Fq (Lc Fq Ω n)).toAlgebra
  haveI : IsScalarTower (RatFunc Fq) (RatFunc (Lc Fq Ω n)) (Fc Fq F Ω n) :=
    IsScalarTower.of_algebraMap_eq fun g =>
      (RingHom.congr_fun (compat_rat_hom (hx_Fc Fq F Ω n)) g).symm
  haveI : Algebra.IsSeparable (RatFunc Fq) (Fc Fq F Ω n) :=
    Algebra.IsSeparable.trans (F := RatFunc Fq) (E := F) (K := Fc Fq F Ω n)
  exact Algebra.isSeparable_tower_top_of_isSeparable (RatFunc Fq) (RatFunc (Lc Fq Ω n))
    (Fc Fq F Ω n)

theorem finrank_Fc (hk : Places.constField Fq F = ⊥) (n : ℕ) [NeZero n] :
    Module.finrank F (Fc Fq F Ω n) = Module.finrank Fq (Lc Fq Ω n) := by
  have h1 := natDegree_minpoly (F' := Fc Fq F Ω n) (pbL Fq Ω n) hk
  have h2 : minpoly F ((pbL Fq Ω n).gen : Ω) =
      minpoly F (algebraMap (Lc Fq Ω n) (Fc Fq F Ω n) (pbL Fq Ω n).gen) := by
    rw [← minpoly.algHom_eq (Fc Fq F Ω n).val (fun a b h => Subtype.ext h)]
    rfl
  rw [(IntermediateField.equivOfEq (Fc_eq_adjoin Fq F Ω n)).toLinearEquiv.finrank_eq,
    IntermediateField.adjoin.finrank
      ((isSeparable_of_mem_Lc (pbL Fq Ω n).gen.2).tower_top F).isIntegral, h2, h1,
    (pbL Fq Ω n).finrank]

/-- **`F_n / F` is a constant field extension** (in the coordinates of `RR.IsConstExt`). -/
theorem isConstExt_Fc (hk : Places.constField Fq F = ⊥) (n : ℕ) [NeZero n] :
    RR.IsConstExt Fq F (Lc Fq Ω n) (Fc Fq F Ω n) (pbL Fq Ω n).basis :=
  isConstExt (pbL Fq Ω n) hk (finrank_Fc Fq F Ω hk n) (hx_Fc Fq F Ω n)

theorem constField_Fc (hk : Places.constField Fq F = ⊥) (n : ℕ) [NeZero n] :
    Places.constField (Lc Fq Ω n) (Fc Fq F Ω n) = ⊥ :=
  constField_eq_bot (pbL Fq Ω n) hk (finrank_Fc Fq F Ω hk n) (hx_Fc Fq F Ω n)

end FF

end Ext

end RamanujanPetersson.PicDescent


end

-- ===== S4.Def_RP_PicDescent_C1 =====
section

/-!
# S4-PicDescent, part C1: the rings of a constant field extension are tensor products

For a constant field extension `F' / L` of `F / Fq` in the coordinates of `RR.IsConstExt`, the rings
of places are `Rfin L F' ≃ L ⊗[Fq] Rfin Fq F` and `Rinf L F' ≃ L ⊗[Fq] Rinf Fq F` (`tensorEquiv`, one
generic statement for both rings). Hence `B_1(F') = N_m(F)` with `m = [L : Fq]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial TensorProduct

namespace RamanujanPetersson.PicDescent

open Polynomial

section TensorIso

variable {Fq : Type*} [Field Fq] {L : Type*} [Field L] [Algebra Fq L]
  {F : Type*} [Field F] [Algebra Fq F] {F' : Type*} [Field F'] [Algebra L F'] [Algebra F F']
  [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
  {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}
  {A : Type*} [CommRing A] [Algebra Fq A] [Algebra A F] [IsScalarTower Fq A F]
  {A' : Type*} [CommRing A'] [Algebra L A'] [Algebra A' F'] [IsScalarTower L A' F']

variable (Fq L F F' A) in
/-- `l ⊗ a ↦ l a`, from `L ⊗[Fq] A` to `F'`. -/
noncomputable def tensorMap : L ⊗[Fq] A →ₐ[L] F' :=
  Algebra.TensorProduct.lift (Algebra.ofId L F')
    ((IsScalarTower.toAlgHom Fq F F').comp (IsScalarTower.toAlgHom Fq A F))
    (fun _ _ => Commute.all _ _)

theorem tensorMap_tmul (l : L) (a : A) :
    tensorMap Fq L F F' A (l ⊗ₜ a) = algebraMap A F a • algebraMap L F' l := by
  rw [tensorMap, Algebra.TensorProduct.lift_tmul, Algebra.smul_def, mul_comm]
  rfl

theorem exists_sum_tmul (c : Module.Basis ι Fq L) (t : L ⊗[Fq] A) :
    ∃ a : ι → A, t = ∑ j, c j ⊗ₜ a j := by
  obtain ⟨b, rfl⟩ := TensorProduct.eq_repr_basis_left c t
  exact ⟨b, Finsupp.sum_fintype _ _ (fun _ => TensorProduct.tmul_zero _ _)⟩

theorem tensorMap_sum (a : ι → A) :
    tensorMap Fq L F F' A (∑ j, c j ⊗ₜ a j) =
      ∑ j, algebraMap A F (a j) • algebraMap L F' (c j) := by
  rw [map_sum]
  simp only [tensorMap_tmul]

variable (hA : Function.Injective (algebraMap A F)) (hA' : Function.Injective (algebraMap A' F'))
  (hli : LinearIndependent F fun j => algebraMap L F' (c j))
  (hsp : ⊤ ≤ Submodule.span F (Set.range fun j => algebraMap L F' (c j)))
  (hc : ∀ f : ι → F, (∑ j, f j • algebraMap L F' (c j)) ∈ (algebraMap A' F').range ↔
    ∀ j, f j ∈ (algebraMap A F).range)

include hA hli in
theorem tensorMap_injective : Function.Injective (tensorMap Fq L F F' A) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨a, rfl⟩ := exists_sum_tmul c t
  rw [tensorMap_sum] at ht
  have h0 := Fintype.linearIndependent_iff.1 hli _ ht
  have : ∀ j, a j = 0 := fun j => hA (by rw [h0 j, map_zero])
  simp [this]

include hc in
theorem tensorMap_mem (t : L ⊗[Fq] A) :
    tensorMap Fq L F F' A t ∈ (IsScalarTower.toAlgHom L A' F').range := by
  obtain ⟨a, rfl⟩ := exists_sum_tmul c t
  rw [tensorMap_sum]
  obtain ⟨y, hy⟩ := (hc _).2 fun j => ⟨a j, rfl⟩
  exact ⟨y, hy⟩

include hsp hc in
theorem exists_tensorMap_eq (y : A') : ∃ t : L ⊗[Fq] A, tensorMap Fq L F F' A t = algebraMap A' F' y := by
  have hy : algebraMap A' F' y ∈ Submodule.span F (Set.range fun j => algebraMap L F' (c j)) :=
    hsp Submodule.mem_top
  obtain ⟨f, hf⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hy
  have hmem : ∀ j, f j ∈ (algebraMap A F).range := (hc f).1 (hf ▸ ⟨y, rfl⟩)
  choose a ha using hmem
  exact ⟨∑ j, c j ⊗ₜ a j, by rw [tensorMap_sum, ← hf]; simp only [ha]⟩

end TensorIso

section Instances

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (L : Type*) [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable (F' : Type*) [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']
variable [Algebra F F'] [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
variable {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}

variable {Fq F L F'}

variable (L' : Type*) [Field L'] [Algebra L L'] [Algebra Fq L'] [IsScalarTower Fq L L']

end Instances

end RamanujanPetersson.PicDescent


end

-- ===== S4.Def_RP_PicDescent_D1 =====
section

/-!
# S4-PicDescent, part D1: the Galois action of `Gal(L/Fq)` on a constant field extension

Generic setting of C1 (`F'` with an `F`-basis `c'_j = algebraMap L F' (c j)`, `c` an `Fq`-basis of `L`).
* `fieldEquiv : L ⊗[Fq] F ≃ₐ[L] F'`; `gal τ : F' ≃ₐ[F] F'` acts by `τ ⊗ id`; `galHom` is an injective group hom;
  `gal_algebraMap_L : gal τ l' = (τ l)'`.
* `mem_range_of_forall_gal`: the fixed field of all `gal τ` is `F` (Artin, `[F' : F] = [L : Fq] = #Gal(L/Fq)`).
* On a ring `A' ≃ L ⊗ A` (C1 `tensorEquiv`): `galA' τ` with `algebraMap_galA'`, `galA'Hom`, `toA' : A → A'`,
  `exists_toA'_eq` (fixed elements of `A'` come from `A`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct

namespace RamanujanPetersson.PicDescent

section Galois

variable {Fq : Type*} [Field Fq] {L : Type*} [Field L] [Algebra Fq L]
  {F : Type*} [Field F] [Algebra Fq F] {F' : Type*} [Field F'] [Algebra L F'] [Algebra F F']
  [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
  {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}
  (hli : LinearIndependent F fun j => algebraMap L F' (c j))
  (hsp : ⊤ ≤ Submodule.span F (Set.range fun j => algebraMap L F' (c j)))

theorem hcF (f : ι → F) : (∑ j, f j • algebraMap L F' (c j)) ∈ (algebraMap F' F').range ↔
    ∀ j, f j ∈ (algebraMap F F).range :=
  ⟨fun _ j => ⟨f j, rfl⟩, fun _ => ⟨_, rfl⟩⟩

include hli hsp in
theorem finrank_F' : Module.finrank F F' = Module.finrank Fq L := by
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp), Module.finrank_eq_card_basis c]

section Rings

variable {A : Type*} [CommRing A] [Algebra Fq A] [Algebra A F] [IsScalarTower Fq A F]
  {A' : Type*} [CommRing A'] [Algebra L A'] [Algebra A' F'] [IsScalarTower L A' F']
  (hA : Function.Injective (algebraMap A F)) (hA' : Function.Injective (algebraMap A' F'))
  (hc : ∀ f : ι → F, (∑ j, f j • algebraMap L F' (c j)) ∈ (algebraMap A' F').range ↔
    ∀ j, f j ∈ (algebraMap A F).range)

end Rings

end Galois

end RamanujanPetersson.PicDescent


end

-- ===== S4.Def_RP_CurveCoh_Pair =====
section

/-!
# S4-CurveCoh, part 1: cohomology of a pair `(Γ, {I_s})` in the `π₁` model (generic algebra)

Setting (S4_DESIGN section 3, reviews R2/R5/R19):
* a topological group `G` (later `π₁(U)`), a normal subgroup `Γ` (later `π₁(U ⊗ F̄)`, the geometric fundamental
  group), a representation `ρ` of `G` on `M` over ANY commutative ring `k` (review END-2, decision R19), and a family
  `I : S → Subgroup G` (later the inertia groups at the geometric boundary points `s ∈ X̄ \ Ū`, review R5).

Definitions:
* `H0 = M^Γ`;
* `H1` = LOCALLY CONSTANT (continuous, `M` discrete) 1-cocycles on `Γ` modulo coboundaries; part 2 shows it is the
  colimit of the finite-level `H¹` over open normal subgroups (covers);
* `H1c` = `H¹` of the mapping cone of `C^*(Γ, M) → ⊕_s C^*(I_s ∩ Γ, M)`: pairs `(c, b)` of a cocycle `c` and boundary
  trivialisations `b_s` with `c g = g • b_s - b_s` on `I_s ∩ Γ`, modulo `(d m, (m)_s)`;
* `H2c` = the coinvariants `M_Γ` (definition kept by review R2; the Tate twist `(-1)` enters the Frobenius as a scalar);
* the exact sequence `0 → H⁰ → ⊕_s M^{I_s} → H¹_c → H¹_par → 0`, `H¹_par = ker (H¹ → ⊕_s H¹(I_s ∩ Γ))`;
* the operators `T_ψ` (`ψ ∈ G`): `(T_ψ c)(g) = ρ(ψ) c(ψ⁻¹ g ψ)`. The GEOMETRIC Frobenius is `F = T_{φ⁻¹}` for an
  arithmetic Frobenius lift `φ`; on `H2c` it is `q • ρ(φ⁻¹)` (geometric Frobenius acts on `ℤ/lⁿ(-1)` by `q`).
  All operators commute with the maps of the exact sequence.
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace CurveCoh

noncomputable section

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module k M] (ρ : Representation k G M) (Γ : Subgroup G)

/-! ## Degree 0 and degree 1 -/

/-- Locally constant (= continuous for discrete `M`) inhomogeneous 1-cocycles `Γ → M`. -/
def Z1 : Submodule k (Γ → M) where
  carrier := {c | IsLocallyConstant c ∧ ∀ g h : Γ, c (g * h) = c g + ρ g (c h)}
  add_mem' := by
    rintro c d ⟨hc, hc'⟩ ⟨hd, hd'⟩
    refine ⟨hc.add hd, fun g h => ?_⟩
    simp only [Pi.add_apply, hc', hd', map_add]
    abel
  zero_mem' := ⟨IsLocallyConstant.zero, fun g h => by simp⟩
  smul_mem' := by
    rintro a c ⟨hc, hc'⟩
    refine ⟨hc.comp (a • ·), fun g h => ?_⟩
    simp only [Pi.smul_apply, hc', smul_add, map_smul]

theorem mem_Z1 (c : Γ → M) :
    c ∈ Z1 ρ Γ ↔ IsLocallyConstant c ∧ ∀ g h : Γ, c (g * h) = c g + ρ g (c h) := Iff.rfl

/-- 1-coboundaries `g ↦ g • m - m` that are locally constant. -/
def B1 : Submodule k (Γ → M) where
  carrier := {c | c ∈ Z1 ρ Γ ∧ ∃ m : M, ∀ g : Γ, c g = ρ g m - m}
  add_mem' := by
    rintro c d ⟨hc, m, hm⟩ ⟨hd, n, hn⟩
    refine ⟨(Z1 ρ Γ).add_mem hc hd, m + n, fun g => ?_⟩
    simp only [Pi.add_apply, hm, hn, map_add]
    abel
  zero_mem' := ⟨(Z1 ρ Γ).zero_mem, 0, fun g => by simp⟩
  smul_mem' := by
    rintro a c ⟨hc, m, hm⟩
    exact ⟨(Z1 ρ Γ).smul_mem a hc, a • m, fun g => by simp [hm, smul_sub]⟩

theorem mem_B1 (c : Γ → M) : c ∈ B1 ρ Γ ↔ c ∈ Z1 ρ Γ ∧ ∃ m : M, ∀ g : Γ, c g = ρ g m - m := Iff.rfl

/-- `H¹(Γ, M)` with continuous (locally constant) cochains. -/
abbrev H1 : Type := ↥(Z1 ρ Γ) ⧸ (B1 ρ Γ).comap (Z1 ρ Γ).subtype

/-- The class of a cocycle. -/
noncomputable def H1.mk : Z1 ρ Γ →ₗ[k] H1 ρ Γ := Submodule.mkQ _

theorem Z1_one {c : Γ → M} (hc : c ∈ Z1 ρ Γ) : c 1 = 0 := by
  have h := hc.2 1 1
  simpa using h

theorem Z1_inv {c : Γ → M} (hc : c ∈ Z1 ρ Γ) (g : Γ) : c g⁻¹ = -ρ (g⁻¹ : Γ) (c g) := by
  have h := hc.2 g g⁻¹
  rw [mul_inv_cancel, Z1_one ρ Γ hc] at h
  have h2 : ρ (g : G) (c g⁻¹) = -c g := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h.symm
  have h3 := congrArg (ρ ((g : G)⁻¹)) h2
  rw [Representation.inv_self_apply, map_neg] at h3
  simpa using h3

/-- A cocycle that is a coboundary on `g` is a coboundary on the conjugate `η g η⁻¹`, with the conjugated
trivialisation `ρ η b - c η`. -/
theorem Z1_conj {c : Γ → M} (hc : c ∈ Z1 ρ Γ) (η g : Γ) (b : M) (hg : c g = ρ g b - b) :
    c (η * g * η⁻¹) = ρ (η * g * η⁻¹ : Γ) (ρ η b - c η) - (ρ η b - c η) := by
  rw [hc.2 (η * g) η⁻¹, hc.2 η g, hg, Z1_inv ρ Γ hc η]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, Module.End.mul_apply, map_sub, map_neg,
    Representation.inv_self_apply]
  abel

/-! ## The cone: compactly supported `H¹` -/

variable {S : Type} (I : S → Subgroup G)

/-- Relative 1-cocycles of the pair `(Γ, {I_s})`: degree-1 cocycles of the mapping cone of
`C^*(Γ, M) → ⊕_s C^*(I_s ∩ Γ, M)`, i.e. a cocycle `c` with boundary trivialisations `b_s`. -/
def Z1c : Submodule k ((Γ → M) × (S → M)) where
  carrier := {p | p.1 ∈ Z1 ρ Γ ∧ ∀ (s : S) (g : Γ), (g : G) ∈ I s → p.1 g = ρ g (p.2 s) - p.2 s}
  add_mem' := by
    rintro p q ⟨hp, hp'⟩ ⟨hq, hq'⟩
    refine ⟨(Z1 ρ Γ).add_mem hp hq, fun s g hg => ?_⟩
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, hp' s g hg, hq' s g hg, map_add]
    abel
  zero_mem' := ⟨(Z1 ρ Γ).zero_mem, fun s g _ => by simp⟩
  smul_mem' := by
    rintro a p ⟨hp, hp'⟩
    refine ⟨(Z1 ρ Γ).smul_mem a hp, fun s g hg => ?_⟩
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, hp' s g hg, map_smul, smul_sub]

theorem mem_Z1c (p : (Γ → M) × (S → M)) : p ∈ Z1c ρ Γ I ↔
    p.1 ∈ Z1 ρ Γ ∧ ∀ (s : S) (g : Γ), (g : G) ∈ I s → p.1 g = ρ g (p.2 s) - p.2 s := Iff.rfl

/-- Relative coboundaries `(d m, (m)_s)`. -/
def B1c : Submodule k ((Γ → M) × (S → M)) where
  carrier := {p | p ∈ Z1c ρ Γ I ∧ ∃ m : M, (∀ g : Γ, p.1 g = ρ g m - m) ∧ ∀ s, p.2 s = m}
  add_mem' := by
    rintro p q ⟨hp, m, hm, hm'⟩ ⟨hq, n, hn, hn'⟩
    refine ⟨(Z1c ρ Γ I).add_mem hp hq, m + n, fun g => ?_, fun s => ?_⟩
    · simp only [Prod.fst_add, Pi.add_apply, hm, hn, map_add]
      abel
    · simp [hm', hn']
  zero_mem' := ⟨(Z1c ρ Γ I).zero_mem, 0, fun g => by simp, fun s => by simp⟩
  smul_mem' := by
    rintro a p ⟨hp, m, hm, hm'⟩
    exact ⟨(Z1c ρ Γ I).smul_mem a hp, a • m, fun g => by simp [hm, smul_sub], fun s => by simp [hm']⟩

theorem mem_B1c (p : (Γ → M) × (S → M)) : p ∈ B1c ρ Γ I ↔
    p ∈ Z1c ρ Γ I ∧ ∃ m : M, (∀ g : Γ, p.1 g = ρ g m - m) ∧ ∀ s, p.2 s = m := Iff.rfl

/-- `H¹_c(Ū, M)`: `H¹` of the mapping cone (relative cohomology of `(Γ, {I_s})`). -/
abbrev H1c : Type := ↥(Z1c ρ Γ I) ⧸ (B1c ρ Γ I).comap (Z1c ρ Γ I).subtype

/-- The class of a relative cocycle. -/
noncomputable def H1c.mk : Z1c ρ Γ I →ₗ[k] H1c ρ Γ I := Submodule.mkQ _

/-- `⊕_s M^{I_s}` (only `I_s ∩ Γ` matters). -/
def bdryInv : Submodule k (S → M) where
  carrier := {b | ∀ (s : S) (g : Γ), (g : G) ∈ I s → ρ g (b s) = b s}
  add_mem' := by
    intro b b' hb hb' s g hg
    simp [hb s g hg, hb' s g hg]
  zero_mem' := fun s g _ => by simp
  smul_mem' := by
    intro a b hb s g hg
    simp [hb s g hg]

theorem mem_bdryInv (b : S → M) :
    b ∈ bdryInv ρ Γ I ↔ ∀ (s : S) (g : Γ), (g : G) ∈ I s → ρ g (b s) = b s := Iff.rfl

/-- Cocycles that are coboundaries on every `I_s ∩ Γ` (unramified at the boundary). -/
def Z1par : Submodule k (Γ → M) where
  carrier := {c | c ∈ Z1 ρ Γ ∧ ∀ s : S, ∃ b : M, ∀ g : Γ, (g : G) ∈ I s → c g = ρ g b - b}
  add_mem' := by
    rintro c d ⟨hc, hc'⟩ ⟨hd, hd'⟩
    refine ⟨(Z1 ρ Γ).add_mem hc hd, fun s => ?_⟩
    obtain ⟨b, hb⟩ := hc' s
    obtain ⟨b', hb'⟩ := hd' s
    refine ⟨b + b', fun g hg => ?_⟩
    simp only [Pi.add_apply, hb g hg, hb' g hg, map_add]
    abel
  zero_mem' := ⟨(Z1 ρ Γ).zero_mem, fun s => ⟨0, fun g _ => by simp⟩⟩
  smul_mem' := by
    rintro a c ⟨hc, hc'⟩
    refine ⟨(Z1 ρ Γ).smul_mem a hc, fun s => ?_⟩
    obtain ⟨b, hb⟩ := hc' s
    exact ⟨a • b, fun g hg => by simp [hb g hg, smul_sub]⟩

/-- `H¹_par = ker (H¹(Γ, M) → ⊕_s H¹(I_s ∩ Γ, M))`, as the image of `Z1par`. -/
noncomputable def H1par : Submodule k (H1 ρ Γ) :=
  ((Z1par ρ Γ I).comap (Z1 ρ Γ).subtype).map (H1.mk ρ Γ)

/-! ## The maps of the exact sequence `0 → H⁰ → ⊕_s M^{I_s} → H¹_c → H¹_par → 0` -/

theorem zero_bdry_mem (b : bdryInv ρ Γ I) : ((0 : Γ → M), (b : S → M)) ∈ Z1c ρ Γ I :=
  ⟨(Z1 ρ Γ).zero_mem, fun s g hg => by simp [(mem_bdryInv ρ Γ I _).1 b.2 s g hg]⟩

/-- `⊕_s M^{I_s} → H¹_c`, `b ↦ [(0, b)]`. -/
noncomputable def bdryToH1c : bdryInv ρ Γ I →ₗ[k] H1c ρ Γ I :=
  H1c.mk ρ Γ I ∘ₗ LinearMap.codRestrict (Z1c ρ Γ I)
    (LinearMap.inr k (Γ → M) (S → M) ∘ₗ (bdryInv ρ Γ I).subtype) (fun b => zero_bdry_mem ρ Γ I b)

/-! ## Frobenius operators -/

section Frob

variable [IsTopologicalGroup G] [hΓ : Γ.Normal]

/-- Conjugation `g ↦ ψ⁻¹ g ψ` on the normal subgroup `Γ`. -/
def conjΓ (ψ : G) (g : Γ) : Γ := ⟨ψ⁻¹ * g * ψ, by simpa using hΓ.conj_mem (g : G) g.2 ψ⁻¹⟩

@[simp] theorem conjΓ_val (ψ : G) (g : Γ) : (conjΓ Γ ψ g : G) = ψ⁻¹ * g * ψ := rfl

theorem conjΓ_mul (ψ : G) (g h : Γ) : conjΓ Γ ψ (g * h) = conjΓ Γ ψ g * conjΓ Γ ψ h := by
  ext
  simp [mul_assoc]

theorem continuous_conjΓ (ψ : G) : Continuous (conjΓ Γ ψ) := by
  have : Continuous fun g : Γ => ψ⁻¹ * (g : G) * ψ :=
    (continuous_const.mul continuous_subtype_val).mul continuous_const
  exact this.subtype_mk _

theorem rho_conj (ψ : G) (g : Γ) (x : M) : ρ ψ (ρ (conjΓ Γ ψ g) x) = ρ g (ρ ψ x) := by
  have e : ψ * (ψ⁻¹ * (g : G) * ψ) = (g : G) * ψ := by group
  calc ρ ψ (ρ (conjΓ Γ ψ g) x) = ρ (ψ * (ψ⁻¹ * (g : G) * ψ)) x := by rw [map_mul]; rfl
    _ = ρ g (ρ ψ x) := by rw [e, map_mul]; rfl

theorem rho_conj' (ψ : G) (g : Γ) (x : M) : ρ (conjΓ Γ ψ⁻¹ g) (ρ ψ x) = ρ ψ (ρ g x) := by
  have e : ψ⁻¹⁻¹ * (g : G) * ψ⁻¹ * ψ = ψ * g := by group
  calc ρ (conjΓ Γ ψ⁻¹ g) (ρ ψ x) = ρ (ψ⁻¹⁻¹ * (g : G) * ψ⁻¹ * ψ) x := by rw [map_mul]; rfl
    _ = ρ ψ (ρ g x) := by rw [e, map_mul]; rfl

/-- The cochain operator `(T_ψ c)(g) = ρ(ψ) (c (ψ⁻¹ g ψ))`. -/
def twist (ψ : G) : (Γ → M) →ₗ[k] (Γ → M) where
  toFun c g := ρ ψ (c (conjΓ Γ ψ g))
  map_add' c d := by
    funext g
    simp
  map_smul' a c := by
    funext g
    simp

theorem twist_apply (ψ : G) (c : Γ → M) (g : Γ) : twist ρ Γ ψ c g = ρ ψ (c (conjΓ Γ ψ g)) := rfl

theorem twist_mem_Z1 (ψ : G) {c : Γ → M} (hc : c ∈ Z1 ρ Γ) : twist ρ Γ ψ c ∈ Z1 ρ Γ := by
  refine ⟨(hc.1.comp_continuous (continuous_conjΓ Γ ψ)).comp (ρ ψ), fun g h => ?_⟩
  rw [twist_apply, twist_apply, twist_apply, conjΓ_mul, hc.2, map_add, rho_conj]

theorem twist_mem_B1 (ψ : G) {c : Γ → M} (hc : c ∈ B1 ρ Γ) : twist ρ Γ ψ c ∈ B1 ρ Γ := by
  obtain ⟨hcZ, m, hm⟩ := hc
  refine ⟨twist_mem_Z1 ρ Γ ψ hcZ, ρ ψ m, fun g => ?_⟩
  rw [twist_apply, hm, map_sub, rho_conj]

/-- Frobenius on `H¹`. -/
noncomputable def frobH1 (ψ : G) : H1 ρ Γ →ₗ[k] H1 ρ Γ :=
  Submodule.mapQ _ _ ((twist ρ Γ ψ).restrict (fun c hc => twist_mem_Z1 ρ Γ ψ hc))
    (fun c hc => twist_mem_B1 ρ Γ ψ hc)

variable {S : Type} (I : S → Subgroup G)

/-- The cone operator: `(c, b) ↦ (T_ψ c, s ↦ ρ(ψ) (ρ(h_s) b_{τ s} - c(h_s)))`. -/
def twistc (ψ : G) (τ : S → S) (h : S → Γ) : ((Γ → M) × (S → M)) →ₗ[k] ((Γ → M) × (S → M)) where
  toFun p := (twist ρ Γ ψ p.1, fun s => ρ ψ (ρ (h s) (p.2 (τ s)) - p.1 (h s)))
  map_add' p q := by
    refine Prod.ext (map_add _ _ _) (funext fun s => ?_)
    simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, map_add, map_sub]
    abel
  map_smul' a p := by
    refine Prod.ext (map_smul _ _ _) (funext fun s => ?_)
    simp [smul_sub]

theorem twistc_fst (ψ : G) (τ : S → S) (h : S → Γ) (p : (Γ → M) × (S → M)) :
    (twistc ρ Γ ψ τ h p).1 = twist ρ Γ ψ p.1 := rfl

theorem twistc_snd (ψ : G) (τ : S → S) (h : S → Γ) (p : (Γ → M) × (S → M)) (s : S) :
    (twistc ρ Γ ψ τ h p).2 s = ρ ψ (ρ (h s) (p.2 (τ s)) - p.1 (h s)) := rfl

/-- The compatibility of a Frobenius lift with the boundary: `ψ⁻¹ (I_s ∩ Γ) ψ ⊆ h_s I_{τ s} h_s⁻¹`. -/
def BdryCompat (ψ : G) (τ : S → S) (h : S → Γ) : Prop :=
  ∀ (s : S) (g : Γ), (g : G) ∈ I s → (h s : G)⁻¹ * (ψ⁻¹ * g * ψ) * h s ∈ I (τ s)

theorem bdryCompat_mem {ψ : G} {τ : S → S} {h : S → Γ} (hI : BdryCompat Γ I ψ τ h) (s : S) (g : Γ)
    (hg : (g : G) ∈ I s) : (((h s)⁻¹ * conjΓ Γ ψ g * h s : Γ) : G) ∈ I (τ s) := by
  simpa [mul_assoc] using hI s g hg

theorem twistc_mem_Z1c (ψ : G) (τ : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ τ h)
    {p : (Γ → M) × (S → M)} (hp : p ∈ Z1c ρ Γ I) : twistc ρ Γ ψ τ h p ∈ Z1c ρ Γ I := by
  refine ⟨twist_mem_Z1 ρ Γ ψ hp.1, fun s g hg => ?_⟩
  have hg' := hp.2 (τ s) _ (bdryCompat_mem Γ I hI s g hg)
  have hc := Z1_conj ρ Γ hp.1 (h s) _ _ hg'
  have he : h s * ((h s)⁻¹ * conjΓ Γ ψ g * h s) * (h s)⁻¹ = conjΓ Γ ψ g := by group
  rw [he] at hc
  rw [twistc_fst, twistc_snd, twist_apply, hc, map_sub, rho_conj]

theorem twistc_mem_B1c (ψ : G) (τ : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ τ h)
    {p : (Γ → M) × (S → M)} (hp : p ∈ B1c ρ Γ I) : twistc ρ Γ ψ τ h p ∈ B1c ρ Γ I := by
  obtain ⟨hpZ, m, hm1, hm2⟩ := hp
  refine ⟨twistc_mem_Z1c ρ Γ I ψ τ h hI hpZ, ρ ψ m, fun g => ?_, fun s => ?_⟩
  · rw [twistc_fst, twist_apply, hm1, map_sub, rho_conj]
  · rw [twistc_snd, hm2, hm1]
    simp

/-- Frobenius on `H¹_c`. -/
noncomputable def frobH1c (ψ : G) (τ : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ τ h) :
    H1c ρ Γ I →ₗ[k] H1c ρ Γ I :=
  Submodule.mapQ _ _ ((twistc ρ Γ ψ τ h).restrict (fun p hp => twistc_mem_Z1c ρ Γ I ψ τ h hI hp))
    (fun p hp => twistc_mem_B1c ρ Γ I ψ τ h hI hp)

/-- `H²_c := M_Γ`, the coinvariants (definition kept by review R2; S4-PD proves it is the cone's `H²`). -/
abbrev H2c : Type := Representation.Coinvariants (ρ.comp Γ.subtype)

/-- Frobenius on `H²_c`: `χ • ρ(ψ)` on coinvariants. For the geometric Frobenius `ψ = φ⁻¹` and `χ = q` this is `F`
on `M_Γ(-1)` (geometric Frobenius acts on `ℤ/lⁿ(-1)` by multiplication by `q`). -/
noncomputable def frobH2c (ψ : G) (χ : k) : H2c ρ Γ →ₗ[k] H2c ρ Γ :=
  Representation.Coinvariants.lift _ (χ • (Representation.Coinvariants.mk _ ∘ₗ ρ ψ)) (fun g =>
    LinearMap.ext fun x => by
      have h := Representation.Coinvariants.mk_self_apply (ρ.comp Γ.subtype) (conjΓ Γ ψ⁻¹ g) (ρ ψ x)
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype] at h
      rw [rho_conj'] at h
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, MonoidHom.coe_comp, Function.comp_apply,
        Subgroup.coe_subtype, h])

theorem frobH2c_mk (ψ : G) (χ : k) (x : M) :
    frobH2c ρ Γ ψ χ (Representation.Coinvariants.mk _ x) = χ • Representation.Coinvariants.mk _ (ρ ψ x) := rfl

/-! ### Frobenius commutes with the exact sequence -/

end Frob

/-! ## Sanity: constant coefficients -/

section Constant

variable (I : S → Subgroup G)

end Constant

end

end CurveCoh
end RamanujanPetersson


end

-- ===== S4.Def_RP_GalCover =====
section

/-!
# S4-GalCover draft v1: Galois etale covers and Frobenius (S4_DESIGN section 1)
-/

set_option autoImplicit false

open scoped Pointwise

namespace RamanujanPetersson

namespace GalCover

variable {A : Type} [CommRing A] [IsDomain A]

/-! ## Constants, the geometric subgroup, Frobenius on constants -/

section Constants

variable (Fq : Type) [Field Fq] [Algebra Fq A]

end Constants

/-! ## Morphisms of covers -/

/-! ## Etale Galois extensions have trivial inertia (bridge `ofEtale`) -/

section Etale

variable {B G : Type} [CommRing B] [IsDomain B] [Algebra A B] [Group G] [Finite G]
  [MulSemiringAction G B] [IsGaloisGroup G A B]

end Etale

end GalCover

/-! ## The etale fundamental group and the finite-quotient bridge -/

section Pi1

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

/-- Galois groups over `K` commute with scalars from `A` (which act through `K`). -/
instance algEquiv_smulCommClass (L : Type) [Field L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] : SMulCommClass (L ≃ₐ[K] L) A L :=
  ⟨fun σ a x => by
    show σ (a • x) = a • σ x
    rw [← algebraMap_smul K a x, ← algebraMap_smul K a (σ x), map_smul]⟩

/-- A subextension `L` of `K̄/K` is unramified over `A`: every inertia group of `Gal(L/K)` acting on the
integral closure of `A` in `L` is trivial. -/
def IsUnramifiedSub (L : IntermediateField K (AlgebraicClosure K)) : Prop :=
  ∀ Q : Ideal (integralClosure A L), Q.IsPrime → Q.inertia (L ≃ₐ[K] L) = ⊥

/-- The finite Galois subextensions of `K̄/K` that are unramified over `A`. -/
def unramSet : Set (IntermediateField K (AlgebraicClosure K)) :=
  {L | FiniteDimensional K L ∧ IsGalois K L ∧ IsUnramifiedSub A K L}

/-- The maximal extension `K_U` of `K` unramified over `U = Spec A`. -/
noncomputable def maxUnram : IntermediateField K (AlgebraicClosure K) :=
  ⨆ L : unramSet A K, (L : IntermediateField K (AlgebraicClosure K))

/-- The etale fundamental group `π₁(U) = Gal(K_U/K)` (Krull topology). -/
noncomputable abbrev Pi1 : Type := maxUnram A K ≃ₐ[K] maxUnram A K

noncomputable example : TopologicalSpace (Pi1 A K) := inferInstance
instance unramSet_isGalois (L : unramSet A K) :
    IsGalois K (L : IntermediateField K (AlgebraicClosure K)) := L.2.2.1

instance maxUnram_isGalois : IsGalois K (maxUnram A K) := by
  unfold maxUnram
  exact ⟨⟩

theorem bot_mem_unramSet : (⊥ : IntermediateField K (AlgebraicClosure K)) ∈ unramSet A K := by
  refine ⟨inferInstance, inferInstance, fun Q _ => ?_⟩
  rw [eq_bot_iff]
  intro σ _
  rw [Subgroup.mem_bot]
  ext x
  obtain ⟨k, hk⟩ := IntermediateField.mem_bot.mp x.2
  have hx : x = algebraMap K _ k := Subtype.ext hk.symm
  rw [hx, AlgEquiv.commutes]
  rfl

/-- Restriction of an `A`-integral element of `L₁ ⊆ L₂` (as an `A`-algebra map of integral closures). -/
noncomputable def incl {L₁ L₂ : IntermediateField K (AlgebraicClosure K)} (h : L₁ ≤ L₂) :
    integralClosure A L₁ →ₐ[A] integralClosure A L₂ :=
  ((IntermediateField.inclusion h).restrictScalars A).mapIntegralClosure

theorem incl_val {L₁ L₂ : IntermediateField K (AlgebraicClosure K)} (h : L₁ ≤ L₂)
    (y : integralClosure A L₁) : (((incl A K h y : L₂) : AlgebraicClosure K)) = ((y : L₁) : AlgebraicClosure K) :=
  rfl

/-- Unramified finite Galois subextensions are closed under composita. -/
theorem sup_mem_unramSet {L₁ L₂ : IntermediateField K (AlgebraicClosure K)} (h₁ : L₁ ∈ unramSet A K)
    (h₂ : L₂ ∈ unramSet A K) : L₁ ⊔ L₂ ∈ unramSet A K := by
  obtain ⟨f₁, g₁, u₁⟩ := h₁
  obtain ⟨f₂, g₂, u₂⟩ := h₂
  refine ⟨inferInstance, inferInstance, fun Q hQ => ?_⟩
  have := hQ
  rw [eq_bot_iff]
  intro τ hτ
  rw [Subgroup.mem_bot]
  obtain ⟨σ, hσ⟩ : ∃ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∀ y : ↥(L₁ ⊔ L₂),
      σ (y : AlgebraicClosure K) = ((τ y : ↥(L₁ ⊔ L₂)) : AlgebraicClosure K) :=
    ⟨τ.liftNormal (AlgebraicClosure K), fun y => τ.liftNormal_commutes (AlgebraicClosure K) y⟩
  -- `σ` fixes each `Lᵢ`: its restriction lies in the inertia of the contracted prime
  have key : ∀ (L : IntermediateField K (AlgebraicClosure K)) (hle : L ≤ L₁ ⊔ L₂) [IsGalois K L],
      IsUnramifiedSub A K L → σ ∈ L.fixingSubgroup := by
    intro L hle _ uL
    have hP : (Q.comap (incl A K hle)).IsPrime := Ideal.IsPrime.comap _
    have hin : AlgEquiv.restrictNormalHom L σ ∈ (Q.comap (incl A K hle)).inertia (L ≃ₐ[K] L) := by
      intro y
      show (incl A K hle) (AlgEquiv.restrictNormalHom L σ • y - y) ∈ Q
      have h : τ • incl A K hle y - incl A K hle y ∈ Q := hτ (incl A K hle y)
      convert h using 2
      apply Subtype.ext; apply Subtype.ext
      show ((AlgEquiv.restrictNormalHom L σ (y : L) : L) : AlgebraicClosure K) - ((y : L) : AlgebraicClosure K)
        = ((τ (incl A K hle y : ↥(L₁ ⊔ L₂)) : ↥(L₁ ⊔ L₂)) : AlgebraicClosure K) - ((y : L) : AlgebraicClosure K)
      rw [AlgEquiv.restrictNormalHom_apply, ← hσ]
      rfl
    have h1 := uL _ hP
    rw [h1, Subgroup.mem_bot] at hin
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have := congrArg (fun e : L ≃ₐ[K] L => ((e ⟨x, hx⟩ : L) : AlgebraicClosure K)) hin
    simpa [AlgEquiv.restrictNormalHom_apply] using this
  have hfix : σ ∈ (L₁ ⊔ L₂).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨key L₁ le_sup_left u₁, key L₂ le_sup_right u₂⟩
  ext y
  rw [AlgEquiv.one_apply, ← hσ]
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hfix y y.2

theorem directedOn_unramSet : DirectedOn (· ≤ ·) (unramSet A K) := fun L₁ h₁ L₂ h₂ =>
  ⟨L₁ ⊔ L₂, sup_mem_unramSet A K h₁ h₂, le_sup_left, le_sup_right⟩

theorem maxUnram_eq_sSup : maxUnram A K = sSup (unramSet A K) := by
  rw [maxUnram, sSup_eq_iSup']

/-- Every finitely generated subextension of `K_U` lies in one unramified finite Galois `L`. -/
theorem exists_unramSet_of_finite (s : Finset (AlgebraicClosure K))
    (hs : ∀ x ∈ s, x ∈ maxUnram A K) :
    ∃ L ∈ unramSet A K, IntermediateField.adjoin K (s : Set (AlgebraicClosure K)) ≤ L := by
  have hc := IntermediateField.adjoin_finset_isCompactElement (F := K) s
  rw [CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le] at hc
  refine hc (unramSet A K) ⟨⊥, bot_mem_unramSet A K⟩ (directedOn_unramSet A K) ?_
  rw [← maxUnram_eq_sSup, IntermediateField.adjoin_le_iff]
  exact fun x hx => hs x hx

section Bridge

variable [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A] [IsNoetherianRing A]

end Bridge

end Pi1

/-! ## Charts over other base rings: the infinity chart and boundary places (review R5) -/

namespace GalCover

section Charts

variable {A : Type} [CommRing A] [IsDomain A]
variable (K L : Type) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]

variable (R0 : Type) [CommRing R0] [IsDomain R0] [IsIntegrallyClosed R0] [Algebra R0 K]
  [IsFractionRing R0 K] [Algebra R0 L] [IsScalarTower R0 K L]

end Charts

/-! ### The two charts of a base curve inside `𝔸¹`: finite (`Fq[X]`) and infinity (`O_∞`) -/

section CurveCharts

open Polynomial

variable {A : Type} [CommRing A] [IsDomain A]
variable (Fq : Type) [Field Fq] [DecidableEq (RatFunc Fq)] [Algebra A (RatFunc Fq)]
  [IsFractionRing A (RatFunc Fq)]
variable (L : Type) [Field L] [Algebra (RatFunc Fq) L] [Algebra A L] [IsScalarTower A (RatFunc Fq) L]

variable [Algebra Fq[X] L] [IsScalarTower Fq[X] (RatFunc Fq) L]

end CurveCharts

end GalCover

end RamanujanPetersson


end

-- ===== S4.Def_RP_CurveCoh_Curve =====
section

/-!
# S4-CurveCoh, part 7: the curve instance

`U = Spec A` with function field `K` (for the project's curves `K = 𝔽_q(X)`), `π₁(U) = Gal(K_U/K)`
(`Pi1 A K`, S4-GalCover, Krull topology, compact).

* Constants: `IsConst q x` (`x ∈ 𝔽_{qⁿ}` for some `n ≥ 1`); the geometric fundamental group
  `pi1geo A K q = π₁(U ⊗ 𝔽̄_q)`, the automorphisms fixing every constant: closed (`pi1geo_isClosed`), normal,
  compact (`pi1geo_compactSpace`, used by the colimit description `curveH1_exists_finite_level`).
* Frobenius lifts `IsFrobLift A K q φ` (`φ x = x^q` on constants): two lifts differ by `π₁^geo`
  (`IsFrobLift.inv_mul_mem`). The EXISTENCE of a lift (the constant-field extensions are unramified, so lie in `K_U`)
  is not proved here: every statement takes the lift `φ` as an argument (supplied by S4-Kummer / CP4a).
* Boundary: for a chart ring `R0` with fraction field `K` (for `∞`: `R0 = O_∞`, S3-Places `Places.Oinf`), the
  pro-chart `proChart A K R0 = integralClosure R0 K_U` with its `π₁(U)`-action; `BdryData` chooses representatives
  `P s` of the `π₁^geo`-orbits of the boundary points (a `π₁(U)`-stable predicate `B`, for `∞` the nonzero primes);
  `I s = BdryData.inertia s` is the inertia group (review R5). `conj_mem_inertia_smul`: inertia is transported by
  conjugation, so every `ψ` permutes the boundary (`BdryData.exists_compat`, giving the data of `frobH1c`).
  Two boundary families (e.g. `∞` and finite removed points) combine with `bdryCompat_sum`.
* Curve cohomology (any commutative coefficient ring `Λ`, review R19): `curveH0/H1/H1c/H1par/H2c` and the
  GEOMETRIC Frobenius `geomFrobH0/H1/H1c/Bdry/H2c` (`F = T_{φ⁻¹}`, `q` on `H²_c`), the exact sequence `curve_les`,
  Frobenius compatibility `geomFrob_les`.
* Lisse coefficients `IsLisse ρ` (open kernel): they factor through a finite Galois etale cover
  (`IsLisse.exists_cover`, via S4-GalCover `exists_cover_of_isOpen`).
* Sanity: `curveH0_trivialEquiv` (`H⁰(Λ) = Λ`, e.g. `Λ = ℤ/lⁿ`), `curveH2c_trivialEquiv` with
  `geomFrobH2c_trivial` (`F = q` on `H²_c(Λ) = Λ(-1)`), `finrank_curveH1c_trivial` (rank of `H¹_c(Λ)` is
  `#boundary - 1` when `H¹_par = 0`, e.g. on `U_j` where S4-Kummer gives `Pic(Ū_j) = 0`).
-/

set_option autoImplicit false

open scoped Pointwise

namespace RamanujanPetersson
namespace CurveCoh

noncomputable section

/-! ## Constants and the geometric fundamental group -/

/-- `x` is a constant of level `q`: `x ∈ 𝔽_{qⁿ}` for some `n ≥ 1`. -/
def IsConst {L : Type} [Field L] (q : ℕ) (x : L) : Prop := ∃ n : ℕ, 0 < n ∧ x ^ q ^ n = x

theorem IsConst.map {L L' F : Type} [Field L] [Field L'] [FunLike F L L'] [RingHomClass F L L'] (f : F)
    {q : ℕ} {x : L} (hx : IsConst q x) : IsConst q (f x) := by
  obtain ⟨n, hn, h⟩ := hx
  exact ⟨n, hn, by rw [← map_pow, h]⟩

section Geo

variable (A K : Type) [CommRing A] [Field K] [Algebra A K] (q : ℕ)

/-- The geometric fundamental group `π₁(U ⊗ 𝔽̄_q) = Gal(K_U / K_U ∩ K𝔽̄_q) ⊆ π₁(U)`: the automorphisms of `K_U`
fixing every constant. -/
def pi1geo : Subgroup (Pi1 A K) where
  carrier := {σ | ∀ x : maxUnram A K, IsConst q x → σ x = x}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {σ τ} hσ hτ x hx => by
    show σ (τ x) = x
    rw [hτ x hx, hσ x hx]
  inv_mem' := fun {σ} hσ x hx => by
    show σ.symm x = x
    rw [AlgEquiv.symm_apply_eq]
    exact (hσ x hx).symm

theorem mem_pi1geo (σ : Pi1 A K) : σ ∈ pi1geo A K q ↔ ∀ x : maxUnram A K, IsConst q x → σ x = x := Iff.rfl

instance pi1geo_normal : (pi1geo A K q).Normal where
  conj_mem σ hσ τ := by
    refine (mem_pi1geo A K q _).2 fun x hx => ?_
    have h1 : σ (τ.symm x) = τ.symm x := hσ _ (hx.map τ.symm)
    show τ (σ (τ.symm x)) = x
    rw [h1, AlgEquiv.apply_symm_apply]

/-- The stabilizer of one element of `K_U`. -/
def fixElt (x : maxUnram A K) : Subgroup (Pi1 A K) where
  carrier := {σ | σ x = x}
  one_mem' := rfl
  mul_mem' := fun {σ τ} (hσ : σ x = x) (hτ : τ x = x) => show σ (τ x) = x by rw [hτ, hσ]
  inv_mem' := fun {σ} (hσ : σ x = x) => show σ.symm x = x by rw [AlgEquiv.symm_apply_eq, hσ]

/-- Stabilizers are open: they contain `Gal(K_U/K(x))` with `K(x)/K` finite. -/
theorem fixElt_isOpen (x : maxUnram A K) : IsOpen (fixElt A K x : Set (Pi1 A K)) := by
  have hx : IsIntegral K x := (Algebra.IsSeparable.isSeparable K x).isIntegral
  haveI : FiniteDimensional K (IntermediateField.adjoin K {x}) := IntermediateField.adjoin.finiteDimensional hx
  refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin K {x}).fixingSubgroup) ?_
    (IntermediateField.fixingSubgroup_isOpen _)
  intro σ hσ
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
  exact hσ x (IntermediateField.subset_adjoin K {x} (Set.mem_singleton x))

theorem pi1geo_isClosed : IsClosed (pi1geo A K q : Set (Pi1 A K)) := by
  have h : (pi1geo A K q : Set (Pi1 A K)) =
      ⋂ (x : maxUnram A K) (_ : IsConst q x), (fixElt A K x : Set (Pi1 A K)) := by
    ext σ
    simp only [Set.mem_iInter, SetLike.mem_coe]
    rfl
  rw [h]
  exact isClosed_iInter fun x => isClosed_iInter fun _ => Subgroup.isClosed_of_isOpen _ (fixElt_isOpen A K x)

/-- `φ ∈ π₁(U)` is an (arithmetic) Frobenius lift: `φ x = x^q` on constants. -/
def IsFrobLift (φ : Pi1 A K) : Prop := ∀ x : maxUnram A K, IsConst q x → φ x = x ^ q

/-! ## Boundary points and their inertia -/

section Boundary

variable (R0 : Type) [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)]
  [IsScalarTower R0 K (maxUnram A K)]

/-- The pro-chart over `Spec R0`: the integral closure of `R0` in `K_U`, acted on by `π₁(U)`. -/
abbrev proChart : Type := integralClosure R0 (maxUnram A K)

/-- A nonzero prime of the pro-chart. For `R0 = O_∞` these are the boundary points over `∞`. -/
def IsBdryPrime (Q : Ideal (proChart A K R0)) : Prop := Q.IsPrime ∧ Q ≠ ⊥

theorem isBdryPrime_smul (σ : Pi1 A K) {Q : Ideal (proChart A K R0)} (hQ : IsBdryPrime A K R0 Q) :
    IsBdryPrime A K R0 (σ • Q) := by
  haveI := hQ.1
  refine ⟨Ideal.IsPrime.smul σ, ?_⟩
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ.2
  exact (Submodule.ne_bot_iff _).2 ⟨σ • x, Ideal.smul_mem_pointwise_smul σ x Q hx, (smul_ne_zero_iff_ne σ).2 hx0⟩

/-- Inertia is transported by conjugation: `σ I(Q) σ⁻¹ = I(σ Q)`. -/
theorem conj_mem_inertia_smul (σ : Pi1 A K) {Q : Ideal (proChart A K R0)} {g : Pi1 A K}
    (hg : g ∈ Q.inertia (Pi1 A K)) : σ * g * σ⁻¹ ∈ (σ • Q).inertia (Pi1 A K) := by
  refine AddSubgroup.mem_inertia.2 fun x => ?_
  have hx : g • (σ⁻¹ • x) - σ⁻¹ • x ∈ Q := AddSubgroup.mem_inertia.1 hg (σ⁻¹ • x)
  show (σ * g * σ⁻¹) • x - x ∈ σ • Q
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub, mul_smul, mul_smul, inv_smul_smul]
  exact hx

/-- The inverse transport: if `Q = σ Q'` then `σ⁻¹ I(Q) σ ⊆ I(Q')`. -/
theorem inv_conj_mem_inertia {σ : Pi1 A K} {Q Q' : Ideal (proChart A K R0)} (hQ : Q = σ • Q') {g : Pi1 A K}
    (hg : g ∈ Q.inertia (Pi1 A K)) : σ⁻¹ * g * σ ∈ Q'.inertia (Pi1 A K) := by
  subst hQ
  refine AddSubgroup.mem_inertia.2 fun x => ?_
  have hx : g • (σ • x) - σ • x ∈ σ • Q' := AddSubgroup.mem_inertia.1 hg (σ • x)
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub, inv_smul_smul] at hx
  show (σ⁻¹ * g * σ) • x - x ∈ Q'
  rw [mul_smul, mul_smul]
  exact hx

/-- Boundary data at the chart `R0`: a `π₁(U)`-stable set `B` of boundary points of the pro-chart and
representatives `P s` of its `π₁^geo`-orbits (the geometric boundary points `s ∈ X̄ \ Ū` over this chart). -/
structure BdryData (S : Type) where
  B : Ideal (proChart A K R0) → Prop
  B_smul : ∀ (σ : Pi1 A K) (Q : Ideal (proChart A K R0)), B Q → B (σ • Q)
  P : S → Ideal (proChart A K R0)
  mem : ∀ s, B (P s)
  cover : ∀ Q, B Q → ∃ s, ∃ g ∈ pi1geo A K q, Q = g • P s
  disj : ∀ s t, ∀ g ∈ pi1geo A K q, P t = g • P s → s = t

variable {A K q R0} {S : Type} (D : BdryData A K q R0 S)

/-- The inertia group `I_s ⊆ π₁(U)` at the boundary point `P s` (review R5). -/
def BdryData.inertia (s : S) : Subgroup (Pi1 A K) := (D.P s).inertia (Pi1 A K)

end Boundary

/-! ## Curve cohomology and the geometric Frobenius -/

section Cohomology

variable {A K} {R0 : Type} [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)]
  [IsScalarTower R0 K (maxUnram A K)] {S : Type}
  {Λ : Type} [CommRing Λ] {M : Type} [AddCommGroup M] [Module Λ M] (ρ : Representation Λ (Pi1 A K) M)

/-- `H¹(U ⊗ 𝔽̄_q, M)` (continuous cohomology of `π₁^geo`). -/
abbrev curveH1 : Type := H1 ρ (pi1geo A K q)

/-- `H¹_par = image (H¹_c → H¹)`. -/
abbrev curveH1par (D : BdryData A K q R0 S) : Submodule Λ (curveH1 q ρ) := H1par ρ (pi1geo A K q) D.inertia

/-! ## Lisse coefficients -/

end Cohomology

/-! ## Sanity checks for the constant sheaf -/

section Sanity

variable {R0 : Type} [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)]
  [IsScalarTower R0 K (maxUnram A K)] {S : Type} (Λ : Type) [CommRing Λ]

end Sanity

end Geo

/-! ## The boundary at infinity (S3-Places) -/

section Infinity

variable (Fq : Type) [Field Fq] [DecidableEq (RatFunc Fq)] (A : Type) [CommRing A] [Algebra A (RatFunc Fq)]

end Infinity

end

end CurveCoh
end RamanujanPetersson


end

-- ===== S4.Def_RP_Kummer_Gal =====
section

/-!
# S4-Kummer, part 1: Kummer characters for a subgroup of a Galois group (generic field theory)

Setting: fields `K ⊆ E`, ANY subgroup `Γ ≤ Gal(E/K)` (later `π₁(U ⊗ F̄) ≤ π₁(U)`, with `E = K_U`), `N ≠ 0` and a
primitive `N`-th root of unity `ζ ∈ E` fixed by `Γ`.

* `epow ζ k = ζ ^ k` for `k : ZMod N`, `dlog` its inverse on `μ_N`;
* `rad Γ N`: the Kummer radicals, units `α` with `α ^ N` fixed by `Γ`;
* `kchar hζ α : Γ → ZMod N`, `σ α = ζ ^ (kchar α σ) α` (`kchar_spec`);
* `kchar_mul` / `kchar_mul_left`: additive in `σ` and in `α`; `kchar_eq_zero_iff`: `kchar α = 0 ↔ Γ fixes α`;
* `isLocallyConstant_kchar` (`E/K` integral, Krull topology);
* `exists_kchar_eq`: EVERY locally constant additive character `Γ → ZMod N` is a Kummer character (Hilbert 90 at a
  finite level, by Dedekind's independence of the finitely many `K`-embeddings `L₁ → E`; no normality needed);
* `kchar_conj`: equivariance, `kchar (φ α) σ = w * kchar α (φ⁻¹ σ φ)` when `φ ζ = ζ ^ w` and `φ` normalises `Γ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Kummer

noncomputable section

/-! ## Powers of `ζ` indexed by `ZMod N` and the discrete logarithm -/

section DLog

variable {E : Type} [Field E] {N : ℕ} [NeZero N] {ζ : E}

/-- `epow ζ k = ζ ^ k` for `k : ZMod N`. -/
def epow (ζ : E) (k : ZMod N) : E := ζ ^ k.val

theorem pow_mod_N (hζ : IsPrimitiveRoot ζ N) (m : ℕ) : ζ ^ (m % N) = ζ ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m N]
  rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

@[simp] theorem epow_zero : epow ζ (0 : ZMod N) = 1 := by
  simp [epow]

theorem epow_add (hζ : IsPrimitiveRoot ζ N) (a b : ZMod N) : epow ζ (a + b) = epow ζ a * epow ζ b := by
  unfold epow
  rw [ZMod.val_add, pow_mod_N hζ, pow_add]

theorem epow_ne_zero (hζ : IsPrimitiveRoot ζ N) (a : ZMod N) : epow ζ a ≠ 0 :=
  pow_ne_zero _ (hζ.ne_zero (NeZero.ne N))

theorem epow_pow_N (hζ : IsPrimitiveRoot ζ N) (a : ZMod N) : epow ζ a ^ N = 1 := by
  unfold epow
  rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]

theorem epow_injective (hζ : IsPrimitiveRoot ζ N) {a b : ZMod N} (h : epow ζ a = epow ζ b) : a = b :=
  ZMod.val_injective N (hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h)

theorem epow_neg_mul (hζ : IsPrimitiveRoot ζ N) (a : ZMod N) : epow ζ (-a) * epow ζ a = 1 := by
  rw [← epow_add hζ, neg_add_cancel, epow_zero]

theorem epow_pow (hζ : IsPrimitiveRoot ζ N) (w k : ZMod N) : epow ζ w ^ k.val = epow ζ (w * k) := by
  unfold epow
  rw [← pow_mul, ZMod.val_mul, pow_mod_N hζ]

open Classical in
/-- The discrete logarithm on `μ_N` (junk value `0` off `μ_N`). -/
def dlog (hζ : IsPrimitiveRoot ζ N) (x : E) : ZMod N :=
  if h : x ^ N = 1 then ((hζ.eq_pow_of_pow_eq_one h).choose : ZMod N) else 0

theorem epow_dlog (hζ : IsPrimitiveRoot ζ N) {x : E} (h : x ^ N = 1) : epow ζ (dlog hζ x) = x := by
  have hs := (hζ.eq_pow_of_pow_eq_one h).choose_spec
  unfold dlog epow
  rw [dif_pos h, ZMod.val_natCast, Nat.mod_eq_of_lt hs.1, hs.2]

theorem dlog_epow (hζ : IsPrimitiveRoot ζ N) (k : ZMod N) : dlog hζ (epow ζ k) = k :=
  epow_injective hζ (epow_dlog hζ (epow_pow_N hζ k))

end DLog

/-! ## Kummer radicals and Kummer characters -/

section Radicals

variable {K E : Type} [Field K] [Field E] [Algebra K E] (Γ : Subgroup (E ≃ₐ[K] E)) (N : ℕ)

/-- Kummer radicals: units `α` whose `N`-th power is fixed by `Γ`. -/
def rad : Subgroup Eˣ where
  carrier := {α | ∀ σ ∈ Γ, σ ((α : E) ^ N) = (α : E) ^ N}
  mul_mem' := by
    intro a b ha hb σ hσ
    simp only [Units.val_mul, mul_pow, map_mul, ha σ hσ, hb σ hσ]
  one_mem' := by
    intro σ _
    simp
  inv_mem' := by
    intro a ha σ hσ
    simp only [Units.val_inv_eq_inv_val, inv_pow, map_inv₀, ha σ hσ]

theorem mem_rad (α : Eˣ) : α ∈ rad Γ N ↔ ∀ σ ∈ Γ, σ ((α : E) ^ N) = (α : E) ^ N := Iff.rfl

/-- Units fixed by `Γ` (the multiplicative group of the fixed field). -/
def fixUnits : Subgroup Eˣ where
  carrier := {α | ∀ σ ∈ Γ, σ (α : E) = α}
  mul_mem' := by
    intro a b ha hb σ hσ
    simp only [Units.val_mul, map_mul, ha σ hσ, hb σ hσ]
  one_mem' := by
    intro σ _
    simp
  inv_mem' := by
    intro a ha σ hσ
    simp only [Units.val_inv_eq_inv_val, map_inv₀, ha σ hσ]

theorem mem_fixUnits (α : Eˣ) : α ∈ fixUnits Γ ↔ ∀ σ ∈ Γ, σ (α : E) = α := Iff.rfl

theorem fixUnits_le_rad : fixUnits Γ ≤ rad Γ N := by
  intro α hα σ hσ
  rw [map_pow, hα σ hσ]

variable {Γ N}

theorem ratio_pow {α : Eˣ} (hα : α ∈ rad Γ N) (σ : Γ) :
    ((σ : E ≃ₐ[K] E) (α : E) / α) ^ N = 1 := by
  rw [div_pow, ← map_pow, hα σ σ.2, div_self (pow_ne_zero _ α.ne_zero)]

variable [NeZero N] {ζ : E} (hζ : IsPrimitiveRoot ζ N)

/-- The Kummer character of `α`: `σ α = ζ ^ (kchar α σ) α`. -/
def kchar (α : Eˣ) (σ : Γ) : ZMod N := dlog hζ ((σ : E ≃ₐ[K] E) (α : E) / α)

theorem kchar_spec {α : Eˣ} (hα : α ∈ rad Γ N) (σ : Γ) :
    (σ : E ≃ₐ[K] E) (α : E) = epow ζ (kchar hζ α σ) * α := by
  rw [kchar, epow_dlog hζ (ratio_pow hα σ), div_mul_cancel₀ _ α.ne_zero]

theorem kchar_eq_iff {α : Eˣ} (hα : α ∈ rad Γ N) (σ : Γ) (k : ZMod N) :
    kchar hζ α σ = k ↔ (σ : E ≃ₐ[K] E) (α : E) = epow ζ k * α := by
  constructor
  · rintro rfl
    exact kchar_spec hζ hα σ
  · intro h
    rw [kchar, h, mul_div_cancel_right₀ _ α.ne_zero, dlog_epow]

theorem map_epow {σ : E ≃ₐ[K] E} (hσ : σ ζ = ζ) (k : ZMod N) : σ (epow ζ k) = epow ζ k := by
  unfold epow
  rw [map_pow, hσ]

variable (hζΓ : ∀ σ ∈ Γ, σ ζ = ζ)
include hζΓ

/-- `kchar α` is a homomorphism `Γ → ZMod N`. -/
theorem kchar_mul {α : Eˣ} (hα : α ∈ rad Γ N) (σ τ : Γ) :
    kchar hζ α (σ * τ) = kchar hζ α σ + kchar hζ α τ := by
  rw [kchar_eq_iff hζ hα, epow_add hζ]
  have e : ((σ * τ : Γ) : E ≃ₐ[K] E) (α : E) = (σ : E ≃ₐ[K] E) ((τ : E ≃ₐ[K] E) (α : E)) := rfl
  rw [e, kchar_spec hζ hα τ, map_mul, kchar_spec hζ hα σ, map_epow (hζΓ σ σ.2)]
  ring

theorem kchar_one {α : Eˣ} (hα : α ∈ rad Γ N) : kchar hζ α (1 : Γ) = 0 := by
  have h := kchar_mul hζ hζΓ hα 1 1
  rw [mul_one] at h
  linear_combination -h

end Radicals

section Radicals2

variable {K E : Type} [Field K] [Field E] [Algebra K E] {Γ : Subgroup (E ≃ₐ[K] E)} {N : ℕ} [NeZero N]
  {ζ : E} (hζ : IsPrimitiveRoot ζ N)

/-- `kchar` is additive in the radical. -/
theorem kchar_mul_left {α β : Eˣ} (hα : α ∈ rad Γ N) (hβ : β ∈ rad Γ N) (σ : Γ) :
    kchar hζ (α * β) σ = kchar hζ α σ + kchar hζ β σ := by
  rw [kchar_eq_iff hζ ((rad Γ N).mul_mem hα hβ), epow_add hζ, Units.val_mul, map_mul, kchar_spec hζ hα σ,
    kchar_spec hζ hβ σ]
  ring

theorem kchar_eq_zero_iff {α : Eˣ} (hα : α ∈ rad Γ N) :
    (∀ σ : Γ, kchar hζ α σ = 0) ↔ α ∈ fixUnits Γ := by
  constructor
  · intro h σ hσ
    have := (kchar_eq_iff hζ hα ⟨σ, hσ⟩ 0).1 (h ⟨σ, hσ⟩)
    rw [epow_zero, one_mul] at this
    exact this
  · intro h σ
    rw [kchar_eq_iff hζ hα, epow_zero, one_mul]
    exact h σ σ.2

theorem kchar_of_fix {α : Eˣ} (hα : α ∈ fixUnits Γ) (σ : Γ) : kchar hζ α σ = 0 :=
  (kchar_eq_zero_iff hζ (fixUnits_le_rad Γ N hα)).2 hα σ

/-- For `E/K` integral, `σ ↦ σ x` is locally constant on `Gal(E/K)` (Krull topology). -/
theorem isLocallyConstant_apply [Algebra.IsIntegral K E] (x : E) :
    IsLocallyConstant (fun σ : E ≃ₐ[K] E => σ x) := by
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro y
  rw [isOpen_iff_mem_nhds]
  intro σ₀ hσ₀
  have hσ₀' : σ₀ x = y := hσ₀
  have hS : IsOpen (MulAction.stabilizer (E ≃ₐ[K] E) x : Set (E ≃ₐ[K] E)) := stabilizer_isOpen_of_isIntegral x
  have hT : IsOpen ((fun τ => σ₀ * τ) '' (MulAction.stabilizer (E ≃ₐ[K] E) x : Set (E ≃ₐ[K] E))) :=
    isOpenMap_mul_left σ₀ _ hS
  refine Filter.mem_of_superset (hT.mem_nhds ⟨1, (MulAction.stabilizer (E ≃ₐ[K] E) x).one_mem, mul_one σ₀⟩) ?_
  rintro _ ⟨τ, hτ, rfl⟩
  have hτ' : τ x = x := hτ
  show (σ₀ * τ) x = y
  rw [AlgEquiv.mul_apply, hτ', hσ₀']

theorem isLocallyConstant_kchar [Algebra.IsIntegral K E] (α : Eˣ) : IsLocallyConstant (kchar hζ (Γ := Γ) α) := by
  have h1 : IsLocallyConstant (fun σ : Γ => (σ : E ≃ₐ[K] E) (α : E)) :=
    (isLocallyConstant_apply (α : E)).comp_continuous continuous_subtype_val
  exact h1.comp (fun y => dlog hζ (y / α))

/-- Kummer characters are equivariant: if `φ` normalises `Γ` and `φ ζ = ζ ^ w`, then
`kchar (φ α) σ = w * kchar α (φ⁻¹ σ φ)`. -/
theorem kchar_conj (φ : E ≃ₐ[K] E) (hφ : ∀ σ ∈ Γ, φ⁻¹ * σ * φ ∈ Γ) {w : ZMod N}
    (hw : φ ζ = epow ζ w) {α : Eˣ} (hα : α ∈ rad Γ N) (hφα : Units.map (φ : E →* E) α ∈ rad Γ N) (σ : Γ) :
    kchar hζ (Units.map (φ : E →* E) α) σ = w * kchar hζ α ⟨φ⁻¹ * (σ : E ≃ₐ[K] E) * φ, hφ σ σ.2⟩ := by
  rw [kchar_eq_iff hζ hφα]
  have e : (σ : E ≃ₐ[K] E) (φ (α : E)) = φ ((φ⁻¹ * σ * φ) (α : E)) := by
    rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply]
    congr 1
    group
  have e2 := kchar_spec hζ hα ⟨φ⁻¹ * (σ : E ≃ₐ[K] E) * φ, hφ σ σ.2⟩
  simp only [Units.coe_map, MonoidHom.coe_coe]
  rw [e]
  rw [show (φ⁻¹ * (σ : E ≃ₐ[K] E) * φ) (α : E) = _ from e2, map_mul]
  unfold epow
  rw [map_pow, hw]
  rw [show epow ζ w ^ (kchar hζ α ⟨φ⁻¹ * (σ : E ≃ₐ[K] E) * φ, hφ σ σ.2⟩).val = _ from epow_pow hζ _ _]
  rfl

/-! ## Surjectivity: every locally constant character is a Kummer character (Hilbert 90) -/

/-- Every locally constant additive character `c : Γ → ZMod N` is `kchar α` for a radical `α`. -/
theorem exists_kchar_eq (hζΓ : ∀ σ ∈ Γ, σ ζ = ζ) (c : Γ → ZMod N) (hc : IsLocallyConstant c)
    (hhom : ∀ σ τ : Γ, c (σ * τ) = c σ + c τ) : ∃ α ∈ rad Γ N, ∀ σ : Γ, kchar hζ α σ = c σ := by
  classical
  have hc1 : c 1 = 0 := by
    have h := hhom 1 1
    rw [mul_one] at h
    linear_combination -h
  have hcinv : ∀ σ : Γ, c σ⁻¹ = - c σ := by
    intro σ
    have h := hhom σ⁻¹ σ
    rw [inv_mul_cancel, hc1] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  -- a finite level `L₁` with `Fix(L₁) ∩ Γ ⊆ ker c`
  obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.mp (hc.isOpen_fiber (0 : ZMod N))
  have h1t : (1 : E ≃ₐ[K] E) ∈ t := by
    have : (1 : Γ) ∈ Subtype.val ⁻¹' t := by
      rw [hts]
      exact hc1
    exact this
  obtain ⟨L₁, hfin, hL₁⟩ := (krullTopology_mem_nhds_one_iff K E t).mp (ht.mem_nhds h1t)
  have hker : ∀ σ : Γ, (σ : E ≃ₐ[K] E) ∈ L₁.fixingSubgroup → c σ = 0 := by
    intro σ hσ
    have : σ ∈ Subtype.val ⁻¹' t := hL₁ hσ
    rw [hts] at this
    exact this
  -- restriction to `L₁`
  let res : Γ → (L₁ →ₐ[K] E) := fun σ => ((σ : E ≃ₐ[K] E) : E →ₐ[K] E).comp L₁.val
  have hres : ∀ σ τ : Γ, res σ = res τ → c σ = c τ := by
    intro σ τ h
    have hfix : ((σ⁻¹ * τ : Γ) : E ≃ₐ[K] E) ∈ L₁.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hx' : (σ : E ≃ₐ[K] E) x = (τ : E ≃ₐ[K] E) x := DFunLike.congr_fun h ⟨x, hx⟩
      show (σ : E ≃ₐ[K] E)⁻¹ ((τ : E ≃ₐ[K] E) x) = x
      rw [← hx', ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have h0 := hker _ hfix
    have h2 := hhom σ (σ⁻¹ * τ)
    rw [mul_inv_cancel_left, h0, add_zero] at h2
    exact h2.symm
  -- the coefficients
  let f : (L₁ →ₐ[K] E) → E := fun h => if hh : ∃ σ : Γ, res σ = h then epow ζ (-c hh.choose) else 0
  have f_res : ∀ σ : Γ, f (res σ) = epow ζ (-c σ) := by
    intro σ
    have hh : ∃ τ : Γ, res τ = res σ := ⟨σ, rfl⟩
    simp only [f, dif_pos hh]
    rw [hres _ _ hh.choose_spec]
  have hcomp : ∀ (σ τ : Γ), (((σ : E ≃ₐ[K] E) : E →ₐ[K] E).comp (res τ)) = res (σ * τ) := by
    intro σ τ
    ext x
    rfl
  have f_comp : ∀ (σ : Γ) (h : L₁ →ₐ[K] E),
      f ((((σ : E ≃ₐ[K] E) : E →ₐ[K] E).comp h)) = epow ζ (-c σ) * f h := by
    intro σ h
    by_cases hh : ∃ τ : Γ, res τ = h
    · obtain ⟨τ, rfl⟩ := hh
      rw [hcomp, f_res, f_res, hhom, neg_add, epow_add hζ]
    · have hh' : ¬ ∃ τ : Γ, res τ = (((σ : E ≃ₐ[K] E) : E →ₐ[K] E).comp h) := by
        rintro ⟨τ, hτ⟩
        apply hh
        refine ⟨σ⁻¹ * τ, ?_⟩
        rw [← hcomp, hτ]
        ext x
        show (σ : E ≃ₐ[K] E)⁻¹ ((σ : E ≃ₐ[K] E) (h x)) = h x
        rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
      simp only [f, dif_neg hh, dif_neg hh', mul_zero]
  -- Dedekind independence of the finitely many embeddings `L₁ → E`
  have : Finite (L₁ →ₐ[K] E) := Finite.algHom K L₁ E
  let _ : Fintype (L₁ →ₐ[K] E) := Fintype.ofFinite _
  have hLI : LinearIndependent E (fun h : L₁ →ₐ[K] E => (h : L₁ → E)) := by
    have := (linearIndependent_monoidHom L₁ E).comp (fun h : L₁ →ₐ[K] E => (h : L₁ →* E))
      (fun a b hab => AlgHom.ext fun x => DFunLike.congr_fun hab x)
    exact this
  have hsum : ∃ z : L₁, ∑ h, f h * h z ≠ 0 := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    have hz : ∑ h, f h • (h : L₁ → E) = 0 := by
      funext z
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact hcon z
    have := (Fintype.linearIndependent_iff.mp hLI) f hz (res 1)
    rw [f_res, hc1, neg_zero, epow_zero] at this
    exact one_ne_zero this
  obtain ⟨z, hz⟩ := hsum
  set β := ∑ h, f h * h z with hβdef
  have hfσ : ∀ (σ : Γ) (h : L₁ →ₐ[K] E), (σ : E ≃ₐ[K] E) (f h) = f h := by
    intro σ h
    by_cases hh : ∃ τ : Γ, res τ = h
    · simp only [f, dif_pos hh]
      exact map_epow (hζΓ σ σ.2) _
    · simp only [f, dif_neg hh, map_zero]
  have hσβ : ∀ σ : Γ, (σ : E ≃ₐ[K] E) β = epow ζ (c σ) * β := by
    intro σ
    let e : (L₁ →ₐ[K] E) ≃ (L₁ →ₐ[K] E) :=
      { toFun := fun h => (((σ : E ≃ₐ[K] E) : E →ₐ[K] E).comp h)
        invFun := fun h => ((((σ : E ≃ₐ[K] E)⁻¹ : E ≃ₐ[K] E) : E →ₐ[K] E).comp h)
        left_inv := fun h => by
          ext x
          show (σ : E ≃ₐ[K] E)⁻¹ ((σ : E ≃ₐ[K] E) (h x)) = h x
          rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
        right_inv := fun h => by
          ext x
          show (σ : E ≃ₐ[K] E) ((σ : E ≃ₐ[K] E)⁻¹ (h x)) = h x
          rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] }
    have step1 : (σ : E ≃ₐ[K] E) β = ∑ h, f h * (e h) z := by
      rw [hβdef, map_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [map_mul, hfσ]
      rfl
    have step2 : ∀ h, f h = epow ζ (c σ) * f (e h) := by
      intro h
      show f h = epow ζ (c σ) * f ((((σ : E ≃ₐ[K] E) : E →ₐ[K] E).comp h))
      rw [f_comp, ← mul_assoc, mul_comm (epow ζ (c σ)), epow_neg_mul hζ, one_mul]
    rw [step1]
    have step3 : ∑ h, f h * (e h) z = ∑ h, epow ζ (c σ) * (f (e h) * (e h) z) :=
      Finset.sum_congr rfl fun h _ => by rw [← mul_assoc, ← step2 h]
    rw [step3, ← Finset.mul_sum, Equiv.sum_comp e (fun h => f h * h z)]
  refine ⟨Units.mk0 β hz, ?_, ?_⟩
  · intro σ hσ
    rw [Units.val_mk0, map_pow, hσβ ⟨σ, hσ⟩, mul_pow, epow_pow_N hζ, one_mul]
  · intro σ
    rw [kchar_eq_iff hζ (by
      intro σ hσ
      rw [Units.val_mk0, map_pow, hσβ ⟨σ, hσ⟩, mul_pow, epow_pow_N hζ, one_mul]), Units.val_mk0]
    exact hσβ σ

end Radicals2

end

end Kummer
end RamanujanPetersson


end

-- ===== S4.Def_RP_Kummer_H1 =====
section

/-!
# S4-Kummer, part 2: `H¹(Γ, ZMod N)` is the Kummer group, with the Frobenius action

Setting of part 1 (`Def_RP_Kummer_Gal`): fields `K ⊆ E` with `E/K` integral, `Γ ≤ Gal(E/K)`, a primitive `N`-th root
of unity `ζ` fixed by `Γ`. Cohomology is the locally constant cohomology of `Def_RP_CurveCoh_Pair` with TRIVIAL
coefficients `ZMod N` (`triv K E N`).

* `B1_triv_eq_bot`, `H1mk_triv_injective`: with trivial coefficients there are no coboundaries;
* `kclass hζ hζΓ hα : H1 (triv K E N) Γ`: the class of the Kummer character of a radical `α`;
* `kummerEquiv`: **Kummer theory**, `rad Γ N / (Γ-fixed units) ≃* H¹(Γ, ZMod N)`;
* `frobH1_kclass`: for `ψ` with `ψ ζ = ζ ^ w'` (and `Γ` normal), `T_ψ [kchar α] = w • [kchar (ψ α)]` when `w w' = 1`;
* `geomFrob_kclass`: for an ARITHMETIC Frobenius `φ ζ = ζ ^ q`, the GEOMETRIC Frobenius `F = T_{φ⁻¹}` acts by
  `F [kchar α] = q • [kchar (φ⁻¹ α)]`: on `H¹(Γ, ZMod N) = (Kummer group) ⊗ μ_N^{⊗ -1}` the twist is the scalar `q`
  (review R4: eigenvalues `q / ω_i`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Kummer

open CurveCoh

noncomputable section

section Triv

variable (K E : Type) [Field K] [Field E] [Algebra K E] (N : ℕ)

/-- Trivial `ZMod N` coefficients for `Gal(E/K)`. -/
abbrev triv : Representation (ZMod N) (E ≃ₐ[K] E) (ZMod N) :=
  Representation.trivial (ZMod N) (E ≃ₐ[K] E) (ZMod N)

variable {K E} (Γ : Subgroup (E ≃ₐ[K] E))

theorem mem_Z1_triv (c : Γ → ZMod N) :
    c ∈ Z1 (triv K E N) Γ ↔ IsLocallyConstant c ∧ ∀ g h : Γ, c (g * h) = c g + c h := by
  rw [mem_Z1]
  simp only [triv, Representation.trivial_apply]

theorem B1_triv_eq_bot : B1 (triv K E N) Γ = ⊥ := by
  rw [eq_bot_iff]
  rintro c ⟨-, m, hm⟩
  rw [Submodule.mem_bot]
  funext g
  rw [hm g]
  simp [triv]

theorem H1mk_triv_injective : Function.Injective (H1.mk (triv K E N) Γ) := by
  rw [← LinearMap.ker_eq_bot, H1.mk, Submodule.ker_mkQ, B1_triv_eq_bot, Submodule.comap_bot,
    Submodule.ker_subtype]

end Triv

section Classes

variable {K E : Type} [Field K] [Field E] [Algebra K E] [Algebra.IsIntegral K E] {N : ℕ} [NeZero N]
  {Γ : Subgroup (E ≃ₐ[K] E)} {ζ : E} (hζ : IsPrimitiveRoot ζ N) (hζΓ : ∀ σ ∈ Γ, σ ζ = ζ)

include hζ hζΓ

theorem kchar_mem_Z1 {α : Eˣ} (hα : α ∈ rad Γ N) : kchar hζ (Γ := Γ) α ∈ Z1 (triv K E N) Γ :=
  (mem_Z1_triv N Γ _).2 ⟨isLocallyConstant_kchar hζ α, kchar_mul hζ hζΓ hα⟩

/-- The Kummer class `[kchar α] ∈ H¹(Γ, ZMod N)` of a radical `α`. -/
def kclass {α : Eˣ} (hα : α ∈ rad Γ N) : H1 (triv K E N) Γ :=
  H1.mk (triv K E N) Γ ⟨kchar hζ α, kchar_mem_Z1 hζ hζΓ hα⟩

theorem kclass_mul {α β : Eˣ} (hα : α ∈ rad Γ N) (hβ : β ∈ rad Γ N) :
    kclass hζ hζΓ ((rad Γ N).mul_mem hα hβ) = kclass hζ hζΓ hα + kclass hζ hζΓ hβ := by
  rw [kclass, kclass, kclass, ← map_add]
  congr 1
  apply Subtype.ext
  funext σ
  show kchar hζ (α * β) σ = kchar hζ α σ + kchar hζ β σ
  exact kchar_mul_left hζ hα hβ σ

theorem kclass_eq_zero_iff {α : Eˣ} (hα : α ∈ rad Γ N) : kclass hζ hζΓ hα = 0 ↔ α ∈ fixUnits Γ := by
  rw [kclass, map_eq_zero_iff _ (H1mk_triv_injective N Γ), Submodule.mk_eq_zero, funext_iff]
  exact kchar_eq_zero_iff hζ hα

/-- Every class is a Kummer class (Hilbert 90, `exists_kchar_eq`). -/
theorem kclass_surjective (x : H1 (triv K E N) Γ) : ∃ α : Eˣ, ∃ hα : α ∈ rad Γ N, kclass hζ hζΓ hα = x := by
  obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.mkQ_surjective _ x
  obtain ⟨α, hα, h⟩ := exists_kchar_eq hζ hζΓ c ((mem_Z1_triv N Γ c).1 hc).1 ((mem_Z1_triv N Γ c).1 hc).2
  refine ⟨α, hα, ?_⟩
  rw [kclass, H1.mk]
  congr 1
  apply Subtype.ext
  funext σ
  exact h σ

end Classes

section Frob

variable {K E : Type} [Field K] [Field E] [Algebra K E] [Algebra.IsIntegral K E] {N : ℕ} [NeZero N]
  {Γ : Subgroup (E ≃ₐ[K] E)} [hΓ : Γ.Normal] {ζ : E} (hζ : IsPrimitiveRoot ζ N) (hζΓ : ∀ σ ∈ Γ, σ ζ = ζ)

end Frob

end

end Kummer
end RamanujanPetersson


end

-- ===== S4.Def_RP_Kummer_Const =====
section

/-!
# S4-Kummer, part 3: constants are unramified; `μ_N ⊆ K_U`; the curve form of Kummer theory

`K` of characteristic `p`, `q = p ^ e` (`e > 0`), `A` any ring with `K = Frac`-like algebra `A → K` (no hypothesis on
`A` is needed: constant extensions are unramified over every `A`).

* `constLevel K p k = K(roots of X^(p^k) - X)` is a finite Galois subextension of `K̄/K` with trivial inertia at every
  prime of the integral closure of `A` (`constLevel_mem_unramSet`): an inertia element `σ` moves a root `s` to a root,
  `σ s - s` is again a root (Frobenius is additive), hence `0` or a unit, and it lies in the prime;
* `mem_maxUnram_of_isConst`: every constant of `K̄` lies in `K_U = maxUnram A K`;
* `exists_zeta`: for `N` prime to `p` there is a primitive `N`-th root of unity `ζ ∈ K_U` which is a constant;
  `zeta_fixed`: `π₁^geo` fixes it; `frobLift_zeta`: an arithmetic Frobenius lift sends `ζ ↦ ζ ^ q`;
* `curveKummerEquiv`: `H¹(U ⊗ 𝔽̄, ZMod N) ≃ rad / (π₁^geo-fixed units)`, and `geomFrobH1_kclass`:
  `F [kchar α] = q • [kchar (φ⁻¹ α)]` for the GEOMETRIC Frobenius of `Def_RP_CurveCoh_Curve` (review R4).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Kummer

open CurveCoh Polynomial

noncomputable section

/-- In a field, `y ^ n = y`, `y ≠ 0`, `1 ≤ n` give `y ^ (n - 1) = 1`. -/
theorem pow_pred_eq_one {F : Type} [Field F] {y : F} {n : ℕ} (hn : 1 ≤ n) (hy : y ^ n = y) (h0 : y ≠ 0) :
    y ^ (n - 1) = 1 := by
  have h : y ^ (n - 1) * y = 1 * y := by rw [← pow_succ, Nat.sub_add_cancel hn, hy, one_mul]
  exact mul_right_cancel₀ h0 h

section Level

variable (A K : Type) [CommRing A] [Field K] [Algebra A K] (p : ℕ) [hp : Fact p.Prime] [CharP K p]

/-- The constant level `K(𝔽_{p^k}) = K(roots of X^(p^k) - X)` inside `K̄`. -/
def constLevel (k : ℕ) : IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.adjoin K (((X : K[X]) ^ (p ^ k) - X).rootSet (AlgebraicClosure K))

variable {K p}

theorem one_lt_pow_p {k : ℕ} (hk : 0 < k) : 1 < p ^ k := Nat.one_lt_pow hk.ne' hp.out.one_lt

theorem mem_constLevel {k : ℕ} (hk : 0 < k) {x : AlgebraicClosure K} (hx : x ^ (p ^ k) = x) :
    x ∈ constLevel K p k := by
  refine IntermediateField.subset_adjoin _ _ ((mem_rootSet).2 ⟨FiniteField.X_pow_card_sub_X_ne_zero K
    (one_lt_pow_p hk), ?_⟩)
  simp [hx]

/-- **Constant extensions are unramified**: `K(𝔽_{p^k}) ∈ unramSet A K`. -/
theorem constLevel_mem_unramSet {k : ℕ} (hk : 0 < k) : constLevel K p k ∈ unramSet A K := by
  have hn : 1 < p ^ k := one_lt_pow_p hk
  have hsplit : ((X : K[X]) ^ (p ^ k) - X).IsSplittingField K (constLevel K p k) :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have hsep : ((X : K[X]) ^ (p ^ k) - X).Separable := galois_poly_separable p (p ^ k) (dvd_pow_self p hk.ne')
  set L := constLevel K p k with hL
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  refine ⟨hsplit.finiteDimensional _ _, IsGalois.of_separable_splitting_field hsep, fun Q hQ => ?_⟩
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  -- `σ` fixes every generator
  have hgen : ∀ y : L, ((y : AlgebraicClosure K)) ^ (p ^ k) = y → σ y = y := by
    intro y hy0
    have hyp : y ^ (p ^ k) = y := Subtype.ext hy0
    have hint : IsIntegral A y := by
      by_cases h0 : y = 0
      · rw [h0]
        exact isIntegral_zero
      · refine IsIntegral.of_pow (by omega : 0 < p ^ k - 1) ?_
        rw [pow_pred_eq_one hn.le hyp h0]
        exact isIntegral_one
    let yA : integralClosure A L := ⟨y, hint⟩
    have hd : σ • yA - yA ∈ Q := hσ yA
    have hdval : ((σ • yA - yA : integralClosure A L) : L) = σ y - y := rfl
    by_contra hne
    have hd0 : σ y - y ≠ 0 := sub_ne_zero.2 hne
    have hdp : (σ y - y) ^ (p ^ k) = σ y - y := by
      rw [sub_pow_char_pow, ← map_pow, hyp]
    have h1 : (σ • yA - yA) ^ (p ^ k - 1) ∈ Q := Ideal.pow_mem_of_mem Q hd _ (by omega)
    have h1' : (σ • yA - yA) ^ (p ^ k - 1) = 1 := by
      apply Subtype.val_injective
      change ((σ • yA - yA : integralClosure A L) : L) ^ (p ^ k - 1) = 1
      rw [hdval, pow_pred_eq_one hn.le hdp hd0]
    rw [h1'] at h1
    exact hQ.ne_top ((Ideal.eq_top_iff_one Q).2 h1)
  have hext : (L.val.comp (σ : L →ₐ[K] L)) = L.val := by
    refine IntermediateField.algHom_ext_of_eq_adjoin K hL (fun x hx => ?_)
    have hx' : x ^ (p ^ k) = x := by
      have := ((mem_rootSet).1 hx).2
      simpa [sub_eq_zero] using this
    simp only [AlgHom.comp_apply, IntermediateField.coe_val]
    rw [AlgEquiv.coe_toAlgHom, hgen _ hx']
  ext y
  have := congrArg (fun f : L →ₐ[K] AlgebraicClosure K => f y) hext
  simp only [AlgHom.comp_apply, IntermediateField.coe_val, AlgEquiv.coe_toAlgHom] at this
  rw [AlgEquiv.one_apply]
  exact this

theorem mem_maxUnram_of_pow {k : ℕ} (hk : 0 < k) {x : AlgebraicClosure K} (hx : x ^ (p ^ k) = x) :
    x ∈ maxUnram A K :=
  le_iSup (fun L : unramSet A K => (L : IntermediateField K (AlgebraicClosure K)))
    ⟨_, constLevel_mem_unramSet A hk⟩ (mem_constLevel hk hx)

/-- Every constant (`x ^ (q ^ n) = x`, `q = p ^ e`, `e, n > 0`) of `K̄` lies in `K_U`. -/
theorem mem_maxUnram_of_isConst {e : ℕ} (he : 0 < e) {x : AlgebraicClosure K} (hx : IsConst (p ^ e) x) :
    x ∈ maxUnram A K := by
  obtain ⟨n, hn, h⟩ := hx
  rw [← pow_mul] at h
  exact mem_maxUnram_of_pow A (Nat.mul_pos he hn) h

end Level

section Zeta

variable (A K : Type) [CommRing A] [Field K] [Algebra A K] (p : ℕ) [hp : Fact p.Prime] [CharP K p]
  {e : ℕ} (he : 0 < e) (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)

include hN in
theorem coprime_q : Nat.Coprime (p ^ e) N := by
  have h : ¬ p ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K p N).2 h)
  exact Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp.out).2 h)

include he hN in
/-- `K_U` contains a primitive `N`-th root of unity which is a constant. -/
theorem exists_zeta : ∃ ζ : maxUnram A K, IsPrimitiveRoot ζ N ∧ IsConst (p ^ e) ζ := by
  have : NeZero (N : AlgebraicClosure K) :=
    ⟨by rw [← map_natCast (algebraMap K (AlgebraicClosure K))]; exact (_root_.map_ne_zero _).2 hN⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (cyclotomic N (AlgebraicClosure K))
    (degree_cyclotomic_pos N (AlgebraicClosure K) (NeZero.pos N)).ne'
  have hzp : IsPrimitiveRoot z N := isRoot_cyclotomic_iff.1 hz
  have hpow : z ^ ((p ^ e) ^ Nat.totient N) = z := by
    have h := Nat.ModEq.pow_totient (coprime_q K p N hN (e := e))
    unfold Nat.ModEq at h
    rw [← pow_mod_N hzp, h, pow_mod_N hzp, pow_one]
  have htot : 0 < Nat.totient N := Nat.totient_pos.2 (NeZero.pos N)
  have hmem : z ∈ maxUnram A K := mem_maxUnram_of_isConst A he ⟨_, htot, hpow⟩
  refine ⟨⟨z, hmem⟩, ?_, ⟨_, htot, Subtype.ext hpow⟩⟩
  exact (IsPrimitiveRoot.map_iff_of_injective (ζ := (⟨z, hmem⟩ : maxUnram A K)) (f := (maxUnram A K).val)
    Subtype.val_injective).1 hzp

variable {A K p N}

theorem zeta_fixed {ζ : maxUnram A K} (hc : IsConst (p ^ e) ζ) : ∀ σ ∈ pi1geo A K (p ^ e), σ ζ = ζ :=
  fun σ hσ => (mem_pi1geo A K _ σ).1 hσ ζ hc

/-- An arithmetic Frobenius lift sends a constant primitive root `ζ` to `ζ ^ q`. -/
theorem frobLift_zeta {ζ : maxUnram A K} (hζ : IsPrimitiveRoot ζ N) (hc : IsConst (p ^ e) ζ) {φ : Pi1 A K}
    (hφ : IsFrobLift A K (p ^ e) φ) : φ ζ = epow ζ ((p ^ e : ℕ) : ZMod N) := by
  rw [hφ ζ hc, epow, ZMod.val_natCast, pow_mod_N hζ]

end Zeta

section Curve

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {q N : ℕ} [NeZero N] {ζ : maxUnram A K}
  (hζ : IsPrimitiveRoot ζ N) (hζΓ : ∀ σ ∈ pi1geo A K q, σ ζ = ζ)

instance maxUnram_isIntegral : Algebra.IsIntegral K (maxUnram A K) := inferInstance

end Curve

end

end Kummer
end RamanujanPetersson


end

-- ===== S4.Def_RP_Kummer_UnrCore =====
section

/-!
# S4-Kummer, part K4a (core): an inertia element fixes an `N`-th root of an `N`-th-power ideal class

* `eq_one_of_sub_mem`: `z ^ N = 1`, `z - 1 ∈ Q` (prime), `N` invertible ⇒ `z = 1` (geometric sum).
* `fixed_of_inertia`: `M ≤ L` in `K̄`, `σ ∈ Q.inertia Gal(L/K)` fixing `M`, `γ ^ N = a ∈ M` with
  `I ^ N * (a) = 1` for a fractional ideal `I` of `integralClosure A M`: then `σ γ = γ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Kummer

noncomputable section

/-- `z ^ N = 1` and `z ≡ 1` modulo a prime `Q` with `N` invertible force `z = 1`. -/
theorem eq_one_of_sub_mem {B : Type*} [CommRing B] [IsDomain B] {Q : Ideal B} [hQ : Q.IsPrime] {N : ℕ}
    (hN : IsUnit (N : B)) {z : B} (hz : z ^ N = 1) (hzQ : z - 1 ∈ Q) : z = 1 := by
  by_contra hne
  have hsum : ∑ i ∈ Finset.range N, z ^ i = 0 := by
    have h := geom_sum_mul z N
    rw [hz, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hne)
  have hmod : (Ideal.Quotient.mk Q) z = 1 := by
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk Q), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hzQ
  have hN0 : (Ideal.Quotient.mk Q) (N : B) = 0 := by
    have h := congrArg (Ideal.Quotient.mk Q) hsum
    simp only [map_sum, map_pow, hmod, one_pow, map_zero, Finset.sum_const, Finset.card_range] at h
    simpa using h
  rw [Ideal.Quotient.eq_zero_iff_mem] at hN0
  exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem Q hN0 hN)

section Core

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
variable {M L : IntermediateField K (AlgebraicClosure K)} (hML : M ≤ L)

/-- The `B_M`-submodule `{x ∈ M | x γⁿ ∈ Q}` of `M`. -/
def rootSub (Q : Ideal (integralClosure A L)) (γ : L) (n : ℕ) : Submodule (integralClosure A M) M where
  carrier := {x | ∃ q ∈ Q, ((q : integralClosure A L) : L) = IntermediateField.inclusion hML x * γ ^ n}
  add_mem' := by
    rintro x y ⟨q1, hq1, h1⟩ ⟨q2, hq2, h2⟩
    refine ⟨q1 + q2, Q.add_mem hq1 hq2, ?_⟩
    show (q1 : L) + (q2 : L) = _
    rw [h1, h2, map_add, add_mul]
  zero_mem' := ⟨0, Q.zero_mem, by simp⟩
  smul_mem' := by
    rintro b x ⟨q, hq, h⟩
    refine ⟨incl A K hML b * q, Q.mul_mem_left _ hq, ?_⟩
    show ((incl A K hML b : integralClosure A L) : L) * (q : L) = _
    rw [h, Algebra.smul_def, map_mul]
    have hb : ((incl A K hML b : integralClosure A L) : L) = IntermediateField.inclusion hML (b : M) := rfl
    rw [hb, mul_assoc]
    rfl

theorem mem_rootSub {Q : Ideal (integralClosure A L)} {γ : L} {n : ℕ} {x : M} :
    x ∈ rootSub hML Q γ n ↔
      ∃ q ∈ Q, ((q : integralClosure A L) : L) = IntermediateField.inclusion hML x * γ ^ n := Iff.rfl

/-- **Inertia fixes Kummer generators of `N`-th-power ideal classes.** -/
theorem fixed_of_inertia [IsFractionRing (integralClosure A M) M] {N : ℕ} [NeZero N] (hN : IsUnit (N : A)) (Q : Ideal (integralClosure A L))
    [hQ : Q.IsPrime] (σ : L ≃ₐ[K] L) (hσ : σ ∈ Q.inertia (L ≃ₐ[K] L))
    (hσM : ∀ x : M, σ (IntermediateField.inclusion hML x) = IntermediateField.inclusion hML x)
    {a : M} (I : FractionalIdeal (nonZeroDivisors (integralClosure A M)) M)
    (hI : I ^ N * FractionalIdeal.spanSingleton _ a = 1)
    (γ : L) (hγ : γ ^ N = IntermediateField.inclusion hML a) : σ γ = γ := by
  have hNpos : 0 < N := NeZero.pos N
  by_cases hγ0 : γ = 0
  · rw [hγ0, map_zero]
  by_contra hne
  have hI' : (I : Submodule (integralClosure A M) M) ^ N * Submodule.span (integralClosure A M) {a} = 1 := by
    rw [← FractionalIdeal.coe_pow, ← FractionalIdeal.coe_spanSingleton (nonZeroDivisors (integralClosure A M)) a, ← FractionalIdeal.coe_mul, hI,
      FractionalIdeal.coe_one]
  -- the root of unity `z = σ γ / γ`
  set z : L := σ γ / γ with hzdef
  have hσγ : σ γ = z * γ := by rw [hzdef, div_mul_cancel₀ _ hγ0]
  have hzN : z ^ N = 1 := by
    have h1 : (σ γ) ^ N = γ ^ N := by rw [← map_pow, hγ, hσM]
    rw [hσγ, mul_pow] at h1
    exact (mul_eq_right₀ (pow_ne_zero N hγ0)).1 h1
  have hzint : IsIntegral A z := IsIntegral.of_pow hNpos (by rw [hzN]; exact isIntegral_one)
  let zB : integralClosure A L := ⟨z, hzint⟩
  have hz1 : zB ≠ 1 := by
    intro h
    apply hne
    have hz : z = 1 := congrArg Subtype.val h
    rw [hσγ, hz, one_mul]
  have hNB : IsUnit (N : integralClosure A L) := by
    simpa using hN.map (algebraMap A (integralClosure A L))
  have hzB : zB ^ N = 1 := Subtype.ext (by simp [zB, hzN])
  have hzQ : zB - 1 ∉ Q := fun h => hz1 (eq_one_of_sub_mem hNB hzB h)
  -- every `e γ` with `e ∈ I` lies in `Q`
  have hW1 : (I : Submodule (integralClosure A M) M) ≤ rootSub hML Q γ 1 := by
    intro e he
    have hmem : e ^ N * a ∈ (1 : Submodule (integralClosure A M) M) := by
      rw [← hI']
      exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ he N) (Submodule.mem_span_singleton_self a)
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 hmem
    have hpow : (IntermediateField.inclusion hML e * γ) ^ N = IntermediateField.inclusion hML (b : M) := by
      rw [mul_pow, ← map_pow, hγ, ← map_mul]
      congr 1
      exact hb.symm
    have hbint : IsIntegral A (IntermediateField.inclusion hML (b : M)) :=
      (incl A K hML b).2
    have hint : IsIntegral A (IntermediateField.inclusion hML e * γ) :=
      IsIntegral.of_pow hNpos (by rw [hpow]; exact hbint)
    let y : integralClosure A L := ⟨_, hint⟩
    have hy : σ • y - y = (zB - 1) * y := by
      apply Subtype.ext
      show σ (IntermediateField.inclusion hML e * γ) - IntermediateField.inclusion hML e * γ =
        (z - 1) * (IntermediateField.inclusion hML e * γ)
      rw [map_mul, hσM, hσγ]
      ring
    have hyQ : σ • y - y ∈ Q := hσ y
    rw [hy] at hyQ
    refine ⟨y, (hQ.mem_or_mem hyQ).resolve_left hzQ, ?_⟩
    rw [pow_one]
  have hWn : ∀ n : ℕ, (I : Submodule (integralClosure A M) M) ^ (n + 1) ≤ rootSub hML Q γ (n + 1) := by
    intro n
    induction n with
    | zero => simpa using hW1
    | succ n ih =>
      rw [pow_succ]
      refine Submodule.mul_le.2 fun x hx y hy => ?_
      obtain ⟨q1, hq1, h1⟩ := ih hx
      obtain ⟨q2, hq2, h2⟩ := hW1 hy
      refine ⟨q1 * q2, Q.mul_mem_right _ hq1, ?_⟩
      show (q1 : L) * (q2 : L) = _
      rw [h1, h2, map_mul]
      ring
  obtain ⟨n, hn⟩ : ∃ n, N = n + 1 := ⟨N - 1, (Nat.succ_pred_eq_of_pos hNpos).symm⟩
  have hfin : (I : Submodule (integralClosure A M) M) ^ N * Submodule.span (integralClosure A M) {a} ≤
      rootSub hML Q γ 0 := by
    refine Submodule.mul_le.2 fun x hx y hy => ?_
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [hn] at hx
    obtain ⟨q, hq, h⟩ := hWn n hx
    refine ⟨incl A K hML b * q, Q.mul_mem_left _ hq, ?_⟩
    show ((incl A K hML b : integralClosure A L) : L) * (q : L) = _
    have hb : ((incl A K hML b : integralClosure A L) : L) = IntermediateField.inclusion hML (b : M) := rfl
    have hab : algebraMap (integralClosure A M) M b = (b : M) := rfl
    rw [hb, h, ← hn, hγ, pow_zero, mul_one, Algebra.smul_def, hab, map_mul, map_mul]
    ring
  have h1 : (1 : M) ∈ rootSub hML Q γ 0 := by
    apply hfin
    rw [hI']
    exact Submodule.one_le.1 le_rfl
  obtain ⟨q, hq, hq1⟩ := h1
  rw [map_one, pow_zero, one_mul] at hq1
  have : q = 1 := Subtype.ext hq1
  exact hQ.ne_top ((Ideal.eq_top_iff_one Q).2 (this ▸ hq))

end Core

end

end Kummer
end RamanujanPetersson


end

-- ===== S4.Def_RP_Kummer_Unr =====
section

/-!
# S4-Kummer, part K4a (assembly): Kummer roots of `N`-th-power ideal classes are unramified

* `mem_fixingSubgroup_adjoin`: an automorphism of `K̄` fixing `S` fixes `K(S)`.
* `lift_mem_fixingSubgroup`: a lift to `K̄` of an inertia element of `Gal(L/K)` fixes every unramified
  Galois subextension of `L` (the `key` step of `GalCover.sup_mem_unramSet`).
* `root_mem_maxUnram`: `M ∈ unramSet A K`, `0 ≠ a ∈ M`, `N` invertible in `A`, and for every `τ ∈ Gal(M/K)` a
  fractional ideal `I` of `integralClosure A M` with `I ^ N * (τ a) = 1`: every `γ ∈ K̄` with `γ ^ N = a` lies in
  `K_U = maxUnram A K`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Kummer

noncomputable section

variable {K : Type} [Field K]

/-- An automorphism of `K̄` fixing a generating set fixes the intermediate field it generates. -/
theorem mem_fixingSubgroup_adjoin {S : Set (AlgebraicClosure K)}
    {σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K} (h : ∀ x ∈ S, σ x = x) :
    σ ∈ (IntermediateField.adjoin K S).fixingSubgroup := by
  have hle : IntermediateField.adjoin K S ≤
      IntermediateField.fixedField (_root_.fixingSubgroup (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) S) := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro f hf
    exact (_root_.mem_fixingSubgroup_iff _).1 hf x hx
  exact (IntermediateField.le_iff_le _ _).1 hle ((_root_.mem_fixingSubgroup_iff _).2 h)

section Lift

variable (A : Type) [CommRing A] [Algebra A K]

/-- A lift `σ` to `K̄` of an inertia element `τ ∈ Gal(L/K)` fixes every unramified Galois subextension `L' ≤ L`. -/
theorem lift_mem_fixingSubgroup {L L' : IntermediateField K (AlgebraicClosure K)} (hle : L' ≤ L) [IsGalois K L']
    (uL : IsUnramifiedSub A K L') (Q : Ideal (integralClosure A L)) [hQ : Q.IsPrime] (τ : L ≃ₐ[K] L)
    (hτ : τ ∈ Q.inertia (L ≃ₐ[K] L)) (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hσ : ∀ y : L, σ (y : AlgebraicClosure K) = ((τ y : L) : AlgebraicClosure K)) : σ ∈ L'.fixingSubgroup := by
  have hP : (Q.comap (incl A K hle)).IsPrime := Ideal.IsPrime.comap _
  have hin : AlgEquiv.restrictNormalHom L' σ ∈ (Q.comap (incl A K hle)).inertia (L' ≃ₐ[K] L') := by
    intro y
    show (incl A K hle) (AlgEquiv.restrictNormalHom L' σ • y - y) ∈ Q
    have h : τ • incl A K hle y - incl A K hle y ∈ Q := hτ (incl A K hle y)
    convert h using 2
    apply Subtype.ext; apply Subtype.ext
    show ((AlgEquiv.restrictNormalHom L' σ (y : L') : L') : AlgebraicClosure K) - ((y : L') : AlgebraicClosure K)
      = ((τ (incl A K hle y : L) : L) : AlgebraicClosure K) - ((y : L') : AlgebraicClosure K)
    rw [AlgEquiv.restrictNormalHom_apply, ← hσ]
    rfl
  have h1 := uL _ hP
  rw [h1, Subgroup.mem_bot] at hin
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have := congrArg (fun e : L' ≃ₐ[K] L' => ((e ⟨x, hx⟩ : L') : AlgebraicClosure K)) hin
  simpa [AlgEquiv.restrictNormalHom_apply] using this

/-- **Kummer roots of `N`-th-power ideal classes are unramified.** -/
theorem root_mem_maxUnram {M : IntermediateField K (AlgebraicClosure K)} (hM : M ∈ unramSet A K)
    [IsFractionRing (integralClosure A M) M] {N : ℕ} [NeZero N] (hN : IsUnit (N : A)) {a : M} (ha : a ≠ 0)
    (hI : ∀ τ : M ≃ₐ[K] M, ∃ I : FractionalIdeal (nonZeroDivisors (integralClosure A M)) M,
      I ^ N * FractionalIdeal.spanSingleton _ (τ a) = 1)
    {γ : AlgebraicClosure K} (hγ : γ ^ N = (a : AlgebraicClosure K)) : γ ∈ maxUnram A K := by
  obtain ⟨fM, gM, uM⟩ := hM
  have hNK : (N : K) ≠ 0 := by
    have h := hN.map (algebraMap A K)
    rw [map_natCast] at h
    exact h.ne_zero
  have hNM : (N : M) ≠ 0 := by
    rw [← map_natCast (algebraMap K M)]
    exact (_root_.map_ne_zero _).2 hNK
  have haint : IsIntegral K (a : AlgebraicClosure K) := Algebra.IsIntegral.isIntegral _
  set P : K[X] := (minpoly K (a : AlgebraicClosure K)).comp (X ^ N) with hPdef
  have hP0 : P ≠ 0 := by
    apply Polynomial.ne_zero_of_natDegree_gt (n := 0)
    rw [hPdef, Polynomial.natDegree_comp, Polynomial.natDegree_X_pow]
    exact Nat.mul_pos (minpoly.natDegree_pos haint) (NeZero.pos N)
  -- every root of `P` is an `N`-th root of a Galois conjugate of `a`
  have hroot : ∀ y ∈ P.rootSet (AlgebraicClosure K), ∃ τ : M ≃ₐ[K] M,
      y ^ N = ((τ a : M) : AlgebraicClosure K) := by
    intro y hy
    have hy0 : aeval (y ^ N) (minpoly K (a : AlgebraicClosure K)) = 0 := by
      have h := (Polynomial.mem_rootSet.1 hy).2
      rwa [hPdef, Polynomial.aeval_comp, Polynomial.aeval_X_pow] at h
    have hsplit : ((minpoly K a).map (algebraMap K M)).Splits := Normal.splits inferInstance a
    rw [IntermediateField.minpoly_eq] at hsplit
    have hmem : y ^ N ∈ M := by
      refine (IntermediateField.splits_iff_mem (IsAlgClosed.splits _)).1 hsplit _ ?_
      exact Polynomial.mem_rootSet.2 ⟨minpoly.ne_zero haint, hy0⟩
    have hmin : minpoly K (⟨y ^ N, hmem⟩ : M) = minpoly K a := by
      rw [IntermediateField.minpoly_eq, IntermediateField.minpoly_eq]
      exact (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible haint) hy0 (minpoly.monic haint)).symm
    obtain ⟨τ, hτ⟩ := MulAction.mem_orbit_iff.1 ((Normal.minpoly_eq_iff_mem_orbit (F := K) (E := ↥M)).1 hmin)
    exact ⟨τ, by rw [← AlgEquiv.smul_def, hτ]⟩
  have hsep : ∀ y ∈ P.rootSet (AlgebraicClosure K), IsSeparable K y := by
    intro y hy
    obtain ⟨τ, hτ⟩ := hroot y hy
    have hb : τ a ≠ 0 := (_root_.map_ne_zero τ).2 ha
    have hpol : (X ^ N - C (τ a) : M[X]).Separable := separable_X_pow_sub_C (τ a) hNM hb
    have hay : aeval y (X ^ N - C (τ a) : M[X]) = 0 := by
      rw [map_sub, aeval_X_pow, aeval_C, hτ]
      exact sub_eq_zero.2 rfl
    have hsepM : IsSeparable M y := hpol.of_dvd (minpoly.dvd M y hay)
    exact IsSeparable.of_algebra_isSeparable_of_isSeparable (F := K) (E := M) hsepM
  set E : IntermediateField K (AlgebraicClosure K) := IntermediateField.adjoin K (P.rootSet (AlgebraicClosure K))
    with hEdef
  have hspl : IsSplittingField K E P := IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have : FiniteDimensional K E := IsSplittingField.finiteDimensional E P
  have : Normal K E := Normal.of_isSplittingField P
  have : Algebra.IsSeparable K E := (IntermediateField.isSeparable_adjoin_iff_isSeparable K (AlgebraicClosure K)).2 hsep
  have : IsGalois K E := ⟨⟩
  have hL : M ⊔ E ∈ unramSet A K := by
    refine ⟨inferInstance, inferInstance, fun Q hQ => ?_⟩
    rw [eq_bot_iff]
    intro τ hτ
    rw [Subgroup.mem_bot]
    obtain ⟨σ, hσ⟩ : ∃ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∀ y : ↥(M ⊔ E),
        σ (y : AlgebraicClosure K) = ((τ y : ↥(M ⊔ E)) : AlgebraicClosure K) :=
      ⟨τ.liftNormal (AlgebraicClosure K), fun y => τ.liftNormal_commutes (AlgebraicClosure K) y⟩
    have hσM : σ ∈ M.fixingSubgroup := lift_mem_fixingSubgroup A le_sup_left uM Q τ hτ σ hσ
    have hτM : ∀ x : M, τ (IntermediateField.inclusion (le_sup_left : M ≤ M ⊔ E) x) =
        IntermediateField.inclusion (le_sup_left : M ≤ M ⊔ E) x := by
      intro x
      apply Subtype.ext
      rw [← hσ]
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσM _ x.2
    have hσE : σ ∈ E.fixingSubgroup := by
      apply mem_fixingSubgroup_adjoin
      intro y hy
      obtain ⟨τ', hτ'⟩ := hroot y hy
      obtain ⟨I, hI'⟩ := hI τ'
      have hyL : y ∈ M ⊔ E := (le_sup_right : E ≤ M ⊔ E) (IntermediateField.subset_adjoin K _ hy)
      have hpow : (⟨y, hyL⟩ : ↥(M ⊔ E)) ^ N = IntermediateField.inclusion (le_sup_left : M ≤ M ⊔ E) (τ' a) :=
        Subtype.ext (by simpa using hτ')
      have hfix := fixed_of_inertia (le_sup_left : M ≤ M ⊔ E) hN Q τ hτ hτM I hI' ⟨y, hyL⟩ hpow
      have := hσ ⟨y, hyL⟩
      rw [hfix] at this
      exact this
    have hfix : σ ∈ (M ⊔ E).fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨hσM, hσE⟩
    ext y
    rw [AlgEquiv.one_apply, ← hσ]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hfix _ y.2
  have hγE : γ ∈ E := by
    apply IntermediateField.subset_adjoin
    refine Polynomial.mem_rootSet.2 ⟨hP0, ?_⟩
    rw [hPdef, Polynomial.aeval_comp, Polynomial.aeval_X_pow, hγ]
    exact minpoly.aeval K _
  exact le_iSup (fun L : unramSet A K => (L : IntermediateField K (AlgebraicClosure K))) ⟨_, hL⟩
    ((le_sup_right : E ≤ M ⊔ E) hγE)

end Lift

end

end Kummer
end RamanujanPetersson


end

-- ===== S4.Def_RP_Tsen_Zero =====
section

set_option autoImplicit false

/-!
# S4-PD (1), T1: common zeros over an algebraically closed field; the strong `C₁` property

* `exists_common_zero`: over an algebraically closed field `k`, `m` polynomials in `n > m` variables without constant
  term have a common nonzero zero (Krull's height theorem + the Nullstellensatz).
* `IsC1 K`: every polynomial in `n` variables over `K` with total degree `< n` and constant term `0` has a nonzero zero.
  (`IsC1.exists_zero_of_isHomogeneous`: the classical `C₁` property for forms.)
-/

namespace RamanujanPetersson.Tsen

open MvPolynomial

section Zero

variable {k : Type*} [Field k]

theorem ringKrullDim_mvPolynomial_fin (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) k) = n := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

end Zero

end RamanujanPetersson.Tsen


end


