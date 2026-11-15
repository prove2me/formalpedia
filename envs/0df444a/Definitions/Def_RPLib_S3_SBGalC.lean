-- Prove2me | Definitions.Def_RPLib_S3_SBGalC
-- name    : RPLib_S3_SBGalC
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:36:32.023017+00:00
-- url     : https://prove2.me/theorems/4eb118ac-6ca3-479f-845f-daa58512f5e0
-- title:
--   Weight-two Ramanujan-Petersson library: S3-ZetaSB, E2b part C: the Galois-twist lower bound for a Galois function field
-- statement:
--   S3-ZetaSB, E2b part C: the Galois-twist lower bound for a Galois function field.
--
--   For `F ⊆ E` with `E / K` Galois (`K = RatFunc Fq`, group `G`, `Hs = Gal(E/F)` as the fixing subgroup of `ι F`):
--   * `constRes : G →* Aut(k'/Fq)` (restriction to the constant field `k'` of `E`) has range of size `ℓ0 = [k' : Fq]`
--     (`card_gal_eq : |G| = ℓ0 |ker|`), and `|Hs| ≤ ℓ0 |Hs ⊓ ker|`;
--   * the `F`-side count `Σ_{h ∈ Hs} N(h) ≤ |Hs| · N_m(F)` and the `K`-side count `|G| q ^ m ≤ Σ_{g ∈ G} N(g)`;
--   * `lower_bound_core`: `q ^ m ≤ N_m(F) + |G| (2 g_E + 1) q ^ (m/2)` when `q ^ m = Q0 ^ 2` is large and `E` has a
--     place of degree `ℓ0`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer 2009, Chapters 1 and 5; E. Bombieri, Counting points on curves over finite fields (d'après S. A. Stepanov), Séminaire Bourbaki 430 (1973); A. Weil, Sur les courbes algébriques et les variétés qui s'en déduisent, Hermann 1948

import Mathlib
import Definitions.Def_RPLib_S3_SBGalB

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

instance finite_constField : Finite (Places.constField Fq E) := Module.finite_of_finite Fq

variable (Fq E) in
/-- Restriction of `Gal(E/K)` to the constant field `k'` of `E`. -/
noncomputable def constRes :
    (E ≃ₐ[RatFunc Fq] E) →* (Places.constField Fq E ≃ₐ[Fq] Places.constField Fq E) :=
  (AlgEquiv.restrictNormalHom (Places.constField Fq E)).comp (AlgEquiv.restrictScalarsHom Fq)

theorem constRes_apply (g : E ≃ₐ[RatFunc Fq] E) (c : Places.constField Fq E) :
    ((constRes Fq E g c : Places.constField Fq E) : E) = g c := by
  change ((AlgEquiv.restrictNormalHom (Places.constField Fq E) (AlgEquiv.restrictScalarsHom Fq g) c :
    Places.constField Fq E) : E) = g c
  rw [AlgEquiv.restrictNormalHom_apply]
  rfl

theorem mem_ker_constRes (g : E ≃ₐ[RatFunc Fq] E) :
    g ∈ (constRes Fq E).ker ↔ ∀ c : Places.constField Fq E, g (c : E) = c := by
  rw [MonoidHom.mem_ker, AlgEquiv.ext_iff]
  refine forall_congr' fun c => ?_
  rw [AlgEquiv.one_apply, ← constRes_apply, Subtype.ext_iff]

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

variable (Fq) in
/-- `ι : F → E` on the rings of finite integers. -/
noncomputable def finMap (ι : F →ₐ[RatFunc Fq] E) : Places.Rfin Fq F →ₐ[Fq[X]] Places.Rfin Fq E :=
  (ι.restrictScalars Fq[X]).mapIntegralClosure

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

theorem frob_pow_apply (m : ℕ) (x : L) :
    (FiniteField.frobeniusAlgHom Fq L ^ m) x = x ^ (Fintype.card Fq ^ m) := by
  rw [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate]

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


