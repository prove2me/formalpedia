-- Prove2me | Definitions.Def_RPLib_S3_SBClosB
-- name    : RPLib_S3_SBClosB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:40:22.519583+00:00
-- url     : https://prove2.me/theorems/8df577b4-edbb-466b-947b-744d78c43bf5
-- title:
--   Weight-two Ramanujan-Petersson library: S3-ZetaSB, E1 part B: a place of `GalE Fq F n` of degree `ℓ(0)`
-- statement:
--   S3-ZetaSB, E1 part B: a place of `GalE Fq F n` of degree `ℓ(0)`.
--
--   Pick a finite place `P` of `E0 = GalE0 Fq F`, of degree `n + 1`, and a place `Q` of `E = GalE Fq F n` over it. A
--   Frobenius element `σ ∈ Gal(E/E0)` at `Q` (Mathlib `IsArithFrobAt.exists_of_isInvariant`) fixes the roots of
--   `X ^ (q ^ (n+1)) - X` (two roots differ by a constant, a unit), hence all of `E`, so `x ^ (q ^ (n+1)) = x` on the residue
--   field: `deg Q ∣ n + 1`. The `q ^ (n+1)` roots are constants, so `n + 1 ≤ ℓ0`, and `ℓ0 ∣ deg Q`: `deg Q = ℓ0 = ℓ(0)`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer 2009, Chapters 1 and 5; E. Bombieri, Counting points on curves over finite fields (d'après S. A. Stepanov), Séminaire Bourbaki 430 (1973); A. Weil, Sur les courbes algébriques et les variétés qui s'en déduisent, Hermann 1948

import Mathlib
import Definitions.Def_RPLib_S3_SBClosA

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


