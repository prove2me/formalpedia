-- Prove2me | Definitions.Def_RPLib_S4_KummerLev
-- name    : RPLib_S4_KummerLev
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:37:51.318328+00:00
-- url     : https://prove2.me/theorems/d8bc3a6c-ce6f-4793-b481-fd1f44869f64
-- title:
--   Kummer roots at a constant level $F \otimes \mathbb{F}_{q^m}$
-- statement:
--   For a function field $F/\mathbb{F}_q$, $A = R_{fin}(F)$ and the constant level $F_m = F \otimes \mathbb{F}_{q^m} \subseteq \overline{F}$, the file transports valuations along ring isomorphisms of Dedekind domains, shows that $x \in F'$ is integral over $R_{fin}(F)$ iff $x \in R_{fin}(F')$, identifies $F_m$ with the constant level $F(\mathbb{F}_{p^{em}})$ (unramified over $A$), shows the residue fields of $R_{fin}(F)$ are perfect, and proves for $a \in F_m^\times$ and $N$ invertible: $$N \mid \operatorname{ord}_v(a) \text{ at every finite place } v \text{ of } F_m \iff \text{every } N\text{-th root of } a \text{ lies in } K_U.$$
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Rosen, Number Theory in Function Fields, GTM 210, Springer (2002), Chapters 8 and 10

import Mathlib
import Definitions.Def_RPLib_S4_KummerRam
import Definitions.Def_RPLib_S4_KummerFix
import Definitions.Def_RPLib_S4_PicDescentD4b

/-!
# S4-Kummer, part K5b: Kummer roots at a constant level `F_m = F ⊗ 𝔽_{q^m}`

`A = Rfin(F)`, `K = F`, `F_m = Fc Fq F K̄ m ⊆ K̄ = AlgebraicClosure F`.

* `valuation_comap`: valuations are transported along a ring isomorphism of Dedekind domains that commutes with the maps to
  a common fraction field.
* `isIntegral_iff_mem_Rfin` (constant field extension `F'/F`): `x ∈ F'` is integral over `Rfin(F)` iff `x ∈ Rfin(F')`.
* `Fc_eq_constLevel`: `F_m = constLevel F p (e m)` when `#Fq = p ^ e`; `Fc_mem_unramSet`.
* `perfect_Rfin`: residue fields of `Rfin(F)` at maximal ideals are perfect (finite).
* `forall_dvd_ord_iff`: for `a ∈ F_m^×` and `N` invertible: `N ∣ ord_v a` at every finite place `v` of `F_m` iff every
  `N`-th root of `a` lies in `K_U = maxUnram (Rfin F) F`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain
open scoped Polynomial

namespace RamanujanPetersson
namespace Kummer

noncomputable section

section Transport

variable {B1 B2 M : Type*} [CommRing B1] [IsDedekindDomain B1] [CommRing B2] [IsDedekindDomain B2]
  [Field M] [Algebra B1 M] [Algebra B2 M] [IsFractionRing B1 M] [IsFractionRing B2 M]

theorem intValuation_comap (e : B1 ≃+* B2) (w : HeightOneSpectrum B2) (b : B1) :
    (HeightOneSpectrum.comap (e : B1 →+* B2) e.surjective w).intValuation b = w.intValuation (e b) := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have heb : e b ≠ 0 := fun h => hb (e.injective (h.trans (map_zero e).symm))
  rw [HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hb,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ heb]
  congr 3
  apply multiplicity_eq_of_emultiplicity_eq
  rw [emultiplicity_eq_emultiplicity_iff]
  intro n
  have hpow : (HeightOneSpectrum.comap (e : B1 →+* B2) e.surjective w).asIdeal ^ n =
      (w.asIdeal ^ n).comap (e : B1 →+* B2) := by
    change (w.asIdeal.comap e) ^ n = (w.asIdeal ^ n).comap e
    rw [← Ideal.map_symm, ← Ideal.map_symm, Ideal.map_pow]
  rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.span_le, Ideal.span_le, Set.singleton_subset_iff,
    Set.singleton_subset_iff, hpow]
  exact Iff.rfl

/-- **Transport of valuations** along `e : B1 ≃+* B2` compatible with the maps to `M`. -/
theorem valuation_comap (e : B1 ≃+* B2) (he : ∀ b, algebraMap B2 M (e b) = algebraMap B1 M b)
    (w : HeightOneSpectrum B2) (x : M) :
    (HeightOneSpectrum.comap (e : B1 →+* B2) e.surjective w).valuation M x = w.valuation M x := by
  obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := B1) x
  rw [map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_comap, intValuation_comap, ← he a, ← he s,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]

end Transport

section Generic

open PicDescent Places

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

/-- In a constant field extension `F'/F`, the integral closure of `Rfin(F)` in `F'` is `Rfin(F')`. -/
theorem isIntegral_iff_mem_Rfin (h : RR.IsConstExt Fq F L F' c) (x : F') :
    IsIntegral (Rfin Fq F) x ↔ IsIntegral L[X] x := by
  constructor
  · intro hx
    letI := algFin h
    haveI := towerFin h
    refine isIntegral_of_forall_algebraMap (A := Rfin Fq F) (fun a => ?_) hx
    rw [IsScalarTower.algebraMap_apply (Rfin Fq F) (Rfin L F') F']
    exact (algebraMap (Rfin Fq F) (Rfin L F') a).2
  · intro hx
    letI := algFin h
    haveI := towerFin h
    haveI := isIntegral_AA' h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin
    exact (Algebra.IsIntegral.isIntegral (R := Rfin Fq F) (⟨x, hx⟩ : Rfin L F')).algebraMap

end Generic

section GenericLev

variable {K : Type} [Field K] (A : Type) [CommRing A] [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]

/-- Generic Kummer criterion at a finite level `M ∈ unramSet`, for any Dedekind model `B` of the integral closure of `A`
in `M` (given by its image in `M`). -/
theorem forall_dvd_iff_of_range {M : IntermediateField K (AlgebraicClosure K)} (hM : M ∈ unramSet A K)
    (hperf : ∀ (p : Ideal A) [p.IsMaximal], PerfectField p.ResidueField) {N : ℕ} [NeZero N] (hN : IsUnit (N : A))
    {a : M} (ha : a ≠ 0) {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B M] [IsFractionRing B M]
    (hB : ∀ x : M, IsIntegral A x ↔ x ∈ (algebraMap B M).range) (hBinj : Function.Injective (algebraMap B M)) :
    (∀ v : HeightOneSpectrum B, (N : ℤ) ∣ WithZero.log (v.valuation M a)) ↔
      ∀ γ : AlgebraicClosure K, γ ^ N = (a : AlgebraicClosure K) → γ ∈ maxUnram A K := by
  haveI : FiniteDimensional K M := hM.1
  haveI : IsGalois K M := hM.2.1
  haveI : IsFractionRing (integralClosure A M) M := integralClosure.isFractionRing_of_finite_extension (A := A) K M
  haveI : IsDedekindDomain (integralClosure A M) := integralClosure.isDedekindDomain (A := A) (K := K) (L := M)
  have hrange : (integralClosure A M).toSubring = (algebraMap B M).range :=
    Subring.ext fun x => hB x
  let e1 : integralClosure A M ≃+* (algebraMap B M).range := RingEquiv.subringCongr hrange
  let e2 : B ≃+* (algebraMap B M).range := RingEquiv.ofBijective (algebraMap B M).rangeRestrict
    ⟨fun x y hxy => hBinj (congrArg Subtype.val hxy), RingHom.rangeRestrict_surjective _⟩
  let eR : integralClosure A M ≃+* B := e1.trans e2.symm
  have heR : ∀ x, algebraMap B M (eR x) = algebraMap (integralClosure A M) M x := fun x =>
    congrArg Subtype.val (e2.apply_symm_apply (e1 x))
  have heR' : ∀ b, algebraMap (integralClosure A M) M (eR.symm b) = algebraMap B M b := fun b => by
    rw [← heR, RingEquiv.apply_symm_apply]
  constructor
  · intro hv γ hγ
    refine root_mem_maxUnram_of_dvd A hM hN ha (fun v => ?_) hγ
    have h1 := hv (HeightOneSpectrum.comap (eR.symm : B →+* integralClosure A M) eR.symm.surjective v)
    rwa [valuation_comap eR.symm heR' v] at h1
  · intro hroot v
    obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq (a : AlgebraicClosure K) (NeZero.pos N)
    have h1 := dvd_log_valuation_of_mem_maxUnram A hM hperf (hroot γ hγ) hγ
      (HeightOneSpectrum.comap (eR : integralClosure A M →+* B) eR.surjective v)
    rwa [valuation_comap eR heR v] at h1

end GenericLev

section Lev

open PicDescent Places

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- Residue fields of `Rfin(F)` at maximal ideals are finite, hence perfect. -/
theorem perfect_Rfin : ∀ (P : Ideal (Rfin Fq F)) [P.IsMaximal], PerfectField P.ResidueField := by
  intro P hP
  have hne : P ≠ ⊥ := by
    rintro rfl
    have hfield : IsField (Rfin Fq F) := Ring.isField_iff_maximal_bot.2 hP
    have hinj : Function.Injective (algebraMap Fq[X] (Rfin Fq F)) := by
      intro a b hab
      apply FaithfulSMul.algebraMap_injective Fq[X] F
      rw [IsScalarTower.algebraMap_apply Fq[X] (Rfin Fq F) F, hab,
        ← IsScalarTower.algebraMap_apply Fq[X] (Rfin Fq F) F]
    exact Polynomial.not_isField Fq (isField_of_isIntegral_of_isField hinj hfield)
  obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  haveI := Places.FiniteQuot.finite (S := Rfin Fq F) a ha0
  haveI : Finite (Rfin Fq F ⧸ P) :=
    Finite.of_surjective _ (Ideal.Quotient.factor_surjective ((Ideal.span_singleton_le_iff_mem _).mpr haP))
  haveI : Finite P.ResidueField :=
    Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField P).2
  infer_instance

variable {Fq F} {p e : ℕ} [Fact p.Prime] [CharP F p]

/-- The constant level `F_m` is `constLevel F p (e m)` (with `#Fq = p ^ e`). -/
theorem Fc_eq_constLevel (hq : Fintype.card Fq = p ^ e) {m : ℕ} (hm : 0 < e * m) :
    Fc Fq F (AlgebraicClosure F) m = constLevel F p (e * m) := by
  have hS : ((Lc Fq (AlgebraicClosure F) m : IntermediateField Fq (AlgebraicClosure F)) : Set (AlgebraicClosure F)) =
      ((Polynomial.X : F[X]) ^ (p ^ (e * m)) - Polynomial.X).rootSet (AlgebraicClosure F) := by
    ext x
    rw [SetLike.mem_coe, mem_Lc, Polynomial.mem_rootSet, hq, ← pow_mul]
    simp only [map_sub, map_pow, Polynomial.aeval_X, sub_eq_zero]
    constructor
    · intro h
      exact ⟨FiniteField.X_pow_card_sub_X_ne_zero F (one_lt_pow_p (p := p) hm), h⟩
    · intro h
      exact h.2
  rw [Fc, constLevel, hS]

theorem Fc_mem_unramSet (hq : Fintype.card Fq = p ^ e) (he : 0 < e) (m : ℕ) [NeZero m] :
    Fc Fq F (AlgebraicClosure F) m ∈ unramSet (Rfin Fq F) F := by
  rw [Fc_eq_constLevel hq (Nat.mul_pos he (NeZero.pos m))]
  exact constLevel_mem_unramSet (Rfin Fq F) (Nat.mul_pos he (NeZero.pos m))

/-- **Kummer criterion at a constant level**: for `a ∈ F_m^×` and `N` invertible, `N` divides `ord_v a` at every finite
place `v` of `F_m` iff every `N`-th root of `a` lies in `K_U`. -/
theorem forall_dvd_ord_iff (hk : constField Fq F = ⊥) (hq : Fintype.card Fq = p ^ e) (he : 0 < e) (m : ℕ) [NeZero m]
    {N : ℕ} [NeZero N] (hN : IsUnit (N : Rfin Fq F)) {a : Fc Fq F (AlgebraicClosure F) m} (ha : a ≠ 0) :
    (∀ v : HeightOneSpectrum (Rfin (Lc Fq (AlgebraicClosure F) m) (Fc Fq F (AlgebraicClosure F) m)),
      (N : ℤ) ∣ Places.ord v a) ↔
    ∀ γ : AlgebraicClosure F, γ ^ N = (a : AlgebraicClosure F) → γ ∈ maxUnram (Rfin Fq F) F := by
  have hB : ∀ x : Fc Fq F (AlgebraicClosure F) m, IsIntegral (Rfin Fq F) x ↔
      x ∈ (algebraMap (Rfin (Lc Fq (AlgebraicClosure F) m) (Fc Fq F (AlgebraicClosure F) m))
        (Fc Fq F (AlgebraicClosure F) m)).range := by
    intro x
    refine (isIntegral_iff_mem_Rfin (isConstExt_Fc Fq F (AlgebraicClosure F) hk m) x).trans ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, ?_⟩
    rintro ⟨y, rfl⟩
    exact y.2
  refine (forall_congr' fun v => ?_).trans
    (forall_dvd_iff_of_range (Rfin Fq F) (Fc_mem_unramSet hq he m) (perfect_Rfin Fq F) hN ha hB Subtype.val_injective)
  rw [Places.ord]
  exact dvd_neg

end Lev

end

end Kummer
end RamanujanPetersson


