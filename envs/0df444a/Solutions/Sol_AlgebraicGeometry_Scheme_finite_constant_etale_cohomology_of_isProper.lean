-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.finite_constant_etale_cohomology_of_isProper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-19T20:45:37.330083+00:00
-- url     : https://prove2.me/submissions/59ebd368-b61f-45fb-a232-8050a8684d2d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AlgebraicGeometry_Scheme_finite_prime_constant_etale_cohomology_in_characteristic
import Theorems.Thm_AlgebraicGeometry_Scheme_finite_prime_constant_etale_cohomology_prime_to_characteristic
import Mathlib

set_option autoImplicit false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped QuotientAddGroup

universe u

namespace PhilipponEtalePrimeCoefficients

private theorem finite_middle {X : Scheme.{u}} (S : ShortComplex AddCommGrpCat.{u})
    (hS : S.ShortExact) (q : ℕ)
    (h₁ : Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat).obj S.X₁).H q))
    (h₃ : Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat).obj S.X₃).H q)) :
    Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat).obj S.X₂).H q) := by
  let F := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}
  letI : PreservesFiniteLimits F := inferInstanceAs
    (PreservesFiniteLimits (Functor.const _ ⋙ presheafToSheaf _ AddCommGrpCat.{u}))
  letI : PreservesFiniteColimits F := inferInstanceAs
    (PreservesFiniteColimits (Functor.const _ ⋙ presheafToSheaf _ AddCommGrpCat.{u}))
  let T := S.map F
  have hT : T.ShortExact := hS.map_of_exact F
  let f := Sheaf.H.map T.f q
  let g := Sheaf.H.map T.g q
  letI := @Fintype.ofFinite (T.X₁.H q) h₁
  letI := @Fintype.ofFinite (T.X₃.H q) h₃
  apply @Finite.of_fintype _ (AddGroup.fintypeOfKerLeRange f g ?_)
  intro y hy
  exact Abelian.Ext.covariant_sequence_exact₂ _ hT y hy

private theorem finite_of_equiv {X : Scheme.{u}} {A B : AddCommGrpCat.{u}} (e : A ≃+ B) (q : ℕ)
    (h : Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat).obj A).H q)) :
    Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat).obj B).H q) := by
  let F := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
    Sheaf.functorH X.smallEtaleTopology q
  let i := F.mapIso e.toAddCommGrpIso
  exact @Finite.of_injective _ _ h i.inv (AddCommGrpCat.mono_iff_injective _ |>.mp inferInstance)

private theorem finite_quotient_step {X : Scheme.{u}} {A : AddCommGrpCat.{u}} (B : AddSubgroup A)
    (q : ℕ)
    (hB : Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat).obj
      (AddCommGrpCat.of B)).H q))
    (hQ : Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat).obj
      (AddCommGrpCat.of (A ⧸ B))).H q)) :
    Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat).obj A).H q) := by
  let S : ShortComplex AddCommGrpCat.{u} :=
    ShortComplex.mk (AddCommGrpCat.ofHom B.subtype)
      (AddCommGrpCat.ofHom (QuotientAddGroup.mk' B)) (by
        ext x
        exact (QuotientAddGroup.eq_zero_iff (N := B) x.val).mpr x.property)
  have hS : S.ShortExact := by
    letI : Mono S.f := (AddCommGrpCat.mono_iff_injective _).mpr Subtype.val_injective
    letI : Epi S.g := (AddCommGrpCat.epi_iff_surjective _).mpr QuotientAddGroup.mk_surjective
    refine { exact := (ShortComplex.ab_exact_iff_function_exact S).mpr ?_ }
    intro x
    change (x : A ⧸ B) = 0 ↔ ∃ b : B, b.val = x
    exact (QuotientAddGroup.eq_zero_iff x).trans
      ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨b, hb⟩ => hb ▸ b.property⟩
  exact finite_middle S hS q hB hQ

/-- Prime-order coefficient groups suffice in each fixed cohomological degree. -/
theorem finite_of_prime {X : Scheme.{u}} (q : ℕ)
    (hp : ∀ p : ℕ, p.Prime →
      Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat).obj
        (AddCommGrpCat.of (ULift.{u} (ZMod p)))).H q))
    (A : AddCommGrpCat.{u}) [Finite A] :
    Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat).obj A).H q) := by
  classical
  generalize hn : Nat.card A = n
  induction n using Nat.strong_induction_on generalizing A with
  | h n ih =>
    by_cases hA : Subsingleton A
    · have h₀ : IsZero A := AddCommGrpCat.isZero_of_subsingleton A
      letI := Sheaf.subsingleton_H_of_isZero
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat).map_isZero h₀) q
      infer_instance
    · haveI : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
      obtain ⟨p, hprime, hdvd⟩ := Nat.exists_prime_and_dvd
        (Nat.ne_of_gt (Finite.one_lt_card (α := A)))
      letI : Fact p.Prime := ⟨hprime⟩
      obtain ⟨a, ha⟩ := exists_prime_addOrderOf_dvd_card' p hdvd
      let B := AddSubgroup.zmultiples a
      have hcard : Nat.card B = p := (Nat.card_zmultiples a).trans ha
      have e : ULift.{u} (ZMod p) ≃+ B :=
        (AddEquiv.ulift : ULift.{u} (ZMod p) ≃+ ZMod p).trans
          (zmodAddEquivOfGenerator (g := ⟨a, AddSubgroup.mem_zmultiples a⟩) (by
            intro b
            obtain ⟨j, hj⟩ := AddSubgroup.mem_zmultiples_iff.mp b.property
            exact AddSubgroup.mem_zmultiples_iff.mpr ⟨j, Subtype.ext hj⟩) hcard)
      apply finite_quotient_step B q (finite_of_equiv e q (hp p hprime))
      apply ih (Nat.card (A ⧸ B)) ?_ (AddCommGrpCat.of (A ⧸ B)) rfl
      rw [← hn, AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup B, hcard]
      exact lt_mul_of_one_lt_right Nat.card_pos hprime.one_lt

end PhilipponEtalePrimeCoefficients

theorem solution
    (K : Type u) [Field K] [IsSepClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π] (A : AddCommGrpCat.{u}) [Finite A] (q : ℕ) :
    Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat).obj A).H q) := by
  apply PhilipponEtalePrimeCoefficients.finite_of_prime q _ A
  intro p hp
  by_cases h : (p : K) = 0
  · exact Scheme.finite_prime_constant_etale_cohomology_in_characteristic K π p hp h q
  · exact Scheme.finite_prime_constant_etale_cohomology_prime_to_characteristic K π p hp h q
