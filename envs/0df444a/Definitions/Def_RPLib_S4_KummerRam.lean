-- Prove2me | Definitions.Def_RPLib_S4_KummerRam
-- name    : RPLib_S4_KummerRam
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:27:57.757328+00:00
-- url     : https://prove2.me/theorems/00ef7e40-becb-430e-b881-278aae1519f9
-- title:
--   Kummer radicals inside unramified extensions have $N$-divisible valuations
-- statement:
--   Let $A$ be a Dedekind domain with fraction field $K$ and perfect residue fields. The file proves that every nonzero prime of the integral closure of $A$ in a finite Galois subextension $L \subseteq \overline{K}$ unramified over $A$ has ramification index $1$ (trivial inertia), and that if $M \le L$ are both unramified, $\alpha \in L$ and $\alpha^N = a \in M$, then $$N \mid \log v(a)$$ at every prime $v$ of the integral closure of $A$ in $M$; the same holds for $\alpha \in K_U$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. Neukirch, Algebraic Number Theory, Grundlehren 322, Springer (1999), Chapter I, Section 9; J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapter I, Section 7

import Mathlib
import Definitions.Def_RPLib_S4_KummerBridge

/-!
# S4-Kummer, part K4b: Kummer radicals inside unramified extensions have `N`-divisible valuations

* `ramificationIdx_eq_one`: every nonzero prime of `B_L` (`L ∈ unramSet A K`, `A` Dedekind with fraction field `K`, perfect
  residue fields at the maximal ideals) has ramification index `1` over `A` (trivial inertia, `Ideal.card_inertia_eq_ramificationIdxIn`).
* `dvd_log_valuation`: `M ≤ L` both in `unramSet`, `α ∈ L`, `α ^ N = a ∈ M`: `N ∣ log v(a)` at every prime `v` of
  `B_M` (tower `Ideal.ramificationIdx_tower` + `valuation_liesOver`).
* `dvd_log_valuation_of_mem_maxUnram`: the same for `α ∈ maxUnram A K`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain

namespace RamanujanPetersson
namespace Kummer

noncomputable section

variable {K : Type} [Field K] (A : Type) [CommRing A] [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]

theorem algebraMap_integralClosure_injective (L : IntermediateField K (AlgebraicClosure K)) :
    Function.Injective (algebraMap A (integralClosure A L)) := by
  intro a b h
  have hinj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  exact hinj (by simpa using congrArg Subtype.val h)

/-- Unramified finite Galois subextensions have ramification index `1` at every prime. -/
theorem ramificationIdx_eq_one {L : IntermediateField K (AlgebraicClosure K)} (hL : L ∈ unramSet A K)
    (hperf : ∀ (p : Ideal A) [p.IsMaximal], PerfectField p.ResidueField)
    (Q : Ideal (integralClosure A L)) [hQ : Q.IsPrime] (hQ0 : Q ≠ ⊥) : Q.ramificationIdx A = 1 := by
  obtain ⟨fL, gL, uL⟩ := hL
  have : IsFractionRing (integralClosure A L) L := integralClosure.isFractionRing_of_finite_extension (A := A) K L
  have : Module.Finite A (integralClosure A L) := IsIntegralClosure.finite A K L (integralClosure A L)
  have : IsGaloisGroup (L ≃ₐ[K] L) A (integralClosure A L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) A (integralClosure A L) K L
  have : Module.IsTorsionFree A (integralClosure A L) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (algebraMap_integralClosure_injective A L)
  have : IsDedekindDomain (integralClosure A L) := integralClosure.isDedekindDomain (A := A) (K := K) (L := L)
  have : Q.IsMaximal := hQ.isMaximal hQ0
  have : (Q.under A).IsMaximal := Ideal.IsMaximal.under A Q
  have : PerfectField (Q.under A).ResidueField := hperf (Q.under A)
  have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) (Q.under A) Q
  rw [uL Q hQ, Subgroup.card_bot, Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under A) Q (L ≃ₐ[K] L)] at h1
  exact h1.symm

/-- **Kummer radicals in unramified extensions have `N`-divisible valuations.** -/
theorem dvd_log_valuation {M L : IntermediateField K (AlgebraicClosure K)} (hML : M ≤ L) (hM : M ∈ unramSet A K)
    (hL : L ∈ unramSet A K) (hperf : ∀ (p : Ideal A) [p.IsMaximal], PerfectField p.ResidueField)
    {N : ℕ} {α : AlgebraicClosure K} (hαL : α ∈ L) {a : M} (hα : α ^ N = (a : AlgebraicClosure K))
    [IsDedekindDomain (integralClosure A M)] [IsFractionRing (integralClosure A M) M]
    (v : HeightOneSpectrum (integralClosure A M)) : (N : ℤ) ∣ WithZero.log (v.valuation M a) := by
  have := hM.1
  have := hL.1
  have := hL.2.1
  have : IsFractionRing (integralClosure A L) L := integralClosure.isFractionRing_of_finite_extension (A := A) K L
  have : IsDedekindDomain (integralClosure A L) := integralClosure.isDedekindDomain (A := A) (K := K) (L := L)
  letI : Algebra (integralClosure A M) (integralClosure A L) := (incl A K hML).toRingHom.toAlgebra
  letI : SMul (integralClosure A M) (integralClosure A L) := Algebra.toSMul
  letI : Algebra M L := (IntermediateField.inclusion hML).toRingHom.toAlgebra
  letI : Algebra (integralClosure A M) L :=
    ((algebraMap M L).comp (algebraMap (integralClosure A M) M)).toAlgebra
  have : @IsScalarTower (integralClosure A M) M L Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : @IsScalarTower (integralClosure A M) (integralClosure A L) L Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower A (integralClosure A M) (integralClosure A L) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext (Subtype.ext rfl))
  have : Module.IsTorsionFree (integralClosure A M) (integralClosure A L) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 fun x y h =>
      Subtype.ext (Subtype.ext (congrArg (fun z : integralClosure A L => ((z : L) : AlgebraicClosure K)) h))
  have : Algebra.IsIntegral (integralClosure A M) (integralClosure A L) :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral (R := A) x).tower_top⟩
  have : Module.Flat (integralClosure A M) (integralClosure A L) := inferInstance
  obtain ⟨w, rfl⟩ := PicDescent.exists_under_eq (A := integralClosure A M) (B := integralClosure A L) v
  have he : w.asIdeal.ramificationIdx (integralClosure A M) = 1 := by
    have h1 := ramificationIdx_eq_one A hL hperf w.asIdeal w.ne_bot
    rw [Ideal.ramificationIdx_tower (R := A) (w.under (integralClosure A M)).asIdeal w.asIdeal] at h1
    exact Nat.dvd_one.1 ⟨_, h1.symm.trans (mul_comm _ _)⟩
  have he' : (w.under (integralClosure A M)).asIdeal.ramificationIdx' w.asIdeal = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (w.under (integralClosure A M)).ne_bot]
    exact he
  have hval := HeightOneSpectrum.valuation_liesOver L (w.under (integralClosure A M)) w a
  rw [he', pow_one] at hval
  have hαa : algebraMap M L a = (⟨α, hαL⟩ : L) ^ N := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow]
    exact hα.symm
  rw [hval, hαa, map_pow, WithZero.log_pow]
  exact ⟨_, nsmul_eq_mul _ _⟩

/-- The same for a Kummer radical `α ∈ K_U`. -/
theorem dvd_log_valuation_of_mem_maxUnram {M : IntermediateField K (AlgebraicClosure K)} (hM : M ∈ unramSet A K)
    (hperf : ∀ (p : Ideal A) [p.IsMaximal], PerfectField p.ResidueField)
    {N : ℕ} {α : AlgebraicClosure K} (hαU : α ∈ maxUnram A K) {a : M} (hα : α ^ N = (a : AlgebraicClosure K))
    [IsDedekindDomain (integralClosure A M)] [IsFractionRing (integralClosure A M) M]
    (v : HeightOneSpectrum (integralClosure A M)) : (N : ℤ) ∣ WithZero.log (v.valuation M a) := by
  obtain ⟨L, hL, hle⟩ := exists_unramSet_of_finite A K {α} (by simpa using hαU)
  refine dvd_log_valuation A (le_sup_left : M ≤ M ⊔ L) hM (sup_mem_unramSet A K hM hL) hperf ?_ hα v
  exact (le_sup_right : L ≤ M ⊔ L) (hle (IntermediateField.subset_adjoin K _ (by simp)))

end

end Kummer
end RamanujanPetersson


