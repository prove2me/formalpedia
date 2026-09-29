-- Prove2me | solution 1 for Algebra.IsStandardSmoothOfRelativeDimension.isDiscreteValuationRing_localization_atPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/477cdcca-1a88-5599-9ed8-f8ccad926720

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_IsStandardSmoothOfRelativeDimension_isDiscreteValuationRing_localization_atPrime

universe u v

open IsLocalRing

attribute [local instance] Ideal.Quotient.field

namespace Algebra
p2m_export "Algebra" "commutes algebraMap mem_iInf FiniteType IsIntegral.of_finite Etale smul_def IsStandardSmoothOfRelativeDimension IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial FiniteType.isNoetherianRing mem_bot isUnramifiedAt_iff_map_eq"
namespace IsStandardSmoothOfRelativeDimension
p2m_export "Algebra.IsStandardSmoothOfRelativeDimension" "out exists_etale_mvPolynomial trans"
p2m_open "Algebra.IsStandardSmoothOfRelativeDimension Algebra"

theorem isDomain_of_maximalIdeal_eq_span {L : Type*} [CommRing L] [IsLocalRing L]
    [IsNoetherianRing L] {ϖ : L} (hreg : IsSMulRegular L ϖ)
    (hmax : maximalIdeal L = Ideal.span {ϖ}) : IsDomain L := by
  classical
  have hpow : ∀ n : ℕ, maximalIdeal L ^ n = Ideal.span {ϖ ^ n} := fun n => by
    rw [hmax, Ideal.span_singleton_pow]
  have key : ∀ x : L, x ≠ 0 → ∃ (n : ℕ) (w : L), IsUnit w ∧ x = w * ϖ ^ n := by
    intro x hx
    have hex : ∃ n : ℕ, x ∉ maximalIdeal L ^ n := by
      by_contra! h
      apply hx
      have hmem : x ∈ ⨅ n : ℕ, maximalIdeal L ^ n := Ideal.mem_iInf.mpr h
      rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal L).ne_top,
        Ideal.mem_bot] at hmem
    have hn0 : Nat.find hex ≠ 0 := by
      intro h0
      have := Nat.find_spec hex
      rw [h0, pow_zero, Ideal.one_eq_top] at this
      exact this trivial
    obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := Nat.exists_eq_succ_of_ne_zero hn0
    have hxj : x ∈ maximalIdeal L ^ j := by
      have := Nat.find_min hex (m := j) (by omega)
      exact not_not.mp this
    have hxj1 : x ∉ maximalIdeal L ^ (j + 1) := hj ▸ Nat.find_spec hex
    rw [hpow] at hxj hxj1
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.mp hxj
    refine ⟨j, w, ?_, rfl⟩
    by_contra hw
    apply hxj1
    have hw' : w ∈ maximalIdeal L := hw
    rw [hmax] at hw'
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hw'
    exact Ideal.mem_span_singleton'.mpr ⟨c, by ring⟩
  have : NoZeroDivisors L := ⟨fun {a b} hab => by
    by_contra h
    push_neg at h
    obtain ⟨n, w, hw, rfl⟩ := key a h.1
    obtain ⟨m, w', hw', rfl⟩ := key b h.2
    have hreg' : IsSMulRegular L (ϖ ^ (n + m)) := hreg.pow (n + m)
    have h0 : ϖ ^ (n + m) • (w * w') = ϖ ^ (n + m) • (0 : L) := by
      rw [smul_eq_mul, smul_zero, ← hab]; ring
    exact (hw.mul hw').ne_zero (hreg' h0)⟩
  exact NoZeroDivisors.to_isDomain L

theorem atom_main
    {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k A]
    (p : Ideal A) [p.IsMaximal] :
    ∃ _ : IsDomain (Localization.AtPrime p), IsDiscreteValuationRing (Localization.AtPrime p) := by
  classical

  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial 1 k A
  let P := MvPolynomial (Fin 1) k
  letI : Algebra P A := g.toRingHom.toAlgebra
  haveI : Algebra.Etale P A := hg
  haveI : IsScalarTower k P A := IsScalarTower.of_algebraMap_eq fun c => (g.commutes c).symm

  let e : P ≃ₐ[k] Polynomial k :=
    (MvPolynomial.renameEquiv k (Equiv.equivPUnit.{1, 1} (Fin 1))).trans
      (MvPolynomial.pUnitAlgEquiv.{u, 0} k)
  haveI : IsPrincipalIdealRing P := IsPrincipalIdealRing.of_surjective e.symm e.symm.surjective
  have hPnf : ¬ IsField P := fun h => Polynomial.not_isField (R := k) (e.symm.toMulEquiv.isField h)

  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing P A

  let q : Ideal P := p.under P
  haveI : Algebra.FiniteType k A :=
    (inferInstance : Algebra.FiniteType k P).trans (inferInstance : Algebra.FiniteType P A)
  haveI : Module.Finite k (A ⧸ p) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ p)
  haveI : Module.Finite k (P ⧸ q) :=
    FiniteDimensional.of_injective (IsScalarTower.toAlgHom k (P ⧸ q) (A ⧸ p)).toLinearMap
      (FaithfulSMul.algebraMap_injective (P ⧸ q) (A ⧸ p))
  haveI hqmax : q.IsMaximal := by
    refine Ideal.Quotient.maximal_of_isField _ ?_
    haveI : Algebra.IsIntegral k (P ⧸ q) := Algebra.IsIntegral.of_finite k _
    exact isField_of_isIntegral_of_isField' (R := k) (S := P ⧸ q) (Field.toIsField k)
  have hq0 : q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hqmax hPnf
  obtain ⟨π, hπ⟩ := (IsPrincipalIdealRing.principal q).principal
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact hq0 (by rw [hπ]; simp)

  set L := Localization.AtPrime p
  letI := Localization.AtPrime.algebraOfLiesOver q p
  have hmap : q.map (algebraMap P L) = maximalIdeal L :=
    ((Algebra.isUnramifiedAt_iff_map_eq (R := P) (p := q) (q := p)).mp inferInstance).2
  have hmaxL : maximalIdeal L = Ideal.span {algebraMap P L π} := by
    rw [← hmap, hπ]
    change Ideal.map (algebraMap P L) (Ideal.span {π}) = _
    rw [Ideal.map_span, Set.image_singleton]

  haveI : Module.Flat P L := Module.Flat.trans P A L
  have hreg : IsSMulRegular L (algebraMap P L π) := by
    have h : IsSMulRegular L π :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hπ0)
    intro a b hab
    apply h
    simpa [Algebra.smul_def] using hab
  have hne : maximalIdeal L ≠ ⊥ := by
    rw [hmaxL, Ne, Ideal.span_singleton_eq_bot]
    intro h0
    have : (algebraMap P L π) • (1 : L) = (algebraMap P L π) • (0 : L) := by simp [h0]
    exact one_ne_zero (hreg this)
  have hnf : ¬ IsField L := fun hF => hne ((IsLocalRing.isField_iff_maximalIdeal_eq).mp hF)

  haveI hdom : IsDomain L := isDomain_of_maximalIdeal_eq_span hreg hmaxL
  have hprinc : (maximalIdeal L).IsPrincipal := ⟨⟨algebraMap P L π, hmaxL⟩⟩
  exact ⟨hdom, ((IsDiscreteValuationRing.TFAE L hnf).out 4 0).mp hprinc⟩

end Algebra.IsStandardSmoothOfRelativeDimension

theorem solution
    {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k A]
    (p : Ideal A) [p.IsMaximal] :
    ∃ _ : IsDomain (Localization.AtPrime p), IsDiscreteValuationRing (Localization.AtPrime p) :=
  Algebra.IsStandardSmoothOfRelativeDimension.atom_main (k := k) p

end S_Algebra_IsStandardSmoothOfRelativeDimension_isDiscreteValuationRing_localization_atPrime
end P2MW
export P2MW.S_Algebra_IsStandardSmoothOfRelativeDimension_isDiscreteValuationRing_localization_atPrime (solution)
