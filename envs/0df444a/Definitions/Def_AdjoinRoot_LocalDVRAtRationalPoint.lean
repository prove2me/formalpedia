-- Prove2me | Definitions.Def_AdjoinRoot_LocalDVRAtRationalPoint
-- name    : AdjoinRoot_LocalDVRAtRationalPoint
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:10:18.625416+00:00
-- url     : https://prove2.me/theorems/f84f717b-ef67-4dc4-aeb7-41f949026f0d
-- title:
--   DVR local rings at smooth rational points of monic plane curves
-- statement:
--   Packages the local-algebra framework in which a one-variable polynomial algebra is standard smooth of relative dimension one, a monic plane algebra becomes standard smooth after inverting its vertical derivative, and localization at a rational point with nonzero derivative is a discrete valuation ring. These statements provide the local rings needed to turn smooth rational points into places of function fields.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans
/-! Local rings of a monic plane equation at rational points with nonvanishing derivative.

A polynomial algebra is standard smooth of relative dimension one, a monic quotient `R[X][Y]/(f)` is standard smooth away
from the vertical derivative, and the localization of such a curve at a rational point where the derivative does not
vanish is a discrete valuation ring. These facts are proved here because definitions of places use them. -/

/-! ### Standard smooth local rings of relative dimension one are discrete valuation rings -/
noncomputable section

universe u v

open IsLocalRing

attribute [local instance] Ideal.Quotient.field

namespace Algebra
namespace IsStandardSmoothOfRelativeDimension

private theorem isDomain_of_maximalIdeal_eq_span {L : Type*} [CommRing L] [IsLocalRing L]
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

/-- A maximal localization of a standard smooth curve algebra over a field is a DVR. -/
private theorem isDiscreteValuationRing_localization_atPrime
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

end

/-! ### Polynomial algebras are standard smooth -/
noncomputable section

namespace Algebra.IsStandardSmoothOfRelativeDimension

/-- A polynomial algebra in one variable is standard smooth of relative dimension one. -/
theorem polynomial (R : Type*) [CommRing R] :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R (Polynomial R) := by
  let e := MvPolynomial.uniqueAlgEquiv R Unit
  let f : MvPolynomial Unit R →ₐ[R] Polynomial R := e.toAlgHom
  have hf : Function.Surjective f := e.surjective
  let P : Algebra.PreSubmersivePresentation R (Polynomial R) Unit Empty :=
    { toPresentation :=
        { toGenerators := Algebra.Generators.ofAlgHom f hf
          relation := Empty.elim
          span_range_relation_eq_ker := by
            rw [Algebra.Generators.ker_ofAlgHom f hf]
            simp only [Set.range_eq_empty, Ideal.span_empty]
            symm
            rw [← RingHom.injective_iff_ker_eq_bot]
            exact e.injective }
      map := Empty.elim
      map_inj := fun a => Empty.elim a }
  let SP : Algebra.SubmersivePresentation R (Polynomial R) Unit Empty :=
    { __ := P
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
        simp }
  apply SP.isStandardSmoothOfRelativeDimension
  simp [Algebra.Presentation.dimension]

end Algebra.IsStandardSmoothOfRelativeDimension

end

/-! ### Standard smoothness away from the derivative -/
noncomputable section

namespace AdjoinRoot

/-- Inverting the derivative of a monic plane equation gives a standard smooth
curve algebra over the coefficient field. -/
theorem standardSmooth_away_derivative {k : Type*} [CommRing k]
    (f : Polynomial (Polynomial k)) (hf : f.Monic) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 k
      (Localization.Away (AdjoinRoot.mk f f.derivative)) := by
  let P : StandardEtalePair (Polynomial k) :=
    { f := f
      monic_f := hf
      g := f.derivative
      cond := ⟨1, 0, 1, by simp⟩ }
  let T := Localization.Away (AdjoinRoot.mk f f.derivative)
  haveI : Algebra.IsStandardEtale (Polynomial k) T :=
    Algebra.IsStandardEtale.of_equiv P.equivAwayAdjoinRoot
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 (Polynomial k) T := by
    rw [← Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero]
    infer_instance
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 k (Polynomial k) :=
    Algebra.IsStandardSmoothOfRelativeDimension.polynomial k
  exact Algebra.IsStandardSmoothOfRelativeDimension.trans 1 0 k (Polynomial k) T

end AdjoinRoot

end

/-! ### Discrete valuation rings at rational points -/
noncomputable section

universe u

namespace AdjoinRoot

private theorem localDVR_of_standardSmoothAway
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    (a : A) [Algebra.IsStandardSmoothOfRelativeDimension 1 k (Localization.Away a)]
    (e : A →ₐ[k] k) (p : Ideal A) [p.IsMaximal]
    (hp : RingHom.ker e.toRingHom = p) (hJac : e a ≠ 0) :
    ∃ _ : IsDomain (Localization.AtPrime p),
      IsDiscreteValuationRing (Localization.AtPrime p) := by
  let T := Localization.Away a
  let eT : T →ₐ[k] k := IsLocalization.Away.liftAlgHom a
    (f := e) (isUnit_iff_ne_zero.mpr hJac)
  let q : Ideal T := RingHom.ker eT.toRingHom
  have heT : Function.Surjective eT := fun a =>
    ⟨algebraMap k T a, eT.commutes a⟩
  haveI : q.IsMaximal := RingHom.ker_isMaximal_of_surjective _ heT
  have hq : q.comap (algebraMap A T) = p := by
    rw [← hp]
    ext a
    change eT (algebraMap A T a) = 0 ↔ e a = 0
    simp [eT, IsLocalization.Away.liftAlgHom]
  clear hp
  subst p
  obtain ⟨hdom, hdvr⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.isDiscreteValuationRing_localization_atPrime
      (k := k) q
  letI := hdom
  letI := hdvr
  let L := Localization.AtPrime (q.comap (algebraMap A T))
  let E : L ≃ₐ[A] Localization.AtPrime q :=
    IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      (Submonoid.powers a) q
  letI : IsDomain L :=
    MulEquiv.isDomain (Localization.AtPrime q) E.toMulEquiv
  exact ⟨inferInstance, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing E.symm⟩

/-- At a rational point of a monic plane equation where the derivative in the
second variable is nonzero, the original point local ring is a DVR. -/
theorem localDVR_at_rationalPoint {k : Type u} [Field k]
    (f : Polynomial (Polynomial k)) (hf : f.Monic)
    (e : AdjoinRoot f →ₐ[k] k) (p : Ideal (AdjoinRoot f)) [p.IsMaximal]
    (hp : RingHom.ker e.toRingHom = p)
    (hderiv : e (AdjoinRoot.mk f f.derivative) ≠ 0) :
    ∃ _ : IsDomain (Localization.AtPrime p),
      IsDiscreteValuationRing (Localization.AtPrime p) := by
  letI := standardSmooth_away_derivative f hf
  exact localDVR_of_standardSmoothAway (AdjoinRoot.mk f f.derivative) e p hp hderiv

end AdjoinRoot

end


