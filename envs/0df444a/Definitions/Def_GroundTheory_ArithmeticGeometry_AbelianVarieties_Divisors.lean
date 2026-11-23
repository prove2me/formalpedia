-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Divisors
-- name    : GroundTheory_ArithmeticGeometry_AbelianVarieties_Divisors
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:29:23.974025+00:00
-- url     : https://prove2.me/theorems/9bae1fc7-39a5-4256-8589-f44c3d45aedb
-- title:
--   Divisors
-- statement:
--   Definitions and structural lemmas for Divisors, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Divisors.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some


set_option autoImplicit false
namespace GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain
open scoped nonZeroDivisors
universe u
variable {F : Type u} [Field F] (W : WeierstrassCurve F)
section Field
variable {W}
noncomputable def evalPoint {x y : F} (h : W.toAffine.Equation x y) :
    W.toAffine.CoordinateRing →+* F :=
  AdjoinRoot.lift (evalRingHom x) y (by rw [eval₂_evalRingHom]; exact h)
theorem evalPoint_mk {x y : F} (h : W.toAffine.Equation x y) (p : F[X][X]) :
    evalPoint h (AdjoinRoot.mk W.toAffine.polynomial p) = p.evalEval x y := by
  rw [evalPoint, AdjoinRoot.lift_mk, eval₂_evalRingHom]
theorem evalPoint_XClass {x y : F} (h : W.toAffine.Equation x y) (x' : F) :
    evalPoint h (XClass W.toAffine x') = x - x' := by
  rw [XClass, evalPoint_mk]
  simp [evalEval_C]
theorem evalPoint_YClass {x y : F} (h : W.toAffine.Equation x y) (y' : F) :
    evalPoint h (YClass W.toAffine (C y')) = y - y' := by
  rw [YClass, evalPoint_mk]
  simp [evalEval_sub, evalEval_X, evalEval_C]
theorem XYIdeal_le_ker {x y : F} (h : W.toAffine.Equation x y) :
    XYIdeal W.toAffine x (C y) ≤ RingHom.ker (evalPoint h) := by
  rw [XYIdeal, Ideal.span_le]
  rintro _ (rfl | rfl)
  · simp [evalPoint_XClass]
  · simp [evalPoint_YClass]
theorem isMaximal_XYIdeal {x y : F} (h : W.toAffine.Equation x y) :
    (XYIdeal W.toAffine x (C y)).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ <|
    MulEquiv.isField (Field.toIsField F)
      (quotientXYIdealEquiv (W' := W.toAffine) (x := x) (y := C y) h).toRingEquiv.toMulEquiv
theorem XYIdeal_ne_bot (x : F) (y : F[X]) : XYIdeal W.toAffine x y ≠ ⊥ := by
  intro h0
  have hx : XClass W.toAffine x ∈ XYIdeal W.toAffine x y :=
    Ideal.subset_span (Set.mem_insert _ _)
  rw [h0, Ideal.mem_bot] at hx
  exact XClass_ne_zero x hx
theorem XYIdeal_inj {x y x' y' : F} (h' : W.toAffine.Equation x' y')
    (he : XYIdeal W.toAffine x (C y) = XYIdeal W.toAffine x' (C y')) : x = x' ∧ y = y' := by
  have h1 : XClass W.toAffine x ∈ XYIdeal W.toAffine x' (C y') :=
    he ▸ Ideal.subset_span (Set.mem_insert _ _)
  have h2 : YClass W.toAffine (C y) ∈ XYIdeal W.toAffine x' (C y') :=
    he ▸ Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have e1 := XYIdeal_le_ker h' h1
  have e2 := XYIdeal_le_ker h' h2
  rw [RingHom.mem_ker, evalPoint_XClass] at e1
  rw [RingHom.mem_ker, evalPoint_YClass] at e2
  exact ⟨(sub_eq_zero.mp e1).symm, (sub_eq_zero.mp e2).symm⟩
noncomputable def heightOneOfNonsingular {x y : F} (h : W.toAffine.Nonsingular x y) :
    HeightOneSpectrum W.toAffine.CoordinateRing where
  asIdeal := XYIdeal W.toAffine x (C y)
  isPrime := (isMaximal_XYIdeal h.1).isPrime
  ne_bot := XYIdeal_ne_bot x (C y)
theorem heightOneOfNonsingular_inj {x y x' y' : F} (h : W.toAffine.Nonsingular x y)
    (h' : W.toAffine.Nonsingular x' y')
    (he : heightOneOfNonsingular h = heightOneOfNonsingular h') : x = x' ∧ y = y' :=
  XYIdeal_inj h'.1 (congrArg HeightOneSpectrum.asIdeal he)
instance : IsNoetherianRing W.toAffine.CoordinateRing :=
  inferInstanceAs (IsNoetherianRing (F[X][X] ⧸ Ideal.span {W.toAffine.polynomial}))
end Field
theorem isDiscreteValuationRing_of_maximalIdeal_mul_eq {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsLocalRing R] (hnf : ¬ IsField R) (J : Ideal R) {t : R} (ht : t ≠ 0)
    (h : IsLocalRing.maximalIdeal R * J = Ideal.span {t}) : IsDiscreteValuationRing R := by
  have hunit : IsUnit ((IsLocalRing.maximalIdeal R : Ideal R) : FractionalIdeal R⁰ (FractionRing R)) := by
    refine isUnit_iff_exists_inv.mpr ⟨(J : FractionalIdeal R⁰ (FractionRing R)) *
        ((Ideal.span {t} : Ideal R) : FractionalIdeal R⁰ (FractionRing R))⁻¹, ?_⟩
    rw [← mul_assoc, ← FractionalIdeal.coeIdeal_mul, h,
      FractionalIdeal.coe_ideal_span_singleton_mul_inv (FractionRing R) ht]
  have hprinc := Ideal.IsPrincipal.of_finite_maximals_of_isUnit
    ((Set.finite_singleton (IsLocalRing.maximalIdeal R)).subset
      fun I hI => IsLocalRing.eq_maximalIdeal hI) hunit
  exact ((IsDiscreteValuationRing.TFAE R hnf).out 0 4).mpr hprinc
section AlgClosed
variable [IsAlgClosed F]
theorem exists_equation (x : F) : ∃ y, W.toAffine.Equation x y := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root
    (C (1 : F) * X ^ 2 + C (W.a₁ * x + W.a₃) * X + C (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)))
    (by rw [degree_quadratic one_ne_zero]; norm_num)
  refine ⟨y, (W.toAffine.equation_iff x y).mpr ?_⟩
  simp only [IsRoot, eval_add, eval_mul, eval_C, eval_pow, eval_X] at hy
  linear_combination hy
variable [W.IsElliptic]
theorem exists_eq_XYIdeal {P : Ideal W.toAffine.CoordinateRing} [hP : P.IsPrime] (hP0 : P ≠ ⊥) :
    ∃ x y, W.toAffine.Nonsingular x y ∧ P = XYIdeal W.toAffine x (C y) := by
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = P.comap (algebraMap F[X] W.toAffine.CoordinateRing) := ⟨_, rfl⟩
  have hQ0 : Q ≠ ⊥ := fun h => hP0 (Ideal.eq_bot_of_comap_eq_bot (hQdef ▸ h))
  have hQ : Q.IsPrime := hQdef ▸ Ideal.IsPrime.comap _
  have hg := Submodule.IsPrincipal.prime_generator_of_isPrime Q hQ0
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ (degree_pos_of_irreducible hg.irreducible).ne'
  have hdvd : Submodule.IsPrincipal.generator Q ∣ X - C x :=
    (irreducible_X_sub_C x).dvd_symm hg.irreducible (dvd_iff_isRoot.mpr hx)
  have hxQ : X - C x ∈ Q := by
    rw [← Submodule.IsPrincipal.span_singleton_generator Q]
    exact Ideal.mem_span_singleton.mpr hdvd
  have hXP : XClass W.toAffine x ∈ P := by
    have : algebraMap F[X] W.toAffine.CoordinateRing (X - C x) = XClass W.toAffine x := by
      simp only [XClass, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]
    rw [← this]
    exact Ideal.mem_comap.mp (hQdef ▸ hxQ)
  obtain ⟨y, hy⟩ := exists_equation W x
  have hns : W.toAffine.Nonsingular x y := equation_iff_nonsingular.mp hy
  have hle : XYIdeal W.toAffine x (C (W.toAffine.negY x y)) * XYIdeal W.toAffine x (C y) ≤ P := by
    rw [XYIdeal_neg_mul hns, XIdeal, Ideal.span_le, Set.singleton_subset_iff]
    exact hXP
  rcases hP.mul_le.mp hle with h1 | h1
  · exact ⟨x, _, (nonsingular_neg ..).mpr hns,
      ((isMaximal_XYIdeal ((equation_neg ..).mpr hy)).eq_of_le hP.ne_top h1).symm⟩
  · exact ⟨x, y, hns, ((isMaximal_XYIdeal hy).eq_of_le hP.ne_top h1).symm⟩
omit [IsAlgClosed F] [W.IsElliptic] in

theorem isDiscreteValuationRing_localization_XYIdeal {x y : F} (h : W.toAffine.Nonsingular x y)
    [(XYIdeal W.toAffine x (C y)).IsPrime] :
    IsDiscreteValuationRing (Localization.AtPrime (XYIdeal W.toAffine x (C y))) := by
  have hnf : ¬ IsField (Localization.AtPrime (XYIdeal W.toAffine x (C y))) :=
    IsLocalization.AtPrime.not_isField W.toAffine.CoordinateRing (P := XYIdeal W.toAffine x (C y))
      (XYIdeal_ne_bot x (C y)) _
  have hinj : Function.Injective (algebraMap W.toAffine.CoordinateRing
      (Localization.AtPrime (XYIdeal W.toAffine x (C y)))) :=
    IsLocalization.injective _ (XYIdeal W.toAffine x (C y)).primeCompl_le_nonZeroDivisors
  have : IsNoetherianRing (Localization.AtPrime (XYIdeal W.toAffine x (C y))) :=
    IsLocalization.isNoetherianRing (XYIdeal W.toAffine x (C y)).primeCompl _ inferInstance
  refine isDiscreteValuationRing_of_maximalIdeal_mul_eq hnf
    ((XYIdeal W.toAffine x (C (W.toAffine.negY x y))).map (algebraMap _ _))
    ((map_ne_zero_iff _ hinj).mpr (XClass_ne_zero (W' := W.toAffine) x)) ?_
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (XYIdeal W.toAffine x (C y)), ← Ideal.map_mul, mul_comm,
    XYIdeal_neg_mul h, XIdeal, Ideal.map_span, Set.image_singleton]
instance isDedekindDomainDvr_coordinateRing : IsDedekindDomainDvr W.toAffine.CoordinateRing where
  is_dvr_at_nonzero_prime P hP0 hP := by
    obtain ⟨x, y, h, rfl⟩ := exists_eq_XYIdeal W hP0
    exact isDiscreteValuationRing_localization_XYIdeal W h
instance isDedekindDomain_coordinateRing : IsDedekindDomain W.toAffine.CoordinateRing :=
  inferInstance
noncomputable def affinePointEquiv :
    {xy : F × F // W.toAffine.Nonsingular xy.1 xy.2} ≃
      HeightOneSpectrum W.toAffine.CoordinateRing :=
  Equiv.ofBijective (fun p => heightOneOfNonsingular p.2)
    ⟨fun p q he => by
      obtain ⟨h1, h2⟩ := heightOneOfNonsingular_inj p.2 q.2 he
      exact Subtype.ext (Prod.ext h1 h2),
    fun v => by
      have := v.isPrime
      obtain ⟨x, y, h, hv⟩ := exists_eq_XYIdeal W v.ne_bot
      exact ⟨⟨(x, y), h⟩, HeightOneSpectrum.ext hv.symm⟩⟩
end AlgClosed
end GroundTheory.Arith.Abelian


