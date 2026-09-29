-- Prove2me | solution 1 for AdjoinRoot.isDomain_and_isIntegrallyClosed_of_isUnit_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/bf582ff5-7bdf-5cd2-960b-9186f07b80cb

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AdjoinRoot_isDomain_and_isIntegrallyClosed_of_isUnit_derivative

set_option autoImplicit false

universe u

open Polynomial

namespace NormalAdjoinRoot

variable {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]

theorem irreducible_map (f : R[X]) (hfm : f.Monic) (hfi : Irreducible f) :
    Irreducible (f.map (algebraMap R (FractionRing R))) :=
  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map hfm).mp hfi

theorem dvd_of_map_dvd (f : R[X]) (hfm : f.Monic) (p : R[X])
    (h : f.map (algebraMap R (FractionRing R)) ∣ p.map (algebraMap R (FractionRing R))) :
    f ∣ p := by
  have hfKm : (f.map (algebraMap R (FractionRing R))).Monic := hfm.map _
  rw [← modByMonic_eq_zero_iff_dvd hfm]
  have h1 : (p %ₘ f).map (algebraMap R (FractionRing R)) = 0 := by
    rw [Polynomial.map_modByMonic _ hfm, (modByMonic_eq_zero_iff_dvd hfKm).mpr h]
  exact (Polynomial.map_injective _ (IsFractionRing.injective R (FractionRing R))) (by rw [h1, Polynomial.map_zero])

end NormalAdjoinRoot

open NormalAdjoinRoot in
theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (f : R[X]) (hfm : f.Monic) (hfi : Irreducible f)
    (hu : IsUnit (AdjoinRoot.mk f (derivative f))) :
    IsDomain (AdjoinRoot f) ∧ IsIntegrallyClosed (AdjoinRoot f) := by
  classical

  haveI hfact : Fact (Irreducible (f.map (algebraMap R (FractionRing R)))) := ⟨irreducible_map f hfm hfi⟩
  have hfK0 : f.map (algebraMap R (FractionRing R)) ≠ 0 := hfact.out.ne_zero

  have hev : Polynomial.eval₂ ((AdjoinRoot.of (f.map (algebraMap R (FractionRing R)))).comp (algebraMap R (FractionRing R)))
      (AdjoinRoot.root (f.map (algebraMap R (FractionRing R)))) f = 0 := by
    rw [← Polynomial.eval₂_map, AdjoinRoot.eval₂_root]
  let j : AdjoinRoot f →+* AdjoinRoot (f.map (algebraMap R (FractionRing R))) := AdjoinRoot.lift _ _ hev
  have hj_mk : ∀ p : R[X], j (AdjoinRoot.mk f p) =
      AdjoinRoot.mk (f.map (algebraMap R (FractionRing R))) (p.map (algebraMap R (FractionRing R))) := fun p => by
    show AdjoinRoot.lift _ _ hev (AdjoinRoot.mk f p) = _
    rw [AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.aeval_eq, ← AdjoinRoot.algebraMap_eq,
      Polynomial.aeval_def]
  have hj_inj : Function.Injective j := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective w
    rw [hj_mk, AdjoinRoot.mk_eq_zero] at hw
    exact AdjoinRoot.mk_eq_zero.mpr (dvd_of_map_dvd f hfm p hw)
  haveI hdom : IsDomain (AdjoinRoot f) := Function.Injective.isDomain j hj_inj
  refine ⟨hdom, ?_⟩

  have hj_of : ∀ r : R, j (algebraMap R (AdjoinRoot f) r) = algebraMap R (AdjoinRoot (f.map (algebraMap R (FractionRing R)))) r :=
    fun r => by
      show AdjoinRoot.lift _ _ hev (algebraMap R (AdjoinRoot f) r) = _
      rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]
      rfl
  let jA : AdjoinRoot f →ₐ[R] AdjoinRoot (f.map (algebraMap R (FractionRing R))) := { j with commutes' := hj_of }
  have hjA : ∀ w, jA w = j w := fun _ => rfl
  have hj_root : j (AdjoinRoot.root f) = AdjoinRoot.root (f.map (algebraMap R (FractionRing R))) := by
    show AdjoinRoot.lift _ _ hev (AdjoinRoot.root f) = _
    rw [AdjoinRoot.lift_root]

  letI algWL : Algebra (AdjoinRoot f) (AdjoinRoot (f.map (algebraMap R (FractionRing R)))) := j.toAlgebra
  haveI : IsScalarTower R (AdjoinRoot f) (AdjoinRoot (f.map (algebraMap R (FractionRing R)))) :=
    IsScalarTower.of_algebraMap_eq fun r => (hj_of r).symm
  haveI : Module.Finite R (AdjoinRoot f) := (AdjoinRoot.powerBasis' hfm).finite

  have hR0 : ∀ b : R, b ∈ nonZeroDivisors R → algebraMap R (AdjoinRoot f) b ∈ nonZeroDivisors (AdjoinRoot f) := by
    intro b hb
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => nonZeroDivisors.ne_zero hb ?_
    have : j (algebraMap R (AdjoinRoot f) b) = 0 := by rw [h0, map_zero]
    rw [hj_of, IsScalarTower.algebraMap_apply R (FractionRing R) (AdjoinRoot (f.map (algebraMap R (FractionRing R)))),
      AdjoinRoot.algebraMap_eq] at this
    have h1 : algebraMap R (FractionRing R) b = 0 :=
      (AdjoinRoot.of (f.map (algebraMap R (FractionRing R)))).injective (by rw [this, map_zero])
    exact (IsFractionRing.injective R (FractionRing R)) (by rw [h1, map_zero])
  haveI hfrac : IsFractionRing (AdjoinRoot f) (AdjoinRoot (f.map (algebraMap R (FractionRing R)))) := by
    refine ⟨fun s => ?_, fun z => ?_, fun {a b} h => ⟨1, by rw [hj_inj h]⟩⟩
    · exact isUnit_iff_ne_zero.mpr fun h0 => nonZeroDivisors.ne_zero s.2 (hj_inj ((h0.trans (map_zero j).symm : j s.1 = j 0)))
    · obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective z
      obtain ⟨b, hb, hbq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) q
      refine ⟨(AdjoinRoot.mk f (IsLocalization.integerNormalization (nonZeroDivisors R) q),
        ⟨algebraMap R (AdjoinRoot f) b, hR0 b hb⟩), ?_⟩
      show AdjoinRoot.mk _ q * j (algebraMap R (AdjoinRoot f) b) = j (AdjoinRoot.mk f _)
      rw [hj_mk, hbq, hj_of, Algebra.smul_def, map_mul, Polynomial.algebraMap_apply, AdjoinRoot.mk_C,
        IsScalarTower.algebraMap_apply R (FractionRing R) (AdjoinRoot (f.map (algebraMap R (FractionRing R)))),
        AdjoinRoot.algebraMap_eq, mul_comm]

  let pb : PowerBasis (FractionRing R) (AdjoinRoot (f.map (algebraMap R (FractionRing R)))) := AdjoinRoot.powerBasis hfK0
  haveI : FiniteDimensional (FractionRing R) (AdjoinRoot (f.map (algebraMap R (FractionRing R)))) := pb.finite
  have hy : IsIntegral R (AdjoinRoot.root (f.map (algebraMap R (FractionRing R)))) := by
    refine ⟨f, hfm, ?_⟩
    have := hev
    rwa [show ((AdjoinRoot.of (f.map (algebraMap R (FractionRing R)))).comp (algebraMap R (FractionRing R))) =
      algebraMap R (AdjoinRoot (f.map (algebraMap R (FractionRing R)))) from RingHom.ext fun _ => rfl] at this

  have hfKm : (f.map (algebraMap R (FractionRing R))).Monic := hfm.map _
  have hminK : minpoly (FractionRing R) pb.gen = f.map (algebraMap R (FractionRing R)) :=
    AdjoinRoot.minpoly_powerBasis_gen_of_monic hfKm
  have hgen : pb.gen = AdjoinRoot.root (f.map (algebraMap R (FractionRing R))) := AdjoinRoot.powerBasis_gen hfK0
  have hd0 : derivative (f.map (algebraMap R (FractionRing R))) ≠ 0 := by
    intro h0
    apply hu.ne_zero
    apply hj_inj
    rw [hj_mk, ← Polynomial.derivative_map, h0, map_zero, map_zero]
  have hsepK : (f.map (algebraMap R (FractionRing R))).Separable :=
    (Polynomial.separable_iff_derivative_ne_zero hfact.out).mpr hd0
  have hysep : IsSeparable (FractionRing R) pb.gen := by
    rw [IsSeparable, hminK]; exact hsepK
  haveI : Algebra.IsSeparable (FractionRing R) (AdjoinRoot (f.map (algebraMap R (FractionRing R)))) := by
    have htop : IntermediateField.adjoin (FractionRing R) {pb.gen} = ⊤ := by
      rw [hgen]; exact IntermediateField.adjoin_root_eq_top _
    haveI := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable (FractionRing R) _).mpr hysep
    exact AlgEquiv.Algebra.isSeparable ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv)

  refine (isIntegrallyClosed_iff (AdjoinRoot (f.map (algebraMap R (FractionRing R))))).mpr fun {z} hz => ?_
  have hzR : IsIntegral R z := isIntegral_trans z hz
  have hy' : IsIntegral R pb.gen := by rw [hgen]; exact hy
  have hb : ∀ i, IsIntegral R (pb.basis i) := fun i => by rw [pb.coe_basis]; exact hy'.pow _
  have hspan := integralClosure_le_span_dualBasis (A := R) (K := FractionRing R) pb.basis hb
    (show z ∈ Subalgebra.toSubmodule (integralClosure R (AdjoinRoot (f.map (algebraMap R (FractionRing R))))) from hzR)
  rw [← Module.Basis.traceDual_def] at hspan
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hspan
  set d := aeval pb.gen (derivative (minpoly (FractionRing R) pb.gen)) with hd
  have hdj : d = j (AdjoinRoot.mk f (derivative f)) := by
    rw [hd, hminK, Polynomial.derivative_map, hj_mk, hgen, AdjoinRoot.aeval_eq]
  have hd0' : d ≠ 0 := by
    rw [hdj]; exact fun h => hu.ne_zero (hj_inj (h.trans (map_zero j).symm))
  have hdz : d * z ∈ Algebra.adjoin R {pb.gen} := by
    rw [← hc, Finset.mul_sum]
    refine Subalgebra.sum_mem _ fun i _ => ?_
    rw [mul_smul_comm, Module.Basis.traceDual_powerBasis_eq pb i, mul_div_cancel₀ _ hd0',
      ← minpolyDiv_eq_of_isIntegrallyClosed (FractionRing R) hy']
    exact Subalgebra.smul_mem _ (coeff_minpolyDiv_mem_adjoin pb.gen i) _

  have hrange : Algebra.adjoin R {pb.gen} = jA.range := by
    rw [hgen, ← hj_root, ← hjA, ← AlgHom.map_adjoin_singleton, AdjoinRoot.adjoinRoot_eq_top, Algebra.map_top]
  rw [hrange] at hdz
  obtain ⟨w, hw⟩ := hdz
  have hw' : j w = d * z := hw
  refine ⟨↑hu.unit⁻¹ * w, ?_⟩
  show j (↑hu.unit⁻¹ * w) = z
  apply mul_left_cancel₀ hd0'
  calc d * j (↑hu.unit⁻¹ * w) = j (AdjoinRoot.mk f (derivative f) * (↑hu.unit⁻¹ * w)) := by rw [hdj, ← map_mul]
    _ = j w := by rw [← mul_assoc, IsUnit.mul_val_inv, one_mul]
    _ = d * z := hw'

end S_AdjoinRoot_isDomain_and_isIntegrallyClosed_of_isUnit_derivative
end P2MW
export P2MW.S_AdjoinRoot_isDomain_and_isIntegrallyClosed_of_isUnit_derivative (solution)
