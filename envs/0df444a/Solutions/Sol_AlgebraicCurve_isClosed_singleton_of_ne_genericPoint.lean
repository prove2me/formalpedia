-- Prove2me | solution 1 for AlgebraicCurve.isClosed_singleton_of_ne_genericPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/18f5db87-04db-5742-a037-3f9601af61e8

import Mathlib
import Theorems.Thm_Algebra_IsStandardSmoothOfRelativeDimension_isDiscreteValuationRing_localization_atPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint

universe u v

open CategoryTheory AlgebraicGeometry IsLocalRing Topology

namespace Algebra p2m_export "Algebra" "algebraMap IsStandardSmoothOfRelativeDimension mem_bot IsStandardSmoothOfRelativeDimension.isDiscreteValuationRing_localization_atPrime" namespace IsStandardSmoothOfRelativeDimension p2m_export "Algebra.IsStandardSmoothOfRelativeDimension" "isDiscreteValuationRing_localization_atPrime" end Algebra.IsStandardSmoothOfRelativeDimension
p2m_open_scoped "Algebra Algebra.IsStandardSmoothOfRelativeDimension" in

theorem Algebra.IsStandardSmoothOfRelativeDimension.isMaximal_of_isPrime_of_ne_bot
    {k : Type u} [Field k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k A]
    (q : Ideal A) [hq : q.IsPrime] (hq0 : q ≠ ⊥) : q.IsMaximal := by
  obtain ⟨m, hm, hqm⟩ := Ideal.exists_le_maximal q hq.ne_top
  obtain ⟨_, hdvr⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.isDiscreteValuationRing_localization_atPrime
      (k := k) m

  have hdisj : Disjoint (m.primeCompl : Set A) q := by
    rw [Set.disjoint_left]; intro a ha haq; exact ha (hqm haq)
  haveI hq' : (q.map (algebraMap A (Localization.AtPrime m))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl _ q hq hdisj
  have hinj := IsLocalization.injective (Localization.AtPrime m) m.primeCompl_le_nonZeroDivisors
  have hq'0 : q.map (algebraMap A (Localization.AtPrime m)) ≠ ⊥ := by
    intro h
    apply hq0
    refine (Submodule.eq_bot_iff _).mpr fun a ha => ?_
    have hmem : algebraMap A (Localization.AtPrime m) a ∈ q.map (algebraMap A _) :=
      Ideal.mem_map_of_mem _ ha
    rw [h, Ideal.mem_bot] at hmem
    exact (injective_iff_map_eq_zero _).mp hinj a hmem
  have hmax' : (q.map (algebraMap A (Localization.AtPrime m))).IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime hq'0 hq'
  have heq : q.map (algebraMap A (Localization.AtPrime m)) = maximalIdeal _ :=
    IsLocalRing.eq_maximalIdeal hmax'

  have : q = m := by
    refine le_antisymm hqm fun a ha => ?_
    have h1 := IsLocalization.comap_map_of_isPrime_disjoint m.primeCompl (Localization.AtPrime m)
      hq hdisj
    have hmem : a ∈ Ideal.comap (algebraMap A (Localization.AtPrime m))
        (q.map (algebraMap A (Localization.AtPrime m))) := by
      rw [Ideal.mem_comap, heq]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m a).mpr ha
    exact h1.le hmem
  exact this ▸ hm

theorem solution
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c]
    (x : C) (hx : x ≠ genericPoint C) : IsClosed ({x} : Set C) := by
  classical
  rw [← closure_subset_iff_isClosed]
  intro y hy

  obtain ⟨U, hU, V, hV, hyV, hle, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := c) y
  have hxV : x ∈ V := by
    obtain ⟨w, hwV, hwx⟩ := mem_closure_iff.mp hy V V.isOpen hyV
    rw [Set.mem_singleton_iff] at hwx
    exact hwx ▸ hwV

  have hcyU : c.base y ∈ U := hle hyV
  obtain rfl : U = ⊤ := top_le_iff.mp fun w _ => by
    rw [Subsingleton.elim w (c.base y)]; exact hcyU
  let e : K ≃+* Γ(Spec (CommRingCat.of K), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  let ψ : K →+* Γ(C, V) := (c.appLE ⊤ V hle).hom.comp e.toRingHom
  have hψ : ψ.IsStandardSmoothOfRelativeDimension 1 :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _ e hstd
  letI : Algebra K Γ(C, V) := ψ.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 K Γ(C, V) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mp hψ
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩

  set qx := hV.primeIdealOf ⟨x, hxV⟩ with hqx
  set qy := hV.primeIdealOf ⟨y, hyV⟩ with hqy

  have hspec : (⟨x, hxV⟩ : V) ⤳ ⟨y, hyV⟩ :=
    Topology.IsInducing.subtypeVal.specializes_iff.mp (specializes_iff_mem_closure.mpr hy)
  have hle' : qx.asIdeal ≤ qy.asIdeal :=
    (PrimeSpectrum.le_iff_specializes qx qy).mpr (hspec.map hV.isoSpec.hom.base.hom.continuous)

  have hinj : Function.Injective (hV.isoSpec.hom.base) := (Scheme.homeoOfIso hV.isoSpec).injective
  have hqx0 : qx.asIdeal ≠ ⊥ := by
    intro h0
    apply hx
    have h1 : qx = genericPoint (Spec Γ(C, V)) := by
      rw [genericPoint_eq_bot_of_affine]; exact PrimeSpectrum.ext h0
    rw [← hV.primeIdealOf_genericPoint] at h1
    exact congrArg Subtype.val (hinj h1)

  have hqxmax : qx.asIdeal.IsMaximal :=
    Algebra.IsStandardSmoothOfRelativeDimension.isMaximal_of_isPrime_of_ne_bot (k := K) _ hqx0
  have hqq : qx = qy := PrimeSpectrum.ext (hqxmax.eq_of_le qy.isPrime.ne_top hle')
  have hxy : (⟨x, hxV⟩ : V) = ⟨y, hyV⟩ := hinj hqq
  rw [Set.mem_singleton_iff]
  exact (congrArg Subtype.val hxy).symm

end S_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
end P2MW
export P2MW.S_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint (solution)
