-- Prove2me | solution 1 for AlgebraicCurve.infinite_setOf_isClosed_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/da8cd636-0168-5982-97e6-079659f694ce

import Mathlib
import Theorems.Thm_Algebra_IsStandardSmoothOfRelativeDimension_isDiscreteValuationRing_localization_atPrime
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_infinite_setOf_isClosed_singleton

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "isClosed_singleton_of_ne_genericPoint"
namespace LInf
p2m_open "AlgebraicCurve"

theorem isField_of_isMaximal_bot (A : Type*) [CommRing A] [Nontrivial A]
    (h : (⊥ : Ideal A).IsMaximal) : IsField A := by
  exact Ring.isField_iff_maximal_bot.mpr h

theorem isField_of_finite_maximalSpectrum (A : Type*) [CommRing A] [IsDomain A] [IsJacobsonRing A]
    [Finite (MaximalSpectrum A)] : IsField A := by
  classical
  haveI := Fintype.ofFinite (MaximalSpectrum A)
  have hjac : (⊥ : Ideal A).jacobson = ⊥ := IsJacobsonRing.out ‹_› Ideal.isRadical_bot
  have hprod : (Finset.univ : Finset (MaximalSpectrum A)).prod (fun m => m.asIdeal) ≤ ⊥ := by
    rw [← hjac]
    refine le_trans Ideal.prod_le_inf ?_
    refine le_sInf fun J hJ => ?_
    exact Finset.inf_le (Finset.mem_univ (⟨J, hJ.2⟩ : MaximalSpectrum A))
  obtain ⟨m, -, hm⟩ := (Ideal.IsPrime.prod_le (Ideal.isPrime_bot (α := A))).mp hprod
  have hm0 : m.asIdeal = ⊥ := le_bot_iff.mp hm
  exact isField_of_isMaximal_bot A (hm0 ▸ m.isMaximal)

end AlgebraicCurve.LInf

open AlgebraicCurve.LInf in
theorem solution
    {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c] :
    {x : C | IsClosed ({x} : Set C)}.Infinite := by
  classical

  obtain ⟨U, hU, V, hV, hηV, hle, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := c)
      (genericPoint C)
  have hfU : c.base (genericPoint C) ∈ U := hle hηV
  obtain rfl : U = ⊤ := top_le_iff.mp fun y _ => by
    rw [Subsingleton.elim y (c.base (genericPoint C))]; exact hfU
  let e : k ≃+* Γ(Spec (CommRingCat.of k), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  let ψ : k →+* Γ(C, V) := (c.appLE ⊤ V hle).hom.comp e.toRingHom
  have hψ : ψ.IsStandardSmoothOfRelativeDimension 1 :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _ e hstd
  letI : Algebra k Γ(C, V) := ψ.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 k Γ(C, V) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mp hψ
  haveI : Nonempty V := ⟨⟨_, hηV⟩⟩

  haveI : Algebra.FiniteType k Γ(C, V) := by
    obtain ⟨g, hg⟩ :=
      Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial 1 k Γ(C, V)
    letI : Algebra (MvPolynomial (Fin 1) k) Γ(C, V) := g.toRingHom.toAlgebra
    haveI : Algebra.Etale (MvPolynomial (Fin 1) k) Γ(C, V) := hg
    haveI : IsScalarTower k (MvPolynomial (Fin 1) k) Γ(C, V) :=
      IsScalarTower.of_algebraMap_eq fun a => (g.commutes a).symm
    exact (inferInstance : Algebra.FiniteType k (MvPolynomial (Fin 1) k)).trans
      (inferInstance : Algebra.FiniteType (MvPolynomial (Fin 1) k) Γ(C, V))
  haveI : IsJacobsonRing Γ(C, V) := isJacobsonRing_of_finiteType (A := k)

  have hnf : ¬ IsField Γ(C, V) := by
    intro hF
    obtain ⟨m, hm⟩ := Ideal.exists_maximal Γ(C, V)
    haveI := hm
    obtain ⟨_, hdvr⟩ :=
      Algebra.IsStandardSmoothOfRelativeDimension.isDiscreteValuationRing_localization_atPrime
        (k := k) m
    have h0 : (0 : Γ(C, V)) ∉ m.primeCompl := fun h => h m.zero_mem
    have hbij := hF.localization_map_bijective (Rₘ := Localization.AtPrime m) h0
    exact IsDiscreteValuationRing.not_isField (Localization.AtPrime m)
      ((RingEquiv.ofBijective _ hbij).symm.toMulEquiv.isField hF)

  by_contra hinf
  have hfin : {x : C | IsClosed ({x} : Set C)}.Finite := Set.not_infinite.mp hinf
  let g : MaximalSpectrum Γ(C, V) → C := fun m => hV.fromSpec ⟨m.asIdeal, m.isMaximal.isPrime⟩
  have hg_closed : ∀ m, IsClosed ({g m} : Set C) := by
    intro m
    apply AlgebraicCurve.isClosed_singleton_of_ne_genericPoint c
    intro hη
    apply hnf
    have hbot : (⟨m.asIdeal, m.isMaximal.isPrime⟩ : PrimeSpectrum Γ(C, V)) = ⊥ := by
      apply hV.fromSpec.isOpenEmbedding.injective
      change g m = _
      rw [hη, ← genericPoint_eq_bot_of_affine, genericPoint_eq_of_isOpenImmersion hV.fromSpec]
    have hm0 : m.asIdeal = ⊥ := congrArg PrimeSpectrum.asIdeal hbot
    exact isField_of_isMaximal_bot _ (hm0 ▸ m.isMaximal)
  have hg_inj : Function.Injective g := by
    intro m m' h
    have h' := hV.fromSpec.isOpenEmbedding.injective h
    exact MaximalSpectrum.ext (congrArg PrimeSpectrum.asIdeal h')
  haveI : Finite (MaximalSpectrum Γ(C, V)) := by
    haveI := hfin.to_subtype
    refine Finite.of_injective
      (fun m => (⟨g m, hg_closed m⟩ : {x : C | IsClosed ({x} : Set C)})) ?_
    intro m m' h
    apply hg_inj
    simp only [Subtype.mk.injEq] at h
    exact h
  exact hnf (isField_of_finite_maximalSpectrum Γ(C, V))

end S_AlgebraicCurve_infinite_setOf_isClosed_singleton
end P2MW
export P2MW.S_AlgebraicCurve_infinite_setOf_isClosed_singleton (solution)
