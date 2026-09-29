-- Prove2me | solution 1 for AlgebraicCurve.Place.finite_setOf_deg_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/9f13d8a3-41e2-50ee-a9e5-fcc99da8326b

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_subsingleton_setOf_forall_ne_ofHeightOneSpectrum
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_finite_setOf_deg_eq

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_finite_setOf_deg_eq.AlgebraicCurve IsDedekindDomain Polynomial IntermediateField"

open scoped Polynomial

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ofHeightOneSpectrum IsCurveOver IsCurveOver.finite_residueField Place.restrict Place.restrict_fiber_finite RationalFunctionField.exists_irreducible_span RationalFunctionField.deg_ofHeightOneSpectrum RationalFunctionField.subsingleton_setOf_forall_ne_ofHeightOneSpectrum IsCurveOver.exists_separating_transcendental"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg ofHeightOneSpectrum restrict restrict_fiber_finite inertiaDeg deg_restrict_mul_inertiaDeg"
namespace FiniteSetOfDegEqAux
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

theorem finite_setOf_natDegree_le (K : Type*) [Field K] [Finite K] (d : ℕ) :
    {g : K[X] | g.natDegree ≤ d}.Finite := by
  haveI : Finite (Polynomial.degreeLT K (d + 1)) :=
    Finite.of_equiv (Fin (d + 1) → K) (Polynomial.degreeLTEquiv K (d + 1)).symm.toEquiv
  refine Set.Finite.subset (Set.toFinite (Polynomial.degreeLT K (d + 1) : Set K[X])) ?_
  intro g hg
  rw [Set.mem_setOf_eq] at hg
  rw [SetLike.mem_coe, Polynomial.mem_degreeLT]
  exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hg)

theorem finite_heightOneSpectrum_of_deg_eq (K : Type*) [Field K] [Finite K] (d : ℕ) :
    {w : HeightOneSpectrum K[X] |
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).deg = d}.Finite := by
  have hfin : ((fun g : K[X] => (Ideal.span {g} : Ideal K[X])) ''
      {g : K[X] | g.natDegree ≤ d}).Finite := (finite_setOf_natDegree_le K d).image _
  have hpre : ((fun w : HeightOneSpectrum K[X] => w.asIdeal) ⁻¹'
      ((fun g : K[X] => (Ideal.span {g} : Ideal K[X])) '' {g : K[X] | g.natDegree ≤ d})).Finite :=
    hfin.preimage fun w _ w' _ h => HeightOneSpectrum.ext h
  refine hpre.subset fun w hw => ?_
  obtain ⟨p, _hpirr, hwI⟩ := RationalFunctionField.exists_irreducible_span K w
  rw [Set.mem_setOf_eq, RationalFunctionField.deg_ofHeightOneSpectrum K hwI] at hw
  exact ⟨p, le_of_eq hw, hwI.symm⟩

theorem finite_setOf_ratFunc_place_deg_eq (K : Type*) [Field K] [Finite K] (d : ℕ) :
    {v : Place K (RatFunc K) | v.deg = d}.Finite := by
  refine Set.Finite.subset
    (Set.Finite.union
      (Set.Finite.image (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K))
        (finite_heightOneSpectrum_of_deg_eq K d))
      (Set.Subsingleton.finite
        (RationalFunctionField.subsingleton_setOf_forall_ne_ofHeightOneSpectrum (K := K))))
    fun v hv => ?_
  rw [Set.mem_setOf_eq] at hv
  simp only [Set.mem_union, Set.mem_image, Set.mem_setOf_eq]
  by_cases hcase : ∃ w : HeightOneSpectrum K[X], v = Place.ofHeightOneSpectrum (K := K) w
  · obtain ⟨w, rfl⟩ := hcase
    exact Or.inl ⟨w, hv, rfl⟩
  · exact Or.inr fun w h => hcase ⟨w, h⟩

theorem exists_ratFunc_intermediate (K F : Type*) [Field K] [Finite K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    ∃ (_ : Algebra (RatFunc K) F) (_ : IsScalarTower K (RatFunc K) F)
      (_ : Algebra.IsIntegral (RatFunc K) F), Module.Finite (RatFunc K) F := by

  haveI : PerfectField K := inferInstance
  obtain ⟨t, htr, hfd, _⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := F)

  let e : RatFunc K ≃ₐ[K] K⟮t⟯ := RatFunc.algEquivOfTranscendental t htr
  letI iAlgF : Algebra (RatFunc K) F := ((K⟮t⟯.val).comp e.toAlgHom).toRingHom.toAlgebra
  letI iAlgKt : Algebra (RatFunc K) K⟮t⟯ := e.toAlgHom.toRingHom.toAlgebra
  haveI iSTF : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun a => (((K⟮t⟯.val).comp e.toAlgHom).commutes a).symm
  haveI iSTtF : IsScalarTower (RatFunc K) K⟮t⟯ F :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl

  haveI iFinKt : Module.Finite (RatFunc K) K⟮t⟯ :=
    ⟨⟨{1}, by
      rw [Finset.coe_singleton, Submodule.span_singleton_eq_top_iff]
      exact fun x => ⟨e.symm x, by
        show algebraMap (RatFunc K) K⟮t⟯ (e.symm x) * 1 = x
        rw [mul_one]; exact e.apply_symm_apply x⟩⟩⟩
  haveI iFinF : Module.Finite (RatFunc K) F := Module.Finite.trans K⟮t⟯ F
  haveI iIntF : Algebra.IsIntegral (RatFunc K) F := Algebra.IsIntegral.of_finite (RatFunc K) F
  exact ⟨iAlgF, iSTF, iIntF, iFinF⟩

end AlgebraicCurve.Place.FiniteSetOfDegEqAux

open AlgebraicCurve.Place.FiniteSetOfDegEqAux in

theorem solution
    (K F : Type*) [Field K] [Finite K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F] (d : ℕ) :
    {v : Place K F | v.deg = d}.Finite := by
  obtain ⟨iAlg, iST, iInt, iFin⟩ := exists_ratFunc_intermediate K F

  have hsub : {w : Place K F | w.deg = d}
      ⊆ ⋃ v ∈ (⋃ d' ∈ Finset.range (d + 1), {v : Place K (RatFunc K) | v.deg = d'}),
          {w : Place K F | w.restrict (RatFunc K) = v} := by
    intro w hw
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_range, exists_prop]
    refine ⟨w.restrict (RatFunc K), ⟨(w.restrict (RatFunc K)).deg, ?_, rfl⟩, rfl⟩
    have htow := w.deg_restrict_mul_inertiaDeg (F := RatFunc K)
    haveI : Module.Finite K w.ResidueField := IsCurveOver.finite_residueField w
    have hdpos : 0 < w.deg := by
      show 0 < Module.finrank K w.ResidueField
      exact Module.finrank_pos
    rw [Set.mem_setOf_eq] at hw
    have hine : 0 < w.inertiaDeg (RatFunc K) := by
      rcases Nat.eq_zero_or_pos (w.inertiaDeg (RatFunc K)) with h0 | hp
      · exfalso; rw [h0, Nat.mul_zero] at htow; omega
      · exact hp
    calc (w.restrict (RatFunc K)).deg
        ≤ (w.restrict (RatFunc K)).deg * w.inertiaDeg (RatFunc K) :=
          Nat.le_mul_of_pos_right _ hine
      _ = d := htow.trans hw
      _ < d + 1 := Nat.lt_succ_self d
  refine Set.Finite.subset ?_ hsub
  refine Set.Finite.biUnion ?_ fun v _ => Place.restrict_fiber_finite v
  exact Set.Finite.biUnion (Finset.range (d + 1)).finite_toSet
    fun d' _ => finite_setOf_ratFunc_place_deg_eq K d'

end S_AlgebraicCurve_Place_finite_setOf_deg_eq
end P2MW
export P2MW.S_AlgebraicCurve_Place_finite_setOf_deg_eq (solution)
