-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.comap_ker_eq_top_and_finrank_eq_zero_of_closedPoint_notMem_support
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/59dc84de-96d5-5de0-ac7c-70de1e255429

import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_comap_ker_eq_top_and_finrank_eq_zero_of_closedPoint_notMem_support

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {O : Type u} [CommRing O] [IsLocalRing O] {X : Scheme.{u}}
    (σ : Spec (CommRingCat.of O) ⟶ X) [IsClosedImmersion σ]
    (J : X.IdealSheafData) (hJ : σ.base (IsLocalRing.closedPoint O) ∉ J.support)
    {k : Type u} [Field k] (y : J.subscheme ⟶ Spec (CommRingCat.of k)) :
    σ.ker.comap J.subschemeι = ⊤ ∧
      (σ.ker.comap J.subschemeι).IsInvertible ∧
      IsFinite ((σ.ker.comap J.subschemeι).subschemeι ≫ y) ∧
      ∀ q : Spec (CommRingCat.of k), ((σ.ker.comap J.subschemeι).subschemeι ≫ y).finrank q = 0 := by

  have hrange : ∀ x ∈ Set.range σ.base, x ∉ (J.support : Set X) := by
    rintro _ ⟨t, rfl⟩ ht
    exact hJ ((((IsLocalRing.specializes_closedPoint t).map σ.base.hom.continuous)).mem_closed J.support.isClosed ht)
  have hsupp : ((σ.ker).support : Set X) = Set.range σ.base := by
    rw [Scheme.Hom.support_ker, (Scheme.Hom.isClosedEmbedding σ).isClosed_range.closure_eq]

  have hK : σ.ker.comap J.subschemeι = ⊤ := by
    apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
    rw [Scheme.IdealSheafData.support_comap]
    refine le_bot_iff.mp fun w hw => ?_
    have hw' : J.subschemeι.base w ∈ ((σ.ker).support : Set X) := hw
    rw [hsupp] at hw'
    refine hrange _ hw' ?_
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨w, rfl⟩
  rw [hK]
  refine ⟨rfl, Scheme.IdealSheafData.isInvertible_top, inferInstance, fun q => ?_⟩

  generalize ((⊤ : (J.subscheme).IdealSheafData).subschemeι ≫ y) = g
  haveI : IsOpenImmersion g := isOpenImmersion_of_isEmpty g
  have hns : ¬ Surjective g := fun h => by
    obtain ⟨x, -⟩ := h.surj q
    exact isEmptyElim x
  rw [← Scheme.Hom.one_le_finrank_iff_surjective] at hns
  simp only [Pi.le_def, Pi.one_apply, not_forall, not_le, Nat.lt_one_iff] at hns
  obtain ⟨y', hy'⟩ := hns
  rwa [Subsingleton.elim q y']

end S_AlgebraicGeometry_Scheme_Hom_comap_ker_eq_top_and_finrank_eq_zero_of_closedPoint_notMem_support
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_comap_ker_eq_top_and_finrank_eq_zero_of_closedPoint_notMem_support (solution)
