-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:56.483846+00:00
-- url     : https://prove2.me/theorems/a2b56112-6ee2-4eb8-997f-6823c8c71977
-- title:
--   Not Is Unit Of Num Mem
-- statement:
--   Definitions and structural lemmas for Not Is Unit Of Num Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsUnitOfNumMem.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_X_cf870dae9c4f
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isMultiHomog_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace regularityLocalResidue_holds
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
def quotEquivMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Surjective f)
    (I : Ideal R) (hI : RingHom.ker f ≤ I) : R ⧸ I ≃+* S ⧸ I.map f :=
  (Ideal.quotEquivOfEq (by
    ext x
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap,
      Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hI])).trans
    (RingHom.quotientKerEquivOfSurjective (f := (Ideal.Quotient.mk (I.map f)).comp f)
      (Ideal.Quotient.mk_surjective.comp hf))
section Loc
variable (P : Ideal (MRing ι))
def frHom : MRing ι →+* FractionRing (MRing ι ⧸ P) :=
  (algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P))).comp (Ideal.Quotient.mk P)
variable {P} [P.IsPrime]
theorem mem_locRing_of_form {W : Ideal (MRing ι)} (hPW : P ≤ W) {u v : MRing ι} {a : K → ℕ}
    (hu : IsMultiHomog u a) (hv : IsMultiHomog v a) (hvW : v ∉ W) :
    frHom P u * (frHom P v)⁻¹ ∈ locRing P W := by
  have hv0 : Ideal.Quotient.mk P v ≠ 0 := fun h => hvW (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))
  have hnz : Ideal.Quotient.mk P v ∈ nonZeroDivisors (MRing ι ⧸ P) := mem_nonZeroDivisors_of_ne_zero hv0
  refine Subring.subset_closure ⟨u, v, a, hnz, hvW, hu, hv, ?_⟩
  rw [IsFractionRing.mk'_eq_div, div_eq_mul_inv]
  rfl
def chartMap {W : Ideal (MRing ι)} (hPW : P ≤ W) (T : ∀ k, ι k) (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι) ∉ W) :
    MRing ι →+* locRing P W :=
  eval₂Hom (Int.castRingHom _) fun p =>
    ⟨frHom P (X p) * (frHom P (X ⟨p.1, T p.1⟩))⁻¹, by
      classical
      exact mem_locRing_of_form hPW (AvoidRing.isMultiHomog_X p.1 p.2) (AvoidRing.isMultiHomog_X p.1 (T p.1)) (hT p.1)⟩
end Loc
end regularityLocalResidue_holds
end
end GroundTheory.Heights₂.Heights.Inter


