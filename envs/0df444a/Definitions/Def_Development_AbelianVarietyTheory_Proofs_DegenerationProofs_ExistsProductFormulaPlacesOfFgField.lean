-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsProductFormulaPlacesOfFgField
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsProductFormulaPlacesOfFgField
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T14:29:00.489591+00:00
-- url     : https://prove2.me/theorems/d718ef2a-3d2f-4c2e-bdb2-4c8f756ce8f6
-- title:
--   Exists Product Formula Places Of Fg Field
-- statement:
--   Definitions and structural lemmas for Exists Product Formula Places Of Fg Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsProductFormulaPlacesOfFgField.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsProductFormulaPlacesFunctionFieldStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS
def Places.sigma {k K : Type} [Field k] [Field K] [Algebra k K] {J : Type} [Finite J]
    (F : J → IntermediateField k K) (P : ∀ j, Places (F j) K) : Places k K where
  I := Σ j, (P j).I
  O := fun i => (P i.1).O i.2
  v := fun i => (P i.1).v i.2
  v_mul := fun i => (P i.1).v_mul i.2
  mem := fun i => (P i.1).mem i.2
  const := fun i c => (P i.1).const i.2 (algebraMap k (F i.1) c)
  fin := fun x => by
    refine (Set.finite_iUnion fun j => ((P j).fin x).image (Sigma.mk (β := fun j => (P j).I) j)).subset ?_
    rintro ⟨j, i⟩ hi
    exact Set.mem_iUnion.2 ⟨j, i, hi, rfl⟩
  sum := fun x => by
    classical
    have := Fintype.ofFinite J
    rw [finsum_eq_sum_of_support_subset (s := Finset.univ.sigma fun j => ((P j).fin x).toFinset),
      Finset.sum_sigma]
    · refine Finset.sum_eq_zero fun j _ => ?_
      rw [← (P j).sum x, finsum_eq_sum _ ((P j).fin x)]
    · rintro ⟨j, i⟩ hi
      simpa using hi
end GlobalTheory.SS
end


