-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40Transfer
-- name    : BS2_b3ba934b_Endpoint40Transfer
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:38:45.77733+00:00
-- url     : https://prove2.me/theorems/498e0fcf-ce25-4e87-b698-c239966f932d
-- title:
--   Sensitivity separation: Endpoint40Transfer (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40Transfer` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40Transfer.lean; original SHA-256 930d5e5b7043a61298cd6bfc3e0f0973bf7796bb283778a1128812386ddb00b2; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Complete raw five-profile transfer for the actual first-endpoint recipe.
Every local sensitivity bound is proved from concrete predicates and flips.
The finite record containment certificate is an explicit final input. -/
import Definitions.Def_BS2_b3ba934b_RawACombination
import Definitions.Def_BS2_b3ba934b_RawTransferSemantics
import Definitions.Def_BS2_b3ba934b_Endpoint40PairData
import Definitions.Def_BS2_b3ba934b_Endpoint40Caps

set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 100000

namespace ThreeBoundEndpoint40Transfer
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundNumeric ThreeBoundFullProfile ThreeBoundConditionalNumeric
open ThreeBoundGradedCandidates ThreeBoundHeadExpressions ThreeBoundActualQ2Bound
open ThreeBoundEndpoint40Pairs ThreeBoundEndpoint40Caps
open scoped Classical
noncomputable section
variable {I : Type} [Fintype I]

theorem caps_eq : ThreeBoundNumeric.Endpoint40.caps=ordinaryCaps10007 := rfl

theorem stage_tournament (p : Fin 4) (F : Fin 40 → (I → Bool) → Bool) :
    TournamentHighRows.IsTournament ((Sensitivity10007Endpoint40.recipe p).stage F).Adj :=
  ⟨Sensitivity10007Labeling.Labeling10007.irreflexive,
    Sensitivity10007Labeling.Labeling10007.edge_compl⟩

theorem stage_outdegree (p : Fin 4) (F : Fin 40 → (I → Bool) → Bool) (w : Fin 10007) :
    (outgoing ((Sensitivity10007Endpoint40.recipe p).stage F) w).card=5003 :=
  Sensitivity10007Labeling.Labeling10007.outdegree w

theorem stage_source (p : Fin 4) (F : Fin 40 → (I → Bool) → Bool) :
    @ResidualCaps.DominatorCardBound (Fin 10007) (fun a b => Classical.propDecidable (a=b))
      ((Sensitivity10007Endpoint40.recipe p).stage F).Adj
      ((Sensitivity10007Endpoint40.recipe p).stage F).label 1
      (ThreeBoundNumeric.Endpoint40.caps.pcross+1) := by
  intro A M color hdis hM hdom hmis
  apply Sensitivity10007BoolCaps.selected_source A M color hdis hM hdom
  intro w hw
  exact hmis w (by simpa only [Finset.mem_union] using hw)

theorem rawA_bound (p : Fin 4) (F : Fin 40 → (I → Bool) → Bool) (hF : Nested F)
    (v : Profile 40) (hv : Upper F v) (hordered : Ordered v)
    (hrecords : ∀ xs ∈ ThreeBoundQ2.records, xs ∈ ThreeBoundNumeric.Endpoint40.records)
    (i j : Fin 40) (hij : i ≤ j) :
    ABound (parent ((Sensitivity10007Endpoint40.recipe p).stage F) F) i j
      ((rawAExpr 40 ThreeBoundNumeric.Endpoint40.caps ThreeBoundNumeric.Endpoint40.records
        (ThreeBoundNumeric.Endpoint40.recipe p i) (ThreeBoundNumeric.Endpoint40.recipe p j)).eval v) := by
  let S := (Sensitivity10007Endpoint40.recipe p).stage F
  let P := pairData p F i j hij
  have hm := entryMatch p F i j hij
  have hAdj : S.Adj=ThreeBoundOrdinarySelected.Adj := rfl
  have hLabel : S.label=Sensitivity10007BoolCaps.label := rfl
  have hq8 : (ThreeBoundNumeric.Endpoint40.recipe p j).tolerance ≤ 8 :=
    (Sensitivity10007Endpoint40.entry_internal_order p j).2.2
  rw [caps_eq]
  by_cases hzero : (ThreeBoundNumeric.Endpoint40.recipe p j).tolerance=0
  · exact rawAExpr_zero_bound S hAdj hLabel F hF (ThreeBoundNumeric.Endpoint40.recipe p)
      i j P hm ThreeBoundNumeric.Endpoint40.records hzero v hv
  · by_cases hlarge : 3 ≤ (ThreeBoundNumeric.Endpoint40.recipe p j).tolerance
    · exact rawAExpr_large_bound S hAdj hLabel F hF (ThreeBoundNumeric.Endpoint40.recipe p)
        i j P hm ThreeBoundNumeric.Endpoint40.records hlarge hq8 v hv
    · have hq2 : (ThreeBoundNumeric.Endpoint40.recipe p j).tolerance ≤ 2 := by omega
      apply rawAExpr_small_bound S hAdj hLabel F hF (ThreeBoundNumeric.Endpoint40.recipe p)
        i j P hm ThreeBoundNumeric.Endpoint40.records (by omega) hq2 v hv
      have hfirst := gradedAExpr_bound S (stage_tournament p F) F hF i j P
        (ThreeBoundNumeric.Endpoint40.recipe p i) (ThreeBoundNumeric.Endpoint40.recipe p j) hm
        (show S.tolerance j ≤ 2 from hq2) ThreeBoundNumeric.Endpoint40.caps
        (stage_caps_sound p F) ThreeBoundNumeric.Endpoint40.records hrecords v hv hordered
      simpa only [caps_eq] using hfirst

/-- The final raw transfer semantics, ready for the independently checked
numeric profile and closure inequalities. -/
theorem raw_sound (p : Fin 4) (F : Fin 40 → (I → Bool) → Bool) (hF : Nested F)
    (v : Profile 40) (hv : Upper F v) (hordered : Ordered v)
    (hrecords : ∀ xs ∈ ThreeBoundQ2.records, xs ∈ ThreeBoundNumeric.Endpoint40.records) :
    Upper (parent ((Sensitivity10007Endpoint40.recipe p).stage F) F)
      (ThreeBoundNumeric.Endpoint40.raw p v) := by
  exact rawTransfer_sound ((Sensitivity10007Endpoint40.recipe p).stage F) (stage_tournament p F)
    F hF (ThreeBoundNumeric.Endpoint40.recipe p) (pairData p F) (entryMatch p F)
    5003 (stage_outdegree p F) ThreeBoundNumeric.Endpoint40.caps ThreeBoundNumeric.Endpoint40.records
    (stage_source p F) v hv (rawA_bound p F hF v hv hordered hrecords)

end
end ThreeBoundEndpoint40Transfer

#print axioms ThreeBoundEndpoint40Transfer.rawA_bound
#print axioms ThreeBoundEndpoint40Transfer.raw_sound


