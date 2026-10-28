-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint16Transfer
-- name    : BS2_b3ba934b_Endpoint16Transfer
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T21:00:47.334701+00:00
-- url     : https://prove2.me/theorems/de25fa0c-427b-48e3-b5fa-ad8030bbedf9
-- title:
--   Sensitivity separation: Endpoint16Transfer (complete source module)
-- statement:
--   Complete Lean source module `Endpoint16Transfer` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16Transfer.lean; original SHA-256 3e140a43bc9c44798fb43cc73d3d8418514069d9573fdb0b0440cd04d177a315; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Full second-endpoint transfer assembly. The strict-zero A estimate is a
separate semantic theorem and is supplied here at the final interface. -/
import Definitions.Def_BS2_b3ba934b_MinmaxRawTransfer
import Definitions.Def_BS2_b3ba934b_MinmaxACombination
import Definitions.Def_BS2_b3ba934b_MinmaxQ2Bound
import Definitions.Def_BS2_b3ba934b_Endpoint16PlainA
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Definitions.Def_BS2_b3ba934b_Endpoint40Caps

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

namespace ThreeBoundEndpoint16Transfer
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundNumeric ThreeBoundFullProfile ThreeBoundMinmaxNumeric
open ThreeBoundEndpoint16Pairs ThreeBoundEndpoint40Caps
open scoped Classical
noncomputable section
variable {I : Type} [Fintype I]

theorem caps_eq : ThreeBoundMinmaxNumeric.Endpoint16.caps=ThreeBoundConditionalNumeric.ordinaryCaps10007 := rfl

theorem stage_tournament (p : Fin 4) (F : Fin 16 → (I → Bool) → Bool) :
    TournamentHighRows.IsTournament ((Sensitivity10007Endpoint16.recipe p).stage F).Adj :=
  ⟨Sensitivity10007Labeling.Labeling10007.irreflexive,Sensitivity10007Labeling.Labeling10007.edge_compl⟩

theorem stage_outdegree (p : Fin 4) (F : Fin 16 → (I → Bool) → Bool) (w : Fin 10007) :
    (outgoing ((Sensitivity10007Endpoint16.recipe p).stage F) w).card=5003 :=
  Sensitivity10007Labeling.Labeling10007.outdegree w

theorem stage_source (p : Fin 4) (F : Fin 16 → (I → Bool) → Bool) :
    @ResidualCaps.DominatorCardBound (Fin 10007) (fun a b => Classical.propDecidable (a=b))
      ((Sensitivity10007Endpoint16.recipe p).stage F).Adj
      ((Sensitivity10007Endpoint16.recipe p).stage F).label 1
      (ThreeBoundMinmaxNumeric.Endpoint16.caps.pcross+1) := by
  intro A M color hdis hM hdom hmis
  apply Sensitivity10007BoolCaps.selected_source A M color hdis hM hdom
  intro w hw
  exact hmis w (by simpa only [Finset.mem_union] using hw)

theorem stage_caps_sound (p : Fin 4) (F : Fin 16 → (I → Bool) → Bool) :
    ThreeBoundActualCaps.CapsSound ((Sensitivity10007Endpoint16.recipe p).stage F).Adj
      ((Sensitivity10007Endpoint16.recipe p).stage F).label ThreeBoundMinmaxNumeric.Endpoint16.caps :=
  ThreeBoundEndpoint40Caps.caps_sound

theorem large_plain : ∀ (p : Fin 4) (i : Fin 16),
    3 ≤ (ThreeBoundMinmaxNumeric.Endpoint16.recipe p i).tolerance →
    (ThreeBoundMinmaxNumeric.Endpoint16.recipe p i).plain=true := by decide +kernel

def ZeroBound (p : Fin 4) (F : Fin 16 → (I → Bool) → Bool) (v : Profile 16) : Prop :=
  ∀ (i j : Fin 16), i ≤ j → (ThreeBoundMinmaxNumeric.Endpoint16.recipe p j).tolerance=0 →
    ABound (parent ((Sensitivity10007Endpoint16.recipe p).stage F) F) i j
      ((ThreeBoundMinmaxA.zeroAExpr 16 ThreeBoundMinmaxNumeric.Endpoint16.caps
        (ThreeBoundMinmaxNumeric.Endpoint16.recipe p i) (ThreeBoundMinmaxNumeric.Endpoint16.recipe p j)).eval v)

theorem rawA_bound_of_zero (p : Fin 4) (F : Fin 16 → (I → Bool) → Bool) (hF : Nested F)
    (v : Profile 16) (hv : Upper F v) (hordered : Ordered v)
    (hrecords : ∀ xs ∈ ThreeBoundQ2.records, xs ∈ ThreeBoundMinmaxNumeric.Endpoint16.records)
    (hzero : ZeroBound p F v) (i j : Fin 16) (hij : i ≤ j) :
    ABound (parent ((Sensitivity10007Endpoint16.recipe p).stage F) F) i j
      ((ThreeBoundMinmaxA.rawAExpr 16 ThreeBoundMinmaxNumeric.Endpoint16.caps ThreeBoundMinmaxNumeric.Endpoint16.records
        (ThreeBoundMinmaxNumeric.Endpoint16.recipe p i) (ThreeBoundMinmaxNumeric.Endpoint16.recipe p j)).eval v) := by
  let S := (Sensitivity10007Endpoint16.recipe p).stage F
  let P := pairData p F i j hij
  have hm := entryMatch p F i j hij
  by_cases hplain : ((ThreeBoundMinmaxNumeric.Endpoint16.recipe p i).plain &&
      (ThreeBoundMinmaxNumeric.Endpoint16.recipe p j).plain)=true
  · rw [ThreeBoundMinmaxA.rawAExpr,if_pos hplain,caps_eq]
    have hboth : (ThreeBoundMinmaxNumeric.Endpoint16.recipe p i).plain=true ∧
        (ThreeBoundMinmaxNumeric.Endpoint16.recipe p j).plain=true := by
      simpa only [Bool.and_eq_true] using hplain
    obtain ⟨hi,hj⟩ := hboth
    exact ThreeBoundEndpoint16Plain.plain_rawA_bound p F hF v hv ThreeBoundMinmaxNumeric.Endpoint16.records i j hij hi hj
  · by_cases hz : (ThreeBoundMinmaxNumeric.Endpoint16.recipe p j).tolerance=0
    · rw [ThreeBoundMinmaxA.rawAExpr,if_neg hplain,if_pos hz]
      exact hzero i j hij hz
    · have hq2 : (ThreeBoundMinmaxNumeric.Endpoint16.recipe p j).tolerance ≤ 2 := by
        by_contra hn
        have hjlarge : 3 ≤ (ThreeBoundMinmaxNumeric.Endpoint16.recipe p j).tolerance := by omega
        have hq := (Sensitivity10007Endpoint16.entry_pair_order p i j hij).2.1
        have hilarge : 3 ≤ (ThreeBoundMinmaxNumeric.Endpoint16.recipe p i).tolerance := by
          change 3 ≤ (Sensitivity10007Endpoint16.entry p i).tolerance
          exact hjlarge.trans hq
        exact hplain (by simp only [large_plain p i hilarge,large_plain p j hjlarge,Bool.and_self])
      rw [caps_eq]
      apply ThreeBoundMinmaxA.rawAExpr_small_bound S (by rfl) (by rfl) F hF
        (ThreeBoundMinmaxNumeric.Endpoint16.recipe p) i j P hm ThreeBoundMinmaxNumeric.Endpoint16.records
        hplain (by omega) (by omega) v hv
      have hh := ThreeBoundMinmaxA.gradedAExpr_bound S (stage_tournament p F) F hF i j P
        (ThreeBoundMinmaxNumeric.Endpoint16.recipe p i) (ThreeBoundMinmaxNumeric.Endpoint16.recipe p j) hm
        (show S.tolerance j ≤ 2 from hq2) ThreeBoundMinmaxNumeric.Endpoint16.caps (stage_caps_sound p F)
        ThreeBoundMinmaxNumeric.Endpoint16.records hrecords v hv hordered
      simpa only [caps_eq] using hh

theorem raw_sound_of_zero (p : Fin 4) (F : Fin 16 → (I → Bool) → Bool) (hF : Nested F)
    (v : Profile 16) (hv : Upper F v) (hordered : Ordered v)
    (hrecords : ∀ xs ∈ ThreeBoundQ2.records, xs ∈ ThreeBoundMinmaxNumeric.Endpoint16.records)
    (hzero : ZeroBound p F v) :
    Upper (parent ((Sensitivity10007Endpoint16.recipe p).stage F) F)
      (ThreeBoundMinmaxNumeric.Endpoint16.raw p v) := by
  exact ThreeBoundMinmaxNumeric.rawTransfer_sound ((Sensitivity10007Endpoint16.recipe p).stage F)
    (stage_tournament p F) F hF (ThreeBoundMinmaxNumeric.Endpoint16.recipe p) (pairData p F) (entryMatch p F)
    5003 ThreeBoundMinmaxNumeric.Endpoint16.caps.pcross
    (ThreeBoundMinmaxA.rawAExpr 16 ThreeBoundMinmaxNumeric.Endpoint16.caps ThreeBoundMinmaxNumeric.Endpoint16.records)
    (stage_outdegree p F) (stage_source p F) v hv (rawA_bound_of_zero p F hF v hv hordered hrecords hzero)

end
end ThreeBoundEndpoint16Transfer

#print axioms ThreeBoundEndpoint16Transfer.rawA_bound_of_zero
#print axioms ThreeBoundEndpoint16Transfer.raw_sound_of_zero


