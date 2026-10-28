-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint16PlainA
-- name    : BS2_b3ba934b_Endpoint16PlainA
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:43:16.324158+00:00
-- url     : https://prove2.me/theorems/520f4864-f622-4b58-b94b-47e31f026e64
-- title:
--   Sensitivity separation: Endpoint16PlainA (complete source module)
-- statement:
--   Complete Lean source module `Endpoint16PlainA` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16PlainA.lean; original SHA-256 235be863fc8b5cbad90afd230c7d18fad4ed178b42c8b1e17c1d0bf897610c0a; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Exact plain-entry compatibility for the sixteen-level min/max endpoint. -/
import Definitions.Def_BS2_b3ba934b_Endpoint16PairData
import Definitions.Def_BS2_b3ba934b_OrdinaryZeroGraded

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
set_option linter.unusedSectionVars false

namespace ThreeBoundEndpoint16Plain
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive ThreeBoundNesting
open ThreeBoundConditional ThreeBoundConditionalNumeric ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundGradedCandidates ThreeBoundHeadExpressions
open scoped Classical
noncomputable section

theorem plain_fields : ∀ (p : Fin 4) (l : Fin 16),
    (ThreeBoundMinmaxNumeric.Endpoint16.recipe p l).plain=true →
    (Sensitivity10007Endpoint16.entry p l).t0=(Sensitivity10007Endpoint16.entry p l).u0 ∧
    (Sensitivity10007Endpoint16.entry p l).t1=(Sensitivity10007Endpoint16.entry p l).u1 ∧
    (Sensitivity10007Endpoint16.entry p l).t2=(Sensitivity10007Endpoint16.entry p l).u2 := by decide +kernel

theorem plain_tolerance : ∀ (p : Fin 4) (l : Fin 16),
    (ThreeBoundMinmaxNumeric.Endpoint16.recipe p l).plain=true →
    (ThreeBoundMinmaxNumeric.Endpoint16.recipe p l).tolerance=0 ∨
      3 ≤ (ThreeBoundMinmaxNumeric.Endpoint16.recipe p l).tolerance := by decide +kernel

theorem plain_curves (p : Fin 4) (l : Fin 16)
    (hp : (ThreeBoundMinmaxNumeric.Endpoint16.recipe p l).plain=true) (d : ℕ) :
    (Sensitivity10007Endpoint16.entry p l).upper d=(Sensitivity10007Endpoint16.entry p l).threshold d := by
  obtain ⟨h0,h1,h2⟩ := plain_fields p l hp
  simp only [Sensitivity10007Endpoint16.Entry.threshold,Sensitivity10007Endpoint16.Entry.upper,h0,h1,h2]

theorem numeric_lower_bounded (p : Fin 4) (l : Fin 16) (d : ℕ) (hd : d<9) :
    ((Sensitivity10007Endpoint16.entry p l).threshold d).val=
      (ThreeBoundMinmaxNumeric.Endpoint16.recipe p l).lowerAt d := by
  simp [ThreeBoundMinmaxNumeric.Endpoint16.recipe,ThreeBoundMinmaxNumeric.Entry.lowerAt,Array.getD,hd]

theorem numeric_base_threshold (p : Fin 4) (l : Fin 16) (d : ℕ) :
    ((Sensitivity10007Endpoint16.entry p l).threshold d).val=
      (ThreeBoundMinmaxNumeric.Endpoint16.recipe p l).base.threshold d := by
  unfold ThreeBoundNumeric.Entry.threshold ThreeBoundMinmaxNumeric.Entry.base
  rw [← numeric_lower_bounded p l 0 (by decide),← numeric_lower_bounded p l 1 (by decide),
    ← numeric_lower_bounded p l 2 (by decide)]
  change ((Sensitivity10007Endpoint16.entry p l).threshold d).val =
    if 3 ≤ (Sensitivity10007Endpoint16.entry p l).tolerance ∨ d=0 then
      ((Sensitivity10007Endpoint16.entry p l).threshold 0).val else
      if d=1 then ((Sensitivity10007Endpoint16.entry p l).threshold 1).val else
        ((Sensitivity10007Endpoint16.entry p l).threshold 2).val
  simp only [Sensitivity10007Endpoint16.Entry.threshold]
  split_ifs <;> simp_all <;> omega

variable {I : Type} [Fintype I]

noncomputable def plainPairData (p : Fin 4) (F : Fin 16 → (I → Bool) → Bool)
    (i j : Fin 16) (hij : i ≤ j)
    (hi : (ThreeBoundMinmaxNumeric.Endpoint16.recipe p i).plain=true)
    (hj : (ThreeBoundMinmaxNumeric.Endpoint16.recipe p j).plain=true) :
    PairData ((Sensitivity10007Endpoint16.recipe p).stage F) F i j where
  weak := (Sensitivity10007Endpoint16.entry p i).threshold
  strong := (Sensitivity10007Endpoint16.entry p j).threshold
  weakMono := (Sensitivity10007Endpoint16.recipe_ordered p).lower_mono i
  strongMono := (Sensitivity10007Endpoint16.recipe_ordered p).lower_mono j
  guards := (Sensitivity10007Endpoint16.recipe_ordered p).guard hij
  tolerances := (Sensitivity10007Endpoint16.recipe_ordered p).tolerance hij
  targets := (Sensitivity10007Endpoint16.recipe_ordered p).lower_order i j hij
  weakDef d u z := by
    change ThreeBoundMinmaxTransfer.mm F ((Sensitivity10007Endpoint16.entry p i).threshold d)
      ((Sensitivity10007Endpoint16.entry p i).upper d) u z = _
    rw [plain_curves p i hi d,ThreeBoundMinmaxTransfer.mm_same]
  strongDef d u z := by
    change ThreeBoundMinmaxTransfer.mm F ((Sensitivity10007Endpoint16.entry p j).threshold d)
      ((Sensitivity10007Endpoint16.entry p j).upper d) u z = _
    rw [plain_curves p j hj d,ThreeBoundMinmaxTransfer.mm_same]
  weakGuardTarget d _ := ThreeBoundEndpoint16Pairs.entry_guard_le_threshold p i d
  guardTarget d _ := ThreeBoundEndpoint16Pairs.entry_guard_le_threshold p j d

theorem plainEntryMatch (p : Fin 4) (F : Fin 16 → (I → Bool) → Bool)
    (i j : Fin 16) (hij : i ≤ j)
    (hi : (ThreeBoundMinmaxNumeric.Endpoint16.recipe p i).plain=true)
    (hj : (ThreeBoundMinmaxNumeric.Endpoint16.recipe p j).plain=true) :
    EntryMatch ((Sensitivity10007Endpoint16.recipe p).stage F) F i j
      (plainPairData p F i j hij hi hj)
      (ThreeBoundMinmaxNumeric.Endpoint16.recipe p i).base
      (ThreeBoundMinmaxNumeric.Endpoint16.recipe p j).base where
  weakGuard := rfl
  strongGuard := rfl
  weakTolerance := rfl
  strongTolerance := rfl
  weakThreshold := numeric_base_threshold p i
  strongThreshold := numeric_base_threshold p j

theorem plain_rawA_bound (p : Fin 4) (F : Fin 16 → (I → Bool) → Bool) (hF : Nested F)
    (v : Profile 16) (hv : Upper F v) (records : List (List ℕ))
    (i j : Fin 16) (hij : i ≤ j)
    (hi : (ThreeBoundMinmaxNumeric.Endpoint16.recipe p i).plain=true)
    (hj : (ThreeBoundMinmaxNumeric.Endpoint16.recipe p j).plain=true) :
    ABound (parent ((Sensitivity10007Endpoint16.recipe p).stage F) F) i j
      ((ThreeBoundNumeric.rawAExpr 16 ordinaryCaps10007 records
        (ThreeBoundMinmaxNumeric.Endpoint16.recipe p i).base
        (ThreeBoundMinmaxNumeric.Endpoint16.recipe p j).base).eval v) := by
  let S := (Sensitivity10007Endpoint16.recipe p).stage F
  let r := fun l => (ThreeBoundMinmaxNumeric.Endpoint16.recipe p l).base
  let P := plainPairData p F i j hij hi hj
  have hm := plainEntryMatch p F i j hij hi hj
  have hAdj : S.Adj=ThreeBoundOrdinarySelected.Adj := rfl
  have hLabel : S.label=Sensitivity10007BoolCaps.label := rfl
  have hq8 : (r j).tolerance ≤ 8 := (Sensitivity10007Endpoint16.entry_internal_order p j).2.2.2.2
  rcases plain_tolerance p j hj with hzero | hlarge
  · exact rawAExpr_zero_bound S hAdj hLabel F hF r i j P hm records hzero v hv
  · exact rawAExpr_large_bound S hAdj hLabel F hF r i j P hm records hlarge hq8 v hv

end
end ThreeBoundEndpoint16Plain

#print axioms ThreeBoundEndpoint16Plain.plain_fields
#print axioms ThreeBoundEndpoint16Plain.plain_rawA_bound


