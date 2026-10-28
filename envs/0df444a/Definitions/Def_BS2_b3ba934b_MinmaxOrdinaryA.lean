-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxOrdinaryA
-- name    : BS2_b3ba934b_MinmaxOrdinaryA
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:42:35.341965+00:00
-- url     : https://prove2.me/theorems/55ff815d-0aa7-4505-93a3-8db2f62ff2cb
-- title:
--   Sensitivity separation: MinmaxOrdinaryA (complete source module)
-- statement:
--   Complete Lean source module `MinmaxOrdinaryA` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxOrdinaryA.lean; original SHA-256 2586c8286c7510760115ef639513425ab4d4b22532e46c7f475049b6ac6710a4; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Ordinary entries and ordinary upper components in the min/max numeric API. -/
import Definitions.Def_BS2_b3ba934b_MinmaxEntryMatch

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxNumeric
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional ThreeBoundMinmaxTransfer ThreeBoundNumeric ThreeBoundFullProfile
open scoped Classical
noncomputable section
variable {n : ℕ} {I : Type} [Fintype I]

theorem ordinaryEntriesAExpr_bound (S : Stage (Fin n) I (Fin 10007))
    (hAdj : S.Adj=ThreeBoundOrdinarySelected.Adj) (hLabel : S.label=Sensitivity10007BoolCaps.label)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F) (recipe : Fin n → Entry)
    (i j : Fin n) (P : ThreeBoundMinmaxTransfer.PairData S F i j)
    (hm : EntryMatch S F i j P (recipe i) (recipe j))
    (hi : (recipe i).ordinary=true) (hj : (recipe j).ordinary=true)
    (hq8 : (recipe j).tolerance ≤ 8) (v : Profile n) (hv : Upper F v) :
    ABound (parent S F) i j
      ((ordinaryAExpr n ThreeBoundConditionalNumeric.ordinaryCaps10007
        ((recipe i).lowerAt 0) (recipe i).guard (recipe i).tolerance
        ((recipe j).lowerAt 0) (recipe j).guard (recipe j).tolerance).eval v) := by
  intro x hx
  rw [matched_ordinary_weak S F i j P (recipe i) (recipe j) hm hi] at hx
  rw [matched_ordinary_strong S F i j P (recipe i) (recipe j) hm hj]
  have hh := ThreeBoundConditionalNumeric.ordinaryAExpr_bound S hAdj hLabel F hF
    (P.weakLower 0) (P.strongLower 0) (S.guard i) (S.guard j)
    (P.lowerOrder 0 (Nat.zero_le _)) P.guards (P.weakGuardTarget 0 (Nat.zero_le _))
    (S.tolerance i) (S.tolerance j) P.tolerances (by simpa only [hm.strongTolerance] using hq8) v hv x hx
  simpa only [hm.weakLower 0 (Nat.zero_le _),hm.strongLower 0 (Nat.zero_le _),
    hm.weakGuard,hm.strongGuard,hm.weakTolerance,hm.strongTolerance] using hh

theorem ordinaryComponentAExpr_bound (S : Stage (Fin n) I (Fin 10007))
    (hAdj : S.Adj=ThreeBoundOrdinarySelected.Adj) (hLabel : S.label=Sensitivity10007BoolCaps.label)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F) (recipe : Fin n → Entry)
    (i j : Fin n) (P : ThreeBoundMinmaxTransfer.PairData S F i j)
    (hm : EntryMatch S F i j P (recipe i) (recipe j))
    (level : ℕ) (hlevel : level ≤ (recipe i).tolerance)
    (hq : (recipe j).tolerance ≤ level) (hq8 : (recipe j).tolerance ≤ 8)
    (hthreshold : (recipe i).upperAt level ≤ (recipe j).lowerAt 0)
    (hordinary : (recipe j).ordinary=true) (v : Profile n) (hv : Upper F v) :
    ABound (parent S F) i j
      ((ordinaryAExpr n ThreeBoundConditionalNumeric.ordinaryCaps10007
        ((recipe i).upperAt level) (recipe i).guard level
        ((recipe j).lowerAt 0) (recipe j).guard (recipe j).tolerance).eval v) := by
  have hlevel' : level ≤ S.tolerance i := by simpa only [hm.weakTolerance] using hlevel
  have hq' : S.tolerance j ≤ level := by simpa only [hm.strongTolerance] using hq
  have ht : P.weakUpper level ≤ P.strongLower 0 := by
    change (P.weakUpper level).val ≤ (P.strongLower 0).val
    rw [hm.weakUpper level hlevel',hm.strongLower 0 (Nat.zero_le _)]
    exact hthreshold
  have hh := ordinary_upper_component_AExpr_bound S hAdj hLabel F hF i j P level hlevel' hq'
    (by simpa only [hm.strongTolerance] using hq8) (P.strongLower 0) ht
    (matched_ordinary_strong S F i j P (recipe i) (recipe j) hm hordinary) v hv
  simpa only [hm.weakUpper level hlevel',hm.strongLower 0 (Nat.zero_le _),
    hm.weakGuard,hm.strongGuard,hm.strongTolerance] using hh

end
end ThreeBoundMinmaxNumeric

#print axioms ThreeBoundMinmaxNumeric.ordinaryEntriesAExpr_bound
#print axioms ThreeBoundMinmaxNumeric.ordinaryComponentAExpr_bound


