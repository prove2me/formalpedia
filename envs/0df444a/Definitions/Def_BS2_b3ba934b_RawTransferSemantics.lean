-- Prove2me | Definitions.Def_BS2_b3ba934b_RawTransferSemantics
-- name    : BS2_b3ba934b_RawTransferSemantics
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T05:47:04.50299+00:00
-- url     : https://prove2.me/theorems/9adba8cf-1dd5-4d0f-a9f4-22a48131be21
-- title:
--   Sensitivity separation: RawTransferSemantics (complete source module)
-- statement:
--   Complete Lean source module `RawTransferSemantics` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/RawTransferSemantics.lean; original SHA-256 451a208d1e9a1a9ee7c2025738e8e8f821fec2d4dd218544aa59d35414cd2e7d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Full five-profile raw transfer from the actual child and parent predicates.
The raw-A theorem is supplied separately; B/M/P/D are discharged here. -/
import Definitions.Def_BS2_b3ba934b_RawConditionalD

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace ThreeBoundConditionalNumeric
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundGradedCandidates ThreeBoundHeadExpressions
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem rawTransfer_sound (S : Stage (Fin n) I V)
    (hT : TournamentHighRows.IsTournament S.Adj)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F) (recipe : Fin n → Entry)
    (P : ∀ i j : Fin n, i ≤ j → PairData S F i j)
    (hm : ∀ (i j : Fin n) (hij : i ≤ j), EntryMatch S F i j (P i j hij) (recipe i) (recipe j))
    (degree : ℕ) (hd : ∀ w, (outgoing S w).card=degree)
    (caps : Caps) (records : List (List ℕ))
    (hcap : ResidualCaps.DominatorCardBound S.Adj S.label 1 (caps.pcross+1))
    (v : Profile n) (hv : Upper F v)
    (hA : ∀ i j : Fin n, i ≤ j →
      ABound (parent S F) i j ((rawAExpr n caps records (recipe i) (recipe j)).eval v)) :
    Upper (parent S F) (rawTransfer n degree caps records recipe v) := by
  intro c
  cases c with
  | a i j => exact hA i j
  | b i j =>
      intro hij
      exact rawBExpr_bound S F hF recipe i j (P i j hij) (hm i j hij) degree hd v hv
  | m i j =>
      intro hij _
      exact rawMExpr_bound S F hF recipe i j (next j)
        (P i j hij) (P j (next j) (self_le_next j))
        (hm i j hij) (hm j (next j) (self_le_next j)) degree hd v hv
  | p j l =>
      intro hjl
      exact rawPExpr_bound S hT F hF recipe j (next j) l
        (P j (next j) (self_le_next j)) (P (next j) l (next_le_of_lt j l hjl))
        (hm j (next j) (self_le_next j)) (hm (next j) l (next_le_of_lt j l hjl))
        degree caps records hcap v hv (hA (next j) l (next_le_of_lt j l hjl))
  | d i j l =>
      intro hij hjl
      have hjk := self_le_next j
      have hkl := next_le_of_lt j l hjl
      have hM := rawMExpr_bound S F hF recipe i j (next j)
        (P i j hij) (P j (next j) hjk) (hm i j hij) (hm j (next j) hjk) degree hd v hv
      have hP := rawPExpr_bound S hT F hF recipe j (next j) l
        (P j (next j) hjk) (P (next j) l hkl) (hm j (next j) hjk) (hm (next j) l hkl)
        degree caps records hcap v hv (hA (next j) l hkl)
      exact rawDExpr_bound S hT F hF recipe i j (next j) l
        (P i j hij) (P j (next j) hjk) (P (next j) l hkl)
        (hm i j hij) (hm j (next j) hjk) (hm (next j) l hkl) degree hd caps records v hv hM hP

end
end ThreeBoundConditionalNumeric

#print axioms ThreeBoundConditionalNumeric.rawTransfer_sound


