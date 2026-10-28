-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxRawTransfer
-- name    : BS2_b3ba934b_MinmaxRawTransfer
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:49:37.926323+00:00
-- url     : https://prove2.me/theorems/4375f0e2-1f16-454a-82b6-6a4854d7b0c0
-- title:
--   Sensitivity separation: MinmaxRawTransfer (complete source module)
-- statement:
--   Complete Lean source module `MinmaxRawTransfer` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxRawTransfer.lean; original SHA-256 c844714b61f832ff401eacf016a815217a65c3397a9a7721873684feb11acc11; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- All five exact profile bounds for actual min/max parent predicates.
Only the separately proved upward A estimate is an input. -/
import Definitions.Def_BS2_b3ba934b_MinmaxRawD

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace ThreeBoundMinmaxNumeric
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundMinmaxTransfer ThreeBoundNumeric ThreeBoundFullProfile
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem rawTransfer_sound (S : Stage (Fin n) I V)
    (hT : TournamentHighRows.IsTournament S.Adj)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F) (recipe : Fin n → Entry)
    (P : ∀ i j : Fin n, i ≤ j → ThreeBoundMinmaxTransfer.PairData S F i j)
    (hm : ∀ (i j : Fin n) (hij : i ≤ j), EntryMatch S F i j (P i j hij) (recipe i) (recipe j))
    (degree pcross : ℕ) (rawA : Entry → Entry → Expr n)
    (hd : ∀ w, (outgoing S w).card=degree)
    (hcap : ResidualCaps.DominatorCardBound S.Adj S.label 1 (pcross+1))
    (v : Profile n) (hv : Upper F v)
    (hA : ∀ i j : Fin n, i ≤ j → ABound (parent S F) i j ((rawA (recipe i) (recipe j)).eval v)) :
    Upper (parent S F) (rawTransfer n degree pcross rawA recipe v) := by
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
        pcross rawA hcap v hv (hA (next j) l (next_le_of_lt j l hjl))
  | d i j l =>
      intro hij hjl
      have hjk := self_le_next j
      have hkl := next_le_of_lt j l hjl
      have hM := rawMExpr_bound S F hF recipe i j (next j)
        (P i j hij) (P j (next j) hjk) (hm i j hij) (hm j (next j) hjk) degree hd v hv
      have hP := rawPExpr_bound S hT F hF recipe j (next j) l
        (P j (next j) hjk) (P (next j) l hkl) (hm j (next j) hjk) (hm (next j) l hkl)
        pcross rawA hcap v hv (hA (next j) l hkl)
      exact rawDExpr_bound S hT F hF recipe i j (next j) l
        (P i j hij) (P j (next j) hjk) (P (next j) l hkl)
        (hm i j hij) (hm j (next j) hjk) (hm (next j) l hkl) degree pcross rawA hd v hv hM hP

end
end ThreeBoundMinmaxNumeric

#print axioms ThreeBoundMinmaxNumeric.rawTransfer_sound


