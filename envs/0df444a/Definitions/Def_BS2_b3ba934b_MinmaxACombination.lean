-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxACombination
-- name    : BS2_b3ba934b_MinmaxACombination
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:43:31.687223+00:00
-- url     : https://prove2.me/theorems/086ba98c-926a-480c-b202-7b1a64ea0ddf
-- title:
--   Sensitivity separation: MinmaxACombination (complete source module)
-- statement:
--   Complete Lean source module `MinmaxACombination` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxACombination.lean; original SHA-256 e8e4fa70b01e5929071cfb2d10248d25e316567f60a4dc5625ec0c43959fb1d0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Ordinary component minima in the exact min/max upward expression. -/
import Definitions.Def_BS2_b3ba934b_MinmaxOrdinaryA
import Definitions.Def_BS2_b3ba934b_MinmaxAExpressions

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000

namespace ThreeBoundMinmaxA
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional ThreeBoundMinmaxTransfer ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric (Entry EntryMatch)
open scoped Classical
noncomputable section
variable {n : ℕ} {I : Type} [Fintype I]

theorem le_foldl_min (z first : ℕ) (xs : List ℕ) (hf : z ≤ first)
    (hxs : ∀ x ∈ xs, z ≤ x) : z ≤ xs.foldl Nat.min first := by
  induction xs generalizing first with
  | nil => exact hf
  | cons x xs ih =>
      apply ih (min first x) (le_min hf (hxs x (by simp)))
      intro y hy
      exact hxs y (by simp [hy])

theorem rawAExpr_small_bound (S : Stage (Fin n) I (Fin 10007))
    (hAdj : S.Adj=ThreeBoundOrdinarySelected.Adj) (hLabel : S.label=Sensitivity10007BoolCaps.label)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F) (recipe : Fin n → ThreeBoundMinmaxNumeric.Entry)
    (i j : Fin n) (P : ThreeBoundMinmaxTransfer.PairData S F i j)
    (hm : EntryMatch S F i j P (recipe i) (recipe j))
    (records : List (List ℕ))
    (hnotplain : ¬((recipe i).plain && (recipe j).plain)=true)
    (hpos : 0<(recipe j).tolerance) (hq8 : (recipe j).tolerance ≤ 8)
    (v : Profile n) (hv : Upper F v)
    (hfirst : ABound (parent S F) i j
      ((gradedAExpr n ThreeBoundConditionalNumeric.ordinaryCaps10007 records (recipe i) (recipe j)).eval v)) :
    ABound (parent S F) i j
      ((rawAExpr n ThreeBoundConditionalNumeric.ordinaryCaps10007 records (recipe i) (recipe j)).eval v) := by
  intro x hx
  simp only [rawAExpr,if_neg hnotplain,if_neg (by omega : (recipe j).tolerance≠0)]
  by_cases hc : (recipe j).ordinary=true
  · rw [if_pos hc,Expr.eval_minimum]
    apply le_foldl_min _ _ _ (hfirst x hx)
    intro value hvalue
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hvalue
    obtain ⟨level,hlevel,hbody⟩ := List.mem_filterMap.mp he
    have hrange := mem_interval.mp hlevel
    split_ifs at hbody with ht
    · have heq := Option.some.inj hbody
      subst e
      exact ThreeBoundMinmaxNumeric.ordinaryComponentAExpr_bound S hAdj hLabel F hF recipe i j P hm
        level (by omega) hrange.1 hq8 ht hc v hv x hx
  · rw [if_neg hc]
    exact hfirst x hx

end
end ThreeBoundMinmaxA

#print axioms ThreeBoundMinmaxA.rawAExpr_small_bound


