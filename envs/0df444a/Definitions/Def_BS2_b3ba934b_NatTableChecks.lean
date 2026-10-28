-- Prove2me | Definitions.Def_BS2_b3ba934b_NatTableChecks
-- name    : BS2_b3ba934b_NatTableChecks
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T05:45:39.187564+00:00
-- url     : https://prove2.me/theorems/e9e1253c-022e-4aee-998b-8487f040cd39
-- title:
--   Sensitivity separation: NatTableChecks (complete source module)
-- statement:
--   Complete Lean source module `NatTableChecks` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/NatTableChecks.lean; original SHA-256 1697051482b0f8234dc028eba3f66c46520034c6c4f61c9091cebfe9a7e6dfeb; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Small structural checks for globally ordered piecewise constant tables. -/
import Definitions.Def_BS2_b3ba934b_FlatProfiles

set_option autoImplicit false

namespace ThreeBoundNumeric.NatTable

theorem bool_and_true (a b : Bool) : ((a && b)=true) ↔ (a=true ∧ b=true) := by
  cases a <;> cases b <;> decide

def lowerCheck (bound : ℕ) : NatTable → Bool
  | .leaf v => bound≤v
  | .branch _ left right => lowerCheck bound left && lowerCheck bound right

theorem lowerCheck_sound (bound : ℕ) (table : NatTable)
    (h : lowerCheck bound table=true) : ∀ i, bound≤table.get i := by
  induction table with
  | leaf v =>
      intro i
      exact of_decide_eq_true h
  | branch cut left right hl hr =>
      have hh : lowerCheck bound left=true ∧ lowerCheck bound right=true := (bool_and_true _ _).mp h
      intro i
      simp only [NatTable.get]
      split_ifs
      · exact hl hh.1 i
      · exact hr hh.2 i

/-- The two trees use the same cuts whenever both nodes branch. A leaf may
represent an arbitrarily large constant interval. No interval endpoints need
to be supplied or trusted. -/
def dominates (factor : ℕ) : NatTable → NatTable → Bool
  | .leaf a, .leaf b => a≤factor*b
  | .leaf a, .branch _ left right =>
      dominates factor (.leaf a) left && dominates factor (.leaf a) right
  | .branch _ left right, .leaf b =>
      dominates factor left (.leaf b) && dominates factor right (.leaf b)
  | .branch ca la ra, .branch cb lb rb =>
      ca==cb && dominates factor la lb && dominates factor ra rb
termination_by a b => sizeOf a+sizeOf b

theorem dominates_sound (factor : ℕ) (a b : NatTable)
    (h : dominates factor a b=true) : ∀ i, a.get i≤factor*b.get i := by
  induction a generalizing b with
  | leaf av =>
      induction b with
      | leaf bv =>
          rw [dominates] at h
          exact fun _=>of_decide_eq_true h
      | branch cb lb rb hl hr =>
          rw [dominates] at h
          have hh : dominates factor (.leaf av) lb=true ∧ dominates factor (.leaf av) rb=true :=
            (bool_and_true _ _).mp h
          intro i
          simp only [NatTable.get]
          split_ifs
          · exact hl hh.1 i
          · exact hr hh.2 i
  | branch ca la ra hl hr =>
      cases b with
      | leaf bv =>
          rw [dominates] at h
          have hh : dominates factor la (.leaf bv)=true ∧ dominates factor ra (.leaf bv)=true :=
            (bool_and_true _ _).mp h
          intro i
          simp only [NatTable.get]
          split_ifs
          · exact hl _ hh.1 i
          · exact hr _ hh.2 i
      | branch cb lb rb =>
          rw [dominates] at h
          have hh : (ca==cb && dominates factor la lb)=true ∧ dominates factor ra rb=true :=
            (bool_and_true _ _).mp h
          have hleft := (bool_and_true _ _).mp hh.1
          have heq : ca=cb := by simpa using hleft.1
          subst cb
          intro i
          simp only [NatTable.get]
          split_ifs
          · exact hl _ hleft.2 i
          · exact hr _ hh.2 i

end ThreeBoundNumeric.NatTable

#print axioms ThreeBoundNumeric.NatTable.dominates_sound


