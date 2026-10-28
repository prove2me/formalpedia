-- Prove2me | Definitions.Def_BS2_b3ba934b_ClosureHomogeneity
-- name    : BS2_b3ba934b_ClosureHomogeneity
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:25:39.648004+00:00
-- url     : https://prove2.me/theorems/ddf88bec-5501-4f46-8bf0-efdcf26daebc
-- title:
--   Sensitivity separation: ClosureHomogeneity (complete source module)
-- statement:
--   Complete Lean source module `ClosureHomogeneity` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/ClosureHomogeneity.lean; original SHA-256 435b0dc3e32b040d7866d760d5f5bde2dcece93d93d7793713473114a15991a5; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_FullProfileClosure
import Mathlib.Algebra.Order.Ring.Nat

set_option autoImplicit false

namespace ThreeBoundFullProfile
variable {n : ℕ}

def scale (c : ℕ) (v : Profile n) : Profile n := fun i => c * v i

theorem rule_value_scale (r : Rule n) (c : ℕ) (v : Profile n) :
    r.value (scale c v) = c * r.value v := by
  cases r <;> simp only [Rule.value, scale, Nat.mul_add, Nat.mul_max_mul_left]

theorem applyRule_scale (tighten : Bool) (c : ℕ) (v : Profile n) (r : Rule n) :
    applyRule tighten (scale c v) r = scale c (applyRule tighten v r) := by
  funext i
  by_cases hi : i = r.target
  · subst i
    cases tighten with
    | false =>
        simpa only [applyRule, if_pos rfl, Bool.false_eq_true, if_false, if_true, scale]
          using rule_value_scale r c v
    | true =>
        simp only [applyRule, if_pos rfl, scale]
        change min (c*v r.target) (r.value (scale c v)) =
          c*min (v r.target) (r.value v)
        rw [rule_value_scale,Nat.mul_min_mul_left]
  · simp [applyRule,hi,scale]

theorem runRules_scale (tighten : Bool) (rs : List (Rule n))
    (c : ℕ) (v : Profile n) :
    runRules tighten rs (scale c v) = scale c (runRules tighten rs v) := by
  induction rs generalizing v with
  | nil => rfl
  | cons r rs ih => simp only [runRules, applyRule_scale, ih]

theorem meet_scale (c : ℕ) (v w : Profile n) :
    meet (scale c v) (scale c w) = scale c (meet v w) := by
  funext i
  exact Nat.mul_min_mul_left c (v i) (w i)

theorem close_scale (c : ℕ) (v : Profile n) :
    close (scale c v) = scale c (close v) := by
  simp only [close, runRules_scale, meet_scale]

end ThreeBoundFullProfile

#print axioms ThreeBoundFullProfile.close_scale


