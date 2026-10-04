-- Prove2me | Definitions.Def_ResourceScheduling_Graph_RAMBudget
-- name    : ResourceScheduling_Graph_RAMBudget
-- status  : Definition
-- author  : @arexychen
-- created : 2026-10-02T15:22:43.466441+00:00
-- url     : https://prove2.me/theorems/776ede47-f2f9-4bd3-b3de-06081656f0d9
-- title:
--   ResourceScheduling Graph RAMBudget
-- statement:
--   Numeric pre-state bounds for every executed primitive, with a structural weight and polynomial degree.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_RAMCode

set_option autoImplicit false
namespace ResourceScheduling.Graph

def RAMBound {V : Type} (B : ℕ) (s : RAMState V) : Prop :=
  (∀ v, s.val v ≤ B) ∧ s.word.length ≤ B

namespace RAMCode

/-- Only numeric registers and the read-only word affect primitive execution costs. -/
def Bounded {V : Type} [DecidableEq V] : RAMCode V → ℕ → RAMState V → Prop
  | .seq p q, B, s => p.Bounded B s ∧ q.Bounded B (p.eval s)
  | .branch _ p q, B, s => p.Bounded B s ∧ q.Bounded B s
  | .loop v p, B, s => RAMBound B s ∧ ∀ i < s.val v,
      let si := ((fun s => p.eval (s.set v (s.val v - 1)))^[i]) s
      p.Bounded B (si.set v (si.val v - 1))
  | _, B, s => RAMBound B s

def weight {V : Type} : RAMCode V → ℕ
  | .seq p q | .branch _ p q => p.weight + q.weight + 1
  | .loop _ p => p.weight + 5
  | _ => 50

def degree {V : Type} : RAMCode V → ℕ
  | .seq p q | .branch _ p q => max p.degree q.degree
  | .loop _ p => p.degree + 1
  | _ => 2

end RAMCode
end ResourceScheduling.Graph


