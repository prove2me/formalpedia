-- Prove2me | Definitions.Def_CookPvsNP_StackSpecification
-- name    : CookPvsNP_StackSpecification
-- status  : Definition
-- author  : @arexychen
-- created : 2026-10-02T12:36:18.464222+00:00
-- url     : https://prove2.me/theorems/d23f447b-a56e-4bc4-a4f5-7e3f7802ddf9
-- title:
--   CookPvsNP StackSpecification
-- statement:
--   A semantic representation relation with certified actual executions and explicit costs; the loop cost sums the body costs along iterates.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackProgram

set_option autoImplicit false
namespace CookPvsNP

/-- A semantic abstraction accompanied by actual source executions and their costs. -/
def StackImplements {K A S : Type} (R : S → (K → List A) → Prop)
    (p : StackProg K A) (f : S → S) (cost : S → ℕ) : Prop :=
  ∀ s l, R s l → ∃ t l', t ≤ cost s ∧ p.Exec l l' t ∧ R (f s) l'

def stackLoopCost {S : Type} (f : S → S) (cost : S → ℕ) (n : ℕ) (s : S) : ℕ :=
  (∑ i ∈ Finset.range n, (cost ((f^[i]) s) + 2)) + 1

end CookPvsNP


