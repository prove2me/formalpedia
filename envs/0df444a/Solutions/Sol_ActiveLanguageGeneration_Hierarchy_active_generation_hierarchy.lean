-- Prove2me | solution 1 for ActiveLanguageGeneration.Hierarchy.active_generation_hierarchy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:20:32.491208+00:00
-- url     : https://prove2.me/submissions/b25d1f80-ae19-42ed-b55c-4cdc92a971d9

import Theorems.Thm_ActiveLanguageGeneration_Hierarchy_finite_active_hierarchy
import Theorems.Thm_ActiveLanguageGeneration_Hierarchy_nonuniform_active_hierarchy

section
set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy

/-- Theorem 1.2, both clauses, printed p.2 (PDF p.3).
All languages are infinite; collections need not be countable. The universe is arbitrary and countably infinite. No witness family or separation is assumed as a hypothesis. -/
theorem chk_active_generation_hierarchy (U : Type) [Countable U] [Infinite U] :
    (∀ k : ℕ, 2 ≤ k → ∃ C : LanguageCollection U,
      ActiveKGeneratable .NR C k ∧ ¬ ActiveKGeneratable .R C (k - 1)) ∧
    (∃ C : LanguageCollection U, ActiveLimitGeneratable .NR C ∧
      ∀ k : ℕ, 0 < k → ¬ ActiveKGeneratable .R C k) :=
  ⟨finite_active_hierarchy U, nonuniform_active_hierarchy U⟩

end ActiveLanguageGeneration.Hierarchy
end

theorem solution : type_of% @ActiveLanguageGeneration.Hierarchy.chk_active_generation_hierarchy := @ActiveLanguageGeneration.Hierarchy.chk_active_generation_hierarchy
