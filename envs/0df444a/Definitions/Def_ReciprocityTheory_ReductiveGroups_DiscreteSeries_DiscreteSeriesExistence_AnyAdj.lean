-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_AnyAdj
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_AnyAdj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:02:07.15424+00:00
-- url     : https://prove2.me/theorems/123e0ed8-a2cf-4356-a371-a2d942e8dc88
-- title:
--   Any Adj
-- statement:
--   Definitions and structural lemmas for Any Adj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/AnyAdj.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
def anyAdjWSum {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (l : List (ℂ × List (Fin n × Fin n))) : Module.End ℂ M :=
  (l.map fun c => c.1 • (c.2.map fun p => E p.1 p.2).prod).sum
theorem anyAdjWSum_append {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (l₁ l₂ : List (ℂ × List (Fin n × Fin n))) :
    anyAdjWSum E (l₁ ++ l₂) = anyAdjWSum E l₁ + anyAdjWSum E l₂ := by
  unfold anyAdjWSum
  rw [List.map_append, List.sum_append]
theorem anyAdjWSum_mul {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (l₁ l₂ : List (ℂ × List (Fin n × Fin n))) :
    anyAdjWSum E l₁ * anyAdjWSum E l₂ =
      anyAdjWSum E (l₁.flatMap fun c => l₂.map fun d => (c.1 * d.1, c.2 ++ d.2)) := by
  unfold anyAdjWSum
  induction l₁ with
  | nil => simp
  | cons c l ih =>
    rw [List.map_cons, List.sum_cons, add_mul, ih, List.flatMap_cons, List.map_append, List.sum_append]
    congr 1
    rw [← List.sum_map_mul_left, List.map_map]
    congr 1
    refine List.map_congr_left fun d _ => ?_
    simp only [Function.comp_apply, List.map_append, List.prod_append, smul_mul_smul_comm]
def anyAdjWordAlg {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) :
    Subalgebra ℂ (Module.End ℂ M) where
  carrier := {A | ∃ l, A = anyAdjWSum E l}
  mul_mem' := by
    rintro _ _ ⟨l₁, rfl⟩ ⟨l₂, rfl⟩
    exact ⟨_, anyAdjWSum_mul E l₁ l₂⟩
  add_mem' := by
    rintro _ _ ⟨l₁, rfl⟩ ⟨l₂, rfl⟩
    exact ⟨l₁ ++ l₂, (anyAdjWSum_append E l₁ l₂).symm⟩
  algebraMap_mem' r := ⟨[(r, [])], by simp [anyAdjWSum, Algebra.algebraMap_eq_smul_one]⟩
end ReciprocityTheory.ChartRestriction.DS


