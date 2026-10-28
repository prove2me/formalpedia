-- Prove2me | Definitions.Def_BS2_b3ba934b_ResidualSelection
-- name    : BS2_b3ba934b_ResidualSelection
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:26:34.319436+00:00
-- url     : https://prove2.me/theorems/eebd97c6-0336-40a2-a03d-450c8a65d6db
-- title:
--   Sensitivity separation: ResidualSelection (complete source module)
-- statement:
--   Complete Lean source module `ResidualSelection` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/ResidualSelection.lean; original SHA-256 f65e1612250326c963a4922501a36374d3cfb59dbbee06538b1fa920d0c9b915; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- The sorted residual prefixes in the case records are sums over actual
distinct marker subsets, not merely optimistic numerical minima. -/
import Definitions.Def_BS2_b3ba934b_GlobalAccounting
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Nodup

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundMarkers
open scoped Classical BigOperators
noncomputable section
variable {V : Type} [DecidableEq V]

theorem exists_markers_of_sorted_prefix (vs : List V) (hvs : vs.Nodup)
    (res : V → ℕ) (k : ℕ) (hk : k ≤ vs.length) :
    ∃ M : Finset V, M ⊆ vs.toFinset ∧ M.card = k ∧
      (∑ v ∈ M, res v) = (((vs.map res).mergeSort (· ≤ ·)).take k).sum := by
  let sorted := vs.mergeSort (fun a b => decide (res a ≤ res b))
  have hp : sorted.Perm vs := List.mergeSort_perm _ _
  have hnd : sorted.Nodup := hp.nodup_iff.mpr hvs
  have htake : (sorted.take k).Nodup := hnd.take
  have hm : sorted.map res = (vs.map res).mergeSort (· ≤ ·) :=
    List.map_mergeSort (fun _ _ _ _ => rfl)
  refine ⟨(sorted.take k).toFinset, ?_, ?_, ?_⟩
  · intro v hv
    exact List.mem_toFinset.mpr (hp.mem_iff.mp
      (List.mem_of_mem_take (List.mem_toFinset.mp hv)))
  · rw [List.toFinset_card_of_nodup htake,List.length_take,hp.length_eq]
    exact min_eq_left hk
  · rw [List.sum_toFinset res htake,List.map_take,hm]

theorem exists_markers_finset (H : Finset V) (res : V → ℕ)
    (k : ℕ) (hk : k ≤ H.card) :
    ∃ M : Finset V, M ⊆ H ∧ M.card = k ∧
      (∑ v ∈ M, res v) = (((H.toList.map res).mergeSort (· ≤ ·)).take k).sum := by
  have hh := exists_markers_of_sorted_prefix H.toList H.nodup_toList res k
    (by simpa using hk)
  simpa using hh

/-- Any cap valid for every chosen k-marker set is valid for the exact
    residual prefix stored in the complete tournament record. -/
theorem bound_by_sorted_prefix (vs : List V) (hvs : vs.Nodup)
    (res : V → ℕ) (k a c : ℕ) (hk : k ≤ vs.length)
    (hcap : ∀ M : Finset V, M ⊆ vs.toFinset → M.card = k →
      a ≤ c+∑ v ∈ M, res v) :
    a ≤ c+(((vs.map res).mergeSort (· ≤ ·)).take k).sum := by
  obtain ⟨M,hM,hcard,hsum⟩ := exists_markers_of_sorted_prefix vs hvs res k hk
  simpa only [hsum] using hcap M hM hcard

end
end ThreeBoundMarkers

#print axioms ThreeBoundMarkers.exists_markers_of_sorted_prefix
#print axioms ThreeBoundMarkers.bound_by_sorted_prefix


