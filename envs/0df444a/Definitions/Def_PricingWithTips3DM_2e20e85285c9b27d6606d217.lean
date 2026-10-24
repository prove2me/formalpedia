-- Prove2me | Definitions.Def_PricingWithTips3DM_2e20e85285c9b27d6606d217
-- name    : PricingWithTips3DM_2e20e85285c9b27d6606d217
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:58:16.387956+00:00
-- url     : https://prove2.me/theorems/c791743a-af32-4852-ac8d-70b75ad6c912
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EdgeLookup.Canonical
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_e440e7fada8eb1675c80f075
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# General CLIQUE verifier: canonical edge-lookup semantics
-/

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeLookup

private theorem leftResult_prepend (queryLeft queryRight candidate remaining : Nat)
    (equal : Bool) (rest : List CliqueSym) :
    leftResult queryLeft queryRight remaining equal
        (prependCliqueTicks candidate (.pairSep :: rest)) =
      rightResult queryLeft queryRight queryRight
        (equal && decide (candidate = remaining)) rest := by
  induction candidate generalizing remaining equal with
  | zero =>
      cases remaining <;> simp [prependCliqueTicks, leftResult]
  | succ candidate ih =>
      cases remaining with
      | zero =>
          simp [prependCliqueTicks, leftResult, ih]
      | succ remaining =>
          simpa [prependCliqueTicks, leftResult] using
            ih remaining equal

private theorem rightResult_prepend
    (queryLeft queryRight candidate remaining : Nat)
    (equal : Bool) (rest : List CliqueSym) :
    rightResult queryLeft queryRight remaining equal
        (prependCliqueTicks candidate (.recordEnd :: rest)) =
      ((equal && decide (candidate = remaining)) ||
        edgesResult queryLeft queryRight rest) := by
  induction candidate generalizing remaining equal with
  | zero =>
      cases remaining <;> simp [prependCliqueTicks, rightResult]
  | succ candidate ih =>
      cases remaining with
      | zero =>
          simp [prependCliqueTicks, rightResult, ih]
      | succ remaining =>
          simpa [prependCliqueTicks, rightResult] using
            ih remaining equal

private theorem edgesResult_encodeCliqueEdge_append
    (query edge : Nat × Nat) (rest : List CliqueSym) :
    edgesResult query.1 query.2 (encodeCliqueEdge edge ++ rest) =
      (decide (query = edge) || edgesResult query.1 query.2 rest) := by
  rcases query with ⟨queryLeft, queryRight⟩
  rcases edge with ⟨left, right⟩
  simp only [encodeCliqueEdge, List.cons_append, edgesResult]
  rw [prependCliqueTicks_append]
  rw [List.cons_append, prependCliqueTicks_append]
  simp only [List.singleton_append]
  rw [leftResult_prepend]
  rw [rightResult_prepend]
  simp [eq_comm]

/-- Scanning canonical edge records is exactly pair membership. -/
theorem edgesResult_encode_edges (query : Nat × Nat)
    (edges : List (Nat × Nat)) :
    edgesResult query.1 query.2 (edges.flatMap encodeCliqueEdge) =
      decide (query ∈ edges) := by
  induction edges with
  | nil => simp [edgesResult]
  | cons edge edges ih =>
      rw [List.flatMap_cons, edgesResult_encodeCliqueEdge_append, ih]
      simp

/-- The reusable edge scan implements the typed adjacency lookup below the
diagonal. -/
theorem edgesResult_encode_eq_adjacencyBool_of_lt
    (I : CliqueInstance) {u v : Nat} (huv : u < v) :
    edgesResult u v (I.edges.flatMap encodeCliqueEdge) =
      adjacencyBool I u v := by
  have h := edgesResult_encode_edges (u, v) I.edges
  simp only at h
  rw [h]
  simp [adjacencyBool, huv]

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeLookup


