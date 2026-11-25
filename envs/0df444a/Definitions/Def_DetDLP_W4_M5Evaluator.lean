-- Prove2me | Definitions.Def_DetDLP_W4_M5Evaluator
-- name    : DetDLP_W4_M5Evaluator
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:37:07.404552+00:00
-- url     : https://prove2.me/theorems/b55dca55-42af-4b15-9503-50fb58da2a88
-- title:
--   Polynomial-time evaluator for the two-layer multiplication gadget
-- statement:
--   For a dimension written in unary, the bit-valued local tensor evaluator runs in polynomial time. The proof obtains this bound from its natural-number dispatcher on a unary-padded dimension and the equality of that dispatcher with the finite-graph tensor predicate.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Lemma 2.3 (pp. 8–9)

import Definitions.Def_DetDLP_W4_M5GateEq
set_option autoImplicit false
namespace DetDLP.w4_M5Evaluator
open Groundwork Groundwork.PolyT w4_M5GraphBounds w4_M5GateOps w4_M5Dispatch w4_M5PortTensor

private theorem padded_eq (q : Pad) (v : ℕ) (a : List Bool) :
    evalNat q v a = evalAt q.length v a := by
  by_cases hd : 1 ≤ q.length
  · by_cases hv : v < vertexCount q.length
    · let i : Fin (vertexCount q.length) := ⟨v,hv⟩
      let u := (vertexIndex q.length).symm i
      have hi : vertexIndex q.length u = i := (vertexIndex q.length).apply_symm_apply i
      have he := evalNat_at q hd u a
      rw [hi] at he
      exact he.trans (by simpa only [evalAt,dif_pos hd,dif_pos hv,tensor] using w4_M5GateEq.gate_eq q hd i a u)
    · simp [evalNat,evalAt,hd,hv]
  · simp [evalNat,evalAt,hd]

theorem f_poly : PolyT f := by
  apply f_poly_of_evalAt
  intro α hEnc d v a hu _ hv ha
  have hp := evalNat_poly (q := fun x => List.replicate (d x) ()) hu hv ha
  apply hp.congr
  intro x
  simpa only [List.length_replicate] using padded_eq (List.replicate (d x) ()) (v x) (a x)

end DetDLP.w4_M5Evaluator


