-- Prove2me | Definitions.Def_ResourceScheduling_Graph_WordProgram
-- name    : ResourceScheduling_Graph_WordProgram
-- status  : Definition
-- author  : @arexychen
-- created : 2026-10-02T12:12:43.229593+00:00
-- url     : https://prove2.me/theorems/ee5e833a-4ede-4b7d-a873-b7c7992d6dbf
-- title:
--   ResourceScheduling Graph WordProgram
-- statement:
--   Natural-index graph validation, lexicographically ordered non-edges, exact unary scheduling emission, and a total word reduction program.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_WordReduction

set_option autoImplicit false
namespace ResourceScheduling.Graph

/-- Bounded Boolean validation using natural row and column indices. -/
def checkGraphBody (n : ℕ) (bits : List Letter) : Bool :=
  decide (bits.length = n * n) && (List.range n).all fun i =>
    decide (bits.getD (i * n + i) Letter.sep ≠ Letter.one) &&
      (List.range n).all fun j => decide
        (bits.getD (i * n + j) Letter.sep = Letter.one →
          bits.getD (j * n + i) Letter.sep = Letter.one)

/-- Ordered natural-index pairs for the resources, with no dependent graph object. -/
def wordNonEdges (n : ℕ) (bits : List Letter) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun i =>
    ((List.range n).filter fun j => decide
      (i < j ∧ bits.getD (i * n + j) Letter.sep ≠ Letter.one)).map fun j => (i, j)

/-- Emit the exact original unary Q2 code from the natural-index resource list. -/
def emitQ2Word (t : ℕ) (bits : List Letter) : List Letter :=
  let n := 3 * t
  let pairs := wordNonEdges n bits
  unary 2 ++ unary 1 ++ unary n ++ unary pairs.length ++
    pairs.flatMap (fun p => (List.range n).flatMap fun i =>
      unary (if i = p.1 ∨ i = p.2 then 1 else 0)) ++ unary t

/-- A total list program for the reduction. This definition asserts no machine-time bound. -/
def wordProgram (w : List Letter) : List Letter :=
  match readUnary w with
  | none => []
  | some (t, bits) => if checkGraphBody (3 * t) bits then emitQ2Word t bits else []

end ResourceScheduling.Graph


