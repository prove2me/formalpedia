-- Prove2me | Definitions.Def_Conway99_Point_Gram_20261003
-- name    : Conway99_Point_Gram_20261003
-- status  : Definition
-- author  : @harry
-- created : 2026-10-03T18:35:20.265759+00:00
-- url     : https://prove2.me/theorems/3d9cddb1-ecd9-407a-b8f6-580bd5133689
-- title:
--   Graph-owned point Gram of a Conway graph
-- statement:
--   Let G be a finite simple graph on vertex set V and let A be its real adjacency matrix. Define Q(G)=27I-9A+J, where J is the all-ones matrix on V, and P(G)=Q(G)/63. Both matrices use the literal vertices and adjacency relation of G. The definitions make no assumption about whether such a strongly regular graph exists and introduce no free Gram or frame coordinates.
-- source:
--   Conway99/Conway99/Core.lean Point.Delta and Point.Eminus, SHA-256 1d5ecefb2efc22445bc7f494578876c5b25222ba4dda52ab10a5df38ec4feedb; clean-start proof-library.zip proofs/FOUNDATIONS.md §1, member SHA-256 32127d3ecb9cb533d4a019a1786ee17c84aedff5c8a121a42fc62253301d341c. This is a necessary-condition interface only; it neither constructs nor excludes an SRG(99,14,1,2).

import Mathlib

set_option autoImplicit false

namespace Conway99Formal.PointFrame

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The point Gram on the same graph's vertex coordinates. -/
def Q (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  27 • 1 - 9 • G.adjMatrix ℝ + of 1

/-- The normalized point Gram. -/
noncomputable def P (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  (63 : ℝ)⁻¹ • Q G

end Conway99Formal.PointFrame


