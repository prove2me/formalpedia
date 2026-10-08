-- Prove2me | Definitions.Def_QaAlgebra_BinaryCode
-- name    : QaAlgebra_BinaryCode
-- status  : Definition
-- author  : @harry
-- created : 2026-10-04T04:41:29.159595+00:00
-- url     : https://prove2.me/theorems/2b937a67-b4c1-4660-961e-0d9fc828f29e
-- title:
--   Binary graph words and Hamming weight
-- statement:
--   For a supplied graph, adjacency is its literal matrix over Z/2Z. For any binary-valued vertex function u, support is the set where u is nonzero and weight is the cardinality of that support.
-- source:
--   Exact original Lean source: formalization/2026-10-03/binary-code/BinaryCode.lean#L20-21, 23-24, 26-27; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 1437e9cd690e050f604a603b7826fef50f4ef1f6c0d21ef32c66c9793cb943e4. Canonical generated Definition: Definitions/Def_QaAlgebra_BinaryCode.lean; generated SHA-256 2d2c4387f63c036f326a128dd94457fd2495c6b867ef1b0f13711530184666b7; Lab Git revision 2b268c701ba7d258d871c91b80aa6724708d5063, path fixtures/generated-project-definitions/Definitions/Def_QaAlgebra_BinaryCode.lean.

import Mathlib

set_option autoImplicit false

/-!
Binary adjacency-code identities for an actual SRG(99,14,1,2).
Sources: Conway99/Conway99/Claims/C01srgcorealgebra.lean §4;
Conway99/Conway99/Claims/C04finitefieldranks.lean §1;
Conway99/results/R003_enriched_binary_code_odd_cross_rank.md §1;
Conway99/results/R017_binary_genus2_smith_weight60.md §1.
-/

namespace Conway99Formal.BinaryCode

open Matrix SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The literal binary adjacency matrix of the graph. -/
def adjacency : Matrix V V (ZMod 2) := G.adjMatrix (ZMod 2)

/-- Literal support of a binary word. -/
def support (u : V → ZMod 2) : Finset V := univ.filter fun v => u v ≠ 0

/-- Hamming weight of a binary word. -/
def weight (u : V → ZMod 2) : ℕ := (support u).card














































end Conway99Formal.BinaryCode


