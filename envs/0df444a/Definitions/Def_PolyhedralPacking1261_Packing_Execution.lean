-- Prove2me | Definitions.Def_PolyhedralPacking1261_Packing_Execution
-- name    : PolyhedralPacking1261_Packing_Execution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:36:37.798343+00:00
-- url     : https://prove2.me/theorems/031c38b5-8cdd-45a4-88bd-e3d8b9cc6aef
-- title:
--   Vertex input layout, full input size, scalar output decoding and its cost
-- statement:
--   The scalar input consists of the number n of pieces, then for each piece its vertex count and all real coordinate triples. Input size is the length of this scalar encoding, including piece records; it is not just n. Indices are zero-based and multiplicities are retained. There is no epsilon input. Output memory cells 0 through 2 contain the lower box corner, 3 through 5 the upper box corner, and cells 6+3i through 8+3i contain the translation of piece i.
--   PackingExecution asserts a genuine first-halting execution of the finite scalar code on exactly that input and decodes the actual final memory. Its time is the number of executed instructions plus 6+3n scalar reads to materialize the output. Every input access is charged by an input instruction; every algorithmic loop and every subroutine is implemented by the same fixed primitive instructions. The given input is already in its declared vertex layout. PackingExecution imposes no feasibility, approximation or polynomial bound: all are separate conclusions of the goal.
-- source:
--   Simon Bartlmae, Anders Aamand, Mikkel Abrahamsen, Polylogarithmic Approximation for Packing Convex Polyhedra, STOC 2027 submission #1261 (October 2026), canonical PDF SHA-256 b915da2d5fece730ea9946885b05ad09e10e575374e6a1df96e8a6149cb0e67e, Theorem 1 and its following clarification, PDF p.2 = printed p.1; fixed input/output encoding

import Definitions.Def_PolyhedralPacking1261_Packing_Geometry
import Definitions.Def_PolyhedralPacking1261_Packing_Machine

set_option autoImplicit false

namespace PolyhedralPacking1261.Packing

def pointWords (p : Point3) : List ℝ := [p 0, p 1, p 2]

def pieceWords (vertices : List Point3) : List ℝ :=
  (vertices.length : ℝ) :: vertices.flatMap pointWords

/-- The input is n followed by each vertex count and its real coordinate triples.
All multiplicities and all piece boundaries are retained. There is no epsilon input. -/
def packingWords (K : PackingInput) : List ℝ :=
  (K.length : ℝ) :: K.flatMap pieceWords

def packingInputSize (K : PackingInput) : ℕ := (packingWords K).length

/-- Cells 0..2 and 3..5 are the lower and upper box corners. Cells 6+3i..8+3i
are the translation of piece i. This is a fixed decoding of scalar output data. -/
def decodePacking (n : ℕ) (state : ScalarState) : PackingOutput n where
  lower r := state.memory r.val
  upper r := state.memory (3 + r.val)
  translation i r := state.memory (6 + 3 * i.val + r.val)

/-- Actual execution on the vertex data, plus one scalar read per output entry.
Input access, all loops, and every subroutine must be executed in the scalar code.
The input is already given in the declared layout; size is its full scalar length. -/
def PackingExecution (program : ScalarProgram) (K : PackingInput)
    (time : ℕ) (out : PackingOutput K.length) : Prop :=
  ∃ scalarTime finalState,
    ScalarExecution program (packingWords K) scalarTime finalState ∧
    out = decodePacking K.length finalState ∧
    time = scalarTime + (6 + 3 * K.length)

end PolyhedralPacking1261.Packing


