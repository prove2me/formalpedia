-- Prove2me | Definitions.Def_ImprovedSteinerForest_Main_Encoding
-- name    : ImprovedSteinerForest_Main_Encoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:27:23.225726+00:00
-- url     : https://prove2.me/theorems/b57766b6-ca84-4ff0-84ac-074874a2b6b5
-- title:
--   Binary codes of instances, edge sets and lists of vertex sets
-- statement:
--   The bit model of p. 13: "The graph and demand list are given explicitly, and rational costs are encoded in binary."
--
--   - The **code of an instance** writes the number of vertices $n$ in unary (the explicit graph lists its vertices), then the number of edges and, for each edge in order, its two endpoints and its cost, then the number of demands and, for each demand in order, its two endpoints. Natural numbers use the self-delimiting binary code `encBin` and rationals the binary code `encRat` (numerator with sign, then denominator) of the published definitions `QAlgorithms_ClassicalBinaryEncoding` and `QAlgorithms_ClassicalRationalEncoding`.
--   - The **code of an edge set** $F$ is its characteristic vector over the edge list, one bit per edge in list order; the code of a vertex set is its characteristic vector over $V$; a list of vertex sets is coded by its length followed by the codes of its members.
--
--   These codes are the inputs and outputs of the polynomial-time statements: a function $M$ on binary strings is polynomial-time computable when the published `PolyTimeComputable` holds (a deterministic multi-stack Turing machine halting within a polynomial in the input length).
--
--   **Formalization Note.** The input length is at least $n$ and at least the total number of bits of the costs, so "polynomial in the input length" is the paper's polynomial running time in bit operations.
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Improved Steiner Forest Approximation via Cut Spaces, STOC 2027 submission (manuscript sha256 b2bf022d…0444), p. 13, §2.1

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding
import Definitions.Def_ImprovedSteinerForest_Main_Instance
set_option autoImplicit false

open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian

namespace ImprovedSteinerForest.Main

/-- Unary code of a natural number: `k` ones followed by a zero. -/
def encUnary (k : ℕ) : Str := List.replicate k true ++ [false]

/-- Binary code of an instance (bit model, p. 13: "The graph and demand list are given explicitly,
and rational costs are encoded in binary"): the vertex set `Fin n` in unary (the explicit graph lists
its vertices), the number of edges, each edge as endpoint, endpoint, cost (rational in binary); then
the number of demands, each demand as its two endpoints. Indices and counts use self-delimiting
binary `encBin`, rationals `encRat`. -/
def encInst (I : Instance) : Str :=
  encUnary I.n ++ encBin I.edges.length ++
    I.edges.flatMap (fun e => encBin e.1.val ++ encBin e.2.1.val ++ encRat e.2.2) ++
    encBin I.pairs.length ++
    I.pairs.flatMap (fun p => encBin p.1.val ++ encBin p.2.val)

open scoped Classical in
/-- Code of an edge set `F ⊆ E_G`: its characteristic vector over the edge list (one bit per edge,
in edge-list order). -/
noncomputable def encEdgeSet (I : Instance) (F : Finset I.Edge) : Str :=
  List.ofFn (fun f : I.Edge => decide (f ∈ F))

open scoped Classical in
/-- Code of a vertex set `U ⊆ V`: its characteristic vector over `Fin n`. -/
noncomputable def encVertexSet (I : Instance) (U : Finset (Fin I.n)) : Str :=
  List.ofFn (fun v : Fin I.n => decide (v ∈ U))

/-- Code of a finite list of vertex sets: its length, then each set by `encVertexSet`. -/
noncomputable def encVertexSets (I : Instance) (L : List (Finset (Fin I.n))) : Str :=
  encBin L.length ++ L.flatMap (encVertexSet I)

end ImprovedSteinerForest.Main


