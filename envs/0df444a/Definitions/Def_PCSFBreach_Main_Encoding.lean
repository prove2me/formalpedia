-- Prove2me | Definitions.Def_PCSFBreach_Main_Encoding
-- name    : PCSFBreach_Main_Encoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:56:24.779069+00:00
-- url     : https://prove2.me/theorems/a30dcce6-f8e7-4551-b126-1ba524642a99
-- title:
--   Rational PCSF instances and their binary codes; codes of edge sets, moat lists and colorings
-- statement:
--   The algorithms of the paper work on rational data (Appendix B, p. 47). A **rational instance** $J$ has the shape of a PCSF instance with nonnegative rational costs and penalties; $J$ is read as a PCSF instance (real data) with the same vertices, edges and pairs.
--
--   Binary codes (strings over $\{0,1\}$):
--   1. a natural number $k$ is written by its binary digits, each digit $b$ as the two bits $1b$, followed by $0$ (self-delimiting, length $O(\log k)$);
--   2. a rational is a sign bit, then the codes of $|\mathrm{num}|$ and $\mathrm{den}$ of its reduced form;
--   3. an instance is the vertex count $n$ in **unary** ($n$ ones, then a zero: the input graph $G=(V,E)$ lists its vertices, so the input length is at least $|V|$), then the code of the number of edges, of each edge $(u,v,c)$, of the number of pairs and of each pair $(s,t,\pi)$;
--   4. an edge set $F$ is its characteristic vector over the edge list (one bit per edge), and a vertex set its characteristic vector over $V$;
--   5. a list of moats with duals $(U,y^n_U,y^e_U)$ and a list of coloring entries $(U,i,a_{Ui})$ are coded entry by entry after their length; a list of coloring entries describes the coloring that sums the listed values of each $(U,i)$ and is $0$ elsewhere.
--
--   Every "polynomial-time" statement of the mission is about a function on these codes that is `PolyTimeComputable`.
-- source:
--   Bosch-Calvo, Grandoni, Mátravölgyi, Breaching the 2-Approximation Barrier for Prize-Collecting Steiner Forest, STOC 2027 submission (manuscript sha256 05d9cc28…3eb3), p. 2, Theorem 1 (polynomial time); p. 47, Appendix B (rational input data)

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_PCSFBreach_Main_Instance
set_option autoImplicit false

open QAlgorithms.Complexity

namespace PCSFBreach.Main

/-- Self-delimiting binary code of a natural number: each binary digit `b` (least significant
first) is written as `true, b`, and the code ends with `false`. Length `2·⌈log₂(k+1)⌉ + 1`. -/
def encNat (k : ℕ) : Str := (Nat.bits k).flatMap (fun b => [true, b]) ++ [false]

/-- Binary code of a rational number: sign bit, then numerator magnitude and denominator
(reduced form), each by `encNat`. -/
def encRat (q : ℚ) : Str := [decide (q < 0)] ++ encNat q.num.natAbs ++ encNat q.den

/-- A PCSF instance with **rational** data, the input of the algorithms (Appendix B, p. 47: "assuming
rational input data"): same shape as `Instance`, nonnegative rational costs and penalties. -/
structure RatInstance where
  n : ℕ
  edges : List (Fin n × Fin n × ℚ)
  pairs : List (Fin n × Fin n × ℚ)
  edge_cost_nonneg : ∀ e ∈ edges, 0 ≤ e.2.2
  penalty_nonneg : ∀ p ∈ pairs, 0 ≤ p.2.2

/-- The PCSF instance (real data) described by a rational instance; edge and pair indices are
those of the rational lists. -/
def RatInstance.toInstance (J : RatInstance) : Instance where
  n := J.n
  edges := J.edges.map (fun e => (e.1, e.2.1, (e.2.2 : ℝ)))
  pairs := J.pairs.map (fun p => (p.1, p.2.1, (p.2.2 : ℝ)))
  edge_cost_nonneg := by
    intro e he
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
    exact Rat.cast_nonneg.mpr (J.edge_cost_nonneg q hq)
  penalty_nonneg := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact Rat.cast_nonneg.mpr (J.penalty_nonneg q hq)

/-- Unary code of a natural number: `k` ones followed by a zero. -/
def encUnary (k : ℕ) : Str := List.replicate k true ++ [false]

/-- Binary code of a rational PCSF instance (bit model, Appendix B p. 47): the vertex set
`V = Fin n` in unary (the input graph `G = (V, E)` lists its vertices, so the input length is at
least `|V|`), the number of edges, each edge as endpoint, endpoint, cost; then the number of
pairs, each pair as endpoint, endpoint, penalty. -/
def encInst (I : RatInstance) : Str :=
  encUnary I.n ++ encNat I.edges.length ++
    I.edges.flatMap (fun e => encNat e.1.val ++ encNat e.2.1.val ++ encRat e.2.2) ++
    encNat I.pairs.length ++
    I.pairs.flatMap (fun p => encNat p.1.val ++ encNat p.2.1.val ++ encRat p.2.2)

open scoped Classical in
/-- Code of an edge set `F ⊆ E`: its characteristic vector over the edge list (one bit per edge,
in edge-list order). -/
noncomputable def encEdgeSet (I : Instance) (F : Finset I.Edge) : Str :=
  List.ofFn (fun e : I.Edge => decide (e ∈ F))

open scoped Classical in
/-- Code of a vertex set `U ⊆ V`: its characteristic vector over `Fin n`. -/
noncomputable def encVertexSet (I : Instance) (U : Finset (Fin I.n)) : Str :=
  List.ofFn (fun v : Fin I.n => decide (v ∈ U))

/-- Code of a list of moats with their normal and extension duals `(U, yⁿ_U, yᵉ_U)`. -/
noncomputable def encMoatList (I : Instance) (L : List (Finset (Fin I.n) × ℚ × ℚ)) : Str :=
  encNat L.length ++ L.flatMap (fun x => encVertexSet I x.1 ++ encRat x.2.1 ++ encRat x.2.2)

/-- Code of a list of coloring entries `(U, i, a_{Ui})`. -/
noncomputable def encColoring (I : Instance) (L : List (Finset (Fin I.n) × I.Pair × ℚ)) : Str :=
  encNat L.length ++ L.flatMap (fun x => encVertexSet I x.1 ++ encNat x.2.1.val ++ encRat x.2.2)

/-- The coloring `a` described by a list of entries `(U, i, a_{Ui})` (entries for the same `(U, i)`
add up; unlisted entries are `0`). -/
def coloringOf (I : Instance) (L : List (Finset (Fin I.n) × I.Pair × ℚ))
    (U : Finset (Fin I.n)) (i : I.Pair) : ℝ :=
  ((L.filter (fun x => decide (x.1 = U ∧ x.2.1 = i))).map (fun x => (x.2.2 : ℝ))).sum

end PCSFBreach.Main


