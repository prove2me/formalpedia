-- Prove2me | Definitions.Def_GirthFiltering_RandomFiltering_ThresholdProgram
-- name    : GirthFiltering_RandomFiltering_ThresholdProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:54.393306+00:00
-- url     : https://prove2.me/theorems/fde28f60-bd7d-4274-bcc9-692d5ae03bb0
-- title:
--   Operational preprocessing and tie-aware threshold computation
-- statement:
--   Active edges retain their original identity, both current endpoints, their weight, and their sampled real label. The program constructs adjacency lists with two incidences per edge and scans only endpoints of active edges. A depth-first stack traversal computes components and the number of visited vertices. The cycle test compares the actual edge count to vertices minus components; its equivalence to cycle existence remains a proof obligation. Contraction maps endpoints to component representatives and retains every surviving edge, including loops and parallel edges.
--
--   Preprocessing first returns $+\infty$ on a forest. On a cyclic input, a zero-edge cycle returns zero; otherwise the zero-edge components are contracted and all zero edges are removed. The remaining number of incident vertices and positive-edge list are computed by scans. All of these operations accrue charges.
--
--   The threshold computation uses the upper median $M$ and three parts. It recurses on labels strictly above $M$ if that part is cyclic; it returns $M$ if the strict part is acyclic but the part at least $M$ is cyclic; otherwise it contracts the latter forest and recurses on the strict lower part. The target equivalence is
--
--   $$
--   \operatorname{FindThreshold}(G,X)=\max_{C\text{ a cycle}}\min_{e\in C}X_e,
--   $$
--
--   with $-\infty$ for a forest. Empty and singleton cases are explicit. The algorithm has no cycle enumeration or exceptional expensive fallback. The three-way extension avoids the printed two-way recursion's failure to shrink on equal labels. Equivalence and deterministic linear cost on every label tape are proved in the goal, not stored as assumptions.
--
--   **Formalization Note** Fuel exhaustion is explicitly totalized; the goal must prove the chosen budgets suffice. Every sample reads the original edge's independent exponential coordinate and charges that ideal draw. Components are identified by existing vertex addresses, avoiding repeated scans of original isolated or already-contracted vertices.
-- source:
--   Yablon, Approximating the Girth of an Undirected, Weighted Graph for Larger Approximation Factors, STOC 2027 submission #59 (2026), pinned PDF sha256 cf63df259cbd099089184755e2c32f0d51f00dea322509f35766f4a91a4e021f, p. 3, Section 1.2 preprocessing; pp. 4–5, Algorithm 2 and its linear-work display; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/59.pdf

import Definitions.Def_GirthFiltering_RandomFiltering_CycleModel
import Definitions.Def_GirthFiltering_RandomFiltering_ChargedPrimitives

namespace GirthFiltering.RandomFiltering

/-- Original IDs persist through deletion and contraction. Vertex IDs are RAM addresses. -/
structure ActiveEdge where
  original : ℕ
  u : ℕ
  v : ℕ
  weight : ℝ
  label : ℝ

def edgeList (G : WeightedGraph) (X : Fin G.q → ℝ) : List ActiveEdge :=
  List.ofFn (fun e : Fin G.q =>
    ⟨e.val, (G.tail e).val, (G.head e).val, G.weight e, X e⟩)

/-- Initial input scan, including allocation of each edge record. -/
def loadEdges (G : WeightedGraph) : Charged (List ActiveEdge) :=
  cOfFn (fun e : Fin G.q => do
    tick
    return ⟨e.val, (G.tail e).val, (G.head e).val, G.weight e, 0⟩)

def pushAll : List ℕ → List ℕ → Charged (List ℕ)
  | [], stack => do tick; return stack
  | v :: vs, stack => do tick; pushAll vs (v :: stack)

/-- Build both incidences, including two incidences for a loop.
The roots list has two entries per edge and need not be deduplicated. -/
def buildAdj : List ActiveEdge → (ℕ → List ℕ) → List ℕ →
    Charged ((ℕ → List ℕ) × List ℕ)
  | [], adj, roots => do tick; return (adj, roots)
  | e :: es, adj, roots => do
    tick
    let adj := Function.update adj e.u (e.v :: adj e.u)
    let adj := Function.update adj e.v (e.u :: adj e.v)
    buildAdj es adj (e.u :: e.v :: roots)

/-- Iterative DFS stack semantics. A positive mark is one plus the root address. -/
def flood : ℕ → (ℕ → List ℕ) → ℕ → List ℕ → (ℕ → ℕ) →
    Charged ((ℕ → ℕ) × ℕ)
  | 0, _, _, _, mark => do tick; return (mark, 0)
  | fuel + 1, adj, root, stack, mark => do
    tick
    match stack with
    | [] => return (mark, 0)
    | v :: rest =>
      if mark v ≠ 0 then flood fuel adj root rest mark
      else
        let mark := Function.update mark v (root + 1)
        let stack ← pushAll (adj v) rest
        let (mark, count) ← flood fuel adj root stack mark
        return (mark, count + 1)

def scanRoots (budget : ℕ) (adj : ℕ → List ℕ) :
    List ℕ → (ℕ → ℕ) → Charged ((ℕ → ℕ) × ℕ × ℕ)
  | [], mark => do tick; return (mark, 0, 0)
  | v :: vs, mark => do
    tick
    if mark v ≠ 0 then scanRoots budget adj vs mark
    else
      let (mark, nv) ← flood budget adj v [v] mark
      let (mark, nv', nc) ← scanRoots budget adj vs mark
      return (mark, nv + nv', nc + 1)

structure Analysis where
  mark : ℕ → ℕ
  vertices : ℕ
  components : ℕ
  cyclic : Bool

/-- A finite undirected multigraph is a forest iff m = v-components.
That fact is a correctness proof obligation, not a stored assumption. -/
def analyze (es : List ActiveEdge) : Charged Analysis := do
  tick
  let m ← cLength es
  let (adj, roots) ← buildAdj es (fun _ => []) []
  let (mark, nv, nc) ← scanRoots (2 * m + 2) adj roots (fun _ => 0)
  return ⟨mark, nv, nc, decide (nv - nc < m)⟩

def representative (mark : ℕ → ℕ) (v : ℕ) : ℕ :=
  if mark v = 0 then v else mark v - 1

def contractEdges (mark : ℕ → ℕ) (es : List ActiveEdge) : Charged (List ActiveEdge) :=
  cMap (fun e => do
    tick
    return { e with u := representative mark e.u, v := representative mark e.v }) es

def cAppend {α : Type} : List α → List α → Charged (List α)
  | [], ys => do tick; return ys
  | x :: xs, ys => do tick; return x :: (← cAppend xs ys)

noncomputable def splitLabels (p : EReal) : List ActiveEdge →
    Charged (List ActiveEdge × List ActiveEdge × List ActiveEdge)
  | [] => do tick; return ([], [], [])
  | e :: es => do
    tick
    let (lo, eq, hi) ← splitLabels p es
    if (e.label : EReal) < p then return (e :: lo, eq, hi)
    else if p < (e.label : EReal) then return (lo, eq, e :: hi)
    else return (lo, e :: eq, hi)

/-- Three-way median extension of Algorithm 2. A cyclic median level is
returned immediately; only a strict high or strict low part can be recursed on.
No distinct-label assumption, probabilistic termination, or cycle enumeration. -/
noncomputable def thresholdFuel : ℕ → List ActiveEdge → Charged EReal
  | 0, _ => do tick; return ⊥
  | fuel + 1, es => do
    tick
    match es with
    | [] => return ⊥
    | [e] => return if e.u = e.v then (e.label : EReal) else ⊥
    | _ =>
      let n ← cLength es
      let labels ← cMap (fun e => do tick; return (e.label : EReal)) es
      let median ← select labels (n / 2)
      let (lo, eq, hi) ← splitLabels median es
      let upper ← analyze hi
      if upper.cyclic then thresholdFuel fuel hi
      else
        let ge ← cAppend eq hi
        let atMedian ← analyze ge
        if atMedian.cyclic then return median
        else thresholdFuel fuel (← contractEdges atMedian.mark lo)

noncomputable def findThreshold (es : List ActiveEdge) : Charged EReal := do
  let m ← cLength es
  thresholdFuel (m + 1) es

noncomputable def splitZero : List ActiveEdge → Charged (List ActiveEdge × List ActiveEdge)
  | [] => do tick; return ([], [])
  | e :: es => do
    tick
    let (zero, positive) ← splitZero es
    if e.weight = 0 then return (e :: zero, positive)
    else return (zero, e :: positive)

inductive Prepared where
  | forest
  | zeroCycle
  | positive (vertices : ℕ) (edges : List ActiveEdge)

/-- Original isolated vertices are never scanned. Admissible inputs have none.
The empty input takes a constant branch before any logarithm or division. -/
noncomputable def prepare (G : WeightedGraph) : Charged Prepared := do
  tick
  if G.q = 0 then return .forest
  let es ← loadEdges G
  let all ← analyze es
  if !all.cyclic then return .forest
  let (zs, ps) ← splitZero es
  let zero ← analyze zs
  if zero.cyclic then return .zeroCycle
  let positive ← contractEdges zero.mark ps
  let stats ← analyze positive
  return .positive stats.vertices positive

/-- No Fin bound is assumed of an internal ID; out-of-range IDs are explicitly
totalized and never reached from a well-formed original graph. -/
def readTape (G : WeightedGraph) (X : Fin G.q → ℝ) (i : ℕ) : ℝ :=
  if h : i < G.q then X ⟨i, h⟩ else 0

/-- Each tape access here is one ideal Exp(edge.weight) draw. Its continuous
joint law is fixed separately; unused zero-edge coordinates are dirac at zero. -/
def sampleEdges (G : WeightedGraph) (es : List ActiveEdge)
    (X : Fin G.q → ℝ) : Charged (List ActiveEdge) :=
  cMap (fun e => do tick; return { e with label := readTape G X e.original }) es

end GirthFiltering.RandomFiltering


