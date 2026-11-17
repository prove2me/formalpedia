-- Prove2me | Definitions.Def_PathCount2k_Supplement_TreeAlgorithm
-- name    : PathCount2k_Supplement_TreeAlgorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:20:46.394814+00:00
-- url     : https://prove2.me/theorems/e29b8eb8-eff7-4eb1-9a23-df74abc6fef3
-- title:
--   §3 — the tree / bounded-treewidth embedding counting algorithm as a charged program
-- statement:
--   This definition writes out the algorithm of §3 (pp.18–27) that proves Theorem 1.2, as a program whose arithmetic operations are counted.
--
--   Input: a pattern on $k$ vertices and a host on $n$ vertices, both as arc sets (an undirected graph enters as both orientations of every edge), a parameter $0<\eta\le1$, accuracy $0<\varepsilon,\delta<1$, and a tape of fair random bits.
--
--   1. **Trivial cases.** $k=0$ returns $1$; $k=1$ returns the number of host vertices (respecting pattern loops, of which forests have none); $k>n$ returns $0$.
--   2. **Structure** (fixed before sampling). $c$ is the least integer $c\ge2$ with $(ec)^{1/c}\le1+\eta/2$ and $h=\lfloor k/c\rfloor$ (Lemma 3.3). A tree decomposition of the pattern of width $\mathrm{tw}(H)$ is computed from an optimal elimination ordering (subset dynamic program, $2^kk^{O(1)}$ operations); the greedy marking of Lemma 3.4 gives a separator $S$ whose removal leaves components of at most $h$ vertices; each component gets a nice tree decomposition (Definition 3.6) with every pattern arc checked once.
--   3. **One trial.** Sample vectors $g_v\in\mathbb Z^k$ and matrices $H_{i,v}\in\mathbb Z^{k\times k}$ with independent entries distributed as the scalar $\xi$ of Definition 2.15. For every injective arc-preserving assignment $\sigma$ of $S$ (Definition 3.5), compute the separator product by degree-one insertions, the component tables of Definition 3.8 (leaf, introduce, edge-check, forget, join) with matrix-valued exterior products (Definition 3.4) enumerated as in Lemma 3.1, and multiply the component contributions in order (Definition 3.9). Sum over $\sigma$ and read $Z_0=b_0^{\top}[Q]_{[k]}b_0$.
--   4. **Amplification** (§3.8). $R=\lceil216K_k\varepsilon^{-2}\rceil$, $q=2\lceil\log_2(2/\delta)\rceil+1$, $\Gamma=k!\,k^{k-1}$; one global budget of $4T_{\mathrm{samp}}$ rejection attempts with $T_{\mathrm{samp}}=Rq\,kn(1+k^2)$ (Observation 3.3), returning $0$ if it is exhausted; $A_j=\sum Z_0^2$ over $R$ trials; output $\mathrm{median}(A_1,\dots,A_q)/(R\Gamma)$ with a linear-time median.
--
--   The random-bit budget is $16T_{\mathrm{samp}}$ when $2\le k\le n$ and $0$ otherwise.
--
--   **Formalization Note** The program is written in the published cost monad `CapacitatedAssort.General.Work`: every arithmetic operation, comparison, loop step and sampling attempt is charged at the site where its value is formed, and the operation count of a run is the monad's final counter. The paper finds a width-$t$ decomposition with the routine of [ACP87] (proof of Theorem 1.2, p.27) and allows Lemma 3.2 for forests; the program instead computes an optimal elimination ordering (Bodlaender–Fomin–Koster–Kratsch–Thilikos subset recursion) and always uses Lemma 3.4, at cost $2^kk^{O(1)}$, which lies within the $(2+\eta)^k$ factor. Tables are functions of full maps $\phi:\{0,\dots,k-1\}\to V(G)$ that depend only on $\phi$ on the bag; each node is charged for its $n^{|B_x|}$ entries. Sample layout: $g_v(j)$ is draw $vk+j$ and entry $(a,b)$ of $H_{i,v}$ is draw $nk+((in+v)k+a)k+b$ of a trial, as in the base mission.
-- source:
--   Panolan, Saurabh, Xue, Zehavi, Counting Paths in Time O*(2^k), with Extensions to Counting Bounded Treewidth Graphs and Multilinear Monomials, STOC 2027 submission manuscript (Nov 2026), §3.1–§3.8, pp.18–27: Lemma 3.1 p.18, Lemmas 3.3–3.4 pp.19–20, Definitions 3.3–3.9 pp.21–25, Observation 3.3 and the complete algorithm pp.26–27

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work
import Definitions.Def_PathCount2k_Exterior
import Definitions.Def_PathCount2k_Gaussian
import Definitions.Def_PathCount2k_DP
import Definitions.Def_PathCount2k_Algorithm
import Definitions.Def_PathCount2k_Supplement_Embedding

open CapacitatedAssort.General

namespace PathCount2k.Supplement

/-! # The algorithm of Theorem 1.2 (§3) as a charged program on a fair-bit tape

Panolan, Saurabh, Xue, Zehavi, *Counting Paths in Time O\*(2^k), with Extensions to Counting
Bounded Treewidth Graphs and Multilinear Monomials*, STOC 2027 submission manuscript (Nov 2026),
§3.1–§3.8, pp.18–27.

**Formalization Note.**
1. *Input.* A pattern given by its arc set `PA : Finset (Fin k × Fin k)` and a host given by its arc
   set `GA : Finset (Fin n × Fin n)` (directed, as at the end of the proof on p.27). An undirected
   pattern or host enters as `symArcs` (both orientations of every edge), see `countEmbU`. Each
   adjacency test is charged one operation after `n²` (host) and `k²` (pattern) preprocessing
   (Lemma 3.9: "After `O(n²)` preprocessing for constant-time host adjacency tests").
2. *Cost model.* The published monad `CapacitatedAssort.General.Work`; every arithmetic operation on
   a table value, every comparison and loop step is charged at the site where its result is formed
   (`charge`), following the base mission. A charged step returns its value as a pure expression whose
   naive evaluation performs exactly the charged operations.
3. *Decomposition.* The paper finds a width-`t` decomposition "in `k^{O(t+1)}` time [ACP87]" (p.27).
   This program instead computes an optimal elimination ordering by the exact subset dynamic program
   `TW(S) = min_{v ∈ S} max(TW(S ∖ v), |Q(S ∖ v, v)|)` (Bodlaender, Fomin, Koster, Kratsch,
   Thilikos, *On exact algorithms for treewidth*, ACM TALG 9(1), 2012) at cost `2^k k^{O(1)}`, which
   is within the `(2 + η)^k` factor of the theorem, and takes the elimination-forest decomposition
   (bag `{v} ∪ Q(S_v, v)`, parent = earliest-eliminated vertex of `Q(S_v, v)`), whose width is
   `tw(H)`. Each vertex is assigned to its own node (weight one) for Lemma 3.4.
4. *Separator.* Lemma 3.4's greedy marking on that forest, with `c` the least integer `c ≥ 2` with
   `e·c ≤ (1 + η/2)^c` (equivalently `(ec)^{1/c} ≤ 1 + η/2`, proof of Lemma 3.3) and `h = ⌊k/c⌋`.
   For forests the paper "may instead use Lemma 3.2" (p.21); this program always uses Lemma 3.4.
5. *Nice decompositions* (Definition 3.6, Lemma 3.6) of each component `C` of `H − S` are built from
   the forest with bags intersected with `C`: at a node, each child's decomposition is brought to the
   node's bag by forget chains then introduce chains, the children are joined left to right, and each
   arc of `H[C]` is checked once, at the node of its earlier-eliminated endpoint (whose bag contains
   both endpoints); the forest roots are closed by forget chains to the empty bag and joined. An
   undirected edge enters as two opposite arcs and so is checked twice (at the same node).
6. *Tables* (Definition 3.8) are functions of a full map `ϕ : Fin k → Fin n`; an entry depends only
   on `ϕ` on the node's bag, and each node is charged for its `n^{|B_x|}` entries.
7. *Matrix-valued exterior elements* (Definition 3.4) are coefficient functions
   `Finset (Fin k) → Matrix (Fin k) (Fin k) ℤ`; the product with a factor of degree at most `h`
   is the enumeration of Lemma 3.1 (`starLe`), charged per enumerated pair.
8. *Sampling* (§3.8 step 2, Observation 3.3): the four-bit rejection sampler of the base mission
   (`PathCount2k.block`, `PathCount2k.xiDecode`) with one global budget of `4·T_samp` attempts,
   `T_samp = R q · k n (1 + k²)`; one charge per attempt; on exhaustion the program returns `0`. The
   draws of a trial are laid out as in the base mission (`PathCount2k.vecOf`, `PathCount2k.matOf`):
   `g_v(j)` is draw `v·k + j`, entry `(a, b)` of `H_{i,v}` is draw `n·k + ((i·n + v)·k + a)·k + b`.
9. *Amplification* (§3.8): `R = ⌈216 K_k ε⁻²⌉` (`PathCount2k.paramR`),
   `q = 2⌈log₂(2/δ)⌉ + 1` (`PathCount2k.paramq`), `Γ = k! k^{k−1}` (`PathCount2k.Gamma`),
   linear-time median (`PathCount2k.selectMedian`), output `median(A₁, …, A_q)/(RΓ)`. -/

/-! ## Matrix-valued exterior elements (Definition 3.4) -/

/-- A matrix-valued exterior element `F = ∑_A e_A ⊗ F_A` with `F_A ∈ ℤ^{k×k}`, Definition 3.4,
p.22. -/
abbrev MExt (k : ℕ) := Finset (Fin k) → Matrix (Fin k) (Fin k) ℤ

/-- The identity `1 = e_∅ ⊗ I_k`, Definition 3.4. -/
def mone (k : ℕ) : MExt k := fun A => if A = ∅ then 1 else 0

/-- The local factor `A_{i,v} = g_v ⊗ H_{i,v}`, Definition 3.4, p.22. -/
def localF {n k : ℕ} (g : Fin n → Fin k → ℤ) (H : Fin k → Fin n → Fin k → Fin k → ℤ) (i : Fin k)
    (v : Fin n) : MExt k :=
  fun A => ∑ j : Fin k, if A = {j} then g v j • Matrix.of (H i v) else 0

/-- **The product `F ⋆ G` enumerated as in Lemma 3.1**, p.18: pairs `(A, B)` with `|B| ≤ h`
and `A ∩ B = ∅`, contributing `(−1)^{inv(A,B)} F_A G_B` to coordinate `A ∪ B` ("each coefficient
multiplication becomes an ordered matrix multiplication"). When `G` has degree at most `h` this is
`(a ⊗ B) ⋆ (b ⊗ C) = (a ∧ b) ⊗ (BC)` extended bilinearly. -/
def starLe {k : ℕ} (h : ℕ) (F G : MExt k) : MExt k := fun S =>
  ∑ A : Finset (Fin k), ∑ B : Finset (Fin k),
    if B.card ≤ h ∧ Disjoint A B ∧ A ∪ B = S then ((-1 : ℤ) ^ inv A B) • (F A * G B) else 0

/-- The number of pairs enumerated by Lemma 3.1: `∑_{j ≤ h} C(k, j) 2^{k−j}`. -/
def pairCount (k h : ℕ) : ℕ := ∑ j ∈ Finset.range (min h k + 1), Nat.choose k j * 2 ^ (k - j)

/-- Charge of one product `starLe h`: listing subsets by size (`(k+1)·2^k`, as the base
`enumMasks`), then per enumerated pair the sign (`k`), the `k × k` matrix product (`2k³`) and the
accumulation (`k²`), plus `3` for indexing. -/
def starCharge (k h : ℕ) : ℕ := (k + 1) * 2 ^ k + pairCount k h * (2 * k ^ 3 + k ^ 2 + k + 3)

/-- The charged product with a factor of degree at most `h` (Lemma 3.1). -/
def starW {k : ℕ} (h : ℕ) (F G : MExt k) : Work (MExt k) := do
  charge (starCharge k h)
  return starLe h F G

/-! ## Elimination ordering and the elimination-forest decomposition -/

/-- The subset of `Fin k` with mask `T`. -/
def ofMask (k T : ℕ) : Finset (Fin k) := Finset.univ.filter fun j => T.testBit j.val

/-- The vertices of `S ∪ {v}` reachable from `v` by a path with all vertices in `S ∪ {v}`
(`k` rounds of expansion). -/
def reachIn {k : ℕ} (adj : Fin k → Fin k → Bool) (S : Finset (Fin k)) (v : Fin k) :
    Finset (Fin k) :=
  (fun R => R ∪ S.filter fun w => ∃ u ∈ R, adj u w = true)^[k] {v}

/-- `Q(S, v)`: the vertices outside `S ∪ {v}` adjacent to a vertex reachable from `v` through `S`
(the higher neighbours of `v` in the filled graph when `S` is eliminated before `v`). -/
def Qset {k : ℕ} (adj : Fin k → Fin k → Bool) (S : Finset (Fin k)) (v : Fin k) :
    Finset (Fin k) :=
  Finset.univ.filter fun w => w ∉ S ∧ w ≠ v ∧ ∃ u ∈ reachIn adj S v, adj u w = true

/-- **Optimal elimination ordering** by the subset dynamic program
`TW(S) = min_{v ∈ S} max(TW(S ∖ {v}), |Q(S ∖ {v}, v)|)`, processing subsets by increasing size;
`arg S` is the first minimizing `v` (eliminated last among `S`). Returns the elimination order
(first eliminated first). Charges: the base `enumMasks` per size, `k + 1` per mask (decoding), and
per pair `(S, v)` the `k` rounds of reachability (`k³`), `Q` (`k²`) and `3` comparisons. -/
def elimOrder (k : ℕ) (adj : Fin k → Fin k → Bool) : Work (List (Fin k)) := do
  let mut tw : Finset (Fin k) → ℕ := fun _ => 0
  let mut arg : Finset (Fin k) → Option (Fin k) := fun _ => none
  for p in List.range' 1 k do
    let masks ← PathCount2k.enumMasks k p
    for T in masks do
      charge (k + 1)
      let S := ofMask k T
      let mut best : Option (Fin k × ℕ) := none
      for v in List.finRange k do
        charge 1
        if v ∈ S then
          charge (k ^ 3 + k ^ 2 + 3)
          let val := max (tw (S.erase v)) (Qset adj (S.erase v) v).card
          match best with
          | none => best := some (v, val)
          | some (_, b) => if val < b then best := some (v, val)
      match best with
      | none => pure ()
      | some (v, b) =>
          tw := fun S' => if S' = S then b else tw S'
          arg := fun S' => if S' = S then some v else arg S'
  let mut S : Finset (Fin k) := Finset.univ
  let mut order : List (Fin k) := []
  for _ in List.range k do
    charge (k + 2)
    match arg S with
    | none => pure ()
    | some v =>
        order := v :: order
        S := S.erase v
  return order

/-- The elimination-forest data: for each vertex `v`, its bag `{v} ∪ Q(S_v, v)` (`S_v` = the
vertices eliminated before `v`) and its parent, the vertex of `Q(S_v, v)` eliminated first (none
for a root). -/
structure ElimForest (k : ℕ) where
  /-- the elimination order, first eliminated first -/
  order : List (Fin k)
  /-- the bag of each vertex's node -/
  bag : Fin k → Finset (Fin k)
  /-- the parent of each vertex's node -/
  parent : Fin k → Option (Fin k)

/-- Position of `v` in the elimination order. -/
def ElimForest.pos {k : ℕ} (E : ElimForest k) (v : Fin k) : ℕ := E.order.idxOf v

/-- Build the elimination forest from an order (pure), charged `k⁴ + k` by `elimForest`. -/
def mkElimForest {k : ℕ} (adj : Fin k → Fin k → Bool) (order : List (Fin k)) : ElimForest k :=
  let before : Fin k → Finset (Fin k) := fun v =>
    Finset.univ.filter fun u => order.idxOf u < order.idxOf v
  let bag : Fin k → Finset (Fin k) := fun v => insert v (Qset adj (before v) v)
  let parent : Fin k → Option (Fin k) := fun v =>
    ((order.drop (order.idxOf v + 1)).filter fun u => u ∈ Qset adj (before v) v).head?
  ⟨order, bag, parent⟩

/-- The charged elimination-forest construction (per vertex: `S_v` (`k`), reachability and `Q`
(`k³ + k²`), parent search (`k`)). -/
def elimForest (k : ℕ) (adj : Fin k → Fin k → Bool) : Work (ElimForest k) := do
  let order ← elimOrder k adj
  charge (k * (k ^ 3 + k ^ 2 + 2 * k + 2) + 1)
  return mkElimForest adj order

/-! ## Lemma 3.4: small separator; components of `H − S` -/

/-- **Lemma 3.4's greedy marking** (p.20): "Root the decomposition tree and process it from leaves
to root. At a node, add its weight to the residual weights returned by its children. If the sum
exceeds `h`, mark the node and return zero; otherwise return the sum." Nodes are processed in
elimination order (children before parents); every node has weight one. Returns
`S = ⋃_{marked x} B_x`. Charged `4` per node plus `k` per marked bag union. -/
def separator {k : ℕ} (E : ElimForest k) (h : ℕ) : Work (Finset (Fin k)) := do
  let mut acc : Fin k → ℕ := fun _ => 0
  let mut S : Finset (Fin k) := ∅
  for v in E.order do
    charge 4
    let tot := 1 + acc v
    if h < tot then
      charge k
      S := S ∪ E.bag v
    else
      match E.parent v with
      | none => pure ()
      | some p => acc := fun u => if u = p then acc u + tot else acc u
  return S

/-- The connected components of `H − S` (underlying undirected adjacency), each as a vertex set,
listed by increasing least vertex. Charged `k + 1` per vertex scan and `k³ + k` per component. -/
def components {k : ℕ} (adj : Fin k → Fin k → Bool) (S : Finset (Fin k)) :
    Work (List (Finset (Fin k))) := do
  let mut seen : Finset (Fin k) := S
  let mut comps : List (Finset (Fin k)) := []
  for u in List.finRange k do
    charge (k + 1)
    if u ∉ seen then
      charge (k ^ 3 + k)
      let C := reachIn adj (Finset.univ \ S) u
      comps := comps ++ [C]
      seen := seen ∪ C
  return comps

/-! ## Nice tree decompositions (Definition 3.6) -/

/-- **A nice tree decomposition**, Definition 3.6, p.22–23: leaves (empty bag), introduce, forget,
edge-check (a designated arc `(i, j)`) and join (two ordered children) nodes; the bag is computed
from the node type. -/
inductive Nice (k : ℕ)
  | leaf : Nice k
  | intro : Fin k → Nice k → Nice k
  | forget : Fin k → Nice k → Nice k
  | check : Fin k → Fin k → Nice k → Nice k
  | join : Nice k → Nice k → Nice k

/-- The bag of a node: `B_x = B_y ∪ {i}` (introduce), `B_y ∖ {i}` (forget), `B_y` (edge-check,
join), `∅` (leaf). -/
def Nice.bag {k : ℕ} : Nice k → Finset (Fin k)
  | .leaf => ∅
  | .intro i c => insert i c.bag
  | .forget i c => c.bag.erase i
  | .check _ _ c => c.bag
  | .join l _ => l.bag

/-- The number of nodes. -/
def Nice.size {k : ℕ} : Nice k → ℕ
  | .leaf => 1
  | .intro _ c => c.size + 1
  | .forget _ c => c.size + 1
  | .check _ _ c => c.size + 1
  | .join l r => l.size + r.size + 1

/-- The elements of a set of pattern vertices, in increasing order. -/
def elems {k : ℕ} (X : Finset (Fin k)) : List (Fin k) := (List.finRange k).filter (· ∈ X)

/-- Introduce, forget and edge-check chains, and a left-to-right join of several children. -/
def introChain {k : ℕ} (l : List (Fin k)) (N : Nice k) : Nice k := l.foldl (fun N i => .intro i N) N
def forgetChain {k : ℕ} (l : List (Fin k)) (N : Nice k) : Nice k :=
  l.foldl (fun N i => .forget i N) N
def checkChain {k : ℕ} (l : List (Fin k × Fin k)) (N : Nice k) : Nice k :=
  l.foldl (fun N a => .check a.1 a.2 N) N
def joinAll {k : ℕ} : List (Nice k) → Nice k
  | [] => .leaf
  | N :: Ns => Ns.foldl (fun acc M => .join acc M) N

/-- The nice decomposition of `H[C]` rooted at the forest node `v`, with root bag `B_v ∩ C`
(Lemma 3.6's transformation on the forest with bags intersected with `C`). The arcs of `H[C]` are
checked at the node of their earlier-eliminated endpoint (whose bag contains both endpoints). `fuel`
bounds the depth (`k` suffices: parents are eliminated later). -/
def niceAt {k : ℕ} (E : ElimForest k) (PA : Finset (Fin k × Fin k)) (C : Finset (Fin k)) :
    ℕ → Fin k → Nice k
  | 0, _ => .leaf
  | fuel + 1, v =>
      let X := E.bag v ∩ C
      let kids := (List.finRange k).filter fun u => E.parent u = some v
      let adapted := kids.map fun u =>
        let Y := E.bag u ∩ C
        introChain (elems (X \ Y)) (forgetChain (elems (Y \ X)) (niceAt E PA C fuel u))
      let base := if kids = [] then introChain (elems X) .leaf else joinAll adapted
      let arcs := ((List.finRange k ×ˢ List.finRange k).filter fun a =>
        decide (a ∈ PA) && decide (a.1 ∈ C) && decide (a.2 ∈ C) &&
          (if E.pos a.1 ≤ E.pos a.2 then decide (a.1 = v) else decide (a.2 = v)))
      checkChain arcs base

/-- The nice decomposition of `H[C]` (empty root and leaf bags): each forest root's decomposition
closed by a forget chain to the empty bag, joined left to right. -/
def niceOf {k : ℕ} (E : ElimForest k) (PA : Finset (Fin k × Fin k)) (C : Finset (Fin k)) :
    Nice k :=
  joinAll (((List.finRange k).filter fun v => E.parent v = none).map fun v =>
    forgetChain (elems (E.bag v ∩ C)) (niceAt E PA C k v))

/-- The charged construction of the nice decomposition of a component (charged `(k + 1)²` per
node and `k³` for the arc and child scans). -/
def niceW {k : ℕ} (E : ElimForest k) (PA : Finset (Fin k × Fin k)) (C : Finset (Fin k)) :
    Work (Nice k) := do
  let N := niceOf E PA C
  charge ((N.size + 1) * (k + 1) ^ 2 + k ^ 3 + k ^ 2)
  return N

/-! ## The component dynamic program (Definition 3.8) -/

/-- A table: an assignment of the pattern vertices (only its values on the bag matter) ↦ entry. -/
abbrev Table (n k : ℕ) := (Fin k → Fin n) → MExt k

/-- **The table recurrences of Definition 3.8**, p.24, for a fixed separator assignment, given the
allowed-image test `Lok i v ↔ v ∈ L^σ_i`:
1. "Leaf. `F_x(∅) = 1`."
2. "Introduce `i`. … `F_x(ϕ) = 1[ϕ(i) ∈ L^σ_i] F_y(ϕ|_{B_y})`."
3. "Check `{i, j}`. … `F_x(ϕ) = 1[{ϕ(i), ϕ(j)} ∈ E(G)] F_y(ϕ)`" (directed: `(ϕ(i), ϕ(j)) ∈ E(G)`).
4. "Forget `i`. … `F_x(ϕ) = ∑_{v ∈ L^σ_i} F_y(ϕ ∪ {i ↦ v}) ⋆ A_{i,v}`."
5. "Join. For the ordered children `y, z`, set `F_x(ϕ) = F_y(ϕ) ⋆ F_z(ϕ)`."
Charges per node: `n^{|B|}` entries, each charged a copy of its `2^k k²` scalars plus indexing;
a forget node is charged per child entry the test, one degree-one product and the accumulation;
a join node one product `starLe h` per entry (both factors have degree at most `|C| ≤ h`). -/
def runNice {n k : ℕ} (h : ℕ) (Lok : Fin k → Fin n → Bool) (GA : Finset (Fin n × Fin n))
    (g : Fin n → Fin k → ℤ) (H : Fin k → Fin n → Fin k → Fin k → ℤ) : Nice k → Work (Table n k)
  | .leaf => do
      charge (2 ^ k * k ^ 2 + 1)
      return fun _ => mone k
  | .intro i c => do
      let F ← runNice h Lok GA g H c
      let B := (Nice.intro i c).bag
      charge (n ^ B.card * (2 ^ k * k ^ 2 + B.card + 2))
      return fun ϕ => if Lok i (ϕ i) then F ϕ else 0
  | .check i j c => do
      let F ← runNice h Lok GA g H c
      let B := c.bag
      charge (n ^ B.card * (2 ^ k * k ^ 2 + B.card + 2))
      return fun ϕ => if (ϕ i, ϕ j) ∈ GA then F ϕ else 0
  | .forget i c => do
      let F ← runNice h Lok GA g H c
      let B := c.bag
      charge (n ^ B.card * (starCharge k 1 + 2 ^ k * k ^ 2 + B.card + 2))
      return fun ϕ => ∑ v : Fin n,
        if Lok i v then starLe 1 (F (Function.update ϕ i v)) (localF g H i v) else 0
  | .join l r => do
      let F ← runNice h Lok GA g H l
      let G ← runNice h Lok GA g H r
      let B := l.bag
      charge (n ^ B.card * (starCharge k h + B.card + 2))
      return fun ϕ => starLe h (F ϕ) (G ϕ)

/-! ## One trial: the assembled contribution `Q` (Definition 3.9) and `Z₀ = b₀ᵀ [Q]_{[k]} b₀` -/

/-- The preprocessed structure of the pattern: separator `S` (as an increasing list, the order
`π_S`), the components `C₁, …, C_ℓ` with their nice decompositions, and `h`. -/
structure Prep (k : ℕ) where
  /-- the separator, increasing -/
  sep : List (Fin k)
  /-- the components with their nice decompositions -/
  comps : List (Finset (Fin k) × Nice k)
  /-- the component-size bound `h = ⌊k/c⌋` -/
  h : ℕ

/-- All maps `Fin k → Fin n` that equal `d` outside the list `l` (one per assignment of the
vertices of `l`). -/
def mapsOn {n k : ℕ} (d : Fin n) : List (Fin k) → List (Fin k → Fin n)
  | [] => [fun _ => d]
  | s :: l => (mapsOn d l).flatMap fun σ => (List.finRange n).map fun v => Function.update σ s v

/-- **One trial** (§3.6, §3.8 step 3): for every separator assignment `σ ∈ Σ` (injective on `S`,
preserving every arc of `H[S]`; Definition 3.5), the allowed images
`L^σ_i = {v ∉ σ(S) : (v, σ(j)) ∈ E(G) for every arc (i, j), (σ(j), v) ∈ E(G) for every arc (j, i),
j ∈ S}`, then `A_{π_S}(σ)` by inserting the separator vertices one at a time, then the component
contributions `Q^σ_{C}` multiplied on the right in order (Definition 3.9:
`Q = ∑_σ A_{π_S}(σ) ⋆ Q^σ_{C₁} ⋆ ⋯ ⋆ Q^σ_{C_ℓ}`), all with the same samples; returns
`Z₀ = b₀ᵀ [Q]_{[k]} b₀`, the `(0, 0)` entry of the coefficient of `e_{[k]}`. -/
def trial {n k : ℕ} (PA : Finset (Fin k × Fin k)) (GA : Finset (Fin n × Fin n)) (P : Prep k)
    (d : Fin n) (g : Fin n → Fin k → ℤ) (H : Fin k → Fin n → Fin k → Fin k → ℤ) : Work ℤ := do
  let Sset : Finset (Fin k) := (Finset.univ.filter fun i => i ∈ P.sep)
  let mut Q : MExt k := fun _ => 0
  for σ in mapsOn d P.sep do
    charge (3 * P.sep.length ^ 2 + P.sep.length + 1)
    let valid : Bool :=
      decide (∀ i ∈ Sset, ∀ j ∈ Sset, σ i = σ j → i = j) &&
        decide (∀ a ∈ PA, a.1 ∈ Sset → a.2 ∈ Sset → (σ a.1, σ a.2) ∈ GA)
    if valid then
      charge (k * n * (3 * P.sep.length + 2))
      let Lok : Fin k → Fin n → Bool := fun i v =>
        decide ((∀ j ∈ Sset, σ j ≠ v) ∧ ∀ j ∈ Sset,
          ((i, j) ∈ PA → (v, σ j) ∈ GA) ∧ ((j, i) ∈ PA → (σ j, v) ∈ GA))
      let mut Pr : MExt k := mone k
      for s in P.sep do
        Pr ← starW 1 Pr (localF g H s (σ s))
      for C in P.comps do
        let T ← runNice P.h Lok GA g H C.2
        Pr ← starW P.h Pr (T σ)
      charge (2 ^ k * k ^ 2)
      Q := Q + Pr
  charge 1
  if hk : 0 < k then return Q Finset.univ ⟨0, hk⟩ ⟨0, hk⟩ else return 0

/-! ## Global-budget sampler (Observation 3.3) -/

/-- One draw of `ξ` from the global attempt budget `B` at cursor `pos`: returns the value (`none`
when the budget is exhausted), the new cursor, and the remaining budget. -/
def drawG (t : ℕ → Bool) : ℕ → ℕ → Option ℤ × ℕ × ℕ
  | 0, pos => (none, pos, 0)
  | B + 1, pos =>
      if PathCount2k.block t pos < 12 then
        (some (PathCount2k.xiDecode (PathCount2k.block t pos)), pos + 4, B)
      else drawG t B (pos + 4)

/-- `c` consecutive draws from the global budget; `none` as soon as the budget is exhausted. -/
def drawListG (t : ℕ → Bool) : ℕ → ℕ → ℕ → Option (List ℤ) × ℕ × ℕ
  | 0, pos, B => (some [], pos, B)
  | c + 1, pos, B =>
      match drawG t B pos with
      | (none, p', B') => (none, p', B')
      | (some x, p', B') =>
          match drawListG t c p' B' with
          | (none, p'', B'') => (none, p'', B'')
          | (some xs, p'', B'') => (some (x :: xs), p'', B'')

/-! ## The complete algorithm (§3.8) -/

/-- `c`: the least integer `c ≥ 2` with `e·c ≤ (1 + η/2)^c`, i.e. `(ec)^{1/c} ≤ 1 + η/2`
(proof of Lemma 3.3, p.19). -/
noncomputable def cParam (η : ℝ) : ℕ :=
  sInf {c : ℕ | 2 ≤ c ∧ Real.exp 1 * c ≤ (1 + η / 2) ^ c}

/-- `T_samp = Rq·kn(1 + k²)`, §3.8 step 2 (equal to the base `PathCount2k.paramT`). -/
noncomputable def Tsamp (n k : ℕ) (ε δ : ℝ) : ℕ := PathCount2k.paramT n k ε δ

/-- **The random-bit budget**: `16·T_samp` fair bits (Observation 3.3: "at most `16s` fair random
bits", `s = T_samp`) when `2 ≤ k ≤ n`, and `0` in the exactly answered cases. -/
noncomputable def embBits (n k : ℕ) (ε δ : ℝ) : ℕ :=
  if 2 ≤ k ∧ k ≤ n then 16 * Tsamp n k ε δ else 0

/-- **The algorithm of Theorem 1.2** (§3.8, pp.26–27) on a directed pattern `PA` on `Fin k` and a
directed host `GA` on `Fin n`, with parameter `η` and fair-bit tape `b`.
1. "Preprocess. Handle `k = 1` and `k > n` exactly" (`k = 0`: the empty map, count `1`; `k = 1`:
   the vertices satisfying the pattern's loops, i.e. `n` for a loopless pattern). "Otherwise,
   construct the separator, the nice component decompositions, and the fixed order `π` …. Prepare
   the host adjacency table."
2. "Choose the parameters. Set `R = ⌈216K_kε⁻²⌉` and `q = 2⌈log₂(2/δ)⌉ + 1`. … `T_samp = Rq kn(1 + k²)`.
   Allow at most `4T_samp` rejection-sampling attempts over the entire algorithm. If this budget is
   exhausted before all required samples are obtained, return zero."
3. "Evaluate the trials. For each group `j ∈ [q]`, initialize `A_j = 0` and perform `R` trials. In
   each trial, generate fresh vectors and matrices, evaluate `Q`, and compute `Z₀ = b₀ᵀ[Q]_{[k]}b₀`.
   Update `A_j ← A_j + Z₀²`."
4. "Return the exact rational number `N̂ = median(A₁, …, A_q)/(RΓ)`."
The output is `((countEmb η k PA n GA ε δ b).run 0).1`, the operation count
`((countEmb η k PA n GA ε δ b).run 0).2`. -/
noncomputable def countEmb (η : ℝ) (k : ℕ) (PA : Finset (Fin k × Fin k)) (n : ℕ)
    (GA : Finset (Fin n × Fin n)) (ε δ : ℝ) (b : Fin (embBits n k ε δ) → Bool) : Work ℝ := do
  charge 1
  if k = 0 then return 1
  charge 1
  if k = 1 then
    let mut cnt : ℕ := 0
    for v in List.finRange n do
      charge (k ^ 2 + 2)
      if ∀ i : Fin k, (i, i) ∈ PA → (v, v) ∈ GA then cnt := cnt + 1
    return (cnt : ℝ)
  charge 1
  if n < k then return 0
  if hn : 0 < n then
    -- host adjacency table and pattern arc table
    charge (n ^ 2 + k ^ 2)
    let adj : Fin k → Fin k → Bool := fun i j => decide (i ≠ j ∧ ((i, j) ∈ PA ∨ (j, i) ∈ PA))
    -- c and h
    let c := cParam η
    charge (3 * (c + 1) ^ 2 + 2)
    let h := k / c
    -- decomposition, separator, components, nice decompositions
    let E ← elimForest k adj
    let S ← separator E h
    let comps ← components adj S
    let mut cd : List (Finset (Fin k) × Nice k) := []
    for C in comps do
      let N ← niceW E PA C
      cd := cd ++ [(C, N)]
    charge (k + 1)
    let P : Prep k := ⟨elems S, cd, h⟩
    -- parameters
    let R := PathCount2k.paramR k ε
    charge (2 * R + 4)
    let r := PathCount2k.paramr δ
    charge (2 * r + 4)
    let q := 2 * r + 1
    charge 6
    let budget := 4 * Tsamp n k ε δ
    charge 2
    let Γ := PathCount2k.Gamma k
    charge (2 * k + 1)
    let t : ℕ → Bool := fun i => if h' : i < embBits n k ε δ then b ⟨i, h'⟩ else false
    -- trials
    let mut pos := 0
    let mut B := budget
    let mut sums : List ℤ := []
    for _j in List.range q do
      charge 1
      let mut acc : ℤ := 0
      for _l in List.range R do
        let res := drawListG t (k * n * (1 + k ^ 2)) pos B
        charge (B - res.2.2 + 1)
        pos := res.2.1
        B := res.2.2
        match res.1 with
        | none => return 0
        | some xs =>
            let z ← trial PA GA P ⟨0, hn⟩ (PathCount2k.vecOf n k xs) (PathCount2k.matOf n k xs)
            charge 2
            acc := acc + z * z
      sums := acc :: sums
    let med ← PathCount2k.selectMedian sums
    charge 2
    return (med : ℝ) / ((R : ℝ) * (Γ : ℝ))
  else return 0

/-- **The algorithm on undirected graphs**: the pattern `H` and host `G` enter as their symmetric
arc sets (both orientations of each edge), after `k² + n²` adjacency tests. -/
noncomputable def countEmbU (η : ℝ) {k n : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ε δ : ℝ)
    (b : Fin (embBits n k ε δ) → Bool) : Work ℝ := do
  charge (k ^ 2 + n ^ 2)
  countEmb η k (symArcs H) n (symArcs G) ε δ b

end PathCount2k.Supplement


