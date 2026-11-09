-- Prove2me | Definitions.Def_MSTCuts2027_Parallel_Algorithms
-- name    : MSTCuts2027_Parallel_Algorithms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:20.157853+00:00
-- url     : https://prove2.me/theorems/c60f2a6a-8760-4d3e-b91c-26a813f9977b
-- title:
--   Algorithms 1, 2, 4, 8 and DACAssignMincut as programs; memory layout; the recursion tree $T(x)$
-- statement:
--   This file writes the paper's algorithms as one program of the machine and fixes where their data lives.
--
--   **Layout for $n$ vertices.** Cell $0$ holds $n$. The array $M$ holds pointers: $M(u,v)$ points to a cut stored as a Boolean array in a separate cut store, and a real cell holds the mincut value of the pair. An array `ord` lists vertices. The word cells of the recursion tree $T(x)$ hold, for round $j$ and index $i$, an edge $(x,\cdot)$ represented by its other endpoint, and a further cell records the number of rounds. The regions are disjoint. Words have absolute value at most $(n+2)^6$.
--
--   **Procedures.**
--   1. `elimBody` is EliminateTriangle (Algorithm 1). If the cut keeps $x$ on the side of $u$ it reports $v$, else $u$.
--   2. `pruneNodeBody`, `pruneLoopBody`, `pruneOneBody` and `pruneEdgesBody` are DACPruneEdges (Algorithm 8). The edges at $x$ are paired consecutively, each pair is resolved by EliminateTriangle, an unpaired last edge is passed on, and rounds repeat until one edge remains.
--   3. `mergeQueryBody` and `mergeQueriesBody` are the mincut computations of MergeTree (Algorithm 2, lines 3–6), one for each proxy edge, run concurrently. They also store the pointer and value of Appendix D.
--   4. `assignNodeBody`, `assignLoopBody` and `assignBody` are DACAssignMincut. They walk the rounds top-down, and if the pruned vertex is $e$ and the survivor $w$, then $M(x,e)=M(w,e)$ when $\lambda_1(w,e)\le\lambda_1(x,w)$ and $M(x,e)=M(x,w)$ otherwise.
--   5. `subsetBody` and `mainBody` are Algorithm 4. A block of at most two vertices is the base case; a larger block splits into $\lfloor s/2\rfloor$ and $\lceil s/2\rceil$ vertices, the two calls run concurrently, and the three routines above follow.
--   6. `proxySetBody` applies Algorithm 8 from the smaller of two blocks to the larger, as line 2 of Algorithm 2 does.
--
--   **Predicates.** `TableOK` is the invariant of Appendix D for a vertex set: all its pairs have a correct pointer and value. `AllPairsOutput` is the final output. `storedCover` is the set of cuts $M$ points to. `IsProxyEdge` has the two properties of Lemma 6. `TreeUpTo` and `IsRecursionTree` describe $T(x)$ in memory. `reportedProxySet` is the set $P$ of Theorem 2 read from memory. `mergeGraph` is the graph on the edges $T_1\cup T_2\cup P$. `subproblemLevel` lists the blocks of Algorithm 4 at a recursion level.
--
--   Stating the algorithms as a program makes the costs and independence claims of Appendices D and E statements about real executions.
--
--   **Formalization Note** Line 7 of Algorithm 2 (computing the tree $T'$) is not a machine step here. The program computes the cut output only, and no step of the cut output reads a tree: Algorithm 8 uses the vertex set of $T_B$ only, as Appendix D says. Trees enter through Theorem 2. Line 15 of Algorithm 4 prints the argument $C_A\cup C_B$; the program uses the updated cover, as Appendix D requires. The test in EliminateTriangle compares the membership of $x$ and of $u$, because the cut $(C,V\setminus C)$ is unoriented; on a cut containing $u$ this is the paper's test $x\in C$.
-- source:
--   Baswana–Roy, Using MSTs to Compute All-Pairs Mincuts and Beyond ..., STOC 2027 submission #21, pinned preprint SHA-256 faa337be0f0f1bfbbcf924cb3591bd51ded2a6ef2c9e2154e00534a840156a11, Algorithm 1 (printed p. 6, PDF p. 8), Algorithm 2 (printed p. 7, PDF p. 9), Algorithm 4 (printed p. 11, PDF p. 13), Algorithm 8 and Appendix D (printed pp. 21–22, PDF pp. 23–24), Appendix E, printed p. 24–25, PDF p. 26–27

import Mathlib
import Definitions.Def_MSTCuts2027_Parallel_CutModel
import Definitions.Def_MSTCuts2027_Parallel_Machine

/-!
# Algorithms 1, 2, 4, 8 and `DACAssignMincut` as machine programs

Baswana–Roy, *Using MSTs to Compute All-Pairs Mincuts and Beyond ...*, STOC 2027 submission #21:
Algorithm 1 (printed p. 6, PDF p. 8), Algorithm 2 (printed p. 7, PDF p. 9), Algorithm 4 (printed
p. 11, PDF p. 13), Algorithm 8 (printed p. 21, PDF p. 23), `DACAssignMincut`, the array `M` and the
recursion tree `T(x)` (printed p. 22, PDF p. 24), Appendix E (printed pp. 24–25, PDF pp. 26–27).

Memory layout for `n` vertices, with every region disjoint from the others:
cell `0` holds `n`; `M(u, v)` is the word cell `tableAddr`; `ord` lists vertices at `ordAddr`; a node
of `T(x)` is the word cell `treeAddr`; cuts are Boolean arrays in the cut store; the number of rounds
of `T(x)` is `roundsAddr`; and the real cell `lamAddr` holds the mincut value of `M(u, v)`.
-/

namespace MSTCuts2027.Parallel

/-! ## Addresses -/

/-- The word cell of `M(u, v)`. -/
def tableAddr (n u v : ℕ) : ℕ := 1 + u * n + v

/-- The real cell holding the mincut value stored with `M(u, v)`. -/
def lamAddr (n u v : ℕ) : ℕ := u * n + v

/-- The word cell of position `i` of the vertex array `ord`. -/
def ordAddr (n i : ℕ) : ℕ := n * n + 1 + i

/-- The first cell of the region of recursion-tree nodes. -/
def treeBase (n : ℕ) : ℕ := n * n + n + 1

/-- The word cell of entry `i` of round `j` of the tree `T(x)` of `x` towards the vertex block that
starts at position `l` of `ord`. Round `0` holds the leaves. -/
def treeAddr (n x l j i : ℕ) : ℕ := treeBase n + ((x * n + l) * n + j) * n + i

/-- The first cell of the cut store. -/
def cutBase (n : ℕ) : ℕ := treeBase n + n * n * n * n

/-- The cut slot of the pair `(x, y)`: Boolean array of `n` cells. -/
def cutAddr (n x y : ℕ) : ℕ := cutBase n + (x * n + y) * n

/-- The first cell after the cut store. -/
def roundsBase (n : ℕ) : ℕ := cutBase n + n * n * n

/-- The word cell holding the number of rounds of `T(x)`. -/
def roundsAddr (n x l : ℕ) : ℕ := roundsBase n + x * n + l

/-- The word size used by the programs below. -/
def wordBound (n : ℕ) : ℕ := (n + 2) ^ 6

/-! ## Programs -/

namespace Prog

instance : Add Expr := ⟨Expr.add⟩
instance : Sub Expr := ⟨Expr.sub⟩
instance : Mul Expr := ⟨Expr.mul⟩
instance : Div Expr := ⟨Expr.div⟩
instance (k : ℕ) : OfNat Expr k := ⟨Expr.const k⟩

/-- Sequencing, right-associated. -/
def block : List Stmt → Stmt
  | [] => .skip
  | [s] => s
  | s :: ss => .seq s (block ss)

/-- The number of vertices, read from cell `0`. -/
def N : Expr := .read 0
def eTable (u v : Expr) : Expr := 1 + u * N + v
def eLam (u v : Expr) : Expr := u * N + v
def eOrd (i : Expr) : Expr := N * N + 1 + i
def eTreeBase : Expr := N * N + N + 1
def eTree (x l j i : Expr) : Expr := eTreeBase + ((x * N + l) * N + j) * N + i
def eCutBase : Expr := eTreeBase + N * N * N * N
def eCut (x y : Expr) : Expr := eCutBase + (x * N + y) * N
def eRoundsBase : Expr := eCutBase + N * N * N
def eRounds (x l : Expr) : Expr := eRoundsBase + x * N + l

/-- Procedure numbers. -/
abbrev pElim : ℕ := 0
abbrev pPruneNode : ℕ := 1
abbrev pPruneLoop : ℕ := 2
abbrev pPruneOne : ℕ := 3
abbrev pPruneEdges : ℕ := 4
abbrev pMergeQuery : ℕ := 5
abbrev pMergeQueries : ℕ := 6
abbrev pAssignNode : ℕ := 7
abbrev pAssignLoop : ℕ := 8
abbrev pAssign : ℕ := 9
abbrev pSubset : ℕ := 10
abbrev pMain : ℕ := 11
abbrev pProxySet : ℕ := 12

/-- `EliminateTriangle(u, v, x, C¹ᵤᵥ)` (Algorithm 1), arguments `x, u, v, p, dest`, where `p` points
to the cut. It writes the vertex `a` of the eliminated pair `(x, a)` to `dest`: `v` if the cut keeps
`x` on the side of `u`, else `u`. The test compares the membership of `x` and `u`, because a stored
cut need not contain `u`; on a cut containing `u` it is the paper's test `x ∈ C¹ᵤᵥ`. -/
def elimBody : Stmt :=
  .ite (.eq (.eq (.read (.var 3 + .var 0)) 0) (.eq (.read (.var 3 + .var 1)) 0))
    (.write (.var 4) (.var 2))
    (.write (.var 4) (.var 1))

/-- One internal node of `T(x)` in `DACPruneEdges` (Algorithm 8, lines 6–7), arguments `x, l, j, i`:
entries `2i` and `2i+1` of round `j` hold `u, v`; EliminateTriangle runs on the cut `M(u, v)`, and
the surviving vertex becomes entry `i` of round `j+1`. -/
def pruneNodeBody : Stmt :=
  let x := Expr.var 0; let l := Expr.var 1; let j := Expr.var 2; let i := Expr.var 3
  let u := Expr.var 4; let v := Expr.var 5
  block [
    .setVar 4 (.read (eTree x l j (2 * i))),
    .setVar 5 (.read (eTree x l j (2 * i + 1))),
    .call pElim [x, u, v, .read (eTable u v), eTree x l (j + 1) i],
    .write (eTree x l (j + 1) i) (u + v - .read (eTree x l (j + 1) i))]

/-- The `while` loop of Algorithm 8 (lines 4–9), arguments `x, l, j, c`: round `j` has `c` entries,
paired consecutively. An unpaired last entry is passed on. At `c = 1` the round number is recorded. -/
def pruneLoopBody : Stmt :=
  let x := Expr.var 0; let l := Expr.var 1; let j := Expr.var 2; let c := Expr.var 3
  .ite (.le c 1) (.write (eRounds x l) j) <| block [
    .parFor 4 0 (c / 2) (.call pPruneNode [x, l, j, .var 4]),
    .ite (.eq (c - 2 * (c / 2)) 1)
      (.write (eTree x l (j + 1) (c / 2)) (.read (eTree x l j (c - 1))))
      .skip,
    .call pPruneLoop [x, l, j + 1, (c + 1) / 2]]

/-- Algorithm 8 for one vertex, arguments `x, l, s`: compute the proxy edge from `x` to the block of
`s` vertices at positions `l, …, l+s-1` of `ord`, filling the tree `T(x)`. -/
def pruneOneBody : Stmt :=
  let x := Expr.var 0; let l := Expr.var 1; let s := Expr.var 2
  block [
    .parFor 3 0 s (.write (eTree x l 0 (.var 3)) (.read (eOrd (l + .var 3)))),
    .call pPruneLoop [x, l, 0, s]]

/-- `DACPruneEdges` (Algorithm 8), arguments `la, sa, lb, sb`: for all `x` in block `A` concurrently. -/
def pruneEdgesBody : Stmt :=
  .parFor 4 0 (.var 1) (.call pPruneOne [.read (eOrd (.var 0 + .var 4)), .var 2, .var 3])

/-- The body of the loop of `MergeTree` (Algorithm 2, lines 4–5) and the pointer of Appendix D,
arguments `x, l`: compute a mincut for the proxy edge `(x, a)` of `x` and store its pointer and value
in `M(x, a)`, `M(a, x)`. -/
def mergeQueryBody : Stmt :=
  let x := Expr.var 0; let l := Expr.var 1; let a := Expr.var 2
  block [
    .setVar 2 (.read (eTree x l (.read (eRounds x l)) 0)),
    .oracle x a (eCut x a) (eLam x a),
    .write (eTable x a) (eCut x a),
    .write (eTable a x) (eCut x a),
    .rcopy (eLam a x) (eLam x a)]

/-- `MergeTree` (Algorithm 2) without line 7, arguments `la, sa, lb`: the mincut computations for the
proxy edges, concurrently (Appendix E, item 1). Line 7, the computation of `T′`, is not a machine step:
Algorithm 4's cut output never reads a tree. -/
def mergeQueriesBody : Stmt :=
  .parFor 3 0 (.var 1) (.call pMergeQuery [.read (eOrd (.var 0 + .var 3)), .var 2])

/-- One internal node of `T(x)` in `DACAssignMincut` (printed p. 22), arguments `x, l, j, i`: the two
children hold `u, v` and the node holds the survivor `w`; `e` is the other child. If
`λ(w, e) ≤ λ(x, w)` then `M(x, e) = M(w, e)`, else `M(x, e) = M(x, w)`. -/
def assignNodeBody : Stmt :=
  let x := Expr.var 0; let l := Expr.var 1; let j := Expr.var 2; let i := Expr.var 3
  let w := Expr.var 6; let e := Expr.var 7
  block [
    .setVar 4 (.read (eTree x l j (2 * i))),
    .setVar 5 (.read (eTree x l j (2 * i + 1))),
    .setVar 6 (.read (eTree x l (j + 1) i)),
    .setVar 7 (.var 4 + .var 5 - w),
    .ite (.rle (eLam w e) (eLam x w))
      (block [
        .write (eTable x e) (.read (eTable w e)),
        .write (eTable e x) (.read (eTable w e)),
        .rcopy (eLam x e) (eLam w e),
        .rcopy (eLam e x) (eLam w e)])
      (block [
        .write (eTable x e) (.read (eTable x w)),
        .write (eTable e x) (.read (eTable x w)),
        .rcopy (eLam x e) (eLam x w),
        .rcopy (eLam e x) (eLam x w)])]

/-- `DACAssignMincut` for one vertex, arguments `x, l, j, c`: the same rounds as `pruneLoopBody`, but
processed top-down, because the recursive call comes first. -/
def assignLoopBody : Stmt :=
  let x := Expr.var 0; let l := Expr.var 1; let j := Expr.var 2; let c := Expr.var 3
  .ite (.le c 1) .skip <| block [
    .call pAssignLoop [x, l, j + 1, (c + 1) / 2],
    .parFor 4 0 (c / 2) (.call pAssignNode [x, l, j, .var 4])]

/-- `DACAssignMincut`, arguments `la, sa, lb, sb`: for all `x` in block `A` concurrently. -/
def assignBody : Stmt :=
  .parFor 4 0 (.var 1) (.call pAssignLoop [.read (eOrd (.var 0 + .var 4)), .var 2, 0, .var 3])

/-- `AllPairsMincutforSubset` (Algorithm 4, lines 4–18), arguments `lo, hi`: the subset at positions
`lo, …, hi-1` of `ord`. A block of size at most `2` is the base case. Otherwise it is split into
`A` of size `⌊s/2⌋` and `B` of size `⌈s/2⌉`; the two recursive calls run concurrently, and then come
`DACPruneEdges`, the mincut computations of `MergeTree`, and `DACAssignMincut`. -/
def subsetBody : Stmt :=
  let lo := Expr.var 0; let hi := Expr.var 1; let s := Expr.var 2
  let u := Expr.var 3; let v := Expr.var 4; let mid := Expr.var 3
  block [
    .setVar 2 (hi - lo),
    .ite (.le s 1) .skip <|
      .ite (.eq s 2)
        (block [
          .setVar 3 (.read (eOrd lo)),
          .setVar 4 (.read (eOrd (lo + 1))),
          .oracle u v (eCut u v) (eLam u v),
          .write (eTable u v) (eCut u v),
          .write (eTable v u) (eCut u v),
          .rcopy (eLam v u) (eLam u v)])
        (block [
          .setVar 3 (lo + s / 2),
          .parFor 4 0 2 (.ite (.eq (.var 4) 0)
            (.call pSubset [lo, mid]) (.call pSubset [mid, hi])),
          .call pPruneEdges [lo, mid - lo, mid, hi - mid],
          .call pMergeQueries [lo, mid - lo, mid],
          .call pAssign [lo, mid - lo, mid, hi - mid]])]

/-- `DACforAllPairsMincut` (Algorithm 4, lines 1–3): list the vertices in `ord`, then recurse on `V`. -/
def mainBody : Stmt :=
  block [
    .parFor 0 0 N (.write (eOrd (.var 0)) (.var 0)),
    .call pSubset [0, N]]

/-- The proxy edges of Theorem 2 between two blocks, arguments `l₁, s₁, l₂, s₂`: as in line 2 of
Algorithm 2, the smaller block plays the role of `A`. -/
def proxySetBody : Stmt :=
  .ite (.le (.var 1) (.var 3))
    (.call pPruneEdges [.var 0, .var 1, .var 2, .var 3])
    (.call pPruneEdges [.var 2, .var 3, .var 0, .var 1])

end Prog

/-- The program of all procedures above, numbered as in `Prog`. -/
def algorithms : Program :=
  [Prog.elimBody, Prog.pruneNodeBody, Prog.pruneLoopBody, Prog.pruneOneBody, Prog.pruneEdgesBody,
   Prog.mergeQueryBody, Prog.mergeQueriesBody, Prog.assignNodeBody, Prog.assignLoopBody,
   Prog.assignBody, Prog.subsetBody, Prog.mainBody, Prog.proxySetBody]

/-! ## Machine set-up and reading results -/

/-- The machine used for `n` vertices with external procedure `P`. -/
def machine {R : Type} {n : ℕ} (P : Oracle R n) : Machine R n := ⟨wordBound n, P⟩

/-- The memory at the start of a run on `n` vertices: cell `0` holds `n`, everything else is `0`. -/
def initialStore (R : Type) [Zero R] (n : ℕ) : Store R :=
  ⟨fun a => if a = 0 then (n : ℤ) else 0, fun _ => 0⟩

/-- `P` is a correct single-pair procedure for `F`: for all distinct `u, v`, the reported cut is a
`(u, v)`-mincut and the reported value is its `F`-value. -/
def IsMincutOracle {n : ℕ} (F : Finset (Fin n) → ℝ) (P : Oracle ℝ n) : Prop :=
  ∀ u v : Fin n, u ≠ v → IsMincut F u v (P u v).cut ∧ (P u v).value = F (P u v).cut

/-- The cut stored as a Boolean array at address `p`: a cell is "true" when nonzero. -/
def cutAt (n : ℕ) (mem : ℕ → ℤ) (p : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun w => mem (p + w) ≠ 0

/-- Standing facts about memory before a procedure runs: cell `0` holds `n` and all word cells fit
in a machine word. -/
def IsReady (n : ℕ) (σ : Store ℝ) : Prop :=
  σ.mem 0 = n ∧ ∀ a, (σ.mem a).natAbs ≤ wordBound n

/-- `M(u, v)` holds a pointer `p` into the cut store, the array at `p` is a `(u, v)`-mincut, and the
real cell of the pair holds `λ₁(u, v)`. -/
def EntryOK {n : ℕ} (F : Finset (Fin n) → ℝ) (σ : Store ℝ) (u v : Fin n) : Prop :=
  ∃ p : ℕ, σ.mem (tableAddr n u v) = p ∧ cutBase n ≤ p ∧ p + n ≤ roundsBase n ∧
    IsMincut F u v (cutAt n σ.mem p) ∧ σ.rmem (lamAddr n u v) = lam F u v

/-- The invariant of Appendix D (printed p. 22) for the vertex set `S`: for all ordered pairs of
distinct vertices of `S`, `M` points to a mincut. -/
def TableOK {n : ℕ} (F : Finset (Fin n) → ℝ) (σ : Store ℝ) (S : Finset (Fin n)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → EntryOK F σ u v

/-- The final output of Theorem 3, retrieved from the memory `σ`: a mincut pointer and the mincut
value for every ordered pair of distinct vertices. The cut itself is `cutAt` of the pointer. -/
def AllPairsOutput {n : ℕ} (F : Finset (Fin n) → ℝ) (σ : Store ℝ) : Prop :=
  ∀ u v : Fin n, u ≠ v → ∃ p : ℕ, σ.mem (tableAddr n u v) = p ∧
    IsMincut F u v (cutAt n σ.mem p) ∧ σ.rmem (lamAddr n u v) = lam F u v

/-- The mincut cover stored for the pairs of `S`: the cuts that `M` points to. -/
def storedCover {n : ℕ} (σ : Store ℝ) (S : Finset (Fin n)) : Set (Finset (Fin n)) :=
  {C | ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ ∃ p : ℕ, σ.mem (tableAddr n u v) = p ∧ C = cutAt n σ.mem p}

/-- The positions `l, …, l + |L| - 1` of `ord` list the distinct vertices of `L`. -/
def OrdOK {n : ℕ} (σ : Store ℝ) (l : ℕ) (L : List (Fin n)) : Prop :=
  L.Nodup ∧ l + L.length ≤ n ∧ ∀ i (h : i < L.length), σ.mem (ordAddr n (l + i)) = ((L[i] : Fin n) : ℕ)

/-- The two properties of Lemma 6: `(x, a)` is a proxy edge from `x` to `B` for the cover `C`. -/
def IsProxyEdge {n : ℕ} (F : Finset (Fin n) → ℝ) (x : Fin n) (B : Finset (Fin n))
    (C : Set (Finset (Fin n))) (a : Fin n) : Prop :=
  a ∈ B ∧
  (∀ v ∈ B, (∃ D ∈ C, IsMincut F x v D) ∨ ∀ D, IsMincut F x a D → IsMincut F x v D) ∧
  (∀ v ∈ B, lam F x v ≤ lam F x a)

/-- The number of entries of round `j` of `T(x)`: `s`, then repeatedly `⌈c/2⌉` (Algorithm 8, line 5). -/
def roundSize (s : ℕ) : ℕ → ℕ
  | 0 => s
  | j + 1 => (roundSize s j + 1) / 2

/-- The vertex `T(x)` keeps out of `u, v` when `M(u, v) = p`: `u` if the cut at `p` keeps `x` on the
side of `u`, else `v`. -/
def survivor (mem : ℕ → ℤ) (p x u v : ℕ) : ℤ :=
  if (mem (p + x) ≠ 0 ↔ mem (p + u) ≠ 0) then (u : ℤ) else (v : ℤ)

/-- The recursion tree `T(x)` (printed p. 22) of the vertex `x` towards the block `L` at position `l`,
stored in memory up to round `J`: round `0` holds the leaves in the order of `L`; each paired entry of
a round `j < J` produces entry `i` of round `j + 1`, by EliminateTriangle on the cut that `M` points
to; an unpaired last entry is passed on. -/
def TreeUpTo {n : ℕ} (mem : ℕ → ℤ) (x : Fin n) (l : ℕ) (L : List (Fin n)) (J : ℕ) : Prop :=
  (∀ i (h : i < L.length), mem (treeAddr n x l 0 i) = ((L[i] : Fin n) : ℕ)) ∧
  ∀ j < J,
    (∀ i, 2 * i + 1 < roundSize L.length j →
      ∃ (u v : Fin n) (p : ℕ), mem (treeAddr n x l j (2 * i)) = (u : ℕ) ∧
        mem (treeAddr n x l j (2 * i + 1)) = (v : ℕ) ∧ mem (tableAddr n u v) = p ∧
        mem (treeAddr n x l (j + 1) i) = survivor mem p x u v) ∧
    (roundSize L.length j % 2 = 1 → 1 < roundSize L.length j →
      mem (treeAddr n x l (j + 1) (roundSize L.length j / 2)) =
        mem (treeAddr n x l j (roundSize L.length j - 1)))

/-- The complete tree `T(x)`, with `⌈log₂ |L|⌉` rounds above the leaves. -/
def IsRecursionTree {n : ℕ} (mem : ℕ → ℤ) (x : Fin n) (l : ℕ) (L : List (Fin n)) : Prop :=
  TreeUpTo mem x l L (Nat.clog 2 L.length)

/-- The vertex stored at the root of `T(x)`, using the recorded number of rounds. -/
def rootValue (n : ℕ) (mem : ℕ → ℤ) (x l : ℕ) : ℤ :=
  mem (treeAddr n x l (mem (roundsAddr n x l)).toNat 0)

/-- The set `P` reported by the program `pProxySet`: one pair for each vertex of the smaller block. -/
def reportedProxySet {n : ℕ} (mem : ℕ → ℤ) (L₁ : List (Fin n)) (l₁ : ℕ) (L₂ : List (Fin n)) (l₂ : ℕ) :
    Finset (Fin n × Fin n) :=
  if L₁.length ≤ L₂.length then
    (L₁.toFinset ×ˢ L₂.toFinset).filter fun q => rootValue n mem q.1 l₂ = (q.2 : ℕ)
  else
    (L₁.toFinset ×ˢ L₂.toFinset).filter fun q => rootValue n mem q.2 l₁ = (q.1 : ℕ)

/-- The graph on `V₁ ∪ V₂` whose edges are `T₁ ∪ T₂ ∪ P` (Theorem 2). -/
def mergeGraph {n : ℕ} {V₁ V₂ : Finset (Fin n)}
    (T₁ : SimpleGraph {y // y ∈ V₁}) (T₂ : SimpleGraph {y // y ∈ V₂})
    (P : Finset (Fin n × Fin n)) : SimpleGraph {y // y ∈ V₁ ∪ V₂} where
  Adj a b := a ≠ b ∧
    ((∃ (ha : a.1 ∈ V₁) (hb : b.1 ∈ V₁), T₁.Adj ⟨a.1, ha⟩ ⟨b.1, hb⟩) ∨
     (∃ (ha : a.1 ∈ V₂) (hb : b.1 ∈ V₂), T₂.Adj ⟨a.1, ha⟩ ⟨b.1, hb⟩) ∨
     (a.1, b.1) ∈ P ∨ (b.1, a.1) ∈ P)
  symm := ⟨by
    rintro a b ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with ⟨ha, hb, h⟩ | ⟨ha, hb, h⟩ | h | h
    · exact Or.inl ⟨hb, ha, h.symm⟩
    · exact Or.inr (Or.inl ⟨hb, ha, h.symm⟩)
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))⟩
  loopless := ⟨fun a h => h.1 rfl⟩

/-- The only shared locations an internal node `(j, i)` of `T(x)` may read in `DACPruneEdges`, where
its children hold `u, v` and `M(u, v) = p`: cell `0`, the two children in round `j`, the pointer, two
cut cells, and the node's own output cell (read back after this thread wrote it). -/
def pruneNodeReads (n x l j i u v p : ℕ) : Finset Loc :=
  {Loc.word 0, Loc.word (treeAddr n x l j (2 * i)), Loc.word (treeAddr n x l j (2 * i + 1)),
   Loc.word (tableAddr n u v), Loc.word (p + x), Loc.word (p + u),
   Loc.word (treeAddr n x l (j + 1) i)}

/-- The only shared locations an internal node `(j, i)` of `T(x)` may read in `DACAssignMincut`, where
its children hold `w, e` in some order and the node holds `w`: cell `0`, the node and its children,
and the entries of the pairs `(x, w)` and `(w, e)`. -/
def assignNodeReads (n x l j i w e : ℕ) : Finset Loc :=
  {Loc.word 0, Loc.word (treeAddr n x l j (2 * i)), Loc.word (treeAddr n x l j (2 * i + 1)),
   Loc.word (treeAddr n x l (j + 1) i), Loc.word (tableAddr n x w), Loc.word (tableAddr n w e),
   Loc.real (lamAddr n x w), Loc.real (lamAddr n w e)}

/-- The shared locations written by a node of `T(x)` in `DACAssignMincut`, with `e` the pruned vertex. -/
def assignNodeWrites (n x e : ℕ) : Finset Loc :=
  {Loc.word (tableAddr n x e), Loc.word (tableAddr n e x),
   Loc.real (lamAddr n x e), Loc.real (lamAddr n e x)}

/-- The subproblems of Algorithm 4 one level further down: a block `[lo, hi)` of more than two
positions splits as `subsetBody` does, and a smaller block is a base case. -/
def splitBlock (p : ℕ × ℕ) : List (ℕ × ℕ) :=
  if p.2 - p.1 ≤ 2 then [] else
    [(p.1, p.1 + (p.2 - p.1) / 2), (p.1 + (p.2 - p.1) / 2, p.2)]

/-- The subproblems of Algorithm 4 at recursion level `k`, as blocks of positions in `ord`. The
program `mainBody` fills `ord` with the identity, so positions are vertices. -/
def subproblemLevel (n : ℕ) : ℕ → List (ℕ × ℕ)
  | 0 => [(0, n)]
  | k + 1 => (subproblemLevel n k).flatMap splitBlock

end MSTCuts2027.Parallel


