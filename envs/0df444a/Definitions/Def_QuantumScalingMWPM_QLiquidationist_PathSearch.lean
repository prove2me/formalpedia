-- Prove2me | Definitions.Def_QuantumScalingMWPM_QLiquidationist_PathSearch
-- name    : QuantumScalingMWPM_QLiquidationist_PathSearch
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:14:41.052746+00:00
-- url     : https://prove2.me/theorems/88ab06ca-6cbc-42a6-8541-76f977a97b49
-- title:
--   QUANTUMPATHSEARCH (Algorithm 1), CONTRACTSEARCHBLOSSOM (Algorithm 2) and QSEARCHONE under the search accounting
-- statement:
--   This module defines the quantum part of FREEVERTEXREDUCTION as transition systems with explicit costs.
--
--   **Algorithm 1 (QUANTUMPATHSEARCH, p. 14).** The state carries the data of Figure 4 (p. 8):
--   1. the search-local family $\Omega'$, which is $\Omega$ followed by temporary blossoms, with $\mathrm{ROOTB}[v]$ the root blossom of $v$ in $\Omega'$;
--   2. the labels $\mathrm{UIO}$, the times $\mathrm{OutTime}$ and the predecessor edges $\mathrm{predEdge}$, the last two indexed by root blossoms;
--   3. the DFS stack $S$, the output $\Psi$ and the counter $t$.
--
--   The outer loop takes every free unlabeled vertex $r$ in turn (any order), labels $V(\mathrm{ROOTB}[r])$ OUT and pushes it. While the stack is nonempty, $\mathrm{GROVERSEARCH}(v)$ is called for its top $v$. It searches $v$'s adjacency list for a neighbour $u$ with $y(v)+y(u)=w(u,v)-2$ that is either UNLABELED (GROWEVENT) or OUT with $\mathrm{OutTime}[\mathrm{ROOTB}[u]]>\mathrm{OutTime}[\mathrm{ROOTB}[v]]$ (BLOSSOMEVENT); this is Figure 5 (p. 9).
--   1. If no such neighbour exists, the call returns $\bot$; $v$ is popped and is now *completely scanned*.
--   2. A GROWEVENT labels $B_u$ IN. Then either an augmenting path is found: it is reconstructed by following $\mathrm{predEdge}$, its temporary blossoms are expanded along their stored cycles, it is added to $\Psi$, and the while loop breaks. Or the tight matched edge out of $B_u$ makes a new OUT blossom.
--   3. A BLOSSOMEVENT runs **Algorithm 2** (CONTRACTSEARCHBLOSSOM, p. 15) on the search-tree path $B_v=C_0,\dots,C_{2k}=B_u$. A new temporary blossom with children $C_0,\dots,C_{2k}$ and cycle edges $\mathrm{predEdge}[C_1],\dots,\mathrm{predEdge}[C_{2k}],(u,v)$ inherits $\mathrm{predEdge}$ and $\mathrm{OutTime}$ of $C_0$. The IN children become OUT and are pushed for $j=k,\dots,1$.
--
--   **Search accounting.** A GROVERSEARCH call over the $d_v$ neighbours of $v$ with $k$ marked ones may return *any* marked neighbour, and returns $\bot$ exactly when $k=0$. It is charged $\lceil\sqrt{d_v/k}\rceil$, or $\lceil\sqrt{d_v}\rceil$ when $k=0$, as Lemma 1 bounds a search. Every other elementary operation costs one unit: each loop iteration, each vertex labelled, pushed, relabelled or enumerated, and each edge of a reconstructed path. The union-by-size relabelling of Algorithm 2 costs $\sum_{i\neq\max}|V(C_i)|$. Statements about these procedures hold for every run, that is, conditioned on the correctness of every search.
--
--   **QSEARCHONE (Figure 3; §§2.3, 3.3–3.5).**
--   1. Task 1 is a run of Algorithm 1.
--   2. Task 2 augments along the lifts of $\Psi$, each charged its length (Fact 1).
--   3. Task 3 is a fresh run of Algorithm 1 on the new matching. Its blossoms are promoted ($\Omega\leftarrow\Omega'$, $z(B)\leftarrow0$ on new blossoms) and its labels are retained.
--   4. Task 4 adjusts $y$ by $\mp1$ on OUT/IN vertices and $z$ by $\pm2$ on OUT/IN root blossoms.
--   5. Task 5 dissolves the root blossoms with $z=0$.
--
--   Tasks 4–5 are charged one unit per vertex, per blossom and per child visited in one traversal.
--
--   **Formalization Note** A `foreach` over a blossom follows an enumeration order `ord`, and the statements quantify over all orders. If the predecessor path of a BLOSSOMEVENT does not lead back to $B_v$ along an odd number of blossoms, the run is stuck; Lemma 2's progress clause excludes this.
-- source:
--   Kourosh Mirsohi, Sandy Irani, Michael Goodrich, STOC 2027 submission #842 (October 2026), Algorithm 1, p. 14; Algorithm 2, p. 15; Figures 3–5, pp. 7–9; §2.3, pp. 8–12; §3.4, pp. 21–22; §3.5, p. 22; Lemma 1, p. 11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/842.pdf

import Mathlib
import Definitions.Def_QuantumScalingMWPM_QLiquidationist_Blossom

/-!
# QUANTUMPATHSEARCH (Algorithm 1), CONTRACTSEARCHBLOSSOM (Algorithm 2) and QSEARCHONE

Kourosh Mirsohi, Sandy Irani, Michael Goodrich, STOC 2027 submission #842 (October 2026):
Algorithm 1 (p. 14), Algorithm 2 (p. 15), Figure 4 (p. 8, data), Figure 5 (p. 9, the GROVERSEARCH
predicate), §2.3 (pp. 8–12), §3.4 (pp. 21–22, Task 3), §3.5 (p. 22, Tasks 4–5), Lemma 1 (p. 11).

**Search accounting.** The running-time and correctness statements about these procedures are
"conditioned on the correctness of all calls to GROVERSEARCH" (Lemmas 3, 8) and charge a search
by Lemma 1 (Lemma 2). Accordingly the procedures are given as a nondeterministic transition
system `Alg1Step`: a call `GROVERSEARCH(v)` over the adjacency list of `v` (length `N = d_v`) with
`k` marked neighbours (Figure 5 predicate, evaluated at the moment of the call) returns any marked
neighbour if `k ≥ 1` and `⊥` iff `k = 0`, and is charged `⌈√(N/k)⌉` if `k ≥ 1` and `⌈√N⌉` if
`k = 0`. Every other operation is charged one unit per elementary step of the pseudocode: one per
loop iteration and per vertex labelled, pushed, relabelled or enumerated, one per edge of a
reconstructed path. Statements quantify over every run, i.e. every resolution of the
nondeterminism.

**State (Figure 4).** `fam` is the search-local family `Ω′` (`Ω` followed by temporary records),
`ROOTB[v] = rootSet fam v`; `uio`, `outT` (OutTime, indexed by root blossoms), `pred` (predEdge,
indexed by root blossoms), the DFS stack `stk` (head = top), the output `psi` (`Ψ`), the counter
`t`; `visited` records the free vertices the outer `foreach` (line 8) has already considered (any
order); `scanned` the vertices from which a search returned `⊥` ("completely scanned", p. 16).

**Formalization Note.** `ord S` is the order in which a `foreach x ∈ V(S)` loop enumerates the
blossom `S`; every statement holds for every enumeration order (`ValidOrd`). The union-by-size
relabelling of Algorithm 2 (lines 9–15) is charged its true work `Σ_{i ≠ max} |V(Cᵢ)|`, while
`ROOTB` is read from `fam` (so the renaming of labels is not modelled). CONTRACTSEARCHBLOSSOM is
enabled only if following `predEdge` from `B_u` reaches `B_v` along an odd number of blossoms
(Corollary 3.1); otherwise the run is stuck, which the progress clause of Lemma 2 excludes.
Path reconstruction (lines 31–32) follows `predEdge` from `B_u` to the free root and expands
every temporary blossom of `Ω′ \ Ω` along its stored defining cycle (`liftPath` stopped at the
blossoms of `Ω`); the path is stored from the free root to `B_u`.
-/

namespace QuantumScalingMWPM.QLiquidationist

open scoped Classical

variable {n : ℕ}

/-- Search labels (`UIO`). -/
inductive Lbl where
  | unl
  | inn
  | out
  deriving DecidableEq

/-- An enumeration order for `foreach` loops over vertex sets: `ord S` lists `S` without
repetition. -/
def ValidOrd (ord : Finset (Fin n) → List (Fin n)) : Prop :=
  ∀ S, (ord S).Nodup ∧ (ord S).toFinset = S

/-- The state of QUANTUMPATHSEARCH (see the module docstring). -/
structure Alg1State (n : ℕ) where
  fam : Family n
  uio : Fin n → Lbl
  outT : Finset (Fin n) → ℕ
  pred : Finset (Fin n) → Option (Fin n × Fin n)
  stk : List (Fin n)
  psi : List (List (Fin n × Fin n))
  t : ℕ
  visited : Finset (Fin n)
  inner : Bool
  done : Bool
  scanned : Finset (Fin n)
  cost : ℕ

/-- Total size `Σ_B |children(B)|` of a family (the cost of copying it). -/
def famSize (Ω : Family n) : ℕ := (Ω.map fun B => B.kids.length).sum

/-- Lines 1–7: `Ω′ ← Ω`, ROOTB, all labels UNLABELED, all predEdge `⊥`, `Ψ ← ∅`, `t ← 0`. -/
def alg1Init (Ω : Family n) : Alg1State n where
  fam := Ω
  uio := fun _ => .unl
  outT := fun _ => 0
  pred := fun _ => none
  stk := []
  psi := []
  t := 0
  visited := ∅
  inner := false
  done := false
  scanned := ∅
  cost := 1 + 3 * n + famSize Ω

/-- The number `d_v` of neighbours of `v`. -/
noncomputable def deg (G : SimpleGraph (Fin n)) (v : Fin n) : ℕ := (G.neighborSet v).ncard

/-- Figure 5: the neighbours `u` of `v` with `y(v) + y(u) = w(u, v) − 2` and either GROWEVENT
(`UIO[u] = UNLABELED`) or BLOSSOMEVENT (`UIO[u] = OUT` and
`OutTime[ROOTB[u]] > OutTime[ROOTB[v]]`). -/
noncomputable def marked (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℤ) (y : Fin n → ℤ)
    (s : Alg1State n) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun u => G.Adj v u ∧ y v + y u = w s(u, v) - 2 ∧
    (s.uio u = .unl ∨
      (s.uio u = .out ∧ s.outT (rootSet s.fam u) > s.outT (rootSet s.fam v)))

/-- The charge of one GROVERSEARCH call over a list of length `N` with `k` marked items
(Lemma 1): `⌈√(N/k)⌉` if `k ≥ 1`, `⌈√N⌉` if `k = 0`. -/
noncomputable def searchCost (N k : ℕ) : ℕ :=
  if k = 0 then ⌈Real.sqrt N⌉₊ else ⌈Real.sqrt ((N : ℝ) / k)⌉₊

/-- Push the vertices of `S` (in the order `ord S`) onto the stack. -/
def pushSet (ord : Finset (Fin n) → List (Fin n)) (S : Finset (Fin n)) (stk : List (Fin n)) :
    List (Fin n) :=
  (ord S).reverse ++ stk

/-- Relabel every vertex of `S` with `ℓ`. -/
def relabel (uio : Fin n → Lbl) (S : Finset (Fin n)) (ℓ : Lbl) : Fin n → Lbl :=
  fun x => if x ∈ S then ℓ else uio x

/-- Follow `predEdge` from the root blossom `B` to the root of the search tree: the edges
`predEdge[B], predEdge[parent B], …` until `⊥` (`fuel` bounds the depth). -/
def chaseEdges (fam : Family n) (pred : Finset (Fin n) → Option (Fin n × Fin n)) :
    ℕ → Finset (Fin n) → List (Fin n × Fin n)
  | 0, _ => []
  | f + 1, B => match pred B with
    | some e => e :: chaseEdges fam pred f (rootSet fam e.1)
    | none => []

/-- Follow `predEdge` from `B` up to `target`: the list of root blossoms `B = C_{last}, …, C₀ =
target` in the order `C₀, …, C_{last}`, if `target` is reached within `fuel` steps. -/
def chaseTo (fam : Family n) (pred : Finset (Fin n) → Option (Fin n × Fin n))
    (target : Finset (Fin n)) : ℕ → Finset (Fin n) → Option (List (Finset (Fin n)))
  | 0, _ => none
  | f + 1, B =>
    if B = target then some [B] else
    match pred B with
    | some e => (chaseTo fam pred target f (rootSet fam e.1)).map fun l => l ++ [B]
    | none => none

/-- The stop predicate for line 32: the blossoms of `Ω` (and single vertices) are not expanded. -/
def hStop (Ω : Family n) : Finset (Fin n) → Bool :=
  fun S => decide (S.card ≤ 1 ∨ S ∈ Ω.map BRec.verts)

/-- Lines 26–43 after a GROWEVENT reaching `B_u`: for `x ∈ V(B_u)` in the order of the list:
if `M[x] = ⊥`, reconstruct the augmenting path (lines 31–32), add it to `Ψ` and break the while
loop; else if `M[x] = q` with `ROOTB[q] ≠ ROOTB[x]` and `y(x) + y(q) = w(x, q)`, make `B_q =
ROOTB[q]` a new OUT blossom (lines 37–43). -/
def growLoop (w : Sym2 (Fin n) → ℤ) (M : Mate n) (y : Fin n → ℤ) (Ω : Family n)
    (ord : Finset (Fin n) → List (Fin n)) (Bu : Finset (Fin n)) :
    List (Fin n) → Alg1State n → Alg1State n
  | [], s => s
  | x :: xs, s =>
    match M x with
    | none =>
      let pbar := (chaseEdges s.fam s.pred (n + 1) Bu).reverse
      let P := liftPath s.fam (hStop Ω) pbar
      { s with psi := s.psi ++ [P], inner := false,
               cost := s.cost + 1 + pbar.length + P.length }
    | some q =>
      if rootSet s.fam q ≠ rootSet s.fam x ∧ y x + y q = w s(x, q) then
        let Bq := rootSet s.fam q
        growLoop w M y Ω ord Bu xs
          { s with pred := Function.update s.pred Bq (some (x, q)), t := s.t + 1,
                   outT := Function.update s.outT Bq (s.t + 1), uio := relabel s.uio Bq .out,
                   stk := pushSet ord Bq s.stk, cost := s.cost + 1 + 2 * Bq.card }
      else growLoop w M y Ω ord Bu xs { s with cost := s.cost + 1 }

/-- Algorithm 2, CONTRACTSEARCHBLOSSOM(v, u), given the search-tree path `C₀ = B_v, …, C₂ₖ = B_u`:
a new temporary blossom with children `C₀, …, C₂ₖ` and defining cycle edges
`predEdge[C₁], …, predEdge[C₂ₖ], (u, v)`, base child `C₀`, inheriting predEdge and OutTime of `C₀`;
the IN children `C₂ⱼ₋₁` become OUT and are pushed for `j = k, …, 1`. -/
def contract (ord : Finset (Fin n) → List (Fin n)) (v u : Fin n) (cs : List (Finset (Fin n)))
    (s : Alg1State n) : Alg1State n :=
  let L := cs.length
  let es := ((List.range (L - 1)).map fun i =>
    (s.pred (cs.getD (i + 1) ∅)).getD (u, v)) ++ [(u, v)]
  let B : BRec n := ⟨cs, es⟩
  let C0 := cs.getD 0 ∅
  let total := (cs.map Finset.card).sum
  let biggest := (cs.map Finset.card).foldr max 0
  let ins := ((List.range (L / 2)).map fun j => cs.getD (2 * j + 1) ∅)
  { s with fam := s.fam ++ [B],
           pred := Function.update s.pred B.verts (s.pred C0),
           outT := Function.update s.outT B.verts (s.outT C0),
           uio := fun x => if ∃ C ∈ ins, x ∈ C then .out else s.uio x,
           stk := ins.foldr (fun C stk => pushSet ord C stk) s.stk,
           cost := s.cost + L + (total - biggest) + (ins.map Finset.card).sum }

/-- One step of QUANTUMPATHSEARCH(G, M, y, z, Ω) (Algorithm 1), under the search accounting. -/
inductive Alg1Step (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℤ) (M : Mate n) (y : Fin n → ℤ)
    (Ω : Family n) (ord : Finset (Fin n) → List (Fin n)) : Alg1State n → Alg1State n → Prop
  /-- Line 8: the next vertex `r` of the outer `foreach`, a free UNLABELED vertex: lines 9–15. -/
  | start (s : Alg1State n) (r : Fin n) :
      s.inner = false → s.done = false → r ∉ s.visited → M r = none → s.uio r = .unl →
      Alg1Step G w M y Ω ord s
        { s with visited := insert r s.visited, inner := true,
                 stk := pushSet ord (rootSet s.fam r) [], t := s.t + 1,
                 outT := Function.update s.outT (rootSet s.fam r) (s.t + 1),
                 uio := relabel s.uio (rootSet s.fam r) .out,
                 cost := s.cost + 1 + 2 * (rootSet s.fam r).card }
  /-- Line 8: a vertex that is not a free UNLABELED vertex is skipped. -/
  | skip (s : Alg1State n) (r : Fin n) :
      s.inner = false → s.done = false → r ∉ s.visited → ¬ (M r = none ∧ s.uio r = .unl) →
      Alg1Step G w M y Ω ord s { s with visited := insert r s.visited, cost := s.cost + 1 }
  /-- Line 47: the outer loop is exhausted; return `Ψ`. -/
  | finish (s : Alg1State n) :
      s.inner = false → s.done = false → s.visited = Finset.univ →
      Alg1Step G w M y Ω ord s { s with done := true, cost := s.cost + 1 }
  /-- Line 16: the stack is empty; the while loop ends. -/
  | empty (s : Alg1State n) :
      s.inner = true → s.stk = [] →
      Alg1Step G w M y Ω ord s { s with inner := false, cost := s.cost + 1 }
  /-- Lines 17–21: GROVERSEARCH(v) returns `⊥` (no marked neighbour); pop `v`. -/
  | fail (s : Alg1State n) (v : Fin n) (rest : List (Fin n)) :
      s.inner = true → s.stk = v :: rest → marked G w y s v = ∅ →
      Alg1Step G w M y Ω ord s
        { s with stk := rest, scanned := insert v s.scanned,
                 cost := s.cost + 1 + searchCost (deg G v) 0 }
  /-- Lines 23–43: GROVERSEARCH(v) returns an UNLABELED marked neighbour `u` (GROWEVENT). -/
  | grow (s : Alg1State n) (v u : Fin n) (rest : List (Fin n)) :
      s.inner = true → s.stk = v :: rest → u ∈ marked G w y s v → s.uio u = .unl →
      Alg1Step G w M y Ω ord s
        (growLoop w M y Ω ord (rootSet s.fam u) (ord (rootSet s.fam u))
          { s with pred := Function.update s.pred (rootSet s.fam u) (some (v, u)),
                   uio := relabel s.uio (rootSet s.fam u) .inn,
                   cost := s.cost + 1 + searchCost (deg G v) (marked G w y s v).card +
                     (rootSet s.fam u).card })
  /-- Lines 45–46 and Algorithm 2: GROVERSEARCH(v) returns an OUT marked neighbour `u`
  (BLOSSOMEVENT); the search-tree path from `B_u` up to `B_v` has `2k + 1` blossoms. -/
  | blossom (s : Alg1State n) (v u : Fin n) (rest : List (Fin n)) (cs : List (Finset (Fin n))) :
      s.inner = true → s.stk = v :: rest → u ∈ marked G w y s v → s.uio u = .out →
      chaseTo s.fam s.pred (rootSet s.fam v) (n + 1) (rootSet s.fam u) = some cs →
      Odd cs.length →
      Alg1Step G w M y Ω ord s
        (contract ord v u cs
          { s with cost := s.cost + 1 + searchCost (deg G v) (marked G w y s v).card })

/-- `s` is a state of some run of QUANTUMPATHSEARCH on `(G, w, M, y, Ω)`. -/
def Alg1Reach (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℤ) (M : Mate n) (y : Fin n → ℤ)
    (Ω : Family n) (ord : Finset (Fin n) → List (Fin n)) (s : Alg1State n) : Prop :=
  Relation.ReflTransGen (Alg1Step G w M y Ω ord) (alg1Init Ω) s

/-- `s` is a final state (line 47 reached) of some run of QUANTUMPATHSEARCH. -/
def Alg1Final (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℤ) (M : Mate n) (y : Fin n → ℤ)
    (Ω : Family n) (ord : Finset (Fin n) → List (Fin n)) (s : Alg1State n) : Prop :=
  Alg1Reach G w M y Ω ord s ∧ s.done = true

/-! ### QSEARCHONE (Figure 3; §§2.3, 3.3–3.5) -/

/-- The cost of Task 2: lifting each path of `Ψ` to `G` (charged its lifted length, Fact 1) and
augmenting along it. -/
def task2Cost (Ω : Family n) (Ψ : List (List (Fin n × Fin n))) : ℕ :=
  (Ψ.map fun P => 1 + (liftG Ω P).length).sum

/-- The result of one run of QSEARCHONE, with the cost of its parts. -/
structure QSOneResult (n : ℕ) where
  M : Mate n
  fam : Family n
  y : Fin n → ℤ
  z : Finset (Fin n) → ℤ
  cost1 : ℕ
  cost2 : ℕ
  cost3 : ℕ
  cost45 : ℕ

/-- The total cost of a run of QSEARCHONE. -/
def QSOneResult.cost (r : QSOneResult n) : ℕ := r.cost1 + r.cost2 + r.cost3 + r.cost45

/-- **QSEARCHONE** (Figure 3, §§2.3, 3.4, 3.5). Task 1: a run of Algorithm 1 on `(M, Ω)` ends with
`Ψ`. Task 2: augment along the lifts of `Ψ` (blossoms re-based). Task 3: a fresh run of Algorithm 1
on the new matching and the re-based family; its temporary blossoms are promoted (`Ω ← Ω′`,
`z(B) ← 0` on the new ones, cost `1 + #new`), its final UIO labels are retained. Task 4: `y(v)`
`∓ 1` on OUT/IN vertices, `z(B) ± 2` on OUT/IN root blossoms. Task 5: root blossoms with `z = 0`
are dissolved and ROOTB is rebuilt by one traversal. Tasks 4–5 are charged
`(1 + n + |Ω′|) + (1 + n + |Ω′| + Σ children)`. -/
def QSearchOne (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℤ)
    (ord : Finset (Fin n) → List (Fin n)) (M : Mate n) (Ω : Family n) (y : Fin n → ℤ)
    (z : Finset (Fin n) → ℤ) (r : QSOneResult n) : Prop :=
  ∃ s₁ s₃ : Alg1State n,
    Alg1Final G w M y Ω ord s₁ ∧
    let M₂ := augmentAll M (s₁.psi.map (liftG Ω))
    let Ω₂ := rebase M₂ Ω
    Alg1Final G w M₂ y Ω₂ ord s₃ ∧
    let news := s₃.fam.drop Ω₂.length
    let isOut : Fin n → Prop := fun v => s₃.uio v = .out
    let isIn : Fin n → Prop := fun v => s₃.uio v = .inn
    let z₄ := adjustZ s₃.fam (zAfterPromotion news z) isOut isIn
    r.M = M₂ ∧ r.y = adjustY y isOut isIn ∧ r.z = z₄ ∧ r.fam = dissolveZero s₃.fam z₄ ∧
    r.cost1 = s₁.cost ∧ r.cost2 = task2Cost Ω s₁.psi ∧
    r.cost3 = s₃.cost + 1 + news.length ∧
    r.cost45 = (1 + n + s₃.fam.length) + (1 + n + s₃.fam.length + famSize s₃.fam)

/-! ### Sanity checks -/

/-- The empty search: on the empty graph with no vertices the outer loop finishes at once. -/
example (y : Fin 0 → ℤ) (w : Sym2 (Fin 0) → ℤ) (M : Mate 0) (ord : Finset (Fin 0) → List (Fin 0)) :
    Alg1Step ⊥ w M y [] ord (alg1Init []) { alg1Init [] with done := true, cost := 2 } := by
  have h := Alg1Step.finish (G := ⊥) (w := w) (M := M) (y := y) (Ω := []) (ord := ord)
    (alg1Init []) rfl rfl (by ext v; exact v.elim0)
  simpa [alg1Init, famSize] using h

/-- The search charge is `⌈√(N/k)⌉`: one marked item among four costs `2`. -/
example : searchCost 4 1 = 2 := by
  simp [searchCost, show Real.sqrt 4 = 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]

end QuantumScalingMWPM.QLiquidationist


