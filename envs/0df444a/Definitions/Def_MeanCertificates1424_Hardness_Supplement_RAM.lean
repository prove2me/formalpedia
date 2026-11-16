-- Prove2me | Definitions.Def_MeanCertificates1424_Hardness_Supplement_RAM
-- name    : MeanCertificates1424_Hardness_Supplement_RAM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:53:42.803706+00:00
-- url     : https://prove2.me/theorems/ac514fb4-6185-40ab-ac92-57e634eabb76
-- title:
--   Unit-cost arithmetic machine, input encodings, weighted distances, source lists and nice tree decompositions
-- statement:
--   The paper's running times "count exact arithmetic operations and comparisons on the numerical input" (§2). This file fixes that model as a **unit-cost real RAM**. A program is a finite list of instructions with rational literals: natural-number cells support constants, addition, truncated subtraction, indirect load and store; real cells support constants, $+,-,\times,\div$, indirect load and store; there are comparisons with conditional jumps on both kinds of cells, an unconditional jump, an oracle instruction returning $f_v(t)$ for a supplied family of functions (used only for separable objectives), and halt. Every executed instruction costs one unit, and the **space** of a run is the number of distinct cells it accesses. There is no conversion from reals to naturals, so real numbers cannot serve as packed words. A run within $T$ steps and $S$ cells ends in a halting configuration whose memory holds the output.
--
--   Inputs are given as adjacency lists (degree followed by sorted neighbours for every vertex), the budget and audit indicators in natural cells, and $L,\epsilon$, the reports, weights and audit intervals in real cells. The certificate output convention is: cell $I[0]=1$ iff $C_I(y)\neq\emptyset$, and then $R[0]=\ell$, $R[1]=u$ and two feasible extremal fields attaining them.
--
--   The file also defines shortest-path distances $d_{\mathrm{len}}$ for nonnegative edge lengths, source lists (location, real initial value, identity) and their first $q$ cones $(\text{init}+d(\text{loc},v),\text{identity})$ in lexicographic order, the output layout of list-per-vertex algorithms, and **nice tree decompositions** supplied as input: a rooted tree of leaf, introduce, forget and join nodes in which children have smaller indices, root and leaf bags are empty, every vertex and edge is covered, the nodes containing a vertex form a subtree, and the width is exactly $\omega$ (largest bag of size $\omega+1$).
--
--   This model is the yardstick of Lemmas 4.5–4.6 and Theorems 4.8, 5.2, 7.1, 7.2 and A.2.
--
--   **Formalization Note** Division by zero returns $0$ (Lean's convention); no algorithm needs it. Bit complexity is not measured (the paper treats it separately in Appendix F).
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Section 2, Representation (printed p.6, PDF p.8); §4.1, §5 (printed pp.14–17, PDF pp.16–19); Remark 6.5 (printed p.21, PDF p.23)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_General

set_option autoImplicit false

namespace MeanCertificates1424.Hardness.Supplement

/-! # Arithmetic computation model (printed p.6, PDF p.8: "Running times count exact
arithmetic operations and comparisons on the numerical input")

A unit-cost real RAM: natural-number cells `I[·]` (counters, indices, pointers, identities)
and real cells `R[·]` (numerical data). Every executed instruction costs one unit, so
arithmetic, comparisons, branches and memory moves are all charged. Integer arithmetic is
only addition and truncated subtraction, and there is no real-to-integer conversion, so
reals cannot be used as packed words. Programs are finite lists of instructions with
rational literals, fixed before every input. Deques, heaps, balanced search trees and
lists are programmed with these instructions. -/

inductive Instr
  /-- `I[d] := c` -/
  | iconst (d c : ℕ)
  /-- `I[d] := I[a] + I[b]` -/
  | iadd (d a b : ℕ)
  /-- `I[d] := I[a] − I[b]` (truncated at 0) -/
  | isub (d a b : ℕ)
  /-- `I[d] := I[I[p]]` -/
  | iload (d p : ℕ)
  /-- `I[I[p]] := I[s]` -/
  | istore (p s : ℕ)
  /-- `R[d] := c` for a rational literal `c` -/
  | rconst (d : ℕ) (c : ℚ)
  /-- `R[d] := R[a] + R[b]` -/
  | radd (d a b : ℕ)
  /-- `R[d] := R[a] − R[b]` -/
  | rsub (d a b : ℕ)
  /-- `R[d] := R[a] · R[b]` -/
  | rmul (d a b : ℕ)
  /-- `R[d] := R[a] / R[b]` (Lean's convention `t / 0 = 0`) -/
  | rdiv (d a b : ℕ)
  /-- `R[d] := R[I[p]]` -/
  | rload (d p : ℕ)
  /-- `R[I[p]] := R[s]` -/
  | rstore (p s : ℕ)
  /-- `R[d] := f_{I[p]}(R[s])`: one exact evaluation of the supplied function of vertex
  `I[p]` (used only for separable objectives, Corollary 4.10) -/
  | oracle (d p s : ℕ)
  /-- if `I[a] ≤ I[b]` then jump to `t` -/
  | ijle (a b t : ℕ)
  /-- if `R[a] ≤ R[b]` then jump to `t` -/
  | rjle (a b t : ℕ)
  /-- jump to `t` -/
  | jmp (t : ℕ)
  | halt

abbrev Program := List Instr

/-- A configuration; `used` records every cell accessed so far (`false` = integer cell,
`true` = real cell). No claimed runtime or correctness is stored. -/
structure Cfg where
  pc : ℕ
  imem : ℕ → ℕ
  rmem : ℕ → ℝ
  used : Finset (Bool × ℕ)

/-- One charged step. A halted configuration, or a program counter outside the program,
is left unchanged. `f v t` is the exact value `f_v(t)` returned by `oracle`. -/
noncomputable def step (P : Program) (f : ℕ → ℝ → ℝ) (c : Cfg) : Cfg :=
  match P[c.pc]? with
  | none => c
  | some .halt => c
  | some (.iconst d k) =>
    ⟨c.pc + 1, Function.update c.imem d k, c.rmem, insert (false, d) c.used⟩
  | some (.iadd d a b) =>
    ⟨c.pc + 1, Function.update c.imem d (c.imem a + c.imem b), c.rmem, insert (false, d) (insert (false, a) (insert (false, b) c.used))⟩
  | some (.isub d a b) =>
    ⟨c.pc + 1, Function.update c.imem d (c.imem a - c.imem b), c.rmem, insert (false, d) (insert (false, a) (insert (false, b) c.used))⟩
  | some (.iload d p) =>
    ⟨c.pc + 1, Function.update c.imem d (c.imem (c.imem p)), c.rmem, insert (false, d) (insert (false, p) (insert (false, c.imem p) c.used))⟩
  | some (.istore p s) =>
    ⟨c.pc + 1, Function.update c.imem (c.imem p) (c.imem s), c.rmem, insert (false, s) (insert (false, p) (insert (false, c.imem p) c.used))⟩
  | some (.rconst d k) =>
    ⟨c.pc + 1, c.imem, Function.update c.rmem d (k : ℝ), insert (true, d) c.used⟩
  | some (.radd d a b) =>
    ⟨c.pc + 1, c.imem, Function.update c.rmem d (c.rmem a + c.rmem b), insert (true, d) (insert (true, a) (insert (true, b) c.used))⟩
  | some (.rsub d a b) =>
    ⟨c.pc + 1, c.imem, Function.update c.rmem d (c.rmem a - c.rmem b), insert (true, d) (insert (true, a) (insert (true, b) c.used))⟩
  | some (.rmul d a b) =>
    ⟨c.pc + 1, c.imem, Function.update c.rmem d (c.rmem a * c.rmem b), insert (true, d) (insert (true, a) (insert (true, b) c.used))⟩
  | some (.rdiv d a b) =>
    ⟨c.pc + 1, c.imem, Function.update c.rmem d (c.rmem a / c.rmem b), insert (true, d) (insert (true, a) (insert (true, b) c.used))⟩
  | some (.rload d p) =>
    ⟨c.pc + 1, c.imem, Function.update c.rmem d (c.rmem (c.imem p)), insert (true, d) (insert (false, p) (insert (true, c.imem p) c.used))⟩
  | some (.rstore p s) =>
    ⟨c.pc + 1, c.imem, Function.update c.rmem (c.imem p) (c.rmem s), insert (true, s) (insert (false, p) (insert (true, c.imem p) c.used))⟩
  | some (.oracle d p s) =>
    ⟨c.pc + 1, c.imem, Function.update c.rmem d (f (c.imem p) (c.rmem s)), insert (true, d) (insert (false, p) (insert (true, s) c.used))⟩
  | some (.ijle a b t) =>
    ⟨if c.imem a ≤ c.imem b then t else c.pc + 1, c.imem, c.rmem, insert (false, a) (insert (false, b) c.used)⟩
  | some (.rjle a b t) =>
    ⟨if c.rmem a ≤ c.rmem b then t else c.pc + 1, c.imem, c.rmem, insert (true, a) (insert (true, b) c.used)⟩
  | some (.jmp t) => ⟨t, c.imem, c.rmem, c.used⟩

/-- The input: natural numbers in `I[0], I[1], …` and reals in `R[0], R[1], …`;
every other cell is `0`. -/
noncomputable def initCfg (ins : List ℕ) (rs : List ℝ) : Cfg where
  pc := 0
  imem := fun i => ins.getD i 0
  rmem := fun i => rs.getD i 0
  used := ∅

def Halted (P : Program) (c : Cfg) : Prop := P[c.pc]? = some Instr.halt

/-- `P` with oracle `f`, started on `(ins, rs)`, halts within `T` steps in configuration
`fin`, having accessed at most `S` distinct cells. Output is read from `fin`'s memory. -/
def RunsWithin (P : Program) (f : ℕ → ℝ → ℝ) (ins : List ℕ) (rs : List ℝ) (T S : ℕ)
    (fin : Cfg) : Prop :=
  ∃ t ≤ T, (step P f)^[t] (initCfg ins rs) = fin ∧ Halted P fin ∧ fin.used.card ≤ S

/-! ## Input encodings (adjacency lists; binary layout fixed here) -/

/-- Adjacency lists: `n`, then for each vertex `v = 0,…,n−1` its degree followed by its
neighbours in increasing order. Size `O(n + |E|)`. -/
noncomputable def encAdj {n : ℕ} (G : SimpleGraph (Fin n)) : List ℕ := by
  classical
  exact n :: (List.finRange n).flatMap fun v =>
    let N := (Finset.univ.filter (G.Adj v)).sort (· ≤ ·)
    N.length :: N.map Fin.val

/-- Number of (undirected) edges. -/
noncomputable def numEdges {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact G.edgeFinset.card

/-- Integer part: adjacency lists, the budget, audit indicators.
Real part: `L, ε`, reports, weights, audit lower and upper ends (`0` off `Q`). -/
noncomputable def encInst (I : Inst) : List ℕ × List ℝ := by
  classical
  exact (encAdj I.graph ++ [I.budget] ++ List.ofFn fun v => if v ∈ I.audits then 1 else 0,
    [I.lip, I.noise] ++ List.ofFn I.reports ++ List.ofFn I.weights ++
      List.ofFn (fun v => if v ∈ I.audits then I.lo v else 0) ++
      List.ofFn (fun v => if v ∈ I.audits then I.hi v else 0))

/-- Output convention for certificate algorithms: `I[0] = 1` iff the class is nonempty;
then `R[0] = ℓ`, `R[1] = u`, `R[2+v] = x⁻_v`, `R[2+n+v] = x⁺_v`. -/
def lowField (n : ℕ) (c : Cfg) : Fin n → ℝ := fun v => c.rmem (2 + v.val)

def upField (n : ℕ) (c : Cfg) : Fin n → ℝ := fun v => c.rmem (2 + n + v.val)

/-- Correct certificate output for `I`: infeasibility reported exactly when `CI` is empty;
otherwise the two endpoints and two feasible extremal fields attaining them. -/
def CertOutput (I : Inst) (c : Cfg) : Prop :=
  (c.imem 0 = 1 ↔ (CI I).Nonempty) ∧
  ((CI I).Nonempty →
    lowField I.n c ∈ CI I ∧ upField I.n c ∈ CI I ∧
    (c.rmem 0 : EReal) = lower I ∧ (c.rmem 1 : EReal) = upper I ∧
    wmean I (lowField I.n c) = c.rmem 0 ∧ wmean I (upField I.n c) = c.rmem 1)

/-! ## Weighted distances and source systems (Lemmas 4.5, 4.6) -/

/-- Shortest-path distance with nonnegative edge lengths `len u v` (symmetric). -/
noncomputable def wdist {n : ℕ} (G : SimpleGraph (Fin n)) (len : Fin n → Fin n → ℝ)
    (u v : Fin n) : ℝ :=
  sInf (Set.range fun p : G.Walk u v => (p.darts.map fun d => len d.fst d.snd).sum)

def NonnegLengths {n : ℕ} (G : SimpleGraph (Fin n)) (len : Fin n → Fin n → ℝ) : Prop :=
  ∀ u v, G.Adj u v → 0 ≤ len u v ∧ len u v = len v u

/-- Lengths as reals listed in adjacency-list order (aligned with `encAdj`). -/
noncomputable def encLengths {n : ℕ} (G : SimpleGraph (Fin n)) (len : Fin n → Fin n → ℝ) :
    List ℝ := by
  classical
  exact (List.finRange n).flatMap fun v =>
    ((Finset.univ.filter (G.Adj v)).sort (· ≤ ·)).map fun u => len v u

/-- A source: location, real initial value and identity. -/
structure Src (n : ℕ) where
  loc : Fin n
  init : ℝ
  ident : ℕ

/-- The first `q` source cones `(init + d(loc, v), identity)` at `v`, in increasing order
of value, ties by identity. -/
noncomputable def topCones {n : ℕ} (d : Fin n → Fin n → ℝ) (srcs : List (Src n)) (q : ℕ)
    (v : Fin n) : List (ℝ × ℕ) := by
  classical
  exact ((srcs.map fun s => (s.init + d s.loc v, s.ident)).mergeSort
    (fun p p' => decide (p.1 < p'.1 ∨ (p.1 = p'.1 ∧ p.2 ≤ p'.2)))).take q

noncomputable def encSrcs {n : ℕ} (srcs : List (Src n)) : List ℕ × List ℝ :=
  (srcs.length :: srcs.flatMap fun s => [s.loc.val, s.ident], srcs.map Src.init)

/-- Output of a list-per-vertex algorithm: `I[1 + v]` entries for vertex `v`, the `j`-th
stored as real `R[v·q + j]` and identity `I[1 + n + v·q + j]`. -/
noncomputable def outCones (n q : ℕ) (c : Cfg) (v : Fin n) : List (ℝ × ℕ) :=
  (List.range (c.imem (1 + v.val))).map fun j =>
    (c.rmem (v.val * q + j), c.imem (1 + n + v.val * q + j))

/-- Output of an alphabet algorithm, block `off` (`0` = upper, `n` = lower): vertex `v` has
`I[1 + off + v]` values `R[(off + v)·q + j]`, `j < I[1 + off + v]`. -/
noncomputable def outValues (n q off : ℕ) (c : Cfg) (v : Fin n) : Finset ℝ :=
  ((List.range (c.imem (1 + off + v.val))).map fun j => c.rmem ((off + v.val) * q + j)).toFinset

/-! ## Nice tree decompositions (Theorem 5.2, printed p.17, PDF p.19) -/

inductive NodeKind (n : ℕ)
  | leaf
  | introduce (v : Fin n)
  | forget (v : Fin n)
  | join

/-- A rooted decomposition supplied as input: nodes `Fin N`, a root, kinds, children
(meaningful per kind) and bags. -/
structure NiceTD (n : ℕ) where
  N : ℕ
  root : Fin N
  kind : Fin N → NodeKind n
  child1 : Fin N → Fin N
  child2 : Fin N → Fin N
  bag : Fin N → Finset (Fin n)

/-- `c` is a child of `t`. -/
def NiceTD.IsChild {n : ℕ} (T : NiceTD n) (t c : Fin T.N) : Prop :=
  match T.kind t with
  | .leaf => False
  | .introduce _ => c = T.child1 t
  | .forget _ => c = T.child1 t
  | .join => c = T.child1 t ∨ c = T.child2 t

/-- A nice tree decomposition of `G` of width exactly `ω`: children have smaller indices,
every non-root node has exactly one parent and the root none (a rooted tree); empty root
and leaf bags; introduce/forget/join nodes; every vertex and edge covered; the nodes whose
bag contains `v` form a connected subtree (exactly one topmost such node). -/
def IsNiceTD {n : ℕ} (G : SimpleGraph (Fin n)) (T : NiceTD n) (ω : ℕ) : Prop :=
  (∀ t c, T.IsChild t c → c < t) ∧
  (∀ c, c ≠ T.root → ∃! t, T.IsChild t c) ∧ (∀ t, ¬ T.IsChild t T.root) ∧
  T.bag T.root = ∅ ∧
  (∀ t, match T.kind t with
    | .leaf => T.bag t = ∅
    | .introduce v => v ∉ T.bag (T.child1 t) ∧ T.bag t = insert v (T.bag (T.child1 t))
    | .forget v => v ∈ T.bag (T.child1 t) ∧ T.bag t = (T.bag (T.child1 t)).erase v
    | .join => T.child1 t ≠ T.child2 t ∧ T.bag (T.child1 t) = T.bag t ∧
        T.bag (T.child2 t) = T.bag t) ∧
  (∀ v, ∃ t, v ∈ T.bag t) ∧
  (∀ u v, G.Adj u v → ∃ t, u ∈ T.bag t ∧ v ∈ T.bag t) ∧
  (∀ v t₁ t₂, v ∈ T.bag t₁ → (∀ p, T.IsChild p t₁ → v ∉ T.bag p) →
    v ∈ T.bag t₂ → (∀ p, T.IsChild p t₂ → v ∉ T.bag p) → t₁ = t₂) ∧
  (∀ t, (T.bag t).card ≤ ω + 1) ∧ (∃ t, (T.bag t).card = ω + 1)

noncomputable def NiceTD.joinCount {n : ℕ} (T : NiceTD n) : ℕ := by
  classical
  exact (Finset.univ.filter fun t => ∃ h : T.kind t = .join, h = h).card

noncomputable def NiceTD.otherCount {n : ℕ} (T : NiceTD n) : ℕ := T.N - T.joinCount

def NodeKind.code {n : ℕ} : NodeKind n → List ℕ
  | .leaf => [0, 0]
  | .introduce v => [1, v.val]
  | .forget v => [2, v.val]
  | .join => [3, 0]

/-- `N`, root, then per node: kind code, vertex, two children, bag size, sorted bag. -/
noncomputable def encTD {n : ℕ} (T : NiceTD n) : List ℕ :=
  T.N :: T.root.val :: (List.finRange T.N).flatMap fun t =>
    (T.kind t).code ++ [(T.child1 t).val, (T.child2 t).val, (T.bag t).card] ++
      ((T.bag t).sort (· ≤ ·)).map Fin.val

end MeanCertificates1424.Hardness.Supplement


