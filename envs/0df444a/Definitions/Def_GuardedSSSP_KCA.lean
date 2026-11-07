-- Prove2me | Definitions.Def_GuardedSSSP_KCA
-- name    : GuardedSSSP_KCA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:12.370981+00:00
-- url     : https://prove2.me/theorems/33971c02-67a3-4c4c-a87d-cc5c2ab692cb
-- title:
--   Comparison–addition decision trees and the topology benchmark $K_{\mathrm{CA}}(G,s)$
-- statement:
--   Fix a rooted directed topology $(G,s)$ with $n$ vertices and $m$ arcs. A **topology-specialized program** $A$ consists of finitely many real literals $c_1,\dots,c_\ell$ and a finite ternary decision tree acting on a growing list of real registers. The registers initially hold $0,c_1,\dots,c_\ell,w_0,\dots,w_{m-1}$. The tree has three kinds of nodes:
--
--   1. an **addition** node $\mathrm{add}(i,j)$ appends the new register $r_i+r_j$ and continues;
--   2. a **comparison** node $\mathrm{cmp}(i,j)$ continues in one of three subtrees according as $r_i<r_j$, $r_i=r_j$ or $r_i>r_j$;
--   3. a **leaf** assigns to each vertex $v$ either the infinity tag or a register index.
--
--   For a weighting $w$, let $C_A(w)$ and $P_A(w)$ be the numbers of comparison and addition nodes on the path that $w$ follows. The program is **correct** if for every $w\in\mathbb R^E_{\ge0}$ and every vertex $v$, the leaf reached gives $v$ the infinity tag exactly when $d_w(s,v)=+\infty$, and otherwise names a register whose value is $d_w(s,v)$. The **numerical benchmark** is
--
--   $$K_{\mathrm{CA}}(G,s)=\min_A\ \sup_{w\in\mathbb R^E_{\ge0}}\big(C_A(w)+P_A(w)\big),$$
--
--   the minimum being over correct programs.
--
--   The benchmark is the yardstick against which Theorem 1.1 measures the running time of one uniform program.
--
--   **Formalization Note** The paper's "finite deterministic programs" with finitely encoded discrete information about the topology are read as decision trees: a program whose charged outcomes determine its run, with free copying and selection, unrolls into a tree with the same per-input counts. Registers are referred to by index, so copying and selecting are free; an out-of-range index reads $0$, another copy of the literal zero. The benchmark is the `sInf` over $\mathbb N$ of the worst-case costs of correct programs; Lemma B.1 states that this set is nonempty.
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), §4.1, p.9 (PDF p.10), display (20)

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Network
import Definitions.Def_GuardedSSSP_dist

namespace GuardedSSSP

open AtomicDynRouting.ResidenceTime

/-!
# Topology-specialized comparison–addition programs and the benchmark `K_CA(G, s)`

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…), §4.1, p.9 (PDF p.10), display (20).

A competitor for a fixed rooted topology `(G, s)` is a finite ternary decision tree over a growing list of
real registers. The initial registers are literal `0`, the program's finitely many real literals, and the
weights `w e` in arc order.

* `add i j next` appends the register `reg i + reg j` (one addition).
* `cmp i j lt eq gt` branches three ways on `reg i < reg j`, `reg i = reg j`, `reg i > reg j`
  (one comparison).
* `leaf out` stops. `out v = none` is the infinity tag of vertex `v`, and `out v = some i` says that the
  label of `v` is register `i`.

`C A w` and `P A w` count the comparisons and additions on the execution reached by `w`. A program is
correct when, for every `w ≥ 0` and every vertex, its output is the distance `dist G w s v`. The benchmark
is `K_CA(G, s) = min_A sup_w (C_A(w) + P_A(w))`.

**Formalization Note.**
* The paper's "finite deterministic programs" with "finitely encoded discrete information" about the
  fixed topology are read as decision trees. A program with free discrete state and a finite worst case
  unrolls into a tree with the same per-input counts, because its charged outcomes determine its run.
  Copying and selecting a held register are free, as on p.9, because registers are referred to by index.
* Comparison and addition apply to any held registers, so mixed sums, register reuse, sharing across
  outputs and equality branches are all allowed. A register index beyond the current list reads `0`
  (`List.getD`), which is only another copy of the literal zero.
* The cost is counted along the execution of `w`, not as the syntactic depth of the tree; this is the
  `sup_w` of (20).
* `KCA G s` is the `sInf` over `ℕ` of the worst-case costs of correct programs. Lemma B.1 states that this
  set is nonempty, so the value is not the junk `sInf ∅ = 0`.
-/

/-- A comparison–addition decision tree whose leaves label the `n` vertices. -/
inductive CATree (n : ℕ) : Type
  | leaf (out : Fin n → Option ℕ)
  | add (i j : ℕ) (next : CATree n)
  | cmp (i j : ℕ) (lt eq gt : CATree n)

/-- A topology-specialized program: finitely many real literals and a decision tree. -/
structure CAProg (n : ℕ) : Type where
  lits : List ℝ
  tree : CATree n

namespace CATree

/-- Run a tree on a register list. Returns the leaf output, the final register list, the number of
comparisons and the number of additions on the path taken. -/
noncomputable def exec {n : ℕ} : CATree n → List ℝ → (Fin n → Option ℕ) × List ℝ × ℕ × ℕ
  | leaf out, regs => (out, regs, 0, 0)
  | add i j next, regs =>
      let r := exec next (regs ++ [regs.getD i 0 + regs.getD j 0])
      (r.1, r.2.1, r.2.2.1, r.2.2.2 + 1)
  | cmp i j lt eq gt, regs =>
      let r := if regs.getD i 0 < regs.getD j 0 then exec lt regs
        else if regs.getD i 0 = regs.getD j 0 then exec eq regs else exec gt regs
      (r.1, r.2.1, r.2.2.1 + 1, r.2.2.2)

end CATree

namespace CAProg

/-- The initial registers: literal zero, then the program's literals, then the weights in arc order. -/
def initRegs {n m : ℕ} (A : CAProg n) (w : Fin m → ℝ) : List ℝ :=
  (0 :: A.lits) ++ List.ofFn w

/-- The execution of `A` on the weighting `w`. -/
noncomputable def run {n m : ℕ} (A : CAProg n) (w : Fin m → ℝ) :
    (Fin n → Option ℕ) × List ℝ × ℕ × ℕ :=
  A.tree.exec (A.initRegs w)

/-- `C_A(w)`: the number of comparisons on the execution of `w`. -/
noncomputable def C {n m : ℕ} (A : CAProg n) (w : Fin m → ℝ) : ℕ := (A.run w).2.2.1

/-- `P_A(w)`: the number of additions on the execution of `w`. -/
noncomputable def P {n m : ℕ} (A : CAProg n) (w : Fin m → ℝ) : ℕ := (A.run w).2.2.2

/-- The label output for vertex `v`: `⊤` for the infinity tag, otherwise the value of the named
register. -/
noncomputable def output {n m : ℕ} (A : CAProg n) (w : Fin m → ℝ) (v : Fin n) : EReal :=
  match (A.run w).1 v with
  | none => ⊤
  | some i => (((A.run w).2.1.getD i 0 : ℝ) : EReal)

end CAProg

/-- `A` is correct for the rooted topology `(G, s)`: on every weighting of the nonnegative orthant, every
vertex receives the infinity tag exactly when it is unreachable, and otherwise a register holding its
distance. -/
def Correct {n m : ℕ} (G : Network (Fin n) (Fin m)) (s : Fin n) (A : CAProg n) : Prop :=
  ∀ w : Fin m → ℝ, (∀ e, 0 ≤ w e) → ∀ v : Fin n, A.output w v = dist G w s v

/-- The numerical benchmark `K_CA(G, s) = min_A sup_{w ∈ ℝ^E_{≥0}} (C_A(w) + P_A(w))`, display (20),
p.9. -/
noncomputable def KCA {n m : ℕ} (G : Network (Fin n) (Fin m)) (s : Fin n) : ℕ :=
  sInf {c : ℕ | ∃ A : CAProg n, Correct G s A ∧
    ∀ w : Fin m → ℝ, (∀ e, 0 ≤ w e) → A.C w + A.P w ≤ c}

end GuardedSSSP


