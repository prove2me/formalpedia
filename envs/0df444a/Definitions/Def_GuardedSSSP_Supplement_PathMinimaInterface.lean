-- Prove2me | Definitions.Def_GuardedSSSP_Supplement_PathMinimaInterface
-- name    : GuardedSSSP_Supplement_PathMinimaInterface
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:21:29.222421+00:00
-- url     : https://prove2.me/theorems/0127762b-1b02-4b0b-8fb4-8b5dd32d46d7
-- title:
--   Operations, legal sequences and the online RAM interface of the bottom-up path-minima structure (Theorem F.1)
-- statement:
--   Let $D$ be a rooted tree on $n$ vertices. The structure supports two operations:
--
--   1. $\mathrm{Finish}(v,k)$ supplies the immutable real key $k$ of $v$;
--   2. $\mathrm{Eval}(u)$, on a finished vertex $u$, returns the minimum key from $u$ up to its highest finished ancestor, inclusive.
--
--   A sequence of operations is **legal** (child-before-parent) when each vertex is finished at most once and only after all its children, and each $\mathrm{Eval}(u)$ comes after the finish of $u$. Since every finished vertex has all its descendants finished, the finished ancestors of $u$ form a contiguous upward segment, and the correct answer is the minimum key over the finished ancestors of $u$.
--
--   **Online execution.** An initialization program runs on the tree (integer memory: $n$, $r$, the parent array). Then, for each operation in turn, a handler program runs from the memory left by the previous run, with the operation written at fixed cells (integer cell $-1$: $1$ for finish, $2$ for eval; integer cell $-2$: the vertex; real cell $-1$: the key). After an Eval run halts, real cell $-2$ holds the answer. Each operation is thus answered before later operations are seen.
--
--   This interface states Theorem F.1 on the base mission's RAM.
--
--   **Formalization Note** Every run uses the word bound $(n+2)^c$ of an $n$-vertex input, independent of the sequence length. Answers are compared in `EReal`.
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), Appendix F and Theorem F.1, p.41 (PDF p.42)

import Mathlib
import Definitions.Def_GuardedSSSP_Machine
import Definitions.Def_GuardedSSSP_Supplement_RootedTree
import Definitions.Def_GuardedSSSP_Supplement_MachineRuns

namespace GuardedSSSP

namespace Supplement

open GuardedSSSP.Machine

/-!
# The online bottom-up path-minima interface of Theorem F.1

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…), Appendix F, p.41 (PDF p.42): "Each vertex is finished once,
after its children, when its immutable key is supplied. An operation Eval(u) on a finished vertex returns
the minimum from u to its highest finished ancestor, inclusive."

**Formalization Note.**
* An operation is `finish v k` (supply the key `k ∈ ℝ` of `v`) or `eval u`. A sequence is *legal* for
  the tree `par` (root `r`) when every `finish v k` is the first finish of `v` and comes after a finish of
  every child of `v`, and every `eval u` comes after a finish of `u`. Not every vertex has to be finished.
* Because every finished vertex has all its descendants finished, the finished ancestors of a finished `u`
  form a contiguous segment from `u` up to its highest finished ancestor. The correct answer to the
  `eval u` at position `i` is therefore the minimum of the keys of the finished ancestors of `u`
  (inclusive), taken in `EReal` (the set is nonempty, it contains `u`).
* **Online execution on the base RAM.** An initialization program runs on the tree; then for each
  operation, in order, the handler program runs from the memory left by the previous run (both banks),
  with registers and program counter reset to `0` and the operation written at pinned cells: integer cell
  `−1` holds `1` (finish) or `2` (eval), integer cell `−2` the vertex, real cell `−1` the key of a finish
  (`0` for an eval). After an `eval` run halts, real cell `−2` holds the answer. Each operation is
  therefore answered before the later operations are seen.
* **Tree input.** Integer memory: cell `0` is `n`, cell `1` is `r`, cell `2 + v` is `par v` (the root's
  slot holds `r`). Real memory, registers and program counter are `0`.
* **Word bound.** Every run uses the word bound `(n + 2)^c` of an `n`-vertex input (`wordBound P n 0`),
  independent of the length of the sequence.
-/

/-- An operation of the path-minima structure on `Fin n`. -/
inductive PMOp (n : ℕ) : Type
  | finish (v : Fin n) (k : ℝ)
  | eval (u : Fin n)

/-- The operation is an evaluation. -/
def PMOp.isEval {n : ℕ} : PMOp n → Bool
  | .finish _ _ => false
  | .eval _ => true

/-- `ops` is a legal child-before-parent sequence of finishes and evaluations for the tree `par` with
root `r`. -/
def IsLegalSeq {n : ℕ} (par : Fin n → Fin n) (r : Fin n) (ops : List (PMOp n)) : Prop :=
  ∀ (i : ℕ) (hi : i < ops.length),
    match ops[i] with
    | .finish v _ =>
        (∀ k' : ℝ, PMOp.finish v k' ∉ ops.take i) ∧
        (∀ c : Fin n, IsChild par r v c → ∃ k' : ℝ, PMOp.finish c k' ∈ ops.take i)
    | .eval u => ∃ k' : ℝ, PMOp.finish u k' ∈ ops.take i

/-- The correct answer to `Eval(u)` after the operations `done`: the minimum key over the finished
ancestors of `u`, inclusive. -/
noncomputable def evalAnswer {n : ℕ} (par : Fin n → Fin n) (done : List (PMOp n)) (u : Fin n) :
    EReal :=
  ⨅ (x : Fin n) (k : ℝ) (_ : IsAnc par x u ∧ PMOp.finish x k ∈ done), ((k : ℝ) : EReal)

/-- The initial state of the initialization program on the tree `(par, r)`. -/
def treeInit {n : ℕ} (par : Fin n → Fin n) (r : Fin n) : State where
  pc := 0
  ireg := fun _ => 0
  imem := fun z =>
    if 0 ≤ z then
      ([(n : ℤ), ((r : ℕ) : ℤ)] ++ List.ofFn (fun v : Fin n => (((par v : ℕ)) : ℤ))).getD z.toNat 0
    else 0
  rreg := fun _ => 0
  rmem := fun _ => 0
  halted := false
  stuck := false

/-- The start state of the handler for the operation `o`, from the memory of the state `σ`. -/
noncomputable def loadOp {n : ℕ} (σ : State) (o : PMOp n) : State where
  pc := 0
  ireg := fun _ => 0
  imem :=
    match o with
    | .finish v _ => Function.update (Function.update σ.imem (-1) 1) (-2) ((v : ℕ) : ℤ)
    | .eval u => Function.update (Function.update σ.imem (-1) 2) (-2) ((u : ℕ) : ℤ)
  rreg := fun _ => 0
  rmem :=
    match o with
    | .finish _ k => Function.update σ.rmem (-1) k
    | .eval _ => Function.update σ.rmem (-1) 0
  halted := false
  stuck := false

/-- The start states of the handler runs for the operations `ops`, the first one built from the memory of
`σ`: each run starts from the final memory of the previous one. -/
noncomputable def handlerStarts {n : ℕ} (Hd : Program) (W : ℤ) : State → List (PMOp n) → List State
  | _, [] => []
  | σ, o :: os => loadOp σ o :: handlerStarts Hd W (finalState Hd W (loadOp σ o)) os

end Supplement

end GuardedSSSP


