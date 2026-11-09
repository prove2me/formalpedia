-- Prove2me | Definitions.Def_MSTCuts2027_Parallel_Machine
-- name    : MSTCuts2027_Parallel_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:49:29.62469+00:00
-- url     : https://prove2.me/theorems/dec3f48a-e8d6-470d-b2c9-4c15b6362a01
-- title:
--   A fork-join CREW machine with charged work and depth and an external single-pair procedure
-- statement:
--   This file fixes the execution model of Appendix E: shared memory with concurrent reads and exclusive writes, in which a program's output, work and depth all result from running it.
--
--   A **program** is a finite list of procedures in a small imperative language. Statements assign a private register, write a shared word cell, copy a shared real cell, sequence, branch, call a procedure with a fresh register frame, run a loop whose iterations execute concurrently (`parFor`, the "pardo" of PRAM pseudocode), or call the external procedure. Expressions combine integer constants, registers and shared cells by $+,-,\times,\div$ and comparisons, and can compare two real cells. Real cells can only be compared and copied.
--
--   **Costs.** Each basic statement, test, fork and call is charged one step. Sequencing adds work and adds depth. A concurrent loop charges one step plus the sum of the threads' work, and one step plus the largest depth of a thread.
--
--   **External procedure.** The procedure $P$ is a function on pairs of vertices of $\{0,\dots,n-1\}$ returning a cut, a value, and the work and depth of that query. A call stores the cut as a Boolean array of $n$ cells at an address the program chooses, stores the value in a real cell, and charges the reported costs plus one step. A call on an equal or out-of-range pair is stuck.
--
--   **Stuck runs.** A run is stuck on a word of absolute value above the machine's word bound, a bad address, an unknown procedure, or a concurrent loop in which some thread writes a location that another thread reads or writes. A run that succeeds is therefore exclusive-write. It is in fact stricter than the model of Appendix E, since a read may not race with a write either.
--
--   The semantics is executable. Since programs are syntax trees, they cannot hide a computation in a Lean function, and it is the semantics that supplies every cost.
--
--   **Formalization Note** `run` takes fuel, which bounds the nesting of executions and plays no part in costs; `Halts` quantifies over it existentially. The type of real cells is a parameter $R$ with a linear order, set to $\mathbb R$ in all theorems, so that a sanity check can execute programs over $\mathbb Z$. Expression size is not charged because a program is one fixed finite term. Division is `Int` division, with $x/0=0$.
-- source:
--   Baswana–Roy, Using MSTs to Compute All-Pairs Mincuts and Beyond ..., STOC 2027 submission #21, pinned preprint SHA-256 faa337be0f0f1bfbbcf924cb3591bd51ded2a6ef2c9e2154e00534a840156a11, Appendix E (CREW PRAM model), printed p. 24, PDF p. 26

import Mathlib

/-!
# A fork-join CREW machine with charged work and depth

The execution model of Baswana–Roy, *Using MSTs to Compute All-Pairs Mincuts and Beyond ...*,
STOC 2027 submission #21, Appendix E (printed p. 24, PDF p. 26): shared memory, concurrent reads,
exclusive writes. Programs are finite syntax trees, so a program cannot hide a computation in a
Lean function, and the semantics below alone determines outputs, work and depth.
-/

namespace MSTCuts2027.Parallel

/-- Expressions over integer machine words. `var i` is a thread-private register, `read a` a shared
word cell and `rle a b` compares two shared real cells (`1` if `R[a] ≤ R[b]`, else `0`). Division is
`Int` division, with Lean's `x / 0 = 0`. Real cells can only be compared and copied. -/
inductive Expr where
  | const (c : ℤ)
  | var (i : ℕ)
  | read (a : Expr)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | div (a b : Expr)
  | lt (a b : Expr)
  | le (a b : Expr)
  | eq (a b : Expr)
  | rle (a b : Expr)
  deriving Repr, Inhabited

/-- Statements. `parFor i lo hi body` is the `pardo` of work-time PRAM pseudocode: it runs `body`
for every `i ∈ [lo, hi)` concurrently. `call f args` calls procedure number `f` of the program with
a fresh register frame. `oracle u v dest rdest` runs the external single-pair procedure. -/
inductive Stmt where
  | skip
  | setVar (i : ℕ) (e : Expr)
  | write (a e : Expr)
  | rcopy (dst src : Expr)
  | seq (s t : Stmt)
  | ite (c : Expr) (s t : Stmt)
  | parFor (i : ℕ) (lo hi : Expr) (body : Stmt)
  | call (f : ℕ) (args : List Expr)
  | oracle (u v dest rdest : Expr)
  deriving Repr, Inhabited

/-- A program is a finite list of procedures, which may call each other recursively. It is a single
finite term: it does not depend on the number of vertices, which it reads from memory. -/
abbrev Program := List Stmt

/-- Shared memory: integer word cells and cells holding values of `R` (the reals in the theorems). -/
structure Store (R : Type) where
  mem : ℕ → ℤ
  rmem : ℕ → R

/-- A shared memory location. -/
inductive Loc where
  | word (a : ℕ)
  | real (a : ℕ)
  deriving DecidableEq, Repr

/-- The answer of the external procedure `P` for one endpoint pair, with the work and depth `P`
spends on that query, including writing out the cut. -/
structure OracleAnswer (R : Type) (n : ℕ) where
  cut : Finset (Fin n)
  value : R
  work : ℕ
  depth : ℕ

/-- The external single-pair procedure `P` on vertex set `Fin n`. -/
abbrev Oracle (R : Type) (n : ℕ) := Fin n → Fin n → OracleAnswer R n

/-- The machine for `n` vertices: its word size bound (every integer handled has absolute value at
most `wordMax`, and every address is at most `wordMax`) and the external procedure. -/
structure Machine (R : Type) (n : ℕ) where
  wordMax : ℕ
  oracle : Oracle R n

/-- The result of running a statement: final memory and registers, the shared locations read and
written, and the charged work and depth. -/
structure Outcome (R : Type) where
  store : Store R
  vars : ℕ → ℤ
  reads : Finset Loc
  writes : Finset Loc
  work : ℕ
  depth : ℕ

/-- Two concurrent threads do not interfere: neither writes a location that the other reads or
writes. Concurrent reads of one location are allowed. -/
def Compatible {R : Type} (o o' : Outcome R) : Prop :=
  Disjoint o.writes o'.writes ∧ Disjoint o.writes o'.reads ∧ Disjoint o.reads o'.writes

instance {R : Type} : DecidableRel (Compatible (R := R)) := fun o o' => by
  unfold Compatible
  infer_instance

/-- Memory `σ` with the locations in `w` replaced by their contents in `τ`. -/
def Store.overlay {R : Type} (σ τ : Store R) (w : Finset Loc) : Store R where
  mem := fun a => if Loc.word a ∈ w then τ.mem a else σ.mem a
  rmem := fun a => if Loc.real a ∈ w then τ.rmem a else σ.rmem a

variable {R : Type} [LinearOrder R] {n : ℕ}

/-- A word, or failure if it is too large for the machine. -/
def Machine.word (M : Machine R n) (z : ℤ) : Option ℤ :=
  if z.natAbs ≤ M.wordMax then some z else none

/-- An address, or failure if it is negative or too large for the machine. -/
def Machine.addr (M : Machine R n) (z : ℤ) : Option ℕ :=
  if 0 ≤ z ∧ z.toNat ≤ M.wordMax then some z.toNat else none

/-- A vertex number, or failure if it is out of range. -/
def vertexOf (n : ℕ) (z : ℤ) : Option (Fin n) :=
  if h : 0 ≤ z ∧ z.toNat < n then some ⟨z.toNat, h.2⟩ else none

/-- Expression evaluation: the value and the shared locations read. -/
def eval (M : Machine R n) (σ : Store R) (vars : ℕ → ℤ) : Expr → Option (ℤ × Finset Loc)
  | .const c => do
      let z ← M.word c
      some (z, ∅)
  | .var i => do
      let z ← M.word (vars i)
      some (z, ∅)
  | .read a => do
      let (x, r) ← eval M σ vars a
      let k ← M.addr x
      let z ← M.word (σ.mem k)
      some (z, insert (Loc.word k) r)
  | .add a b => do
      let (x, r) ← eval M σ vars a
      let (y, r') ← eval M σ vars b
      let z ← M.word (x + y)
      some (z, r ∪ r')
  | .sub a b => do
      let (x, r) ← eval M σ vars a
      let (y, r') ← eval M σ vars b
      let z ← M.word (x - y)
      some (z, r ∪ r')
  | .mul a b => do
      let (x, r) ← eval M σ vars a
      let (y, r') ← eval M σ vars b
      let z ← M.word (x * y)
      some (z, r ∪ r')
  | .div a b => do
      let (x, r) ← eval M σ vars a
      let (y, r') ← eval M σ vars b
      let z ← M.word (x / y)
      some (z, r ∪ r')
  | .lt a b => do
      let (x, r) ← eval M σ vars a
      let (y, r') ← eval M σ vars b
      some (if x < y then 1 else 0, r ∪ r')
  | .le a b => do
      let (x, r) ← eval M σ vars a
      let (y, r') ← eval M σ vars b
      some (if x ≤ y then 1 else 0, r ∪ r')
  | .eq a b => do
      let (x, r) ← eval M σ vars a
      let (y, r') ← eval M σ vars b
      some (if x = y then 1 else 0, r ∪ r')
  | .rle a b => do
      let (x, r) ← eval M σ vars a
      let (y, r') ← eval M σ vars b
      let ka ← M.addr x
      let kb ← M.addr y
      some (if σ.rmem ka ≤ σ.rmem kb then 1 else 0,
        insert (Loc.real ka) (insert (Loc.real kb) (r ∪ r')))

/-- Evaluate a list of expressions, collecting values and shared reads. -/
def evalList (M : Machine R n) (σ : Store R) (vars : ℕ → ℤ) :
    List Expr → Option (List ℤ × Finset Loc)
  | [] => some ([], ∅)
  | e :: es => do
      let (x, r) ← eval M σ vars e
      let (xs, r') ← evalList M σ vars es
      some (x :: xs, r ∪ r')

/-- The register frame of a procedure call: argument `i` in register `i`, all others `0`. -/
def frame (args : List ℤ) : ℕ → ℤ := fun i => args.getD i 0

/-- Memory after the external procedure's answer is stored: the cut's Boolean array in the word
cells `dest + w` (`w < n`) and its value in the real cell `rdest`. -/
def storeAnswer (σ : Store R) (ans : OracleAnswer R n) (dest rdest : ℕ) : Store R where
  mem := fun c =>
    if h : dest ≤ c ∧ c < dest + n then
      (if (⟨c - dest, by omega⟩ : Fin n) ∈ ans.cut then 1 else 0)
    else σ.mem c
  rmem := fun c => if c = rdest then ans.value else σ.rmem c

/-- The locations written by `storeAnswer`. -/
def answerWrites (n dest rdest : ℕ) : Finset Loc :=
  insert (Loc.real rdest) ((Finset.range n).image fun w => Loc.word (dest + w))

/-- The operational semantics, with `fuel` bounding the nesting of statement executions (recursion
included); `none` means that the fuel ran out or the program is stuck. A program is stuck on an
oversized word, a bad address, an unknown procedure, an external query on an out-of-range or equal
pair, or a `parFor` whose threads interfere: a run that succeeds is therefore exclusive-write.

Costs: every basic statement, every test, every fork and every call costs one step, whatever the
size of its expressions (a program is a fixed finite term, so that size is a constant). Sequencing
adds work and depth. `parFor` charges one step of depth plus the largest depth of a thread, and one
step of work plus the sum of the threads' work. An external query additionally charges exactly the
work and depth that the answer reports. -/
def run (M : Machine R n) (P : Program) : ℕ → Stmt → Store R → (ℕ → ℤ) → Option (Outcome R)
  | 0, _, _, _ => none
  | _ + 1, .skip, σ, vars => some ⟨σ, vars, ∅, ∅, 1, 1⟩
  | _ + 1, .setVar i e, σ, vars => do
      let (x, r) ← eval M σ vars e
      some ⟨σ, Function.update vars i x, r, ∅, 1, 1⟩
  | _ + 1, .write a e, σ, vars => do
      let (x, r) ← eval M σ vars a
      let (y, r') ← eval M σ vars e
      let k ← M.addr x
      some ⟨{ σ with mem := Function.update σ.mem k y }, vars, r ∪ r',
        {Loc.word k}, 1, 1⟩
  | _ + 1, .rcopy d s, σ, vars => do
      let (x, r) ← eval M σ vars d
      let (y, r') ← eval M σ vars s
      let kd ← M.addr x
      let ks ← M.addr y
      some ⟨{ σ with rmem := Function.update σ.rmem kd (σ.rmem ks) }, vars,
        insert (Loc.real ks) (r ∪ r'), {Loc.real kd}, 1, 1⟩
  | fuel + 1, .seq s t, σ, vars => do
      let o ← run M P fuel s σ vars
      let o' ← run M P fuel t o.store o.vars
      some ⟨o'.store, o'.vars, o.reads ∪ o'.reads, o.writes ∪ o'.writes,
        o.work + o'.work, o.depth + o'.depth⟩
  | fuel + 1, .ite c s t, σ, vars => do
      let (x, r) ← eval M σ vars c
      let o ← run M P fuel (if x ≠ 0 then s else t) σ vars
      some ⟨o.store, o.vars, r ∪ o.reads, o.writes, o.work + 1, o.depth + 1⟩
  | fuel + 1, .parFor i lo hi body, σ, vars => do
      let (a, r) ← eval M σ vars lo
      let (b, r') ← eval M σ vars hi
      let outs ← (List.range (b - a).toNat).mapM fun k =>
        run M P fuel body σ (Function.update vars i (a + k))
      if outs.Pairwise Compatible then
        some ⟨outs.foldl (fun τ o => τ.overlay o.store o.writes) σ, vars,
          outs.foldl (fun w o => w ∪ o.reads) (r ∪ r'),
          outs.foldl (fun w o => w ∪ o.writes) ∅,
          (outs.map Outcome.work).sum + 1,
          (outs.map Outcome.depth).foldr max 0 + 1⟩
      else none
  | fuel + 1, .call f args, σ, vars => do
      let (xs, r) ← evalList M σ vars args
      let body ← P[f]?
      let o ← run M P fuel body σ (frame xs)
      some ⟨o.store, vars, r ∪ o.reads, o.writes, o.work + 1, o.depth + 1⟩
  | _ + 1, .oracle u v dest rdest, σ, vars => do
      let (x, r₁) ← eval M σ vars u
      let (y, r₂) ← eval M σ vars v
      let (d, r₃) ← eval M σ vars dest
      let (e, r₄) ← eval M σ vars rdest
      let a ← vertexOf n x
      let b ← vertexOf n y
      let kd ← M.addr d
      let ke ← M.addr e
      if a ≠ b ∧ kd + n ≤ M.wordMax then
        let ans := M.oracle a b
        some ⟨storeAnswer σ ans kd ke, vars, r₁ ∪ r₂ ∪ r₃ ∪ r₄, answerWrites n kd ke,
          ans.work + 1, ans.depth + 1⟩
      else none

/-- Procedure `f` of `P`, called on the words `args` from memory `σ`, halts with outcome `o`. Enough
fuel is existentially quantified, because fuel plays no role in costs or results. -/
def Halts (M : Machine R n) (P : Program) (f : ℕ) (args : List ℤ) (σ : Store R)
    (o : Outcome R) : Prop :=
  ∃ fuel : ℕ, ∃ body : Stmt, P[f]? = some body ∧ run M P fuel body σ (frame args) = some o

end MSTCuts2027.Parallel


