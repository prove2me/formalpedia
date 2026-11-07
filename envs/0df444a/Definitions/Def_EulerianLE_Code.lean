-- Prove2me | Definitions.Def_EulerianLE_Code
-- name    : EulerianLE_Code
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:56:36.113659+00:00
-- url     : https://prove2.me/theorems/355e5f8f-f80c-4e5f-8af2-3f9e0225e7e7
-- title:
--   A program language with concurrent branches, and Programs 7 and 8 (the OR protocol)
-- statement:
--   Programs 1–8 are written in a small language: send a pulse through a port, $\mathtt{BlockingRecv}(i,n)$ (blocked until $n$ pulses wait at $i$, then consume them; nothing if $n=0$), **wait until** at least $k$ pulses wait at a port of a set (and continue with the selected port), consume a pulse at one of several ports, read and update the node's variables, reset the counters $\tilde\sigma,\tilde\rho$, while loops, concurrent branches with a join, and `terminate`.
--
--   An interpreter turns a text into a node program. Without concurrent branches the main thread steps. During a concurrent loop, the first branch that is not blocked steps; when all have completed the node joins them; otherwise the node performs one queue test listing the guards of all blocked branches, and the branch whose guard fires resumes.
--
--   Programs 7 and 8, the OR initiator and the OR participant with input $b$, are built into the language. An instance runs on a port pair $(i,j)$, with $j$ the outgoing CW port: a pulse waiting at $i$ is CW, one waiting at $j$ is CCW. The initiator sends a CW pulse and waits: if a CW pulse returns it sends a second CW pulse, consumes it and returns $0$; otherwise it forwards the CCW pulse, consumes a CW pulse and returns $(1,\text{non-witness})$. A participant waits for a pulse; if it is CCW or $b=0$ it forwards two pulses and returns $0$ if both were CW and $(1,\text{non-witness})$ otherwise; if it is CW and $b=1$ it reflects two pulses and returns $(1,\text{witness})$.
--
--   **Formalization Note** The program point of an OR instance is part of the node's state, which is how Lemma 32 identifies instances in an arbitrary surrounding algorithm. Concurrent branches are tried in list order, the refinement of the paper's unspecified interleaving.
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), §2, p.7 (PDF p.9): instructions; Programs 7, 8, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_EulerianLE_NodeProg

namespace EulerianLE

/-- What a program can read besides its pulses: its variables (`store`) and the resettable counters
σ̃ (`sig`) and ρ̃ (`rho`) of its sends and consumptions at each port (Frei, Gelles, Ghazy, Nolin, STOC
2027 submission (manuscript sha256 90954a93…), §2, p.7; §4). -/
structure Ctx (deg : ℕ) (S : Type) where
  store : S
  sig : Fin deg → ℕ
  rho : Fin deg → ℕ

/-- The output of an OR instance (Programs 7, 8, p.22): `0`, or `(1, witness)` / `(1, non-witness)`. -/
inductive OrOut : Type
  | zero
  | one (witness : Bool)
  deriving DecidableEq, Repr

/-- The two OR programs: `ComputeORWitness_initiator` (Program 7) and
`ComputeORWitness_participant(b)` (Program 8). -/
inductive ORRole : Type
  | initiator
  | participant (b : Bool)

/-- The program points of Programs 7 and 8 (p.22, PDF p.24), each with the data the rest of the
instance needs. The instance runs on the port pair `(i, j)` with `j` the outgoing CW port and `i` the
incoming CW port; a pulse waiting at `i` is CW and one waiting at `j` is CCW.

* Program 7: `i3` (Line 3, `Send(CW,1)` through `j`), `i4` (Line 4, wait at `i` or `j`), `i6`, `i7`, `i8`
  (Lines 6–8), `i11`, `i12`, `i13` (Lines 11–13).
* Program 8: `p3 b` (Line 3, the initial wait), `f1 s cw` / `f1s s cw` (the consumption at `s` and the
  send through the other port of the first forwarded pulse), `f2 cw` / `f2s s cw` (the same for the
  second, consumed at `i` or `j`), with `cw` the number of forwarded pulses consumed at `i`, and `p11`,
  `p11s`, `p12`, `p12s` (Lines 11–12, the reflecting case).
* `ret o`: the instance returns `o`. -/
inductive ORLine (deg : ℕ) : Type
  | i3 | i4 | i6 | i7 | i8 | i11 | i12 | i13
  | p3 (b : Bool)
  | f1 (s : Fin deg) | f1s (s : Fin deg) (cw : ℕ) | f2 (cw : ℕ) | f2s (s : Fin deg) (cw : ℕ)
  | p11 | p11s | p12 | p12s
  | ret (o : OrOut)

/-- An OR instance in progress: its port pair (`i` incoming CW, `j` outgoing CW) and program point. -/
structure ORState (deg : ℕ) where
  i : Fin deg
  j : Fin deg
  line : ORLine deg

/-- The first program point of an OR program. -/
def ORRole.start {deg : ℕ} : ORRole → ORLine deg
  | .initiator => .i3
  | .participant b => .p3 b

/-- The program text of a node, in continuation-passing style over variables of type `S`.

* `done`: the current block ends (a loop body returns to its loop; a branch completes; the program
  returns).
* `halt`: `terminate`; the program completes.
* `send i k`: `Send(i, 1)`.
* `recv i n k`: `BlockingRecv(i, n)`: blocked until `n` pulses are waiting at `i`, which are then
  consumed one at a time; `n = 0` is no operation.
* `waitAt need ports k`: `wait until` at least `need` pulses are waiting at a port of `ports`; `k` gets
  the selected port.
* `consumeAt ports k`: consume a pulse at one of several ports; `k` gets the port.
* `get k`: read the variables and counters; `set f k`: update the variables; `resetCounters k`: set
  σ̃ and ρ̃ to `0`.
* `loop c body k`: `while c do body`, then `k`.
* `par bs k`: run the branches `bs` concurrently, join them, then `k`.
* `orCall role i j k`: run Program 7 or 8 on the port pair `(i, j)` and continue with `k` of its output.

**Formalization Note.** Programs 7 and 8 are built in (`ORLine`), so that an OR instance and its
program point are visible in the node's state (Lemma 32). -/
inductive Code (deg : ℕ) (S : Type) : Type
  | done
  | halt
  | send (i : Fin deg) (k : Code deg S)
  | recv (i : Fin deg) (n : ℕ) (k : Code deg S)
  | waitAt (need : ℕ) (ports : Finset (Fin deg)) (k : Fin deg → Code deg S)
  | consumeAt (ports : Finset (Fin deg)) (k : Fin deg → Code deg S)
  | get (k : Ctx deg S → Code deg S)
  | set (f : S → S) (k : Code deg S)
  | resetCounters (k : Code deg S)
  | loop (c : Ctx deg S → Bool) (body : Code deg S) (k : Code deg S)
  | par (bs : List (Code deg S)) (k : Code deg S)
  | orCall (role : ORRole) (i j : Fin deg) (k : OrOut → Code deg S)

/-- A frame of a branch's stack: a piece of program text, or an OR instance with the code that receives
its output. -/
inductive Frame (deg : ℕ) (S : Type) : Type
  | code (c : Code deg S)
  | orf (st : ORState deg) (k : OrOut → Code deg S)

/-- The consumption of `n` pulses at `i`, one at a time. -/
def takeN {deg : ℕ} {S : Type} (i : Fin deg) : ℕ → Code deg S → Code deg S
  | 0, k => k
  | n + 1, k => .consumeAt {i} fun _ => takeN i n k

/-- What a branch does next. `block g k`: it waits on the guard `g` and continues with `k p` when the
guard selects `p`. -/
inductive BStep (deg : ℕ) (S : Type) : Type
  | finished
  | halt
  | tau (ctx : Ctx deg S) (stk : List (Frame deg S))
  | send (i : Fin deg) (ctx : Ctx deg S) (stk : List (Frame deg S))
  | block (g : Guard deg) (k : Fin deg → Ctx deg S × List (Frame deg S))

namespace BStep

variable {deg : ℕ} {S : Type}

/-- Record a send through `i`. -/
def sendAt (i : Fin deg) (ctx : Ctx deg S) (stk : List (Frame deg S)) : BStep deg S :=
  .send i { ctx with sig := Function.update ctx.sig i (ctx.sig i + 1) } stk

/-- Wait for a pulse at `p` and consume it. -/
def takeAt (p : Fin deg) (ctx : Ctx deg S) (stk : Fin deg → List (Frame deg S)) : BStep deg S :=
  .block ⟨1, {p}, true⟩ fun q => ({ ctx with rho := Function.update ctx.rho q (ctx.rho q + 1) }, stk q)

end BStep

/-- One step of an OR instance in state `st`, with continuation `k` and the rest `rest` of the branch's
stack: Program 7 (initiator) and Program 8 (participant), p.22. -/
def orStep {deg : ℕ} {S : Type} (ctx : Ctx deg S) (st : ORState deg) (k : OrOut → Code deg S)
    (rest : List (Frame deg S)) : BStep deg S :=
  let i := st.i
  let j := st.j
  let go : ORLine deg → List (Frame deg S) := fun l => .orf ⟨i, j, l⟩ k :: rest
  let other : Fin deg → Fin deg := fun s => if s = i then j else i
  match st.line with
  -- Program 7
  | .i3 => .sendAt j ctx (go .i4)
  | .i4 => .block ⟨1, {i, j}, false⟩ fun s => (ctx, go (if s = i then .i6 else .i11))
  | .i6 => .takeAt i ctx fun _ => go .i7
  | .i7 => .sendAt j ctx (go .i8)
  | .i8 => .takeAt i ctx fun _ => go (.ret .zero)
  | .i11 => .takeAt j ctx fun _ => go .i12
  | .i12 => .sendAt i ctx (go .i13)
  | .i13 => .takeAt i ctx fun _ => go (.ret (.one false))
  -- Program 8
  | .p3 b => .block ⟨1, {i, j}, false⟩ fun s =>
      (ctx, go (if s = j ∨ b = false then .f1 s else .p11))
  | .f1 s => .takeAt s ctx fun _ => go (.f1s s (if s = i then 1 else 0))
  | .f1s s cw => .sendAt (other s) ctx (go (.f2 cw))
  | .f2 cw => .block ⟨1, {i, j}, true⟩ fun s =>
      ({ ctx with rho := Function.update ctx.rho s (ctx.rho s + 1) },
        go (.f2s s (cw + if s = i then 1 else 0)))
  | .f2s s cw => .sendAt (other s) ctx (go (.ret (if cw = 2 then .zero else .one false)))
  | .p11 => .takeAt i ctx fun _ => go .p11s
  | .p11s => .sendAt i ctx (go .p12)
  | .p12 => .takeAt j ctx fun _ => go .p12s
  | .p12s => .sendAt j ctx (go (.ret (.one true)))
  | .ret o => .tau ctx (.code (k o) :: rest)

/-- One step of a branch with stack `stk`.

**Formalization Note.** A `par` inside a branch is not supported and is skipped; Programs 1–8 have
none (their concurrent loops are at the top level of a program). -/
def bstep {deg : ℕ} {S : Type} (ctx : Ctx deg S) : List (Frame deg S) → BStep deg S
  | [] => .finished
  | .orf st k :: rest => orStep ctx st k rest
  | .code c :: rest =>
    match c with
    | .done => .tau ctx rest
    | .halt => .halt
    | .send i k => .sendAt i ctx (.code k :: rest)
    | .recv i n k =>
      if n = 0 then .tau ctx (.code k :: rest)
      else .block ⟨n, {i}, false⟩ fun _ => (ctx, .code (takeN i n k) :: rest)
    | .waitAt need ps k => .block ⟨need, ps, false⟩ fun p => (ctx, .code (k p) :: rest)
    | .consumeAt ps k => .block ⟨1, ps, true⟩ fun p =>
        ({ ctx with rho := Function.update ctx.rho p (ctx.rho p + 1) }, .code (k p) :: rest)
    | .get k => .tau ctx (.code (k ctx) :: rest)
    | .set f k => .tau { ctx with store := f ctx.store } (.code k :: rest)
    | .resetCounters k => .tau { ctx with sig := fun _ => 0, rho := fun _ => 0 } (.code k :: rest)
    | .loop cond body k =>
      if cond ctx then .tau ctx (.code body :: .code (.loop cond body k) :: rest)
      else .tau ctx (.code k :: rest)
    | .par _ k => .tau ctx (.code k :: rest)
    | .orCall role i j k => .tau ctx (.orf ⟨i, j, role.start⟩ k :: rest)

/-- The state of an interpreted program: variables and counters, the stack of the main thread, and,
while a concurrent loop runs, the stacks of its branches (the main stack then holds the code after
the join). -/
structure RunState (deg : ℕ) (S : Type) where
  ctx : Ctx deg S
  main : List (Frame deg S)
  brs : Option (List (List (Frame deg S)))

/-- The list with its positions. -/
def withIdx {α : Type} : List α → ℕ → List (ℕ × α)
  | [], _ => []
  | a :: l, n => (n, a) :: withIdx l (n + 1)

/-- The first branch whose next step is not blocked, with that step. -/
def firstActive {deg : ℕ} {S : Type} : List (ℕ × BStep deg S) → Option (ℕ × BStep deg S)
  | [] => none
  | (_, .block _ _) :: l => firstActive l
  | (_, .finished) :: l => firstActive l
  | (n, b) :: _ => some (n, b)

/-- The blocked branches, with their guards and continuations. -/
def blockedOf {deg : ℕ} {S : Type} :
    List (ℕ × BStep deg S) → List (ℕ × Guard deg × (Fin deg → Ctx deg S × List (Frame deg S)))
  | [] => []
  | (n, .block g k) :: l => (n, g, k) :: blockedOf l
  | _ :: l => blockedOf l

/-- One step of an interpreted program. Without concurrent branches, the main stack steps. With
branches, the first branch (in list order) that is not blocked steps; if all have completed, the
node joins them; otherwise the node executes one queue test listing the guards of all blocked
branches, in branch order, and the branch whose guard fires resumes.

**Formalization Note.** Branch order is the refinement "smallest index first" of the paper's
unspecified interleaving of concurrent branches (paper.md decision 6). A `halt` in a branch
completes the program. -/
def RunState.step {deg : ℕ} {S Out : Type} (out : Ctx deg S → Out) (st : RunState deg S) :
    Instr deg (RunState deg S) Out :=
  match st.brs with
  | none =>
    match st.main with
    | .code (.par bs k) :: rest =>
      .tau { st with brs := some (bs.map fun b => [.code b]), main := .code k :: rest }
    | stk =>
      match bstep st.ctx stk with
      | .finished => .complete (out st.ctx)
      | .halt => .complete (out st.ctx)
      | .tau c s => .tau { st with ctx := c, main := s }
      | .send i c s => .send i { st with ctx := c, main := s }
      | .block g k => .test [g] none fun _ p => { st with ctx := (k p).1, main := (k p).2 }
  | some bs =>
    let steps := withIdx (bs.map (bstep st.ctx)) 0
    match firstActive steps with
    | some (n, .tau c s) => .tau { st with ctx := c, brs := some (bs.set n s) }
    | some (n, .send i c s) => .send i { st with ctx := c, brs := some (bs.set n s) }
    | some (_, _) => .complete (out st.ctx)
    | none =>
      if bs.all (·.isEmpty) then .tau { st with brs := none }
      else
        let bl := blockedOf steps
        .test (bl.map (·.2.1)) none fun gi p =>
          match bl[gi]? with
          | some (n, _, k) => { st with ctx := (k p).1, brs := some (bs.set n (k p).2) }
          | none => st

/-- The node program of a program text `c` with initial variables `s₀` and output `out` read from the
variables and counters when the program completes. -/
def Code.prog {deg : ℕ} {S Out : Type} (c : Code deg S) (s₀ : S) (out : Ctx deg S → Out) :
    NodeProg deg Out where
  State := RunState deg S
  init := ⟨⟨s₀, fun _ => 0, fun _ => 0⟩, [.code c], none⟩
  step := RunState.step out

end EulerianLE


