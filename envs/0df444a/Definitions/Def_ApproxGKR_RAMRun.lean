-- Prove2me | Definitions.Def_ApproxGKR_RAMRun
-- name    : ApproxGKR_RAMRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:03.719665+00:00
-- url     : https://prove2.me/theorems/a67611aa-6400-4992-9d8f-338cc181c6b6
-- title:
--   The online log-cost oracle RAM with phases
-- statement:
--   The machine model of the mission (the paper names none; it counts bit operations, p.5 and p.27). A program is a list of instructions over a memory $M:\mathbb N\to\mathbb N$ of finite support: constants, addition, truncated subtraction, indirect load and store, a conditional jump, bit reads from the read-only instance, from the *current* prover message and from the *current* coin (value $2$ past the end), an oracle call, and `endPhase`/`accept`/`reject`.
--
--   1. **Cost.** Each executed instruction costs $1$ plus the binary sizes of every address and value it touches; an oracle call costs $1$ plus the sizes of the query fields and of the answer ("charged separately", Theorem C.1).
--   2. **Space.** The maximum over the run of $\sum_{M[a]\ne0}(\mathrm{size}(a)+\mathrm{size}(M[a]))$; the instance, message and coin are read-only and not counted.
--   3. **Phases.** A verifier run has $R$ phases; phase $t$ sees the instance, message $t$ and coin $t$ only, and the memory persists. A phase $t<R$ ends with `endPhase`; `accept` accepts; anything else rejects.
--   4. **Oracle.** A query is (layer, type, $\log_2N$, precision $p$, point as root indices); the answer $(A,B)$ stands for $(A+iB)2^{-p}$.
--   5. A **single run** (`SRun`) is a one-phase run that halts by `accept`; its output is the bit string $M[1],\dots,M[M[0]]$.
--
--   **Formalization Note** The online phase structure is the stronger reading of the verifier's $O(Db+m\ell)$ space: the paper's accounting stores only the current coefficient vector and the current and preceding challenge vectors (§C.4, p.39), not the transcript.
-- source:
--   Das, Gupta, Mondal, More, Delegating Computation with Approximate Arithmetic: Interactive Proofs for Wizards (manuscript, sha256 78b2a36b…), §2.1, p.5; App. B.2, p.27; Theorem C.1, pp.33–34; §C.4, p.39

import Mathlib

namespace ApproxGKR

/-! An online log-cost oracle RAM with phases: the machine model in which the verifier, the
honest prover and the root-approximation algorithm of the mission are programs.

Das, Gupta, Mondal, More, *Delegating Computation with Approximate Arithmetic* (manuscript,
sha256 78b2a36b…): "running times count bit operations" (§2.1, p.5; App. B.2, p.27); the verifier
uses "`O(Db + mℓ)` space" (Theorem C.1, p.34) with "Storing the current coefficient vector takes
`O(Db)` bits, and storing the preceding and current challenge vectors takes `O(mℓ)` bits" (§C.4,
p.39); "both parties may query these polynomials at tuples of roots of unity to any requested
absolute error" (p.30), with "the costs of evaluating the polynomial extensions … charged
separately" (p.34).

**Formalization Note** (the machine is this mission's reading; the paper names none)
* Memory is a finitely supported map `ℕ → ℕ`. Instructions: constants, addition, truncated
  subtraction, indirect load and store, a conditional jump, bit reads from the read-only
  instance, from the *current* prover message and from the *current* coin (value `2` past the
  end), an oracle call, and `endPhase` / `accept` / `reject`.
* Each executed instruction costs `1 +` the binary sizes of every address and value it uses
  (log-cost). An oracle call costs `1 +` the sizes of the query fields and of the answer: the
  evaluation itself is charged separately, as on p.34.
* Space is the maximum, over the configurations of the run, of `Σ_{M[a] ≠ 0} (size a + size M[a])`.
  The instance, the message and the coin are read-only inputs and are not counted.
* A run has `R` phases. In phase `t` the program sees the instance, message `t` and coin `t` only;
  the memory persists between phases. Phase `t < R` ends with `endPhase`; `accept` accepts;
  `reject`, a jump out of the program, or `endPhase` in phase `R` rejects. So the verifier cannot
  re-read old messages unless it stored them in its (counted) memory. -/

/-- Instructions of the RAM. -/
inductive Instr where
  /-- `M[d] := c` -/
  | const (d c : ℕ)
  /-- `M[d] := M[a] + M[b]` -/
  | add (d a b : ℕ)
  /-- `M[d] := M[a] ∸ M[b]` -/
  | monus (d a b : ℕ)
  /-- `M[d] := M[M[a]]` -/
  | load (d a : ℕ)
  /-- `M[M[a]] := M[b]` -/
  | store (a b : ℕ)
  /-- if `M[a] ≤ M[b]` jump to `target` -/
  | jle (a b target : ℕ)
  /-- `M[d] :=` bit `M[a]` of the instance (`2` past the end) -/
  | readIn (d a : ℕ)
  /-- `M[d] :=` bit `M[a]` of the current prover message (`2` past the end) -/
  | readMsg (d a : ℕ)
  /-- `M[d] :=` bit `M[a]` of the current coin (`2` past the end) -/
  | readCoin (d a : ℕ)
  /-- oracle call: query read from `M[1..6]`, answer written to `M[7..10]` -/
  | oracle
  | endPhase
  | accept
  | reject

/-- A program is a list of instructions; the program counter indexes it. -/
abbrev Program : Type := List Instr

/-- An oracle query: the layer `i`, the type (`0` = `add~`, otherwise `mult~`), `log₂ N`, the
requested precision `p` (absolute error `2^{−p}`), and the point as a list of root indices in
`Fin (2^{logN})`, in the coordinate order `(g, u, v)`. -/
structure Query where
  layer : ℕ
  type : ℕ
  logN : ℕ
  prec : ℕ
  point : List ℕ

/-- An oracle answer function: the answer `(A, B)`, standing for `(A + iB)2^{−p}`. -/
abbrev OracleAnswers : Type := Query → ℤ × ℤ

/-- The read-only environment of a phase. -/
structure Env where
  inst : List Bool
  msg : List Bool
  coin : List Bool
  oracle : OracleAnswers

/-- Bit access: `1`, `0`, or `2` past the end. -/
def bitAt (w : List Bool) (i : ℕ) : ℕ :=
  match w[i]? with
  | some true => 1
  | some false => 0
  | none => 2

/-- Memory. -/
abbrev Mem : Type := ℕ →₀ ℕ

/-- The space of a memory: `Σ_{M[a] ≠ 0} (size a + size M[a])`. -/
def memSpace (M : Mem) : ℕ := M.sum (fun a v => Nat.size a + Nat.size v)

/-- A configuration. -/
structure Cfg where
  pc : ℕ
  mem : Mem

/-- How a step ends. -/
inductive Ctl where
  | cont
  | endPhase
  | accept
  | reject

/-- The query held in memory: `M[1]` layer, `M[2]` type, `M[3]` `log N`, `M[4]` precision,
`M[5]` base address and `M[6]` length of the point. -/
def queryOf (M : Mem) : Query :=
  { layer := M 1, type := M 2, logN := M 3, prec := M 4,
    point := (List.range (M 6)).map (fun j => M (M 5 + j)) }

/-- The read cost of a query: the sizes of the six header cells and their contents, and of the
point's addresses and entries. -/
def queryCost (M : Mem) : ℕ :=
  (List.range 6).foldr (fun a s => Nat.size (a + 1) + Nat.size (M (a + 1)) + s) 0 +
    (List.range (M 6)).foldr (fun j s => Nat.size (M 5 + j) + Nat.size (M (M 5 + j)) + s) 0

/-- Writes an oracle answer `(A, B)`: `M[7] = |A|`, `M[8] = [A < 0]`, `M[9] = |B|`,
`M[10] = [B < 0]`. -/
noncomputable def writeAns (M : Mem) (A B : ℤ) : Mem :=
  (((M.update 7 A.natAbs).update 8 (if A < 0 then 1 else 0)).update 9 B.natAbs).update 10
    (if B < 0 then 1 else 0)

/-- One step: the control outcome, the next configuration, the cost, and the oracle query made
(if any). -/
noncomputable def step (P : Program) (e : Env) (c : Cfg) : Ctl × Cfg × ℕ × Option Query :=
  let M := c.mem
  let nxt : Mem → Cfg := fun M' => ⟨c.pc + 1, M'⟩
  match P[c.pc]? with
  | none => (Ctl.reject, c, 1, none)
  | some (Instr.const d k) =>
      (Ctl.cont, nxt (M.update d k), 1 + Nat.size d + Nat.size k, none)
  | some (Instr.add d a b) =>
      (Ctl.cont, nxt (M.update d (M a + M b)),
        1 + Nat.size d + Nat.size a + Nat.size b + Nat.size (M a) + Nat.size (M b) +
          Nat.size (M a + M b), none)
  | some (Instr.monus d a b) =>
      (Ctl.cont, nxt (M.update d (M a - M b)),
        1 + Nat.size d + Nat.size a + Nat.size b + Nat.size (M a) + Nat.size (M b) +
          Nat.size (M a - M b), none)
  | some (Instr.load d a) =>
      (Ctl.cont, nxt (M.update d (M (M a))),
        1 + Nat.size d + Nat.size a + Nat.size (M a) + Nat.size (M (M a)), none)
  | some (Instr.store a b) =>
      (Ctl.cont, nxt (M.update (M a) (M b)),
        1 + Nat.size a + Nat.size (M a) + Nat.size b + Nat.size (M b), none)
  | some (Instr.jle a b tgt) =>
      (Ctl.cont, ⟨if M a ≤ M b then tgt else c.pc + 1, M⟩,
        1 + Nat.size a + Nat.size b + Nat.size (M a) + Nat.size (M b) + Nat.size tgt, none)
  | some (Instr.readIn d a) =>
      (Ctl.cont, nxt (M.update d (bitAt e.inst (M a))),
        3 + Nat.size d + Nat.size a + Nat.size (M a), none)
  | some (Instr.readMsg d a) =>
      (Ctl.cont, nxt (M.update d (bitAt e.msg (M a))),
        3 + Nat.size d + Nat.size a + Nat.size (M a), none)
  | some (Instr.readCoin d a) =>
      (Ctl.cont, nxt (M.update d (bitAt e.coin (M a))),
        3 + Nat.size d + Nat.size a + Nat.size (M a), none)
  | some Instr.oracle =>
      (Ctl.cont, nxt (writeAns M (e.oracle (queryOf M)).1 (e.oracle (queryOf M)).2),
        1 + queryCost M + Nat.size (e.oracle (queryOf M)).1.natAbs +
          Nat.size (e.oracle (queryOf M)).2.natAbs + 8, some (queryOf M))
  | some Instr.endPhase => (Ctl.endPhase, nxt M, 1, none)
  | some Instr.accept => (Ctl.accept, c, 1, none)
  | some Instr.reject => (Ctl.reject, c, 1, none)

/-- The result of running one phase. -/
structure PhaseRes where
  ctl : Ctl
  cfg : Cfg
  time : ℕ
  space : ℕ
  queries : List Query

/-- Run one phase for at most `fuel` steps (`none` if the fuel runs out). -/
noncomputable def runPhase (P : Program) (e : Env) : ℕ → Cfg → Option PhaseRes
  | 0, _ => none
  | f + 1, c =>
      match step P e c with
      | (Ctl.cont, c', t, q) =>
          (runPhase P e f c').map fun r =>
            { r with time := t + r.time, space := max (memSpace c.mem) r.space,
                     queries := q.toList ++ r.queries }
      | (ctl, c', t, q) =>
          some ⟨ctl, c', t, max (memSpace c.mem) (memSpace c'.mem), q.toList⟩

/-- The outcome of a complete run. -/
structure Outcome where
  accepted : Bool
  mem : Mem
  time : ℕ
  space : ℕ
  queries : List Query

/-- Run `n` remaining phases starting with phase `t`, each with at most `fuel` steps. -/
noncomputable def runPhases (P : Program) (inst : List Bool) (msg coin : ℕ → List Bool)
    (O : OracleAnswers) (fuel : ℕ) : ℕ → ℕ → Cfg → Option Outcome
  | 0, _, c => some ⟨false, c.mem, 0, memSpace c.mem, []⟩
  | n + 1, t, c =>
      match runPhase P ⟨inst, msg t, coin t, O⟩ fuel c with
      | none => none
      | some r =>
          match r.ctl with
          | Ctl.accept => some ⟨true, r.cfg.mem, r.time, r.space, r.queries⟩
          | Ctl.endPhase =>
              if n = 0 then some ⟨false, r.cfg.mem, r.time, r.space, r.queries⟩
              else (runPhases P inst msg coin O fuel n (t + 1) r.cfg).map fun o =>
                { o with time := r.time + o.time, space := max r.space o.space,
                         queries := r.queries ++ o.queries }
          | _ => some ⟨false, r.cfg.mem, r.time, r.space, r.queries⟩

/-- **A complete run** of program `P` on instance `inst` with `R` phases, messages `msg t` and
coins `coin t` (`t = 1, …, R`), oracle answers `O`, has outcome `o` (acceptance, final memory,
total time, space, and the list of oracle queries made). Runs start at `pc = 0` with empty memory.
The run is deterministic; the fuel only bounds the search. -/
def RAMRun (P : Program) (inst : List Bool) (R : ℕ) (msg coin : ℕ → List Bool)
    (O : OracleAnswers) (o : Outcome) : Prop :=
  ∃ fuel, runPhases P inst msg coin O fuel R 1 ⟨0, 0⟩ = some o

/-- The output written in memory: the bits `M[1] ≠ 0, …, M[M[0]] ≠ 0`. -/
def outputOf (M : Mem) : List Bool :=
  (List.range (M 0)).map (fun j => decide (M (j + 1) ≠ 0))

/-- A single (one-phase) run on input `inp` halts by `accept` with output `out`, total time
`time` and space `space`. Used for the honest prover and for stand-alone algorithms. -/
def SRun (P : Program) (inp : List Bool) (O : OracleAnswers) (out : List Bool)
    (time space : ℕ) : Prop :=
  ∃ o : Outcome, RAMRun P inp 1 (fun _ => []) (fun _ => []) O o ∧ o.accepted = true ∧
    out = outputOf o.mem ∧ time = o.time ∧ space = o.space

end ApproxGKR


