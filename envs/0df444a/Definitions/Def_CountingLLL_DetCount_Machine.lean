-- Prove2me | Definitions.Def_CountingLLL_DetCount_Machine
-- name    : CountingLLL_DetCount_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:07.315443+00:00
-- url     : https://prove2.me/theorems/c6d71495-9bf4-427d-b728-24ed14e15f5a
-- title:
--   A bit-cost random-access machine with an evaluation oracle
-- statement:
--   This is the computational model of §2.5. A **program** is a finite list of instructions over integer registers $\mathrm{reg}:\mathbb N\to\mathbb Z$ and integer memory $M:\mathbb Z\to\mathbb Z$: literal load, addition, subtraction, multiplication, floor division and remainder, compare-and-branch, jump, indirect load and store, an **oracle query**, and halt with an output pair of integers $(a,b)$ (a rational $a/b$).
--
--   Costs are binary. With $B$ one plus the total bit length of the operands, result and memory address accessed, every instruction costs $B$, and multiplication, division and remainder cost $B^2$. A query `query d c base` asks the evaluation oracle of Assumption 1 whether constraint $\mathrm{reg}\,c$ is satisfied by the local assignment stored at $M[\mathrm{reg\,base}+j]$, $j<|\mathrm{vbl}(c)|$, in increasing variable order. It adds $1$ to the oracle counter and is charged the bit lengths of the cells and addresses it reads. An invalid query returns $0$. A separate counter records the number of executed instructions. For the graph-operation bound of Lemma 4.2, `IsGraphProgram` restricts the program to literal loads, addition and subtraction of indices, comparison/branch, jump, indirect loads/stores, and halt; multiplication, division, remainder and evaluation-oracle queries are excluded.
--
--   The constraint functions of the instance are reachable only through the query instruction. The explicit input lists $n$, $m$, the domain sizes, every scope and every variable-incidence list. The counting program also receives a precision request
--   $$s(\varepsilon)=\max\big(1,\lceil\log_2(1/\varepsilon)\rceil\big),$$
--   which represents the dyadic tolerance $\eta=2^{-s}$ with $\varepsilon/2<\eta\le\varepsilon$. The module also fixes the layout of shared dependency lists used in Lemma 4.2, and the membership-array convention used in Lemma 4.1.
--
--   All running-time and oracle-cost statements of the mission are about runs of this machine.
--
--   **Formalization Note** After `halt`, or when the program counter leaves the program, the state stutters at no cost, so the counters of a halted run are final.
-- source:
--   Hongyang Liu, Chunyang Wang, Yitong Yin, Yiyao Zhang, Can Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 submission #442 (October 2026), §2.5 (computational model), Assumption 1, Theorem 1.2, PDF p. 8 (printed p. 7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_DetCount_Expansion

set_option autoImplicit false

namespace CountingLLL.DetCount

/-! # A bit-cost oracle RAM (§2.5)

A random-access machine with integer registers and integer memory, binary (logarithmic) cost for
arithmetic and data access, and unit-cost calls to the evaluation oracle of Assumption 1. The
constraint predicates of the instance are reachable only through the `query` instruction. -/

/-- Instructions. Register indices, jump targets and literals are constants of the program; no
instruction carries a function or a proof.
* `lit d z`: `reg d := z`.
* `add d a b`, `sub d a b`, `mul d a b`: `reg d := reg a ∘ reg b`.
* `div d a b`, `mod d a b`: floor division and floor remainder (`Int.fdiv`, `Int.fmod`;
  total, with `x / 0 = 0` and `x mod 0 = x`).
* `jlt a b t`: jump to `t` if `reg a < reg b`, otherwise fall through.
* `jmp t`: jump to `t`.
* `load d a`: `reg d := M[reg a]`; `store a b`: `M[reg a] := reg b`.
* `query d c base`: evaluation-oracle call on constraint `reg c` with the local assignment read
  from `M[reg base + j]`, `j < |vbl(c)|`, in increasing order of the scope's variables; writes `1`
  to `reg d` if the constraint is satisfied and `0` otherwise (also `0` on an invalid query).
* `halt a b`: stop with output `(reg a, reg b)` (a rational is a pair of integers). -/
inductive Instr where
  | lit (d : ℕ) (z : ℤ)
  | add (d a b : ℕ)
  | sub (d a b : ℕ)
  | mul (d a b : ℕ)
  | div (d a b : ℕ)
  | mod (d a b : ℕ)
  | jlt (a b t : ℕ)
  | jmp (t : ℕ)
  | load (d a : ℕ)
  | store (a b : ℕ)
  | query (d c base : ℕ)
  | halt (a b : ℕ)
  deriving DecidableEq

/-- A program is a finite list of instructions; `pc` indexes into it. -/
abbrev Program : Type := List Instr

/-- The graph-operation fragment used in Lemma 4.2. A primitive reads/writes a word or a
membership mark, compares indices, adds/subtracts indices for addressing and iteration, or
controls the finite program. Multiplication, division, remainder and evaluation-oracle queries
are excluded: counting arbitrary RAM instructions would not specify graph-operation cost. -/
def IsGraphProgram (P : Program) : Prop :=
  ∀ ins ∈ P, match ins with
    | .lit _ _ | .add _ _ _ | .sub _ _ _ | .jlt _ _ _ | .jmp _ |
      .load _ _ | .store _ _ | .halt _ _ => True
    | .mul _ _ _ | .div _ _ _ | .mod _ _ _ | .query _ _ _ => False

/-- Machine state: program counter, registers, memory, oracle-call counter, bit-time counter,
instruction counter (one per executed instruction; graph operations for an `IsGraphProgram`), and the
output (`none` while running). -/
structure State where
  pc : ℕ
  reg : ℕ → ℤ
  mem : ℤ → ℤ
  oracle : ℕ
  time : ℕ
  steps : ℕ
  out : Option (ℤ × ℤ)

/-- Binary length of an integer: the number of bits of `|z|` (`0` for `z = 0`). -/
def bl (z : ℤ) : ℕ := Nat.size z.natAbs

/-- The variables of `vbl(c)` in increasing order. -/
noncomputable def scopeList (Φ : CSP) (c : Fin Φ.m) : List (Fin Φ.n) :=
  (Φ.scope c).sort (· ≤ ·)

/-- The oracle's answer for constraint `c` on the local values `val j` (`j` = position of the
variable in `scopeList`): `false` if some value lies outside its domain `{0, …, q_v − 1}`,
otherwise the constraint's predicate on that local assignment. -/
noncomputable def oracleAnswer (Φ : CSP) (c : Fin Φ.m) (val : ℕ → ℤ) : Bool := by
  classical
  exact
    if ∀ v ∈ Φ.scope c, 0 ≤ val ((scopeList Φ c).idxOf v) ∧
        val ((scopeList Φ c).idxOf v) < (Φ.q v : ℤ) then
      Φ.pred c (fun v => ⟨(val ((scopeList Φ c).idxOf v.1)).toNat % Φ.q v.1,
        Nat.mod_lt _ (by have := Φ.two_le_q v.1; omega)⟩)
    else false

/-- One step of the machine on oracle instance `Φ` and program `P`. After `halt` (or when `pc`
leaves the program) the state stutters at no cost. Costs, with `B = 1 + ` total bit length of the
accessed operands, result and memory address:
`lit`, `add`, `sub`, comparisons/jumps, `load`, `store`, `halt` cost `B`; `mul`, `div`, `mod`
cost `B²`; `query` adds `1` to the oracle counter and charges
`1 + bl(reg c) + bl(reg base) + Σ_{j < |vbl(c)|} (bl(reg base + j) + bl(M[reg base + j]))`
(only the first two terms for an invalid constraint index). Every executed instruction adds `1`
to `steps`. The predicates of `Φ` occur only in the `query` branch. -/
noncomputable def step (Φ : CSP) (P : Program) (s : State) : State :=
  match s.out with
  | some _ => s
  | none =>
    match P[s.pc]? with
    | none => s
    | some ins =>
      match ins with
      | .lit d z =>
        { s with reg := Function.update s.reg d z, pc := s.pc + 1,
                 time := s.time + (1 + bl z), steps := s.steps + 1 }
      | .add d a b =>
        let z := s.reg a + s.reg b
        { s with reg := Function.update s.reg d z, pc := s.pc + 1,
                 time := s.time + (1 + bl (s.reg a) + bl (s.reg b) + bl z),
                 steps := s.steps + 1 }
      | .sub d a b =>
        let z := s.reg a - s.reg b
        { s with reg := Function.update s.reg d z, pc := s.pc + 1,
                 time := s.time + (1 + bl (s.reg a) + bl (s.reg b) + bl z),
                 steps := s.steps + 1 }
      | .mul d a b =>
        let z := s.reg a * s.reg b
        { s with reg := Function.update s.reg d z, pc := s.pc + 1,
                 time := s.time + (1 + bl (s.reg a) + bl (s.reg b) + bl z) ^ 2,
                 steps := s.steps + 1 }
      | .div d a b =>
        let z := Int.fdiv (s.reg a) (s.reg b)
        { s with reg := Function.update s.reg d z, pc := s.pc + 1,
                 time := s.time + (1 + bl (s.reg a) + bl (s.reg b) + bl z) ^ 2,
                 steps := s.steps + 1 }
      | .mod d a b =>
        let z := Int.fmod (s.reg a) (s.reg b)
        { s with reg := Function.update s.reg d z, pc := s.pc + 1,
                 time := s.time + (1 + bl (s.reg a) + bl (s.reg b) + bl z) ^ 2,
                 steps := s.steps + 1 }
      | .jlt a b t =>
        { s with pc := if s.reg a < s.reg b then t else s.pc + 1,
                 time := s.time + (1 + bl (s.reg a) + bl (s.reg b)),
                 steps := s.steps + 1 }
      | .jmp t =>
        { s with pc := t, time := s.time + 1, steps := s.steps + 1 }
      | .load d a =>
        let addr := s.reg a
        let v := s.mem addr
        { s with reg := Function.update s.reg d v, pc := s.pc + 1,
                 time := s.time + (1 + bl addr + bl v), steps := s.steps + 1 }
      | .store a b =>
        let addr := s.reg a
        let v := s.reg b
        { s with mem := Function.update s.mem addr v, pc := s.pc + 1,
                 time := s.time + (1 + bl addr + bl v), steps := s.steps + 1 }
      | .query d c base =>
        let ci := s.reg c
        let b0 := s.reg base
        if h : 0 ≤ ci ∧ ci.toNat < Φ.m then
          let cc : Fin Φ.m := ⟨ci.toNat, h.2⟩
          let len := (Φ.scope cc).card
          let ans := oracleAnswer Φ cc (fun j => s.mem (b0 + j))
          { s with reg := Function.update s.reg d (if ans then 1 else 0), pc := s.pc + 1,
                   oracle := s.oracle + 1,
                   time := s.time + (1 + bl ci + bl b0 +
                     ∑ j ∈ Finset.range len, (bl (b0 + j) + bl (s.mem (b0 + j)))),
                   steps := s.steps + 1 }
        else
          { s with reg := Function.update s.reg d 0, pc := s.pc + 1,
                   oracle := s.oracle + 1, time := s.time + (1 + bl ci + bl b0),
                   steps := s.steps + 1 }
      | .halt a b =>
        { s with out := some (s.reg a, s.reg b),
                 time := s.time + (1 + bl (s.reg a) + bl (s.reg b)), steps := s.steps + 1 }

/-- The state after `t` steps. The machine is deterministic. -/
noncomputable def run (Φ : CSP) (P : Program) (s : State) (t : ℕ) : State :=
  (step Φ P)^[t] s

/-- Initial state with memory `M` and registers `R`; all counters zero, no output. -/
def initState (M : ℤ → ℤ) (R : ℕ → ℤ) : State :=
  ⟨0, R, M, 0, 0, 0, none⟩

/-- A list of words laid out at addresses `0, 1, 2, …`; every other cell holds `0`. -/
def listMem (w : List ℤ) : ℤ → ℤ :=
  fun a => if 0 ≤ a then w.getD a.toNat 0 else 0

/-- The `len` cells starting at address `a`. -/
def readList (M : ℤ → ℤ) (a : ℤ) (len : ℕ) : List ℤ :=
  (List.range len).map (fun j => M (a + j))

/-- The constraints containing variable `v`, in increasing order (its incidence list). -/
noncomputable def incidence (Φ : CSP) (v : Fin Φ.n) : List (Fin Φ.m) := by
  classical
  exact (Finset.univ.filter (fun c => v ∈ Φ.scope c)).sort (· ≤ ·)

/-- The explicit input encoding of `Φ` (§2.5), as a flat word list:
`n, m, q_0, …, q_{n−1}`, then for each constraint `c` (in index order) `|vbl(c)|` followed by the
variables of `vbl(c)` in increasing order, then for each variable `v` the number of constraints
containing `v` followed by those constraints in increasing order. The predicates are not
part of the input; they are reachable only by `query`. -/
noncomputable def cspWords (Φ : CSP) : List ℤ :=
  [(Φ.n : ℤ), (Φ.m : ℤ)] ++
  (List.finRange Φ.n).map (fun v => (Φ.q v : ℤ)) ++
  ((List.finRange Φ.m).map (fun c =>
    ((Φ.scope c).card : ℤ) :: (scopeList Φ c).map (fun v => (v.val : ℤ)))).flatten ++
  ((List.finRange Φ.n).map (fun v =>
    ((incidence Φ v).length : ℤ) :: (incidence Φ v).map (fun c => (c.val : ℤ)))).flatten

/-- The precision request for a real accuracy `ε ∈ (0,1)`: `s(ε) = max(1, ⌈log₂(1/ε)⌉)`. It
represents the dyadic tolerance `η = 2^{−s}`, for which `ε/2 < η ≤ ε`. -/
noncomputable def precisionCode (ε : ℝ) : ℕ :=
  max 1 ⌈Real.logb 2 (1 / ε)⌉₊

/-- Input memory of the counting program of Theorem 1.2: the precision request `s` at address
`0`, followed by `cspWords Φ` from address `1` on. -/
noncomputable def countingInput (Φ : CSP) (s : ℕ) : ℤ → ℤ :=
  listMem ((s : ℤ) :: cspWords Φ)

/-- Input memory of a preprocessing program (Lemma 4.1): `cspWords Φ` from address `0` on. -/
noncomputable def preprocessInput (Φ : CSP) : ℤ → ℤ :=
  listMem (cspWords Φ)

/-- Start memory of the marginal estimator of Lemma 4.1: the final memory `M` of the shared
preprocessing at nonnegative addresses, and the membership array of the current subfamily `E` at
the negative addresses (`M[−1−c] = 1` iff `c ∈ E`, for `c < m`; `0` elsewhere). -/
noncomputable def estimatorMem (Φ : CSP) (M : ℤ → ℤ) (E : Finset (Fin Φ.m)) : ℤ → ℤ := by
  classical
  exact fun a =>
    if 0 ≤ a then M a
    else if h : (-1 - a).toNat < Φ.m then (if (⟨(-1 - a).toNat, h⟩ : Fin Φ.m) ∈ E then 1 else 0)
    else 0

/-- Start registers of the marginal estimator: `reg 0 = c₀`, `reg 1 = L`, all others `0`. -/
def estimatorRegs (c₀ L : ℕ) : ℕ → ℤ :=
  fun i => if i = 0 then (c₀ : ℤ) else if i = 1 then (L : ℤ) else 0

/-- The sorted neighbour list of `c` in the dependency graph `G(C)` of the whole formula. -/
noncomputable def nbrList (Φ : CSP) (c : Fin Φ.m) : List (Fin Φ.m) :=
  (Φ.nbr Finset.univ c).sort (· ≤ ·)

/-- The adjacency blocks: for each constraint `c`, its degree in `G(C)` followed by its sorted
neighbour list. -/
noncomputable def nbrBlocks (Φ : CSP) : List (List ℤ) :=
  (List.finRange Φ.m).map (fun c =>
    ((nbrList Φ c).length : ℤ) :: (nbrList Φ c).map (fun c' => (c'.val : ℤ)))

/-- The graph-access layout used in Lemma 4.2 (shared dependency lists plus a membership array
for the current family), as a flat word list:
`m, c₀, |T|`, the members of `T` in increasing order, the membership bits of `E`
(`1` if `c ∈ E`, else `0`, for `c = 0, …, m−1`), an offset table (the address where the block of
`c` begins, for `c = 0, …, m−1`), then the blocks `nbrBlocks Φ` in index order. -/
noncomputable def graphWords (Φ : CSP) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m)
    (T : Finset (Fin Φ.m)) : List ℤ := by
  classical
  exact
    let base : ℕ := 3 + T.card + 2 * Φ.m
    [(Φ.m : ℤ), (c₀.val : ℤ), (T.card : ℤ)] ++
    (T.sort (· ≤ ·)).map (fun c => (c.val : ℤ)) ++
    (List.finRange Φ.m).map (fun c => if c ∈ E then (1 : ℤ) else 0) ++
    (List.finRange Φ.m).map (fun c =>
      ((base + (((nbrBlocks Φ).take c.val).map List.length).sum : ℕ) : ℤ)) ++
    (nbrBlocks Φ).flatten

end CountingLLL.DetCount


