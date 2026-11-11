-- Prove2me | Definitions.Def_MongeApprox_Sparsify_Machine
-- name    : MongeApprox_Sparsify_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:01:57.304001+00:00
-- url     : https://prove2.me/theorems/8dfcfc43-2f74-4c4d-a73d-f87826720441
-- title:
--   The oracle real RAM: SmaleNinth core with integer memory, int→real cast, a matrix-entry oracle and halt; input and output layouts (§3 Model of Computation)
-- statement:
--   The model of computation of §3: a word RAM extended with real registers, where $+,-,\times,\div$ and comparisons of reals and the integer-to-real conversion take constant time, and reals cannot be converted to integers. A **program** is one fixed finite list of instructions: the published real-RAM core (`SmaleNinth.RAMInstr`: real constants, $+,-,\times,\div$, indirect real load/store through integer pointers, pointer set/copy/increment/decrement, branches $r\le0$ and $p\le p'$), integer $+$ and $-$, integer memory load/store, the cast of an integer to a real, the oracle call `entry d a b` setting $r_d:=M_{p_a,p_b}$ for the $p\times q$ matrix $M$, and `halt`. Every executed instruction, the oracle call included, costs one step; entry queries are also counted separately. A program is **admissible** if its real literals are rational and it halts only through `halt`.
--
--   **Formalization Note.** An oracle call with an index outside $[0..p)\times[0..q)$, an invalid program counter, or the core's `accept`/`reject` leave the run stuck forever. There is no integer $\times$, $\div$, bit operation, floor, real-to-integer conversion, square root, logarithm or randomness: fewer operations than the paper's word RAM, so an existence claim over these programs is stronger. **Input** (`init ints reals`): integer cell $k\ge0$ holds `ints[k]`, real cell $k\ge0$ holds `reals[k]`, everything else $0$. **Output**: integer output $k$ is integer cell $-1-k$, real output $k$ is real cell $-1-k$. `HaltsWithin P M s₀ T Post`: the run executes `halt` after some $k\le T$ steps and the halted state satisfies `Post`. `queryState s i j` restarts a halted state for one entry query (memories kept, $p_0:=i$, $p_1:=j$). `OutputsCondensed M̂`: real outputs $0..q-1$ hold the top row, $q..q+p-1$ the leftmost column; integer output $0$ is the core size $N$; for $t<N$, integer outputs $2t+1,2t+2$ and real output $q+p+t$ hold the triple $(i_t,j_t,\widehat M^\square_{i_tj_t})$, the triples listing every nonzero density entry exactly once and nothing else. `OutputsReplacement rows cols μ̂`: a count $N$, then for $t<N$ ranks $(k_t,l_t)$ into the lists of nonzero rows and columns and a value $v_t$ (real output $t$), listing each nonzero entry of $\widehat\mu$ exactly once.
-- source:
--   Gorbachev 2026, Edit Distance Approximation: Subquadratic Factor Three and Monge Approximation Schemes (PDF sha256 b7eeb435…), §3 Model of Computation, printed p. 18 (PDF 20); Theorem 1.8, printed p. 5 (PDF 7); Theorem 7.3 and Fact 7.4, printed p. 35 (PDF 37)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_MongeApprox_Sparsify_Monge

/-!
# The oracle real RAM (word RAM with real registers and a matrix-entry oracle)

Gorbachev, *Edit Distance Approximation: Subquadratic Factor Three and Monge Approximation Schemes*
(2026, PDF sha256 b7eeb435…), §3 "Model of Computation", printed p. 18 (PDF 20): "We work in the
word RAM model with machine words of Ω(log N) bits. … we extend this model with registers that
store real numbers, as in the real RAM model … Additions, subtractions, multiplications,
divisions, and comparisons of real numbers take constant time, as does converting an integer to a
real number, but real numbers cannot be converted to integers, for example by rounding."
"Given oracle access to the entries of M" (Theorem 1.8, printed p. 5 / PDF 7; Theorem 7.3 and
Fact 7.4, printed p. 35 / PDF 37).

Conventions.
* The core is the published `SmaleNinth.RAMInstr` (real registers, real memory `ℤ → ℝ` addressed
  through integer pointer registers, `+ − × ÷` on reals, real constants, indirect real load/store,
  pointer set/copy/increment/decrement, the branches `r ≤ 0` and `p ≤ p′`). The extension follows
  the shape of the published `DoublingMST.Instr`: pointer `+` and `−`, an integer memory
  `ℤ → ℤ` with load and store through pointers, the cast of a pointer to a real, the entry oracle,
  and `halt`.
* Integer registers are the core's pointer registers, over unbounded `ℤ`; there is no integer
  `×`, `÷`, shift or bit operation, no floor, no real-to-integer conversion, no square root, log or
  exponential, and no randomness. Fewer operations than the paper's word RAM make an existence
  claim over these programs stronger.
* The oracle `entry dst a b` sets `r[dst] := M_{p[a], p[b]}` for the `p × q` matrix `M`; if
  `p[a] ∉ [0..p)` or `p[b] ∉ [0..q)` the run is stuck forever. It counts as one step and one
  entry query (`queries`).
* Cost: every executed instruction costs one step (`work`), including jumps, oracle calls and
  `halt`. An invalid program counter makes the run stuck forever (charged). After `halt` the
  state stutters.
* `Admissible P`: every real literal is rational and the core's `accept`/`reject` do not occur
  (a run stops only through `halt`). Irrational parameters are passed as real input.
* Input (`init ints reals`): integer memory cell `k ≥ 0` holds entry `k` of `ints`, real memory
  cell `k ≥ 0` entry `k` of `reals`; all other cells, all registers, and the counters are `0`.
* Output: entry `k` of an integer output list is integer cell `−1 − k` (`intOut`), entry `k` of a
  real output list is real cell `−1 − k` (`realOut`).
* `HaltsWithin P M s₀ T Post`: the run of `P` with oracle `M` from `s₀` executes `halt` after some
  `k ≤ T` steps and the halted state satisfies `Post`.
* `queryState s i j`: the state `s` (memory and registers kept) restarted at program counter `0`
  with counters and flags cleared and `p[0] := i`, `p[1] := j`; used to run an entry-query
  program against data prepared by an earlier program (Fact 7.4's "oracles for F and G").
* `OutputsCondensed M̂ s` (the condensed representation of a `p × q` matrix `M̂`): real outputs
  `0, …, q − 1` are the top row `M̂_{0j}`, real outputs `q, …, q + p − 1` the leftmost column
  `M̂_{i0}`; integer output `0` is the core size `N ≥ 0`, integer outputs `2t + 1, 2t + 2` and real
  output `q + p + t` (`t < N`) are the triple `(i_t, j_t, M̂□_{i_t j_t})`; the triples list every
  position with `M̂□_ij ≠ 0` exactly once, and no other position.
* `OutputsReplacement rows cols µ̂ s` (Lemma 7.5's output): integer output `0` is a count `N ≥ 0`;
  for `t < N`, integer outputs `2t + 1, 2t + 2` are ranks `k_t < |rows|`, `l_t < |cols|` and real
  output `t` is a value `v_t`; the positions `(rows[k_t], cols[l_t])` list every nonzero entry of
  `µ̂` exactly once, with value `v_t`.
-/

namespace MongeApprox.Sparsify

/-- An instruction. Register and pointer arguments are natural numbers.
* `core i`: a `SmaleNinth` real-RAM instruction.
* `pointerAdd d a b`, `pointerSub d a b`: `p[d] := p[a] ± p[b]`.
* `integerLoad d a`, `integerStore a b`: `p[d] := I[p[a]]`, `I[p[a]] := p[b]`.
* `pointerReal d a`: `r[d] := (p[a] : ℝ)`.
* `entry d a b`: `r[d] := M_{p[a], p[b]}` (one entry query).
* `halt`: stop. -/
inductive Instr where
  | core (instruction : SmaleNinth.RAMInstr)
  | pointerAdd (dst a b : ℕ)
  | pointerSub (dst a b : ℕ)
  | integerLoad (dst address : ℕ)
  | integerStore (address src : ℕ)
  | pointerReal (dst pointer : ℕ)
  | entry (dst a b : ℕ)
  | halt

/-- A program: one finite list of instructions, fixed before the input. -/
abbrev Program := List Instr

/-- Every real literal is rational, and the core halting instructions `accept`/`reject` do not
occur (the machine stops only through `halt`). -/
def Admissible (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ value) => ∃ r : ℚ, value = (r : ℝ)
    | .core .accept | .core .reject => False
    | _ => True

/-- The static core table of `P`: extension instructions are placeholders, always dispatched by
`step`. -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- A machine state: the core configuration, integer memory, the halted and stuck flags, the
number of executed instructions and the number of entry queries. -/
structure State where
  core : SmaleNinth.RAMConfig
  integerMemory : ℤ → ℤ
  halted : Bool
  stuck : Bool
  work : ℕ
  queries : ℕ

/-- One step of `P` with entry oracle `M` (a `p × q` matrix). -/
noncomputable def step {p q : ℕ} (P : Program) (M : Matrix (Fin p) (Fin q) ℝ)
    (s : State) : State :=
  if s.halted || s.stuck then s else
    let t := { s with
      work := s.work + 1
      core := { s.core with pc := s.core.pc + 1 } }
    match P[s.core.pc]? with
    | none => { s with work := s.work + 1, stuck := true }
    | some (.core _) =>
        { t with core := SmaleNinth.RAMStep (coreProgram P) s.core }
    | some (.pointerAdd dst a b) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs dst (s.core.ptrs a + s.core.ptrs b) } }
    | some (.pointerSub dst a b) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs dst (s.core.ptrs a - s.core.ptrs b) } }
    | some (.integerLoad dst a) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs dst (s.integerMemory (s.core.ptrs a)) } }
    | some (.integerStore a b) =>
        { t with integerMemory :=
            Function.update s.integerMemory (s.core.ptrs a) (s.core.ptrs b) }
    | some (.pointerReal dst a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs dst (s.core.ptrs a : ℝ) } }
    | some (.entry dst a b) =>
        if h : (0 ≤ s.core.ptrs a ∧ (s.core.ptrs a).toNat < p) ∧
            (0 ≤ s.core.ptrs b ∧ (s.core.ptrs b).toNat < q) then
          { t with
            queries := s.queries + 1
            core := { t.core with
              regs := Function.update s.core.regs dst
                (M ⟨(s.core.ptrs a).toNat, h.1.2⟩ ⟨(s.core.ptrs b).toNat, h.2.2⟩) } }
        else { s with work := s.work + 1, stuck := true }
    | some .halt => { t with halted := true }

/-- The state after `k` steps from `s₀`. -/
noncomputable def run {p q : ℕ} (P : Program) (M : Matrix (Fin p) (Fin q) ℝ)
    (s₀ : State) (k : ℕ) : State :=
  (step P M)^[k] s₀

/-- The initial state on integer input `ints` and real input `reals`: integer cell `k ≥ 0` holds
`ints[k]`, real cell `k ≥ 0` holds `reals[k]`, everything else (registers, other cells, counters,
program counter) is `0`. -/
def init (ints : List ℤ) (reals : List ℝ) : State where
  core := ⟨0, fun _ => 0, fun _ => 0, fun k => if 0 ≤ k then reals.getD k.toNat 0 else 0⟩
  integerMemory := fun k => if 0 ≤ k then ints.getD k.toNat 0 else 0
  halted := false
  stuck := false
  work := 0
  queries := 0

/-- `P`, started in `s₀` with entry oracle `M`, executes `halt` after some `k ≤ T` steps and the
halted state satisfies `Post`. -/
def HaltsWithin {p q : ℕ} (P : Program) (M : Matrix (Fin p) (Fin q) ℝ) (s₀ : State) (T : ℝ)
    (Post : State → Prop) : Prop :=
  ∃ k : ℕ, (k : ℝ) ≤ T ∧ (run P M s₀ k).halted = true ∧ Post (run P M s₀ k)

/-- Restart the data in `s` for one entry query `(i, j)`: program counter `0`, flags and counters
cleared, `p[0] := i`, `p[1] := j`; all other registers and both memories are kept. -/
def queryState (s : State) (i j : ℤ) : State where
  core := { s.core with
    pc := 0
    ptrs := Function.update (Function.update s.core.ptrs 0 i) 1 j }
  integerMemory := s.integerMemory
  halted := false
  stuck := false
  work := 0
  queries := 0

/-- Entry `k` of the integer output list: integer cell `−1 − k`. -/
def intOut (s : State) (k : ℕ) : ℤ :=
  s.integerMemory (-1 - (k : ℤ))

/-- Entry `k` of the real output list: real cell `−1 − k`. -/
def realOut (s : State) (k : ℕ) : ℝ :=
  s.core.mem (-1 - (k : ℤ))

/-- The list `t ↦ (pos t, val t)`, `t < N`, enumerates exactly the nonzero entries of `f`, each
once: every listed position has `f (pos t) = val t ≠ 0`, positions are distinct, and every
position with a nonzero value is listed. -/
def ListsExactly (f : ℤ × ℤ → ℝ) (N : ℕ) (pos : ℕ → ℤ × ℤ) (val : ℕ → ℝ) : Prop :=
  (∀ t < N, f (pos t) = val t ∧ val t ≠ 0) ∧
  (∀ t < N, ∀ t' < N, pos t = pos t' → t = t') ∧
  (∀ z, f z ≠ 0 → ∃ t < N, pos t = z)

/-- The halted state `s` holds the condensed representation of the `p × q` matrix `M̂`: the top
row at real outputs `0, …, q − 1`, the leftmost column at real outputs `q, …, q + p − 1`, the core
size `N` at integer output `0`, and the core triples `(i_t, j_t, M̂□_{i_t j_t})`, `t < N`, at
integer outputs `2t + 1`, `2t + 2` and real output `q + p + t`, listing every nonzero density
entry exactly once. -/
def OutputsCondensed {p q : ℕ} (Mhat : Matrix (Fin p) (Fin q) ℝ) (s : State) : Prop :=
  (∀ (i : Fin p) (j : Fin q), (i : ℕ) = 0 → realOut s j = Mhat i j) ∧
  (∀ (i : Fin p) (j : Fin q), (j : ℕ) = 0 → realOut s (q + i) = Mhat i j) ∧
  0 ≤ intOut s 0 ∧
  ListsExactly (densityZ Mhat) (intOut s 0).toNat
    (fun t => (intOut s (2 * t + 1), intOut s (2 * t + 2))) (fun t => realOut s (q + p + t))

/-- The halted state `s` lists the nonzero entries of `µ̂` (Lemma 7.5's output): integer output `0`
is a count `N`; for `t < N` integer outputs `2t + 1`, `2t + 2` are ranks `k_t < |rows|`,
`l_t < |cols|`, real output `t` is a value, and the positions `(rows[k_t], cols[l_t])` enumerate
every nonzero entry of `µ̂` exactly once with its value. -/
def OutputsReplacement (rows cols : List ℤ) (μhat : ℤ × ℤ → ℝ) (s : State) : Prop :=
  0 ≤ intOut s 0 ∧
  (∀ t < (intOut s 0).toNat,
    0 ≤ intOut s (2 * t + 1) ∧ (intOut s (2 * t + 1)).toNat < rows.length ∧
    0 ≤ intOut s (2 * t + 2) ∧ (intOut s (2 * t + 2)).toNat < cols.length) ∧
  ListsExactly μhat (intOut s 0).toNat
    (fun t => (rows.getD (intOut s (2 * t + 1)).toNat 0, cols.getD (intOut s (2 * t + 2)).toNat 0))
    (fun t => realOut s t)

end MongeApprox.Sparsify


