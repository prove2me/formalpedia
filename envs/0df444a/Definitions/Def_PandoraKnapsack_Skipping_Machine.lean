-- Prove2me | Definitions.Def_PandoraKnapsack_Skipping_Machine
-- name    : PandoraKnapsack_Skipping_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:24:11.968489+00:00
-- url     : https://prove2.me/theorems/7460ec8d-4433-4fc5-8d20-d619c145caa0
-- title:
--   Costed real-RAM model with coefficient access and uniform draws
-- statement:
--   The model in which "polynomial-time algorithm" is stated. A program is a finite list of instructions of the published real pointer machine `SmaleNinth.RAMInstr` (unit-cost exact arithmetic and comparisons on reals, integer pointers moved by ±1, indirect memory ℤ → ℝ, `accept` halts), extended by exact access to the instance coefficients v_i, p_i^j, Pr[s_i^j ≤ r] and E[min{s_i^j,r}], uniform [0,1] draws, and copying a pointer into a real register. Item and choice indices for coefficient access are held in pointers; an out-of-range index returns zero.
--
--   Every executed instruction costs one step, including each coefficient query and each draw. Optimization is performed by the program's arithmetic, comparisons and memory instructions within the same step bound. There is no LP-solving instruction or external optimizer. This is the exact-coefficient-access arithmetic model; it does not assert a bit-complexity bound for arbitrary real data.
--
--   Memory initially holds n, m and T in cells 0, 1 and 2 and zero elsewhere. Input size is n + m + bitlength(T). The output encodes a list of item, choice and threshold triples; non-natural or out-of-range entries fail to decode. A B-step run uses at most B independent uniform draws, with law `drawLaw B`. `outputPolicy` returns the decoded list, defaulting to the empty list if decoding fails; the theorem separately requires successful decoding and policy validity for every draw sequence.
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen (2026), Pandora's Knapsack via Simple Policies, supplied PDF (STOC 2027 submission), SHA256 45e5830b173d687c08d5175988af81bf660c693ff805b1d2e7bc213140d27a2d, Theorem 5.1, printed p. 21 (PDF 23), and Appendix B.1, printed pp. 39–41 (PDF 41–43); computational model fixed by the formalization

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_PandoraKnapsack_Skipping_Policies

open MeasureTheory

namespace PandoraKnapsack.Skipping

/-! **The computational model of "polynomial-time algorithm for MPK".**

Barak et al. (2026), *Pandora's Knapsack via Simple Policies*, supplied PDF (SHA256
45e5830b…7a2d): Theorem 5.1, printed p. 21 (PDF 23), and Appendix B.1, printed pp. 39–41
(PDF 41–43), which solves "a compact LP that may be solved in polynomial time". The paper fixes
no machine model or input-access interface; this module fixes one.

**Model.** A program is a finite list of instructions of the published real pointer machine
`SmaleNinth.RAMInstr` (unit-cost exact arithmetic and comparisons on reals, pointers moved by
`±1`, indirect memory `ℤ → ℝ`), extended by
* exact *coefficient access* to the instance: the value `v_i`, the cost `p_i^j`, the CDF
  `Pr[s_i^j ≤ r]` and the truncated mean `E[min{s_i^j, r}]` at a real argument `r`, for item and
  choice indices held in pointer registers (an index out of range returns `0`);
* `uniform dst`: one independent uniform draw from `[0, 1]`;
* `ptrReal dst q`: copy the integer in pointer `q` into a real register.

**Costs.** Every executed instruction costs one step. There is no optimization oracle: any
LP computation must be implemented using the listed instructions and its arithmetic, comparisons
and memory accesses all count toward the step bound. Coefficient queries and uniform draws each
cost one step. This is an exact-coefficient-access arithmetic model, not a bit-complexity model.

**Input and output.** Memory initially holds `n`, `m`, `T` in cells `0, 1, 2` and `0`
elsewhere; the input size is `n + m + bitlength(T)`. The program halts on `accept`. The output
is read from memory: cell `0` holds the length `ℓ`, and cells `1 + 3r, 2 + 3r, 3 + 3r` hold the
item, choice and threshold of the `r`-th triple; each must be a natural number. -/
/-- An instruction: a real-RAM instruction or one of the MPK extensions. -/
inductive Instr where
  /-- A real pointer-machine instruction (`accept` halts). -/
  | core (i : SmaleNinth.RAMInstr)
  /-- `r[dst] := v_{p[q]}`. -/
  | value (dst q : ℕ)
  /-- `r[dst] := p_{p[q]}^{p[q']}`. -/
  | cost (dst q q' : ℕ)
  /-- `r[dst] := Pr[s_{p[q]}^{p[q']} ≤ r[src]]`. -/
  | cdf (dst q q' src : ℕ)
  /-- `r[dst] := E[min{s_{p[q]}^{p[q']}, r[src]}]`. -/
  | truncMean (dst q q' src : ℕ)
  /-- `r[dst] :=` the next uniform draw. -/
  | uniform (dst : ℕ)
  /-- `r[dst] := p[q]`. -/
  | ptrReal (dst q : ℕ)

/-- A program, executed from position `0`. -/
abbrev Program := List Instr

/-- A machine state: the real-RAM configuration and the number of uniform draws used so far. -/
structure State where
  core : SmaleNinth.RAMConfig
  draws : ℕ

/-- The real-RAM table of a program; extension instructions are placeholders dispatched by
`step`. -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun ins => match ins with
    | .core i => i
    | _ => .const 0 0

/-- Read a natural number from a memory cell (`none` unless the cell holds one). -/
noncomputable def readNat (x : ℝ) : Option ℕ := by
  classical
  exact if h : ∃ k : ℕ, (k : ℝ) = x then some (Nat.find h) else none

/-- The index held in a pointer, if it lies in `{0, …, k − 1}`. -/
def ptrIndex (k : ℕ) (z : ℤ) : Option (Fin k) :=
  if h : 0 ≤ z ∧ z < k then some ⟨z.toNat, by omega⟩ else none

variable {n m T : ℕ}

/-- One execution step. A configuration on `accept` (or past the end of the program) is a fixed
point. Coefficient access and sampling are the only oracle instructions. -/
noncomputable def step (I : Instance n m T) (ω : ℕ → ℝ) (P : Program)
    (s : State) : State :=
  let c := s.core
  let setReg (dst : ℕ) (v : ℝ) : State :=
    { s with core := ⟨c.pc + 1, Function.update c.regs dst v, c.ptrs, c.mem⟩ }
  match P[c.pc]? with
  | none => s
  | some (.core _) => { s with core := SmaleNinth.RAMStep (coreProgram P) c }
  | some (.value dst q) =>
    setReg dst (match ptrIndex n (c.ptrs q) with
      | some i => I.value i
      | none => 0)
  | some (.cost dst q q') =>
    setReg dst (match ptrIndex n (c.ptrs q), ptrIndex m (c.ptrs q') with
      | some i, some j => I.cost i j
      | _, _ => 0)
  | some (.cdf dst q q' src) =>
    setReg dst (match ptrIndex n (c.ptrs q), ptrIndex m (c.ptrs q') with
      | some i, some j => cdf I i j (c.regs src)
      | _, _ => 0)
  | some (.truncMean dst q q' src) =>
    setReg dst (match ptrIndex n (c.ptrs q), ptrIndex m (c.ptrs q') with
      | some i, some j => truncMean I i j (c.regs src)
      | _, _ => 0)
  | some (.uniform dst) =>
    { core := ⟨c.pc + 1, Function.update c.regs dst (ω s.draws), c.ptrs, c.mem⟩
      draws := s.draws + 1 }
  | some (.ptrReal dst q) => setReg dst (c.ptrs q : ℝ)

/-- The initial state on an instance with parameters `n, m, T`. -/
noncomputable def initState (n m T : ℕ) : State where
  core := ⟨0, fun _ => 0, fun _ => 0,
    fun k => if k = 0 then (n : ℝ) else if k = 1 then (m : ℝ) else if k = 2 then (T : ℝ) else 0⟩
  draws := 0

/-- The state after `t` steps, with draw sequence `ω`. -/
noncomputable def run (I : Instance n m T) (ω : ℕ → ℝ) (P : Program) (t : ℕ) :
    State :=
  (step I ω P)^[t] (initState n m T)

/-- The machine has halted (its current instruction is `accept`). -/
def Halted (P : Program) (s : State) : Prop :=
  P[s.core.pc]? = some (Instr.core SmaleNinth.RAMInstr.accept)

/-- The input size `n + m + bitlength(T)`. -/
def inputSize (n m T : ℕ) : ℕ := n + m + Nat.size T

/-- Decode the `r`-th output triple. -/
noncomputable def decodeEntry (n m : ℕ) (mem : ℤ → ℝ) (r : ℕ) : Option (Fin n × Fin m × ℕ) :=
  match readNat (mem (1 + 3 * (r : ℤ))), readNat (mem (2 + 3 * (r : ℤ))),
      readNat (mem (3 + 3 * (r : ℤ))) with
  | some i, some j, some θ => if h : i < n ∧ j < m then some (⟨i, h.1⟩, ⟨j, h.2⟩, θ) else none
  | _, _, _ => none

/-- Decode the output list of (item, choice, threshold) triples from memory. -/
noncomputable def decodeOutput (n m : ℕ) (mem : ℤ → ℝ) : Option (SkipList n m) :=
  match readNat (mem 0) with
  | some ℓ => (List.range ℓ).mapM (decodeEntry n m mem)
  | none => none

/-- The draw sequence of a run with step budget `B`: `B` independent uniform values on `[0, 1]`
(a run of at most `B` steps makes at most `B` draws); later draws, never reached, are `0`. -/
noncomputable def extendDraws {B : ℕ} (ω : Fin B → unitInterval) : ℕ → ℝ :=
  fun k => if h : k < B then (ω ⟨k, h⟩ : ℝ) else 0

/-- The law of the draws: the product of `B` uniform laws on `[0, 1]`. -/
noncomputable def drawLaw (B : ℕ) : Measure (Fin B → unitInterval) :=
  Measure.pi fun _ => (volume : Measure unitInterval)

/-- The policy output after `B` steps (the empty list if nothing decodable is in memory). -/
noncomputable def outputPolicy (I : Instance n m T) (P : Program) (B : ℕ)
    (ω : Fin B → unitInterval) : SkipList n m :=
  (decodeOutput n m (run I (extendDraws ω) P B).core.mem).getD []

end PandoraKnapsack.Skipping


