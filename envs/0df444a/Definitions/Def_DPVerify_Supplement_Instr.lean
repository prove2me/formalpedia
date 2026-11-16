-- Prove2me | Definitions.Def_DPVerify_Supplement_Instr
-- name    : DPVerify_Supplement_Instr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:57:22.595289+00:00
-- url     : https://prove2.me/theorems/c26c872a-84ee-43af-9d6b-83c4d7fde041
-- title:
--   Randomized sample-access real RAM: unit-cost runs, acceptance probability, expected running time and the input layout of Theorem 5.1
-- statement:
--   The cost model of Theorem 5.1 (§5.2.4: "Reading, validating, and preprocessing the marginals costs $O(m)$ real-RAM operations … A hash table computes the singleton count in expected linear time") is a **randomized real RAM with sample access**:
--
--   1. The scalar core is the published real pointer machine `SmaleNinth.RAMInstr`: real registers, integer pointer registers, a memory $\mathbb Z\to\mathbb R$ addressed through pointers, exact $+,-,\times,\div$ (with $x/0=0$), literals, pointer set/copy/increment/decrement, the jumps "$r_i\le0$" and "$p_q\le p_{q'}$", and the halting instructions accept and reject.
--   2. Extensions: the cast $r_d:=p_q$; $p_d:=\lfloor r_a\rfloor$ (addresses computed from data); **sample**, $r_d:=$ coordinate $p_{q'}$ of sample number $p_q$ of the verifier's sample (as a natural number, $0$ out of range); **unif**, $r_d:=$ the next entry of an i.i.d. $\mathrm{Unif}[0,1]$ stream; **lap**, $r_d:=$ the next entry of an independent i.i.d. $\mathrm{Lap}(1)$ stream.
--   3. A program is a finite instruction list; it is **admissible** if every literal is rational.
--   4. Each executed instruction costs one step. The run **accepts** if it reaches accept; its **running time** is the first step at which it sits on accept or reject ($\infty$ if never). The acceptance probability and the expected running time are taken over the two random streams.
--   5. Input layout for Theorem 5.1: memory cell $0$ holds $\sigma$, cell $1$ holds $\varepsilon$, and cell $2+k$ holds the $k$-th entry of the prover's message $(M^{(i)}_a)_{i\in[d],a\in A_i}$ in lexicographic order of $(i,a)$; all other cells, registers and pointers are $0$. The sample $S\in\mathcal X^s$ is read only through the sample instruction.
--
--   **Formalization Note** Real parameters are inputs, not literals, so a program cannot hide real numbers in its code. Reading a whole sample costs $d$ steps, matching the paper's "$O(d)$ per verifier sample". Direct addressing in the zero-initialized memory plays the role of the paper's hash table.
-- source:
--   Du, Dwork, Tankala, Zhang, Differentially Private Verification of Distribution Properties, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), §5.2.4, p.26 (PDF p.29), and §5.1.1, p.20 (PDF p.23)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_PrivLearn_Generic_Privacy

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace DPVerify.Supplement

/-!
# The randomized sample-access real RAM of §5.2.4 and the input layout of Theorem 5.1

Du, Dwork, Tankala, Zhang, *Differentially Private Verification of Distribution Properties*,
arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), §5.2.4, p.26 = PDF p.29:
"Reading, validating, and preprocessing the marginals costs O(m) real-RAM operations. Evaluating
Q(x) … costs O(d) per verifier sample. … sampling from Q takes O(∑ᵢ log |Aᵢ|) = O(log N) time.
… A hash table computes the singleton count in expected linear time in the sample size."

**Formalization Note**
* The scalar core is the published `SmaleNinth.RAMInstr` pointer machine over `ℝ` (exact
  `+ − × ÷` with `x/0 = 0`, literals, indirect memory `ℤ → ℝ` through integer pointer registers,
  pointer set/copy/increment/decrement, the comparison jumps `r[i] ≤ 0` and `p[q] ≤ p[q']`, and
  the halting instructions `accept`/`reject`). It is extended with: the cast `r[d] := p[q]`;
  `floor` from a real register into a pointer register (`p[d] := ⌊r[a]⌋`, so addresses can be
  computed from data, which is what makes direct-addressed counting possible); `sample`, which
  reads one coordinate of one sample of the verifier's input sample; `unif`, which reads the next
  entry of an i.i.d. `Unif[0,1]` stream; and `lap`, which reads the next entry of an independent
  i.i.d. `Lap(1)` stream (`Lap(b)` is `b · Lap(1)`). No instruction carries a function or an
  oracle beyond these.
* `Admissible`: every real literal is rational, so the program cannot hide real parameters in
  its constants; real parameters are inputs.
* Cost: every executed instruction is one step, including each `sample` (one coordinate of one
  sample), `unif` and `lap`. An invalid program counter is stuck (never halts). After
  `accept`/`reject` the state stutters. `haltTime` is the first step count at which the run sits
  on `accept` or `reject`, and `⊤` if it never does.
* Randomness: `Streams = (ℕ → ℝ) × (ℕ → ℝ)`; the `j`-th executed `unif` reads entry `j` of the
  first stream, the `j`-th executed `lap` entry `j` of the second. `tape` makes the first stream
  i.i.d. uniform on `[0, 1]` and, independently, the second i.i.d. `Lap(1)`
  (`PrivLearn.Generic.laplace 1`).
* Sample access: the machine reads the verifier's sample through `sam : ℤ → ℤ → ℝ`,
  `sam a b` = coordinate `b` of sample `a`; `sampleTable` gives it for a sample
  `S : Fin s → ∏ᵢ Fin (n i)` (coordinates as naturals, `0` out of range).
-/

/-- An instruction of the machine. -/
inductive Instr where
  /-- A `SmaleNinth` real-RAM instruction (including `accept` and `reject`). -/
  | core (instruction : SmaleNinth.RAMInstr)
  /-- `r[dst] := (p[pointer] : ℝ)`. -/
  | pointerReal (dst pointer : ℕ)
  /-- `p[dst] := ⌊r[src]⌋`. -/
  | floor (dst src : ℕ)
  /-- `r[dst] :=` coordinate `p[q']` of sample number `p[q]`. -/
  | sample (dst q q' : ℕ)
  /-- `r[dst] :=` the next unread entry of the `Unif[0,1]` stream. -/
  | unif (dst : ℕ)
  /-- `r[dst] :=` the next unread entry of the `Lap(1)` stream. -/
  | lap (dst : ℕ)

/-- A program: one finite list of instructions. -/
abbrev Program := List Instr

/-- Every real literal of `P` is rational. -/
def Admissible (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ value) => ∃ q : ℚ, value = (q : ℝ)
    | _ => True

/-- The static core table of `P` (extension instructions are placeholders, dispatched by
`step`). -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- A machine state: the core configuration and the two stream cursors. -/
structure State where
  core : SmaleNinth.RAMConfig
  unifCursor : ℕ
  lapCursor : ℕ

/-- The randomness of a run: the `Unif[0,1]` stream and the `Lap(1)` stream. -/
abbrev Streams := (ℕ → ℝ) × (ℕ → ℝ)

/-- `P` sits on a halting instruction (`accept` if `b`, `reject` otherwise) in state `st`. -/
def HaltedWith (P : Program) (st : State) (b : Bool) : Prop :=
  P[st.core.pc]? = some (.core (if b then SmaleNinth.RAMInstr.accept else .reject))

/-- One step of `P` with sample access `sam` on the streams `ω`. Halted states (on `accept` or
`reject`) and invalid program counters stay put. -/
noncomputable def step (P : Program) (sam : ℤ → ℤ → ℝ) (ω : Streams) (st : State) : State :=
  let next : SmaleNinth.RAMConfig := { st.core with pc := st.core.pc + 1 }
  let setReg (d : ℕ) (v : ℝ) : State :=
    { st with core := { next with regs := Function.update st.core.regs d v } }
  let setPtr (d : ℕ) (v : ℤ) : State :=
    { st with core := { next with ptrs := Function.update st.core.ptrs d v } }
  match P[st.core.pc]? with
  | none => st
  | some (.core _) => { st with core := SmaleNinth.RAMStep (coreProgram P) st.core }
  | some (.pointerReal d q) => setReg d (st.core.ptrs q : ℝ)
  | some (.floor d a) => setPtr d ⌊st.core.regs a⌋
  | some (.sample d q q') => setReg d (sam (st.core.ptrs q) (st.core.ptrs q'))
  | some (.unif d) => { setReg d (ω.1 st.unifCursor) with unifCursor := st.unifCursor + 1 }
  | some (.lap d) => { setReg d (ω.2 st.lapCursor) with lapCursor := st.lapCursor + 1 }

/-- The state after `t` steps. -/
noncomputable def run (P : Program) (sam : ℤ → ℤ → ℝ) (s₀ : State) (ω : Streams) (t : ℕ) :
    State :=
  (step P sam ω)^[t] s₀

/-- The run accepts: it reaches `accept` at some step. -/
def Accepts (P : Program) (sam : ℤ → ℤ → ℝ) (s₀ : State) (ω : Streams) : Prop :=
  ∃ t : ℕ, HaltedWith P (run P sam s₀ ω t) true

/-- The running time: the first step count at which the run sits on `accept` or `reject`
(`⊤` if it never halts). -/
noncomputable def haltTime (P : Program) (sam : ℤ → ℤ → ℝ) (s₀ : State) (ω : Streams) : ℕ∞ :=
  sInf ((fun t : ℕ => (t : ℕ∞)) ''
    {t | HaltedWith P (run P sam s₀ ω t) true ∨ HaltedWith P (run P sam s₀ ω t) false})

/-- The tape measure: i.i.d. `Unif[0,1]` entries in the first stream and, independently, i.i.d.
`Lap(1)` entries in the second. -/
noncomputable def tape : Measure Streams :=
  (Measure.infinitePi fun _ : ℕ => (volume : Measure ℝ).restrict (Set.Icc 0 1)).prod
    (Measure.infinitePi fun _ : ℕ => PrivLearn.Generic.laplace 1)

/-- The probability that the run accepts. -/
noncomputable def acceptProb (P : Program) (sam : ℤ → ℤ → ℝ) (s₀ : State) : ℝ≥0∞ :=
  tape {ω | Accepts P sam s₀ ω}

/-- The probability that the run does not accept (it rejects or never halts). -/
noncomputable def rejectProb (P : Program) (sam : ℤ → ℤ → ℝ) (s₀ : State) : ℝ≥0∞ :=
  tape {ω | ¬ Accepts P sam s₀ ω}

/-- The expected running time over the streams. -/
noncomputable def expTime (P : Program) (sam : ℤ → ℤ → ℝ) (s₀ : State) : ℝ≥0∞ :=
  ∫⁻ ω, ((haltTime P sam s₀ ω : ℕ∞) : ℝ≥0∞) ∂tape

/-- Sample access for a sample `S : Fin s → ∏ᵢ Fin (n i)`: coordinate `b` of sample `a`, as a
natural number, and `0` if `a ∉ [0, s)` or `b ∉ [0, d)`. -/
noncomputable def sampleTable {d s : ℕ} {n : Fin d → ℕ} (S : Fin s → (i : Fin d) → Fin (n i)) :
    ℤ → ℤ → ℝ := fun a b =>
  if h : 0 ≤ a ∧ a < s ∧ 0 ≤ b ∧ b < d then
    ((S ⟨a.toNat, by omega⟩ ⟨b.toNat, by omega⟩ : ℕ) : ℝ)
  else 0

/-- The input memory of Theorem 5.1's verifier: cell `0` holds `σ`, cell `1` holds `ε`, and cell
`2 + k` holds the `k`-th entry of the prover's message `M = (M^{(i)}_a)` flattened in the order
`(i, a)` lexicographic (`finSigmaFinEquiv`), `k < ∑ᵢ n i`; every other cell is `0`. -/
noncomputable def inputMem {d : ℕ} {n : Fin d → ℕ} (σ ε : ℝ) (M : (i : Fin d) → Fin (n i) → ℝ) :
    ℤ → ℝ := fun a =>
  if a = 0 then σ else if a = 1 then ε else
    if h : 2 ≤ a ∧ a - 2 < ((∑ i, n i : ℕ) : ℤ) then
      M (finSigmaFinEquiv.symm ⟨(a - 2).toNat, by omega⟩).1
        (finSigmaFinEquiv.symm ⟨(a - 2).toNat, by omega⟩).2
    else 0

/-- The initial state: program counter, registers, pointers and cursors `0`, memory
`inputMem σ ε M`. -/
noncomputable def inputState {d : ℕ} {n : Fin d → ℕ} (σ ε : ℝ)
    (M : (i : Fin d) → Fin (n i) → ℝ) : State :=
  ⟨⟨0, fun _ => 0, fun _ => 0, inputMem σ ε M⟩, 0, 0⟩

end DPVerify.Supplement


