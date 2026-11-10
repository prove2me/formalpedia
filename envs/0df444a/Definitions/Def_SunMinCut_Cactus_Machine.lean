-- Prove2me | Definitions.Def_SunMinCut_Cactus_Machine
-- name    : SunMinCut_Cactus_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:23:49.320568+00:00
-- url     : https://prove2.me/theorems/2ecf652b-e627-4bc0-bd90-0283103616ed
-- title:
--   Randomized unit-cost real RAM, draw-tape measure, input and output layouts
-- statement:
--   The machine of footnote 1 (p. 2) is the published real-RAM core `SmaleNinth.RAMInstr` (real registers, integer pointer registers, memory indexed by integers, constants, $+,-,\times,/$, indirect load/store, pointer set/copy/increment/decrement, comparison jumps) extended by: rounding $\lfloor x\rfloor$, natural logarithm, real power $x^y$ on nonnegative bases (zero on negative bases), real↔pointer conversion, a **uniform draw** from $[0,1]$ (the next cell of the draw tape), and `halt`. Every executed instruction costs one operation. A program is **admissible** if its constants are rational and it excludes the core accept/reject instructions. It can halt explicitly or by running off the program. `Deterministic P` requires that the program contain no uniform-draw instruction.
--
--   A run starts with program counter $0$, all registers $0$, and the input list in memory cells $0,1,\dots$ (other cells $0$); a halted state is fixed and running off the end of the program halts. The draw tape $\omega\in[0,1]^{\mathbb N}$ carries the product of uniform (Lebesgue) measures (`tapeMeasure`). `HaltsWithin P l B`: for **every** tape, the run on input $l$ has halted after $\lfloor B\rfloor$ steps. `outputAt P l B ω` is the output after $\lfloor B\rfloor$ steps: the memory block of length $p[1]$ starting at address $p[2]$.
--
--   Layouts: `GraphCode G l`: $l=[n,m]$ followed by $(a_e,b_e,w_e)$ for each record, with $\{a_e,b_e\}$ its endpoint pair in either orientation. `EdgeListCode T l`: the number of edges then each edge of $T$ once as a vertex pair, in any order and orientation. `shoreList S`: the indicator $[\mathbb 1(0\in S),\dots,\mathbb 1(n-1\in S)]$. `CactusCode K π l`: $[q,e]$, then $\pi(0),\dots,\pi(n-1)$, then each edge of $K$ as a node pair. `CutCactusOut S K π l`: $l$ is `shoreList S` followed by a cactus code.
--
--   **Formalization Note** Division by zero is zero; logarithm uses Lean’s log(abs x) convention with log 0 = 0. Power calls `Real.rpow` only on nonnegative bases and returns zero on negative bases, excluding Mathlib’s cosine continuation there. These exceptional-value conventions can be implemented with constant-cost guards and arithmetic. No instruction computes a cut, tree, LCA, connectivity, cactus or Poisson process.
-- source:
--   Sun 2026, doi:10.5281/zenodo.23915020, footnote 1 p. 2, §1 p. 2

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_SunMinCut_Cactus_CactusGraph

open MeasureTheory

namespace SunMinCut.Cactus

/-- An instruction of the randomized unit-cost real RAM of Sun 2026 (footnote 1, p. 2): the
published real-RAM core (constants, `+ − × /`, indirect load/store through integer pointers,
pointer arithmetic, comparisons with jumps), extended by rounding, logarithms, powers,
real/pointer conversion, a uniform draw from `[0, 1]`, and halting. -/
inductive Instr where
  /-- An instruction of the published core `SmaleNinth.RAMInstr`. -/
  | core (i : SmaleNinth.RAMInstr)
  /-- `r[dst] := ⌊r[src]⌋` (rounding). -/
  | floor (dst src : ℕ)
  /-- `r[dst] := log r[src]` (natural logarithm; Lean-total: `log x = log |x|`, `log 0 = 0`). -/
  | log (dst src : ℕ)
  /-- `r[dst] := r[i] ^ r[j]` for a nonnegative base; negative bases return zero.
  The guard excludes the cosine continuation used by `Real.rpow` on negative bases. -/
  | pow (dst i j : ℕ)
  /-- `p[q] := ⌊r[src]⌋`, a real register used as an address. -/
  | toPtr (q src : ℕ)
  /-- `r[dst] := p[q]`. -/
  | ofPtr (dst q : ℕ)
  /-- `r[dst] :=` a fresh uniform draw from `[0, 1]` (the next cell of the draw tape). -/
  | draw (dst : ℕ)
  /-- Stop. -/
  | halt

/-- A program: a finite list of instructions, executed from position `0`. -/
abbrev Program := List Instr

/-- The program's constants are rational and it uses the core's `accept`/`reject` nowhere (it
stops only through `halt`). Fixing the program fixes these finitely many constants. -/
def Admissible (P : Program) : Prop :=
  ∀ i ∈ P, (∀ dst c, i = .core (.const dst c) → ∃ x : ℚ, c = (x : ℝ)) ∧
    i ≠ .core .accept ∧ i ≠ .core .reject

/-- A deterministic program has no uniform-draw instruction. -/
def Deterministic (P : Program) : Prop := ∀ dst, Instr.draw dst ∉ P

/-- A machine state: the core configuration, the number of draws used, and the halting flag. -/
structure State where
  /-- Program counter, real registers, pointer registers and memory. -/
  cfg : SmaleNinth.RAMConfig
  /-- Number of uniform draws consumed. -/
  draws : ℕ
  /-- Whether the machine has halted. -/
  halted : Bool

/-- The draw tape: a sequence of points of `[0, 1]`. -/
abbrev Tape := ℕ → unitInterval

/-- The probability on draw tapes: the product of uniform (Lebesgue) measures on `[0, 1]`. -/
noncomputable def tapeMeasure : Measure Tape :=
  Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)

/-- The core instruction of an instruction (`accept` for the extensions; only used at positions
holding a core instruction). -/
def Instr.coreOf : Instr → SmaleNinth.RAMInstr
  | .core i => i
  | _ => .accept

/-- Advance the program counter after updating the real registers. -/
def State.setReg (S : State) (regs : ℕ → ℝ) : State :=
  { S with cfg := { S.cfg with pc := S.cfg.pc + 1, regs := regs } }

/-- One step; every executed instruction is one operation. A halted state is fixed, and running
off the end of the program halts. -/
noncomputable def step (P : Program) (ω : Tape) (S : State) : State :=
  if S.halted then S else
  let r := S.cfg.regs
  match P[S.cfg.pc]? with
  | none => { S with halted := true }
  | some (.core _) =>
      { S with cfg := SmaleNinth.RAMStep (P.map Instr.coreOf) S.cfg }
  | some (.floor dst src) => S.setReg (Function.update r dst (⌊r src⌋ : ℝ))
  | some (.log dst src) => S.setReg (Function.update r dst (Real.log (r src)))
  | some (.pow dst i j) =>
      S.setReg (Function.update r dst (if 0 ≤ r i then r i ^ r j else 0))
  | some (.toPtr q src) =>
      { S with cfg := ⟨S.cfg.pc + 1, r, Function.update S.cfg.ptrs q ⌊r src⌋, S.cfg.mem⟩ }
  | some (.ofPtr dst q) => S.setReg (Function.update r dst (S.cfg.ptrs q : ℝ))
  | some (.draw dst) =>
      { S.setReg (Function.update r dst (ω S.draws : ℝ)) with draws := S.draws + 1 }
  | some .halt => { S with halted := true }

/-- The state after `t` steps of `P` on input memory `x` and draw tape `ω` (program counter `0`,
all registers `0`, no draws used). -/
noncomputable def run (P : Program) (x : ℤ → ℝ) (ω : Tape) (t : ℕ) : State :=
  (step P ω)^[t] ⟨⟨0, fun _ => 0, fun _ => 0, x⟩, 0, false⟩

/-- The input memory holding the list `l` in cells `0, 1, …` and `0` elsewhere. -/
noncomputable def inputMem (l : List ℝ) : ℤ → ℝ := fun j => if 0 ≤ j then l.getD j.toNat 0 else 0

/-- The output of a state: the memory block of length `p[1]` starting at address `p[2]`. -/
noncomputable def output (S : State) : List ℝ :=
  (List.range (S.cfg.ptrs 1).toNat).map fun j => S.cfg.mem (S.cfg.ptrs 2 + (j : ℤ))

/-- Every execution of `P` on input `l` halts within `B` operations: for every draw tape the
state after `⌊B⌋₊` steps is halted. -/
def HaltsWithin (P : Program) (l : List ℝ) (B : ℝ) : Prop :=
  ∀ ω : Tape, (run P (inputMem l) ω ⌊B⌋₊).halted = true

/-- The output of `P` on input `l` and tape `ω`, read after `⌊B⌋₊` steps (the final output when
the run halts within `B` operations). -/
noncomputable def outputAt (P : Program) (l : List ℝ) (B : ℝ) (ω : Tape) : List ℝ :=
  output (run P (inputMem l) ω ⌊B⌋₊)

/-! ### Input and output layouts -/

/-- The flat list `[a₀, b₀, w₀, a₁, b₁, w₁, …]` of the records. -/
def recordList {n m : ℕ} (a b : Fin m → Fin n) (w : Fin m → ℝ) : List ℝ :=
  (List.ofFn fun e => [((a e : ℕ) : ℝ), ((b e : ℕ) : ℝ), w e]).flatten

/-- `l` encodes the graph `G`: `[n, m]` followed by each record `e` as `(a_e, b_e, w_e)`, with
`{a_e, b_e}` its endpoint pair written in either orientation. -/
def GraphCode {n m : ℕ} (G : Graph n m) (l : List ℝ) : Prop :=
  ∃ a b : Fin m → Fin n, (∀ e, G.ends e = s(a e, b e)) ∧
    l = [(n : ℝ), (m : ℝ)] ++ recordList a b G.u

/-- `l` encodes the edges of the tree (or graph) `T`: their number, then each edge once as a pair
of vertex indices, in any order and orientation. -/
def EdgeListCode {n : ℕ} (T : SimpleGraph (Fin n)) (l : List ℝ) : Prop :=
  ∃ es : List (Fin n × Fin n), (es.map fun p => s(p.1, p.2)).Nodup ∧
    (∀ f, f ∈ T.edgeSet ↔ ∃ p ∈ es, f = s(p.1, p.2)) ∧
    l = ((es.length : ℕ) : ℝ) :: (es.map fun p => [((p.1 : ℕ) : ℝ), ((p.2 : ℕ) : ℝ)]).flatten

/-- The indicator list `[𝟙(0 ∈ S), …, 𝟙(n-1 ∈ S)]` of a shore. -/
noncomputable def shoreList {n : ℕ} (S : Finset (Fin n)) : List ℝ :=
  List.ofFn fun v : Fin n => by classical exact if v ∈ S then 1 else 0

/-- `l` encodes the cactus `(K, π)`: `[q, e]`, then `π(0), …, π(n-1)`, then each edge of `K` as a
pair of node indices in either orientation. -/
def CactusCode {n q e : ℕ} (K : MGraph q e) (π : Fin n → Fin q) (l : List ℝ) : Prop :=
  ∃ a b : Fin e → Fin q, (∀ i, K.ends i = s(a i, b i)) ∧
    l = [(q : ℝ), (e : ℝ)] ++ List.ofFn (fun v => ((π v : ℕ) : ℝ)) ++
      (List.ofFn fun i => [((a i : ℕ) : ℝ), ((b i : ℕ) : ℝ)]).flatten

/-- `l` is a shore followed by a cactus: `shoreList S ++ code of (K, π)`. -/
def CutCactusOut {n q e : ℕ} (S : Finset (Fin n)) (K : MGraph q e) (π : Fin n → Fin q)
    (l : List ℝ) : Prop :=
  ∃ c, CactusCode K π c ∧ l = shoreList S ++ c

end SunMinCut.Cactus


