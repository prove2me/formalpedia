-- Prove2me | Definitions.Def_TwMSOCount_Main_Machine
-- name    : TwMSOCount_Main_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:40:00.717453+00:00
-- url     : https://prove2.me/theorems/95c421cd-6d46-464a-a07f-905ceb0f31a3
-- title:
--   Rational-cell log-cost RAM with arithmetic, scalar-entry, bit-time and bit-space counters, fair coins, and the input and output encodings
-- statement:
--   The algorithms of the paper are run on a **random-access machine** whose cells $R_0, R_1, \dots$ hold exact rationals. Instructions: load a constant, copy, $R_d := R_a \circ R_b$ for $\circ \in \{+,-,\times,\div\}$ (division by $0$ gives $0$), floor, indirect load and store through the address $\lfloor R_a \rfloor$, a conditional jump on the comparison $R_a \le R_b$, an unconditional jump, $\mathrm{coin}$ (write the next fair random bit), and halt. A run starts with the input word in cells $0,\dots,\ell-1$ and $0$ elsewhere.
--
--   Cost model (Definition D.1). A rational is stored as a reduced fraction; its **bit length** is the number of bits of its numerator plus those of its denominator. One step on operands of bit lengths $\ell_1, \ell_2$ costs $(\ell_1+\ell_2+1)^2$ for an arithmetic operation or comparison, the bit lengths of address and value plus one for a load or store, the value length plus one for constants and copies, and $1$ for jumps and coins; the **bit time** of a run is the total cost of its steps up to the first halt. The **arithmetic operations** are the executed additions, subtractions, multiplications, divisions, floors and comparisons. The **scalar entries** are the cells ever written (input cells included), and the **bit space** is the maximum over the run of the stored bits (address bits plus content bits over these cells).
--
--   A deterministic run uses the all-zero coin tape. The **fair-coin tape** is the product of independent uniform bits indexed by $\mathbb N$. A randomized call of a program $Q$ from a configuration either halts, with output the word in cells $1,\dots,\lfloor R_0\rfloor$, or runs forever (cost $+\infty$).
--
--   The **input** for $(n, k, C = \{0,\dots,r-1\}, \psi, \lambda, \beta)$ is the word $n, k, r, |\mathrm{code}(\psi)|, \mathrm{code}(\psi), \lambda_0,\dots,\lambda_{r-1}, \beta_{0,0},\dots,\beta_{r-1,r-1}$, one stored rational per number (so $n$ is read in binary). $L$ is the total bit length of the $r + r^2$ weight entries ($L \ge 1$), and the parameter size is $|\theta| = k + r + \mathrm{size}(\psi)$. The **output code** of a colored graph $(G,\chi)$ on $[n]$ lists $\chi(0),\dots,\chi(n-1)$ and then the adjacency bits of the pairs $i<j$ in lexicographic order.
--
--   **Formalization Note.** `Instr`, `Program`, `Config`, `step`, `stepCost`, `stepArith`, `runStats` (first halt via `Nat.find`), `RunStats` (`time`, `arith`, `entries`, `space`), `zeroTape`, `coinTape := Measure.infinitePi` of uniform bits, `callOutput`, `callCost`, `Config.restart` (keep every cell, reset the program counter and the coin pointer), `encodeInput`, `weightLength`, `thetaSize`, `codeGraph`.
-- source:
--   Zou, Wang, Chang, Wang, Kuželka, Exact Counting and Sampling of Labeled Graphs of Bounded Treewidth with MSO Properties, STOC 2027 submission (manuscript sha256 2715a74f…775b), §2, p. 4 (PDF 5); Definition D.1, p. 31 (PDF 32); Appendix D.4, p. 35 (PDF 36)

import Mathlib
import Definitions.Def_TwMSOCount_Main_Weights

open MeasureTheory
open scoped ENNReal

namespace TwMSOCount.Main

/-- Bit length of a stored rational in reduced form: bits of `|numerator|` plus bits of the
denominator (Definition D.1: "Rationals are stored as reduced fractions of integers in binary").
Zero, stored as `0/1`, has length `1`. -/
def qbits (q : ℚ) : ℕ := Nat.size q.num.natAbs + Nat.size q.den

/-- Instructions of a random-access machine whose cells hold exact rationals (indexed by `ℕ`).
`add`/`sub`/`mul`/`div` write `R d := R a ∘ R b` (division by `0` gives `0`), `floor` writes
`⌊R a⌋`, `jle a b t` jumps to `t` when `R a ≤ R b` (a comparison), `load d a` / `store a s` use
indirect addressing through cell `⌊R a⌋`, `coin d` writes the next fair random bit into `R d`. -/
inductive Instr where
  | const (d : ℕ) (q : ℚ)
  | mov (d a : ℕ)
  | add (d a b : ℕ)
  | sub (d a b : ℕ)
  | mul (d a b : ℕ)
  | div (d a b : ℕ)
  | floor (d a : ℕ)
  | load (d a : ℕ)
  | store (a s : ℕ)
  | jle (a b t : ℕ)
  | jmp (t : ℕ)
  | coin (d : ℕ)
  | halt

/-- A program is a finite list of instructions. -/
abbrev Program := List Instr

/-- A configuration: program counter, cell contents, the set of cells ever written (input cells
included), and the number of random bits read so far. -/
structure Config where
  pc : ℕ
  reg : ℕ → ℚ
  used : Finset ℕ
  coins : ℕ

/-- The initial configuration on an input word: cells `0, …, |w|-1` hold the word, all other
cells hold `0`. -/
def Config.init (w : List ℚ) : Config :=
  ⟨0, fun i => w.getD i 0, Finset.range w.length, 0⟩

/-- Address held by cell `a`: `⌊R a⌋` truncated to `ℕ`. -/
def Config.addr (c : Config) (a : ℕ) : ℕ := (⌊c.reg a⌋).toNat

/-- Write `q` into cell `d`. -/
def Config.write (c : Config) (d : ℕ) (q : ℚ) : Config :=
  { c with reg := Function.update c.reg d q, used := insert d c.used, pc := c.pc + 1 }

/-- A configuration is halted when the instruction at `pc` is `halt` or `pc` is past the end. -/
def halted (P : Program) (c : Config) : Prop :=
  P[c.pc]? = some Instr.halt ∨ P[c.pc]? = none

/-- One step on coin tape `τ`; a halted configuration stays. -/
def step (P : Program) (τ : ℕ → Bool) (c : Config) : Config :=
  match P[c.pc]? with
  | none => c
  | some Instr.halt => c
  | some (Instr.const d q) => c.write d q
  | some (Instr.mov d a) => c.write d (c.reg a)
  | some (Instr.add d a b) => c.write d (c.reg a + c.reg b)
  | some (Instr.sub d a b) => c.write d (c.reg a - c.reg b)
  | some (Instr.mul d a b) => c.write d (c.reg a * c.reg b)
  | some (Instr.div d a b) => c.write d (c.reg a / c.reg b)
  | some (Instr.floor d a) => c.write d (⌊c.reg a⌋ : ℚ)
  | some (Instr.load d a) => c.write d (c.reg (c.addr a))
  | some (Instr.store a s) => c.write (c.addr a) (c.reg s)
  | some (Instr.jle a b t) => { c with pc := if c.reg a ≤ c.reg b then t else c.pc + 1 }
  | some (Instr.jmp t) => { c with pc := t }
  | some (Instr.coin d) =>
      { c.write d (if τ c.coins then 1 else 0) with coins := c.coins + 1 }

/-- Bit cost of the step taken from `c` (logarithmic-cost RAM): an arithmetic operation or
comparison on operands of bit lengths `ℓ₁, ℓ₂` costs `(ℓ₁ + ℓ₂ + 1)²` (schoolbook multiplication,
long division and reduction by the Euclidean algorithm), a load or store costs the bit lengths of the
address and of the value moved, plus one; other steps cost `1`; a halted configuration costs `0`. -/
def stepCost (P : Program) (c : Config) : ℕ :=
  match P[c.pc]? with
  | none => 0
  | some Instr.halt => 0
  | some (Instr.const _ q) => qbits q + 1
  | some (Instr.mov _ a) => qbits (c.reg a) + 1
  | some (Instr.add _ a b) => (qbits (c.reg a) + qbits (c.reg b) + 1) ^ 2
  | some (Instr.sub _ a b) => (qbits (c.reg a) + qbits (c.reg b) + 1) ^ 2
  | some (Instr.mul _ a b) => (qbits (c.reg a) + qbits (c.reg b) + 1) ^ 2
  | some (Instr.div _ a b) => (qbits (c.reg a) + qbits (c.reg b) + 1) ^ 2
  | some (Instr.floor _ a) => (qbits (c.reg a) + 1) ^ 2
  | some (Instr.load _ a) => qbits (c.reg a) + qbits (c.reg (c.addr a)) + 1
  | some (Instr.store a s) => qbits (c.reg a) + qbits (c.reg s) + 1
  | some (Instr.jle a b _) => (qbits (c.reg a) + qbits (c.reg b) + 1) ^ 2
  | some (Instr.jmp _) => 1
  | some (Instr.coin _) => 1

/-- `1` when the step from `c` is an arithmetic operation of Definition D.1 (addition,
subtraction, multiplication, division, floor, or a comparison of two stored rationals), else `0`.
Index arithmetic is also performed by these instructions and is counted. -/
def stepArith (P : Program) (c : Config) : ℕ :=
  match P[c.pc]? with
  | some (Instr.add _ _ _) => 1
  | some (Instr.sub _ _ _) => 1
  | some (Instr.mul _ _ _) => 1
  | some (Instr.div _ _ _) => 1
  | some (Instr.floor _ _) => 1
  | some (Instr.jle _ _ _) => 1
  | _ => 0

/-- Stored bits of a configuration: over the cells written so far, the bits of the address plus
the bits of the content. -/
def Config.spaceBits (c : Config) : ℕ := ∑ i ∈ c.used, (Nat.size i + qbits (c.reg i))

/-- The configuration after `t` steps. -/
def run (P : Program) (τ : ℕ → Bool) (c : Config) (t : ℕ) : Config := (step P τ)^[t] c

/-- Resource usage of a run that halts after exactly `T` steps. -/
structure RunStats where
  /-- the configuration at the first halt -/
  final : Config
  /-- bit time: total bit cost of the steps taken -/
  time : ℕ
  /-- number of arithmetic operations -/
  arith : ℕ
  /-- number of scalar entries: cells holding a stored rational (cells ever written) -/
  entries : ℕ
  /-- bit space: the maximum of `spaceBits` over the run -/
  space : ℕ

/-- Statistics of the run of `P` from `c` on tape `τ` stopped after `T` steps. -/
def statsAt (P : Program) (τ : ℕ → Bool) (c : Config) (T : ℕ) : RunStats :=
  ⟨run P τ c T, ∑ t ∈ Finset.range T, stepCost P (run P τ c t),
    ∑ t ∈ Finset.range T, stepArith P (run P τ c t), (run P τ c T).used.card,
    (Finset.range (T + 1)).sup (fun t => (run P τ c t).spaceBits)⟩

open Classical in
/-- The run of `P` from `c` on tape `τ`, stopped at its first halted configuration; `none` if it
never halts. -/
noncomputable def runStats (P : Program) (τ : ℕ → Bool) (c : Config) : Option RunStats :=
  if h : ∃ T, halted P (run P τ c T) then some (statsAt P τ c (Nat.find h)) else none

/-- The all-zero tape, used for deterministic runs. -/
def zeroTape : ℕ → Bool := fun _ => false

/-- The output word of a configuration: cell `0` holds its length `ℓ` (as `⌊R 0⌋`), cells
`1, …, ℓ` hold its entries. -/
def Config.output (c : Config) : List ℚ :=
  (List.range (⌊c.reg 0⌋).toNat).map (fun i => c.reg (i + 1))

/-- Restart from a configuration: keep every cell (the tables), reset `pc` and the coin pointer. -/
def Config.restart (c : Config) : Config := { c with pc := 0, coins := 0 }

/-- The fair-coin tape: independent uniform bits indexed by `ℕ` (Definition D.1). -/
noncomputable def coinTape : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure

/-- Output of one randomized call of `Q` from `c` on tape `τ`, `none` if it never halts. -/
noncomputable def callOutput (Q : Program) (c : Config) (τ : ℕ → Bool) : Option (List ℚ) :=
  (runStats Q τ c).map (fun s => s.final.output)

/-- Bit cost of one randomized call, `⊤` on a tape on which it never halts. -/
noncomputable def callCost (Q : Program) (c : Config) (τ : ℕ → Bool) : ℝ≥0∞ :=
  match runStats Q τ c with
  | some s => (s.time : ℝ≥0∞)
  | none => ⊤

/-- Input word for `(n, k, C = Fin r, ψ, λ, β)`: `n, k, r`, the length of the code of `ψ`, the code
of `ψ`, then `λ_0, …, λ_{r-1}`, then `β_{c,d}` row by row. Every number is one stored rational, so
`n` is read in binary. -/
noncomputable def encodeInput (n k r : ℕ) (ψ : Formula r Empty) (w : Weights r) : List ℚ :=
  let code := ψ.encode (fun e => e.elim)
  [(n : ℚ), (k : ℚ), (r : ℚ), (code.length : ℚ)] ++ code.map (fun x => (x : ℚ)) ++
    (List.finRange r).map (fun c => ((w.vtx c : ℚ≥0) : ℚ)) ++
    (List.finRange r).flatMap (fun c => (List.finRange r).map (fun d => ((w.edge c d : ℚ≥0) : ℚ)))

/-- `L`: total binary encoding length of the weights (all `r` vertex weights and all `r²` entries
of the symmetric matrix `β`). Since `r ≥ 1`, `L ≥ 1`. -/
def weightLength {r : ℕ} (w : Weights r) : ℕ :=
  (∑ c : Fin r, qbits (w.vtx c : ℚ)) + ∑ c : Fin r, ∑ d : Fin r, qbits (w.edge c d : ℚ)

/-- Size of the parameter `θ = (k, C, ψ)`: `k + |C| + size ψ`. Finitely many `θ` have a given
size. -/
def thetaSize {r : ℕ} (k : ℕ) (ψ : Formula r Empty) : ℕ := k + r + ψ.size

open Classical in
/-- Output code of a colored labeled graph `(G, χ)` on `Fin n`: the colors `χ 0, …, χ (n-1)`,
then for the pairs `i < j` in lexicographic order the bit `[ij ∈ E(G)]`. -/
noncomputable def codeGraph {n r : ℕ} (G : SimpleGraph (Fin n)) (χ : Fin n → Fin r) : List ℚ :=
  (List.finRange n).map (fun i => ((χ i).val : ℚ)) ++
    (List.finRange n).flatMap (fun i =>
      ((List.finRange n).filter (fun j => i < j)).map (fun j => if G.Adj i j then (1 : ℚ) else 0))

end TwMSOCount.Main


