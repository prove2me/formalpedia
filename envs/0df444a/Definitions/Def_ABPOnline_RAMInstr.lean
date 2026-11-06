-- Prove2me | Definitions.Def_ABPOnline_RAMInstr
-- name    : ABPOnline_RAMInstr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:53:41.780652+00:00
-- url     : https://prove2.me/theorems/3deaf3fa-cde8-4591-b650-1af97ad4fd91
-- title:
--   An interactive real-RAM for counting arithmetic operations of an online algorithm
-- statement:
--   A **real-RAM program** is a finite list of instructions acting on real registers $r[0],r[1],\dots$ and natural-number registers $n[0],n[1],\dots$: load of a real constant written in the program; conversion $r[d]:=n[a]$; the arithmetic operations $+,-,\times,\div$ and the functions $\sqrt{\cdot}$, $\exp$, $\log$ and the standard normal distribution function $\Phi$ on real registers; indirect load and store $r[d]:=r[n[a]]$, $r[n[a]]:=r[s]$; natural constants, addition and truncated subtraction; unconditional jumps and jumps on $r[a]<r[b]$ or $n[a]<n[b]$; **read the next column** of the $M\times N$ input into $M$ consecutive real registers; **emit** the sign $+1$ if $r[s]\ge0$ and $-1$ otherwise; and halt. A run on input $(M,N,G)$ starts with $n[0]=M$, $n[1]=N$ and all other registers $0$.
--
--   The I/O protocol makes the program online: a column may be read only after every column read so far has received its sign, and at most $N$ signs may be emitted; an illegal step stops the machine with a fault. The **cost** of a run is the number of executed instructions, a column read counting $M$.
--
--   This model gives a precise meaning to "the algorithm uses $O(MN)$ arithmetic operations" in Theorem 1.1.
--
--   **Formalization Note** The operations are Lean's total functions ($x/0=0$, $\sqrt x=0$ for $x<0$, $\log x=\log|x|$, $\log0=0$). There is no real-to-integer conversion, so real data affect control flow only through comparisons. The $k$-th emitted sign is defined as `ramSign`; if fewer signs are ever emitted it is $1$.
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), Theorem 1.1, p.1 (PDF p.2) ('This algorithm uses O(MN) arithmetic operations'); §4.3, p.14 (PDF p.15)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace ABPOnline

/-- The instructions of the interactive **real-RAM** used to count arithmetic operations
(arXiv:2609.02124, Theorem 1.1, printed p.1, PDF p.2: "This algorithm uses O(MN) arithmetic
operations"; §4.3, p.14). Real registers `r[·]` and natural-number registers `n[·]`:

* `rconst d c`: `r[d] := c`, for a real constant `c` written in the program;
* `ofNat d a`: `r[d] := n[a]`;
* `add`, `sub`, `mul`, `div` `d a b`: `r[d] := r[a] ∘ r[b]`;
* `sqrt`, `exp`, `log`, `normCdf` `d a`: `r[d] := f(r[a])` with `f = √, exp, log, Φ`;
* `load d a`: `r[d] := r[n[a]]`; `store a s`: `r[n[a]] := r[s]` (indirect addressing);
* `nconst d c`: `n[d] := c`; `nadd`, `nsub` `d a b`: `n[d] := n[a] ± n[b]` (truncated);
* `jmp t`; `jltR a b t`: jump to `t` if `r[a] < r[b]`; `jltN a b t`: jump if `n[a] < n[b]`;
* `readCol a`: read the next column `g` of the input into `r[n[a]], …, r[n[a] + M − 1]`;
* `emit s`: output the sign `+1` if `r[s] ≥ 0` and `−1` otherwise;
* `halt`. -/
inductive RAMInstr : Type
  | rconst (d : ℕ) (c : ℝ)
  | ofNat (d a : ℕ)
  | add (d a b : ℕ)
  | sub (d a b : ℕ)
  | mul (d a b : ℕ)
  | div (d a b : ℕ)
  | sqrt (d a : ℕ)
  | exp (d a : ℕ)
  | log (d a : ℕ)
  | normCdf (d a : ℕ)
  | load (d a : ℕ)
  | store (a s : ℕ)
  | nconst (d c : ℕ)
  | nadd (d a b : ℕ)
  | nsub (d a b : ℕ)
  | jmp (t : ℕ)
  | jltR (a b t : ℕ)
  | jltN (a b t : ℕ)
  | readCol (a : ℕ)
  | emit (s : ℕ)
  | halt

/-- A configuration of the real-RAM: program counter, registers, the number of columns read, the
signs emitted so far, the cost so far, and the halting and fault flags. -/
structure RAMConfig where
  pc : ℕ
  reg : ℕ → ℝ
  nreg : ℕ → ℕ
  colsRead : ℕ
  signs : List ℝ
  cost : ℕ
  halted : Bool
  fault : Bool

/-- The initial configuration on an `M × N` input: `n[0] = M`, `n[1] = N`, every other register
`0`. -/
def RAMConfig.init (M N : ℕ) : RAMConfig where
  pc := 0
  reg := fun _ => 0
  nreg := fun j => if j = 0 then M else if j = 1 then N else 0
  colsRead := 0
  signs := []
  cost := 0
  halted := false
  fault := false

/-- The stopped configuration after an illegal step (a column read out of turn, a sign too many,
or the program counter off the program). -/
def RAMConfig.toFault (c : RAMConfig) : RAMConfig := { c with halted := true, fault := true }

/-- One step of the real-RAM on the `M × N` input `G`, revealed column by column.

**Formalization Note** Every instruction costs `1`, except `readCol`, which costs `M` (one per
entry read). The real operations are Lean's total functions: `x/0 = 0`, `√x = 0` for `x < 0`,
`log x = log |x|` with `log 0 = 0`, and `Φ` is the standard normal distribution function. The
I/O protocol: `readCol` is legal only when every column read so far has had its sign emitted
(`colsRead ≤ #signs`) and a column remains; `emit` is legal while fewer than `N` signs have been
emitted. Hence the sign for column `k` (0-based) is emitted after at most `k + 1` columns have been
read. An illegal step stops the machine with the fault flag. -/
noncomputable def ramStep (prog : List RAMInstr) (M N : ℕ) (G : Fin M × Fin N → ℝ)
    (c : RAMConfig) : RAMConfig :=
  if c.halted then c else
  match prog[c.pc]? with
  | none => c.toFault
  | some ins =>
    let c1 : RAMConfig := { c with pc := c.pc + 1, cost := c.cost + 1 }
    match ins with
    | .rconst d x => { c1 with reg := Function.update c.reg d x }
    | .ofNat d a => { c1 with reg := Function.update c.reg d (c.nreg a : ℝ) }
    | .add d a b => { c1 with reg := Function.update c.reg d (c.reg a + c.reg b) }
    | .sub d a b => { c1 with reg := Function.update c.reg d (c.reg a - c.reg b) }
    | .mul d a b => { c1 with reg := Function.update c.reg d (c.reg a * c.reg b) }
    | .div d a b => { c1 with reg := Function.update c.reg d (c.reg a / c.reg b) }
    | .sqrt d a => { c1 with reg := Function.update c.reg d (Real.sqrt (c.reg a)) }
    | .exp d a => { c1 with reg := Function.update c.reg d (Real.exp (c.reg a)) }
    | .log d a => { c1 with reg := Function.update c.reg d (Real.log (c.reg a)) }
    | .normCdf d a =>
        { c1 with reg := Function.update c.reg d (cdf (gaussianReal 0 1) (c.reg a)) }
    | .load d a => { c1 with reg := Function.update c.reg d (c.reg (c.nreg a)) }
    | .store a s => { c1 with reg := Function.update c.reg (c.nreg a) (c.reg s) }
    | .nconst d x => { c1 with nreg := Function.update c.nreg d x }
    | .nadd d a b => { c1 with nreg := Function.update c.nreg d (c.nreg a + c.nreg b) }
    | .nsub d a b => { c1 with nreg := Function.update c.nreg d (c.nreg a - c.nreg b) }
    | .jmp t => { c1 with pc := t }
    | .jltR a b t => if c.reg a < c.reg b then { c1 with pc := t } else c1
    | .jltN a b t => if c.nreg a < c.nreg b then { c1 with pc := t } else c1
    | .readCol a =>
        if h : c.colsRead ≤ c.signs.length ∧ c.colsRead < N then
          { c with pc := c.pc + 1, cost := c.cost + M, colsRead := c.colsRead + 1,
                   reg := fun j => if h' : c.nreg a ≤ j ∧ j < c.nreg a + M then
                     G (⟨j - c.nreg a, by omega⟩, ⟨c.colsRead, h.2⟩) else c.reg j }
        else c.toFault
    | .emit s =>
        if c.signs.length < N then
          { c1 with signs := c.signs ++ [if 0 ≤ c.reg s then (1 : ℝ) else -1] }
        else c.toFault
    | .halt => { c1 with halted := true }

/-- The configuration after `t` steps of the program `prog` on the input `G`. -/
noncomputable def ramExec (prog : List RAMInstr) (M N : ℕ) (G : Fin M × Fin N → ℝ) (t : ℕ) :
    RAMConfig :=
  (ramStep prog M N G)^[t] (RAMConfig.init M N)

/-- The run halts at step `t` without fault, having emitted exactly `N` signs. -/
def RAMHaltsOK (prog : List RAMInstr) (M N : ℕ) (G : Fin M × Fin N → ℝ) (t : ℕ) : Prop :=
  (ramExec prog M N G t).halted = true ∧ (ramExec prog M N G t).fault = false ∧
    (ramExec prog M N G t).signs.length = N

open Classical in
/-- The `k`-th sign emitted by the program on the input `G` (signs are only appended, so this is
well defined); `1` if fewer than `k + 1` signs are ever emitted. -/
noncomputable def ramSign (prog : List RAMInstr) (M N : ℕ) (G : Fin M × Fin N → ℝ) (k : ℕ) :
    ℝ :=
  if h : ∃ t, k < (ramExec prog M N G t).signs.length then
    (ramExec prog M N G (Nat.find h)).signs.getD k 1
  else 1

end ABPOnline


