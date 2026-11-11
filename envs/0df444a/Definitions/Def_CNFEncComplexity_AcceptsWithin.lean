-- Prove2me | Definitions.Def_CNFEncComplexity_AcceptsWithin
-- name    : CNFEncComplexity_AcceptsWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:31:07.74243+00:00
-- url     : https://prove2.me/theorems/c2070bc5-2786-4cbd-a24e-95197d40a7ab
-- title:
--   Nondeterministic RAM acceptance within logarithmic cost $t$
-- statement:
--   Fix a program and an input string $w\in\{0,1\}^*$ on a read-only tape that is read sequentially. A configuration consists of the program counter, the registers $r_0,r_1,r_2,\dots$ (all natural numbers, $r_0$ the accumulator) and the position of the input head. The machine starts with program counter $0$, all registers $0$ and the head on the first symbol. Each instruction acts as listed in `Instr`; $\mathtt{read}$ returns the next input bit as $0$ or $1$, or the end marker $2$ past the end of the input, and advances the head.
--
--   Costs follow the **logarithmic cost criterion**: with $\ell(v)=\lfloor\log_2 v\rfloor+2$ for $v\ge1$ and $\ell(0)=1$ the bit length, one step costs $1$ plus $\ell$ of every operand, address and value it reads or writes.
--
--   The program **accepts $w$ within cost $t$** if some finite run reaches a $\mathtt{halt}$ instruction with $r_0=1$ and the total cost of the run, the halting step (cost $1+\ell(r_0)$) included, is at most $t$.
--
--   **Formalization Note** This is a reading of the informal model of §3.1, which follows Robson [Rob91] without reproducing it. Acceptance is existential: runs that reject, or cost more than $t$, are irrelevant. Halting with $r_0\ne1$, or a program counter outside the program, rejects. The verification file checks that the predicate can be both true and false (`[read, halt]` accepts $1$ and never accepts $0$).
-- source:
--   Krapivin, Przybocki, Subercaseaux, The CNF Encoding Complexity of Boolean Functions, arXiv:2611.05614 (held version, sha256 97421ce1…), §3.1, pp.10–11 (PDF 11–12)

import Mathlib
import Definitions.Def_CNFEncComplexity_Instr

namespace CNFEncComplexity

/-- A configuration of the nondeterministic RAM: program counter, registers `r₀, r₁, …`
(`reg 0` is the accumulator r₀) and the position of the head on the read-only input tape. -/
structure Config where
  pc : ℕ
  reg : ℕ → ℕ
  head : ℕ

/-- The length in bits `ℓ(v) = size(v) + 1` of a number, for the logarithmic cost criterion
(`ℓ(0) = 1`). -/
def bitLen (v : ℕ) : ℕ := Nat.size v + 1

/-- The symbol under the input head: the input bit as `0`/`1`, or the end marker `2` past the end
of the input. -/
def readSym (w : List Bool) (h : ℕ) : ℕ :=
  match w[h]? with
  | some true => 1
  | some false => 0
  | none => 2

/-- One transition `Step prog w c c' k` of program `prog` on input tape `w`, from `c` to `c'`,
with logarithmic cost `k`: one plus the bit length of every operand, address and value read or
written. `njump` has two successors; `halt` and a program counter outside the program have none. -/
inductive Step (prog : List Instr) (w : List Bool) : Config → Config → ℕ → Prop where
  | loadc {c : Config} {v : ℕ} (h : prog[c.pc]? = some (Instr.loadc v)) :
      Step prog w c ⟨c.pc + 1, Function.update c.reg 0 v, c.head⟩ (1 + bitLen v)
  | load {c : Config} {j : ℕ} (h : prog[c.pc]? = some (Instr.load j)) :
      Step prog w c ⟨c.pc + 1, Function.update c.reg 0 (c.reg j), c.head⟩
        (1 + bitLen j + bitLen (c.reg j))
  | loadi {c : Config} {j : ℕ} (h : prog[c.pc]? = some (Instr.loadi j)) :
      Step prog w c ⟨c.pc + 1, Function.update c.reg 0 (c.reg (c.reg j)), c.head⟩
        (1 + bitLen j + bitLen (c.reg j) + bitLen (c.reg (c.reg j)))
  | store {c : Config} {j : ℕ} (h : prog[c.pc]? = some (Instr.store j)) :
      Step prog w c ⟨c.pc + 1, Function.update c.reg j (c.reg 0), c.head⟩
        (1 + bitLen j + bitLen (c.reg 0))
  | storei {c : Config} {j : ℕ} (h : prog[c.pc]? = some (Instr.storei j)) :
      Step prog w c ⟨c.pc + 1, Function.update c.reg (c.reg j) (c.reg 0), c.head⟩
        (1 + bitLen j + bitLen (c.reg j) + bitLen (c.reg 0))
  | add {c : Config} {j : ℕ} (h : prog[c.pc]? = some (Instr.add j)) :
      Step prog w c ⟨c.pc + 1, Function.update c.reg 0 (c.reg 0 + c.reg j), c.head⟩
        (1 + bitLen j + bitLen (c.reg 0) + bitLen (c.reg j))
  | sub {c : Config} {j : ℕ} (h : prog[c.pc]? = some (Instr.sub j)) :
      Step prog w c ⟨c.pc + 1, Function.update c.reg 0 (c.reg 0 - c.reg j), c.head⟩
        (1 + bitLen j + bitLen (c.reg 0) + bitLen (c.reg j))
  | read {c : Config} (h : prog[c.pc]? = some Instr.read) :
      Step prog w c ⟨c.pc + 1, Function.update c.reg 0 (readSym w c.head), c.head + 1⟩
        (1 + bitLen (readSym w c.head))
  | jump {c : Config} {l : ℕ} (h : prog[c.pc]? = some (Instr.jump l)) :
      Step prog w c ⟨l, c.reg, c.head⟩ (1 + bitLen l)
  | jzeroTaken {c : Config} {l : ℕ} (h : prog[c.pc]? = some (Instr.jzero l)) (h0 : c.reg 0 = 0) :
      Step prog w c ⟨l, c.reg, c.head⟩ (1 + bitLen l + bitLen (c.reg 0))
  | jzeroNotTaken {c : Config} {l : ℕ} (h : prog[c.pc]? = some (Instr.jzero l)) (h0 : c.reg 0 ≠ 0) :
      Step prog w c ⟨c.pc + 1, c.reg, c.head⟩ (1 + bitLen l + bitLen (c.reg 0))
  | njumpLeft {c : Config} {l₁ l₂ : ℕ} (h : prog[c.pc]? = some (Instr.njump l₁ l₂)) :
      Step prog w c ⟨l₁, c.reg, c.head⟩ (1 + bitLen l₁ + bitLen l₂)
  | njumpRight {c : Config} {l₁ l₂ : ℕ} (h : prog[c.pc]? = some (Instr.njump l₁ l₂)) :
      Step prog w c ⟨l₂, c.reg, c.head⟩ (1 + bitLen l₁ + bitLen l₂)

/-- A finite run `Reaches prog w c c' k`: a sequence of transitions from `c` to `c'` of total
cost `k`. -/
inductive Reaches (prog : List Instr) (w : List Bool) : Config → Config → ℕ → Prop where
  | refl (c : Config) : Reaches prog w c c 0
  | step {c c' c'' : Config} {k k' : ℕ} :
      Step prog w c c' k → Reaches prog w c' c'' k' → Reaches prog w c c'' (k + k')

/-- The initial configuration: program counter `0`, every register `0`, head on the first input
symbol. -/
def initConfig : Config := ⟨0, fun _ => 0, 0⟩

/-- **Nondeterministic RAM acceptance within cost `t`.** Krapivin, Przybocki, Subercaseaux, *The CNF Encoding Complexity of Boolean Functions*, arXiv:2611.05614 (held version, sha256 97421ce1…), §3.1, pp.10–11 (PDF 11–12):
"a machine is specified by a sequence of instructions (i₁, . . . , i_T) … The input is given on a
read-only tape, which is read sequentially (i.e., no random access). There are infinitely many
registers r₀, r₁, r₂, . . ., with r₀ representing a special accumulator register … As with Robson, we
use the logarithmic cost criterion, where the cost of an operation is proportional to the lengths of
its operands measured in bits."

`AcceptsWithin prog w t`: some finite run of `prog` on the input tape `w`, from `initConfig`,
reaches a `halt` instruction with `r₀ = 1`, and the total cost of the run, the halting step included
(cost `1 + ℓ(r₀)`), is at most `t`.

**Formalization Note.** This is a reading of the paper's informal model (Robson's [Rob91] model is not
reproduced in the paper). The input is read only sequentially by `read`, which returns the end
marker `2` past the end of the input. Costs follow the logarithmic (Cook–Reckhow) criterion, with
`ℓ(v) = size(v) + 1` charged for every operand, address and value an instruction reads or writes.
Acceptance is existential (nondeterministic): runs that do not accept, or exceed cost `t`, are
irrelevant. Halting with `r₀ ≠ 1`, or a program counter outside the program, rejects. -/
def AcceptsWithin (prog : List Instr) (w : List Bool) (t : ℕ) : Prop :=
  ∃ (c : Config) (k : ℕ), Reaches prog w initConfig c k ∧ prog[c.pc]? = some Instr.halt ∧
    c.reg 0 = 1 ∧ k + (1 + bitLen (c.reg 0)) ≤ t

end CNFEncComplexity


