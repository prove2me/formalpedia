-- Prove2me | Definitions.Def_TurnstileRank_TightBounds_WordRAM
-- name    : TurnstileRank_TightBounds_WordRAM
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T20:08:43.427465+00:00
-- url     : https://prove2.me/theorems/82297bf8-397e-42ab-9355-e8e0c5af8cd1
-- title:
--   A minimal word RAM and word-RAM implementations of linear sketching algorithms (§7)
-- statement:
--   A word RAM with $w$-bit words and $S$ memory cells. A program is a list of instructions whose operands are cell addresses, each costing one time unit: `const` (write a constant mod $2^w$); `arith op` with $+,-,\times$ modulo $2^w$, integer division and remainder ($x/0=0$, $x\bmod0=x$), bitwise and/or/xor, left shift (mod $2^w$) and right shift, and the comparisons $<,=$ (result $1$/$0$); `load d a` ($m[d]:=m[m[a]]$) and `store a s` ($m[m[a]]:=m[s]$); `jz a t`, `jmp t`, `halt`. Any access to an address $\ge S$ or a jump outside the program is a fault. `runWithin` runs a program from instruction $0$ for at most $T$ steps and returns the memory at `halt`.
--
--   A streaming algorithm `RamAlg Ρ` has, for every seed $\rho$, an initial memory `init ρ` of $S$ cells (so the seed is stored and counted), an update program, a rank program and a select program. An update $(u,\Delta)$ writes $u$ and $\Delta$ (two's complement) into cells $0,1$ and runs the update program, which must halt within $T_u$ steps. A rank query $x$ writes $x$ into cell $0$ and runs the rank program on the memory after the stream within $T_q$ steps; the answer is $m[0]/m[1]$ ($m[0]$ in two's complement, $m[1]>0$). A select query with target $a/b$ writes $a,b$ into cells $0,1$ and runs the select program; the answer is $m[0]$. Queries do not change the stored memory. The memory is $S\cdot w$ bits, which bounds everything the machine stores at any time.
--
--   `RamExec L P n T_u T_q` (an implementation of the linear sketch $L$ on $[U]$ for final mass at most $n$): the initial memories hold $w$-bit words; $(U+1)(n+1)\le2^w$ ; and for every seed of $L$ and every stream of updates with $-2^{w-1}\le\Delta<2^{w-1}$ whose final vector $f$ is nonnegative with $\|f\|_1\le n$, all updates halt within $T_u$ steps, every rank query $x\le U$ and every select query with target $a/b\in[0,\|f\|_1]$ ($a,b<2^w$, $b>0$) halts within $T_q$ steps, and every answer equals the answer of $L$ on the state $A_\rho(f)$.
--
--   `RamImpl L P n C T_u T_q` additionally requires $w\le C\log_2(nU)$, exactly the fast word-RAM clause. The unrestricted-time bit-space clauses use `RamExec` and charge every one of the $S w$ working bits; they impose no word-size cap. No logarithm is replaced by $1+\log$.
-- source:
--   Hu, Jiang, Liu, Yu (2026), Tight Bounds for Rank Estimation in Turnstile Streams, held STOC 2027 submission, SHA-256 4be4260012249f6a39249d22651326b8b78a13b1a792ae41b80f8363cd5567b6, §7, printed pp. 29–37 (PDF 30–38): Proposition 7.1, Theorems 7.3 and 7.6, Remark 7.7, §7.4

import Mathlib
import Definitions.Def_TurnstileRank_TightBounds_LinearSketch

/-!
# A minimal word RAM, and word-RAM implementations of turnstile sketches (§7)

Hu, Jiang, Liu, Yu (2026), held STOC 2027 submission (SHA-256 4be42600…), §7, printed pp. 29–37
(PDF 30–38): Proposition 7.1, Theorems 7.3 and 7.6 bound the space "with random seed included,
throughout updates and answering queries", and "on a word RAM machine with `O(log nU)`-bit words"
the update and query time. Remark 7.7 / §7.4 (p. 37): in the word model "update magnitudes … are
bounded" so that they fit in words.

**The machine.** A word RAM with `w`-bit words and `S` memory cells (addresses `0, …, S − 1`).
A program is a list of instructions; every operand is a cell address. One instruction costs one
time unit:
* `const d c` writes `c mod 2^w` to cell `d`;
* `arith op d a b` writes `op(m[a], m[b])` to cell `d`, with `+, −, ×` modulo `2^w`, integer
  division and remainder (`x / 0 = 0`, `x % 0 = x`), bitwise and/or/xor, shifts (`shl` modulo
  `2^w`), and the comparisons `<`, `=` (result `1` or `0`);
* `load d a` writes `m[m[a]]` to `d`; `store a s` writes `m[s]` to cell `m[a]` (indirect access);
* `jz a t` jumps to instruction `t` if `m[a] = 0`; `jmp t` jumps; `halt` stops.
Any access to an address `≥ S`, or a jump outside the program, is a fault. So `S · w` bits bound
everything the machine ever stores.

**Streaming on the machine (stored seed).** A `RamAlg Ρ` has an initial memory `init ρ` for each
seed `ρ` (so the seed is stored and counted), an update program and two query programs. An update
`(u, Δ)` writes `u` and `Δ` (two's complement) to cells `0, 1` and runs the update program from
instruction `0`, which must halt within the update-time budget `Tu`. A rank query `x` writes `x` to
cell `0` and runs the rank program on the memory after the stream, which must halt within `Tq`; the
answer is the rational number `m[0] / m[1]`, `m[0]` read in two's complement and `m[1] > 0`. A select
query with target `a / b` writes `a, b` to cells `0, 1` and runs the select program; the answer is
`m[0]`. Queries do not change the stored memory.

**Formalization Note.**
* Updates are integer updates `(u, Δ)` whose `Δ` fits in a word (`−2^{w−1} ≤ Δ < 2^{w−1}`), as
  word-RAM inputs must; select targets are rationals `a / b` with `a, b < 2^w`.
* `RamExec L P …` says that the machine `P`, with the same seeds as the linear sketch `L`, has
  `(U + 1)(n + 1) ≤ 2^w`, keeps every cell a word, runs
  every update within `Tu` and every query within `Tq` steps on every seed and every admissible
  stream, and answers every query exactly as `L` answers it. The machine is thereby an
  implementation of the linear sketching algorithm `L`. For bit-space bounds without a time
  claim, `S · w` counts its workspace and no word-size restriction is imposed. `RamImpl` adds
  the printed fast-implementation requirement `w ≤ C log₂(nU)` (without a boundary correction).
-/

noncomputable section

open scoped BigOperators Classical

namespace TurnstileRank.TightBounds

namespace RAM

/-- Binary word operations. -/
inductive Op where
  | add | sub | mul | div | mod | and | or | xor | shl | shr | lt | eq

/-- The value of a word operation on `w`-bit words. -/
def Op.eval (w : ℕ) : Op → ℕ → ℕ → ℕ
  | .add, x, y => (x + y) % 2 ^ w
  | .sub, x, y => (x + 2 ^ w - y % 2 ^ w) % 2 ^ w
  | .mul, x, y => (x * y) % 2 ^ w
  | .div, x, y => x / y
  | .mod, x, y => x % y
  | .and, x, y => x &&& y
  | .or, x, y => x ||| y
  | .xor, x, y => x ^^^ y
  | .shl, x, y => (x * 2 ^ y) % 2 ^ w
  | .shr, x, y => x / 2 ^ y
  | .lt, x, y => if x < y then 1 else 0
  | .eq, x, y => if x = y then 1 else 0

/-- Instructions; every operand is a cell address. -/
inductive Instr where
  | const (d c : ℕ)
  | arith (op : Op) (d a b : ℕ)
  | load (d a : ℕ)
  | store (a s : ℕ)
  | jz (a t : ℕ)
  | jmp (t : ℕ)
  | halt

/-- A program. -/
abbrev Program := List Instr

/-- A memory of `S` cells. -/
abbrev Mem (S : ℕ) := Fin S → ℕ

/-- A configuration: program counter and memory. -/
structure Config (S : ℕ) where
  pc : ℕ
  mem : Mem S

/-- Read cell `a` (a fault if `a ≥ S`). -/
def rd {S : ℕ} (m : Mem S) (a : ℕ) : Option ℕ := if h : a < S then some (m ⟨a, h⟩) else none

/-- Write `v` to cell `a` (a fault if `a ≥ S`). -/
def wr {S : ℕ} (m : Mem S) (a v : ℕ) : Option (Mem S) :=
  if h : a < S then some (Function.update m ⟨a, h⟩ v) else none

/-- One step of the machine; `halt` is a fixed point, and `none` is a fault. -/
def step (w S : ℕ) (P : Program) (c : Config S) : Option (Config S) :=
  match P[c.pc]? with
  | none => none
  | some .halt => some c
  | some (.const d v) => (wr c.mem d (v % 2 ^ w)).map fun m => ⟨c.pc + 1, m⟩
  | some (.arith op d a b) =>
      (rd c.mem a).bind fun x => (rd c.mem b).bind fun y =>
        (wr c.mem d (op.eval w x y)).map fun m => ⟨c.pc + 1, m⟩
  | some (.load d a) =>
      (rd c.mem a).bind fun p => (rd c.mem p).bind fun v =>
        (wr c.mem d v).map fun m => ⟨c.pc + 1, m⟩
  | some (.store a s) =>
      (rd c.mem a).bind fun p => (rd c.mem s).bind fun v =>
        (wr c.mem p v).map fun m => ⟨c.pc + 1, m⟩
  | some (.jz a t) => (rd c.mem a).map fun x => ⟨if x = 0 then t else c.pc + 1, c.mem⟩
  | some (.jmp t) => some ⟨t, c.mem⟩

/-- `T` steps of the machine. -/
def exec (w S : ℕ) (P : Program) : ℕ → Config S → Option (Config S)
  | 0, c => some c
  | T + 1, c => (step w S P c).bind (exec w S P T)

/-- The instruction at the program counter is `halt`. -/
def isHalted {S : ℕ} (P : Program) (c : Config S) : Prop :=
  match P[c.pc]? with
  | some .halt => True
  | _ => False

/-- Run `P` from instruction `0` on memory `m` for at most `T` steps: the memory at `halt`, or
`none` if the machine faults or has not halted after `T` steps. -/
def runWithin (w S : ℕ) (P : Program) (T : ℕ) (m : Mem S) : Option (Mem S) :=
  match exec w S P T ⟨0, m⟩ with
  | some c => if isHalted P c then some c.mem else none
  | none => none

/-- Write the input words `xs` (reduced modulo `2^w`) into cells `0, 1, …`. -/
def setInputs {S : ℕ} (w : ℕ) (m : Mem S) (xs : List ℕ) : Mem S :=
  fun i => if h : i.val < xs.length then xs[i.val] % 2 ^ w else m i

/-- Two's complement encoding of an integer in a `w`-bit word. -/
def encInt (w : ℕ) (z : ℤ) : ℕ := (z % (2 ^ w : ℤ)).toNat

/-- Two's complement decoding of a `w`-bit word. -/
def decInt (w : ℕ) (v : ℕ) : ℤ := if v < 2 ^ (w - 1) then (v : ℤ) else (v : ℤ) - 2 ^ w

end RAM

open RAM

/-- A streaming algorithm on the word RAM with seeds `Ρ`: word size, number of cells, the initial
memory of each seed (which stores the seed), and the update, rank and select programs. -/
structure RamAlg (Ρ : Type) where
  w : ℕ
  S : ℕ
  init : Ρ → Mem S
  upd : Program
  rankProg : Program
  selProg : Program

namespace RamAlg

variable {Ρ : Type}

/-- Every cell of every initial memory holds a `w`-bit word. -/
def WordsOK (P : RamAlg Ρ) : Prop := ∀ ρ i, P.init ρ i < 2 ^ P.w

/-- One update `(u, Δ)` within `Tu` steps. -/
def update (P : RamAlg Ρ) (Tu : ℕ) (m : Mem P.S) (u : ℕ) (Δ : ℤ) : Option (Mem P.S) :=
  runWithin P.w P.S P.upd Tu (setInputs P.w m [u, encInt P.w Δ])

/-- The memory after a stream of updates from seed `ρ`, each update within `Tu` steps. -/
def runStream {U : ℕ} (P : RamAlg Ρ) (Tu : ℕ) (ρ : Ρ) (s : List (Fin U × ℤ)) : Option (Mem P.S) :=
  s.foldl (fun om ud => om.bind fun m => P.update Tu m ud.1.val ud.2) (some (P.init ρ))

/-- The answer to the rank query `x` within `Tq` steps: `m[0] / m[1]` with `m[0]` in two's
complement and `m[1] > 0`. -/
def rankAns (P : RamAlg Ρ) (Tq : ℕ) (m : Mem P.S) (x : ℕ) : Option ℝ :=
  (runWithin P.w P.S P.rankProg Tq (setInputs P.w m [x])).bind fun m' =>
    (rd m' 0).bind fun num => (rd m' 1).bind fun den =>
      if 0 < den then some ((decInt P.w num : ℝ) / (den : ℝ)) else none

/-- The answer to the select query with target `a / b` within `Tq` steps: `m[0]`. -/
def selAns (P : RamAlg Ρ) (Tq : ℕ) (m : Mem P.S) (a b : ℕ) : Option ℕ :=
  (runWithin P.w P.S P.selProg Tq (setInputs P.w m [a, b])).bind fun m' => rd m' 0

/-- The final vector `f_u = Σ Δ` of a stream of integer updates. -/
def finalVecZ {U : ℕ} (s : List (Fin U × ℤ)) : Fin U → ℤ :=
  fun u => (s.map fun ud => if ud.1 = u then ud.2 else 0).sum

/-- An admissible word-RAM stream: every `Δ` fits in a `w`-bit word, and the final vector is
nonnegative with total at most `n`. -/
def AdmissibleZ {U : ℕ} (w n : ℕ) (s : List (Fin U × ℤ)) : Prop :=
  (∀ ud ∈ s, -(2 : ℤ) ^ (w - 1) ≤ ud.2 ∧ ud.2 < 2 ^ (w - 1)) ∧
    (∀ u, 0 ≤ finalVecZ s u) ∧ mass (finalVecZ s) ≤ n

end RamAlg

/-- `P` is a word-RAM implementation of the linear sketch `L` on `[U]` for streams of final mass at
most `n`, update time `Tu` and query time `Tq`: words hold
`(U + 1)(n + 1)` values; every cell is a word; on every seed of `L` and every admissible stream all
updates halt within `Tu` steps and every rank query `x ≤ U` and every select query with target
`a / b ∈ [0, ‖f‖₁]` halts within `Tq` steps with an answer; and every answer equals the answer of `L`
on the state `A_ρ(f)` of the final vector `f`. -/
def RamExec {U : ℕ} {Ρ G : Type} [AddCommGroup G] (L : LinearSketch U Ρ G Query ℝ)
    (P : RamAlg Ρ) (n : ℕ) (Tu Tq : ℕ) : Prop :=
  P.WordsOK ∧ (U + 1) * (n + 1) ≤ 2 ^ P.w ∧
    ∀ ρ ∈ L.law.support, ∀ s : List (Fin U × ℤ), RamAlg.AdmissibleZ P.w n s →
      ∃ m, P.runStream Tu ρ s = some m ∧
        (∀ x : ℕ, x ≤ U →
          P.rankAns Tq m x = some (L.dec ρ (L.state ρ (RamAlg.finalVecZ s)) (Query.rank x))) ∧
        (∀ a b : ℕ, a < 2 ^ P.w → 0 < b → b < 2 ^ P.w →
          (a : ℝ) / b ≤ (mass (RamAlg.finalVecZ s) : ℝ) →
          ∃ xh : ℕ, P.selAns Tq m a b = some xh ∧
            (xh : ℝ) = L.dec ρ (L.state ρ (RamAlg.finalVecZ s)) (Query.select ((a : ℝ) / b)))

/-- A word-RAM implementation with the printed `O(log₂(nU))` word-size bound.
The unrestricted-time bit-space clauses use `RamExec` and count all `S · w` memory bits. -/
def RamImpl {U : ℕ} {Ρ G : Type} [AddCommGroup G] (L : LinearSketch U Ρ G Query ℝ)
    (P : RamAlg Ρ) (n : ℕ) (C : ℝ) (Tu Tq : ℕ) : Prop :=
  (P.w : ℝ) ≤ C * Real.logb 2 ((n : ℝ) * U) ∧ RamExec L P n Tu Tq

end TurnstileRank.TightBounds


