-- Prove2me | Definitions.Def_SubsetConvFPRAS_Machine
-- name    : SubsetConvFPRAS_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:57.111129+00:00
-- url     : https://prove2.me/theorems/5885f20a-67e1-483c-aac2-0e609e974f04
-- title:
--   The arithmetic model: a unit-cost real RAM with fair coins and two value oracles
-- statement:
--   The paper counts "arithmetic operations and evaluation oracle calls" with no bit lengths, on real weights (it calls this "the arithmetic model", p.44). This file fixes that model, so that "there is an algorithm" is a statement about programs.
--
--   A **program** is a finite list of instructions over real registers, integer pointer registers, a real memory and an integer memory indexed by $\mathbb Z$, and bitmaps (subsets of the ground set $\{0,\dots,n-1\}$) indexed by $\mathbb Z$. The instructions are those of the published real RAM `SmaleNinth.RAMInstr` (rational constants, $+,-,\times,\div$ with $x/0=0$, indirect load and store, pointer set, copy, increment, decrement, and conditional jumps on $r\le0$ and $p\le p'$), plus: pointer addition and subtraction, integer load and store, the cast of a pointer to a real, **coin** (write the next fair bit of the tape), one-bit read and write of a bitmap, **query** (write $\mu(S)$ or $\nu(S)$ for the set $S$ held in a bitmap), and **halt** (output a real register).
--
--   Every executed instruction costs one unit of work, queries, coins and jumps included; a run of $k$ steps has work at most $k$, and a halted state stays put at no cost. A program is **admissible** if every literal is rational and it uses no accept/reject instruction. Fair coins come from a tape; probabilities are counts of $B$-bit tapes divided by $2^B$, since a run of $B$ steps reads at most $B$ coins.
--
--   The file also fixes the input layouts: for Theorem 1.6, integer cell $0$ holds $n$, cell $1+u$ holds $\alpha_u$, bitmaps $0,1$ hold $S_0,T_0$, and real cells $0,1,2$ hold $\varepsilon,R_\mu,R_\nu$; the layouts of Corollaries 5.6, 5.12, Theorem 5.1 and Lemma A.2 are stated next to their definitions.
--
--   **Formalization Note** Not in the language: floor, real-to-integer cast, pointer multiplication, square root, $\exp$, $\log$, a uniform real sample, and any evaluation of $g_\mu$; Appendix A.5 runs the algorithm with arithmetic only. The randomness primitive is a fair coin: the page names none for its arithmetic model, and a unit-cost uniform real would be a stronger machine, hence a weaker theorem. $\mu,\nu$ reach a program only through `query`, so a program cannot read the instance for free.
-- source:
--   Chen, Liu, An FPRAS for Counting Common Bases of Two Matroids, arXiv:2610.06724 (version held, sha256 6c1d68c2…919476), Definition 1.1, p.3; Theorem 1.6 and footnote 2, pp.4–5; Appendix A.5, p.39; Appendix C, p.44 ("the arithmetic model")

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

open scoped Classical

namespace SubsetConvFPRAS

/-!
# The arithmetic model: a unit-cost real RAM with fair coins and two value oracles

X. Chen, K. Liu, *An FPRAS for Counting Common Bases of Two Matroids*, arXiv:2610.06724 (version held,
sha256 6c1d68c2…), Definition 1.1, p.3; Theorem 1.6 and its footnote 2, pp.4–5; Appendix A.5, p.39.
The paper counts "arithmetic operations and evaluation oracle calls", with no bit lengths, on real
weights (p.44 names this "the arithmetic model"). This file makes that model precise.

The core is the published `SmaleNinth.RAMInstr`. The extension follows the shape of the published
`FasterSFM.Machine`, with these differences: two real value oracles, real output, no pointer
multiplication and no square root.

**Formalization Note.**
* Instructions: the core's constants, `+ - × ÷` (`x / 0 = 0`), indirect real load and store, pointer set,
  copy, increment, decrement, and the two conditional jumps; integer pointer `+` and `-`; integer load
  and store; the cast of a pointer to a real; `coin`; one-bit read and write of a bitmap; `query`; `halt`.
* Not in the language: pointer multiplication, floor, real-to-integer cast, square root, exp, log, a
  uniform real sample, an evaluation of `g_μ`. Appendix A.5 runs the algorithm with arithmetic only.
* `Admissible` programs use rational literals only and no core `accept`/`reject`. It restricts the
  existentially chosen program, never the input.
* Randomness is fair coins, one bit per executed `coin`. The page names no primitive for its arithmetic
  model; a unit-cost real sample would make a stronger machine, hence a weaker theorem.
* Every executed instruction costs one unit of `work`, including `query`, `coin`, `halt` and jumps. An
  invalid program counter is stuck and charged. After `halt` the state stutters at no cost. So
  `work ≤ k` after `k` steps, and a run that has halted within `k` steps has spent at most `k`.
* `μ` and `ν` occur only in the `query` branch of `step`, the tape only in the `coin` branch.
* Probabilities are by counting over `Fin B → Bool`. A run of `B` steps reads at most `B` coins, so bits
  beyond `B` are irrelevant.
-/

/-- An instruction of the model. Register, pointer and label arguments are natural numbers.
* `core i`: a `SmaleNinth` real-RAM instruction.
* `pointerAdd d a b`, `pointerSub d a b`: `p[d] := p[a] ± p[b]`.
* `integerLoad d a`, `integerStore a b`: `p[d] := I[p[a]]`, `I[p[a]] := p[b]` (integer memory).
* `pointerReal d a`: `r[d] := (p[a] : ℝ)`.
* `coin d`: `r[d] := 1` if the next tape bit is `true`, else `0`; the tape cursor advances.
* `bitWrite bank elt val`: set bit `p[elt]` of bitmap `p[bank]` to `r[val] ≠ 0`.
* `bitRead d bank elt`: `r[d] := 1` if bit `p[elt]` of bitmap `p[bank]` is set, else `0`.
* `query which d bank`: `r[d] := μ(bitmap p[bank])` if `which = false`, `ν(bitmap p[bank])` if `true`.
* `halt src`: output `r[src]` and stop. -/
inductive Instr where
  | core (instruction : SmaleNinth.RAMInstr)
  | pointerAdd (dst a b : ℕ)
  | pointerSub (dst a b : ℕ)
  | integerLoad (dst address : ℕ)
  | integerStore (address src : ℕ)
  | pointerReal (dst pointer : ℕ)
  | coin (dst : ℕ)
  | bitWrite (bank element value : ℕ)
  | bitRead (dst bank element : ℕ)
  | query (which : Bool) (dst bank : ℕ)
  | halt (src : ℕ)

/-- A program: one finite list of instructions, the same for every instance. -/
abbrev Program := List Instr

/-- Every real literal is rational, and the core halting instructions do not occur. -/
def Admissible (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ value) => ∃ q : ℚ, value = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True

/-- The static core table of `P`: extension instructions are placeholders, always dispatched by
`step`. -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- A machine state on ground set `Fin n`: the core configuration, integer memory, bitmaps, the tape
cursor, the output, and the counters. -/
structure State (n : ℕ) where
  core : SmaleNinth.RAMConfig
  integerMemory : ℤ → ℤ
  bitmap : ℤ → Finset (Fin n)
  cursor : ℕ
  output : Option ℝ
  queries : ℕ
  work : ℕ

/-- One step of `P` with value oracles `μ`, `ν` and coin tape `ω`. Bit indices outside `0 ≤ i < n` read
`0` and write nothing. -/
noncomputable def step {n : ℕ} (P : Program) (μ ν : Finset (Fin n) → ℝ) (ω : ℕ → Bool)
    (s : State n) : State n :=
  if s.output.isSome then s else
    let t := { s with
      work := s.work + 1
      core := { s.core with pc := s.core.pc + 1 } }
    match P[s.core.pc]? with
    | none => { s with work := s.work + 1 }
    | some (.core _) =>
        { t with core := SmaleNinth.RAMStep (coreProgram P) s.core }
    | some (.pointerAdd d a b) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs d (s.core.ptrs a + s.core.ptrs b) } }
    | some (.pointerSub d a b) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs d (s.core.ptrs a - s.core.ptrs b) } }
    | some (.integerLoad d a) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs d (s.integerMemory (s.core.ptrs a)) } }
    | some (.integerStore a b) =>
        { t with integerMemory := Function.update s.integerMemory (s.core.ptrs a) (s.core.ptrs b) }
    | some (.pointerReal d a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs d (s.core.ptrs a : ℝ) } }
    | some (.coin d) =>
        { t with
          cursor := s.cursor + 1
          core := { t.core with
            regs := Function.update s.core.regs d (if ω s.cursor then 1 else 0) } }
    | some (.bitWrite b e v) =>
        if hb : 0 ≤ s.core.ptrs e ∧ (s.core.ptrs e).toNat < n then
          let j : Fin n := ⟨(s.core.ptrs e).toNat, hb.2⟩
          let bank := s.core.ptrs b
          let contents := if s.core.regs v = 0 then (s.bitmap bank).erase j
            else insert j (s.bitmap bank)
          { t with bitmap := Function.update s.bitmap bank contents }
        else t
    | some (.bitRead d b e) =>
        let value : ℝ := if hb : 0 ≤ s.core.ptrs e ∧ (s.core.ptrs e).toNat < n then
          if (⟨(s.core.ptrs e).toNat, hb.2⟩ : Fin n) ∈ s.bitmap (s.core.ptrs b) then 1 else 0
          else 0
        { t with core := { t.core with regs := Function.update s.core.regs d value } }
    | some (.query which d b) =>
        { t with
          queries := s.queries + 1
          core := { t.core with
            regs := Function.update s.core.regs d
              ((if which then ν else μ) (s.bitmap (s.core.ptrs b))) } }
    | some (.halt src) => { t with output := some (s.core.regs src) }

/-- The state after `k` steps from `s₀`. -/
noncomputable def run {n : ℕ} (P : Program) (μ ν : Finset (Fin n) → ℝ) (s₀ : State n)
    (ω : ℕ → Bool) (k : ℕ) : State n :=
  (step P μ ν ω)^[k] s₀

/-- An initial state: program counter `0`, all registers and pointers `0`, the given memories and
bitmaps, cursor at the first coin, no output, both counters `0`. -/
def mkInit {n : ℕ} (ints : ℤ → ℤ) (bitmaps : ℤ → Finset (Fin n)) (reals : ℤ → ℝ) : State n :=
  ⟨⟨0, fun _ => 0, fun _ => 0, reals⟩, ints, bitmaps, 0, none, 0, 0⟩

/-- A tape from finitely many bits; later bits are `false`. -/
def extendBits {B : ℕ} (bits : Fin B → Bool) : ℕ → Bool :=
  fun k => if h : k < B then bits ⟨k, h⟩ else false

/-- The number of `B`-bit tapes on which the state after `B` steps satisfies `p`. Dividing by `2^B` gives
the probability of `p` under fair coins. -/
noncomputable def tapeCount {n : ℕ} (P : Program) (μ ν : Finset (Fin n) → ℝ) (s₀ : State n) (B : ℕ)
    (p : State n → Prop) : ℕ :=
  Nat.card {bits : Fin B → Bool // p (run P μ ν s₀ (extendBits bits) B)}

/-- Bitmaps from a list: `bitmap i` is the `i`-th entry, and empty elsewhere. -/
def bitmapsOf {n : ℕ} (l : List (Finset (Fin n))) : ℤ → Finset (Fin n) :=
  fun i => if 0 ≤ i then (l[i.toNat]?).getD ∅ else ∅

/-- Reals from a list followed by a vector: `M i` is the `i`-th entry of `l`, then `M (l.length + u) = z u`,
and `0` elsewhere. -/
noncomputable def realsOf {n : ℕ} (l : List ℝ) (z : Fin n → ℝ) : ℤ → ℝ :=
  fun i =>
    if 0 ≤ i ∧ i < l.length then (l[i.toNat]?).getD 0
    else if h : 0 ≤ i - l.length ∧ (i - l.length).toNat < n then z ⟨(i - l.length).toNat, h.2⟩
    else 0

/-- The input size in integer cell `0`, and `0` elsewhere. -/
def intsOfSize (n : ℕ) : ℤ → ℤ := fun i => if i = 0 then (n : ℤ) else 0

/-- Input of Theorem 1.6: `I 0 = n`, `I (1+u) = α u`; bitmaps `0, 1` hold `S₀, T₀`; `M 0 = ε`,
`M 1 = R_μ`, `M 2 = R_ν`. -/
noncomputable def initGoal {n : ℕ} (α : Fin n → Fin 3) (S₀ T₀ : Finset (Fin n)) (ε Rμ Rν : ℝ) :
    State n :=
  mkInit
    (fun i => if i = 0 then (n : ℤ)
      else if h : 0 ≤ i - 1 ∧ (i - 1).toNat < n then ((α ⟨(i - 1).toNat, h.2⟩ : ℕ) : ℤ) else 0)
    (bitmapsOf [S₀, T₀]) (realsOf [ε, Rμ, Rν] (fun _ : Fin 0 => 0))

/-- Input of Theorem 5.1: `I 0 = n`; bitmaps `0, 1` hold `S₀, T₀`; `M 0 = ε`, `M 1 = R_μ`, `M 2 = R_ν`.
The degrees `a, b` are not given: they are the sizes of `S₀, T₀`. -/
noncomputable def initConvolution {n : ℕ} (S₀ T₀ : Finset (Fin n)) (ε Rμ Rν : ℝ) : State n :=
  mkInit (intsOfSize n) (bitmapsOf [S₀, T₀]) (realsOf [ε, Rμ, Rν] (fun _ : Fin 0 => 0))

/-- Input of Corollary 5.6: `I 0 = n`; bitmaps `0, 1` hold `S₀, T₀`; `M 0 = t`, `M 1 = R_μ`, `M 2 = R_ν`,
`M 3 = ε`, `M (4+u) = z u`. The output pair is left in bitmaps `2, 3`. -/
noncomputable def initSampler {n : ℕ} (S₀ T₀ : Finset (Fin n)) (t Rμ Rν ε : ℝ) (z : Fin n → ℝ) :
    State n :=
  mkInit (intsOfSize n) (bitmapsOf [S₀, T₀]) (realsOf [t, Rμ, Rν, ε] z)

/-- Input of Corollary 5.12: `I 0 = n`; bitmaps `0, 1` hold `S₀, T₀`; `M 0 = R_μ`, `M 1 = R_ν`. The field
register is `M (2+u)`, for `u : Fin n`. -/
noncomputable def initField {n : ℕ} (S₀ T₀ : Finset (Fin n)) (Rμ Rν : ℝ) : State n :=
  mkInit (intsOfSize n) (bitmapsOf [S₀, T₀]) (realsOf [Rμ, Rν] (fun _ : Fin 0 => 0))

/-- The field register of Corollary 5.12: `z u = M (2+u)`. -/
def fieldOf {n : ℕ} (s : State n) : Fin n → ℝ := fun u => s.core.mem (2 + (u : ℕ))

/-- Input of Lemma A.2: `I 0 = n`; bitmaps `0, 1, 2` hold `A₀`, `C`, `O`. The oracle is the first one. The
output set of size `k`, if any, is left in bitmap `3 + k`. -/
noncomputable def initSupport {n : ℕ} (A₀ Cs Os : Finset (Fin n)) : State n :=
  mkInit (intsOfSize n) (bitmapsOf [A₀, Cs, Os]) (fun _ => 0)

end SubsetConvFPRAS


