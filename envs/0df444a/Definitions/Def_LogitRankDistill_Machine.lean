-- Prove2me | Definitions.Def_LogitRankDistill_Machine
-- name    : LogitRankDistill_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:59:34.295917+00:00
-- url     : https://prove2.me/theorems/44d0e588-fd81-418d-9581-6211833b7a9e
-- title:
--   The oracle real RAM (SmaleNinth core plus sample and logit instructions), its input layout and the output format of Algorithm 1
-- statement:
--   The paper's "runs in poly($N$) time" (Theorems 5.11, 5.14) is read on an **oracle real RAM**: the published real-RAM core (exact $+,-,\times,\div$ on reals, rational literals, indirect real memory through integer pointer registers, pointer set/copy/increment/decrement, comparison jumps) extended by integer pointer addition and subtraction, an integer memory, a pointer-to-real cast, and two oracle instructions:
--   - `sample a` writes the next draw $y_{1:T}\sim M$ (token codes $0,\dots,|\Sigma|-1$) into integer memory starting at the address in pointer register $a$ (one draw);
--   - `logit dst a len` reads a token sequence $y_{1:t}$ ($t<T$) from integer memory and writes the $|\Sigma|$ reals $O(y_{1:t})$ into real memory (one oracle call);
--   and `halt`. Each executed instruction is one step. No instruction solves a linear program, rounds a real, or carries an oracle value or a token.
--
--   **Input.** Integer memory holds $T,|\Sigma|,d,K,n,N_{\max}=(K+1)(|\Sigma|+1)$ and the table $m(0),\dots,m(N_{\max})$; real memory holds $\alpha,\varepsilon_\star,\delta_\star,\beta,\gamma_{\mathrm{thres}},\eta,\delta$. **Output.** At the first halted state, real memory cells $-1,\dots,-\ell$ with $\ell$ = pointer register 0. **Output format of Algorithm 1:** $[0]$ for $\bot$; otherwise $1,\bar d$ and, for $t=1,\dots,T$, the sets $\hat F_t$ and $\tilde F_t$ (size, then each member as its length and token codes) and for each $i<\bar d$ the stored values $L_{t,i}(f)$ for $f\in\tilde F_t\cup\Sigma\cup\Sigma^2$ ($\Sigma^2$ only for $t\le T-1$), all sets listed in lexicographic order of token codes.
--
--   **Formalization Note.** Tokens are coded by the fixed bijection `Fintype.equivFin Tok`. A program is a list of instructions, independent of the instance; `Admissible` asks for rational literals and no core `accept`/`reject`. The step function follows the published pattern of `GoodHypotheses.Proper.Machine` (not imported: its oracles are densities on an abstract domain).
-- source:
--   Golowich, Liu, Shetty, Provably Distilling from Modern Language Models via Low Logit Rank, manuscript of November 3, 2026 (arXiv:2512.09892; sha256 2ce0606e…), p. 30 Theorem 5.11 and p. 33 Theorem 5.14 ("runs in poly(N) time"; the machine is a reading); p. 17 sampling oracle

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_LogitRankDistill_Algorithms

namespace LogitRankDistill

/-!
# The oracle real RAM (machine model for "runs in poly(N) time") and the output format

Golowich, Liu, Shetty, *Provably Distilling from Modern Language Models via Low Logit Rank*,
manuscript of November 3, 2026 (arXiv:2512.09892; sha256 2ce0606e…), Theorem 5.11 (p. 30) and
Theorem 5.14 (p. 33): "… and runs in poly(N) time". The paper names no machine. This one is the
published real-RAM core `SmaleNinth.RAMInstr` (exact `+ − × ÷`, real literals, indirect real
memory through integer pointer registers, pointer set/copy/increment/decrement, comparison jumps)
extended, after the pattern of `GoodHypotheses.Proper.Machine`, by:
* integer pointer addition/subtraction, an integer memory `ℤ → ℤ`, and a pointer-to-real cast;
* `sample a`: writes the next draw `y_{1:T}` of the stream (`ω cursor`), token codes
  `0, …, |Σ| − 1`, into integer memory cells `p[a], …, p[a] + T − 1` (one draw from `M`);
* `logit dst a len`: reads the token codes in integer memory cells `p[a], …, p[a] + p[len] − 1`;
  if `0 ≤ p[len] < T` and every cell holds a valid code, it writes `O(y_{1:t})(z_j)` into real
  memory cells `p[dst] + j`, `j = 0, …, |Σ| − 1` (one call to the logit oracle); otherwise it
  writes `0` there;
* `halt`.
No instruction carries a token, a real logit or the oracle, so a program is fixed independently of
the instance. There is no floor, no real-to-integer cast and no instruction solving a linear
program. `Admissible` requires rational literals and forbids the core's `accept`/`reject`. Every
executed instruction costs one step; an invalid program counter is stuck and charged, so only
`halt` halts. Tokens are coded by the fixed bijection `Fintype.equivFin Tok`.
-/

open Classical

/-- An instruction of the oracle real RAM. -/
inductive Instr where
  /-- A `SmaleNinth` real-RAM instruction. -/
  | core (instruction : SmaleNinth.RAMInstr)
  /-- `p[dst] := p[a] + p[b]`. -/
  | pointerAdd (dst a b : ℕ)
  /-- `p[dst] := p[a] - p[b]`. -/
  | pointerSub (dst a b : ℕ)
  /-- `p[dst] := I[p[address]]` (integer memory). -/
  | integerLoad (dst address : ℕ)
  /-- `I[p[address]] := p[src]`. -/
  | integerStore (address src : ℕ)
  /-- `r[dst] := (p[pointer] : ℝ)`. -/
  | pointerReal (dst pointer : ℕ)
  /-- One draw `y_{1:T} ∼ M` (the next stream cell), codes into `I[p[address] + j]`, `j < T`. -/
  | sample (address : ℕ)
  /-- One logit-oracle call on the sequence coded in `I[p[address]], …, I[p[address] + p[len] − 1]`;
  answers into `M[p[dst] + j]`, `j < |Σ|`. -/
  | logit (dst address len : ℕ)
  /-- Halt. -/
  | halt

/-- A program: one finite list of instructions. -/
abbrev Program := List Instr

/-- Every real literal is rational and the core's `accept`/`reject` do not occur. -/
def Admissible (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ value) => ∃ q : ℚ, value = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True

/-- The static core table of `P` (extension instructions are placeholders, never executed by the
core). -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- A machine state. -/
structure MState where
  /-- Program counter, real registers, pointer registers, real memory. -/
  core : SmaleNinth.RAMConfig
  /-- Integer memory. -/
  intMem : ℤ → ℤ
  /-- Number of draws read from the stream so far. -/
  cursor : ℕ
  /-- Number of logit-oracle calls so far. -/
  calls : ℕ
  /-- Halted flag. -/
  halted : Bool
  /-- Number of instructions executed. -/
  work : ℕ

variable {Tok : Type*} [Fintype Tok] [DecidableEq Tok]

/-- The code `0, …, |Σ| − 1` of a token. -/
noncomputable def tokCode (y : Tok) : ℤ :=
  ((Fintype.equivFin Tok y : ℕ) : ℤ)

/-- The token with code `v`, if `v` is a valid code. -/
noncomputable def tokOfCode (v : ℤ) : Option Tok :=
  if h : 0 ≤ v ∧ v < (Fintype.card Tok : ℤ) then
    some ((Fintype.equivFin Tok).symm ⟨v.toNat, by omega⟩)
  else none

/-- One step of `P` with logit oracle `O` and stream `ω`. -/
noncomputable def step {T : ℕ} (P : Program) (O : List Tok → Tok → ℝ) (ω : ℕ → Fin T → Tok)
    (s : MState) : MState :=
  if s.halted then s else
    let t : MState := { s with
      work := s.work + 1
      core := { s.core with pc := s.core.pc + 1 } }
    match P[s.core.pc]? with
    | none => { s with work := s.work + 1 }
    | some (.core _) => { t with core := SmaleNinth.RAMStep (coreProgram P) s.core }
    | some (.pointerAdd d a b) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs d (s.core.ptrs a + s.core.ptrs b) } }
    | some (.pointerSub d a b) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs d (s.core.ptrs a - s.core.ptrs b) } }
    | some (.integerLoad d a) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs d (s.intMem (s.core.ptrs a)) } }
    | some (.integerStore a b) =>
        { t with intMem := Function.update s.intMem (s.core.ptrs a) (s.core.ptrs b) }
    | some (.pointerReal d a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs d (s.core.ptrs a : ℝ) } }
    | some (.sample a) =>
        { t with
          cursor := s.cursor + 1
          intMem := fun z =>
            if h : s.core.ptrs a ≤ z ∧ z < s.core.ptrs a + T then
              tokCode (ω s.cursor ⟨(z - s.core.ptrs a).toNat, by omega⟩)
            else s.intMem z }
    | some (.logit d a len) =>
        let ℓ := s.core.ptrs len
        let codes : List (Option Tok) :=
          (List.range ℓ.toNat).map fun j => tokOfCode (s.intMem (s.core.ptrs a + j))
        let q : List Tok := codes.reduceOption
        let valid : Prop := 0 ≤ ℓ ∧ ℓ < (T : ℤ) ∧ q.length = ℓ.toNat
        { t with
          calls := s.calls + 1
          core := { t.core with
            mem := fun z =>
              if h : s.core.ptrs d ≤ z ∧ z < s.core.ptrs d + Fintype.card Tok then
                (if valid then
                  O q ((Fintype.equivFin Tok).symm ⟨(z - s.core.ptrs d).toNat, by omega⟩)
                else 0)
              else s.core.mem z } }
    | some .halt => { t with halted := true }

/-- The state after `k` steps. -/
noncomputable def mrun {T : ℕ} (P : Program) (O : List Tok → Tok → ℝ) (ω : ℕ → Fin T → Tok)
    (s₀ : MState) (k : ℕ) : MState :=
  (step P O ω)^[k] s₀

/-- The initial state: all registers, pointers and counters `0`; integer memory holds `ints` from
cell `0`, real memory holds `reals` from cell `0`, all other cells `0`. -/
noncomputable def initMState (ints : List ℤ) (reals : List ℝ) : MState :=
  ⟨⟨0, fun _ => 0, fun _ => 0, fun z => if 0 ≤ z then reals.getD z.toNat 0 else 0⟩,
    fun z => if 0 ≤ z then ints.getD z.toNat 0 else 0, 0, 0, false, 0⟩

/-- The input of Algorithm 1: integer memory holds `T, |Σ|, d, K, n, N_max` and then the table
`m(0), …, m(N_max)` with `N_max = (K + 1)(|Σ| + 1)` (an upper bound on every `|F̃_t|`); real
memory holds `α, ε⋆, δ⋆, β, γ_thres, η, δ`. The model is reached only through `sample` and
`logit`. -/
noncomputable def algInput (T q d : ℕ) (α ε δ : ℝ) (p : Params) : MState :=
  initMState
    ([(T : ℤ), (q : ℤ), (d : ℤ), (p.K : ℤ), (p.n : ℤ), (((p.K + 1) * (q + 1) : ℕ) : ℤ)] ++
      (List.range ((p.K + 1) * (q + 1) + 1)).map fun N => ((p.m N : ℕ) : ℤ))
    [α, ε, δ, p.β, p.γthres, p.η, p.δ]

/-- The run halts within `B` steps on the stream `ω`. -/
def HaltsWithin {T : ℕ} (P : Program) (O : List Tok → Tok → ℝ) (ω : ℕ → Fin T → Tok)
    (s₀ : MState) (B : ℝ) : Prop :=
  ∃ k : ℕ, (k : ℝ) ≤ B ∧ (mrun P O ω s₀ k).halted = true

/-- The output of a halted run: real memory cells `−1, −2, …, −ℓ` at the first halted state, where
`ℓ = p[0]` there (`[]` if `p[0] < 0` or the run never halts). -/
noncomputable def mOutput {T : ℕ} (P : Program) (O : List Tok → Tok → ℝ) (ω : ℕ → Fin T → Tok)
    (s₀ : MState) : List ℝ :=
  if hk : ∃ k, (mrun P O ω s₀ k).halted = true then
    let s := mrun P O ω s₀ (Nat.find hk)
    (List.range (s.core.ptrs 0).toNat).map fun j => s.core.mem (-((j : ℤ) + 1))
  else []

set_option warn.classDefReducibility false in
/-- The fixed linear order on token sequences used to list a set of sequences: lexicographic on
token codes. -/
noncomputable def seqOrder : LinearOrder (List Tok) :=
  LinearOrder.lift' (List.map fun y : Tok => (Fintype.equivFin Tok y : ℕ))
    (List.map_injective_iff.mpr fun _ _ h => (Fintype.equivFin Tok).injective (Fin.ext h))

/-- The members of a finite set of sequences, in the order `seqOrder`. -/
noncomputable def sortSeqs (F : Finset (List Tok)) : List (List Tok) :=
  letI := (seqOrder : LinearOrder (List Tok))
  F.sort (· ≤ ·)

/-- A sequence written as reals: its length, then its token codes. -/
noncomputable def codeSeq (f : List Tok) : List ℝ :=
  (f.length : ℝ) :: f.map fun y => ((tokCode y : ℤ) : ℝ)

/-- A finite set of sequences written as reals: its size, then its members in order. -/
noncomputable def codeSet (F : Finset (List Tok)) : List ℝ :=
  (F.card : ℝ) :: (sortSeqs F).flatMap codeSeq

/-- The output of Algorithm 1 written as a list of reals: `[0]` for `⊥`; otherwise `1, d̄`, then
for each `t = 1, …, T`: the set `F̂_t`, the set `F̃_t`, and for each `i < d̄` the stored values
`L_{t,i}(f)` for `f` in `F̃_t ∪ Σ ∪ Σ²` (`Σ²` only for `t ≤ T − 1`), in the order `seqOrder`. -/
noncomputable def serialize (T : ℕ) : Option (Learned Tok) → List ℝ
  | none => [0]
  | some D =>
      [1, (D.dbar : ℝ)] ++ (List.range' 1 T).flatMap fun t =>
        codeSet (D.Fhat t) ++ codeSet (D.Ftil t) ++
          (List.range D.dbar).flatMap fun i =>
            (sortSeqs (D.Ftil t ∪
              ((Finset.univ : Finset Tok).image fun y => [y]) ∪
              (if t + 1 ≤ T then
                (Finset.univ : Finset (Tok × Tok)).image fun yz => [yz.1, yz.2] else ∅))).map
              fun f => D.vals t i f

end LogitRankDistill


