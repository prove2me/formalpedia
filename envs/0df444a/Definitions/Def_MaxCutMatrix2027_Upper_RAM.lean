-- Prove2me | Definitions.Def_MaxCutMatrix2027_Upper_RAM
-- name    : MaxCutMatrix2027_Upper_RAM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T12:47:19.013305+00:00
-- url     : https://prove2.me/theorems/1c68df2d-39a6-4808-9270-094de366be81
-- title:
--   Unit-cost randomized RAM instructions and transition semantics
-- statement:
--   A RAM state consists of natural and real registers, three memory banks used by the program, a control stack, a random-tape cursor, an oracle-query trace, and an optional real output. The instruction syntax includes constants, arithmetic, ceiling, random-access loads and stores, comparisons, branches, loops, a geometric-gap instruction, a pair query, and halt. The only instruction that reads the graph is the pair query.
--
--   If $\operatorname{step}_{G,\omega}$ denotes one transition, execution is defined by
--   $$\operatorname{run}_{G,\omega}(0)=\mathrm{initial},\qquad
--   \operatorname{run}_{G,\omega}(t+1)=\operatorname{step}_{G,\omega}(\operatorname{run}_{G,\omega}(t)).$$
--   Each transition, including control dispatch, costs one operation. Exact geometric-gap generation, index arithmetic, real arithmetic, and ceiling follow the unit-cost randomized RAM reading of p.28. The final theorem requires all tape reads to be in range and all queried pairs to be distinct valid vertices; default values on invalid inputs are never part of a valid execution.
--
--   This supplies operational resource semantics reusable for finite oracle algorithms. It contains no accuracy promise, running-time field, or optimization primitive.
-- source:
--   Songhua He, STOC 2027 submission #351 (October 2026), §3 adjacency-matrix model; Algorithm 1 and RAM implementation, pp.13,17,28, p.28 (PDF p.28); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/351.pdf; PDF SHA-256 b38cd84079663d9e2eb7375d7bf1572d5dc7c2157cfaf90e175fd371a9503631

import Mathlib

set_option autoImplicit false

namespace MaxCutMatrix2027.Upper

/-- Unit-cost RAM operations on index words. Division and remainder are integer operations;
all divisors in Algorithm 1 are positive. No oracle optimization or MAX-CUT primitive exists. -/
inductive NatOp where
  | add | sub | mul | div | mod | max
  deriving DecidableEq

inductive RealOp where
  | add | mul | div
  deriving DecidableEq

/-- Tests read registers only. They cannot inspect the graph or random tape. -/
inductive Test where
  | lt (a b : ℕ)
  | le (a b : ℕ)
  | ne (a b : ℕ)
  | both (a b : Test)

/-- Structured syntax for a finite RAM program. `gap dst p` is the paper's exact,
unit-cost geometric-gap instruction, with parameter in real register p. Random access
loads/stores, index arithmetic, real arithmetic and real-to-index ceiling are unit cost.
Sequence, loop and conditional dispatch are also charged one transition each. -/
inductive Command where
  | natConst (dst value : ℕ)
  | natOp (dst : ℕ) (op : NatOp) (a b : ℕ)
  | realConst (dst : ℕ) (value : ℝ)
  | realOp (dst : ℕ) (op : RealOp) (a b : ℕ)
  | cast (dst src : ℕ)
  | ceil (dst src : ℕ)
  | load (dst bank addr : ℕ)
  | store (bank addr src : ℕ)
  | gap (dst parameter : ℕ)
  | query (dst u v : ℕ)
  | seq (body : List Command)
  | branch (test : Test) (yes no : List Command)
  | loop (test : Test) (body : List Command)
  | halt (output : ℕ)

/-- Registers and memory, rather than arbitrary semantic callbacks, carry the computation.
Memory is initially zero; bank identifiers in the program are 0,1,2. -/
structure RAMState where
  control : List Command
  natReg : ℕ → ℕ
  realReg : ℕ → ℝ
  memory : ℕ → ℕ → ℕ
  randomCursor : ℕ
  randomParameters : List ℝ
  queries : List (ℕ × ℕ)
  output : Option ℝ

abbrev RandomTape (L : ℕ) := Fin L → ℕ

noncomputable def natOpValue (op : NatOp) (a b : ℕ) : ℕ :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .mul => a * b
  | .div => a / b
  | .mod => a % b
  | .max => max a b

noncomputable def realOpValue (op : RealOp) (a b : ℝ) : ℝ :=
  match op with
  | .add => a + b
  | .mul => a * b
  | .div => a / b

noncomputable def testValue (r : ℕ → ℕ) : Test → Bool
  | .lt a b => decide (r a < r b)
  | .le a b => decide (r a ≤ r b)
  | .ne a b => decide (r a ≠ r b)
  | .both a b => testValue r a && testValue r b

/-- One charged transition. Only `query` sees the oracle. Out-of-range tape reads return
zero to totalize the interpreter; the goal separately requires that none occurs. -/
noncomputable def ramStep {L : ℕ} (oracle : ℕ → ℕ → Bool) (ω : RandomTape L)
    (st : RAMState) : RAMState := by
  classical
  exact match st.output, st.control with
  | some _, _ => st
  | none, [] => st
  | none, c :: tail =>
    let base := {st with control := tail}
    match c with
    | .natConst dst v => {base with natReg := Function.update st.natReg dst v}
    | .natOp dst op a b => {base with natReg := Function.update st.natReg dst (natOpValue op (st.natReg a) (st.natReg b))}
    | .realConst dst v => {base with realReg := Function.update st.realReg dst v}
    | .realOp dst op a b => {base with realReg := Function.update st.realReg dst (realOpValue op (st.realReg a) (st.realReg b))}
    | .cast dst src => {base with realReg := Function.update st.realReg dst (st.natReg src)}
    | .ceil dst src => {base with natReg := Function.update st.natReg dst ⌈st.realReg src⌉₊}
    | .load dst bank addr => {base with natReg := Function.update st.natReg dst (st.memory bank (st.natReg addr))}
    | .store bank addr src => {base with memory := Function.update st.memory bank (Function.update (st.memory bank) (st.natReg addr) (st.natReg src))}
    | .gap dst p => {base with natReg := Function.update st.natReg dst (if h : st.randomCursor < L then ω ⟨st.randomCursor, h⟩ else 0), randomCursor := st.randomCursor + 1, randomParameters := st.realReg p :: st.randomParameters}
    | .query dst u v => {base with natReg := Function.update st.natReg dst (if oracle (st.natReg u) (st.natReg v) then 1 else 0), queries := (st.natReg u, st.natReg v) :: st.queries}
    | .seq body => {base with control := body ++ tail}
    | .branch test yes no => {base with control := (if testValue st.natReg test then yes else no) ++ tail}
    | .loop test body => {base with control := if testValue st.natReg test then body ++ (c :: tail) else tail}
    | .halt out => {base with output := some (st.realReg out)}

/-- t is the number of executed transitions, not a freely supplied cost. -/
noncomputable def ramRun {L : ℕ} (oracle : ℕ → ℕ → Bool) (ω : RandomTape L)
    (initial : RAMState) : ℕ → RAMState
  | 0 => initial
  | t + 1 => ramStep oracle ω (ramRun oracle ω initial t)

end MaxCutMatrix2027.Upper


