-- Prove2me | Definitions.Def_OverflowBinPacking_IID_Supplement_Computation
-- name    : OverflowBinPacking_IID_Supplement_Computation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:54:31.907271+00:00
-- url     : https://prove2.me/theorems/fe887083-ca96-4232-b91b-abe7dda61d61
-- title:
--   Executable distribution-oracle policy compilers and resource obligations
-- statement:
--   The published general real RAM supplies arithmetic, indirect memory, comparisons, indices, halting, and independent uniforms. Extend its instruction set only by distribution CDF and truncated-first-moment queries, each charged one operation. Program literals must be rational and the compiler is deterministic. Its finite output is a data vector for a fixed finite decision program. A placement run receives the known laws, parameters, the observed size prefix and its previous assignments; it receives no current or future size.
--   $$T_{\mathrm{charged}}=t+1+|\mathrm{code}|+n\bigl(\mathrm{fuel}+|\mathrm{data}|+4n+6\bigr).$$
--   This count includes construction, output size, decision instructions and prefix-handling overhead. Every fixed random tape induces an ordinary deterministic rule; expected cost averages over independent simulation uniforms. Out-of-range actions or attempts to reuse a broken bin open a fresh bin. The compiler-correctness predicate requires actual halting, polynomial finite output and decision fuel, feasibility, measurable integrable expected cost, and comparison with every deterministic benchmark. These are all conclusions required of a program by the theorem, not assumptions on an unspecified algorithm. This supports auditable existential algorithm statements while the separate DP module gives the paper's backward recursion.
-- source:
--   Perez-Salazar, Singh & Toriello, Adaptive Bin Packing with Overflow, arXiv:2007.11532v2, pp. 6, 20–26, Theorems 1.5, 6.1 and §6.5

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_OverflowBinPacking_IID_Supplement_Capacity
import Definitions.Def_OverflowBinPacking_IID_Supplement_DP

namespace OverflowBinPacking.IID.Supplement
open MeasureTheory

/-- Extend the published general real RAM only by distribution access. A query
costs one step, as do the RAM's arithmetic, memory and comparison operations. -/
inductive OracleInstr where
  | core (op : MatMulTimeLP.Instr)
  | cdf (dst law bound : ℕ)
  | moment (dst law bound : ℕ)

abbrev OracleProgram := List OracleInstr

/-- Finite rational constants; a compiler is deterministic. A decision program
may draw uniforms to implement the paper's causal simulation of X'. -/
def InstructionAllowed (random : Bool) : OracleInstr → Prop
  | .core (.rconst _ x) => ∃ q : ℚ, x = (q : ℝ)
  | .core (.gauss _) => False
  | .core (.unif _) => random = true
  | _ => True

def ProgramAllowed (random : Bool) (P : OracleProgram) : Prop :=
  ∀ op ∈ P, InstructionAllowed random op

/-- Invalid law indices return zero. This never supplies a nonlocal input. -/
noncomputable def oracleLaw {n : ℕ} (μ : Fin n → Measure ℝ) (i : ℕ) : Measure ℝ :=
  if h : i < n then μ ⟨i, h⟩ else 0

noncomputable def oracleStep {n : ℕ} (μ : Fin n → Measure ℝ) (P : OracleProgram)
    (ω : MatMulTimeLP.Tape) (t : ℕ) (s : MatMulTimeLP.State) : MatMulTimeLP.State :=
  match P[s.pc]? with
  | none => s
  | some (.core op) =>
    MatMulTimeLP.step ((List.replicate s.pc MatMulTimeLP.Instr.halt) ++ [op]) ω t s
  | some (.cdf d i b) =>
    ⟨s.pc + 1, Function.update s.R d ((oracleLaw μ (s.N i)).real (Set.Iic (s.R b))), s.N⟩
  | some (.moment d i b) =>
    ⟨s.pc + 1, Function.update s.R d
      (∫ x in Set.Iic (s.R b), x ∂oracleLaw μ (s.N i)), s.N⟩

noncomputable def oracleRun {n : ℕ} (μ : Fin n → Measure ℝ) (P : OracleProgram)
    (input : List ℝ) (ω : MatMulTimeLP.Tape) : ℕ → MatMulTimeLP.State
  | 0 => MatMulTimeLP.initState input
  | t + 1 => oracleStep μ P ω t (oracleRun μ P input ω t)

def oracleHalted (P : OracleProgram) (s : MatMulTimeLP.State) : Prop :=
  P[s.pc]? = none ∨ P[s.pc]? = some (.core .halt)

/-- A compiler outputs a finite table/data vector. The decision procedure is a
fixed finite program, supplied with this data and the observed prefix at each step. -/
structure Scheme where
  compiler : OracleProgram
  decision : OracleProgram

def Scheme.Allowed (A : Scheme) : Prop :=
  ProgramAllowed false A.compiler ∧ ProgramAllowed true A.decision

/-- Output convention: N[0] cells of data R[0..], N[1] steps per decision. -/
structure PolicyCode where
  decision : OracleProgram
  data : List ℝ
  fuel : ℕ

noncomputable def Scheme.output {n : ℕ} (A : Scheme) (μ : Fin n → Measure ℝ)
    (C ε : ℝ) (t : ℕ) : PolicyCode :=
  let s := oracleRun μ A.compiler [n, C, ε] (fun _ => (0, 0)) t
  ⟨A.decision, (List.range (s.N 0)).map s.R, s.N 1⟩

def PolicyCode.size (B : PolicyCode) : ℕ := B.decision.length + B.data.length + 2

/-- Input access is causal by construction: only x_k for k<i is present.
The packing prefix records past random decisions. Out-of-range actions and actions
on broken bins are completed by opening the fresh bin i. -/
noncomputable def codeChoice {n : ℕ} (B : PolicyCode) (μ : Fin n → Measure ℝ)
    (C ε c : ℝ) (ω : MatMulTimeLP.Tape) (x : Fin n → ℝ)
    (p : List (Fin n)) (i : Fin n) : Fin n :=
  let obs := ((List.finRange n).filter (fun k => k < i)).map x
  let input : List ℝ := [(n : ℝ), C, ε, (i.val : ℝ), (B.data.length : ℝ)] ++ B.data ++ obs ++
    (p.map (fun j => (j.val : ℝ)))
  let s := oracleRun μ B.decision input (fun k => ω (Nat.pair i.val k)) B.fuel
  if hj : s.N 0 < n then
    let j : Fin n := ⟨s.N 0, hj⟩
    if j ≤ i ∧ usage (fun k _ => (p[k.val]?).getD k) x j i ≤ c then j else i
  else i

noncomputable def codePrefix {n : ℕ} (B : PolicyCode) (μ : Fin n → Measure ℝ)
    (C ε c : ℝ) (ω : MatMulTimeLP.Tape) (x : Fin n → ℝ) : ℕ → List (Fin n)
  | 0 => []
  | t + 1 =>
    let p := codePrefix B μ C ε c ω x t
    if h : t < n then p ++ [codeChoice B μ C ε c ω x p ⟨t, h⟩] else p

noncomputable def codeRule {n : ℕ} (B : PolicyCode) (μ : Fin n → Measure ℝ)
    (C ε c : ℝ) (ω : MatMulTimeLP.Tape) : Rule n :=
  fun i x => ((codePrefix B μ C ε c ω x (i.val + 1))[i.val]?).getD i

/-- The source's expected cost includes the simulation's independent uniforms. -/
noncomputable def codeCost {n : ℕ} (B : PolicyCode) (μ : Fin n → Measure ℝ)
    (C ε c : ℝ) : ℝ :=
  ∫ ω, costAt μ C c (codeRule B μ C ε c ω) ∂MatMulTimeLP.tapeLaw

/-- Uniform construction-time/representation obligations. All resource estimates,
correctness and admissibility are conclusions of the theorem using this predicate,
never input assumptions. The finite program's execution determines the output. -/
def Scheme.Compiles {n : ℕ} (A : Scheme) (μ : Fin n → Measure ℝ) (C ε : ℝ)
    (timeBound : ℝ) (polyConst polyDegree : ℕ) (capacity factor : ℝ) : Prop :=
  ∃ t : ℕ, (t + 1 : ℝ) ≤ timeBound ∧
    oracleHalted A.compiler (oracleRun μ A.compiler [n, C, ε] (fun _ => (0, 0)) t) ∧
    let B := A.output μ C ε t
    (t + 1 + B.size + n * (B.fuel + B.data.length + 4 * n + 6) : ℝ) ≤ timeBound ∧
    B.size ≤ polyConst * (n + 1) ^ polyDegree ∧
    B.fuel ≤ polyConst * (n + 1) ^ polyDegree ∧
    (∀ ω, PolicyAt capacity (codeRule B μ C ε capacity ω)) ∧
    Measurable (fun ω => costAt μ C capacity (codeRule B μ C ε capacity ω)) ∧
    Integrable (fun ω => costAt μ C capacity (codeRule B μ C ε capacity ω)) MatMulTimeLP.tapeLaw ∧
    ∀ a : Rule n, IsPolicy a → codeCost B μ C ε capacity ≤ factor * cost μ C a

end OverflowBinPacking.IID.Supplement


