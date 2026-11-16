-- Prove2me | Definitions.Def_TransparencyTeamContracts_Submodular_Supplement_OracleMachine
-- name    : TransparencyTeamContracts_Submodular_Supplement_OracleMachine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:11:52.740195+00:00
-- url     : https://prove2.me/theorems/42d96c9b-0984-4641-8474-6116d9dd077f
-- title:
--   Finite deterministic value-oracle programs and charged execution
-- statement:
--   The general computation model is the published real pointer RAM extended with one value-query instruction reading an already stored subset bitmap. A finite program has no function-valued instructions, optimization oracle or encoded optimum. Every scalar operation, comparison, pointer or memory operation and query is charged; the number of queries is counted separately along the same run. Code literals must be rational. The exact-real dialect additionally allows charged square roots and logarithms; the field-only admissibility condition excludes both for the numerical algorithms in Lemmas D.2, D.5 and Theorem 4.4.
--
--   Inputs contain the size, accuracy, costs, scale interval, initial teams and fixed shares; the technology is accessible only through value queries. The output memory contains a team bitmap and individual contract shares. The predicate for computation requires an actual halted run with both cost bounds and the specified output certificate. Uniform polynomial bounds have constants and degrees chosen before all sizes, costs, technologies and accuracies.
-- source:
--   Paul Duetting, Yingkai Li, Inbal Talgam-Cohen, Jinzhao Wu, STOC 2027 submission #1292 (October 2026), Appendix D, printed pp. 33–46 (PDF pp. 35–48)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_TransparencyTeamContracts_Submodular_Supplement_Benchmarks

open Finset
open scoped Classical

namespace TransparencyTeamContracts.Submodular.Supplement

/-- A finite deterministic value-oracle dialect of the published real RAM.
There are no function-valued instructions or optimization primitives. Square roots
and logarithms implement the exact-real interpretation of Appendix D; each is charged.
A query reads a bitmap already stored by scalar stores, not an implicitly computed team. -/
inductive OracleInstr where
  | core (i : SmaleNinth.RAMInstr)
  | sqrt (dst src : ℕ)
  | log (dst src : ℕ)
  | value (dst base : ℕ)
  | halt

abbrev OracleProgram := List OracleInstr

def Admissible (p : OracleProgram) : Prop :=
  ∀ ins ∈ p, match ins with
    | .core (.const _ r) => ∃ q : ℚ, r = q
    | .core .accept | .core .reject => False
    | _ => True

/-- The numerical algorithms D.2 and 4.4 use only field arithmetic and
comparisons. Square roots and logarithms are approximated by their code, not
granted as exact unit-cost instructions. D.3 alone uses the richer exact dialect. -/
def FieldAdmissible (p : OracleProgram) : Prop :=
  Admissible p ∧ ∀ ins ∈ p, match ins with
    | .sqrt _ _ | .log _ _ => False
    | _ => True

/-- Query argument bitmap, at the address held in pointer `base`. -/
noncomputable def querySet (n : ℕ) (s : SmaleNinth.RAMConfig) (base : ℕ) : Finset (Fin n) :=
  univ.filter (fun i => s.mem (s.ptrs base + (i : ℕ)) = 1)

noncomputable def machineStep {n : ℕ} (p : OracleProgram)
    (f : Finset (Fin n) → ℝ) (s : SmaleNinth.RAMConfig) : SmaleNinth.RAMConfig :=
  match p[s.pc]? with
  | none | some .halt => s
  | some (.value dst base) =>
      {s with pc := s.pc + 1, regs := Function.update s.regs dst (f (querySet n s base))}
  | some (.sqrt dst src) =>
      {s with pc := s.pc + 1, regs := Function.update s.regs dst (Real.sqrt (s.regs src))}
  | some (.log dst src) =>
      {s with pc := s.pc + 1, regs := Function.update s.regs dst (Real.log (s.regs src))}
  | some (.core (.jle i target)) => {s with pc := if s.regs i ≤ 0 then target else s.pc + 1}
  | some (.core (.pjle i j target)) =>
      {s with pc := if s.ptrs i ≤ s.ptrs j then target else s.pc + 1}
  | some (.core i) =>
      let t := SmaleNinth.RAMStep [i] {s with pc := 0}
      {t with pc := s.pc + 1}

/-- Scalar input header (accuracy, lower/upper scales, residual share), then costs,
team bitmap, second-team bitmap and fixed shares. Pointer zero initially contains n.
Rewards are available only through the value instruction. -/
noncomputable def machineInput {n : ℕ} (c : Fin n → ℝ) (ε lo hi B : ℝ)
    (S T : Finset (Fin n)) (α : Fin n → ℝ) : SmaleNinth.RAMConfig :=
  ⟨0, fun _ => 0, fun j => if j = 0 then n else 0,
    fun z => if z = 0 then ε else if z = 1 then lo else if z = 2 then hi else
      if z = 3 then B else
      if h : 10 ≤ z ∧ z < 10 + n then c ⟨(z - 10).toNat, by omega⟩ else
      if h : 10 + n ≤ z ∧ z < 10 + 2 * n then
        if (⟨(z - 10 - n).toNat, by omega⟩ : Fin n) ∈ S then 1 else 0 else
      if h : 10 + 2 * n ≤ z ∧ z < 10 + 3 * n then
        if (⟨(z - 10 - 2 * n).toNat, by omega⟩ : Fin n) ∈ T then 1 else 0 else
      if h : 10 + 3 * n ≤ z ∧ z < 10 + 4 * n then
        α ⟨(z - 10 - 3 * n).toNat, by omega⟩ else 0⟩

noncomputable def machineRun {n : ℕ} (p : OracleProgram) (f : Finset (Fin n) → ℝ)
    (input : SmaleNinth.RAMConfig) (t : ℕ) : SmaleNinth.RAMConfig :=
  (machineStep p f)^[t] input

noncomputable def queryCount {n : ℕ} (p : OracleProgram) (f : Finset (Fin n) → ℝ)
    (input : SmaleNinth.RAMConfig) (t : ℕ) : ℕ :=
  ∑ k ∈ range t, match p[(machineRun p f input k).pc]? with
    | some (.value _ _) => 1
    | _ => 0

/-- Negative output cells alternate membership bits and shares. -/
noncomputable def outputTeam (n : ℕ) (s : SmaleNinth.RAMConfig) : Finset (Fin n) :=
  univ.filter (fun i => s.mem (-1 - 2 * (i : ℕ)) = 1)
def outputContract (n : ℕ) (s : SmaleNinth.RAMConfig) : Fin n → ℝ :=
  fun i => s.mem (-2 - 2 * (i : ℕ))

/-- The same finite program, input, and actual run witness both charged counts.
No arbitrary function or external solution is passed as an output oracle. -/
def Computes {n : ℕ} (p : OracleProgram) (f : Finset (Fin n) → ℝ)
    (input : SmaleNinth.RAMConfig) (steps queries : ℕ)
    (Out : (Fin n → ℝ) → Finset (Fin n) → Prop) : Prop :=
  ∃ t ≤ steps, p[(machineRun p f input t).pc]? = some .halt ∧
    queryCount p f input t ≤ queries ∧
    Out (outputContract n (machineRun p f input t)) (outputTeam n (machineRun p f input t))

noncomputable def smallBudget (C d n : ℕ) (ζ lo hi : ℝ) : ℕ :=
  C * (n + 1 + ⌈1 / ζ⌉₊ + ⌈1 + Real.log (hi / lo)⌉₊) ^ d
noncomputable def mainBudget (C d n : ℕ) (ε : ℝ) : ℕ :=
  C * (n + 1) ^ (C * (1 + ⌈1 / ε⌉₊) ^ d)

end TransparencyTeamContracts.Submodular.Supplement


