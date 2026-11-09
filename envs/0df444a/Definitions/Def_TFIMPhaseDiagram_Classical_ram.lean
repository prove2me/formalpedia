-- Prove2me | Definitions.Def_TFIMPhaseDiagram_Classical_ram
-- name    : TFIMPhaseDiagram_Classical_ram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:01:49.471196+00:00
-- url     : https://prove2.me/theorems/a0421a94-686c-4608-b907-f5fd38ee5ee1
-- title:
--   Uniform Real RAM programs and quantum estimator queries
-- statement:
--   Programs are finite instruction lists extending the published real/index-cell machine by scalar exponential, logarithm, truncation, and casts between nonnegative integer indices and real cells. Only rational literals and the source's uniform random draws are admissible; Gaussian and square-root instructions are excluded. Every instruction costs one step. Input arrays are laid out explicitly in memory and outputs occupy cells following the input. The random tape has independent uniform coordinates; the unused Gaussian coordinate of the published tape is inaccessible to admissible programs.
--
--   For each query, the success contract requires termination within a charged integer budget, measurable output, and probability at least $1-\delta$ of the appropriate error event. A uniform polynomial budget has the form
--   $$C\left\lceil(1+n+\max|J|+\max|h|+\max|\eta|+\epsilon^{-1})^d\right\rceil\bigl(1+\lceil\log(1/\delta)\rceil\bigr).$$
--   Programs and constants precede all varying data in the target theorem. No target value, output law, sampler, matrix exponential, or success certificate is a machine instruction or an input.
--
--   The explicit annealing counts are $m=\lceil16e^2L/\epsilon^2\rceil$, $K=Lm$, $r=2\lceil16\log(1/\delta)\rceil+1$, and $K'=Kr$.
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026), canonical source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, §2, p.5; Theorem 11, pp.7–8; proof (10)–(12), pp.10–11; P16 proof, pp.29–30

import Definitions.Def_TFIMPhaseDiagram_Classical_quantum
import Definitions.Def_MatMulTimeLP_RealRAM

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

namespace TFIMPhaseDiagram.Classical
attribute [local instance] Classical.propDecidable

/-- Extend the published core machine only by the scalar operations in Section 2. -/
inductive RAMInstruction where
  | core (i : MatMulTimeLP.Instr)
  | exp (dst src : ℕ)
  | log (dst src : ℕ)
  | truncate (dst src : ℕ)
  | toIndex (dst src : ℕ)
  | fromIndex (dst src : ℕ)
abbrev RAMProgram := List RAMInstruction

def AllowedInstruction : RAMInstruction → Prop
  | .core (.gauss _) => False
  | .core (.rsqrt _ _) => False
  | .core (.rconst _ c) => ∃ q : ℚ, c = q
  | _ => True
def Admissible (P : RAMProgram) : Prop := ∀ i ∈ P, AllowedInstruction i

def coreProjection (P : RAMProgram) : MatMulTimeLP.Program :=
  P.map (fun i => match i with | .core j => j | _ => .halt)
def ramHalted (P : RAMProgram) (s : MatMulTimeLP.State) : Prop :=
  P[s.pc]? = none ∨ P[s.pc]? = some (.core .halt)

def ramStep (P : RAMProgram) (ω : MatMulTimeLP.Tape) (t : ℕ)
    (s : MatMulTimeLP.State) : MatMulTimeLP.State :=
  match P[s.pc]? with
  | none => s
  | some (.core _) => MatMulTimeLP.step (coreProjection P) ω t s
  | some (.exp i j) => ⟨s.pc+1, Function.update s.R i (Real.exp (s.R j)), s.N⟩
  | some (.log i j) => ⟨s.pc+1, Function.update s.R i (Real.log (s.R j)), s.N⟩
  | some (.truncate i j) => ⟨s.pc+1, Function.update s.R i (Int.floor (s.R j)), s.N⟩
  | some (.toIndex i j) => ⟨s.pc+1, s.R, Function.update s.N i (Nat.floor (s.R j))⟩
  | some (.fromIndex i j) => ⟨s.pc+1, Function.update s.R i (s.N j), s.N⟩
def ramState (P : RAMProgram) (input : List ℝ) (ω : MatMulTimeLP.Tape) : ℕ → MatMulTimeLP.State
  | 0 => MatMulTimeLP.initState input
  | t+1 => ramStep P ω t (ramState P input ω t)
def HaltsWithin (P : RAMProgram) (input : List ℝ) (budget : ℕ) : Prop :=
  ∀ ω, ∃ t, t+1 ≤ budget ∧ ramHalted P (ramState P input ω t)
/-- Observing at a fixed valid time bound avoids a default output for nontermination. -/
def ramOutput (P : RAMProgram) (input : List ℝ) (budget : ℕ) (ω : MatMulTimeLP.Tape) : ℂ :=
  let s := ramState P input ω budget
  ⟨s.R input.length, s.R (input.length+1)⟩

inductive Query (n : ℕ) where
  | partition
  | xSubset (S : Finset (Fin n))
  | pauli (P : Fin n → Pauli)
def pauliCode : Pauli → ℝ | .I => 0 | .X => 1 | .Y => 2 | .Z => 3

def queryCode {n : ℕ} : Query n → List ℝ
  | .partition => [0]
  | .xSubset S => 1 :: (List.finRange n).map (fun i => if i ∈ S then 1 else 0)
  | .pauli P => 2 :: (List.finRange n).map (fun i => pauliCode (P i))
def encodeInput {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h η : Fin n → ℝ)
    (ε δ : ℝ) (q : Query n) : List ℝ :=
  [(n : ℝ), ε, δ] ++ MatMulTimeLP.matToList J ++ MatMulTimeLP.vecToList h ++
    MatMulTimeLP.vecToList η ++ queryCode q

def target {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h η : Fin n → ℝ) : Query n → ℂ
  | .partition => partition J h η
  | .xSubset S => Matrix.trace (xSubset S * density J h η)
  | .pauli P => Matrix.trace (pauliString P * density J h η)
def GoodOutput {n : ℕ} (ε : ℝ) (q : Query n) (out truth : ℂ) : Prop :=
  match q with
  | .partition | .xSubset _ => ExpApprox ε out truth
  | .pauli _ => ‖out - truth‖ ≤ ε
/-- A uniform polynomial and an integer repetition budget valid for every delta in (0,1).
The added 1 encodes the usual asymptotic log(delta^-1) bound as delta tends to zero. -/
def goalBudget {n : ℕ} (C d : ℕ) (J : Matrix (Fin n) (Fin n) ℝ) (h η : Fin n → ℝ)
    (ε δ : ℝ) : ℕ :=
  C * ⌈(1 + (n : ℝ) + maxEntry J + maxField h + maxField η + ε⁻¹)^d⌉₊ *
    (1 + ⌈Real.log (1/δ)⌉₊)

def SuccessfulRun {n : ℕ} (P : RAMProgram) (budget : ℕ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h η : Fin n → ℝ) (ε δ : ℝ) (q : Query n) : Prop :=
  let input := encodeInput J h η ε δ q
  let output := ramOutput P input budget
  HaltsWithin P input budget ∧ Measurable output ∧
    1-δ ≤ MatMulTimeLP.tapeLaw.real {ω | GoodOutput ε q (output ω) (target J h η q)}

/-- Concrete annealing resource witnesses from pp.29-30. -/
def productSamples (L : ℕ) (ε : ℝ) : ℕ := ⌈16 * Real.exp 2 * (L : ℝ) / ε^2⌉₊
def baseSamples (L : ℕ) (ε : ℝ) : ℕ := L * productSamples L ε
def medianRepeats (δ : ℝ) : ℕ := 2 * ⌈16 * Real.log (1/δ)⌉₊ + 1
def totalSamples (L : ℕ) (ε δ : ℝ) : ℕ := baseSamples L ε * medianRepeats δ
end TFIMPhaseDiagram.Classical


