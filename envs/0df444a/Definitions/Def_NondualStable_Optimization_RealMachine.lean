-- Prove2me | Definitions.Def_NondualStable_Optimization_RealMachine
-- name    : NondualStable_Optimization_RealMachine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:15.192109+00:00
-- url     : https://prove2.me/theorems/93af2df1-891e-497c-9396-1c2ce255a212
-- title:
--   Finite randomized real-arithmetic programs and charged oracle executions
-- statement:
--   A program is a finite list of scalar instructions on real and natural registers, with indirect memory access, conditional branches, rational powers, positive logarithms and independent scalar standard Gaussian draws. The initial registers contain only $d,T,G,R,\varepsilon,\delta$; norm parameters may be constants of the code. A query instruction is the only access to the unknown objective. It appends the actual point, value and subgradient to the history.
--
--   Each scalar instruction is charged. A query additionally charges scalar coordinate copies, and report and output instructions charge the values they copy. The separately counted first-order calls are exactly the history length. Finite-fuel execution has no asserted termination guarantee. Faults, including division by zero and nonpositive logarithm arguments, remain visible.
--
--   For an error tolerance $E$, accuracy means
--   $$f(\hat x)\le f(y)+E\quad\text{for every }y\in R B_p^d.$$
--   Safety asserts successful halting, feasible queries and output, and the required query cap on every tape. Certificate accuracy additionally asserts $\ell\le f(y)$ for every feasible $y$ and $f(\hat x)\le\ell+\varepsilon$. An implementation of Algorithm 1 emits a charged macro-state trace obeying the bundle transition relation and returns its current best point, allowing early returns. These are predicates for theorem conclusions, never correctness fields attached to a program.
-- source:
--   David Martínez-Rubio, Cristóbal Guzmán, STOC 2027 submission #415 (October 2026), printed pp. 11–12/PDF pp. 12–13, real-arithmetic model and Theorem 12; printed pp. 25–28/PDF pp. 26–29, Appendix F and Theorem 3 proof

import Definitions.Def_NondualStable_Optimization_Bundle

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NondualStable.Optimization

/-- A finite instruction alphabet. Rational powers use integer numerator and
positive denominator read from natural registers; negative powers use division.
There is no instruction for evaluating f except `query`, or for minimization,
expectation, separation, vector norms, or ellipsoid solves. -/
inductive Instruction where
  | const (dst : ℕ) (v : ℝ)
  | natConst (dst v : ℕ)
  | natAdd (dst a b : ℕ)
  | natSub (dst a b : ℕ)
  | ofNat (dst a : ℕ)
  | add (dst a b : ℕ)
  | sub (dst a b : ℕ)
  | mul (dst a b : ℕ)
  | div (dst a b : ℕ)
  | power (dst a numerator denominator : ℕ)
  | log (dst a : ℕ)
  | load (dst addr : ℕ)
  | store (addr src : ℕ)
  | jump (target : ℕ)
  | less (a b yes no : ℕ)
  | natLess (a b yes no : ℕ)
  | gaussian (dst : ℕ)
  | query (pointAddr valueDst gradAddr : ℕ)
  | report (lower upper pointAddr phaseFlag phaseLower phaseGap phaseStart doneFlag : ℕ)
  | halt (lower pointAddr : ℕ)

abbrev Program := List Instruction
abbrev Tape := ℕ → ℝ

noncomputable def tapeLaw : Measure Tape :=
  Measure.infinitePi (fun _ => gaussianReal 0 1)

structure MachineState (d : ℕ) where
  pc : ℕ := 0
  realReg : ℕ → ℝ := fun _ => 0
  natReg : ℕ → ℕ := fun _ => 0
  cursor : ℕ := 0
  operations : ℕ := 0
  history : History d := []
  reports : List (BundleState d) := []
  output : Option (ℝ × Vec d) := none
  stopped : Bool := false
  fault : Bool := false

/-- Parameters are the only initial data: n[0]=d, n[1]=T and
r[0..3]=(G,R,epsilon,delta). Norm parameters are fixed program constants.
The objective and its minimizer never appear in the initial registers. -/
noncomputable def machineInit (d T : ℕ) (G R ε δ : ℝ) : MachineState d where
  natReg := fun i => if i = 0 then d else if i = 1 then T else 0
  realReg := fun i => if i = 0 then G else if i = 1 then R else if i = 2 then ε
    else if i = 3 then δ else 0

def machineFault {d : ℕ} (s : MachineState d) : MachineState d :=
  {s with stopped := true, fault := true}

def readVector {d : ℕ} (s : MachineState d) (addr : ℕ) : Vec d :=
  fun i => s.realReg (s.natReg addr + i.val)

/-- Each scalar instruction costs one. Query and report copy their scalar
coordinates and charge for those copies; the first-order call is counted
separately by the appended history entry. An invalid instruction faults. -/
noncomputable def machineStep {d : ℕ} (P : Program) (O : Oracle d) (ω : Tape)
    (s : MachineState d) : MachineState d := by
  classical
  exact if s.stopped then s else
    match P[s.pc]? with
    | none => machineFault s
    | some ins =>
      let u := {s with pc := s.pc + 1, operations := s.operations + 1}
      match ins with
      | .const dst v => {u with realReg := Function.update s.realReg dst v}
      | .natConst dst v => {u with natReg := Function.update s.natReg dst v}
      | .natAdd dst a b => {u with natReg := Function.update s.natReg dst (s.natReg a + s.natReg b)}
      | .natSub dst a b => {u with natReg := Function.update s.natReg dst (s.natReg a - s.natReg b)}
      | .ofNat dst a => {u with realReg := Function.update s.realReg dst (s.natReg a : ℝ)}
      | .add dst a b => {u with realReg := Function.update s.realReg dst (s.realReg a + s.realReg b)}
      | .sub dst a b => {u with realReg := Function.update s.realReg dst (s.realReg a - s.realReg b)}
      | .mul dst a b => {u with realReg := Function.update s.realReg dst (s.realReg a * s.realReg b)}
      | .div dst a b => if s.realReg b = 0 then machineFault u else
          {u with realReg := Function.update s.realReg dst (s.realReg a / s.realReg b)}
      | .power dst a num den => if s.natReg den = 0 ∨ s.realReg a < 0 then machineFault u else
          {u with realReg := Function.update s.realReg dst ((s.realReg a) ^ ((s.natReg num : ℝ) / (s.natReg den : ℝ)))}
      | .log dst a => if s.realReg a ≤ 0 then machineFault u else
          {u with realReg := Function.update s.realReg dst (Real.log (s.realReg a))}
      | .load dst a => {u with realReg := Function.update s.realReg dst (s.realReg (s.natReg a))}
      | .store a src => {u with realReg := Function.update s.realReg (s.natReg a) (s.realReg src)}
      | .jump j => {u with pc := j}
      | .less a b yes no => {u with pc := if s.realReg a < s.realReg b then yes else no}
      | .natLess a b yes no => {u with pc := if s.natReg a < s.natReg b then yes else no}
      | .gaussian dst => {u with cursor := s.cursor + 1, realReg := Function.update s.realReg dst (ω s.cursor)}
      | .query addr dst gradAddr =>
          let x := readVector s addr
          let a := O s.history x
          let regs := Function.update s.realReg dst a.val
          {u with
            operations := s.operations + 2 * d + 1
            history := s.history ++ [⟨x, a⟩],
            realReg := fun j => if h : s.natReg gradAddr ≤ j ∧ j < s.natReg gradAddr + d
              then a.grad ⟨j - s.natReg gradAddr, by omega⟩ else regs j}
      | .report ell U addr flag lo gap start done =>
          let phase := if 0 < s.realReg flag then some (⟨s.realReg lo, s.realReg gap, s.natReg start⟩ : Phase) else none
          let b : BundleState d := ⟨s.history, s.realReg ell, s.realReg U,
            readVector s addr, phase, decide (0 < s.realReg done)⟩
          {u with reports := s.reports ++ [b], operations := s.operations + d + 8}
      | .halt ell addr => {u with stopped := true, output := some (s.realReg ell, readVector s addr), operations := s.operations + d + 2}

noncomputable def execute {d : ℕ} (P : Program) (T : ℕ) (G R ε δ : ℝ)
    (O : Oracle d) (ω : Tape) (fuel : ℕ) : MachineState d :=
  (machineStep P O ω)^[fuel] (machineInit d T G R ε δ)

def Safe {d : ℕ} (p : ℝ≥0∞) (R : ℝ) (T : ℕ) (s : MachineState d) : Prop :=
  s.stopped = true ∧ s.fault = false ∧ s.history.length ≤ T ∧
  (∀ o ∈ s.history, o.point ∈ ball p R) ∧
  ∃ ell x, s.output = some (ell, x) ∧ x ∈ ball p R

def Accurate {d : ℕ} (p : ℝ≥0∞) (R E : ℝ) (f : Vec d → ℝ)
    (s : MachineState d) : Prop :=
  ∃ ell x, s.output = some (ell, x) ∧
    ∀ y ∈ ball p R, f x ≤ f y + E

def CertificateAccurate {d : ℕ} (p : ℝ≥0∞) (R ε : ℝ) (f : Vec d → ℝ)
    (s : MachineState d) : Prop :=
  ∃ ell x, s.output = some (ell, x) ∧ (∀ y ∈ ball p R, ell ≤ f y) ∧ f x ≤ ell + ε

/-- Macro traces are emitted by charged report instructions. A completed or
early-stopped trace has exactly the machine's oracle history and returns the
current best point. Every transition obeys Algorithm 1 with a valid certificate;
the providers here specify behavior and do not perform free machine operations. -/
def BundleImplementation {d : ℕ} (p : ℝ≥0∞) (G R ε : ℝ)
    (O : Oracle d) (s : MachineState d) : Prop :=
  ∃ S : ModelSolver d, ∃ A : CenterProvider d, ∃ n : ℕ,
    ValidModelSolver p R S ∧ FeasibleProvider p R S A ∧
    s.reports = (List.range (n + 1)).map (bundleRun G R ε O S A) ∧
    s.history = (bundleRun G R ε O S A n).history ∧
    s.output = some ((bundleRun G R ε O S A n).lower, (bundleRun G R ε O S A n).best)

noncomputable def operationBudget (C : ℝ) (k : ℕ) (d : ℕ) (a δ : ℝ) : ℝ :=
  C * ((d : ℝ) + 1 + a + Real.log (1 / δ)) ^ k

end NondualStable.Optimization


