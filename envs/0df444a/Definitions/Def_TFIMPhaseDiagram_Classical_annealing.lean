-- Prove2me | Definitions.Def_TFIMPhaseDiagram_Classical_annealing
-- name    : TFIMPhaseDiagram_Classical_annealing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:05:09.336836+00:00
-- url     : https://prove2.me/theorems/688f95a6-6fb1-41fd-bb56-f43c8c5b75d1
-- title:
--   Charged sampling/evaluation oracle machine and annealing estimator
-- statement:
--   The oracle machine is a finite program over scalar/index RAM instructions, a point-sampling instruction, and an instruction evaluating $V$ at a stored point. Point storage is separate from real memory. Sample draws, evaluations, and additional arithmetic have separate counters; evaluating $V$ is never free. The oracle tape has independent samples at each time and annealing stage, on an arbitrary measurable space.
--
--   The prescribed stage sequence takes $m$ samples at each $i/L$, $0\le i<L$, and repeats this schedule $r$ times. With $m=\lceil16e^2L/\epsilon^2\rceil$, the mathematical estimator is
--   $$\operatorname{median}_{1\le q\le r}\prod_{i=0}^{L-1}\frac1m\sum_{j=1}^m\exp(V(X_{qij})/L).$$
--   The median is defined by ordering its odd list; the runtime theorem may implement linear-time selection. The stage contract prevents adaptive selection of sampling distributions. No finite-support or rational-input assumption is imposed.
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026), canonical source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, Proposition 16, p.9; Proposition 33 and P16 proof, pp.29–30

import Definitions.Def_TFIMPhaseDiagram_Classical_sampling

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

namespace TFIMPhaseDiagram.Classical
attribute [local instance] Classical.propDecidable

/-- An oracle samples a point at stage i/L; V is evaluated only by a charged eval instruction. -/
inductive OracleInstruction where
  | core (i : RAMInstruction)
  | sample (pointReg stageReg : ℕ)
  | evaluate (realReg pointReg : ℕ)
abbrev OracleProgram := List OracleInstruction
structure OracleState (A : Type) where
  machine : MatMulTimeLP.State
  points : ℕ → Option A
  samples : ℕ
  evaluations : ℕ
  arithmetic : ℕ

def oracleProjection (P : OracleProgram) : RAMProgram :=
  P.map (fun i => match i with | .core j => j | _ => .core .halt)
def OracleAdmissible (P : OracleProgram) : Prop :=
  ∀ i ∈ P, match i with | .core j => AllowedInstruction j | _ => True

def oracleStep {A : Type} {L : ℕ} (P : OracleProgram) (V : A → ℝ)
    (ω : ℕ → Fin L → A) (t : ℕ) (s : OracleState A) : OracleState A :=
  match P[s.machine.pc]? with
  | none => s
  | some (.core j) =>
    let charge := match j with | .core .halt => 0 | _ => 1
    ⟨ramStep (oracleProjection P) (fun _ => (0,0)) t s.machine,
      s.points, s.samples, s.evaluations, s.arithmetic + charge⟩
  | some (.sample dst src) =>
    if h : s.machine.N src < L then
      ⟨⟨s.machine.pc+1, s.machine.R, s.machine.N⟩,
        Function.update s.points dst (some (ω t ⟨s.machine.N src,h⟩)),
        s.samples+1, s.evaluations, s.arithmetic⟩
    else ⟨⟨s.machine.pc+1, s.machine.R, s.machine.N⟩,
      s.points, s.samples, s.evaluations, s.arithmetic⟩
  | some (.evaluate dst src) =>
    ⟨⟨s.machine.pc+1, Function.update s.machine.R dst
        (match s.points src with | some x => V x | none => 0), s.machine.N⟩,
      s.points, s.samples, s.evaluations+1, s.arithmetic⟩

def oracleState {A : Type} {L : ℕ} (P : OracleProgram) (V : A → ℝ)
    (input : List ℝ) (ω : ℕ → Fin L → A) : ℕ → OracleState A
  | 0 => ⟨MatMulTimeLP.initState input, fun _ => none, 0, 0, 0⟩
  | t+1 => oracleStep P V ω t (oracleState P V input ω t)
def oracleHalted (P : OracleProgram) {A : Type} (s : OracleState A) : Prop :=
  P[s.machine.pc]? = none ∨ P[s.machine.pc]? = some (.core (.core .halt))
def oracleTapeLaw {A : Type} [MeasurableSpace A] {L : ℕ} (μ : Fin L → Measure A) :
    Measure (ℕ → Fin L → A) := Measure.infinitePi (fun _ => Measure.pi μ)
def oracleOutput {A : Type} {L : ℕ} (P : OracleProgram) (V : A → ℝ)
    (input : List ℝ) (b : ℕ) (ω : ℕ → Fin L → A) : ℝ :=
  (oracleState P V input ω b).machine.R input.length
/-- The mathematical annealing estimator, including its odd median repetition count. -/
def productMean (L m : ℕ) (V : ℝ → ℝ) (x : Fin L → Fin m → ℝ) : ℝ :=
  ∏ i, ((∑ j, Real.exp (V (x i j) / L)) / m)
def annealingEstimate {A : Type} (L : ℕ) (ε δ : ℝ) (V : A → ℝ)
    (x : Fin (medianRepeats δ) → Fin L → Fin (productSamples L ε) → A) : ℝ :=
  let estimates := (List.finRange (medianRepeats δ)).map (fun r =>
    ∏ i : Fin L, ((∑ j : Fin (productSamples L ε), Real.exp (V (x r i j) / L)) /
      (productSamples L ε : ℝ)))
  (estimates.mergeSort (fun a b => decide (a ≤ b))).getD (medianRepeats δ / 2) 0
/-- Each group of m draws uses the next deterministic annealing stage, then repeats.
No stage selection can depend on previous sample values. -/
def PrescribedStages {A : Type} {L : ℕ} (P : OracleProgram) (V : A → ℝ)
    (input : List ℝ) (m b : ℕ) : Prop :=
  ∀ (ω : ℕ → Fin L → A) (t : ℕ), t < b →
    let s := oracleState P V input ω t
    ∀ dst src : ℕ, P[s.machine.pc]? = some (.sample dst src) →
      s.machine.N src = (s.samples / m) % L
end TFIMPhaseDiagram.Classical


